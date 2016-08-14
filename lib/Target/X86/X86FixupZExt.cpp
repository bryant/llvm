#include "X86Subtarget.h"
#include "llvm/CodeGen/CalcSpillWeights.h"
#include "llvm/CodeGen/LiveIntervalAnalysis.h"
#include "llvm/CodeGen/LivePhysRegs.h"
#include "llvm/CodeGen/LiveRegMatrix.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/RegisterClassInfo.h"
#include "llvm/CodeGen/VirtRegMap.h"

#include <iterator>

#define DEBUG_TYPE "x86-fixup-zext"

namespace {
using namespace llvm;
using std::unique_ptr;
using std::vector;
using std::pair;
using std::copy_if;
using Segment = LiveRange::Segment;

template <typename Elem, typename Container>
using is_iterable_of = typename std::enable_if<std::is_same<
    typename std::decay<decltype(*std::declval<Container>().begin())>::type,
    Elem>::value>::type;

unsigned get_phys(unsigned reg, const VirtRegMap &vrm) {
  return TargetRegisterInfo::isVirtualRegister(reg) ? vrm.getPhys(reg) : reg;
}

unsigned get_phys(const MachineOperand &regop, const VirtRegMap &vrm) {
  const auto *f = regop.getParent()->getParent()->getParent();
  const auto &tri = *f->getSubtarget().getRegisterInfo();
  assert(regop.isReg());
  unsigned preg = get_phys(regop.getReg(), vrm);
  return regop.getSubReg() ? tri.getSubReg(preg, regop.getSubReg()) : preg;
}

unsigned get_phys(const MachineInstr &i, unsigned opnum,
                  const VirtRegMap &vrm) {
  return get_phys(i.getOperand(opnum), vrm);
}

void erase_instr(MachineInstr &i, LiveIntervals &li) {
  li.RemoveMachineInstrFromMaps(i);
  i.eraseFromParent();
}

DenseMap<MachineBasicBlock *, MachineInstr *>
dominating_defs(unsigned gr8, const MachineRegisterInfo &mri,
                const SlotIndexes &si) {
  DenseMap<MachineBasicBlock *, MachineInstr *> defs;
  // at least until release_37, getInstructionIndex is expensive.
  DenseMap<MachineBasicBlock *, SlotIndex> cached;

  for (MachineInstr &def : mri.def_instructions(gr8)) {
    unsigned tied_use;
    if (def.isRegTiedToUseOperand(0, &tied_use) &&
        def.getOperand(tied_use).getReg() != def.getOperand(0).getReg()) {
      DEBUG(dbgs() << "dominating_defs: " << def.getOperand(0) << " is tied to "
                   << def.getOperand(tied_use) << "\n");
      return dominating_defs(def.getOperand(tied_use).getReg(), mri, si);
    }
    MachineBasicBlock *bb = def.getParent();
    if (defs.find(bb) == defs.end() ||
        si.getInstructionIndex(def) < cached.lookup(bb)) {
      cached[bb] = si.getInstructionIndex(def);
      defs[bb] = &def;
    }
  }
  return defs;
}

void add_seg(SlotIndex s, SlotIndex e, LiveInterval &live, LiveIntervals &li) {
  assert(live.vni_begin() != live.vni_end());
  live.addSegment(Segment(std::move(s), std::move(e), *live.vni_begin()));
}

void add_seg(MachineInstr &s, MachineInstr &e, LiveInterval &live,
             LiveIntervals &li) {
  return add_seg(li.getInstructionIndex(s), li.getInstructionIndex(e), live,
                 li);
}

void add_segs(LiveInterval &src, LiveInterval &dest, LiveIntervals &li) {
  for (const Segment &s : src) {
    add_seg(s.start, s.end, dest, li);
  }
}

bool mov32r0_segs(MachineInstr &def8,
                  SmallVectorImpl<pair<MachineInstr *, MachineInstr *>> &segs,
                  LiveIntervals &li) {
  const MachineFunction &f = *def8.getParent()->getParent();
  const auto &tri = f.getSubtarget().getRegisterInfo();
  MachineBasicBlock &bb = *def8.getParent();
  MachineBasicBlock::iterator ins = &def8;

  if (const Segment *eflagseg =
          li.getRegUnit(*MCRegUnitIterator(X86::EFLAGS, tri))
              .getSegmentContaining(slot(def8))) {
    if (eflagseg->start <= slot(*bb.begin()) && bb.isLiveIn(X86::EFLAGS)) {
      if (bb.pred_size() > 1) {
        return false;
      }
      segs.push_back(make_pair(bb.begin(), &def8));
      return mov32r0_segs(*(*bb.pred_begin())->rbegin(), segs, li);
    }
    ins = li.getInstructionFromIndex(eflagseg->start);
  }
  segs.push_back(make_pair(ins, &def8));
  return true;
}

template <typename T, typename = is_iterable_of<LiveInterval *, T>>
raw_ostream &operator<<(raw_ostream &out, const T &es) {
  for (LiveInterval *e : es) {
    out << "\t" << (*e) << "\n";
  }
  return out;
}

template <typename T, typename = is_iterable_of<LiveInterval *, T>>
bool interferes(const T &as, const LiveInterval &b,
                const MachineRegisterInfo &mri) {
  return any_of(as, [&](const LiveInterval *a) { return a->overlaps(b); });
}

struct ReAllocTool {
  const TargetRegisterInfo *tri;
  const MachineRegisterInfo *mri;
  LiveRegMatrix *lrm;
  VirtRegMap *vrm;
  RegisterClassInfo rci;
  BitVector unused_csr;

  void add_reg_to_bv(BitVector &bv, MCPhysReg reg) const {
    for (MCRegAliasIterator r(reg, tri, true); r.isValid(); ++r) {
      bv.set(*r);
    }
  }

  BitVector bv_from_regs(ArrayRef<MCPhysReg> regs) const {
    BitVector rv(tri->getNumRegs());
    for (const MCPhysReg &r : regs) {
      add_reg_to_bv(rv, r);
    }
    return rv;
  }

  ReAllocTool(const MachineFunction &f, LiveRegMatrix &lrm_, VirtRegMap &vrm_)
      : tri(f.getSubtarget().getRegisterInfo()), mri(&f.getRegInfo()),
        lrm(&lrm_), vrm(&vrm_), rci(), unused_csr(tri->getNumRegs()) {
    const MCPhysReg *csr = tri->getCalleeSavedRegs(&f);
    for (unsigned i = 0; csr[i] != 0; i += 1) {
      if (!lrm->isPhysRegUsed(csr[i])) {
        add_reg_to_bv(unused_csr, csr[i]);
      }
    }
    rci.runOnMachineFunction(f);
  }

  bool interf(LiveInterval &live, unsigned preg) const {
    return lrm->checkInterference(live, preg) != LiveRegMatrix::IK_Free;
  }

  template <typename T, typename = is_iterable_of<LiveInterval *, T>>
  bool interf(LiveInterval &live, unsigned preg, T &evictees) const {
    if (lrm->checkRegMaskInterference(live, preg) ||
        lrm->checkRegUnitInterference(live, preg)) {
      return true;
    }
    DenseSet<LiveInterval *> ev;
    for (MCRegUnitIterator regunit(preg, tri); regunit.isValid(); ++regunit) {
      LiveIntervalUnion::Query &q = lrm->query(live, *regunit);
      if (q.collectInterferingVRegs() > 0) {
        for (LiveInterval *l : q.interferingVRegs()) {
          ev.insert(l);
        }
      }
    }
    std::copy(ev.begin(), ev.end(), back_inserter(evictees));
    return evictees.size() > 0;
  }

  const MCPhysReg *alloc_next(LiveInterval &live,
                              const BitVector *except = nullptr,
                              ArrayRef<MCPhysReg>::iterator *it = nullptr,
                              const TargetRegisterClass *rc = nullptr) const {
    ArrayRef<MCPhysReg> ord =
        rci.getOrder(rc ? rc : mri->getRegClass(live.reg));
    BitVector rs = unused_csr;
    if (except != nullptr) {
      rs |= *except;
    }
    auto rv = std::find_if(
        it ? std::next(*it) : ord.begin(), ord.end(),
        [&](MCPhysReg r) { return !rs.test(r) && !interf(live, r); });
    return rv == ord.end() ? nullptr : rv;
  }

  MCPhysReg alloc(LiveInterval &live, const BitVector *except = nullptr,
                  const TargetRegisterClass *rc = nullptr) const {
    const MCPhysReg *rv = alloc_next(live, except, nullptr, rc);
    return rv == nullptr ? 0 : *rv;
  }

  // (re-)allocate a group of interfering intervals. brute force search. returns
  // nullptr if impossible.
  template <typename C, typename = is_iterable_of<LiveInterval *, C>>
  unique_ptr<vector<pair<LiveInterval *, const MCPhysReg *>>>
  alloc_interf_intervals(C group, const BitVector *except = nullptr) const {
    if (group.empty()) {
      return make_unique<vector<pair<LiveInterval *, const MCPhysReg *>>>();
    }
    auto assigned =
        make_unique<vector<pair<LiveInterval *, const MCPhysReg *>>>();

    auto maybe_unassign = [&](pair<LiveInterval *, const MCPhysReg *> &p) {
      if (p.second) {
        lrm->unassign(*p.first);
      }
    };

    auto maybe_assign = [&](pair<LiveInterval *, const MCPhysReg *> &p) {
      if (p.second) {
        lrm->assign(*p.first, *p.second);
      }
    };

    auto try_next_in_group = [&]() {
      assert(!group.empty());
      assigned->push_back(
          std::make_pair(group.back(), alloc_next(*group.back(), except)));
      group.pop_back();
      maybe_assign(assigned->back());
    };

    auto back_to_previous = [&]() {
      assert(!assigned->empty());
      maybe_unassign(assigned->back());
      group.push_back(assigned->back().first);
      assigned->pop_back();
    };

    auto try_next_reg = [&]() {
      assert(!assigned->empty());
      maybe_unassign(assigned->back());
      assigned->back().second =
          alloc_next(*assigned->back().first, except, &assigned->back().second);
      maybe_assign(assigned->back());
    };

    try_next_in_group();

    while (!group.empty() || assigned->back().second == nullptr) {
      if (assigned->back().second == nullptr) {
        back_to_previous();
        if (assigned->empty()) {
          return nullptr;
        }
        try_next_reg();
      } else {
        try_next_in_group();
      }
    }
    for (auto &p : *assigned) {
      lrm->unassign(*p.first);
    }
    return assigned;
  }

  template <typename C, typename = is_iterable_of<LiveInterval *, C>>
  unique_ptr<vector<MCPhysReg>>
  evict_intervals(const C &lives, const BitVector *excepts = nullptr) const {
    DenseMap<LiveInterval *, const MCPhysReg *> newmap;
    vector<LiveInterval *> ungrouped(lives.begin(), lives.end());

    while (!ungrouped.empty()) {
      vector<LiveInterval *> group;
      group.push_back(ungrouped.back());
      ungrouped.pop_back();
      bool done = false;
      while (!done) {
        auto it = std::partition(
            ungrouped.begin(), ungrouped.end(),
            [&](LiveInterval *h) { return !interferes(group, *h, *mri); });
        done = it == ungrouped.end();
        std::copy(it, ungrouped.end(), back_inserter(group));
        ungrouped.erase(it, ungrouped.end());
      }
      if (auto newassigns = alloc_interf_intervals(group, excepts)) {
        for (auto pair_ : *newassigns) {
          newmap.insert(pair_);
        }
      } else {
        return nullptr;
      }
    }
    auto rv = make_unique<vector<MCPhysReg>>();
    transform(lives, back_inserter(*rv),
              [&](LiveInterval *l) { return *newmap[l]; });
    return rv;
  }

  MCPhysReg unassign(LiveInterval &live) {
    unsigned old = get_phys(live.reg, *vrm);
    lrm->unassign(live);
    return old;
  }

  template <typename C, typename = is_iterable_of<LiveInterval *, C>>
  vector<MCPhysReg> unassign_all(C &lives) {
    vector<MCPhysReg> r;
    transform(lives, back_inserter(r),
              [&](LiveInterval *l) { return unassign(*l); });
    return r;
  }

  template <typename C, typename D,
            typename = is_iterable_of<LiveInterval *, C>,
            typename = is_iterable_of<MCPhysReg, D>>
  void assign_all(C &lives, D &&regs) {
    for (auto intv_reg : zip_first(lives, std::forward<D>(regs))) {
      lrm->assign(*std::get<0>(intv_reg), std::get<1>(intv_reg));
    }
  }

  bool reserve_phys_reg(MCPhysReg preg, LiveInterval &live) {
    vector<LiveInterval *> evictees;
    if (!interf(live, preg, evictees)) {
      DEBUG(dbgs() << "ReAllocTool: " << tri->getName(preg)
                   << " is already free.\n");
      return true;
    } else if (evictees.size() > 0) {
      DEBUG(dbgs() << "ReAllocTool: trying to reserve " << tri->getName(preg)
                   << " by evicting:\n"
                   << evictees);
      vector<MCPhysReg> oldregs = unassign_all(evictees);
      BitVector bv = bv_from_regs(preg);
      if (auto newregs = evict_intervals(evictees, &bv)) {
        assign_all(evictees, *newregs);
        return true;
      }
      assign_all(evictees, oldregs);
    }
    DEBUG(dbgs() << "ReAllocTool: unable to reserve " << tri->getName(preg)
                 << "\n");
    return false;
  }
};

struct Candidate {
  MachineInstr *ins;
  MachineInstr *gr8def;
  MachineInstr *movzx;
  LiveIntervals *li;
  LiveInterval *live32;
  LiveInterval *live8;
  unique_ptr<LiveInterval> extra;
  vector<MCPhysReg> constraints;

private:
  unsigned pdest;
  unsigned psrc;

public:
  static MachineInstr *valid_candidate(MachineInstr &i, LiveIntervals &li) {
    if (i.getOpcode() != X86::MOVZX32rr8 || i.getOperand(1).getSubReg() != 0) {
      return nullptr;
    }

    const MachineFunction &f = *i.getParent()->getParent();
    const MachineRegisterInfo &mri = f.getRegInfo();
    const TargetRegisterInfo &tri = *f.getSubtarget().getRegisterInfo();

    unsigned src = i.getOperand(1).getReg();
    auto bbdefs = dominating_defs(src, mri, *li.getSlotIndexes());
    if (bbdefs.size() > 1 || (mri.getSimpleHint(src) &&
                              !tri.isVirtualRegister(mri.getSimpleHint(src)))) {
      DEBUG(dbgs() << "passing over " << i << "defs: " << bbdefs.size()
                   << ", gr8 hint: " << PrintReg(mri.getSimpleHint(src), &tri)
                   << "\n");
      return nullptr;
    }
    return bbdefs.begin()->second;
  }

  Candidate(const SmallVectorImpl<pair<MachineInstr *, MachineInstr *>> &segs,
            MachineInstr &gr8, MachineInstr &movzx_,
            const TargetRegisterInfo &tri, LiveIntervals &li_)
      : ins(nullptr), gr8def(&gr8), movzx(&movzx_), li(&li_),
        live32(&li->getInterval(movzx->getOperand(0).getReg())),
        live8(&li->getInterval(movzx->getOperand(1).getReg())),
        extra(new LiveInterval(live32->reg, live32->weight)), constraints() {
    MachineBasicBlock &bb = *segs.front().first->getParent();
    const TargetInstrInfo &tii = *bb.getParent()->getSubtarget().getInstrInfo();
    ins = BuildMI(bb, segs.front().first, movzx->getDebugLoc(),
                  tii.get(X86::MOV32r0), 0);
    li->InsertMachineInstrInMaps(*ins);
    extra->getNextValue(li->getInstructionIndex(*ins),
                        li->getVNInfoAllocator());
    add_seg(*ins, *segs.front().second, *extra, *li);
    for (auto p : make_range(std::next(segs.begin()), segs.end())) {
      add_seg(*p.first, *p.second, *extra, *li);
    }
  }

  ~Candidate() {
    if (ins) {
      erase_instr(ins, *li);
    }
  }

  Candidate(Candidate &&c)
      : ins(c.ins), gr8def(c.gr8def), movzx(c.movzx), li(c.li),
        live32(c.live32), live8(c.live8), extra(std::move(c.extra)),
        constraints(std::move(c.constraints)) {
    c.ins = nullptr;
  }

  Candidate &operator=(Candidate &&c) {
    ins = c.ins;
    gr8def = c.gr8def;
    movzx = c.movzx;
    live32 = c.live32;
    live8 = c.live8;
    li = c.li;
    extra = std::move(c.extra);
    constraints = std::move(c.constraints);
    c.ins = nullptr;
    return *this;
  }

  static unique_ptr<Candidate> from_mi(MachineInstr &i, LiveIntervals &li,
                                       const VirtRegMap &vrm) {
    const MachineFunction &f = *i.getParent()->getParent();
    const MachineRegisterInfo &mri = f.getRegInfo();
    const TargetRegisterInfo &tri = *f.getSubtarget().getRegisterInfo();

    MachineInstr *def;
    SmallVector<pair<MachineInstr *, MachineInstr *>, 4> segs;
    if ((def = valid_candidate(i, li)) == nullptr ||
        !mov32r0_segs(*def, segs, li)) {
      return nullptr;
    }

    Candidate c(segs, *def, i, tri, li);
    if (c.live32->overlaps(*c.extra)) {
      return nullptr;
    }

    add_segs(*c.live32, *c.extra, li);
    add_segs(*c.live8, *c.extra, li);

    unsigned dest = i.getOperand(0).getReg();
    // look for copy instr reg alloc hints
    for (const MachineInstr &use : mri.use_instructions(dest)) {
      if (use.isCopy()) {
        if (unsigned hint =
                get_phys(VirtRegAuxInfo::copyHint(&use, dest, tri, mri), vrm)) {
          c.constraints.push_back(hint);
        }
      }
    }

    // look for regmask constraints if no hints were found
    if (c.constraints.empty()) {
      BitVector regmask;
      if (li.checkRegMaskInterference(*c.extra, regmask)) {
        const TargetRegisterClass &destcls = *mri.getRegClass(dest);
        copy_if(destcls.begin(), destcls.end(), back_inserter(c.constraints),
                [&](MCPhysReg r) { return regmask.test(reg); });
      }
    }
    return make_unique<Candidate>(std::move(c));
  }

  bool operator<(const Candidate &b) const {
    if (constraints.size() > 0 && b.constraints.size() == 0)
      return true;
    if (b.constraints.size() > 0 && constraints.size() == 0)
      return false;
    if (constraints.size() < b.constraints.size())
      return true;
    return li_size() > b.li_size();
  }

  unsigned li_size() const { return extra->getSize(); }

  friend raw_ostream &operator<<(raw_ostream &out, const Candidate &c) {
    out << "Candidate:\n\tinserted: " << (*c.ins)
        << "\tgr8 def: " << (*c.gr8def) << "\tmovzx: " << (*c.movzx)
        << "\txor gr32: " << (*c.extra);
    if (c.constraints.size() > 0) {
      out << "\n\tconstraints:";
      for (unsigned cx : c.constraints) {
        out << " " << PrintReg(cx, &c.tri());
      }
    } else {
      out << "\n\tno constraints.";
    }
    return out;
  }

  const X86RegisterInfo &tri() const {
    return *reinterpret_cast<const X86RegisterInfo *>(
        ins->getParent()->getParent()->getSubtarget().getRegisterInfo());
  }

  const X86InstrInfo &tii() const {
    return *reinterpret_cast<const X86InstrInfo *>(
        ins->getParent()->getParent()->getSubtarget().getInstrInfo());
  }

  MachineRegisterInfo &mri() const {
    return ins->getParent()->getParent()->getRegInfo();
  }

  void unassign(ReAllocTool &ratool) {
    pdest = ratool.unassign(*live32);
    psrc = ratool.unassign(*live8);
  }

  void assign_old(LiveRegMatrix &lrm) {
    lrm.assign(*live32, pdest);
    lrm.assign(*live8, psrc);
    pdest = psrc = 0;
  }

  void assign_new(LiveRegMatrix &lrm, MCPhysReg newdest) {
    // vsrc uses => vdest:sub_8bit; insert vdest = mov32r0; del movzx
    unsigned vdest = movzx->getOperand(0).getReg();
    unsigned vsrc = movzx->getOperand(1).getReg();

    // in-place operand mutation would confuse defusechain_iterator
    vector<MachineOperand *> ops;
    transform(mri().reg_operands(vsrc), back_inserter(ops),
              [](MachineOperand &op) { return &op; });
    for (MachineOperand *op : ops) {
      DEBUG(dbgs() << "changing " << (*op->getParent()));
      op->substVirtReg(vdest, X86::sub_8bit, tri());
      DEBUG(dbgs() << "to " << (*op->getParent()));
    }

    erase_instr(*movzx, *li);
    li->removeInterval(vsrc);
    li->removeInterval(vdest);

    const TargetRegisterClass &destcls = *mri().getRegClass(vdest);
    ins->getOperand(0).setReg(vdest);
    if (destcls.getSize() > 32 / 8) {
      ins->getOperand(0).setSubReg(X86::sub_32bit);
      ins->getOperand(0).setIsUndef();
    }
    if (const TargetRegisterClass *newcls = gr8def->getRegClassConstraintEffect(
            0, ins->getRegClassConstraintEffect(0, &destcls, &tii(), &tri()),
            &tii(), &tri())) {
      DEBUG(dbgs() << "updating reg class from "
                   << tri().getRegClassName(&destcls) << " to "
                   << tri().getRegClassName(newcls) << "\n");
      mri().setRegClass(vdest, newcls);
    } else {
      DEBUG(dbgs() << "not updating reg class\n");
    }
    li->removeInterval(vdest);
    lrm.assign(li->createAndComputeVirtRegInterval(vdest), newdest);
    ins = nullptr; // prevent erasure of mov32r0 by dtor
  }

  bool valid_dest_reg(MCPhysReg physreg) const {
    return mri().getRegClass(movzx->getOperand(0).getReg())->contains(physreg);
  }
};

struct X86FixupZExt : public MachineFunctionPass {
  static char id;

  X86FixupZExt() : MachineFunctionPass(id) {}

  const char *getPassName() const override {
    return "X86 Zero-Extension Fix-up";
  }

  void getAnalysisUsage(AnalysisUsage &a) const override {
    a.addRequired<LiveRegMatrix>();
    a.addRequired<VirtRegMap>();
    a.addRequired<LiveIntervals>();
    a.setPreservesAll();
    return MachineFunctionPass::getAnalysisUsage(a);
  }

  bool runOnMachineFunction(MachineFunction &f) override {
    VirtRegMap &vrm = getAnalysis<VirtRegMap>();
    LiveIntervals &li = getAnalysis<LiveIntervals>();
    LiveRegMatrix &lrm = getAnalysis<LiveRegMatrix>();
    vector<Candidate> constrained, cands;
    ReAllocTool ratool(f, lrm, vrm);

    DEBUG(dbgs() << "analyzing " << f.getName() << "'s movzxes.\n");
    for (MachineBasicBlock &bb : f) {
      for (MachineInstr &i : bb) {
        if (auto cand = Candidate::from_mi(i, li, vrm)) {
          if (cand->constraints.size() > 0) {
            constrained.push_back(std::move(*cand.release()));
          } else {
            cands.push_back(std::move(*cand.release()));
          }
        }
      }
    }

    BitVector nosub8;
    if (f.getSubtarget<X86Subtarget>().is64Bit()) {
      nosub8 = ratool.bv_from_regs({X86::RIP});
    } else {
      nosub8 = ratool.bv_from_regs(ArrayRef<MCPhysReg>(
          X86::GR32_ABCDRegClass.begin(), X86::GR32_ABCDRegClass.end()));
      nosub8.flip();
    }

    auto reserve_one_of = [&](ArrayRef<MCPhysReg> regs, const Candidate &c) {
      for (MCPhysReg preg : regs) {
        if (!nosub8.test(preg) && c.valid_dest_reg(preg) &&
            !ratool.unused_csr.test(preg) &&
            ratool.reserve_phys_reg(preg, *c.extra)) {
          return preg;
        }
      }
      return static_cast<MCPhysReg>(0);
    };

    DEBUG(vrm.print(dbgs()));
    DEBUG(f.print(dbgs(), li.getSlotIndexes()));
    std::sort(constrained.begin(), constrained.end());
    for (Candidate &c : constrained) {
      DEBUG(dbgs() << c << "\n");
      c.unassign(ratool);
      if (unsigned newreg = reserve_one_of(c.constraints, c)) {
        DEBUG(dbgs() << "works\n");
        c.assign_new(lrm, newreg);
      } else {
        c.assign_old(lrm);
        if (none_of(c.constraints, [&](MCPhysReg r) {
              return r == get_phys(*c.movzx, 0, vrm);
            })) {
          // only demote if RA pass missed all hints
          c.constraints.clear();
          DEBUG(dbgs() << "demoting to unconstrained candidate\n");
          cands.push_back(std::move(c));
        } else {
          DEBUG(dbgs() << "could not transform\n");
        }
      }
    }

    std::sort(cands.begin(), cands.end());
    for (Candidate &c : cands) {
      DEBUG(dbgs() << c << "\n");
      c.unassign(ratool);
      MCPhysReg newreg;
      if (!f.getSubtarget<X86Subtarget>().is64Bit() &&
          ((newreg = ratool.alloc(*c.extra, &nosub8)) != 0 ||
           (newreg = reserve_one_of(
                ArrayRef<MCPhysReg>(X86::GR32_ABCDRegClass.begin(),
                                    X86::GR32_ABCDRegClass.end()),
                c)) != 0)) {
        DEBUG(dbgs() << "works\n");
        c.assign_new(lrm, newreg);
      } else if (f.getSubtarget<X86Subtarget>().is64Bit() &&
                 (newreg = ratool.alloc(*c.extra, &nosub8)) != 0) {
        DEBUG(dbgs() << "works\n");
        c.assign_new(lrm, newreg);
      } else {
        DEBUG(dbgs() << "could not transform\n");
        c.assign_old(lrm);
      }
    }
    return false;
  }
};

char X86FixupZExt::id = 0;
}

namespace llvm {
FunctionPass *createX86FixupZExt() { return new X86FixupZExt(); }
}
