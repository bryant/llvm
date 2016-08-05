#include "X86Subtarget.h"
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
using Segment = LiveRange::Segment;

template <typename Elem, typename Container>
using is_iterable_of = typename std::enable_if<std::is_same<
    typename std::decay<decltype(*std::declval<Container>().begin())>::type,
    Elem>::value>::type;

template <typename T> auto push_to(T &t) -> decltype(std::back_inserter(t)) {
  return std::back_inserter(t);
}

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

MachineInstr *insert_mov32r0(MachineInstr &def8, vector<Segment> &segments,
                             LiveIntervals &li) {
  auto slot = [&](MachineInstr &i) { return li.getInstructionIndex(i); };
  const MachineFunction &f = *def8.getParent()->getParent();
  const auto &tri = f.getSubtarget().getRegisterInfo();
  MachineBasicBlock &bb = *def8.getParent();
  MachineBasicBlock::iterator ins = &def8;

  if (const Segment *eflagseg =
          li.getRegUnit(*MCRegUnitIterator(X86::EFLAGS, tri))
              .getSegmentContaining(slot(def8))) {
    if (eflagseg->start <= slot(*bb.begin()) && bb.isLiveIn(X86::EFLAGS)) {
      if (bb.pred_size() > 1) {
        return nullptr;
      }
      segments.push_back(Segment(li.getMBBStartIdx(&bb), slot(def8), nullptr));
      return insert_mov32r0(*(*bb.pred_begin())->rbegin(), segments, li);
    }
    ins = li.getInstructionFromIndex(eflagseg->start);
  }
  // insert dummy mov32r0
  MachineInstrBuilder mib =
      BuildMI(bb, ins, def8.getDebugLoc(),
              f.getSubtarget().getInstrInfo()->get(X86::MOV32r0), 0);
  li.InsertMachineInstrInMaps(*mib);
  segments.push_back(Segment(slot(*mib), slot(def8), nullptr));
  return mib;
}

template <typename T, typename = is_iterable_of<LiveInterval *, T>>
raw_ostream &operator<<(raw_ostream &out, const T &es) {
  for (LiveInterval *e : es) {
    out << "\t" << (*e) << "\n";
  }
  return out;
}
bool interferes(const LiveInterval &a, const LiveInterval &b,
                const MachineRegisterInfo &mri) {
  return a.overlaps(b) && mri.getRegClass(a.reg) == mri.getRegClass(b.reg);
}

template <typename T, typename = is_iterable_of<LiveInterval *, T>>
bool interferes(const T &as, const LiveInterval &b,
                const MachineRegisterInfo &mri) {
  return any_of(as,
                [&](const LiveInterval *a) { return interferes(*a, b, mri); });
}

template <typename... Ranges>
void li_union(LiveRange *dest, const Ranges *... src) {
  for (const auto *r : {src...}) {
    for (const Segment &s : *r) {
      dest->addSegment(Segment(s.start, s.end, nullptr));
    }
  }
}

template <typename Iterator, typename Predicate>
Iterator move_to_end_if(Iterator first, Iterator last, Predicate p) {
  Iterator rv = last;
  while (first != rv) {
    if (p(*first)) {
      --rv;
      std::swap(*first, *rv);
    } else {
      ++first;
    }
  }
  return rv;
}

template <typename Range, typename Predicate>
auto move_to_end_if(Range &r, Predicate p) -> decltype(r.end()) {
  return move_to_end_if(r.begin(), r.end(), std::move(p));
}

struct ReAllocTool {
  const TargetRegisterInfo *tri;
  const MachineRegisterInfo *mri;
  LiveRegMatrix *lrm;
  VirtRegMap *vrm;
  RegisterClassInfo rci;
  BitVector unused_csr;

public:
  ReAllocTool(const MachineFunction &f, LiveRegMatrix &lrm_, VirtRegMap &vrm_)
      : tri(f.getSubtarget().getRegisterInfo()), mri(&f.getRegInfo()),
        lrm(&lrm_), vrm(&vrm_), rci(), unused_csr(tri->getNumRegs()) {
    const MCPhysReg *csr = tri->getCalleeSavedRegs(&f);
    for (unsigned i = 0; csr[i] != 0; i += 1) {
      if (!lrm->isPhysRegUsed(csr[i])) {
        for (MCRegAliasIterator reg(csr[i], tri, true); reg.isValid(); ++reg) {
          unused_csr.set(*reg);
        }
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
    std::copy(ev.begin(), ev.end(), push_to(evictees));
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

  MCPhysReg alloc(LiveInterval &live, const TargetRegisterClass *rc = nullptr,
                  const BitVector *except = nullptr) const {
    const MCPhysReg *rv = alloc_next(live, except, nullptr, rc);
    return rv == nullptr ? 0 : *rv;
  }

  // (re-)allocate a group of interfering intervals. brute force search. returns
  // nullptr if impossible.
  template <typename C, typename = is_iterable_of<LiveInterval *, C>>
  unique_ptr<vector<pair<LiveInterval *, const MCPhysReg *>>>
  alloc_interf_intervals(C group, ArrayRef<MCPhysReg> excepts) const {
    if (group.empty()) {
      return make_unique<vector<pair<LiveInterval *, const MCPhysReg *>>>();
    }
    BitVector except(tri->getNumRegs());

    for (MCPhysReg r : excepts) {
      for (MCRegAliasIterator reg(r, tri, true); reg.isValid(); ++reg) {
        except.set(*reg);
      }
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
          std::make_pair(group.back(), alloc_next(*group.back(), &except)));
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
      assigned->back().second = alloc_next(*assigned->back().first, &except,
                                           &assigned->back().second);
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
  evict_intervals(const C &lives, ArrayRef<MCPhysReg> excepts) const {
    DenseMap<LiveInterval *, const MCPhysReg *> newmap;
    vector<LiveInterval *> ungrouped(lives.begin(), lives.end());

    while (!ungrouped.empty()) {
      vector<LiveInterval *> group;
      group.push_back(ungrouped.back());
      ungrouped.pop_back();
      bool done = false;
      while (!done) {
        auto it = move_to_end_if(ungrouped, [&](LiveInterval *h) {
          return interferes(group, *h, *mri);
        });
        done = it == ungrouped.end();
        std::copy(it, ungrouped.end(), push_to(group));
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
    transform(lives, push_to(*rv), [&](LiveInterval *l) { return *newmap[l]; });
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
    transform(lives, push_to(r), [&](LiveInterval *l) { return unassign(*l); });
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
      if (auto newregs = evict_intervals(evictees, {preg})) {
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
  vector<MCPhysReg> constraints;
  LiveInterval *live32;
  LiveInterval *live8;
  unique_ptr<LiveInterval> extra;
  // private:
  // assign/reassign
  unsigned pdest;
  unsigned psrc;

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

  static unique_ptr<Candidate> from_mi(MachineInstr &i, LiveIntervals &li,
                                       const VirtRegMap &vrm) {
    const MachineFunction &f = *i.getParent()->getParent();
    const MachineRegisterInfo &mri = f.getRegInfo();
    const TargetRegisterInfo &tri = *f.getSubtarget().getRegisterInfo();

    vector<Segment> xorlive;
    MachineInstr *def, *ins;
    if ((def = valid_candidate(i, li)) == nullptr ||
        (ins = insert_mov32r0(*def, xorlive, li)) == nullptr) {
      return nullptr;
    }

    unsigned dest = i.getOperand(0).getReg(), src = i.getOperand(1).getReg();
    // look for copy instr reg alloc hints
    vector<MCPhysReg> cx;
    for (const MachineInstr &use : mri.use_instructions(dest)) {
      if (use.isCopy() && !tri.isVirtualRegister(use.getOperand(0).getReg())) {
        unsigned r =
            use.getOperand(1).getSubReg()
                ? tri.getMatchingSuperReg(use.getOperand(0).getReg(),
                                          use.getOperand(1).getSubReg(),
                                          mri.getRegClass(dest))
                : get_phys(use.getOperand(0), vrm);
        if (f.getSubtarget<X86Subtarget>().is64Bit() ||
            X86::GR32_ABCDRegClass.contains(r)) {
          cx.push_back(r);
        }
      }
    }

    LiveInterval &live32 = li.getInterval(dest), &live8 = li.getInterval(src);
    unique_ptr<LiveInterval> extra(new LiveInterval(live32.reg, live32.weight));
    for (Segment seg : xorlive) {
      extra->addSegment(seg);
    }
    li_union(extra.get(), &live32, &live8);

    return unique_ptr<Candidate>(new Candidate{
        ins, def, &i, std::move(cx), &live32, &live8, std::move(extra), 0, 0});
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
        << "\txor gr32: ";
    for (const Segment &s : *c.extra) {
      out << "[" << s.start << ", " << s.end << "), ";
    }
    if (c.constraints.size() > 0) {
      out << "\n\tconstraints:";
      for (unsigned cx : c.constraints) {
        out << " " << PrintReg(cx, &c.get_tri());
      }
    } else {
      out << "\n\tno constraints.";
    }
    return out;
  }

  const X86RegisterInfo &get_tri() const {
    const MachineFunction &f = *ins->getParent()->getParent();
    return *reinterpret_cast<const X86RegisterInfo *>(
        f.getSubtarget().getRegisterInfo());
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

  void assign_new(LiveRegMatrix &lrm, LiveIntervals &li, MCPhysReg newdest) {
    // vsrc uses => vdest:sub_8bit; insert vdest = mov32r0; del movzx
    unsigned vdest = movzx->getOperand(0).getReg();
    unsigned vsrc = movzx->getOperand(1).getReg();

    MachineFunction &f = *ins->getParent()->getParent();
    MachineRegisterInfo &mri = f.getRegInfo();
    // in-place operand mutation would confuse defusechain_iterator
    vector<MachineOperand *> ops;
    transform(mri.reg_operands(vsrc), push_to(ops),
              [](MachineOperand &op) { return &op; });
    for (MachineOperand *op : ops) {
      DEBUG(dbgs() << "changing " << (*op->getParent()));
      op->substVirtReg(vdest, X86::sub_8bit, get_tri());
      DEBUG(dbgs() << "to " << (*op->getParent()));
    }

    li.RemoveMachineInstrFromMaps(*movzx);
    movzx->eraseFromParent();
    li.removeInterval(vsrc);
    li.removeInterval(vdest);

    ins->getOperand(0).setReg(vdest);
    if (mri.getRegClass(vdest)->getSize() != 32 / 8) {
      assert(mri.getRegClass(vdest)->getSize() > 32 / 8);
      ins->getOperand(0).setSubReg(X86::sub_32bit);
      ins->getOperand(0).setIsUndef();
    }
    mri.setRegClass(vdest, f.getSubtarget<X86Subtarget>().is64Bit()
                               ? &X86::GR32RegClass
                               : &X86::GR32_ABCDRegClass);
    lrm.assign(li.createAndComputeVirtRegInterval(vdest), newdest);
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
    vector<Candidate> constrained, cands, dispose;
    ReAllocTool ratool(f, lrm, vrm);

    DEBUG(dbgs() << "analyzing " << f.getName() << "'s movzxes.\n");
    for (MachineBasicBlock &bb : f) {
      for (MachineInstr &i : bb) {
        if (auto cand = Candidate::from_mi(i, li, vrm)) {
          if (cand->constraints.size() > 0) {
            constrained.emplace_back(std::move(*cand.release()));
          } else {
            cands.emplace_back(std::move(*cand.release()));
          }
        }
      }
    }

    DEBUG(vrm.print(dbgs()));
    DEBUG(f.print(dbgs(), li.getSlotIndexes()));
    std::sort(constrained.begin(), constrained.end());
    std::for_each(constrained.begin(), constrained.end(), [&](Candidate &c) {
      DEBUG(dbgs() << c << "\n");
      c.unassign(ratool);
      bool demote = true;
      for (MCPhysReg preg : c.constraints) {
        if (ratool.reserve_phys_reg(preg, *c.extra)) {
          DEBUG(dbgs() << "works\n");
          c.assign_new(lrm, li, preg);
          return;
        }
        // only demote if RA pass missed all hints
        demote &= preg != get_phys(c.movzx->getOperand(0).getReg(), vrm);
      }
      DEBUG(dbgs() << "could not transform\n");
      c.assign_old(lrm);
      if (demote) {
        c.constraints.clear();
        DEBUG(dbgs() << "demoting to unconstrained candidate\n");
        cands.push_back(std::move(c));
      } else {
        dispose.push_back(std::move(c));
      }
    });

    auto try_harder_to_alloc = [&](Candidate &c) {
      for (MCPhysReg newreg : X86::GR32_ABCDRegClass) {
        if (!ratool.unused_csr.test(newreg) &&
            ratool.reserve_phys_reg(newreg, *c.extra)) {
          return newreg;
        }
      }
      return static_cast<MCPhysReg>(0);
    };

    std::sort(cands.begin(), cands.end());
    for (Candidate &c : cands) {
      DEBUG(dbgs() << c << "\n");
      c.unassign(ratool);
      MCPhysReg newreg;
      if (!f.getSubtarget<X86Subtarget>().is64Bit() &&
          ((newreg = ratool.alloc(*c.extra, &X86::GR32_ABCDRegClass)) != 0 ||
           (newreg = try_harder_to_alloc(c)) != 0)) {
        DEBUG(dbgs() << "works\n");
        // one last check
        vector<LiveInterval *> evictees;
        if (ratool.interf(*c.extra, newreg, evictees)) {
          DEBUG(dbgs() << evictees);
          assert(false);
        }
        c.assign_new(lrm, li, newreg);
      } else if (f.getSubtarget<X86Subtarget>().is64Bit() &&
                 (newreg = ratool.alloc(*c.extra)) != 0) {
        DEBUG(dbgs() << "works\n");
        c.assign_new(lrm, li, newreg);
      } else {
        DEBUG(dbgs() << "could not transform\n");
        c.assign_old(lrm);
        dispose.push_back(std::move(c));
      }
    }

    for (Candidate &c : dispose) {
      DEBUG(dbgs() << "purging dummy instr: " << (*c.ins));
      li.RemoveMachineInstrFromMaps(*c.ins);
      c.ins->eraseFromParent();
    }
    return false;
  }
};

char X86FixupZExt::id = 0;
}

namespace llvm {
FunctionPass *createX86FixupZExt() { return new X86FixupZExt(); }
}
