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

MachineInstr *find_ins(MachineInstr &bottom, vector<Segment> &segments,
                       LiveIntervals &li) {
  auto slot = [&](MachineInstr &i) { return li.getInstructionIndex(i); };
  const MachineFunction &f = *bottom.getParent()->getParent();
  const auto &tri = f.getSubtarget().getRegisterInfo();
  MachineBasicBlock &bb = *bottom.getParent();
  MachineBasicBlock::iterator ins = &bottom;
  for (; ins != bb.begin(); --ins) {
    SlotIndex s = slot(*ins);
    if (!li.getRegUnit(*MCRegUnitIterator(X86::EFLAGS, tri)).liveAt(s)) {
      break;
    }
  }
  if (ins == bb.begin() && bb.isLiveIn(X86::EFLAGS)) {
    if (bb.pred_size() > 1) {
      return nullptr;
    }
    segments.push_back(Segment(li.getMBBStartIdx(&bb), slot(bottom), nullptr));
    return find_ins(*(*bb.pred_begin())->rbegin(), segments, li);
  }
  // insert dummy mov32r0
  MachineInstrBuilder mib =
      BuildMI(bb, ins, bottom.getDebugLoc(),
              f.getSubtarget().getInstrInfo()->get(X86::MOV32r0), 0);
  li.InsertMachineInstrInMaps(*mib);
  segments.push_back(Segment(slot(*mib), slot(bottom), nullptr));
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

bool phys_reg_used(unsigned reg, const TargetRegisterInfo &tri,
                   LiveIntervals &li) {
  for (MCRegUnitIterator u(reg, &tri); u.isValid(); ++u) {
    if (!li.getRegUnit(*u).empty()) {
      return true;
    }
  }
  return false;
}

unsigned maybe_id_copy(unsigned vreg, const MachineRegisterInfo &mri,
                       const VirtRegMap &vrm) {
  auto test = [&](const MachineInstr &i) {
    const MachineFunction &f = *i.getParent()->getParent();
    const TargetRegisterInfo &tri = *f.getSubtarget().getRegisterInfo();
    return i.isCopy() &&
           get_phys(i.getOperand(1), vrm) == get_phys(i.getOperand(0), vrm);
  };
  return any_of(mri.use_instr_begin(vreg), mri.use_instr_end(), test);
}

bool disjoint_ranges(unsigned vreg0, unsigned vreg1, LiveIntervals &li) {
  if (!TargetRegisterInfo::isVirtualRegister(vreg0) ||
      !TargetRegisterInfo::isVirtualRegister(vreg1)) {
    // assume non-disjoint
    return false;
  }
  return !li.getInterval(vreg0).overlaps(li.getInterval(vreg1));
}

BitVector allocatable_regs(const MachineFunction &f, const LiveRegMatrix &lrm) {
  const X86RegisterInfo &tri = *reinterpret_cast<const X86RegisterInfo *>(
      f.getSubtarget().getRegisterInfo());
  BitVector unusable = f.getRegInfo().getReservedRegs();
  auto set = [&unusable, &tri](unsigned r) {
    for (MCRegAliasIterator u(r, &tri, true); u.isValid(); ++u) {
      unusable.set(*u);
    }
  };
  const MCPhysReg *csr = tri.getCalleeSavedRegs(&f);
  for (unsigned i = 0; csr[i] != 0; i += 1) {
    if (!lrm.isPhysRegUsed(csr[i])) {
      set(csr[i]);
    }
  }
  unusable.flip();
  return unusable;
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
    llvm::copy(ev, push_to(evictees));
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
  alloc_intervals(const C &lives, ArrayRef<MCPhysReg> excepts) const {
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
};

struct Candidate {
  MachineInstr *ins;
  MachineInstr *gr8def;
  MachineInstr *movzx;
  unsigned pdest;
  unsigned psrc;
  vector<MCPhysReg> constraints;
  LiveInterval *live32;
  LiveInterval *live8;
  unique_ptr<LiveInterval> extra;

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
        (ins = find_ins(*def, xorlive, li)) == nullptr) {
      return nullptr;
    }

    unsigned dest = i.getOperand(0).getReg(), src = i.getOperand(1).getReg();
    // look for reg alloc copy instr hints
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

    return unique_ptr<Candidate>(
        new Candidate{ins, def, &i, get_phys(dest, vrm), get_phys(src, vrm),
                      std::move(cx), &live32, &live8, std::move(extra)});
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

  void unassign(LiveRegMatrix &lrm) {
    lrm.unassign(*live32);
    lrm.unassign(*live8);
  }

  void assign_old(LiveRegMatrix &lrm) {
    lrm.assign(*live32, pdest);
    lrm.assign(*live8, psrc);
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
      DEBUG(dbgs() << "changing " << (*op));
      op->substVirtReg(vdest, X86::sub_8bit, get_tri());
      DEBUG(dbgs() << " to " << (*op) << "\n");
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

BitVector bitvec_from_reg(unsigned preg, const TargetRegisterInfo &tri) {
  BitVector rv(tri.getNumRegs());
  for (MCRegAliasIterator reg(preg, &tri, true); reg.isValid(); ++reg) {
    rv.set(*reg);
  }
  return rv;
}

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
    const MachineRegisterInfo &mri = f.getRegInfo();
    const TargetRegisterInfo &tri = *f.getSubtarget().getRegisterInfo();
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
      c.unassign(lrm);
      bool demote = true;
      for (MCPhysReg preg : c.constraints) {
        DEBUG(dbgs() << "trying to remap to " << tri.getName(preg) << "\n");
        vector<LiveInterval *> evictees;
        if (!ratool.interf(*c.extra, preg, evictees)) {
          DEBUG(dbgs() << "works\n");
          c.assign_new(lrm, li, preg);
          return;
        } else if (evictees.size() > 0) {
          DEBUG(dbgs() << "attempting to evict: " << evictees);
          vector<MCPhysReg> oldregs = ratool.unassign_all(evictees);
          if (auto newregs = ratool.alloc_intervals(evictees, {preg})) {
            DEBUG(dbgs() << "works\n");
            ratool.assign_all(evictees, *newregs);
            c.assign_new(lrm, li, preg);
            return;
          } else {
            // how depressing.
            ratool.assign_all(evictees, oldregs);
          }
        }
        demote &= preg != c.pdest; // only demote if RA pass missed all hints
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
        vector<LiveInterval *> evictees;
        if (!ratool.unused_csr.test(newreg)) {
          DEBUG(dbgs() << "try_harder_to_alloc: trying " << tri.getName(newreg)
                       << "\n");
          if (!ratool.interf(*c.extra, newreg, evictees)) {
            return newreg;
          } else if (evictees.size() > 0) {
            DEBUG(dbgs() << "trying to reserve " << tri.getName(newreg)
                         << " by evicting:\n"
                         << evictees);
            vector<MCPhysReg> oldregs = ratool.unassign_all(evictees);
            if (auto newregs = ratool.alloc_intervals(evictees, {newreg})) {
              DEBUG(dbgs() << "found new assignment\n");
              ratool.assign_all(evictees, *newregs);
              return newreg;
            }
            DEBUG(dbgs() << "couldn't re-alloc evictees\n");
            ratool.assign_all(evictees, oldregs);
          }
        }
      }
      return static_cast<MCPhysReg>(0);
    };

    std::sort(cands.begin(), cands.end());
    for (Candidate &c : cands) {
      DEBUG(dbgs() << c << "\n");
      c.unassign(lrm);
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

struct MarkZExt : public MachineFunctionPass {
  static char id;

  MarkZExt() : MachineFunctionPass(id) {}

  const char *getPassName() const override { return "x86 movzx32rr8 hints"; }

  void getAnalysisUsage(AnalysisUsage &a) const override {
    a.addRequired<LiveIntervals>();
    a.setPreservesAll();
    return MachineFunctionPass::getAnalysisUsage(a);
  }

  bool runOnMachineFunction(MachineFunction &f) override {
    MachineRegisterInfo &mri = f.getRegInfo();
    const X86RegisterInfo &tri = *reinterpret_cast<const X86RegisterInfo *>(
        f.getSubtarget<X86Subtarget>().getRegisterInfo());
    LiveIntervals &li = getAnalysis<LiveIntervals>();

    for (MachineBasicBlock &bb : f) {
      for (MachineInstr &i : bb) {
        /*MachineInstr &use = *mri.use_instr_begin(gr32);
        if (use.isCopy()) {
          dbgs() << "found a copy use: " << use;
          if (unsigned hintedgr32 =
                  VirtRegAuxInfo::copyHint(&use, gr32, tri, mri)) {
            dbgs() << "found a hint for " << PrintReg(gr32, &tri) << "! "
                   << PrintReg(hintedgr32, &tri) << "\n";
            if (unsigned hintedgr8 =
                    tri.getSubReg(hintedgr32, X86::sub_8bit)) {
              dbgs() << "hinting " << PrintReg(hintedgr8, &tri) << " for "
                     << PrintReg(gr8, &tri) << "\n";
              mri.setSimpleHint(gr8, hintedgr8);
            }
          }
        } else {
           dbgs() << "hinting arbitrarily\n";
           mri.setRegAllocationHint(gr32, X86Hint::ParentGR32, gr8);
           mri.setRegAllocationHint(gr8, X86Hint::SubGR8, gr32);
         }*/
      }
    }
    return false;
  }
};

char MarkZExt::id = 0;

MachineInstr *find_def(unsigned reg, const MachineRegisterInfo &mri,
                       LiveIntervals &li) {
  MachineInstr *rv = &*mri.def_instr_begin(reg);
  SlotIndex s = li.getInstructionIndex(*rv);
  dbgs() << "finding def for " << PrintReg(reg) << "\n";
  for (MachineInstr &def : mri.def_instructions(reg)) {
    unsigned tied_use;
    if (def.isPHI() || (def.isCopy() && def.getOperand(1).getSubReg() != 0)) {
      dbgs() << "unacceptable def: " << def;
      return nullptr;
    } else if (def.isRegTiedToUseOperand(0, &tied_use) &&
               def.getOperand(tied_use).getReg() !=
                   def.getOperand(0).getReg()) {
      dbgs() << "found tied def: " << def;
      return find_def(def.getOperand(tied_use).getReg(), mri, li);
    } else if (li.getInstructionIndex(def) < s) {
      rv = &def;
      s = li.getInstructionIndex(def);
    }
  }
  return rv;
}

struct ZExtRepair : public MachineFunctionPass {
  static char id;

  ZExtRepair() : MachineFunctionPass(id) {}

  const char *getPassName() const override {
    return "x86 zext repair (actually marks all movzx as insert_subreg)";
  }

  void getAnalysisUsage(AnalysisUsage &a) const override {
    a.addRequired<LiveIntervals>();
    a.setPreservesCFG();
    // a.setPreservesAll();
    return MachineFunctionPass::getAnalysisUsage(a);
  }

  bool runOnMachineFunction(MachineFunction &f) override {
    MachineRegisterInfo &mri = f.getRegInfo();
    const X86RegisterInfo &tri = *reinterpret_cast<const X86RegisterInfo *>(
        f.getSubtarget<X86Subtarget>().getRegisterInfo());
    const TargetInstrInfo &tii = *f.getSubtarget<X86Subtarget>().getInstrInfo();
    LiveIntervals &li = getAnalysis<LiveIntervals>();

    vector<std::pair<MachineInstr *, MachineInstr *>> queue;

    for (MachineBasicBlock &bb : f) {
      for (MachineInstr &i : bb) {
        if (i.getOpcode() != X86::MOVZX32rr8 ||
            i.getOperand(1).getSubReg() != 0) {
          continue;
        }
        MachineInstr *def8 = find_def(i.getOperand(1).getReg(), mri, li);
        if (def8 == nullptr) {
          continue;
        }

        dbgs() << "expanding " << i;

        // auto insdefs = insertion_points_for<4>(i.getOperand(1).getReg(), f,
        // li);
        //// TODO: run transform for all dominating gr8 defs.
        // if (insdefs.size() > 1) {
        //  dbgs() << "ignoring " << i << "as it has multiple dom defs:\n";
        //  for (auto ins_defs : insdefs) {
        //    dbgs() << "\t" << (*ins_defs.first) << "for "
        //           << (*ins_defs.second[0]);
        //  };
        //  continue;
        //}
        // queue.push_back(std::make_pair(insdefs.begin()->first, &i));
      }
    }

    const TargetRegisterClass *gr32c = f.getSubtarget<X86Subtarget>().is64Bit()
                                           ? &X86::GR32RegClass
                                           : &X86::GR32_ABCDRegClass;
    for (auto ins_zext : queue) {
      MachineInstr *ins = ins_zext.first;
      MachineInstr *i = ins_zext.second;
      unsigned gr32 = mri.createVirtualRegister(gr32c);
      unsigned inserted = mri.createVirtualRegister(gr32c);
      dbgs() << "inserting xor before " << (*ins);
      BuildMI(*ins->getParent(), ins, i->getDebugLoc(), tii.get(X86::MOV32r0),
              gr32);
      dbgs() << "inserting insert_subreg before " << (*i);
      BuildMI(*i->getParent(), i, i->getDebugLoc(), tii.get(X86::INSERT_SUBREG),
              inserted)
          .addReg(gr32)
          .addReg(i->getOperand(1).getReg())
          .addImm(X86::sub_8bit);
      mri.replaceRegWith(i->getOperand(0).getReg(), inserted);
      i->eraseFromParent();
    }
    return false;
  }
};

char ZExtRepair::id = 0;
}

namespace llvm {
FunctionPass *createX86FixupZExt() { return new X86FixupZExt(); }
FunctionPass *createMarkZExt() { return new MarkZExt(); }
FunctionPass *createZExtRepair() { return new ZExtRepair(); };
}
