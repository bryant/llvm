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

unsigned getPhys(unsigned Reg, const VirtRegMap &VRM) {
  return TargetRegisterInfo::isVirtualRegister(Reg) ? VRM.getPhys(Reg) : Reg;
}

unsigned getPhys(const MachineOperand &RegOp, const VirtRegMap &VRM) {
  const MachineFunction &MF = *RegOp.getParent()->getParent()->getParent();
  const TargetRegisterInfo &TRI = *MF.getSubtarget().getRegisterInfo();
  assert(RegOp.isReg());
  unsigned PReg = getPhys(RegOp.getReg(), VRM);
  return RegOp.getSubReg() ? TRI.getSubReg(PReg, RegOp.getSubReg()) : PReg;
}

unsigned getPhys(const MachineInstr &MI, unsigned Op, const VirtRegMap &VRM) {
  return getPhys(MI.getOperand(Op), VRM);
}

void eraseInstr(MachineInstr &MI, LiveIntervals &LI) {
  LI.RemoveMachineInstrFromMaps(MI);
  MI.eraseFromParent();
}

DenseMap<MachineBasicBlock *, MachineInstr *>
dominatingDefs(unsigned GR8, const MachineRegisterInfo &MRI,
               const SlotIndexes &SI) {
  DenseMap<MachineBasicBlock *, MachineInstr *> Defs;
  // at least until release_37, getInstructionIndex is expensive.
  DenseMap<MachineBasicBlock *, SlotIndex> Cached;

  for (MachineInstr &Def : MRI.def_instructions(GR8)) {
    unsigned TiedUse;
    if (Def.isRegTiedToUseOperand(0, &TiedUse) &&
        Def.getOperand(TiedUse).getReg() != Def.getOperand(0).getReg()) {
      DEBUG(dbgs() << "dominatingDefs: " << Def.getOperand(0) << " is tied to "
                   << Def.getOperand(TiedUse) << "\n");
      return dominatingDefs(Def.getOperand(TiedUse).getReg(), MRI, SI);
    }
    MachineBasicBlock *MBB = Def.getParent();
    if (Defs.find(MBB) == Defs.end() ||
        SI.getInstructionIndex(Def) < Cached.lookup(MBB)) {
      Cached[MBB] = SI.getInstructionIndex(Def);
      Defs[MBB] = &Def;
    }
  }
  return Defs;
}

void addSeg(SlotIndex s, SlotIndex e, LiveInterval &Live, LiveIntervals &LI) {
  assert(Live.vni_begin() != Live.vni_end());
  Live.addSegment(Segment(std::move(s), std::move(e), *Live.vni_begin()));
}

void addSeg(MachineInstr &s, MachineInstr &e, LiveInterval &Live,
            LiveIntervals &LI) {
  return addSeg(LI.getInstructionIndex(s), LI.getInstructionIndex(e), Live, LI);
}

void addSegs(LiveInterval &Src, LiveInterval &Dest, LiveIntervals &LI) {
  for (const Segment &s : Src) {
    addSeg(s.start, s.end, Dest, LI);
  }
}

bool mov32r0Segs(MachineInstr &Def8,
                 SmallVectorImpl<pair<MachineInstr *, MachineInstr *>> &Segs,
                 LiveIntervals &LI) {
  const MachineFunction &MF = *Def8.getParent()->getParent();
  const TargetRegisterInfo &TRI = *MF.getSubtarget().getRegisterInfo();
  MachineBasicBlock &MBB = *Def8.getParent();
  MachineBasicBlock::iterator Ins = &Def8;

  if (const Segment *eflagseg =
          LI.getRegUnit(*MCRegUnitIterator(X86::EFLAGS, &TRI))
              .getSegmentContaining(LI.getInstructionIndex(Def8))) {
    if (eflagseg->start <= LI.getInstructionIndex(*MBB.begin()) &&
        MBB.isLiveIn(X86::EFLAGS)) {
      if (MBB.pred_size() > 1) {
        return false;
      }
      Segs.push_back(make_pair(MBB.begin(), &Def8));
      return mov32r0Segs(*(*MBB.pred_begin())->rbegin(), Segs, LI);
    }
    Ins = LI.getInstructionFromIndex(eflagseg->start);
  }
  Segs.push_back(make_pair(Ins, &Def8));
  return true;
}

template <typename T, typename = is_iterable_of<LiveInterval *, T>>
raw_ostream &operator<<(raw_ostream &out, const T &Lives) {
  for (LiveInterval *e : Lives) {
    out << "\t" << (*e) << "\n";
  }
  return out;
}

template <typename T, typename = is_iterable_of<LiveInterval *, T>>
bool interferes(const T &as, const LiveInterval &b,
                const MachineRegisterInfo &MRI) {
  return any_of(as, [&](const LiveInterval *a) { return a->overlaps(b); });
}

struct ReAllocTool {
  const TargetRegisterInfo *TRI;
  const MachineRegisterInfo *MRI;
  LiveRegMatrix *LRM;
  VirtRegMap *VRM;
  RegisterClassInfo RCI;
  BitVector unused_csr;

  void addRegToBitVec(BitVector &BV, MCPhysReg Reg) const {
    for (MCRegAliasIterator r(Reg, TRI, true); r.isValid(); ++r) {
      BV.set(*r);
    }
  }

  BitVector bitVecFromRegs(ArrayRef<MCPhysReg> Regs) const {
    BitVector rv(TRI->getNumRegs());
    for (const MCPhysReg &r : Regs) {
      addRegToBitVec(rv, r);
    }
    return rv;
  }

  ReAllocTool(const MachineFunction &MF, LiveRegMatrix &LRM_, VirtRegMap &VRM_)
      : TRI(MF.getSubtarget().getRegisterInfo()), MRI(&MF.getRegInfo()),
        LRM(&LRM_), VRM(&VRM_), RCI(), unused_csr(TRI->getNumRegs()) {
    const MCPhysReg *csr = TRI->getCalleeSavedRegs(&MF);
    for (unsigned i = 0; csr[i] != 0; i += 1) {
      if (!LRM->isPhysRegUsed(csr[i])) {
        addRegToBitVec(unused_csr, csr[i]);
      }
    }
    RCI.runOnMachineFunction(MF);
  }

  bool interf(LiveInterval &Live, unsigned PReg) const {
    return LRM->checkInterference(Live, PReg) != LiveRegMatrix::IK_Free;
  }

  template <typename T, typename = is_iterable_of<LiveInterval *, T>>
  bool interf(LiveInterval &Live, unsigned PReg, T &Evictees) const {
    if (LRM->checkRegMaskInterference(Live, PReg) ||
        LRM->checkRegUnitInterference(Live, PReg)) {
      return true;
    }
    DenseSet<LiveInterval *> UniqueEv;
    for (MCRegUnitIterator regunit(PReg, TRI); regunit.isValid(); ++regunit) {
      LiveIntervalUnion::Query &q = LRM->query(Live, *regunit);
      if (q.collectInterferingVRegs() > 0) {
        for (LiveInterval *l : q.interferingVRegs()) {
          UniqueEv.insert(l);
        }
      }
    }
    std::copy(UniqueEv.begin(), UniqueEv.end(), back_inserter(Evictees));
    return Evictees.size() > 0;
  }

  const MCPhysReg *allocNext(LiveInterval &Live,
                             const BitVector *Except = nullptr,
                             ArrayRef<MCPhysReg>::iterator *it = nullptr,
                             const TargetRegisterClass *TRC = nullptr) const {
    ArrayRef<MCPhysReg> Ord =
        RCI.getOrder(TRC ? TRC : MRI->getRegClass(Live.reg));
    BitVector rs = unused_csr;
    if (Except) {
      rs |= *Except;
    }
    auto rv = std::find_if(
        it ? std::next(*it) : Ord.begin(), Ord.end(),
        [&](MCPhysReg r) { return !rs.test(r) && !interf(Live, r); });
    return rv == Ord.end() ? nullptr : rv;
  }

  MCPhysReg alloc(LiveInterval &Live, const BitVector *Except = nullptr,
                  const TargetRegisterClass *TRC = nullptr) const {
    const MCPhysReg *rv = allocNext(Live, Except, nullptr, TRC);
    return rv ? 0 : *rv;
  }

  // (re-)allocate a group of interfering intervals. brute force search. returns
  // nullptr if impossible.
  template <typename C, typename = is_iterable_of<LiveInterval *, C>>
  unique_ptr<vector<pair<LiveInterval *, const MCPhysReg *>>>
  allocInterfIntervals(C Group, const BitVector *Except = nullptr) const {
    if (Group.empty()) {
      return make_unique<vector<pair<LiveInterval *, const MCPhysReg *>>>();
    }
    auto Assigned =
        make_unique<vector<pair<LiveInterval *, const MCPhysReg *>>>();

    auto maybeUnassign = [&](pair<LiveInterval *, const MCPhysReg *> &P) {
      if (P.second) {
        LRM->unassign(*P.first);
      }
    };

    auto maybeAssign = [&](pair<LiveInterval *, const MCPhysReg *> &P) {
      if (P.second) {
        LRM->assign(*P.first, *P.second);
      }
    };

    auto tryNextInGroup = [&]() {
      assert(!Group.empty());
      Assigned->push_back(
          std::make_pair(Group.back(), allocNext(*Group.back(), Except)));
      Group.pop_back();
      maybeAssign(Assigned->back());
    };

    auto backToPrevious = [&]() {
      assert(!Assigned->empty());
      maybeUnassign(Assigned->back());
      Group.push_back(Assigned->back().first);
      Assigned->pop_back();
    };

    auto tryNextReg = [&]() {
      assert(!Assigned->empty());
      maybeUnassign(Assigned->back());
      Assigned->back().second =
          allocNext(*Assigned->back().first, Except, &Assigned->back().second);
      maybeAssign(Assigned->back());
    };

    tryNextInGroup();

    while (!Group.empty() || !Assigned->back().second) {
      if (Assigned->back().second) {
        tryNextInGroup();
      } else {
        backToPrevious();
        if (Assigned->empty()) {
          return nullptr;
        }
        tryNextReg();
      }
    }
    for (pair<LiveInterval *, const MCPhysReg *> &P : *Assigned) {
      LRM->unassign(*P.first);
    }
    return Assigned;
  }

  template <typename C, typename = is_iterable_of<LiveInterval *, C>>
  unique_ptr<vector<MCPhysReg>>
  evictIntervals(const C &Lives, const BitVector *Excepts = nullptr) const {
    DenseMap<LiveInterval *, const MCPhysReg *> NewAssigns;
    vector<LiveInterval *> Ungrouped(Lives.begin(), Lives.end());

    while (!Ungrouped.empty()) {
      vector<LiveInterval *> Group;
      Group.push_back(Ungrouped.back());
      Ungrouped.pop_back();
      bool Done = false;
      while (!Done) {
        auto it = std::partition(
            Ungrouped.begin(), Ungrouped.end(),
            [&](LiveInterval *h) { return !interferes(Group, *h, *MRI); });
        Done = it == Ungrouped.end();
        std::copy(it, Ungrouped.end(), back_inserter(Group));
        Ungrouped.erase(it, Ungrouped.end());
      }
      if (auto n = allocInterfIntervals(Group, Excepts)) {
        for (pair<LiveInterval *, const MCPhysReg *> pair_ : *n) {
          NewAssigns.insert(pair_);
        }
      } else {
        return nullptr;
      }
    }
    auto rv = make_unique<vector<MCPhysReg>>();
    transform(Lives, back_inserter(*rv),
              [&](LiveInterval *l) { return *NewAssigns[l]; });
    return rv;
  }

  MCPhysReg unassign(LiveInterval &Live) {
    unsigned Old = getPhys(Live.reg, *VRM);
    LRM->unassign(Live);
    return Old;
  }

  template <typename C, typename = is_iterable_of<LiveInterval *, C>>
  vector<MCPhysReg> unassignAll(C &Lives) {
    vector<MCPhysReg> OldRegs;
    transform(Lives, back_inserter(OldRegs),
              [&](LiveInterval *l) { return unassign(*l); });
    return OldRegs;
  }

  template <typename C, typename D,
            typename = is_iterable_of<LiveInterval *, C>,
            typename = is_iterable_of<MCPhysReg, D>>
  void assignAll(C &Lives, D &&Regs) {
    for (auto intv_reg : zip_first(Lives, std::forward<D>(Regs))) {
      LRM->assign(*std::get<0>(intv_reg), std::get<1>(intv_reg));
    }
  }

  bool reservePhysReg(MCPhysReg PReg, LiveInterval &Live) {
    vector<LiveInterval *> Evictees;
    if (!interf(Live, PReg, Evictees)) {
      DEBUG(dbgs() << "ReAllocTool: " << TRI->getName(PReg)
                   << " is already free.\n");
      return true;
    } else if (Evictees.size() > 0) {
      DEBUG(dbgs() << "ReAllocTool: trying to reserve " << TRI->getName(PReg)
                   << " by evicting:\n"
                   << Evictees);
      vector<MCPhysReg> OldRegs = unassignAll(Evictees);
      BitVector bv = bitVecFromRegs(PReg);
      if (auto NewRegs = evictIntervals(Evictees, &bv)) {
        assignAll(Evictees, *NewRegs);
        return true;
      }
      assignAll(Evictees, OldRegs);
    }
    DEBUG(dbgs() << "ReAllocTool: unable to reserve " << TRI->getName(PReg)
                 << "\n");
    return false;
  }
};

struct Candidate {
  MachineInstr *ins;
  MachineInstr *gr8def;
  MachineInstr *movzx;
  LiveIntervals *LI;
  LiveInterval *live32;
  LiveInterval *live8;
  unique_ptr<LiveInterval> extra;
  vector<MCPhysReg> constraints;

private:
  // used to cache originally assigned registers for live32 and live8.
  unsigned pdest;
  unsigned psrc;

public:
  static MachineInstr *validCandidate(MachineInstr &MI, LiveIntervals &LI) {
    if (MI.getOpcode() != X86::MOVZX32rr8 ||
        MI.getOperand(1).getSubReg() != 0) {
      return nullptr;
    }

    const MachineFunction &MF = *MI.getParent()->getParent();
    const MachineRegisterInfo &MRI = MF.getRegInfo();
    const TargetRegisterInfo &TRI = *MF.getSubtarget().getRegisterInfo();

    unsigned Src = MI.getOperand(1).getReg();
    auto bbdefs = dominatingDefs(Src, MRI, *LI.getSlotIndexes());
    if (bbdefs.size() > 1 || (MRI.getSimpleHint(Src) &&
                              !TRI.isVirtualRegister(MRI.getSimpleHint(Src)))) {
      DEBUG(dbgs() << "passing over " << MI << "defs: " << bbdefs.size()
                   << ", gr8 hint: " << PrintReg(MRI.getSimpleHint(Src), &TRI)
                   << "\n");
      return nullptr;
    }
    return bbdefs.begin()->second;
  }

  Candidate(const SmallVectorImpl<pair<MachineInstr *, MachineInstr *>> &Segs,
            MachineInstr &GR8, MachineInstr &Movzx_,
            const TargetRegisterInfo &TRI, LiveIntervals &LI_)
      : ins(nullptr), gr8def(&GR8), movzx(&Movzx_), LI(&LI_),
        live32(&LI->getInterval(movzx->getOperand(0).getReg())),
        live8(&LI->getInterval(movzx->getOperand(1).getReg())),
        extra(new LiveInterval(live32->reg, live32->weight)), constraints() {
    MachineBasicBlock &MBB = *Segs.front().first->getParent();
    const TargetInstrInfo &TII =
        *MBB.getParent()->getSubtarget().getInstrInfo();
    ins = BuildMI(MBB, Segs.front().first, movzx->getDebugLoc(),
                  TII.get(X86::MOV32r0), 0);
    LI->InsertMachineInstrInMaps(*ins);
    extra->getNextValue(LI->getInstructionIndex(*ins),
                        LI->getVNInfoAllocator());
    addSeg(*ins, *Segs.front().second, *extra, *LI);
    for (auto P : make_range(std::next(Segs.begin()), Segs.end())) {
      addSeg(*P.first, *P.second, *extra, *LI);
    }
  }

  ~Candidate() {
    if (ins) {
      eraseInstr(*ins, *LI);
    }
  }

  Candidate(Candidate &&C)
      : ins(C.ins), gr8def(C.gr8def), movzx(C.movzx), LI(C.LI),
        live32(C.live32), live8(C.live8), extra(std::move(C.extra)),
        constraints(std::move(C.constraints)) {
    C.ins = nullptr;
  }

  Candidate &operator=(Candidate &&C) {
    ins = C.ins;
    gr8def = C.gr8def;
    movzx = C.movzx;
    live32 = C.live32;
    live8 = C.live8;
    LI = C.LI;
    extra = std::move(C.extra);
    constraints = std::move(C.constraints);
    C.ins = nullptr;
    return *this;
  }

  static unique_ptr<Candidate> fromMI(MachineInstr &MI, LiveIntervals &LI,
                                      const VirtRegMap &VRM) {
    const MachineFunction &MF = *MI.getParent()->getParent();
    const MachineRegisterInfo &MRI = MF.getRegInfo();
    const TargetRegisterInfo &TRI = *MF.getSubtarget().getRegisterInfo();

    MachineInstr *Def8;
    SmallVector<pair<MachineInstr *, MachineInstr *>, 4> Segs;
    if (!(Def8 = validCandidate(MI, LI)) || !mov32r0Segs(*Def8, Segs, LI)) {
      return nullptr;
    }

    Candidate C(Segs, *Def8, MI, TRI, LI);
    if (C.live32->overlaps(*C.extra)) {
      return nullptr;
    }

    addSegs(*C.live32, *C.extra, LI);
    addSegs(*C.live8, *C.extra, LI);

    unsigned Dest = MI.getOperand(0).getReg();
    // look for copy instr reg alloc hints
    for (const MachineInstr &Use : MRI.use_instructions(Dest)) {
      if (Use.isCopy()) {
        if (unsigned Hint =
                getPhys(VirtRegAuxInfo::copyHint(&Use, Dest, TRI, MRI), VRM)) {
          C.constraints.push_back(Hint);
        }
      }
    }

    // look for regmask constraints if no hints were found
    if (C.constraints.empty()) {
      BitVector RegMask;
      if (LI.checkRegMaskInterference(*C.extra, RegMask)) {
        const TargetRegisterClass &DestCls = *MRI.getRegClass(Dest);
        copy_if(DestCls.begin(), DestCls.end(), back_inserter(C.constraints),
                [&](MCPhysReg r) { return RegMask.test(r); });
      }
    }
    return make_unique<Candidate>(std::move(C));
  }

  bool operator<(const Candidate &C) const {
    if (constraints.size() > 0 && C.constraints.size() == 0)
      return true;
    if (C.constraints.size() > 0 && constraints.size() == 0)
      return false;
    if (constraints.size() < C.constraints.size())
      return true;
    return li_size() > C.li_size();
  }

  unsigned li_size() const { return extra->getSize(); }

  friend raw_ostream &operator<<(raw_ostream &out, const Candidate &C) {
    out << "Candidate:\n\tinserted: " << (*C.ins)
        << "\tgr8 def: " << (*C.gr8def) << "\tmovzx: " << (*C.movzx)
        << "\txor gr32: " << (*C.extra);
    if (C.constraints.size() > 0) {
      out << "\n\tconstraints:";
      for (unsigned cx : C.constraints) {
        out << " " << PrintReg(cx, &C.TRI());
      }
    } else {
      out << "\n\tno constraints.";
    }
    return out;
  }

  const X86RegisterInfo &TRI() const {
    return *reinterpret_cast<const X86RegisterInfo *>(
        ins->getParent()->getParent()->getSubtarget().getRegisterInfo());
  }

  const X86InstrInfo &TII() const {
    return *reinterpret_cast<const X86InstrInfo *>(
        ins->getParent()->getParent()->getSubtarget().getInstrInfo());
  }

  MachineRegisterInfo &MRI() const {
    return ins->getParent()->getParent()->getRegInfo();
  }

  void unassign(ReAllocTool &RATool) {
    pdest = RATool.unassign(*live32);
    psrc = RATool.unassign(*live8);
  }

  void assignOld(LiveRegMatrix &LRM) {
    LRM.assign(*live32, pdest);
    LRM.assign(*live8, psrc);
    pdest = psrc = 0;
  }

  void assignNew(LiveRegMatrix &LRM, MCPhysReg NewDest) {
    // VSrc uses => VDest:sub_8bit; insert VDest = mov32r0; del movzx
    unsigned VDest = movzx->getOperand(0).getReg();
    unsigned VSrc = movzx->getOperand(1).getReg();

    // in-place operand mutation would confuse defusechain_iterator
    vector<MachineOperand *> Ops;
    transform(MRI().reg_operands(VSrc), back_inserter(Ops),
              [](MachineOperand &Op) { return &Op; });
    for (MachineOperand *Op : Ops) {
      DEBUG(dbgs() << "changing " << (*Op->getParent()));
      Op->substVirtReg(VDest, X86::sub_8bit, TRI());
      DEBUG(dbgs() << "to " << (*Op->getParent()));
    }

    eraseInstr(*movzx, *LI);
    LI->removeInterval(VSrc);
    LI->removeInterval(VDest);

    const TargetRegisterClass &DestCls = *MRI().getRegClass(VDest);
    ins->getOperand(0).setReg(VDest);
    if (DestCls.getSize() > 32 / 8) {
      ins->getOperand(0).setSubReg(X86::sub_32bit);
      ins->getOperand(0).setIsUndef();
    }
    if (const TargetRegisterClass *NewCls = gr8def->getRegClassConstraintEffect(
            0, ins->getRegClassConstraintEffect(0, &DestCls, &TII(), &TRI()),
            &TII(), &TRI())) {
      DEBUG(dbgs() << "updating reg class from "
                   << TRI().getRegClassName(&DestCls) << " to "
                   << TRI().getRegClassName(NewCls) << "\n");
      MRI().setRegClass(VDest, NewCls);
    } else {
      DEBUG(dbgs() << "not updating reg class\n");
    }
    LI->removeInterval(VDest);
    LRM.assign(LI->createAndComputeVirtRegInterval(VDest), NewDest);
    ins = nullptr; // prevent erasure of mov32r0 by dtor
  }

  bool validDestReg(MCPhysReg PReg) const {
    return MRI().getRegClass(movzx->getOperand(0).getReg())->contains(PReg);
  }
};

struct X86FixupZExt : public MachineFunctionPass {
  static char id;

  X86FixupZExt() : MachineFunctionPass(id) {}

  const char *getPassName() const override {
    return "X86 Zero-Extension Fix-up";
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<LiveRegMatrix>();
    AU.addRequired<VirtRegMap>();
    AU.addRequired<LiveIntervals>();
    AU.setPreservesAll();
    return MachineFunctionPass::getAnalysisUsage(AU);
  }

  bool runOnMachineFunction(MachineFunction &MF) override {
    VirtRegMap &VRM = getAnalysis<VirtRegMap>();
    LiveIntervals &LI = getAnalysis<LiveIntervals>();
    LiveRegMatrix &LRM = getAnalysis<LiveRegMatrix>();
    vector<Candidate> Constrained, Cands;
    ReAllocTool RATool(MF, LRM, VRM);

    DEBUG(dbgs() << "analyzing " << MF.getName() << "'s movzxes.\n");
    for (MachineBasicBlock &MBB : MF) {
      for (MachineInstr &MI : MBB) {
        if (auto Cand = Candidate::fromMI(MI, LI, VRM)) {
          if (Cand->constraints.size() > 0) {
            Constrained.push_back(std::move(*Cand.release()));
          } else {
            Cands.push_back(std::move(*Cand.release()));
          }
        }
      }
    }

    BitVector NoSub8;
    if (MF.getSubtarget<X86Subtarget>().is64Bit()) {
      NoSub8 = RATool.bitVecFromRegs({X86::RIP});
    } else {
      NoSub8 = RATool.bitVecFromRegs(ArrayRef<MCPhysReg>(
          X86::GR32_ABCDRegClass.begin(), X86::GR32_ABCDRegClass.end()));
      NoSub8.flip();
    }

    auto reserveOneOf = [&](ArrayRef<MCPhysReg> Regs, const Candidate &C) {
      for (MCPhysReg PReg : Regs) {
        if (!NoSub8.test(PReg) && C.validDestReg(PReg) &&
            !RATool.unused_csr.test(PReg) &&
            RATool.reservePhysReg(PReg, *C.extra)) {
          return PReg;
        }
      }
      return static_cast<MCPhysReg>(0);
    };

    DEBUG(VRM.print(dbgs()));
    DEBUG(MF.print(dbgs(), LI.getSlotIndexes()));
    std::sort(Constrained.begin(), Constrained.end());
    for (Candidate &C : Constrained) {
      DEBUG(dbgs() << C << "\n");
      C.unassign(RATool);
      if (MCPhysReg NewReg = reserveOneOf(C.constraints, C)) {
        DEBUG(dbgs() << "works\n");
        C.assignNew(LRM, NewReg);
      } else {
        C.assignOld(LRM);
        if (none_of(C.constraints, [&](MCPhysReg PReg) {
              return PReg == getPhys(*C.movzx, 0, VRM);
            })) {
          // only demote if RA pass missed all hints
          C.constraints.clear();
          DEBUG(dbgs() << "demoting to unconstrained candidate\n");
          Cands.push_back(std::move(C));
        } else {
          DEBUG(dbgs() << "could not transform\n");
        }
      }
    }

    std::sort(Cands.begin(), Cands.end());
    for (Candidate &C : Cands) {
      DEBUG(dbgs() << C << "\n");
      C.unassign(RATool);
      MCPhysReg NewReg;
      if (!MF.getSubtarget<X86Subtarget>().is64Bit() &&
          ((NewReg = RATool.alloc(*C.extra, &NoSub8)) != 0 ||
           (NewReg =
                reserveOneOf(ArrayRef<MCPhysReg>(X86::GR32_ABCDRegClass.begin(),
                                                 X86::GR32_ABCDRegClass.end()),
                             C)) != 0)) {
        DEBUG(dbgs() << "works\n");
        C.assignNew(LRM, NewReg);
      } else if (MF.getSubtarget<X86Subtarget>().is64Bit() &&
                 (NewReg = RATool.alloc(*C.extra, &NoSub8)) != 0) {
        DEBUG(dbgs() << "works\n");
        C.assignNew(LRM, NewReg);
      } else {
        DEBUG(dbgs() << "could not transform\n");
        C.assignOld(LRM);
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
