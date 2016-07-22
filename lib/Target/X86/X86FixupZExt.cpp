#include "X86Subtarget.h"
#include "llvm/CodeGen/CalcSpillWeights.h"
#include "llvm/CodeGen/LiveIntervalAnalysis.h"
#include "llvm/CodeGen/LivePhysRegs.h"
#include "llvm/CodeGen/LiveRegMatrix.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/VirtRegMap.h"

#define DEBUG_TYPE "x86-fixup-zext"

namespace {
using namespace llvm;

bool live_at(const SlotIndex &s, const LiveRange &range) {
  using Segment = LiveRange::Segment;
  return std::any_of(range.begin(), range.end(),
                     [&](const Segment &seg) { return seg.contains(s); });
}

unsigned get_phys(unsigned reg, const VirtRegMap &vrm) {
  return TargetRegisterInfo::isVirtualRegister(reg) ? vrm.getPhys(reg) : reg;
}

bool free_within(const SlotIndex &start, const SlotIndex &end, unsigned gr32,
                 unsigned gr8, const TargetRegisterInfo &tri,
                 LiveIntervals &li) {
  dbgs() << "free_within called on " << start << ", " << end << "\n";
  unsigned gr8unit = *MCRegUnitIterator(gr8, &tri);
  for (MCRegUnitIterator sub(gr32, &tri); sub.isValid(); ++sub) {
    if (*sub != gr8unit && li.getRegUnit(*sub).overlaps(start, end)) {
      return false;
    }
  }
  return true;
}

MachineInstr *insertion_point_for(MachineInstr &i,
                                  const MachineRegisterInfo &mri,
                                  const TargetRegisterInfo &tri,
                                  LiveIntervals &li, const VirtRegMap &vrm) {
  SlotIndex e = li.getInstructionIndex(i);
  unsigned gr8 = i.getOperand(1).getReg();
  // insert before ins.
  MachineBasicBlock::iterator ins =
      &*mri.def_instr_begin(i.getOperand(1).getReg());
  while (true) {
    SlotIndex s = li.getInstructionIndex(*ins);
    if (!live_at(s, li.getRegUnit(*MCRegUnitIterator(X86::EFLAGS, &tri))) &&
        !live_at(s, li.getRegUnit(*MCRegUnitIterator(gr8, &tri))) &&
        free_within(s, e, get_phys(i.getOperand(0).getReg(), vrm), gr8, tri,
                    li)) {
      return ins;
    }

    if (ins == i.getParent()->begin()) {
      break;
    } else {
      --ins;
    }
  }
  return nullptr;
}

void print_units(unsigned reg, const TargetRegisterInfo &tri,
                 LiveIntervals &li) {
  for (MCRegUnitIterator u(reg, &tri); u.isValid(); ++u) {
    dbgs() << "unit (" << tri.getName(reg) << "): " << (*u) << " => "
           << li.getRegUnit(*u) << "\n";
  }
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

bool used_in_identity_copy(unsigned vreg, const MachineRegisterInfo &mri,
                           const VirtRegMap &vrm) {
  return any_of(mri.use_instr_begin(vreg), mri.use_instr_end(),
                [&](const MachineInstr &i) {
                  return i.isCopy() &&
                         get_phys(i.getOperand(1).getReg(), vrm) ==
                             get_phys(i.getOperand(0).getReg(), vrm) &&
                         i.getOperand(1).getSubReg() ==
                             i.getOperand(0).getSubReg();
                });
}

bool disjoint_ranges(unsigned vreg0, unsigned vreg1, LiveIntervals &li) {
  if (!TargetRegisterInfo::isVirtualRegister(vreg0) ||
      !TargetRegisterInfo::isVirtualRegister(vreg1)) {
    // assume non-disjoint
    return false;
  }
  return !li.getInterval(vreg0).overlaps(li.getInterval(vreg1));
}

void compute_zext_dests(SmallVectorImpl<unsigned> &gr32s,
                        const X86RegisterInfo &tri,
                        const MachineRegisterInfo &mri) {
  BitVector reserved = mri.getReservedRegs();
  auto set = [&reserved, &tri](unsigned r) {
    for (MCRegAliasIterator u(r, &tri, true); u.isValid(); ++u) {
      dbgs() << "reserving " << tri.getName(*u) << "\n";
      reserved.set(*u);
    }
  };
  set(tri.getStackRegister());
  set(tri.getBaseRegister());
  // set(tri.getFrameRegister());

  for (unsigned reg = X86::NoRegister + 1; reg < X86::NUM_TARGET_REGS;
       reg += 1) {
    if (!reserved.test(reg) && X86::GR32RegClass.contains(reg) &&
        tri.getSubReg(reg, X86::sub_8bit) &&
        !reserved.test(tri.getSubReg(reg, X86::sub_8bit))) {
      gr32s.push_back(reg);
    }
  }
}

unsigned unassign(LiveInterval &range, VirtRegMap &vrm, LiveRegMatrix &lrm) {
  unsigned oldreg = vrm.getPhys(range.reg);
  lrm.unassign(range);
  return oldreg;
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
    const X86RegisterInfo &tri = *reinterpret_cast<const X86RegisterInfo *>(
        f.getSubtarget<X86Subtarget>().getRegisterInfo());
    VirtRegMap &vrm = getAnalysis<VirtRegMap>();
    LiveIntervals &li = getAnalysis<LiveIntervals>();
    LiveRegMatrix &lrm = getAnalysis<LiveRegMatrix>();

    SmallVector<unsigned, 8> gr32s;
    compute_zext_dests(gr32s, tri, mri);

    for (MachineBasicBlock &bb : f) {
      for (MachineInstr &i : reverse(bb)) {
        if (!(i.getOpcode() == X86::MOVZX32rr8 &&
              disjoint_ranges(i.getOperand(0).getReg(),
                              i.getOperand(1).getReg(), li))) {
          continue;
        }

        LiveInterval &live32 = li.getInterval(i.getOperand(0).getReg());
        LiveInterval &live8 = li.getInterval(i.getOperand(1).getReg());

        dbgs() << "considering " << i;
        if (used_in_identity_copy(i.getOperand(0).getReg(), mri, vrm)) {
          // only consider assigned gr32
          dbgs() << "dest is used in identity copy, only considering "
                 << tri.getName(get_phys(i.getOperand(0).getReg(), vrm))
                 << "\n";

          unsigned old32 = unassign(live32, vrm, lrm);
          unsigned old8 = unassign(live8, vrm, lrm);

          unsigned gr8 = tri.getSubReg(old32, X86::sub_8bit);
          if (lrm.checkInterference(live32, old32) == LiveRegMatrix::IK_Free &&
              lrm.checkInterference(live8, gr8) == LiveRegMatrix::IK_Free) {
            dbgs() << "possible: " << tri.getName(old32) << "(with "
                   << tri.getName(gr8) << ")\n";
          }
          lrm.assign(live32, old32);
          lrm.assign(live8, old8);
        } else {
          unsigned old32 = unassign(live32, vrm, lrm);
          unsigned old8 = unassign(live8, vrm, lrm);

          for (unsigned gr32 : gr32s) {
            unsigned gr8 = tri.getSubReg(gr32, X86::sub_8bit);
            if (lrm.checkInterference(live32, gr32) == LiveRegMatrix::IK_Free &&
                lrm.checkInterference(live8, gr8) == LiveRegMatrix::IK_Free) {
              dbgs() << "possible: " << tri.getName(gr32) << "(with "
                     << tri.getName(gr8) << ")\n";
            }
          }
          lrm.assign(live32, old32);
          lrm.assign(live8, old8);
        }
      }
    }
    return false;
  }
};

char X86FixupZExt::id = 0;

struct MarkZExt : public MachineFunctionPass {
  static char id;

  MarkZExt() : MachineFunctionPass(id) {}

  const char *getPassName() const override { return "x86 movzx32rr8 hints"; }

  bool runOnMachineFunction(MachineFunction &f) override {
    MachineRegisterInfo &mri = f.getRegInfo();
    const X86RegisterInfo &tri = *reinterpret_cast<const X86RegisterInfo *>(
        f.getSubtarget<X86Subtarget>().getRegisterInfo());

    for (MachineBasicBlock &bb : f) {
      for (MachineInstr &i : bb) {
        if (i.getOpcode() == X86::MOVZX32rr8) {
          dbgs() << "checking out " << i;
          unsigned gr32 = i.getOperand(0).getReg();
          unsigned gr8 = i.getOperand(1).getReg();

          MachineInstr &use = *mri.use_instr_begin(gr32);
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
          }
          // mri.setRegAllocationHint(gr32, X86Hint::ParentGR32, gr8);
        }
      }
      return false;
    }
  }
};

char MarkZExt::id = 0;
}

namespace llvm {
FunctionPass *createX86FixupZExt() { return new X86FixupZExt(); }
FunctionPass *createMarkZExt() { return new MarkZExt(); }
}
