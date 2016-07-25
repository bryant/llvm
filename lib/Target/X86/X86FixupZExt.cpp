#include "X86Subtarget.h"
#include "llvm/CodeGen/CalcSpillWeights.h"
#include "llvm/CodeGen/LiveIntervalAnalysis.h"
#include "llvm/CodeGen/LivePhysRegs.h"
#include "llvm/CodeGen/LiveRegMatrix.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/VirtRegMap.h"

#include <iterator>

#define DEBUG_TYPE "x86-fixup-zext"

namespace {
using namespace llvm;
using std::back_inserter;

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

DenseMap<MachineBasicBlock *, MachineInstr *>
dominating_defs(unsigned gr8, const MachineRegisterInfo &mri,
                const SlotIndexes &si) {
  DenseMap<MachineBasicBlock *, MachineInstr *> defs;
  // at least until release_37, getInstructionIndex is expensive.
  DenseMap<MachineBasicBlock *, SlotIndex> cached;

  for (MachineInstr &def : mri.def_instructions(gr8)) {
    MachineBasicBlock *bb = def.getParent();
    if (defs.find(bb) == defs.end() ||
        si.getInstructionIndex(def) < cached.lookup(bb)) {
      cached[bb] = si.getInstructionIndex(def);
      defs[bb] = &def;
    }
  }
  return defs;
}

template <size_t N>
DenseMap<MachineInstr *, SmallVector<MachineInstr *, N>>
insertion_points_for(unsigned gr8, const MachineFunction &f,
                     LiveIntervals &li) {
  DenseMap<MachineInstr *, SmallVector<MachineInstr *, N>> rv;

  for (auto bb_def :
       dominating_defs(gr8, f.getRegInfo(), *li.getSlotIndexes())) {
    // xor would be inserted before ins.
    MachineBasicBlock::iterator ins = bb_def.second;
    while (true) {
      SlotIndex s = li.getInstructionIndex(*ins);
      if (!live_at(s, li.getRegUnit(*MCRegUnitIterator(
                          X86::EFLAGS,
                          f.getSubtarget<X86Subtarget>().getRegisterInfo()))) ||
          ins == bb_def.first->begin()) {
        if (rv.count(ins)) {
          rv[ins].push_back(bb_def.second);
        } else {
          rv[ins] = {bb_def.second};
        }
        break;
      } else {
        --ins;
      }
    }
  }
  return rv;
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

unsigned maybe_id_copy(unsigned vreg, const MachineRegisterInfo &mri,
                       const VirtRegMap &vrm) {
  if (any_of(mri.use_instr_begin(vreg), mri.use_instr_end(),
             [&](const MachineInstr &i) {
               return i.isCopy() &&
                      get_phys(i.getOperand(1).getReg(), vrm) ==
                          get_phys(i.getOperand(0).getReg(), vrm) &&
                      i.getOperand(1).getSubReg() ==
                          i.getOperand(0).getSubReg();
             })) {
    return get_phys(vreg, vrm);
  }
  return 0;
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
                        const MachineFunction &f, const LiveRegMatrix &lrm) {
  const X86RegisterInfo &tri = *reinterpret_cast<const X86RegisterInfo *>(
      f.getSubtarget<X86Subtarget>().getRegisterInfo());
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
  for (unsigned reg = X86::NoRegister + 1; reg < X86::NUM_TARGET_REGS;
       reg += 1) {
    if (!unusable.test(reg) && X86::GR32RegClass.contains(reg) &&
        tri.getSubReg(reg, X86::sub_8bit) &&
        !unusable.test(tri.getSubReg(reg, X86::sub_8bit))) {
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
    compute_zext_dests(gr32s, f, lrm);
    for (unsigned gr32 : gr32s) {
      DEBUG(dbgs() << "usable gr32: " << tri.getName(gr32) << "\n");
    }

    for (MachineBasicBlock &bb : f) {
      for (MachineBasicBlock::iterator iter = bb.begin(); iter != bb.end();) {
        MachineInstr &i = *iter;
        ++iter;
        // TODO: permit sub_32bit. cf.  ragreedy-last-chance-recoloring.ll
        if (!(i.getOpcode() == X86::MOVZX32rr8 &&
              i.getOperand(0).getSubReg() == 0 &&
              i.getOperand(1).getSubReg() == 0 /*&&
              disjoint_ranges(i.getOperand(0).getReg(),
                              i.getOperand(1).getReg(), li)*/)) {
          continue;
        }

        dbgs() << "considering " << i;

        auto insdefs = insertion_points_for<4>(i.getOperand(1).getReg(), f, li);
        // TODO: run transform for all dominating gr8 defs.
        if (insdefs.size() > 1) {
          dbgs() << "ignoring " << i << "as it has multiple dom defs:\n";
          for (auto ins_defs : insdefs) {
            dbgs() << "\t" << (*ins_defs.first) << "for "
                   << (*ins_defs.second[0]);
          };
          continue;
        }

        MachineInstr *ins = insdefs.begin()->first;

        unsigned priority = maybe_id_copy(i.getOperand(0).getReg(), mri, vrm);
        LiveInterval &live32 = li.getInterval(i.getOperand(0).getReg());
        LiveInterval &live8 = li.getInterval(i.getOperand(1).getReg());

        LiveInterval extra(live32.reg, live32.weight);

        SlotIndex s = li.getInstructionIndex(*ins);
        dbgs() << "insertion point is just before " << s << " which equates to "
               << (*ins);
        SlotIndex e = li.getInstructionIndex(i);
        extra.addSegment(LiveRange::Segment(s, e, nullptr));

        unsigned old32 = unassign(live32, vrm, lrm);
        unsigned old8 = unassign(live8, vrm, lrm);

        auto could_work = [&](unsigned r) {
          dbgs() << "trying " << tri.getName(r) << "\n";
          unsigned gr8 = tri.getSubReg(r, X86::sub_8bit);
          bool a = lrm.checkInterference(live32, r) == LiveRegMatrix::IK_Free;
          bool b = lrm.checkInterference(extra, r) == LiveRegMatrix::IK_Free;
          bool c = lrm.checkInterference(live8, gr8) == LiveRegMatrix::IK_Free;
          if (!a) {
            dbgs() << tri.getName(r) << " not free in " << live32 << "\n";
          }
          if (!b) {
            dbgs() << tri.getName(r) << " not free in (" << s << ", " << e
                   << ")\n";
          }
          if (!c) {
            dbgs() << tri.getName(gr8) << " not free in " << live8 << "\n";
          }

          return a && b && c;
        };

        auto doit = [&](unsigned new32) {
          unsigned vreg32 = i.getOperand(0).getReg();
          unsigned vreg8 = i.getOperand(1).getReg();
          dbgs() << "subregister operand change: " << PrintReg(vreg8) << "\n";

          // in-place operand mutation would confuse
          // MachineRegisterInfo::defusechain_iterator
          SmallVector<MachineInstr *, 16> iis;
          transform(mri.reg_instr_begin(vreg8), mri.reg_instr_end(),
                    back_inserter(iis), [](MachineInstr &i) { return &i; });
          for (MachineInstr *ii : iis) {
            dbgs() << "changing " << (*ii);
            for (MachineOperand &op : ii->operands()) {
              if (op.isReg() && op.getReg() == vreg8) {
                op.setReg(vreg32);
                op.setSubReg(X86::sub_8bit);
              }
            }
            dbgs() << "becomes " << (*ii);
          }

          MachineInstrBuilder mib = BuildMI(
              *ins->getParent(), ins, i.getDebugLoc(),
              f.getSubtarget<X86Subtarget>().getInstrInfo()->get(X86::MOV32r0),
              vreg32);
          li.RemoveMachineInstrFromMaps(i);
          li.InsertMachineInstrInMaps(*mib);
          i.eraseFromParent();
          li.removeInterval(vreg8);
          li.removeInterval(vreg32);

          LiveInterval &newlive32 = li.createAndComputeVirtRegInterval(vreg32);
          // li.repairIntervalsInRange(&bb, bb.begin(), bb.end(), {vreg8,
          // vreg32});

          dbgs() << "reassigning " << PrintReg(newlive32.reg) << ": "
                 << tri.getName(old32) << " => " << tri.getName(new32) << "\n";
          // lrm.assign(live8, tri.getSubReg(new32, X86::sub_8bit));
          lrm.assign(newlive32, new32);
        };

        dbgs() << "gr32 would be live in (" << s << ", " << e << ") and "
               << live32 << "\n";
        dbgs() << "gr8 would be live in " << live8 << "\n";

        bool changed = false;
        if (priority != 0 && could_work(priority)) {
          doit(priority);
          changed = true;
        } else {
          for (unsigned gr32 : gr32s) {
            if (could_work(gr32)) {
              doit(gr32);
              changed = true;
              break;
            }
          }
        }

        if (!changed) {
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
          } /* else {
             dbgs() << "hinting arbitrarily\n";
             mri.setRegAllocationHint(gr32, X86Hint::ParentGR32, gr8);
             mri.setRegAllocationHint(gr8, X86Hint::SubGR8, gr32);
           }*/
        }
      }
    }
    return false;
  }
};

char MarkZExt::id = 0;
}

namespace llvm {
FunctionPass *createX86FixupZExt() { return new X86FixupZExt(); }
FunctionPass *createMarkZExt() { return new MarkZExt(); }
}
