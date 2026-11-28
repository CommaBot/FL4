/-
P3 (p3J gen 59): **the native syscall top over the P2 platform record `LocPlat`** (Architect ruling 2026-11-28
14:01Z, item 1): a thin front-end over gen 54's `kernel_entry_runMcWKR_sysLzz`, so the native syscall refinement is
stated over the same platform record as the V15 trunk and BootSt (`PathObl.LocPlat`, P2/E2EVFl4W3).

* **`MachPlat.toF`**: `MachPlat` gives `MachPlatF` (the mask split; collapse A, Q removed JBootIpi's old helper of
  this name when `MachPlat` became irqfix's `MachPlatT`: here restated for the written-back `MachPlat`, whose
  `mask` asks `w.val < cond m 256 126`).
* **`kernel_entry_runMcWKR_sysLzzP`**: `_sysLzz` with its 14 arch / store globals read off one
  `P : LocPlat st arI AR MR` — `ARIface` `P.ari`, `ArchTotal` `P.tot`, `numDomains = 1` `P.nd`, `MachPlatF`
  `P.mach.toF`, `IpiF` `P.mach.noIpi`, `MRKeepD` `P.kd`, `hPAi` `P.pa.irqAR`, `IrqPlatA` `P.ia`, `TimeAgree` `P.t`,
  `hmax` `P.max`, `htu` `P.tu`, `ArchRefines` `P.ref`, `StoreExt` `P.sx`, `SetDlDetR` `P.dr` — plus `hFpu`,
  `hFW` (not in `LocPlat`), `[PlainStore st]`, the run state `hR : RunMcWKR` and `_sysLzz`'s per-call
  antecedents verbatim. Proved by applying `_sysLzz`: no new premise, `LocPlat` unchanged, `_sysLzz` untouched.
  One direction only: `LocPlat` also carries `io : MRKeepIo` and `pi : PortInValMR`, which `_sysLzz` does not take,
  so `_sysLzz` is not derivable from `_sysLzzP`; `_sysLzzP` is `_sysLzz` at the platforms `LocPlat` describes.
* **`kernel_entry_runMcWKR_sysUP`** / **`kernel_entry_runMcWKR_sysUWCP`**: the same front-end for the
  unknown-syscall clause `_sysU` (P3JMcFltQ) and its footprint form `_sysUWC` (P3JMcLiftR, `hFt` [J] kept as there).

Named premises: none new (`FpuImplDet` [P] (ScFpuNd), `FpuWriteDet` [P] (ArchSwThr), `LocPlat`'s fields [P]
(tagged at their P3 sources), `_sysUWC`'s `SysUFootWC` [J]). No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMidIpcC
import Fl4Proofs.P3.P3JMcFltQ
import Fl4Proofs.P2.E2EVFl4W3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

section
variable {A : Type} {arI : machine.Arch A}

/-- (p3J gen 59) **`MachPlat` gives `MachPlatF`** (module docstring; with `MachPlatF.toT` the two are
`MachPlat ↔ MachPlatF ∧ IpiF`). -/
theorem MachPlat.toF {MR : A → Fl4Spec.MachineState → Prop} (h : MachPlat arI MR) : MachPlatF arI MR :=
  ⟨h.now, h.irqPending, h.take, fun a w ms hR hw => h.mask a w true ms hR hw,
    fun a w ms hR hw => h.mask a w false ms hR (by show w.val < 126; omega), h.ack, h.frame⟩

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 59) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, over the platform record `LocPlat`**:
`kernel_entry_runMcWKR_sysLzz` with its arch / store globals taken from `P`; besides `P` only `hFpu`, `hFW`,
`PlainStore` and `hR` (module docstring). -/
theorem kernel_entry_runMcWKR_sysLzzP [Fl4Proofs.P1.PlainStore st] (P : Fl4Proofs.P2.PathObl.LocPlat st arI AR MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzz P.ari P.tot P.nd P.mach.toF P.mach.noIpi P.kd P.pa.irqAR P.ia P.t P.max P.tu P.ref
    P.sx P.dr hFpu hFW hR

/-- (p3J gen 59) **The unknown-syscall entry over `LocPlat`** (`kernel_entry_runMcWKR_sysU` with its globals from
`P`; module docstring). -/
theorem kernel_entry_runMcWKR_sysUP [Fl4Proofs.P1.PlainStore st] (P : Fl4Proofs.P2.PathObl.LocPlat st arI AR MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ) :
    ∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
        RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysU P.ari P.tot P.nd P.mach.toF P.mach.noIpi P.kd P.pa.irqAR P.ia P.t P.max P.tu P.ref
    P.sx P.dr hFpu hFW hR

/-- (p3J gen 59) **The unknown-syscall entry with its footprint premise over `LocPlat`**
(`kernel_entry_runMcWKR_sysUWC` with its globals from `P`; `hFt` [J] as there). -/
theorem kernel_entry_runMcWKR_sysUWCP [Fl4Proofs.P1.PlainStore st] (P : Fl4Proofs.P2.PathObl.LocPlat st arI AR MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hFt : SysUFootWC (L := L) arI AR MR s a σ) :
    ∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
        RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysUWC P.ari P.tot P.nd P.mach.toF P.mach.noIpi P.kd P.pa.irqAR P.ia P.t P.max P.tu P.ref
    P.sx P.dr hFpu hFW hR hFt

end

end

end Fl4Proofs.P3.Mc
