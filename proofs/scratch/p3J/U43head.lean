/-
P3 (line p3J, gen 11): **`kernel_entry_reachU43`** = `kernel_entry_reachU42` without the per-entry
`ArchSwFT` [P] (the thread half of `ArchSwF`), which is now a theorem from opaque-operation facts.

* ArchSwThr: **`archSwFT_of : FpuImplDet → FpuWriteDet → P0.ArchTotal ar → ArchSwFT st ar N T C c`** at
  every ghost set. `ArchSwFT`'s post says nothing about CR3, so no `StateRel` / `VsRel` at the scheduler's
  intermediate states is needed: FL4's `set_vm_root` keeps the store and is total; the spec's `setVmRoot`
  has one outcome by `VsRootOK` (already `ArchSwFT`'s guard) and the TCB from `SchedRel`; the spec's
  `lazyFpuRestore` has one outcome given that the three opaque FPU machine operations it can run
  (`enableFpuImpl`, `disableFpuImpl`, `writeFpuStateImpl`) have at most one outcome each.
* `KFinAtR42` has the single field `arch : ArchSwFT`, so `kFinAtR42_of` / `kFinEv42_of` supply every
  per-entry `KFinAtR42` / `KFinEv42` premise of U42.
* **Premise diff U42 → U43**: the syscall clause's `(∀ x ∈ (specFront c σ).1, … → KFinAtR42 …) →` and the
  five event clauses' `KFinEv42 …` premises are **removed**; one global premise is **added**:
  `hFW : FpuWriteDet` [P] (Fl4Spec `opaque writeFpuStateImpl`, l4v `MachineOps.X64.writeFpuState_impl`,
  `consts'`: at most one outcome; the same shape as U41's `hFpu : FpuImplDet`, which does not cover this
  operation). `hFpu : FpuImplDet` is reused unchanged. Start (`JReachU40`) and conclusion verbatim. [W] 0.
  Why `FpuWriteDet` cannot be avoided: in `lazyFpuRestore`'s owner-switch branch the spec runs
  `writeFpuStateImpl` on the new owner's image; if it had two outcomes `archSwitchToThread` would have two,
  and `ArchSwFT` asks for exactly one (it is not derivable from U42's premises; it is a fact about an
  opaque constant, not about FL4).
* **`kernel_entry_reachU42_of43`**: U42's statement verbatim plus `hFW : FpuWriteDet`, from U43 (the
  dropped premises are ignored). As gen 8's `kernel_entry_reachU40_of41` (+ `hFpu`).

Named premises: U42's (XTopJointKEntryU42) minus `KFinAtR42.arch : ArchSwFT` [P] (per entry), plus
`FpuWriteDet` [P] (global, opaque constant). Remaining per-entry premises unchanged from
U42: `KDispHypsKVU39` [J], `JDecMRLK` [J]. No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU42
import Fl4Proofs.P3.ArchSwThr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- Every `KFinAtR42` from the opaque FPU premises and `ArchTotal` (`archSwFT_of`). -/
theorem kFinAtR42_of (hFpu : FpuImplDet) (hFW : FpuWriteDet) (hA : P0.ArchTotal arI)
    {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} : KFinAtR42 (L := L) arI AR Z H Cs s a σ :=
  ⟨archSwFT_of hFpu hFW hA⟩

/-- Every `KFinEv42` from the opaque FPU premises and `ArchTotal`. -/
theorem kFinEv42_of (hFpu : FpuImplDet) (hFW : FpuWriteDet) (hA : P0.ArchTotal arI)
    {AR : A → Fl4Spec.Cr3 → Prop} {ev : Fl4Spec.Event} {Kf : S → A → Prop} {σ : Fl4Spec.State Unit} :
    KFinEv42 (L := L) arI AR ev Kf σ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => kFinAtR42_of hFpu hFW hA

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

