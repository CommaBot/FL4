/-
P3 (issue #16, g6b): **`kernel_entry_reachU5`** = g6a's `kernel_entry_reachU4`
with the fixed finish bundle (INV-PLAN §1.U3L.H).

* `KFinAtR5`: `KFinAtR31` without `sni` (`SniHyp`) and `send` (`SendHyp`).
  Both are theorems now (ScSniProof): `sniHyp_of` from `ArchTotal` and
  `SetDlDet` [P], `sendHyp_of` from `ArchTotal`. (`SniHyp` itself was narrowed
  in place to `SniPre` states, where it is consumed: before, it was false at
  every related state whose current thread has no SC.) `KFinEv5`: `KFinEv`
  with `KFinAtR5`.
* `SetDlDetR MR` [P]: the timer's opaque `setDeadlineImpl` has at most one
  outcome at every `MR`-related machine state. With `MachPlat.frame` (`MR` does
  not read `machineStateRest`) and the `MR` state the top's reachability
  carries, it gives the state-free `SetDlDet` (`setDlDet_of`).
* `kernel_entry_reachU5`: `kernel_entry_reachU4` with `hFin` / every `KFinEv`
  asking `KFinAtR5`, and the new platform premise `hDR`. Premises removed: D4
  `sni`, D5 `send` (both ∀st). Added: `hDR` (a fact of the opaque timer
  operation, under `MR`).
-/
import Fl4Proofs.P3.XTopJointKEntryU4
import Fl4Proofs.P3.ScSniProof
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[P] The timer's opaque `setDeadlineImpl` has at most one outcome at an
`MR`-related machine state** (module docstring). -/
def SetDlDetR (MR : A → Fl4Spec.MachineState → Prop) : Prop :=
  ∀ (a : A) (ms : Fl4Spec.MachineState), MR a ms → ∀ (d : Fl4Spec.Word64) (x y : Unit × Fl4Spec.MachineStateRest),
    x ∈ (Fl4Spec.setDeadlineImpl d ms.machineStateRest).1 → y ∈ (Fl4Spec.setDeadlineImpl d ms.machineStateRest).1 →
      x = y

/-- `SetDlDet` from `SetDlDetR` at one `MR` state: `MR` does not read the
machine-state rest (`MachPlat.frame`). -/
theorem setDlDet_of {MR : A → Fl4Spec.MachineState → Prop} (hM : MachPlat arI MR) (hDR : SetDlDetR (A := A) MR)
    {a : A} {ms : Fl4Spec.MachineState} (h : MR a ms) : SetDlDet := fun d mr x y hx hy =>
  hDR a { ms with machineStateRest := mr } (hM.frame a ms _ h rfl rfl rfl rfl) d x y hx hy

/-- **`KFinAtR31` without `sni` and `send`** (module docstring). -/
structure KFinAtR5 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ
  arch : ArchSwF st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c
  tail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      timer.fire st arI s a = ok rf →
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) ∨
       ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄
  /-- [J] the idle TCB's vtable (`IdleVt`, from `KFinAtR8.idle`) and the arch premises `ArchRefines` [P] /
  `ARKeep` the g7e scheduler chain needs, carried to the old finish lemmas. -/
  rr : FinRootR arI AR σ

variable {arI}

theorem KFinAtR5.to31 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (hA : P0.ArchTotal arI) (hD : SetDlDet) (F : KFinAtR5 (L := L) arI AR Z H Cs s a σ) :
    KFinAtR31 (L := L) arI AR Z H Cs s a σ :=
  ⟨F.hd, F.arch, F.archNd, sniHyp_of hA hD, sendHyp_of hA, F.tail, F.rr⟩

variable (arI)

/-- `KFinEv` with `KFinAtR5`. -/
def KFinEv5 (AR : A → Fl4Spec.Cr3 → Prop) (ev : Fl4Spec.Event) (Kf : S → A → Prop) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
    ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
      Kf s' a' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 → KFinAtR5 (L := L) arI AR Z' H' Cs' s' a' x.2

variable {arI}

theorem KFinEv5.to {AR : A → Fl4Spec.Cr3 → Prop} {ev : Fl4Spec.Event} {Kf : S → A → Prop} {σ : Fl4Spec.State Unit}
    (hA : P0.ArchTotal arI) (hD : SetDlDet) (h : KFinEv5 (L := L) arI AR ev Kf σ) : KFinEv (L := L) arI AR ev Kf σ :=
  fun x hx Z' H' Cs' Ac' Lst' D' s' a' hK J => (h x hx Z' H' Cs' Ac' Lst' D' s' a' hK J).to31 hA hD

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

end

end

end Fl4Proofs.P3.SInvR.G5
