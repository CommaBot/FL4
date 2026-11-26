/-
P3 (line p3J, gen 8): **`kernel_entry_reachU41`** = `kernel_entry_reachU40` without the per-entry
`KFinAtR13.archNd` (`ArchNdF` [P]), from a [P] on two opaque machine operations.

* `KFinAtR41` = `KFinAtR13` without `archNd` (only `arch : ArchSwF` [P]); `KFinEv41` = `KFinEv13` on
  `KFinAtR41`. `KFinAtR41.to13` / `KFinEv41.to13` (from `FpuImplDet`, ScFpuNd's `archNdF_of`),
  `KFinAtR13.to41` / `KFinEv13.to41` (dropped).
* **Premise diff U40 → U41**: new global premise `hFpu : FpuImplDet` [P] (Fl4Spec `Machine.lean`'s opaque
  `enableFpuImpl` / `disableFpuImpl` have at most one outcome; l4v `MachineOps.X64` `consts'`); the syscall
  clause's finish premise `KFinAtR13 …` ↦ `KFinAtR41 …` and every event's `KFinEv13 …` ↦ `KFinEv41 …`
  (`archNd` removed). Start condition (`JReachU40`) and conclusion verbatim. [W] 0. A per-entry, ∀-state [P]
  about the spec's domain-switch semantics and both relations is traded for one about two opaque constants.
* **`kernel_entry_reachU40_of41`**: U40's statement with the one more hypothesis `hFpu : FpuImplDet` (U40's own
  premises do not give it: `ArchNdF` speaks only of reachable relations' states).

Named premises: U40's (XTopJointKEntryU40) with `archNd` removed, plus `FpuImplDet` [P]. No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU40
import Fl4Proofs.P3.ScFpuNd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KFinAtR13` without `archNd`.** -/
structure KFinAtR41 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  /-- [P] `ArchSwF` (as `KFinAtR13.arch`). -/
  arch : ArchSwF st arI Z.N Z.T Z.C Z.c

/-- `KFinEv13` with `KFinAtR41`. -/
def KFinEv41 (AR : A → Fl4Spec.Cr3 → Prop) (ev : Fl4Spec.Event) (Kf : S → A → Prop) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
    ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
      Kf s' a' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 → KFinAtR41 (L := L) arI AR Z' H' Cs' s' a' x.2

variable {arI}

theorem KFinAtR41.to13 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : KFinAtR41 (L := L) arI AR Z H Cs s a σ) (hD : FpuImplDet) :
    KFinAtR13 (L := L) arI AR Z H Cs s a σ :=
  ⟨h.arch, archNdF_of hD⟩

theorem KFinAtR13.to41 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : KFinAtR13 (L := L) arI AR Z H Cs s a σ) :
    KFinAtR41 (L := L) arI AR Z H Cs s a σ :=
  ⟨h.arch⟩

theorem KFinEv41.to13 {AR : A → Fl4Spec.Cr3 → Prop} {ev : Fl4Spec.Event} {Kf : S → A → Prop}
    {σ : Fl4Spec.State Unit} (h : KFinEv41 (L := L) arI AR ev Kf σ) (hD : FpuImplDet) :
    KFinEv13 (L := L) arI AR ev Kf σ :=
  fun x hx Z' H' Cs' Ac' Lst' D' s' a' hK hJ => (h x hx Z' H' Cs' Ac' Lst' D' s' a' hK hJ).to13 hD

theorem KFinEv13.to41 {AR : A → Fl4Spec.Cr3 → Prop} {ev : Fl4Spec.Event} {Kf : S → A → Prop}
    {σ : Fl4Spec.State Unit} (h : KFinEv13 (L := L) arI AR ev Kf σ) :
    KFinEv41 (L := L) arI AR ev Kf σ :=
  fun x hx Z' H' Cs' Ac' Lst' D' s' a' hK hJ => (h x hx Z' H' Cs' Ac' Lst' D' s' a' hK hJ).to41

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

