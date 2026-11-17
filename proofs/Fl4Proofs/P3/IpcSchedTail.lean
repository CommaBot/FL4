/-
P3 (DESIGN.md §9), TCB invocations: **SetSchedParams' scheduler steps**
(the leaf `SchedTailXHyp` from `JAtZ` is IpcSchedTailJ's `schedTailXHypJ`;
`schedTailXHyp_of` is retired): after the fault-handler install,
FL4's `set_mcp` (`XTopAt.tcbWr`, the spec's `set_mcpriority`), `set_priority`
(`set_priority_irel`), and the SC bind or unbind (`bind_irel`,
`unbind_irel`: the Sc proofs' `bind_tcb_refines`, `unbind_tcb_refines`,
lifted by `tk_liftCW`), against the spec's `set_mcpriority`, `set_priority`
and SC step. The spec facts after the install are the Sc proofs' `SpecPost`
(named).
-/
import Fl4Proofs.P3.IpcReadRegs
import Fl4Proofs.P3.ArchKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec

noncomputable section

theorem nkt_schedContextUnbindTcb (p : ObjRef) : NKT (schedContextUnbindTcb (Z := Unit) p) := by
  unfold schedContextUnbindTcb setTcbObjRef setScObjRef
  refine nkt_bind (nkt_getSchedContext _) fun _ => nkt_bind (nkt_assertOpt _) fun _ => nkt_bind (nkt_gets _) fun _ =>
    nkt_bind (nkt_when _ nkt_rescheduleRequired) fun _ => nkt_bind (nkt_tcbSchedAction _ _) fun _ =>
    nkt_bind (nkt_tcbReleaseRemove _) fun _ => ?_
  nkt_auto

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core

section
variable {S A C : Type} {st : machine.Store S} [L : P1.LawfulStore st] {arI : machine.Arch A} {AR : A → C → Prop}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : ARKeep arI AR) {c : C}
include hS hA hK
set_option linter.unusedSectionVars false

theorem AK.schedcontext_bind_tcb {s : S} {a : A} {sc : obj.Sc} {t : obj.Tcb} (h : AR a c) :
    schedcontext.bind_tcb st arI s a sc t ⦃ r => AR r.2 c ⦄ := by
  unfold schedcontext.bind_tcb; ak_walk

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 4000000 in
/-- **`unbind_tcb` on `IRel`** (`unbind_tcb_refines`, lifted by `tk_liftCW`). -/
theorem unbind_irel (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) (hN : NSC N C σ) (hI : Inv σ) {p : U64} (hp : p ∈ C)
    {y : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap p.bv = some (.schedContext y n)) {t : U64} (ht : t ∈ T)
    (hyt : y.scTcb = some t.bv) :
    schedcontext.unbind_tcb st s p ⦃ s' => ∃ σ', Fl4Spec.schedContextUnbindTcb (Z := Unit) p.bv σ =
      ({((), σ')}, False) ∧ IRel st th cr N T C E R B c s' σ' ⦄ := by
  have hS := hX.2.2.1
  have hsw24 := sw_hdr hS hp (K := 24#u64) (by simp) (by simp) (by decide)
  refine WP.spec_mono (unbind_tcb_refines s σ hS hX.1.toN hN hI hp hk ht hyt) ?_
  rintro s' ⟨σ', he, hS', hR', -, -, -, hw, -⟩
  have hK : ScTKw (fun q => q = σ.curThread) σ σ' :=
    ScTKw.ofFalse (NKT.of_eq (nkt_schedContextUnbindTcb _) he)
  refine ⟨σ', he, tk_liftCW hP0 hX (hw.mono fun b hb => ?_) hK hS' hR'⟩
  rcases hb with h | h
  · exact Or.inl (Or.inl (KFoot.of_sfoot h))
  · subst h; exact Or.inl (Or.inl (KFoot.of_sw hsw24))

set_option maxHeartbeats 4000000 in
/-- **`bind_tcb` on `IRel`** (`bind_tcb_refines`, lifted by `tk_liftCW`). -/
theorem bind_irel (hP0 : IPlaced N T E R B) (s : S) (a : A) {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) (hN : NSC N C σ) (hI : Inv σ) {p : U64} (hp : p ∈ C) (hp0 : p ≠ 0#u64)
    {y : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap p.bv = some (.schedContext y n)) (hy0 : y.scTcb = none)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hxt0 : xt.tcbSchedContext = none)
    (hblk : Fl4Spec.runnable xt.tcbState = false → inClass xt.tcbState → Fl4Spec.scActive y = true → released σ y)
    (hT : TimeAgree ar) :
    schedcontext.bind_tcb st ar s a p t ⦃ r => ∃ σ', Fl4Spec.schedContextBindTcb (Z := Unit) p.bv t.bv σ =
      ({((), σ')}, False) ∧ IRel st th cr N T C E R B c r.1 σ' ⦄ := by
  refine WP.spec_mono (bind_tcb_refines s a σ hX.2.2.1 hX.1.toN hN hI hp hp0 hk hy0 ht hkt hxt0 hblk hT) ?_
  rintro r ⟨σ', he, hS', hR', -, -, -, hw⟩
  have hK : ScTKw (fun q => q = σ.curThread) σ σ' :=
    ScTKw.ofFalse (NKT.of_eq (nkt_schedContextBindTcb _ _) he)
  exact ⟨σ', he, tk_liftCW hP0 hX (hw.mono fun _ h => Or.inl (Or.inl h)) hK hS' hR'⟩

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
open Fl4Proofs.P3.Notif (inClass released)

end

end

end Fl4Proofs.P3
