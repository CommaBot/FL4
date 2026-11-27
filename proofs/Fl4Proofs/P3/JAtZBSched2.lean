/-
P3 (line mmuAD, gen 28): **the VM-epoch frame for native steps that change the spec heap, and the scheduler step
at `JAtZV2`** (gen 27's "Next" item 2, first part).

* **`JAtZV.kV`**: FL4 writes confined to `OObj` words keep every VCPU's `TCB` word (`JAtZV.oobj_v`).
* **`JAtZV.ofBS`**: P3/JAtZBSched's `JAtZV.ofB` with its "spec heap unchanged" premise `hke` replaced by what
  the extension actually reads of the spec: the VCPU objects of `V` kept (`hvk`), every post-state object at an
  address the pre-state had an object of the same size (`hsz`, for `JVm.sep` by `JVm.step`), and no new spec
  `runningVM` thread (`hrv`, for `RunVmB` through both states' TCB relations: state word = `tsCode`). Native
  scheduler / IPC steps (thread states other than `runningVM`, SC fields, queues) satisfy all three; only
  `vmEnter` sets `runningVM`.
* **`JAtZV2.ofB`**, **`JAtZV2.ofBS`**: the same at `JAtZV2` (`VBind` from the kept VCPU objects and `TCB` words).
* **`JAtZV2.switchJ`**: `possible_switch_to` at `JAtZV2 V X` (P3/JAtZBSched's `JAtZV.switchJ`, the binding kept).

No named premise (`hvk`/`hsz`/`hrv` are the statement's scope: the facts of the spec step the lemma is applied
to). No existing statement changed.
-/
import Fl4Proofs.P3.JAtZBSched
import Fl4Proofs.P3.JAtZBVcpuX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **`OObj` writes keep every VCPU's `TCB` word.** -/
theorem JAtZV.kV (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {s' : S} {W : U64 → Prop}
    (hw : P1.WritesIn st s s' W) (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) :
    ∀ u ∈ V, L.mem s' (vTcbA u) = L.mem s (vTcbA u) := by
  intro u hu
  have hf := (J.base.jvLay J.vm).vfit u hu
  have e := lay_vTcb_val hf.2
  exact hw.mem_eq (by unfold P1.Aligned; rw [e]; omega) fun hb => by
    rcases J.oobj_v hu (hO _ hb) with h | h <;> omega

set_option maxHeartbeats 4000000 in
/-- **The VM-epoch frame for a native step that changes the spec heap** (module docstring). -/
theorem JAtZV.ofBS (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s')
    (hvk : ∀ u ∈ V, σ'.kheap u.bv = σ.kheap u.bv)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (hrv : ∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM) :
    JAtZV (L := L) arI V X AR Z H Cs Ac' Lst' D' s' a' σ' := by
  have B := J.base
  have Ly := B.jvLay J.vm
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') := B.xtop.slotsSame_of hw hO
  have nV : ∀ u ∈ V, ∀ b, W b → b.val < u.val ∨ u.val + 32768 ≤ b.val := fun u hu b hb => J.oobj_v hu (hO b hb)
  have E' : JExtV (L := L) V X Z.th s' := J.extv.of_eq (fun y hy => hSS.capV hy) hv (J.kV hw hO)
  have R' : RunVmB (L := L) Z.th s' := by
    intro t ht h8
    rw [hv t ht]
    refine J.rvm t ht ?_
    obtain ⟨x', hk', -⟩ := B'.xtop.rel.2.1.1.tcb t ht
    have w' := (B'.xtop.fin.1.1.2.2.1.at_tcb (B'.thT t ht) hk').st
    rw [Sched.stA_tStA] at h8 ⊢
    rw [h8] at w'
    have hx' : x'.tcbState = .runningVM := by
      cases hx : x'.tcbState <;> rw [hx] at w' <;> simp_all [tsCode]
    obtain ⟨x, hk, hx⟩ := hrv _ x' hk' hx'
    have w0 := (B.xtop.fin.1.1.2.2.1.at_tcb (B.thT t ht) hk).st
    rw [hx] at w0
    apply UScalar.eq_of_val_eq
    rw [w0]; simp [tsCode]
  have Jv' : JVm (L := L) V H s' σ' :=
    J.vm.step (fun _ h => h) (fun _ _ => rfl) hw.1 (fun u hu => by rw [hvk u hu]; exact J.vm.spec u hu)
      (fun o ko' ho => Or.inl (hsz o ko' ho))
  have Vl' : VList st V Z.th s' := J.vl.writes hw fun b hb => by
    refine ⟨J.vl.lw_al Ly.vfit hb, fun hW => ?_⟩
    rcases hb with rfl | ⟨u, hu, rfl | rfl⟩
    · exact hh _ hW rfl
    · have := lay_next_val (Ly.vfit u hu).2
      rcases nV u hu _ hW with h | h <;> omega
    · have := lay_prev_val (Ly.vfit u hu).2
      rcases nV u hu _ hW with h | h <;> omega
  exact ⟨B', E', R', Jv', Vl'⟩

/-- `VBind` from the kept VCPU objects and `TCB` words. -/
theorem VBind.ofV {σ σ' : Fl4Spec.State Unit} {m m' : U64 → U64} (h : VBind V σ m)
    (hvk : ∀ u ∈ V, σ'.kheap u.bv = σ.kheap u.bv) (hm : ∀ v ∈ V, m' (vTcbA v) = m (vTcbA v)) :
    VBind V σ' m' := by
  unfold VBind at h ⊢
  intro v hv
  obtain ⟨vs, h1, h2⟩ := h v hv
  exact ⟨vs, by rw [hvk v hv]; exact h1, by rw [hm v hv]; exact h2⟩

/-- **`JAtZV.ofB` at `JAtZV2`** (spec heap unchanged). -/
theorem JAtZV2.ofB (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s') (hke : σ'.kheap = σ.kheap) :
    JAtZV2 (L := L) arI V X AR Z H Cs Ac' Lst' D' s' a' σ' :=
  ⟨J.zv.ofB B' hw hO hh hv hke, J.vb.ofKheap hke (J.zv.kV hw hO)⟩

/-- **`JAtZV.ofBS` at `JAtZV2`** (module docstring). -/
theorem JAtZV2.ofBS (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s')
    (hvk : ∀ u ∈ V, σ'.kheap u.bv = σ.kheap u.bv)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (hrv : ∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM) :
    JAtZV2 (L := L) arI V X AR Z H Cs Ac' Lst' D' s' a' σ' :=
  ⟨J.zv.ofBS B' hw hO hh hv hvk hsz hrv, J.vb.ofV hvk (J.zv.kV hw hO)⟩

set_option maxHeartbeats 4000000 in
/-- **`possible_switch_to` at `JAtZV2 V X`** (P3/JAtZBSched's `JAtZV.switchJ`, the binding kept). -/
theorem JAtZV2.switchJ (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (hti : t.bv ≠ σ.idleThread) (htc : t.bv ≠ σ.curThread) (hs : Fl4Spec.schedulable t.bv σ = true) :
    sched.possible_switch_to st s t ⦃ s' => ∃ σ', Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
  have B := J.zv.base
  have hS := B.xtop.fin.1.1.1
  have hR := B.xtop.fin.1.1.2.2.1
  refine WP.spec_mono (WP.spec_and (WP.spec_and (B.switchJ ht hti htc hs)
    (possible_switch_to_refines s σ hR hS B.inv.actReady t ht)) (possible_switch_to_sfoot hR hS B.inv.actReady ht)) ?_
  rintro s' ⟨⟨⟨σ1, he1, Lst', B'⟩, ⟨σ2, he2, hke, -, -⟩⟩, hw⟩
  have e12 : σ2 = σ1 := by
    rw [he1] at he2
    have h := congrArg Prod.fst he2
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at h
    exact h.symm
  subst e12
  have hwT : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) :=
    WritesIn.tfoot_of_kfoot (WritesIn.kfoot_of_sfoot hw)
  have hv : VKeep (L := L) Z.th s s' := VKeep.of_tfoot hS B.thT hwT
  have hh : ∀ b, SFoot st Z.T Z.c s b → b ≠ P1.vHeadA st s := by
    intro b hb e
    subst e
    have hvh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val B.kern.ksbFit
    rcases SFoot.range hS.placed.tcb hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩
    · have d := B.kern.hks y _ (B.zH.1 y hy) (fun _ h => by cases h)
      simp only [P1.HKind.bits, Nat.reducePow] at d
      omega
    · have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
      omega
  exact ⟨σ2, he1, Lst', J.ofB B' hw (fun b h => tfoot_oobj hS (Or.inl (Or.inl h))) hh hv hke⟩

end

end Fl4Proofs.P3
