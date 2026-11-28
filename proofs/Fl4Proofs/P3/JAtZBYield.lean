/-
P3 (line mmuAD, gen 29): **SC-code steps at `JAtZV2`; `cancel_yield_to` lifted** (gen 28's "Next" item 3).

* **`zv_tk`**: a spec step `ScTKw (fun _ => False) σ σ'` (P3/ScTK: the SC code's steps, no thread changes state)
  keeps every arch object, keeps every object's size, and makes no new `runningVM` thread — exactly the three
  spec facts `JAtZV.ofBS` asks (`hvk`, `hsz`, `hrv`).
* **`JAtZB.tfoot_nh`**: a `TFoot` word (scheduler footprint: TCB words past 256, the current node, notification
  words, SC words) is not the VCPU-list head word `ksb + 80` (`JKern.hks`, the node base).
* **`JAtZV2.ofTK`**: the VM-epoch frame for every native step with a `TFoot` footprint and an `ScTKw (fun _ =>
  False)` spec step: `JAtZB` after ⇒ `JAtZV2` after (`JAtZV2.ofBS` with `tfoot_oobj`, `VKeep.of_tfoot`,
  `tfoot_nh`, `zv_tk`).
* **`JAtZB.deadP_sc_stepG`**, **`JAtZB.deadP_sc_step`** (P3/ScDeadStep, generated copies over `JAtZB`,
  `scratch/mmu24_jatzb_gen.py cancelYieldJD`; the other 23 dependencies are already in P3/JAtZBWr / JAtZBSched),
  **`JAtZB.cancelYieldJD`** (P3/XTopJointYield's `JAtZ.cancelYieldJD` over `JAtZB`, proof verbatim; the post
  also names the spec step's `ScTKw` and FL4's `TFoot` footprint, both already proved inside).
* **`JAtZV2.cancelYieldJ`**: `cancel_yield_to` of a yielder at `JAtZV2 V X` for any `V`, premises exactly
  `JAtZ.cancelYieldJD`'s.

No named premise. No existing statement changed.

(mmuAD gen 42b17, second pass) Copies removed (originals generalised in place): P3/ScDeadStep `deadP_sc_step`,
`deadP_sc_stepG`.

(mmuAD gen 42b18) Removed (the originals are stated over `JAtZB` in place, the `JAtZ` names their corollaries with
`ext` rebuilt): P3/XTopJointYield `cancelYieldJD` (the original now has the copy's statement).
-/
import Fl4Proofs.P3.JAtZBSched2
import Fl4Proofs.P3.XTopJointYield
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- **What an `ScTKw (fun _ => False)` spec step keeps of the VM epoch** (module docstring). -/
theorem zv_tk {σ σ' : Fl4Spec.State Unit} (h : Sched.ScTKw (fun _ => False) σ σ') :
    (∀ p ao, σ.kheap p = some (.archObj ao) → σ'.kheap p = σ.kheap p) ∧
    (∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko) ∧
    (∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM) := by
  refine ⟨fun p ao hp => ?_, fun o ko' ho => ?_, fun o x' ho hx => ?_⟩
  · have k := h.kh p
    rw [hp] at k ⊢
    cases e : σ'.kheap p with
    | none => rw [e] at k; exact k.elim
    | some o' =>
      rw [e] at k
      change Sched.TKObj False (.archObj ao) o' at k
      rcases k with k | ⟨x, y, h1, -⟩ | ⟨x, y, n, h1, -⟩ | ⟨x, y, h1, -⟩ | ⟨x, y, h1, -⟩
      · rw [k]
      all_goals cases h1
  · have k := h.kh o
    rw [ho] at k
    cases e : σ.kheap o with
    | none => rw [e] at k; exact k.elim
    | some ko =>
      rw [e] at k
      change Sched.TKObj False ko ko' at k
      refine ⟨ko, rfl, ?_⟩
      rcases k with rfl | ⟨x, y, rfl, rfl, -⟩ | ⟨x, y, n, rfl, rfl⟩ | ⟨x, y, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ <;> rfl
  · have k := h.kh o
    rw [ho] at k
    cases e : σ.kheap o with
    | none => rw [e] at k; exact k.elim
    | some ko =>
      rw [e] at k
      change Sched.TKObj False ko (.tcb x') at k
      rcases k with k | ⟨x, y, h1, h2, -, h3⟩ | ⟨_, _, _, -, h2⟩ | ⟨_, _, -, h2, -⟩ | ⟨_, _, -, h2, -⟩
      · exact ⟨x', by rw [k], hx⟩
      · cases h2
        refine ⟨x, by rw [h1], ?_⟩
        rcases h3 with h3 | ⟨h3, -⟩
        · rw [← h3]; exact hx
        · exact h3.elim
      all_goals cases h2

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **A `TFoot` word is not the VCPU-list head word** (module docstring). -/
theorem JAtZB.tfoot_nh (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64}
    (h : Sched.TFoot st Z.T Z.N Z.C Z.c s σ b) : b ≠ P1.vHeadA st s := by
  intro e
  subst e
  have hvh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
  rcases Sched.tfoot_tcb J.xtop.fin.1.1.1 h with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ |
      ⟨sc, hsc, x, n, hk, hso⟩
  · have d := J.kern.hks y _ (J.zH.1 y hy) (fun _ h => by cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d
    omega
  · have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
    omega
  · have d := J.kern.hks n _ (J.zH.2.2.2 n hn) (fun _ h => by cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d
    omega
  · obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hH := (hJ.sc sc x n (J.c0 sc hsc) hk).2
    have d := J.kern.hks sc _ hH (fun _ h => by cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d
    unfold Sched.ScObj at hso
    omega

/-- **The VM-epoch frame of an SC-code step** (module docstring). -/
theorem JAtZV2.ofTK (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {Ac' : Set U64}
    {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw (fun _ => False) σ σ') :
    JAtZV2 (L := L) arI V X AR Z H Cs Ac' Lst' D' s' a' σ' := by
  have B := J.zv.base
  have hS := B.xtop.fin.1.1.1
  obtain ⟨h1, h2, h3⟩ := zv_tk hK
  exact J.ofBS B' hw (fun b hb => Sched.tfoot_oobj hS hb) (fun b hb => B.tfoot_nh hb) (VKeep.of_tfoot hS B.thT hw)
    (fun u hu => by obtain ⟨y, hy⟩ := J.zv.vm.spec u hu; exact h1 _ _ hy) h2 h3

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **`cancel_yield_to` of a yielder at `JAtZV2`** (module docstring). -/
theorem JAtZV2.cancelYieldJ (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {y p : U64} (hy : y ∈ Z.T)
    (hp : L.mem s (yieldA y) = p) (hp0 : p ≠ 0#u64) :
    schedcontext.cancel_yield_to st s y ⦃ s' => ∃ σ',
      Fl4Spec.schedContextCancelYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64), JAtZV2 (L := L) arI V X AR Z H Cs Ac' Lst' D s' a σ' ⦄ :=
  WP.spec_mono (J.zv.base.cancelYieldJD hy hp hp0) fun _ ⟨σ', he, hK, hW, Ac', Lst', B'⟩ =>
    ⟨σ', he, Ac', Lst', J.ofTK B' hW hK⟩

end

end

end

end Fl4Proofs.P3
