/-
P3 (DESIGN.md §9), scheduling contexts: **`unblock_sporadic` refines the
spec's sporadic unblock check** (`get_tcb_obj_ref tcb_sched_context t >>=
if_sporadic_cur_sc_test_refill_unblock_check`, the tail of a wake-up),
discharging `WakeHyps.unblock` (SchedNtfn.lean).
-/
import Fl4Proofs.P3.ScUnblock
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

@[step] theorem sched.cur_sc.spec' (s : S) :
    sched.cur_sc st s ⦃ v => v = nodeW st s (L.cpu s) layout.node.CUR_SC ⦄ := by
  unfold sched.cur_sc; step*; simp_all [nodeW]

theorem sc_ne_eq (a b : obj.Sc) :
    core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc a b = ok (decide (a ≠ b)) := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  simp [obj.Sc.Insts.CoreCmpPartialEqSc.eq]
  exact ⟨fun h => h ▸ rfl, UScalar.eq_of_val_eq⟩

theorem bne_zero (y : U64) : (y != 0#u64) = !decide (y.val = 0) := by
  by_cases e : y = 0#u64
  · subst e; rfl
  · have : y.val ≠ 0 := fun h => e (UScalar.eq_of_val_eq (by simpa using h))
    simp [e, this]

@[step] theorem sporadic.sc_sporadic.spec' (s : S) (sc : obj.Sc) :
    sporadic.sc_sporadic st s sc ⦃ b => b = decide (sc ≠ 0#u64 ∧ L.mem s (scW sc 64#u64) ≠ 0#u64) ⦄ := by
  unfold sporadic.sc_sporadic obj.Sc.sporadic
  step
  by_cases h : sc = 0#u64
  · have : b = true := by rw [b_post]; simp [h]
    simp [this, h]
  · have : b = false := by rw [b_post]; simp [h]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    step*
    simp_all [scW, layout.sc.SPORADIC, bne_zero]

/-- **`unblock_sporadic` refines the spec's unblock check** (`WakeHyps.unblock`). -/
theorem unblock_sporadic_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (t : U64) (ht : t ∈ T) :
    notification.unblock_sporadic st s t ⦃ s' => ¬ (specUnblock t.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (specUnblock t.bv σ).1 ∧ FootEq N T (L.mem s) (L.mem s') ∧ KView σ σ' ∧
        SchedRel st N T C c s' σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  have hspec0 : specUnblock t.bv σ = (Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit)
      (optRef (L.mem s (scA t)))) σ := by
    unfold specUnblock Fl4Spec.getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hkt), hsct]
  -- a single spec outcome suffices
  have fin : ∀ s' σ', Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t))) σ =
      ({((), σ')}, False) → FootEq N T (L.mem s) (L.mem s') → KView σ σ' → SchedRel st N T C c s' σ' →
      ¬ (specUnblock t.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (specUnblock t.bv σ).1 ∧ FootEq N T (L.mem s) (L.mem s') ∧
        KView σ σ' ∧ SchedRel st N T C c s' σ' := by
    intro s' σ' he hf hv hS'
    rw [hspec0, he]
    exact ⟨id, σ', rfl, hf, hv, hS'⟩
  unfold notification.unblock_sporadic
  step
  rw [i_post]
  step
  by_cases h0 : L.mem s (scA t) = 0#u64
  · have hb : b = false := by rw [b_post]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine fin s σ ?_ FootEq.rfl' (KView.refl σ) hS
    rw [h0, optRef_zero]; rfl
  · have hscC := hs.scMem t ht h0
    obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
    have hsp : (x.scSporadic = true) ↔ L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64 := by
      rw [hx.sporadic]; simp
    have hif : ∀ (P : Prop) [Decidable P] (Q : Prop) [Decidable Q],
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t))) σ =
          (if x.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc then
            Fl4Spec.refillUnblockCheck (L.mem s (scA t)).bv σ else ({((), σ)}, False)) := by
      intro _ _ _ _
      rw [optRef_ne h0]
      unfold Fl4Spec.ifSporadicCurScTestRefillUnblockCheck Fl4Spec.ifCondRefillUnblockCheck
      simp only [Fl4Spec.NonDet.maybeM]
      rw [nd_bind_one (getSchedContext_eq hk), nd_gets_bind, nd_pure_bind']
      simp only [Fl4Spec.NonDet.when]
      by_cases e : x.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc
      · simp only [e, ne_eq, not_false_eq_true, forall_const, and_self, ↓reduceIte, Option.some.injEq,
          Bool.false_eq_true, IsEmpty.forall_iff]
      · simp only [ne_eq, forall_const, ↓reduceIte, Option.some.injEq]
        rw [ite_f (c := x.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc) (by simpa only [ne_eq] using e),
          ite_f (c := x.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc) (by simpa only [ne_eq] using e)]
        rfl
    have hif' := hif True True
    by_cases hsp' : L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64
    · have hb : b = true := by rw [b_post]; simp [h0, hsp']
      simp only [hb, ↓reduceIte]
      step
      rw [sc_ne_eq]
      simp only [bind_ok]
      rw [s1_post, hc.cur]
      by_cases e : L.mem s (scA t) = nodeW st s c layout.node.CUR_SC
      · simp only [e, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        refine fin s σ ?_ FootEq.rfl' (KView.refl σ) hS
        rw [hif', ite_f]; rw [e, ← hs.curSc]; simp
      · simp only [e, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
        refine WP.spec_mono (unblock_check_refines s σ hS hscC (hx.spor hsp')) ?_
        rintro s' ⟨σ', he, hf, hv, hS'⟩
        refine fin s' σ' ?_ hf hv hS'
        rw [hif', ite_t ⟨hsp.2 hsp', by rw [hs.curSc]; exact bv_ne e⟩, he]
    · have hb : b = false := by rw [b_post]; simp [h0]; simpa using hsp'
      simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine fin s σ ?_ FootEq.rfl' (KView.refl σ) hS
      rw [hif', ite_f (fun h => hsp' (hsp.1 h.1))]

end

end

end Fl4Proofs.P3.Sched
