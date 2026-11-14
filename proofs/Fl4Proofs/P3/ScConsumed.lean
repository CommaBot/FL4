/-
P3 (DESIGN.md §9), scheduling contexts: **`schedcontext::update_consumed`
refines l4v `sched_context_update_consumed`** (`update_consumed_refines`)
and keeps `Inv`.

FL4 caps the consumed time at `U64::MAX` ticks where the spec caps it at
`maxTicksToUs` (left unspecified in the spec's `Machine`): the two agree
if the platform's `maxTicksToUs` is `2 ^ 64 - 1` (`hmax`), and FL4's
`ticks_to_us` is the spec's `ticksToUs` (`htu`).
-/
import Fl4Proofs.P3.ScCharge5
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- An SC replaced by one with the same refills, refill max, period and
TCB keeps `Inv`. -/
theorem Inv.scUpd {σ : State Unit} {p : ObjRef} (h : Inv σ) {y y' : SchedContext} {m : Nat}
    (hk : σ.kheap p = some (.schedContext y m)) (e1 : y'.scRefills = y.scRefills)
    (e2 : y'.scRefillMax = y.scRefillMax) (e3 : y'.scPeriod = y.scPeriod) (e4 : y'.scTcb = y.scTcb) :
    Inv (updSc σ p y' m) :=
  ((h.toBut p).scUpd hk e1 e2 e3 e4).inv fun x hx => by simp [updK] at hx

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`update_consumed` refines `sched_context_update_consumed`.** -/
theorem update_consumed_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {sc : U64} (hsc : sc ∈ C)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    schedcontext.update_consumed st ar s a sc ⦃ r => ∃ σ',
      Fl4Spec.schedContextUpdateConsumed (Z := Unit) sc.bv σ = ({(r.1.bv, σ')}, False) ∧
      SchedRel st N T C c r.2 σ' ∧ NtfnStateRel N T (L.mem r.2) σ' ∧ NSC N C σ' ∧ Inv σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  have hsp : Fl4Spec.schedContextUpdateConsumed (Z := Unit) sc.bv σ =
      (if Fl4Spec.maxTicksToUs ≤ x.scConsumed then
        (do
          Fl4Spec.setScObjRef Fl4Spec.scConsumedUpdate sc.bv (x.scConsumed - Fl4Spec.maxTicksToUs)
          return Fl4Spec.ticksToUs Fl4Spec.maxTicksToUs) σ
      else (do
          Fl4Spec.setScObjRef Fl4Spec.scConsumedUpdate sc.bv 0
          return Fl4Spec.ticksToUs x.scConsumed) σ) := by
    unfold Fl4Spec.schedContextUpdateConsumed
    rw [nd_bind_one (getSchedContext_eq hk), nd_pure_bind']
    split_ifs <;> rfl
  -- the write of the SC's consumed word, and the result
  have fin : ∀ (v : U64) (w : Fl4Spec.Ticks), v.bv = w → ∀ (r : U64) (tm : Fl4Spec.Ticks), r.bv = tm →
      (Fl4Spec.setScObjRef Fl4Spec.scConsumedUpdate sc.bv w >>= fun _ => pure tm) σ =
        ({(r.bv, updSc σ sc.bv { x with scConsumed := v.bv } n)}, False) ∧
      SchedRel st N T C c (L.wr s (scW sc 8#u64) v) (updSc σ sc.bv { x with scConsumed := v.bv } n) ∧
      NtfnStateRel N T (L.mem (L.wr s (scW sc 8#u64) v)) (updSc σ sc.bv { x with scConsumed := v.bv } n) ∧
      NSC N C (updSc σ sc.bv { x with scConsumed := v.bv } n) ∧ Inv (updSc σ sc.bv { x with scConsumed := v.bv } n) := by
    intro v w hv r tm hr
    obtain ⟨hS1, hf, hkv⟩ := hS.set_sc_consumed hsc hk v
    refine ⟨?_, hS1, hR.frame hS.placed hf hkv, hN.kview hR hkv, hI.scUpd hk rfl rfl rfl rfl⟩
    rw [nd_bind_one (updateSchedContext_eq hk _), hr, hv]; rfl
  unfold schedcontext.update_consumed
  step with obj.Sc.consumed.spec' as ⟨cv, hcv⟩
  have hxc : x.scConsumed = cv.bv := by rw [hx.consumed, hcv]
  by_cases hge : cv ≥ core.num.U64.MAX
  · simp only [hge, ↓reduceIte]
    have hcm : cv = core.num.U64.MAX := by
      have := cv.hBounds
      simp [core.num.U64.MAX, U64.rMax] at hge ⊢
      scalar_tac
    subst hcm
    step as ⟨i, hi⟩
    have hi0 : i = 0#u64 := by scalar_tac
    subst hi0
    step with obj.Sc.set_consumed.spec' as ⟨s1, hs1⟩
    subst hs1
    refine WP.spec_bind (htu _) ?_
    intro r hr
    simp only [WP.spec_ok]
    obtain ⟨h1, h2, h3, h4, h5⟩ := fin 0#u64 (x.scConsumed - Fl4Spec.maxTicksToUs)
      (by rw [hxc, hmax]; simp) r _ (by rw [hr, ← hmax])
    refine ⟨_, ?_, h2, h3, h4, h5⟩
    rw [hsp, if_pos (by rw [hxc, hmax]; exact BitVec.le_refl _)]
    exact h1
  · simp only [hge, ↓reduceIte]
    step with obj.Sc.set_consumed.spec' as ⟨s1, hs1⟩
    subst hs1
    refine WP.spec_bind (htu _) ?_
    intro r hr
    simp only [WP.spec_ok]
    obtain ⟨h1, h2, h3, h4, h5⟩ := fin 0#u64 0 rfl r _ (by rw [hr, ← hxc])
    refine ⟨_, ?_, h2, h3, h4, h5⟩
    rw [hsp, if_neg (by rw [hxc, hmax, ← u64_le_bv]; exact hge)]
    exact h1

end

end

end Fl4Proofs.P3.Sched
