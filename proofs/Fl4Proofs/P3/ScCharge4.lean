/-
P3 (DESIGN.md §9), scheduling contexts: **`end_timeslice` refines l4v
`end_timeslice`** (`end_timeslice_refines`), restoring `Inv` from `InvBut`
for the current thread. The timeout-fault branch (`handle_timeout`, IPC) and
the timeout-handler test (a CSpace read) are hypotheses (`hto`, `hval`).
-/
import Fl4Proofs.P3.ScCharge3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`end_timeslice` refines `end_timeslice`.** -/
theorem end_timeslice_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ)
    (hI : InvBut σ (nodeW st s c layout.node.CUR_THREAD).bv)
    (hsc : nodeW st s c layout.node.CUR_SC ∈ C) (hsc0 : nodeW st s c layout.node.CUR_SC ≠ 0#u64)
    (htw : L.mem s (scW (nodeW st s c layout.node.CUR_SC) 24#u64) = nodeW st s c layout.node.CUR_THREAD)
    (hts : L.mem s (scA (nodeW st s c layout.node.CUR_THREAD)) = nodeW st s c layout.node.CUR_SC)
    (hsch : Fl4Spec.schedulable (nodeW st s c layout.node.CUR_THREAD).bv σ = true)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hval : faults.valid_timeout_handler st s (nodeW st s c layout.node.CUR_THREAD) ⦃ b =>
      Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv σ = ({(b, σ)}, False) ⦄)
    (hto : faults.handle_timeout st ar s a (nodeW st s c layout.node.CUR_THREAD)
      (error.Fault.Timeout (L.mem s (scW (nodeW st s c layout.node.CUR_SC) 48#u64))) ⦃ r => ∃ σ',
      Fl4Spec.handleTimeout (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv
        (.timeout (L.mem s (scW (nodeW st s c layout.node.CUR_SC) 48#u64)).bv) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧
      σ'.consumedTime = σ.consumedTime ⦄)
    (can : Bool) :
    sched.end_timeslice st ar s a can ⦃ r => ∃ σ', Fl4Spec.endTimeslice (Z := Unit) can σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧
      σ'.consumedTime = σ.consumedTime ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  set sc := nodeW st s c layout.node.CUR_SC with hscd
  set ct := nodeW st s c layout.node.CUR_THREAD with hctd
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  have hct : ct ∈ T := hc.curT
  have hrr : decide (L.rperiod s sc = 0#u64) = decide (x.scPeriod = 0) := by
    apply decide_eq_decide.2
    rw [hx.period]
    exact ⟨fun h => by rw [h]; rfl, fun h => eq_of_bv (by rw [h]; rfl)⟩
  have hrap := rap_refines s a σ hS hR hI hsc hct htw hts hsc0 hsch hmb
  have hspec : ∀ v : Bool, Fl4Spec.isValidTimeoutHandler (Z := Unit) ct.bv σ = ({(v, σ)}, False) →
      Fl4Spec.endTimeslice (Z := Unit) can σ =
      (if can = true ∧ ¬ decide (x.scPeriod = 0) = true ∧ v = true then
        Fl4Spec.handleTimeout ct.bv (.timeout (L.mem s (scW sc 48#u64)).bv) σ
      else (do
          let ready ← Fl4Spec.getScRefillReady (Z := Unit) sc.bv
          let sufficient ← Fl4Spec.getScRefillSufficient sc.bv 0
          if ready = true ∧ sufficient = true then Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedAppend ct.bv
          else Fl4Spec.postpone sc.bv) σ) := by
    intro v hv
    unfold Fl4Spec.endTimeslice
    rw [nd_gets_bind, hs.curSc, nd_bind_one (isRoundRobin_eq hk), nd_gets_bind, hs.curThread, nd_bind_one hv]
    split_ifs
    · rw [nd_bind_one (getSchedContext_eq hk), hx.badge]
    · rfl
  unfold sched.end_timeslice
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.cur_thread.spec' as ⟨ct', hct'⟩
  rw [hc.cur] at hsc' hct'
  subst hsc' hct'
  step with sporadic.is_round_robin.spec as ⟨rr, hrr'⟩
  refine WP.spec_bind hval ?_
  intro v hv
  have hA : ¬ (can = true ∧ ¬ decide (x.scPeriod = 0) = true ∧ v = true) → (do
      let b ← sporadic.ready st s sc
      if b then do
        let b1 ← sporadic.sufficient st ar s a sc 0#u64
        if b1 then do
          let s1 ← sched.append st s ct
          ok (s1, a)
        else do
          let s1 ← sched.postpone st s sc
          ok (s1, a)
      else do
        let s1 ← sched.postpone st s sc
        ok (s1, a)) ⦃ r => ∃ σ', Fl4Spec.endTimeslice (Z := Unit) can σ = ({((), σ')}, False) ∧
          SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧
          σ'.consumedTime = σ.consumedTime ⦄ := fun hn =>
    WP.spec_mono hrap fun r ⟨_, σ', h1, h2, h3, h4, h5, h6⟩ =>
      ⟨σ', by rw [hspec v hv, ite_f hn]; exact h1, h2, h3, h5, hN.kview hR h4, h6⟩
  by_cases hcan : can = true
  · rw [if_pos hcan]
    by_cases hr : rr = true
    · rw [if_pos hr]
      exact hA (fun h => h.2.1 (hrr ▸ hrr' ▸ hr))
    · rw [if_neg hr]
      by_cases hvv : v = true
      · rw [if_pos hvv]
        step with obj.Sc.badge.spec' as ⟨bd, hbd⟩
        subst hbd
        refine WP.spec_mono hto fun r ⟨σ', h1, h2⟩ => ⟨σ', ?_, h2⟩
        rw [hspec v hv, ite_t ⟨hcan, fun h => hr (hrr' ▸ hrr ▸ h), hvv⟩]; exact h1
      · rw [if_neg hvv]
        exact hA (fun h => hvv h.2.2)
  · rw [if_neg hcan]
    exact hA (fun h => hcan h.1)
end

end

end Fl4Proofs.P3.Sched
