/-
P3 (DESIGN.md §9), scheduling contexts: **`charge_budget` without timeout
faults** (`can_timeout_fault = false`: Yield, the preemption point's
inactive-thread branch), at the scheduler relation, with FL4's footprint
(toward `charge_budget` at `J`, KENTRY-PLAN item 8).

ScCharge6's `charge_budget_refines` asks the timeout-fault send (`hto`) for
every `can`; here it is asked only when `can = true`
(`end_timeslice_refinesG`) and not at all for `can = false`
(`charge_tail_refinesF`, `charge_budget_refinesF`). The copies also carry
FL4's writes: `KFoot` for the head (`charge_head_refinesK`: the ring,
`budget_check`'s `KFoot`, the SC's `CONSUMED` word) and `SFoot` for the tail
(`end_timeslice_sfootF`: `append` or `postpone`; the node words,
`reschedule_required`).
-/
import Fl4Proofs.P3.ScCharge6
import Fl4Proofs.P3.ScScheduleTop
import Fl4Proofs.P3.IpcSchedLift
import Fl4Proofs.P3.ScSwitch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- A thread out of the spec's release queue has a clear release bit. -/
theorem rel0_of {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {t : U64} (ht : t ∈ T) (hn : t.bv ∉ σ.releaseQueue) : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  by_contra hne
  exact hn (by rw [hs.rel, mem_map_bv]; exact (hc.released t ht).1 hne)

/-- **`end_timeslice` without timeout faults writes scheduler words** (`append`
or `postpone`). -/
theorem end_timeslice_sfootF (hAT : P0.ArchTotal ar) {N T C : Set U64} {c : U64} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hS : SchedRel st N T C c s σ) {sc ct : U64}
    (hcs : nodeW st s c layout.node.CUR_SC = sc) (hcc : nodeW st s c layout.node.CUR_THREAD = ct)
    (hsc : sc ∈ C) (hct : ct ∈ T) (htw : L.mem s (scW sc 24#u64) = ct)
    (hr0 : (L.mem s (inqA ct) &&& sched.Q_RELEASE) = 0#u64) :
    sched.end_timeslice st ar s a false ⦃ r => WritesIn st s r.1 (SFoot st T c s) ∧ r.2 = a ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have P : (do let s1 ← sched.postpone st s sc; ok (s1, a)) ⦃ r => WritesIn st s r.1 (SFoot st T c s) ∧ r.2 = a ⦄ :=
    WP.spec_bind (Ipc.postpone_sfootI hS hsc hct htw hr0) fun s1 h1 => by
      simp only [WP.spec_ok]
      refine ⟨h1.mono fun b hb => ?_, by first | trivial | rfl⟩
      rcases hb with ⟨y, hy, e | e | e⟩ | ⟨g1, g2, -⟩
      · exact Or.inl ⟨y, hy, 3480#u64, by unfold SOff SOffL; decide, e⟩
      · exact Or.inl ⟨y, hy, 3488#u64, by unfold SOff SOffL; decide, e⟩
      · exact Or.inl ⟨y, hy, 3592#u64, by unfold SOff SOffL; decide, e⟩
      · exact Or.inr ⟨g1, g2⟩
  have Ap : (do let s1 ← sched.append st s ct; ok (s1, a)) ⦃ r => WritesIn st s r.1 (SFoot st T c s) ∧ r.2 = a ⦄ :=
    WP.spec_bind (append_sfoot hS hct) fun s1 h1 => by simp only [WP.spec_ok]; exact ⟨h1, by first | trivial | rfl⟩
  unfold sched.end_timeslice
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.cur_thread.spec' as ⟨ct', hct'⟩
  rw [hc.cur, hcs] at hsc'
  rw [hc.cur, hcc] at hct'
  subst hsc' hct'
  step with sporadic.is_round_robin.spec as ⟨rr, _hrr⟩
  step with Notif.obj.Tcb.state.spec as ⟨state, _hst⟩
  refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun valid _ => ?_
  · split
    · exact P0.faults.valid_timeout_handler.p0 st s _ L.total
    · simp
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with sporadic.ready.spec as ⟨b, _hb⟩
  split
  · step with sporadic.sufficient.ok (st := st) hAT as ⟨b1⟩
    split
    · exact Ap
    · exact P
  · exact P

/-- **`end_timeslice` refines `end_timeslice`** (ScCharge4's
`end_timeslice_refines` with the timeout-fault premise asked only when `can`). -/
theorem end_timeslice_refinesG {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ)
    (hI : InvBut σ (nodeW st s c layout.node.CUR_THREAD).bv)
    (hsc : nodeW st s c layout.node.CUR_SC ∈ C) (hsc0 : nodeW st s c layout.node.CUR_SC ≠ 0#u64)
    (htw : L.mem s (scW (nodeW st s c layout.node.CUR_SC) 24#u64) = nodeW st s c layout.node.CUR_THREAD)
    (hts : L.mem s (scA (nodeW st s c layout.node.CUR_THREAD)) = nodeW st s c layout.node.CUR_SC)
    (hsch : Fl4Spec.schedulable (nodeW st s c layout.node.CUR_THREAD).bv σ = true)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hval : faults.valid_timeout_handler st s (nodeW st s c layout.node.CUR_THREAD) ⦃ b =>
      Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv σ = ({(b, σ)}, False) ⦄)
    (can : Bool) (hto : can = true → faults.handle_timeout st ar s a (nodeW st s c layout.node.CUR_THREAD)
      (error.Fault.Timeout (L.mem s (scW (nodeW st s c layout.node.CUR_SC) 48#u64))) ⦃ r => ∃ σ',
      Fl4Spec.handleTimeout (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv
        (.timeout (L.mem s (scW (nodeW st s c layout.node.CUR_SC) 48#u64)).bv) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧
      σ'.consumedTime = σ.consumedTime ∧ (IdleOK σ → IdleOK σ') ⦄) :
    sched.end_timeslice st ar s a can ⦃ r => ∃ σ', Fl4Spec.endTimeslice (Z := Unit) can σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧
      σ'.consumedTime = σ.consumedTime ∧ (IdleOK σ → IdleOK σ') ⦄ := by
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
  obtain ⟨tx, hkt, _, _, _, _⟩ := hs.tcb ct hct
  have hst := (hR.at_tcb hct hkt).st
  have hvm : L.mem s (tStA ct) = sched.TS_RUNNING_VM ↔ tx.tcbState = .runningVM := by
    have e8 : sched.TS_RUNNING_VM = 8#u64 := by unfold sched.TS_RUNNING_VM; rfl
    have he : ∀ x y : U64, x = y ↔ x.val = y.val := fun x y => ⟨fun h => congrArg UScalar.val h, UScalar.eq_of_val_eq⟩
    rw [e8, he, hst]
    cases tx.tcbState <;> simp [tsCode]
  have hguard : (do
      let state ← obj.Tcb.state st ct s
      if state != sched.TS_RUNNING_VM then faults.valid_timeout_handler st s ct else ok false) ⦃ b =>
      (if tx.tcbState = .runningVM then pure false else Fl4Spec.isValidTimeoutHandler (Z := Unit) ct.bv) σ =
        ({(b, σ)}, False) ⦄ := by
    step with Notif.obj.Tcb.state.spec as ⟨state, hstate⟩
    rw [hstate]
    by_cases hvm' : tx.tcbState = .runningVM
    · have hw := hvm.mpr hvm'
      simp [hw, hvm', pure, Fl4Spec.NonDet.pure]
    · have hw := fun e => hvm' (hvm.mp e)
      simpa only [bne_iff_ne, if_pos hw, if_neg hvm'] using hval
  have hspec : ∀ v : Bool, (if tx.tcbState = .runningVM then pure false else Fl4Spec.isValidTimeoutHandler (Z := Unit) ct.bv) σ = ({(v, σ)}, False) →
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
    rw [nd_gets_bind, hs.curSc, nd_bind_one (isRoundRobin_eq hk), nd_gets_bind, hs.curThread, nd_bind_one (getThreadState_eq hkt)]
    by_cases hvm' : tx.tcbState = .runningVM
    all_goals simp only [hvm', ↓reduceIte] at hv ⊢
    all_goals rw [nd_bind_one hv]
    all_goals split_ifs
    all_goals first | (rw [nd_bind_one (getSchedContext_eq hk), hx.badge]) | rfl
  unfold sched.end_timeslice
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.cur_thread.spec' as ⟨ct', hct'⟩
  rw [hc.cur] at hsc' hct'
  subst hsc' hct'
  step with sporadic.is_round_robin.spec as ⟨rr, hrr'⟩
  rw [← Aeneas.Std.bind_assoc]
  refine WP.spec_bind hguard ?_
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
          σ'.consumedTime = σ.consumedTime ∧ (IdleOK σ → IdleOK σ') ⦄ := fun hn =>
    WP.spec_mono hrap fun r ⟨_, σ', h1, h2, h3, h4, h5, h6, h7⟩ =>
      ⟨σ', by rw [hspec v hv, ite_f hn]; exact h1, h2, h3, h5, hN.kview hR h4, h6, h7⟩
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
        refine WP.spec_mono (hto hcan) fun r ⟨σ', h1, h2⟩ => ⟨σ', ?_, h2⟩
        rw [hspec v hv, ite_t ⟨hcan, fun h => hr (hrr' ▸ hrr ▸ h), hvv⟩]; exact h1
      · rw [if_neg hvv]
        exact hA (fun h => hvv h.2.2)
  · rw [if_neg hcan]
    exact hA (fun h => hcan h.1)

/-- **`charge_budget` before the consumed-time reset** (ScCharge6's
`charge_head_refines` with FL4's footprint, `KFoot`). -/
theorem charge_head_refinesK {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hscC : nodeW st s c layout.node.CUR_SC ∈ C)
    (htw : L.mem s (scW (nodeW st s c layout.node.CUR_SC) 24#u64) = nodeW st s c layout.node.CUR_THREAD)
    (hact : (nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc → ∀ x n,
      σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) → Fl4Spec.scActive x = true)
    (hnr : (nodeW st s c layout.node.CUR_THREAD).bv ∉ σ.releaseQueue)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) (used : U64) (b : Bool)
    (hb : b = decide ((nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc)) :
    (if b then do
      let b1 ← sporadic.is_round_robin st s (nodeW st s c layout.node.CUR_SC)
      let s3 ← if b1 then do
          let hi ← obj.Sc.refill_head st (nodeW st s c layout.node.CUR_SC) s
          let ti ← obj.Sc.refill_tail st (nodeW st s c layout.node.CUR_SC) s
          let h ← sporadic.get st s (nodeW st s c layout.node.CUR_SC) hi
          let t ← sporadic.get st s (nodeW st s c layout.node.CUR_SC) ti
          let i ← lift (core.num.U64.wrapping_add h.amount t.amount)
          let s4 ← sporadic.put st s (nodeW st s c layout.node.CUR_SC) hi { h with amount := i }
          sporadic.put st s4 (nodeW st s c layout.node.CUR_SC) ti { t with amount := 0#u64 }
        else sporadic.budget_check st ar s a used
      let i ← obj.Sc.consumed st (nodeW st s c layout.node.CUR_SC) s3
      let total ← lift (core.num.U64.wrapping_add i used)
      obj.Sc.set_consumed st (nodeW st s c layout.node.CUR_SC) s3 total
    else ok s) ⦃ s2 => ∃ σ2, chargeHead used.bv σ = ({((), σ2)}, False) ∧
      SchedRel st N T C c s2 σ2 ∧ NtfnStateRel N T (L.mem s2) σ2 ∧ NSC N C σ2 ∧
      InvBut σ2 (nodeW st s c layout.node.CUR_THREAD).bv ∧
      HeadKeeps σ σ2 (nodeW st s c layout.node.CUR_SC).bv ∧
      TmoKeep st (nodeW st s c layout.node.CUR_THREAD) s σ s2 σ2 ∧
      WritesIn st s s2 (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  set sc := nodeW st s c layout.node.CUR_SC with hscd
  set ct := nodeW st s c layout.node.CUR_THREAD with hctd
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hscC
  have hct : ct ∈ T := hc.curT
  have hct0 : ct ≠ 0#u64 := fun e => (hc.tcbs ct hct).ne0 (by rw [e]; rfl)
  have hown : x.scTcb = some ct.bv := by rw [hx.tcb, htw, optRef_ne hct0]
  obtain ⟨xct, hkct, -⟩ := hs.tcb ct hct
  have hcts : ct.bv ≠ sc.bv := fun e => by rw [e, hk] at hkct; cases hkct
  have hupd : ∀ (σ0 : Fl4Spec.State Unit) (y : Fl4Spec.SchedContext) (m : Nat),
      (updSc σ0 sc.bv y m).kheap ct.bv = σ0.kheap ct.bv := fun σ0 y m => by
    simp [updK, Function.update_of_ne hcts]
  have hspec : chargeHead used.bv σ = Fl4Spec.NonDet.when (sc.bv ≠ σ.idleSc) (do
      let robin ← Fl4Spec.isRoundRobin (Z := Unit) sc.bv
      if robin
      then Fl4Spec.refillResetRr sc.bv
      else Fl4Spec.refillBudgetCheck used.bv
      Fl4Spec.updateSchedContext sc.bv (fun y => { y with scConsumed := y.scConsumed + used.bv })) σ := by
    unfold chargeHead; rw [nd_gets_bind, nd_gets_bind, hs.curSc]
  by_cases hid : sc.bv ≠ σ.idleSc
  · have hb' : b = true := by rw [hb]; simpa using hid
    simp only [hb', ↓reduceIte]
    have hrr : decide (L.rperiod s sc = 0#u64) = decide (x.scPeriod = 0) := by
      apply decide_eq_decide.2
      rw [hx.period]
      exact ⟨fun h => by rw [h]; rfl, fun h => eq_of_bv (by rw [h]; rfl)⟩
    have hspec2 : ∀ (σ3 : Fl4Spec.State Unit),
        (if decide (x.scPeriod = 0) = true then Fl4Spec.refillResetRr (Z := Unit) sc.bv
          else Fl4Spec.refillBudgetCheck used.bv) σ = ({((), σ3)}, False) →
        chargeHead used.bv σ = Fl4Spec.updateSchedContext (Z := Unit) sc.bv
          (fun y => { y with scConsumed := y.scConsumed + used.bv }) σ3 := by
      intro σ3 h3
      rw [hspec]; unfold Fl4Spec.NonDet.when; rw [if_pos hid, nd_bind_one (isRoundRobin_eq hk)]
      split_ifs at h3 ⊢ <;> exact nd_bind_one h3 _
    -- the consumed update and the result, from the state after the refill update
    have fin : ∀ (s3 : S) (y' : Fl4Spec.SchedContext), y' = { x with scRefills := y'.scRefills } →
        (if decide (x.scPeriod = 0) = true then Fl4Spec.refillResetRr (Z := Unit) sc.bv
          else Fl4Spec.refillBudgetCheck used.bv) σ = ({((), updSc σ sc.bv y' n)}, False) →
        SchedRel st N T C c s3 (updSc σ sc.bv y' n) → NtfnStateRel N T (L.mem s3) (updSc σ sc.bv y' n) →
        NSC N C (updSc σ sc.bv y' n) → InvBut (updSc σ sc.bv y' n) ct.bv →
        TmoKeep st ct s σ s3 (updSc σ sc.bv y' n) → WritesIn st s s3 (KFoot st T N C c s σ) →
        (do
          let i ← obj.Sc.consumed st sc s3
          let total ← lift (core.num.U64.wrapping_add i used)
          obj.Sc.set_consumed st sc s3 total) ⦃ s2 => ∃ σ2, chargeHead used.bv σ = ({((), σ2)}, False) ∧
          SchedRel st N T C c s2 σ2 ∧ NtfnStateRel N T (L.mem s2) σ2 ∧ NSC N C σ2 ∧
          InvBut σ2 ct.bv ∧ HeadKeeps σ σ2 sc.bv ∧ TmoKeep st ct s σ s2 σ2 ∧
          WritesIn st s s2 (KFoot st T N C c s σ) ⦄ := by
      intro s3 y' hy' h3 hS3 hR3 hN3 hI3 hT3 hW3
      have hk3 : (updSc σ sc.bv y' n).kheap sc.bv = some (.schedContext y' n) := by simp [updK]
      refine WP.spec_mono (consumed_refines s3 _ hS3 hR3 hN3 hI3 hscC hk3 used) ?_
      rintro s2 ⟨σ2, h1, rfl, h2, h3', h4, h5, hw5⟩
      refine ⟨_, by rw [hspec2 _ h3]; exact h1, h2, h3', h4, h5, ?_, ?_, ?_⟩
      · rw [updSc_updSc]
        exact HeadKeeps.updSc hk (by rw [hy']) (by rw [hy'])
      · refine hT3.trans (TmoKeep.of_kheap hw5 (fun b e => ?_) (hupd _ _ _))
        subst e
        obtain ⟨Q3, R3, -, hs3⟩ := hS3.lists
        obtain ⟨x3, n3, hk3', hx3⟩ := hs3.scs sc hscC
        rw [hk3] at hk3'; cases hk3'
        have := (hS3.scOut sc hscC _ _ hk3 _ (hx3.in_obj (hx3.hdr (K := 8#u64) (by simp) (by simp)).2)).2.2.1 ct hct
        omega
      · refine (hW3.trans hw5).mono fun b hb => ?_
        rcases hb with hb | rfl
        · exact hb
        · exact KFoot.of_sw (sw_hdr hS hscC (K := 8#u64) (by simp) (by simp) (by decide))
    step with sporadic.is_round_robin.spec as ⟨rr, hrr'⟩
    subst hrr'
    by_cases h0 : L.rperiod s sc = 0#u64
    · have e0 : decide (L.rperiod s sc = 0#u64) = true := decide_eq_true h0
      have hper : x.scPeriod = 0 := by have := hrr ▸ e0; simpa using this
      simp only [e0, ↓reduceIte]
      have hx := hx.strong (hact hid x n hk)
      refine WP.spec_bind (rr_reset_refines (RingAt.refl hx.wf)) ?_
      rintro s3 ⟨hring, hl⟩
      obtain ⟨hS3, hf, hkv⟩ := hS.ringAt hscC hk hring
      rw [hl] at hS3 hkv
      have hne := refills_ne' hx.wf
      have hI3 : InvBut (updSc σ sc.bv { x with scRefills := (rrResetL (L.refills s sc)).map toRefill } n) ct.bv :=
        hI.refillUpd hk rfl (by simp [rrResetL]) (fun _ hp => absurd hper hp)
          (fun _ _ => rrResetL_rr hx.refills (hI.rr _ x n hk (hact hid x n hk) hper)) (Or.inl hown) hnr
      refine fin s3 _ rfl ?_ hS3 (by rw [← hl]; rw [← hl] at hkv; exact hR.frame hS.placed hf hkv)
        (hN.kview hR hkv) hI3 (TmoKeep.of_kheap (RingAt.kfoot hS hscC hring) (fun b hb => kfoot_tslot hS hct hb)
          (hupd _ _ _)) (RingAt.kfoot hS hscC hring)
      rw [if_pos (by simpa using hper)]
      exact refillResetRr_eq hk hx.refills hne |>.trans rfl
    · have e0 : decide (L.rperiod s sc = 0#u64) = false := decide_eq_false h0
      have hper : ¬ x.scPeriod = 0 := by
        intro e; have := hrr ▸ e0; simp [e] at this
      simp only [e0, Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_bind (budget_check_refines_inv s a σ hS hI hscC (hact hid) hmrt hmb h0 used
        (fun y m h => by rw [hk] at h; cases h; exact Or.inl hown) hnr) ?_
      rintro s3 ⟨σ3, h1, hf, hkv, hS3, hI3, hpost, hw3⟩
      obtain ⟨y', rfl, hy', -⟩ := hpost x n hk
      exact fin s3 y' hy' (by rw [if_neg (by simpa using hper)]; exact h1) hS3 (hR.frame hS.placed hf hkv)
        (hN.kview hR hkv) hI3 (TmoKeep.of_kheap hw3 (fun b hb => kfoot_tslot hS hct hb) (hupd _ _ _)) hw3
  · have hb' : b = false := by rw [hb]; simpa using hid
    simp only [hb', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ, ?_, hS, hR, hN, hI.toBut _, HeadKeeps.refl σ _, TmoKeep.refl _ _ _, WritesIn.refl _ _⟩
    rw [hspec]; unfold Fl4Spec.NonDet.when; rw [if_neg hid]; rfl


/-- **`charge_budget` after the head, without timeout faults** (ScCharge6's
`charge_tail_refines` at `can = false`, with FL4's footprint): the consumed-time reset, and for a
schedulable current thread `end_timeslice`, `reschedule_required` and the
reprogram flag. -/
theorem charge_tail_refinesF {N T C : Set U64} {c : U64} (s2 : S) (a : A) (σ2 : Fl4Spec.State Unit)
    (hAT : P0.ArchTotal ar) (hS : SchedRel st N T C c s2 σ2) (hR : NtfnStateRel N T (L.mem s2) σ2) (hN : NSC N C σ2)
    {sc ct : U64} (hI : InvBut σ2 ct.bv) (hcs : σ2.curSc = sc.bv) (hcc : σ2.curThread = ct.bv)
    (hscC : sc ∈ C) (hsc0 : sc ≠ 0#u64) {xt : Fl4Spec.Tcb} (hkt : σ2.kheap ct.bv = some (.tcb xt))
    (hxs : xt.tcbSchedContext = some sc.bv) (hnb : NotIpcBlk xt.tcbState)
    {y2 : Fl4Spec.SchedContext} {n2 : Nat} (hky : σ2.kheap sc.bv = some (.schedContext y2 n2))
    (hyt : y2.scTcb = some ct.bv)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hval : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' →
      TmoKeep st ct s2 σ2 s' σ' →
      faults.valid_timeout_handler st s' ct ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) ct.bv σ' = ({(b, σ')}, False) ⦄) :
    (do
      let s3 ← sched.set_consumed st s2 0#u64
      let ct ← sched.cur_thread st s3
      let b1 ← sched.is_schedulable st s3 ct
      if b1
      then
        let (s4, a1) ← sched.end_timeslice st ar s3 a false
        let s5 ← sched.reschedule_required st s4
        let s6 ← sched.set_reprogram st s5
        ok (s6, a1)
      else ok (s3, a)) ⦃ r => ∃ σ', chargeTail false σ2 = ({((), σ')}, False) ∧
        SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧
        (σ'.schedulerAction = .chooseNewThread ∨ σ' = { σ2 with consumedTime := 0 }) ∧ σ'.consumedTime = 0 ∧
        (IdleOK σ2 → IdleOK σ') ∧ WritesIn st s2 r.1 (SFoot st T c s2) ∧ r.2 = a ⦄ := by
  have hc2 := hS.lists.choose_spec.choose_spec.1.cur
  have hN2 := hS.lists.choose_spec.choose_spec.1.node
  step with sched.set_consumed.spec' as ⟨s3, hs3⟩
  rw [hc2] at hs3
  subst hs3
  have w3 := sfoot_wr_node hN2 (o := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
    (by simp [layout.node.CONSUMED]) 0#u64
  obtain ⟨hS3', hf3, -⟩ := hS.set_node_consumed 0#u64
  set σ3 : Fl4Spec.State Unit := { σ2 with consumedTime := 0 } with hσ3
  have hS3 : SchedRel st N T C c (L.wr s2 (L.nodeAt s2 c layout.node.CONSUMED) 0#u64) σ3 := hS3'
  set s3 := L.wr s2 (L.nodeAt s2 c layout.node.CONSUMED) 0#u64 with hs3d
  have hR3 : NtfnStateRel N T (L.mem s3) σ3 := hR.frame hS.placed hf3 (KView.of_kheap rfl)
  have hN3 : NSC N C σ3 := hN
  have hI3 : InvBut σ3 ct.bv := hI.congr rfl rfl rfl rfl
  obtain ⟨Q3, R3, hc3, hs3⟩ := hS3.lists
  have e1 : nodeW st s3 c layout.node.CUR_THREAD = ct := eq_of_bv (by rw [← hs3.curThread]; exact hcc)
  have e2 : nodeW st s3 c layout.node.CUR_SC = sc := eq_of_bv (by rw [← hs3.curSc]; exact hcs)
  have hct : ct ∈ T := e1 ▸ hc3.curT
  step with sched.cur_thread.spec' as ⟨ct', hct'⟩
  rw [hc3.cur, e1] at hct'
  subst ct'
  step with sched.is_schedulable.spec' as ⟨b1, hb1⟩
  rw [schedulable_eq hR3 hS3 hct] at hb1
  subst hb1
  have hspec := chargeTail_eq false σ2 hcc
  rw [← hσ3] at hspec
  by_cases hsch : Fl4Spec.schedulable ct.bv σ3 = true
  · simp only [hsch, ↓reduceIte]
    rw [if_pos hsch] at hspec
    have hE := end_timeslice_refinesG (ar := ar) s3 a σ3 hS3 hR3 hN3 (by rw [e1]; exact hI3) (by rw [e2]; exact hscC)
      (by rw [e2]; exact hsc0) (by rw [e1, e2]; exact word24_of hS3 hscC hky hyt)
      (by rw [e1, e2]; exact scA_of hS3 hct hkt hxs) (by rw [e1]; exact hsch) hmb
      (by rw [e1]; exact hval s3 σ3 hS3 (TmoKeep.node_wr hS hct (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) 0#u64 rfl)) false (fun h => absurd h Bool.false_ne_true)
    obtain ⟨-, -, -, -, -, -, -, -, -, hnr3⟩ := schedulable_inv hsch
    refine WP.spec_bind (WP.spec_and hE (end_timeslice_sfootF hAT s3 a σ3 hS3 e2 e1 hscC hct
      (word24_of hS3 hscC hky hyt) (rel0_of hS3 hct hnr3))) ?_
    rintro ⟨s4, a1⟩ ⟨⟨σ4, h4, hS4, hI4, hR4, hN4, hc4, hid4⟩, hw4, ha4⟩
    refine WP.spec_bind (WP.spec_and (reschedule_required_refines s4 σ4 hR4 hS4 hI4.actReady)
      (reschedule_required_sfoot hS4)) ?_
    rintro s5 ⟨⟨σ5, h5, hk5, hr5, hf5, hS5⟩, hw5⟩
    obtain ⟨σ5', h5', hq5, hcm5⟩ := rescheduleRequired_calm hI4.actReady
    rw [h5'] at h5
    have e5 : σ5 = σ5' := pair_eq h5
    subst e5
    have hI5 : Inv σ5 := hI4.qchange hq5
    have hkv5 : KView σ4 σ5 := KView.of_kheap hk5
    have hR5 : NtfnStateRel N T (L.mem s5) σ5 := hR4.frame hS4.placed hf5 hkv5
    have hN5 : NSC N C σ5 := hN4.kview hR4 hkv5
    step with sched.set_reprogram.spec' as ⟨s6, hs6⟩
    rw [hS5.lists.choose_spec.choose_spec.1.cur] at hs6
    subst hs6
    have hw6 := sfoot_wr_node hS5.lists.choose_spec.choose_spec.1.node (o := layout.node.REPROGRAM)
      (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) 1#u64
    obtain ⟨hS6, hf6, -⟩ := hS5.set_reprogram
    refine ⟨{ σ5 with reprogramTimer := true }, ?_, hS6, hI5.congr rfl rfl rfl rfl,
      hR5.frame hS5.placed hf6 (KView.of_kheap rfl), hN5, Or.inl (rescheduleRequired_action (σ' := σ5) hI4.actReady h5' :),
      (rescheduleRequired_consumed (σ' := σ5) hI4.actReady h5').trans hc4, fun hid => ?_,
      WritesIn.sfoot_trans (WritesIn.sfoot_trans (WritesIn.sfoot_trans w3 hw4) hw5) hw6, ha4⟩
    · rw [hspec, nd_bind_one h4, nd_bind_one h5']
      rfl
    · have hid5 : IdleOK σ5 := (hid4 (IdleOK.of hid rfl rfl id)).of hcm5.2.2.2.2.2.1
        (by rw [hcm5.1]) (fun hm => by rw [hq5.2.1] at hm; exact hm) hcm5.isc
      exact hid5.of rfl rfl id
  · simp only [Bool.not_eq_true] at hsch
    simp only [hsch, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ3, ?_, hS3, ?_, hR3, hN3, Or.inr rfl, rfl, fun hid => IdleOK.of hid rfl rfl id, w3, by first | trivial | rfl⟩
    · rw [hspec, if_neg (by rw [hsch]; exact Bool.false_ne_true)]
    · refine hI3.inv fun x hx hcl => ?_
      intro x' scp y n h1 h2 h3 h4 h5
      have hkt3 : σ3.kheap ct.bv = some (.tcb xt) := hkt
      rw [hkt3] at hx h1; cases hx; cases h1
      have := schedulable_of hkt3 h2 (inClass_runnable hcl.cls hnb) h3 h4 h5
      rw [hsch] at this; cases this

/-- **`charge_budget` without timeout faults refines l4v `charge_budget`**
(ScCharge6's `charge_budget_refines` at `can_timeout_fault = false`: no
`hto`; with FL4's footprint, `KFoot`). -/
theorem charge_budget_refinesF {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hAT : P0.ArchTotal ar) (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hscC : nodeW st s c layout.node.CUR_SC ∈ C) (hsc0 : nodeW st s c layout.node.CUR_SC ≠ 0#u64)
    (htw : L.mem s (scW (nodeW st s c layout.node.CUR_SC) 24#u64) = nodeW st s c layout.node.CUR_THREAD)
    (hts : L.mem s (scA (nodeW st s c layout.node.CUR_THREAD)) = nodeW st s c layout.node.CUR_SC)
    (hidle : (nodeW st s c layout.node.IDLE_SC).bv = σ.idleSc)
    (hact : (nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc → ∀ x n,
      σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) → Fl4Spec.scActive x = true)
    (hnr : (nodeW st s c layout.node.CUR_THREAD).bv ∉ σ.releaseQueue)
    (hnb : ∀ xt, σ.kheap (nodeW st s c layout.node.CUR_THREAD).bv = some (.tcb xt) →
      NotIpcBlk xt.tcbState)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hval : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' →
      TmoKeep st (nodeW st s c layout.node.CUR_THREAD) s σ s' σ' →
      faults.valid_timeout_handler st s' (nodeW st s c layout.node.CUR_THREAD) ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv σ' =
          ({(b, σ')}, False) ⦄)
    (used : U64) :
    sched.charge_budget st ar s a used false ⦃ r => ∃ σ',
      Fl4Spec.chargeBudget (Z := Unit) used.bv false σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧
      (σ'.schedulerAction = .chooseNewThread ∨ HeadKeeps σ σ' (nodeW st s c layout.node.CUR_SC).bv) ∧
      σ'.consumedTime = 0 ∧ (ActIdle σ → ActIdle σ') ∧ WritesIn st s r.1 (KFoot st T N C c s σ) ∧ r.2 = a ∧
      ∃ σ2, HeadKeeps σ σ2 (nodeW st s c layout.node.CUR_SC).bv ∧ chargeTail false σ2 = ({((), σ')}, False) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hct : nodeW st s c layout.node.CUR_THREAD ∈ T := hc.curT
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb _ hct
  have hxs : xt.tcbSchedContext = some (nodeW st s c layout.node.CUR_SC).bv := by
    rw [hsct, hts, optRef_ne hsc0]
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hct0 : nodeW st s c layout.node.CUR_THREAD ≠ 0#u64 := fun e => (hc.tcbs _ hct).ne0 (by rw [e]; rfl)
  have hown : x.scTcb = some (nodeW st s c layout.node.CUR_THREAD).bv := by rw [hx.tcb, htw, optRef_ne hct0]
  unfold sched.charge_budget
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.idle_sc.spec' as ⟨id', hid'⟩
  rw [hc.cur] at hsc' hid'
  subst hsc' hid'
  rw [sc_ne_eq]
  simp only [bind_ok]
  have hb : decide (nodeW st s c layout.node.CUR_SC ≠ nodeW st s c layout.node.IDLE_SC) =
      decide ((nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc) := by
    rw [← hidle]
    apply decide_eq_decide.2
    exact ⟨fun h e => h (eq_of_bv e), fun h e => h (by rw [e])⟩
  refine WP.spec_bind (charge_head_refinesK s a σ hS hR hN hI hscC htw hact hnr hmrt hmb used _ hb) ?_
  rintro s2 ⟨σ2, h2, hS2, hR2, hN2, hI2, hK, hTK, hW2⟩
  have ⟨hcs, hcc, _, _, _, _, _, _, hfr, hsck⟩ := hK
  obtain ⟨y2, hky, hyt, -⟩ := hsck x n hk
  have hkt2 : σ2.kheap (nodeW st s c layout.node.CUR_THREAD).bv = some (.tcb xt) := by
    rw [hfr _ (fun e => by rw [e, hk] at hkt; cases hkt)]; exact hkt
  refine WP.spec_mono (charge_tail_refinesF s2 a σ2 hAT hS2 hR2 hN2 hI2 (by rw [hcs, hs.curSc])
    (by rw [hcc, hs.curThread]) hscC hsc0 hkt2 hxs (hnb xt hkt) hky (by rw [hyt]; exact hown) hmb (fun s' σ' h1 h2 => hval s' σ' h1 (hTK.trans h2))) ?_
  rintro r ⟨σ', h1, h3, h4, h5, h6, h7, h8, h9, hw, hra⟩
  refine ⟨σ', by rw [chargeBudget_eq, nd_bind_one h2]; exact h1, h3, h4, h5, h6, ?_, h8, fun hA => ?_, WritesIn.kfoot_sfoot hW2 hw, hra, σ2, hK, h1⟩
  · rcases h7 with h7 | rfl
    · exact Or.inl h7
    · exact Or.inr hK
  · have hA2 := hA.headKeeps hK ⟨x, n, hk⟩
    rcases h7 with h7 | rfl
    · exact ActIdle.of_noswitch (h9 hA2.2) (fun t e => by rw [h7] at e; cases e)
    · exact hA2.keep (TKeepE.of_kheap _ rfl) (fun _ h => h) (Or.inl rfl) rfl

end

end

end Fl4Proofs.P3.Sched
