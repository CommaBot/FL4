/-
P3 (DESIGN.md §9), scheduling contexts: **`commit_time` refines l4v
`commit_time`** (`commit_time_refines`). It charges the consumed time to the
current SC (round-robin: `refill_budget_check_round_robin`, `rrChargeL`;
otherwise `refill_budget_check`) without requeueing the current thread, so it
keeps `InvBut` for the current thread, as in l4v (where the current thread's
budget is checked by `check_budget`, not by `valid_sched`).
-/
import Fl4Proofs.P3.ScHead
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- `commit_time` before the consumed-time reset. -/
def commitHead : SMonad Unit Unit := do
  let csc ← Fl4Spec.NonDet.gets fun s : State Unit => s.curSc
  let active ← getScActive csc
  let isc ← Fl4Spec.NonDet.gets fun s : State Unit => s.idleSc
  Fl4Spec.NonDet.when (active ∧ csc ≠ isc) <| do
    let consumed ← Fl4Spec.NonDet.gets fun s : State Unit => s.consumedTime
    Fl4Spec.NonDet.when (0 < consumed) <| do
      let robin ← isRoundRobin csc
      if robin
      then refillBudgetCheckRoundRobin consumed
      else refillBudgetCheck consumed
    updateSchedContext csc fun sc => { sc with scConsumed := sc.scConsumed + consumed }

theorem commitTime_eq (σ : State Unit) :
    commitTime (Z := Unit) σ =
      (commitHead >>= fun _ => Fl4Spec.NonDet.modify fun s : State Unit => { s with consumedTime := 0 }) σ := by
  unfold commitTime commitHead
  simp only [nd_bind_assoc', nd_gets_bind]
  have e : ∀ (m : SMonad Unit Bool) (F G : Bool → SMonad Unit Unit), (∀ a s, F a s = G a s) →
      (m >>= F) σ = (m >>= G) σ :=
    fun m F G h => by rw [show F = G from funext fun a => funext fun s => h a s]
  apply e
  intro a s
  simp only [nd_bind_assoc']

theorem getScActive_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) :
    getScActive (Z := Unit) p σ = ({(scActive x, σ)}, False) := by
  have : readScActive (Z := Unit) p σ = some (scActive x) := by
    show Option.bind (readSchedContext p σ) (fun sc => Lookup.oreturn (scActive sc) σ) = _
    rw [readSchedContext_eq hk]; rfl
  simp [getScActive, Fl4Spec.NonDet.getsThe, this, Fl4Spec.NonDet.assertOpt]; rfl

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

theorem sc_active_spec (s : S) (sc : obj.Sc) :
    sporadic.sc_active st s sc ⦃ b => b = decide (L.rmax s sc > 0#u64) ⦄ := by
  unfold sporadic.sc_active
  step with obj.Sc.refill_max.spec as ⟨i, hi⟩
  simp [hi]

/-- **FL4's round-robin charge** is `rrChargeL` on the list. -/
theorem rr_charge_refines {s0 s : S} {sc : U64} {n : Nat} (h : RingAt st s0 s sc n) (c : U64) :
    (do
      let hi ← obj.Sc.refill_head st sc s
      let ti ← obj.Sc.refill_tail st sc s
      let h ← sporadic.get st s sc hi
      let i ← lift (core.num.U64.wrapping_sub h.amount c)
      let s4 ← sporadic.put st s sc hi { h with amount := i }
      let t ← sporadic.get st s4 sc ti
      let i1 ← lift (core.num.U64.wrapping_add t.amount c)
      sporadic.put st s4 sc ti { t with amount := i1 }) ⦃ s' => RingAt st s0 s' sc n ∧
        L.refills s' sc = rrChargeL (L.refills s sc) c ⦄ := by
  step with obj.Sc.refill_head.spec as ⟨hi, hhi⟩
  step with obj.Sc.refill_tail.spec as ⟨ti, hti⟩
  step with sporadic.get.spec as ⟨hr, hhr⟩
  simp only [lift, bind_ok]
  step with sporadic.put.spec as ⟨s4, hs4⟩
  step with sporadic.get.spec as ⟨tr, htr⟩
  try simp only [lift, bind_ok]
  refine WP.spec_mono (sporadic.put.spec s4 sc ti _) ?_
  rintro s5 rfl
  subst hhi hti hhr hs4 htr
  have hW := h.wf
  obtain ⟨h8, hb, hfit⟩ := hW.bounds
  have hhl := hW.head_lt
  set r1 : sporadic.Refill := ⟨(L.refill s sc (L.rhead s sc)).time, core.num.U64.wrapping_sub
    (L.refill s sc (L.rhead s sc)).amount c⟩ with hr1
  have h1 : RingAt st s0 (L.putS s sc (L.rhead s sc) r1) sc n := h.putS hhl r1
  have e1 : L.refills (L.putS s sc (L.rhead s sc) r1) sc = r1 :: (L.refills s sc).tail := by
    rw [refills_of (hW.size_putS hhl) (fun k hk => hW.rf_set_head (by have := hW.size_le; omega)),
      refills_set_head hW]
  have et : L.rtail (L.putS s sc (L.rhead s sc) r1) sc = L.rtail s sc := rtail_putS h8 (by omega)
  rw [← et]
  refine ⟨h1.putS h1.wf.tail_lt _, ?_⟩
  rw [refills_set_tail h1.wf, refills_tail_eq h1.wf, e1]
  unfold rrChargeL
  rw [← head_eq' hW]

/-- What charging `c` to `x` leaves at the head of `y`, if `x`'s head was
sufficient for `c`; and that charging `0` leaves the refills. -/
def HF (x y : Fl4Spec.SchedContext) (c : Fl4Spec.Ticks) : Prop :=
  (0 < c → Fl4Spec.refillSufficient c (Fl4Spec.refillHd x) = true →
    Fl4Spec.MIN_BUDGET ≤ (Fl4Spec.refillHd y).rAmount ∧
      ((Fl4Spec.refillHd y).rTime = (Fl4Spec.refillHd x).rTime ∨
        (Fl4Spec.refillHd y).rTime = (Fl4Spec.refillHd x).rTime + c)) ∧
  (¬ 0 < c → y.scRefills = x.scRefills)

theorem HF_refl (x : Fl4Spec.SchedContext) (c : Fl4Spec.Ticks) : HF x x c := by
  refine ⟨fun _ hsuf => ⟨?_, Or.inl rfl⟩, fun _ => rfl⟩
  obtain ⟨h1, h2⟩ := suff_nat hsuf
  rw [BitVec.le_def]; omega

/-- `HF` from `σ` to `σ'` for the SC at `p`, charging the consumed time. -/
def HFP (σ σ' : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) : Prop :=
  ∀ y m, σ'.kheap p = some (.schedContext y m) → ∃ x0, σ.kheap p = some (.schedContext x0 m) ∧ HF x0 y σ.consumedTime

/-- **`commit_time`'s refill update.** -/
theorem commit_refill_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hscC : nodeW st s c layout.node.CUR_SC ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n)) (hact : Fl4Spec.scActive x = true)
    {u0 : Fl4Spec.ObjRef} (hown : x.scTcb = some u0 ∨ x.scTcb = none)
    (hnr : 0 < (nodeW st s c layout.node.CONSUMED).bv → u0 ∉ σ.releaseQueue)
    (hsuf0 : 0 < (nodeW st s c layout.node.CONSUMED).bv → x.scPeriod = 0 →
      Fl4Spec.refillSufficient (nodeW st s c layout.node.CONSUMED).bv (Fl4Spec.refillHd x) = true)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    (if nodeW st s c layout.node.CONSUMED > 0#u64 then do
        let b2 ← sporadic.is_round_robin st s (nodeW st s c layout.node.CUR_SC)
        if b2 then do
          let hi ← obj.Sc.refill_head st (nodeW st s c layout.node.CUR_SC) s
          let ti ← obj.Sc.refill_tail st (nodeW st s c layout.node.CUR_SC) s
          let h ← sporadic.get st s (nodeW st s c layout.node.CUR_SC) hi
          let i ← lift (core.num.U64.wrapping_sub h.amount (nodeW st s c layout.node.CONSUMED))
          let s4 ← sporadic.put st s (nodeW st s c layout.node.CUR_SC) hi { h with amount := i }
          let t ← sporadic.get st s4 (nodeW st s c layout.node.CUR_SC) ti
          let i1 ← lift (core.num.U64.wrapping_add t.amount (nodeW st s c layout.node.CONSUMED))
          sporadic.put st s4 (nodeW st s c layout.node.CUR_SC) ti { t with amount := i1 }
        else sporadic.budget_check st ar s a (nodeW st s c layout.node.CONSUMED)
      else ok s) ⦃ s3 => ∃ y', Fl4Spec.NonDet.when (0 < (nodeW st s c layout.node.CONSUMED).bv) (do
          let robin ← Fl4Spec.isRoundRobin (Z := Unit) (nodeW st s c layout.node.CUR_SC).bv
          if robin
          then Fl4Spec.refillBudgetCheckRoundRobin (nodeW st s c layout.node.CONSUMED).bv
          else Fl4Spec.refillBudgetCheck (nodeW st s c layout.node.CONSUMED).bv) σ =
            ({((), updSc σ (nodeW st s c layout.node.CUR_SC).bv y' n)}, False) ∧
        y' = { x with scRefills := y'.scRefills } ∧
        SchedRel st N T C c s3 (updSc σ (nodeW st s c layout.node.CUR_SC).bv y' n) ∧
        NtfnStateRel N T (L.mem s3) (updSc σ (nodeW st s c layout.node.CUR_SC).bv y' n) ∧
        NSC N C (updSc σ (nodeW st s c layout.node.CUR_SC).bv y' n) ∧
        InvBut (updSc σ (nodeW st s c layout.node.CUR_SC).bv y' n) u0 ∧
        HF x y' (nodeW st s c layout.node.CONSUMED).bv ∧ WritesIn st s s3 (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  set sc := nodeW st s c layout.node.CUR_SC with hscd
  set cn := nodeW st s c layout.node.CONSUMED with hcnd
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hscC
  rw [hk] at hk'; cases hk'
  replace hx := hx.strong hact
  have hrr : decide (L.rperiod s sc = 0#u64) = decide (x.scPeriod = 0) := by
    apply decide_eq_decide.2
    rw [hx.period]
    exact ⟨fun h => by rw [h]; rfl, fun h => eq_of_bv (by rw [h]; rfl)⟩
  by_cases hc0 : cn > 0#u64
  · rw [if_pos hc0]
    have hlt : 0 < cn.bv := (u64_lt_bv _ _).1 hc0
    have hsp : ∀ σ3 : Fl4Spec.State Unit,
        (if decide (x.scPeriod = 0) = true then Fl4Spec.refillBudgetCheckRoundRobin (Z := Unit) cn.bv
          else Fl4Spec.refillBudgetCheck cn.bv) σ = ({((), σ3)}, False) →
        Fl4Spec.NonDet.when (0 < cn.bv) (do
          let robin ← Fl4Spec.isRoundRobin (Z := Unit) sc.bv
          if robin
          then Fl4Spec.refillBudgetCheckRoundRobin cn.bv
          else Fl4Spec.refillBudgetCheck cn.bv) σ = ({((), σ3)}, False) := by
      intro σ3 h3
      unfold Fl4Spec.NonDet.when; rw [if_pos hlt, nd_bind_one (isRoundRobin_eq hk)]; exact h3
    step with sporadic.is_round_robin.spec as ⟨rr, hrr'⟩
    subst hrr'
    by_cases h0 : L.rperiod s sc = 0#u64
    · have e0 : decide (L.rperiod s sc = 0#u64) = true := decide_eq_true h0
      have hper : x.scPeriod = 0 := by have := hrr ▸ e0; simpa using this
      simp only [e0, ↓reduceIte]
      refine WP.spec_mono (rr_charge_refines (RingAt.refl hx.wf) cn) ?_
      rintro s3 ⟨hring, hl⟩
      obtain ⟨hS3, hf, hkv⟩ := hS.ringAt hscC hk hring
      rw [hl] at hS3 hkv
      have hne := refills_ne' hx.wf
      have hR3 := hR.frame hS.placed hf hkv
      refine ⟨_, hsp _ ?_, rfl, hS3, hR3, hN.kview hR hkv,
        hI.refillUpd hk rfl (by simp [rrChargeL]) (fun _ hp => absurd hper hp) (fun _ _ => by
          obtain ⟨h1, h2⟩ := suff_nat (hsuf0 hlt hper)
          rw [refillHd_map hx.refills hne] at h1 h2
          exact rrChargeL_rr hx.refills (hI.rr _ x n hk hact hper) cn h1 h2) hown (hnr hlt),
        ⟨fun _ hsuf => ?_, fun h => absurd hlt h⟩, RingAt.kfoot hS hscC hring⟩
      · rw [if_pos (by simpa using hper)]
        exact refillBudgetCheckRoundRobin_eq hs.curSc hk hx.refills hne cn
      · have hH : Fl4Spec.refillHd x = toRefill ((L.refills s sc).headD zR) := refillHd_map hx.refills hne
        obtain ⟨hlt', hmin⟩ := suff_nat hsuf
        rw [hH] at hlt' hmin
        have hav : (toRefill ((L.refills s sc).headD zR)).rAmount.toNat = ((L.refills s sc).headD zR).amount.val := rfl
        have hcv : cn.bv.toNat = cn.val := rfl
        rw [hav, hcv] at hlt' hmin
        have hne2 : rrChargeL (L.refills s sc) cn ≠ [] := by simp [rrChargeL]
        obtain ⟨ht, ha⟩ := rrChargeL_head hne cn
        rw [refillHd_map (x := { x with scRefills := (rrChargeL (L.refills s sc) cn).map toRefill }) rfl hne2, hH]
        refine ⟨?_, Or.inl (by simp only [toRefill]; rw [ht])⟩
        rw [BitVec.le_def]
        show _ ≤ ((rrChargeL (L.refills s sc) cn).headD zR).amount.val
        have hb : ((L.refills s sc).headD zR).amount.val < 2 ^ 64 := by scalar_tac
        rcases ha with ha | ha <;> rw [ha]
        · rw [wsub_val (by omega)]; omega
        · rw [wadd_val (by rw [wsub_val (by omega)]; omega), wsub_val (by omega)]; omega
    · have e0 : decide (L.rperiod s sc = 0#u64) = false := decide_eq_false h0
      have hper : ¬ x.scPeriod = 0 := by
        intro e; have := hrr ▸ e0; simp [e] at this
      simp only [e0, Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_mono (budget_check_refines_inv s a σ hS hI hscC
        (fun y m h => by rw [hk] at h; cases h; exact hact) hmrt hmb h0 cn
        (fun y m h => by rw [hk] at h; cases h; exact hown) (hnr hlt)) ?_
      rintro s3 ⟨σ3, h1, hf, hkv, hS3, hI3, hpost, hwb⟩
      obtain ⟨y', rfl, hy', -⟩ := hpost x n hk
      have hm2 : 2 ≤ x.scRefillMax := by rw [← hx.max]; have := hx.wf.min_le; simpa using this
      refine ⟨y', hsp _ (by rw [if_neg (by simpa using hper)]; exact h1), hy', hS3, hR.frame hS.placed hf hkv,
        hN.kview hR hkv, hI3, ⟨fun _ hsuf => ?_, fun h => absurd hlt h⟩, hwb⟩
      exact refillBudgetCheck_head hs.curSc hk hx.refills (refills_ne' hx.wf) hx.period hper hm2 cn hsuf h1 y' n
        (by simp [updK])
  · rw [if_neg hc0, WP.spec_ok]
    have hlt : ¬ 0 < cn.bv := fun h => hc0 ((u64_lt_bv _ _).2 h)
    have e : updSc σ sc.bv x n = σ := updSc_self hk
    refine ⟨x, ?_, rfl, ?_, ?_, ?_, ?_, ⟨fun h => absurd h hlt, fun _ => rfl⟩, WritesIn.refl _ _⟩ <;> rw [e]
    · unfold Fl4Spec.NonDet.when; rw [if_neg hlt]; rfl
    · exact hS
    · exact hR
    · exact hN
    · exact hI.toBut _

/-- **`commit_time` refines l4v `commit_time`**; it keeps `Inv` except
`rd` for the current thread. Hypotheses: the current SC is one of `C` and
bound to the current thread, which is not in the release queue; `idle_sc`
is `idle_sc_ptr`; the platform constants. -/
theorem commit_time_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hscC : nodeW st s c layout.node.CUR_SC ∈ C)
    {u0 : Fl4Spec.ObjRef} (hown0 : ∀ x n, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) →
      x.scTcb = some u0 ∨ x.scTcb = none)
    (hidle : (nodeW st s c layout.node.IDLE_SC).bv = σ.idleSc)
    (hnr : 0 < σ.consumedTime → u0 ∉ σ.releaseQueue) (hoff : OffOK σ)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    sched.commit_time st ar s a ⦃ s' => ∃ σ', Fl4Spec.commitTime (Z := Unit) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧
      InvBut σ' u0 ∧ HeadKeeps σ σ' (nodeW st s c layout.node.CUR_SC).bv ∧
      HFP σ σ' (nodeW st s c layout.node.CUR_SC).bv ∧ WritesIn st s s' (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hown : x.scTcb = some u0 ∨ x.scTcb = none := hown0 x n hk
  have hsp0 : ∀ σ1, commitHead σ = ({((), σ1)}, False) → Fl4Spec.commitTime (Z := Unit) σ =
      ({((), { σ1 with consumedTime := 0 })}, False) := fun σ1 h1 => by
    rw [commitTime_eq, nd_bind_one h1]; rfl
  -- the consumed-time reset
  have fin : ∀ (s1 : S) (σ1 : Fl4Spec.State Unit), commitHead σ = ({((), σ1)}, False) →
      SchedRel st N T C c s1 σ1 → NtfnStateRel N T (L.mem s1) σ1 → NSC N C σ1 →
      InvBut σ1 u0 → HeadKeeps σ σ1 (nodeW st s c layout.node.CUR_SC).bv →
      HFP σ σ1 (nodeW st s c layout.node.CUR_SC).bv → WritesIn st s s1 (KFoot st T N C c s σ) →
      sched.set_consumed st s1 0#u64 ⦃ s' => ∃ σ', Fl4Spec.commitTime (Z := Unit) σ = ({((), σ')}, False) ∧
        SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧
        InvBut σ' u0 ∧
        HeadKeeps σ σ' (nodeW st s c layout.node.CUR_SC).bv ∧ HFP σ σ' (nodeW st s c layout.node.CUR_SC).bv ∧
        WritesIn st s s' (KFoot st T N C c s σ) ⦄ := by
    intro s1 σ1 h1 hS1 hR1 hN1 hI1 hK1 hH1 hw1
    refine WP.spec_mono (sched.set_consumed.spec' s1 0#u64) ?_
    rintro s' rfl
    have hNd := hS1.lists.choose_spec.choose_spec.1.node
    rw [hS1.lists.choose_spec.choose_spec.1.cur]
    obtain ⟨hS2, hf2, -⟩ := hS1.set_node_consumed 0#u64
    have ho : (layout.node.CONSUMED).val < 4288 := by simp [layout.node.CONSUMED]
    exact ⟨{ σ1 with consumedTime := 0 }, hsp0 σ1 h1, hS2, hR1.frame hS1.placed hf2 (KView.of_kheap rfl), hN1,
      hI1.congr rfl rfl rfl rfl, hK1, hH1, WritesIn.kfoot_sfoot hw1
        ((writesIn_wr (nodeAt_aligned hNd ho (by simp [layout.node.CONSUMED]))).mono fun b hb => hb ▸ sfoot_node hNd ho)⟩
  have hsph : commitHead σ = Fl4Spec.NonDet.when (Fl4Spec.scActive x = true ∧ (nodeW st s c layout.node.CUR_SC).bv ≠
      σ.idleSc) (do
        let consumed ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.consumedTime
        Fl4Spec.NonDet.when (0 < consumed) (do
          let robin ← Fl4Spec.isRoundRobin (Z := Unit) (nodeW st s c layout.node.CUR_SC).bv
          if robin
          then Fl4Spec.refillBudgetCheckRoundRobin consumed
          else Fl4Spec.refillBudgetCheck consumed)
        Fl4Spec.updateSchedContext (nodeW st s c layout.node.CUR_SC).bv
          fun sc => { sc with scConsumed := sc.scConsumed + consumed }) σ := by
    unfold commitHead
    rw [nd_gets_bind, hs.curSc, nd_bind_one (getScActive_eq hk), nd_gets_bind]
  have hnone : ¬ (Fl4Spec.scActive x = true ∧ (nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc) →
      sched.set_consumed st s 0#u64 ⦃ s' => ∃ σ', Fl4Spec.commitTime (Z := Unit) σ = ({((), σ')}, False) ∧
        SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧
        InvBut σ' u0 ∧
        HeadKeeps σ σ' (nodeW st s c layout.node.CUR_SC).bv ∧ HFP σ σ' (nodeW st s c layout.node.CUR_SC).bv ∧
        WritesIn st s s' (KFoot st T N C c s σ) ⦄ := fun hn =>
    fin s σ (by rw [hsph]; unfold Fl4Spec.NonDet.when; rw [if_neg hn]; rfl) hS hR hN (hI.toBut _) (HeadKeeps.refl σ _)
      (fun y m hy => ⟨y, hy, HF_refl y _⟩) (WritesIn.refl _ _)
  unfold sched.commit_time
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  rw [hc.cur] at hsc'
  subst hsc'
  step with sc_active_spec as ⟨b, hb⟩
  have hab : b = Fl4Spec.scActive x := by
    rw [hb]
    show _ = decide (0 < x.scRefillMax)
    apply decide_eq_decide.2
    rw [← hx.max]; rfl
  subst hab
  by_cases hact : Fl4Spec.scActive x = true
  · simp only [hact, ↓reduceIte]
    step with sched.idle_sc.spec' as ⟨id', hid'⟩
    rw [hc.cur] at hid'
    subst hid'
    rw [sc_ne_eq]
    simp only [bind_ok]
    by_cases hid : nodeW st s c layout.node.CUR_SC = nodeW st s c layout.node.IDLE_SC
    · simp only [hid, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [← hid]
      simp only [bind_ok]
      exact hnone (fun h => h.2 (by rw [hid, hidle]))
    · have hid2 : (nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc := by
        rw [← hidle]; exact bv_ne hid
      simp only [hid, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
      step with sched.consumed.spec' as ⟨cn, hcn⟩
      rw [hc.cur] at hcn
      subst hcn
      refine WP.spec_bind (commit_refill_refines s a σ hS hR hN hI hscC hk hact hown (fun h => hnr (by rw [hs.consumed]; exact h))
        (fun h0 _ => by
          rw [← hs.consumed] at h0 ⊢
          exact (hoff h0 x n (by rw [hs.curSc]; exact hk) (fun _ => hact)).1) hmrt hmb) ?_
      rintro s3 ⟨y', h3, hy', hS3, hR3, hN3, hI3, hHF, hw3⟩
      have hk3 : (updSc σ (nodeW st s c layout.node.CUR_SC).bv y' n).kheap (nodeW st s c layout.node.CUR_SC).bv =
          some (.schedContext y' n) := by simp [updK]
      obtain ⟨Q3, R3, hc3, hs3⟩ := hS3.lists
      obtain ⟨x3, n3, hk3', hx3⟩ := hs3.scs _ hscC
      rw [hk3] at hk3'; cases hk3'
      step with obj.Sc.consumed.spec' as ⟨i, hi⟩
      try simp only [lift, bind_ok]
      step with obj.Sc.set_consumed.spec' as ⟨s2, hs2⟩
      subst hs2
      have e : ({ y' with scConsumed := (core.num.U64.wrapping_add i (nodeW st s c layout.node.CONSUMED)).bv } :
          Fl4Spec.SchedContext) = { y' with scConsumed := y'.scConsumed + (nodeW st s c layout.node.CONSUMED).bv } := by
        rw [core.num.U64.wrapping_add_bv_eq, hi, hx3.consumed]
      obtain ⟨hS2, hf, hkv⟩ := hS3.set_sc_consumed hscC hk3 (core.num.U64.wrapping_add i (nodeW st s c layout.node.CONSUMED))
      rw [e] at hS2 hkv
      have hsw8 := sw_hdr hS hscC (K := 8#u64) (by simp) (by simp) (by decide)
      have hal8 := (hx3.hdr (K := 8#u64) (by simp) (by simp)).1
      refine fin _ _ ?_ hS2 (hR3.frame hS3.placed hf hkv) (hN3.kview hR3 hkv) (hI3.scUpd hk3 rfl rfl rfl rfl) ?_ ?_
        (WritesIn.kfoot_sw hw3 ((writesIn_wr hal8).mono fun b hb => hb ▸ hsw8))
      · rw [hsph, Fl4Spec.NonDet.when, if_pos ⟨hact, hid2⟩, nd_gets_bind, hs.consumed, nd_bind_one h3]
        exact updateSchedContext_eq hk3 _
      · rw [updSc_updSc]; exact HeadKeeps.updSc hk (by rw [hy']) (by rw [hy'])
      · intro y m hy
        rw [updSc_updSc] at hy
        simp only [updK_kheap, Function.update_self, Option.some.injEq, Fl4Spec.KernelObject.schedContext.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        exact ⟨x, hk, by rw [hs.consumed]; exact hHF⟩
  · simp only [Bool.not_eq_true] at hact
    simp only [hact, Bool.false_eq_true, ↓reduceIte, bind_ok]
    exact hnone (fun h => by rw [hact] at h; exact Bool.false_ne_true h.1)

end

end

end Fl4Proofs.P3.Sched
