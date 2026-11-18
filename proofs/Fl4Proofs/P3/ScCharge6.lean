/-
P3 (DESIGN.md §9), scheduling contexts: **`charge_budget` refines l4v
`charge_budget`** (`charge_budget_refines`) and keeps `Inv`: the refill
update (`refill_reset_rr` or `refill_budget_check`) leaves `InvBut` for the
current thread, and `end_timeslice` (appending or postponing it) restores
`Inv`; a current thread that is not schedulable is not blocked on a
notification (l4v `cur_sc_not_blocked`), so `rd` holds for it vacuously.

* `rr_reset_refines`: FL4's round-robin reset on the ring is `rrResetL`;
* `consumed_refines`: the SC's `consumed` update;
* `charge_head_refines`: everything before the consumed-time reset;
* `charge_tail_refines`: the reset, `end_timeslice`, `reschedule_required`
  and the reprogram flag;
* `charge_budget_refines`: the whole function.
-/
import Fl4Proofs.P3.ScCur
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- `charge_budget` up to the consumed-time reset. -/
def chargeHead (consumed : Ticks) : SMonad Unit Unit := do
  let cscPtr ← Fl4Spec.NonDet.gets fun s : State Unit => s.curSc
  let isc ← Fl4Spec.NonDet.gets fun s : State Unit => s.idleSc
  Fl4Spec.NonDet.when (cscPtr ≠ isc) <| do
    let robin ← isRoundRobin cscPtr
    if robin
    then refillResetRr cscPtr
    else refillBudgetCheck consumed
    updateSchedContext cscPtr (fun sc => { sc with scConsumed := sc.scConsumed + consumed })

/-- The rest of `charge_budget`. -/
def chargeTail (canTimeout : Bool) : SMonad Unit Unit := do
  Fl4Spec.NonDet.modify fun s : State Unit => { s with consumedTime := 0 }
  let ct ← Fl4Spec.NonDet.gets fun s : State Unit => s.curThread
  let sched ← Fl4Spec.NonDet.gets (schedulable ct)
  Fl4Spec.NonDet.when sched <| do
    endTimeslice canTimeout
    rescheduleRequired
    Fl4Spec.NonDet.modify fun s : State Unit => { s with reprogramTimer := true }

theorem chargeBudget_eq (consumed : Ticks) (can : Bool) (σ : State Unit) :
    chargeBudget (Z := Unit) consumed can σ = (chargeHead consumed >>= fun _ => chargeTail can) σ := by
  unfold chargeHead chargeBudget
  simp only [nd_bind_assoc', nd_gets_bind]
  all_goals rfl

theorem chargeTail_eq (can : Bool) (σ : State Unit) {t : ObjRef} (ht : σ.curThread = t) :
    chargeTail can σ = (if schedulable t { σ with consumedTime := 0 } = true then
      (do
        endTimeslice can
        rescheduleRequired
        Fl4Spec.NonDet.modify fun s : State Unit => { s with reprogramTimer := true }) { σ with consumedTime := 0 }
      else ({((), { σ with consumedTime := 0 })}, False)) := by
  subst ht
  unfold chargeTail
  rw [nd_bind_one (rfl : Fl4Spec.NonDet.modify (fun s : State Unit => { s with consumedTime := 0 }) σ =
    ({((), { σ with consumedTime := 0 })}, False)), nd_gets_bind, nd_gets_bind]
  unfold Fl4Spec.NonDet.when
  split_ifs <;> rfl

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **FL4's round-robin reset** is `rrResetL` on the list. -/
theorem rr_reset_refines {s0 s : S} {sc : U64} {n : Nat} (h : RingAt st s0 s sc n) :
    (do
      let hi ← obj.Sc.refill_head st sc s
      let ti ← obj.Sc.refill_tail st sc s
      let h ← sporadic.get st s sc hi
      let t ← sporadic.get st s sc ti
      let i ← lift (core.num.U64.wrapping_add h.amount t.amount)
      let s4 ← sporadic.put st s sc hi { h with amount := i }
      sporadic.put st s4 sc ti { t with amount := 0#u64 }) ⦃ s' => RingAt st s0 s' sc n ∧
        L.refills s' sc = rrResetL (L.refills s sc) ⦄ := by
  step with obj.Sc.refill_head.spec as ⟨hi, hhi⟩
  step with obj.Sc.refill_tail.spec as ⟨ti, hti⟩
  step with sporadic.get.spec as ⟨hr, hhr⟩
  step with sporadic.get.spec as ⟨tr, htr⟩
  simp only [lift, bind_ok]
  step with sporadic.put.spec as ⟨s4, hs4⟩
  refine WP.spec_mono (sporadic.put.spec s4 sc ti _) ?_
  rintro s5 rfl
  subst hhi hti hhr htr hs4
  have hW := h.wf
  obtain ⟨h8, hb, hfit⟩ := hW.bounds
  have hhl := hW.head_lt
  set r1 : sporadic.Refill := ⟨(L.refill s sc (L.rhead s sc)).time, core.num.U64.wrapping_add
    (L.refill s sc (L.rhead s sc)).amount (L.refill s sc (L.rtail s sc)).amount⟩ with hr1
  set r2 : sporadic.Refill := ⟨(L.refill s sc (L.rtail s sc)).time, 0#u64⟩ with hr2
  have h1 : RingAt st s0 (L.putS s sc (L.rhead s sc) r1) sc n := h.putS hhl r1
  have e1 : L.refills (L.putS s sc (L.rhead s sc) r1) sc = r1 :: (L.refills s sc).tail := by
    rw [refills_of (hW.size_putS hhl) (fun k hk => hW.rf_set_head (by have := hW.size_le; omega)),
      refills_set_head hW]
  have et : L.rtail (L.putS s sc (L.rhead s sc) r1) sc = L.rtail s sc := rtail_putS h8 (by omega)
  have ep : L.putS (L.putS s sc (L.rhead s sc) r1) sc (L.rtail s sc) r2 =
      L.putS (L.putS s sc (L.rhead s sc) r1) sc (L.rtail (L.putS s sc (L.rhead s sc) r1) sc) r2 := by rw [et]
  rw [ep]
  refine ⟨h1.putS h1.wf.tail_lt r2, ?_⟩
  rw [refills_set_tail h1.wf, e1]
  unfold rrResetL
  rw [← head_eq' hW, ← refills_tail_eq hW]

section Spec
open Fl4Spec
/-- `rrResetL` on a list of at least two refills. -/
theorem rrResetL_split (a l : sporadic.Refill) (i : List sporadic.Refill) :
    rrResetL (a :: (i ++ [l])) =
      ⟨a.time, core.num.U64.wrapping_add a.amount l.amount⟩ :: (i ++ [⟨l.time, 0#u64⟩]) := by
  have e : (a :: (i ++ [l])).getLastD zR = l := by
    rw [← List.cons_append, List.getLastD_eq_getLast?, List.getLast?_concat]; rfl
  unfold rrResetL
  rw [e, List.headD_cons, List.tail_cons, ← List.cons_append, List.dropLast_concat]; rfl

/-- `rrChargeL` on a list of at least two refills. -/
theorem rrChargeL_split (a l : sporadic.Refill) (i : List sporadic.Refill) (c : U64) :
    rrChargeL (a :: (i ++ [l])) c =
      ⟨a.time, core.num.U64.wrapping_sub a.amount c⟩ :: (i ++ [⟨l.time, core.num.U64.wrapping_add l.amount c⟩]) := by
  unfold rrChargeL
  simp only [List.headD_cons, List.tail_cons]
  have e : ∀ b : sporadic.Refill, (b :: (i ++ [l])).getLastD zR = l := fun b => by
    rw [← List.cons_append, List.getLastD_eq_getLast?, List.getLast?_concat]; rfl
  rw [e, ← List.cons_append, List.dropLast_concat]; rfl

/-- A list of at least two refills is a head, a middle and a last. -/
theorem rr_split {x : SchedContext} {rs : List sporadic.Refill} (hx : x.scRefills = rs.map toRefill)
    (h : 2 ≤ x.scRefills.length) : ∃ a i l, rs = a :: (i ++ [l]) := by
  rw [hx, List.length_map] at h
  match rs, h with
  | a :: t, h =>
    rcases List.eq_nil_or_concat t with e | ⟨i, l, e⟩
    · subst e; simp at h
    · exact ⟨a, i, l, by rw [e, List.concat_eq_append]⟩

/-- The round-robin reset keeps `RRok`: the head gains the tail. -/
theorem rrResetL_rr {x : SchedContext} {rs : List sporadic.Refill} (hx : x.scRefills = rs.map toRefill)
    (h : RRok x) : RRok { x with scRefills := (rrResetL rs).map toRefill } := by
  obtain ⟨a, i, l, rfl⟩ := rr_split hx h.1
  obtain ⟨h1, h2, h3⟩ := h
  unfold refillHd at h3
  rw [hx] at h1 h2 h3
  simp [toRefill, List.sum_append, the] at h2 h3
  have hav : a.amount.val + l.amount.val < 2 ^ 64 := by omega
  have hw := wadd_val (x := a.amount) (y := l.amount) hav
  refine ⟨?_, ?_, ?_⟩
  · simp [rrResetL_split]
  · simp [rrResetL_split, toRefill, List.sum_append]; omega
  · unfold refillHd
    simp [rrResetL_split, toRefill, the]
    rw [BitVec.le_def] at h3 ⊢
    show _ ≤ (core.num.U64.wrapping_add a.amount l.amount).val
    rw [hw]; exact Nat.le_trans h3 (Nat.le_add_right _ _)

/-- The round-robin charge keeps `RRok` when the head pays the charge and
keeps `MIN_BUDGET`. -/
theorem rrChargeL_rr {x : SchedContext} {rs : List sporadic.Refill} (hx : x.scRefills = rs.map toRefill)
    (h : RRok x) (c : U64) (hc : c.val < (rs.headD zR).amount.val)
    (hm : MIN_BUDGET.toNat ≤ (rs.headD zR).amount.val - c.val) :
    RRok { x with scRefills := (rrChargeL rs c).map toRefill } := by
  obtain ⟨a, i, l, rfl⟩ := rr_split hx h.1
  obtain ⟨h1, h2, h3⟩ := h
  rw [hx] at h1 h2
  simp [toRefill, List.sum_append] at h2 hc hm
  have hsub := wsub_val (x := a.amount) (y := c) (by omega)
  have hav : l.amount.val + c.val < 2 ^ 64 := by omega
  have hw := wadd_val (x := l.amount) (y := c) hav
  refine ⟨?_, ?_, ?_⟩
  · simp [rrChargeL_split]
  · simp [rrChargeL_split, toRefill, List.sum_append]; omega
  · unfold refillHd
    simp [rrChargeL_split, toRefill, the]
    rw [BitVec.le_def]
    show _ ≤ (core.num.U64.wrapping_sub a.amount c).val
    rw [hsub]; exact hm
end Spec

/-- **The SC's `consumed` update** refines `update_sched_context`. -/
theorem consumed_refines {N T C : Set U64} {c : U64} (s3 : S) (σ3 : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s3 σ3) (hR : NtfnStateRel N T (L.mem s3) σ3) (hN : NSC N C σ3)
    {t : Fl4Spec.ObjRef} (hI : InvBut σ3 t) {sc : U64} (hsc : sc ∈ C) {x3 : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ3.kheap sc.bv = some (.schedContext x3 n)) (used : U64) :
    (do
      let i ← obj.Sc.consumed st sc s3
      let total ← lift (core.num.U64.wrapping_add i used)
      obj.Sc.set_consumed st sc s3 total) ⦃ s2 => ∃ σ2,
        Fl4Spec.updateSchedContext (Z := Unit) sc.bv (fun y => { y with scConsumed := y.scConsumed + used.bv }) σ3 =
          ({((), σ2)}, False) ∧
        σ2 = updSc σ3 sc.bv { x3 with scConsumed := x3.scConsumed + used.bv } n ∧
        SchedRel st N T C c s2 σ2 ∧ NtfnStateRel N T (L.mem s2) σ2 ∧ NSC N C σ2 ∧ InvBut σ2 t ∧
        WritesIn st s3 s2 (· = scW sc 8#u64) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  step with obj.Sc.consumed.spec' as ⟨i, hi⟩
  simp only [lift, bind_ok]
  refine WP.spec_mono (obj.Sc.set_consumed.spec' s3 sc _) ?_
  rintro s2 rfl
  have e : ({ x3 with scConsumed := (core.num.U64.wrapping_add i used).bv } : Fl4Spec.SchedContext) =
      { x3 with scConsumed := x3.scConsumed + used.bv } := by
    rw [core.num.U64.wrapping_add_bv_eq, hi, hx.consumed]
  obtain ⟨hS2, hf, hkv⟩ := hS.set_sc_consumed hsc hk (core.num.U64.wrapping_add i used)
  rw [e] at hS2 hkv
  exact ⟨_, updateSchedContext_eq hk _, rfl, hS2, hR.frame hS.placed hf hkv, hN.kview hR hkv,
    hI.scUpd hk rfl rfl rfl rfl, writesIn_wr (hx.hdr (K := 8#u64) (by simp) (by simp)).1⟩

/-- **`charge_budget` before the consumed-time reset.** -/
theorem charge_head_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
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
      TmoKeep st (nodeW st s c layout.node.CUR_THREAD) s σ s2 σ2 ⦄ := by
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
        TmoKeep st ct s σ s3 (updSc σ sc.bv y' n) →
        (do
          let i ← obj.Sc.consumed st sc s3
          let total ← lift (core.num.U64.wrapping_add i used)
          obj.Sc.set_consumed st sc s3 total) ⦃ s2 => ∃ σ2, chargeHead used.bv σ = ({((), σ2)}, False) ∧
          SchedRel st N T C c s2 σ2 ∧ NtfnStateRel N T (L.mem s2) σ2 ∧ NSC N C σ2 ∧
          InvBut σ2 ct.bv ∧ HeadKeeps σ σ2 sc.bv ∧ TmoKeep st ct s σ s2 σ2 ⦄ := by
      intro s3 y' hy' h3 hS3 hR3 hN3 hI3 hT3
      have hk3 : (updSc σ sc.bv y' n).kheap sc.bv = some (.schedContext y' n) := by simp [updK]
      refine WP.spec_mono (consumed_refines s3 _ hS3 hR3 hN3 hI3 hscC hk3 used) ?_
      rintro s2 ⟨σ2, h1, rfl, h2, h3', h4, h5, hw5⟩
      refine ⟨_, by rw [hspec2 _ h3]; exact h1, h2, h3', h4, h5, ?_, ?_⟩
      · rw [updSc_updSc]
        exact HeadKeeps.updSc hk (by rw [hy']) (by rw [hy'])
      · refine hT3.trans (TmoKeep.of_kheap hw5 (fun b e => ?_) (hupd _ _ _))
        subst e
        obtain ⟨Q3, R3, -, hs3⟩ := hS3.lists
        obtain ⟨x3, n3, hk3', hx3⟩ := hs3.scs sc hscC
        rw [hk3] at hk3'; cases hk3'
        have := (hS3.scOut sc hscC _ _ hk3 _ (hx3.in_obj (hx3.hdr (K := 8#u64) (by simp) (by simp)).2)).2.2.1 ct hct
        omega
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
          (hupd _ _ _))
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
        (hN.kview hR hkv) hI3 (TmoKeep.of_kheap hw3 (fun b hb => kfoot_tslot hS hct hb) (hupd _ _ _))
  · have hb' : b = false := by rw [hb]; simpa using hid
    simp only [hb', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ, ?_, hS, hR, hN, hI.toBut _, HeadKeeps.refl σ _, TmoKeep.refl _ _ _⟩
    rw [hspec]; unfold Fl4Spec.NonDet.when; rw [if_neg hid]; rfl

/-- **`charge_budget` after the head**: the consumed-time reset, and for a
schedulable current thread `end_timeslice`, `reschedule_required` and the
reprogram flag. -/
theorem charge_tail_refines {N T C : Set U64} {c : U64} (s2 : S) (a : A) (σ2 : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s2 σ2) (hR : NtfnStateRel N T (L.mem s2) σ2) (hN : NSC N C σ2)
    {sc ct : U64} (hI : InvBut σ2 ct.bv) (hcs : σ2.curSc = sc.bv) (hcc : σ2.curThread = ct.bv)
    (hscC : sc ∈ C) (hsc0 : sc ≠ 0#u64) {xt : Fl4Spec.Tcb} (hkt : σ2.kheap ct.bv = some (.tcb xt))
    (hxs : xt.tcbSchedContext = some sc.bv) (hnb : NotIpcBlk xt.tcbState)
    {y2 : Fl4Spec.SchedContext} {n2 : Nat} (hky : σ2.kheap sc.bv = some (.schedContext y2 n2))
    (hyt : y2.scTcb = some ct.bv)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hval : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' →
      TmoKeep st ct s2 σ2 s' σ' →
      faults.valid_timeout_handler st s' ct ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) ct.bv σ' = ({(b, σ')}, False) ⦄)
    (hto : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' → NtfnStateRel N T (L.mem s') σ' →
      NSC N C σ' → InvBut σ' ct.bv →
      faults.handle_timeout st ar s' a ct (error.Fault.Timeout (L.mem s' (scW sc 48#u64))) ⦃ r => ∃ σ'',
        Fl4Spec.handleTimeout (Z := Unit) ct.bv (.timeout (L.mem s' (scW sc 48#u64)).bv) σ' =
          ({((), σ'')}, False) ∧
        SchedRel st N T C c r.1 σ'' ∧ Inv σ'' ∧ NtfnStateRel N T (L.mem r.1) σ'' ∧ NSC N C σ'' ∧
        σ''.consumedTime = σ'.consumedTime ∧ (IdleOK σ' → IdleOK σ'') ⦄)
    (can : Bool) :
    (do
      let s3 ← sched.set_consumed st s2 0#u64
      let ct ← sched.cur_thread st s3
      let b1 ← sched.is_schedulable st s3 ct
      if b1
      then
        let (s4, a1) ← sched.end_timeslice st ar s3 a can
        let s5 ← sched.reschedule_required st s4
        let s6 ← sched.set_reprogram st s5
        ok (s6, a1)
      else ok (s3, a)) ⦃ r => ∃ σ', chargeTail can σ2 = ({((), σ')}, False) ∧
        SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧
        (σ'.schedulerAction = .chooseNewThread ∨ σ' = { σ2 with consumedTime := 0 }) ∧ σ'.consumedTime = 0 ∧
        (IdleOK σ2 → IdleOK σ') ⦄ := by
  have hc2 := hS.lists.choose_spec.choose_spec.1.cur
  step with sched.set_consumed.spec' as ⟨s3, hs3⟩
  rw [hc2] at hs3
  subst hs3
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
  have hspec := chargeTail_eq can σ2 hcc
  rw [← hσ3] at hspec
  by_cases hsch : Fl4Spec.schedulable ct.bv σ3 = true
  · simp only [hsch, ↓reduceIte]
    rw [if_pos hsch] at hspec
    have hE := end_timeslice_refines (ar := ar) s3 a σ3 hS3 hR3 hN3 (by rw [e1]; exact hI3) (by rw [e2]; exact hscC)
      (by rw [e2]; exact hsc0) (by rw [e1, e2]; exact word24_of hS3 hscC hky hyt)
      (by rw [e1, e2]; exact scA_of hS3 hct hkt hxs) (by rw [e1]; exact hsch) hmb
      (by rw [e1]; exact hval s3 σ3 hS3 (TmoKeep.node_wr hS hct (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) 0#u64 rfl)) (by rw [e1, e2]; exact hto s3 σ3 hS3 hR3 hN3 hI3) can
    refine WP.spec_bind hE ?_
    rintro ⟨s4, a1⟩ ⟨σ4, h4, hS4, hI4, hR4, hN4, hc4, hid4⟩
    refine WP.spec_bind (reschedule_required_refines s4 σ4 hR4 hS4 hI4.actReady) ?_
    rintro s5 ⟨σ5, h5, hk5, hr5, hf5, hS5⟩
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
    obtain ⟨hS6, hf6, -⟩ := hS5.set_reprogram
    refine ⟨{ σ5 with reprogramTimer := true }, ?_, hS6, hI5.congr rfl rfl rfl rfl,
      hR5.frame hS5.placed hf6 (KView.of_kheap rfl), hN5, Or.inl (rescheduleRequired_action (σ' := σ5) hI4.actReady h5' :),
      (rescheduleRequired_consumed (σ' := σ5) hI4.actReady h5').trans hc4, fun hid => ?_⟩
    · rw [hspec, nd_bind_one h4, nd_bind_one h5']
      rfl
    · have hid5 : IdleOK σ5 := (hid4 (IdleOK.of hid rfl rfl id)).of hcm5.2.2.2.2.2.1
        (by rw [hcm5.1]) (fun hm => by rw [hq5.2.1] at hm; exact hm) hcm5.isc
      exact hid5.of rfl rfl id
  · simp only [Bool.not_eq_true] at hsch
    simp only [hsch, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ3, ?_, hS3, ?_, hR3, hN3, Or.inr rfl, rfl, fun hid => IdleOK.of hid rfl rfl id⟩
    · rw [hspec, if_neg (by rw [hsch]; exact Bool.false_ne_true)]
    · refine hI3.inv fun x hx hcl => ?_
      intro x' scp y n h1 h2 h3 h4 h5
      have hkt3 : σ3.kheap ct.bv = some (.tcb xt) := hkt
      rw [hkt3] at hx h1; cases hx; cases h1
      have := schedulable_of hkt3 h2 (inClass_runnable hcl hnb) h3 h4 h5
      rw [hsch] at this; cases this

/-- **`charge_budget` refines l4v `charge_budget`** and keeps the invariant.

Hypotheses beyond the relations: the current SC is one of `C`, is not
null, and is bound to the current thread both ways (l4v
`cur_sc_tcb_are_bound`); if it is not the idle SC it is active (l4v
`cur_sc_active`); the current thread is not in the release queue and not
blocked on a notification (l4v `cur_sc_not_blocked`, `ct_not_in_release_q`);
`idle_sc` is the spec's `idle_sc_ptr`; the platform constants; and the
timeout-fault test and send (`hval`, `hto`, a CSpace read and IPC). -/
theorem charge_budget_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
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
    (hto : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' → NtfnStateRel N T (L.mem s') σ' →
      NSC N C σ' → InvBut σ' (nodeW st s c layout.node.CUR_THREAD).bv →
      faults.handle_timeout st ar s' a (nodeW st s c layout.node.CUR_THREAD)
        (error.Fault.Timeout (L.mem s' (scW (nodeW st s c layout.node.CUR_SC) 48#u64))) ⦃ r => ∃ σ'',
        Fl4Spec.handleTimeout (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv
          (.timeout (L.mem s' (scW (nodeW st s c layout.node.CUR_SC) 48#u64)).bv) σ' = ({((), σ'')}, False) ∧
        SchedRel st N T C c r.1 σ'' ∧ Inv σ'' ∧ NtfnStateRel N T (L.mem r.1) σ'' ∧ NSC N C σ'' ∧
        σ''.consumedTime = σ'.consumedTime ∧ (IdleOK σ' → IdleOK σ'') ⦄)
    (used : U64) (can : Bool) :
    sched.charge_budget st ar s a used can ⦃ r => ∃ σ',
      Fl4Spec.chargeBudget (Z := Unit) used.bv can σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧
      (σ'.schedulerAction = .chooseNewThread ∨ HeadKeeps σ σ' (nodeW st s c layout.node.CUR_SC).bv) ∧
      σ'.consumedTime = 0 ∧ (ActIdle σ → ActIdle σ') ⦄ := by
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
  refine WP.spec_bind (charge_head_refines s a σ hS hR hN hI hscC htw hact hnr hmrt hmb used _ hb) ?_
  rintro s2 ⟨σ2, h2, hS2, hR2, hN2, hI2, hK, hTK⟩
  have ⟨hcs, hcc, _, _, _, _, _, _, hfr, hsck⟩ := hK
  obtain ⟨y2, hky, hyt, -⟩ := hsck x n hk
  have hkt2 : σ2.kheap (nodeW st s c layout.node.CUR_THREAD).bv = some (.tcb xt) := by
    rw [hfr _ (fun e => by rw [e, hk] at hkt; cases hkt)]; exact hkt
  refine WP.spec_mono (charge_tail_refines s2 a σ2 hS2 hR2 hN2 hI2 (by rw [hcs, hs.curSc])
    (by rw [hcc, hs.curThread]) hscC hsc0 hkt2 hxs (hnb xt hkt) hky (by rw [hyt]; exact hown) hmb (fun s' σ' h1 h2 => hval s' σ' h1 (hTK.trans h2)) hto can) ?_
  rintro r ⟨σ', h1, h3, h4, h5, h6, h7, h8, h9⟩
  refine ⟨σ', by rw [chargeBudget_eq, nd_bind_one h2]; exact h1, h3, h4, h5, h6, ?_, h8, fun hA => ?_⟩
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
