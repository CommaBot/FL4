/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, rd1; KENTRY-PLAN off1's R1-R3):
**the readiness slices of l4v `valid_sched` as a carried spec invariant:
definitions, boot, and the charge of a sufficient consumed time** (spec side
only, outside the `JAtZ` cone).

* `RdyT σ t` (l4v `released_sc_tcb_at`): `t` is a TCB bound to an active SC
  whose head refill is ready (`r_time ≤ cur_time`) and sufficient
  (`MIN_BUDGET ≤ r_amount`).
* `R1` (l4v `valid_ready_qs`, its readiness half): every ready-queued thread is
  `RdyT`.
* `R2` (l4v `valid_sched_action` / `weak_valid_sched_action`, readiness
  half): the switch target is `RdyT`.
* `R3` (l4v `released_ipc_queues`): a thread blocked on a notification, on a
  receive, or on a send without a timeout fault, if bound to an SC, is `RdyT`
  (`possible_switch_to` of a woken thread tests no readiness).
* `RV` (l4v `valid_refills` / `valid_sched_context`, the part these need): an
  active SC has `MIN_REFILLS ≤ refill_max` (so a one-refill list is never
  full and `schedule_used` never moves the head) and its refill amounts sum
  below `2 ^ 64` (so `refill_unblock_check`'s merges never wrap the head's
  amount).
* `Rdy := R1 ∧ R2 ∧ R3 ∧ RV`; `boot_rdy`.
* `Suff σ` (l4v `cur_sc_offset_sufficient`, an intra-entry fact): the consumed
  time is sufficient for the current SC's head, when that SC is active and
  not the idle SC. Established by `check_budget` / `preemption_point`, not
  carried across exits.
* **`rbc_head_mem`**: ScHead's `refillBudgetCheck_head` (sufficient charge:
  the head keeps `MIN_BUDGET` and moves by `0` or the usage) for an arbitrary
  outcome (that lemma takes the outcome equation, only available through the
  FL4 relation); `rbc_head` the same for any spec SC (the refill list as an
  FL4 list by `ofR`).
* **`commit_cur`**: `commit_time` with `OffReady ∧ Suff ∧ RV ∧ RNE` leaves the
  current SC with a ready, sufficient head (raw, consumed time 0), its
  binding / refill max kept, every other object, the queues, the action and
  the times kept, the consumed time 0.
-/
import Fl4Proofs.P3.ScHead
import Fl4Proofs.P3.SpecInvOffT
import Fl4Proofs.P3.SpecInvSbK
open Classical
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The sufficient charge, for any outcome -/

/-- **ScHead's `refillBudgetCheck_head` for an arbitrary outcome** (same proof,
on membership). -/
theorem rbc_head_mem {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.SchedContext} {n : Nat}
    (hcur : σ.curSc = p) (hk : σ.kheap p = some (.schedContext x n)) {rs : List sporadic.Refill}
    (hx : x.scRefills = rs.map toRefill) (hne : rs ≠ []) {per : U64} (hper : x.scPeriod = per.bv)
    (hp0 : x.scPeriod ≠ 0) (hm2 : 2 ≤ x.scRefillMax) (u : U64)
    (hsuf : Fl4Spec.refillSufficient u.bv (Fl4Spec.refillHd x) = true)
    {r : Unit × Fl4Spec.State Unit} (hm : r ∈ (Fl4Spec.refillBudgetCheck (Z := Unit) u.bv σ).1) :
    (r.2 = σ ∨ ∃ z, r.2 = updSc σ p z n ∧ z.scRefillMax = x.scRefillMax ∧ z.scTcb = x.scTcb ∧
        z.scPeriod = x.scPeriod ∧ z.scSporadic = x.scSporadic ∧ z.scRefills ≠ []) ∧
      ∀ y m, r.2.kheap p = some (.schedContext y m) → Fl4Spec.MIN_BUDGET ≤ (Fl4Spec.refillHd y).rAmount ∧
      ((Fl4Spec.refillHd y).rTime = (Fl4Spec.refillHd x).rTime ∨
        (Fl4Spec.refillHd y).rTime = (Fl4Spec.refillHd x).rTime + u.bv) := by
  obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hH : Fl4Spec.refillHd x = toRefill hd := refillHd_map hx hne
  have hne' : x.scRefills ≠ [] := by rw [hx]; simp
  obtain ⟨hlt, hmin⟩ := suff_nat hsuf
  rw [hH] at hlt hmin
  simp only [toRefill] at hlt hmin
  have hav : hd.amount.bv.toNat = hd.amount.val := rfl
  have huv : u.bv.toNat = u.val := rfl
  rw [hav, huv] at hlt hmin
  rw [refillBudgetCheck_eq hcur hk hp0] at hm
  have hov : ¬ Fl4Spec.the (Fl4Spec.headRefillOverrun (Z := Unit) p u.bv σ) = true := by
    simp only [headRefillOverrun_eq hk hne', hH, Fl4Spec.the, toRefill, decide_eq_true_eq, not_and, BitVec.le_def]
    intro h1; rw [hav, huv] at h1; omega
  unfold Fl4Spec.handleOverrun at hm
  rw [nd_bind_one (wl_done (C := fun usage s => Fl4Spec.the (Fl4Spec.headRefillOverrun p usage s) = true)
    (B := fun usage => Fl4Spec.chargeEntireHeadRefill p usage) hov)] at hm
  unfold Fl4Proofs.P3.Sched.specTail at hm
  rw [nd_bind_one (getRefillHead_eq hk hne'), hH, Fl4Spec.NonDet.when] at hm
  have hmin' : ¬ (toRefill hd).rAmount < Fl4Spec.MIN_BUDGET := by
    simp only [toRefill]; rw [BitVec.lt_def, hav]; omega
  split_ifs at hm with hc
  · rw [nd_bind_one (postBody_eq hk (hd := hd) (tl := tl) hx hper (toRefill hd) rfl u)] at hm
    set l := schedUsedL x.scRefillMax (⟨core.num.U64.wrapping_add hd.time u, core.num.U64.wrapping_sub hd.amount u⟩ :: tl)
      ⟨core.num.U64.wrapping_add hd.time per, u⟩ with hl
    have hk1 : (updSc σ p { x with scRefills := l.map toRefill } n).kheap p =
        some (.schedContext { x with scRefills := l.map toRefill } n) := by simp [updK]
    have hlne : l ≠ [] := by rw [hl]; exact schedUsedL_ne
    obtain ⟨ht, ha⟩ := schedUsedL_head hm2 ⟨core.num.U64.wrapping_add hd.time u, core.num.U64.wrapping_sub hd.amount u⟩
      tl ⟨core.num.U64.wrapping_add hd.time per, u⟩
    rw [← hl] at ht ha
    have hlam : Fl4Spec.MIN_BUDGET.toNat ≤ (l.headD zR).amount.val := by
      rcases ha with ha | ha <;> rw [ha]
      · rw [wsub_val (by omega)]; omega
      · have hb : hd.amount.val < 2 ^ 64 := by scalar_tac
        dsimp only
        rw [wadd_val (by rw [wsub_val (by omega)]; omega), wsub_val (by omega)]; omega
    have hinsuf : ¬ Fl4Spec.the (Fl4Spec.refillHeadInsufficient (Z := Unit) p
        (updSc σ p { x with scRefills := l.map toRefill } n)) = true := by
      simp only [refillHeadInsufficient_eq hk1 (by simpa using hlne),
        refillHd_map (x := { x with scRefills := l.map toRefill }) rfl hlne, Fl4Spec.the, toRefill,
        decide_eq_true_eq, BitVec.lt_def]
      have e : (l.headD zR).amount.bv.toNat = (l.headD zR).amount.val := rfl
      rw [e]; omega
    unfold Fl4Spec.headInsufficientLoop at hm
    rw [wl_done (C := fun _ s => Fl4Spec.the (Fl4Spec.refillHeadInsufficient p s) = true)
      (B := fun _ => Fl4Spec.mergeNonoverlappingHeadRefill p) hinsuf] at hm
    obtain rfl : r = ((), _) := hm
    refine ⟨Or.inr ⟨_, rfl, rfl, rfl, rfl, rfl, by simpa using hlne⟩, ?_⟩
    intro y m hy
    rw [hk1] at hy; cases hy
    rw [refillHd_map (x := { x with scRefills := l.map toRefill }) rfl hlne]
    refine ⟨by rw [BitVec.le_def]; exact hlam, Or.inr ?_⟩
    rw [hH]; simp only [toRefill]; rw [ht, core.num.U64.wrapping_add_bv_eq]
  · rw [nd_bind_one (show Fl4Spec.NonDet.pure (σ := Fl4Spec.State Unit) () σ = ({((), σ)}, False) from rfl)] at hm
    have hinsuf : ¬ Fl4Spec.the (Fl4Spec.refillHeadInsufficient (Z := Unit) p σ) = true := by
      simp only [refillHeadInsufficient_eq hk hne', hH, Fl4Spec.the, decide_eq_true_eq]; exact hmin'
    unfold Fl4Spec.headInsufficientLoop at hm
    rw [wl_done (C := fun _ s => Fl4Spec.the (Fl4Spec.refillHeadInsufficient p s) = true)
      (B := fun _ => Fl4Spec.mergeNonoverlappingHeadRefill p) hinsuf] at hm
    obtain rfl : r = ((), σ) := hm
    refine ⟨Or.inl rfl, ?_⟩
    intro y m hy
    rw [hk] at hy; cases hy
    refine ⟨?_, Or.inl rfl⟩
    rw [hH]; simp only [toRefill]; rw [BitVec.le_def, hav]; omega

/-- A spec refill as an FL4 refill. -/
def ofR (r : Fl4Spec.Refill) : sporadic.Refill := { time := ⟨r.rTime⟩, amount := ⟨r.rAmount⟩ }

theorem map_ofR (l : List Fl4Spec.Refill) : (l.map ofR).map toRefill = l := by
  rw [List.map_map]; conv_rhs => rw [← List.map_id l]
  rfl

/-- **The sufficient charge of any spec SC** (`rbc_head_mem`). -/
theorem rbc_head {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.SchedContext} {n : Nat}
    (hcur : σ.curSc = p) (hk : σ.kheap p = some (.schedContext x n)) (hne : x.scRefills ≠ [])
    (hp0 : x.scPeriod ≠ 0) (hm2 : 2 ≤ x.scRefillMax) (u : Fl4Spec.Ticks)
    (hsuf : Fl4Spec.refillSufficient u (Fl4Spec.refillHd x) = true)
    {r : Unit × Fl4Spec.State Unit} (hm : r ∈ (Fl4Spec.refillBudgetCheck (Z := Unit) u σ).1) :
    (r.2 = σ ∨ ∃ z, r.2 = updSc σ p z n ∧ z.scRefillMax = x.scRefillMax ∧ z.scTcb = x.scTcb ∧
        z.scPeriod = x.scPeriod ∧ z.scSporadic = x.scSporadic ∧ z.scRefills ≠ []) ∧
      ∀ y m, r.2.kheap p = some (.schedContext y m) → Fl4Spec.MIN_BUDGET ≤ (Fl4Spec.refillHd y).rAmount ∧
      ((Fl4Spec.refillHd y).rTime = (Fl4Spec.refillHd x).rTime ∨
        (Fl4Spec.refillHd y).rTime = (Fl4Spec.refillHd x).rTime + u) :=
  rbc_head_mem (rs := x.scRefills.map ofR) (per := ⟨x.scPeriod⟩) hcur hk (map_ofR _).symm
    (by simpa using hne) rfl hp0 hm2 ⟨u⟩ hsuf hm

/-! ## The carried slices -/

section Rdy
open Fl4Spec

/-- **l4v `released_sc_tcb_at`**: a TCB bound to an active SC with a ready,
sufficient head refill. -/
def RdyT (σ : State Unit) (t : ObjRef) : Prop :=
  ∃ x c y n, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some c ∧ σ.kheap c = some (.schedContext y n) ∧
    scActive y = true ∧ refillReady σ.curTime (refillHd y) = true ∧ refillSufficient 0 (refillHd y) = true

/-- **R1 [J]** (l4v `valid_ready_qs`, readiness half). -/
def R1 (σ : State Unit) : Prop := ∀ d p t, t ∈ σ.readyQueues d p → RdyT σ t

/-- **R2 [J]** (l4v `valid_sched_action`, readiness half of the switch target). -/
def R2 (σ : State Unit) : Prop := ∀ t, σ.schedulerAction = .switchThread t → RdyT σ t

/-- The blocked states `released_ipc_queues` covers (a sender with a timeout
fault is exempt, as in l4v and `Notif.inClassR`). -/
def BlkR (ts : ThreadState) (f : Option Fault) : Prop :=
  (∃ n, ts = .blockedOnNotification n) ∨ (∃ e d, ts = .blockedOnSend e d ∧ ∀ b, f ≠ some (.timeout b)) ∨
    (∃ e r d, ts = .blockedOnReceive e r d)

/-- **R3 [J]** (l4v `released_ipc_queues`): a blocked thread's SC, if bound, is released. -/
def R3 (σ : State Unit) : Prop :=
  ∀ t x c, σ.kheap t = some (.tcb x) → BlkR x.tcbState x.tcbFault → x.tcbSchedContext = some c → RdyT σ t

/-- **RV [J]** (l4v `valid_refills`, the refill-max part): an active SC has room
for two refills. -/
def RV (σ : State Unit) : Prop :=
  ∀ p y n, σ.kheap p = some (.schedContext y n) → scActive y = true → MIN_REFILLS ≤ y.scRefillMax

/-- **The carried readiness bundle.** -/
def Rdy (σ : State Unit) : Prop := R1 σ ∧ R2 σ ∧ R3 σ ∧ RV σ

/-- **The intra-entry sufficiency** (l4v `cur_sc_offset_sufficient`). -/
def Suff (σ : State Unit) : Prop :=
  ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → scActive y = true → σ.curSc ≠ σ.idleSc →
    refillSufficient σ.consumedTime (refillHd y) = true

/-! ## Boot (non-vacuity) -/

theorem init_tcbSt {u : ObjRef} {x : Tcb} (h : initKheap u = some (.tcb x)) : x.tcbState = .idleThreadState := by
  by_cases e : u = idleThreadPtr
  · subst e
    unfold initKheap at h
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self] at h
    cases h; rfl
  · exfalso
    unfold initKheap at h
    simp only [Function.update_apply, e, if_false] at h
    split_ifs at h <;> cases h

theorem boot_rdy : Rdy (initASt (Z := Unit)) := by
  refine ⟨fun d p t h => by simp [initASt] at h, fun t h => by simp [initASt] at h, fun t x c hx hb _ => ?_,
    fun p y n hy _ => ?_⟩
  · exfalso
    have e := init_tcbSt (u := t) hx
    rcases hb with ⟨_, h⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h⟩ <;> rw [e] at h <;> cases h
  · have hy' : initKheap p = some (.schedContext y n) := hy
    by_cases e : p = idleScPtr
    · subst e
      rw [SInvV.initKheap_idleSc] at hy'
      cases hy'
      exact le_refl _
    · exfalso
      unfold initKheap at hy'
      simp only [Function.update_apply, e, if_false] at hy'
      split_ifs at hy' <;> cases hy'

/-! ## Refill arithmetic -/

theorem suff0_of {h : Refill} (hm : MIN_BUDGET ≤ h.rAmount) : refillSufficient 0 h = true := by
  unfold refillSufficient refillCapacity
  simp [hm]

theorem min_le_of_suff {u : Ticks} {h : Refill} (hs : refillSufficient u h = true) : MIN_BUDGET ≤ h.rAmount := by
  obtain ⟨h1, h2⟩ := Sched.suff_nat hs
  rw [BitVec.le_def]; omega

theorem ready_of_nat {t : Time} {h : Refill} (hm : h.rTime.toNat ≤ t.toNat) : refillReady t h = true := by
  show decide (h.rTime + 0 ≤ t) = true
  apply decide_eq_true
  rw [BitVec.le_def]; simpa using hm

theorem nat_of_ready {t : Time} {h : Refill} (hm : refillReady t h = true) : h.rTime.toNat ≤ t.toNat := by
  have := of_decide_eq_true (show decide (h.rTime + 0 ≤ t) = true from hm)
  rw [BitVec.le_def] at this; simpa using this

/-- The round-robin charge's head (`refill_budget_check_round_robin` on the list). -/
theorem rr_head (L : List Refill) (hne : L ≠ []) (c : Ticks) :
    (the ((({ (the L.head?) with rAmount := (the L.head?).rAmount - c } : Refill) :: L.tail).dropLast ++
        [{ (the (({ (the L.head?) with rAmount := (the L.head?).rAmount - c } : Refill) :: L.tail).getLast?) with
          rAmount := (the (({ (the L.head?) with rAmount := (the L.head?).rAmount - c } : Refill) ::
            L.tail).getLast?).rAmount + c }]).head?).rTime = (the L.head?).rTime ∧
    ((the ((({ (the L.head?) with rAmount := (the L.head?).rAmount - c } : Refill) :: L.tail).dropLast ++
        [{ (the (({ (the L.head?) with rAmount := (the L.head?).rAmount - c } : Refill) :: L.tail).getLast?) with
          rAmount := (the (({ (the L.head?) with rAmount := (the L.head?).rAmount - c } : Refill) ::
            L.tail).getLast?).rAmount + c }]).head?).rAmount = (the L.head?).rAmount - c ∨
     (the ((({ (the L.head?) with rAmount := (the L.head?).rAmount - c } : Refill) :: L.tail).dropLast ++
        [{ (the (({ (the L.head?) with rAmount := (the L.head?).rAmount - c } : Refill) :: L.tail).getLast?) with
          rAmount := (the (({ (the L.head?) with rAmount := (the L.head?).rAmount - c } : Refill) ::
            L.tail).getLast?).rAmount + c }]).head?).rAmount = (the L.head?).rAmount) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  cases t with
  | nil =>
    simp only [List.head?_cons, Sched.the_some, List.tail_cons, List.dropLast_singleton, List.getLast?_singleton,
      List.nil_append]; simp
  | cons b t =>
    simp only [List.head?_cons, Sched.the_some, List.tail_cons, List.dropLast_cons_of_ne_nil (List.cons_ne_nil b t),
      List.cons_append]; simp

/-! ## `commit_time` with a sufficient consumed time -/

theorem kh_upd (σ : State Unit) (p : ObjRef) (y : SchedContext) (n : Nat) :
    (Sched.updSc σ p y n).kheap p = some (.schedContext y n) := by simp [Notif.updK]

/-- What `commit_time` leaves at the current SC (module docstring). -/
def CommitOut (σ : State Unit) (x : SchedContext) (n : Nat) (σ' : State Unit) : Prop :=
  ∃ y, σ' = { Sched.updSc σ σ.curSc y n with consumedTime := 0 } ∧ y.scTcb = x.scTcb ∧
    y.scRefillMax = x.scRefillMax ∧ y.scSporadic = x.scSporadic ∧ y.scPeriod = x.scPeriod ∧
    (x.scRefills ≠ [] → y.scRefills ≠ []) ∧ (refillHd y).rTime.toNat ≤ σ.curTime.toNat ∧
    (scActive x = true → σ.curSc ≠ σ.idleSc → refillSufficient 0 (refillHd y) = true) ∧
    (¬ (scActive x = true ∧ σ.curSc ≠ σ.idleSc) → y.scRefills = x.scRefills)

/-- **`commit_time` with a sufficient consumed time** (module docstring). -/
theorem commit_cur {σ : State Unit} {x : SchedContext} {n : Nat}
    (hk : σ.kheap σ.curSc = some (.schedContext x n)) (hO : Sched.OffReady σ) (hS : Suff σ) (hV : RV σ)
    (hne : scActive x = true → x.scRefills ≠ []) {r : Unit × State Unit}
    (hr : r ∈ (commitTime (Z := Unit) σ).1) : CommitOut σ x n r.2 := by
  have hoff := hO x n hk
  unfold commitTime at hr
  rw [nd_gets_bind, nd_bind_one (getScActive_eq hk), nd_gets_bind] at hr
  by_cases hc : scActive x = true ∧ σ.curSc ≠ σ.idleSc
  · rw [NonDet.when, if_pos hc, nd_bind_assoc', nd_gets_bind, nd_bind_assoc'] at hr
    obtain ⟨hact, hni⟩ := hc
    have hne' := hne hact
    have hsuf := hS x n hk hact hni
    have hm2 : 2 ≤ x.scRefillMax := hV _ x n hk hact
    by_cases h0 : 0 < σ.consumedTime
    · rw [NonDet.when, if_pos h0, nd_bind_assoc', nd_bind_one (isRoundRobin_eq hk)] at hr
      by_cases hrr : x.scPeriod = 0
      · rw [if_pos (by simpa using hrr)] at hr
        unfold refillBudgetCheckRoundRobin at hr
        rw [nd_bind_assoc', nd_gets_bind, nd_bind_assoc', nd_bind_one (updateRefillHd_eq hk _),
          nd_bind_one (updateRefillTl_eq (kh_upd _ _ _ _) _), updSc_updSc,
          nd_bind_one (updateSchedContext_eq (kh_upd _ _ _ _) _), updSc_updSc] at hr
        obtain rfl : r = ((), _) := hr
        obtain ⟨ht, ha⟩ := rr_head x.scRefills hne' σ.consumedTime
        refine ⟨_, rfl, rfl, rfl, rfl, rfl, fun _ => by simp, ?_, fun _ _ => ?_, fun h => absurd ⟨hact, hni⟩ h⟩
        · show (the (_ : List Refill).head?).rTime.toNat ≤ _
          rw [ht]; exact Nat.le_trans (Nat.le_add_right _ _) hoff
        · apply suff0_of
          show MIN_BUDGET ≤ (the (_ : List Refill).head?).rAmount
          obtain ⟨h1, h2⟩ := Sched.suff_nat hsuf
          have h3 : MIN_BUDGET.toNat ≤ (refillHd x).rAmount.toNat := BitVec.le_def.mp (min_le_of_suff hsuf)
          rcases ha with ha | ha <;> rw [ha]
          · rw [BitVec.le_def, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact Nat.le_of_lt h1)]; exact h2
          · rw [BitVec.le_def]; exact h3
      · rw [if_neg (by simpa using hrr)] at hr
        obtain ⟨y1, hy1, hr⟩ := hr
        dsimp only at hr
        obtain ⟨hfr, hhd⟩ := rbc_head rfl hk hne' hrr hm2 σ.consumedTime hsuf hy1
        obtain ⟨h1, h2⟩ := Sched.suff_nat hsuf
        have hnat : ∀ z m, y1.2.kheap σ.curSc = some (.schedContext z m) →
            (refillHd z).rTime.toNat ≤ σ.curTime.toNat ∧ refillSufficient 0 (refillHd z) = true := by
          intro z m hz
          obtain ⟨hmn, hrt⟩ := hhd z m hz
          refine ⟨?_, suff0_of hmn⟩
          have hlt := σ.curTime.isLt
          rcases hrt with e | e <;> rw [e]
          · exact Nat.le_trans (Nat.le_add_right _ _) hoff
          · rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; exact hoff
        rcases hfr with e | ⟨z, e, ez1, ez2, ez3, ez4, ez5⟩
        · rw [e, nd_bind_one (updateSchedContext_eq hk _)] at hr
          obtain rfl : r = ((), _) := hr
          obtain ⟨hz1, hz2⟩ := hnat x n (by rw [e]; exact hk)
          exact ⟨_, rfl, rfl, rfl, rfl, rfl, fun h => h, hz1, fun _ _ => hz2, fun h => absurd ⟨hact, hni⟩ h⟩
        · rw [e, nd_bind_one (updateSchedContext_eq (kh_upd _ _ _ _) _), updSc_updSc] at hr
          obtain rfl : r = ((), _) := hr
          obtain ⟨hz1, hz2⟩ := hnat z n (by rw [e]; exact kh_upd _ _ _ _)
          exact ⟨_, rfl, ez2, ez1, ez4, ez3, fun _ => ez5, hz1, fun _ _ => hz2, fun h => absurd ⟨hact, hni⟩ h⟩
    · rw [NonDet.when, if_neg h0, nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl),
        nd_bind_one (updateSchedContext_eq hk _)] at hr
      obtain rfl : r = ((), _) := hr
      have hc0 : σ.consumedTime = 0 := by
        by_contra hz; exact h0 (BitVec.lt_def.mpr (by
          have : σ.consumedTime.toNat ≠ 0 := fun e => hz (BitVec.eq_of_toNat_eq (by simpa using e))
          simp; omega))
      refine ⟨_, rfl, rfl, rfl, rfl, rfl, fun h => h, Nat.le_trans (Nat.le_add_right _ _) hoff, fun _ _ => ?_,
        fun h => absurd ⟨hact, hni⟩ h⟩
      have := hsuf; rw [hc0] at this; exact this
  · rw [NonDet.when, if_neg hc, nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl)]
      at hr
    obtain rfl : r = ((), _) := hr
    refine ⟨x, ?_, rfl, rfl, rfl, rfl, fun h => h, Nat.le_trans (Nat.le_add_right _ _) hoff,
      fun h1 h2 => absurd ⟨h1, h2⟩ hc, fun _ => rfl⟩
    show _ = { Sched.updSc σ σ.curSc x n with consumedTime := 0 }
    rw [updSc_self hk]

/-! ## One SC rewritten: the frame of `Rdy` -/

theorem rdyT_frame {σ σ' : State Unit} {p : ObjRef} (hk : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q)
    (ht : σ'.curTime = σ.curTime)
    (hp : ∀ y n, σ.kheap p = some (.schedContext y n) → scActive y = true →
      refillReady σ.curTime (refillHd y) = true → refillSufficient 0 (refillHd y) = true →
      ∃ z, σ'.kheap p = some (.schedContext z n) ∧ scActive z = true ∧
        refillReady σ.curTime (refillHd z) = true ∧ refillSufficient 0 (refillHd z) = true)
    (hpt : ∀ x, σ.kheap p ≠ some (.tcb x)) {t : ObjRef} (h : RdyT σ t) : RdyT σ' t := by
  obtain ⟨x, c, y, n, hx, hc, hy, ha, hr, hs⟩ := h
  have htp : t ≠ p := by rintro rfl; exact hpt x hx
  by_cases e : c = p
  · subst e
    obtain ⟨z, hz, h1, h2, h3⟩ := hp y n hy ha hr hs
    exact ⟨x, c, z, n, by rw [hk t htp]; exact hx, hc, hz, h1, by rw [ht]; exact h2, h3⟩
  · exact ⟨x, c, y, n, by rw [hk t htp]; exact hx, hc, by rw [hk c e]; exact hy, ha, by rw [ht]; exact hr, hs⟩

/-- **`Rdy` across a rewrite of one SC** keeping an active, released SC
active and released, and the refill-max clause. -/
theorem rdy_frame1 {σ σ' : State Unit} {p : ObjRef} (h : Rdy σ) (hk : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q)
    (ht : σ'.curTime = σ.curTime) (hq : σ'.readyQueues = σ.readyQueues)
    (ha : σ'.schedulerAction = σ.schedulerAction)
    (hp : ∀ y n, σ.kheap p = some (.schedContext y n) → scActive y = true →
      refillReady σ.curTime (refillHd y) = true → refillSufficient 0 (refillHd y) = true →
      ∃ z, σ'.kheap p = some (.schedContext z n) ∧ scActive z = true ∧
        refillReady σ.curTime (refillHd z) = true ∧ refillSufficient 0 (refillHd z) = true)
    (hpt : ∀ x, σ.kheap p ≠ some (.tcb x)) (hpt' : ∀ x, σ'.kheap p ≠ some (.tcb x))
    (hpv : ∀ z n, σ'.kheap p = some (.schedContext z n) → scActive z = true → MIN_REFILLS ≤ z.scRefillMax) :
    Rdy σ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have F := fun {t} (h : RdyT σ t) => rdyT_frame hk ht hp hpt h
  refine ⟨fun d q t hm => F (h1 d q t (hq ▸ hm)), fun t e => F (h2 t (ha ▸ e)), fun t x c hx hb hc => ?_,
    fun q z n hz hz' => ?_⟩
  · have htp : t ≠ p := by rintro rfl; exact hpt' x hx
    rw [hk t htp] at hx
    exact F (h3 t x c hx hb hc)
  · by_cases e : q = p
    · subst e; exact hpv z n hz hz'
    · rw [hk q e] at hz; exact h4 q z n hz hz'

/-- **`commit_time` keeps `Rdy` and gives `OffReady`** (with the consumed time
sufficient: the intra-entry `Suff`). -/
theorem rdy_commitTime {σ : State Unit} {x : SchedContext} {n : Nat} (h : Rdy σ)
    (hk : σ.kheap σ.curSc = some (.schedContext x n)) (hO : Sched.OffReady σ) (hS : Suff σ)
    (hne : scActive x = true → x.scRefills ≠ []) {r : Unit × State Unit}
    (hr : r ∈ (commitTime (Z := Unit) σ).1) : Rdy r.2 ∧ Sched.OffReady r.2 ∧ CommitOut σ x n r.2 := by
  obtain ⟨y, e, e1, e2, e3, e4, e5, e6, e7, e8⟩ := commit_cur hk hO hS h.2.2.2 hne hr
  rw [e]
  have hkc : ∀ q, q ≠ σ.curSc → ({ Sched.updSc σ σ.curSc y n with consumedTime := 0 } : State Unit).kheap q =
      σ.kheap q := fun q hq => by simp [Notif.updK, hq]
  have hkp : ({ Sched.updSc σ σ.curSc y n with consumedTime := 0 } : State Unit).kheap σ.curSc =
      some (.schedContext y n) := kh_upd _ _ _ _
  have hay : scActive y = scActive x := by simp only [scActive, e2]
  refine ⟨rdy_frame1 h hkc rfl rfl rfl (fun y0 n0 hy0 ha0 hr0 hs0 => ?_) (fun x0 hx0 => by rw [hk] at hx0; cases hx0)
    (fun x0 hx0 => by rw [hkp] at hx0; cases hx0) (fun z n0 hz hz' => ?_), fun z m hz => ?_,
    ⟨y, rfl, e1, e2, e3, e4, e5, e6, e7, e8⟩⟩
  · rw [hk] at hy0; cases hy0
    refine ⟨y, hkp, by rw [hay]; exact ha0, ?_⟩
    by_cases hc : scActive x = true ∧ σ.curSc ≠ σ.idleSc
    · exact ⟨ready_of_nat e6, e7 hc.1 hc.2⟩
    · have er := e8 hc
      have eh : refillHd y = refillHd x := by unfold refillHd; rw [er]
      rw [eh]; exact ⟨hr0, hs0⟩
  · rw [hkp] at hz; cases hz
    rw [hay] at hz'
    rw [e2]; exact h.2.2.2 _ x n hk hz'
  · cases (hkp.symm.trans hz)
    show (refillHd y).rTime.toNat + (0 : Ticks).toNat ≤ σ.curTime.toNat
    simpa using e6

end Rdy

end

end Fl4Proofs.P3.SInvR
