/-
P3 (DESIGN.md §9), notifications: **`receive_signal` and `complete_signal`
refine l4v `receive_signal` / `complete_signal`** (`Z = Unit`), except the
blocking case (NtfnBlock.lean):

* `receive_signal_poll`: polling (`blocking = false`) a notification that is
  not active writes 0 to the badge register (l4v `do_nbrecv_failed_transfer`);
  single spec outcome, no hypotheses on other subsystems;
* `receive_signal_active`: on an active notification, the badge goes to the
  badge register and the notification becomes idle, then the scheduler tail
  (donate the notification's SC, sporadic unblock check) against the spec's,
  a hypothesis (`RecvHyps.recvTail`);
* `complete_signal_active`: the same for `complete_signal`, with its own
  tail (`RecvHyps.completeTail`). (`complete_signal` on a notification that
  is not active: FL4 returns, the spec fails, so there is nothing to
  refine.)

The receive's cap is a notification cap to `n` (`Cap.notificationCap n.bv _ _`).
-/
import Fl4Proofs.P3.NtfnWake
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Notif
open fl4_core Fl4Proofs.P1

noncomputable section

/-! ## The tails and their hypotheses -/

section Defs
variable {S A : Type} (st : machine.Store S) (ar : machine.Arch A)

/-- FL4's tail of a receive on an active notification (after the
notification is made idle). -/
def rustRecvTail (s : S) (a : A) (t : obj.Tcb) (n : U64) : Result (S × A) := do
  let (s3, a1) ← notification.maybe_donate_sched_context st ar s a t n
  let i ← obj.Tcb.sc st t s3
  let s4 ← sched.cur_sc st s3
  let b1 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i s4
  if b1
  then
    let b2 ← sporadic.sc_sporadic st s3 i
    if b2
    then
      let s5 ← sporadic.unblock_check st s3 i
      ok (s5, a1)
    else ok (s3, a1)
  else ok (s3, a1)

/-- FL4's tail of `complete_signal`. -/
def rustCompleteTail (s : S) (a : A) (t : obj.Tcb) (n : U64) : Result (S × A) := do
  let (s3, a1) ← notification.maybe_donate_sched_context st ar s a t n
  let i1 ← obj.Tcb.sc st t s3
  let b2 ← sporadic.sc_sporadic st s3 i1
  if b2
  then
    let i2 ← obj.Ntfn.sc st n s3
    if i1 = i2
    then
      let s4 ← sched.cur_sc st s3
      let b3 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i1 s4
      if b3
      then
        let s5 ← sporadic.unblock_check st s3 i1
        ok (s5, a1)
      else ok (s3, a1)
    else ok (s3, a1)
  else ok (s3, a1)

end Defs

section SpecDefs
open Fl4Spec

/-- The spec's tail of `receive_signal` on an active notification. -/
def specRecvTail (t n : ObjRef) : SMonad Unit Unit := do
  maybeDonateSc t n
  let scPtr ← getTcbObjRef Tcb.tcbSchedContext t
  ifSporadicCurScTestRefillUnblockCheck scPtr

/-- The spec's tail of `complete_signal`. -/
def specCompleteTail (tptr ntfnptr : ObjRef) : SMonad Unit Unit := do
  maybeDonateSc tptr ntfnptr
  let scOpt ← getTcbObjRef Tcb.tcbSchedContext tptr
  NonDet.maybeM (fun scp => do
      let sc ← getSchedContext scp
      NonDet.when sc.scSporadic <| do
        let ntfnScp ← getNtfnObjRef Notification.ntfnSc ntfnptr
        let curScPtr ← NonDet.gets fun s : State Unit => s.curSc
        NonDet.when (scOpt = ntfnScp ∧ scp ≠ curScPtr) <| refillUnblockCheck scp)
    scOpt

/-- Hypothesis (l4v `valid_sched_action`, refill part): a schedulable
switch-to candidate has an SC whose head refill is sufficient and ready. -/
def ActReady (σ : State Unit) : Prop :=
  ∀ t, σ.schedulerAction = .switchThread t → schedulable t σ = true →
    ∃ x scp, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some scp ∧
      getScRefillSufficient (Z := Unit) scp 0 σ = ({(true, σ)}, False) ∧
      getScRefillReady (Z := Unit) scp σ = ({(true, σ)}, False)

/-- What blocking thread `t` on notification `n` changes (NtfnBlock.lean): the
TCB's state (to one that is not runnable), the notification, possibly the
scheduler action (to choose-new). -/
def BlockStep (σ σ' : State Unit) (t n : ObjRef) : Prop :=
  (σ'.schedulerAction = σ.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread) ∧
  σ'.curTime = σ.curTime ∧ σ'.releaseQueue = σ.releaseQueue ∧
  (∀ p, p ≠ t → p ≠ n → σ'.kheap p = σ.kheap p) ∧
  (∃ x y, σ.kheap n = some (.notification x) ∧ σ'.kheap n = some (.notification y)) ∧
  (∃ x y, σ.kheap t = some (.tcb x) ∧ σ'.kheap t = some (.tcb y) ∧
    y.tcbSchedContext = x.tcbSchedContext ∧ runnable y.tcbState = false)

end SpecDefs

section Hyps
variable {S A : Type} (st : machine.Store S) (ar : machine.Arch A) [L : LawfulStore st]

/-- `c` (FL4, from `s`) refines `m` (spec, from `σ`): the spec does not fail,
FL4's outcome is matched by one of the spec's, FL4 keeps the footprint, the
spec keeps `KView`, and `SR` holds after. -/
def TailRef (N T : Set U64) (SR : S → Fl4Spec.State Unit → Prop) {α : Type} (fst : α → S) (s : S)
    (σ : Fl4Spec.State Unit) (c : Result α) (m : Fl4Spec.SMonad Unit Unit) : Prop :=
  c ⦃ r => ¬ (m σ).2 ∧ ∃ σ', ((), σ') ∈ (m σ).1 ∧ FootEq N T (L.mem s) (L.mem (fst r)) ∧ KView σ σ' ∧
    SR (fst r) σ' ⦄

/-- The receive-side hypotheses on the other subsystems. -/
structure RecvHyps (N T : Set U64) (SR : S → Fl4Spec.State Unit → Prop) : Prop where
  recvTail : ∀ s (a : A) σ (t n : U64), NtfnStateRel N T (L.mem s) σ → SR s σ → t ∈ T → n ∈ N →
    TailRef st N T SR Prod.fst s σ (rustRecvTail st ar s a t n) (specRecvTail t.bv n.bv)
  completeTail : ∀ s (a : A) σ (t n : U64), NtfnStateRel N T (L.mem s) σ → SR s σ → t ∈ T → n ∈ N →
    TailRef st N T SR Prod.fst s σ (rustCompleteTail st ar s a t n) (specCompleteTail t.bv n.bv)
  returnSc : ∀ s σ0 σ (t n : U64), NtfnStateRel N T (L.mem s) σ → SR s σ → t ∈ T → n ∈ N →
    ActReady σ0 → BlockStep σ0 σ t.bv n.bv →
    TailRef st N T SR id s σ (notification.maybe_return_sched_context st s n t) (Fl4Spec.maybeReturnSc n.bv t.bv)

end Hyps

/-! ## Single writes -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {N T : Set U64}

/-- Writing the badge register of a TCB. -/
theorem set_badge_reg_rel (hP : NPlaced T N) {s : S} {σ : Fl4Spec.State Unit}
    (hR : NtfnStateRel N T (L.mem s) σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (v : U64) :
    NtfnStateRel N T (L.mem (L.wr s (badgeRegA t) v)) (updK σ t.bv (.tcb (setReg x Fl4Spec.badge_register v.bv))) ∧
      WritesIn st s (L.wr s (badgeRegA t) v) (NWrite N T) ∧
      NtfnStep σ (updK σ t.bv (.tcb (setReg x Fl4Spec.badge_register v.bv))) := by
  have hx := hR.at_tcb ht hk
  obtain ⟨hw, hoth⟩ := twr_wr (st := st) hP ht (K := 256#u64) (Or.inr (Or.inr rfl)) s v
  rw [← badgeRegA_eq] at hw hoth
  refine ⟨hR.upd_tcb ht _ hw.ntfn hw.tcb hw.links (Or.inr ⟨?_, ?_⟩) ⟨?_, ?_, ?_, ?_⟩, hw.foot,
    NtfnStep.tcb hk x.tcbState _⟩
  · rw [tStA_eq, hoth _ (by simp) (by simp) (by simp)]
  · rw [tBlockA_eq, hoth _ (by simp) (by simp) (by simp)]
  · show (L.mem _ (tStA t)).val = tsCode (setReg x _ _).tcbState
    rw [setReg_state, tStA_eq, hoth _ (by simp) (by simp) (by simp), ← tStA_eq]; exact hx.st
  · intro n' hn'
    rw [setReg_state] at hn'
    rw [tBlockA_eq, hoth _ (by simp) (by simp) (by simp), ← tBlockA_eq]; exact hx.blk n' hn'
  · show (L.mem _ (badgeRegA t)).bv = badgeOf (setReg x _ _)
    rw [badgeOf_setReg, rd_wr_eq (foot_breg hP ht).1]
  · show (L.mem _ (prioA t)).val = (setReg x _ _).tcbPriority.toNat
    rw [setReg_prio, prioA_eq', hoth _ (by simp) (by simp) (by simp), ← prioA_eq']; exact hx.prio

theorem zero_and3' : (obj.NTFN_IDLE &&& 3#u64) = 0#u64 := by rw [ntfn_consts.1]; decide

/-- Making an active notification idle (`set_state(NTFN_IDLE)`). -/
theorem set_idle_rel (hP : NPlaced T N) {s : S} {σ : Fl4Spec.State Unit}
    (hR : NtfnStateRel N T (L.mem s) σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0) :
    let s' := L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))
    NtfnStateRel N T (L.mem s') (updK σ n.bv (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))) ∧
      WritesIn st s s' (NWrite N T) ∧
      NtfnStep σ (updK σ n.bv (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))) := by
  intro s'
  have hna := hP.ntfn n hn
  have h : NWr st N T n s s' := by
    show NWr st N T n s (L.wr s (epTSA n) _); rw [epTSA_eq]; exact nwr_wr hP hn (by simp) (by simp) _ _
  have hx := hR.at_ntfn hn hk
  have hobj := hx.obj
  rw [hact] at hobj
  obtain ⟨-, hq, -⟩ := hobj
  rw [queueRel_nil_iff] at hq
  have ne_ts : ∀ K : U64, K.val < 40 → K.val % 8 = 0 → K ≠ 8#u64 →
      L.mem s' (core.num.U64.wrapping_add n K) = L.mem s (core.num.U64.wrapping_add n K) := by
    intro K hK hK8 hne
    show L.mem (L.wr _ (epTSA n) _) _ = _
    rw [epTSA_eq]
    exact rd_wr_ne (nword hP hn (by simp) (by simp)).1 (nword hP hn hK hK8).1
      (nwords_ne hna (by simp) (by omega) (Ne.symm hne))
  have e_head : L.mem s' (epHeadA n) = L.mem s (epHeadA n) := by rw [epHeadA_eq, ne_ts _ (by simp) (by simp) (by simp)]
  have e_ts : L.mem s' (epTSA n) = (L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64) :=
    rd_wr_eq (foot_ts hP hn).1
  have e_bound : L.mem s' (nBoundA n) = L.mem s (nBoundA n) := by
    rw [nBoundA_eq, ne_ts _ (by simp) (by simp) (by simp)]
  have e_sc : L.mem s' (nScA n) = L.mem s (nScA n) := by rw [nScA_eq, ne_ts _ (by simp) (by simp) (by simp)]
  refine ⟨hR.upd_ntfn hn _ h.ntfn (fun y hy => (h.tcb y hy).1) (fun y hy _ => (h.tcb y hy).2) ⟨?_, ?_, ?_, ?_⟩,
    h.foot, NtfnStep.ntfn hk rfl rfl⟩
  · show NtfnObjRel _ T n .idleNtfn
    refine ⟨?_, ?_⟩
    · rw [stOf, e_ts, ts_state]; exact zero_and3'
    · rw [queueRel_nil_iff]
      refine ⟨?_, ?_⟩
      · show L.mem s' (epHeadA n) = 0#u64
        rw [e_head]; exact hq.1
      · show L.mem s' (epTSA n) &&& ~~~3#u64 = 0#u64
        rw [e_ts, ts_end]; exact hq.2
  · show x.ntfnBoundTcb = _; rw [e_bound]; exact hx.bound
  · rw [e_bound]; exact hx.bound_mem
  · show x.ntfnSc = _; rw [e_sc]; exact hx.sc

end

/-! ## `receive_signal` -/

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T : Set U64}
  {SR : S → Fl4Spec.State Unit → Prop}

/-- The spec's `receive_signal` on a notification cap to `p`, unfolded to the
notification. -/
theorem receiveSignal_cap {σ : Fl4Spec.State Unit} {p t : Fl4Spec.ObjRef} {x : Fl4Spec.Notification}
    (hk : σ.kheap p = some (.notification x)) (b : Fl4Spec.Badge) (r : Fl4Spec.CapRights) (blk : Bool) :
    Fl4Spec.receiveSignal (Z := Unit) t (.notificationCap p b r) blk σ =
      (match x.ntfnObj with
        | .activeNtfn badge => do
          Fl4Spec.asUser t <| Fl4Spec.setRegister Fl4Spec.badge_register badge
          Fl4Spec.setNotification p <| Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x
          specRecvTail t p
        | _ => Fl4Spec.receiveSignalBlocked t p blk) σ := by
  unfold Fl4Spec.receiveSignal
  dsimp only
  rw [nd_pure_bind', nd_bind_one (getNotification_eq hk)]
  rfl

/-- `receive_signal` on a notification that is not active is
`receive_signal_blocked`. -/
theorem receiveSignal_notActive {σ : Fl4Spec.State Unit} {p t : Fl4Spec.ObjRef} {x : Fl4Spec.Notification}
    (hk : σ.kheap p = some (.notification x)) (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b) (b : Fl4Spec.Badge)
    (r : Fl4Spec.CapRights) (blk : Bool) :
    Fl4Spec.receiveSignal (Z := Unit) t (.notificationCap p b r) blk σ = Fl4Spec.receiveSignalBlocked t p blk σ := by
  rw [receiveSignal_cap hk]
  revert hna
  cases x.ntfnObj with
  | activeNtfn b' => intro h; exact absurd rfl (h b')
  | _ => intro _; rfl

/-- **Polling** a notification that is not active: the badge register gets
0. -/
theorem receive_signal_poll (hP : NPlaced T N) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) {t : U64} (ht : t ∈ T) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b) (cb : Fl4Spec.Badge) (cr : Fl4Spec.CapRights) :
    notification.receive_signal st ar s a t n false ⦃ r =>
      r.2 = a ∧ SingleRel (st := st) N T s σ (Fl4Spec.receiveSignal t.bv (.notificationCap n.bv cb cr) false σ) r.1 ⦄ := by
  have hx := hR.at_ntfn hn hk
  obtain ⟨xt, hkt, -⟩ := hR.tcb t ht
  have hspec : Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) false σ =
      ({((), updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register 0)))}, False) := by
    rw [receiveSignal_cap hk]
    have : (match x.ntfnObj with
        | .activeNtfn badge => (do
          Fl4Spec.asUser t.bv <| Fl4Spec.setRegister Fl4Spec.badge_register badge
          Fl4Spec.setNotification n.bv <| Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x
          specRecvTail t.bv n.bv : Fl4Spec.SMonad Unit Unit)
        | _ => Fl4Spec.receiveSignalBlocked t.bv n.bv false) = Fl4Spec.receiveSignalBlocked t.bv n.bv false := by
      cases h : x.ntfnObj with
      | activeNtfn b => exact absurd h (hna b)
      | _ => rfl
    rw [this]
    unfold Fl4Spec.receiveSignalBlocked Fl4Spec.doNbrecvFailedTransfer
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [nd_bind_one (asUser_setRegister_eq _ _ hkt)]
    rfl
  have hst : stOf (L.mem s) n = obj.NTFN_IDLE ∨ stOf (L.mem s) n = obj.NTFN_WAITING := by
    have := hx.obj
    cases h : x.ntfnObj with
    | idleNtfn => exact Or.inl (stOf_idle (T := T) (h ▸ this) rfl)
    | waitingNtfn q => exact Or.inr (stOf_waiting (T := T) (h ▸ this) rfl)
    | activeNtfn b => exact absurd h (hna b)
  obtain ⟨hR', hW, hS⟩ := set_badge_reg_rel hP hR ht hkt 0#u64
  unfold notification.receive_signal
  step
  rw [st_post, epState_eq] at *
  rcases hst with hst | hst
  · simp only [hst, ↓reduceIte, Bool.false_eq_true]
    step
    subst s1_post
    exact ⟨_, hspec, hR', hS, hW⟩
  · simp only [hst, ntfn_consts.1, ntfn_consts.2.1, show (1#u64 : U64) ≠ 0#u64 by decide, ↓reduceIte,
      Bool.false_eq_true]
    step
    subst s1_post
    exact ⟨_, hspec, hR', hS, hW⟩


/-- Receiving from an active notification: the badge register and the
notification after the two writes, related to the spec's. -/
theorem recv_active_prefix (hP : NPlaced T N) {s : S} {σ : Fl4Spec.State Unit}
    (hR : NtfnStateRel N T (L.mem s) σ) {t : U64} (ht : t ∈ T) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) {b0 : Fl4Spec.Badge}
    (hact : x.ntfnObj = .activeNtfn b0) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) :
    let s1 := L.wr s (badgeRegA t) (L.mem s (nBadgeA n))
    let s2 := L.wr s1 (epTSA n) ((L.mem s1 (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))
    let σ1 := updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))
    let σ2 := updK σ1 n.bv (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))
    Fl4Spec.asUser (Z := Unit) t.bv (Fl4Spec.setRegister Fl4Spec.badge_register b0) σ = ({((), σ1)}, False) ∧
    Fl4Spec.setNotification (Z := Unit) n.bv (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x) σ1 =
      ({((), σ2)}, False) ∧
    NtfnStateRel N T (L.mem s2) σ2 ∧ WritesIn st s s2 (NWrite N T) ∧ NtfnStep σ σ2 := by
  intro s1 s2 σ1 σ2
  have hx := hR.at_ntfn hn hk
  have hb0 : (L.mem s (nBadgeA n)).bv = b0 := by
    have := hx.obj; rw [hact] at this; exact this.2.2
  obtain ⟨hR1, hW1, hS1⟩ := set_badge_reg_rel hP hR ht hkt (L.mem s (nBadgeA n))
  rw [hb0] at hR1 hS1
  have hnt : n.bv ≠ t.bv := by intro e; rw [e, hkt] at hk; cases hk
  have hk1 : σ1.kheap n.bv = some (.notification x) := by simp [σ1, hnt, hk]
  obtain ⟨hR2, hW2, hS2⟩ := set_idle_rel hP hR1 hn hk1 hact
  exact ⟨asUser_setRegister_eq _ _ hkt, setNotification_eq _ hk1, hR2,
    (hW1.trans hW2).mono (fun _ h => by rcases h with h | h <;> exact h), hS1.trans hS2⟩

/-- **Receive on an active notification**: the badge goes to the badge
register, the notification becomes idle, then the scheduler tail. -/
theorem receive_signal_active (hH : SchedHyps st ar N T SR) (hV : RecvHyps st ar N T SR) (hP : NPlaced T N)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : NtfnStateRel N T (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (blk : Bool) (cb : Fl4Spec.Badge) (cr : Fl4Spec.CapRights) :
    notification.receive_signal st ar s a t n blk ⦃ r =>
      ¬ (Fl4Spec.receiveSignal t.bv (.notificationCap n.bv cb cr) blk σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveSignal t.bv (.notificationCap n.bv cb cr) blk σ).1 ∧
        NtfnStateRel N T (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ntfn hn hk
  obtain ⟨xt, hkt, -⟩ := hR.tcb t ht
  obtain ⟨e1, e2, hR2, hW, hS⟩ := recv_active_prefix (st := st) hP hR ht hn hk hact hkt
  have hspec : Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) blk σ =
      specRecvTail t.bv n.bv (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
        (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))) := by
    rw [receiveSignal_cap hk]
    simp only [hact]
    rw [nd_bind_one e1, nd_bind_one e2]
  rw [hspec]
  have hSR2 := hH.stable _ _ _ _ hSR hW hS
  have hsa : stOf (L.mem s) n = obj.NTFN_ACTIVE := stOf_active hx.obj hact
  unfold notification.receive_signal
  step
  have hi : ¬ L.epState s n = obj.NTFN_IDLE := by
    rw [epState_eq, hsa, ntfn_consts.1, ntfn_consts.2.2]; decide
  have hw' : ¬ L.epState s n = obj.NTFN_WAITING := by
    rw [epState_eq, hsa, ntfn_consts.2.1, ntfn_consts.2.2]; decide
  rw [st_post]
  simp only [hi, hw', ↓reduceIte]
  step
  step
  step
  subst_vars
  refine WP.spec_mono (hV.recvTail _ a _ t n hR2 hSR2 ht hn) ?_
  rintro r ⟨hnf, σ', hm, hf, hv, hS'⟩
  exact ⟨hnf, σ', hm, hR2.frame hP hf hv, hS'⟩

/-- **`complete_signal` on an active notification** (bound notification at
the end of a receive): as the active receive, with `complete_signal`'s
tail. -/
theorem complete_signal_active (hH : SchedHyps st ar N T SR) (hV : RecvHyps st ar N T SR) (hP : NPlaced T N)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : NtfnStateRel N T (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0) :
    notification.complete_signal st ar s a n t ⦃ r =>
      ¬ (Fl4Spec.completeSignal n.bv t.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (Fl4Spec.completeSignal n.bv t.bv σ).1 ∧
        NtfnStateRel N T (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ntfn hn hk
  obtain ⟨xt, hkt, -⟩ := hR.tcb t ht
  obtain ⟨e1, e2, hR2, hW, hS⟩ := recv_active_prefix (st := st) hP hR ht hn hk hact hkt
  have hspec : Fl4Spec.completeSignal (Z := Unit) n.bv t.bv σ =
      specCompleteTail t.bv n.bv (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
        (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))) := by
    unfold Fl4Spec.completeSignal
    rw [nd_bind_one (getNotification_eq hk)]
    simp only [hact]
    rw [nd_bind_one e1, nd_bind_one e2]
    rfl
  rw [hspec]
  have hSR2 := hH.stable _ _ _ _ hSR hW hS
  have hsa : stOf (L.mem s) n = obj.NTFN_ACTIVE := stOf_active hx.obj hact
  have ht0 : t ≠ 0#u64 := fun e => (hP.tcb t ht).ne0 (by rw [e]; rfl)
  unfold notification.complete_signal
  step
  simp only [b_post, ht0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step
  rw [i_post, epState_eq, hsa]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  step
  step
  step
  subst_vars
  refine WP.spec_mono (hV.completeTail _ a _ t n hR2 hSR2 ht hn) ?_
  rintro r ⟨hnf, σ', hm, hf, hv, hS'⟩
  exact ⟨hnf, σ', hm, hR2.frame hP hf hv, hS'⟩

end

end

end Fl4Proofs.P3.Notif
