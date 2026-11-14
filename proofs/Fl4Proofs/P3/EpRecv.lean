/-
P3 (DESIGN.md §9), endpoints: **`receive_ipc` on an idle endpoint or one
with waiting receivers refines l4v `receive_ipc`** (`Z = Unit`):

* `receive_ipc_poll`: a polling receive (`blocking = false`) writes 0 to the
  badge register (l4v `do_nbrecv_failed_transfer`);
* `receive_ipc_block`: a blocking receive sets the thread's state to
  `BlockedOnReceive e reply` (block object and reply words;
  `schedule_tcb` ↔ `set_thread_state_act`), links the reply object to the
  thread (`reply_tcb`), and inserts the thread in the queue by priority
  (`ep_append_rel`); the endpoint becomes `RecvEP`.

In both the spec has exactly one outcome and does not fail.

Scope (hypotheses): the thread has no bound notification (the bound,
active case is `complete_signal`, NtfnRecv.lean; the bound case also runs
`maybe_return_sc`), and the reply cap is null or a reply cap whose reply
object is not linked to a thread (otherwise both cancel that thread's IPC
first, `cancel_ipc`, not covered here). As for the send: the thread is not
blocked on an endpoint, and the queue is sorted by priority.
-/
import Fl4Proofs.P3.EpRegs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-! ## The reply cap -/

/-- FL4's reply cap `rc` and the spec's `rc'` name the reply `rv` (0 for
none), whose reply object (if any) is in `R` and not linked to a thread. -/
def ReplyArg (R : Set U64) (m : U64 → U64) (rc : capability.Cap) (rc' : Fl4Spec.Cap) (rv : U64) : Prop :=
  (rc = .Null ∧ rc' = .nullCap ∧ rv = 0#u64) ∨
  (∃ b r', rc = .Reply rv b ∧ rc' = .replyCap rv.bv r' ∧ rv ∈ R ∧ m (rTcbA rv) = 0#u64)

/-! ## The preamble -/

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)}

/-- What `receive_ipc` does before looking at the endpoint, without a bound
notification and with a reply cap as in `ReplyArg`. -/
theorem receive_ipc_pre (s : S) (a : A) (t e cb : U64) (c1 c2 c3 c4 blk : Bool) (rc : capability.Cap)
    (rc' : Fl4Spec.Cap) (rv : U64) (hrc : ReplyArg R (L.mem s) rc rc' rv) (hbound : L.mem s (tBoundA t) = 0#u64)
    {P : S × A → Prop}
    (h : (do
      let st1 ← obj.Ep.state st e s
      if st1 = obj.EP_IDLE then do
        let s3 ← endpoint.wait_for_sender st s t e blk rv
        ok (s3, a)
      else if st1 = obj.EP_RECV then do
        let s3 ← endpoint.wait_for_sender st s t e blk rv
        ok (s3, a)
      else endpoint.receive_from_sender st ar s a t e rv) ⦃ P ⦄) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ P ⦄ := by
  unfold endpoint.receive_ipc
  simp only [capability.Cap.ptr, bind_tc_ok]
  rcases hrc with ⟨rfl, -, rfl⟩ | ⟨b, r', rfl, -, -, h0⟩
  · simp only [endpoint.take_reply, bind_tc_ok]
    step as ⟨i, hi⟩
    simp only [hi, hbound, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    simp only [bind_tc_ok, bind_ok, Bind.bind]
    exact h
  · simp only [endpoint.take_reply]
    step as ⟨i, hi⟩
    step as ⟨b, hb⟩
    simp only [hb, hi, h0, decide_true, ↓reduceIte, bind_tc_ok]
    step as ⟨j, hj⟩
    simp only [hj, hbound, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    simp only [bind_tc_ok, bind_ok, Bind.bind]
    exact h

end

/-! ## The spec's preamble -/

section Spec
open Fl4Spec

/-- The spec's reply cap `rc'` names `reply`, a reply object not linked to a
thread. -/
def SpecReplyArg (σ : State Unit) (rc' : Cap) (reply : Option ObjRef) : Prop :=
  (rc' = .nullCap ∧ reply = none) ∨
  (∃ r rr x, rc' = .replyCap r rr ∧ reply = some r ∧ σ.kheap r = some (.reply x) ∧ x.replyTcb = none)

theorem nd_when_false {σ' : Type} {P : Prop} [Decidable P] (h : ¬ P) (m : NonDet σ' Unit) :
    NonDet.when P m = pure () := by
  unfold NonDet.when; rw [if_neg h]; rfl

theorem nd_when_false_bind {σ' β : Type} {P : Prop} [Decidable P] (h : ¬ P) (m : NonDet σ' Unit)
    (f : Unit → NonDet σ' β) (s : σ') : (NonDet.when P m >>= f) s = f () s := by
  rw [nd_when_false h, nd_pure_bind']

/-- `receive_ipc` without a bound notification on an endpoint with no waiting
sender is `receive_ipc_blocked`. -/
theorem receiveIpc_noSend {σ : State Unit} {t e : ObjRef} (b : Badge) (rights : CapRights) (blk : Bool)
    {rc' : Cap} {reply : Option ObjRef} (hrc : SpecReplyArg σ rc' reply) {xt : Tcb}
    (hkt : σ.kheap t = some (.tcb xt)) (hb : xt.tcbBoundNotification = none) {x : Endpoint}
    (hk : σ.kheap e = some (.endpoint x)) (hns : ∀ q, x ≠ .sendEP q) :
    receiveIpc (Z := Unit) t (.endpointCap e b rights) blk rc' σ = receiveIpcBlocked blk t e reply σ := by
  unfold receiveIpc
  dsimp only
  rw [nd_pure_bind']
  rcases hrc with ⟨rfl, rfl⟩ | ⟨r, rr, xr, rfl, rfl, hkr, hr⟩
  · dsimp only
    rw [nd_pure_bind', nd_bind_one (getEndpoint_eq hk), nd_bind_one (getTcbObjRef_eq _ hkt)]
    simp only [hb]
    rw [nd_pure_bind']
    simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte]
    rw [nd_when_false_bind (by simp [hb])]
  · dsimp only
    rw [nd_bind_one (getReplyTcb_eq hkr)]
    simp only [hr]
    rw [nd_when_false_bind (by simp [hr])]
    rw [nd_pure_bind', nd_bind_one (getEndpoint_eq hk), nd_bind_one (getTcbObjRef_eq _ hkt)]
    simp only [hb]
    rw [nd_pure_bind']
    simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte]
    rw [nd_when_false_bind (by simp [hb])]

end Spec

/-! ## The FL4 side -/

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

theorem replyArg_ne {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} {m : U64 → U64}
    (hP : EPlaced T E R B) (h : ReplyArg R m rc rc' rv) (hne : rv ≠ 0#u64) : rv ∈ R ∧ m (rTcbA rv) = 0#u64 := by
  rcases h with ⟨-, -, rfl⟩ | ⟨b, r', -, -, hr, h0⟩
  · exact absurd rfl hne
  · exact ⟨hr, h0⟩

theorem rep_ne0 (hP : EPlaced T E R B) {r : U64} (hr : r ∈ R) : r ≠ 0#u64 := by
  intro e; have := (hP.rep r hr).2.1; rw [e] at this; exact this rfl

theorem replyArg_spec (hP : EPlaced T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hR : EpStateRel T E R B (L.mem s) σ)
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (h : ReplyArg R (L.mem s) rc rc' rv) :
    SpecReplyArg σ rc' (optRef rv) := by
  rcases h with ⟨-, rfl, rfl⟩ | ⟨b, r', -, rfl, hr, h0⟩
  · exact Or.inl ⟨rfl, optRef_zero⟩
  · obtain ⟨xr, hkr, hxr⟩ := hR.reply rv hr
    exact Or.inr ⟨rv.bv, r', xr, rfl, optRef_ne (rep_ne0 hP hr), hkr, by rw [hxr, h0, optRef_zero]⟩

/-- The three writes of a blocking receive. -/
theorem block_recv_writes (hP : EPlaced T E R B) (s : S) {t : U64} (ht : t ∈ T) (e rv : U64) :
    let s3 := L.wr (L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_RECV) (tBlockA t) e) (tReplyA t) rv
    Agree (L.mem s) (L.mem s3) (fun b => b.val ≠ t.val + 3328 ∧ b.val ≠ t.val + 3336 ∧ b.val ≠ t.val + 3360) ∧
      L.mem s3 (tStA t) = sched.TS_BLOCKED_ON_RECV ∧ L.mem s3 (tBlockA t) = e ∧ L.mem s3 (tReplyA t) = rv ∧
      WritesIn st s s3 (EWrite T E R B) := by
  intro s3
  have hta := hP.tcb t ht
  have a1 := (a_st hta).1; have a2 := (a_blk hta).1; have a3 := (a_reply hta).1
  have v1 := val_st hta; have v2 := val_blk hta; have v3 := val_reply hta
  have g1 := agree_wr2 (L := L) (s := s) (v := sched.TS_BLOCKED_ON_RECV) (w := e) a1 a2
  have g2 := agree_wr (L := L) (s := L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_RECV) (tBlockA t) e) (v := rv) a3
  refine ⟨(g1.mono fun b hb => ?_).trans (g2.mono fun b hb => ?_), ?_, ?_, ?_, ?_⟩
  · rw [v1, v2]; omega
  · rw [v3]; omega
  · show L.mem (L.wr (L.wr (L.wr s _ _) _ _) _ _) _ = _
    rw [L.mem_wr_ne a3 a1 (by omega), L.mem_wr_ne a2 a1 (by omega), L.mem_wr_same a1]
  · show L.mem (L.wr (L.wr (L.wr s _ _) _ _) _ _) _ = _
    rw [L.mem_wr_ne a3 a2 (by omega), L.mem_wr_same a2]
  · exact L.mem_wr_same a3
  · refine (((wr_ewrite (E := E) (R := R) (B := B) ht (twf_of 3328 v1 (by unfold TWOffN; omega)) a1 s _).trans
      (wr_ewrite (E := E) (R := R) (B := B) ht (twf_of 3336 v2 (by unfold TWOffN; omega)) a2 _ _)).trans
      (wr_ewrite (E := E) (R := R) (B := B) ht (twf_of 3360 v3 (by unfold TWOffN; omega)) a3 _ _)).mono
      fun b hb => ?_
    rcases hb with (hb | hb) | hb <;> exact hb

/-- Linking the reply object `r` to the thread `t` (`reply.set_tcb t`). -/
theorem reply_link_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {r : U64} (hr : r ∈ R) {xr : Fl4Spec.Reply}
    (hkr : σ.kheap r.bv = some (.reply xr)) {t : U64} (ht : TcbAddr t) :
    Fl4Spec.setReplyObjRef (Z := Unit) Fl4Spec.replyTcbUpdate r.bv (some t.bv) σ =
      ({((), updK σ r.bv (.reply { xr with replyTcb := some t.bv }))}, False) ∧
    EpStateRel T E R B (L.mem (L.wr s (rTcbA r) t)) (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) ∧
    SR (L.wr s (rTcbA r) t) (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) ∧
    Agree (L.mem s) (L.mem (L.wr s (rTcbA r) t)) (fun b => b.val ≠ r.val) := by
  have ha := a_rtcb hP hr
  have hag := agree_wr (L := L) (s := s) (v := t) ha.1
  have hag' : Agree (L.mem s) (L.mem (L.wr s (rTcbA r) t)) (fun b => b.val ≠ r.val) :=
    hag.mono fun b hb => by rw [rTcbA_val]; exact hb
  have ht0 : t ≠ 0#u64 := fun e => ht.ne0 (by rw [e]; rfl)
  refine ⟨setReplyTcb_eq _ hkr, hR.upd_reply hP hr _ (hag'.mono fun b hb => hb.2) ?_, ?_, hag'⟩
  · show some t.bv = optRef _
    rw [rd_wr_eq ha.1, optRef_ne ht0]
  · refine hH.stable _ _ _ _ hSR ((writesIn_wr ha.1).mono fun b hb => ?_) (EpStep.reply hkr _)
    subst hb
    exact Or.inr (Or.inl ⟨r, hr, rTcbA_val r⟩)

theorem ok_bind_spec {α β : Type} (x : α) (f : α → Result β) {P : β → Prop} (h : f x ⦃ P ⦄) :
    (do let y ← ok x; f y) ⦃ P ⦄ := by
  simp only [Bind.bind, bind_ok]; exact h

/-- **Blocking receive** on an idle endpoint or one with waiting receivers. -/
theorem receive_ipc_block (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock true x)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) true rc ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ = ({((), σ')}, False) ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hta := hP.tcb t ht
  have hq := not_queued hR ht hkt hnb
  have htq : t.bv ∉ x.epQueue := hq e he x hk
  have hbound : L.mem s (tBoundA t) = 0#u64 := optRef_none (hxt.bound.symm.trans hbn)
  have hns : ∀ q, x ≠ .sendEP q := fun q h => by subst h; simp [CanBlock] at hc
  have hspec0 := receiveIpc_noSend b rights true (replyArg_spec hP hR hrc) hkt hbn hk hns
  set x1 : Fl4Spec.Tcb := { xt with tcbState := .blockedOnReceive e.bv (optRef rv) { receiverCanGrant := false } }
  set σ1 := updK σ t.bv (.tcb x1)
  set s3 := L.wr (L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_RECV) (tBlockA t) e) (tReplyA t) rv
  obtain ⟨hA3, r1, r2, r3, hW3⟩ := block_recv_writes (L := L) hP s ht e rv
  have v1 := val_st hta; have v2 := val_blk hta; have v3 := val_reply hta
  have hR1 : EpStateRel T E R B (L.mem s3) σ1 := by
    refine hR.upd_tcb hP ht x1 (hA3.mono fun b hb => ?_) (Or.inl hq) ?_
    · have n1 : b.val ≠ (tStA t).val := fun h => hb.2 (TF.of_val (a_st hta).2 h)
      have n2 : b.val ≠ (tBlockA t).val := fun h => hb.2 (TF.of_val (a_blk hta).2 h)
      have n3 : b.val ≠ (tReplyA t).val := fun h => hb.2 (TF.of_val (a_reply hta).2 h)
      omega
    refine hxt.restate hta (hA3.mono fun b hb => ?_) rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_
    · have := hb.2; omega
    · rw [r1]; unfold sched.TS_BLOCKED_ON_RECV; rfl
    · intro e' h; simp only [x1, Fl4Spec.epBlocked, Option.some.injEq] at h; subst h; rw [r2]
    · intro e' d'' h; simp [x1] at h
    · intro e' r d'' h
      simp only [x1, Fl4Spec.ThreadState.blockedOnReceive.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      refine ⟨by rw [r3], fun hne => ?_⟩
      rw [r3]
      by_cases h0 : rv = 0#u64
      · rw [h0, optRef_zero] at hne; exact absurd rfl hne
      · exact (replyArg_ne hP hrc h0).1
    · intro r h; simp [x1] at h
  have hS1 : EpStep σ σ1 := EpStep.tcb hkt _ xt.tcbArch
  have hSR1 := hH.stable _ _ _ _ hSR hW3 hS1
  set σ2 := stsAct σ1 t.bv
  have hnt : e.bv ≠ t.bv := kheap_ne hk hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hk2 : σ2.kheap e.bv = some (.endpoint x) := by simp [σ2, σ1, stsAct_kheap, hnt, hk]
  have hkt2 : σ2.kheap t.bv = some (.tcb x1) := by simp [σ2, σ1, stsAct_kheap]
  have hspec : Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ =
      (Fl4Spec.NonDet.maybeM (fun r => Fl4Spec.setReplyObjRef Fl4Spec.replyTcbUpdate r (some t.bv)) (optRef rv) >>=
        fun _ => Fl4Spec.tcbEpAppend t.bv e.bv true) σ2 := by
    rw [hspec0]
    unfold Fl4Spec.receiveIpcBlocked
    rw [if_pos rfl, nd_bind_one (setThreadState_eq _ hkt)]
  have hprio3 : ∀ y ∈ T, L.mem s3 (prioA y) = L.mem s (prioA y) := by
    intro y hy
    have hya := hP.tcb y hy
    refine hA3 _ (a_prio hya).1 ?_
    have := val_prio hya
    by_cases eyt : y = t
    · subst eyt; omega
    · have := tcb_disj hP ht hy eyt; omega
  have key : (do
      let s3 ← endpoint.wait_for_sender st s t e true rv
      ok (s3, a)) ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ = ({((), σ')}, False) ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
    unfold endpoint.wait_for_sender
    simp only [↓reduceIte]
    step as ⟨s1', h1⟩
    step as ⟨s2', h2⟩
    step as ⟨s3', h3⟩
    subst h1 h2 h3
    refine WP.spec_bind (hH.scheduleTcb _ σ1 t hR1 hSR1 ht) ?_
    rintro s4 ⟨hf4, hS4⟩
    have hR2 : EpStateRel T E R B (L.mem s4) σ2 := hR1.frame hP hf4 (KView.stsAct' _ _)
    have hfoot : ∀ {a'}, Aligned a' ∧ TF t a' → L.mem s4 a' = L.mem s3 a' := fun h =>
      hf4 _ h.1 (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl h.2⟩)))
    have hprio4 : ∀ y ∈ T, L.mem s4 (prioA y) = L.mem s (prioA y) := fun y hy => by
      have hya := hP.tcb y hy
      rw [hf4 _ (a_prio hya).1 (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl (a_prio hya).2⟩))), hprio3 y hy]
    -- the tail, from a state related to `σ3` with the endpoint and thread unchanged
    have tail : ∀ (s5 : S) (σ3 : Fl4Spec.State Unit), EpStateRel T E R B (L.mem s5) σ3 → SR s5 σ3 →
        σ3.kheap e.bv = some (.endpoint x) → σ3.kheap t.bv = some (.tcb x1) →
        (∀ y ∈ T, L.mem s5 (prioA y) = L.mem s (prioA y)) →
        L.mem s5 (tStA t) = sched.TS_BLOCKED_ON_RECV → L.mem s5 (tBlockA t) = e →
        (Fl4Spec.NonDet.maybeM (fun r => Fl4Spec.setReplyObjRef Fl4Spec.replyTcbUpdate r (some t.bv)) (optRef rv) σ2 =
          ({((), σ3)}, False)) →
        (do
          let s6 ← endpoint.ep_append st s5 e t obj.EP_RECV
          ok (s6, a)) ⦃ r => r.2 = a ∧
          ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ =
            ({((), σ')}, False) ∧ EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
      intro s5 σ3 hR3 hS3 hk3 hkt3 hpr5 hst5 hb5 hm
      have hsort5 := sorted_transfer hP.tcb hx (hR3.at_ep he hk3) hpr5 hsort
      have happ := ep_append_rel hH hP s5 σ3 hR3 hS3 ht hkt3 he hk3 true hc htq
        (by rw [hst5]; unfold sched.TS_BLOCKED_ON_RECV; rfl) hb5 hsort5
      simp only [↓reduceIte] at happ
      refine WP.spec_bind happ ?_
      rintro s6 ⟨σ', hσ', hR', hS'⟩
      simp only [WP.spec_ok]
      exact ⟨by simp, σ', by rw [hspec, nd_bind_one hm]; exact hσ', hR', hS'⟩
    by_cases h0 : rv = 0#u64
    · simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      apply ok_bind_spec
      refine tail s4 σ2 hR2 hS4 hk2 hkt2 hprio4 ?_ ?_ (by rw [h0, optRef_zero]; rfl)
      · rw [hfoot (a_st hta), r1]
      · rw [hfoot (a_blk hta), r2]
    · have hne : (rv != 0#u64) = true := by simp [h0]
      simp only [hne, ↓reduceIte]
      obtain ⟨hrR, -⟩ := replyArg_ne hP hrc h0
      obtain ⟨xr, hkr, -⟩ := hR2.reply rv hrR
      obtain ⟨e1, hR5, hS5, hA5⟩ := reply_link_rel hH hP s4 σ2 hR2 hS4 hrR hkr hta
      step as ⟨s6', h6⟩
      subst h6
      have hnr : rv.bv ≠ e.bv := kheap_ne hkr hk2 (fun _ h1 h2 => by subst h1; cases h2)
      have hnr' : rv.bv ≠ t.bv := kheap_ne hkr hkt2 (fun _ h1 h2 => by subst h1; cases h2)
      have hdis := hP.rt rv hrR t ht
      refine tail _ _ hR5 hS5 (by simp [Ne.symm hnr, hk2]) (by simp [Ne.symm hnr', hkt2]) ?_ ?_ ?_ ?_
      · intro y hy
        have hya := hP.tcb y hy
        have := hP.rt rv hrR y hy
        rw [hA5 _ (a_prio hya).1 (by show (prioA y).val ≠ rv.val; rw [val_prio hya]; omega), hprio4 y hy]
      · rw [hA5 _ (a_st hta).1 (by show (tStA t).val ≠ rv.val; rw [val_st hta]; omega), hfoot (a_st hta), r1]
      · rw [hA5 _ (a_blk hta).1 (by show (tBlockA t).val ≠ rv.val; rw [val_blk hta]; omega), hfoot (a_blk hta), r2]
      · rw [optRef_ne h0]; exact e1
  apply receive_ipc_pre s a t e cb c1 c2 c3 c4 true rc rc' rv hrc hbound
  step as ⟨st1, hst1⟩
  rw [hst1, epState_eq]
  cases x with
  | idleEP =>
    rw [hx.1, if_pos ep_state_vals.1.symm]
    exact key
  | recvEP q =>
    rw [hx.1, if_neg (by rw [ep_state_vals.1]; decide), if_pos ep_state_vals.2.2.symm]
    exact key
  | sendEP q => exact absurd rfl (hns q)

/-- **Polling receive** on an idle endpoint or one with waiting receivers:
the badge register gets 0. -/
theorem receive_ipc_poll (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hbn : xt.tcbBoundNotification = none)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock true x) (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) false rc ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ = ({((), σ')}, False) ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hbound : L.mem s (tBoundA t) = 0#u64 := optRef_none (hxt.bound.symm.trans hbn)
  have hns : ∀ q, x ≠ .sendEP q := fun q h => by subst h; simp [CanBlock] at hc
  have hspec0 := receiveIpc_noSend b rights false (replyArg_spec hP hR hrc) hkt hbn hk hns
  obtain ⟨hR1, hW1, hS1⟩ := write_reg_rel hP s σ hR ht hkt Fl4Spec.badge_register 0#u64
  have hspec : Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ =
      ({((), updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register (0#u64 : U64).bv)))}, False) := by
    rw [hspec0]
    unfold Fl4Spec.receiveIpcBlocked Fl4Spec.doNbrecvFailedTransfer
    rw [if_neg (by simp), nd_bind_one (asUser_setRegister_eq _ _ hkt)]
    rfl
  have key : (do
      let s3 ← endpoint.wait_for_sender st s t e false rv
      ok (s3, a)) ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ = ({((), σ')}, False) ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
    unfold endpoint.wait_for_sender
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← regIdx_badge]
    step as ⟨s1', h1⟩
    subst h1
    exact ⟨_, hspec, hR1, hH.stable _ _ _ _ hSR hW1 hS1⟩
  apply receive_ipc_pre s a t e cb c1 c2 c3 c4 false rc rc' rv hrc hbound
  step as ⟨st1, hst1⟩
  rw [hst1, epState_eq]
  cases x with
  | idleEP =>
    rw [hx.1, if_pos ep_state_vals.1.symm]
    exact key
  | recvEP q =>
    rw [hx.1, if_neg (by rw [ep_state_vals.1]; decide), if_pos ep_state_vals.2.2.symm]
    exact key
  | sendEP q => exact absurd rfl (hns q)

end

end

end Fl4Proofs.P3.Endp
