/-
P3 (DESIGN.md §9), endpoints: **`send_ipc` on an idle endpoint or one with
waiting senders refines l4v `send_ipc`** (`Z = Unit`):

* `send_ipc_noblock`: a non-blocking send (`blocking = false`) does
  nothing, as the spec;
* `send_ipc_block`: a blocking send sets the thread's state to
  `BlockedOnSend e ⦇badge, canGrant, canGrantReply, isCall⦈` (the block
  object, badge and flags words; `schedule_tcb` ↔ `set_thread_state_act`,
  `EpHyps.scheduleTcb`) and inserts it in the queue by priority
  (`ep_append_rel`); the endpoint becomes `SendEP`.

In both the spec has exactly one outcome and does not fail.

Extra hypotheses: the thread is a TCB not blocked on an endpoint (it is the
running thread in seL4), and the endpoint's queue is sorted by priority.
-/
import Fl4Proofs.P3.EpAppend
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

/-- The queue of a related endpoint is the list of the relation, in any
related state where the endpoint is the same. -/
theorem queue_same {m m' : U64 → U64} {e : U64} {x : Fl4Spec.Endpoint} (hT : TcbPlaced T)
    (h : EpObjRel m T e x) (h' : EpObjRel m' T e x) {xs : List U64}
    (hq : QueueRel m' T .Ep (qOf m' e) xs) : QueueRel m T .Ep (qOf m e) xs := by
  obtain ⟨ys, hy1, hy2, -⟩ := h.queue
  obtain ⟨zs, hz1, hz2, -⟩ := h'.queue
  have e1 : xs = zs := hq.unique hT hz1
  have e2 : zs = ys := List.map_injective_iff.2 (fun a b h => eq_of_bv h) (hz2.symm.trans hy2)
  rw [e1, e2]; exact hy1

/-- Sortedness carries over to a state with the same endpoint and
priorities. -/
theorem sorted_transfer {m m' : U64 → U64} {e : U64} {x : Fl4Spec.Endpoint} (hT : TcbPlaced T)
    (h : EpObjRel m T e x) (h' : EpObjRel m' T e x) (hpr : ∀ y ∈ T, m' (prioA y) = m (prioA y))
    (hsort : ∀ xs, QueueRel m T .Ep (qOf m e) xs → PrioSorted (fun y => m (prioA y)) xs) :
    ∀ xs, QueueRel m' T .Ep (qOf m' e) xs → PrioSorted (fun y => m' (prioA y)) xs := by
  intro xs hq
  have hq0 := queue_same hT h h' hq
  exact prioSorted_congr (hsort xs hq0) fun y hy => hpr y (hq.mem y hy)

end

/-! ## The spec side -/

section Spec
open Fl4Spec

theorem sendIpc_noblock {σ : State Unit} {e : ObjRef} {x : Endpoint} (hk : σ.kheap e = some (.endpoint x))
    (hc : CanBlock false x) (call : Bool) (badge : Badge) (g gr d : Bool) (t : ObjRef) :
    sendIpc (Z := Unit) false call badge g gr d t e σ = ({((), σ)}, False) := by
  unfold sendIpc
  rw [nd_bind_one (getEndpoint_eq hk)]
  cases x with
  | idleEP => rfl
  | sendEP q => rfl
  | recvEP q => simp [CanBlock] at hc

theorem sendIpc_block {σ : State Unit} {e : ObjRef} {x : Endpoint} (hk : σ.kheap e = some (.endpoint x))
    (hc : CanBlock false x) (call : Bool) (badge : Badge) (g gr d : Bool) (t : ObjRef) :
    sendIpc (Z := Unit) true call badge g gr d t e σ = sendIpcBlocked t e badge g gr call σ := by
  unfold sendIpc
  rw [nd_bind_one (getEndpoint_eq hk)]
  cases x with
  | idleEP => rfl
  | sendEP q => rfl
  | recvEP q => simp [CanBlock] at hc

end Spec

/-! ## `send_ipc` -/

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

theorem stOf_ep {m : U64 → U64} {e : U64} {x : Fl4Spec.Endpoint} (h : EpObjRel m T e x) :
    stOf m e = (match x with | .idleEP => 0#u64 | .sendEP _ => 1#u64 | .recvEP _ => 2#u64) := by
  cases x <;> exact h.1

theorem flags_eq (g gr c : Bool) :
    ((if g then endpoint.FLAG_GRANT else 0#u64) ||| (if gr then endpoint.FLAG_GRANT_REPLY else 0#u64)) |||
      (if c then endpoint.FLAG_CALL else 0#u64) =
    flagsOf { senderBadge := 0, senderCanGrant := g, senderCanGrantReply := gr, senderIsCall := c } := by
  unfold endpoint.FLAG_GRANT endpoint.FLAG_GRANT_REPLY endpoint.FLAG_CALL flagsOf; rfl

/-- A write to a written field of a TCB stays in `EWrite`. -/
theorem wr_ewrite {t b : U64} (ht : t ∈ T) (hb : TWF t b) (hal : Aligned b) (s : S) (v : U64) :
    WritesIn st s (L.wr s b v) (EWrite T E R B) :=
  (writesIn_wr hal).mono fun c hc => by subst hc; exact Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl hb⟩))

theorem twf_of {t b : U64} (k : Nat) (hv : b.val = t.val + k) (hk : TWOffN k) : TWF t b :=
  ⟨by omega, by rw [hv, Nat.add_sub_cancel_left]; exact hk⟩

/-- Two writes to distinct aligned words. -/
theorem agree_wr2 {s : S} {a b v w : U64} (ha : Aligned a) (hb : Aligned b) :
    Agree (L.mem s) (L.mem (L.wr (L.wr s a v) b w)) (fun c => c.val ≠ a.val ∧ c.val ≠ b.val) :=
  ((agree_wr (L := L) (s := s) (v := v) ha).mono fun _ h => h.1).trans
    ((agree_wr (L := L) (s := L.wr s a v) (v := w) hb).mono fun _ h => h.2)

/-- The four writes of a blocking send. -/
theorem block_send_writes (hP : EPlaced T E R B) (s : S) {t : U64} (ht : t ∈ T) (e badge f : U64) :
    let s4 := L.wr (L.wr (L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_SEND) (tBlockA t) e) (tBadgeA t) badge)
      (tFlagsA t) f
    Agree (L.mem s) (L.mem s4) (fun b => b.val ≠ t.val + 3328 ∧ b.val ≠ t.val + 3336 ∧ b.val ≠ t.val + 3344 ∧
        b.val ≠ t.val + 3352) ∧
      L.mem s4 (tStA t) = sched.TS_BLOCKED_ON_SEND ∧ L.mem s4 (tBlockA t) = e ∧ L.mem s4 (tBadgeA t) = badge ∧
      L.mem s4 (tFlagsA t) = f ∧ WritesIn st s s4 (EWrite T E R B) := by
  intro s4
  have hta := hP.tcb t ht
  have a1 := (a_st hta).1; have a2 := (a_blk hta).1; have a3 := (a_badge hta).1; have a4 := (a_flags hta).1
  have v1 := val_st hta; have v2 := val_blk hta; have v3 := val_badge hta; have v4 := val_flags hta
  have g1 := agree_wr2 (L := L) (s := s) (v := sched.TS_BLOCKED_ON_SEND) (w := e) a1 a2
  have g2 := agree_wr2 (L := L) (s := L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_SEND) (tBlockA t) e)
    (v := badge) (w := f) a3 a4
  refine ⟨(g1.mono fun b hb => ?_).trans (g2.mono fun b hb => ?_), ?_, ?_, ?_, ?_, ?_⟩
  · rw [v1, v2]; omega
  · rw [v3, v4]; omega
  · show L.mem (L.wr (L.wr (L.wr (L.wr s _ _) _ _) _ _) _ _) _ = _
    rw [L.mem_wr_ne a4 a1 (by omega), L.mem_wr_ne a3 a1 (by omega), L.mem_wr_ne a2 a1 (by omega),
      L.mem_wr_same a1]
  · show L.mem (L.wr (L.wr (L.wr (L.wr s _ _) _ _) _ _) _ _) _ = _
    rw [L.mem_wr_ne a4 a2 (by omega), L.mem_wr_ne a3 a2 (by omega), L.mem_wr_same a2]
  · show L.mem (L.wr (L.wr (L.wr (L.wr s _ _) _ _) _ _) _ _) _ = _
    rw [L.mem_wr_ne a4 a3 (by omega), L.mem_wr_same a3]
  · exact L.mem_wr_same a4
  · refine (((wr_ewrite (E := E) (R := R) (B := B) ht (twf_of 3328 v1 (by unfold TWOffN; omega)) a1 s _).trans
      (wr_ewrite (E := E) (R := R) (B := B) ht (twf_of 3336 v2 (by unfold TWOffN; omega)) a2 _ _)).trans
      ((wr_ewrite (E := E) (R := R) (B := B) ht (twf_of 3344 v3 (by unfold TWOffN; omega)) a3 _ _).trans
      (wr_ewrite (E := E) (R := R) (B := B) ht (twf_of 3352 v4 (by unfold TWOffN; omega)) a4 _ _))).mono fun b hb => ?_
    rcases hb with (hb | hb) | (hb | hb) <;> exact hb

theorem flag_ite (b : Bool) (v : U64) : (if b then ok v else ok 0#u64 : Result U64) = ok (if b then v else 0#u64) := by
  cases b <;> rfl

/-- **Blocking send** on an idle endpoint or one with waiting senders. -/
theorem send_ipc_block (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock false x)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (call : Bool) (badge : U64) (g gr d : Bool) :
    endpoint.send_ipc st ar s a true call badge g gr d t e ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.sendIpc (Z := Unit) true call badge.bv g gr d t.bv e.bv σ = ({((), σ')}, False) ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hta := hP.tcb t ht
  have hq := not_queued hR ht hkt hnb
  have htq : t.bv ∉ x.epQueue := hq e he x hk
  set d' : Fl4Spec.SenderPayload :=
    { senderBadge := badge.bv, senderCanGrant := g, senderCanGrantReply := gr, senderIsCall := call }
  set x1 : Fl4Spec.Tcb := { xt with tcbState := .blockedOnSend e.bv d' }
  set σ1 := updK σ t.bv (.tcb x1)
  set f := ((if g then endpoint.FLAG_GRANT else 0#u64) ||| (if gr then endpoint.FLAG_GRANT_REPLY else 0#u64)) |||
      (if call then endpoint.FLAG_CALL else 0#u64) with hf
  set s4 := L.wr (L.wr (L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_SEND) (tBlockA t) e) (tBadgeA t) badge)
      (tFlagsA t) f
  obtain ⟨hA4, r1, r2, r3, r4, hW4⟩ := block_send_writes (L := L) hP s ht e badge f
  have v1 := val_st hta; have v2 := val_blk hta; have v3 := val_badge hta; have v4 := val_flags hta
  have hR1 : EpStateRel T E R B (L.mem s4) σ1 := by
    refine hR.upd_tcb hP ht x1 (hA4.mono fun b hb => ?_) (Or.inl hq) ?_
    · have n1 : b.val ≠ (tStA t).val := fun h => hb.2 (TF.of_val (a_st hta).2 h)
      have n2 : b.val ≠ (tBlockA t).val := fun h => hb.2 (TF.of_val (a_blk hta).2 h)
      have n3 : b.val ≠ (tBadgeA t).val := fun h => hb.2 (TF.of_val (a_badge hta).2 h)
      have n4 : b.val ≠ (tFlagsA t).val := fun h => hb.2 (TF.of_val (a_flags hta).2 h)
      omega
    refine hxt.restate hta (hA4.mono fun b hb => ?_) rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_
    · have := hb.2; omega
    · rw [r1]; unfold sched.TS_BLOCKED_ON_SEND; rfl
    · intro e' h; simp only [x1, Fl4Spec.epBlocked, Option.some.injEq] at h; subst h; rw [r2]
    · intro e' d'' h
      simp only [x1, Fl4Spec.ThreadState.blockedOnSend.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨by rw [r3], by rw [r4, hf, flags_eq]; rfl⟩
    · intro e' r d'' h; simp [x1] at h
    · intro r h; simp [x1] at h
  have hS1 : EpStep σ σ1 := EpStep.tcb hkt _ xt.tcbArch
  have hSR1 := hH.stable _ _ _ _ hSR hW4 hS1
  set σ2 := stsAct σ1 t.bv
  have hnt : e.bv ≠ t.bv := kheap_ne hk hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hk2 : σ2.kheap e.bv = some (.endpoint x) := by simp [σ2, σ1, stsAct_kheap, hnt, hk]
  have hkt2 : σ2.kheap t.bv = some (.tcb x1) := by simp [σ2, σ1, stsAct_kheap]
  have hspec : Fl4Spec.sendIpc (Z := Unit) true call badge.bv g gr d t.bv e.bv σ =
      Fl4Spec.tcbEpAppend t.bv e.bv false σ2 := by
    rw [sendIpc_block hk hc]
    unfold Fl4Spec.sendIpcBlocked
    rw [nd_bind_one (setThreadState_eq _ hkt)]
  have key : (do
      let s1 ← obj.Tcb.set_state st t s sched.TS_BLOCKED_ON_SEND
      let s2 ← obj.Tcb.set_block_obj st t s1 e
      let s3 ← obj.Tcb.set_block_badge st t s2 badge
      let i ← ok (if g = true then endpoint.FLAG_GRANT else 0#u64)
      let i1 ← ok (if gr = true then endpoint.FLAG_GRANT_REPLY else 0#u64)
      let i2 ← lift (i ||| i1)
      let i3 ← ok (if call = true then endpoint.FLAG_CALL else 0#u64)
      let f ← lift (i2 ||| i3)
      let s4 ← obj.Tcb.set_block_flags st t s3 f
      let s5 ← sched.schedule_tcb st s4 t
      let s6 ← endpoint.ep_append st s5 e t obj.EP_SEND
      ok (s6, a)) ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.sendIpc (Z := Unit) true call badge.bv g gr d t.bv e.bv σ = ({((), σ')}, False) ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
    step; step; step
    simp only [lift]
    step
    subst s1_post s2_post s3_post i2_post
    refine WP.spec_bind (hH.scheduleTcb _ σ1 t hR1 hSR1 ht) ?_
    rintro s5 ⟨hf5, hS5⟩
    have hR2 : EpStateRel T E R B (L.mem s5) σ2 := hR1.frame hP hf5 (KView.stsAct' _ _)
    have hpr : ∀ y ∈ T, L.mem s5 (prioA y) = L.mem s (prioA y) := by
      intro y hy
      have hya := hP.tcb y hy
      rw [hf5 _ (a_prio hya).1 (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl (a_prio hya).2⟩)))]
      refine hA4 _ (a_prio hya).1 ?_
      have := val_prio hya
      by_cases eyt : y = t
      · subst eyt; omega
      · have := tcb_disj hP ht hy eyt; omega
    have hsort5 := sorted_transfer hP.tcb hx (hR2.at_ep he hk2) hpr hsort
    have htst : (L.mem s5 (tStA t)).val = if false = true then 3 else 4 := by
      rw [hf5 _ (a_st hta).1 (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl (a_st hta).2⟩))), r1]
      unfold sched.TS_BLOCKED_ON_SEND; rfl
    have htb : L.mem s5 (tBlockA t) = e := by
      rw [hf5 _ (a_blk hta).1 (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl (a_blk hta).2⟩))), r2]
    have happ := ep_append_rel hH hP s5 σ2 hR2 hS5 ht hkt2 he hk2 false hc htq htst htb hsort5
    simp only [Bool.false_eq_true, ↓reduceIte] at happ
    refine WP.spec_bind happ ?_
    rintro s6 ⟨σ', hσ', hR', hS'⟩
    simp only [WP.spec_ok]
    exact ⟨by simp, σ', by rw [hspec]; exact hσ', hR', hS'⟩
  unfold endpoint.send_ipc
  step
  rw [st_post, epState_eq]
  cases x with
  | idleEP =>
    rw [hx.1, if_pos ep_state_vals.1.symm]
    simp only [↓reduceIte, flag_ite]
    exact key
  | sendEP q =>
    rw [hx.1, if_neg (by rw [ep_state_vals.1]; decide), if_pos ep_state_vals.2.1.symm]
    simp only [↓reduceIte, flag_ite]
    exact key
  | recvEP q => simp [CanBlock] at hc

/-- **Non-blocking send** on an idle endpoint or one with waiting senders:
nothing happens. -/
theorem send_ipc_noblock (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock false x) (call : Bool) (badge : U64) (g gr d : Bool) (t : U64) :
    endpoint.send_ipc st ar s a false call badge g gr d t e ⦃ r => r = (s, a) ∧
      Fl4Spec.sendIpc (Z := Unit) false call badge.bv g gr d t.bv e.bv σ = ({((), σ)}, False) ⦄ := by
  have hx := hR.at_ep he hk
  have hspec := sendIpc_noblock hk hc call badge.bv g gr d t.bv
  unfold endpoint.send_ipc
  step
  rw [st_post, epState_eq]
  cases x with
  | idleEP =>
    rw [hx.1, if_pos ep_state_vals.1.symm]
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨trivial, hspec⟩
  | sendEP q =>
    rw [hx.1, if_neg (by rw [ep_state_vals.1]; decide), if_pos ep_state_vals.2.1.symm]
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨trivial, hspec⟩
  | recvEP q => simp [CanBlock] at hc

end

end

end Fl4Proofs.P3.Endp
