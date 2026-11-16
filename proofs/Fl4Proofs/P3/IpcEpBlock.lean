/-
P3 (DESIGN.md §9), IPC: **the endpoint theorems outside the transfer bundle,
on the merged relation**: polling receive, blocking send, blocking receive
(the `_comb` proofs of TcbRel.lean and EpComb.lean with `Ipc.IpcSchedHyps` for
`CombHyps`, for `SRS T SR`: the `_i` theorems), and the non-blocking send.
The `XI` theorems restate them over `Ipc.IpcRel` and `SR`.
-/
import Fl4Proofs.P3.IpcEpSteps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

theorem receive_ipc_poll_i (hH0 : Ipc.IpcSchedHyps st ar N T E R B SR) (hP0 : Ipc.IPlaced N T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hRC : CombRel N T E R B (L.mem s) σ) (hSR : SRS st T SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hbn : xt.tcbBoundNotification = none)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock true x) (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) false rc ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ = ({((), σ')}, False) ∧
        CombRel N T E R B (L.mem r.1) σ' ∧ SRS st T SR r.1 σ' ⦄ := by
  have hR := hRC.2
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hbound : L.mem s (tBoundA t) = 0#u64 := optRef_none (hxt.bound.symm.trans hbn)
  have hns : ∀ q, x ≠ .sendEP q := fun q h => by subst h; simp [CanBlock] at hc
  have hspec0 := receiveIpc_noSend b rights false (replyArg_spec hP0.e hR hrc) hkt hbn hk hns
  obtain ⟨hR1, hW1, hS1⟩ := write_reg_rel hP0.e s σ hR ht hkt Fl4Spec.badge_register 0#u64
  obtain ⟨hN1, -, -⟩ := set_badge_reg_rel (L := L) hP0.n hRC.1 ht hkt 0#u64
  rw [badgeRegA_eq_regA] at hN1
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
        CombRel N T E R B (L.mem r.1) σ' ∧ SRS st T SR r.1 σ' ⦄ := by
    unfold endpoint.wait_for_sender
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← regIdx_badge]
    step as ⟨s1', h1⟩
    subst h1
    exact ⟨_, hspec, ⟨hN1, hR1⟩, (hH0.epHyps hP0).stable _ _ _ _ hSR hW1 hS1⟩
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


theorem send_ipc_block_i (hH0 : Ipc.IpcSchedHyps st ar N T E R B SR) (hP0 : Ipc.IPlaced N T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hRC : CombRel N T E R B (L.mem s) σ) (hSR : SRS st T SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4)
    (hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock false x)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (call : Bool) (badge : U64) (g gr d : Bool) :
    endpoint.send_ipc st ar s a true call badge g gr d t e ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.sendIpc (Z := Unit) true call badge.bv g gr d t.bv e.bv σ = ({((), σ')}, False) ∧
        CombRel N T E R B (L.mem r.1) σ' ∧ SRS st T SR r.1 σ' ⦄ := by
  have hH := hH0.epHyps hP0
  have hP := hP0.e
  have hR := hRC.2
  have hN := hRC.1
  have hqn := not_member hN ht hkt hnn
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
  have hN1 : NtfnStateRel N T (L.mem s4) σ1 := by
    have hxt1 := hN.at_tcb ht hkt
    have g4 : ∀ b, Aligned b → (b.val < t.val + 3328 ∨ t.val + 3360 ≤ b.val) → L.mem s4 b = L.mem s b :=
      fun b hb hv => hA4 b hb (by omega)
    refine ntfn_upd_fields hP0.toC hN ht x1 (fun b hb hv => hA4 b hb ?_) hqn ⟨?_, ?_, ?_, ?_⟩
    · omega
    · rw [r1]; unfold sched.TS_BLOCKED_ON_SEND; rfl
    · intro n h; simp [x1] at h
    · show (L.mem s4 (badgeRegA t)).bv = badgeOf xt
      rw [g4 _ (by rw [badgeRegA_eq_regA]; exact (a_reg hta _).1) (by
        rw [badgeRegA_eq, tw_val hta (by simp)]; left; simp)]
      exact hxt1.badge
    · show (L.mem s4 (prioA t)).val = xt.tcbPriority.toNat
      rw [g4 _ (a_prio hta).1 (by rw [val_prio hta]; omega)]
      exact hxt1.prio
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
        CombRel N T E R B (L.mem r.1) σ' ∧ SRS st T SR r.1 σ' ⦄ := by
    step; step; step
    simp only [lift]
    step
    subst s1_post s2_post s3_post i2_post
    simp only [show ∀ u, Fl4Proofs.P3.stA u = tStA u from fun _ => rfl,
      show ∀ u, Fl4Proofs.P1.stA u = tStA u from fun _ => rfl]
    refine WP.spec_bind (hH0.schedC hP0 _ σ1 t (by exact hR1) (by exact hSR1) ht) ?_
    rintro s5 ⟨hf5, hfN5, hS5⟩
    have hN2 : NtfnStateRel N T (L.mem s5) σ2 := hN1.frame hP0.n hfN5 (Notif.KView.stsAct _ _)
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
    obtain ⟨xs, hQ, hxs, hB⟩ := (hR2.at_ep he hk2).queue
    have htxs : t ∉ xs := fun h => htq (by rw [hxs]; exact List.mem_map_of_mem h)
    have hqa := WP.spec_mono (ep_append_full hP s5 he t obj.EP_SEND xs hQ ht htxs) fun _ h => h.2.2.1
    refine WP.spec_bind (WP.spec_and happ hqa) ?_
    rintro s6 ⟨⟨σ', hσ', hR', hS'⟩, hQA⟩
    -- the spec's append only changes the endpoint
    have hq2 : ∀ y ∈ x.epQueue, ∃ z, σ2.kheap y = some (.tcb z) ∧ z.tcbPriority = prioOf σ2 y := by
      intro y hy
      rw [hxs] at hy
      obtain ⟨y', hy'x, rfl⟩ := List.mem_map.1 hy
      obtain ⟨z, hz, -⟩ := hR2.tcb y' (hQ.mem y' hy'x)
      exact ⟨z, hz, by simp [prioOf, hz]⟩
    rw [tcbEpAppend_eq hk2 hkt2 (prioOf σ2) hq2] at hσ'
    have hσe : σ' = updK σ2 e.bv (.endpoint (Fl4Spec.updateEpQueue x
        (specIns x.epQueue (prioOf σ2) x1.tcbPriority t.bv) false)) := by
      have := congrArg Prod.fst hσ'
      simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
      exact this.symm
    have hkv : Notif.KView σ2 σ' := by
      rw [hσe]
      refine ⟨fun p y h => ?_, fun p y h => ⟨y, ?_, rfl, rfl, rfl⟩⟩
      · have : p ≠ e.bv := by intro h'; rw [h', hk2] at h; cases h
        simp [this, h]
      · have : p ≠ e.bv := by intro h'; rw [h', hk2] at h; cases h
        simp [this, h]
    have hW : ∀ w ∈ t :: xs, w ∈ T ∧ (L.mem s5 (tStA w)).val ≠ 6 := by
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ⟨ht, by rw [htst]; simp⟩
      · exact ⟨hQ.mem w hw, by rcases (hB w hw).2 with h | h <;> rw [h] <;> simp⟩
    have hN3 := ntfn_frame_ep hP0.toC hN2 he hW hQA hkv
    simp only [WP.spec_ok]
    exact ⟨by simp, σ', by rw [hspec, tcbEpAppend_eq hk2 hkt2 (prioOf σ2) hq2, hσe], ⟨hN3, hR'⟩, hS'⟩
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


theorem receive_ipc_block_i (hH0 : Ipc.IpcSchedHyps st ar N T E R B SR) (hP0 : Ipc.IPlaced N T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hRC : CombRel N T E R B (L.mem s) σ) (hSR : SRS st T SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    (hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock true x)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) true rc ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ = ({((), σ')}, False) ∧
        CombRel N T E R B (L.mem r.1) σ' ∧ SRS st T SR r.1 σ' ⦄ := by
  have hH := hH0.epHyps hP0
  have hP := hP0.e
  have hR := hRC.2
  have hN := hRC.1
  have hqn := not_member hN ht hkt hnn
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
  have hN1 : NtfnStateRel N T (L.mem s3) σ1 := by
    have hxt1 := hN.at_tcb ht hkt
    have g3 : ∀ b, Aligned b → (b.val < t.val + 3328 ∨ t.val + 3368 ≤ b.val) → L.mem s3 b = L.mem s b :=
      fun b hb hv => hA3 b hb (by omega)
    refine ntfn_upd_fields hP0.toC hN ht x1 g3 hqn ⟨?_, ?_, ?_, ?_⟩
    · rw [r1]; unfold sched.TS_BLOCKED_ON_RECV; rfl
    · intro n h; simp [x1] at h
    · show (L.mem s3 (badgeRegA t)).bv = badgeOf xt
      rw [g3 _ (by rw [badgeRegA_eq_regA]; exact (a_reg hta _).1) (by
        rw [badgeRegA_eq, tw_val hta (by simp)]; left; simp)]
      exact hxt1.badge
    · show (L.mem s3 (prioA t)).val = xt.tcbPriority.toNat
      rw [g3 _ (a_prio hta).1 (by rw [val_prio hta]; omega)]
      exact hxt1.prio
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
        CombRel N T E R B (L.mem r.1) σ' ∧ SRS st T SR r.1 σ' ⦄ := by
    unfold endpoint.wait_for_sender
    simp only [↓reduceIte]
    step as ⟨s1', h1⟩
    step as ⟨s2', h2⟩
    step as ⟨s3', h3⟩
    subst h1 h2 h3
    simp only [show ∀ u, Fl4Proofs.P3.stA u = tStA u from fun _ => rfl,
      show ∀ u, Fl4Proofs.P1.stA u = tStA u from fun _ => rfl]
    refine WP.spec_bind (hH0.schedC hP0 _ σ1 t (by exact hR1) (by exact hSR1) ht) ?_
    rintro s4 ⟨hf4, hfN4, hS4⟩
    have hR2 : EpStateRel T E R B (L.mem s4) σ2 := hR1.frame hP hf4 (KView.stsAct' _ _)
    have hN2 : NtfnStateRel N T (L.mem s4) σ2 := hN1.frame hP0.n hfN4 (Notif.KView.stsAct _ _)
    have hfoot : ∀ {a'}, Aligned a' ∧ TF t a' → L.mem s4 a' = L.mem s3 a' := fun h =>
      hf4 _ h.1 (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl h.2⟩)))
    have hprio4 : ∀ y ∈ T, L.mem s4 (prioA y) = L.mem s (prioA y) := fun y hy => by
      have hya := hP.tcb y hy
      rw [hf4 _ (a_prio hya).1 (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl (a_prio hya).2⟩))), hprio3 y hy]
    have tail : ∀ (s5 : S) (σ3 : Fl4Spec.State Unit), EpStateRel T E R B (L.mem s5) σ3 →
        NtfnStateRel N T (L.mem s5) σ3 → SRS st T SR s5 σ3 →
        σ3.kheap e.bv = some (.endpoint x) → σ3.kheap t.bv = some (.tcb x1) →
        (∀ y ∈ T, L.mem s5 (prioA y) = L.mem s (prioA y)) →
        L.mem s5 (tStA t) = sched.TS_BLOCKED_ON_RECV → L.mem s5 (tBlockA t) = e →
        (Fl4Spec.NonDet.maybeM (fun r => Fl4Spec.setReplyObjRef Fl4Spec.replyTcbUpdate r (some t.bv)) (optRef rv) σ2 =
          ({((), σ3)}, False)) →
        (do
          let s6 ← endpoint.ep_append st s5 e t obj.EP_RECV
          ok (s6, a)) ⦃ r => r.2 = a ∧
          ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ =
            ({((), σ')}, False) ∧ CombRel N T E R B (L.mem r.1) σ' ∧ SRS st T SR r.1 σ' ⦄ := by
      intro s5 σ3 hR3 hN3 hS3 hk3 hkt3 hpr5 hst5 hb5 hm
      have hsort5 := sorted_transfer hP.tcb hx (hR3.at_ep he hk3) hpr5 hsort
      have htst : (L.mem s5 (tStA t)).val = if true = true then 3 else 4 := by
        rw [hst5]; unfold sched.TS_BLOCKED_ON_RECV; rfl
      have happ := ep_append_rel hH hP s5 σ3 hR3 hS3 ht hkt3 he hk3 true hc htq htst hb5 hsort5
      simp only [↓reduceIte] at happ
      obtain ⟨xs, hQ, hxs, hB⟩ := (hR3.at_ep he hk3).queue
      have htxs : t ∉ xs := fun h => htq (by rw [hxs]; exact List.mem_map_of_mem h)
      have hqa := WP.spec_mono (ep_append_full hP s5 he t obj.EP_RECV xs hQ ht htxs) fun _ h => h.2.2.1
      refine WP.spec_bind (WP.spec_and happ hqa) ?_
      rintro s6 ⟨⟨σ', hσ', hR', hS'⟩, hQA⟩
      have hq3 : ∀ y ∈ x.epQueue, ∃ z, σ3.kheap y = some (.tcb z) ∧ z.tcbPriority = prioOf σ3 y := by
        intro y hy
        rw [hxs] at hy
        obtain ⟨y', hy'x, rfl⟩ := List.mem_map.1 hy
        obtain ⟨z, hz, -⟩ := hR3.tcb y' (hQ.mem y' hy'x)
        exact ⟨z, hz, by simp [prioOf, hz]⟩
      have hσ2 := hσ'
      rw [tcbEpAppend_eq hk3 hkt3 (prioOf σ3) hq3] at hσ2
      have hσe : σ' = updK σ3 e.bv (.endpoint (Fl4Spec.updateEpQueue x
          (specIns x.epQueue (prioOf σ3) x1.tcbPriority t.bv) true)) := by
        have := congrArg Prod.fst hσ2
        simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
        exact this.symm
      have hkv : Notif.KView σ3 σ' := by
        rw [hσe]
        refine ⟨fun p y h => ?_, fun p y h => ⟨y, ?_, rfl, rfl, rfl⟩⟩
        · have : p ≠ e.bv := by intro h'; rw [h', hk3] at h; cases h
          simp [this, h]
        · have : p ≠ e.bv := by intro h'; rw [h', hk3] at h; cases h
          simp [this, h]
      have hW : ∀ w ∈ t :: xs, w ∈ T ∧ (L.mem s5 (tStA w)).val ≠ 6 := by
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact ⟨ht, by rw [htst]; simp⟩
        · exact ⟨hQ.mem w hw, by rcases (hB w hw).2 with h | h <;> rw [h] <;> simp⟩
      have hN' := ntfn_frame_ep hP0.toC hN3 he hW hQA hkv
      simp only [WP.spec_ok]
      exact ⟨by simp, σ', by rw [hspec, nd_bind_one hm]; exact hσ', ⟨hN', hR'⟩, hS'⟩
    by_cases h0 : rv = 0#u64
    · simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      apply ok_bind_spec
      refine tail s4 σ2 hR2 hN2 hS4 hk2 hkt2 hprio4 ?_ ?_ (by rw [h0, optRef_zero]; rfl)
      · rw [hfoot (a_st hta), r1]
      · rw [hfoot (a_blk hta), r2]
    · have hne : (rv != 0#u64) = true := by simp [h0]
      simp only [hne, ↓reduceIte]
      obtain ⟨hrR, -⟩ := replyArg_ne hP hrc h0
      obtain ⟨xr, hkr, -⟩ := hR2.reply rv hrR
      obtain ⟨e1, hR5, hS5, hA5⟩ := reply_link_rel hH hP s4 σ2 hR2 hS4 hrR hkr hta
      have hN5 := ntfn_reply_write hP0.toC hN2 hrR hA5 hkr { xr with replyTcb := some t.bv }
      step as ⟨s6', h6⟩
      subst h6
      have hnr : rv.bv ≠ e.bv := kheap_ne hkr hk2 (fun _ h1 h2 => by subst h1; cases h2)
      have hnr' : rv.bv ≠ t.bv := kheap_ne hkr hkt2 (fun _ h1 h2 => by subst h1; cases h2)
      have hdis := hP.rt rv hrR t ht
      refine tail _ _ hR5 hN5 hS5 (by simp [Ne.symm hnr, hk2]) (by simp [Ne.symm hnr', hkt2]) ?_ ?_ ?_ ?_
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


/-- **Polling receive** on an endpoint with no sender, on the merged relation. -/
theorem receive_ipc_pollI (hH : Ipc.IpcSchedHyps st ar N T E R B SR) (hP : Ipc.IPlaced N T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : Ipc.IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hbn : xt.tcbBoundNotification = none)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock true x) (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) false rc ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ = ({((), σ')}, False) ∧
        Ipc.IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  WP.spec_mono (receive_ipc_poll_i hH hP s a σ ⟨hR.toN, hR.toE⟩ ⟨hSR, Ipc.ScRelM.of hR⟩ ht hkt hbn he hk hc cb c1 c2 c3 c4
    hrc b rights) fun _ ⟨h1, σ', h2, h3, h4⟩ => ⟨h1, σ', h2, Ipc.IpcRel.of h3.1 h3.2 h4.2.all, h4.1⟩

/-- **Blocking send**, on the merged relation. -/
theorem send_ipc_blockI (hH : Ipc.IpcSchedHyps st ar N T E R B SR) (hP : Ipc.IPlaced N T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : Ipc.IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4)
    (hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock false x)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (call : Bool) (badge : U64) (g gr d : Bool) :
    endpoint.send_ipc st ar s a true call badge g gr d t e ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.sendIpc (Z := Unit) true call badge.bv g gr d t.bv e.bv σ = ({((), σ')}, False) ∧
        Ipc.IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  WP.spec_mono (send_ipc_block_i hH hP s a σ ⟨hR.toN, hR.toE⟩ ⟨hSR, Ipc.ScRelM.of hR⟩ ht hkt hnb hnn he hk hc hsort call
    badge g gr d) fun _ ⟨h1, σ', h2, h3, h4⟩ => ⟨h1, σ', h2, Ipc.IpcRel.of h3.1 h3.2 h4.2.all, h4.1⟩

/-- **Blocking receive** on an idle endpoint or one with waiting receivers,
on the merged relation. -/
theorem receive_ipc_blockI (hH : Ipc.IpcSchedHyps st ar N T E R B SR) (hP : Ipc.IPlaced N T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : Ipc.IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    (hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock true x)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) true rc ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ = ({((), σ')}, False) ∧
        Ipc.IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  WP.spec_mono (receive_ipc_block_i hH hP s a σ ⟨hR.toN, hR.toE⟩ ⟨hSR, Ipc.ScRelM.of hR⟩ ht hkt hnb hbn hnn he hk hc hsort
    cb c1 c2 c3 c4 hrc b rights) fun _ ⟨h1, σ', h2, h3, h4⟩ => ⟨h1, σ', h2, Ipc.IpcRel.of h3.1 h3.2 h4.2.all, h4.1⟩

/-- **Non-blocking send** with no receiver, on the merged relation: nothing
changes. -/
theorem send_ipc_noblockI (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : Ipc.IpcRel N T E R B (L.mem s) σ)
    (hSR : SR s σ) {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock false x) (call : Bool) (badge : U64) (g gr d : Bool) (t : U64) :
    endpoint.send_ipc st ar s a false call badge g gr d t e ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.sendIpc (Z := Unit) false call badge.bv g gr d t.bv e.bv σ = ({((), σ')}, False) ∧
        Ipc.IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  WP.spec_mono (send_ipc_noblock (ar := ar) s a σ hR.toE he hk hc call badge g gr d t) fun r ⟨h1, h2⟩ => by
    subst h1; exact ⟨rfl, σ, h2, hR, hSR⟩

end

end

end Fl4Proofs.P3.Endp
