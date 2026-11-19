/-
P3 (DESIGN.md §9), IPC: **`receive_ipc`'s blocking wait with no reply cap at
`J`** (KENTRY-PLAN.md item 6 (b), part): the current thread, runnable,
resumed and in no ready queue, with no bound notification and a null reply
cap, blocks receiving on an idle or receiving endpoint
(`JAtZ.recvIpcBlock0J`), from `JAtZ` before to `JAtZ` after. The receive
analogue of XTopJointSendBlock's `JAtZ.sendBlockJ`.

* P1's footprint `endpoint.wait_for_sender.foot0` (`Foot`, as
  `send_block.foot`; the reply word written with 0, no reply object).
* FL4's side on `IRel`: `wait_for_sender_blockF0` (as `send_ipc_blockF`,
  the writes of EpRecv's `receive_ipc_block`), footprint `CnW`;
  `receive_ipc_block0_red` reduces `receive_ipc` to it (EpRecv's
  `receive_ipc_pre`).
* The spec's side: `recvIpcBlock0_eq` (the outcome, explicit), the frame
  `BFrR t e` (`t`'s TCB from a runnable state to `blockedOnReceive e none`,
  `e`'s endpoint queue grown; copies of XTopJointSendBlock's `BFr` lemmas)
  and `IK` of the step.
* `RRecv` after (`RRecv.frameR`): the only new receive-blocked thread is
  `t`, and no reply names `t` before (`SchedValid.replyTcb`: a reply's
  thread is blocked on reply or receiving, `t` is runnable).
-/
import Fl4Proofs.P3.XTopJointRecvIpcAct
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
  {Q : U64 → U64 → List U64} {R : U64 → List U64}

set_option maxHeartbeats 4000000 in
/-- **The blocking wait's footprint** with no reply object. -/
theorem endpoint.wait_for_sender.foot0 (s : S) (t e : U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hc : CanBlock st T Ac s t) (hH : H e = some .ep) :
    endpoint.wait_for_sender st s t e true 0#u64 ⦃ s' => Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have ht := hc.mem
  have hta := h.tcbs t ht
  have hN := h.nodes _ h.cur
  unfold endpoint.wait_for_sender
  simp only [↓reduceIte]
  step with obj.Tcb.set_state.spec as ⟨s1, e1⟩
  step with obj.Tcb.set_block_obj.wr as ⟨s2, e2⟩
  step with obj.Tcb.set_reply_obj.wr as ⟨s3, e3⟩
  have h1 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s1 Q R := by
    rw [e1]; exact blk_set_state h hc
  have h2 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s2 Q R := by
    rw [e2]; exact inv_wr_fieldX (K := 3336#u64) h1 ht (Or.inr rfl) (by simp) (by simp) (by simp)
  have h3 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s3 Q R := by
    rw [e3]; exact inv_wr_fieldX (K := 3360#u64) h2 ht (Or.inr rfl) (by simp) (by simp) (by simp)
  rw [stA_eq] at e1
  have w3 : WritesIn st s s3 (BlkFoot st s t 0#u64) := by
    rw [e3, e2, e1]
    exact blk_wr_field (K := 3360#u64) hta (blk_wr_field hta (blk_wr_field hta (WritesIn.refl _ _) (by simp))
      (by simp)) (by simp)
  have v3 : L.mem s3 (stA t) = sched.TS_BLOCKED_ON_RECV := by
    rw [e3, fld_wr_ne' (K := 3360#u64) (a := replyA t) hta rfl (stA_eq t) (by simp) (by simp) (by simp) (by simp)
      (by simp), e2, fld_wr_ne' hta (blockA_eq t) (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp), e1,
      stA_eq]
    exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
  have a3 : L.actionW s3 = L.actionW s := by
    rw [e3, act_wr_field (K := 3360#u64) (a := replyA t) (h2.nodes _ h2.cur) ht hta rfl (by simp) (by simp),
      e2, act_wr_field (h1.nodes _ h1.cur) ht hta (blockA_eq t) (by simp) (by simp),
      e1, act_wr_field hN ht hta rfl (by simp) (by simp)]
  refine WP.spec_bind (sched.schedule_tcb.blk s3 t h3 (by rw [v3]; exact blocked_not_runnable (Or.inr (Or.inl rfl))))
    ?_
  rintro s4 ⟨h4, e4, -⟩
  obtain ⟨w4, -, -, -, -, -⟩ := blk_sched h3 ht w3 a3 e4
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  try simp only [Aeneas.Std.bind_ok]
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have heE : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 (Or.inl hH)
  obtain ⟨hE, -, hq⟩ := hEW.1 e heE
  obtain ⟨kf, -, -, ke⟩ := blkfoot_keep h hEW ht (fun h0 => absurd rfl h0) w4
  have hqe : L.epQ s4 e = L.epQ s e := by simp only [LawfulStore.epQ, (ke e heE).1, (ke e heE).2]
  have hq4 : QueueRel (L.mem s4) T .Ep (L.epQ s4 e) (EQ e) :=
    ⟨hq.nodup, hq.mem, by rw [hqe]; exact hq.head, by rw [hqe]; exact hq.last, hq.seg.congr fun y hy =>
      ⟨kf y (hq.mem y hy) (prevOff .Ep) (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simp [prevOff]),
       kf y (hq.mem y hy) (nextOff .Ep) (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simp [nextOff])⟩⟩
  have hn : t ∉ EQ e := fun hm => hc.nb (hEW.2.2.2.1 e heE t hm).2.2
  refine WP.spec_mono (endpoint.ep_append.foot s4 e t obj.EP_RECV (EQ e) h.tcbs hE hq4 ht hn) fun s6 w6 => ?_
  refine (blkfoot_foot h ht w4).trans (Foot.of w6 fun b hb => hb.kw ?_ (Or.inl hH))
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact hq.mem w hw

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- `receive_ipc` with no bound notification and a null reply cap on an idle
or receiving endpoint: its blocking wait. -/
theorem receive_ipc_block0_red {s : S} {a : A} {t e cb : U64} {c1 c2 c3 c4 : Bool}
    (hbound : L.mem s (tBoundA t) = 0#u64) (hst : stOf (L.mem s) e = 0#u64 ∨ stOf (L.mem s) e = 2#u64)
    {P : S × A → Prop}
    (h : (do
      let s3 ← endpoint.wait_for_sender st s t e true 0#u64
      ok (s3, a)) ⦃ P ⦄) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) true .Null ⦃ P ⦄ := by
  apply receive_ipc_pre (R := ∅) s a t e cb c1 c2 c3 c4 true .Null .nullCap 0#u64 (Or.inl ⟨rfl, rfl, rfl⟩) hbound
  refine WP.spec_bind (P1.obj.Ep.state.spec s e) ?_
  rintro v rfl
  rw [epState_eq]
  rcases hst with h0 | h0
  · rw [h0, if_pos ep_state_vals.1.symm]
    exact h
  · rw [h0, if_neg (by rw [ep_state_vals.1]; decide), if_pos ep_state_vals.2.2.symm]
    exact h

set_option maxHeartbeats 16000000 in
/-- **The blocking wait with no reply object on `IRel`, with its footprint**
(module docstring). -/
theorem wait_for_sender_blockF0 (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4)
    (hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m) (hbn : xt.tcbBoundNotification = none)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : Endp.CanBlock true x)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    (do
      let s3 ← endpoint.wait_for_sender st s t e true 0#u64
      ok (s3, a)) ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true .nullCap σ = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c r.1 σ' ∧ WritesIn st s r.1 (CnW (st := st) T N C E R c s σ) ⦄ := by
  have hH0 := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP0.e
  have hH := hH0.epHyps hP0
  have hP := hP0.e
  obtain ⟨hRI, hSRT⟩ := hX
  have hSchR : SchedRel st N T C c s σ := hSRT.2.1
  obtain ⟨Q0, R0, hc0, -⟩ := hSchR.lists
  have hR := hRI.toE
  have hN := hRI.toN
  have hSR : SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ := ⟨hSRT, ScRelM.of hRI⟩
  have hqn := not_member hN ht hkt hnn
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hta := hP.tcb t ht
  have hq := not_queued hR ht hkt hnb
  have htq : t.bv ∉ x.epQueue := hq e he x hk
  have hns : ∀ q, x ≠ .sendEP q := fun q h => by subst h; simp [Endp.CanBlock] at hc
  have hrc : ReplyArg R (L.mem s) .Null .nullCap 0#u64 := Or.inl ⟨rfl, rfl, rfl⟩
  have hspec0 := receiveIpc_noSend b rights true (replyArg_spec hP hR hrc) hkt hbn hk hns
  set x1 : Fl4Spec.Tcb :=
    { xt with tcbState := .blockedOnReceive e.bv (optRef 0#u64) { receiverCanGrant := false } }
  set σ1 := updK σ t.bv (.tcb x1)
  set s3 := L.wr (L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_RECV) (tBlockA t) e) (tReplyA t) 0#u64
  obtain ⟨hA3, r1, r2, r3, hW3⟩ := block_recv_writes (L := L) hP s ht e 0#u64
  have v1 := val_st hta; have v2 := val_blk hta; have v3 := val_reply hta
  -- the footprint of the three field writes
  have hF3 : WritesIn st s s3 (CnW (st := st) T N C E R c s σ) := by
    refine ⟨hW3.1, hW3.2.1, fun b hb hn => hA3 b hb ⟨fun h => hn ?_, fun h => hn ?_, fun h => hn ?_⟩⟩
    · exact Or.inl (Or.inr ⟨t, ht, 3328, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨t, ht, 3336, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨t, ht, 3360, by omega, by omega, by omega, by omega, by omega, h⟩)
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
      rw [optRef_zero] at hne; exact absurd rfl hne
    · intro r h; simp [x1] at h
  have hN1 : NtfnStateRel N T (L.mem s3) σ1 := by
    have hxt1 := hN.at_tcb ht hkt
    have g3 : ∀ b, Aligned b → (b.val < t.val + 3328 ∨ t.val + 3368 ≤ b.val) → L.mem s3 b = L.mem s b :=
      fun b hb hv => hA3 b hb (by omega)
    refine ntfn_upd_fields hP0.toC hN ht x1 (fun b hb hv => hA3 b hb ?_) hqn ⟨?_, ?_, ?_, ?_⟩
    · omega
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
  have hspec : Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true .nullCap σ =
      Fl4Spec.tcbEpAppend t.bv e.bv true σ2 := by
    rw [hspec0]
    unfold Fl4Spec.receiveIpcBlocked
    rw [if_pos rfl, nd_bind_one (Notif.setThreadState_eq _ hkt), optRef_zero]
    exact nd_pure_bind' _ _ _
  have hprio3 : ∀ y ∈ T, L.mem s3 (prioA y) = L.mem s (prioA y) := by
    intro y hy
    have hya := hP.tcb y hy
    refine hA3 _ (a_prio hya).1 ?_
    have := val_prio hya
    by_cases eyt : y = t
    · subst eyt; omega
    · have := tcb_disj hP ht hy eyt; omega
  -- the action word of a state with `s`'s kernel base and core
  have hactW : ∀ s' : S, L.ksb s' = L.ksb s → L.cpu s' = L.cpu s →
      Aligned (L.nodeAt s' (L.cpu s') layout.node.SCHED_ACTION) ∧
        CnW (st := st) T N C E R c s σ (L.nodeAt s' (L.cpu s') layout.node.SCHED_ACTION) := by
    intro s' hk' hc'
    have hN0 := hc0.node
    have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
    rw [nodeAt_ksb hk', hc', hc0.cur]
    refine ⟨nodeAt_aligned hN0 ho (by simp [layout.node.SCHED_ACTION]), Or.inl (Or.inl (KFoot.of_sfoot (Or.inr ?_)))⟩
    exact ⟨by rw [nodeAt_val hN0 ho]; omega, by rw [nodeAt_val hN0 ho]; omega⟩
  unfold endpoint.wait_for_sender
  simp only [↓reduceIte]
  step as ⟨s1', h1⟩
  step as ⟨s2', h2⟩
  step as ⟨s3', h3⟩
  subst h1 h2 h3
  try simp only [show ∀ u, Fl4Proofs.P3.stA u = tStA u from fun _ => rfl,
    show ∀ u, Fl4Proofs.P1.stA u = tStA u from fun _ => rfl]
  refine WP.spec_bind (WP.spec_and (hH0.schedC hP0 s3 σ1 t (by exact hR1) (by exact hSR1) ht)
    (schedule_tcb_cases s3 t)) ?_
  rintro s4 ⟨⟨hf4, hfN4, hS4⟩, hc4⟩
  have hF4 : WritesIn st s s4 (CnW (st := st) T N C E R c s σ) := by
    rcases hc4 with rfl | rfl
    · exact hF3
    · refine hF3.trans (B := CnW (st := st) T N C E R c s σ) ?_ |>.mono fun b hb => hb.elim id id
      obtain ⟨ha1, ha2⟩ := hactW _ hW3.1 hW3.2.1
      exact (writesIn_wr ha1).mono fun b hb => hb ▸ ha2
  have hN2 : NtfnStateRel N T (L.mem s4) σ2 := hN1.frame hP0.n hfN4 (Notif.KView.stsAct _ _)
  have hR2 : EpStateRel T E R B (L.mem s4) σ2 := hR1.frame hP hf4 (KView.stsAct' _ _)
  have hpr : ∀ y ∈ T, L.mem s4 (prioA y) = L.mem s (prioA y) := by
    intro y hy
    have hya := hP.tcb y hy
    rw [hf4 _ (a_prio hya).1 (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl (a_prio hya).2⟩))), hprio3 y hy]
  have hsort4 := sorted_transfer hP.tcb hx (hR2.at_ep he hk2) hpr hsort
  have htst : (L.mem s4 (tStA t)).val = if true = true then 3 else 4 := by
    rw [hf4 _ (a_st hta).1 (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl (a_st hta).2⟩))), r1]
    unfold sched.TS_BLOCKED_ON_RECV; rfl
  have htb : L.mem s4 (tBlockA t) = e := by
    rw [hf4 _ (a_blk hta).1 (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl (a_blk hta).2⟩))), r2]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  apply ok_bind_spec
  have happ := ep_append_rel hH hP s4 σ2 hR2 hS4 ht hkt2 he hk2 true hc htq htst htb hsort4
  simp only [↓reduceIte] at happ
  obtain ⟨xs, hQ, hxs, hB⟩ := (hR2.at_ep he hk2).queue
  have htxs : t ∉ xs := fun h => htq (by rw [hxs]; exact List.mem_map_of_mem h)
  have hqa := ep_append_full hP s4 he t obj.EP_RECV xs hQ ht htxs
  refine WP.spec_bind (WP.spec_and happ hqa) ?_
  rintro s6 ⟨⟨σ', hσ', hR', hS'⟩, -, -, hQA, hWE⟩
  have hF6 : WritesIn st s s6 (CnW (st := st) T N C E R c s σ) := by
    refine hF4.trans (B := CnW (st := st) T N C E R c s σ) ⟨hWE.1, hWE.2.1, fun b hb hn => hQA b hb
      ⟨fun h => hn (Or.inr (Or.inl ⟨e, he, h⟩)), fun ⟨w, hw, h⟩ => hn ?_⟩⟩ |>.mono fun b hb => hb.elim id id
    have hwT : w ∈ T := by
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ht
      · exact hQ.mem w hw
    rcases h with h | h
    · exact Or.inl (Or.inr ⟨w, hwT, 3496, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨w, hwT, 3504, by omega, by omega, by omega, by omega, by omega, h⟩)
  have hq2 : ∀ y ∈ x.epQueue, ∃ z, σ2.kheap y = some (.tcb z) ∧ z.tcbPriority = Notif.prioOf σ2 y := by
    intro y hy
    rw [hxs] at hy
    obtain ⟨y', hy'x, rfl⟩ := List.mem_map.1 hy
    obtain ⟨z, hz, -⟩ := hR2.tcb y' (hQ.mem y' hy'x)
    exact ⟨z, hz, by simp [Notif.prioOf, hz]⟩
  rw [tcbEpAppend_eq hk2 hkt2 (Notif.prioOf σ2) hq2] at hσ'
  have hσe : σ' = updK σ2 e.bv (.endpoint (Fl4Spec.updateEpQueue x
      (specIns x.epQueue (Notif.prioOf σ2) x1.tcbPriority t.bv) true)) := by
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
  have hW : ∀ w ∈ t :: xs, w ∈ T ∧ (L.mem s4 (tStA w)).val ≠ 6 := by
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ⟨ht, by rw [htst]; simp⟩
    · exact ⟨hQ.mem w hw, by rcases (hB w hw).2 with h | h <;> rw [h] <;> simp⟩
  have hN3 := ntfn_frame_ep hP0.toC hN2 he hW hQA hkv
  simp only [WP.spec_ok]
  exact ⟨by simp, σ', by rw [hspec, tcbEpAppend_eq hk2 hkt2 (Notif.prioOf σ2) hq2, hσe],
    ⟨IpcRel.of hN3 hR' hS'.2.all, hS'.1⟩, hF6⟩

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical


/-- **One object's change by the blocking receive (null reply)**: `t`'s TCB from a runnable
state to `blockedOnReceive`, or `e`'s endpoint. -/
def BChgR (t e p : ObjRef) (o o' : KernelObject) : Prop :=
  (∃ x ep d, o = .tcb x ∧ o' = .tcb { x with tcbState := .blockedOnReceive ep none d } ∧ p = t ∧
    runnable x.tcbState = true) ∨
  (∃ x y, o = .endpoint x ∧ o' = .endpoint y ∧ p = e)

/-- **The spec's frame of the blocking receive (null reply)** (module docstring). -/
structure BFrR (t e : ObjRef) (σ σ' : State Unit) : Prop where
  sk : Sk σ σ'
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ o o', σ.kheap p = some o ∧ σ'.kheap p = some o' ∧ BChgR t e p o o'

section
variable {t e : ObjRef} {σ σ' : State Unit}

/-- A TCB's change: kept, or `t`'s, runnable, to `blockedOnReceive`. -/
def TKbR (t p : ObjRef) (x : Tcb) (st : ThreadState) : Prop :=
  st = x.tcbState ∨ (p = t ∧ runnable x.tcbState = true ∧ ∃ ep d, st = .blockedOnReceive ep none d)

theorem TKbR.run {p : ObjRef} {x : Tcb} {st : ThreadState} (h : TKbR t p x st) (hr : runnable x.tcbState = false) :
    st = x.tcbState := by
  rcases h with h | ⟨-, h, -⟩
  · exact h
  · rw [hr] at h; cases h

theorem BFrR.tcbF (h : BFrR t e σ σ') {p : ObjRef} {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    ∃ st, σ'.kheap p = some (.tcb { x with tcbState := st }) ∧ TKbR t p x st := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x.tcbState, by rw [h1, hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨x', ep, d, e1, rfl, hp', hr⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨_, h2, Or.inr ⟨hp', hr, ep, d, rfl⟩⟩

theorem BFrR.tcbB (h : BFrR t e σ σ') {p : ObjRef} {y : Tcb} (hp : σ'.kheap p = some (.tcb y)) :
    ∃ x st, σ.kheap p = some (.tcb x) ∧ y = { x with tcbState := st } ∧ TKbR t p x st := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, y.tcbState, by rw [← h1, hp], rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨x, ep, d, rfl, e2, hp', hr⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨x, _, h1, rfl, Or.inr ⟨hp', hr, ep, d, rfl⟩⟩

/-- The other kinds kept. -/
theorem BFrR.othF (h : BFrR t e σ σ') {p : ObjRef} {o : KernelObject} (hp : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h4 : ∀ x, o ≠ .endpoint x) : σ'.kheap p = some o := by
  rcases h.kh p with e' | ⟨o0, o', k1, k2, hc⟩
  · rw [e', hp]
  · rw [hp] at k1; cases k1
    rcases hc with ⟨_, _, _, e1, -⟩ | ⟨_, _, e1, -⟩
    · exact absurd e1 (h1 _)
    · exact absurd e1 (h4 _)

theorem BFrR.othB (h : BFrR t e σ σ') {p : ObjRef} {o' : KernelObject} (hp : σ'.kheap p = some o')
    (h1 : ∀ x, o' ≠ .tcb x) (h4 : ∀ x, o' ≠ .endpoint x) : σ.kheap p = some o' := by
  rcases h.kh p with e' | ⟨o, o'', k1, k2, hc⟩
  · rw [← e', hp]
  · rw [hp] at k2; cases k2
    rcases hc with ⟨_, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩
    · exact absurd e2 (h1 _)
    · exact absurd e2 (h4 _)

theorem BFrR.scF (h : BFrR t e σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ.kheap p = some (.schedContext y n)) : σ'.kheap p = some (.schedContext y n) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrR.scB (h : BFrR t e σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ'.kheap p = some (.schedContext y n)) : σ.kheap p = some (.schedContext y n) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrR.replyF (h : BFrR t e σ σ') {p : ObjRef} {x : Reply} (hp : σ.kheap p = some (.reply x)) :
    σ'.kheap p = some (.reply x) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrR.replyB (h : BFrR t e σ σ') {p : ObjRef} {x : Reply} (hp : σ'.kheap p = some (.reply x)) :
    σ.kheap p = some (.reply x) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrR.ntfnF (h : BFrR t e σ σ') {p : ObjRef} {x : Notification} (hp : σ.kheap p = some (.notification x)) :
    σ'.kheap p = some (.notification x) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrR.ntfnB (h : BFrR t e σ σ') {p : ObjRef} {x : Notification} (hp : σ'.kheap p = some (.notification x)) :
    σ.kheap p = some (.notification x) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrR.epF (h : BFrR t e σ σ') {p : ObjRef} {x : Endpoint} (hp : σ.kheap p = some (.endpoint x)) :
    ∃ y, σ'.kheap p = some (.endpoint y) ∧ (y = x ∨ p = e) := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [h1, hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, e1, -⟩ | ⟨x', y, e1, rfl, hp'⟩ <;> cases e1
    exact ⟨y, h2, Or.inr hp'⟩

theorem BFrR.epB (h : BFrR t e σ σ') {p : ObjRef} {y : Endpoint} (hp : σ'.kheap p = some (.endpoint y)) :
    ∃ x, σ.kheap p = some (.endpoint x) ∧ (y = x ∨ p = e) := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← h1, hp], Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, -, e2, -⟩ | ⟨x, y', rfl, e2, hp'⟩ <;> cases e2
    exact ⟨x, h1, Or.inr hp'⟩

theorem BFrR.kind (h : BFrR t e σ σ') (p : ObjRef) :
    (∀ o, σ.kheap p = some o → ∃ o', σ'.kheap p = some o' ∧ aType o' = aType o) ∧
    (∀ o', σ'.kheap p = some o' → ∃ o, σ.kheap p = some o ∧ aType o' = aType o) := by
  rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
  · exact ⟨fun o ho => ⟨o, by rw [e', ho], rfl⟩, fun o' ho => ⟨o', by rw [← e', ho], rfl⟩⟩
  · have ha : aType o' = aType o := by
      rcases hc with ⟨x, ep, d, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ <;> rfl
    exact ⟨fun o0 ho0 => ⟨o', h2, by rw [h1] at ho0; cases ho0; exact ha⟩,
      fun o0 ho0 => ⟨o, h1, by rw [h2] at ho0; cases ho0; exact ha⟩⟩

theorem BFrR.szKeep (h : BFrR t e σ σ') : SzKeep σ σ' := fun _ y n hp => ⟨y, h.scB hp⟩

theorem BFrR.ykeep (h : BFrR t e σ σ') : YKeep σ σ' := by
  refine ⟨fun p x hp => ?_, fun p y n hp => ⟨y, h.scF hp, rfl⟩, fun p z n hp => ⟨z, h.scB hp, rfl⟩⟩
  obtain ⟨st, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem BFrR.mcpKeep (h : BFrR t e σ σ') : McpKeep σ σ' := fun p x hp => by
  obtain ⟨st, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem BFrR.bufKeep (h : BFrR t e σ σ') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => by obtain ⟨st, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem BFrR.prio (h : BFrR t e σ σ') (u : ObjRef) : Sched.prioOf σ' u = Sched.prioOf σ u := by
  unfold Sched.prioOf
  rw [tcbsOf_eq, tcbsOf_eq]
  cases hk : σ.kheap u with
  | some o =>
    cases o with
    | tcb x =>
      obtain ⟨st, hk', -⟩ := h.tcbF hk
      rw [hk']; rfl
    | _ =>
      cases hk' : σ'.kheap u with
      | none => rfl
      | some o' => cases o' with
        | tcb y => obtain ⟨x, -, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
        | _ => rfl
  | none =>
    cases hk' : σ'.kheap u with
    | none => rfl
    | some o' => cases o' with
      | tcb y => obtain ⟨x, -, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
      | _ => rfl

theorem BFrR.nsc {N C : Set U64} (h : BFrR t e σ σ') (hN : NSC N C σ) : NSC N C σ' := by
  intro n hn y p hy hp
  exact hN n hn y p (h.ntfnB hy) hp

theorem BFrR.own {T C : Set U64} (h : BFrR t e σ σ') (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · obtain ⟨st, hkt', -⟩ := h.tcbF hkt
    refine Or.inl ⟨u, hu, _, hkt', by rw [h.sk.csc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
    · rw [h.sk.csc] at hy
      exact hown y n (h.scB hy)
    · rw [h.sk.cons] at h0; rw [h.sk.rel] at hm; exact hnr h0 hm
  · refine Or.inr ⟨by rw [h.sk.csc]; exact hcs, fun y n hy => ?_⟩
    rw [h.sk.csc] at hy
    exact hun y n (h.scB hy)

theorem BFrR.off (h : BFrR t e σ σ') (hO : OffOK σ) : OffOK σ' := by
  intro hc y n hy ha
  rw [h.sk.cons] at hc ⊢; rw [h.sk.tm]
  rw [h.sk.csc] at hy; rw [h.sk.csc, h.sk.isc] at ha
  exact hO hc y n (h.scB hy) ha

theorem BFrR.idleOK (h : BFrR t e σ σ') (hO : IdleOK σ) : IdleOK σ' := by
  obtain ⟨x, hx, h1, h2, h3⟩ := hO
  obtain ⟨st, hx', hs⟩ := h.tcbF hx
  refine ⟨{ x with tcbState := st }, by rw [h.sk.idle]; exact hx', by rw [h.sk.isc]; exact h1, ?_,
    by rw [h.sk.idle, h.sk.rel]; exact h3⟩
  show st = _
  rw [hs.run (by rw [h2]; rfl)]; exact h2

/-- `BlockedScActive` after, `t`'s SCs active. -/
theorem BFrR.bsa (h : BFrR t e σ σ') (hB : BlockedScActive σ)
    (ht : ∀ p y n, σ.kheap p = some (.schedContext y n) → y.scTcb = some t → scActive y = true) :
    BlockedScActive σ' := by
  refine ⟨fun p z n u y hp hyt hy hq => ?_, fun p z n hp hr => hB.replies p z n (h.scB hp) hr⟩
  obtain ⟨x, st, hx, rfl, hs⟩ := h.tcbB hy
  rcases hs with rfl | ⟨rfl, -, -⟩
  · exact hB.tcb p z n u x (h.scB hp) hyt hx hq
  · exact ht p z n (h.scB hp) hyt

/-- `IpcSorted` after, `e`'s queue sorted. -/
theorem BFrR.isorted (h : BFrR t e σ σ') (hS : IpcSorted σ)
    (he : ∀ y, σ'.kheap e = some (.endpoint y) → SortedQ σ y.epQueue) : IpcSorted σ' := by
  refine ⟨fun p y hp => ?_, fun p y hp => ?_⟩
  · obtain ⟨x, hx, hc⟩ := h.epB hp
    rcases hc with rfl | rfl
    · exact (hS.1 p y hx).congr fun u _ => h.prio u
    · exact (he y hp).congr fun u _ => h.prio u
  · exact (hS.2 p y (h.ntfnB hp)).congr fun u _ => h.prio u

theorem BFrR.kback (h : BFrR t e σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e' | ⟨ko, ko'', h1, h2, hc⟩
  · exact ⟨ko', by rw [← e', ho], id, id, id, id, id, id⟩
  · rw [ho] at h2; cases h2
    rcases hc with ⟨x, ep, d, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩
    · exact ⟨_, h1, by simp⟩
    · exact ⟨_, h1, by simp⟩

theorem BFrR.ksz (h : BFrR t e σ σ') : KSz σ σ' := fun o ko' ho => by
  obtain ⟨ko, h1, e'⟩ := (h.kind o).2 ko' ho
  exact ⟨ko, h1, e'.symm⟩

theorem BFrR.ksub (h : BFrR t e σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun rr cs hc hw => ⟨cs, ?_, hw⟩, fun u hu => ?_, fun hn => ?_⟩
  · exact h.othB hc (fun _ e => by cases e) (fun _ e => by cases e)
  · obtain ⟨x, -, hx, -⟩ := h.tcbB hu; exact ⟨x, hx⟩
  · rcases h.kh o with e' | ⟨ko, ko', h1, -, -⟩
    · rw [e']; exact hn
    · rw [hn] at h1; cases h1

theorem BFrR.callKeep (h : BFrR t e σ σ') :
    (∀ q y n, σ.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
    (∀ q x, σ.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
    (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n)) :=
  ⟨fun q y n hq => ⟨y, h.scF hq, rfl⟩, fun q x hq => ⟨x, h.replyF hq, rfl⟩, fun p x n hp => ⟨x, h.scB hp⟩⟩

theorem BFrR.skeep (h : BFrR t e σ σ') : Ipc.SKeep σ σ' := by
  refine ⟨h.sk.rel, h.sk.tm, fun p y hy => ?_, fun p y n hy => h.scB hy⟩
  obtain ⟨x, st, hx, rfl, -⟩ := h.tcbB hy
  exact ⟨x, hx, rfl⟩

/-- **`RRecv` across `BFrR`** (module docstring): no reply names `t` before. -/
theorem RRecv.frameR {R : Set U64} {m m' : U64 → U64} {σ σ' : State Unit} {t e : ObjRef} (h : RRecv m R σ)
    (hm : ∀ d ∈ R, m' (rPrevA d) = m (rPrevA d) ∧ m' (rNextA d) = m (rNextA d)) (F : BFrR t e σ σ')
    (hnt : ∀ d ∈ R, ∀ xr, σ.kheap d.bv = some (.reply xr) → xr.replyTcb ≠ some t) :
    RRecv m' R σ' := fun d hd hr => by
  obtain ⟨xr, u, xu, hkr, hru, hku, hrb⟩ := hr
  have hkr0 := F.replyB hkr
  obtain ⟨x0, st0, hk0, rfl, hs⟩ := F.tcbB hku
  have hut : u ≠ t := fun e => hnt d hd xr hkr0 (e ▸ hru)
  have hst : st0 = x0.tcbState := by
    rcases hs with h1 | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hut
  obtain ⟨h1, h2⟩ := h d hd ⟨xr, u, x0, hkr0, hru, hk0, by rw [← hst]; exact hrb⟩
  exact ⟨(hm d hd).2.trans h1, (hm d hd).1.trans h2⟩

end

/-- **The spec's blocking receive with a null reply cap in `BFrR`** (module
docstring). -/
theorem recvIpcBlock0_eq {σ : State Unit} {t e : ObjRef} {xt : Tcb} {x : Endpoint}
    (hkt : σ.kheap t = some (.tcb xt)) (hbn : xt.tcbBoundNotification = none)
    (hk : σ.kheap e = some (.endpoint x)) (hc : Endp.CanBlock true x)
    (htq : t ∉ x.epQueue) (hq : ∀ y ∈ x.epQueue, ∃ z, σ.kheap y = some (.tcb z)) (hr : runnable xt.tcbState = true)
    (hS : SortedQ σ x.epQueue) (b : Badge) (rights : CapRights) :
    ∃ σ', receiveIpc (Z := Unit) t (.endpointCap e b rights) true .nullCap σ = ({((), σ')}, False) ∧
      BFrR t e σ σ' ∧ IK t σ σ' ∧ σ'.readyQueues = σ.readyQueues ∧
      (t = σ.curThread → σ.schedulerAction = .resumeCurThread → σ'.schedulerAction = .chooseNewThread) ∧
      (∀ y, σ'.kheap e = some (.endpoint y) → SortedQ σ y.epQueue) := by
  let x1 : Tcb := { xt with tcbState := .blockedOnReceive e none { receiverCanGrant := false } }
  let σ2 := stsAct (updK σ t (.tcb x1)) t
  let q' := Notif.specIns x.epQueue (Sched.prioOf σ2) x1.tcbPriority t
  let σ' := updK σ2 e (.endpoint (updateEpQueue x q' true))
  have hns : ∀ q, x ≠ .sendEP q := fun q h => by subst h; simp [Endp.CanBlock] at hc
  have hte : t ≠ e := by rintro rfl; rw [hkt] at hk; cases hk
  have hk2 : σ2.kheap e = some (.endpoint x) := by simp [σ2, stsAct_kheap, Ne.symm hte, hk]
  have hkt2 : σ2.kheap t = some (.tcb x1) := by simp [σ2, stsAct_kheap]
  have hq2 : ∀ y ∈ x.epQueue, ∃ z, σ2.kheap y = some (.tcb z) ∧ z.tcbPriority = Sched.prioOf σ2 y := by
    intro y hy
    obtain ⟨z, hz⟩ := hq y hy
    have hyt : y ≠ t := fun h => htq (h ▸ hy)
    have hz2 : σ2.kheap y = some (.tcb z) := by simp [σ2, stsAct_kheap, hyt, hz]
    exact ⟨z, hz2, (prioOf_eq hz2).symm⟩
  have hblk : receiveIpc (Z := Unit) t (.endpointCap e b rights) true .nullCap σ =
      ((setThreadState t (.blockedOnReceive e none { receiverCanGrant := false }) >>= fun _ =>
        (pure () : SMonad Unit Unit) >>= fun _ => tcbEpAppend t e true) σ) := by
    rw [Endp.receiveIpc_noSend b rights true (Or.inl ⟨rfl, rfl⟩) hkt hbn hk hns]
    unfold receiveIpcBlocked
    rw [if_pos rfl]
    rfl
  have heq : receiveIpc (Z := Unit) t (.endpointCap e b rights) true .nullCap σ = ({((), σ')}, False) := by
    rw [hblk, nd_bind_one (Notif.setThreadState_eq _ hkt), nd_pure_bind']
    exact Endp.tcbEpAppend_eq hk2 hkt2 (Sched.prioOf σ2) hq2 true
  have hm : ((), σ') ∈ (receiveIpc (Z := Unit) t (.endpointCap e b rights) true .nullCap σ).1 := by
    rw [heq]; exact Set.mem_singleton _
  have hik : IK t σ σ' := by
    rw [hblk] at hm
    exact ikm_bind (ikm_setThreadState _) (fun _ => ikm_bind (ikm_pure _) fun _ => ikm_tcbEpAppend t e true)
      σ ((), σ') hm
  have hsk2 : Sk σ σ2 := by
    show Sk σ (stsAct _ t)
    unfold stsAct; split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsk : Sk σ σ' := hsk2.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hkh : ∀ p, σ'.kheap p = if p = e then some (.endpoint (updateEpQueue x q' true))
      else if p = t then some (.tcb x1) else σ.kheap p := by
    intro p
    simp only [σ', σ2, updK_kheap, stsAct_kheap, Function.update_apply]
  have hpr2 : ∀ u, Sched.prioOf σ2 u = Sched.prioOf σ u := by
    intro u
    by_cases hut : u = t
    · subst hut; exact (prioOf_eq hkt2).trans (prioOf_eq hkt).symm
    · unfold Sched.prioOf; rw [tcbsOf_eq, tcbsOf_eq]
      simp only [σ2, stsAct_kheap, updK_kheap, Function.update_apply, if_neg hut]
  have hrq : σ'.readyQueues = σ.readyQueues := by
    show (stsAct _ t).readyQueues = _
    unfold stsAct; split <;> rfl
  refine ⟨σ', heq, ⟨hsk, fun p => ?_⟩, hik, hrq, fun hct hres => ?_, fun y hy => ?_⟩
  · rw [hkh]
    by_cases hpe : p = e
    · rw [if_pos hpe]; exact Or.inr ⟨.endpoint x, .endpoint (updateEpQueue x q' true), by rw [hpe]; exact hk, rfl,
        Or.inr ⟨x, _, rfl, rfl, hpe⟩⟩
    · rw [if_neg hpe]
      by_cases hpt : p = t
      · rw [if_pos hpt]
        exact Or.inr ⟨.tcb xt, .tcb x1, by rw [hpt]; exact hkt, rfl, Or.inl ⟨xt, e, _, rfl, rfl, hpt, hr⟩⟩
      · rw [if_neg hpt]; exact Or.inl rfl
  · have hns' : ¬ schedulable t (updK σ t (.tcb x1)) = true := by
      intro hs
      obtain ⟨y, -, -, -, hy, -, hrun, -⟩ := schedulable_inv hs
      rw [updK_kheap, Function.update_self] at hy
      cases hy
      simp [x1, runnable] at hrun
    show (stsAct _ t).schedulerAction = _
    unfold stsAct
    rw [if_pos ⟨hct, hres, hns'⟩]
  · rw [hkh, if_pos rfl] at hy
    cases hy
    rw [epQueue_update]
    exact (sortedQ_specIns (hS.congr fun u _ => hpr2 u) t (prioOf_eq hkt2)).congr fun u _ => (hpr2 u).symm

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- A store-only step lifted to the `(state, arch)` pair. -/
theorem spec_lift_ok {m : Result S} {P : S → Prop} (h : m ⦃ P ⦄) (a : A) :
    (do
      let s3 ← m
      ok (s3, a)) ⦃ r => P r.1 ⦄ :=
  WP.spec_bind h fun s3 h3 => (WP.spec_ok _).2 h3

set_option maxHeartbeats 16000000 in
/-- **The blocking receive with a null reply cap at `J`** (module docstring):
the current thread `t`, with no bound notification, blocks receiving on the
idle or receiving endpoint `e`, covered by a cap (`hcov`). -/
theorem JAtZ.recvIpcBlock0J (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : Entered σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hbn : xt.tcbBoundNotification = none)
    {e : U64} (he : e ∈ Z.E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : Endp.CanBlock true x)
    (hcov : (∀ k, Z.th e = some k → Covered (L.mem s) Z.G e.val (e.val + max (objSize k) 1)) ∧
      (∀ k, H e = some k → Covered (L.mem s) Z.G e.val (e.val + 2 ^ k.bits)))
    (cb : U64) (c1 c2 c3 c4 : Bool) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) true .Null ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true .nullCap σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hC : CurInv σ := J.curInv (by rw [hni.2]; intro e; cases e)
  have hres : σ.schedulerAction = .resumeCurThread := hni.2
  have hti : σ.curThread ≠ σ.idleThread := hni.1
  obtain ⟨xc, hkc, hscc, -⟩ := hC.tcb
  rw [hcur, hkt] at hkc; cases hkc
  have hr : Fl4Spec.runnable xt.tcbState = true := (J.curRun.run hni) xt (by rw [hcur]; exact hkt)
  have hnb3 : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by
    rcases runnable_code hr with h | h | h <;> rw [h] <;> decide
  have hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m := fun m h => by rw [h] at hr; cases hr
  have htq : t.bv ∉ x.epQueue := Endp.not_queued hI.1.toE ht hkt hnb3 e he x hk
  have hq : ∀ y ∈ x.epQueue, ∃ z, σ.kheap y = some (.tcb z) := fun y hy => by
    obtain ⟨z, hz, -⟩ := (J.sv.epQ _ _ hk).2 y hy
    exact ⟨z, hz⟩
  obtain ⟨σ', heq, F, hik, -, hcn, hsrt⟩ :=
    recvIpcBlock0_eq hkt hbn hk hc htq hq hr (J.isorted.1 _ _ hk) b rights
  have hcn' : σ'.schedulerAction = .chooseNewThread := hcn hcur.symm hres
  -- P1's `BlkOK` after and footprint
  have hcb := J.canBlockCur ht hcur hkt hr hni hnq
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  have hHe : H e = some .ep := J.zH.2.1 e he
  have hx := hI.1.toE.at_ep he hk
  have hst2 : stOf (L.mem s) e = 0#u64 ∨ stOf (L.mem s) e = 2#u64 := by
    cases x with
    | idleEP => exact Or.inl hx.1
    | recvEP q => exact Or.inr hx.1
    | sendEP q => simp [Endp.CanBlock] at hc
  have hst0 : L.epState s e = 0#u64 ∨ L.epState s e = 2#u64 := by rw [epState_eq]; exact hst2
  have hbound : L.mem s (tBoundA t) = 0#u64 :=
    optRef_none ((hI.1.toE.at_tcb ht hkt).bound.symm.trans hbn)
  have p1b := spec_lift_ok (P1.endpoint.wait_for_sender.inv s t e true 0#u64 Q0 R0 h0 hB0 hX0 hS0 hSg0
    (J.zH.1 t ht) (fun _ => hcb) hHe hst0 (fun h => absurd rfl h)) a
  have p1f := spec_lift_ok (P1.endpoint.wait_for_sender.foot0 (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H)
    (Z := P1.Heap.scBits H) s t e h0 hcb hHe) a
  apply receive_ipc_block0_red hbound hst2
  refine WP.spec_mono (WP.spec_and (WP.spec_and (wait_for_sender_blockF0 J.ip s a σ hI ht hkt hnb3 hnn hbn he hk hc
    (J.qsortedE e he) b rights) p1b) p1f) ?_
  rintro ⟨s', a'⟩ ⟨⟨⟨ea, σ0, h0eq, hIR, hW⟩, hbk⟩, hfoot⟩
  simp only at ea hbk hfoot hIR hW
  subst a'
  obtain rfl : σ' = σ0 := by
    have e1 := (Prod.mk.inj (h0eq.symm.trans heq)).1
    exact (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e1)).symm
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := ⟨⟨Q0, R0, hbk.1⟩, hbk.2⟩
  have hDbg := J.kw_dbg hfoot
  -- the assembly (as XTopJointSendBlock's `JAtZ.sendBlockJ`)
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hW fun b hb => CnW.oobj hI.2.2.1 hb
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR hAR hF.1 F.sk.cdt F.sk.orig F.ksub hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hW
  have ck := F.callKeep
  have hCR' : CallRel (L.mem s') Z.R Z.C σ' Lst :=
    J.call.frame k3 k4 (fun q _ y n hy => ck.1 _ y n hy) (fun d _ x hx => ck.2.1 _ x hx)
  have hRP' := J.rp.frame hks ck.2.2
  have hRF' : RFree (L.mem s') Z.R Z.C σ' Lst := by
    intro d hd hfd
    obtain ⟨y, hy, hyt⟩ := hfd
    obtain ⟨e1, e2⟩ := k4 d hd
    obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨y, F.replyB hy, hyt⟩
    exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
  have hAI3 : ActIdle σ' := ⟨fun u hu => (by rw [hcn'] at hu; cases hu), F.idleOK J.act.2⟩
  have hcur3 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := Or.inl hcn'
  have hrun3 : CurRunM σ' := Or.inl (by rw [hcn']; intro h; cases h)
  -- the dead: the thread is not dead (runnable); the endpoint leaves the dead set
  have htD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by rcases runnable_code hr with h | h | h <;> rw [h] <;> decide)
  have hdead : ∀ q ∈ D \ {e}, DeadP (L := L) H s' q := fun q hq => by
    have hd := J.jcov.dead q hq.1
    have hqt : q.bv ≠ t.bv := htD q hq.1
    have hqe : q.bv ≠ e.bv := fun h => hq.2 (P1.eq_of_bv h)
    refine J.deadP_keep hS3 hIR.1 (fun x hx h0 => ?_) (fun x hx => ?_)
      (fun x hx => ⟨x, F.ntfnF hx, Or.inl rfl, rfl, Or.inl rfl⟩)
      (fun x hx => ⟨x, F.replyF hx, rfl⟩) (fun x n hx => ⟨x, F.scF hx, Or.inl rfl, Or.inl rfl⟩)
      (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hW hz hqC hK8 hK) F.sk.idle hAI3.1
      (J.yld.frame k2 F.ykeep) (F.ykeep.dk q.bv) hd
    · obtain ⟨st', hk3, hs'⟩ := F.tcbF hx
      refine ⟨_, hk3, ?_, rfl, Or.inl rfl⟩
      show st' = x.tcbState
      rcases hs' with e1 | ⟨e1, -⟩
      · exact e1
      · exact absurd e1 hqt
    · obtain ⟨y, hy, hc'⟩ := F.epF hx
      rcases hc' with rfl | e1
      · exact hy
      · exact absurd e1 hqe
  have hidl := J.idleW_keep hS3 F.sk.idle F.sk.isc
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.cnW_irq hW) hidl.2⟩
  have hkern := J.kern_keep hks hW.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D \ {e})
  -- no reply names the runnable thread (`SchedValid.replyTcb`)
  have hnt : ∀ d ∈ Z.R, ∀ xr, σ.kheap d.bv = some (.reply xr) → xr.replyTcb ≠ some t.bv := by
    intro d _ xr hkr hrt
    obtain ⟨x', hk', hs'⟩ := J.sv.replyTcb _ xr _ hkr hrt
    rw [hkt] at hk'; cases hk'
    rcases hs' with hs' | ⟨ep, dd, hs'⟩ <;> rw [hs'] at hr <;> cases hr
  have hRR' := J.rrecv.frameR k4 F hnt
  have hjcov : JCovD (L := L) Z.th H Z.G (D \ {e}) Cs s' := by
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
    exact (J.jcov.undead hcov.1 hcov.2).same (fun y hy _ _ => ⟨hy, hF.1.capV (hsl y hy)⟩) (fun q hq _ => hdead q hq)
      (J.jcov.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩) hidl hks
      (J.jcov.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩)
  -- `Inv` (`InvBut.ik`; the thread's `RelIfBound` from a runnable state)
  have hnqT : NotQueued σ t.bv := ⟨by rw [← hcur]; exact hnq, by rw [← hcur]; exact hC.notRel⟩
  obtain ⟨hIB, -⟩ := (J.inv.toBut t.bv).ik hnqT hik
  have hrib : RelIfBound σ' t.bv := Ipc.RelIfBound.of_keep (J.inv.rd t.bv xt hkt (Or.inl hr)) F.skeep
  have I3 : Inv σ' := hIB.inv fun _ _ _ => hrib
  -- `BlockedScActive`: the thread's SC is the current SC, active
  have hscA : ∀ p y n, σ.kheap p = some (.schedContext y n) → y.scTcb = some t.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    obtain ⟨q, hqC, eq⟩ := J.obj.sc p y n hp
    subst eq
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hq0 := J.c0 q hqC
    have hqS : q ∈ P1.Heap.scs H := ⟨_, (hJ.sc q y n hq0 hp).2⟩
    obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hqC hqS hq0 hp hyt
    rw [hkt] at hku; cases hku
    have e1 : σ.curSc = q.bv := Option.some.inj (hscc.symm.trans hxs)
    rw [← e1] at hp
    exact hC.active (J.curSc_ne_idle hC hti) y n hp
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst (D \ {e}) s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, hjcov, hkern,
      J.cnW_utc hW hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa hscA, F.isorted J.isorted hsrt, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hCs : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  have J3 := J.cs_frameI hks hX3 hW (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) F.sk.arch
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback hCs R
  rw [heq]
  exact ⟨_, Set.mem_singleton _, J3.xtop.relTop, _, _, _, _, _, _, J3⟩

end

end

end Fl4Proofs.P3
