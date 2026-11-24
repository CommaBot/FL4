/-
P3 (DESIGN.md §9), IPC: **`receive_ipc` with an active bound notification at
`J`** (KENTRY-PLAN.md item 6 (a)): the current thread, resumed, whose bound
notification is active, receives its signal instead (`complete_signal`).

* The spec: `receiveIpc_active` (the reply cap null or naming an unlinked
  reply, `SpecReplyArg`: no `cancel_ipc`), `completeSignal_cur` (the badge,
  the notification idle; the donation and the sporadic check are no-ops for
  a thread on the current SC).
* FL4: `receive_ipc_preA` (`take_reply` a no-op as EpRecv's
  `receive_ipc_pre`, then `complete_signal`), `complete_signal_cur_eq` (the
  same two writes as `receive_signal` on an active notification,
  XTopJointRecvSig's `recvActS`).
* `JAtZ.recvIpcActJ`: as XTopJointRecvSig's `JAtZ.recvSigActiveJ` (P1's
  `BlkOK` after from `receive_signal.ipc`, which reaches the same state).
-/
import Fl4Proofs.P3.XTopJointRecvSigRet
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- **The spec's receive with an active bound notification**: its
`complete_signal`, for a reply cap as in `SpecReplyArg`. -/
theorem receiveIpc_active {σ : State Unit} {t e n : ObjRef} (b : Badge) (rights : CapRights) (blk : Bool)
    {rc' : Cap} {reply : Option ObjRef} (hrc : SpecReplyArg σ rc' reply) {xt : Tcb}
    (hkt : σ.kheap t = some (.tcb xt)) (hb : xt.tcbBoundNotification = some n) {x : Endpoint}
    (hk : σ.kheap e = some (.endpoint x)) {xn : Notification} (hkn : σ.kheap n = some (.notification xn))
    {b0 : Badge} (hact : xn.ntfnObj = .activeNtfn b0) :
    receiveIpc (Z := Unit) t (.endpointCap e b rights) blk rc' σ = completeSignal n t σ := by
  have hA : isActive xn = true := by simp [isActive, hact]
  unfold receiveIpc
  dsimp only
  rw [nd_pure_bind']
  rcases hrc with ⟨rfl, rfl⟩ | ⟨r, rr, xr, rfl, rfl, hkr, hr⟩
  · dsimp only
    rw [nd_pure_bind', nd_bind_one (getEndpoint_eq hk), nd_bind_one (getTcbObjRef_eq _ hkt)]
    simp only [hb]
    rw [nd_bind_one (getNotification_eq hkn), if_pos ⟨by simp, hA⟩]
    rfl
  · dsimp only
    rw [nd_bind_one (getReplyTcb_eq hkr)]
    simp only [hr]
    rw [nd_when_false_bind (by simp [hr])]
    rw [nd_pure_bind', nd_bind_one (getEndpoint_eq hk), nd_bind_one (getTcbObjRef_eq _ hkt)]
    simp only [hb]
    rw [nd_bind_one (getNotification_eq hkn), if_pos ⟨by simp, hA⟩]
    rfl

/-- **The spec's `complete_signal` for a thread on the current SC**: the
badge register, the notification idle. -/
theorem completeSignal_cur {σ : State Unit} {t n : ObjRef} {xt : Tcb} {x : Notification} {b0 : Badge}
    (hkt : σ.kheap t = some (.tcb xt)) (hkn : σ.kheap n = some (.notification x))
    (hact : x.ntfnObj = .activeNtfn b0) (hsc : xt.tcbSchedContext = some σ.curSc) {y : SchedContext} {m : Nat}
    (hks : σ.kheap σ.curSc = some (.schedContext y m)) (hct : σ.curSc ≠ t) (hcn : σ.curSc ≠ n) (hnt : n ≠ t) :
    completeSignal (Z := Unit) n t σ = ({((), updK (updK σ t (.tcb (setReg xt badge_register b0))) n
      (.notification (ntfnObjUpdate (fun _ => .idleNtfn) x)))}, False) := by
  have hk1 : (updK σ t (.tcb (setReg xt badge_register b0))).kheap n = some (.notification x) := by
    simp [updK, hnt, hkn]
  set σ2 := updK (updK σ t (.tcb (setReg xt badge_register b0))) n
    (.notification (ntfnObjUpdate (fun _ => .idleNtfn) x)) with hσ2
  have hkt2 : σ2.kheap t = some (.tcb (setReg xt badge_register b0)) := by simp [σ2, updK, Ne.symm hnt]
  have hks2 : σ2.kheap σ2.curSc = some (.schedContext y m) := by simp [σ2, updK, hct, hcn, hks]
  have hkn2 : σ2.kheap n = some (.notification (ntfnObjUpdate (fun _ => .idleNtfn) x)) := by simp [σ2, updK]
  have hsc2 : (setReg xt badge_register b0).tcbSchedContext = some σ2.curSc := by
    simp only [σ2, updK]; exact hsc
  have hd : maybeDonateSc (Z := Unit) t n σ2 = ({((), σ2)}, False) := by
    unfold maybeDonateSc getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hkt2), hsc2]
    simp only [NonDet.when, reduceCtorEq, ↓reduceIte]
    rfl
  unfold completeSignal
  rw [nd_bind_one (getNotification_eq hkn)]
  simp only [hact]
  rw [nd_bind_one (asUser_setRegister_eq _ _ hkt), nd_bind_one (setNotification_eq _ hk1), nd_bind_one hd]
  unfold getTcbObjRef
  rw [nd_bind_one (threadGet_eq _ hkt2), hsc2]
  show (getSchedContext σ2.curSc >>= _) σ2 = _
  rw [nd_bind_one (getSchedContext_eq hks2)]
  unfold NonDet.when
  split_ifs
  · rw [nd_bind_one (getNtfnSc_eq hkn2), Notif.nd_gets_bind, if_neg (by simp)]
    rfl
  · rfl

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)}

/-- What `receive_ipc` does with an active bound notification `n` and a
reply cap as in `ReplyArg` (no `cancel_ipc`): `complete_signal`. -/
theorem receive_ipc_preA (s : S) (a : A) (t e cb : U64) (c1 c2 c3 c4 blk : Bool) (rc : capability.Cap)
    (rc' : Fl4Spec.Cap) (rv : U64) (hrc : ReplyArg R (L.mem s) rc rc' rv) {n : U64}
    (hbound : L.mem s (tBoundA t) = n) (hn0 : n ≠ 0#u64) (hst : stOf (L.mem s) n = obj.NTFN_ACTIVE)
    {P : S × A → Prop} (h : notification.complete_signal st ar s a n t ⦃ P ⦄) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ P ⦄ := by
  unfold endpoint.receive_ipc
  simp only [capability.Cap.ptr, bind_tc_ok]
  rcases hrc with ⟨rfl, -, rfl⟩ | ⟨b, r', rfl, -, -, h0⟩
  · simp only [endpoint.take_reply, bind_tc_ok]
    step with Endp.obj.Tcb.bound_ntfn.spec as ⟨i, hi⟩
    simp only [hi, hbound]
    rw [if_pos (by simpa using hn0)]
    refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
    rintro v rfl
    rw [epState_eq, hst, if_pos rfl]
    exact h
  · simp only [endpoint.take_reply]
    step with Endp.obj.Reply.tcb.spec as ⟨i, hi⟩
    step with P1.obj.Tcb.is_null.spec as ⟨b, hb⟩
    simp only [hb, hi, h0, decide_true, ↓reduceIte, bind_tc_ok]
    step with Endp.obj.Tcb.bound_ntfn.spec as ⟨j, hj⟩
    simp only [hj, hbound]
    rw [if_pos (by simpa using hn0)]
    refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
    rintro v rfl
    rw [epState_eq, hst, if_pos rfl]
    exact h

end

end

end Fl4Proofs.P3.Endp

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- FL4's `complete_signal` on an active notification for a thread whose SC
is the current SC (after the writes): the two writes of `recvActS`. -/
theorem complete_signal_cur_eq {s : S} {a : A} {t n : U64} (ht0 : t ≠ 0#u64)
    (hst : stOf (L.mem s) n = obj.NTFN_ACTIVE)
    (h0 : L.mem (recvActS st s t n) (P1.scA t) ≠ 0#u64)
    (hc : L.mem (recvActS st s t n) (P1.scA t) =
      Sched.nodeW st (recvActS st s t n) (L.cpu (recvActS st s t n)) layout.node.CUR_SC) :
    notification.complete_signal st arI s a n t ⦃ r => r = (recvActS st s t n, a) ⦄ := by
  unfold recvActS at h0 hc ⊢
  rw [regIdx_badge] at h0 hc ⊢
  unfold notification.complete_signal
  step with P1.obj.Tcb.is_null.spec as ⟨b, hb⟩
  simp only [hb, ht0, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
  rintro v rfl
  rw [epState_eq, hst]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (obj.Ntfn.badge.spec s n) ?_
  rintro b rfl
  refine WP.spec_bind (obj.Tcb.set_reg.spec s t layout.reg.BADGE _) ?_
  rintro s1 rfl
  refine WP.spec_bind (obj.Ntfn.set_state.spec _ n obj.NTFN_IDLE) ?_
  rintro s2 rfl
  rw [maybe_donate_hasSc h0, bind_ok]
  refine WP.spec_bind (P1.obj.Tcb.sc.spec _ t) ?_
  rintro i rfl
  step with sporadic.sc_sporadic.spec' as ⟨b2, hb2⟩
  split
  · refine WP.spec_bind (Notif.obj.Ntfn.sc.spec _ n) ?_
    rintro i2 rfl
    split
    · refine WP.spec_bind (Sched.sched.cur_sc.spec' _) ?_
      rintro c rfl
      rw [Sched.sc_ne_eq, bind_ok, hc]
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    · exact (WP.spec_ok _).2 rfl
  · exact (WP.spec_ok _).2 rfl

set_option maxHeartbeats 16000000 in
/-- **`receive_ipc` with an active bound notification at `J`** (module
docstring): the current thread, resumed. -/
theorem JAtZ.recvIpcActJ (hAT : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv)
    (hni : Entered σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt0 : σ.kheap t.bv = some (.tcb xt))
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hbn : xt.tcbBoundNotification = some n.bv) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (blk : Bool) {e : U64} {xe : Fl4Spec.Endpoint} (hke : σ.kheap e.bv = some (.endpoint xe))
    (cb : U64) (c1 c2 c3 c4 : Bool)
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hC : CurInv σ := J.curInv (by rw [hni.2]; intro e; cases e)
  have hkt := hkt0
  obtain ⟨xc, hkc, hscc, -⟩ := hC.tcb
  rw [hcur, hkt] at hkc; cases hkc
  obtain ⟨ys, ms, hks⟩ := hC.sc
  have hrn : Fl4Spec.runnable xt.tcbState = true := (J.curRun.run hni) xt (by rw [hcur]; exact hkt)
  have hcb := J.canBlockCur ht hcur hkt hrn hni hnq
  -- the badge register
  have hx := hI.1.toN.at_ntfn hn hk
  have hst : stOf (L.mem s) n = obj.NTFN_ACTIVE := stOf_active (T := Z.T) (hact ▸ hx.obj) rfl
  have hb0 : (L.mem s (nBadgeA n)).bv = b0 := by
    have := hx.obj; rw [hact] at this; exact this.2.2
  have hXb := badge_wr_irel J.ip hI ht hkt (L.mem s (nBadgeA n))
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V1, J1⟩ := J.regWrJ ht hkt Fl4Spec.badge_register _ hXb
  rw [hb0] at J1
  have hnt : n.bv ≠ t.bv := by intro e; rw [e, hkt] at hk; cases hk
  have hk1 : (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))).kheap n.bv = some (.notification x) := by
    simp [updK, hnt, hk]
  -- the notification's state
  have hI1 := J1.xtop.irelK J1.ks J1.buf
  obtain ⟨hR2, hW2, hS2⟩ := set_idle_relI J1.ip hI1.1 hn hk1 hact
  have hSch2 := hI1.2.2.1.stable hW2 hS2
  obtain ⟨Q, R, hc, hs⟩ := hSch2.lists
  obtain ⟨xt2, hkt2, -, -, hsct2, -⟩ := hs.tcb t ht
  have hkt2' : (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
      (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))).kheap t.bv =
      some (.tcb (setReg xt Fl4Spec.badge_register b0)) := by
    simp [updK, hnt.symm]
  rw [hkt2'] at hkt2; cases hkt2
  have hsw : optRef (L.mem (recvActS st s t n) (P1.scA t)) = some σ.curSc := hsct2.symm.trans hscc
  have h0 : L.mem (recvActS st s t n) (P1.scA t) ≠ 0#u64 := by
    intro e; rw [e, optRef_zero] at hsw; cases hsw
  have hcw : L.mem (recvActS st s t n) (P1.scA t) =
      Sched.nodeW st (recvActS st s t n) (L.cpu (recvActS st s t n)) layout.node.CUR_SC := by
    apply P1.eq_of_bv
    rw [Notif.optRef_ne h0] at hsw
    rw [Option.some.inj hsw]
    exact hs.curSc.trans (congrArg (fun q => (Sched.nodeW st (recvActS st s t n) q layout.node.CUR_SC).bv) hc.cur).symm
  have heq := spec_eq_ok (receive_signal_active_eq (arI := arI) (a := a) blk hst h0 hcw)
  -- P1's `BlkOK` after
  obtain ⟨⟨Q0, R0, h0'⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  have p1 := P1.notification.receive_signal.ipc hAT s a t n blk Q0 R0 h0' hB0 hX0 hS0 hSg0 hcb
    (J.zH.2.2.2 n hn) (J.zH.2.2.2 n hn) (by rw [epState_eq, hst, ntfn_consts.2.2]; decide)
  rw [heq, WP.spec_ok] at p1
  simp only [WP.uncurry'_pair] at p1
  -- the notification write at `J`
  have hxw : ∀ l, x.ntfnObj ≠ .waitingNtfn l := fun l h => by rw [hact] at h; cases h
  obtain ⟨σ', V', hsp', -, J2⟩ := J1.signal_badge_post hn hk1 hxw
    (y := Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x) (fun l h => by cases h) rfl rfl rfl
    ⟨_, rfl, hR2, hS2, hW2, NoBlock.ntfnUpd _ _ _⟩ p1
  obtain rfl := (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj hsp').1))
  -- the spec's outcome and FL4's
  have hct : σ.curSc ≠ t.bv := fun e => by rw [e, hkt] at hks; cases hks
  have hcn : σ.curSc ≠ n.bv := fun e => by rw [e, hk] at hks; cases hks
  have hxt := hI.1.toE.at_tcb ht hkt
  have hb1 : optRef (L.mem s (tBoundA t)) = some n.bv := hxt.bound.symm.trans hbn
  have hbz : L.mem s (tBoundA t) ≠ 0#u64 := fun e => by rw [e, optRef_zero] at hb1; cases hb1
  have hbound : L.mem s (tBoundA t) = n := by
    rw [Notif.optRef_ne hbz] at hb1; exact P1.eq_of_bv (Option.some.inj hb1)
  have ht0 : t ≠ 0#u64 := fun e => by
    obtain ⟨Q1, R1, hc1, -⟩ := J.xtop.fin.1.1.1.lists
    exact (hc1.tcbs t ht).ne0 (by rw [e]; rfl)
  have heqI := spec_eq_ok (receive_ipc_preA (ar := arI) s a t e cb c1 c2 c3 c4 blk rc rc' rv hrc hbound
    (by rw [← hbound]; exact hbz) hst (complete_signal_cur_eq (arI := arI) (a := a) ht0 hst h0 hcw))
  have hspecI := receiveIpc_active b rights blk (replyArg_spec J.ip.e hI.1.toE hrc) hkt hbn hke hk hact
  rw [hspecI, completeSignal_cur hkt hk hact hscc hks hct hcn hnt, heqI, WP.spec_ok]
  exact ⟨_, Set.mem_singleton _, J2.xtop.relTop, _, _, _, _, _, _, J2, inferInstance⟩


end

end

end Fl4Proofs.P3
