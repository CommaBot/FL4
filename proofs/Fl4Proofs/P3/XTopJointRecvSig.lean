/-
P3 (DESIGN.md §9), IPC: **`receive_signal` at `J`** (KENTRY-PLAN.md item 5,
toward XTopJointDispatch's `JRecvSigHyp`), by the notification's state.

* `JAtZ.recvSigPollJ`: polling a notification that is not active (FL4's
  `receive_signal` with `blocking = false`): the badge register := 0, the
  spec's `doNbrecvFailedTransfer`; one register write at `J`
  (`JAtZ.regWrJ`, `badge_wr_irel`).
* `JAtZ.recvSigActiveJ`: an active notification: the badge register := the
  notification's badge (`regWrJ`), the notification idle (IpcNtfnRecv's
  `set_idle_relI`, a badge-only notification write at `J`:
  `JAtZ.signal_badge_post`, with P1's `BlkOK` after by
  `notification.receive_signal.ipc` from `JAtZ.canBlockCur`); the
  donation and the sporadic check are no-ops for the current thread, which
  runs on the current SC (`CurInv.tcb`; FL4: `maybe_donate_hasSc`, the SC
  word is the `CUR_SC` word; the spec: `specRecvTail_cur`).
* `JAtZ.canBlockCur`: P1's `CanBlock` of the current thread at a resumed
  entry from `JAtZ` (as XTopJointFaultRecv's).
* The blocking receive: XTopJointRecvSigBlock (`JAtZ.recvSigBlockJ`) and
  XTopJointRecvSigRet (`JAtZ.recvSigRetJ`, `jRecvSigHyp_of`, `dispatch_recvJS`).
-/
import Fl4Proofs.P3.XTopJointDispatch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- FL4's `receive_signal` on a non-active notification without blocking:
the badge register := 0. -/
theorem receive_signal_poll_eq {s : S} {a : A} {σ : Fl4Spec.State Unit} {N T E R : Set U64}
    {B : Set (U64 × Fl4Spec.Word)} (hR : IpcRel N T E R B (L.mem s) σ) {t n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b) :
    notification.receive_signal st arI s a t n false ⦃ r => r = (L.wr s (badgeRegA t) 0#u64, a) ⦄ := by
  have hx := hR.toN.at_ntfn hn hk
  have hst : stOf (L.mem s) n = obj.NTFN_IDLE ∨ stOf (L.mem s) n = obj.NTFN_WAITING := by
    have := hx.obj
    cases h : x.ntfnObj with
    | idleNtfn => exact Or.inl (stOf_idle (T := T) (h ▸ this) rfl)
    | waitingNtfn q => exact Or.inr (stOf_waiting (T := T) (h ▸ this) rfl)
    | activeNtfn b => exact absurd h (hna b)
  unfold notification.receive_signal
  refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
  rintro v rfl
  rw [epState_eq]
  rcases hst with hst | hst
  · rw [hst, if_pos rfl, if_neg (by simp)]
    refine WP.spec_bind (obj.Tcb.set_reg.spec s t layout.reg.BADGE 0#u64) ?_
    rintro s1 rfl
    rw [WP.spec_ok, badgeRegA_eq_regA, regIdx_badge]
  · rw [hst, if_neg (by rw [ntfn_consts.1, ntfn_consts.2.1]; decide), if_pos rfl, if_neg (by simp)]
    refine WP.spec_bind (obj.Tcb.set_reg.spec s t layout.reg.BADGE 0#u64) ?_
    rintro s1 rfl
    rw [WP.spec_ok, badgeRegA_eq_regA, regIdx_badge]

set_option maxHeartbeats 8000000 in
/-- **Polling a non-active notification at `J`** (module docstring). -/
theorem JAtZ.recvSigPollJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b) (cb : Fl4Spec.Badge) (cr : Fl4Spec.CapRights) :
    notification.receive_signal st arI s a t n false ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) false σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  refine WP.spec_mono (receive_signal_poll_eq (arI := arI) (a := a) hI.1 hn hk hna) ?_
  rintro r rfl
  obtain ⟨xt, hkt, -⟩ := hI.1.tcb t ht
  have hXb := badge_wr_irel J.ip hI ht hkt 0#u64
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V1, J1⟩ := J.regWrJ ht hkt Fl4Spec.badge_register 0#u64 hXb
  have hspec : Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) false σ =
      ({((), updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register (0#u64 : U64).bv)))}, False) := by
    rw [receiveSignal_notActive hk hna]
    unfold Fl4Spec.receiveSignalBlocked Fl4Spec.doNbrecvFailedTransfer
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [nd_bind_one (asUser_setRegister_eq _ _ hkt)]
    rfl
  rw [hspec, badgeRegA_eq_regA]
  exact ⟨_, Set.mem_singleton _, J1.xtop.relTop, _, _, _, _, _, _, J1⟩

/-- P1's `CanBlock` of the current thread, runnable, in no queue, not the
idle thread, at a resumed entry or after a reschedule became pending when the
thread has no SC (a receive after `maybe_return_sched_context`,
XTopJointRecvIpcRet). -/
theorem JAtZ.canBlockCurG {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (hrn : Fl4Spec.runnable x.tcbState = true)
    (hti : σ.curThread ≠ σ.idleThread) (hnr : ct.bv ∉ σ.releaseQueue)
    (hsa : σ.schedulerAction = .resumeCurThread ∨
      (σ.schedulerAction = .chooseNewThread ∧ x.tcbSchedContext = none))
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) :
    P1.CanBlock st (P1.Heap.tcbs H) Ac s ct := by
  have hS := J.xtop.fin.1.1.1
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨Q, R, hcq, hs⟩ := hS.lists
  have htH : ct ∈ P1.Heap.tcbs H := J.zH.1 ct ht
  have hnq' : ∀ d p, ct.bv ∉ σ.readyQueues d p := by rw [← hcur]; exact hnq
  obtain ⟨bq, br⟩ := J.curBits ht hnq' hnr
  have hsw : ∀ u, σ.schedulerAction = .switchThread u → u ≠ ct.bv := fun u hu => by
    rcases hsa with h | ⟨h, -⟩ <;> rw [h] at hu <;> cases hu
  obtain ⟨hna, -⟩ := J.words_of_spec ht hsw (fun e => hti (by rw [hcur, e]))
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb ct ht
  rw [hk] at hk0; cases hk0
  have hv : (L.mem s (P1.stA ct)).val = tsCode x.tcbState := by
    rw [P1.stA_eq, ← tStA_eq]; exact hTR.st
  obtain ⟨hnb, hnrp⟩ := P1.run_word (w := L.mem s (P1.stA ct)) (by rw [hv]; exact runnable_code hrn)
  have hcw : L.curW s = ct := by
    apply P1.eq_of_bv
    rw [← hcur, hs.curThread]
    unfold P1.LawfulStore.curW nodeW; rw [hcq.cur]
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  refine ⟨htH, hnb, hnrp, bq, br, hna, ?_, ?_⟩
  · intro h
    have ei : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
      unfold P1.LawfulStore.idleW nodeW; rw [hcq.cur]
    exact hti (by rw [hcur, hs.idleTh, ← ei, h])
  · rcases hsa with hres | ⟨-, hsc0⟩
    · have ha0 : L.actionW s = 0#u64 := by
        have h := hS.act
        rw [hres] at h
        unfold P1.LawfulStore.actionW; rw [hcq.cur]; exact h
      exact fun h1 => hB0.sact ct htH (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha0, hcw⟩))))) h1
    · intro h1
      obtain ⟨xt0, hkt0, -, -, hsct, -⟩ := hs.tcb ct ht
      rw [hk] at hkt0; cases hkt0
      rw [hsc0] at hsct
      exact absurd (optRef_none hsct.symm) h1

/-- P1's `CanBlock` of the current thread at a resumed entry (runnable, in no
ready queue). -/
theorem JAtZ.canBlockCur {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (hrn : Fl4Spec.runnable x.tcbState = true)
    (hni : Entered σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) :
    P1.CanBlock st (P1.Heap.tcbs H) Ac s ct :=
  J.canBlockCurG ht hcur hk hrn hni.1 (by rw [← hcur]; exact (J.curInv (by rw [hni.2]; intro e; cases e)).notRel)
    (Or.inl hni.2) hnq

/-- FL4's `maybe_donate_sched_context` for a thread with an SC: nothing. -/
theorem maybe_donate_hasSc {s : S} {a : A} {t n : U64} (h0 : L.mem s (P1.scA t) ≠ 0#u64) :
    notification.maybe_donate_sched_context st arI s a t n = ok (s, a) := by
  unfold notification.maybe_donate_sched_context
  rw [spec_eq_ok (P1.obj.Tcb.sc.spec s t), bind_ok, if_neg h0]

/-- The state after the two writes of `receive_signal` on an active
notification: the badge register, then the notification's state idle. -/
def recvActS (st : machine.Store S) [L : P1.LawfulStore st] (s : S) (t n : U64) : S :=
  L.wr (L.wr s (regA t (regIdx Fl4Spec.badge_register)) (L.mem s (nBadgeA n))) (P1.epTSA n)
    ((L.mem (L.wr s (regA t (regIdx Fl4Spec.badge_register)) (L.mem s (nBadgeA n))) (P1.epTSA n) &&& ~~~3#u64) |||
      (obj.NTFN_IDLE &&& 3#u64))

/-- FL4's `receive_signal` on an active notification for a thread whose SC
is the current SC (after the writes): the two writes. -/
theorem receive_signal_active_eq {s : S} {a : A} {t n : U64} (blk : Bool)
    (hst : stOf (L.mem s) n = obj.NTFN_ACTIVE)
    (h0 : L.mem (recvActS st s t n) (P1.scA t) ≠ 0#u64)
    (hc : L.mem (recvActS st s t n) (P1.scA t) =
      Sched.nodeW st (recvActS st s t n) (L.cpu (recvActS st s t n)) layout.node.CUR_SC) :
    notification.receive_signal st arI s a t n blk ⦃ r => r = (recvActS st s t n, a) ⦄ := by
  unfold recvActS at h0 hc ⊢
  rw [regIdx_badge] at h0 hc ⊢
  unfold notification.receive_signal
  refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
  rintro v rfl
  rw [epState_eq, hst, if_neg (by rw [ntfn_consts.1, ntfn_consts.2.2]; decide),
    if_neg (by rw [ntfn_consts.2.1, ntfn_consts.2.2]; decide)]
  refine WP.spec_bind (obj.Ntfn.badge.spec s n) ?_
  rintro b rfl
  refine WP.spec_bind (obj.Tcb.set_reg.spec s t layout.reg.BADGE _) ?_
  rintro s1 rfl
  refine WP.spec_bind (obj.Ntfn.set_state.spec _ n obj.NTFN_IDLE) ?_
  rintro s2 rfl
  rw [maybe_donate_hasSc h0, bind_ok]
  refine WP.spec_bind (P1.obj.Tcb.sc.spec _ t) ?_
  rintro i rfl
  refine WP.spec_bind (Sched.sched.cur_sc.spec' _) ?_
  rintro c rfl
  rw [Sched.sc_ne_eq, bind_ok, hc]
  simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]

/-- The spec's tail of `receive_signal` (active) for a thread whose SC is the
current SC: nothing. -/
theorem specRecvTail_cur {σ : Fl4Spec.State Unit} {t n : Fl4Spec.ObjRef} {xt : Fl4Spec.Tcb}
    (hkt : σ.kheap t = some (.tcb xt)) (hsc : xt.tcbSchedContext = some σ.curSc)
    {y : Fl4Spec.SchedContext} {m : Nat} (hks : σ.kheap σ.curSc = some (.schedContext y m)) :
    specRecvTail t n σ = ({((), σ)}, False) := by
  have h1 : Fl4Spec.maybeDonateSc (Z := Unit) t n σ = ({((), σ)}, False) := by
    unfold Fl4Spec.maybeDonateSc Fl4Spec.getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hkt), hsc]
    simp only [Fl4Spec.NonDet.when, reduceCtorEq, ↓reduceIte]
    rfl
  unfold specRecvTail
  rw [nd_bind_one h1]
  unfold Fl4Spec.getTcbObjRef
  rw [nd_bind_one (threadGet_eq _ hkt), hsc, Sched.ifSporadic_some hks, ite_f (by simp)]

set_option maxHeartbeats 16000000 in
/-- **Receiving from an active notification at `J`** (module docstring): the
current thread, resumed. -/
theorem JAtZ.recvSigActiveJ (hAT : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv)
    (hni : Entered σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0) (blk : Bool) (cb : Fl4Spec.Badge)
    (cr : Fl4Spec.CapRights) :
    notification.receive_signal st arI s a t n blk ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) blk σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hC : CurInv σ := J.curInv (by rw [hni.2]; intro e; cases e)
  obtain ⟨xt, hkt, -⟩ := hI.1.tcb t ht
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
  -- the spec's outcome
  have hspec : Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) blk σ =
      specRecvTail t.bv n.bv (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
        (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))) := by
    rw [receiveSignal_cap hk]
    simp only [hact]
    rw [nd_bind_one (asUser_setRegister_eq _ _ hkt), nd_bind_one (setNotification_eq _ hk1)]
  have hct : σ.curSc ≠ t.bv := fun e => by rw [e, hkt] at hks; cases hks
  have hcn : σ.curSc ≠ n.bv := fun e => by rw [e, hk] at hks; cases hks
  rw [hspec, specRecvTail_cur hkt2' hscc (y := ys) (m := ms) (by simp [updK, hct, hcn, hks]), heq, WP.spec_ok]
  exact ⟨_, Set.mem_singleton _, J2.xtop.relTop, _, _, _, _, _, _, J2⟩

end

end

end Fl4Proofs.P3
