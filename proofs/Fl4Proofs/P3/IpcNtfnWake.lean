/-
P3 (DESIGN.md §9), IPC: **`send_signal` waking a thread on the merged
relation** (NtfnWake.lean with `IpcRel` and `IpcSchedHyps`): the waiting
case (`ntfn_dequeue` writes only the notification's queue words and the
waiters' links, `QKeeps.agree`) and the idle case with a bound TCB blocked on
a receive (`IpcSchedHyps.cancelIpc`). The woken thread's state is 6 or 0,
so it is in no endpoint queue either.
-/
import Fl4Proofs.P3.IpcNtfnSched
import Fl4Proofs.P3.NtfnWake
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Notif
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- After `ntfn_dequeue` of the head of a waiting notification: related to
the spec's `tcb_ntfn_dequeue`, and the dequeued TCB is in no queue. -/
theorem rel_after_dequeueI (hP : IPlaced N T E R B) {s s1 : S} {σ : Fl4Spec.State Unit}
    (hR : IpcRel N T E R B (L.mem s) σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {xs : List U64} (hxs : x.ntfnObj = .waitingNtfn (xs.map UScalar.bv))
    (hQ : QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs) (hB : ∀ y ∈ xs, BlockedOn (L.mem s) n y)
    {d : U64} (hd : d ∈ xs)
    (h1 : QueueRel (L.mem s1) T .Ep (qOf (L.mem s1) n) (xs.erase d))
    (h2 : stOf (L.mem s1) n = (if xs.erase d = [] then 0#u64 else stOf (L.mem s) n))
    (h3 : QKeeps st N T n xs s s1) (hst : stOf (L.mem s) n = 1#u64) :
    IpcRel N T E R B (L.mem s1) (updK σ n.bv (.notification (afterDequeue x d))) ∧
      ∀ n' ∈ N, ∀ z, (updK σ n.bv (.notification (afterDequeue x d))).kheap n'.bv = some (.notification z) →
        d.bv ∉ z.ntfnObj.ntfnQueue := by
  have hx := hR.toN.at_ntfn hn hk
  have hrm : Fl4Spec.removeAll d.bv (Fl4Spec.ntfnQueueOf x) = (xs.erase d).map UScalar.bv := by
    show Fl4Spec.removeAll d.bv x.ntfnObj.ntfnQueue = _
    rw [hxs]; exact removeAll_map hQ.nodup d
  have hobj : NtfnObjRel (L.mem s1) T n (afterDequeue x d).ntfnObj := by
    show NtfnObjRel _ T n (match Fl4Spec.removeAll d.bv (Fl4Spec.ntfnQueueOf x) with
      | [] => Fl4Spec.Ntfn.idleNtfn
      | _ => Fl4Spec.Ntfn.waitingNtfn (Fl4Spec.removeAll d.bv (Fl4Spec.ntfnQueueOf x)))
    rw [hrm]
    cases he : xs.erase d with
    | nil =>
      rw [he] at h1 h2
      exact ⟨by rw [h2]; rfl, h1⟩
    | cons y ys =>
      rw [he] at h1 h2
      simp only [List.map_cons]
      refine ⟨by rw [h2]; simpa using hst, y :: ys, List.cons_ne_nil _ _, rfl, h1, fun z hz => ?_⟩
      have hz' : z ∈ xs := by
        have : z ∈ xs.erase d := by rw [he]; exact hz
        exact List.mem_of_mem_erase this
      obtain ⟨e1, e2⟩ := hB z hz'
      exact ⟨(h3.tcb z (hQ.mem z hz')).st ▸ e1, (h3.tcb z (hQ.mem z hz')).blk ▸ e2⟩
  have hR1 := hR.upd_ntfn hP hn (afterDequeue x d) (fun b hb ⟨_, hnw, hnl⟩ => h3.agree b hb
      (fun w hw => by
        have hwa := hP.e.tcb w (hQ.mem w hw)
        refine ⟨fun e => hnl ⟨w, hQ.mem w hw, (hB w hw).2, Or.inl (by rw [e, val_next hwa])⟩,
          fun e => hnl ⟨w, hQ.mem w hw, (hB w hw).2, Or.inr (by rw [e, val_prev hwa])⟩⟩)
      (fun e => hnw (e ▸ (nw_words hP hn).1)) (fun e => hnw (e ▸ (nw_words hP hn).2.1)))
    ⟨hobj, by rw [h3.bound]; exact hx.bound, by rw [h3.bound]; exact hx.bound_mem,
      by rw [h3.sc]; exact hx.sc⟩
  refine ⟨hR1, fun n' hn' z hz hdz => ?_⟩
  by_cases e : n' = n
  · subst e
    simp only [updK_kheap, Function.update_self, Option.some.injEq, Fl4Spec.KernelObject.notification.injEq] at hz
    subst hz
    have := hobj
    revert hdz
    show d.bv ∉ (match Fl4Spec.removeAll d.bv (Fl4Spec.ntfnQueueOf x) with
      | [] => Fl4Spec.Ntfn.idleNtfn
      | _ => Fl4Spec.Ntfn.waitingNtfn (Fl4Spec.removeAll d.bv (Fl4Spec.ntfnQueueOf x))).ntfnQueue
    rw [hrm]
    have hnd : d ∉ xs.erase d := hQ.nodup.not_mem_erase
    cases he : xs.erase d with
    | nil => simp [Fl4Spec.Ntfn.ntfnQueue]
    | cons y ys =>
      rw [he] at hnd
      simp only [List.map_cons, Fl4Spec.Ntfn.ntfnQueue]
      intro hm
      rw [← List.map_cons] at hm
      obtain ⟨w, hw, hwd⟩ := List.mem_map.1 hm
      exact hnd (eq_of_bv hwd ▸ hw)
  · have hz0 : σ.kheap n'.bv = some (.notification z) := by
      simpa [updK_kheap, bv_inj e] using hz
    obtain ⟨-, -, hb'⟩ := (hR.toN.at_ntfn hn' hz0).obj.blocked hdz
    exact e (hb'.symm.trans (hB d hd).2)

/-- **Waiting**: the first waiter is woken with the badge. -/
theorem send_signal_waitingI (hH : IpcSchedHyps st ar N T E R B SR) (hP : IPlaced N T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) {q : List Fl4Spec.ObjRef}
    (hw : x.ntfnObj = .waitingNtfn q) (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r => ¬ (Fl4Spec.sendSignal n.bv badge.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendSignal n.bv badge.bv σ).1 ∧ IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.toN.at_ntfn hn hk
  have hobj := hx.obj
  rw [hw] at hobj
  obtain ⟨hst, xs, hne, rfl, hQ, hB⟩ := hobj
  obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hd : d ∈ d :: rest := List.mem_cons_self
  have hdT : d ∈ T := hQ.mem d hd
  obtain ⟨xd, hkd, -⟩ := hR.tcb d hdT
  -- the spec
  have hmem : d.bv ∈ Fl4Spec.ntfnQueueOf x := by
    show d.bv ∈ x.ntfnObj.ntfnQueue
    rw [hw]; simp [Fl4Spec.Ntfn.ntfnQueue]
  set σ1 := updK σ n.bv (.notification (afterDequeue x d))
  have hspec : Fl4Spec.sendSignal n.bv badge.bv σ = specWake d.bv n.bv badge.bv σ1 := by
    unfold Fl4Spec.sendSignal
    rw [nd_bind_one (getNotification_eq hk)]
    simp only [hw]
    unfold Fl4Spec.updateWaitingNtfn
    rw [nd_bind_one (assert_true (by simp) σ), nd_pure_bind', List.map_cons, the_head,
      nd_bind_one (tcbNtfnDequeue_eq hk hmem)]
    rfl
  rw [hspec]
  -- FL4
  unfold notification.send_signal
  step
  have hsw : st = obj.NTFN_WAITING := by rw [st_post]; exact stOf_waiting (q := _) hx.obj hw
  simp only [hsw, ntfn_consts.1, ntfn_consts.2.1, show (1#u64 : U64) ≠ 0#u64 by decide, ↓reduceIte]
  step
  have hqh : q.head = d := by rw [q_post, epQ_eq, hQ.head]; rfl
  rw [hqh]
  refine WP.spec_bind (ntfn_dequeue_full hP.n s hn d _ hQ hd) ?_
  rintro s1 ⟨h1, h2, h3⟩
  obtain ⟨hR1, hq1⟩ := rel_after_dequeueI hP hR hn hk hw hQ hB hd h1 h2 h3 hst
  have hSR1 := hH.stableN _ _ _ _ hSR h3.foot (NtfnStep.ntfn (y := afterDequeue x d) hk rfl rfl)
    (NoBlock.ntfnUpd _ _ _)
  have hk1 : σ1.kheap d.bv = some (.tcb xd) := by
    have : d.bv ≠ n.bv := by intro e; rw [e, hk] at hkd; cases hkd
    simp [σ1, this, hkd]
  have hcls : inClassR xd.tcbState xd.tcbFault ∨ RelIfBound σ1 d.bv := by
    left; right; left
    have h6 := (hB d hd).1
    have := (hR.toN.at_tcb hdT hkd).st
    rw [h6] at this
    exact tsCode_six' this.symm
  have hnr : Fl4Spec.runnable xd.tcbState = false := by
    obtain ⟨m, hm⟩ : ∃ m, xd.tcbState = .blockedOnNotification m := by
      have h6 := (hB d hd).1
      have := (hR.toN.at_tcb hdT hkd).st
      rw [h6] at this
      exact tsCode_six' this.symm
    rw [hm]; rfl
  have hni : xd.tcbState ≠ .idleThreadState := by
    obtain ⟨m, hm⟩ : ∃ m, xd.tcbState = .blockedOnNotification m := by
      have h6 := (hB d hd).1
      have := (hR.toN.at_tcb hdT hkd).st
      rw [h6] at this
      exact tsCode_six' this.symm
    rw [hm]; exact fun h => by cases h
  have hqE := IpcRel.not_ep_queued hR1 (t := d) (by
    rw [(h3.tcb d hdT).st, (hB d hd).1]; decide)
  exact wake_refinesI hH hP s1 a σ1 hR1 hSR1 hdT hn hk1 hq1 hqE badge hcls hnr hni

/-- **Idle, bound TCB blocked on a receive**: its IPC is cancelled, then it
is woken with the badge. -/
theorem send_signal_idle_bound_recvI (hH : IpcSchedHyps st ar N T E R B SR) (hP : IPlaced N T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn)
    {t : Fl4Spec.ObjRef} {tcb : Fl4Spec.Tcb} (hb : x.ntfnBoundTcb = some t) (hkt : σ.kheap t = some (.tcb tcb))
    (hrb : Fl4Spec.receiveBlocked tcb.tcbState = true) (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r => ¬ (Fl4Spec.sendSignal n.bv badge.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendSignal n.bv badge.bv σ).1 ∧ IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.toN.at_ntfn hn hk
  obtain ⟨hb0, hbt⟩ := optRef_some (hx.bound ▸ hb)
  subst hbt
  have hiT := hx.bound_mem hb0
  have hy := hR.toN.at_tcb hiT hkt
  have hs3 : L.mem s (tStA (L.mem s (nBoundA n))) = sched.TS_BLOCKED_ON_RECV := by
    have h3 := hy.st
    rw [tsVals.2.2.1]
    apply UScalar.eq_of_val_eq
    revert hrb h3
    cases tcb.tcbState <;> simp [tsCode, Fl4Spec.receiveBlocked]
  unfold notification.send_signal
  step
  have : st = obj.NTFN_IDLE := by rw [st_post]; exact stOf_idle hx.obj hidle
  simp only [this, ↓reduceIte]
  step
  step
  subst i_post
  simp only [b_post, hb0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step
  have hs3' : i1 = sched.TS_BLOCKED_ON_RECV := by rw [i1_post]; exact hs3
  simp only [hs3', ↓reduceIte]
  refine WP.spec_bind (hH.cancelIpc s a σ _ tcb hR hSR hiT hkt hrb) ?_
  rintro ⟨s1, a1⟩ ⟨σ1, x1, hc, hR1, hSR1, hk1, hin, hrb1⟩
  have hspec : Fl4Spec.sendSignal n.bv badge.bv σ = specWake (L.mem s (nBoundA n)).bv n.bv badge.bv σ1 := by
    unfold Fl4Spec.sendSignal
    rw [nd_bind_one (getNotification_eq hk)]
    simp only [hidle, hb]
    rw [nd_bind_one (getThreadState_eq hkt)]
    simp only [hrb, ↓reduceIte]
    rw [nd_bind_one hc]
    rfl
  rw [hspec]
  have hq1 : ∀ n' ∈ N, ∀ z, σ1.kheap n'.bv = some (.notification z) →
      (L.mem s (nBoundA n)).bv ∉ z.ntfnObj.ntfnQueue := by
    intro n' hn' z hz hm
    obtain ⟨-, h6, -⟩ := (hR1.toN.at_ntfn hn' hz).obj.blocked hm
    have := (hR1.toN.at_tcb hiT hk1).st
    rw [hin, h6] at this
    cases this
  have hqE := IpcRel.not_ep_queued hR1 (t := L.mem s (nBoundA n)) (by
    rw [(hR1.toN.at_tcb hiT hk1).st, hin]; decide)
  exact wake_refinesI hH hP s1 a1 σ1 hR1 hSR1 hiT hn hk1 hq1 hqE badge (Or.inr hrb1) (by rw [hin]; rfl)
    (by rw [hin]; exact fun h => by cases h)

end

end

end Fl4Proofs.P3.Notif
