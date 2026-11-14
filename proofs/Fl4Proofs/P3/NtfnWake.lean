/-
P3 (DESIGN.md §9), notifications: **`send_signal` wakes a thread**, refining
l4v `send_signal` (`Z = Unit`) relative to `SchedHyps` (NtfnSched.lean):

* `send_signal_waiting`: on a waiting notification, the first waiter is
  dequeued (the notification becomes idle if it was the last), set
  running, gets the badge in its badge register, then the scheduler tail;
* `send_signal_idle_bound_recv`: on an idle notification whose bound TCB is
  blocked on a receive, its IPC is cancelled, then the same wake-up.

From states related by `NtfnStateRel` and `SR`, the spec does not fail and
every FL4 outcome is related to one of the spec's outcomes.
-/
import Fl4Proofs.P3.NtfnSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Notif
open fl4_core Fl4Proofs.P1

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T : Set U64}
  {SR : S → Fl4Spec.State Unit → Prop}

/-- The spec's notification after dequeuing `d` from the waiting queue
`xs`. -/
def afterDequeue (x : Fl4Spec.Notification) (d : U64) : Fl4Spec.Notification :=
  Fl4Spec.ntfnObjUpdate (fun _ =>
    match Fl4Spec.removeAll d.bv (Fl4Spec.ntfnQueueOf x) with
    | [] => Fl4Spec.Ntfn.idleNtfn
    | _ => Fl4Spec.Ntfn.waitingNtfn (Fl4Spec.removeAll d.bv (Fl4Spec.ntfnQueueOf x))) x

/-- After `ntfn_dequeue` of the head of a waiting notification: related to
the spec's `tcb_ntfn_dequeue`, and the dequeued TCB is in no queue. -/
theorem rel_after_dequeue {s s1 : S} {σ : Fl4Spec.State Unit}
    (hR : NtfnStateRel N T (L.mem s) σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {xs : List U64} (hxs : x.ntfnObj = .waitingNtfn (xs.map UScalar.bv))
    (hQ : QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs) (hB : ∀ y ∈ xs, BlockedOn (L.mem s) n y)
    {d : U64} (hd : d ∈ xs)
    (h1 : QueueRel (L.mem s1) T .Ep (qOf (L.mem s1) n) (xs.erase d))
    (h2 : stOf (L.mem s1) n = (if xs.erase d = [] then 0#u64 else stOf (L.mem s) n))
    (h3 : QKeeps st N T n xs s s1) (hst : stOf (L.mem s) n = 1#u64) :
    NtfnStateRel N T (L.mem s1) (updK σ n.bv (.notification (afterDequeue x d))) ∧
      ∀ n' ∈ N, ∀ z, (updK σ n.bv (.notification (afterDequeue x d))).kheap n'.bv = some (.notification z) →
        d.bv ∉ z.ntfnObj.ntfnQueue := by
  have hx := hR.at_ntfn hn hk
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
  have hR1 := hR.upd_ntfn hn (afterDequeue x d) h3.ntfn h3.tcb
    (fun y hy hb => h3.links y hy (fun hyx => hb (hB y hyx).2))
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
    obtain ⟨-, -, hb'⟩ := (hR.at_ntfn hn' hz0).obj.blocked hdz
    exact e (hb'.symm.trans (hB d hd).2)

theorem the_head {α : Type} [Nonempty α] (a : α) (l : List α) : Fl4Spec.the (a :: l).head? = a := rfl

/-- **Waiting**: the first waiter is woken with the badge. -/
theorem send_signal_waiting (hH : SchedHyps st ar N T SR) (hP : NPlaced T N) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : NtfnStateRel N T (L.mem s) σ) (hSR : SR s σ) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) {q : List Fl4Spec.ObjRef}
    (hw : x.ntfnObj = .waitingNtfn q) (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r => ¬ (Fl4Spec.sendSignal n.bv badge.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendSignal n.bv badge.bv σ).1 ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ntfn hn hk
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
  refine WP.spec_bind (ntfn_dequeue_full hP s hn d _ hQ hd) ?_
  rintro s1 ⟨h1, h2, h3⟩
  obtain ⟨hR1, hq1⟩ := rel_after_dequeue hR hn hk hw hQ hB hd h1 h2 h3 hst
  have hSR1 := hH.stable _ _ _ _ hSR h3.foot (NtfnStep.ntfn (y := afterDequeue x d) hk rfl rfl)
    (NoBlock.ntfnUpd _ _ _)
  have hk1 : σ1.kheap d.bv = some (.tcb xd) := by
    have : d.bv ≠ n.bv := by intro e; rw [e, hk] at hkd; cases hkd
    simp [σ1, this, hkd]
  have hcls : inClass xd.tcbState ∨ RelIfBound σ1 d.bv := by
    left; right
    have h6 := (hB d hd).1
    have := (hR.at_tcb hdT hkd).st
    rw [h6] at this
    exact tsCode_six' this.symm
  have hnr : Fl4Spec.runnable xd.tcbState = false := by
    obtain ⟨m, hm⟩ : ∃ m, xd.tcbState = .blockedOnNotification m := by
      have h6 := (hB d hd).1
      have := (hR.at_tcb hdT hkd).st
      rw [h6] at this
      exact tsCode_six' this.symm
    rw [hm]; rfl
  exact wake_refines hH hP s1 a σ1 hR1 hSR1 hdT hn hk1 hq1 badge hcls hnr

/-- **Idle, bound TCB blocked on a receive**: its IPC is cancelled, then it
is woken with the badge. -/
theorem send_signal_idle_bound_recv (hH : SchedHyps st ar N T SR) (hP : NPlaced T N) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : NtfnStateRel N T (L.mem s) σ) (hSR : SR s σ) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn)
    {t : Fl4Spec.ObjRef} {tcb : Fl4Spec.Tcb} (hb : x.ntfnBoundTcb = some t) (hkt : σ.kheap t = some (.tcb tcb))
    (hrb : Fl4Spec.receiveBlocked tcb.tcbState = true) (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r => ¬ (Fl4Spec.sendSignal n.bv badge.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendSignal n.bv badge.bv σ).1 ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ntfn hn hk
  obtain ⟨hb0, hbt⟩ := optRef_some (hx.bound ▸ hb)
  subst hbt
  have hiT := hx.bound_mem hb0
  have hy := hR.at_tcb hiT hkt
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
  simp only [i1_post, hs3, ↓reduceIte]
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
    obtain ⟨-, h6, -⟩ := (hR1.at_ntfn hn' hz).obj.blocked hm
    have := (hR1.at_tcb hiT hk1).st
    rw [hin, h6] at this
    cases this
  exact wake_refines hH hP s1 a1 σ1 hR1 hSR1 hiT hn hk1 hq1 badge (Or.inr hrb1) (by rw [hin]; rfl)

end

end

end Fl4Proofs.P3.Notif
