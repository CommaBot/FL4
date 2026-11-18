/-
P3 (DESIGN.md §9), IPC: **the scheduler invariants across a notification's
`cancel_all_signals`** (spec side only), toward `JAtZ` after a notification
cap's deletion (`JStepHyps.del`).

One thread of the loop (`remove_and_restart_ntfn_queued_thread`), the head
`t` of the notification's queue, blocked on it:

* the dequeue (`Inv.updNtfn`), the restart (`Inv.stable`: blocked on a
  notification, hence `inClass`, to `Restart`), `stsAct` (`QChange`);
* the sporadic check of `t`'s SC (`Inv.unblockTail`: `t` is in no release
  queue, being blocked; its SC active, `BlockedScActive`);
* `possible_switch_to t` (`possibleSwitchTo_qchange` when `t` is
  schedulable; otherwise nothing: its SC, active, kept active by the check,
  `MaxK.mk_unblock`).

`BlockedScActive` after: `t` is no longer blocked; the other threads and the
SCs other than `t`'s are kept; `t`'s SC changes its refills only
(`unblockCur_some`, the check deterministic).

`inv_ntfn_iter`: one thread; `inv_cancelAllSignals`: the loop and the
reschedule (`rescheduleRequired_qchange`).
-/
import Fl4Proofs.P3.SpecFinOut
import Fl4Proofs.P3.ScInvR
import Fl4Proofs.P3.SpecDet
import Fl4Proofs.P3.ScMaxKeep
import Fl4Proofs.P3.IpcEpTail
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- The facts the loop carries: `Inv`, `BlockedScActive`, the queued threads
blocked on the notification. -/
def NtfnLoopInv (σ : State Unit) (r : ObjRef) (l : List ObjRef) : Prop :=
  Inv σ ∧ BlockedScActive σ ∧ (∃ n, σ.kheap r = some (.notification n) ∧ ntfnQueueOf n = l) ∧ l.Nodup ∧
    ∀ u ∈ l, ∃ x, σ.kheap u = some (.tcb x) ∧ x.tcbState = .blockedOnNotification r

theorem mem_singleton_snd {α : Type} {a b : α × State Unit} (h : a ∈ ({b} : Set (α × State Unit))) : a.2 = b.2 := by
  rw [Set.mem_singleton_iff.1 h]

/-! ### The spec's frame of the finalisation -/

/-- The state's fields other than the heap, the action, the ready queues and
the timer flag, kept. -/
structure Sk (σ σ' : State Unit) : Prop where
  ct : σ'.curThread = σ.curThread
  idle : σ'.idleThread = σ.idleThread
  cons : σ'.consumedTime = σ.consumedTime
  tm : σ'.curTime = σ.curTime
  csc : σ'.curSc = σ.curSc
  rel : σ'.releaseQueue = σ.releaseQueue
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap
  arch : σ'.archState = σ.archState
  dt : σ'.domainTime = σ.domainTime

theorem Sk.refl (σ : State Unit) : Sk σ σ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Sk.trans {σ1 σ2 σ3 : State Unit} (h1 : Sk σ1 σ2) (h2 : Sk σ2 σ3) : Sk σ1 σ3 :=
  ⟨h2.ct.trans h1.ct, h2.idle.trans h1.idle, h2.cons.trans h1.cons, h2.tm.trans h1.tm, h2.csc.trans h1.csc,
    h2.rel.trans h1.rel, h2.cdt.trans h1.cdt, h2.orig.trans h1.orig, h2.arch.trans h1.arch, h2.dt.trans h1.dt⟩

/-- A notification object kept, or a non-waiting one replaced by a
non-waiting one. -/
def NObj (a b : Ntfn) : Prop := b = a ∨ ((∀ l, a ≠ .waitingNtfn l) ∧ ∀ l, b ≠ .waitingNtfn l)

theorem NObj.trans {a b c : Ntfn} (h1 : NObj a b) (h2 : NObj b c) : NObj a c := by
  rcases h1 with rfl | ⟨ha, hb⟩ <;> rcases h2 with rfl | ⟨hb', hc⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hb', hc⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hc⟩

theorem NObj.nw {a b : Ntfn} (h : NObj a b) (ha : ∀ l, a ≠ .waitingNtfn l) : ∀ l, b ≠ .waitingNtfn l := by
  rcases h with rfl | ⟨-, hb⟩
  · exact ha
  · exact hb

/-- `NObj` keeps the queue empty or the same. -/
theorem NObj.queue {a b : Ntfn} (h : NObj a b) : b.ntfnQueue.Sublist a.ntfnQueue := by
  rcases h with rfl | ⟨ha, hb⟩
  · exact List.Sublist.refl _
  · cases b with
    | waitingNtfn l => exact absurd rfl (hb l)
    | _ => exact List.nil_sublist _

/-- **A TCB's state and saved context by a notification `r`'s step**: kept,
or (`q = false`) a thread blocked on `r` restarted (`cancel_all_signals`) or
woken running with its context changed (`send_signal`: the badge register). -/
def TChg (q : Bool) (r : ObjRef) (x : Tcb) (st : ThreadState) (ar : ArchTcb) : Prop :=
  (st = x.tcbState ∧ ar = x.tcbArch) ∨
    (q = false ∧ x.tcbState = .blockedOnNotification r ∧ (st = .restart ∨ st = .running))

theorem TChg.trans {q : Bool} {r : ObjRef} {x : Tcb} {st1 st2 : ThreadState} {ar1 ar2 : ArchTcb}
    (h1 : TChg q r x st1 ar1) {bn1 : Option ObjRef}
    (h2 : TChg q r { x with tcbState := st1, tcbBoundNotification := bn1, tcbArch := ar1 } st2 ar2) :
    TChg q r x st2 ar2 := by
  rcases h2 with ⟨e1, e2⟩ | ⟨hq2, e1, e7⟩ <;> rcases h1 with ⟨e3, e4⟩ | ⟨hq1, e5, e6⟩
  · exact Or.inl ⟨e1.trans e3, e2.trans e4⟩
  · exact Or.inr ⟨hq1, e5, by rw [e1]; exact e6⟩
  · simp only at e1
    exact Or.inr ⟨hq2, by rw [← e3]; exact e1, e7⟩
  · simp only at e1; rcases e6 with e | e <;> rw [e] at e1 <;> cases e1

/-- **One object's change by a notification `r`'s step** (`cur` the current
SC; `q`: no thread restarted or woken, no refill and no queue changed): a
TCB's state and context (`TChg`) and bound notification; an SC's refills
(not the current SC's) and notification; `r`'s queue (shorter) and SC
(cleared); a non-waiting object may become another non-waiting one (`NObj`:
a signal's badge). -/
def NChg (q : Bool) (r cur p : ObjRef) (o o' : KernelObject) : Prop :=
  (∃ x st bn ar, o = .tcb x ∧ o' = .tcb { x with tcbState := st, tcbBoundNotification := bn, tcbArch := ar } ∧
    TChg q r x st ar ∧ (bn = x.tcbBoundNotification ∨ bn = none)) ∨
  (∃ y n rf nt, o = .schedContext y n ∧ o' = .schedContext { y with scRefills := rf, scNtfn := nt } n ∧
    (p = cur ∨ q = true → rf = y.scRefills) ∧ (nt = y.scNtfn ∨ nt = none)) ∨
  (∃ x y, o = .notification x ∧ o' = .notification y ∧ p = r ∧
    y.ntfnObj.ntfnQueue.Sublist x.ntfnObj.ntfnQueue ∧ (q = true → NObj x.ntfnObj y.ntfnObj) ∧
    (y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none) ∧ ((∀ l, x.ntfnObj ≠ .waitingNtfn l) → NObj x.ntfnObj y.ntfnObj) ∧
    (y.ntfnBoundTcb = x.ntfnBoundTcb ∨ y.ntfnBoundTcb = none))

theorem or_none_trans {α : Type} {a b c : Option α} (h1 : b = a ∨ b = none) (h2 : c = b ∨ c = none) :
    c = a ∨ c = none := by
  rcases h2 with rfl | rfl
  · exact h1
  · exact Or.inr rfl

theorem NChg.trans {q : Bool} {r cur p : ObjRef} {o1 o2 o3 : KernelObject} (h1 : NChg q r cur p o1 o2)
    (h2 : NChg q r cur p o2 o3) : NChg q r cur p o1 o3 := by
  rcases h1 with ⟨x, st, bn, ar, rfl, rfl, hs, hb⟩ | ⟨y, n, rf, nt, rfl, rfl, hr, hn⟩ |
    ⟨x, y, rfl, rfl, hp, hq, hq', hs, hw, hb⟩
  · rcases h2 with ⟨x2, st2, bn2, ar2, e, rfl, hs2, hb2⟩ | ⟨_, _, _, _, e, -⟩ | ⟨_, _, e, -⟩ <;> cases e
    exact Or.inl ⟨x, st2, bn2, ar2, rfl, rfl, hs.trans hs2, or_none_trans hb hb2⟩
  · rcases h2 with ⟨_, _, _, _, e, -⟩ | ⟨y2, n2, rf2, nt2, e, rfl, hr2, hn2⟩ | ⟨_, _, e, -⟩ <;> cases e
    exact Or.inr (Or.inl ⟨y, n, rf2, nt2, rfl, rfl, fun h => (hr2 h).trans (hr h), or_none_trans hn hn2⟩)
  · rcases h2 with ⟨_, _, _, _, e, -⟩ | ⟨_, _, _, _, e, -⟩ | ⟨y2, z, e, rfl, -, hq2, hq2', hs2, hw2, hb2⟩ <;> cases e
    refine Or.inr (Or.inr ⟨x, z, rfl, rfl, hp, hq2.trans hq, fun h => (hq' h).trans (hq2' h),
      or_none_trans hs hs2, fun h => (hw h).trans (hw2 ((hw h).nw h)), or_none_trans hb hb2⟩)

theorem NChg.weak {r cur p : ObjRef} {o o' : KernelObject} (h : NChg true r cur p o o') : NChg false r cur p o o' := by
  rcases h with ⟨x, st, bn, ar, h1, h2, hs, hb⟩ | ⟨y, n, rf, nt, h1, h2, hr, hn⟩ | ⟨x, y, h1, h2, hp, hq, -, hs, hw, hb⟩
  · refine Or.inl ⟨x, st, bn, ar, h1, h2, ?_, hb⟩
    rcases hs with e | ⟨e, -⟩
    · exact Or.inl e
    · cases e
  · exact Or.inr (Or.inl ⟨y, n, rf, nt, h1, h2, fun _ => hr (Or.inr rfl), hn⟩)
  · exact Or.inr (Or.inr ⟨x, y, h1, h2, hp, hq, (fun h => by cases h), hs, hw, hb⟩)

/-- **The spec's frame of a notification `r`'s finalisation** (`NChg`). -/
structure NFr (q : Bool) (r : ObjRef) (σ σ' : State Unit) : Prop where
  sk : Sk σ σ'
  act : q = true → σ'.schedulerAction = σ.schedulerAction ∧ σ'.readyQueues = σ.readyQueues
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ o o', σ.kheap p = some o ∧ σ'.kheap p = some o' ∧ NChg q r σ.curSc p o o'

theorem NFr.refl (q : Bool) (r : ObjRef) (σ : State Unit) : NFr q r σ σ :=
  ⟨Sk.refl σ, fun _ => ⟨rfl, rfl⟩, fun _ => Or.inl rfl⟩

theorem NFr.trans {q : Bool} {r : ObjRef} {σ1 σ2 σ3 : State Unit} (h1 : NFr q r σ1 σ2) (h2 : NFr q r σ2 σ3) :
    NFr q r σ1 σ3 := by
  refine ⟨h1.sk.trans h2.sk, fun hq => ⟨(h2.act hq).1.trans (h1.act hq).1, (h2.act hq).2.trans (h1.act hq).2⟩,
    fun p => ?_⟩
  have hc2 : σ2.curSc = σ1.curSc := h1.sk.csc
  rcases h2.kh p with e2 | ⟨o2, o3, k2, k3, c2⟩
  · rw [e2]; exact h1.kh p
  · rw [hc2] at c2
    rcases h1.kh p with e1 | ⟨o1, o2', k1, k2', c1⟩
    · exact Or.inr ⟨o2, o3, by rw [← e1]; exact k2, k3, c2⟩
    · obtain rfl := Option.some.inj (k2'.symm.trans k2)
      exact Or.inr ⟨o1, o3, k1, k3, c1.trans c2⟩

theorem NFr.weak {r : ObjRef} {σ σ' : State Unit} (h : NFr true r σ σ') : NFr false r σ σ' :=
  ⟨h.sk, (fun e => by cases e), fun p => (h.kh p).imp_right fun ⟨o, o', h1, h2, h3⟩ => ⟨o, o', h1, h2, h3.weak⟩⟩

theorem NFr.ofSk {q : Bool} {r : ObjRef} {σ σ' : State Unit} (hs : Sk σ σ')
    (ha : q = true → σ'.schedulerAction = σ.schedulerAction ∧ σ'.readyQueues = σ.readyQueues)
    (hk : σ'.kheap = σ.kheap) : NFr q r σ σ' :=
  ⟨hs, ha, fun p => Or.inl (by rw [hk])⟩

theorem NFr.upd {q : Bool} {r : ObjRef} {σ : State Unit} {p : ObjRef} {o o' : KernelObject}
    (hk : σ.kheap p = some o) (hc : NChg q r σ.curSc p o o') : NFr q r σ (updK σ p o') := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, fun p' => ?_⟩
  by_cases e : p' = p
  · subst e; exact Or.inr ⟨o, o', hk, by simp [updK], hc⟩
  · exact Or.inl (by simp [updK, e])

theorem NFr.sts (r : ObjRef) (σ : State Unit) (t : ObjRef) : NFr false r σ (Notif.stsAct σ t) := by
  unfold Notif.stsAct; split
  · exact NFr.ofSk ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun e => by cases e) rfl
  · exact NFr.refl _ _ _

/-- Only the ready queues and the scheduler action changed. -/
def QOnly (σ σ' : State Unit) : Prop :=
  ∃ rq act, σ' = { σ with readyQueues := rq, schedulerAction := act }

theorem QOnly.nfr {r : ObjRef} {σ σ' : State Unit} (h : QOnly σ σ') : NFr false r σ σ' := by
  obtain ⟨rq, act, rfl⟩ := h
  exact NFr.ofSk ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun e => by cases e) rfl

/-- **`reschedule_required`'s outcome**: only the queues and the action
(`choose_new_thread`) changed. -/
theorem resched_q {σ : State Unit} (hA : ActReady σ) :
    ∃ σ', rescheduleRequired (Z := Unit) σ = ({((), σ')}, False) ∧ QOnly σ σ' ∧
      σ'.schedulerAction = .chooseNewThread := by
  cases ha : σ.schedulerAction with
  | switchThread t =>
    by_cases hs : schedulable t σ = true
    · obtain ⟨x, -, -, -, hk, -⟩ := schedulable_inv hs
      have he := tcbSchedAction_gen hk tcbSchedEnqueue
      exact ⟨_, rescheduleRequired_sched ha hs hA he,
        ⟨(setQ σ x.tcbDomain x.tcbPriority (tcbSchedEnqueue t (σ.readyQueues x.tcbDomain x.tcbPriority))).readyQueues,
          .chooseNewThread, rfl⟩, rfl⟩
    · exact ⟨_, rescheduleRequired_notsched ha (by simpa using hs), ⟨σ.readyQueues, .chooseNewThread, rfl⟩, rfl⟩
  | _ => exact ⟨_, rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h),
      ⟨σ.readyQueues, .chooseNewThread, rfl⟩, rfl⟩

/-- **`possible_switch_to`'s outcome**: only the queues and the action
changed. -/
theorem pst_q {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (hA : ActReady σ) :
    ∃ σ', possibleSwitchTo (Z := Unit) t σ = ({((), σ')}, False) ∧ QOnly σ σ' := by
  rw [possibleSwitchTo_unfold hk]
  split_ifs
  · exact ⟨_, tcbSchedAction_gen hk _,
      ⟨(setQ σ x.tcbDomain x.tcbPriority (tcbSchedEnqueue t (σ.readyQueues x.tcbDomain x.tcbPriority))).readyQueues,
        σ.schedulerAction, rfl⟩⟩
  · obtain ⟨σ1, he, ⟨rq, act, rfl⟩, -⟩ := resched_q hA
    have hk' : ({ σ with readyQueues := rq, schedulerAction := act } : State Unit).kheap t = some (.tcb x) := hk
    refine ⟨setQ { σ with readyQueues := rq, schedulerAction := act } x.tcbDomain x.tcbPriority
      (tcbSchedEnqueue t (rq x.tcbDomain x.tcbPriority)), by rw [nd_bind_one he, tcbSchedAction_gen hk' _],
      ⟨(setQ { σ with readyQueues := rq, schedulerAction := act } x.tcbDomain x.tcbPriority
        (tcbSchedEnqueue t (rq x.tcbDomain x.tcbPriority))).readyQueues, act, rfl⟩⟩
  · exact ⟨_, setAction_eq σ _, ⟨σ.readyQueues, _, rfl⟩⟩
  · exact ⟨σ, rfl, ⟨σ.readyQueues, σ.schedulerAction, rfl⟩⟩

/-- **The refill check of the current SC does nothing** (the guard
`asst = some true → scp ≠ cur_sc`). -/
theorem unblockCur_self {σ σ' : State Unit} {c : ObjRef} {y : SchedContext} {k : Nat}
    (hk : σ.kheap c = some (.schedContext y k)) (hc : c = σ.curSc)
    (hm : ((), σ') ∈ (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) (some c) σ).1) : σ' = σ := by
  unfold ifSporadicCurScAssertRefillUnblockCheck ifCondRefillUnblockCheck at hm
  simp only [NonDet.maybeM] at hm
  rw [nd_bind_one (getSchedContext_eq hk), nd_gets_bind, nd_pure_bind'] at hm
  simp only [NonDet.when] at hm
  split_ifs at hm with h1 h2
  · exact absurd hc (by simpa using h2)
  · exact mem_singleton_snd hm
  · exact mem_singleton_snd hm

set_option maxHeartbeats 8000000 in
/-- **One thread of `cancel_all_signals` keeps the loop's facts.** -/
theorem inv_ntfn_iter {σ σ5 : State Unit} {r t : ObjRef} {l : List ObjRef} (h : NtfnLoopInv σ r (t :: l))
    (hm : ((), σ5) ∈ (removeAndRestartNtfnQueuedThread (Z := Unit) t r σ).1) :
    NtfnLoopInv σ5 r l ∧ NFr false r σ σ5 := by
  obtain ⟨hI, hB, ⟨n, hk, hq⟩, hnd, hbl⟩ := h
  have htl : t ∉ l := (List.nodup_cons.1 hnd).1
  obtain ⟨x, hkt, hxs⟩ := hbl t (List.mem_cons_self ..)
  have hrt : r ≠ t := by rintro rfl; rw [hk] at hkt; cases hkt
  have htq : t ∈ ntfnQueueOf n := by rw [hq]; exact List.mem_cons_self ..
  -- t is in no release queue (blocked)
  have htrel : t ∉ σ.releaseQueue := fun hm' => by
    obtain ⟨x', -, -, -, h1, -, h3, -⟩ := hI.rel t hm'
    rw [hkt] at h1; cases h1; rw [hxs] at h3; cases h3
  -- t's SC, active (blocked on a notification)
  have hsa : ∀ p y k, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y k) → scActive y = true := by
    intro p y k hp hky
    obtain ⟨y', k', hky', hyt⟩ := hI.back t x p hkt hp
    rw [hky] at hky'; cases hky'
    exact hB.tcb p y k t x hky hyt hkt (by rw [hxs]; rfl)
  -- the dequeue
  set n1 : Notification := ntfnObjUpdate (fun _ =>
      match removeAll t (ntfnQueueOf n) with
      | [] => Ntfn.idleNtfn
      | _ => Ntfn.waitingNtfn (removeAll t (ntfnQueueOf n))) n with hn1
  have hdq := tcbNtfnDequeue_eq hk htq
  set σ1 := updK σ r (.notification n1) with hσ1
  have hI1 : Inv σ1 := hI.updNtfn hk (fun p hp => hI.ntfnSc r n p hk hp)
  have hkp1 : ∀ q, q ≠ r → σ1.kheap q = σ.kheap q := fun q hq => by simp [hσ1, updK, hq]
  have hkt1 : σ1.kheap t = some (.tcb x) := by rw [hkp1 t (Ne.symm hrt)]; exact hkt
  have hq1 : ntfnQueueOf n1 = l := by
    have hr : removeAll t (t :: l) = l := by
      unfold removeAll
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact List.filter_eq_self.2 fun a ha => by
        simp only [ne_eq, decide_eq_true_eq]; rintro rfl; exact htl ha
    rw [hn1, hq, hr]
    cases l <;> rfl
  -- the restart
  set x' : Tcb := { x with tcbState := .restart } with hx'
  set σ2' := updK σ1 t (.tcb x') with hσ2'
  have hkp2 : ∀ q, q ≠ t → σ2'.kheap q = σ1.kheap q := fun q hq => by simp [hσ2', updK, hq]
  have hkt2' : σ2'.kheap t = some (.tcb x') := by simp [hσ2', updK]
  have hI2' : Inv σ2' := by
    refine hI1.stable (NtfnStep.tcb hkt1 .restart x.tcbArch) fun p y z hy hz => ?_
    by_cases e : p = t
    · subst e
      rw [hkt1] at hy; cases hy
      have : z = x' := by
        have h' : σ2'.kheap p = some (.tcb z) := hz
        rw [hkt2'] at h'; cases h'; rfl
      subst this
      exact Or.inr ⟨rfl, by rw [hxs]; nofun, Or.inl (Or.inr (Or.inl ⟨r, hxs⟩))⟩
    · left
      have h' : σ2'.kheap p = some (.tcb z) := hz
      rw [hkp2 p e, hy] at h'; cases h'; rfl
  have hst := setThreadState_eq' hkt1 .restart
  set σ2 := stsAct σ2' t with hσ2
  obtain ⟨hk2, ht2, hr2, ha2⟩ := stsAct_heap σ2' t
  have hI2 : Inv σ2 := hI2'.qchange (qchange_stsAct σ2' t)
  have hrel2 : σ2.releaseQueue = σ.releaseQueue := by rw [hσ2, hr2]; rfl
  have hkt2 : σ2.kheap t = some (.tcb x') := by rw [hk2]; exact hkt2'
  have hkp2b : ∀ q, q ≠ t → q ≠ r → σ2.kheap q = σ.kheap q := fun q h1 h2 => by
    rw [hk2, hkp2 q h1, hkp1 q h2]
  -- the membership, step by step
  unfold removeAndRestartNtfnQueuedThread at hm
  rw [nd_bind_one hdq] at hm
  replace hm : ((), σ5) ∈ ((setThreadState (Z := Unit) t .restart >>= fun _ => (do
      let scOpt ← getTcbObjRef Tcb.tcbSchedContext t
      ifSporadicCurScAssertRefillUnblockCheck scOpt
      possibleSwitchTo t)) σ1).1 := hm
  rw [nd_bind_one hst,
    nd_bind_one (show getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t σ2 = _ from threadGet_eq _ hkt2)] at hm
  obtain ⟨z3, hz3, hm⟩ := hm
  obtain ⟨⟨⟩, σ3⟩ := z3
  -- the sporadic check
  have hu : ((), σ3) ∈ (specUnblock t σ2).1 := by
    rw [← Ipc.specSporadicAssert_eq]; unfold Endp.specSporadicAssert
    rw [nd_bind_one (show getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t σ2 = _ from threadGet_eq _ hkt2)]
    exact hz3
  have hsa2 : ∀ p y k, x'.tcbSchedContext = some p → σ2.kheap p = some (.schedContext y k) → scActive y = true := by
    intro p y k hp hky
    have hpt : p ≠ t := by rintro rfl; rw [hkt2] at hky; cases hky
    have hpr : p ≠ r := by intro e; rw [e, hk2, hkp2 r hrt, hσ1] at hky; simp [updK] at hky
    rw [hkp2b p hpt hpr] at hky
    exact hsa p y k hp hky
  have hI3 : Inv σ3 := hI2.unblockTail hkt2
    (fun p y k _ _ hm' => absurd (hrel2 ▸ hm') htrel)
    (fun p y k hp hky _ => hsa2 p y k hp hky) hu
  -- `MaxK` across the check: SCs keep `REFILL_MAX` and their thread
  have hK3 : MaxK.SCK σ2 σ3 := by
    have e : specUnblock t = (getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>=
        ifSporadicCurScTestRefillUnblockCheck (Z := Unit)) := rfl
    exact MaxK.mk_unblock t σ2 ((), σ3) (by rw [← e]; exact hu)
  -- the check is deterministic, and changes only the SC's refills
  have hdet3 : ∀ y, y ∈ (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) x'.tcbSchedContext σ2).1 → y = ((), σ3) :=
    fun y hy => (Det.det_ifCondRefillUnblockCheck _ _ _).det σ2 y ((), σ3) hy hz3
  have hshape : σ3 = σ2 ∨ ∃ c y z k, x.tcbSchedContext = some c ∧ σ2.kheap c = some (.schedContext y k) ∧
      σ3 = updSc { σ2 with reprogramTimer := true } c z k ∧ z = { y with scRefills := z.scRefills } ∧
      c ≠ σ2.curSc := by
    cases hxc : x.tcbSchedContext with
    | none =>
      left
      have : ((), σ2) ∈ (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) x'.tcbSchedContext σ2).1 := by
        show ((), σ2) ∈ (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) x.tcbSchedContext σ2).1
        rw [hxc]; unfold ifSporadicCurScAssertRefillUnblockCheck ifCondRefillUnblockCheck
        simp only [NonDet.maybeM]; exact Set.mem_singleton _
      exact (congrArg Prod.snd (hdet3 _ this)).symm
    | some c =>
      obtain ⟨y, k, hky, -⟩ := hI2.back t x' c hkt2 hxc
      have hne : y.scSporadic = true → y.scRefills ≠ [] := fun _ =>
        hI2.ne c y k hky (hsa2 c y k hxc hky)
      obtain ⟨σ3', hm3', hc3⟩ := unblockCur_some hky hne
      have e3 : σ3' = σ3 := congrArg Prod.snd (hdet3 _ (by show _ ∈ (_ : Set _); rw [show x'.tcbSchedContext = some c from hxc]; exact hm3'))
      subst e3
      rcases hc3 with e | ⟨z, e, -, -, hz, -, -⟩
      · exact Or.inl e
      · by_cases hcc : c = σ2.curSc
        · exact Or.inl (unblockCur_self hky hcc hm3')
        · exact Or.inr ⟨c, y, z, k, rfl, hky, e, hz, hcc⟩
  have hkt3 : σ3.kheap t = some (.tcb x') := by
    rcases hshape with e | ⟨c, y, z, k, -, hky, e, -, -⟩
    · rw [e]; exact hkt2
    · have hct : c ≠ t := by rintro rfl; rw [hkt2] at hky; cases hky
      rw [e]; simp [updSc, updK, Ne.symm hct, hkt2]
  -- the switch
  obtain ⟨σ6, he6, hk6, ht6, hr6, ha6⟩ := pst_ok hkt3 hI3.actReady
  have hm' : ((), σ5) ∈ (possibleSwitchTo (Z := Unit) t σ3).1 := hm
  have e56 : σ5 = σ6 := mem_singleton_snd (by rw [he6] at hm'; exact hm')
  subst e56
  have hI5 : Inv σ5 := by
    by_cases hs : schedulable t σ3 = true
    · exact hI3.qchange (possibleSwitchTo_qchange hI3 hs he6)
    · have hnop : possibleSwitchTo (Z := Unit) t σ3 = ({((), σ3)}, False) := by
        rw [possibleSwitchTo_unfold hkt3, if_neg]
        rintro ⟨hsc, hnr⟩
        apply hs
        obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hsc
        obtain ⟨y3, k3, hky3, -⟩ := hI3.back t x' c hkt3 hc
        obtain ⟨y2, hky2, hm2, -⟩ := hK3 c y3 k3 hky3
        have ha2 := hsa2 c y2 k3 hc hky2
        exact schedulable_of hkt3 hc rfl hky3 (by simpa [scActive, hm2] using ha2)
          (by simpa [inReleaseQueue] using hnr)
      have : σ5 = σ3 := ((Prod.mk.inj (singleton_one_eq (hnop.symm.trans he6))).2).symm
      rw [this]; exact hI3
  -- what the loop carries
  have hkp5 : ∀ q, q ≠ t → q ≠ r → (∀ c, x.tcbSchedContext = some c → q ≠ c) → σ5.kheap q = σ.kheap q := by
    intro q h1 h2 h3
    rw [hk6]
    rcases hshape with e | ⟨c, y, z, k, hxc, -, e, -, -⟩
    · rw [e]; exact hkp2b q h1 h2
    · rw [e]; simp only [updSc, updK, Function.update_of_ne (h3 c hxc)]; exact hkp2b q h1 h2
  have hkr5 : σ5.kheap r = some (.notification n1) := by
    rw [hk6]
    have hr2' : σ2.kheap r = some (.notification n1) := by rw [hk2, hkp2 r hrt]; simp [hσ1, updK]
    rcases hshape with e | ⟨c, y, z, k, -, hky, e, -, -⟩
    · rw [e]; exact hr2'
    · have hcr : c ≠ r := by rintro rfl; rw [hr2'] at hky; cases hky
      rw [e]; simp only [updSc, updK, Function.update_of_ne (Ne.symm hcr)]; exact hr2'
  have hbl5 : ∀ u ∈ l, ∃ x0, σ5.kheap u = some (.tcb x0) ∧ x0.tcbState = .blockedOnNotification r := by
    intro u hu
    obtain ⟨xu, hku, hsu⟩ := hbl u (List.mem_cons_of_mem _ hu)
    have hut : u ≠ t := fun e => htl (e ▸ hu)
    have hur : u ≠ r := by rintro rfl; rw [hk] at hku; cases hku
    have huc : ∀ c, x.tcbSchedContext = some c → u ≠ c := by
      rintro c hc rfl
      obtain ⟨y, k, hky, -⟩ := hI.back t x u hkt hc
      rw [hku] at hky; cases hky
    exact ⟨xu, by rw [hkp5 u hut hur huc]; exact hku, hsu⟩
  have hpt_of : ∀ p y k, σ2.kheap p = some (.schedContext y k) → p ≠ t := by
    rintro p y k hky rfl; rw [hkt2] at hky; cases hky
  have hpr_of : ∀ p y k, σ2.kheap p = some (.schedContext y k) → p ≠ r := by
    intro p y k hky e; rw [e, hk2, hkp2 r hrt] at hky; simp [hσ1, updK] at hky
  -- an SC of `σ5`: `REFILL_MAX` and thread as at `σ`
  have hsc5 : ∀ p y k, σ5.kheap p = some (.schedContext y k) → ∃ y0, σ.kheap p = some (.schedContext y0 k) ∧
      y.scRefillMax = y0.scRefillMax ∧ y.scTcb = y0.scTcb := by
    intro p y k hp
    have hp3 : σ3.kheap p = some (.schedContext y k) := by rw [← hk6]; exact hp
    obtain ⟨y2, hky2, hm2, ht2'⟩ := hK3 p y k hp3
    have e := hkp2b p (hpt_of p y2 k hky2) (hpr_of p y2 k hky2)
    rw [e] at hky2
    exact ⟨y2, hky2, hm2, ht2'⟩
  -- `t`'s SC is an SC at `σ5`
  have hc5sc : ∀ c, x.tcbSchedContext = some c → ∃ y k, σ5.kheap c = some (.schedContext y k) := by
    intro c hc
    rw [hk6]
    rcases hshape with e | ⟨c', y0, z, k0, hxc', hky0, e, -, -⟩
    · obtain ⟨y, k, hky, -⟩ := hI2.back t x' c hkt2 hc
      exact ⟨y, k, by rw [e]; exact hky⟩
    · rw [hc] at hxc'; cases hxc'
      exact ⟨z, k0, by rw [e]; simp [updSc, updK]⟩
  have hB5 : BlockedScActive σ5 := by
    refine ⟨fun p y k u xu hp hyt hxu hqu => ?_, fun p y k hp hr => ?_⟩
    · -- the thread `u` is not `t` (no longer blocked), kept
      have hut : u ≠ t := by
        rintro rfl
        rw [hk6, hkt3] at hxu; cases hxu; simp [hx', ipcQueuedThreadState] at hqu
      have hur : u ≠ r := by rintro rfl; rw [hkr5] at hxu; cases hxu
      have huc : ∀ c, x.tcbSchedContext = some c → u ≠ c := by
        rintro c hc rfl
        obtain ⟨y', k', hy'⟩ := hc5sc u hc
        rw [hxu] at hy'; cases hy'
      have hxu0 : σ.kheap u = some (.tcb xu) := by rw [← hkp5 u hut hur huc]; exact hxu
      obtain ⟨y0, hky0, hm0, ht0⟩ := hsc5 p y k hp
      have := hB.tcb p y0 k u xu hky0 (ht0 ▸ hyt) hxu0 hqu
      simpa [scActive, hm0] using this
    · by_cases hpc : ∃ c, x.tcbSchedContext = some c ∧ p = c
      · obtain ⟨c, hc, rfl⟩ := hpc
        obtain ⟨y0, hky0, hm0, -⟩ := hsc5 p y k hp
        have := hsa p y0 k hc hky0
        simpa [scActive, hm0] using this
      · push_neg at hpc
        have hpt : p ≠ t := by
          rintro rfl; rw [hk6, hkt3] at hp; cases hp
        have hpr : p ≠ r := by rintro rfl; rw [hkr5] at hp; cases hp
        rw [hkp5 p hpt hpr (fun c hc e => hpc c hc e)] at hp
        exact hB.replies p y k hp hr
  -- the frame
  have hF1 : NFr false r σ σ1 := NFr.upd hk (Or.inr (Or.inr ⟨n, n1, rfl, rfl, rfl,
    by rw [show n1.ntfnObj.ntfnQueue = l from hq1, show n.ntfnObj.ntfnQueue = t :: l from hq];
       exact List.sublist_cons_self t l, (fun h => by cases h), Or.inl rfl, fun hw => by
         exfalso
         cases ho : n.ntfnObj with
         | waitingNtfn l' => exact hw l' ho
         | _ => simp [ntfnQueueOf, ho, Ntfn.ntfnQueue] at hq, Or.inl rfl⟩))
  have hF2 : NFr false r σ1 σ2' := NFr.upd (o' := .tcb x') hkt1
    (Or.inl ⟨x, .restart, x.tcbBoundNotification, x.tcbArch, rfl, rfl, Or.inr ⟨rfl, hxs, Or.inl rfl⟩, Or.inl rfl⟩)
  have hF3 : NFr false r σ2 σ3 := by
    rcases hshape with e | ⟨c, y, z, k, -, hky, e, hz, hcc⟩
    · rw [e]; exact NFr.refl _ _ _
    · rw [e]
      have h0 : NFr false r σ2 { σ2 with reprogramTimer := true } :=
        NFr.ofSk ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun e => by cases e) rfl
      refine h0.trans (NFr.upd (σ := { σ2 with reprogramTimer := true }) (o' := .schedContext z k) hky
        (Or.inr (Or.inl ⟨y, k, z.scRefills, y.scNtfn, rfl, congrArg (fun w => KernelObject.schedContext w k) hz,
          fun h => absurd (h.resolve_right (by simp)) hcc, Or.inl rfl⟩)))
  obtain ⟨σ7, he7, hq7⟩ := pst_q hkt3 hI3.actReady
  have e57 : σ5 = σ7 := (Prod.mk.inj (singleton_one_eq (he6.symm.trans he7))).2
  have hF5 : NFr false r σ3 σ5 := by rw [e57]; exact hq7.nfr
  exact ⟨⟨hI5, hB5, ⟨n1, hkr5, hq1⟩, (List.nodup_cons.1 hnd).2, hbl5⟩,
    hF1.trans (hF2.trans ((NFr.sts r σ2' t).trans (hF3.trans hF5)))⟩

/-- **The loop of `cancel_all_signals` keeps the loop's facts.** -/
theorem ntfn_loop_inv {r : ObjRef} : ∀ (l : List ObjRef) (σ σ' : State Unit), NtfnLoopInv σ r l →
    ((), σ') ∈ (NonDet.mapMx (fun t => removeAndRestartNtfnQueuedThread (Z := Unit) t r) l σ).1 →
    NtfnLoopInv σ' r [] ∧ NFr false r σ σ'
  | [], σ, σ', h, hm => by
    have : σ' = σ := mem_singleton_snd hm
    rw [this]; exact ⟨h, NFr.refl _ _ _⟩
  | t :: l, σ, σ', h, hm => by
    obtain ⟨y, hy, hm⟩ := (show ((), σ') ∈ ((removeAndRestartNtfnQueuedThread (Z := Unit) t r >>= fun _ =>
      NonDet.mapMx (fun t => removeAndRestartNtfnQueuedThread (Z := Unit) t r) l) σ).1 from hm)
    obtain ⟨⟨⟩, σ5⟩ := y
    obtain ⟨h5, hF5⟩ := inv_ntfn_iter h hy
    obtain ⟨h', hF'⟩ := ntfn_loop_inv l σ5 σ' h5 hm
    exact ⟨h', hF5.trans hF'⟩

/-- **`cancel_all_signals` keeps `Inv` and `BlockedScActive`** (the queued
threads blocked on the notification, duplicate-free: `SchedValid`), in the
frame `NFr`, the action then `choose_new_thread` unless nothing changed. -/
theorem inv_cancelAllSignals {σ σ' : State Unit} {r : ObjRef} {n : Notification} (hI : Inv σ)
    (hB : BlockedScActive σ) (hkn : σ.kheap r = some (.notification n))
    (hV : (ntfnQueueOf n).Nodup ∧
      ∀ u ∈ ntfnQueueOf n, ∃ xu, σ.kheap u = some (.tcb xu) ∧ xu.tcbState = .blockedOnNotification r)
    (hm : ((), σ') ∈ (cancelAllSignals (Z := Unit) r σ).1) :
    Inv σ' ∧ BlockedScActive σ' ∧ NFr false r σ σ' ∧ (σ'.schedulerAction = .chooseNewThread ∨ σ' = σ) := by
  unfold cancelAllSignals at hm
  rw [nd_bind_one (getNotification_eq hkn)] at hm
  obtain ⟨hnd, hbl⟩ := hV
  cases ho : n.ntfnObj with
  | waitingNtfn q =>
    rw [ho] at hm
    obtain ⟨z, hz, hm⟩ := hm
    obtain ⟨⟨⟩, σf⟩ := z
    have hq' : ntfnQueueOf n = q := by simp [ntfnQueueOf, ho, Ntfn.ntfnQueue]
    rw [hq'] at hnd hbl
    have h0 : NtfnLoopInv σ r q := ⟨hI, hB, ⟨n, hkn, hq'⟩, hnd, fun u hu => hbl u hu⟩
    obtain ⟨⟨hIf, hBf, -⟩, hFf⟩ := ntfn_loop_inv q σ σf h0 hz
    obtain ⟨σr, hr, hq⟩ := rescheduleRequired_qchange hIf.actReady
    obtain ⟨σr', hr', hQ', ha'⟩ := resched_q hIf.actReady
    have hm' : ((), σ') ∈ (rescheduleRequired (Z := Unit) σf).1 := hm
    have e : σ' = σr := mem_singleton_snd (by rw [hr] at hm'; exact hm')
    have e' : σ' = σr' := mem_singleton_snd (by rw [hr'] at hm'; exact hm')
    subst e
    refine ⟨hIf.qchange hq, ?_, hFf.trans (e' ▸ hQ'.nfr), Or.inl (e' ▸ ha')⟩
    obtain ⟨hk, -⟩ := hq
    exact ⟨fun p y k t x hp hyt hx hqt => hBf.tcb p y k t x (hk ▸ hp) hyt (hk ▸ hx) hqt,
      fun p y k hp hr' => hBf.replies p y k (hk ▸ hp) hr'⟩
  | idleNtfn =>
    rw [ho] at hm
    have : σ' = σ := mem_singleton_snd hm
    rw [this]; exact ⟨hI, hB, NFr.refl _ _ _, Or.inr rfl⟩
  | activeNtfn b =>
    rw [ho] at hm
    have : σ' = σ := mem_singleton_snd hm
    rw [this]; exact ⟨hI, hB, NFr.refl _ _ _, Or.inr rfl⟩

/-! ### What the frame keeps -/

section
variable {q : Bool} {r : ObjRef} {σ σ' : State Unit}

theorem NFr.tcbF (h : NFr q r σ σ') {p : ObjRef} {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    ∃ st bn ar, σ'.kheap p = some (.tcb { x with tcbState := st, tcbBoundNotification := bn, tcbArch := ar }) ∧
      TChg q r x st ar ∧ (bn = x.tcbBoundNotification ∨ bn = none) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x.tcbState, x.tcbBoundNotification, x.tcbArch, by rw [e, hp], Or.inl ⟨rfl, rfl⟩, Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨x', st, bn, ar, e1, rfl, hs, hb⟩ | ⟨_, _, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨st, bn, ar, h2, hs, hb⟩

theorem NFr.tcbB (h : NFr q r σ σ') {p : ObjRef} {y : Tcb} (hp : σ'.kheap p = some (.tcb y)) :
    ∃ x st bn ar, σ.kheap p = some (.tcb x) ∧
      y = { x with tcbState := st, tcbBoundNotification := bn, tcbArch := ar } ∧
      TChg q r x st ar ∧ (bn = x.tcbBoundNotification ∨ bn = none) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, y.tcbState, y.tcbBoundNotification, y.tcbArch, by rw [← e, hp], rfl, Or.inl ⟨rfl, rfl⟩, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨x, st, bn, ar, rfl, e2, hs, hb⟩ | ⟨_, _, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨x, st, bn, ar, h1, rfl, hs, hb⟩

/-- A TCB's state kept unless it was blocked on `r`. -/
theorem TChg.st {q : Bool} {r : ObjRef} {x : Tcb} {st : ThreadState} {ar : ArchTcb} (h : TChg q r x st ar)
    (hx : x.tcbState ≠ .blockedOnNotification r) : st = x.tcbState := by
  rcases h with ⟨e, -⟩ | ⟨-, e, -⟩
  · exact e
  · exact absurd e hx

/-- With `q = true`, a TCB's state and context kept. -/
theorem TChg.quiet {r : ObjRef} {x : Tcb} {st : ThreadState} {ar : ArchTcb} (h : TChg true r x st ar) :
    st = x.tcbState ∧ ar = x.tcbArch := by
  rcases h with e | ⟨e, -⟩
  · exact e
  · cases e

/-- A TCB's state: kept, or no longer IPC-queued. -/
theorem TChg.ipcQ {q : Bool} {r : ObjRef} {x : Tcb} {st : ThreadState} {ar : ArchTcb} (h : TChg q r x st ar)
    (hq : ipcQueuedThreadState st = true) : ipcQueuedThreadState x.tcbState = true := by
  rcases h with ⟨e, -⟩ | ⟨-, -, e | e⟩
  · rw [← e]; exact hq
  · rw [e] at hq; simp [ipcQueuedThreadState] at hq
  · rw [e] at hq; simp [ipcQueuedThreadState] at hq

theorem NFr.scF (h : NFr q r σ σ') {p : ObjRef} {y : SchedContext} {n : Nat} (hp : σ.kheap p = some (.schedContext y n)) :
    ∃ rf nt, σ'.kheap p = some (.schedContext { y with scRefills := rf, scNtfn := nt } n) ∧
      (p = σ.curSc ∨ q = true → rf = y.scRefills) ∧ (nt = y.scNtfn ∨ nt = none) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y.scRefills, y.scNtfn, by rw [e, hp], fun _ => rfl, Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, _, e1, -⟩ | ⟨y', n', rf, nt, e1, rfl, hr, hn⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨rf, nt, h2, hr, hn⟩

theorem NFr.scB (h : NFr q r σ σ') {p : ObjRef} {z : SchedContext} {n : Nat} (hp : σ'.kheap p = some (.schedContext z n)) :
    ∃ y rf nt, σ.kheap p = some (.schedContext y n) ∧ z = { y with scRefills := rf, scNtfn := nt } ∧
      (p = σ.curSc ∨ q = true → rf = y.scRefills) ∧ (nt = y.scNtfn ∨ nt = none) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨z, z.scRefills, z.scNtfn, by rw [← e, hp], rfl, fun _ => rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, _, -, e2, -⟩ | ⟨y, n', rf, nt, rfl, e2, hr, hn⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨y, rf, nt, h1, rfl, hr, hn⟩

theorem NFr.ntfnB (h : NFr q r σ σ') {p : ObjRef} {y : Notification} (hp : σ'.kheap p = some (.notification y)) :
    ∃ x, σ.kheap p = some (.notification x) ∧ (p ≠ r → y = x) ∧
      y.ntfnObj.ntfnQueue.Sublist x.ntfnObj.ntfnQueue ∧ (q = true → NObj x.ntfnObj y.ntfnObj) ∧
      (y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none) ∧ ((∀ l, x.ntfnObj ≠ .waitingNtfn l) → NObj x.ntfnObj y.ntfnObj) ∧
      (y.ntfnBoundTcb = x.ntfnBoundTcb ∨ y.ntfnBoundTcb = none) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e, hp], fun _ => rfl, List.Sublist.refl _, fun _ => Or.inl rfl, Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, _, -, e2, -⟩ | ⟨_, _, _, _, -, e2, -⟩ | ⟨x, y', rfl, e2, hpr, hq, hq', hs, hw, hb⟩ <;> cases e2
    exact ⟨x, h1, fun hne => absurd hpr hne, hq, hq', hs, hw, hb⟩

theorem NFr.othB (h : NFr q r σ σ') {p : ObjRef} {o' : KernelObject} (hp : σ'.kheap p = some o')
    (h1 : ∀ x, o' ≠ .tcb x) (h2 : ∀ y n, o' ≠ .schedContext y n) (h3 : ∀ x, o' ≠ .notification x) :
    σ.kheap p = some o' := by
  rcases h.kh p with e | ⟨o, o'', k1, k2, hc⟩
  · rw [← e, hp]
  · rw [hp] at k2; cases k2
    rcases hc with ⟨_, _, _, _, -, e2, -⟩ | ⟨_, _, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩
    · exact absurd e2 (h1 _)
    · exact absurd e2 (h2 _ _)
    · exact absurd e2 (h3 _)

theorem NFr.othF (h : NFr q r σ σ') {p : ObjRef} {o : KernelObject} (hp : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h2 : ∀ y n, o ≠ .schedContext y n) (h3 : ∀ x, o ≠ .notification x) :
    σ'.kheap p = some o := by
  rcases h.kh p with e | ⟨o0, o', k1, k2, hc⟩
  · rw [e, hp]
  · rw [hp] at k1; cases k1
    rcases hc with ⟨_, _, _, _, e1, -⟩ | ⟨_, _, _, _, e1, -⟩ | ⟨_, _, e1, -⟩
    · exact absurd e1 (h1 _)
    · exact absurd e1 (h2 _ _)
    · exact absurd e1 (h3 _)

/-- The objects' kinds and sizes kept, both ways. -/
theorem NFr.kind (h : NFr q r σ σ') (p : ObjRef) :
    (∀ o, σ.kheap p = some o → ∃ o', σ'.kheap p = some o' ∧ aType o' = aType o) ∧
    (∀ o', σ'.kheap p = some o' → ∃ o, σ.kheap p = some o ∧ aType o' = aType o) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨fun o ho => ⟨o, by rw [e, ho], rfl⟩, fun o' ho => ⟨o', by rw [← e, ho], rfl⟩⟩
  · have ha : aType o' = aType o := by
      rcases hc with ⟨x, st, bn, ar, rfl, rfl, -⟩ | ⟨y, n, rf, nt, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ <;> rfl
    exact ⟨fun o0 ho0 => ⟨o', h2, by rw [h1] at ho0; cases ho0; exact ha⟩,
      fun o0 ho0 => ⟨o, h1, by rw [h2] at ho0; cases ho0; exact ha⟩⟩

theorem NFr.szKeep (h : NFr q r σ σ') : SzKeep σ σ' := fun p y n hp => by
  obtain ⟨y0, -, -, hy0, -⟩ := h.scB hp; exact ⟨y0, hy0⟩

theorem NFr.ckeep (h : NFr q r σ σ') : Sched.CKeep σ σ' := by
  refine ⟨fun p y n hp => ?_, fun p x hp => ⟨x, h.othF hp (fun _ e => by cases e) (fun _ _ e => by cases e)
    (fun _ e => by cases e), rfl, rfl⟩, fun p x n hp => ?_⟩
  · obtain ⟨rf, nt, hp', -⟩ := h.scF hp; exact ⟨_, hp', rfl⟩
  · obtain ⟨y0, -, -, hy0, -⟩ := h.scB hp; exact ⟨y0, hy0⟩

theorem NFr.ykeep (h : NFr q r σ σ') : YKeep σ σ' := by
  refine ⟨fun p x hp => ?_, fun p y n hp => ?_, fun p z n hp => ?_⟩
  · obtain ⟨st, bn, ar, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩
  · obtain ⟨rf, nt, hp', -⟩ := h.scF hp; exact ⟨_, hp', rfl⟩
  · obtain ⟨y0, rf, nt, hy0, rfl, -⟩ := h.scB hp; exact ⟨y0, hy0, rfl⟩

theorem NFr.mcpKeep (h : NFr q r σ σ') : McpKeep σ σ' := fun p x hp => by
  obtain ⟨st, bn, ar, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem NFr.bufKeep (h : NFr q r σ σ') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => by obtain ⟨st, bn, ar, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩


theorem NFr.prio (h : NFr q r σ σ') (u : ObjRef) : prioOf σ' u = prioOf σ u := by
  unfold prioOf
  rw [tcbsOf_eq, tcbsOf_eq]
  cases hk : σ.kheap u with
  | some o =>
    cases o with
    | tcb x =>
      obtain ⟨st, bn, ar, hk', -⟩ := h.tcbF hk
      rw [hk']; rfl
    | _ =>
      cases hk' : σ'.kheap u with
      | none => rfl
      | some o' => cases o' with
        | tcb y => obtain ⟨x, -, -, -, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
        | _ => rfl
  | none =>
    cases hk' : σ'.kheap u with
    | none => rfl
    | some o' => cases o' with
      | tcb y => obtain ⟨x, -, -, -, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
      | _ => rfl

theorem NFr.nsc {N C : Set U64} (h : NFr q r σ σ') (hN : NSC N C σ) : NSC N C σ' := by
  intro n hn y p hy hp
  obtain ⟨x, hx, -, -, -, hs, -, -⟩ := h.ntfnB hy
  rcases hs with e | e
  · exact hN n hn x p hx (e ▸ hp)
  · rw [e] at hp; cases hp

theorem NFr.isorted (h : NFr q r σ σ') (hS : IpcSorted σ) : IpcSorted σ' := by
  refine ⟨fun p x hp => ?_, fun p y hp => ?_⟩
  · have hp0 := h.othB hp (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
    exact (hS.1 p x hp0).congr fun u _ => h.prio u
  · obtain ⟨x, hx, -, hsub, -, -⟩ := h.ntfnB hp
    exact ((hS.2 p x hx).sublist hsub).congr fun u _ => h.prio u

theorem NFr.own {T C : Set U64} (h : NFr q r σ σ') (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · obtain ⟨st, bn, ar, hkt', -⟩ := h.tcbF hkt
    refine Or.inl ⟨u, hu, _, hkt', by rw [h.sk.csc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
    · rw [h.sk.csc] at hy
      obtain ⟨y0, rf, nt, hy0, rfl, -⟩ := h.scB hy
      exact hown y0 n hy0
    · rw [h.sk.cons] at h0; rw [h.sk.rel] at hm; exact hnr h0 hm
  · refine Or.inr ⟨by rw [h.sk.csc]; exact hcs, fun y n hy => ?_⟩
    rw [h.sk.csc] at hy
    obtain ⟨y0, rf, nt, hy0, rfl, -⟩ := h.scB hy
    exact hun y0 n hy0

theorem NFr.off (h : NFr q r σ σ') (hO : OffOK σ) : OffOK σ' := by
  intro hc y n hy ha
  rw [h.sk.cons] at hc ⊢; rw [h.sk.tm]
  rw [h.sk.csc] at hy ha
  obtain ⟨y0, rf, nt, hy0, rfl, hr, -⟩ := h.scB hy
  have e : rf = y0.scRefills := hr (Or.inl rfl)
  subst e
  exact hO hc y0 n hy0 ha

theorem NFr.idleOK (h : NFr q r σ σ') (hO : IdleOK σ) : IdleOK σ' := by
  obtain ⟨x, hx, h1, h2, h3⟩ := hO
  obtain ⟨st, bn, ar, hx', hs, -⟩ := h.tcbF hx
  refine ⟨{ x with tcbState := st, tcbBoundNotification := bn, tcbArch := ar }, by rw [h.sk.idle]; exact hx', h1, ?_,
    by rw [h.sk.idle, h.sk.rel]; exact h3⟩
  show st = _
  rw [hs.st (by rw [h2]; nofun)]; exact h2

theorem NFr.bsa (h : NFr q r σ σ') (hB : BlockedScActive σ) : BlockedScActive σ' := by
  refine ⟨fun p z n t y hp hyt hy hq => ?_, fun p z n hp hr => ?_⟩
  · obtain ⟨y0, rf, nt, hy0, rfl, -⟩ := h.scB hp
    obtain ⟨x, st, bn, ar, hx, rfl, hs, -⟩ := h.tcbB hy
    have hq0 : ipcQueuedThreadState x.tcbState = true := hs.ipcQ hq
    exact hB.tcb p y0 n t x hy0 hyt hx hq0
  · obtain ⟨y0, rf, nt, hy0, rfl, -⟩ := h.scB hp
    exact hB.replies p y0 n hy0 hr

/-- `NFr true` keeps what the scheduler reads (`SFr`). -/
theorem NFr.sfr (h : NFr true r σ σ') : SFr σ σ' := by
  refine ⟨fun p x hp => ?_, fun p y hp => ?_, fun p y n hp => ?_, fun p y n hp => ?_, h.sk.tm, h.sk.rel⟩
  · obtain ⟨st, bn, ar, hp', hs, -⟩ := h.tcbF hp
    refine ⟨_, hp', ?_, rfl⟩
    show runnable st = _
    rw [hs.quiet.1]
  · obtain ⟨x, -, -, -, hx, -⟩ := h.tcbB hp; exact ⟨x, hx⟩
  · obtain ⟨rf, nt, hp', hr, -⟩ := h.scF hp
    have e : rf = y.scRefills := hr (Or.inr rfl)
    subst e
    exact ⟨_, hp', rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨y0, -, -, hy0, -⟩ := h.scB hp; exact ⟨y0, hy0⟩

theorem NFr.curInv (h : NFr q r σ σ') (hC : CurInv σ) : CurInv σ' := by
  obtain ⟨xt, hkt, hxs, hnb⟩ := hC.tcb
  obtain ⟨x, n, hx⟩ := hC.sc
  obtain ⟨st, bn, ar, hkt', hs, -⟩ := h.tcbF hkt
  obtain ⟨rf, nt, hx', -⟩ := h.scF hx
  have hst : st = xt.tcbState := hs.st (hnb.1 r)
  refine ⟨⟨_, by rw [h.sk.ct]; exact hkt', by rw [h.sk.csc]; exact hxs, by rw [hst]; exact hnb⟩,
    ⟨_, n, by rw [h.sk.csc]; exact hx'⟩, fun hne y m hy => ?_, by rw [h.sk.ct, h.sk.rel]; exact hC.notRel⟩
  rw [h.sk.csc] at hne hy
  obtain ⟨y0, rf', nt', hy0, rfl, -⟩ := h.scB hy
  exact hC.active hne y0 m hy0

theorem NFr.actIdle (h : NFr true r σ σ') (hA : ActIdle σ) : ActIdle σ' := by
  refine ⟨fun t ht => ?_, h.idleOK hA.2⟩
  rw [(h.act rfl).1] at ht
  rw [h.sfr.schedulable]; exact hA.1 t ht

theorem NFr.curRunW (h : NFr q r σ σ') (hR : CurRunW σ) : CurRunW σ' := by
  rcases hR with hR | e
  · refine Or.inl fun y hy => ?_
    rw [h.sk.ct] at hy
    obtain ⟨x, st, bn, ar, hx, rfl, hs, -⟩ := h.tcbB hy
    have hst : st = x.tcbState := hs.st (fun e => by have := hR x hx; rw [e] at this; simp [runnable] at this)
    show runnable st = true
    rw [hst]; exact hR x hx
  · exact Or.inr (by rw [h.sk.ct, h.sk.idle]; exact e)

end

/-! ### The unbinding steps and the whole finalisation -/

/-- **`sched_context_maybe_unbind_ntfn`**: `NFr true`, `Inv` kept, the
notification's queue and bound TCB kept. -/
theorem msu_nfr {σ σ' : State Unit} {r : ObjRef} {n : Notification} (hk : σ.kheap r = some (.notification n))
    (hsc : ∀ c, n.ntfnSc = some c → ∃ y k, σ.kheap c = some (.schedContext y k))
    (hm : ((), σ') ∈ (schedContextMaybeUnbindNtfn (Z := Unit) r σ).1) :
    NFr true r σ σ' ∧ (Inv σ → Inv σ') ∧
      ∃ n', σ'.kheap r = some (.notification n') ∧ n'.ntfnObj = n.ntfnObj ∧ n'.ntfnBoundTcb = n.ntfnBoundTcb := by
  unfold schedContextMaybeUnbindNtfn at hm
  rw [nd_bind_one (getSkObjRef_ntfn_eq hk _)] at hm
  cases hn : n.ntfnSc with
  | none =>
    rw [hn] at hm
    have e : σ' = σ := mem_singleton_snd (b := ((), σ)) hm
    subst e
    exact ⟨NFr.refl _ _ _, id, n, hk, rfl, rfl⟩
  | some c =>
    obtain ⟨y, k, hky⟩ := hsc c hn
    have hrc : r ≠ c := by rintro rfl; rw [hk] at hky; cases hky
    rw [hn] at hm
    simp only [NonDet.maybeM] at hm
    unfold doUnbindNtfnSc setNtfnObjRef at hm
    rw [nd_bind_one (updateSkObjRef_ntfn_eq hk _ _)] at hm
    set σ1 := updK σ r (.notification (ntfnScUpdate (fun _ => none) n)) with hσ1
    have hky1 : σ1.kheap c = some (.schedContext y k) := by
      simp only [hσ1, updK, Function.update_of_ne (Ne.symm hrc)]; exact hky
    have e2 : setScObjRef (Z := Unit) scNtfnUpdate c none σ1 =
        ({((), updSc σ1 c (scNtfnUpdate (fun _ => none) y) k)}, False) := updateSchedContext_eq hky1 _
    replace hm : ((), σ') ∈ (setScObjRef (Z := Unit) scNtfnUpdate c none σ1).1 := hm
    rw [e2] at hm
    have e : σ' = updSc σ1 c (scNtfnUpdate (fun _ => none) y) k := mem_singleton_snd hm
    subst e
    refine ⟨(NFr.upd (o' := .notification (ntfnScUpdate (fun _ => none) n)) hk
        (Or.inr (Or.inr ⟨n, _, rfl, rfl, rfl, List.Sublist.refl _, fun _ => Or.inl rfl, Or.inr rfl, fun _ => Or.inl rfl,
          Or.inl rfl⟩))).trans
      (NFr.upd (o' := .schedContext (scNtfnUpdate (fun _ => none) y) k) hky1
        (Or.inr (Or.inl ⟨y, k, y.scRefills, none, rfl, rfl, fun _ => rfl, Or.inr rfl⟩))), fun hI => ?_,
      ntfnScUpdate (fun _ => none) n, ?_, rfl, rfl⟩
    · have hI1 : Inv σ1 := hI.updNtfn hk (fun p hp => by simp [ntfnScUpdate] at hp)
      exact hI1.scFields hky1 rfl rfl rfl rfl
    · simp [updSc, updK, hσ1, Function.update_of_ne hrc]

/-- **`unbind_maybe_notification`**: `NFr true`, `Inv` kept, the
notification's queue and SC kept. -/
theorem umn_nfr {σ σ' : State Unit} {r : ObjRef} {n : Notification} (hk : σ.kheap r = some (.notification n))
    (hb : ∀ t, n.ntfnBoundTcb = some t → ∃ x, σ.kheap t = some (.tcb x))
    (hm : ((), σ') ∈ (unbindMaybeNotification (Z := Unit) r σ).1) :
    NFr true r σ σ' ∧ (Inv σ → Inv σ') ∧
      ∃ n', σ'.kheap r = some (.notification n') ∧ n'.ntfnObj = n.ntfnObj ∧ n'.ntfnSc = n.ntfnSc := by
  unfold unbindMaybeNotification at hm
  rw [nd_bind_one (getSkObjRef_ntfn_eq hk _)] at hm
  cases hn : n.ntfnBoundTcb with
  | none =>
    rw [hn] at hm
    have e : σ' = σ := mem_singleton_snd (b := ((), σ)) hm
    subst e
    exact ⟨NFr.refl _ _ _, id, n, hk, rfl, rfl⟩
  | some t =>
    obtain ⟨x, hkt⟩ := hb t hn
    have hrt : r ≠ t := by rintro rfl; rw [hk] at hkt; cases hkt
    rw [hn] at hm
    simp only [NonDet.maybeM] at hm
    unfold doUnbindNotification setNtfnObjRef at hm
    rw [nd_bind_one (updateSkObjRef_ntfn_eq hk _ _)] at hm
    set σ1 := updK σ r (.notification (ntfnBoundTcbUpdate (fun _ => none) n)) with hσ1
    have hkt1 : σ1.kheap t = some (.tcb x) := by
      simp only [hσ1, updK, Function.update_of_ne (Ne.symm hrt)]; exact hkt
    have e2 := threadSet_eq (Z := Unit) (tcbBoundNotificationUpdate fun _ => none) hkt1
    replace hm : ((), σ') ∈ (threadSet (Z := Unit) (tcbBoundNotificationUpdate fun _ => none) t σ1).1 := hm
    rw [e2] at hm
    have e : σ' = updK σ1 t (.tcb (tcbBoundNotificationUpdate (fun _ => none) x)) := mem_singleton_snd hm
    subst e
    refine ⟨(NFr.upd (o' := .notification (ntfnBoundTcbUpdate (fun _ => none) n)) hk
        (Or.inr (Or.inr ⟨n, _, rfl, rfl, rfl, List.Sublist.refl _, fun _ => Or.inl rfl, Or.inl rfl, fun _ => Or.inl rfl,
          Or.inr rfl⟩))).trans
      (NFr.upd (o' := .tcb (tcbBoundNotificationUpdate (fun _ => none) x)) hkt1
        (Or.inl ⟨x, x.tcbState, none, x.tcbArch, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr rfl⟩)), fun hI => ?_,
      ntfnBoundTcbUpdate (fun _ => none) n, ?_, rfl, rfl⟩
    · have hI1 : Inv σ1 := hI.updNtfn hk (fun p hp => hI.ntfnSc r n p hk hp)
      exact hI1.tcbUpd hkt1 _ rfl rfl
    · simp [updK, hσ1, Function.update_of_ne hrt]

/-- **The spec's finalisation of notification `r`** (its three steps): `Inv`
and `BlockedScActive` kept, the frame `NFr`, and either the action
`choose_new_thread` (a waiting notification: `cancel_all_signals`'s
reschedule) or the quiet frame `NFr true` (nothing restarted). -/
theorem finNtfn_spec {σ σ1 σ2 σ3 : State Unit} {r : ObjRef} {n : Notification} (hI : Inv σ)
    (hB : BlockedScActive σ) (hV : SchedValid σ) (hk : σ.kheap r = some (.notification n))
    (hsc : ∀ c, n.ntfnSc = some c → ∃ y k, σ.kheap c = some (.schedContext y k))
    (hb : ∀ t, n.ntfnBoundTcb = some t → ∃ x, σ.kheap t = some (.tcb x))
    (h1 : ((), σ1) ∈ (schedContextMaybeUnbindNtfn (Z := Unit) r σ).1)
    (h2 : ((), σ2) ∈ (unbindMaybeNotification (Z := Unit) r σ1).1)
    (h3 : ((), σ3) ∈ (cancelAllSignals (Z := Unit) r σ2).1) :
    Inv σ3 ∧ BlockedScActive σ3 ∧ NFr false r σ σ3 ∧
      (σ3.schedulerAction = .chooseNewThread ∨ NFr true r σ σ3) := by
  obtain ⟨F1, I1, n1, hk1, ho1, hb1⟩ := msu_nfr hk hsc h1
  have hb' : ∀ t, n1.ntfnBoundTcb = some t → ∃ x, σ1.kheap t = some (.tcb x) := by
    intro t ht
    obtain ⟨x, hx⟩ := hb t (hb1 ▸ ht)
    obtain ⟨st, bn, ar, hx', -⟩ := F1.tcbF hx
    exact ⟨_, hx'⟩
  obtain ⟨F2, I2, n2, hk2, ho2, -⟩ := umn_nfr hk1 hb' h2
  have F12 := F1.trans F2
  -- the queue: `n`'s, its threads still blocked on `r`
  obtain ⟨hnd, hbl⟩ := hV.ntfnQ r n hk
  have hq2 : ntfnQueueOf n2 = ntfnQueueOf n := by simp only [ntfnQueueOf, ho2, ho1]
  have hV2 : (ntfnQueueOf n2).Nodup ∧
      ∀ u ∈ ntfnQueueOf n2, ∃ xu, σ2.kheap u = some (.tcb xu) ∧ xu.tcbState = .blockedOnNotification r := by
    rw [hq2]
    refine ⟨hnd, fun u hu => ?_⟩
    obtain ⟨xu, hxu, hs⟩ := hbl u hu
    obtain ⟨st, bn, ar, hxu', hst, -⟩ := F12.tcbF hxu
    have : st = xu.tcbState := hst.quiet.1
    exact ⟨_, hxu', by rw [this]; exact hs⟩
  obtain ⟨I3, B3, F3, ha3⟩ := inv_cancelAllSignals (I2 (I1 hI)) (F12.bsa hB) hk2 hV2 h3
  refine ⟨I3, B3, F12.weak.trans F3, ?_⟩
  rcases ha3 with e | e
  · exact Or.inl e
  · subst e; exact Or.inr F12

end Spec

end

end Fl4Proofs.P3.Sched
