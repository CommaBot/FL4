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

set_option maxHeartbeats 8000000 in
/-- **One thread of `cancel_all_signals` keeps the loop's facts.** -/
theorem inv_ntfn_iter {σ σ5 : State Unit} {r t : ObjRef} {l : List ObjRef} (h : NtfnLoopInv σ r (t :: l))
    (hm : ((), σ5) ∈ (removeAndRestartNtfnQueuedThread (Z := Unit) t r σ).1) : NtfnLoopInv σ5 r l := by
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
      σ3 = updSc { σ2 with reprogramTimer := true } c z k ∧ z = { y with scRefills := z.scRefills } := by
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
      · exact Or.inr ⟨c, y, z, k, rfl, hky, e, hz⟩
  have hkt3 : σ3.kheap t = some (.tcb x') := by
    rcases hshape with e | ⟨c, y, z, k, -, hky, e, -⟩
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
    rcases hshape with e | ⟨c, y, z, k, hxc, -, e, -⟩
    · rw [e]; exact hkp2b q h1 h2
    · rw [e]; simp only [updSc, updK, Function.update_of_ne (h3 c hxc)]; exact hkp2b q h1 h2
  have hkr5 : σ5.kheap r = some (.notification n1) := by
    rw [hk6]
    have hr2' : σ2.kheap r = some (.notification n1) := by rw [hk2, hkp2 r hrt]; simp [hσ1, updK]
    rcases hshape with e | ⟨c, y, z, k, -, hky, e, -⟩
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
    rcases hshape with e | ⟨c', y0, z, k0, hxc', hky0, e, -⟩
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
  exact ⟨hI5, hB5, ⟨n1, hkr5, hq1⟩, (List.nodup_cons.1 hnd).2, hbl5⟩

/-- **The loop of `cancel_all_signals` keeps the loop's facts.** -/
theorem ntfn_loop_inv {r : ObjRef} : ∀ (l : List ObjRef) (σ σ' : State Unit), NtfnLoopInv σ r l →
    ((), σ') ∈ (NonDet.mapMx (fun t => removeAndRestartNtfnQueuedThread (Z := Unit) t r) l σ).1 →
    NtfnLoopInv σ' r []
  | [], σ, σ', h, hm => by
    have : σ' = σ := mem_singleton_snd hm
    rw [this]; exact h
  | t :: l, σ, σ', h, hm => by
    obtain ⟨y, hy, hm⟩ := (show ((), σ') ∈ ((removeAndRestartNtfnQueuedThread (Z := Unit) t r >>= fun _ =>
      NonDet.mapMx (fun t => removeAndRestartNtfnQueuedThread (Z := Unit) t r) l) σ).1 from hm)
    obtain ⟨⟨⟩, σ5⟩ := y
    exact ntfn_loop_inv l σ5 σ' (inv_ntfn_iter h hy) hm

/-- **`cancel_all_signals` keeps `Inv` and `BlockedScActive`** (the queued
threads blocked on the notification, duplicate-free: `SchedValid`). -/
theorem inv_cancelAllSignals {σ σ' : State Unit} {r : ObjRef} {n : Notification} (hI : Inv σ)
    (hB : BlockedScActive σ) (hV : SchedValid σ) (hkn : σ.kheap r = some (.notification n))
    (hm : ((), σ') ∈ (cancelAllSignals (Z := Unit) r σ).1) :
    Inv σ' ∧ BlockedScActive σ' := by
  unfold cancelAllSignals at hm
  rw [nd_bind_one (getNotification_eq hkn)] at hm
  obtain ⟨hnd, hbl⟩ := hV.ntfnQ r n hkn
  cases ho : n.ntfnObj with
  | waitingNtfn q =>
    rw [ho] at hm
    obtain ⟨z, hz, hm⟩ := hm
    obtain ⟨⟨⟩, σf⟩ := z
    have hq' : ntfnQueueOf n = q := by simp [ntfnQueueOf, ho, Ntfn.ntfnQueue]
    rw [hq'] at hnd hbl
    have h0 : NtfnLoopInv σ r q := ⟨hI, hB, ⟨n, hkn, hq'⟩, hnd, fun u hu => hbl u hu⟩
    obtain ⟨hIf, hBf, -⟩ := ntfn_loop_inv q σ σf h0 hz
    obtain ⟨σr, hr, hq⟩ := rescheduleRequired_qchange hIf.actReady
    have hm' : ((), σ') ∈ (rescheduleRequired (Z := Unit) σf).1 := hm
    have e : σ' = σr := mem_singleton_snd (by rw [hr] at hm'; exact hm')
    subst e
    refine ⟨hIf.qchange hq, ?_⟩
    obtain ⟨hk, -⟩ := hq
    exact ⟨fun p y k t x hp hyt hx hqt => hBf.tcb p y k t x (hk ▸ hp) hyt (hk ▸ hx) hqt,
      fun p y k hp hr' => hBf.replies p y k (hk ▸ hp) hr'⟩
  | idleNtfn =>
    rw [ho] at hm
    have : σ' = σ := mem_singleton_snd hm
    rw [this]; exact ⟨hI, hB⟩
  | activeNtfn b =>
    rw [ho] at hm
    have : σ' = σ := mem_singleton_snd hm
    rw [this]; exact ⟨hI, hB⟩

end Spec

end

end Fl4Proofs.P3.Sched
