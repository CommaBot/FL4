/-
P3 (DESIGN.md §9), IPC: **the scheduler invariants across `send_signal`'s
wake-up of a thread blocked on the notification** (spec side only), toward
`SignalRestJHyp` (ScSignalJ).

From the state after the dequeue (`σ1`: the thread `t` blocked on the
notification `r`), the spec's `specWake t r badge` (NtfnSched): the state
`running` (`Inv.stable`: blocked on a notification, hence `inClass`;
`stsAct`: `QChange`), the badge register (`Inv.tcbUpd`), no SC donation
(`maybe_donate_sc` the identity, a premise), `possible_switch_to t` when
schedulable (`possibleSwitchTo_qchange`), the sporadic check of `t`'s SC
(`Inv.unblockTail`: `t`, blocked, in no release queue, its SC active by
`BlockedScActive`; the check changes that SC's refills only, never the
current SC's: `unblock_shape`).

* `wake_inv3`: `Inv` before the switch (hence `ActReady`, for FL4's side).
* `wake_spec`: after the wake: `Inv`, `BlockedScActive`, the frame
  `NFr false r` (the thread woken `running`, its context changed: `TChg`),
  `ActIdle` (a switch target is the old one or the woken thread, schedulable
  when switched to: `NFr.sched`), the action `choose_new_thread` or `CurInv`
  (`possible_switch_to` from `choose_new_thread` keeps it: `pst_act`), and
  `CurRunM`.
-/
import Fl4Proofs.P3.IpcFinNtfnInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

theorem Sk.stsAct (σ : State Unit) (t : ObjRef) : Sk σ (Notif.stsAct σ t) := by
  unfold Notif.stsAct; split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact Sk.refl σ

/-- **`possible_switch_to`'s action**: kept, `choose_new_thread`, or a switch
to the target from `resume_cur_thread`. -/
theorem pst_act {σ σ' : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (hA : ActReady σ)
    (he : possibleSwitchTo (Z := Unit) t σ = ({((), σ')}, False)) :
    σ'.schedulerAction = σ.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread ∨
      (σ.schedulerAction = .resumeCurThread ∧ σ'.schedulerAction = .switchThread t) := by
  rw [possibleSwitchTo_unfold hk] at he
  split_ifs at he with h1 h2 h3
  · rw [tcbSchedAction_gen hk] at he
    rw [pair_eq he]; exact Or.inl rfl
  · obtain ⟨σ1, e1, hk1, -, -, ha1⟩ := resched_ok hA
    have hk' : σ1.kheap t = some (.tcb x) := by rw [hk1]; exact hk
    rw [nd_bind_one e1, tcbSchedAction_gen hk'] at he
    rw [pair_eq he]; exact Or.inr (Or.inl ha1)
  · rw [setAction_eq] at he
    rw [pair_eq he]; exact Or.inr (Or.inr ⟨by simpa using h3, rfl⟩)
  · rw [pair_eq he]; exact Or.inl rfl

/-- **`NFr` keeps a schedulable thread schedulable** (a schedulable thread is
runnable, so not blocked on `r`: its state kept). -/
theorem NFr.sched {q : Bool} {r : ObjRef} {σ σ' : State Unit} (h : NFr q r σ σ') {u : ObjRef}
    (hs : schedulable u σ = true) : schedulable u σ' = true := by
  obtain ⟨x, scp, y, n, hk, hsc, hrun, hky, hact, hnr⟩ := schedulable_inv hs
  obtain ⟨st, bn, ar, hk', hst, -⟩ := h.tcbF hk
  obtain ⟨rf, nt, hky', -⟩ := h.scF hky
  have e : st = x.tcbState := hst.st (fun e => by rw [e] at hrun; simp [runnable] at hrun)
  exact schedulable_of hk' hsc (by show runnable st = true; rw [e]; exact hrun) hky' hact
    (by rw [h.sk.rel]; exact hnr)

/-- **The sporadic check's outcome** (`specUnblock`, deterministic): the
state kept, or the thread's SC (not the current SC) with new refills. -/
theorem unblock_shape {σ σ' : State Unit} (hI : Inv σ) {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x))
    (hsa : ∀ p y k, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y k) → scActive y = true)
    (hm : ((), σ') ∈ (specUnblock t σ).1) :
    σ' = σ ∨ ∃ c y z k, x.tcbSchedContext = some c ∧ σ.kheap c = some (.schedContext y k) ∧
      σ' = updSc { σ with reprogramTimer := true } c z k ∧ z = { y with scRefills := z.scRefills } ∧
      c ≠ σ.curSc := by
  rw [← Ipc.specSporadicAssert_eq] at hm
  unfold Endp.specSporadicAssert at hm
  rw [nd_bind_one (show getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t σ = _ from threadGet_eq _ hkt)] at hm
  have hdet : ∀ w, w ∈ (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) x.tcbSchedContext σ).1 →
      w = ((), σ') :=
    fun w hw => (Det.det_ifCondRefillUnblockCheck _ _ _).det σ w ((), σ') hw hm
  cases hxc : x.tcbSchedContext with
  | none =>
    left
    have : ((), σ) ∈ (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) x.tcbSchedContext σ).1 := by
      rw [hxc]; unfold ifSporadicCurScAssertRefillUnblockCheck ifCondRefillUnblockCheck
      simp only [NonDet.maybeM]; exact Set.mem_singleton _
    exact (congrArg Prod.snd (hdet _ this)).symm
  | some c =>
    obtain ⟨y, k, hky, -⟩ := hI.back t x c hkt hxc
    have hne : y.scSporadic = true → y.scRefills ≠ [] := fun _ => hI.ne c y k hky (hsa c y k hxc hky)
    obtain ⟨σ3', hm3', hc3⟩ := unblockCur_some hky hne
    have e3 : σ3' = σ' := congrArg Prod.snd (hdet _ (by rw [hxc]; exact hm3'))
    subst e3
    rcases hc3 with e | ⟨z, e, -, -, hz, -, -⟩
    · exact Or.inl e
    · by_cases hcc : c = σ.curSc
      · exact Or.inl (unblockCur_self hky hcc hm3')
      · exact Or.inr ⟨c, y, z, k, rfl, hky, e, hz, hcc⟩

/-- **The sporadic check in the frame** `NFr false r`, the action kept. -/
theorem unblock_frame {σ σ' : State Unit} (hI : Inv σ) {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x))
    (hsa : ∀ p y k, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y k) → scActive y = true)
    (hm : ((), σ') ∈ (specUnblock t σ).1) (r : ObjRef) :
    NFr false r σ σ' ∧ σ'.schedulerAction = σ.schedulerAction := by
  rcases unblock_shape hI hkt hsa hm with e | ⟨c, y, z, k, -, hky, e, hz, hcc⟩
  · subst e; exact ⟨NFr.refl _ _ _, rfl⟩
  · subst e
    refine ⟨?_, rfl⟩
    have h0 : NFr false r σ { σ with reprogramTimer := true } :=
      NFr.ofSk ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun e => by cases e) rfl
    exact h0.trans (NFr.upd (σ := { σ with reprogramTimer := true }) (o' := .schedContext z k) hky
      (Or.inr (Or.inl ⟨y, k, z.scRefills, y.scNtfn, rfl, congrArg (fun w => KernelObject.schedContext w k) hz,
        fun h => absurd (h.resolve_right (by simp)) hcc, Or.inl rfl⟩)))

/-- The spec's state after the wake's state and badge-register writes. -/
def wakeSt3 (σ1 : State Unit) (t : ObjRef) (x : Tcb) (badge : Word) : State Unit :=
  updK (Notif.stsAct (updK σ1 t (.tcb { x with tcbState := .running })) t) t
    (.tcb (setReg { x with tcbState := .running } badge_register badge))

/-- **`Inv` after the wake's writes** (module docstring). -/
theorem wake_inv3 {σ1 : State Unit} {r t : ObjRef} {x : Tcb} (hI : Inv σ1) (hkt : σ1.kheap t = some (.tcb x))
    (hxs : x.tcbState = .blockedOnNotification r) (badge : Word) : Inv (wakeSt3 σ1 t x badge) := by
  set x1 : Tcb := { x with tcbState := .running } with hx1
  set σA := updK σ1 t (.tcb x1) with hσA
  have hkpA : ∀ p, p ≠ t → σA.kheap p = σ1.kheap p := fun p hp => by
    simp only [hσA, updK, Function.update_of_ne hp]
  have hktA : σA.kheap t = some (.tcb x1) := by simp [hσA, updK]
  have hIA : Inv σA := by
    refine hI.stable (NtfnStep.tcb hkt .running x.tcbArch) fun p y z hy hz => ?_
    by_cases e : p = t
    · subst e
      rw [hkt] at hy; cases hy
      have : z = x1 := by
        have h' : σA.kheap p = some (.tcb z) := hz
        rw [hktA] at h'; cases h'; rfl
      subst this
      exact Or.inr ⟨rfl, by rw [hxs]; nofun, Or.inl (Or.inr (Or.inl ⟨r, hxs⟩))⟩
    · left
      have h' : σA.kheap p = some (.tcb z) := hz
      rw [hkpA p e, hy] at h'; cases h'; rfl
  have hI2 : Inv (Notif.stsAct σA t) := hIA.qchange (qchange_stsAct σA t)
  have hk2 : (Notif.stsAct σA t).kheap t = some (.tcb x1) := by rw [stsAct_kheap]; exact hktA
  show Inv (updK (Notif.stsAct σA t) t (.tcb (setReg x1 badge_register badge)))
  exact hI2.tcbUpd hk2 _ rfl rfl

set_option maxHeartbeats 4000000 in
/-- **The scheduler invariants after the wake** (module docstring). -/
theorem wake_spec {σ1 σ' : State Unit} {r t : ObjRef} {x : Tcb} {badge : Word}
    (hI : Inv σ1) (hB : BlockedScActive σ1) (hAI : ActIdle σ1)
    (hcur : σ1.schedulerAction = .chooseNewThread ∨ CurInv σ1) (hrun : CurRunM σ1)
    (hkt : σ1.kheap t = some (.tcb x)) (hxs : x.tcbState = .blockedOnNotification r)
    (hND : maybeDonateSc (Z := Unit) t r (wakeSt3 σ1 t x badge) = ({((), wakeSt3 σ1 t x badge)}, False))
    (hm : ((), σ') ∈ (specWake t r badge σ1).1) :
    Inv σ' ∧ BlockedScActive σ' ∧ NFr false r σ1 σ' ∧ ActIdle σ' ∧
      (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ CurRunM σ' := by
  set x1 : Tcb := { x with tcbState := .running } with hx1
  set x3 : Tcb := setReg x1 badge_register badge with hx3
  set σA := updK σ1 t (.tcb x1) with hσA
  set σ2 := Notif.stsAct σA t with hσ2
  set σ3 := wakeSt3 σ1 t x badge with hσ3
  have hk2 : σ2.kheap t = some (.tcb x1) := by rw [hσ2, stsAct_kheap]; simp [hσA, updK]
  have hkp2 : ∀ p, p ≠ t → σ2.kheap p = σ1.kheap p := fun p hp => by
    rw [hσ2, stsAct_kheap]; simp only [hσA, updK, Function.update_of_ne hp]
  have hk3 : σ3.kheap t = some (.tcb x3) := by
    show (updK σ2 t (.tcb x3)).kheap t = _; simp [updK]
  have hkp3 : ∀ p, p ≠ t → σ3.kheap p = σ1.kheap p := fun p hp => by
    show (updK σ2 t (.tcb x3)).kheap p = _
    simp only [updK, Function.update_of_ne hp]; exact hkp2 p hp
  have hI3 : Inv σ3 := wake_inv3 hI hkt hxs badge
  -- `t`, blocked, is in no release queue; its SC is active
  have htrel : t ∉ σ1.releaseQueue := fun hm' => by
    obtain ⟨x', -, -, -, h1, -, h3, -⟩ := hI.rel t hm'
    rw [hkt] at h1; cases h1; rw [hxs] at h3; cases h3
  have hsa : ∀ p y k, x.tcbSchedContext = some p → σ1.kheap p = some (.schedContext y k) → scActive y = true := by
    intro p y k hp hky
    obtain ⟨y', k', hky', hyt⟩ := hI.back t x p hkt hp
    rw [hky] at hky'; cases hky'
    exact hB.tcb p y k t x hky hyt hkt (by rw [hxs]; rfl)
  -- the spec's run
  have hsp : specWake t r badge σ1 = specWakeTail t r σ3 := by
    unfold specWake
    rw [nd_bind_one (Notif.setThreadState_eq _ hkt), nd_bind_one (Notif.asUser_setRegister_eq _ _ hk2)]
    rfl
  rw [hsp] at hm
  unfold specWakeTail at hm
  rw [nd_bind_one hND, nd_gets_bind] at hm
  -- the frame to `σ3`
  have hS3 : Sk σ1 σ3 :=
    (show Sk σ1 σA from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).trans
      ((Sk.stsAct σA t).trans (show Sk σ2 σ3 from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))
  have F3 : NFr false r σ1 σ3 := by
    refine ⟨hS3, (fun e => by cases e), fun p => ?_⟩
    by_cases e : p = t
    · subst e
      exact Or.inr ⟨.tcb x, .tcb x3, hkt, hk3, Or.inl ⟨x, .running, x.tcbBoundNotification, x3.tcbArch, rfl, rfl,
        Or.inr ⟨rfl, hxs, Or.inr rfl⟩, Or.inl rfl⟩⟩
    · exact Or.inl (hkp3 p e)
  have ha2 : σ2.schedulerAction = σA.schedulerAction ∨ σ2.schedulerAction = .chooseNewThread :=
    (stsAct_heap σA t).2.2.2
  have ha3 : σ3.schedulerAction = σ1.schedulerAction ∨ σ3.schedulerAction = .chooseNewThread := ha2
  -- the schedulability test and the switch
  obtain ⟨σ4, h4, F4, hI4, ha4, hk4e⟩ : ∃ σ4,
      (NonDet.when (schedulable t σ3 = true) (possibleSwitchTo (Z := Unit) t)) σ3 = ({((), σ4)}, False) ∧
      NFr false r σ3 σ4 ∧ Inv σ4 ∧
      (σ4.schedulerAction = σ3.schedulerAction ∨ σ4.schedulerAction = .chooseNewThread ∨
        (σ3.schedulerAction = .resumeCurThread ∧ σ4.schedulerAction = .switchThread t ∧
          schedulable t σ3 = true)) ∧ σ4.kheap = σ3.kheap := by
    by_cases hs : schedulable t σ3 = true
    · obtain ⟨σ4, he4, hq4⟩ := pst_q hk3 hI3.actReady
      have hQ := possibleSwitchTo_qchange hI3 hs he4
      refine ⟨σ4, by unfold NonDet.when; rw [if_pos hs]; exact he4, hq4.nfr, hI3.qchange hQ, ?_, hQ.1⟩
      rcases pst_act hk3 hI3.actReady he4 with e | e | ⟨e1, e2⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr ⟨e1, e2, hs⟩)
    · exact ⟨σ3, by unfold NonDet.when; rw [if_neg hs]; rfl, NFr.refl _ _ _, hI3, Or.inl rfl, rfl⟩
  rw [nd_bind_one h4] at hm
  have hu : ((), σ') ∈ (specUnblock t σ4).1 := hm
  have hk4 : σ4.kheap t = some (.tcb x3) := by rw [hk4e]; exact hk3
  have hsa4 : ∀ p y k, x3.tcbSchedContext = some p → σ4.kheap p = some (.schedContext y k) →
      scActive y = true := by
    intro p y k hp hky
    have hpt : p ≠ t := by rintro rfl; rw [hk4] at hky; cases hky
    rw [hk4e, hkp3 p hpt] at hky
    exact hsa p y k hp hky
  obtain ⟨F5, ha5⟩ := unblock_frame hI4 hk4 hsa4 hu r
  have FF : NFr false r σ1 σ' := F3.trans (F4.trans F5)
  have hrel4 : σ4.releaseQueue = σ1.releaseQueue := (F3.trans F4).sk.rel
  have hI' : Inv σ' := hI4.unblockTail hk4 (fun p y k _ _ hm' => absurd (hrel4 ▸ hm') htrel)
    (fun p y k hp hky _ => hsa4 p y k hp hky) hu
  -- the action
  have hact : σ'.schedulerAction = σ1.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread ∨
      (σ1.schedulerAction = .resumeCurThread ∧ σ'.schedulerAction = .switchThread t ∧
        schedulable t σ3 = true) := by
    rw [ha5]
    rcases ha4 with e | e | ⟨e1, e2, e3⟩
    · rw [e]; exact ha3.imp_right Or.inl
    · exact Or.inr (Or.inl e)
    · rcases ha3 with e' | e'
      · exact Or.inr (Or.inr ⟨by rw [← e']; exact e1, e2, e3⟩)
      · rw [e'] at e1; cases e1
  have hcn : σ1.schedulerAction = .chooseNewThread → σ'.schedulerAction = .chooseNewThread := by
    intro e
    rcases hact with e' | e' | ⟨e1, -, -⟩
    · rw [e', e]
    · exact e'
    · rw [e] at e1; cases e1
  refine ⟨hI', FF.bsa hB, FF, ⟨fun u hu' => ?_, FF.idleOK hAI.2⟩, ?_, ?_⟩
  · rcases hact with e | e | ⟨-, e2, e3⟩
    · exact FF.sched (hAI.1 u (by rw [← e]; exact hu'))
    · rw [e] at hu'; cases hu'
    · rw [e2] at hu'; cases hu'
      exact (F4.trans F5).sched e3
  · rcases hcur with e | hC
    · exact Or.inl (hcn e)
    · exact Or.inr (FF.curInv hC)
  · refine hrun.of_act FF.curRunW fun e => ?_
    rcases hact with e' | e' | ⟨e1, -, -⟩
    · rw [e']; exact e
    · exact act_cn_nr e'
    · exact absurd e1 e

end Spec

end

end Fl4Proofs.P3.Sched
