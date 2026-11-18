/-
P3 (DESIGN.md §9), IPC: **the scheduler invariants across `send_signal`'s
wake-up with or without an SC donation** (spec side only), toward
`SignalRestJHyp` (ScSignalJ), in the frame `DWFr` (IpcSignalDonFr).

* `unblock_shapeS`, `unblock_frameS`: IpcSignalWakeSpec's `unblock_shape`,
  `unblock_frame` with the thread's SC active only when sporadic (a donated
  SC need not be active; `SchedValid.scSpor` gives sporadic ⇒ active).
* `wake_tailD`: from the state after the wake's writes (the thread `t`
  `running`, in no queue): `maybe_donate_sc` (`donate_dfr`, `Inv.donate`,
  `ActIdle.donate`), the switch when schedulable, the sporadic check
  (`Inv.unblockTail` with `Inv.donate`'s release-queue fact): `Inv`,
  `BlockedScActive`, `DWFr`, `ActIdle`, the action `choose_new_thread` or
  `CurInv`, `CurRunM`.
* `wake_f3`, `wake_f3B`: the wake's writes in `NFr` (a waiting
  notification's head) and `CFr` (a bound thread made inactive by its
  `cancel_ipc`).
* `wake_specG`: `wake_tailD` from the state before the writes, given `Inv`
  after them and their frame `CFr`.
-/
import Fl4Proofs.P3.IpcSignalDonFr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- `unblock_shape` with the SC active when sporadic. -/
theorem unblock_shapeS {σ σ' : State Unit} (hI : Inv σ) {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x))
    (hsa : ∀ p y k, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y k) → y.scSporadic = true →
      scActive y = true)
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
    have hne : y.scSporadic = true → y.scRefills ≠ [] := fun hs => hI.ne c y k hky (hsa c y k hxc hky hs)
    obtain ⟨σ3', hm3', hc3⟩ := unblockCur_some hky hne
    have e3 : σ3' = σ' := congrArg Prod.snd (hdet _ (by rw [hxc]; exact hm3'))
    subst e3
    rcases hc3 with e | ⟨z, e, -, -, hz, -, -⟩
    · exact Or.inl e
    · by_cases hcc : c = σ.curSc
      · exact Or.inl (unblockCur_self hky hcc hm3')
      · exact Or.inr ⟨c, y, z, k, rfl, hky, e, hz, hcc⟩

/-- `unblock_frame` with the SC active when sporadic. -/
theorem unblock_frameS {σ σ' : State Unit} (hI : Inv σ) {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x))
    (hsa : ∀ p y k, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y k) → y.scSporadic = true →
      scActive y = true)
    (hm : ((), σ') ∈ (specUnblock t σ).1) (r : ObjRef) :
    NFr false r σ σ' ∧ σ'.schedulerAction = σ.schedulerAction := by
  rcases unblock_shapeS hI hkt hsa hm with e | ⟨c, y, z, k, -, hky, e, hz, hcc⟩
  · subst e; exact ⟨NFr.refl _ _ _, rfl⟩
  · subst e
    refine ⟨?_, rfl⟩
    have h0 : NFr false r σ { σ with reprogramTimer := true } :=
      NFr.ofSk ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun e => by cases e) rfl
    exact h0.trans (NFr.upd (σ := { σ with reprogramTimer := true }) (o' := .schedContext z k) hky
      (Or.inr (Or.inl ⟨y, k, z.scRefills, y.scNtfn, rfl, congrArg (fun w => KernelObject.schedContext w k) hz,
        fun h => absurd (h.resolve_right (by simp)) hcc, Or.inl rfl⟩)))

set_option maxHeartbeats 8000000 in
/-- **The wake's tail with or without a donation** (module docstring). -/
theorem wake_tailD {σ3 σd σ' : State Unit} {r t : ObjRef} {x3 : Tcb} {xn : Notification}
    (hI3 : Inv σ3) (hB3 : BlockedScActive σ3) (hAI3 : ActIdle σ3)
    (hcur3 : σ3.schedulerAction = .chooseNewThread ∨ CurInv σ3) (hrun3 : CurRunM σ3)
    (hk3 : σ3.kheap t = some (.tcb x3)) (hxr : x3.tcbState = .running)
    (hkn3 : σ3.kheap r = some (.notification xn)) (hnq3 : NotQueued σ3 t)
    (hoff3 : OffOK σ3)
    (hsp3 : ∀ c y k, σ3.kheap c = some (.schedContext y k) → y.scSporadic = true → scActive y = true)
    (hD : maybeDonateSc (Z := Unit) t r σ3 = ({((), σd)}, False))
    (hm : ((), σ') ∈ (specWakeTail t r σ3).1) :
    Inv σ' ∧ BlockedScActive σ' ∧ DWFr r t σ3 σ' ∧ ActIdle σ' ∧
      (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ CurRunM σ' := by
  unfold specWakeTail at hm
  rw [nd_bind_one hD, nd_gets_bind] at hm
  have hrun3' : runnable x3.tcbState = true := by rw [hxr]; rfl
  have hnipc : ∀ x, σ3.kheap t = some (.tcb x) → ipcQueuedThreadState x.tcbState = false := fun x hx => by
    rw [hk3] at hx; cases hx; rw [hxr]; rfl
  -- the donation
  obtain ⟨Fd, had, -, -, Bd⟩ := donate_dfr (r := r) hI3 hk3 hkn3 hnq3 hoff3 hB3 hnipc hD
  obtain ⟨Id, hrq⟩ := Inv.donate hI3 hk3 hkn3 hrun3' hnq3 hD
  have AId : ActIdle σd := ActIdle.donate hAI3 hI3 hk3 hkn3 hnq3 hD
  obtain ⟨xd, hkd⟩ : ∃ xd, σd.kheap t = some (.tcb xd) := by
    obtain ⟨st, bn, fl, ar, sc, hkd, -⟩ := Fd.tcbF hk3
    exact ⟨_, hkd⟩
  -- the schedulability test and the switch
  obtain ⟨σ4, h4, F4, hI4, ha4, hk4e, ht4, hr4⟩ : ∃ σ4,
      (NonDet.when (schedulable t σd = true) (possibleSwitchTo (Z := Unit) t)) σd = ({((), σ4)}, False) ∧
      NFr false r σd σ4 ∧ Inv σ4 ∧
      (σ4.schedulerAction = σd.schedulerAction ∨ σ4.schedulerAction = .chooseNewThread ∨
        (σd.schedulerAction = .resumeCurThread ∧ σ4.schedulerAction = .switchThread t ∧
          schedulable t σd = true)) ∧ σ4.kheap = σd.kheap ∧ σ4.curTime = σd.curTime ∧
      σ4.releaseQueue = σd.releaseQueue := by
    by_cases hs : schedulable t σd = true
    · obtain ⟨σ4, he4, hq4⟩ := pst_q hkd Id.actReady
      have hQ := possibleSwitchTo_qchange Id hs he4
      have hn4 := hq4.nfr (r := r)
      obtain ⟨rq, act, e4⟩ := hq4
      refine ⟨σ4, by unfold NonDet.when; rw [if_pos hs]; exact he4, hn4, Id.qchange hQ, ?_, hQ.1,
        by rw [e4], by rw [e4]⟩
      rcases pst_act hkd Id.actReady he4 with e | e | ⟨e1, e2⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr ⟨e1, e2, hs⟩)
    · exact ⟨σd, by unfold NonDet.when; rw [if_neg hs]; rfl, NFr.refl _ _ _, Id, Or.inl rfl, rfl, rfl, rfl⟩
  rw [nd_bind_one h4] at hm
  have hu : ((), σ') ∈ (specUnblock t σ4).1 := hm
  have hk4 : σ4.kheap t = some (.tcb xd) := by rw [hk4e]; exact hkd
  have hsa4 : ∀ p y k, xd.tcbSchedContext = some p → σ4.kheap p = some (.schedContext y k) →
      y.scSporadic = true → scActive y = true := by
    intro p y k _ hky hs
    rw [hk4e] at hky
    obtain ⟨y0, rf, nt, tc, hy0, rfl, -⟩ := Fd.scB hky
    exact hsp3 p y0 k hy0 hs
  obtain ⟨F5, ha5⟩ := unblock_frameS hI4 hk4 hsa4 hu r
  have FF : DWFr r t σ3 σ' := Fd.trans (DWFr.ofNFr (F4.trans F5))
  have hI' : Inv σ' := hI4.unblockTail hk4
    (fun p y n hp hky hm' => by
      rw [ht4]; exact hrq xd p y n hkd hp (by rw [← hk4e]; exact hky) (by rw [← hr4]; exact hm'))
    hsa4 hu
  -- the action
  have hact : σ'.schedulerAction = σ3.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread ∨
      (σ3.schedulerAction = .resumeCurThread ∧ σ'.schedulerAction = .switchThread t ∧
        schedulable t σd = true) := by
    rw [ha5, ← had]
    rcases ha4 with e | e | ⟨e1, e2, e3⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr ⟨e1, e2, e3⟩)
  have hcn : σ3.schedulerAction = .chooseNewThread → σ'.schedulerAction = .chooseNewThread := by
    intro e
    rcases hact with e' | e' | ⟨e1, -, -⟩
    · rw [e', e]
    · exact e'
    · rw [e] at e1; cases e1
  refine ⟨hI', (F4.trans F5).bsa Bd, FF, ⟨fun u hu' => ?_, FF.idleOK hAI3.2⟩, ?_, ?_⟩
  · rcases hact with e | e | ⟨-, e2, e3⟩
    · exact FF.sched (hAI3.1 u (by rw [← e]; exact hu'))
    · rw [e] at hu'; cases hu'
    · rw [e2] at hu'; cases hu'
      exact (F4.trans F5).sched e3
  · rcases hcur3 with e | hC
    · exact Or.inl (hcn e)
    · exact Or.inr (FF.curInv hC)
  · refine hrun3.of_act FF.curRunW fun e => ?_
    rcases hact with e' | e' | ⟨e1, -, -⟩
    · rw [e']; exact e
    · exact act_cn_nr e'
    · exact absurd e1 e

/-- **The wake's writes of a thread blocked on `r`** in `NFr false r`. -/
theorem wake_f3 {σ1 : State Unit} {r t : ObjRef} {x : Tcb} (hkt : σ1.kheap t = some (.tcb x))
    (hxs : x.tcbState = .blockedOnNotification r) (badge : Word) : NFr false r σ1 (wakeSt3 σ1 t x badge) := by
  set x1 : Tcb := { x with tcbState := .running } with hx1
  set x3 : Tcb := setReg x1 badge_register badge with hx3
  set σA := updK σ1 t (.tcb x1) with hσA
  set σ2 := Notif.stsAct σA t with hσ2
  have hkp2 : ∀ p, p ≠ t → σ2.kheap p = σ1.kheap p := fun p hp => by
    rw [hσ2, stsAct_kheap]; simp only [hσA, updK, Function.update_of_ne hp]
  have hk3 : (wakeSt3 σ1 t x badge).kheap t = some (.tcb x3) := by
    show (updK σ2 t (.tcb x3)).kheap t = _; simp [updK]
  have hkp3 : ∀ p, p ≠ t → (wakeSt3 σ1 t x badge).kheap p = σ1.kheap p := fun p hp => by
    show (updK σ2 t (.tcb x3)).kheap p = _
    simp only [updK, Function.update_of_ne hp]; exact hkp2 p hp
  have hS3 : Sk σ1 (wakeSt3 σ1 t x badge) :=
    (show Sk σ1 σA from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).trans
      ((Sk.stsAct σA t).trans (show Sk σ2 (updK σ2 t (.tcb x3)) from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))
  refine ⟨hS3, (fun e => by cases e), fun p => ?_⟩
  by_cases e : p = t
  · subst e
    exact Or.inr ⟨.tcb x, .tcb x3, hkt, hk3, Or.inl ⟨x, .running, x.tcbBoundNotification, x3.tcbArch, rfl, rfl,
      Or.inr ⟨rfl, hxs, Or.inr rfl⟩, Or.inl rfl⟩⟩
  · exact Or.inl (hkp3 p e)

/-- **The wake's writes of an inactive bound thread** in `CFr r t`. -/
theorem wake_f3B {σ1 : State Unit} {r t : ObjRef} {x : Tcb} (hkt : σ1.kheap t = some (.tcb x))
    (hxs : x.tcbState = .inactive) (badge : Word) : CFr r t σ1 (wakeSt3 σ1 t x badge) := by
  set x1 : Tcb := { x with tcbState := .running } with hx1
  set x3 : Tcb := setReg x1 badge_register badge with hx3
  set σA := updK σ1 t (.tcb x1) with hσA
  set σ2 := Notif.stsAct σA t with hσ2
  have hkp2 : ∀ p, p ≠ t → σ2.kheap p = σ1.kheap p := fun p hp => by
    rw [hσ2, stsAct_kheap]; simp only [hσA, updK, Function.update_of_ne hp]
  have hk3 : (wakeSt3 σ1 t x badge).kheap t = some (.tcb x3) := by
    show (updK σ2 t (.tcb x3)).kheap t = _; simp [updK]
  have hkp3 : ∀ p, p ≠ t → (wakeSt3 σ1 t x badge).kheap p = σ1.kheap p := fun p hp => by
    show (updK σ2 t (.tcb x3)).kheap p = _
    simp only [updK, Function.update_of_ne hp]; exact hkp2 p hp
  have hS3 : Sk σ1 (wakeSt3 σ1 t x badge) :=
    (show Sk σ1 σA from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).trans
      ((Sk.stsAct σA t).trans (show Sk σ2 (updK σ2 t (.tcb x3)) from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))
  refine ⟨hS3, fun p => ?_⟩
  by_cases e : p = t
  · subst e
    exact Or.inr ⟨.tcb x, .tcb x3, hkt, hk3, Or.inl ⟨x, .running, x.tcbBoundNotification, x.tcbFault, x3.tcbArch,
      rfl, rfl, Or.inr ⟨Or.inl rfl, rfl, Or.inr hxs, Or.inr (Or.inl rfl)⟩⟩⟩
  · exact Or.inl (hkp3 p e)

set_option maxHeartbeats 8000000 in
/-- **The scheduler invariants after a wake with or without a donation**
(module docstring). -/
theorem wake_specG {σ1 σd σ' : State Unit} {r t : ObjRef} {x : Tcb} {xn : Notification} {badge : Word}
    (hI : Inv σ1) (hI3 : Inv (wakeSt3 σ1 t x badge)) (hB : BlockedScActive σ1) (hAI : ActIdle σ1)
    (hcur : σ1.schedulerAction = .chooseNewThread ∨ CurInv σ1) (hrun : CurRunM σ1)
    (hkt : σ1.kheap t = some (.tcb x)) (hxr : runnable x.tcbState = false)
    (F3 : CFr r t σ1 (wakeSt3 σ1 t x badge)) (hkn : σ1.kheap r = some (.notification xn))
    (hoff : OffOK σ1)
    (hsp : ∀ c y k, σ1.kheap c = some (.schedContext y k) → y.scSporadic = true → scActive y = true)
    (hD : maybeDonateSc (Z := Unit) t r (wakeSt3 σ1 t x badge) = ({((), σd)}, False))
    (hm : ((), σ') ∈ (specWake t r badge σ1).1) :
    Inv σ' ∧ BlockedScActive σ' ∧ DWFr r t σ1 σ' ∧ ActIdle σ' ∧
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
  have htn : t ≠ r := by rintro rfl; rw [hkt] at hkn; cases hkn
  have hkn3 : σ3.kheap r = some (.notification xn) := by rw [hkp3 r (Ne.symm htn)]; exact hkn
  have hq3 : σ3.readyQueues = σ1.readyQueues := by
    show (Notif.stsAct σA t).readyQueues = _; unfold Notif.stsAct; split <;> rfl
  have hr3 : σ3.releaseQueue = σ1.releaseQueue := F3.sk.rel
  have hnq1 := hI.notQueued hkt hxr
  have hnq3 : NotQueued σ3 t := ⟨fun d p => by rw [hq3]; exact hnq1.1 d p, by rw [hr3]; exact hnq1.2⟩
  have hsp3 : ∀ c y k, σ3.kheap c = some (.schedContext y k) → y.scSporadic = true → scActive y = true := by
    intro c y k hc
    have hct : c ≠ t := by rintro rfl; rw [hk3] at hc; cases hc
    rw [hkp3 c hct] at hc; exact hsp c y k hc
  have hoff3 : OffOK σ3 := F3.off hoff
  have ha3 : σ3.schedulerAction = σ1.schedulerAction ∨ σ3.schedulerAction = .chooseNewThread :=
    (stsAct_heap σA t).2.2.2
  have hcn3 : σ1.schedulerAction = .chooseNewThread → σ3.schedulerAction = .chooseNewThread := fun e => by
    rcases ha3 with e' | e'
    · rw [e', e]
    · exact e'
  have hAI3 : ActIdle σ3 := by
    refine ⟨fun u hu => ?_, F3.idleOK hAI.2⟩
    rcases ha3 with e | e
    · exact F3.sched (hAI.1 u (by rw [← e]; exact hu))
    · rw [e] at hu; cases hu
  have hsw : specWake t r badge σ1 = specWakeTail t r σ3 := by
    unfold specWake
    rw [nd_bind_one (Notif.setThreadState_eq _ hkt), nd_bind_one (Notif.asUser_setRegister_eq _ _ hk2)]
    rfl
  rw [hsw] at hm
  obtain ⟨I', B', F', AI', cur', run'⟩ := wake_tailD (x3 := x3) hI3 (F3.bsa hB) hAI3 (hcur.imp hcn3 F3.curInv)
    (hrun.of_act F3.curRunW fun e => by
      rcases ha3 with e' | e'
      · rw [e']; exact e
      · exact act_cn_nr e') hk3 rfl hkn3 hnq3 hoff3 hsp3 hD hm
  exact ⟨I', B', (DWFr.ofCFr F3).trans F', AI', cur', run'⟩

end Spec

end

end Fl4Proofs.P3.Sched
