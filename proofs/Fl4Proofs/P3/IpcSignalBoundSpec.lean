/-
P3 (DESIGN.md §9), IPC: **the scheduler invariants across `send_signal`'s
wake-up of the idle notification `r`'s bound thread `t` blocked receiving**
(spec side only), toward `SignalRestJHyp` (ScSignalJ), in the frame `CFr r t`
(IpcSignalBoundFr).

* `cancelIpc_recv_cfr`: `cancel_ipc t` of `t` blocked receiving (on an
  endpoint holding it, with its reply naming it): the frame `CFr r t`, `t`
  `Inactive` with no fault, the action kept or `choose_new_thread`.
* `cancel_recv_inv`: `Inv` after it (`ikm_cancelIpc`, `InvBut.ik`: `t`, not
  runnable, in no queue; `t`'s `RelIfBound` given).
* `wake_inv3B`, `wake_specB`: `wake_inv3`, `wake_spec` (IpcSignalWakeSpec) for
  an inactive thread bound to `r` with `RelIfBound` (`Inv.stable`'s
  `NoBlock`), its SC active, in the frame `CFr r t`.
-/
import Fl4Proofs.P3.IpcSignalBoundFr
import Fl4Proofs.P3.ScRestartSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- A bound receive-blocked or inactive thread set `Inactive`. -/
theorem CFr.stsIn {r t : ObjRef} {σ : State Unit} {y : Tcb} (hk : σ.kheap t = some (.tcb y))
    (hrb : RbIn y.tcbState) :
    CFr r t σ (stsAct (updK σ t (.tcb { y with tcbState := .inactive })) t) :=
  (CFr.upd hk (Or.inl ⟨y, .inactive, y.tcbBoundNotification, y.tcbFault, y.tcbArch, rfl, rfl,
    Or.inr ⟨Or.inl rfl, rfl, hrb, Or.inl rfl⟩⟩)).trans (CFr.sts _ _ _ _)

theorem act_sts {σ : State Unit} {u : ObjRef} {σ0 : State Unit}
    (h : σ.schedulerAction = σ0.schedulerAction ∨ σ.schedulerAction = .chooseNewThread) :
    (stsAct σ u).schedulerAction = σ0.schedulerAction ∨ (stsAct σ u).schedulerAction = .chooseNewThread := by
  rcases (stsAct_heap σ u).2.2.2 with e | e
  · rw [e]; exact h
  · exact Or.inr e

set_option maxHeartbeats 4000000 in
/-- **`cancel_ipc` of a bound thread blocked receiving** in the frame `CFr`
(module docstring). -/
theorem cancelIpc_recv_cfr {σ σ1 : State Unit} {r t ep : ObjRef} {ro : Option ObjRef} {d : ReceiverPayload}
    {x : Tcb} {xe : Endpoint} (hkt : σ.kheap t = some (.tcb x)) (hst : x.tcbState = .blockedOnReceive ep ro d)
    (hke : σ.kheap ep = some (.endpoint xe)) (hq : t ∈ xe.epQueue)
    (hro : ∀ rp, ro = some rp → ∃ xr, σ.kheap rp = some (.reply xr) ∧ xr.replyTcb = some t)
    (hm : ((), σ1) ∈ (cancelIpc (Z := Unit) t σ).1) :
    CFr r t σ σ1 ∧ σ1.kheap t = some (.tcb { x with tcbFault := none, tcbState := .inactive }) ∧
      (σ1.schedulerAction = σ.schedulerAction ∨ σ1.schedulerAction = .chooseNewThread) := by
  have hte : t ≠ ep := by rintro rfl; rw [hkt] at hke; cases hke
  have hrb : RbIn x.tcbState := Or.inl ⟨ep, ro, d, hst⟩
  set x1 : Tcb := { x with tcbFault := none } with hx1
  set σA := updK σ t (.tcb x1) with hσA
  have hkA : σA.kheap t = some (.tcb x1) := by simp [hσA, updK]
  have hkeA : σA.kheap ep = some (.endpoint xe) := by simp [hσA, updK, Ne.symm hte, hke]
  have FA : CFr r t σ σA := CFr.upd hkt (Or.inl ⟨x, x.tcbState, x.tcbBoundNotification, none, x.tcbArch, rfl, rfl,
    Or.inr ⟨Or.inl rfl, rfl, hrb, Or.inr (Or.inr rfl)⟩⟩)
  set σB := updK σA ep (.endpoint (Endp.epDeq xe t)) with hσB
  have hkB : σB.kheap t = some (.tcb x1) := by simp [hσB, updK, hte, hkA]
  have FB : CFr r t σA σB := CFr.upd hkeA (Or.inr (Or.inr (Or.inl ⟨xe, Endp.epDeq xe t, rfl, rfl,
    by rw [epDeq_queue']; unfold removeAll; exact List.filter_sublist, hq⟩)))
  have hdq : tcbEpDequeue (Z := Unit) t ep σA = ({((), σB)}, False) := Endp.tcbEpDequeue_eq hkeA hq
  have hrb1 : RbIn x1.tcbState := hrb
  have hc0 : ∀ σX : State Unit, blockedCancelIpc (Z := Unit) (.blockedOnReceive ep ro d) t ro σA =
      ({((), σX)}, False) → σ1 = σX := by
    intro σX h
    have hts : threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) t σ = ({((), σA)}, False) :=
      threadSet_eq _ hkt
    have e : cancelIpc (Z := Unit) t σ = ({((), σX)}, False) := by
      unfold cancelIpc
      rw [nd_bind_one (getThreadState_eq hkt), nd_bind_one hts, hst]
      exact h
    rw [e] at hm
    exact (Prod.mk.inj (Set.mem_singleton_iff.1 hm)).2
  have hasrt : NonDet.assertOpt (σ := State Unit) (epBlocked (.blockedOnReceive ep ro d)) σA =
      ({(ep, σA)}, False) := rfl
  cases ro with
  | none =>
    have e1 := hc0 _ (by
      unfold blockedCancelIpc getBlockingObject
      rw [nd_bind_one hasrt, nd_bind_one hdq]
      dsimp only
      rw [Notif.setThreadState_eq _ hkB])
    subst e1
    refine ⟨(FA.trans FB).trans (CFr.stsIn hkB hrb1), by rw [stsAct_kheap]; simp [updK, hx1], ?_⟩
    exact act_sts (Or.inl rfl)
  | some rp =>
    obtain ⟨xr, hkr, hrt⟩ := hro rp rfl
    have hre : rp ≠ ep := by rintro rfl; rw [hkr] at hke; cases hke
    have htr : t ≠ rp := by rintro rfl; rw [hkt] at hkr; cases hkr
    have hkrB : σB.kheap rp = some (.reply xr) := by simp [hσB, hσA, updK, hre, Ne.symm htr, hkr]
    set σC := updK σB rp (.reply { xr with replyTcb := none }) with hσC
    have hkC : σC.kheap t = some (.tcb x1) := by simp [hσC, updK, htr, hkB]
    have FC : CFr r t σB σC := CFr.upd hkrB (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hrt⟩)))
    set x3 : Tcb := { x1 with tcbState := .inactive } with hx3
    set σD := stsAct (updK σC t (.tcb x3)) t with hσD
    have hkD : σD.kheap t = some (.tcb x3) := by rw [hσD, stsAct_kheap]; simp [updK]
    have FD : CFr r t σC σD := CFr.stsIn hkC hrb1
    have e3 : replyUnlinkTcb (Z := Unit) t rp σB = ({((), σD)}, False) :=
      (replyUnlinkTcb_eq hkrB hrt hkB (Or.inr ⟨ep, d, hst⟩) htr).trans (Notif.setThreadState_eq _ hkC)
    have e1 := hc0 _ (by
      unfold blockedCancelIpc getBlockingObject
      rw [nd_bind_one hasrt, nd_bind_one hdq]
      dsimp only
      rw [nd_bind_one e3, Notif.setThreadState_eq _ hkD])
    subst e1
    refine ⟨(((FA.trans FB).trans FC).trans FD).trans (CFr.stsIn hkD (Or.inr rfl)),
      by rw [stsAct_kheap]; simp [updK, hx3, hx1], ?_⟩
    exact act_sts (act_sts (Or.inl rfl))

/-- **`Inv` after `cancel_ipc` of a thread blocked receiving** (module
docstring). -/
theorem cancel_recv_inv {σ σ1 : State Unit} {t : ObjRef} {x : Tcb} (hI : Inv σ) (hkt : σ.kheap t = some (.tcb x))
    (hrb : RbIn x.tcbState) (hm : ((), σ1) ∈ (cancelIpc (Z := Unit) t σ).1) (hrib : RelIfBound σ1 t) :
    Inv σ1 := by
  have ik : IK t σ σ1 := ikm_cancelIpc σ ((), σ1) hm
  obtain ⟨hB, -⟩ := (hI.toBut t).ik (hI.notQueued hkt hrb.not_run) ik
  exact hB.inv fun _ _ _ => hrib

/-- **`Inv` after the wake's writes** for an inactive thread bound with
`RelIfBound` (module docstring). -/
theorem wake_inv3B {σ1 : State Unit} {t : ObjRef} {x : Tcb} (hI : Inv σ1) (hkt : σ1.kheap t = some (.tcb x))
    (hxs : x.tcbState = .inactive) (hrib : RelIfBound σ1 t) (badge : Word) : Inv (wakeSt3 σ1 t x badge) := by
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
      exact Or.inr ⟨rfl, by rw [hxs]; nofun, Or.inr hrib⟩
    · left
      have h' : σA.kheap p = some (.tcb z) := hz
      rw [hkpA p e, hy] at h'; cases h'; rfl
  have hI2 : Inv (Notif.stsAct σA t) := hIA.qchange (qchange_stsAct σA t)
  have hk2 : (Notif.stsAct σA t).kheap t = some (.tcb x1) := by rw [stsAct_kheap]; exact hktA
  show Inv (updK (Notif.stsAct σA t) t (.tcb (setReg x1 badge_register badge)))
  exact hI2.tcbUpd hk2 _ rfl rfl

set_option maxHeartbeats 4000000 in
/-- **The scheduler invariants after the wake of an inactive bound thread**
(module docstring; `wake_spec`'s proof in `CFr`). -/
theorem wake_specB {σ1 σ' : State Unit} {r t : ObjRef} {x : Tcb} {badge : Word}
    (hI : Inv σ1) (hB : BlockedScActive σ1) (hAI : ActIdle σ1)
    (hcur : σ1.schedulerAction = .chooseNewThread ∨ CurInv σ1) (hrun : CurRunM σ1)
    (hkt : σ1.kheap t = some (.tcb x)) (hxs : x.tcbState = .inactive)
    (hrib : RelIfBound σ1 t)
    (hsa : ∀ p y k, x.tcbSchedContext = some p → σ1.kheap p = some (.schedContext y k) → scActive y = true)
    (hND : maybeDonateSc (Z := Unit) t r (wakeSt3 σ1 t x badge) = ({((), wakeSt3 σ1 t x badge)}, False))
    (hm : ((), σ') ∈ (specWake t r badge σ1).1) :
    Inv σ' ∧ BlockedScActive σ' ∧ CFr r t σ1 σ' ∧ ActIdle σ' ∧
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
  have hI3 : Inv σ3 := wake_inv3B hI hkt hxs hrib badge
  -- `t`, not runnable, is in no release queue
  have htrel : t ∉ σ1.releaseQueue := fun hm' => by
    obtain ⟨x', -, -, -, h1, -, h3, -⟩ := hI.rel t hm'
    rw [hkt] at h1; cases h1; rw [hxs] at h3; cases h3
  have hsp : specWake t r badge σ1 = specWakeTail t r σ3 := by
    unfold specWake
    rw [nd_bind_one (Notif.setThreadState_eq _ hkt), nd_bind_one (Notif.asUser_setRegister_eq _ _ hk2)]
    rfl
  rw [hsp] at hm
  unfold specWakeTail at hm
  rw [nd_bind_one hND, nd_gets_bind] at hm
  have hS3 : Sk σ1 σ3 :=
    (show Sk σ1 σA from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).trans
      ((Sk.stsAct σA t).trans (show Sk σ2 σ3 from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))
  have F3 : CFr r t σ1 σ3 := by
    refine ⟨hS3, fun p => ?_⟩
    by_cases e : p = t
    · subst e
      exact Or.inr ⟨.tcb x, .tcb x3, hkt, hk3, Or.inl ⟨x, .running, x.tcbBoundNotification, x.tcbFault, x3.tcbArch,
        rfl, rfl, Or.inr ⟨Or.inl rfl, rfl, Or.inr hxs, Or.inr (Or.inl rfl)⟩⟩⟩
    · exact Or.inl (hkp3 p e)
  have ha2 : σ2.schedulerAction = σA.schedulerAction ∨ σ2.schedulerAction = .chooseNewThread :=
    (stsAct_heap σA t).2.2.2
  have ha3 : σ3.schedulerAction = σ1.schedulerAction ∨ σ3.schedulerAction = .chooseNewThread := ha2
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
  have FF : CFr r t σ1 σ' := F3.trans (CFr.ofNFr (F4.trans F5))
  have hrel4 : σ4.releaseQueue = σ1.releaseQueue := (hS3.trans F4.sk).rel
  have hI' : Inv σ' := hI4.unblockTail hk4 (fun p y k _ _ hm' => absurd (hrel4 ▸ hm') htrel)
    (fun p y k hp hky _ => hsa4 p y k hp hky) hu
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
