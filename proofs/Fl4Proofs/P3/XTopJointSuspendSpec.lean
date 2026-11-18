/-
P3 (DESIGN.md §9): **the spec side of `suspend`'s scheduler tail at `J`**
(toward `JAtZ.suspendJ`, XTopJointSuspend): after `cancel_ipc` and the
restart PC, `suspend` dequeues the thread, removes it from the release
queue, cuts its yield-to pair and makes it `Inactive` (`suspendSc`). In the
middle `Inv` fails (a thread with an SC out of the release queue), so the four
are one `J` step with one spec frame:

* `SusF t x σ σ'`: the current thread, SC, time, consumed time and idle
  thread kept; the release queue shrunk, without `t`; the scheduler action
  kept or a reschedule set (set when `t` is current and resumed); `t`'s TCB
  `x` made `Inactive` with its yield-to cut; every other object kept but SCs
  with their yield-from cut. `susF_of`: the spec's steps give it.
* What it keeps: `ScTKw` (`SusF.tkw`, `t` IPC-free), `LK`, `FK`, `CKeep`,
  `NSC`, `CurInv`, `CurOwnW`, `OffOK`, `ActIdle` (`t` neither the switch
  target nor idle), `BlockedScActive`, `CurRunM` (`t` may be current: a
  resumed current thread is rescheduled, any other action keeps `CurRunM`).
* `suspendSc_inv`: `Inv` after (TcbSpecInv's `suspend_inv` without the
  `cancel_ipc` and restart-PC steps).
-/
import Fl4Proofs.P3.XTopJointYield
import Fl4Proofs.P3.IpcSuspendJ
import Fl4Proofs.P3.TcbSpecInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical Fl4Proofs.P3.Notif

noncomputable section

/-- **The spec's `suspend` after `cancel_ipc` and the restart PC.** -/
def suspendSc (t : ObjRef) : SMonad Unit Unit := do
  tcbSchedAction tcbSchedDequeue t
  tcbReleaseRemove t
  schedContextCancelYieldTo t
  setThreadState t .inactive

/-- `suspend` split at its scheduler tail. -/
theorem suspend_split (t : ObjRef) : suspend (Z := Unit) t = (do
    cancelIpc t
    let state ← getThreadState t
    NonDet.when (state = .running) <| updateRestartPc t
    suspendSc t) := rfl

set_option maxHeartbeats 8000000 in
/-- **`Inv` after `suspendSc`** (module docstring). -/
theorem suspendSc_inv {σ σ' : State Unit} (h : Inv σ) {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hq : ∀ d p, t ∈ σ.readyQueues d p → d = x.tcbDomain ∧ p = x.tcbPriority)
    (hm : ((), σ') ∈ (suspendSc t σ).1) : Inv σ' := by
  unfold suspendSc at hm
  obtain ⟨y4, h4, hm⟩ := hm
  obtain ⟨y5, h5, hm⟩ := hm
  obtain ⟨y6, h6, hm⟩ := hm
  rw [tcbSchedAction_gen hk] at h4
  have e4 := Set.mem_singleton_iff.1 h4
  obtain ⟨bb, hb⟩ := tcbReleaseRemove_eq y4.2 t
  rw [hb] at h5
  have e5 := Set.mem_singleton_iff.1 h5
  have mid : InvBut y5.2 t ∧ NotQueued y5.2 t := by
    cases hr : runnable x.tcbState
    · have hNQ : NotQueued σ t := h.notQueued hk hr
      have ik4 : IK t σ y4.2 := by
        rw [e4]
        refine IK.of_eq rfl ?_ rfl rfl
        funext d' p'
        simp only [setQ]
        split_ifs with e
        · obtain ⟨rfl, rfl⟩ := e
          unfold tcbSchedDequeue
          exact List.filter_eq_self.2 fun a ha => decide_eq_true fun ea =>
            hNQ.1 x.tcbDomain x.tcbPriority (ea ▸ ha)
        · rfl
      have ik5 : IK t y4.2 y5.2 := by
        rw [e5]
        refine IK.of_eq rfl rfl ?_ rfl
        show List.filter _ _ = _
        exact List.filter_eq_self.2 fun a ha => decide_eq_true fun ea =>
          hNQ.2 (by rw [← ik4.2.2.1]; exact ea ▸ ha)
      exact (h.toBut t).ik hNQ (ik4.trans ik5)
    · have hI4 : Inv y4.2 := by rw [e4]; exact h.qchange (qchange_dequeue hk)
      have hnq4 : ∀ d p, t ∉ y4.2.readyQueues d p := by
        intro d p hm4
        rw [e4] at hm4
        simp only [setQ] at hm4
        split_ifs at hm4 with e
        · unfold tcbSchedDequeue at hm4
          simp at hm4
        · obtain ⟨rfl, rfl⟩ := hq d p hm4
          exact e ⟨rfl, rfl⟩
      have hB : InvBut y5.2 t := by rw [e5]; exact hI4.relRemove t bb
      refine ⟨hB, fun d p => ?_, ?_⟩
      · rw [e5]; exact hnq4 d p
      · rw [e5]; simp [setRel]
  obtain ⟨hB5, hN5⟩ := mid
  have ik6 : IK t y5.2 y6.2 := ikm_cancelYieldTo t y5.2 y6 h6
  have hik7 : IKM t (setThreadState (Z := Unit) t ThreadState.inactive) := ikm_setThreadState _
  have ik7 : IK t y6.2 σ' := hik7 y6.2 ((), σ') hm
  obtain ⟨hB, -⟩ := hB5.ik hN5 (ik6.trans ik7)
  refine hB.inv fun x' hx' hc => ?_
  exfalso
  obtain ⟨x6, hk6, -⟩ := ik7.tcbB hx'
  have hm' : ((), σ') ∈ (setThreadState (Z := Unit) t ThreadState.inactive y6.2).1 := hm
  rw [Notif.setThreadState_eq .inactive hk6] at hm'
  rw [(Prod.mk.inj (Set.mem_singleton_iff.1 hm')).2] at hx'
  rw [stsAct_kheap] at hx'
  simp [updK] at hx'
  subst hx'
  simp [inClass, runnable] at hc

/-! ## The frame -/

/-- **The spec frame of `suspendSc`** (module docstring). -/
structure SusF (t : ObjRef) (x : Tcb) (σ σ' : State Unit) : Prop where
  ct : σ'.curThread = σ.curThread
  csc : σ'.curSc = σ.curSc
  cons : σ'.consumedTime = σ.consumedTime
  tm : σ'.curTime = σ.curTime
  idle : σ'.idleThread = σ.idleThread
  isc : σ'.idleSc = σ.idleSc
  rel : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue
  relt : t ∉ σ'.releaseQueue
  act : σ'.schedulerAction = σ.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread
  actc : σ.curThread = t → σ.schedulerAction = .resumeCurThread → σ'.schedulerAction = .chooseNewThread
  hk : σ.kheap t = some (.tcb x)
  hk' : σ'.kheap t = some (.tcb { x with tcbYieldTo := none, tcbState := .inactive })
  kh : ∀ p, p ≠ t → σ'.kheap p = σ.kheap p ∨ ∃ z n, σ.kheap p = some (.schedContext z n) ∧
    σ'.kheap p = some (.schedContext { z with scYieldFrom := none } n)
  um : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap
  dl : σ'.domainList = σ.domainList
  dsi : σ'.domainStartIndex = σ.domainStartIndex
  arch : σ'.archState = σ.archState
  ist : σ'.interruptStates = σ.interruptStates
  inode : σ'.interruptIrqNode = σ.interruptIrqNode

/-- `stsAct` changes the scheduler action only. -/
theorem stsAct_rec (σ : State Unit) (t : ObjRef) :
    stsAct σ t = { σ with schedulerAction := (stsAct σ t).schedulerAction } := by
  unfold stsAct; split_ifs <;> rfl

set_option maxHeartbeats 4000000 in
/-- **`SusF` from the spec's steps** (module docstring): the state `σ5`
before `set_thread_state Inactive`. -/
theorem susF_of {σ σ5 : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (h5k : σ5.kheap t = some (.tcb { x with tcbYieldTo := none }))
    (h5o : ∀ p, p ≠ t → σ5.kheap p = σ.kheap p ∨ ∃ z n, σ.kheap p = some (.schedContext z n) ∧
      σ5.kheap p = some (.schedContext { z with scYieldFrom := none } n))
    (hct : σ5.curThread = σ.curThread) (hcsc : σ5.curSc = σ.curSc) (hcons : σ5.consumedTime = σ.consumedTime)
    (htm : σ5.curTime = σ.curTime) (hidle : σ5.idleThread = σ.idleThread) (hisc : σ5.idleSc = σ.idleSc)
    (hrel : σ5.releaseQueue = σ.releaseQueue.filter fun u => decide (t ≠ u))
    (hact : σ5.schedulerAction = σ.schedulerAction)
    (hum : σ5.machineState.underlyingMemory = σ.machineState.underlyingMemory) (hcdt : σ5.cdt = σ.cdt)
    (horig : σ5.isOriginalCap = σ.isOriginalCap) (hdl : σ5.domainList = σ.domainList)
    (hdsi : σ5.domainStartIndex = σ.domainStartIndex) (harch : σ5.archState = σ.archState)
    (hist : σ5.interruptStates = σ.interruptStates) (hin : σ5.interruptIrqNode = σ.interruptIrqNode) :
    SusF t x σ (stsAct (updK σ5 t (.tcb { { x with tcbYieldTo := none } with tcbState := .inactive })) t) := by
  have hA := stsAct_action (updK σ5 t (.tcb { { x with tcbYieldTo := none } with tcbState := .inactive })) t
  rw [stsAct_rec]
  refine ⟨hct, hcsc, hcons, htm, hidle, hisc, fun u hu => ?_, fun hu => ?_, ?_, fun hc hr => ?_, hk, ?_, fun p hp => ?_,
    hum, hcdt, horig, hdl, hdsi, harch, hist, hin⟩
  · change u ∈ σ5.releaseQueue at hu
    rw [hrel] at hu
    exact (List.mem_filter.1 hu).1
  · change t ∈ σ5.releaseQueue at hu
    rw [hrel] at hu
    simp at hu
  · rcases hA with e | e
    · exact Or.inr e
    · exact Or.inl (e.trans hact)
  · show (stsAct _ t).schedulerAction = _
    have hns : ¬ schedulable t (updK σ5 t (.tcb { { x with tcbYieldTo := none } with tcbState := .inactive })) =
        true := fun hs => by
      obtain ⟨x', -, -, -, hk', -, hrun, -⟩ := schedulable_inv hs
      simp [updK] at hk'
      subst hk'
      simp [runnable] at hrun
    unfold stsAct
    rw [if_pos ⟨by rw [← hc]; exact hct.symm, by rw [← hr]; exact hact, hns⟩]
  · show Function.update σ5.kheap t _ t = _
    simp
  · have e : Function.update σ5.kheap t
        (some (.tcb { { x with tcbYieldTo := none } with tcbState := .inactive })) p = σ5.kheap p :=
      Function.update_of_ne hp _ _
    show Function.update σ5.kheap t _ p = _ ∨ ∃ z n, _ ∧ Function.update σ5.kheap t _ p = _
    rw [e]
    exact h5o p hp

section
variable {t : ObjRef} {x : Tcb} {σ σ' : State Unit} (F : SusF t x σ σ')
include F

theorem SusF.tcbF {p : ObjRef} {y : Tcb} (hp : σ.kheap p = some (.tcb y)) (hpt : p ≠ t) :
    σ'.kheap p = some (.tcb y) := by
  rcases F.kh p hpt with e | ⟨z, n, h1, -⟩
  · rw [e]; exact hp
  · rw [hp] at h1; cases h1

theorem SusF.tcbB {p : ObjRef} {y : Tcb} (hp : σ'.kheap p = some (.tcb y)) (hpt : p ≠ t) :
    σ.kheap p = some (.tcb y) := by
  rcases F.kh p hpt with e | ⟨z, n, -, h2⟩
  · rw [← e]; exact hp
  · rw [hp] at h2; cases h2

theorem SusF.scF {p : ObjRef} {z : SchedContext} {n : Nat} (hp : σ.kheap p = some (.schedContext z n)) :
    ∃ w, σ'.kheap p = some (.schedContext w n) ∧ w = { z with scYieldFrom := w.scYieldFrom } := by
  have hpt : p ≠ t := by rintro rfl; rw [F.hk] at hp; cases hp
  rcases F.kh p hpt with e | ⟨z', n', h1, h2⟩
  · exact ⟨z, by rw [e]; exact hp, rfl⟩
  · rw [hp] at h1; cases h1; exact ⟨_, h2, rfl⟩

theorem SusF.scB {p : ObjRef} {w : SchedContext} {n : Nat} (hp : σ'.kheap p = some (.schedContext w n)) :
    ∃ z, σ.kheap p = some (.schedContext z n) ∧ w = { z with scYieldFrom := w.scYieldFrom } := by
  have hpt : p ≠ t := by rintro rfl; rw [F.hk'] at hp; cases hp
  rcases F.kh p hpt with e | ⟨z', n', h1, h2⟩
  · exact ⟨w, by rw [← e]; exact hp, rfl⟩
  · rw [hp] at h2; cases h2; exact ⟨z', h1, rfl⟩

theorem SusF.oth {p : ObjRef} {o : KernelObject} (ho : ∀ x, o ≠ .tcb x) (hs : ∀ z n, o ≠ .schedContext z n) :
    σ'.kheap p = some o ↔ σ.kheap p = some o := by
  by_cases hpt : p = t
  · subst hpt; rw [F.hk, F.hk']; constructor <;> intro h <;> cases h <;> exact absurd rfl (ho _)
  rcases F.kh p hpt with e | ⟨z, n, h1, h2⟩
  · rw [e]
  · rw [h1, h2]; constructor <;> intro h <;> cases h <;> exact absurd rfl (hs _ _)

/-- `ScTKw` for an IPC-free thread. -/
theorem SusF.tkw (hfree : IpcFree x.tcbState) : ScTKw (fun p => p = t) σ σ' := by
  refine ⟨fun p => ?_, F.um, F.cdt, F.orig, F.dl, F.dsi, F.arch, F.ist, F.inode, F.ct, F.isc⟩
  by_cases hpt : p = t
  · subst hpt; rw [F.hk, F.hk']
    show TKObj _ _ _
    refine Or.inr (Or.inl ⟨x, { x with tcbYieldTo := none, tcbState := .inactive }, rfl, rfl, rfl,
      Or.inr ⟨rfl, hfree, rfl, rfl, ?_⟩⟩)
    intro _ e; simp at e
  · rcases F.kh p hpt with e | ⟨z, n, h1, h2⟩
    · rw [e]; exact OTK.refl _ _
    · rw [h1, h2]
      show TKObj _ _ _
      exact Or.inr (Or.inr (Or.inl ⟨z, _, n, rfl, rfl⟩))

theorem SusF.lk {W : ObjRef → Prop} : LK W σ σ' := fun p => Or.inr (by
  by_cases hpt : p = t
  · subst hpt; rw [F.hk, F.hk']
    show LObj _ _
    refine ⟨?_, ?_, ?_⟩
    · intro y ey; cases ey; exact ⟨_, rfl, Or.inl rfl⟩
    · intro y n ey; cases ey
    · intro y ey; cases ey
  · rcases F.kh p hpt with e | ⟨z, n, h1, h2⟩
    · rw [e]; exact OL.refl _
    · rw [h1, h2]
      show LObj _ _
      refine ⟨?_, ?_, ?_⟩
      · intro y ey; cases ey
      · intro y m ey; cases ey; exact ⟨_, rfl, Or.inl rfl, Or.inl rfl⟩
      · intro y ey; cases ey)

theorem SusF.fk : FK σ σ' := ⟨F.csc, F.idle, F.isc⟩

theorem SusF.nsc {N C : Set U64} (hN : NSC N C σ) : NSC N C σ' :=
  fun n hn y p hy hp => hN n hn y p ((F.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).1 hy) hp

theorem SusF.ckeep : CKeep σ σ' :=
  ⟨fun q y n hq => let ⟨w, hw, e⟩ := F.scF hq; ⟨w, hw, by rw [e]⟩,
    fun q y hq => ⟨y, (F.oth (o := .reply y) (fun _ e => by cases e) (fun _ _ e => by cases e)).2 hq, rfl, rfl⟩,
    fun p y n hp => let ⟨z, hz, _⟩ := F.scB hp; ⟨z, hz⟩⟩

theorem SusF.curInv (hC : CurInv σ) : CurInv σ' := by
  obtain ⟨xt, hkc, hcs, hnb⟩ := hC.tcb
  obtain ⟨y1, n1, hk1⟩ := hC.sc
  refine ⟨?_, ?_, fun hne y n hy => ?_, fun hm => hC.notRel (by have := F.rel _ hm; rwa [F.ct] at this)⟩
  · by_cases hct : σ.curThread = t
    · rw [hct, F.hk] at hkc; cases hkc
      refine ⟨{ x with tcbYieldTo := none, tcbState := .inactive }, by rw [F.ct, hct]; exact F.hk',
        by rw [F.csc]; exact hcs, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · intro _ e; simp at e
      · intro _ _ e; simp at e
      · intro _ _ _ e; simp at e
    · exact ⟨xt, by rw [F.ct]; exact F.tcbF hkc hct, by rw [F.csc]; exact hcs, hnb⟩
  · obtain ⟨w, hw, -⟩ := F.scF hk1; exact ⟨w, n1, by rw [F.csc]; exact hw⟩
  · rw [F.csc, F.isc] at hne; rw [F.csc] at hy
    obtain ⟨z, hz, e⟩ := F.scB hy
    rw [e]; exact hC.active hne z n hz

theorem SusF.own {T C : Set U64} (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · left
    by_cases hut : u.bv = t
    · rw [hut, F.hk] at hkt; cases hkt
      refine ⟨u, hu, _, by rw [hut]; exact F.hk', by rw [F.csc]; exact hxs, fun y n hy => ?_, fun _ hm => ?_⟩
      · rw [F.csc] at hy; obtain ⟨z, hz, e⟩ := F.scB hy; rw [e]; exact hown z n hz
      · rw [hut] at hm; exact F.relt hm
    · refine ⟨u, hu, xt, F.tcbF hkt hut, by rw [F.csc]; exact hxs, fun y n hy => ?_,
        fun h0 hm => hnr (by rw [← F.cons]; exact h0) (F.rel _ hm)⟩
      rw [F.csc] at hy; obtain ⟨z, hz, e⟩ := F.scB hy; rw [e]; exact hown z n hz
  · refine Or.inr ⟨by rw [F.csc]; exact hcs, fun y n hy => ?_⟩
    rw [F.csc] at hy; obtain ⟨z, hz, e⟩ := F.scB hy; rw [e]; exact hun z n hz

theorem SusF.off (hO : OffOK σ) : OffOK σ' := by
  intro h0 y n hy ha
  rw [F.cons] at h0 ⊢; rw [F.tm]; rw [F.csc] at hy; rw [F.csc, F.isc] at ha
  obtain ⟨z, hz, e⟩ := F.scB hy
  rw [e] at ha ⊢; exact hO h0 z n hz ha

theorem SusF.sched {u : ObjRef} (hu : u ≠ t) (hs : schedulable u σ = true) : schedulable u σ' = true := by
  obtain ⟨y, scp, z, n, hk, hsc, hrun, hkz, hac, hnr⟩ := schedulable_inv hs
  obtain ⟨w, hw, e⟩ := F.scF hkz
  exact schedulable_of (F.tcbF hk hu) hsc hrun hw (by rw [e]; exact hac) (fun hm => hnr (F.rel _ hm))

theorem SusF.actIdle (hA : ActIdle σ) (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t)
    (hid : t ≠ σ.idleThread) : ActIdle σ' := by
  refine ⟨fun u hu => ?_, ?_⟩
  · have hu0 : σ.schedulerAction = .switchThread u := by
      rcases F.act with e | e
      · rw [← e]; exact hu
      · rw [e] at hu; cases hu
    exact F.sched (hsa u hu0) (hA.1 u hu0)
  · obtain ⟨y, h1, h2, h3, h4⟩ := hA.2
    exact ⟨y, by rw [F.idle]; exact F.tcbF h1 (Ne.symm hid), by rw [F.isc]; exact h2, h3,
      fun hm => h4 (by rw [F.idle] at hm; exact F.rel _ hm)⟩

theorem SusF.bsa (hB : BlockedScActive σ) : BlockedScActive σ' := by
  refine ⟨fun p y n u xu hp hyu hku hq => ?_, fun p y n hp hr => ?_⟩
  · obtain ⟨z, hz, e⟩ := F.scB hp
    have hut : u ≠ t := by
      rintro rfl; rw [F.hk'] at hku; cases hku; simp [ipcQueuedThreadState] at hq
    rw [e] at hyu ⊢
    exact hB.tcb p z n u xu hz hyu (F.tcbB hku hut) hq
  · obtain ⟨z, hz, e⟩ := F.scB hp
    rw [e] at hr ⊢
    exact hB.replies p z n hz hr

/-- `CurRunM` after `suspend`: a resumed current thread is rescheduled
(`F.actc`); with any other action pending the current thread may be the
suspended one. -/
theorem SusF.curRun (hR : CurRunM σ) : CurRunM σ' := by
  by_cases hnr : σ'.schedulerAction ≠ .resumeCurThread
  · exact Or.inl hnr
  have hr' : σ'.schedulerAction = .resumeCurThread := not_not.1 hnr
  have ha : σ'.schedulerAction = σ.schedulerAction := F.act.resolve_right (by rw [hr']; intro e; cases e)
  have h0 : ¬ σ.schedulerAction ≠ .resumeCurThread := fun e => e (by rw [← ha]; exact hr')
  right
  rcases hR.resolve_left h0 with h | h
  · left
    intro y hy
    rw [F.ct] at hy
    by_cases hct : σ.curThread = t
    · exact absurd (F.actc hct (not_not.1 h0)) (by rw [hr']; intro e; cases e)
    · exact h y (F.tcbB hy hct)
  · right; rw [F.ct, F.idle]; exact h

end

/-- **`complete_yield_to` keeps the current thread, the scheduler action
and the idle thread** (its yield-to SC, if any, an SC). -/
theorem completeYieldTo_ca {σ σ' : State Unit} {y : ObjRef} {x : Tcb} (hk : σ.kheap y = some (.tcb x))
    (hq : ∀ q, x.tcbYieldTo = some q → ∃ z n, σ.kheap q = some (.schedContext z n))
    (he : completeYieldTo (Z := Unit) y σ = ({((), σ')}, False)) :
    σ'.curThread = σ.curThread ∧ σ'.schedulerAction = σ.schedulerAction ∧ σ'.idleThread = σ.idleThread := by
  cases hyt : x.tcbYieldTo with
  | none =>
    have e := the_result (completeYieldTo_none hk hyt) he
    subst e; exact ⟨rfl, rfl, rfl⟩
  | some q =>
    obtain ⟨z, n, hz⟩ := hq q hyt
    have hqy : q ≠ y := by rintro rfl; rw [hk] at hz; cases hz
    obtain ⟨v, w, hsc⟩ := setConsumed_shape hz hk
    rw [completeYieldTo_some hk hyt, nd_bind_one hsc] at he
    have hk1 : (updK (updSc σ q (scConsumedUpdate (fun _ => v) z) n) y (.tcb (Endp.replyTcb x w))).kheap y =
        some (.tcb (Endp.replyTcb x w)) := by simp [updK]
    have hz1 : (updK (updSc σ q (scConsumedUpdate (fun _ => v) z) n) y (.tcb (Endp.replyTcb x w))).kheap q =
        some (.schedContext (scConsumedUpdate (fun _ => v) z) n) := by simp [updK, updSc, hqy]
    have e := the_result (cancelYieldTo_some hk1 (by rw [← hyt]; rfl) hz1 hqy) he
    subst e; exact ⟨rfl, rfl, rfl⟩

end

end Fl4Proofs.P3.Sched
