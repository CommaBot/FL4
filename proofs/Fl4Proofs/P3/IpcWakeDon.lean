/-
P3 (DESIGN.md §9), IPC: **`WakeOK` across an SC donation** (spec side only),
for the wake tails of the sends that donate (`reply_push` with donation,
`send_ipc`'s donation to a receiver without an SC).

`WakeOK σ d` (IpcSV: the switch target's SC ready and sufficient, every
TCB's SC bound back, the target not `d`) reads only the scheduler view
(`sv`), the time and the action. It is kept by:

* `SVS.wakeOK'`: any `SVS` step;
* `wake_drop`: a TCB losing its SC;
* `wake_scTcb`: an SC bound by no TCB getting a new thread;
* `wake_bind`: `d` bound to an SC whose thread is `d`.

`donate_wake`: `sched_context_donate c d` (any `c`: its old thread loses it);
`replyPush_wake`: `reply_push t d r don`.
-/
import Fl4Proofs.P3.IpcSV
open Classical

namespace Fl4Proofs.P3.SVK
open Fl4Spec Fl4Proofs.P3.Notif

noncomputable section

theorem SVS.wakeOK' {σ σ' : State Unit} (h : SVS σ σ') {d : ObjRef} (hW : WakeOK σ d) : WakeOK σ' d := by
  refine ⟨h.actReadyW hW.1, h.scBack hW.2.1, fun u hu => hW.2.2 u ?_⟩
  rcases h.2.2 with e | e
  · rw [← e]; exact hu
  · rw [e] at hu; cases hu

/-- **A TCB losing its SC keeps `WakeOK`.** -/
theorem wake_drop {σ : State Unit} {d t : ObjRef} (hW : WakeOK σ d) {x x' : Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hx' : x'.tcbSchedContext = none) :
    WakeOK (updK σ t (.tcb x')) d := by
  have hkp : ∀ p, p ≠ t → (updK σ t (.tcb x')).kheap p = σ.kheap p := fun p hp => by
    simp only [updK, Function.update_of_ne hp]
  have hkt : (updK σ t (.tcb x')).kheap t = some (.tcb x') := by simp [updK]
  refine ⟨fun u hu x0 scp y n hk0 hsc hky hact => ?_, fun u x0 p hk0 hp => ?_, fun u hu => hW.2.2 u hu⟩
  · have hut : u ≠ t := by rintro rfl; rw [hkt] at hk0; cases hk0; rw [hx'] at hsc; cases hsc
    have hst : scp ≠ t := by rintro rfl; rw [hkt] at hky; cases hky
    rw [hkp u hut] at hk0; rw [hkp scp hst] at hky
    exact hW.1 u hu x0 scp y n hk0 hsc hky hact
  · have hut : u ≠ t := by rintro rfl; rw [hkt] at hk0; cases hk0; rw [hx'] at hp; cases hp
    rw [hkp u hut] at hk0
    obtain ⟨y, n, hky, hyt⟩ := hW.2.1 u x0 p hk0 hp
    have hpt : p ≠ t := by rintro rfl; rw [hk] at hky; cases hky
    exact ⟨y, n, by rw [hkp p hpt]; exact hky, hyt⟩

/-- **An SC bound by no TCB getting a new thread keeps `WakeOK`.** -/
theorem wake_scTcb {σ : State Unit} {d c : ObjRef} (hW : WakeOK σ d) {y y' : SchedContext} {n : Nat}
    (hk : σ.kheap c = some (.schedContext y n))
    (hno : ∀ u xu, σ.kheap u = some (.tcb xu) → xu.tcbSchedContext ≠ some c)
    (hr : y'.scRefills = y.scRefills) (hm : y'.scRefillMax = y.scRefillMax) :
    WakeOK (updK σ c (.schedContext y' n)) d := by
  have hkp : ∀ p, p ≠ c → (updK σ c (.schedContext y' n)).kheap p = σ.kheap p := fun p hp => by
    simp only [updK, Function.update_of_ne hp]
  have hkc : (updK σ c (.schedContext y' n)).kheap c = some (.schedContext y' n) := by simp [updK]
  refine ⟨fun u hu x0 scp z m hk0 hsc hkz hact => ?_, fun u x0 p hk0 hp => ?_, fun u hu => hW.2.2 u hu⟩
  · have huc : u ≠ c := by rintro rfl; rw [hkc] at hk0; cases hk0
    rw [hkp u huc] at hk0
    have hsc' : scp ≠ c := fun e => hno u x0 hk0 (e ▸ hsc)
    rw [hkp scp hsc'] at hkz
    exact hW.1 u hu x0 scp z m hk0 hsc hkz hact
  · have huc : u ≠ c := by rintro rfl; rw [hkc] at hk0; cases hk0
    rw [hkp u huc] at hk0
    have hpc : p ≠ c := fun e => hno u x0 hk0 (e ▸ hp)
    obtain ⟨z, m, hkz, hzt⟩ := hW.2.1 u x0 p hk0 hp
    exact ⟨z, m, by rw [hkp p hpc]; exact hkz, hzt⟩

/-- **`d` bound to an SC whose thread is `d` keeps `WakeOK`.** -/
theorem wake_bind {σ : State Unit} {d c : ObjRef} (hW : WakeOK σ d) {x x' : Tcb} {y : SchedContext} {n : Nat}
    (hkd : σ.kheap d = some (.tcb x)) (hkc : σ.kheap c = some (.schedContext y n)) (hyt : y.scTcb = some d)
    (hx' : x'.tcbSchedContext = some c) : WakeOK (updK σ d (.tcb x')) d := by
  have hkp : ∀ p, p ≠ d → (updK σ d (.tcb x')).kheap p = σ.kheap p := fun p hp => by
    simp only [updK, Function.update_of_ne hp]
  have hkd' : (updK σ d (.tcb x')).kheap d = some (.tcb x') := by simp [updK]
  have hcd : c ≠ d := by rintro rfl; rw [hkd] at hkc; cases hkc
  refine ⟨fun u hu x0 scp z m hk0 hsc hkz hact => ?_, fun u x0 p hk0 hp => ?_, fun u hu => hW.2.2 u hu⟩
  · have hud : u ≠ d := hW.2.2 u hu
    rw [hkp u hud] at hk0
    have hsd : scp ≠ d := by rintro rfl; rw [hkd'] at hkz; cases hkz
    rw [hkp scp hsd] at hkz
    exact hW.1 u hu x0 scp z m hk0 hsc hkz hact
  · by_cases hud : u = d
    · subst hud
      rw [hkd'] at hk0; cases hk0
      rw [hx'] at hp; cases hp
      exact ⟨y, n, by rw [hkp _ hcd]; exact hkc, hyt⟩
    · rw [hkp u hud] at hk0
      obtain ⟨z, m, hkz, hzt⟩ := hW.2.1 u x0 p hk0 hp
      have hpd : p ≠ d := by rintro rfl; rw [hkd] at hkz; cases hkz
      exact ⟨z, m, by rw [hkp p hpd]; exact hkz, hzt⟩

theorem sv_rescheduleRequired' : SVM (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; sv_auto

theorem sv_testReschedule' (t : ObjRef) : SVM (testReschedule (Z := Unit) t) := by
  unfold testReschedule; sv_auto
  exact sv_rescheduleRequired'

theorem sv_bindScReply' (c r : ObjRef) : SVM (bindScReply (Z := Unit) c r) := by
  unfold bindScReply; sv_auto

/-- An `SVS` step keeps a TCB's SC and an SC's thread. -/
theorem SVS.tcbSc {σ σ' : State Unit} (h : SVS σ σ') {u : ObjRef} {x : Tcb} (hk : σ.kheap u = some (.tcb x)) :
    ∃ x', σ'.kheap u = some (.tcb x') ∧ x'.tcbSchedContext = x.tcbSchedContext := by
  have e := h.1 u; rw [hk] at e
  exact sv_tcb e

theorem SVS.scOf {σ σ' : State Unit} (h : SVS σ σ') {c : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap c = some (.schedContext y n)) :
    ∃ y', σ'.kheap c = some (.schedContext y' n) ∧ y'.scRefills = y.scRefills ∧
      y'.scRefillMax = y.scRefillMax ∧ y'.scTcb = y.scTcb := by
  have e := h.1 c; rw [hk] at e
  exact sv_sc e

theorem wd_getTcb_mem {σ : State Unit} {p : ObjRef} {y : Tcb × State Unit}
    (hy : y ∈ (NonDet.getsThe (getTcb (Z := Unit) p) σ).1) : σ.kheap p = some (.tcb y.1) ∧ y.2 = σ := by
  unfold NonDet.getsThe getTcb readObject at hy
  cases h : σ.kheap p with
  | none => rw [h] at hy; exact hy.elim
  | some k =>
    rw [h] at hy
    cases k <;> simp only [NonDet.assertOpt] at hy
    all_goals first | exact hy.elim | skip
    rw [Set.mem_singleton_iff.1 hy]; exact ⟨rfl, rfl⟩

theorem wd_setObject_mem {σ : State Unit} {p : ObjRef} {o : KernelObject} {x : Unit × State Unit}
    (hx : x ∈ (setObject (Z := Unit) p o σ).1) :
    x.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk⟩ : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap p with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  obtain ⟨-, rfl⟩ := hk
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]

/-- An outcome of `thread_set`: the object a TCB, updated. -/
theorem threadSet_mem {σ : State Unit} {f : Tcb → Tcb} {t : ObjRef} {x : Unit × State Unit}
    (hx : x ∈ (threadSet (Z := Unit) f t σ).1) : ∃ xt, σ.kheap t = some (.tcb xt) ∧ x.2 = updK σ t (.tcb (f xt)) := by
  unfold threadSet at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨hk, hs⟩ := wd_getTcb_mem hy
  rw [hs] at hx
  exact ⟨y.1, hk, wd_setObject_mem hx⟩

/-- An outcome of `get_sc_obj_ref`: the object an SC, the state kept. -/
theorem getScObjRef_mem {σ : State Unit} {g : SchedContext → Option ObjRef} {c : ObjRef}
    {y : Option ObjRef × State Unit} (hy : y ∈ (getScObjRef (Z := Unit) g c σ).1) :
    ∃ yc n, σ.kheap c = some (.schedContext yc n) ∧ y = (g yc, σ) := by
  unfold getScObjRef getSchedContext at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨w, hw, hz⟩ := hz
  obtain ⟨k, hk, rfl⟩ : ∃ k, σ.kheap c = some k ∧ w = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hw
    cases h : σ.kheap c with
    | none => rw [h] at hw; exact hw.elim
    | some k => rw [h] at hw; exact ⟨k, rfl, Set.mem_singleton_iff.1 hw⟩
  cases k with
  | schedContext yc n =>
    refine ⟨yc, n, hk, ?_⟩
    rw [Set.mem_singleton_iff.1 hz] at hy
    exact Set.mem_singleton_iff.1 hy
  | _ => exact hz.elim

/-- **`sched_context_donate c d` keeps `WakeOK`.** -/
theorem donate_wake {σ σ' : State Unit} {c d : ObjRef} (hW : WakeOK σ d)
    (hm : ((), σ') ∈ (schedContextDonate (Z := Unit) c d σ).1) : WakeOK σ' d := by
  unfold schedContextDonate at hm
  obtain ⟨y1, hy1, hm⟩ := hm
  obtain ⟨yc, n, hkc, rfl⟩ := getScObjRef_mem hy1
  obtain ⟨y2, hy2, hm⟩ := hm
  -- the old holder's unbind: `WakeOK`, `c` an SC bound by no TCB
  have hmid : WakeOK y2.2 d ∧ ∃ yc', y2.2.kheap c = some (.schedContext yc' n) ∧
      yc'.scRefills = yc.scRefills ∧ yc'.scRefillMax = yc.scRefillMax ∧
      ∀ u xu, y2.2.kheap u = some (.tcb xu) → xu.tcbSchedContext ≠ some c := by
    cases hyt : yc.scTcb with
    | none =>
      rw [hyt] at hy2
      simp only [NonDet.when, ne_eq, not_true_eq_false, ↓reduceIte] at hy2
      rw [Set.mem_singleton_iff.1 hy2]
      refine ⟨hW, yc, hkc, rfl, rfl, fun u xu hku hus => ?_⟩
      obtain ⟨z, m, hkz, hzt⟩ := hW.2.1 u xu c hku hus
      rw [hkc] at hkz; cases hkz; rw [hyt] at hzt; cases hzt
    | some f =>
      rw [hyt] at hy2
      simp only [NonDet.when, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte] at hy2
      obtain ⟨z1, hz1, hy2⟩ := hy2
      rw [Set.mem_singleton_iff.1 hz1] at hy2
      obtain ⟨z2, hz2, hy2⟩ := hy2
      have h2 := sv_tcbSchedAction' _ _ σ z2 hz2
      obtain ⟨z3, hz3, hy2⟩ := hy2
      have h3 := sv_tcbReleaseRemove' _ z2.2 z3 hz3
      have h23 := h2.trans h3
      obtain ⟨z4, hz4, hy2⟩ := hy2
      obtain ⟨x3, hkt3, e4⟩ := threadSet_mem hz4
      rw [e4] at hy2
      have h5 := sv_testReschedule' f _ y2 hy2
      have hW4 : WakeOK (updK z3.2 f (.tcb (tcbSchedContextUpdate (fun _ => none) x3))) d :=
        wake_drop (h23.wakeOK' hW) hkt3 rfl
      have hW5 := h5.wakeOK' hW4
      have hfc : c ≠ f := by rintro rfl; obtain ⟨y', hy', -⟩ := h23.scOf hkc; rw [hkt3] at hy'; cases hy'
      obtain ⟨yc3, hkc3, hr3, hm3, ht3⟩ := h23.scOf hkc
      have hkc4 : (updK z3.2 f (.tcb (tcbSchedContextUpdate (fun _ => none) x3))).kheap c =
          some (.schedContext yc3 n) := by
        simp only [updK, Function.update_of_ne hfc]; exact hkc3
      obtain ⟨yc5, hkc5, hr5, hm5, ht5⟩ := h5.scOf hkc4
      have hkt4 : (updK z3.2 f (.tcb (tcbSchedContextUpdate (fun _ => none) x3))).kheap f =
          some (.tcb (tcbSchedContextUpdate (fun _ => none) x3)) := by simp [updK]
      obtain ⟨xt5, hkt5, hxt5⟩ := h5.tcbSc hkt4
      refine ⟨hW5, yc5, hkc5, hr5.trans hr3, hm5.trans hm3, fun u xu hku hus => ?_⟩
      by_cases hut : u = f
      · subst hut; rw [hkt5] at hku; cases hku; rw [hxt5] at hus; cases hus
      · obtain ⟨z, m, hkz, hzt⟩ := hW5.2.1 u xu c hku hus
        rw [hkc5] at hkz; cases hkz
        rw [ht5, ht3, hyt] at hzt; cases hzt; exact hut rfl
  obtain ⟨hW5, yc5, hkc5, -, -, hno⟩ := hmid
  -- the two binds
  obtain ⟨w1, hw1, hm⟩ := hm
  obtain ⟨y0, n0, hk0, e1⟩ := updSc_mem hw1
  rw [hkc5] at hk0; cases hk0
  have hW6 : WakeOK (updK y2.2 c (.schedContext (scTcbUpdate (fun _ => some d) yc5) n)) d :=
    wake_scTcb hW5 hkc5 hno rfl rfl
  have hw1' : w1.2 = updK y2.2 c (.schedContext (scTcbUpdate (fun _ => some d) yc5) n) := e1
  rw [hw1'] at hm
  obtain ⟨xd6, hkd6, e2⟩ := threadSet_mem hm
  rw [show σ' = _ from e2]
  have hkc6 : (updK y2.2 c (.schedContext (scTcbUpdate (fun _ => some d) yc5) n)).kheap c =
      some (.schedContext (scTcbUpdate (fun _ => some d) yc5) n) := by simp [updK]
  exact wake_bind hW6 hkd6 hkc6 rfl rfl

/-- **`reply_push t d r don` keeps `WakeOK`** (`t`, `d` TCBs). -/
theorem replyPush_wake {σ σ' : State Unit} {t d r : ObjRef} {don : Bool} (hW : WakeOK σ d) {xt xd : Tcb}
    (hkt : σ.kheap t = some (.tcb xt)) (hkd : σ.kheap d = some (.tcb xd))
    (hm : ((), σ') ∈ (replyPush (Z := Unit) t d r don σ).1) : WakeOK σ' d := by
  unfold replyPush at hm
  rw [nd_bind_one (show getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t σ = _ from threadGet_eq _ hkt),
    nd_bind_one (show getTcbObjRef (Z := Unit) Tcb.tcbSchedContext d σ = _ from threadGet_eq _ hkd)] at hm
  obtain ⟨z1, hz1, hm⟩ := hm
  have h1 := sv_updateSkObjRef' KernelObject.reply _ r _ (fun _ => so_reply _) σ z1 hz1
  obtain ⟨z2, hz2, hm⟩ := hm
  have h2 := sv_setThreadState' t _ z1.2 z2 hz2
  have h12 := h1.trans h2
  have hW2 := h12.wakeOK' hW
  unfold NonDet.when at hm
  split_ifs at hm with hc
  · obtain ⟨hcs, -, -⟩ := hc
    obtain ⟨c, hcc⟩ := Option.ne_none_iff_exists'.1 hcs
    rw [hcc] at hm
    obtain ⟨z3, hz3, hm⟩ := hm
    have h3 := sv_bindScReply' c r z2.2 z3 hz3
    exact donate_wake (h3.wakeOK' hW2) hm
  · rw [(Prod.mk.inj (Set.mem_singleton_iff.1 hm)).2]; exact hW2

/-- **The woken thread's sporadic check keeps `WakeOK`** (`unblock_wake`, the
action kept). -/
theorem unblock_wakeOK {σ σ1 : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (a b : Option Bool) (hW : WakeOK σ t)
    (hu : ((), σ1) ∈ ((getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= fun o =>
      ifCondRefillUnblockCheck (Z := Unit) o a b) σ).1) : WakeOK σ1 t := by
  have h1 := unblock_wake hk a b hW hu
  refine ⟨h1.1, h1.2, fun u hu' => hW.2.2 u ?_⟩
  obtain ⟨y0, hy0, hx⟩ := hu
  have hy : y0 = (x.tcbSchedContext, σ) := by
    unfold getTcbObjRef threadGet at hy0
    obtain ⟨z, hz, hz2⟩ := hy0
    unfold NonDet.getsThe getTcb readObject at hz
    rw [hk] at hz
    rw [Set.mem_singleton_iff.1 hz] at hz2
    exact Set.mem_singleton_iff.1 hz2
  subst hy
  cases hsc : x.tcbSchedContext with
  | none =>
    rw [hsc] at hx
    have : σ1 = σ := by
      unfold ifCondRefillUnblockCheck at hx; simp only [NonDet.maybeM] at hx
      exact (Prod.mk.inj (Set.mem_singleton_iff.1 hx)).2
    rw [← this]; exact hu'
  | some p =>
    rw [hsc] at hx
    rw [← (os_ifCond p a b σ ((), σ1) hx).2.2.2]; exact hu'

/-- Every outcome of `m` keeps `WakeOK σ d`. -/
def WK (d : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → WakeOK σ d → WakeOK x.2 d

theorem wk_bind {d : ObjRef} {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : WK d m) (hg : ∀ a, WK d (g a)) : WK d (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩ hW
  exact hg y.1 y.2 x hx (hm σ y hy hW)

theorem wk_svm {d : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h : SVM m) : WK d m :=
  fun σ x hx hW => (h σ x hx).wakeOK' hW

theorem wk_when {d : ObjRef} (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : WK d m) :
    WK d (NonDet.when P m) := by
  unfold NonDet.when; split
  · exact h
  · exact wk_svm (sv_pure _)

theorem wk_donate {d : ObjRef} (c : ObjRef) : WK d (schedContextDonate (Z := Unit) c d) := by
  intro σ x hx hW
  obtain ⟨⟨⟩, σ'⟩ := x
  exact donate_wake hW hx

/-- **`reply_remove` of the reply's caller `d` keeps `WakeOK σ d`** (the SC
donated back to `d`). -/
theorem wk_replyRemove (d r : ObjRef) : WK d (replyRemove (Z := Unit) d r) := by
  unfold replyRemove
  dsimp only
  repeat' (first
    | exact wk_donate _
    | exact wk_svm (sv_replyUnlinkTcb _ _)
    | exact wk_svm (sv_replyUnlinkSc' _ _)
    | exact wk_svm (sv_getSimpleKo' _ _)
    | exact wk_svm (sv_getTcbObjRef' _ _)
    | (refine wk_bind ?_ (fun _ => ?_))
    | (apply wk_when)
    | split
    | (apply wk_svm; sv_auto; done)
    | (dsimp only))

/-! ## No switch pending (`NoSwitch`), kept by the reply path -/

/-- No switch target pending (l4v `scheduler_action ≠ switch_thread`; at a
system call's entry the action is `resume_cur_thread`). -/
def NoSwitch (σ : State Unit) : Prop := ∀ u, σ.schedulerAction ≠ .switchThread u

/-- With no switch pending, `TailOK` is `SCBack`. -/
theorem tailOK_of_ns {σ : State Unit} (h : NoSwitch σ) (hB : SCBack σ) : TailOK σ :=
  ⟨fun u hu => absurd hu (h u), hB, fun u hu => absurd hu (h u)⟩

/-- Every outcome of `m` keeps the action or makes it `choose_new_thread`. -/
def AM {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → x.2.schedulerAction = σ.schedulerAction ∨ x.2.schedulerAction = .chooseNewThread

theorem AM.noSwitch {α : Type} {m : NonDet (State Unit) α} (h : AM m) {σ : State Unit} {x : α × State Unit}
    (hx : x ∈ (m σ).1) (hN : NoSwitch σ) : NoSwitch x.2 := by
  intro u hu
  rcases h σ x hx with e | e
  · exact hN u (e ▸ hu)
  · rw [e] at hu; cases hu

theorem am_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : AM m) (hg : ∀ a, AM (g a)) : AM (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  rcases hg y.1 y.2 x hx with e | e
  · rw [e]; exact hm σ y hy
  · exact Or.inr e

theorem am_svm {α : Type} {m : NonDet (State Unit) α} (h : SVM m) : AM m := fun σ x hx => (h σ x hx).2.2

theorem am_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : AM m) : AM (NonDet.when P m) := by
  unfold NonDet.when; split
  · exact h
  · exact am_svm (sv_pure _)

theorem am_threadSet (f : Tcb → Tcb) (t : ObjRef) : AM (threadSet (Z := Unit) f t) := by
  intro σ x hx
  obtain ⟨xt, -, e⟩ := threadSet_mem hx
  rw [e]; exact Or.inl rfl

theorem am_updSc (q : ObjRef) (f : SchedContext → SchedContext) : AM (updateSchedContext (Z := Unit) q f) := by
  intro σ x hx
  obtain ⟨y0, n0, -, e⟩ := updSc_mem hx
  rw [e]; exact Or.inl rfl

theorem am_donate (c d : ObjRef) : AM (schedContextDonate (Z := Unit) c d) := by
  unfold schedContextDonate
  repeat' (first
    | exact am_threadSet _ _
    | exact am_updSc _ _
    | exact am_svm (sv_testReschedule' _)
    | exact am_svm (sv_tcbReleaseRemove' _)
    | exact am_svm (sv_tcbSchedAction' _ _)
    | (refine am_bind ?_ (fun _ => ?_))
    | (apply am_when)
    | split
    | (apply am_svm; sv_auto; done)
    | (dsimp only))

theorem am_replyRemove (d r : ObjRef) : AM (replyRemove (Z := Unit) d r) := by
  unfold replyRemove
  dsimp only
  repeat' (first
    | exact am_donate _ _
    | exact am_svm (sv_replyUnlinkTcb _ _)
    | exact am_svm (sv_replyUnlinkSc' _ _)
    | exact am_svm (sv_getSimpleKo' _ _)
    | exact am_svm (sv_getTcbObjRef' _ _)
    | (refine am_bind ?_ (fun _ => ?_))
    | (apply am_when)
    | split
    | (apply am_svm; sv_auto; done)
    | (dsimp only))

/-- The sporadic check keeps the action (`os_ifCond`). -/
theorem unblock_act {σ σ1 : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (a b : Option Bool)
    (hu : ((), σ1) ∈ ((getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= fun o =>
      ifCondRefillUnblockCheck (Z := Unit) o a b) σ).1) : σ1.schedulerAction = σ.schedulerAction := by
  obtain ⟨y0, hy0, hx⟩ := hu
  have hy : y0 = (x.tcbSchedContext, σ) := by
    unfold getTcbObjRef threadGet at hy0
    obtain ⟨z, hz, hz2⟩ := hy0
    unfold NonDet.getsThe getTcb readObject at hz
    rw [hk] at hz
    rw [Set.mem_singleton_iff.1 hz] at hz2
    exact Set.mem_singleton_iff.1 hz2
  subst hy
  cases hsc : x.tcbSchedContext with
  | none =>
    rw [hsc] at hx
    have : σ1 = σ := by
      unfold ifCondRefillUnblockCheck at hx; simp only [NonDet.maybeM] at hx
      exact (Prod.mk.inj (Set.mem_singleton_iff.1 hx)).2
    rw [this]
  | some p =>
    rw [hsc] at hx
    exact (os_ifCond p a b σ ((), σ1) hx).2.2.2

theorem noSwitch_sts {σ : State Unit} (h : NoSwitch σ) (t : ObjRef) (o : KernelObject) :
    NoSwitch (stsAct (updK σ t o) t) := by
  intro u hu
  rcases (svs_stsAct (updK σ t o) t).2.2 with e | e
  · exact h u (e ▸ hu)
  · rw [e] at hu; cases hu

end

end Fl4Proofs.P3.SVK
