/-
P3 (line mmuAD, gen 41): **the spec's success tail after the restart** (spec only) — what `fl4HandleInvocationVF`
does after a VCPU invocation that replied in FL4's decode: from the restart state `zcR c σ'` (P3/JAtZV3HiComm) the
spec reads `Restart`, replies `(0, ms)` when called and sets `Running`; that is the state FL4's in-decode reply
reaches from `σ'` directly (`replyState` / `replyTcbB` of P3/XTopReply, then `Running`).

* `zc_sched_tcb`: the schedulability of `c` reads `c`'s runnability and SC, the SC objects and the release queue.
* `zc_specTail_false`: `specTail false` of a `Restart` thread is `setThreadState .running`.
* `zc_stsAct_act`: `stsAct` over a state that differs from `T` only in the scheduler action `zcR` may have set is
  `stsAct T` (case on whether the restart's act fired; both sides read the same schedulability).
* **`zc_tail`**: `specTail call c ms (zcR c σ') = {((), stsAct (updK (if call then replyState σ' c x ms else σ') c
  (.tcb {(if call then replyTcbB x … ms else x) with tcbState := .running})) c)}` for a `Running` current thread `c`.

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3HiComm
open Classical

namespace Fl4Proofs.P3
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

section
variable {c : ObjRef}

theorem zc_sched_tcb {τ A : State Unit} {y y' : Tcb} (h1 : τ.kheap c = some (.tcb y)) (h1' : A.kheap c = some (.tcb y'))
    (hr : runnable y.tcbState = runnable y'.tcbState) (hs : y.tcbSchedContext = y'.tcbSchedContext)
    (h2 : scsOf τ = scsOf A) (h3 : τ.releaseQueue = A.releaseQueue) : schedulable c τ = schedulable c A := by
  unfold schedulable
  apply decide_eq_decide.2
  rw [h2, h3]
  simp only [optPred, optMapSome, optMap, tcbsOfKh, h1, h1', tcbOf, hr, hs]

theorem zc_specTail_false {τ : State Unit} {y : Tcb} (hk : τ.kheap c = some (.tcb y)) (hrs : y.tcbState = .restart)
    (ms : List Data) :
    specTail false c ms τ = ({((), Notif.stsAct (Notif.updK τ c (.tcb { y with tcbState := .running })) c)}, False) := by
  unfold specTail
  rw [Notif.nd_bind_one (Notif.getThreadState_eq hk)]
  simp only [hrs]
  rw [Endp.nd_when_false (by simp), Notif.nd_pure_bind']
  exact Notif.setThreadState_eq .running hk

theorem zc_rec_eta (T : State Unit) : { T with schedulerAction := T.schedulerAction } = T := rfl

/-- `stsAct` past the restart's scheduler action (module docstring). -/
theorem zc_stsAct_act {σ T : State Unit} {x : Tcb} (hk : σ.kheap c = some (.tcb x))
    (hcur : T.curThread = σ.curThread) (hact : T.schedulerAction = σ.schedulerAction)
    (hsch : schedulable c T = schedulable c (Notif.updK σ c (.tcb { x with tcbState := .restart }))) :
    Notif.stsAct { T with schedulerAction := (zcR c σ).schedulerAction } c = Notif.stsAct T c := by
  rw [zcR_of hk]
  unfold Notif.stsAct
  by_cases C0 : c = (Notif.updK σ c (.tcb { x with tcbState := .restart })).curThread ∧
      (Notif.updK σ c (.tcb { x with tcbState := .restart })).schedulerAction = .resumeCurThread ∧
      ¬schedulable c (Notif.updK σ c (.tcb { x with tcbState := .restart })) = true
  · rw [if_pos C0]
    have C2 : c = T.curThread ∧ T.schedulerAction = .resumeCurThread ∧ ¬schedulable c T = true := by
      rw [hcur, hact, hsch]; exact C0
    have C1 : ¬ (c = ({ T with schedulerAction := SchedulerAction.chooseNewThread } : State Unit).curThread ∧
        ({ T with schedulerAction := SchedulerAction.chooseNewThread } : State Unit).schedulerAction =
          .resumeCurThread ∧
        ¬schedulable c { T with schedulerAction := SchedulerAction.chooseNewThread } = true) := fun h => by
      have := h.2.1; cases this
    rw [if_neg C1, if_pos C2]
  · rw [if_neg C0]
    have e : (Notif.updK σ c (.tcb { x with tcbState := .restart })).schedulerAction = T.schedulerAction := by
      rw [hact]; rfl
    rw [e]

theorem zc_replyStateB_fields (σ : State Unit) (t : ObjRef) (x : Tcb) (buf : Option ObjRef) (ms : List Data) :
    (replyStateB σ t x buf ms).curThread = σ.curThread ∧ (replyStateB σ t x buf ms).schedulerAction = σ.schedulerAction ∧
      (replyStateB σ t x buf ms).releaseQueue = σ.releaseQueue := by
  cases buf <;> exact ⟨rfl, rfl, rfl⟩

theorem zc_replyStateB_R {σ : State Unit} {x : Tcb} (hk : σ.kheap c = some (.tcb x)) (buf : Option ObjRef)
    (ms : List Data) (Y : Tcb) :
    Notif.updK (replyStateB (zcR c σ) c { x with tcbState := .restart } buf ms) c (.tcb Y) =
      { Notif.updK (replyStateB σ c x buf ms) c (.tcb Y) with schedulerAction := (zcR c σ).schedulerAction } := by
  have hR := zcR_rec (c := c) hk
  generalize (zcR c σ).schedulerAction = a at hR ⊢
  rw [hR]
  cases σ
  cases buf <;> simp only [replyStateB, MrS, Endp.mrState, Endp.mrStateN, Endp.setUm, Notif.updK,
    Function.update_idem] <;> rfl

theorem zc_scs_tcb {σ T : State Unit} (hT : ∀ q, q ≠ c → T.kheap q = σ.kheap q) {y : Tcb}
    (hy : T.kheap c = some (.tcb y)) {x' : Tcb} :
    scsOf T = scsOf (Notif.updK σ c (.tcb x')) := by
  funext q
  by_cases e : q = c
  · subst e
    simp only [scsOfKh, optMap, Notif.updK_kheap, Function.update_self, hy, scOf]
  · simp only [scsOfKh, optMap, Notif.updK_kheap, Function.update_of_ne e, hT q e]

/-- **The spec's success tail after the restart** (module docstring). -/
theorem zc_tail {σ : State Unit} {x : Tcb} (hk : σ.kheap c = some (.tcb x)) (hrs : x.tcbState = .running)
    (hcur : σ.curThread = c) (call : Bool) (ms : List Data) (hlen : ms.length ≤ msgMaxLength)
    (hfr : ∀ p, Endp.ipcBufOf true x = some p → ∀ z ∈ Endp.mrPairs ms,
      (Endp.bufAddr p z.1).toNat % 8 = 0 ∧ inUserFrame (Endp.bufAddr p z.1) σ) :
    specTail call c ms (zcR c σ) = ({((), Notif.stsAct (Notif.updK (if call then replyState σ c x ms else σ) c
      (.tcb { (if call then replyTcbB x (Endp.ipcBufOf true x) ms else x) with tcbState := .running })) c)}, False) := by
  have hD : zcDom c σ := ⟨hcur, x, hk, by rw [hrs]; exact fun h => by cases h⟩
  have hk' : (zcR c σ).kheap c = some (.tcb { x with tcbState := .restart }) := by
    rw [zcR_kheap hk, Function.update_self]
  cases call
  · rw [zc_specTail_false hk' rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have e1 : Notif.updK (zcR c σ) c (.tcb { { x with tcbState := .restart } with tcbState := .running }) =
        { Notif.updK σ c (.tcb { x with tcbState := .running }) with
          schedulerAction := (zcR c σ).schedulerAction } := by
      have hR := zcR_rec (c := c) hk
      generalize (zcR c σ).schedulerAction = a at hR ⊢
      rw [hR]
      simp only [Notif.updK, Function.update_idem]
    rw [e1, zc_stsAct_act (T := Notif.updK σ c (.tcb { x with tcbState := .running })) hk rfl rfl
      (zc_sched_tcb (y := { x with tcbState := .running }) (y' := { x with tcbState := .restart })
        (by rw [Notif.updK_kheap, Function.update_self]) (by rw [Notif.updK_kheap, Function.update_self]) rfl rfl
        (zc_scs_tcb (fun q hq => by rw [Notif.updK_kheap, Function.update_of_ne hq])
          (by rw [Notif.updK_kheap, Function.update_self])) rfl)]
  · have hfr' : ∀ p, Endp.ipcBufOf true { x with tcbState := .restart } = some p → ∀ z ∈ Endp.mrPairs ms,
        (Endp.bufAddr p z.1).toNat % 8 = 0 ∧ inUserFrame (Endp.bufAddr p z.1) (zcR c σ) := fun p hp z hz =>
      ⟨(hfr p hp z hz).1, (zc_inUserFrame hD _).2 (hfr p hp z hz).2⟩
    rw [specTail_data hk' rfl ms hlen hfr']
    simp only [↓reduceIte]
    have e1 := zc_replyStateB_R hk (Endp.ipcBufOf true x) ms
      { replyTcbB x (Endp.ipcBufOf true x) ms with tcbState := .running }
    have ey : ({ replyTcbB { x with tcbState := .restart } (Endp.ipcBufOf true { x with tcbState := .restart }) ms with
        tcbState := .running } : Tcb) = { replyTcbB x (Endp.ipcBufOf true x) ms with tcbState := .running } := rfl
    have eb : Endp.ipcBufOf true { x with tcbState := .restart } = Endp.ipcBufOf true x := rfl
    unfold replyState
    rw [ey, eb, e1]
    obtain ⟨f1, f2, f3⟩ := zc_replyStateB_fields σ c x (Endp.ipcBufOf true x) ms
    rw [zc_stsAct_act (T := Notif.updK (replyStateB σ c x (Endp.ipcBufOf true x) ms) c
        (.tcb { replyTcbB x (Endp.ipcBufOf true x) ms with tcbState := .running })) hk f1 f2
      (zc_sched_tcb (y := { replyTcbB x (Endp.ipcBufOf true x) ms with tcbState := .running })
        (y' := { x with tcbState := .restart }) (by rw [Notif.updK_kheap, Function.update_self])
        (by rw [Notif.updK_kheap, Function.update_self]) rfl rfl
        (zc_scs_tcb (fun q hq => by rw [Notif.updK_kheap, Function.update_of_ne hq, replyStateB_kheap_ne _ _ _ _ _ hq])
          (by rw [Notif.updK_kheap, Function.update_self])) f3)]

end

end

end Fl4Proofs.P3
