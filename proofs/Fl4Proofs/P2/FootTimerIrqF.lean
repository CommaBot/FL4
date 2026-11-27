/-
# P2: the timer interrupt's `fire_ok` on the guarded store

`fire_ok.guard`: `localtimer.fire_ok` (`localtimer.rs`) on any store `gS` answering `R` reads as `st`
(`PathObl.GRd`) is the real one when `R` holds the words it reads: the due thread `p.tm`'s right and parent links,
the left links of the walk to its successor (`fire_ok_loop`, any predicate `P` closed under the real left links), the
successor's deadline, and for the tail (`fireTail`, inlined three times by the extraction, `fire_ok_eq`) the
notification's state, bound thread and head, `p.tm`'s state and what `wake_ok` reads (`WakeRd`).

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read bind_guard_congr)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R]

/-- The tail of `fire_ok`: the bound notification's signal is one the local path may send. -/
def fireTail (M : machine.Store S) (s : S) (cpu : U64) (ct : obj.Tcb) (p : localtimer.TimerIrqPlan) :
    Result Bool :=
  if p.ntfn = 0#u64
  then ok true
  else do
    let st ← obj.Ntfn.state M p.ntfn s
    if st = obj.NTFN_ACTIVE
    then ok true
    else
      if st = obj.NTFN_IDLE
      then do
        let b2 ← obj.Ntfn.bound_tcb M p.ntfn s
        if b2 = 0#u64
        then ok true
        else
          if b2 != p.tm
          then ok false
          else do
            let bs ← obj.Tcb.state M p.tm s
            if bs = sched.TS_RUNNING_VM
            then ok false
            else
              if bs = sched.TS_BLOCKED_ON_RECV
              then
                if p.waiter = p.tm
                then
                  if p.ep != 0#u64
                  then localtimer.wake_ok M s cpu ct p.tm p.ntfn
                  else ok false
                else ok false
              else ok true
      else
        if st = obj.NTFN_WAITING
        then do
          let i3 ← obj.Ntfn.head M p.ntfn s
          localtimer.wake_ok M s cpu ct i3 p.ntfn
        else ok false

theorem fire_ok_eq (M : machine.Store S) (s : S) (cpu : U64) (ct : obj.Tcb) (p : localtimer.TimerIrqPlan)
    (now : U64) :
    localtimer.fire_ok M s cpu ct p now =
      (if p.tm = 0#u64
      then ok false
      else do
        let i ← obj.Tcb.timer_right M p.tm s
        let i1 ← obj.Tcb.timer_parent M p.tm s
        let b ← obj.Tcb.is_null i
        if b
        then do
          let b1 ← obj.Tcb.is_null i1
          if b1
          then fireTail M s cpu ct p
          else do
            let i2 ← obj.Tcb.timer_deadline M i1 s
            if i2 <= now then ok false else fireTail M s cpu ct p
        else do
          let i2 ← localtimer.fire_ok_loop M s i layout.TREE_FUEL
          let b1 ← obj.Tcb.is_null i2
          if b1
          then fireTail M s cpu ct p
          else do
            let i3 ← obj.Tcb.timer_deadline M i2 s
            if i3 <= now then ok false else fireTail M s cpu ct p) := by
  unfold localtimer.fire_ok fireTail
  rfl

/-- What `wake_ok s cpu ct w n` reads. -/
structure WakeRd (st : machine.Store S) [L : LawfulStore st] (R : U64 → Prop) (s : S) (w n : U64) : Prop where
  may : MayRd (L := L) R s w
  dom : R (domA w)
  inq : R (inqA w)
  nsc : R (ntfnScA n)
  top : TopRd st R s

theorem WakeRd.guard {s : S} {w n : U64} (h : WakeRd st R s w n) (ct : obj.Tcb) :
    localtimer.wake_ok gS s (L.cpu s) ct w n = localtimer.wake_ok st s (L.cpu s) ct w n :=
  wake_ok.guard h.may h.dom h.inq h.nsc h.top

theorem ntfn_state_guard (n : obj.Ntfn) (s : S) (h : R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE)) :
    obj.Ntfn.state gS n s = obj.Ntfn.state st n s := by
  unfold obj.Ntfn.state
  rw [PathObl.obj.Ntfn.tail_state.guard (gS := gS) n s h]

theorem fireTail.guard {s : S} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan}
    (h1 : R (core.num.U64.wrapping_add p.ntfn layout.ntfn.TAIL_STATE))
    (h2 : R (core.num.U64.wrapping_add p.ntfn layout.ntfn.BOUND_TCB))
    (h3 : R (core.num.U64.wrapping_add p.tm layout.tcb.STATE)) (hw1 : WakeRd st R s p.tm p.ntfn)
    (h4 : R (core.num.U64.wrapping_add p.ntfn layout.ntfn.HEAD))
    (hw2 : ∀ w, obj.Ntfn.head st p.ntfn s = ok w → WakeRd st R s w p.ntfn) :
    fireTail gS s (L.cpu s) ct p = fireTail st s (L.cpu s) ct p := by
  unfold fireTail
  by_cases h0 : p.ntfn = 0#u64
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0, ntfn_state_guard p.ntfn s h1]
  refine bind_guard_congr rfl fun x _ => ?_
  by_cases ha : x = obj.NTFN_ACTIVE
  · rw [if_pos ha, if_pos ha]
  rw [if_neg ha, if_neg ha]
  by_cases hi : x = obj.NTFN_IDLE
  · rw [if_pos hi, if_pos hi, PathObl.obj.Ntfn.bound_tcb.guard (gS := gS) p.ntfn s h2]
    refine bind_guard_congr rfl fun b2 _ => ?_
    by_cases hz : b2 = 0#u64
    · rw [if_pos hz, if_pos hz]
    rw [if_neg hz, if_neg hz]
    by_cases hn : (b2 != p.tm) = true
    · rw [if_pos hn, if_pos hn]
    rw [if_neg hn, if_neg hn, PathObl.obj.Tcb.state.guard (gS := gS) p.tm s h3]
    refine bind_guard_congr rfl fun bs _ => ?_
    by_cases hv : bs = sched.TS_RUNNING_VM
    · rw [if_pos hv, if_pos hv]
    rw [if_neg hv, if_neg hv]
    by_cases hr : bs = sched.TS_BLOCKED_ON_RECV
    · rw [if_pos hr, if_pos hr]
      by_cases hwt : p.waiter = p.tm
      swap
      · rw [if_neg hwt, if_neg hwt]
      rw [if_pos hwt, if_pos hwt]
      by_cases he : (p.ep != 0#u64) = true
      swap
      · rw [if_neg he, if_neg he]
      rw [if_pos he, if_pos he]
      exact hw1.guard ct
    · rw [if_neg hr, if_neg hr]
  · rw [if_neg hi, if_neg hi]
    by_cases hw : x = obj.NTFN_WAITING
    swap
    · rw [if_neg hw, if_neg hw]
    rw [if_pos hw, if_pos hw, PathObl.obj.Ntfn.head.guard (gS := gS) p.ntfn s h4]
    exact bind_guard_congr rfl fun w ew => (hw2 w ew).guard ct

/-- The walk to the due thread's successor: left links from its right child. -/
theorem fire_ok_loop.guard {s : S} (P : U64 → Prop)
    (hP : ∀ x, P x → R (core.num.U64.wrapping_add x 3544#u64) ∧ ∀ y, obj.Tcb.timer_left st x s = ok y → P y)
    {i fuel : U64} (hi : P i) :
    GE (localtimer.fire_ok_loop gS s i fuel) (localtimer.fire_ok_loop st s i fuel) P := by
  unfold localtimer.fire_ok_loop
  refine GE.loop (fun y : U64 × U64 => P y.1) (fun y => y.2.val) (fun y hy => ?_) (i, fuel) hi
  obtain ⟨i1, f1⟩ := y
  -- `PathObl.guard`: in this theorem's body a bare `guard` names the theorem itself (`fire_ok_loop.guard`)
  show GE (localtimer.fire_ok_loop.body gS s i1 f1) (localtimer.fire_ok_loop.body st s i1 f1) _
  unfold localtimer.fire_ok_loop.body
  rw [PathObl.obj.Tcb.timer_left.guard (gS := gS) i1 s (hP i1 hy).1]
  refine GE.bind (GE.refl _) fun j ej => ?_
  have hj : P j := (hP i1 hy).2 j ej
  refine GE.ite (fun _ => GE.ite (fun hf => GE.bind (GE.refl _) fun f2 ef => GE.ret ?_)
    (fun _ => GE.ret ?_)) (fun _ => GE.ret ?_)
  · unfold LoopPost; exact ⟨hj, ge_sub1_lt hf ef⟩
  · unfold LoopPost; exact hy
  · unfold LoopPost; exact hy

/-- **`fire_ok` on the guarded store** (module docstring). -/
theorem fire_ok.guard {s : S} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan} {now : U64} (P : U64 → Prop)
    (hr : R (core.num.U64.wrapping_add p.tm 3552#u64)) (hp : R (core.num.U64.wrapping_add p.tm 3560#u64))
    (hd1 : ∀ x, obj.Tcb.timer_parent st p.tm s = ok x → R (core.num.U64.wrapping_add x 3528#u64))
    (hP0 : ∀ x, obj.Tcb.timer_right st p.tm s = ok x → P x)
    (hP : ∀ x, P x → R (core.num.U64.wrapping_add x 3544#u64) ∧ ∀ y, obj.Tcb.timer_left st x s = ok y → P y)
    (hd2 : ∀ x, P x → R (core.num.U64.wrapping_add x 3528#u64))
    (h1 : R (core.num.U64.wrapping_add p.ntfn layout.ntfn.TAIL_STATE))
    (h2 : R (core.num.U64.wrapping_add p.ntfn layout.ntfn.BOUND_TCB))
    (h3 : R (core.num.U64.wrapping_add p.tm layout.tcb.STATE)) (hw1 : WakeRd st R s p.tm p.ntfn)
    (h4 : R (core.num.U64.wrapping_add p.ntfn layout.ntfn.HEAD))
    (hw2 : ∀ w, obj.Ntfn.head st p.ntfn s = ok w → WakeRd st R s w p.ntfn) :
    localtimer.fire_ok gS s (L.cpu s) ct p now = localtimer.fire_ok st s (L.cpu s) ct p now := by
  have hT := fireTail.guard (gS := gS) (ct := ct) h1 h2 h3 hw1 h4 hw2
  rw [fire_ok_eq, fire_ok_eq]
  by_cases h0 : p.tm = 0#u64
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0, PathObl.obj.Tcb.timer_right.guard (gS := gS) p.tm s hr]
  refine bind_guard_congr rfl fun i ei => ?_
  rw [PathObl.obj.Tcb.timer_parent.guard (gS := gS) p.tm s hp]
  refine bind_guard_congr rfl fun i1 ei1 => ?_
  refine bind_guard_congr rfl fun b _ => ?_
  cases b
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    refine (GE.bind (Q := fun _ => True) (fire_ok_loop.guard P hP (hP0 i ei)) fun i2 hi2 =>
      ⟨?_, fun _ _ => trivial⟩).1
    refine bind_guard_congr rfl fun b1 _ => ?_
    cases b1
    · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
        PathObl.obj.Tcb.timer_deadline.guard (gS := gS) i2 s (hd2 i2 hi2)]
      refine bind_guard_congr rfl fun d _ => ?_
      by_cases hd : d ≤ now
      · rw [if_pos hd, if_pos hd]
      · rw [if_neg hd, if_neg hd]; exact hT
    · rw [if_pos rfl, if_pos rfl]; exact hT
  · rw [if_pos rfl, if_pos rfl]
    refine bind_guard_congr rfl fun b1 _ => ?_
    cases b1
    · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
        PathObl.obj.Tcb.timer_deadline.guard (gS := gS) i1 s (hd1 i1 ei1)]
      refine bind_guard_congr rfl fun d _ => ?_
      by_cases hd : d ≤ now
      · rw [if_pos hd, if_pos hd]
      · rw [if_neg hd, if_neg hd]; exact hT
    · rw [if_pos rfl, if_pos rfl]; exact hT

theorem core_of_guard (s : S) (t : obj.Tcb) (h : R (core.num.U64.wrapping_add t 3568#u64)) :
    localtimer.core_of gS s t = localtimer.core_of st s t := by
  unfold localtimer.core_of
  rw [PathObl.obj.Tcb.timer_height.guard (gS := gS) t s h]

/-- `plan_objects` goes past its first check for `tm`: `tm` is homed on this core and armed in this core's tree. -/
def TmHere (st : machine.Store S) [L : LawfulStore st] (s : S) (tm : U64) : Prop :=
  obj.Tcb.affinity st tm s = ok (L.cpu s) ∧ localtimer.core_of st s tm = ok (L.cpu s)

/-- What `plan_objects` reads of the earliest armed thread `tm` and of its bound notification: its `AFFINITY`,
`TIMER_HEIGHT` and `BOUND_NTFN`, and, once `tm` is this core's (`TmHere`), its `STATE`, `BLOCK_OBJ`, `REPLY_OBJ` and
its bound notification's state and `BOUND_TCB`. -/
structure PlanTm (st : machine.Store S) [L : LawfulStore st] (R : U64 → Prop) (s : S) (tm : U64) : Prop where
  aff : R (core.num.U64.wrapping_add tm 3520#u64)
  ht : R (core.num.U64.wrapping_add tm 3568#u64)
  bn : R (core.num.U64.wrapping_add tm 3368#u64)
  here : TmHere st s tm →
    R (core.num.U64.wrapping_add tm layout.tcb.STATE) ∧ R (core.num.U64.wrapping_add tm 3336#u64) ∧
    R (core.num.U64.wrapping_add tm 3360#u64) ∧
    (∀ n, obj.Tcb.bound_ntfn st tm s = ok n → n ≠ 0#u64 →
      R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) ∧ R (core.num.U64.wrapping_add n layout.ntfn.BOUND_TCB))

set_option maxHeartbeats 4000000 in
/-- **`plan_objects` on the guarded store**: it reads the node's `TIMER_MIN` and what `PlanTm` lists. -/
theorem plan_objects.guard {s : S} (h1 : R (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))
    (h2 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      PlanTm st R s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) :
    localtimer.plan_objects gS s = localtimer.plan_objects st s := by
  unfold localtimer.plan_objects
  rw [PathObl.gst_cur_cpu (g := gS)]
  refine bind_guard_congr rfl fun cpu ecpu => ?_
  rw [L.cur_cpu_eq] at ecpu
  have hc := ok_inj_ff ecpu
  subst hc
  dsimp only
  rw [PathObl.obj.node_get.guard (gS := gS) s _ _ h1]
  refine bind_guard_congr rfl fun i ei => ?_
  rw [node_get_ok] at ei
  have hi := ok_inj_ff ei
  subst hi
  refine bind_guard_congr rfl fun b eb => ?_
  rw [is_null_eq eb]
  by_cases h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64
  · rw [if_pos (decide_eq_true h0), if_pos (decide_eq_true h0)]
  have P := h2 h0
  rw [if_neg (by simpa using h0), if_neg (by simpa using h0), PathObl.obj.Tcb.affinity.guard (gS := gS) _ s P.aff]
  refine bind_guard_congr rfl fun i1 ei1 => ?_
  by_cases ha : (i1 != L.cpu s) = true
  · rw [if_pos ha, if_pos ha]
  have e1 : i1 = L.cpu s := by by_contra hne; exact ha (bne_iff_ne.mpr hne)
  subst e1
  rw [if_neg ha, if_neg ha, core_of_guard s _ P.ht]
  refine bind_guard_congr rfl fun i2 ei2 => ?_
  by_cases hb : (i2 != L.cpu s) = true
  · rw [if_pos hb, if_pos hb]
  have e2 : i2 = L.cpu s := by by_contra hne; exact hb (bne_iff_ne.mpr hne)
  subst e2
  have hh : TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) := And.intro ei1 ei2
  obtain ⟨Pst, Pbo, Pro, Pnt⟩ := P.here hh
  rw [if_neg hb, if_neg hb, PathObl.obj.Tcb.bound_ntfn.guard (gS := gS) _ s P.bn]
  refine bind_guard_congr rfl fun n en => ?_
  by_cases hn : n = 0#u64
  · rw [if_pos hn, if_pos hn]
  obtain ⟨hn1, hn2⟩ := Pnt n en hn
  rw [if_neg hn, if_neg hn]
  refine bind_guard_congr rfl fun x _ => ?_
  obtain ⟨x1, x2⟩ := x
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [ntfn_state_guard n s hn1]
  refine bind_guard_congr rfl fun i3 _ => ?_
  by_cases h3 : (i3 != obj.NTFN_IDLE) = true
  · rw [if_pos h3, if_pos h3]
  rw [if_neg h3, if_neg h3, PathObl.obj.Ntfn.bound_tcb.guard (gS := gS) n s hn2]
  refine bind_guard_congr rfl fun i4 _ => ?_
  by_cases h4 : (i4 != L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) = true
  · rw [if_pos h4, if_pos h4]
  rw [if_neg h4, if_neg h4, PathObl.obj.Tcb.state.guard (gS := gS) _ s Pst]
  refine bind_guard_congr rfl fun i5 _ => ?_
  by_cases h5 : (i5 != sched.TS_BLOCKED_ON_RECV) = true
  · rw [if_pos h5, if_pos h5]
  rw [if_neg h5, if_neg h5, PathObl.obj.Tcb.block_obj.guard (gS := gS) _ s Pbo]
  refine bind_guard_congr rfl fun ep _ => ?_
  by_cases h6 : ep = 0#u64
  · rw [if_pos h6, if_pos h6]
  rw [if_neg h6, if_neg h6]
  refine bind_guard_congr rfl fun y _ => ?_
  obtain ⟨y1, y2⟩ := y
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [PathObl.obj.Tcb.reply_obj.guard (gS := gS) _ s Pro]

end

end Fl4Proofs.P2
