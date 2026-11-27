/-
# P2 (p2lf): `timer::fire` firing one timer, on the guarded store

`timer.fire.guard_one`: on any store `gS` answering `R` reads and `W` writes as `st`, `timer::fire` at a state `X`
whose earliest timer `tm` (this core's `TIMER_MIN`) is due is its real run when the first iteration's accesses
are allowed (`CUR_TIME`, `TIMER_MIN`, `tm`'s deadline and badge, the guarded `timer::remove`, `tm`'s
`BOUND_NTFN` after it, the guarded `send_signal` of a bound notification, `REPROGRAM`) and the second iteration
stops: at its state the new `TIMER_MIN` is null or not due (premises at the real intermediate states).

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireSig
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (bind_guard_congr)

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- What the second iteration of `fire` reads at its state `Y`, and that it stops (`now` the first's
`CUR_TIME`). -/
def FireStop (st : machine.Store S) [L : LawfulStore st] (R : U64 → Prop) (Y : S) (now : U64) : Prop :=
  R (L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN) ∧
    (L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN) ≠ 0#u64 →
      R (tdA (L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN))) ∧
      L.mem Y (tdA (L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN))) > now)

theorem fire_body_stop {A : Type} (ar : machine.Arch A) (Y : S) (a : A) (now i : U64)
    (h : FireStop st R Y now) :
    timer.fire_loop.body gS ar now Y a i = timer.fire_loop.body st ar now Y a i := by
  obtain ⟨r1, h2⟩ := h
  unfold timer.fire_loop.body
  by_cases hi : i < timer.FIRE_BATCH
  swap
  · simp only [hi, ↓reduceIte]
  simp only [hi, ↓reduceIte, PathObl.LT.gcc, L.cur_cpu_eq, bind_ok, bind_tc_ok]
  rw [PathObl.obj.node_get.guard (gS := gS) Y _ _ r1, node_get_ok]
  simp only [bind_ok, bind_tc_ok, is_null_ok]
  by_cases h0 : L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN) = 0#u64
  · simp only [h0, decide_true, ↓reduceIte]
  obtain ⟨r2, hgt⟩ := h2 h0
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [PathObl.obj.Tcb.timer_deadline.guard (gS := gS) _ Y r2, eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) Y _)]
  simp only [bind_ok, bind_tc_ok, hgt, ↓reduceIte]

theorem fire_body_done {A : Type} (ar : machine.Arch A) (Y : S) (a : A) (now i : U64) {R' : U64 → Prop}
    (h : FireStop st R' Y now) :
    timer.fire_loop.body st ar now Y a i = ok (ControlFlow.done (Y, a)) := by
  obtain ⟨-, h2⟩ := h
  unfold timer.fire_loop.body
  by_cases hi : i < timer.FIRE_BATCH
  swap
  · simp only [hi, ↓reduceIte]
  simp only [hi, ↓reduceIte, L.cur_cpu_eq, bind_ok, bind_tc_ok]
  rw [node_get_ok]
  simp only [bind_ok, bind_tc_ok, is_null_ok]
  by_cases h0 : L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN) = 0#u64
  · simp only [h0, decide_true, ↓reduceIte]
  obtain ⟨-, hgt⟩ := h2 h0
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) Y _)]
  simp only [bind_ok, bind_tc_ok, hgt, ↓reduceIte]

set_option maxHeartbeats 4000000 in
/-- The first iteration of `fire` (the due timer `tm`), on the guarded store, and where it continues. -/
theorem fire_body_one {A : Type} (ar : machine.Arch A) (X : S) (a : A)
    (hRc : R (L.nodeAt X (L.cpu X) layout.node.CUR_TIME)) (hRt : R (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))
    (h0 : L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) ≠ 0#u64)
    (rD : R (tdA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
    (hdue : ¬ L.mem X (tdA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) >
      L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME))
    (rB : R (tbA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
    (hrm : timer.remove gS X (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN)) =
      timer.remove st X (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN)))
    (hk : ∀ X1, timer.remove st X (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN)) = ok X1 →
      R (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) ∧
      (L.mem X1 (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) ≠ 0#u64 →
        notification.send_signal gS ar X1 a (L.mem X1 (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
            (L.mem X (tbA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN)))) =
          notification.send_signal st ar X1 a (L.mem X1 (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
            (L.mem X (tbA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))) ∧
      ∀ X2 a2,
        (if L.mem X1 (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) != 0#u64 then
          notification.send_signal st ar X1 a (L.mem X1 (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
            (L.mem X (tbA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
        else ok (X1, a)) = ok (X2, a2) →
        W (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) ∧
        FireStop st R (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64)
          (L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME))) :
    timer.fire_loop.body gS ar (L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME)) X a 0#u64 = timer.fire_loop.body st ar (L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME)) X a 0#u64 ∧
      ∀ y, timer.fire_loop.body st ar (L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME)) X a 0#u64 = ok (ControlFlow.cont y) →
        FireStop st R y.1 (L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME)) ∧ y.2.2.val = 1 := by
  have hb : (0#u64 : U64) < timer.FIRE_BATCH := by unfold timer.FIRE_BATCH; decide
  constructor
  · unfold timer.fire_loop.body
    simp only [hb, ↓reduceIte, PathObl.LT.gcc, L.cur_cpu_eq, bind_ok, bind_tc_ok]
    rw [PathObl.obj.node_get.guard (gS := gS) X _ _ hRt, node_get_ok]
    simp only [bind_ok, bind_tc_ok, is_null_ok, h0, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [PathObl.obj.Tcb.timer_deadline.guard (gS := gS) _ X rD, eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) X _)]
    simp only [bind_ok, bind_tc_ok, hdue, ↓reduceIte]
    rw [PathObl.obj.Tcb.timer_badge.guard (gS := gS) _ X rB, eq_of_spec_fd (obj.Tcb.timer_badge.val (L := L) X _)]
    simp only [bind_ok, bind_tc_ok]
    rw [hrm]
    refine bind_guard_congr rfl fun X1 h1 => ?_
    obtain ⟨rBn, hsig, hk2⟩ := hk X1 h1
    rw [PathObl.obj.Tcb.bound_ntfn.guard (gS := gS) _ X1 rBn, eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) X1 _)]
    simp only [bind_ok, bind_tc_ok]
    refine bind_guard_congr ?_ fun x hx => ?_
    · by_cases hn : (L.mem X1 (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) != 0#u64) = true
      · rw [if_pos hn, if_pos hn]; exact hsig (bne_iff_ne.mp hn)
      · rw [if_neg hn, if_neg hn]
    · obtain ⟨X2, a2⟩ := x
      obtain ⟨wR, -⟩ := hk2 X2 a2 hx
      simp only [Aeneas.Std.uncurry_apply_pair, PathObl.LT.gcc, L.cur_cpu_eq, bind_ok, bind_tc_ok]
      rw [PathObl.obj.node_set.guard (gS := gS) X2 _ _ _ wR]
  · intro y hy
    unfold timer.fire_loop.body at hy
    simp only [hb, ↓reduceIte, L.cur_cpu_eq, bind_ok, bind_tc_ok] at hy
    rw [node_get_ok] at hy
    simp only [bind_ok, bind_tc_ok, is_null_ok, h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hy
    rw [eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) X _)] at hy
    simp only [bind_ok, bind_tc_ok, hdue, ↓reduceIte] at hy
    rw [eq_of_spec_fd (obj.Tcb.timer_badge.val (L := L) X _)] at hy
    simp only [bind_ok, bind_tc_ok] at hy
    obtain ⟨X1, h1, hy⟩ := bind_eq_ok hy
    obtain ⟨-, -, hk2⟩ := hk X1 h1
    rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) X1 _)] at hy
    simp only [bind_ok, bind_tc_ok] at hy
    obtain ⟨⟨X2, a2⟩, h2, hy⟩ := bind_eq_ok hy
    obtain ⟨-, hst⟩ := hk2 X2 a2 h2
    simp only [Aeneas.Std.uncurry_apply_pair, L.cur_cpu_eq, bind_ok, bind_tc_ok] at hy
    rw [eq_of_spec_fd (obj.node_set.spec (L := L) X2 _ _ _)] at hy
    simp only [bind_ok, bind_tc_ok] at hy
    obtain ⟨i4, hi4, hy⟩ := bind_eq_ok hy
    have e := ok_inj_ff hy
    simp only [ControlFlow.cont.injEq] at e
    subst e
    obtain ⟨z, hz, hzv⟩ := spec_ex_fd (U64.add_spec (x := 0#u64) (y := 1#u64) (by scalar_tac))
    rw [hz] at hi4
    have ez := ok_inj_ff hi4
    subst ez
    refine ⟨hst, ?_⟩
    simp only at hzv ⊢
    rw [hzv]; simp

set_option maxHeartbeats 4000000 in
/-- **`timer::fire` firing exactly one timer, on the guarded store** (module docstring). -/
theorem timer.fire.guard_one {A : Type} (ar : machine.Arch A) (X : S) (a : A)
    (hRc : R (L.nodeAt X (L.cpu X) layout.node.CUR_TIME)) (hRt : R (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))
    (h0 : L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) ≠ 0#u64)
    (rD : R (tdA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
    (hdue : ¬ L.mem X (tdA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) >
      L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME))
    (rB : R (tbA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
    (hrm : timer.remove gS X (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN)) =
      timer.remove st X (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN)))
    (hk : ∀ X1, timer.remove st X (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN)) = ok X1 →
      R (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) ∧
      (L.mem X1 (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) ≠ 0#u64 →
        notification.send_signal gS ar X1 a (L.mem X1 (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
            (L.mem X (tbA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN)))) =
          notification.send_signal st ar X1 a (L.mem X1 (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
            (L.mem X (tbA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))) ∧
      ∀ X2 a2,
        (if L.mem X1 (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) != 0#u64 then
          notification.send_signal st ar X1 a (L.mem X1 (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
            (L.mem X (tbA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
        else ok (X1, a)) = ok (X2, a2) →
        W (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) ∧
        FireStop st R (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64)
          (L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME))) :
    timer.fire gS ar X a = timer.fire st ar X a := by
  unfold timer.fire timer.fire_loop
  simp only [PathObl.LT.gcc, L.cur_cpu_eq, bind_ok, bind_tc_ok]
  rw [PathObl.obj.node_get.guard (gS := gS) X _ _ hRc, node_get_ok]
  simp only [bind_ok, bind_tc_ok]
  refine PathObl.loop_guard_congr
    (fun x => x = (X, a, 0#u64) ∨ (FireStop st R x.1 (L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME)) ∧ 0 < x.2.2.val)) (fun x => 1 - x.2.2.val) ?_ _
    (Or.inl rfl)
  rintro x (rfl | ⟨hs, -⟩)
  · obtain ⟨e, hc⟩ := fire_body_one (gS := gS) ar X a hRc hRt h0 rD hdue rB hrm hk
    refine ⟨e, fun y hy => ?_⟩
    obtain ⟨hs, hv⟩ := hc y hy
    exact ⟨Or.inr ⟨hs, by omega⟩, by simp; omega⟩
  · refine ⟨fire_body_stop (gS := gS) ar x.1 x.2.1 _ x.2.2 hs, fun y hy => ?_⟩
    have hd := fire_body_done ar x.1 x.2.1 _ x.2.2 hs
    rw [hd] at hy
    exact absurd (ok_inj_ff hy) (by simp)

end gst

end Fl4Proofs.P2
