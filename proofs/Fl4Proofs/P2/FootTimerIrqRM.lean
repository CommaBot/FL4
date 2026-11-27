/-
# P2: the round-robin ring merge's frame, and `check_budget`'s rr case on the guarded store

`cbRR_frame`: `charge_budget`'s round-robin ring update (`cbRR`: head refill := head + tail amounts, tail amount
:= 0, SC `CONSUMED` += used) writes only the SC's ring words and its `CONSUMED`, and keeps the ring well formed
(P1 `RefillsWF.putS` / `frame_putS` / `wr_cons`, as in `charge_budget.allG`).

With it, `sched.charge_budget.guard_rrC` discharges `charge_budget.guard_rr`'s `htl` by `cbTail.guard_rr`: the node's
words keep their addresses across the ring writes, and `RRTail` at every state after the node's `CONSUMED` is
cleared remains a premise (`F`, for the round-robin walk). `sched.check_budget.guard_rr`: an insufficient budget,
then `charge_budget` (`hcb`).

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqRT
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (RdHead bind_guard_congr)

section law
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- Two refill writes, at the ring's head and tail indices, stay in the ring and keep it well formed. -/
theorem putS2_frame {s : S} {sc : U64} {z : Nat} (hW : RefillsWF st s sc z) (r1 r2 : sporadic.Refill) :
    WritesIn st s (L.putS (L.putS s sc (L.rhead s sc) r1) sc (L.rtail s sc) r2) (InRing sc z) ∧
      RefillsWF st (L.putS (L.putS s sc (L.rhead s sc) r1) sc (L.rtail s sc) r2) sc z := by
  have h4 := hW.putS (r := r1) hW.head_lt
  have w4 := hW.frame_putS (r := r1) hW.head_lt
  obtain ⟨h8, -, -⟩ := hW.bounds
  have hfit : sc.val + 96 + 16 * (L.rhead s sc).val + 16 ≤ 2 ^ 64 := by
    have := hW.bounds.2.2; have := hW.inside; have := hW.head_lt; have := hW.le_abs
    have := absMax_lt z; obtain ⟨-, hm, -⟩ := hW.bounds; omega
  have htl : (L.rtail s sc).val < (L.rmax (L.putS s sc (L.rhead s sc) r1) sc).val := by
    rw [rmax_putS h8 hfit]; exact hW.tail_lt
  exact ⟨w4.trans1 (h4.frame_putS htl), h4.putS htl⟩

/-- **The round-robin ring merge** writes only the ring and the SC's `CONSUMED`, and keeps the ring well
formed. -/
theorem cbRR_frame {s s2 : S} {sc : U64} {z : Nat} {used : U64} (hW : RefillsWF st s sc z)
    (hal : Aligned (core.num.U64.wrapping_add sc layout.sc.CONSUMED)) (h : cbRR st s sc used = ok s2) :
    WritesIn st s s2 (fun b => InRing sc z b ∨ b = core.num.U64.wrapping_add sc layout.sc.CONSUMED) ∧
      RefillsWF st s2 sc z := by
  unfold cbRR at h
  rw [eq_of_spec_fd (obj.Sc.refill_head.spec (L := L) s sc),
    eq_of_spec_fd (obj.Sc.refill_tail.spec (L := L) s sc)] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (sporadic.get.spec (L := L) s sc (L.rhead s sc)),
    eq_of_spec_fd (sporadic.get.spec (L := L) s sc (L.rtail s sc))] at h
  simp only [bind_ok, lift] at h
  rw [eq_of_spec_fd (sporadic.put.spec (L := L) s sc (L.rhead s sc) _)] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (sporadic.put.spec (L := L) _ sc (L.rtail s sc) _)] at h
  simp only [bind_ok] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (obj.Sc.set_consumed.spec (L := L) _ sc _)] at h
  have hx : ∃ r1 r2 v, L.wr (L.putS (L.putS s sc (L.rhead s sc) r1) sc (L.rtail s sc) r2)
      (core.num.U64.wrapping_add sc layout.sc.CONSUMED) v = s2 := ⟨_, _, _, ok_inj_ff h⟩
  obtain ⟨r1, r2, v, rfl⟩ := hx
  obtain ⟨w3, h3⟩ := putS2_frame hW r1 r2
  exact ⟨(w3.trans (writesIn_wr hal)).mono fun b hb => by
      rcases hb with hb | hb
      · exact Or.inl hb
      · exact Or.inr hb, h3.wr_cons⟩

end law

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- **`charge_budget` on a round-robin SC, its tail composed in** (module docstring). -/
theorem sched.charge_budget.guard_rrC {A : Type} (ar : machine.Arch A) {T : Set U64} (s : S) (a : A) (used : U64)
    {z : Nat}
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.CUR_SC)) (h2 : R (L.nodeAt s (L.cpu s) layout.node.IDLE_SC))
    (hsc : ∀ sc, sched.cur_sc st s = ok sc → ∀ isc, sched.idle_sc st s = ok isc → sc ≠ isc ∧
      R (core.num.U64.wrapping_add sc layout.sc.PERIOD) ∧ sporadic.is_round_robin st s sc = ok true ∧
      R (core.num.U64.wrapping_add sc layout.sc.REFILL_HEAD) ∧
      R (core.num.U64.wrapping_add sc layout.sc.REFILL_TAIL) ∧
      (∀ i, (obj.Sc.refill_head st sc s = ok i ∨ obj.Sc.refill_tail st sc s = ok i) →
        R (rtA sc i) ∧ R (raA sc i) ∧ W (rtA sc i) ∧ W (raA sc i)) ∧
      R (core.num.U64.wrapping_add sc layout.sc.CONSUMED) ∧ W (core.num.U64.wrapping_add sc layout.sc.CONSUMED))
    (hW : RefillsWF st s (L.cscW s) z) (hal : Aligned (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED))
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (F : ∀ s2 s3, cbRR st s (L.cscW s) used = ok s2 → sched.set_consumed st s2 0#u64 = ok s3 →
      RRTail st ar T R W s3 a) :
    sched.charge_budget gS ar s a used true = sched.charge_budget st ar s a used true := by
  refine sched.charge_budget.guard_rr (gS := gS) ar s a used true h1 h2 hsc fun sc s2 esc e2 => ?_
  have esc' : sched.cur_sc st s = ok (L.cscW s) := eq_of_spec_fd (sched.cur_sc.spec (L := L) s)
  rw [esc'] at esc
  have e : L.cscW s = sc := ok_inj_ff esc
  subst e
  obtain ⟨w, -⟩ := cbRR_frame hW hal e2
  exact cbTail.guard_rr (gS := gS) ar s2 a
    (fun o ho h8 => by rw [w.2.1, nodeAt_of_ksb w.1]; exact hNd o ho h8) fun s3 e3 => F s2 s3 e2 e3

/-- **`check_budget` with an insufficient budget**: `CUR_SC`, `CONSUMED`, the SC's head, then `charge_budget`
(`hcb`). -/
theorem sched.check_budget.guard_rr {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.CUR_SC)) (h2 : R (L.nodeAt s (L.cpu s) layout.node.CONSUMED))
    (h3 : ∀ sc, sched.cur_sc st s = ok sc → RdHead (L := L) R s sc)
    (hins : ∀ sc c, sched.cur_sc st s = ok sc → sched.consumed st s = ok c →
      sporadic.sufficient st ar s a sc c = ok false)
    (hcb : ∀ c, sched.consumed st s = ok c →
      sched.charge_budget gS ar s a c true = sched.charge_budget st ar s a c true) :
    sched.check_budget gS ar s a = sched.check_budget st ar s a := by
  unfold sched.check_budget
  rw [PathObl.sched.cur_sc.guard (gS := gS) s h1]
  refine bind_guard_congr rfl fun sc esc => ?_
  rw [PathObl.sched.consumed.guard (gS := gS) s h2]
  refine bind_guard_congr rfl fun c ec => ?_
  rw [PathObl.sporadic.sufficient.guard (gS := gS) ar s a sc c (h3 sc esc), hins sc c esc ec]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  rw [hcb c ec]

end gst

end Fl4Proofs.P2
