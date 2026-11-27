/-
# P2: the round-robin case of the timer interrupt, `check_budget`'s tail on the guarded store

The rr case of `localtimer.handle_timer_irq_local` (budget insufficient, `round_robin_ok`): `check_budget` calls
`charge_budget`, which on a round-robin SC merges the tail refill into the head one (`cbRR`), adds the used time to
the SC's `CONSUMED`, clears the node's `CONSUMED`, and, the current thread being schedulable, ends its timeslice
(`end_timeslice`: append to its ready queue), asks for a reschedule and sets `REPROGRAM` (`cbTail`).

On any store `gS` answering `R` reads and `W` writes as `st` (`PathObl.GRd` / `PathObl.GWr`):

* `sched.charge_budget.guard_rr`: the current and idle SC words, the round-robin SC's `PERIOD`, ring head / tail
  words, the two refills (read and written) and `CONSUMED`; then `cbTail` at every state `cbRR` can end in (`htl`);
* `cbTail.guard`: the node's words, the current thread's schedulability words, then `end_timeslice` at the real
  run's state (`hend`), `reschedule_required` with the action `RESUME_CURRENT` and `set_reprogram`;
* `sched.end_timeslice.guard_rr`: a round-robin SC that is ready with sufficient budget: the SC's `PERIOD` and
  head refill, the thread's state and timeout-handler slot, then `append` (`happ`);
* `sched.reschedule_required.guard_resume`, `faults.valid_timeout_handler.guard`.

`sched.append` (the ready-queue insertion) and `schedule`'s choose-new path are not covered here.

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqAcc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (RdHead)

section defs
variable {S : Type}

/-- `charge_budget`'s round-robin ring update and `CONSUMED` addition (as in the source). -/
def cbRR (M : machine.Store S) (s : S) (sc : obj.Sc) (used : U64) : Result S := do
  let s3 ← do
    let hi ← obj.Sc.refill_head M sc s
    let ti ← obj.Sc.refill_tail M sc s
    let h ← sporadic.get M s sc hi
    let t ← sporadic.get M s sc ti
    let i ← lift (core.num.U64.wrapping_add h.amount t.amount)
    let s4 ← sporadic.put M s sc hi { h with amount := i }
    sporadic.put M s4 sc ti { t with amount := 0#u64 }
  let i ← obj.Sc.consumed M sc s3
  let total ← lift (core.num.U64.wrapping_add i used)
  obj.Sc.set_consumed M sc s3 total

/-- `charge_budget` after the SC update (as in the source). -/
def cbTail (M : machine.Store S) {A : Type} (ar : machine.Arch A) (s2 : S) (a : A) (ctf : Bool) :
    Result (S × A) := do
  let s3 ← sched.set_consumed M s2 0#u64
  let ct ← sched.cur_thread M s3
  let b1 ← sched.is_schedulable M s3 ct
  if b1
  then
    let (s4, a1) ← sched.end_timeslice M ar s3 a ctf
    let s5 ← sched.reschedule_required M s4
    let s6 ← sched.set_reprogram M s5
    ok (s6, a1)
  else ok (s3, a)

end defs

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- **`charge_budget` on a round-robin SC** (module docstring). -/
theorem sched.charge_budget.guard_rr {A : Type} (ar : machine.Arch A) (s : S) (a : A) (used : U64) (ctf : Bool)
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.CUR_SC)) (h2 : R (L.nodeAt s (L.cpu s) layout.node.IDLE_SC))
    (hsc : ∀ sc, sched.cur_sc st s = ok sc → ∀ isc, sched.idle_sc st s = ok isc → sc ≠ isc ∧
      R (core.num.U64.wrapping_add sc layout.sc.PERIOD) ∧ sporadic.is_round_robin st s sc = ok true ∧
      R (core.num.U64.wrapping_add sc layout.sc.REFILL_HEAD) ∧
      R (core.num.U64.wrapping_add sc layout.sc.REFILL_TAIL) ∧
      (∀ i, (obj.Sc.refill_head st sc s = ok i ∨ obj.Sc.refill_tail st sc s = ok i) →
        R (rtA sc i) ∧ R (raA sc i) ∧ W (rtA sc i) ∧ W (raA sc i)) ∧
      R (core.num.U64.wrapping_add sc layout.sc.CONSUMED) ∧ W (core.num.U64.wrapping_add sc layout.sc.CONSUMED))
    (htl : ∀ sc s2, sched.cur_sc st s = ok sc → cbRR st s sc used = ok s2 →
      cbTail gS ar s2 a ctf = cbTail st ar s2 a ctf) :
    sched.charge_budget gS ar s a used ctf = sched.charge_budget st ar s a used ctf := by
  unfold sched.charge_budget
  rw [PathObl.sched.cur_sc.guard (gS := gS) s h1]
  refine PathObl.bind_guard_congr rfl fun sc esc => ?_
  rw [PathObl.sched.idle_sc.guard (gS := gS) s h2]
  refine PathObl.bind_guard_congr rfl fun isc eisc => ?_
  obtain ⟨hne, hP, hrr, hH, hTl, hRf, hC, hCw⟩ := hsc sc esc isc eisc
  refine PathObl.bind_guard_congr rfl fun b eb => ?_
  have hb : b = true := (PathObl.post_of_ok (sc_ne.spec' sc isc) eb).2 hne
  subst hb
  simp only [↓reduceIte]
  rw [PathObl.sporadic.is_round_robin.guard (gS := gS) s sc hP, hrr]
  simp only [bind_ok, ↓reduceIte]
  refine PathObl.bind_guard_congr ?_ fun s2 es2 => htl sc s2 esc es2
  refine PathObl.bind_guard_congr ?_ fun s3 _ => ?_
  · rw [PathObl.obj.Sc.refill_head.guard (gS := gS) sc s hH]
    refine PathObl.bind_guard_congr rfl fun hi ehi => ?_
    rw [PathObl.obj.Sc.refill_tail.guard (gS := gS) sc s hTl]
    refine PathObl.bind_guard_congr rfl fun ti eti => ?_
    obtain ⟨r1, r2, w1, w2⟩ := hRf hi (Or.inl ehi)
    obtain ⟨r3, r4, w3, w4⟩ := hRf ti (Or.inr eti)
    rw [PathObl.sporadic.get.guard (gS := gS) s sc hi r1 r2]
    refine PathObl.bind_guard_congr rfl fun h _ => ?_
    rw [PathObl.sporadic.get.guard (gS := gS) s sc ti r3 r4]
    refine PathObl.bind_guard_congr rfl fun t _ => ?_
    refine PathObl.bind_guard_congr rfl fun i _ => ?_
    rw [PathObl.sporadic.put.guard (gS := gS) (sc := sc) s hi _ w1 w2]
    refine PathObl.bind_guard_congr rfl fun s4 _ => ?_
    exact PathObl.sporadic.put.guard (gS := gS) (sc := sc) s4 ti _ w3 w4
  · rw [PathObl.obj.Sc.consumed.guard (gS := gS) sc s3 hC]
    refine PathObl.bind_guard_congr rfl fun i _ => ?_
    refine PathObl.bind_guard_congr rfl fun total _ => ?_
    exact PathObl.obj.Sc.set_consumed.guard (gS := gS) sc s3 total hCw

/-- **`reschedule_required` with the action `RESUME_CURRENT`**: reads the action, sets it to `CHOOSE_NEW`. -/
theorem sched.reschedule_required.guard_resume (s : S)
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) (h2 : W (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (ha : L.actionW s = sched.ACTION_RESUME_CURRENT) :
    sched.reschedule_required gS s = sched.reschedule_required st s := by
  unfold sched.reschedule_required
  rw [PathObl.sched.action.guard (gS := gS) s h1, eq_of_spec_fd (sched.action.spec (L := L) s), ha]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact PathObl.sched.set_action.guard (gS := gS) s _ h2

/-- `reschedule_required` with the action `RESUME_CURRENT` sets it to `CHOOSE_NEW`. -/
theorem reschedule_required_resume {X Y : S} (ha : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (h : sched.reschedule_required st X = ok Y) :
    Y = L.wr X (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) sched.ACTION_CHOOSE_NEW := by
  unfold sched.reschedule_required at h
  rw [eq_of_spec_fd (sched.action.spec (L := L) X), ha] at h
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  rw [eq_of_spec_fd (sched.set_action.spec (L := L) X _)] at h
  exact (ok_inj_ff h).symm

/-- **The timeout-handler check**: the handler slot's two words. -/
theorem faults.valid_timeout_handler.guard (s : S) (t : obj.Tcb)
    (h : ∀ sl, obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER = ok sl →
      R sl ∧ R (core.num.U64.wrapping_add sl 8#u64)) :
    faults.valid_timeout_handler gS s t = faults.valid_timeout_handler st s t := by
  unfold faults.valid_timeout_handler
  refine PathObl.bind_guard_congr rfl fun sl esl => ?_
  rw [PathObl.obj.Slot.cap.guard (gS := gS) sl s (h sl esl).1 (h sl esl).2]

/-- **`end_timeslice` of a round-robin SC that is ready with sufficient budget** (timeout faults allowed): the
SC's `PERIOD` and head refill, the thread's state and timeout-handler slot, then `append` (`happ`). -/
theorem sched.end_timeslice.guard_rr {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.CUR_SC)) (h2 : R (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hp : R (core.num.U64.wrapping_add (L.cscW s) layout.sc.PERIOD))
    (hrr : sporadic.is_round_robin st s (L.cscW s) = ok true) (hst : R (stA (L.curW s)))
    (hvt : ∀ sl, obj.Tcb.slot (L.curW s) layout.tcb.SLOT_TIMEOUT_HANDLER = ok sl →
      R sl ∧ R (core.num.U64.wrapping_add sl 8#u64))
    (hhd : RdHead (L := L) R s (L.cscW s)) (hct : R (ctA (L := L) s))
    (hrd : sporadic.ready st s (L.cscW s) = ok true)
    (hsf : sporadic.sufficient st ar s a (L.cscW s) 0#u64 = ok true)
    (happ : sched.append gS s (L.curW s) = sched.append st s (L.curW s)) :
    sched.end_timeslice gS ar s a true = sched.end_timeslice st ar s a true := by
  have esc : sched.cur_sc st s = ok (L.cscW s) := eq_of_spec_fd (sched.cur_sc.spec (L := L) s)
  unfold sched.end_timeslice
  rw [PathObl.sched.cur_sc.guard (gS := gS) s h1, esc]
  simp only [bind_ok]
  rw [PathObl.sched.cur_thread.guard (gS := gS) s h2, cur_thread_ok]
  simp only [bind_ok]
  rw [PathObl.sporadic.is_round_robin.guard (gS := gS) s _ hp, hrr]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.state.guard (gS := gS) _ s hst]
  refine PathObl.bind_guard_congr rfl fun v _ => ?_
  refine PathObl.bind_guard_congr ?_ fun valid _ => ?_
  · by_cases hv : (v != sched.TS_RUNNING_VM) = true
    · rw [if_pos hv, if_pos hv, faults.valid_timeout_handler.guard (gS := gS) s _ hvt]
    · rw [if_neg hv, if_neg hv]
  · simp only [↓reduceIte]
    rw [PathObl.sporadic.ready.guard (gS := gS) s _ hhd hct, hrd]
    simp only [bind_ok, ↓reduceIte]
    rw [PathObl.sporadic.sufficient.guard (gS := gS) ar s a _ _ hhd, hsf]
    simp only [bind_ok, ↓reduceIte]
    rw [happ]

/-- **`charge_budget`'s tail** (module docstring): `hend` gives `end_timeslice` at the real run's state, which
keeps the kernel base, the core and the action `RESUME_CURRENT`. -/
theorem cbTail.guard {A : Type} (ar : machine.Arch A) (s2 : S) (a : A) (ctf : Bool)
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s2 (L.cpu s2) o) ∧ W (L.nodeAt s2 (L.cpu s2) o))
    (hct : ∀ s3, sched.set_consumed st s2 0#u64 = ok s3 → R (stA (L.curW s3)) ∧ R (scA (L.curW s3)) ∧
      R (maxA (L.mem s3 (scA (L.curW s3)))) ∧ R (inqA (L.curW s3)))
    (hend : ∀ s3, sched.set_consumed st s2 0#u64 = ok s3 → sched.is_schedulable st s3 (L.curW s3) = ok true →
      sched.end_timeslice gS ar s3 a ctf = sched.end_timeslice st ar s3 a ctf ∧
      ∀ s4 a1, sched.end_timeslice st ar s3 a ctf = ok (s4, a1) →
        L.ksb s4 = L.ksb s2 ∧ L.cpu s4 = L.cpu s2 ∧ L.actionW s4 = sched.ACTION_RESUME_CURRENT) :
    cbTail gS ar s2 a ctf = cbTail st ar s2 a ctf := by
  unfold cbTail
  have cs := hNd layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  rw [PathObl.sched.set_consumed.guard (gS := gS) s2 _ cs.2]
  refine PathObl.bind_guard_congr rfl fun s3 es3 => ?_
  have e3 : s3 = L.wr s2 (L.nodeA s2 layout.node.CONSUMED) 0#u64 := by
    have e := es3
    rw [eq_of_spec_fd (sched.set_consumed.spec (L := L) s2 _)] at e
    exact (ok_inj_ff e).symm
  have k3 : L.ksb s3 = L.ksb s2 := by rw [e3, L.ksb_wr]
  have c3 : L.cpu s3 = L.cpu s2 := by rw [e3, LawfulStore.cpu_wr]
  have nd3 : ∀ o, L.nodeAt s3 (L.cpu s3) o = L.nodeAt s2 (L.cpu s2) o := fun o => by rw [c3, nodeAt_of_ksb k3]
  rw [PathObl.sched.cur_thread.guard (gS := gS) s3
    (by rw [nd3]; exact (hNd _ (by rw [curth_val]; omega) (by rw [curth_val])).1), cur_thread_ok]
  simp only [bind_ok]
  obtain ⟨r1, r2, r3, r4⟩ := hct s3 es3
  rw [PathObl.sched.is_schedulable.guard (gS := gS) s3 _ r1 r2 r3 r4]
  refine PathObl.bind_guard_congr rfl fun b eb => ?_
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
  simp only [↓reduceIte]
  obtain ⟨g1, g2⟩ := hend s3 es3 eb
  rw [g1]
  refine PathObl.bind_guard_congr rfl fun x ex => ?_
  obtain ⟨s4, a1⟩ := x
  obtain ⟨k4, c4, ac4⟩ := g2 s4 a1 ex
  simp only [Aeneas.Std.uncurry_apply_pair]
  have nd4 : ∀ o, L.nodeAt s4 (L.cpu s4) o = L.nodeAt s2 (L.cpu s2) o := fun o => by rw [c4, nodeAt_of_ksb k4]
  have sa := hNd layout.node.SCHED_ACTION (by rw [act_val]; omega) (by rw [act_val])
  rw [sched.reschedule_required.guard_resume (gS := gS) s4 (by rw [nd4]; exact sa.1) (by rw [nd4]; exact sa.2) ac4]
  refine PathObl.bind_guard_congr rfl fun s5 es5 => ?_
  have e5 := reschedule_required_resume ac4 es5
  have nd5 : ∀ o, L.nodeAt s5 (L.cpu s5) o = L.nodeAt s2 (L.cpu s2) o := fun o => by
    rw [e5, LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _), nd4]
  rw [PathObl.sched.set_reprogram.guard (gS := gS) s5
    (by rw [nd5]; exact (hNd layout.node.REPROGRAM (by simp [layout.node.REPROGRAM])
      (by simp [layout.node.REPROGRAM])).2)]

end gst

end Fl4Proofs.P2
