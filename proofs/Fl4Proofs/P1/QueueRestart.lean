/-
P1: the pieces of `restart` (sched.rs; seL4 `restart`, MCS): its head
(`cancel_ipc`, then the `Restart` state), `schedcontext::resume` (which may
`postpone` the SC's thread) and its tail (`possible_switch_to` of a
schedulable thread) keep `SchedQueuesInv`.  The middle `refill_unblock_check`
is a free-word write (`sporadic.unblock_check.fr`) given `RefillsWF` of the
thread's SC.  Composing them into `sched.restart` needs the SC's words (its
refill ring, `CORE` and `TCB` words) to survive `cancel_ipc`'s reply-object
writes and `unblock_check`, which needs object-level disjointness of reply
objects and SCs that the P1 invariant does not record (see the report).
-/
import Fl4Proofs.P1.QueueCancel
import Fl4Proofs.P1.QueueSchedStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64}
variable {Cs : Set U64} {A : Type _} {ar : machine.Arch A}

theorem ts_restart : sched.TS_RESTART = 2#u64 := ts_vals.2.1

theorem runnable_restart : Runnable sched.TS_RESTART := Or.inr rfl
theorem not_blocked_restart : ¬ Blocked sched.TS_RESTART := by
  obtain ⟨-, -, h3, h4, h6⟩ := ts_vals
  unfold Blocked; rw [h3, h4, h6, ts_restart]; decide

/-- The head of `restart`: `cancel_ipc`, then the thread is `Restart`. -/
theorem restart_head (s : S) (a : A) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω s Q R) (ht : t ∈ T)
    (hrecv : L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s (replyA t) ≠ 0#u64 →
      rTcbA (L.mem s (replyA t)) ∈ Ω)
    (hreply : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY → ReplyΩ st Ω s t) :
    (do
      let (s1, a1) ← ipc.cancel_ipc st ar s a t
      let s2 ← sched.set_thread_state st s1 t sched.TS_RESTART
      ok (s2, a1)) ⦃ s' _ => SchedQueuesInv st T Cs Ω s' Q R ∧ L.mem s' (stA t) = sched.TS_RESTART ⦄ := by
  refine WP.spec_bind (ipc.cancel_ipc.inv s a t Q R h ht hrecv hreply) ?_
  rintro ⟨s1, a1⟩ ⟨h1, nb1, -, -⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (WP.spec_and (sched.set_thread_state.inv s1 t _ Q R h1 ht not_blocked_restart (Or.inr nb1)
    ⟨fun _ _ _ _ _ => runnable_restart, fun _ _ _ => runnable_restart, fun _ => runnable_restart⟩)
    (sched.set_thread_state.state s1 t _ Q R h1 ht)) ?_
  rintro s2 ⟨h2, e2, -⟩
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact ⟨h2.congrX empty_congr, e2⟩

theorem sporadic.sufficient.ok (hA : P0.ArchTotal ar) (s : S) (a : A) (sc : obj.Sc) (u : U64) :
    sporadic.sufficient st ar s a sc u ⦃ _ => True ⦄ := by
  unfold sporadic.sufficient sporadic.capacity
  step with sporadic.head.spec as ⟨r⟩
  refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun _ _ => ?_
  · split
    · simp
    · step*
  · step with sporadic.min_budget.ok hA as ⟨m⟩

/-- seL4 `schedContext_resume`: a schedulable thread whose SC is not ready
or has too little budget is postponed.  The SC's `TCB` and `CORE` words
must name a TCB (not the switch-to candidate) and a core. -/
theorem schedcontext.resume.inv (hA : P0.ArchTotal ar) (s : S) (a : A) (sc : obj.Sc)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω s Q R)
    (hsc : sc ≠ 0#u64 → L.mem s (scTcbA sc) ≠ 0#u64 →
      L.mem s (scTcbA sc) ∈ T ∧ OutsideObjs st T Cs s (scCoreA sc) ∧ L.mem s (scCoreA sc) ∈ Cs ∧
        L.actionW s ≠ L.mem s (scTcbA sc)) :
    schedcontext.resume st ar s a sc ⦃ s' _ => ∃ Q' R', SchedQueuesInv st T Cs Ω s' Q' R' ⦄ := by
  unfold schedcontext.resume
  step with obj.Sc.is_null.spec as ⟨b, b_post⟩
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h⟩
  rename_i hb
  have hsc0 : sc ≠ 0#u64 := by simpa [b_post] using hb
  step with obj.Sc.tcb.spec as ⟨i, i_post⟩
  step with obj.Tcb.is_null.spec as ⟨b1, b1_post⟩
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h⟩
  rename_i hb1
  have hi0 : L.mem s (scTcbA sc) ≠ 0#u64 := by rw [← i_post]; simpa [b1_post] using hb1
  obtain ⟨hiT, hcore, hcs, hna⟩ := hsc hsc0 hi0
  step with sched.is_schedulable.spec' as ⟨b2, b2_post⟩
  split
  · rename_i hb2
    obtain ⟨hrun, -, hr0⟩ := b2_post hb2
    rw [i_post] at hrun hr0
    have post := sched.postpone.inv s sc Q R h hiT hr0 hcore hcs hrun hna
    step with sporadic.ready.spec as ⟨b3⟩
    split
    · step with sporadic.sufficient.ok (st := st) hA as ⟨b4⟩
      split
      · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h⟩
      · exact WP.spec_bind post fun s1 h1 => by simpa using h1
    · exact WP.spec_bind post fun s1 h1 => by simpa using h1
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h⟩

/-- The tail of `restart`: a schedulable thread goes through
`possible_switch_to`. -/
theorem restart_tail (s : S) (a : A) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω s Q R) (ht : t ∈ T) :
    (do
      let b ← sched.is_schedulable st s t
      if b then do
        let s5 ← sched.possible_switch_to st s t
        ok (s5, a)
      else ok (s, a)) ⦃ s' _ => ∃ Q' R', SchedQueuesInv st T Cs Ω s' Q' R' ⦄ := by
  step with sched.is_schedulable.spec' as ⟨b, b_post⟩
  split
  · rename_i hb
    refine WP.spec_bind (sched.possible_switch_to.inv s t Q R h ht (b_post hb).1) ?_
    rintro s5 ⟨Q5, h5⟩
    simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q5, R, h5⟩
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h⟩

end

end Fl4Proofs.P1
