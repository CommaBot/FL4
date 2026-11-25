/-
# P2 (p2lf): the queue operations of the timer interrupt's fire case, on the guarded store

On any store `gS` answering `R` reads and `W` writes as `st` (`PathObl.GRd` / `PathObl.GWr`), the queue
operations a fired timer's signal runs (`tcbqueue.remove` / `prepend` / `append` on either link, a notification's
and an endpoint's queue words, `ntfn_dequeue`, `ep_dequeue`) are their real runs, given the words they read in `R`
and the words they write in `W`. The neighbours' link words are stated at the state the operation starts in
(`L.mem X (nextA l t)` …): the callers name them from the queue invariants.

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqObl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (bind_guard_congr)

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

theorem tcbqueue.prev.guardL (X : S) (l : tcbqueue.Link) (t : U64) (h : R (prevA l t)) :
    tcbqueue.prev gS X l t = tcbqueue.prev st X l t := by
  unfold tcbqueue.prev
  cases l
  · exact PathObl.obj.Tcb.sched_prev.guard (gS := gS) t X h
  · exact PathObl.obj.Tcb.ep_prev.guard (gS := gS) t X h

theorem tcbqueue.next.guardL (X : S) (l : tcbqueue.Link) (t : U64) (h : R (nextA l t)) :
    tcbqueue.next gS X l t = tcbqueue.next st X l t := by
  unfold tcbqueue.next
  cases l
  · exact PathObl.obj.Tcb.sched_next.guard (gS := gS) t X h
  · exact PathObl.obj.Tcb.ep_next.guard (gS := gS) t X h

theorem tcbqueue.set_prev.guardL (X : S) (l : tcbqueue.Link) (t v : U64) (h : W (prevA l t)) :
    tcbqueue.set_prev gS X l t v = tcbqueue.set_prev st X l t v := by
  unfold tcbqueue.set_prev
  cases l
  · exact PathObl.obj.Tcb.set_sched_prev.guard (gS := gS) t X v h
  · exact PathObl.obj.Tcb.set_ep_prev.guard (gS := gS) t X v h

theorem tcbqueue.set_next.guardL (X : S) (l : tcbqueue.Link) (t v : U64) (h : W (nextA l t)) :
    tcbqueue.set_next gS X l t v = tcbqueue.set_next st X l t v := by
  unfold tcbqueue.set_next
  cases l
  · exact PathObl.obj.Tcb.set_sched_next.guard (gS := gS) t X v h
  · exact PathObl.obj.Tcb.set_ep_next.guard (gS := gS) t X v h

/-- **`tcbqueue.remove`** of `t` from the queue `q` on the link `l`: `t`'s links (read, then cleared), the
successor's `prev` link unless `t` is the tail, the predecessor's `next` link unless `t` is the head. -/
theorem tcbqueue.remove.guardL (X : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t : U64)
    (r1 : R (prevA l t)) (r2 : R (nextA l t))
    (wPn : q.end ≠ t → W (prevA l (L.mem X (nextA l t))))
    (wNp : q.head ≠ t → W (nextA l (L.mem X (prevA l t))))
    (w1 : W (nextA l t)) (w2 : W (prevA l t)) :
    tcbqueue.remove gS X l q t = tcbqueue.remove st X l q t := by
  unfold tcbqueue.remove
  rw [tcbqueue.prev.guardL (gS := gS) X l t r1, tcbqueue.next.guardL (gS := gS) X l t r2]
  refine bind_guard_congr rfl fun i hi => ?_
  refine bind_guard_congr rfl fun i1 hi1 => ?_
  rw [eq_of_spec_fd (tcbqueue.prev.spec (L := L) X l t)] at hi
  rw [eq_of_spec_fd (tcbqueue.next.spec (L := L) X l t)] at hi1
  have ei : L.mem X (prevA l t) = i := ok_inj_ff hi
  have ei1 : L.mem X (nextA l t) = i1 := ok_inj_ff hi1
  subst ei ei1
  have eH : obj.Tcb.Insts.CoreCmpPartialEqTcb.eq q.head t = ok (decide (q.head = t)) :=
    eq_of_spec_fd (obj.Tcb.eq.spec _ _)
  have eE : obj.Tcb.Insts.CoreCmpPartialEqTcb.eq q.end t = ok (decide (q.end = t)) :=
    eq_of_spec_fd (obj.Tcb.eq.spec _ _)
  have g1 : ∀ (Y : S) (v : U64), tcbqueue.set_next gS Y l t v = tcbqueue.set_next st Y l t v :=
    fun Y v => tcbqueue.set_next.guardL (gS := gS) Y l t v w1
  have g2 : ∀ (Y : S) (v : U64), tcbqueue.set_prev gS Y l t v = tcbqueue.set_prev st Y l t v :=
    fun Y v => tcbqueue.set_prev.guardL (gS := gS) Y l t v w2
  by_cases hH : q.head = t
  · by_cases hE : q.end = t
    · simp only [eH, eE]
      simp only [hH, hE, eq_self_iff_true, decide_true, ↓reduceIte, bind_ok, g1, g2]
    · have g3 : ∀ (Y : S) (v : U64), tcbqueue.set_prev gS Y l (L.mem X (nextA l t)) v =
          tcbqueue.set_prev st Y l (L.mem X (nextA l t)) v :=
        fun Y v => tcbqueue.set_prev.guardL (gS := gS) Y l _ v (wPn hE)
      simp only [eH, eE]
      simp only [hH, hE, eq_self_iff_true, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok, g1, g2, g3]
  · have g4 : ∀ (Y : S) (v : U64), tcbqueue.set_next gS Y l (L.mem X (prevA l t)) v =
        tcbqueue.set_next st Y l (L.mem X (prevA l t)) v :=
      fun Y v => tcbqueue.set_next.guardL (gS := gS) Y l _ v (wNp hH)
    by_cases hE : q.end = t
    · simp only [eH, eE]
      simp only [hH, hE, eq_self_iff_true, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok, g1, g2, g4]
    · have g3 : ∀ (Y : S) (v : U64), tcbqueue.set_prev gS Y l (L.mem X (nextA l t)) v =
          tcbqueue.set_prev st Y l (L.mem X (nextA l t)) v :=
        fun Y v => tcbqueue.set_prev.guardL (gS := gS) Y l _ v (wPn hE)
      simp only [eH, eE]
      simp only [hH, hE, eq_self_iff_true, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok, g1, g2, g3, g4]

/-- **`tcbqueue.prepend`**: `t`'s links, and the old head's `prev` link when the queue is not empty. -/
theorem tcbqueue.prepend.guardL (X : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t : U64)
    (w1 : W (nextA l t)) (w2 : W (prevA l t)) (w3 : q.head ≠ 0#u64 → W (prevA l q.head)) :
    tcbqueue.prepend gS X l q t = tcbqueue.prepend st X l q t := by
  unfold tcbqueue.prepend tcbqueue.Queue.is_empty
  rw [is_null_ok]
  simp only [bind_ok]
  by_cases hq : q.head = 0#u64
  · rw [if_pos (by simp [hq]), if_pos (by simp [hq]), tcbqueue.set_next.guardL (gS := gS) X l t _ w1]
    refine bind_guard_congr rfl fun s1 _ => ?_
    rw [tcbqueue.set_prev.guardL (gS := gS) s1 l t _ w2]
  · rw [if_neg (by simpa using hq), if_neg (by simpa using hq), tcbqueue.set_next.guardL (gS := gS) X l t _ w1]
    refine bind_guard_congr rfl fun s1 _ => ?_
    rw [tcbqueue.set_prev.guardL (gS := gS) s1 l t _ w2]
    refine bind_guard_congr rfl fun s2 _ => ?_
    rw [tcbqueue.set_prev.guardL (gS := gS) s2 l _ _ (w3 hq)]

/-- **`tcbqueue.append`**: `t`'s links, and the old tail's `next` link when the queue is not empty. -/
theorem tcbqueue.append.guardL (X : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t : U64)
    (w1 : W (nextA l t)) (w2 : W (prevA l t)) (w3 : q.head ≠ 0#u64 → W (nextA l q.end)) :
    tcbqueue.append gS X l q t = tcbqueue.append st X l q t := by
  unfold tcbqueue.append tcbqueue.Queue.is_empty
  rw [is_null_ok]
  simp only [bind_ok]
  by_cases hq : q.head = 0#u64
  · rw [if_pos (by simp [hq]), if_pos (by simp [hq]), tcbqueue.set_next.guardL (gS := gS) X l t _ w1]
    refine bind_guard_congr rfl fun s1 _ => ?_
    rw [tcbqueue.set_prev.guardL (gS := gS) s1 l t _ w2]
  · rw [if_neg (by simpa using hq), if_neg (by simpa using hq), tcbqueue.set_next.guardL (gS := gS) X l _ _ (w3 hq)]
    refine bind_guard_congr rfl fun s1 _ => ?_
    rw [tcbqueue.set_prev.guardL (gS := gS) s1 l t _ w2]
    refine bind_guard_congr rfl fun s2 _ => ?_
    rw [tcbqueue.set_next.guardL (gS := gS) s2 l t _ w1]

theorem obj.Ntfn.state.guardQ (n : obj.Ntfn) (X : S)
    (h : R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE)) :
    obj.Ntfn.state gS n X = obj.Ntfn.state st n X := by
  unfold obj.Ntfn.state; rw [PathObl.obj.Ntfn.tail_state.guard (gS := gS) n X h]

theorem obj.Ep.state.guardQ (ep : obj.Ep) (X : S) (h : R (core.num.U64.wrapping_add ep layout.ep.TAIL_STATE)) :
    obj.Ep.state gS ep X = obj.Ep.state st ep X := by
  unfold obj.Ep.state; rw [PathObl.obj.Ep.tail_state.guard (gS := gS) ep X h]

theorem obj.Ep.tail.guardQ (ep : obj.Ep) (X : S) (h : R (core.num.U64.wrapping_add ep layout.ep.TAIL_STATE)) :
    obj.Ep.tail gS ep X = obj.Ep.tail st ep X := by
  unfold obj.Ep.tail; rw [PathObl.obj.Ep.tail_state.guard (gS := gS) ep X h]

theorem obj.Ep.set_queue.guardQ (ep : obj.Ep) (X : S) (hd tl stt : U64)
    (hH : W (core.num.U64.wrapping_add ep layout.ep.HEAD))
    (hT : W (core.num.U64.wrapping_add ep layout.ep.TAIL_STATE)) :
    obj.Ep.set_queue gS ep X hd tl stt = obj.Ep.set_queue st ep X hd tl stt := by
  unfold obj.Ep.set_queue
  rw [PathObl.obj.Ep.set_head.guard (gS := gS) ep X hd hH]
  refine bind_guard_congr rfl fun s1 _ => ?_
  simp only [lift, bind_ok]
  rw [PathObl.obj.Ep.set_tail_state.guard (gS := gS) ep s1 _ hT]

theorem obj.Ntfn.tail.guard (n : obj.Ntfn) (X : S) (h : R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE)) :
    obj.Ntfn.tail gS n X = obj.Ntfn.tail st n X := by
  unfold obj.Ntfn.tail; rw [PathObl.obj.Ntfn.tail_state.guard (gS := gS) n X h]

theorem notification.get_queue.guard (X : S) (n : obj.Ntfn)
    (h1 : R (core.num.U64.wrapping_add n layout.ntfn.HEAD))
    (h2 : R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE)) :
    notification.get_queue gS X n = notification.get_queue st X n := by
  unfold notification.get_queue
  rw [PathObl.obj.Ntfn.head.guard (gS := gS) n X h1, obj.Ntfn.tail.guard (gS := gS) n X h2]

theorem notification.set_queue.guard (X : S) (n : obj.Ntfn) (q : tcbqueue.Queue) (v : U64)
    (h1 : W (core.num.U64.wrapping_add n layout.ntfn.HEAD))
    (h2 : W (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE)) :
    notification.set_queue gS X n q v = notification.set_queue st X n q v := by
  simp only [notification.set_queue, obj.Ntfn.set_queue]
  rw [PathObl.obj.Ntfn.set_head.guard (gS := gS) n X _ h1]
  refine bind_guard_congr rfl fun s1 _ => ?_
  simp only [lift, bind_ok]
  rw [PathObl.obj.Ntfn.set_tail_state.guard (gS := gS) n s1 _ h2]

/-- **`ntfn_dequeue n t`**: the notification's queue words, then `tcbqueue.remove` on the `Ep` links. -/
theorem notification.ntfn_dequeue.guard (X : S) (n : obj.Ntfn) (t : U64)
    (h1 : R (core.num.U64.wrapping_add n layout.ntfn.HEAD))
    (h2 : R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (w1 : W (core.num.U64.wrapping_add n layout.ntfn.HEAD))
    (w2 : W (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (hrm : ∀ q, notification.get_queue st X n = ok q →
      tcbqueue.remove gS X tcbqueue.Link.Ep q t = tcbqueue.remove st X tcbqueue.Link.Ep q t) :
    notification.ntfn_dequeue gS X n t = notification.ntfn_dequeue st X n t := by
  unfold notification.ntfn_dequeue
  rw [obj.Ntfn.state.guardQ (gS := gS) n X h2]
  refine bind_guard_congr rfl fun v _ => ?_
  rw [notification.get_queue.guard (gS := gS) X n h1 h2]
  refine bind_guard_congr rfl fun q hq => ?_
  rw [hrm q hq]
  refine bind_guard_congr rfl fun x _ => ?_
  obtain ⟨q1, s1⟩ := x
  simp only [Aeneas.Std.uncurry_apply_pair]
  refine bind_guard_congr rfl fun b _ => ?_
  by_cases hb : b = true
  · rw [if_pos hb, if_pos hb]; exact notification.set_queue.guard (gS := gS) s1 n q1 _ w1 w2
  · rw [if_neg hb, if_neg hb]; exact notification.set_queue.guard (gS := gS) s1 n q1 _ w1 w2

theorem endpoint.get_queue.guard (X : S) (ep : obj.Ep)
    (h1 : R (core.num.U64.wrapping_add ep layout.ep.HEAD))
    (h2 : R (core.num.U64.wrapping_add ep layout.ep.TAIL_STATE)) :
    endpoint.get_queue gS X ep = endpoint.get_queue st X ep := by
  unfold endpoint.get_queue
  rw [PathObl.obj.Ep.head.guard (gS := gS) ep X h1, obj.Ep.tail.guardQ (gS := gS) ep X h2]

/-- **`ep_dequeue ep t`**: the endpoint's queue words, then `tcbqueue.remove` on the `Ep` links. -/
theorem endpoint.ep_dequeue.guard (X : S) (ep : obj.Ep) (t : U64)
    (h1 : R (core.num.U64.wrapping_add ep layout.ep.HEAD))
    (h2 : R (core.num.U64.wrapping_add ep layout.ep.TAIL_STATE))
    (w1 : W (core.num.U64.wrapping_add ep layout.ep.HEAD))
    (w2 : W (core.num.U64.wrapping_add ep layout.ep.TAIL_STATE))
    (hrm : ∀ q, endpoint.get_queue st X ep = ok q →
      tcbqueue.remove gS X tcbqueue.Link.Ep q t = tcbqueue.remove st X tcbqueue.Link.Ep q t) :
    endpoint.ep_dequeue gS X ep t = endpoint.ep_dequeue st X ep t := by
  unfold endpoint.ep_dequeue
  rw [endpoint.get_queue.guard (gS := gS) X ep h1 h2]
  refine bind_guard_congr rfl fun q hq => ?_
  rw [obj.Ep.state.guardQ (gS := gS) ep X h2]
  refine bind_guard_congr rfl fun v _ => ?_
  rw [hrm q hq]
  refine bind_guard_congr rfl fun x _ => ?_
  obtain ⟨q1, s1⟩ := x
  simp only [Aeneas.Std.uncurry_apply_pair]
  refine bind_guard_congr rfl fun b _ => ?_
  by_cases hb : b = true
  · rw [if_pos hb, if_pos hb]; simp only [endpoint.set_queue]; exact obj.Ep.set_queue.guardQ (gS := gS) ep s1 _ _ _ w1 w2
  · rw [if_neg hb, if_neg hb]; simp only [endpoint.set_queue]; exact obj.Ep.set_queue.guardQ (gS := gS) ep s1 _ _ _ w1 w2

end gst

end Fl4Proofs.P2
