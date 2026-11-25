/-
# P2: guarded-store lemmas for the tail of `switch_to`

For the per-path obligation of `P2/PathObl.lean`, stated at each callee's
entry state:

* `timer.earliest.guard`: the node's `TIMER_MIN` and the timer-min thread's
  deadline;
* `sched.set_next_interrupt.guard` (this branch's body, before main #99):
  the node's words (`CUR_TIME`, `CUR_THREAD`, `RELEASE_HEAD`, `TIMER_MIN`,
  `ARMED`, read; `ARMED`, written), the kernel's `DOMAIN_TIME`, the current
  thread's SC word and head refill, the release head's SC word and head
  refill, the timer-min thread's deadline;
* `sched.activate_thread.guard`, for a current thread that yields to no SC
  (`YIELD_TO = 0`, a hypothesis: `complete_yield_to` is not entered): the
  thread's `YIELD_TO`, state, `FAULT_IP` (read), `NEXT_IP`, state (written),
  and `set_thread_state`'s words (p2io's `AccessIo`).

Generic over the Arch instance (no Arch premise). No premises.
-/
import Fl4Proofs.P2.AccessSwitch
import Fl4Proofs.P2.AccessIo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W] [L : LawfulStore st]

theorem timer.earliest.guard (s : S) (htm : R (tmA (L := L) s))
    (htd : L.mem s (tmA (L := L) s) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64)) :
    timer.earliest gS s = timer.earliest st s := by
  unfold timer.earliest
  simp only [gst_cur_cpu, L.cur_cpu_eq, bind_ok]
  rw [obj.node_get.guard s _ _ htm, node_get_ok s _ layout.node.TIMER_MIN]
  simp only [bind_ok, is_null_ok]
  by_cases h0 : L.mem s (tmA (L := L) s) = 0#u64
  · simp only [h0, decide_true, ↓reduceIte]
  · rw [obj.Tcb.timer_deadline.guard _ s (htd h0)]

/-- **`set_next_interrupt`** (module docstring). -/
theorem sched.set_next_interrupt.guard {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeA s o) ∧ W (L.nodeA s o))
    (hdt : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hsc : R (scA (L.curW s))) (hhd : RdHead (L := L) R s (L.mem s (scA (L.curW s))))
    (hrs : L.mem s (rhA (L := L) s) ≠ 0#u64 → R (scA (L.mem s (rhA (L := L) s))) ∧
      RdHead (L := L) R s (L.mem s (scA (L.mem s (rhA (L := L) s)))))
    (htd : L.mem s (tmA (L := L) s) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64)) :
    sched.set_next_interrupt gS ar s a = sched.set_next_interrupt st ar s a := by
  unfold sched.set_next_interrupt
  rw [sched.cur_time.guard s (hNd layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1,
    sched.cur_thread.guard s (hNd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1, cur_thread_ok]
  simp only [bind_ok]
  rw [obj.Tcb.sc.guard _ s hsc, tcb_sc_ok]
  simp only [bind_ok]
  rw [sporadic.head.guard s _ hhd, sched.domain_time.guard s hdt,
    timer.earliest.guard s (hNd layout.node.TIMER_MIN (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1 htd]
  simp only [gst_cur_cpu, L.cur_cpu_eq, bind_ok]
  rw [obj.node_get.guard s _ layout.node.RELEASE_HEAD (hNd layout.node.RELEASE_HEAD (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])).1,
    obj.node_get.guard s _ layout.node.ARMED (hNd layout.node.ARMED (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED])).1,
    node_get_ok s _ layout.node.RELEASE_HEAD]
  simp only [bind_ok, is_null_ok,
    obj.node_set.guard s (L.cpu s) layout.node.ARMED _ (hNd layout.node.ARMED (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED])).2]
  by_cases h1 : L.mem s (rhA (L := L) s) = 0#u64
  · simp only [h1, decide_true, ↓reduceIte]
  · obtain ⟨hs1, hs2⟩ := hrs h1
    unfold sched.ready_time
    rw [obj.Tcb.sc.guard _ s hs1, tcb_sc_ok s (L.mem s (rhA (L := L) s))]
    simp only [bind_ok]
    rw [sporadic.head.guard s _ hs2]

/-- **`activate_thread`** of a current thread `t` that yields to no SC. -/
theorem sched.activate_thread.guardV {A : Type} (ar : machine.Arch A) (s : S) (a : A) {t : U64}
    (hcur : L.curW s = t) (hT : TcbAddr t) (hy0 : L.mem s (yieldA t) = 0#u64) (hn : NodeSt (L := L) R W s)
    (hyt : R (yieldA t)) (hst : R (stA t)) (hrg : R (regA t layout.reg.FAULT_IP))
    (hwr : W (regA t layout.reg.NEXT_IP)) (hw : SWr gS st t sched.TS_RUNNING) (h2 : R (scA t))
    (h3 : R (maxA (L.mem s (scA t)))) (h4 : R (inqA t)) :
    sched.activate_thread gS ar s a = sched.activate_thread st ar s a := by
  unfold sched.activate_thread
  rw [sched.cur_thread.guard s hn.1, cur_thread_ok, hcur]
  simp only [bind_ok]
  rw [obj.Tcb.yield_to.guard t s hyt, eq_ok_of_spec (obj.Tcb.yield_to.spec s t), hy0]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Aeneas.Std.uncurry_apply_pair]
  rw [obj.Tcb.state.guard t s hst]
  refine bind_guard_congr rfl fun v _ => ?_
  split
  · rw [obj.Tcb.reg.guard t s _ hrg]
    refine bind_guard_congr rfl fun pc _ => ?_
    rw [obj.Tcb.set_reg.guard t s _ _ hwr, set_reg_ok' s t layout.reg.NEXT_IP pc]
    simp only [bind_ok]
    rw [sched.set_thread_state.guardV _ t _ hn.wr hw hst h2 (by
      rw [st_wr_sc hT, reg_wr_sc hT (by simp [layout.reg.NEXT_IP])]; exact h3) h4]
  · rfl

theorem sched.activate_thread.guard {A : Type} (ar : machine.Arch A) (s : S) (a : A) {t : U64}
    (hcur : L.curW s = t) (hT : TcbAddr t) (hy0 : L.mem s (yieldA t) = 0#u64) (hn : NodeSt (L := L) R W s)
    (hyt : R (yieldA t)) (hst : R (stA t)) (hrg : R (regA t layout.reg.FAULT_IP))
    (hwr : W (regA t layout.reg.NEXT_IP)) (hw : W (stA t)) (h2 : R (scA t))
    (h3 : R (maxA (L.mem s (scA t)))) (h4 : R (inqA t)) :
    sched.activate_thread gS ar s a = sched.activate_thread st ar s a :=
  sched.activate_thread.guardV ar s a hcur hT hy0 hn hyt hst hrg hwr (SWr.of_W hw) h2 h3 h4

end

end Fl4Proofs.P2.PathObl
