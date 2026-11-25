/-
# P2 (p2lf): a fired timer's `send_signal`, on the guarded store

`send_signal` of the notification `n` with badge `badge`, in the branches `fire_ok` accepts, on any store `gS`
answering `R` reads and `W` writes as `st`:

* branch equations on any store (`send_signal_act`, `send_signal_idle0`, `send_signal_bnr`, `send_signal_recv`,
  `send_signal_wait`): an active (or any non-idle, non-waiting) notification ORs the badge in; an idle one with no
  bound thread, or a bound thread neither in `Recv` nor running a VM, is made active; an idle one whose bound thread
  waits in `Recv` runs `cancel_ipc` and `wakeTail`; a waiting one dequeues its head and runs `wakeTail`;
* `notification.set_active.guard`, and `notification.send_signal.guardF`: the guarded run is the real one given the
  notification's words and, per branch, the guarded `cancel_ipc` / `ntfn_dequeue` and `wakeTail` (premises at the
  real intermediate states).

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (bind_guard_congr)

section eqs
variable {S : Type _} {A : Type _} (M : machine.Store S) (ar : machine.Arch A) (X : S) (a : A) (n badge : U64)

theorem send_signal_act {v : U64} (h1 : obj.Ntfn.state M n X = ok v) (h2 : v ≠ obj.NTFN_IDLE)
    (h3 : v ≠ obj.NTFN_WAITING) :
    notification.send_signal M ar X a n badge = (do
      let i ← obj.Ntfn.badge M n X
      let s1 ← obj.Ntfn.set_badge M n X (i ||| badge)
      ok (s1, a)) := by
  unfold notification.send_signal
  rw [h1]
  simp only [bind_ok, if_neg h2, if_neg h3, lift]

theorem send_signal_idle0 (h1 : obj.Ntfn.state M n X = ok obj.NTFN_IDLE)
    (h2 : obj.Ntfn.bound_tcb M n X = ok 0#u64) :
    notification.send_signal M ar X a n badge = (do
      let s1 ← notification.set_active M X n badge
      ok (s1, a)) := by
  unfold notification.send_signal
  rw [h1, h2]
  simp only [bind_ok, is_null_ok, eq_self_iff_true, if_true, decide_true, ↓reduceIte]

theorem send_signal_bnr {b v : U64} (h1 : obj.Ntfn.state M n X = ok obj.NTFN_IDLE)
    (h2 : obj.Ntfn.bound_tcb M n X = ok b) (hb : b ≠ 0#u64) (h3 : obj.Tcb.state M b X = ok v)
    (hv1 : v ≠ sched.TS_BLOCKED_ON_RECV) (hv2 : v ≠ sched.TS_RUNNING_VM) :
    notification.send_signal M ar X a n badge = (do
      let s1 ← notification.set_active M X n badge
      let i2 ← obj.Tcb.state M b s1
      if i2 = sched.TS_RUNNING_VM then notification.kick_guest M ar s1 a b else ok (s1, a)) := by
  unfold notification.send_signal
  rw [h1, h2]
  simp only [bind_ok, is_null_ok, eq_self_iff_true, if_true, hb, decide_false, Bool.false_eq_true, h3,
    if_neg hv1, if_neg hv2, ↓reduceIte]

theorem send_signal_recv {b : U64} (h1 : obj.Ntfn.state M n X = ok obj.NTFN_IDLE)
    (h2 : obj.Ntfn.bound_tcb M n X = ok b) (hb : b ≠ 0#u64) (h3 : obj.Tcb.state M b X = ok sched.TS_BLOCKED_ON_RECV) :
    notification.send_signal M ar X a n badge = (do
      let (s1, a1) ← ipc.cancel_ipc M ar X a b
      wakeTail M ar s1 a1 b n badge) := by
  unfold notification.send_signal
  rw [h1, h2]
  simp only [bind_ok, is_null_ok, eq_self_iff_true, if_true, hb, decide_false, Bool.false_eq_true, h3,
    ↓reduceIte]
  rfl

theorem send_signal_wait (h1 : obj.Ntfn.state M n X = ok obj.NTFN_WAITING) :
    notification.send_signal M ar X a n badge = (do
      let q ← notification.get_queue M X n
      let s1 ← notification.ntfn_dequeue M X n q.head
      wakeTail M ar s1 a q.head n badge) := by
  unfold notification.send_signal
  rw [h1]
  have : obj.NTFN_WAITING ≠ obj.NTFN_IDLE := by unfold obj.NTFN_WAITING obj.NTFN_IDLE; decide
  simp only [bind_ok, if_neg this, eq_self_iff_true, if_true, ↓reduceIte]
  rfl

end eqs

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- **`set_active`**: the notification's `TAIL_STATE` (read, written) and `BADGE` (written). -/
theorem notification.set_active.guard (X : S) (n badge : U64)
    (r1 : R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (w1 : W (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (w2 : W (core.num.U64.wrapping_add n layout.ntfn.BADGE)) :
    notification.set_active gS X n badge = notification.set_active st X n badge := by
  have e1 : obj.Ntfn.set_state gS n X obj.NTFN_ACTIVE = obj.Ntfn.set_state st n X obj.NTFN_ACTIVE := by
    unfold obj.Ntfn.set_state
    rw [obj.Ntfn.tail.guard (gS := gS) n X r1]
    refine bind_guard_congr rfl fun t _ => ?_
    simp only [lift, bind_ok]
    rw [PathObl.obj.Ntfn.set_tail_state.guard (gS := gS) n X _ w1]
  unfold notification.set_active
  rw [e1]
  refine bind_guard_congr rfl fun s1 _ => ?_
  exact PathObl.obj.Ntfn.set_badge.guard (gS := gS) n s1 _ w2

/-- The notification words `set_active` writes. -/
def SaD (n w : U64) : Prop := w = epTSA n ∨ w = ntfnBdA n

/-- **A fired timer's `send_signal` on the guarded store** (module docstring): per the notification's state at
`X`, the words read and written, and the guarded sub-runs at the real states. -/
theorem notification.send_signal.guardF {A : Type} (ar : machine.Arch A) (X : S) (a : A) (n badge : U64)
    (r1 : R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE)) (aT : Aligned (epTSA n))
    (aB : Aligned (ntfnBdA n))
    (hO : L.epState X n ≠ obj.NTFN_IDLE → L.epState X n ≠ obj.NTFN_WAITING →
      R (core.num.U64.wrapping_add n layout.ntfn.BADGE) ∧ W (core.num.U64.wrapping_add n layout.ntfn.BADGE))
    (hI : L.epState X n = obj.NTFN_IDLE →
      R (core.num.U64.wrapping_add n layout.ntfn.BOUND_TCB) ∧
      (L.mem X (ntfnBtA n) = 0#u64 ∨ L.mem X (stA (L.mem X (ntfnBtA n))) ≠ sched.TS_BLOCKED_ON_RECV →
        W (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) ∧ W (core.num.U64.wrapping_add n layout.ntfn.BADGE)) ∧
      (L.mem X (ntfnBtA n) ≠ 0#u64 →
        R (stA (L.mem X (ntfnBtA n))) ∧ L.mem X (stA (L.mem X (ntfnBtA n))) ≠ sched.TS_RUNNING_VM ∧
        (L.mem X (stA (L.mem X (ntfnBtA n))) ≠ sched.TS_BLOCKED_ON_RECV →
          ∀ Y, WritesIn st X Y (SaD n) → L.mem Y (stA (L.mem X (ntfnBtA n))) ≠ sched.TS_RUNNING_VM) ∧
        (L.mem X (stA (L.mem X (ntfnBtA n))) = sched.TS_BLOCKED_ON_RECV →
          ipc.cancel_ipc gS ar X a (L.mem X (ntfnBtA n)) = ipc.cancel_ipc st ar X a (L.mem X (ntfnBtA n)) ∧
          ∀ X1 a1, ipc.cancel_ipc st ar X a (L.mem X (ntfnBtA n)) = ok (X1, a1) →
            wakeTail gS ar X1 a1 (L.mem X (ntfnBtA n)) n badge =
              wakeTail st ar X1 a1 (L.mem X (ntfnBtA n)) n badge)))
    (hW : L.epState X n = obj.NTFN_WAITING →
      R (core.num.U64.wrapping_add n layout.ntfn.HEAD) ∧
      notification.ntfn_dequeue gS X n (L.epQ X n).head = notification.ntfn_dequeue st X n (L.epQ X n).head ∧
      ∀ X1, notification.ntfn_dequeue st X n (L.epQ X n).head = ok X1 →
        wakeTail gS ar X1 a (L.epQ X n).head n badge = wakeTail st ar X1 a (L.epQ X n).head n badge) :
    notification.send_signal gS ar X a n badge = notification.send_signal st ar X a n badge := by
  have eS : obj.Ntfn.state st n X = ok (L.epState X n) := eq_of_spec_fd (obj.Ntfn.state.spec (L := L) X n)
  have eSg : obj.Ntfn.state gS n X = ok (L.epState X n) := by rw [obj.Ntfn.state.guardQ (gS := gS) n X r1, eS]
  by_cases hi : L.epState X n = obj.NTFN_IDLE
  · obtain ⟨rB, hSA, hB⟩ := hI hi
    rw [hi] at eS eSg
    have eB : obj.Ntfn.bound_tcb st n X = ok (L.mem X (ntfnBtA n)) := eq_of_spec_fd (obj.Ntfn.bound_tcb.val (L := L) X n)
    have eBg : obj.Ntfn.bound_tcb gS n X = ok (L.mem X (ntfnBtA n)) := by
      rw [PathObl.obj.Ntfn.bound_tcb.guard (gS := gS) n X rB, eB]
    by_cases h0 : L.mem X (ntfnBtA n) = 0#u64
    · rw [h0] at eB eBg
      rw [send_signal_idle0 gS ar X a n badge eSg eBg, send_signal_idle0 st ar X a n badge eS eB]
      obtain ⟨w1, w2⟩ := hSA (Or.inl h0)
      rw [notification.set_active.guard (gS := gS) X n badge r1 w1 w2]
    obtain ⟨rS, hnv, hbn, hrc⟩ := hB h0
    have eT : obj.Tcb.state st (L.mem X (ntfnBtA n)) X = ok (L.mem X (stA (L.mem X (ntfnBtA n)))) :=
      eq_of_spec_fd (obj.Tcb.state.spec (L := L) X _)
    have eTg : obj.Tcb.state gS (L.mem X (ntfnBtA n)) X = ok (L.mem X (stA (L.mem X (ntfnBtA n)))) := by
      rw [PathObl.obj.Tcb.state.guard (gS := gS) _ X rS, eT]
    by_cases hr : L.mem X (stA (L.mem X (ntfnBtA n))) = sched.TS_BLOCKED_ON_RECV
    · rw [hr] at eT eTg
      rw [send_signal_recv gS ar X a n badge eSg eBg h0 eTg, send_signal_recv st ar X a n badge eS eB h0 eT]
      obtain ⟨hc1, hc2⟩ := hrc hr
      rw [hc1]
      refine bind_guard_congr rfl fun x hx => ?_
      obtain ⟨X1, a1⟩ := x
      exact hc2 X1 a1 hx
    · rw [send_signal_bnr gS ar X a n badge eSg eBg h0 eTg hr hnv,
        send_signal_bnr st ar X a n badge eS eB h0 eT hr hnv]
      obtain ⟨w1, w2⟩ := hSA (Or.inr hr)
      rw [notification.set_active.guard (gS := gS) X n badge r1 w1 w2]
      refine bind_guard_congr rfl fun s1 hs1 => ?_
      have wi : WritesIn st X s1 (SaD n) := by
        unfold notification.set_active at hs1
        rw [eq_of_spec_fd (obj.Ntfn.set_state.val (L := L) X n _)] at hs1
        simp only [bind_ok] at hs1
        rw [eq_of_spec_fd (obj.Ntfn.set_badge.wr (L := L) _ n badge)] at hs1
        rw [← ok_inj_ff hs1]
        refine ⟨by rw [L.ksb_wr, L.ksb_wr], by rw [L.cpu_wr, L.cpu_wr], fun c hc hc' => ?_⟩
        rw [mem_wr_ne' aB hc (fun e => hc' (Or.inr e.symm)), mem_wr_ne' aT hc (fun e => hc' (Or.inl e.symm))]
      rw [PathObl.obj.Tcb.state.guard (gS := gS) _ s1 rS]
      refine bind_guard_congr rfl fun v hv => ?_
      rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s1 _)] at hv
      rw [← ok_inj_ff hv, if_neg (hbn hr s1 wi), if_neg (hbn hr s1 wi)]
  · by_cases hw : L.epState X n = obj.NTFN_WAITING
    · obtain ⟨rH, hd, hwt⟩ := hW hw
      rw [hw] at eS eSg
      rw [send_signal_wait gS ar X a n badge eSg, send_signal_wait st ar X a n badge eS,
        notification.get_queue.guard (gS := gS) X n rH r1]
      refine bind_guard_congr rfl fun q hq => ?_
      rw [eq_of_spec_fd (notification.get_queue.spec (L := L) X n)] at hq
      have e := ok_inj_ff hq
      subst e
      rw [hd]
      exact bind_guard_congr rfl fun X1 h1 => hwt X1 h1
    · obtain ⟨rBd, wBd⟩ := hO hi hw
      rw [send_signal_act gS ar X a n badge eSg hi hw, send_signal_act st ar X a n badge eS hi hw,
        PathObl.obj.Ntfn.badge.guard (gS := gS) n X rBd]
      refine bind_guard_congr rfl fun i _ => ?_
      rw [PathObl.obj.Ntfn.set_badge.guard (gS := gS) n X _ wBd]

end gst

end Fl4Proofs.P2
