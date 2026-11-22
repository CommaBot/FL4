/-
# The ReplyRecv meeting point (FL4 #56, m65 (R-a))

The general path's `dispatch_syscall … SysReplyRecv` from the dispatch state
`X0` (where `fastpath.reply_recv` is entered) makes exactly the fast path's
writes, in the fast path's order (KENTRY-PLAN m64's trace), and ends in the
fast path's state `X15` just before `switch_to u`. Stated over the fast run's
intermediate states `X1 … X15` (the binds of `rrTail`) and, for every read the
general path makes there, its value (`RRReads`): the decode / reply / receive
side is then pure rewriting.

* `do_reply_transfer_rr`: `do_reply_transfer` on the reply object, from `X1`
  (after `t`'s Restart) to `X7` (after `set_action u`);
* `handle_invocation_rr`: `handle_invocation` on the `REPLY` cptr, from `X0`
  to `X8` (after `t`'s Running);
* `ep_append_empty`, `handle_recv_rr`: `handle_recv` from `X8` to `X15`
  (`wait_for_sender` on the idle endpoint, `ep_append` = the fast path's two
  link writes and the queue write);
* **`rr_sync`**: `dispatch_syscall X0 SysReplyRecv = ok (X15, a2)`.

The reads are each a frame fact through the writes before them (KENTRY-PLAN
m64 R1–R7); `RRReads` names them one by one so that their derivation from
entry-state facts (the handoff) is per word.
-/
import Fl4Proofs.P1.FastRRSum
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} (st : machine.Store S) (ar : machine.Arch A)

theorem ite_ok_rr {α : Type _} {c : Prop} [Decidable c] (x y : α) :
    (if c then (ok x : Result α) else ok y) = ok (if c then x else y) := by
  split <;> rfl

theorem bne_self_rr (x : U64) : (x != x) = false := by simp

/-- With no extra caps announced, `lookup_extra_caps` returns `NO_EXTRA_CAPS`
whatever the buffer. -/
theorem lookup_extra_caps_zero (s : S) (t : obj.Tcb) (buf : U64) (info : msginfo.MessageInfo)
    (h : info.extra_caps = 0#u64) :
    ipc.lookup_extra_caps st s t buf info = ok (core.result.Result.Ok ipc.NO_EXTRA_CAPS) := by
  unfold ipc.lookup_extra_caps
  split
  · rfl
  · unfold ipc.lookup_extra_caps_loop
    rw [loop]
    unfold ipc.lookup_extra_caps_loop.body
    have h0 : ¬ ((0#u64 : U64) < 0#u64) := by scalar_tac
    simp only [h, h0, ↓reduceIte, bind_ok, bind_tc_ok]

theorem after_invocation_ok (s : S) (a : A) :
    syscall.after_invocation st ar s a (core.result.Result.Ok ()) = ok (true, s, a) := rfl

theorem unknown_ne_null : ¬ (fl4_abi.consts.fault.UnknownSyscall = fl4_abi.consts.fault.NullFault) := by
  unfold fl4_abi.consts.fault.UnknownSyscall fl4_abi.consts.fault.NullFault; decide

/-- **`do_reply_transfer` on the accepted ReplyRecv run** (from `X1`, after
`t`'s Restart, to `X7`, after the action write): the fast path's
`reply_remove`, `unblock_check` branch, `handle_fault_reply` (restart),
`clear_fault`, `u`'s Restart, and `possible_switch_to u` = `set_action u`. -/
theorem do_reply_transfer_rr {X1 X2 X3 X4 X5 X6 X7 : S} {a a1 a2 : A} {t u rptr usc : U64} {g b9 : Bool}
    (hrt : obj.Reply.tcb st rptr X1 = ok u) (hun : obj.Tcb.is_null u = ok false)
    (hus : obj.Tcb.state st u X1 = ok sched.TS_BLOCKED_ON_REPLY)
    (h2 : ipc.reply_remove st ar X1 a rptr u = ok (X2, a1))
    (hsc2 : obj.Tcb.sc st u X2 = ok usc)
    (h3s : sporadic.sc_sporadic st X2 usc = ok b9)
    (h3 : (if b9 then do
        let i13 ← obj.Sc.cpu st usc X2
        let i14 ← obj.node_get st X2 i13 layout.node.CUR_SC
        if usc != i14 then sporadic.unblock_check st X2 usc else ok X2
      else ok X2) = ok X3)
    (hft : obj.Tcb.fault_type st u X3 = ok fl4_abi.consts.fault.UnknownSyscall)
    (h4 : faults.handle_fault_reply st ar X3 a1 u t = ok (true, X4, a2))
    (h5 : faults.clear_fault st X4 u = ok X5)
    (h6 : obj.Tcb.set_state st u X5 sched.TS_RESTART = ok X6)
    (hsch6 : sched.schedule_tcb st X6 u = ok X6)
    (hsc6 : obj.Tcb.sc st u X6 = ok usc) (husc : obj.Sc.is_null usc = ok false)
    (hrun6 : sched.is_runnable st X6 u = ok true)
    (hrdy6 : sporadic.ready st X6 usc = ok true)
    (hsuf6 : sporadic.sufficient st ar X6 a2 usc 0#u64 = ok true)
    (hpst : sched.possible_switch_to st X6 u = ok X7) :
    ipc.do_reply_transfer st ar X1 a t rptr g = ok (X7, a2) := by
  unfold ipc.do_reply_transfer
  simp only [hrt, hun, hus, bind_ok, Bool.false_eq_true, ↓reduceIte, bne_self_rr]
  rw [h2]; simp only [bind_ok, uncurry_apply_pair]
  rw [hsc2]; simp only [bind_ok]
  rw [h3s]; simp only [bind_ok]
  rw [h3]; simp only [bind_ok]
  rw [hft]; simp only [bind_ok, unknown_ne_null, ↓reduceIte]
  rw [h4]; simp only [bind_ok, uncurry_apply_pair]
  rw [h5]; simp only [bind_ok, ↓reduceIte]
  unfold sched.set_thread_state
  rw [h6]; simp only [bind_ok]
  rw [hsch6]; simp only [bind_ok, uncurry_apply_pair]
  rw [hsc6]; simp only [bind_ok]
  rw [husc]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  rw [hrun6]; simp only [bind_ok, ↓reduceIte]
  rw [hrdy6]; simp only [bind_ok, ↓reduceIte]
  rw [hsuf6]; simp only [bind_ok, ↓reduceIte]
  rw [hpst]; simp only [bind_ok]

/-- **`handle_invocation` on the accepted ReplyRecv run** (the `REPLY` cptr,
not a call, not blocking, first phase), from `X0` to `X8`: the lookup the fast
path's `reply_caps` made, no extra caps, the Reply decode (`t` Restart with a
no-op `schedule_tcb`, `do_reply_transfer`), then `t` Running with a no-op
`schedule_tcb`. -/
theorem handle_invocation_rr {X0 X1 X7 X8 : S} {a a2 : A} {t rptr cptr buf : U64} {g : Bool}
    {info : msginfo.MessageInfo} {found : cspace.Resolved}
    (hct : sched.cur_thread st X0 = ok t) (hmi : msg.msg_info st X0 t = ok info)
    (hex : info.extra_caps = 0#u64)
    (hls : cspace.lookup_slot st X0 t cptr = ok (core.result.Result.Ok found))
    (hcap : obj.Slot.cap st found.slot X0 = ok (capability.Cap.Reply rptr g))
    (hbuf : msg.lookup_ipc_buffer st X0 false t = ok buf)
    (h1 : obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1)
    (hsch1 : sched.schedule_tcb st X1 t = ok X1)
    (hdrt : ipc.do_reply_transfer st ar X1 a t rptr g = ok (X7, a2))
    (hst7 : obj.Tcb.state st t X7 = ok sched.TS_RESTART)
    (h8 : obj.Tcb.set_state st t X7 sched.TS_RUNNING = ok X8)
    (hsch8 : sched.schedule_tcb st X8 t = ok X8) :
    syscall.handle_invocation st ar X0 a false false true true cptr =
      ok (core.result.Result.Ok (), X8, a2) := by
  unfold syscall.handle_invocation
  rw [hct]; simp only [bind_ok]
  rw [hmi]; simp only [bind_ok]
  rw [hls]; simp only [bind_ok]
  rw [hcap]; simp only [bind_ok]
  rw [hbuf]; simp only [bind_ok]
  rw [lookup_extra_caps_zero st X0 t buf info hex]; simp only [bind_ok]
  simp only [ite_ok_rr, bind_ok]
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  unfold sched.set_thread_state
  rw [h1]; simp only [bind_ok]
  rw [hsch1]; simp only [bind_ok]
  rw [hdrt]; simp only [bind_ok, uncurry_apply_pair]
  rw [hst7]; simp only [bind_ok, ↓reduceIte, Bool.false_eq_true]
  rw [h8]; simp only [bind_ok]
  rw [hsch8]; simp only [bind_ok]

/-- `ep_append` on an empty endpoint queue: the receiver's two link words and
the queue word (the fast path's `set_ep_next 0`, `set_ep_prev 0`,
`Ep.set_queue t t`). -/
theorem ep_append_empty {X12 X13 X14 X15 : S} {ep t state : U64} {q : tcbqueue.Queue}
    (hq : endpoint.get_queue st X12 ep = ok q) (hq0 : q.head = 0#u64)
    (hpr : ∃ p, obj.Tcb.prio st t X12 = ok p)
    (h13 : obj.Tcb.set_ep_next st t X12 0#u64 = ok X13)
    (h14 : obj.Tcb.set_ep_prev st t X13 0#u64 = ok X14)
    (h15 : obj.Ep.set_queue st ep X14 t t state = ok X15) :
    endpoint.ep_append st X12 ep t state = ok X15 := by
  obtain ⟨p, hp⟩ := hpr
  unfold endpoint.ep_append
  rw [hq]; simp only [bind_ok]
  unfold tcbqueue.append_by_prio
  rw [hp]; simp only [bind_ok]
  unfold tcbqueue.Queue.is_empty obj.Tcb.is_null
  simp only [hq0, decide_true, bind_ok, ↓reduceIte]
  unfold tcbqueue.prepend tcbqueue.Queue.is_empty obj.Tcb.is_null
  simp only [hq0, decide_true, bind_ok, ↓reduceIte]
  unfold tcbqueue.set_next tcbqueue.set_prev
  rw [h13]; simp only [bind_ok]
  rw [h14]; simp only [bind_ok, uncurry_apply_pair]
  unfold endpoint.set_queue
  exact h15

/-- **`handle_recv` on the accepted ReplyRecv run** (blocking, with a reply),
from `X8` to `X15`: the two cap lookups again, `take_reply` with the reply
object free, the bound notification as the fast path checked it, the idle
endpoint ⇒ `wait_for_sender` (`schedule_tcb` a no-op, the reply's TCB word,
`ep_append` on the empty queue). -/
theorem handle_recv_rr {X8 X9 X10 X11 X12 X15 : S} {a : A} {t rptr ep i i1 n : U64}
    {b0 : U64} {g b1 b3 b4 : Bool}
    (hct : sched.cur_thread st X8 = ok t)
    (hcap : obj.Tcb.reg st t X8 layout.reg.CAP = ok i1)
    (hlk1 : cspace.lookup_cap st X8 t i1 =
      ok (core.result.Result.Ok (capability.Cap.Endpoint ep b0 b1 true b3 b4)))
    (hrep : obj.Tcb.reg st t X8 layout.reg.REPLY = ok i)
    (hlk2 : cspace.lookup_cap st X8 t i = ok (core.result.Result.Ok (capability.Cap.Reply rptr g)))
    (hrt : obj.Reply.tcb st rptr X8 = ok 0#u64)
    (hbn : obj.Tcb.bound_ntfn st t X8 = ok n)
    (hnc : n = 0#u64 ∨ (n ≠ 0#u64 ∧ ∃ i7, obj.Ntfn.state st n X8 = ok i7 ∧ ¬ i7 = obj.NTFN_ACTIVE ∧
      notification.maybe_return_sched_context st X8 n t = ok X8))
    (hep : obj.Ep.state st ep X8 = ok obj.EP_IDLE)
    (h9 : obj.Tcb.set_state st t X8 sched.TS_BLOCKED_ON_RECV = ok X9)
    (h10 : obj.Tcb.set_block_obj st t X9 ep = ok X10)
    (h11 : obj.Tcb.set_reply_obj st t X10 rptr = ok X11)
    (hsch11 : sched.schedule_tcb st X11 t = ok X11)
    (hr0 : rptr ≠ 0#u64)
    (h12 : obj.Reply.set_tcb st rptr X11 t = ok X12)
    (h15 : endpoint.ep_append st X12 ep t obj.EP_RECV = ok X15) :
    syscall.handle_recv st ar X8 a true true = ok (X15, a) := by
  unfold syscall.handle_recv
  rw [hct]; simp only [bind_ok]
  rw [hcap]; simp only [bind_ok]
  rw [hlk1]; simp only [bind_ok, ↓reduceIte]
  rw [hrep]; simp only [bind_ok]
  rw [hlk2]; simp only [bind_ok]
  unfold endpoint.receive_ipc capability.Cap.ptr endpoint.take_reply
  simp only [bind_ok]
  rw [hrt]; simp only [obj.Tcb.is_null, decide_true, bind_ok, ↓reduceIte, uncurry_apply_pair]
  rw [hbn]; simp only [bind_ok]
  have hw : endpoint.wait_for_sender st X8 t ep true rptr = ok X15 := by
    unfold endpoint.wait_for_sender
    simp only [↓reduceIte]
    rw [h9]; simp only [bind_ok]
    rw [h10]; simp only [bind_ok]
    rw [h11]; simp only [bind_ok]
    rw [hsch11]; simp only [bind_ok, hr0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte]
    rw [h12]; simp only [bind_ok, uncurry_apply_pair]
    exact h15
  rcases hnc with rfl | ⟨hn0, i7, h7, hna, hmr⟩
  · simp only [bne_self_rr, Bool.false_eq_true, ↓reduceIte, bind_ok, uncurry_apply_pair]
    rw [hep]; simp only [bind_ok, ↓reduceIte]
    rw [hw]; simp only [bind_ok]
  · have hn : (n != 0#u64) = true := by simpa using hn0
    simp only [hn, ↓reduceIte]
    rw [h7]; simp only [bind_ok, hna, ↓reduceIte]
    rw [hmr]; simp only [bind_ok, uncurry_apply_pair]
    rw [hep]; simp only [bind_ok, ↓reduceIte]
    rw [hw]; simp only [bind_ok]

/-- **The meeting point, as a composition**: the general path's
`dispatch_syscall … SysReplyRecv` from `X0` is `handle_invocation` to `X8`
then `handle_recv` to `X15` (`after_invocation (Ok ())` = continue). -/
theorem rr_sync_of {X0 X8 X15 : S} {a a2 : A} {t i i1 : U64}
    (hct : sched.cur_thread st X0 = ok t)
    (hcap : obj.Tcb.reg st t X0 layout.reg.CAP = ok i1)
    (hrep : obj.Tcb.reg st t X0 layout.reg.REPLY = ok i)
    (hinv : syscall.handle_invocation st ar X0 a false false true true i =
      ok (core.result.Result.Ok (), X8, a2))
    (hrecv : syscall.handle_recv st ar X8 a2 true true = ok (X15, a2)) :
    syscall.dispatch_syscall st ar X0 a fl4_abi.syscall.SysReplyRecv = ok (X15, a2) := by
  rw [dispatch_rr]
  rw [hct]; simp only [bind_ok]
  rw [hcap]; simp only [bind_ok]
  rw [hrep]; simp only [bind_ok]
  rw [hinv]; simp only [bind_ok, uncurry_apply_pair]
  rw [after_invocation_ok]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte]
  exact hrecv

/-- **The accepted run's write part, step by step** (`rrTail` split into its
binds; the restart flag still a variable, `hfr_us` fixes it). -/
theorem rrTail_split {s s' : S} {a a' : A} {t rptr ep u usc : U64}
    (h : rrTail st ar s a t rptr ep u usc = ok (true, s', a')) :
    ∃ X1 X2 a1 b9 X3 restart X4 a2 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15,
      obj.Tcb.set_state st t s sched.TS_RESTART = ok X1 ∧
      ipc.reply_remove st ar X1 a rptr u = ok (X2, a1) ∧
      sporadic.sc_sporadic st X2 usc = ok b9 ∧
      (if b9 then do
        let i13 ← obj.Sc.cpu st usc X2
        let i14 ← obj.node_get st X2 i13 layout.node.CUR_SC
        if usc != i14 then sporadic.unblock_check st X2 usc else ok X2
      else ok X2) = ok X3 ∧
      faults.handle_fault_reply st ar X3 a1 u t = ok (restart, X4, a2) ∧
      faults.clear_fault st X4 u = ok X5 ∧
      obj.Tcb.set_state st u X5 (if restart then sched.TS_RESTART else sched.TS_INACTIVE) = ok X6 ∧
      sched.set_action st X6 u = ok X7 ∧
      obj.Tcb.set_state st t X7 sched.TS_RUNNING = ok X8 ∧
      obj.Tcb.set_state st t X8 sched.TS_BLOCKED_ON_RECV = ok X9 ∧
      obj.Tcb.set_block_obj st t X9 ep = ok X10 ∧
      obj.Tcb.set_reply_obj st t X10 rptr = ok X11 ∧
      obj.Reply.set_tcb st rptr X11 t = ok X12 ∧
      obj.Tcb.set_ep_next st t X12 0#u64 = ok X13 ∧
      obj.Tcb.set_ep_prev st t X13 0#u64 = ok X14 ∧
      obj.Ep.set_queue st ep X14 t t obj.EP_RECV = ok X15 ∧
      fastpath.switch_to st ar X15 a2 u = ok (s', a') := by
  unfold rrTail at h
  obtain ⟨X1, e1, h⟩ := bind_eq_ok h
  obtain ⟨⟨X2, a1⟩, e2, h⟩ := bind_eq_ok h
  try simp only at h
  obtain ⟨b9, e3s, h⟩ := bind_eq_ok h
  obtain ⟨X3, e3, h⟩ := bind_eq_ok h
  obtain ⟨⟨restart, X4, a2⟩, e4, h⟩ := bind_eq_ok h
  try simp only at h
  obtain ⟨X5, e5, h⟩ := bind_eq_ok h
  have fin : ∀ (v : U64), (do
      let s6 ← obj.Tcb.set_state st u X5 v
      let s7 ← sched.set_action st s6 u
      let s8 ← obj.Tcb.set_state st t s7 sched.TS_RUNNING
      let s9 ← obj.Tcb.set_state st t s8 sched.TS_BLOCKED_ON_RECV
      let s10 ← obj.Tcb.set_block_obj st t s9 ep
      let s11 ← obj.Tcb.set_reply_obj st t s10 rptr
      let s12 ← obj.Reply.set_tcb st rptr s11 t
      let s13 ← obj.Tcb.set_ep_next st t s12 0#u64
      let s14 ← obj.Tcb.set_ep_prev st t s13 0#u64
      let s15 ← obj.Ep.set_queue st ep s14 t t obj.EP_RECV
      let (s16, a3) ← fastpath.switch_to st ar s15 a2 u
      ok (true, s16, a3)) = ok (true, s', a') →
      ∃ X6 X7 X8 X9 X10 X11 X12 X13 X14 X15,
        obj.Tcb.set_state st u X5 v = ok X6 ∧ sched.set_action st X6 u = ok X7 ∧
        obj.Tcb.set_state st t X7 sched.TS_RUNNING = ok X8 ∧
        obj.Tcb.set_state st t X8 sched.TS_BLOCKED_ON_RECV = ok X9 ∧
        obj.Tcb.set_block_obj st t X9 ep = ok X10 ∧ obj.Tcb.set_reply_obj st t X10 rptr = ok X11 ∧
        obj.Reply.set_tcb st rptr X11 t = ok X12 ∧ obj.Tcb.set_ep_next st t X12 0#u64 = ok X13 ∧
        obj.Tcb.set_ep_prev st t X13 0#u64 = ok X14 ∧ obj.Ep.set_queue st ep X14 t t obj.EP_RECV = ok X15 ∧
        fastpath.switch_to st ar X15 a2 u = ok (s', a') := by
    intro v h
    obtain ⟨X6, e6, h⟩ := bind_eq_ok h
    obtain ⟨X7, e7, h⟩ := bind_eq_ok h
    obtain ⟨X8, e8, h⟩ := bind_eq_ok h
    obtain ⟨X9, e9, h⟩ := bind_eq_ok h
    obtain ⟨X10, e10, h⟩ := bind_eq_ok h
    obtain ⟨X11, e11, h⟩ := bind_eq_ok h
    obtain ⟨X12, e12, h⟩ := bind_eq_ok h
    obtain ⟨X13, e13, h⟩ := bind_eq_ok h
    obtain ⟨X14, e14, h⟩ := bind_eq_ok h
    obtain ⟨X15, e15, h⟩ := bind_eq_ok h
    obtain ⟨⟨s16, a3⟩, e16, h⟩ := bind_eq_ok h
    have e := ok_inj_ff h
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    exact ⟨X6, X7, X8, X9, X10, X11, X12, X13, X14, X15, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩
  cases restart
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨X6, X7, X8, X9, X10, X11, X12, X13, X14, X15, r⟩ := fin _ h
    exact ⟨X1, X2, a1, b9, X3, false, X4, a2, X5, X6, X7, X8, X9, X10, X11, X12, X13, X14, X15,
      e1, e2, e3s, e3, e4, e5, by simp only [Bool.false_eq_true, ↓reduceIte]; exact r⟩
  · simp only [↓reduceIte] at h
    obtain ⟨X6, X7, X8, X9, X10, X11, X12, X13, X14, X15, r⟩ := fin _ h
    exact ⟨X1, X2, a1, b9, X3, true, X4, a2, X5, X6, X7, X8, X9, X10, X11, X12, X13, X14, X15,
      e1, e2, e3s, e3, e4, e5, by simp only [↓reduceIte]; exact r⟩

end

/-! ## (R-b) `finish` from action `u` is the fast path's `switch_to u` -/

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- **`schedule` with a switch-to candidate `u`** (the action word after
`possible_switch_to u`), nothing due, the current thread not schedulable, and
the fast path's priority check (`RRChecks.hp`, read at this state): it switches
to `u` (`switch_to_thread`) and then runs `schedule`'s common end. -/
theorem schedule_sw (s : S) (a : A) {u c : U64}
    (hT : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) <
        L.mem s (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
    (hR : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = 0#u64 ∨
      ¬ ((L.refill s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))
          (L.rhead s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))))).time ≤
        L.curTime s))
    (ha : sched.action st s = ok u) (hu0 : (u != sched.ACTION_RESUME_CURRENT) = true)
    (hucn : ¬ u = sched.ACTION_CHOOSE_NEW)
    (hct : sched.cur_thread st s = ok c) (hns : sched.is_schedulable st s c = ok false)
    (hp : ∃ t1 b7 ff, sched.idle_thread st s = ok t1 ∧ obj.Tcb.Insts.CoreCmpPartialEqTcb.eq c t1 = ok b7 ∧
      (if b7 then ok true else do
        let i11 ← obj.Tcb.prio st u s
        let i12 ← obj.Tcb.prio st c s
        if i11 < i12 then ok true else ok false) = ok ff ∧
      (¬ ff = true ∨ (ff = true ∧ ∃ i11 i12 b8, sched.cur_domain st s = ok i11 ∧ obj.Tcb.prio st u s = ok i12 ∧
        sched.is_highest_prio st s i11 i12 = ok b8 ∧ b8 = true))) :
    sched.schedule st ar s a =
      (do
        let (s3, a2) ← sched.switch_to_thread st ar s a u
        schedTail (st := st) ar s3 a2) := by
  obtain ⟨t1, b7, ff, hi, he, hf, hc⟩ := hp
  unfold sched.schedule
  rw [awaken_none ar s a hT hR]; simp only [bind_ok, uncurry_apply_pair]
  rw [check_domain_time_one]; simp only [bind_ok]
  rw [ha]; simp only [bind_ok, hu0, ↓reduceIte]
  rw [hct]; simp only [bind_ok]
  rw [hns]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, hucn]
  rw [hct]; simp only [bind_ok]
  rw [hi]; simp only [bind_ok]
  rw [he]; simp only [bind_ok]
  rw [hf]; simp only [bind_ok]
  rcases hc with hff | ⟨rfl, i11, i12, b8, hd, hpr, hhp, rfl⟩
  · simp only [hff, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp only [↓reduceIte]
    rw [hd]; simp only [bind_ok]
    rw [hpr]; simp only [bind_ok]
    rw [hhp]; simp only [bind_ok, ↓reduceIte, Bool.false_eq_true]
    rfl

/-- **(R-b) `finish` after the meeting point**: when `schedule` switches to
`u` and `u`'s dequeue is a no-op, the general `finish` ends where the fast
path's `switch_to u` ends (`set_vm_root` returns the store unchanged, so the
dequeue reads the meeting state; then `schedTail_act`). Since #57 `finish`
ends with `vcpu.check` of the current thread: `hnv` (the fast run's end
thread is not `TS_RUNNING_VM`) makes it a no-op (`finish_ok_of_old`). -/
theorem finish_rr {X : S} {a : A} {u : U64} {s' : S} {a' : A}
    (hfast : fastpath.switch_to st ar X a u = ok (s', a'))
    (hsch : sched.schedule st ar X a =
      (do let (s3, a2) ← sched.switch_to_thread st ar X a u; schedTail (st := st) ar s3 a2))
    (hdq : sched.dequeue st X u = ok X)
    (hnv : L.mem s' (stA (L.curW s')) ≠ sched.TS_RUNNING_VM) :
    syscall.finish st ar X a = ok (s', a') := by
  refine finish_ok_of_old ar ?_ hnv
  have hf0 := hfast
  unfold fastpath.switch_to at hf0
  obtain ⟨⟨s1, a1⟩, e1, -⟩ := bind_eq_ok hf0
  have hs1 : s1 = X := set_vm_root_ok_s ar e1
  subst hs1
  unfold fastpath.switch_to at hfast
  rw [e1] at hfast
  simp only [bind_ok, uncurry_apply_pair, set_action_ok] at hfast
  obtain ⟨s2, e2, hfast⟩ := bind_eq_ok hfast
  unfold syscall.finish_old
  rw [hsch]; unfold sched.switch_to_thread
  rw [e1]; simp only [bind_ok, uncurry_apply_pair]
  rw [hdq]; simp only [bind_ok]
  rw [e2]; simp only [bind_ok, uncurry_apply_pair]
  rw [schedTail_act (L := L) ar s2 a1]
  · unfold fastTail; exact hfast
  · intro x; obtain ⟨_, _⟩ := x; rfl

end

end Fl4Proofs.P1
