/-
# The accepted ReplyRecv fast path (FL4 #56, m64 (R))

The ReplyRecv half of the fast-path premise, in m58's meeting-point style.
First step: the inversion of an accepted `fastpath.reply_recv_found` (as
FastFault's `fault_acc`): every check held at the entry state (`RRChecks`,
in the raw form the extraction reads them) and the run is `rrTail`, the
write part verbatim (fastpath.rs from `t.set_state(Restart)` to
`switch_to(u)`).

Against the general path (`dispatch_syscall SysReplyRecv` + `finish`) the
writes come in the same order (m57 (3)): `t` Restart (`set_thread_state`'s
`schedule_tcb` a no-op: `t` stays schedulable), `do_reply_transfer`'s
`reply_remove`, `unblock_check`, `handle_fault_reply`, `clear_fault`, `u`'s
state, `possible_switch_to u` from RESUME = the action write, `t` Running,
`receive_ipc`'s `wait_for_sender` on the idle endpoint; the general path adds
only reads (the decode, the second cap lookups, `take_reply` with
`r.tcb = 0`, the bound notification) and `schedule`'s choice of `u`.
-/
import Fl4Proofs.P1.FastFaultEnt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} (st : machine.Store S) (ar : machine.Arch A)

/-- The write part of an accepted `fastpath.reply_recv_found` (from `t`'s
Restart to `switch_to u`), verbatim from the extraction. -/
def rrTail (s : S) (a : A) (t : obj.Tcb) (rptr ep_ptr i1 i5 : Std.U64) : Result (Bool × S × A) := do
  let s1 ← obj.Tcb.set_state st t s sched.TS_RESTART
  let (s2, a1) ← ipc.reply_remove st ar s1 a rptr i1
  let b9 ← sporadic.sc_sporadic st s2 i5
  let s3 ←
    if b9
    then
      do
      let i13 ← obj.Sc.cpu st i5 s2
      let i14 ← obj.node_get st s2 i13 layout.node.CUR_SC
      if i5 != i14
      then sporadic.unblock_check st s2 i5
      else ok s2
    else ok s2
  let (restart, s4, a2) ← faults.handle_fault_reply st ar s3 a1 i1 t
  let s5 ← faults.clear_fault st s4 i1
  if restart
  then
    let s6 ← obj.Tcb.set_state st i1 s5 sched.TS_RESTART
    let s7 ← sched.set_action st s6 i1
    let s8 ← obj.Tcb.set_state st t s7 sched.TS_RUNNING
    let s9 ← obj.Tcb.set_state st t s8 sched.TS_BLOCKED_ON_RECV
    let s10 ← obj.Tcb.set_block_obj st t s9 ep_ptr
    let s11 ← obj.Tcb.set_reply_obj st t s10 rptr
    let s12 ← obj.Reply.set_tcb st rptr s11 t
    let s13 ← obj.Tcb.set_ep_next st t s12 0#u64
    let s14 ← obj.Tcb.set_ep_prev st t s13 0#u64
    let s15 ← obj.Ep.set_queue st ep_ptr s14 t t obj.EP_RECV
    let (s16, a3) ← fastpath.switch_to st ar s15 a2 i1
    ok (true, s16, a3)
  else
    let s6 ← obj.Tcb.set_state st i1 s5 sched.TS_INACTIVE
    let s7 ← sched.set_action st s6 i1
    let s8 ← obj.Tcb.set_state st t s7 sched.TS_RUNNING
    let s9 ← obj.Tcb.set_state st t s8 sched.TS_BLOCKED_ON_RECV
    let s10 ← obj.Tcb.set_block_obj st t s9 ep_ptr
    let s11 ← obj.Tcb.set_reply_obj st t s10 rptr
    let s12 ← obj.Reply.set_tcb st rptr s11 t
    let s13 ← obj.Tcb.set_ep_next st t s12 0#u64
    let s14 ← obj.Tcb.set_ep_prev st t s13 0#u64
    let s15 ← obj.Ep.set_queue st ep_ptr s14 t t obj.EP_RECV
    let (s16, a3) ← fastpath.switch_to st ar s15 a2 i1
    ok (true, s16, a3)

/-- The checks of an accepted `fastpath.reply_recv_found` at its entry state,
in the form the extraction reads them (`u` = the reply's TCB, `usc` = its
SC). -/
structure RRChecks (s : S) (a : A) (t : obj.Tcb) (rptr ep_ptr u usc : Std.U64) : Prop where
  act : ∃ i, sched.action st s = ok i ∧ ¬ (i != sched.ACTION_RESUME_CURRENT) = true
  sch : ∃ b, sched.is_schedulable st s t = ok b ∧ b = true
  info : ∃ info, msg.msg_info st s t = ok info ∧ ¬ (info.extra_caps != 0#u64) = true ∧
    ¬ (info.label != 0#u64) = true
  tcb : obj.Reply.tcb st rptr s = ok u
  u0 : ∃ b, obj.Tcb.is_null u = ok b ∧ ¬ b = true
  ust : ∃ i, obj.Tcb.state st u s = ok i ∧ ¬ (i != sched.TS_BLOCKED_ON_REPLY) = true
  uft : ∃ i, obj.Tcb.fault_type st u s = ok i ∧ ¬ (i != fl4_abi.consts.fault.UnknownSyscall) = true
  nxt : (∃ i, obj.Reply.next st rptr s = ok i ∧ ¬ (i != 0#u64) = true) ∨
    (∃ i, obj.Reply.next st rptr s = ok i ∧ (i != 0#u64) = true ∧
      ∃ b, obj.Reply.next_is_head st rptr s = ok b ∧ ¬ b = true)
  sc : obj.Tcb.sc st u s = ok usc
  sc0 : ∃ b, obj.Sc.is_null usc = ok b ∧ ¬ b = true
  rdy : ∃ b, sporadic.ready st s usc = ok b ∧ b = true
  suf : ∃ b, sporadic.sufficient st ar s a usc 0#u64 = ok b ∧ b = true
  here : ∃ b, fastpath.schedulable_here st s u = ok b ∧ b = true
  ntfn : (∃ i, obj.Tcb.bound_ntfn st t s = ok i ∧ ¬ (i != 0#u64) = true) ∨
    (∃ i, obj.Tcb.bound_ntfn st t s = ok i ∧ (i != 0#u64) = true ∧
      ∃ i7, obj.Ntfn.state st i s = ok i7 ∧ ¬ i7 = obj.NTFN_ACTIVE ∧
      ∃ i8, obj.Ntfn.sc st i s = ok i8 ∧
        (¬ (i8 != 0#u64) = true ∨ ((i8 != 0#u64) = true ∧ ∃ i9, obj.Tcb.sc st t s = ok i9 ∧ ¬ i8 = i9)))
  ep : ∃ i, obj.Ep.state st ep_ptr s = ok i ∧ ¬ (i != obj.EP_IDLE) = true
  hp : ∃ t1 b7 ff, sched.idle_thread st s = ok t1 ∧ obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t1 = ok b7 ∧
    (if b7 then ok true else do
      let i11 ← obj.Tcb.prio st u s
      let i12 ← obj.Tcb.prio st t s
      if i11 < i12 then ok true else ok false) = ok ff ∧
    (¬ ff = true ∨ (ff = true ∧ ∃ i11 i12 b8, sched.cur_domain st s = ok i11 ∧ obj.Tcb.prio st u s = ok i12 ∧
      sched.is_highest_prio st s i11 i12 = ok b8 ∧ b8 = true))

/-- Goal-directed elimination of an equation on a bind. -/
theorem eq_bind_imp {α β : Type _} {m : Result α} {f : α → Result β} {y : β} {G : Prop}
    (h : ∀ x, m = ok x → f x = ok y → G) : Std.bind m f = ok y → G := fun hb => by
  obtain ⟨x, e, hx⟩ := bind_eq_ok hb; exact h x e hx

theorem eq_bind_imp' {α β : Type _} {m : Result α} {f : α → Result β} {y : β} {G : Prop}
    (h : ∀ x, m = ok x → f x = ok y → G) : (m >>= f) = ok y → G := eq_bind_imp h

/-- Goal-directed case split of an equation on an `if`. -/
theorem eq_ite_imp {β : Type _} {c : Prop} [Decidable c] {x z : Result β} {y : β} {G : Prop}
    (h1 : c → x = ok y → G) (h2 : ¬ c → z = ok y → G) : (if c then x else z) = ok y → G := by
  by_cases hc : c
  · rw [if_pos hc]; exact h1 hc
  · rw [if_neg hc]; exact h2 hc

open Lean Elab Tactic Meta in
/-- Succeeds when the goal is `bind (obj.Tcb.set_state …) f = _ → _` (the
walk reached the write part): a syntactic guard. -/
elab "rr_at_tail" : tactic => withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  let .forallE _ ty _ _ := g | throwError "rr_at_tail: not an implication"
  let some (_, lhs, _) := ty.eq? | throwError "rr_at_tail: not an equation"
  let args := lhs.getAppArgs
  if args.size < 2 then throwError "rr_at_tail: not a bind"
  unless (args[args.size - 2]!).getAppFn.isConstOf ``obj.Tcb.set_state do
    throwError "rr_at_tail: not the write part"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **Inversion of an accepted `fastpath.reply_recv_found`**: its checks held
at the entry state and the run is `rrTail` from there. -/
theorem reply_recv_found_acc {s : S} {a : A} {t : obj.Tcb} {rptr ep_ptr : Std.U64} {s' : S} {a' : A}
    (h : fastpath.reply_recv_found st ar s a t rptr ep_ptr = ok (true, s', a')) :
    ∃ u usc, RRChecks st ar s a t rptr ep_ptr u usc ∧
      rrTail st ar s a t rptr ep_ptr u usc = ok (true, s', a') := by
  unfold fastpath.reply_recv_found at h
  revert h
  repeat' (first
    | (rr_at_tail; intro h; refine ⟨_, _, ?_, h⟩; clear h)
    | (with_reducible_and_instances refine eq_bind_imp (fun _ _ => ?_))
    | (with_reducible_and_instances refine eq_bind_imp' (fun _ _ => ?_))
    | (with_reducible refine eq_ite_imp (fun _ => ?_) (fun _ => ?_))
    | (intro h; simp at h; done))
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | assumption
    | exact ⟨_, ‹_›, ‹_›⟩
    | exact ⟨_, ‹_›, ‹_›, ‹_›⟩
    | exact Or.inl ⟨_, ‹_›, ‹_›⟩
    | exact Or.inr ⟨_, ‹_›, ‹_›, _, ‹_›, ‹_›⟩
    | exact Or.inr ⟨_, ‹_›, ‹_›, _, ‹_›, ‹_›, _, ‹_›, Or.inl ‹_›⟩
    | exact Or.inr ⟨_, ‹_›, ‹_›, _, ‹_›, ‹_›, _, ‹_›, Or.inr ⟨‹_›, _, ‹_›, ‹_›⟩⟩
    | exact ⟨_, _, _, ‹_›, ‹_›, ‹_›, Or.inl ‹_›⟩
    | exact ⟨_, _, _, ‹_›, ‹_›, ‹_›, Or.inr ⟨‹_›, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›⟩⟩

/-! ## R3 / R7: the restart flag and the Arch value -/

/-- **R3 / R7 for `handle_fault_reply`**: replying to an UnknownSyscall fault
with label 0 restarts the receiver, and the Arch value comes back unchanged
(so `do_reply_transfer` takes `possible_switch_to`, and its `sufficient` reads
`min_budget` on the fast path's Arch value). -/
theorem hfr_us {s : S} {a : A} {rcv snd : obj.Tcb} {restart : Bool} {s4 : S} {a4 : A}
    (hty : obj.Tcb.fault_type st rcv s = ok fl4_abi.consts.fault.UnknownSyscall)
    (htag : ∃ tag, msg.msg_info st s snd = ok tag ∧ tag.label = 0#u64)
    (h : faults.handle_fault_reply st ar s a rcv snd = ok (restart, s4, a4)) : restart = true ∧ a4 = a := by
  obtain ⟨tag, et, hl⟩ := htag
  unfold faults.handle_fault_reply at h
  rw [et, hty] at h
  simp only [bind_ok] at h
  have c : fl4_abi.consts.fault.UnknownSyscall ≠ fl4_abi.consts.fault.CapFault := by
    unfold fl4_abi.consts.fault.UnknownSyscall fl4_abi.consts.fault.CapFault; decide
  rw [if_neg c, if_pos trivial] at h
  obtain ⟨s1, -, h⟩ := bind_eq_ok h
  obtain ⟨s2, -, h⟩ := bind_eq_ok h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, -, e3⟩ := e
  exact ⟨by rw [← e1]; simp [hl], e3.symm⟩

/-- **R7 for `reply_remove`**: off the head of a call stack (the fast path's
check) it is the unlink branch, which returns the Arch value unchanged. -/
theorem reply_remove_a {s : S} {a : A} {r t : U64} {s' : S} {a' : A}
    (hn : (∃ i, obj.Reply.next st r s = ok i ∧ ¬ (i != 0#u64) = true) ∨
      (∃ i, obj.Reply.next st r s = ok i ∧ (i != 0#u64) = true ∧
        ∃ b, obj.Reply.next_is_head st r s = ok b ∧ ¬ b = true))
    (h : ipc.reply_remove st ar s a r t = ok (s', a')) : a' = a := by
  unfold ipc.reply_remove at h
  rcases hn with ⟨i, hi, hc⟩ | ⟨i, hi, hc, b, hb, hbc⟩
  · rw [hi] at h; simp only [bind_ok] at h
    obtain ⟨p, -, h⟩ := bind_eq_ok h
    rw [if_neg hc] at h
    revert h
    repeat' (first
      | (with_reducible_and_instances refine eq_bind_imp (fun _ _ => ?_))
      | (with_reducible_and_instances refine eq_bind_imp' (fun _ _ => ?_))
      | (intro h; exact (congrArg (fun x => x.2) (ok_inj_ff h)).symm))
  · rw [hi] at h; simp only [bind_ok] at h
    obtain ⟨p, -, h⟩ := bind_eq_ok h
    rw [if_pos hc, hb] at h; simp only [bind_ok] at h
    rw [if_neg hbc] at h
    revert h
    repeat' (first
      | (with_reducible_and_instances refine eq_bind_imp (fun _ _ => ?_))
      | (with_reducible_and_instances refine eq_bind_imp' (fun _ _ => ?_))
      | (intro h; exact (congrArg (fun x => x.2) (ok_inj_ff h)).symm))

/-- **Inversion of an accepted `fastpath.reply_recv`**: the current thread's
`reply_caps` found the reply object and the endpoint, and
`reply_recv_found` accepted. -/
theorem reply_recv_acc {s : S} {a : A} {s' : S} {a' : A}
    (h : fastpath.reply_recv st ar s a = ok (true, s', a')) :
    ∃ t rptr ep_ptr, sched.cur_thread st s = ok t ∧ fastpath.reply_caps st s t = ok (some (rptr, ep_ptr)) ∧
      fastpath.reply_recv_found st ar s a t rptr ep_ptr = ok (true, s', a') := by
  unfold fastpath.reply_recv at h
  obtain ⟨t, ht, h⟩ := bind_eq_ok h
  obtain ⟨o, ho, h⟩ := bind_eq_ok h
  cases o with
  | none => simp at h
  | some p =>
    obtain ⟨rptr, ep⟩ := p
    exact ⟨t, rptr, ep, ht, ho, h⟩

/-- **What `reply_caps` found**: the current thread's CSpace root, its
`REPLY` register resolving to a slot holding a Reply cap on `rptr`, and its
`CAP` register resolving to a slot holding an Endpoint cap on `ep_ptr` with
the receive right. -/
structure RCaps (s : S) (t : obj.Tcb) (rptr ep_ptr : Std.U64) : Prop where
  root : ∃ sl root, obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok sl ∧ obj.Slot.cap st sl s = ok root ∧
    (∃ i found g, obj.Tcb.reg st t s layout.reg.REPLY = ok i ∧
      cspace.resolve_address_bits st s root i cspace.WORD_BITS = ok (core.result.Result.Ok found) ∧
      obj.Slot.cap st found.slot s = ok (capability.Cap.Reply rptr g)) ∧
    (∃ i1 found1 b0 b1 b3 b4, obj.Tcb.reg st t s layout.reg.CAP = ok i1 ∧
      cspace.resolve_address_bits st s root i1 cspace.WORD_BITS = ok (core.result.Result.Ok found1) ∧
      obj.Slot.cap st found1.slot s = ok (capability.Cap.Endpoint ep_ptr b0 b1 true b3 b4))

theorem reply_caps_some {s : S} {t : obj.Tcb} {rptr ep_ptr : Std.U64}
    (h : fastpath.reply_caps st s t = ok (some (rptr, ep_ptr))) : RCaps st s t rptr ep_ptr := by
  unfold fastpath.reply_caps at h
  obtain ⟨sl, hsl, h⟩ := bind_eq_ok h
  obtain ⟨root, hroot, h⟩ := bind_eq_ok h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨r, hr, h⟩ := bind_eq_ok h
  cases r with
  | Err _ => simp at h
  | Ok found =>
    simp only at h
    obtain ⟨c, hc, h⟩ := bind_eq_ok h
    cases c
    all_goals try (simp at h; done)
    rename_i p g
    simp only at h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok h
    cases r1 with
    | Err _ => simp at h
    | Ok found1 =>
      simp only at h
      obtain ⟨c1, hc1, h⟩ := bind_eq_ok h
      cases c1
      all_goals try (simp at h; done)
      rename_i p1 b0 b1 b2 b3 b4
      simp only at h
      cases b2
      · simp at h
      · simp only [↓reduceIte] at h
        have e := ok_inj_ff h
        simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact ⟨⟨sl, root, hsl, hroot, ⟨i, found, g, hi, hr, hc⟩, ⟨i1, found1, b0, b1, b3, b4, hi1, hr1, hc1⟩⟩⟩

/-! ## The general path's ReplyRecv branch -/

/-- `dispatch_syscall` on `SysReplyRecv`: `handle_invocation` on the
`REPLY` cptr (not a call, not blocking, may donate, first phase), then, if
not preempted, `handle_recv` (blocking, with a reply). -/
theorem dispatch_rr (s : S) (a : A) :
    syscall.dispatch_syscall st ar s a fl4_abi.syscall.SysReplyRecv = (do
      let t ← sched.cur_thread st s
      let _cptr ← obj.Tcb.reg st t s layout.reg.CAP
      let reply ← obj.Tcb.reg st t s layout.reg.REPLY
      let (r, s1, a1) ← syscall.handle_invocation st ar s a false false true true reply
      let (b, s2, a2) ← syscall.after_invocation st ar s1 a1 r
      if b then syscall.handle_recv st ar s2 a2 true true else ok (s2, a2)) := by
  have c1 : fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysSend; decide
  have c2 : fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBSend := by
    unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBSend; decide
  have c3 : fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysCall := by
    unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysCall; decide
  have c4 : fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysRecv := by
    unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysRecv; decide
  have c5 : fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBRecv := by
    unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBRecv; decide
  have c6 : fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysWait := by
    unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysWait; decide
  have c7 : fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBWait := by
    unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBWait; decide
  unfold syscall.dispatch_syscall
  simp only [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5, if_neg c6, if_neg c7, if_pos rfl, ↓reduceIte]

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- `schedule_tcb` while a switch-to candidate or choose-new is pending is no
write (the general path's `set_thread_state` of `t` after `possible_switch_to
u`, and `wait_for_sender`'s). -/
theorem schedule_tcb_nr (s : S) (x : obj.Tcb) (ha : L.actionW s ≠ sched.ACTION_RESUME_CURRENT) :
    sched.schedule_tcb st s x = ok s := by
  unfold sched.schedule_tcb
  rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.eq.spec _ _)]; simp only [bind_ok]
  split
  · rw [eq_of_spec_fd (sched.action.spec (L := L) s)]; simp only [bind_ok, ha, ↓reduceIte]
  · rfl

/-- `schedule_tcb` of a schedulable thread is no write (the general path's
`set_thread_state t Restart` in the Reply decode: `t` stays schedulable). -/
theorem schedule_tcb_sch (s : S) (x : obj.Tcb) (hs : sched.is_schedulable st s x = ok true) :
    sched.schedule_tcb st s x = ok s := by
  unfold sched.schedule_tcb
  rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.eq.spec _ _)]; simp only [bind_ok]
  split
  · rw [eq_of_spec_fd (sched.action.spec (L := L) s)]; simp only [bind_ok]
    split
    · rw [hs]; simp only [bind_ok, ↓reduceIte]
    · rfl
  · rfl

end

end Fl4Proofs.P1
