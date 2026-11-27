/-
# The accepted ReplyRecv fast path ends where the general path ends (FL4 #56, m66 (R-d))

m65's sync lemmas composed (`rr_same`): an accepted `fastpath.reply_recv`
from a dispatch state `X0` (`reply_recv_acc`, `reply_recv_found_acc`,
`reply_caps_some`, `rrTail_split`; the restart flag by `hfr_us`) gives

  `dispatch_syscall X0 SysReplyRecv = ok (X15, a2)` and `finish X15 a2 = ok (s', a')`

(`do_reply_transfer_rr`, `handle_invocation_rr`, `ep_append_empty`,
`handle_recv_rr`, `rr_sync_of`, `schedule_sw`, `finish_rr`): equality of
states, under `StoreExt` [P] (the fast path writes `t`'s BLOCK_OBJ before its
STATE, `wait_for_sender` STATE first: one `wr_comm`).

The general path's reads at the fast run's intermediate states are the
hypothesis bundle `RRPre` (fields `RRR3` / `RRReads`, one per read the general
path makes that is not already one of the fast path's own checks at `X0`).
Those that ARE the fast path's checks or its cap lookups at `X0` (the decode's
`cur_thread` / `msg_info` / `extra_caps`, `lookup_slot` + the Reply cap, the
`CAP` / `REPLY` registers, `is_null u`, `is_null usc`), the restart flag
(`hfr_us`) and the totality reads (`lookup_ipc_buffer`, `prio`) are derived
here. Each field of `RRReads` holds in every reachable accepted run (KENTRY-PLAN
m65 / m66: a frame read through the run's writes, or a typing fact); their
derivation from entry-state facts is the remaining (R-a') work.

* `syscall_rr_general`: the general `syscall … false` from the kernel entry
  state follows the fast entry's prefix (`FAULT_IP` write, trap flag clear,
  native number, passing `budget_ok`) and then `dispatch_syscall` + `finish`.
* `FastAcc.of_split_rr`: `FastAcc` from the fault half (`FastFaultOK`,
  `StoreExt` [P]) and the ReplyRecv half proved from `RRPreAt` (the bundle
  at every dispatch state), replacing m60's `FastRRP` [P].
* Top `kernel_entry.entry_of7r` = `entry_of7` with `hRR : FastRRP` [P]
  replaced by `hRP : RRPreAt` (the general path's reads; no `P` inside).
-/
import Fl4Proofs.P1.FastRRSync
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- The reads before the restart flag is known: `u`'s fault type (`ty`) and
`t`'s label at `X3` (where `handle_fault_reply` runs). -/
structure RRR3G (ty : U64) (X3 : S) (t u : U64) : Prop where
  ft3 : obj.Tcb.fault_type st u X3 = ok ty
  lbl3 : ∃ tag, msg.msg_info st X3 t = ok tag ∧ tag.label = 0#u64

/-- `RRR3G` for an UnknownSyscall fault (m66). -/
abbrev RRR3 (X3 : S) (t u : U64) : Prop := RRR3G (st := st) fl4_abi.consts.fault.UnknownSyscall X3 t u

/-- **The general path's reads along an accepted ReplyRecv run** (the states
`X1 … X15` are the binds of `rrTail`, restart = true). Each is a read the
general path makes that is not one of the fast path's checks at `X0`. -/
structure RRReads (t rptr ep u usc : U64) (X1 X2 X6 X7 X8 X11 X12 X15 : S) (a2 : A) : Prop where
  /-- `t`'s state and blocking-object words are aligned and distinct: the fast
  path writes BLOCK_OBJ then STATE, `wait_for_sender` STATE then BLOCK_OBJ
  (`rr_found_sameG` swaps them). -/
  tw : Aligned (stA t) ∧ Aligned (blockA t) ∧ stA t ≠ blockA t
  sch1 : sched.is_schedulable st X1 t = ok true
  rt1 : obj.Reply.tcb st rptr X1 = ok u
  us1 : obj.Tcb.state st u X1 = ok sched.TS_BLOCKED_ON_REPLY
  sc2 : obj.Tcb.sc st u X2 = ok usc
  sch6 : sched.schedule_tcb st X6 u = ok X6
  sc6 : obj.Tcb.sc st u X6 = ok usc
  run6 : sched.is_runnable st X6 u = ok true
  rdy6 : sporadic.ready st X6 usc = ok true
  suf6 : sporadic.sufficient st ar X6 a2 usc 0#u64 = ok true
  pst : sched.possible_switch_to st X6 u = ok X7
  st7 : obj.Tcb.state st t X7 = ok sched.TS_RESTART
  act8 : L.actionW X8 ≠ sched.ACTION_RESUME_CURRENT
  ct8 : sched.cur_thread st X8 = ok t
  lk8 : ∃ i i1 b0 b1 b3 b4 g, obj.Tcb.reg st t X8 layout.reg.CAP = ok i1 ∧
    cspace.lookup_cap st X8 t i1 = ok (core.result.Result.Ok (capability.Cap.Endpoint ep b0 b1 true b3 b4)) ∧
    obj.Tcb.reg st t X8 layout.reg.REPLY = ok i ∧
    cspace.lookup_cap st X8 t i = ok (core.result.Result.Ok (capability.Cap.Reply rptr g))
  rt8 : obj.Reply.tcb st rptr X8 = ok 0#u64
  ntfn8 : ∃ n, obj.Tcb.bound_ntfn st t X8 = ok n ∧
    (n = 0#u64 ∨ (n ≠ 0#u64 ∧ ∃ i7, obj.Ntfn.state st n X8 = ok i7 ∧ ¬ i7 = obj.NTFN_ACTIVE ∧
      notification.maybe_return_sched_context st X8 n t = ok X8))
  ep8 : obj.Ep.state st ep X8 = ok obj.EP_IDLE
  act11 : L.actionW X11 ≠ sched.ACTION_RESUME_CURRENT
  r0 : rptr ≠ 0#u64
  q12 : ∃ q, endpoint.get_queue st X12 ep = ok q ∧ q.head = 0#u64
  T15 : L.mem X15 (L.nodeAt X15 (L.cpu X15) layout.node.TIMER_MIN) = 0#u64 ∨
    L.mem X15 (L.nodeAt X15 (L.cpu X15) layout.node.CUR_TIME) <
      L.mem X15 (tdA (L.mem X15 (L.nodeAt X15 (L.cpu X15) layout.node.TIMER_MIN)))
  R15 : L.mem X15 (L.nodeAt X15 (L.cpu X15) layout.node.RELEASE_HEAD) = 0#u64 ∨
    ¬ ((L.refill X15 (L.mem X15 (scA (L.mem X15 (L.nodeAt X15 (L.cpu X15) layout.node.RELEASE_HEAD))))
        (L.rhead X15 (L.mem X15 (scA (L.mem X15 (L.nodeAt X15 (L.cpu X15) layout.node.RELEASE_HEAD)))))).time ≤
      L.curTime X15)
  act15 : sched.action st X15 = ok u
  ucn : ¬ u = sched.ACTION_CHOOSE_NEW
  ct15 : sched.cur_thread st X15 = ok t
  ns15 : sched.is_schedulable st X15 t = ok false
  hp15 : ∃ t1 b7 ff, sched.idle_thread st X15 = ok t1 ∧ obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t1 = ok b7 ∧
    (if b7 then ok true else do
      let i11 ← obj.Tcb.prio st u X15
      let i12 ← obj.Tcb.prio st t X15
      if i11 < i12 then ok true else ok false) = ok ff ∧
    (¬ ff = true ∨ (ff = true ∧ ∃ i11 i12 b8, sched.cur_domain st X15 = ok i11 ∧ obj.Tcb.prio st u X15 = ok i12 ∧
      sched.is_highest_prio st X15 i11 i12 = ok b8 ∧ b8 = true))
  dq15 : sched.dequeue st X15 u = ok X15
  /-- (#57, m67) The thread the accepted run switches to (`u`, made
  `TS_RESTART` at `X6`, so `activate_thread` makes it `TS_RUNNING`) is not
  `TS_RUNNING_VM` at the run's end: the general `finish`'s `vcpu.check` is a
  no-op (`finish_rr`). A read of the end state, as m62's `FaultNvm`. -/
  nvm : ∀ s' a', fastpath.switch_to st ar X15 a2 u = ok (s', a') →
    L.mem s' (stA (L.curW s')) ≠ sched.TS_RUNNING_VM

/-- **The ReplyRecv read bundle at a dispatch state `X0`** (a receiver with a
fault of type `ty`, pf1): for every accepted
run's checks (`RRChecks`, the `reply_caps` result) and its intermediate states,
`RRR3` at `X3` and, once the restart flag is `true`, `RRReads`. -/
def RRPreG (ty : U64) (X0 : S) (a : A) : Prop :=
  ∀ (t rptr ep u usc : U64) (X1 X2 : S) (a1 : A) (b9 : Bool) (X3 : S),
    sched.cur_thread st X0 = ok t → fastpath.reply_caps st X0 t = ok (some (rptr, ep)) →
    RRChecksG st ar ty X0 a t rptr ep u usc →
    obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1 →
    ipc.reply_remove st ar X1 a rptr u = ok (X2, a1) →
    sporadic.sc_sporadic st X2 usc = ok b9 →
    (if b9 then do
      let i13 ← obj.Sc.cpu st usc X2
      let i14 ← obj.node_get st X2 i13 layout.node.CUR_SC
      if usc != i14 then sporadic.unblock_check st X2 usc else ok X2
    else ok X2) = ok X3 →
    RRR3G (st := st) ty X3 t u ∧
    ∀ (X4 : S) (a2 : A) (X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 : S),
      faults.handle_fault_reply st ar X3 a1 u t = ok (true, X4, a2) →
      faults.clear_fault st X4 u = ok X5 →
      obj.Tcb.set_state st u X5 sched.TS_RESTART = ok X6 →
      sched.set_action st X6 u = ok X7 →
      obj.Tcb.set_state st t X7 sched.TS_RUNNING = ok X8 →
      obj.Tcb.set_block_obj st t X8 ep = ok X9 →
      obj.Tcb.set_state st t X9 sched.TS_BLOCKED_ON_RECV = ok X10 →
      obj.Tcb.set_reply_obj st t X10 rptr = ok X11 →
      obj.Reply.set_tcb st rptr X11 t = ok X12 →
      obj.Tcb.set_ep_next st t X12 0#u64 = ok X13 →
      obj.Tcb.set_ep_prev st t X13 0#u64 = ok X14 →
      obj.Ep.set_queue st ep X14 t t obj.EP_RECV = ok X15 →
      RRReads (L := L) ar t rptr ep u usc X1 X2 X6 X7 X8 X11 X12 X15 a2

/-- `RRPreG` for an UnknownSyscall fault (m66). -/
abbrev RRPre (X0 : S) (a : A) : Prop := RRPreG (L := L) ar fl4_abi.consts.fault.UnknownSyscall X0 a

/-- **`rr_same` from the checks, over the fault type** (pf1): an accepted run
`rrTail` after the checks `RRChecksG ty` (with `(rptr, ep)` what `reply_caps`
returns at `X0`) ends where `dispatch_syscall … SysReplyRecv` + `finish` end,
given `StoreExt` [P], `RRPreG ty` and the restart flag `HfrRestart ty`. -/
theorem rr_found_sameG (hX : StoreExt st) {ty : U64} [HfrRestart st ar ty] (hty0 : ¬ ty = fl4_abi.consts.fault.NullFault)
    {X0 s' : S} {a a' : A} {t rptr ep u usc : U64}
    (hct : sched.cur_thread st X0 = ok t) (hrc : fastpath.reply_caps st X0 t = ok (some (rptr, ep)))
    (hC : RRChecksG st ar ty X0 a t rptr ep u usc) (hT : rrTail st ar X0 a t rptr ep u usc = ok (true, s', a'))
    (hP : RRPreG (L := L) ar ty X0 a) :
    ∃ X a'', syscall.dispatch_syscall st ar X0 a fl4_abi.syscall.SysReplyRecv = ok (X, a'') ∧
      syscall.finish st ar X a'' = ok (s', a') := by
  have hRC := reply_caps_some st hrc
  obtain ⟨X1, X2, a1, b9, X3, restart, X4, a2, X5, X6, X7, X8, X9, X10, X11, X12, X13, X14, X15,
    e1, e2, e3s, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ := rrTail_split st ar hT
  obtain ⟨R3, hR⟩ := hP t rptr ep u usc X1 X2 a1 b9 X3 hct hrc hC e1 e2 e3s e3
  obtain ⟨hrs, -⟩ := HfrRestart.restart (st := st) (ar := ar) R3.ft3 R3.lbl3 e4
  subst hrs
  rw [if_pos rfl] at e6
  have R := hR X4 a2 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  have hun : obj.Tcb.is_null u = ok false := by
    obtain ⟨b, hb, hbn⟩ := hC.u0
    rw [Bool.not_eq_true] at hbn; subst hbn; exact hb
  have husc : obj.Sc.is_null usc = ok false := by
    obtain ⟨b, hb, hbn⟩ := hC.sc0
    rw [Bool.not_eq_true] at hbn; subst hbn; exact hb
  obtain ⟨⟨sl, root, hsl, hroot, ⟨i, found, g, hi, hr, hc⟩, ⟨i1, found1, b0, b1, b3, b4, hi1, hr1, hc1⟩⟩⟩ := hRC
  have hls : cspace.lookup_slot st X0 t i = ok (core.result.Result.Ok found) := by
    unfold cspace.lookup_slot
    rw [hsl]; simp only [bind_ok]
    rw [hroot]; simp only [bind_ok]
    exact hr
  obtain ⟨info, hmi, hex, -⟩ := hC.info
  have hex' : info.extra_caps = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hex
  obtain ⟨buf, hbuf, -⟩ := spec_ex_fd (P0.msg.lookup_ipc_buffer.p0 st X0 false t L.total)
  have hdrt := do_reply_transfer_rrG st ar (t := t) (g := g) (hty0 := hty0) R.rt1 hun R.us1 e2 R.sc2 e3s e3 R3.ft3 e4 e5 e6
    R.sch6 R.sc6 husc R.run6 R.rdy6 R.suf6 R.pst
  have hinv := handle_invocation_rr st ar hct hmi hex' hls hc hbuf e1 (schedule_tcb_sch (L := L) X1 t R.sch1)
    hdrt R.st7 e8 (schedule_tcb_nr (L := L) X8 t R.act8)
  obtain ⟨j, j1, c0, c1, c3, c4, g', hj1, hlk1, hj, hlk2⟩ := R.lk8
  obtain ⟨n, hbn, hnc⟩ := R.ntfn8
  obtain ⟨q, hq, hq0⟩ := R.q12
  obtain ⟨p, hp, -⟩ := spec_ex_fd (P0.obj.Tcb.prio.p0 st t X12 L.total)
  have hap := ep_append_empty st hq hq0 ⟨p, hp⟩ e13 e14 e15
  -- the two writes in the general path's order (`wr_comm`)
  obtain ⟨tS, tB, tne⟩ := R.tw
  have w9 : X9 = L.wr X8 (blockA t) ep := by
    have := obj.Tcb.set_block_obj.wr (L := L) X8 t ep; rw [e9, WP.spec_ok] at this; exact this
  have w10 : X10 = L.wr (L.wr X8 (stA t) sched.TS_BLOCKED_ON_RECV) (blockA t) ep := by
    have := obj.Tcb.set_state.spec (L := L) X9 t sched.TS_BLOCKED_ON_RECV; rw [e10, WP.spec_ok] at this
    rw [this, w9]; exact wr_comm hX X8 _ _ tB tS (Ne.symm tne)
  have g9 := eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) X8 t sched.TS_BLOCKED_ON_RECV)
  have g10 : obj.Tcb.set_block_obj st t (L.wr X8 (stA t) sched.TS_BLOCKED_ON_RECV) ep = ok X10 := by
    rw [w10]; exact eq_of_spec_fd (obj.Tcb.set_block_obj.wr (L := L) _ t ep)
  have hrecv := handle_recv_rr st ar (a := a2) R.ct8 hj1 hlk1 hj hlk2 R.rt8 hbn hnc R.ep8 g9 g10 e11
    (schedule_tcb_nr (L := L) X11 t R.act11) R.r0 e12 hap
  have hdisp := rr_sync_of st ar hct hi1 hi hinv hrecv
  have hu0 : (u != sched.ACTION_RESUME_CURRENT) = true := by
    obtain ⟨b, hb, hbn⟩ := hC.u0
    unfold obj.Tcb.is_null at hb
    have e := ok_inj_ff hb
    subst e
    unfold sched.ACTION_RESUME_CURRENT
    simpa using hbn
  have hsch := schedule_sw ar X15 a2 R.T15 R.R15 R.act15 hu0 R.ucn R.ct15 R.ns15 R.hp15
  exact ⟨X15, a2, hdisp, finish_rr ar e16 hsch R.dq15 (R.nvm _ _ e16)⟩

/-- **(R-d) The accepted ReplyRecv fast path ends where the general path
ends**: from the dispatch state `X0`, `dispatch_syscall … SysReplyRecv` then
`finish` reach the fast path's result, given the read bundle `RRPre` and
`StoreExt` [P]. -/
theorem rr_same (hX : StoreExt st) {X0 s' : S} {a a' : A} (h : fastpath.reply_recv st ar X0 a = ok (true, s', a'))
    (hP : RRPre (L := L) ar X0 a) :
    ∃ X a'', syscall.dispatch_syscall st ar X0 a fl4_abi.syscall.SysReplyRecv = ok (X, a'') ∧
      syscall.finish st ar X a'' = ok (s', a') := by
  obtain ⟨t, rptr, ep, hct, hrc, hf⟩ := reply_recv_acc st ar h
  obtain ⟨u, usc, hC, hT⟩ := reply_recv_found_acc st ar hf
  exact rr_found_sameG ar hX unknown_ne_null hct hrc hC hT hP

omit L in
/-- **The general `syscall` on the fast entry's ReplyRecv route**: the same
prefix (the `FAULT_IP` write, trap flag clear, a native number, a passing
`budget_ok`), then `dispatch_syscall` and `finish`. -/
theorem syscall_rr_general {s s1 s2 s' X : S} {a a2 a' a'' : A} {n : I64} {t nx i1 : U64}
    (et : sched.cur_thread st s = ok t) (enx : obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1)
    (ef : obj.Tcb.flags st t s1 = ok i1)
    (c1 : ¬ (i1 &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true)
    (c2 : ¬ n < fl4_abi.syscall.SYSCALL_MIN) (c3 : ¬ n > fl4_abi.syscall.SYSCALL_MAX)
    (eb : syscall.budget_ok st ar s1 a = ok (true, s2, a2))
    (hd : syscall.dispatch_syscall st ar s2 a2 n = ok (X, a''))
    (hf : syscall.finish st ar X a'' = ok (s', a')) :
    syscall.syscall st ar s a n false = ok (false, s', a') := by
  unfold syscall.syscall
  rw [et]; simp only [bind_ok]
  rw [enx]; simp only [lift, bind_ok]
  rw [es1]; simp only [bind_ok]
  rw [ef]; simp only [lift, bind_ok, if_neg c1, if_neg c2, if_neg c3]
  rw [eb]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte, Bool.false_eq_true]
  rw [hd]; simp only [bind_ok, uncurry_apply_pair]
  rw [hf]; simp only [bind_ok, uncurry_apply_pair]

/-- `RRPre` at every dispatch state of the entry from `s` (the `FAULT_IP`
write, then a passing `budget_ok`). -/
def RRPreAtG (ty : U64) (s : S) (a : A) : Prop :=
  ∀ t nx s1 s2 a2, sched.cur_thread st s = ok t → obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
    obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
    syscall.budget_ok st ar s1 a = ok (true, s2, a2) → RRPreG (L := L) ar ty s2 a2

/-- `RRPreAtG` for an UnknownSyscall fault (m66). -/
abbrev RRPreAt (s : S) (a : A) : Prop := RRPreAtG (L := L) ar fl4_abi.consts.fault.UnknownSyscall s a

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

end

end Fl4Proofs.P1
