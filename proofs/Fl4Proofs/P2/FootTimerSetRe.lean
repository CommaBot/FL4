/-
# P2: replaying an accepted `TCB_SetTimer` local path on another store

`set_timer_replay`: if a store `st'` (in practice `PathObl.guard st R W`) answers every call of an accepted run
of `localtimer.handle_set_timer_local` on `st` the same way, at the arguments of that run, it ends the same way.
The plumbing between `set_timer_acc` (`P2/FootTimerSetAcc.lean`) and the per-call guard lemmas.

No named premises.
-/
import Fl4Proofs.P2.FootTimerSetR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type} {st st' : machine.Store S} {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **Replay** (module docstring). -/
theorem set_timer_replay {s s1 s2 s3 s4 s5 s6 s7 s8 s9 : S} {a a1 a2 a3 a4 : A} {n : I64}
    {target t cpu i i2 csc nx now dl bd cns t1 : U64} {info : msginfo.MessageInfo}
    (et : sched.cur_thread st s = ok t) (gt : sched.cur_thread st' s = sched.cur_thread st s)
    (gcpu : st'.cur_cpu = st.cur_cpu) (ecpu : st.cur_cpu s = ok cpu)
    (emi : msg.msg_info st s t = ok info) (gmi : msg.msg_info st' s t = msg.msg_info st s t)
    (cn : ¬ (n != fl4_abi.syscall.SysCall) = true)
    (ei : obj.Tcb.flags st t s = ok i) (gi : obj.Tcb.flags st' t s = obj.Tcb.flags st t s)
    (c1 : ¬ (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true)
    (c2 : ¬ (info.label != fl4_abi.label.TCBSetTimer) = true)
    (c3 : ¬ (info.extra_caps != 0#u64) = true) (c4 : ¬ info.length < 2#u64)
    (ecsc : sched.cur_sc st s = ok csc) (gcsc : sched.cur_sc st' s = sched.cur_sc st s)
    (eb : localtimer.set_timer_target_ok st s cpu target = ok true)
    (gb : localtimer.set_timer_target_ok st' s cpu target = localtimer.set_timer_target_ok st s cpu target)
    (eb1 : localtimer.current_ok st s cpu t csc = ok true)
    (gb1 : localtimer.current_ok st' s cpu t csc = localtimer.current_ok st s cpu t csc)
    (ei2 : obj.Tcb.state st t s = ok i2) (gi2 : obj.Tcb.state st' t s = obj.Tcb.state st t s)
    (c5 : ¬ (i2 != sched.TS_RUNNING) = true)
    (eb2 : sched.is_schedulable st s t = ok true)
    (gb2 : sched.is_schedulable st' s t = sched.is_schedulable st s t)
    (eb3 : localtimer.sched_quiet st s cpu = ok true)
    (gb3 : localtimer.sched_quiet st' s cpu = localtimer.sched_quiet st s cpu)
    (enx : obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx)
    (gnx : obj.Tcb.reg st' t s layout.reg.NEXT_IP = obj.Tcb.reg st t s layout.reg.NEXT_IP)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx localtimer.SYSCALL_INSN_LEN) =
      ok s1)
    (gs1 : obj.Tcb.set_reg st' t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx localtimer.SYSCALL_INSN_LEN) =
      obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx localtimer.SYSCALL_INSN_LEN))
    (eu : sched.update_timestamp st ar s1 a = ok (s2, a1))
    (gu : sched.update_timestamp st' ar s1 a = sched.update_timestamp st ar s1 a)
    (enow : sched.cur_time st s2 = ok now) (gnow : sched.cur_time st' s2 = sched.cur_time st s2)
    (edl : msg.syscall_arg st s2 t 0#u64 0#u64 = ok dl)
    (gdl : msg.syscall_arg st' s2 t 0#u64 0#u64 = msg.syscall_arg st s2 t 0#u64 0#u64)
    (ebd : msg.syscall_arg st s2 t 0#u64 1#u64 = ok bd)
    (gbd : msg.syscall_arg st' s2 t 0#u64 1#u64 = msg.syscall_arg st s2 t 0#u64 1#u64)
    (ecns : sched.consumed st s2 = ok cns) (gcns : sched.consumed st' s2 = sched.consumed st s2)
    (eb4 : sporadic.sufficient st ar s2 a1 csc cns = ok true)
    (gb4 : sporadic.sufficient st' ar s2 a1 csc cns = sporadic.sufficient st ar s2 a1 csc cns)
    (eb5 : localtimer.timer_due st s2 cpu now = ok false)
    (gb5 : localtimer.timer_due st' s2 cpu now = localtimer.timer_due st s2 cpu now)
    (eb6 : localtimer.release_due st s2 cpu = ok false)
    (gb6 : localtimer.release_due st' s2 cpu = localtimer.release_due st s2 cpu)
    (hdl : dl = 0#u64 ∨ now < dl)
    (es3 : sched.set_thread_state st s2 t sched.TS_RESTART = ok s3)
    (gs3 : sched.set_thread_state st' s2 t sched.TS_RESTART = sched.set_thread_state st s2 t sched.TS_RESTART)
    (es4 : timer.insert st s3 target dl bd = ok s4)
    (gs4 : timer.insert st' s3 target dl bd = timer.insert st s3 target dl bd)
    (es5 : msg.reply_success_empty st s4 t = ok s5)
    (gs5 : msg.reply_success_empty st' s4 t = msg.reply_success_empty st s4 t)
    (es6 : sched.set_thread_state st s5 t sched.TS_RUNNING = ok s6)
    (gs6 : sched.set_thread_state st' s5 t sched.TS_RUNNING = sched.set_thread_state st s5 t sched.TS_RUNNING)
    (es7 : sched.schedule st ar s6 a1 = ok (s7, a2))
    (gs7 : sched.schedule st' ar s6 a1 = sched.schedule st ar s6 a1)
    (es8 : sched.activate_thread st ar s7 a2 = ok (s8, a3))
    (gs8 : sched.activate_thread st' ar s7 a2 = sched.activate_thread st ar s7 a2)
    (et1 : sched.cur_thread st s8 = ok t1) (gt1 : sched.cur_thread st' s8 = sched.cur_thread st s8)
    (es9 : vcpu.check st ar s8 a3 t1 = ok (s9, a4))
    (gs9 : vcpu.check st' ar s8 a3 t1 = vcpu.check st ar s8 a3 t1) :
    localtimer.handle_set_timer_local st' ar s a n target = ok (true, s9, a4) := by
  unfold localtimer.handle_set_timer_local
  rw [gt, et, gcpu]
  simp only [bind_ok]
  rw [ecpu]
  simp only [bind_ok]
  rw [gmi, emi]
  simp only [bind_ok, lift]
  rw [num_domains_ne_one_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [if_neg cn, gi, ei]
  simp only [bind_ok]
  rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4, gcsc, ecsc]
  simp only [bind_ok]
  rw [gb, eb]
  simp only [bind_ok, ↓reduceIte]
  rw [gb1, eb1]
  simp only [bind_ok, ↓reduceIte]
  rw [gi2, ei2]
  simp only [bind_ok]
  rw [if_neg c5, gb2, eb2]
  simp only [bind_ok, ↓reduceIte]
  rw [gb3, eb3]
  simp only [bind_ok, ↓reduceIte]
  rw [gnx, enx]
  simp only [bind_ok]
  rw [gs1, es1]
  simp only [bind_ok]
  rw [gu, eu]
  simp only [bind_ok, uncurry_apply_pair]
  rw [gnow, enow]
  simp only [bind_ok]
  rw [gdl, edl]
  simp only [bind_ok]
  rw [gbd, ebd]
  simp only [bind_ok]
  rw [gcns, ecns]
  simp only [bind_ok]
  rw [gb4, eb4]
  simp only [bind_ok, ↓reduceIte]
  rw [gb5, eb5]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  rw [gb6, eb6]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  have tail : (do
      let s3 ← sched.set_thread_state st' s2 t sched.TS_RESTART
      let s4 ← timer.insert st' s3 target dl bd
      let s5 ← msg.reply_success_empty st' s4 t
      let s6 ← sched.set_thread_state st' s5 t sched.TS_RUNNING
      let (s7, a2) ← sched.schedule st' ar s6 a1
      let (s8, a3) ← sched.activate_thread st' ar s7 a2
      let t1 ← sched.cur_thread st' s8
      let (s9, a4) ← vcpu.check st' ar s8 a3 t1
      ok (true, s9, a4)) = ok (true, s9, a4) := by
    rw [gs3, es3]; simp only [bind_ok]
    rw [gs4, es4]; simp only [bind_ok]
    rw [gs5, es5]; simp only [bind_ok]
    rw [gs6, es6]; simp only [bind_ok]
    rw [gs7, es7]; simp only [bind_ok, uncurry_apply_pair]
    rw [gs8, es8]; simp only [bind_ok, uncurry_apply_pair]
    rw [gt1, et1]; simp only [bind_ok]
    rw [gs9, es9]; simp only [bind_ok, uncurry_apply_pair]
  by_cases cd : (dl != 0#u64) = true
  · rw [if_pos cd]
    have : ¬ dl <= now := by
      rcases hdl with h | h
      · simp [h] at cd
      · scalar_tac
    rw [if_neg this]; exact tail
  · rw [if_neg cd]; exact tail

end

end Fl4Proofs.P2
