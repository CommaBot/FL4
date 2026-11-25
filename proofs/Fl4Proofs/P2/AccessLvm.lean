/-
# P2 (line lvm, gen 3): #104's local VM entries on the guarded store, their checks (`PathObl.acc` heads)

`PathObl.acc` asks that an accepted run, on the store guarded to the path's read / write sets
(`PathObl.guard st R W`, or any `GRd` store), ends as the real run. Every #104 local VM body is a block of
read-only checks (the "head") followed by the work (the "tail": `update_timestamp` or `syscall_prefix`, then
`vcpu.check` / `vcpu.enter` / `vcpu.decode`, `check_budget`, `finish`). Here each body is split as
`head (tail)` by definition (`vexit_eq`, `venter_eq`, `vinv_eq`, `vtimer_eq`: `rfl`), and each head is proved to
read only the words listed in its hypotheses: on any store answering those reads as `st`, the body equals the
real one as soon as the tail does (`*_acc_head`). So `acc` for these entries reduces to `acc` of the tail,
started at the entry state with the values the head read.

* `vcpu.get.guard`, `ntfn_quiet.guard`, `vm_running.guard`, `current_vm_ok.guard`: the helpers;
* `vexit_acc_head` (`handle_vcpu_exit_local`, fl4-sync `local_vm_exit` with `NO_IRQ`);
* `vtimer_acc_head` (`handle_vm_timer_irq_local`, `local_vm_timer_irq`);
* `venter_acc_head` (`handle_vm_enter_local`, `local_vm_syscall` `SysVMEnter`);
* `vinv_acc_head` (`handle_vcpu_invocation_local`, `local_vm_syscall` VCPU state labels).

The heads read, besides the current thread's TCB words, the node words and the current SC's `CORE` word
(all rule 1 / 3 / 5 words this core holds or the gate's, as for the timer and I/O-port paths), two VCPU words:
`v.PENDING` (exit, timer: rule 7, `lock v`'s; `pending_rperm`) and `v.TCB` (invocation: the gate's,
`OwnMapV.rpermV_vtcb`), and the bound notification's `TAIL_STATE` (rule 4, the bound thread's home core). With
rule 7 (`P2/OwnMapVcpu.lean`) every head read is permitted; under `own` alone `v.PENDING` is already gate-owned
and readable, but the tails' VCPU writes are not writable (`OwnMapV.wpermV_vcpu` is what makes them so).

No named premises (the helper and head lemmas assume only the guarded store's answers on the listed words).
-/
import Fl4Proofs.P2.FootTimerSetG
import Fl4Proofs.P2.FootTimerIrqF
import Fl4Proofs.P2.FootTimerIrqH
import Fl4Proofs.P2.AccessIo
import Fl4Proofs.P2.AccessFastRR
import Fl4Proofs.P2.OwnMapVcpu
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

/-! ## The bodies as head and tail (definitional) -/

section defs
variable {S : Type} {A : Type}

/-- `handle_vcpu_exit_local`'s work after its checks (both arms run this text). -/
def vexitTail (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (ct csc cpu : U64) :
    Result (Bool × S × A) := do
  let (s1, a1) ← sched.update_timestamp m ar s a
  let now ← sched.cur_time m s1
  let i4 ← sched.consumed m s1
  let b4 ← sporadic.sufficient m ar s1 a1 csc i4
  if b4
  then
    let b5 ← localvm.awaken_quiet m s1 cpu now
    if b5
    then
      let (s2, a2) ← vcpu.check m ar s1 a1 ct
      let (_, s3, a3) ← sched.check_budget m ar s2 a2
      let (s4, a4) ← localvm.finish m ar s3 a3
      ok (true, s4, a4)
    else ok (false, s1, a1)
  else ok (false, s1, a1)

/-- `handle_vcpu_exit_local`'s checks, the work `T` abstracted. -/
def vexitHead (m : machine.Store S) (s : S) (a : A) (v n : U64)
    (T : U64 → U64 → U64 → Result (Bool × S × A)) : Result (Bool × S × A) := do
  let ct ← sched.cur_thread m s
  let cpu ← m.cur_cpu s
  let csc ← sched.cur_sc m s
  if layout.NUM_DOMAINS != 1#u64
  then ok (false, s, a)
  else
    let i ← obj.Tcb.state m ct s
    if i != sched.TS_RUNNING_VM
    then ok (false, s, a)
    else
      if v = 0#u64
      then ok (false, s, a)
      else
        let i1 ← vcpu.bound m s ct
        if i1 != v
        then ok (false, s, a)
        else
          let i2 ← obj.Tcb.bound_ntfn m ct s
          if i2 != n
          then ok (false, s, a)
          else
            let i3 ← vcpu.get m s v vcpu.PENDING
            if i3 = 0#u64
            then
              let b ← localvm.ntfn_quiet m s n
              if b
              then
                let b1 ← localvm.current_vm_ok m s cpu ct csc
                if b1
                then
                  let b2 ← sched.is_schedulable m s ct
                  if b2
                  then
                    let b3 ← localtimer.sched_quiet m s cpu
                    if b3
                    then T ct csc cpu
                    else ok (false, s, a)
                  else ok (false, s, a)
                else ok (false, s, a)
              else ok (false, s, a)
            else
              let b ← localvm.current_vm_ok m s cpu ct csc
              if b
              then
                let b1 ← sched.is_schedulable m s ct
                if b1
                then
                  let b2 ← localtimer.sched_quiet m s cpu
                  if b2
                  then T ct csc cpu
                  else ok (false, s, a)
                else ok (false, s, a)
              else ok (false, s, a)

theorem vexit_eq (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (v n : U64) :
    localvm.handle_vcpu_exit_local m ar s a v n = vexitHead m s a v n (vexitTail m ar s a) := by
  rfl

/-- `handle_vm_enter_local`'s work after its checks. -/
def venterTail (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (ct csc cpu : U64) :
    Result (Bool × S × A) := do
  let (s1, a1) ← localvm.syscall_prefix m ar s a ct
  let now ← sched.cur_time m s1
  let i6 ← sched.consumed m s1
  let b4 ← sporadic.sufficient m ar s1 a1 csc i6
  if b4
  then
    let b5 ← localvm.awaken_quiet m s1 cpu now
    if b5
    then
      let (_, s2, a2) ← sched.check_budget_restart m ar s1 a1
      let (s3, a3) ← vcpu.enter m ar s2 a2 ct
      let (s4, a4) ← localvm.finish m ar s3 a3
      ok (true, s4, a4)
    else ok (false, s1, a1)
  else ok (false, s1, a1)

/-- `handle_vm_enter_local`'s checks, the work `T` abstracted (`virtualization` is an Arch call at the entry
Arch value, not memory). -/
def venterHead (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (number : I64) (v n : U64)
    (T : U64 → U64 → U64 → Result (Bool × S × A)) : Result (Bool × S × A) := do
  let ct ← sched.cur_thread m s
  let cpu ← m.cur_cpu s
  if layout.NUM_DOMAINS != 1#u64
  then ok (false, s, a)
  else
    if number != fl4_abi.syscall.SysVMEnter
    then ok (false, s, a)
    else
      let i ← obj.Tcb.flags m ct s
      let i1 ← lift (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS)
      if i1 != 0#u64
      then ok (false, s, a)
      else
        let i2 ← ar.virtualization a
        if i2 = 0#u64
        then ok (false, s, a)
        else
          if v = 0#u64
          then ok (false, s, a)
          else
            let i3 ← vcpu.bound m s ct
            if i3 != v
            then ok (false, s, a)
            else
              let i4 ← obj.Tcb.bound_ntfn m ct s
              if i4 != n
              then ok (false, s, a)
              else
                let b ← localvm.ntfn_quiet m s n
                if b
                then
                  let csc ← sched.cur_sc m s
                  let b1 ← localvm.current_vm_ok m s cpu ct csc
                  if b1
                  then
                    let i5 ← obj.Tcb.state m ct s
                    if i5 != sched.TS_RUNNING
                    then ok (false, s, a)
                    else
                      let b2 ← sched.is_schedulable m s ct
                      if b2
                      then
                        let b3 ← localtimer.sched_quiet m s cpu
                        if b3
                        then T ct csc cpu
                        else ok (false, s, a)
                      else ok (false, s, a)
                  else ok (false, s, a)
                else ok (false, s, a)

theorem venter_eq (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (number : I64) (v n : U64) :
    localvm.handle_vm_enter_local m ar s a number v n = venterHead m ar s a number v n (venterTail m ar s a) := by
  rfl

end defs

section defs2
variable {S : Type} {A : Type}

/-- `handle_vcpu_invocation_local`'s work after its checks (both number arms run this text). -/
def vinvTail (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (number : I64) (v : U64)
    (ct csc cpu : U64) (info : msginfo.MessageInfo) : Result (Bool × S × A) := do
  let (s1, a1) ←
    localvm.syscall_prefix m
      ar s a ct
  let now ← sched.cur_time m s1
  let i6 ← sched.consumed m s1
  let b5 ←
    sporadic.sufficient m
      ar s1 a1 csc i6
  if b5
  then
    let b6 ←
      localvm.awaken_quiet m s1
        cpu now
    if b6
    then
      let buf ←
        msg.lookup_ipc_buffer m s1
          false ct
      let r ←
        ipc.lookup_extra_caps m s1
          ct buf info
      match r with
      | core.result.Result.Ok e =>
        let length ←
          if info.length > msg.N_MSG_REGISTERS
          then
            if buf = 0#u64
            then ok msg.N_MSG_REGISTERS
            else ok info.length
          else ok info.length
        let (r1, s2, a2) ←
          vcpu.decode m
            ar s1 a1 info.label
            length v (number =
            fl4_abi.syscall.SysCall) buf e
        let (s3, a3) ←
          match r1 with
          | core.result.Result.Ok _ =>
            do
            let i7 ←
              obj.Tcb.state m ct
                s2
            if i7 = sched.TS_RESTART
            then
              let s4 ←
                if number =
                  fl4_abi.syscall.SysCall
                then
                  msg.reply_success_empty
                    m s2 ct
                else ok s2
              let s5 ←
                sched.set_thread_state
                  m s4 ct
                  sched.TS_RUNNING
              ok (s5, a2)
            else ok (s2, a2)
          | core.result.Result.Err e1 =>
            match e1 with
            | error.Exc.Fault _ => ok (s2, a2)
            | error.Exc.Lookup _ => ok (s2, a2)
            | error.Exc.Sys e2 =>
              do
              let t ←
                if number =
                  fl4_abi.syscall.SysCall
                then
                  syscall.reply_error
                    m s2 ct e2
                else ok s2
              ok (t, a2)
            | error.Exc.Preempted => ok (s2, a2)
        let (s4, a4) ←
          localvm.finish m
            ar s3 a3
        ok (true, s4, a4)
      | core.result.Result.Err _ =>
        ok (false, s1, a1)
    else ok (false, s1, a1)
  else ok (false, s1, a1)

/-- `handle_vcpu_invocation_local`'s checks, the work `T` abstracted. -/
def vinvHead (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (number : I64) (slot : obj.Slot) (v : U64)
    (T : U64 → U64 → U64 → msginfo.MessageInfo → Result (Bool × S × A)) : Result (Bool × S × A) := do
  let ct ← sched.cur_thread m s
  let cpu ← m.cur_cpu s
  let info ← msg.msg_info m s ct
  if layout.NUM_DOMAINS != 1#u64
  then ok (false, s, a)
  else
    let i ← obj.Tcb.flags m ct s
    let i1 ← lift (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS)
    if i1 != 0#u64
    then ok (false, s, a)
    else
      if number != fl4_abi.syscall.SysCall
      then
        if number != fl4_abi.syscall.SysSend
        then ok (false, s, a)
        else
          let b ← localvm.is_vcpu_state_label info.label
          if b
          then
            if info.extra_caps != 0#u64
            then ok (false, s, a)
            else
              let i2 ← ar.virtualization a
              if i2 = 0#u64
              then ok (false, s, a)
              else
                if v = 0#u64
                then ok (false, s, a)
                else
                  let c ← obj.Slot.cap m slot s
                  let b1 ←
                    core.cmp.PartialEq.ne.trait_default
                      capability.Cap.Insts.CoreCmpPartialEqCap c
                      (capability.Cap.Vcpu v)
                  if b1
                  then ok (false, s, a)
                  else
                    let i3 ← vcpu.get m s v vcpu.TCB
                    if i3 != ct
                    then ok (false, s, a)
                    else
                      let i4 ← vcpu.bound m s ct
                      if i4 != v
                      then ok (false, s, a)
                      else
                        let csc ← sched.cur_sc m s
                        let b2 ←
                          localvm.current_vm_ok m s cpu ct csc
                        if b2
                        then
                          let i5 ← obj.Tcb.state m ct s
                          if i5 != sched.TS_RUNNING
                          then ok (false, s, a)
                          else
                            let b3 ←
                              sched.is_schedulable m s ct
                            if b3
                            then
                              let b4 ←
                                localtimer.sched_quiet m s cpu
                              if b4
                              then
                                T ct csc cpu info
                              else ok (false, s, a)
                            else ok (false, s, a)
                        else ok (false, s, a)
          else ok (false, s, a)
      else
        let b ← localvm.is_vcpu_state_label info.label
        if b
        then
          if info.extra_caps != 0#u64
          then ok (false, s, a)
          else
            let i2 ← ar.virtualization a
            if i2 = 0#u64
            then ok (false, s, a)
            else
              if v = 0#u64
              then ok (false, s, a)
              else
                let c ← obj.Slot.cap m slot s
                let b1 ←
                  core.cmp.PartialEq.ne.trait_default
                    capability.Cap.Insts.CoreCmpPartialEqCap c
                    (capability.Cap.Vcpu v)
                if b1
                then ok (false, s, a)
                else
                  let i3 ← vcpu.get m s v vcpu.TCB
                  if i3 != ct
                  then ok (false, s, a)
                  else
                    let i4 ← vcpu.bound m s ct
                    if i4 != v
                    then ok (false, s, a)
                    else
                      let csc ← sched.cur_sc m s
                      let b2 ←
                        localvm.current_vm_ok m s cpu ct csc
                      if b2
                      then
                        let i5 ← obj.Tcb.state m ct s
                        if i5 != sched.TS_RUNNING
                        then ok (false, s, a)
                        else
                          let b3 ← sched.is_schedulable m s ct
                          if b3
                          then
                            let b4 ←
                              localtimer.sched_quiet m s cpu
                            if b4
                            then
                              T ct csc cpu info
                            else ok (false, s, a)
                          else ok (false, s, a)
                      else ok (false, s, a)
        else ok (false, s, a)

theorem vinv_eq (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (number : I64) (slot : obj.Slot)
    (v : U64) :
    localvm.handle_vcpu_invocation_local m ar s a number slot v =
      vinvHead m ar s a number slot v (vinvTail m ar s a number v) := by
  rfl

/-- `handle_vm_timer_irq_local`'s work after its checks. -/
def vtimerTail (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (irq : U64) (p : localtimer.TimerIrqPlan)
    (ct csc cpu : U64) : Result (Bool × S × A) := do
  let (s1, a1) ←
    sched.update_timestamp m ar
      s a
  let now ← sched.cur_time m s1
  let b5 ← localtimer.release_due m s1 cpu
  if b5
  then ok (false, s1, a1)
  else
    let i4 ← sched.consumed m s1
    let b6 ←
      sporadic.sufficient m ar
        s1 a1 csc i4
    let due ←
      localtimer.timer_due m s1 cpu now
    let ok1 ←
      if ¬ b6
      then
        if due
        then ok false
        else
          if ¬ b6
          then
            localtimer.round_robin_ok m
              ar s1 a1 cpu ct csc now
          else
            if due
            then
              do
              let b7 ←
                localtimer.fire_ok m s1 cpu
                  ct p now
              if b7
              then ok true
              else ok false
            else ok true
      else
        if ¬ b6
        then
          localtimer.round_robin_ok m
            ar s1 a1 cpu ct csc now
        else
          if due
          then
            do
            let b7 ←
              localtimer.fire_ok m s1 cpu ct
                p now
            if b7
            then ok true
            else ok false
          else ok true
    if ok1
    then
      let (s2, a2) ←
        vcpu.check m ar s1 a1
          ct
      let (_, s3, a3) ←
        sched.check_budget m ar
          s2 a2
      let (s4, a4) ←
        interrupt.handle_interrupt m
          ar s3 a3 irq
      let (s5, a5) ←
        localvm.finish m ar s4
          a4
      ok (true, s5, a5)
    else ok (false, s1, a1)

/-- `handle_vm_timer_irq_local`'s checks, the work `T` abstracted. -/
def vtimerHead (m : machine.Store S) (s : S) (a : A) (irq : U64) (p : localtimer.TimerIrqPlan) (n : U64)
    (T : U64 → U64 → U64 → Result (Bool × S × A)) : Result (Bool × S × A) := do
  let cpu ← m.cur_cpu s
  if layout.NUM_DOMAINS != 1#u64
  then ok (false, s, a)
  else
    let i ← layout.irq.MAX
    if irq > i
    then ok (false, s, a)
    else
      let i1 ← interrupt.irq_state m s irq
      if i1 != interrupt.IRQ_TIMER
      then ok (false, s, a)
      else
        let tip ← localtimer.plan_objects m s
        let b ← localtimer.same_plan tip p
        if b
        then
          let ct ← sched.cur_thread m s
          let csc ← sched.cur_sc m s
          let i2 ← obj.Tcb.state m ct s
          if i2 != sched.TS_RUNNING_VM
          then ok (false, s, a)
          else
            let i3 ← obj.Tcb.bound_ntfn m ct s
            if i3 != n
            then ok (false, s, a)
            else
              let b1 ← localvm.ntfn_quiet m s n
              if b1
              then
                let b2 ← localvm.vm_running m s ct
                if b2
                then
                  let b3 ←
                    localvm.current_vm_ok m s cpu ct csc
                  if b3
                  then
                    let b4 ← localtimer.sched_quiet m s cpu
                    if b4
                    then
                      T ct csc cpu
                    else ok (false, s, a)
                  else ok (false, s, a)
                else ok (false, s, a)
              else ok (false, s, a)
        else ok (false, s, a)

theorem vtimer_eq (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (irq : U64)
    (p : localtimer.TimerIrqPlan) (n : U64) :
    localvm.handle_vm_timer_irq_local m ar s a irq p n = vtimerHead m s a irq p n (vtimerTail m ar s a irq p) := by
  rfl

end defs2

/-! ## The helpers on a guarded store -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

theorem vcpu.get.guard (s : S) (v off : U64) (h : R (core.num.U64.wrapping_add v off)) :
    vcpu.get gS s v off = vcpu.get st s v off := by
  unfold vcpu.get
  simp only [lift, bind_ok]
  exact PathObl.gst_read h

theorem ntfn_quiet.guard (s : S) (n : U64)
    (h : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE)) :
    localvm.ntfn_quiet gS s n = localvm.ntfn_quiet st s n := by
  unfold localvm.ntfn_quiet
  by_cases h0 : n = 0#u64
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0, PathObl.obj.Ntfn.state.guard n s (h h0)]

theorem vm_running.guard (s : S) (ct : U64) (h1 : R (core.num.U64.wrapping_add ct 3664#u64))
    (h2 : L.mem s (core.num.U64.wrapping_add ct 3664#u64) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add ct 3664#u64)) vcpu.PENDING)) :
    localvm.vm_running gS s ct = localvm.vm_running st s ct := by
  unfold localvm.vm_running
  rw [vcpu.bound.guardT s ct h1]
  have e : vcpu.bound st s ct = ok (L.mem s (core.num.U64.wrapping_add ct 3664#u64)) := by
    exact eq_of_spec_fd (vcpu.bound.spec (L := L) s ct)
  rw [e]
  simp only [bind_ok]
  by_cases h0 : L.mem s (core.num.U64.wrapping_add ct 3664#u64) = 0#u64
  · simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  · have hb : (L.mem s (core.num.U64.wrapping_add ct 3664#u64) != 0#u64) = true := bne_iff_ne.mpr h0
    rw [if_pos hb, if_pos hb, vcpu.get.guard s _ _ (h2 h0)]

theorem current_vm_ok.guard (s : S) (cpu ct csc : U64) (h1 : R (affA ct)) (h3 : R (yieldA ct))
    (h5 : R (scA ct)) (h7 : R (scCoreA csc)) (h8 : R (L.nodeAt s (L.cpu s) layout.node.IDLE_THREAD))
    (h9 : R (domA ct)) (h10 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN)) :
    localvm.current_vm_ok gS s cpu ct csc = localvm.current_vm_ok st s cpu ct csc := by
  unfold localvm.current_vm_ok
  rw [PathObl.sched.idle_thread.guard s h8, PathObl.obj.Tcb.affinity.guard ct s h1,
    PathObl.obj.Tcb.yield_to.guard ct s h3, PathObl.obj.Tcb.sc.guard ct s h5, PathObl.obj.Sc.cpu.guard csc s h7,
    PathObl.obj.Tcb.domain.guard ct s h9, PathObl.sched.cur_domain.guard s h10]

/-- The words the VM heads read of the current thread `ct`, its SC and the node / kernel state (as
`current_ok.guard` / `sched_quiet.guard` / `is_schedulable.guard` read them). -/
structure LvmRd (st : machine.Store S) [L : LawfulStore st] (R : U64 → Prop) (s : S) (ct csc : U64) : Prop where
  cur : R (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
  curSc : R (L.nodeAt s (L.cpu s) layout.node.CUR_SC)
  vcpu : R (core.num.U64.wrapping_add ct 3664#u64)
  bntfn : R (core.num.U64.wrapping_add ct 3368#u64)
  aff : R (affA ct)
  yld : R (yieldA ct)
  sc : R (scA ct)
  scCore : R (scCoreA csc)
  idle : R (L.nodeAt s (L.cpu s) layout.node.IDLE_THREAD)
  dom : R (domA ct)
  curDom : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN)
  state : R (stA ct)
  maxA : R (maxA (L.mem s (scA ct)))
  inq : R (inqA ct)
  act : R (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)
  domTime : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME)
  ipi : R (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING)

/-- **The checks of `handle_vcpu_exit_local` read only the listed words**: on a store answering them as
`st`, the head with any two tails that agree at the values read is the real head. -/
theorem vexitHead.guard (s : S) {A : Type} (a : A) (v n csc : U64) (hcsc : sched.cur_sc st s = ok csc)
    (hR : LvmRd st R s (L.curW s) csc)
    (hp : v ≠ 0#u64 → R (core.num.U64.wrapping_add v vcpu.PENDING))
    (hn : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    {T1 T2 : U64 → U64 → U64 → Result (Bool × S × A)}
    (hT : T1 (L.curW s) csc (L.cpu s) = T2 (L.curW s) csc (L.cpu s)) :
    vexitHead gS s a v n T1 = vexitHead st s a v n T2 := by
  unfold vexitHead
  rw [PathObl.sched.cur_thread.guard s hR.cur, cur_thread_ok, PathObl.gst_cur_cpu, L.cur_cpu_eq,
    PathObl.sched.cur_sc.guard s hR.curSc, hcsc]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.state.guard _ s hR.state, vcpu.bound.guardT s _ hR.vcpu,
    PathObl.obj.Tcb.bound_ntfn.guard _ s hR.bntfn, ntfn_quiet.guard s n hn,
    current_vm_ok.guard s _ _ _ hR.aff hR.yld hR.sc hR.scCore hR.idle hR.dom hR.curDom,
    PathObl.sched.is_schedulable.guard s _ hR.state hR.sc hR.maxA hR.inq,
    sched_quiet.guard s hR.act hR.domTime hR.ipi, hT]
  by_cases hv : v = 0#u64
  · simp only [hv, ↓reduceIte]
  · rw [vcpu.get.guard s v _ (hp hv)]

/-- **`PathObl.acc` of `handle_vcpu_exit_local` reduces to its tail** (module docstring). -/
theorem vexit_acc_head {A : Type} (ar : machine.Arch A) (s : S) (a : A) (v n csc : U64)
    (hcsc : sched.cur_sc st s = ok csc) (hR : LvmRd st R s (L.curW s) csc)
    (hp : v ≠ 0#u64 → R (core.num.U64.wrapping_add v vcpu.PENDING))
    (hn : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (hT : vexitTail gS ar s a (L.curW s) csc (L.cpu s) = vexitTail st ar s a (L.curW s) csc (L.cpu s)) :
    localvm.handle_vcpu_exit_local gS ar s a v n = localvm.handle_vcpu_exit_local st ar s a v n := by
  rw [vexit_eq, vexit_eq]
  exact vexitHead.guard s a v n csc hcsc hR hp hn hT

/-- **The checks of `handle_vm_enter_local` read only the listed words** (and the flags word). -/
theorem venterHead.guard {A : Type} (ar : machine.Arch A) (s : S) (a : A) (number : I64) (v n csc : U64)
    (hcsc : sched.cur_sc st s = ok csc) (hR : LvmRd st R s (L.curW s) csc)
    (hf : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (hn : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    {T1 T2 : U64 → U64 → U64 → Result (Bool × S × A)}
    (hT : T1 (L.curW s) csc (L.cpu s) = T2 (L.curW s) csc (L.cpu s)) :
    venterHead gS ar s a number v n T1 = venterHead st ar s a number v n T2 := by
  unfold venterHead
  rw [PathObl.sched.cur_thread.guard s hR.cur, cur_thread_ok, PathObl.gst_cur_cpu, L.cur_cpu_eq]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.flags.guard _ s hf, vcpu.bound.guardT s _ hR.vcpu,
    PathObl.obj.Tcb.bound_ntfn.guard _ s hR.bntfn, ntfn_quiet.guard s n hn,
    PathObl.sched.cur_sc.guard s hR.curSc, hcsc]
  simp only [bind_ok]
  rw [current_vm_ok.guard s _ _ _ hR.aff hR.yld hR.sc hR.scCore hR.idle hR.dom hR.curDom,
    PathObl.obj.Tcb.state.guard _ s hR.state,
    PathObl.sched.is_schedulable.guard s _ hR.state hR.sc hR.maxA hR.inq,
    sched_quiet.guard s hR.act hR.domTime hR.ipi, hT]

/-- **`PathObl.acc` of `handle_vm_enter_local` reduces to its tail.** -/
theorem venter_acc_head {A : Type} (ar : machine.Arch A) (s : S) (a : A) (number : I64) (v n csc : U64)
    (hcsc : sched.cur_sc st s = ok csc) (hR : LvmRd st R s (L.curW s) csc)
    (hf : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (hn : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (hT : venterTail gS ar s a (L.curW s) csc (L.cpu s) = venterTail st ar s a (L.curW s) csc (L.cpu s)) :
    localvm.handle_vm_enter_local gS ar s a number v n = localvm.handle_vm_enter_local st ar s a number v n := by
  rw [venter_eq, venter_eq]
  exact venterHead.guard ar s a number v n csc hcsc hR hf hn hT

/-- **The checks of `handle_vcpu_invocation_local` read only the listed words** (message info, flags, the
slot fl4-sync found, `v.TCB`, and `LvmRd`'s). -/
theorem vinvHead.guard {A : Type} (ar : machine.Arch A) (s : S) (a : A) (number : I64) (slot : obj.Slot)
    (v csc : U64) (info : msginfo.MessageInfo) (hcsc : sched.cur_sc st s = ok csc)
    (hinfo : msg.msg_info st s (L.curW s) = ok info) (hR : LvmRd st R s (L.curW s) csc)
    (hmi : R (regA (L.curW s) layout.reg.MSG_INFO)) (hf : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (hsl : R slot) (hsl8 : R (core.num.U64.wrapping_add slot 8#u64))
    (hvt : R (core.num.U64.wrapping_add v vcpu.TCB))
    {T1 T2 : U64 → U64 → U64 → msginfo.MessageInfo → Result (Bool × S × A)}
    (hT : T1 (L.curW s) csc (L.cpu s) info = T2 (L.curW s) csc (L.cpu s) info) :
    vinvHead gS ar s a number slot v T1 = vinvHead st ar s a number slot v T2 := by
  unfold vinvHead
  rw [PathObl.sched.cur_thread.guard s hR.cur, cur_thread_ok, PathObl.gst_cur_cpu, L.cur_cpu_eq]
  simp only [bind_ok]
  rw [PathObl.msg.msg_info.guard s _ hmi, hinfo]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.flags.guard _ s hf, PathObl.obj.Slot.cap.guard slot s hsl hsl8, vcpu.get.guard s v _ hvt,
    vcpu.bound.guardT s _ hR.vcpu, PathObl.sched.cur_sc.guard s hR.curSc, hcsc]
  simp only [bind_ok]
  rw [current_vm_ok.guard s _ _ _ hR.aff hR.yld hR.sc hR.scCore hR.idle hR.dom hR.curDom,
    PathObl.obj.Tcb.state.guard _ s hR.state,
    PathObl.sched.is_schedulable.guard s _ hR.state hR.sc hR.maxA hR.inq,
    sched_quiet.guard s hR.act hR.domTime hR.ipi, hT]

/-- **`PathObl.acc` of `handle_vcpu_invocation_local` reduces to its tail.** -/
theorem vinv_acc_head {A : Type} (ar : machine.Arch A) (s : S) (a : A) (number : I64) (slot : obj.Slot)
    (v csc : U64) (info : msginfo.MessageInfo) (hcsc : sched.cur_sc st s = ok csc)
    (hinfo : msg.msg_info st s (L.curW s) = ok info) (hR : LvmRd st R s (L.curW s) csc)
    (hmi : R (regA (L.curW s) layout.reg.MSG_INFO)) (hf : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (hsl : R slot) (hsl8 : R (core.num.U64.wrapping_add slot 8#u64))
    (hvt : R (core.num.U64.wrapping_add v vcpu.TCB))
    (hT : vinvTail gS ar s a number v (L.curW s) csc (L.cpu s) info =
      vinvTail st ar s a number v (L.curW s) csc (L.cpu s) info) :
    localvm.handle_vcpu_invocation_local gS ar s a number slot v =
      localvm.handle_vcpu_invocation_local st ar s a number slot v := by
  rw [vinv_eq, vinv_eq]
  exact vinvHead.guard ar s a number slot v csc info hcsc hinfo hR hmi hf hsl hsl8 hvt hT

/-- **The checks of `handle_vm_timer_irq_local` read only the listed words** (the IRQ state word, the timer
plan's words as `plan_objects.guard`, `LvmRd`'s, the bound VCPU's `PENDING`). -/
theorem vtimerHead.guard (s : S) {A : Type} (a : A) (irq : U64) (p : localtimer.TimerIrqPlan) (n csc : U64)
    {i : U64} (hi : interrupt.state_off irq = ok i) (hirq : R (core.num.U64.wrapping_add (L.ksb s) i))
    (hp1 : R (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))
    (hp2 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      PlanTm st R s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))
    (hcsc : sched.cur_sc st s = ok csc) (hR : LvmRd st R s (L.curW s) csc)
    (hvp : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64)) vcpu.PENDING))
    (hn : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    {T1 T2 : U64 → U64 → U64 → Result (Bool × S × A)}
    (hT : T1 (L.curW s) csc (L.cpu s) = T2 (L.curW s) csc (L.cpu s)) :
    vtimerHead gS s a irq p n T1 = vtimerHead st s a irq p n T2 := by
  unfold vtimerHead
  rw [PathObl.gst_cur_cpu, L.cur_cpu_eq]
  simp only [bind_ok]
  rw [Fl4Proofs.P2.interrupt.irq_state.guard s irq hi hirq, plan_objects.guard hp1 hp2,
    PathObl.sched.cur_thread.guard s hR.cur, cur_thread_ok, PathObl.sched.cur_sc.guard s hR.curSc, hcsc]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.state.guard _ s hR.state, PathObl.obj.Tcb.bound_ntfn.guard _ s hR.bntfn,
    ntfn_quiet.guard s n hn, vm_running.guard s _ hR.vcpu hvp,
    current_vm_ok.guard s _ _ _ hR.aff hR.yld hR.sc hR.scCore hR.idle hR.dom hR.curDom,
    sched_quiet.guard s hR.act hR.domTime hR.ipi, hT]

/-- **`PathObl.acc` of `handle_vm_timer_irq_local` reduces to its tail.** -/
theorem vtimer_acc_head {A : Type} (ar : machine.Arch A) (s : S) (a : A) (irq : U64) (p : localtimer.TimerIrqPlan)
    (n csc : U64) {i : U64} (hi : interrupt.state_off irq = ok i) (hirq : R (core.num.U64.wrapping_add (L.ksb s) i))
    (hp1 : R (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))
    (hp2 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      PlanTm st R s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))
    (hcsc : sched.cur_sc st s = ok csc) (hR : LvmRd st R s (L.curW s) csc)
    (hvp : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64)) vcpu.PENDING))
    (hn : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (hT : vtimerTail gS ar s a irq p (L.curW s) csc (L.cpu s) = vtimerTail st ar s a irq p (L.curW s) csc (L.cpu s)) :
    localvm.handle_vm_timer_irq_local gS ar s a irq p n = localvm.handle_vm_timer_irq_local st ar s a irq p n := by
  rw [vtimer_eq, vtimer_eq]
  exact vtimerHead.guard s a irq p n csc hi hirq hp1 hp2 hcsc hR hvp hn hT

end

/-! ## Rule 7 for the heads' VCPU reads -/

section
open OwnMapV
variable {K : KLayoutV}

/-- **`read_own` of `v.PENDING`** for a path holding `lock v` with `v` bound: the exit / timer heads read it
after checking `ct.VCPU = v`, and `v.TCB = ct ≠ 0` by P1's VCPU binding invariant (`QueueVcpuLink`). -/
theorem pending_rperm (hK : RegionOKV K) {m : U64 → U64} {v c : U64} {lk : U64 → Prop} (hv : v ∈ K.vcpus)
    (hpv : (OwnMap.fld v oVPENDING).val = v.val + 20520) (hb : m (OwnMap.fld v oVTCB) ≠ 0#u64) (hl : lk v) :
    PathObl.RPerm (ownV K) c lk m (OwnMap.fld v oVPENDING) :=
  rpermV_vcpu hK (vpending_in hK hv hpv).1 (vpending_in hK hv hpv).2 hb hl

/-- **`write_own` of `v.PENDING`** (the tails' `vcpu.report` / `vcpu.enter` writes): held by the path. -/
theorem pending_wperm (hK : RegionOKV K) {m : U64 → U64} {v c : U64} {lk : U64 → Prop} (hv : v ∈ K.vcpus)
    (hpv : (OwnMap.fld v oVPENDING).val = v.val + 20520) (hb : m (OwnMap.fld v oVTCB) ≠ 0#u64) (hl : lk v) :
    PathObl.WPerm (ownV K) c lk m (OwnMap.fld v oVPENDING) :=
  wpermV_vcpu hK (vpending_in hK hv hpv).1 (vpending_in hK hv hpv).2 hb hl

end

end Fl4Proofs.P2
