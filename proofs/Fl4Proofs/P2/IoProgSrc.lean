/-
# P2: the pruned I/O port body in the generator's input form (line hpzg)

`xtask/scripts/gen_prog.py` reads extracted-style definitions (`def f (m : machine.Store S) (ar :
machine.Arch A) (s : S) (a : A) … : Result … := do …`). Of the pruned I/O port body (`IoPrune`), `ioTailP`
already has that form; `decIo` (a `Std.bind` term), `hinvIo` (a match on a tuple projection) and `ioBodyP`
(Arch-generic `∀ {A}` signature) do not. Here are the same bodies in that form, and the (definitional) equations:

* `decIoG` / `decIo_eq_G` (`@[reif_simps]`, so the generated equation of `hinvIoG` meets `decIoG`);
* `hinvPost` / `hinvIoG` / `hinvIo_eq_G`: `hinvIo` with its tail after `decIo` a function of the decoded
  result (a match on a parameter, which the generated equation proof splits cleanly);
* `ioBodyG` / `ioBodyP_eq_G`;
* `nd_is_ok`: the pure step `core.result.Result.is_ok` never diverges (for `interp_liftR`).

No premises.
-/
import Fl4Proofs.P2.IoPrune
import Fl4Proofs.P2.ProgGenBase
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core

section
variable {S : Type}

/-- `decIo` in do form. -/
def decIoG {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (lbl length : U64)
    (_slot : obj.Slot) (cap : capability.Cap) (_block call _cd _fp : Bool) (buf : U64)
    (_extra : Array obj.Slot 3#usize) : Result ((core.result.Result Unit error.Exc) × S × A) := do
  match cap with
  | capability.Cap.IoPort first last x =>
    let _ ← sched.cur_thread m s
    ioport.decode m ar s a lbl length (capability.Cap.IoPort first last x) call buf
  | _ => fail .panic

@[reif_simps] theorem decIo_eq_G {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)
    (lbl length : U64) (slot : obj.Slot) (cap : capability.Cap) (block call cd fp : Bool) (buf : U64)
    (extra : Array obj.Slot 3#usize) :
    decIo m ar s a lbl length slot cap block call cd fp buf extra =
      decIoG m ar s a lbl length slot cap block call cd fp buf extra := by
  cases cap <;> rfl

/-- The part of `hinvIo` after `decIo`, on the decoded result `r3` as a parameter (so the generated
equation splits a match on a variable, not on a projection). -/
def hinvPost {A : Type} (m : machine.Store S) (s1 : S) (a1 : A) (t : U64) (is_call : Bool)
    (r3 : core.result.Result Unit error.Exc) : Result ((core.result.Result Unit error.Exc) × S × A) := do
  match r3 with
  | core.result.Result.Ok _ =>
    let i ← obj.Tcb.state m t s1
    if i = sched.TS_RESTART
    then
      let s2 ←
        if is_call
        then msg.reply_success_empty m s1 t
        else ok s1
      let s3 ← sched.set_thread_state m s2 t sched.TS_RUNNING
      ok (core.result.Result.Ok (), s3, a1)
    else ok (core.result.Result.Ok (), s1, a1)
  | core.result.Result.Err e1 =>
    match e1 with
    | error.Exc.Fault _ => ok (core.result.Result.Ok (), s1, a1)
    | error.Exc.Lookup _ => ok (core.result.Result.Ok (), s1, a1)
    | error.Exc.Sys e2 =>
      if is_call
      then
        let s2 ← syscall.reply_error m s1 t e2
        ok (core.result.Result.Ok (), s2, a1)
      else ok (core.result.Result.Ok (), s1, a1)
    | error.Exc.Preempted => ok (r3, s1, a1)

/-- `hinvIo` with its tail as `hinvPost`. -/
def hinvIoG {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (is_call : Bool)
    (blocking : Bool) (can_donate : Bool) (first_phase : Bool) (cptr : U64) :
    Result ((core.result.Result Unit error.Exc) × S × A) := do
  let t ← sched.cur_thread m s
  let info ← msg.msg_info m s t
  let r ← cspace.lookup_slot m s t cptr
  match r with
  | core.result.Result.Ok r1 =>
    let cap ← obj.Slot.cap m r1.slot s
    let buf ← msg.lookup_ipc_buffer m s false t
    let r2 ← ipc.lookup_extra_caps m s t buf info
    match r2 with
    | core.result.Result.Ok e =>
      let length ←
        if info.length > msg.N_MSG_REGISTERS
        then if buf = 0#u64
             then ok msg.N_MSG_REGISTERS
             else ok info.length
        else ok info.length
      let (r3, s1, a1) ←
        decIoG m ar s a info.label length r1.slot cap blocking is_call can_donate first_phase buf e
      hinvPost m s1 a1 t is_call r3
    | core.result.Result.Err f =>
      if blocking
      then
        let (s1, a1) ← faults.handle_fault m ar s a t f
        ok (core.result.Result.Ok (), s1, a1)
      else ok (core.result.Result.Ok (), s, a)
  | core.result.Result.Err lf =>
    if blocking
    then
      let (s1, a1) ← faults.handle_fault m ar s a t (error.Fault.Cap cptr false lf)
      ok (core.result.Result.Ok (), s1, a1)
    else ok (core.result.Result.Ok (), s, a)

@[reif_simps] theorem hinvIo_eq_G {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64) :
    hinvIo m ar s a is_call blocking can_donate first_phase cptr =
      hinvIoG m ar s a is_call blocking can_donate first_phase cptr := by
  unfold hinvIo hinvIoG
  simp only [decIo_eq_G]
  rfl

/-- `Result.is_ok` (a pure step of `ioport.invocation_ok`) never diverges. -/
@[reif_simps] theorem nd_is_ok {T E : Type} (x : core.result.Result T E) : core.result.Result.is_ok x ≠ div := by
  cases x <;> simp [core.result.Result.is_ok]

/-- `ioBodyP` with the extracted argument order. -/
def ioBodyG {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (number : I64) :
    Result (Bool × S × A) := do
  let t ← sched.cur_thread m s
  let info ← msg.msg_info m s t
  if layout.NUM_DOMAINS != 1#u64
  then ok (false, s, a)
  else
    let i ← obj.Tcb.flags m t s
    let i1 ← lift (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS)
    if i1 != 0#u64
    then ok (false, s, a)
    else
      if number != fl4_abi.syscall.SysCall
      then
        if number != fl4_abi.syscall.SysSend
        then ok (false, s, a)
        else ioTailP m ar s a t info number
      else ioTailP m ar s a t info number

theorem ioBodyP_eq_G {A : Type} (number : I64) (ar : machine.Arch A) (m : machine.Store S) (s : S) (a : A) :
    ioBodyP S number ar m s a = ioBodyG m ar s a number := rfl

end

end Fl4Proofs.P2.PathObl
