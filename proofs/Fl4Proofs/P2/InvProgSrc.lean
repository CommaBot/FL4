/-
# P2 (line hpzg, generation 6): the pruned frame-cap invocation body in the generator's input form

`syscall.handle_invocation_local` (`P2/InvLP.lean`) decodes the cap at the plan's slot `p.slot` with the full
`syscall.decode_invocation`, whose call closure has `zero` / `clear_free` (untyped reset, `vspace.decode`,
`ept.decode`, `vcpu.reset_svm`), so a tree of it is not `NoZero`. On the bridge's stores and states the cap at
`p.slot` is a CNode cap (`P2/InvPrune.lean`), and `decode_invocation`'s CNode arm is `cnode.decode`, whose closure
(485 functions: Copy / Mint / Move / Mutate / Rotate / Revoke / Delete / CancelBadgedSends, `cdt.delete` with every
`finalise_cap` arm) makes no `zero` / `clear_free` call. Here, in the form `xtask/scripts/gen_prog.py` reads
(extracted-style `def`s, `GEN_EXTRA`):

* `decCNG`: `decode_invocation` with its CNode arm only (every other cap fails); `decInv_eq_CN`: equal to
  `decode_invocation` on a CNode cap (`rfl`);
* `invPostG`: the part of the body after the decode, on the decoded result as a parameter (so the generated
  equation splits a match on a variable, not on a tuple projection: lesson of `hinvIoG`);
* `invTailG` (`InvDec.invTail` with `decCNG` / `invPostG`), `invBodyG` (the body), `invBodyP` (as
  `E2E.LocalPath.F`).

No premises.
-/
import Fl4Proofs.P2.IoProgSrc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core

section
variable {S : Type}

/-- `syscall.decode_invocation` with its CNode arm only; every other cap fails. -/
def decCNG {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (lbl length : U64)
    (_slot : obj.Slot) (cap : capability.Cap) (_block _call _cd fp : Bool) (buf : U64)
    (extra : Array obj.Slot 3#usize) : Result ((core.result.Result Unit error.Exc) × S × A) := do
  match cap with
  | capability.Cap.CNode x y z w =>
    let _ ← sched.cur_thread m s
    if fp
    then
      ok (core.result.Result.Err (error.Exc.Sys (error.SysError.InvalidCapability 0#u64)), s, a)
    else cnode.decode m ar s a lbl length (capability.Cap.CNode x y z w) buf extra
  | _ => fail .panic

/-- On a CNode cap, `decode_invocation` is `decCNG`. -/
theorem decInv_eq_CN {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)
    (lbl length : U64) (slot : obj.Slot) (x y z w : U64) (block call cd fp : Bool) (buf : U64)
    (extra : Array obj.Slot 3#usize) :
    syscall.decode_invocation m ar s a lbl length slot (capability.Cap.CNode x y z w) block call cd fp buf extra =
      decCNG m ar s a lbl length slot (capability.Cap.CNode x y z w) block call cd fp buf extra := rfl

/-- The frame-cap invocation body after the decode, on the decoded result `r` as a parameter. -/
def invPostG {A : Type} (m : machine.Store S) (s3 : S) (a2 : A) (t : U64)
    (r : core.result.Result Unit error.Exc) : Result (S × A × (core.result.Result Unit error.Exc)) := do
  match r with
  | core.result.Result.Ok _ =>
    let i6 ← obj.Tcb.state m t s3
    let t1 ←
      if i6 = sched.TS_RESTART
      then
        do
        let s5 ← msg.reply_success_empty m s3 t
        sched.set_thread_state m s5 t sched.TS_RUNNING
      else ok s3
    ok (t1, a2, core.result.Result.Ok ())
  | core.result.Result.Err e =>
    let (t1, r2) ←
      match e with
      | error.Exc.Fault _ => ok (s3, core.result.Result.Ok ())
      | error.Exc.Lookup _ => ok (s3, core.result.Result.Ok ())
      | error.Exc.Sys e1 =>
        do
        let s5 ← syscall.reply_error m s3 t e1
        ok (s5, core.result.Result.Ok ())
      | error.Exc.Preempted => ok (s3, r)
    ok (t1, a2, r2)

/-- `InvDec.invTail` with `decCNG` for the decode and `invPostG` after it. -/
def invTailG {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (t : U64)
    (info : msginfo.MessageInfo) (p : localinv.Plan) : Result (Bool × S × A) := do
  let b ← localinv.is_local_label info.label
  if b
  then
    let next ← obj.Tcb.reg m t s layout.reg.NEXT_IP
    let i2 ← lift (core.num.U64.wrapping_sub next 2#u64)
    let s1 ← obj.Tcb.set_reg m t s layout.reg.FAULT_IP i2
    let (s2, a1) ← sched.update_timestamp m ar s1 a
    let csc ← sched.cur_sc m s2
    let i3 ← sched.action m s2
    if i3 != sched.ACTION_RESUME_CURRENT
    then ok (false, s2, a1)
    else
      let i4 ← obj.Tcb.yield_to m t s2
      if i4 != 0#u64
      then ok (false, s2, a1)
      else
        let i5 ← sched.consumed m s2
        let b1 ← sporadic.sufficient m ar s2 a1 csc i5
        if b1
        then
          let b2 ← fastpath.schedulable_here m s2 t
          if b2
          then
            let b3 ← localinv.Plan.still_holds m p s2
            if b3
            then
              let buf ← msg.lookup_ipc_buffer m s2 false t
              let length ←
                if info.length > msg.N_MSG_REGISTERS
                then
                  if buf = 0#u64
                  then ok msg.N_MSG_REGISTERS
                  else ok info.length
                else ok info.length
              let cap ← obj.Slot.cap m p.slot s2
              let (r, s3, a2) ← decCNG m ar s2 a1 info.label length p.slot cap true true true false buf p.extra
              let (s4, a3, r1) ← invPostG m s3 a2 t r
              let (_, s5, a4) ← syscall.after_invocation m ar s4 a3 r1
              let (s6, a5) ← syscall.finish m ar s5 a4
              ok (true, s6, a5)
            else ok (false, s2, a1)
          else ok (false, s2, a1)
        else ok (false, s2, a1)
  else ok (false, s, a)

/-- **The pruned frame-cap invocation body** (extracted argument order). -/
def invBodyG {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (number : I64)
    (p : localinv.Plan) : Result (Bool × S × A) := do
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
      then ok (false, s, a)
      else invTailG m ar s a t info p

/-- `invBodyG` as `E2E.LocalPath.F` (generic in the Arch instance). -/
abbrev invBodyP (S : Type) (number : I64) (p : localinv.Plan) : ∀ {A : Type}, machine.Arch A →
    machine.Store S → S → A → Result (Bool × S × A) :=
  fun ar m s a => invBodyG m ar s a number p

end

/-- The pure step `ept.CORES` (an `irreducible` constant, which the generator's scan of `def`s misses) never
diverges (for `SProg.liftR` in `R.ept.invalidate`). -/
@[reif_simps] theorem nd_ept_CORES : fl4_core.ept.CORES ≠ div :=
  ne_div_of_spec Fl4Proofs.P0.Consts.ept.CORES.spec

/-- A checked subtraction of a positive amount decreases (the measure of `ept.lookup_loop`, for the generated
trees). -/
theorem usub_lt {ty : UScalarTy} {x y z : UScalar ty} (e : x - y = ok z) (hy : 0 < y.val) : z.val < x.val := by
  have := UScalar.sub_equiv x y
  rw [e] at this
  simp at this
  first | omega | scalar_tac

end Fl4Proofs.P2.PathObl
