/-
# P2 (line pte, generation 10): the pruned PageMap invocation body in the generator's input form

`syscall.handle_invocation_local` decodes the cap at the plan's slot with the full `syscall.decode_invocation`
(`P2/InvProgSrc.lean`: its closure has `zero` / `clear_free`). On the PageMap arm's states the cap at `p.slot` is a
small RAM frame cap (`plan_with_mapF`, `P2/InvPmPlan.lean`) and the label is `X86PageMap`, so the decode is
`decode_invocation`'s Frame arm → `vspace.decode` → `vspace.decode_frame` at `X86PageMap` →
`vspace.decode_page_map` (Rust `crates/fl4-core/src/arch/x86_64/vspace.rs`), whose closure (`check_vspace`,
`page_entry_slot`, `frame_address`, `make_user_page`, `set_cap`, `write_mapping` with `invalidate_page` /
`invalidate_asid`) makes no `zero` / `clear_free` call. Here, in the form `xtask/scripts/gen_prog.py` reads:

* `decPmG`: `decode_invocation` cut to the Frame arm at `X86PageMap` (every other cap or label fails);
  **`decInv_eq_Pm`**: equal to `decode_invocation` on a Frame cap at `X86PageMap`;
* `invTailPmG`, `invBodyPmG`, `invBodyPmP`: `InvProgSrc`'s `invTailG` / `invBodyG` / `invBodyP` with `decPmG`
  (the post-decode tail `invPostG` is shared).

The decode is kept whole below `decode_page_map` (Large / Huge sizes included): the arm's restriction to a small
frame is a fact of the entry (`plan_with_mapF`), not of the tree. No premises.
-/
import Fl4Proofs.P2.InvProgSrc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core

section
variable {S : Type}

/-- `syscall.decode_invocation` cut to its Frame arm at `X86PageMap`; every other cap or label fails. -/
def decPmG {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (lbl length : U64)
    (slot : obj.Slot) (cap : capability.Cap) (_block _call _cd _fp : Bool) (buf : U64)
    (extra : Array obj.Slot 3#usize) : Result ((core.result.Result Unit error.Exc) × S × A) := do
  match cap with
  | capability.Cap.Frame ptr size rights is_device mapped is_ept asid vaddr =>
    let _ ← sched.cur_thread m s
    let _ ← sched.cur_thread m s
    if lbl = fl4_abi.label.X86PageMap
    then
      if mapped
      then
        if is_ept
        then
          let r ← error.invalid_cap Unit 0#u64
          ok (r, s, a)
        else
          vspace.decode_page_map m ar s a length slot
            { ptr, size, rights, is_device, mapped, is_ept, asid, vaddr } buf extra
      else
        vspace.decode_page_map m ar s a length slot
          { ptr, size, rights, is_device, mapped, is_ept, asid, vaddr } buf extra
    else fail .panic
  | _ => fail .panic

/-- The two labels differ. -/
theorem lbl_pm_ne_ept : fl4_abi.label.X86PageMap ≠ fl4_abi.label.X86PageMapEPT := by
  simp [fl4_abi.label.X86PageMap, fl4_abi.label.X86PageMapEPT]

/-- **On a Frame cap at `X86PageMap`, `decode_invocation` is `decPmG`.** -/
theorem decInv_eq_Pm {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)
    (length : U64) (slot : obj.Slot) (ptr : U64) (size : capability.FrameSize) (rights : U64)
    (is_device mapped is_ept : Bool) (asid vaddr : U64) (block call cd fp : Bool) (buf : U64)
    (extra : Array obj.Slot 3#usize) :
    syscall.decode_invocation m ar s a fl4_abi.label.X86PageMap length slot
        (capability.Cap.Frame ptr size rights is_device mapped is_ept asid vaddr) block call cd fp buf extra =
      decPmG m ar s a fl4_abi.label.X86PageMap length slot
        (capability.Cap.Frame ptr size rights is_device mapped is_ept asid vaddr) block call cd fp buf extra := by
  unfold syscall.decode_invocation vspace.decode vspace.decode_frame decPmG
  simp only [vspace.as_frame, bind_ok, if_neg lbl_pm_ne_ept, if_true]

/-- `InvDec.invTail` with `decPmG` for the decode and `invPostG` after it. -/
def invTailPmG {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (t : U64)
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
              let (r, s3, a2) ← decPmG m ar s2 a1 info.label length p.slot cap true true true false buf p.extra
              let (s4, a3, r1) ← invPostG m s3 a2 t r
              let (_, s5, a4) ← syscall.after_invocation m ar s4 a3 r1
              let (s6, a5) ← syscall.finish m ar s5 a4
              ok (true, s6, a5)
            else ok (false, s2, a1)
          else ok (false, s2, a1)
        else ok (false, s2, a1)
  else ok (false, s, a)

/-- **The pruned PageMap invocation body** (extracted argument order). -/
def invBodyPmG {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (number : I64)
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
      else invTailPmG m ar s a t info p

/-- `invBodyPmG` as `E2E.LocalPath.F` (generic in the Arch instance). -/
abbrev invBodyPmP (S : Type) (number : I64) (p : localinv.Plan) : ∀ {A : Type}, machine.Arch A →
    machine.Store S → S → A → Result (Bool × S × A) :=
  fun ar m s a => invBodyPmG m ar s a number p

end

end Fl4Proofs.P2.PathObl
