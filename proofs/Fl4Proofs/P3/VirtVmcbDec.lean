/-
P3x for virtualization (line virt, gen 16, item 4): **WriteVMCB's extracted decode** — as gen 14's
`decode_wrmsr_eq` (P3/VirtMsrDec) for WriteMSR.

* `wrvmcbTail`: FL4's WriteVMCB arm after the decode's prefix (vcpu.rs l. 934-950): `old` (the word at `f` when
  `f < svm::END` and 8-aligned, else 0), `sanitize_vmcb`'s verdict, and on `Ok val` the store `set(v, f, val)`, for
  CR0 / CR3 / CR4 / EFER / G_PAT `set(v, SVM_CPU, 0)`, for RAX `set(v, REGS, val)`, then `reply`; on `Err` the error
  with the state after the stall — copied from the extracted `vcpu.decode`.
* **`decode_wrvmcb_eq`**: for `lbl = X86VCPUWriteVMCB` past the length check (`¬ length < 2`), the extracted
  `vcpu.decode` is the decode's prefix (`stall`, `cur_thread`, `virtualization`, the two syscall arguments) and then,
  on the SVM backend (`i = 2`), `wrvmcbTail`; on VMX the `illegal` error. So gen 15's store half
  (`vmcbStore_svm`, P3/VirtVmcbStore) and gen 12's verdict (`sanitize_vmcb_rel`, P3/VirtSanSvm) are statements about
  the pieces of FL4's decode itself.

No premise (no [J]/[P]/[W]). New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtMsrDec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtVmcbDec
open fl4_core Fl4Proofs.P3.VirtMsrDec

section
variable {S : Type} {st : machine.Store S} {A : Type} {ar : machine.Arch A}

/-- FL4's WriteVMCB after the decode's prefix (module docstring; the extracted arm). -/
def wrvmcbTail (st : machine.Store S) (ar : machine.Arch A) (s1 : S) (a1 : A) (v f value : U64) (call : Bool) :
    Result ((core.result.Result Unit error.Exc) × S × A) := do
  let i1 ← vcpu.svm.END
  let old ←
    if f < i1
    then
      do
      let i2 ← lift (f &&& 7#u64)
      if i2 = 0#u64
      then vcpu.get st s1 v f
      else ok 0#u64
    else ok 0#u64
  let r ← vcpu.sanitize_vmcb ar a1 f old value
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s2 ← vcpu.set st s1 v f val
    let b ←
      match f with
      | 1368#uscalar => ok true
      | 1360#uscalar => ok true
      | 1352#uscalar => ok true
      | 1232#uscalar => ok true
      | 1640#uscalar => ok true
      | _ => ok false
    let s3 ←
      if b
      then vcpu.set st s2 v vcpu.SVM_CPU 0#u64
      else ok s2
    let i2 ← vcpu.svm.RAX
    let s4 ←
      if f = i2
      then vcpu.set st s3 v vcpu.REGS val
      else ok s3
    let s5 ← vcpu.reply st s4 call val
    ok (core.result.Result.Ok (), s5, a1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame error.Exc) residual
    ok (r1, s1, a1)

set_option maxHeartbeats 8000000 in
/-- **The extracted `vcpu.decode` on `X86VCPUWriteVMCB`** (module docstring). -/
theorem decode_wrvmcb_eq (s : S) (a : A) (length v : U64) (call : Bool) (buf : U64)
    (ex : Aeneas.Std.Array obj.Slot 3#usize) (hlen : ¬ length < 2#u64) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteVMCB length v call buf ex =
      vcpu.stall st ar s a v >>= fun p => (do
        let ct ← sched.cur_thread st p.1
        let i ← ar.virtualization p.2
        let f ← if length > 0#u64 then msg.syscall_arg st p.1 ct buf 0#u64 else ok 0#u64
        let value ← if length > 1#u64 then msg.syscall_arg st p.1 ct buf 1#u64 else ok 0#u64
        if i = 2#u64 then wrvmcbTail st ar p.1 p.2 v f value call
        else do
          let r ← error.illegal Unit
          ok (r, p.1, p.2)) := by
  unfold vcpu.decode
  simp (config := { decide := true }) only [fl4_abi.label.X86VCPUSetTCB, fl4_abi.label.X86VCPUWriteRegisters,
    fl4_abi.label.X86VCPUFlushTLB, fl4_abi.label.X86VCPUReadVMCS, fl4_abi.label.X86VCPUWriteVMCS,
    fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUWriteVMCB, ite_true, ite_false, if_true, if_false, hlen]
  refine bind_ext fun x => ?_
  obtain ⟨s1, a1⟩ := x
  refine bind_ext (m := sched.cur_thread st s1) fun ct => ?_
  refine bind_ext (m := ar.virtualization a1) fun i => ?_
  refine bind_ext fun f => ?_
  refine bind_ext fun value => ?_
  rfl

end
end Fl4Proofs.P3.VirtVmcbDec
