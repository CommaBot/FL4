/-
P3x for virtualization (line virt, gen 14, item 2): **gen 13's WriteMSR transcription is the extracted arm** —
removes the narrowing of `VirtMsrEq.fl4WriteMsr_rel` (which was stated over a hand transcription of FL4
`vcpu::decode`'s WriteMSR arm, vcpu.rs l. 978-1006).

* **`decode_wrmsr_eq`**: for `lbl = X86VCPUWriteMSR` past the length check (`¬ length < 2`), the extracted
  `vcpu.decode` — all its inlined copies of the MSR arm (the `f = 0x485` split duplicates it, the read/write label
  test is inlined inside each; the three canonical-MSR tests are three copies of the same tail) — is exactly: the
  decode's prefix (`stall`, `cur_thread`, `virtualization`, the two syscall arguments), then `wrmsrTail`: gen 13's
  `fl4WriteMsr` verdict, and on `Ok x` the store `write x value`, the read-back and `reply`; on `Err e` the error
  with the state after the stall. So `fl4WriteMsr_rel` (verdict = `checkMsrWrite`, address = `v + msrOff`) is a
  statement about FL4's decode itself.
* `ite3`, `bind_ext`: helpers (the label tests are decided by `simp` with `decide`, as P1/QueueDecVcpu's `vlbl`).

Premise: `P0.ArchTotal ar` (the standard totality hypothesis; `vcpu_capability` returns). No [J]/[P]/[W]/[S].
New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtMsrEq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtMsrDec
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanSvm Fl4Proofs.P3.VirtMsrEq

theorem ite3 {α : Type _} {c1 c2 c3 : Prop} [Decidable c1] [Decidable c2] [Decidable c3] (X Y : α) :
    (if c1 then X else if c2 then X else if c3 then X else Y) = if (c1 ∨ c2 ∨ c3) then X else Y := by
  by_cases h1 : c1 <;> by_cases h2 : c2 <;> by_cases h3 : c3 <;> simp [h1, h2, h3]

theorem bind_ext {α β : Type _} {m : Result α} {f g : α → Result β} (h : ∀ x, f x = g x) :
    (m >>= f) = (m >>= g) := by rw [funext h]

section
variable {S : Type} {st : machine.Store S} {A : Type} {ar : machine.Arch A}

/-- FL4's WriteMSR after the decode's prefix (stall, current thread, backend, the two arguments): the
transcription `fl4WriteMsr`, then on success the store, the read-back and the reply. -/
def wrmsrTail (st : machine.Store S) (ar : machine.Arch A) (s1 : S) (a1 : A) (v f value : U64) (amd call : Bool) :
    Result ((core.result.Result Unit error.Exc) × S × A) := do
  let r ← fl4WriteMsr ar a1 v f value amd
  match r with
  | .Ok x => do
    let s2 ← st.write s1 x value
    let i4 ← st.read s2 x
    let s3 ← vcpu.reply st s2 call i4
    ok (core.result.Result.Ok (), s3, a1)
  | .Err e => ok (core.result.Result.Err e, s1, a1)

set_option maxHeartbeats 8000000 in
/-- **The extracted `vcpu.decode` on `X86VCPUWriteMSR`** (FL4 vcpu.rs l. 978-1006, all four inlined copies of the
MSR arm): past the length check it is the transcription `fl4WriteMsr` followed by the write, the read-back and the
reply. -/
theorem decode_wrmsr_eq (hA : P0.ArchTotal ar) (s : S) (a : A) (length v : U64) (call : Bool) (buf : U64)
    (ex : Aeneas.Std.Array obj.Slot 3#usize) (hlen : ¬ length < 2#u64) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteMSR length v call buf ex =
      vcpu.stall st ar s a v >>= fun p => (do
        let ct ← sched.cur_thread st p.1
        let i ← ar.virtualization p.2
        let f ← if length > 0#u64 then msg.syscall_arg st p.1 ct buf 0#u64 else ok 0#u64
        let value ← if length > 1#u64 then msg.syscall_arg st p.1 ct buf 1#u64 else ok 0#u64
        wrmsrTail st ar p.1 p.2 v f value (i = 2#u64) call) := by
  unfold vcpu.decode
  simp (config := { decide := true }) only [fl4_abi.label.X86VCPUSetTCB, fl4_abi.label.X86VCPUWriteRegisters,
    fl4_abi.label.X86VCPUFlushTLB, fl4_abi.label.X86VCPUReadVMCS, fl4_abi.label.X86VCPUWriteVMCS,
    fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUWriteVMCB, fl4_abi.label.X86VCPUReadMSR,
    fl4_abi.label.X86VCPUWriteMSR, ite_true, ite_false, if_true, if_false, bind_ok, hlen, ite_self]
  refine bind_ext fun x => ?_
  obtain ⟨s1, a1⟩ := x
  refine bind_ext (m := sched.cur_thread st s1) fun ct => ?_
  refine bind_ext (m := ar.virtualization a1) fun i => ?_
  refine bind_ext fun f => ?_
  refine bind_ext fun value => ?_
  beta_reduce
  obtain ⟨o, ho, -⟩ := msr_addr_eq v f (decide (i = 2#u64))
  unfold wrmsrTail fl4WriteMsr
  rw [ho, bind_ok, bind_ok]
  cases o with
  | none => simp [error.illegal]
  | some x =>
    try dsimp only
    obtain ⟨w1, hw1, -⟩ := P1.spec_ex_fd (hA.vcpu_capability a1 1#u64)
    obtain ⟨w0, hw0, -⟩ := P1.spec_ex_fd (hA.vcpu_capability a1 0#u64)
    rw [ite3]
    by_cases p : (f = 3221225602#u64 ∨ f = 3221225603#u64 ∨ f = 3221225730#u64)
    · rw [if_pos p, if_pos p]
      simp only [hw1, bind_ok, canonical_eq]
      cases hcb : canonical value.bv w1.bv
      · simp [error.invalid_arg]
      · simp only [bind_ok, if_true, Bool.true_eq_false, if_false]
        by_cases fX : f = 4294967294#u64
        · rw [if_pos fX, if_pos fX]
          simp only [hw0, bind_ok, valid_xcr0_eq]
          cases hxb : validXcr0 value.bv w0.bv
          · simp [error.invalid_arg]
          · by_cases fI : f = vcpu.MSR_VM_IBPB_DEFER <;> by_cases hv1 : value > 1#u64 <;>
              simp [fI, hv1, error.invalid_arg]
        · rw [if_neg fX, if_neg fX]
          by_cases fI : f = vcpu.MSR_VM_IBPB_DEFER <;> by_cases hv1 : value > 1#u64 <;>
            simp [fI, hv1, error.invalid_arg]
    · rw [if_neg p, if_neg p]
      simp only [bind_ok, Bool.true_eq_false, if_false]
      by_cases fX : f = 4294967294#u64
      · rw [if_pos fX, if_pos fX]
        simp only [hw0, bind_ok, valid_xcr0_eq]
        cases hxb : validXcr0 value.bv w0.bv
        · simp [error.invalid_arg]
        · by_cases fI : f = vcpu.MSR_VM_IBPB_DEFER <;> by_cases hv1 : value > 1#u64 <;>
            simp [fI, hv1, error.invalid_arg]
      · rw [if_neg fX, if_neg fX]
        by_cases fI : f = vcpu.MSR_VM_IBPB_DEFER <;> by_cases hv1 : value > 1#u64 <;>
          simp [fI, hv1, error.invalid_arg]

end
end Fl4Proofs.P3.VirtMsrDec
