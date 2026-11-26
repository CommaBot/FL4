/-
P3x for virtualization (line virt, gen 17, item 2): **WriteMSR / WriteVMCB against the spec's decoder**, and
**`ReplyPl` without `JAtZ`**.

Spec side (`decodeVcpuInvocation`, Ext/VirtVcpu):
* **`spec_decode_wrmsr`**: on the WriteMSR label with at least two arguments the spec's decode is
  `checkMsrWrite (args[0]) (args[1])`'s verdict, `writeMsr v args[0] args[1]` on `ok`.
* **`spec_decode_wrvmcb`** (`virtKind = .svm`): the VCPU read, then `sanitizeVmcb args[0] (specOld st args[0])
  args[1]`'s verdict (`specOld`, P3/VirtVmcbE2E), `writeVmcb v args[0] val` on `ok val`; `wrvmcbK` names the part
  after the read.

The arguments:
* `vsyscall_arg_reg`: `msg::syscall_arg` below 4 reads message register `mrIdx i` of the given thread.
* **`regs_stall`**: the caller's registers are kept by the stall's `IPI_PENDING` write (`ReplyPl`: the current
  thread is a TCB off the current node).
* **`wr_args`**: past the length check the decode's `f`, `value` are message registers 0 and 1 of the current
  thread; `specMrs_getD_lo`: the spec's `args[i]` (`specMrs`, the front end's argument list) is register
  `mrIdx i` for `i < 4`, `i < len`.

Joint:
* **`wrmsr_spec_joint`**: gen 15's `TailPost` (the post `decode_wrmsr_vmx/svm` give, P3/VirtMsrE2E) and the spec's
  decode with `args[0] = f`, `args[1] = value`: either the spec decodes `writeMsr v f value`, FL4 answers `Ok` and
  the VCPU relates to `vs.set k (.msr f) value`, or the spec throws `e'`, FL4 answers the related `e`, state kept.
* **`wrvmcb_spec_joint`**: likewise from `decode_wrvmcb_gen`'s `VmcbPost` (P3/VirtVmcbE2E) against `wrvmcbK`
  at the spec's VCPU `vs`.
* **`wrmsr_args_joint`**: `wr_args` + `regs_stall` + `specMrs_getD_lo`: from the entry state's registers
  (`(L.mem s (regA ct (regIdx r))).bv = regs r`, the front end's `hregs`) and `args = specMrs regs sbo um len`,
  `2 ≤ len`, the decoded `f`, `value` are `args[0]`, `args[1]`.

`ReplyPl` in VM epochs:
* **`JKern.replyPl`**: `ReplyPl st v s` from `JKern` (the kernel-global facts, not `JExt`), the layout record
  `JVLay` (P3/JExtVLay; all its fields are non-`ext`) and `JVm.ks` — no `JAtZ`; gen 16's `JAtZ.replyPl` is the
  instance at `JAtZ` states.

No premise (no [J]/[P]/[W]). New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtVmcbE2E
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtArgsSpec
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtSanSvm
open Fl4Proofs.P3.VirtVcpuRel Fl4Proofs.P3.VirtMsrEq Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit
open Fl4Proofs.P3.VirtMsrStore Fl4Proofs.P3.VirtVmcbStore Fl4Proofs.P3.VirtReplyKeep Fl4Proofs.P3.VirtVmcbDec
open Fl4Proofs.P3.VirtVmcbTail Fl4Proofs.P3.VirtMsrE2E Fl4Proofs.P3.VirtVmcbE2E

noncomputable section

/-! ## The spec's decode -/

section
variable {Z : Type}

/-- **The spec's WriteMSR decode** (module docstring). -/
theorem spec_decode_wrmsr {label : Data} {args : List Data} {v : ObjRef} {caps : List (Cap × CslotPtr)}
    (hl : vcpuLabelOf label = some .writeMsr) (hlen : 2 ≤ args.length) :
    decodeVcpuInvocation (Z := Z) label args v caps =
      match checkMsrWrite (args.getD 0 0) (args.getD 1 0) with
      | .error e => NonDetE.throwError e
      | .ok () => NonDetE.returnOk (.writeMsr v (args.getD 0 0) (args.getD 1 0)) := by
  unfold decodeVcpuInvocation
  simp only [hl]
  rw [if_neg (by omega)]
  first | rfl | (split <;> rfl)

/-- The spec's WriteVMCB after the VCPU read. -/
def wrvmcbK (v : ObjRef) (f x : Word) (st : VcpuState) : SEMonad Z VcpuInvocation :=
  match sanitizeVmcb f (specOld st f) x with
  | .error e => NonDetE.throwError e
  | .ok val => NonDetE.returnOk (.writeVmcb v f val)

/-- **The spec's WriteVMCB decode on SVM** (module docstring). -/
theorem spec_decode_wrvmcb (hk : virtKind = .svm) {label : Data} {args : List Data} {v : ObjRef}
    {caps : List (Cap × CslotPtr)} (hl : vcpuLabelOf label = some .writeVmcb) (hlen : 2 ≤ args.length) :
    decodeVcpuInvocation (Z := Z) label args v caps =
      (NonDetE.liftE (getVcpu v) >>= wrvmcbK v (args.getD 0 0) (args.getD 1 0)) := by
  unfold decodeVcpuInvocation wrvmcbK specOld
  simp only [hl]
  rw [if_neg (by simp [hk]), if_neg (by omega)]
  simp only [hk]
  try rfl

end

/-! ## The arguments -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

theorem vsyscall_arg_reg {s : S} {regs : Register → Word} {ct buf : U64}
    (hregs : ∀ r, (L.mem s (Endp.regA ct (Endp.regIdx r))).bv = regs r) (i : U64) (hi : i.val < 4) :
    ∃ x, msg.syscall_arg st s ct buf i = ok x ∧ x.bv = regs (Endp.mrIdx i.val) := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by simp [msg.N_MSG_REGISTERS]
  unfold msg.syscall_arg
  have h4 : i < msg.N_MSG_REGISTERS := by
    have : i.val < msg.N_MSG_REGISTERS.val := by omega
    scalar_tac
  rw [if_pos h4]
  obtain ⟨r, hr, hrv⟩ := spec_exists (Endp.msg_register_spec i hi)
  rw [hr, bind_ok]
  obtain ⟨x, hx, hxv⟩ := spec_exists (Endp.obj.Tcb.reg.spec (L := L) s ct r)
  rw [hx]
  refine ⟨x, rfl, ?_⟩
  rw [hxv, hrv, hregs]

/-- **The stall keeps the caller's registers** (module docstring). -/
theorem regs_stall {v : U64} {s s1 : S} (P : ReplyPl st v s) (hW : P1.WritesIn st s s1 (· = ipiA st s))
    {regs : Register → Word} (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r) :
    ∀ r, (L.mem s1 (Endp.regA (L.mem s1 (curA st s1)) (Endp.regIdx r))).bv = regs r := by
  intro r
  have ec : L.mem s1 (curA st s1) = L.mem s (curA st s) := by
    rw [curA_of hW]; exact hW.2.2 _ P.curA_al (fun e => P.ipi_ne_cur e.symm)
  rw [ec]
  have hv := Endp.regA_val P.ctA (Endp.regIdx_lt r)
  have hr := Endp.regIdx_lt r
  have hal4 := P.ctA.align
  have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
  rw [h12] at hal4
  have hal : P1.Aligned (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r)) := by
    unfold P1.Aligned; rw [hv]; omega
  have hne : ¬ Endp.regA (L.mem s (curA st s)) (Endp.regIdx r) = ipiA st s := by
    intro e
    have h1 := (P.node (off := layout.node.IPI_PENDING) (by simp [layout.node.IPI_PENDING])).1
    have h3 := P.ctN
    have hoff : layout.node.IPI_PENDING.val < 4288 := by simp [layout.node.IPI_PENDING]
    unfold ipiA at e
    rw [← e, hv] at h1
    omega
  rw [hW.2.2 _ hal hne]; exact hregs r

/-- **The decoded arguments are message registers 0 and 1** (module docstring). -/
theorem wr_args {s1 : S} {regs : Register → Word} {buf length f value : U64}
    (hregs : ∀ r, (L.mem s1 (Endp.regA (L.mem s1 (curA st s1)) (Endp.regIdx r))).bv = regs r)
    (hlen : ¬ length < 2#u64)
    (hf : (if length > 0#u64 then msg.syscall_arg st s1 (L.mem s1 (curA st s1)) buf 0#u64 else ok 0#u64) = ok f)
    (hv : (if length > 1#u64 then msg.syscall_arg st s1 (L.mem s1 (curA st s1)) buf 1#u64 else ok 0#u64) =
      ok value) :
    f.bv = regs (Endp.mrIdx 0) ∧ value.bv = regs (Endp.mrIdx 1) := by
  have h0 : length > 0#u64 := by scalar_tac
  have h1 : length > 1#u64 := by scalar_tac
  rw [if_pos h0] at hf
  rw [if_pos h1] at hv
  obtain ⟨x0, e0, b0⟩ := vsyscall_arg_reg (st := st) (buf := buf) hregs 0#u64 (by simp)
  obtain ⟨x1, e1, b1⟩ := vsyscall_arg_reg (st := st) (buf := buf) hregs 1#u64 (by simp)
  rw [e0] at hf
  rw [e1] at hv
  rw [← Fl4Proofs.P1.ok_inj_ff hf, ← Fl4Proofs.P1.ok_inj_ff hv]
  exact ⟨b0, b1⟩

theorem specMrs_getD_lo {regs : Register → Word} {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (i : Nat)
    (hi : i < 4) (hl : i < len) : (Endp.specMrs regs sbo um len).getD i 0 = regs (Endp.mrIdx i) := by
  obtain ⟨h1, h2⟩ := Endp.specMrs_lo regs sbo um len i hi hl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some, ← h2, getElem!_pos _ i h1]

theorem specMrs_two {regs : Register → Word} {sbo : Option ObjRef} {um : Word → Word8} {len : Nat}
    (hl : 2 ≤ len) : 2 ≤ (Endp.specMrs regs sbo um len).length := by
  rw [specMrs_length]
  cases sbo <;> (try simp only) <;> omega

/-- **The decoded arguments are the spec's `args[0]`, `args[1]`** (module docstring). -/
theorem wrmsr_args_joint {v : U64} {s s1 : S} (P : ReplyPl st v s) (hW : P1.WritesIn st s s1 (· = ipiA st s))
    {regs : Register → Word} (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hl : 2 ≤ len)
    {buf length f value : U64} (hlen : ¬ length < 2#u64)
    (hf : (if length > 0#u64 then msg.syscall_arg st s1 (L.mem s1 (curA st s1)) buf 0#u64 else ok 0#u64) = ok f)
    (hv : (if length > 1#u64 then msg.syscall_arg st s1 (L.mem s1 (curA st s1)) buf 1#u64 else ok 0#u64) =
      ok value) :
    2 ≤ (Endp.specMrs regs sbo um len).length ∧ (Endp.specMrs regs sbo um len).getD 0 0 = f.bv ∧
      (Endp.specMrs regs sbo um len).getD 1 0 = value.bv := by
  obtain ⟨e0, e1⟩ := wr_args (regs_stall P hW hregs) hlen hf hv
  refine ⟨specMrs_two hl, ?_, ?_⟩
  · rw [specMrs_getD_lo 0 (by omega) (by omega), e0]
  · rw [specMrs_getD_lo 1 (by omega) (by omega), e1]

/-! ## Joint verdicts -/

variable {Z : Type}

/-- **WriteMSR: FL4's verdict and the spec's decode** (module docstring). -/
theorem wrmsr_spec_joint {R : (Word → Word) → Word → VcpuState → Prop} {k : VirtKind} {s1 : S} {v f value : U64}
    {vs : VcpuState} {r : (core.result.Result Unit error.Exc) × S × A}
    (hT : TailPost R k st s1 v f value vs r) {label : Data} {args : List Data} {vo : ObjRef}
    {caps : List (Cap × CslotPtr)} (hl : vcpuLabelOf label = some .writeMsr) (hlen : 2 ≤ args.length)
    (h0 : args.getD 0 0 = f.bv) (h1 : args.getD 1 0 = value.bv) :
    (decodeVcpuInvocation (Z := Z) label args vo caps = NonDetE.returnOk (.writeMsr vo f.bv value.bv) ∧
        r.1 = .Ok () ∧ R (memW st r.2.1) v.bv (vs.set k (.msr f.bv) value.bv)) ∨
      (∃ e e', decodeVcpuInvocation (Z := Z) label args vo caps = NonDetE.throwError e' ∧ SysErrRel e e' ∧
        r.1 = .Err e ∧ r.2.1 = s1) := by
  rw [spec_decode_wrmsr hl hlen, h0, h1]
  rcases hT with ⟨hc, hr, hR⟩ | ⟨e, e', hc, hs, hr, hst⟩
  · left; rw [hc]; exact ⟨rfl, hr, hR⟩
  · right; rw [hc]; exact ⟨e, e', rfl, hs, hr, hst⟩

/-- **WriteVMCB: FL4's verdict and the spec's decode** after the spec's VCPU read (module docstring). -/
theorem wrvmcb_spec_joint {s1 : S} {v f value : U64} {vs : VcpuState}
    {r : (core.result.Result Unit error.Exc) × S × A}
    (hT : VmcbPost st s1 v f value ⟨specOld vs f.bv⟩ vs r) (vo : ObjRef) {a0 a1 : Word} (h0 : a0 = f.bv)
    (h1 : a1 = value.bv) :
    (∃ val, wrvmcbK (Z := Z) vo a0 a1 vs = NonDetE.returnOk (.writeVmcb vo f.bv val) ∧ r.1 = .Ok () ∧
        VcpuRelSvm (memW st r.2.1) v.bv (vs.set .svm (.vmcb f.bv) val)) ∨
      (∃ e e', wrvmcbK (Z := Z) vo a0 a1 vs = NonDetE.throwError e' ∧ SysErrRel e e' ∧ r.1 = .Err e ∧
        r.2.1 = s1) := by
  subst h0 h1
  unfold wrvmcbK
  rcases hT with ⟨val, hc, hr, hR⟩ | ⟨e, e', hc, hs, hr, hst⟩
  · left
    have hc' : sanitizeVmcb f.bv (specOld vs f.bv) value.bv = .ok val := hc
    rw [hc']; exact ⟨val, rfl, hr, hR⟩
  · right
    have hc' : sanitizeVmcb f.bv (specOld vs f.bv) value.bv = .error e' := hc
    rw [hc']; exact ⟨e, e', rfl, hs, hr, hst⟩

end

/-! ## `ReplyPl` without `JAtZ` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {H : P1.Heap} {Cs D : Set U64} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} {V U : Set U64}

/-- **`ReplyPl` from the kernel-global facts, the layout record and the VCPU placement** (module docstring). -/
theorem JKern.replyPl (K : JKern (L := L) arI H Cs D th s σ) (Ly : JVLay V th U) (Jv : JVm (L := L) V H s σ)
    {v : U64} (hv : v ∈ V) : ReplyPl st v s := by
  have ht : th (L.mem s (curA st s)) = some .tcb := K.curT
  have nodeT := K.hnd _ .tcb K.curH (L.cpu s) K.cpuCs
  have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
  simp only [P1.HKind.bits, h12] at nodeT
  have hvap := Ly.vap v hv _ _ ht
  simp only [objSize] at hvap
  exact ⟨Ly.vfit v hv, K.ksbAl, K.nodeFit, K.csLt _ K.cpuCs, Jv.ks v hv, Ly.tA _ ht, nodeT, hvap⟩

end

end
end Fl4Proofs.P3.VirtArgsSpec
