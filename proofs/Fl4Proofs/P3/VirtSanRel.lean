/-
P3x for virtualization (line virt, gen 11): **VIRT-PLAN R1 on the relation side, and `vcpu::init` against
`initVcpu` at the image level** — facts about `VcpuRelVmx` / `VcpuRelSvm` (gen 10, `Fl4Spec/Ext/VirtRel*`) that the
sanitized writes and VCPU creation need; no FL4 store, no J layer.

* FL4's VMCS index (`vcpu::vmcs_addr`, spec `vmcsIdx`) is **injective on the 86 table encodings**: `unIdx` inverts it
  on every `WRITE_FIELDS` / `READ_FIELDS` encoding (`canon_write`, `canon_read`: one `decide` per field, no `decide`
  over a list), so **`vmcsOff_inj`**; every VMCS place lies below `TCB` (`vmcsOff_lt_tcb`), every other related place
  at or above it.
* **`VcpuRelVmx.write_vmcs`**: storing `x` at FL4's place of a writable VMCS field relates to `vs.set .vmx (.vmcs f) x`
  (VIRT-PLAN §5.1 X86VCPUWriteVMCS "field := sanitized", FL4 `vcpu::decode` → `write_vmcs`).
  **`VcpuRelSvm.write_vmcb`**: the same for a WriteVMCB word other than RAX (`f ≠ Svm.rax`: RAX's canonical place is
  GPR 0 / FL4's `REGS`, and FL4 writes both copies — the RAX case is `SvmRaxSync`'s, not covered here).
  `svmTab` (FL4 `sanitize_vmcb`'s 50 match arms, vcpu.rs l. 596-630), `writeRule_mem` (every word `Svm.writeRule`
  accepts is an arm), `svm_writable_lt`.
* `vcpu::init` (vcpu.rs l. 644-678) at the image level: `InitCommon`, **`InitImgVmx`**, **`InitImgSvm`** state, place by
  place, the words `init` leaves in a retype-zeroed VCPU; **`vcpuRelVmx_init`** / **`vcpuRelSvm_init`**: such an image
  relates to the spec's `initVcpu .vmx` / `initVcpu .svm` (Ext/VirtState, the retype hook of `fl4InvokeUntypedV`).
  The FL4 program walk that `vcpu.init` produces such an image from a zeroed one is not here (open item).

No named premise; no [J]/[P]/[W]/[S]. New file only.
-/
import Fl4Proofs.P3.VirtVcpuRel

namespace Fl4Proofs.P3.VirtSanRel
open Fl4Spec Fl4Proofs.P3.VirtVcpuRel

/-- The inverse of FL4's VMCS index on the encodings of its tables. -/
def unIdx (i : Word) : Word :=
  ((i &&& 0x7f) <<< 1) ||| (((i >>> 7) &&& 3) <<< 10) ||| (((i >>> 9) &&& 3) <<< 13)

theorem canon_write : ∀ f ∈ Vmx.vmxWriteFields, unIdx (vmcsIdx f) = f := by
  intro f hf
  simp only [Vmx.vmxWriteFields, List.mem_cons, List.not_mem_nil, or_false] at hf
  repeat (rcases hf with rfl | hf; · decide)

theorem canon_read : ∀ f ∈ Vmx.vmxReadFields, unIdx (vmcsIdx f) = f := by
  intro f hf
  simp only [Vmx.vmxReadFields, List.mem_cons, List.not_mem_nil, or_false] at hf
  repeat (rcases hf with rfl | hf; · decide)

theorem canon_tab {f : Word} (hf : Vmx.writable f = true ∨ Vmx.readable f = true) : unIdx (vmcsIdx f) = f := by
  rcases hf with h | h
  · exact canon_write f (of_decide_eq_true h)
  · exact canon_read f (of_decide_eq_true h)

theorem vmcsOff_inj {f g : Word} (hf : Vmx.writable f = true ∨ Vmx.readable f = true)
    (hg : Vmx.writable g = true ∨ Vmx.readable g = true) (e : vmcsOff f = vmcsOff g) : f = g := by
  unfold vmcsOff at e
  have h1 : vmcsIdx f * 8 = vmcsIdx g * 8 := add_left_cancel e
  have h2 : (vmcsIdx f).toNat = (vmcsIdx g).toNat := by
    have := congrArg BitVec.toNat h1
    simp only [BitVec.toNat_mul, toNat_eight] at this
    have a := vmcsIdx_lt f; have b := vmcsIdx_lt g
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
  rw [← canon_tab hf, ← canon_tab hg, BitVec.eq_of_toNat_eq h2]

/-- Every VMCS place lies below `TCB` (`SHADOW + 8 · idx ≤ 0x4ff8`). -/
theorem vmcsOff_lt_tcb (f : Word) : (vmcsOff f).toNat < VcpuLay.TCB.toNat := by
  have := vmcsIdx_lt f
  have e1 : VcpuLay.SHADOW.toNat = 4096 := rfl
  have e2 : VcpuLay.TCB.toNat = 20480 := rfl
  unfold vmcsOff
  rw [BitVec.toNat_add, BitVec.toNat_mul, toNat_eight, e1, e2]
  rw [Nat.mod_eq_of_lt (a := (vmcsIdx f).toNat * 8) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem ne_of_tcb_le {v o p : Word} (hp : p.toNat < VcpuLay.TCB.toNat) (ho : VcpuLay.TCB.toNat ≤ o.toNat) :
    v + o ≠ v + p := fun e => by
  have := congrArg BitVec.toNat (add_left_cancel e); omega

theorem gprOff_ge : ∀ i, VcpuLay.TCB.toNat ≤ (gprOff i).toNat := by decide
theorem exitOff_ge : ∀ i, VcpuLay.TCB.toNat ≤ (exitOff i).toNat := by decide

theorem msrOff_ge {m i : Word} (h : msrSlot m = some i) : VcpuLay.TCB.toNat ≤ (VcpuLay.MSRS + i * 8).toNat := by
  unfold msrSlot at h
  split_ifs at h <;> cases h <;> decide

theorem ioOff_ge (p : BitVec 16) : VcpuLay.TCB.toNat ≤ (vcpuIoOff p).toNat := by
  have hp := p.isLt
  have e1 : VcpuLay.IO.toNat = 24576 := rfl
  have e2 : VcpuLay.TCB.toNat = 20480 := rfl
  unfold vcpuIoOff
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, toNat_eight, e1, e2]
  have : p.toNat / 64 < 1024 := by omega
  rw [Nat.mod_eq_of_lt (a := p.toNat / 64) (by omega), Nat.mod_eq_of_lt (a := p.toNat / 64 * 8) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- **WriteVMCS on the relation**: storing `x` at FL4's place of a writable VMCS field `f` (`vmcs_addr`) relates
to the abstract VCPU with field `f` set to `x` (VIRT-PLAN §5.1 X86VCPUWriteVMCS, effect "field := sanitized"). -/
theorem VcpuRelVmx.write_vmcs {mem : Word → Word} {v : Word} {vs : VcpuState} {f x : Word}
    (h : VcpuRelVmx mem v vs) (hf : Vmx.writable f = true) :
    VcpuRelVmx (Function.update mem (v + vmcsOff f) x) v (vs.set .vmx (.vmcs f) x) := by
  have hl := vmcsOff_lt_tcb f
  have up : ∀ o, VcpuLay.TCB.toNat ≤ o.toNat → Function.update mem (v + vmcsOff f) x (v + o) = mem (v + o) :=
    fun o ho => Function.update_of_ne (ne_of_tcb_le hl ho) _ _
  have hc : VField.canon .vmx (.vmcs f) = .vmcs f := rfl
  refine
    { tcb := by rw [up _ (by decide)]; exact h.tcb
      valid := by rw [up _ (by decide)]; exact h.valid
      pending := by rw [up _ (by decide)]; exact h.pending
      mrs := fun i => by rw [up _ (exitOff_ge i)]; exact h.mrs i
      gpr := fun i => by
        simp only [VcpuState.set, hc]
        rw [Function.update_of_ne (by simp), up _ (gprOff_ge i)]; exact h.gpr i
      xcr0 := by
        simp only [VcpuState.set, hc]
        rw [Function.update_of_ne (by simp), up _ (by decide)]; exact h.xcr0
      ibpb := by
        simp only [VcpuState.set, hc]
        rw [Function.update_of_ne (by simp), up _ (by decide)]; exact h.ibpb
      vmcs := fun g hg => by
        simp only [VcpuState.set, hc]
        by_cases e : g = f
        · subst e; rw [Function.update_self, Function.update_self]
        · have hne : v + vmcsOff g ≠ v + vmcsOff f := fun e' => e (vmcsOff_inj hg (Or.inl hf) (add_left_cancel e'))
          rw [Function.update_of_ne (by simpa using e), Function.update_of_ne hne]; exact h.vmcs g hg
      msr := fun m i hi => by
        simp only [VcpuState.set, hc]
        rw [Function.update_of_ne (by simp), up _ (msrOff_ge hi)]; exact h.msr m i hi
      cr2 := by
        simp only [VcpuState.set, hc]
        rw [Function.update_of_ne (by simp), up _ (by decide)]; exact h.cr2
      io := fun p => by rw [up _ (ioOff_ge p)]; exact h.io p }

/-- FL4 `sanitize_vmcb`'s match arms, in FL4's order (the 50 WriteVMCB-writable VMCB words). -/
def svmTab : List Word := [0x000, 0x008, 0x010, 0x038, 0x050, 0x060, 0x068, 0x0a8, 0x0c8, 0x4c8, 0x4d0, 0x548, 0x400, 0x410, 0x420, 0x430, 0x440, 0x450, 0x460, 0x470, 0x480, 0x490, 0x550, 0x558, 0x560, 0x568, 0x570, 0x578, 0x5d8, 0x5f8, 0x600, 0x618, 0x628, 0x640, 0x668, 0x408, 0x418, 0x428, 0x438, 0x448, 0x458, 0x468, 0x478, 0x488, 0x498, 0x608, 0x610, 0x620, 0x630, 0x638]

/-- Every word `Svm.writeRule` accepts is an arm of FL4's `sanitize_vmcb` match. -/
theorem writeRule_mem {g : Word} (h : (Svm.writeRule g).isSome = true) : g ∈ svmTab := by
  unfold Svm.writeRule at h
  by_cases h1 : g = Svm.interceptCr
  · subst h1; simp only [svmTab]; repeat (first | exact .head _ | apply List.Mem.tail)
  rw [if_neg h1] at h
  by_cases h2 : g = Svm.interceptExc
  · subst h2; simp only [svmTab]; repeat (first | exact .head _ | apply List.Mem.tail)
  rw [if_neg h2] at h
  by_cases h3 : g = Svm.interceptMisc2
  · subst h3; simp only [svmTab]; repeat (first | exact .head _ | apply List.Mem.tail)
  rw [if_neg h3] at h
  by_cases h4 : g = Svm.pauseFilter
  · subst h4; simp only [svmTab]; repeat (first | exact .head _ | apply List.Mem.tail)
  rw [if_neg h4] at h
  by_cases h5 : g = Svm.tscOffset
  · subst h5; simp only [svmTab]; repeat (first | exact .head _ | apply List.Mem.tail)
  rw [if_neg h5] at h
  by_cases h6 : g = Svm.intCtl
  · subst h6; simp only [svmTab]; repeat (first | exact .head _ | apply List.Mem.tail)
  rw [if_neg h6] at h
  by_cases h7 : g = Svm.intState
  · subst h7; simp only [svmTab]; repeat (first | exact .head _ | apply List.Mem.tail)
  rw [if_neg h7] at h
  by_cases h8 : g = Svm.eventInj
  · subst h8; simp only [svmTab]; repeat (first | exact .head _ | apply List.Mem.tail)
  rw [if_neg h8] at h
  by_cases h9 : g = Svm.nextRip
  · subst h9; simp only [svmTab]; repeat (first | exact .head _ | apply List.Mem.tail)
  rw [if_neg h9] at h
  by_cases h10 : g = Svm.cpl
  · subst h10; simp only [svmTab]; repeat (first | exact .head _ | apply List.Mem.tail)
  rw [if_neg h10] at h
  by_cases h11 : g = Svm.efer
  · subst h11; simp only [svmTab]; repeat (first | exact .head _ | apply List.Mem.tail)
  rw [if_neg h11] at h
  by_cases h12 : g = Svm.cr4
  · subst h12; simp only [svmTab]; repeat (first | exact .head _ | apply List.Mem.tail)
  rw [if_neg h12] at h
  by_cases h13 : g ∈ Svm.segAttrOffsets ++ [Svm.cr3, Svm.cr0, Svm.dr7, Svm.dr6, Svm.rflags, Svm.rip, Svm.rsp,
      Svm.rax, Svm.star, Svm.sfmask, Svm.sysenterCs, Svm.cr2, Svm.gPat]
  · simp only [Svm.segAttrOffsets, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at h13
    repeat (rcases h13 with rfl | h13; · simp only [svmTab]; repeat (first | exact .head _ | apply List.Mem.tail))
  rw [if_neg h13] at h
  by_cases h14 : g ∈ Svm.segBaseOffsets ++ [Svm.lstar, Svm.cstar, Svm.kernelGsBase, Svm.sysenterEsp,
      Svm.sysenterEip]
  · simp only [Svm.segBaseOffsets, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at h14
    repeat (rcases h14 with rfl | h14; · simp only [svmTab]; repeat (first | exact .head _ | apply List.Mem.tail))
  rw [if_neg h14] at h
  simp at h

/-- Every WriteVMCB-writable word lies in the VMCB (below `svm::END` = 0x6e8). -/
theorem svm_writable_lt {f : Word} (hf : Svm.writable f = true) : f.toNat < 0x6e8 := by
  have hm := writeRule_mem hf
  simp only [svmTab, List.mem_cons, List.not_mem_nil, or_false] at hm
  repeat (rcases hm with rfl | hm; · decide)

/-- **WriteVMCB on the relation** (a word other than RAX, whose canonical place is GPR 0). -/
theorem VcpuRelSvm.write_vmcb {mem : Word → Word} {v : Word} {vs : VcpuState} {f x : Word}
    (h : VcpuRelSvm mem v vs) (hf : Svm.writable f = true) (hx : f ≠ Svm.rax) :
    VcpuRelSvm (Function.update mem (v + f) x) v (vs.set .svm (.vmcb f) x) := by
  have hl : f.toNat < VcpuLay.TCB.toNat := by
    have := svm_writable_lt hf; have e2 : VcpuLay.TCB.toNat = 20480 := rfl; omega
  have up : ∀ o, VcpuLay.TCB.toNat ≤ o.toNat → Function.update mem (v + f) x (v + o) = mem (v + o) :=
    fun o ho => Function.update_of_ne (ne_of_tcb_le hl ho) _ _
  have hc : VField.canon .svm (.vmcb f) = .vmcb f := by simp [VField.canon, hx]
  refine
    { tcb := by rw [up _ (by decide)]; exact h.tcb
      valid := by rw [up _ (by decide)]; exact h.valid
      pending := by rw [up _ (by decide)]; exact h.pending
      mrs := fun i => by rw [up _ (exitOff_ge i)]; exact h.mrs i
      gpr := fun i => by
        simp only [VcpuState.set, hc]
        rw [Function.update_of_ne (by simp), up _ (gprOff_ge i)]; exact h.gpr i
      xcr0 := by
        simp only [VcpuState.set, hc]
        rw [Function.update_of_ne (by simp), up _ (by decide)]; exact h.xcr0
      ibpb := by
        simp only [VcpuState.set, hc]
        rw [Function.update_of_ne (by simp), up _ (by decide)]; exact h.ibpb
      vmcb := fun g hr hh hg => by
        simp only [VcpuState.set, hc]
        by_cases e : g = f
        · subst e; rw [Function.update_self, Function.update_self]
        · have hne : v + g ≠ v + f := fun e' => e (add_left_cancel e')
          rw [Function.update_of_ne (by simpa using e), Function.update_of_ne hne]; exact h.vmcb g hr hh hg }

/-! ## `vcpu::init` against `initVcpu`: the image the relation reads -/

/-- The words of FL4's VCPU image both backends' `vcpu::init` leave (VIRT-PLAN §5.4; FL4 `vcpu.rs` `init`): the
binding word, the exit record and the GPRs zero (the retype's zeroing, untouched by `init`), XCR0 the host's
(`set(s, v, XCR0, a.vcpu_capability(0))`), `VM_IBPB_DEFER` zero. -/
structure InitCommon (mem : Word → Word) (v : Word) : Prop where
  tcb : mem (v + VcpuLay.TCB) = 0
  valid : mem (v + VcpuLay.VALID) = 0
  pending : mem (v + VcpuLay.PENDING) = 0
  mrs : ∀ i, mem (v + exitOff i) = 0
  gpr : ∀ i, mem (v + gprOff i) = 0
  xcr0 : mem (v + VcpuLay.XCR0) = hostXcr0
  ibpb : mem (v + VcpuLay.VM_IBPB_DEFER) = 0

/-- **FL4's VMX image after `vcpu::init`** (the `else` branch of `init`): every I/O-bitmap word all ones (the
`while i < 1024` loop), every table VMCS field at its `vmxInitFields` value (the `WRITE_FIELDS` loop writes
`sanitize_vmcs(a, f, 0)`, then the entry controls, RFLAGS and PAT are rewritten; the read-only fields keep the
retype's zero), the syscall-MSR slots and CR2 zero. -/
structure InitImgVmx (mem : Word → Word) (v : Word) : Prop extends InitCommon mem v where
  vmcs : ∀ f, (Vmx.writable f = true ∨ Vmx.readable f = true) → mem (v + vmcsOff f) = vmxInitFields (.vmcs f)
  msr : ∀ m i, msrSlot m = some i → mem (v + (VcpuLay.MSRS + i * 8)) = 0
  cr2 : mem (v + VcpuLay.CR2) = 0
  io : ∀ p, mem (v + vcpuIoOff p) = ~~~0

/-- **FL4's SVM image after `vcpu::init`** (`reset_svm` and the five control words): every related VMCB word at its
`svmInitFields` value. -/
structure InitImgSvm (mem : Word → Word) (v : Word) : Prop extends InitCommon mem v where
  vmcb : ∀ off, Svm.readable off = true → Svm.hiddenRead off = false → off ≠ Svm.rax →
    mem (v + off) = svmInitFields (.vmcb off)

theorem shl_ne_zero (n : Nat) (h : n < 64) : ((1 : Word) <<< n) ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_shiftLeft] at this
  have h1 : (1 : Word).toNat = 1 := rfl
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [h1, h0, Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h)] at this
  exact absurd this (Nat.two_pow_pos n).ne'

theorem ioBit_ne (p : BitVec 16) : vcpuIoBit p ≠ 0 := shl_ne_zero _ (Nat.mod_lt _ (by decide))

theorem initCommon_rel {k : VirtKind} {mem : Word → Word} {v : Word} (h : InitCommon mem v)
    (hk : k ≠ .svm) : VcpuRelCommon mem v (initVcpu k) where
  tcb := by rw [h.tcb]; simp [initVcpu, vcpuTcbRef]
  valid := by rw [h.valid]; simp [initVcpu]
  pending := by rw [h.pending]; simp [initVcpu]
  mrs i := by rw [h.mrs i]; rfl
  gpr i := by rw [h.gpr i]; simp [initVcpu, hk, vmxInitFields]
  xcr0 := by rw [h.xcr0]; simp [initVcpu, hk, vmxInitFields]
  ibpb := by rw [h.ibpb]; simp [initVcpu, hk, vmxInitFields, msrVmIbpbDefer, msrXcr0, Vmx.controlEntryControls]

/-- **`vcpu::init` relates to `initVcpu .vmx`**: an image of the `InitImgVmx` shape is the spec's new VCPU. -/
theorem vcpuRelVmx_init {mem : Word → Word} {v : Word} (h : InitImgVmx mem v) :
    VcpuRelVmx mem v (initVcpu .vmx) :=
  { initCommon_rel h.toInitCommon (by decide) with
    vmcs := fun f hf => by rw [h.vmcs f hf]; simp [initVcpu]
    msr := fun m i hi => by
      rw [h.msr m i hi]
      have : m ≠ msrXcr0 := by unfold msrSlot at hi; split_ifs at hi <;> subst_vars <;> decide
      simp [initVcpu, vmxInitFields, this]
    cr2 := by rw [h.cr2]; simp [initVcpu, vmxInitFields, msrCr2, msrXcr0]
    io := fun p => by
      rw [h.io p]
      have e : (~~~(0 : Word)) &&& vcpuIoBit p = vcpuIoBit p := by
        ext i hi
        simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero, Bool.not_false, Bool.true_and]
        try simp
      simp only [initVcpu, e]
      simp only [ne_eq, decide_not, ioBit_ne p, decide_false, Bool.not_false] }

theorem initCommon_relSvm {mem : Word → Word} {v : Word} (h : InitCommon mem v) :
    VcpuRelCommon mem v (initVcpu .svm) where
  tcb := by rw [h.tcb]; simp [initVcpu, vcpuTcbRef]
  valid := by rw [h.valid]; simp [initVcpu]
  pending := by rw [h.pending]; simp [initVcpu]
  mrs i := by rw [h.mrs i]; rfl
  gpr i := by
    rw [h.gpr i]
    simp [initVcpu, svmInitFields, svmReset]
  xcr0 := by rw [h.xcr0]; simp [initVcpu, svmInitFields, svmReset]
  ibpb := by rw [h.ibpb]; simp [initVcpu, svmInitFields, svmReset, msrVmIbpbDefer, msrXcr0]

/-- **`vcpu::init` relates to `initVcpu .svm`**. -/
theorem vcpuRelSvm_init {mem : Word → Word} {v : Word} (h : InitImgSvm mem v) :
    VcpuRelSvm mem v (initVcpu .svm) :=
  { initCommon_relSvm h.toInitCommon with
    vmcb := fun off hr hh hx => by rw [h.vmcb off hr hh hx]; simp [initVcpu] }

end Fl4Proofs.P3.VirtSanRel
