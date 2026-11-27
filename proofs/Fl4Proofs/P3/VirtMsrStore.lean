/-
P3x for virtualization (line virt, gen 15, item 2): **WriteMSR keeps the VCPU relation** — the store half of FL4
`vcpu::decode`'s WriteMSR arm (vcpu.rs l. 987-1006: `write(x, value)`, `read(x)`, `reply`), on top of gen 14's
`decode_wrmsr_eq` (P3/VirtMsrDec: the extracted arm = prefix `>>=` `wrmsrTail`) and gen 13's `fl4WriteMsr_rel`
(verdict = `checkMsrWrite`, address `v + msrOff`), against the spec's `performVcpuInvocation (.writeMsr v m val)`
(Ext/VirtVcpu: `vcpuUpdate v (·.set virtKind (.msr m) val)`, reply `[val]`).

* `WrAt mem mem' v o x`: `mem'` is `mem` with the VCPU word `v + o` set to `x` (as far as the object's aligned
  words go). `memW_wr`: FL4's `Store::write` of an aligned VCPU word gives `WrAt` on `memW` (P3/VirtInitWalk).
* `msrOfOff`, **`msrOff_cases`** (FL4's MSR offset determines the MSR; the offsets per backend), `msrOff_inj`,
  `msrOff_of_slot`, `VcpuRelCommon.upd` (the shared part under one field update and one word write).
* **`msrStore_vmx`**: `VcpuRelVmx mem v vs`, `msrOff false m = some o`, `WrAt mem mem' v o x` ⇒
  `VcpuRelVmx mem' v (vs.set .vmx (.msr m) x)`. **`msrStore_svm`**: the same for SVM (`VcpuRelSvm`; the syscall
  MSRs and CR2 are VMCB save-area words there, `VField.canon`).
* **`wrmsrTail_vmx`**, **`wrmsrTail_svm`**: FL4's WriteMSR tail from a related VCPU: on the spec's
  `checkMsrWrite … = ok ()` FL4 answers `Ok`, replies with the written value (read-back), and the VCPU relates to
  `vs.set k (.msr f) value`; on `error e'` FL4 answers the related error `e` (`SysErrRel`) with the state unchanged.
* Spec side: `getVcpu_out`, **`vcpuUpdate_out`**, **`writeMsr_out`** (`performVcpuInvocation (.writeMsr v m val)`:
  the VCPU becomes `vs.set virtKind (.msr m) val`, reply `[val]`).
* **`writeMsr_rel_vmx`**, **`writeMsr_rel_svm`**: both halves joined — after FL4's tail and the spec's operation the
  VCPU at `v` relates (`VRelAt`, P3/VirtRetypeInit) on the backend.

Named premises:
* `CapAgree ar a` [P] (gen 11, unchanged).
* **`ReplyKeepsV st s x value call v` [J]** (new): FL4's `vcpu::reply` (vcpu.rs l. 1068-1070 via `full_reply`'s
  callers; extracted `vcpu.reply`: the caller's MR0 / BADGE / MSG_INFO registers, its state word, and
  `schedule_tcb`'s queue words) after the MSR write leaves the VCPU object's words alone. Justification: every word
  `reply` writes is a TCB word of the current thread or a scheduler word (P1's `XSV` footprint, QueueDecVcpu's
  `reply_leaf`), and no VCPU object overlaps a TCB or the kernel globals (mmuAD's `JW` / `JVLay` placement).
  Not false on reachable states: the current thread is a TCB, never inside a 2^15-aligned VCPU object.
State hypothesis (not a premise): `VFits v`. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtMsrDec
import Fl4Proofs.P3.VirtRetypeInit
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtMsrStore
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel
open Fl4Proofs.P3.VirtMsrEq Fl4Proofs.P3.VirtMsrDec Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit

noncomputable section

/-! ## The memory after one VCPU word write -/

/-- `mem'` is `mem` with the VCPU word at offset `o` set to `x` (on the object's aligned words). -/
def WrAt (mem mem' : Word → Word) (v o x : Word) : Prop :=
  mem' (v + o) = x ∧ ∀ off : Word, off.toNat < 32768 → off.toNat % 8 = 0 → off ≠ o → mem' (v + off) = mem (v + off)

theorem WrAt.keep {mem mem' : Word → Word} {v o x off : Word} (hw : WrAt mem mem' v o x) (h1 : off.toNat < 32768)
    (h2 : off.toNat % 8 = 0) (h3 : off.toNat ≠ o.toNat) : mem' (v + off) = mem (v + off) :=
  hw.2 off h1 h2 fun e => h3 (congrArg BitVec.toNat e)

/-! ## FL4's MSR offsets -/

/-- The MSR at an offset (left inverse of `msrOff amd`). -/
def msrOfOff (amd : Bool) (o : Word) : Word :=
  if o = VcpuLay.XCR0 then msrXcr0 else if o = VcpuLay.VM_IBPB_DEFER then msrVmIbpbDefer
  else if amd then
    (if o = Svm.star then msrStar else if o = Svm.lstar then msrLstar else if o = Svm.cstar then msrCstar
      else if o = Svm.sfmask then msrFmask else if o = Svm.kernelGsBase then msrKernelGsBase else msrCr2)
  else if o = VcpuLay.CR2 then msrCr2 else if o = VcpuLay.MSRS then msrStar
  else if o = VcpuLay.MSRS + 8 then msrLstar else if o = VcpuLay.MSRS + 16 then msrCstar
  else if o = VcpuLay.MSRS + 24 then msrFmask else msrKernelGsBase

/-- What an offset of `msrOff` is (checked on the eight MSRs and both backends). -/
def OffP (amd : Bool) (m o : Word) : Prop :=
  msrOfOff amd o = m ∧ o.toNat < 32768 ∧ o.toNat % 8 = 0 ∧
    (amd = false → o.toNat = 20504 ∨ o.toNat = 20512 ∨ o.toNat = 20544 ∨ (20864 ≤ o.toNat ∧ o.toNat ≤ 20896)) ∧
    (amd = true → o.toNat = 20504 ∨ o.toNat = 20544 ∨ (1536 ≤ o.toNat ∧ o.toNat ≤ 1600))

theorem msrOff_cases {amd : Bool} {m o : Word} (ho : msrOff amd m = some o) : OffP amd m o := by
  have hm : m ∈ vcpuMsrs := (msrOff_isSome amd m).1 (by rw [ho]; rfl)
  simp only [vcpuMsrs, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases amd
  · obtain rfl : o = (0x5180 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun _ => by decide, fun h => absurd h (by decide)⟩
  · obtain rfl : o = (0x600 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun h => absurd h (by decide), fun _ => by decide⟩
  · obtain rfl : o = (0x5188 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun _ => by decide, fun h => absurd h (by decide)⟩
  · obtain rfl : o = (0x608 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun h => absurd h (by decide), fun _ => by decide⟩
  · obtain rfl : o = (0x5190 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun _ => by decide, fun h => absurd h (by decide)⟩
  · obtain rfl : o = (0x610 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun h => absurd h (by decide), fun _ => by decide⟩
  · obtain rfl : o = (0x5198 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun _ => by decide, fun h => absurd h (by decide)⟩
  · obtain rfl : o = (0x618 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun h => absurd h (by decide), fun _ => by decide⟩
  · obtain rfl : o = (0x51a0 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun _ => by decide, fun h => absurd h (by decide)⟩
  · obtain rfl : o = (0x620 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun h => absurd h (by decide), fun _ => by decide⟩
  · obtain rfl : o = (0x5020 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun _ => by decide, fun h => absurd h (by decide)⟩
  · obtain rfl : o = (0x640 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun h => absurd h (by decide), fun _ => by decide⟩
  · obtain rfl : o = (0x5018 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun _ => by decide, fun h => absurd h (by decide)⟩
  · obtain rfl : o = (0x5018 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun h => absurd h (by decide), fun _ => by decide⟩
  · obtain rfl : o = (0x5040 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun _ => by decide, fun h => absurd h (by decide)⟩
  · obtain rfl : o = (0x5040 : Word) := Option.some.inj (ho.symm.trans (by decide))
    exact ⟨by decide, by decide, by decide, fun h => absurd h (by decide), fun _ => by decide⟩

theorem msrOff_inj {amd : Bool} {m m' o : Word} (ho : msrOff amd m = some o) (ho' : msrOff amd m' = some o) :
    m = m' :=
  (msrOff_cases ho).1.symm.trans (msrOff_cases ho').1

theorem msrSlot_mem {m i : Word} (h : msrSlot m = some i) :
    m ∈ [msrStar, msrLstar, msrCstar, msrFmask, msrKernelGsBase] := by
  unfold msrSlot at h
  split_ifs at h <;> first | (subst_vars; simp) | cases h

theorem msrOff_of_slot {m i : Word} (h : msrSlot m = some i) : msrOff false m = some (VcpuLay.MSRS + i * 8) := by
  unfold msrSlot at h
  split_ifs at h <;> first | (cases h; subst_vars; decide) | cases h

theorem msrOff_xcr0 (amd : Bool) : msrOff amd msrXcr0 = some VcpuLay.XCR0 := by cases amd <;> rfl
theorem msrOff_ibpb (amd : Bool) : msrOff amd msrVmIbpbDefer = some VcpuLay.VM_IBPB_DEFER := by cases amd <;> rfl
theorem msrOff_cr2 : msrOff false msrCr2 = some VcpuLay.CR2 := rfl

/-! ## Offsets of the relation's places -/

theorem gprOff_nat (i : Fin 15) : (gprOff i).toNat = 20736 + 8 * i.val := by
  unfold gprOff
  rw [off_toNat VcpuLay.REGS i.val (by decide) (by omega)]; rfl
theorem exitOff_nat (i : Fin 30) : (exitOff i).toNat = 20992 + 8 * i.val := by
  unfold exitOff
  rw [off_toNat VcpuLay.EXIT i.val (by decide) (by omega)]; rfl

theorem vmcsOff_nat (f : Word) : (vmcsOff f).toNat < 20480 ∧ (vmcsOff f).toNat % 8 = 0 := by
  have h := vmcsIdx_lt f
  have a : VcpuLay.SHADOW.toNat = 4096 := rfl
  unfold vmcsOff
  rw [BitVec.toNat_add, BitVec.toNat_mul, a, toNat_eight]
  simp only [Nat.reducePow] at h ⊢
  omega

theorem ioOff_nat (p : BitVec 16) : 24576 ≤ (vcpuIoOff p).toNat ∧ (vcpuIoOff p).toNat < 32768 ∧
    (vcpuIoOff p).toNat % 8 = 0 := by
  have hp : p.toNat < 65536 := p.isLt
  simp [vcpuIoOff, VcpuLay.IO, BitVec.toNat_add, BitVec.toNat_mul]
  omega

/-! ## The shared part under one update -/

/-- An MSR offset is none of the shared part's other places. -/
def HO (o : Word) : Prop :=
  o.toNat ≠ 20480 ∧ o.toNat ≠ 20528 ∧ o.toNat ≠ 20520 ∧ (∀ i : Nat, i < 15 → o.toNat ≠ 20736 + 8 * i) ∧
    (∀ i : Nat, i < 30 → o.toNat ≠ 20992 + 8 * i)

theorem hO_of {o : Word} (h : o.toNat = 20504 ∨ o.toNat = 20512 ∨ o.toNat = 20544 ∨
    (20864 ≤ o.toNat ∧ o.toNat ≤ 20896) ∨ (1536 ≤ o.toNat ∧ o.toNat ≤ 1600)) : HO o :=
  ⟨by omega, by omega, by omega, fun i _ => by omega, fun i _ => by omega⟩

theorem VcpuRelCommon.upd {mem mem' : Word → Word} {v o x : Word} {vs : VcpuState} {F : VField}
    (h : VcpuRelCommon mem v vs) (hw : WrAt mem mem' v o x) (hF : ∀ i, F ≠ .gpr i)
    (hO : HO o)
    (hX : (F = .msr msrXcr0 ∧ o = VcpuLay.XCR0) ∨ (F ≠ .msr msrXcr0 ∧ o.toNat ≠ 20504))
    (hI : (F = .msr msrVmIbpbDefer ∧ o = VcpuLay.VM_IBPB_DEFER) ∨ (F ≠ .msr msrVmIbpbDefer ∧ o.toNat ≠ 20544)) :
    VcpuRelCommon mem' v { vs with fields := Function.update vs.fields F x } where
  tcb := by rw [hw.keep (by decide) (by decide) (fun e => hO.1 (by rw [← e]; rfl))]; exact h.tcb
  valid := by rw [hw.keep (by decide) (by decide) (fun e => hO.2.1 (by rw [← e]; rfl))]; exact h.valid
  pending := by rw [hw.keep (by decide) (by decide) (fun e => hO.2.2.1 (by rw [← e]; rfl))]; exact h.pending
  mrs i := by
    have e := exitOff_nat i
    rw [hw.keep (by omega) (by omega) (fun e' => hO.2.2.2.2 i.val i.isLt (by omega))]; exact h.mrs i
  gpr i := by
    have e := gprOff_nat i
    show Function.update vs.fields F x (.gpr i) = _
    rw [Function.update_of_ne (fun e' => hF i e'.symm),
      hw.keep (by omega) (by omega) (fun e' => hO.2.2.2.1 i.val i.isLt (by omega))]; exact h.gpr i
  xcr0 := by
    show Function.update vs.fields F x (.msr msrXcr0) = _
    rcases hX with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
    · rw [Function.update_self, hw.1]
    · rw [Function.update_of_ne (fun e => h1 e.symm), hw.keep (by decide) (by decide) (fun e => h2 (by rw [← e]; rfl))]
      exact h.xcr0
  ibpb := by
    show Function.update vs.fields F x (.msr msrVmIbpbDefer) = _
    rcases hI with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
    · rw [Function.update_self, hw.1]
    · rw [Function.update_of_ne (fun e => h1 e.symm), hw.keep (by decide) (by decide) (fun e => h2 (by rw [← e]; rfl))]
      exact h.ibpb

theorem toNat_ne_of_ne {a b : Word} (h : a ≠ b) : a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)

/-! ## The relations under WriteMSR's store -/

theorem set_vmx_msr (vs : VcpuState) (m x : Word) :
    vs.set .vmx (.msr m) x = { vs with fields := Function.update vs.fields (.msr m) x } := by
  simp [VcpuState.set, VField.canon]

/-- **WriteMSR's store keeps the VMX relation** (module docstring). -/
theorem msrStore_vmx {mem mem' : Word → Word} {v m o x : Word} {vs : VcpuState} (h : VcpuRelVmx mem v vs)
    (ho : msrOff false m = some o) (hw : WrAt mem mem' v o x) :
    VcpuRelVmx mem' v (vs.set .vmx (.msr m) x) := by
  rw [set_vmx_msr]
  obtain ⟨-, -, -, hv, -⟩ := msrOff_cases ho
  have hv := hv rfl
  -- a `.msr m'` place `o'`: the update and the write agree there
  have hmsr : ∀ m' o', msrOff false m' = some o' → vs.fields (.msr m') = mem (v + o') →
      Function.update vs.fields (.msr m) x (.msr m') = mem' (v + o') := by
    intro m' o' ho' hold
    by_cases e : m' = m
    · subst e; rw [ho] at ho'; cases ho'; rw [Function.update_self, hw.1]
    · obtain ⟨-, h1, h2, -⟩ := msrOff_cases ho'
      rw [Function.update_of_ne (by simpa using e),
        hw.keep h1 h2 (toNat_ne_of_ne fun e' => e (msrOff_inj ho' (e' ▸ ho)))]
      exact hold
  refine { VcpuRelCommon.upd h.toVcpuRelCommon hw (fun i => by simp) (hO_of (by omega)) ?_ ?_ with
    vmcs := fun f hf => ?_, msr := fun m' i hi => hmsr m' _ (msrOff_of_slot hi) (h.msr m' i hi),
    cr2 := hmsr _ _ msrOff_cr2 h.cr2, io := fun p => ?_ }
  · by_cases e : m = msrXcr0
    · subst e; rw [msrOff_xcr0] at ho; cases ho; exact Or.inl ⟨rfl, rfl⟩
    · refine Or.inr ⟨by simpa using e, fun e' => e (msrOff_inj ho (?_ : msrOff false msrXcr0 = some o))⟩
      rw [msrOff_xcr0]; congr 1; exact BitVec.eq_of_toNat_eq (by rw [e']; rfl)
  · by_cases e : m = msrVmIbpbDefer
    · subst e; rw [msrOff_ibpb] at ho; cases ho; exact Or.inl ⟨rfl, rfl⟩
    · refine Or.inr ⟨by simpa using e, fun e' => e (msrOff_inj ho (?_ : msrOff false msrVmIbpbDefer = some o))⟩
      rw [msrOff_ibpb]; congr 1; exact BitVec.eq_of_toNat_eq (by rw [e']; rfl)
  · have := vmcsOff_nat f
    show Function.update vs.fields (.msr m) x (.vmcs f) = _
    rw [Function.update_of_ne (by simp), hw.keep (by omega) this.2 (by omega)]; exact h.vmcs f hf
  · have := ioOff_nat p
    show vs.ioDenied p = _
    rw [hw.keep this.2.1 this.2.2 (by omega)]; exact h.io p

theorem svm_canon_of {m o : Word} (ho : svmMsrOff m = some o) : VField.canon .svm (.msr m) = .vmcb o := by
  unfold svmMsrOff at ho
  simp only [VField.canon, if_pos rfl]
  split_ifs at ho ⊢ <;> first | (cases ho; rfl) | cases ho

/-- **WriteMSR's store keeps the SVM relation** (module docstring). -/
theorem msrStore_svm {mem mem' : Word → Word} {v m o x : Word} {vs : VcpuState} (h : VcpuRelSvm mem v vs)
    (ho : msrOff true m = some o) (hw : WrAt mem mem' v o x) :
    VcpuRelSvm mem' v (vs.set .svm (.msr m) x) := by
  obtain ⟨-, -, -, -, hv⟩ := msrOff_cases ho
  have hv := hv rfl
  unfold VcpuState.set
  by_cases e1 : m = msrXcr0
  · subst e1
    rw [msrOff_xcr0] at ho; cases ho
    have hc : VField.canon .svm (.msr msrXcr0) = .msr msrXcr0 := by simp only [VField.canon]; decide
    rw [hc]
    refine { VcpuRelCommon.upd h.toVcpuRelCommon hw (fun i => by simp) (hO_of (Or.inl rfl)) (Or.inl ⟨rfl, rfl⟩)
      (Or.inr ⟨by decide, by decide⟩) with vmcb := fun off hr hh hx => ?_ }
    have := readable_nat hr
    show Function.update vs.fields (.msr msrXcr0) x (.vmcb off) = _
    rw [Function.update_of_ne (by simp), hw.keep (by omega) this.1 (by
      have : (VcpuLay.XCR0).toNat = 20504 := rfl; omega)]
    exact h.vmcb off hr hh hx
  by_cases e2 : m = msrVmIbpbDefer
  · subst e2
    rw [msrOff_ibpb] at ho; cases ho
    have hc : VField.canon .svm (.msr msrVmIbpbDefer) = .msr msrVmIbpbDefer := by simp only [VField.canon]; decide
    rw [hc]
    refine { VcpuRelCommon.upd h.toVcpuRelCommon hw (fun i => by simp) (hO_of (Or.inr (Or.inr (Or.inl rfl))))
      (Or.inr ⟨by decide, by decide⟩) (Or.inl ⟨rfl, rfl⟩) with vmcb := fun off hr hh hx => ?_ }
    have := readable_nat hr
    show Function.update vs.fields (.msr msrVmIbpbDefer) x (.vmcb off) = _
    rw [Function.update_of_ne (by simp), hw.keep (by omega) this.1 (by
      have : (VcpuLay.VM_IBPB_DEFER).toNat = 20544 := rfl; omega)]
    exact h.vmcb off hr hh hx
  have hs : svmMsrOff m = some o := by
    unfold msrOff at ho; rw [if_neg e1, if_neg e2, if_pos rfl] at ho; exact ho
  have hO : 1536 ≤ o.toNat ∧ o.toNat ≤ 1600 := by
    rcases hv with h' | h' | h'
    · exact absurd (msrOff_inj ho (by rw [msrOff_xcr0]; congr 1; exact BitVec.eq_of_toNat_eq (by rw [h']; rfl))) e1
    · exact absurd (msrOff_inj ho (by rw [msrOff_ibpb]; congr 1; exact BitVec.eq_of_toNat_eq (by rw [h']; rfl))) e2
    · exact h'
  rw [svm_canon_of hs]
  refine { VcpuRelCommon.upd h.toVcpuRelCommon hw (fun i => by simp) (hO_of (by omega))
    (Or.inr ⟨by simp, by omega⟩) (Or.inr ⟨by simp, by omega⟩) with vmcb := fun off hr hh hx => ?_ }
  show Function.update vs.fields (.vmcb o) x (.vmcb off) = _
  by_cases e : off = o
  · subst e; rw [Function.update_self, hw.1]
  · have := readable_nat hr
    rw [Function.update_of_ne (by simpa using e), hw.keep (by omega) this.1 (toNat_ne_of_ne e)]
    exact h.vmcb off hr hh hx

/-! ## FL4's store -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

/-- **FL4's `Store::write` of a VCPU word** gives `WrAt` on the relation's memory. -/
theorem memW_wr {v x : U64} (hv : VFits v) {o : Word} (ho1 : o.toNat < 32768) (ho2 : o.toNat % 8 = 0)
    (hx : x.bv = v.bv + o) (s : S) (val : U64) :
    WrAt (memW st s) (memW st (L.wr s x val)) v.bv o val.bv := by
  have hx' : x = ⟨v.bv + o⟩ := by rcases x with ⟨b⟩; exact congrArg (fun b => (⟨b⟩ : U64)) hx
  have hal : ∀ off : Word, off.toNat < 32768 → off.toNat % 8 = 0 → P1.Aligned ⟨v.bv + off⟩ := by
    intro off h1 h2
    unfold P1.Aligned; rw [vo_val hv h1]; have := hv.1; omega
  subst hx'
  refine ⟨?_, fun off h1 h2 hne => ?_⟩
  · unfold memW; rw [L.mem_wr _ _ _ _ (hal o ho1 ho2) (hal o ho1 ho2), if_pos rfl]
  · unfold memW; rw [L.mem_wr _ _ _ _ (hal o ho1 ho2) (hal off h1 h2), if_neg]
    intro e
    have e2 := congrArg UScalar.val e
    rw [vo_val hv ho1, vo_val hv h1] at e2
    exact hne (BitVec.eq_of_toNat_eq (by omega))

/-- **`ReplyKeepsV` [J]** (module docstring): FL4's `reply` after WriteMSR's store (state `L.wr s x value`, the
read-back `value`) leaves the VCPU object at `v` alone. -/
def ReplyKeepsV (st : machine.Store S) [L : P1.LawfulStore st] (s : S) (x value : U64) (call : Bool) (v : U64) :
    Prop :=
  vcpu.reply st (L.wr s x value) call value ⦃ s' =>
    AgreeAt (memW st (L.wr s x value)) (memW st s') v.bv ⦄

/-- The post of WriteMSR's tail against `checkMsrWrite` (module docstring). -/
def TailPost (R : (Word → Word) → Word → VcpuState → Prop) (k : VirtKind) (st : machine.Store S)
    [L : P1.LawfulStore st] (s1 : S) (v f value : U64) (vs : VcpuState)
    (r : (core.result.Result Unit error.Exc) × S × A) : Prop :=
  (checkMsrWrite f.bv value.bv = .ok () ∧ r.1 = .Ok () ∧ R (memW st r.2.1) v.bv (vs.set k (.msr f.bv) value.bv)) ∨
  (∃ e e', checkMsrWrite f.bv value.bv = .error e' ∧ SysErrRel e e' ∧ r.1 = .Err e ∧ r.2.1 = s1)

theorem wrmsrTail_gen {a1 : A} (hc : CapAgree ar a1) {s1 : S} {v : U64} (hv : VFits v) (f value : U64)
    (amd call : Bool) (R : (Word → Word) → Word → VcpuState → Prop) (k : VirtKind) (vs : VcpuState)
    (hR : ∀ o, msrOff amd f.bv = some o → ∀ mem', WrAt (memW st s1) mem' v.bv o value.bv →
      R mem' v.bv (vs.set k (.msr f.bv) value.bv))
    (hRc : ∀ mem mem', AgreeAt mem mem' v.bv → R mem v.bv (vs.set k (.msr f.bv) value.bv) →
      R mem' v.bv (vs.set k (.msr f.bv) value.bv))
    (hK : ∀ x : U64, x.bv.toNat % 8 = 0 → ReplyKeepsV st s1 x value call v) :
    wrmsrTail st ar s1 a1 v f value amd call ⦃ r => TailPost R k st s1 v f value vs r ⦄ := by
  obtain ⟨r, hr, hrel, haddr⟩ := fl4WriteMsr_rel hc v f value amd
  unfold wrmsrTail
  rw [hr, bind_ok]
  cases r with
  | Ok x =>
    rcases hcm : checkMsrWrite f.bv value.bv with e' | u
    · rw [hcm] at hrel; exact hrel.elim
    cases u
    obtain ⟨o, ho, hox⟩ := Option.map_eq_some_iff.1 (haddr x rfl)
    obtain ⟨-, h1, h2, -⟩ := msrOff_cases ho
    have hw := memW_wr (st := st) hv h1 h2 hox.symm s1 value
    have hxa : P1.Aligned x := by
      have e : x = ⟨v.bv + o⟩ := by rcases x with ⟨b⟩; exact congrArg (fun b => (⟨b⟩ : U64)) hox.symm
      unfold P1.Aligned; rw [e, vo_val hv h1]; have := hv.1; omega
    dsimp only
    rw [L.write_eq, bind_ok, L.read_eq, bind_ok, L.mem_wr _ _ _ _ hxa hxa, if_pos rfl]
    refine WP.spec_bind (hK x hxa) fun s3 hag => (WP.spec_ok _).2 (Or.inl ⟨hcm, rfl, ?_⟩)
    exact hRc _ _ hag (hR o ho _ hw)
  | Err e =>
    rcases hcm : checkMsrWrite f.bv value.bv with e' | u
    · rw [hcm] at hrel
      exact (WP.spec_ok _).2 (Or.inr ⟨e, e', hcm, hrel, rfl, rfl⟩)
    · rw [hcm] at hrel; exact hrel.elim

/-- **WriteMSR's tail on VMX** (module docstring; premises `CapAgree` [P], `ReplyKeepsV` [J]). -/
theorem wrmsrTail_vmx {a1 : A} (hc : CapAgree ar a1) {s1 : S} {v : U64} (hv : VFits v) (f value : U64)
    (call : Bool) {vs : VcpuState} (h : VcpuRelVmx (memW st s1) v.bv vs)
    (hK : ∀ x : U64, x.bv.toNat % 8 = 0 → ReplyKeepsV st s1 x value call v) :
    wrmsrTail st ar s1 a1 v f value false call ⦃ r => TailPost VcpuRelVmx .vmx st s1 v f value vs r ⦄ :=
  wrmsrTail_gen hc hv f value false call VcpuRelVmx .vmx vs (fun _ ho _ hw => msrStore_vmx h ho hw)
    (fun _ _ hag h' => VcpuRelVmx.congr hag h') hK

/-- **WriteMSR's tail on SVM** (module docstring; premises `CapAgree` [P], `ReplyKeepsV` [J]). -/
theorem wrmsrTail_svm {a1 : A} (hc : CapAgree ar a1) {s1 : S} {v : U64} (hv : VFits v) (f value : U64)
    (call : Bool) {vs : VcpuState} (h : VcpuRelSvm (memW st s1) v.bv vs)
    (hK : ∀ x : U64, x.bv.toNat % 8 = 0 → ReplyKeepsV st s1 x value call v) :
    wrmsrTail st ar s1 a1 v f value true call ⦃ r => TailPost VcpuRelSvm .svm st s1 v f value vs r ⦄ :=
  wrmsrTail_gen hc hv f value true call VcpuRelSvm .svm vs (fun _ ho _ hw => msrStore_svm h ho hw)
    (fun _ _ hag h' => VcpuRelSvm.congr hag h') hK

end

/-! ## Spec side -/

section
variable {Z : Type}

theorem getVcpu_out {σ : State Z} {v : ObjRef} {vs : VcpuState} (hv : vcpuAt σ v = some vs)
    {y : VcpuState × State Z} (hy : y ∈ (getVcpu (Z := Z) v σ).1) : y = (vs, σ) := by
  unfold vcpuAt at hv
  unfold getVcpu at hy
  obtain ⟨z, hz, hy⟩ := hy
  unfold getObject NonDet.getsThe readObject at hz
  split at hv
  · next st h =>
    rw [h] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    cases hv
    exact Set.mem_singleton_iff.1 hy
  · cases hv

/-- **`vcpuUpdate`**: the VCPU at `v` becomes `f vs`. -/
theorem vcpuUpdate_out {σ : State Z} {v : ObjRef} {vs : VcpuState} (hv : vcpuAt σ v = some vs)
    {f : VcpuState → VcpuState} {x : Unit × State Z} (hx : x ∈ (vcpuUpdate (Z := Z) v f σ).1) :
    vcpuAt x.2 v = some (f vs) := by
  obtain ⟨y, hy, hx⟩ := hx
  obtain rfl := getVcpu_out hv hy
  rw [setVcpu_out hx]; unfold vcpuAt; simp

/-- **The spec's WriteMSR** (`performVcpuInvocation (.writeMsr v m val)`): the VCPU becomes
`vs.set virtKind (.msr m) val`, the reply is `[val]`. -/
theorem writeMsr_out {σ : State Z} {v : ObjRef} {m val : Word} {vs : VcpuState} (hv : vcpuAt σ v = some vs)
    {x : List Data × State Z} (hx : x ∈ (performVcpuInvocation (Z := Z) (.writeMsr v m val) σ).1) :
    vcpuAt x.2 v = some (vs.set virtKind (.msr m) val) ∧ x.1 = [val] := by
  simp only [performVcpuInvocation] at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hx
  exact ⟨vcpuUpdate_out hv hy, rfl⟩

theorem set_msr_ne_svm {k : VirtKind} (hk : k ≠ .svm) (vs : VcpuState) (m x : Word) :
    vs.set k (.msr m) x = vs.set .vmx (.msr m) x := by
  simp [VcpuState.set, VField.canon, hk]

/-- **WriteMSR, both halves, VMX**: FL4's relation after the tail and the spec's VCPU after WriteMSR relate. -/
theorem writeMsr_rel_vmx (hk : virtKind ≠ .svm) {mem : Word → Word} {σ : State Z} {v : ObjRef} {m val : Word}
    {vs : VcpuState} (hv : vcpuAt σ v = some vs) (hf : VcpuRelVmx mem v (vs.set .vmx (.msr m) val))
    {x : List Data × State Z} (hx : x ∈ (performVcpuInvocation (Z := Z) (.writeMsr v m val) σ).1) :
    VRelAt mem x.2 v := by
  obtain ⟨e, -⟩ := writeMsr_out hv hx
  exact ⟨_, e, fun h => absurd h hk, fun _ => by rw [set_msr_ne_svm hk]; exact hf⟩

/-- **WriteMSR, both halves, SVM**. -/
theorem writeMsr_rel_svm (hk : virtKind = .svm) {mem : Word → Word} {σ : State Z} {v : ObjRef} {m val : Word}
    {vs : VcpuState} (hv : vcpuAt σ v = some vs) (hf : VcpuRelSvm mem v (vs.set .svm (.msr m) val))
    {x : List Data × State Z} (hx : x ∈ (performVcpuInvocation (Z := Z) (.writeMsr v m val) σ).1) :
    VRelAt mem x.2 v := by
  obtain ⟨e, -⟩ := writeMsr_out hv hx
  exact ⟨_, e, fun _ => by rw [hk]; exact hf, fun h => absurd hk h⟩

end

end
end Fl4Proofs.P3.VirtMsrStore
