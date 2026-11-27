/-
P3 (line mmuAD, gen 32): **X86VCPUWriteVMCS end to end at `JAtZV3`** — the extracted `vcpu.decode` at label
`X86VCPUWriteVMCS` (vcpu.rs l. 822-900: `stall`, `cur_thread`, `virtualization`, `syscall_arg` 0/1, the label and
length checks, `sanitize_vmcs`, `vcpu_sync`, `write_vmcs`, the `SVM_CPU := 0` flush for the paging fields, `reply`),
paired with the extended spec's `decodeVcpuInvocation` (Ext/VirtVcpu: `.writeVmcs v f val` with `val` the spec's
`sanitizeVmcs f x`, or its error) and `performVcpuInvocation (.writeVmcs v f val)` (`vcpuUpdate v (·.set virtKind
(.vmcs f) val)`, reply `[val]`). Uses the virt line's gen 11 `VirtSanEq.sanitize_vmcs_rel` and
`VirtSanRel.VcpuRelVmx.write_vmcs` (brought over verbatim in this generation's first commit) and gen 30's
`JAtZV3.vcpuStep`.

* **`v3_vmcs_addr`**: FL4's `vcpu.vmcs_addr v f` is the word `v + vmcsOff f` (the spec relation's place), for
  every `f` (11-bit index, no overflow). `v3_vmcsOff_val` (`vmcsOff f = 4096 + 8 · vmcsIdx f`).
* **`JAtZV3.vmcsWr`**: FL4's store of `x` at `v + vmcsOff f` for a writable VMCS field, paired with the spec VCPU
  `vs.set virtKind (.vmcs f) x`, keeps `JAtZV3` (VMX platform). **`JAtZV3.svmWr`**: a store to the `SVM_CPU` word
  keeps `JAtZV3` with the spec unchanged (the word is unread: gen 30's `JAtZV3.vcpuWr`).
* Spec side: **`zv_label_wvmcs`** (`vcpuLabelOf 75 = some .writeVmcs`), **`zv_decode_wvmcs`** (the decoder at a
  WriteVMCS message of length ≥ 2 on VMX is the match on `sanitizeVmcs f x`), **`zv_perform_wvmcs`**.
* **`JAtZV3.writeVmcsJ`**: `vcpu.decode … X86VCPUWriteVMCS len p call buf ex` at a `JAtZV3` state, `p ∈ V` a spec
  VCPU, `len ≥ 2`: the post names FL4's `cur_thread` `ct` and the two argument words `f`, `x` it read
  (`syscall_arg ct buf 0/1` at the entry state), and for every spec argument list agreeing with them (length `len`,
  `args[0] = f`, `args[1] = x`): either sanitize failed — FL4 returns `Err e`, the spec decoder throws `e'` with
  `SysErrRel e e'`, the store is unchanged and `JAtZV3` holds (another arch state) — or it succeeded with `y` — the
  spec decoder returns `.writeVmcs p f y`, `performVcpuInvocation` has exactly one outcome `([y], σ')`, `JAtZV3`
  holds at FL4's state just before `reply` and `σ'`, and FL4's final state is `vcpu.reply` of it with `y`
  (l4v `handle_invocation`'s `reply_from_kernel` tail on `[y]`, left to the caller as for every invocation).

Named premises (all **[P]**, platform agreements, module-local definitions):
* **`ZvVirtAgree arI`** — `Arch::virtualization` answers 2 exactly when the spec's `virtKind` is `.svm`, at every arch
  state (FL4 `fl4-arch-x86_64` `arch.rs` l. 57 returns `vm::backend()`: 0 none, 1 VMX, 2 SVM, fixed at boot; the spec's
  `virtKind` is the platform's backend, Ext/VirtBackend). Not false on reachable states: the backend never changes
  after boot. Used here with `hvk : virtKind = .vmx` (WriteVMCS is VMX-only on both sides).
* **`ZvSyncKeep arI AR`** — `Arch::vcpu_sync` keeps the arch relation `AR` (machine.rs l. 62-66: it brings the VCPU's
  software VMCS image up to date with the hardware VMCS; `fl4-arch-x86_64` `vm::sync`: VMREADs of guest state, no CR3
  or paging change). The other `Arch` operations have this as an `ARKeep` field; `vcpu_sync` was not needed before.
  Non-vacuous: the model platform `XTopJointMachRel.modelArch` has `vcpu_sync a _ _ := ok a`.
* **`∀ a, VirtSanEq.CapAgree arI a`** — virt gen 11's [P] `CapAgree` at every arch state (the capability MSR words are
  read once at boot, `vm::capability`; `stall`'s `vcpu_barrier` may change the arch value before `sanitize_vmcs`).

No other premise; no existing statement changed. Not covered: the SVM decline branch (`virtualization = 2`), lengths
< 2, ReadVMCS; the caller's `reply` / `handle_invocation` tail.
-/
import Fl4Proofs.P3.JAtZV3Gpr
import Fl4Proofs.P3.VirtSanEq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Premises (platform) -/

section
variable {A : Type}

/-- **[P]** `Arch::virtualization` answers 2 exactly on an SVM platform (module docstring). -/
def ZvVirtAgree (arI : machine.Arch A) : Prop :=
  ∀ a, ∃ i, arI.virtualization a = ok i ∧ (i = 2#u64 ↔ Fl4Spec.virtKind = .svm)

/-- **[P]** `Arch::vcpu_sync` keeps the arch relation (module docstring). -/
def ZvSyncKeep (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ a v f c, AR a c → arI.vcpu_sync a v f ⦃ a' => AR a' c ⦄

end

/-! ## FL4's VMCS place -/

theorem v3_shr1 (x : U64) : x >>> (1#i32) = ok ⟨x.bv >>> 1⟩ := by
  rw [VirtSanEq.shr_i32 x _ (by decide) (by decide)]; rfl
theorem v3_shr10 (x : U64) : x >>> (10#i32) = ok ⟨x.bv >>> 10⟩ := by
  rw [VirtSanEq.shr_i32 x _ (by decide) (by decide)]; rfl
theorem v3_shl7 (x : U64) : x <<< (7#i32) = ok ⟨x.bv <<< 7⟩ := by
  rw [VirtSanEq.shl_i32 x _ (by decide) (by decide)]; rfl

theorem v3_mul8 (x : U64) (h : x.bv.toNat < 2048) : x * 8#u64 = ok ⟨x.bv * (8 : BitVec 64)⟩ := by
  have hx : x.val < 2048 := h
  obtain ⟨w, hw, hwv⟩ := P1.spec_ex_fd (U64.mul_spec (x := x) (y := 8#u64) (by scalar_tac))
  rw [hw]
  congr 1
  apply UScalar.eq_of_val_eq
  have h8 : (8#u64 : U64).val = 8 := by simp
  show w.val = (x.bv * (8 : BitVec 64)).toNat
  rw [hwv, h8, BitVec.toNat_mul, VirtVcpuRel.toNat_eight, show x.val = x.bv.toNat from rfl,
    Nat.mod_eq_of_lt (by omega)]

theorem v3_vmcsOff_val (f : Fl4Spec.Word) : (Fl4Spec.vmcsOff f).toNat = 4096 + (Fl4Spec.vmcsIdx f).toNat * 8 := by
  have h := VirtVcpuRel.vmcsIdx_lt f
  have a : Fl4Spec.VcpuLay.SHADOW.toNat = 4096 := rfl
  unfold Fl4Spec.vmcsOff
  rw [BitVec.toNat_add, BitVec.toNat_mul, a, VirtVcpuRel.toNat_eight]
  simp only [Nat.reducePow] at h ⊢
  omega

/-- **FL4's `vmcs_addr v f` is `v + vmcsOff f`** (module docstring). -/
theorem v3_vmcs_addr (v f : U64) : vcpu.vmcs_addr v f = ok ⟨v.bv + Fl4Spec.vmcsOff f.bv⟩ := by
  have hI := VirtVcpuRel.vmcsIdx_lt f.bv
  unfold Fl4Spec.vmcsIdx at hI
  unfold vcpu.vmcs_addr
  simp only [lift, bind_ok, v3_shr1, v3_shr10, v3_shl7, VirtSanEq.shr_13, VirtSanEq.shl_9]
  rw [v3_mul8 _ ?hb]
  · simp only [bind_ok]
    congr 1
    apply VirtSanEq.u64_ext
    simp only [core.num.U64.wrapping_add_bv_eq, UScalar.bv_and, UScalar.bv_or, vcpu.SHADOW, Fl4Spec.vmcsOff,
      Fl4Spec.vmcsIdx, U64.ofNat_bv]
    rw [BitVec.add_assoc]
    congr 2
    all_goals first | rfl | decide
  · simp only [UScalar.bv_and, UScalar.bv_or, U64.ofNat_bv]
    first | exact hI | simpa using hI

/-! ## The VCPU word steps -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **FL4's store at a writable VMCS field's place, paired with the spec's field update** (module docstring). -/
theorem JAtZV3.vmcsWr (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    (hvk : Fl4Spec.virtKind = .vmx) {f : Fl4Spec.Word} (hf : Fl4Spec.Vmx.writable f = true) (x : U64)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s ⟨p.bv + Fl4Spec.vmcsOff f⟩ x) a
      (Notif.updK σ p.bv (.archObj (.vcpu (vs.set Fl4Spec.virtKind (.vmcs f) x.bv)))) := by
  have Ly := J.z2.zv.base.jvLay J.z2.zv.vm
  have hfv := Ly.vfit p hp
  have hfu := hfv.2
  have ho := VirtVcpuRel.vmcsOff_lt' f
  have hov := v3_vmcsOff_val f
  have hil := VirtVcpuRel.vmcsIdx_lt f
  simp only [Nat.reducePow] at hil
  have e1 := v3_toNat_add hfu ho
  have hwv : (⟨p.bv + Fl4Spec.vmcsOff f⟩ : U64).val = p.val + 4096 + (Fl4Spec.vmcsIdx f).toNat * 8 := by
    show (p.bv + Fl4Spec.vmcsOff f).toNat = _
    rw [e1, hov]; omega
  have hal : P1.Aligned (⟨p.bv + Fl4Spec.vmcsOff f⟩ : U64) := by
    show (⟨p.bv + Fl4Spec.vmcsOff f⟩ : U64).val % 8 = 0
    have : p.val % 32768 = 0 := hfv.1
    rw [hwv]; omega
  have hW : P1.WritesIn st s (L.wr s ⟨p.bv + Fl4Spec.vmcsOff f⟩ x) (· = ⟨p.bv + Fl4Spec.vmcsOff f⟩) :=
    P1.writesIn_wr hal
  have R0 := J.vr p hp vs hk
  rw [hvk] at R0
  have R0' : Fl4Spec.VcpuRelVmx (vmemW (L.mem s)) p.bv vs := R0
  have R1 := VirtSanRel.VcpuRelVmx.write_vmcs (x := x.bv) R0' hf
  have hag : VirtVcpuRel.AgreeAt (Function.update (vmemW (L.mem s)) (p.bv + Fl4Spec.vmcsOff f) x.bv)
      (vmemW (L.mem (L.wr s ⟨p.bv + Fl4Spec.vmcsOff f⟩ x))) p.bv := by
    intro o hol
    by_cases e : o = Fl4Spec.vmcsOff f
    · subst e
      rw [Function.update_self]
      have ha : (p.bv + Fl4Spec.vmcsOff f).toNat % 8 = 0 := hal
      unfold vmemW
      rw [if_pos ha, L.mem_wr s _ x _ hal hal, if_pos rfl]
    · have hne : p.bv + o ≠ p.bv + Fl4Spec.vmcsOff f := fun h => e (add_left_cancel h)
      rw [Function.update_of_ne hne]
      exact v3_agree hfu (o0 := Fl4Spec.vmcsOff f)
        (fun b hb _ _ hne' => hW.mem_eq hb fun e' => hne' (by rw [e', hwv, hov]; omega)) o hol e
  have R2 := VirtVcpuRel.VcpuRelVmx.congr hag R1
  have hR : Fl4Spec.VcpuRel Fl4Spec.virtKind (vmemW (L.mem (L.wr s ⟨p.bv + Fl4Spec.vmcsOff f⟩ x))) p.bv
      (vs.set Fl4Spec.virtKind (.vmcs f) x.bv) := by
    rw [hvk]; exact R2
  have hlt := VirtSanRel.vmcsOff_lt_tcb f
  have ht : Fl4Spec.VcpuLay.TCB.toNat = 20480 := rfl
  rw [ht, hov] at hlt
  exact J.vcpuStep hp hal (by rw [hwv]; omega) (by rw [hwv]; omega) ⟨by rw [hwv]; omega, by rw [hwv]; omega,
    by rw [hwv]; omega⟩ x hk _ rfl hR

/-- **A store to the `SVM_CPU` word** keeps `JAtZV3`, spec unchanged (module docstring). -/
theorem JAtZV3.svmWr (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V) (x : U64) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s (svmA p) x) a σ := by
  have Ly := J.z2.zv.base.jvLay J.z2.zv.vm
  have hf := Ly.vfit p hp
  have esv := lay_svm_val hf.2
  have h1 : p.val % 32768 = 0 := hf.1
  have aS : P1.Aligned (svmA p) := by unfold P1.Aligned; rw [esv]; omega
  exact J.vcpuWr hp aS (by rw [esv]; omega) (by rw [esv]; omega) (by rw [esv]; omega)
    (by rw [esv]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega) x

end

/-! ## The spec side -/

section
open Fl4Spec

theorem zv_label_wvmcs : vcpuLabelOf (75 : Data) = some .writeVmcs := by decide

theorem zv_decode_wvmcs {args : List Data} {v : ObjRef} {ec : List (Cap × CslotPtr)} {f x : Word}
    (hvk : virtKind = .vmx) (hl : 2 ≤ args.length) (h0 : args.getD 0 0 = f) (h1 : args.getD 1 0 = x) :
    decodeVcpuInvocation (Z := Unit) 75 args v ec =
      match sanitizeVmcs f x with
      | .error e => NonDetE.throwError e
      | .ok val => NonDetE.returnOk (.writeVmcs v f val) := by
  have hn : ¬ args.length < 2 := by omega
  simp only [decodeVcpuInvocation, zv_label_wvmcs, hvk, h0, h1, hn, decide_false, reduceCtorEq,
    Bool.false_eq_true, ↓reduceIte]
  rfl

theorem zv_perform_wvmcs {σ : State Unit} {v : ObjRef} {vs : VcpuState}
    (hk : σ.kheap v = some (.archObj (.vcpu vs))) (f val : Word) :
    performVcpuInvocation (Z := Unit) (.writeVmcs v f val) σ =
      ({([val], Notif.updK σ v (.archObj (.vcpu (vs.set virtKind (.vmcs f) val))))}, False) := by
  show ((vcpuUpdate (Z := Unit) v fun s => VcpuState.set virtKind s (VField.vmcs f) val) >>= fun _ =>
    (pure [val] : SMonad Unit (List Data))) σ = _
  rw [Notif.nd_bind_one (zv_vcpuUpdate_eq hk _)]
  rfl

end

/-! ## The invocation -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

theorem zv_lbl_ne {x y : U64} (h : x.val ≠ y.val) : ¬ x = y := fun e => h (congrArg UScalar.val e)

theorem zv_wvmcs_bv : fl4_abi.label.X86VCPUWriteVMCS.bv = (75 : Fl4Spec.Data) := by
  unfold fl4_abi.label.X86VCPUWriteVMCS; rfl

set_option maxHeartbeats 16000000 in
/-- **X86VCPUWriteVMCS at `JAtZV3`, paired with the spec's decode and perform** (module docstring). -/
theorem JAtZV3.writeVmcsJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hSy : ZvSyncKeep arI AR) (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a')
    (hvk : Fl4Spec.virtKind = .vmx) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {len : U64} (hlen : 2 ≤ len.val) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUWriteVMCS len p call buf ex ⦃ r => ∃ ct f x : U64,
      sched.cur_thread st s = ok ct ∧ msg.syscall_arg st s ct buf 0#u64 = ok f ∧
      msg.syscall_arg st s ct buf 1#u64 = ok x ∧
      ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), args.length = len.val →
        args.getD 0 0 = f.bv → args.getD 1 0 = x.bv →
        (∃ e e', r.1 = .Err e ∧ SysErrRel e e' ∧
          Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUWriteVMCS.bv args p.bv ec =
            Fl4Spec.NonDetE.throwError e' ∧
          r.2.1 = s ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s r.2.2 σ) ∨
        (∃ (y : U64) (s3 : S) (σ' : Fl4Spec.State Unit), r.1 = .Ok () ∧
          Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUWriteVMCS.bv args p.bv ec =
            Fl4Spec.NonDetE.returnOk (.writeVmcs p.bv f.bv y.bv) ∧
          Fl4Spec.performVcpuInvocation (Z := Unit) (.writeVmcs p.bv f.bv y.bv) σ = ({([y.bv], σ')}, False) ∧
          JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s3 r.2.2 σ' ∧ vcpu.reply st s3 call y = ok r.2.1) ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  unfold vcpu.decode
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar hvt) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  have J1 := J.archV hAR1
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  rw [hct, bind_ok]
  obtain ⟨i, hi, hi2⟩ := hVA a1
  have hi2' : ¬ i = 2#u64 := fun e => by have := hi2.1 e; rw [hvk] at this; exact absurd this (by decide)
  rw [hi, bind_ok]
  have g0 : len > 0#u64 := by scalar_tac
  have g1 : len > 1#u64 := by scalar_tac
  have g2 : ¬ len < 2#u64 := by scalar_tac
  obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
  obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
  rw [if_pos g0, hf, bind_ok, if_pos g1, hx, bind_ok]
  have n73 : ¬ fl4_abi.label.X86VCPUWriteVMCS = fl4_abi.label.X86VCPUSetTCB :=
    zv_lbl_ne (by simp [fl4_abi.label.X86VCPUWriteVMCS, fl4_abi.label.X86VCPUSetTCB])
  have n81 : ¬ fl4_abi.label.X86VCPUWriteVMCS = fl4_abi.label.X86VCPUWriteRegisters :=
    zv_lbl_ne (by simp [fl4_abi.label.X86VCPUWriteVMCS, fl4_abi.label.X86VCPUWriteRegisters])
  have n76 : ¬ fl4_abi.label.X86VCPUWriteVMCS = fl4_abi.label.X86VCPUFlushTLB :=
    zv_lbl_ne (by simp [fl4_abi.label.X86VCPUWriteVMCS, fl4_abi.label.X86VCPUFlushTLB])
  have n74 : ¬ fl4_abi.label.X86VCPUWriteVMCS = fl4_abi.label.X86VCPUReadVMCS :=
    zv_lbl_ne (by simp [fl4_abi.label.X86VCPUWriteVMCS, fl4_abi.label.X86VCPUReadVMCS])
  rw [if_neg n73, if_neg n81, if_neg n76, if_neg n74]
  simp only [↓reduceIte, if_neg hi2', if_neg g2, bind_ok]
  obtain ⟨r, hr, hrel⟩ := VirtSanEq.sanitize_vmcs_rel (hCap a1) f x
  rw [hr, bind_ok]
  -- the spec decoder at these arguments
  have hD : ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), args.length = len.val →
      args.getD 0 0 = f.bv → args.getD 1 0 = x.bv →
      Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUWriteVMCS.bv args p.bv ec =
        match Fl4Spec.sanitizeVmcs f.bv x.bv with
        | .error e => Fl4Spec.NonDetE.throwError e
        | .ok val => Fl4Spec.NonDetE.returnOk (.writeVmcs p.bv f.bv val) := by
    intro args ec hl h0 h1
    rw [zv_wvmcs_bv]
    exact zv_decode_wvmcs hvk (by omega) h0 h1
  rcases r with y | e
  · -- sanitized value `y`
    have hs : Fl4Spec.sanitizeVmcs f.bv x.bv = .ok y.bv := by
      rcases hsv : Fl4Spec.sanitizeVmcs f.bv x.bv with er | y'
      · rw [hsv] at hrel; exact absurd hrel (by simp [VirtSanEq.WordResRel])
      · rw [hsv] at hrel; simp only [VirtSanEq.WordResRel] at hrel; rw [hrel]
    have hw : Fl4Spec.Vmx.writable f.bv = true := by
      by_contra hw
      simp only [Bool.not_eq_true] at hw
      simp [Fl4Spec.sanitizeVmcs, hw] at hs
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (hSy a1 p f _ hAR1) fun a2 hAR2 => ?_
    have J2 := J.archV hAR2
    unfold vcpu.write_vmcs
    rw [v3_vmcs_addr, bind_ok]
    refine WP.spec_bind (P1.LawfulStore.write_spec s _ _) fun s2 e2 => ?_
    subst e2
    have J3 := J2.vmcsWr hp hvk hw y hk
    refine WP.spec_bind (Pₘ := fun s3 => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s3 a2
      (Notif.updK σ p.bv (.archObj (.vcpu (vs.set Fl4Spec.virtKind (.vmcs f.bv) y.bv))))) ?_ ?_
    · repeat' split
      all_goals first
        | exact (WP.spec_ok _).2 J3
        | (simp only [vcpu.set, lift, bind_ok]
           exact WP.spec_mono (P1.LawfulStore.write_spec _ _ _) fun s3 e3 => by
             rw [e3]; exact J3.svmWr hp 0#u64)
    · intro s3 J4
      obtain ⟨s4, h4, -⟩ := P1.spec_ex_fd (P0.vcpu.reply.p0 st s3 call y (P1.LawfulStore.total (st := st)))
      rw [h4, bind_ok]
      refine (WP.spec_ok _).2 ⟨ct, f, x, rfl, hf, hx, fun args ec hl h0 h1 => Or.inr ⟨y, s3, _, rfl, ?_,
        zv_perform_wvmcs hk _ _, J4, h4⟩⟩
      rw [hD args ec hl h0 h1, hs]
  · -- sanitize refused
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, WP.spec_ok]
    refine ⟨ct, f, x, rfl, hf, hx, fun args ec hl h0 h1 => ?_⟩
    rcases hsv : Fl4Spec.sanitizeVmcs f.bv x.bv with e' | y'
    · rw [hsv] at hrel
      exact Or.inl ⟨e, e', rfl, hrel, by rw [hD args ec hl h0 h1, hsv], by first | rfl | trivial, J1⟩
    · rw [hsv] at hrel; exact absurd hrel (by simp [VirtSanEq.WordResRel])

end

end

end Fl4Proofs.P3
