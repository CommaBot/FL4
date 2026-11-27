/-
P3 (line mmuAD, gen 37): **one post for every X86VCPU label at `JAtZV3`** — the shape the VCPU dispatcher
(`P3/JAtZV3VDisp`) proves for the whole extracted `vcpu.decode`, and the five end-to-end theorems of gens 32–36
(`setTcbJ`, `writeRegsJ`, `writeVmcsJ`, `writeMsrJ`, `writeVmcbJ`) restated in it.

* **`VArgs st s ct buf len args`**: a spec argument list agrees with FL4's argument words — `len` of them, and
  word `i < len` is what `msg.syscall_arg st s ct buf i` reads at the entry state (FL4 reads exactly these, the
  front end's `getMrs`). `VArgs.a0` / `a1`: the two first words.
* **`VDecTail st ct call rep s' r2`**: how FL4 ends a successful invocation from the state `s'` paired with the
  spec's perform outcome (reply words `rep`) to its final state `r2`: (a) `rep = []` and the caller's
  `set_thread_state ct TS_RESTART` (SetTCB, WriteRegisters, FlushTLB, the I/O-port labels); (b) `rep = [y]` and
  `vcpu.reply s' call y` (the one-word replies); (c) `rep = ws` and `vcpuReplyWs s' ct call ws` — FL4's
  in-decode reply of several words (ReadVMCB: `lookup_ipc_buffer`, `set_mr` word by word from 0, `BADGE := 0`,
  message info of the count `set_mr` returned, `TS_RUNNING`; with `call = false` only `TS_RUNNING`), the words
  given as a list.
* **`VDecPost … lbl len p call buf b c r`**: FL4's `cur_thread` `ct`, and for every spec argument list agreeing
  with FL4's words (`VArgs`) and every spec extra-cap list agreeing with FL4's first extra-cap slot (`StcbCaps b c`,
  gen 35): either an error — FL4 `Err e`, the spec decoder (as `ExceptT.run … σ`) throws `e'` with
  `SysErrRel e e'`, FL4's store unchanged and `JAtZV3` holds with the arch state after the decode — or success —
  the spec decoder returns some `inv`, `performVcpuInvocationF inv` (FL4's perform, `Ext/VirtKernelF`) has exactly
  the one outcome `(rep, σ')`, `JAtZV3` at an FL4 state `s'` and `σ'` (any `Ac'`/`Lst'`), and `VDecTail` from `s'`.
* **`JAtZV3.vdErr`**: the error case from an error the decoder throws at every agreeing argument list.
* Adapters (proofs only, from the existing statements): **`JAtZV3.vdStcb`** (`setTcbJ`), **`vdWregs`**
  (`writeRegsJ`, `len ≥ 15`), **`vdWvmcs`** (`writeVmcsJ`, VMX, `len ≥ 2`), **`vdWmsr`** (`writeMsrJ`, `len ≥ 2`),
  **`vdWvmcb`** (`writeVmcbJ`, SVM, `len ≥ 2`). `performVcpuInvocation` and `performVcpuInvocationF` agree on every
  invocation but `setTcb` (definitionally).
* Spec labels: `zv_label_*` / `zv_*_bv` for the labels not named before (ReadMSR 49, ReadVMCS 74, FlushTLB 76,
  ReadVMCB 77, EnableIOPort 79, DisableIOPort 80).

Premises: those of the five theorems ([P] `ZvVirtAgree`, [P] `ZvSyncKeep`, [P] `∀ a, CapAgree arI a`,
`P0.ArchTotal`, `ARKeep`), unchanged. No new premise; no existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3SetTcb
import Fl4Proofs.P3.JAtZV3Vmcb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Spec labels -/

section
open Fl4Spec

theorem zv_label_rmsr : vcpuLabelOf (49 : Data) = some .readMsr := by decide
theorem zv_label_rvmcs : vcpuLabelOf (74 : Data) = some .readVmcs := by decide
theorem zv_label_flush : vcpuLabelOf (76 : Data) = some .flushTlb := by decide
theorem zv_label_rvmcb : vcpuLabelOf (77 : Data) = some .readVmcb := by decide
theorem zv_label_eio : vcpuLabelOf (79 : Data) = some .enableIoPort := by decide
theorem zv_label_dio : vcpuLabelOf (80 : Data) = some .disableIoPort := by decide

end

theorem zv_rmsr_bv : fl4_abi.label.X86VCPUReadMSR.bv = (49 : Fl4Spec.Data) := by
  unfold fl4_abi.label.X86VCPUReadMSR; rfl
theorem zv_rvmcs_bv : fl4_abi.label.X86VCPUReadVMCS.bv = (74 : Fl4Spec.Data) := by
  unfold fl4_abi.label.X86VCPUReadVMCS; rfl
theorem zv_flush_bv : fl4_abi.label.X86VCPUFlushTLB.bv = (76 : Fl4Spec.Data) := by
  unfold fl4_abi.label.X86VCPUFlushTLB; rfl
theorem zv_rvmcb_bv : fl4_abi.label.X86VCPUReadVMCB.bv = (77 : Fl4Spec.Data) := by
  unfold fl4_abi.label.X86VCPUReadVMCB; rfl
theorem zv_eio_bv : fl4_abi.label.X86VCPUEnableIOPort.bv = (79 : Fl4Spec.Data) := by
  unfold fl4_abi.label.X86VCPUEnableIOPort; rfl
theorem zv_dio_bv : fl4_abi.label.X86VCPUDisableIOPort.bv = (80 : Fl4Spec.Data) := by
  unfold fl4_abi.label.X86VCPUDisableIOPort; rfl

/-! ## The post -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- FL4's argument words agree with a spec argument list (module docstring). -/
def VArgs (st : machine.Store S) (s : S) (ct buf len : U64) (args : List Fl4Spec.Data) : Prop :=
  args.length = len.val ∧ ∀ (i : ℕ) (w : U64), i < len.val →
    msg.syscall_arg st s ct buf (⟨BitVec.ofNat 64 i⟩ : U64) = ok w → args.getD i 0 = w.bv

theorem VArgs.a0 {s : S} {ct buf len : U64} {args : List Fl4Spec.Data} (h : VArgs st s ct buf len args)
    (hl : 0 < len.val) {f : U64} (hf : msg.syscall_arg st s ct buf 0#u64 = ok f) : args.getD 0 0 = f.bv :=
  h.2 0 f hl hf

theorem VArgs.a1 {s : S} {ct buf len : U64} {args : List Fl4Spec.Data} (h : VArgs st s ct buf len args)
    (hl : 1 < len.val) {x : U64} (hx : msg.syscall_arg st s ct buf 1#u64 = ok x) : args.getD 1 0 = x.bv :=
  h.2 1 x hl hx

/-- FL4's word-by-word `set_mr` of a list of words from MR `i` (count `n` so far). -/
def vcpuReplyWsLoop (st : machine.Store S) (ct b : U64) : S → List U64 → U64 → U64 → Result (S × U64)
  | s, [], _, n => ok (s, n)
  | s, w :: ws, i, n => do
    let (n1, s1) ← msg.set_mr st s ct b i w
    let i2 ← i + 1#u64
    vcpuReplyWsLoop st ct b s1 ws i2 n1

/-- FL4's in-decode reply of several words (module docstring, tail (c)). -/
def vcpuReplyWs (st : machine.Store S) (s : S) (ct : U64) (call : Bool) (ws : List U64) : Result S :=
  if call then do
    let b ← msg.lookup_ipc_buffer st s true ct
    let (s2, n) ← vcpuReplyWsLoop st ct b s ws 0#u64 0#u64
    let s3 ← obj.Tcb.set_reg st ct s2 layout.reg.BADGE 0#u64
    let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 n
    let s4 ← msg.set_msg_info st s3 ct mi
    sched.set_thread_state st s4 ct sched.TS_RUNNING
  else sched.set_thread_state st s ct sched.TS_RUNNING

/-- How FL4 ends a successful VCPU invocation (module docstring). -/
def VDecTail (st : machine.Store S) (ct : U64) (call : Bool) (rep : List Fl4Spec.Data) (s' r2 : S) : Prop :=
  (rep = [] ∧ sched.set_thread_state st s' ct sched.TS_RESTART = ok r2) ∨
  (∃ y : U64, rep = [y.bv] ∧ vcpu.reply st s' call y = ok r2) ∨
  (∃ ws : List U64, rep = ws.map (·.bv) ∧ vcpuReplyWs st s' ct call ws = ok r2)

/-- **The VCPU decode's post at `JAtZV3`** (module docstring). -/
def VDecPost (arI : machine.Arch A) (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap)
    (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (σ : Fl4Spec.State Unit)
    (lbl len p : U64) (call : Bool) (buf : U64) (b : Bool) (c : capability.Cap)
    (r : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ ct : U64, sched.cur_thread st s = ok ct ∧
    ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), VArgs st s ct buf len args →
      StcbCaps b c ec →
      (∃ e e', r.1 = .Err e ∧ SysErrRel e e' ∧
        ExceptT.run (Fl4Spec.decodeVcpuInvocation (Z := Unit) lbl.bv args p.bv ec) σ =
          ExceptT.run (Fl4Spec.NonDetE.throwError (σ := Fl4Spec.State Unit) (α := Fl4Spec.VcpuInvocation) e') σ ∧
        r.2.1 = s ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s r.2.2 σ) ∨
      (∃ (inv : Fl4Spec.VcpuInvocation) (rep : List Fl4Spec.Data) (s' : S) (σ' : Fl4Spec.State Unit)
          (Ac' : Set U64) (Lst' : U64 → List U64), r.1 = .Ok () ∧
        ExceptT.run (Fl4Spec.decodeVcpuInvocation (Z := Unit) lbl.bv args p.bv ec) σ =
          ExceptT.run (Fl4Spec.NonDetE.returnOk (σ := Fl4Spec.State Unit) (ε := Fl4Spec.SyscallError) inv) σ ∧
        Fl4Spec.performVcpuInvocationF (Z := Unit) inv σ = ({(rep, σ')}, False) ∧
        JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D s' r.2.2 σ' ∧ VDecTail st ct call rep s' r.2.1)

end

/-! ## The error case and the adapters -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **An error the decoder throws at every agreeing argument list** gives `VDecPost` (module docstring). -/
theorem JAtZV3.vdErr {a1 : A} (J1 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a1 σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {e : error.Exc} {e' : Fl4Spec.SyscallError} (he : SysErrRel e e')
    {lbl len p : U64} {call : Bool} {buf : U64} {b : Bool} {c : capability.Cap}
    (hD : ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), args.length = len.val →
      Fl4Spec.decodeVcpuInvocation (Z := Unit) lbl.bv args p.bv ec = Fl4Spec.NonDetE.throwError e') :
    VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c (.Err e, s, a1) :=
  ⟨ct, hct, fun args ec hA _ => Or.inl ⟨e, e', rfl, he, by rw [hD args ec hA.1], rfl, J1⟩⟩

/-- `setTcbJ` in `VDecPost` form. -/
theorem JAtZV3.vdStcb (hA : P0.ArchTotal arI) (hVA : ZvVirtAgree arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR) {p : U64} (hp : p ∈ V)
    (len : U64) (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize) {sl : obj.Slot} {b : Bool}
    (hsl : Array.index_usize ex 0#usize = ok sl) (hb : obj.Slot.is_null sl = ok b) {c : capability.Cap}
    (hc : b = false → obj.Slot.cap st sl s = ok c) (hct : ∀ t, c = .Thread t → Z.th t = some .tcb) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUSetTCB len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUSetTCB len p call buf b c r ⦄ := by
  refine WP.spec_mono (JAtZV3.setTcbJ hA hVA J hK hp len call buf ex hsl hb hc hct) ?_
  rintro r ⟨ct, hct', HH⟩
  refine ⟨ct, hct', fun args ec _ hE => ?_⟩
  rcases HH args ec hE with ⟨e, e', h1, h2, h3, h4, h5⟩ | ⟨t, s7, σ', Ac', Lst', h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨e, e', h1, h2, by rw [h3], h4, h5⟩
  · exact Or.inr ⟨.setTcb p.bv t.bv, [], s7, σ', Ac', Lst', h1, by rw [h2], h3, h4, Or.inl ⟨rfl, h5⟩⟩

/-- `writeRegsJ` in `VDecPost` form. -/
theorem JAtZV3.vdWregs (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hAT : P0.ArchTotal arI) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {len : U64} (hlen : 15 ≤ len.val) (call : Bool) {buf : U64}
    (hb : BufOut V buf) (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUWriteRegisters len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUWriteRegisters len p call buf b c r ⦄ := by
  refine WP.spec_mono (J.writeRegsJ hK hAT hp hk hlen call hb ex) ?_
  rintro r ⟨ct, vals, hct, hv, h1, hD, s3, σ', h3, h4, h5⟩
  refine ⟨ct, hct, fun args ec hA _ => Or.inr ⟨.writeRegisters p.bv fun i => (vals i).bv, [], s3, σ', Ac, Lst, h1, ?_, h3, h4, Or.inl ⟨rfl, h5⟩⟩⟩
  rw [hD args ec hA.1 (fun i => hA.2 i.val (vals i) (by have := i.isLt; omega) (hv i))]

/-- `writeVmcsJ` in `VDecPost` form. -/
theorem JAtZV3.vdWvmcs (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hSy : ZvSyncKeep arI AR) (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a')
    (hvk : Fl4Spec.virtKind = .vmx) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {len : U64} (hlen : 2 ≤ len.val) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUWriteVMCS len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUWriteVMCS len p call buf b c r ⦄ := by
  refine WP.spec_mono (J.writeVmcsJ hK hSy hVA hCap hvk hp hk hlen call buf ex) ?_
  rintro r ⟨ct, f, x, hct, hf, hx, HH⟩
  refine ⟨ct, hct, fun args ec hA _ => ?_⟩
  rcases HH args ec hA.1 (hA.a0 (by omega) hf) (hA.a1 (by omega) hx) with
    ⟨e, e', h1, h2, h3, h4, h5⟩ | ⟨y, s3, σ', h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨e, e', h1, h2, by rw [h3], h4, h5⟩
  · exact Or.inr ⟨.writeVmcs p.bv f.bv y.bv, [y.bv], s3, σ', Ac, Lst, h1, by rw [h2], h3, h4, Or.inr (Or.inl ⟨y, rfl, h5⟩)⟩

/-- `writeMsrJ` in `VDecPost` form. -/
theorem JAtZV3.vdWmsr (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hK : ARKeep arI AR) (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a')
    {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {len : U64} (hlen : 2 ≤ len.val) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUWriteMSR len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUWriteMSR len p call buf b c r ⦄ := by
  refine WP.spec_mono (J.writeMsrJ hAT hK hVA hCap hp hk hlen call buf ex) ?_
  rintro r ⟨ct, f, x, hct, hf, hx, HH⟩
  refine ⟨ct, hct, fun args ec hA _ => ?_⟩
  rcases HH args ec hA.1 (hA.a0 (by omega) hf) (hA.a1 (by omega) hx) with
    ⟨e, e', h1, h2, h3, h4, h5⟩ | ⟨s3, σ', h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨e, e', h1, h2, by rw [h3], h4, h5⟩
  · exact Or.inr ⟨.writeMsr p.bv f.bv x.bv, [x.bv], s3, σ', Ac, Lst, h1, by rw [h2], h3, h4, Or.inr (Or.inl ⟨x, rfl, h5⟩)⟩

/-- `writeVmcbJ` in `VDecPost` form. -/
theorem JAtZV3.vdWvmcb (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ)
    (hK : ARKeep arI AR) (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a')
    (hvk : Fl4Spec.virtKind = .svm) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {len : U64} (hlen : 2 ≤ len.val) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUWriteVMCB len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUWriteVMCB len p call buf b c r ⦄ := by
  refine WP.spec_mono (J.writeVmcbJ hK hVA hCap hvk hp hk hlen call buf ex) ?_
  rintro r ⟨ct, f, x, hct, hf, hx, HH⟩
  refine ⟨ct, hct, fun args ec hA _ => ?_⟩
  rcases HH args ec hA.1 (hA.a0 (by omega) hf) (hA.a1 (by omega) hx) with
    ⟨e, e', h1, h2, h3, h4, h5⟩ | ⟨y, s3, σ', h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨e, e', h1, h2, h3, h4, h5⟩
  · exact Or.inr ⟨.writeVmcb p.bv f.bv y.bv, [y.bv], s3, σ', Ac, Lst, h1, h2, h3, h4, Or.inr (Or.inl ⟨y, rfl, h5⟩)⟩

end

end

end Fl4Proofs.P3
