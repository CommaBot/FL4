/-
P3x for virtualization (line virt, gen 18, item 1): **WriteMSR / WriteVMCB at the syscall level** — one statement
per invocation from the decode's entry state, chaining FL4's whole decode (`decode_wrmsr_vmx/svm`, P3/VirtMsrE2E;
`decode_wrvmcb_gen`, P3/VirtVmcbE2E), the argument bridge from the entry registers (`wrmsr_args_joint`,
P3/VirtArgsSpec), the joint verdicts (`wrmsr_spec_joint`, `wrvmcb_spec_joint`), the spec's VCPU read (`getVcpu`,
`getVcpu_eq`) and the spec halves of the store (`writeMsr_rel_vmx/svm`, P3/VirtMsrStore; `writeVmcb_rel_svm`,
P3/VirtVmcbStore).

* `stall_keep`: `vcpu.stall` keeps any arch predicate kept by `vcpu_barrier` and `remote_stall` (gen 16's
  `stall_cap` is the `CapAgree` instance).
* **`VirtCodeKeepStall ar`** [P] (new): the stall's two arch operations keep `VirtCodeAgree` (gen 13's [P]); with it
  the backend word `i` the decode reads after the stall is 2 exactly when `virtKind = .svm` (`stall_code`).
* `spec_wrvmcb_run`: at a state where `v` is the VCPU `vs`, the spec's WriteVMCB decode runs as `wrvmcbK … vs`.
* **`wrmsr_sys`**: from a `ReplyPl` state where the VCPU relates (`VRelAt`, either backend) and the entry registers
  are `regs` (the front end's register fact `hregs`, `length.val = len`), FL4's WriteMSR decode returns; after the
  stall `s1` (writes ⊆ `IPI_PENDING`) either the spec's decode on `specMrs regs sbo um len` is
  `returnOk (.writeMsr v f value)`, FL4 answers `Ok` and every spec outcome of `performVcpuInvocation` relates at
  `v` (`VRelAt`) to FL4's final state, or the spec's decode throws `e'`, FL4 answers the related `e` and the state
  is `s1`.
* **`wrvmcb_sys`** (`virtKind = .svm`): the same for WriteVMCB; the spec side is the decode run at `σ`
  (`ExceptT.run … σ`), since the spec's decode reads the VCPU.
* `wrmsr_sysJ`, `wrvmcb_sysJ`: the same with `ReplyPl` from `JKern` + `JVLay` + `JVm` (`JKern.replyPl`).

Named premises: `CapAgree ar a` [P], `CapKeepStall ar` [P], `VirtCodeAgree ar a` [P] (unchanged), and
**`VirtCodeKeepStall ar`** [P] (new). Justification: `Arch::virtualization()` returns the backend chosen at boot
(fl4-arch-x86_64 `vm::backend()`, a write-once global); an ordering barrier or a stall IPI does not change it.
Not false on reachable states (on the existing top's platform `virtualization() = 0` for every arch state).
`P0.ArchTotal ar` (standard totality). New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtArgsSpec
import Fl4Proofs.P3.VirtReportEq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtWrSys
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtSanSvm
open Fl4Proofs.P3.VirtVcpuRel Fl4Proofs.P3.VirtMsrEq Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit
open Fl4Proofs.P3.VirtMsrStore Fl4Proofs.P3.VirtVmcbStore Fl4Proofs.P3.VirtReplyKeep Fl4Proofs.P3.VirtVmcbDec
open Fl4Proofs.P3.VirtVmcbTail Fl4Proofs.P3.VirtMsrE2E Fl4Proofs.P3.VirtVmcbE2E Fl4Proofs.P3.VirtArgsSpec

noncomputable section

/-! ## The stall keeps the backend code -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

theorem remote_tcb_stall_keep {Q : A → Prop} (h1 : ∀ a, Q a → ar.vcpu_barrier a ⦃ a' => Q a' ⦄)
    (h2 : ∀ a c, Q a → ar.remote_stall a c ⦃ a' => Q a' ⦄) (s : S) {a : A} (h : Q a) (t : obj.Tcb) :
    smp.remote_tcb_stall st ar s a t ⦃ r => Q r.2 ⦄ := by
  unfold smp.remote_tcb_stall
  refine WP.spec_bind (P1.obj.Tcb.affinity.spec s t) fun cpu _ => ?_
  rw [L.cur_cpu_eq, bind_ok]
  split
  · refine WP.spec_bind (P1.obj.node_get.spec s _ _) fun i1 _ => ?_
    split
    · refine WP.spec_bind (h2 a cpu h) fun a1 h1 => ?_
      exact WP.spec_mono (resched_arch s a1 cpu) fun r e => e ▸ h1
    · exact (WP.spec_ok _).2 h
  · exact (WP.spec_ok _).2 h

/-- **The stall keeps an arch predicate kept by its two arch operations**. -/
theorem stall_keep {Q : A → Prop} (h1 : ∀ a, Q a → ar.vcpu_barrier a ⦃ a' => Q a' ⦄)
    (h2 : ∀ a c, Q a → ar.remote_stall a c ⦃ a' => Q a' ⦄) {a : A} (h : Q a) (s : S) (v : U64) :
    vcpu.stall st ar s a v ⦃ r => Q r.2 ⦄ := by
  unfold vcpu.stall
  refine WP.spec_bind (h1 a h) fun a1 ha1 => ?_
  unfold vcpu.get
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun t _ => ?_
  refine WP.spec_bind (P1.obj.Tcb.is_null.spec t) fun b _ => ?_
  split
  · exact (WP.spec_ok _).2 ha1
  · exact remote_tcb_stall_keep h1 h2 s ha1 _

end

section
variable {A : Type} (ar : machine.Arch A)

/-- **`VirtCodeKeepStall` [P]** (module docstring): the stall's arch operations keep `VirtCodeAgree`. -/
def VirtCodeKeepStall : Prop :=
  (∀ a, VirtCodeAgree ar a → ar.vcpu_barrier a ⦃ a' => VirtCodeAgree ar a' ⦄) ∧
    (∀ a c, VirtCodeAgree ar a → ar.remote_stall a c ⦃ a' => VirtCodeAgree ar a' ⦄)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

/-- After the stall the backend word is 2 exactly on SVM (premises `VirtCodeAgree` [P], `VirtCodeKeepStall` [P]). -/
theorem stall_code (hKv : VirtCodeKeepStall ar) {a : A} (hk : VirtCodeAgree ar a) {s s1 : S} {v : U64} {a1 : A}
    (hp : vcpu.stall st ar s a v = ok (s1, a1)) {i : U64} (hi : ar.virtualization a1 = ok i) :
    (i = 2#u64 ↔ virtKind = .svm) := by
  have h := stall_keep (st := st) hKv.1 hKv.2 hk s v
  rw [hp] at h
  obtain ⟨c, hc, hiff⟩ := (WP.spec_ok _).1 h
  rw [hi] at hc
  rw [Fl4Proofs.P1.ok_inj_ff hc]; exact hiff

end

/-! ## The spec's WriteVMCB decode run at a VCPU state -/

section
variable {Z : Type} [StateExt Z]

theorem spec_wrvmcb_run (hk : virtKind = .svm) {label : Data} {args : List Data} {v : ObjRef}
    {caps : List (Cap × CslotPtr)} (hl : vcpuLabelOf label = some .writeVmcb) (hlen : 2 ≤ args.length)
    {σ : State Z} {vs : VcpuState} (hv : vcpuAt σ v = some vs) :
    ExceptT.run (decodeVcpuInvocation (Z := Z) label args v caps) σ =
      ExceptT.run (wrvmcbK (Z := Z) v (args.getD 0 0) (args.getD 1 0) vs) σ := by
  rw [spec_decode_wrvmcb hk hl hlen]
  exact Endp.runE_liftE_bind (VirtReportEq.getVcpu_eq hv)

end

/-! ## The syscall-level statements -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {Z : Type} [StateExt Z]

set_option maxHeartbeats 1000000 in
/-- **WriteMSR at the syscall level** (module docstring; premises `CapAgree`, `CapKeepStall`, `VirtCodeAgree`,
`VirtCodeKeepStall`, all [P]; state facts `ReplyPl`, `VRelAt`, the entry registers). -/
theorem wrmsr_sys (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) (hKv : VirtCodeKeepStall ar) {a : A}
    (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S} {v : U64} (P : ReplyPl st v s) {σ : State Z}
    (hR : VRelAt (memW st s) σ v.bv) (length : U64) (call : Bool) (buf : U64)
    (ex : Aeneas.Std.Array obj.Slot 3#usize) (hlen : ¬ length < 2#u64) {regs : Register → Word}
    (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hL : length.val = len) {label : Data}
    (hl : vcpuLabelOf label = some .writeMsr) (caps : List (Cap × CslotPtr)) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteMSR length v call buf ex ⦃ r =>
      ∃ (s1 : S) (a1 : A) (f value : U64), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ((decodeVcpuInvocation (Z := Z) label (Endp.specMrs regs sbo um len) v.bv caps =
              NonDetE.returnOk (.writeMsr v.bv f.bv value.bv) ∧ r.1 = .Ok () ∧
            ∀ x ∈ (performVcpuInvocation (Z := Z) (.writeMsr v.bv f.bv value.bv) σ).1,
              VRelAt (memW st r.2.1) x.2 v.bv) ∨
          (∃ e e', decodeVcpuInvocation (Z := Z) label (Endp.specMrs regs sbo um len) v.bv caps =
              NonDetE.throwError e' ∧ SysErrRel e e' ∧ r.1 = .Err e ∧ r.2.1 = s1)) ⦄ := by
  have hl2 : 2 ≤ len := by
    have : ¬ length.val < 2 := fun h => hlen (by scalar_tac)
    omega
  obtain ⟨vs, hvs, hS, hV⟩ := hR
  by_cases hsvm : virtKind = .svm
  · refine WP.spec_mono (decode_wrmsr_svm hA hK hc P length call buf ex hlen (hS hsvm)) ?_
    rintro r ⟨s1, a1, i, f, value, hp, hW, hi, hf, hv, hT⟩
    have hi2 : decide (i = 2#u64) = true := decide_eq_true ((stall_code hKv hk hp hi).2 hsvm)
    obtain ⟨hlA, h0, h1⟩ := wrmsr_args_joint (sbo := sbo) (um := um) P hW hregs hl2 hlen hf hv
    refine ⟨s1, a1, f, value, hp, hW, ?_⟩
    rcases wrmsr_spec_joint (Z := Z) (vo := v.bv) (caps := caps) (hT hi2) hl hlA h0 h1 with ⟨hd, hr, hR'⟩ | hE
    · exact Or.inl ⟨hd, hr, fun x hx => writeMsr_rel_svm hsvm hvs hR' hx⟩
    · exact Or.inr hE
  · refine WP.spec_mono (decode_wrmsr_vmx hA hK hc P length call buf ex hlen (hV hsvm)) ?_
    rintro r ⟨s1, a1, i, f, value, hp, hW, hi, hf, hv, hT⟩
    have hi2 : decide (i = 2#u64) = false := decide_eq_false fun e => hsvm ((stall_code hKv hk hp hi).1 e)
    obtain ⟨hlA, h0, h1⟩ := wrmsr_args_joint (sbo := sbo) (um := um) P hW hregs hl2 hlen hf hv
    refine ⟨s1, a1, f, value, hp, hW, ?_⟩
    rcases wrmsr_spec_joint (Z := Z) (vo := v.bv) (caps := caps) (hT hi2) hl hlA h0 h1 with ⟨hd, hr, hR'⟩ | hE
    · exact Or.inl ⟨hd, hr, fun x hx => writeMsr_rel_vmx hsvm hvs hR' hx⟩
    · exact Or.inr hE

set_option maxHeartbeats 1000000 in
/-- **WriteVMCB at the syscall level, SVM** (module docstring; premises as `wrmsr_sys`). -/
theorem wrvmcb_sys (hsvm : virtKind = .svm) (hA : P0.ArchTotal ar) (hK : CapKeepStall ar)
    (hKv : VirtCodeKeepStall ar) {a : A} (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S} {v : U64}
    (P : ReplyPl st v s) {σ : State Z} (hR : VRelAt (memW st s) σ v.bv) (length : U64) (call : Bool) (buf : U64)
    (ex : Aeneas.Std.Array obj.Slot 3#usize) (hlen : ¬ length < 2#u64) {regs : Register → Word}
    (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hL : length.val = len) {label : Data}
    (hl : vcpuLabelOf label = some .writeVmcb) (caps : List (Cap × CslotPtr)) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteVMCB length v call buf ex ⦃ r =>
      ∃ (s1 : S) (a1 : A) (f value : U64), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ((∃ val, ExceptT.run (decodeVcpuInvocation (Z := Z) label (Endp.specMrs regs sbo um len) v.bv caps) σ =
              ExceptT.run (NonDetE.returnOk (.writeVmcb v.bv f.bv val) : SEMonad Z VcpuInvocation) σ ∧
            r.1 = .Ok () ∧
            ∀ x ∈ (performVcpuInvocation (Z := Z) (.writeVmcb v.bv f.bv val) σ).1,
              VRelAt (memW st r.2.1) x.2 v.bv) ∨
          (∃ e e', ExceptT.run (decodeVcpuInvocation (Z := Z) label (Endp.specMrs regs sbo um len) v.bv caps) σ =
              ExceptT.run (NonDetE.throwError e' : SEMonad Z VcpuInvocation) σ ∧ SysErrRel e e' ∧
            r.1 = .Err e ∧ r.2.1 = s1)) ⦄ := by
  have hl2 : 2 ≤ len := by
    have : ¬ length.val < 2 := fun h => hlen (by scalar_tac)
    omega
  obtain ⟨vs, hvs, hS, -⟩ := hR
  refine WP.spec_mono (decode_wrvmcb_gen hA hK hc P length call buf ex hlen (hS hsvm)) ?_
  rintro r ⟨s1, a1, i, f, value, hp, hW, hi, hf, hv, hT, -⟩
  have hi2 : i = 2#u64 := (stall_code hKv hk hp hi).2 hsvm
  obtain ⟨hlA, h0, h1⟩ := wrmsr_args_joint (sbo := sbo) (um := um) P hW hregs hl2 hlen hf hv
  refine ⟨s1, a1, f, value, hp, hW, ?_⟩
  rw [spec_wrvmcb_run hsvm hl hlA hvs]
  rcases wrvmcb_spec_joint (Z := Z) (hT hi2) v.bv h0 h1 with ⟨val, hd, hr, hR'⟩ | ⟨e, e', hd, hE⟩
  · exact Or.inl ⟨val, by rw [hd], hr, fun x hx => writeVmcb_rel_svm hsvm hvs hR' hx⟩
  · exact Or.inr ⟨e, e', by rw [hd], hE⟩

end

/-! ## With `ReplyPl` from the kernel-global facts -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {AI : Type} {arI : machine.Arch AI}
variable {H : P1.Heap} {Cs D : Set U64} {th : TypedHeap} {σ : Fl4Spec.State Unit} {V U : Set U64}

/-- **WriteMSR at the syscall level from `JKern` + `JVLay` + `JVm`** (premises as `wrmsr_sys`). -/
theorem wrmsr_sysJ (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) (hKv : VirtCodeKeepStall ar) {a : A}
    (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S}
    (K : JKern (L := L) arI H Cs D th s σ) (Ly : JVLay V th U) (Jv : JVm (L := L) V H s σ) {v : U64} (hvV : v ∈ V)
    (hR : VRelAt (memW st s) σ v.bv) (length : U64) (call : Bool) (buf : U64)
    (ex : Aeneas.Std.Array obj.Slot 3#usize) (hlen : ¬ length < 2#u64) {regs : Register → Word}
    (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hL : length.val = len) {label : Data}
    (hl : vcpuLabelOf label = some .writeMsr) (caps : List (Cap × CslotPtr)) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteMSR length v call buf ex ⦃ r =>
      ∃ (s1 : S) (a1 : A) (f value : U64), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ((decodeVcpuInvocation (Z := Unit) label (Endp.specMrs regs sbo um len) v.bv caps =
              NonDetE.returnOk (.writeMsr v.bv f.bv value.bv) ∧ r.1 = .Ok () ∧
            ∀ x ∈ (performVcpuInvocation (Z := Unit) (.writeMsr v.bv f.bv value.bv) σ).1,
              VRelAt (memW st r.2.1) x.2 v.bv) ∨
          (∃ e e', decodeVcpuInvocation (Z := Unit) label (Endp.specMrs regs sbo um len) v.bv caps =
              NonDetE.throwError e' ∧ SysErrRel e e' ∧ r.1 = .Err e ∧ r.2.1 = s1)) ⦄ :=
  wrmsr_sys hA hK hKv hc hk (JKern.replyPl K Ly Jv hvV) hR length call buf ex hlen hregs hL hl caps

/-- **WriteVMCB at the syscall level from `JKern` + `JVLay` + `JVm`, SVM** (premises as `wrmsr_sys`). -/
theorem wrvmcb_sysJ (hsvm : virtKind = .svm) (hA : P0.ArchTotal ar) (hK : CapKeepStall ar)
    (hKv : VirtCodeKeepStall ar) {a : A} (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S}
    (K : JKern (L := L) arI H Cs D th s σ) (Ly : JVLay V th U) (Jv : JVm (L := L) V H s σ) {v : U64} (hvV : v ∈ V)
    (hR : VRelAt (memW st s) σ v.bv) (length : U64) (call : Bool) (buf : U64)
    (ex : Aeneas.Std.Array obj.Slot 3#usize) (hlen : ¬ length < 2#u64) {regs : Register → Word}
    (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hL : length.val = len) {label : Data}
    (hl : vcpuLabelOf label = some .writeVmcb) (caps : List (Cap × CslotPtr)) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteVMCB length v call buf ex ⦃ r =>
      ∃ (s1 : S) (a1 : A) (f value : U64), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ((∃ val, ExceptT.run (decodeVcpuInvocation (Z := Unit) label (Endp.specMrs regs sbo um len) v.bv caps) σ =
              ExceptT.run (NonDetE.returnOk (.writeVmcb v.bv f.bv val) : SEMonad Unit VcpuInvocation) σ ∧
            r.1 = .Ok () ∧
            ∀ x ∈ (performVcpuInvocation (Z := Unit) (.writeVmcb v.bv f.bv val) σ).1,
              VRelAt (memW st r.2.1) x.2 v.bv) ∨
          (∃ e e', ExceptT.run (decodeVcpuInvocation (Z := Unit) label (Endp.specMrs regs sbo um len) v.bv caps) σ =
              ExceptT.run (NonDetE.throwError e' : SEMonad Unit VcpuInvocation) σ ∧ SysErrRel e e' ∧
            r.1 = .Err e ∧ r.2.1 = s1)) ⦄ :=
  wrvmcb_sys hsvm hA hK hKv hc hk (JKern.replyPl K Ly Jv hvV) hR length call buf ex hlen hregs hL hl caps

end

end
end Fl4Proofs.P3.VirtWrSys
