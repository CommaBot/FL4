/-
P3 (line mmuAD, gen 36): **X86VCPUWriteVMCB end to end at `JAtZV3`** (SVM) — the extracted `vcpu.decode` at label
`X86VCPUWriteVMCB` (virt gen 16's `VirtVmcbDec.decode_wrvmcb_eq`: `stall`, `cur_thread`, `virtualization`,
`syscall_arg` 0/1, then `wrvmcbTail`: FL4's `old` word, `sanitize_vmcb`, the store at `v + f`, `SVM_CPU := 0` for the
paging words, the `REGS` copy for RAX, `reply`) paired with the extended spec's `decodeVcpuInvocation` (run at `σ`:
`getVcpu`, the spec's `old`, `sanitizeVmcb`; virt gen 18's `VirtWrSys.spec_wrvmcb_run`) and
`performVcpuInvocation (.writeVmcb v f val)` (`vcpuUpdate v (·.set virtKind (.vmcb f) val)`, reply `[val]`). Pattern of
P3/JAtZV3Vmcs's `writeVmcsJ`; the relation-level pieces are the virt line's, copied byte-identically:
`VirtSanSvm.sanitize_vmcb_rel` (FL4's verdict), `VirtVmcbE2E.sanitize_old_eq` (FL4's `old` and the spec's give the
same verdict), `VirtVmcbStore.VcpuRelSvm.store_vmcb` / `keep_word` / `store_rax` (each store's relation).

* `v3_wrAtV`: an aligned FL4 store at `p + o` is a `WrAt` of the relation's word view `vmemW`.
* `JAtZV3.relSvm`, `JAtZV3.relSvmW`: on SVM the spec VCPU relates to FL4's image over `vmemW` / over `memW`.
* **`JAtZV3.svmStep`**: an aligned store at `p + o` (not a link word) with the spec VCPU `vs'` whose relation the store
  gives keeps `JAtZV3` (gen 30's `vcpuStep`). `JAtZV3.vmcbRaxWr` (the VMCB RAX word, spec unchanged), `JAtZV3.vmcbWr`
  (a writable word other than RAX, spec `vs.set virtKind (.vmcb f) val`), `JAtZV3.regsWr` (RAX's `REGS` copy after the
  RAX word, spec `vs.set virtKind (.vmcb rax) val`).
* Spec side: `zv_label_wvmcb`, **`zv_perform_wvmcb2`**, `zv_wvmcb_bv`.
* **`JAtZV3.writeVmcbJ`**: `vcpu.decode … X86VCPUWriteVMCB len p call buf ex` at a `JAtZV3` state, SVM platform,
  `p ∈ V` a spec VCPU, `len ≥ 2`: the post names FL4's `cur_thread` `ct` and the arguments `f`, `x`, and for every spec
  argument list agreeing with them: either the verdict is an error — FL4 returns `Err e`, the spec decoder (run at
  `σ`) throws `e'` with `SysErrRel e e'`, the store is unchanged and `JAtZV3` holds — or a value `y` — the spec decoder
  returns `.writeVmcb p f y`, `performVcpuInvocation` has exactly one outcome `([y], σ')`, `JAtZV3` holds at FL4's
  state just before `reply` and `σ'`, and FL4's final state is `vcpu.reply` of it with `y`.

Named premises (existing, all [P]): `ZvVirtAgree arI` (gen 32), `∀ a, VirtSanEq.CapAgree arI a` (virt gen 11, as
`writeVmcsJ`), `ARKeep arI AR`. Scope: `virtKind = .svm` (WriteVMCB is SVM-only on both sides). No new premise; no
existing statement changed. Not covered: the VMX refusal, lengths < 2, the caller's `handle_invocation` tail.
-/
import Fl4Proofs.P3.JAtZV3Msr
import Fl4Proofs.P3.VirtWrSys
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- An aligned FL4 store at `p + o` is a `WrAt` of `vmemW` (module docstring). -/
theorem v3_wrAtV {p : U64} (hv : VFits p) {o : Fl4Spec.Word} (h1 : o.toNat < 32768) (h2 : o.toNat % 8 = 0) {x : U64}
    (hx : x.bv = p.bv + o) (s : S) (val : U64) :
    VirtMsrStore.WrAt (vmemW (L.mem s)) (vmemW (L.mem (L.wr s x val))) p.bv o val.bv := by
  obtain ⟨w1, w2⟩ := VirtMsrStore.memW_wr (st := st) hv h1 h2 hx s val
  refine ⟨?_, fun off g1 g2 hne => ?_⟩
  · rw [v3_vmemW_al hv h1 h2]; exact w1
  · rw [v3_vmemW_al hv g1 g2, v3_vmemW_al hv g1 g2]; exact w2 off g1 g2 hne

theorem JAtZV3.relSvm (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    (hvk : Fl4Spec.virtKind = .svm) {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) :
    Fl4Spec.VcpuRelSvm (vmemW (L.mem s)) p.bv vs := by
  have R0 := J.vr p hp vs hk
  rw [hvk] at R0
  exact R0

theorem JAtZV3.relSvmW (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    (hvk : Fl4Spec.virtKind = .svm) {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) :
    Fl4Spec.VcpuRelSvm (VirtInitWalk.memW st s) p.bv vs := by
  have hfv := (J.z2.zv.base.jvLay J.z2.zv.vm).vfit p hp
  have hv : VFits p := ⟨hfv.1, hfv.2⟩
  refine VirtReplyKeep.VcpuRelSvm.congrA (fun o ho h2 => ?_) (J.relSvm hp hvk hk)
  have h1 : o.toNat < 32768 := by
    have := BitVec.lt_def.1 ho
    rw [show Fl4Spec.VcpuLay.SIZE.toNat = 32768 from rfl] at this
    exact this
  rw [v3_vmemW_al hv h1 h2]
  rfl

set_option maxHeartbeats 4000000 in
/-- **An aligned VCPU store paired with the spec VCPU it relates to keeps `JAtZV3`** (SVM; module docstring). -/
theorem JAtZV3.svmStep (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    (hvk : Fl4Spec.virtKind = .svm) {o : Fl4Spec.Word} (h1 : o.toNat < 32768) (h2 : o.toNat % 8 = 0)
    (hl : o.toNat ≠ 20480 ∧ o.toNat ≠ 20488 ∧ o.toNat ≠ 20496) {x : U64} (hx : x.bv = p.bv + o) (val : U64)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (vs' : Fl4Spec.VcpuState)
    (ht : Fl4Spec.VcpuState.tcb vs' = Fl4Spec.VcpuState.tcb vs)
    (hR : ∀ mem', VirtMsrStore.WrAt (vmemW (L.mem s)) mem' p.bv o val.bv → Fl4Spec.VcpuRelSvm mem' p.bv vs') :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s x val) a (Notif.updK σ p.bv (.archObj (.vcpu vs'))) := by
  have hfv := (J.z2.zv.base.jvLay J.z2.zv.vm).vfit p hp
  have hv : VFits p := ⟨hfv.1, hfv.2⟩
  have hxv : x.val = p.val + o.toNat := by
    have e : x = ⟨p.bv + o⟩ := by rcases x with ⟨b⟩; exact congrArg (fun b => (⟨b⟩ : U64)) hx
    rw [e, VirtInitWalk.vo_val hv h1]
  have hal : P1.Aligned x := by unfold P1.Aligned; rw [hxv]; have := hv.1; omega
  have hR' : Fl4Spec.VcpuRel Fl4Spec.virtKind (vmemW (L.mem (L.wr s x val))) p.bv vs' := by
    rw [hvk]; exact hR _ (v3_wrAtV hv h1 h2 hx s val)
  exact J.vcpuStep hp hal (by rw [hxv]; omega) (by rw [hxv]; omega)
    ⟨by rw [hxv]; omega, by rw [hxv]; omega, by rw [hxv]; omega⟩ val hk vs' ht hR'

theorem v3_updK_self {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}
    (hk : σ.kheap p = some o) : Notif.updK σ p o = σ := by
  unfold Notif.updK
  rw [show Function.update σ.kheap p (some o) = σ.kheap from by rw [← hk]; exact Function.update_eq_self _ _]

/-- The VMCB RAX word stored: spec unchanged (`keep_word`). -/
theorem JAtZV3.vmcbRaxWr (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    (hvk : Fl4Spec.virtKind = .svm) {x : U64} (hx : x.bv = p.bv + Fl4Spec.Svm.rax) (val : U64)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s x val) a σ := by
  have h := J.svmStep hp hvk (o := Fl4Spec.Svm.rax) (by decide) (by decide) (by decide) hx val hk vs rfl
    (fun _ hw => VirtVmcbStore.VcpuRelSvm.keep_word (J.relSvm hp hvk hk) hw (Or.inl rfl))
  rwa [v3_updK_self hk] at h

/-- A writable VMCB word other than RAX stored, paired with the spec's field update (`store_vmcb`). -/
theorem JAtZV3.vmcbWr (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    (hvk : Fl4Spec.virtKind = .svm) {f : Fl4Spec.Word} (hf : Fl4Spec.Svm.writable f = true) (hr : f ≠ Fl4Spec.Svm.rax)
    {x : U64} (hx : x.bv = p.bv + f) (val : U64)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s x val) a
      (Notif.updK σ p.bv (.archObj (.vcpu (vs.set Fl4Spec.virtKind (.vmcb f) val.bv)))) := by
  obtain ⟨fa, fl⟩ := VirtVmcbStore.svm_writable_nat hf
  rw [hvk]
  exact J.svmStep hp hvk (o := f) (by omega) fa (by omega) hx val hk _ rfl
    (fun _ hw => VirtVmcbStore.VcpuRelSvm.store_vmcb (J.relSvm hp hvk hk) hf hr hw)

/-- RAX's `REGS` copy stored after the RAX word, paired with the spec's RAX update (`store_rax`). -/
theorem JAtZV3.regsWr (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    (hvk : Fl4Spec.virtKind = .svm) {x : U64} (hx : x.bv = p.bv + Fl4Spec.VcpuLay.REGS) (val : U64)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s x val) a
      (Notif.updK σ p.bv (.archObj (.vcpu (vs.set Fl4Spec.virtKind (.vmcb Fl4Spec.Svm.rax) val.bv)))) := by
  rw [hvk]
  exact J.svmStep hp hvk (o := Fl4Spec.VcpuLay.REGS) (by decide) (by decide) (by decide) hx val hk _ rfl
    (fun _ hw => VirtVmcbStore.VcpuRelSvm.store_rax (J.relSvm hp hvk hk) hw)

end

/-! ## The spec side -/

section
open Fl4Spec

theorem zv_label_wvmcb : vcpuLabelOf (78 : Data) = some .writeVmcb := by decide

theorem zv_perform_wvmcb2 {σ : State Unit} {v : ObjRef} {vs : VcpuState}
    (hk : σ.kheap v = some (.archObj (.vcpu vs))) (f val : Word) :
    performVcpuInvocation (Z := Unit) (.writeVmcb v f val) σ =
      ({([val], Notif.updK σ v (.archObj (.vcpu (vs.set virtKind (.vmcb f) val))))}, False) := by
  show ((vcpuUpdate (Z := Unit) v fun s => VcpuState.set virtKind s (VField.vmcb f) val) >>= fun _ =>
    (pure [val] : SMonad Unit (List Data))) σ = _
  rw [Notif.nd_bind_one (zv_vcpuUpdate_eq hk _)]
  rfl

end

/-! ## The invocation -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

theorem zv_wvmcb_bv : fl4_abi.label.X86VCPUWriteVMCB.bv = (78 : Fl4Spec.Data) := by
  unfold fl4_abi.label.X86VCPUWriteVMCB; rfl

set_option maxHeartbeats 16000000 in
/-- **X86VCPUWriteVMCB at `JAtZV3`, paired with the spec's decode and perform** (module docstring). -/
theorem JAtZV3.writeVmcbJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ)
    (hK : ARKeep arI AR) (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a')
    (hvk : Fl4Spec.virtKind = .svm) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {len : U64} (hlen : 2 ≤ len.val) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUWriteVMCB len p call buf ex ⦃ r => ∃ ct f x : U64,
      sched.cur_thread st s = ok ct ∧ msg.syscall_arg st s ct buf 0#u64 = ok f ∧
      msg.syscall_arg st s ct buf 1#u64 = ok x ∧
      ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), args.length = len.val →
        args.getD 0 0 = f.bv → args.getD 1 0 = x.bv →
        (∃ e e', r.1 = .Err e ∧ SysErrRel e e' ∧
          ExceptT.run (Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUWriteVMCB.bv args p.bv ec) σ =
            ExceptT.run (Fl4Spec.NonDetE.throwError (σ := Fl4Spec.State Unit) (α := Fl4Spec.VcpuInvocation) e') σ ∧
          r.2.1 = s ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s r.2.2 σ) ∨
        (∃ (y : U64) (s3 : S) (σ' : Fl4Spec.State Unit), r.1 = .Ok () ∧
          ExceptT.run (Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUWriteVMCB.bv args p.bv ec) σ =
            ExceptT.run (Fl4Spec.NonDetE.returnOk (σ := Fl4Spec.State Unit) (ε := Fl4Spec.SyscallError)
              (.writeVmcb p.bv f.bv y.bv)) σ ∧
          Fl4Spec.performVcpuInvocation (Z := Unit) (.writeVmcb p.bv f.bv y.bv) σ = ({([y.bv], σ')}, False) ∧
          JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s3 r.2.2 σ' ∧ vcpu.reply st s3 call y = ok r.2.1) ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  have hfv := (B.jvLay J.z2.zv.vm).vfit p hp
  have hv : VFits p := ⟨hfv.1, hfv.2⟩
  have hRm := J.relSvmW hp hvk hk
  have g2 : ¬ len < 2#u64 := by scalar_tac
  rw [VirtVmcbDec.decode_wrvmcb_eq (st := st) s a len p call buf ex g2]
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar hvt) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only at e1 hAR1
  subst s1
  have J1 := J.archV hAR1
  dsimp only
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  rw [hct, bind_ok]
  obtain ⟨i, hi, hi2⟩ := hVA a1
  rw [hi, bind_ok]
  have g0 : len > 0#u64 := by scalar_tac
  have g1 : len > 1#u64 := by scalar_tac
  obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
  obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
  rw [if_pos g0, hf, bind_ok, if_pos g1, hx, bind_ok, if_pos (hi2.2 hvk)]
  -- the spec decoder at these arguments
  have hva : Fl4Spec.vcpuAt σ p.bv = some vs := by unfold Fl4Spec.vcpuAt; rw [hk]
  have hD : ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), args.length = len.val →
      args.getD 0 0 = f.bv → args.getD 1 0 = x.bv →
      ExceptT.run (Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUWriteVMCB.bv args p.bv ec) σ =
        ExceptT.run (VirtArgsSpec.wrvmcbK (Z := Unit) p.bv f.bv x.bv vs) σ := by
    intro args ec hl h0 h1
    rw [zv_wvmcb_bv, VirtWrSys.spec_wrvmcb_run hvk zv_label_wvmcb (by omega) hva, h0, h1]
  have hso := VirtVmcbE2E.sanitize_old_eq hRm f x
  unfold VirtVmcbDec.wrvmcbTail
  rw [VirtInitWalk.END_eq, bind_ok, VirtVmcbTail.old_eq, bind_ok]
  obtain ⟨r, hr, hrel⟩ := VirtSanSvm.sanitize_vmcb_rel (hCap a1) f (VirtVmcbTail.oldF st s p f) x
  rw [hr, bind_ok]
  cases r with
  | Err e =>
    rcases hs : Fl4Spec.sanitizeVmcb f.bv (VirtVmcbTail.oldF st s p f).bv x.bv with e' | val'
    · rw [hs] at hrel
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 ⟨ct, f, x, by first | rfl | exact hct, by first | rfl | exact hf,
        by first | rfl | exact hx, fun args ec hl h0 h1 => Or.inl ⟨e, e', rfl, hrel, ?_, rfl, J1⟩⟩
      rw [hD args ec hl h0 h1]
      unfold VirtArgsSpec.wrvmcbK
      rw [← hso, hs]
    · rw [hs] at hrel; exact hrel.elim
  | Ok y =>
    rcases hs : Fl4Spec.sanitizeVmcb f.bv (VirtVmcbTail.oldF st s p f).bv x.bv with e' | val'
    · rw [hs] at hrel; exact hrel.elim
    have hvv : y.bv = val' := by rw [hs] at hrel; exact hrel
    have hwf := VirtVmcbTail.writable_of_ok hs
    obtain ⟨fa, fl⟩ := VirtVmcbStore.svm_writable_nat hwf
    have hspec : ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), args.length = len.val →
        args.getD 0 0 = f.bv → args.getD 1 0 = x.bv →
        ExceptT.run (Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUWriteVMCB.bv args p.bv ec) σ =
          ExceptT.run (Fl4Spec.NonDetE.returnOk (σ := Fl4Spec.State Unit) (ε := Fl4Spec.SyscallError)
            (.writeVmcb p.bv f.bv y.bv)) σ := by
      intro args ec hl h0 h1
      rw [hD args ec hl h0 h1]
      unfold VirtArgsSpec.wrvmcbK
      rw [← hso, hs, hvv]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have hx1 : (core.num.U64.wrapping_add p f).bv = p.bv + f.bv := VirtMsrEq.wadd_bv p f
    have hx3 : (core.num.U64.wrapping_add p vcpu.REGS).bv = p.bv + Fl4Spec.VcpuLay.REGS := by
      rw [VirtMsrEq.wadd_bv, VirtVmcbTail.regs_bv]
    have hraxf : f = 1528#u64 ↔ f.bv = Fl4Spec.Svm.rax := by
      constructor
      · rintro rfl; decide
      · intro e; apply UScalar.eq_of_val_eq
        have := congrArg BitVec.toNat e
        rw [VirtVmcbStore.rax_nat] at this; exact this
    -- the word, then `SVM_CPU := 0` for the paging words, then RAX's `REGS` copy, then the reply
    refine WP.spec_bind (vset_eq s p f y) fun s2 e2 => ?_
    subst e2
    refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun b _ => ?_
    by_cases hra : f.bv = Fl4Spec.Svm.rax
    · have J2 := J1.vmcbRaxWr hp hvk (by rw [hx1, hra]) y hk
      refine WP.spec_bind (Pₘ := fun s3 => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s3 a1 σ) ?_ fun s3 J3 => ?_
      · split
        · exact WP.spec_mono (vset_eq _ p vcpu.SVM_CPU 0#u64) fun s3 e3 => by
            rw [e3]; exact J2.svmWr hp 0#u64
        · exact (WP.spec_ok _).2 J2
      rw [VirtVmcbTail.RAX_eq, bind_ok, if_pos (hraxf.2 hra)]
      refine WP.spec_bind (vset_eq s3 p vcpu.REGS y) fun s4 e4 => ?_
      subst e4
      have J4 := J3.regsWr hp hvk hx3 y hk
      obtain ⟨s5, h5, -⟩ := P1.spec_ex_fd (P0.vcpu.reply.p0 st _ call y (P1.LawfulStore.total (st := st)))
      rw [h5, bind_ok]
      refine (WP.spec_ok _).2 ⟨ct, f, x, by first | rfl | exact hct, by first | rfl | exact hf,
        by first | rfl | exact hx, fun args ec hl h0 h1 => Or.inr ⟨y, _, _, rfl, hspec args ec hl h0 h1, ?_, J4, h5⟩⟩
      rw [← hra]
      exact zv_perform_wvmcb2 hk _ _
    · have J2 := J1.vmcbWr hp hvk hwf hra hx1 y hk
      refine WP.spec_bind (Pₘ := fun s3 => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s3 a1
        (Notif.updK σ p.bv (.archObj (.vcpu (vs.set Fl4Spec.virtKind (.vmcb f.bv) y.bv))))) ?_ fun s3 J3 => ?_
      · split
        · exact WP.spec_mono (vset_eq _ p vcpu.SVM_CPU 0#u64) fun s3 e3 => by
            rw [e3]; exact J2.svmWr hp 0#u64
        · exact (WP.spec_ok _).2 J2
      rw [VirtVmcbTail.RAX_eq, bind_ok, if_neg (fun e => hra (hraxf.1 e))]
      try simp only [bind_ok]
      obtain ⟨s5, h5, -⟩ := P1.spec_ex_fd (P0.vcpu.reply.p0 st s3 call y (P1.LawfulStore.total (st := st)))
      rw [h5, bind_ok]
      exact (WP.spec_ok _).2 ⟨ct, f, x, by first | rfl | exact hct, by first | rfl | exact hf,
        by first | rfl | exact hx, fun args ec hl h0 h1 => Or.inr ⟨y, s3, _, rfl, hspec args ec hl h0 h1,
          zv_perform_wvmcb2 hk _ _, J3, h5⟩⟩

end

end

end Fl4Proofs.P3
