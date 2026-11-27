/-
P3 (line mmuAD, gen 36): **X86VCPUWriteMSR end to end at `JAtZV3`** — the extracted `vcpu.decode` at label
`X86VCPUWriteMSR` (vcpu.rs l. 978-1006; virt gen 15's `VirtMsrDec.decode_wrmsr_eq`: `stall`, `cur_thread`,
`virtualization`, `syscall_arg` 0/1, `fl4WriteMsr`, the store, the read-back, `reply`) paired with the extended spec's
`decodeVcpuInvocation` (Ext/VirtVcpu: `.writeMsr v f x` when `checkMsrWrite f x` passes, its error otherwise) and
`performVcpuInvocation (.writeMsr v f x)` (`vcpuUpdate v (·.set virtKind (.msr f) x)`, reply `[x]`). Pattern of
P3/JAtZV3Vmcs's `writeVmcsJ`; the relation-level pieces are the virt line's (copied byte-identically in gen 35):
`VirtMsrEq.fl4WriteMsr_rel` (FL4's check = `checkMsrWrite`, address `v + msrOff amd f`), `VirtMsrStore.msrStore_vmx` /
`msrStore_svm` (a store at the MSR's place relates the updated spec VCPU), `VirtMsrStore.memW_wr`.

* `v3_vmemW_al`: on a VCPU's aligned words the relation's word view `vmemW` is the plain memory word.
* **`JAtZV3.msrWr`**: FL4's store of `val` at `p + o`, `o = msrOff (virtKind = svm) m`, paired with the spec VCPU
  `vs.set virtKind (.msr m) val`, keeps `JAtZV3` (gen 30's `vcpuStep`; the offset is none of the link words).
  `v3_msr_al`: that address is aligned.
* Spec side: `zv_label_wmsr`, **`zv_decode_wmsr`**, **`zv_perform_wmsr`**, `zv_wmsr_bv`.
* **`JAtZV3.writeMsrJ`**: `vcpu.decode … X86VCPUWriteMSR len p call buf ex` at a `JAtZV3` state, `p ∈ V` a spec VCPU,
  `len ≥ 2`, either backend: the post names FL4's `cur_thread` `ct` and the two argument words `f`, `x`, and for every
  spec argument list agreeing with them: either the check failed — FL4 returns `Err e`, the spec decoder throws `e'`
  with `SysErrRel e e'`, the store is unchanged and `JAtZV3` holds — or it passed — the spec decoder returns
  `.writeMsr p f x`, `performVcpuInvocation` has exactly one outcome `([x], σ')`, `JAtZV3` holds at FL4's state just
  before `reply` and `σ'`, and FL4's final state is `vcpu.reply` of it with `x` (the read-back of the stored word).

Named premises (existing, all [P]): `ZvVirtAgree arI` (gen 32), `∀ a, VirtSanEq.CapAgree arI a` (virt gen 11, as
`writeVmcsJ`), `ARKeep arI AR`, `P0.ArchTotal arI` (platform totality). No new premise; no existing statement changed.
Not covered: lengths < 2 (FL4 reads 0 for a missing argument, the spec refuses), the caller's `handle_invocation` tail.
-/
import Fl4Proofs.P3.JAtZV3Vmcs
import Fl4Proofs.P3.VirtMsrE2E
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- On a VCPU's aligned words `vmemW` is the memory word (module docstring). -/
theorem v3_vmemW_al {p : U64} (hv : VFits p) {off : Fl4Spec.Word} (h1 : off.toNat < 32768) (h2 : off.toNat % 8 = 0)
    (m : U64 → U64) : vmemW m (p.bv + off) = (m ⟨p.bv + off⟩).bv := by
  unfold vmemW
  rw [if_pos]
  show (⟨p.bv + off⟩ : U64).val % 8 = 0
  rw [VirtInitWalk.vo_val hv h1]
  have := hv.1
  omega

/-- The MSR place `p + msrOff amd m` of a VCPU of `V` is aligned. -/
theorem v3_msr_al (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V) {amd : Bool}
    {m o : Fl4Spec.Word} (ho : VirtMsrEq.msrOff amd m = some o) {x : U64} (hx : x.bv = p.bv + o) : P1.Aligned x := by
  have hfv := (J.z2.zv.base.jvLay J.z2.zv.vm).vfit p hp
  have hv : VFits p := ⟨hfv.1, hfv.2⟩
  obtain ⟨-, h1, h2, -, -⟩ := VirtMsrStore.msrOff_cases ho
  have e : x = ⟨p.bv + o⟩ := by rcases x with ⟨b⟩; exact congrArg (fun b => (⟨b⟩ : U64)) hx
  unfold P1.Aligned
  rw [e, VirtInitWalk.vo_val hv h1]
  have := hv.1
  omega

set_option maxHeartbeats 4000000 in
/-- **FL4's store at an MSR's place, paired with the spec's MSR update** (module docstring). -/
theorem JAtZV3.msrWr (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {m o : Fl4Spec.Word} (ho : VirtMsrEq.msrOff (decide (Fl4Spec.virtKind = .svm)) m = some o) {x : U64}
    (hx : x.bv = p.bv + o) (val : U64) {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s x val) a
      (Notif.updK σ p.bv (.archObj (.vcpu (vs.set Fl4Spec.virtKind (.msr m) val.bv)))) := by
  have hfv := (J.z2.zv.base.jvLay J.z2.zv.vm).vfit p hp
  have hv : VFits p := ⟨hfv.1, hfv.2⟩
  obtain ⟨-, h1, h2, h3, h4⟩ := VirtMsrStore.msrOff_cases ho
  have hxv : x.val = p.val + o.toNat := by
    have e : x = ⟨p.bv + o⟩ := by rcases x with ⟨b⟩; exact congrArg (fun b => (⟨b⟩ : U64)) hx
    rw [e, VirtInitWalk.vo_val hv h1]
  have hal : P1.Aligned x := v3_msr_al J hp ho hx
  have hoN : o.toNat ≠ 20480 ∧ o.toNat ≠ 20488 ∧ o.toNat ≠ 20496 := by
    rcases Bool.eq_false_or_eq_true (decide (Fl4Spec.virtKind = .svm)) with hb | hb
    · have := h4 hb; omega
    · have := h3 hb; omega
  obtain ⟨w1, w2⟩ := VirtMsrStore.memW_wr (st := st) hv h1 h2 hx s val
  have hW : VirtMsrStore.WrAt (vmemW (L.mem s)) (vmemW (L.mem (L.wr s x val))) p.bv o val.bv := by
    refine ⟨?_, fun off g1 g2 hne => ?_⟩
    · rw [v3_vmemW_al hv h1 h2]; exact w1
    · rw [v3_vmemW_al hv g1 g2, v3_vmemW_al hv g1 g2]; exact w2 off g1 g2 hne
  have R0 := J.vr p hp vs hk
  have hR : Fl4Spec.VcpuRel Fl4Spec.virtKind (vmemW (L.mem (L.wr s x val))) p.bv
      (vs.set Fl4Spec.virtKind (.msr m) val.bv) := by
    revert R0 ho
    rcases hvk : Fl4Spec.virtKind with _ | _ | _ | _
    · intro _ R0; exact (show False from R0).elim
    · intro ho R0
      have ho' : VirtMsrEq.msrOff false m = some o := ho
      exact VirtMsrStore.msrStore_vmx R0 ho' hW
    · intro ho R0
      have ho' : VirtMsrEq.msrOff true m = some o := ho
      exact VirtMsrStore.msrStore_svm R0 ho' hW
    · intro _ R0; exact (show False from R0).elim
  exact J.vcpuStep hp hal (by rw [hxv]; omega) (by rw [hxv]; omega)
    ⟨by rw [hxv]; omega, by rw [hxv]; omega, by rw [hxv]; omega⟩ val hk _ rfl hR

end

/-! ## The spec side -/

section
open Fl4Spec

theorem zv_label_wmsr : vcpuLabelOf (50 : Data) = some .writeMsr := by decide

theorem zv_decode_wmsr {args : List Data} {v : ObjRef} {ec : List (Cap × CslotPtr)} {f x : Word}
    (hl : 2 ≤ args.length) (h0 : args.getD 0 0 = f) (h1 : args.getD 1 0 = x) :
    decodeVcpuInvocation (Z := Unit) 50 args v ec =
      match checkMsrWrite f x with
      | .error e => NonDetE.throwError e
      | .ok () => NonDetE.returnOk (.writeMsr v f x) := by
  have hn : ¬ args.length < 2 := by omega
  simp only [decodeVcpuInvocation, zv_label_wmsr, h0, h1, hn, decide_false, reduceCtorEq,
    Bool.false_eq_true, ↓reduceIte]
  rfl

theorem zv_perform_wmsr {σ : State Unit} {v : ObjRef} {vs : VcpuState}
    (hk : σ.kheap v = some (.archObj (.vcpu vs))) (f val : Word) :
    performVcpuInvocation (Z := Unit) (.writeMsr v f val) σ =
      ({([val], Notif.updK σ v (.archObj (.vcpu (vs.set virtKind (.msr f) val))))}, False) := by
  show ((vcpuUpdate (Z := Unit) v fun s => VcpuState.set virtKind s (VField.msr f) val) >>= fun _ =>
    (pure [val] : SMonad Unit (List Data))) σ = _
  rw [Notif.nd_bind_one (zv_vcpuUpdate_eq hk _)]
  rfl

end

/-! ## The invocation -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

theorem zv_wmsr_bv : fl4_abi.label.X86VCPUWriteMSR.bv = (50 : Fl4Spec.Data) := by
  unfold fl4_abi.label.X86VCPUWriteMSR; rfl

set_option maxHeartbeats 16000000 in
/-- **X86VCPUWriteMSR at `JAtZV3`, paired with the spec's decode and perform** (module docstring). -/
theorem JAtZV3.writeMsrJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hK : ARKeep arI AR) (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a')
    {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {len : U64} (hlen : 2 ≤ len.val) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUWriteMSR len p call buf ex ⦃ r => ∃ ct f x : U64,
      sched.cur_thread st s = ok ct ∧ msg.syscall_arg st s ct buf 0#u64 = ok f ∧
      msg.syscall_arg st s ct buf 1#u64 = ok x ∧
      ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), args.length = len.val →
        args.getD 0 0 = f.bv → args.getD 1 0 = x.bv →
        (∃ e e', r.1 = .Err e ∧ SysErrRel e e' ∧
          Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUWriteMSR.bv args p.bv ec =
            Fl4Spec.NonDetE.throwError e' ∧
          r.2.1 = s ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s r.2.2 σ) ∨
        (∃ (s3 : S) (σ' : Fl4Spec.State Unit), r.1 = .Ok () ∧
          Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUWriteMSR.bv args p.bv ec =
            Fl4Spec.NonDetE.returnOk (.writeMsr p.bv f.bv x.bv) ∧
          Fl4Spec.performVcpuInvocation (Z := Unit) (.writeMsr p.bv f.bv x.bv) σ = ({([x.bv], σ')}, False) ∧
          JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s3 r.2.2 σ' ∧ vcpu.reply st s3 call x = ok r.2.1) ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  have g2 : ¬ len < 2#u64 := by scalar_tac
  rw [VirtMsrDec.decode_wrmsr_eq (st := st) hAT s a len p call buf ex g2]
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
  rw [if_pos g0, hf, bind_ok, if_pos g1, hx, bind_ok]
  have hamd : decide (i = 2#u64) = decide (Fl4Spec.virtKind = .svm) := by
    by_cases h : i = 2#u64
    · rw [decide_eq_true h, decide_eq_true (hi2.1 h)]
    · rw [decide_eq_false h, decide_eq_false (fun e => h (hi2.2 e))]
  -- the spec decoder at these arguments
  have hD : ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), args.length = len.val →
      args.getD 0 0 = f.bv → args.getD 1 0 = x.bv →
      Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUWriteMSR.bv args p.bv ec =
        match Fl4Spec.checkMsrWrite f.bv x.bv with
        | .error e => Fl4Spec.NonDetE.throwError e
        | .ok () => Fl4Spec.NonDetE.returnOk (.writeMsr p.bv f.bv x.bv) := by
    intro args ec hl h0 h1
    rw [zv_wmsr_bv]
    exact zv_decode_wmsr (by omega) h0 h1
  unfold VirtMsrDec.wrmsrTail
  obtain ⟨r, hr, hrel, haddr⟩ := VirtMsrEq.fl4WriteMsr_rel (hCap a1) p f x (decide (i = 2#u64))
  rw [hr, bind_ok]
  cases r with
  | Ok w =>
    rcases hcm : Fl4Spec.checkMsrWrite f.bv x.bv with e' | u
    · rw [hcm] at hrel; exact hrel.elim
    cases u
    obtain ⟨o, ho, hox⟩ := Option.map_eq_some_iff.1 (haddr w rfl)
    rw [hamd] at ho
    have hwal : P1.Aligned w := v3_msr_al J hp ho hox.symm
    have J2 := J1.msrWr hp ho hox.symm x hk
    dsimp only
    rw [L.write_eq, bind_ok, L.read_eq, bind_ok, L.mem_wr _ _ _ _ hwal hwal, if_pos rfl]
    obtain ⟨s4, h4, -⟩ := P1.spec_ex_fd (P0.vcpu.reply.p0 st (L.wr s w x) call x (P1.LawfulStore.total (st := st)))
    rw [h4, bind_ok]
    refine (WP.spec_ok _).2 ⟨ct, f, x, by first | rfl | exact hct, by first | rfl | exact hf,
      by first | rfl | exact hx, fun args ec hl h0 h1 => Or.inr ⟨L.wr s w x, _, rfl, ?_,
        zv_perform_wmsr hk _ _, J2, h4⟩⟩
    rw [hD args ec hl h0 h1, hcm]
  | Err e =>
    dsimp only
    refine (WP.spec_ok _).2 ⟨ct, f, x, by first | rfl | exact hct, by first | rfl | exact hf,
      by first | rfl | exact hx, fun args ec hl h0 h1 => ?_⟩
    rcases hcm : Fl4Spec.checkMsrWrite f.bv x.bv with e' | u
    · rw [hcm] at hrel
      exact Or.inl ⟨e, e', rfl, hrel, by rw [hD args ec hl h0 h1, hcm], rfl, J1⟩
    · rw [hcm] at hrel; exact hrel.elim

end

end

end Fl4Proofs.P3
