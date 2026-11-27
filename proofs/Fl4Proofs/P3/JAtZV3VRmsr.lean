/-
P3 (line mmuAD, gen 37): **X86VCPUReadMSR end to end at `JAtZV3`** — the extracted `vcpu.decode` at label
`X86VCPUReadMSR` (vcpu.rs l. 978-1006, the read side: `IA32_VMX_MISC` 0x485 answered from `vcpu_capability` on
VMX and 0 on SVM; otherwise `msr_addr`, none → `IllegalOperation`, some place → the word there and `reply`) paired
with the extended spec's `decodeVcpuInvocation` (`.readVmxMisc` / `.readMsr v f` / `illegalOperation` for
`f ∉ vcpuMsrs`) and `performVcpuInvocationF` (`[if svm then 0 else vcpuCapability 0x485]` /
`[vs.get virtKind (.msr f)]`), in `VDecPost` form (`P3/JAtZV3VDec`).

* Spec side: `zv_decode_rmsr_misc`, `zv_decode_rmsr_bad`, `zv_decode_rmsr_ok`, `zv_perform_rmsr`.
* **`JAtZV3.readMsrJ`**: `len ≥ 1`, either backend; FL4's store is unchanged, `JAtZV3` holds with the arch state
  after the stall, the reply word is the spec's (virt gen 13's `VirtMsrEq.msr_addr_eq`, `msrOff_isSome`,
  `msrOff_rel_vmx` / `msrOff_rel_svm`; gen 36's `v3_vmemW_al`), tail (b).
* Used by `P3/JAtZV3VDisp3` to discharge `VcpuNyp2`'s `readMsr` field.

Premises: [P] `ZvVirtAgree arI`, [P] `∀ a, CapAgree arI a`, `ARKeep arI AR`. No new premise; no existing
statement changed.
-/
import Fl4Proofs.P3.JAtZV3VDisp2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Fl4Spec

theorem zv_decode_rmsr_misc {args : List Data} (hl : 1 ≤ args.length) (h0 : args.getD 0 0 = msrVmxMisc)
    (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 49 args v ec = NonDetE.returnOk .readVmxMisc := by
  have hn : ¬ args.length < 1 := by omega
  unfold decodeVcpuInvocation; rw [zv_label_rmsr]; simp only [hn, h0, ↓reduceIte]

theorem zv_decode_rmsr_bad {args : List Data} (hl : 1 ≤ args.length) {f : Word} (h0 : args.getD 0 0 = f)
    (hm : f ≠ msrVmxMisc) (hb : f ∉ vcpuMsrs) (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 49 args v ec = NonDetE.throwError .illegalOperation := by
  have hn : ¬ args.length < 1 := by omega
  unfold decodeVcpuInvocation; rw [zv_label_rmsr]; simp only [hn, h0, hm, hb, ↓reduceIte, not_false_eq_true]

theorem zv_decode_rmsr_ok {args : List Data} (hl : 1 ≤ args.length) {f : Word} (h0 : args.getD 0 0 = f)
    (hm : f ≠ msrVmxMisc) (hb : f ∈ vcpuMsrs) (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 49 args v ec = NonDetE.returnOk (.readMsr v f) := by
  have hn : ¬ args.length < 1 := by omega
  unfold decodeVcpuInvocation; rw [zv_label_rmsr]
  simp only [hn, h0, hm, hb, ↓reduceIte, not_true_eq_false]

theorem zv_perform_rmsr {σ : State Unit} {v : ObjRef} {vs : VcpuState}
    (hk : σ.kheap v = some (.archObj (.vcpu vs))) (m : Word) :
    performVcpuInvocationF (Z := Unit) (.readMsr v m) σ = ({([vs.get virtKind (.msr m)], σ)}, False) := by
  show ((getVcpu (Z := Unit) v) >>= fun st => (pure [st.get virtKind (.msr m)] : SMonad Unit (List Data))) σ = _
  rw [Notif.nd_bind_one (zv_getVcpu_eq hk)]
  rfl

end

section
open Classical Fl4Proofs.P3.Vs
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 16000000 in
/-- **X86VCPUReadMSR at `JAtZV3`, `len ≥ 1`** (module docstring). -/
theorem JAtZV3.readMsrJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a') {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {len : U64} (hlen : 1 ≤ len.val)
    (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUReadMSR len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUReadMSR len p call buf b c r ⦄ := by
  have g0 : len > 0#u64 := by scalar_tac
  have g1 : ¬ len < 1#u64 := by scalar_tac
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
  rw [hi, bind_ok]
  obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
  obtain ⟨x, hx⟩ : ∃ x, (if len > 1#u64 then msg.syscall_arg st s ct buf 1#u64 else ok 0#u64) = ok x := by
    split
    · obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨x, hx⟩
    · exact ⟨_, rfl⟩
  rw [if_pos g0, hf, bind_ok, hx, bind_ok]
  have n73 := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUSetTCB])
  have n81 := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUWriteRegisters])
  have n76 := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUFlushTLB])
  have n74 := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUReadVMCS])
  have n75 := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUWriteVMCS])
  have n77 := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUReadVMCB
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUReadVMCB])
  have n78 := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUWriteVMCB
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUWriteVMCB])
  have n50 := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUWriteMSR
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUWriteMSR])
  simp only [if_neg n73, if_neg n81, if_neg n76, if_neg n74, if_neg n75, if_neg n77, if_neg n78, if_neg n50,
    eq_self_iff_true, ↓reduceIte, bind_ok, if_neg g1]
  have hamd : decide (i = 2#u64) = decide (Fl4Spec.virtKind = .svm) := by
    by_cases h : i = 2#u64
    · rw [decide_eq_true h, decide_eq_true (hi2.1 h)]
    · rw [decide_eq_false h, decide_eq_false (fun e => h (hi2.2 e))]
  by_cases hm : f = 1157#u64
  · have hfm : f.bv = Fl4Spec.msrVmxMisc := by rw [hm]; rfl
    rw [if_pos hm]
    by_cases h2 : i = 2#u64
    · rw [if_pos h2]
      obtain ⟨s4, h4, -⟩ := P1.spec_ex_fd (P0.vcpu.reply.p0 st s call 0#u64 (P1.LawfulStore.total (st := st)))
      rw [h4, bind_ok, WP.spec_ok]
      have hP : Fl4Spec.performVcpuInvocationF (Z := Unit) .readVmxMisc σ = ({([(0#u64 : U64).bv], σ)}, False) := by
        show ({([if Fl4Spec.virtKind = .svm then 0 else Fl4Spec.vcpuCapability Fl4Spec.msrVmxMisc], σ)}, False) = _
        rw [if_pos (hi2.1 h2)]; rfl
      refine ⟨ct, hct, fun args ec hA _ => Or.inr ⟨.readVmxMisc, [(0#u64 : U64).bv], s, σ, Ac, Lst, rfl, ?_, hP, J1,
        Or.inr (Or.inl ⟨0#u64, rfl, h4⟩)⟩⟩
      rw [zv_rmsr_bv, zv_decode_rmsr_misc (by rw [hA.1]; exact hlen) ((hA.a0 (by omega) hf).trans hfm)]
    · rw [if_neg h2, hCap a1 f, bind_ok]
      obtain ⟨s4, h4, -⟩ := P1.spec_ex_fd
        (P0.vcpu.reply.p0 st s call ⟨Fl4Spec.vcpuCapability f.bv⟩ (P1.LawfulStore.total (st := st)))
      rw [h4, bind_ok, WP.spec_ok]
      have hP : Fl4Spec.performVcpuInvocationF (Z := Unit) .readVmxMisc σ =
          ({([(⟨Fl4Spec.vcpuCapability f.bv⟩ : U64).bv], σ)}, False) := by
        show ({([if Fl4Spec.virtKind = .svm then 0 else Fl4Spec.vcpuCapability Fl4Spec.msrVmxMisc], σ)}, False) = _
        rw [if_neg (fun e => h2 (hi2.2 e)), hfm]
      refine ⟨ct, hct, fun args ec hA _ => Or.inr ⟨.readVmxMisc, _, s, σ, Ac, Lst, rfl, ?_, hP, J1,
        Or.inr (Or.inl ⟨_, rfl, h4⟩)⟩⟩
      rw [zv_rmsr_bv, zv_decode_rmsr_misc (by rw [hA.1]; exact hlen) ((hA.a0 (by omega) hf).trans hfm)]
  · have hfm : f.bv ≠ Fl4Spec.msrVmxMisc := fun e => hm (VirtSanEq.u64_ext (by rw [e]; rfl))
    rw [if_neg hm]
    obtain ⟨o, ho, hom⟩ := VirtMsrEq.msr_addr_eq p f (decide (i = 2#u64))
    rw [ho, bind_ok]
    rw [hamd] at hom
    cases o with
    | none =>
      dsimp only
      simp only [error.illegal, bind_ok, WP.spec_ok]
      have hnone : VirtMsrEq.msrOff (decide (Fl4Spec.virtKind = .svm)) f.bv = none := by
        rcases h : VirtMsrEq.msrOff (decide (Fl4Spec.virtKind = .svm)) f.bv with _ | o'
        · rfl
        · rw [h] at hom; simp at hom
      have hb : f.bv ∉ Fl4Spec.vcpuMsrs := fun hin => by
        have := (VirtMsrEq.msrOff_isSome (decide (Fl4Spec.virtKind = .svm)) f.bv).2 hin
        rw [hnone] at this; simp at this
      exact ⟨ct, hct, fun args ec hA _ => Or.inl ⟨_, .illegalOperation, rfl, trivial, by
        rw [zv_rmsr_bv, zv_decode_rmsr_bad (by rw [hA.1]; exact hlen) (hA.a0 (by omega) hf) hfm hb _ ec],
        rfl, J1⟩⟩
    | some y =>
      dsimp only
      simp only [Option.map_some] at hom
      obtain ⟨o', ho', hy⟩ := Option.map_eq_some_iff.1 hom.symm
      have hyb : y.bv = p.bv + o' := hy.symm
      rw [L.read_eq, bind_ok]
      obtain ⟨s4, h4, -⟩ := P1.spec_ex_fd
        (P0.vcpu.reply.p0 st s call (L.mem s y) (P1.LawfulStore.total (st := st)))
      rw [h4, bind_ok, WP.spec_ok]
      have hin : f.bv ∈ Fl4Spec.vcpuMsrs := (VirtMsrEq.msrOff_isSome _ _).1 (by rw [ho']; rfl)
      have hfv := (J.z2.zv.base.jvLay J.z2.zv.vm).vfit p hp
      have hv : VFits p := ⟨hfv.1, hfv.2⟩
      obtain ⟨-, b1, b2, -, -⟩ := VirtMsrStore.msrOff_cases ho'
      have ey : y = ⟨p.bv + o'⟩ := by rcases y with ⟨b⟩; exact congrArg (fun b => (⟨b⟩ : U64)) hyb
      have hval : (L.mem s y).bv = vs.get Fl4Spec.virtKind (.msr f.bv) := by
        have R0 := J.vr p hp vs hk
        rw [ey, ← v3_vmemW_al hv b1 b2 (L.mem s)]
        revert R0 ho'
        rcases hvk : Fl4Spec.virtKind with _ | _ | _ | _
        · intro _ R0; exact (show False from R0).elim
        · intro ho' R0
          have ho2 : VirtMsrEq.msrOff false f.bv = some o' := ho'
          exact (VirtMsrEq.msrOff_rel_vmx R0 ho2).symm
        · intro ho' R0
          have ho2 : VirtMsrEq.msrOff true f.bv = some o' := ho'
          exact (VirtMsrEq.msrOff_rel_svm R0 ho2).symm
        · intro _ R0; exact (show False from R0).elim
      have hP : Fl4Spec.performVcpuInvocationF (Z := Unit) (.readMsr p.bv f.bv) σ =
          ({([(L.mem s y).bv], σ)}, False) := by
        rw [zv_perform_rmsr hk, hval]
      refine ⟨ct, hct, fun args ec hA _ => Or.inr ⟨.readMsr p.bv f.bv, _, s, σ, Ac, Lst, rfl, ?_, hP, J1,
        Or.inr (Or.inl ⟨_, rfl, h4⟩)⟩⟩
      rw [zv_rmsr_bv, zv_decode_rmsr_ok (by rw [hA.1]; exact hlen) (hA.a0 (by omega) hf) hfm hin]

end

end

end Fl4Proofs.P3
