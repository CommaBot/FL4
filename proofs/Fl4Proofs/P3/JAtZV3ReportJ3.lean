/-
P3 (line mmuAD, gen 34): **`ReportJ3` proved** (gen 33's statement, P3/JAtZV3Report): FL4's `vcpu::report t badge`
refines the spec's `vmReportF t badge` at every `JAtZV3` state for a `runningVM` thread; hence **`ReportJ3All`**
(gen 33's [J]) is a theorem, and `vcpu.detach` / SetTCB's binding core hold without it.

* The four branches are separate lemmas (P3/JAtZV3RepBr0 helpers `rvTriple`, `v3_full_reply`, `v3_ite_spec`;
  P3/JAtZV3RepBrB `repBrB`, P3/JAtZV3RepBrC `repBrC2`/`repBrC1`, P3/JAtZV3RepBrA `repBrA2`/`repBrA1`), each stating
  its piece of the extracted `vcpu.report` verbatim; `v3_bound` reads the TCB VCPU word.
* **`JAtZV3.reportJ3M`**: the refinement part. FL4's TCB VCPU word is 0 (spec `tcbVcpuOf = none`) or a VCPU `v ∈ V`
  bound back to `t` (`JExtV.bnd`, `VBind`, as P3/JAtZV3Report's `detachF`); `PENDING` / `VALID` by `rdPend` /
  `rdValid`; the buffer by `lookup_buf_full` (`JBufR`, as P3/XTopJointFault). Four branches: no pending exit and not
  full (MR0..2 by `rvTriple` or zeros, `repFin`); a pending exit (`repLoop0`, `repTail` with `repLoop1`); no pending
  exit, full (`repLoop2`, then `repTail` with `repLoop3`, or without VCPU `repFinN`). The spec side is
  P3/JAtZV3RepSpec's `v3_vmReportF_some` / `_none` with P3/JAtZV3RepMrs' `repR` per branch.
* **`JAtZV3.reportJ3`**: `ReportJ3` (with P3/JAtZV3RepFoot's `reportFoot` for the state word and the `JW` words).
* **`v3_reportJ3All`**: `ReportJ3All` from the platform premises.
* **`JAtZV3.detachF2`**, **`JAtZV3.setTcbCoreF2`**: gen 33's `detachF` / `setTcbCoreF` with `ReportJ3All` [J]
  discharged (same posts).

Premises: [P] `ZvVirtAgree arI` (P3/JAtZV3Vmcs, gen 32: `virtualization` answers 2 exactly on SVM) and
`P0.ArchTotal arI` (P0's platform totality, as P3/JExtVSteps' `vcpu_report_w` and gen 32's `writeRegsJ`). No [J].
No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3RepBrB
import Fl4Proofs.P3.JAtZV3RepBrC
import Fl4Proofs.P3.JAtZV3RepBrA
import Fl4Proofs.P3.JAtZV3RepFoot
import Fl4Proofs.P3.JAtZV3Report
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

theorem v3_bound (s : S) (t : U64) : vcpu.bound st s t ⦃ v => v = L.mem s (tVcpuA t) ⦄ := by
  unfold vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_mono (P1.LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  exact ev

set_option maxHeartbeats 8000000 in
/-- **The refinement part of `ReportJ3`** (module docstring). -/
theorem JAtZV3.reportJ3M (hVA : ZvVirtAgree arI) (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64}
    (ht : Z.th t = some .tcb) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hrs : x.tcbState = .runningVM) (badge : U64) :
    vcpu.report st arI s a t badge ⦃ s' => ∃ (σr : Fl4Spec.State Unit) (Lst' : U64 → List U64),
      Fl4Spec.vmReportF (Z := Unit) t.bv badge.bv σ = ({((), σr)}, False) ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a σr ⦄ := by
  have Jz := J.z2.zv
  have B := Jz.base
  have hO := J.vo
  have htT := B.thT t ht
  have hOK := B.bok
  have hBC := bufCover_of_frameCover (T := Z.T) B.bok B.fcov
  obtain ⟨xr', hkr', hwr⟩ := B.buf t htT
  rw [hk] at hkr'; cases hkr'
  have hEP := B.xtop.fin.1.2.ep
  have hbuf : ∀ b : U64, ((b = 0#u64 ↔ Endp.ipcBufOf true x = none) ∧
      ((L.mem s (tIpcBufA t)).bv = x.tcbIpcBuffer → ∀ p', Endp.ipcBufOf true x = some p' → b.bv = p')) →
      JBufR Z.B b (Endp.ipcBufOf true x) := by
    rintro b ⟨hrw0, hrwp⟩
    cases hrb : Endp.ipcBufOf true x with
    | none => exact hrw0.2 hrb
    | some rp =>
      have hrwv : b.bv = rp := hrwp hwr rp hrb
      exact ⟨(fun e => by have := hrw0.1 e; rw [hrb] at this; cases this), hBC t htT x true rp hk hrb b hrwv, hrwv⟩
  have halF : ∀ b : U64, JBufR Z.B b (Endp.ipcBufOf true x) → ∀ ms : List Fl4Spec.Word, ∀ p,
      Endp.ipcBufOf true x = some p → ∀ q ∈ Endp.mrPairs ms,
      (Endp.bufAddr p q.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p q.1) σ := by
    intro b hb ms p hp q hq
    have := (List.of_mem_zip hq).1
    simp at this
    have hb' := hb
    rw [hp] at hb'
    exact ⟨Endp.bufAddr_aligned hEP hb'.2.1 _, buf_frame_of_ok hOK hk hp _ (by omega)⟩
  unfold vcpu.report
  refine WP.spec_bind (v3_bound s t) fun v ev' => ?_
  by_cases hv0 : v = 0#u64
  · have h0 : L.mem s (tVcpuA t) = 0#u64 := ev'.symm.trans hv0
    have hTV : Fl4Spec.tcbVcpuOf σ t.bv = none := zv_tcbVcpuOf_none fun w ws hw hwt => by
      obtain ⟨u, hu, -, h1, -⟩ := J.z2.specBound hO ht hw hwt
      exact Jz.extv.nz u hu (h1.symm.trans h0)
    refine WP.spec_bind (Pₘ := fun p => p = false) (by
      rw [if_neg (by simp [hv0])]; exact (WP.spec_ok _).2 rfl) fun pending hpend => ?_
    subst hpend
    refine WP.spec_bind (lookup_buf_full s σ B.xtop.rel.2.1.1 B.xtop.rel.2.1.2.1 ht hk hOK true) fun b hb0 => ?_
    have hb := hbuf b hb0
    refine WP.spec_bind (v3_full_reply J htT hk) fun full hfull => ?_
    refine v3_ite_spec (fun h => absurd h (by simp)) (fun _ => ?_)
    refine v3_ite_spec (fun hf => ?_) (fun hf => ?_)
    · exact J.repBrC1 hVA htT hk hrs hb (halF b hb) hv0 hTV rfl hf hfull badge
    · exact J.repBrA1 hVA htT hk hrs hb (halF b hb) hv0 hTV rfl (by simpa using hf) hfull badge
  · have hne0 : L.mem s (tVcpuA t) ≠ 0#u64 := fun h => hv0 (ev'.trans h)
    obtain ⟨hvV, hvt⟩ := (Jz.extv.bnd t ht).resolve_left hne0
    rw [← ev'] at hvV hvt
    obtain ⟨vs, hkv, hbv⟩ := J.z2.vb v hvV
    have hvs : Fl4Spec.VcpuState.tcb vs = some t.bv := by
      rcases hbv with ⟨-, h0⟩ | ⟨t', -, h1, h2⟩
      · have e : t = 0#u64 := hvt.symm.trans h0
        subst e
        exact absurd ht (B.detPl Jz.vm).h0
      · have e : t' = t := h2.symm.trans hvt
        rw [h1, e]
    have hTV : Fl4Spec.tcbVcpuOf σ t.bv = some v.bv := zv_tcbVcpuOf_eq hkv hvs fun w ws hw hwt => by
      obtain ⟨u, hu, rfl, h1, -⟩ := J.z2.specBound hO ht hw hwt
      rw [← h1, ← ev']
    have hvt' : v.bv ≠ t.bv := fun e => by rw [e, hk] at hkv; cases hkv
    have hne : (v != 0#u64) = true := by simp [hv0]
    refine WP.spec_bind (Pₘ := fun p => p = vs.exit.pending) (by
      rw [if_pos hne, v3_get_eq, bind_ok, WP.spec_ok]; exact J.rdPend hvV hkv) fun pending hpend => ?_
    refine WP.spec_bind (lookup_buf_full s σ B.xtop.rel.2.1.1 B.xtop.rel.2.1.2.1 ht hk hOK true) fun b hb0 => ?_
    have hb := hbuf b hb0
    refine WP.spec_bind (v3_full_reply J htT hk) fun full hfull => ?_
    refine v3_ite_spec (fun hp => J.repBrB hVA htT hk hrs hb (halF b hb) hv0 hvV hkv hvt' hTV hpend hp hfull badge)
      (fun hp => ?_)
    have hp' : pending = false := by simpa using hp
    refine v3_ite_spec (fun hf => J.repBrC2 hVA htT hk hrs hb (halF b hb) hv0 hvV hkv hvt' hTV hpend hp' hf hfull badge)
      (fun hf => J.repBrA2 hVA htT hk hrs hb (halF b hb) hv0 hvV hkv hvt' hTV hpend hp' (by simpa using hf) hfull badge)

/-- **`ReportJ3` at every `JAtZV3` state, for a `runningVM` thread** (module docstring). -/
theorem JAtZV3.reportJ3 (hA : P0.ArchTotal arI) (hVA : ZvVirtAgree arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : Z.th t = some .tcb)
    (hrun : ∃ x, σ.kheap t.bv = some (.tcb x) ∧ x.tcbState = .runningVM) (badge : U64) :
    ReportJ3 st arI V X AR Z H Cs Ac Lst D s a σ t badge := by
  obtain ⟨x, hk, hrs⟩ := hrun
  unfold ReportJ3
  refine WP.spec_mono (WP.spec_and (J.reportJ3M hVA ht hk hrs badge) (J.reportFoot hA ht badge)) ?_
  rintro s' ⟨⟨σr, Lst', h1, h2⟩, h3, h4⟩
  exact ⟨σr, Ac, Lst', h1, h2, h3, h4⟩

end

/-- **`ReportJ3All` is a theorem** (gen 33's [J], discharged; module docstring). -/
theorem v3_reportJ3All {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
    (hA : P0.ArchTotal arI) (hVA : ZvVirtAgree arI) (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) : ReportJ3All st arI V X AR Z H Cs D :=
  fun _ _ _ _ _ _ J ht hrun => J.reportJ3 hA hVA ht hrun 0#u64

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **`vcpu.detach` at `JAtZV3`, both branches, paired with `vcpuDetachF`** — gen 33's `detachF` without the
`ReportJ3All` [J] (module docstring). -/
theorem JAtZV3.detachF2 (hA : P0.ArchTotal arI) (hVA : ZvVirtAgree arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR) {t : U64}
    (ht : Z.th t = some .tcb) :
    vcpu.detach st arI s a t ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
      Fl4Spec.vcpuDetachF (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ∧ DetMem st V Z.th t s r.1 ⦄ :=
  J.detachF hK (v3_reportJ3All hA hVA V X AR Z H Cs D) ht

/-- **The binding core of `X86VCPUSetTCB` at `JAtZV3`, paired with `associateVcpuTcbF`** — gen 33's `setTcbCoreF`
without the `ReportJ3All` [J] (module docstring). -/
theorem JAtZV3.setTcbCoreF2 (hA : P0.ArchTotal arI) (hVA : ZvVirtAgree arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR) {t v : U64}
    (ht : Z.th t = some .tcb) (hv : v ∈ V) :
    (do
      let (s3, a2) ← smp.remote_tcb_stall st arI s a t
      let (s4, a3) ← vcpu.detach st arI s3 a2 t
      let i1 ← vcpu.get st s4 v vcpu.TCB
      let b1 ← obj.Tcb.is_null i1
      let (s5, a4) ← if b1 then ok (s4, a3) else vcpu.detach st arI s4 a3 i1
      let s6 ← vcpu.set st s5 v vcpu.TCB t
      let i2 ← layout.tcb.VCPU
      let i3 ← lift (core.num.U64.wrapping_add t i2)
      let s7 ← st.write s6 i3 v
      ok (s7, a4)) ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
        Fl4Spec.associateVcpuTcbF (Z := Unit) v.bv t.bv σ = ({((), σ')}, False) ∧
        JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ⦄ :=
  J.setTcbCoreF hK (v3_reportJ3All hA hVA V X AR Z H Cs D) ht hv

end

end

end Fl4Proofs.P3
