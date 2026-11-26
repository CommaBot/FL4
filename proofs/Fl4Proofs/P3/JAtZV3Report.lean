/-
P3 (line mmuAD, gen 33): **`ReportJ3` — FL4's `vcpu::report` against the spec's `vmReportF` at `JAtZV3`**, and
**`vcpu.detach` / SetTCB's binding core against `vcpuDetachF` / `associateVcpuTcbF` without the `hst` / `hso`
scope** (P3/JAtZV3Detach's `detachN` / `setTcbCore` had both; their `runningVM` branch was out of scope because gen
29's `ReportJ` is false as stated, P3/JAtZV3Detach's docstring and the gen 30 handoff).

## The statement

`ReportJ3 … s a σ t badge` (a `Prop`, P3/JAtZBDetach's `ReportJ` with `JAtZV3` for `JAtZV2` and the virt line's
`vmReportF` (Ext/VirtReport, virt gen 12, FL4 #80/#81/#85) for `vmReport`, any badge): FL4's `vcpu.report t badge`
at `(s, a)` ends at `s'` with: the spec's `vmReportF t badge σ` has exactly one outcome `σr`, `JAtZV3` holds at
`(s', a, σr)` (some `Ac'`, `Lst'`), `t`'s state word is no longer 8 (`TS_RUNNING_VM`), and no `JW` word (slot
words, TCB VCPU words, VCPU `TCB` words) is written.

**Why it is not false at reachable states (gen 30's check redone against `vmReportF`).** Gen 30 found `ReportJ`
false because FL4 writes `FAULT_IP := NEXT_IP` and has full-state / 3-MR branches the old `vmReport` lacked.
`vmReportF` is FL4's `report` branch by branch (compared with the extracted `vcpu.report`, Fl4Core/Funs.lean
l. 7659-8100, and `vcpu.finish_notification` l. 7254): `full` = `MSG_INFO = 30` read first (`vmFullReply`);
neither pending nor full: MR0..2 := RIP / primary controls / entry interruption (VMX) or RIP / `INTERCEPT_EXC >> 32`
/ `EVENTINJ` (SVM), zeros without VCPU, message info 0, the badge; otherwise the 30-MR loop (exit words if `PENDING`
or `VALID`, else 0), then without `VALID` the entry state, GPRs (MR10..24), RFLAGS / interruptibility / CR3 (0 on
VMX) / CR2 (VMX `CR2` word, SVM VMCB CR2 = `canon .svm (.msr msrCr2)`), MR2 masked to 32 bits when full, then
pending: `PENDING := 0` (`VcpuState.reported`), message info 1, badge 0; not pending (full):
`finish_notification` (MR3 := 0x60 on SVM / 1 on VMX, MR4/6/25/26 := 0, MR5 := 0 unless `VALID` and exit MR27 bit
31), message info 0, the badge; every branch `FAULT_IP := NEXT_IP` and `Running` (FL4 writes FaultIP before the
state, the spec after; different TCB fields). Every VCPU word read is related by `VRel` (`VcpuRelCommon`: exit MRs,
`PENDING`, `VALID`, GPRs; `VcpuRelVmx.vmcs` / `cr2`; `VcpuRelSvm.vmcb` — RIP, `INTERCEPT_EXC`, `EVENTINJ`, RFLAGS,
`INT_STATE`, CR3, CR2 are readable, not hidden, not RAX), the backend choice by gen 32's [P] `ZvVirtAgree`, the
buffer by `lookup_buf_full` / `BufCover` as in P3/XTopJointFault, `runnable .runningVM = true` (the ready-queue
facts do not change with `runningVM → running`). No mismatch is left; `ReportJ3` is the statement still to be
proved (gen 33 handoff: plan and the pieces it needs). The post's last two conjuncts hold by P3/JExtVSteps'
`vcpu_report_w` (it writes `RepW` words, `PENDING`, the state word (left at `TS_RUNNING`), `SCHED_ACTION`).

`ReportJ3All … D` [J]: `ReportJ3 … s a σ t 0` at every `JAtZV3` state (any `Ac`, `Lst`) for every typed-heap TCB
`t` whose spec state is `runningVM` — the form `JAtZV3.reportJ3` will have once proved. It is a ∀-premise over
`JAtZV3` states (not over `IRel` states): it carries exactly the refinement argued above, nothing about states the
invariant does not describe.

## Proved here

* **`JAtZV3.detachF`**: the extracted `vcpu.detach t` at `JAtZV3`, **both branches**, paired with `vcpuDetachF t`
  (the spec with `vmReportF`); premise `ReportJ3All` [J] (used only when `t` is `runningVM`; otherwise gen 30's
  `detachN` and the virt line's `VirtReportEq.vcpuDetachF_eq`). Post: one spec outcome, `JAtZV3` (some `Ac'`,
  `Lst'`), `DetMem` (the link words after).
* **`JAtZV3.setTcbCoreF`**: the decode's `Cap.Thread ptr` block of `X86VCPUSetTCB` at `JAtZV3`, paired with
  `associateVcpuTcbF`; premise `ReportJ3All` [J]; **no `hst` / `hso`**: the target and v's old thread may be
  `runningVM`.

Named premises: `ReportJ3All` [J] (above). No [P] / [W] / [S]. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3Detach
import Fl4Proofs.P3.VirtReportEq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- **`ReportJ3`** (module docstring): FL4's `vcpu.report t badge` refines the spec's `vmReportF t badge` at a
`JAtZV3` state. -/
def ReportJ3 {S : Type} (st : machine.Store S) [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
    (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (t badge : U64) : Prop :=
  vcpu.report st arI s a t badge ⦃ s' => ∃ (σr : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
    Fl4Spec.vmReportF (Z := Unit) t.bv badge.bv σ = ({((), σr)}, False) ∧
    JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D s' a σr ∧ L.mem s' (P1.stA t) ≠ 8#u64 ∧
    ∀ b, JW V Z.th b → L.mem s' b = L.mem s b ⦄

/-- **`ReportJ3All`** [J] (module docstring): `ReportJ3 … t 0` at every `JAtZV3` state for every typed-heap TCB
whose spec state is `runningVM`. -/
def ReportJ3All {S : Type} (st : machine.Store S) [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
    (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (D : Set U64) : Prop :=
  ∀ (Ac : Set U64) (Lst : U64 → List U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (t : U64),
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ → Z.th t = some .tcb →
    (∃ x, σ.kheap t.bv = some (.tcb x) ∧ x.tcbState = .runningVM) →
    ReportJ3 st arI V X AR Z H Cs Ac Lst D s a σ t 0#u64

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 16000000 in
/-- **`vcpu.detach` at `JAtZV3`, both branches, paired with `vcpuDetachF`** (module docstring). -/
theorem JAtZV3.detachF (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hR : ReportJ3All st arI V X AR Z H Cs D) {t : U64} (ht : Z.th t = some .tcb) :
    vcpu.detach st arI s a t ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
      Fl4Spec.vcpuDetachF (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ∧ DetMem st V Z.th t s r.1 ⦄ := by
  have Jz := J.z2.zv
  have B := Jz.base
  obtain ⟨xt, hkt, hwst⟩ := B.specTcb ht
  by_cases hrv : xt.tcbState = .runningVM
  swap
  · have hst : ∀ x, σ.kheap t.bv = some (.tcb x) → x.tcbState ≠ .runningVM := by
      intro x hx; rw [hkt] at hx; cases hx; exact hrv
    refine WP.spec_mono (J.detachN hK ht hst) fun r h => ?_
    obtain ⟨σ', hD, -, J', DM⟩ := h
    refine ⟨σ', Ac, Lst, ?_, J', DM⟩
    rw [VirtReportEq.vcpuDetachF_eq hkt hrv]
    exact hD
  have hO := J.vo
  have P := B.jwPl Jz.vm
  have Ly := B.jvLay Jz.vm
  have JWt : JW V Z.th (tVcpuA t) := Or.inr (Or.inl ⟨t, ht, rfl⟩)
  have aT : P1.Aligned (tVcpuA t) := P.jw _ JWt
  have hS := B.xtop.fin.1.1.1
  have h8 : L.mem s (P1.stA t) = 8#u64 := by
    apply UScalar.eq_of_val_eq
    rw [hwst, hrv]
    simp [Notif.tsCode]
  unfold vcpu.detach vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  have ev' : v = L.mem s (tVcpuA t) := ev
  split
  · rename_i hv0
    have h0 : L.mem s (tVcpuA t) = 0#u64 := by rw [← ev']; exact hv0
    have hTV : Fl4Spec.tcbVcpuOf σ t.bv = none := zv_tcbVcpuOf_none fun w ws hw hwt => by
      obtain ⟨u, hu, -, h1, -⟩ := J.z2.specBound hO ht hw hwt
      exact Jz.extv.nz u hu (h1.symm.trans h0)
    refine (WP.spec_ok _).2 ⟨σ, Ac, Lst, ?_, J, ⟨h0, fun w hw e => absurd (e.symm.trans h0) (Jz.extv.nz w hw),
      fun b _ _ _ => rfl⟩⟩
    unfold Fl4Spec.vcpuDetachF Fl4Spec.getTcbVcpu
    rw [Notif.nd_gets_bind, hTV]
    rfl
  rename_i hv0
  have hvne : L.mem s (tVcpuA t) ≠ 0#u64 := by rw [← ev']; exact hv0
  obtain ⟨hvV, hvt⟩ := (Jz.extv.bnd t ht).resolve_left hvne
  rw [← ev'] at hvV hvt
  have hf := Ly.vfit v hvV
  have JWb : JW V Z.th (vTcbA v) := Or.inr (Or.inr ⟨v, hvV, rfl⟩)
  have aB : P1.Aligned (vTcbA v) := P.jw _ JWb
  have esv := lay_svm_val hf.2
  have evt := lay_vTcb_val hf.2
  have aS : P1.Aligned (svmA v) := by unfold P1.Aligned; rw [esv]; omega
  have g1 : v.val ≤ (svmA v).val := by rw [esv]; omega
  have g2 : (svmA v).val < v.val + 32768 := by rw [esv]; omega
  have g3 : (svmA v).val ≠ v.val + 20480 ∧ (svmA v).val ≠ v.val + 20488 ∧ (svmA v).val ≠ v.val + 20496 := by
    rw [esv]; omega
  have nJ : ¬ JW V Z.th (svmA v) := (Ly.nJS_v hvV g1 g2 g3.1).1
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar (Or.inr (by rw [hvt]; exact B.thT t ht))) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  obtain ⟨vs, hk, hb⟩ := J.z2.vb v hvV
  have hvs : Fl4Spec.VcpuState.tcb vs = some t.bv := by
    rcases hb with ⟨-, h0⟩ | ⟨t', -, h1, h2⟩
    · have e : t = 0#u64 := hvt.symm.trans h0
      subst e
      exact absurd ht (B.detPl Jz.vm).h0
    · have e : t' = t := h2.symm.trans hvt
      rw [h1, e]
  have hTV : Fl4Spec.tcbVcpuOf σ t.bv = some v.bv := zv_tcbVcpuOf_eq hk hvs fun w ws hw hwt => by
    obtain ⟨u, hu, rfl, h1, -⟩ := J.z2.specBound hO ht hw hwt
    rw [← h1, ← ev']
  have J1 := J.archV hAR1
  refine WP.spec_bind (P1.obj.Tcb.state.spec s t) fun i ei => ?_
  have hi : i = sched.TS_RUNNING_VM := by rw [ei]; simp [h8, sched.TS_RUNNING_VM]
  rw [if_pos hi]
  refine WP.spec_bind (hR Ac Lst s a1 σ t J1 ht ⟨xt, hkt, hrv⟩) ?_
  rintro s2 ⟨σr, Ac', Lst', hRep, J2, h82, hJW⟩
  have htv2 : L.mem s2 (tVcpuA t) = v := by rw [hJW _ JWt]; exact ev'.symm
  have hvt2 : L.mem s2 (vTcbA v) = t := by rw [hJW _ JWb]; exact hvt
  obtain ⟨vs2, hk2, -⟩ := J2.z2.vb v hvV
  simp only [vcpu.set, lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
  subst e3
  step as ⟨o2, ho2⟩
  subst ho2
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s4 e4 => ?_
  subst e4
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s5 e5 => ?_
  subst e5
  have nT : (svmA v).val ≠ (tVcpuA t).val := fun e => nJ (by rw [UScalar.eq_of_val_eq e]; exact JWt)
  have nB : (svmA v).val ≠ (vTcbA v).val := by rw [esv, evt]; omega
  have nTB : (tVcpuA t).val ≠ (vTcbA v).val := fun e => P.vb t ht v hvV (UScalar.eq_of_val_eq e)
  refine (WP.spec_ok _).2 ⟨_, Ac', Lst', ?_,
    (J2.unbind ht hvV htv2 hvt2 h82 hk2 { vs2 with tcb := none } rfl).vcpuWr hvV aS g1 g2 g3
      (by rw [esv]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega) 0#u64, ⟨?_, ?_, ?_⟩⟩
  · unfold Fl4Spec.vcpuDetachF Fl4Spec.getTcbVcpu
    rw [Notif.nd_gets_bind, hTV]
    dsimp only
    rw [Notif.nd_bind_one (Notif.getThreadState_eq hkt)]
    unfold Fl4Spec.NonDet.when
    rw [if_pos hrv]
    exact (Notif.nd_bind_one hRep _).trans (zv_vcpuUpdate_eq hk2 _)
  · show L.mem (L.wr (L.wr (L.wr s2 (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (svmA v) 0#u64) (tVcpuA t) = 0#u64
    rw [L.mem_wr_ne aS aT nT, L.mem_wr_same aT]
  · intro w hw e
    rw [← e, ← ev']
    show L.mem (L.wr (L.wr (L.wr s2 (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (svmA v) 0#u64) (vTcbA v) = 0#u64
    rw [L.mem_wr_ne aS aB nB, L.mem_wr_ne aT aB nTB, L.mem_wr_same aB]
  · intro b hb h1 h2
    have hW := ((P1.writesIn_wr (st := st) (s := s2) (v := 0#u64) aB).trans
      (P1.writesIn_wr (v := 0#u64) aT)).trans (P1.writesIn_wr (v := 0#u64) aS)
    refine (hW.mem_eq (P.jw b hb) ?_).trans (hJW b hb)
    rintro ((e | e) | e)
    · exact h2 v hvV ev'.symm e
    · exact h1 e
    · exact nJ (e ▸ hb)

set_option maxHeartbeats 16000000 in
/-- **The binding core of `X86VCPUSetTCB` at `JAtZV3`, paired with `associateVcpuTcbF`**, without the `hst` /
`hso` scope (module docstring). -/
theorem JAtZV3.setTcbCoreF (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hR : ReportJ3All st arI V X AR Z H Cs D) {t v : U64} (ht : Z.th t = some .tcb) (hv : v ∈ V) :
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
        JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
  have Jz := J.z2.zv
  have B := Jz.base
  have P := B.jwPl Jz.vm
  have hS := B.xtop.fin.1.1.1
  have hv0 : v ≠ 0#u64 := Jz.extv.nz v hv
  have JWt : JW V Z.th (tVcpuA t) := Or.inr (Or.inl ⟨t, ht, rfl⟩)
  refine WP.spec_bind (Sched.remote_tcb_stall_id (ar := arI) a hS (B.thT t ht)) ?_
  rintro ⟨s3, a2⟩ e
  try simp only [uncurry_apply_pair]
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2⟩ := e
  subst s3
  subst a2
  refine WP.spec_bind (J.detachF hK hR ht) ?_
  rintro ⟨s4, a3⟩ ⟨σ1, Ac1, Lst1, hD1, J1, DM1⟩
  try simp only [uncurry_apply_pair]
  obtain ⟨vs1, hk1, hb1⟩ := J1.z2.vb v hv
  unfold vcpu.get
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s4 _) fun i1 ei1 => ?_
  have ei1' : i1 = L.mem s4 (vTcbA v) := ei1
  refine WP.spec_bind (P1.obj.Tcb.is_null.spec i1) fun b1 eb1 => ?_
  refine WP.spec_bind (Pₘ := fun r => ∃ (σ2 : Fl4Spec.State Unit) (Ac2 : Set U64) (Lst2 : U64 → List U64),
      Fl4Spec.associateVcpuTcbF (Z := Unit) v.bv t.bv σ =
        Fl4Spec.vcpuUpdate (Z := Unit) v.bv (fun x : Fl4Spec.VcpuState => { x with tcb := some t.bv }) σ2 ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac2 Lst2 D r.1 r.2 σ2 ∧ L.mem r.1 (tVcpuA t) = 0#u64 ∧
      L.mem r.1 (vTcbA v) = 0#u64) ?_ ?_
  · split
    · rename_i hb
      have hi0 : i1 = 0#u64 := by rw [eb1] at hb; simpa using hb
      have hm0 : L.mem s4 (vTcbA v) = 0#u64 := ei1'.symm.trans hi0
      have htc : Fl4Spec.VcpuState.tcb vs1 = none := by
        rcases hb1 with ⟨h, -⟩ | ⟨o, ho0, -, hm⟩
        · exact h
        · exact absurd (hm.symm.trans hm0) ho0
      refine (WP.spec_ok _).2 ⟨σ1, Ac1, Lst1, ?_, J1, DM1.w0, hm0⟩
      unfold Fl4Spec.associateVcpuTcbF
      rw [Notif.nd_bind_one hD1, Notif.nd_bind_one (zv_getVcpu_eq hk1), htc]
      try exact Notif.nd_pure_bind' _ _ _
    · rename_i hb
      have hi0 : i1 ≠ 0#u64 := by rw [eb1] at hb; simpa using hb
      obtain ⟨o, ho0, htc, hm⟩ : ∃ o : U64, o ≠ 0#u64 ∧ Fl4Spec.VcpuState.tcb vs1 = some o.bv ∧
          L.mem s4 (vTcbA v) = o := by
        rcases hb1 with ⟨-, h⟩ | h
        · exact absurd (ei1'.trans h) hi0
        · exact h
      have eio : o = i1 := (ei1'.trans hm).symm
      rw [eio] at ho0 htc hm
      obtain ⟨hto, hov⟩ := (J1.z2.zv.extv.back v hv).resolve_left (by rw [hm]; exact ho0)
      rw [hm] at hto hov
      have hne : t ≠ i1 := fun e => hv0 (by rw [← hov, ← e]; exact DM1.w0)
      refine WP.spec_mono (J1.detachF hK hR hto) ?_
      rintro ⟨s5, a4⟩ ⟨σ2, Ac2, Lst2, hD2, J2, DM2⟩
      refine ⟨σ2, Ac2, Lst2, ?_, J2, ?_, ?_⟩
      · unfold Fl4Spec.associateVcpuTcbF
        rw [Notif.nd_bind_one hD1, Notif.nd_bind_one (zv_getVcpu_eq hk1), htc]
        exact Notif.nd_bind_one hD2 _
      · rw [DM2.keep _ JWt (fun e => hne (tVcpuA_inj e)) (fun w hw _ => P.vb t ht w hw)]
        exact DM1.w0
      · exact DM2.b0 v hv hov
  rintro ⟨s5, a4⟩ ⟨σ2, Ac2, Lst2, hA2, J2, hw0, hb0⟩
  try simp only [uncurry_apply_pair]
  obtain ⟨vs2, hk2, -⟩ := J2.z2.vb v hv
  simp only [vcpu.set, lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec s5 _ _) fun s6 e6 => ?_
  subst e6
  step as ⟨o2, ho2⟩
  subst ho2
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s7 e7 => ?_
  subst e7
  refine (WP.spec_ok _).2 ⟨_, Ac2, Lst2, by rw [hA2]; exact zv_vcpuUpdate_eq hk2 _,
    J2.bind ht hv hw0 hb0 hk2 { vs2 with tcb := some t.bv } rfl⟩

end

end

end Fl4Proofs.P3
