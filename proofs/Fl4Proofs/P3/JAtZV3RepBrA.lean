/-
P3 (line mmuAD, gen 34): **`ReportJ3`'s short branch** (no pending exit, not full: MR0..2 from the entry state (`rvTriple`) or zeros, message info 0, the badge; `JAtZV3.repBrA2` / `repBrA1`).

No named premise beyond [P] `ZvVirtAgree arI` (gen 32). No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3RepBr0
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 4000000 in
/-- **Branch: no pending exit, not full, with a VCPU** (module docstring). -/
theorem JAtZV3.repBrA2 (hVA : ZvVirtAgree arI) (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ)
    {t : U64} (htT : t ∈ Z.T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hrs : x.tcbState = .runningVM) {b : U64} (hb : JBufR Z.B b (Endp.ipcBufOf true x))
    (hal : ∀ ms : List Fl4Spec.Word, ∀ p, Endp.ipcBufOf true x = some p → ∀ q ∈ Endp.mrPairs ms,
      (Endp.bufAddr p q.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p q.1) σ)
    {v : U64} (hv0 : v ≠ 0#u64) (hvV : v ∈ V) {vs : Fl4Spec.VcpuState}
    (hkv : σ.kheap v.bv = some (.archObj (.vcpu vs))) (hvt' : v.bv ≠ t.bv)
    (hTV : Fl4Spec.tcbVcpuOf σ t.bv = some v.bv)
    {pending full : Bool} (hpend : pending = vs.exit.pending) (hp : pending = false) (hf : full = false)
    (hfull : full = Fl4Proofs.P3.repFull x) (badge : U64) :
    (do
      let i ← arI.virtualization a
      let (ip, ctl, intr) ←
        if v = 0#u64
        then ok (0#u64, 0#u64, 0#u64)
        else
          if i = 2#u64
          then
            do
            let i1 ← vcpu.svm.RIP
            let i2 ← vcpu.get st s v i1
            let i3 ← vcpu.get st s v vcpu.svm.INTERCEPT_EXC
            let i4 ← i3 >>> 32#i32
            let i5 ← vcpu.get st s v vcpu.svm.EVENT_INJ
            ok (i2, i4, i5)
          else
            do
            let i1 ← vcpu.read_vmcs st s v vcpu.vmx.GUEST_RIP
            let i2 ←
              vcpu.read_vmcs st s v
                vcpu.vmx.CONTROL_PRIMARY_PROCESSOR_CONTROLS
            let i3 ←
              vcpu.read_vmcs st s v
                vcpu.vmx.CONTROL_ENTRY_INTERRUPTION_INFO
            ok (i1, i2, i3)
      let (_, s1) ← msg.set_mr st s t b 0#u64 ip
      let (_, s2) ← msg.set_mr st s1 t b 1#u64 ctl
      let (_, s3) ← msg.set_mr st s2 t b 2#u64 intr
      let s4 ←
        obj.Tcb.set_reg st t s3 layout.reg.MSG_INFO 0#u64
      let s5 ← obj.Tcb.set_reg st t s4 layout.reg.BADGE badge
      let next_ip ← obj.Tcb.reg st t s5 layout.reg.NEXT_IP
      let s6 ←
        obj.Tcb.set_reg st t s5 layout.reg.FAULT_IP next_ip
      sched.set_thread_state st s6 t sched.TS_RUNNING) ⦃ s' => ∃ (σr : Fl4Spec.State Unit) (Lst' : U64 → List U64),
      Fl4Spec.vmReportF (Z := Unit) t.bv badge.bv σ = ({((), σr)}, False) ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a σr ⦄ := by
  subst hp hf
  have hq : ∀ p, Endp.ipcBufOf true x = some p → Endp.ipcBufOf true x = some p := fun _ h => h
  have J0 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ t.bv x (Endp.ipcBufOf true x) []) := by
    rw [jMrSt_nil hk]; exact J
  obtain ⟨i, hvi, hi⟩ := hVA a
  refine WP.spec_bind (Pₘ := fun i' => i' = i) (by rw [hvi, WP.spec_ok]) fun i' hi' => ?_
  subst hi'
  refine WP.spec_bind (Pₘ := fun r : U64 × U64 × U64 => r.1.bv = vs.entryIp Fl4Spec.virtKind ∧
      r.2.1.bv = vs.entryCtl Fl4Spec.virtKind ∧ r.2.2.bv = vs.entryIntr Fl4Spec.virtKind)
    (v3_ite_spec (fun h => absurd h hv0) (fun _ => J.rvTriple hvV hkv hi)) ?_
  rintro ⟨ip, ctl, intr⟩ ⟨h1, h2, h3⟩
  simp only at h1 h2 h3
  refine WP.spec_bind (setMrJ3 J0 htT hq hb 0#u64 (by simp) (by simp) ip) ?_
  rintro ⟨_, s1⟩ J1
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (setMrJ3 J1 htT hq hb 1#u64 (by simp [mrUpd]) (by simp [mrUpd]) ctl) ?_
  rintro ⟨_, s2⟩ J2
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (setMrJ3 J2 htT hq hb 2#u64 (by simp [mrUpd]) (by simp [mrUpd]) intr) ?_
  rintro ⟨_, s3⟩ J3
  try simp only [uncurry_apply_pair]
  rw [v3_list3, h1, h2, h3] at J3
  refine WP.spec_mono (J3.repFin htT (jMrSt_rcv _ _ _ _ _) hrs 0#u64 badge) fun s' h' => ?_
  obtain ⟨Lst', J'⟩ := h'
  refine ⟨_, Lst', ?_, J'⟩
  rw [v3_vmReportF_some hk hTV hkv badge.bv (hal _), v3_repR_short x vs badge.bv hpend.symm hfull.symm]
  rfl

set_option maxHeartbeats 4000000 in
/-- **Branch: no pending exit, not full, without VCPU** (module docstring). -/
theorem JAtZV3.repBrA1 (hVA : ZvVirtAgree arI) (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ)
    {t : U64} (htT : t ∈ Z.T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hrs : x.tcbState = .runningVM) {b : U64} (hb : JBufR Z.B b (Endp.ipcBufOf true x))
    (hal : ∀ ms : List Fl4Spec.Word, ∀ p, Endp.ipcBufOf true x = some p → ∀ q ∈ Endp.mrPairs ms,
      (Endp.bufAddr p q.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p q.1) σ)
    {v : U64} (hv0 : v = 0#u64) (hTV : Fl4Spec.tcbVcpuOf σ t.bv = none)
    {pending full : Bool} (hp : pending = false) (hf : full = false) (hfull : full = Fl4Proofs.P3.repFull x) (badge : U64) :
    (do
      let i ← arI.virtualization a
      let (ip, ctl, intr) ←
        if v = 0#u64
        then ok (0#u64, 0#u64, 0#u64)
        else
          if i = 2#u64
          then
            do
            let i1 ← vcpu.svm.RIP
            let i2 ← vcpu.get st s v i1
            let i3 ← vcpu.get st s v vcpu.svm.INTERCEPT_EXC
            let i4 ← i3 >>> 32#i32
            let i5 ← vcpu.get st s v vcpu.svm.EVENT_INJ
            ok (i2, i4, i5)
          else
            do
            let i1 ← vcpu.read_vmcs st s v vcpu.vmx.GUEST_RIP
            let i2 ←
              vcpu.read_vmcs st s v
                vcpu.vmx.CONTROL_PRIMARY_PROCESSOR_CONTROLS
            let i3 ←
              vcpu.read_vmcs st s v
                vcpu.vmx.CONTROL_ENTRY_INTERRUPTION_INFO
            ok (i1, i2, i3)
      let (_, s1) ← msg.set_mr st s t b 0#u64 ip
      let (_, s2) ← msg.set_mr st s1 t b 1#u64 ctl
      let (_, s3) ← msg.set_mr st s2 t b 2#u64 intr
      let s4 ←
        obj.Tcb.set_reg st t s3 layout.reg.MSG_INFO 0#u64
      let s5 ← obj.Tcb.set_reg st t s4 layout.reg.BADGE badge
      let next_ip ← obj.Tcb.reg st t s5 layout.reg.NEXT_IP
      let s6 ←
        obj.Tcb.set_reg st t s5 layout.reg.FAULT_IP next_ip
      sched.set_thread_state st s6 t sched.TS_RUNNING) ⦃ s' => ∃ (σr : Fl4Spec.State Unit) (Lst' : U64 → List U64),
      Fl4Spec.vmReportF (Z := Unit) t.bv badge.bv σ = ({((), σr)}, False) ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a σr ⦄ := by
  subst hp hf
  have hq : ∀ p, Endp.ipcBufOf true x = some p → Endp.ipcBufOf true x = some p := fun _ h => h
  have J0 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ t.bv x (Endp.ipcBufOf true x) []) := by
    rw [jMrSt_nil hk]; exact J
  obtain ⟨i, hvi, hi⟩ := hVA a
  refine WP.spec_bind (Pₘ := fun i' => i' = i) (by rw [hvi, WP.spec_ok]) fun i' hi' => ?_
  subst hi'
  refine WP.spec_bind (Pₘ := fun r : U64 × U64 × U64 => r = (0#u64, 0#u64, 0#u64))
    (v3_ite_spec (fun _ => (WP.spec_ok _).2 rfl) (fun h => absurd hv0 h)) ?_
  rintro ⟨ip, ctl, intr⟩ hr
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  refine WP.spec_bind (setMrJ3 J0 htT hq hb 0#u64 (by simp) (by simp) 0#u64) ?_
  rintro ⟨_, s1⟩ J1
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (setMrJ3 J1 htT hq hb 1#u64 (by simp [mrUpd]) (by simp [mrUpd]) 0#u64) ?_
  rintro ⟨_, s2⟩ J2
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (setMrJ3 J2 htT hq hb 2#u64 (by simp [mrUpd]) (by simp [mrUpd]) 0#u64) ?_
  rintro ⟨_, s3⟩ J3
  try simp only [uncurry_apply_pair]
  rw [v3_list3] at J3
  refine WP.spec_mono (J3.repFin htT (jMrSt_rcv _ _ _ _ _) hrs 0#u64 badge) fun s' h' => ?_
  obtain ⟨Lst', J'⟩ := h'
  refine ⟨_, Lst', ?_, J'⟩
  rw [v3_vmReportF_none hk hTV badge.bv (hal _), v3_repR_noneShort x badge.bv hfull.symm]
  rfl


end

end

end Fl4Proofs.P3
