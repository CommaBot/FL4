/-
P3 (line mmuAD, gen 30): **`vcpu.detach` and the binding core of `X86VCPUSetTCB` at `JAtZV3`** (P3/JAtZBDetach's
`JAtZV2.detachN` / `JAtZV2.setTcbCore`, proofs copied with the `JAtZV3` steps of P3/JAtZV3).

* **`JAtZV3.detachN`**: the extracted `vcpu.detach t` at `JAtZV3`, paired with `vcpuDetach t`; same scope `hst`
  (t's spec state is not `runningVM`) as at `JAtZV2`; `VOnly` is now the field `J.vo` (no argument). The unbinding
  writes go through `JAtZV3.unbind` (spec VCPU `{ vs with tcb := none }`, the `TCB` word 0), the `SVM_CPU := 0`
  write through `JAtZV3.vcpuWr` (offset 0x5038, read by no field of `VcpuRel`).
* **`JAtZV3.setTcbCore`**: the decode's `Cap.Thread ptr` block at `JAtZV3`, paired with `associateVcpuTcb`; same
  scope `hst` / `hso` as at `JAtZV2` (no `runningVM` thread involved).

The `report` branch is not lifted: gen 29's `ReportJ` [J] is **false as stated** at reachable states (P3/JAtZV3's
handoff notes; FL4's `vcpu::report` sets `FAULT_IP := NEXT_IP` and has a full-state branch, the extended spec's
`vmReport` does neither — Ext/VirtEntry's docstring lists FL4 #80/#81/#85 as not yet modelled), so `hst` / `hso`
stay.

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 16000000 in
/-- **`vcpu.detach` at `JAtZV3`, paired with the spec's `vcpuDetach`** (module docstring). -/
theorem JAtZV3.detachN (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    {t : U64} (ht : Z.th t = some .tcb)
    (hst : ∀ x, σ.kheap t.bv = some (.tcb x) → x.tcbState ≠ .runningVM) :
    vcpu.detach st arI s a t ⦃ r => ∃ σ', Fl4Spec.vcpuDetach (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      DetSpec σ σ' ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D r.1 r.2 σ' ∧ DetMem st V Z.th t s r.1 ⦄ := by
  have Jz := J.z2.zv
  have hO := J.vo
  have B := Jz.base
  have P := B.jwPl Jz.vm
  have Ly := B.jvLay Jz.vm
  have JWt : JW V Z.th (tVcpuA t) := Or.inr (Or.inl ⟨t, ht, rfl⟩)
  have aT : P1.Aligned (tVcpuA t) := P.jw _ JWt
  have hS := B.xtop.fin.1.1.1
  have h8 : L.mem s (P1.stA t) ≠ 8#u64 := B.st8 ht hst
  unfold vcpu.detach vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  have ev' : v = L.mem s (tVcpuA t) := ev
  split
  · rename_i hv0
    have h0 : L.mem s (tVcpuA t) = 0#u64 := by rw [← ev']; exact hv0
    refine (WP.spec_ok _).2 ⟨σ, zv_vcpuDetach_none (zv_tcbVcpuOf_none fun w ws hw hwt => ?_),
      fun p => Or.inl rfl, J, ⟨h0, fun w hw e => absurd (e.symm.trans h0) (Jz.extv.nz w hw),
        fun b _ _ _ => rfl⟩⟩
    obtain ⟨u, hu, -, h1, -⟩ := J.z2.specBound hO ht hw hwt
    exact Jz.extv.nz u hu (h1.symm.trans h0)
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
  refine WP.spec_bind (P1.obj.Tcb.state.spec s t) fun i ei => ?_
  have hne : ¬ (i = sched.TS_RUNNING_VM) := by rw [ei]; simpa [sched.TS_RUNNING_VM] using h8
  simp only [hne, ↓reduceIte, bind_ok, vcpu.set, lift]
  refine WP.spec_bind (P1.LawfulStore.write_spec s _ _) fun s3 e3 => ?_
  subst e3
  step as ⟨o2, ho2⟩
  subst ho2
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s4 e4 => ?_
  subst e4
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s5 e5 => ?_
  subst e5
  refine (WP.spec_ok _).2 ?_
  -- the spec side
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
  obtain ⟨xt, hkt, -⟩ := B.specTcb ht
  have hD := zv_vcpuDetach_bound hk hTV hkt (hst xt hkt)
  -- FL4 side
  have J1 := J.archV hAR1
  have J2 := J1.unbind ht hvV ev'.symm hvt h8 hk { vs with tcb := none } rfl
  have J3 := J2.vcpuWr hvV aS g1 g2 g3
    (by rw [esv]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega) 0#u64
  have nT : (svmA v).val ≠ (tVcpuA t).val := fun e => nJ (by rw [UScalar.eq_of_val_eq e]; exact JWt)
  have nB : (svmA v).val ≠ (vTcbA v).val := by rw [esv, evt]; omega
  have nTB : (tVcpuA t).val ≠ (vTcbA v).val := fun e => P.vb t ht v hvV (UScalar.eq_of_val_eq e)
  refine ⟨_, hD, fun p => ?_, J3, ⟨?_, ?_, ?_⟩⟩
  · by_cases e : p = v.bv
    · subst e; exact Or.inr ⟨vs, hk, by simp [Notif.updK]⟩
    · exact Or.inl (by simp [Notif.updK, Function.update_of_ne e])
  · show L.mem (L.wr (L.wr (L.wr s (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (svmA v) 0#u64) (tVcpuA t) = 0#u64
    rw [L.mem_wr_ne aS aT nT, L.mem_wr_same aT]
  · intro w hw e
    rw [← e, ← ev']
    show L.mem (L.wr (L.wr (L.wr s (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (svmA v) 0#u64) (vTcbA v) = 0#u64
    rw [L.mem_wr_ne aS aB nB, L.mem_wr_ne aT aB nTB, L.mem_wr_same aB]
  · intro b hb h1 h2
    have hW := ((P1.writesIn_wr (st := st) (s := s) (v := 0#u64) aB).trans
      (P1.writesIn_wr (v := 0#u64) aT)).trans (P1.writesIn_wr (v := 0#u64) aS)
    refine hW.mem_eq (P.jw b hb) ?_
    rintro ((e | e) | e)
    · exact h2 v hvV ev'.symm e
    · exact h1 e
    · exact nJ (e ▸ hb)

set_option maxHeartbeats 16000000 in
/-- **The binding core of `X86VCPUSetTCB` at `JAtZV3`, paired with `associateVcpuTcb`** (module docstring). -/
theorem JAtZV3.setTcbCore (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    {t v : U64} (ht : Z.th t = some .tcb) (hv : v ∈ V)
    (hst : ∀ x, σ.kheap t.bv = some (.tcb x) → x.tcbState ≠ .runningVM)
    (hso : ∀ vs o x, σ.kheap v.bv = some (.archObj (.vcpu vs)) → Fl4Spec.VcpuState.tcb vs = some o →
      σ.kheap o = some (.tcb x) → x.tcbState ≠ .runningVM) :
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
      ok (s7, a4)) ⦃ r => ∃ σ', Fl4Spec.associateVcpuTcb (Z := Unit) v.bv t.bv σ = ({((), σ')}, False) ∧
        JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D r.1 r.2 σ' ⦄ := by
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
  refine WP.spec_bind (J.detachN hK ht hst) ?_
  rintro ⟨s4, a3⟩ ⟨σ1, hD1, DS1, J1, DM1⟩
  try simp only [uncurry_apply_pair]
  obtain ⟨vs1, hk1, hb1⟩ := J1.z2.vb v hv
  unfold vcpu.get
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s4 _) fun i1 ei1 => ?_
  have ei1' : i1 = L.mem s4 (vTcbA v) := ei1
  refine WP.spec_bind (P1.obj.Tcb.is_null.spec i1) fun b1 eb1 => ?_
  refine WP.spec_bind (Pₘ := fun r => ∃ σ2, Fl4Spec.associateVcpuTcb (Z := Unit) v.bv t.bv σ =
      Fl4Spec.vcpuUpdate (Z := Unit) v.bv (fun x : Fl4Spec.VcpuState => { x with tcb := some t.bv }) σ2 ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D r.1 r.2 σ2 ∧ L.mem r.1 (tVcpuA t) = 0#u64 ∧
      L.mem r.1 (vTcbA v) = 0#u64) ?_ ?_
  · split
    · rename_i hb
      have hi0 : i1 = 0#u64 := by rw [eb1] at hb; simpa using hb
      have hm0 : L.mem s4 (vTcbA v) = 0#u64 := ei1'.symm.trans hi0
      have htc : Fl4Spec.VcpuState.tcb vs1 = none := by
        rcases hb1 with ⟨h, -⟩ | ⟨o, ho0, -, hm⟩
        · exact h
        · exact absurd (hm.symm.trans hm0) ho0
      refine (WP.spec_ok _).2 ⟨σ1, ?_, J1, DM1.w0, hm0⟩
      unfold Fl4Spec.associateVcpuTcb
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
      -- the old thread is not in `runningVM`
      have hst1 : ∀ x, σ1.kheap i1.bv = some (.tcb x) → x.tcbState ≠ .runningVM := by
        intro x hx
        rcases DS1 v.bv with ev | ⟨vs', h1, h2⟩
        · rw [ev] at hk1
          rcases DS1 i1.bv with eo | ⟨vs'', h3, h4⟩
          · rw [eo] at hx
            exact hso vs1 i1.bv x hk1 htc hx
          · rw [h4] at hx; cases hx
        · rw [h2] at hk1
          cases hk1
          simp at htc
      refine WP.spec_mono (J1.detachN hK hto hst1) ?_
      rintro ⟨s5, a4⟩ ⟨σ2, hD2, -, J2, DM2⟩
      refine ⟨σ2, ?_, J2, ?_, ?_⟩
      · unfold Fl4Spec.associateVcpuTcb
        rw [Notif.nd_bind_one hD1, Notif.nd_bind_one (zv_getVcpu_eq hk1), htc]
        exact Notif.nd_bind_one hD2 _
      · rw [DM2.keep _ JWt (fun e => hne (tVcpuA_inj e)) (fun w hw _ => P.vb t ht w hw)]
        exact DM1.w0
      · exact DM2.b0 v hv hov
  rintro ⟨s5, a4⟩ ⟨σ2, hA2, J2, hw0, hb0⟩
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
  refine (WP.spec_ok _).2 ⟨_, by rw [hA2]; exact zv_vcpuUpdate_eq hk2 _,
    J2.bind ht hv hw0 hb0 hk2 { vs2 with tcb := some t.bv } rfl⟩


end

end

end Fl4Proofs.P3
