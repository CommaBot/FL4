/-
P3 (line mmuAD, gen 34): **the VCPU values `vcpu::report` reads, backend by backend** (step 2 of gen 33's plan,
continued), and the `VALID = 0` block writing MR7/8/9/29 (`JAtZV3.repCr`).

Each `rv*` lemma takes FL4's code for one value — `if i = 2 then <SVM VMCB word> else <VMX VMCS field>` with `i`
from `Arch::virtualization` (`i = 2 ↔ virtKind = .svm`, gen 32's [P] `ZvVirtAgree`) — and gives the spec value:
`entryIp` / `entryCtl` / `entryIntr` (Ext/VirtState) and the RFLAGS / interruptibility / CR3 / CR2 words of
`vmenterFullMrs` (Ext/VirtReport), via P3/JAtZV3VRead's `rdVmcb` / `rdVmcs` / `rdCr2*`.

* `v3_kind`: a related VCPU exists only on VMX or SVM.
* `JAtZV3.rdSvmW`: a VMCB word at a literal FL4 offset.
* `JAtZV3.rvIp`, `rvCtl`, `rvIntr`, `rvFlags`, `rvInt`, `rvCr3`, `rvCr2`.
* `crF`, **`JAtZV3.repCr`**: the block `virtualization; flags; int; cr3; cr2; set_mr 7, 8, 9, 29` at a 30-word
  message.

Premise used: [P] `ZvVirtAgree arI` (gen 32). No new named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3RepFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Fl4Spec

theorem v3_kind {k : VirtKind} {mem : Word → Word} {v : Word} {vs : VcpuState} (h : VcpuRel k mem v vs) :
    k = .vmx ∨ k = .svm := by
  cases k with
  | vmx => exact Or.inl rfl
  | svm => exact Or.inr rfl
  | none => exact h.elim
  | armEl2 => exact h.elim

theorem v3_shr32 (x : U64) : x >>> (32#i32) = ok ⟨x.bv >>> 32⟩ := by
  rw [VirtSanEq.shr_i32 x _ (by decide) (by decide)]; rfl

/-- The MR7/8/9/29 words of the `VALID = 0` block (`vmenterFullMrs`'s RFLAGS, interruptibility, CR3, CR2). -/
def crF (vs : VcpuState) (F : Nat → Word) : Nat → Word := fun i =>
  if i = 29 then vs.get virtKind (.msr msrCr2)
  else if i = 9 then (if virtKind = .svm then vs.get virtKind (.vmcb Svm.cr3) else 0)
  else if i = 8 then (if virtKind = .svm then vs.get virtKind (.vmcb Svm.intState)
    else vs.get virtKind (.vmcs Vmx.guestInterruptability))
  else if i = 7 then (if virtKind = .svm then vs.get virtKind (.vmcb Svm.rflags)
    else vs.get virtKind (.vmcs Vmx.guestRflags))
  else F i

theorem v3_rip_ok : Svm.readable Svm.rip = true ∧ Svm.hiddenRead Svm.rip = false ∧ Svm.rip ≠ Svm.rax ∧
    Svm.rip.toNat = 1400 := by decide
theorem v3_iexc_ok : Svm.readable Svm.interceptExc = true ∧ Svm.hiddenRead Svm.interceptExc = false ∧
    Svm.interceptExc ≠ Svm.rax ∧ Svm.interceptExc.toNat = 8 := by decide
theorem v3_einj_ok : Svm.readable Svm.eventInj = true ∧ Svm.hiddenRead Svm.eventInj = false ∧
    Svm.eventInj ≠ Svm.rax ∧ Svm.eventInj.toNat = 168 := by decide
theorem v3_rfl_ok : Svm.readable Svm.rflags = true ∧ Svm.hiddenRead Svm.rflags = false ∧
    Svm.rflags ≠ Svm.rax ∧ Svm.rflags.toNat = 1392 := by decide
theorem v3_ist_ok : Svm.readable Svm.intState = true ∧ Svm.hiddenRead Svm.intState = false ∧
    Svm.intState ≠ Svm.rax ∧ Svm.intState.toNat = 104 := by decide
theorem v3_cr3_ok : Svm.readable Svm.cr3 = true ∧ Svm.hiddenRead Svm.cr3 = false ∧
    Svm.cr3 ≠ Svm.rax ∧ Svm.cr3.toNat = 1360 := by decide

theorem v3_vmx_rd : Vmx.readable Vmx.guestRip = true ∧ Vmx.readable Vmx.controlPrimaryProcessorControls = true ∧
    Vmx.readable Vmx.controlEntryInterruptionInfo = true ∧ Vmx.readable Vmx.guestRflags = true ∧
    Vmx.readable Vmx.guestInterruptability = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Vmx.readable, Vmx.vmxReadFields]

theorem v3_vmx_ids : (vcpu.vmx.GUEST_RIP).bv = Vmx.guestRip ∧
    (vcpu.vmx.CONTROL_PRIMARY_PROCESSOR_CONTROLS).bv = Vmx.controlPrimaryProcessorControls ∧
    (vcpu.vmx.CONTROL_ENTRY_INTERRUPTION_INFO).bv = Vmx.controlEntryInterruptionInfo ∧
    (vcpu.vmx.GUEST_RFLAGS).bv = Vmx.guestRflags ∧ (vcpu.vmx.GUEST_INTERRUPTABILITY).bv = Vmx.guestInterruptability := by
  unfold vcpu.vmx.GUEST_RIP vcpu.vmx.CONTROL_PRIMARY_PROCESSOR_CONTROLS vcpu.vmx.CONTROL_ENTRY_INTERRUPTION_INFO
    vcpu.vmx.GUEST_RFLAGS vcpu.vmx.GUEST_INTERRUPTABILITY
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

theorem JAtZV3.rdSvmW (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (hvk : Fl4Spec.virtKind = .svm)
    (o : U64) (w : Fl4Spec.Word) (he : o.val = w.toNat)
    (hw : Fl4Spec.Svm.readable w = true ∧ Fl4Spec.Svm.hiddenRead w = false ∧ w ≠ Fl4Spec.Svm.rax ∧ w.toNat < 20480) :
    (L.mem s (core.num.U64.wrapping_add p o)).bv = vs.get Fl4Spec.virtKind (.vmcb w) := by
  have e : o = ⟨w⟩ := UScalar.eq_of_val_eq he
  subst e
  exact J.rdVmcb hp hk hvk ⟨w⟩ hw.1 hw.2.1 hw.2.2.1 hw.2.2.2

theorem JAtZV3.kindV (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) :
    Fl4Spec.virtKind = .vmx ∨ Fl4Spec.virtKind = .svm := v3_kind (J.vr p hp vs hk)

theorem v3_read_vmcs_eq (s : S) (p f : U64) :
    vcpu.read_vmcs st s p f = ok (L.mem s ⟨p.bv + Fl4Spec.vmcsOff f.bv⟩) := by
  unfold vcpu.read_vmcs; rw [v3_vmcs_addr, bind_ok, L.read_eq]

variable {p : U64} {vs : Fl4Spec.VcpuState} {i : U64}

theorem JAtZV3.rvIp (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hp : p ∈ V)
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (hi : i = 2#u64 ↔ Fl4Spec.virtKind = .svm) :
    (if i = 2#u64 then do
        let i2 ← vcpu.svm.RIP
        vcpu.get st s p i2
      else vcpu.read_vmcs st s p vcpu.vmx.GUEST_RIP) ⦃ r => r.bv = vs.entryIp Fl4Spec.virtKind ⦄ := by
  unfold Fl4Spec.VcpuState.entryIp
  by_cases hs : Fl4Spec.virtKind = .svm
  · rw [if_pos (hi.2 hs), if_pos hs]
    have hR : vcpu.svm.RIP = ok 1400#u64 := by unfold vcpu.svm.RIP vcpu.svm.SAVE; rfl
    rw [hR, bind_ok, v3_get_eq, WP.spec_ok]
    obtain ⟨h1, h2, h3, h4⟩ := v3_rip_ok
    exact J.rdSvmW hp hk hs 1400#u64 _ (by rw [h4]; rfl) ⟨h1, h2, h3, by omega⟩
  · rw [if_neg (fun h => hs (hi.1 h)), if_neg hs, v3_read_vmcs_eq, WP.spec_ok]
    have hvk := (J.kindV hp hk).resolve_right hs
    exact (J.rdVmcs hp hk hvk vcpu.vmx.GUEST_RIP (by rw [v3_vmx_ids.1]; exact v3_vmx_rd.1)).trans (by rw [v3_vmx_ids.1])

theorem JAtZV3.rvCtl (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hp : p ∈ V)
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (hi : i = 2#u64 ↔ Fl4Spec.virtKind = .svm) :
    (if i = 2#u64 then do
        let i2 ← vcpu.get st s p vcpu.svm.INTERCEPT_EXC
        i2 >>> 32#i32
      else vcpu.read_vmcs st s p vcpu.vmx.CONTROL_PRIMARY_PROCESSOR_CONTROLS) ⦃ r =>
        r.bv = vs.entryCtl Fl4Spec.virtKind ⦄ := by
  unfold Fl4Spec.VcpuState.entryCtl
  by_cases hs : Fl4Spec.virtKind = .svm
  · rw [if_pos (hi.2 hs), if_pos hs, v3_get_eq, bind_ok, v3_shr32, WP.spec_ok]
    obtain ⟨h1, h2, h3, h4⟩ := v3_iexc_ok
    show (L.mem s (core.num.U64.wrapping_add p vcpu.svm.INTERCEPT_EXC)).bv >>> 32 = _
    rw [J.rdSvmW hp hk hs vcpu.svm.INTERCEPT_EXC _ (by rw [h4]; unfold vcpu.svm.INTERCEPT_EXC; rfl)
      ⟨h1, h2, h3, by omega⟩]
  · rw [if_neg (fun h => hs (hi.1 h)), if_neg hs, v3_read_vmcs_eq, WP.spec_ok]
    have hvk := (J.kindV hp hk).resolve_right hs
    exact (J.rdVmcs hp hk hvk vcpu.vmx.CONTROL_PRIMARY_PROCESSOR_CONTROLS (by rw [v3_vmx_ids.2.1]; exact v3_vmx_rd.2.1)).trans (by rw [v3_vmx_ids.2.1])

theorem JAtZV3.rvIntr (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hp : p ∈ V)
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (hi : i = 2#u64 ↔ Fl4Spec.virtKind = .svm) :
    (if i = 2#u64 then vcpu.get st s p vcpu.svm.EVENT_INJ
      else vcpu.read_vmcs st s p vcpu.vmx.CONTROL_ENTRY_INTERRUPTION_INFO) ⦃ r =>
        r.bv = vs.entryIntr Fl4Spec.virtKind ⦄ := by
  unfold Fl4Spec.VcpuState.entryIntr
  by_cases hs : Fl4Spec.virtKind = .svm
  · rw [if_pos (hi.2 hs), if_pos hs, v3_get_eq, WP.spec_ok]
    obtain ⟨h1, h2, h3, h4⟩ := v3_einj_ok
    exact J.rdSvmW hp hk hs vcpu.svm.EVENT_INJ _ (by rw [h4]; unfold vcpu.svm.EVENT_INJ; rfl) ⟨h1, h2, h3, by omega⟩
  · rw [if_neg (fun h => hs (hi.1 h)), if_neg hs, v3_read_vmcs_eq, WP.spec_ok]
    have hvk := (J.kindV hp hk).resolve_right hs
    exact (J.rdVmcs hp hk hvk vcpu.vmx.CONTROL_ENTRY_INTERRUPTION_INFO (by rw [v3_vmx_ids.2.2.1]; exact v3_vmx_rd.2.2.1)).trans (by rw [v3_vmx_ids.2.2.1])

theorem JAtZV3.rvFlags (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hp : p ∈ V)
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (hi : i = 2#u64 ↔ Fl4Spec.virtKind = .svm) :
    (if i = 2#u64 then do
        let i4 ← vcpu.svm.RFLAGS
        vcpu.get st s p i4
      else vcpu.read_vmcs st s p vcpu.vmx.GUEST_RFLAGS) ⦃ r =>
        r.bv = (if Fl4Spec.virtKind = .svm then vs.get Fl4Spec.virtKind (.vmcb Fl4Spec.Svm.rflags)
          else vs.get Fl4Spec.virtKind (.vmcs Fl4Spec.Vmx.guestRflags)) ⦄ := by
  by_cases hs : Fl4Spec.virtKind = .svm
  · rw [if_pos (hi.2 hs), if_pos hs]
    have hR : vcpu.svm.RFLAGS = ok 1392#u64 := by unfold vcpu.svm.RFLAGS vcpu.svm.SAVE; rfl
    rw [hR, bind_ok, v3_get_eq, WP.spec_ok]
    obtain ⟨h1, h2, h3, h4⟩ := v3_rfl_ok
    exact J.rdSvmW hp hk hs 1392#u64 _ (by rw [h4]; rfl) ⟨h1, h2, h3, by omega⟩
  · rw [if_neg (fun h => hs (hi.1 h)), if_neg hs, v3_read_vmcs_eq, WP.spec_ok]
    have hvk := (J.kindV hp hk).resolve_right hs
    exact (J.rdVmcs hp hk hvk vcpu.vmx.GUEST_RFLAGS (by rw [v3_vmx_ids.2.2.2.1]; exact v3_vmx_rd.2.2.2.1)).trans (by rw [v3_vmx_ids.2.2.2.1])

theorem JAtZV3.rvInt (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hp : p ∈ V)
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (hi : i = 2#u64 ↔ Fl4Spec.virtKind = .svm) :
    (if i = 2#u64 then vcpu.get st s p vcpu.svm.INT_STATE
      else vcpu.read_vmcs st s p vcpu.vmx.GUEST_INTERRUPTABILITY) ⦃ r =>
        r.bv = (if Fl4Spec.virtKind = .svm then vs.get Fl4Spec.virtKind (.vmcb Fl4Spec.Svm.intState)
          else vs.get Fl4Spec.virtKind (.vmcs Fl4Spec.Vmx.guestInterruptability)) ⦄ := by
  by_cases hs : Fl4Spec.virtKind = .svm
  · rw [if_pos (hi.2 hs), if_pos hs, v3_get_eq, WP.spec_ok]
    obtain ⟨h1, h2, h3, h4⟩ := v3_ist_ok
    exact J.rdSvmW hp hk hs vcpu.svm.INT_STATE _ (by rw [h4]; unfold vcpu.svm.INT_STATE; rfl) ⟨h1, h2, h3, by omega⟩
  · rw [if_neg (fun h => hs (hi.1 h)), if_neg hs, v3_read_vmcs_eq, WP.spec_ok]
    have hvk := (J.kindV hp hk).resolve_right hs
    exact (J.rdVmcs hp hk hvk vcpu.vmx.GUEST_INTERRUPTABILITY (by rw [v3_vmx_ids.2.2.2.2]; exact v3_vmx_rd.2.2.2.2)).trans (by rw [v3_vmx_ids.2.2.2.2])

theorem JAtZV3.rvCr3 (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hp : p ∈ V)
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (hi : i = 2#u64 ↔ Fl4Spec.virtKind = .svm) :
    (if i = 2#u64 then do
        let i4 ← vcpu.svm.CR3
        vcpu.get st s p i4
      else ok 0#u64) ⦃ r =>
        r.bv = (if Fl4Spec.virtKind = .svm then vs.get Fl4Spec.virtKind (.vmcb Fl4Spec.Svm.cr3) else 0) ⦄ := by
  by_cases hs : Fl4Spec.virtKind = .svm
  · rw [if_pos (hi.2 hs), if_pos hs]
    have hR : vcpu.svm.CR3 = ok 1360#u64 := by unfold vcpu.svm.CR3 vcpu.svm.SAVE; rfl
    rw [hR, bind_ok, v3_get_eq, WP.spec_ok]
    obtain ⟨h1, h2, h3, h4⟩ := v3_cr3_ok
    exact J.rdSvmW hp hk hs 1360#u64 _ (by rw [h4]; rfl) ⟨h1, h2, h3, by omega⟩
  · rw [if_neg (fun h => hs (hi.1 h)), if_neg hs, WP.spec_ok]
    rfl

theorem JAtZV3.rvCr2 (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hp : p ∈ V)
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (hi : i = 2#u64 ↔ Fl4Spec.virtKind = .svm) :
    (if i = 2#u64 then do
        let i4 ← vcpu.svm.CR2
        vcpu.get st s p i4
      else vcpu.get st s p vcpu.CR2) ⦃ r => r.bv = vs.get Fl4Spec.virtKind (.msr Fl4Spec.msrCr2) ⦄ := by
  by_cases hs : Fl4Spec.virtKind = .svm
  · rw [if_pos (hi.2 hs)]
    have hR : vcpu.svm.CR2 = ok 1600#u64 := by unfold vcpu.svm.CR2 vcpu.svm.SAVE; rfl
    rw [hR, bind_ok, v3_get_eq, WP.spec_ok]
    exact J.rdCr2Svm hp hk hs
  · rw [if_neg (fun h => hs (hi.1 h)), v3_get_eq, WP.spec_ok]
    exact J.rdCr2Vmx hp hk ((J.kindV hp hk).resolve_right hs)

variable {σ0 : Fl4Spec.State Unit} {x0 : Fl4Spec.Tcb} {pb : Option Fl4Spec.ObjRef}

set_option maxHeartbeats 16000000 in
/-- **The `VALID = 0` block: MR7/8/9/29** (module docstring). -/
theorem JAtZV3.repCr (hVA : ZvVirtAgree arI) {t b : U64} {F : Nat → Fl4Spec.Word} {s5 : S}
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s5 a (jMrSt σ0 t.bv x0 pb ((List.range 30).map F)))
    (hr : t ∈ Z.T) (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p) (hb : JBufR Z.B b pb)
    {v : U64} (hv : v ∈ V) (hkv : σ0.kheap v.bv = some (.archObj (.vcpu vs))) (hvt : v.bv ≠ t.bv) :
    (do
      let i3 ← arI.virtualization a
      let flags ←
        if i3 = 2#u64
        then
          do
          let i4 ← vcpu.svm.RFLAGS
          vcpu.get st s5 v i4
        else vcpu.read_vmcs st s5 v vcpu.vmx.GUEST_RFLAGS
      let int ←
        if i3 = 2#u64
        then vcpu.get st s5 v vcpu.svm.INT_STATE
        else
          vcpu.read_vmcs st s5 v
            vcpu.vmx.GUEST_INTERRUPTABILITY
      let cr3 ←
        if i3 = 2#u64
        then do
             let i4 ← vcpu.svm.CR3
             vcpu.get st s5 v i4
        else ok 0#u64
      let cr2 ←
        if i3 = 2#u64
        then do
             let i4 ← vcpu.svm.CR2
             vcpu.get st s5 v i4
        else vcpu.get st s5 v vcpu.CR2
      let (_, s7) ← msg.set_mr st s5 t b 7#u64 flags
      let (_, s8) ← msg.set_mr st s7 t b 8#u64 int
      let (_, s9) ← msg.set_mr st s8 t b 9#u64 cr3
      let (_, s10) ← msg.set_mr st s9 t b 29#u64 cr2
      ok s10) ⦃ s' => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s' a
        (jMrSt σ0 t.bv x0 pb ((List.range 30).map (crF vs F))) ⦄ := by
  obtain ⟨i, hvi, hi⟩ := hVA a
  have hk := v3_kv (ms := (List.range 30).map F) (x0 := x0) (pb := pb) hkv hvt
  rw [hvi, bind_ok]
  refine WP.spec_bind (J.rvFlags hv hk hi) fun fl hfl => ?_
  refine WP.spec_bind (J.rvInt hv hk hi) fun it hit => ?_
  refine WP.spec_bind (J.rvCr3 hv hk hi) fun c3 hc3 => ?_
  refine WP.spec_bind (J.rvCr2 hv hk hi) fun c2 hc2 => ?_
  refine WP.spec_bind (setMrJ3F J hr hq hb 7#u64 7 (by simp) (by omega) fl) ?_
  rintro ⟨_, s7⟩ J7
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (setMrJ3F J7 hr hq hb 8#u64 8 (by simp) (by omega) it) ?_
  rintro ⟨_, s8⟩ J8
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (setMrJ3F J8 hr hq hb 9#u64 9 (by simp) (by omega) c3) ?_
  rintro ⟨_, s9⟩ J9
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (setMrJ3F J9 hr hq hb 29#u64 29 (by simp) (by omega) c2) ?_
  rintro ⟨_, s10⟩ J10
  try simp only [uncurry_apply_pair]
  rw [WP.spec_ok]
  rw [v3_map_congr 30 (G := crF vs F) (fun k _ => by
    unfold crF
    rw [hfl, hit, hc3, hc2]
    all_goals (by_cases e29 : k = 29 <;> by_cases e9 : k = 9 <;> by_cases e8 : k = 8 <;> by_cases e7 : k = 7 <;>
      simp_all))] at J10
  exact J10

end

end

end Fl4Proofs.P3
