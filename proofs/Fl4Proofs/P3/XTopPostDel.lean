/-
P3 (DESIGN.md §9), CSpace: **`post_cap_deletion` at `XTop`**
(`XPostDelHyp` discharged, `xPostDelHyp_of`): the cleanup of an IRQ handler
cap (FL4's IRQ state word, IRQ masked; the spec's `deleted_irq_handler`) and
of an IO port cap (FL4's bitmap bits cleared; the spec's
`free_ioport_range`), each a kernel-state step (`XTopAt.ksStep`, as
StepSem's `Steps.irqWr` and IoControl's `Steps.mask`).

The cleanup caps are well formed (`CapWf`): an IRQ handler's number is below
128 (FL4's IRQ count), an IO port cap's range is ordered.
-/
import Fl4Proofs.P3.XTopTcbData
import Fl4Proofs.P3.IoControl
import Fl4Proofs.P3.IoPost
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The IRQ handler cleanup at `XTop`.** -/
theorem post_irqX {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) {Z : XSets} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) (hK : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hL : IntLayout Z.th (L.ksb s)) (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (irq : U64) (hirq : irq.val < 128) :
    objects.post_cap_deletion st arI s a (.IrqHandler irq) ⦃ r =>
      SlotsSame Z.th (L.mem s) (L.mem r.1) ∧ L.ksb r.1 = L.ksb s ∧ ∃ σ',
        ((), σ') ∈ (Fl4Spec.postCapDeletion (Z := Unit) (absCap (.IrqHandler irq)) σ).1 ∧
        CRel Z.th (L.mem r.1) σ' Z.G ∧ XTopAt (L := L) AR Z r.1 r.2 σ' ⦄ := by
  unfold objects.post_cap_deletion interrupt.deleted_irq_handler
  simp only
  obtain ⟨a1, hm⟩ := hmask a irq (decide (interrupt.IRQ_INACTIVE = interrupt.IRQ_INACTIVE))
  rw [set_irq_state_eq arI s a _ irq hm, WP.spec_ok]
  have hv := irqStA_val hL.fit hirq
  have ha8 : (L.ksb s).val % 8 = 0 := by have := hL.align; omega
  set s' := L.wr s (irqStA (L.ksb s) irq) interrupt.IRQ_INACTIVE
  set σ' := setIrqSt .irqInactive (BitVec.ofNat 8 irq.val) σ
  have hw : P1.WritesIn st s s' (KsW (L.ksb s)) := by
    refine (P1.writesIn_wr (by unfold P1.Aligned; rw [hv]; omega)).mono fun b e => ?_
    subst e
    have hK : (⟨BitVec.ofNat 64 (224 + 8 * irq.val)⟩ : U64).val = 224 + 8 * irq.val := by
      show (BitVec.ofNat 64 _).toNat = _; simp; omega
    exact ⟨⟨BitVec.ofNat 64 (224 + 8 * irq.val)⟩, by rw [hK]; omega, by rw [hK]; omega, by rw [hK]; omega,
      by rw [hK, hv]; omega, by rw [hK]; omega⟩
  have hsti : irqSt interrupt.IRQ_INACTIVE = .irqInactive := by unfold interrupt.IRQ_INACTIVE; rfl
  have hX' : XTopAt (L := L) AR Z s' a1 σ' :=
    XTopAt.ksStep hX hK hw (by constructor <;> rfl)
      (IrqRel.wr hL hX.fin.1.1.2.2.2.1 hirq _ _ (by rw [hsti]; rfl) rfl)
      (IoRel.irqWr hL hX.fin.1.1.2.2.2.2.1 hirq _ _ rfl)
      (hX.rel.2.2.2.1.frame (fun o ho => (DK4.irqSt hL.fit ha8 hirq interrupt.IRQ_INACTIVE).2 o ho) rfl rfl)
      (hAM _ _ _ hX.fin.1.1.2.2.2.2.2.2 (Or.inr (Or.inl ⟨irq, _, hm⟩)))
  refine ⟨hX.slotsSame_of hw (fun b hb => ?_), hw.1, σ', ?_, hX'.rel.2.1, hX'⟩
  · obtain ⟨K, h1, h2, -, e⟩ := hb
    exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · exact setIrqState_mem' _ _ _

set_option maxHeartbeats 4000000 in
/-- **The IO port cleanup at `XTop`.** -/
theorem post_ioX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) (hK : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hIo : IoLayout Z.th (L.ksb s)) (f l owner : U64) (hfl : f.val ≤ l.val) (hl : l.val < 65536) :
    objects.post_cap_deletion st arI s a (.IoPort f l owner) ⦃ r =>
      SlotsSame Z.th (L.mem s) (L.mem r.1) ∧ L.ksb r.1 = L.ksb s ∧ ∃ σ',
        ((), σ') ∈ (Fl4Spec.postCapDeletion (Z := Unit) (absCap (.IoPort f l owner)) σ).1 ∧
        CRel Z.th (L.mem r.1) σ' Z.G ∧ XTopAt (L := L) AR Z r.1 r.2 σ' ⦄ := by
  unfold objects.post_cap_deletion ioport.free_ioports
  simp only
  refine WP.spec_bind (set_mask_spec hIo s rfl f l hfl hl false) ?_
  intro s1 hM
  rw [WP.spec_ok]
  have hka : (L.ksb s).val % 8 = 0 := by
    have h0 := (hIo.out 0#u64 (by decide)).1
    unfold P1.Aligned at h0; rw [ioA_val hIo.fit (by decide)] at h0; omega
  have hw : P1.WritesIn st s s1 (KsW (L.ksb s)) := by
    refine ⟨hM.1, hM.2.1, fun b hb hn => hM.2.2.1 b hb fun w hw e => hn ?_⟩
    subst e
    have hv := ioA_val hIo.fit hw
    have hK : (⟨BitVec.ofNat 64 (5344 + 8 * w.val)⟩ : U64).val = 5344 + 8 * w.val := by
      show (BitVec.ofNat 64 _).toNat = _; simp; omega
    exact ⟨⟨BitVec.ofNat 64 (5344 + 8 * w.val)⟩, by rw [hK]; omega, by rw [hK]; omega, by rw [hK]; omega,
      by rw [hK, hv]; omega, by rw [hK]; omega⟩
  set σ' := ioMaskSt (BitVec.ofNat 16 f.val) (BitVec.ofNat 16 l.val) false σ
  have hX' : XTopAt (L := L) AR Z s1 a σ' := by
    refine XTopAt.ksStep hX hK hw (by constructor <;> rfl) ⟨fun i hi => ?_, hX.fin.1.1.2.2.2.1.node⟩
      (IoRel.mask hX.fin.1.1.2.2.2.2.1 hl hfl hM)
      (hX.rel.2.2.2.1.frame (fun o ho => (DK4.of_mask hIo.fit hka hM).2 o ho) rfl rfl)
      hX.fin.1.1.2.2.2.2.2.2
    have hv := irqStA_val hIo.fit hi
    rw [hM.2.2.1 _ (by unfold P1.Aligned; rw [hv]; omega) fun w hw e => by
      have := ioA_val hIo.fit hw; rw [← e, hv] at this; omega]
    exact hX.fin.1.1.2.2.2.1.st i hi
  refine ⟨hX.slotsSame_of hw (fun b hb => ?_), hw.1, σ', setIoportMask_mem _ _ _ _, hX'.rel.2.1, hX'⟩
  obtain ⟨K, h1, h2, -, e⟩ := hb
  exact Or.inr (Or.inl ⟨by omega, by omega⟩)

/-- **`XPostDelHyp` holds** (the IRQ handler and IO port cleanups), from the
kernel-state block's layout at the `XTopAt` states (`IntLayout`, `IoLayout` [P]), the arch IRQ mask
total and keeping `AR` (`ARMask` [P]). -/
theorem xPostDelHyp_of {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) {th : TypedHeap}
    (hLay : ∀ (Z : XSets) s a σ, Z.th = th → XTopAt (L := L) AR Z s a σ →
      IntLayout th (L.ksb s) ∧ IoLayout th (L.ksb s))
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a') :
    XPostDelHyp (L := L) arI AR th := by
  intro Z s a σ cl hth hX hK hTh hDS hcl hcln hclw
  have hLy := hLay Z s a σ hth hX
  subst hth
  cases cl <;> simp only [CleanCap] at hcl
  · exact absurd rfl hcln
  · exact post_irqX arI hAM hX hK hLy.1 hmask _ hclw
  · obtain ⟨hf, hl, hfl⟩ := hclw
    exact post_ioX arI hX hK hLy.2 _ _ _ hfl hl

end

end

end Fl4Proofs.P3
