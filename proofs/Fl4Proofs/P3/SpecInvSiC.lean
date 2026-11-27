/-
P3 (issue #16, sd7; KENTRY-PLAN g7a-4 (2)): **the CNode, IRQ control, IRQ handler,
IO-port control and ASID-pool performs keep `SI N t`** (sg1's SpecInvSgC for the
idle vtable slot; spec side only).

* Every destination these performs write a non-null cap into is a lookup destination
  (`DestRefV`: `notIV_of_destRef`), a slot holding a non-null cap (`notIV_of_held`), or
  an IRQ-node slot (`set_irq_handler`; cref `[]`, no TCB slot). The CNode decode facts are
  sg1's (`CnOKN`, `RotOKN`).
-/
import Fl4Proofs.P3.SpecInvSiG
open Classical

namespace Fl4Proofs.P3.SInvIV
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvG

noncomputable section

set_option maxHeartbeats 1000000

variable {N : Irq → ObjRef} {t : ObjRef}

/-! ## View lemmas -/

theorem iv_post_move {w w' : UView} (h : IVV t w) {src dest : CslotPtr} {c : Cap}
    (h1 : w'.2.1 src = some .nullCap) (h2 : w'.2.1 dest = some c)
    (h3 : ∀ x, x ≠ src → x ≠ dest → w'.2.1 x = w.2.1 x) (hd : NotIV t dest ∨ c = .nullCap) : IVV t w' := by
  intro a ha
  by_cases e1 : (t, tcbCnodeIndex 1) = src
  · rw [e1, h1] at ha; cases ha; rfl
  by_cases e2 : (t, tcbCnodeIndex 1) = dest
  · rcases hd with hd | hd
    · exact absurd e2.symm hd
    · rw [e2, h2] at ha; cases ha; exact hd
  · rw [h3 _ e1 e2] at ha; exact h a ha

theorem iv_swap {w : UView} (h : IVV t w) {s1 s2 : CslotPtr} (h1 : NotIV t s1) (h2 : NotIV t s2) (c1 c2 : Cap) :
    IVV t (vCap s2 c1 (vCap s1 c2 (vRen (sw s1 s2) w))) := by
  refine iv_vCap (iv_vCap ?_ (Or.inl h1)) (Or.inl h2)
  intro a ha
  have e1 : sw s1 s2 (t, tcbCnodeIndex 1) = (t, tcbCnodeIndex 1) := by
    unfold sw; rw [if_neg (fun e => h1 e.symm), if_neg (fun e => h2 e.symm)]
  have ha' : w.2.1 (sw s1 s2 (t, tcbCnodeIndex 1)) = some a := ha
  rw [e1] at ha'
  exact h a ha'

/-! ## The CNode performs -/

/-- **`invoke_cnode` keeps `SI N t`** from the decode's facts. -/
theorem iw_invokeCnode (ci : CnodeInvocation) (σ : State Unit) (hI : SI N t σ) (hok : CnOKN (uV σ) ci)
    (hr : RotOKN (uV σ) ci) : ∀ y ∈ ((invokeCnode (Z := Unit) ci).run σ).1, SI N t y.2 := by
  intro y hy
  cases ci with
  | revokeCall d => exact iw_capRevoke d σ hI y hy
  | deleteCall d => exact iw_capDelete d σ hI y hy
  | insertCall c src dest =>
    simp only [invokeCnode, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact hv_capInsertSI c src dest σ ⟨hI, hok.1, posOK_of_destRef hI.1.1.2 hok.2,
      Or.inl (notIV_of_destRef hI.2.1 hok.2)⟩ x hx
  | moveCall c src dest =>
    obtain ⟨c0, hs, hd, hre, hc, hne, hdr⟩ := hok
    simp only [invokeCnode, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    have hp := posOK_of_destRef hI.1.1.2 hdr
    obtain ⟨hU, h1, h2, h3⟩ := hv_capMove3 hI.1 hs hd hre hc hp hne σ rfl x hx
    have hM := (hv_capMove3 (N := fun _ => t) ⟨hI.1.1, hI.2.1⟩ hs hd hre hc hp hne σ rfl x hx).1
    exact ⟨hU, hM.2, iv_post_move hI.2.2 h1 h2 h3 (Or.inl (notIV_of_destRef hI.2.1 hdr))⟩
  | rotateCall c1 c2 s1 s2 s3 =>
    obtain ⟨c1', c2', h1, h2, hr1, hn1, hr2, hn2, h21, h23, hdr, h3⟩ := hok
    obtain ⟨hd1, hd2⟩ := hr
    have hN1 : NotIV t s1 := notIV_of_destRef hI.2.1 hd1
    have hN2 : NotIV t s2 := notIV_of_destRef hI.2.1 hd2
    simp only [invokeCnode, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    split at hx
    · refine ⟨hv_capSwap3 (Ne.symm h21) hr1 hr2 hn1 hn2 σ ⟨hI.1, h1, h2⟩ x hx,
        (hv_capSwap3 (N := fun _ => t) (Ne.symm h21) hr1 hr2 hn1 hn2 σ ⟨⟨hI.1.1, hI.2.1⟩, h1, h2⟩ x hx).2, ?_⟩
      have hv := capSwap_view (w := uV σ) (Ne.symm h21) c1 c2 σ rfl x hx
      show IVV t (uV x.2)
      rw [hv]
      exact iv_swap hI.2.2 hN1 hN2 c1 c2
    · rename_i h13
      obtain ⟨x1, hx1, hx⟩ := hx
      have hP2 : PosOK (uV σ) s2 := posOK_of_nn hI.1.1.2 h2 (hr2.nn hn2)
      have hP3 : PosOK (uV σ) s3 := posOK_of_destRef hI.1.1.2 hdr
      obtain ⟨hI1, hs1, hd1', hoth⟩ := hv_capMove3 hI.1 h2 (h3 h13) hr2 hn2 hP3 h23 σ rfl x1 hx1
      have hM1 := (hv_capMove3 (N := fun _ => t) ⟨hI.1.1, hI.2.1⟩ h2 (h3 h13) hr2 hn2 hP3 h23 σ rfl x1 hx1).1
      have hnov1 : IVV t (uV x1.2) :=
        iv_post_move hI.2.2 hs1 hd1' hoth (Or.inl (notIV_of_destRef hI.2.1 hdr))
      have h1' : (uV x1.2).2.1 s1 = some c1' := by
        rw [hoth s1 (Ne.symm h21) h13]; exact h1
      have hP2' : PosOK (uV x1.2) s2 := posOK_move h2 hr2 hs1 hd1' hoth (h3 h13) hP2
      obtain ⟨hI2, hs2, hd2', hoth2⟩ := hv_capMove3 hI1 h1' hs1 hr1 hn1 hP2' (Ne.symm h21) x1.2 rfl x hx
      have hM2 := (hv_capMove3 (N := fun _ => t) ⟨hI1.1, hM1.2⟩ h1' hs1 hr1 hn1 hP2' (Ne.symm h21) x1.2 rfl x hx).1
      exact ⟨hI2, hM2.2, iv_post_move hnov1 hs2 hd2' hoth2 (Or.inl hN2)⟩
  | cancelBadgedSendsCall cap =>
    cases cap
    case endpointCap ep b r =>
      exact (show IKE (SI N t) (withoutPreemption (Z := Unit) (NonDet.when (b ≠ 0) (cancelBadgedSends ep b))) by
        iw_auto) σ hI y hy
    all_goals
      obtain ⟨x, hx, -⟩ := mem_liftE' (show y ∈ ((NonDetE.liftE (ε := Unit)
        (NonDet.fail : NonDet (State Unit) Unit)).run σ).1 from hy)
      exact hx.elim

/-! ## Issue inserts -/

/-- An insert of a cap derived from the source's cap into a CNode lookup slot keeps `SIV N t`. -/
theorem hv_insertCtlSI {c0 c : Cap} (hR : RefRel c0 c) (src dest : CslotPtr) :
    HV (fun w => SIV N t w ∧ w.2.1 src = some c0 ∧ DestRefV w dest) (SIV N t) (capInsert (Z := Unit) c src dest) :=
  hv_pre (hv_capInsertSI c src dest) fun _ h => ⟨h.1, ⟨c0, h.2.1, Or.inr hR⟩, posOK_of_destRef h.1.1.1.2 h.2.2,
    Or.inl (notIV_of_destRef h.1.2.1 h.2.2)⟩

macro "iwctl_auto" : tactic => `(tactic| repeat' (first
  | exact hv_insertCtlSI (refRel_irq _) _ _ | exact hv_insertCtlSI (refRel_ioport _ _) _ _
  | (refine hv_pure_bind ?_) | (dsimp only)
  | (refine hv_bind (hv_uk fun _ => by uk_auto) fun _ => ?_)))

theorem iw_archInvokeIrqControl (i : ArchIrqControlInvocation) (σ : State Unit) (hI : SI N t σ)
    (hok : ArchIrqOKN (uV σ) i) : ∀ y ∈ ((archInvokeIrqControl (Z := Unit) i).run σ).1, SI N t y.2 := by
  intro y hy
  cases i with
  | issueIRQHandlerIOAPIC irq dest src ioapic pin level polarity vector =>
    simp only [archInvokeIrqControl, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (show HV (fun w => SIV N t w ∧ w.2.1 src = some .irqControlCap ∧ DestRefV w dest) (SIV N t) _ by iwctl_auto)
      σ ⟨hI, hok⟩ x hx
  | issueIRQHandlerMSI irq dest src bus dev func handle =>
    simp only [archInvokeIrqControl, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (show HV (fun w => SIV N t w ∧ w.2.1 src = some .irqControlCap ∧ DestRefV w dest) (SIV N t) _ by iwctl_auto)
      σ ⟨hI, hok⟩ x hx

theorem iw_invokeIrqControl (i : IrqControlInvocation) (σ : State Unit) (hI : SI N t σ)
    (hok : IrqCOKN (uV σ) i) : ∀ y ∈ ((invokeIrqControl (Z := Unit) i).run σ).1, SI N t y.2 := by
  intro y hy
  cases i with
  | irqControl irq dest src =>
    simp only [invokeIrqControl] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (show HV (fun w => SIV N t w ∧ w.2.1 src = some .irqControlCap ∧ DestRefV w dest) (SIV N t) _ by iwctl_auto)
      σ ⟨hI, hok⟩ x hx
  | archIRQControl i => exact iw_archInvokeIrqControl i σ hI hok y hy

theorem iw_invokeFl4IrqControl (i : Fl4IrqControlInvocation) (σ : State Unit) (hI : SI N t σ)
    (hok : Fl4IrqCOKN (uV σ) i) : ∀ y ∈ ((invokeFl4IrqControl (Z := Unit) i).run σ).1, SI N t y.2 := by
  intro y hy
  cases i with
  | spec i => exact iw_invokeIrqControl i σ hI hok y hy
  | ioapicRemapped irq dest src ioapic pin level polarity vector handle =>
    simp only [invokeFl4IrqControl, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (show HV (fun w => SIV N t w ∧ w.2.1 src = some .irqControlCap ∧ DestRefV w dest) (SIV N t) _ by iwctl_auto)
      σ ⟨hI, hok⟩ x hx

theorem iw_performIoportControl (i : IoPortControlInvocation) (σ : State Unit) (hI : SI N t σ)
    (hok : IoCOKN (uV σ) i) : ∀ y ∈ (performIoportControlInvocation (Z := Unit) i σ).1, SI N t y.2 := by
  cases i with
  | ioPortControlInvocation f l dest src =>
    unfold performIoportControlInvocation
    exact (show HV (fun w => SIV N t w ∧ w.2.1 src = some (.archObjectCap .ioPortControlCap) ∧ DestRefV w dest)
      (SIV N t) _ by iwctl_auto) σ ⟨hI, hok⟩

/-! ## The IRQ handler -/

/-- **`set_irq_handler` keeps `SI N t`**: it writes into the IRQ-node slot, no TCB slot. -/
theorem iw_setIRQHandler (irq : Irq) (cap : Cap) (slot : CslotPtr) (σ : State Unit) (hI : SI N t σ)
    (hN : σ.interruptIrqNode = N) (hok : IrqHOKN (uV σ) (.setIRQHandler irq cap slot)) :
    ∀ y ∈ (invokeIrqHandler (Z := Unit) (.setIRQHandler irq cap slot) σ).1, SI N t y.2 := by
  have hP := p3_setIRQHandler irq cap slot σ hI.1 hN hok
  obtain ⟨hc, hdr, hnt⟩ := hok
  intro y hy
  refine ⟨hP y hy, ?_⟩
  simp only [invokeIrqHandler, getIrqSlot] at hy
  obtain ⟨x1, hx1, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hx1
  obtain ⟨x2, hx2, hy⟩ := hy
  dsimp only at hx2 hy
  rw [hN] at hx2 hy
  have hne : slot ≠ (N irq, []) := notNode_of_destRef hI.1.2 hdr irq
  have hc2 : (uV x2.2).2.1 slot = some cap := (capDeleteOne_keep _ slot hne (uV σ) σ rfl x2 hx2).trans hc
  have hO2 : IrqOutV (fun _ => t) (uV x2.2) := io_capDeleteOne (N := fun _ => t) _ σ hI.2.1 x2 hx2
  have hn2 : IVV t (uV x2.2) := iw_capDeleteOne_iv _ σ hI.2.2 x2 hx2
  have hnv : NotIV t (N irq, []) := fun e => tcbCnodeIndex_ne_nil 1 (congrArg Prod.snd e).symm
  exact ⟨hv_capInsertIO cap slot _ x2.2 ⟨hO2, fun c0 h0 => by rw [hc2] at h0; cases h0; exact subset_rfl⟩ y hy,
    iv_capInsert cap slot _ x2.2 ⟨hn2, Or.inl hnv⟩ y hy⟩

/-! ## The ASID pool -/

theorem iw_performAsidPoolInvocation (iv : AsidPoolInvocation) :
    IK (SI N t) (performAsidPoolInvocation (Z := Unit) iv) := by
  refine iw_of (fun _ => p3_performAsidPoolInvocation iv) fun σ h y hy => ?_
  cases iv with
  | assign asid poolPtr ctSlot =>
    refine (show HV (IVV t) (IVV t) (performAsidPoolInvocation (Z := Unit) (.assign asid poolPtr ctSlot)) from ?_)
      σ h.2.2 y hy
    unfold performAsidPoolInvocation
    refine hv_getCap_bind fun w c hw hc => ?_
    split
    · rename_i b m
      refine hv_bind (hv_pre (iv_setCap _ _) fun w' e => e ▸ ⟨hw, Or.inl (notIV_of_held hw hc ?_)⟩)
        fun _ => hv_uk fun _ => uk_storeAsidPoolEntry _ _ _
      intro e; cases e
    · intro σ _ y hy; exact hy.elim

end

end Fl4Proofs.P3.SInvIV
