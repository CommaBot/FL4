/-
P3 (line irqfix, gen 3): vih3's cap and IRQ-state writers (SpecInvValidIrqHandlersW) restated for l4v's
`valid_irq_handlers` (`ValidIrqHandlersL`, SpecInvVihL): `CAL c is` (a handler cap's line is in `IRQSignal`),
`VHL R σ := ValidIrqMasks σ ∧ ValidIrqHandlersL σ ∧ R σ.interruptStates`, `VIL`, `RML R` (`R` survives lines
entering `IRQSignal`). Leaves as vih3's: `set_cap` of a `CAL` cap, `set_untyped_cap_as_full`, `cap_insert`,
`cap_move`, `cap_swap`, `cap_swap_for_delete`, `create_cap`, `retype_region`, `delete_objects`, and
`set_irq_state IRQSignal` (`vhl_setIrqState_signal`). The generic pieces (pinned `get_cap` binds, CDT writers)
are vih3's, reused. No premise; no sorry.
-/
import Fl4Proofs.P3.SpecInvVihL
import Fl4Proofs.P3.SpecInvValidIrqHandlersW
open Classical

namespace Fl4Proofs.P3.SInvVL
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.MachT Fl4Proofs.P3.MachF Fl4Proofs.P3.SInvV

noncomputable section

set_option maxHeartbeats 1000000

/-- A cap that may be written: a handler cap names a line that is not inactive. -/
def CAL (c : Cap) (is : Irq → IrqState) : Prop := ∀ irq, c = .irqHandlerCap irq → is irq = .irqSignal

/-- `R` survives lines becoming non-inactive. -/
def RML (R : (Irq → IrqState) → Prop) : Prop :=
  ∀ is is', (∀ i, is i = .irqSignal → is' i = .irqSignal) → R is → R is'

/-- **The invariant with a carried IRQ-state fact** (module docstring). -/
def VHL (R : (Irq → IrqState) → Prop) (σ : State Unit) : Prop :=
  ValidIrqMasks σ ∧ ValidIrqHandlersL σ ∧ R σ.interruptStates

abbrev VIL : State Unit → Prop := VHL (fun _ => True)

theorem cal_of_slot {σ : State Unit} (h : ValidIrqHandlersL σ) {p : ObjRef} {r : CnodeIndex} {c : Cap}
    (hc : capOpt (σ.kheap p) r = some c) : CAL c σ.interruptStates :=
  fun irq e => h p r irq (e ▸ hc)

theorem rml_ca (c : Cap) : RML (CAL c) := fun _ _ hm h irq e => hm irq (h irq e)
theorem rml_true : RML (fun _ => True) := fun _ _ _ _ => trivial
theorem rml_and {R1 R2 : (Irq → IrqState) → Prop} (h1 : RML R1) (h2 : RML R2) : RML (fun is => R1 is ∧ R2 is) :=
  fun is is' hm h => ⟨h1 is is' hm h.1, h2 is is' hm h.2⟩

theorem cal_noH {c : Cap} (h : ∀ irq, c ≠ .irqHandlerCap irq) (is : Irq → IrqState) : CAL c is :=
  fun irq e => absurd e (h irq)

instance (R : (Irq → IrqState) → Prop) : WLH (VHL R) where
  view σ σ' e w h := ⟨WLH.view (P := ValidIrqMasks) σ σ' e w h.1,
    WLH.view (P := ValidIrqHandlersL) σ σ' e w h.2.1, by rw [hV_is e]; exact h.2.2⟩
  uts σ h x hx := ⟨WLH.uts (P := ValidIrqMasks) σ h.1 x hx, WLH.uts (P := ValidIrqHandlersL) σ h.2.1 x hx,
    by rw [hV_is (hv_uts (hV σ) σ rfl x hx)]; exact h.2.2⟩
  msk mop hm σ h x hx := ⟨WLH.msk (P := ValidIrqMasks) mop hm σ h.1 x hx,
    WLH.msk (P := ValidIrqHandlersL) mop hm σ h.2.1 x hx,
    by rw [hV_is (ik_doMachineOp (P := fun σ' => hV σ' = hV σ) (fun _ _ h => h) mop σ rfl x hx)]; exact h.2.2⟩

/-- A step keeping the machine fields keeps `ValidIrqMasks` and `R`; `VHL R`
follows from `ValidIrqHandlersL`. -/
theorem vhl_of_mtk {R : (Irq → IrqState) → Prop} {σ σ' : State Unit} (e : msFT σ' = msFT σ) (h : VHL R σ)
    (hh : ValidIrqHandlersL σ') : VHL R σ' :=
  ⟨vim_view σ σ' (vw_of_msFT e) h.1, hh, by rw [is_of_vw (vw_of_msFT e)]; exact h.2.2⟩

/-- Strengthen the carried fact for one step. -/
theorem ikp_vhl_and {R Q : (Irq → IrqState) → Prop} {α : Type} {m : NonDet (State Unit) α} {σ : State Unit}
    (hm : IKH (VHL fun is => R is ∧ Q is) m) (hq : Q σ.interruptStates) : IKp (VHL R) σ m :=
  fun h x hx => let h' := hm σ ⟨h.1, h.2.1, h.2.2, hq⟩ x hx; ⟨h'.1, h'.2.1, h'.2.2.1⟩

theorem ik_vhl_weaken {R Q : (Irq → IrqState) → Prop} {α : Type} {m : NonDet (State Unit) α}
    (hm : IKH (VHL Q) m) (hq : ∀ is, R is → Q is) (hr : ∀ σ x, x ∈ (m σ).1 → Q σ.interruptStates →
      R σ.interruptStates → R x.2.interruptStates) : IKH (VHL R) m :=
  fun σ h x hx => let h' := hm σ ⟨h.1, h.2.1, hq _ h.2.2⟩ x hx; ⟨h'.1, h'.2.1, hr σ x hx (hq _ h.2.2) h.2.2⟩

/-! ## `set_cap` -/

section C
variable {R : (Irq → IrqState) → Prop}

theorem vhl_setCap_p (c : Cap) (sl : CslotPtr) (σ : State Unit) (hc : VHL R σ → CAL c σ.interruptStates) :
    IKp (VHL R) σ (setCap (Z := Unit) c sl) := by
  intro h x hx
  have e := mtk_setCap c sl σ x hx
  exact vhl_of_mtk e h (h.2.1.hk (hkl_setCap sl (fun irq e' => Or.inr (hc h irq e')) x hx))

theorem vhl_setCap (c : Cap) (sl : CslotPtr) (hc : ∀ is, R is → CAL c is) : IKH (VHL R) (setCap (Z := Unit) c sl) :=
  fun σ => vhl_setCap_p c sl σ fun h => hc _ h.2.2

end C

/-- Side conditions `∀ is, R is → CAL c is`. -/
macro "cal_side" : tactic => `(tactic| first
  | assumption
  | (intro _ _ _ h; cases h; done)
  | (intro _ _; exact cal_noH (by intro _ h; cases h) _)
  | (intro _ h; exact h.1)
  | (intro _ h; exact h.2.1)
  | (intro _ h; exact h.2)
  | (intro _ _; exact cal_noH (fun _ h => by simp_all) _))

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine vhl_setCap _ _ ?_); cal_side))

section C2
variable {R : (Irq → IrqState) → Prop}

theorem cal_freeIndexUpdate_ut {c : Cap} (h : isUntypedCap c = true) (g : Nat → Nat) (is : Irq → IrqState) :
    CAL (freeIndexUpdate g c) is := by
  cases c <;> first | (simp [isUntypedCap] at h; done) | exact cal_noH (fun _ e => by simp [freeIndexUpdate] at e) _

theorem vhl_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : CslotPtr) :
    IKH (VHL R) (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull
  split
  · rename_i h
    exact vhl_setCap _ _ fun is _ => cal_freeIndexUpdate_ut (by simpa using h.1) _ is
  · exact ik_pure _

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vhl_setUntypedCapAsFull _ _ _)

theorem vhl_capInsert (c : Cap) (src dst : CslotPtr) (hc : ∀ is, R is → CAL c is) :
    IKH (VHL R) (capInsert (Z := Unit) c src dst) := by
  unfold capInsert; hv_auto

theorem vhl_capMove (c : Cap) (src dst : CslotPtr) (hc : ∀ is, R is → CAL c is) :
    IKH (VHL R) (capMove (Z := Unit) c src dst) := by
  unfold capMove; hv_auto

theorem vhl_capSwap (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) (hc1 : ∀ is, R is → CAL c1 is)
    (hc2 : ∀ is, R is → CAL c2 is) : IKH (VHL R) (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap; hv_auto

/-- `cap_swap_for_delete`: both caps are read from slots of the same state. -/
theorem vhl_capSwapForDelete (s1 s2 : CslotPtr) : IKH (VHL R) (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete
  refine ik_when _ (ik_getCap_bind fun c1 σ h1 => ikp_getCap_bind fun c2 h2 hσ => ?_)
  refine ikp_vhl_and (Q := fun is => CAL c1 is ∧ CAL c2 is)
    (vhl_capSwap c1 s1 c2 s2 (fun _ h => h.2.1) (fun _ h => h.2.2)) ⟨cal_of_slot hσ.2.1 h1, cal_of_slot hσ.2.1 h2⟩ hσ

theorem cal_defaultCap (t : ApiObjectType) (o : ObjRef) (b : Nat) (d : Bool) (is : Irq → IrqState) :
    CAL (defaultCap t o b d) is :=
  cal_noH (fun _ e => by cases t <;> simp only [defaultCap] at e <;> cases e) _

theorem vhl_createCap (t : ApiObjectType) (b : Nat) (u : CslotPtr) (d : Bool) (x : CslotPtr × ObjRef) :
    IKH (VHL R) (createCap (Z := Unit) t b u d x) := by
  obtain ⟨dest, oref⟩ := x
  unfold createCap; dsimp only
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_gets _) fun _ => ik_bind (hv_setCdt _) fun _ =>
    ik_bind (ik_doExtendedOp (fun _ _ h => WLH.view _ _ (by rfl) (by rfl) h) _) fun _ =>
    ik_bind (hv_setOriginal _ _) fun _ => vhl_setCap _ _ fun is _ => cal_defaultCap _ _ _ _ is

end C2

/-! ## Retype and detype -/

section RT
variable {R : (Irq → IrqState) → Prop}

theorem vhl_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType)
    (dev : Bool) : IKH (VHL R) (retypeRegionWith (Z := Unit) bA ptr n oB ty dev) := by
  intro σ h y hy
  have e := mtk_retypeRegionWith' bA ptr n oB ty dev σ y hy
  refine vhl_of_mtk e h ?_
  rcases (SInvU.retypeRegionWith_out hy).2 with e' | ⟨hty, e'⟩
  · rw [e']; exact h.2.1
  · rw [e']
    intro p cref irq hc
    have ei := is_of_vw (vw_of_msFT e)
    rw [e'] at ei
    simp only [SInvU.retKh] at hc
    split_ifs at hc
    · exact absurd hc (capOpt_default_noH hty _ _ _ _ _)
    · exact h.2.1 p cref irq hc

theorem vhl_retypeRegion (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType) (dev : Bool) :
    IKH (VHL R) (retypeRegion (Z := Unit) ptr n oB ty dev) := by
  rw [← retypeRegionWith_objBitsApi]; exact vhl_retypeRegionWith _ _ _ _ _ _

theorem vhl_deleteObjects (ptr : Word) (bits : Nat) : IKH (VHL R) (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  refine ik_bind (WLH.msk _ (mt_freeMemory _ _)) fun _ => ik_modify fun σ h => ?_
  refine ⟨vim_view σ _ rfl h.1, fun p cref irq hc => ?_, h.2.2⟩
  simp only [detype] at hc
  split_ifs at hc
  · simp [capOpt] at hc
  · exact h.2.1 p cref irq hc

end RT

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vhl_createCap _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vhl_retypeRegionWith _ _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vhl_retypeRegion _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vhl_deleteObjects _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vhl_capSwapForDelete _ _)

/-! ## `set_irq_state` -/

theorem vhl_setIrqState_signal {R : (Irq → IrqState) → Prop} (hR : RML R) {st : IrqState}
    (hst : st = .irqSignal) (i : Irq) : IKH (VHL R) (setIrqState (Z := Unit) st i) := by
  intro σ h x hx
  obtain ⟨hk, hi⟩ := setIrqState_out hx
  refine ⟨vim_sis st i σ h.1 x hx, h.2.1.hk (hkl_setIrqState_signal hst i σ x hx), ?_⟩
  refine hR _ _ (fun j hj => ?_) h.2.2
  rw [hi]; by_cases e : j = i
  · subst e; rw [Function.update_self]; exact hst
  · rw [Function.update_of_ne e]; exact hj

end

end Fl4Proofs.P3.SInvVL
