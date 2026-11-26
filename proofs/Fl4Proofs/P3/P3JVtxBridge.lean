/-
P3 (line p3J, gen 3): **the bridge from U37's scope to the spec extension** (`Fl4Spec/Ext/VirtP3x`).

* **`vtxInv_of_virtRoute`**: for a native cap (`Vs.NativeCap`) whose message's extra caps do not start with a
  virtualization cap, every `VirtRoute` input (VirtP3x: the inputs on which the extended decoder
  `fl4DecodeInvocationV` leaves the ported `fl4DecodeInvocation`) is a `VtxInv` (XTopJointKEntryU37):
  label 88 on a thread cap, label 60 (or an EPT-mapped frame's map / unmap) on a frame cap, the VT-x retype
  gate (`untypedVtxGate`) on an untyped cap; an ASID pool's EPT-root assign needs an EPT cap first among the
  extra caps. VCPU / EPT caps are not native.
* **`decodeV_eq_of_noVtx`**: so off a `VtxInv` (U37's `KNoVtx` at the invoked cap) the decode U37 refines
  against, `fl4DecodeInvocation … (absCap c) …` (`specDec`), is the extended decoder's, through VirtP3x's
  `fl4DecodeInvocationV_base`: on the entries U37 covers, the ported decode and the extension's decode of
  FL4's VT-x behaviour agree.
No premise; no sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU37
import Fl4Spec.Ext.VirtP3x
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core

theorem dtn_bv37 (w : U64) : Fl4Spec.dataToNat w.bv = w.val := rfl

/-- **Every `VirtRoute` input of a native cap is a `VtxInv`** (module docstring). -/
theorem vtxInv_of_virtRoute {fp : Bool} {lbl : U64} {argsU : List U64} {c : capability.Cap}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} (hN : Vs.NativeCap c)
    (hX : ∀ x ∈ excaps.head?, ¬ Fl4Spec.IsVirtCap x.1)
    (h : Fl4Spec.VirtRoute fp lbl.bv (argsU.map UScalar.bv) (absCap c) excaps) : VtxInv c lbl argsU := by
  cases c
  case Thread p =>
    have h' : ¬ fp = true ∧ Fl4Spec.dataToNat lbl.bv = Fl4Spec.fl4SetEptRootLabel := h
    show lbl = fl4_abi.label.TCBSetEPTRoot
    exact UScalar.eq_of_val_eq (h'.2.trans (by simp [fl4_abi.label.TCBSetEPTRoot, Fl4Spec.fl4SetEptRootLabel]))
  case Frame p sz r d m ept asid va =>
    show ept = true ∨ lbl = fl4_abi.label.X86PageMapEPT
    rcases (h : _ ∨ _ ∨ _) with h1 | ⟨hm, -⟩ | ⟨hm, -⟩
    · right
      exact UScalar.eq_of_val_eq (h1.trans (by simp [fl4_abi.label.X86PageMapEPT, Fl4Spec.fl4PageMapEptLabel]))
    · left
      cases ept
      · cases m <;> simp at hm
      · rfl
    · left
      cases ept
      · cases m <;> simp at hm
      · rfl
  case Untyped p sb fi dev =>
    have h' : Fl4Spec.untypedVtxGate lbl.bv (argsU.map UScalar.bv) (excaps.map Prod.fst) := h
    obtain ⟨-, hlen, -, hv, -⟩ := h'
    show ∃ x, argsU.head? = some x ∧ 14 ≤ x.val ∧ x.val < 19
    cases argsU with
    | nil => simp at hlen
    | cons x xs =>
      refine ⟨x, rfl, ?_⟩
      have hv' : 14 ≤ Fl4Spec.dataToNat x.bv ∧ Fl4Spec.dataToNat x.bv ≤ 18 := by
        simpa [Fl4Spec.isVtxObjectTypeNum] using hv
      rw [dtn_bv37] at hv'
      exact ⟨hv'.1, by omega⟩
  case AsidPool p base =>
    have h' : Fl4Spec.invocationType lbl.bv = .archInvocationLabel .x64ASIDPoolAssign ∧
        Fl4Spec.startsWithEptRoot excaps = true := h
    obtain ⟨-, he⟩ := h'
    clear h
    match excaps, he, hX with
    | (.archObjectCap (.eptCap _ 0 none), _) :: _, _, hX => exact (hX _ rfl trivial).elim
  case Vcpu p => exact (hN : False).elim
  case Ept p l m asid va => exact (hN : False).elim
  all_goals exact (h : False).elim

/-- **Off a `VtxInv`, the refined decode is the extension's** (module docstring). -/
theorem decodeV_eq_of_noVtx (fp : Bool) (lbl : U64) (argsU : List U64) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (hN : Vs.NativeCap c) (hv : ¬ VtxInv c lbl argsU)
    (hX : ∀ x ∈ excaps.head?, ¬ Fl4Spec.IsVirtCap x.1) :
    Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp lbl.bv (argsU.map UScalar.bv) ci sl (absCap c) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4InvocationV.base
        (Fl4Spec.fl4DecodeInvocation fp lbl.bv (argsU.map UScalar.bv) ci sl (absCap c) excaps buffer) :=
  Fl4Spec.fl4DecodeInvocationV_base fp lbl.bv (argsU.map UScalar.bv) ci sl (absCap c) excaps buffer
    (fun h => hv (vtxInv_of_virtRoute hN hX h))

end Fl4Proofs.P3.SInvR.G5
