/-
P3 (DESIGN.md §9): **invocations whose spec result is empty** (for
`TopPostDMX`, HandleTopX.lean).

* `OkAll P m`: every `ok` outcome of the spec computation `m` satisfies `P`,
  with combinators for `bind`, `pure`, `throw`, `liftE`, `liftME` and `ite`.
* `NilInv inv`: the invocations whose `fl4PerformInvocation` returns `[]`
  among those the VSpace and domain caps decode to; `perform_nil`.
* `decOut_nil_*`: the VSpace and domain caps' decodes give only such
  invocations, except a page cap's `GetAddress` (which FL4 replies itself,
  `DecOKRMX`).
-/
import Fl4Proofs.P3.HandleTopX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open Classical

noncomputable section

section OkAll
open Fl4Spec

/-- Every `ok` outcome of `m` satisfies `P`. -/
def OkAll {σ ε α : Type} (P : α → Prop) (m : NonDetE σ ε α) : Prop :=
  ∀ s y, y ∈ (m.run s).1 → ∀ a, y.1 = .ok a → P a

variable {σ ε α β : Type}

theorem okAll_bind' {Q : α → Prop} {P : β → Prop} {m : NonDetE σ ε α} {f : α → NonDetE σ ε β}
    (hm : OkAll Q m) (h : ∀ a, Q a → OkAll P (f a)) : OkAll P (m >>= f) := by
  intro s y hy a hya
  obtain ⟨z, hz, ⟨b, hb, hy'⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE_inv hy
  · exact h b (hm s z hz b hb) z.2 y hy' a hya
  · cases hya

theorem okAll_bind {P : β → Prop} {m : NonDetE σ ε α} {f : α → NonDetE σ ε β}
    (h : ∀ a, OkAll P (f a)) : OkAll P (m >>= f) :=
  okAll_bind' (Q := fun _ => True) (fun _ _ _ _ _ => trivial) fun a _ => h a

theorem okAll_pure {P : α → Prop} {a : α} (h : P a) : OkAll (σ := σ) (ε := ε) P (pure a) := by
  intro s y hy b hb
  rw [ExceptT.run_pure] at hy
  rw [Set.mem_singleton_iff.1 hy] at hb
  cases hb; exact h

theorem okAll_returnOk {P : α → Prop} {a : α} (h : P a) : OkAll (σ := σ) (ε := ε) P (NonDetE.returnOk a) :=
  okAll_pure h

theorem okAll_throw {P : α → Prop} {e : ε} : OkAll (σ := σ) P (NonDetE.throwError e) := by
  intro s y hy b hb
  unfold NonDetE.throwError at hy
  rw [ExceptT.run_throw] at hy
  rw [Set.mem_singleton_iff.1 hy] at hb
  cases hb

/-- The values of a `NonDet` computation. -/
def NdAll (P : α → Prop) (m : NonDet σ α) : Prop := ∀ s x, x ∈ (m s).1 → P x.1

theorem okAll_liftE {P : α → Prop} {m : NonDet σ α} (h : NdAll P m) :
    OkAll (ε := ε) P (NonDetE.liftE m) := by
  intro s y hy b hb
  unfold NonDetE.liftE at hy
  rw [ExceptT.run_lift] at hy
  obtain ⟨x, hx, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy] at hb
  cases hb; exact h s x hx

theorem okAll_liftE_fail {P : α → Prop} : OkAll (ε := ε) P (NonDetE.liftE (NonDet.fail : NonDet σ α)) :=
  okAll_liftE fun _ _ hx => by simp [NonDet.fail] at hx

theorem okAll_liftME {Q : α → Prop} {P : β → Prop} {f : α → β} {m : NonDetE σ ε α}
    (hm : OkAll Q m) (hf : ∀ a, Q a → P (f a)) : OkAll P (NonDetE.liftME f m) := by
  unfold NonDetE.liftME
  exact okAll_bind' hm fun a ha => okAll_pure (hf a ha)

theorem okAll_ite {P : α → Prop} {c : Prop} [Decidable c] {m1 m2 : NonDetE σ ε α}
    (h1 : c → OkAll P m1) (h2 : ¬ c → OkAll P m2) : OkAll P (if c then m1 else m2) := by
  split
  · exact h1 ‹_›
  · exact h2 ‹_›

theorem okAll_mono {P Q : α → Prop} {m : NonDetE σ ε α} (h : OkAll P m) (hPQ : ∀ a, P a → Q a) : OkAll Q m :=
  fun s y hy a ha => hPQ a (h s y hy a ha)

theorem ndAll_bind {P : β → Prop} {m : NonDet σ α} {f : α → NonDet σ β} (h : ∀ a, NdAll P (f a)) :
    NdAll P (m >>= f) := by
  intro s x hx
  obtain ⟨z, -, hz⟩ := hx
  exact h z.1 z.2 x hz

theorem ndAll_pure {P : α → Prop} {a : α} (h : P a) : NdAll (σ := σ) P (pure a) := by
  intro s x hx
  rw [Set.mem_singleton_iff.1 hx]; exact h

theorem ndAll_fail {P : α → Prop} : NdAll (σ := σ) P NonDet.fail := by
  intro s x hx; simp [NonDet.fail] at hx

theorem DecOut.okAll {α : Type} {m : SEMonad Unit α} {σ : State Unit} {inv : α} {P : α → Prop}
    (h : DecOut m σ inv) (hm : OkAll P m) : P inv :=
  hm σ _ h.1 inv rfl

end OkAll

section Nil
open Fl4Spec fl4_core

macro "ndall" : tactic => `(tactic| (
  repeat (first
    | exact ndAll_fail
    | (unfold archNoReturn)
    | (refine ndAll_pure ?_; rfl)
    | split
    | (refine ndAll_bind fun _ => ?_))))

def NilArch : ArchInvocation → Prop
  | .invokePage (.pageGetAddr _) => False
  | .invokeIOPort _ => False
  | _ => True

def NilInv : Fl4Invocation → Prop
  | .invokeDomain _ => True
  | .invokeArchObject (.pml4Flush _) => True
  | .invokeArchObject (.deriveSubframe _) => True
  | .invokeArchObject (.spec i) => NilArch i
  | _ => False

theorem arch_nil {i : ArchInvocation} (h : NilArch i) :
    OkAll (· = []) (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation
  refine okAll_liftE ?_
  cases i with
  | invokePage op =>
    cases op with
    | pageGetAddr _ => exact absurd h id
    | _ => dsimp only; unfold performPageInvocation; dsimp only; ndall
  | invokeIOPort _ => exact absurd h id
  | _ => dsimp only; ndall

theorem perform_nil (b c d : Bool) {inv : Fl4Invocation} (h : NilInv inv) :
    OkAll (· = []) (fl4PerformInvocation (Z := Unit) b c d inv) := by
  cases inv with
  | invokeDomain _ => exact okAll_liftE (by ndall)
  | invokeArchObject i =>
    cases i with
    | spec i => exact arch_nil h
    | pml4Flush _ => exact okAll_liftE (by ndall)
    | deriveSubframe _ => exact okAll_liftE (by ndall)
    | testAndClearAccessed _ => exact absurd h id
  | _ => exact absurd h id

macro "okall" : tactic => `(tactic| (
  repeat (first
    | exact okAll_throw
    | exact okAll_liftE_fail
    | (refine okAll_returnOk ?_; first | exact ⟨_, rfl⟩ | trivial)
    | (refine okAll_pure ?_; first | exact ⟨_, rfl⟩ | trivial)
    | (refine okAll_ite (fun _ => ?_) (fun _ => ?_))
    | split
    | (refine okAll_bind fun _ => ?_)
    | (unfold NonDetE.whenE)
    | (unfold NonDetE.unlessE)
    | (dsimp only)
    | (unfold letFun))))

theorem okAll_true {σ ε α : Type} (m : NonDetE σ ε α) : OkAll (fun _ => True) m := fun _ _ _ _ _ => trivial

/-- The arch caps but a page cap: the decode gives a `NilInv` arch invocation. -/
theorem okAll_archDecode {label : Data} {args : List Data} {x : CapRef} {cte : CslotPtr} {cap : ArchCap}
    {ex : List (Cap × CslotPtr)} (hc : ∀ a b c d e f, cap ≠ .pageCap a b c d e f) (hio : ∀ f l, cap ≠ .ioPortCap f l)
    (hioc : cap ≠ .ioPortControlCap) :
    OkAll NilArch (archDecodeInvocation (Z := Unit) label args x cte cap ex) := by
  unfold archDecodeInvocation
  cases cap with
  | pageCap a b c d e f => exact absurd rfl (hc a b c d e f)
  | ioPortCap f l => exact absurd rfl (hio f l)
  | ioPortControlCap => exact absurd rfl hioc
  | pageTableCap _ _ => dsimp only; unfold decodePageTableInvocation; okall
  | pageDirectoryCap _ _ => dsimp only; unfold decodePageDirectoryInvocation; okall
  | pdPointerTableCap _ _ => dsimp only; unfold decodePdptInvocation; okall
  | _ => dsimp only; okall

set_option maxHeartbeats 2000000 in
theorem okAll_pageDecode {label : Data} {args : List Data} {cte : CslotPtr} {cap : ArchCap}
    {ex : List (Cap × CslotPtr)} (hl : invocationType label ≠ .archInvocationLabel .x64PageGetAddress) :
    OkAll NilArch (decodePageInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageInvocation
  okall
  all_goals exact absurd ‹_› hl

theorem okAll_specDec_arch (fp : Bool) (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    {c : fl4_core.capability.Cap} (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) {ac : ArchCap}
    (habs : absCap c = .archObjectCap ac) (hc : ∀ a b c d e f, ac ≠ .pageCap a b c d e f)
    (hio : ∀ f l, ac ≠ .ioPortCap f l) (hioc : ac ≠ .ioPortControlCap) :
    OkAll NilInv (specDec fp slbl args ci sl c excaps buffer) := by
  unfold specDec
  rw [habs]
  unfold fl4DecodeInvocation
  dsimp only
  refine okAll_liftME (Q := fun a => NilInv (.invokeArchObject a)) ?_ (fun _ h => h)
  unfold fl4ArchDecodeInvocation
  cases ac with
  | pageCap a b c d e f => exact absurd rfl (hc a b c d e f)
  | pml4Cap _ _ =>
    dsimp only
    refine okAll_ite (fun _ => okAll_liftME (okAll_true _) fun _ _ => trivial)
      (fun _ => okAll_liftME (okAll_archDecode hc hio hioc) fun _ h => h)
  | _ => dsimp only; exact okAll_liftME (okAll_archDecode hc hio hioc) fun _ h => h

theorem okAll_specDec_frame (fp : Bool) (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    {c : fl4_core.capability.Cap} (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) {a b r d e f}
    (habs : absCap c = .archObjectCap (.pageCap a b r d e f))
    (hTAC : dataToNat slbl ≠ fl4TestAndClearLabel)
    (hGA : invocationType slbl ≠ .archInvocationLabel .x64PageGetAddress) :
    OkAll NilInv (specDec fp slbl args ci sl c excaps buffer) := by
  unfold specDec
  rw [habs]
  unfold fl4DecodeInvocation
  dsimp only
  refine okAll_liftME (Q := fun a => NilInv (.invokeArchObject a)) ?_ (fun _ h => h)
  unfold fl4ArchDecodeInvocation
  dsimp only
  refine okAll_ite (fun _ => okAll_liftME (okAll_true _) fun _ _ => trivial) (fun _ => ?_)
  rw [if_neg hTAC]
  refine okAll_liftME (Q := NilArch) ?_ fun _ h => h
  unfold archDecodeInvocation; dsimp only
  exact okAll_pageDecode hGA

theorem okAll_specDec_domain (fp : Bool) (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    OkAll NilInv (specDec fp slbl args ci sl .Domain excaps buffer) := by
  unfold specDec fl4DecodeInvocation
  simp only [absCap]
  exact okAll_ite (fun _ => okAll_throw) (fun _ => okAll_liftME (okAll_true _) fun _ _ => trivial)

/-! The VSpace and domain caps of the `DecOKDM` producers (VsDomF, TopMCaps). -/

theorem okAll_specDec_pageTable (fp : Bool) (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (p : U64) (m : Bool) (asid va : U64) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    OkAll NilInv (specDec fp slbl args ci sl (.PageTable p m asid va) excaps buffer) :=
  okAll_specDec_arch fp slbl args ci sl excaps buffer rfl (fun _ _ _ _ _ _ h => by cases h)
    (fun _ _ h => by cases h) (fun h => by cases h)

theorem okAll_specDec_pageDirectory (fp : Bool) (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (p : U64) (m : Bool) (asid va : U64) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    OkAll NilInv (specDec fp slbl args ci sl (.PageDirectory p m asid va) excaps buffer) :=
  okAll_specDec_arch fp slbl args ci sl excaps buffer rfl (fun _ _ _ _ _ _ h => by cases h)
    (fun _ _ h => by cases h) (fun h => by cases h)

theorem okAll_specDec_pdpt (fp : Bool) (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (p : U64) (m : Bool) (asid va : U64) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    OkAll NilInv (specDec fp slbl args ci sl (.Pdpt p m asid va) excaps buffer) :=
  okAll_specDec_arch fp slbl args ci sl excaps buffer rfl (fun _ _ _ _ _ _ h => by cases h)
    (fun _ _ h => by cases h) (fun h => by cases h)

theorem okAll_specDec_pml4 (fp : Bool) (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (p : U64) (m : Bool) (asid : U64) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    OkAll NilInv (specDec fp slbl args ci sl (.Pml4 p m asid) excaps buffer) :=
  okAll_specDec_arch fp slbl args ci sl excaps buffer rfl (fun _ _ _ _ _ _ h => by cases h)
    (fun _ _ h => by cases h) (fun h => by cases h)

theorem okAll_specDec_asidControl (fp : Bool) (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    OkAll NilInv (specDec fp slbl args ci sl .AsidControl excaps buffer) :=
  okAll_specDec_arch fp slbl args ci sl excaps buffer rfl (fun _ _ _ _ _ _ h => by cases h)
    (fun _ _ h => by cases h) (fun h => by cases h)

theorem okAll_specDec_asidPool (fp : Bool) (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (p base : U64) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    OkAll NilInv (specDec fp slbl args ci sl (.AsidPool p base) excaps buffer) :=
  okAll_specDec_arch fp slbl args ci sl excaps buffer rfl (fun _ _ _ _ _ _ h => by cases h)
    (fun _ _ h => by cases h) (fun h => by cases h)

/-- A frame cap, its label neither `GetAddress` nor `TestAndClearAccessed`
(those reply in the decode, `DecOKRMX`). -/
theorem okAll_specDec_frameCap (fp : Bool) (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (p : U64) (sz : capability.FrameSize) (r : U64) (d m e : Bool) (asid va : U64)
    (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef)
    (hTAC : dataToNat slbl ≠ fl4TestAndClearLabel)
    (hGA : invocationType slbl ≠ .archInvocationLabel .x64PageGetAddress) :
    OkAll NilInv (specDec fp slbl args ci sl (.Frame p sz r d m e asid va) excaps buffer) :=
  okAll_specDec_frame fp slbl args ci sl excaps buffer rfl hTAC hGA

/-- **A `DecOKDM` producer whose decode gives only `NilInv` invocations**
gives `DecOKDMX` for `X` true. -/
theorem DecOKDM.toX {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] (arI : machine.Arch A)
    {s : S} {ar : A} {σ : State Unit} {lbl length slot : U64} {c : fl4_core.capability.Cap}
    {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array fl4_core.obj.Slot 3#usize} {slbl : Data}
    {args : List Data} {ci : CapRef} {sl : CslotPtr} {excaps : List (Cap × CslotPtr)} {buffer : Option ObjRef}
    (h : DecOKDM (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer)
    (hm : OkAll NilInv (specDec fp slbl args ci sl c excaps buffer)) :
    DecOKDMX (L := L) arI (fun _ _ _ => True) s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl
      excaps buffer :=
  WP.spec_mono h fun _ hr => TopPostDMX.ofDM hr fun _ hd σ1 y hy rr hrr =>
    perform_nil blk call don (hd.okAll hm) σ1 y hy rr hrr

end Nil

end

end Fl4Proofs.P3
