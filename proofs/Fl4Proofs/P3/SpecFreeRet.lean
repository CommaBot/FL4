/-
P3: **the spec's untyped invocation on the heap** (for `SpecFree` across
retype, l4v `valid_untyped`).

* `NAll`: every outcome satisfies a predicate (no claim about failure).
* `reset_avoid`: every outcome of `reset_untyped_cap` on an untyped cap
  with a nonzero free index has no object starting in the cap's region
  (`delete_objects`, and only `KSz` steps after it).
* `invokeUntyped_kheap`: every object after `invoke_untyped` is an old
  object of the same type (not starting in the source cap's region when
  the invocation resets a used cap), or one of the new objects
  (`regionPtrs`), of the type `default_object` gives.
-/
import Fl4Proofs.P3.SpecKSz
import Fl4Proofs.P3.UntypedResetRefine
import Fl4Proofs.P3.UntypedLoop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open Fl4Spec

noncomputable section

section
variable {σ α β ε : Type}

/-- Every outcome from `s` satisfies `P`. -/
def NAll (m : NonDet σ α) (s : σ) (P : α × σ → Prop) : Prop := ∀ x ∈ (m s).1, P x

theorem NAll.mono {m : NonDet σ α} {s : σ} {P Q : α × σ → Prop} (h : NAll m s P) (hq : ∀ x, P x → Q x) :
    NAll m s Q := fun x hx => hq x (h x hx)

theorem nall_bind {m : NonDet σ α} {f : α → NonDet σ β} {s : σ} {P : β × σ → Prop}
    (h : NAll m s (fun x => NAll (f x.1) x.2 P)) : NAll (m >>= f) s P := by
  rintro r ⟨x, hx, hr⟩; exact h x hx r hr

theorem nall_det {m : NonDet σ α} {s s' : σ} {a : α} {X : Prop} {P : α × σ → Prop} (h : m s = ({(a, s')}, X))
    (hP : P (a, s')) : NAll m s P := by
  intro x hx; rw [h] at hx; rw [Set.mem_singleton_iff.1 hx]; exact hP

theorem nall_pure {a : α} {s : σ} {P : α × σ → Prop} (hP : P (a, s)) : NAll (NonDet.pure a) s P :=
  nall_det rfl hP

theorem nallE_bind {m : NonDetE σ ε α} {f : α → NonDetE σ ε β} {s : σ} {P : Except ε β × σ → Prop}
    (h : NAll m.run s (fun x => match x.1 with
      | .ok a => NAll (f a).run x.2 P
      | .error e => P (.error e, x.2))) : NAll (m >>= f).run s P := by
  rw [ExceptT.run_bind]
  apply nall_bind
  intro x hx
  have := h x hx
  rcases x with ⟨e | a, s1⟩
  · exact nall_det rfl this
  · exact this

theorem nall_liftE {m : NonDet σ α} {s : σ} {P : Except ε α × σ → Prop} (h : NAll m s (fun x => P (.ok x.1, x.2))) :
    NAll (NonDetE.liftE (ε := ε) m).run s P := by
  rw [liftE_run]; exact nall_bind (h.mono fun x hx => nall_pure hx)

end

theorem NKZ.nall {α : Type} {m : NonDet (State Unit) α} (h : NKZ m) (s : State Unit) :
    NAll m s (fun x => KSz s x.2) := fun x hx => h s x hx

theorem NKZE.nall {ε α : Type} {m : NonDetE (State Unit) ε α} (h : NKZE m) (s : State Unit) :
    NAll m.run s (fun x => KSz s x.2) := fun x hx => h s x hx

/-! ## The reset -/

theorem nkze_mapMEx {ε α β : Type} {f : α → NonDetE (State Unit) ε β} (hf : ∀ a, NKZE (f a)) :
    ∀ l : List α, NKZE (NonDetE.mapMEx f l)
  | [] => nkze_pure _
  | a :: l => nkze_bind (hf a) (fun _ => nkze_mapMEx hf l)

theorem nkz_clearMemory (a : Word) (n : Nat) : NKZ (doMachineOp (Z := Unit) (clearMemory a n)) := nkz_doMachineOp _

/-- What follows `delete_objects` in the reset keeps `KSz`. -/
macro "nkze_reset_tail" : tactic => `(tactic| (
  try dsimp only
  apply nkze_ite
  · refine nkze_bind (nkze_liftE (nkz_bind (nkz_unless (nkz_doMachineOp _)) (fun _ => nkz_setCap _ _))) (fun _ => ?_)
    unfold archPostResetUntyped; exact nkze_liftE (nkz_pure _)
  · refine nkze_bind (nkze_mapMEx (fun i => ?_) _) (fun _ => ?_)
    · exact nkze_bind (nkze_liftE (nkz_doMachineOp _)) (fun _ =>
        nkze_bind (nkze_liftE (nkz_setCap _ _)) (fun _ => nkze_preemptionPoint))
    · unfold archPostResetUntyped; exact nkze_liftE (nkz_pure _)))

/-- **The reset keeps `KSz`.** -/
theorem nkze_resetUntypedCap (sl : CslotPtr) : NKZE (resetUntypedCap (Z := Unit) sl) := by
  unfold resetUntypedCap
  refine nkze_bind (nkze_liftE (nkz_getCap _)) (fun cap => ?_)
  refine nkze_bind (nkze_returnOk _) (fun _ => nkze_bind (nkze_returnOk _) (fun _ => ?_))
  refine nkze_ite _ (nkze_returnOk _) ?_
  refine nkze_bind (nkze_liftE (nkz_deleteObjects _ _)) (fun _ => nkze_bind (nkze_returnOk _) (fun _ => ?_))
  nkze_reset_tail

/-- No object starts in the region. -/
def AvoidS (R : Set ObjRef) (σ : State Unit) : Prop := ∀ o ∈ R, σ.kheap o = none

theorem AvoidS.ksz {R : Set ObjRef} {σ σ' : State Unit} (h : AvoidS R σ) (hk : KSz σ σ') : AvoidS R σ' := by
  intro o ho
  cases e : σ'.kheap o with
  | none => rfl
  | some ko' =>
    obtain ⟨ko, hko, -⟩ := hk o ko' e
    rw [h o ho] at hko; cases hko

/-- **The reset of a used untyped cap empties its region**, on every
outcome (preempted ones included). -/
theorem reset_avoid {sl : CslotPtr} {σ : State Unit} {dev : Bool} {pu : ObjRef} {sz fi : Nat}
    (hg : getCap (Z := Unit) sl σ = ({(.untypedCap dev pu sz fi, σ)}, False)) (hfi : fi ≠ 0) :
    NAll (resetUntypedCap (Z := Unit) sl).run σ (fun y => AvoidS (regionSet pu sz) y.2) := by
  unfold resetUntypedCap
  apply nallE_bind
  refine nall_det (run_liftE hg) ?_
  dsimp only
  simp only [NonDetE.returnOk, ndE_pure_bind, Fl4Spec.bitsOf, Fl4Spec.objRefOf, Fl4Spec.freeIndexOf,
    Fl4Spec.isDeviceUntypedCap, hfi, ↓reduceIte]
  apply nallE_bind
  apply nall_liftE
  intro y hy
  have hD : AvoidS (regionSet pu sz) y.2 := by
    unfold deleteObjects at hy
    obtain ⟨z, -, hz⟩ := hy
    rw [Set.mem_singleton_iff.1 hz]
    intro o ho
    simp only [detype]
    split_ifs with h
    · rfl
    · exact absurd ho h
  dsimp only
  refine NAll.mono (P := fun x => KSz y.2 x.2) ?_ (fun x hx => by rcases x with ⟨e | u, s1⟩ <;> exact hD.ksz hx)
  apply NKZE.nall
  nkze_reset_tail

/-! ## The invocation -/

/-- What an object after `invoke_untyped` is: an old object of the same type
(not starting in `R`), or a new one. -/
def RetKh (bitsApi : ApiObjectType → Nat → Nat) (σ σ' : State Unit) (R : Set ObjRef) (rb : ObjRef)
    (t : ApiObjectType) (us : Nat) (n : Nat) (dev : Bool) : Prop :=
  ∀ o ko', σ'.kheap o = some ko' →
    (∃ ko, σ.kheap o = some ko ∧ aType ko = aType ko' ∧ o ∉ R) ∨
    (t ≠ .untyped ∧ o ∈ regionPtrs rb n (2 ^ bitsApi t us) ∧ ∃ cd, aType ko' = aType (defaultObject t dev us cd))

theorem RetKh.ksz {bitsApi : ApiObjectType → Nat → Nat} {σ σ1 σ2 : State Unit} {R : Set ObjRef} {rb : ObjRef}
    {t : ApiObjectType} {us n : Nat} {dev : Bool} (h : RetKh bitsApi σ σ1 R rb t us n dev) (hk : KSz σ1 σ2) :
    RetKh bitsApi σ σ2 R rb t us n dev := by
  intro o ko2 h2
  obtain ⟨ko1, h1, e1⟩ := hk o ko2 h2
  rcases h o ko1 h1 with ⟨ko, h0, e0, hR⟩ | ⟨ht, hm, cd, e⟩
  · exact Or.inl ⟨ko, h0, e0.trans e1, hR⟩
  · exact Or.inr ⟨ht, hm, cd, e1.symm.trans e⟩

/-- The retype after the reset: old objects of the same type, or new. -/
theorem retype_body_kh (bitsApi : ApiObjectType → Nat → Nat) (sl : CslotPtr) (base rb : ObjRef)
    (t : ApiObjectType) (us : Nat) (slots : List CslotPtr) (dev : Bool) (σ : State Unit) :
    NAll (NonDetE.liftE (ε := Unit) (do
      let cap ← getCap (Z := Unit) sl
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< bitsApi t us)
      let freeRef ← pure (rb + totalObjectSize)
      setCap (.untypedCap dev base (Fl4Spec.bitsOf cap) (unat (freeRef - base))) sl
      let orefs ← retypeRegionWith bitsApi rb slots.length us t dev
      initArchObjects t dev rb slots.length us orefs
      NonDet.mapMx (createCap t us sl dev) (slots.zip orefs))).run σ
      (fun y => y.1 = .ok () ∧ RetKh bitsApi σ y.2 ∅ rb t us slots.length dev) := by
  apply nall_liftE
  apply nall_bind
  refine ((nkz_getCap sl).nall σ).mono (fun x hx => ?_)
  apply nall_bind; refine nall_det rfl ?_
  apply nall_bind; refine nall_det rfl ?_
  apply nall_bind
  refine ((nkz_setCap _ sl).nall _).mono (fun x2 hx2 => ?_)
  have h01 := hx.trans hx2
  apply nall_bind
  refine nall_det (retypeRegionWith_eq bitsApi rb slots.length us t dev x2.2) ?_
  apply nall_bind
  refine ((nkz_initArchObjects _ _ _ _ _ _).nall _).mono (fun x3 hx3 => ?_)
  refine ((nkz_mapMx (fun a => nkz_createCap t us sl dev a) _).nall _).mono (fun x4 hx4 => ?_)
  refine ⟨rfl, RetKh.ksz ?_ (hx3.trans hx4)⟩
  intro o ko' hk
  dsimp only at hk
  split_ifs at hk with ht
  · simp only [regionHeap] at hk
    rw [foldr_update_apply] at hk
    split_ifs at hk with hm
    · cases hk; exact Or.inr ⟨ht, hm, _, rfl⟩
    · obtain ⟨ko, h0, e0⟩ := h01 o ko' hk
      exact Or.inl ⟨ko, h0, e0, fun h => h⟩
  · obtain ⟨ko, h0, e0⟩ := h01 o ko' hk
    exact Or.inl ⟨ko, h0, e0, fun h => h⟩

/-- **Every object after `invoke_untyped`** is an old object of the same
type, not starting in the source cap's region if the invocation resets the
cap with a nonzero free index, or a new one. -/
theorem invokeUntyped_kheap (bitsApi : ApiObjectType → Nat → Nat) (sl : CslotPtr) (rs : Bool) (base rb : ObjRef)
    (t : ApiObjectType) (us : Nat) (slots : List CslotPtr) (dev : Bool) (σ : State Unit)
    {dv : Bool} {pu : ObjRef} {sz fi : Nat}
    (hg : getCap (Z := Unit) sl σ = ({(.untypedCap dv pu sz fi, σ)}, False)) :
    NAll (invokeUntypedWith (Z := Unit) bitsApi (.retype sl rs base rb t us slots dev)).run σ
      (fun y => (y.1 = .ok () ∨ rs = true) ∧
        RetKh bitsApi σ y.2 (if rs = true ∧ fi ≠ 0 then regionSet pu sz else ∅) rb t us
          (if y.1 = .ok () then slots.length else 0) dev) := by
  have hpre : NAll (NonDetE.whenE (rs = true) (resetUntypedCap (Z := Unit) sl)).run σ
      (fun y => (y.1 = .ok () ∨ rs = true) ∧ KSz σ y.2 ∧ (rs = true ∧ fi ≠ 0 → AvoidS (regionSet pu sz) y.2)) := by
    unfold NonDetE.whenE
    split_ifs with hr
    · intro y hy
      refine ⟨Or.inr hr, (nkze_resetUntypedCap sl).nall σ y hy, fun ⟨_, hf⟩ => reset_avoid hg hf y hy⟩
    · refine nall_det rfl ⟨Or.inl rfl, KSz.refl σ, fun ⟨h, _⟩ => absurd h hr⟩
  -- an old object kept by a `KSz` step, outside the region if it was emptied
  have hold : ∀ σr : State Unit, KSz σ σr → (rs = true ∧ fi ≠ 0 → AvoidS (regionSet pu sz) σr) → ∀ n,
      RetKh bitsApi σ σr (if rs = true ∧ fi ≠ 0 then regionSet pu sz else ∅) rb t us n dev := by
    intro σr hk hA n o ko' ho
    obtain ⟨ko, h0, e0⟩ := hk o ko' ho
    refine Or.inl ⟨ko, h0, e0, fun hR => ?_⟩
    split_ifs at hR with hc
    · rw [hA hc o hR] at ho; cases ho
    · exact hR
  unfold invokeUntypedWith
  apply nallE_bind
  refine hpre.mono (fun x ⟨hrs, hk, hA⟩ => ?_)
  rcases x with ⟨e | u, σr⟩
  · refine ⟨Or.inr ?_, hold σr hk hA _⟩
    rcases hrs with h | h
    · cases h
    · exact h
  · refine (retype_body_kh bitsApi sl base rb t us slots dev σr).mono (fun y ⟨hy1, hy⟩ => ⟨Or.inl hy1, ?_⟩)
    rw [if_pos hy1]
    intro o ko' ho
    rcases hy o ko' ho with ⟨ko1, h1, e1, -⟩ | hn
    · rcases hold σr hk hA slots.length o ko1 h1 with ⟨ko, h0, e0, hR⟩ | ⟨ht, hm, cd, e⟩
      · exact Or.inl ⟨ko, h0, e0.trans e1, hR⟩
      · exact Or.inr ⟨ht, hm, cd, e1.symm.trans e⟩
    · exact Or.inr hn

end

end Fl4Proofs.P3
