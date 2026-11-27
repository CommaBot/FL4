/-
P3 (issue #16, s26): **l4v `valid_untyped` for device untyped caps**, the
definitions, the split into a cap half and an object half, and the cap
writers (spec side only; outside the `JAtZ` cone). The generalisation of
SpecInvUtZW's `ZR` (g5g) from non-device untyped caps and non-device data
pages to the device untyped caps and every object kind; C26 of INV-PLAN §1.U3L.

* `UtSetD`: a set of device untyped caps `(b, n, f)` (base, size bits, free
  index); `frD b n f` / `rgD b n`: the free part and the region as byte numbers.
* The invariant: `GoodD U O` (every object `(o, k)` of `O` misses the region
  of every cap of `U`, or lies in its used part `[b, b + f)`), `HUD U σ`
  (every device untyped cap of `σ` is a cap `(b, n, f)` of `U` with a free
  index at least `f`, or full) and the object half `OIn O σ` of SpecInvDvK1
  (every object of `σ`, with its `objBits`, is in `O`). **`ZSD U O σ`** is
  their conjunction, **`ZD σ := ∃ U O, ZSD U O σ`** the carried invariant;
  `zd_iff : ZD σ ↔ DevRangeS σ` (the concrete statement).
* The split: `HUD U` reads only the caps (a `WLH` predicate, vih2's frames
  keep it); the object half is the `OBK` family. `ik_zd`: a function keeping
  every `HUD U` and every `OIn O` keeps `ZD`.
* `HUD U` leaves, as `hv_leaf` rules (SpecInvUtZW's `HU` leaves with the
  device flag): `set_cap` of an `UtInD U` cap, `set_untyped_cap_as_full`,
  `cap_insert` / `cap_move` / `cap_swap`, `cap_swap_for_delete`,
  `retype_region`, `delete_objects`.
-/
import Fl4Proofs.P3.SpecInvDvK6
import Fl4Proofs.P3.SpecInvValidIrqHandlersS
open Classical

namespace Fl4Proofs.P3.SInvDV
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The invariant -/

/-- A set of device untyped caps (base, size bits, free index). -/
abbrev UtSetD := ObjRef → Nat → Nat → Prop

/-- An object `(o, k)` misses the region of the cap `(b, n, f)` or lies in its used part
`[b, b + min f 2^n)` (the free index is at most the size in every reachable state, SpecInvUt's `UtWf`;
the `min` lets a full cap's record stand for any larger index). -/
def InUsed (b : ObjRef) (n f : Nat) (o : ObjRef) (k : Nat) : Prop :=
  (o.toNat + 2 ^ k ≤ b.toNat ∨ b.toNat + 2 ^ n ≤ o.toNat) ∨
    (b.toNat ≤ o.toNat ∧ o.toNat + 2 ^ k ≤ b.toNat + min f (2 ^ n))

/-- A cap that may be written: a device untyped cap is a cap of `U` with a
larger free index, or full. -/
def UtInD (U : UtSetD) (c : Cap) : Prop :=
  ∀ b n f, c = .untypedCap true b n f → ∃ f0, U b n f0 ∧ (f0 ≤ f ∨ 2 ^ n ≤ f)

/-- **The cap half**: every cap of `σ` is `UtInD U`. -/
def HUD (U : UtSetD) (σ : State Unit) : Prop :=
  ∀ p cref c, capOpt (σ.kheap p) cref = some c → UtInD U c

/-- **l4v `valid_untyped` for device caps** (pure): every object of `O` misses
the region of every cap of `U` or lies in its used part. -/
def GoodD (U : UtSetD) (O : ObSet) : Prop := ∀ b n f, U b n f → ∀ o k, O o k → InUsed b n f o k

/-- The invariant at the sets `U`, `O`. -/
def ZSD (U : UtSetD) (O : ObSet) (σ : State Unit) : Prop := GoodD U O ∧ HUD U σ ∧ OIn O σ

/-- **The carried invariant** (module docstring). -/
def ZD (σ : State Unit) : Prop := ∃ U O, ZSD U O σ

/-- **[J] spec, C26 of INV-PLAN §1.U3L** (l4v `valid_untyped` for device
untyped caps): every object of the heap misses the region of every device
untyped cap or lies in its used part `[b, b + min f 2^n)` (no object in a
device cap's free part, none straddling its region). -/
def DevRangeS (σ : State Unit) : Prop :=
  ∀ p cref b n f, capOpt (σ.kheap p) cref = some (.untypedCap true b n f) →
    ∀ o ko, σ.kheap o = some ko → InUsed b n f o (objBits ko)

/-- The caps of a state. -/
def HasUD (σ : State Unit) : UtSetD := fun b n f => ∃ p cref, capOpt (σ.kheap p) cref = some (.untypedCap true b n f)

/-- The objects of a state. -/
def ObOf (σ : State Unit) : ObSet := fun o k => ∃ ko, σ.kheap o = some ko ∧ k = objBits ko

theorem inUsed_mono {b : ObjRef} {n f0 f : Nat} (h : f0 ≤ f ∨ 2 ^ n ≤ f) {o : ObjRef} {k : Nat}
    (hu : InUsed b n f0 o k) : InUsed b n f o k := by
  unfold InUsed at *
  rcases hu with hu | ⟨h1, h2⟩
  · exact Or.inl hu
  · rcases h with h | h
    · exact Or.inr ⟨h1, by omega⟩
    · exact Or.inr ⟨h1, by omega⟩

theorem zsd_canon {σ : State Unit} (h : DevRangeS σ) : ZSD (HasUD σ) (ObOf σ) σ := by
  refine ⟨?_, ?_, fun o ko h => ⟨ko, h, rfl⟩⟩
  · rintro b n f ⟨p, cref, hc⟩ o k ⟨ko, ho, rfl⟩
    exact h p cref b n f hc o ko ho
  · intro p cref c hc b n f e
    subst e
    exact ⟨f, ⟨p, cref, hc⟩, Or.inl le_rfl⟩

theorem zd_iff {σ : State Unit} : ZD σ ↔ DevRangeS σ := by
  constructor
  · rintro ⟨U, O, hG, hH, hO⟩ p cref b n f hc o ko ho
    obtain ⟨f0, hU, hf⟩ := hH p cref _ hc b n f rfl
    exact inUsed_mono hf (hG b n f0 hU o _ (hO o ko ho))
  · intro h; exact ⟨_, _, zsd_canon h⟩

variable {U : UtSetD} {σ σ' : State Unit}

theorem utInD_noUt {c : Cap} (h : ∀ b n f, c ≠ .untypedCap true b n f) (U : UtSetD) : UtInD U c :=
  fun b n f e => absurd e (h b n f)

theorem utInD_of_slot (h : HUD U σ) {p : ObjRef} {r : CnodeIndex} {c : Cap}
    (hc : capOpt (σ.kheap p) r = some c) : UtInD U c := h p r c hc

instance (U : UtSetD) : WLH (HUD U) :=
  wlh_of_hV fun _ _ e h p cref c hc => h p cref c (by rw [← hV_cap e]; exact hc)

theorem hd_of_hV (e : hV σ' = hV σ) (h : HUD U σ) : HUD U σ' :=
  fun p cref c hc => h p cref c (by rw [← hV_cap e]; exact hc)

/-! ## The split -/

/-- **Keeping every `HUD U` and every `OIn O` keeps `ZD`.** -/
theorem ik_zd {α : Type} {m : NonDet (State Unit) α} (hH : ∀ U, IKH (HUD U) m) (hY : ∀ O, OBK O m) :
    IKH ZD m := by
  rintro σ ⟨U, O, hG, hU, hP⟩ x hx
  exact ⟨U, O, hG, hH U σ hU x hx, hY O σ hP x hx⟩

theorem ike_zd {ε α : Type} {m : NonDetE (State Unit) ε α} (hH : ∀ U, IKHE (HUD U) m) (hY : ∀ O, OBKE O m) :
    IKHE ZD m :=
  ik_zd (m := ExceptT.run m) hH hY

/-- `IKp` of `ZSD U O` from the cap half and the object half pinned at a state. -/
theorem ikp_zsd {O : ObSet} {α : Type} {m : NonDet (State Unit) α} (hH : IKp (HUD U) σ m)
    (hY : IKp (OIn O) σ m) : IKp (ZSD U O) σ m :=
  fun h x hx => ⟨h.1, hH h.2.1 x hx, hY h.2.2 x hx⟩

/-! ## `set_cap` and the cap writers (`HUD U`) -/

/-- Side conditions `UtInD U c`. -/
macro "utd_side" : tactic => `(tactic| first
  | assumption
  | (intro _ _ _ h; cases h; done)
  | exact utInD_noUt (fun _ _ _ h => by cases h) _
  | (intro _ _ _ h; simp_all; done))

theorem hd_setCap_p (c : Cap) (sl : CslotPtr) (σ : State Unit) (hc : HUD U σ → UtInD U c) :
    IKp (HUD U) σ (setCap (Z := Unit) c sl) := by
  intro h x hx
  obtain ⟨o, r⟩ := sl
  intro p cref a hp
  rcases (vih_setCap_out hx).2 p cref _ hp with ⟨-, -, e⟩ | ⟨-, h0⟩
  · subst e; exact hc h
  · exact h p cref a h0

theorem hd_setCap (c : Cap) (sl : CslotPtr) (hc : UtInD U c) : IKH (HUD U) (setCap (Z := Unit) c sl) :=
  fun σ => hd_setCap_p c sl σ fun _ => hc

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine hd_setCap _ _ ?_); utd_side))

/-- The free index raised to the maximum. -/
theorem utInD_maxFree {c : Cap} (h : UtInD U c) : UtInD U (maxFreeIndexUpdate c) := by
  intro b n f e
  cases c with
  | untypedCap d b' n' f' =>
    simp only [maxFreeIndexUpdate, freeIndexUpdate, untypedSzBits, maxFreeIndex, Cap.untypedCap.injEq] at e
    obtain ⟨e1, e2, e3, e4⟩ := e
    cases e1; cases e2; cases e3; cases e4
    obtain ⟨f0, hU, -⟩ := h _ _ f' rfl
    exact ⟨f0, hU, Or.inr le_rfl⟩
  | _ => simp [maxFreeIndexUpdate, freeIndexUpdate] at e

theorem hd_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : CslotPtr) (hs : UtInD U srcCap) :
    IKH (HUD U) (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull
  split
  · exact hd_setCap _ _ (utInD_maxFree hs)
  · exact ik_pure _

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine hd_setUntypedCapAsFull _ _ _ ?_); utd_side))

/-- `cap_insert` re-reads its source cap: `set_untyped_cap_as_full` writes it back full. -/
theorem hd_capInsert (c : Cap) (src dst : CslotPtr) (hc : UtInD U c) :
    IKH (HUD U) (capInsert (Z := Unit) c src dst) := by
  unfold capInsert
  refine ik_getCap_bind fun sc σ hs h => ?_
  have hsc : UtInD U sc := utInD_of_slot h hs
  refine ikp_of_ik ?_ σ h
  hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine hd_capInsert _ _ _ ?_); utd_side))

theorem hd_capMove (c : Cap) (src dst : CslotPtr) (hc : UtInD U c) :
    IKH (HUD U) (capMove (Z := Unit) c src dst) := by
  unfold capMove; hv_auto

theorem hd_capSwap (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) (hc1 : UtInD U c1) (hc2 : UtInD U c2) :
    IKH (HUD U) (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine hd_capMove _ _ _ ?_); utd_side))
macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine hd_capSwap _ _ _ _ ?_ ?_) <;> utd_side))

theorem hd_capSwapForDelete (s1 s2 : CslotPtr) : IKH (HUD U) (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete
  refine ik_when _ (ik_getCap_bind fun c1 σ h1 => ikp_getCap_bind fun c2 h2 hσ => ?_)
  exact hd_capSwap c1 s1 c2 s2 (utInD_of_slot hσ h1) (utInD_of_slot hσ h2) σ hσ

theorem capOpt_default_noUtD {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (n : Nat) (d : Domain)
    (cref : CnodeIndex) (b : ObjRef) (m f : Nat) :
    capOpt (some (defaultObject ty dev n d)) cref ≠ some (.untypedCap true b m f) := by
  intro h
  cases ty with
  | untyped => exact hty rfl
  | capTableObject =>
    simp only [defaultObject, capOpt] at h
    split_ifs at h with h1
    simp only [emptyCnode] at h
    split_ifs at h with h2
    cases h
  | tcbObject =>
    simp only [defaultObject, capOpt, tcbCnodeMap, defaultTcb, Function.update_apply] at h
    split_ifs at h <;> cases h
  | archObject a => simp only [defaultObject, capOpt] at h; cases h
  | _ => simp only [defaultObject, capOpt] at h; cases h

theorem hd_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType)
    (dev : Bool) : IKH (HUD U) (retypeRegionWith (Z := Unit) bA ptr n oB ty dev) := by
  intro σ h y hy p cref c hc
  rcases (SInvU.retypeRegionWith_out hy).2 with e' | ⟨hty, e'⟩
  · rw [e'] at hc; exact h p cref c hc
  · rw [e'] at hc
    simp only [SInvU.retKh] at hc
    split_ifs at hc
    · intro b m f e; subst e; exact absurd hc (capOpt_default_noUtD hty _ _ _ _ _ _ _)
    · exact h p cref c hc

theorem hd_retypeRegion (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType) (dev : Bool) :
    IKH (HUD U) (retypeRegion (Z := Unit) ptr n oB ty dev) := by
  rw [← retypeRegionWith_objBitsApi]; exact hd_retypeRegionWith _ _ _ _ _ _

theorem hd_deleteObjects (ptr : Word) (bits : Nat) : IKH (HUD U) (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  refine ik_bind (WLH.msk _ (mt_freeMemory _ _)) fun _ => ik_modify fun σ h => ?_
  intro p cref c hc
  simp only [detype] at hc
  split_ifs at hc
  · simp [capOpt] at hc
  · exact h p cref c hc

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_retypeRegionWith _ _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_retypeRegion _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_deleteObjects _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_capSwapForDelete _ _)

end

end Fl4Proofs.P3.SInvDV
