/-
P3 (DESIGN.md §9), invariant line G1 (g5g, KENTRY-PLAN g5g): **l4v
`untyped_ranges_zero` with the data-page part of `valid_untyped`**, the
definitions, the split into a cap half and a memory half, and the cap writers
(spec side only; outside the `JAtZ` cone; g5c's SpecInvIoPortsW with untyped
caps for IO-port caps).

* `UtSet`: a set of (non-device) untyped caps `(b, n, f)` (base, size bits,
  free index); `fr b n f` / `rg b n`: the free part `[b + f, b + 2^n)` and the
  region `[b, b + 2^n)`, as byte numbers.
* The invariant: `GoodZ U D` (every page of `D` misses the free part of every
  cap of `U`, and a page meeting the region of a cap of `U` lies inside it:
  l4v `valid_untyped` for data pages), `HU U σ` (every non-device untyped cap
  of `σ` is a cap `(b, n, f)` of `U` with a free index at least `f`, or full),
  and the memory half `YP D (FU U) σ` of SpecInvUtZK1 (the pages of `σ` are in
  `D`, the memory is zero on the free parts `FU U`). **`ZS U D σ`** is their
  conjunction, **`ZR σ := ∃ U D, ZS U D σ`** the carried invariant;
  `zr_iff : ZR σ ↔ SpecUtZ' σ ∧ UtPgR σ` (SpecInvUtZS states it with
  SpecInvG5's `SpecUtZ`).
* The split: `HU U` reads only the caps, so it is a `WLH` predicate (vih2's
  frames SpecInvValidIrqHandlersF1..F4 keep it); the memory half is the `YK`
  family. `ik_zr`: a function keeping every `HU U` and every `YP D F` keeps
  `ZR` (the free parts only shrink, the pages only disappear, the memory stays
  zero on the old free parts).
* `UtIn U c`: if `c` is a non-device untyped cap, it is in `U` (up to a larger
  free index): what a cap about to be written must satisfy (a pure fact).
* `HU U` leaves, as `hv_leaf` rules: `set_cap` of an `UtIn U` cap,
  `set_untyped_cap_as_full` (the free index raised to the maximum),
  `cap_insert` / `cap_move` / `cap_swap` of `UtIn U` caps,
  `cap_swap_for_delete`, `retype_region` (default objects hold only null
  caps), `delete_objects`. `create_cap` writes a default cap, an untyped one
  for an untyped retype: it is the untyped perform's (SpecInvUtZS).
-/
import Fl4Proofs.P3.SpecInvUtZK6
import Fl4Proofs.P3.SpecInvValidIrqHandlersS
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The invariant -/

/-- A set of non-device untyped caps (base, size bits, free index). -/
abbrev UtSet := ObjRef → Nat → Nat → Prop

/-- The free part of an untyped cap, as byte numbers. -/
def fr (b : ObjRef) (n f : Nat) : Set Nat := {a | b.toNat + f ≤ a ∧ a < b.toNat + 2 ^ n}

/-- The region of an untyped cap, as byte numbers. -/
def rg (b : ObjRef) (n : Nat) : Set Nat := {a | b.toNat ≤ a ∧ a < b.toNat + 2 ^ n}

/-- The free parts of the caps of `U`. -/
def FU (U : UtSet) : Set Nat := {a | ∃ b n f, U b n f ∧ a ∈ fr b n f}

/-- A cap that may be written: a non-device untyped cap is a cap of `U` with a
larger free index, or full. -/
def UtIn (U : UtSet) (c : Cap) : Prop :=
  ∀ b n f, c = .untypedCap false b n f → ∃ f0, U b n f0 ∧ (f0 ≤ f ∨ 2 ^ n ≤ f)

/-- **The cap half**: every cap of `σ` is `UtIn U`. -/
def HU (U : UtSet) (σ : State Unit) : Prop :=
  ∀ p cref c, capOpt (σ.kheap p) cref = some c → UtIn U c

/-- **l4v `valid_untyped` for data pages** (pure): every page of `D` misses
the free part of every cap of `U`, and lies inside the region of a cap of `U`
it meets. -/
def GoodZ (U : UtSet) (D : PgSet) : Prop :=
  ∀ b n f, U b n f → ∀ o sz, D o sz →
    (∀ a, a ∈ pgB o sz → a ∉ fr b n f) ∧ ((∃ a, a ∈ pgB o sz ∧ a ∈ rg b n) → ∀ a, a ∈ pgB o sz → a ∈ rg b n)

/-- The invariant at the sets `U`, `D`. -/
def ZS (U : UtSet) (D : PgSet) (σ : State Unit) : Prop := GoodZ U D ∧ HU U σ ∧ YP D (FU U) σ

/-- **The carried invariant** (module docstring). -/
def ZR (σ : State Unit) : Prop := ∃ U D, ZS U D σ

/-- `SpecUtZ` on `capOpt` (SpecInvG5's `SpecUtZ` reads `SInvU.capAt`, the same cap). -/
def SpecUtZ' (σ : State Unit) : Prop :=
  ∀ p cref b n f, capOpt (σ.kheap p) cref = some (.untypedCap false b n f) →
    ∀ a : Word, b.toNat + f ≤ a.toNat → a.toNat < b.toNat + 2 ^ n → σ.machineState.underlyingMemory a = 0

/-- **[J] spec** (l4v `valid_untyped`, restricted to non-device data pages
and non-device untyped caps): a data page misses the free part of every
untyped cap and lies inside the region of every untyped cap it meets. -/
def UtPgR (σ : State Unit) : Prop :=
  ∀ p cref b n f, capOpt (σ.kheap p) cref = some (.untypedCap false b n f) →
    ∀ o sz, σ.kheap o = some (.archObj (.dataPage false sz)) →
      (∀ a, a ∈ pgB o sz → a ∉ fr b n f) ∧ ((∃ a, a ∈ pgB o sz ∧ a ∈ rg b n) → ∀ a, a ∈ pgB o sz → a ∈ rg b n)

/-- The caps of a state. -/
def HasU (σ : State Unit) : UtSet := fun b n f => ∃ p cref, capOpt (σ.kheap p) cref = some (.untypedCap false b n f)

/-- The pages of a state. -/
def PgOf (σ : State Unit) : PgSet := fun o sz => σ.kheap o = some (.archObj (.dataPage false sz))

theorem fr_mono {b : ObjRef} {n f0 f : Nat} (h : f0 ≤ f ∨ 2 ^ n ≤ f) {a : Nat} (ha : a ∈ fr b n f) :
    a ∈ fr b n f0 := by
  obtain ⟨h1, h2⟩ := ha
  rcases h with h | h
  · exact ⟨by omega, h2⟩
  · exact absurd h2 (by omega)

theorem zr_iff {σ : State Unit} : ZR σ ↔ SpecUtZ' σ ∧ UtPgR σ := by
  constructor
  · rintro ⟨U, D, hG, hH, hD, hP, hM⟩
    refine ⟨fun p cref b n f hc a h1 h2 => ?_, fun p cref b n f hc o sz ho => ?_⟩
    · obtain ⟨f0, hU, hf⟩ := hH p cref _ hc b n f rfl
      exact hM a ⟨b, n, f0, hU, fr_mono hf ⟨h1, h2⟩⟩
    · obtain ⟨f0, hU, hf⟩ := hH p cref _ hc b n f rfl
      obtain ⟨g1, g2⟩ := hG b n f0 hU o sz (hP o sz ho)
      exact ⟨fun a ha hfa => g1 a ha (fr_mono hf hfa), g2⟩
  · rintro ⟨hZ, hR⟩
    refine ⟨HasU σ, PgOf σ, ?_, ?_, ?_, fun o sz h => h, ?_⟩
    · rintro b n f ⟨p, cref, hc⟩ o sz ho
      exact hR p cref b n f hc o sz ho
    · intro p cref c hc b n f e
      subst e
      exact ⟨f, ⟨p, cref, hc⟩, Or.inl le_rfl⟩
    · rintro o sz ho a ha ⟨b, n, f, ⟨p, cref, hc⟩, hfa⟩
      exact (hR p cref b n f hc o sz ho).1 a ha hfa
    · rintro a ⟨b, n, f, ⟨p, cref, hc⟩, h1, h2⟩
      exact hZ p cref b n f hc a h1 h2

variable {U : UtSet} {σ σ' : State Unit}

theorem utIn_noUt {c : Cap} (h : ∀ b n f, c ≠ .untypedCap false b n f) (U : UtSet) : UtIn U c :=
  fun b n f e => absurd e (h b n f)

theorem utIn_of_slot (h : HU U σ) {p : ObjRef} {r : CnodeIndex} {c : Cap}
    (hc : capOpt (σ.kheap p) r = some c) : UtIn U c := h p r c hc

instance (U : UtSet) : WLH (HU U) :=
  wlh_of_hV fun _ _ e h p cref c hc => h p cref c (by rw [← hV_cap e]; exact hc)

theorem hu_of_hV (e : hV σ' = hV σ) (h : HU U σ) : HU U σ' :=
  fun p cref c hc => h p cref c (by rw [← hV_cap e]; exact hc)

/-! ## The split -/

/-- **Keeping every `HU U` and every `YP D F` keeps `ZR`.** -/
theorem ik_zr {α : Type} {m : NonDet (State Unit) α} (hH : ∀ U, IKH (HU U) m) (hY : ∀ D F, YK D F m) :
    IKH ZR m := by
  rintro σ ⟨U, D, hG, hU, hP⟩ x hx
  exact ⟨U, D, hG, hH U σ hU x hx, hY D (FU U) σ hP x hx⟩

theorem ike_zr {ε α : Type} {m : NonDetE (State Unit) ε α} (hH : ∀ U, IKHE (HU U) m) (hY : ∀ D F, YKE D F m) :
    IKHE ZR m :=
  ik_zr (m := ExceptT.run m) hH hY

/-- `IKp` of `ZS U D` from the cap half and the memory half pinned at a state. -/
theorem ikp_zs {D : PgSet} {α : Type} {m : NonDet (State Unit) α} (hH : IKp (HU U) σ m)
    (hY : IKp (YP D (FU U)) σ m) : IKp (ZS U D) σ m :=
  fun h x hx => ⟨h.1, hH h.2.1 x hx, hY h.2.2 x hx⟩

/-! ## `set_cap` and the cap writers (`HU U`) -/

/-- Side conditions `UtIn U c`. -/
macro "ut_side" : tactic => `(tactic| first
  | assumption
  | (intro _ _ _ h; cases h; done)
  | exact utIn_noUt (fun _ _ _ h => by cases h) _
  | (intro _ _ _ h; simp_all; done))

theorem hu_setCap_p (c : Cap) (sl : CslotPtr) (σ : State Unit) (hc : HU U σ → UtIn U c) :
    IKp (HU U) σ (setCap (Z := Unit) c sl) := by
  intro h x hx
  obtain ⟨o, r⟩ := sl
  intro p cref a hp
  rcases (vih_setCap_out hx).2 p cref _ hp with ⟨-, -, e⟩ | ⟨-, h0⟩
  · subst e; exact hc h
  · exact h p cref a h0

theorem hu_setCap (c : Cap) (sl : CslotPtr) (hc : UtIn U c) : IKH (HU U) (setCap (Z := Unit) c sl) :=
  fun σ => hu_setCap_p c sl σ fun _ => hc

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine hu_setCap _ _ ?_); ut_side))

/-- The free index raised to the maximum. -/
theorem utIn_maxFree {c : Cap} (h : UtIn U c) : UtIn U (maxFreeIndexUpdate c) := by
  intro b n f e
  cases c with
  | untypedCap d b' n' f' =>
    simp only [maxFreeIndexUpdate, freeIndexUpdate, untypedSzBits, maxFreeIndex, Cap.untypedCap.injEq] at e
    obtain ⟨e1, e2, e3, e4⟩ := e
    cases e1; cases e2; cases e3; cases e4
    obtain ⟨f0, hU, -⟩ := h _ _ f' rfl
    exact ⟨f0, hU, Or.inr le_rfl⟩
  | _ => simp [maxFreeIndexUpdate, freeIndexUpdate] at e

theorem hu_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : CslotPtr) (hs : UtIn U srcCap) :
    IKH (HU U) (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull
  split
  · exact hu_setCap _ _ (utIn_maxFree hs)
  · exact ik_pure _

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine hu_setUntypedCapAsFull _ _ _ ?_); ut_side))

/-- `cap_insert` re-reads its source cap: `set_untyped_cap_as_full` writes it back full. -/
theorem hu_capInsert (c : Cap) (src dst : CslotPtr) (hc : UtIn U c) :
    IKH (HU U) (capInsert (Z := Unit) c src dst) := by
  unfold capInsert
  refine ik_getCap_bind fun sc σ hs h => ?_
  have hsc : UtIn U sc := utIn_of_slot h hs
  refine ikp_of_ik ?_ σ h
  hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine hu_capInsert _ _ _ ?_); ut_side))

theorem hu_capMove (c : Cap) (src dst : CslotPtr) (hc : UtIn U c) :
    IKH (HU U) (capMove (Z := Unit) c src dst) := by
  unfold capMove; hv_auto

theorem hu_capSwap (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) (hc1 : UtIn U c1) (hc2 : UtIn U c2) :
    IKH (HU U) (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine hu_capMove _ _ _ ?_); ut_side))
macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine hu_capSwap _ _ _ _ ?_ ?_) <;> ut_side))

theorem hu_capSwapForDelete (s1 s2 : CslotPtr) : IKH (HU U) (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete
  refine ik_when _ (ik_getCap_bind fun c1 σ h1 => ikp_getCap_bind fun c2 h2 hσ => ?_)
  exact hu_capSwap c1 s1 c2 s2 (utIn_of_slot hσ h1) (utIn_of_slot hσ h2) σ hσ

theorem capOpt_default_noUt {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (n : Nat) (d : Domain)
    (cref : CnodeIndex) (b : ObjRef) (m f : Nat) :
    capOpt (some (defaultObject ty dev n d)) cref ≠ some (.untypedCap false b m f) := by
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

theorem hu_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType)
    (dev : Bool) : IKH (HU U) (retypeRegionWith (Z := Unit) bA ptr n oB ty dev) := by
  intro σ h y hy p cref c hc
  rcases (SInvU.retypeRegionWith_out hy).2 with e' | ⟨hty, e'⟩
  · rw [e'] at hc; exact h p cref c hc
  · rw [e'] at hc
    simp only [SInvU.retKh] at hc
    split_ifs at hc
    · intro b m f e; subst e; exact absurd hc (capOpt_default_noUt hty _ _ _ _ _ _ _)
    · exact h p cref c hc

theorem hu_retypeRegion (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType) (dev : Bool) :
    IKH (HU U) (retypeRegion (Z := Unit) ptr n oB ty dev) := by
  rw [← retypeRegionWith_objBitsApi]; exact hu_retypeRegionWith _ _ _ _ _ _

theorem hu_deleteObjects (ptr : Word) (bits : Nat) : IKH (HU U) (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  refine ik_bind (WLH.msk _ (mt_freeMemory _ _)) fun _ => ik_modify fun σ h => ?_
  intro p cref c hc
  simp only [detype] at hc
  split_ifs at hc
  · simp [capOpt] at hc
  · exact h p cref c hc

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_retypeRegionWith _ _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_retypeRegion _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_deleteObjects _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_capSwapForDelete _ _)

end

end Fl4Proofs.P3.SInvUZ
