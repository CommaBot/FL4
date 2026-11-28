/-
P1 (aarch64, gen 54): **the x86 derivation-tree ghost on the A64 MDB chain and the untyped invariant `UtInvA`**
(Architect decision, option (B): after three same-class finds on the flat chain facts, give A64 x86's
`MdbGhost.par` tree, ghost only, linked to the existing `MdbA64` `NEXT` chain, and port x86 `UtInv` and its step
lemmas instead of re-deriving them; memory side only, nothing coupled to `Fl4Spec`).

* **The tree**: x86 `Fl4Proofs.P3.MdbTree` is memory-free (`Mdb.Desc`, `Mdb.SegOK`, `Mdb.MdbOK` with `insert` /
  `conj` / `remove`) and is imported as is. A64's chain ghost `G` (`MdbLk`) gets a parent map `par` with
  `Mdb.MdbOK par G`: every slot of a chain is followed in it by exactly its descendants.
  Ghost-form bridges: `insA_eq` / `insG_eq` (A64 `insG` = `map (Mdb.insAfter …)`), `remG_eq` (A64 `remG` =
  `Mdb.removeChains`), `swap_eq_swp` / `renG_eq` (A64 `renG` = `map (map (Equiv.swap …))`).
* **Ranges** (x86 CapRange over A64's `ptrA` / `sizeA`): `baseA`, `topA`, `WithinA`, `DisjA`, `DisjRA`; `mskA_val`,
  `ut_rangeA` (x86 `ut_range`), `capA_ut_b` (an `Untyped` slot's size bits `< 64`, from `EncWf`).
* **`UtInvA st OS par s`** (x86 `UtInv`, l4v `untyped_inc` / `caps_no_overlap` / the range part of `valid_cap`):
  `reg` (physical ranges do not wrap), `inc` (descendants of an untyped cap lie in it, below its free index),
  `noov` (a physical cap meeting an untyped cap's free part is an untyped cap containing it), `excl` (of two untyped
  caps of one region, one is full), `fib` (free index `≤ 2^b`), `drange` (an untyped cap and a physical cap whose
  ranges meet are ancestor / descendant), and **`anc`**: ancestors of an untyped cap are untyped — x86 derives this
  (`MdbInv.anc_ut`) from `MdbInv.desc` (the tree is `is_mdb_parent_of`'s), which A64 does not carry; here it is a
  field, kept by every step (seL4: only untyped caps have untyped children).
* `TreeA st OS G par s` = `MdbLk ∧ Mdb.MdbOK par G ∧ UtInvA`; `MdbTU` its `∃ G par`. Boot: `TreeA.empty`.
* `UA d c` (x86 `UtEq`, with the free index allowed to grow: `set_untyped_cap_as_full`) and `FullA.ua`.
* Data-level steps, each mirroring an x86 lemma: **`UtInvA.ren`** (x86 `UtInv.rename`; caps and tree renamed by any
  permutation of `OS`: swap, move), `UtInvA.recap` (x86 `UtInv.of_alike` / `raise_fi`; the identity renaming:
  in-place `set_cap` of an alike cap, the free index raised), **`UtInvA.rem`** (x86 `UtInv.remove`: `empty_slot`),
  **`UtInvA.ins`** (x86 `InsCtx.utinv` at `b = true`: `insert_with_cap`, the new slot `src`'s child, the source made
  full when the copy is an `Untyped` of its region, `hut`: an untyped source has no descendants — `derive_cap`'s
  `ensure_no_children`).
* **Corollaries (the gen-53 flat facts)**: `UtInvA.freeFresh` (`FreeFresh` from `noov` + `reg`),
  **`TreeA.utRangeOrd`** (`UtRangeOrd` from the tree: `drange` + `anc` put a key cap of `u`'s region below `u`,
  `SegOK` puts it in `u`'s block, `inc` puts the block in the region, `MdbLk.chain` gives the `NEXT` path),
  `MdbTU.flat`; **`cdt.ensure_no_children.noDesc`** (`Ok` at a revocable `Untyped` slot ⇒ no descendants: the first
  descendant would be `NEXT u`, in `u`'s region).

No named premise; new definitions and theorems only. `RngOneA64` / `KindA` / `UtRev` are untouched (side by side).
-/
import Fl4ProofsA64.P1.MdbUt
import Fl4Proofs.P3.MdbTree
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-! ## Ghost forms -/

theorem insA_eq (src dest : U64) : ∀ c : List U64, insA src dest c = Mdb.insAfter src dest c
  | [] => rfl
  | a :: l => by simp only [insA, Mdb.insAfter, insA_eq src dest l]

theorem insG_eq (src dest : U64) (G : List (List U64)) : insG src dest G = G.map (Mdb.insAfter src dest) := by
  have : insA src dest = Mdb.insAfter src dest := funext (insA_eq src dest)
  unfold insG; rw [this]

/-- `List.erase` does not depend on which lawful `BEq` instance it uses (A64's `remG` and x86's
`Mdb.removeChains` elaborate `erase` at different instances). -/
theorem erase_inst {α : Type} (i1 i2 : BEq α) [h1 : @LawfulBEq α i1] [h2 : @LawfulBEq α i2] (l : List α) (x : α) :
    @List.erase α i1 l x = @List.erase α i2 l x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a = x
    · subst h
      have e1 : @BEq.beq α i1 a a = true := @beq_self_eq_true α i1 _ a
      have e2 : @BEq.beq α i2 a a = true := @beq_self_eq_true α i2 _ a
      simp only [List.erase, e1, e2]
    · have e1 : @BEq.beq α i1 a x = false := by
        cases hb : @BEq.beq α i1 a x
        · rfl
        · exact absurd (@LawfulBEq.eq_of_beq α i1 h1 a x hb) h
      have e2 : @BEq.beq α i2 a x = false := by
        cases hb : @BEq.beq α i2 a x
        · rfl
        · exact absurd (@LawfulBEq.eq_of_beq α i2 h2 a x hb) h
      simp only [List.erase, e1, e2, ih]

theorem remG_eq (x : U64) : ∀ G : List (List U64), remG x G = Mdb.removeChains x G
  | [] => rfl
  | c :: G => by
    rw [remG, remG_eq x G]
    unfold Mdb.removeChains
    rw [List.map_cons]
    by_cases h : c.erase x = []
    · have h' : @List.erase U64 instBEqOfDecidableEq c x = [] := (erase_inst instBEqOfDecidableEq _ c x).trans h
      rw [if_pos h, h']
      simp only [List.filter_cons, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · rw [if_neg h]
      obtain ⟨a, l, hal⟩ : ∃ a l, c.erase x = a :: l := by
        cases e : c.erase x with
        | nil => exact absurd e h
        | cons a l => exact ⟨a, l, rfl⟩
      have hal' : @List.erase U64 instBEqOfDecidableEq c x = a :: l := (erase_inst instBEqOfDecidableEq _ c x).trans hal
      rw [hal, hal']
      simp only [List.filter_cons, List.isEmpty_cons, Bool.not_false, ↓reduceIte]

theorem swap_eq_swp (x1 x2 y : U64) : Equiv.swap x1 x2 y = swp x1 x2 y := by
  rw [Equiv.swap_apply_def]; rfl

theorem renG_eq (x1 x2 : U64) (G : List (List U64)) :
    renG x1 x2 G = G.map (List.map (Equiv.swap x1 x2)) := by
  have : swp x1 x2 = ⇑(Equiv.swap x1 x2) := funext fun y => (swap_eq_swp x1 x2 y).symm
  unfold renG; rw [this]

theorem conjPar_refl (par : U64 → Option U64) : Mdb.conjPar (Equiv.refl U64) par = par := by
  funext x; simp [Mdb.conjPar]

/-! ## Ranges -/

/-- A cap's base, as a number (x86 `baseF`). -/
noncomputable def baseA (c : capability.Cap) : Nat := (ptrA c).val
/-- A cap's last byte, as a number (x86 `topF`). -/
noncomputable def topA (c : capability.Cap) : Nat := (wa (ptrA c) (mskA (sizeA c))).val

def WithinA (b a : capability.Cap) : Prop := baseA a ≤ baseA b ∧ topA b ≤ topA a
def DisjA (a b : capability.Cap) : Prop := topA a < baseA b ∨ topA b < baseA a
def DisjRA (c : capability.Cap) (lo hi : Nat) : Prop := topA c < lo ∨ hi ≤ baseA c

theorem mskA_val {b : U64} (hb : b.val < 64) : (mskA b).val = 2 ^ b.val - 1 := by
  have h : objects.mask b ⦃ m => m.val = 2 ^ b.val - 1 ⦄ := by
    unfold objects.mask
    have hn : ¬ (b >= 64#u64) := fun h => by
      have h' : (64#u64 : U64).val ≤ b.val := h
      simp at h'; omega
    rw [if_neg hn]
    simp only [lift, bind_ok]
    refine WP.spec_bind (shl1_val hb) fun z hz => ?_
    rw [WP.spec_ok]
    have h1 : 1 ≤ 2 ^ b.val := Nat.one_le_two_pow
    have h2 : 2 ^ b.val < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hb
    simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits, hz]
    omega
  rw [mskA_eq, WP.spec_ok] at h; exact h

theorem wa_val (x y : U64) : (wa x y).val = (x.val + y.val) % 2 ^ 64 := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]

/-- An `Untyped` slot's size bits are below 64 (every decoded cap is `EncWf`). -/
theorem capA_ut_b {s : S} {x p b i : U64} {d : Bool} (h : capA st s x = .Untyped p b i d) : b.val < 64 := by
  have w := CapRt.decodeF_encWf (L.mem s x).bv (L.mem s (wa x 8#u64)).bv
  have e : CapRt.decodeF (L.mem s x).bv (L.mem s (wa x 8#u64)).bv = .Untyped p b i d := h
  rw [e] at w; exact w.2

/-- **An untyped cap's range**, when it does not wrap (x86 `ut_range`). -/
theorem ut_rangeA {p b i : U64} {d : Bool} (hb : b.val < 64)
    (hr : baseA (.Untyped p b i d) ≤ topA (.Untyped p b i d)) :
    baseA (.Untyped p b i d) = p.val ∧ topA (.Untyped p b i d) = p.val + 2 ^ b.val - 1 ∧
      p.val + 2 ^ b.val ≤ 2 ^ 64 := by
  have hb' : baseA (.Untyped p b i d) = p.val := by unfold baseA; rw [ptrA_ut]
  have hm := mskA_val hb
  have h1 : 1 ≤ 2 ^ b.val := Nat.one_le_two_pow
  have hp : 2 ^ b.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hb
  have ht : topA (.Untyped p b i d) = (p.val + (2 ^ b.val - 1)) % 2 ^ 64 := by
    unfold topA; rw [ptrA_ut, sizeA_ut, wa_val, hm]
  rw [hb', ht] at hr
  have hpv : p.val < 2 ^ 64 := p.hBounds
  have hnw : p.val + (2 ^ b.val - 1) < 2 ^ 64 := by
    by_contra hc
    have : (p.val + (2 ^ b.val - 1)) % 2 ^ 64 = p.val + (2 ^ b.val - 1) - 2 ^ 64 := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨hb', ?_, by omega⟩
  rw [ht, Nat.mod_eq_of_lt hnw]; omega

theorem isUtA_ex {c : capability.Cap} (h : isUtA c = true) : ∃ p b i e, c = .Untyped p b i e := by
  cases c with
  | Untyped p b i e => exact ⟨p, b, i, e, rfl⟩
  | _ => simp [isUtA] at h

/-- A cap in `U`'s range with no wrap is in its region in `same_region_as`'s sense. -/
theorem inU_of {OS : Set U64} {s : S} {p b i : U64} {d : Bool} (hb : b.val < 64)
    (hr : baseA (.Untyped p b i d) ≤ topA (.Untyped p b i d)) {z : U64} (hz : z ∈ OS)
    (h1 : physA (capA st s z) = true) (h2 : p.val ≤ baseA (capA st s z))
    (h3 : topA (capA st s z) < p.val + 2 ^ b.val) (h4 : baseA (capA st s z) ≤ topA (capA st s z)) :
    InU st OS s (.Untyped p b i d) z := by
  refine ⟨hz, ?_⟩
  obtain ⟨-, r2, -⟩ := ut_rangeA hb hr
  have t : (wa p (mskA b)).val = p.val + 2 ^ b.val - 1 := by
    have := r2; unfold topA at this; rwa [ptrA_ut, sizeA_ut] at this
  rw [sraA_ut]
  simp only [h1, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨h2, ?_, h4⟩
  show topA (capA st s z) ≤ (wa p (mskA b)).val
  rw [t]; omega

/-! ## The invariant -/

/-- **The untyped invariant** (module docstring; x86 `UtInv` plus `anc`). -/
structure UtInvA (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (par : U64 → Option U64) (s : S) :
    Prop where
  reg : ∀ x ∈ OS, physA (capA st s x) = true → baseA (capA st s x) ≤ topA (capA st s x)
  inc : ∀ x ∈ OS, ∀ p b i d, capA st s x = .Untyped p b i d → ∀ y, Mdb.Desc par y x →
    physA (capA st s y) = true ∧ p.val ≤ baseA (capA st s y) ∧ topA (capA st s y) < p.val + i.val
  noov : ∀ x ∈ OS, ∀ p b i d, capA st s x = .Untyped p b i d → ∀ y ∈ OS, physA (capA st s y) = true →
    DisjRA (capA st s y) (p.val + i.val) (p.val + 2 ^ b.val) ∨
      (isUtA (capA st s y) = true ∧ WithinA (capA st s x) (capA st s y))
  excl : ∀ x ∈ OS, ∀ y ∈ OS, x ≠ y → ∀ p b i i' d d', capA st s x = .Untyped p b i d →
    capA st s y = .Untyped p b i' d' → 2 ^ b.val ≤ i.val ∨ 2 ^ b.val ≤ i'.val
  fib : ∀ x ∈ OS, ∀ p b i d, capA st s x = .Untyped p b i d → i.val ≤ 2 ^ b.val
  drange : ∀ x ∈ OS, ∀ p b i d, capA st s x = .Untyped p b i d → ∀ y ∈ OS, y ≠ x →
    physA (capA st s y) = true → ¬ DisjA (capA st s y) (capA st s x) → Mdb.Desc par y x ∨ Mdb.Desc par x y
  anc : ∀ x y, Mdb.Desc par y x → isUtA (capA st s y) = true → isUtA (capA st s x) = true

/-- The parent map relates `OS` slots only. -/
def ParIn (OS : Set U64) (par : U64 → Option U64) : Prop := ∀ a b, par a = some b → a ∈ OS ∧ b ∈ OS

theorem desc_in {OS : Set U64} {par : U64 → Option U64} (hP : ParIn OS par) {y x : U64}
    (h : Mdb.Desc par y x) : y ∈ OS ∧ x ∈ OS := by
  induction h with
  | single h1 => exact hP _ _ h1
  | tail _ h2 ih => exact ⟨ih.1, (hP _ _ h2).2⟩

/-- **The tree on the chain** (module docstring). -/
structure TreeA (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (G : List (List U64))
    (par : U64 → Option U64) (s : S) : Prop where
  lk : MdbLk st OS G s
  tree : Mdb.MdbOK par G
  ut : UtInvA st OS par s

/-- The tree carried with its ghosts hidden. -/
def MdbTU (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) : Prop :=
  ∃ G : List (List U64), ∃ par : U64 → Option U64, TreeA st OS G par s

section gen
variable {OS : Set U64} {G : List (List U64)} {par : U64 → Option U64}

theorem TreeA.parIn {s : S} (h : TreeA st OS G par s) : ParIn OS par := fun a b e =>
  ⟨((h.lk.members a).1 (h.tree.par_mem a b e).1).1, ((h.lk.members b).1 (h.tree.par_mem a b e).2).1⟩

theorem TreeA.noself {s : S} (h : TreeA st OS G par s) (x : U64) : par x ≠ some x := fun e => by
  obtain ⟨ch, hch, hx⟩ := List.mem_flatten.1 (h.tree.par_mem x x e).1
  exact Mdb.not_desc_self (h.tree.seg ch hch) ((List.nodup_flatten.1 h.tree.nodup).1 ch hch) hx
    (Relation.TransGen.single e)

/-! ### Boot -/

theorem UtInvA.empty {s : S} (h : ∀ x ∈ OS, capA st s x = .Null) : UtInvA st OS (fun _ => none) s := by
  have nd : ∀ y x : U64, ¬ Mdb.Desc (fun _ : U64 => (none : Option U64)) y x :=
    fun y x => Mdb.not_desc_of_none rfl
  refine ⟨fun x hx hp => ?_, fun x hx _ _ _ _ hc => ?_, fun x hx _ _ _ _ hc => ?_,
    fun x hx _ _ _ _ _ _ _ _ _ hc _ => ?_, fun x hx _ _ _ _ hc => ?_, fun x hx _ _ _ _ hc => ?_,
    fun x y hd => absurd hd (nd y x)⟩ <;> (try rw [h x hx] at hc) <;> (try cases hc)
  rw [h x hx, physA_null] at hp; cases hp

theorem TreeA.empty {s : S} (h : ∀ x ∈ OS, capA st s x = .Null) : TreeA st OS [] (fun _ => none) s :=
  ⟨MdbLk.empty h, ⟨by simp, by simp, fun a b e => by cases e⟩, UtInvA.empty h⟩

theorem MdbTU.empty {s : S} (h : ∀ x ∈ OS, capA st s x = .Null) : MdbTU st OS s := ⟨[], _, TreeA.empty h⟩

/-! ### Alike caps -/

/-- **A new cap `d` for an old cap `c`, for `UtInvA`** (x86 `UtEq`, the free index allowed to grow). -/
structure UA (d c : capability.Cap) : Prop where
  phys : physA d = physA c
  ptr : ptrA d = ptrA c
  size : sizeA d = sizeA c
  isut : isUtA d = isUtA c
  ut : ∀ p b i e, d = .Untyped p b i e →
    ∃ i0 e0, c = .Untyped p b i0 e0 ∧ i0.val ≤ i.val ∧ (i = i0 ∨ i.val ≤ 2 ^ b.val)

theorem UA.refl (c : capability.Cap) : UA c c :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ i e h => ⟨i, e, h, le_refl _, Or.inl rfl⟩⟩

theorem UA.base {d c : capability.Cap} (h : UA d c) : baseA d = baseA c := by unfold baseA; rw [h.ptr]
theorem UA.top {d c : capability.Cap} (h : UA d c) : topA d = topA c := by unfold topA; rw [h.ptr, h.size]

/-- `set_untyped_cap_as_full`'s effect is alike (the old free index bounded, `fib`). -/
theorem FullA.ua {d c : capability.Cap} (h : FullA d c)
    (hf : ∀ p b i e, c = .Untyped p b i e → i.val ≤ 2 ^ b.val) : UA d c := by
  rcases h with rfl | ⟨p, b, i, e, i1, rfl, rfl, hi⟩
  · exact UA.refl _
  · have hb := hf p b i e rfl
    refine ⟨by rw [physA_ut, physA_ut], by rw [ptrA_ut, ptrA_ut], by rw [sizeA_ut, sizeA_ut], rfl,
      fun p' b' i' e' h => ?_⟩
    injection h with a1 a2 a3 a4
    subst a1 a2 a3 a4
    exact ⟨i, e, rfl, by omega, Or.inr (by omega)⟩

/-! ### Renaming (x86 `UtInv.rename`) -/

/-- **Caps and tree renamed by a permutation `e` of `OS`** (swap, move; `e = refl`: recap). -/
theorem UtInvA.ren {s s' : S} (hU : UtInvA st OS par s) (hP : ParIn OS par) (e : U64 ≃ U64)
    (he : ∀ y ∈ OS, e y ∈ OS) (he' : ∀ y ∈ OS, e.symm y ∈ OS)
    (hc : ∀ y ∈ OS, UA (capA st s' (e y)) (capA st s y)) : UtInvA st OS (Mdb.conjPar e par) s' := by
  have hq : ∀ z ∈ OS, UA (capA st s' z) (capA st s (e.symm z)) := fun z hz => by
    have := hc _ (he' z hz); rwa [Equiv.apply_symm_apply] at this
  have hD : ∀ y x, Mdb.Desc (Mdb.conjPar e par) y x ↔ Mdb.Desc par (e.symm y) (e.symm x) := by
    intro y x
    have := Mdb.desc_conj e par (e.symm y) (e.symm x)
    simpa using this
  refine ⟨fun x hx hp => ?_, fun x hx p b i d hcx y hd => ?_, fun x hx p b i d hcx y hy hp => ?_,
    fun x hx y hy hxy p b i i' d d' hcx hcy => ?_, fun x hx p b i d hcx => ?_,
    fun x hx p b i d hcx y hy hyx hp hd => ?_, fun x y hd hu => ?_⟩
  · have q := hq x hx
    rw [q.phys] at hp; rw [q.base, q.top]; exact hU.reg _ (he' x hx) hp
  · obtain ⟨i0, e0, hc0, hle, -⟩ := (hq x hx).ut p b i d hcx
    have hd0 := (hD y x).1 hd
    have hyO : y ∈ OS := by
      have := he _ (desc_in hP hd0).1; rwa [Equiv.apply_symm_apply] at this
    obtain ⟨g1, g2, g3⟩ := hU.inc _ (he' x hx) p b i0 e0 hc0 _ hd0
    have q := hq y hyO
    rw [q.phys, q.base, q.top]; exact ⟨g1, g2, by omega⟩
  · have qx := hq x hx
    have qy := hq y hy
    obtain ⟨i0, e0, hc0, hle, -⟩ := qx.ut p b i d hcx
    rw [qy.phys] at hp
    rcases hU.noov _ (he' x hx) p b i0 e0 hc0 _ (he' y hy) hp with g | ⟨g1, g2⟩
    · left; unfold DisjRA at g ⊢; rw [qy.base, qy.top]; omega
    · right; rw [qy.isut]; refine ⟨g1, ?_⟩
      unfold WithinA at g2 ⊢; rw [qx.base, qx.top, qy.base, qy.top]; exact g2
  · obtain ⟨g0, f0, hg0, hgl, -⟩ := (hq x hx).ut _ _ _ _ hcx
    obtain ⟨g0', f0', hg0', hgl', -⟩ := (hq y hy).ut _ _ _ _ hcy
    rcases hU.excl _ (he' x hx) _ (he' y hy) (fun h => hxy (e.symm.injective h)) _ _ _ _ _ _ hg0 hg0' with g | g
    · left; omega
    · right; omega
  · obtain ⟨i0, e0, hc0, -, hor⟩ := (hq x hx).ut p b i d hcx
    rcases hor with h | h
    · rw [h]; exact hU.fib _ (he' x hx) _ _ _ _ hc0
    · exact h
  · have qx := hq x hx
    have qy := hq y hy
    obtain ⟨i0, e0, hc0, -, -⟩ := qx.ut p b i d hcx
    rw [qy.phys] at hp
    have hd0 : ¬ DisjA (capA st s (e.symm y)) (capA st s (e.symm x)) := by
      unfold DisjA at hd ⊢; rw [qx.base, qx.top, qy.base, qy.top] at hd; exact hd
    rcases hU.drange _ (he' x hx) p b i0 e0 hc0 _ (he' y hy) (fun h => hyx (e.symm.injective h)) hp hd0 with
      g | g
    · exact Or.inl ((hD y x).2 g)
    · exact Or.inr ((hD x y).2 g)
  · have hd0 := (hD y x).1 hd
    obtain ⟨h1, h2⟩ := desc_in hP hd0
    have hyO : y ∈ OS := by have := he _ h1; rwa [Equiv.apply_symm_apply] at this
    have hxO : x ∈ OS := by have := he _ h2; rwa [Equiv.apply_symm_apply] at this
    rw [(hq y hyO).isut] at hu; rw [(hq x hxO).isut]; exact hU.anc _ _ hd0 hu

/-- **Caps alike in place, tree kept** (x86 `UtInv.of_alike` / `raise_fi`). -/
theorem UtInvA.recap {s s' : S} (hU : UtInvA st OS par s) (hP : ParIn OS par)
    (hc : ∀ y ∈ OS, UA (capA st s' y) (capA st s y)) : UtInvA st OS par s' := by
  have := hU.ren hP (Equiv.refl U64) (fun y hy => hy) (fun y hy => hy) hc
  rwa [conjPar_refl] at this

/-! ### Removal (x86 `UtInv.remove`) -/

theorem UtInvA.rem {s s' : S} (hU : UtInvA st OS par s) (hP : ParIn OS par) {x : U64} (hx : par x ≠ some x)
    (hx0 : capA st s' x = .Null) (hk : ∀ y ∈ OS, y ≠ x → capA st s' y = capA st s y) :
    UtInvA st OS (Mdb.removePar x par) s' := by
  have hD : ∀ y z, Mdb.Desc (Mdb.removePar x par) y z ↔ y ≠ x ∧ z ≠ x ∧ Mdb.Desc par y z :=
    Mdb.desc_remove_iff hx
  have neU : ∀ {z p b i d}, capA st s' z = .Untyped p b i d → z ≠ x := fun h e => by
    rw [e, hx0] at h; cases h
  have neP : ∀ {z}, physA (capA st s' z) = true → z ≠ x := fun h e => by
    rw [e, hx0, physA_null] at h; cases h
  refine ⟨fun z hz hp => ?_, fun z hz p b i d hc y hd => ?_, fun z hz p b i d hc y hy hp => ?_,
    fun z hz y hy hzy p b i i' d d' hcz hcy => ?_, fun z hz p b i d hc => ?_,
    fun z hz p b i d hc y hy hyz hp hd => ?_, fun z y hd hu => ?_⟩
  · have hzx := neP hp
    rw [hk z hz hzx] at hp ⊢; exact hU.reg z hz hp
  · have hzx := neU hc
    obtain ⟨hyx, -, hd0⟩ := (hD y z).1 hd
    rw [hk z hz hzx] at hc
    rw [hk y (desc_in hP hd0).1 hyx]; exact hU.inc z hz p b i d hc y hd0
  · have hzx := neU hc
    have hyx := neP hp
    rw [hk z hz hzx] at hc ⊢; rw [hk y hy hyx] at hp ⊢
    exact hU.noov z hz p b i d hc y hy hp
  · have hzx := neU hcz
    have hyx := neU hcy
    rw [hk z hz hzx] at hcz; rw [hk y hy hyx] at hcy
    exact hU.excl z hz y hy hzy _ _ _ _ _ _ hcz hcy
  · have hzx := neU hc
    rw [hk z hz hzx] at hc; exact hU.fib z hz _ _ _ _ hc
  · have hzx := neU hc
    have hyx := neP hp
    rw [hk z hz hzx] at hc hd; rw [hk y hy hyx] at hp hd
    rcases hU.drange z hz p b i d hc y hy hyz hp hd with g | g
    · exact Or.inl ((hD y z).2 ⟨hyx, hzx, g⟩)
    · exact Or.inr ((hD z y).2 ⟨hzx, hyx, g⟩)
  · obtain ⟨hyx, hzx, hd0⟩ := (hD y z).1 hd
    obtain ⟨hyO, hzO⟩ := desc_in hP hd0
    rw [hk y hyO hyx] at hu; rw [hk z hzO hzx]; exact hU.anc z y hd0 hu

/-! ### Insertion (x86 `InsCtx.utinv`, `dest` a child of `src`) -/

set_option maxHeartbeats 2000000 in
/-- **Insertion of `dest` after `src` as its child** (module docstring). -/
theorem UtInvA.ins {s s' : S} (hU : UtInvA st OS par s) (hP : ParIn OS par) {src dest : U64}
    (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest)
    (hdp : ∀ z, par z ≠ some dest) (hdn : par dest = none)
    (hk : ∀ y ∈ OS, y ≠ src → y ≠ dest → capA st s' y = capA st s y)
    (hs : UA (capA st s' src) (capA st s src)) (hdA : UA (capA st s' dest) (capA st s src))
    (hfull : ∀ p b i e, capA st s' dest = .Untyped p b i e →
      ∃ i1 e1, capA st s' src = .Untyped p b i1 e1 ∧ i1.val = 2 ^ b.val)
    (hut : isUtA (capA st s src) = true → ∀ y, ¬ Mdb.Desc par y src) :
    UtInvA st OS (Function.update par dest (some src)) s' := by
  have hD : ∀ y x, Mdb.Desc (Function.update par dest (some src)) y x ↔
      Mdb.Desc par y x ∨ (y = dest ∧ (x = src ∨ Mdb.Desc par src x)) := by
    intro y x
    rw [Mdb.desc_update_iff hdp hdn (by simpa using hsd)]
    constructor
    · rintro (h | ⟨hy, h | ⟨q, hq, h⟩⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hy, Or.inl (Option.some.inj h).symm⟩
      · exact Or.inr ⟨hy, Or.inr (by rw [Option.some.inj hq]; exact h)⟩
    · rintro (h | ⟨hy, hx | h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hy, Or.inl (by rw [hx])⟩
      · exact Or.inr ⟨hy, Or.inr ⟨src, rfl, h⟩⟩
  have ndD : ∀ x, ¬ Mdb.Desc par dest x := fun x => Mdb.not_desc_of_none hdn
  have nDd : ∀ y, ¬ Mdb.Desc par y dest := fun y => Mdb.not_desc_of_no_child hdp
  have V : ∀ z ∈ OS, z ≠ dest → UA (capA st s' z) (capA st s z) := fun z hz hzd => by
    by_cases e : z = src
    · rw [e]; exact hs
    · rw [hk z hz e hzd]; exact UA.refl _
  have W : ∀ z ∈ OS, ∃ z0 ∈ OS, UA (capA st s' z) (capA st s z0) ∧ (z ≠ dest → z0 = z) ∧
      (z = dest → z0 = src) := fun z hz => by
    by_cases hzd : z = dest
    · exact ⟨src, hsrc, by rw [hzd]; exact hdA, fun h => absurd hzd h, fun _ => rfl⟩
    · exact ⟨z, hz, V z hz hzd, fun _ => rfl, fun h => absurd h hzd⟩
  -- the source is full when the copy is an `Untyped`
  have sfull : ∀ p b i e, capA st s' src = .Untyped p b i e → isUtA (capA st s src) = true →
      i.val = 2 ^ b.val := fun p b i e hc hu => by
    have hu' : isUtA (capA st s' dest) = true := by rw [hdA.isut]; exact hu
    obtain ⟨p', b', i', e', hd'⟩ := isUtA_ex hu'
    obtain ⟨i1, e1, hs1, hi1⟩ := hfull _ _ _ _ hd'
    rw [hc] at hs1
    injection hs1 with a1 a2 a3 a4
    subst a1 a2 a3 a4
    exact hi1
  refine ⟨fun x hx hp => ?_, fun x hx p b i d hc y hy => ?_, fun x hx p b i d hc y hy hp => ?_,
    fun x hx y hy hxy p b i i' d d' hcx hcy => ?_, fun x hx p b i d hc => ?_,
    fun x hx p b i d hc y hy hyx hp hd => ?_, fun x y hd hu => ?_⟩
  -- reg
  · obtain ⟨x0, hx0, q, -, -⟩ := W x hx
    rw [q.phys] at hp; rw [q.base, q.top]; exact hU.reg x0 hx0 hp
  -- inc
  · rcases (hD y x).1 hy with h0 | ⟨hyd, hxs | h0⟩
    · have hyd : y ≠ dest := fun e => ndD x (by rw [← e]; exact h0)
      have hxd : x ≠ dest := fun e => nDd y (by rw [← e]; exact h0)
      obtain ⟨hyO, -⟩ := desc_in hP h0
      obtain ⟨i0, e0, hc0, hle, -⟩ := (V x hx hxd).ut p b i d hc
      obtain ⟨g1, g2, g3⟩ := hU.inc x hx p b i0 e0 hc0 y h0
      have q := V y hyO hyd
      rw [q.phys, q.base, q.top]; exact ⟨g1, g2, by omega⟩
    · subst y; subst x
      obtain ⟨i0, e0, hc0, -, -⟩ := hs.ut p b i d hc
      have hi := sfull p b i d hc (by rw [hc0]; rfl)
      have hr := hU.reg src hsrc (by rw [hc0]; exact physA_ut _ _ _ _)
      rw [hc0] at hr
      obtain ⟨r1, r2, -⟩ := ut_rangeA (capA_ut_b hc0) hr
      have h2 : 1 ≤ 2 ^ b.val := Nat.one_le_two_pow
      rw [hdA.phys, hdA.base, hdA.top, hc0, r1, r2, physA_ut]
      exact ⟨rfl, le_refl _, by omega⟩
    · subst y
      have hxd : x ≠ dest := fun e => nDd src (by rw [← e]; exact h0)
      obtain ⟨i0, e0, hc0, hle, -⟩ := (V x hx hxd).ut p b i d hc
      obtain ⟨g1, g2, g3⟩ := hU.inc x hx p b i0 e0 hc0 src h0
      rw [hdA.phys, hdA.base, hdA.top]; exact ⟨g1, g2, by omega⟩
  -- noov
  · obtain ⟨x0, hx0, qx, -, -⟩ := W x hx
    obtain ⟨y0, hy0, qy, -, -⟩ := W y hy
    obtain ⟨i0, e0, hc0, hle, -⟩ := qx.ut p b i d hc
    rw [qy.phys] at hp
    rcases hU.noov x0 hx0 p b i0 e0 hc0 y0 hy0 hp with g | ⟨g1, g2⟩
    · left; unfold DisjRA at g ⊢; rw [qy.base, qy.top]; omega
    · right; rw [qy.isut]; refine ⟨g1, ?_⟩
      unfold WithinA at g2 ⊢; rw [qx.base, qx.top, qy.base, qy.top]; exact g2
  -- excl
  · obtain ⟨x0, hx0, qx, hxn, hxd'⟩ := W x hx
    obtain ⟨y0, hy0, qy, hyn, hyd'⟩ := W y hy
    obtain ⟨g0, f0, hg0, hgl, -⟩ := qx.ut _ _ _ _ hcx
    obtain ⟨g0', f0', hg0', hgl', -⟩ := qy.ut _ _ _ _ hcy
    by_cases hxy0 : x0 = y0
    · by_cases hx' : x = dest
      · have hy' : y ≠ dest := fun e => hxy (hx'.trans e.symm)
        have e1 : y = src := by rw [← hyn hy', ← hxy0, hxd' hx']
        have ey : y0 = src := by rw [hyn hy', e1]
        rw [e1] at hcy
        exact Or.inr (le_of_eq (sfull _ _ _ _ hcy (by rw [← ey, hg0']; rfl)).symm)
      · have e1 : x = src := by
          rw [← hxn hx']
          by_cases hy' : y = dest
          · rw [hxy0, hyd' hy']
          · exact absurd ((hxn hx').symm.trans (hxy0.trans (hyn hy'))) hxy
        have ex : x0 = src := by rw [hxn hx', e1]
        rw [e1] at hcx
        exact Or.inl (le_of_eq (sfull _ _ _ _ hcx (by rw [← ex, hg0]; rfl)).symm)
    · rcases hU.excl x0 hx0 y0 hy0 hxy0 _ _ _ _ _ _ hg0 hg0' with g | g
      · left; omega
      · right; omega
  -- fib
  · obtain ⟨x0, hx0, q, -, -⟩ := W x hx
    obtain ⟨i0, e0, hc0, -, hor⟩ := q.ut p b i d hc
    rcases hor with h | h
    · rw [h]; exact hU.fib x0 hx0 _ _ _ _ hc0
    · exact h
  -- drange
  · have up : ∀ {a z}, Mdb.Desc par a z → Mdb.Desc (Function.update par dest (some src)) a z :=
      fun e => (hD _ _).2 (Or.inl e)
    have dn : ∀ {z}, (z = src ∨ Mdb.Desc par src z) → Mdb.Desc (Function.update par dest (some src)) dest z :=
      fun e => (hD _ _).2 (Or.inr ⟨rfl, e⟩)
    by_cases hxD : x = dest
    · subst x
      have qy := V y hy hyx
      obtain ⟨i0, e0, hc0, -, -⟩ := hdA.ut p b i d hc
      have hsu : isUtA (capA st s src) = true := by rw [hc0]; rfl
      rw [qy.phys] at hp
      have hd0 : ¬ DisjA (capA st s y) (capA st s src) := by
        unfold DisjA at hd ⊢; rw [qy.base, qy.top, hdA.base, hdA.top] at hd; exact hd
      by_cases hys : y = src
      · right; rw [hys]; exact dn (Or.inl rfl)
      · rcases hU.drange src hsrc _ _ _ _ hc0 y hy hys hp hd0 with g | g
        · exact absurd g (hut hsu y)
        · exact Or.inr (dn (Or.inr g))
    · have qx := V x hx hxD
      obtain ⟨i0, e0, hc0, -, -⟩ := qx.ut p b i d hc
      by_cases hyD : y = dest
      · subst y
        rw [hdA.phys] at hp
        have hd0 : ¬ DisjA (capA st s src) (capA st s x) := by
          unfold DisjA at hd ⊢; rw [qx.base, qx.top, hdA.base, hdA.top] at hd; exact hd
        by_cases hxs : x = src
        · left; rw [hxs]; exact dn (Or.inl rfl)
        · rcases hU.drange x hx _ _ _ _ hc0 src hsrc (Ne.symm hxs) hp hd0 with g | g
          · exact Or.inl (dn (Or.inr g))
          · exact absurd g (hut (hU.anc src x g (by rw [hc0]; rfl)) x)
      · have qy := V y hy hyD
        rw [qy.phys] at hp
        have hd0 : ¬ DisjA (capA st s y) (capA st s x) := by
          unfold DisjA at hd ⊢; rw [qx.base, qx.top, qy.base, qy.top] at hd; exact hd
        rcases hU.drange x hx _ _ _ _ hc0 y hy hyx hp hd0 with g | g
        · exact Or.inl (up g)
        · exact Or.inr (up g)
  -- anc
  · rcases (hD y x).1 hd with h0 | ⟨hyd, hxs | h0⟩
    · have hyd : y ≠ dest := fun e => ndD x (by rw [← e]; exact h0)
      have hxd : x ≠ dest := fun e => nDd y (by rw [← e]; exact h0)
      obtain ⟨hyO, hxO⟩ := desc_in hP h0
      rw [(V y hyO hyd).isut] at hu; rw [(V x hxO hxd).isut]; exact hU.anc x y h0 hu
    · rw [hyd, hdA.isut] at hu; rw [hxs, hs.isut]; exact hu
    · rw [hyd, hdA.isut] at hu
      have hxO := (desc_in hP h0).2
      have hxd : x ≠ dest := fun e => nDd src (by rw [← e]; exact h0)
      rw [(V x hxO hxd).isut]; exact hU.anc x src h0 hu

/-! ## The flat facts as corollaries -/

/-- **`FreeFresh` from `UtInvA`** (`noov` and `reg`). -/
theorem UtInvA.freeFresh {s : S} (hU : UtInvA st OS par s) : FreeFresh st OS s := by
  refine ⟨fun u hu p b i d hcu c hc hk ⟨h1, h2⟩ => ?_⟩
  have hpc : physA (capA st s c) = true := hk.1
  have hrc := hU.reg c hc hpc
  have hbc : baseA (capA st s c) = (ptrA (capA st s c)).val := rfl
  rcases hU.noov u hu p b i d hcu c hc hpc with g | ⟨g1, -⟩
  · unfold DisjRA at g; omega
  · rw [hk.2.1] at g1; cases g1

theorem nx_split {s : S} (hM : MdbLk st OS G s) {ch : List U64} (hch : ch ∈ G) {A B : List U64} {a b : U64}
    (e : ch = A ++ a :: b :: B) : NxA st s a = b :=
  (hM.chain ch hch A.length a b (by rw [e, List.getElem?_append_right (by omega)]; simp)
    (by rw [e, List.getElem?_append_right (by omega)]; simp)).1

/-- A stretch of a chain whose slots satisfy `P` is a `NEXT` path. -/
theorem chain_path {s : S} (hM : MdbLk st OS G s) {ch : List U64} (hch : ch ∈ G) {P : U64 → Prop} :
    ∀ (l : List U64) {pre rest : List U64} {u c : U64}, ch = pre ++ u :: (l ++ c :: rest) →
      (∀ z ∈ l, P z) → P c → UtAbs.Path (NxA st s) P u c
  | [], pre, rest, u, c, e, _, hc => .of (nx_split hM hch (by simpa using e)) hc
  | z :: l, pre, rest, u, c, e, hl, hc => by
    have e1 : ch = pre ++ u :: z :: (l ++ c :: rest) := by simpa using e
    have e2 : ch = (pre ++ [u]) ++ z :: (l ++ c :: rest) := by rw [e1]; simp
    exact .cons (nx_split hM hch e1) (hl z (by simp))
      (chain_path hM hch l e2 (fun w hw => hl w (by simp [hw])) hc)

/-- **Descendants of an `Untyped` slot are in its region.** -/
theorem TreeA.inU_desc {s : S} (h : TreeA st OS G par s) {u p b i : U64} {d : Bool} (hu : u ∈ OS)
    (hc : capA st s u = .Untyped p b i d) {z : U64} (hz : Mdb.Desc par z u) : InU st OS s (.Untyped p b i d) z := by
  have hU := h.ut
  obtain ⟨g1, g2, g3⟩ := hU.inc u hu p b i d hc z hz
  have zO := (desc_in h.parIn hz).1
  have hf := hU.fib u hu p b i d hc
  have hru := hU.reg u hu (by rw [hc]; exact physA_ut _ _ _ _)
  rw [hc] at hru
  exact inU_of (capA_ut_b hc) hru zO g1 g2 (by omega) (hU.reg z zO g1)

/-- A descendant of `u` is reached from `u` along `NEXT` through descendants. -/
theorem TreeA.path_desc {s : S} (h : TreeA st OS G par s) {u c : U64} {P : U64 → Prop} (hu : u ∈ G.flatten)
    (hc : Mdb.Desc par c u) (hP : ∀ z, Mdb.Desc par z u → P z) : UtAbs.Path (NxA st s) P u c := by
  obtain ⟨ch, hch, huc⟩ := List.mem_flatten.1 hu
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem huc
  obtain ⟨dd, rest, hpost, hd⟩ := h.tree.seg ch hch pre u post hsplit
  obtain ⟨d1, d2, hd12⟩ := List.append_of_mem ((hd c).1 hc)
  have e : ch = pre ++ u :: (d1 ++ c :: (d2 ++ rest)) := by rw [hsplit, hpost, hd12]; simp
  exact chain_path h.lk hch d1 e (fun z hz => hP z ((hd z).2 (by rw [hd12]; simp [hz]))) (hP c hc)

/-- **`UtRangeOrd` from the tree** (module docstring). -/
theorem TreeA.utRangeOrd {s : S} (h : TreeA st OS G par s) : UtRangeOrd st OS s := by
  refine ⟨fun u hu p b i d hcu c hc hk h1 h2 => ?_⟩
  have hU := h.ut
  have hcu' : c ≠ u := fun e => by rw [e, hcu] at hk; exact nk_ut _ _ _ _ hk
  have hpc : physA (capA st s c) = true := hk.1
  have hru := hU.reg u hu (by rw [hcu]; exact physA_ut _ _ _ _)
  rw [hcu] at hru
  obtain ⟨r1, r2, -⟩ := ut_rangeA (capA_ut_b hcu) hru
  have hrc := hU.reg c hc hpc
  have hbc : baseA (capA st s c) = (ptrA (capA st s c)).val := rfl
  have hnd : ¬ DisjA (capA st s c) (capA st s u) := by
    unfold DisjA; rw [hcu, r1, r2]; have : 1 ≤ 2 ^ b.val := Nat.one_le_two_pow; omega
  rcases hU.drange u hu p b i d hcu c hc hcu' hpc hnd with hD | hD
  · have huG : u ∈ G.flatten := (h.lk.members u).2 ⟨hu, by rw [hcu]; exact fun e => by cases e⟩
    exact h.path_desc huG hD fun z hz => h.inU_desc hu hcu hz
  · have := hU.anc c u hD (by rw [hcu]; rfl)
    rw [hk.2.1] at this; cases this

theorem MdbTU.flat {s : S} (h : MdbTU st OS s) : UtRangeOrd st OS s ∧ FreeFresh st OS s := by
  obtain ⟨G, par, hT⟩ := h
  exact ⟨hT.utRangeOrd, hT.ut.freeFresh⟩

/-- **`ensure_no_children` returning `Ok` at a revocable `Untyped` slot: no descendants** (the first one would be
`NEXT u`, in the region). -/
theorem cdt.ensure_no_children.noDesc (hO : OSOK T Ω Sg OS) {s : S} (h : TreeA st OS G par s) {u p b i : U64}
    {d : Bool} (hu : u ∈ OS) (hc : capA st s u = .Untyped p b i d) (hr : obj.Slot.revocable st u s = ok true)
    (he : cdt.ensure_no_children st s u = ok (core.result.Result.Ok ())) : ∀ y, ¬ Mdb.Desc par y u := by
  intro y hy
  have huG : u ∈ G.flatten := (h.lk.members u).2 ⟨hu, by rw [hc]; exact fun e => by cases e⟩
  obtain ⟨ch, hch, huc⟩ := List.mem_flatten.1 huG
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem huc
  obtain ⟨dd, rest, hpost, hd⟩ := h.tree.seg ch hch pre u post hsplit
  have hyd := (hd y).1 hy
  cases dd with
  | nil => simp at hyd
  | cons d0 d' =>
    have e : ch = pre ++ u :: d0 :: (d' ++ rest) := by rw [hsplit, hpost]; simp
    have hn := nx_split h.lk hch e
    have hd0 : Mdb.Desc par d0 u := (hd d0).2 (by simp)
    exact cdt.ensure_no_children.out hO hc hr he (by rw [hn]; exact h.inU_desc hu hc hd0)

end gen

end ST
end R
end W7

end

end Fl4ProofsA64.P1
