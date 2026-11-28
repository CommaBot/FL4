/-
P1 (aarch64, gen 53): **retype freshness on the A64 MDB chain** (Architect ruling relayed in gen 52) — two flat
facts beside `RngOneA64` / `KindA`, no new ghost, no named premise: `FreeFresh` and `UtRangeOrd`, stated over the
`NEXT` links themselves (the chain `MdbLk` ties to its ghost), so they need no ghost of their own.

* `sraA a b`: the kernel's own `same_region_as` (objects.rs:84–96) as a total function; `sraA_ut` (its value for an
  `Untyped` first argument), `sra_ut_congr` (it reads only the region `ptr` / `size_bits` and the second cap's
  physical bit, `ptrA`, `sizeA`), `sraA_null`, `sraA_self`. **`InU st OS s U z`**: `z` is an `OS` slot holding a
  cap in `U`'s region (`sraA U cap = true`).
* `UtAbs.Path nx P a b` (any type): a `NEXT` path from `a` to `b` every node after `a` satisfies `P`; transfer
  lemmas `Path.congr` (links agreeing on the path), `Path.map` (links renamed: swap / move), `Path.ins` (a node
  inserted after `s`: `insert_with_cap` / `insert_new_cap`), `Path.rem` (a node unlinked: `empty_slot`), `snoc`.
* **`FreeFresh st OS s`** (l4v `valid_untyped`'s free part): for every `Untyped p b i _` cap in an `OS` slot, no `OS`
  slot holds a `RngKeyA` cap with `ptrA` in `[p + i, p + 2 ^ b)`.
* **`UtRangeOrd st OS s`** (l4v `untyped_mdb` + `descendants_range_in`, along the chain): for every `Untyped p b i _`
  slot `u` and every `OS` slot `c` holding a `RngKeyA` cap with `ptrA` in `[p, p + 2 ^ b)`, `c` is reached from `u`
  along `NEXT` with every slot after `u` up to `c` in `u`'s region (`InU`): `c` is after `u` on its chain and every
  slot between lies in the region.
* `UtRev st OS s` (l4v `ut_revocable`): every `Untyped` slot of `OS` has its revocable bit set. **Finding**: the
  derivation from `ensure_no_children` needs it — `is_mdb_parent_of` (cdt.rs:106–138) is false for a non-revocable
  slot, so `ensure_no_children` returns `Ok` whatever follows; boot and `OSKeep` steps here, the flag-level
  preservation along insert / move / swap is still owed.
* Boot: `UtRangeOrd.empty`, `FreeFresh.empty`, `UtRev.empty` (no non-null `OS` cap).
* **The derivation (closes reset)**: `UtRangeOrd.none` — `NEXT u` outside `u`'s region ⇒ no `RngKeyA` cap with
  `ptrA` in `[p, p + 2 ^ b)`; `cdt.ensure_no_children.out` (`Ok` at a revocable `Untyped` slot ⇒ `NEXT u` outside
  the region), **`cdt.ensure_no_children.noKey`** (both, under `UtRev`), `FreeFresh.reset` (then any free index,
  in particular `0`, keeps `FreeFresh`).
* Preservation, data level: `RA d c` (a new cap `d` standing for an old cap `c`: key kept, same physical bit /
  `ptrA` / `sizeA`, an `Untyped` for an `Untyped` of the same region with no smaller free index unless full),
  `FullA` (`set_untyped_cap_as_full`'s effect) and `FullA.ra`; **`FreeFresh.ofRA`** (every new cap `RA` some old
  cap); **`UtRangeOrd.ren`** (caps and links renamed by an involution: swap, move), **`UtRangeOrd.recap`** (links
  kept, caps `RA`: in-place `set_cap` of an alike cap, `OSKeep` steps — `UtRangeOrd.keep` / `FreeFresh.keep` /
  `UtRev.keep`), **`UtRangeOrd.ins`** (insertion after `src`), **`UtRangeOrd.rem`** (removal).
* Function level: **`cdt.swap.ut`** (any two encodable caps `RA` the replaced ones: `cap_swap_for_delete`, Rotate),
  **`cdt.cap_swap_for_delete.ut`**, **`cdt.move_cap.ut`**, **`cdt.set_untyped_cap_as_full.full`**,
  **`cdt.insert_with_cap.srcF`**, **`cdt.insert_with_cap.ut`** / **`cdt.insert.ut`** (new cap `RA` the source's).

No named premise; new definitions and theorems only. Still owed: `empty_slot` / the deletion loops / the CNode
decode tops at function level (data-level `UtRangeOrd.rem` / `recap` are their steps), `UtRev` along insert / move
/ swap, retype (see the gen-53 handoff on the strengthening `insert_new_cap` needs).
-/
import Fl4ProofsA64.P1.MdbSW
import Fl4ProofsA64.P1.QueueReset
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1

/-! ## Paths along `NEXT`, abstractly -/

namespace UtAbs
variable {α : Type}

/-- A `NEXT` path from `a` to `b`: every node after `a` satisfies `P`. -/
inductive Path (nx : α → α) (P : α → Prop) : α → α → Prop
  | one {a : α} : P (nx a) → Path nx P a (nx a)
  | step {a b : α} : P (nx a) → Path nx P (nx a) b → Path nx P a b

variable {nx nx' : α → α} {P P' Q : α → Prop}

theorem Path.of {a c : α} (e : nx a = c) (h : P c) : Path nx P a c := by subst e; exact .one h

theorem Path.cons {a c b : α} (e : nx a = c) (h : P c) (t : Path nx P c b) : Path nx P a b := by
  subst e; exact .step h t

theorem Path.first {a b : α} (h : Path nx P a b) : P (nx a) := by cases h <;> assumption

theorem Path.last {a b : α} (h : Path nx P a b) : P b := by
  induction h with
  | one h => exact h
  | step _ _ ih => exact ih

theorem Path.snoc {a b c : α} (h : Path nx P a b) (e : nx b = c) (hc : P c) : Path nx P a c := by
  induction h with
  | one hp => exact .step hp (.of e hc)
  | step hp _ ih => exact .step hp (ih e)

/-- **Links agreeing at every node the path leaves from.** -/
theorem Path.congr {a b : α} (h : Path nx P a b) (hPQ : ∀ z, P z → Q z) (he : ∀ z, Q z → nx' z = nx z)
    (hP : ∀ z, P z → P' z) : Q a → Path nx' P' a b := by
  induction h with
  | one hp => intro hq; exact .of (he _ hq) (hP _ hp)
  | step hp _ ih => intro hq; exact .cons (he _ hq) (hP _ hp) (ih (hPQ _ hp))

/-- **Links renamed by `f`** (swap, move). -/
theorem Path.map (f : α → α) {a b : α} (h : Path nx P a b) (hPQ : ∀ z, P z → Q z)
    (he : ∀ z, Q z → nx' (f z) = f (nx z)) (hP : ∀ z, P z → P' (f z)) : Q a → Path nx' P' (f a) (f b) := by
  induction h with
  | one hp => intro hq; exact .of (he _ hq) (hP _ hp)
  | step hp _ ih => intro hq; exact .cons (he _ hq) (hP _ hp) (ih (hPQ _ hp))

/-- **A node `d` inserted after `s`.** -/
theorem Path.ins {s d : α} {a b : α} (h : Path nx P a b) (hPQ : ∀ z, P z → Q z)
    (he : ∀ z, Q z → z ≠ s → nx' z = nx z) (hs : nx' s = d) (hd : nx' d = nx s)
    (hP : ∀ z, P z → P' z) (hdP : P s → P' d) : Q a → (a = s → P' d) → Path nx' P' a b := by
  induction h with
  | @one a hp =>
    intro hq ha
    by_cases e : a = s
    · subst e; exact .cons hs (ha rfl) (.of hd (hP _ hp))
    · exact .of (he _ hq e) (hP _ hp)
  | @step a b hp _ ih =>
    intro hq ha
    have ih' := ih (hPQ _ hp) (fun e => hdP (e ▸ hp))
    by_cases e : a = s
    · subst e; exact .cons hs (ha rfl) (.cons hd (hP _ hp) ih')
    · exact .cons (he _ hq e) (hP _ hp) ih'

/-- **A node `x` unlinked** (its predecessor's `NEXT` becomes `x`'s). -/
theorem Path.rem [DecidableEq α] {x : α} {a b : α} (h : Path nx P a b) (hPQ : ∀ z, P z → Q z) (hx : nx x ≠ x)
    (he : ∀ z, Q z → z ≠ x → nx' z = if nx z = x then nx x else nx z)
    (hP : ∀ z, P z → z ≠ x → P' z) : b ≠ x →
    (Q a → a ≠ x → Path nx' P' a b) ∧ (a = x → ∀ y, Q y → y ≠ x → nx' y = nx x → Path nx' P' y b) := by
  induction h with
  | @one a hp =>
    intro hb
    refine ⟨fun hq hax => .of (by rw [he a hq hax, if_neg hb]) (hP _ hp hb), fun hax y _ _ hey => ?_⟩
    subst hax; exact .of hey (hP _ hp hb)
  | @step a b hp _ ih =>
    intro hb
    have ih := ih hb
    refine ⟨fun hq hax => ?_, fun hax y _ _ hey => ?_⟩
    · by_cases e : nx a = x
      · exact ih.2 e a hq hax (by rw [he a hq hax, if_pos e])
      · exact .cons (by rw [he a hq hax, if_neg e]) (hP _ hp e) (ih.1 (hPQ _ hp) e)
    · subst hax
      exact .cons hey (hP _ hp hx) (ih.1 (hPQ _ hp) hx)

end UtAbs

open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-! ## `same_region_as` as a total function -/

theorem sra_total (a b : capability.Cap) : ∃ v, objects.same_region_as a b = ok v := by
  have h := P0.objects.same_region_as.p0 a b
  revert h
  cases objects.same_region_as a b <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

theorem mask_total (b : U64) : ∃ m, objects.mask b = ok m := by
  have h := P0.objects.mask.p0 b
  revert h
  cases objects.mask b <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

noncomputable def sraA (a b : capability.Cap) : Bool := Classical.choose (sra_total a b)
theorem sraA_eq (a b : capability.Cap) : objects.same_region_as a b = ok (sraA a b) :=
  Classical.choose_spec (sra_total a b)

noncomputable def mskA (b : U64) : U64 := Classical.choose (mask_total b)
theorem mskA_eq (b : U64) : objects.mask b = ok (mskA b) := Classical.choose_spec (mask_total b)

theorem ptrA_ut (p b i : U64) (d : Bool) : ptrA (.Untyped p b i d) = p := by
  have h := ptrA_eq (.Untyped p b i d); simp only [capability.Cap.ptr] at h; exact (okinj h).symm

theorem physA_ut (p b i : U64) (d : Bool) : physA (.Untyped p b i d) = true := by
  have h := physA_eq (.Untyped p b i d); simp only [objects.cap_is_physical] at h; exact (okinj h).symm

theorem sizeA_ut (p b i : U64) (d : Bool) : sizeA (.Untyped p b i d) = b := by
  have h := sizeA_eq (.Untyped p b i d); simp only [objects.cap_size_bits] at h; exact (okinj h).symm

theorem physA_null : physA .Null = false := by
  have h := physA_eq .Null; simp only [objects.cap_is_physical] at h; exact (okinj h).symm

/-- **`same_region_as` with an `Untyped` first argument** (objects.rs:86–96). -/
theorem sraA_ut (p b i : U64) (d : Bool) (c : capability.Cap) :
    sraA (.Untyped p b i d) c = (physA c && (decide (p ≤ ptrA c) &&
      (decide (wa (ptrA c) (mskA (sizeA c)) ≤ wa p (mskA b)) &&
        decide (ptrA c ≤ wa (ptrA c) (mskA (sizeA c)))))) := by
  have e := sraA_eq (.Untyped p b i d) c
  simp only [objects.same_region_as, physA_eq, ptrA_eq, sizeA_eq, mskA_eq, bind_ok, lift] at e
  apply okinj
  rw [← e]
  by_cases h1 : physA c = true
  · by_cases h2 : p ≤ ptrA c
    · by_cases h3 : wa (ptrA c) (mskA (sizeA c)) ≤ wa p (mskA b)
      · simp [h1, h2, h3]
      · simp [h1, h2, h3]
    · simp [h1, h2]
  · simp [h1]

/-- `same_region_as (Untyped p b ..)` reads only `p`, `b` and the other cap's physical bit, base and size. -/
theorem sra_ut_congr (p b i i' : U64) (d d' : Bool) {c c' : capability.Cap} (h1 : physA c = physA c')
    (h2 : ptrA c = ptrA c') (h3 : sizeA c = sizeA c') :
    sraA (.Untyped p b i d) c = sraA (.Untyped p b i' d') c' := by
  rw [sraA_ut, sraA_ut, h1, h2, h3]

theorem sraA_null (p b i : U64) (d : Bool) : sraA (.Untyped p b i d) .Null = false := by
  rw [sraA_ut, physA_null]; rfl

/-- An `Untyped` cap whose region holds some cap holds its own region (the region does not wrap). -/
theorem sraA_self {p b i : U64} {d : Bool} {c : capability.Cap} (h : sraA (.Untyped p b i d) c = true)
    (i' : U64) (d' : Bool) : sraA (.Untyped p b i d) (.Untyped p b i' d') = true := by
  rw [sraA_ut] at h
  rw [sraA_ut, physA_ut, ptrA_ut, sizeA_ut]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h2, h3, h4⟩ := h
  have : p ≤ wa p (mskA b) := by
    have a2 : p.val ≤ (ptrA c).val := h2
    have a3 : (wa (ptrA c) (mskA (sizeA c))).val ≤ (wa p (mskA b)).val := h3
    have a4 : (ptrA c).val ≤ (wa (ptrA c) (mskA (sizeA c))).val := h4
    show p.val ≤ (wa p (mskA b)).val
    omega
  simp [this]

/-! ## The facts -/

/-- Slot `z` is an `OS` slot holding a cap in `U`'s region. -/
def InU (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) (U : capability.Cap) (z : U64) : Prop :=
  z ∈ OS ∧ sraA U (capA st s z) = true

/-- **`FreeFresh`** (module docstring). -/
structure FreeFresh (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) : Prop where
  fresh : ∀ u ∈ OS, ∀ p b i d, capA st s u = .Untyped p b i d → ∀ c ∈ OS, RngKeyA (capA st s c) →
    ¬ (p.val + i.val ≤ (ptrA (capA st s c)).val ∧ (ptrA (capA st s c)).val < p.val + 2 ^ b.val)

/-- **`UtRangeOrd`** (module docstring). -/
structure UtRangeOrd (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) : Prop where
  ord : ∀ u ∈ OS, ∀ p b i d, capA st s u = .Untyped p b i d → ∀ c ∈ OS, RngKeyA (capA st s c) →
    p.val ≤ (ptrA (capA st s c)).val → (ptrA (capA st s c)).val < p.val + 2 ^ b.val →
    UtAbs.Path (NxA st s) (InU st OS s (.Untyped p b i d)) u c

/-- **`UtRev`** (module docstring): `Untyped` slots are revocable. -/
def UtRev (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) : Prop :=
  ∀ u ∈ OS, isUtA (capA st s u) = true → obj.Slot.revocable st u s = ok true

section gen
variable {OS : Set U64}

theorem InU.os {s : S} {p b i : U64} {d : Bool} {z : U64} (h : InU st OS s (.Untyped p b i d) z) :
    z ∈ OS ∧ capA st s z ≠ .Null := ⟨h.1, fun e => by have := h.2; rw [e, sraA_null] at this; cases this⟩

/-! ### Boot -/

theorem FreeFresh.empty {s : S} (h : ∀ x ∈ OS, capA st s x = .Null) : FreeFresh st OS s :=
  ⟨fun u hu _ _ _ _ hc => by rw [h u hu] at hc; cases hc⟩

theorem UtRangeOrd.empty {s : S} (h : ∀ x ∈ OS, capA st s x = .Null) : UtRangeOrd st OS s :=
  ⟨fun u hu _ _ _ _ hc => by rw [h u hu] at hc; cases hc⟩

theorem UtRev.empty {s : S} (h : ∀ x ∈ OS, capA st s x = .Null) : UtRev st OS s :=
  fun u hu hc => by rw [h u hu] at hc; cases hc

/-! ### The derivation: `ensure_no_children` closes reset -/

/-- **`NEXT u` outside `u`'s region ⇒ no key cap in it.** -/
theorem UtRangeOrd.none {s : S} (h : UtRangeOrd st OS s) {u p b i : U64} {d : Bool} (hu : u ∈ OS)
    (hc : capA st s u = .Untyped p b i d) (hn : ¬ InU st OS s (.Untyped p b i d) (NxA st s u)) :
    ∀ c ∈ OS, RngKeyA (capA st s c) →
      ¬ (p.val ≤ (ptrA (capA st s c)).val ∧ (ptrA (capA st s c)).val < p.val + 2 ^ b.val) :=
  fun c hc' hk ⟨h1, h2⟩ => hn (h.ord u hu p b i d hc c hc' hk h1 h2).first

/-- **`ensure_no_children` returning `Ok` at a revocable `Untyped` slot**: `NEXT u` is outside the region. -/
theorem cdt.ensure_no_children.out (hO : OSOK T Ω Sg OS) {s : S} {u p b i : U64} {d : Bool}
    (hc : capA st s u = .Untyped p b i d) (hr : obj.Slot.revocable st u s = ok true)
    (he : cdt.ensure_no_children st s u = ok (core.result.Result.Ok ())) :
    ¬ InU st OS s (.Untyped p b i d) (NxA st s u) := by
  rintro ⟨hm, hs⟩
  have hn0 : NxA st s u ≠ 0#u64 := hO.nz _ hm
  have hp : cdt.is_mdb_parent_of st s u (NxA st s u) = ok true := by
    unfold cdt.is_mdb_parent_of
    simp only [hr, capA_eq, hc, sraA_eq, hs, bind_ok, ↓reduceIte]
  unfold cdt.ensure_no_children at he
  rw [next_eq, bind_ok] at he
  simp [obj.Slot.is_null, hn0, hp] at he
  first
  | done
  | exact absurd (okinj he) (by simp)

/-- **Reset is fresh**: `ensure_no_children` returning `Ok` at an `Untyped` slot leaves no key cap in its region. -/
theorem cdt.ensure_no_children.noKey (hO : OSOK T Ω Sg OS) {s : S} (hU : UtRangeOrd st OS s) (hR : UtRev st OS s)
    {u p b i : U64} {d : Bool} (hu : u ∈ OS) (hc : capA st s u = .Untyped p b i d)
    (he : cdt.ensure_no_children st s u = ok (core.result.Result.Ok ())) :
    ∀ c ∈ OS, RngKeyA (capA st s c) →
      ¬ (p.val ≤ (ptrA (capA st s c)).val ∧ (ptrA (capA st s c)).val < p.val + 2 ^ b.val) :=
  hU.none hu hc (cdt.ensure_no_children.out hO hc (hR u hu (by rw [hc]; rfl)) he)

/-- **`FreeFresh` with a slot's `Untyped` rewritten to any free index** when no key cap is in its region (reset). -/
theorem FreeFresh.reset {s s' : S} (hF : FreeFresh st OS s) {u p b i : U64} {d : Bool}
    (hno : ∀ c ∈ OS, RngKeyA (capA st s c) →
      ¬ (p.val ≤ (ptrA (capA st s c)).val ∧ (ptrA (capA st s c)).val < p.val + 2 ^ b.val))
    (hcu : capA st s' u = .Untyped p b i d) (hk : ∀ y ∈ OS, y ≠ u → capA st s' y = capA st s y)
    (hku : ¬ RngKeyA (capA st s u)) : FreeFresh st OS s' := by
  refine ⟨fun u' hu' p' b' i' d' hc' c hc hk' ⟨h1, h2⟩ => ?_⟩
  have hcu' : c ≠ u := fun e => by rw [e, hcu] at hk'; exact nk_ut _ _ _ _ hk'
  rw [hk c hc hcu'] at hk' h1 h2
  by_cases e : u' = u
  · subst e
    rw [hcu] at hc'
    obtain ⟨rfl, rfl, rfl, rfl⟩ : p = p' ∧ b = b' ∧ i = i' ∧ d = d' := by
      injection hc' with a1 a2 a3 a4; exact ⟨a1, a2, a3, a4⟩
    exact hno c hc hk' ⟨by omega, h2⟩
  · rw [hk u' hu' e] at hc'
    exact hF.fresh u' hu' p' b' i' d' hc' c hc hk' ⟨h1, h2⟩

/-! ### Alike caps -/

/-- **A new cap `d` standing for an old cap `c`** (module docstring). -/
structure RA (d c : capability.Cap) : Prop where
  key : RngKeyA d → RngKeyA c
  phys : physA d = physA c
  ptr : ptrA d = ptrA c
  size : sizeA d = sizeA c
  ut : ∀ p b i e, d = .Untyped p b i e →
    ∃ i0 e0, c = .Untyped p b i0 e0 ∧ (i0.val ≤ i.val ∨ 2 ^ b.val ≤ i.val)

theorem RA.refl (c : capability.Cap) : RA c c :=
  ⟨id, rfl, rfl, rfl, fun _ _ i e h => ⟨i, e, h, Or.inl (le_refl _)⟩⟩

theorem RA.sra {d c : capability.Cap} (h : RA d c) (p b i i' : U64) (e e' : Bool) :
    sraA (.Untyped p b i e) d = sraA (.Untyped p b i' e') c := sra_ut_congr p b i i' e e' h.phys h.ptr h.size

/-- `set_untyped_cap_as_full`'s effect on the source's cap. -/
def FullA (d c : capability.Cap) : Prop :=
  d = c ∨ ∃ p b i e i1, c = .Untyped p b i e ∧ d = .Untyped p b i1 e ∧ i1.val = 2 ^ b.val

theorem FullA.ra {d c : capability.Cap} (h : FullA d c) : RA d c := by
  rcases h with rfl | ⟨p, b, i, e, i1, rfl, rfl, hi⟩
  · exact RA.refl _
  · refine ⟨fun k => absurd k (nk_ut _ _ _ _), by rw [physA_ut, physA_ut], by rw [ptrA_ut, ptrA_ut],
      by rw [sizeA_ut, sizeA_ut], fun p' b' i' e' h => ?_⟩
    injection h with a1 a2 a3 a4
    subst a1 a2 a3 a4
    exact ⟨i, e, rfl, Or.inr (le_of_eq hi.symm)⟩

/-! ### `FreeFresh` along any step whose new caps stand for old ones -/

theorem FreeFresh.ofRA {s s' : S} (hF : FreeFresh st OS s)
    (hr : ∀ y ∈ OS, ∃ z ∈ OS, RA (capA st s' y) (capA st s z)) : FreeFresh st OS s' := by
  refine ⟨fun u hu p b i d hcu c hc hk ⟨h1, h2⟩ => ?_⟩
  obtain ⟨u0, hu0, ru⟩ := hr u hu
  obtain ⟨c0, hc0, rc⟩ := hr c hc
  obtain ⟨i0, e0, hu0c, hi⟩ := ru.ut p b i d hcu
  rcases hi with hi | hi
  · rw [rc.ptr] at h1 h2
    exact hF.fresh u0 hu0 p b i0 e0 hu0c c0 hc0 (rc.key hk) ⟨by omega, h2⟩
  · omega

/-- `FreeFresh.ofRA` where new null caps need no old cap (removal). -/
theorem FreeFresh.ofRAN {s s' : S} (hF : FreeFresh st OS s)
    (hr : ∀ y ∈ OS, capA st s' y ≠ .Null → ∃ z ∈ OS, RA (capA st s' y) (capA st s z)) : FreeFresh st OS s' := by
  refine ⟨fun u hu p b i d hcu c hc hk ⟨h1, h2⟩ => ?_⟩
  obtain ⟨u0, hu0, ru⟩ := hr u hu (by rw [hcu]; exact fun e => by cases e)
  obtain ⟨c0, hc0, rc⟩ := hr c hc (fun e => by rw [e] at hk; exact RngKeyA.not_null hk)
  obtain ⟨i0, e0, hu0c, hi⟩ := ru.ut p b i d hcu
  rcases hi with hi | hi
  · rw [rc.ptr] at h1 h2
    exact hF.fresh u0 hu0 p b i0 e0 hu0c c0 hc0 (rc.key hk) ⟨by omega, h2⟩
  · omega

/-! ### `UtRangeOrd` along renaming, recapping, insertion, removal -/

/-- **Caps and links renamed by an involution `f` of `OS`** (swap, move). -/
theorem UtRangeOrd.ren {s s' : S} (h : UtRangeOrd st OS s) {f : U64 → U64} (hf : ∀ y ∈ OS, f y ∈ OS)
    (hff : ∀ y ∈ OS, f (f y) = y) (hc : ∀ y ∈ OS, RA (capA st s' (f y)) (capA st s y))
    (hn : ∀ y ∈ OS, capA st s y ≠ .Null → NxA st s' (f y) = f (NxA st s y)) : UtRangeOrd st OS s' := by
  refine ⟨fun u' hu' p b i e hcu c' hc' hk h1 h2 => ?_⟩
  have ru := hc (f u') (hf u' hu')
  have rc := hc (f c') (hf c' hc')
  rw [hff u' hu'] at ru
  rw [hff c' hc'] at rc
  obtain ⟨i0, e0, hu0, -⟩ := ru.ut p b i e hcu
  rw [rc.ptr] at h1 h2
  have Qa := h.ord (f u') (hf u' hu') p b i0 e0 hu0 (f c') (hf c' hc') (rc.key hk) h1 h2
  have Qb := UtAbs.Path.map (nx' := NxA st s') (P' := InU st OS s' (.Untyped p b i e))
    (Q := fun z => z ∈ OS ∧ capA st s z ≠ .Null) f Qa (fun z hz => hz.os)
    (fun z hz => hn z hz.1 hz.2) (fun z hz => ⟨hf z hz.1, by
      have r := hc z hz.1
      rw [r.sra p b i i0 e e0]; exact hz.2⟩) ⟨hf u' hu', by rw [hu0]; exact fun e => by cases e⟩
  rw [hff u' hu', hff c' hc'] at Qb
  exact Qb

/-- **Links kept, caps alike** (in-place `set_cap` of an alike cap, steps keeping every `OS` word). -/
theorem UtRangeOrd.recap {s s' : S} (h : UtRangeOrd st OS s) (hn : ∀ y ∈ OS, NxA st s' y = NxA st s y)
    (hc : ∀ y ∈ OS, RA (capA st s' y) (capA st s y)) : UtRangeOrd st OS s' :=
  h.ren (f := id) (fun _ hy => hy) (fun _ _ => rfl) hc (fun y hy _ => hn y hy)

theorem UtRangeOrd.keep {s s' : S} (h : UtRangeOrd st OS s) (k : OSKeep st OS s s') : UtRangeOrd st OS s' :=
  h.recap (fun y hy => by unfold NxA; rw [(k y hy).2.2.2])
    (fun y hy => by unfold capA; rw [(k y hy).1, (k y hy).2.1]; exact RA.refl _)

theorem FreeFresh.keep {s s' : S} (h : FreeFresh st OS s) (k : OSKeep st OS s s') : FreeFresh st OS s' :=
  h.ofRA fun y hy => ⟨y, hy, by unfold capA; rw [(k y hy).1, (k y hy).2.1]; exact RA.refl _⟩

theorem revocable_congr {s s' : S} {u : U64} (h : L.mem s' (wa u 24#u64) = L.mem s (wa u 24#u64)) :
    obj.Slot.revocable st u s' = obj.Slot.revocable st u s := by
  unfold obj.Slot.revocable obj.Slot.next_word
  simp only [lift, bind_ok, cte_next, L.read_eq, h]

theorem UtRev.keep {s s' : S} (h : UtRev st OS s) (k : OSKeep st OS s s') : UtRev st OS s' := by
  intro u hu hc
  have e : capA st s' u = capA st s u := by unfold capA; rw [(k u hu).1, (k u hu).2.1]
  rw [revocable_congr (k u hu).2.2.2]; rw [e] at hc; exact h u hu hc

/-- **Insertion of `dest` after `src`** (`insert_with_cap`): the new cap and the source's rewritten cap stand for
the source's old cap; `src.NEXT := dest`, `dest.NEXT :=` the old `src.NEXT`, other links kept. -/
theorem UtRangeOrd.ins {s s' : S} (h : UtRangeOrd st OS s) {src dest : U64} (hsrc : src ∈ OS) (hd : dest ∈ OS)
    (hd0 : capA st s dest = .Null) (hk : ∀ y ∈ OS, y ≠ src → y ≠ dest → capA st s' y = capA st s y)
    (hs : RA (capA st s' src) (capA st s src)) (hdA : RA (capA st s' dest) (capA st s src))
    (hnx : ∀ y ∈ OS, y ≠ src → y ≠ dest → NxA st s' y = NxA st s y) (hns : NxA st s' src = dest)
    (hnd : NxA st s' dest = NxA st s src) : UtRangeOrd st OS s' := by
  -- every new cap stands for an old one
  have rA : ∀ y ∈ OS, y ≠ dest → RA (capA st s' y) (capA st s y) := fun y hy hyd => by
    by_cases e : y = src
    · subst e; exact hs
    · rw [hk y hy e hyd]; exact RA.refl _
  refine ⟨fun u' hu' p b i e hcu c' hc' hkc h1 h2 => ?_⟩
  -- transfer of the region predicate
  have hPd : ∀ {i0 : U64} {e0 : Bool} z, InU st OS s (.Untyped p b i0 e0) z → InU st OS s' (.Untyped p b i e) z :=
    fun {i0 e0} z hz => by
      have hzd : z ≠ dest := fun ez => by have := hz.os.2; rw [ez] at this; exact this hd0
      exact ⟨hz.1, by rw [(rA z hz.1 hzd).sra p b i i0 e e0]; exact hz.2⟩
  have hdP : ∀ {i0 : U64} {e0 : Bool}, InU st OS s (.Untyped p b i0 e0) src → InU st OS s' (.Untyped p b i e) dest :=
    fun {i0 e0} hz => ⟨hd, by rw [hdA.sra p b i i0 e e0]; exact hz.2⟩
  have hQ : ∀ {i0 : U64} {e0 : Bool} z, InU st OS s (.Untyped p b i0 e0) z → z ∈ OS ∧ z ≠ dest :=
    fun {i0 e0} z hz => ⟨hz.1, fun ez => by have := hz.os.2; rw [ez] at this; exact this hd0⟩
  have he : ∀ z, z ∈ OS ∧ z ≠ dest → z ≠ src → NxA st s' z = NxA st s z := fun z hz hzs => hnx z hz.1 hzs hz.2
  by_cases hud : u' = dest
  · -- the new cap is an `Untyped` copy: the old path from `src`
    subst hud
    obtain ⟨i0, e0, hsu, -⟩ := hdA.ut p b i e hcu
    have hcd : c' ≠ u' := fun ec => by rw [ec, hcu] at hkc; exact nk_ut _ _ _ _ hkc
    have hcs : c' ≠ src := fun ec => by
      rw [ec] at hkc; have := hs.key hkc; rw [hsu] at this; exact nk_ut _ _ _ _ this
    rw [hk c' hc' hcs hcd] at hkc h1 h2
    have Qa := h.ord src hsrc p b i0 e0 hsu c' hc' hkc h1 h2
    have hD : InU st OS s' (.Untyped p b i e) u' := ⟨hd, by
      rw [hcu]; exact sraA_self (by rw [(rA c' hc' hcd).sra p b i i0 e e0]; exact Qa.last.2) i e⟩
    cases Qa with
    | one hp => exact .of hnd (hPd _ hp)
    | step hp t =>
      exact .cons hnd (hPd _ hp) (UtAbs.Path.ins t (fun z hz => hQ z hz) he hns hnd (fun z hz => hPd z hz)
        hdP (hQ _ hp) (fun _ => hD))
  · obtain ⟨i0, e0, hu0, -⟩ := (rA u' hu' hud).ut p b i e hcu
    by_cases hcd : c' = dest
    · -- the new key cap: the old path to `src`, then `dest`
      subst hcd
      have kS := hdA.key hkc
      rw [hdA.ptr] at h1 h2
      have hus : u' ≠ src := fun eu => by rw [← eu, hu0] at kS; exact nk_ut _ _ _ _ kS
      have Qa := h.ord u' hu' p b i0 e0 hu0 src hsrc kS h1 h2
      have Qb := UtAbs.Path.ins Qa (fun z hz => hQ z hz) he hns hnd (fun z hz => hPd z hz) hdP
        ⟨hu', hud⟩ (fun eu => absurd eu hus)
      exact Qb.snoc hns (hdP Qa.last)
    · have rc := rA c' hc' hcd
      rw [rc.ptr] at h1 h2
      have Qa := h.ord u' hu' p b i0 e0 hu0 c' hc' (rc.key hkc) h1 h2
      exact UtAbs.Path.ins Qa (fun z hz => hQ z hz) he hns hnd (fun z hz => hPd z hz) hdP ⟨hu', hud⟩
        (fun eu => ⟨hd, by
          rw [hdA.sra p b i i0 e e0, ← eu, hu0]
          exact sraA_self Qa.last.2 i0 e0⟩)

/-- **Removal of `x`** (`empty_slot`): `x` ends null, other caps kept, a member whose `NEXT` was `x` now points at
`x`'s `NEXT`, other members' links kept. -/
theorem UtRangeOrd.rem {s s' : S} (h : UtRangeOrd st OS s) {x : U64} (hx0 : capA st s' x = .Null)
    (hk : ∀ y ∈ OS, y ≠ x → capA st s' y = capA st s y) (hxx : NxA st s x ≠ x)
    (hnx : ∀ y ∈ OS, capA st s y ≠ .Null → y ≠ x →
      NxA st s' y = if NxA st s y = x then NxA st s x else NxA st s y) : UtRangeOrd st OS s' := by
  refine ⟨fun u' hu' p b i e hcu c' hc' hkc h1 h2 => ?_⟩
  have hux : u' ≠ x := fun eu => by rw [eu, hx0] at hcu; cases hcu
  have hcx : c' ≠ x := fun ec => by rw [ec, hx0] at hkc; exact RngKeyA.not_null hkc
  rw [hk u' hu' hux] at hcu
  rw [hk c' hc' hcx] at hkc h1 h2
  have Qa := h.ord u' hu' p b i e hcu c' hc' hkc h1 h2
  exact (UtAbs.Path.rem (Q := fun z => z ∈ OS ∧ capA st s z ≠ .Null) (P' := InU st OS s' (.Untyped p b i e))
    Qa (fun z hz => hz.os) hxx (fun z hz hzx => hnx z hz.1 hz.2 hzx)
    (fun z hz hzx => ⟨hz.1, by rw [hk z hz.1 hzx]; exact hz.2⟩) hcx).1 ⟨hu', by rw [hcu]; exact fun e => by cases e⟩ hux

/-- **Removal with `MdbLk`'s link facts** (the form `MdbLk.rem` and `cdt.empty_slot.mdbFL` use): every other `OS`
slot but `x`'s `PREV` keeps its `NEXT`, the `PREV` takes `x`'s `NEXT`. -/
theorem UtRangeOrd.remL {G : List (List U64)} {s s' : S} (h : UtRangeOrd st OS s) (hM : MdbLk st OS G s)
    (h0 : ∀ y ∈ OS, y ≠ 0#u64) {x : U64} (hxG : x ∈ G.flatten) (hx0 : capA st s' x = .Null)
    (hk : ∀ y ∈ OS, y ≠ x → capA st s' y = capA st s y)
    (hnx : ∀ y ∈ OS, y ≠ x → y ≠ L.mem s (wa x 16#u64) → NxA st s' y = NxA st s y)
    (hP : L.mem s (wa x 16#u64) ≠ 0#u64 → NxA st s' (L.mem s (wa x 16#u64)) = NxA st s x) :
    UtRangeOrd st OS s' := by
  have F := hM.lkF h0
  refine h.rem hx0 hk (F.nxne x hxG) fun y hy hy0 hyx => ?_
  have hyG : y ∈ G.flatten := (hM.members y).2 ⟨hy, hy0⟩
  by_cases e : y = L.mem s (wa x 16#u64)
  · have hp0 : L.mem s (wa x 16#u64) ≠ 0#u64 := by rw [← e]; exact h0 y hy
    have hx : NxA st s y = x := by rw [e]; exact F.pvnx x hxG hp0
    rw [if_pos hx, e]; exact hP hp0
  · have hx : NxA st s y ≠ x := fun ex => by
      have := F.nxpv y hyG (by rw [ex]; exact h0 x ((hM.members x).1 hxG).1)
      rw [ex] at this; exact e this.symm
    rw [if_neg hx]; exact hnx y hy hyx e

end gen

/-! ## Function level -/

section fn
variable {OS : Set U64} {G : List (List U64)}

set_option maxHeartbeats 1000000 in
/-- **`swap`** of two distinct canonical members writing encodable caps that stand for the replaced ones. -/
theorem cdt.swap.ut (hO : OSOK T Ω Sg OS) {s : S} (hM : MdbLk st OS G s) (hU : UtRangeOrd st OS s)
    (hF : FreeFresh st OS s) {x1 x2 : U64} {c1 c2 : capability.Cap} (hx1 : x1 ∈ G.flatten) (hx2 : x2 ∈ G.flatten)
    (hne : x1 ≠ x2) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) (hw1 : CapRt.EncWf c1)
    (hw2 : CapRt.EncWf c2) (ha1 : RA c1 (capA st s x1)) (ha2 : RA c2 (capA st s x2)) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => UtRangeOrd st OS s' ∧ FreeFresh st OS s' ⦄ := by
  have h0 : ∀ y ∈ OS, y ≠ 0#u64 := hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have o1 := inOS x1 hx1
  have o2 := inOS x2 hx2
  refine WP.spec_mono (cdt.swap.lrW hO (LR.self s) o1 o2 hne hs1 hs2 hw1 hw2
    (fun h => inOS _ (F.pvm _ hx1 h)) (fun h => inOS _ (F.nxm _ hx1 h))
    (fun h => inOS _ (F.pvm _ hx2 h)) (fun h => inOS _ (F.nxm _ hx2 h))) ?_
  rintro s' ⟨hL, e1, e2, ek⟩
  have hc : ∀ y ∈ OS, RA (capA st s' (swp x1 x2 y)) (capA st s y) := by
    intro y hy
    unfold swp
    by_cases a1 : y = x1
    · rw [a1, if_pos rfl, e2]; exact ha1
    · rw [if_neg a1]
      by_cases a2 : y = x2
      · rw [a2, if_pos rfl, e1]; exact ha2
      · rw [if_neg a2, ek y hy a1 a2]; exact RA.refl _
  refine ⟨hU.ren (fun y hy => swp_os o1 o2 hy) (fun y _ => swp_swp x1 x2 y) hc (fun y hy hy0 => ?_),
    hF.ofRA fun y hy => ⟨swp x1 x2 y, swp_os o1 o2 hy, by have := hc _ (swp_os o1 o2 hy); rwa [swp_swp] at this⟩⟩
  have hyG : y ∈ G.flatten := (hM.members y).2 ⟨hy, hy0⟩
  rw [(hL _ (swp_os o1 o2 hy)).2, swp_tr, swp_tr]; exact (LkAbs.sw_ok F hx1 hx2 hne hyG).1

/-- **`cap_swap_for_delete`** of two canonical members (equal slots return the state). -/
theorem cdt.cap_swap_for_delete.ut (hO : OSOK T Ω Sg OS) {s : S} (hM : MdbLk st OS G s)
    (hU : UtRangeOrd st OS s) (hF : FreeFresh st OS s) {x1 x2 : U64} (hx1 : x1 ∈ G.flatten)
    (hx2 : x2 ∈ G.flatten) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => UtRangeOrd st OS s' ∧ FreeFresh st OS s' ⦄ := by
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · exact (WP.spec_ok _).2 ⟨hU, hF⟩
  · rename_i hne'
    have hne : x1 ≠ x2 := by simpa using hne'
    rw [capA_eq, bind_ok, capA_eq, bind_ok]
    exact cdt.swap.ut hO hM hU hF hx1 hx2 hne hs1 hs2 (CapRt.decodeF_encWf _ _) (CapRt.decodeF_encWf _ _)
      (RA.refl _) (RA.refl _)

set_option maxHeartbeats 1000000 in
/-- **`move_cap`** of a member into a null canonical slot, the new cap standing for the source's. -/
theorem cdt.move_cap.ut (hO : OSOK T Ω Sg OS) {s : S} (hM : MdbLk st OS G s) (hU : UtRangeOrd st OS s)
    (hF : FreeFresh st OS s) {src dest : U64} {nc : capability.Cap} (hsG : src ∈ G.flatten) (hd : dest ∈ OS)
    (hd0 : capA st s dest = .Null) (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc)
    (hal : RA nc (capA st s src)) :
    cdt.move_cap st s nc src dest ⦃ s' => UtRangeOrd st OS s' ∧ FreeFresh st OS s' ⦄ := by
  have h0 : ∀ y ∈ OS, y ≠ 0#u64 := hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have hsrc := inOS src hsG
  have hdG : dest ∉ G.flatten := fun m => ((hM.members dest).1 m).2 hd0
  have hsd : src ≠ dest := fun e => hdG (e ▸ hsG)
  have r1 : ∀ y, y ∈ G.flatten → NxA st s y ≠ dest ∧ L.mem s (wa y 16#u64) ≠ dest :=
    fun y hy => ⟨fun e => hdG (by rw [← e]; exact F.nxm y hy (by rw [e]; exact h0 dest hd)),
      fun e => hdG (by rw [← e]; exact F.pvm y hy (by rw [e]; exact h0 dest hd))⟩
  refine WP.spec_mono (cdt.move_cap.lr hO (LR.self s) hsrc hd hsd hdc hw
    (fun h => inOS _ (F.pvm _ hsG h)) (fun h => inOS _ (F.nxm _ hsG h))) ?_
  rintro s' ⟨hL, ed, es, ek⟩
  have hc : ∀ y ∈ OS, RA (capA st s' (swp dest src y)) (capA st s y) := by
    intro y hy
    unfold swp
    by_cases a1 : y = dest
    · rw [a1, if_pos rfl, es, hd0]; exact RA.refl _
    · rw [if_neg a1]
      by_cases a2 : y = src
      · rw [a2, if_pos rfl, ed]; exact hal
      · rw [if_neg a2, ek y hy a2 a1]; exact RA.refl _
  refine ⟨hU.ren (fun y hy => swp_os hd hsrc hy) (fun y _ => swp_swp dest src y) hc (fun y hy hy0 => ?_),
    hF.ofRA fun y hy => ⟨swp dest src y, swp_os hd hsrc hy, by
      have := hc _ (swp_os hd hsrc hy); rwa [swp_swp] at this⟩⟩
  have hyG : y ∈ G.flatten := (hM.members y).2 ⟨hy, hy0⟩
  rw [(hL _ (swp_os hd hsrc hy)).2, swp_tr, swp_tr]
  exact (LkAbs.mv_ok F hdG (fun y hy => r1 y hy) hsG hyG).1

/-- **`set_untyped_cap_as_full`**: the source's cap is kept or made a full `Untyped` of the same region. -/
theorem cdt.set_untyped_cap_as_full.full (hO : OSOK T Ω Sg OS) {s : S} {src : U64} (hsrc : src ∈ OS)
    {sc nc : capability.Cap} (hsc : capA st s src = sc) :
    cdt.set_untyped_cap_as_full st s sc nc src ⦃ s1 => FullA (capA st s1 src) sc ⦄ := by
  have same : FullA (capA st s src) sc := Or.inl hsc
  have hd : capability.Cap.decode (L.mem s src) (L.mem s (wa src 8#u64)) = ok sc := by
    have e := capA_eq (st := st) s src; rw [DPF.slot_cap_dec, hsc] at e; exact e
  cases sc with
  | Untyped p b i d =>
    cases nc with
    | Untyped p' b' i' d' =>
      simp only [cdt.set_untyped_cap_as_full]
      by_cases e1 : p = p'
      · rw [if_pos e1]
        by_cases e2 : b = b'
        · rw [if_pos e2]
          simp only [lift, bind_ok]
          have wf0 := CapRt.decode_encWf hd
          have hb : b.val < 64 := wf0.2
          refine WP.spec_bind (shl1_val hb) fun i1 hi1 => ?_
          have wf : CapRt.EncWf (.Untyped p b i1 d) := wf0
          obtain ⟨w0, w1, he, hr⟩ := CapRt.decode_encode _ wf
          rw [set_cap_eq he, WP.spec_ok]
          exact Or.inr ⟨p, b, i, d, i1, rfl, capA_wr2_self hO hsrc hr, hi1⟩
        · rw [if_neg e2]; exact (WP.spec_ok _).2 same
      · rw [if_neg e1]; exact (WP.spec_ok _).2 same
    | _ => exact (WP.spec_ok _).2 same
  | _ => exact (WP.spec_ok _).2 same

set_option maxHeartbeats 1000000 in
/-- **`insert_with_cap`'s effect on the source's cap**: `set_untyped_cap_as_full`'s, the later writes keep it. -/
theorem cdt.insert_with_cap.srcF (hO : OSOK T Ω Sg OS) {s : S} {src dest : U64} {nc sc : capability.Cap}
    (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest) (hsc : capA st s src = sc) (hw : CapRt.EncWf nc)
    (hnN : NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => FullA (capA st s' src) sc ⦄ := by
  unfold cdt.insert_with_cap
  refine WP.spec_bind (P0.objects.is_cap_revocable.p0 nc sc) fun rv _ => ?_
  rw [next_eq, bind_ok]
  refine WP.spec_bind (cdt.set_untyped_cap_as_full.full hO hsrc (nc := nc) hsc) fun s1 h1 => ?_
  obtain ⟨w0, w1, he, hr⟩ := CapRt.decode_encode nc hw
  rw [set_cap_eq he, bind_ok]
  have C2 : capA st (L.wr (L.wr s1 dest w0) (wa dest 8#u64) w1) src = capA st s1 src :=
    capA_wr2_other hO hd hsrc hsd
  generalize L.wr (L.wr s1 dest w0) (wa dest 8#u64) w1 = s2 at C2 ⊢
  rw [set_prev_eq, bind_ok]
  refine WP.spec_bind (set_nf_spec _ dest _ rv rv) ?_
  rintro s4 ⟨w4, rfl, -⟩
  rw [set_next_eq, bind_ok]
  have fin : ∀ s' : S, CK st OS s2 s' → FullA (capA st s' src) sc := fun s' hc => by
    rw [hc src hsrc, C2]; exact h1
  simp only [obj.Slot.is_null, bind_ok]
  split
  · exact (WP.spec_ok _).2 (fin _ ((((CK.refl (st := st) (OS := OS) s2).p hO hd src).n hO hd w4).n hO hsrc _))
  · rename_i hn0
    have hN0 : NxA st s src ≠ 0#u64 := by simpa using hn0
    rw [set_prev_eq, WP.spec_ok]
    exact fin _ (((((CK.refl (st := st) (OS := OS) s2).p hO hd src).n hO hd w4).n hO hsrc _).p hO (hnN hN0) dest)

set_option maxHeartbeats 1000000 in
/-- **`insert_with_cap`** of a non-null encodable cap standing for the source's into a null canonical slot. -/
theorem cdt.insert_with_cap.ut (hO : OSOK T Ω Sg OS) {s : S} (hM : MdbLk st OS G s) (hU : UtRangeOrd st OS s)
    (hF : FreeFresh st OS s) {src dest : U64} {nc sc : capability.Cap} (hsrc : src ∈ G.flatten) (hd : dest ∈ OS)
    (hd0 : capA st s dest = .Null) (hdc : obj.sext48 dest = ok dest) (hsc : capA st s src = sc)
    (hw : CapRt.EncWf nc) (hA : RA nc sc) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => UtRangeOrd st OS s' ∧ FreeFresh st OS s' ⦄ := by
  have h0 : ∀ y ∈ OS, y ≠ 0#u64 := hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have os := inOS src hsrc
  have hs0 : capA st s src ≠ .Null := ((hM.members src).1 hsrc).2
  have hsc0 : sc ≠ .Null := by rw [← hsc]; exact hs0
  have dG : dest ∉ G.flatten := fun hm => ((hM.members dest).1 hm).2 hd0
  have hsd : src ≠ dest := fun e => dG (e ▸ hsrc)
  have hNm : NxA st s src ≠ 0#u64 → NxA st s src ∈ G.flatten := F.nxm _ hsrc
  refine WP.spec_mono (WP.spec_and (cdt.insert_with_cap.lr hO (LR.self s) os hd hsd hdc hsc hsc0 hw
    (fun h => inOS _ (hNm h))) (cdt.insert_with_cap.srcF hO os hd hsd hsc hw (fun h => inOS _ (hNm h)))) ?_
  rintro s' ⟨⟨hL, ed, -, -, ek, -⟩, hfs⟩
  have hs : RA (capA st s' src) (capA st s src) := by rw [hsc]; exact hfs.ra
  have hdA : RA (capA st s' dest) (capA st s src) := by rw [ed, hsc]; exact hA
  refine ⟨hU.ins os hd hd0 ek hs hdA (fun y hy h1 h2 => ?_) ?_ ?_, hF.ofRA fun y hy => ?_⟩
  · rw [(hL y hy).2]; simp [h1, h2]
  · rw [(hL src os).2]; simp
  · rw [(hL dest hd).2]; simp [hsd.symm]
  · by_cases e1 : y = dest
    · exact ⟨src, os, by rw [e1]; exact hdA⟩
    · by_cases e2 : y = src
      · exact ⟨src, os, by rw [e2]; exact hs⟩
      · exact ⟨y, hy, by rw [ek y hy e2 e1]; exact RA.refl _⟩

set_option maxHeartbeats 1000000 in
/-- **`empty_slot`** of an `OS` slot (gen 49's cleanup hypotheses; `cdt.empty_slot.mdbFL`). -/
theorem cdt.empty_slot.ut {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) {s : S}
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) (hU : UtRangeOrd st OS s)
    (hF : FreeFresh st OS s) {a : A} {x : U64} (hx : x ∈ OS) {cl : capability.Cap} {Pw : U64 → Prop}
    (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => UtRangeOrd st OS r.1 ∧ FreeFresh st OS r.1 ⦄ := by
  refine WP.spec_mono (cdt.empty_slot.mdbFL hO hO.nz hM hRO hK hx hpw hpcd) ?_
  rintro r ⟨⟨_, -, -, -, hcr, -, hx0, -⟩, hl, hl0⟩
  refine ⟨?_, hF.ofRAN fun y hy hy0 => ⟨y, hy, ?_⟩⟩
  · by_cases hn : capA st s x = .Null
    · exact hU.recap (hl0 hn) fun y hy => by
        by_cases e : y = x
        · rw [e, hx0, hn]; exact RA.refl _
        · rw [hcr y hy e]; exact RA.refl _
    · exact hU.remL hM hO.nz ((hM.members x).2 ⟨hx, hn⟩) hx0 hcr (hl hn).1 (hl hn).2
  · have e : y ≠ x := fun e => hy0 (by rw [e]; exact hx0)
    rw [hcr y hy e]; exact RA.refl _

/-- **`insert`** (the source cap read from `src`). -/
theorem cdt.insert.ut (hO : OSOK T Ω Sg OS) {s : S} (hM : MdbLk st OS G s) (hU : UtRangeOrd st OS s)
    (hF : FreeFresh st OS s) {src dest : U64} {nc : capability.Cap} (hsrc : src ∈ G.flatten) (hd : dest ∈ OS)
    (hd0 : capA st s dest = .Null) (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc)
    (hA : RA nc (capA st s src)) :
    cdt.insert st s nc src dest ⦃ s' => UtRangeOrd st OS s' ∧ FreeFresh st OS s' ⦄ := by
  unfold cdt.insert
  rw [capA_eq, bind_ok]
  exact cdt.insert_with_cap.ut hO hM hU hF hsrc hd hd0 hdc rfl hw hA

end fn

end ST
end R
end W7

end

end Fl4ProofsA64.P1
