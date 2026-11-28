/-
P1 (aarch64, gen 47): **`MdbLk`, `RngOneA64` and `KindA` along a renaming of two slots** — the data step of
`cdt::swap` (cdt.rs:67–; seL4 `cteSwap`: the two caps exchange slots together with their MDB nodes, so the chain
order of caps is unchanged and the ghost is renamed, P3's `renG G (Equiv.swap s1 s2)`).

* `swp x1 x2 y` (the transposition), `renG x1 x2 G` (every chain mapped by it); `swp_swp`, `swp_zero`, `swp_os`.
* **`MdbLk.ren`**: at the state after, every `OS` slot `y`'s cap now sits at `swp y`, and for the members (non-null
  caps) `NEXT` / `PREV` sit at `swp y` and are renamed (`swp 0 = 0`) ⇒ `MdbLk OS (renG x1 x2 G)`.
* **`RngOneA64.ren`**, **`KindA.ren`** (caps moved by the transposition).

The function-level `cdt::swap` instance is not in this file (see the handoff). No named premise.
-/
import Fl4ProofsA64.P1.MdbEmpty
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- The transposition of `x1` and `x2`. -/
def swp (x1 x2 y : U64) : U64 := if y = x1 then x2 else if y = x2 then x1 else y

/-- The ghost renamed by the transposition. -/
def renG (x1 x2 : U64) (G : List (List U64)) : List (List U64) := G.map (List.map (swp x1 x2))

theorem swp_swp (x1 x2 y : U64) : swp x1 x2 (swp x1 x2 y) = y := by
  unfold swp
  by_cases h1 : y = x1
  · subst h1; by_cases h2 : x2 = y <;> simp [h2]
  · by_cases h2 : y = x2
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem swp_inj (x1 x2 : U64) : Function.Injective (swp x1 x2) := fun a b e => by
  rw [← swp_swp x1 x2 a, e, swp_swp]

theorem swp_zero {x1 x2 : U64} (h1 : x1 ≠ 0#u64) (h2 : x2 ≠ 0#u64) : swp x1 x2 0#u64 = 0#u64 := by
  unfold swp; rw [if_neg (Ne.symm h1), if_neg (Ne.symm h2)]

theorem swp_os {OS : Set U64} {x1 x2 : U64} (h1 : x1 ∈ OS) (h2 : x2 ∈ OS) {y : U64} (hy : y ∈ OS) :
    swp x1 x2 y ∈ OS := by
  unfold swp; split
  · exact h2
  · split
    · exact h1
    · exact hy

theorem renG_flat (x1 x2 : U64) (G : List (List U64)) :
    (renG x1 x2 G).flatten = G.flatten.map (swp x1 x2) := by
  unfold renG; rw [List.map_flatten]

theorem mem_renG_flat {x1 x2 : U64} {G : List (List U64)} {y : U64} :
    y ∈ (renG x1 x2 G).flatten ↔ swp x1 x2 y ∈ G.flatten := by
  rw [renG_flat, List.mem_map]
  constructor
  · rintro ⟨y0, hy0, rfl⟩; rw [swp_swp]; exact hy0
  · intro h; exact ⟨_, h, swp_swp x1 x2 y⟩

section ren
variable {OS : Set U64} {G : List (List U64)}

/-- **`MdbLk` along the renaming** (module docstring). -/
theorem MdbLk.ren {s s' : S} (h : MdbLk st OS G s) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {x1 x2 : U64} (hx1 : x1 ∈ OS)
    (hx2 : x2 ∈ OS) (hc : ∀ y ∈ OS, capA st s' (swp x1 x2 y) = capA st s y)
    (hn : ∀ y ∈ G.flatten, NxA st s' (swp x1 x2 y) = swp x1 x2 (NxA st s y))
    (hp : ∀ y ∈ G.flatten, L.mem s' (wa (swp x1 x2 y) 16#u64) = swp x1 x2 (L.mem s (wa y 16#u64))) :
    MdbLk st OS (renG x1 x2 G) s' := by
  have hz := swp_zero (h0 x1 hx1) (h0 x2 hx2)
  have mem : ∀ ch ∈ G, ∀ {i : Nat} {a : U64}, ch[i]? = some a → a ∈ G.flatten := fun ch hch _ _ e =>
    List.mem_flatten.2 ⟨ch, hch, List.mem_of_getElem? e⟩
  refine ⟨?_, fun ch hch => ?_, fun ch hch i a b ha hb => ?_, fun ch hch a ha => ?_, fun ch hch a ha => ?_,
    fun y => ?_⟩
  · rw [renG_flat]; exact h.nodup.map (swp_inj x1 x2)
  · obtain ⟨c, hc0, rfl⟩ := List.mem_map.1 hch
    simpa using h.ne_nil c hc0
  · obtain ⟨c, hc0, rfl⟩ := List.mem_map.1 hch
    rw [List.getElem?_map] at ha hb
    obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.1 ha
    obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
    have old := h.chain c hc0 i a0 b0 ha0 hb0
    exact ⟨by rw [hn a0 (mem c hc0 ha0), old.1], by rw [hp b0 (mem c hc0 hb0), old.2]⟩
  · obtain ⟨c, hc0, rfl⟩ := List.mem_map.1 hch
    rw [List.head?_map] at ha
    obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.1 ha
    have a0m : a0 ∈ G.flatten := List.mem_flatten.2 ⟨c, hc0, List.mem_of_mem_head? ha0⟩
    rw [hp a0 a0m, h.head c hc0 a0 ha0, hz]
  · obtain ⟨c, hc0, rfl⟩ := List.mem_map.1 hch
    rw [List.getLast?_map] at ha
    obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.1 ha
    have a0m : a0 ∈ G.flatten := List.mem_flatten.2 ⟨c, hc0, List.mem_of_getLast? ha0⟩
    rw [hn a0 a0m, h.last c hc0 a0 ha0, hz]
  · rw [mem_renG_flat, h.members]
    constructor
    · rintro ⟨hy, hcy⟩
      have hyO : y ∈ OS := by rw [← swp_swp x1 x2 y]; exact swp_os hx1 hx2 hy
      refine ⟨hyO, ?_⟩
      rw [← swp_swp x1 x2 y, hc _ hy]; exact hcy
    · rintro ⟨hy, hcy⟩
      refine ⟨swp_os hx1 hx2 hy, ?_⟩
      rw [← hc _ (swp_os hx1 hx2 hy), swp_swp]; exact hcy

/-- **`RngOneA64` along the renaming.** -/
theorem RngOneA64.ren {s s' : S} (h : RngOneA64 st G s) {x1 x2 : U64}
    (hc : ∀ y ∈ G.flatten, capA st s' (swp x1 x2 y) = capA st s y) : RngOneA64 st (renG x1 x2 G) s' := by
  refine ⟨fun y hy y' hy' k k' hcl => ?_, fun ch hch i j k y z y' hi hj hk hij hjk ky ky' hcl => ?_⟩
  · have a := mem_renG_flat.1 hy
    have a' := mem_renG_flat.1 hy'
    have e : capA st s' y = capA st s (swp x1 x2 y) := by rw [← hc _ a, swp_swp]
    have e' : capA st s' y' = capA st s (swp x1 x2 y') := by rw [← hc _ a', swp_swp]
    rw [e] at k hcl; rw [e'] at k' hcl
    obtain ⟨c, hc0, h1, h2⟩ := h.one _ a _ a' k k' hcl
    refine ⟨_, List.mem_map.2 ⟨c, hc0, rfl⟩, ?_, ?_⟩
    · exact List.mem_map.2 ⟨_, h1, swp_swp x1 x2 y⟩
    · exact List.mem_map.2 ⟨_, h2, swp_swp x1 x2 y'⟩
  · obtain ⟨c, hc0, rfl⟩ := List.mem_map.1 hch
    rw [List.getElem?_map] at hi hj hk
    obtain ⟨y0, hy0, rfl⟩ := Option.map_eq_some_iff.1 hi
    obtain ⟨z0, hz0, rfl⟩ := Option.map_eq_some_iff.1 hj
    obtain ⟨y1, hy1, rfl⟩ := Option.map_eq_some_iff.1 hk
    have mem : ∀ {n : Nat} {w : U64}, c[n]? = some w → w ∈ G.flatten := fun e =>
      List.mem_flatten.2 ⟨c, hc0, List.mem_of_getElem? e⟩
    rw [hc _ (mem hy0)] at ky hcl ⊢; rw [hc _ (mem hy1)] at ky' hcl; rw [hc _ (mem hz0)]
    exact h.chunk c hc0 i j k y0 z0 y1 hy0 hz0 hy1 hij hjk ky ky' hcl

/-- **`KindA` along the renaming.** -/
theorem KindA.ren {s s' : S} (h : KindA st OS s) {x1 x2 : U64} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS)
    (hc : ∀ y ∈ OS, capA st s' (swp x1 x2 y) = capA st s y) : KindA st OS s' := by
  have e : ∀ y ∈ OS, capA st s' y = capA st s (swp x1 x2 y) := fun y hy => by
    rw [← hc _ (swp_os hx1 hx2 hy), swp_swp]
  refine ⟨fun y hy y' hy' k k' hp => ?_⟩
  rw [e y hy] at k hp ⊢; rw [e y' hy'] at k' hp ⊢
  exact h.kind _ (swp_os hx1 hx2 hy) _ (swp_os hx1 hx2 hy') k k' hp

end ren

end ST
end R
end W7

end

end Fl4ProofsA64.P1
