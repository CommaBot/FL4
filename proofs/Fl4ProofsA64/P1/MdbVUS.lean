/-
P1 (aarch64, gen 58): **the RAM reset's unified shrink** — the heap drops the untyped's region `R = [p, p + 2^b)`
(`H.drop (RegionD H p (p + 2^b))`, gen 53's `HeapWin.drop` / `utHeap` model) and `OS` drops the slots meeting it
(`OffR`), with the companion fact that every dropped slot is null.

* **`OffR lo hi OS`**: the `OS` slots apart from `[lo, hi)`; `OSOK.offR` (a subset keeps the placement).
* **The companion fact.** **`reset_null`**: every `OS` slot meeting the region of an `Untyped` slot `u` without
  descendants (`ensure_no_children`, `cdt.ensure_no_children.noDesc`) is null — from `UtInvA` (`reg`, `drange`,
  `anc`) **and `CoverA`**: every non-null `OS` slot lies (all 32 bytes) inside the range of a physical
  non-untyped `OS` cap (l4v Invariants_AI `if_unsafe_then_cap` / `ex_cte_cap_wp_to`: a non-null cte's object is
  named by a cap — a CNode / TCB / Zombie cap here). The covering cap meets the region, so `drange` makes it a
  descendant of `u` (excluded) or an ancestor (then untyped by `anc`, excluded). **`CoverA` is not derivable from
  the carried facts** (`UtInvA` / `MdbST` speak of caps, not of where slots lie; `CapIn` is forward only), so it is a
  case hypothesis of `reset_null` here, not a premise; see the gen-58 handoff.
* **Shrinking `OS` by null slots** (mirror of gen 55's `TreeA.grow`): `UtInvA.shrink`, **`MdbST.sub`**,
  `UtRev.sub`; `ValidUntypedA.sub` (MdbVU).
* **`ValidUntypedA.reset`**: after the reset, over `H.drop (RegionD …)` and `OffR`: the reset slot's untyped (any
  free index) sees no kept object in its region; the other kept slots are as before.
* **`OSKeep.clearR`**: a write frame inside the region (`clear_free` of a chunk, untyped.rs:239 / 245) keeps every
  `OffR` slot's words. **`reset_start`**: `MdbST ∧ UtRev ∧ ValidUntypedA` over `OS` and `H` with `CoverA` and a
  childless untyped give the three over `OffR` and the dropped heap at the reset's start (the region's slots null,
  the dropped objects off every kept slot's view).

Not here (owed): the chunked loop itself (`reset_untyped_loop`: the clear step is `OSKeep.clearR`, the final
`set_cap` gen 55's `TreeA.lowerW`, the preemption point an `OSKeep` under `JV`, as `LoopMZ.pre`).

No named premise; new definitions and theorems only (`CoverA` a case hypothesis of `reset_null` / `reset_start`).
-/
import Fl4ProofsA64.P1.MdbVUC
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- **The `OS` slots apart from `[lo, hi)`.** -/
def OffR (lo hi : Nat) (OS : Set U64) : Set U64 := {x | x ∈ OS ∧ (x.val + 32 ≤ lo ∨ hi ≤ x.val)}

/-- **l4v `if_unsafe_then_cap` / `ex_cte_cap_wp_to`, A64 form** (module docstring): every non-null `OS` slot lies
inside the range of a physical non-untyped `OS` cap. -/
def CoverA (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) : Prop :=
  ∀ y ∈ OS, capA st s y ≠ .Null → ∃ z ∈ OS, physA (capA st s z) = true ∧ isUtA (capA st s z) = false ∧
    baseA (capA st s z) ≤ y.val ∧ y.val + 31 ≤ topA (capA st s z)

variable {OS : Set U64} {par : U64 → Option U64}

theorem OffR.sub {lo hi : Nat} : OffR lo hi OS ⊆ OS := fun _ h => h.1

theorem OSOK.offR {lo hi : Nat} (h : OSOK T Ω Sg OS) : OSOK T Ω Sg (OffR lo hi OS) :=
  ⟨fun x hx => h.slot x hx.1, fun x hx => h.fit x hx.1, fun x hx y hy => h.disj x hx.1 y hy.1,
    fun x hx => h.nz x hx.1⟩

/-! ## The companion fact -/

/-- **Every `OS` slot meeting a childless untyped's region is null** (module docstring). -/
theorem reset_null {s : S} (hU : UtInvA st OS par s) (hC : CoverA st OS s) {u p b i : U64} {d : Bool}
    (hu : u ∈ OS) (hcu : capA st s u = .Untyped p b i d) (hnd : ∀ y, ¬ Mdb.Desc par y u) :
    ∀ y ∈ OS, ¬ (y.val + 32 ≤ p.val ∨ p.val + 2 ^ b.val ≤ y.val) → capA st s y = .Null := by
  intro y hy hm
  by_contra hn
  obtain ⟨z, hz, hp, hnu, h1, h2⟩ := hC y hy hn
  obtain ⟨rb, rt, -⟩ := ut_rangeA (capA_ut_b hcu) (by
    have := hU.reg u hu (by rw [hcu]; exact physA_ut _ _ _ _); rwa [hcu] at this)
  have hb1 : 1 ≤ 2 ^ b.val := Nat.one_le_two_pow
  have hzu : z ≠ u := fun e => by rw [e, hcu] at hnu; simp [isUtA] at hnu
  have hD : ¬ DisjA (capA st s z) (capA st s u) := by
    unfold DisjA; rw [hcu, rb, rt]; omega
  rcases hU.drange u hu p b i d hcu z hz hzu hp hD with g | g
  · exact hnd z g
  · have := hU.anc z u g (by rw [hcu]; rfl)
    rw [hnu] at this; cases this

/-! ## Shrinking `OS` by null slots -/

theorem UtInvA.shrink {OS' : Set U64} {s : S} (h : UtInvA st OS par s) (hs : OS' ⊆ OS) : UtInvA st OS' par s :=
  ⟨fun x hx => h.reg x (hs hx), fun x hx => h.inc x (hs hx),
    fun x hx p b i d hc y hy => h.noov x (hs hx) p b i d hc y (hs hy),
    fun x hx y hy => h.excl x (hs hx) y (hs hy), fun x hx => h.fib x (hs hx),
    fun x hx p b i d hc y hy => h.drange x (hs hx) p b i d hc y (hs hy), h.anc⟩

/-- **`MdbST` over `OS` shrunk by null slots** (the ghosts kept). -/
theorem MdbST.sub {OS' : Set U64} {s : S} (h : MdbST st OS s) (hs : OS' ⊆ OS)
    (hn : ∀ x ∈ OS, x ∉ OS' → capA st s x = .Null) : MdbST st OS' s := by
  obtain ⟨G, par, hM, hRO, hK, hN, hC, hTr, hU⟩ := h
  refine ⟨G, par, ⟨hM.nodup, hM.ne_nil, hM.chain, hM.head, hM.last, fun x => ?_⟩, hRO,
    ⟨fun x hx y hy => hK.kind x (hs hx) y (hs hy)⟩, fun x hx => hN x (hs hx),
    ⟨fun x hx y hy => hC.cls x (hs hx) y (hs hy)⟩, hTr, hU.shrink hs⟩
  rw [hM.members x]
  constructor
  · rintro ⟨hx, hc⟩
    by_cases h' : x ∈ OS'
    · exact ⟨h', hc⟩
    · exact absurd (hn x hx h') hc
  · rintro ⟨hx, hc⟩; exact ⟨hs hx, hc⟩

theorem UtRev.sub {OS' : Set U64} {s : S} (h : UtRev st OS s) (hs : OS' ⊆ OS) : UtRev st OS' s :=
  fun u hu => h u (hs hu)

/-! ## The reset's end -/

/-- **`ValidUntypedA` over the dropped heap and `OffR` after the reset** (module docstring). -/
theorem ValidUntypedA.reset {H : Heap} {s s' : S} (h : ValidUntypedA st H OS s) {OS' : Set U64} (hs : OS' ⊆ OS)
    {u p b i' : U64} {d : Bool} (hcu : capA st s' u = .Untyped p b i' d)
    (hk : ∀ y ∈ OS', y ≠ u → capA st s' y = capA st s y) :
    ValidUntypedA st (H.drop (RegionD H p.val (p.val + 2 ^ b.val))) OS' s' := by
  intro y hy p' b' i'' hcy q k hq
  obtain ⟨hnD, hq0⟩ := Heap.drop_eq_some.1 hq
  by_cases e : y = u
  · rw [e, hcu] at hcy
    injection hcy with a1 a2 a3 a4
    subst a1 a2 a3
    unfold RegionD MeetsR at hnD
    rw [hq0] at hnD
    simp only [Option.elim, not_not] at hnD
    rcases hnD with g | g
    · left; omega
    · right; exact g
  · rw [hk y hy e] at hcy
    exact h y (hs hy) p' b' i'' hcy q k hq0

/-- **A write frame inside the region keeps every `OffR` slot's words.** -/
theorem OSKeep.clearR (hO : OSOK T Ω Sg OS) {lo hi : Nat} {s s' : S} {F : U64 → Prop} (hw : WritesIn st s s' F)
    (hF : ∀ b, F b → lo ≤ b.val ∧ b.val < hi) : OSKeep st (OffR lo hi OS) s s' :=
  OSKeep.of_off hO.offR hw fun y hy o ho h8 hb => by
    have hv := wv (hO.fit y hy.1) ho
    have := hF _ hb
    rcases hy.2 with g | g <;> omega

/-- **The reset's start over the shrunk sets** (module docstring): `OffR` of the region, the dropped heap. -/
theorem reset_start {H : Heap} {s : S} (hS : MdbST st OS s) (hR : UtRev st OS s) (hV : ValidUntypedA st H OS s)
    (hC : CoverA st OS s) {u p b i : U64} {d : Bool} (hu : u ∈ OS) (hcu : capA st s u = .Untyped p b i d)
    (hnd : ∀ G par, TreeA st OS G par s → ∀ y, ¬ Mdb.Desc par y u) :
    u ∈ OffR p.val (p.val + 2 ^ b.val) OS ∧
    MdbST st (OffR p.val (p.val + 2 ^ b.val) OS) s ∧ UtRev st (OffR p.val (p.val + 2 ^ b.val) OS) s ∧
    ValidUntypedA st (H.drop (RegionD H p.val (p.val + 2 ^ b.val))) (OffR p.val (p.val + 2 ^ b.val) OS) s ∧
    ∀ x ∈ OS, x ∉ OffR p.val (p.val + 2 ^ b.val) OS → capA st s x = .Null := by
  obtain ⟨G, par, hM, hRO, hK, hN, hC', hTr, hU⟩ := id hS
  have hnd' := hnd G par ⟨hM, hTr, hU⟩
  have hn : ∀ x ∈ OS, x ∉ OffR p.val (p.val + 2 ^ b.val) OS → capA st s x = .Null := fun x hx hx' =>
    reset_null hU hC hu hcu hnd' x hx fun h => hx' ⟨hx, h⟩
  have huO : u ∈ OffR p.val (p.val + 2 ^ b.val) OS := by
    by_contra h'
    have := hn u hu h'
    rw [hcu] at this; cases this
  refine ⟨huO, hS.sub OffR.sub hn, hR.sub OffR.sub, ?_, hn⟩
  exact (hV.sub OffR.sub).heap fun q k hq => (Heap.drop_eq_some.1 hq).2

end ST
end R
end W7

end

end Fl4ProofsA64.P1
