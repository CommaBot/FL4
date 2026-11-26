/-
# P2 (line glue, gen 3): **framing of accepted runs**, and what is left of gaps G2 / G3

## G3 (start-time `σ` versus completion-time prefix memory)

When core `c` completes an accepted body, Serial's history replays it from the prefix memory `H₁` at completion
(`LocInv.sim` with `n := H₁`), while the start fact's chain state `σ₀` matches the prefix memory `H₀` at start. Between
the two, other cores' completed bodies changed `H` only on words they held, never on the words `c` reads. This
module proves the store-level half of the bridge:

* **`E2E.interp_frame`**: a run of a tree whose reads all lie in `R` (`Within`) is a function of the words of `R`:
  from any state `σ₁` agreeing with `σ₀` on the aligned words of `R`, with the same constants (`cpu`, `ksb`,
  masks), the same tree runs with the same result value and Arch state, and its final memory is, on every aligned
  word, either the first run's final memory (a word it wrote) or `σ₁`'s own (a word it did not write, where the
  first run left `σ₀`'s).
* **`E2E.PathObl.frame_acc`**: for an accepted run of a local path, `R` is its `ReadSet` (`PathObl.acc` +
  `IsProgOn`). So the accepted run from `σ₁` is the merge `mix W (run from σ₀) σ₁` — exactly the shape of Serial's
  `H' = mix W s.mem H₁`.

So the accepted case of the chain induction reduces to one fact, the **cross-core view** of the chain: a state of
`Ch` of core `c` with memory `H₁` (holding `c`'s locks, with `c`'s Arch state). That is not a P3 fact and is not
derivable here: P3's chain `JReachSt` steps one core's run from one of that core's states (`L.cpu` is part of the
store state, `LawfulStore` gives no way to change it), so after core `d`'s run `Ch` contains `H₁` only as a state of
core `d`. In an abstract `LawfulStore` there need be no state with memory `H₁` and `cpu = c` at all, so no proof
from the chain's definition can supply it. Closing G3 needs it as a named premise.

## G2 (`GlueAt`'s Arch state `a` versus the chain triple's)

Option (b), "`F`'s memory result does not depend on `a` beyond what the chain fixes", is **false**: the bodies'
`update_timestamp` writes the Arch clock reading into the node's `CUR_TIME` (and the consumed time into `CONSUMED`),
so two Arch states with different clocks give different memories, while `Ch` fixes only that *some* `a` with a
spec triple exists. Option (a) — a start family whose `a` is the chain triple's — is the honest one, and needs the
same cross-core fact as G3 (the triple's `a` must be core `c`'s Arch state). It is not built here, since without
the cross-core premise it would only strengthen the start [P].

## Decision on the serial exit (step 4)

The memory clause `L.mem σe x = s'.mem x` (aligned, non-user) on `SerExitW` would discharge the chain part of the
start [P] only together with the cross-core premise above. Adding it alone strengthens a [P] with no discharge, so
**it is not added** (task rule: never strengthen a [P] without a net discharge). Net premise change of gen 3: none.

No premise added; no existing statement changed.
-/
import Fl4Proofs.P2.GlueAdeq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner)

noncomputable section
open Classical

section frame
variable {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}

/-- **A run reading only `R` is a function of `R`** (module docstring). -/
theorem interp_frame (hmk : MasksWr st) {R : U64 → Prop} {σ σ₁ : S} (p : SProg X) :
    ∀ (s s₁ : S) (a : A) (Wd : Set U64) (r : X × S × A) (R0 User : U64 → Prop) (W0 T : Set U64),
      interp st ar p s a = ok r →
      Within st ar (fun b => Aligned b ∧ R b) (fun b => Aligned b) p s a →
      Once st ar R0 User W0 T p s a →
      L.cpu s₁ = L.cpu s → L.ksb s₁ = L.ksb s → st.frame_masks s₁ = st.frame_masks s →
      (∀ y, Aligned y → (R y ∨ y ∈ Wd) → L.mem s₁ y = L.mem s y) →
      (∀ y, Aligned y → y ∉ Wd → L.mem s y = L.mem σ y ∧ L.mem s₁ y = L.mem σ₁ y) →
      ∃ r₁, interp st ar p s₁ a = ok r₁ ∧ r₁.1 = r.1 ∧ r₁.2.2 = r.2.2 ∧
        ∀ y, Aligned y → L.mem r₁.2.1 y = L.mem r.2.1 y ∨
          (L.mem r.2.1 y = L.mem σ y ∧ L.mem r₁.2.1 y = L.mem σ₁ y) := by
  induction p with
  | ret x =>
    intro s s₁ a Wd r _ _ _ _ h _ _ _ _ _ hE hO
    simp only [interp] at h
    obtain rfl := Result.ok_injective h
    refine ⟨(x, s₁, a), by simp only [interp], rfl, rfl, fun y hy => ?_⟩
    by_cases hw : y ∈ Wd
    · exact Or.inl (hE y hy (Or.inr hw))
    · exact Or.inr (hO y hy hw)
  | err e =>
    intro s s₁ a Wd r _ _ _ _ h
    simp only [interp] at h
    exact absurd h fail_not_ok
  | zero q n k ih =>
    intro s s₁ a Wd r _ _ _ _ _ _ hN
    simp only [Once] at hN
  | clr q n k ih =>
    intro s s₁ a Wd r _ _ _ _ _ _ hN
    simp only [Once] at hN
  | rd q k ih =>
    intro s s₁ a Wd r R0 User W0 T h hW hN hc hk hm hE hO
    simp only [interp] at h
    obtain ⟨v, hv, hk'⟩ := bok.mp h
    simp only [Within] at hW
    simp only [Once] at hN
    obtain ⟨⟨hal, hr⟩, hW⟩ := hW
    have ev : v = L.mem s q := Result.ok_injective (hv.symm.trans (L.read_eq s q))
    have e1 : st.read s₁ q = ok v := by rw [L.read_eq, hE q hal (Or.inl hr), ev]
    obtain ⟨r₁, h1, h2, h3, h4⟩ :=
      ih v s s₁ a Wd r R0 User W0 _ hk' (hW _ hv) (hN.2 _ hv) hc hk hm hE hO
    exact ⟨r₁, by simp only [interp]; exact bok.mpr ⟨v, e1, h1⟩, h2, h3, h4⟩
  | rdp q k ih =>
    intro s s₁ a Wd r R0 User W0 T h hW hN hc hk hm hE hO
    simp only [interp] at h
    obtain ⟨v, hv, hk'⟩ := bok.mp h
    simp only [Within] at hW
    simp only [Once] at hN
    obtain ⟨⟨hal, hr⟩, ⟨hal8, hr8⟩, hW⟩ := hW
    have ev : v = (L.mem s q, L.mem s (core.num.U64.wrapping_add q 8#u64)) :=
      Result.ok_injective (hv.symm.trans (L.read_pair_eq s q))
    have e1 : st.read_pair s₁ q = ok v := by
      rw [L.read_pair_eq, hE q hal (Or.inl hr), hE _ hal8 (Or.inl hr8), ev]
    obtain ⟨r₁, h1, h2, h3, h4⟩ :=
      ih v s s₁ a Wd r R0 User W0 _ hk' (hW _ hv) (hN.2.2 _ hv) hc hk hm hE hO
    exact ⟨r₁, by simp only [interp]; exact bok.mpr ⟨v, e1, h1⟩, h2, h3, h4⟩
  | wr q v k ih =>
    intro s s₁ a Wd r R0 User W0 T h hW hN hc hk hm hE hO
    simp only [interp] at h
    obtain ⟨s', hv, hk'⟩ := bok.mp h
    simp only [Within] at hW
    simp only [Once] at hN
    obtain ⟨hal, hW⟩ := hW
    have es : s' = L.wr s q v := Result.ok_injective (hv.symm.trans (L.write_eq s q v))
    subst es
    have hE' : ∀ y, Aligned y → (R y ∨ y ∈ insert q Wd) → L.mem (L.wr s₁ q v) y = L.mem (L.wr s q v) y := by
      intro y hy hyR
      rw [L.mem_wr s q v y hal hy, L.mem_wr s₁ q v y hal hy]
      by_cases hne : q = y
      · rw [if_pos hne, if_pos hne]
      · rw [if_neg hne, if_neg hne]
        refine hE y hy (hyR.imp_right fun h => ?_)
        rcases Set.mem_insert_iff.mp h with h | h
        · exact absurd h.symm hne
        · exact h
    have hO' : ∀ y, Aligned y → y ∉ insert q Wd →
        L.mem (L.wr s q v) y = L.mem σ y ∧ L.mem (L.wr s₁ q v) y = L.mem σ₁ y := by
      intro y hy hyW
      have hne : q ≠ y := fun h => hyW (h ▸ Set.mem_insert q Wd)
      rw [L.mem_wr s q v y hal hy, L.mem_wr s₁ q v y hal hy, if_neg hne, if_neg hne]
      exact hO y hy fun h => hyW (Set.mem_insert_of_mem _ h)
    obtain ⟨r₁, h1, h2, h3, h4⟩ := ih (L.wr s q v) (L.wr s₁ q v) a (insert q Wd) r R0 User _ _ hk' (hW _ hv)
      (hN _ hv) (by rw [L.cpu_wr, L.cpu_wr]; exact hc) (by rw [L.ksb_wr, L.ksb_wr]; exact hk)
      (by rw [hmk, hmk]; exact hm) hE' hO'
    exact ⟨r₁, by simp only [interp]; exact bok.mpr ⟨_, L.write_eq s₁ q v, h1⟩, h2, h3, h4⟩
  | ksb k ih =>
    intro s s₁ a Wd r R0 User W0 T h hW hN hc hk hm hE hO
    simp only [interp] at h
    obtain ⟨v, hv, hk'⟩ := bok.mp h
    simp only [Within] at hW
    simp only [Once] at hN
    have e1 : st.ks_base s₁ = ok v := by rw [L.ks_base_eq, hk, ← L.ks_base_eq]; exact hv
    obtain ⟨r₁, h1, h2, h3, h4⟩ := ih v s s₁ a Wd r R0 User W0 T hk' (hW _ hv) (hN _ hv) hc hk hm hE hO
    exact ⟨r₁, by simp only [interp]; exact bok.mpr ⟨v, e1, h1⟩, h2, h3, h4⟩
  | cpu k ih =>
    intro s s₁ a Wd r R0 User W0 T h hW hN hc hk hm hE hO
    simp only [interp] at h
    obtain ⟨v, hv, hk'⟩ := bok.mp h
    simp only [Within] at hW
    simp only [Once] at hN
    have e1 : st.cur_cpu s₁ = ok v := by rw [L.cur_cpu_eq, hc, ← L.cur_cpu_eq]; exact hv
    obtain ⟨r₁, h1, h2, h3, h4⟩ := ih v s s₁ a Wd r R0 User W0 T hk' (hW _ hv) (hN _ hv) hc hk hm hE hO
    exact ⟨r₁, by simp only [interp]; exact bok.mpr ⟨v, e1, h1⟩, h2, h3, h4⟩
  | masks k ih =>
    intro s s₁ a Wd r R0 User W0 T h hW hN hc hk hm hE hO
    simp only [interp] at h
    obtain ⟨v, hv, hk'⟩ := bok.mp h
    simp only [Within] at hW
    simp only [Once] at hN
    have e1 : st.frame_masks s₁ = ok v := by rw [hm]; exact hv
    obtain ⟨r₁, h1, h2, h3, h4⟩ := ih v s s₁ a Wd r R0 User W0 T hk' (hW _ hv) (hN _ hv) hc hk hm hE hO
    exact ⟨r₁, by simp only [interp]; exact bok.mpr ⟨v, e1, h1⟩, h2, h3, h4⟩
  | arch op k ih =>
    intro s s₁ a Wd r R0 User W0 T h hW hN hc hk hm hE hO
    simp only [interp] at h
    obtain ⟨⟨b, a'⟩, hv, hk'⟩ := bok.mp h
    simp only [Within] at hW
    simp only [Once] at hN
    obtain ⟨r₁, h1, h2, h3, h4⟩ :=
      ih b s s₁ a' Wd r R0 User W0 T hk' (hW _ _ hv) (hN _ _ hv) hc hk hm hE hO
    exact ⟨r₁, by simp only [interp]; exact bok.mpr ⟨(b, a'), hv, h1⟩, h2, h3, h4⟩

end frame

section path
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **An accepted run of a local path is a function of its read set** (module docstring, G3): from any state `σ₁`
of the same core agreeing with the entry state `σ` on the aligned words of `ReadSet σ` (user words included), the
body gives the same result value and Arch state, and memory that is the first run's on the words it wrote and
`σ₁`'s elsewhere. -/
theorem LocalPath.frame_acc (P : LocalPath own cls ko User) {σ σ₁ : P.S} {a : P.A} {r : P.X × P.S × P.A}
    (hpre : P.Pre σ) (h : P.F P.ar P.st σ a = ok r) (hacc : P.Acc r.1)
    (hc : P.L.cpu σ₁ = P.L.cpu σ) (hk : P.L.ksb σ₁ = P.L.ksb σ)
    (hm : P.st.frame_masks σ₁ = P.st.frame_masks σ)
    (hE : ∀ y, Aligned y → P.RS σ y → P.L.mem σ₁ y = P.L.mem σ y) :
    ∃ r₁, interp P.st P.ar P.p σ₁ a = ok r₁ ∧ r₁.1 = r.1 ∧ r₁.2.2 = r.2.2 ∧
      ∀ y, Aligned y → P.L.mem r₁.2.1 y = P.L.mem r.2.1 y ∨
        (P.L.mem r.2.1 y = P.L.mem σ y ∧ P.L.mem r₁.2.1 y = P.L.mem σ₁ y) := by
  letI := P.L
  have gu : AltOf P.st P.Pre P.RS cls ko User σ := AltOf.pre hpre
  have hI : interp P.st P.ar P.p σ a = ok r := by
    rw [← P.isProg _ (Narrow.self _) σ gu a]; exact h
  have hA := P.side.read_aligned σ σ a r hpre (Alt.refl σ) h
  rw [P.isProg _ (Narrow.guard _ _ _) σ gu a] at hA
  have hA := (interp_guard P.p σ a r hA).2
  have hWr : Within P.st P.ar (P.RS σ) (fun b => Aligned b) P.p σ a := Within.mono (fun _ h => h) (fun b hb => P.obl.aligned σ b hpre (Or.inl hb)) P.p σ a
    (P.obl.within P.isProg hpre gu h hacc)
  have hW : Within P.st P.ar (fun b => Aligned b ∧ P.RS σ b) (fun b => Aligned b) P.p σ a :=
    Within.mono (fun b hb => hb) (fun b hb => hb.2) P.p σ a (within_and P.p σ a hA hWr)
  have hO := P.once σ σ a r hpre (Alt.refl σ) hI
  exact interp_frame (R := P.RS σ) (σ := σ) (σ₁ := σ₁) P.masks P.p σ σ₁ a ∅ r _ _ _ _ hI hW hO hc hk hm
    (fun y hy hyR => hE y hy (hyR.resolve_right (Set.notMem_empty y))) (fun _ _ _ => ⟨rfl, rfl⟩)

end path

end
end Fl4Proofs.P2.E2E
