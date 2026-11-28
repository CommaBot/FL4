/-
P1 (aarch64, gen 47): **`MdbLk`, `RngOneA64` and `KindA` along the removal of a slot from its chain** — the data
step of `cdt::empty_slot` (cdt.rs:198–215: the predecessor's `NEXT` becomes the successor, the successor's `PREV`
the predecessor, the slot cleared) and of every deletion that ends in it.

* Ghost: `remG x G` — every chain with `x` erased, emptied chains dropped (P3's `remG` without `par`).
* List facts: `nd_idx` (a nodup list's index of an element is unique), `erase_idx` (`(c.erase x)[n]? =
  c[if n < i then n else n + 1]?` where `c[i]? = some x`), `remG_mem` / `remG_of` / `remG_sub`, `remG_flat`.
* **`MdbLk.rem`**: at the state after, with `P` / `N` the slot's old `PREV` / `NEXT`: `x`'s cap null, every other
  `OS` slot's cap kept, `NEXT` kept off `P` and `PREV` kept off `N`, `P`'s `NEXT` = `N` (if `P ≠ 0`) and `N`'s
  `PREV` = `P` (if `N ≠ 0`) ⇒ `MdbLk OS (remG x G)` (`h0`: no `OS` slot at 0, the links' null).
* **`RngOneA64.rem`** (members' caps kept; contiguity survives because erasing is an order-preserving re-indexing),
  **`KindA.rem`** (only a cap made null).

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.MdbKind
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-! ## Lists -/

theorem nd_idx {α : Type _} : ∀ {l : List α} {i j : Nat} {a : α}, l.Nodup → l[i]? = some a → l[j]? = some a → i = j
  | [], _, _, _, _, hi, _ => by simp at hi
  | _ :: _, 0, 0, _, _, _, _ => rfl
  | b :: l, 0, j + 1, a, h, hi, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    simp only [List.getElem?_cons_succ] at hj
    subst hi
    exact absurd (List.mem_of_getElem? hj) (List.nodup_cons.1 h).1
  | b :: l, i + 1, 0, a, h, hi, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    simp only [List.getElem?_cons_succ] at hi
    subst hj
    exact absurd (List.mem_of_getElem? hi) (List.nodup_cons.1 h).1
  | b :: l, i + 1, j + 1, a, h, hi, hj => by
    simp only [List.getElem?_cons_succ] at hi hj
    exact congrArg (· + 1) (nd_idx (List.nodup_cons.1 h).2 hi hj)

theorem erase_mid {α : Type _} [BEq α] [LawfulBEq α] {x : α} :
    ∀ (l1 l2 : List α), x ∉ l1 → (l1 ++ x :: l2).erase x = l1 ++ l2
  | [], l2, _ => by simp
  | a :: l1, l2, h => by
    have ha : a ≠ x := fun e => h (by rw [e]; exact List.mem_cons.2 (Or.inl rfl))
    have h1 : x ∉ l1 := fun e => h (List.mem_cons.2 (Or.inr e))
    rw [List.cons_append, List.erase_cons_tail (by simpa using ha), erase_mid l1 l2 h1, List.cons_append]

theorem idx_mid {α : Type _} (l1 l2 : List α) (x : α) (n : Nat) :
    (l1 ++ l2)[n]? = (l1 ++ x :: l2)[if n < l1.length then n else n + 1]? := by
  split
  · rename_i h
    rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · rename_i h
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      show n + 1 - l1.length = (n - l1.length) + 1 by omega, List.getElem?_cons_succ]

/-- **Erasing re-indexes order-preservingly.** -/
theorem erase_idx {α : Type _} [BEq α] [LawfulBEq α] {c : List α} {x : α} {i : Nat} (hnd : c.Nodup)
    (hi : c[i]? = some x) (n : Nat) : (c.erase x)[n]? = c[if n < i then n else n + 1]? := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem (List.mem_of_getElem? hi)
  have hl : (l1 ++ x :: l2)[l1.length]? = some x := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  have e : i = l1.length := nd_idx hnd hi hl
  subst e
  have hx1 : x ∉ l1 := fun hm => by
    have := List.disjoint_of_nodup_append hnd hm (List.mem_cons.2 (Or.inl rfl)); exact this
  rw [erase_mid l1 l2 hx1]; exact idx_mid l1 l2 x n

theorem len_erase {α : Type _} [BEq α] [LawfulBEq α] {c : List α} {x : α} (hx : x ∈ c) :
    (c.erase x).length = c.length - 1 := List.length_erase_of_mem hx

/-! ## The ghost with a slot removed -/

/-- `x` erased from every chain, emptied chains dropped. -/
def remG (x : U64) : List (List U64) → List (List U64)
  | [] => []
  | c :: G => if c.erase x = [] then remG x G else c.erase x :: remG x G

theorem remG_mem {x : U64} : ∀ {G : List (List U64)} {c' : List U64}, c' ∈ remG x G →
    ∃ c ∈ G, c' = c.erase x ∧ c' ≠ []
  | [], _, h => by simp [remG] at h
  | c :: G, c', h => by
    unfold remG at h
    split at h
    · obtain ⟨d, hd, e, ne⟩ := remG_mem h; exact ⟨d, List.mem_cons.2 (Or.inr hd), e, ne⟩
    · rename_i hn
      rcases List.mem_cons.1 h with e | h
      · exact ⟨c, List.mem_cons.2 (Or.inl rfl), e, by rw [e]; exact hn⟩
      · obtain ⟨d, hd, e, ne⟩ := remG_mem h; exact ⟨d, List.mem_cons.2 (Or.inr hd), e, ne⟩

theorem remG_of {x : U64} : ∀ {G : List (List U64)} {c : List U64}, c ∈ G → c.erase x ≠ [] →
    c.erase x ∈ remG x G
  | [], _, h, _ => by simp at h
  | d :: G, c, h, hn => by
    unfold remG
    rcases List.mem_cons.1 h with e | h
    · subst e; rw [if_neg hn]; exact List.mem_cons.2 (Or.inl rfl)
    · split
      · exact remG_of h hn
      · exact List.mem_cons.2 (Or.inr (remG_of h hn))

theorem remG_sub {x : U64} : ∀ G : List (List U64), (remG x G).flatten.Sublist G.flatten
  | [] => by simp [remG]
  | c :: G => by
    unfold remG; split
    · rw [List.flatten_cons]; exact (remG_sub G).trans (List.sublist_append_right _ _)
    · rw [List.flatten_cons, List.flatten_cons]
      exact (List.erase_sublist (a := x) (l := c)).append (remG_sub G)

theorem ch_nodup {G : List (List U64)} (hnd : G.flatten.Nodup) {c : List U64} (hc : c ∈ G) : c.Nodup :=
  (List.nodup_flatten.1 hnd).1 c hc

/-- Two chains sharing a member are equal. -/
theorem ch_eq : ∀ {G : List (List U64)}, G.flatten.Nodup → ∀ {c d : List U64} {y : U64}, c ∈ G → d ∈ G → y ∈ c →
    y ∈ d → c = d
  | [], _, _, _, _, hc, _, _, _ => by simp at hc
  | e :: G, hnd, c, d, y, hc, hd, hyc, hyd => by
    rw [List.flatten_cons] at hnd
    have hdis := List.disjoint_of_nodup_append hnd
    have hG := hnd.of_append_right
    rcases List.mem_cons.1 hc with e1 | hc1 <;> rcases List.mem_cons.1 hd with e2 | hd1
    · rw [e1, e2]
    · rw [e1] at hyc; exact (hdis hyc (List.mem_flatten.2 ⟨d, hd1, hyd⟩)).elim
    · rw [e2] at hyd; exact (hdis hyd (List.mem_flatten.2 ⟨c, hc1, hyc⟩)).elim
    · exact ch_eq hG hc1 hd1 hyc hyd

theorem remG_flat {G : List (List U64)} (hnd : G.flatten.Nodup) {x y : U64} :
    y ∈ (remG x G).flatten ↔ y ∈ G.flatten ∧ y ≠ x := by
  constructor
  · intro hy
    obtain ⟨c', hc', hyc'⟩ := List.mem_flatten.1 hy
    obtain ⟨c, hc, rfl, -⟩ := remG_mem hc'
    have := (List.Nodup.mem_erase_iff (ch_nodup hnd hc)).1 hyc'
    exact ⟨List.mem_flatten.2 ⟨c, hc, this.2⟩, this.1⟩
  · rintro ⟨hy, hne⟩
    obtain ⟨c, hc, hyc⟩ := List.mem_flatten.1 hy
    have h1 : y ∈ c.erase x := (List.mem_erase_of_ne hne).2 hyc
    exact List.mem_flatten.2 ⟨_, remG_of hc (List.ne_nil_of_mem h1), h1⟩

/-! ## `RngOneA64` and `KindA` -/

/-- **`RngOneA64` along a removal** (the members' caps kept). -/
theorem RngOneA64.rem {G : List (List U64)} {s s' : S} (h : RngOneA64 st G s) (hnd : G.flatten.Nodup) {x : U64}
    (hk : ∀ y ∈ G.flatten, y ≠ x → capA st s' y = capA st s y) : RngOneA64 st (remG x G) s' := by
  have hk' : ∀ y ∈ (remG x G).flatten, capA st s' y = capA st s y := fun y hy =>
    hk y ((remG_flat hnd).1 hy).1 ((remG_flat hnd).1 hy).2
  refine ⟨fun y hy y' hy' k k' hc => ?_, fun ch' hch' i j k y z y' hi hj hk2 hij hjk ky ky' hc => ?_⟩
  · rw [hk' y hy] at k hc; rw [hk' y' hy'] at k' hc
    have a := (remG_flat hnd).1 hy
    have a' := (remG_flat hnd).1 hy'
    obtain ⟨c, hc0, hyc, hyc'⟩ := h.one y a.1 y' a'.1 k k' hc
    have h1 : y ∈ c.erase x := (List.mem_erase_of_ne a.2).2 hyc
    exact ⟨_, remG_of hc0 (List.ne_nil_of_mem h1), h1, (List.mem_erase_of_ne a'.2).2 hyc'⟩
  · have mem : ∀ {n w}, ch'[n]? = some w → w ∈ (remG x G).flatten := fun e =>
      List.mem_flatten.2 ⟨ch', hch', List.mem_of_getElem? e⟩
    rw [hk' y (mem hi)] at ky hc; rw [hk' y' (mem hk2)] at ky' hc
    rw [hk' z (mem hj), hk' y (mem hi)]
    obtain ⟨c, hc0, rfl, -⟩ := remG_mem hch'
    have hcn := ch_nodup hnd hc0
    by_cases hx : x ∈ c
    · obtain ⟨i0, hi0, hxi⟩ := List.getElem_of_mem hx
      have ex : c[i0]? = some x := by simp [hi0, hxi]
      rw [erase_idx hcn ex] at hi hj hk2
      refine h.chunk c hc0 _ _ _ y z y' hi hj hk2 ?_ ?_ ky ky' hc <;> split <;> split <;> omega
    · rw [List.erase_of_not_mem hx] at hi hj hk2
      exact h.chunk c hc0 i j k y z y' hi hj hk2 hij hjk ky ky' hc

/-- **`KindA` along a removal**: `x`'s cap made null, the others kept. -/
theorem KindA.rem {OS : Set U64} {s s' : S} (h : KindA st OS s) {x : U64} (hcx : capA st s' x = .Null)
    (hk : ∀ y ∈ OS, y ≠ x → capA st s' y = capA st s y) : KindA st OS s' := by
  have hn : ∀ y ∈ OS, RngKeyA (capA st s' y) → capA st s' y = capA st s y := fun y hy k => by
    by_cases e : y = x
    · subst e; rw [hcx] at k; exact absurd k RngKeyA.not_null
    · exact hk y hy e
  refine ⟨fun y hy y' hy' k k' hp => ?_⟩
  have e1 := hn y hy k
  have e2 := hn y' hy' k'
  rw [e1] at k hp ⊢; rw [e2] at k' hp ⊢
  exact h.kind y hy y' hy' k k' hp

/-! ## `MdbLk` -/

theorem lt_of_some {α : Type _} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : i < l.length := by
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h

section lk
variable {OS : Set U64} {G : List (List U64)}

/-- The slot's `PREV` word, when not null, is its chain predecessor. -/
theorem MdbLk.prev_idx {s : S} (h : MdbLk st OS G s) {c : List U64} (hc : c ∈ G) {i : Nat} {x : U64}
    (hi : c[i]? = some x) (hP : L.mem s (wa x 16#u64) ≠ 0#u64) :
    ∃ j, i = j + 1 ∧ c[j]? = some (L.mem s (wa x 16#u64)) := by
  cases i with
  | zero => exact absurd (h.head c hc x (by rw [List.head?_eq_getElem?]; exact hi)) hP
  | succ j =>
    have hj : j < c.length := by have := lt_of_some hi; omega
    have e := getElem?_of_lt hj
    exact ⟨j, rfl, by rw [e, (h.chain c hc j _ x e hi).2]⟩

/-- The slot's `NEXT`, when not null, is its chain successor. -/
theorem MdbLk.next_idx {s : S} (h : MdbLk st OS G s) {c : List U64} (hc : c ∈ G) {i : Nat} {x : U64}
    (hi : c[i]? = some x) (hN : NxA st s x ≠ 0#u64) : c[i + 1]? = some (NxA st s x) := by
  by_cases hl : i + 1 < c.length
  · have e := getElem?_of_lt hl
    rw [e, (h.chain c hc i x _ hi e).1]
  · have hi' := lt_of_some hi
    refine absurd (h.last c hc x ?_) hN
    rw [List.getLast?_eq_getElem?, show c.length - 1 = i by omega]; exact hi

/-- **`MdbLk` along the removal of `x` from its chain** (module docstring). -/
theorem MdbLk.rem {s s' : S} (h : MdbLk st OS G s) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {x : U64} (hx : x ∈ G.flatten)
    (hcx : capA st s' x = .Null) (hc : ∀ y ∈ OS, y ≠ x → capA st s' y = capA st s y)
    (hnx : ∀ y ∈ OS, y ≠ x → y ≠ L.mem s (wa x 16#u64) → NxA st s' y = NxA st s y)
    (hpv : ∀ y ∈ OS, y ≠ x → y ≠ NxA st s x → L.mem s' (wa y 16#u64) = L.mem s (wa y 16#u64))
    (hP : L.mem s (wa x 16#u64) ≠ 0#u64 → NxA st s' (L.mem s (wa x 16#u64)) = NxA st s x)
    (hN : NxA st s x ≠ 0#u64 → L.mem s' (wa (NxA st s x) 16#u64) = L.mem s (wa x 16#u64)) :
    MdbLk st OS (remG x G) s' := by
  have hnd := h.nodup
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((h.members y).1 hy).1
  obtain ⟨cx, hcx0, hxcx⟩ := List.mem_flatten.1 hx
  obtain ⟨ix, hix, hxi⟩ := List.getElem_of_mem hxcx
  have exi : cx[ix]? = some x := by rw [getElem?_of_lt hix, hxi]
  have hcxn := ch_nodup hnd hcx0
  have memc : ∀ {c : List U64}, c ∈ G → ∀ {n : Nat} {y : U64}, c[n]? = some y → y ∈ G.flatten :=
    fun hc0 _ _ e => List.mem_flatten.2 ⟨_, hc0, List.mem_of_getElem? e⟩
  -- an element equal to `P` / `N` sits just before / after `x` in `x`'s chain
  have keyP : ∀ {c : List U64}, c ∈ G → ∀ {n : Nat} {y : U64}, c[n]? = some y → y = L.mem s (wa x 16#u64) →
      c = cx ∧ n + 1 = ix := by
    intro c hc0 n y hy e
    have hP0 : L.mem s (wa x 16#u64) ≠ 0#u64 := e ▸ h0 y (inOS y (memc hc0 hy))
    obtain ⟨j, hj, ej⟩ := h.prev_idx hcx0 exi hP0
    have hcc : c = cx := ch_eq hnd hc0 hcx0 (List.mem_of_getElem? hy)
      (by rw [e]; exact List.mem_of_getElem? ej)
    subst hcc
    exact ⟨rfl, by rw [hj, nd_idx hcxn hy (e ▸ ej)]⟩
  have keyN : ∀ {c : List U64}, c ∈ G → ∀ {n : Nat} {y : U64}, c[n]? = some y → y = NxA st s x →
      c = cx ∧ n = ix + 1 := by
    intro c hc0 n y hy e
    have hN0 : NxA st s x ≠ 0#u64 := e ▸ h0 y (inOS y (memc hc0 hy))
    have ej := h.next_idx hcx0 exi hN0
    have hcc : c = cx := ch_eq hnd hc0 hcx0 (List.mem_of_getElem? hy)
      (by rw [e]; exact List.mem_of_getElem? ej)
    subst hcc
    exact ⟨rfl, nd_idx hcxn hy (e ▸ ej)⟩
  have nex : ∀ {c : List U64}, c ∈ G → ∀ {n : Nat} {y : U64}, (c.erase x)[n]? = some y → y ≠ x :=
    fun hc0 _ _ e => ((List.Nodup.mem_erase_iff (ch_nodup hnd hc0)).1 (List.mem_of_getElem? e)).1
  have ofer : ∀ {c : List U64}, c ∈ G → ∀ {n : Nat} {y : U64}, (c.erase x)[n]? = some y → y ∈ OS :=
    fun hc0 _ _ e => inOS _ (List.mem_flatten.2 ⟨_, hc0,
      ((List.Nodup.mem_erase_iff (ch_nodup hnd hc0)).1 (List.mem_of_getElem? e)).2⟩)
  refine ⟨List.Nodup.sublist (remG_sub G) hnd, fun ch hch => (remG_mem hch).choose_spec.2.2,
    fun ch hch n a b ha hb => ?_, fun ch hch a ha => ?_, fun ch hch a ha => ?_, fun y => ?_⟩
  · -- chain
    obtain ⟨c, hc0, rfl, -⟩ := remG_mem hch
    have aO := ofer hc0 ha
    have bO := ofer hc0 hb
    have ax := nex hc0 ha
    have bx := nex hc0 hb
    by_cases hxc : x ∈ c
    · obtain rfl : c = cx := ch_eq hnd hc0 hcx0 hxc hxcx
      rw [erase_idx hcxn exi] at ha hb
      by_cases h1 : n + 1 < ix
      · rw [if_pos (by omega)] at ha; rw [if_pos h1] at hb
        have old := h.chain c hc0 n a b ha hb
        refine ⟨?_, ?_⟩
        · rw [hnx a aO ax fun e => by have := (keyP hc0 ha e).2; omega]; exact old.1
        · rw [hpv b bO bx fun e => by have := (keyN hc0 hb e).2; omega]; exact old.2
      · by_cases h2 : n + 1 = ix
        · rw [if_pos (by omega)] at ha; rw [if_neg h1] at hb
          have l1 := h.chain c hc0 n a x ha (by rw [h2]; exact exi)
          have l2 := h.chain c hc0 (n + 1) x b (by rw [h2]; exact exi) hb
          have eP : L.mem s (wa x 16#u64) = a := l1.2
          have eN : NxA st s x = b := l2.1
          refine ⟨?_, ?_⟩
          · rw [← eP, hP (by rw [eP]; exact h0 a aO), eN]
          · rw [← eN, hN (by rw [eN]; exact h0 b bO), eP]
        · rw [if_neg (by omega)] at ha; rw [if_neg h1] at hb
          have old := h.chain c hc0 (n + 1) a b ha hb
          refine ⟨?_, ?_⟩
          · rw [hnx a aO ax fun e => by have := (keyP hc0 ha e).2; omega]; exact old.1
          · rw [hpv b bO bx fun e => by have := (keyN hc0 hb e).2; omega]; exact old.2
    · rw [List.erase_of_not_mem hxc] at ha hb
      have old := h.chain c hc0 n a b ha hb
      refine ⟨?_, ?_⟩
      · rw [hnx a aO ax fun e => absurd ((keyP hc0 ha e).1 ▸ hxcx) hxc]; exact old.1
      · rw [hpv b bO bx fun e => absurd ((keyN hc0 hb e).1 ▸ hxcx) hxc]; exact old.2
  · -- head
    obtain ⟨c, hc0, rfl, -⟩ := remG_mem hch
    rw [List.head?_eq_getElem?] at ha
    have aO := ofer hc0 ha
    have ax := nex hc0 ha
    by_cases hxc : x ∈ c
    · obtain rfl : c = cx := ch_eq hnd hc0 hcx0 hxc hxcx
      rw [erase_idx hcxn exi] at ha
      by_cases hi0 : ix = 0
      · subst hi0
        rw [if_neg (by omega)] at ha
        have l2 := h.chain c hc0 0 x a exi ha
        have eN : NxA st s x = a := l2.1
        have eP : L.mem s (wa x 16#u64) = 0#u64 := h.head c hc0 x (by rw [List.head?_eq_getElem?]; exact exi)
        rw [← eN, hN (by rw [eN]; exact h0 a aO), eP]
      · rw [if_pos (by omega)] at ha
        rw [hpv a aO ax fun e => by have := (keyN hc0 ha e).2; omega]
        exact h.head c hc0 a (by rw [List.head?_eq_getElem?]; exact ha)
    · rw [List.erase_of_not_mem hxc] at ha
      rw [hpv a aO ax fun e => absurd ((keyN hc0 ha e).1 ▸ hxcx) hxc]
      exact h.head c hc0 a (by rw [List.head?_eq_getElem?]; exact ha)
  · -- last
    obtain ⟨c, hc0, rfl, hne⟩ := remG_mem hch
    rw [List.getLast?_eq_getElem?] at ha
    have aO := ofer hc0 ha
    have ax := nex hc0 ha
    by_cases hxc : x ∈ c
    · obtain rfl : c = cx := ch_eq hnd hc0 hcx0 hxc hxcx
      have hlen := len_erase (x := x) hxc
      have hpos : 0 < (c.erase x).length := List.length_pos_of_ne_nil hne
      rw [hlen, erase_idx hcxn exi] at ha
      by_cases hl : ix = c.length - 1
      · rw [if_pos (by omega)] at ha
        have l1 := h.chain c hc0 (c.length - 1 - 1) a x ha
          (by rw [show c.length - 1 - 1 + 1 = ix by omega]; exact exi)
        have eP : L.mem s (wa x 16#u64) = a := l1.2
        have eN : NxA st s x = 0#u64 := h.last c hc0 x (by rw [List.getLast?_eq_getElem?, ← hl]; exact exi)
        rw [← eP, hP (by rw [eP]; exact h0 a aO), eN]
      · rw [if_neg (by omega)] at ha
        rw [hnx a aO ax fun e => by have := (keyP hc0 ha e).2; omega]
        exact h.last c hc0 a (by rw [List.getLast?_eq_getElem?, show c.length - 1 = c.length - 1 - 1 + 1 by omega]; exact ha)
    · rw [List.erase_of_not_mem hxc] at ha
      rw [hnx a aO ax fun e => absurd ((keyP hc0 ha e).1 ▸ hxcx) hxc]
      exact h.last c hc0 a (by rw [List.getLast?_eq_getElem?]; exact ha)
  · -- members
    rw [remG_flat hnd, h.members]
    constructor
    · rintro ⟨⟨hy, hcy⟩, hne⟩; exact ⟨hy, by rw [hc y hy hne]; exact hcy⟩
    · rintro ⟨hy, hcy⟩
      have hne : y ≠ x := fun e => hcy (by rw [e, hcx])
      exact ⟨⟨hy, by rw [← hc y hy hne]; exact hcy⟩, hne⟩

end lk

end ST
end R
end W7

end

end Fl4ProofsA64.P1
