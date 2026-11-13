/-
P3 (DESIGN.md §9), CSpace: the derivation tree as a list structure (no
memory, no spec).

FL4 (like seL4's C kernel) keeps the CDT as doubly linked lists of slots in
which every slot is followed immediately by its descendants. Here a chain is
a `List α` of nodes and the tree is a parent map `par`:

* `Desc par y x`: `y` descends from `x` (transitive closure of `par`).
* `SegOK par ch`: in `ch`, every node is followed by exactly its
  descendants, then by the rest.
* `MdbOK par chains`: the chains are disjoint and each is `SegOK`, and
  `par` only relates nodes of the chains.

`MdbOK.insert`: inserting a new node right after `src` (what `cteInsert`
does to the links) keeps `MdbOK`, when the new node becomes `src`'s child,
or its sibling (same parent) if `src` has no descendants (`InsCase`).
-/
import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Chain
import Mathlib.Logic.Equiv.Basic

namespace Fl4Proofs.P3.Mdb

variable {α : Type} [DecidableEq α]
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `y` descends from `x` under the parent map `par` (`x` is a proper ancestor
of `y`). -/
def Desc (par : α → Option α) (y x : α) : Prop := Relation.TransGen (fun a b => par a = some b) y x

/-- In a chain, every element is followed immediately by its descendants. -/
def SegOK (par : α → Option α) (ch : List α) : Prop :=
  ∀ pre x post, ch = pre ++ x :: post → ∃ d rest, post = d ++ rest ∧ ∀ y, Desc par y x ↔ y ∈ d

/-- Insert `y` right after the first `x`. -/
def insAfter (x y : α) : List α → List α
  | [] => []
  | a :: l => if a = x then a :: y :: l else a :: insAfter x y l

theorem insAfter_of_not_mem {x y : α} {l : List α} (h : x ∉ l) : insAfter x y l = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mem_cons, not_or] at h
    simp [insAfter, Ne.symm h.1, ih h.2]

theorem insAfter_split {x y : α} {A B : List α} (hA : x ∉ A) : insAfter x y (A ++ x :: B) = A ++ x :: y :: B := by
  induction A with
  | nil => simp [insAfter]
  | cons a A ih =>
    simp only [List.mem_cons, not_or] at hA
    simp [insAfter, Ne.symm hA.1, ih hA.2]

/-! ## Descendants after an update of one parent -/

section Update
variable {par : α → Option α} {dest : α} {np : Option α}

/-- Nothing descends from a node that is nobody's parent. -/
theorem not_desc_of_no_child {par : α → Option α} {y d : α} (h : ∀ z, par z ≠ some d) : ¬ Desc par y d := by
  intro hd
  induction hd with
  | single h1 => exact h _ h1
  | tail _ h2 _ => exact h _ h2

theorem desc_update_iff (hpd : ∀ z, par z ≠ some dest) (hdn : par dest = none) (hnp : np ≠ some dest)
    (y x : α) :
    Desc (Function.update par dest np) y x ↔
      Desc par y x ∨ (y = dest ∧ (np = some x ∨ ∃ p, np = some p ∧ Desc par p x)) := by
  have hpd' : ∀ z, Function.update par dest np z ≠ some dest := by
    intro z; by_cases hz : z = dest
    · subst hz; simpa using hnp
    · simpa [Function.update_of_ne hz] using hpd z
  constructor
  · intro h
    induction h with
    | @single b h1 =>
      by_cases hy : y = dest
      · subst hy; right; simp at h1; exact ⟨rfl, Or.inl h1⟩
      · left; rw [Function.update_of_ne hy] at h1; exact Relation.TransGen.single h1
    | @tail b c h1 h2 ih =>
      have hb : b ≠ dest := by
        rintro rfl; exact not_desc_of_no_child hpd' h1
      rw [Function.update_of_ne hb] at h2
      rcases ih with ih | ⟨rfl, ih⟩
      · exact Or.inl (Relation.TransGen.tail ih h2)
      · right; refine ⟨rfl, Or.inr ?_⟩
        rcases ih with ih | ⟨p, hp, ih⟩
        · exact ⟨b, ih, Relation.TransGen.single h2⟩
        · exact ⟨p, hp, Relation.TransGen.tail ih h2⟩
  · have lift : ∀ {y x}, Desc par y x → Desc (Function.update par dest np) y x := by
      intro y x h
      induction h with
      | @single b h1 =>
        have : y ≠ dest := by rintro rfl; rw [hdn] at h1; cases h1
        exact Relation.TransGen.single (by rw [Function.update_of_ne this]; exact h1)
      | @tail b c _ h2 ih =>
        have : b ≠ dest := by rintro rfl; rw [hdn] at h2; cases h2
        exact Relation.TransGen.tail ih (by rw [Function.update_of_ne this]; exact h2)
    rintro (h | ⟨rfl, h | ⟨p, hp, h⟩⟩)
    · exact lift h
    · exact Relation.TransGen.single (by simp [h])
    · exact Relation.TransGen.head (by simp [hp]) (lift h)

end Update

/-! ## Consequences of `SegOK` -/

theorem desc_after {par : α → Option α} {ch : List α} (hs : SegOK par ch) {pre x post} (h : ch = pre ++ x :: post)
    {y} (hy : Desc par y x) : y ∈ post := by
  obtain ⟨d, rest, rfl, hd⟩ := hs pre x post h
  exact List.mem_append_left _ ((hd y).1 hy)

theorem not_desc_self {par : α → Option α} {ch : List α} (hs : SegOK par ch) (hn : ch.Nodup) {x} (hx : x ∈ ch) :
    ¬ Desc par x x := by
  intro h
  obtain ⟨pre, post, hc⟩ := List.append_of_mem hx
  have := desc_after hs hc h
  rw [hc] at hn
  have := List.nodup_append.1 hn
  simp at this
  tauto

/-! ## List facts -/

theorem nodup_suffix_unique {L p1 p2 s1 s2 : List α} {x : α} (hn : L.Nodup)
    (h1 : L = p1 ++ x :: s1) (h2 : L = p2 ++ x :: s2) : s1 = s2 := by
  subst h1
  induction p1 generalizing p2 with
  | nil =>
    cases p2 with
    | nil => simpa using h2
    | cons b p2 =>
      simp at h2; obtain ⟨rfl, h2⟩ := h2
      simp [h2] at hn
  | cons a p1 ih =>
    cases p2 with
    | nil =>
      simp at h2; obtain ⟨rfl, h2⟩ := h2
      simp at hn
    | cons b p2 =>
      simp at h2; obtain ⟨rfl, h2⟩ := h2
      exact ih (List.nodup_cons.1 hn).2 h2

theorem prefix_split {d rest A2 B : List α} {src : α} (h : d ++ rest = A2 ++ src :: B) (hs : src ∉ A2) :
    (∃ D1, d = A2 ++ src :: D1 ∧ B = D1 ++ rest) ∨ (src ∉ d ∧ ∃ R, A2 = d ++ R) := by
  rcases List.append_eq_append_iff.1 h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · right; refine ⟨fun hm => hs (h1 ▸ List.mem_append_left _ hm), a', h1⟩
  · cases c' with
    | nil => right; simp at h1; subst h1; exact ⟨hs, [], by simp⟩
    | cons c0 c'' =>
      simp at h2; obtain ⟨rfl, h2⟩ := h2
      left; exact ⟨c'', h1, h2⟩

theorem desc_step_iff {par : α → Option α} {a p x : α} (h : par a = some p) :
    Desc par a x ↔ p = x ∨ Desc par p x := by
  unfold Desc
  rw [Relation.TransGen.head'_iff]
  constructor
  · rintro ⟨b, hb, hr⟩
    rw [h] at hb; cases hb
    rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨c, hc, hr'⟩
    · exact Or.inl rfl
    · exact Or.inr (Relation.TransGen.head' hc hr')
  · rintro (rfl | hd)
    · exact ⟨p, h, Relation.ReflTransGen.refl⟩
    · exact ⟨p, h, hd.to_reflTransGen⟩

/-! ## Inserting a slot after `src` -/

/-- How the new slot `dest` hangs off the tree: as a child of `src`, or (when
`src` has no descendants) as its sibling, with `src`'s parent. -/
def InsCase (par : α → Option α) (src : α) (np : Option α) : Prop :=
  np = some src ∨ (np = par src ∧ ∀ y, ¬ Desc par y src)

theorem nodup_mid {A B : List α} {x : α} (h : (A ++ x :: B).Nodup) : x ∉ A ∧ x ∉ B := by
  rw [List.nodup_middle, List.nodup_cons, List.mem_append, not_or] at h; exact h.1

theorem nodup_ins {A B : List α} {x y : α} (h : (A ++ x :: B).Nodup) (hy : y ∉ A ++ x :: B) :
    (A ++ x :: y :: B).Nodup := by
  have e : A ++ x :: y :: B = (A ++ [x]) ++ y :: B := by simp
  rw [e, List.nodup_middle, List.nodup_cons]
  exact ⟨by simpa using hy, by simpa using h⟩

theorem not_desc_of_none {par : α → Option α} {a x : α} (h : par a = none) : ¬ Desc par a x := by
  intro hd
  obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.1 hd
  rw [h] at hb; cases hb

theorem segOK_insAfter {par : α → Option α} {A B : List α} {src dest : α}
    (hn : (A ++ src :: B).Nodup) (hdest : dest ∉ A ++ src :: B) (hs : SegOK par (A ++ src :: B))
    (hpd : ∀ z, par z ≠ some dest) (hdn : par dest = none) {np : Option α} (hnp : np ≠ some dest)
    (hcase : InsCase par src np) :
    SegOK (Function.update par dest np) (A ++ src :: dest :: B) := by
  have hD := desc_update_iff hpd hdn hnp
  obtain ⟨hsA, hsB⟩ := nodup_mid hn
  have hn' := nodup_ins hn hdest
  have hsrc_no_self : ¬ Desc par src src := not_desc_self hs hn (by simp)
  have hdest_old : ∀ x, ¬ Desc par dest x := fun x => not_desc_of_none hdn
  have hpd' : ∀ z, Function.update par dest np z ≠ some dest := by
    intro z; by_cases hz : z = dest
    · subst hz; simpa using hnp
    · simpa [Function.update_of_ne hz] using hpd z
  have hdestanc : ∀ x, x ≠ src → ((np = some x ∨ ∃ p, np = some p ∧ Desc par p x) ↔ Desc par src x) := by
    intro x hx
    rcases hcase with rfl | ⟨rfl, -⟩
    · simp [Ne.symm hx]
    · cases hps : par src with
      | none => simp [not_desc_of_none hps]
      | some p => rw [desc_step_iff hps]; simp
  intro pre x post hdec
  have hx : x ∈ A ++ src :: dest :: B := by rw [hdec]; simp
  simp only [List.mem_append, List.mem_cons] at hx
  rcases hx with hxA | rfl | rfl | hxB
  · -- `x` before `src`
    obtain ⟨A1, A2, rfl⟩ := List.append_of_mem hxA
    have hxs : x ≠ src := fun h => hsA (h ▸ List.mem_append_right _ (by simp))
    have hpost : post = A2 ++ src :: dest :: B :=
      (nodup_suffix_unique (p1 := A1) (s1 := A2 ++ src :: dest :: B) hn' (by simp) hdec).symm
    subst hpost
    obtain ⟨d, rest, hdr, hd⟩ := hs A1 x (A2 ++ src :: B) (by simp)
    have hsA2 : src ∉ A2 := fun h => hsA (List.mem_append_right _ (List.mem_cons_of_mem _ h))
    rcases prefix_split hdr.symm hsA2 with ⟨D1, rfl, hB⟩ | ⟨hsd, R, hR⟩
    · refine ⟨A2 ++ src :: dest :: D1, rest, by simp [hB], ?_⟩
      intro y
      rw [hD]
      have hsx : Desc par src x := (hd src).2 (by simp)
      by_cases hy : y = dest
      · subst hy
        simp only [hdest_old, false_or, true_and, List.mem_append, List.mem_cons, true_or, or_true, iff_true]
        exact (hdestanc x hxs).2 hsx
      · simp only [hy, false_and, or_false, hd, List.mem_append, List.mem_cons, false_or]
    · refine ⟨d, R ++ src :: dest :: B, by simp [hR], ?_⟩
      intro y
      rw [hD, ← hd]
      constructor
      · rintro (h | ⟨rfl, h⟩)
        · exact h
        · exact absurd ((hd src).1 ((hdestanc x hxs).1 h)) hsd
      · exact Or.inl
  · -- `x = src`
    have hpost : post = dest :: B := (nodup_suffix_unique (p1 := A) (s1 := dest :: B) hn' (by simp) hdec).symm
    subst hpost
    obtain ⟨d, rest, hdr, hd⟩ := hs A x B (by simp)
    rcases hcase with hnp' | ⟨hnp', hno⟩
    · refine ⟨dest :: d, rest, by simp [hdr], ?_⟩
      intro y; rw [hD, hd, hnp']; simp only [List.mem_cons]
      constructor
      · rintro (h | ⟨rfl, -⟩); exact Or.inr h; exact Or.inl rfl
      · rintro (rfl | h); exact Or.inr ⟨rfl, by simp⟩; exact Or.inl h
    · refine ⟨[], dest :: B, by simp, ?_⟩
      intro y; rw [hD]
      simp only [hno, false_or, List.not_mem_nil, iff_false, not_and]
      rintro rfl h
      rw [hnp'] at h
      rcases h with h | ⟨p, hp, h⟩
      · exact hsrc_no_self (Relation.TransGen.single h)
      · first | exact h.elim | exact hsrc_no_self (Relation.TransGen.head hp h)
  · -- `x = dest`
    have hpost : post = B := (nodup_suffix_unique (p1 := A ++ [src]) (s1 := B) hn' (by simp) hdec).symm
    subst hpost
    exact ⟨[], post, by simp, fun y => by simp [not_desc_of_no_child hpd']⟩
  · -- `x` after `dest`
    obtain ⟨B1, B2, rfl⟩ := List.append_of_mem hxB
    have hpost : post = B2 :=
      (nodup_suffix_unique (p1 := A ++ src :: dest :: B1) (s1 := B2) hn' (by simp) hdec).symm
    subst hpost
    obtain ⟨d, rest, hdr, hd⟩ := hs (A ++ src :: B1) x post (by simp)
    have hxs : x ≠ src := fun h => hsB (h ▸ List.mem_append_right _ (by simp))
    refine ⟨d, rest, hdr, ?_⟩
    intro y; rw [hD, ← hd]
    constructor
    · rintro (h | ⟨rfl, h⟩)
      · exact h
      · exfalso
        have := desc_after hs (pre := A ++ src :: B1) (x := x) (post := post) (by simp) ((hdestanc x hxs).1 h)
        exact hsB (List.mem_append_right _ (List.mem_cons_of_mem _ this))
    · exact Or.inl

theorem segOK_other {par : α → Option α} {ch : List α} {src dest : α}
    (hs : SegOK par ch) (hsrc : src ∉ ch) (hdest : dest ∉ ch)
    (hpd : ∀ z, par z ≠ some dest) (hdn : par dest = none) {np : Option α} (hnp : np ≠ some dest)
    (hcase : InsCase par src np) :
    SegOK (Function.update par dest np) ch := by
  have hD := desc_update_iff hpd hdn hnp
  intro pre x post hdec
  obtain ⟨d, rest, hdr, hd⟩ := hs pre x post hdec
  have hxch : x ∈ ch := by rw [hdec]; simp
  have hxs : x ≠ src := fun h => hsrc (h ▸ hxch)
  refine ⟨d, rest, hdr, fun y => ?_⟩
  rw [hD, ← hd]
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · exact h
    · exfalso
      have hsx : Desc par src x := by
        rcases hcase with rfl | ⟨rfl, -⟩
        · rcases h with h | ⟨p, hp, h⟩
          · cases h; exact absurd rfl hxs
          · cases hp; exact h
        · cases hps : par src with
          | none => rw [hps] at h; simp at h
          | some p => rw [hps] at h; rw [desc_step_iff hps]; simpa using h
      exact hsrc (hdec ▸ List.mem_append_right _ (List.mem_cons_of_mem _ (desc_after hs hdec hsx)))
  · exact Or.inl

theorem map_insAfter_of_not_mem {src dest : α} {C : List (List α)} (h : src ∉ C.flatten) :
    C.map (insAfter src dest) = C := by
  induction C with
  | nil => rfl
  | cons c C ih =>
    simp only [List.flatten_cons, List.mem_append, not_or] at h
    simp [insAfter_of_not_mem h.1, ih h.2]

/-! ## The whole derivation tree -/

/-- The derivation forest `par` laid out as the chains: each slot is in one
chain, followed immediately by its descendants. -/
structure MdbOK (par : α → Option α) (chains : List (List α)) : Prop where
  nodup : chains.flatten.Nodup
  seg : ∀ ch ∈ chains, SegOK par ch
  par_mem : ∀ a b, par a = some b → a ∈ chains.flatten ∧ b ∈ chains.flatten

/-- Inserting `dest` after `src`, as `src`'s child or (if `src` has no
descendants) its sibling. -/
theorem MdbOK.insert {par : α → Option α} {chains : List (List α)} (h : MdbOK par chains)
    {src dest : α} (hsrc : src ∈ chains.flatten) (hdest : dest ∉ chains.flatten)
    {np : Option α} (hcase : InsCase par src np) :
    MdbOK (Function.update par dest np) (chains.map (insAfter src dest)) := by
  have hpd : ∀ z, par z ≠ some dest := fun z hz => hdest (h.par_mem z dest hz).2
  have hdn : par dest = none := by
    cases hc : par dest with
    | none => rfl
    | some b => exact absurd (h.par_mem dest b hc).1 hdest
  have hnp : np ≠ some dest := by
    rcases hcase with rfl | ⟨rfl, -⟩
    · intro e; cases e; exact hdest hsrc
    · exact hpd src
  -- the chain holding `src`
  obtain ⟨ch, hch, hsch⟩ := List.mem_flatten.1 hsrc
  obtain ⟨C1, C2, rfl⟩ := List.append_of_mem hch
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hsch
  have hnd := h.nodup
  simp only [List.flatten_append, List.flatten_cons] at hnd
  have hsA' : src ∉ A := by
    intro hm; have := (List.nodup_append.1 hnd).2.1
    have := (List.nodup_append.1 this).1
    exact (nodup_mid this).1 hm
  have hC1 : src ∉ C1.flatten := by
    intro hm; exact (List.disjoint_of_nodup_append hnd hm (by simp)).elim
  have hC2 : src ∉ C2.flatten := by
    intro hm
    have := (List.nodup_append.1 hnd).2.1
    exact (List.disjoint_of_nodup_append this (by simp) hm).elim
  have e : (C1 ++ (A ++ src :: B) :: C2).map (insAfter src dest) = C1 ++ (A ++ src :: dest :: B) :: C2 := by
    simp [map_insAfter_of_not_mem hC1, map_insAfter_of_not_mem hC2, insAfter_split hsA']
  rw [e]
  have hmemiff : ∀ y, y ∈ (C1 ++ (A ++ src :: dest :: B) :: C2).flatten ↔
      y = dest ∨ y ∈ (C1 ++ (A ++ src :: B) :: C2).flatten := by
    intro y; simp only [List.flatten_append, List.flatten_cons, List.mem_append, List.mem_cons]; tauto
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.flatten_append, List.flatten_cons] at hnd ⊢
    have e2 : C1.flatten ++ (A ++ src :: dest :: B ++ C2.flatten) =
        (C1.flatten ++ A ++ [src]) ++ dest :: (B ++ C2.flatten) := by simp
    rw [e2, List.nodup_middle, List.nodup_cons]
    refine ⟨?_, by simpa using hnd⟩
    simpa using hdest
  · intro ch' hch'
    simp only [List.mem_append, List.mem_cons] at hch'
    have hdch : ∀ c ∈ C1 ++ (A ++ src :: B) :: C2, dest ∉ c := fun c hc hm => hdest (List.mem_flatten.2 ⟨c, hc, hm⟩)
    rcases hch' with h1 | rfl | h2
    · exact segOK_other (h.seg ch' (by simp [h1])) (fun hm => hC1 (List.mem_flatten.2 ⟨ch', h1, hm⟩))
        (hdch ch' (by simp [h1])) hpd hdn hnp hcase
    · have hn1 : (A ++ src :: B).Nodup := by
        have := (List.nodup_append.1 hnd).2.1; exact (List.nodup_append.1 this).1
      exact segOK_insAfter hn1 (hdch _ (by simp)) (h.seg _ (by simp)) hpd hdn hnp hcase
    · exact segOK_other (h.seg ch' (by simp [h2])) (fun hm => hC2 (List.mem_flatten.2 ⟨ch', h2, hm⟩))
        (hdch ch' (by simp [h2])) hpd hdn hnp hcase
  · intro a b hab
    by_cases ha : a = dest
    · subst ha
      simp only [Function.update_self] at hab
      refine ⟨(hmemiff _).2 (Or.inl rfl), (hmemiff _).2 (Or.inr ?_)⟩
      rcases hcase with rfl | ⟨rfl, -⟩
      · cases hab; exact hsrc
      · exact (h.par_mem src b hab).2
    · rw [Function.update_of_ne ha] at hab
      obtain ⟨h1, h2⟩ := h.par_mem a b hab
      exact ⟨(hmemiff _).2 (Or.inr h1), (hmemiff _).2 (Or.inr h2)⟩

/-! ## Links of a chain after an insertion -/

theorem isChain_ins {R R' : α → α → Prop} {A B : List α} {src dest : α}
    (hc : (A ++ src :: B).IsChain R)
    (hA : ∀ a b, a ∈ A → b ∈ A → R a b → R' a b)
    (hAs : ∀ x ∈ A.getLast?, R x src → R' x src)
    (hsd : R' src dest) (hdb : ∀ y ∈ B.head?, R' dest y)
    (hB : ∀ a b, a ∈ B → b ∈ B.tail → R a b → R' a b) :
    (A ++ src :: dest :: B).IsChain R' := by
  rw [List.isChain_append] at hc ⊢
  obtain ⟨hcA, hcB, hlink⟩ := hc
  refine ⟨hcA.imp_of_mem_imp hA, ?_, ?_⟩
  · rw [List.isChain_cons_cons, List.isChain_cons]
    exact ⟨hsd, hdb, (List.isChain_cons.1 hcB).2.imp_of_mem_tail_imp hB⟩
  · intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact hAs x hx (hlink x hx _ (by simp))

/-! ## Renaming nodes (move, swap) -/

/-- The parent map with nodes renamed by `e`. -/
def conjPar (e : α ≃ α) (par : α → Option α) : α → Option α := fun x => (par (e.symm x)).map e

theorem desc_conj (e : α ≃ α) (par : α → Option α) (y x : α) :
    Desc (conjPar e par) (e y) (e x) ↔ Desc par y x := by
  have step : ∀ a b, (conjPar e par) (e a) = some (e b) ↔ par a = some b := by
    intro a b; simp [conjPar]
  constructor
  · intro h
    have key : ∀ u v, Desc (conjPar e par) u v → Desc par (e.symm u) (e.symm v) := by
      intro u v h
      induction h with
      | @single b h1 =>
        apply Relation.TransGen.single
        have := (step (e.symm u) (e.symm b)).1 (by simpa using h1); exact this
      | @tail b c _ h2 ih =>
        exact Relation.TransGen.tail ih ((step (e.symm b) (e.symm c)).1 (by simpa using h2))
    simpa using key _ _ h
  · intro h
    induction h with
    | @single b h1 => exact Relation.TransGen.single ((step _ _).2 h1)
    | @tail b c _ h2 ih => exact Relation.TransGen.tail ih ((step _ _).2 h2)

theorem segOK_conj (e : α ≃ α) {par : α → Option α} {ch : List α} (hs : SegOK par ch) :
    SegOK (conjPar e par) (ch.map e) := by
  intro pre x post hdec
  have hdec' : ch = pre.map e.symm ++ e.symm x :: post.map e.symm := by
    have := congrArg (List.map e.symm) hdec
    simpa [List.map_map] using this
  obtain ⟨d, rest, hdr, hd⟩ := hs _ _ _ hdec'
  refine ⟨d.map e, rest.map e, ?_, ?_⟩
  · have := congrArg (List.map e) hdr
    simpa [List.map_map] using this
  · intro y
    have := desc_conj e par (e.symm y) (e.symm x)
    simp only [Equiv.apply_symm_apply] at this
    rw [this, hd]
    simp only [List.mem_map]
    constructor
    · intro h; exact ⟨_, h, by simp⟩
    · rintro ⟨z, hz, rfl⟩; simpa using hz

theorem MdbOK.conj (e : α ≃ α) {par : α → Option α} {chains : List (List α)} (h : MdbOK par chains) :
    MdbOK (conjPar e par) (chains.map (List.map e)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← List.map_flatten]; exact h.nodup.map e.injective
  · intro ch' hch'
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    exact segOK_conj e (h.seg ch hch)
  · intro a b hab
    simp only [conjPar, Option.map_eq_some_iff] at hab
    obtain ⟨b0, hb0, rfl⟩ := hab
    obtain ⟨h1, h2⟩ := h.par_mem _ _ hb0
    rw [← List.map_flatten]
    exact ⟨List.mem_map.2 ⟨_, h1, by simp⟩, List.mem_map.2 ⟨_, h2, rfl⟩⟩

/-! ## Removing a node (empty_slot) -/

/-- The parent map after removing `x`: its children get its parent. -/
def removePar (x : α) (par : α → Option α) : α → Option α :=
  fun y => if y = x then none else if par y = some x then par x else par y

theorem desc_remove_iff {par : α → Option α} {x : α} (hx : par x ≠ some x) (y z : α) :
    Desc (removePar x par) y z ↔ y ≠ x ∧ z ≠ x ∧ Desc par y z := by
  constructor
  · intro h
    induction h with
    | @single b h1 =>
      unfold removePar at h1
      by_cases hy : y = x
      · simp [hy] at h1
      · simp only [hy, ↓reduceIte] at h1
        by_cases hp : par y = some x
        · rw [if_pos hp] at h1
          refine ⟨hy, fun hb => hx (hb ▸ h1), Relation.TransGen.tail (Relation.TransGen.single hp) h1⟩
        · rw [if_neg hp] at h1
          exact ⟨hy, fun hb => hp (hb ▸ h1), Relation.TransGen.single h1⟩
    | @tail b c _ h2 ih =>
      obtain ⟨hy, hb, hd⟩ := ih
      unfold removePar at h2
      simp only [hb, ↓reduceIte] at h2
      by_cases hp : par b = some x
      · rw [if_pos hp] at h2
        exact ⟨hy, fun hc => hx (hc ▸ h2), Relation.TransGen.tail (Relation.TransGen.tail hd hp) h2⟩
      · rw [if_neg hp] at h2
        exact ⟨hy, fun hc => hp (hc ▸ h2), Relation.TransGen.tail hd h2⟩
  · rintro ⟨hy, hz, h⟩
    -- the stronger statement, by induction on the path
    have key : ∀ w, Desc par y w →
        (w ≠ x → Desc (removePar x par) y w) ∧ (w = x → ∀ u, par x = some u → Desc (removePar x par) y u) := by
      intro w hw
      induction hw with
      | @single b h1 =>
        refine ⟨fun hb => Relation.TransGen.single ?_, fun hb u hu => Relation.TransGen.single ?_⟩
        · simp [removePar, hy, h1, hb]
        · subst hb; simp [removePar, hy, h1, hu]
      | @tail b c hd h2 ih =>
        refine ⟨fun hc => ?_, fun hc u hu => ?_⟩
        · by_cases hb : b = x
          · exact ih.2 hb c (hb ▸ h2)
          · exact Relation.TransGen.tail (ih.1 hb) (by simp [removePar, hb, h2, hc])
        · subst hc
          have hb : b ≠ c := fun e => hx (e ▸ h2)
          exact Relation.TransGen.tail (ih.1 hb) (by simp [removePar, hb, h2, hu])
    exact (key z h).1 hz

theorem segOK_remove {par : α → Option α} {A B : List α} {x : α} (hn : (A ++ x :: B).Nodup)
    (hs : SegOK par (A ++ x :: B)) (hx : par x ≠ some x) : SegOK (removePar x par) (A ++ B) := by
  have hD := desc_remove_iff hx
  obtain ⟨hxA, hxB⟩ := nodup_mid hn
  have hn' : (A ++ B).Nodup := by
    have := List.nodup_middle.1 hn; exact (List.nodup_cons.1 this).2
  intro pre z post hdec
  have hz : z ∈ A ++ B := by rw [hdec]; simp
  simp only [List.mem_append] at hz
  rcases hz with hzA | hzB
  · obtain ⟨A1, A2, rfl⟩ := List.append_of_mem hzA
    have hpost : post = A2 ++ B :=
      (nodup_suffix_unique (p1 := A1) (s1 := A2 ++ B) hn' (by simp) hdec).symm
    subst hpost
    obtain ⟨d, rest, hdr, hd⟩ := hs A1 z (A2 ++ x :: B) (by simp)
    have hxA2 : x ∉ A2 := fun h => hxA (List.mem_append_right _ (List.mem_cons_of_mem _ h))
    have hzx : z ≠ x := fun h => hxA (h ▸ List.mem_append_right _ (by simp))
    rcases prefix_split hdr.symm hxA2 with ⟨D1, rfl, hB⟩ | ⟨hsd, R, hR⟩
    · refine ⟨A2 ++ D1, rest, by simp [hB], fun y => ?_⟩
      rw [hD, hd]
      constructor
      · rintro ⟨hy, -, h⟩
        simp only [List.mem_append, List.mem_cons] at h ⊢; tauto
      · intro h
        have hyx : y ≠ x := by
          rintro rfl
          simp only [List.mem_append] at h
          rcases h with h | h
          · exact hxA2 h
          · exact hxB (hB ▸ List.mem_append_left _ h)
        exact ⟨hyx, hzx, by simp only [List.mem_append, List.mem_cons] at h ⊢; tauto⟩
    · refine ⟨d, R ++ B, by simp [hR], fun y => ?_⟩
      rw [hD, hd]
      constructor
      · rintro ⟨-, -, h⟩; exact h
      · intro h; exact ⟨fun e => hsd (e ▸ h), hzx, h⟩
  · obtain ⟨B1, B2, rfl⟩ := List.append_of_mem hzB
    have hpost : post = B2 :=
      (nodup_suffix_unique (p1 := A ++ B1) (s1 := B2) hn' (by simp) hdec).symm
    subst hpost
    obtain ⟨d, rest, hdr, hd⟩ := hs (A ++ x :: B1) z post (by simp)
    have hzx : z ≠ x := fun h => hxB (h ▸ List.mem_append_right _ (by simp))
    refine ⟨d, rest, hdr, fun y => ?_⟩
    rw [hD, hd]
    constructor
    · rintro ⟨-, -, h⟩; exact h
    · intro h
      refine ⟨?_, hzx, h⟩
      rintro rfl
      exact hxB (List.mem_append_right _ (List.mem_cons_of_mem _ (hdr ▸ List.mem_append_left _ h)))

theorem segOK_remove_other {par : α → Option α} {ch : List α} {x : α} (hs : SegOK par ch) (hxc : x ∉ ch)
    (hx : par x ≠ some x) : SegOK (removePar x par) ch := by
  intro pre z post hdec
  obtain ⟨d, rest, hdr, hd⟩ := hs pre z post hdec
  have hzx : z ≠ x := fun h => hxc (h ▸ by rw [hdec]; simp)
  refine ⟨d, rest, hdr, fun y => ?_⟩
  rw [desc_remove_iff hx, hd]
  constructor
  · rintro ⟨-, -, h⟩; exact h
  · intro h
    refine ⟨?_, hzx, h⟩
    rintro rfl; exact hxc (by rw [hdec, hdr]; simp [h])

theorem erase_mid {A B : List α} {x : α} (hx : x ∉ A) : (A ++ x :: B).erase x = A ++ B := by
  rw [List.erase_append_right _ hx]; simp

theorem erase_not_mem' {ch : List α} {x : α} (hx : x ∉ ch) : ch.erase x = ch := List.erase_of_not_mem hx

/-- The chains after removing `x` (dropping a chain that becomes empty). -/
def removeChains (x : α) (chains : List (List α)) : List (List α) :=
  (chains.map (fun ch => ch.erase x)).filter (fun ch => !ch.isEmpty)

theorem flatten_filter_ne_nil (L : List (List α)) : (L.filter (fun ch => !ch.isEmpty)).flatten = L.flatten := by
  induction L with
  | nil => rfl
  | cons c L ih => cases c <;> simp [List.filter_cons, ih]

theorem flatten_map_erase_sublist (x : α) (L : List (List α)) :
    (L.map (fun ch => ch.erase x)).flatten.Sublist L.flatten := by
  induction L with
  | nil => simp
  | cons c L ih => simpa using (List.erase_sublist (l := c) (a := x)).append ih

theorem mem_removeChains {x y : α} {chains : List (List α)} (hn : chains.flatten.Nodup) :
    y ∈ (removeChains x chains).flatten ↔ y ∈ chains.flatten ∧ y ≠ x := by
  unfold removeChains
  rw [flatten_filter_ne_nil]
  simp only [List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨_, ⟨ch, hch, rfl⟩, hy⟩
    have hnd := (List.nodup_flatten.1 hn).1 ch hch
    exact ⟨⟨ch, hch, (List.erase_subset) hy⟩, fun e => by subst e; exact (List.Nodup.not_mem_erase hnd) hy⟩
  · rintro ⟨⟨ch, hch, hy⟩, hyx⟩
    exact ⟨_, ⟨ch, hch, rfl⟩, (List.mem_erase_of_ne hyx).2 hy⟩

theorem MdbOK.remove {par : α → Option α} {chains : List (List α)} (h : MdbOK par chains) {x : α}
    (hx : par x ≠ some x) : MdbOK (removePar x par) (removeChains x chains) := by
  have hmem := fun y => mem_removeChains (x := x) (y := y) h.nodup
  refine ⟨?_, ?_, ?_⟩
  · unfold removeChains; rw [flatten_filter_ne_nil]
    exact (flatten_map_erase_sublist x chains).nodup h.nodup
  · intro ch' hch'
    unfold removeChains at hch'
    obtain ⟨hch', -⟩ := List.mem_filter.1 hch'
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    have hnd := (List.nodup_flatten.1 h.nodup).1 ch hch
    by_cases hxc : x ∈ ch
    · obtain ⟨A, B, rfl⟩ := List.append_of_mem hxc
      have : (A ++ x :: B).erase x = A ++ B := by
        rw [List.erase_append_right _ (nodup_mid hnd).1]; simp
      rw [this]; exact segOK_remove hnd (h.seg _ hch) hx
    · rw [List.erase_of_not_mem hxc]; exact segOK_remove_other (h.seg ch hch) hxc hx
  · intro a b hab
    unfold removePar at hab
    by_cases hax : a = x
    · simp [hax] at hab
    · simp only [hax, ↓reduceIte] at hab
      by_cases hp : par a = some x
      · rw [if_pos hp] at hab
        exact ⟨(hmem a).2 ⟨(h.par_mem a x hp).1, hax⟩, (hmem b).2 ⟨(h.par_mem x b hab).2, fun e => hx (e ▸ hab)⟩⟩
      · rw [if_neg hp] at hab
        exact ⟨(hmem a).2 ⟨(h.par_mem a b hab).1, hax⟩, (hmem b).2 ⟨(h.par_mem a b hab).2, fun e => hp (e ▸ hab)⟩⟩

end Fl4Proofs.P3.Mdb
