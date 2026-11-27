/-
P3 (line mmuAD, gen 23): **the VCPU list invariant `VList`** — the kernel-global doubly-linked list of VCPUs
(`VCPU_HEAD`, each VCPU's `NEXT` / `PREV` words, vcpu.rs `init` l. 644-650 / `finalise` l. 737-750).

* `VSeg m p l n`: the list `l` laid out in memory `m` as a doubly-linked segment — every element nonzero, its
  `PREV` word the element before (`p` for the first), its `NEXT` word the element after (`n` after the last).
  Pure lemmas: `VSeg.congr`, `.ne0`, `.next`, `.prev`, `.listed` (P1's `VListed` from the head along `NEXT` is
  exactly membership in `l`), `.insert` (insertion at the head), `.at`, `.remove`, **`.unlink`** (removal of any
  element given the four link writes of `finalise`).
* **`VList st V th s`**: some duplicate-free list `l` with members exactly `V` is a `VSeg (L.mem s) 0 l 0` whose
  first element is the head word's value (`0` for the empty list); and the head word is aligned and none of `JW V
  th` / `SW th` (gen 22's `hhd`). It packs gen 22's three list [J]s:
  **`VList.hL`** (`hL`: `VListed ↔ ∈ V`), **`VList.hP`** (`hP`: a nonzero `PREV` of a VCPU of `V` is in `V`, the
  doubly-linked invariant), **`VList.hhd`** (`hhd`).
* `_of` corollaries with `hL` / `hP` / `hhd` removed in favour of `VList`: **`JVLay.finPlV`**, **`JAtZ.finPlV`**,
  **`vcpu_finalise_jv_vl`** (= `vcpu_finalise_jv_lay` over `VList`).
* Frames: **`VList.frame`** (same head and link words of `V`, kernel base kept, typed heap's `JW` / `SW` words not
  grown), **`VList.writes`** (a `WritesIn` footprint missing the list words `LW V s`), `VList.mono_th`.
* `VList.empty`: `V = ∅` from a zero head word.

No [P] / [W] / [S] premise; no existing statement changed.
-/
import Fl4Proofs.P3.JExtVFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## Pure list segments -/

/-- The first element, `n` for the empty list. -/
def vhd0 : List U64 → U64 → U64
  | [], n => n
  | a :: _, _ => a

/-- The last element, `d` for the empty list. -/
def vlastD : List U64 → U64 → U64
  | [], d => d
  | a :: l, _ => vlastD l a

/-- **A doubly-linked segment** (module docstring). -/
def VSeg (m : U64 → U64) : U64 → List U64 → U64 → Prop
  | _, [], _ => True
  | p, w :: l, n => w ≠ 0#u64 ∧ m (vPrevA w) = p ∧ m (P1.vNextA w) = vhd0 l n ∧ VSeg m w l n

theorem vhd0_mem {l : List U64} {n : U64} : vhd0 l n = n ∨ vhd0 l n ∈ l := by
  cases l with
  | nil => exact Or.inl rfl
  | cons a l => exact Or.inr (by simp [vhd0])

theorem vlastD_mem : ∀ (l : List U64) (x d : U64), vlastD (x :: l) d ∈ x :: l
  | [], x, d => by simp [vlastD]
  | y :: l, x, d => by
    have h := vlastD_mem l y x
    show vlastD (y :: l) x ∈ x :: y :: l
    exact List.mem_cons_of_mem _ h

theorem vmem_split {v : U64} : ∀ {l : List U64}, v ∈ l → ∃ l1 l2, l = l1 ++ v :: l2
  | [], h => by simp at h
  | w :: l, h => by
    rcases List.mem_cons.1 h with e | h
    · subst e; exact ⟨[], l, rfl⟩
    · obtain ⟨l1, l2, e⟩ := vmem_split h
      exact ⟨w :: l1, l2, by rw [e]; rfl⟩

theorem vnodup_mid {v : U64} {l2 : List U64} : ∀ {l1 : List U64}, (l1 ++ v :: l2).Nodup →
    (l1 ++ l2).Nodup ∧ v ∉ l1 ++ l2
  | [], h => by
    simp only [List.nil_append] at h ⊢
    exact ⟨(List.nodup_cons.1 h).2, (List.nodup_cons.1 h).1⟩
  | u :: l1, h => by
    simp only [List.cons_append] at h ⊢
    obtain ⟨h1, h2⟩ := List.nodup_cons.1 h
    obtain ⟨i1, i2⟩ := vnodup_mid h2
    refine ⟨List.nodup_cons.2 ⟨fun hu => h1 ?_, i1⟩, ?_⟩
    · simp only [List.mem_append, List.mem_cons] at hu ⊢; tauto
    · simp only [List.mem_cons, not_or]
      refine ⟨fun e => h1 ?_, i2⟩
      rw [← e]; simp

section
variable {m m' : U64 → U64}

theorem VSeg.congr {n : U64} {l : List U64} : ∀ {p : U64}, VSeg m p l n →
    (∀ u ∈ l, m' (P1.vNextA u) = m (P1.vNextA u) ∧ m' (vPrevA u) = m (vPrevA u)) → VSeg m' p l n := by
  induction l with
  | nil => intro p _ _; simp only [VSeg]
  | cons w l ih =>
    intro p h hm
    simp only [VSeg] at h ⊢
    obtain ⟨h0, h1, h2, h3⟩ := h
    obtain ⟨e1, e2⟩ := hm w (by simp)
    exact ⟨h0, by rw [e2]; exact h1, by rw [e1]; exact h2, ih h3 fun u hu => hm u (by simp [hu])⟩

theorem VSeg.ne0 {n : U64} {l : List U64} : ∀ {p : U64}, VSeg m p l n → ∀ u ∈ l, u ≠ 0#u64 := by
  induction l with
  | nil => intro p _ u hu; simp at hu
  | cons w l ih =>
    intro p h u hu
    simp only [VSeg] at h
    obtain ⟨h0, -, -, h3⟩ := h
    rcases List.mem_cons.1 hu with e | hu
    · rw [e]; exact h0
    · exact ih h3 u hu

theorem VSeg.next {n : U64} {l : List U64} : ∀ {p : U64}, VSeg m p l n → ∀ u ∈ l,
    m (P1.vNextA u) = n ∨ m (P1.vNextA u) ∈ l := by
  induction l with
  | nil => intro p _ u hu; simp at hu
  | cons w l ih =>
    intro p h u hu
    simp only [VSeg] at h
    obtain ⟨-, -, h2, h3⟩ := h
    rcases List.mem_cons.1 hu with e | hu
    · rw [e, h2]
      rcases vhd0_mem (l := l) (n := n) with e' | e'
      · exact Or.inl e'
      · exact Or.inr (List.mem_cons_of_mem _ e')
    · rcases ih h3 u hu with e' | e'
      · exact Or.inl e'
      · exact Or.inr (List.mem_cons_of_mem _ e')

theorem VSeg.prev {n : U64} {l : List U64} : ∀ {p : U64}, VSeg m p l n → ∀ u ∈ l,
    m (vPrevA u) = p ∨ m (vPrevA u) ∈ l := by
  induction l with
  | nil => intro p _ u hu; simp at hu
  | cons w l ih =>
    intro p h u hu
    simp only [VSeg] at h
    obtain ⟨-, h1, -, h3⟩ := h
    rcases List.mem_cons.1 hu with e | hu
    · rw [e]; exact Or.inl h1
    · rcases ih h3 u hu with e' | e'
      · right; rw [e']; simp
      · exact Or.inr (List.mem_cons_of_mem _ e')

/-- **Insertion at the head** (`vcpu::init`). -/
theorem VSeg.insert {l : List U64} {v : U64} (hs : VSeg m 0#u64 l 0#u64) (hnd : l.Nodup)
    (hv0 : v ≠ 0#u64) (hpv : m' (vPrevA v) = 0#u64) (hnv : m' (P1.vNextA v) = vhd0 l 0#u64)
    (hph : ∀ w l', l = w :: l' → m' (vPrevA w) = v)
    (hN : ∀ u ∈ l, m' (P1.vNextA u) = m (P1.vNextA u))
    (hP : ∀ u ∈ l, u ≠ vhd0 l 0#u64 → m' (vPrevA u) = m (vPrevA u)) :
    VSeg m' 0#u64 (v :: l) 0#u64 := by
  simp only [VSeg]
  refine ⟨hv0, hpv, hnv, ?_⟩
  cases l with
  | nil => simp only [VSeg]
  | cons w l' =>
    simp only [VSeg] at hs ⊢
    obtain ⟨hw0, -, hnw, hs'⟩ := hs
    have hwl : w ∉ l' := (List.nodup_cons.1 hnd).1
    refine ⟨hw0, hph w l' rfl, by rw [hN w (by simp)]; exact hnw, ?_⟩
    exact hs'.congr fun u hu => ⟨hN u (by simp [hu]),
      hP u (by simp [hu]) (fun e => hwl (by simp only [vhd0] at e; rw [← e]; exact hu))⟩

theorem VSeg.at {v n : U64} {l2 : List U64} : ∀ (l1 : List U64) {p : U64},
    VSeg m p (l1 ++ v :: l2) n → m (P1.vNextA v) = vhd0 l2 n ∧ m (vPrevA v) = vlastD l1 p
  | [], p, h => by
    simp only [List.nil_append, VSeg] at h
    exact ⟨h.2.2.1, h.2.1⟩
  | u :: l1, p, h => by
    simp only [List.cons_append, VSeg] at h
    obtain ⟨-, -, -, h3⟩ := h
    exact VSeg.at l1 h3

/-- **Removal of an element** (general form, along the prefix). -/
theorem VSeg.remove {v n : U64} {l2 : List U64} : ∀ (l1 : List U64) {p : U64},
    VSeg m p (l1 ++ v :: l2) n → (l1 ++ v :: l2).Nodup → (∀ u ∈ l1 ++ v :: l2, u ≠ p ∧ u ≠ n) →
    (∀ u ∈ l1 ++ l2, u ≠ m (vPrevA v) → m' (P1.vNextA u) = m (P1.vNextA u)) →
    (∀ u ∈ l1 ++ l2, u ≠ m (P1.vNextA v) → m' (vPrevA u) = m (vPrevA u)) →
    (∀ u ∈ l1, u = m (vPrevA v) → m' (P1.vNextA u) = m (P1.vNextA v)) →
    (∀ u ∈ l2, u = m (P1.vNextA v) → m' (vPrevA u) = m (vPrevA v)) →
    VSeg m' p (l1 ++ l2) n
  | [], p, hs, hnd, hpn, hN, hP, _, hPn => by
    simp only [List.nil_append] at hs hnd hpn hN hP ⊢
    simp only [VSeg] at hs
    obtain ⟨-, hpv, hnv, hs2⟩ := hs
    cases l2 with
    | nil => simp only [VSeg]
    | cons w l3 =>
      simp only [VSeg] at hs2 ⊢
      obtain ⟨hw0, -, hnw, hs3⟩ := hs2
      have hnv' : m (P1.vNextA v) = w := hnv
      have hwl3 : w ∉ l3 := (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).1
      have hwp : w ≠ p := (hpn w (by simp)).1
      refine ⟨hw0, ?_, ?_, ?_⟩
      · rw [hPn w (by simp) hnv'.symm, hpv]
      · rw [hN w (by simp) (by rw [hpv]; exact hwp)]; exact hnw
      · refine hs3.congr fun u hu => ⟨hN u (by simp [hu]) (by rw [hpv]; exact (hpn u (by simp [hu])).1),
          hP u (by simp [hu]) (fun e => hwl3 (by rw [hnv'] at e; rw [← e]; exact hu))⟩
  | u :: l1, p, hs, hnd, hpn, hN, hP, hNp, hPn => by
    have hat := VSeg.at (u :: l1) hs
    simp only [List.cons_append] at hs hnd hpn hN hP ⊢
    simp only [VSeg] at hs ⊢
    obtain ⟨hu0, hpu, hnu, hs'⟩ := hs
    have hnd' := List.nodup_cons.1 hnd
    have hul : u ∉ l1 ++ v :: l2 := hnd'.1
    have hun : u ≠ m (P1.vNextA v) := by
      rw [hat.1]
      rcases vhd0_mem (l := l2) (n := n) with e | e
      · rw [e]; exact (hpn u (by simp)).2
      · intro h; apply hul; rw [h]; simp [e]
    refine ⟨hu0, by rw [hP u (by simp) hun]; exact hpu, ?_, ?_⟩
    · cases l1 with
      | nil =>
        have e : m (vPrevA v) = u := hat.2
        rw [hNp u (by simp) e.symm, hat.1]; simp only [List.nil_append]
      | cons x l1' =>
        have hxm := vlastD_mem l1' x u
        have e : m (vPrevA v) = vlastD (x :: l1') u := hat.2
        have hne : u ≠ m (vPrevA v) := by
          rw [e]; intro h; apply hul; rw [h]; exact List.mem_append_left _ hxm
        rw [hN u (by simp) hne, hnu]; rfl
    · exact VSeg.remove l1 hs' hnd'.2 (fun w hw => ⟨fun e => hul (e ▸ hw), (hpn w (List.mem_cons_of_mem _ hw)).2⟩)
        (fun w hw => hN w (List.mem_cons_of_mem _ hw)) (fun w hw => hP w (List.mem_cons_of_mem _ hw))
        (fun w hw => hNp w (List.mem_cons_of_mem _ hw)) hPn

/-- **Unlinking** (`vcpu::finalise`'s four link writes; module docstring). -/
theorem VSeg.unlink {l : List U64} {v : U64} (hs : VSeg m 0#u64 l 0#u64) (hnd : l.Nodup) (hv : v ∈ l)
    (hN : ∀ u ∈ l, u ≠ v → u ≠ m (vPrevA v) → m' (P1.vNextA u) = m (P1.vNextA u))
    (hP : ∀ u ∈ l, u ≠ v → u ≠ m (P1.vNextA v) → m' (vPrevA u) = m (vPrevA u))
    (hNp : m (vPrevA v) ≠ 0#u64 → m' (P1.vNextA (m (vPrevA v))) = m (P1.vNextA v))
    (hPn : m (P1.vNextA v) ≠ 0#u64 → m' (vPrevA (m (P1.vNextA v))) = m (vPrevA v)) :
    ∃ l', l'.Nodup ∧ (∀ w, w ∈ l' ↔ w ∈ l ∧ w ≠ v) ∧ VSeg m' 0#u64 l' 0#u64 ∧
      vhd0 l' 0#u64 = (if m (vPrevA v) = 0#u64 then m (P1.vNextA v) else vhd0 l 0#u64) := by
  obtain ⟨l1, l2, rfl⟩ := vmem_split hv
  obtain ⟨hnd', hvn⟩ := vnodup_mid hnd
  have hne0 := hs.ne0
  have hat := VSeg.at l1 hs
  refine ⟨l1 ++ l2, hnd', fun w => ?_, ?_, ?_⟩
  · constructor
    · intro hw
      refine ⟨by simp only [List.mem_append, List.mem_cons] at hw ⊢; tauto, fun e => hvn (e ▸ hw)⟩
    · rintro ⟨hw, hne⟩
      simp only [List.mem_append, List.mem_cons] at hw ⊢
      rcases hw with h | h | h
      · exact Or.inl h
      · exact absurd h hne
      · exact Or.inr h
  · refine VSeg.remove l1 hs hnd (fun u hu => ⟨hne0 u hu, hne0 u hu⟩)
      (fun u hu h => hN u (by simp only [List.mem_append, List.mem_cons] at hu ⊢; tauto)
        (fun e => hvn (e ▸ hu)) h)
      (fun u hu h => hP u (by simp only [List.mem_append, List.mem_cons] at hu ⊢; tauto)
        (fun e => hvn (e ▸ hu)) h) (fun u hu e => ?_) (fun u hu e => ?_)
    · have h0 : m (vPrevA v) ≠ 0#u64 := by rw [← e]; exact hne0 u (List.mem_append_left _ hu)
      rw [e]; exact hNp h0
    · have h0 : m (P1.vNextA v) ≠ 0#u64 := by
        rw [← e]; exact hne0 u (by simp [hu])
      rw [e]; exact hPn h0
  · cases l1 with
    | nil =>
      have e : m (vPrevA v) = 0#u64 := hat.2
      rw [if_pos e, hat.1]; rfl
    | cons x l1' =>
      have hxm := vlastD_mem l1' x 0#u64
      have e : m (vPrevA v) = vlastD (x :: l1') 0#u64 := hat.2
      have h0 : m (vPrevA v) ≠ 0#u64 := by rw [e]; exact hne0 _ (List.mem_append_left _ hxm)
      rw [if_neg h0]; rfl

end

/-! ## Memory-level list invariant -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {V X U : Set U64} {th : TypedHeap}

/-- The list's head and link words (the words `VList` reads). -/
def LW (st : machine.Store S) [L : P1.LawfulStore st] (V : Set U64) (s : S) (b : U64) : Prop :=
  b = P1.vHeadA st s ∨ ∃ w ∈ V, b = P1.vNextA w ∨ b = vPrevA w

/-- **The VCPU list invariant** (module docstring). -/
structure VList (st : machine.Store S) [L : P1.LawfulStore st] (V : Set U64) (th : TypedHeap) (s : S) : Prop where
  lst : ∃ l : List U64, l.Nodup ∧ (∀ w, w ∈ l ↔ w ∈ V) ∧ L.mem s (P1.vHeadA st s) = vhd0 l 0#u64 ∧
    VSeg (L.mem s) 0#u64 l 0#u64
  hd : P1.Aligned (P1.vHeadA st s) ∧ ¬ JW V th (P1.vHeadA st s) ∧ ¬ SW th (P1.vHeadA st s)

theorem VSeg.listed {s : S} {l : List U64} (hs : VSeg (L.mem s) 0#u64 l 0#u64)
    (hh : L.mem s (P1.vHeadA st s) = vhd0 l 0#u64) (w : U64) : P1.VListed st s w ↔ w ∈ l := by
  have all : ∀ (l : List U64) {p : U64}, VSeg (L.mem s) p l 0#u64 →
      (∀ w l', l = w :: l' → P1.VListed st s w) → ∀ u ∈ l, P1.VListed st s u := by
    intro l
    induction l with
    | nil => intro p _ _ u hu; simp at hu
    | cons w l ih =>
      intro p h hw u hu
      have hW := hw w l rfl
      simp only [VSeg] at h
      obtain ⟨-, -, h2, h3⟩ := h
      rcases List.mem_cons.1 hu with e | hu
      · rw [e]; exact hW
      · refine ih h3 (fun x l'' e => ?_) u hu
        subst e
        have e2 : L.mem s (P1.vNextA w) = x := h2
        have hx0 : x ≠ 0#u64 := VSeg.ne0 h3 x (by simp)
        have := P1.VListed.next hW (by rw [e2]; exact hx0)
        rwa [e2] at this
  constructor
  · intro h
    induction h with
    | head h0 =>
      rw [hh] at h0 ⊢
      rcases vhd0_mem (l := l) (n := 0#u64) with e | e
      · exact absurd e h0
      · exact e
    | next _ h0 ih =>
      rcases hs.next _ ih with e | e
      · exact absurd e h0
      · exact e
  · intro hw
    refine all l hs (fun x l' e => ?_) w hw
    subst e
    have e2 : L.mem s (P1.vHeadA st s) = x := hh
    have hx0 : x ≠ 0#u64 := VSeg.ne0 hs x (by simp)
    have := P1.VListed.head (st := st) (s := s) (by rw [e2]; exact hx0)
    rwa [e2] at this

variable {s : S}

/-- **`hL`** (gen 22): the list's members are exactly `V`. -/
theorem VList.hL (Vl : VList st V th s) : ∀ w, P1.VListed st s w ↔ w ∈ V := by
  obtain ⟨l, -, hm, hh, hs⟩ := Vl.lst
  intro w; rw [VSeg.listed hs hh w, hm]

/-- **`hP`** (gen 22): a nonzero `PREV` of a VCPU of `V` is in `V` (the doubly-linked invariant). -/
theorem VList.hP (Vl : VList st V th s) : ∀ w ∈ V, L.mem s (vPrevA w) ≠ 0#u64 → L.mem s (vPrevA w) ∈ V := by
  obtain ⟨l, -, hm, -, hs⟩ := Vl.lst
  intro w hw h0
  rcases hs.prev w ((hm w).2 hw) with e | e
  · exact absurd e h0
  · exact (hm _).1 e

/-- **`hhd`** (gen 22). -/
theorem VList.hhd (Vl : VList st V th s) :
    P1.Aligned (P1.vHeadA st s) ∧ ¬ JW V th (P1.vHeadA st s) ∧ ¬ SW th (P1.vHeadA st s) := Vl.hd

/-- The next VCPU of a VCPU of `V` is 0 or in `V`. -/
theorem VList.next (Vl : VList st V th s) : ∀ w ∈ V, L.mem s (P1.vNextA w) ≠ 0#u64 →
    L.mem s (P1.vNextA w) ∈ V := by
  obtain ⟨l, -, hm, -, hs⟩ := Vl.lst
  intro w hw h0
  rcases hs.next w ((hm w).2 hw) with e | e
  · exact absurd e h0
  · exact (hm _).1 e

/-- The head is 0 or in `V`. -/
theorem VList.head (Vl : VList st V th s) : L.mem s (P1.vHeadA st s) ≠ 0#u64 → L.mem s (P1.vHeadA st s) ∈ V := by
  obtain ⟨l, -, hm, hh, -⟩ := Vl.lst
  intro h0
  rw [hh] at h0 ⊢
  rcases vhd0_mem (l := l) (n := 0#u64) with e | e
  · exact absurd e h0
  · exact (hm _).1 e

/-- The empty list. -/
theorem VList.empty (h0 : L.mem s (P1.vHeadA st s) = 0#u64)
    (hd : P1.Aligned (P1.vHeadA st s) ∧ ¬ JW ∅ th (P1.vHeadA st s) ∧ ¬ SW th (P1.vHeadA st s)) :
    VList st ∅ th s :=
  ⟨⟨[], List.nodup_nil, fun w => by simp, h0, by simp only [VSeg]⟩, hd⟩

/-- **The frame** (module docstring). -/
theorem VList.frame (Vl : VList st V th s) {s' : S} {th' : TypedHeap} (hk : L.ksb s' = L.ksb s)
    (hw : ∀ b, LW st V s b → L.mem s' b = L.mem s b)
    (hth : ∀ b, JW V th' b → JW V th b) (hsw : ∀ b, SW th' b → SW th b) : VList st V th' s' := by
  have ea : P1.vHeadA st s' = P1.vHeadA st s := by unfold P1.vHeadA; rw [hk]
  obtain ⟨l, hnd, hm, hh, hs⟩ := Vl.lst
  refine ⟨⟨l, hnd, hm, ?_, hs.congr fun u hu => ⟨hw _ (Or.inr ⟨u, (hm u).1 hu, Or.inl rfl⟩),
    hw _ (Or.inr ⟨u, (hm u).1 hu, Or.inr rfl⟩)⟩⟩, ?_⟩
  · rw [ea, hw _ (Or.inl rfl)]; exact hh
  · rw [ea]
    exact ⟨Vl.hd.1, fun h => Vl.hd.2.1 (hth _ h), fun h => Vl.hd.2.2 (hsw _ h)⟩

/-- **The frame along a footprint** missing the list words. -/
theorem VList.writes (Vl : VList st V th s) {s' : S} {W : U64 → Prop} (hW : P1.WritesIn st s s' W)
    (hl : ∀ b, LW st V s b → P1.Aligned b ∧ ¬ W b) : VList st V th s' :=
  Vl.frame hW.1 (fun b hb => hW.mem_eq (hl b hb).1 (hl b hb).2) (fun _ h => h) (fun _ h => h)

/-- The typed heap's `JW` / `SW` words not grown. -/
theorem VList.mono_th (Vl : VList st V th s) {th' : TypedHeap} (hth : ∀ b, JW V th' b → JW V th b)
    (hsw : ∀ b, SW th' b → SW th b) : VList st V th' s :=
  Vl.frame rfl (fun _ _ => rfl) hth hsw

/-- `JW` over a smaller `V`. -/
theorem jw_mono_V {V V' : Set U64} (h : V' ⊆ V) {b : U64} (hb : JW V' th b) : JW V th b := by
  rcases hb with h1 | h1 | ⟨w, hw, e⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr ⟨w, h hw, e⟩)

/-- `JW` over `insert v V`. -/
theorem jw_insert {v b : U64} (hb : JW (insert v V) th b) : JW V th b ∨ b = vTcbA v := by
  rcases hb with h1 | h1 | ⟨w, hw, e⟩
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr (Or.inl h1))
  · rcases Set.mem_insert_iff.1 hw with rfl | hw
    · exact Or.inr e
    · exact Or.inl (Or.inr (Or.inr ⟨w, hw, e⟩))

/-- The list words of `V` are aligned (VCPUs 2^15-aligned and fitting, the head word aligned). -/
theorem VList.lw_al (Vl : VList st V th s) (hf : ∀ w ∈ V, w.val % 32768 = 0 ∧ w.val + 32768 ≤ 2 ^ 64)
    {b : U64} (hb : LW st V s b) : P1.Aligned b := by
  rcases hb with rfl | ⟨w, hw, rfl | rfl⟩
  · exact Vl.hd.1
  · have := lay_next_val (hf w hw).2; have := (hf w hw).1; unfold P1.Aligned; omega
  · have := lay_prev_val (hf w hw).2; have := (hf w hw).1; unfold P1.Aligned; omega

/-! ## `_of` corollaries: gen 22's `hL` / `hP` / `hhd` from `VList` -/

/-- **`JVLay.finPl` over `VList`** (`hL`, `hP`, `hhd` discharged; `hnd` [J] as before). -/
theorem JVLay.finPlV (Ly : JVLay V th U) (Vl : VList st V th s) {v : U64} (hv : v ∈ V)
    (hnd : ∀ b, (b = ipiA st s ∨ b = actA st s) → ∀ w ∈ V, b.val < w.val ∨ w.val + 32768 ≤ b.val) :
    FinPl st V th (fun _ => U) s v :=
  Ly.finPl hv Vl.hL Vl.hP Vl.hd hnd

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {ar : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **`JAtZ.finPl` over `VList`**: no list [J] left. -/
theorem JAtZ.finPlV (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ)
    (Vl : VList st V Z.th s) {v : U64} (hv : v ∈ V) : FinPl st V Z.th (fun _ => BufU Z σ) s v :=
  J.finPl Jv hv Vl.hL Vl.hP Vl.hd

/-- **`vcpu_finalise_jv_lay` over `VList`**: `hL`, `hP`, `hhd` removed. -/
theorem vcpu_finalise_jv_vl (hA : P0.ArchTotal ar) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Jv : JVm (L := L) V H s σ) (E : JExtV (L := L) V X Z.th s) (R : RunVmB (L := L) Z.th s)
    (Vl : VList st V Z.th s) (a' : A) {v : U64} (hvV : v ∈ V) :
    vcpu.finalise st ar s a' v ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ∧
      L.mem r.1 (vTcbA v) = 0#u64 ⦄ :=
  vcpu_finalise_jv_lay hA J Jv E R a' hvV Vl.hL Vl.hP Vl.hd

end

end

end Fl4Proofs.P3
