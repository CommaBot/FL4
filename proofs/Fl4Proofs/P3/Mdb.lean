/-
P3 (DESIGN.md §9), CSpace: the state relation for the derivation tree.

FL4 keeps seL4's C representation (obj.rs, cdt.rs): each slot's `prev` and
`next` words link the slots into doubly linked lists in which every slot is
followed by its descendants; the `revocable` bit is seL4's `mdbRevocable`
and the `first_badged` bit `mdbFirstBadged`. The spec has a parent map
`cdt : cslot_ptr ⇀ cslot_ptr` and `is_original_cap`.

The relation goes through a ghost (`MdbGhost`): the list of chains (each a
list of slot addresses in `next` order) and the parent of each slot by
address.

* `MdbLinks th mem G` (concrete, hypothesis/P1 invariant): the chains are
  exactly the non-null slots of the typed heap; consecutive slots of a chain
  are linked both ways, a chain's first slot has `prev = 0` and its last
  `next = 0`; and `MdbTree.MdbOK G.par G.chains`: every slot is followed in
  its chain by exactly its descendants.
* `CdtRel th σ G mem`: on the slots of the typed heap (`AbsSlot`), the spec's
  `cdt` is the ghost parent map through `cslotAddr`, nothing else has a
  parent in the spec, and `is_original_cap` is the `revocable` bit.

Not related here: `first_badged` (no spec counterpart), the deterministic
spec's `cdt_list` (the order of siblings; the theorems are for the
nondeterministic spec, `Z = Unit`), and the fact that `is_mdb_parent_of`
computes the ghost parent relation from caps and flags (needed for revoke and
`ensure_no_children`, not for insert/move/swap/empty).
-/
import Fl4Proofs.P3.Links
import Fl4Proofs.P3.MdbTree
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section
set_option linter.unusedSimpArgs false

/-! ## Canonical slot addresses -/

theorem canonical_zero : Canonical 0#u64 := Or.inl (fun j hj _ => by simp)

theorem canonical_of_high {a : U64} (h : 2 ^ 64 - 2 ^ 47 ≤ a.val) : Canonical a := by
  right
  intro j hj hj'
  rw [← BitVec.getLsbD_eq_getElem]
  show a.val.testBit j = true
  have ha := a.hBounds
  simp only [UScalarTy.U64_numBits_eq] at ha
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  interval_cases j <;> omega

theorem IsSlot.canonical {th : TypedHeap} (hP : Placed th) {a : U64} (h : IsSlot th a) : Canonical a :=
  canonical_of_high (h.high hP)

/-! ## Words of slots -/

theorem wordOf_val {a k : U64} (h : a.val + k.val < 2 ^ 64) : (wordOf a k).val = a.val + k.val := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega

theorem wordOf_zero (a : U64) : wordOf a 0#u64 = a := by
  apply UScalar.eq_of_val_eq
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]

/-- The offset of one of a slot's four words. -/
def Off (k : U64) : Prop := k = 0#u64 ∨ k = 8#u64 ∨ k = 16#u64 ∨ k = 24#u64

theorem Off.lt {k : U64} (h : Off k) : k.val < 32 ∧ k.val % 8 = 0 := by
  rcases h with rfl | rfl | rfl | rfl <;> simp

theorem capAt_words (mem : U64 → U64) (a : U64) :
    capAt mem a = capability.Cap.decode (mem (wordOf a 0#u64)) (mem (wordOf a 8#u64)) := by
  rw [wordOf_zero]; rfl

section Frame
variable {th : TypedHeap} (hP : Placed th)
include hP

theorem slot_word_val {a k : U64} (ha : IsSlot th a) (hk : Off k) : (wordOf a k).val = a.val + k.val :=
  wordOf_val (by have := ha.fit hP; have := hk.lt; omega)

theorem slot_word_aligned {a k : U64} (ha : IsSlot th a) (hk : Off k) : P1.Aligned (wordOf a k) := by
  unfold P1.Aligned; rw [slot_word_val hP ha hk]; have := ha.align hP; have := hk.lt; omega

theorem slot_word_eq_iff {a b k l : U64} (ha : IsSlot th a) (hb : IsSlot th b) (hk : Off k) (hl : Off l) :
    (wordOf a k).val = (wordOf b l).val ↔ a = b ∧ k = l := by
  rw [slot_word_val hP ha hk, slot_word_val hP hb hl]
  constructor
  · intro h
    by_cases hab : a = b
    · subst hab; exact ⟨rfl, UScalar.eq_of_val_eq (by omega)⟩
    · have := ha.apart hP hb hab; have := hk.lt; have := hl.lt; omega
  · rintro ⟨rfl, rfl⟩; rfl

variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem mem_wr_slot {a b k l : U64} (ha : IsSlot th a) (hb : IsSlot th b) (hk : Off k) (hl : Off l)
    (s : S) (v : U64) :
    L.mem (L.wr s (wordOf b l) v) (wordOf a k) = if a = b ∧ k = l then v else L.mem s (wordOf a k) := by
  rw [P1.LawfulStore.mem_wr_val (slot_word_aligned hP hb hl) (slot_word_aligned hP ha hk)]
  have := slot_word_eq_iff hP hb ha hl hk
  by_cases h : b = a ∧ l = k
  · obtain ⟨rfl, rfl⟩ := h; simp
  · have h' : ¬ (a = b ∧ k = l) := fun ⟨h1, h2⟩ => h ⟨h1.symm, h2.symm⟩
    simp only [h', ↓reduceIte, ite_eq_right_iff]
    intro e; exact absurd (this.1 e) h

/-- Writing a link word leaves every cap alone. -/
theorem capAt_wr_link {a b l : U64} (ha : IsSlot th a) (hb : IsSlot th b) (hl : l = 16#u64 ∨ l = 24#u64)
    (s : S) (v : U64) : capAt (L.mem (L.wr s (wordOf b l) v)) a = capAt (L.mem s) a := by
  have hl' : Off l := by rcases hl with rfl | rfl <;> simp [Off]
  rw [capAt_words, capAt_words, mem_wr_slot hP ha hb (Or.inl rfl) hl', mem_wr_slot hP ha hb (Or.inr (Or.inl rfl)) hl']
  rcases hl with rfl | rfl <;> simp

theorem prevOf_wr16 {a b : U64} (ha : IsSlot th a) (hb : IsSlot th b) (s : S) (v : U64) :
    prevOf (L.mem (L.wr s (wordOf b 16#u64) v)) a = if a = b then v else prevOf (L.mem s) a := by
  unfold prevOf
  rw [mem_wr_slot hP ha hb (by simp [Off]) (by simp [Off])]; simp

theorem word24_wr16 {a b : U64} (ha : IsSlot th a) (hb : IsSlot th b) (s : S) (v : U64) :
    L.mem (L.wr s (wordOf b 16#u64) v) (wordOf a 24#u64) = L.mem s (wordOf a 24#u64) := by
  rw [mem_wr_slot hP ha hb (by simp [Off]) (by simp [Off])]; simp

theorem prevOf_wr24 {a b : U64} (ha : IsSlot th a) (hb : IsSlot th b) (s : S) (v : U64) :
    prevOf (L.mem (L.wr s (wordOf b 24#u64) v)) a = prevOf (L.mem s) a := by
  unfold prevOf
  rw [mem_wr_slot hP ha hb (by simp [Off]) (by simp [Off])]; simp

theorem word24_wr24 {a b : U64} (ha : IsSlot th a) (hb : IsSlot th b) (s : S) (v : U64) :
    L.mem (L.wr s (wordOf b 24#u64) v) (wordOf a 24#u64) = if a = b then v else L.mem s (wordOf a 24#u64) := by
  rw [mem_wr_slot hP ha hb (by simp [Off]) (by simp [Off])]; simp

/-- Writing a cap word leaves every link word alone. -/
theorem link_wr_cap {a b k l : U64} (ha : IsSlot th a) (hb : IsSlot th b) (hk : k = 16#u64 ∨ k = 24#u64)
    (hl : l = 0#u64 ∨ l = 8#u64) (s : S) (v : U64) :
    L.mem (L.wr s (wordOf b l) v) (wordOf a k) = L.mem s (wordOf a k) := by
  have hk' : Off k := by rcases hk with rfl | rfl <;> simp [Off]
  have hl' : Off l := by rcases hl with rfl | rfl <;> simp [Off]
  rw [mem_wr_slot hP ha hb hk' hl']
  rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;> simp

end Frame

/-! ## The relation -/

/-- Ghost state of the derivation tree: the chains of linked slots, in
`next` order, and each slot's parent, by address. -/
structure MdbGhost where
  chains : List (List U64)
  par : U64 → Option U64

/-- Hypothesis (P1 invariant): the slot links realise the ghost chains, and
the ghost tree is laid out in them (`MdbOK`). -/
structure MdbLinks (th : TypedHeap) (mem : U64 → U64) (G : MdbGhost) : Prop where
  tree : Mdb.MdbOK G.par G.chains
  ne_nil : ∀ ch ∈ G.chains, ch ≠ []
  chain : ∀ ch ∈ G.chains, ch.IsChain (fun a b => nextOf mem a = b ∧ prevOf mem b = a)
  head : ∀ ch ∈ G.chains, ∀ h : ch ≠ [], prevOf mem (ch.head h) = 0#u64
  last : ∀ ch ∈ G.chains, ∀ h : ch ≠ [], nextOf mem (ch.getLast h) = 0#u64
  members : ∀ a, a ∈ G.chains.flatten ↔ IsSlot th a ∧ ∃ c, capAt mem a = Result.ok c ∧ c ≠ capability.Cap.Null

/-- A slot of the typed heap, as the spec names it. -/
def AbsSlot (th : TypedHeap) (sl : Fl4Spec.CslotPtr) : Prop :=
  ∃ p, sl.1 = p.bv ∧ (th p = some (.cnode sl.2.length) ∨
    (th p = some .tcb ∧ ∃ i, i < tcbSlots ∧ sl.2 = Fl4Spec.tcbCnodeIndex i))

/-- The spec's `cdt` and `is_original_cap` against the ghost tree and the
`revocable` bits. -/
structure CdtRel {Z : Type} (th : TypedHeap) (mem : U64 → U64) (σ : Fl4Spec.State Z) (G : MdbGhost) : Prop where
  cdt : ∀ sl, AbsSlot th sl → (σ.cdt sl).map cslotAddr = G.par (cslotAddr sl)
  cdt_slot : ∀ sl q, σ.cdt sl = some q → AbsSlot th sl ∧ AbsSlot th q
  orig : ∀ sl, AbsSlot th sl → σ.isOriginalCap sl = revOf mem (cslotAddr sl)
  par_slot : ∀ a b, G.par a = some b → ∃ sl, AbsSlot th sl ∧ cslotAddr sl = a

end

end Fl4Proofs.P3
