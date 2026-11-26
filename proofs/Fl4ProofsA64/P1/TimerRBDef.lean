-- AArch64 port of Fl4Proofs.P1.TimerRBDef (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d7, TIMER-RB-PLAN §12 step 9a): the definitions of the timer red-black invariant (`TRB.RBT`, `TRB.Bal`,
`TRB.Rep`, `lk`, `CoreTree`, `TimerRB`) and its frame by `TAgree`, upstream of `QueueObjs` so that the P1
object invariants can carry `TimerRB` (moved verbatim from `TimerRB` / `TimerRBFrame`).
-/
import Fl4ProofsA64.P1.QueueCancel
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

namespace TRB

/-- An abstract red-black tree: `node red l k r` (`red = false` is black); `leaf` is the null link. -/
inductive RBT where
  | leaf : RBT
  | node (red : Bool) (l : RBT) (k : U64) (r : RBT) : RBT

namespace RBT

/-- The in-order key list. -/
def keys : RBT → List U64
  | leaf => []
  | node _ l k r => l.keys ++ k :: r.keys

/-- The number of nodes on a longest root–leaf path. -/
def height : RBT → Nat
  | leaf => 0
  | node _ l _ r => max l.height r.height + 1

def isRed : RBT → Bool
  | leaf => false
  | node c _ _ _ => c

/-- The root's key (`0` for the empty tree, the null link). -/
def rootKey : RBT → U64
  | leaf => 0#u64
  | node _ _ k _ => k

/-- The leftmost key (`0` for the empty tree). -/
def minKey (t : RBT) : U64 := t.keys.headD 0#u64

theorem rootKey_mem (t : RBT) : t.rootKey = 0#u64 ∨ t.rootKey ∈ t.keys := by
  cases t with
  | leaf => exact Or.inl rfl
  | node c l k r => exact Or.inr (by simp [rootKey, keys])

theorem minKey_mem (t : RBT) : t.minKey = 0#u64 ∨ t.minKey ∈ t.keys := by
  unfold minKey
  cases h : t.keys with
  | nil => exact Or.inl rfl
  | cons a l => exact Or.inr (by simp)

end RBT

open RBT

/-- `Bal t n`: every root–leaf path of `t` has `n` black nodes and no red node has a red child (CLRS
red-black properties 4 and 5). -/
inductive Bal : RBT → Nat → Prop
  | leaf : Bal .leaf 0
  | red {l r : RBT} {k : U64} {n : Nat} : Bal l n → Bal r n → l.isRed = false → r.isRed = false →
      Bal (.node true l k r) n
  | black {l r : RBT} {k : U64} {n : Nat} : Bal l n → Bal r n → Bal (.node false l k r) (n + 1)

theorem ite_bool_le (b : Bool) : (if b = true then 1 else 0) ≤ 1 := by cases b <;> simp

/-- Height ≤ twice the black height (plus one for a red root). -/
theorem Bal.height_le {t : RBT} {n : Nat} (h : Bal t n) :
    t.height ≤ 2 * n + (if t.isRed = true then 1 else 0) := by
  induction h with
  | leaf => simp [RBT.height]
  | @red l r k n hl hr bl br ihl ihr =>
    rw [bl, show ((if false = true then 1 else 0) : Nat) = 0 from rfl] at ihl
    rw [br, show ((if false = true then 1 else 0) : Nat) = 0 from rfl] at ihr
    have hm := Nat.max_le.2 ⟨ihl, ihr⟩
    show max l.height r.height + 1 ≤ 2 * n + (if true = true then 1 else 0)
    rw [show ((if true = true then 1 else 0) : Nat) = 1 from rfl]; omega
  | @black l r k n hl hr ihl ihr =>
    have a := ite_bool_le l.isRed
    have b := ite_bool_le r.isRed
    have hm := Nat.max_le.2 ⟨Nat.le_trans ihl (Nat.add_le_add_left a _),
      Nat.le_trans ihr (Nat.add_le_add_left b _)⟩
    show max l.height r.height + 1 ≤ 2 * (n + 1) + (if false = true then 1 else 0)
    rw [show ((if false = true then 1 else 0) : Nat) = 0 from rfl]; omega

/-- A tree of black height `n` has at least `2^n − 1` nodes. -/
theorem Bal.pow_le {t : RBT} {n : Nat} (h : Bal t n) : 2 ^ n ≤ t.keys.length + 1 := by
  induction h with
  | leaf => simp [RBT.keys]
  | red _ _ _ _ ihl ihr => simp only [RBT.keys, List.length_append, List.length_cons]; omega
  | black _ _ ihl ihr => simp only [RBT.keys, List.length_append, List.length_cons, pow_succ]; omega

/-- Distinct 64-bit words: at most `2^64` of them. -/
theorem nodup_len {l : List U64} (h : l.Nodup) : l.length ≤ 2 ^ 64 := by
  have hm : (l.map (fun x : U64 => (⟨x.val, x.hBounds⟩ : Fin (2 ^ 64)))).Nodup := by
    refine h.map ?_
    intro a b e
    exact UScalar.eq_of_val_eq (congrArg Fin.val e)
  have := hm.length_le_card
  simpa using this

/-- **The height bound.** A red-black tree with a black root and distinct 64-bit keys has height at most
128 (`TREE_FUEL`): `2^n ≤ |keys| + 1 ≤ 2^64 + 1` gives black height `n ≤ 64`, and height `≤ 2n`. -/
theorem height_le_128 {t : RBT} {n : Nat} (h : Bal t n) (hb : t.isRed = false) (hd : t.keys.Nodup) :
    t.height ≤ 128 := by
  have h1 := h.height_le
  rw [hb, show ((if false = true then 1 else 0) : Nat) = 0 from rfl] at h1
  have h2 := h.pow_le
  have h3 := nodup_len hd
  have e64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  have e65 : (2 : Nat) ^ 65 = 36893488147419103232 := by norm_num
  have hn : n ≤ 64 := by
    by_contra hc
    have : (2 : Nat) ^ 65 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega

/-- The heap's timer links: left, right, parent and the colour bit. -/
structure Links where
  l : U64 → U64
  r : U64 → U64
  p : U64 → U64
  red : U64 → Bool

/-- `Rep k par x t`: the heap tree reached from the link `x`, whose parent word must be `par`, is `t`.
A null link is a leaf; a non-null `x` is `node (red x) l x r` with `p x = par` and its children's
subtrees `l`, `r` reached from `l x`, `r x` with parent `x` (parent/child consistency both ways). -/
inductive Rep (k : Links) : U64 → U64 → RBT → Prop
  | leaf (par x : U64) : x = 0#u64 → Rep k par x .leaf
  | node {par x : U64} {c : Bool} {l r : RBT} : x ≠ 0#u64 → k.p x = par → k.red x = c →
      Rep k x (k.l x) l → Rep k x (k.r x) r → Rep k par x (.node c l x r)

theorem Rep.root {k : Links} {par x : U64} {t : RBT} (h : Rep k par x t) : x = t.rootKey := by
  cases h with
  | leaf _ _ e => exact e
  | node => rfl

theorem Rep.root_mem {k : Links} {par x : U64} {t : RBT} (h : Rep k par x t) : x = 0#u64 ∨ x ∈ t.keys := by
  rw [h.root]; exact t.rootKey_mem

/-- The tree is a function of the heap: `Rep` is deterministic. -/
theorem Rep.det {k : Links} {t : RBT} : ∀ {par par' x : U64} {t' : RBT}, Rep k par x t → Rep k par' x t' → t = t' := by
  induction t with
  | leaf =>
    intro par par' x t' h h'
    cases h with
    | leaf _ _ e =>
      cases h' with
      | leaf => rfl
      | node hx => exact absurd e hx
  | node c l k0 r ihl ihr =>
    intro par par' x t' h h'
    cases h with
    | node hx hp hc hl hr =>
      cases h' with
      | leaf _ _ e => exact absurd e hx
      | node hx' hp' hc' hl' hr' =>
        rw [ihl hl hl', ihr hr hr', ← hc, hc']

/-- Every link of a node of the tree is null, a node of the same tree, or (for the root's parent link)
the outer parent `par`. -/
theorem Rep.links {k : Links} {par x : U64} {t : RBT} (h : Rep k par x t) :
    ∀ y ∈ t.keys, (k.l y = 0#u64 ∨ k.l y ∈ t.keys) ∧ (k.r y = 0#u64 ∨ k.r y ∈ t.keys) ∧
      (k.p y = par ∨ k.p y ∈ t.keys) := by
  induction h with
  | leaf => intro y hy; simp [RBT.keys] at hy
  | @node par x c l r hx hp hc hl hr ihl ihr =>
    intro y hy
    simp only [RBT.keys, List.mem_append, List.mem_cons] at hy ⊢
    rcases hy with hy | hy | hy
    · obtain ⟨a, b, d⟩ := ihl y hy
      refine ⟨a.imp_right Or.inl, b.imp_right Or.inl, Or.inr ?_⟩
      rcases d with d | d
      · exact Or.inr (Or.inl d)
      · exact Or.inl d
    · subst hy
      refine ⟨(hl.root_mem).imp_right Or.inl, (hr.root_mem).imp_right (fun m => Or.inr (Or.inr m)),
        Or.inl hp⟩
    · obtain ⟨a, b, d⟩ := ihr y hy
      refine ⟨a.imp_right (fun m => Or.inr (Or.inr m)), b.imp_right (fun m => Or.inr (Or.inr m)), Or.inr ?_⟩
      rcases d with d | d
      · exact Or.inr (Or.inl d)
      · exact Or.inr (Or.inr d)

end TRB

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Cs : Set U64}

/-- The timer links at state `s` (`timer::left/right/parent`; the colour is `is_red`'s `height & RED != 0`). -/
def lk (st : machine.Store S) [L : LawfulStore st] (s : S) : TRB.Links where
  l y := L.mem s (tlA y)
  r y := L.mem s (trA y)
  p y := L.mem s (tpA y)
  red y := (L.mem s (thA y) &&& 1#u64) != 0#u64

@[simp] theorem lk_l (s : S) (y : U64) : (lk st s).l y = L.mem s (tlA y) := rfl
@[simp] theorem lk_r (s : S) (y : U64) : (lk st s).r y = L.mem s (trA y) := rfl
@[simp] theorem lk_p (s : S) (y : U64) : (lk st s).p y = L.mem s (tpA y) := rfl

/-- The timer tree of core `c` is the red-black tree `t`. -/
structure CoreTree (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) (c : U64) (t : TRB.RBT) :
    Prop where
  /-- The links from `TIMER_ROOT` form `t` (the root's parent word is null). -/
  rep : TRB.Rep (lk st s) 0#u64 (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)) t
  /-- Each TCB occurs once. -/
  nodup : t.keys.Nodup
  inT : ∀ y ∈ t.keys, y ∈ T
  /-- Every node is armed and belongs to core `c` (`core_of`). -/
  armed : ∀ y ∈ t.keys, L.mem s (tdA y) ≠ 0#u64
  core : ∀ y ∈ t.keys, (L.mem s (thA y)).val >>> 8 = c.val
  /-- In-order deadlines are non-decreasing (an equal deadline is inserted to the right). -/
  sorted : t.keys.Pairwise (fun a b => (L.mem s (tdA a)).val ≤ (L.mem s (tdA b)).val)
  /-- Red-black: a black height, no red–red edge, a black root. -/
  bal : ∃ n, TRB.Bal t n
  black : t.isRed = false
  /-- `TIMER_MIN` is the leftmost node (null for the empty tree). -/
  min : L.mem s (L.nodeAt s c layout.node.TIMER_MIN) = t.minKey

/-- **The timer-tree invariant.** Every core's tree is a red-black tree (`CoreTree`); every armed TCB is a
node of some core's tree; every unarmed TCB has null timer links. -/
structure TimerRB (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (s : S) : Prop where
  tree : ∀ c ∈ Cs, ∃ t, CoreTree st T s c t
  armed : ∀ y ∈ T, L.mem s (tdA y) ≠ 0#u64 → ∃ c ∈ Cs, ∃ t, CoreTree st T s c t ∧ y ∈ t.keys
  idle : ∀ y ∈ T, L.mem s (tdA y) = 0#u64 →
    L.mem s (tlA y) = 0#u64 ∧ L.mem s (trA y) = 0#u64 ∧ L.mem s (tpA y) = 0#u64

/-- A core's tree has height at most 128 (`TREE_FUEL`). -/
theorem CoreTree.height_le {s : S} {c : U64} {t : TRB.RBT} (h : CoreTree st T s c t) : t.height ≤ 128 := by
  obtain ⟨n, hb⟩ := h.bal
  exact TRB.height_le_128 hb h.black h.nodup

/-- A core's tree is determined by the heap. -/
theorem CoreTree.uniq {s : S} {c : U64} {t t' : TRB.RBT} (h : CoreTree st T s c t) (h' : CoreTree st T s c t') :
    t = t' := TRB.Rep.det h.rep h'.rep
end

end Fl4ProofsA64.P1

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

namespace TRB

/-- `Rep` depends only on the links of the tree's own nodes. -/
theorem Rep.congr {k k' : Links} {par x : U64} {t : RBT} (h : Rep k par x t)
    (he : ∀ y ∈ t.keys, k'.l y = k.l y ∧ k'.r y = k.r y ∧ k'.p y = k.p y ∧ k'.red y = k.red y) :
    Rep k' par x t := by
  revert he
  induction h with
  | leaf par x e => intro _; exact .leaf par x e
  | @node par x c l r hx hp hc hl hr ihl ihr =>
    intro he
    obtain ⟨e1, e2, e3, e4⟩ := he x (by simp [RBT.keys])
    refine .node hx (e3.trans hp) (e4.trans hc) ?_ ?_
    · rw [e1]; exact ihl fun y hy => he y (by simp [RBT.keys, hy])
    · rw [e2]; exact ihr fun y hy => he y (by simp [RBT.keys, hy])

end TRB

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Cs : Set U64}

/-- Two states agree on the timer words of `T` and `Cs`. -/
structure TAgree (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (s s' : S) : Prop where
  td : ∀ y ∈ T, L.mem s' (tdA y) = L.mem s (tdA y)
  tl : ∀ y ∈ T, L.mem s' (tlA y) = L.mem s (tlA y)
  tr : ∀ y ∈ T, L.mem s' (trA y) = L.mem s (trA y)
  tp : ∀ y ∈ T, L.mem s' (tpA y) = L.mem s (tpA y)
  th : ∀ y ∈ T, L.mem s' (thA y) = L.mem s (thA y)
  root : ∀ c ∈ Cs, L.mem s' (L.nodeAt s' c layout.node.TIMER_ROOT) = L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)
  min : ∀ c ∈ Cs, L.mem s' (L.nodeAt s' c layout.node.TIMER_MIN) = L.mem s (L.nodeAt s c layout.node.TIMER_MIN)

theorem CoreTree.congr {s s' : S} {c : U64} {t : TRB.RBT} (h : CoreTree st T s c t) (e : TAgree st T Cs s s')
    (hc : c ∈ Cs) : CoreTree st T s' c t := by
  have kT := h.inT
  refine ⟨?_, h.nodup, h.inT, fun y hy => by rw [e.td y (kT y hy)]; exact h.armed y hy,
    fun y hy => by rw [e.th y (kT y hy)]; exact h.core y hy, ?_, h.bal, h.black,
    by rw [e.min c hc]; exact h.min⟩
  · rw [e.root c hc]
    refine h.rep.congr fun y hy => ⟨e.tl y (kT y hy), e.tr y (kT y hy), e.tp y (kT y hy), ?_⟩
    show ((L.mem s' (thA y) &&& 1#u64) != 0#u64) = ((L.mem s (thA y) &&& 1#u64) != 0#u64)
    rw [e.th y (kT y hy)]
  · exact h.sorted.imp_of_mem fun ha hb hab => by
      rw [e.td _ (kT _ ha), e.td _ (kT _ hb)]; exact hab

/-- `TimerRB` reads only the timer words. -/
theorem TimerRB.congr {s s' : S} (h : TimerRB st T Cs s) (e : TAgree st T Cs s s') : TimerRB st T Cs s' := by
  refine ⟨fun c hc => ?_, fun y hy hd => ?_, fun y hy hd => ?_⟩
  · obtain ⟨t, ct⟩ := h.tree c hc
    exact ⟨t, ct.congr e hc⟩
  · rw [e.td y hy] at hd
    obtain ⟨c, hc, t, ct, hyt⟩ := h.armed y hy hd
    exact ⟨c, hc, t, ct.congr e hc, hyt⟩
  · rw [e.td y hy] at hd
    obtain ⟨a, b, d⟩ := h.idle y hy hd
    rw [e.tl y hy, e.tr y hy, e.tp y hy]
    exact ⟨a, b, d⟩

end

end Fl4ProofsA64.P1
