/-
P1 (jc6d, TIMER-RB-PLAN stage 1): the red-black invariant of the per-core timer trees (`timer.rs`).

The heap links of a core's tree are related (`TRB.Rep`) to an abstract red-black tree `TRB.RBT` (Okasaki /
CLRS shape: a colour on every node, `leaf` for null).  `CoreTree` is the per-core invariant (parent/child
consistency, distinct keys, all armed TCBs of that core, in-order sorted by deadline with ties as `insert`
breaks them, red-black balance, black root, `TIMER_MIN` = the leftmost node), `TimerRB` the whole-state one
(every armed TCB is in its core's tree, every unarmed TCB has null links).

Main results: `TRB.height_le_128` (a red-black tree with a black root and distinct 64-bit keys has height at
most 128 = `TREE_FUEL`, so no tree loop of `timer.rs` is ever cut off) and `TimerRB.no_link` (no timer-tree
word names an unarmed TCB, e.g. one just passed to `timer::remove`).
-/
import Fl4Proofs.P1.QueueTimerW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

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

/-- **No timer-tree word names an unarmed TCB** (e.g. `t` right after `timer::remove t`): no TCB's
left/right/parent link and no core's `TIMER_ROOT`/`TIMER_MIN`. -/
theorem TimerRB.no_link {s : S} {x : U64} (h : TimerRB st T Cs s) (hT : TcbPlaced T) (hx : x ∈ T)
    (hd : L.mem s (tdA x) = 0#u64) :
    (∀ y ∈ T, L.mem s (tlA y) ≠ x ∧ L.mem s (trA y) ≠ x ∧ L.mem s (tpA y) ≠ x) ∧
    (∀ c ∈ Cs, L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) ≠ x ∧
      L.mem s (L.nodeAt s c layout.node.TIMER_MIN) ≠ x) := by
  have hx0 : (0#u64) ≠ x := fun e => (hT x hx).ne0 (by rw [← e]; simp)
  have key : ∀ {c : U64} {t : TRB.RBT}, CoreTree st T s c t → ∀ v, v = 0#u64 ∨ v ∈ t.keys → v ≠ x :=
    fun {c t} ct v hv e => by
      subst e
      rcases hv with hv | hv
      · exact hx0 hv.symm
      · exact ct.armed v hv hd
  refine ⟨fun y hy => ?_, fun c hc => ?_⟩
  · by_cases hdy : L.mem s (tdA y) = 0#u64
    · obtain ⟨a, b, d⟩ := h.idle y hy hdy
      rw [a, b, d]; exact ⟨hx0, hx0, hx0⟩
    · obtain ⟨c, -, t, ct, hyt⟩ := h.armed y hy hdy
      obtain ⟨a, b, d⟩ := ct.rep.links y hyt
      exact ⟨key ct _ a, key ct _ b, key ct _ d⟩
  · obtain ⟨t, ct⟩ := h.tree c hc
    refine ⟨key ct _ ct.rep.root_mem, ?_⟩
    rw [ct.min]; exact key ct _ t.minKey_mem

/-- The nodes of the trees are TCBs whose links are typed: `TimerRB` gives the link part of `TimerOK` for
the TCBs of `T`. -/
theorem TimerRB.links_tz {s : S} (h : TimerRB st T Cs s) {y : U64} (hy : y ∈ T) :
    Tz T (L.mem s (tlA y)) ∧ Tz T (L.mem s (trA y)) ∧ Tz T (L.mem s (tpA y)) := by
  by_cases hdy : L.mem s (tdA y) = 0#u64
  · obtain ⟨a, b, d⟩ := h.idle y hy hdy
    rw [a, b, d]; exact ⟨Tz.zero, Tz.zero, Tz.zero⟩
  · obtain ⟨c, -, t, ct, hyt⟩ := h.armed y hy hdy
    obtain ⟨a, b, d⟩ := ct.rep.links y hyt
    have tz : ∀ v, v = 0#u64 ∨ v ∈ t.keys → Tz T v := fun v hv =>
      hv.elim (fun e => e ▸ Tz.zero) (fun m => Tz.of_mem (ct.inT v m))
    exact ⟨tz _ a, tz _ b, tz _ (d.imp_left id)⟩

end

end Fl4Proofs.P1
