-- AArch64 port of Fl4Proofs.P1.TimerRBZip (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d, TIMER-RB-PLAN stage 3a): the zipper over the abstract timer tree.  A context `Ctx` is the path
from the root to a subtree; `rep_plug` splits the heap relation of a whole tree into the path (`CRep`: each
path node's links, colour and sibling subtree, ending at the root word) and the subtree.  Rotations at a node
keep the in-order key list (`rotL_keys`, `rotR_keys`), so `Nodup`, membership, the deadline order and the
leftmost key of the whole tree are kept (`plug_keys_congr`).
-/
import Fl4ProofsA64.P1.TimerRB
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64

namespace TRB

/-- A path from the root down to a hole: `lc c k r up` = the hole is the left child of node `k` (colour `c`,
right subtree `r`), whose own path is `up`; `rc` symmetric. -/
inductive Ctx where
  | top : Ctx
  | lc (c : Bool) (k : U64) (r : RBT) (up : Ctx) : Ctx
  | rc (c : Bool) (l : RBT) (k : U64) (up : Ctx) : Ctx

namespace Ctx

def plug : Ctx → RBT → RBT
  | top, t => t
  | lc c k r up, t => up.plug (.node c t k r)
  | rc c l k up, t => up.plug (.node c l k t)

/-- The hole's parent key (`0` at the top). -/
def par : Ctx → U64
  | top => 0#u64
  | lc _ k _ _ => k
  | rc _ _ k _ => k

theorem plug_keys_congr : ∀ (ctx : Ctx) {t t' : RBT}, t.keys = t'.keys →
    (ctx.plug t).keys = (ctx.plug t').keys
  | top, _, _, e => e
  | lc c k r up, t, t', e => plug_keys_congr up (t := .node c t k r) (t' := .node c t' k r)
      (by simp only [RBT.keys, e])
  | rc c l k up, t, t', e => plug_keys_congr up (t := .node c l k t) (t' := .node c l k t')
      (by simp only [RBT.keys, e])

/-- The subtree's keys are keys of the whole tree. -/
theorem keys_sub : ∀ (ctx : Ctx) (t : RBT), ∀ y ∈ t.keys, y ∈ (ctx.plug t).keys
  | top, _, _, h => h
  | lc c k r up, t, y, h => keys_sub up _ y (by simp [RBT.keys, h])
  | rc c l k up, t, y, h => keys_sub up _ y (by simp [RBT.keys, h])

end Ctx

/-- `CRep k R ctx x`: the heap path `ctx`, from the root word `R` down to the hole, whose child link names
`x`. -/
inductive CRep (k : Links) (R : U64) : Ctx → U64 → Prop
  | top {x : U64} : R = x → CRep k R .top x
  | lc {c : Bool} {kk : U64} {r : RBT} {up : Ctx} {x : U64} : kk ≠ 0#u64 → k.l kk = x → k.red kk = c →
      k.p kk = up.par → Rep k kk (k.r kk) r → CRep k R up kk → CRep k R (.lc c kk r up) x
  | rc {c : Bool} {l : RBT} {kk : U64} {up : Ctx} {x : U64} : kk ≠ 0#u64 → k.r kk = x → k.red kk = c →
      k.p kk = up.par → Rep k kk (k.l kk) l → CRep k R up kk → CRep k R (.rc c l kk up) x

/-- **Zipper split.** The whole tree from the root word `R` is `ctx.plug t` iff the path is `ctx` (ending at
`t`'s root) and the subtree at the hole, with parent `ctx.par`, is `t`. -/
theorem rep_plug {k : Links} {R : U64} : ∀ (ctx : Ctx) (t : RBT),
    Rep k 0#u64 R (ctx.plug t) ↔ CRep k R ctx t.rootKey ∧ Rep k ctx.par t.rootKey t
  | .top, t => by
    constructor
    · intro h
      have e := h.root
      subst e
      exact ⟨.top rfl, h⟩
    · rintro ⟨hc, h⟩
      cases hc with
      | top e => rw [e]; exact h
  | .lc c kk r up, t => by
    show Rep k 0#u64 R (up.plug (.node c t kk r)) ↔ _
    rw [rep_plug up]
    show CRep k R up kk ∧ Rep k up.par kk (.node c t kk r) ↔ CRep k R (.lc c kk r up) t.rootKey ∧ Rep k kk t.rootKey t
    constructor
    · rintro ⟨hu, hn⟩
      cases hn with
      | node hx hp hc hl hr =>
        have e := hl.root
        exact ⟨.lc hx e hc hp hr hu, e ▸ hl⟩
    · rintro ⟨hc, h⟩
      cases hc with
      | lc hx hl hcol hp hr hu =>
        refine ⟨hu, .node hx hp hcol ?_ hr⟩
        rw [hl]; exact h
  | .rc c l kk up, t => by
    show Rep k 0#u64 R (up.plug (.node c l kk t)) ↔ _
    rw [rep_plug up]
    show CRep k R up kk ∧ Rep k up.par kk (.node c l kk t) ↔ CRep k R (.rc c l kk up) t.rootKey ∧ Rep k kk t.rootKey t
    constructor
    · rintro ⟨hu, hn⟩
      cases hn with
      | node hx hp hc hl hr =>
        have e := hr.root
        exact ⟨.rc hx e hc hp hl hu, e ▸ hr⟩
    · rintro ⟨hc, h⟩
      cases hc with
      | rc hx hr hcol hp hl hu =>
        refine ⟨hu, .node hx hp hcol hl ?_⟩
        rw [hr]; exact h

/-- Left rotation at the subtree's root (`timer::rotate_left`): `x(a, y(b, g))` ↦ `y(x(a, b), g)`, colours
kept. -/
def rotL : RBT → RBT
  | .node cx a x (.node cy b y g) => .node cy (.node cx a x b) y g
  | t => t

/-- Right rotation (`timer::rotate_right`): `x(y(a, b), g)` ↦ `y(a, x(b, g))`. -/
def rotR : RBT → RBT
  | .node cx (.node cy a y b) x g => .node cy a y (.node cx b x g)
  | t => t

theorem rotL_keys : ∀ t : RBT, (rotL t).keys = t.keys
  | .node cx a x (.node cy b y g) => by simp [rotL, RBT.keys]
  | .node _ _ _ .leaf => rfl
  | .leaf => rfl

theorem rotR_keys : ∀ t : RBT, (rotR t).keys = t.keys
  | .node cx (.node cy a y b) x g => by simp [rotR, RBT.keys]
  | .node _ .leaf _ _ => rfl
  | .leaf => rfl

/-- A rotation anywhere in the tree keeps the whole in-order key list. -/
theorem plug_rotL_keys (ctx : Ctx) (t : RBT) : (ctx.plug (rotL t)).keys = (ctx.plug t).keys :=
  ctx.plug_keys_congr (rotL_keys t)
theorem plug_rotR_keys (ctx : Ctx) (t : RBT) : (ctx.plug (rotR t)).keys = (ctx.plug t).keys :=
  ctx.plug_keys_congr (rotR_keys t)

end TRB

end Fl4ProofsA64.P1
