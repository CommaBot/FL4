-- AArch64 port of Fl4Proofs.P1.TimerRBRead (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d, TIMER-RB-PLAN stage 2b): the timer-tree accessors (`timer.left/right/parent/is_red/root`) read the
heap links `lk`, and on a node of a represented tree they return the abstract child / parent / colour.
-/
import Fl4ProofsA64.P1.TimerRBFrame
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

namespace TRB
namespace RBT
def leftT : RBT → RBT
  | leaf => leaf
  | node _ l _ _ => l
def rightT : RBT → RBT
  | leaf => leaf
  | node _ _ _ r => r
end RBT

/-- The null-guarded left link (`timer::left`) of the root of a represented tree is its left subtree's root. -/
theorem Rep.left_root {k : Links} {par x : U64} {t : RBT} (h : Rep k par x t) :
    (if x = 0#u64 then 0#u64 else k.l x) = t.leftT.rootKey := by
  cases h with
  | leaf _ _ e => rw [if_pos e]; rfl
  | node hx _ _ hl _ => rw [if_neg hx]; exact hl.root
theorem Rep.right_root {k : Links} {par x : U64} {t : RBT} (h : Rep k par x t) :
    (if x = 0#u64 then 0#u64 else k.r x) = t.rightT.rootKey := by
  cases h with
  | leaf _ _ e => rw [if_pos e]; rfl
  | node hx _ _ _ hr => rw [if_neg hx]; exact hr.root
theorem Rep.parent_eq {k : Links} {par x : U64} {t : RBT} (h : Rep k par x t) :
    (if x = 0#u64 then 0#u64 else k.p x) = if x = 0#u64 then 0#u64 else par := by
  cases h with
  | leaf _ _ e => rw [if_pos e, if_pos e]
  | node hx hp _ _ _ => rw [if_neg hx, if_neg hx, hp]
theorem Rep.red_eq {k : Links} {par x : U64} {t : RBT} (h : Rep k par x t) :
    (if x = 0#u64 then false else k.red x) = t.isRed := by
  cases h with
  | leaf _ _ e => rw [if_pos e]; rfl
  | node hx _ hc _ _ => rw [if_neg hx, hc]; rfl

end TRB

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem timer.left.links (s : S) (x : U64) :
    timer.left st s x ⦃ v => v = if x = 0#u64 then 0#u64 else (lk st s).l x ⦄ := by
  unfold timer.left
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · rename_i hb
    have hx : x = 0#u64 := by rw [eb] at hb; exact of_decide_eq_true hb
    subst hx; simp
  · rename_i hb
    have hx : x ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    step with obj.Tcb.timer_left.val as ⟨i, ei⟩; try simp only [WP.spec_ok]
    rw [ei, if_neg hx]; rfl

theorem timer.right.links (s : S) (x : U64) :
    timer.right st s x ⦃ v => v = if x = 0#u64 then 0#u64 else (lk st s).r x ⦄ := by
  unfold timer.right
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · rename_i hb
    have hx : x = 0#u64 := by rw [eb] at hb; exact of_decide_eq_true hb
    subst hx; simp
  · rename_i hb
    have hx : x ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    step with obj.Tcb.timer_right.val as ⟨i, ei⟩; try simp only [WP.spec_ok]
    rw [ei, if_neg hx]; rfl

theorem timer.parent.links (s : S) (x : U64) :
    timer.parent st s x ⦃ v => v = if x = 0#u64 then 0#u64 else (lk st s).p x ⦄ := by
  unfold timer.parent
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · rename_i hb
    have hx : x = 0#u64 := by rw [eb] at hb; exact of_decide_eq_true hb
    subst hx; simp
  · rename_i hb
    have hx : x ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    step with obj.Tcb.timer_parent.val as ⟨i, ei⟩; try simp only [WP.spec_ok]
    rw [ei, if_neg hx]; rfl

theorem timer.is_red.links (s : S) (x : U64) :
    timer.is_red st s x ⦃ v => v = if x = 0#u64 then false else (lk st s).red x ⦄ := by
  unfold timer.is_red
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · rename_i hb
    have hx : x = 0#u64 := by rw [eb] at hb; exact of_decide_eq_true hb
    subst hx; simp
  · rename_i hb
    have hx : x ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    step with obj.Tcb.timer_height.val as ⟨i, ei⟩
    unfold timer.RED
    simp only [lift, Aeneas.Std.bind_ok, WP.spec_ok]
    rw [ei, if_neg hx]; rfl

theorem timer.root.val (s : S) (c : U64) :
    timer.root st s c ⦃ v => v = L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) ⦄ := by
  unfold timer.root
  step with obj.node_get.spec as ⟨v, ev⟩
  try simp only [WP.spec_ok]
  exact ev

/-- On a represented tree the accessors return the abstract children, parent and colour. -/
theorem timer.left.rep (s : S) {par x : U64} {t : TRB.RBT} (h : TRB.Rep (lk st s) par x t) :
    timer.left st s x ⦃ v => v = t.leftT.rootKey ⦄ :=
  WP.spec_mono (timer.left.links s x) fun v e => e.trans h.left_root
theorem timer.right.rep (s : S) {par x : U64} {t : TRB.RBT} (h : TRB.Rep (lk st s) par x t) :
    timer.right st s x ⦃ v => v = t.rightT.rootKey ⦄ :=
  WP.spec_mono (timer.right.links s x) fun v e => e.trans h.right_root
theorem timer.parent.rep (s : S) {par x : U64} {t : TRB.RBT} (h : TRB.Rep (lk st s) par x t) :
    timer.parent st s x ⦃ v => v = if x = 0#u64 then 0#u64 else par ⦄ :=
  WP.spec_mono (timer.parent.links s x) fun v e => e.trans h.parent_eq
theorem timer.is_red.rep (s : S) {par x : U64} {t : TRB.RBT} (h : TRB.Rep (lk st s) par x t) :
    timer.is_red st s x ⦃ v => v = t.isRed ⦄ :=
  WP.spec_mono (timer.is_red.links s x) fun v e => e.trans h.red_eq

end

end Fl4ProofsA64.P1
