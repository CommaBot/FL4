/-
P1 (jc6d, TIMER-RB-PLAN stage 6, part 1): the pure side of `timer::remove` and its leftmost walks.
`Ctx.app` composes paths (`plug_app`), `LSpine` is a path of left turns only (the path from a subtree's
root to its leftmost node), `plug_hole` rebuilds a tree whose hole link was re-pointed.
`timer.remove_loop0.lm`: the leftmost walk from a non-null subtree root ends at the leftmost node (the
`fuel = 0` exit is unreachable when the subtree's height is at most `fuel + 1`); the other three walks of
`remove` are the same loop.  `min_*`: the `TIMER_MIN` update of `remove` names the new leftmost node.
-/
import Fl4Proofs.P1.TimerRBInsF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

namespace TRB

namespace Ctx

/-- Path composition: `app i o` is the path `o` followed by `i` below its hole. -/
def app : Ctx → Ctx → Ctx
  | top, o => o
  | lc c k r up, o => lc c k r (app up o)
  | rc c l k up, o => rc c l k (app up o)

theorem plug_app : ∀ (i o : Ctx) (t : RBT), (app i o).plug t = o.plug (i.plug t)
  | top, _, _ => rfl
  | lc c k r up, o, t => plug_app up o (.node c t k r)
  | rc c l k up, o, t => plug_app up o (.node c l k t)

theorem app_par : ∀ (i o : Ctx), i ≠ top → (app i o).par = i.par
  | top, _, h => absurd rfl h
  | lc _ _ _ _, _, _ => rfl
  | rc _ _ _ _, _, _ => rfl

end Ctx

/-- A path of left turns only. -/
def LSpine : Ctx → Prop
  | .top => True
  | .lc _ _ _ up => LSpine up
  | .rc _ _ _ _ => False

theorem LSpine.pre : ∀ {i : Ctx}, LSpine i → i.pre = []
  | .top, _ => rfl
  | .lc _ _ _ up, h => LSpine.pre (i := up) h
  | .rc _ _ _ _, h => h.elim

theorem LSpine.of_pre : ∀ {i : Ctx}, i.pre = [] → LSpine i
  | .top, _ => trivial
  | .lc _ _ _ up, h => LSpine.of_pre (i := up) h
  | .rc _ _ _ _, h => by simp [Ctx.pre] at h

theorem LSpine.post_head : ∀ {i : Ctx}, LSpine i → i.post.headD 0#u64 = i.par
  | .top, _ => rfl
  | .lc _ _ _ _, _ => rfl
  | .rc _ _ _ _, h => h.elim

theorem LSpine.keys {i : Ctx} (h : LSpine i) (t : RBT) : (i.plug t).keys = t.keys ++ i.post := by
  rw [Ctx.plug_keys, h.pre]; simp

theorem keys_nil {t : RBT} (h : t.keys = []) : t = .leaf := by
  cases t with
  | leaf => rfl
  | node c l k r => simp [RBT.keys] at h

theorem Rep.zero {k : Links} {p x : U64} {t : RBT} (h : Rep k p x t) (hx : x = 0#u64) : t = .leaf := by
  cases h with
  | leaf => rfl
  | node h0 => exact absurd hx h0

/-- **Plugging at a re-pointed hole.** The path's links kept off the hole's parent, the hole's link
re-pointed to `x`, and the subtree `u` (root `x`, parent the hole's parent) give the whole tree. -/
theorem plug_hole {K K' : Links} {R R' x : U64} {ctx : Ctx} {t0 : U64} {u : RBT} (hc : CRep K R ctx t0)
    (hn : (ctx.pre ++ ctx.post).Nodup)
    (he : ∀ z ∈ ctx.pre ++ ctx.post, z ≠ ctx.par → Same K K' z)
    (hu : HoleUpd K K' R R' ctx x) (hx : x = u.rootKey) (h : Rep K' ctx.par x u) : Rep K' 0#u64 R' (ctx.plug u) := by
  subst hx
  exact (rep_plug ctx u).2 ⟨hc.hole hn he hu, h⟩

/-! ### The `TIMER_MIN` update -/

theorem min_head {L1 L2 : List U64} {t : U64} (hd : (L1 ++ t :: L2).Nodup) (h : (L1 ++ t :: L2).headD 0#u64 = t) :
    L1 = [] := by
  cases L1 with
  | nil => rfl
  | cons a L =>
    simp only [List.cons_append, List.headD_cons] at h
    subst h
    exact absurd (List.mem_append_right L (List.mem_cons_self ..)) (List.nodup_cons.1 hd).1

theorem min_ne {L1 L2 : List U64} {t : U64} (h : (L1 ++ t :: L2).headD 0#u64 ≠ t) :
    (L1 ++ L2).headD 0#u64 = (L1 ++ t :: L2).headD 0#u64 := by
  cases L1 with
  | nil => exact absurd rfl h
  | cons a L => rfl

/-- The keys of the tree with `t` removed. -/
abbrev delKeys (ctx : Ctx) (a b : RBT) : List U64 := ctx.pre ++ a.keys ++ b.keys ++ ctx.post

theorem plug_t_keys (ctx : Ctx) (c : Bool) (a b : RBT) (t : U64) :
    (ctx.plug (.node c a t b)).keys = (ctx.pre ++ a.keys) ++ t :: (b.keys ++ ctx.post) := by
  rw [Ctx.plug_keys]; simp [RBT.keys]

theorem delKeys_eq (ctx : Ctx) (a b : RBT) : delKeys ctx a b = (ctx.pre ++ a.keys) ++ (b.keys ++ ctx.post) := by
  simp [delKeys]

/-- `t` was the leftmost node: nothing before it, no left child, and its path turns left only. -/
theorem min_is_t {ctx : Ctx} {c : Bool} {a b : RBT} {t : U64} (hd : (ctx.plug (.node c a t b)).keys.Nodup)
    (h : (ctx.plug (.node c a t b)).minKey = t) : ctx.pre = [] ∧ a = .leaf ∧ LSpine ctx := by
  unfold RBT.minKey at h
  rw [plug_t_keys] at hd h
  have e := min_head hd h
  have e1 : ctx.pre = [] := (List.append_eq_nil_iff.1 e).1
  exact ⟨e1, keys_nil (List.append_eq_nil_iff.1 e).2, LSpine.of_pre e1⟩

/-- The new leftmost node when `t` was the leftmost one and had no right child: `t`'s parent. -/
theorem min_new_par {ctx : Ctx} {c : Bool} {a b : RBT} {t : U64} (hd : (ctx.plug (.node c a t b)).keys.Nodup)
    (h : (ctx.plug (.node c a t b)).minKey = t) (hb : b = .leaf) : (delKeys ctx a b).headD 0#u64 = ctx.par := by
  obtain ⟨e1, ea, hl⟩ := min_is_t hd h
  subst ea hb
  simp only [delKeys, e1, RBT.keys, List.nil_append]
  exact hl.post_head

/-- The new leftmost node when `t` was the leftmost one: the leftmost node `y` of its right subtree. -/
theorem min_new_r {ctx ctx2 : Ctx} {c cy : Bool} {a g : RBT} {t y : U64}
    (hd : (ctx.plug (.node c a t (ctx2.plug (.node cy .leaf y g)))).keys.Nodup)
    (h : (ctx.plug (.node c a t (ctx2.plug (.node cy .leaf y g)))).minKey = t) (h2 : LSpine ctx2) :
    (delKeys ctx a (ctx2.plug (.node cy .leaf y g))).headD 0#u64 = y := by
  obtain ⟨e1, ea, -⟩ := min_is_t hd h
  subst ea
  simp only [delKeys, e1, RBT.keys, List.nil_append, h2.keys, List.append_assoc, List.cons_append,
    List.headD_cons]

/-- `t` was not the leftmost node: the leftmost node is unchanged. -/
theorem min_keep {ctx : Ctx} {c : Bool} {a b : RBT} {t : U64} (h : (ctx.plug (.node c a t b)).minKey ≠ t) :
    (delKeys ctx a b).headD 0#u64 = (ctx.plug (.node c a t b)).minKey := by
  unfold RBT.minKey at h ⊢
  rw [plug_t_keys] at h ⊢
  rw [delKeys_eq]; exact min_ne h

end TRB

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **The leftmost walk of `remove`.** From the non-null root `x` of a represented subtree `b` of height at
most `f + 1`, `remove`'s loop returns `b`'s leftmost node `y` (`b = ctx2.plug (node cy leaf y g)` with
`ctx2` a left spine); the `fuel = 0` exit is never taken. -/
theorem timer.remove_loop0.lm (s : S) (f : U64) {par x : U64} {b : TRB.RBT} (h : TRB.Rep (lk st s) par x b)
    (hx : x ≠ 0#u64) (hh : b.height ≤ f.val + 1) :
    timer.remove_loop0 st s x f ⦃ y => ∃ ctx2 cy g, TRB.LSpine ctx2 ∧ b = ctx2.plug (.node cy .leaf y g) ⦄ := by
  unfold timer.remove_loop0
  apply loop.spec_decr_nat (measure := fun x : U64 × U64 => x.2.val)
    (inv := fun x : U64 × U64 => ∃ ctx2 sub p', TRB.LSpine ctx2 ∧ b = ctx2.plug sub ∧
      TRB.Rep (lk st s) p' x.1 sub ∧ x.1 ≠ 0#u64 ∧ sub.height ≤ x.2.val + 1)
  · rintro ⟨y1, f1⟩ ⟨ctx2, sub, p', hL, eb, hr, hy0, hht⟩
    simp only at hr hy0 hht
    unfold timer.remove_loop0.body
    step with timer.left.rep (st := st) s hr as ⟨l1, el1⟩
    step with obj.Tcb.is_null.spec as ⟨bn, ebn⟩
    cases sub with
    | leaf => exact absurd hr.root hy0
    | node cc l kk r =>
      have ek : y1 = kk := hr.root
      subst ek
      have el1' : l1 = l.rootKey := el1
      obtain ⟨-, -, hl, -⟩ := TRB.Rep.node_inv hr
      have hl' : TRB.Rep (lk st s) y1 l1 l := by rw [el1', ← hl.root]; exact hl
      split
      · rename_i hb
        have h0 : l1 = 0#u64 := by rw [ebn] at hb; exact of_decide_eq_true hb
        have e := hl'.zero h0
        subst e
        simp only [WP.spec_ok]
        exact ⟨ctx2, cc, r, hL, eb⟩
      · rename_i hb
        have hl0 : l1 ≠ 0#u64 := fun e => hb (by rw [ebn, e]; rfl)
        have hlh : 1 ≤ l.height := by
          cases l with
          | leaf => exact absurd el1' hl0
          | node => simp [TRB.RBT.height]
        have hh2 : l.height ≤ f1.val := by simp only [TRB.RBT.height] at hht; omega
        split
        · step as ⟨f2, hf2⟩
          have hf2' : f2.val = f1.val - 1 := by scalar_tac
          try simp only [WP.spec_ok]
          exact ⟨⟨.lc cc y1 r ctx2, l, y1, hL, eb, hl', hl0, by show l.height ≤ f2.val + 1; omega⟩,
            by show f2.val < f1.val; omega⟩
        · rename_i hz
          exfalso; apply hz; scalar_tac
  · exact ⟨.top, b, par, trivial, rfl, h, hx, hh⟩

theorem timer.remove_loop1.lm (s : S) (f : U64) {par x : U64} {b : TRB.RBT} (h : TRB.Rep (lk st s) par x b)
    (hx : x ≠ 0#u64) (hh : b.height ≤ f.val + 1) :
    timer.remove_loop1 st s x f ⦃ y => ∃ ctx2 cy g, TRB.LSpine ctx2 ∧ b = ctx2.plug (.node cy .leaf y g) ⦄ :=
  timer.remove_loop0.lm s f h hx hh
theorem timer.remove_loop2.lm (s : S) (f : U64) {par x : U64} {b : TRB.RBT} (h : TRB.Rep (lk st s) par x b)
    (hx : x ≠ 0#u64) (hh : b.height ≤ f.val + 1) :
    timer.remove_loop2 st s x f ⦃ y => ∃ ctx2 cy g, TRB.LSpine ctx2 ∧ b = ctx2.plug (.node cy .leaf y g) ⦄ :=
  timer.remove_loop0.lm s f h hx hh
theorem timer.remove_loop3.lm (s : S) (f : U64) {par x : U64} {b : TRB.RBT} (h : TRB.Rep (lk st s) par x b)
    (hx : x ≠ 0#u64) (hh : b.height ≤ f.val + 1) :
    timer.remove_loop3 st s x f ⦃ y => ∃ ctx2 cy g, TRB.LSpine ctx2 ∧ b = ctx2.plug (.node cy .leaf y g) ⦄ :=
  timer.remove_loop0.lm s f h hx hh

end

end Fl4Proofs.P1
