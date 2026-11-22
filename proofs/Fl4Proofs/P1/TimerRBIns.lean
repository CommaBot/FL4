/-
P1 (jc6d, TIMER-RB-PLAN stage 4, part 1): the `insert` descent.  From the root of a represented tree whose
in-order deadlines are sorted, `timer::insert`'s loop walks to a leaf hole `ctx` (the result `p` is
`ctx.par`, `go_left` its side, `first` iff no key lies before the hole) such that every key before the
hole has deadline `≤ d` and every key after it `> d`.  The fuel never runs out: the loop keeps
`height(subtree) ≤ fuel`, and a non-null `cur` is a node, of height `≥ 1` (`timer.insert_loop.desc`).
-/
import Fl4Proofs.P1.TimerRBRed
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

namespace TRB

/-- The hole's side matches `go_left` (`true` = left child; unconstrained at the top). -/
def Dir : Ctx → Bool → Prop
  | .top, _ => True
  | .lc _ _ _ _, g => g = true
  | .rc _ _ _ _, g => g = false

/-- In a sorted tree, a node's left keys come before it and its right keys after it. -/
theorem sorted_mid {R : U64 → U64 → Prop} {ctx : Ctx} {c : Bool} {l r : RBT} {k : U64}
    (h : ((ctx.plug (.node c l k r)).keys).Pairwise R) : (∀ z ∈ l.keys, R z k) ∧ (∀ z ∈ r.keys, R k z) := by
  rw [Ctx.plug_keys] at h
  have hm : (l.keys ++ k :: r.keys).Pairwise R :=
    h.sublist ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _))
  rw [List.pairwise_append, List.pairwise_cons] at hm
  exact ⟨fun z hz => hm.2.2 z hz k (List.mem_cons_self ..), hm.2.1.1⟩

/-- The descent's result: a leaf hole `ctx` of `t` with parent `p`, side `gl`, `fst` iff nothing lies
before it, deadlines `≤ d` before and `> d` after. -/
def DescOut (t : RBT) (D : U64 → Nat) (d : Nat) (r : U64 × Bool × Bool) : Prop :=
  ∃ ctx : Ctx, ctx.plug .leaf = t ∧ r.1 = ctx.par ∧ Dir ctx r.2.1 ∧ (r.2.2 = true ↔ ctx.pre = []) ∧
    (∀ z ∈ ctx.pre, D z ≤ d) ∧ (∀ z ∈ ctx.post, d < D z)

/-- The descent's loop state `(p, cur, go_left, first, fuel)`. -/
def DescInv (t : RBT) (D : U64 → Nat) (d : Nat) (x : U64 × U64 × Bool × Bool × U64) : Prop :=
  ∃ (ctx : Ctx) (sub : RBT), ctx.plug sub = t ∧ x.2.1 = sub.rootKey ∧ x.1 = ctx.par ∧ Dir ctx x.2.2.1 ∧
    (x.2.2.2.1 = true ↔ ctx.pre = []) ∧ (∀ z ∈ ctx.pre, D z ≤ d) ∧ (∀ z ∈ ctx.post, d < D z) ∧
    sub.height ≤ x.2.2.2.2.val

/-- **Attaching a new red leaf at a leaf hole** (the link part of `insert` after the descent): the hole's
link names `t0`, `t0` has null children, parent `ctx.par` and colour red, nothing else changed. -/
theorem attach_rep {k k' : Links} {R R' : U64} {ctx : Ctx} {t0 : U64}
    (h : Rep k 0#u64 R (ctx.plug .leaf)) (hd : (ctx.plug .leaf).keys.Nodup) (ht0 : t0 ≠ 0#u64)
    (hn : t0 ∉ (ctx.plug .leaf).keys)
    (et : k'.l t0 = 0#u64 ∧ k'.r t0 = 0#u64 ∧ k'.p t0 = ctx.par ∧ k'.red t0 = true)
    (eo : ∀ z, z ≠ t0 → z ≠ ctx.par → Same k k' z)
    (hu : HoleUpd k k' R R' ctx t0) :
    Rep k' 0#u64 R' (ctx.plug (.node true .leaf t0 .leaf)) := by
  obtain ⟨hc, -⟩ := (rep_plug ctx _).1 h
  have hk := Ctx.plug_keys ctx .leaf
  have hd' : (ctx.pre ++ ctx.post).Nodup := by have := hd; rw [hk] at this; exact nd_out this
  have mem : ∀ z ∈ ctx.pre ++ ctx.post, z ∈ (ctx.plug .leaf).keys := fun z hz => by
    rw [hk]; simp only [List.mem_append] at hz ⊢; tauto
  refine (rep_plug ctx _).2 ⟨hc.hole hd' (fun z hz hzp => eo z (fun e => hn (e ▸ mem z hz)) hzp) hu, ?_⟩
  exact .node ht0 et.2.2.1 et.2.2.2 (.leaf _ _ et.1) (.leaf _ _ et.2.1)

/-- The keys after attaching: `t0` sits exactly at the hole. -/
theorem attach_keys (ctx : Ctx) (t0 : U64) :
    (ctx.plug (.node true .leaf t0 .leaf)).keys = ctx.pre ++ t0 :: ctx.post := by
  rw [Ctx.plug_keys]; simp [RBT.keys]

/-- Sortedness after attaching a key whose deadline separates the two sides. -/
theorem attach_sorted {D : U64 → Nat} {ctx : Ctx} {t0 : U64}
    (hs : (ctx.plug .leaf).keys.Pairwise (fun a b => D a ≤ D b))
    (hpre : ∀ z ∈ ctx.pre, D z ≤ D t0) (hpost : ∀ z ∈ ctx.post, D t0 < D z) :
    (ctx.plug (.node true .leaf t0 .leaf)).keys.Pairwise (fun a b => D a ≤ D b) := by
  rw [attach_keys]
  rw [Ctx.plug_keys] at hs
  have hs' : (ctx.pre ++ ctx.post).Pairwise (fun a b => D a ≤ D b) := by simpa [RBT.keys] using hs
  rw [List.pairwise_append] at hs' ⊢
  refine ⟨hs'.1, List.pairwise_cons.2 ⟨fun z hz => Nat.le_of_lt (hpost z hz), hs'.2.1⟩, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact hpre a ha
  · exact hs'.2.2 a ha b hb

/-- The leftmost key after attaching: `t0` iff nothing lies before the hole (`first`), else unchanged. -/
theorem attach_min (ctx : Ctx) (t0 : U64) :
    (ctx.plug (.node true .leaf t0 .leaf)).minKey = if ctx.pre = [] then t0 else (ctx.plug .leaf).minKey := by
  unfold RBT.minKey
  rw [attach_keys, Ctx.plug_keys]
  cases ctx.pre with
  | nil => simp [RBT.keys]
  | cons a l => simp [RBT.keys]

end TRB

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **The `insert` descent.** -/
theorem timer.insert_loop.desc (s : S) (d f : U64) {R : U64} {t : TRB.RBT} (h : TRB.Rep (lk st s) 0#u64 R t)
    (hs : t.keys.Pairwise (fun a b => (L.mem s (tdA a)).val ≤ (L.mem s (tdA b)).val)) (hh : t.height ≤ f.val) :
    timer.insert_loop st s d 0#u64 R false true f ⦃ r => TRB.DescOut t (fun z => (L.mem s (tdA z)).val) d.val r ⦄ := by
  unfold timer.insert_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.2.2.val)
    (inv := TRB.DescInv t (fun z => (L.mem s (tdA z)).val) d.val)
  · rintro ⟨p1, c1, g1, fst1, f1⟩ ⟨ctx, sub, ep, ec, epp, edir, efst, hpre, hpost, hht⟩
    simp only at ec epp edir efst hht
    have hsub := ((TRB.rep_plug ctx sub).1 (by rw [ep]; exact h)).2
    rw [← ec] at hsub
    unfold timer.insert_loop.body
    step with obj.Tcb.is_null.spec as ⟨bn, ebn⟩
    split
    · rename_i hb
      have h0 : c1 = 0#u64 := by rw [ebn] at hb; exact of_decide_eq_true hb
      simp only [WP.spec_ok]
      cases sub with
      | leaf => exact ⟨ctx, ep, epp, edir, efst, hpre, hpost⟩
      | node cc l kk r =>
        exfalso
        have : c1 = kk := ec
        exact TRB.Rep.keys_ne0 hsub kk (by simp [TRB.RBT.keys]) (this.symm.trans h0)
    · rename_i hb
      have hc0 : c1 ≠ 0#u64 := fun e => hb (by rw [ebn, e]; rfl)
      cases sub with
      | leaf => exact absurd ec hc0
      | node cc l kk r =>
        have ekk : c1 = kk := ec
        subst kk
        have hf : 0 < f1.val := by simp only [TRB.RBT.height] at hht; omega
        have hlr : l.height + 1 ≤ f1.val ∧ r.height + 1 ≤ f1.val := by
          simp only [TRB.RBT.height] at hht; omega
        have hso : (∀ z ∈ l.keys, (L.mem s (tdA z)).val ≤ (L.mem s (tdA c1)).val) ∧
            (∀ z ∈ r.keys, (L.mem s (tdA c1)).val ≤ (L.mem s (tdA z)).val) :=
          TRB.sorted_mid (ctx := ctx) (c := cc) (by rw [ep]; exact hs)
        split
        · step as ⟨f2, hf2⟩
          have hf2' : f2.val = f1.val - 1 := by scalar_tac
          step with obj.Tcb.timer_deadline.val as ⟨i, ei⟩
          split
          · rename_i hlt
            have hlt' : d.val < (L.mem s (tdA c1)).val := by rw [← ei]; scalar_tac
            step with timer.left.rep (st := st) s hsub as ⟨c2, ec2⟩
            try simp only [WP.spec_ok]
            refine ⟨⟨.lc cc c1 r ctx, l, ep, ec2, rfl, rfl, efst, hpre, ?_, by show l.height ≤ f2.val; omega⟩,
              by show f2.val < f1.val; omega⟩
            intro z hz
            simp only [TRB.Ctx.post, List.mem_cons, List.mem_append] at hz
            rcases hz with rfl | hz | hz
            · exact hlt'
            · exact Nat.lt_of_lt_of_le hlt' (hso.2 z hz)
            · exact hpost z hz
          · rename_i hlt
            have hle : (L.mem s (tdA c1)).val ≤ d.val := by rw [← ei]; scalar_tac
            step with timer.right.rep (st := st) s hsub as ⟨c2, ec2⟩
            try simp only [WP.spec_ok]
            refine ⟨⟨.rc cc l c1 ctx, r, ep, ec2, rfl, rfl, by simp [TRB.Ctx.pre], ?_, hpost, by show r.height ≤ f2.val; omega⟩,
              by show f2.val < f1.val; omega⟩
            intro z hz
            simp only [TRB.Ctx.pre, List.mem_append, List.mem_singleton] at hz
            rcases hz with (hz | hz) | rfl
            · exact hpre z hz
            · exact Nat.le_trans (hso.1 z hz) hle
            · exact hle
        · rename_i hz
          exfalso; apply hz; scalar_tac
  · exact ⟨.top, t, rfl, h.root, rfl, trivial, by simp [TRB.Ctx.pre], by simp [TRB.Ctx.pre],
      by simp [TRB.Ctx.post], hh⟩

end

end Fl4Proofs.P1
