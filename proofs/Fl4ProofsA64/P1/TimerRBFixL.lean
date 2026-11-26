-- AArch64 port of Fl4Proofs.P1.TimerRBFixL (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d, TIMER-RB-PLAN stage 5, the loop): `timer::insert_fixup` keeps the red-black shape.  The loop state
`(s, z, fuel)` is in one of two modes (`FixInv`):
- `FixA`: `z` is a red node at a hole `ctx` with `CtxOK ctx n` (the only red–red edge is `z`–parent), the
  root is black unless `z` is the root, and `ctx.blk + 1 ≤ fuel`;
- `FixB` (after a rotation case): the tree is balanced and `z`'s parent is black or null.
A recolouring round (uncle red) moves `z` to the grandparent and removes one black node from the path, so
the fuel bound is kept and the `fuel = 0` exit is never taken (initially `blk ≤ 64 < 128`, `blk_le_64`).
On exit the tree is balanced (`Bal`, root possibly red); `insert_fixup` then blackens the root.
-/
import Fl4ProofsA64.P1.TimerRBFixH
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

namespace TRB

/-- Mode A: `z` red at a hole, red-black except a red–red edge at `z`, fuel bound. -/
def FixA (W : RBT) (z : U64) (f : Nat) : Prop :=
  ∃ (ctx : Ctx) (a b : RBT) (n : Nat), W = ctx.plug (.node true a z b) ∧ Bal (.node true a z b) n ∧
    CtxOK ctx n ∧ RootB ctx ∧ ctx.blk + 1 ≤ f

/-- Mode B: balanced, `z`'s parent black or null. -/
def FixB (W : RBT) (z : U64) : Prop :=
  ∃ (ctx : Ctx) (cz : Bool) (a b : RBT) (m : Nat), W = ctx.plug (.node cz a z b) ∧ ctx.parRed = false ∧ Bal W m

/-- Uncle red, parent on the left: recolour. -/
theorem fix_case1L {up : Ctx} {l r u1 u2 : RBT} {pk gk uk : U64} {n f : Nat}
    (hl : Bal l n) (hr : Bal r n) (hu : Bal (.node true u1 uk u2) n) (hc : CtxOK up (n + 1))
    (hR : RootB up) (hf : up.blk + 2 ≤ f) :
    FixA (up.plug (.node true (.node false l pk r) gk (.node false u1 uk u2))) gk (f - 1) := by
  cases hu with
  | red h1 h2 _ _ => exact ⟨up, _, _, n + 1, rfl, .red (.black hl hr) (.black h1 h2) rfl rfl, hc, hR, by omega⟩

/-- Uncle red, parent on the right: recolour. -/
theorem fix_case1R {up : Ctx} {l r u1 u2 : RBT} {pk gk uk : U64} {n f : Nat}
    (hl : Bal l n) (hr : Bal r n) (hu : Bal (.node true u1 uk u2) n) (hc : CtxOK up (n + 1))
    (hR : RootB up) (hf : up.blk + 2 ≤ f) :
    FixA (up.plug (.node true (.node false u1 uk u2) gk (.node false l pk r))) gk (f - 1) := by
  cases hu with
  | red h1 h2 _ _ => exact ⟨up, _, _, n + 1, rfl, .red (.black h1 h2) (.black hl hr) rfl rfl, hc, hR, by omega⟩

/-- Uncle black, `z` outer on the left: after recolouring and `rotate_right(g)`. -/
theorem fix_case3L {up : Ctx} {a b r u : RBT} {z pk gk : U64} {n : Nat}
    (hz : Bal (.node true a z b) n) (hr : Bal r n) (hrb : r.isRed = false) (hu : Bal u n)
    (hub : u.isRed = false) (hc : CtxOK up (n + 1)) :
    FixB (up.plug (.node false (.node true a z b) pk (.node true r gk u))) z :=
  ⟨.lc false pk (.node true r gk u) up, true, a, b, n + 1 + up.blk, rfl, rfl,
    plug_bal hc (.black hz (.red hr hu hrb hub)) (fun e => by simp [RBT.isRed] at e)⟩

/-- Uncle black, `z` outer on the right: after recolouring and `rotate_left(g)`. -/
theorem fix_case3R {up : Ctx} {a b r u : RBT} {z pk gk : U64} {n : Nat}
    (hz : Bal (.node true a z b) n) (hr : Bal r n) (hrb : r.isRed = false) (hu : Bal u n)
    (hub : u.isRed = false) (hc : CtxOK up (n + 1)) :
    FixB (up.plug (.node false (.node true u gk r) pk (.node true a z b))) z :=
  ⟨.rc false (.node true u gk r) pk up, true, a, b, n + 1 + up.blk, rfl, rfl,
    plug_bal hc (.black (.red hu hr hub hrb) hz) (fun e => by simp [RBT.isRed] at e)⟩

/-- Exit in mode A on a black or null parent: balanced. -/
theorem fixA_exit {ctx : Ctx} {a b : RBT} {z : U64} {n : Nat} (hz : Bal (.node true a z b) n)
    (hc : CtxOK ctx n) (hp : ctx.parRed = false) : Bal (ctx.plug (.node true a z b)) (n + ctx.blk) :=
  plug_bal hc hz fun _ => hp

/-- Blackening the root of a balanced tree keeps it balanced. -/
theorem Bal.blacken {c : Bool} {l r : RBT} {k : U64} {m : Nat} (h : Bal (.node c l k r) m) :
    ∃ m', Bal (.node false l k r) m' := by
  cases h with
  | red hl hr _ _ => exact ⟨_, .black hl hr⟩
  | black hl hr => exact ⟨_, .black hl hr⟩

/-- Two keys on different sides of a node are distinct; a key differs from the null root of a leaf. -/
theorem ne_rootR {ctx : Ctx} {c : Bool} {a b : RBT} {k x : U64} (hd : (ctx.plug (.node c a k b)).keys.Nodup)
    (hx : x ∈ a.keys ∨ x = k) (h0 : x ≠ 0#u64) : x ≠ b.rootKey := by
  rcases b.rootKey_mem with e | hm
  · rw [e]; exact h0
  rw [Ctx.plug_keys] at hd
  have hM : (a.keys ++ k :: b.keys).Nodup := nd_in hd
  rcases hx with hx | rfl
  · exact nd_sep hM hx (List.mem_cons_of_mem _ hm)
  · intro e
    exact (List.nodup_cons.1 (hM.sublist (List.sublist_append_right _ _))).1 (e ▸ hm)

theorem ne_rootL {ctx : Ctx} {c : Bool} {a b : RBT} {k x : U64} (hd : (ctx.plug (.node c a k b)).keys.Nodup)
    (hx : x ∈ b.keys ∨ x = k) (h0 : x ≠ 0#u64) : x ≠ a.rootKey := by
  rcases a.rootKey_mem with e | hm
  · rw [e]; exact h0
  rw [Ctx.plug_keys] at hd
  have hM : (a.keys ++ k :: b.keys).Nodup := nd_in hd
  rcases hx with hx | rfl
  · exact fun e => nd_sep hM hm (List.mem_cons_of_mem _ hx) e.symm
  · exact fun e => nd_sep hM hm (List.mem_cons_self ..) e.symm

/-- A red hole parent is not the root of a root-black tree. -/
theorem RootB.lc_red {k : U64} {r : RBT} {up : Ctx} (h : RootB (.lc true k r up)) : up ≠ .top := by
  rintro rfl
  have := h.isRed (by intro e; cases e) .leaf
  simp [Ctx.plug, RBT.isRed] at this

theorem RootB.rc_red {l : RBT} {k : U64} {up : Ctx} (h : RootB (.rc true l k up)) : up ≠ .top := by
  rintro rfl
  have := h.isRed (by intro e; cases e) .leaf
  simp [Ctx.plug, RBT.isRed] at this

end TRB

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

theorem FB.nd {s0 s : S} {c : U64} {Ks : List U64} {W : TRB.RBT} (h : FB st T s0 c Ks s W) (hd : Ks.Nodup) :
    W.keys.Nodup := by rw [h.keys]; exact hd

/-- The loop's result: the heap is a balanced tree (root possibly red). -/
abbrev FixOut (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c : U64) (Ks : List U64)
    (s : S) : Prop :=
  ∃ W m, FB st T s0 c Ks s W ∧ TRB.Bal W m

/-- The loop invariant on `(s, z, fuel)`. -/
abbrev FixInv (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c : U64) (Ks : List U64)
    (x : S × U64 × U64) : Prop :=
  ∃ W, FB st T s0 c Ks x.1 W ∧ (TRB.FixA W x.2.1 x.2.2.val ∨ TRB.FixB W x.2.1)

/-- What one round must deliver (`loop.spec_decr_nat`'s body condition, measure = fuel). -/
abbrev FixPost (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c : U64) (Ks : List U64)
    (f : U64) (r : ControlFlow (S × U64 × U64) S) : Prop :=
  match r with
  | .done y => FixOut st T s0 c Ks y
  | .cont x' => FixInv st T s0 c Ks x' ∧ x'.2.2.val < f.val

/-- A round that exits: `z`'s parent is null or black. -/
theorem fix_body_exit (s : S) (c z f : U64) {s0 : S} {Ks : List U64} {W : TRB.RBT} {m : Nat}
    (h : FB st T s0 c Ks s W) (hb : TRB.Bal W m) {p : U64} {tz : TRB.RBT} (hzr : TRB.Rep (lk st s) p z tz)
    (hz0 : z ≠ 0#u64) (hp : p = 0#u64 ∨ ∃ pp tp, TRB.Rep (lk st s) pp p tp ∧ tp.isRed = false) :
    timer.insert_fixup_loop.body st c s z f ⦃ r => FixPost st T s0 c Ks f r ⦄ := by
  unfold timer.insert_fixup_loop.body
  step with timer.parent.rep s hzr as ⟨p', hp'⟩
  rw [if_neg hz0] at hp'
  subst p'
  step with obj.Tcb.is_null.spec as ⟨bn, ebn⟩
  split
  · try simp only [WP.spec_ok]
    exact ⟨W, m, h, hb⟩
  · rename_i hbn
    have p0 : p ≠ 0#u64 := fun e => hbn (by rw [ebn, e]; rfl)
    obtain ⟨pp, tp, hpr, hpb⟩ := hp.resolve_left p0
    step with timer.is_red.rep s hpr as ⟨b1, hb1⟩
    split
    · rename_i hb'
      exfalso; rw [hb1, hpb] at hb'; exact absurd hb' (by simp)
    · try simp only [WP.spec_ok]
      exact ⟨W, m, h, hb⟩

/-- Before the rotation case's tail, parent on the left: `pp` red with red child `z1` on the left. -/
def C3L (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c : U64) (Ks : List U64)
    (up : TRB.Ctx) (gk : U64) (u : TRB.RBT) (n : Nat) (s1 : S) (z1 pp : U64) : Prop :=
  ∃ a b r, FB st T s0 c Ks s1 (up.plug (.node false (.node true (.node true a z1 b) pp r) gk u)) ∧
    TRB.Bal (.node true a z1 b) n ∧ TRB.Bal r n ∧ r.isRed = false

/-- Mirror: parent on the right, `z1` its right child. -/
def C3R (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c : U64) (Ks : List U64)
    (up : TRB.Ctx) (gk : U64) (u : TRB.RBT) (n : Nat) (s1 : S) (z1 pp : U64) : Prop :=
  ∃ a b r, FB st T s0 c Ks s1 (up.plug (.node false u gk (.node true r pp (.node true a z1 b)))) ∧
    TRB.Bal (.node true a z1 b) n ∧ TRB.Bal r n ∧ r.isRed = false

/-- The rotation case's tail, parent on the left: recolour, `rotate_right(g)`. -/
theorem fix_tailL {s0 s1 : S} {c : U64} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) {up : TRB.Ctx} {gk : U64} {u : TRB.RBT} {n : Nat} {z1 pp f1 f : U64}
    (hC : C3L st T s0 c Ks up gk u n s1 z1 pp) (hu : TRB.Bal u n) (hub : u.isRed = false)
    (hc : TRB.CtxOK up (n + 1)) (hlt : f1.val < f.val) :
    (do
      let s2 ← timer.set_red st s1 pp false
      let s3 ← timer.set_red st s2 gk true
      let s4 ← timer.rotate_right st s3 c gk
      ok (ControlFlow.cont (s4, z1, f1))) ⦃ r => FixPost st T s0 c Ks f r ⦄ := by
  obtain ⟨a, b, r, h, hz, hr, hrb⟩ := hC
  step with FB.set_red (.lc false gk u up) true (.node true a z1 b) pp r hT hd hk h false as ⟨s2, h2⟩
  step with FB.set_red up false (.node false (.node true a z1 b) pp r) gk u hT hd hk h2 true as ⟨s3, h3⟩
  step with FB.rotR up true false (.node true a z1 b) pp r gk u hT hd hk h3 as ⟨s4, h4⟩
  try simp only [WP.spec_ok]
  exact ⟨⟨_, h4, Or.inr (TRB.fix_case3L hz hr hrb hu hub hc)⟩, hlt⟩

/-- The rotation case's tail, parent on the right: recolour, `rotate_left(g)`. -/
theorem fix_tailR {s0 s1 : S} {c : U64} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) {up : TRB.Ctx} {gk : U64} {u : TRB.RBT} {n : Nat} {z1 pp f1 f : U64}
    (hC : C3R st T s0 c Ks up gk u n s1 z1 pp) (hu : TRB.Bal u n) (hub : u.isRed = false)
    (hc : TRB.CtxOK up (n + 1)) (hlt : f1.val < f.val) :
    (do
      let s2 ← timer.set_red st s1 pp false
      let s3 ← timer.set_red st s2 gk true
      let s4 ← timer.rotate_left st s3 c gk
      ok (ControlFlow.cont (s4, z1, f1))) ⦃ r => FixPost st T s0 c Ks f r ⦄ := by
  obtain ⟨a, b, r, h, hz, hr, hrb⟩ := hC
  step with FB.set_red (.rc false u gk up) true r pp (.node true a z1 b) hT hd hk h false as ⟨s2, h2⟩
  step with FB.set_red up false u gk (.node false r pp (.node true a z1 b)) hT hd hk h2 true as ⟨s3, h3⟩
  step with FB.rotL up true u gk false r pp (.node true a z1 b) hT hd hk h3 as ⟨s4, h4⟩
  try simp only [WP.spec_ok]
  exact ⟨⟨_, h4, Or.inr (TRB.fix_case3R hz hr hrb hu hub hc)⟩, hlt⟩

/-- A round with a red parent on the left of `g`, `z` a left child. -/
theorem fix_body_LL (s : S) (c f : U64) {s0 : S} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) {up : TRB.Ctx} {a b r u : TRB.RBT} {z pk gk : U64} {n : Nat}
    (h : FB st T s0 c Ks s (up.plug (.node false (.node true (.node true a z b) pk r) gk u)))
    (hz : TRB.Bal (.node true a z b) n) (hr : TRB.Bal r n) (hrb : r.isRed = false) (hu : TRB.Bal u n)
    (hc : TRB.CtxOK up (n + 1)) (hR : TRB.RootB up) (hf : up.blk + 2 ≤ f.val) :
    timer.insert_fixup_loop.body st c s z f ⦃ r => FixPost st T s0 c Ks f r ⦄ := by
  have hW := h.nd hd
  have hzr : TRB.Rep (lk st s) pk z (.node true a z b) :=
    ((TRB.rep_plug (.lc true pk r (.lc false gk u up)) (.node true a z b)).1 h.rep).2
  have hpr : TRB.Rep (lk st s) gk pk (.node true (.node true a z b) pk r) :=
    ((TRB.rep_plug (.lc false gk u up) (.node true (.node true a z b) pk r)).1 h.rep).2
  have hgr : TRB.Rep (lk st s) up.par gk (.node false (.node true (.node true a z b) pk r) gk u) :=
    ((TRB.rep_plug up _).1 h.rep).2
  have hur : TRB.Rep (lk st s) gk u.rootKey u :=
    ((TRB.rep_plug (.rc false (.node true (.node true a z b) pk r) gk up) u).1 h.rep).2
  have z0 : z ≠ 0#u64 := TRB.Rep.keys_ne0 hzr z (by simp [TRB.RBT.keys])
  have pk0 : pk ≠ 0#u64 := TRB.Rep.keys_ne0 hpr pk (by simp [TRB.RBT.keys])
  unfold timer.insert_fixup_loop.body
  step with timer.parent.rep s hzr as ⟨p, hp⟩
  rw [if_neg z0] at hp
  subst p
  step with obj.Tcb.is_null.spec as ⟨bn, ebn⟩
  split
  · rename_i hb; exfalso; exact pk0 (by rw [ebn] at hb; exact of_decide_eq_true hb)
  step with timer.is_red.rep s hpr as ⟨b1, hb1⟩
  split
  swap
  · rename_i hb; exfalso; exact hb (by rw [hb1]; rfl)
  split
  · rename_i hf0; exfalso; have : f.val = 0 := by scalar_tac
    omega
  step as ⟨f1, hf1⟩
  have hf1' : f1.val = f.val - 1 := by clear * - hf1 hf; scalar_tac
  have hlt : f1.val < f.val := by omega
  step with timer.parent.rep s hpr as ⟨g, hg⟩
  rw [if_neg pk0] at hg
  subst g
  step with timer.left.rep s hgr as ⟨t, ht⟩
  replace ht : t = pk := ht
  subst t
  step with tcb_eq.iff as ⟨b2, hb2⟩
  split
  swap
  · rename_i hb; exfalso; exact hb (hb2.2 trivial)
  step with timer.right.rep s hgr as ⟨uv, huv⟩
  replace huv : uv = u.rootKey := huv
  subst uv
  step with timer.is_red.rep s hur as ⟨b3, hb3⟩
  split
  · rename_i hb
    cases u with
    | leaf => exfalso; rw [hb3] at hb; exact absurd hb (by simp [TRB.RBT.isRed])
    | node cu u1 uk u2 =>
      have hcu : cu = true := by rw [hb3] at hb; exact hb
      subst hcu
      simp only [TRB.RBT.rootKey]
      step with FB.set_red (.lc false gk (.node true u1 uk u2) up) true (.node true a z b) pk r hT hd hk h false
        as ⟨s1, h1⟩
      step with FB.set_red (.rc false (.node false (.node true a z b) pk r) gk up) true u1 uk u2 hT hd hk h1 false
        as ⟨s2, h2⟩
      step with FB.set_red up false (.node false (.node true a z b) pk r) gk (.node false u1 uk u2) hT hd hk h2 true
        as ⟨s3, h3⟩
      try simp only [WP.spec_ok]
      refine ⟨⟨_, h3, Or.inl ?_⟩, hlt⟩
      show TRB.FixA _ gk f1.val
      rw [hf1']; exact TRB.fix_case1L hz hr hu hc hR hf
  · rename_i hb
    have hub : u.isRed = false := by rw [hb3] at hb; simpa using hb
    step with timer.right.rep s hpr as ⟨t1, ht1⟩
    replace ht1 : t1 = r.rootKey := ht1
    subst t1
    have zr : z ≠ r.rootKey := TRB.ne_rootR (ctx := .lc false gk u up) (c := true) (a := .node true a z b)
      (k := pk) hW (Or.inl (by simp [TRB.RBT.keys])) z0
    step with tcb_eq.iff as ⟨b4, hb4⟩
    have hb4f : ¬ b4 = true := fun e => zr (hb4.1 e)
    refine WP.spec_bind (Pₘ := fun x => C3L st T s0 c Ks up gk u n x.1 x.2.1 x.2.2) ?_ ?_
    · rw [if_neg hb4f]
      exact (WP.spec_ok _).2 ⟨a, b, r, h, hz, hr, hrb⟩
    · rintro ⟨s1, z1, pp⟩ hC
      exact fix_tailL hT hd hk hC hu hub hc hlt

/-- A round with a red parent on the left of `g`, `z` a right child (rotate at the parent first). -/
theorem fix_body_RL (s : S) (c f : U64) {s0 : S} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) {up : TRB.Ctx} {a b l u : TRB.RBT} {z pk gk : U64} {n : Nat}
    (h : FB st T s0 c Ks s (up.plug (.node false (.node true l pk (.node true a z b)) gk u)))
    (hz : TRB.Bal (.node true a z b) n) (hl : TRB.Bal l n) (hlb : l.isRed = false) (hu : TRB.Bal u n)
    (hc : TRB.CtxOK up (n + 1)) (hR : TRB.RootB up) (hf : up.blk + 2 ≤ f.val) :
    timer.insert_fixup_loop.body st c s z f ⦃ r => FixPost st T s0 c Ks f r ⦄ := by
  have hzr : TRB.Rep (lk st s) pk z (.node true a z b) :=
    ((TRB.rep_plug (.rc true l pk (.lc false gk u up)) (.node true a z b)).1 h.rep).2
  have hpr : TRB.Rep (lk st s) gk pk (.node true l pk (.node true a z b)) :=
    ((TRB.rep_plug (.lc false gk u up) (.node true l pk (.node true a z b))).1 h.rep).2
  have hgr : TRB.Rep (lk st s) up.par gk (.node false (.node true l pk (.node true a z b)) gk u) :=
    ((TRB.rep_plug up _).1 h.rep).2
  have hur : TRB.Rep (lk st s) gk u.rootKey u :=
    ((TRB.rep_plug (.rc false (.node true l pk (.node true a z b)) gk up) u).1 h.rep).2
  have z0 : z ≠ 0#u64 := TRB.Rep.keys_ne0 hzr z (by simp [TRB.RBT.keys])
  have pk0 : pk ≠ 0#u64 := TRB.Rep.keys_ne0 hpr pk (by simp [TRB.RBT.keys])
  unfold timer.insert_fixup_loop.body
  step with timer.parent.rep s hzr as ⟨p, hp⟩
  rw [if_neg z0] at hp
  subst p
  step with obj.Tcb.is_null.spec as ⟨bn, ebn⟩
  split
  · rename_i hb; exfalso; exact pk0 (by rw [ebn] at hb; exact of_decide_eq_true hb)
  step with timer.is_red.rep s hpr as ⟨b1, hb1⟩
  split
  swap
  · rename_i hb; exfalso; exact hb (by rw [hb1]; rfl)
  split
  · rename_i hf0; exfalso; have : f.val = 0 := by scalar_tac
    omega
  step as ⟨f1, hf1⟩
  have hf1' : f1.val = f.val - 1 := by clear * - hf1 hf; scalar_tac
  have hlt : f1.val < f.val := by omega
  step with timer.parent.rep s hpr as ⟨g, hg⟩
  rw [if_neg pk0] at hg
  subst g
  step with timer.left.rep s hgr as ⟨t, ht⟩
  replace ht : t = pk := ht
  subst t
  step with tcb_eq.iff as ⟨b2, hb2⟩
  split
  swap
  · rename_i hb; exfalso; exact hb (hb2.2 trivial)
  step with timer.right.rep s hgr as ⟨uv, huv⟩
  replace huv : uv = u.rootKey := huv
  subst uv
  step with timer.is_red.rep s hur as ⟨b3, hb3⟩
  split
  · rename_i hb
    cases u with
    | leaf => exfalso; rw [hb3] at hb; exact absurd hb (by simp [TRB.RBT.isRed])
    | node cu u1 uk u2 =>
      have hcu : cu = true := by rw [hb3] at hb; exact hb
      subst hcu
      simp only [TRB.RBT.rootKey]
      step with FB.set_red (.lc false gk (.node true u1 uk u2) up) true l pk (.node true a z b) hT hd hk h false
        as ⟨s1, h1⟩
      step with FB.set_red (.rc false (.node false l pk (.node true a z b)) gk up) true u1 uk u2 hT hd hk h1 false
        as ⟨s2, h2⟩
      step with FB.set_red up false (.node false l pk (.node true a z b)) gk (.node false u1 uk u2) hT hd hk h2 true
        as ⟨s3, h3⟩
      try simp only [WP.spec_ok]
      refine ⟨⟨_, h3, Or.inl ?_⟩, hlt⟩
      show TRB.FixA _ gk f1.val
      rw [hf1']; exact TRB.fix_case1L hl hz hu hc hR hf
  · rename_i hb
    have hub : u.isRed = false := by rw [hb3] at hb; simpa using hb
    step with timer.right.rep s hpr as ⟨t1, ht1⟩
    replace ht1 : t1 = z := ht1
    subst t1
    step with tcb_eq.iff as ⟨b4, hb4⟩
    have hb4t : b4 = true := hb4.2 trivial
    cases hz with
    | red ha hb' hab hbb =>
    refine WP.spec_bind (Pₘ := fun x => C3L st T s0 c Ks up gk u n x.1 x.2.1 x.2.2) ?_ ?_
    · rw [if_pos hb4t]
      step with FB.rotL (.lc false gk u up) true l pk true a z b hT hd hk h as ⟨s2, h2⟩
      have hn : TRB.Rep (lk st s2) z pk (.node true l pk a) :=
        ((TRB.rep_plug (.lc true z b (.lc false gk u up)) (.node true l pk a)).1 h2.rep).2
      step with timer.parent.rep s2 hn as ⟨pp1, hpp⟩
      rw [if_neg pk0] at hpp
      subst pp1
      try simp only [WP.spec_ok]
      exact ⟨l, a, b, h2, .red hl ha hlb hab, hb', hbb⟩
    · rintro ⟨s1, z1, pp⟩ hC
      exact fix_tailL hT hd hk hC hu hub hc hlt

/-- A round with a red parent on the right of `g`, `z` a right child. -/
theorem fix_body_RR (s : S) (c f : U64) {s0 : S} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) {up : TRB.Ctx} {a b l u : TRB.RBT} {z pk gk : U64} {n : Nat}
    (h : FB st T s0 c Ks s (up.plug (.node false u gk (.node true l pk (.node true a z b)))))
    (hz : TRB.Bal (.node true a z b) n) (hl : TRB.Bal l n) (hlb : l.isRed = false) (hu : TRB.Bal u n)
    (hc : TRB.CtxOK up (n + 1)) (hR : TRB.RootB up) (hf : up.blk + 2 ≤ f.val) :
    timer.insert_fixup_loop.body st c s z f ⦃ r => FixPost st T s0 c Ks f r ⦄ := by
  have hW := h.nd hd
  have hzr : TRB.Rep (lk st s) pk z (.node true a z b) :=
    ((TRB.rep_plug (.rc true l pk (.rc false u gk up)) (.node true a z b)).1 h.rep).2
  have hpr : TRB.Rep (lk st s) gk pk (.node true l pk (.node true a z b)) :=
    ((TRB.rep_plug (.rc false u gk up) (.node true l pk (.node true a z b))).1 h.rep).2
  have hgr : TRB.Rep (lk st s) up.par gk (.node false u gk (.node true l pk (.node true a z b))) :=
    ((TRB.rep_plug up _).1 h.rep).2
  have hur : TRB.Rep (lk st s) gk u.rootKey u :=
    ((TRB.rep_plug (.lc false gk (.node true l pk (.node true a z b)) up) u).1 h.rep).2
  have z0 : z ≠ 0#u64 := TRB.Rep.keys_ne0 hzr z (by simp [TRB.RBT.keys])
  have pk0 : pk ≠ 0#u64 := TRB.Rep.keys_ne0 hpr pk (by simp [TRB.RBT.keys])
  have pu : pk ≠ u.rootKey := TRB.ne_rootL (ctx := up) (c := false) (a := u)
    (b := .node true l pk (.node true a z b)) (k := gk) hW (Or.inl (by simp [TRB.RBT.keys])) pk0
  unfold timer.insert_fixup_loop.body
  step with timer.parent.rep s hzr as ⟨p, hp⟩
  rw [if_neg z0] at hp
  subst p
  step with obj.Tcb.is_null.spec as ⟨bn, ebn⟩
  split
  · rename_i hb; exfalso; exact pk0 (by rw [ebn] at hb; exact of_decide_eq_true hb)
  step with timer.is_red.rep s hpr as ⟨b1, hb1⟩
  split
  swap
  · rename_i hb; exfalso; exact hb (by rw [hb1]; rfl)
  split
  · rename_i hf0; exfalso; have : f.val = 0 := by scalar_tac
    omega
  step as ⟨f1, hf1⟩
  have hf1' : f1.val = f.val - 1 := by clear * - hf1 hf; scalar_tac
  have hlt : f1.val < f.val := by omega
  step with timer.parent.rep s hpr as ⟨g, hg⟩
  rw [if_neg pk0] at hg
  subst g
  step with timer.left.rep s hgr as ⟨t, ht⟩
  replace ht : t = u.rootKey := ht
  subst t
  step with tcb_eq.iff as ⟨b2, hb2⟩
  split
  · rename_i hb; exfalso; exact pu (hb2.1 hb)
  step with timer.is_red.rep s hur as ⟨b3, hb3⟩
  split
  · rename_i hb
    cases u with
    | leaf => exfalso; rw [hb3] at hb; exact absurd hb (by simp [TRB.RBT.isRed])
    | node cu u1 uk u2 =>
      have hcu : cu = true := by rw [hb3] at hb; exact hb
      subst hcu
      simp only [TRB.RBT.rootKey]
      step with FB.set_red (.rc false (.node true u1 uk u2) gk up) true l pk (.node true a z b) hT hd hk h false
        as ⟨s1, h1⟩
      step with FB.set_red (.lc false gk (.node false l pk (.node true a z b)) up) true u1 uk u2 hT hd hk h1 false
        as ⟨s2, h2⟩
      step with FB.set_red up false (.node false u1 uk u2) gk (.node false l pk (.node true a z b)) hT hd hk h2 true
        as ⟨s3, h3⟩
      try simp only [WP.spec_ok]
      refine ⟨⟨_, h3, Or.inl ?_⟩, hlt⟩
      show TRB.FixA _ gk f1.val
      rw [hf1']; exact TRB.fix_case1R hl hz hu hc hR hf
  · rename_i hb
    have hub : u.isRed = false := by rw [hb3] at hb; simpa using hb
    step with timer.left.rep s hpr as ⟨t1, ht1⟩
    replace ht1 : t1 = l.rootKey := ht1
    subst t1
    have zl : z ≠ l.rootKey := TRB.ne_rootL (ctx := .rc false u gk up) (c := true) (b := .node true a z b)
      (k := pk) hW (Or.inl (by simp [TRB.RBT.keys])) z0
    step with tcb_eq.iff as ⟨b4, hb4⟩
    have hb4f : ¬ b4 = true := fun e => zl (hb4.1 e)
    refine WP.spec_bind (Pₘ := fun x => C3R st T s0 c Ks up gk u n x.1 x.2.1 x.2.2) ?_ ?_
    · rw [if_neg hb4f]
      exact (WP.spec_ok _).2 ⟨a, b, l, h, hz, hl, hlb⟩
    · rintro ⟨s1, z1, pp⟩ hC
      exact fix_tailR hT hd hk hC hu hub hc hlt

/-- A round with a red parent on the right of `g`, `z` a left child (rotate at the parent first). -/
theorem fix_body_LR (s : S) (c f : U64) {s0 : S} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) {up : TRB.Ctx} {a b r u : TRB.RBT} {z pk gk : U64} {n : Nat}
    (h : FB st T s0 c Ks s (up.plug (.node false u gk (.node true (.node true a z b) pk r))))
    (hz : TRB.Bal (.node true a z b) n) (hr : TRB.Bal r n) (hrb : r.isRed = false) (hu : TRB.Bal u n)
    (hc : TRB.CtxOK up (n + 1)) (hR : TRB.RootB up) (hf : up.blk + 2 ≤ f.val) :
    timer.insert_fixup_loop.body st c s z f ⦃ r => FixPost st T s0 c Ks f r ⦄ := by
  have hW := h.nd hd
  have hzr : TRB.Rep (lk st s) pk z (.node true a z b) :=
    ((TRB.rep_plug (.lc true pk r (.rc false u gk up)) (.node true a z b)).1 h.rep).2
  have hpr : TRB.Rep (lk st s) gk pk (.node true (.node true a z b) pk r) :=
    ((TRB.rep_plug (.rc false u gk up) (.node true (.node true a z b) pk r)).1 h.rep).2
  have hgr : TRB.Rep (lk st s) up.par gk (.node false u gk (.node true (.node true a z b) pk r)) :=
    ((TRB.rep_plug up _).1 h.rep).2
  have hur : TRB.Rep (lk st s) gk u.rootKey u :=
    ((TRB.rep_plug (.lc false gk (.node true (.node true a z b) pk r) up) u).1 h.rep).2
  have z0 : z ≠ 0#u64 := TRB.Rep.keys_ne0 hzr z (by simp [TRB.RBT.keys])
  have pk0 : pk ≠ 0#u64 := TRB.Rep.keys_ne0 hpr pk (by simp [TRB.RBT.keys])
  have pu : pk ≠ u.rootKey := TRB.ne_rootL (ctx := up) (c := false) (a := u)
    (b := .node true (.node true a z b) pk r) (k := gk) hW (Or.inl (by simp [TRB.RBT.keys])) pk0
  unfold timer.insert_fixup_loop.body
  step with timer.parent.rep s hzr as ⟨p, hp⟩
  rw [if_neg z0] at hp
  subst p
  step with obj.Tcb.is_null.spec as ⟨bn, ebn⟩
  split
  · rename_i hb; exfalso; exact pk0 (by rw [ebn] at hb; exact of_decide_eq_true hb)
  step with timer.is_red.rep s hpr as ⟨b1, hb1⟩
  split
  swap
  · rename_i hb; exfalso; exact hb (by rw [hb1]; rfl)
  split
  · rename_i hf0; exfalso; have : f.val = 0 := by scalar_tac
    omega
  step as ⟨f1, hf1⟩
  have hf1' : f1.val = f.val - 1 := by clear * - hf1 hf; scalar_tac
  have hlt : f1.val < f.val := by omega
  step with timer.parent.rep s hpr as ⟨g, hg⟩
  rw [if_neg pk0] at hg
  subst g
  step with timer.left.rep s hgr as ⟨t, ht⟩
  replace ht : t = u.rootKey := ht
  subst t
  step with tcb_eq.iff as ⟨b2, hb2⟩
  split
  · rename_i hb; exfalso; exact pu (hb2.1 hb)
  step with timer.is_red.rep s hur as ⟨b3, hb3⟩
  split
  · rename_i hb
    cases u with
    | leaf => exfalso; rw [hb3] at hb; exact absurd hb (by simp [TRB.RBT.isRed])
    | node cu u1 uk u2 =>
      have hcu : cu = true := by rw [hb3] at hb; exact hb
      subst hcu
      simp only [TRB.RBT.rootKey]
      step with FB.set_red (.rc false (.node true u1 uk u2) gk up) true (.node true a z b) pk r hT hd hk h false
        as ⟨s1, h1⟩
      step with FB.set_red (.lc false gk (.node false (.node true a z b) pk r) up) true u1 uk u2 hT hd hk h1 false
        as ⟨s2, h2⟩
      step with FB.set_red up false (.node false u1 uk u2) gk (.node false (.node true a z b) pk r) hT hd hk h2 true
        as ⟨s3, h3⟩
      try simp only [WP.spec_ok]
      refine ⟨⟨_, h3, Or.inl ?_⟩, hlt⟩
      show TRB.FixA _ gk f1.val
      rw [hf1']; exact TRB.fix_case1R hz hr hu hc hR hf
  · rename_i hb
    have hub : u.isRed = false := by rw [hb3] at hb; simpa using hb
    step with timer.left.rep s hpr as ⟨t1, ht1⟩
    replace ht1 : t1 = z := ht1
    subst t1
    step with tcb_eq.iff as ⟨b4, hb4⟩
    have hb4t : b4 = true := hb4.2 trivial
    cases hz with
    | red ha hb' hab hbb =>
    refine WP.spec_bind (Pₘ := fun x => C3R st T s0 c Ks up gk u n x.1 x.2.1 x.2.2) ?_ ?_
    · rw [if_pos hb4t]
      step with FB.rotR (.rc false u gk up) true true a z b pk r hT hd hk h as ⟨s2, h2⟩
      have hn : TRB.Rep (lk st s2) z pk (.node true b pk r) :=
        ((TRB.rep_plug (.rc true a z (.rc false u gk up)) (.node true b pk r)).1 h2.rep).2
      step with timer.parent.rep s2 hn as ⟨pp1, hpp⟩
      rw [if_neg pk0] at hpp
      subst pp1
      try simp only [WP.spec_ok]
      exact ⟨b, r, a, h2, .red hb' hr hbb hrb, ha, hab⟩
    · rintro ⟨s1, z1, pp⟩ hC
      exact fix_tailR hT hd hk hC hu hub hc hlt

/-- **One round of `insert_fixup`'s loop keeps the invariant** (or exits with a balanced tree). -/
theorem fix_body (s : S) (c z f : U64) {s0 : S} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) (hx : FixInv st T s0 c Ks (s, z, f)) :
    timer.insert_fixup_loop.body st c s z f ⦃ r => FixPost st T s0 c Ks f r ⦄ := by
  obtain ⟨W, h, hm⟩ := hx
  rcases hm with ⟨ctx, a, b, n, rfl, hz, hc, hR, hf⟩ | ⟨ctx, cz, a, b, m, rfl, hpr, hb⟩
  · have hzr : TRB.Rep (lk st s) ctx.par z (.node true a z b) := ((TRB.rep_plug ctx _).1 h.rep).2
    have z0 : z ≠ 0#u64 := TRB.Rep.keys_ne0 hzr z (by simp [TRB.RBT.keys])
    cases ctx with
    | top => exact fix_body_exit s c z f h (m := n) hz hzr z0 (Or.inl rfl)
    | lc cp pk r up =>
      cases cp with
      | false =>
        exact fix_body_exit s c z f h (TRB.fixA_exit hz hc rfl) hzr z0
          (Or.inr ⟨_, _, ((TRB.rep_plug up (.node false (.node true a z b) pk r)).1 h.rep).2, rfl⟩)
      | true =>
        cases hc with
        | lcR hr hrb hup hcu =>
          have hne := hR.lc_red
          have hR1 := hR.lc_up
          cases up with
          | top => exact absurd rfl hne
          | lc cg gk u up2 =>
            cases cg with
            | true => simp [TRB.Ctx.parRed] at hup
            | false =>
              cases hcu with
              | lcB hu hcu2 =>
                exact fix_body_LL s c f hT hd hk h hz hr hrb hu hcu2 hR1.lc_up
                  (by simp only [TRB.Ctx.blk] at hf; omega)
          | rc cg u gk up2 =>
            cases cg with
            | true => simp [TRB.Ctx.parRed] at hup
            | false =>
              cases hcu with
              | rcB hu hcu2 =>
                exact fix_body_LR s c f hT hd hk h hz hr hrb hu hcu2 hR1.rc_up
                  (by simp only [TRB.Ctx.blk] at hf; omega)
    | rc cp l pk up =>
      cases cp with
      | false =>
        exact fix_body_exit s c z f h (TRB.fixA_exit hz hc rfl) hzr z0
          (Or.inr ⟨_, _, ((TRB.rep_plug up (.node false l pk (.node true a z b))).1 h.rep).2, rfl⟩)
      | true =>
        cases hc with
        | rcR hl hlb hup hcu =>
          have hne := hR.rc_red
          have hR1 := hR.rc_up
          cases up with
          | top => exact absurd rfl hne
          | lc cg gk u up2 =>
            cases cg with
            | true => simp [TRB.Ctx.parRed] at hup
            | false =>
              cases hcu with
              | lcB hu hcu2 =>
                exact fix_body_RL s c f hT hd hk h hz hl hlb hu hcu2 hR1.lc_up
                  (by simp only [TRB.Ctx.blk] at hf; omega)
          | rc cg u gk up2 =>
            cases cg with
            | true => simp [TRB.Ctx.parRed] at hup
            | false =>
              cases hcu with
              | rcB hu hcu2 =>
                exact fix_body_RR s c f hT hd hk h hz hl hlb hu hcu2 hR1.rc_up
                  (by simp only [TRB.Ctx.blk] at hf; omega)
  · have hzr : TRB.Rep (lk st s) ctx.par z (.node cz a z b) := ((TRB.rep_plug ctx _).1 h.rep).2
    have z0 : z ≠ 0#u64 := TRB.Rep.keys_ne0 hzr z (by simp [TRB.RBT.keys])
    cases ctx with
    | top => exact fix_body_exit s c z f h hb hzr z0 (Or.inl rfl)
    | lc cc k r up =>
      have e : cc = false := hpr
      subst e
      exact fix_body_exit s c z f h hb hzr z0
        (Or.inr ⟨_, _, ((TRB.rep_plug up (.node false (.node cz a z b) k r)).1 h.rep).2, rfl⟩)
    | rc cc l k up =>
      have e : cc = false := hpr
      subst e
      exact fix_body_exit s c z f h hb hzr z0
        (Or.inr ⟨_, _, ((TRB.rep_plug up (.node false l k (.node cz a z b))).1 h.rep).2, rfl⟩)

/-- **`insert_fixup`'s loop**: from the invariant, it ends with a balanced tree (the fuel never runs out). -/
theorem timer.insert_fixup_loop.rb (s : S) (c z f : U64) {s0 : S} {Ks : List U64} (hT : TcbPlaced T)
    (hd : Ks.Nodup) (hk : ∀ y ∈ Ks, y ∈ T) (h : FixInv st T s0 c Ks (s, z, f)) :
    timer.insert_fixup_loop st s c z f ⦃ s' => FixOut st T s0 c Ks s' ⦄ := by
  unfold timer.insert_fixup_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val) (inv := FixInv st T s0 c Ks)
  · rintro ⟨s1, z1, f1⟩ hx
    refine WP.spec_mono (fix_body s1 c z1 f1 hT hd hk hx) fun r hr => ?_
    cases r with
    | done y => exact hr
    | cont x' => exact hr
  · exact h

/-- **`timer::insert_fixup`** (stage 5): from `t` attached red at a leaf hole of a red-black tree (black
root), the result is a red-black tree with black root over the same keys, with writes only to links and
height words of those keys and the root word, core bits kept (`FB`). -/
theorem timer.insert_fixup.rb (s : S) (c t : U64) {ctx : TRB.Ctx} {m : Nat} (hT : TcbPlaced T)
    (hN : NodePlaced st T s c)
    (hrep : TRB.Rep (lk st s) 0#u64 (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT))
      (ctx.plug (.node true .leaf t .leaf)))
    (hb : TRB.Bal (ctx.plug .leaf) m) (hbl : (ctx.plug .leaf).isRed = false)
    (hd : (ctx.plug (.node true .leaf t .leaf)).keys.Nodup)
    (hk : ∀ y ∈ (ctx.plug (.node true .leaf t .leaf)).keys, y ∈ T) :
    timer.insert_fixup st s c t ⦃ s' => ∃ W n, FB st T s c (ctx.plug (.node true .leaf t .leaf)).keys s' W ∧
      TRB.Bal W n ∧ W.isRed = false ⦄ := by
  have h0 := FB.init (T := T) hN hrep
  obtain ⟨n, hl, hc, -⟩ := TRB.CtxOK.of_bal ctx hb
  cases hl
  have hblk := TRB.blk_le_64 hc (t := .node true .leaf t .leaf) (.red .leaf .leaf) hd
  have e128 : (128#u64 : U64).val = 128 := by simp
  have ht : t ∈ (ctx.plug (.node true .leaf t .leaf)).keys :=
    TRB.Ctx.keys_sub ctx _ t (by simp [TRB.RBT.keys])
  unfold timer.insert_fixup
  refine WP.spec_bind (timer.insert_fixup_loop.rb s c t 128#u64 hT hd hk
    ⟨_, h0, Or.inl ⟨ctx, .leaf, .leaf, 0, rfl, .red .leaf .leaf rfl rfl, hc, TRB.RootB.of_isRed hbl,
      by rw [e128]; omega⟩⟩) fun s1 hs1 => ?_
  obtain ⟨W, m1, h1, hb1⟩ := hs1
  cases W with
  | leaf =>
    exfalso
    rw [← h1.keys] at ht
    simp [TRB.RBT.keys] at ht
  | node cw lw kw rw =>
    step with timer.root.val (st := st) s1 c as ⟨r, hr⟩
    have er : r = kw := hr.trans h1.rep.root
    clear hr
    subst r
    refine WP.spec_mono (FB.set_red .top cw lw kw rw hT hd hk h1 false) fun s' h' => ?_
    obtain ⟨m', hm'⟩ := TRB.Bal.blacken hb1
    exact ⟨_, m', h', hm', rfl⟩

end

end Fl4ProofsA64.P1
