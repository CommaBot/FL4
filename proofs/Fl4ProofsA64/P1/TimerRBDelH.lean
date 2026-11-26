-- AArch64 port of Fl4Proofs.P1.TimerRBDelH (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d, TIMER-RB-PLAN stage 6, part 2): the structural part of `timer::remove` on the heap.
The extraction repeats `remove`'s splice/transplant code three times (once per `TIMER_MIN` branch); the
definitions `delClr`, `delOne`, `delTwoFin`, `delTwo`, `delTail` restate one copy and are definitionally
equal to each repetition.
- `splice_rep` (pure): removing a node with at most one child (the child takes its place).
- `delOne.spec`: one-child splice (`replace_child` + the child's parent word), then `remove_fixup`
  (spec as a hypothesis) when the removed colour is black, then the clearing of `t`'s words.
- `delTwo.spec`: two children: the leftmost walk finds `y` (`timer.remove_loop0.lm`), `y` is spliced
  out of its place (when it is not `t`'s right child) and transplanted into `t`'s place with `t`'s colour.
- `delTail.spec`: the three cases; the tree before the fixup is `ctxX.plug tx` with `x = tx.rootKey`,
  `x_parent = ctxX.par` and the removed colour `rr` (`DelShape`), the writes are links/height words of the
  old keys and the root word (`DelMid`).
-/
import Fl4ProofsA64.P1.TimerRBDel
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

/-- `remove`'s final clearing of `t`'s timer words. -/
def delClr {S : Type _} (st : machine.Store S) (s : S) (t : obj.Tcb) : Result S := do
  let s5 ← timer.set_parent st s t 0#u64
  let s6 ← timer.set_left st s5 t 0#u64
  let s7 ← timer.set_right st s6 t 0#u64
  let s8 ← obj.Tcb.set_timer_deadline st t s7 0#u64
  obj.Tcb.set_timer_height st t s8 0#u64

/-- `remove`, one-child case, from the parent read on. -/
def delOne {S : Type _} (st : machine.Store S) (s1 : S) (cpu : Std.U64) (t : obj.Tcb) (removed_red : Bool)
    (x : obj.Tcb) : Result S := do
  let x_parent ← timer.parent st s1 t
  let s2 ← timer.replace_child st s1 cpu x_parent t x
  let b2 ← obj.Tcb.is_null x
  let (s3, x_parent1) ←
    if b2
    then ok (s2, x_parent)
    else
      do
      let s4 ← timer.set_parent st s2 x x_parent
      ok (s4, x_parent)
  let s4 ←
    if removed_red
    then ok s3
    else timer.remove_fixup st s3 cpu x x_parent1
  delClr st s4 t

/-- `remove`, two-children case, from the transplant of `y` into `t`'s place on. -/
def delTwoFin {S : Type _} (st : machine.Store S) (s2 : S) (cpu : Std.U64) (t tl x1 x_parent y1 : obj.Tcb)
    (removed_red1 : Bool) : Result S := do
  let tp ← timer.parent st s2 t
  let s3 ← timer.replace_child st s2 cpu tp t y1
  let s4 ← timer.set_parent st s3 y1 tp
  let s5 ← timer.set_left st s4 y1 tl
  let s6 ← timer.set_parent st s5 tl y1
  let tred ← timer.is_red st s6 t
  let s7 ← timer.set_red st s6 y1 tred
  let s8 ←
    if removed_red1
    then ok s7
    else timer.remove_fixup st s7 cpu x1 x_parent
  delClr st s8 t

/-- `remove`, two-children case. -/
def delTwo {S : Type _} (st : machine.Store S) (s1 : S) (cpu : Std.U64) (t tl tr : obj.Tcb) : Result S := do
  let y ←
    timer.remove_loop0 st s1 tr layout.TREE_FUEL
  let removed_red1 ← timer.is_red st s1 y
  let x ← timer.right st s1 y
  let t1 ← timer.parent st s1 y
  let b3 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t1 t
  let (s2, x1, x_parent, y1) ←
    if b3
    then ok (s1, x, y, y)
    else
      do
      let s3 ← timer.set_left st s1 t1 x
      let b4 ← obj.Tcb.is_null x
      let (s4, x_parent1) ←
        if b4
        then ok (s3, t1)
        else
          do
          let s5 ← timer.set_parent st s3 x t1
          ok (s5, t1)
      let s5 ← timer.set_right st s4 y tr
      let s6 ← timer.set_parent st s5 tr y
      ok (s6, x, x_parent1, y)
  delTwoFin st s2 cpu t tl x1 x_parent y1 removed_red1

/-- `remove` after the `TIMER_MIN` update. -/
def delTail {S : Type _} (st : machine.Store S) (s1 : S) (cpu : Std.U64) (t : obj.Tcb) : Result S := do
  let removed_red ← timer.is_red st s1 t
  let tl ← timer.left st s1 t
  let tr ← timer.right st s1 t
  let b1 ← obj.Tcb.is_null tl
  if b1
  then
    let x ← if b1
              then ok tr
              else ok tl
    delOne st s1 cpu t removed_red x
  else
    let b2 ← obj.Tcb.is_null tr
    if b2
    then
      let x ← if b1
                then ok tr
                else ok tl
      delOne st s1 cpu t removed_red x
    else delTwo st s1 cpu t tl tr

namespace TRB

theorem Rep.root_ne0 {k : Links} {p x : U64} {t : RBT} (h : Rep k p x t) (ht : t ≠ .leaf) : x ≠ 0#u64 := by
  cases h with
  | leaf => exact absurd rfl ht
  | node h0 => exact h0

theorem Ctx.height_le : ∀ (ctx : Ctx) (t : RBT), t.height ≤ (ctx.plug t).height
  | .top, _ => le_refl _
  | .lc c k r up, t => by
    show t.height ≤ (up.plug (.node c t k r)).height
    exact (Nat.le_succ_of_le (le_max_left t.height r.height)).trans (Ctx.height_le up (.node c t k r))
  | .rc c l k up, t => by
    show t.height ≤ (up.plug (.node c l k t)).height
    exact (Nat.le_succ_of_le (le_max_right l.height t.height)).trans (Ctx.height_le up (.node c l k t))

theorem LSpine.keys_node {i : Ctx} (h : LSpine i) (c : Bool) (y : U64) (g : RBT) :
    (i.plug (.node c .leaf y g)).keys = y :: (i.plug g).keys := by
  rw [h.keys, h.keys]; simp [RBT.keys]

theorem plug_sub {ctx : Ctx} {t t' : RBT} (h : ∀ z ∈ t.keys, z ∈ t'.keys) :
    ∀ z ∈ (ctx.plug t).keys, z ∈ (ctx.plug t').keys := fun z hz => by
  rw [Ctx.plug_keys] at hz ⊢
  simp only [List.mem_append] at hz ⊢
  rcases hz with (hz | hz) | hz
  · exact Or.inl (Or.inl hz)
  · exact Or.inl (Or.inr (h z hz))
  · exact Or.inr hz

/-- **Splicing out a node with at most one child** (pure): the child `u` takes the node's place. -/
theorem splice_rep {K K' : Links} {R R' : U64} {ctx : Ctx} {c : Bool} {u0 u1 u : RBT} {y : U64}
    (h : Rep K 0#u64 R (ctx.plug (.node c u0 y u1))) (hd : (ctx.plug (.node c u0 y u1)).keys.Nodup)
    (hu : (u0 = .leaf ∧ u = u1) ∨ (u1 = .leaf ∧ u = u0))
    (ex : u.rootKey ≠ 0#u64 → K'.l u.rootKey = K.l u.rootKey ∧ K'.r u.rootKey = K.r u.rootKey ∧
      K'.p u.rootKey = ctx.par ∧ K'.red u.rootKey = K.red u.rootKey)
    (eo : ∀ z, z ≠ 0#u64 → z ≠ ctx.par → z ≠ u.rootKey → Same K K' z)
    (hh : HoleUpd K K' R R' ctx u.rootKey) : Rep K' 0#u64 R' (ctx.plug u) := by
  obtain ⟨mpar, m0, -, -, -, -, ht⟩ := mid_facts h hd
  obtain ⟨hc, -⟩ := (rep_plug ctx _).1 h
  have hk := Ctx.plug_keys ctx (.node c u0 y u1)
  have hd2 := hd
  rw [hk] at hd2
  have n0 := h.keys_ne0
  obtain ⟨-, -, hl, hr⟩ := Rep.node_inv ht
  have hn : (RBT.node c u0 y u1).keys.Nodup := nd_in hd2
  have uin : ∀ z ∈ u.keys, z ∈ (RBT.node c u0 y u1).keys := fun z hz => by
    rcases hu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [RBT.keys, hz]
  have hun : u.keys.Nodup := by
    rcases hu with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hn.sublist ((List.sublist_cons_self _ _).trans (List.sublist_append_right _ _))
    · exact hn.sublist (List.sublist_append_left _ _)
  have hu' : Rep K y u.rootKey u := by
    rcases hu with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · rw [← hr.root]; exact hr
    · rw [← hl.root]; exact hl
  refine plug_hole hc (nd_out hd2) (fun z hz hzp => eo z ?_ hzp ?_) hh rfl ?_
  · exact n0 z (by rw [hk]; simp only [List.mem_append] at hz ⊢; tauto)
  · intro e
    rcases u.rootKey_mem with e0 | m
    · exact n0 z (by rw [hk]; simp only [List.mem_append] at hz ⊢; tauto) (e.trans e0)
    · exact nd_mid hd2 (uin _ m) hz e.symm
  · exact hu'.reparent hun ex fun z hz hne => eo z (m0 z (uin z hz)) (mpar z (uin z hz)) hne

end TRB

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-- The words a splice/transplant writes: the links of the old keys (and of the null word), the root word. -/
def LinkFoot (st : machine.Store S) [L : LawfulStore st] (s0 : S) (c : U64) (Ks : List U64) (w : U64) : Prop :=
  (∃ z, (z = 0#u64 ∨ z ∈ Ks) ∧ (w = tlA z ∨ w = trA z ∨ w = tpA z)) ∨ w = L.nodeAt s0 c layout.node.TIMER_ROOT

theorem linkFoot_fix {s0 : S} {c : U64} {Ks : List U64} {w : U64} (h : LinkFoot st s0 c Ks w) :
    FixFoot st s0 c Ks w := by
  rcases h with ⟨z, hz, e | e | e⟩ | e
  · exact Or.inl ⟨z, hz, Or.inl e⟩
  · exact Or.inl ⟨z, hz, Or.inr (Or.inl e)⟩
  · exact Or.inl ⟨z, hz, Or.inr (Or.inr (Or.inl e))⟩
  · exact Or.inr e

theorem linkFoot_th {s0 : S} {c y : U64} {Ks : List U64} (hT : TcbPlaced T) (hN : NodePlaced st T s0 c)
    (hk : ∀ z ∈ Ks, z ∈ T) (hy : y ∈ T) : ¬ LinkFoot st s0 c Ks (thA y) := by
  rintro (⟨z, hz, e | e | e⟩ | e)
  · exact tz_ne hT (Tz.of_mem hy) (hz.imp_right (hk z)) (K1 := 3568#u64) (K2 := 3544#u64) (by simp) (by simp)
      (by simp) (congrArg UScalar.val e)
  · exact tz_ne hT (Tz.of_mem hy) (hz.imp_right (hk z)) (K1 := 3568#u64) (K2 := 3552#u64) (by simp) (by simp)
      (by simp) (congrArg UScalar.val e)
  · exact tz_ne hT (Tz.of_mem hy) (hz.imp_right (hk z)) (K1 := 3568#u64) (K2 := 3560#u64) (by simp) (by simp)
      (by simp) (congrArg UScalar.val e)
  · exact node_ne_tz hT hN (o := layout.node.TIMER_ROOT) (by rw [timer_root_val]; simp) (Tz.of_mem hy)
      (K := 3568#u64) (by simp) (congrArg UScalar.val e).symm

/-- The state right before `remove_fixup`: the heap is `W` from the root word, the writes since `s1` are
links/height words of the old keys `Ks` and the root word, core bits kept. -/
structure DelMid (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s1 : S) (c : U64) (Ks : List U64)
    (s : S) (W : TRB.RBT) : Prop where
  rep : TRB.Rep (lk st s) 0#u64 (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)) W
  wi : WritesIn st s1 s (FixFoot st s1 c Ks)
  core : ∀ y ∈ T, (L.mem s (thA y)).val >>> 8 = (L.mem s1 (thA y)).val >>> 8
  np : NodePlaced st T s c

/-- The state after `remove` clears `t`'s words. -/
def clrT (st : machine.Store S) [L : LawfulStore st] (s : S) (t : U64) : S :=
  L.wr (L.wr (L.wr (L.wr (L.wr s (tpA t) 0#u64) (tlA t) 0#u64) (trA t) 0#u64) (tdA t) 0#u64) (thA t) 0#u64

theorem delClr.on (s : S) (t : U64) (hT : TcbPlaced T) (ht : t ∈ T) :
    delClr st s t ⦃ s' => s' = clrT st s t ⦄ := by
  unfold delClr
  refine WP.spec_bind (timer.set_parent.on s t 0#u64 hT ht) fun s5 e5 => ?_
  subst e5
  refine WP.spec_bind (timer.set_left.on _ t 0#u64 hT ht) fun s6 e6 => ?_
  subst e6
  refine WP.spec_bind (timer.set_right.on _ t 0#u64 hT ht) fun s7 e7 => ?_
  subst e7
  refine WP.spec_bind (obj.Tcb.set_timer_deadline.wr _ t 0#u64) fun s8 e8 => ?_
  subst e8
  exact WP.spec_mono (obj.Tcb.set_timer_height.wr _ t 0#u64) fun s' e => e

theorem rr_tail {s3 : S} {rr : Bool} {Q : S → S → Prop} (c : U64) (x xp : U64)
    (hf : rr = false → timer.remove_fixup st s3 c x xp ⦃ s4 => Q s3 s4 ⦄) :
    (if rr then ok s3 else timer.remove_fixup st s3 c x xp) ⦃ s4 => (rr = true → s4 = s3) ∧ (rr = false → Q s3 s4) ⦄ := by
  cases rr
  · rw [if_neg (by simp)]
    exact WP.spec_mono (hf rfl) fun s4 h => ⟨fun e => absurd e (by simp), fun _ => h⟩
  · rw [if_pos rfl]
    exact (WP.spec_ok _).2 ⟨fun _ => rfl, fun e => absurd e (by simp)⟩

/-- **One-child splice** (`delOne`): the child `u` takes `t`'s place. -/
theorem delOne.spec (s1 : S) (c t : U64) {ctx : TRB.Ctx} {ct : Bool} {a b u : TRB.RBT} {Q : S → S → Prop}
    (hT : TcbPlaced T) (hN : NodePlaced st T s1 c)
    (h : TRB.Rep (lk st s1) 0#u64 (L.mem s1 (L.nodeAt s1 c layout.node.TIMER_ROOT)) (ctx.plug (.node ct a t b)))
    (hd : (ctx.plug (.node ct a t b)).keys.Nodup) (hk : ∀ z ∈ (ctx.plug (.node ct a t b)).keys, z ∈ T)
    (hu : (a = .leaf ∧ u = b) ∨ (b = .leaf ∧ u = a))
    (hfix : ∀ s3, DelMid st T s1 c (ctx.plug (.node ct a t b)).keys s3 (ctx.plug u) → ct = false →
      timer.remove_fixup st s3 c u.rootKey ctx.par ⦃ s4 => Q s3 s4 ⦄) :
    delOne st s1 c t ct u.rootKey ⦃ s' => ∃ s3 s4, DelMid st T s1 c (ctx.plug (.node ct a t b)).keys s3 (ctx.plug u) ∧
      (ct = true → s4 = s3) ∧ (ct = false → Q s3 s4) ∧ s' = clrT st s4 t ⦄ := by
  obtain ⟨mpar, m0, mpk, mp0, mk, mhl, ht⟩ := TRB.mid_facts h hd
  have tin : t ∈ (TRB.RBT.node ct a t b).keys := by simp [TRB.RBT.keys]
  have ht0 : t ≠ 0#u64 := m0 t tin
  have htT : t ∈ T := hk t (mk t tin)
  have uin : ∀ z ∈ u.keys, z ∈ (TRB.RBT.node ct a t b).keys := fun z hz => by
    rcases hu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [TRB.RBT.keys, hz]
  have hxK : u.rootKey ≠ 0#u64 → u.rootKey ∈ (ctx.plug (.node ct a t b)).keys := fun h0 =>
    mk _ (uin _ ((u.rootKey_mem).resolve_left h0))
  have hxT : u.rootKey ≠ 0#u64 → u.rootKey ∈ T := fun h0 => hk _ (hxK h0)
  have hxp : u.rootKey ≠ 0#u64 → u.rootKey ≠ ctx.par := fun h0 => mpar _ (uin _ ((u.rootKey_mem).resolve_left h0))
  have hpx : ctx ≠ .top → ctx.par ≠ u.rootKey := fun et e => by
    by_cases h0 : u.rootKey = 0#u64
    · exact mp0 et (e.trans h0)
    · exact hxp h0 e.symm
  have hpT : ctx ≠ .top → ctx.par ∈ T := fun e => hk _ (mpk e)
  have hpK : ctx.par = 0#u64 ∨ ctx.par ∈ (ctx.plug (.node ct a t b)).keys := by
    by_cases et : ctx = .top
    · subst et; exact Or.inl rfl
    · exact Or.inr (mpk et)
  have r0 := RW.init hN (LinkFoot st s1 c (ctx.plug (.node ct a t b)).keys)
  obtain ⟨hpt, -, -, -⟩ := TRB.Rep.node_inv ht
  unfold delOne
  step with timer.parent.links (st := st) s1 t as ⟨xp, exp⟩
  rw [if_neg ht0] at exp
  have exp' : xp = ctx.par := exp.trans hpt
  subst exp'
  refine WP.spec_bind (timer.replace_child.rw (y := u.rootKey) s1 c r0 hT hpT (mhl ht0)
    ⟨Or.inr rfl, Or.inl ⟨_, hpK, Or.inl rfl⟩, Or.inl ⟨_, hpK, Or.inr (Or.inl rfl)⟩⟩) fun s2 r2 => ?_
  step with obj.Tcb.is_null.spec as ⟨bx, ebx⟩
  refine WP.spec_bind (Pₘ := fun r : S × U64 => RW st T s1 r.1 c
      ((TRB.holeSet ctx u.rootKey (lk st s1)).setP u.rootKey ctx.par)
      (TRB.holeR ctx u.rootKey (L.mem s1 (L.nodeAt s1 c layout.node.TIMER_ROOT)))
      (LinkFoot st s1 c (ctx.plug (.node ct a t b)).keys) ∧ r.2 = ctx.par) ?_ ?_
  · split
    · rename_i hb
      have e0 : u.rootKey = 0#u64 := by rw [ebx] at hb; exact of_decide_eq_true hb
      exact (WP.spec_ok _).2 ⟨⟨r2.eq.setP_out (z := u.rootKey) (by rw [e0]; exact fun h0 => (hT _ h0).ne0 (by simp)) _,
        r2.root, r2.wi, r2.np⟩, rfl⟩
    · rename_i hb
      have hx0 : u.rootKey ≠ 0#u64 := fun e => hb (by rw [ebx, e]; rfl)
      refine WP.spec_bind (timer.set_parent.on _ u.rootKey ctx.par hT (hxT hx0)) fun s4 e => ?_
      subst e
      exact (WP.spec_ok _).2 ⟨r2.wr_tp hT (hxT hx0) (Or.inl ⟨_, Or.inr (hxK hx0), Or.inr (Or.inr rfl)⟩), rfl⟩
  rintro ⟨s3, xp1⟩ ⟨r3, e⟩
  simp only at r3 e
  subst e
  try simp only [WP.uncurry'_pair]
  have hh : TRB.HoleUpd (lk st s1) ((TRB.holeSet ctx u.rootKey (lk st s1)).setP u.rootKey ctx.par)
      (L.mem s1 (L.nodeAt s1 c layout.node.TIMER_ROOT))
      (TRB.holeR ctx u.rootKey (L.mem s1 (L.nodeAt s1 c layout.node.TIMER_ROOT))) ctx u.rootKey := by
    cases ctx with
    | top => rfl
    | lc cp p rp up =>
      have hp := hpx (by intro e; cases e)
      simp only [TRB.Ctx.par] at hp
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp [TRB.holeSet, Function.update_apply, hp]
    | rc cp lp p up =>
      have hp := hpx (by intro e; cases e)
      simp only [TRB.Ctx.par] at hp
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp [TRB.holeSet, Function.update_apply, hp]
  have hrep := TRB.splice_rep h hd hu (fun hx0 => by
      have := hxp hx0
      simp [Function.update_apply, TRB.holeSet_l_ne this, TRB.holeSet_r_ne this])
    (fun z h1 h2 h3 => by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Function.update_apply, h3, TRB.holeSet_l_ne h2, TRB.holeSet_r_ne h2]) hh
  have mid : DelMid st T s1 c (ctx.plug (.node ct a t b)).keys s3 (ctx.plug u) := by
    refine ⟨?_, r3.wi.mono fun w hw => linkFoot_fix hw, fun y hy => ?_, r3.np⟩
    · rw [r3.root]
      exact hrep.congr_on (fun z hz => hk z (TRB.plug_sub uin z hz)) r3.eq
    · exact congrArg (fun v : U64 => v.val >>> 8) (r3.wi.mem_eq (b := thA y)
        (tz_aligned hT (Tz.of_mem hy) (K := 3568#u64) (by simp) (by simp)) (linkFoot_th hT hN hk hy))
  refine WP.spec_bind (rr_tail c u.rootKey ctx.par (hfix s3 mid)) fun s4 h4 => ?_
  exact WP.spec_mono (delClr.on s4 t hT htT) fun s' e => ⟨s3, s4, mid, h4.1, h4.2, e⟩


namespace TRB

/-- **Transplant** (pure): `y`, no longer in `t`'s right subtree (now `B`, hanging at `y`'s right link in
`K2`, `P2`), takes `t`'s place: the hole re-pointed, `y`'s parent/left/colour set, `t`'s left child re-parented. -/
theorem transplant_rep {K K2 : Links} {R : U64} {ctx : Ctx} {ct : Bool} {a b B : RBT} {t y : U64}
    (h : Rep K 0#u64 R (ctx.plug (.node ct a t b))) (hd : (ctx.plug (.node ct a t b)).keys.Nodup)
    (hbk : b.keys = y :: B.keys) (ha : a ≠ .leaf)
    (P1 : ∀ z, z ≠ 0#u64 → z ∉ B.keys → z ≠ y → Same K K2 z) (P2 : Rep K2 y (K2.r y) B) :
    Rep (((((holeSet ctx y K2).setP y ctx.par).setL y a.rootKey).setP a.rootKey y).setRed y ct) 0#u64
      (holeR ctx y R) (ctx.plug (.node ct a y B)) := by
  obtain ⟨mpar, m0, mpk, mp0, mk, mhl, ht⟩ := mid_facts h hd
  have ht : Rep K ctx.par t (.node ct a t b) := ht
  obtain ⟨hpt, hct, hra, -⟩ := Rep.node_inv ht
  have etl : K.l t = a.rootKey := hra.root
  rw [etl] at hra
  have hd' := hd
  rw [Ctx.plug_keys] at hd'
  simp only [RBT.keys, hbk] at hd'
  have hM : (a.keys ++ t :: y :: B.keys).Nodup := nd_in hd'
  have out : ∀ z ∈ a.keys ++ t :: y :: B.keys, ∀ w ∈ ctx.pre ++ ctx.post, z ≠ w :=
    fun z hz w hw => nd_mid hd' hz hw
  have hM1 : (t :: y :: B.keys).Nodup := hM.sublist (List.sublist_append_right _ _)
  have hty : t ≠ y := fun e => (List.nodup_cons.1 hM1).1 (by simp [e])
  have htB : t ∉ B.keys := fun m => (List.nodup_cons.1 hM1).1 (by simp [m])
  have hyB : y ∉ B.keys := (List.nodup_cons.1 (List.nodup_cons.1 hM1).2).1
  have haM : ∀ z ∈ a.keys, ∀ w ∈ t :: y :: B.keys, z ≠ w := fun z hz w hw => nd_sep hM hz hw
  have inN : ∀ z ∈ a.keys ++ t :: y :: B.keys, z ∈ (RBT.node ct a t b).keys := fun z hz => by
    simp only [RBT.keys, hbk]; exact hz
  have tin : t ∈ a.keys ++ t :: y :: B.keys := by simp
  have yin : y ∈ a.keys ++ t :: y :: B.keys := by simp
  have ht0 : t ≠ 0#u64 := m0 t (inN t tin)
  have hy0 : y ≠ 0#u64 := m0 y (inN y yin)
  have hyp : y ≠ ctx.par := mpar y (inN y yin)
  have tlm : a.rootKey ∈ a.keys := (a.rootKey_mem).resolve_left (hra.root_ne0 ha)
  have tlin : a.rootKey ∈ a.keys ++ t :: y :: B.keys := List.mem_append_left _ tlm
  have htl0 : a.rootKey ≠ 0#u64 := m0 _ (inN _ tlin)
  have htlp : a.rootKey ≠ ctx.par := mpar _ (inN _ tlin)
  have hytl : y ≠ a.rootKey := fun e => haM _ tlm y (by simp) e.symm
  have htlB : a.rootKey ∉ B.keys := fun m => haM _ tlm _ (by simp [m]) rfl
  have parS : ctx ≠ .top → Same K K2 ctx.par := fun et =>
    P1 _ (mp0 et) (fun m => mpar _ (inN _ (by simp [m])) rfl) (fun e => hyp e.symm)
  have hc := ((rep_plug ctx _).1 h).1
  have he : ∀ z ∈ ctx.pre ++ ctx.post, z ≠ ctx.par → Same K
      (((((holeSet ctx y K2).setP y ctx.par).setL y a.rootKey).setP a.rootKey y).setRed y ct) z := by
    intro z hz hzp
    have hzy : z ≠ y := (out y yin z hz).symm
    have hztl : z ≠ a.rootKey := (out _ tlin z hz).symm
    have hzB : z ∉ B.keys := fun m => out z (by simp [m]) z hz rfl
    have hz0 : z ≠ 0#u64 := by
      have := h.keys_ne0 z
      rw [Ctx.plug_keys] at this
      exact this (by simp only [List.mem_append] at hz ⊢; tauto)
    have hS := P1 z hz0 hzB hzy
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [Function.update_apply, hzy, hztl, holeSet_l_ne hzp, holeSet_r_ne hzp, hS.1, hS.2.1, hS.2.2.1,
        hS.2.2.2]
  have hu : HoleUpd K
      (((((holeSet ctx y K2).setP y ctx.par).setL y a.rootKey).setP a.rootKey y).setRed y ct)
      R
      (holeR ctx y R) ctx y := by
    have parY : ctx ≠ .top → ctx.par ≠ y := fun _ e => hyp e.symm
    have parTl : ctx.par ≠ a.rootKey := fun e => htlp e.symm
    cases ctx with
    | top => rfl
    | lc cp p rp up =>
      have hS := parS (by intro e; cases e)
      have h1 := parY (by intro e; cases e)
      simp only [Ctx.par] at hS h1 parTl
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
        simp [holeSet, Function.update_apply, h1, parTl, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2]
    | rc cp lp p up =>
      have hS := parS (by intro e; cases e)
      have h1 := parY (by intro e; cases e)
      simp only [Ctx.par] at hS h1 parTl
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
        simp [holeSet, Function.update_apply, h1, parTl, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2]
  have hA : Rep (((((holeSet ctx y K2).setP y ctx.par).setL y a.rootKey).setP a.rootKey y).setRed y ct)
      y a.rootKey a := by
    have hS := P1 _ htl0 htlB (fun e => hytl e.symm)
    refine hra.reparent (hM.sublist (List.sublist_append_left _ _)) (fun _ => ?_) (fun z hz hne => ?_)
    · simp [Function.update_apply, hytl.symm, holeSet_l_ne htlp, holeSet_r_ne htlp, hS.1, hS.2.1, hS.2.2.2]
    · have hzy : z ≠ y := haM z hz y (by simp)
      have hzp : z ≠ ctx.par := mpar z (inN z (List.mem_append_left _ hz))
      have hz0 : z ≠ 0#u64 := m0 z (inN z (List.mem_append_left _ hz))
      have hzB : z ∉ B.keys := fun m => haM z hz z (by simp [m]) rfl
      have hS' := P1 z hz0 hzB hzy
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp [Function.update_apply, hzy, hne, holeSet_l_ne hzp, holeSet_r_ne hzp, hS'.1, hS'.2.1,
          hS'.2.2.1, hS'.2.2.2]
  have hB : Rep (((((holeSet ctx y K2).setP y ctx.par).setL y a.rootKey).setP a.rootKey y).setRed y ct)
      y ((((((holeSet ctx y K2).setP y ctx.par).setL y a.rootKey).setP a.rootKey y).setRed y ct).r y) B := by
    have er : ((((((holeSet ctx y K2).setP y ctx.par).setL y a.rootKey).setP a.rootKey y).setRed y ct).r y) =
        K2.r y := by simp [holeSet_r_ne hyp]
    rw [er]
    refine P2.congr fun z hz => ?_
    have hzy : z ≠ y := fun e => hyB (e ▸ hz)
    have hzp : z ≠ ctx.par := mpar z (inN z (by simp [hz]))
    have hztl : z ≠ a.rootKey := fun e => htlB (e ▸ hz)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Function.update_apply, hzy, hztl, holeSet_l_ne hzp, holeSet_r_ne hzp]
  have hnode : Rep (((((holeSet ctx y K2).setP y ctx.par).setL y a.rootKey).setP a.rootKey y).setRed y ct)
      ctx.par y (.node ct a y B) := by
    refine .node hy0 (by simp [Function.update_apply, hytl]) (by simp) ?_ hB
    rw [show ((((((holeSet ctx y K2).setP y ctx.par).setL y a.rootKey).setP a.rootKey y).setRed y ct).l y) =
      a.rootKey by simp]
    exact hA
  have hrep := plug_hole hc (nd_out hd') he hu rfl hnode
  exact hrep

end TRB

/-- **Two children, the transplant** (`delTwoFin`): `y` (already spliced out of `t`'s right subtree, which
is now `B` hanging at `y`'s right link, `P2`) takes `t`'s place and colour. -/
theorem delTwoFin.spec (s2 : S) (c t : U64) {s1 : S} {ctx : TRB.Ctx} {ct cy : Bool} {a b B : TRB.RBT}
    {y x1 xp : U64} {K2 : TRB.Links} {Q : S → S → Prop} (hT : TcbPlaced T) (hN : NodePlaced st T s1 c)
    (h : TRB.Rep (lk st s1) 0#u64 (L.mem s1 (L.nodeAt s1 c layout.node.TIMER_ROOT)) (ctx.plug (.node ct a t b)))
    (hd : (ctx.plug (.node ct a t b)).keys.Nodup) (hk : ∀ z ∈ (ctx.plug (.node ct a t b)).keys, z ∈ T)
    (hbk : b.keys = y :: B.keys) (ha : a ≠ .leaf)
    (r2 : RW st T s1 s2 c K2 (L.mem s1 (L.nodeAt s1 c layout.node.TIMER_ROOT))
      (LinkFoot st s1 c (ctx.plug (.node ct a t b)).keys))
    (P1 : ∀ z, z ≠ 0#u64 → z ∉ B.keys → z ≠ y → TRB.Same (lk st s1) K2 z)
    (P2 : TRB.Rep K2 y (K2.r y) B)
    (hfix : ∀ s7, DelMid st T s1 c (ctx.plug (.node ct a t b)).keys s7 (ctx.plug (.node ct a y B)) → cy = false →
      timer.remove_fixup st s7 c x1 xp ⦃ s8 => Q s7 s8 ⦄) :
    delTwoFin st s2 c t a.rootKey x1 xp y cy ⦃ s' => ∃ s7 s8,
      DelMid st T s1 c (ctx.plug (.node ct a t b)).keys s7 (ctx.plug (.node ct a y B)) ∧
      (cy = true → s8 = s7) ∧ (cy = false → Q s7 s8) ∧ s' = clrT st s8 t ⦄ := by
  obtain ⟨mpar, m0, mpk, mp0, mk, mhl, ht⟩ := TRB.mid_facts h hd
  have ht : TRB.Rep (lk st s1) ctx.par t (.node ct a t b) := ht
  obtain ⟨hpt, hct, hra, -⟩ := TRB.Rep.node_inv ht
  have etl : (lk st s1).l t = a.rootKey := hra.root
  rw [etl] at hra
  have hd' := hd
  rw [TRB.Ctx.plug_keys] at hd'
  simp only [TRB.RBT.keys, hbk] at hd'
  have hM : (a.keys ++ t :: y :: B.keys).Nodup := TRB.nd_in hd'
  have out : ∀ z ∈ a.keys ++ t :: y :: B.keys, ∀ w ∈ ctx.pre ++ ctx.post, z ≠ w :=
    fun z hz w hw => TRB.nd_mid hd' hz hw
  have hM1 : (t :: y :: B.keys).Nodup := hM.sublist (List.sublist_append_right _ _)
  have hty : t ≠ y := fun e => (List.nodup_cons.1 hM1).1 (by simp [e])
  have htB : t ∉ B.keys := fun m => (List.nodup_cons.1 hM1).1 (by simp [m])
  have hyB : y ∉ B.keys := (List.nodup_cons.1 (List.nodup_cons.1 hM1).2).1
  have haM : ∀ z ∈ a.keys, ∀ w ∈ t :: y :: B.keys, z ≠ w := fun z hz w hw => TRB.nd_sep hM hz hw
  have inN : ∀ z ∈ a.keys ++ t :: y :: B.keys, z ∈ (TRB.RBT.node ct a t b).keys := fun z hz => by
    simp only [TRB.RBT.keys, hbk]; exact hz
  have tin : t ∈ a.keys ++ t :: y :: B.keys := by simp
  have yin : y ∈ a.keys ++ t :: y :: B.keys := by simp
  have ht0 : t ≠ 0#u64 := m0 t (inN t tin)
  have htT : t ∈ T := hk t (mk t (inN t tin))
  have hy0 : y ≠ 0#u64 := m0 y (inN y yin)
  have hyT : y ∈ T := hk y (mk y (inN y yin))
  have hyp : y ≠ ctx.par := mpar y (inN y yin)
  have tlm : a.rootKey ∈ a.keys := (a.rootKey_mem).resolve_left (hra.root_ne0 ha)
  have tlin : a.rootKey ∈ a.keys ++ t :: y :: B.keys := List.mem_append_left _ tlm
  have htl0 : a.rootKey ≠ 0#u64 := m0 _ (inN _ tlin)
  have htlT : a.rootKey ∈ T := hk _ (mk _ (inN _ tlin))
  have htlp : a.rootKey ≠ ctx.par := mpar _ (inN _ tlin)
  have hytl : y ≠ a.rootKey := fun e => haM _ tlm y (by simp) e.symm
  have htlB : a.rootKey ∉ B.keys := fun m => haM _ tlm _ (by simp [m]) rfl
  have yK : y ∈ (ctx.plug (.node ct a t b)).keys := mk y (inN y yin)
  have tlK : a.rootKey ∈ (ctx.plug (.node ct a t b)).keys := mk _ (inN _ tlin)
  have hpT : ctx ≠ .top → ctx.par ∈ T := fun e => hk _ (mpk e)
  have hpK : ctx.par = 0#u64 ∨ ctx.par ∈ (ctx.plug (.node ct a t b)).keys := by
    by_cases et : ctx = .top
    · subst et; exact Or.inl rfl
    · exact Or.inr (mpk et)
  have parS : ctx ≠ .top → TRB.Same (lk st s1) K2 ctx.par := fun et =>
    P1 _ (mp0 et) (fun m => mpar _ (inN _ (by simp [m])) rfl) (fun e => hyp e.symm)
  have hl : TRB.HoleL K2 t ctx := by
    by_cases et : ctx = .top
    · subst et; trivial
    · exact (mhl ht0).congr (parS et).1
  have Pt := P1 t ht0 htB hty
  have fy : ∀ w, (w = tlA y ∨ w = trA y ∨ w = tpA y) → LinkFoot st s1 c (ctx.plug (.node ct a t b)).keys w :=
    fun w hw => Or.inl ⟨y, Or.inr yK, hw⟩
  unfold delTwoFin
  step with timer.parent.links (st := st) s2 t as ⟨tp, etp⟩
  rw [if_neg ht0, (r2.eq t htT).2.2.1, Pt.2.2.1, hpt] at etp
  subst etp
  refine WP.spec_bind (timer.replace_child.rw (y := y) s2 c r2 hT hpT hl
    ⟨Or.inr rfl, Or.inl ⟨_, hpK, Or.inl rfl⟩, Or.inl ⟨_, hpK, Or.inr (Or.inl rfl)⟩⟩) fun s3 r3 => ?_
  refine WP.spec_bind (timer.set_parent.on s3 y ctx.par hT hyT) fun s4 e => ?_
  subst e
  have r4 := r3.wr_tp (v := ctx.par) hT hyT (fy _ (Or.inr (Or.inr rfl)))
  refine WP.spec_bind (timer.set_left.on _ y a.rootKey hT hyT) fun s5 e => ?_
  subst e
  have r5 := r4.wr_tl (v := a.rootKey) hT hyT (fy _ (Or.inl rfl))
  refine WP.spec_bind (timer.set_parent.on _ a.rootKey y hT htlT) fun s6 e => ?_
  have r6 := r5.wr_tp (v := y) hT htlT (Or.inl ⟨_, Or.inr tlK, Or.inr (Or.inr rfl)⟩)
  rw [← e] at r6
  step with timer.is_red.links (st := st) _ t as ⟨tred, etred⟩
  rw [if_neg ht0, (r6.eq t htT).2.2.2] at etred
  have etred' : tred = ct := by
    rw [etred]
    simp only [TRB.Links.setP_red, TRB.Links.setL_red, TRB.holeSet_red]
    rw [Pt.2.2.2, hct]
  clear etred
  subst tred
  refine WP.spec_bind (timer.set_red.on _ y ct hT hyT) fun s7 e7 => ?_
  -- the tree before the fixup
  have hrep := TRB.transplant_rep h hd hbk ha P1 P2
  have sub : ∀ w ∈ (TRB.RBT.node ct a y B).keys, w ∈ (TRB.RBT.node ct a t b).keys := by
    intro w hw
    apply inN w
    simp only [TRB.RBT.keys, List.mem_append, List.mem_cons] at hw ⊢
    rcases hw with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))
  have kin : ∀ z ∈ (ctx.plug (.node ct a y B)).keys, z ∈ T := fun z hz => hk z (TRB.plug_sub sub z hz)
  have hthy : (L.mem s6 (thA y)) = L.mem s1 (thA y) := by
    have ha8 : Aligned (thA y) := tz_aligned hT (Tz.of_mem hyT) (K := 3568#u64) (by simp) (by simp)
    exact r6.wi.mem_eq ha8 (linkFoot_th hT hN hk hyT)
  have mid : DelMid st T s1 c (ctx.plug (.node ct a t b)).keys s7 (ctx.plug (.node ct a y B)) := by
    refine ⟨?_, ?_, fun z hz => ?_, by rw [e7]; exact r6.np.wr⟩
    · have er7 : L.mem s7 (L.nodeAt s7 c layout.node.TIMER_ROOT) =
          TRB.holeR ctx y (L.mem s1 (L.nodeAt s1 c layout.node.TIMER_ROOT)) := by
        rw [e7]; exact (root_wr_fld (K := 3568#u64) hT r6.np hyT (by simp) (by simp)).trans r6.root
      rw [er7]
      exact hrep.congr_on kin (by rw [e7]; exact (r6.eq.setRed y ct).trans (lk_wr_red ct hT hyT))
    · rw [e7]
      exact (r6.wi.trans (writesIn_wr (a := thA y)
        (tz_aligned hT (Tz.of_mem hyT) (K := 3568#u64) (by simp) (by simp)))).mono fun w hw =>
          hw.elim linkFoot_fix fun e => Or.inl ⟨y, Or.inr yK, Or.inr (Or.inr (Or.inr e))⟩
    · by_cases ez : z = y
      · subst ez
        have e1 : L.mem s7 (thA z) = (L.mem s6 (thA z) &&& ~~~1#u64) ||| redW ct := by
          rw [e7]; exact L.mem_wr_same (tz_aligned hT (Tz.of_mem hyT) (K := 3568#u64) (by simp) (by simp))
        rw [e1, core_wr_red, hthy]
      · rw [e7, th_keep hT hyT hz ez]
        exact congrArg (fun v : U64 => v.val >>> 8) (r6.wi.mem_eq (b := thA z)
          (tz_aligned hT (Tz.of_mem hz) (K := 3568#u64) (by simp) (by simp)) (linkFoot_th hT hN hk hz))
  refine WP.spec_bind (rr_tail c x1 xp (hfix s7 mid)) fun s8 h8 => ?_
  exact WP.spec_mono (delClr.on s8 t hT htT) fun s' e => ⟨s7, s8, mid, h8.1, h8.2, e⟩


/-- **Two children** (`delTwo`): `y` = the leftmost node of `t`'s right subtree `b`
(`b = ctx2.plug (node cy leaf y g)`) is spliced out (its right subtree `g` takes its place) and put in
`t`'s place with `t`'s colour. -/
theorem delTwo.spec (s1 : S) (c t : U64) {ctx : TRB.Ctx} {ct : Bool} {a b : TRB.RBT} {Q : S → S → Prop}
    (hT : TcbPlaced T) (hN : NodePlaced st T s1 c)
    (h : TRB.Rep (lk st s1) 0#u64 (L.mem s1 (L.nodeAt s1 c layout.node.TIMER_ROOT)) (ctx.plug (.node ct a t b)))
    (hd : (ctx.plug (.node ct a t b)).keys.Nodup) (hk : ∀ z ∈ (ctx.plug (.node ct a t b)).keys, z ∈ T)
    (ha : a ≠ .leaf) (hb : b ≠ .leaf) (hh : (ctx.plug (.node ct a t b)).height ≤ 128)
    (hfix : ∀ ctx2 cy y g, TRB.LSpine ctx2 → b = ctx2.plug (.node cy .leaf y g) → ∀ s7,
      DelMid st T s1 c (ctx.plug (.node ct a t b)).keys s7 (ctx.plug (.node ct a y (ctx2.plug g))) → cy = false →
      timer.remove_fixup st s7 c g.rootKey (TRB.Ctx.app ctx2 (.rc ct a y ctx)).par ⦃ s8 => Q s7 s8 ⦄) :
    delTwo st s1 c t a.rootKey b.rootKey ⦃ s' => ∃ ctx2 cy y g, TRB.LSpine ctx2 ∧
      b = ctx2.plug (.node cy .leaf y g) ∧ ∃ s7 s8,
      DelMid st T s1 c (ctx.plug (.node ct a t b)).keys s7 (ctx.plug (.node ct a y (ctx2.plug g))) ∧
      (cy = true → s8 = s7) ∧ (cy = false → Q s7 s8) ∧ s' = clrT st s8 t ⦄ := by
  obtain ⟨mpar, m0, mpk, mp0, mk, mhl, ht⟩ := TRB.mid_facts h hd
  have ht : TRB.Rep (lk st s1) ctx.par t (.node ct a t b) := ht
  obtain ⟨hpt, hct, hra, hrb⟩ := TRB.Rep.node_inv ht
  have etr : (lk st s1).r t = b.rootKey := hrb.root
  rw [etr] at hrb
  have htr0 : b.rootKey ≠ 0#u64 := hrb.root_ne0 hb
  have hbh : b.height ≤ layout.TREE_FUEL.val + 1 := by
    have h1 := TRB.Ctx.height_le ctx (.node ct a t b)
    have h2 : b.height + 1 ≤ (TRB.RBT.node ct a t b).height := Nat.succ_le_succ (le_max_right _ _)
    rw [layout.TREE_FUEL.val_eq]; omega
  have hn : (TRB.RBT.node ct a t b).keys.Nodup := by
    have := hd; rw [TRB.Ctx.plug_keys] at this; exact TRB.nd_in this
  have hbn : b.keys.Nodup := hn.sublist ((List.sublist_cons_self _ _).trans (List.sublist_append_right _ _))
  have htb : t ∉ b.keys := (List.nodup_cons.1 (hn.sublist (List.sublist_append_right _ _))).1
  have bin : ∀ z ∈ b.keys, z ∈ (ctx.plug (.node ct a t b)).keys := fun z hz => mk z (by simp [TRB.RBT.keys, hz])
  unfold delTwo
  refine WP.spec_bind (timer.remove_loop0.lm s1 layout.TREE_FUEL hrb htr0 hbh) ?_
  rintro y ⟨ctx2, cy, g, hL, eb⟩
  have hbk : b.keys = y :: (ctx2.plug g).keys := by rw [eb]; exact hL.keys_node cy y g
  have inW : ∀ z ∈ ((TRB.Ctx.app ctx2 (.rc ct a t ctx)).plug (.node cy .leaf y g)).keys,
      z ∈ (ctx.plug (.node ct a t b)).keys := fun z hz => by
    rw [TRB.Ctx.plug_app, ← eb] at hz; exact hz
  have hW : TRB.Rep (lk st s1) 0#u64 (L.mem s1 (L.nodeAt s1 c layout.node.TIMER_ROOT))
      ((TRB.Ctx.app ctx2 (.rc ct a t ctx)).plug (.node cy .leaf y g)) := by
    rw [TRB.Ctx.plug_app, ← eb]; exact h
  have hdW : ((TRB.Ctx.app ctx2 (.rc ct a t ctx)).plug (.node cy .leaf y g)).keys.Nodup := by
    rw [TRB.Ctx.plug_app, ← eb]; exact hd
  obtain ⟨mparB, m0B, mpkB, mp0B, mkB, -, htB⟩ := TRB.mid_facts hW hdW
  have htB : TRB.Rep (lk st s1) (TRB.Ctx.app ctx2 (.rc ct a t ctx)).par y (.node cy .leaf y g) := htB
  obtain ⟨-, -, -, hry⟩ := TRB.Rep.node_inv htB
  have yin : y ∈ (TRB.RBT.node cy .leaf y g).keys := by simp [TRB.RBT.keys]
  have hy0 : y ≠ 0#u64 := m0B y yin
  have yK : y ∈ (ctx.plug (.node ct a t b)).keys := inW y (mkB y yin)
  have hyT : y ∈ T := hk y yK
  have hBn : (ctx2.plug g).keys.Nodup := by have := hbn; rw [hbk] at this; exact (List.nodup_cons.1 this).2
  have hyB : y ∉ (ctx2.plug g).keys := by have := hbn; rw [hbk] at this; exact (List.nodup_cons.1 this).1
  step with timer.is_red.rep (st := st) s1 htB as ⟨rr, err⟩
  step with timer.right.rep (st := st) s1 htB as ⟨x, ex⟩
  step with timer.parent.rep (st := st) s1 htB as ⟨t1, et1⟩
  rw [if_neg hy0] at et1
  step with tcb_eq.blk t1 t as ⟨b3, eb3⟩
  have err' : rr = cy := err
  have ex' : x = g.rootKey := ex
  clear err ex
  subst rr x t1
  refine WP.spec_bind (Pₘ := fun r : S × U64 × U64 × U64 => r.2.2.2 = y ∧
      r.2.2.1 = (TRB.Ctx.app ctx2 (.rc ct a y ctx)).par ∧ r.2.1 = g.rootKey ∧
      ∃ K2, RW st T s1 r.1 c K2 (L.mem s1 (L.nodeAt s1 c layout.node.TIMER_ROOT))
        (LinkFoot st s1 c (ctx.plug (.node ct a t b)).keys) ∧
        (∀ z, z ≠ 0#u64 → z ∉ (ctx2.plug g).keys → z ≠ y → TRB.Same (lk st s1) K2 z) ∧
        TRB.Rep K2 y (K2.r y) (ctx2.plug g)) ?_ ?_
  · cases ctx2 with
    | top =>
      have e3 : b3 = true := by rw [eb3]; exact decide_eq_true rfl
      rw [if_pos e3]
      exact (WP.spec_ok _).2 ⟨rfl, rfl, rfl, lk st s1, RW.init hN _, fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩, hry⟩
    | rc _ _ _ _ => exact (hL : False).elim
    | lc cq q rq up =>
      have hqY : ∀ z ∈ (TRB.RBT.node cy .leaf y g).keys, z ≠ q := mparB
      have hq0 : q ≠ 0#u64 := mp0B (by intro e; cases e)
      have qK : q ∈ (ctx.plug (.node ct a t b)).keys := inW q (mpkB (by intro e; cases e))
      have hqT : q ∈ T := hk q qK
      have hqB : q ∈ (TRB.Ctx.plug (.lc cq q rq up) g).keys := TRB.Ctx.keys_sub up _ q (by simp [TRB.RBT.keys])
      have hqt : q ≠ t := fun e => htb (by rw [hbk, ← e]; exact List.mem_cons_of_mem _ hqB)
      have gY : ∀ z ∈ g.keys, z ∈ (TRB.RBT.node cy .leaf y g).keys := fun z hz => by simp [TRB.RBT.keys, hz]
      have gB : ∀ z ∈ g.keys, z ∈ (TRB.Ctx.plug (.lc cq q rq up) g).keys := TRB.Ctx.keys_sub _ g
      have hxq : g.rootKey ≠ q := fun e => by
        rcases g.rootKey_mem with e0 | m
        · exact hq0 (e.symm.trans e0)
        · exact hqY _ (gY _ m) e
      have hxK : g.rootKey ≠ 0#u64 → g.rootKey ∈ (ctx.plug (.node ct a t b)).keys := fun h0 =>
        inW _ (mkB _ (gY _ ((g.rootKey_mem).resolve_left h0)))
      have e3 : b3 = false := by rw [eb3]; exact decide_eq_false hqt
      rw [if_neg (by rw [e3]; simp)]
      refine WP.spec_bind (timer.set_left.on s1 q g.rootKey hT hqT) fun s3 e => ?_
      subst e
      have r1 := (RW.init hN (LinkFoot st s1 c (ctx.plug (.node ct a t b)).keys)).wr_tl (v := g.rootKey) hT hqT
        (Or.inl ⟨q, Or.inr qK, Or.inl rfl⟩)
      step with obj.Tcb.is_null.spec as ⟨b4, eb4⟩
      refine WP.spec_bind (Pₘ := fun r : S × U64 => RW st T s1 r.1 c
          (((lk st s1).setL q g.rootKey).setP g.rootKey q) (L.mem s1 (L.nodeAt s1 c layout.node.TIMER_ROOT))
          (LinkFoot st s1 c (ctx.plug (.node ct a t b)).keys) ∧ r.2 = q) ?_ ?_
      · split
        · rename_i hb4
          have e0 : g.rootKey = 0#u64 := by rw [eb4] at hb4; exact of_decide_eq_true hb4
          exact (WP.spec_ok _).2 ⟨⟨r1.eq.setP_out (z := g.rootKey)
            (by rw [e0]; exact fun h0 => (hT _ h0).ne0 (by simp)) _, r1.root, r1.wi, r1.np⟩, rfl⟩
        · rename_i hb4
          have hx0 : g.rootKey ≠ 0#u64 := fun e => hb4 (by rw [eb4, e]; rfl)
          refine WP.spec_bind (timer.set_parent.on _ g.rootKey q hT (hk _ (hxK hx0))) fun s4 e => ?_
          subst e
          exact (WP.spec_ok _).2 ⟨r1.wr_tp hT (hk _ (hxK hx0)) (Or.inl ⟨_, Or.inr (hxK hx0), Or.inr (Or.inr rfl)⟩), rfl⟩
      rintro ⟨s4, xq⟩ ⟨r4, e⟩
      simp only at r4 e
      subst xq
      try simp only [WP.uncurry'_pair]
      -- `y` spliced out: the subtree at `t`'s right is now `B = ctx2.plug g`
      have hs := TRB.splice_rep (K' := ((lk st s1).setL q g.rootKey).setP g.rootKey q) hW hdW
        (Or.inl ⟨rfl, rfl⟩)
        (fun hx0 => by simp [Function.update_apply, hxq, TRB.Ctx.app, TRB.Ctx.par])
        (fun z h1 h2 h3 => by
          simp only [TRB.Ctx.app, TRB.Ctx.par] at h2
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Function.update_apply, h2, h3])
        (by refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp [Function.update_apply, hxq.symm])
      rw [TRB.Ctx.plug_app] at hs
      obtain ⟨-, hnK⟩ := (TRB.rep_plug ctx (.node ct a t (TRB.Ctx.plug (.lc cq q rq up) g))).1 hs
      have hnK : TRB.Rep (((lk st s1).setL q g.rootKey).setP g.rootKey q) ctx.par t
          (.node ct a t (TRB.Ctx.plug (.lc cq q rq up) g)) := hnK
      obtain ⟨-, -, -, hBK⟩ := TRB.Rep.node_inv hnK
      have eK1r : (((lk st s1).setL q g.rootKey).setP g.rootKey q).r t = b.rootKey := by simp; exact etr
      rw [eK1r] at hBK
      have trB : b.rootKey ∈ (TRB.Ctx.plug (.lc cq q rq up) g).keys := (hBK.root_mem).resolve_left htr0
      have trK : b.rootKey ∈ (ctx.plug (.node ct a t b)).keys := bin _ (by rw [hbk]; exact List.mem_cons_of_mem _ trB)
      have htrT : b.rootKey ∈ T := hk _ trK
      have hytr : y ≠ b.rootKey := fun e => hyB (e ▸ trB)
      refine WP.spec_bind (timer.set_right.on _ y b.rootKey hT hyT) fun s5 e => ?_
      subst e
      have r5 := r4.wr_tr (v := b.rootKey) hT hyT (Or.inl ⟨y, Or.inr yK, Or.inr (Or.inl rfl)⟩)
      refine WP.spec_bind (timer.set_parent.on _ b.rootKey y hT htrT) fun s6 e => ?_
      subst e
      have r6 := r5.wr_tp (v := y) hT htrT (Or.inl ⟨_, Or.inr trK, Or.inr (Or.inr rfl)⟩)
      refine (WP.spec_ok _).2 ⟨rfl, rfl, rfl, _, r6, fun z h0 hzB hzy => ?_, ?_⟩
      · have hzq : z ≠ q := fun e => hzB (e ▸ hqB)
        have hztr : z ≠ b.rootKey := fun e => hzB (e ▸ trB)
        have hzx : z ≠ g.rootKey := fun e => by
          rcases g.rootKey_mem with e0 | m
          · exact h0 (e.trans e0)
          · exact hzB (e ▸ gB _ m)
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Function.update_apply, hzq, hztr, hzx, hzy]
      · rw [show ((((((lk st s1).setL q g.rootKey).setP g.rootKey q).setR y b.rootKey).setP b.rootKey y).r y) =
          b.rootKey by simp]
        refine hBK.reparent hBn (fun _ => ?_) (fun z hz hne => ?_)
        · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Function.update_apply, hytr, hytr.symm]
        · have hzy : z ≠ y := fun e => hyB (e ▸ hz)
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Function.update_apply, hzy, hne]
  rintro ⟨s2, x1, xp, y1⟩ ⟨ey1, exp, ex1, K2, r2, P1, P2⟩
  simp only at ey1 exp ex1
  subst y1 xp x1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_mono (delTwoFin.spec s2 c t (b := b) (B := ctx2.plug g) hT hN h hd hk hbk ha r2 P1 P2
    (hfix ctx2 cy y g hL eb)) fun s' hs => ?_
  obtain ⟨s7, s8, m, h1, h2, h3⟩ := hs
  exact ⟨ctx2, cy, y, g, hL, eb, s7, s8, m, h1, h2, h3⟩

/-- The three shapes of `remove`'s structural part: the subtree `tx` at the path `ctxX` is where `x` sits
(`x = tx.rootKey`, `x_parent = ctxX.par`); `rr` is the removed colour. -/
def DelShape (ctx : TRB.Ctx) (ct : Bool) (a b : TRB.RBT) (ctxX : TRB.Ctx) (tx : TRB.RBT) (rr : Bool) : Prop :=
  (a = .leaf ∧ ctxX = ctx ∧ tx = b ∧ rr = ct) ∨ (a ≠ .leaf ∧ b = .leaf ∧ ctxX = ctx ∧ tx = a ∧ rr = ct) ∨
  (∃ ctx2 cy y, TRB.LSpine ctx2 ∧ a ≠ .leaf ∧ b = ctx2.plug (.node cy .leaf y tx) ∧
    ctxX = TRB.Ctx.app ctx2 (.rc ct a y ctx) ∧ rr = cy)

/-- **`remove` after the `TIMER_MIN` update** (`delTail`): one of the three shapes, the fixup (when the
removed colour is black), the clearing of `t`. -/
theorem delTail.spec (s1 : S) (c t : U64) {ctx : TRB.Ctx} {ct : Bool} {a b : TRB.RBT} {Q : S → S → Prop}
    (hT : TcbPlaced T) (hN : NodePlaced st T s1 c)
    (h : TRB.Rep (lk st s1) 0#u64 (L.mem s1 (L.nodeAt s1 c layout.node.TIMER_ROOT)) (ctx.plug (.node ct a t b)))
    (hd : (ctx.plug (.node ct a t b)).keys.Nodup) (hk : ∀ z ∈ (ctx.plug (.node ct a t b)).keys, z ∈ T)
    (hh : (ctx.plug (.node ct a t b)).height ≤ 128)
    (hfix : ∀ ctxX tx rr s7, DelShape ctx ct a b ctxX tx rr →
      DelMid st T s1 c (ctx.plug (.node ct a t b)).keys s7 (ctxX.plug tx) → rr = false →
      timer.remove_fixup st s7 c tx.rootKey ctxX.par ⦃ s8 => Q s7 s8 ⦄) :
    delTail st s1 c t ⦃ s' => ∃ ctxX tx rr s7 s8, DelShape ctx ct a b ctxX tx rr ∧
      DelMid st T s1 c (ctx.plug (.node ct a t b)).keys s7 (ctxX.plug tx) ∧
      (rr = true → s8 = s7) ∧ (rr = false → Q s7 s8) ∧ s' = clrT st s8 t ⦄ := by
  obtain ⟨-, -, -, -, -, -, ht⟩ := TRB.mid_facts h hd
  have ht : TRB.Rep (lk st s1) ctx.par t (.node ct a t b) := ht
  obtain ⟨-, -, hra, hrb⟩ := TRB.Rep.node_inv ht
  have hra2 : TRB.Rep (lk st s1) t a.rootKey a := by rw [← hra.root]; exact hra
  have hrb2 : TRB.Rep (lk st s1) t b.rootKey b := by rw [← hrb.root]; exact hrb
  unfold delTail
  step with timer.is_red.rep (st := st) s1 ht as ⟨rr, err⟩
  step with timer.left.rep (st := st) s1 ht as ⟨tl, etl⟩
  step with timer.right.rep (st := st) s1 ht as ⟨tr, etr⟩
  have err' : rr = ct := err
  have etl' : tl = a.rootKey := etl
  have etr' : tr = b.rootKey := etr
  subst rr tl tr
  step with obj.Tcb.is_null.spec as ⟨b1, eb1⟩
  split
  · rename_i hb1
    have ea : a = .leaf := hra2.zero (by rw [eb1] at hb1; exact of_decide_eq_true hb1)
    refine WP.spec_bind (Pₘ := fun x => x = b.rootKey) ((WP.spec_ok _).2 rfl) fun x ex => ?_
    subst x
    refine WP.spec_mono (delOne.spec s1 c t (u := b) hT hN h hd hk (Or.inl ⟨ea, rfl⟩)
      (fun s3 m hc => hfix ctx b ct s3 (Or.inl ⟨ea, rfl, rfl, rfl⟩) m hc)) fun s' hs => ?_
    obtain ⟨s3, s4, m, h1, h2, h3⟩ := hs
    exact ⟨ctx, b, ct, s3, s4, Or.inl ⟨ea, rfl, rfl, rfl⟩, m, h1, h2, h3⟩
  · rename_i hb1
    have ha : a ≠ .leaf := fun e => hb1 (by rw [eb1, e]; rfl)
    step with obj.Tcb.is_null.spec as ⟨b2, eb2⟩
    split
    · rename_i hb2
      have eb : b = .leaf := hrb2.zero (by rw [eb2] at hb2; exact of_decide_eq_true hb2)
      refine WP.spec_mono (delOne.spec s1 c t (u := a) hT hN h hd hk (Or.inr ⟨eb, rfl⟩)
        (fun s3 m hc => hfix ctx a ct s3 (Or.inr (Or.inl ⟨ha, eb, rfl, rfl, rfl⟩)) m hc)) fun s' hs => ?_
      obtain ⟨s3, s4, m, h1, h2, h3⟩ := hs
      exact ⟨ctx, a, ct, s3, s4, Or.inr (Or.inl ⟨ha, eb, rfl, rfl, rfl⟩), m, h1, h2, h3⟩
    · rename_i hb2
      have hb : b ≠ .leaf := fun e => hb2 (by rw [eb2, e]; rfl)
      refine WP.spec_mono (delTwo.spec s1 c t hT hN h hd hk ha hb hh
        (fun ctx2 cy y g hL eb s7 m hc => hfix _ g cy s7 (Or.inr (Or.inr ⟨ctx2, cy, y, hL, ha, eb, rfl, rfl⟩))
          (by rw [TRB.Ctx.plug_app]; exact m) hc)) fun s' hs => ?_
      obtain ⟨ctx2, cy, y, g, hL, eb, s7, s8, m, h1, h2, h3⟩ := hs
      exact ⟨_, g, cy, s7, s8, Or.inr (Or.inr ⟨ctx2, cy, y, hL, ha, eb, rfl, rfl⟩),
        by rw [TRB.Ctx.plug_app]; exact m, h1, h2, h3⟩

end

end Fl4ProofsA64.P1
