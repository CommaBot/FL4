-- AArch64 port of Fl4Proofs.P1.TimerRBRotH (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d, TIMER-RB-PLAN stage 3c, part 3): `timer::rotate_left` / `rotate_right` on the heap.  A rotation at
a node `x` of the core's tree (with context `ctx`) leaves the heap representing the abstractly rotated tree
from the (possibly new) root word, and writes only the links of `x`, its rotated child `y`, the moved
subtree's root `b`, the hole's parent `ctx.par`, and the root word (`timer.rotate_left.rep`,
`timer.rotate_right.rep`).  The walk carries `RW`: the links agree on `T` with an explicit `Links` value
(updated per write), the root word is known, and the writes stay in a footprint.
-/
import Fl4ProofsA64.P1.TimerRBRotP
import Fl4ProofsA64.P1.TimerRBWr
import Fl4ProofsA64.P1.TimerRBRead
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

namespace TRB

@[simp] theorem Links.setL_l (k : Links) (z v : U64) : (k.setL z v).l = Function.update k.l z v := rfl
@[simp] theorem Links.setL_r (k : Links) (z v : U64) : (k.setL z v).r = k.r := rfl
@[simp] theorem Links.setL_p (k : Links) (z v : U64) : (k.setL z v).p = k.p := rfl
@[simp] theorem Links.setL_red (k : Links) (z v : U64) : (k.setL z v).red = k.red := rfl
@[simp] theorem Links.setR_l (k : Links) (z v : U64) : (k.setR z v).l = k.l := rfl
@[simp] theorem Links.setR_r (k : Links) (z v : U64) : (k.setR z v).r = Function.update k.r z v := rfl
@[simp] theorem Links.setR_p (k : Links) (z v : U64) : (k.setR z v).p = k.p := rfl
@[simp] theorem Links.setR_red (k : Links) (z v : U64) : (k.setR z v).red = k.red := rfl
@[simp] theorem Links.setP_l (k : Links) (z v : U64) : (k.setP z v).l = k.l := rfl
@[simp] theorem Links.setP_r (k : Links) (z v : U64) : (k.setP z v).r = k.r := rfl
@[simp] theorem Links.setP_p (k : Links) (z v : U64) : (k.setP z v).p = Function.update k.p z v := rfl
@[simp] theorem Links.setP_red (k : Links) (z v : U64) : (k.setP z v).red = k.red := rfl

theorem LinksEqOn.trans {T : Set U64} {k1 k2 k3 : Links} (e1 : LinksEqOn T k1 k2) (e2 : LinksEqOn T k2 k3) :
    LinksEqOn T k1 k3 := fun y hy => by
  obtain ⟨a1, b1, c1, d1⟩ := e1 y hy
  obtain ⟨a2, b2, c2, d2⟩ := e2 y hy
  exact ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1⟩

theorem LinksEqOn.setL {T : Set U64} {k k' : Links} (e : LinksEqOn T k k') (z v : U64) :
    LinksEqOn T (k.setL z v) (k'.setL z v) := fun y hy => by
  obtain ⟨a, b, c, d⟩ := e y hy
  refine ⟨?_, b, c, d⟩
  show Function.update k'.l z v y = Function.update k.l z v y
  by_cases h : y = z
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]; exact a
theorem LinksEqOn.setR {T : Set U64} {k k' : Links} (e : LinksEqOn T k k') (z v : U64) :
    LinksEqOn T (k.setR z v) (k'.setR z v) := fun y hy => by
  obtain ⟨a, b, c, d⟩ := e y hy
  refine ⟨a, ?_, c, d⟩
  show Function.update k'.r z v y = Function.update k.r z v y
  by_cases h : y = z
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]; exact b
theorem LinksEqOn.setP {T : Set U64} {k k' : Links} (e : LinksEqOn T k k') (z v : U64) :
    LinksEqOn T (k.setP z v) (k'.setP z v) := fun y hy => by
  obtain ⟨a, b, c, d⟩ := e y hy
  refine ⟨a, b, ?_, d⟩
  show Function.update k'.p z v y = Function.update k.p z v y
  by_cases h : y = z
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]; exact c

/-- A parent write outside `T` is invisible on `T`. -/
theorem LinksEqOn.setP_out {T : Set U64} {k k' : Links} (e : LinksEqOn T k k') {z : U64} (hz : z ∉ T) (v : U64) :
    LinksEqOn T (k.setP z v) k' := fun y hy => by
  obtain ⟨a, b, c, d⟩ := e y hy
  refine ⟨a, b, ?_, d⟩
  show k'.p y = Function.update k.p z v y
  rw [Function.update_of_ne (fun h => hz (by rw [← h]; exact hy))]; exact c

/-- The hole's parent link (or nothing, at the top) re-pointed to `y`. -/
def holeSet : Ctx → U64 → Links → Links
  | .top, _, K => K
  | .lc _ p _ _, y, K => K.setL p y
  | .rc _ _ p _, y, K => K.setR p y

/-- The root word after re-pointing the hole: `y` at the top, else unchanged. -/
def holeR : Ctx → U64 → U64 → U64
  | .top, y, _ => y
  | .lc _ _ _ _, _, R => R
  | .rc _ _ _ _, _, R => R

@[simp] theorem holeSet_p (ctx : Ctx) (y : U64) (K : Links) : (holeSet ctx y K).p = K.p := by
  cases ctx <;> rfl
@[simp] theorem holeSet_red (ctx : Ctx) (y : U64) (K : Links) : (holeSet ctx y K).red = K.red := by
  cases ctx <;> rfl
@[simp] theorem holeSet_l_ne {ctx : Ctx} {y z : U64} {K : Links} (h : z ≠ ctx.par) : (holeSet ctx y K).l z = K.l z := by
  cases ctx with
  | top => rfl
  | lc c p r up => exact Function.update_of_ne h _ _
  | rc c l p up => rfl
@[simp] theorem holeSet_r_ne {ctx : Ctx} {y z : U64} {K : Links} (h : z ≠ ctx.par) : (holeSet ctx y K).r z = K.r z := by
  cases ctx with
  | top => rfl
  | lc c p r up => rfl
  | rc c l p up => exact Function.update_of_ne h _ _

/-- What `replace_child` needs to pick the hole's side: the parent's left link is the old child iff the
hole is a left one. -/
def HoleL (k : Links) (x : U64) : Ctx → Prop
  | .top => True
  | .lc _ p _ _ => k.l p = x
  | .rc _ _ p _ => k.l p ≠ x

theorem HoleL.congr {k k' : Links} {x : U64} {ctx : Ctx} (h : HoleL k x ctx) (e : k'.l ctx.par = k.l ctx.par) :
    HoleL k' x ctx := by
  cases ctx with
  | top => trivial
  | lc c p r up => show k'.l p = x; rw [show k'.l p = k.l p from e]; exact h
  | rc c l p up => show k'.l p ≠ x; rw [show k'.l p = k.l p from e]; exact h

theorem Rep.node_inv {k : Links} {par x : U64} {c : Bool} {l r : RBT} (h : Rep k par x (.node c l x r)) :
    k.p x = par ∧ k.red x = c ∧ Rep k x (k.l x) l ∧ Rep k x (k.r x) r := by
  cases h with
  | node _ hp hc hl hr => exact ⟨hp, hc, hl, hr⟩

/-- Facts about a subtree `t` at a hole of a represented tree without duplicate keys. -/
theorem mid_facts {k : Links} {R : U64} {ctx : Ctx} {t : RBT} (h : Rep k 0#u64 R (ctx.plug t))
    (hd : (ctx.plug t).keys.Nodup) :
    (∀ z ∈ t.keys, z ≠ ctx.par) ∧ (∀ z ∈ t.keys, z ≠ 0#u64) ∧ (ctx ≠ .top → ctx.par ∈ (ctx.plug t).keys) ∧
    (ctx ≠ .top → ctx.par ≠ 0#u64) ∧ (∀ z ∈ t.keys, z ∈ (ctx.plug t).keys) ∧
    (t.rootKey ≠ 0#u64 → HoleL k t.rootKey ctx) ∧ Rep k ctx.par t.rootKey t := by
  obtain ⟨hc, ht⟩ := (rep_plug ctx _).1 h
  have n0 := h.keys_ne0
  have hk := Ctx.plug_keys ctx t
  rw [hk] at hd n0
  have nz : ∀ z ∈ t.keys, z ≠ 0#u64 := fun z hz =>
    n0 z (List.mem_append_left _ (List.mem_append_right _ hz))
  have pk : ctx ≠ .top → ctx.par ∈ (ctx.plug t).keys := fun e => by
    rw [hk]; have := Ctx.par_mem ctx e; simp only [List.mem_append] at this ⊢; tauto
  refine ⟨fun z hz => ?_, nz, pk, fun e => n0 _ (by rw [← hk]; exact pk e),
    fun z hz => by rw [hk]; exact List.mem_append_left _ (List.mem_append_right _ hz), fun h0 => ?_, ht⟩
  · by_cases e : ctx = .top
    · subst e; exact nz z hz
    · exact nd_mid hd hz (Ctx.par_mem ctx e)
  · have hm : t.rootKey ∈ t.keys := (t.rootKey_mem).resolve_left h0
    cases hc with
    | top => trivial
    | lc hx hl => exact hl
    | @rc c l kk up _ hx hr hcol hp hl hu =>
      intro e
      rcases hl.root_mem with e0 | m
      · exact h0 (e.symm.trans e0)
      · refine nd_mid hd hm ?_ rfl
        have m' : t.rootKey ∈ l.keys := by rw [← e]; exact m
        simp only [Ctx.pre, Ctx.post, List.mem_append]
        exact Or.inl (Or.inl (Or.inr m'))

end TRB

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-- A node-word write keeps the links of `T`. -/
theorem lk_wr_node {s : S} {c o v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c) (ho : o.val < 4288)
    (ho8 : o.val % 8 = 0) : TRB.LinksEqOn T (lk st s) (lk st (L.wr s (L.nodeAt s c o) v)) := fun y hy => by
  have f : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s (L.nodeAt s c o) v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun K h1 h2 => trb_fld_wr_node hT hN ho ho8 hy h1 h2
  refine ⟨f 3544#u64 (by simp) (by simp), f 3552#u64 (by simp) (by simp), f 3560#u64 (by simp) (by simp), ?_⟩
  show ((L.mem (L.wr s (L.nodeAt s c o) v) (thA y) &&& 1#u64) != 0#u64) = ((L.mem s (thA y) &&& 1#u64) != 0#u64)
  rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, f 3568#u64 (by simp) (by simp)]

/-- The state of a link walk from `s0`: the links agree on `T` with `K`, the root word of core `c` is `R`,
the writes since `s0` lie in `F`. -/
structure RW (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 s : S) (c : U64) (K : TRB.Links)
    (R : U64) (F : U64 → Prop) : Prop where
  eq : TRB.LinksEqOn T K (lk st s)
  root : L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) = R
  wi : WritesIn st s0 s F
  np : NodePlaced st T s c

theorem RW.init {s : S} {c : U64} (hN : NodePlaced st T s c) (F : U64 → Prop) :
    RW st T s s c (lk st s) (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)) F :=
  ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl, WritesIn.refl _ _, hN⟩

theorem root_wr_fld {s : S} {c z K v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c) (hz : z ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    L.mem (L.wr s (core.num.U64.wrapping_add z K) v)
      (L.nodeAt (L.wr s (core.num.U64.wrapping_add z K) v) c layout.node.TIMER_ROOT) =
      L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) :=
  trb_node_wr_fld hT hz hK hK8 hN (by rw [timer_root_val]; simp) (by rw [timer_root_val])

theorem RW.wr_tl {s0 s : S} {c R z v : U64} {K : TRB.Links} {F : U64 → Prop} (h : RW st T s0 s c K R F)
    (hT : TcbPlaced T) (hz : z ∈ T) (hF : F (tlA z)) : RW st T s0 (L.wr s (tlA z) v) c (K.setL z v) R F :=
  ⟨(h.eq.setL z v).trans (lk_wr_tl hT hz), (root_wr_fld (K := 3544#u64) hT h.np hz (by simp) (by simp)).trans h.root,
    (h.wi.trans (writesIn_wr (a := tlA z) (tz_aligned hT (Tz.of_mem hz) (K := 3544#u64) (by simp) (by simp)))).mono
      fun b hb => hb.elim id fun e => by rw [e]; exact hF, h.np.wr⟩
theorem RW.wr_tr {s0 s : S} {c R z v : U64} {K : TRB.Links} {F : U64 → Prop} (h : RW st T s0 s c K R F)
    (hT : TcbPlaced T) (hz : z ∈ T) (hF : F (trA z)) : RW st T s0 (L.wr s (trA z) v) c (K.setR z v) R F :=
  ⟨(h.eq.setR z v).trans (lk_wr_tr hT hz), (root_wr_fld (K := 3552#u64) hT h.np hz (by simp) (by simp)).trans h.root,
    (h.wi.trans (writesIn_wr (a := trA z) (tz_aligned hT (Tz.of_mem hz) (K := 3552#u64) (by simp) (by simp)))).mono
      fun b hb => hb.elim id fun e => by rw [e]; exact hF, h.np.wr⟩
theorem RW.wr_tp {s0 s : S} {c R z v : U64} {K : TRB.Links} {F : U64 → Prop} (h : RW st T s0 s c K R F)
    (hT : TcbPlaced T) (hz : z ∈ T) (hF : F (tpA z)) : RW st T s0 (L.wr s (tpA z) v) c (K.setP z v) R F :=
  ⟨(h.eq.setP z v).trans (lk_wr_tp hT hz), (root_wr_fld (K := 3560#u64) hT h.np hz (by simp) (by simp)).trans h.root,
    (h.wi.trans (writesIn_wr (a := tpA z) (tz_aligned hT (Tz.of_mem hz) (K := 3560#u64) (by simp) (by simp)))).mono
      fun b hb => hb.elim id fun e => by rw [e]; exact hF, h.np.wr⟩

theorem RW.wr_root {s0 s : S} {c R v : U64} {K : TRB.Links} {F : U64 → Prop} (h : RW st T s0 s c K R F)
    (hT : TcbPlaced T) (hF : F (L.nodeAt s0 c layout.node.TIMER_ROOT)) :
    RW st T s0 (L.wr s (L.nodeAt s c layout.node.TIMER_ROOT) v) c K v F := by
  have ho : layout.node.TIMER_ROOT.val < 4288 := by rw [timer_root_val]; simp
  have ho8 : layout.node.TIMER_ROOT.val % 8 = 0 := by rw [timer_root_val]
  refine ⟨h.eq.trans (lk_wr_node hT h.np ho ho8), ?_, ?_, h.np.wr⟩
  · rw [trb_node_wr_node h.np h.np ho ho8 ho ho8, if_pos ⟨rfl, rfl⟩]
  · refine (h.wi.trans (writesIn_wr (a := L.nodeAt s c layout.node.TIMER_ROOT) (nodeAt_aligned h.np ho ho8))).mono
      fun b hb => hb.elim id fun e => ?_
    rw [e, nodeAt_of_ksb h.wi.1]; exact hF

/-- `replace_child(ctx.par, x, y)`: re-points the hole (`TRB.holeSet`; the root word at the top). -/
theorem timer.replace_child.rw (s : S) (c : U64) {s0 : S} {ctx : TRB.Ctx} {x y R : U64} {K : TRB.Links}
    {F : U64 → Prop} (h : RW st T s0 s c K R F) (hT : TcbPlaced T) (hp : ctx ≠ .top → ctx.par ∈ T)
    (hl : TRB.HoleL K x ctx)
    (hF : F (L.nodeAt s0 c layout.node.TIMER_ROOT) ∧ F (tlA ctx.par) ∧ F (trA ctx.par)) :
    timer.replace_child st s c ctx.par x y ⦃ s' => RW st T s0 s' c (TRB.holeSet ctx y K) (TRB.holeR ctx y R) F ⦄ := by
  unfold timer.replace_child
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  cases ctx with
  | top =>
    split
    · unfold timer.set_root
      exact WP.spec_mono (obj.node_set.spec s c _ y) fun s' e => by subst e; exact h.wr_root hT hF.1
    · rename_i hb; rw [eb] at hb; simp [TRB.Ctx.par] at hb
  | lc cp p rp up =>
    have hpT : p ∈ T := hp (fun e => by cases e)
    have hp0 : p ≠ 0#u64 := fun e => (hT p hpT).ne0 (by rw [e]; rfl)
    simp only [TRB.Ctx.par] at eb hF ⊢
    split
    · rename_i hb
      rw [eb] at hb; exact absurd (of_decide_eq_true hb) hp0
    · step with timer.left.links (st := st) s p as ⟨lv, elv⟩
      step with tcb_eq.blk lv x as ⟨bq, ebq⟩
      split
      · exact WP.spec_mono (timer.set_left.on s p y hT hpT) fun s' e => by subst e; exact h.wr_tl hT hpT hF.2.1
      · rename_i hq
        exfalso; apply hq
        rw [ebq, elv, if_neg hp0, (h.eq p hpT).1]
        exact decide_eq_true hl
  | rc cp lp p up =>
    have hpT : p ∈ T := hp (fun e => by cases e)
    have hp0 : p ≠ 0#u64 := fun e => (hT p hpT).ne0 (by rw [e]; rfl)
    simp only [TRB.Ctx.par] at eb hF ⊢
    split
    · rename_i hb
      rw [eb] at hb; exact absurd (of_decide_eq_true hb) hp0
    · step with timer.left.links (st := st) s p as ⟨lv, elv⟩
      step with tcb_eq.blk lv x as ⟨bq, ebq⟩
      split
      · rename_i hq
        exfalso
        rw [ebq, elv, if_neg hp0, (h.eq p hpT).1] at hq
        exact hl (of_decide_eq_true hq)
      · exact WP.spec_mono (timer.set_right.on s p y hT hpT) fun s' e => by subst e; exact h.wr_tr hT hpT hF.2.2

/-- The words a rotation at `x` writes: the links of `x`, `y`, `b` and the hole's parent, and the root word. -/
def RotFoot (st : machine.Store S) [L : LawfulStore st] (s : S) (c x y b p : U64) (w : U64) : Prop :=
  (∃ z, (z = x ∨ z = y ∨ z = b ∨ z = p) ∧ (w = tlA z ∨ w = trA z ∨ w = tpA z)) ∨
    w = L.nodeAt s c layout.node.TIMER_ROOT

/-- **`timer::rotate_left` on the heap.** -/
theorem timer.rotate_left.rep (s : S) (c : U64) {ctx : TRB.Ctx} {cx cy : Bool} {a b g : TRB.RBT} {x y : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s c)
    (h : TRB.Rep (lk st s) 0#u64 (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT))
      (ctx.plug (.node cx a x (.node cy b y g))))
    (hd : (ctx.plug (.node cx a x (.node cy b y g))).keys.Nodup)
    (hk : ∀ z ∈ (ctx.plug (.node cx a x (.node cy b y g))).keys, z ∈ T) :
    timer.rotate_left st s c x ⦃ s' =>
      TRB.Rep (lk st s') 0#u64 (L.mem s' (L.nodeAt s' c layout.node.TIMER_ROOT))
        (ctx.plug (TRB.rotL (.node cx a x (.node cy b y g)))) ∧
      WritesIn st s s' (RotFoot st s c x y b.rootKey ctx.par) ⦄ := by
  obtain ⟨mpar, m0, mpk, mp0, mk, mhl, ht⟩ := TRB.mid_facts h hd
  have hM : (a.keys ++ x :: (b.keys ++ y :: g.keys)).Nodup := by
    have hd' := hd; rw [TRB.Ctx.plug_keys] at hd'; exact TRB.nd_in hd'
  have hM2 : (x :: (b.keys ++ y :: g.keys)).Nodup := hM.sublist (List.sublist_append_right _ _)
  have hM3 : (b.keys ++ y :: g.keys).Nodup := (List.nodup_cons.1 hM2).2
  have inx : x ∈ (TRB.RBT.node cx a x (.node cy b y g)).keys := by simp [TRB.RBT.keys]
  have iny : y ∈ (TRB.RBT.node cx a x (.node cy b y g)).keys := by simp [TRB.RBT.keys]
  have inb : b.rootKey ≠ 0#u64 → b.rootKey ∈ (TRB.RBT.node cx a x (.node cy b y g)).keys := fun h0 => by
    have := (b.rootKey_mem).resolve_left h0; simp [TRB.RBT.keys, this]
  have hx0 := m0 x inx
  have hy0 := m0 y iny
  have hxT := hk x (mk x inx)
  have hyT := hk y (mk y iny)
  have hbT : b.rootKey ≠ 0#u64 → b.rootKey ∈ T := fun h0 => hk _ (mk _ (inb h0))
  have hpT : ctx ≠ .top → ctx.par ∈ T := fun e => hk _ (mpk e)
  have hxp := mpar x inx
  have hyp := mpar y iny
  have ht' : TRB.Rep (lk st s) ctx.par x (.node cx a x (.node cy b y g)) := ht
  obtain ⟨hpx, -, -, hyy⟩ := TRB.Rep.node_inv ht'
  have e1 : (lk st s).r x = y := hyy.root
  rw [e1] at hyy
  obtain ⟨-, -, hb, -⟩ := TRB.Rep.node_inv hyy
  have e2 : (lk st s).l y = b.rootKey := hb.root
  have hxy : x ≠ y := fun e => (List.nodup_cons.1 hM2).1 (by simp [e])
  have hxb : x ≠ b.rootKey := fun e => by
    rcases b.rootKey_mem with e' | e'
    · exact hx0 (e.trans e')
    · exact (List.nodup_cons.1 hM2).1 (List.mem_append_left _ (e ▸ e'))
  have hyb : y ≠ b.rootKey := fun e => by
    rcases b.rootKey_mem with e' | e'
    · exact hy0 (e.trans e')
    · exact TRB.nd_sep hM3 e' (List.mem_cons_self ..) e.symm
  have hbp : b.rootKey ≠ 0#u64 → b.rootKey ≠ ctx.par := fun h0 => mpar _ (inb h0)
  have hpb : ctx ≠ .top → ctx.par ≠ b.rootKey := fun et e => by
    by_cases h0 : b.rootKey = 0#u64
    · exact mp0 et (e.trans h0)
    · exact mpar _ (inb h0) e.symm
  have fx : ∀ w, (w = tlA x ∨ w = trA x ∨ w = tpA x) → RotFoot st s c x y b.rootKey ctx.par w :=
    fun w hw => Or.inl ⟨x, Or.inl rfl, hw⟩
  have fy : ∀ w, (w = tlA y ∨ w = trA y ∨ w = tpA y) → RotFoot st s c x y b.rootKey ctx.par w :=
    fun w hw => Or.inl ⟨y, Or.inr (Or.inl rfl), hw⟩
  have fb : ∀ w, (w = tlA b.rootKey ∨ w = trA b.rootKey ∨ w = tpA b.rootKey) →
      RotFoot st s c x y b.rootKey ctx.par w :=
    fun w hw => Or.inl ⟨b.rootKey, Or.inr (Or.inr (Or.inl rfl)), hw⟩
  have fp : ∀ w, (w = tlA ctx.par ∨ w = trA ctx.par ∨ w = tpA ctx.par) → RotFoot st s c x y b.rootKey ctx.par w :=
    fun w hw => Or.inl ⟨ctx.par, Or.inr (Or.inr (Or.inr rfl)), hw⟩
  have froot : RotFoot st s c x y b.rootKey ctx.par (L.nodeAt s c layout.node.TIMER_ROOT) := Or.inr rfl
  have r0 := RW.init hN (RotFoot st s c x y b.rootKey ctx.par)
  unfold timer.rotate_left
  step with timer.right.links (st := st) s x as ⟨y', ey'⟩
  rw [if_neg hx0, e1] at ey'
  subst y'
  step with timer.left.links (st := st) s y as ⟨yl, eyl⟩
  rw [if_neg hy0, e2] at eyl
  subst yl
  refine WP.spec_bind (timer.set_right.on s x b.rootKey hT hxT) fun s1 e => ?_
  subst e
  have r1 := r0.wr_tr (v := b.rootKey) hT hxT (fx _ (Or.inr (Or.inl rfl)))
  step with obj.Tcb.is_null.spec as ⟨bn, ebn⟩
  refine WP.spec_bind (Pₘ := fun r => RW st T s r.1 c (((lk st s).setR x b.rootKey).setP b.rootKey x)
    (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)) (RotFoot st s c x y b.rootKey ctx.par) ∧ r.2 = x) ?_ ?_
  · split
    · rename_i hbn
      have e0 : b.rootKey = 0#u64 := by rw [ebn] at hbn; exact of_decide_eq_true hbn
      simp only [WP.spec_ok]
      refine ⟨⟨r1.eq.setP_out (z := b.rootKey) (by rw [e0]; exact fun h0 => (hT _ h0).ne0 (by simp)) x,
        r1.root, r1.wi, r1.np⟩, trivial⟩
    · rename_i hbn
      have hb0 : b.rootKey ≠ 0#u64 := fun e => hbn (by rw [ebn, e]; rfl)
      refine WP.spec_bind (timer.set_parent.on _ b.rootKey x hT (hbT hb0)) fun s3 e => ?_
      subst e
      simp only [WP.spec_ok]
      exact ⟨r1.wr_tp hT (hbT hb0) (fb _ (Or.inr (Or.inr rfl))), trivial⟩
  rintro ⟨s2, x1⟩ ⟨h2, ex1⟩
  simp only at h2 ex1
  subst x1
  try simp only [WP.uncurry'_pair]
  step with timer.parent.links (st := st) s2 x as ⟨xp, exp⟩
  rw [if_neg hx0, (h2.eq x hxT).2.2.1] at exp
  have exp' : xp = ctx.par := exp.trans ((Function.update_of_ne hxb _ _).trans hpx)
  subst exp'
  refine WP.spec_bind (timer.set_parent.on _ y ctx.par hT hyT) fun s3 e => ?_
  subst e
  have r3 := h2.wr_tp (v := ctx.par) hT hyT (fy _ (Or.inr (Or.inr rfl)))
  refine WP.spec_bind (timer.replace_child.rw (y := y) _ c r3 hT hpT ((mhl hx0).congr rfl)
    ⟨froot, fp _ (Or.inl rfl), fp _ (Or.inr (Or.inl rfl))⟩) fun s4 r4 => ?_
  refine WP.spec_bind (timer.set_left.on s4 y x hT hyT) fun s5 e => ?_
  subst e
  have r5 := r4.wr_tl (v := x) hT hyT (fy _ (Or.inl rfl))
  refine WP.spec_mono (timer.set_parent.on _ x y hT hxT) fun s6 e => ?_
  subst e
  have r6 := r5.wr_tp (v := y) hT hxT (fx _ (Or.inr (Or.inr rfl)))
  refine ⟨?_, r6.wi⟩
  rw [r6.root]
  refine TRB.Rep.congr_on ?_ (fun z hz => hk z (by rwa [TRB.plug_rotL_keys] at hz)) r6.eq
  refine TRB.rotL_rep h hd ?_ ?_ ?_ ?_ ?_
  · simp [Function.update_apply, hxy, hxy.symm, hxb, hxb.symm, hyb, hyb.symm, hxp, hyp]
  · simp [Function.update_apply, hxy, hxy.symm, hxb, hxb.symm, hyb, hyb.symm, hxp, hyp]
  · intro hb0
    have h3 := hbp hb0
    simp [Function.update_apply, hxy, hxy.symm, hxb, hxb.symm, hyb, hyb.symm, hxp, hyp, h3]
  · intro z h1 h2 h3 h4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Function.update_apply, h1, h2, h3, h4]
  · cases ctx with
    | top => exact rfl
    | lc cp p rp up =>
      have hp := hpb (by intro e; cases e)
      simp only [TRB.Ctx.par] at hxp hyp hp
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
        simp [TRB.holeSet, Function.update_apply, hxy, hxy.symm, hxb, hxb.symm, hyb, hyb.symm, hxp, hxp.symm,
          hyp, hyp.symm, hp, hp.symm]
    | rc cp lp p up =>
      have hp := hpb (by intro e; cases e)
      simp only [TRB.Ctx.par] at hxp hyp hp
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
        simp [TRB.holeSet, Function.update_apply, hxy, hxy.symm, hxb, hxb.symm, hyb, hyb.symm, hxp, hxp.symm,
          hyp, hyp.symm, hp, hp.symm]


/-- **`timer::rotate_right` on the heap** (mirror of `timer.rotate_left.rep`). -/
theorem timer.rotate_right.rep (s : S) (c : U64) {ctx : TRB.Ctx} {cx cy : Bool} {a b g : TRB.RBT} {x y : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s c)
    (h : TRB.Rep (lk st s) 0#u64 (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT))
      (ctx.plug (.node cx (.node cy a y b) x g)))
    (hd : (ctx.plug (.node cx (.node cy a y b) x g)).keys.Nodup)
    (hk : ∀ z ∈ (ctx.plug (.node cx (.node cy a y b) x g)).keys, z ∈ T) :
    timer.rotate_right st s c x ⦃ s' =>
      TRB.Rep (lk st s') 0#u64 (L.mem s' (L.nodeAt s' c layout.node.TIMER_ROOT))
        (ctx.plug (TRB.rotR (.node cx (.node cy a y b) x g))) ∧
      WritesIn st s s' (RotFoot st s c x y b.rootKey ctx.par) ⦄ := by
  obtain ⟨mpar, m0, mpk, mp0, mk, mhl, ht⟩ := TRB.mid_facts h hd
  have hM : (a.keys ++ y :: b.keys ++ x :: g.keys).Nodup := by
    have hd' := hd; rw [TRB.Ctx.plug_keys] at hd'; exact TRB.nd_in hd'
  have hM1 : (a.keys ++ y :: b.keys).Nodup := hM.sublist (List.sublist_append_left _ _)
  have hM2 : (y :: b.keys).Nodup := hM1.sublist (List.sublist_append_right _ _)
  have inx : x ∈ (TRB.RBT.node cx (.node cy a y b) x g).keys := by simp [TRB.RBT.keys]
  have iny : y ∈ (TRB.RBT.node cx (.node cy a y b) x g).keys := by simp [TRB.RBT.keys]
  have inb : b.rootKey ≠ 0#u64 → b.rootKey ∈ (TRB.RBT.node cx (.node cy a y b) x g).keys := fun h0 => by
    have := (b.rootKey_mem).resolve_left h0; simp [TRB.RBT.keys, this]
  have hx0 := m0 x inx
  have hy0 := m0 y iny
  have hxT := hk x (mk x inx)
  have hyT := hk y (mk y iny)
  have hbT : b.rootKey ≠ 0#u64 → b.rootKey ∈ T := fun h0 => hk _ (mk _ (inb h0))
  have hpT : ctx ≠ .top → ctx.par ∈ T := fun e => hk _ (mpk e)
  have hxp := mpar x inx
  have hyp := mpar y iny
  have ht' : TRB.Rep (lk st s) ctx.par x (.node cx (.node cy a y b) x g) := ht
  obtain ⟨hpx, -, hyy, -⟩ := TRB.Rep.node_inv ht'
  have e1 : (lk st s).l x = y := hyy.root
  rw [e1] at hyy
  obtain ⟨-, -, -, hb⟩ := TRB.Rep.node_inv hyy
  have e2 : (lk st s).r y = b.rootKey := hb.root
  have hxy : x ≠ y := fun e => TRB.nd_sep hM (a := y) (b := x) (by simp) (by simp) e.symm
  have hxb : x ≠ b.rootKey := fun e => by
    rcases b.rootKey_mem with e' | e'
    · exact hx0 (e.trans e')
    · exact TRB.nd_sep hM (a := x) (b := x) (by simp [e, e']) (by simp) rfl
  have hyb : y ≠ b.rootKey := fun e => by
    rcases b.rootKey_mem with e' | e'
    · exact hy0 (e.trans e')
    · exact (List.nodup_cons.1 hM2).1 (e ▸ e')
  have hbp : b.rootKey ≠ 0#u64 → b.rootKey ≠ ctx.par := fun h0 => mpar _ (inb h0)
  have hpb : ctx ≠ .top → ctx.par ≠ b.rootKey := fun et e => by
    by_cases h0 : b.rootKey = 0#u64
    · exact mp0 et (e.trans h0)
    · exact mpar _ (inb h0) e.symm
  have fx : ∀ w, (w = tlA x ∨ w = trA x ∨ w = tpA x) → RotFoot st s c x y b.rootKey ctx.par w :=
    fun w hw => Or.inl ⟨x, Or.inl rfl, hw⟩
  have fy : ∀ w, (w = tlA y ∨ w = trA y ∨ w = tpA y) → RotFoot st s c x y b.rootKey ctx.par w :=
    fun w hw => Or.inl ⟨y, Or.inr (Or.inl rfl), hw⟩
  have fb : ∀ w, (w = tlA b.rootKey ∨ w = trA b.rootKey ∨ w = tpA b.rootKey) →
      RotFoot st s c x y b.rootKey ctx.par w :=
    fun w hw => Or.inl ⟨b.rootKey, Or.inr (Or.inr (Or.inl rfl)), hw⟩
  have fp : ∀ w, (w = tlA ctx.par ∨ w = trA ctx.par ∨ w = tpA ctx.par) → RotFoot st s c x y b.rootKey ctx.par w :=
    fun w hw => Or.inl ⟨ctx.par, Or.inr (Or.inr (Or.inr rfl)), hw⟩
  have froot : RotFoot st s c x y b.rootKey ctx.par (L.nodeAt s c layout.node.TIMER_ROOT) := Or.inr rfl
  have r0 := RW.init hN (RotFoot st s c x y b.rootKey ctx.par)
  unfold timer.rotate_right
  step with timer.left.links (st := st) s x as ⟨y', ey'⟩
  rw [if_neg hx0, e1] at ey'
  subst y'
  step with timer.right.links (st := st) s y as ⟨yr, eyr⟩
  rw [if_neg hy0, e2] at eyr
  subst yr
  refine WP.spec_bind (timer.set_left.on s x b.rootKey hT hxT) fun s1 e => ?_
  subst e
  have r1 := r0.wr_tl (v := b.rootKey) hT hxT (fx _ (Or.inl rfl))
  step with obj.Tcb.is_null.spec as ⟨bn, ebn⟩
  refine WP.spec_bind (Pₘ := fun r => RW st T s r.1 c (((lk st s).setL x b.rootKey).setP b.rootKey x)
    (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)) (RotFoot st s c x y b.rootKey ctx.par) ∧ r.2 = x) ?_ ?_
  · split
    · rename_i hbn
      have e0 : b.rootKey = 0#u64 := by rw [ebn] at hbn; exact of_decide_eq_true hbn
      simp only [WP.spec_ok]
      refine ⟨⟨r1.eq.setP_out (z := b.rootKey) (by rw [e0]; exact fun h0 => (hT _ h0).ne0 (by simp)) x,
        r1.root, r1.wi, r1.np⟩, trivial⟩
    · rename_i hbn
      have hb0 : b.rootKey ≠ 0#u64 := fun e => hbn (by rw [ebn, e]; rfl)
      refine WP.spec_bind (timer.set_parent.on _ b.rootKey x hT (hbT hb0)) fun s3 e => ?_
      subst e
      simp only [WP.spec_ok]
      exact ⟨r1.wr_tp hT (hbT hb0) (fb _ (Or.inr (Or.inr rfl))), trivial⟩
  rintro ⟨s2, x1⟩ ⟨h2, ex1⟩
  simp only at h2 ex1
  subst x1
  try simp only [WP.uncurry'_pair]
  step with timer.parent.links (st := st) s2 x as ⟨xp, exp⟩
  rw [if_neg hx0, (h2.eq x hxT).2.2.1] at exp
  have exp' : xp = ctx.par := exp.trans ((Function.update_of_ne hxb _ _).trans hpx)
  subst exp'
  refine WP.spec_bind (timer.set_parent.on _ y ctx.par hT hyT) fun s3 e => ?_
  subst e
  have r3 := h2.wr_tp (v := ctx.par) hT hyT (fy _ (Or.inr (Or.inr rfl)))
  refine WP.spec_bind (timer.replace_child.rw (y := y) _ c r3 hT hpT ((mhl hx0).congr (Function.update_of_ne hxp.symm _ _))
    ⟨froot, fp _ (Or.inl rfl), fp _ (Or.inr (Or.inl rfl))⟩) fun s4 r4 => ?_
  refine WP.spec_bind (timer.set_right.on s4 y x hT hyT) fun s5 e => ?_
  subst e
  have r5 := r4.wr_tr (v := x) hT hyT (fy _ (Or.inr (Or.inl rfl)))
  refine WP.spec_mono (timer.set_parent.on _ x y hT hxT) fun s6 e => ?_
  subst e
  have r6 := r5.wr_tp (v := y) hT hxT (fx _ (Or.inr (Or.inr rfl)))
  refine ⟨?_, r6.wi⟩
  rw [r6.root]
  refine TRB.Rep.congr_on ?_ (fun z hz => hk z (by rwa [TRB.plug_rotR_keys] at hz)) r6.eq
  refine TRB.rotR_rep h hd ?_ ?_ ?_ ?_ ?_
  · simp [Function.update_apply, hxy, hxy.symm, hxb, hxb.symm, hyb, hyb.symm, hxp, hyp]
  · simp [Function.update_apply, hxy, hxy.symm, hxb, hxb.symm, hyb, hyb.symm, hxp, hyp]
  · intro hb0
    have h3 := hbp hb0
    simp [Function.update_apply, hxy, hxy.symm, hxb, hxb.symm, hyb, hyb.symm, hxp, hyp, h3]
  · intro z h1 h2 h3 h4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Function.update_apply, h1, h2, h3, h4]
  · cases ctx with
    | top => exact rfl
    | lc cp p rp up =>
      have hp := hpb (by intro e; cases e)
      simp only [TRB.Ctx.par] at hxp hyp hp
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
        simp [TRB.holeSet, Function.update_apply, hxy, hxy.symm, hxb, hxb.symm, hyb, hyb.symm, hxp, hxp.symm,
          hyp, hyp.symm, hp, hp.symm]
    | rc cp lp p up =>
      have hp := hpb (by intro e; cases e)
      simp only [TRB.Ctx.par] at hxp hyp hp
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
        simp [TRB.holeSet, Function.update_apply, hxy, hxy.symm, hxb, hxb.symm, hyb, hyb.symm, hxp, hxp.symm,
          hyp, hyp.symm, hp, hp.symm]

end

end Fl4ProofsA64.P1
