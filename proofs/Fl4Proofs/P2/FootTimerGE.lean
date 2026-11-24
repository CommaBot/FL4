/-
# P2: the timer tree code reads and writes only the tree words of a fixed key set (`GE` leaves)

The red-black tree code (`timer.remove`, `timer.insert` and their loops and rotations) on core `c` reaches
the nodes of `c`'s tree only through links. Fix a key set `K` (core `c`'s keys at entry, and the inserted
thread): every word the code touches is a timer field of a key or a node word of core `c` (`TW`), as long
as the root word and the links of the keys `Kr ⊆ K` whose links have been set hold `0` or a key (`TI`).
Every link write stores such a value, so `TI` is kept (`TI.wr_fld`, `TI.wr_node`).

Leaves (`GE` of `P2/GuardGE.lean`, on `guard st R W` with `TW ⊆ R`, `TW ⊆ W`, `TC`): `timer.left` /
`right` / `parent` / `root` return `0` or a key, `is_red`, the setters keep `TI`.

No named premises.
-/
import Fl4Proofs.P2.GuardGE
import Fl4Proofs.P2.FootTimerAcc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {R W : U64 → Prop}

/-- `v` is null or in `K`. -/
def Kz (K : U64 → Prop) (v : U64) : Prop := v = 0#u64 ∨ K v

/-- The tree words: the timer fields (`TIMER_DEADLINE ..= TIMER_HEIGHT`) of the keys `K` and the node
words of core `c` (addresses at the entry state `s0`). -/
def TW (st : machine.Store S) [L : LawfulStore st] (s0 : S) (c : U64) (K : U64 → Prop) (w : U64) : Prop :=
  (∃ z, K z ∧ ∃ k : U64, 3528 ≤ k.val ∧ k.val < 3576 ∧ w = core.num.U64.wrapping_add z k) ∨
    (∃ o : U64, o.val < 4288 ∧ w = L.nodeAt s0 c o)

/-- The fixed context: placement, keys are TCBs, the guard admits `TW`. -/
structure TC (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c : U64) (K : U64 → Prop)
    (R W : U64 → Prop) : Prop where
  tcbs : TcbPlaced T
  inT : ∀ z, K z → z ∈ T
  node : NodePlaced st T s0 c
  rd : ∀ w, TW st s0 c K w → R w
  wr : ∀ w, TW st s0 c K w → W w

/-- The walk invariant: the root word and the links of `Kr` are null or keys. -/
structure TI (st : machine.Store S) [L : LawfulStore st] (s0 : S) (c : U64) (K Kr : U64 → Prop) (s : S) :
    Prop where
  ksb : L.ksb s = L.ksb s0
  cpu : L.cpu s = L.cpu s0
  sub : ∀ z, Kr z → K z
  root : Kz K (L.mem s (L.nodeAt s0 c layout.node.TIMER_ROOT))
  lnk : ∀ z, Kr z → Kz K (L.mem s (tlA z)) ∧ Kz K (L.mem s (trA z)) ∧ Kz K (L.mem s (tpA z))

variable {s0 : S} {c : U64} {K Kr : U64 → Prop}

theorem TW.fld {z k : U64} (hz : K z) (h1 : 3528 ≤ k.val) (h2 : k.val < 3576) :
    TW st s0 c K (core.num.U64.wrapping_add z k) := Or.inl ⟨z, hz, k, h1, h2, rfl⟩

theorem TW.nd {s : S} {o : U64} (hI : TI st s0 c K Kr s) (ho : o.val < 4288) :
    TW st s0 c K (L.nodeAt s c o) := Or.inr ⟨o, ho, nodeAt_of_ksb hI.ksb c o⟩

theorem Kz.tz (C : TC st T s0 c K R W) {v : U64} (h : Kz K v) : Tz T v := h.imp_right (C.inT v)

theorem Kz.ne0 {v : U64} (h : Kz K v) (hn : v ≠ 0#u64) : K v := h.resolve_left hn

/-! ## Writes keep `TI` -/

theorem TI.wr_fld (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {z k v : U64} (hz : K z)
    (hk1 : 3528 ≤ k.val) (hk2 : k.val < 3576) (hk8 : k.val % 8 = 0)
    (hv : k.val = 3544 ∨ k.val = 3552 ∨ k.val = 3560 → Kz K v) :
    TI st s0 c K Kr (L.wr s (core.num.U64.wrapping_add z k) v) := by
  have hzT := C.inT z hz
  refine ⟨by simp [hI.ksb], by simp [hI.cpu], hI.sub, ?_, fun y hy => ?_⟩
  · rw [L.mem_wr_ne (tz_aligned C.tcbs (Tz.of_mem hzT) (by omega) hk8)
      (nodeAt_aligned C.node (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT]))
      (fun e => node_ne_tz C.tcbs C.node (by simp [layout.node.TIMER_ROOT]) (Tz.of_mem hzT) (by omega) e.symm)]
    exact hI.root
  · have hyT := C.inT y (hI.sub y hy)
    obtain ⟨a1, a2, a3⟩ := hI.lnk y hy
    have one : ∀ k' : U64, k'.val < 4096 → k'.val % 8 = 0 → (k'.val = 3544 ∨ k'.val = 3552 ∨ k'.val = 3560) →
        Kz K (L.mem s (core.num.U64.wrapping_add y k')) →
        Kz K (L.mem (L.wr s (core.num.U64.wrapping_add z k) v) (core.num.U64.wrapping_add y k')) := by
      intro k' h1 h2 h3 h4
      rw [trb_fld_wr C.tcbs hzT hyT (by omega) hk8 h1 h2]
      split
      · rename_i he; exact hv (by omega)
      · exact h4
    exact ⟨one 3544#u64 (by simp) (by simp) (by simp) a1, one 3552#u64 (by simp) (by simp) (by simp) a2,
      one 3560#u64 (by simp) (by simp) (by simp) a3⟩

theorem TI.wr_node (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {o v : U64} (ho : o.val < 4288)
    (ho8 : o.val % 8 = 0) (hv : o.val = layout.node.TIMER_ROOT.val → Kz K v) :
    TI st s0 c K Kr (L.wr s (L.nodeAt s0 c o) v) := by
  have hR : layout.node.TIMER_ROOT.val < 4288 := by simp [layout.node.TIMER_ROOT]
  refine ⟨by simp [hI.ksb], by simp [hI.cpu], hI.sub, ?_, fun y hy => ?_⟩
  · rw [L.mem_wr _ _ _ _ (nodeAt_aligned C.node ho ho8)
      (nodeAt_aligned C.node hR (by simp [layout.node.TIMER_ROOT]))]
    split
    · rename_i he
      have := congrArg UScalar.val he
      rw [nodeAt_val C.node ho, nodeAt_val C.node hR] at this
      exact hv (by omega)
    · exact hI.root
  · have hyT := C.inT y (hI.sub y hy)
    obtain ⟨a1, a2, a3⟩ := hI.lnk y hy
    have e : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 →
        L.mem (L.wr s (L.nodeAt s0 c o) v) (core.num.U64.wrapping_add y k) =
          L.mem s (core.num.U64.wrapping_add y k) := fun k h1 h2 =>
      L.mem_wr_ne (nodeAt_aligned C.node ho ho8) (tz_aligned C.tcbs (Tz.of_mem hyT) h1 h2)
        (node_ne_tz C.tcbs C.node ho (Tz.of_mem hyT) h1)
    exact ⟨by rw [tlA, e _ (by simp) (by simp)]; exact a1, by rw [trA, e _ (by simp) (by simp)]; exact a2,
      by rw [tpA, e _ (by simp) (by simp)]; exact a3⟩

/-- Adding a key whose links are set. -/
theorem TI.ext {s : S} (hI : TI st s0 c K Kr s) {t : U64} (ht : K t)
    (h : Kz K (L.mem s (tlA t)) ∧ Kz K (L.mem s (trA t)) ∧ Kz K (L.mem s (tpA t))) :
    TI st s0 c K (fun z => Kr z ∨ z = t) s :=
  ⟨hI.ksb, hI.cpu, fun z hz => hz.elim (hI.sub z) (fun e => e ▸ ht), hI.root,
    fun z hz => hz.elim (hI.lnk z) (fun e => e ▸ h)⟩

/-! ## Leaves -/

theorem is_null_eq {x : U64} {b : Bool} (h : obj.Tcb.is_null x = ok b) : b = decide (x = 0#u64) := by
  rw [eq_of_spec_fd (obj.Tcb.is_null.spec x)] at h; exact (ok_inj_ff h).symm

/-- A read of a link of `x ∈ Kr`. -/
theorem lnk_ge {M : machine.Store S} {x : U64} {f : machine.Store S → U64 → S → Result U64} {a : U64 → U64}
    (hg : f (guard st R W) x = f st x) (hv : ∀ s, f st x s ⦃ v => v = L.mem s (a x) ⦄) {s : S}
    (hk : Kz K (L.mem s (a x))) : GE (f (guard st R W) x s) (f st x s) (Kz K) := by
  rw [hg]
  exact ⟨rfl, fun v e => by rw [eq_of_spec_fd (hv s)] at e; exact (ok_inj_ff e) ▸ hk⟩

theorem ge_left (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x : U64} (hx : Kz Kr x) :
    GE (timer.left (guard st R W) s x) (timer.left st s x) (Kz K) := by
  unfold timer.left
  refine GE.bind (GE.refl _) fun b hb => ?_
  rw [is_null_eq hb]
  refine GE.ite (fun h => GE.ret (Or.inl (of_decide_eq_true h))) (fun h => ?_)
  have hxr : Kr x := hx.resolve_left fun e => h (decide_eq_true e)
  have hxk := hI.sub x hxr
  rw [PathObl.obj.Tcb.timer_left.guard x s (C.rd _ (TW.fld hxk (by simp) (by simp)))]
  refine GE.bind (GE.refl _) fun i hi => GE.ret ?_
  rw [eq_of_spec_fd (obj.Tcb.timer_left.val (L := L) s x)] at hi
  exact (ok_inj_ff hi) ▸ (hI.lnk x hxr).1

theorem ge_right (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x : U64} (hx : Kz Kr x) :
    GE (timer.right (guard st R W) s x) (timer.right st s x) (Kz K) := by
  unfold timer.right
  refine GE.bind (GE.refl _) fun b hb => ?_
  rw [is_null_eq hb]
  refine GE.ite (fun h => GE.ret (Or.inl (of_decide_eq_true h))) (fun h => ?_)
  have hxr : Kr x := hx.resolve_left fun e => h (decide_eq_true e)
  have hxk := hI.sub x hxr
  rw [PathObl.obj.Tcb.timer_right.guard x s (C.rd _ (TW.fld hxk (by simp) (by simp)))]
  refine GE.bind (GE.refl _) fun i hi => GE.ret ?_
  rw [eq_of_spec_fd (obj.Tcb.timer_right.val (L := L) s x)] at hi
  exact (ok_inj_ff hi) ▸ (hI.lnk x hxr).2.1

theorem ge_parent (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x : U64} (hx : Kz Kr x) :
    GE (timer.parent (guard st R W) s x) (timer.parent st s x) (Kz K) := by
  unfold timer.parent
  refine GE.bind (GE.refl _) fun b hb => ?_
  rw [is_null_eq hb]
  refine GE.ite (fun h => GE.ret (Or.inl (of_decide_eq_true h))) (fun h => ?_)
  have hxr : Kr x := hx.resolve_left fun e => h (decide_eq_true e)
  have hxk := hI.sub x hxr
  rw [PathObl.obj.Tcb.timer_parent.guard x s (C.rd _ (TW.fld hxk (by simp) (by simp)))]
  refine GE.bind (GE.refl _) fun i hi => GE.ret ?_
  rw [eq_of_spec_fd (obj.Tcb.timer_parent.val (L := L) s x)] at hi
  exact (ok_inj_ff hi) ▸ (hI.lnk x hxr).2.2

theorem ge_is_red (C : TC st T s0 c K R W) {s : S} (_hI : TI st s0 c K Kr s) {x : U64} (hx : Kz K x) :
    GE (timer.is_red (guard st R W) s x) (timer.is_red st s x) (fun _ => True) := by
  unfold timer.is_red
  refine GE.bind (GE.refl _) fun b hb => ?_
  rw [is_null_eq hb]
  refine GE.ite (fun _ => GE.ret trivial) (fun h => ?_)
  have hxk : K x := hx.resolve_left fun e => h (decide_eq_true e)
  rw [PathObl.obj.Tcb.timer_height.guard x s (C.rd _ (TW.fld hxk (by simp) (by simp)))]
  exact ⟨rfl, fun _ _ => trivial⟩

theorem ge_root (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) :
    GE (timer.root (guard st R W) s c) (timer.root st s c) (Kz K) := by
  unfold timer.root
  rw [PathObl.obj.node_get.guard s c _ (C.rd _ (TW.nd hI (by simp [layout.node.TIMER_ROOT])))]
  refine GE.bind (GE.refl _) fun i hi => GE.ret ?_
  rw [eq_of_spec_fd (obj.node_get.spec (L := L) s c _), nodeAt_of_ksb hI.ksb] at hi
  exact (ok_inj_ff hi) ▸ hI.root

theorem ge_node_get (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {o : U64} (ho : o.val < 4288) :
    GE (obj.node_get (guard st R W) s c o) (obj.node_get st s c o)
      (fun v => v = L.mem s (L.nodeAt s0 c o)) := by
  rw [PathObl.obj.node_get.guard s c _ (C.rd _ (TW.nd hI ho))]
  exact ⟨rfl, fun v e => by
    rw [eq_of_spec_fd (obj.node_get.spec (L := L) s c _), nodeAt_of_ksb hI.ksb] at e; exact (ok_inj_ff e).symm⟩

theorem ge_node_set (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {o v : U64} (ho : o.val < 4288)
    (ho8 : o.val % 8 = 0) (hv : o.val = layout.node.TIMER_ROOT.val → Kz K v) :
    GE (obj.node_set (guard st R W) s c o v) (obj.node_set st s c o v) (TI st s0 c K Kr) := by
  rw [PathObl.obj.node_set.guard s c _ _ (C.wr _ (TW.nd hI ho))]
  exact ⟨rfl, fun s' e => by
    rw [eq_of_spec_fd (obj.node_set.spec (L := L) s c _ _), nodeAt_of_ksb hI.ksb] at e
    exact (ok_inj_ff e) ▸ TI.wr_node C hI ho ho8 hv⟩

theorem ge_set_root (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {v : U64} (hv : Kz K v) :
    GE (timer.set_root (guard st R W) s c v) (timer.set_root st s c v) (TI st s0 c K Kr) := by
  unfold timer.set_root
  exact ge_node_set C hI (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT]) fun _ => hv

/-- A write of a timer field of `x ∈ K` (a link field only with a null or key value). -/
theorem fld_ge (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x k v : U64} (hx : K x)
    {f : machine.Store S → U64 → S → U64 → Result S}
    (hk1 : 3528 ≤ k.val) (hk2 : k.val < 3576) (hk8 : k.val % 8 = 0)
    (hg : f (guard st R W) x s v = f st x s v)
    (hw : f st x s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add x k) v ⦄)
    (hv : k.val = 3544 ∨ k.val = 3552 ∨ k.val = 3560 → Kz K v) :
    GE (f (guard st R W) x s v) (f st x s v) (TI st s0 c K Kr) := by
  rw [hg]
  exact ⟨rfl, fun s' e => by rw [eq_of_spec_fd hw] at e; exact (ok_inj_ff e) ▸ TI.wr_fld C hI hx hk1 hk2 hk8 hv⟩

theorem ge_set_left (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x v : U64} (hx : Kz K x)
    (hv : Kz K v) : GE (timer.set_left (guard st R W) s x v) (timer.set_left st s x v) (TI st s0 c K Kr) := by
  unfold timer.set_left
  refine GE.bind (GE.refl _) fun b hb => ?_
  rw [is_null_eq hb]
  refine GE.ite (fun _ => GE.ret hI) (fun h => ?_)
  have hxk : K x := hx.resolve_left fun e => h (decide_eq_true e)
  exact fld_ge C hI hxk (k := 3544#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_left.guard x s v (C.wr _ (TW.fld hxk (by simp) (by simp))))
    (obj.Tcb.set_timer_left.wr (L := L) s x v) fun _ => hv

theorem ge_set_right (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x v : U64} (hx : Kz K x)
    (hv : Kz K v) : GE (timer.set_right (guard st R W) s x v) (timer.set_right st s x v) (TI st s0 c K Kr) := by
  unfold timer.set_right
  refine GE.bind (GE.refl _) fun b hb => ?_
  rw [is_null_eq hb]
  refine GE.ite (fun _ => GE.ret hI) (fun h => ?_)
  have hxk : K x := hx.resolve_left fun e => h (decide_eq_true e)
  exact fld_ge C hI hxk (k := 3552#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_right.guard x s v (C.wr _ (TW.fld hxk (by simp) (by simp))))
    (obj.Tcb.set_timer_right.wr (L := L) s x v) fun _ => hv

theorem ge_set_parent (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x v : U64} (hx : Kz K x)
    (hv : Kz K v) : GE (timer.set_parent (guard st R W) s x v) (timer.set_parent st s x v) (TI st s0 c K Kr) := by
  unfold timer.set_parent
  refine GE.bind (GE.refl _) fun b hb => ?_
  rw [is_null_eq hb]
  refine GE.ite (fun _ => GE.ret hI) (fun h => ?_)
  have hxk : K x := hx.resolve_left fun e => h (decide_eq_true e)
  exact fld_ge C hI hxk (k := 3560#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_parent.guard x s v (C.wr _ (TW.fld hxk (by simp) (by simp))))
    (obj.Tcb.set_timer_parent.wr (L := L) s x v) fun _ => hv

theorem ge_set_red (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x : U64} {red : Bool}
    (hx : Kz K x) : GE (timer.set_red (guard st R W) s x red) (timer.set_red st s x red) (TI st s0 c K Kr) := by
  unfold timer.set_red
  refine GE.bind (GE.refl _) fun b hb => ?_
  rw [is_null_eq hb]
  refine GE.ite (fun _ => GE.ret hI) (fun h => ?_)
  have hxk : K x := hx.resolve_left fun e => h (decide_eq_true e)
  rw [PathObl.obj.Tcb.timer_height.guard x s (C.rd _ (TW.fld hxk (by simp) (by simp)))]
  refine GE.bind (GE.refl _) fun i _ => ?_
  refine GE.bind (GE.refl _) fun i1 _ => ?_
  refine GE.bind (GE.refl _) fun hh _ => ?_
  refine GE.ite (fun _ => ?_) (fun _ => ?_) <;> refine GE.bind (GE.refl _) fun i2 _ => ?_ <;>
    exact fld_ge C hI hxk (k := 3568#u64) (by simp) (by simp) (by simp)
      (PathObl.obj.Tcb.set_timer_height.guard x s i2 (C.wr _ (TW.fld hxk (by simp) (by simp))))
      (obj.Tcb.set_timer_height.wr (L := L) s x i2) (fun h => by simp at h)

/-- The leaf rules for the tree code, then the composition rules. Side conditions by assumption (or the
null handle). -/
macro "tg_side" : tactic => `(tactic| first | assumption | exact Or.inl rfl)
macro "tg_step" : tactic => `(tactic| with_reducible first
  | with_reducible apply GE.bind_assoc
  | with_reducible apply GE.bind_ok
  | with_reducible apply GE.bind_ite
  | with_reducible apply GE.uncurry
  | (refine GE.bind (ge_left (by assumption) (by assumption) (by tg_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_right (by assumption) (by assumption) (by tg_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_parent (by assumption) (by assumption) (by tg_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_is_red (by assumption) (by assumption) (by tg_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_root (by assumption) (by assumption)) (fun _ _ => ?_))
  | (refine GE.bind (ge_set_left (by assumption) (by assumption) (by tg_side) (by tg_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_set_right (by assumption) (by assumption) (by tg_side) (by tg_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_set_parent (by assumption) (by assumption) (by tg_side) (by tg_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_set_red (by assumption) (by assumption) (by tg_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_set_root (by assumption) (by assumption) (by tg_side)) (fun _ _ => ?_))
  | exact ge_set_left (by assumption) (by assumption) (by tg_side) (by tg_side)
  | exact ge_set_right (by assumption) (by assumption) (by tg_side) (by tg_side)
  | exact ge_set_parent (by assumption) (by assumption) (by tg_side) (by tg_side)
  | exact ge_set_red (by assumption) (by assumption) (by tg_side)
  | exact ge_set_root (by assumption) (by assumption) (by tg_side)
  | (with_reducible refine GE.ite (fun _ => ?_) (fun _ => ?_))
  | (with_reducible refine GE.ret ?_)
  | (with_reducible refine GE.bind (GE.refl _) (fun _ _ => ?_)))

theorem ge_replace_child (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K K s) {p old new : U64}
    (hp : Kz K p) (hn : Kz K new) :
    GE (timer.replace_child (guard st R W) s c p old new) (timer.replace_child st s c p old new)
      (TI st s0 c K K) := by
  unfold timer.replace_child
  repeat' tg_step

theorem ge_rotate_left (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K K s) {x : U64} (hx : Kz K x) :
    GE (timer.rotate_left (guard st R W) s c x) (timer.rotate_left st s c x) (TI st s0 c K K) := by
  unfold timer.rotate_left
  repeat' (first
    | (refine GE.bind (ge_replace_child (by assumption) (by assumption) (by tg_side) (by tg_side)) (fun _ _ => ?_))
    | tg_step)

theorem ge_rotate_right (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K K s) {x : U64} (hx : Kz K x) :
    GE (timer.rotate_right (guard st R W) s c x) (timer.rotate_right st s c x) (TI st s0 c K K) := by
  unfold timer.rotate_right
  repeat' (first
    | (refine GE.bind (ge_replace_child (by assumption) (by assumption) (by tg_side) (by tg_side)) (fun _ _ => ?_))
    | tg_step)

end

end Fl4Proofs.P2
