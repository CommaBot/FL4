/-
# P2 (line p3mc, gen 19): the timer tree code on a store that answers **only the target's** deadline writes

`TC` (P2/FootTimerGE) asks the store `gS` to answer a key's `TIMER_DEADLINE` write as `st` for **every** key of the
tree (`wd`). The tree code writes the deadline of the removed / inserted thread only (`timer::remove` /
`timer::insert`'s tail), which the proofs of `ge_rm_tail` / `ge_ht_dl` use at that thread alone. Here `TC` takes a
second key predicate `Kd`, and `wd` is asked only for the keys of `Kd`:

* `GED.TC … Kd` (the fields of `TC`, `wd` only for `Kd x`), and every `TC` lemma of `FootTimerGE`, `FootTimerGELoop`,
  `FootTimerGERem`, `FootTimerGEIns` re-proved over it with the same proof (copied; the lemmas not about `TC` are
  used from `Fl4Proofs.P2`), with `ge_rm_tail` / `ge_remove` / `ge_ht_dl` / `ge_insert` asking `Kd` of the removed /
  inserted thread. The tactic macros are copied as `tgd_*`.

Used by P2/FootTimerSetAccD (`set_timer_accGD`: the accepted st run with the deadline write premise at the target
only). No premise. No existing statement changed.
-/
import Fl4Proofs.P2.FootTimerGEIns
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.GED
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2
open Fl4Proofs.P2.PathObl (guard guard_read GRd GWr)
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read GRd GWr)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {R W : U64 → Prop}
variable {gS : machine.Store S} [GRd gS st R] [GWr gS st W]

/-- The fixed context: placement, keys are TCBs, the store `gS` answers the tree words as `st`: reads of
`TW` and writes of `TWl` (`GRd` / `GWr` sets), and writes of a key's height (`wh`) / deadline (`wd`) under
the conditions the tree code meets there (the core bits of an armed key's height stay `c`; a deadline is
written only for a thread homed on `c` whose height names `c` while it is armed). -/
structure TC (st : machine.Store S) [L : LawfulStore st] (gS : machine.Store S) (T : Set U64) (s0 : S) (c : U64)
    (K : U64 → Prop) (R W : U64 → Prop) (Kd : U64 → Prop) : Prop where
  tcbs : TcbPlaced T
  inT : ∀ z, K z → z ∈ T
  node : NodePlaced st T s0 c
  rd : ∀ w, TW st s0 c K w → R w
  wr : ∀ w, TWl st s0 c K w → W w
  wh : ∀ s x v, K x → (L.mem s (tdA x) ≠ 0#u64 → (L.mem s (thA x)).val >>> 8 = c.val ∧ v.val >>> 8 = c.val) →
    gS.write s (thA x) v = st.write s (thA x) v
  wd : ∀ s x v, K x → Kd x → L.mem s (affA x) = c → L.mem s0 (affA x) = c →
    (L.mem s (tdA x) ≠ 0#u64 ∨ v ≠ 0#u64 → (L.mem s (thA x)).val >>> 8 = c.val) →
    gS.write s (tdA x) v = st.write s (tdA x) v

variable {s0 : S} {c : U64} {K Kr : U64 → Prop} {Kd : U64 → Prop}

theorem Kz.tz (C : TC st gS T s0 c K R W Kd) {v : U64} (h : Kz K v) : Tz T v := h.imp_right (C.inT v)

/-! ## Writes keep `TI` -/

theorem TI.wr_fld (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {z k v : U64} (hz : K z)
    (hk1 : 3528 ≤ k.val) (hk2 : k.val < 3576) (hk8 : k.val % 8 = 0)
    (hv : k.val = 3544 ∨ k.val = 3552 ∨ k.val = 3560 → Kz K v)
    (hd : k.val = 3528 → v ≠ 0#u64 → (L.mem s (thA z)).val >>> 8 = c.val)
    (hh : k.val = 3568 → L.mem s (tdA z) ≠ 0#u64 → v.val >>> 8 = c.val) :
    TI st s0 c K Kr (L.wr s (core.num.U64.wrapping_add z k) v) := by
  have hzT := C.inT z hz
  have fw : ∀ y, y ∈ T → ∀ k' : U64, k'.val < 4096 → k'.val % 8 = 0 →
      L.mem (L.wr s (core.num.U64.wrapping_add z k) v) (core.num.U64.wrapping_add y k') =
        if y = z ∧ k'.val = k.val then v else L.mem s (core.num.U64.wrapping_add y k') :=
    fun y hy k' h1 h2 => trb_fld_wr C.tcbs hzT hy (by omega) hk8 h1 h2
  refine ⟨by simp [hI.ksb], by simp [hI.cpu], hI.sub, ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
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
  · have hyT := C.inT y hy
    have e1 : L.mem (L.wr s (core.num.U64.wrapping_add z k) v) (tdA y) =
        if y = z ∧ (3528#u64 : U64).val = k.val then v else L.mem s (tdA y) := fw y hyT 3528#u64 (by simp) (by simp)
    have e2 : L.mem (L.wr s (core.num.U64.wrapping_add z k) v) (thA y) =
        if y = z ∧ (3568#u64 : U64).val = k.val then v else L.mem s (thA y) := fw y hyT 3568#u64 (by simp) (by simp)
    rw [e1, e2]
    intro hne
    by_cases hyz : y = z
    · by_cases k1 : (3528#u64 : U64).val = k.val
      · rw [if_pos ⟨hyz, k1⟩] at hne
        have k1' : k.val = 3528 := by simp at k1; omega
        rw [if_neg (fun h => by have := h.2; simp at this; omega), hyz]
        exact hd k1' hne
      · rw [if_neg (fun h => k1 h.2)] at hne
        by_cases k2 : (3568#u64 : U64).val = k.val
        · have k2' : k.val = 3568 := by simp at k2; omega
          rw [if_pos ⟨hyz, k2⟩]
          rw [hyz] at hne
          exact hh k2' hne
        · rw [if_neg (fun h => k2 h.2)]; exact hI.hj y hy hne
    · rw [if_neg (fun h => hyz h.1)] at hne
      rw [if_neg (fun h => hyz h.1)]
      exact hI.hj y hy hne
  · have e : L.mem (L.wr s (core.num.U64.wrapping_add z k) v) (affA y) =
        if y = z ∧ (3520#u64 : U64).val = k.val then v else L.mem s (affA y) :=
      fw y (C.inT y hy) 3520#u64 (by simp) (by simp)
    rw [e, if_neg (fun h => by have := h.2; simp at this; omega)]
    exact hI.af y hy

theorem TI.wr_node (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {o v : U64} (ho : o.val < 4288)
    (ho8 : o.val % 8 = 0) (hv : o.val = layout.node.TIMER_ROOT.val → Kz K v) :
    TI st s0 c K Kr (L.wr s (L.nodeAt s0 c o) v) := by
  have hR : layout.node.TIMER_ROOT.val < 4288 := by simp [layout.node.TIMER_ROOT]
  have e : ∀ y, y ∈ T → ∀ k : U64, k.val < 4096 → k.val % 8 = 0 →
      L.mem (L.wr s (L.nodeAt s0 c o) v) (core.num.U64.wrapping_add y k) =
        L.mem s (core.num.U64.wrapping_add y k) := fun y hyT k h1 h2 =>
    L.mem_wr_ne (nodeAt_aligned C.node ho ho8) (tz_aligned C.tcbs (Tz.of_mem hyT) h1 h2)
      (node_ne_tz C.tcbs C.node ho (Tz.of_mem hyT) h1)
  refine ⟨by simp [hI.ksb], by simp [hI.cpu], hI.sub, ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
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
    exact ⟨by rw [tlA, e y hyT _ (by simp) (by simp)]; exact a1, by rw [trA, e y hyT _ (by simp) (by simp)]; exact a2,
      by rw [tpA, e y hyT _ (by simp) (by simp)]; exact a3⟩
  · have hyT := C.inT y hy
    rw [tdA, thA, e y hyT _ (by simp) (by simp), e y hyT _ (by simp) (by simp)]
    exact hI.hj y hy
  · rw [affA, e y (C.inT y hy) _ (by simp) (by simp)]
    exact hI.af y hy

/-! ## Leaves -/

theorem ge_left (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {x : U64} (hx : Kz Kr x) :
    GE (timer.left gS s x) (timer.left st s x) (Kz K) := by
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

theorem ge_right (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {x : U64} (hx : Kz Kr x) :
    GE (timer.right gS s x) (timer.right st s x) (Kz K) := by
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

theorem ge_parent (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {x : U64} (hx : Kz Kr x) :
    GE (timer.parent gS s x) (timer.parent st s x) (Kz K) := by
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

theorem ge_is_red (C : TC st gS T s0 c K R W Kd) {s : S} (_hI : TI st s0 c K Kr s) {x : U64} (hx : Kz K x) :
    GE (timer.is_red gS s x) (timer.is_red st s x) (fun _ => True) := by
  unfold timer.is_red
  refine GE.bind (GE.refl _) fun b hb => ?_
  rw [is_null_eq hb]
  refine GE.ite (fun _ => GE.ret trivial) (fun h => ?_)
  have hxk : K x := hx.resolve_left fun e => h (decide_eq_true e)
  rw [PathObl.obj.Tcb.timer_height.guard x s (C.rd _ (TW.fld hxk (by simp) (by simp)))]
  exact ⟨rfl, fun _ _ => trivial⟩

theorem ge_root (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) :
    GE (timer.root gS s c) (timer.root st s c) (Kz K) := by
  unfold timer.root
  rw [PathObl.obj.node_get.guard s c _ (C.rd _ (TW.nd hI (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])))]
  refine GE.bind (GE.refl _) fun i hi => GE.ret ?_
  rw [eq_of_spec_fd (obj.node_get.spec (L := L) s c _), nodeAt_of_ksb hI.ksb] at hi
  exact (ok_inj_ff hi) ▸ hI.root

theorem ge_node_get (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {o : U64} (ho : o.val < 4288)
    (ho8 : o.val % 8 = 0) :
    GE (obj.node_get gS s c o) (obj.node_get st s c o)
      (fun v => v = L.mem s (L.nodeAt s0 c o)) := by
  rw [PathObl.obj.node_get.guard s c _ (C.rd _ (TW.nd hI ho ho8))]
  exact ⟨rfl, fun v e => by
    rw [eq_of_spec_fd (obj.node_get.spec (L := L) s c _), nodeAt_of_ksb hI.ksb] at e; exact (ok_inj_ff e).symm⟩

theorem ge_node_set (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {o v : U64} (ho : o.val < 4288)
    (ho8 : o.val % 8 = 0) (hv : o.val = layout.node.TIMER_ROOT.val → Kz K v) :
    GE (obj.node_set gS s c o v) (obj.node_set st s c o v) (TI st s0 c K Kr) := by
  rw [PathObl.obj.node_set.guard s c _ _ (C.wr _ (TWl.nd hI ho ho8))]
  exact ⟨rfl, fun s' e => by
    rw [eq_of_spec_fd (obj.node_set.spec (L := L) s c _ _), nodeAt_of_ksb hI.ksb] at e
    exact (ok_inj_ff e) ▸ TI.wr_node C hI ho ho8 hv⟩

theorem ge_set_root (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {v : U64} (hv : Kz K v) :
    GE (timer.set_root gS s c v) (timer.set_root st s c v) (TI st s0 c K Kr) := by
  unfold timer.set_root
  exact ge_node_set C hI (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT]) fun _ => hv

/-- A write of a timer field of `x ∈ K` (a link field only with a null or key value). -/
theorem fld_ge (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {x k v : U64} (hx : K x)
    {f : machine.Store S → U64 → S → U64 → Result S}
    (hk1 : 3528 ≤ k.val) (hk2 : k.val < 3576) (hk8 : k.val % 8 = 0)
    (hg : f gS x s v = f st x s v)
    (hw : f st x s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add x k) v ⦄)
    (hv : k.val = 3544 ∨ k.val = 3552 ∨ k.val = 3560 → Kz K v)
    (hd : k.val = 3528 → v ≠ 0#u64 → (L.mem s (thA x)).val >>> 8 = c.val)
    (hh : k.val = 3568 → L.mem s (tdA x) ≠ 0#u64 → v.val >>> 8 = c.val) :
    GE (f gS x s v) (f st x s v) (TI st s0 c K Kr) := by
  rw [hg]
  exact ⟨rfl, fun s' e => by
    rw [eq_of_spec_fd hw] at e; exact (ok_inj_ff e) ▸ TI.wr_fld C hI hx hk1 hk2 hk8 hv hd hh⟩

/-- A timer-field write of a key, with its real effect. -/
theorem fld_ge' (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {x k v : U64}
    (hx : K x) {f : machine.Store S → U64 → S → U64 → Result S}
    (hk1 : 3528 ≤ k.val) (hk2 : k.val < 3576) (hk8 : k.val % 8 = 0)
    (hg : f gS x s v = f st x s v)
    (hw : f st x s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add x k) v ⦄)
    (hv : k.val = 3544 ∨ k.val = 3552 ∨ k.val = 3560 → Kz K v)
    (hd : k.val = 3528 → v ≠ 0#u64 → (L.mem s (thA x)).val >>> 8 = c.val)
    (hh : k.val = 3568 → L.mem s (tdA x) ≠ 0#u64 → v.val >>> 8 = c.val) :
    GE (f gS x s v) (f st x s v)
      (fun s' => TI st s0 c K Kr s' ∧ s' = L.wr s (core.num.U64.wrapping_add x k) v) := by
  rw [hg]
  refine ⟨rfl, fun s' e => ?_⟩
  rw [eq_of_spec_fd hw] at e
  have e' := ok_inj_ff e
  subst e'
  exact ⟨TI.wr_fld C hI hx hk1 hk2 hk8 hv hd hh, rfl⟩

/-- Core `c`'s node fits: `c < 2 ^ 56`. -/
theorem TC.cs (C : TC st gS T s0 c K R W Kd) : c.val < 2 ^ 56 := by
  have := C.node.fits; simp only [LawfulStore.nodeBase] at this; omega

theorem ge_set_left (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {x v : U64} (hx : Kz K x)
    (hv : Kz K v) : GE (timer.set_left gS s x v) (timer.set_left st s x v) (TI st s0 c K Kr) := by
  unfold timer.set_left
  refine GE.bind (GE.refl _) fun b hb => ?_
  rw [is_null_eq hb]
  refine GE.ite (fun _ => GE.ret hI) (fun h => ?_)
  have hxk : K x := hx.resolve_left fun e => h (decide_eq_true e)
  exact fld_ge C hI hxk (k := 3544#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_left.guard x s v (C.wr _ (TWl.fld hxk (by simp) (by simp))))
    (obj.Tcb.set_timer_left.wr (L := L) s x v) (fun _ => hv) (fun h => by simp at h) (fun h => by simp at h)

theorem ge_set_right (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {x v : U64} (hx : Kz K x)
    (hv : Kz K v) : GE (timer.set_right gS s x v) (timer.set_right st s x v) (TI st s0 c K Kr) := by
  unfold timer.set_right
  refine GE.bind (GE.refl _) fun b hb => ?_
  rw [is_null_eq hb]
  refine GE.ite (fun _ => GE.ret hI) (fun h => ?_)
  have hxk : K x := hx.resolve_left fun e => h (decide_eq_true e)
  exact fld_ge C hI hxk (k := 3552#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_right.guard x s v (C.wr _ (TWl.fld hxk (by simp) (by simp))))
    (obj.Tcb.set_timer_right.wr (L := L) s x v) (fun _ => hv) (fun h => by simp at h) (fun h => by simp at h)

theorem ge_set_parent (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {x v : U64} (hx : Kz K x)
    (hv : Kz K v) : GE (timer.set_parent gS s x v) (timer.set_parent st s x v) (TI st s0 c K Kr) := by
  unfold timer.set_parent
  refine GE.bind (GE.refl _) fun b hb => ?_
  rw [is_null_eq hb]
  refine GE.ite (fun _ => GE.ret hI) (fun h => ?_)
  have hxk : K x := hx.resolve_left fun e => h (decide_eq_true e)
  exact fld_ge C hI hxk (k := 3560#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_parent.guard x s v (C.wr _ (TWl.fld hxk (by simp) (by simp))))
    (obj.Tcb.set_timer_parent.wr (L := L) s x v) (fun _ => hv) (fun h => by simp at h) (fun h => by simp at h)

theorem ge_set_red (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {x : U64} {red : Bool}
    (hx : Kz K x) : GE (timer.set_red gS s x red) (timer.set_red st s x red) (TI st s0 c K Kr) := by
  unfold timer.set_red timer.RED
  refine GE.bind (GE.refl _) fun b hb => ?_
  rw [is_null_eq hb]
  refine GE.ite (fun _ => GE.ret hI) (fun h => ?_)
  have hxk : K x := hx.resolve_left fun e => h (decide_eq_true e)
  rw [PathObl.obj.Tcb.timer_height.guard x s (C.rd _ (TW.fld hxk (by simp) (by simp))),
    eq_of_spec_fd (obj.Tcb.timer_height.val (L := L) s x)]
  simp only [lift, bind_ok]
  refine GE.ite (fun _ => ?_) (fun _ => ?_) <;>
    exact fld_ge C hI hxk (k := 3568#u64) (by simp) (by simp) (by simp)
      (sth_of (C.wh s x _ hxk fun hd =>
        ⟨hI.hj x hxk hd, (shr8_red _ _ (by simp)).trans (hI.hj x hxk hd)⟩))
      (obj.Tcb.set_timer_height.wr (L := L) s x _) (fun h => by simp at h) (fun h => by simp at h)
      (fun _ hd => (shr8_red _ _ (by simp)).trans (hI.hj x hxk hd))

/-- The leaf rules for the tree code, then the composition rules. Side conditions by assumption (or the
null handle). -/
macro "tgd_side" : tactic => `(tactic| first | assumption | exact Or.inl rfl | exact Or.inr (by assumption))
macro "tgd_step" : tactic => `(tactic| with_reducible first
  | with_reducible apply GE.bind_assoc
  | with_reducible apply GE.bind_ok
  | with_reducible apply GE.bind_ite
  | with_reducible apply GE.uncurry
  | with_reducible apply GE.bind_uncurry
  | (refine GE.bind (ge_left (by assumption) (by assumption) (by tgd_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_right (by assumption) (by assumption) (by tgd_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_parent (by assumption) (by assumption) (by tgd_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_is_red (by assumption) (by assumption) (by tgd_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_root (by assumption) (by assumption)) (fun _ _ => ?_))
  | (refine GE.bind (ge_set_left (by assumption) (by assumption) (by tgd_side) (by tgd_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_set_right (by assumption) (by assumption) (by tgd_side) (by tgd_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_set_parent (by assumption) (by assumption) (by tgd_side) (by tgd_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_set_red (by assumption) (by assumption) (by tgd_side)) (fun _ _ => ?_))
  | (refine GE.bind (ge_set_root (by assumption) (by assumption) (by tgd_side)) (fun _ _ => ?_))
  | exact ge_set_left (by assumption) (by assumption) (by tgd_side) (by tgd_side)
  | exact ge_set_right (by assumption) (by assumption) (by tgd_side) (by tgd_side)
  | exact ge_set_parent (by assumption) (by assumption) (by tgd_side) (by tgd_side)
  | exact ge_set_red (by assumption) (by assumption) (by tgd_side)
  | exact ge_set_root (by assumption) (by assumption) (by tgd_side)
  | (with_reducible refine GE.ite (fun _ => ?_) (fun _ => ?_))
  | (with_reducible refine GE.ret ?_)
  | (with_reducible refine GE.bind (GE.refl _) (fun _ _ => ?_)))

theorem ge_replace_child (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K K s) {p old new : U64}
    (hp : Kz K p) (hn : Kz K new) :
    GE (timer.replace_child gS s c p old new) (timer.replace_child st s c p old new)
      (TI st s0 c K K) := by
  unfold timer.replace_child
  repeat' tgd_step

theorem ge_rotate_left (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K K s) {x : U64} (hx : Kz K x) :
    GE (timer.rotate_left gS s c x) (timer.rotate_left st s c x) (TI st s0 c K K) := by
  unfold timer.rotate_left
  repeat' (first
    | (refine GE.bind (ge_replace_child (by assumption) (by assumption) (by tgd_side) (by tgd_side)) (fun _ _ => ?_))
    | tgd_step)

theorem ge_rotate_right (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K K s) {x : U64} (hx : Kz K x) :
    GE (timer.rotate_right gS s c x) (timer.rotate_right st s c x) (TI st s0 c K K) := by
  unfold timer.rotate_right
  repeat' (first
    | (refine GE.bind (ge_replace_child (by assumption) (by assumption) (by tgd_side) (by tgd_side)) (fun _ _ => ?_))
    | tgd_step)

end


open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read GRd GWr)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {R W : U64 → Prop}
variable {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
variable {s0 : S} {c : U64} {K : U64 → Prop} {Kd : U64 → Prop}

/-- With the rotations. -/
macro "tgd_step2" : tactic => `(tactic| first
  | (with_reducible refine GE.bind (ge_rotate_left (by assumption) (by assumption) (by tgd_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_rotate_right (by assumption) (by assumption) (by tgd_side)) (fun _ _ => ?_))
  | (with_reducible exact ge_rotate_left (by assumption) (by assumption) (by tgd_side))
  | (with_reducible exact ge_rotate_right (by assumption) (by assumption) (by tgd_side))
  | tgd_step)

/-- Closing a loop body's postcondition. -/
macro "tgd_fin" : tactic => `(tactic| (
  (try unfold LoopPost)
  (try dsimp only)
  repeat' (apply And.intro)
  all_goals first
    | assumption
    | exact Or.inl rfl
    | exact ge_sub1_lt (by assumption) (by assumption)
    | exact ge_sub1_lt' (by assumption) (by assumption)
    | trivial))

/-! ## `remove_fixup` -/

theorem ge_remove_fixup_body (C : TC st gS T s0 c K R W Kd) {s : S} {x p fuel : U64} (hI : TI st s0 c K K s)
    (hx : Kz K x) (hp : Kz K p) :
    GE (timer.remove_fixup_loop.body gS c s x p fuel) (timer.remove_fixup_loop.body st c s x p fuel)
      (LoopPost (fun y : S × U64 × U64 × U64 => TI st s0 c K K y.1 ∧ Kz K y.2.1 ∧ Kz K y.2.2.1)
        (fun y => y.2.2.2.val) (fun z : S × U64 => TI st s0 c K K z.1 ∧ Kz K z.2) (s, x, p, fuel)) := by
  unfold timer.remove_fixup_loop.body
  repeat' tgd_step2
  all_goals tgd_fin

theorem ge_remove_fixup_loop (C : TC st gS T s0 c K R W Kd) {s : S} {x p fuel : U64} (hI : TI st s0 c K K s)
    (hx : Kz K x) (hp : Kz K p) :
    GE (timer.remove_fixup_loop gS s c x p fuel) (timer.remove_fixup_loop st s c x p fuel)
      (fun z : S × U64 => TI st s0 c K K z.1 ∧ Kz K z.2) := by
  unfold timer.remove_fixup_loop
  refine GE.loop (fun y : S × U64 × U64 × U64 => TI st s0 c K K y.1 ∧ Kz K y.2.1 ∧ Kz K y.2.2.1)
    (fun y => y.2.2.2.val) (fun y hy => ?_) (s, x, p, fuel) ⟨hI, hx, hp⟩
  obtain ⟨s1, x1, p1, f1⟩ := y
  exact ge_remove_fixup_body C hy.1 hy.2.1 hy.2.2

theorem ge_remove_fixup (C : TC st gS T s0 c K R W Kd) {s : S} {x p : U64} (hI : TI st s0 c K K s)
    (hx : Kz K x) (hp : Kz K p) :
    GE (timer.remove_fixup gS s c x p) (timer.remove_fixup st s c x p) (TI st s0 c K K) := by
  unfold timer.remove_fixup
  refine GE.bind (ge_remove_fixup_loop C hI hx hp) fun z hz => ?_
  obtain ⟨s1, x1⟩ := z
  obtain ⟨h1, h2⟩ := hz
  apply GE.uncurry
  dsimp only at h1 h2
  repeat' tgd_step
  all_goals tgd_fin

/-! ## `insert_fixup` -/

theorem ge_insert_fixup_body (C : TC st gS T s0 c K R W Kd) {s : S} {z fuel : U64} (hI : TI st s0 c K K s)
    (hz : Kz K z) :
    GE (timer.insert_fixup_loop.body gS c s z fuel) (timer.insert_fixup_loop.body st c s z fuel)
      (LoopPost (fun y : S × U64 × U64 => TI st s0 c K K y.1 ∧ Kz K y.2.1) (fun y => y.2.2.val)
        (TI st s0 c K K) (s, z, fuel)) := by
  unfold timer.insert_fixup_loop.body
  repeat' tgd_step2
  all_goals tgd_fin

theorem ge_insert_fixup (C : TC st gS T s0 c K R W Kd) {s : S} {z : U64} (hI : TI st s0 c K K s) (hz : Kz K z) :
    GE (timer.insert_fixup gS s c z) (timer.insert_fixup st s c z) (TI st s0 c K K) := by
  unfold timer.insert_fixup timer.insert_fixup_loop
  refine GE.bind (GE.loop (Q := TI st s0 c K K) (fun y : S × U64 × U64 => TI st s0 c K K y.1 ∧ Kz K y.2.1)
    (fun y => y.2.2.val) (fun y hy => ?_) (s, z, 128#u64) ⟨hI, hz⟩) fun s1 h1 => ?_
  · obtain ⟨s1, z1, f1⟩ := y
    exact ge_insert_fixup_body C hy.1 hy.2
  · repeat' tgd_step
    all_goals tgd_fin

/-! ## `remove`'s successor searches -/

theorem ge_remove_loop0 (C : TC st gS T s0 c K R W Kd) {s : S} {y fuel : U64} (hI : TI st s0 c K K s) (hy : Kz K y) :
    GE (timer.remove_loop0 gS s y fuel) (timer.remove_loop0 st s y fuel) (Kz K) := by
  unfold timer.remove_loop0
  refine GE.loop (fun y : U64 × U64 => Kz K y.1) (fun y => y.2.val) (fun y hy => ?_) (y, fuel) hy
  obtain ⟨y1, f1⟩ := y
  show GE (timer.remove_loop0.body gS s y1 f1) (timer.remove_loop0.body st s y1 f1) _
  unfold timer.remove_loop0.body
  repeat' tgd_step
  all_goals tgd_fin

theorem ge_remove_loop1 (C : TC st gS T s0 c K R W Kd) {s : S} {y fuel : U64} (hI : TI st s0 c K K s) (hy : Kz K y) :
    GE (timer.remove_loop1 gS s y fuel) (timer.remove_loop1 st s y fuel) (Kz K) := by
  unfold timer.remove_loop1
  refine GE.loop (fun y : U64 × U64 => Kz K y.1) (fun y => y.2.val) (fun y hy => ?_) (y, fuel) hy
  obtain ⟨y1, f1⟩ := y
  show GE (timer.remove_loop1.body gS s y1 f1) (timer.remove_loop1.body st s y1 f1) _
  unfold timer.remove_loop1.body
  repeat' tgd_step
  all_goals tgd_fin

theorem ge_remove_loop2 (C : TC st gS T s0 c K R W Kd) {s : S} {y fuel : U64} (hI : TI st s0 c K K s) (hy : Kz K y) :
    GE (timer.remove_loop2 gS s y fuel) (timer.remove_loop2 st s y fuel) (Kz K) := by
  unfold timer.remove_loop2
  refine GE.loop (fun y : U64 × U64 => Kz K y.1) (fun y => y.2.val) (fun y hy => ?_) (y, fuel) hy
  obtain ⟨y1, f1⟩ := y
  show GE (timer.remove_loop2.body gS s y1 f1) (timer.remove_loop2.body st s y1 f1) _
  unfold timer.remove_loop2.body
  repeat' tgd_step
  all_goals tgd_fin

theorem ge_remove_loop3 (C : TC st gS T s0 c K R W Kd) {s : S} {y fuel : U64} (hI : TI st s0 c K K s) (hy : Kz K y) :
    GE (timer.remove_loop3 gS s y fuel) (timer.remove_loop3 st s y fuel) (Kz K) := by
  unfold timer.remove_loop3
  refine GE.loop (fun y : U64 × U64 => Kz K y.1) (fun y => y.2.val) (fun y hy => ?_) (y, fuel) hy
  obtain ⟨y1, f1⟩ := y
  show GE (timer.remove_loop3.body gS s y1 f1) (timer.remove_loop3.body st s y1 f1) _
  unfold timer.remove_loop3.body
  repeat' tgd_step
  all_goals tgd_fin

/-! ## `insert`'s descent -/

theorem ge_td (C : TC st gS T s0 c K R W Kd) {s : S} {x : U64} (hx : K x) :
    GE (obj.Tcb.timer_deadline gS x s) (obj.Tcb.timer_deadline st x s) (fun _ => True) :=
  ⟨PathObl.obj.Tcb.timer_deadline.guard x s (C.rd _ (TW.fld hx (by simp) (by simp))), fun _ _ => trivial⟩

theorem ge_insert_loop (C : TC st gS T s0 c K R W Kd) {s : S} {d p cur : U64} {gl fi : Bool} {fuel : U64}
    (hI : TI st s0 c K K s) (hp : Kz K p) (hc : Kz K cur) :
    GE (timer.insert_loop gS s d p cur gl fi fuel) (timer.insert_loop st s d p cur gl fi fuel)
      (fun z : U64 × Bool × Bool => Kz K z.1) := by
  unfold timer.insert_loop
  refine GE.loop (fun y : U64 × U64 × Bool × Bool × U64 => Kz K y.1 ∧ Kz K y.2.1) (fun y => y.2.2.2.2.val)
    (fun y hy => ?_) (p, cur, gl, fi, fuel) ⟨hp, hc⟩
  obtain ⟨p1, c1, g1, f1, n1⟩ := y
  obtain ⟨hp1, hc1⟩ := hy
  show GE (timer.insert_loop.body gS s d p1 c1 g1 f1 n1) (timer.insert_loop.body st s d p1 c1 g1 f1 n1) _
  unfold timer.insert_loop.body
  repeat' (first
    | (with_reducible refine GE.bind (ge_td C (kz_of_null (by assumption) (by assumption) (by assumption))) (fun _ _ => ?_))
    | tgd_step)
  all_goals tgd_fin

end


open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read GRd GWr)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {R W : U64 → Prop}
variable {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
variable {s0 : S} {c : U64} {K : U64 → Prop} {Kd : U64 → Prop}

theorem ge_td' (C : TC st gS T s0 c K R W Kd) {s : S} {x : U64} (hx : K x) :
    GE (obj.Tcb.timer_deadline gS x s) (obj.Tcb.timer_deadline st x s)
      (fun v => obj.Tcb.timer_deadline st x s = ok v) :=
  ⟨PathObl.obj.Tcb.timer_deadline.guard x s (C.rd _ (TW.fld hx (by simp) (by simp))), fun _ e => e⟩

theorem ge_core_of (C : TC st gS T s0 c K R W Kd) {s : S} {t : U64} (ht : K t) (h : timer.core_of st s t = ok c) :
    GE (timer.core_of gS s t) (timer.core_of st s t) (fun v => v = c) := by
  have e : timer.core_of gS s t = timer.core_of st s t := by
    unfold timer.core_of
    rw [PathObl.obj.Tcb.timer_height.guard t s (C.rd _ (TW.fld ht (by simp) (by simp)))]
  rw [e]
  exact ⟨rfl, fun v hv => by rw [h] at hv; exact (ok_inj_ff hv).symm⟩

theorem ge_get_min (C : TC st gS T s0 c K R W Kd) {s : S} {Kr : U64 → Prop} (hI : TI st s0 c K Kr s) :
    GE (obj.node_get gS s c layout.node.TIMER_MIN) (obj.node_get st s c layout.node.TIMER_MIN)
      (fun _ => True) :=
  GE.mono (ge_node_get C hI (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])) fun _ _ => trivial

theorem ge_set_min (C : TC st gS T s0 c K R W Kd) {s : S} {Kr : U64 → Prop} (hI : TI st s0 c K Kr s) {v : U64} :
    GE (obj.node_set gS s c layout.node.TIMER_MIN v) (obj.node_set st s c layout.node.TIMER_MIN v)
      (TI st s0 c K Kr) :=
  ge_node_set C hI (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
    (fun h => by simp [layout.node.TIMER_MIN, layout.node.TIMER_ROOT] at h)

/-- **`remove`'s tail**: the deadline zeroed (the key homed on `c`, its height naming `c` while armed), then
the height (the key disarmed by then). -/
theorem ge_rm_tail (C : TC st gS T s0 c K R W Kd) {s : S} {Kr : U64 → Prop} (hI : TI st s0 c K Kr s) {x : U64}
    (hx : K x) (hxd : Kd x) (ha : L.mem s0 (affA x) = c) :
    GE (Std.bind (obj.Tcb.set_timer_deadline gS x s 0#u64) fun s8 => obj.Tcb.set_timer_height gS x s8 0#u64)
      (Std.bind (obj.Tcb.set_timer_deadline st x s 0#u64) fun s8 => obj.Tcb.set_timer_height st x s8 0#u64)
      (fun s' => TI st s0 c K Kr s' ∧ L.mem s' (tdA x) = 0#u64) := by
  have hxT := C.inT x hx
  have aD : Aligned (tdA x) := field_aligned (C.tcbs x hxT) (by simp) (by simp)
  have aH : Aligned (thA x) := field_aligned (C.tcbs x hxT) (by simp) (by simp)
  have nDH : tdA x ≠ thA x := tcb_word_ne (C.tcbs x hxT) (C.tcbs x hxT) (by simp) (by simp) (fun _ => by simp)
  have wD := C.wd s x 0#u64 hx hxd (by rw [hI.af x hx]; exact ha) ha
    (fun h => h.elim (fun hd => hI.hj x hx hd) (fun h => absurd rfl h))
  refine GE.bind (fld_ge' C hI hx (k := 3528#u64) (by simp) (by simp) (by simp) (std_of wD)
    (obj.Tcb.set_timer_deadline.wr (L := L) s x _) (fun h => by simp at h) (fun _ h => absurd rfl h)
    (fun h => by simp at h)) fun s8 h8 => ?_
  obtain ⟨h8, e8⟩ := h8
  have d8 : L.mem s8 (tdA x) = 0#u64 := by rw [e8]; exact L.mem_wr_same aD
  have wH := C.wh s8 x 0#u64 hx (fun hd => absurd d8 hd)
  refine GE.mono (fld_ge' C h8 hx (k := 3568#u64) (by simp) (by simp) (by simp) (sth_of wH)
    (obj.Tcb.set_timer_height.wr (L := L) s8 x _) (fun h => by simp at h) (fun h => by simp at h)
    (fun _ hd => absurd d8 hd)) fun s' h' => ⟨h'.1, ?_⟩
  rw [h'.2]
  exact (mem_wr_ne' aH aD (Ne.symm nDH)).trans d8

/-- With `remove`'s callees. -/
macro "tgd_stepR" : tactic => `(tactic| first
  | (with_reducible refine GE.bind (ge_remove_loop0 (by assumption) (by assumption) (by tgd_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_remove_loop1 (by assumption) (by assumption) (by tgd_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_remove_loop2 (by assumption) (by assumption) (by tgd_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_remove_loop3 (by assumption) (by assumption) (by tgd_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_remove_fixup (by assumption) (by assumption) (by tgd_side) (by tgd_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_replace_child (by assumption) (by assumption) (by tgd_side) (by tgd_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_get_min (by assumption) (by assumption)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_set_min (by assumption) (by assumption)) (fun _ _ => ?_))
  | (with_reducible exact ge_rm_tail (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  | tgd_step)

set_option maxHeartbeats 2000000 in
/-- **`timer.remove` of an armed key of core `c`'s tree reads and writes only tree words of `K`.** -/
theorem ge_remove (C : TC st gS T s0 c K R W Kd) {s : S} {t : U64} (hI : TI st s0 c K K s) (ht : K t) (htd : Kd t)
    (ha : L.mem s0 (affA t) = c)
    (hco : ∀ i, obj.Tcb.timer_deadline st t s = ok i → ¬ i = 0#u64 → timer.core_of st s t = ok c) :
    GE (timer.remove gS s t) (timer.remove st s t) (fun s' => TI st s0 c K K s' ∧ L.mem s' (tdA t) = 0#u64) := by
  unfold timer.remove
  refine GE.bind (ge_td' C ht) fun i hi => ?_
  refine GE.ite (fun hi0 => GE.ret ⟨hI, ?_⟩) (fun hi0 => ?_)
  · rw [eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) s t)] at hi; rw [← hi0]; exact ok_inj_ff hi
  refine GE.bind (ge_core_of C ht (hco i hi hi0)) fun cpu hcpu => ?_
  subst hcpu
  repeat' tgd_stepR
  all_goals tgd_fin

end


open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read GRd GWr)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {R W : U64 → Prop}
variable {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
variable {s0 : S} {c : U64} {Kd : U64 → Prop}

theorem TC.mono {K K' : U64 → Prop} (C : TC st gS T s0 c K' R W Kd) (h : ∀ z, K z → K' z) : TC st gS T s0 c K R W Kd :=
  ⟨C.tcbs, fun z hz => C.inT z (h z hz), C.node, fun w hw => C.rd w (hw.mono h),
    fun w hw => C.wr w (TWl.mono h hw), fun s x v hx => C.wh s x v (h x hx),
    fun s x v hx => C.wd s x v (h x hx)⟩

theorem is_null_key {K : U64 → Prop} (C : TC st gS T s0 c K R W Kd) {x : U64} (hx : K x) :
    obj.Tcb.is_null x = ok false := by
  have h0 : x ≠ 0#u64 := fun e => (C.tcbs x (C.inT x hx)).ne0 (by rw [e]; rfl)
  rw [eq_of_spec_fd (obj.Tcb.is_null.spec x)]
  simp [h0]

theorem ge_set_parent' {K Kr : U64 → Prop} (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {x v : U64}
    (hx : K x) (hv : Kz K v) :
    GE (timer.set_parent gS s x v) (timer.set_parent st s x v)
      (fun s' => TI st s0 c K Kr s' ∧ s' = L.wr s (tpA x) v) := by
  unfold timer.set_parent
  rw [is_null_key C hx]
  apply GE.bind_ok
  refine GE.ite (fun h => absurd h Bool.false_ne_true) (fun _ => ?_)
  exact fld_ge' C hI hx (k := 3560#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_parent.guard x s v (C.wr _ (TWl.fld hx (by simp) (by simp))))
    (obj.Tcb.set_timer_parent.wr (L := L) s x v) (fun _ => hv) (fun h => by simp at h) (fun h => by simp at h)

theorem ge_set_left' {K Kr : U64 → Prop} (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {x v : U64}
    (hx : K x) (hv : Kz K v) :
    GE (timer.set_left gS s x v) (timer.set_left st s x v)
      (fun s' => TI st s0 c K Kr s' ∧ s' = L.wr s (tlA x) v) := by
  unfold timer.set_left
  rw [is_null_key C hx]
  apply GE.bind_ok
  refine GE.ite (fun h => absurd h Bool.false_ne_true) (fun _ => ?_)
  exact fld_ge' C hI hx (k := 3544#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_left.guard x s v (C.wr _ (TWl.fld hx (by simp) (by simp))))
    (obj.Tcb.set_timer_left.wr (L := L) s x v) (fun _ => hv) (fun h => by simp at h) (fun h => by simp at h)

theorem ge_set_right' {K Kr : U64 → Prop} (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {x v : U64}
    (hx : K x) (hv : Kz K v) :
    GE (timer.set_right gS s x v) (timer.set_right st s x v)
      (fun s' => TI st s0 c K Kr s' ∧ s' = L.wr s (trA x) v) := by
  unfold timer.set_right
  rw [is_null_key C hx]
  apply GE.bind_ok
  refine GE.ite (fun h => absurd h Bool.false_ne_true) (fun _ => ?_)
  exact fld_ge' C hI hx (k := 3552#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_right.guard x s v (C.wr _ (TWl.fld hx (by simp) (by simp))))
    (obj.Tcb.set_timer_right.wr (L := L) s x v) (fun _ => hv) (fun h => by simp at h) (fun h => by simp at h)

/-- `t`'s three links set (parent `p`, null children): `t` joins the keys with null-or-key links. -/
theorem ge_tlinks {Ks : U64 → Prop} {t p : U64} (C : TC st gS T s0 c (fun z => Ks z ∨ z = t) R W Kd) {s : S}
    (hI : TI st s0 c (fun z => Ks z ∨ z = t) Ks s) (hp : Kz (fun z => Ks z ∨ z = t) p)
    {α : Type} {k k' : S → Result α} {Q : α → Prop}
    (hk : ∀ s', TI st s0 c (fun z => Ks z ∨ z = t) (fun z => Ks z ∨ z = t) s' → GE (k' s') (k s') Q) :
    GE (Std.bind (timer.set_parent gS s t p) fun s5 =>
          Std.bind (timer.set_left gS s5 t 0#u64) fun s6 =>
            Std.bind (timer.set_right gS s6 t 0#u64) k')
       (Std.bind (timer.set_parent st s t p) fun s5 =>
          Std.bind (timer.set_left st s5 t 0#u64) fun s6 =>
            Std.bind (timer.set_right st s6 t 0#u64) k) Q := by
  have ht : (fun z => Ks z ∨ z = t) t := Or.inr rfl
  have hT := C.tcbs
  have htT := C.inT t ht
  refine GE.bind (ge_set_parent' C hI ht hp) fun s5 h5 => ?_
  obtain ⟨h5, e5⟩ := h5
  refine GE.bind (ge_set_left' C h5 ht (Or.inl rfl)) fun s6 h6 => ?_
  obtain ⟨h6, e6⟩ := h6
  refine GE.bind (ge_set_right' C h6 ht (Or.inl rfl)) fun s7 h7 => ?_
  obtain ⟨h7, e7⟩ := h7
  apply hk
  refine h7.ext ht ⟨?_, ?_, ?_⟩ <;> subst e7 e6 e5 <;> simp only [tlA, trA, tpA]
  · rw [trb_fld_wr hT htT htT (by simp) (by simp) (by simp) (by simp), if_neg (by simp),
      trb_fld_wr hT htT htT (by simp) (by simp) (by simp) (by simp), if_pos (by simp)]
    exact Or.inl rfl
  · rw [trb_fld_wr hT htT htT (by simp) (by simp) (by simp) (by simp), if_pos (by simp)]
    exact Or.inl rfl
  · rw [trb_fld_wr hT htT htT (by simp) (by simp) (by simp) (by simp), if_neg (by simp),
      trb_fld_wr hT htT htT (by simp) (by simp) (by simp) (by simp), if_neg (by simp),
      trb_fld_wr hT htT htT (by simp) (by simp) (by simp) (by simp), if_pos (by simp)]
    exact hp

theorem ge_set_tb {K Kr : U64 → Prop} (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {x v : U64}
    (hx : K x) :
    GE (obj.Tcb.set_timer_badge gS x s v) (obj.Tcb.set_timer_badge st x s v) (TI st s0 c K Kr) :=
  fld_ge C hI hx (k := 3536#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_badge.guard x s v (C.wr _ (TWl.fld hx (by simp) (by simp))))
    (obj.Tcb.set_timer_badge.wr (L := L) s x v) (fun h => by simp at h) (fun h => by simp at h) (fun h => by simp at h)

theorem ge_set_rep {K Kr : U64 → Prop} (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {v : U64} :
    GE (obj.node_set gS s c layout.node.REPROGRAM v) (obj.node_set st s c layout.node.REPROGRAM v)
      (TI st s0 c K Kr) :=
  ge_node_set C hI (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
    (fun h => by simp [layout.node.REPROGRAM, layout.node.TIMER_ROOT] at h)

/-- **`insert`'s height then deadline**: the height `c <<< 8 | RED` (naming `c`) first, then the deadline, the
key homed on `c`. -/
theorem ge_ht_dl {K Kr : U64 → Prop} (C : TC st gS T s0 c K R W Kd) {s : S} (hI : TI st s0 c K Kr s) {x i v d : U64}
    (hx : K x) (hxd : Kd x) (ha : L.mem s0 (affA x) = c) (hi : c <<< 8#i32 = ok i) (hv : lift (i ||| timer.RED) = ok v)
    {α : Type} {k k' : S → Result α} {Q : α → Prop}
    (hk : ∀ s', TI st s0 c K Kr s' → GE (k' s') (k s') Q) :
    GE (Std.bind (obj.Tcb.set_timer_height gS x s v) fun s3 =>
          Std.bind (obj.Tcb.set_timer_deadline gS x s3 d) k')
       (Std.bind (obj.Tcb.set_timer_height st x s v) fun s3 =>
          Std.bind (obj.Tcb.set_timer_deadline st x s3 d) k) Q := by
  have hxT := C.inT x hx
  have aH : Aligned (thA x) := field_aligned (C.tcbs x hxT) (by simp) (by simp)
  have hvc : v.val >>> 8 = c.val := ins_ht_core C.cs hi hv
  have wH := C.wh s x v hx (fun hd => ⟨hI.hj x hx hd, hvc⟩)
  refine GE.bind (fld_ge' C hI hx (k := 3568#u64) (by simp) (by simp) (by simp) (sth_of wH)
    (obj.Tcb.set_timer_height.wr (L := L) s x _) (fun h => by simp at h) (fun h => by simp at h)
    (fun _ _ => hvc)) fun s3 h3 => ?_
  obtain ⟨h3, e3⟩ := h3
  have t3 : (L.mem s3 (thA x)).val >>> 8 = c.val := by
    rw [e3, show core.num.U64.wrapping_add x 3568#u64 = thA x from rfl, L.mem_wr_same aH]; exact hvc
  have wD := C.wd s3 x d hx hxd (by rw [h3.af x hx]; exact ha) ha (fun _ => t3)
  refine GE.bind (fld_ge C h3 hx (k := 3528#u64) (by simp) (by simp) (by simp) (std_of wD)
    (obj.Tcb.set_timer_deadline.wr (L := L) s3 x _) (fun h => by simp at h) (fun _ _ => t3)
    (fun h => by simp at h)) fun s4 h4 => hk s4 h4

/-- With `insert`'s callees. -/
macro "tgd_stepI" : tactic => `(tactic| first
  | (with_reducible refine ge_tlinks (by assumption) (by assumption) (by tgd_side) (fun _ _ => ?_))
  | (with_reducible refine ge_ht_dl ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_set_tb (by assumption) (by assumption) (by assumption)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_insert_fixup (by assumption) (by assumption) (by tgd_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_set_min (by assumption) (by assumption)) (fun _ _ => ?_))
  | (with_reducible exact GE.mono (ge_set_rep (by assumption) (by assumption)) (fun _ _ => trivial))
  | tgd_step)

set_option maxHeartbeats 2000000 in
/-- **`timer.insert` of `t` on the current core `c` reads and writes only tree words of `Ks ∪ {t}`**,
after a removal that keeps the walk invariant on `Ks`. -/
theorem ge_insert {Ks : U64 → Prop} {t d bd : U64} (C : TC st gS T s0 c (fun z => Ks z ∨ z = t) R W Kd) {s : S}
    (hc : L.cpu s0 = c) (ha : L.mem s0 (affA t) = c) (htd : Kd t)
    (hrem : GE (timer.remove gS s t) (timer.remove st s t)
      (fun s1 => TI st s0 c Ks Ks s1 ∧ L.mem s1 (tdA t) = 0#u64 ∧ L.mem s1 (affA t) = L.mem s0 (affA t))) :
    GE (timer.insert gS s t d bd) (timer.insert st s t d bd) (fun _ => True) := by
  have C0 : TC st gS T s0 c Ks R W Kd := C.mono fun z h => Or.inl h
  unfold timer.insert
  refine GE.bind hrem fun s1 h1 => ?_
  obtain ⟨h1, hd1, ha1⟩ := h1
  refine GE.ite (fun _ => GE.ret trivial) (fun _ => ?_)
  refine GE.bind (ge_cur_cpu ‹PathObl.GRd gS st R›.cur_cpu h1 hc) fun cpu hcpu => ?_
  subst hcpu
  refine GE.bind (ge_root C0 h1) fun cur hcur => ?_
  refine GE.bind (ge_insert_loop C0 h1 (Or.inl rfl) hcur) fun r hr => ?_
  obtain ⟨p, gl, fi⟩ := r
  have hp : Kz (fun z => Ks z ∨ z = t) p := hr.imp_right Or.inl
  have h1' := h1.widen (K' := fun z => Ks z ∨ z = t) (fun z h => Or.inl h)
    (fun z hz hd => hz.elim (fun h => h1.hj z h hd) (fun e => absurd (e ▸ hd1) hd))
    (fun z hz => hz.elim (fun h => h1.af z h) (fun e => e ▸ ha1))
  have ht : (fun z => Ks z ∨ z = t) t := Or.inr rfl
  clear h1 hr hcur C0 hd1 ha1
  repeat' tgd_stepI
  all_goals tgd_fin

end

end Fl4Proofs.P2.GED
