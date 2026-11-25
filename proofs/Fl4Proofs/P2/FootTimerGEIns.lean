/-
# P2: `timer.insert` on the guarded store (`GE`, see `P2/FootTimerGE.lean`)

`ge_insert`: inserting `t` into the current core `c`'s tree, after a removal that keeps the walk invariant
on the keys `Ks` (`hrem`), reads and writes only tree words of `Ks ∪ {t}`. The descent and the hole
parent use `Ks`; `t`'s links are set (to the hole parent and null) before anything reads them
(`ge_tlinks`), from which `t` joins the keys whose links are null or keys, as `insert_fixup` needs.

No named premises.
-/
import Fl4Proofs.P2.FootTimerGERem
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read GRd GWr)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {R W : U64 → Prop}
variable {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
variable {s0 : S} {c : U64}

theorem TW.mono {K K' : U64 → Prop} (h : ∀ z, K z → K' z) {w : U64} (hw : TW st s0 c K w) :
    TW st s0 c K' w := by
  rcases hw with ⟨z, hz, r⟩ | r
  · exact Or.inl ⟨z, h z hz, r⟩
  · exact Or.inr r

theorem TWl.mono {K K' : U64 → Prop} (h : ∀ z, K z → K' z) {w : U64} (hw : TWl st s0 c K w) :
    TWl st s0 c K' w := by
  rcases hw with ⟨z, hz, r⟩ | r
  · exact Or.inl ⟨z, h z hz, r⟩
  · exact Or.inr r

theorem TC.mono {K K' : U64 → Prop} (C : TC st gS T s0 c K' R W) (h : ∀ z, K z → K' z) : TC st gS T s0 c K R W :=
  ⟨C.tcbs, fun z hz => C.inT z (h z hz), C.node, fun w hw => C.rd w (hw.mono h),
    fun w hw => C.wr w (TWl.mono h hw), fun s x v hx => C.wh s x v (h x hx),
    fun s x v hx => C.wd s x v (h x hx)⟩

theorem TI.widen {K K' Kr : U64 → Prop} {s : S} (hI : TI st s0 c K Kr s) (h : ∀ z, K z → K' z)
    (hj : ∀ z, K' z → L.mem s (tdA z) ≠ 0#u64 → (L.mem s (thA z)).val >>> 8 = c.val)
    (af : ∀ z, K' z → L.mem s (affA z) = L.mem s0 (affA z)) :
    TI st s0 c K' Kr s :=
  ⟨hI.ksb, hI.cpu, fun z hz => h z (hI.sub z hz), hI.root.imp_right (h _), fun z hz =>
    let ⟨a, b, d⟩ := hI.lnk z hz
    ⟨a.imp_right (h _), b.imp_right (h _), d.imp_right (h _)⟩, hj, af⟩

theorem TI.congr {K Kr Kr' : U64 → Prop} {s : S} (hI : TI st s0 c K Kr s) (h : ∀ z, Kr' z → Kr z) :
    TI st s0 c K Kr' s :=
  ⟨hI.ksb, hI.cpu, fun z hz => hI.sub z (h z hz), hI.root, fun z hz => hI.lnk z (h z hz), hI.hj, hI.af⟩

theorem is_null_key {K : U64 → Prop} (C : TC st gS T s0 c K R W) {x : U64} (hx : K x) :
    obj.Tcb.is_null x = ok false := by
  have h0 : x ≠ 0#u64 := fun e => (C.tcbs x (C.inT x hx)).ne0 (by rw [e]; rfl)
  rw [eq_of_spec_fd (obj.Tcb.is_null.spec x)]
  simp [h0]

theorem ge_set_parent' {K Kr : U64 → Prop} (C : TC st gS T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x v : U64}
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

theorem ge_set_left' {K Kr : U64 → Prop} (C : TC st gS T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x v : U64}
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

theorem ge_set_right' {K Kr : U64 → Prop} (C : TC st gS T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x v : U64}
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
theorem ge_tlinks {Ks : U64 → Prop} {t p : U64} (C : TC st gS T s0 c (fun z => Ks z ∨ z = t) R W) {s : S}
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

theorem ge_cur_cpu {K Kr : U64 → Prop} {s : S} (hI : TI st s0 c K Kr s) (hc : L.cpu s0 = c) :
    GE (gS.cur_cpu s) (st.cur_cpu s) (fun v => v = c) :=
  ⟨rfl, fun v e => by rw [L.cur_cpu_eq] at e; rw [← ok_inj_ff e, hI.cpu, hc]⟩

theorem ge_set_tb {K Kr : U64 → Prop} (C : TC st gS T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x v : U64}
    (hx : K x) :
    GE (obj.Tcb.set_timer_badge gS x s v) (obj.Tcb.set_timer_badge st x s v) (TI st s0 c K Kr) :=
  fld_ge C hI hx (k := 3536#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_badge.guard x s v (C.wr _ (TWl.fld hx (by simp) (by simp))))
    (obj.Tcb.set_timer_badge.wr (L := L) s x v) (fun h => by simp at h) (fun h => by simp at h) (fun h => by simp at h)

theorem ge_set_rep {K Kr : U64 → Prop} (C : TC st gS T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {v : U64} :
    GE (obj.node_set gS s c layout.node.REPROGRAM v) (obj.node_set st s c layout.node.REPROGRAM v)
      (TI st s0 c K Kr) :=
  ge_node_set C hI (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
    (fun h => by simp [layout.node.REPROGRAM, layout.node.TIMER_ROOT] at h)

/-- **`insert`'s height then deadline**: the height `c <<< 8 | RED` (naming `c`) first, then the deadline, the
key homed on `c`. -/
theorem ge_ht_dl {K Kr : U64 → Prop} (C : TC st gS T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x i v d : U64}
    (hx : K x) (ha : L.mem s0 (affA x) = c) (hi : c <<< 8#i32 = ok i) (hv : lift (i ||| timer.RED) = ok v)
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
  have wD := C.wd s3 x d hx (by rw [h3.af x hx]; exact ha) ha (fun _ => t3)
  refine GE.bind (fld_ge C h3 hx (k := 3528#u64) (by simp) (by simp) (by simp) (std_of wD)
    (obj.Tcb.set_timer_deadline.wr (L := L) s3 x _) (fun h => by simp at h) (fun _ _ => t3)
    (fun h => by simp at h)) fun s4 h4 => hk s4 h4

/-- With `insert`'s callees. -/
macro "tg_stepI" : tactic => `(tactic| first
  | (with_reducible refine ge_tlinks (by assumption) (by assumption) (by tg_side) (fun _ _ => ?_))
  | (with_reducible refine ge_ht_dl (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_set_tb (by assumption) (by assumption) (by assumption)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_insert_fixup (by assumption) (by assumption) (by tg_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_set_min (by assumption) (by assumption)) (fun _ _ => ?_))
  | (with_reducible exact GE.mono (ge_set_rep (by assumption) (by assumption)) (fun _ _ => trivial))
  | tg_step)

set_option maxHeartbeats 2000000 in
/-- **`timer.insert` of `t` on the current core `c` reads and writes only tree words of `Ks ∪ {t}`**,
after a removal that keeps the walk invariant on `Ks`. -/
theorem ge_insert {Ks : U64 → Prop} {t d bd : U64} (C : TC st gS T s0 c (fun z => Ks z ∨ z = t) R W) {s : S}
    (hc : L.cpu s0 = c) (ha : L.mem s0 (affA t) = c)
    (hrem : GE (timer.remove gS s t) (timer.remove st s t)
      (fun s1 => TI st s0 c Ks Ks s1 ∧ L.mem s1 (tdA t) = 0#u64 ∧ L.mem s1 (affA t) = L.mem s0 (affA t))) :
    GE (timer.insert gS s t d bd) (timer.insert st s t d bd) (fun _ => True) := by
  have C0 : TC st gS T s0 c Ks R W := C.mono fun z h => Or.inl h
  unfold timer.insert
  refine GE.bind hrem fun s1 h1 => ?_
  obtain ⟨h1, hd1, ha1⟩ := h1
  refine GE.ite (fun _ => GE.ret trivial) (fun _ => ?_)
  refine GE.bind (ge_cur_cpu h1 hc) fun cpu hcpu => ?_
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
  repeat' tg_stepI
  all_goals tg_fin

end

end Fl4Proofs.P2
