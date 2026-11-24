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
open Fl4Proofs.P2.PathObl (guard guard_read)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {R W : U64 → Prop}
variable {s0 : S} {c : U64}

theorem TW.mono {K K' : U64 → Prop} (h : ∀ z, K z → K' z) {w : U64} (hw : TW st s0 c K w) :
    TW st s0 c K' w := by
  rcases hw with ⟨z, hz, r⟩ | r
  · exact Or.inl ⟨z, h z hz, r⟩
  · exact Or.inr r

theorem TC.mono {K K' : U64 → Prop} (C : TC st T s0 c K' R W) (h : ∀ z, K z → K' z) : TC st T s0 c K R W :=
  ⟨C.tcbs, fun z hz => C.inT z (h z hz), C.node, fun w hw => C.rd w (hw.mono h),
    fun w hw => C.wr w (hw.mono h)⟩

theorem TI.widen {K K' Kr : U64 → Prop} {s : S} (hI : TI st s0 c K Kr s) (h : ∀ z, K z → K' z) :
    TI st s0 c K' Kr s :=
  ⟨hI.ksb, hI.cpu, fun z hz => h z (hI.sub z hz), hI.root.imp_right (h _), fun z hz =>
    let ⟨a, b, d⟩ := hI.lnk z hz
    ⟨a.imp_right (h _), b.imp_right (h _), d.imp_right (h _)⟩⟩

theorem TI.congr {K Kr Kr' : U64 → Prop} {s : S} (hI : TI st s0 c K Kr s) (h : ∀ z, Kr' z → Kr z) :
    TI st s0 c K Kr' s :=
  ⟨hI.ksb, hI.cpu, fun z hz => hI.sub z (h z hz), hI.root, fun z hz => hI.lnk z (h z hz)⟩

/-- A link write of a key, with its real effect. -/
theorem fld_ge' {K Kr : U64 → Prop} (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x k v : U64}
    (hx : K x) {f : machine.Store S → U64 → S → U64 → Result S}
    (hk1 : 3528 ≤ k.val) (hk2 : k.val < 3576) (hk8 : k.val % 8 = 0)
    (hg : f (guard st R W) x s v = f st x s v)
    (hw : f st x s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add x k) v ⦄)
    (hv : k.val = 3544 ∨ k.val = 3552 ∨ k.val = 3560 → Kz K v) :
    GE (f (guard st R W) x s v) (f st x s v)
      (fun s' => TI st s0 c K Kr s' ∧ s' = L.wr s (core.num.U64.wrapping_add x k) v) := by
  rw [hg]
  refine ⟨rfl, fun s' e => ?_⟩
  rw [eq_of_spec_fd hw] at e
  have e' := ok_inj_ff e
  subst e'
  exact ⟨TI.wr_fld C hI hx hk1 hk2 hk8 hv, rfl⟩

theorem is_null_key {K : U64 → Prop} (C : TC st T s0 c K R W) {x : U64} (hx : K x) :
    obj.Tcb.is_null x = ok false := by
  have h0 : x ≠ 0#u64 := fun e => (C.tcbs x (C.inT x hx)).ne0 (by rw [e]; rfl)
  rw [eq_of_spec_fd (obj.Tcb.is_null.spec x)]
  simp [h0]

theorem ge_set_parent' {K Kr : U64 → Prop} (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x v : U64}
    (hx : K x) (hv : Kz K v) :
    GE (timer.set_parent (guard st R W) s x v) (timer.set_parent st s x v)
      (fun s' => TI st s0 c K Kr s' ∧ s' = L.wr s (tpA x) v) := by
  unfold timer.set_parent
  rw [is_null_key C hx]
  apply GE.bind_ok
  refine GE.ite (fun h => absurd h Bool.false_ne_true) (fun _ => ?_)
  exact fld_ge' C hI hx (k := 3560#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_parent.guard x s v (C.wr _ (TW.fld hx (by simp) (by simp))))
    (obj.Tcb.set_timer_parent.wr (L := L) s x v) fun _ => hv

theorem ge_set_left' {K Kr : U64 → Prop} (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x v : U64}
    (hx : K x) (hv : Kz K v) :
    GE (timer.set_left (guard st R W) s x v) (timer.set_left st s x v)
      (fun s' => TI st s0 c K Kr s' ∧ s' = L.wr s (tlA x) v) := by
  unfold timer.set_left
  rw [is_null_key C hx]
  apply GE.bind_ok
  refine GE.ite (fun h => absurd h Bool.false_ne_true) (fun _ => ?_)
  exact fld_ge' C hI hx (k := 3544#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_left.guard x s v (C.wr _ (TW.fld hx (by simp) (by simp))))
    (obj.Tcb.set_timer_left.wr (L := L) s x v) fun _ => hv

theorem ge_set_right' {K Kr : U64 → Prop} (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x v : U64}
    (hx : K x) (hv : Kz K v) :
    GE (timer.set_right (guard st R W) s x v) (timer.set_right st s x v)
      (fun s' => TI st s0 c K Kr s' ∧ s' = L.wr s (trA x) v) := by
  unfold timer.set_right
  rw [is_null_key C hx]
  apply GE.bind_ok
  refine GE.ite (fun h => absurd h Bool.false_ne_true) (fun _ => ?_)
  exact fld_ge' C hI hx (k := 3552#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_right.guard x s v (C.wr _ (TW.fld hx (by simp) (by simp))))
    (obj.Tcb.set_timer_right.wr (L := L) s x v) fun _ => hv

/-- `t`'s three links set (parent `p`, null children): `t` joins the keys with null-or-key links. -/
theorem ge_tlinks {Ks : U64 → Prop} {t p : U64} (C : TC st T s0 c (fun z => Ks z ∨ z = t) R W) {s : S}
    (hI : TI st s0 c (fun z => Ks z ∨ z = t) Ks s) (hp : Kz (fun z => Ks z ∨ z = t) p)
    {α : Type} {k k' : S → Result α} {Q : α → Prop}
    (hk : ∀ s', TI st s0 c (fun z => Ks z ∨ z = t) (fun z => Ks z ∨ z = t) s' → GE (k' s') (k s') Q) :
    GE (Std.bind (timer.set_parent (guard st R W) s t p) fun s5 =>
          Std.bind (timer.set_left (guard st R W) s5 t 0#u64) fun s6 =>
            Std.bind (timer.set_right (guard st R W) s6 t 0#u64) k')
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
    GE ((guard st R W).cur_cpu s) (st.cur_cpu s) (fun v => v = c) :=
  ⟨rfl, fun v e => by rw [L.cur_cpu_eq] at e; rw [← ok_inj_ff e, hI.cpu, hc]⟩

theorem ge_set_tb {K Kr : U64 → Prop} (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {x v : U64}
    (hx : K x) :
    GE (obj.Tcb.set_timer_badge (guard st R W) x s v) (obj.Tcb.set_timer_badge st x s v) (TI st s0 c K Kr) :=
  fld_ge C hI hx (k := 3536#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_badge.guard x s v (C.wr _ (TW.fld hx (by simp) (by simp))))
    (obj.Tcb.set_timer_badge.wr (L := L) s x v) (fun h => by simp at h)

theorem ge_set_rep {K Kr : U64 → Prop} (C : TC st T s0 c K R W) {s : S} (hI : TI st s0 c K Kr s) {v : U64} :
    GE (obj.node_set (guard st R W) s c layout.node.REPROGRAM v) (obj.node_set st s c layout.node.REPROGRAM v)
      (TI st s0 c K Kr) :=
  ge_node_set C hI (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
    (fun h => by simp [layout.node.REPROGRAM, layout.node.TIMER_ROOT] at h)

/-- With `insert`'s callees. -/
macro "tg_stepI" : tactic => `(tactic| first
  | (with_reducible refine ge_tlinks (by assumption) (by assumption) (by tg_side) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_set_td (by assumption) (by assumption) (by assumption)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_set_tb (by assumption) (by assumption) (by assumption)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_set_th (by assumption) (by assumption) (by assumption)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_insert_fixup (by assumption) (by assumption) (by tg_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_set_min (by assumption) (by assumption)) (fun _ _ => ?_))
  | (with_reducible exact GE.mono (ge_set_rep (by assumption) (by assumption)) (fun _ _ => trivial))
  | tg_step)

set_option maxHeartbeats 2000000 in
/-- **`timer.insert` of `t` on the current core `c` reads and writes only tree words of `Ks ∪ {t}`**,
after a removal that keeps the walk invariant on `Ks`. -/
theorem ge_insert {Ks : U64 → Prop} {t d bd : U64} (C : TC st T s0 c (fun z => Ks z ∨ z = t) R W) {s : S}
    (hc : L.cpu s0 = c)
    (hrem : GE (timer.remove (guard st R W) s t) (timer.remove st s t) (TI st s0 c Ks Ks)) :
    GE (timer.insert (guard st R W) s t d bd) (timer.insert st s t d bd) (fun _ => True) := by
  have C0 : TC st T s0 c Ks R W := C.mono fun z h => Or.inl h
  unfold timer.insert
  refine GE.bind hrem fun s1 h1 => ?_
  refine GE.ite (fun _ => GE.ret trivial) (fun _ => ?_)
  refine GE.bind (ge_cur_cpu h1 hc) fun cpu hcpu => ?_
  subst hcpu
  refine GE.bind (ge_root C0 h1) fun cur hcur => ?_
  refine GE.bind (ge_insert_loop C0 h1 (Or.inl rfl) hcur) fun r hr => ?_
  obtain ⟨p, gl, fi⟩ := r
  have hp : Kz (fun z => Ks z ∨ z = t) p := hr.imp_right Or.inl
  have h1' := h1.widen (K' := fun z => Ks z ∨ z = t) fun z h => Or.inl h
  have ht : (fun z => Ks z ∨ z = t) t := Or.inr rfl
  clear h1 hr hcur C0
  repeat' tg_stepI
  all_goals tg_fin

end

end Fl4Proofs.P2
