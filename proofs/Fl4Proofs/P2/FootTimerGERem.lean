/-
# P2: `timer.remove` on the guarded store (`GE`, see `P2/FootTimerGE.lean`)

`ge_remove`: removing an armed key `t` of core `c`'s tree (`core_of t = c`) on `guard st R W` is the real
removal, keeps the walk invariant `TI` and leaves `t` disarmed: every read and write is a tree word of the keys `K`
(`TW`), with the successor searches and `remove_fixup` of `P2/FootTimerGELoop.lean`.

No named premises.
-/
import Fl4Proofs.P2.FootTimerGELoop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read GRd GWr)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {R W : U64 → Prop}
variable {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
variable {s0 : S} {c : U64} {K : U64 → Prop}

theorem ge_td' (C : TC st gS T s0 c K R W) {s : S} {x : U64} (hx : K x) :
    GE (obj.Tcb.timer_deadline gS x s) (obj.Tcb.timer_deadline st x s)
      (fun v => obj.Tcb.timer_deadline st x s = ok v) :=
  ⟨PathObl.obj.Tcb.timer_deadline.guard x s (C.rd _ (TW.fld hx (by simp) (by simp))), fun _ e => e⟩

theorem ge_core_of (C : TC st gS T s0 c K R W) {s : S} {t : U64} (ht : K t) (h : timer.core_of st s t = ok c) :
    GE (timer.core_of gS s t) (timer.core_of st s t) (fun v => v = c) := by
  have e : timer.core_of gS s t = timer.core_of st s t := by
    unfold timer.core_of
    rw [PathObl.obj.Tcb.timer_height.guard t s (C.rd _ (TW.fld ht (by simp) (by simp)))]
  rw [e]
  exact ⟨rfl, fun v hv => by rw [h] at hv; exact (ok_inj_ff hv).symm⟩

theorem ge_get_min (C : TC st gS T s0 c K R W) {s : S} {Kr : U64 → Prop} (hI : TI st s0 c K Kr s) :
    GE (obj.node_get gS s c layout.node.TIMER_MIN) (obj.node_get st s c layout.node.TIMER_MIN)
      (fun _ => True) :=
  GE.mono (ge_node_get C hI (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])) fun _ _ => trivial

theorem ge_set_min (C : TC st gS T s0 c K R W) {s : S} {Kr : U64 → Prop} (hI : TI st s0 c K Kr s) {v : U64} :
    GE (obj.node_set gS s c layout.node.TIMER_MIN v) (obj.node_set st s c layout.node.TIMER_MIN v)
      (TI st s0 c K Kr) :=
  ge_node_set C hI (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
    (fun h => by simp [layout.node.TIMER_MIN, layout.node.TIMER_ROOT] at h)

/-- **`remove`'s tail**: the deadline zeroed (the key homed on `c`, its height naming `c` while armed), then
the height (the key disarmed by then). -/
theorem ge_rm_tail (C : TC st gS T s0 c K R W) {s : S} {Kr : U64 → Prop} (hI : TI st s0 c K Kr s) {x : U64}
    (hx : K x) (ha : L.mem s0 (affA x) = c) :
    GE (Std.bind (obj.Tcb.set_timer_deadline gS x s 0#u64) fun s8 => obj.Tcb.set_timer_height gS x s8 0#u64)
      (Std.bind (obj.Tcb.set_timer_deadline st x s 0#u64) fun s8 => obj.Tcb.set_timer_height st x s8 0#u64)
      (fun s' => TI st s0 c K Kr s' ∧ L.mem s' (tdA x) = 0#u64) := by
  have hxT := C.inT x hx
  have aD : Aligned (tdA x) := field_aligned (C.tcbs x hxT) (by simp) (by simp)
  have aH : Aligned (thA x) := field_aligned (C.tcbs x hxT) (by simp) (by simp)
  have nDH : tdA x ≠ thA x := tcb_word_ne (C.tcbs x hxT) (C.tcbs x hxT) (by simp) (by simp) (fun _ => by simp)
  have wD := C.wd s x 0#u64 hx (by rw [hI.af x hx]; exact ha) ha
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
macro "tg_stepR" : tactic => `(tactic| first
  | (with_reducible refine GE.bind (ge_remove_loop0 (by assumption) (by assumption) (by tg_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_remove_loop1 (by assumption) (by assumption) (by tg_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_remove_loop2 (by assumption) (by assumption) (by tg_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_remove_loop3 (by assumption) (by assumption) (by tg_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_remove_fixup (by assumption) (by assumption) (by tg_side) (by tg_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_replace_child (by assumption) (by assumption) (by tg_side) (by tg_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_get_min (by assumption) (by assumption)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_set_min (by assumption) (by assumption)) (fun _ _ => ?_))
  | (with_reducible exact ge_rm_tail (by assumption) (by assumption) (by assumption) (by assumption))
  | tg_step)

set_option maxHeartbeats 2000000 in
/-- **`timer.remove` of an armed key of core `c`'s tree reads and writes only tree words of `K`.** -/
theorem ge_remove (C : TC st gS T s0 c K R W) {s : S} {t : U64} (hI : TI st s0 c K K s) (ht : K t)
    (ha : L.mem s0 (affA t) = c)
    (hco : ∀ i, obj.Tcb.timer_deadline st t s = ok i → ¬ i = 0#u64 → timer.core_of st s t = ok c) :
    GE (timer.remove gS s t) (timer.remove st s t) (fun s' => TI st s0 c K K s' ∧ L.mem s' (tdA t) = 0#u64) := by
  unfold timer.remove
  refine GE.bind (ge_td' C ht) fun i hi => ?_
  refine GE.ite (fun hi0 => GE.ret ⟨hI, ?_⟩) (fun hi0 => ?_)
  · rw [eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) s t)] at hi; rw [← hi0]; exact ok_inj_ff hi
  refine GE.bind (ge_core_of C ht (hco i hi hi0)) fun cpu hcpu => ?_
  subst hcpu
  repeat' tg_stepR
  all_goals tg_fin

end

end Fl4Proofs.P2
