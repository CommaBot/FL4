/-
# P2: `timer.remove` on the guarded store (`GE`, see `P2/FootTimerGE.lean`)

`ge_remove`: removing an armed key `t` of core `c`'s tree (`core_of t = c`) on `guard st R W` is the real
removal, and keeps the walk invariant `TI`: every read and write is a tree word of the keys `K`
(`TW`), with the successor searches and `remove_fixup` of `P2/FootTimerGELoop.lean`.

No named premises.
-/
import Fl4Proofs.P2.FootTimerGELoop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {R W : U64 → Prop}
variable {s0 : S} {c : U64} {K : U64 → Prop}

theorem ge_td' (C : TC st T s0 c K R W) {s : S} {x : U64} (hx : K x) :
    GE (obj.Tcb.timer_deadline (guard st R W) x s) (obj.Tcb.timer_deadline st x s)
      (fun v => obj.Tcb.timer_deadline st x s = ok v) :=
  ⟨tdG (C.rd _ (TW.fld hx (by simp) (by simp))), fun _ e => e⟩

theorem ge_core_of (C : TC st T s0 c K R W) {s : S} {t : U64} (ht : K t) (h : timer.core_of st s t = ok c) :
    GE (timer.core_of (guard st R W) s t) (timer.core_of st s t) (fun v => v = c) := by
  have e : timer.core_of (guard st R W) s t = timer.core_of st s t := by
    unfold timer.core_of
    rw [PathObl.obj.Tcb.timer_height.guard t s (C.rd _ (TW.fld ht (by simp) (by simp)))]
  rw [e]
  exact ⟨rfl, fun v hv => by rw [h] at hv; exact (ok_inj_ff hv).symm⟩

theorem ge_get_min (C : TC st T s0 c K R W) {s : S} {Kr : U64 → Prop} (hI : TI st s0 c K Kr s) :
    GE (obj.node_get (guard st R W) s c layout.node.TIMER_MIN) (obj.node_get st s c layout.node.TIMER_MIN)
      (fun _ => True) :=
  GE.mono (ge_node_get C hI (by simp [layout.node.TIMER_MIN])) fun _ _ => trivial

theorem ge_set_min (C : TC st T s0 c K R W) {s : S} {Kr : U64 → Prop} (hI : TI st s0 c K Kr s) {v : U64} :
    GE (obj.node_set (guard st R W) s c layout.node.TIMER_MIN v) (obj.node_set st s c layout.node.TIMER_MIN v)
      (TI st s0 c K Kr) :=
  ge_node_set C hI (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
    (fun h => by simp [layout.node.TIMER_MIN, layout.node.TIMER_ROOT] at h)

theorem ge_set_th (C : TC st T s0 c K R W) {s : S} {Kr : U64 → Prop} (hI : TI st s0 c K Kr s) {x v : U64}
    (hx : K x) :
    GE (obj.Tcb.set_timer_height (guard st R W) x s v) (obj.Tcb.set_timer_height st x s v) (TI st s0 c K Kr) :=
  fld_ge C hI hx (k := 3568#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_height.guard x s v (C.wr _ (TW.fld hx (by simp) (by simp))))
    (obj.Tcb.set_timer_height.wr (L := L) s x v) (fun h => by simp at h)

theorem ge_set_td (C : TC st T s0 c K R W) {s : S} {Kr : U64 → Prop} (hI : TI st s0 c K Kr s) {x v : U64}
    (hx : K x) :
    GE (obj.Tcb.set_timer_deadline (guard st R W) x s v) (obj.Tcb.set_timer_deadline st x s v)
      (TI st s0 c K Kr) :=
  fld_ge C hI hx (k := 3528#u64) (by simp) (by simp) (by simp)
    (PathObl.obj.Tcb.set_timer_deadline.guard x s v (C.wr _ (TW.fld hx (by simp) (by simp))))
    (obj.Tcb.set_timer_deadline.wr (L := L) s x v) (fun h => by simp at h)

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
  | (with_reducible refine GE.bind (ge_set_th (by assumption) (by assumption) (by assumption)) (fun _ _ => ?_))
  | (with_reducible exact ge_set_td (by assumption) (by assumption) (by assumption))
  | tg_step)

set_option maxHeartbeats 2000000 in
/-- **`timer.remove` of an armed key of core `c`'s tree reads and writes only tree words of `K`.** -/
theorem ge_remove (C : TC st T s0 c K R W) {s : S} {t : U64} (hI : TI st s0 c K K s) (ht : K t)
    (hco : ∀ i, obj.Tcb.timer_deadline st t s = ok i → ¬ i = 0#u64 → timer.core_of st s t = ok c) :
    GE (timer.remove (guard st R W) s t) (timer.remove st s t) (TI st s0 c K K) := by
  unfold timer.remove
  refine GE.bind (ge_td' C ht) fun i hi => ?_
  refine GE.ite (fun _ => GE.ret hI) (fun hi0 => ?_)
  refine GE.bind (ge_core_of C ht (hco i hi hi0)) fun cpu hcpu => ?_
  subst hcpu
  repeat' tg_stepR
  all_goals tg_fin

end

end Fl4Proofs.P2
