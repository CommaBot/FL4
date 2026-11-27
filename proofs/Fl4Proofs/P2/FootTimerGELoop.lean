/-
# P2: the timer tree's loops on the guarded store (`GE`, see `P2/FootTimerGE.lean`)

`remove_fixup`, `insert_fixup`, `remove`'s successor searches (`remove_loop0` .. `remove_loop3`) and
`insert`'s descent (`insert_loop`): each body run on `guard st R W` is the real body, and keeps the walk
invariant (`TI`, node variables null or keys) with a smaller fuel (`GE.loop`).

No named premises.
-/
import Fl4Proofs.P2.FootTimerGE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read GRd GWr)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {R W : U64 → Prop}
variable {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
variable {s0 : S} {c : U64} {K : U64 → Prop}

/-- With the rotations. -/
macro "tg_step2" : tactic => `(tactic| first
  | (with_reducible refine GE.bind (ge_rotate_left (by assumption) (by assumption) (by tg_side)) (fun _ _ => ?_))
  | (with_reducible refine GE.bind (ge_rotate_right (by assumption) (by assumption) (by tg_side)) (fun _ _ => ?_))
  | (with_reducible exact ge_rotate_left (by assumption) (by assumption) (by tg_side))
  | (with_reducible exact ge_rotate_right (by assumption) (by assumption) (by tg_side))
  | tg_step)

/-- Closing a loop body's postcondition. -/
macro "tg_fin" : tactic => `(tactic| (
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

theorem ge_remove_fixup_body (C : TC st gS T s0 c K R W) {s : S} {x p fuel : U64} (hI : TI st s0 c K K s)
    (hx : Kz K x) (hp : Kz K p) :
    GE (timer.remove_fixup_loop.body gS c s x p fuel) (timer.remove_fixup_loop.body st c s x p fuel)
      (LoopPost (fun y : S × U64 × U64 × U64 => TI st s0 c K K y.1 ∧ Kz K y.2.1 ∧ Kz K y.2.2.1)
        (fun y => y.2.2.2.val) (fun z : S × U64 => TI st s0 c K K z.1 ∧ Kz K z.2) (s, x, p, fuel)) := by
  unfold timer.remove_fixup_loop.body
  repeat' tg_step2
  all_goals tg_fin

theorem ge_remove_fixup_loop (C : TC st gS T s0 c K R W) {s : S} {x p fuel : U64} (hI : TI st s0 c K K s)
    (hx : Kz K x) (hp : Kz K p) :
    GE (timer.remove_fixup_loop gS s c x p fuel) (timer.remove_fixup_loop st s c x p fuel)
      (fun z : S × U64 => TI st s0 c K K z.1 ∧ Kz K z.2) := by
  unfold timer.remove_fixup_loop
  refine GE.loop (fun y : S × U64 × U64 × U64 => TI st s0 c K K y.1 ∧ Kz K y.2.1 ∧ Kz K y.2.2.1)
    (fun y => y.2.2.2.val) (fun y hy => ?_) (s, x, p, fuel) ⟨hI, hx, hp⟩
  obtain ⟨s1, x1, p1, f1⟩ := y
  exact ge_remove_fixup_body C hy.1 hy.2.1 hy.2.2

theorem ge_remove_fixup (C : TC st gS T s0 c K R W) {s : S} {x p : U64} (hI : TI st s0 c K K s)
    (hx : Kz K x) (hp : Kz K p) :
    GE (timer.remove_fixup gS s c x p) (timer.remove_fixup st s c x p) (TI st s0 c K K) := by
  unfold timer.remove_fixup
  refine GE.bind (ge_remove_fixup_loop C hI hx hp) fun z hz => ?_
  obtain ⟨s1, x1⟩ := z
  obtain ⟨h1, h2⟩ := hz
  apply GE.uncurry
  dsimp only at h1 h2
  repeat' tg_step
  all_goals tg_fin

/-! ## `insert_fixup` -/

theorem ge_insert_fixup_body (C : TC st gS T s0 c K R W) {s : S} {z fuel : U64} (hI : TI st s0 c K K s)
    (hz : Kz K z) :
    GE (timer.insert_fixup_loop.body gS c s z fuel) (timer.insert_fixup_loop.body st c s z fuel)
      (LoopPost (fun y : S × U64 × U64 => TI st s0 c K K y.1 ∧ Kz K y.2.1) (fun y => y.2.2.val)
        (TI st s0 c K K) (s, z, fuel)) := by
  unfold timer.insert_fixup_loop.body
  repeat' tg_step2
  all_goals tg_fin

theorem ge_insert_fixup (C : TC st gS T s0 c K R W) {s : S} {z : U64} (hI : TI st s0 c K K s) (hz : Kz K z) :
    GE (timer.insert_fixup gS s c z) (timer.insert_fixup st s c z) (TI st s0 c K K) := by
  unfold timer.insert_fixup timer.insert_fixup_loop
  refine GE.bind (GE.loop (Q := TI st s0 c K K) (fun y : S × U64 × U64 => TI st s0 c K K y.1 ∧ Kz K y.2.1)
    (fun y => y.2.2.val) (fun y hy => ?_) (s, z, 128#u64) ⟨hI, hz⟩) fun s1 h1 => ?_
  · obtain ⟨s1, z1, f1⟩ := y
    exact ge_insert_fixup_body C hy.1 hy.2
  · repeat' tg_step
    all_goals tg_fin

/-! ## `remove`'s successor searches -/

theorem ge_remove_loop0 (C : TC st gS T s0 c K R W) {s : S} {y fuel : U64} (hI : TI st s0 c K K s) (hy : Kz K y) :
    GE (timer.remove_loop0 gS s y fuel) (timer.remove_loop0 st s y fuel) (Kz K) := by
  unfold timer.remove_loop0
  refine GE.loop (fun y : U64 × U64 => Kz K y.1) (fun y => y.2.val) (fun y hy => ?_) (y, fuel) hy
  obtain ⟨y1, f1⟩ := y
  show GE (timer.remove_loop0.body gS s y1 f1) (timer.remove_loop0.body st s y1 f1) _
  unfold timer.remove_loop0.body
  repeat' tg_step
  all_goals tg_fin

theorem ge_remove_loop1 (C : TC st gS T s0 c K R W) {s : S} {y fuel : U64} (hI : TI st s0 c K K s) (hy : Kz K y) :
    GE (timer.remove_loop1 gS s y fuel) (timer.remove_loop1 st s y fuel) (Kz K) := by
  unfold timer.remove_loop1
  refine GE.loop (fun y : U64 × U64 => Kz K y.1) (fun y => y.2.val) (fun y hy => ?_) (y, fuel) hy
  obtain ⟨y1, f1⟩ := y
  show GE (timer.remove_loop1.body gS s y1 f1) (timer.remove_loop1.body st s y1 f1) _
  unfold timer.remove_loop1.body
  repeat' tg_step
  all_goals tg_fin

theorem ge_remove_loop2 (C : TC st gS T s0 c K R W) {s : S} {y fuel : U64} (hI : TI st s0 c K K s) (hy : Kz K y) :
    GE (timer.remove_loop2 gS s y fuel) (timer.remove_loop2 st s y fuel) (Kz K) := by
  unfold timer.remove_loop2
  refine GE.loop (fun y : U64 × U64 => Kz K y.1) (fun y => y.2.val) (fun y hy => ?_) (y, fuel) hy
  obtain ⟨y1, f1⟩ := y
  show GE (timer.remove_loop2.body gS s y1 f1) (timer.remove_loop2.body st s y1 f1) _
  unfold timer.remove_loop2.body
  repeat' tg_step
  all_goals tg_fin

theorem ge_remove_loop3 (C : TC st gS T s0 c K R W) {s : S} {y fuel : U64} (hI : TI st s0 c K K s) (hy : Kz K y) :
    GE (timer.remove_loop3 gS s y fuel) (timer.remove_loop3 st s y fuel) (Kz K) := by
  unfold timer.remove_loop3
  refine GE.loop (fun y : U64 × U64 => Kz K y.1) (fun y => y.2.val) (fun y hy => ?_) (y, fuel) hy
  obtain ⟨y1, f1⟩ := y
  show GE (timer.remove_loop3.body gS s y1 f1) (timer.remove_loop3.body st s y1 f1) _
  unfold timer.remove_loop3.body
  repeat' tg_step
  all_goals tg_fin

/-! ## `insert`'s descent -/

theorem kz_of_null {x : U64} {b : Bool} (h : Kz K x) (hb : obj.Tcb.is_null x = ok b) (hn : ¬ b = true) : K x :=
  h.resolve_left fun e => hn (by rw [is_null_eq hb, e]; rfl)

theorem ge_td (C : TC st gS T s0 c K R W) {s : S} {x : U64} (hx : K x) :
    GE (obj.Tcb.timer_deadline gS x s) (obj.Tcb.timer_deadline st x s) (fun _ => True) :=
  ⟨PathObl.obj.Tcb.timer_deadline.guard x s (C.rd _ (TW.fld hx (by simp) (by simp))), fun _ _ => trivial⟩

theorem ge_insert_loop (C : TC st gS T s0 c K R W) {s : S} {d p cur : U64} {gl fi : Bool} {fuel : U64}
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
    | tg_step)
  all_goals tg_fin

end

end Fl4Proofs.P2
