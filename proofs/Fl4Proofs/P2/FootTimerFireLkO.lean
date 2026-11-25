/-
# P2 (p2lf): the lock-owned words a waking fire run touches

The waking branches of a fired timer's signal touch words that a lock owns (`OwnMap.own`): a queued thread's
`EP_NEXT` / `EP_PREV` (`gOwner`: `lock BLOCK_OBJ`), and the endpoint's and reply object's words (`Region.obj`:
their own lock). With the glue's locks (`PlanLk` [P], `P2/FootTimerFireLk`) they are readable and writable:

* `glink_own`: a queued thread's queue links are its `BLOCK_OBJ`'s lock's;
* `obj_own`: a word of an endpoint / reply region is that object's lock's;
* `held_lock`: a held lock's words are the path's.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireLk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Scs : Set U64} {Z : U64 → Nat} {K : KLayout}

/-- **A queued thread's queue links are its `BLOCK_OBJ`'s lock's.** -/
theorem glink_own {s : S} (hL : StLay K st T Scs Z s) (hT : TcbPlaced T) {t k : U64} (ht : t ∈ T)
    (hk : k.val = 3496 ∨ k.val = 3504) (hq : QueuedState (L.mem s (stA t))) :
    own K (L.mem s) (core.num.U64.wrapping_add t k) = .lock (L.mem s (blockA t)) := by
  have e := hL.own_tcb hT (L.mem s) ht (k := k) (by omega) (by omega)
  unfold fld at e
  have es : stA t = core.num.U64.wrapping_add t oSTATE := by rw [stA_eq]; rfl
  have eb : blockA t = core.num.U64.wrapping_add t oBLOCK_OBJ := by rw [blockA_eq]; rfl
  rw [es] at hq
  rw [e, tcbOwner, if_neg (show ¬ GateField k.val by unfold GateField; omega),
    if_neg (show ¬ TimerField k.val by unfold TimerField; omega),
    if_pos (show GField k.val by unfold GField; omega), gOwner]
  unfold fld
  rw [if_pos hq, eb]

/-- **A word of an endpoint / reply region is that object's lock's.** -/
theorem obj_own {m : U64 → U64} {x p : U64} (h : region K x = .obj p) : own K m x = .lock p := by
  simp only [own, h]

/-- A held lock's words are the path's. -/
theorem held_lock {c : U64} {lk : U64 → Prop} {o : Owner U64 U64} {p : U64} (h : o = .lock p) (hp : lk p) :
    HeldBy c lk o := by
  subst h; exact hp

end

end Fl4Proofs.P2
