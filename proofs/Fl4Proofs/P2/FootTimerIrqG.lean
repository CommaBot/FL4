/-
# P2: the timer interrupt local path's checks on the guarded store

Guarded-store equalities for `top_ok`, `wake_ok`, `round_robin_ok` (`localtimer.rs`), each stated with the words it
reads in `R`, at the real run's values, on any store `gS` that answers `R` reads as `st` (`PathObl.GRd`: `guard st R W`
for `acc`, `gd st R P` for `move`). `MayRd R s t`: the words `may_run_here s cpu t` reads.

No named premises.
-/
import Fl4Proofs.P2.FootTimerSetG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read bind_guard_congr)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R]

/-- The words `may_run_here` reads for `t`. -/
structure MayRd (R : U64 → Prop) (s : S) (t : U64) : Prop where
  aff : R (affA t)
  st : R (stA t)
  yld : R (yieldA t)
  vcpu : R (core.num.U64.wrapping_add t 3664#u64)
  sc : R (scA t)
  core : R (scCoreA (L.mem s (scA t)))

theorem MayRd.guard {s : S} {t : U64} (h : MayRd (L := L) R s t) (cpu : U64) :
    localtimer.may_run_here gS s cpu t = localtimer.may_run_here st s cpu t :=
  may_run_here.guard s cpu t h.aff h.st h.yld h.vcpu h.sc h.core

/-- The words `top_ok` reads: the bitmaps, the current domain, the head of the highest queue and its thread's. -/
structure TopRd (st : machine.Store S) [L : LawfulStore st] (R : U64 → Prop) (s : S) : Prop where
  l1 : R (L.nodeAt s (L.cpu s) layout.node.L1_BITMAP)
  dom : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN)
  bm : PathObl.RdBitmap (L := L) R s
  top : ∀ d p q, sched.cur_domain st s = ok d → sched.highest_prio st s d = ok p →
    layout.node.READY_QUEUES = ok q →
    R (L.nodeAt s (L.cpu s) (core.num.U64.wrapping_add q (core.num.U64.wrapping_mul p 16#u64))) ∧
    MayRd (L := L) R s (L.mem s (L.nodeAt s (L.cpu s) (core.num.U64.wrapping_add q (core.num.U64.wrapping_mul p 16#u64))))

theorem top_ok.guard {s : S} (h : TopRd st R s) :
    localtimer.top_ok gS s (L.cpu s) = localtimer.top_ok st s (L.cpu s) := by
  unfold localtimer.top_ok
  rw [PathObl.obj.node_get.guard (gS := gS) s _ _ h.l1]
  refine bind_guard_congr rfl fun i _ => ?_
  by_cases h0 : i = 0#u64
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0, PathObl.sched.cur_domain.guard (gS := gS) s h.dom]
  refine bind_guard_congr rfl fun d ed => ?_
  rw [PathObl.sched.highest_prio.guard (gS := gS) s d h.bm]
  refine bind_guard_congr rfl fun p ep => ?_
  simp only [lift, bind_ok]
  refine bind_guard_congr rfl fun q eq => ?_
  obtain ⟨h1, h2⟩ := h.top d p q ed ep eq
  rw [PathObl.obj.node_get.guard (gS := gS) s _ _ h1]
  refine bind_guard_congr rfl fun t et => ?_
  rw [node_get_ok] at et
  rw [← ok_inj_ff et]
  exact h2.guard _

theorem wake_ok.guard {s : S} {ct w n : U64} (hw : MayRd (L := L) R s w) (hd : R (domA w))
    (hq : R (inqA w)) (hn : R (ntfnScA n)) (ht : TopRd st R s) :
    localtimer.wake_ok gS s (L.cpu s) ct w n = localtimer.wake_ok st s (L.cpu s) ct w n := by
  unfold localtimer.wake_ok
  refine bind_guard_congr rfl fun b _ => ?_
  cases b
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  rw [if_pos rfl, if_pos rfl, hw.guard]
  refine bind_guard_congr rfl fun b1 _ => ?_
  cases b1
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  rw [if_pos rfl, if_pos rfl, PathObl.obj.Tcb.domain.guard (gS := gS) w s hd]
  refine bind_guard_congr rfl fun i _ => ?_
  rw [PathObl.sched.cur_domain.guard (gS := gS) s ht.dom]
  refine bind_guard_congr rfl fun i1 _ => ?_
  by_cases hi : i = i1
  swap
  · rw [if_neg hi, if_neg hi]
  rw [if_pos hi, if_pos hi, PathObl.sched.queued.guard (gS := gS) s w hq]
  refine bind_guard_congr rfl fun b2 _ => ?_
  cases b2
  swap
  · rw [if_pos rfl, if_pos rfl]
  rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, PathObl.obj.Tcb.sc.guard (gS := gS) w s hw.sc]
  refine bind_guard_congr rfl fun i2 _ => ?_
  by_cases h2 : i2 = 0#u64
  swap
  · rw [if_neg h2, if_neg h2]; exact top_ok.guard ht
  rw [if_pos h2, if_pos h2, PathObl.obj.Ntfn.sc.guard (gS := gS) n s hn]
  refine bind_guard_congr rfl fun i3 _ => ?_
  by_cases h3 : (i3 != 0#u64) = true
  · rw [if_pos h3, if_pos h3]
  · rw [if_neg h3, if_neg h3]; exact top_ok.guard ht

theorem round_robin_ok.guard {A : Type} (ar : machine.Arch A) {s : S} (a : A) {ct csc now : U64}
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.IDLE_SC)) (h2 : R (core.num.U64.wrapping_add csc layout.sc.PERIOD))
    (h3 : R (stA ct)) (h4 : R (scA ct)) (h5 : R (maxA (L.mem s (scA ct)))) (h6 : R (inqA ct))
    (h7 : R (headA csc)) (h8 : R (tailA csc))
    (h9 : R (rtA csc (L.rhead s csc)) ∧ R (raA csc (L.rhead s csc)))
    (h10 : R (rtA csc (L.rtail s csc)) ∧ R (raA csc (L.rtail s csc)))
    (h11 : R (L.nodeAt s (L.cpu s) layout.node.L1_BITMAP))
    (h12 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN)) (h13 : PathObl.RdBitmap (L := L) R s)
    (h14 : R (core.num.U64.wrapping_add ct 3448#u64)) :
    localtimer.round_robin_ok gS ar s a (L.cpu s) ct csc now =
      localtimer.round_robin_ok st ar s a (L.cpu s) ct csc now := by
  unfold localtimer.round_robin_ok
  rw [PathObl.sched.idle_sc.guard (gS := gS) s h1]
  refine bind_guard_congr rfl fun s1 _ => ?_
  refine bind_guard_congr rfl fun b _ => ?_
  cases b
  swap
  · rw [if_pos rfl, if_pos rfl]
  rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, PathObl.sporadic.is_round_robin.guard (gS := gS) s csc h2]
  refine bind_guard_congr rfl fun b1 _ => ?_
  cases b1
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  rw [if_pos rfl, if_pos rfl, PathObl.sched.is_schedulable.guard (gS := gS) s ct h3 h4 h5 h6]
  refine bind_guard_congr rfl fun b2 _ => ?_
  cases b2
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  rw [if_pos rfl, if_pos rfl, PathObl.sched.queued.guard (gS := gS) s ct h6]
  refine bind_guard_congr rfl fun b3 _ => ?_
  cases b3
  swap
  · rw [if_pos rfl, if_pos rfl]
  rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, PathObl.obj.Sc.refill_head.guard (gS := gS) csc s h7,
    eq_of_spec_fd (obj.Sc.refill_head.spec (L := L) s csc)]
  simp only [bind_ok]
  rw [PathObl.obj.Sc.refill_tail.guard (gS := gS) csc s h8, eq_of_spec_fd (obj.Sc.refill_tail.spec (L := L) s csc)]
  simp only [bind_ok]
  by_cases he : L.rhead s csc = L.rtail s csc
  · rw [if_pos he, if_pos he]
  rw [if_neg he, if_neg he, PathObl.sporadic.get.guard (gS := gS) s csc _ h9.1 h9.2]
  refine bind_guard_congr rfl fun x _ => ?_
  rw [PathObl.sporadic.get.guard (gS := gS) s csc _ h10.1 h10.2]
  refine bind_guard_congr rfl fun y _ => ?_
  by_cases ht : x.time > now
  · rw [if_pos ht, if_pos ht]
  rw [if_neg ht, if_neg ht]
  simp only [lift, bind_ok]
  refine bind_guard_congr rfl fun i1 _ => ?_
  by_cases hm : core.num.U64.wrapping_add x.amount y.amount < i1
  · rw [if_pos hm, if_pos hm]
  rw [if_neg hm, if_neg hm, PathObl.obj.node_get.guard (gS := gS) s _ _ h11]
  refine bind_guard_congr rfl fun i2 _ => ?_
  by_cases h0 : i2 = 0#u64
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0, PathObl.sched.cur_domain.guard (gS := gS) s h12]
  refine bind_guard_congr rfl fun d _ => ?_
  rw [PathObl.sched.highest_prio.guard (gS := gS) s d h13]
  refine bind_guard_congr rfl fun p _ => ?_
  rw [PathObl.obj.Tcb.prio.guard (gS := gS) ct s h14]

end

end Fl4Proofs.P2
