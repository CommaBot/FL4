/-
# P2: the round-robin case of the timer interrupt: what `round_robin_ok` checked, and the ring after the merge

`round_robin_ok_true`: an accepted `round_robin_ok` (`localtimer.rs`) at state `X` says the current SC is not the
idle SC and is round-robin (period 0), the current thread is schedulable and not queued, the ring has two
distinct refills (head ≠ tail), the head is ready at `now`, the head and tail amounts together reach
`min_budget`, and either the L1 bitmap is empty or the highest priority is below the current thread's.

`cbRR_head`: after `charge_budget`'s ring merge (`cbRR`, `P2/FootTimerIrqRR.lean`) the head index and the period
are kept and the head refill is the old head with the tail's amount added (the tail write is at another index:
`refill_putS_ne`; the SC's `CONSUMED` is outside the ring). `rr_wr_out`: a write outside the SC keeps all three.
`rr_sufficient`: `sufficient(·, 0)` holds once the head's amount reaches `min_budget`.

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqRM
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section law
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **What an accepted `round_robin_ok` checked** (module docstring). -/
theorem round_robin_ok_true {A : Type _} {ar : machine.Arch A} {X : S} {a : A} {cpu ct csc now : U64}
    (h : localtimer.round_robin_ok st ar X a cpu ct csc now = ok true) :
    (∃ isc, sched.idle_sc st X = ok isc ∧ csc ≠ isc) ∧ L.rperiod X csc = 0#u64 ∧
      sched.is_schedulable st X ct = ok true ∧ (L.mem X (inqA ct) &&& sched.Q_QUEUED) = 0#u64 ∧
      L.rhead X csc ≠ L.rtail X csc ∧ (L.refill X csc (L.rhead X csc)).time ≤ now ∧
      (∃ m, sporadic.min_budget ar a = ok m ∧
        m ≤ core.num.U64.wrapping_add (L.refill X csc (L.rhead X csc)).amount
          (L.refill X csc (L.rtail X csc)).amount) ∧
      (L.mem X (L.nodeAt X cpu layout.node.L1_BITMAP) = 0#u64 ∨
        ∃ p, sched.highest_prio st X (L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN)) = ok p ∧
          p < L.mem X (prioA ct)) := by
  unfold localtimer.round_robin_ok at h
  obtain ⟨isc, eisc, h⟩ := bind_eq_ok h
  simp only [obj.Sc.Insts.CoreCmpPartialEqSc.eq, bind_ok] at h
  by_cases h0 : csc = isc
  · simp [h0] at h
  rw [if_neg (by simpa using h0)] at h
  rw [eq_of_spec_fd (sporadic.is_round_robin.spec (L := L) X csc)] at h
  simp only [bind_ok] at h
  by_cases h1 : L.rperiod X csc = 0#u64
  swap
  · simp [h1] at h
  rw [if_pos (by simpa using h1)] at h
  obtain ⟨b2, eb2, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  rw [if_pos rfl] at h
  rw [eq_of_spec_fd (sched.queued.spec (L := L) X ct)] at h
  simp only [bind_ok] at h
  by_cases h3 : (L.mem X (inqA ct) &&& sched.Q_QUEUED) = 0#u64
  swap
  · rw [if_pos (by simp only [decide_eq_true_eq]; exact h3)] at h
    simp at h
  rw [if_neg (by simp only [decide_eq_true_eq, ne_eq, not_not]; exact h3)] at h
  rw [eq_of_spec_fd (obj.Sc.refill_head.spec (L := L) X csc),
    eq_of_spec_fd (obj.Sc.refill_tail.spec (L := L) X csc)] at h
  simp only [bind_ok] at h
  by_cases h4 : L.rhead X csc = L.rtail X csc
  · simp [h4] at h
  rw [if_neg h4] at h
  rw [eq_of_spec_fd (sporadic.get.spec (L := L) X csc (L.rhead X csc)),
    eq_of_spec_fd (sporadic.get.spec (L := L) X csc (L.rtail X csc))] at h
  simp only [bind_ok] at h
  by_cases h5 : (L.refill X csc (L.rhead X csc)).time > now
  · simp [h5] at h
  rw [if_neg h5] at h
  simp only [lift, bind_ok] at h
  obtain ⟨m, em, h⟩ := bind_eq_ok h
  by_cases h6 : core.num.U64.wrapping_add (L.refill X csc (L.rhead X csc)).amount
      (L.refill X csc (L.rtail X csc)).amount < m
  · simp [h6] at h
  rw [if_neg h6, node_get_ok] at h
  simp only [bind_ok] at h
  refine ⟨⟨isc, eisc, h0⟩, h1, eb2, h3, h4, not_lt.1 h5, ⟨m, em, not_lt.1 h6⟩, ?_⟩
  by_cases h7 : L.mem X (L.nodeAt X cpu layout.node.L1_BITMAP) = 0#u64
  · exact Or.inl h7
  right
  rw [if_neg h7, cur_domain_ok] at h
  simp only [bind_ok] at h
  obtain ⟨p, ep, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (obj.Tcb.prio.spec (L := L) X ct)] at h
  simp only [bind_ok] at h
  exact ⟨p, ep, by simpa using ok_inj_ff h⟩

/-- Writing refill `j` leaves refill `i ≠ j` alone. -/
theorem refill_putS_ne {s : S} {sc : obj.Sc} {i j : U64} {r : sporadic.Refill} (h8 : sc.val % 8 = 0)
    (hi : sc.val + 96 + 16 * i.val + 16 ≤ 2 ^ 64) (hj : sc.val + 96 + 16 * j.val + 16 ≤ 2 ^ 64)
    (hij : i.val ≠ j.val) :
    L.refill (L.putS s sc j r) sc i = L.refill s sc i := by
  unfold LawfulStore.refill LawfulStore.putS
  rw [L.mem_wr_ne (by addr) (by addr) (by addr), L.mem_wr_ne (by addr) (by addr) (by addr),
    L.mem_wr_ne (by addr) (by addr) (by addr), L.mem_wr_ne (by addr) (by addr) (by addr)]

/-- **The ring after the round-robin merge** (module docstring). -/
theorem cbRR_head {s s2 : S} {sc : obj.Sc} {z : Nat} {used : U64} (hW : RefillsWF st s sc z)
    (hne : L.rhead s sc ≠ L.rtail s sc) (h : cbRR st s sc used = ok s2) :
    L.rhead s2 sc = L.rhead s sc ∧ L.rperiod s2 sc = L.rperiod s sc ∧
      L.refill s2 sc (L.rhead s sc) = ({ L.refill s sc (L.rhead s sc) with
        amount := core.num.U64.wrapping_add (L.refill s sc (L.rhead s sc)).amount
          (L.refill s sc (L.rtail s sc)).amount } : sporadic.Refill) := by
  unfold cbRR at h
  rw [eq_of_spec_fd (obj.Sc.refill_head.spec (L := L) s sc),
    eq_of_spec_fd (obj.Sc.refill_tail.spec (L := L) s sc)] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (sporadic.get.spec (L := L) s sc (L.rhead s sc)),
    eq_of_spec_fd (sporadic.get.spec (L := L) s sc (L.rtail s sc))] at h
  simp only [bind_ok, lift] at h
  rw [eq_of_spec_fd (sporadic.put.spec (L := L) s sc (L.rhead s sc) _)] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (sporadic.put.spec (L := L) _ sc (L.rtail s sc) _)] at h
  simp only [bind_ok] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (obj.Sc.set_consumed.spec (L := L) _ sc _)] at h
  have e := (ok_inj_ff h).symm
  subst e
  obtain ⟨h8, hm, hfit⟩ := hW.bounds
  have := hW.min_le; simp at this
  have hh := hW.head_lt
  have ht := hW.tail_lt
  have hhi : sc.val + 96 + 16 * (L.rhead s sc).val + 16 ≤ 2 ^ 64 := by omega
  have hti : sc.val + 96 + 16 * (L.rtail s sc).val + 16 ≤ 2 ^ 64 := by omega
  have hcv : (core.num.U64.wrapping_add sc layout.sc.CONSUMED).val = sc.val + 8 := by
    simp [layout.sc.CONSUMED, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have ha : Aligned (core.num.U64.wrapping_add sc layout.sc.CONSUMED) := by unfold Aligned; rw [hcv]; omega
  have eC : ∀ (X : S) (b v : U64), Aligned b → (b.val < sc.val + 8 ∨ sc.val + 8 < b.val) →
      L.mem (L.wr X (core.num.U64.wrapping_add sc layout.sc.CONSUMED) v) b = L.mem X b :=
    fun X b v hb h1 => L.mem_wr_ne ha hb (by omega)
  have hij : (L.rhead s sc).val ≠ (L.rtail s sc).val := fun e => hne (UScalar.eq_of_val_eq e)
  refine ⟨?_, ?_, ?_⟩
  · show L.mem _ (headA sc) = _
    rw [eC _ _ _ (by addr) (by addr)]
    exact (rhead_putS h8 hti).trans (rhead_putS h8 hhi)
  · show L.mem _ (periodA sc) = _
    rw [eC _ _ _ (by addr) (by addr)]
    exact (rperiod_putS h8 hti).trans (rperiod_putS h8 hhi)
  · have rC : ∀ (X : S) (v : U64), L.refill (L.wr X (core.num.U64.wrapping_add sc layout.sc.CONSUMED) v) sc
        (L.rhead s sc) = L.refill X sc (L.rhead s sc) := fun X v => by
      unfold LawfulStore.refill
      rw [eC _ _ _ (by addr) (by addr), eC _ _ _ (by addr) (by addr)]
    rw [rC, refill_putS_ne h8 hhi hti hij, refill_putS_same h8]

/-- **A write outside the SC** keeps the head index, the period and the head refill. -/
theorem rr_wr_out {X : S} {sc : obj.Sc} {z : Nat} {b v : U64} (hW : RefillsWF st X sc z) (hb : Aligned b)
    (hout : Outside b sc z) :
    L.rhead (L.wr X b v) sc = L.rhead X sc ∧ L.rperiod (L.wr X b v) sc = L.rperiod X sc ∧
      L.refill (L.wr X b v) sc (L.rhead X sc) = L.refill X sc (L.rhead X sc) := by
  obtain ⟨h8, hm, hfit⟩ := hW.bounds
  have := hW.min_le; simp at this
  have hh := hW.head_lt
  unfold Outside at hout
  refine ⟨L.mem_wr_ne hb (by addr) (by addr), L.mem_wr_ne hb (by addr) (by addr), ?_⟩
  unfold LawfulStore.refill
  rw [L.mem_wr_ne hb (by addr) (by addr), L.mem_wr_ne hb (by addr) (by addr)]

/-- `sufficient(·, 0)` once the head's amount reaches `min_budget`. -/
theorem rr_sufficient {A : Type _} {ar : machine.Arch A} {X : S} {a : A} {sc : obj.Sc} {m : U64}
    (hm : sporadic.min_budget ar a = ok m) (hle : m ≤ (L.refill X sc (L.rhead X sc)).amount) :
    sporadic.sufficient st ar X a sc 0#u64 = ok true := by
  unfold sporadic.sufficient sporadic.capacity
  rw [eq_of_spec_fd (sporadic.head.spec (L := L) X sc)]
  have n0 : ∀ x : U64, ¬ (0#u64 > x) := fun x => by simp only [gt_iff_lt]; scalar_tac
  simp only [bind_ok, if_neg (n0 _), u64_sub0, hm]
  simp [hle]

end law

end Fl4Proofs.P2
