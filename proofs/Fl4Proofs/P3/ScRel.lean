/-
P3 (DESIGN.md §9), scheduling contexts: the relation of one SC object.

FL4's SC (layout.rs `sc`): words `PERIOD` 0, `CONSUMED` 8, `CORE` 16,
`TCB` 24, `REPLY` 32, `NTFN` 40, `BADGE` 48, `YIELD_FROM` 56, `SPORADIC` 64,
`REFILL_MAX` 72, `REFILL_HEAD` 80, `REFILL_TAIL` 88, then the refill ring
(16 bytes per refill). P1 (Refill.lean) views the ring as a list,
`L.refills s sc` (oldest first), under `RefillsWF` (head and tail index a
ring of `REFILL_MAX` refills, `MIN_REFILLS ≤ REFILL_MAX`, the object is
placed, `2 ^ sb` bytes).

`ScRel1 st s sc x n` relates it to the spec's `.schedContext x n`:
`RefillsWF st s sc n`; `sc_period`, `sc_consumed`, `sc_badge` are the
words; `sc_tcb`, `sc_ntfn`, `sc_yield_from` the pointer words (0 ↔ none);
`sc_sporadic` ↔ the `SPORADIC` word is nonzero; `sc_refill_max` is
`REFILL_MAX`; `sc_refills` is the ring as a list.

Not related: `sc_budget` (FL4 does not store the budget; the spec only reads
it in `refill_new`/`refill_update`-level configuration and the refill
invariants), `sc_replies` (FL4 keeps the head of the reply stack in `REPLY`
and links the stack through the replies; the reply subsystem relates it),
and FL4's `CORE` (no spec counterpart: single core).

`ScIn st s sc a`: `a` is one of the words the relation reads (header and
the `REFILL_MAX` ring slots). `ScRel1.agree`: the relation only depends on
them.
-/
import Fl4Proofs.P3.Ntfn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} (st : machine.Store S) [L : LawfulStore st]

/-- Word `K` of the SC at `sc`. -/
def scW (sc K : U64) : U64 := core.num.U64.wrapping_add sc K

/-- FL4's refill as the spec's. -/
def toRefill (r : sporadic.Refill) : Fl4Spec.Refill := ⟨r.time.bv, r.amount.bv⟩

/-- The words of the SC at `sc` the relation reads. -/
def ScIn (s : S) (sc a : U64) : Prop := sc.val ≤ a.val ∧ a.val < sc.val + 96 + 16 * (L.rmax s sc).val

/-- The SC at `sc` and the spec's `.schedContext x n`. -/
structure ScRel1 (s : S) (sc : U64) (x : Fl4Spec.SchedContext) (n : Nat) : Prop where
  wf : RefillsWF st s sc n
  period : x.scPeriod = (L.rperiod s sc).bv
  consumed : x.scConsumed = (L.mem s (scW sc 8#u64)).bv
  tcb : x.scTcb = optRef (L.mem s (scW sc 24#u64))
  ntfn : x.scNtfn = optRef (L.mem s (scW sc 40#u64))
  badge : x.scBadge = (L.mem s (scW sc 48#u64)).bv
  yieldFrom : x.scYieldFrom = optRef (L.mem s (scW sc 56#u64))
  sporadic : x.scSporadic = decide (L.mem s (scW sc 64#u64) ≠ 0#u64)
  max : (L.rmax s sc).val = x.scRefillMax
  refills : x.scRefills = (L.refills s sc).map toRefill

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem scW_val {sc K : U64} (h : sc.val + K.val < 2 ^ 64) : (scW sc K).val = sc.val + K.val := by
  simp [scW, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-- Facts about the placement of a related SC. -/
theorem ScRel1.bounds {s : S} {sc : U64} {x : Fl4Spec.SchedContext} {n : Nat} (h : ScRel1 st s sc x n) :
    sc.val % 8 = 0 ∧ 2 ≤ (L.rmax s sc).val ∧ sc.val + 96 + 16 * (L.rmax s sc).val ≤ 2 ^ 64 := by
  obtain ⟨h8, hm, hfit⟩ := h.wf.bounds
  have := h.wf.min_le; simp at this
  exact ⟨h8, this, by omega⟩

/-- A header word of a related SC (offset `K < 96`, a multiple of 8): aligned
and read by the relation. -/
theorem ScRel1.hdr {s : S} {sc : U64} {x : Fl4Spec.SchedContext} {n : Nat} (h : ScRel1 st s sc x n) {K : U64}
    (hK : K.val < 96) (hK8 : K.val % 8 = 0) : Aligned (scW sc K) ∧ ScIn st s sc (scW sc K) := by
  obtain ⟨h8, h2, hfit⟩ := h.bounds
  have hv := scW_val (sc := sc) (K := K) (by omega)
  exact ⟨by unfold Aligned; rw [hv]; omega, by unfold ScIn; rw [hv]; omega⟩

theorem maxA_eq (sc : U64) : maxA sc = scW sc 72#u64 := by unfold maxA scW layout.sc.REFILL_MAX; rfl
theorem headA_eq (sc : U64) : headA sc = scW sc 80#u64 := by unfold headA scW layout.sc.REFILL_HEAD; rfl
theorem tailA_eq (sc : U64) : tailA sc = scW sc 88#u64 := by unfold tailA scW layout.sc.REFILL_TAIL; rfl
theorem periodA_eq (sc : U64) : periodA sc = scW sc 0#u64 := by unfold periodA scW layout.sc.PERIOD; rfl

/-- Memory that agrees on the words of the SC at `sc`. -/
def ScAgree (st : machine.Store S) [L : LawfulStore st] (s s' : S) (sc : U64) : Prop :=
  ∀ a, Aligned a → ScIn st s sc a → L.mem s' a = L.mem s a

/-- The relation only reads `ScIn`. -/
theorem ScRel1.agree {s s' : S} {sc : U64} {x : Fl4Spec.SchedContext} {n : Nat} (h : ScRel1 st s sc x n)
    (ha : ScAgree st s s' sc) : ScRel1 st s' sc x n := by
  obtain ⟨h8, h2, hfit⟩ := h.bounds
  have hw : ∀ K : U64, K.val < 96 → K.val % 8 = 0 → L.mem s' (scW sc K) = L.mem s (scW sc K) :=
    fun K h1 h2 => ha _ (h.hdr h1 h2).1 (h.hdr h1 h2).2
  have em : L.rmax s' sc = L.rmax s sc := by
    simp only [LawfulStore.rmax, maxA_eq]; exact hw _ (by simp) (by simp)
  have eh : L.rhead s' sc = L.rhead s sc := by
    simp only [LawfulStore.rhead, headA_eq]; exact hw _ (by simp) (by simp)
  have et : L.rtail s' sc = L.rtail s sc := by
    simp only [LawfulStore.rtail, tailA_eq]; exact hw _ (by simp) (by simp)
  have ep : L.rperiod s' sc = L.rperiod s sc := by
    simp only [LawfulStore.rperiod, periodA_eq]; exact hw _ (by simp) (by simp)
  have hW' : RefillsWF st s' sc n := h.wf.of_hdr em (by rw [eh]; exact h.wf.head_lt) (by rw [et]; exact h.wf.tail_lt)
  have hsz : L.size s' sc = L.size s sc := by simp only [LawfulStore.size, em, eh, et]
  have hrf : ∀ k, L.rf s' sc k = L.rf s sc k := by
    intro k
    have hix : L.ix s' sc k = L.ix s sc k := by simp only [LawfulStore.ix, em, eh]
    have hk := h.wf.ix_lt k
    obtain ⟨-, -, -, -, -, hin⟩ := h.wf.inside
    obtain ⟨h1, h2', h3⟩ := hin _ hk
    unfold LawfulStore.rf LawfulStore.refill
    rw [hix, ha _ (by unfold Aligned; rw [h1]; omega) (by unfold ScIn; rw [h1]; omega),
      ha _ (by unfold Aligned; rw [h2']; omega) (by unfold ScIn; rw [h2']; omega)]
  have hrs : L.refills s' sc = L.refills s sc := by
    simp only [LawfulStore.refills, hsz]
    exact List.map_congr_left (fun k _ => hrf k)
  exact ⟨hW', by rw [ep]; exact h.period, by rw [hw _ (by simp) (by simp)]; exact h.consumed,
    by rw [hw _ (by simp) (by simp)]; exact h.tcb, by rw [hw _ (by simp) (by simp)]; exact h.ntfn,
    by rw [hw _ (by simp) (by simp)]; exact h.badge, by rw [hw _ (by simp) (by simp)]; exact h.yieldFrom,
    by rw [hw _ (by simp) (by simp)]; exact h.sporadic, by rw [em]; exact h.max, by rw [hrs]; exact h.refills⟩

theorem ScIn.agree {s s' : S} {sc a : U64} (hm : L.rmax s' sc = L.rmax s sc) (h : ScIn st s sc a) :
    ScIn st s' sc a := by unfold ScIn; rw [hm]; exact h

end

end

end Fl4Proofs.P3.Sched
