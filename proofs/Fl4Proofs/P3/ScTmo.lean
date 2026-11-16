/-
P3, scheduling contexts: **`charge_budget`'s `hval` from the CSpace
relation**. `valid_timeout_handler` reads only the current thread's
timeout-handler slot, and the budget path keeps it and the spec's handler
(`TmoKeep`, ScCharge1: the path writes scheduler, node and SC words only).
So the `hval` of `budget_ok_refines` and `entry_check_budget_refines`
follows from `StateRel` at the entry (`hval_of_rel`, through
`valid_timeout_handler_rel`'s reading of the slot).
-/
import Fl4Proofs.P3.IpcTimeout
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`valid_timeout_handler` at a state keeping the entry's slot and
handler** (`TmoKeep`), from `StateRel` at the entry. -/
theorem hval_of_rel {th : TypedHeap} (hP : Placed th) {s0 : S} {σ0 : Fl4Spec.State Unit}
    (hR : StateRel th (L.mem s0) σ0) {ct : U64} (ht : th ct = some .tcb) :
    ∀ (s : S) (σ : Fl4Spec.State Unit), TmoKeep st ct s0 σ0 s σ →
      faults.valid_timeout_handler st s ct ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) ct.bv σ = ({(b, σ)}, False) ⦄ := by
  intro s σ hK
  obtain ⟨x0, c, hkx0, hc, hca⟩ := hR.timeoutCap ht
  obtain ⟨x, hkx, he⟩ := hK.2 x0 hkx0
  have hal := hP.align ct _ ht
  have hfit := hP.fits ct _ ht
  simp only [objSize] at hfit
  have hsv : (slotOf ct 4).val = ct.val + 128 := slotOf_val (by omega)
  have h8v : (core.num.U64.wrapping_add (slotOf ct 4) 8#u64).val = ct.val + 136 := by
    rw [wordOf_val (by rw [hsv]; simp; omega), hsv]; simp
  have e1 : L.mem s (slotOf ct 4) = L.mem s0 (slotOf ct 4) :=
    hK.1 _ (by unfold Aligned; rw [hsv]; omega) (by rw [hsv]; try omega) (by rw [hsv]; try omega)
  have e2 : L.mem s (core.num.U64.wrapping_add (slotOf ct 4) 8#u64) =
      L.mem s0 (core.num.U64.wrapping_add (slotOf ct 4) 8#u64) :=
    hK.1 _ (by unfold Aligned; rw [h8v]; omega) (by rw [h8v]; try omega) (by rw [h8v]; try omega)
  have hc' : capAt (L.mem s) (slotOf ct 4) = ok c := by unfold capAt; rw [e1, e2]; exact hc
  unfold faults.valid_timeout_handler
  rw [Endp.tcb_slot_timeout]
  apply Endp.ok_bind_spec
  rw [slot_cap_eq, hc']
  apply Endp.ok_bind_spec
  have hx := hca.2
  rw [← he] at hx
  cases c <;> exact (WP.spec_ok _).2 (by rw [Endp.isValidTimeoutHandler_eq hkx, ← hx]; simp [absCap, Fl4Spec.isEpCap])

end

end

end Fl4Proofs.P3.Sched
