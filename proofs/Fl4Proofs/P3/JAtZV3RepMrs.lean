/-
P3 (line mmuAD, gen 34): **FL4's 30 report words = the spec's `vmenterFullMrs`** (step 3 of gen 33's plan, the list
equality), and the pure report `repR` (P3/JAtZV3RepSpec) branch by branch.

* `v3_finRange_map`: `(List.finRange 30).map f` as a `List.range` map.
* **`v3_mrs_pend`** (a pending exit, either `full`) and **`v3_mrs_full`** (no pending exit, full-state caller):
  word `i < 30` of what FL4 wrote — the loop's exit/zero words (`exitMrN`), without a saved exit the entry state
  (`rpEntF`), GPRs (`gprOv`) and RFLAGS/interruptibility/CR3/CR2 (`crF`), MR2 masked when full (`rpFullF`), and
  without a pending exit `finish_notification`'s words (`repFinF` with `rpVecOf`) — is `vmenterFullMrs virtKind
  (some vs) full ⟨i, _⟩` (by cases on the flags and on `i`).
* `v3_repR_pend`, `v3_repR_full`, `v3_repR_noneFull`, `v3_repR_short`, `v3_repR_noneShort`: `repR` in each branch.

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3RepTail
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Fl4Spec

theorem v3_finRange_map (f : Fin 30 → Word) :
    (List.finRange 30).map f = (List.range 30).map (fun i => if h : i < 30 then f ⟨i, h⟩ else 0) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
  have hi : i < 30 := by simpa using h1
  rw [dif_pos hi]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem v3_mrs_pend (vs : VcpuState) (full : Bool) (hp : vs.exit.pending = true) (i : Nat) (hi : i < 30) :
    rpFullF full (rpTailF vs (exitMrN (true || vs.exit.valid) vs)) i = vmenterFullMrs virtKind (some vs) full ⟨i, hi⟩ := by
  simp only [vmenterFullMrs]
  by_cases hv : vs.exit.valid = true <;> cases full <;> interval_cases i <;>
    simp [rpFullF, rpTailF, exitMrN, crF, gprOv, rpEntF, hp, hv, vmenterMrIp, vmenterMrCtl,
      vmenterMrIntr, vmenterMrRflags, vmenterMrGuestInt, vmenterMrCr3, vmenterMrCr2, vmenterMrReason,
      vmenterMrQual, vmenterMrGpa, vmenterMrInsnLen]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem v3_mrs_full (vs : VcpuState) (hp : vs.exit.pending = false) (i : Nat) (hi : i < 30) :
    repFinF (rpVecOf vs.exit.valid vs) (rpFullF true (rpTailF vs (exitMrN (false || vs.exit.valid) vs))) i =
      vmenterFullMrs virtKind (some vs) true ⟨i, hi⟩ := by
  simp only [vmenterFullMrs]
  by_cases hv : vs.exit.valid = true <;> interval_cases i <;>
    simp [repFinF, rpVecOf, rpFullF, rpTailF, exitMrN, crF, gprOv, rpEntF, hp, hv, vmenterMrIp,
      vmenterMrCtl, vmenterMrIntr, vmenterMrRflags, vmenterMrGuestInt, vmenterMrCr3, vmenterMrCr2, vmenterMrReason,
      vmenterMrQual, vmenterMrGpa, vmenterMrInsnLen]

theorem v3_mrs_none (i : Nat) (hi : i < 30) :
    repFinF false (exitMrN false default) i = vmenterFullMrs virtKind none true ⟨i, hi⟩ := by
  simp only [vmenterFullMrs]
  interval_cases i <;> simp [repFinF, exitMrN, vmenterMrReason]

theorem v3_repR_pend (x : Tcb) (vs : VcpuState) (bd : Word) (hp : vs.exit.pending = true) :
    repR x (some vs) bd = ⟨(List.range 30).map (rpFullF (repFull x) (rpTailF vs (exitMrN (true || vs.exit.valid) vs))),
      (1#u64 : U64).bv, (0#u64 : U64).bv, true⟩ := by
  unfold repR vmenterReportF
  simp only [hp, not_true_eq_false, false_and, ↓reduceIte]
  rw [v3_finRange_map]
  all_goals first | (congr 1; exact v3_map_congr 30 fun i hi => by rw [dif_pos hi, v3_mrs_pend vs _ hp i hi]) | congr 1 | rfl

theorem v3_repR_full (x : Tcb) (vs : VcpuState) (bd : Word) (hp : vs.exit.pending = false)
    (hf : repFull x = true) :
    repR x (some vs) bd = ⟨(List.range 30).map
      (repFinF (rpVecOf vs.exit.valid vs) (rpFullF true (rpTailF vs (exitMrN (false || vs.exit.valid) vs)))),
      (0#u64 : U64).bv, bd, false⟩ := by
  unfold repR
  rw [hf]
  unfold vmenterReportF
  simp only [hp, Bool.false_eq_true, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte]
  rw [v3_finRange_map]
  all_goals first | (congr 1; exact v3_map_congr 30 fun i hi => by rw [dif_pos hi, v3_mrs_full vs hp i hi]) | congr 1 | rfl

theorem v3_repR_noneFull (x : Tcb) (bd : Word) (hf : repFull x = true) :
    repR x none bd = ⟨(List.range 30).map (repFinF false (exitMrN false default)), (0#u64 : U64).bv, bd, false⟩ := by
  unfold repR
  rw [hf]
  unfold vmenterReportF
  simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte]
  rw [v3_finRange_map]
  all_goals first | (congr 1; exact v3_map_congr 30 fun i hi => by rw [dif_pos hi, v3_mrs_none i hi]) | congr 1 | rfl

theorem v3_repR_short (x : Tcb) (vs : VcpuState) (bd : Word) (hp : vs.exit.pending = false)
    (hf : repFull x = false) :
    repR x (some vs) bd = ⟨[vs.entryIp virtKind, vs.entryCtl virtKind, vs.entryIntr virtKind], (0#u64 : U64).bv, bd,
      false⟩ := by
  unfold repR
  rw [hf]
  unfold vmenterReportF
  simp [hp, vmenterEntryMrs]
  all_goals rfl

theorem v3_repR_noneShort (x : Tcb) (bd : Word) (hf : repFull x = false) :
    repR x none bd = ⟨[0, 0, 0], (0#u64 : U64).bv, bd, false⟩ := by
  unfold repR
  rw [hf]
  unfold vmenterReportF
  simp [vmenterEntryMrs]
  all_goals rfl

end

end

end Fl4Proofs.P3
