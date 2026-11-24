/-
P3 (issue #16, fb3c), invariant line G1: **the frame batch keeps every
scheduler view and `cfS`** (spec side only), so rd14b's `Cov` arm
`.invokeArchObject _` covers `X86PML4FrameBatch` as it covers the other
VSpace arms.

* `fbEntryX` (SpecFbX: the entry with its frame `cap_delete` written out:
  `is_final_cap`, `arch_finalise_cap` of a frame, `empty_slot slot Null`)
  is an `SVM ∧ CFK` step by `sv_auto` / `cfk_auto` over rd13b's VSpace leaves
  and rd14f's `empty_slot` leaves; `rk_performFrameBatchX` lifts it to the
  batch.
* **`perfA_frameBatch`**: rd13b's `perfA_sve` (no error outcome: the batch
  is lifted).
-/
import Fl4Proofs.P3.SpecInvRd14bB
import Fl4Proofs.P3.SpecFbX
open Classical

namespace Fl4Proofs.P3.SInvR.A13b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b

noncomputable section

set_option maxHeartbeats 4000000

/-! ## `empty_slot` (rd14f E's leaves, copied: that module is downstream of rd14b) -/

theorem svfb_postCapDeletion (c : Cap) : SVK.SVM (postCapDeletion (Z := Unit) c) := by
  unfold postCapDeletion
  split
  · unfold deletedIrqHandler setIrqState; sv_auto
  · unfold archPostCapDeletion
    split
    · unfold freeIoportRange; sv_auto
    · sv_auto
  · sv_auto

theorem cfkfb_postCapDeletion (c : Cap) : CFK (postCapDeletion (Z := Unit) c) := by
  unfold postCapDeletion
  split
  · unfold deletedIrqHandler setIrqState; cfk_auto
  · unfold archPostCapDeletion
    split
    · unfold freeIoportRange; cfk_auto
    · cfk_auto
  · cfk_auto

theorem svfb_emptySlot (sl : CslotPtr) (ci : Cap) : SVK.SVM (emptySlot (Z := Unit) sl ci) := by
  simp only [emptySlot, setCdt]
  sv_auto
  all_goals first | exact svfb_postCapDeletion _ | (unfold setOriginal; sv_auto)
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact svfb_emptySlot _ _)

theorem cfkfb_emptySlot (sl : CslotPtr) (ci : Cap) : CFK (emptySlot (Z := Unit) sl ci) := by
  simp only [emptySlot, setCdt]
  cfk_auto
  all_goals first | exact cfkfb_postCapDeletion _ | (unfold setOriginal; cfk_auto)
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfkfb_emptySlot _ _)

/-- fb3f: by step lemmas (`ik_performFrameBatchW` at `SVS σ0 ·`, transitive), no whole-entry unfolding. -/
theorem svfb_performFrameBatch (b : Fl4FrameBatchInvocation) : SVK.SVM (performFrameBatch (Z := Unit) b) := by
  intro σ0 x hx
  have k : ∀ {α : Type} {m : NonDet (State Unit) α}, SVK.SVM m → IK (fun s => SVK.SVS σ0 s) m :=
    fun h s hs y hy => hs.trans (h s y hy)
  exact ik_performFrameBatchW (P := fun s => SVK.SVS σ0 s) b (fun _ _ _ _ => k (SVK.sv_capInsert _ _ _))
    (fun _ => k (sv13_performPageInvocation _)) (fun _ _ _ _ _ _ _ => k (by simp only [archFinaliseCap]; sv_auto))
    (fun _ => k (svfb_emptySlot _ _))
    (fun _ _ _ _ => k (by unfold unmapPageUnflushed; sv_auto)) (fun _ _ _ => k (SVK.sv_setCap _ _))
    (k (sv13_flushAll _ _)) σ0 (SVK.SVS.refl σ0) x hx

/-- fb3f: by step lemmas (`ik_performFrameBatchW` at `cfS · = cfS σ0`). -/
theorem cfkfb_performFrameBatch (b : Fl4FrameBatchInvocation) : CFK (performFrameBatch (Z := Unit) b) := by
  intro σ0 x hx
  have k : ∀ {α : Type} {m : NonDet (State Unit) α}, CFK m → IK (fun s => cfS s = cfS σ0) m :=
    fun h s hs y hy => (h s y hy).trans hs
  exact ik_performFrameBatchW (P := fun s => cfS s = cfS σ0) b (fun _ _ _ _ => k (cfk_capInsert _ _ _))
    (fun _ => k (cfk_performPageInvocation _)) (fun _ _ _ _ _ _ _ => k (cfk_archFinaliseCap' _ _))
    (fun _ => k (cfkfb_emptySlot _ _))
    (fun _ _ _ _ => k (by unfold unmapPageUnflushed; cfk_auto)) (fun _ _ _ => k (cfk_setCap _ _))
    (k (by unfold flushAll; exact cfk_doMachineOp (Fl4Proofs.P3.MachT.mkf_invalidateASID _ _))) σ0 rfl x hx

/-- **The frame batch** has `PerfA` from `KP σ0 ∧ CB0`. -/
theorem perfA_frameBatch {σ0 s : State Unit} (bl call don : Bool) (i : Fl4FrameBatchInvocation)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) : PerfA σ0 bl call don (.invokeArchObject (.frameBatch i)) s :=
  perfA_sve (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation]
                exact SVK.sve_liftE (svfb_performFrameBatch i))
    (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation]
        intro σ x hx
        obtain ⟨y, hy, rfl⟩ := SInv.fbx_mem_liftE hx
        exact cfkfb_performFrameBatch i σ y hy)
    (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation]; ne_auto) hK hb

end

end Fl4Proofs.P3.SInvR.A13b
