/-
P3 (DESIGN.md §9): **P1's `CapTyped` across the cap transformations**:
`mask_cap_rights`, `update_cap_data` and `derive_cap` keep the object an
endpoint, notification or reply cap names (`mask_typed`, `update_typed`,
`derive_typed`), so a derived cap is `CapTyped` when its source is.
-/
import Fl4Proofs.P3.ScPlace
import Fl4Proofs.P3.MdbStepOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1

noncomputable section

section
variable {H : Heap} {Rp Nt : Set U64}

theorem mask_typed {r : capability.Rights} {c c' : capability.Cap} (h : capability.mask_cap_rights r c = ok c')
    (hv : CapTyped H Rp Nt c) : CapTyped H Rp Nt c' := by
  have hnull : CapTyped H Rp Nt .Null :=
    ⟨fun _ _ _ _ _ _ e => (by cases e), fun _ _ _ _ e => (by cases e), fun _ _ e => (by cases e)⟩
  cases c <;> simp only [capability.mask_cap_rights] at h
  case Frame p sz v dev m ept a va =>
    unfold capability.mask_vm_rights at h
    repeat' split at h
    all_goals (simp at h; subst h)
    all_goals exact ⟨fun _ _ _ _ _ _ e => (by cases e), fun _ _ _ _ e => (by cases e), fun _ _ e => (by cases e)⟩
  all_goals (repeat' split at h)
  all_goals (simp at h; try subst h)
  all_goals first
    | exact hv
    | exact hnull
    | (refine ⟨fun _ _ _ _ _ _ e => ?_, fun _ _ _ _ e => ?_, fun _ _ e => ?_⟩ <;> cases e <;>
        first
        | exact hv.1 _ _ _ _ _ _ rfl
        | exact hv.2.1 _ _ _ _ rfl
        | exact hv.2.2 _ _ rfl)

theorem update_typed {pr : Bool} {d : U64} {c c' : capability.Cap} (h : objects.update_cap_data pr d c = ok c')
    (hv : CapTyped H Rp Nt c) : CapTyped H Rp Nt c' := by
  have hcn : ∀ p r gs g, CapTyped H Rp Nt (.CNode p r gs g) :=
    fun _ _ _ _ => ⟨fun _ _ _ _ _ _ e => (by cases e), fun _ _ _ _ e => (by cases e), fun _ _ e => (by cases e)⟩
  have hnull : CapTyped H Rp Nt .Null :=
    ⟨fun _ _ _ _ _ _ e => (by cases e), fun _ _ _ _ e => (by cases e), fun _ _ e => (by cases e)⟩
  cases c <;> simp only [objects.update_cap_data] at h
  case CNode p r gs g =>
    simp only [lift, bind_ok] at h
    split at h
    · simp at h; subst h; exact hnull
    · revert h; generalize d >>> 6#i32 = x; cases x <;> simp
      generalize objects.mask (d &&& 63#u64) = y; cases y <;> simp
      intro h; subst h; exact hcn _ _ _ _
  all_goals (repeat' split at h)
  all_goals (simp at h; try subst h)
  all_goals first
    | exact hv
    | exact hnull
    | (refine ⟨fun _ _ _ _ _ _ e => ?_, fun _ _ _ _ e => ?_, fun _ _ e => ?_⟩ <;> cases e <;>
        first
        | exact hv.1 _ _ _ _ _ _ rfl
        | exact hv.2.1 _ _ _ _ rfl
        | exact hv.2.2 _ _ rfl)

theorem derive_typed {S : Type} {st : machine.Store S} {s : S} {slot : obj.Slot} {c c' : capability.Cap}
    (h : objects.derive_cap st s slot c = ok (.Ok c')) (hv : CapTyped H Rp Nt c) : CapTyped H Rp Nt c' := by
  have hnull : CapTyped H Rp Nt .Null :=
    ⟨fun _ _ _ _ _ _ e => (by cases e), fun _ _ _ _ e => (by cases e), fun _ _ e => (by cases e)⟩
  cases c
  case Untyped p sb fi dev =>
    unfold objects.derive_cap at h
    revert h; generalize cdt.ensure_no_children st s slot = r
    cases r with
    | ret v =>
      cases v <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      intro h; subst h; exact hv
    | _ => simp
  case Frame p sz r dv m ept a va =>
    simp only [objects.derive_cap] at h; simp at h; subst h
    exact ⟨fun _ _ _ _ _ _ e => (by cases e), fun _ _ _ _ e => (by cases e), fun _ _ e => (by cases e)⟩
  all_goals simp only [objects.derive_cap] at h
  all_goals (repeat' split at h)
  all_goals (simp at h; try subst h)
  all_goals first
    | exact hv
    | exact hnull
    | (refine ⟨fun _ _ _ _ _ _ e => ?_, fun _ _ _ _ e => ?_, fun _ _ e => ?_⟩ <;> cases e <;>
        first
        | exact hv.1 _ _ _ _ _ _ rfl
        | exact hv.2.1 _ _ _ _ rfl
        | exact hv.2.2 _ _ rfl)

end

end

end Fl4Proofs.P3.Sched
