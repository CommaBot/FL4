/-
P3 (DESIGN.md §9), CSpace: the caps CNode Copy, Mint, Move and Mutate put
in the destination name the source's object (`copied_okey`): what
`insert_full_fin` and `move_full_fin` need to keep `FinInv`.
-/
import Fl4Proofs.P3.CnodeShape
import Fl4Proofs.P3.FinOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem mask_okey {r : capability.Rights} {c c' : capability.Cap} (h : capability.mask_cap_rights r c = ok c') :
    okey c' = okey c := by
  cases c <;> simp only [capability.mask_cap_rights] at h
  case Frame p sz v dev m a va =>
    unfold capability.mask_vm_rights at h
    repeat' split at h
    all_goals (simp at h; subst h; simp [okey])
  all_goals (repeat' split at h) <;> (simp at h; subst h; simp [okey])

theorem update_okey {pr : Bool} {d : U64} {c c' : capability.Cap} (h : objects.update_cap_data pr d c = ok c')
    (hn : c' ≠ .Null) : okey c' = okey c := by
  cases c <;> simp only [objects.update_cap_data] at h
  case CNode p r gs g =>
    simp only [lift, bind_ok] at h
    split at h
    · simp at h; subst h; exact absurd rfl hn
    · rw [shr_eq _ _ (by decide) (by decide), objects_mask_eq] at h
      obtain ⟨m, hm, -⟩ := spec_exists (mask_spec (d &&& 63#u64) (by
        have : (d &&& 63#u64).val = d.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod d.val 6
        rw [this]; omega))
      rw [hm] at h; simp at h; subst h; simp [okey]
  all_goals (repeat' split at h) <;> (simp at h; subst h; first | exact absurd rfl hn | simp_all [okey])

section
variable {S : Type} {st : machine.Store S}

theorem derive_okey {s : S} {slot : U64} {c c' : capability.Cap}
    (h : objects.derive_cap st s slot c = ok (.Ok c')) (hn : c' ≠ .Null) : okey c' = okey c := by
  cases c
  case Untyped p sb fi dev =>
    unfold objects.derive_cap at h
    obtain ⟨r, -, h⟩ := bind_ok_inv h
    obtain ⟨cf, -, h⟩ := bind_ok_inv h
    cases cf with
    | Continue _ => simp at h; subst h; rfl
    | Break res =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from] at h
      cases res with
      | Ok x => cases x
      | Err e => simp at h
  all_goals simp only [objects.derive_cap] at h
  all_goals (repeat' split at h) <;> (simp at h; try subst h) <;>
    first | exact absurd rfl hn | simp_all [okey]


/-- The cap `copied_cap` produces, when not null, names the source's object. -/
theorem copied_okey {s : S} {lbl length buf src : U64} {srcC nc : capability.Cap} {mv : Bool}
    (h : cnode.copied_cap st s lbl length buf src srcC = ok (.Ok (nc, mv))) (hn : nc ≠ .Null) :
    okey nc = okey srcC := by
  unfold cnode.copied_cap at h
  obtain ⟨ct, -, h⟩ := bind_ok_inv h
  split at h
  · split at h
    · simp [error.truncated] at h
    obtain ⟨i, -, h⟩ := bind_ok_inv h
    obtain ⟨r, -, h⟩ := bind_ok_inv h
    obtain ⟨c1, hc1, h⟩ := bind_ok_inv h
    obtain ⟨r1, hr1, h⟩ := bind_ok_inv h
    cases r1 with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from] at h
    | Ok v =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at h
      obtain ⟨rfl, rfl⟩ := h
      exact (derive_okey hr1 hn).trans (mask_okey hc1)
  · split at h
    · split at h
      · simp [error.truncated] at h
      obtain ⟨i, -, h⟩ := bind_ok_inv h
      obtain ⟨r, -, h⟩ := bind_ok_inv h
      obtain ⟨d, -, h⟩ := bind_ok_inv h
      obtain ⟨c1, hc1, h⟩ := bind_ok_inv h
      obtain ⟨c2, hc2, h⟩ := bind_ok_inv h
      obtain ⟨r1, hr1, h⟩ := bind_ok_inv h
      cases r1 with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from] at h
      | Ok v =>
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        obtain ⟨rfl, rfl⟩ := h
        have hn2 : c2 ≠ .Null := by
          intro e; subst e; simp [objects.derive_cap] at hr1; exact hn hr1.symm
        exact (derive_okey hr1 hn).trans ((update_okey hc2 hn2).trans (mask_okey hc1))
    · split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
      · split at h
        · simp [error.truncated] at h
        obtain ⟨d, -, h⟩ := bind_ok_inv h
        obtain ⟨c1, hc1, h⟩ := bind_ok_inv h
        simp at h; obtain ⟨rfl, rfl⟩ := h
        exact update_okey hc1 hn

end

end

end Fl4Proofs.P3
