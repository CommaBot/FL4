/-
# P2 (line invj, generation 5): the Delete PTE arm's leaf is in pte's reachability convention (`ptesR_of_spe`)

pte gen 8's convention `K.ptes := ptesR K m` (P2/PteReach.lean: the leaf entries the x86 walk reaches in the
epoch-start memory `m`). The Delete PTE arm's leaf `e` is the plan's `small_page_entry asid vaddr` at the entry
(`del_coreP` / `DelEntP`): `find_vspace_for_asid` found a root and `lookup_pt_slot` found `e`, for a user address.
That is `ptesR_of_run`'s input, so at a bundle state agreeing with `m` on the gate words (`GateAg`; a start state of
the epoch is one, pte's E2EPRStart) the leaf is in `ptesR K m`:

* **`ptesR_of_spe`**. No named premise. No existing statement changes.

This is the `e ∈ K.ptes` fact the PTE arm's `ownP` path needs (rule 8: `e` owned by `.lock e`), under pte's
convention, not a convention of this line's own.
-/
import Fl4Proofs.P2.InvDelPteAcc
import Fl4Proofs.P2.PteReach
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P3.Vs (UserV)

section bundle
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A' : Type} {arI : machine.Arch A'}
  {AR : A' → Fl4Spec.Cr3 → Prop} {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64}
  {D : Set U64} {σ : S} {a' : A'} {τ : Fl4Spec.State Unit} {K : KLayoutP} {m : U64 → U64}

/-- (invj gen 5) **A found small-page entry is in the reachability convention** (module docstring). -/
theorem ptesR_of_spe (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σ a' τ) (hag : GateAg st K m σ)
    (nv : K.vcpus = ∅) {asid va e : U64}
    (hc : localinv.small_page_entry st σ asid va = ok (some e)) : e ∈ ptesR K m := by
  unfold localinv.small_page_entry at hc
  obtain ⟨r, hr, hc⟩ := bind_eq_ok hc
  cases r with
  | Err e0 =>
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual] at hc
    exact absurd (ok_inj_ff hc) (by simp)
  | Ok root =>
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok] at hc
    unfold localinv.page_entry at hc
    by_cases hu : va > fl4_abi.consts.USER_TOP
    · rw [if_pos hu] at hc
      exact absurd (ok_inj_ff hc) (by simp)
    · rw [if_neg hu] at hc
      have hv : UserV va := by
        unfold UserV
        have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
        have : ¬ fl4_abi.consts.USER_TOP.val < va.val := hu
        omega
      unfold vspace.small_page_entry at hc
      obtain ⟨r2, hr2, hc⟩ := bind_eq_ok hc
      cases r2 with
      | Err e2 =>
        simp only [core.result.Result.ok] at hc
        exact absurd (ok_inj_ff hc) (by simp)
      | Ok x =>
        simp only [core.result.Result.ok] at hc
        have hx : x = e := Option.some.inj (ok_inj_ff hc)
        subst hx
        exact ptesR_of_run B hag nv hr hv hr2

end bundle

end Fl4Proofs.P2.E2EP
