/-
# `vcpu.decode` never preempts (FL4 #104, line lvm)

`lvm_decode_np`: a run of `vcpu.decode` never returns `Err Preempted`, for every
label and with no invariant: its error leaves are `error.illegal` / `truncated` /
`invalid_arg` (all `Sys`), and its two `?` exits forward `sanitize_vmcs` /
`sanitize_vmcb` errors, which are `invalid_arg` too (`lvm_sanitize_vmcs_np`,
`lvm_sanitize_vmcb_np`). Used by `P1/LocalVmInvoke` (the general
`handle_invocation` and the local reply arm differ only on `Err Preempted`).

The proofs walk backwards from the result (`FastDecline`'s `decl_walk` style:
`spec_bind_imp` / `spec_ite_imp` / `split` at the head of the goal, no
simplification of the whole body), with the error constructors and the
sanitizers' results kept (`np_bind_val`). No premise, no totality needed.
-/
import Fl4Proofs.P1.LocalVmEnter
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- A bind whose first action's results all satisfy `Q` (goal-directed walks). -/
theorem np_bind_val {α β : Type _} {m : Result α} {f : α → Result β} {P : β → Prop} {G : Prop}
    {Q : α → Prop} (hm : ∀ x, m = ok x → Q x) (h : ∀ x, Q x → f x ⦃ P ⦄ → G) :
    (Std.bind m f) ⦃ P ⦄ → G := fun hb => by
  obtain ⟨x, hx, hf⟩ := spec_bind_inv hb; exact h x (hm x hx) hf

/-- `np_bind_val` for the typeclass bind. -/
theorem np_bind_val' {α β : Type _} {m : Result α} {f : α → Result β} {P : β → Prop} {G : Prop}
    {Q : α → Prop} (hm : ∀ x, m = ok x → Q x) (h : ∀ x, Q x → f x ⦃ P ⦄ → G) :
    (m >>= f) ⦃ P ⦄ → G := np_bind_val hm h

theorem np_illegal (T : Type _) :
    ∀ x, error.illegal T = ok x → x = .Err (.Sys .IllegalOperation) := by
  intro x hx; unfold error.illegal at hx; exact (ok_inj_ff hx).symm

theorem np_truncated (T : Type _) :
    ∀ x, error.truncated T = ok x → x = .Err (.Sys .TruncatedMessage) := by
  intro x hx; unfold error.truncated at hx; exact (ok_inj_ff hx).symm

theorem np_invalid_arg (T : Type _) (n : U64) :
    ∀ x, error.invalid_arg T n = ok x → x = .Err (.Sys (.InvalidArgument n)) := by
  intro x hx; unfold error.invalid_arg at hx; exact (ok_inj_ff hx).symm

/-- The walk. -/
syntax "np_walk" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| np_walk) => `(tactic| repeat' (first
      | ((with_reducible refine np_bind_val (m := error.illegal _) (np_illegal _) (fun _ hq => ?_)); subst hq)
      | ((with_reducible refine np_bind_val' (m := error.illegal _) (np_illegal _) (fun _ hq => ?_)); subst hq)
      | ((with_reducible refine np_bind_val (m := error.truncated _) (np_truncated _) (fun _ hq => ?_)); subst hq)
      | ((with_reducible refine np_bind_val' (m := error.truncated _) (np_truncated _) (fun _ hq => ?_)); subst hq)
      | ((with_reducible refine np_bind_val (m := error.invalid_arg _ _) (np_invalid_arg _ _) (fun _ hq => ?_)); subst hq)
      | ((with_reducible refine np_bind_val' (m := error.invalid_arg _ _) (np_invalid_arg _ _) (fun _ hq => ?_)); subst hq)
      | ((with_reducible refine np_bind_val (m := vcpu.sanitize_vmcs _ _ _ _) (lvm_sanitize_vmcs_np _ _ _ _) (fun x hq => ?_));
         rcases x with _ | _ <;>
         simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           core.convert.FromSame.from, bind_tc_ok])
      | ((with_reducible refine np_bind_val (m := vcpu.sanitize_vmcb _ _ _ _ _) (lvm_sanitize_vmcb_np _ _ _ _ _) (fun x hq => ?_));
         rcases x with _ | _ <;>
         simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           core.convert.FromSame.from, bind_tc_ok])
      | ((with_reducible_and_instances refine spec_bind_imp (fun _ => ?_)); try simp only [uncurry_eta_fd])
      | ((with_reducible_and_instances refine spec_bind_imp' (fun _ => ?_)); try simp only [uncurry_eta_fd])
      | (with_reducible refine spec_ite_imp (fun _ => ?_) (fun _ => ?_))
      | split))

theorem np_leaf3 {S A : Type _} {v r : core.result.Result Unit error.Exc} {s s' : S} {a a' : A}
    (hv : v ≠ .Err .Preempted) : (ok (v, s, a) : Result _) ⦃ x => x = (r, s', a') ⦄ → r ≠ .Err .Preempted := by
  intro h; rw [WP.spec_ok] at h; rw [← (Prod.mk.inj h).1]; exact hv

theorem np_leaf1 {v r : core.result.Result U64 error.Exc}
    (hv : v ≠ .Err .Preempted) : (ok v : Result _) ⦃ x => x = r ⦄ → r ≠ .Err .Preempted := by
  intro h; rw [WP.spec_ok] at h; rw [← h]; exact hv

theorem np_leaf_inv {r : core.result.Result U64 error.Exc} (n : U64) :
    error.invalid_arg U64 n ⦃ x => x = r ⦄ → r ≠ .Err .Preempted := by
  intro h; unfold error.invalid_arg at h; rw [WP.spec_ok] at h; rw [← h]; simp

/-- A leaf of `np_walk`: `ok (r, …)` matched against the run's result. -/
syntax "np_leaf" : tactic
macro_rules
  | `(tactic| np_leaf) => `(tactic| first
      | exact np_leaf_inv _
      | ((first | refine np_leaf3 ?_ | refine np_leaf1 ?_); first
          | assumption
          | (intro h; cases h; contradiction)
          | (simp; done)))

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- `sanitize_vmcs` fails only with `invalid_arg`. -/
theorem lvm_sanitize_vmcs_np (a : A) (f value : U64) :
    ∀ r, vcpu.sanitize_vmcs ar a f value = ok r → r ≠ .Err .Preempted := by
  intro r hr
  have h' := spec_of_eq_fd hr
  clear hr
  revert h'
  unfold vcpu.sanitize_vmcs
  np_walk
  all_goals np_leaf

set_option maxHeartbeats 4000000 in
/-- `sanitize_vmcb` fails only with `invalid_arg`. -/
theorem lvm_sanitize_vmcb_np (a : A) (f old value : U64) :
    ∀ r, vcpu.sanitize_vmcb ar a f old value = ok r → r ≠ .Err .Preempted := by
  intro r hr
  have h' := spec_of_eq_fd hr
  clear hr
  revert h'
  unfold vcpu.sanitize_vmcb
  np_walk
  all_goals np_leaf

set_option maxHeartbeats 8000000 in
/-- **`vcpu.decode` never returns `Err Preempted`.** -/
theorem lvm_decode_np {s s' : S} {a a' : A} {lbl len v : U64} {call : Bool} {buf : U64}
    {ex : Aeneas.Std.Array obj.Slot 3#usize} {r : core.result.Result Unit error.Exc}
    (hd : vcpu.decode st ar s a lbl len v call buf ex = ok (r, s', a')) :
    r ≠ .Err .Preempted := by
  have h' := spec_of_eq_fd hd
  clear hd
  revert h'
  unfold vcpu.decode
  np_walk
  all_goals np_leaf

end

end Fl4Proofs.P1
