/-
P3 (issue #16, fb-spec-2): **the FL4 extension `X86PML4FrameBatch` in the
spec-invariant families** (spec side only; KENTRY-PLAN fb-spec). The batch's
perform is a loop (`fbRun`, structural recursion on the entries), which the
families' `*_auto` cannot unfold; these combinators reduce `IK P` of the loop
and of `performFrameBatch` to `IK P` of one entry (`fbEntry`, no recursion:
each family proves it with its own `*_auto`) and of the final `flushAll`.
-/
import Fl4Proofs.P3.SpecInvNativeScopeK
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

variable {P : State Unit → Prop}

/-- The loop keeps `P` when every entry does. -/
theorem ik_fbRun {b : Fl4FrameBatchInvocation} (h : ∀ w, IKE P (fbEntry (Z := Unit) b w)) :
    ∀ (ws : List (Data × Data × Data)) (n : Nat) (d : Bool), IK P (fbRun (Z := Unit) b ws n d)
  | [], n, d => ik_pure _
  | w :: ws, n, d => by
    unfold fbRun
    refine ik_bind (h w) fun r => ?_
    cases r with
    | ok d' => exact ik_fbRun h ws (n + 1) (d || d')
    | error c => exact ik_pure _

/-- **The batch keeps `P`** when every entry and the final flush do. -/
theorem ik_performFrameBatch {b : Fl4FrameBatchInvocation} (h : ∀ w, IKE P (fbEntry (Z := Unit) b w))
    (hf : IK P (flushAll (Z := Unit) b.vspace b.asid)) : IK P (performFrameBatch (Z := Unit) b) := by
  unfold performFrameBatch
  refine ik_bind (ik_fbRun h _ _ _) fun r => ?_
  obtain ⟨done, err, d⟩ := r
  exact ik_bind (ik_when _ hf) fun _ => ik_pure _

end

end Fl4Proofs.P3.SInv
