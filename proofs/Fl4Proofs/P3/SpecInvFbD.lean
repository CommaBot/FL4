/-
P3 (issue #16, fb-spec-2): **`X86PML4FrameBatch` in the projection frames
`FK f`** (VsDom's `DK`, SpecInvDomF's `DL`): SpecInvFbK's combinators for
`FK`. The loop keeps `f` when each entry does; the batch when, also, the
final `flushAll` does.
-/
import Fl4Proofs.P3.VsDom
open Classical

namespace Fl4Proofs.P3.Vs
open Fl4Spec

noncomputable section

variable {β : Type} {f : State Unit → β}

theorem fk_fbRun {b : Fl4FrameBatchInvocation} (h : ∀ w, FKE f (fbEntry (Z := Unit) b w)) :
    ∀ (ws : List (Data × Data × Data)) (n : Nat) (d : Bool), FK f (fbRun (Z := Unit) b ws n d)
  | [], n, d => dk_pure _
  | w :: ws, n, d => by
    unfold fbRun
    refine dk_bind (h w) fun r => ?_
    cases r with
    | ok d' => exact fk_fbRun h ws (n + 1) (d || d')
    | error c => exact dk_pure _

theorem fk_performFrameBatch {b : Fl4FrameBatchInvocation} (h : ∀ w, FKE f (fbEntry (Z := Unit) b w))
    (hf : FK f (flushAll (Z := Unit) b.vspace b.asid)) : FK f (performFrameBatch (Z := Unit) b) := by
  unfold performFrameBatch
  refine dk_bind (fk_fbRun h _ _ _) fun r => ?_
  obtain ⟨done, err, d⟩ := r
  refine dk_bind ?_ fun _ => dk_pure _
  unfold NonDet.when
  split
  · exact hf
  · exact dk_pure' _

end

end Fl4Proofs.P3.Vs
