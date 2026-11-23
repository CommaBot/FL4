/-
P3 (issue #16, FL4 #71), VSpace FrameBatch: **one DELETE entry at `J`** (KENTRY-PLAN fb3l):
`frame_batch_entry`'s DELETE arm: the target slot's lookup, a null slot done, a frame cap
(a deferred delete: `unmap_page_unflushed` against `unmapPageUnflushed`, the cleared frame's `set_cap`) then
`cdt.delete` against `fbDelete`, any other cap `IllegalOperation`.
-/
import Fl4Proofs.P3.XTopJointFbDefs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 8000000 in
/-- **One DELETE entry at `J`** (module docstring). OPEN. -/
theorem fb_entry_delJ (hA : ArchRefines arI AR) (hT : P0.ArchTotal arI) {σ : Fl4Spec.State Unit} {th0 : TypedHeap}
    {ct buf : U64} {args : List U64} {bt : vspace.Batch} {b : Fl4Spec.Fl4FrameBatchInvocation}
    (C : FbCtx σ th0 args bt b) (hopC : bt.op ≠ vspace.frame_batch.COPY_MAP) (hopR : bt.op ≠ vspace.frame_batch.REMAP)
    (x : S) (a : A) (τ : Fl4Spec.State Unit) (hM : FbMidJ (L := L) (AR := AR) arI σ th0 ct buf args x a τ)
    (w : Fl4Spec.Data × Fl4Spec.Data × Fl4Spec.Data) (w0 w1 w2 : U64)
    (hw0 : w0.bv = w.1) (hw1 : w1.bv = w.2.1) (hw2 : w2.bv = w.2.2) (df : Bool) :
    vspace.frame_batch_entry st arI x a bt w0 w1 w2 df ⦃ r =>
      FbEntryPost (L := L) (AR := AR) arI σ th0 ct buf args b w τ df r ⦄ := by
  fail "FB3 OPEN: the FrameBatch DELETE entry (KENTRY-PLAN fb3l)"

end

end

end Fl4Proofs.P3
