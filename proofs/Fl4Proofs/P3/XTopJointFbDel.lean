/-
P3 (issue #16, FL4 #71), VSpace FrameBatch: **one DELETE entry at `J`** (KENTRY-PLAN fb3l):
`frame_batch_entry`'s DELETE arm: the target slot's lookup, a null slot done, a frame cap
(a deferred delete: `unmap_page_unflushed` against `unmapPageUnflushed`, the cleared frame's `set_cap`) then
`cdt.delete` against `fbDelete`, any other cap `IllegalOperation`.
-/
import Fl4Proofs.P3.XTopJointFbDefs
import Fl4Proofs.P3.XTopJointFbDelFrame
import Fl4Proofs.P3.SpecFbKeepDel
import Fl4Proofs.P3.SpecFbDelRun
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- FL4's error code is the spec's reply label (ReplyFailX's `code_label` unmasked). -/
theorem code_fb {e : error.SysError} {e' : Fl4Spec.SyscallError} (he : ErrRel (.Sys e) e') :
    error.SysError.code e ⦃ c => c.bv = (Fl4Spec.msgFromSyscallError e').1 ⦄ := by
  rcases he with h | ⟨n, he, rfl⟩
  · cases e <;> cases e' <;> simp only [SysErrRel] at h <;>
      simp only [error.SysError.code, WP.spec_ok, Fl4Spec.msgFromSyscallError, fl4_abi.consts.error.InvalidArgument,
        fl4_abi.consts.error.IllegalOperation, fl4_abi.consts.error.RangeError, fl4_abi.consts.error.AlignmentError,
        fl4_abi.consts.error.FailedLookup, fl4_abi.consts.error.TruncatedMessage, fl4_abi.consts.error.DeleteFirst,
        fl4_abi.consts.error.RevokeFirst, fl4_abi.consts.error.NotEnoughMemory] <;> decide
  · cases he
    simp only [error.SysError.code, WP.spec_ok, Fl4Spec.msgFromSyscallError, fl4_abi.consts.error.InvalidCapability]
    decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`FbMidJ` with the deletion's liveness facts** (KENTRY-PLAN fb3l): the frame delete at `J`
runs at XTopJointWJL's `WJL` (`LiveDN` at the state's MDB ghost, `NoSwitch`, `SpecGlob`, `PPR0`), as
the CNode Delete does from `JEntryAt.live`; the batch's loop must carry them. -/
def FbLiveJ (σ : Fl4Spec.State Unit) (th0 : TypedHeap) (ct buf : U64) (args : List U64) (x : S) (a : A)
    (τ : Fl4Spec.State Unit) : Prop :=
  (∃ (Z1 : XSets) (H1 : P1.Heap) (Cs1 Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
    Z1.th = th0 ∧ ct ∈ Z1.T ∧ (buf ≠ 0#u64 → ∃ sp, BufMap Z1.B buf sp) ∧
    JAtZ (L := L) arI AR Z1 H1 Cs1 Ac1 Lst1 D1 x a τ ∧ LiveDN (L := L) Z1.th H1 Cs1 Z1.G x τ) ∧
  (∀ (i : U64) v, args[i.val]? = some v → msg.syscall_arg st x ct buf i = ok v) ∧
  FbKeep σ τ ∧ Vs.NoSwitch τ ∧ SpecGlob τ ∧ PPR0 τ

theorem FbLiveJ.mid {σ : Fl4Spec.State Unit} {th0 : TypedHeap} {ct buf : U64} {args : List U64} {x : S} {a : A}
    {τ : Fl4Spec.State Unit} (h : FbLiveJ (L := L) (AR := AR) arI σ th0 ct buf args x a τ) :
    FbMidJ (L := L) (AR := AR) arI σ th0 ct buf args x a τ :=
  by
  obtain ⟨⟨Z1, H1, Cs1, Ac1, Lst1, D1, h1, h2, h3, J, -⟩, h4, h5, -⟩ := h
  exact ⟨⟨Z1, H1, Cs1, Ac1, Lst1, D1, h1, h2, h3, J⟩, h4, h5⟩

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
