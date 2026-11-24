/-
P3 (issue #16, FL4 #71), VSpace FrameBatch: **one REMAP entry at `J`** (KENTRY-PLAN fb3l):
`frame_batch_entry`'s REMAP arm: the source slot's lookup (`lookup_source_slot` against the spec's
`lookupSourceSlot`, Lookup's `lookup_slot_for_cnode_op_refines`), then `batch_map` against `fbMap`
(XTopJointFbMapJ's `JAtZ.batchMapJ`), `FbMidJ` after by `FbMidJ.step`.

* `fb_code`: FL4's error code of a related error is the spec's label (`msgFromSyscallError`), as
  ReplyFailX's `code_label` without the label mask.
* `fbEntry_remap`: the spec's entry at a REMAP batch.
-/
import Fl4Proofs.P3.XTopJointFbMapJL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section


/-- **FL4's error code is the spec's label** (`ErrRel` or the alignment error). -/
theorem fb_code {e : error.SysError} {e' : Fl4Spec.SyscallError}
    (he : ErrRel (.Sys e) e' ∨ (e = .AlignmentError ∧ e' = .alignmentError)) :
    error.SysError.code e ⦃ c => c.bv = (Fl4Spec.msgFromSyscallError e').1 ⦄ := by
  rcases he with (h | ⟨n, he, rfl⟩) | ⟨rfl, rfl⟩
  · cases e <;> cases e' <;> simp only [SysErrRel] at h <;>
      simp only [error.SysError.code, WP.spec_ok, Fl4Spec.msgFromSyscallError, fl4_abi.consts.error.InvalidArgument,
        fl4_abi.consts.error.IllegalOperation, fl4_abi.consts.error.RangeError, fl4_abi.consts.error.AlignmentError,
        fl4_abi.consts.error.FailedLookup, fl4_abi.consts.error.TruncatedMessage, fl4_abi.consts.error.DeleteFirst,
        fl4_abi.consts.error.RevokeFirst, fl4_abi.consts.error.NotEnoughMemory] <;> decide
  · cases he
    simp only [error.SysError.code, WP.spec_ok, Fl4Spec.msgFromSyscallError, fl4_abi.consts.error.InvalidCapability]
    decide
  · simp only [error.SysError.code, WP.spec_ok, Fl4Spec.msgFromSyscallError, fl4_abi.consts.error.AlignmentError]
    decide

theorem fbr_branch_ok {α β : Type} (x : α) :
    core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Ok x : core.result.Result α β) =
      ok (core.ops.control_flow.ControlFlow.Continue x) := rfl

theorem fbr_branch_err {α β : Type} (e : β) :
    core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Err e : core.result.Result α β) =
      ok (core.ops.control_flow.ControlFlow.Break (core.result.Result.Err e)) := rfl

theorem fbr_fromResidual (e : error.Exc) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
      (core.convert.FromSame error.Exc) (core.result.Result.Err e) = ok (core.result.Result.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
    core.convert.FromSame.from]

section Spec
open Fl4Spec

theorem fbEntry_remap {b : Fl4FrameBatchInvocation} (h : b.op = .remap) (w : Data × Data × Data) :
    fbEntry (Z := Unit) b w = (do
      let slot ← fbCode <| lookupSourceSlot b.cnode (dataToCptr w.1) b.depth
      fbCode <| fbMap b slot w.2.1
      NonDetE.returnOk false) := by
  unfold fbEntry; rw [h]

theorem fbCode_err {α : Type} {m : SEMonad Unit α} {σ : State Unit} {e : SyscallError}
    (h : ExceptT.run m σ = ({(.error e, σ)}, False)) :
    ExceptT.run (fbCode m) σ = ({(.error (msgFromSyscallError e).1, σ)}, False) := by
  unfold fbCode; rw [runE_handle_err h]; rfl

theorem fbCode_ok {α : Type} {m : SEMonad Unit α} {σ : State Unit} {x : α}
    (h : ExceptT.run m σ = ({(.ok x, σ)}, False)) :
    ExceptT.run (fbCode m) σ = ({(.ok x, σ)}, False) := by
  unfold fbCode; exact runE_handle_ok h

theorem fbCode_mem {α : Type} {m : SEMonad Unit α} {σ σ' : State Unit} {x : α}
    (h : ((.ok x, σ') : Except SyscallError α × State Unit) ∈ (ExceptT.run m σ).1) :
    ((.ok x, σ') : Except Data α × State Unit) ∈ (ExceptT.run (fbCode m) σ).1 := by
  unfold fbCode NonDetE.handleE
  rw [ExceptT.run_mk]
  exact ⟨_, h, rfl⟩

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 8000000 in
/-- **One REMAP entry at `J`** (module docstring). -/
theorem fb_entry_remapJ [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR) (hT : P0.ArchTotal arI) {σ : Fl4Spec.State Unit} {th0 : TypedHeap}
    {ct buf : U64} {args : List U64} {bt : vspace.Batch} {b : Fl4Spec.Fl4FrameBatchInvocation}
    (C : FbCtx σ th0 args bt b) (hopC : bt.op ≠ vspace.frame_batch.COPY_MAP) (hopR : bt.op = vspace.frame_batch.REMAP)
    (x : S) (a : A) (τ : Fl4Spec.State Unit) (hM : FbMidJ (L := L) (AR := AR) arI σ th0 ct buf args x a τ)
    (w : Fl4Spec.Data × Fl4Spec.Data × Fl4Spec.Data) (w0 w1 w2 : U64)
    (hw0 : w0.bv = w.1) (hw1 : w1.bv = w.2.1) (hw2 : w2.bv = w.2.2) (df : Bool) :
    vspace.frame_batch_entry st arI x a bt w0 w1 w2 df ⦃ r =>
      FbEntryPost (L := L) (AR := AR) arI σ th0 ct buf args b w τ df r ∧ CnSlotsKept (L := L) th0 x r.2.1 ⦄ := by
  unfold FbEntryPost
  obtain ⟨p1, as1, op, depth, a1, cr, a2, dd, cn, dcn⟩ := bt
  obtain ⟨⟨Z1, H1, Cs1, Ac1, Lst1, D1, hth, hct, hbm, J, hLv⟩, hargs, hK, hns, hsg, hp0⟩ := id hM
  have hbop : b.op = .remap := C.hopR.1 hopR
  have hX := J.xtop
  obtain ⟨-, hCR, -, -, -, -, -⟩ := id hX.rel
  obtain ⟨hSt, hSV, -, -, -⟩ := id hCR
  have hcv : CapValid Z1.th cn := by rw [hth]; exact C.hcv
  have hpos : as1.bv > 0 := by
    have : as1.val ≠ 0 := fun h => C.h0 (UScalar.eq_of_val_eq (by simpa using h))
    show 0 < as1.bv.toNat
    exact Nat.pos_of_ne_zero this
  have hf : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) as1.bv) τ = ({(.ok p1.bv, τ)}, False) :=
    hK.findVs hpos C.hf
  have hE : Fl4Spec.fbEntry (Z := Unit) b w = _ := fbEntry_remap hbop w
  unfold vspace.frame_batch_entry
  simp only at hopC hopR ⊢
  rw [if_neg hopC, if_pos hopR, lookup_source_eq]
  refine WP.spec_bind (lookup_slot_for_cnode_op_refines (Z := Unit) Z1.th x τ hSt hSV true cn (absCap cn)
    ⟨C.hcw, rfl⟩ hcv w0 depth) ?_
  rintro r1 ⟨e1, he1, hrel1⟩
  have hls : ExceptT.run (Fl4Spec.lookupSourceSlot (Z := Unit) b.cnode (Fl4Spec.dataToCptr w.1) b.depth) τ =
      ({(e1, τ)}, False) := by rw [C.hbc, C.hdep, ← hw0]; exact he1
  cases r1 with
  | Err e =>
    cases e1 with
    | ok _ => exact hrel1.elim
    | error e' =>
      simp only [fbr_branch_err, bind_ok, fbr_fromResidual]
      refine (WP.spec_ok _).2 ⟨⟨τ, hM, Or.inr ⟨e, rfl, rfl, ?_⟩⟩, CnSlotsKept.refl _ _⟩
      have hrun : ((Fl4Spec.fbEntry (Z := Unit) b w).run τ) = ({(.error (Fl4Spec.msgFromSyscallError e').1, τ)}, False) := by
        rw [hE]; exact runE_bind_err (fbCode_err hls)
      cases e with
      | Sys e2 =>
        refine WP.spec_mono (fb_code (Or.inl (Or.inl hrel1))) fun c hc => ?_
        rw [hrun, hc]; exact Set.mem_singleton _
      | _ => exact hrel1.elim
  | Ok sl =>
    cases e1 with
    | error _ => exact hrel1.elim
    | ok sl' =>
      obtain ⟨rfl, pc, hpc1, hpc, -⟩ := hrel1
      obtain ⟨sa, idx⟩ := sl'
      simp only at hpc1 hpc
      subst hpc1
      simp only [fbr_branch_ok, bind_ok]
      have hrun1 : (Fl4Spec.fbEntry (Z := Unit) b w).run τ = ExceptT.run (Fl4Spec.fbCode (Fl4Spec.fbMap (Z := Unit) b
          (pc.bv, idx) w.2.1) >>= fun _ => Fl4Spec.NonDetE.returnOk false) τ := by
        rw [hE]; exact runE_bind_ok (fbCode_ok hls)
      refine WP.spec_bind (JAtZ.batchMapJL arI hA J hLv hns hsg hp0 hpc rfl C.h0 C.hasid hf op depth a1 cr a2 dd cn dcn w1 b C.hbv
        C.hba C.hmr C.hat) ?_
      rintro ⟨r2, s2, a2'⟩ (⟨e, e', h1, h2, h3, h4, h5⟩ | ⟨h1, τ1, hmem, J', hK1, hF, hLv1, hns1, hsg1, hp01, hCSK⟩)
      · simp only at h1 h4 h5
        subst h1 h4 h5
        fbj_red
        refine (WP.spec_ok _).2 ⟨⟨τ, hM, Or.inr ⟨e, rfl, rfl, ?_⟩⟩, CnSlotsKept.refl _ _⟩
        have hrun : ((Fl4Spec.fbEntry (Z := Unit) b w).run τ) =
            ({(.error (Fl4Spec.msgFromSyscallError e').1, τ)}, False) := by
          rw [hrun1, ← hw1]; exact runE_bind_err (fbCode_err h3)
        cases e with
        | Sys e2 =>
          have h2' : ErrRel (.Sys e2) e' ∨ (e2 = .AlignmentError ∧ e' = .alignmentError) := by
            rcases h2 with h | ⟨he2, rfl⟩
            · exact Or.inl h
            · cases he2; exact Or.inr ⟨rfl, rfl⟩
          refine WP.spec_mono (fb_code h2') fun c hc => ?_
          rw [hrun, hc]; exact Set.mem_singleton _
        | _ => rcases h2 with (h | ⟨n, h, -⟩) | ⟨h, -⟩ <;> cases h
      · simp only at h1
        subst h1
        fbj_red
        refine (WP.spec_ok _).2 ⟨⟨τ1, FbMidJ.step arI (a := a) (H1 := H1) (Cs1 := Cs1) (Ac1 := Ac1) (Lst1 := Lst1) (D1 := D1)
          C.hal hth hct hbm hargs hK J' rfl rfl rfl hF hK1 hLv1 hns1 hsg1 hp01,
          Or.inl ⟨rfl, false, ?_, by simp⟩⟩, hth ▸ hCSK⟩
        rw [hrun1]
        exact mem_bindE_ok (fbCode_mem (by rw [← hw1]; exact hmem)) (Set.mem_singleton _)

end

end

end Fl4Proofs.P3
