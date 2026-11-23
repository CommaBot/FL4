/-
P3 (issue #16, FL4 #71), VSpace FrameBatch: **one DELETE entry at `J`** (KENTRY-PLAN fb3l):
`frame_batch_entry`'s DELETE arm: the target slot's lookup, a null slot done, a frame cap
(a deferred delete: `unmap_page_unflushed` against `unmapPageUnflushed`, the cleared frame's `set_cap`) then
`cdt.delete` against `fbDelete`, any other cap `IllegalOperation`.
-/
import Fl4Proofs.P3.XTopJointFbDefs
import Fl4Proofs.P3.XTopJointFbDelFrameN
import Fl4Proofs.P3.XTopJointFbDelDefer
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

set_option maxHeartbeats 8000000 in
/-- **One DELETE entry at `J`** (module docstring). OPEN. -/
theorem fb_entry_delJ [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR) (hT : P0.ArchTotal arI) {σ : Fl4Spec.State Unit} {th0 : TypedHeap}
    {ct buf : U64} {args : List U64} {bt : vspace.Batch} {b : Fl4Spec.Fl4FrameBatchInvocation}
    (hDP : JDelParts (L := L) arI AR th0) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (C : FbCtx σ th0 args bt b) (hopC : bt.op ≠ vspace.frame_batch.COPY_MAP) (hopR : bt.op ≠ vspace.frame_batch.REMAP)
    (x : S) (a : A) (τ : Fl4Spec.State Unit) (hM : FbMidJ (L := L) (AR := AR) arI σ th0 ct buf args x a τ)
    (w : Fl4Spec.Data × Fl4Spec.Data × Fl4Spec.Data) (w0 w1 w2 : U64)
    (hw0 : w0.bv = w.1) (hw1 : w1.bv = w.2.1) (hw2 : w2.bv = w.2.2) (df : Bool) :
    vspace.frame_batch_entry st arI x a bt w0 w1 w2 df ⦃ r =>
      FbEntryPost (L := L) (AR := AR) arI σ th0 ct buf args b w τ df r ⦄ := by
  obtain ⟨⟨Z1, H1, Cs1, Ac1, Lst1, D1, hth, hct, hbm, J, hLv⟩, hargs, hK, hns, hsg, hp0⟩ := hM
  subst hth
  have hbop : b.op = .delete := by
    cases e : b.op
    · exact absurd (C.hopC.2 e) hopC
    · exact absurd (C.hopR.2 e) hopR
    · rfl
  obtain ⟨hR, hV, -, -, -⟩ := J.xtop.rel.2.1
  have hM0 : FbMidJ (L := L) (AR := AR) arI σ Z1.th ct buf args x a τ :=
    ⟨⟨Z1, H1, Cs1, Ac1, Lst1, D1, rfl, hct, hbm, J, hLv⟩, hargs, hK, hns, hsg, hp0⟩
  unfold vspace.frame_batch_entry
  rw [if_neg hopC, if_neg hopR]
  rw [show cspace.lookup_target_slot st x bt.cnode w0 bt.depth =
    cspace.lookup_slot_for_cnode_op st x false bt.cnode w0 bt.depth from rfl]
  refine WP.spec_bind (lookup_slot_for_cnode_op_refines (Z := Unit) Z1.th x τ hR hV false bt.cnode b.cnode
    ⟨C.hcw, C.hbc.symm⟩ C.hcv w0 bt.depth) ?_
  rintro r ⟨e, he, hrel⟩
  have hlk : (Fl4Spec.lookupTargetSlot (Z := Unit) b.cnode (Fl4Spec.dataToCptr w.1) b.depth).run τ =
      ({(e, τ)}, False) := by
    rw [← hw0, C.hdep]; exact he
  cases r with
  | Err err =>
    cases e with
    | ok _ => exact hrel.elim
    | error e' =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
      refine ⟨τ, hM0, Or.inr ⟨err, rfl, rfl, ?_⟩⟩
      cases err with
      | Sys e1 =>
        show error.SysError.code e1 ⦃ _ ⦄
        exact WP.spec_mono (code_fb (Or.inl hrel)) fun c hc => by
          rw [hc]; exact fbEntry_del_lookupErr hbop (by rw [hlk]; exact Set.mem_singleton _)
      | _ => cases e' <;> exact hrel.elim
  | Ok sl0 =>
    cases e with
    | error _ => exact hrel.elim
    | ok sl =>
      obtain ⟨rfl, pp, hpp1, hpp, -⟩ := hrel
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have hlkm : (Except.ok sl, τ) ∈ ((Fl4Spec.lookupTargetSlot (Z := Unit) b.cnode (Fl4Spec.dataToCptr w.1)
          b.depth).run τ).1 := by rw [hlk]; exact Set.mem_singleton _
      have hAs : AbsSlot Z1.th sl := ⟨pp, hpp1, Or.inl hpp⟩
      obtain ⟨c, ac, hc, hca, hg⟩ := hR.slot_cap (Z := Unit) hpp1 hpp
      have hac : ac = absCap c := hca.abs
      subst hac
      have hgm : (absCap c, τ) ∈ (Fl4Spec.getCap (Z := Unit) sl τ).1 := by rw [hg]; exact Set.mem_singleton _
      rw [slot_cap_eq, hc]; simp only [bind_ok]
      by_cases hcn : c = .Null
      · subst hcn
        rw [cap_is_null_null]; simp only [bind_ok, ↓reduceIte, WP.spec_ok]
        exact ⟨τ, hM0, Or.inl ⟨rfl, false, fbEntry_del_null hbop hlkm hgm, by simp⟩⟩
      rw [cap_is_null_ne hcn]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
      have hacn : absCap c ≠ .nullCap := fun h => hcn (absCap_eq_null.1 h)
      by_cases hfr : ∃ p sz rt dv mp ep asd va, c = .Frame p sz rt dv mp ep asd va
      swap
      · have ho : vspace.as_frame c = ok none := by
          cases c <;> first | rfl | exact absurd ⟨_, _, _, _, _, _, _, _, rfl⟩ hfr
        rw [ho]; simp only [bind_ok, error.illegal, WP.spec_ok]
        refine ⟨τ, hM0, Or.inr ⟨_, rfl, rfl, ?_⟩⟩
        show error.SysError.code .IllegalOperation ⦃ _ ⦄
        refine WP.spec_mono (code_fb (e' := .illegalOperation) (Or.inl trivial)) fun cc hcc => ?_
        rw [hcc]
        refine fbEntry_del_other hbop hlkm hgm hacn fun dev p R mt sz m h => ?_
        cases c <;> simp [absCap] at h
        exact hfr ⟨_, _, _, _, _, _, _, _, rfl⟩
      obtain ⟨p, sz, rt, dv, mp, ep, asd, va, rfl⟩ := hfr
      simp only [vspace.as_frame, bind_ok]
      have hdd := C.hdd
      have hba := C.hba
      have hpos : bt.asid.bv > 0 := by
        have h := C.h0
        show 0 < bt.asid.bv.toNat
        exact Nat.pos_of_ne_zero (fun e => h (UScalar.eq_of_val_eq (by simpa using e)))
      split_ifs with k1 k2 k3 k4 k5
      pick_goal 3
      · -- the deferred unmap
        try dsimp only
        obtain ⟨⟨b2, sU⟩, hu, -⟩ := spec_exists (P0.vspace.unmap_page_unflushed.p0 st x bt.root sz va p L.total)
        rw [hu]
        try simp only [bind_ok]
        fbj_red
        subst k2
        have k3' : ep = false := by simpa using k3
        have k4' : dv = false := by simpa using k4
        subst k3' k4' k5
        obtain ⟨sS, hs, -⟩ := spec_exists (P0.obj.Slot.set_cap.p0 st (cslotAddr sl) sU
          (.Frame p sz rt false false false 0#u64 0#u64) L.total)
        have hfv := hK.findVs hpos C.hf
        have hdf : b.deferDelete = true ∧
            (if true then (if false then Fl4Spec.VMMapType.vmEptMap else .vmVSpaceMap) else .vmNoMap) =
              .vmVSpaceMap ∧ false = false ∧ bt.asid.bv = b.asid := ⟨by rw [hdd]; exact k1, rfl, rfl, hba.symm⟩
        have hu' := hu
        cases b2 <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, hs] <;> fbj_red <;>
        refine WP.spec_bind (JAtZ.fbDelDeferJ arI J hDP hT hnd hARI hLv hns hsg hp0 hAs hc hfv hu hs) ?_ <;>
        rintro ⟨r1, s4, a4⟩ ⟨hr1, τu, τs, τ1, G', V', Ac', Lst', D', hu1, hs1, hd1, J', hLv', hns', hsg', hp0', hkb,
          hK', hum'⟩ <;>
        fbj_red <;>
        refine (WP.spec_ok _).2 ⟨τ1, FbMidJ.step arI C.hal rfl hct hbm hargs hK J' rfl rfl rfl
          (FbFootK.of_rel arI J J' rfl rfl hK' hum') hK' hLv' hns' hsg' hp0', Or.inl ⟨hr1, _,
          fbEntry_del_frameD hbop hlkm hgm hdf (by rw [C.hbv]; exact hu1) hs1 hd1, by simp⟩⟩
      all_goals
        have hnot : ¬ (bt.defer_delete = true ∧ mp = true ∧ ep = false ∧ dv = false ∧ asd = bt.asid) := by
          rintro ⟨q1, q2, q3, q4, q5⟩; simp_all
        try simp only [bind_ok]
        fbj_red
        refine WP.spec_bind (JAtZ.fbDelFrameJN arI J hDP hT hnd hARI hLv hns hsg hp0 hAs hc rfl) ?_
        rintro ⟨r1, s4, a4⟩ ⟨hr1, σ', G', V', Ac', Lst', D', hd, J', hLv', hns', hsg', hp0', hkb⟩
        fbj_red
        have hcA := (SInvU.getCap_capAt hgm).2
        obtain ⟨hK', hum'⟩ := fbKeep_capDelete_frame hcA hd
        have hndP : ∀ asid' vaddr, (if mp then some (asd.bv, va.bv) else none) = some (asid', vaddr) →
            ¬ (b.deferDelete = true ∧ (if mp then (if ep then Fl4Spec.VMMapType.vmEptMap else .vmVSpaceMap)
              else .vmNoMap) = .vmVSpaceMap ∧ dv = false ∧ asid' = b.asid) := by
          intro a' v hm ⟨h1, h2, h3, h4⟩
          cases mp
          · simp at hm
          · cases ep
            · simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
              obtain ⟨rfl, rfl⟩ := hm
              exact hnot ⟨by rw [← hdd]; exact h1, rfl, rfl, h3, P1.eq_of_bv (h4.trans hba)⟩
            · simp at h2
        exact (WP.spec_ok _).2 ⟨σ', FbMidJ.step arI C.hal rfl hct hbm hargs hK J' rfl rfl rfl
          (FbFootK.of_rel arI J J' rfl rfl hK' hum') hK' hLv' hns' hsg' hp0', Or.inl ⟨hr1, false,
          fbEntry_del_frame hbop hlkm hgm hndP hd, by simp⟩⟩

end

end

end Fl4Proofs.P3
