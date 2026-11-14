/-
P3 (DESIGN.md §9), CSpace: **the CNode CancelBadgedSends invocation** in
full (FL4 `cnode::decode_cancel_badged_sends`) against l4v
`decode_cnode_invocation` (the `CNodeCancelBadgedSends` branch) followed
by `set_thread_state Restart` and `invoke_cnode`, including a non-zero
badge.

`cnode_other_refines` covers only a zero badge, where neither side does
anything. Here the endpoint side, FL4's `endpoint::cancel_badged_sends`
against the spec's `cancel_badged_sends`, is the hypothesis `CancelEpHyp`:
from the state after `set_thread_state`, FL4 leaves every cap slot as it
was (`SlotsSame`), and the spec has a single outcome that is related to
FL4's and keeps the CDT and the originality map.
-/
import Fl4Proofs.P3.CnodeOther
import Fl4Proofs.P3.CancelKSub
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The endpoint side of CancelBadgedSends (a hypothesis): from any FL4
state `s1` that agrees with `s` on cap slots and the spec state `σ1` after
`set_thread_state Restart`, FL4's `cancel_badged_sends` keeps every cap
slot, and the spec's `cancel_badged_sends` has a single outcome, related
to FL4's, with the same CDT and originality map. -/
def CancelEpHyp (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ s1 σ1 (p b : U64), b ≠ 0#u64 → SlotsSame th (L.mem s) (L.mem s1) →
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
    StateRel th (L.mem s1) σ1 →
    endpoint.cancel_badged_sends st s1 p b ⦃ s2 =>
      SlotsSame th (L.mem s1) (L.mem s2) ∧ ∃ σ2,
        Fl4Spec.cancelBadgedSends (Z := Unit) p.bv b.bv σ1 = ({((), σ2)}, False) ∧
        StateRel th (L.mem s2) σ2 ∧ σ2.cdt = σ1.cdt ∧ σ2.isOriginalCap = σ1.isOriginalCap ⦄

/-- **CNode CancelBadgedSends**, decode and invoke, for any badge: FL4's
`cnode::decode` at label `CNodeCancelBadgedSends` against l4v's
`decode_cnode_invocation`, then `set_thread_state Restart` and
`invoke_cnode`, given the endpoint side `CancelEpHyp`. -/
theorem cnode_cancel_refines {A : Type} (arI : machine.Arch A) (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeCancelBadgedSends)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (cap : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel cap a) (hcv : CapValid th cap)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List Fl4Spec.Cap)
    (hI : MdbInv (L.mem s) G) (hFI : FinInv th (L.mem s) σ G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hEp : CancelEpHyp (L := L) th s σ) :
    cnode.decode st arI s ar fl4_abi.label.CNodeCancelBadgedSends length cap buf extra ⦃ res =>
      InvPost (L := L) th σ G (Fl4Spec.decodeCnodeInvocation slbl (args.map UScalar.bv) a excaps) s
        (res.1, res.2.1) ⦄ := by
  have hin : Fl4Spec.genInvocationType slbl ∈
      Fl4Spec.GenInvocationLabels.uptoEnum .cnodeRevoke .cnodeRotate := by rw [hlbl]; decide
  unfold cnode.decode
  have n1 : ¬ fl4_abi.label.CNodeCancelBadgedSends < fl4_abi.label.CNodeRevoke := by
    have := lbl_revoke_val; have := lbl_cancel_val; scalar_tac
  have n2 : ¬ fl4_abi.label.CNodeCancelBadgedSends > fl4_abi.label.CNodeRotate := by
    have := lbl_cancel_val; have := lbl_rotate_val; scalar_tac
  rw [if_neg n1, if_neg n2]
  by_cases h2 : length < 2#u64
  · rw [if_pos h2]
    simp only [error.truncated, bind_ok]
    rw [WP.spec_ok]
    exact ⟨rfl, .truncatedMessage, decode_short _ _ _ σ hin _ (by simp; scalar_tac), trivial⟩
  rw [if_neg h2]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | [_] => exfalso; simp at hlen; scalar_tac
    | y0 :: y1 :: rest => exact ⟨y0, y1, rest, rfl⟩
  simp only [hct, hargs 0#u64 y0 (by simp), hargs 1#u64 y1 (by simp), bind_ok]
  unfold cspace.lookup_target_slot
  obtain ⟨r1, hr1, e1, he1, hrel1⟩ := spec_exists
    (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hR hV false cap a hca hcv y0 y1)
  rw [hr1]; simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  have hlt : (Fl4Spec.lookupTargetSlot (Z := Unit) a (Fl4Spec.dataToCptr y0.bv) (Fl4Spec.dataToNat y1.bv)).run σ =
      ({(e1, σ)}, False) := he1
  have hdec := decode_lookup slbl a excaps hin y0.bv y1.bv (rest.map UScalar.bv)
  simp only [List.map_cons]
  rw [hdec]
  cases r1 with
  | Err e =>
    cases e1 with
    | ok _ => exact hrel1.elim
    | error e' =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.from, bind_ok, bind_tc_ok]
      rw [WP.spec_ok]
      exact ⟨rfl, e', run_bind_error hlt _, hrel1⟩
  | Ok dest =>
    cases e1 with
    | error _ => exact hrel1.elim
    | ok dsl =>
      obtain ⟨rfl, pd, hpd1, hpd⟩ := hrel1
      have g1 : ¬ fl4_abi.label.CNodeCancelBadgedSends ≥ fl4_abi.label.CNodeCopy := by
        have := lbl_copy_val; have := lbl_cancel_val; scalar_tac
      have k1 : ¬ fl4_abi.label.CNodeCancelBadgedSends = fl4_abi.label.CNodeRevoke := by rw [u64_eq_iff]; simp
      have k2 : ¬ fl4_abi.label.CNodeCancelBadgedSends = fl4_abi.label.CNodeDelete := by rw [u64_eq_iff]; simp
      simp only [g1, k1, k2, ↓reduceIte, bind_ok]
      have hAd : AbsSlot th dsl := ⟨pd, hpd1, Or.inl hpd⟩
      obtain ⟨c, ad, hc, hcad, hgd⟩ := hR.slot_cap (Z := Unit) hpd1 hpd
      unfold cnode.decode_cancel_badged_sends
      obtain ⟨o, ho, hoe, hos⟩ := full_endpoint_rel c
      simp only [slot_cap_eq, hc, bind_ok, ho]
      rw [hcad.abs] at hgd
      have hsp : (copyTail slbl (rest.map UScalar.bv) excaps dsl).run σ =
          (Fl4Spec.NonDetE.unlessE (Fl4Spec.hasCancelSendRights (absCap c))
            (Fl4Spec.NonDetE.throwError .illegalOperation) >>= fun _ =>
            Fl4Spec.NonDetE.returnOk (Fl4Spec.CnodeInvocation.cancelBadgedSendsCall (absCap c))).run σ := by
        rw [copyTail_cancel _ _ _ _ hlbl, run_bind_ok (run_liftE hgd)]
      cases o with
      | none =>
        have hn : ¬ Fl4Spec.hasCancelSendRights (absCap c) := by simp [hos]
        simp only [error.illegal, bind_ok, uncurry_apply_pair]
        rw [WP.spec_ok]
        refine ⟨rfl, .illegalOperation, ?_, trivial⟩
        rw [run_bind_ok hlt, hsp]
        simp only [Fl4Spec.NonDetE.unlessE, hn, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
      | some pb =>
        obtain ⟨p, b⟩ := pb
        have hce := (hoe p b).1 rfl
        subst hce
        have hy : Fl4Spec.hasCancelSendRights (absCap (.Endpoint p b true true true true)) := by simp [hos]
        -- `set_thread_state`, on both sides
        have hts := set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact
        obtain ⟨s2, hs2, hS⟩ := spec_exists hts
        obtain ⟨tcb, hk, -⟩ := hR.tcb ct htcb
        rw [← hcur] at hk
        obtain ⟨σ1, hst, hR1, hV1, hM1, hC1, hcdt1, hio1⟩ := restart_rel hR hV hM hC hS hk .restart
        have hI1 := MdbInv.of_same hM hI hS
        have hFI1 := hFI.of_same hM hS (ksub_of_eq (setThreadState_nks _ _) hst)
        have hdec' : (Fl4Spec.lookupTargetSlot (Z := Unit) a (Fl4Spec.dataToCptr y0.bv)
            (Fl4Spec.dataToNat y1.bv) >>= fun d => copyTail slbl (rest.map UScalar.bv) excaps d).run σ =
            ({(.ok (.cancelBadgedSendsCall (absCap (.Endpoint p b true true true true))), σ)}, False) := by
          rw [run_bind_ok hlt, hsp]
          simp only [Fl4Spec.NonDetE.unlessE, hy, ↓reduceIte, ndE_pure_bind]; rfl
        simp only [uncurry_apply_pair, hct, bind_ok, hs2]
        by_cases hb : b = 0#u64
        · subst hb
          simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok, uncurry_apply_pair]
          rw [WP.spec_ok]
          refine ⟨_, hdec', σ1, hst, σ1, G, ?_, hR1, hV1, hM1, hC1, hI1, hFI1⟩
          show (Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
            (.endpointCap p.bv (0#u64 : U64).bv (rightsOf true true true true)))).run σ1 = _
          unfold Fl4Spec.invokeCnode Fl4Spec.withoutPreemption
          simp only [Fl4Spec.NonDet.when]
          have : ¬ ((0#u64 : U64).bv ≠ 0) := by simp
          simp only [this, ↓reduceIte]
          exact run_liftE rfl
        have hbn : (b != 0#u64) = true := by simpa using hb
        have hbv : b.bv ≠ 0 := by
          intro h; apply hb; apply UScalar.eq_of_val_eq
          have := congrArg BitVec.toNat h; simpa using this
        simp only [hbn, ↓reduceIte]
        obtain ⟨s3, hs3, hS3, σ2, hcb, hR2, hcdt2, hio2⟩ := spec_exists (hEp s2 σ1 p b hb hS hst hR1)
        rw [hs3]; simp only [bind_ok, uncurry_apply_pair]
        rw [WP.spec_ok]
        have hcap : ∀ x, IsSlot th x → capAt (L.mem s3) x = capAt (L.mem s2) x := fun x hx => hS3.capAt hx
        refine ⟨_, hdec', σ1, hst, σ2, G, ?_, hR2, hV1.of_caps hcap, hM1.of_same hS3,
          hC1.of_same hS3 hcdt2 hio2, MdbInv.of_same hM1 hI1 hS3,
          hFI1.of_same hM1 hS3 (ksub_of_eq (cancelBadgedSends_nks _ _) hcb)⟩
        show (Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
          (.endpointCap p.bv b.bv (rightsOf true true true true)))).run σ1 = _
        unfold Fl4Spec.invokeCnode Fl4Spec.withoutPreemption
        simp only [Fl4Spec.NonDet.when, hbv, ne_eq, not_false_eq_true, ↓reduceIte]
        exact run_liftE' hcb

end

end

end Fl4Proofs.P3
