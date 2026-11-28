/-
P3 (p3J gen 39): **the CNode CancelBadgedSends leaf at stable ghosts, with its `ProjW` footprint, for both
classes**; the rest set {CNode at Revoke / Delete, Thread}.

* `cn_cancel_topJSt`: XTopJointLiveCn's `cn_cancel_topJL` with the post `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)`
  (no `LiveDN` needed): the caller's restart by P3JStepFt's `stepClosed_jatW` (`JAtZ` at `Z.mv G1 V1` and the
  restart's `ProjW` footprint), the cancel by XTopJointCbs's `JAtZ.cancelBadgedJ` (at `Z.mv G1 V'`) and P3JCbsFt's
  `JAtZ.cbsProjW`, joined by `projW_trans`.
* `decode_cnode_cancelJSt`: `decode_invocation_cnode_cancelJL`'s route (CnodeCancel's `cnode_cancel_dec`) at that
  post.
* **`decCnCbsSt`** (any flags): at a dispatch state, label 27, at
  `X := JStab (Z.mv Z.G V') H Cs ∧ WritesIn s' · (ProjW H Cs s')`; the endpoints' `EpQPre` at the dispatch state
  as a hypothesis (supplied by XTopJointKEntry27b's `epQPre_of_sinv` from `SInvX`'s `epQAll`), the switch target
  none (`Entered`), the endpoint of a full-rights endpoint cap among `Z.E` (`JAtZ.jpl`, `hset`); `MR` by
  `XCapP.mrT` with `MKD.decode_cnode_nrd` / `MachT.dec_cnode_q`; never preempted (`cnode_noPre_of`).
* `CnDel l`: `l` is 25 (Revoke) or 26 (Delete). `IsRestCap8 cp l`: a CNode cap with `CnDel l`, or a Thread cap.
  `restCap7_of8`, `restCap8_of`. **`midDecRest7_of_cbs`** / **`invDecRest7_of_cbs`** (`MidDecStWL` / `InvDecStWL`
  at `KW ∧ IsRestCap7` from the leaf and the same at `KW ∧ IsRestCap8`), `midDecStWL_of_7` / `invDecStWL_of_7`.
* **`DispStabFootLza` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap8`, midSpec, midRecvSw verbatim};
  **`dispStabFootLz_of_Lza`**, **`dispStabFootLza_of_Lz`** (honesty, proved); top **`kernel_entry_runMcWKR_sysLza`**
  (globals verbatim as `_sysLz`).

Premise honesty: `DispStabFootLza`'s decode fields are `DispStabFootLz`'s at the smaller antecedent
(`IsRestCap8 cp l → IsRestCap7 cp l`), midSpec / midRecvSw verbatim: implied by `DispStabFootLz`
(`dispStabFootLza_of_Lz`) and implying it given the tops' platform facts (`dispStabFootLz_of_Lza`).

Named premise: `DispStabFootLza` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JCbsFt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 39) The CNode labels left: Revoke (25), Delete (26). -/
def CnDel (l : U64) : Prop := 25 ≤ l.val ∧ l.val ≤ 26

/-- (p3J gen 39) The caps left after the CancelBadgedSends leaf, with the message label. -/
def IsRestCap8 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, _ => True
  | _, _ => False

theorem restCap8_of {cp : capability.Cap} {l : U64} (h : IsRestCap7 cp l)
    (hS : ¬ ∃ p r gs g, cp = .CNode p r gs g ∧ l.val = 27) : IsRestCap8 cp l := by
  cases cp
  case CNode p r gs g =>
    show CnDel l
    have h' : CnHard l := h
    unfold CnHard at h'; unfold CnDel
    have : l.val ≠ 27 := fun e => hS ⟨p, r, gs, g, rfl, e⟩
    omega
  all_goals first | trivial | exact False.elim h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
  {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 39) **A CancelBadgedSends's outcome at stable ghosts, with its `ProjW` footprint** (module
docstring; XTopJointLiveCn's `cn_cancel_topJL`). -/
theorem cn_cancel_topJSt (hAM : ARMask arI AR) {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s)) (hC : CurRun σ)
    {ct : U64} (hcur : σ.curThread = ct.bv) (hQ : ∀ e, EpQPre σ e)
    (hsw : ∀ u, σ.schedulerAction = .switchThread u → u ≠ ct.bv)
    (hE : ∀ (e b : U64) (sl : Fl4Spec.CslotPtr), AbsSlot Z.th sl →
      capV (L.mem s) (cslotAddr sl) = .Endpoint e b true true true true → e ∈ Z.E)
    {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (hq : CancelDec (L := L) Z.th ct σ m s (res.1, res.2.1) ∧ res.2.2 = ar) :
    TopPostDMX (L := L) (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) σ blk call don
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m) s res := by
  obtain ⟨r, s', a'⟩ := res
  obtain ⟨hq, rfl⟩ := hq
  cases r with
  | Err e =>
    obtain ⟨rfl, e', h1, h2⟩ := hq
    exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ⟨J.stab, P1.WritesIn.refl _ _⟩⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, p, b, rfl, ⟨sl, hsl, hcV⟩, s2, hs2, h0, h1⟩ := hq
    obtain ⟨htcb, x, hk⟩ := J.xtop.curTcb hcur
    have hrn : Fl4Spec.runnable x.tcbState = true := hC x (by rw [hcur]; exact hk)
    have hσ1 : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
      have hst' := hst
      rw [hcur, Notif.setThreadState_eq .restart hk] at hst'
      have := congrArg (fun q => ((), σ1) ∈ q.1) hst'
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
      simpa using this.symm
    obtain ⟨⟨G1, V1, Ac1, Lst1, D1, J1, -⟩, W1⟩ := (stepClosed_jatW arI hAM (jStepHyps arI)).restart s a' σ ct x s2
      hcur hk htcb hrn hs2 Z H Cs Ac Lst D rfl J hZB
    rw [← hσ1] at J1
    by_cases hb : b = 0#u64
    · subst hb
      have e := h0 rfl
      subst e
      have hrun0 : (Fl4Spec.invokeCnode (Z := Unit)
          (.cancelBadgedSendsCall (absCap (.Endpoint p 0#u64 true true true true)))).run σ1 =
          ({(.ok (), σ1)}, False) := by
        show (Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
          (.endpointCap p.bv (0#u64 : U64).bv (rightsOf true true true true)))).run σ1 = _
        unfold Fl4Spec.invokeCnode Fl4Spec.withoutPreemption
        simp only [Fl4Spec.NonDet.when]
        have : ¬ ((0#u64 : U64).bv ≠ 0) := by simp
        simp only [this, ↓reduceIte]
        exact run_liftE rfl
      have hx : ((.ok (), σ1) : Except Unit Unit × Fl4Spec.State Unit) ∈
          ((Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
            (absCap (.Endpoint p 0#u64 true true true true)))).run σ1).1 := by rw [hrun0]; rfl
      exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ1),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨_, _, Or.inl ⟨rfl, rfl⟩, J1.xtop.rel.1, J1.xtop.rel.2.1,
          J1.xtop.rel.2.2.1, J1.xtop.rel.2.2.2.1, J1.xtop.rel.2.2.2.2.1⟩, ⟨⟨G1, V1, Ac1, Lst1, D1, J1⟩, W1⟩⟩
    · have hcb := h1 hb
      have he : p ∈ (Z.mv G1 V1).E := hE p b sl hsl hcV
      have hpre : EpQPre σ1 p.bv := by rw [hσ1]; exact epQPre_restart hk (hQ _) hsw
      have h := J1.cancelBadgedJ b he hpre
      have hW := J1.cbsProjW b he
      rw [hcb, WP.spec_ok] at h hW
      obtain ⟨σ3, V3, hm3, J3, -, -⟩ := h
      have hbv : b.bv ≠ 0 := by
        intro h; apply hb; apply UScalar.eq_of_val_eq
        have := congrArg BitVec.toNat h; simpa using this
      have hx : ((.ok (), σ3) : Except Unit Unit × Fl4Spec.State Unit) ∈
          ((Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
            (absCap (.Endpoint p b true true true true)))).run σ1).1 := by
        show _ ∈ ((Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
          (.endpointCap p.bv b.bv (rightsOf true true true true)))).run σ1).1
        unfold Fl4Spec.invokeCnode Fl4Spec.withoutPreemption
        simp only [Fl4Spec.NonDet.when, hbv, ne_eq, not_false_eq_true, ↓reduceIte]
        exact mem_liftE (x := ((), σ3)) hm3
      exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ3),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨_, _, Or.inl ⟨rfl, rfl⟩, J3.xtop.rel.1, J3.xtop.rel.2.1,
          J3.xtop.rel.2.2.1, J3.xtop.rel.2.2.2.1, J3.xtop.rel.2.2.2.2.1⟩,
        ⟨JStab.mv (G := G1) (V := V1) ⟨_, _, _, _, _, J3⟩, W1.projW_trans hW⟩⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 39) **The CNode CancelBadgedSends label at stable ghosts, with its `ProjW` footprint**
(XTopJointLiveCn's `decode_invocation_cnode_cancelJL`, the same route). -/
theorem decode_cnode_cancelJSt (hAM : ARMask arI AR) (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s)) (hC : CurRun σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeCancelBadgedSends)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (hQ : ∀ e, EpQPre σ e)
    (hsw : ∀ u, σ.schedulerAction = .switchThread u → u ≠ ct.bv)
    (hE : ∀ (e b : U64) (sl : Fl4Spec.CslotPtr), AbsSlot Z.th sl →
      capV (L.mem s) (cslotAddr sl) = .Endpoint e b true true true true → e ∈ Z.E)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.CNodeCancelBadgedSends length slot
      (.CNode p r gs g) blk call don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, hFI⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_cancel_dec arI Z.th s ar σ Z.G hR hV hX.rel.1 hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI hFI hact hcur htcb)
      fun res h => cn_cancel_topJSt arI hAM J hZB hC hcur hQ hsw hE h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨J.stab, P1.WritesIn.refl _ _⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 39) **The CNode cap's decode at a dispatch state at CancelBadgedSends, any flags** (module
docstring). -/
theorem decCnCbsSt (hA : P0.ArchTotal arI) (hARI : ARIface arI AR) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb) (hsg : SpecGlob σb)
    (hQ : ∀ e, EpQPre σb e)
    (hMb : MR a' σb.machineState) {ct : U64} (hct : sched.cur_thread st s' = ok ct)
    {info : msginfo.MessageInfo} {mi : Fl4Spec.MessageInfo} {buf : U64} {buffer : Option Fl4Spec.ObjRef}
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))} {argsU : List U64}
    (hinfo : msg.msg_info st s' ct = ok info)
    (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False))
    (hbuf : msg.lookup_ipc_buffer st s' false ct = ok buf)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False))
    (hr2 : ipc.lookup_extra_caps st s' ct buf info = ok r2)
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False))
    (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σb = ({(argsU.map UScalar.bv, σb)}, False))
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p r gs g : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.CNode p r gs g))
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs) (hl : info.label.val = 27)
    (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.CNode p r gs g) bl call don fp buf e mi.miLabel
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  have e27 : info.label = fl4_abi.label.CNodeCancelBadgedSends := UScalar.eq_of_val_eq (by rw [hl, lbl_cancel_val])
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  rw [← hLb]
  obtain ⟨sl', hl', hd⟩ := cnode_canon info.label
  refine XCapP.lbl_congr arI (specDec_cnode p r gs g hd) ?_
  have hr : info.label ≠ fl4_abi.label.CNodeRevoke := fun e => by rw [e, lbl_revoke_val] at hl; omega
  have hd' : info.label ≠ fl4_abi.label.CNodeDelete := fun e => by rw [e, lbl_delete_val] at hl; omega
  have hlbl : Fl4Spec.genInvocationType sl' = .cnodeCancelBadgedSends := by
    rw [hl']; unfold cnodeLabelOf; simp [hl]
  have hsr : Fl4Spec.genInvocationType sl' ≠ .cnodeRevoke := by rw [hlbl]; intro e; cases e
  have hsd : Fl4Spec.genInvocationType sl' ≠ .cnodeDelete := by rw [hlbl]; intro e; cases e
  refine XCapP.mrT hMT ?_ (MKD.decode_cnode_nrd L.total hA hKD hr hd' hMb)
    (fun inv hdc => MachT.dec_cnode_q fp sl' _ ci sl _ _ _ exs buffer hsr hsd σb _ hdc.1 inv rfl)
  refine XCap.toPN arI ?_ (cnode_noPre_of hl' (by omega))
  have hX := J.xtop
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .CNode p r gs g := capV_of_capAt hc
  obtain ⟨hwf, hcv⟩ := slot_cap_wf hX hAs hsc
  obtain ⟨hcur, -⟩ := J.curEq hct
  rw [e27]
  exact decode_cnode_cancelJSt arI hARI.toMask s' a' σb J (J.zNoBlk hsg) (J.curRun.run hnib) sl' hlbl
    (msgLen info buf) buf ct hct argsU hLen hArgs p r gs g hwf hcv e exs J.kern.act hcur hQ
    (fun u hu => by rw [hnib.2] at hu; cases hu)
    (fun e b sl' hsl hcV => by
      obtain ⟨Tr, Cq, hJl⟩ := J.jpl
      exact J.hset.1 e ((hJl.typed _ hsl.isSlot).1 e b _ _ _ _ hcV))
    (cslotAddr sl) bl call don fp ci sl buffer

set_option maxHeartbeats 4000000 in
/-- (p3J gen 39) **`MidDecStWL` at `KW ∧ IsRestCap7` from the CancelBadgedSends leaf** (module docstring). -/
theorem midDecRest7_of_cbs (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap8 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap7 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p r gs g, cp = .CNode p r gs g ∧ info.label.val = 27
  · obtain ⟨p, r, gs, g, rfl, hl⟩ := hS
    obtain ⟨hnib, hsg⟩ := dispEnteredSg hnd hX hni hBA
    exact decCnCbsSt hA hARI hMT hKD J hnib hsg (epQPre_of_sinv hnd hX.sb (hX.entered hni) hX.epQAll hBA) hMb hct
      a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap8_of hW.2 hS⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

end Fl4Proofs.P3.Mc
