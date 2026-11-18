/-
P3 (DESIGN.md §9), TCB: **the Thread cap at `JAt`, label by label**
(`decode_invocation_threadJ`, in the shape of the CNode cap's
`decode_invocation_cnodeJ_steps`).

* `TcbJOpen`: the Thread cap's labels whose `JAt` step is not yet proved;
  only for them the per-op named premise `JPostHyp` [W] (XTopJointStep) is
  still taken, lifted by `XCap.jat` from `decode_invocation_threadJAt`.
* Every other label through `decode_invocation_threadX` at `X := JAt`: the
  labels of no TCB invocation (and the fast-path flag's decode error) are the
  spec's `IllegalOperation` with the state unchanged (`tcb_illegalX`, `JAt`
  at the start).
-/
import Fl4Proofs.P3.XTopJointDelR
import Fl4Proofs.P3.XTopJointReply
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The Thread cap's labels still open at `JAt`** (their `JPostHyp` [W]
taken): the TCB invocation labels (2..24) but Suspend (12) and
UnbindNotification (15). -/
def TcbJOpen (lbl : U64) : Prop := 2 ≤ lbl.val ∧ lbl.val ≤ 24 ∧ lbl.val ≠ 12 ∧ lbl.val ≠ 15

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}
  {s : S} {ar : A} {σ : Fl4Spec.State Unit}

/-- The target, not FL4's idle word, is not the spec's idle thread. -/
theorem JAtZ.ne_idle (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) {p : U64} (hpI : p ≠ L.idleW s) :
    p.bv ≠ σ.idleThread := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have ei : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
    unfold P1.LawfulStore.idleW nodeW; rw [hc.cur]
  intro e
  exact hpI (Eq.symm (by rw [ei]; apply P1.eq_of_bv; rw [← hs.idleTh, ← e]))


set_option maxHeartbeats 8000000 in
/-- **The caller's restart at `J`** (`tcb::restart_caller`): FL4's and the
spec's (`restart_dstate`), `XTopAt` after (`XTopAt.restart`), the rest by
`jowes_restart`; no switch pending after (`Entered`), the idle thread kept. -/
theorem JAtZ.restartJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ∃ s1 σ1 x, tcb.restart_caller st s = ok s1 ∧
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      σ.kheap ct.bv = some (.tcb x) ∧ σ.curThread = ct.bv ∧
      σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv ∧
      (∀ u, σ1.schedulerAction = .switchThread u → False) ∧ σ1.idleThread = σ.idleThread ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s1 ar σ1 := by
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩
  obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, -, -, -⟩ :=
    restart_dstate Z.th J.xtop.rel.1 s σ Z.G hDS ct hct hcur htcb J.kern.act
  have e : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    have hst := hst1
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  have h := XTopAt.restart J.xtop hcur hk hrun
  rw [hs1, WP.spec_ok] at h
  obtain ⟨hX1, hSS, hk1⟩ := h
  obtain ⟨hkb, hkz⟩ := kback_ksz_upd (σ' := Notif.stsAct (Notif.updK σ ct.bv
    (.tcb { x with tcbState := .restart })) ct.bv) hk (by rw [stsAct_kheap]; rfl)
  obtain ⟨Ac', Lst', D', R⟩ := jowes_restart arI s ar σ ct x s1 hcur hk htcb hrun hs1 Z H Cs Ac Lst D rfl J hX1
  refine ⟨s1, σ1, x, hrc1, hst1, hk, hcur, e, ?_, ?_, Ac', Lst', D', ?_⟩
  · subst e
    intro u e
    unfold Notif.stsAct at e
    split_ifs at e
    all_goals first
      | (have e2 : σ.schedulerAction = .switchThread u := e
         rw [hni.2] at e2; cases e2)
      | cases e
  · subst e; unfold Notif.stsAct; split_ifs <;> rfl
  · subst e; exact J.cs_frame hk1 hX1 hkb (JCs.same J hSS hkz) R

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **The Suspend label at `JAt`** (as `tcb_suspendX`): the caller's restart
(`JAtZ.restartJ`), then `JAtZ.suspendJ` with the four cancel steps
(`jCancel_send`, `jCancel_ntfn`, `jCancel_reply`; `jCancel_recv` from
`RecvReplyLinksHyp` [J], l4v `valid_replies`, already `JDelParts.recvRep`). -/
theorem tcb_suspendJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (hRR : ∀ (H : P1.Heap) (Cs : Set U64), RecvReplyLinksHyp (L := L) arI AR H Cs)
    (p : U64) (hpT : p ∈ Z.T) (hpI : p ≠ L.idleW s) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSuspend)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (c : tcb.Ctx) (blk call don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBSuspend p c blk call don slbl args ci sl
      excaps buffer := by
  have hdec : (specDec false slbl args ci sl (.Thread p) excaps buffer).run σ =
      ({(.ok (.invokeTCB (.suspend p.bv)), σ)}, False) := by
    show (Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer).run σ = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    apply run_liftME_ok
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]; rfl
  have hid0 := J.ne_idle hpI
  obtain ⟨s1, σ1, x, hrc1, hst, -, -, -, hns, hid1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  unfold TcbOKX
  rw [decode_suspend_eq arI s ar p c hstall, hrc1]
  simp only [bind_ok]
  refine WP.spec_bind (J1.suspendJ (jCancel_send arI) (jCancel_ntfn arI) (jCancel_recv arI (hRR))
    (jCancel_reply arI) hpT (fun u h => (hns u h).elim) (by rw [hid1]; exact hid0)) ?_
  rintro ⟨s2, a2⟩ ⟨-, σ', hsus, V, Ac', Lst', D', J2⟩
  refine (WP.spec_ok _).2 ?_
  have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.suspend p.bv))).run σ1).1 := by
    show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
    exact mem_liftE (x := ([], σ')) (mem_bind_nd (x := ((), σ')) (by rw [hsus]; exact Set.mem_singleton _) rfl)
  exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
    J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac', Lst', D', J2⟩⟩

set_option maxHeartbeats 8000000 in
/-- **The UnbindNotification label at `JAt`** (as `tcb_unbind_ntfnX`): the
bound check; when bound, the caller's restart (`JAtZ.restartJ`, the bound
word kept: the spec's restart keeps the thread's binding), then
`JAtZ.unbindNJ`. -/
theorem tcb_unbind_ntfnJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbUnbindNotification)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (length buf : U64) (call : Bool) (slot : obj.Slot)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBUnbindNotification p
      ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl excaps buffer := by
  have hX := J.xtop
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX tcb.decode
  rw [hstall, hdec0]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  show (do
    let i ← obj.Tcb.bound_ntfn st p s
    if (i : U64).val = (0#u64).val then do
        let r ← error.illegal Unit
        ok (r, s, ar)
      else do
        let s2 ← tcb.restart_caller st s
        let s3 ← notification.unbind_notification st s2 p
        ok (core.result.Result.Ok (), s3, ar)) ⦃ r => TopPostDMX (L := L) (JAt (L := L) arI AR) σ blk call don
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeUnbindNotification (Z := Unit) (Fl4Spec.Cap.threadCap p.bv))) s r ⦄
  rw [tcb_bound_eq]
  simp only [bind_ok, ← u64_eq_iff]
  obtain ⟨xp, hkp, hxp⟩ := hX.fin.1.1.2.1.tcb p hpT
  have hbp : xp.tcbBoundNotification = Notif.optRef (L.mem s (P1.boundA p)) := hxp.bound
  have hsp0 : (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv)).run σ =
      ((match Notif.optRef (L.mem s (P1.boundA p)) with
        | none => Fl4Spec.NonDetE.throwError .illegalOperation
        | some _ => Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit) >>= fun _ =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.notificationControl p.bv none)).run σ := by
    simp only [Fl4Spec.decodeUnbindNotification]
    rw [lE_bind (m := Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbBoundNotification p.bv)
      (Notif.threadGet_eq _ hkp), hbp]
    generalize Notif.optRef (L.mem s (P1.boundA p)) = o
    cases o <;> rfl
  by_cases hb0 : L.mem s (P1.boundA p) = 0#u64
  · simp only [hb0, ↓reduceIte, error.illegal, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    exact run_throw_bind _ _ _
  simp only [hb0, ↓reduceIte]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
      (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv))).run σ =
      ({(.ok (.invokeTCB (.notificationControl p.bv none)), σ)}, False) := by
    apply run_liftME_ok
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    exact (congrArg (fun m : Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation => m.run σ) (retOk_bind () _)).trans rfl
  obtain ⟨s1, σ1, x, hrc1, hst, hk, -, he1, -, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  -- the bound word after the restart, through the spec (the restart keeps the binding)
  have hb1 : L.mem s1 (P1.boundA p) ≠ 0#u64 := by
    intro h1
    obtain ⟨xp1, hkp1, hxp1⟩ := J1.xtop.fin.1.1.2.1.tcb p hpT
    have hb1' : xp1.tcbBoundNotification = Notif.optRef (L.mem s1 (P1.boundA p)) := hxp1.bound
    have b1 : xp1.tcbBoundNotification = none := by rw [hb1', h1]; simp [Notif.optRef]
    have b0 : xp.tcbBoundNotification ≠ none := by rw [hbp]; simp [Notif.optRef, hb0]
    apply b0
    rw [he1, stsAct_kheap, updK_kheap] at hkp1
    by_cases hpc : p.bv = ct.bv
    · rw [hpc, Function.update_self] at hkp1
      rw [hpc, hk] at hkp
      cases hkp; cases hkp1; exact b1
    · rw [Function.update_of_ne hpc, hkp] at hkp1
      cases hkp1; exact b1
  rw [hrc1]; simp only [bind_ok]
  refine WP.spec_bind (J1.unbindNJ hpT hb1) ?_
  rintro s3 ⟨σ', hun, -, -, -, V, Ac', Lst', D', J2⟩
  refine (WP.spec_ok _).2 ?_
  have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
        (.invokeTCB (.notificationControl p.bv none))).run σ1).1 := by
    show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
    exact mem_liftE (x := ([], σ')) (mem_bind_nd (x := ((), σ')) (by rw [hun]; exact Set.mem_singleton _) rfl)
  exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
    J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac', Lst', D', J2⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The Thread cap, `JAt` after** (module docstring): the labels of
`TcbJOpen` by `decode_invocation_threadJAt` and `XCap.jat` with the per-op
premise (`JPostHyp` [W], only at those labels); the others proved. -/
theorem decode_invocation_threadJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hA : ∀ s a σ G, WX (L := L) AR Z.th s a σ G → Notif.ActReady σ)
    (hBT : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → BufWordRel Z'.T (L.mem s') σ')
    (hOK : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → Endp.IpcBufCapOK σ')
    (hBC : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → Endp.BufCover Z'.T Z'.B σ')
    (hBPl : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' →
      Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ')
    (hFl : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → FlagsRel Z'.T (L.mem s') σ')
    (lbl length : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl)
    (hsc : capV (L.mem s) (cslotAddr sl) = .Thread p)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hpI : p ≠ L.idleW s)
    (x0 x1 x2 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps) (hnc : NcHyp (st := st) s σ x0 x1 x2)
    (hnc0 : ∀ sl : Fl4Spec.CslotPtr, x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
    (hA5 : ArgRel (st := st) s σ ct buf buffer 5) (hGb : GetBpHyp (st := st) s ct p)
    (hI : TcbXIpc (L := L) arI AR Z.th s ar σ p ct buf argsU blk call don)
    (hFr : ∀ (x ptr offset r : U64) (sz : capability.FrameSize) (m ep : Bool) (asid va : U64),
      capV (L.mem s) x = .Frame ptr sz r false m ep asid va → FpuPass true offset r sz →
      FpuFrameXHyp (L := L) AR Z p (core.num.U64.wrapping_add ptr offset))
    (hRR : ∀ (H : P1.Heap) (Cs : Set U64), RecvReplyLinksHyp (L := L) arI AR H Cs)
    (hR : TcbJOpen lbl → JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl) (.Thread p) blk call don fp buf
      extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.Thread p) blk call don fp buf extra slbl
      (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  by_cases hop : TcbJOpen lbl
  · exact XCap.jat arI (decode_invocation_threadJAt arI s ar σ J hni hG hARI hT hA hBT hOK hBC hBPl hFl lbl length p
      blk call don fp buf extra ct hct slbl hlbl argsU hlen hargs ci sl hAs hsc excaps buffer hext hstall' hNative hcw
      hpI x0 x1 x2 hx0 hx1 hx2 hXc hnc hnc0 hcapC hA5 hGb hI hFr) J (hR hop)
  have no : ∀ l : U64, 2 ≤ l.val → l.val ≤ 24 → l.val ≠ 12 → l.val ≠ 15 → lbl = l → False :=
    fun l h1 h2 h3 h4 h => hop (h ▸ ⟨h1, h2, h3, h4⟩)
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hpT : p ∈ Z.T := J.thT p (slot_cap_wf J.xtop hAs hsc).2
  exact decode_invocation_threadX arI s ar σ hJ0 lbl length (cslotAddr sl) p blk call don fp buf extra ct hct slbl
    hlbl _ ci sl excaps buffer hext (hstall' p) hNative
    {
      readRegisters := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      writeRegisters := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      copyRegisters := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      configure := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      setPriority := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      setMCPriority := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      setSchedParams := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      setTimeoutEndpoint := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      setIPCBuffer := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      setSpace := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      suspend := fun h => by
        subst h
        exact tcb_suspendJ arI s ar σ J hni hRR p hpT hpI slbl (by rw [hlbl]; simp [tcbLabelOf]) (hstall' p) ct hct _
          blk call don _ ci sl excaps buffer,
      resume := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      bindNotification := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      unbindNotification := fun h => by
        subst h
        exact tcb_unbind_ntfnJ arI s ar σ J hni p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) (hstall' p) ct hct
          length buf call (cslotAddr sl) extra blk don _ ci sl excaps buffer,
      setBreakpoint := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      getBreakpoint := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      unsetBreakpoint := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      configureSingleStepping := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      setTLSBase := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      setFlags := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      readFPU := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      writeFPU := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim,
      setTimer := fun h => (no _ (by simp) (by simp) (by simp) (by simp) h).elim }

end

end

end Fl4Proofs.P3
