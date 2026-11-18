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
taken): the TCB invocation labels (2..24) but Suspend (12),
UnbindNotification (15), SetBreakpoint (16), UnsetBreakpoint (18) and
SetTLSBase (20). -/
def TcbJOpen (lbl : U64) : Prop :=
  2 ≤ lbl.val ∧ lbl.val ≤ 24 ∧ lbl.val ≠ 12 ∧ lbl.val ≠ 15 ∧ lbl.val ≠ 16 ∧ lbl.val ≠ 18 ∧ lbl.val ≠ 20

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
      σ1.curThread = σ.curThread ∧ sched.set_thread_state st s ct sched.TS_RESTART = ok s1 ∧
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
  refine ⟨s1, σ1, x, hrc1, hst1, hk, hcur, e, ?_, ?_, ?_, hs1, Ac', Lst', D', ?_⟩
  · subst e
    intro u e
    unfold Notif.stsAct at e
    split_ifs at e
    all_goals first
      | (have e2 : σ.schedulerAction = .switchThread u := e
         rw [hni.2] at e2; cases e2)
      | cases e
  · subst e; unfold Notif.stsAct; split_ifs <;> rfl
  · subst e; exact (stsAct_fields _ _).2.1
  · subst e; exact J.cs_frame hk1 hX1 hkb (JCs.same J hSS hkz) R

set_option maxHeartbeats 4000000 in
/-- **A scheduler step at `J`** (`stepClosed_jat`'s scheduler case, with
XTopJointRest's `jowes_sched`, no premise). -/
theorem JAtZ.schedJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hS : SchedStep (L := L) Z.th s σ s' σ') :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s' ar σ' := by
  have hX := J.xtop
  have hX1 := hX.schedStep J.ks J.thT hS
  have hW := (hS.2.1 Z.N Z.T Z.C Z.c J.thT hX.fin.1.1.1 hX.fin.1.1.2.2.1).2.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    hX.slotsSame_of hW fun b hb => schW_oobj hX.fin.1.1.1.placed.tcb hb
  obtain ⟨Ac', Lst', D', R⟩ := jowes_sched arI s s' ar σ σ' hS Z H Cs Ac Lst D rfl J hX1
  exact ⟨Ac', Lst', D', J.cs_frame hW.1 hX1 (KBack.of_kheap hS.1.kh) (JCs.same J hSS (KSz.of_kheap hS.1.kh)) R⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

open Fl4Proofs.P1 in
set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across a register step with debug words** (XTopJointRegFrame's
`JAtZ.reg_frameF`, the write set widened by the TCBs' debug words, offsets
448..512: TCB words outside every relation, as the register words). -/
theorem JAtZ.reg_frameG (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64}
    (hI3 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hw : P1.WritesIn st s s' (fun b => RegFW Z.T Z.C b ∨ ∃ y ∈ Z.T, y.val + 448 ≤ b.val ∧ b.val < y.val + 512)) (hA : QKY σ σ') (hyk : YKeep σ σ') (hInv : Inv σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) ∅ s)) :
    ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst D s' a σ' := by
  have hI := J.xtop.irelK J.ks J.buf
  have hT : TcbPlaced Z.T := J.ip.e.tcb
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hw fun b hb => by
    rcases hb with ((hb | ⟨q, hq, rfl⟩) | ⟨y, hy, hb⟩) | ⟨y, hy, h1, h2⟩
    · obtain ⟨y, hy, h1, h2⟩ := hb
      exact Or.inr (Or.inr (Or.inl ⟨y, hy, h1, by omega⟩))
    · obtain ⟨x0, n0, hk0, hx0⟩ := hs.scs q hq
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨q, hq, x0, n0, hk0, hx0.in_obj (hx0.hdr (K := 8#u64) (by simp) (by simp)).2⟩))))))
    · exact Or.inr (Or.inr (Or.inl ⟨y, hy, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨y, hy, by omega, by omega⟩))
  have hwF : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) := hw.mono fun b hb => by
    rcases hb with ((⟨y, hy, k1, k2⟩ | ⟨q, hq, rfl⟩) | ⟨y, hy, hb⟩) | ⟨y, hy, k1, k2⟩
    · exact Or.inr ⟨y, hy, b.val - y.val, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inl (KFoot.of_sw (sw_hdr hS hq (K := 8#u64) (by simp) (by simp) (by decide)))
    · exact Or.inr ⟨y, hy, 3376, by omega, by omega, by omega, by omega, by omega, hb⟩
    · exact Or.inr ⟨y, hy, b.val - y.val, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hck : Fl4Proofs.P3.CKeep σ σ' := hA.ckeepP
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3 hAR hF.1 hck.cdt hck.orig hck.ks hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.finW_keeps hwF
  have ck := hA.callKeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hDbg := J.kw_dbg (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hI3.2.2.1
  have hAI3 : ActIdle σ' := hA.actIdle J.act
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_qk hA hS3 hI3.1 hwF k3 hAI3.1
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => hA.szKeep q.bv y n hq) hks (J.finW_irq hwF)⟩
  have hkern := J.kern_keep hks hwF.2.1 hS3 hA.ct hA.csc (fun sl h => Or.inl (by rw [← hA.orig]; exact h))
    (by rw [hA.arch])
    (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hDbg
    (D' := D)
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac' Lst D s' σ' :=
    ⟨hCR', hRF', J.yld.frame k2 hyk, J.mcp.frame k1 hA.mcpKeep, J.buf.frame kb hA.bufKeep, hRP',
      J.apart.sc_frame hks hA.szKeep, hjpl, J.jcov_keep hks hF.1 hdead, hkern,
      J.finW_utc hwF hF.1 hA.cdt hA.orig hA.arch hDbg, hA.nsc J.nsc, hInv, hA.cur J.cur, hA.own J.own, hA.off J.off,
      hAI3, hA.bsa J.bsa, hA.isorted J.isorted, hA.curRunM J.curRun, hblk⟩
  have hC0 := JCs.same J hF.1 hA.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨V', J.cs_frameV hks hX3 hA.kback hC R⟩

open Fl4Proofs.P1 in
set_option maxHeartbeats 8000000 in
/-- **A debug word of a TCB written at `J`** (`JAtZ.reg_frameG` with the
spec state kept: `XTopAt.tcbWrA`, `IRel` by `XTopAt.irelK`, P1's `BlkOK` by
`blk_rf`, its footprint by `foot_field`). -/
theorem JAtZ.dbgWrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (wa : U64)
    (Kv : Nat) (hK : 448 ≤ Kv ∧ Kv < 512 ∧ Kv % 8 = 0) (hwav : wa.val = t.val + Kv) (v : U64) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (L.wr s wa v) a σ := by
  have hT : TcbPlaced Z.T := J.ip.e.tcb
  have hta := hT t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hT
  set K : U64 := ⟨BitVec.ofNat 64 Kv⟩ with hKdef
  have hKv : K.val = Kv := by
    show (BitVec.ofNat 64 Kv).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hKt : (core.num.U64.wrapping_add t K).val = t.val + K.val := tfield_val hta (by omega)
  have hreq : wa = core.num.U64.wrapping_add t K := UScalar.eq_of_val_eq (by rw [hwav, hKt, hKv])
  subst hreq
  have hwa : P1.Aligned (core.num.U64.wrapping_add t K) := P1.field_aligned hta (by omega) (by omega)
  have hw : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t K) v) (· = core.num.U64.wrapping_add t K) :=
    P1.writesIn_wr hwa
  have hblk := (P1.blk_rf J.blk (hw.mono fun b hb => Or.inl ⟨t, htH, K, by omega, by omega, hb⟩)).1
  have hfoot : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t K) v) (P1.KW st (P1.Heap.tcbs H) Cs
      (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s) :=
    P1.foot_field hTH htH (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
  have hX' := J.xtop.tcbWrA ht _ Kv (Or.inr (Or.inr (Or.inl hK))) (by rw [hKt, hKv]) v
  have hks : L.ksb (L.wr s (core.num.U64.wrapping_add t K) v) = L.ksb s := hw.1
  have hwF : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t K) v) (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) :=
    hw.mono fun b hb => Or.inr ⟨t, ht, Kv, by omega, by omega, by omega, by omega, by omega, by rw [hb, hKt, hKv]⟩
  obtain ⟨-, -, kb, -, -⟩ := J.finW_keeps hwF
  have hA : QKY σ σ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun p => Or.inl rfl⟩
  have hBW : BufWordRel Z.T (L.mem (L.wr s (core.num.U64.wrapping_add t K) v)) σ := J.buf.frame kb hA.bufKeep
  have hI3 := hX'.irelK (by rw [hks]; exact J.ks) hBW
  exact J.reg_frameG hI3 (hw.mono fun b hb => Or.inr ⟨t, ht, by rw [hb, hKt, hKv]; omega,
    by rw [hb, hKt, hKv]; omega⟩) hA (YKeep.of_kheap rfl) J.inv hblk hfoot

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
  obtain ⟨s1, σ1, x, hrc1, hst, -, -, -, hns, hid1, -, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
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
  obtain ⟨s1, σ1, x, hrc1, hst, hk, -, he1, -, -, -, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
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

set_option maxHeartbeats 8000000 in
/-- **The UnsetBreakpoint label at `JAt`** (as `tcb_unset_bpX`): the
argument by `ArgRel` [J], the caller's restart (`JAtZ.restartJ`), the two
debug words (`JAtZ.dbgWrJ`); the spec keeps its state. -/
theorem tcb_unset_bpJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .unsetBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 1)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBUnsetBreakpoint p ⟨length, buf, call, slot, extra⟩
      blk call don slbl args ci sl excaps buffer := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKX
  rw [decode_unset_eq arI s ar p _ hstall, hdec0]
  obtain ⟨bp, hbp, hbs⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 0#u64 (by decide)
  rw [hbp]; simp only [bind_ok]; rw [check_bp_eq]
  simp only [bind_ok]
  have hsp : (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv).run σ =
      (Fl4Spec.fl4CheckBpNum (Z := Unit) bp.bv >>= fun _ =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TcbInvocation.unsetBreakpoint p.bv bp.bv)).run σ := by
    unfold Fl4Spec.decodeFl4UnsetBreakpoint
    exact run_bind_ok hbs _
  by_cases hb : bp ≥ 4#u64
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, bp_err⟩, hJ0⟩)
    apply run_liftME_err
    rw [hsp]
    exact run_bind_error (by rw [checkBp_run, if_pos hb]) _
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨s1, σ1, x, hrc1, hst1, -, -, -, -, -, -, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    rw [hrc1]; simp only [bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv)).run σ =
        ({(.ok (.invokeFl4TCB (.unsetBreakpoint p.bv bp.bv)), σ)}, False) := by
      apply run_liftME_ok
      rw [hsp, run_bind_ok (by rw [checkBp_run, if_neg hb])]
      rfl
    have hbpv : bp.val < 4 := by
      have : ¬ (4 ≤ bp.val) := fun h => hb (by scalar_tac)
      omega
    have hpf := (J1.ip.e.tcb p hpT).fits
    refine WP.spec_bind (unset_bp_wr s1 p bp hbpv) ?_
    rintro s2 ⟨v, rfl⟩
    obtain ⟨V2, J2⟩ := J1.dbgWrJ hpT (dbgA p 5#u64) (448 + 40) (by omega)
      (by rw [dbgA_val (by omega) (by decide)]; simp) v
    obtain ⟨V3, J3⟩ := J2.dbgWrJ hpT (dbgA p bp) (448 + 8 * bp.val) (by omega)
      (by rw [dbgA_val (i := bp) (by omega) (by omega)]; omega) 0#u64
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ1), rfl,
      ⟨_, _, Or.inl ⟨rfl, rfl⟩, J3.xtop.rel.1, J3.xtop.rel.2.1, J3.xtop.rel.2.2.1, J3.xtop.rel.2.2.2.1,
        J3.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac1, Lst1, D1, J3⟩⟩)

set_option maxHeartbeats 8000000 in
/-- **The SetBreakpoint label at `JAt`** (as `tcb_set_bpX`): FL4's checks
against the spec's (the five arguments by `ArgRel` [J]), the caller's restart
(`JAtZ.restartJ`), the two debug words (`JAtZ.dbgWrJ`); the spec keeps its
state. -/
theorem tcb_set_bpJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .setBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 5)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBSetBreakpoint p ⟨length, buf, call, slot, extra⟩
      blk call don slbl args ci sl excaps buffer := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4SetBreakpoint (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKX
  rw [decode_setbp_eq arI s ar p _ hstall, hdec0]
  have hc : (⟨length, buf, call, slot, extra⟩ : tcb.Ctx).buf = buf := rfl
  obtain ⟨bp, h0, g0⟩ := arg_rel hA hct hcur _ hc 0#u64 (by decide)
  obtain ⟨vaddr, h1, g1⟩ := arg_rel hA hct hcur _ hc 1#u64 (by decide)
  obtain ⟨ty, h2, g2⟩ := arg_rel hA hct hcur _ hc 2#u64 (by decide)
  obtain ⟨size, h3, g3⟩ := arg_rel hA hct hcur _ hc 3#u64 (by decide)
  obtain ⟨rw, h4, g4⟩ := arg_rel hA hct hcur _ hc 4#u64 (by decide)
  rw [set_bp_checked_eq s p _ h0 h1 h2 h3 h4]
  have hsp := set_bp_spec_run σ buffer p.bv g0 g1 g2 g3 g4
  have hrel := bpErr_rel bp vaddr ty size rw
  cases hF : bpErrF bp vaddr ty size rw with
  | some e =>
    cases hS : bpErrS bp vaddr.bv ty.bv size.bv rw.bv with
    | none => rw [hF, hS] at hrel; exact hrel.elim
    | some e' =>
      rw [hF, hS] at hrel
      dsimp only at hrel
      dsimp only
      simp only [bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨e, rfl, rfl, ⟨e', ?_, hrel⟩, hJ0⟩)
      apply run_liftME_err
      rw [hsp, hS]
  | none =>
    cases hS : bpErrS bp vaddr.bv ty.bv size.bv rw.bv with
    | some e' => rw [hF, hS] at hrel; exact hrel.elim
    | none =>
    have hbpv := bpErrF_bp hF
    simp only
    obtain ⟨s1, σ1, x, hrc1, hst1, -, -, -, -, -, -, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    rw [hrc1]; simp only [bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4SetBreakpoint (Z := Unit) buffer p.bv)).run σ =
        ({(.ok (.invokeFl4TCB (.setBreakpoint p.bv bp.bv vaddr.bv ty.bv size.bv rw.bv)), σ)}, False) := by
      apply run_liftME_ok
      rw [hsp, hS]
    have hpf := (J1.ip.e.tcb p hpT).fits
    have hin : (do
        let s2 ← debug.set_breakpoint st s1 p bp vaddr ty size rw
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2)) ⦃ x =>
          ∃ v, x = (.Ok (), L.wr (L.wr s1 (dbgA p bp) vaddr) (dbgA p 5#u64) v) ⦄ :=
      WP.spec_bind (set_bp_wr (st := st) s1 p bp vaddr ty size rw) (fun s2 ⟨v, h⟩ => (WP.spec_ok _).2 ⟨v, by rw [h]⟩)
    refine WP.spec_bind hin ?_
    rintro x ⟨v, rfl⟩
    obtain ⟨V2, J2⟩ := J1.dbgWrJ hpT (dbgA p bp) (448 + 8 * bp.val) (by omega)
      (by rw [dbgA_val (i := bp) (by omega) (by omega)]; omega) vaddr
    obtain ⟨V3, J3⟩ := J2.dbgWrJ hpT (dbgA p 5#u64) (448 + 40) (by omega)
      (by rw [dbgA_val (by omega) (by decide)]; simp) v
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ1), rfl,
      ⟨_, _, Or.inl ⟨rfl, rfl⟩, J3.xtop.rel.1, J3.xtop.rel.2.1, J3.xtop.rel.2.2.1, J3.xtop.rel.2.2.2.1,
        J3.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac1, Lst1, D1, J3⟩⟩)

set_option maxHeartbeats 8000000 in
/-- **The SetTLSBase label at `JAt`** (as `tcb_set_tlsX`): the caller's
restart (`JAtZ.restartJ`), the `TLS_BASE` register (`JAtZ.regWrJ`), and for
the current thread `reschedule_required` as a scheduler step
(`JAtZ.schedJ`; `ActReady` at `WX` [J], already a premise); the
current-thread word outside the objects [P]. -/
theorem tcb_set_tlsJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (hA : ∀ s a σ G, WX (L := L) AR Z.th s a σ G → Notif.ActReady σ)
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetTLSBase)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBSetTLSBase p ⟨length, buf, call, slot, extra⟩ blk
      call don slbl (args.map UScalar.bv) ci sl excaps buffer := by
  have hX := J.xtop
  have hP := hX.rel.1
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (hX.curTcb hcur).1
  have hact := J.kern.act
  have hpT : p ∈ Z.T := J.thT p hp
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hdec0 : (specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer) =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetTlsBase (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX tcb.decode
  rw [hstall, hdec0]
  simp only [bind_ok, u64_eq_iff, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val, lbl_tcbSetBreakpoint_val,
    lbl_tcbGetBreakpoint_val, lbl_tcbUnsetBreakpoint_val, lbl_tcbConfigureSingleStepping_val,
    lbl_tcbSetTLSBase_val, lbl_tcbSetEPTRoot_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  refine let_pair_spec s ar (fun s1 => tcb.decode_set_tls_base st s1 p ⟨length, buf, call, slot, extra⟩) _ ?_
  unfold tcb.decode_set_tls_base
  by_cases h1 : length < 1#u64
  · simp only [if_pos h1, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 ?_
    apply Or.inl
    refine ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩
    apply run_liftME_err
    unfold Fl4Spec.decodeSetTlsBase
    rw [whenE_pos (show (args.map UScalar.bv).length = 0 by rw [List.length_map, ← hlen]; scalar_tac)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [if_neg h1]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
      (Fl4Spec.decodeSetTlsBase (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv))).run σ =
      ({(.ok (.invokeTCB (.setTLSBase p.bv y0.bv)), σ)}, False) := by
    apply run_liftME_ok
    unfold Fl4Spec.decodeSetTlsBase
    rw [whenE_neg (by simp), retOk_bind]
    show (Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.setTLSBase p.bv (Fl4Spec.ucast 64 y0.bv)) :
      Fl4Spec.SEMonad Unit _).run σ = _
    rw [ucast64_self]; rfl
  rw [harg]; simp only [bind_ok]
  obtain ⟨s1, σ1, x0, hrc1, hst1, -, -, -, -, -, hcur1', hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have hc1 := set_thread_state_cases (L := L) s ct sched.TS_RESTART
  rw [hs1, WP.spec_ok] at hc1
  rw [hrc1]; simp only [bind_ok]
  obtain ⟨w, hw, hwb⟩ := sanitise_tls y0
  rw [hw]; simp only [bind_ok, set_reg_tls_eq]
  -- the current thread is unchanged
  have hctv : L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct := by
    have := cur_thread_spec' (L := L) s; rw [hct, WP.spec_ok] at this; exact this.symm
  have hpf := hP.fits p _ hp
  have hcf := hP.fits ct _ htcb
  have hpa := hP.align p _ hp
  have hca := hP.align ct _ htcb
  simp only [objSize] at hpf hcf
  have hstv : (stA ct).val = ct.val + 3328 := by
    rw [stA_eq, wordOf_val (by simp; omega)]; simp
  have hcs2 : sched.cur_thread st (L.wr s1 (tlsA p) w) = ok ct := by
    rw [cur_thread_eq]
    simp only [P1.nodeAt_wr, L.cpu_wr]
    have hcwA : P1.Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) := hcw.1
    have hn1 : L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD = L.nodeAt s (L.cpu s) layout.node.CUR_THREAD := by
      rcases hc1 with rfl | rfl <;> simp
    rw [hn1, L.mem_wr_ne (by unfold P1.Aligned; rw [tlsA_val (by omega)]; omega) hcwA
      (fun e => out_ne hcw hp (w := tlsA p) (by rw [tlsA_val (by omega)]; omega) e)]
    rcases hc1 with rfl | rfl
    · rw [L.mem_wr_ne (by unfold P1.Aligned; rw [hstv]; omega) hcwA
        (fun e => out_ne hcw htcb (by rw [hstv]; omega) e), hctv]
    · rw [L.mem_wr_ne hact.1 hcwA (fun e => cur_ne_action s e.symm),
        L.mem_wr_ne (by unfold P1.Aligned; rw [hstv]; omega) hcwA
        (fun e => out_ne hcw htcb (by rw [hstv]; omega) e), hctv]
  rw [hcs2]; simp only [bind_ok, obj.Tcb.Insts.CoreCmpPartialEqTcb.eq]
  -- the spec: the target's TCB, its register at `J`
  have hcur1 : σ1.curThread = ct.bv := by rw [hcur1', hcur]
  obtain ⟨x, hkx, -⟩ := J1.xtop.fin.1.1.2.1.tcb p hpT
  have htl : tlsA p = regA p (regIdx Fl4Spec.tlsBaseRegister) := by
    unfold tlsA regA layout.tcb.REGS; rfl
  have hXr := reg_wr_irel J1.ip (J1.xtop.irelK J1.ks J1.buf) hpT hkx Fl4Spec.tlsBaseRegister (by decide) w
  obtain ⟨V2, J2⟩ := J1.regWrJ hpT hkx Fl4Spec.tlsBaseRegister w hXr
  rw [← htl] at J2
  by_cases hpc : p = ct
  · subst hpc
    simp only [decide_true, ↓reduceIte]
    have hA2 := hA _ _ _ _ ⟨Z.mv Z.G V2, rfl, rfl, J2.xtop, J2.ks, J2.thT⟩
    obtain ⟨σ', hres, hK', hdl', hds'⟩ := rescheduleRequired_k hA2
    have hS := J2.xtop.fin.1.1.1
    have hN := J2.xtop.fin.1.1.2.2.1
    obtain ⟨s3, hrun3, ⟨σ3, he3, -, -, -, -⟩, hw⟩ := spec_exists (WP.spec_and
      (Sched.reschedule_required_refines _ _ hN hS hA2) (Sched.reschedule_required_sfootI hS))
    rw [hrun3]; simp only [bind_ok]
    rw [hres] at he3
    have e3 : σ3 = σ' := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he3))).2.symm
    subst σ3
    obtain ⟨Ac3, Lst3, D3, J3⟩ := J2.schedJ (schedStep_resched hA2 hrun3 hres hK' hdl' hds')
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ'), ?_,
      ⟨_, _, Or.inl ⟨rfl, rfl⟩, J3.xtop.rel.1, J3.xtop.rel.2.1, J3.xtop.rel.2.2.1, J3.xtop.rel.2.2.2.1,
        J3.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac3, Lst3, D3, J3⟩⟩)
    refine invoke_tls_mem (y := ((), σ')) hkx y0.bv ?_ blk call don
    rw [← hwb, hcur1]
    simp only [Fl4Spec.NonDet.when, if_pos trivial]
    rw [hres]; rfl
  · have hne : decide (p = ct) = false := by simp [hpc]
    rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], _), ?_,
      ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1, J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1,
        J2.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac1, Lst1, D1, J2⟩⟩)
    refine invoke_tls_mem (y := ((), Notif.updK σ1 p.bv (.tcb (Notif.setReg x Fl4Spec.tlsBaseRegister w.bv))))
      hkx y0.bv ?_ blk call don
    have : ¬ p.bv = σ1.curThread := fun e => hpc (UScalar.eq_of_val_eq (by
      rw [hcur1] at e; have := congrArg BitVec.toNat e; simpa using this))
    rw [← hwb]
    simp only [Fl4Spec.NonDet.when, if_neg this]
    exact Set.mem_singleton _

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
  have no : ∀ l : U64, 2 ≤ l.val → l.val ≤ 24 → l.val ≠ 12 → l.val ≠ 15 → l.val ≠ 16 → l.val ≠ 18 →
      l.val ≠ 20 → lbl = l → False :=
    fun l h1 h2 h3 h4 h5 h6 h7 h => hop (h ▸ ⟨h1, h2, h3, h4, h5, h6, h7⟩)
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ Z.T := J.thT p hp
  exact decode_invocation_threadX arI s ar σ hJ0 lbl length (cslotAddr sl) p blk call don fp buf extra ct hct slbl
    hlbl _ ci sl excaps buffer hext (hstall' p) hNative
    {
      readRegisters := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      writeRegisters := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      copyRegisters := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      configure := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      setPriority := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      setMCPriority := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      setSchedParams := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      setTimeoutEndpoint := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      setIPCBuffer := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      setSpace := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      suspend := fun h => by
        subst h
        exact tcb_suspendJ arI s ar σ J hni hRR p hpT hpI slbl (by rw [hlbl]; simp [tcbLabelOf]) (hstall' p) ct hct _
          blk call don _ ci sl excaps buffer,
      resume := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      bindNotification := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      unbindNotification := fun h => by
        subst h
        exact tcb_unbind_ntfnJ arI s ar σ J hni p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) (hstall' p) ct hct
          length buf call (cslotAddr sl) extra blk don _ ci sl excaps buffer,
      setBreakpoint := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .setBreakpoint by
          simp [tcbExtOf])
        exact tcb_set_bpJ arI s ar σ J hni p hpT slbl hg he length buf ct hct (hstall' p) buffer hA5 call
          (cslotAddr sl) extra blk don _ ci sl excaps,
      getBreakpoint := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      unsetBreakpoint := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .unsetBreakpoint by
          simp [tcbExtOf])
        exact tcb_unset_bpJ arI s ar σ J hni p hpT slbl hg he length buf ct hct
          (hstall' p) buffer (fun i hi => hA5 i (by omega)) call (cslotAddr sl) extra blk don _ ci sl excaps,
      configureSingleStepping := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      setTLSBase := fun h => by
        subst h
        exact tcb_set_tlsJ arI s ar σ J hni hA p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU
          hlen hargs hcw (hstall' p) call (cslotAddr sl) extra blk don ci sl excaps buffer,
      setFlags := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      readFPU := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      writeFPU := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim,
      setTimer := fun h => (no _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) h).elim }

end

end

end Fl4Proofs.P3
