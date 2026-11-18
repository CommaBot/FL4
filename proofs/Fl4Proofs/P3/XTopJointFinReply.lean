/-
P3 (DESIGN.md §9), IPC: **`JAtZ` across a final reply cap's finalisation**
(toward `JStepHyps.del`, as XTopJointFin / XTopJointFinEp): FL4's
`finalise_cap` of a reply cap against the spec's, from `JAtZ` before to
`JAtZ` after (`JAtZ.finReplyJ`). By the reply's thread (IpcFinReply's
`xFinReply_of`):

* none: nothing changes;
* blocked receiving with the reply: `cancel_ipc` (IpcSignalBound's
  `cancel_ipc_recvF`, footprint `CnW`; P1's `cancel_ipc.kw` for `KW`), in the
  spec frame `CFr` (IpcSignalBoundSpec's `cancelIpc_recv_cfr`,
  `cancel_recv_inv`), `JAtZ` after by ScSignalBoundJ's `JAtZ.wake_postB`
  (the freed reply by `RecvReplyHyp` [J]);
* blocked on the reply: `reply_remove`, given by the caller (`hRm`; the
  [J] premise `JReplyRemoveHyp` of XTopJointDelR).
-/
import Fl4Proofs.P3.XTopJointFinEp
import Fl4Proofs.P3.IpcFinReply
import Fl4Proofs.P3.IpcSignalBoundSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- The outcome of `JAtZ.finReplyJ`: the spec's finalisation, `JAtZ` after at
fresh VSpace sets, the slots and the kernel-state base kept. -/
def FinRPost (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (c : capability.Cap) (s' : S) (a' : A) : Prop :=
  ∃ σ' V' Ac' Lst' D', ((absCap capability.Cap.Null, absCap capability.Cap.Null), σ') ∈
      (Fl4Spec.finaliseCap (Z := Unit) (absCap c) true σ).1 ∧
    JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σ' ∧ SlotsSame Z.th (L.mem s) (L.mem s') ∧
    L.ksb s' = L.ksb s

set_option maxHeartbeats 16000000 in
/-- **`JAtZ` across a final reply cap's finalisation** (module docstring),
`reply_remove`'s case given (`hRm`). -/
theorem JAtZ.finReplyJ (hT : P0.ArchTotal arI) (hRR : RecvReplyHyp (L := L) arI AR H Cs)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hRm : ∀ (r t : U64) (x : Fl4Spec.Tcb), r ∈ Z.R → t ∈ Z.T → σ.kheap t.bv = some (.tcb x) →
      x.tcbState = .blockedOnReply r.bv → ipc.reply_remove st arI s a r t ⦃ res => res.2 = a ∧ ∃ σ' V' Ac' Lst' D',
        Fl4Spec.replyRemove (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' res.1 res.2 σ' ∧
        SlotsSame Z.th (L.mem s) (L.mem res.1) ∧ L.ksb res.1 = L.ksb s ⦄)
    {p : U64} {g : Bool} (hp : p ∈ Z.R) :
    objects.finalise_cap st arI s a (.Reply p g) true false ⦃ res =>
      res.1 = (capability.Cap.Null, capability.Cap.Null) ∧ res.2.2 = a ∧
      FinRPost (L := L) (arI := arI) AR Z H Cs s a σ (.Reply p g) res.2.1 res.2.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hpH : H p = some .reply := J.zH.2.2.1 p hp
  obtain ⟨xr, hkr, hxr⟩ := hI.1.toE.reply p hp
  have hP0 := J.ip
  -- the receive case's raw outcome, before P1's `BlkOK` after
  have main : objects.finalise_cap st arI s a (.Reply p g) true false ⦃ res =>
      res.1 = (capability.Cap.Null, capability.Cap.Null) ∧ res.2.2 = a ∧
      (FinRPost (L := L) (arI := arI) AR Z H Cs s a σ (.Reply p g) res.2.1 res.2.2 ∨
        ∃ (t : U64) (xt : Fl4Spec.Tcb) (σ1 : Fl4Spec.State Unit), t ∈ Z.T ∧ σ.kheap t.bv = some (.tcb xt) ∧
          xr.replyTcb = some t.bv ∧ (∃ e d, xt.tcbState = .blockedOnReceive e (some p.bv) d) ∧
          Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ1)}, False) ∧
          IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c res.2.1 σ1 ∧
          RelIfBound σ1 t.bv ∧ P1.WritesIn st s res.2.1 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) ∧
          P1.WritesIn st s res.2.1 (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
            (P1.Heap.scBits H) (P1.EH H) s)) ⦄ := by
    have hfc : objects.finalise_cap st arI s a (.Reply p g) true false =
        objects.finalise_cap_object st arI s a (.Reply p g) true := by
      simp [objects.finalise_cap]
    rw [hfc]
    unfold objects.finalise_cap_object
    simp only [↓reduceIte]
    step with Endp.obj.Reply.tcb.spec as ⟨i, hi⟩
    step with obj.Tcb.is_null.spec as ⟨b0, hb0⟩
    by_cases h0 : i = 0#u64
    · have hb : b0 = true := by rw [hb0, h0]; rfl
      simp only [hb, ↓reduceIte]; rw [WP.spec_ok]
      refine ⟨rfl, rfl, Or.inl ⟨σ, Z.vs, Ac, Lst, D, ?_, J, SlotsSame.refl _ _, rfl⟩⟩
      exact finReply_mem_none hkr (by rw [hxr, ← hi, h0, Notif.optRef_zero])
    have hb : b0 = false := by rw [hb0]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    have htp : xr.replyTcb = some i.bv := by rw [hxr, ← hi, Notif.optRef_ne h0]
    obtain ⟨xt, hkt, hst⟩ := J.sv.replyTcb p.bv xr i.bv hkr htp
    obtain ⟨t', ht', et⟩ := J.obj.tcb _ xt hkt
    have e' : t' = i := P1.eq_of_bv et
    subst e'
    have hTRE := hI.1.toE.at_tcb ht' hkt
    step with Fl4Proofs.P1.obj.Tcb.state.spec as ⟨w, hw⟩
    have hv : w.val = tsCode xt.tcbState := by rw [hw, P1.stA_eq, ← tStA_eq]; exact hTRE.st
    have e5 : sched.TS_BLOCKED_ON_REPLY = 5#u64 := by unfold sched.TS_BLOCKED_ON_REPLY; rfl
    rcases hst with hs | ⟨e, d, hs⟩
    · have heq : w = sched.TS_BLOCKED_ON_REPLY := UScalar.eq_of_val_eq (by rw [hv, hs, e5]; rfl)
      simp only [heq, ↓reduceIte]
      refine WP.spec_bind (hRm p t' xt hp ht' hkt hs) ?_
      rintro ⟨s1, a1⟩ ⟨rfl, σ1, V1, Ac1, Lst1, D1, he1, J1, hSS1, hks1⟩
      show (ok ((capability.Cap.Null, capability.Cap.Null), s1, a1)) ⦃ _ ⦄
      rw [WP.spec_ok]
      refine ⟨rfl, rfl, Or.inl ⟨σ1, V1, Ac1, Lst1, D1, ?_, J1, hSS1, hks1⟩⟩
      refine finReply_mem_some hkr htp hkt ?_
      rw [hs]; show ((), σ1) ∈ (Fl4Spec.replyRemove t'.bv p.bv σ).1
      rw [he1]; exact Set.mem_singleton _
    · have hne : w ≠ sched.TS_BLOCKED_ON_REPLY := fun h => by rw [h, e5, hs] at hv; simp [tsCode] at hv
      have heq : w = sched.TS_BLOCKED_ON_RECV := UScalar.eq_of_val_eq (by rw [hv, hs, tsVals.2.2.1]; rfl)
      have hRRn : sched.TS_BLOCKED_ON_RECV ≠ sched.TS_BLOCKED_ON_REPLY := by rw [e5, tsVals.2.2.1]; decide
      simp only [heq, hRRn, ↓reduceIte]
      have hrb : Fl4Spec.receiveBlocked xt.tcbState = true := by rw [hs]; rfl
      have hiT : t' ∈ P1.Heap.tcbs H := J.zH.1 t' ht'
      obtain ⟨⟨Q, R, h0⟩, -, hX, -, hSg⟩ := J.blk
      refine WP.spec_bind (WP.spec_and (cancel_ipc_recvF (ar := arI) hP0 s a σ hI ht' hkt hrb
        (cancelRecvHyp_of hI.1.toE J.sv J.obj J.inv ht' hkt hrb))
        (P1.ipc.cancel_ipc.kw s a t' h0 hiT hX.1 hSg.sub (fun hs' => by
          obtain ⟨h1, h2⟩ := hX.2.1.reply t' hiT hs'
          exact ⟨h1, h2, hX.2.1.next _ h1, hX.2.1.prev _ h1⟩) (fun hs' h0' => (hX.2.1.recv t' hiT hs' h0').1))) ?_
      rintro ⟨s1, a1⟩ ⟨⟨rfl, σ1, x1, he1, hI1, -, -, hrib, hw1⟩, hf1⟩
      show (ok ((capability.Cap.Null, capability.Cap.Null), s1, a1)) ⦃ _ ⦄
      rw [WP.spec_ok]
      exact ⟨rfl, rfl, Or.inr ⟨t', xt, σ1, ht', hkt, htp, ⟨e, d, hs⟩, he1, hI1, hrib, hw1, hf1⟩⟩
  refine WP.spec_mono (WP.spec_and main
    (P1.fin_cap_reply.slots (ar := arI) hT s a p g true false J.blk hpH)) ?_
  rintro ⟨⟨rem, cl⟩, s3, a3⟩ ⟨⟨e1, e2, hout⟩, -, hblk, -, -⟩
  simp only at e1 e2 hout hblk ⊢
  refine ⟨e1, e2, ?_⟩
  rcases hout with h | ⟨t, xt, σ1, ht, hkt, htp, ⟨ep, d, hst⟩, he1, hI1, hrib, hw, hfoot⟩
  · exact h
  subst e2
  -- the spec: `cancel_ipc` of a receiver, in `CFr`
  have hrb : Fl4Spec.receiveBlocked xt.tcbState = true := by rw [hst]; rfl
  have hm1 : ((), σ1) ∈ (Fl4Spec.cancelIpc (Z := Unit) t.bv σ).1 := by rw [he1]; exact Set.mem_singleton _
  obtain ⟨xe, hke, hq⟩ := J.sv.recvQ t.bv xt ep (some p.bv) d hkt hst
  obtain ⟨F, -, hact⟩ := cancelIpc_recv_cfr (r := p.bv) hkt hst hke hq
    (fun rp h => J.sv.recvReply t.bv xt ep rp d hkt (by rw [hst, h])) hm1
  have I3 : Inv σ1 := cancel_recv_inv J.inv hkt (Or.inl ⟨ep, some p.bv, d, hst⟩) hm1 hrib
  have B3 := F.bsa J.bsa
  have hAI3 : ActIdle σ1 := by
    rcases hact with e | e
    · exact ⟨fun u hu => F.sched (J.act.1 u (by rw [← e]; exact hu)), F.idleOK J.act.2⟩
    · exact ⟨fun u hu => (by rw [e] at hu; cases hu), F.idleOK J.act.2⟩
  have hcur3 : σ1.schedulerAction = .chooseNewThread ∨ CurInv σ1 := by
    rcases hact with e | e
    · exact J.cur.imp (fun h => by rw [e]; exact h) F.curInv
    · exact Or.inl e
  have hrun3 : CurRunM σ1 := by
    rcases hact with e | e
    · exact J.curRun.imp (fun h => by rw [e]; exact h) F.curRunW
    · exact Or.inl (act_cn_nr e)
  have hF : IFrame (L := L) Z.th s s3 := IRel.iframe_of hI hw fun b hb => CnW.oobj hI.2.2.1 hb
  have ht' : ∀ q ∈ D, q.bv ≠ t.bv := by
    intro q hq e
    have htq : t = q := (P1.eq_of_bv e).symm
    subst htq
    have hd := (J.jcov.dead t hq).1 (J.zH.1 t ht)
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.tcb t ht
    rw [hkt] at hk'; cases hk'
    have h3 := hR.st
    rw [← stA_tStA, hd.1, hst] at h3
    unfold sched.TS_INACTIVE at h3
    simp [tsCode] at h3
  obtain ⟨V', J'⟩ := J.wake_postB hI1 hF hw hblk hfoot F I3 B3 hAI3 hcur3 hrun3
    (fun d hd xr' hx hxt => hRR Z Ac Lst D s _ σ J d hd xr' t.bv xt hx hxt hkt hrb) ht'
  refine ⟨σ1, V', Ac, Lst, D, ?_, J', hF.1, hF.2⟩
  refine finReply_mem_some hkr htp hkt ?_
  rw [hst]; exact hm1

end

end

end Fl4Proofs.P3
