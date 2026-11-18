/-
P3 (DESIGN.md §9), IPC: **`cancel_ipc` of a thread blocked receiving, at
`J`** (`jCancel_recv`: XTopJointSuspend's `JCancelAt` for the receive state,
toward `suspend` of a final thread cap's thread).

As the receive case of XTopJointFinReply's `JAtZ.finReplyJ`, for any reply
(or none): FL4's side by IpcSignalBound's `cancel_ipc_recvF` (fault clear,
the endpoint dequeue, the reply unlink, `Inactive`; footprint `CnW`) and P1's
`cancel_ipc.kw` (`KW`) and `cancel_ipc.blk` (`BlkOK` after); the spec's in
the frame `CFr` (IpcSignalBoundSpec's `cancelIpc_recv_cfr`,
`cancel_recv_inv`); `JAtZ` after by ScSignalBoundJ's `JAtZ.wake_postB` (used
here without a wake: its post state is any `CFr` step), the unlinked reply's
links by `RecvReplyHyp` [J] (l4v `valid_replies`, carried as
XTopJointDelR's `JDelParts.recvRep`).
-/
import Fl4Proofs.P3.XTopJointSuspend
import Fl4Proofs.P3.XTopJointFinReply
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **`cancel_ipc` of a thread blocked receiving, at `J`** (module
docstring). -/
theorem JAtZ.cancelRecvJ (hRR : RecvReplyHyp (L := L) arI AR H Cs)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb}
    (hkt : σ.kheap t.bv = some (.tcb xt)) {ep : Fl4Spec.ObjRef} {ro : Option Fl4Spec.ObjRef}
    {d : Fl4Spec.ReceiverPayload} (hst : xt.tcbState = .blockedOnReceive ep ro d) :
    ipc.cancel_ipc st arI s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  have hrb : Fl4Spec.receiveBlocked xt.tcbState = true := by rw [hst]; rfl
  have hiT : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  obtain ⟨⟨Q, R, h0⟩, -, hX, -, hSg⟩ := J.blk
  refine WP.spec_mono (WP.spec_and (WP.spec_and (cancel_ipc_recvF (ar := arI) hP0 s a σ hI ht hkt hrb
    (cancelRecvHyp_of hI.1.toE J.sv J.obj J.inv ht hkt hrb))
    (P1.ipc.cancel_ipc.kw s a t h0 hiT hX.1 hSg.sub (fun hs' => by
      obtain ⟨h1, h2⟩ := hX.2.1.reply t hiT hs'
      exact ⟨h1, h2, hX.2.1.next _ h1, hX.2.1.prev _ h1⟩) (fun hs' h0' => (hX.2.1.recv t hiT hs' h0').1)))
    (P1.ipc.cancel_ipc.blk s a t J.blk hiT)) ?_
  rintro ⟨s3, a3⟩ ⟨⟨⟨h1, σ1, x1, he1, hI1, -, -, hrib, hw⟩, hfoot⟩, hblk⟩
  try simp only [WP.uncurry'_pair] at hfoot hblk
  try dsimp only at h1 he1 hI1 hrib hw hfoot hblk ⊢
  subst h1
  refine ⟨rfl, σ1, he1, ?_⟩
  -- the spec: `cancel_ipc` of a receiver, in `CFr`
  have hm1 : ((), σ1) ∈ (Fl4Spec.cancelIpc (Z := Unit) t.bv σ).1 := by rw [he1]; exact Set.mem_singleton _
  obtain ⟨xe, hke, hq⟩ := J.sv.recvQ t.bv xt ep ro d hkt hst
  obtain ⟨F, -, hact⟩ := cancelIpc_recv_cfr (r := t.bv) hkt hst hke hq
    (fun rp h => J.sv.recvReply t.bv xt ep rp d hkt (by rw [hst, h])) hm1
  have I3 : Inv σ1 := cancel_recv_inv J.inv hkt (Or.inl ⟨ep, ro, d, hst⟩) hm1 hrib
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
  exact ⟨V', Ac, Lst, D, J'⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JCancelAt` for a thread blocked receiving** (module docstring), from
`RecvReplyHyp` [J] at every heap. -/
theorem jCancel_recv {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}
    (hRR : ∀ (H : P1.Heap) (Cs : Set U64), RecvReplyHyp (L := L) arI AR H Cs) :
    JCancelAt (L := L) arI AR th fun ts => ∃ e r d, ts = .blockedOnReceive e r d := by
  intro Z H Cs Ac Lst D s a σ _ J t ht x hk ⟨e, r, d, hst⟩
  exact J.cancelRecvJ (hRR H Cs) ht hk hst

end

end

end Fl4Proofs.P3
