/-
P3 (DESIGN.md §9), endpoints: `send_ipc` to a waiting receiver whose IPC
buffer is mapped (`send_ipc_recv_buf`): as `send_ipc_recv`, with the
message's buffer words (`do_ipc_transfer_buf`).
-/
import Fl4Proofs.P3.EpXferBuf2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **Send to a waiting receiver with an IPC buffer** (as `send_ipc_recv`;
the buffer words go too, `do_ipc_transfer_buf`). -/
theorem send_ipc_recv_buf (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hBm : EpBufMapHyps st T E R B SR) (hTl : EpTailHyps st A T E R B SR)
    (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hft : xt.tcbFault = none)
    {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xd = some rp)
    (badge : U64) (g gr : Bool)
    (hcaps : g = false ∨ ipcBufOf false xt = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xt.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv)
    (blk : Bool) :
    endpoint.send_ipc st ar s a blk false badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  obtain ⟨hst2, xs, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : d' = d := eq_of_bv hd'.symm
  subst hdd
  have hdT : d' ∈ T := hQ.mem d' (by simp)
  have hda := hP.tcb d' hdT
  have hxd := hR.at_tcb hdT hkd
  have hd3 : (L.mem s (tStA d')).val = 3 := (hB d' (by simp)).1
  have hdb : L.mem s (tBlockA d') = e := (hB d' (by simp)).2
  -- the receiver's state
  obtain ⟨e', rep, dd, hstd⟩ := tsCode_three (hxd.st.symm.trans hd3)
  have he' : e' = e.bv := by
    have := hxd.blk e' (by rw [hstd]; rfl); rw [hdb] at this; exact this.symm
  subst he'
  obtain ⟨hrep, hrepR⟩ := hxd.recv _ _ _ hstd
  have htd : t ≠ d' := by
    intro h; subst h; exact hnb.1 (hxt.st.symm.trans hd3)
  have hde : d'.bv ≠ e.bv := kheap_ne hkd hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  -- FL4
  unfold endpoint.send_ipc
  step as ⟨st0, hst0⟩
  rw [hst0, epState_eq, hst2]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.1]; decide)]
  step as ⟨q0, hq0⟩
  have hhead : q0.head = d' := by rw [hq0, epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (ep_dequeue_rel hH hP s σ hR hSR he hk (d := d') (by simp [Fl4Spec.Endpoint.epQueue])) ?_
  rintro s1 ⟨e1, hR1, hS1, hA1⟩
  set σ1 := updK σ e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv))
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hkd1 : σ1.kheap d'.bv = some (.tcb xd) := by simp [σ1, hde, hkd]
  -- the transfer
  refine WP.spec_bind (do_ipc_transfer_buf hH hBf hBm hP s1 a σ1 hR1 hS1 ht hdT htd hkt1 hkd1 hft hrb e badge g
    hcaps) ?_
  rintro s2 ⟨σ2, e2, hR2, hS2, hA2, hk2o, x2, hkd2, hx2st⟩
  have htd' : t.bv ≠ d'.bv := bv_inj htd
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := (hk2o _ htd').trans hkt1
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2st, hstd]
  -- `d'` is in no endpoint queue from `σ1` on
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1]
  have hdb1 : L.mem s1 (tBlockA d') = e := by
    rw [hA1 _ (a_blk hda).1 ⟨d', hdT, (a_blk hda).2⟩, hdb]
  have hq1 := dequeued_not_queued hR1 he hdb1 hk1e (epDeq_not_mem _)
  have hq2 : ∀ e'' ∈ E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1 e'' he'' z (by rw [← hk2o _ (Ne.symm hne)]; exact hz)
  -- the reply word
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ⟨?_, ?_⟩, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    · rintro ⟨r', hr'⟩
      rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hw, he⟩
      have := hP.bt wp hw d' hdT
      have := congrArg UScalar.val he
      rw [val_reply hda] at this; omega
  step as ⟨i, hi⟩
  rw [hi, hrw]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (Pₘ := fun s3 => ∃ σ3 x3, EpStateRel T E R B (L.mem s3) σ3 ∧ SR s3 σ3 ∧
      Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) rep σ2 = ({((), σ3)}, False) ∧
      σ3.kheap t.bv = some (.tcb xt) ∧ σ3.kheap d'.bv = some (.tcb x3) ∧
      (∀ e'' ∈ E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue)) ?_ ?_
  · cases hrp : rep with
    | none =>
      rw [hrp] at hrep
      have h0 := optRef_none hrep
      simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨σ2, _, hR2, hS2, rfl, hkt2, hkd2, hq2⟩
    | some r =>
      rw [hrp] at hrep hrepR hst2'
      obtain ⟨hw0, hwr⟩ := optRef_some hrep
      have hwR := hrepR (by simp)
      have hne0 : (L.mem s (tReplyA d') != 0#u64) = true := by simp [hw0]
      simp only [hne0, ↓reduceIte]
      set w := L.mem s (tReplyA d') with hwdef
      subst hwr
      obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
      have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
      have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
      have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
      have hkr2 : σ2.kheap w.bv = some (.reply xr) := (hk2o _ hwd).trans (by simp [σ1, hwe, hkr])
      have hb' := hback e.bv w.bv dd xr (by rw [hstd, hrp]) hkr
      refine WP.spec_mono (reply_unlink_rel hH hP s2 σ2 hR2 hS2 hdT hkd2 hst2' hwR hkr2 hb' hq2) ?_
      rintro s3 ⟨e3, hR3, hS3⟩
      refine ⟨_, { x2 with tcbState := .inactive }, hR3, hS3, e3, ?_, ?_, ?_⟩
      · rw [stsAct_kheap]; simp [htd', hwt.symm, hkt2]
      · rw [stsAct_kheap]; simp
      · intro e'' he'' z hz
        rw [stsAct_kheap] at hz
        have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
        have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [hwd] at hz
        exact hq2 e'' he'' z (by simpa [Ne.symm hne, Ne.symm hne'] using hz)
  · rintro s3 ⟨σ3, x3, hR3, hS3, hU, hkt3, hkd3, hq3⟩
    have hxt3 := hR3.at_tcb ht hkt3
    step as ⟨i1, hi1⟩
    have hf0 : i1 = fl4_abi.consts.fault.NullFault := by
      rw [hi1, hxt3.fault0.2 hft]; unfold fl4_abi.consts.fault.NullFault; rfl
    simp only [hf0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    apply ok_bind_spec
    refine WP.spec_bind (set_thread_state_rel hH hP s3 σ3 hR3 hS3 hdT hkd3 hq3 .running (by simp [tsCode])
      sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
    rintro s5 ⟨hR5, hS5⟩
    have hspec := sendIpc_recv_eq hk hkd hde hstd blk badge.bv g gr e2 hU hkt3 hft hkd3 (t := t.bv)
    rw [hspec]
    refine WP.spec_mono (hTl.wakeTail s5 a _ d' hR5 hS5 hdT) ?_
    rintro ⟨s7, a7⟩ ⟨ha7, hnf, σ', hm, hf, hv, hS'⟩
    exact ⟨ha7, hnf, σ', hm, hR5.frame hP hf hv, hS'⟩

end

end

end Fl4Proofs.P3.Endp
