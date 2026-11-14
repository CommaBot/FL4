/-
P3 (DESIGN.md §9), endpoints: `receive_ipc` from a waiting sender into a
mapped IPC buffer (`receive_ipc_send_buf`): as `receive_ipc_send`, with the
message's buffer words (`do_ipc_transfer_buf`).
-/
import Fl4Proofs.P3.EpSendBuf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **Receive from a waiting sender into a mapped IPC buffer** (as
`receive_ipc_send`, with the buffer words, `do_ipc_transfer_buf`). -/
theorem receive_ipc_send_buf (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hBm : EpBufMapHyps st T E R B SR)
    (hTl : EpTailHyps st A T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xt = some rp)
    {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = false)
    (hcaps : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hta := hP.tcb t ht
  have hbound : L.mem s (tBoundA t) = 0#u64 := optRef_none (hxt.bound.symm.trans hbn)
  have hsr := replyArg_spec hP hR hrc
  obtain ⟨hst1, xs0, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨sd', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : sd' = sd := eq_of_bv hd'.symm
  subst hdd
  have hsT : sd' ∈ T := hQ.mem sd' (by simp)
  have hsa := hP.tcb sd' hsT
  have hxs := hR.at_tcb hsT hks
  have hs4 : (L.mem s (tStA sd')).val = 4 := (hB sd' (by simp)).1
  have hsb : L.mem s (tBlockA sd') = e := (hB sd' (by simp)).2
  obtain ⟨e', dd, hstd⟩ := tsCode_four (hxs.st.symm.trans hs4)
  have he' : e' = e.bv := by
    have := hxs.blk e' (by rw [hstd]; rfl); rw [hsb] at this; exact this.symm
  subst he'
  obtain ⟨hbadge, hflags⟩ := hxs.send _ _ hstd
  have hts : t ≠ sd' := by
    intro h; subst h; exact hnb.2 (hxt.st.symm.trans hs4)
  have hse : sd'.bv ≠ e.bv := kheap_ne hks hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  apply receive_ipc_pre s a t e cb c1 c2 c3 c4 blk rc rc' rv hrc hbound
  step as ⟨st0, hst0⟩
  rw [hst0, epState_eq, hst1]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.2]; decide)]
  unfold endpoint.receive_from_sender
  step as ⟨q0, hq0⟩
  have hhead : q0.head = sd' := by rw [hq0, epQ_eq]; exact hQ.head
  rw [hhead]
  refine WP.spec_bind (ep_dequeue_rel hH hP s σ hR hSR he hk (d := sd') (by simp [Fl4Spec.Endpoint.epQueue])) ?_
  rintro s1 ⟨e1, hR1, hS1, hA1⟩
  set σ1 := updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hks1 : σ1.kheap sd'.bv = some (.tcb xs) := by simp [σ1, hse, hks]
  have hbw : L.mem s1 (tBadgeA sd') = L.mem s (tBadgeA sd') := hA1 _ (a_badge hsa).1 ⟨sd', hsT, (a_badge hsa).2⟩
  have hfw : L.mem s1 (tFlagsA sd') = L.mem s (tFlagsA sd') := hA1 _ (a_flags hsa).1 ⟨sd', hsT, (a_flags hsa).2⟩
  step as ⟨bdg, hbdg⟩
  step as ⟨fl, hfl⟩
  step as ⟨i, hi, hi'⟩
  step as ⟨i1, hi1, hi1'⟩
  step as ⟨i2, hi2, hi2'⟩
  have hg : (i != 0#u64) = dd.senderCanGrant := by
    rw [← flags_grant dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi
  have hc : (i2 != 0#u64) = false := by
    rw [← hcall _ _ hstd, ← flags_call dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi2
  have hbb : bdg.bv = dd.senderBadge := by rw [hbdg, hbw]; exact hbadge
  have hcaps' := hcaps _ _ hstd
  rw [← hg] at hcaps'
  refine WP.spec_bind (do_ipc_transfer_buf hH hBf hBm hP s1 a σ1 hR1 hS1 hsT ht (Ne.symm hts) hks1 hkt1 hfs hrb e bdg
    (i != 0#u64) hcaps') ?_
  rintro s2 ⟨σ2, e2, hR2, hS2, hA2, hk2o, x2, hkt2, -⟩
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv σ1 =
      ({((), σ2)}, False) := by rw [← hbb, ← hg]; exact e2
  have hst' : sd'.bv ≠ t.bv := bv_inj (Ne.symm hts)
  have hks2 : σ2.kheap sd'.bv = some (.tcb xs) := (hk2o _ hst').trans hks1
  have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) :=
    (hk2o _ hte.symm).trans (by simp [σ1])
  refine WP.spec_bind (hTl.sporadicAssert s2 σ2 sd' hR2 hS2 hsT) ?_
  rintro s3 ⟨σ3, hA, hf3, hv3, hS3⟩
  have hR3 := hR2.frame hP hf3 hv3
  obtain ⟨xs3, hks3, hs3st, -, -, hs3f, -⟩ := hv3.2.2.1 _ _ hks2
  have hk3e := hv3.1 _ _ hk2e
  have hxs3 := hR3.at_tcb hsT hks3
  step as ⟨ft, hft⟩
  have hft0 : ft = fl4_abi.consts.fault.NullFault := by
    rw [hft, hxs3.fault0.2 (hs3f.trans hfs)]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hc, hft0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  -- the sender is in no queue
  have hb3 : L.mem s3 (tBlockA sd') = e := by
    rw [hf3 _ (a_blk hsa).1 (Or.inr (Or.inr (Or.inl ⟨sd', hsT, Or.inl (a_blk hsa).2⟩)))]
    rw [hA2 _ (a_blk hsa).1 ⟨?_, ?_⟩, hA1 _ (a_blk hsa).1 ⟨sd', hsT, (a_blk hsa).2⟩, hsb]
    · rintro ⟨r', hr'⟩
      have := tcb_disj hP ht hsT hts.symm
      rw [val_blk hsa, regA_val hta (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hw, he'⟩
      have := hP.bt wp hw sd' hsT
      have := congrArg UScalar.val he'
      rw [val_blk hsa] at this; omega
  have hq3 := dequeued_not_queued hR3 he hb3 hk3e (epDeq_not_mem _)
  refine WP.spec_bind (set_thread_state_rel hH hP s3 σ3 hR3 hS3 hsT hks3 hq3 .running (by simp [tsCode])
    sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
  rintro s4 ⟨hR4, hS4⟩
  have hspec := receiveIpc_send_eq b rights blk hsr hkt hbn hk hks hse hstd (hcall _ _ hstd) e2' hA hks3
    (hs3f.trans hfs)
  rw [hspec]
  refine WP.spec_mono (hTl.switchTo s4 a _ sd' hR4 hS4 hsT) ?_
  rintro ⟨s5, a5⟩ ⟨ha5, hnf, σ', hm, hf, hv, hS'⟩
  exact ⟨ha5, hnf, σ', hm, hR4.frame hP hf hv, hS'⟩

end

end

end Fl4Proofs.P3.Endp
