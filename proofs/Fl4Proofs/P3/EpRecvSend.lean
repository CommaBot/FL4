/-
P3 (DESIGN.md §9), endpoints: **`receive_ipc` on an endpoint with a waiting
sender refines l4v `receive_ipc`** (`Z = Unit`), for a sender that is not
calling and has no fault (`receive_ipc_send`): the sender is dequeued
(`ep_dequeue_rel`), its badge and grant right read from its block words
(l4v `BlockedOnSend` payload), the message transferred
(`do_ipc_transfer_regs`: receiver without IPC buffer, no extra caps), the
sporadic check of the sender (`EpTailHyps.sporadicAssert`), the sender set
running, then `possible_switch_to` (`EpTailHyps.switchTo`).

Same scope as `receive_ipc_block` for the receiver (no bound notification,
reply cap as in `ReplyArg`). The spec does not fail, and FL4's outcome is
related to one of the spec's.
-/
import Fl4Proofs.P3.EpSend
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

theorem flags_grant (d : Fl4Spec.SenderPayload) : ((flagsOf d &&& endpoint.FLAG_GRANT) != 0#u64) = d.senderCanGrant := by
  unfold flagsOf endpoint.FLAG_GRANT
  cases d.senderCanGrant <;> cases d.senderCanGrantReply <;> cases d.senderIsCall <;> decide
theorem flags_call (d : Fl4Spec.SenderPayload) : ((flagsOf d &&& endpoint.FLAG_CALL) != 0#u64) = d.senderIsCall := by
  unfold flagsOf endpoint.FLAG_CALL
  cases d.senderCanGrant <;> cases d.senderCanGrantReply <;> cases d.senderIsCall <;> decide

section Spec
open Fl4Spec

theorem nd_bind_assoc {σ' α β γ : Type} (m : NonDet σ' α) (f : α → NonDet σ' β) (g : β → NonDet σ' γ) (s : σ') :
    (m >>= fun x => f x >>= g) s = ((m >>= f) >>= g) s := by
  simp only [nd_bind_apply']
  ext r
  · simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, y, hy, hr⟩; exact ⟨y, ⟨x, hx, hy⟩, hr⟩
    · rintro ⟨y, ⟨x, hx, hy⟩, hr⟩; exact ⟨x, hx, y, hy, hr⟩
  · simp only [Set.mem_setOf_eq]
    constructor
    · rintro (h | ⟨x, hx, h | ⟨y, hy, h⟩⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨x, hx, h⟩)
      · exact Or.inr ⟨y, ⟨x, hx, hy⟩, h⟩
    · rintro ((h | ⟨x, hx, h⟩) | ⟨y, ⟨x, hx, hy⟩, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, Or.inl h⟩
      · exact Or.inr ⟨x, hx, Or.inr ⟨y, hy, h⟩⟩

/-- The spec's `receive_ipc` from a waiting sender `sd` (not calling, no
fault), without a bound notification, given the outcomes of its steps. -/
theorem receiveIpc_send_eq {σ : State Unit} {t e sd : ObjRef} (b : Badge) (rights : CapRights) (blk : Bool)
    {rc' : Cap} {reply : Option ObjRef} (hrc : SpecReplyArg σ rc' reply) {xt : Tcb}
    (hkt : σ.kheap t = some (.tcb xt)) (hb : xt.tcbBoundNotification = none) {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.sendEP (sd :: q)))) {xs : Tcb} (hks : σ.kheap sd = some (.tcb xs))
    (hse : sd ≠ e) {dd : SenderPayload} (hst : xs.tcbState = .blockedOnSend e dd)
    (hcall : dd.senderIsCall = false) {σ2 σ3 : State Unit}
    (hT : doIpcTransfer (Z := Unit) sd (some e) dd.senderBadge dd.senderCanGrant t
      (updK σ e (.endpoint (epDeq (.sendEP (sd :: q)) sd))) = ({((), σ2)}, False))
    (hA : specSporadicAssert sd σ2 = ({((), σ3)}, False))
    {xs3 : Tcb} (hks3 : σ3.kheap sd = some (.tcb xs3)) (hf3 : xs3.tcbFault = none) :
    receiveIpc (Z := Unit) t (.endpointCap e b rights) blk rc' σ =
      possibleSwitchTo sd (stsAct (updK σ3 sd (.tcb { xs3 with tcbState := .running })) sd) := by
  have hks1 : (updK σ e (.endpoint (epDeq (.sendEP (sd :: q)) sd))).kheap sd = some (.tcb xs) := by
    simp [hse, hks]
  unfold receiveIpc
  dsimp only
  rw [nd_pure_bind']
  rcases hrc with ⟨rfl, rfl⟩ | ⟨r, rr, xr, rfl, rfl, hkr, hr⟩
  · dsimp only
    rw [nd_pure_bind', nd_bind_one (getEndpoint_eq hk), nd_bind_one (getTcbObjRef_eq _ hkt)]
    simp only [hb]
    rw [nd_pure_bind']
    simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte]
    rw [nd_when_false_bind (by simp [hb])]
    rw [nd_bind_one (assert_true (by simp) σ), nd_pure_bind']
    rw [show the (sd :: q).head? = sd from rfl, nd_bind_one (tcbEpDequeue_eq hk (by simp [Endpoint.epQueue])),
      nd_bind_one (getThreadState_eq hks1), hst]
    dsimp only
    rw [nd_pure_bind', nd_bind_one hT, nd_bind_assoc, nd_bind_one (show (getTcbObjRef Tcb.tcbSchedContext sd >>= ifSporadicCurScAssertRefillUnblockCheck) σ2 = _ from hA), nd_bind_one (threadGet_eq _ hks3), hf3, hcall]
    simp only [Bool.false_eq_true, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
    rw [nd_bind_one (setThreadState_eq _ hks3), hf3]
  · dsimp only
    rw [nd_bind_one (getReplyTcb_eq hkr)]
    simp only [hr]
    rw [nd_when_false_bind (by simp [hr])]
    rw [nd_pure_bind', nd_bind_one (getEndpoint_eq hk), nd_bind_one (getTcbObjRef_eq _ hkt)]
    simp only [hb]
    rw [nd_pure_bind']
    simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte]
    rw [nd_when_false_bind (by simp [hb])]
    rw [nd_bind_one (assert_true (by simp) σ), nd_pure_bind']
    rw [show the (sd :: q).head? = sd from rfl, nd_bind_one (tcbEpDequeue_eq hk (by simp [Endpoint.epQueue])),
      nd_bind_one (getThreadState_eq hks1), hst]
    dsimp only
    rw [nd_pure_bind', nd_bind_one hT, nd_bind_assoc, nd_bind_one (show (getTcbObjRef Tcb.tcbSchedContext sd >>= ifSporadicCurScAssertRefillUnblockCheck) σ2 = _ from hA), nd_bind_one (threadGet_eq _ hks3), hf3, hcall]
    simp only [Bool.false_eq_true, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
    rw [nd_bind_one (setThreadState_eq _ hks3), hf3]

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- `receive_ipc_send` over the bundled step lemmas (`EpSteps`). -/
theorem receive_ipc_send_gen {NS : Fl4Spec.ThreadState → Prop} {GC : Prop} (hX : EpSteps st A ar T E R B SR NS GC)
    (hTl : EpTailHyps st A T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    (hrb : ipcBufOf true xt = none)
    {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = false)
    (hcaps : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → GC ∨ dd.senderCanGrant = false ∨ ipcBufOf false xs = none ∨
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
  refine WP.spec_bind (hX.deq hP s σ hR hSR he hk (d := sd') (by simp [Fl4Spec.Endpoint.epQueue])) ?_
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
  refine WP.spec_bind (hX.xregs hP s1 a σ1 hR1 hS1 hsT ht (Ne.symm hts) hks1 hkt1 hfs hrb e bdg
    (i != 0#u64) hcaps') ?_
  rintro s2 ⟨e2, hR2, hS2, hA2⟩
  set σ2 := updK σ1 t.bv (.tcb (xferTcb xt xs bdg.bv))
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv σ1 =
      ({((), σ2)}, False) := by rw [← hbb, ← hg]; exact e2
  have hst' : sd'.bv ≠ t.bv := bv_inj (Ne.symm hts)
  have hks2 : σ2.kheap sd'.bv = some (.tcb xs) := by simp [σ2, hst', hks1]
  have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) := by
    simp [σ2, σ1, hte.symm]
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
    rw [hA2 _ (a_blk hsa).1 ?_, hA1 _ (a_blk hsa).1 ⟨sd', hsT, (a_blk hsa).2⟩, hsb]
    rintro ⟨r', hr'⟩
    have := tcb_disj hP ht hsT hts.symm
    rw [val_blk hsa, regA_val hta (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
  have hq3 := dequeued_not_queued hR3 he hb3 hk3e (epDeq_not_mem _)
  refine WP.spec_bind (hX.sts hP s3 σ3 hR3 hS3 hsT hks3 hq3 (hX.ns_ep _ (by rw [hs3st, hstd]; simp [tsCode])) .running (by simp [tsCode])
    sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
  rintro s4 ⟨hR4, hS4⟩
  have hspec := receiveIpc_send_eq b rights blk hsr hkt hbn hk hks hse hstd (hcall _ _ hstd) e2' hA hks3
    (hs3f.trans hfs)
  rw [hspec]
  refine WP.spec_mono (hTl.switchTo s4 a _ sd' hR4 hS4 hsT) ?_
  rintro ⟨s5, a5⟩ ⟨ha5, hnf, σ', hm, hf, hv, hS'⟩
  exact ⟨ha5, hnf, σ', hm, hR4.frame hP hf hv, hS'⟩

/-- **Receive from a waiting sender** (not calling, no fault; receiver
without IPC buffer and bound notification, no extra caps). -/
theorem receive_ipc_send (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hTl : EpTailHyps st A T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    (hrb : ipcBufOf true xt = none)
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
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  receive_ipc_send_gen (EpHyps.steps (ar := ar) hH hBf (fun _ => True) (fun _ _ => trivial)) hTl hP s a σ hR hSR ht hkt hnb hbn hrb he hk hks hfs hcall (fun e' dd h => Or.inr (hcaps e' dd h)) cb c1 c2 c3 c4 hrc b rights blk

end

end

end Fl4Proofs.P3.Endp
