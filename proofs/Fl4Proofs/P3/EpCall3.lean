/-
P3 (DESIGN.md §9), endpoints: the call branch of `receive_ipc` from a
waiting sender (`receive_from_sender`, l4v `receive_ipc`):

* `receive_ipc_sendCallPush`: the sender is calling with a grant or
  grant-reply right and the receiver has a reply cap: `reply_push sender
  receiver r` without donation (the sender has no scheduling context, so
  FL4's `can_donate` and l4v's `donate` are both false);
* `receive_ipc_sendCallInactive`: otherwise the sender becomes `Inactive`.

`EpScHyps`: the SC binding of a TCB, related by `SR` (`scRel`), and kept by
the sporadic unblock check on both sides.
-/
import Fl4Proofs.P3.EpCall2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem receiveIpc_sendCallInactive_eq {σ : State Unit} {t e sd : ObjRef} (b : Badge) (rights : CapRights) (blk : Bool)
    {rc' : Cap} {reply : Option ObjRef} (hrc : SpecReplyArg σ rc' reply) {xt : Tcb}
    (hkt : σ.kheap t = some (.tcb xt)) (hb : xt.tcbBoundNotification = none) {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.sendEP (sd :: q)))) {xs : Tcb} (hks : σ.kheap sd = some (.tcb xs))
    (hse : sd ≠ e) {dd : SenderPayload} (hst : xs.tcbState = .blockedOnSend e dd)
    (hcall : dd.senderIsCall = true)
    (hcond : ¬ ((dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) ∧ reply ≠ none)) {σ2 σ3 : State Unit}
    (hT : doIpcTransfer (Z := Unit) sd (some e) dd.senderBadge dd.senderCanGrant t
      (updK σ e (.endpoint (epDeq (.sendEP (sd :: q)) sd))) = ({((), σ2)}, False))
    (hA : specSporadicAssert sd σ2 = ({((), σ3)}, False))
    {xs3 : Tcb} (hks3 : σ3.kheap sd = some (.tcb xs3)) (hf3 : xs3.tcbFault = none) :
    receiveIpc (Z := Unit) t (.endpointCap e b rights) blk rc' σ = setThreadState sd .inactive σ3 := by
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
    simp only [true_or, ↓reduceIte]
    split
    · exfalso; simp_all
    · rfl
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
    simp only [true_or, ↓reduceIte]
    split
    · exfalso; simp_all
    · rfl

theorem receiveIpc_sendCallPush_eq {σ : State Unit} {t e sd : ObjRef} (b : Badge) (rights : CapRights) (blk : Bool)
    {r : ObjRef} {rr : CapRights} {xr : Reply} (hkr : σ.kheap r = some (.reply xr)) (hr : xr.replyTcb = none) {xt : Tcb}
    (hkt : σ.kheap t = some (.tcb xt)) (hb : xt.tcbBoundNotification = none) {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.sendEP (sd :: q)))) {xs : Tcb} (hks : σ.kheap sd = some (.tcb xs))
    (hse : sd ≠ e) {dd : SenderPayload} (hst : xs.tcbState = .blockedOnSend e dd)
    (hcall : dd.senderIsCall = true)
    (hg : dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) {σ2 σ3 : State Unit}
    (hT : doIpcTransfer (Z := Unit) sd (some e) dd.senderBadge dd.senderCanGrant t
      (updK σ e (.endpoint (epDeq (.sendEP (sd :: q)) sd))) = ({((), σ2)}, False))
    (hA : specSporadicAssert sd σ2 = ({((), σ3)}, False))
    {xs3 : Tcb} (hks3 : σ3.kheap sd = some (.tcb xs3)) (hf3 : xs3.tcbFault = none)
    (hsc3 : xs3.tcbSchedContext = none) :
    receiveIpc (Z := Unit) t (.endpointCap e b rights) blk (.replyCap r rr) σ = replyPush sd t r false σ3 := by
  have hks1 : (updK σ e (.endpoint (epDeq (.sendEP (sd :: q)) sd))).kheap sd = some (.tcb xs) := by
    simp [hse, hks]
  unfold receiveIpc
  dsimp only
  rw [nd_pure_bind']
  dsimp only
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
  simp only [true_or, ↓reduceIte]
  rw [if_pos ⟨hg, by simp⟩, nd_bind_one (getTcbObjRef_eq _ hks3), hsc3, nd_pure_bind']
  simp only [ne_eq, not_true_eq_false, false_and, decide_false, the]

end Spec

theorem flags_grantReply (d : Fl4Spec.SenderPayload) :
    ((flagsOf d &&& endpoint.FLAG_GRANT_REPLY) != 0#u64) = d.senderCanGrantReply := by
  unfold flagsOf endpoint.FLAG_GRANT_REPLY
  cases d.senderCanGrant <;> cases d.senderCanGrantReply <;> cases d.senderIsCall <;> decide

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The SC binding of TCBs: related by `SR`, and kept by the spec's sporadic
unblock check. -/
structure EpScHyps (T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop) :
    Prop where
  scRel : ∀ s σ (t : U64) (x : Fl4Spec.Tcb), SR s σ → σ.kheap t.bv = some (.tcb x) → t ∈ T →
    (L.mem s (scA t) = 0#u64 ↔ x.tcbSchedContext = none)
  sporadicSc : ∀ σ σ' (t : U64) (x : Fl4Spec.Tcb), specSporadicAssert t.bv σ = ({((), σ')}, False) →
    σ.kheap t.bv = some (.tcb x) → ∃ y, σ'.kheap t.bv = some (.tcb y) ∧ y.tcbSchedContext = x.tcbSchedContext

end Hyps

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- `receive_ipc_sendCallPush` over the bundled step lemmas (`EpSteps`). -/
theorem receive_ipc_sendCallPush_gen {NS : Fl4Spec.ThreadState → Prop} (hX : EpSteps st A ar T E R B SR NS)
    (hTl : EpTailHyps st A T E R B SR) (hSc : EpScHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    (hrb : ipcBufOf true xt = none)
    {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true)
    (hg : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true)
    (hscn : xs.tcbSchedContext = none)
    (hcaps : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rv : U64} (b' : Bool) (r' : Fl4Spec.CapRights) (hrvR : rv ∈ R) (hrv0 : L.mem s (rTcbA rv) = 0#u64) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk (.Reply rv b') ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk (.replyCap rv.bv r') σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk (.replyCap rv.bv r') σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hta := hP.tcb t ht
  have hbound : L.mem s (tBoundA t) = 0#u64 := optRef_none (hxt.bound.symm.trans hbn)
  have hrc : ReplyArg R (L.mem s) (.Reply rv b') (.replyCap rv.bv r') rv := Or.inr ⟨b', r', rfl, rfl, hrvR, hrv0⟩
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
  apply receive_ipc_pre s a t e cb c1 c2 c3 c4 blk _ _ rv hrc hbound
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
  have hgi : (i != 0#u64) = dd.senderCanGrant := by
    rw [← flags_grant dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi
  have hc : (i2 != 0#u64) = true := by
    have hfc := flags_call dd
    rw [hcall _ _ hstd] at hfc
    have e : i2 = flagsOf dd &&& endpoint.FLAG_CALL := by
      rw [← hflags, ← hfw, ← hfl]; exact UScalar.eq_of_val_eq hi2
    rw [e]; exact hfc
  have hgr : (i1 != 0#u64) = dd.senderCanGrantReply := by
    rw [← flags_grantReply dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi1
  have hbb : bdg.bv = dd.senderBadge := by rw [hbdg, hbw]; exact hbadge
  have hcaps' := hcaps _ _ hstd
  rw [← hgi] at hcaps'
  refine WP.spec_bind (hX.xregs hP s1 a σ1 hR1 hS1 hsT ht (Ne.symm hts) hks1 hkt1 hfs hrb e bdg
    (i != 0#u64) hcaps') ?_
  rintro s2 ⟨e2, hR2, hS2, hA2⟩
  set σ2 := updK σ1 t.bv (.tcb (xferTcb xt xs bdg.bv))
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv σ1 =
      ({((), σ2)}, False) := by rw [← hbb, ← hgi]; exact e2
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
  simp only [hc, hft0, ↓reduceIte]
  -- the sender is in no queue
  have hb3 : L.mem s3 (tBlockA sd') = e := by
    rw [hf3 _ (a_blk hsa).1 (Or.inr (Or.inr (Or.inl ⟨sd', hsT, Or.inl (a_blk hsa).2⟩)))]
    rw [hA2 _ (a_blk hsa).1 ?_, hA1 _ (a_blk hsa).1 ⟨sd', hsT, (a_blk hsa).2⟩, hsb]
    rintro ⟨r', hr'⟩
    have := tcb_disj hP ht hsT hts.symm
    rw [val_blk hsa, regA_val hta (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
  have hq3 := dequeued_not_queued hR3 he hb3 hk3e (epDeq_not_mem _)
  -- the reply object and the sender's SC
  obtain ⟨xr, hkr, hxr⟩ := hR.reply rv hrvR
  rw [hrv0, optRef_zero] at hxr
  have hre : rv.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hrt : rv.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hrs : rv.bv ≠ sd'.bv := kheap_ne hkr hks (fun _ h1 h2 => by subst h1; cases h2)
  have hkr2 : σ2.kheap rv.bv = some (.reply xr) := by simp [σ2, σ1, hre, hrt, hkr]
  obtain ⟨xr3, hkr3, -⟩ := hv3.2.1 _ _ hkr2
  have hkt2 : σ2.kheap t.bv = some (.tcb (xferTcb xt xs bdg.bv)) := by simp [σ2]
  obtain ⟨xt3, hkt3, -⟩ := hv3.2.2.1 _ _ hkt2
  obtain ⟨y, hy, hysc⟩ := hSc.sporadicSc σ2 σ3 sd' xs hA hks2
  rw [hks3] at hy; cases hy
  have hsc3 : xs3.tcbSchedContext = none := hysc.trans hscn
  have hscw : L.mem s3 (scA sd') = 0#u64 := (hSc.scRel s3 σ3 sd' xs3 hS3 hks3 hsT).2 hsc3
  have hspec := receiveIpc_sendCallPush_eq (rr := r') b rights blk hkr hxr hkt hbn hk hks hse hstd (hcall _ _ hstd)
    (hg _ _ hstd) e2' hA hks3 (hs3f.trans hfs) hsc3 (t := t.bv) (r := rv.bv)
  have hrvne : (rv != 0#u64) = true := by simp [rep_ne0 hP hrvR]
  have hpush := hX.push hP s3 a σ3 hR3 hS3 hsT hks3 hkt3 hq3 (hX.ns_ep _ (by rw [hs3st, hstd]; simp [tsCode])) hrvR hkr3
  have hg' := hg _ _ hstd
  cases hgg : dd.senderCanGrant with
  | true =>
    rw [hgg] at hgi
    simp only [hgi, hrvne, ↓reduceIte]
    step as ⟨i3, hi3⟩
    rw [hi3, hscw]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    apply ok_bind_spec
    refine WP.spec_mono hpush ?_
    rintro ⟨s4, a4⟩ ⟨ha4, hp4, hR4, hS4⟩
    rw [hspec, hp4]
    exact ⟨ha4, by simp, _, by simp, hR4, hS4⟩

  | false =>
    rw [hgg] at hgi hg'
    simp only [Bool.false_eq_true, false_or] at hg'
    rw [hg'] at hgr
    simp only [hgi, hgr, hrvne, Bool.false_eq_true, ↓reduceIte]
    step as ⟨i3, hi3⟩
    rw [hi3, hscw]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    apply ok_bind_spec
    refine WP.spec_mono hpush ?_
    rintro ⟨s4, a4⟩ ⟨ha4, hp4, hR4, hS4⟩
    rw [hspec, hp4]
    exact ⟨ha4, by simp, _, by simp, hR4, hS4⟩

/-- **Receive from a calling sender with a grant right, into a reply cap**:
the reply goes to the sender, which becomes `BlockedOnReply` (no donation:
the sender has no scheduling context). -/
theorem receive_ipc_sendCallPush (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hTl : EpTailHyps st A T E R B SR) (hSc : EpScHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    (hrb : ipcBufOf true xt = none)
    {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true)
    (hg : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true)
    (hscn : xs.tcbSchedContext = none)
    (hcaps : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rv : U64} (b' : Bool) (r' : Fl4Spec.CapRights) (hrvR : rv ∈ R) (hrv0 : L.mem s (rTcbA rv) = 0#u64) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk (.Reply rv b') ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk (.replyCap rv.bv r') σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk (.replyCap rv.bv r') σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  receive_ipc_sendCallPush_gen (EpHyps.steps (ar := ar) hH hBf (fun _ => True) (fun _ _ => trivial)) hTl hSc hP s a σ hR hSR ht hkt hnb hbn hrb he hk hks hfs hcall hg hscn hcaps cb c1 c2 c3 c4 b' r' hrvR hrv0 b rights blk

/-- `receive_ipc_sendCallInactive` over the bundled step lemmas (`EpSteps`). -/
theorem receive_ipc_sendCallInactive_gen {NS : Fl4Spec.ThreadState → Prop} (hX : EpSteps st A ar T E R B SR NS)
    (hTl : EpTailHyps st A T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    (hrb : ipcBufOf true xt = none)
    {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true)
    (hcaps : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv)
    (hno : (∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∧ dd.senderCanGrantReply = false) ∨
      rv = 0#u64) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
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
  have hgi : (i != 0#u64) = dd.senderCanGrant := by
    rw [← flags_grant dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi
  have hc : (i2 != 0#u64) = true := by
    have hfc := flags_call dd
    rw [hcall _ _ hstd] at hfc
    have e : i2 = flagsOf dd &&& endpoint.FLAG_CALL := by
      rw [← hflags, ← hfw, ← hfl]; exact UScalar.eq_of_val_eq hi2
    rw [e]; exact hfc
  have hgr : (i1 != 0#u64) = dd.senderCanGrantReply := by
    rw [← flags_grantReply dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi1
  have hbb : bdg.bv = dd.senderBadge := by rw [hbdg, hbw]; exact hbadge
  have hcaps' := hcaps _ _ hstd
  rw [← hgi] at hcaps'
  refine WP.spec_bind (hX.xregs hP s1 a σ1 hR1 hS1 hsT ht (Ne.symm hts) hks1 hkt1 hfs hrb e bdg
    (i != 0#u64) hcaps') ?_
  rintro s2 ⟨e2, hR2, hS2, hA2⟩
  set σ2 := updK σ1 t.bv (.tcb (xferTcb xt xs bdg.bv))
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv σ1 =
      ({((), σ2)}, False) := by rw [← hbb, ← hgi]; exact e2
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
  simp only [hc, hft0, ↓reduceIte]
  -- the sender is in no queue
  have hb3 : L.mem s3 (tBlockA sd') = e := by
    rw [hf3 _ (a_blk hsa).1 (Or.inr (Or.inr (Or.inl ⟨sd', hsT, Or.inl (a_blk hsa).2⟩)))]
    rw [hA2 _ (a_blk hsa).1 ?_, hA1 _ (a_blk hsa).1 ⟨sd', hsT, (a_blk hsa).2⟩, hsb]
    rintro ⟨r', hr'⟩
    have := tcb_disj hP ht hsT hts.symm
    rw [val_blk hsa, regA_val hta (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
  have hq3 := dequeued_not_queued hR3 he hb3 hk3e (epDeq_not_mem _)
  have hcond : ¬ ((dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) ∧ optRef rv ≠ none) := by
    rintro ⟨h1, h2⟩
    rcases hno with h | h
    · obtain ⟨g1, g2⟩ := h _ _ hstd; rw [g1, g2] at h1; simp at h1
    · rw [h, optRef_zero] at h2; exact h2 rfl
  have hspec := receiveIpc_sendCallInactive_eq b rights blk hsr hkt hbn hk hks hse hstd (hcall _ _ hstd) hcond
    e2' hA hks3 (hs3f.trans hfs) (t := t.bv)
  rcases hno with h | h
  · obtain ⟨g1, g2⟩ := h _ _ hstd
    rw [g1] at hgi
    rw [g2] at hgr
    simp only [hgi, hgr, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (hX.sts hP s3 σ3 hR3 hS3 hsT hks3 hq3 (hX.ns_ep _ (by rw [hs3st, hstd]; simp [tsCode])) .inactive (by simp [tsCode])
      sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
    rintro s4 ⟨h1, h2⟩
    simp only [WP.spec_ok]
    rw [hspec, setThreadState_eq _ hks3]
    exact ⟨trivial, by simp, _, by simp, h1, h2⟩
  · simp only [h, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ite_self]
    refine WP.spec_bind (hX.sts hP s3 σ3 hR3 hS3 hsT hks3 hq3 (hX.ns_ep _ (by rw [hs3st, hstd]; simp [tsCode])) .inactive (by simp [tsCode])
      sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
    rintro s4 ⟨h1, h2⟩
    simp only [WP.spec_ok]
    rw [hspec, setThreadState_eq _ hks3]
    exact ⟨trivial, by simp, _, by simp, h1, h2⟩

/-- **Receive from a calling sender without a grant right or without a
reply cap**: the sender becomes `Inactive`. -/
theorem receive_ipc_sendCallInactive (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hTl : EpTailHyps st A T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    (hrb : ipcBufOf true xt = none)
    {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true)
    (hcaps : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv)
    (hno : (∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∧ dd.senderCanGrantReply = false) ∨
      rv = 0#u64) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  receive_ipc_sendCallInactive_gen (EpHyps.steps (ar := ar) hH hBf (fun _ => True) (fun _ _ => trivial)) hTl hP s a σ hR hSR ht hkt hnb hbn hrb he hk hks hfs hcall hcaps cb c1 c2 c3 c4 hrc hno b rights blk

end

end

end Fl4Proofs.P3.Endp
