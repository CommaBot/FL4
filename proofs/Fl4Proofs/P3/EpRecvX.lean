/-
P3 (DESIGN.md §9), endpoints: **`receive_ipc` from a calling or faulted
sender, over an abstract transfer** (`hXf`, with `XferPost`: the post of the
bundle's `xbuf`). FL4 treats a sender with a fault like a calling one
(`receive_from_sender`'s `ftype != NullFault` branch), as l4v does
(`senderIsCall ∨ fault ≠ none`): `receive_ipc_cfPush_gen`,
`receive_ipc_cfInactive_gen`. The transfer can be the registers-only one,
into a receive buffer, or of a fault.
-/
import Fl4Proofs.P3.EpCall3
import Fl4Proofs.P3.EpRecvBuf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem receiveIpc_cfInactive_eq {σ : State Unit} {t e sd : ObjRef} (b : Badge) (rights : CapRights) (blk : Bool)
    {rc' : Cap} {reply : Option ObjRef} (hrc : SpecReplyArg σ rc' reply) {xt : Tcb}
    (hkt : σ.kheap t = some (.tcb xt)) (hb : xt.tcbBoundNotification = none) {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.sendEP (sd :: q)))) {xs : Tcb} (hks : σ.kheap sd = some (.tcb xs))
    (hse : sd ≠ e) {dd : SenderPayload} (hst : xs.tcbState = .blockedOnSend e dd)
    (hcond : ¬ ((dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) ∧ reply ≠ none)) {σ2 σ3 : State Unit}
    (hT : doIpcTransfer (Z := Unit) sd (some e) dd.senderBadge dd.senderCanGrant t
      (updK σ e (.endpoint (epDeq (.sendEP (sd :: q)) sd))) = ({((), σ2)}, False))
    (hA : specSporadicAssert sd σ2 = ({((), σ3)}, False))
    {xs3 : Tcb} (hks3 : σ3.kheap sd = some (.tcb xs3)) (hcf : dd.senderIsCall = true ∨ xs3.tcbFault ≠ none) :
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
    rw [nd_pure_bind', nd_bind_one hT, nd_bind_assoc, nd_bind_one (show (getTcbObjRef Tcb.tcbSchedContext sd >>= ifSporadicCurScAssertRefillUnblockCheck) σ2 = _ from hA), nd_bind_one (threadGet_eq _ hks3)]
    rw [if_pos hcf]
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
    rw [nd_pure_bind', nd_bind_one hT, nd_bind_assoc, nd_bind_one (show (getTcbObjRef Tcb.tcbSchedContext sd >>= ifSporadicCurScAssertRefillUnblockCheck) σ2 = _ from hA), nd_bind_one (threadGet_eq _ hks3)]
    rw [if_pos hcf]
    split
    · exfalso; simp_all
    · rfl

theorem receiveIpc_cfPush_eq {σ : State Unit} {t e sd : ObjRef} (b : Badge) (rights : CapRights) (blk : Bool)
    {r : ObjRef} {rr : CapRights} {xr : Reply} (hkr : σ.kheap r = some (.reply xr)) (hr : xr.replyTcb = none) {xt : Tcb}
    (hkt : σ.kheap t = some (.tcb xt)) (hb : xt.tcbBoundNotification = none) {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.sendEP (sd :: q)))) {xs : Tcb} (hks : σ.kheap sd = some (.tcb xs))
    (hse : sd ≠ e) {dd : SenderPayload} (hst : xs.tcbState = .blockedOnSend e dd)
    (hg : dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) {σ2 σ3 : State Unit}
    (hT : doIpcTransfer (Z := Unit) sd (some e) dd.senderBadge dd.senderCanGrant t
      (updK σ e (.endpoint (epDeq (.sendEP (sd :: q)) sd))) = ({((), σ2)}, False))
    (hA : specSporadicAssert sd σ2 = ({((), σ3)}, False))
    {xs3 : Tcb} (hks3 : σ3.kheap sd = some (.tcb xs3)) (hcf : dd.senderIsCall = true ∨ xs3.tcbFault ≠ none)
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
  rw [nd_pure_bind', nd_bind_one hT, nd_bind_assoc, nd_bind_one (show (getTcbObjRef Tcb.tcbSchedContext sd >>= ifSporadicCurScAssertRefillUnblockCheck) σ2 = _ from hA), nd_bind_one (threadGet_eq _ hks3)]
  rw [if_pos hcf]
  rw [if_pos ⟨hg, by simp⟩, nd_bind_one (getTcbObjRef_eq _ hks3), hsc3, nd_pure_bind']
  simp only [ne_eq, not_true_eq_false, false_and, decide_false, the]

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- The post of a transfer step (the bundle's `xbuf`). -/
def XferPost (T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop) (s : S)
    (σ : Fl4Spec.State Unit) (snd rcv ep badge : U64) (grant : Bool) (xr : Fl4Spec.Tcb) (s' : S) : Prop :=
  ∃ σ', Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
    EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ∧
    Agree (L.mem s) (L.mem s') (fun b => AllTF T b ∧ ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
    KeepNC σ σ' rcv.bv ∧ ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState

theorem receive_ipc_cfPush_gen {NS : Fl4Spec.ThreadState → Prop} {GC : Prop} (hX : EpSteps st A ar T E R B SR NS GC)
    (hTl : EpTailHyps st A T E R B SR) (hSc : EpScHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    
    {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs))
    (hXf : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → ∀ (s1 : S) (σ1 : Fl4Spec.State Unit) (bdg : U64),
      EpStateRel T E R B (L.mem s1) σ1 → SR s1 σ1 → σ1.kheap sd.bv = some (.tcb xs) →
      σ1.kheap t.bv = some (.tcb xt) →
      ipc.do_ipc_transfer st ar s1 a sd e bdg dd.senderCanGrant t ⦃ s' => XferPost (L := L) T E R B SR s1 σ1 sd t e bdg
        dd.senderCanGrant xt s' ⦄)
    (hcf : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true ∨ xs.tcbFault ≠ none)
    (hg : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true)
    (hscn : xs.tcbSchedContext = none)
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
  have hgr : (i1 != 0#u64) = dd.senderCanGrantReply := by
    rw [← flags_grantReply dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi1
  have hbb : bdg.bv = dd.senderBadge := by rw [hbdg, hbw]; exact hbadge
  rw [hgi]
  refine WP.spec_bind (hXf _ _ hstd s1 σ1 bdg hR1 hS1 hks1 hkt1) ?_
  rintro s2 ⟨σ2, e2, hR2, hS2, hA2, hk2o, x2, hkt2, -⟩
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv σ1 =
      ({((), σ2)}, False) := by rw [← hbb]; exact e2
  have hst' : sd'.bv ≠ t.bv := bv_inj (Ne.symm hts)
  have hks2 : σ2.kheap sd'.bv = some (.tcb xs) := hk2o.fwd hst' hks1 (fun _ _ e => by cases e)
  have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) :=
    hk2o.fwd hte.symm (by simp [σ1]) (fun _ _ e => by cases e)
  refine WP.spec_bind (hTl.sporadicAssert s2 σ2 sd' hR2 hS2 hsT) ?_
  rintro s3 ⟨σ3, hA, hf3, hv3, hS3⟩
  have hR3 := hR2.frame hP hf3 hv3
  obtain ⟨xs3, hks3, hs3st, -, -, hs3f, -⟩ := hv3.2.2.1 _ _ hks2
  have hk3e := hv3.1 _ _ hk2e
  have hxs3 := hR3.at_tcb hsT hks3
  step as ⟨ft, hft⟩
  have hcf3 : dd.senderIsCall = true ∨ xs3.tcbFault ≠ none := by rw [hs3f]; exact hcf _ _ hstd
  have hbr : (i2 != 0#u64) = true ∨ ((i2 != 0#u64) = false ∧ (ft != fl4_abi.consts.fault.NullFault) = true) := by
    have e : i2 = flagsOf dd &&& endpoint.FLAG_CALL := by
      rw [← hflags, ← hfw, ← hfl]; exact UScalar.eq_of_val_eq hi2
    have hfc := flags_call dd
    cases hcc : dd.senderIsCall
    · right
      rw [hcc] at hfc
      refine ⟨by rw [e]; exact hfc, ?_⟩
      have hf3' : xs3.tcbFault ≠ none := by rw [hcc] at hcf3; simpa using hcf3
      have hne : L.mem s3 (tFaultA sd') ≠ 0#u64 := fun h => hf3' (hxs3.fault0.1 h)
      rw [hft]; unfold fl4_abi.consts.fault.NullFault
      simpa using hne
    · left; rw [hcc] at hfc; rw [e]; exact hfc
  rcases hbr with hc | ⟨hc, hfn⟩
  on_goal 1 => simp only [hc, ↓reduceIte]
  on_goal 2 => simp only [hc, hfn, Bool.false_eq_true, ↓reduceIte]
  all_goals
    -- the sender is in no queue
    have hb3 : L.mem s3 (tBlockA sd') = e := by
      rw [hf3 _ (a_blk hsa).1 (Or.inr (Or.inr (Or.inl ⟨sd', hsT, Or.inl (a_blk hsa).2⟩)))]
      rw [hA2 _ (a_blk hsa).1 ⟨⟨sd', hsT, (a_blk hsa).2⟩, ?_, ?_⟩, hA1 _ (a_blk hsa).1 ⟨sd', hsT, (a_blk hsa).2⟩, hsb]
      · rintro ⟨r', hr'⟩
        have := tcb_disj hP ht hsT hts.symm
        rw [val_blk hsa, regA_val hta (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
      · rintro ⟨wp, hw, he'⟩
        have := hP.bt wp hw sd' hsT
        have := congrArg UScalar.val he'
        rw [val_blk hsa] at this; omega
    have hq3 := dequeued_not_queued hR3 he hb3 hk3e (epDeq_not_mem _)
    -- the reply object and the sender's SC
    obtain ⟨xr, hkr, hxr⟩ := hR.reply rv hrvR
    rw [hrv0, optRef_zero] at hxr
    have hre : rv.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
    have hrt : rv.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
    have hrs : rv.bv ≠ sd'.bv := kheap_ne hkr hks (fun _ h1 h2 => by subst h1; cases h2)
    have hkr2 : σ2.kheap rv.bv = some (.reply xr) :=
        hk2o.fwd hrt (by simp [σ1, hre, hkr]) (fun _ _ e => by cases e)
    obtain ⟨xr3, hkr3, -⟩ := hv3.2.1 _ _ hkr2
    obtain ⟨xt3, hkt3, -⟩ := hv3.2.2.1 _ _ hkt2
    obtain ⟨y, hy, hysc⟩ := hSc.sporadicSc σ2 σ3 sd' xs hA hks2
    rw [hks3] at hy; cases hy
    have hsc3 : xs3.tcbSchedContext = none := hysc.trans hscn
    have hscw : L.mem s3 (scA sd') = 0#u64 := (hSc.scRel s3 σ3 sd' xs3 hS3 hks3 hsT).2 hsc3
    have hspec := receiveIpc_cfPush_eq (rr := r') b rights blk hkr hxr hkt hbn hk hks hse hstd
      (hg _ _ hstd) e2' hA hks3 hcf3 hsc3 (t := t.bv) (r := rv.bv)
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

theorem receive_ipc_cfInactive_gen {NS : Fl4Spec.ThreadState → Prop} {GC : Prop} (hX : EpSteps st A ar T E R B SR NS GC)
    (hTl : EpTailHyps st A T E R B SR) (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    
    {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs))
    (hXf : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → ∀ (s1 : S) (σ1 : Fl4Spec.State Unit) (bdg : U64),
      EpStateRel T E R B (L.mem s1) σ1 → SR s1 σ1 → σ1.kheap sd.bv = some (.tcb xs) →
      σ1.kheap t.bv = some (.tcb xt) →
      ipc.do_ipc_transfer st ar s1 a sd e bdg dd.senderCanGrant t ⦃ s' => XferPost (L := L) T E R B SR s1 σ1 sd t e bdg
        dd.senderCanGrant xt s' ⦄)
    (hcf : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true ∨ xs.tcbFault ≠ none)
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
  have hgr : (i1 != 0#u64) = dd.senderCanGrantReply := by
    rw [← flags_grantReply dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi1
  have hbb : bdg.bv = dd.senderBadge := by rw [hbdg, hbw]; exact hbadge
  rw [hgi]
  refine WP.spec_bind (hXf _ _ hstd s1 σ1 bdg hR1 hS1 hks1 hkt1) ?_
  rintro s2 ⟨σ2, e2, hR2, hS2, hA2, hk2o, x2, hkt2, -⟩
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv σ1 =
      ({((), σ2)}, False) := by rw [← hbb]; exact e2
  have hst' : sd'.bv ≠ t.bv := bv_inj (Ne.symm hts)
  have hks2 : σ2.kheap sd'.bv = some (.tcb xs) := hk2o.fwd hst' hks1 (fun _ _ e => by cases e)
  have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) :=
    hk2o.fwd hte.symm (by simp [σ1]) (fun _ _ e => by cases e)
  refine WP.spec_bind (hTl.sporadicAssert s2 σ2 sd' hR2 hS2 hsT) ?_
  rintro s3 ⟨σ3, hA, hf3, hv3, hS3⟩
  have hR3 := hR2.frame hP hf3 hv3
  obtain ⟨xs3, hks3, hs3st, -, -, hs3f, -⟩ := hv3.2.2.1 _ _ hks2
  have hk3e := hv3.1 _ _ hk2e
  have hxs3 := hR3.at_tcb hsT hks3
  step as ⟨ft, hft⟩
  have hcf3 : dd.senderIsCall = true ∨ xs3.tcbFault ≠ none := by rw [hs3f]; exact hcf _ _ hstd
  have hbr : (i2 != 0#u64) = true ∨ ((i2 != 0#u64) = false ∧ (ft != fl4_abi.consts.fault.NullFault) = true) := by
    have e : i2 = flagsOf dd &&& endpoint.FLAG_CALL := by
      rw [← hflags, ← hfw, ← hfl]; exact UScalar.eq_of_val_eq hi2
    have hfc := flags_call dd
    cases hcc : dd.senderIsCall
    · right
      rw [hcc] at hfc
      refine ⟨by rw [e]; exact hfc, ?_⟩
      have hf3' : xs3.tcbFault ≠ none := by rw [hcc] at hcf3; simpa using hcf3
      have hne : L.mem s3 (tFaultA sd') ≠ 0#u64 := fun h => hf3' (hxs3.fault0.1 h)
      rw [hft]; unfold fl4_abi.consts.fault.NullFault
      simpa using hne
    · left; rw [hcc] at hfc; rw [e]; exact hfc
  rcases hbr with hc | ⟨hc, hfn⟩
  on_goal 1 => simp only [hc, ↓reduceIte]
  on_goal 2 => simp only [hc, hfn, Bool.false_eq_true, ↓reduceIte]
  all_goals
    -- the sender is in no queue
    have hb3 : L.mem s3 (tBlockA sd') = e := by
      rw [hf3 _ (a_blk hsa).1 (Or.inr (Or.inr (Or.inl ⟨sd', hsT, Or.inl (a_blk hsa).2⟩)))]
      rw [hA2 _ (a_blk hsa).1 ⟨⟨sd', hsT, (a_blk hsa).2⟩, ?_, ?_⟩, hA1 _ (a_blk hsa).1 ⟨sd', hsT, (a_blk hsa).2⟩, hsb]
      · rintro ⟨r', hr'⟩
        have := tcb_disj hP ht hsT hts.symm
        rw [val_blk hsa, regA_val hta (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
      · rintro ⟨wp, hw, he'⟩
        have := hP.bt wp hw sd' hsT
        have := congrArg UScalar.val he'
        rw [val_blk hsa] at this; omega
    have hq3 := dequeued_not_queued hR3 he hb3 hk3e (epDeq_not_mem _)
    have hcond : ¬ ((dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) ∧ optRef rv ≠ none) := by
      rintro ⟨h1, h2⟩
      rcases hno with h | h
      · obtain ⟨g1, g2⟩ := h _ _ hstd; rw [g1, g2] at h1; simp at h1
      · rw [h, optRef_zero] at h2; exact h2 rfl
    have hspec := receiveIpc_cfInactive_eq b rights blk hsr hkt hbn hk hks hse hstd hcond
      e2' hA hks3 hcf3 (t := t.bv)
    rcases hno with h | h
    · obtain ⟨g1, g2⟩ := h _ _ hstd
      rw [g1] at hgi
      rw [g2] at hgr
      simp only [hgi, hgr, g1, Bool.false_eq_true, ↓reduceIte]
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

end

end

end Fl4Proofs.P3.Endp
