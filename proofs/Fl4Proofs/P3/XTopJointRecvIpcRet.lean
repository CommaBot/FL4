/-
P3 (DESIGN.md §9), IPC: **`receive_ipc`'s blocking wait with a bound
notification lending the thread its SC at `J`** (KENTRY-PLAN.md item 6
(b-ret); l4v `receive_ipc`'s `maybe_return_sc` for a passive server): the
current thread's bound notification is not active and its SC is the
thread's, so FL4's `maybe_return_sched_context` and the spec's
`maybe_return_sc` give it back BEFORE the wait (the thread still running, in
no queue), then the wait runs on the thread without an SC with a reschedule
pending.

* `receiveIpc_boundR`: the spec's `receive_ipc` is `maybe_return_sc` then
  `receiveIpcBlocked` (the endpoint was read before, `maybe_return_sc` keeps
  it).
* `recvTail`, `recvTail_wait`, `receive_ipc_blockR_red`: FL4's `receive_ipc`
  is `maybe_return_sched_context` then the endpoint-state switch.
* `JAtZ.recvCov_ofW`: the covers of a receive's caps after a step writing in
  `TFoot` (XTopJointRecvIpc's `recvCov_of` at the same state).
* `JAtZ.recvIpcRetJ`: XTopJointRecvSigRet's `JAtZ.maybeReturnJQ` (the
  running current thread: `NotQueued`, P1's `CanBlock` words) to a `JAtZ`
  after it, then XTopJointRecvIpcBlock's `JAtZ.recvIpcBlockJG` there (a
  reschedule pending, the thread with no SC; there the spec's and FL4's
  receive reduce to the wait as a bound notification not lending: the
  notification's SC is not the thread's any more).
-/
import Fl4Proofs.P3.XTopJointRecvIpcBound
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

section Spec
open Fl4Spec

/-- **The spec's blocking receive with a bound notification lending the
thread its SC** (not active), on an endpoint with no waiting sender:
`maybe_return_sc` (outcome `σ2`, `hm`), then the blocking wait at `σ2`. -/
theorem receiveIpc_boundR {σ σ2 : State Unit} {t e n : ObjRef} (b : Badge) (rights : CapRights)
    {rc' : Cap} {reply : Option ObjRef} (hrc : SpecReplyArg σ rc' reply) {xt : Tcb}
    (hkt : σ.kheap t = some (.tcb xt)) (hb : xt.tcbBoundNotification = some n) {x : Endpoint}
    (hk : σ.kheap e = some (.endpoint x)) (hns : ∀ q, x ≠ .sendEP q) {xn : Notification}
    (hkn : σ.kheap n = some (.notification xn)) (hna : isActive xn = false)
    (hm : maybeReturnSc (Z := Unit) n t σ = ({((), σ2)}, False)) :
    receiveIpc (Z := Unit) t (.endpointCap e b rights) true rc' σ = receiveIpcBlocked true t e reply σ2 := by
  have tail : ∀ (f : Unit → NonDet (State Unit) Unit),
      (NonDet.when (xt.tcbBoundNotification ≠ none ∧ true = true) (maybeReturnSc (Z := Unit) (the (some n)) t) >>= f) σ =
        f () σ2 := by
    intro f
    unfold NonDet.when
    rw [if_pos (by simp [hb]), show the (some n) = n from rfl, nd_bind_one hm]
  unfold receiveIpc
  dsimp only
  rw [nd_pure_bind']
  rcases hrc with ⟨rfl, rfl⟩ | ⟨r, rr, xr, rfl, rfl, hkr, hr⟩
  · dsimp only
    rw [nd_pure_bind', nd_bind_one (getEndpoint_eq hk), nd_bind_one (getTcbObjRef_eq _ hkt)]
    simp only [hb]
    rw [nd_bind_one (getNotification_eq hkn), if_neg (by simp [hna]), tail]
    all_goals (cases x <;> first | exact absurd rfl (hns _) | rfl)
  · dsimp only
    rw [nd_bind_one (getReplyTcb_eq hkr)]
    simp only [hr]
    rw [nd_when_false_bind (by simp [hr])]
    rw [nd_pure_bind', nd_bind_one (getEndpoint_eq hk), nd_bind_one (getTcbObjRef_eq _ hkt)]
    simp only [hb]
    rw [nd_bind_one (getNotification_eq hkn), if_neg (by simp [hna]), tail]
    all_goals (cases x <;> first | exact absurd rfl (hns _) | rfl)

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {R : Set U64}

variable (st ar) in
/-- FL4's `receive_ipc` after the bound notification's part: the switch on
the endpoint's state. -/
def recvTail (s : S) (a : A) (t e rv : U64) : Result (S × A) := do
  let st1 ← obj.Ep.state st e s
  if st1 = obj.EP_IDLE then do
    let s3 ← endpoint.wait_for_sender st s t e true rv
    ok (s3, a)
  else if st1 = obj.EP_RECV then do
    let s3 ← endpoint.wait_for_sender st s t e true rv
    ok (s3, a)
  else endpoint.receive_from_sender st ar s a t e rv

/-- `recvTail` on an idle or receiving endpoint: the blocking wait. -/
theorem recvTail_wait {s : S} {a : A} {t e rv : U64}
    (hst : stOf (L.mem s) e = 0#u64 ∨ stOf (L.mem s) e = 2#u64) {P : S × A → Prop}
    (h : (do
      let s3 ← endpoint.wait_for_sender st s t e true rv
      ok (s3, a)) ⦃ P ⦄) :
    recvTail st ar s a t e rv ⦃ P ⦄ := by
  unfold recvTail
  refine WP.spec_bind (P1.obj.Ep.state.spec s e) ?_
  rintro v rfl
  rw [epState_eq]
  rcases hst with h0 | h0
  · rw [h0, if_pos ep_state_vals.1.symm]
    exact h
  · rw [h0, if_neg (by rw [ep_state_vals.1]; decide), if_pos ep_state_vals.2.2.symm]
    exact h

/-- **FL4's blocking receive with a bound notification that is not active**,
any SC: `maybe_return_sched_context`, then `recvTail`. -/
theorem receive_ipc_blockR_red {s : S} {a : A} {t e cb : U64} {c1 c2 c3 c4 : Bool}
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg R (L.mem s) rc rc' rv) {n : U64}
    (hbound : L.mem s (tBoundA t) = n) (hn0 : n ≠ 0#u64) (hstN : stOf (L.mem s) n ≠ obj.NTFN_ACTIVE)
    {P : S × A → Prop}
    (h : notification.maybe_return_sched_context st s n t ⦃ s' => recvTail st ar s' a t e rv ⦃ P ⦄ ⦄) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) true rc ⦃ P ⦄ := by
  have key : (do
      let (s2, a2) ← (do
        let t' ← notification.maybe_return_sched_context st s n t
        ok (t', a))
      let st1 ← obj.Ep.state st e s2
      if st1 = obj.EP_IDLE then do
        let s3 ← endpoint.wait_for_sender st s2 t e true rv
        ok (s3, a2)
      else if st1 = obj.EP_RECV then do
        let s3 ← endpoint.wait_for_sender st s2 t e true rv
        ok (s3, a2)
      else endpoint.receive_from_sender st ar s2 a2 t e rv) ⦃ P ⦄ := by
    have h1 : (do
        let t' ← notification.maybe_return_sched_context st s n t
        ok (t', a)) ⦃ r => recvTail st ar r.1 r.2 t e rv ⦃ P ⦄ ⦄ :=
      WP.spec_bind h fun s' hs' => (WP.spec_ok _).2 hs'
    refine WP.spec_bind h1 ?_
    rintro ⟨s2, a2⟩ hq
    exact hq
  unfold endpoint.receive_ipc
  simp only [capability.Cap.ptr, bind_tc_ok]
  rcases hrc with ⟨rfl, -, rfl⟩ | ⟨b, r', rfl, -, -, h0⟩
  · simp only [endpoint.take_reply, bind_tc_ok]
    step with Endp.obj.Tcb.bound_ntfn.spec as ⟨i, hi⟩
    simp only [hi, hbound]
    rw [if_pos (by simpa using hn0)]
    refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
    rintro v rfl
    rw [epState_eq, if_neg hstN]
    simp only [show (n != 0#u64) = true by simpa using hn0, ↓reduceIte, bind_tc_ok, bind_ok, Bind.bind]
    simpa only [bind_tc_ok, bind_ok, Bind.bind] using key
  · simp only [endpoint.take_reply]
    step with Endp.obj.Reply.tcb.spec as ⟨i, hi⟩
    step with P1.obj.Tcb.is_null.spec as ⟨b, hb⟩
    simp only [hb, hi, h0, decide_true, ↓reduceIte, bind_tc_ok]
    step with Endp.obj.Tcb.bound_ntfn.spec as ⟨j, hj⟩
    simp only [hj, hbound]
    rw [if_pos (by simpa using hn0)]
    refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
    rintro v rfl
    rw [epState_eq, if_neg hstN]
    simp only [show (n != 0#u64) = true by simpa using hn0, ↓reduceIte, bind_tc_ok, bind_ok, Bind.bind]
    simpa only [bind_tc_ok, bind_ok, Bind.bind] using key

end

end Fl4Proofs.P3.Endp

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- The objects of a blocking receive's caps are covered after a step writing
in `TFoot` (both caps held, `J.cover_cap`). -/
theorem JAtZ.recvCov_ofW (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) {p b : U64} {sd g gr : Bool} (he : p ∈ Z.E)
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr)) {rc : capability.Cap}
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc) {rc' : Fl4Spec.Cap} {rv : U64}
    (hra : ReplyArg Z.R (L.mem s) rc rc' rv) :
    ((∀ k, Z.th p = some k → Sched.Covered (L.mem s') Z.G p.val (p.val + max (objSize k) 1)) ∧
      (∀ k, H p = some k → Sched.Covered (L.mem s') Z.G p.val (p.val + 2 ^ k.bits))) ∧
    (rv ≠ 0#u64 →
      (∀ k, Z.th rv = some k → Sched.Covered (L.mem s') Z.G rv.val (rv.val + max (objSize k) 1)) ∧
      (∀ k, H rv = some k → Sched.Covered (L.mem s') Z.G rv.val (rv.val + 2 ^ k.bits))) := by
  have hHe : H p = some .ep := J.zH.2.1 p he
  have hfit := J.kern.heap.fits p _ hHe
  simp only [P1.HKind.bits] at hfit
  obtain ⟨y, hy, hcv⟩ := hHd
  refine ⟨J.cover_cap hw hy (by rw [capAt_capV, hcv]) (fun h => by cases h)
    (ok_inj (phys_eq _).symm) rfl (range_ep p b sd true g gr hfit) fun k hk' => by
      rw [hHe] at hk'; cases hk'
      exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩, fun h0 => ?_⟩
  rcases hra with ⟨-, -, rfl⟩ | ⟨g', r', rfl, -, hrR, -⟩
  · exact absurd rfl h0
  obtain ⟨y', hy', hcv'⟩ := hHr rv g' rfl
  have hHr' : H rv = some .reply := J.zH.2.2.1 rv hrR
  have hfit' := J.kern.heap.fits rv _ hHr'
  simp only [P1.HKind.bits] at hfit'
  exact J.cover_cap hw hy' (by rw [capAt_capV, hcv']) (fun h => by cases h)
    (ok_inj (phys_eq _).symm) rfl (range_reply rv g' hfit') fun k hk' => by
      rw [hHr'] at hk'; cases hk'
      exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩

set_option maxHeartbeats 8000000 in
/-- **The blocking receive with a bound notification lending the thread its
SC at `J`** (module docstring). -/
theorem JAtZ.recvIpcRetJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : Entered σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    {n : U64} (hn : n ∈ Z.N) (hbn : xt.tcbBoundNotification = some n.bv)
    {xn : Fl4Spec.Notification} (hkn : σ.kheap n.bv = some (.notification xn))
    (hna : Fl4Spec.isActive xn = false) (hlend : xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)
    {e : U64} (he : e ∈ Z.E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : Endp.CanBlock true x) {cb : U64} {sd g gr : Bool}
    (hHd : JHeld (L := L) Z.th s (.Endpoint e cb sd true g gr)) {rc : capability.Cap}
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hC : CurInv σ := J.curInv (by rw [hni.2]; intro e; cases e)
  have hnrl : t.bv ∉ σ.releaseQueue := by rw [← hcur]; exact hC.notRel
  have hr : Fl4Spec.runnable xt.tcbState = true := (J.curRun.run hni) xt (by rw [hcur]; exact hkt)
  have hns : ∀ q, x ≠ .sendEP q := fun q h => by subst h; simp [Endp.CanBlock] at hc
  -- the SC `i` lent by the notification, the thread's
  obtain ⟨hl1, hl2⟩ := hlend
  obtain ⟨i0, hi0⟩ := Option.ne_none_iff_exists'.1 hl2
  have hxs0 : xt.tcbSchedContext = some i0 := hl1.symm.trans hi0
  obtain ⟨y, m, hky, -⟩ := J.inv.back t.bv xt i0 hkt hxs0
  obtain ⟨i, hiC, rfl⟩ := J.obj.sc _ y m hky
  have hnqT : NotQueued σ t.bv := ⟨by rw [← hcur]; exact hnq, hnrl⟩
  obtain ⟨σ2, he2, kt, -, ko, ct, -, -, -, hidl, -, rq, a1, -, hrq2⟩ :=
    maybeReturn_shape J.inv hkn hkt hky hxs0 hi0 hnqT
  -- FL4's bound-notification words
  have hxt := hI.1.toE.at_tcb ht hkt
  have hb1 : optRef (L.mem s (tBoundA t)) = some n.bv := hxt.bound.symm.trans hbn
  have hbz : L.mem s (tBoundA t) ≠ 0#u64 := fun e => by rw [e, optRef_zero] at hb1; cases hb1
  have hbound : L.mem s (tBoundA t) = n := by
    rw [Notif.optRef_ne hbz] at hb1; exact P1.eq_of_bv (Option.some.inj hb1)
  have hxn := hI.1.toN.at_ntfn hn hkn
  have hstN : stOf (L.mem s) n ≠ obj.NTFN_ACTIVE := by
    have ho := hxn.obj
    cases hxo : xn.ntfnObj with
    | activeNtfn b0 => simp [Fl4Spec.isActive, hxo] at hna
    | idleNtfn => rw [hxo] at ho; rw [ho.1, ntfn_consts.2.2]; decide
    | waitingNtfn q => rw [hxo] at ho; rw [ho.1, ntfn_consts.2.2]; decide
  have hcb := J.canBlockCur ht hcur hkt hr hni hnq
  have hsp1 := receiveIpc_boundR b rights (replyArg_spec J.ip.e hI.1.toE hrc) hkt hbn hk hns hkn hna he2
  refine receive_ipc_blockR_red hrc hbound (by rw [← hbound]; exact hbz) hstN ?_
  refine WP.spec_mono (J.maybeReturnJQ ht hn hiC hkt hkn hxs0 hi0 hnqT ⟨hcb.nq, hcb.nr, hcb.na⟩
    (fun u hu => by rw [hni.2] at hu; cases hu) (by rw [← hcur]; exact hni.1)) ?_
  rintro s' ⟨hW, σ', he', Ac', Lst', J2⟩
  rw [the_result he2 he'] at J2
  have hI2 := J2.xtop.irelK J2.ks J2.buf
  -- the objects kept by `maybe_return_sc`
  have hte : e.bv ≠ t.bv := fun h => by rw [h, hkt] at hk; cases hk
  have hie : e.bv ≠ i.bv := fun h => by rw [h, hky] at hk; cases hk
  have hk2 : σ2.kheap e.bv = some (.endpoint x) := by rw [ko _ hte hie]; exact hk
  have hnt : n.bv ≠ t.bv := fun h => by rw [h, hkt] at hkn; cases hkn
  have hni' : n.bv ≠ i.bv := fun h => by rw [h, hky] at hkn; cases hkn
  have hkn2 : σ2.kheap n.bv = some (.notification xn) := by rw [ko _ hnt hni']; exact hkn
  have hcur2 : σ2.curThread = t.bv := ct.trans hcur
  have hti2 : σ2.curThread ≠ σ2.idleThread := by rw [ct, hidl]; exact hni.1
  have hnq2 : ∀ d p, σ2.curThread ∉ σ2.readyQueues d p := by rw [hcur2]; exact hrq2
  -- the reply cap at the state after
  have hrc2 : ReplyArg Z.R (L.mem s') rc rc' rv := by
    rcases hrc with h | ⟨bb, r', h1, h2, hrR, h0⟩
    · exact Or.inl h
    refine Or.inr ⟨bb, r', h1, h2, hrR, ?_⟩
    obtain ⟨xr, hkr, hxr⟩ := hI.1.toE.reply rv hrR
    obtain ⟨xr2, hkr2, hxr2⟩ := hI2.1.toE.reply rv hrR
    have hrt : rv.bv ≠ t.bv := fun h => by rw [h, hkt] at hkr; cases hkr
    have hri : rv.bv ≠ i.bv := fun h => by rw [h, hky] at hkr; cases hkr
    rw [ko _ hrt hri, hkr] at hkr2; cases hkr2
    rw [h0, optRef_zero] at hxr
    exact optRef_none (hxr2.symm.trans hxr)
  obtain ⟨hcov, hcovR⟩ := J.recvCov_ofW hW he hHd hHr hrc
  have hx2 := hI2.1.toE.at_ep he hk2
  have hst2 : stOf (L.mem s') e = 0#u64 ∨ stOf (L.mem s') e = 2#u64 := by
    cases x with
    | idleEP => exact Or.inl hx2.1
    | recvEP q => exact Or.inr hx2.1
    | sendEP q => exact absurd rfl (hns q)
  have hsp2 := receiveIpc_boundNA b rights true (replyArg_spec J2.ip.e hI2.1.toE hrc2) kt hbn hk2 hns hkn2 hna
    (fun _ h => h.2 h.1)
  have key := J2.recvIpcBlockJG ht hcur2 hti2 hnq2 (fun h => hnrl (rq _ h)) kt hr (Or.inr ⟨a1 hcur.symm, rfl⟩) he
    hk2 hc hcov hrc2 hcovR cb sd true g gr b rights (m := recvTail st arI s' a t e rv)
    (fun h => recvTail_wait hst2 h) hsp2
  rw [hsp1, ← hsp2]
  exact key

end

end

end Fl4Proofs.P3
