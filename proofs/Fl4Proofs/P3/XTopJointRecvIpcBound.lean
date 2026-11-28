/-
P3 (DESIGN.md §9), IPC: **`receive_ipc`'s blocking wait with a bound idle or
waiting notification at `J`** (KENTRY-PLAN.md item 6 (b-ntfn), the no-op
part): the current thread's bound notification is not active and its SC is
not the thread's, so `maybe_return_sched_context` (FL4) and `maybe_return_sc`
(the spec) do nothing (XTopJointRecvSigBlock's `maybe_return_noop`,
`maybeReturnSc_noop`) and the receive is XTopJointRecvIpcBlock's blocking
wait (`JAtZ.recvIpcBlockNJ`).

* `receive_ipc_blockN_red`: FL4's `receive_ipc` reduced to the wait (as
  EpRecv's `receive_ipc_pre` with the bound notification read).
* `receiveIpc_boundNA`: the spec's `receive_ipc` reduced to
  `receiveIpcBlocked` (as EpRecv's `receiveIpc_noSend`).

(p3J gen 54) Each receive leaf ending in `RJR` / `RJ` here has a post-parametric form `…Q` (post
`RelTopM ∧ Pq`, `Pq` from every `JAtZR` / `JAtZ` at `Z.mv G V` with the entry's `H`, `Cs` by `hPq`; the proof moved
there); the original statement is unchanged and is its one-line instance. No new premises.
-/
import Fl4Proofs.P3.XTopJointRecvIpcBlock
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

section Spec
open Fl4Spec

/-- **The spec's receive with a bound notification that is not active** and
whose SC is not the thread's (when blocking), on an endpoint with no waiting
sender: the blocking or polling wait. -/
theorem receiveIpc_boundNA {σ : State Unit} {t e n : ObjRef} (b : Badge) (rights : CapRights) (blk : Bool)
    {rc' : Cap} {reply : Option ObjRef} (hrc : SpecReplyArg σ rc' reply) {xt : Tcb}
    (hkt : σ.kheap t = some (.tcb xt)) (hb : xt.tcbBoundNotification = some n) {x : Endpoint}
    (hk : σ.kheap e = some (.endpoint x)) (hns : ∀ q, x ≠ .sendEP q) {xn : Notification}
    (hkn : σ.kheap n = some (.notification xn)) (hna : isActive xn = false)
    (hnr : blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)) :
    receiveIpc (Z := Unit) t (.endpointCap e b rights) blk rc' σ = receiveIpcBlocked blk t e reply σ := by
  have tail : ∀ (f : Unit → NonDet (State Unit) Unit),
      (NonDet.when (xt.tcbBoundNotification ≠ none ∧ blk = true) (maybeReturnSc (Z := Unit) (the (some n)) t) >>= f) σ = f () σ := by
    intro f
    cases blk with
    | false => exact nd_when_false_bind (by simp) _ _ _
    | true =>
      unfold NonDet.when
      rw [if_pos (by simp [hb]), show the (some n) = n from rfl, nd_bind_one (Ipc.maybeReturnSc_noop hkn hkt (hnr rfl))]
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

/-- **FL4's blocking receive with a bound notification that is not active**
and whose SC is not the thread's, on an idle or receiving endpoint: the
blocking wait. -/
theorem receive_ipc_blockN_red {s : S} {a : A} {t e cb : U64} {c1 c2 c3 c4 : Bool}
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg R (L.mem s) rc rc' rv) {n : U64}
    (hbound : L.mem s (tBoundA t) = n) (hn0 : n ≠ 0#u64) (hstN : stOf (L.mem s) n ≠ obj.NTFN_ACTIVE)
    (hwn : L.mem s (nScA n) = 0#u64 ∨ L.mem s (nScA n) ≠ L.mem s (P1.scA t))
    (hst : stOf (L.mem s) e = 0#u64 ∨ stOf (L.mem s) e = 2#u64) {P : S × A → Prop}
    (h : (do
      let s3 ← endpoint.wait_for_sender st s t e true rv
      ok (s3, a)) ⦃ P ⦄) :
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
    have hm : (do
        let t' ← notification.maybe_return_sched_context st s n t
        ok (t', a)) ⦃ r => r = (s, a) ⦄ :=
      WP.spec_bind (Sched.maybe_return_noop hwn) fun s' h' => by rw [h']; exact (WP.spec_ok _).2 rfl
    refine WP.spec_bind hm ?_
    rintro ⟨s2, a2⟩ hq
    rw [Prod.mk.injEq] at hq
    rw [hq.1, hq.2]
    refine WP.spec_bind (P1.obj.Ep.state.spec s e) ?_
    rintro v rfl
    rw [epState_eq]
    rcases hst with h0 | h0
    · rw [h0, if_pos ep_state_vals.1.symm]
      exact h
    · rw [h0, if_neg (by rw [ep_state_vals.1]; decide), if_pos ep_state_vals.2.2.symm]
      exact h
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

set_option maxHeartbeats 4000000 in
/-- (p3J gen 54) **`JAtZ.recvIpcBlockNJG` with its post as a parameter** (module docstring: `Pq` from every `JAtZ` at `Z.mv G V` with the entry's `H`, `Cs`; `JAtZ.recvIpcBlockNJG` is its instance at `RJ`). -/
theorem JAtZ.recvIpcBlockNJGQ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hti : σ.curThread ≠ σ.idleThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (hnrl : t.bv ∉ σ.releaseQueue)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hr : Fl4Spec.runnable xt.tcbState = true)
    (hsa : σ.schedulerAction = .resumeCurThread ∨
      (σ.schedulerAction = .chooseNewThread ∧ xt.tcbSchedContext = none))
    {n : U64} (hn : n ∈ Z.N) (hbn : xt.tcbBoundNotification = some n.bv)
    {xn : Fl4Spec.Notification} (hkn : σ.kheap n.bv = some (.notification xn))
    (hna : Fl4Spec.isActive xn = false) (hnr : ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none))
    {e : U64} (he : e ∈ Z.E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : Endp.CanBlock true x)
    (hcov : (∀ k, Z.th e = some k → Covered (L.mem s) Z.G e.val (e.val + max (objSize k) 1)) ∧
      (∀ k, H e = some k → Covered (L.mem s) Z.G e.val (e.val + 2 ^ k.bits)))
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (hcovR : rv ≠ 0#u64 → (∀ k, Z.th rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + max (objSize k) 1)) ∧
      (∀ k, H rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + 2 ^ k.bits)))
    (cb : U64) (c1 c2 c3 c4 : Bool) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights)
    {Pq : S → A → Fl4Spec.State Unit → Prop}
    (hPq : ∀ (G : MdbGhost) (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S)
      (a' : A) (σ' : Fl4Spec.State Unit), JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac' Lst' D' s' a' σ' → Pq s' a' σ') :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ).1,
        RelTopM (L := L) r.1 z.2 ∧ Pq r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hns : ∀ q, x ≠ .sendEP q := fun q h => by subst h; simp [Endp.CanBlock] at hc
  have hx := hI.1.toE.at_ep he hk
  have hst2 : stOf (L.mem s) e = 0#u64 ∨ stOf (L.mem s) e = 2#u64 := by
    cases x with
    | idleEP => exact Or.inl hx.1
    | recvEP q => exact Or.inr hx.1
    | sendEP q => exact absurd rfl (hns q)
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
  have hwn : L.mem s (nScA n) = 0#u64 ∨ L.mem s (nScA n) ≠ L.mem s (P1.scA t) := by
    have hsN : xn.ntfnSc = optRef (L.mem s (nScA n)) := hxn.sc
    obtain ⟨Q0, R0, -, hs0⟩ := J.xtop.fin.1.1.1.lists
    obtain ⟨xt0, hkt0, -, -, hsct, -⟩ := hs0.tcb t ht
    rw [hkt] at hkt0; cases hkt0
    by_cases h0 : L.mem s (nScA n) = 0#u64
    · exact Or.inl h0
    · refine Or.inr fun he' => hnr ⟨?_, ?_⟩
      · rw [hsN, he']; exact hsct.symm
      · rw [hsN, Notif.optRef_ne h0]; simp
  exact J.recvIpcBlockJGQ ht hcur hti hnq hnrl hkt hr hsa he hk hc hcov hrc hcovR cb c1 c2 c3 c4 b rights
    (fun h => receive_ipc_blockN_red hrc hbound (by rw [← hbound]; exact hbz) hstN hwn hst2 h)
    (receiveIpc_boundNA b rights true (replyArg_spec J.ip.e hI.1.toE hrc) hkt hbn hk hns hkn hna (fun _ => hnr)) hPq

set_option maxHeartbeats 4000000 in
/-- **The blocking receive with a bound idle or waiting notification at `J`**
(module docstring): the notification's SC is not the thread's (`hnr`); at a
resumed entry or with a reschedule pending when the thread has no SC (`hsa`,
as `JAtZ.recvIpcBlockJG`). -/
theorem JAtZ.recvIpcBlockNJG (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hti : σ.curThread ≠ σ.idleThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (hnrl : t.bv ∉ σ.releaseQueue)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hr : Fl4Spec.runnable xt.tcbState = true)
    (hsa : σ.schedulerAction = .resumeCurThread ∨
      (σ.schedulerAction = .chooseNewThread ∧ xt.tcbSchedContext = none))
    {n : U64} (hn : n ∈ Z.N) (hbn : xt.tcbBoundNotification = some n.bv)
    {xn : Fl4Spec.Notification} (hkn : σ.kheap n.bv = some (.notification xn))
    (hna : Fl4Spec.isActive xn = false) (hnr : ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none))
    {e : U64} (he : e ∈ Z.E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : Endp.CanBlock true x)
    (hcov : (∀ k, Z.th e = some k → Covered (L.mem s) Z.G e.val (e.val + max (objSize k) 1)) ∧
      (∀ k, H e = some k → Covered (L.mem s) Z.G e.val (e.val + 2 ^ k.bits)))
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (hcovR : rv ≠ 0#u64 → (∀ k, Z.th rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + max (objSize k) 1)) ∧
      (∀ k, H rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + 2 ^ k.bits)))
    (cb : U64) (c1 c2 c3 c4 : Bool) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ :=
  JAtZ.recvIpcBlockNJGQ (Pq := fun s' a' σ' => ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a' σ' ∧ VxE Z)
    J ht hcur hti hnq hnrl hkt hr hsa hn hbn hkn hna hnr he hk hc hcov hrc hcovR cb c1 c2 c3 c4 b rights (fun _ _ _ _ _ _ _ _ J' => ⟨_, _, _, _, _, _, J', inferInstance⟩)

/-- **The blocking receive with a bound idle or waiting notification at `J`**
(module docstring): the notification's SC is not the thread's (`hnr`). -/
theorem JAtZ.recvIpcBlockNJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : Entered σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    {n : U64} (hn : n ∈ Z.N) (hbn : xt.tcbBoundNotification = some n.bv)
    {xn : Fl4Spec.Notification} (hkn : σ.kheap n.bv = some (.notification xn))
    (hna : Fl4Spec.isActive xn = false) (hnr : ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none))
    {e : U64} (he : e ∈ Z.E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : Endp.CanBlock true x)
    (hcov : (∀ k, Z.th e = some k → Covered (L.mem s) Z.G e.val (e.val + max (objSize k) 1)) ∧
      (∀ k, H e = some k → Covered (L.mem s) Z.G e.val (e.val + 2 ^ k.bits)))
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (hcovR : rv ≠ 0#u64 → (∀ k, Z.th rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + max (objSize k) 1)) ∧
      (∀ k, H rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + 2 ^ k.bits)))
    (cb : U64) (c1 c2 c3 c4 : Bool) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ :=
  J.recvIpcBlockNJG ht hcur hni.1 hnq (by rw [← hcur]; exact (J.curInv (by rw [hni.2]; intro e; cases e)).notRel) hkt
    ((J.curRun.run hni) xt (by rw [hcur]; exact hkt)) (Or.inl hni.2) hn hbn hkn hna hnr he hk hc hcov hrc hcovR
    cb c1 c2 c3 c4 b rights

end

end

end Fl4Proofs.P3
