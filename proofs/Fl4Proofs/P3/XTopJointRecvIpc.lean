/-
P3 (DESIGN.md §9), IPC: **`receive_ipc` at `J`** (KENTRY-PLAN.md item 6,
toward XTopJointDispatch's `JRecvIpcHyp`).

* `JAtZ.recvIpcPollJ`: a polling receive (`blocking = false`) of a thread
  with no bound notification, on an endpoint with no waiting sender, with a
  null reply cap or one whose reply object is not linked to a thread
  (EpRecv's `ReplyArg`): the badge register := 0 (the spec's
  `doNbrecvFailedTransfer`, EpRecv's `receiveIpc_noSend`), one register write
  at `J` (`JAtZ.regWrJ`, `badge_wr_irel`); FL4's side by EpRecv's
  `receive_ipc_pre` (`receive_ipc_poll_eq`).
* `jRecvIpcHyp_of`: `JRecvIpcHyp` from it and `JRecvIpcRestHyp` [W], the
  other cases (a blocking receive, a waiting sender, a bound notification,
  a reply object linked to another thread: `take_reply`'s `cancel_ipc`);
  `dispatch_recvJR`: `dispatch_recvJS` with it.
-/
import Fl4Proofs.P3.XTopJointRecvSig
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- FL4's polling `receive_ipc` with no bound notification on an idle or
receiving endpoint, the reply cap as in `ReplyArg`: the badge register := 0. -/
theorem receive_ipc_poll_eq {R : Set U64} {s : S} {a : A} {t e cb : U64} {c1 c2 c3 c4 : Bool}
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg R (L.mem s) rc rc' rv)
    (hbound : L.mem s (tBoundA t) = 0#u64) (hst : stOf (L.mem s) e = 0#u64 ∨ stOf (L.mem s) e = 2#u64) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) false rc ⦃ r =>
      r = (L.wr s (regA t (regIdx Fl4Spec.badge_register)) 0#u64, a) ⦄ := by
  have key : (do
      let s3 ← endpoint.wait_for_sender st s t e false rv
      ok (s3, a)) ⦃ r => r = (L.wr s (regA t (regIdx Fl4Spec.badge_register)) 0#u64, a) ⦄ := by
    unfold endpoint.wait_for_sender
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (obj.Tcb.set_reg.spec s t layout.reg.BADGE 0#u64) ?_
    rintro s1 rfl
    rw [WP.spec_ok, regIdx_badge]
  apply receive_ipc_pre s a t e cb c1 c2 c3 c4 false rc rc' rv hrc hbound
  refine WP.spec_bind (P1.obj.Ep.state.spec s e) ?_
  rintro v rfl
  rw [epState_eq]
  rcases hst with h | h
  · rw [h, if_pos ep_state_vals.1.symm]
    exact key
  · rw [h, if_neg (by rw [ep_state_vals.1]; decide), if_pos ep_state_vals.2.2.symm]
    exact key

set_option maxHeartbeats 8000000 in
/-- **A polling receive at `J`** (module docstring). -/
theorem JAtZ.recvIpcPollJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hbn : xt.tcbBoundNotification = none)
    {e : U64} (he : e ∈ Z.E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hns : ∀ q, x ≠ .sendEP q) (cb : U64) (c1 c2 c3 c4 : Bool)
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) false rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hR := hI.1.toE
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hbound : L.mem s (tBoundA t) = 0#u64 := optRef_none (hxt.bound.symm.trans hbn)
  have hst : stOf (L.mem s) e = 0#u64 ∨ stOf (L.mem s) e = 2#u64 := by
    cases x with
    | idleEP => exact Or.inl hx.1
    | recvEP q => exact Or.inr hx.1
    | sendEP q => exact absurd rfl (hns q)
  refine WP.spec_mono (receive_ipc_poll_eq (arI := arI) (a := a) (cb := cb) (c1 := c1) (c2 := c2) (c3 := c3)
    (c4 := c4) hrc hbound hst) ?_
  rintro r rfl
  have hspec0 := receiveIpc_noSend b rights false (replyArg_spec J.ip.e hR hrc) hkt hbn hk hns
  have hspec : Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ =
      ({((), updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register (0#u64 : U64).bv)))}, False) := by
    rw [hspec0]
    unfold Fl4Spec.receiveIpcBlocked Fl4Spec.doNbrecvFailedTransfer
    rw [if_neg (by simp), nd_bind_one (asUser_setRegister_eq _ _ hkt)]
    rfl
  have hXb := badge_wr_irel J.ip hI ht hkt 0#u64
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V1, J1⟩ := J.regWrJ ht hkt Fl4Spec.badge_register 0#u64 hXb
  rw [hspec]
  exact ⟨_, Set.mem_singleton _, J1.xtop.relTop, _, _, _, _, _, _, J1⟩

/-- The case `JAtZ.recvIpcPollJ` proves: polling, no bound notification, no
waiting sender, the reply cap null or naming a reply object not linked to a
thread. -/
def RecvIpcPollCase (ct : U64) (blocking : Bool) (s : S) (σ : Fl4Spec.State Unit) (p : U64)
    (rc : capability.Cap) : Prop :=
  blocking = false ∧ (∀ xt, σ.kheap ct.bv = some (.tcb xt) → xt.tcbBoundNotification = none) ∧
    (∀ x, σ.kheap p.bv = some (.endpoint x) → ∀ q, x ≠ .sendEP q) ∧
    (rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (rTcbA q) = 0#u64)

variable (arI) in
/-- **`receive_ipc` at `J`, the cases not proved** [W] (KENTRY-PLAN.md item 6;
IpcLeaves' `recv_ipc_leaf` is at `IRel` only, and there without a bound
notification): `JRecvIpcHyp` outside `RecvIpcPollCase`. -/
def JRecvIpcRestHyp (AR : A → Fl4Spec.Cr3 → Prop) (ct : U64) (blocking : Bool) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    ¬ RecvIpcPollCase (L := L) ct blocking s σ p rc →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) blocking rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄

set_option maxHeartbeats 4000000 in
/-- **`JRecvIpcHyp` from `JRecvIpcRestHyp`** (`JAtZ.recvIpcPollJ` for
`RecvIpcPollCase`). -/
theorem jRecvIpcHyp_of {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T) (blocking : Bool)
    (hW : JRecvIpcRestHyp (L := L) arI AR ct blocking s a σ) :
    JRecvIpcHyp (L := L) arI AR ct blocking s a σ := by
  intro p b sd g gr rc rc' hpE hrc
  by_cases hc : RecvIpcPollCase (L := L) ct blocking s σ p rc
  swap
  · exact hW p b sd g gr rc rc' hpE hrc hc
  obtain ⟨rfl, hbn, hns, hrr⟩ := hc
  obtain ⟨xe, hke⟩ := hpE
  obtain ⟨e, he, h⟩ := J.obj.ep _ xe hke
  rw [Sched.bv_inj h] at he
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
  have hra : ∃ rv, ReplyArg Z.R (L.mem s) rc rc' rv := by
    rcases hrc with ⟨rfl, rfl⟩ | ⟨hcr, q, g', rfl, xr, hkr⟩
    · exact ⟨0#u64, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · have hrc' : rc' = absCap (.Reply q g') := hcr.abs
      subst hrc'
      obtain ⟨r, hr, h⟩ := J.obj.reply _ xr hkr
      rw [Sched.bv_inj h] at hr
      have h0 : L.mem s (rTcbA q) = 0#u64 := by
        rcases hrr with h | ⟨q', g'', h, h0⟩
        · cases h
        · cases h; exact h0
      exact ⟨q, Or.inr ⟨g', _, rfl, rfl, hr, h0⟩⟩
  obtain ⟨rv, hra⟩ := hra
  exact J.recvIpcPollJ ht hkt (hbn xt hkt) he hke (hns xe hke) b sd true g gr hra b.bv (rightsOf sd true g gr)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_recvJS` with `jRecvIpcHyp_of`**: the receiving syscalls at
`J` against `fl4HandleEvent rep`'s branches; premises the two receive
leaves' remaining cases (`JRecvIpcRestHyp`, `JRecvSigBlockHyp` [W]). -/
theorem dispatch_recvJR (rep : Bool) (hZ : XferHZ L AR Z) (hAT : P0.ArchTotal arI) (s : S) (a : A)
    (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (number : I64) (bl cr : Bool) (hn : RecvSys number bl cr)
    (hW : JRecvIpcRestHyp (L := L) arI AR ct bl s a σ)
    (hB : bl = true → JRecvSigBlockHyp (L := L) arI AR ct s a σ) :
    syscall.dispatch_syscall st arI s a number ⦃ r =>
      ∃ y ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) rep (recvSysOf bl cr)).run σ).1,
        y.1 = .ok () ∧ RJ (L := L) arI AR r.1 r.2 y.2 ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  exact dispatch_recvJS rep hZ hAT s a σ J hni hct hnq hvfh number bl cr hn (jRecvIpcHyp_of J hctT bl hW) hB

end

end

end Fl4Proofs.P3
