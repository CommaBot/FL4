/-
P3 (DESIGN.md §9), IPC: **`send_ipc` and `receive_ipc` by endpoint state**,
on `IpcRel ∧ SRT … SRE`, from the `I` and `XG` theorems:

* `send_ipc_top`: idle or sending endpoint (block / no block, IpcEpBlock),
  receiving endpoint (the head receiver: `send_ipc_recvG` / `_bufG` for a
  send, `send_ipc_callG` / `_call_inactiveG` for a call). The receiver's
  reply back-pointer (`hback`) is `SchedValid.recvReply`.
* `receive_ipc_top`: likewise, for the receive side.

What the theorems do not cover is named (`SendRest`, `RecvRest`): a donating
send to a receiver, a call to a receiver with an IPC buffer; on the receive
side, a sender with a fault, a call sender with the receiver's IPC buffer,
a call sender with an SC (the donation).
-/
import Fl4Proofs.P3.IpcEpGrant
import Fl4Proofs.P3.IpcEpBlock
import Fl4Proofs.P3.SchedValidRel
import Fl4Proofs.P3.IpcSendTop
import Fl4Proofs.P3.EpSendX
import Fl4Proofs.P3.IpcEpXfer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **The IPC queues of `O` are sorted by priority**, highest first, at `s`
(seL4's `tcbEPAppend` order). -/
def QSorted (st : machine.Store S) [L : LawfulStore st] (T O : Set U64) (s : S) : Prop :=
  ∀ e ∈ O, ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs

/-- `QSorted` from P1's queue witness (`EpsWit`, endpoints and notifications)
with its lists sorted. -/
theorem qSorted_of_eps {Cs Ω : Set U64} {H : P1.Heap} {s : S} {E' O : Set U64} {EQ : U64 → List U64}
    (hW : P1.EpsWit st T Cs Ω H ∅ s E' EQ) (hTP : TcbPlaced T) (hsub : O ⊆ E')
    (hS : ∀ e ∈ E', PrioSorted (fun y => L.mem s (prioA y)) (EQ e)) : QSorted st T O s := by
  intro e he xs hq
  rw [Sched.eqs_unique hW hTP (hsub he) hq]
  exact hS e (hsub he)

/-- **The native-path scope**: no thread runs a guest (`RunningVM`).
VT-x: RunningVM branch not yet refined (DESIGN §5); named until the VCPU/EPT
round. -/
def NativeScope (σ : Fl4Spec.State Unit) : Prop := ∀ p x, σ.kheap p = some (.tcb x) → x.tcbState ≠ .runningVM

/-- The receiver's reply back-pointer, from `SchedValid`. -/
theorem hback_of {σ : Fl4Spec.State Unit} (hV : Sched.SchedValid σ) {d : Fl4Spec.ObjRef} {xd : Fl4Spec.Tcb}
    (hkd : σ.kheap d = some (.tcb xd)) :
    ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d := by
  intro e' r dd xr hs hkr
  obtain ⟨xr', hkr', h⟩ := hV.recvReply d xd e' r dd hkd hs
  rw [hkr] at hkr'; cases hkr'; exact h

set_option maxHeartbeats 4000000 in
/-- **The transfer step for `receive_ipc_cf*_gen`** on the grant bundle's
relation: the registers-only transfer, into a receive buffer (`stepsG`'s
`xregs`, `xbuf`), or of a faulted sender (`do_ipc_transfer_fault`,
`_faultN`); a timeout-faulted sender has no SC (`hto`). -/
theorem xferX_top (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) {sd t : U64} (hsd : sd ∈ T) (ht : t ∈ T) (hne : sd ≠ t) {xs xt : Fl4Spec.Tcb}
    (hto : ∀ b, xs.tcbFault = some (.timeout b) → xs.tcbSchedContext = none) (a : A) (e : U64) (g : Bool) :
    ∀ (s1 : S) (σ1 : Fl4Spec.State Unit) (bdg : U64), EpStateRel T E R B (L.mem s1) σ1 →
      SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s1 σ1 →
      σ1.kheap sd.bv = some (.tcb xs) → σ1.kheap t.bv = some (.tcb xt) →
      ipc.do_ipc_transfer st ar s1 a sd e bdg g t ⦃ s' => XferPost (L := L) T E R B
        (SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))) s1 σ1 sd t e bdg g xt s' ⦄ := by
  intro s1 σ1 bdg hR1 hS1 hks hkt
  have hX := IpcSchedHyps.stepsG (A := A) hH hBf hBm hP0
  cases hf : xs.tcbFault with
  | none =>
    cases hrb : ipcBufOf true xt with
    | none =>
      exact WP.spec_mono (hX.xregs hP0.e s1 a σ1 hR1 hS1 hsd ht hne hks hkt hf hrb e bdg g (Or.inl trivial))
        fun _ ⟨h1, h2, h3, h4⟩ => ⟨_, h1, h2, h3, h4.mono fun _ h => h.2.1,
          KeepNC.of_eq fun p hp => by simp [hp], xferTcb xt xs bdg.bv, by simp, xferTcb_state _ _ _⟩
    | some rp => exact hX.xbuf hP0.e s1 a σ1 hR1 hS1 hsd ht hne hks hkt hf hrb e bdg g (Or.inl trivial)
  | some f =>
    have hok : FaultOK (L := L) s1 sd xs f := by
      cases f with
      | timeout b =>
        have hsc := hto b hf
        obtain ⟨Q, R0, -, hsp⟩ := hS1.1.1.2.1.lists
        obtain ⟨x, hk', -, -, hscw, -⟩ := hsp.tcb sd hsd
        rw [hks] at hk'; cases hk'
        exact ⟨hsc, optRef_none (hscw.symm.trans hsc)⟩
      | _ => trivial
    have lift : ∀ s' : S, (∃ σ', Fl4Spec.doIpcTransfer (Z := Unit) sd.bv (some e.bv) bdg.bv g t.bv σ1 =
        ({((), σ')}, False) ∧ EpStateRel T E R B (L.mem s') σ' ∧
        SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s' σ' ∧
        Agree (L.mem s1) (L.mem s') (fun b => ¬ RcvReg t b ∧ ¬ BufW B b) ∧
        (∀ q, q ≠ t.bv → σ'.kheap q = σ1.kheap q) ∧
        ∃ x', σ'.kheap t.bv = some (.tcb x') ∧ x'.tcbState = xt.tcbState) →
        XferPost (L := L) T E R B (SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))) s1 σ1 sd t e
          bdg g xt s' :=
      fun _ ⟨σ', h1, h2, h3, h4, h5, x', h6, h7⟩ =>
        ⟨σ', h1, h2, ⟨h3, ntfn_lift_rcv hP0.toC hS1.2 h2 ht h4 h5 hkt h6 h7⟩, h4.mono fun _ h => h.2,
          KeepNC.of_eq h5, x', h6, h7⟩
    cases hrb : ipcBufOf true xt with
    | none =>
      exact WP.spec_mono (do_ipc_transfer_faultN (ar := ar) (hH.epHyps hP0) hBf.srs hP0.e s1 a σ1 hR1 hS1.1 hsd ht
        hne hks hkt hf hok hrb e bdg g) lift
    | some rp =>
      exact WP.spec_mono (do_ipc_transfer_fault (ar := ar) (hH.epHyps hP0) hBm.srs hP0.e s1 a σ1 hR1 hS1.1 hsd ht
        hne hks hkt hf hok hrb e bdg g) lift

/-- **What `send_ipc_top` does not cover**: a send to a waiting receiver that
donates (`can_donate`, `schedContextDonate`). -/
def SendRest (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (Rel : S → Fl4Spec.State Unit → Prop)
    (T : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (blk call : Bool) (badge : U64) (g gr don : Bool)
    (t e : U64) : Prop :=
  ∀ (d : U64) q xd, σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))) → d ∈ T →
    σ.kheap d.bv = some (.tcb xd) → don = true →
    t ∈ T → ∀ xt, σ.kheap t.bv = some (.tcb xt) → (tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) →
    tsCode xt.tcbState ≠ 6 → xt.tcbFault = none → Sched.SchedValid σ → SVK.TailOK σ →
    endpoint.send_ipc st ar s a blk call badge g gr don t e ⦃ r => r.2 = a ∧
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call badge.bv g gr don t.bv e.bv σ).1, Rel r.1 z.2 ⦄

set_option maxHeartbeats 4000000 in
/-- **`send_ipc` on `IpcRel ∧ SRT … SRE`**, by the endpoint's state. -/
theorem send_ipc_top (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ)
    (hV : Sched.SchedValid σ) (hTO : SVK.TailOK σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    (hns : tsCode xt.tcbState ≠ 6) (hft : xt.tcbFault = none)
    {e : U64} (he : e ∈ E)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (blk call : Bool) (badge : U64) (g gr don : Bool)
    (hU : SendRest st ar (fun s σ => IpcRel N T E R B (L.mem s) σ ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ)
      T s a σ blk call badge g gr don t e) :
    endpoint.send_ipc st ar s a blk call badge g gr don t e ⦃ r => r.2 = a ∧
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call badge.bv g gr don t.bv e.bv σ).1,
        IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 z.2 ⦄ := by
  obtain ⟨x, hk, hx⟩ := hR.ep e he
  have blockCase : CanBlock false x → endpoint.send_ipc st ar s a blk call badge g gr don t e ⦃ r => r.2 = a ∧
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call badge.bv g gr don t.bv e.bv σ).1,
        IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 z.2 ⦄ := by
    intro hc
    cases blk
    · exact WP.spec_mono (send_ipc_noblockI (ar := ar) s a σ hR hSR he hk hc call badge g gr don t)
        fun _ ⟨h1, σ', h2, h3, h4⟩ => ⟨h1, ((), σ'), by rw [h2]; rfl, h3, h4⟩
    · exact WP.spec_mono (send_ipc_blockI hH hP s a σ hR hSR ht hkt hnb hnn he hk hc hsort call badge g gr don)
        fun _ ⟨h1, σ', h2, h3, h4⟩ => ⟨h1, ((), σ'), by rw [h2]; rfl, h3, h4⟩
  cases x with
  | idleEP => exact blockCase trivial
  | sendEP q => exact blockCase rfl
  | recvEP q =>
    obtain ⟨-, xs, hne, hq, hQ, hQO⟩ := hx
    obtain ⟨d, ys, rfl⟩ : ∃ d ys, xs = d :: ys := by
      cases xs with
      | nil => exact absurd rfl hne
      | cons d ys => exact ⟨d, ys, rfl⟩
    have hd : d ∈ T := hQ.mem d (by simp)
    obtain ⟨xd, hkd, -⟩ := hR.tcb d hd
    have hk' : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: ys.map UScalar.bv))) := by rw [hk, hq]; rfl
    have hback := hback_of hV hkd
    have cv : ∀ r : S × A, (r.2 = a ∧ ¬ (Fl4Spec.sendIpc (Z := Unit) blk call badge.bv g gr don t.bv
        e.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk call badge.bv g gr don t.bv e.bv σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 σ') →
        r.2 = a ∧ ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call badge.bv g gr don t.bv e.bv σ).1,
          IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 z.2 :=
      fun _ ⟨h1, _, σ', h2, h3, h4⟩ => ⟨h1, ((), σ'), h2, h3, h4⟩
    cases don
    swap
    · exact hU d _ xd hk' hd hkd rfl ht xt hkt hnb hns hft hV hTO
    cases call
    · cases hrb : ipcBufOf true xd with
      | none =>
        exact WP.spec_mono (send_ipc_recvG hH hBf hBm hTl hP s a σ hR hSR ht hkt hnb hft he hk' hkd hrb badge g gr
          hback hTO blk) cv
      | some rp =>
        exact WP.spec_mono (send_ipc_recv_bufG hH hBf hBm hTl hP s a σ hR hSR ht hkt hnb hft he hk' hkd hrb badge g
          gr hback hTO blk) cv
    · obtain ⟨xt0, hkt0, hTRt⟩ := hR.tcb t ht
      rw [hkt] at hkt0; cases hkt0
      have htd : t ≠ d := by
        rintro rfl
        exact hnb.1 (hTRt.st.symm.trans (hQO t (by simp)).1)
      have hXs := IpcSchedHyps.stepsG (A := A) hH hBf hBm hP
      have hSB := IpcRel.toSRN hR hSR
      have hXf := fun s1 σ1 => xferX_top (st := st) (xt := xd) hH hBf hBm hP ht hd htd
        (fun b h => by rw [hft] at h; cases h) a e g s1 σ1 badge
      have cvN : ∀ r : S × A, (r.2 = a ∧ ¬ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).2 ∧
          ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).1 ∧
          EpStateRel T E R B (L.mem r.1) σ' ∧
          SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) r.1 σ') →
          r.2 = a ∧ ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).1,
            IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 z.2 :=
        fun _ ⟨h1, _, σ', h2, h3, h4⟩ => ⟨h1, ((), σ'), h2, IpcRel.ofSRN h3 h4⟩
      by_cases hgg : g = true ∨ gr = true
      · by_cases hrp : ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none
        · exact WP.spec_mono (send_ipc_callX_gen hXs.toEpSteps (hTl.tail hP) hP.e s a σ hR.toE hSB ht hkt hnb hns he
            hk' hkd badge g gr hXf hback hgg hrp hTO blk) cvN
        · refine WP.spec_mono (send_ipc_call_inactiveX_gen hXs.toEpSteps (hTl.tail hP) hP.e s a σ hR.toE hSB ht hkt
            hnb hns he hk' hkd badge g gr hXf hback (Or.inr ?_) hTO blk) cvN
          intro e' rep dd hs
          by_contra hn
          refine hrp fun e'' rep' dd' hs' => ?_
          rw [hs] at hs'; cases hs'; exact hn
      · refine WP.spec_mono (send_ipc_call_inactiveX_gen hXs.toEpSteps (hTl.tail hP) hP.e s a σ hR.toE hSB ht hkt hnb
          hns he hk' hkd badge g gr hXf hback (Or.inl ?_) hTO blk) cvN
        cases g <;> cases gr <;> simp_all

/-- **What `receive_ipc_top` does not cover**: a waiting sender with a
timeout fault and an SC (its fault message reads the SC), or a calling or
faulted sender with an SC, a grant right and a reply (the donation). -/
def RecvRest (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (Rel : S → Fl4Spec.State Unit → Prop)
    (T : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (t : U64) (xt : Fl4Spec.Tcb) (cap : capability.Cap)
    (ac : Fl4Spec.Cap) (blk : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap) (rv e : U64) : Prop :=
  ∀ (sd : U64) q xs, σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))) → sd ∈ T →
    σ.kheap sd.bv = some (.tcb xs) →
    ((∃ b, xs.tcbFault = some (.timeout b) ∧ xs.tcbSchedContext ≠ none) ∨
      ∃ e' dd, xs.tcbState = .blockedOnSend e' dd ∧ (dd.senderIsCall = true ∨ xs.tcbFault ≠ none) ∧
        (dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) ∧ rv ≠ 0#u64 ∧ xs.tcbSchedContext ≠ none) →
    endpoint.receive_ipc st ar s a t cap blk rc ⦃ r => r.2 = a ∧
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv ac blk rc' σ).1, Rel r.1 z.2 ⦄

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` on `IpcRel ∧ SRT … SRE`**, by the endpoint's state, for
a thread without a bound notification and a reply cap as in `ReplyArg`. -/
theorem receive_ipc_top (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    (hbn : xt.tcbBoundNotification = none)
    {e : U64} (he : e ∈ E)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool)
    (hTO : SVK.TailOK σ) (hU : RecvRest st ar (fun s σ => IpcRel N T E R B (L.mem s) σ ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ)
      T s a σ t xt (.Endpoint e cb c1 c2 c3 c4) (.endpointCap e.bv b rights) blk rc rc' rv e) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 z.2 ⦄ := by
  obtain ⟨x, hk, hx⟩ := hR.ep e he
  have blockCase : CanBlock true x → endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r =>
      r.2 = a ∧ ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 z.2 ⦄ := by
    intro hc
    cases blk
    · exact WP.spec_mono (receive_ipc_pollI hH hP s a σ hR hSR ht hkt hbn he hk hc cb c1 c2 c3 c4 hrc b rights)
        fun _ ⟨h1, σ', h2, h3, h4⟩ => ⟨h1, ((), σ'), by rw [h2]; rfl, h3, h4⟩
    · exact WP.spec_mono (receive_ipc_blockI hH hP s a σ hR hSR ht hkt hnb hbn hnn he hk hc hsort cb c1 c2 c3 c4 hrc
        b rights) fun _ ⟨h1, σ', h2, h3, h4⟩ => ⟨h1, ((), σ'), by rw [h2]; rfl, h3, h4⟩
  cases x with
  | idleEP => exact blockCase trivial
  | recvEP q => exact blockCase rfl
  | sendEP q =>
    obtain ⟨-, xs, hne, hq, hQ, hQO⟩ := hx
    obtain ⟨sd, ys, rfl⟩ : ∃ d ys, xs = d :: ys := by
      cases xs with
      | nil => exact absurd rfl hne
      | cons d ys => exact ⟨d, ys, rfl⟩
    have hsd : sd ∈ T := hQ.mem sd (by simp)
    obtain ⟨xsd, hks, hTRs⟩ := hR.tcb sd hsd
    obtain ⟨xt0, hkt0, hTRt⟩ := hR.tcb t ht
    rw [hkt] at hkt0; cases hkt0
    have hsdt : sd ≠ t := by
      rintro rfl
      exact hnb.2 (hTRt.st.symm.trans (hQO sd (by simp)).1)
    have hk' : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: ys.map UScalar.bv))) := by rw [hk, hq]; rfl
    have cv : ∀ r : S × A, (r.2 = a ∧ ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc'
        σ).2 ∧ ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 σ') →
        r.2 = a ∧ ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
          IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 z.2 :=
      fun _ ⟨h1, _, σ', h2, h3, h4⟩ => ⟨h1, ((), σ'), h2, h3, h4⟩
    have cvN : ∀ r : S × A, (r.2 = a ∧ ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc'
        σ).2 ∧ ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧
        SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) r.1 σ') →
        r.2 = a ∧ ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
          IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 z.2 :=
      fun _ ⟨h1, _, σ', h2, h3, h4⟩ => ⟨h1, ((), σ'), h2, IpcRel.ofSRN h3 h4⟩
    -- a timeout fault with an SC: named
    by_cases hto : ∀ b', xsd.tcbFault = some (.timeout b') → xsd.tcbSchedContext = none
    swap
    · push_neg at hto
      obtain ⟨b', h1, h2⟩ := hto
      exact hU sd _ xsd hk' hsd hks (Or.inl ⟨b', h1, h2⟩)
    have hXf := fun e' (dd : Fl4Spec.SenderPayload) (_ : xsd.tcbState = .blockedOnSend e' dd) => xferX_top (st := st) (xt := xt) hH hBf hBm hP hsd ht hsdt hto a e dd.senderCanGrant
    have hX := IpcSchedHyps.stepsG (A := A) hH hBf hBm hP
    have hSB := IpcRel.toSRN hR hSR
    have nonCall : xsd.tcbFault = none → (∀ e' dd, xsd.tcbState = .blockedOnSend e' dd → dd.senderIsCall = false) →
        endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
          ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
            IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 z.2 ⦄ := by
      intro hfs hcall
      cases hrb : ipcBufOf true xt with
      | none =>
        exact WP.spec_mono (receive_ipc_sendG hH hBf hBm hTl hP s a σ hR hSR ht hkt hnb hbn hrb he hk' hks hfs hcall
          cb c1 c2 c3 c4 hrc b rights hTO blk) cv
      | some rp =>
        exact WP.spec_mono (receive_ipc_send_bufG hH hBf hBm hTl hP s a σ hR hSR ht hkt hnb hbn hrb he hk' hks hfs
          hcall cb c1 c2 c3 c4 hrc b rights hTO blk) cv
    cases hs : xsd.tcbState with
    | blockedOnSend e' dd =>
      have uniq : ∀ e'' dd', xsd.tcbState = .blockedOnSend e'' dd' → dd' = dd := fun e'' dd' h => by
        rw [hs] at h; cases h; rfl
      by_cases hcf : dd.senderIsCall = true ∨ xsd.tcbFault ≠ none
      swap
      · push_neg at hcf
        exact nonCall (by simpa using hcf.2) fun e'' dd' h => by
          rw [uniq e'' dd' h]; simpa using hcf.1
      have hcf' : ∀ e'' dd', xsd.tcbState = .blockedOnSend e'' dd' → dd'.senderIsCall = true ∨ xsd.tcbFault ≠ none :=
        fun e'' dd' h => by rw [uniq e'' dd' h]; exact hcf
      have inact : ((dd.senderCanGrant = false ∧ dd.senderCanGrantReply = false) ∨ rv = 0#u64) →
          endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
            ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
              IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 z.2 ⦄ := by
        intro hno
        refine WP.spec_mono (receive_ipc_cfInactive_gen hX.toEpSteps (hTl.tail hP) hP.e s a σ hR.toE hSB ht hkt hnb
          hbn he hk' hks hXf hcf' cb c1 c2 c3 c4 hrc ?_ b rights blk) cvN
        rcases hno with h | h
        · exact Or.inl fun e'' dd' h' => by rw [uniq e'' dd' h']; exact h
        · exact Or.inr h
      by_cases hgg : dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true
      · by_cases hrv : rv = 0#u64
        · exact inact (Or.inr hrv)
        rcases hrc with ⟨-, -, h0⟩ | ⟨b', r', rfl, rfl, hrvR, hrv0⟩
        · exact absurd h0 hrv
        by_cases hscn : xsd.tcbSchedContext = none
        · exact WP.spec_mono (receive_ipc_cfPush_gen hX.toEpSteps (hTl.tail hP) hTl.sc hP.e s a σ hR.toE hSB ht hkt
            hnb hbn he hk' hks hXf hcf' (fun e'' dd' h => by rw [uniq e'' dd' h]; exact hgg) hscn cb c1 c2 c3 c4 b' r'
            hrvR hrv0 b rights blk) cvN
        · exact hU sd _ xsd hk' hsd hks (Or.inr ⟨e', dd, hs, hcf, hgg, hrv, hscn⟩)
      · exact inact (Or.inl ⟨Bool.eq_false_iff.2 fun h => hgg (Or.inl h), Bool.eq_false_iff.2 fun h => hgg (Or.inr h)⟩)
    | _ =>
      exact absurd ((hQO sd (by simp)).1) (by rw [hTRs.st, hs]; simp [tsCode])



/-- `IpcRel ∧ SRT … SRE`. -/
def IRel (st : machine.Store S) [L : LawfulStore st] (th : TypedHeap) (cr : Fl4Spec.Cr3) (N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64)
    (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  IpcRel N T E R B (L.mem s) σ ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ

set_option maxHeartbeats 4000000 in
/-- **The send tail of an endpoint invocation** (`hsend` of
`decode_endpointDMX`): `set_thread_state Restart` then `send_ipc`, on `IRel`.
At related states: `SchedValid` (`hSV`), endpoint queues sorted by priority
(`hsort`), and what `send_ipc_top` does not cover (`hU`). -/
theorem send_tail_top (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (hSV : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → Sched.SchedValid σ')
    (hsort : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → QSorted st T E s')
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    {ct : U64} (hct : ct ∈ T) (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hft : xt.tcbFault = none)
    {σ1 : Fl4Spec.State Unit} (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    {p : U64} (hp : p ∈ E) (b : U64) (blk call g gr don : Bool) (hTO : SVK.TailOK σ)
    (hU : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → SendRest st ar (IRel st th cr N T C E R B c) T s' a σ' blk call b g gr don
      ct p) :
    (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← endpoint.send_ipc st ar s1 a blk call b g gr don ct p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => r.1 = .Ok () ∧
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call b.bv g gr don σ1.curThread p.bv σ1).1,
        RelTopM (L := L) r.2.1 z.2 ∧ IRel st th cr N T C E R B c r.2.1 z.2 ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  have hSB := IpcRel.toSRN hIR hSRT
  have hsteps := IpcSchedHyps.stepsG (A := A) hH hBf hBm hP
  obtain ⟨xt0, hk0, hTR⟩ := hIR.tcb ct hct
  rw [hkt] at hk0; cases hk0
  have hq := IpcRel.not_ep_queued hIR (t := ct) (by rw [hTR.st]; omega)
  have hcode : sched.TS_RESTART.val = tsCode .restart := by unfold sched.TS_RESTART; rfl
  refine WP.spec_bind (hsteps.sts hP.e s σ hIR.toE hSB hct hkt hq (show tsCode xt.tcbState ≠ 6 by omega) .restart
    (by decide) sched.TS_RESTART hcode) ?_
  rintro s1 ⟨hE1, hS1⟩
  rw [hcur, Notif.setThreadState_eq .restart hkt] at hst
  have hσ1 : σ1 = stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv := by
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and, iff_true] at this
    simpa using this.symm
  subst hσ1
  obtain ⟨hIR1, hSRT1⟩ := IpcRel.ofSRN hE1 hS1
  have hX1 : IRel st th cr N T C E R B c s1 _ := ⟨hIR1, hSRT1⟩
  have hkt1 : (stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv).kheap ct.bv =
      some (.tcb { xt with tcbState := .restart }) := by rw [stsAct_kheap]; simp
  have hc1 : (stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv).curThread = ct.bv := by
    unfold stsAct; split_ifs <;> exact hcur
  refine WP.spec_bind (send_ipc_top hH hBf hBm hTl hP s1 a _ hIR1 hSRT1 (hSV _ _ hX1) (tailOK_sts hTO hkt rfl) hct hkt1
    (by simp [tsCode]) (fun m h => by cases h) (by simp [tsCode]) hft hp (hsort _ _ hX1 p hp) blk call b g gr don
    (hU _ _ hX1)) ?_
  rintro ⟨s2, a1⟩ ⟨-, z, hz, hIR2, hSRT2⟩
  apply (WP.spec_ok _).2
  exact ⟨rfl, z, by rw [hc1]; exact hz, (SRT.relTop ⟨hIR2, hSRT2⟩).1, hIR2, hSRT2⟩



set_option maxHeartbeats 4000000 in
/-- **`send_signal` on `IRel`**, by the notification's state; named: no
thread is `RunningVM` (`hvm`, FL4 has no VT-x). -/
theorem send_signal_top (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    {n : U64} (hn : n ∈ N) (hvm : NativeScope σ) (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ).1, IRel st th cr N T C E R B c r.1 z.2 ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  obtain ⟨x, hk, hx⟩ := hIR.ntfn n hn
  have single : ∀ r : S × A, (r.2 = a ∧ SingleRelI (st := st) N T E R B s σ (Fl4Spec.sendSignal n.bv badge.bv σ) r.1) →
      ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ).1, IRel st th cr N T C E R B c r.1 z.2 :=
    fun _ ⟨_, σ', heq, hR', hS, hW, hNB⟩ => ⟨((), σ'), by rw [heq]; rfl, hR', hH.stableN _ _ _ _ hSRT hW hS hNB⟩
  have full : ∀ r : S × A, (¬ (Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ).2 ∧ ∃ σ', ((), σ') ∈
      (Fl4Spec.sendSignal n.bv badge.bv σ).1 ∧ IpcRel N T E R B (L.mem r.1) σ' ∧
      SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 σ') →
      ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ).1, IRel st th cr N T C E R B c r.1 z.2 :=
    fun _ ⟨_, σ', h1, h2, h3⟩ => ⟨((), σ'), h1, h2, h3⟩
  cases ho : x.ntfnObj with
  | activeNtfn b0 => exact WP.spec_mono (send_signal_activeI (ar := ar) hP s a σ hIR hn hk ho badge) single
  | waitingNtfn q => exact WP.spec_mono (send_signal_waitingI hH hP s a σ hIR hSRT hn hk ho badge) full
  | idleNtfn =>
    cases hb : x.ntfnBoundTcb with
    | none => exact WP.spec_mono (send_signal_idle_unboundI (ar := ar) hP s a σ hIR hn hk ho hb badge) single
    | some t =>
      obtain ⟨hb0, hbt⟩ := optRef_some (hx.bound ▸ hb)
      obtain ⟨tcb, hkt, -⟩ := hIR.tcb _ (hx.bound_mem hb0)
      rw [hbt] at hkt
      cases hrb : Fl4Spec.receiveBlocked tcb.tcbState
      · exact WP.spec_mono (send_signal_idle_bound_idleI (ar := ar) hP s a σ hIR hn hk ho hb hkt hrb
          (hvm _ _ hkt) badge) single
      · exact WP.spec_mono (send_signal_idle_bound_recvI hH hP s a σ hIR hSRT hn hk ho hb hkt hrb badge) full


set_option maxHeartbeats 4000000 in
/-- **The send tail of a notification invocation** (`hsend` of
`decode_notificationDMX`): `set_thread_state Restart` then `send_signal`. -/
theorem send_tail_ntfn (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (hvm : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → NativeScope σ')
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    {ct : U64} (hct : ct ∈ T) (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3)
    {σ1 : Fl4Spec.State Unit} (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    {p : U64} (hp : p ∈ N) (b : U64) :
    (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← notification.send_signal st ar s1 a p b
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => r.1 = .Ok () ∧
      ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) p.bv b.bv σ1).1,
        RelTopM (L := L) r.2.1 z.2 ∧ IRel st th cr N T C E R B c r.2.1 z.2 ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  have hSB := IpcRel.toSRN hIR hSRT
  have hsteps := IpcSchedHyps.stepsG (A := A) hH hBf hBm hP
  obtain ⟨xt0, hk0, hTR⟩ := hIR.tcb ct hct
  rw [hkt] at hk0; cases hk0
  have hq := IpcRel.not_ep_queued hIR (t := ct) (by rw [hTR.st]; omega)
  have hcode : sched.TS_RESTART.val = tsCode .restart := by unfold sched.TS_RESTART; rfl
  refine WP.spec_bind (hsteps.sts hP.e s σ hIR.toE hSB hct hkt hq (show tsCode xt.tcbState ≠ 6 by omega) .restart
    (by decide) sched.TS_RESTART hcode) ?_
  rintro s1 ⟨hE1, hS1⟩
  rw [hcur, Notif.setThreadState_eq .restart hkt] at hst
  have hσ1 : σ1 = stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv := by
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and, iff_true] at this
    simpa using this.symm
  subst hσ1
  obtain ⟨hIR1, hSRT1⟩ := IpcRel.ofSRN hE1 hS1
  have hX1 : IRel st th cr N T C E R B c s1 _ := ⟨hIR1, hSRT1⟩
  refine WP.spec_bind (send_signal_top hH hP s1 a _ hX1 hp (hvm _ _ hX1) b) ?_
  rintro ⟨s2, a1⟩ ⟨z, hz, hIR2, hSRT2⟩
  apply (WP.spec_ok _).2
  exact ⟨rfl, z, hz, (SRT.relTop ⟨hIR2, hSRT2⟩).1, hIR2, hSRT2⟩


/-- **`notQueued` from P1's queue invariant** (`SchedQueuesInv`'s `runQ` /
`runR`: a thread in a ready or release queue is runnable) through the
scheduler relation (the spec's queues are FL4's, `SchedSpec.rq`/`rel`) and
the TCB states (`EpStateRel`). -/
theorem notQueued_of_blk {s : S} {σ : Fl4Spec.State Unit} (hS : Sched.SchedRel st N T C c s σ)
    (hE : EpStateRel T E R B (L.mem s) σ) {Cs Ω : Set U64} {H : P1.Heap} {Q' : U64 → U64 → List U64}
    {R' : U64 → List U64} (hQ : P1.SchedQueuesInv st T Cs Ω H s Q' R') (hc : c ∈ Cs)
    {t : U64} {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hr : Fl4Spec.runnable x.tcbState = false) :
    NotQueued σ t.bv := by
  obtain ⟨Q, R0, hC, hSp⟩ := hS.lists
  have hTP := hC.tcbs
  -- a queued thread is runnable in FL4, hence in the spec
  have key : ∀ y ∈ T, y.bv = t.bv → P1.Runnable (L.mem s (P1.stA y)) → False := by
    intro y hy hyt hrun
    obtain ⟨xy, hky, hxy⟩ := hE.tcb y hy
    rw [hyt, hk] at hky; cases hky
    have h1 := hxy.st
    rw [← Sched.stA_tStA] at h1
    unfold P1.Runnable at hrun
    rcases hrun with h | h | h <;> rw [h] at h1 <;>
      simp only [sched.TS_RUNNING, sched.TS_RESTART, sched.TS_RUNNING_VM] at h1 <;>
      cases hst : x.tcbState <;> simp_all [tsCode, Fl4Spec.runnable]
  refine ⟨fun d p hm => ?_, fun hm => ?_⟩
  · by_cases hd : d = 0
    · subst hd
      set q : U64 := ⟨BitVec.ofNat 64 p.toNat⟩ with hqdef
      have hqv : q.val = p.toNat := by
        show (BitVec.ofNat 64 p.toNat).toNat = p.toNat
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := p.isLt; omega)
      have hq : q.val < 256 := by rw [hqv]; exact p.isLt
      have hpq : Sched.specPrio q = p := by
        unfold Sched.specPrio; rw [hqv]; simp
      rw [← hpq, hSp.rq q hq] at hm
      obtain ⟨y, hy, hyt⟩ := List.mem_map.1 hm
      have hyT := (hC.ready.1.rel q hq).mem y hy
      have hQe : Q q = Q' c q := QueueRel.unique hTP (hC.ready.1.rel q hq) ((hQ.ready c hc).1.rel q hq)
      rw [hQe] at hy
      exact key y hyT hyt (hQ.runQ c hc q hq y hy)
    · rw [hSp.rqDom d p hd] at hm; cases hm
  · rw [hSp.rel] at hm
    obtain ⟨y, hy, hyt⟩ := List.mem_map.1 hm
    have hyT := hC.release.mem y hy
    have hRe : R0 = R' c := QueueRel.unique hTP hC.release (hQ.release c hc)
    rw [hRe] at hy
    exact key y hyT hyt (hQ.runR c hc y hy)


/-- **`IpcSchedHyps` for `SRT … SRE` with `notQueued` proved** from P1's
queue invariant at related states (`hBlk`, P1's `BlkOK`), by
`notQueued_of_blk`. -/
theorem ipcSchedHyps_blk (hP0 : IPlaced N T E R B)
    (hBlk : ∀ s σ, SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ →
      ∃ (Cs Ω : Set U64) (H : P1.Heap) (Q : U64 → U64 → List U64) (R' : U64 → List U64),
        P1.SchedQueuesInv st T Cs Ω H s Q R' ∧ c ∈ Cs)
    (hW : IpcWakeHyps st ar th cr N T C E R B c)
    (hX : ∀ s σ (t : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ →
      SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ → t ∈ T → σ.kheap t.bv = some (.tcb x) →
      Fl4Spec.receiveBlocked x.tcbState = true → CancelRecvHyp E (L.mem s) σ t x) :
    IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)) :=
  ipcSchedHyps_full hP0 (fun s σ _ _ hR hS hk hr =>
    let ⟨_, _, _, _, _, hQ, hc⟩ := hBlk s σ hS
    notQueued_of_blk hS.2.1 hR.toE hQ hc hk hr) hW hX



end

end

end Fl4Proofs.P3.Endp

namespace Fl4Proofs.P3
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : P1.LawfulStore st] {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- An endpoint of the spec's heap is one of the relation's (`ObjCover`). -/
theorem memE_of_cover {σ : Fl4Spec.State Unit} (hO : Sched.ObjCover N T E R C σ) {p : U64}
    (hp : ∃ x, σ.kheap p.bv = some (.endpoint x)) : p ∈ E := by
  obtain ⟨x, hk⟩ := hp
  obtain ⟨e, he, h⟩ := hO.ep _ x hk
  rw [Sched.bv_inj h] at he; exact he

/-- **An endpoint cap for `handle_invocation_refinesMX`**, with `X := IRel`:
`decode_endpointDMX` with the send tail `send_tail_top`. -/
theorem decode_endpoint_top (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (hSV : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → Sched.SchedValid σ')
    (hsort : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → QSorted st T E s')
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    (lbl length slot : U64) (p b : U64) (sd rv g gr : Bool) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcT : ct ∈ T) (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hft : xt.tcbFault = none) (hp : p ∈ E) (hTO : SVK.TailOK σ)
    (hU : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → SendRest st ar (IRel st th cr N T C E R B c) T s' a σ' blk call b g gr don
      ct p) :
    DecOKDMX (L := L) ar (fun s _ σ => IRel st th cr N T C E R B c s σ) s a σ lbl length slot (.Endpoint p b sd rv g gr)
      blk call don fp buf extra slbl args ci sl excaps buffer := by
  obtain ⟨σ1, hst⟩ : ∃ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) := by
    rw [hcur, Notif.setThreadState_eq .restart hkt]; exact ⟨_, rfl⟩
  exact decode_endpointDMX ar _ s a σ lbl length slot p b sd rv g gr blk call don fp buf extra slbl args ci sl excaps
    buffer ct hct hX hst fun _ => send_tail_top hH hBf hBm hTl hP hSV hsort s a σ hX hcT hcur hkt hrun hft hst hp b
      blk call g gr don hTO hU


set_option maxHeartbeats 4000000 in
/-- **The `ipc` leaf of `RecvLeaves`** on `IRel`, from `receive_ipc_top`. The
spec's objects are the relation's (`ObjCover`); named: the current thread
running or restarting without a bound notification, the endpoint queues
sorted, a reply cap whose reply is linked (`take_reply` cancels its thread's
IPC first, `hlink`), and `RecvRest`. -/
theorem recv_ipc_leaf (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    (hO : Sched.ObjCover N T E R C σ)
    {ct : U64} (hcT : ct ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hbn : xt.tcbBoundNotification = none)
    (hsort : QSorted st T E s) (hTO : SVK.TailOK σ)
    (blocking : Bool)
    (hlink : ∀ p b sd g gr q g', q ∈ R → L.mem s (Endp.rTcbA q) ≠ 0#u64 →
      endpoint.receive_ipc st ar s a ct (.Endpoint p b sd true g gr) blocking (.Reply q g') ⦃ r =>
        ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking
          (absCap (.Reply q g')) σ).1, IRel st th cr N T C E R B c r.1 z.2 ⦄)
    (hU : ∀ p b sd g gr rc rc' rv, RecvRest st ar (IRel st th cr N T C E R B c) T s a σ ct xt (.Endpoint p b sd true g gr)
      (absCap (.Endpoint p b sd true g gr)) blocking rc rc' rv p) :
    ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    endpoint.receive_ipc st ar s a ct (.Endpoint p b sd true g gr) blocking rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking rc' σ).1,
        IRel st th cr N T C E R B c r.1 z.2 ⦄ := by
  intro p b sd g gr rc rc' hpE hrc
  have hp : p ∈ E := memE_of_cover hO hpE
  obtain ⟨hIR, hSRT⟩ := hX
  have hnn : ∀ n, xt.tcbState ≠ .blockedOnNotification n := fun n h => by
    rw [h] at hrun; simp [tsCode] at hrun
  have run : ∀ {rv : U64}, ReplyArg R (L.mem s) rc rc' rv →
      endpoint.receive_ipc st ar s a ct (.Endpoint p b sd true g gr) blocking rc ⦃ r =>
        ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking rc' σ).1,
          IRel st th cr N T C E R B c r.1 z.2 ⦄ := fun {rv} hra =>
    WP.spec_mono (receive_ipc_top hH hBf hBm hTl hP s a σ hIR hSRT hcT hkt ⟨by omega, by omega⟩ hnn hbn hp (hsort p hp) b sd true g gr hra b.bv (rightsOf sd true g gr) blocking
      hTO (hU p b sd g gr rc rc' rv)) fun _ ⟨_, z, hz, h1, h2⟩ => ⟨z, hz, h1, h2⟩
  rcases hrc with ⟨rfl, rfl⟩ | ⟨hcr, q, g', rfl, hq⟩
  · exact run (Or.inl ⟨rfl, rfl, rfl⟩)
  · have hqR : q ∈ R := by
      obtain ⟨x, hk⟩ := hq
      obtain ⟨r, hr, h⟩ := hO.reply _ x hk
      rw [Sched.bv_inj h] at hr; exact hr
    have hrc' : rc' = absCap (.Reply q g') := hcr.abs
    subst hrc'
    by_cases h0 : L.mem s (Endp.rTcbA q) = 0#u64
    · exact run (Or.inr ⟨g', _, rfl, rfl, hqR, h0⟩)
    · exact hlink p b sd g gr q g' hqR h0


/-- **The `bound` leaf of `RecvLeaves`**: the bound TCB of a notification of
the spec's heap, from `IpcRel` (`ObjCover`). -/
theorem recv_bound_leaf {s : S} {σ : Fl4Spec.State Unit} (hIR : IpcRel N T E R B (L.mem s) σ)
    (hO : Sched.ObjCover N T E R C σ) :
    ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
      Fl4Spec.getNtfnObjRef (Z := Unit) Fl4Spec.Notification.ntfnBoundTcb p.bv σ =
        ({(Notif.optRef (L.mem s (Notif.nBoundA p)), σ)}, False) := by
  rintro p - - - - - ⟨x, hk⟩
  obtain ⟨n, hn, h⟩ := hO.ntfn _ x hk
  rw [Sched.bv_inj h] at hn
  obtain ⟨x', hk', hr⟩ := hIR.ntfn p hn
  rw [hk] at hk'; cases hk'
  rw [← hr.bound]
  show Fl4Spec.getSkObjRef Fl4Spec.KernelObject.notification Fl4Spec.Notification.ntfnBoundTcb p.bv σ = _
  unfold Fl4Spec.getSkObjRef
  rw [nd_bind_one (getNotification_eq hk)]; rfl

set_option maxHeartbeats 4000000 in
/-- **The `sig` leaf of `RecvLeaves`** on `IRel`, by the notification's
state (`receive_signal_activeI`, `_blockI`, `_pollI`); named: `IpcRecvHyps`,
the current thread's scheduling facts (not queued, released if bound, not
the switch target, not idle), `ActReady` and the notification queues sorted. -/
theorem recv_sig_leaf (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hRV : IpcRecvHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    (hO : Sched.ObjCover N T E R C σ)
    {ct : U64} (hcT : ct ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrr : xt.tcbState = .running ∨ xt.tcbState = .restart)
    (hsortN : QSorted st T N s)
    (hAR : ActReady σ) (hNQ : NotQueued σ ct.bv) (hRB : RelIfBound σ ct.bv)
    (hsane : ∀ u, σ.schedulerAction = .switchThread u → u ≠ ct.bv) (hnidle : ct.bv ≠ σ.idleThread)
    (blocking : Bool) :
    ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
      notification.receive_signal st ar s a ct p blocking ⦃ r =>
        ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac blocking σ).1, IRel st th cr N T C E R B c r.1 z.2 ⦄ := by
  rintro p b w rd ac hcr ⟨x, hk⟩
  have hac : ac = absCap (.Notification p b w rd) := hcr.abs
  subst hac
  obtain ⟨n, hn, h⟩ := hO.ntfn _ x hk
  rw [Sched.bv_inj h] at hn
  obtain ⟨hIR, hSRT⟩ := hX
  obtain ⟨xt0, hk0, hTR⟩ := hIR.tcb ct hcT
  rw [hkt] at hk0; cases hk0
  have hRun : ∀ y, σ.kheap ct.bv = some (.tcb y) → Fl4Spec.runnable y.tcbState = true := fun y hy => by
    rw [hkt] at hy; cases hy; rcases hrr with h | h <;> rw [h] <;> rfl
  cases hact : x.ntfnObj with
  | activeNtfn b0 =>
    exact WP.spec_mono (receive_signal_activeI hH hRV hP s a σ hIR hSRT hcT hn hk hact blocking b.bv
      (rightsOf w rd false false) hNQ hRun) fun _ ⟨_, σ', h1, h2, h3⟩ => ⟨((), σ'), h1, h2, h3⟩
  | _ =>
    have hna : ∀ b', x.ntfnObj ≠ .activeNtfn b' := fun b' h => by rw [hact] at h; cases h
    cases blocking
    · refine WP.spec_mono (receive_signal_pollI (ar := ar) hP s a σ hIR hcT hn hk hna b.bv
        (rightsOf w rd false false)) ?_
      rintro r ⟨-, σ', heq, hR', hS, hW, hNB⟩
      refine ⟨((), σ'), ?_, hR', hH.stableN _ _ _ _ hSRT hW hS hNB⟩
      show _ ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv (.notificationCap p.bv b.bv (rightsOf w rd false false))
        false σ).1
      rw [heq]; rfl
    · have hnb : ∀ m, xt.tcbState ≠ .blockedOnNotification m := fun m h => by
        rcases hrr with h' | h' <;> rw [h'] at h <;> cases h
      have hqE := IpcRel.not_ep_queued hIR (t := ct) (by rw [hTR.st]; rcases hrr with h | h <;> rw [h] <;> decide)
      exact WP.spec_mono (receive_signal_blockI hH hRV hP s a σ hIR hSRT hcT hkt hnb hqE hn hk hna (hsortN p hn)
        b.bv (rightsOf w rd false false) hAR hNQ hRB hsane hnidle) fun _ ⟨_, σ', h1, h2, h3⟩ => ⟨((), σ'), h1, h2, h3⟩


/-- **`RecvLeaves` on `IRel`**: the `ipc`, `sig` and `bound` leaves from the
IPC theorems (`recv_ipc_leaf`, `recv_sig_leaf`, `recv_bound_leaf`); the cap
fault (`handle_fault`, `hflt`) named, with the named facts of the leaves. -/
theorem recvLeaves_of (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hRV : IpcRecvHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    (hO : Sched.ObjCover N T E R C σ)
    {ct : U64} (hcT : ct ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrr : xt.tcbState = .running ∨ xt.tcbState = .restart) (hbn : xt.tcbBoundNotification = none)
    (hsort : QSorted st T E s) (hsortN : QSorted st T N s)
    (hAR : ActReady σ) (hNQ : NotQueued σ ct.bv) (hRB : RelIfBound σ ct.bv)
    (hsane : ∀ u, σ.schedulerAction = .switchThread u → u ≠ ct.bv) (hnidle : ct.bv ≠ σ.idleThread)
    (hTO : SVK.TailOK σ) (blocking : Bool)
    (hlink : ∀ p b sd g gr q g', q ∈ R → L.mem s (Endp.rTcbA q) ≠ 0#u64 →
      endpoint.receive_ipc st ar s a ct (.Endpoint p b sd true g gr) blocking (.Reply q g') ⦃ r =>
        ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking
          (absCap (.Reply q g')) σ).1, IRel st th cr N T C E R B c r.1 z.2 ⦄)
    (hU : ∀ p b sd g gr rc rc' rv, RecvRest st ar (IRel st th cr N T C E R B c) T s a σ ct xt (.Endpoint p b sd true g gr)
      (absCap (.Endpoint p b sd true g gr)) blocking rc rc' rv p)
    (hflt : ∀ cptr lf lf', LookupFaultRel lf lf' →
      faults.handle_fault st ar s a ct (.Cap cptr true lf) ⦃ r =>
        ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
          IRel st th cr N T C E R B c r.1 z.2 ⦄) :
    RecvLeaves (st := st) (ar := ar) (fun s _ σ => IRel st th cr N T C E R B c s σ) ct blocking s a σ where
  ipc := recv_ipc_leaf hH hBf hBm hTl hP s a σ hX hO hcT hkt (by rcases hrr with h | h <;> rw [h] <;> decide) hbn
    hsort hTO blocking hlink hU
  sig := recv_sig_leaf hH hRV hP s a σ hX hO hcT hkt hrr hsortN hAR hNQ hRB hsane hnidle blocking
  bound := recv_bound_leaf hX.1 hO
  flt := hflt


/-- A notification of the spec's heap is one of the relation's. -/
theorem memN_of_cover {σ : Fl4Spec.State Unit} (hO : Sched.ObjCover N T E R C σ) {p : U64}
    (hp : ∃ x, σ.kheap p.bv = some (.notification x)) : p ∈ N := by
  obtain ⟨x, hk⟩ := hp
  obtain ⟨n, hn, h⟩ := hO.ntfn _ x hk
  rw [Sched.bv_inj h] at hn; exact hn

/-- **A notification cap for `handle_invocation_refinesMX`**, with
`X := IRel`: `decode_notificationDMX` with `send_tail_ntfn`. -/
theorem decode_notification_top (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (hvm : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → NativeScope σ')
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    (lbl length slot : U64) (p b : U64) (sd rv : Bool) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcT : ct ∈ T) (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hp : p ∈ N) :
    DecOKDMX (L := L) ar (fun s _ σ => IRel st th cr N T C E R B c s σ) s a σ lbl length slot (.Notification p b sd rv)
      blk call don fp buf extra slbl args ci sl excaps buffer := by
  obtain ⟨σ1, hst⟩ : ∃ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) := by
    rw [hcur, Notif.setThreadState_eq .restart hkt]; exact ⟨_, rfl⟩
  exact decode_notificationDMX ar _ s a σ lbl length slot p b sd rv blk call don fp buf extra slbl args ci sl
    excaps buffer ct hct hX hst fun _ => send_tail_ntfn hH hBf hBm hP hvm s a σ hX hcT hcur hkt hrun hst hp b

end

end

end Fl4Proofs.P3
