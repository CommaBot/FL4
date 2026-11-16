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
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T C E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- The receiver's reply back-pointer, from `SchedValid`. -/
theorem hback_of {σ : Fl4Spec.State Unit} (hV : Sched.SchedValid σ) {d : Fl4Spec.ObjRef} {xd : Fl4Spec.Tcb}
    (hkd : σ.kheap d = some (.tcb xd)) :
    ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d := by
  intro e' r dd xr hs hkr
  obtain ⟨xr', hkr', h⟩ := hV.recvReply d xd e' r dd hkd hs
  rw [hkr] at hkr'; cases hkr'; exact h

/-- **What `send_ipc_top` does not cover**: a send to a waiting receiver that
donates, or a call to a receiver with an IPC buffer. -/
def SendRest (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (Rel : S → Fl4Spec.State Unit → Prop)
    (T : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (blk call : Bool) (badge : U64) (g gr don : Bool)
    (t e : U64) : Prop :=
  ∀ (d : U64) q xd, σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))) → d ∈ T →
    σ.kheap d.bv = some (.tcb xd) → (don = true ∨ (call = true ∧ ipcBufOf true xd ≠ none)) →
    endpoint.send_ipc st ar s a blk call badge g gr don t e ⦃ r => r.2 = a ∧
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call badge.bv g gr don t.bv e.bv σ).1, Rel r.1 z.2 ⦄

set_option maxHeartbeats 4000000 in
/-- **`send_ipc` on `IpcRel ∧ SRT … SRE`**, by the endpoint's state. -/
theorem send_ipc_top (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SRT st N T C E R B c (SRE st N T C E R B c) s σ)
    (hV : Sched.SchedValid σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    (hns : tsCode xt.tcbState ≠ 6) (hft : xt.tcbFault = none)
    {e : U64} (he : e ∈ E)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (blk call : Bool) (badge : U64) (g gr don : Bool)
    (hU : SendRest st ar (fun s σ => IpcRel N T E R B (L.mem s) σ ∧ SRT st N T C E R B c (SRE st N T C E R B c) s σ)
      T s a σ blk call badge g gr don t e) :
    endpoint.send_ipc st ar s a blk call badge g gr don t e ⦃ r => r.2 = a ∧
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call badge.bv g gr don t.bv e.bv σ).1,
        IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st N T C E R B c (SRE st N T C E R B c) r.1 z.2 ⦄ := by
  obtain ⟨x, hk, hx⟩ := hR.ep e he
  have blockCase : CanBlock false x → endpoint.send_ipc st ar s a blk call badge g gr don t e ⦃ r => r.2 = a ∧
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call badge.bv g gr don t.bv e.bv σ).1,
        IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st N T C E R B c (SRE st N T C E R B c) r.1 z.2 ⦄ := by
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
    obtain ⟨-, xs, hne, hq, hQ, -⟩ := hx
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
        IpcRel N T E R B (L.mem r.1) σ' ∧ SRT st N T C E R B c (SRE st N T C E R B c) r.1 σ') →
        r.2 = a ∧ ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call badge.bv g gr don t.bv e.bv σ).1,
          IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st N T C E R B c (SRE st N T C E R B c) r.1 z.2 :=
      fun _ ⟨h1, _, σ', h2, h3, h4⟩ => ⟨h1, ((), σ'), h2, h3, h4⟩
    cases don
    swap
    · exact hU d _ xd hk' hd hkd (Or.inl rfl)
    cases call
    · cases hrb : ipcBufOf true xd with
      | none =>
        exact WP.spec_mono (send_ipc_recvG hH hBf hBm hTl hP s a σ hR hSR ht hkt hnb hft he hk' hkd hrb badge g gr
          hback blk) cv
      | some rp =>
        exact WP.spec_mono (send_ipc_recv_bufG hH hBf hBm hTl hP s a σ hR hSR ht hkt hnb hft he hk' hkd hrb badge g
          gr hback blk) cv
    · by_cases hrb : ipcBufOf true xd = none
      swap
      · exact hU d _ xd hk' hd hkd (Or.inr ⟨rfl, hrb⟩)
      by_cases hgg : g = true ∨ gr = true
      · by_cases hrp : ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none
        · exact WP.spec_mono (send_ipc_callG hH hBf hBm hTl hP s a σ hR hSR ht hkt hnb hft hns he hk' hkd hrb badge
            g gr hback hgg hrp blk) cv
        · refine WP.spec_mono (send_ipc_call_inactiveG hH hBf hBm hTl hP s a σ hR hSR ht hkt hnb hft hns he hk' hkd
            hrb badge g gr hback (Or.inr ?_) blk) cv
          intro e' rep dd hs
          by_contra hn
          refine hrp fun e'' rep' dd' hs' => ?_
          rw [hs] at hs'; cases hs'; exact hn
      · refine WP.spec_mono (send_ipc_call_inactiveG hH hBf hBm hTl hP s a σ hR hSR ht hkt hnb hft hns he hk' hkd
          hrb badge g gr hback (Or.inl ?_) blk) cv
        cases g <;> cases gr <;> simp_all

/-- **What `receive_ipc_top` does not cover**: a waiting sender with a fault
(`do_fault_transfer`), or a calling sender with the receiver's IPC buffer,
or a granting caller with an SC and a reply (the donation). -/
def RecvRest (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (Rel : S → Fl4Spec.State Unit → Prop)
    (T : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (t : U64) (xt : Fl4Spec.Tcb) (cap : capability.Cap)
    (ac : Fl4Spec.Cap) (blk : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap) (rv e : U64) : Prop :=
  ∀ (sd : U64) q xs, σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))) → sd ∈ T →
    σ.kheap sd.bv = some (.tcb xs) →
    (xs.tcbFault ≠ none ∨ ∃ e' dd, xs.tcbState = .blockedOnSend e' dd ∧ dd.senderIsCall = true ∧
      (ipcBufOf true xt ≠ none ∨ ((dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) ∧ rv ≠ 0#u64 ∧
        xs.tcbSchedContext ≠ none))) →
    endpoint.receive_ipc st ar s a t cap blk rc ⦃ r => r.2 = a ∧
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv ac blk rc' σ).1, Rel r.1 z.2 ⦄

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` on `IpcRel ∧ SRT … SRE`**, by the endpoint's state, for
a thread without a bound notification and a reply cap as in `ReplyArg`. -/
theorem receive_ipc_top (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SRT st N T C E R B c (SRE st N T C E R B c) s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    (hbn : xt.tcbBoundNotification = none)
    {e : U64} (he : e ∈ E)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool)
    (hU : RecvRest st ar (fun s σ => IpcRel N T E R B (L.mem s) σ ∧ SRT st N T C E R B c (SRE st N T C E R B c) s σ)
      T s a σ t xt (.Endpoint e cb c1 c2 c3 c4) (.endpointCap e.bv b rights) blk rc rc' rv e) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st N T C E R B c (SRE st N T C E R B c) r.1 z.2 ⦄ := by
  obtain ⟨x, hk, hx⟩ := hR.ep e he
  have blockCase : CanBlock true x → endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r =>
      r.2 = a ∧ ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st N T C E R B c (SRE st N T C E R B c) r.1 z.2 ⦄ := by
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
    obtain ⟨-, xs, hne, hq, hQ, -⟩ := hx
    obtain ⟨sd, ys, rfl⟩ : ∃ d ys, xs = d :: ys := by
      cases xs with
      | nil => exact absurd rfl hne
      | cons d ys => exact ⟨d, ys, rfl⟩
    have hsd : sd ∈ T := hQ.mem sd (by simp)
    obtain ⟨xsd, hks, -⟩ := hR.tcb sd hsd
    have hk' : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: ys.map UScalar.bv))) := by rw [hk, hq]; rfl
    have cv : ∀ r : S × A, (r.2 = a ∧ ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc'
        σ).2 ∧ ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SRT st N T C E R B c (SRE st N T C E R B c) r.1 σ') →
        r.2 = a ∧ ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
          IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st N T C E R B c (SRE st N T C E R B c) r.1 z.2 :=
      fun _ ⟨h1, _, σ', h2, h3, h4⟩ => ⟨h1, ((), σ'), h2, h3, h4⟩
    by_cases hfs : xsd.tcbFault = none
    swap
    · exact hU sd _ xsd hk' hsd hks (Or.inl hfs)
    have nonCall : (∀ e' dd, xsd.tcbState = .blockedOnSend e' dd → dd.senderIsCall = false) →
        endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
          ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
            IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st N T C E R B c (SRE st N T C E R B c) r.1 z.2 ⦄ := by
      intro hcall
      cases hrb : ipcBufOf true xt with
      | none =>
        exact WP.spec_mono (receive_ipc_sendG hH hBf hBm hTl hP s a σ hR hSR ht hkt hnb hbn hrb he hk' hks hfs hcall
          cb c1 c2 c3 c4 hrc b rights blk) cv
      | some rp =>
        exact WP.spec_mono (receive_ipc_send_bufG hH hBf hBm hTl hP s a σ hR hSR ht hkt hnb hbn hrb he hk' hks hfs
          hcall cb c1 c2 c3 c4 hrc b rights blk) cv
    cases hs : xsd.tcbState with
    | blockedOnSend e' dd =>
      have uniq : ∀ e'' dd', xsd.tcbState = .blockedOnSend e'' dd' → dd' = dd := fun e'' dd' h => by
        rw [hs] at h; cases h; rfl
      cases hc : dd.senderIsCall
      · exact nonCall fun e'' dd' h => by rw [uniq e'' dd' h]; exact hc
      have hcall : ∀ e'' dd', xsd.tcbState = .blockedOnSend e'' dd' → dd'.senderIsCall = true :=
        fun e'' dd' h => by rw [uniq e'' dd' h]; exact hc
      by_cases hrb : ipcBufOf true xt = none
      swap
      · exact hU sd _ xsd hk' hsd hks (Or.inr ⟨e', dd, hs, hc, Or.inl hrb⟩)
      have inact : ((dd.senderCanGrant = false ∧ dd.senderCanGrantReply = false) ∨ rv = 0#u64) →
          endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
            ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
              IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st N T C E R B c (SRE st N T C E R B c) r.1 z.2 ⦄ := by
        intro hno
        refine WP.spec_mono (receive_ipc_sendCallInactiveG hH hBf hBm hTl hP s a σ hR hSR ht hkt hnb hbn hrb he hk'
          hks hfs hcall cb c1 c2 c3 c4 hrc ?_ b rights blk) cv
        rcases hno with h | h
        · exact Or.inl fun e'' dd' h' => by rw [uniq e'' dd' h']; exact h
        · exact Or.inr h
      by_cases hgg : dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true
      · by_cases hrv : rv = 0#u64
        · exact inact (Or.inr hrv)
        rcases hrc with ⟨-, -, h0⟩ | ⟨b', r', rfl, rfl, hrvR, hrv0⟩
        · exact absurd h0 hrv
        by_cases hscn : xsd.tcbSchedContext = none
        · exact WP.spec_mono (receive_ipc_sendCallPushG hH hBf hBm hTl hP s a σ hR hSR ht hkt hnb hbn hrb he hk' hks
            hfs hcall (fun e'' dd' h => by rw [uniq e'' dd' h]; exact hgg) hscn cb c1 c2 c3 c4 b' r' hrvR hrv0 b
            rights blk) cv
        · exact hU sd _ xsd hk' hsd hks (Or.inr ⟨e', dd, hs, hc, Or.inr ⟨hgg, hrv, hscn⟩⟩)
      · exact inact (Or.inl ⟨Bool.eq_false_iff.2 fun h => hgg (Or.inl h), Bool.eq_false_iff.2 fun h => hgg (Or.inr h)⟩)
    | _ => exact nonCall fun e'' dd' h => by rw [hs] at h; cases h



/-- `IpcRel ∧ SRT … SRE`. -/
def IRel (st : machine.Store S) [L : LawfulStore st] (N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64)
    (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  IpcRel N T E R B (L.mem s) σ ∧ SRT st N T C E R B c (SRE st N T C E R B c) s σ

set_option maxHeartbeats 4000000 in
/-- **The send tail of an endpoint invocation** (`hsend` of
`decode_endpointDMX`): `set_thread_state Restart` then `send_ipc`, on `IRel`.
At related states: `SchedValid` (`hSV`), endpoint queues sorted by priority
(`hsort`), and what `send_ipc_top` does not cover (`hU`). -/
theorem send_tail_top (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (hSV : ∀ s' σ', IRel st N T C E R B c s' σ' → Sched.SchedValid σ')
    (hsort : ∀ s' σ', IRel st N T C E R B c s' σ' → ∀ e ∈ E, ∀ xs, QueueRel (L.mem s') T .Ep (qOf (L.mem s') e) xs →
      PrioSorted (fun y => L.mem s' (prioA y)) xs)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st N T C E R B c s σ)
    {ct : U64} (hct : ct ∈ T) (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hft : xt.tcbFault = none)
    {σ1 : Fl4Spec.State Unit} (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    {p : U64} (hp : p ∈ E) (b : U64) (blk call g gr don : Bool)
    (hU : ∀ s' σ', IRel st N T C E R B c s' σ' → SendRest st ar (IRel st N T C E R B c) T s' a σ' blk call b g gr don
      ct p) :
    (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← endpoint.send_ipc st ar s1 a blk call b g gr don ct p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => r.1 = .Ok () ∧
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call b.bv g gr don σ1.curThread p.bv σ1).1,
        RelTopM (L := L) r.2.1 z.2 ∧ IRel st N T C E R B c r.2.1 z.2 ⦄ := by
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
  have hX1 : IRel st N T C E R B c s1 _ := ⟨hIR1, hSRT1⟩
  have hkt1 : (stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv).kheap ct.bv =
      some (.tcb { xt with tcbState := .restart }) := by rw [stsAct_kheap]; simp
  have hc1 : (stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv).curThread = ct.bv := by
    unfold stsAct; split_ifs <;> exact hcur
  refine WP.spec_bind (send_ipc_top hH hBf hBm hTl hP s1 a _ hIR1 hSRT1 (hSV _ _ hX1) hct hkt1
    (by simp [tsCode]) (fun m h => by cases h) (by simp [tsCode]) hft hp (hsort _ _ hX1 p hp) blk call b g gr don
    (hU _ _ hX1)) ?_
  rintro ⟨s2, a1⟩ ⟨-, z, hz, hIR2, hSRT2⟩
  apply (WP.spec_ok _).2
  exact ⟨rfl, z, by rw [hc1]; exact hz, (SRT.relTop ⟨hIR2, hSRT2⟩).1, hIR2, hSRT2⟩



set_option maxHeartbeats 4000000 in
/-- **`send_signal` on `IRel`**, by the notification's state; named: no
thread is `RunningVM` (`hvm`, FL4 has no VT-x). -/
theorem send_signal_top (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st N T C E R B c s σ)
    {n : U64} (hn : n ∈ N) (hvm : ∀ p x, σ.kheap p = some (.tcb x) → x.tcbState ≠ .runningVM) (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ).1, IRel st N T C E R B c r.1 z.2 ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  obtain ⟨x, hk, hx⟩ := hIR.ntfn n hn
  have single : ∀ r : S × A, (r.2 = a ∧ SingleRelI (st := st) N T E R B s σ (Fl4Spec.sendSignal n.bv badge.bv σ) r.1) →
      ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ).1, IRel st N T C E R B c r.1 z.2 :=
    fun _ ⟨_, σ', heq, hR', hS, hW, hNB⟩ => ⟨((), σ'), by rw [heq]; rfl, hR', hH.stableN _ _ _ _ hSRT hW hS hNB⟩
  have full : ∀ r : S × A, (¬ (Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ).2 ∧ ∃ σ', ((), σ') ∈
      (Fl4Spec.sendSignal n.bv badge.bv σ).1 ∧ IpcRel N T E R B (L.mem r.1) σ' ∧
      SRT st N T C E R B c (SRE st N T C E R B c) r.1 σ') →
      ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ).1, IRel st N T C E R B c r.1 z.2 :=
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
theorem send_tail_ntfn (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (hvm : ∀ s' σ', IRel st N T C E R B c s' σ' → ∀ p x, σ'.kheap p = some (.tcb x) → x.tcbState ≠ .runningVM)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st N T C E R B c s σ)
    {ct : U64} (hct : ct ∈ T) (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3)
    {σ1 : Fl4Spec.State Unit} (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    {p : U64} (hp : p ∈ N) (b : U64) :
    (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← notification.send_signal st ar s1 a p b
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => r.1 = .Ok () ∧
      ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) p.bv b.bv σ1).1,
        RelTopM (L := L) r.2.1 z.2 ∧ IRel st N T C E R B c r.2.1 z.2 ⦄ := by
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
  have hX1 : IRel st N T C E R B c s1 _ := ⟨hIR1, hSRT1⟩
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
    (hBlk : ∀ s σ, SRT st N T C E R B c (SRE st N T C E R B c) s σ →
      ∃ (Cs Ω : Set U64) (H : P1.Heap) (Q : U64 → U64 → List U64) (R' : U64 → List U64),
        P1.SchedQueuesInv st T Cs Ω H s Q R' ∧ c ∈ Cs)
    (hW : IpcWakeHyps st ar N T C E R B c)
    (hX : ∀ s σ (t : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ →
      SRT st N T C E R B c (SRE st N T C E R B c) s σ → t ∈ T → σ.kheap t.bv = some (.tcb x) →
      Fl4Spec.receiveBlocked x.tcbState = true → CancelRecvHyp E (L.mem s) σ t x) :
    IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)) :=
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
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : P1.LawfulStore st] {N T C E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- An endpoint of the spec's heap is one of the relation's (`ObjCover`). -/
theorem memE_of_cover {σ : Fl4Spec.State Unit} (hO : Sched.ObjCover N T E R C σ) {p : U64}
    (hp : ∃ x, σ.kheap p.bv = some (.endpoint x)) : p ∈ E := by
  obtain ⟨x, hk⟩ := hp
  obtain ⟨e, he, h⟩ := hO.ep _ x hk
  rw [Sched.bv_inj h] at he; exact he

/-- **An endpoint cap for `handle_invocation_refinesMX`**, with `X := IRel`:
`decode_endpointDMX` with the send tail `send_tail_top`. -/
theorem decode_endpoint_top (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (hSV : ∀ s' σ', IRel st N T C E R B c s' σ' → Sched.SchedValid σ')
    (hsort : ∀ s' σ', IRel st N T C E R B c s' σ' → ∀ e ∈ E, ∀ xs, P1.QueueRel (L.mem s') T .Ep (qOf (L.mem s') e) xs →
      PrioSorted (fun y => L.mem s' (prioA y)) xs)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st N T C E R B c s σ)
    (lbl length slot : U64) (p b : U64) (sd rv g gr : Bool) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcT : ct ∈ T) (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hft : xt.tcbFault = none) (hp : p ∈ E)
    (hU : ∀ s' σ', IRel st N T C E R B c s' σ' → SendRest st ar (IRel st N T C E R B c) T s' a σ' blk call b g gr don
      ct p) :
    DecOKDMX (L := L) ar (fun s _ σ => IRel st N T C E R B c s σ) s a σ lbl length slot (.Endpoint p b sd rv g gr)
      blk call don fp buf extra slbl args ci sl excaps buffer := by
  obtain ⟨σ1, hst⟩ : ∃ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) := by
    rw [hcur, Notif.setThreadState_eq .restart hkt]; exact ⟨_, rfl⟩
  exact decode_endpointDMX ar _ s a σ lbl length slot p b sd rv g gr blk call don fp buf extra slbl args ci sl excaps
    buffer ct hct hX hst fun _ => send_tail_top hH hBf hBm hTl hP hSV hsort s a σ hX hcT hcur hkt hrun hft hst hp b
      blk call g gr don hU


set_option maxHeartbeats 4000000 in
/-- **The `ipc` leaf of `RecvLeaves`** on `IRel`, from `receive_ipc_top`. The
spec's objects are the relation's (`ObjCover`); named: the current thread
running or restarting without a bound notification, the endpoint queues
sorted, a reply cap whose reply is linked (`take_reply` cancels its thread's
IPC first, `hlink`), and `RecvRest`. -/
theorem recv_ipc_leaf (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st N T C E R B c s σ)
    (hO : Sched.ObjCover N T E R C σ)
    {ct : U64} (hcT : ct ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hbn : xt.tcbBoundNotification = none)
    (hsort : ∀ e ∈ E, ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (blocking : Bool)
    (hlink : ∀ p b sd g gr q g', q ∈ R → L.mem s (Endp.rTcbA q) ≠ 0#u64 →
      endpoint.receive_ipc st ar s a ct (.Endpoint p b sd true g gr) blocking (.Reply q g') ⦃ r =>
        ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking
          (absCap (.Reply q g')) σ).1, IRel st N T C E R B c r.1 z.2 ⦄)
    (hU : ∀ p b sd g gr rc rc' rv, RecvRest st ar (IRel st N T C E R B c) T s a σ ct xt (.Endpoint p b sd true g gr)
      (absCap (.Endpoint p b sd true g gr)) blocking rc rc' rv p) :
    ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    endpoint.receive_ipc st ar s a ct (.Endpoint p b sd true g gr) blocking rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking rc' σ).1,
        IRel st N T C E R B c r.1 z.2 ⦄ := by
  intro p b sd g gr rc rc' hpE hrc
  have hp : p ∈ E := memE_of_cover hO hpE
  obtain ⟨hIR, hSRT⟩ := hX
  have hnn : ∀ n, xt.tcbState ≠ .blockedOnNotification n := fun n h => by
    rw [h] at hrun; simp [tsCode] at hrun
  have run : ∀ {rv : U64}, ReplyArg R (L.mem s) rc rc' rv →
      endpoint.receive_ipc st ar s a ct (.Endpoint p b sd true g gr) blocking rc ⦃ r =>
        ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking rc' σ).1,
          IRel st N T C E R B c r.1 z.2 ⦄ := fun {rv} hra =>
    WP.spec_mono (receive_ipc_top hH hBf hBm hTl hP s a σ hIR hSRT hcT hkt ⟨by omega, by omega⟩ hnn hbn hp (hsort p hp) b sd true g gr hra b.bv (rightsOf sd true g gr) blocking
      (hU p b sd g gr rc rc' rv)) fun _ ⟨_, z, hz, h1, h2⟩ => ⟨z, hz, h1, h2⟩
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
theorem recv_sig_leaf (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hRV : IpcRecvHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st N T C E R B c s σ)
    (hO : Sched.ObjCover N T E R C σ)
    {ct : U64} (hcT : ct ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrr : xt.tcbState = .running ∨ xt.tcbState = .restart)
    (hsortN : ∀ n ∈ N, ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs →
      PrioSorted (fun y => L.mem s (prioA y)) xs)
    (hAR : ActReady σ) (hNQ : NotQueued σ ct.bv) (hRB : RelIfBound σ ct.bv)
    (hsane : ∀ u, σ.schedulerAction = .switchThread u → u ≠ ct.bv) (hnidle : ct.bv ≠ σ.idleThread)
    (blocking : Bool) :
    ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
      notification.receive_signal st ar s a ct p blocking ⦃ r =>
        ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac blocking σ).1, IRel st N T C E R B c r.1 z.2 ⦄ := by
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
theorem recvLeaves_of (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hRV : IpcRecvHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st N T C E R B c s σ)
    (hO : Sched.ObjCover N T E R C σ)
    {ct : U64} (hcT : ct ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrr : xt.tcbState = .running ∨ xt.tcbState = .restart) (hbn : xt.tcbBoundNotification = none)
    (hsort : ∀ e ∈ E, ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs →
      PrioSorted (fun y => L.mem s (prioA y)) xs)
    (hsortN : ∀ n ∈ N, ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs →
      PrioSorted (fun y => L.mem s (prioA y)) xs)
    (hAR : ActReady σ) (hNQ : NotQueued σ ct.bv) (hRB : RelIfBound σ ct.bv)
    (hsane : ∀ u, σ.schedulerAction = .switchThread u → u ≠ ct.bv) (hnidle : ct.bv ≠ σ.idleThread)
    (blocking : Bool)
    (hlink : ∀ p b sd g gr q g', q ∈ R → L.mem s (Endp.rTcbA q) ≠ 0#u64 →
      endpoint.receive_ipc st ar s a ct (.Endpoint p b sd true g gr) blocking (.Reply q g') ⦃ r =>
        ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking
          (absCap (.Reply q g')) σ).1, IRel st N T C E R B c r.1 z.2 ⦄)
    (hU : ∀ p b sd g gr rc rc' rv, RecvRest st ar (IRel st N T C E R B c) T s a σ ct xt (.Endpoint p b sd true g gr)
      (absCap (.Endpoint p b sd true g gr)) blocking rc rc' rv p)
    (hflt : ∀ cptr lf lf', LookupFaultRel lf lf' →
      faults.handle_fault st ar s a ct (.Cap cptr true lf) ⦃ r =>
        ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
          IRel st N T C E R B c r.1 z.2 ⦄) :
    RecvLeaves (st := st) (ar := ar) (fun s _ σ => IRel st N T C E R B c s σ) ct blocking s a σ where
  ipc := recv_ipc_leaf hH hBf hBm hTl hP s a σ hX hO hcT hkt (by rcases hrr with h | h <;> rw [h] <;> decide) hbn
    hsort blocking hlink hU
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
theorem decode_notification_top (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (hvm : ∀ s' σ', IRel st N T C E R B c s' σ' → ∀ p x, σ'.kheap p = some (.tcb x) → x.tcbState ≠ .runningVM)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st N T C E R B c s σ)
    (lbl length slot : U64) (p b : U64) (sd rv : Bool) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcT : ct ∈ T) (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hp : p ∈ N) :
    DecOKDMX (L := L) ar (fun s _ σ => IRel st N T C E R B c s σ) s a σ lbl length slot (.Notification p b sd rv)
      blk call don fp buf extra slbl args ci sl excaps buffer := by
  obtain ⟨σ1, hst⟩ : ∃ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) := by
    rw [hcur, Notif.setThreadState_eq .restart hkt]; exact ⟨_, rfl⟩
  exact decode_notificationDMX ar _ s a σ lbl length slot p b sd rv blk call don fp buf extra slbl args ci sl
    excaps buffer ct hct hX hst fun _ => send_tail_ntfn hH hBf hBm hP hvm s a σ hX hcT hcur hkt hrun hst hp b

end

end

end Fl4Proofs.P3
