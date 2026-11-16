/-
P3 (DESIGN.md §9), IPC: **the endpoint transfer theorems with grants** (G4):
each `XG` is `X_gen` with the steps of `IpcSchedHyps.stepsG` (the bundle with
`GC := True`, IpcGrantX.lean) for `SRT … SRE`, so without the no-caps
hypothesis of `XI` (IpcEpIpc.lean).
-/
import Fl4Proofs.P3.IpcGrantX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`send_ipc_recv` with grants** on `SRT … SRE`. -/
theorem send_ipc_recvG (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hft : xt.tcbFault = none) {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q)))) {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) (hrb : ipcBufOf true xd = none) (badge : U64) (g gr : Bool) (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv) (blk : Bool) :
    endpoint.send_ipc st ar s a blk false badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ (SRT st th cr N T C E R B c (SRE st N T C E R B c)) r.1 σ' ⦄ :=
  WP.spec_mono (send_ipc_recv_gen (IpcSchedHyps.stepsG (A := A) hH hBf hBm hP).toEpSteps (hTl.tail hP) hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hft he hk hkd hrb badge g gr (Or.inl trivial) hback blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

/-- **`send_ipc_call` with grants** on `SRT … SRE`. -/
theorem send_ipc_callG (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hft : xt.tcbFault = none) (hns : tsCode xt.tcbState ≠ 6) {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q)))) {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) (hrb : ipcBufOf true xd = none) (badge : U64) (g gr : Bool) (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv) (hg : g = true ∨ gr = true) (hrp0 : ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none) (blk : Bool) :
    endpoint.send_ipc st ar s a blk true badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ (SRT st th cr N T C E R B c (SRE st N T C E R B c)) r.1 σ' ⦄ :=
  WP.spec_mono (send_ipc_call_gen (IpcSchedHyps.stepsG (A := A) hH hBf hBm hP).toEpSteps (hTl.tail hP) hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hft hns he hk hkd hrb badge g gr (Or.inl trivial) hback hg hrp0 blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

/-- **`send_ipc_call_inactive` with grants** on `SRT … SRE`. -/
theorem send_ipc_call_inactiveG (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hft : xt.tcbFault = none) (hns : tsCode xt.tcbState ≠ 6) {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q)))) {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) (hrb : ipcBufOf true xd = none) (badge : U64) (g gr : Bool) (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv) (hno : (g = false ∧ gr = false) ∨ ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep = none) (blk : Bool) :
    endpoint.send_ipc st ar s a blk true badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ (SRT st th cr N T C E R B c (SRE st N T C E R B c)) r.1 σ' ⦄ :=
  WP.spec_mono (send_ipc_call_inactive_gen (IpcSchedHyps.stepsG (A := A) hH hBf hBm hP).toEpSteps (hTl.tail hP) hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hft hns he hk hkd hrb badge g gr (Or.inl trivial) hback hno blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

/-- **`receive_ipc_sendCallPush` with grants** on `SRT … SRE`. -/
theorem receive_ipc_sendCallPushG (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none) (hrb : ipcBufOf true xt = none) {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q)))) {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none) (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true) (hg : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) (hscn : xs.tcbSchedContext = none) (cb : U64) (c1 c2 c3 c4 : Bool) {rv : U64} (b' : Bool) (r' : Fl4Spec.CapRights) (hrvR : rv ∈ R) (hrv0 : L.mem s (rTcbA rv) = 0#u64) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk (.Reply rv b') ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk (.replyCap rv.bv r') σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk (.replyCap rv.bv r') σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ (SRT st th cr N T C E R B c (SRE st N T C E R B c)) r.1 σ' ⦄ :=
  WP.spec_mono (receive_ipc_sendCallPush_gen (IpcSchedHyps.stepsG (A := A) hH hBf hBm hP).toEpSteps (hTl.tail hP) hTl.sc hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hbn hrb he hk hks hfs hcall hg hscn (fun _ _ _ => Or.inl trivial) cb c1 c2 c3 c4 b' r' hrvR hrv0 b rights blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

/-- **`receive_ipc_sendCallInactive` with grants** on `SRT … SRE`. -/
theorem receive_ipc_sendCallInactiveG (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none) (hrb : ipcBufOf true xt = none) {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q)))) {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none) (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true) (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg R (L.mem s) rc rc' rv) (hno : (∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∧ dd.senderCanGrantReply = false) ∨
      rv = 0#u64) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ (SRT st th cr N T C E R B c (SRE st N T C E R B c)) r.1 σ' ⦄ :=
  WP.spec_mono (receive_ipc_sendCallInactive_gen (IpcSchedHyps.stepsG (A := A) hH hBf hBm hP).toEpSteps (hTl.tail hP) hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hbn hrb he hk hks hfs hcall (fun _ _ _ => Or.inl trivial) cb c1 c2 c3 c4 hrc hno b rights blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

/-- **`receive_ipc_send` with grants** on `SRT … SRE`. -/
theorem receive_ipc_sendG (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none) (hrb : ipcBufOf true xt = none) {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q)))) {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none) (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = false) (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ (SRT st th cr N T C E R B c (SRE st N T C E R B c)) r.1 σ' ⦄ :=
  WP.spec_mono (receive_ipc_send_gen (IpcSchedHyps.stepsG (A := A) hH hBf hBm hP).toEpSteps (hTl.tail hP) hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hbn hrb he hk hks hfs hcall (fun _ _ _ => Or.inl trivial) cb c1 c2 c3 c4 hrc b rights blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

/-- **`send_ipc_recv_buf` with grants** on `SRT … SRE`. -/
theorem send_ipc_recv_bufG (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hft : xt.tcbFault = none) {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q)))) {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xd = some rp) (badge : U64) (g gr : Bool) (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv) (blk : Bool) :
    endpoint.send_ipc st ar s a blk false badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ (SRT st th cr N T C E R B c (SRE st N T C E R B c)) r.1 σ' ⦄ :=
  WP.spec_mono (send_ipc_recv_buf_gen (IpcSchedHyps.stepsG (A := A) hH hBf hBm hP) (hTl.tail hP) hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hft he hk hkd hrb badge g gr (Or.inl trivial) hback blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

/-- **`receive_ipc_send_buf` with grants** on `SRT … SRE`. -/
theorem receive_ipc_send_bufG (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none) {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xt = some rp) {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q)))) {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none) (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = false) (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ (SRT st th cr N T C E R B c (SRE st N T C E R B c)) r.1 σ' ⦄ :=
  WP.spec_mono (receive_ipc_send_buf_gen (IpcSchedHyps.stepsG (A := A) hH hBf hBm hP) (hTl.tail hP) hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hbn hrb he hk hks hfs hcall (fun _ _ _ => Or.inl trivial) cb c1 c2 c3 c4 hrc b rights blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

end

end

end Fl4Proofs.P3.Endp
