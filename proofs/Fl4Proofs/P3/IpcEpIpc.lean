/-
P3 (DESIGN.md §9), IPC: **the endpoint transfer theorems on the merged
relation** `IpcRel`: each `XI` is `X_gen` (in the file of `X`) with the steps
of `IpcSchedHyps.steps` and the tails of `IpcEpTailHyps`, for
`SR` ∧ the SC words ∧ the notification relation (IpcEpBase.lean). Next to the
endpoint theorems' hypotheses: `IpcSchedHyps` and `IpcEpTailHyps` for `SR`,
`IPlaced`, and, for the calls, a caller not `BlockedOnNotification`.
-/
import Fl4Proofs.P3.IpcEpSteps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **`send_ipc_recv` on the merged relation.** -/
theorem send_ipc_recvI (hH : IpcSchedHyps st ar N T E R B SR) (hBf : EpBufHyps st T E R B SR) (hBm : EpBufMapHyps st T E R B SR) (hTl : IpcEpTailHyps st A N T E R B SR) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hft : xt.tcbFault = none) {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q)))) {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) (hrb : ipcBufOf true xd = none) (badge : U64) (g gr : Bool) (hcaps : g = false ∨ ipcBufOf false xt = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xt.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv) (blk : Bool) :
    endpoint.send_ipc st ar s a blk false badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  WP.spec_mono (send_ipc_recv_gen (hH.steps (A := A) hBf hBm hP).toEpSteps (hTl.tail hP) hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hft he hk hkd hrb badge g gr (Or.inr hcaps) hback blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

/-- **`send_ipc_call` on the merged relation.** -/
theorem send_ipc_callI (hH : IpcSchedHyps st ar N T E R B SR) (hBf : EpBufHyps st T E R B SR) (hBm : EpBufMapHyps st T E R B SR) (hTl : IpcEpTailHyps st A N T E R B SR) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hft : xt.tcbFault = none) (hns : tsCode xt.tcbState ≠ 6) {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q)))) {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) (hrb : ipcBufOf true xd = none) (badge : U64) (g gr : Bool) (hcaps : g = false ∨ ipcBufOf false xt = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xt.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv) (hg : g = true ∨ gr = true) (hrp0 : ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none) (blk : Bool) :
    endpoint.send_ipc st ar s a blk true badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  WP.spec_mono (send_ipc_call_gen (hH.steps (A := A) hBf hBm hP).toEpSteps (hTl.tail hP) hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hft hns he hk hkd hrb badge g gr (Or.inr hcaps) hback hg hrp0 blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

/-- **`send_ipc_call_inactive` on the merged relation.** -/
theorem send_ipc_call_inactiveI (hH : IpcSchedHyps st ar N T E R B SR) (hBf : EpBufHyps st T E R B SR) (hBm : EpBufMapHyps st T E R B SR) (hTl : IpcEpTailHyps st A N T E R B SR) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hft : xt.tcbFault = none) (hns : tsCode xt.tcbState ≠ 6) {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q)))) {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) (hrb : ipcBufOf true xd = none) (badge : U64) (g gr : Bool) (hcaps : g = false ∨ ipcBufOf false xt = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xt.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv) (hno : (g = false ∧ gr = false) ∨ ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep = none) (blk : Bool) :
    endpoint.send_ipc st ar s a blk true badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr false t.bv e.bv σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  WP.spec_mono (send_ipc_call_inactive_gen (hH.steps (A := A) hBf hBm hP).toEpSteps (hTl.tail hP) hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hft hns he hk hkd hrb badge g gr (Or.inr hcaps) hback hno blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

/-- **`receive_ipc_sendCallPush` on the merged relation.** -/
theorem receive_ipc_sendCallPushI (hH : IpcSchedHyps st ar N T E R B SR) (hBf : EpBufHyps st T E R B SR) (hBm : EpBufMapHyps st T E R B SR) (hTl : IpcEpTailHyps st A N T E R B SR) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none) (hrb : ipcBufOf true xt = none) {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q)))) {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none) (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true) (hg : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) (hscn : xs.tcbSchedContext = none) (hcaps : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) (cb : U64) (c1 c2 c3 c4 : Bool) {rv : U64} (b' : Bool) (r' : Fl4Spec.CapRights) (hrvR : rv ∈ R) (hrv0 : L.mem s (rTcbA rv) = 0#u64) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk (.Reply rv b') ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk (.replyCap rv.bv r') σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk (.replyCap rv.bv r') σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  WP.spec_mono (receive_ipc_sendCallPush_gen (hH.steps (A := A) hBf hBm hP).toEpSteps (hTl.tail hP) hTl.sc hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hbn hrb he hk hks hfs hcall hg hscn (fun e' dd h => Or.inr (hcaps e' dd h)) cb c1 c2 c3 c4 b' r' hrvR hrv0 b rights blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

/-- **`receive_ipc_sendCallInactive` on the merged relation.** -/
theorem receive_ipc_sendCallInactiveI (hH : IpcSchedHyps st ar N T E R B SR) (hBf : EpBufHyps st T E R B SR) (hBm : EpBufMapHyps st T E R B SR) (hTl : IpcEpTailHyps st A N T E R B SR) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none) (hrb : ipcBufOf true xt = none) {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q)))) {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none) (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true) (hcaps : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg R (L.mem s) rc rc' rv) (hno : (∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∧ dd.senderCanGrantReply = false) ∨
      rv = 0#u64) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  WP.spec_mono (receive_ipc_sendCallInactive_gen (hH.steps (A := A) hBf hBm hP).toEpSteps (hTl.tail hP) hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hbn hrb he hk hks hfs hcall (fun e' dd h => Or.inr (hcaps e' dd h)) cb c1 c2 c3 c4 hrc hno b rights blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

/-- **`receive_ipc_send` on the merged relation.** -/
theorem receive_ipc_sendI (hH : IpcSchedHyps st ar N T E R B SR) (hBf : EpBufHyps st T E R B SR) (hBm : EpBufMapHyps st T E R B SR) (hTl : IpcEpTailHyps st A N T E R B SR) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none) (hrb : ipcBufOf true xt = none) {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q)))) {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none) (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = false) (hcaps : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  WP.spec_mono (receive_ipc_send_gen (hH.steps (A := A) hBf hBm hP).toEpSteps (hTl.tail hP) hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hbn hrb he hk hks hfs hcall (fun e' dd h => Or.inr (hcaps e' dd h)) cb c1 c2 c3 c4 hrc b rights blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

/-- **`send_ipc_recv_buf` on the merged relation.** -/
theorem send_ipc_recv_bufI (hH : IpcSchedHyps st ar N T E R B SR) (hBf : EpBufHyps st T E R B SR) (hBm : EpBufMapHyps st T E R B SR) (hTl : IpcEpTailHyps st A N T E R B SR) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hft : xt.tcbFault = none) {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q)))) {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xd = some rp) (badge : U64) (g gr : Bool) (hcaps : g = false ∨ ipcBufOf false xt = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xt.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv) (blk : Bool) :
    endpoint.send_ipc st ar s a blk false badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  WP.spec_mono (send_ipc_recv_buf_gen (hH.steps (A := A) hBf hBm hP) (hTl.tail hP) hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hft he hk hkd hrb badge g gr (Or.inr hcaps) hback blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

/-- **`receive_ipc_send_buf` on the merged relation.** -/
theorem receive_ipc_send_bufI (hH : IpcSchedHyps st ar N T E R B SR) (hBf : EpBufHyps st T E R B SR) (hBm : EpBufMapHyps st T E R B SR) (hTl : IpcEpTailHyps st A N T E R B SR) (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none) {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xt = some rp) {e sd : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q)))) {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none) (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = false) (hcaps : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderCanGrant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) (blk : Bool) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  WP.spec_mono (receive_ipc_send_buf_gen (hH.steps (A := A) hBf hBm hP) (hTl.tail hP) hP.e s a σ hR.toE (IpcRel.toSRN hR hSR) ht hkt hnb hbn hrb he hk hks hfs hcall (fun e' dd h => Or.inr (hcaps e' dd h)) cb c1 c2 c3 c4 hrc b rights blk) fun _ ⟨h1, h2, σ', h3, h4, h5⟩ => ⟨h1, h2, σ', h3, IpcRel.ofSRN h4 h5⟩

end

end

end Fl4Proofs.P3.Endp
