/-
P3 (DESIGN.md §9), IPC: **`do_ipc_transfer` on the merged relation**: the
register-only transfer, the transfer into a receive buffer, and the transfers
of a faulted sender (with and without a receive buffer). Each is the endpoint
lemma for `SRS T SR` (through `IpcSchedHyps.epHyps`) with the notification
relation lifted over the receiver's register and buffer words
(`ntfn_lift_rcv`).
-/
import Fl4Proofs.P3.IpcEpSteps
import Fl4Proofs.P3.EpFaultNone
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **`do_ipc_transfer`, registers only**, on the merged relation. -/
theorem do_ipc_transfer_regsI (hH : Ipc.IpcSchedHyps st ar N T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hP : Ipc.IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : Ipc.IpcRel N T E R B (L.mem s) σ)
    (hSR : SR s σ) {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (hrb : ipcBufOf true xr = none) (ep badge : U64) (grant : Bool)
    (hcaps : grant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
        ({((), updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv)))}, False) ∧
      Ipc.IpcRel N T E R B (L.mem s') (updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv))) ∧
      SR s' (updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv))) ⦄ := by
  refine WP.spec_mono (do_ipc_transfer_regs (ar := ar) (hH.epHyps hP) hBf.srs hP.e s a σ hR.toE
    ⟨hSR, Ipc.ScRelM.of hR⟩ hs hr hne hks hkr hf hrb ep badge grant hcaps) ?_
  rintro s' ⟨h1, h2, h3, h4⟩
  refine ⟨h1, Ipc.IpcRel.of (ntfn_lift_rcv hP.toC hR.toN h2 hr (h4.mono fun _ h => h.1) (fun p hp => by simp [hp])
    hkr (by simp only [updK_kheap, Function.update_self]; exact rfl) (xferTcb_state _ _ _)) h2 h3.2.all, h3.1⟩

/-- **`do_ipc_transfer` with a receive buffer**, on the merged relation. -/
theorem do_ipc_transfer_bufI (hH : Ipc.IpcSchedHyps st ar N T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hBm : EpBufMapHyps st T E R B SR) (hP : Ipc.IPlaced N T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : Ipc.IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xr = some rp) (ep badge : U64) (grant : Bool)
    (hcaps : grant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      Ipc.IpcRel N T E R B (L.mem s') σ' ∧ SR s' σ' ⦄ := by
  refine WP.spec_mono (do_ipc_transfer_buf (ar := ar) (hH.epHyps hP) hBf.srs hBm.srs hP.e s a σ hR.toE
    ⟨hSR, Ipc.ScRelM.of hR⟩ hs hr hne hks hkr hf hrb ep badge grant hcaps) ?_
  rintro s' ⟨σ', h1, h2, h3, h4, h5, x', h6, h7⟩
  exact ⟨σ', h1, Ipc.IpcRel.of (ntfn_lift_rcv hP.toC hR.toN h2 hr h4 h5 hkr h6 h7) h2 h3.2.all, h3.1⟩

/-- **`do_ipc_transfer` of a faulted sender** into a receiver with an IPC
buffer, on the merged relation. -/
theorem do_ipc_transfer_faultI (hH : Ipc.IpcSchedHyps st ar N T E R B SR) (hBm : EpBufMapHyps st T E R B SR)
    (hP : Ipc.IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : Ipc.IpcRel N T E R B (L.mem s) σ)
    (hSR : SR s σ) {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {f : Fl4Spec.Fault} (hf : xs.tcbFault = some f) (hok : FaultOK (L := L) s snd xs f)
    {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xr = some rp) (ep badge : U64) (grant : Bool) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      Ipc.IpcRel N T E R B (L.mem s') σ' ∧ SR s' σ' ⦄ := by
  refine WP.spec_mono (do_ipc_transfer_fault (ar := ar) (hH.epHyps hP) hBm.srs hP.e s a σ hR.toE
    ⟨hSR, Ipc.ScRelM.of hR⟩ hs hr hne hks hkr hf hok hrb ep badge grant) ?_
  rintro s' ⟨σ', h1, h2, h3, h4, h5, x', h6, h7⟩
  exact ⟨σ', h1, Ipc.IpcRel.of (ntfn_lift_rcv hP.toC hR.toN h2 hr h4 h5 hkr h6 h7) h2 h3.2.all, h3.1⟩

/-- **`do_ipc_transfer` of a faulted sender**, no receive buffer, on the
merged relation. -/
theorem do_ipc_transfer_faultNI (hH : Ipc.IpcSchedHyps st ar N T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hP : Ipc.IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : Ipc.IpcRel N T E R B (L.mem s) σ)
    (hSR : SR s σ) {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {f : Fl4Spec.Fault} (hf : xs.tcbFault = some f) (hok : FaultOK (L := L) s snd xs f)
    (hrb : ipcBufOf true xr = none) (ep badge : U64) (grant : Bool) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      Ipc.IpcRel N T E R B (L.mem s') σ' ∧ SR s' σ' ⦄ := by
  refine WP.spec_mono (do_ipc_transfer_faultN (ar := ar) (hH.epHyps hP) hBf.srs hP.e s a σ hR.toE
    ⟨hSR, Ipc.ScRelM.of hR⟩ hs hr hne hks hkr hf hok hrb ep badge grant) ?_
  rintro s' ⟨σ', h1, h2, h3, h4, h5, x', h6, h7⟩
  exact ⟨σ', h1, Ipc.IpcRel.of (ntfn_lift_rcv hP.toC hR.toN h2 hr h4 h5 hkr h6 h7) h2 h3.2.all, h3.1⟩

end

end

end Fl4Proofs.P3.Endp
