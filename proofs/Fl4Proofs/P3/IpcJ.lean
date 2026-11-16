/-
P3 (DESIGN.md §9), IPC: **named facts reduced to the l4v invariants already
named elsewhere** (for the final fold).

* `cancelOK_of`: `CancelOK` (the blocked-state facts `cancel_ipc` needs)
  from `SchedValid` (l4v `valid_objs`/`sym_refs` for blocked threads and the
  call stacks).
* `cancelRecvHyp_of`: `CancelRecvHyp` (IpcCancel; `IpcSchedHyps`' receiver
  facts) from `SchedValid`, `ObjCover` and the Sc proofs' `Inv`.
* `notQueued_of`: a thread that is not runnable is in no ready or release
  queue (`IpcSchedHyps.notQueued`), from `Inv` (l4v `valid_ready_qs`,
  `valid_release_q`: queue members are runnable).
-/
import Fl4Proofs.P3.IpcLeaves
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

/-- **`CancelOK` from `SchedValid`.** -/
theorem cancelOK_of {σ : Fl4Spec.State Unit} (hV : SchedValid σ) {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) : CancelOK σ t x := by
  refine ⟨fun ep pl h => hV.sendQ t x ep pl hk h, fun ep ro d h => hV.recvQ t x ep ro d hk h,
    fun ep rp d h => hV.recvReply t x ep rp d hk h, fun n h => hV.ntfnW t x n hk h, fun rp h => ?_⟩
  obtain ⟨xr, hkr, hrt⟩ := hV.onReply t x rp hk h
  refine ⟨xr, hkr, hrt, fun sc y k hks hm => ?_⟩
  obtain ⟨xr', hkr', h1, h2⟩ := hV.replies sc y k rp hks hm
  rw [hkr] at hkr'; cases hkr'
  exact ⟨h1, h2⟩

/-- **`CancelRecvHyp` from `SchedValid`, `ObjCover` and `Inv`.** -/
theorem cancelRecvHyp_of {N T E R C : Set U64} {B : Set (U64 × Fl4Spec.Word)} {m : U64 → U64}
    {σ : Fl4Spec.State Unit} (hR : EpStateRel T E R B m σ) (hV : SchedValid σ) (hO : ObjCover N T E R C σ)
    (hI : Inv σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hrb : Fl4Spec.receiveBlocked x.tcbState = true) : CancelRecvHyp E m σ t x := by
  obtain ⟨e, ro, d, hst⟩ : ∃ e ro d, x.tcbState = .blockedOnReceive e ro d := by
    cases h : x.tcbState <;> simp [h, Fl4Spec.receiveBlocked] at hrb
    exact ⟨_, _, _, rfl⟩
  refine ⟨cancelOK_of hV hk, ?_, hI.rd t.bv x hk (Or.inr (Or.inr (Or.inr ⟨e, ro, d, hst⟩)))⟩
  have hTR := hR.at_tcb ht hk
  have hb : (m (tBlockA t)).bv = e := hTR.blk e (by rw [hst]; rfl)
  obtain ⟨xe, hke, -⟩ := hV.recvQ t.bv x e ro d hk hst
  obtain ⟨e', he', he'b⟩ := hO.ep e xe hke
  have : m (tBlockA t) = e' := eq_of_bv (hb.trans he'b.symm)
  rw [this]; exact he'

/-- **A thread that is not runnable is not queued**, from `Inv`. -/
theorem notQueued_of {σ : Fl4Spec.State Unit} (hI : Inv σ) {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hnr : Fl4Spec.runnable x.tcbState = false) : NotQueued σ t := by
  refine ⟨fun d p hm => ?_, fun hm => ?_⟩
  · obtain ⟨x', _, _, _, h1, -, h3, -⟩ := hI.rq d p t hm
    rw [hk] at h1; cases h1; rw [hnr] at h3; cases h3
  · obtain ⟨x', _, _, _, h1, -, h3, -⟩ := hI.rel t hm
    rw [hk] at h1; cases h1; rw [hnr] at h3; cases h3

end

end Fl4Proofs.P3.Ipc
