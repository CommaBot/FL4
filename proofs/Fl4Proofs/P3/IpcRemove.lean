/-
P3 (DESIGN.md §9), IPC: **`reply_remove` on `IRel`** (`ReplyHyps.remove`),
its IPC half.

* `reply_unlink_irel`: `reply_unlink` of a thread blocked on the reply
  (`reply_remove`'s last step, l4v `reply_unlink_tcb`) refines on `IRel`:
  IpcCancel's `reply_unlink_c` for `SRT … SRE` (`ipcCore_top`), the thread in
  no endpoint queue from its state.

The reply path's spec facts, reduced to l4v invariants (named, for the final
fold):
* `TmoCapsValid`: l4v `valid_cap` for the TCBs' timeout-handler caps that are
  endpoint caps (`ep_at`), the one valid-caps fact; with `ObjCover` it gives
  `epE` (`epE_of`).
* `postponeOK_of`: `PostponeOK` from the Sc proofs' `Inv` (l4v
  `valid_release_q`, `sorted_release_q`, `sym_refs` of the SC links) and the
  thread not released; `not_released_of`: a thread that is not runnable is
  not released, by `Inv.rel` (l4v `valid_release_q`: release-queue members
  are runnable). Across the reply this is needed at the state before the
  receiver's restart, where it is blocked on the reply, with the release
  queue unchanged by the restart.
-/
import Fl4Proofs.P3.IpcDonate
import Fl4Proofs.P3.ScCallRemove
open Aeneas Aeneas.Std Result


/-! ## The spec's call-stack part of `reply_remove` changes only scheduling fields -/

namespace Fl4Proofs.P3.Sched
open Fl4Spec

noncomputable section

theorem nkt_replyRemoveSc (t r : ObjRef) : NKT (replyRemoveSc t r) := by
  unfold replyRemoveSc replyUnlinkSc getTcbObjRef getReply getSimpleKo
  repeat' (first | exact nkt_schedContextDonate _ _ | nkt_step | (unfold NonDet.when; split) | split)

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section Unlink
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- The spec's state after `reply_unlink_tcb`. -/
def unlinkSt (σ : Fl4Spec.State Unit) (t r : Fl4Spec.ObjRef) (x : Fl4Spec.Tcb) (xr : Fl4Spec.Reply) :
    Fl4Spec.State Unit :=
  stsAct (updK (updK σ r (.reply { xr with replyTcb := none })) t (.tcb { x with tcbState := .inactive })) t

/-- **`reply_unlink` of a thread blocked on the reply, on `IRel`.** -/
theorem reply_unlink_irel (hP0 : IPlaced N T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) {r : U64} (hst : x.tcbState = .blockedOnReply r.bv) (hr : r ∈ R)
    {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr)) (hback : xr.replyTcb = some t.bv) :
    ipc.reply_unlink st s r t ⦃ s' =>
      Fl4Spec.replyUnlinkTcb (Z := Unit) t.bv r.bv σ = ({((), unlinkSt σ t.bv r.bv x xr)}, False) ∧
      IRel st th cr N T C E R B c s' (unlinkSt σ t.bv r.bv x xr) ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP
  have hSR := IpcRel.toSRN hIR hSRT
  have hR := hIR.toE
  obtain ⟨x0, hk0, hTR⟩ := hIR.tcb t ht
  rw [hk] at hk0; cases hk0
  have hq := IpcRel.not_ep_queued hIR (t := t) (by rw [hTR.st, hst]; simp [tsCode])
  obtain ⟨e1, hR1, hS1, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s σ hR hSR.1 hr hkr 0#u64
  have hN1 := ntfn_reply_write hP0.toC hSR.2 hr hA1 hkr { xr with replyTcb := optRef 0#u64 }
  rw [optRef_zero] at e1 hR1 hS1 hN1
  have hrt : r.bv ≠ t.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hk1 : (updK σ r.bv (.reply { xr with replyTcb := none })).kheap t.bv = some (.tcb x) := by
    simp [Ne.symm hrt, hk]
  have hq1 : ∀ e ∈ E, ∀ z, (updK σ r.bv (.reply { xr with replyTcb := none })).kheap e.bv = some (.endpoint z) →
      t.bv ∉ z.epQueue := by
    intro e he z hz
    have hre : r.bv ≠ e.bv := by
      intro h; rw [← h] at hz; simp at hz
    exact hq e he z (by simpa [Ne.symm hre] using hz)
  unfold ipc.reply_unlink
  step as ⟨s1, hs1⟩
  subst hs1
  refine WP.spec_mono (set_thread_state_c hH hP0 hP _ _ hR1 ⟨hS1, hN1⟩ ht hk1 hq1 (by rw [hst]; simp [tsCode])
    .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
  rintro s2 ⟨hR2, hS2⟩
  refine ⟨?_, IpcRel.ofSRN hR2 hS2⟩
  unfold Fl4Spec.replyUnlinkTcb
  rw [nd_bind_one (getReply_eq hkr), nd_bind_one (assert_true hback σ), nd_bind_one (getThreadState_eq hk),
    nd_bind_one (assert_true (Or.inl hst) σ), nd_bind_one e1, Notif.setThreadState_eq _ hk1]
  rfl

end Unlink


/-! ## The reply path's spec facts -/

section Facts
open Fl4Spec

/-- l4v `valid_cap` of an endpoint cap: the object is an endpoint. -/
def EpCapValid (σ : State Unit) (cap : Cap) : Prop :=
  ∀ p bd r, cap = .endpointCap p bd r → ∃ z, σ.kheap p = some (.endpoint z)

/-- **The valid-caps fact** (l4v `valid_objs`' `valid_cap`, for endpoint
caps): every TCB's timeout-handler cap. -/
def TmoCapsValid (σ : State Unit) : Prop :=
  ∀ t x, σ.kheap t = some (.tcb x) → EpCapValid σ x.tcbTimeoutHandler

/-- **`epE` from `ObjCover` and `TmoCapsValid`.** -/
theorem epE_of {N T E R C : Set U64} {σ : State Unit} (hO : Sched.ObjCover N T E R C σ) (hV : TmoCapsValid σ)
    {t : U64} {x : Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {p bd : Word} {r : CapRights}
    (hh : x.tcbTimeoutHandler = .endpointCap p bd r) : ∀ e : U64, e.bv = p → e ∈ E := by
  intro e he
  obtain ⟨z, hz⟩ := hV _ x hk p bd r hh
  obtain ⟨e', he', h'⟩ := hO.ep _ z hz
  have : e = e' := Sched.bv_inj (h'.trans he.symm).symm
  rw [this]; exact he'

/-- **A thread that is not runnable is not released** (`Inv.rel`). -/
theorem not_released_of {σ : State Unit} (hI : Inv σ) {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hnr : runnable x.tcbState = false) : t ∉ σ.releaseQueue := fun hm => by
  obtain ⟨x', _, _, _, h1, -, h3, -⟩ := hI.rel t hm
  rw [hk] at h1; cases h1; rw [hnr] at h3; cases h3

/-- **`PostponeOK` from `Inv`** and the thread not released. -/
theorem postponeOK_of {σ : State Unit} (hI : Inv σ) {t sc : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hsc : x.tcbSchedContext = some sc) {y : SchedContext} {n : Nat} (hky : σ.kheap sc = some (.schedContext y n))
    (hnr : t ∉ σ.releaseQueue) : PostponeOK σ t y := by
  refine ⟨⟨fun u hu => ?_, hI.sorted⟩, hnr, ?_⟩
  · obtain ⟨x', p, -, -, h1, h2, -⟩ := hI.rel u hu; exact ⟨x', p, h1, h2⟩
  · obtain ⟨y', n', h1, h2⟩ := hI.back t x sc hk hsc
    rw [hky] at h1; cases h1; exact h2

end Facts

end

end Fl4Proofs.P3.Ipc
