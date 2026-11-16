/-
P3 (DESIGN.md §9): **`SchedValid`, the spec invariant beside the Sc side's
`Inv`** for what the finalisations of final object caps need of the spec
state beyond `Inv` and `ActReady` (the l4v invariants it restates):

* the IPC queues: duplicate-free; an endpoint's threads TCBs whose SCs are
  ready and sufficient when active (`released_ipc_queues`; for a
  notification's, blocked on it (`valid_ntfn`), this is `Inv.rd`); a thread
  blocked on an endpoint or a notification is in its queue (`valid_ep`,
  `valid_ntfn`, `sym_refs`);
* the replies: a thread blocked on a reply, or receiving with one, is the
  reply's thread, and a reply's thread is blocked on it (`sym_refs`); a
  reply in an SC's stack is a reply whose SC is the SC exactly when it is the
  head (`valid_replies`);
* the other links: an SC's thread, notification and yield-from thread, a
  TCB's bound notification and yield-to SC, a notification's bound thread
  exist (`valid_objs`, `sym_refs`), a yield-from thread yields to the SC.

`CapObjAt` is l4v's `valid_cap` for the object caps finalised here (the
object of the cap's kind exists); `CapObjHyp` asks it of related states.

From `Inv ∧ ActReady ∧ SchedValid` and `CapObjAt`: `ntfnPre_of_valid`,
`epPre_of_valid`, `replyPre_of_valid`, and at the cap level
`ntfnSpecHyp_of`, `epSpecHyp_of`, `replySpecHyp_of`.
-/
import Fl4Proofs.P3.SpecFinOutReply
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section Spec
open Fl4Spec

/-- A queued thread: a TCB whose SC (if any) is ready and sufficient when
active (l4v `released_ipc_queues`). -/
def QRdy (σ : State Unit) (u : ObjRef) : Prop :=
  ∃ x, σ.kheap u = some (.tcb x) ∧ ∀ c, x.tcbSchedContext = some c → ∀ y k, σ.kheap c = some (.schedContext y k) →
    scActive y = true → refillReady σ.curTime (refillHd y) = true ∧ refillSufficient 0 (refillHd y) = true

/-- **The spec invariant** (see the module docstring). -/
structure SchedValid (σ : State Unit) : Prop where
  epQ : ∀ e x, σ.kheap e = some (.endpoint x) → x.epQueue.Nodup ∧ ∀ u ∈ x.epQueue, QRdy σ u
  ntfnQ : ∀ n x, σ.kheap n = some (.notification x) → (ntfnQueueOf x).Nodup ∧
    ∀ u ∈ ntfnQueueOf x, ∃ xu, σ.kheap u = some (.tcb xu) ∧ xu.tcbState = .blockedOnNotification n
  recvQ : ∀ t x ep ro d, σ.kheap t = some (.tcb x) → x.tcbState = .blockedOnReceive ep ro d →
    ∃ xe, σ.kheap ep = some (.endpoint xe) ∧ t ∈ xe.epQueue
  sendQ : ∀ t x ep pl, σ.kheap t = some (.tcb x) → x.tcbState = .blockedOnSend ep pl →
    ∃ xe, σ.kheap ep = some (.endpoint xe) ∧ t ∈ xe.epQueue
  ntfnW : ∀ t x n, σ.kheap t = some (.tcb x) → x.tcbState = .blockedOnNotification n →
    ∃ xn, σ.kheap n = some (.notification xn) ∧ t ∈ ntfnQueueOf xn
  recvReply : ∀ t x ep r d, σ.kheap t = some (.tcb x) → x.tcbState = .blockedOnReceive ep (some r) d →
    ∃ xr, σ.kheap r = some (.reply xr) ∧ xr.replyTcb = some t
  onReply : ∀ t x r, σ.kheap t = some (.tcb x) → x.tcbState = .blockedOnReply r →
    ∃ xr, σ.kheap r = some (.reply xr) ∧ xr.replyTcb = some t
  replyTcb : ∀ r xr t, σ.kheap r = some (.reply xr) → xr.replyTcb = some t →
    ∃ x, σ.kheap t = some (.tcb x) ∧
      (x.tcbState = .blockedOnReply r ∨ ∃ ep d, x.tcbState = .blockedOnReceive ep (some r) d)
  replies : ∀ sc y k r, σ.kheap sc = some (.schedContext y k) → r ∈ y.scReplies →
    ∃ xr, σ.kheap r = some (.reply xr) ∧ (y.scReplies.head? = some r → xr.replySc = some sc) ∧
      (y.scReplies.head? ≠ some r → xr.replySc = none)
  scTcb : ∀ sc y k f, σ.kheap sc = some (.schedContext y k) → y.scTcb = some f → ∃ x, σ.kheap f = some (.tcb x)
  scNtfn : ∀ sc y k n, σ.kheap sc = some (.schedContext y k) → y.scNtfn = some n →
    ∃ xn, σ.kheap n = some (.notification xn)
  scYieldFrom : ∀ sc y k t, σ.kheap sc = some (.schedContext y k) → y.scYieldFrom = some t →
    ∃ x, σ.kheap t = some (.tcb x) ∧ x.tcbYieldTo = some sc
  tcbYieldTo : ∀ t x p, σ.kheap t = some (.tcb x) → x.tcbYieldTo = some p → ∃ y k, σ.kheap p = some (.schedContext y k)
  tcbNtfn : ∀ t x n, σ.kheap t = some (.tcb x) → x.tcbBoundNotification = some n →
    ∃ xn, σ.kheap n = some (.notification xn)
  ntfnTcb : ∀ n xn t, σ.kheap n = some (.notification xn) → xn.ntfnBoundTcb = some t → ∃ x, σ.kheap t = some (.tcb x)

/-- l4v `valid_cap` for the object caps finalised here: the object of the
cap's kind exists. -/
def CapObjAt (σ : State Unit) : Cap → Prop
  | .notificationCap r _ _ => ∃ x, σ.kheap r = some (.notification x)
  | .endpointCap r _ _ => ∃ x, σ.kheap r = some (.endpoint x)
  | .replyCap r _ => ∃ x, σ.kheap r = some (.reply x)
  | .threadCap r => ∃ x, σ.kheap r = some (.tcb x)
  | .schedContextCap r _ => ∃ y k, σ.kheap r = some (.schedContext y k)
  | _ => True

theorem SchedValid.repOK {σ : State Unit} (h : SchedValid σ) (u : ObjRef) : RepOK σ u :=
  fun x hk ep r d hs => h.recvReply u x ep r d hk hs

theorem SchedValid.scRepOK {σ : State Unit} (h : SchedValid σ) {r : ObjRef} {xr : Reply}
    (hkr : σ.kheap r = some (.reply xr)) : ScRepOK σ r xr := by
  intro sc y k hks hmem
  obtain ⟨xr', hkr', h1, h2⟩ := h.replies sc y k r hks hmem
  rw [hkr] at hkr'; cases hkr'
  refine ⟨h1, h2, fun r' hr' => ?_, fun f hf => h.scTcb sc y k f hks hf⟩
  obtain ⟨x', hk', -⟩ := h.replies sc y k r' hks (List.mem_of_mem_tail hr')
  exact ⟨x', hk'⟩

/-- A thread blocked on a notification has its SC released when active
(`Inv.rd`; not runnable, it is in no release queue, `Inv.rel`). -/
theorem Inv.qRdy_ntfn {σ : State Unit} (hI : Inv σ) {u n : ObjRef} {xu : Tcb} (hku : σ.kheap u = some (.tcb xu))
    (hs : xu.tcbState = .blockedOnNotification n) : QRdy σ u := by
  refine ⟨xu, hku, fun c hc y k hky ha => ?_⟩
  have hnq : u ∉ σ.releaseQueue := fun hm => by
    obtain ⟨x', -, -, -, hk', -, hr, -⟩ := hI.rel u hm
    rw [hku] at hk'; cases hk'
    rw [hs] at hr; cases hr
  exact hI.rd u xu hku (Or.inr (Or.inl ⟨n, hs⟩)) xu c y k hku hc hky ha hnq

/-- A blocked thread of `inClass` (on a notification or an endpoint) has its
SC released when active (`Inv.rd`; not runnable, it is in no release queue,
`Inv.rel`). -/
theorem Inv.qRdy_blk {σ : State Unit} (hI : Inv σ) {u : ObjRef} {xu : Tcb} (hku : σ.kheap u = some (.tcb xu))
    (hcl : inClass xu.tcbState) (hnr : runnable xu.tcbState = false) : QRdy σ u := by
  refine ⟨xu, hku, fun c hc y k hky ha => ?_⟩
  have hnq : u ∉ σ.releaseQueue := fun hm => by
    obtain ⟨x', -, -, -, hk', -, hr, -⟩ := hI.rel u hm
    rw [hku] at hk'; cases hk'
    rw [hnr] at hr; cases hr
  exact hI.rd u xu hku hcl xu c y k hku hc hky ha hnq

theorem ntfnPre_of_valid {σ : State Unit} {r : ObjRef} (hI : Inv σ) (hA : ActReady σ) (hV : SchedValid σ)
    (ho : ∃ x, σ.kheap r = some (.notification x)) : NtfnPre σ r := by
  obtain ⟨n, hk⟩ := ho
  obtain ⟨hnd, hq⟩ := hV.ntfnQ r n hk
  exact ntfnPre_of_inv hI hA hk (fun t ht => hV.ntfnTcb r n t hk ht) hnd fun u hu => by
    obtain ⟨xu, hku, hs⟩ := hq u hu
    exact hI.qRdy_ntfn hku hs

theorem epPre_of_valid {σ : State Unit} {r : ObjRef} (hI : Inv σ) (hA : ActReady σ) (hV : SchedValid σ)
    (ho : ∃ x, σ.kheap r = some (.endpoint x)) : EpPre σ r := by
  obtain ⟨x, hk⟩ := ho
  obtain ⟨hnd, hq⟩ := hV.epQ r x hk
  refine epPre_of_inv hI hA hk hnd fun u hu => ?_
  obtain ⟨xu, hku, hc⟩ := hq u hu
  exact ⟨xu, hku, hc, hV.repOK u⟩

theorem replyPre_of_valid {σ : State Unit} {r : ObjRef} (hA : ActReady σ) (hV : SchedValid σ)
    (ho : ∃ x, σ.kheap r = some (.reply x)) : ReplyPre σ r := by
  obtain ⟨xr, hkr⟩ := ho
  refine ⟨xr, hkr, fun tp ht => ?_⟩
  obtain ⟨x, hkt, hst⟩ := hV.replyTcb r xr tp hkr ht
  refine ⟨x, hkt, ?_⟩
  rcases hst with hst | ⟨ep, d, hst⟩
  · exact Or.inl ⟨hst, hV.scRepOK hkr, hA⟩
  · obtain ⟨xe, hke, hq⟩ := hV.recvQ tp x ep (some r) d hkt hst
    exact Or.inr ⟨ep, d, xe, hst, hke, hq⟩

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The scheduling invariants at related states**: `Inv`, `ActReady` and
`SchedValid`. -/
def SchedCoupling (th : TypedHeap) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost), DState (L := L) th s σ G →
    Inv σ ∧ Notif.ActReady σ ∧ SchedValid σ

/-- **l4v `valid_cap` at related states**, for the caps in slots. -/
def CapObjHyp (th : TypedHeap) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c → CapObjAt σ (absCap c)

theorem ntfnSpecHyp_of (th : TypedHeap) (hC : SchedCoupling (L := L) th) (hO : CapObjHyp (L := L) th) :
    NtfnSpecHyp (L := L) th := by
  intro s σ G sl n b0 b1 b2 hDS hA hc _
  obtain ⟨hI, hAR, hV⟩ := hC s σ G hDS
  exact ntfnPre_of_valid hI hAR hV (hO s σ G sl _ hDS hA hc)

theorem epSpecHyp_of (th : TypedHeap) (hC : SchedCoupling (L := L) th) (hO : CapObjHyp (L := L) th) :
    EpSpecHyp (L := L) th := by
  intro s σ G sl e b x1 x2 x3 x4 hDS hA hc _
  obtain ⟨hI, hAR, hV⟩ := hC s σ G hDS
  exact epPre_of_valid hI hAR hV (hO s σ G sl _ hDS hA hc)

theorem replySpecHyp_of (th : TypedHeap) (hC : SchedCoupling (L := L) th) (hO : CapObjHyp (L := L) th) :
    ReplySpecHyp (L := L) th := by
  intro s σ G sl p g hDS hA hc _
  obtain ⟨-, hAR, hV⟩ := hC s σ G hDS
  exact replyPre_of_valid hAR hV (hO s σ G sl _ hDS hA hc)

end

end Fl4Proofs.P3.Sched
