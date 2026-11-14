/-
P3 (DESIGN.md §9), endpoints: the spec's accessors on related objects.

On a state where `p` is an endpoint (resp. a reply object, a TCB),
`get_endpoint`, `set_endpoint`, `get_reply`, `set_reply_obj_ref
reply_tcb_update`, `tcb_ep_dequeue` of a member and `tcb_ep_append` have
exactly one outcome and do not fail; the lemmas here compute it.
-/
import Fl4Proofs.P3.EpRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open Fl4Spec Classical Fl4Proofs.P3.Notif

noncomputable section

variable {Z : Type}

theorem partialInv_ep (x : Endpoint) : partialInv KernelObject.endpoint (.endpoint x) = some x := by
  have hu : ∃! y, KernelObject.endpoint y = .endpoint x := ⟨x, rfl, fun y h => by cases h; rfl⟩
  unfold partialInv The
  simp only [hu, ↓reduceIte, ↓reduceDIte]
  have h := (Classical.choose_spec hu).1
  injection h with h
  rw [h]

theorem partialInv_reply (x : Reply) : partialInv KernelObject.reply (.reply x) = some x := by
  have hu : ∃! y, KernelObject.reply y = .reply x := ⟨x, rfl, fun y h => by cases h; rfl⟩
  unfold partialInv The
  simp only [hu, ↓reduceIte, ↓reduceDIte]
  have h := (Classical.choose_spec hu).1
  injection h with h
  rw [h]

theorem getEndpoint_eq {σ : State Z} {p : ObjRef} {x : Endpoint}
    (hk : σ.kheap p = some (.endpoint x)) : getEndpoint (Z := Z) p σ = ({(x, σ)}, False) := by
  show getSimpleKo KernelObject.endpoint p σ = _
  unfold getSimpleKo
  show (getObject p >>= _) σ = _
  rw [nd_bind_one (getObject_eq hk)]
  show (NonDet.assert _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.assert (σ := State Z) (isSimpleType (.endpoint x)) σ = ({((), σ)}, False) by
    simp [NonDet.assert, isSimpleType, aType])]
  simp only [partialInv_ep]; rfl

theorem setEndpoint_eq {σ : State Z} {p : ObjRef} {x : Endpoint} (y : Endpoint)
    (hk : σ.kheap p = some (.endpoint x)) :
    setEndpoint (Z := Z) p y σ = ({((), updK σ p (.endpoint y))}, False) := by
  show setSimpleKo KernelObject.endpoint p y σ = _
  unfold setSimpleKo
  show (getObject p >>= _) σ = _
  rw [nd_bind_one (getObject_eq hk)]
  show (NonDet.assert _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.assert (σ := State Z) (isSimpleType (.endpoint x)) σ = ({((), σ)}, False) by
    simp [NonDet.assert, isSimpleType, aType])]
  show (NonDet.assert _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.assert (σ := State Z)
      (partialInv KernelObject.endpoint (.endpoint x) ≠ none) σ = ({((), σ)}, False) by
    simp [NonDet.assert, partialInv_ep])]
  exact setObject_eq hk rfl

theorem getReply_eq {σ : State Z} {p : ObjRef} {x : Reply}
    (hk : σ.kheap p = some (.reply x)) : getReply (Z := Z) p σ = ({(x, σ)}, False) := by
  show getSimpleKo KernelObject.reply p σ = _
  unfold getSimpleKo
  show (getObject p >>= _) σ = _
  rw [nd_bind_one (getObject_eq hk)]
  show (NonDet.assert _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.assert (σ := State Z) (isSimpleType (.reply x)) σ = ({((), σ)}, False) by
    simp [NonDet.assert, isSimpleType, aType])]
  simp only [partialInv_reply]; rfl

theorem setReply_eq {σ : State Z} {p : ObjRef} {x : Reply} (y : Reply)
    (hk : σ.kheap p = some (.reply x)) :
    setReply (Z := Z) p y σ = ({((), updK σ p (.reply y))}, False) := by
  show setSimpleKo KernelObject.reply p y σ = _
  unfold setSimpleKo
  show (getObject p >>= _) σ = _
  rw [nd_bind_one (getObject_eq hk)]
  show (NonDet.assert _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.assert (σ := State Z) (isSimpleType (.reply x)) σ = ({((), σ)}, False) by
    simp [NonDet.assert, isSimpleType, aType])]
  show (NonDet.assert _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.assert (σ := State Z)
      (partialInv KernelObject.reply (.reply x) ≠ none) σ = ({((), σ)}, False) by
    simp [NonDet.assert, partialInv_reply])]
  exact setObject_eq hk rfl

theorem getReplyTcb_eq {σ : State Z} {p : ObjRef} {x : Reply}
    (hk : σ.kheap p = some (.reply x)) : getReplyTcb (Z := Z) p σ = ({(x.replyTcb, σ)}, False) := by
  show (NonDet.liftM _ _) σ = _
  unfold NonDet.liftM
  rw [nd_bind_one' (getReply_eq hk)]; rfl

/-- `set_reply_obj_ref reply_tcb_update`. -/
theorem setReplyTcb_eq {σ : State Z} {p : ObjRef} {x : Reply} (v : Option ObjRef)
    (hk : σ.kheap p = some (.reply x)) :
    setReplyObjRef (Z := Z) replyTcbUpdate p v σ = ({((), updK σ p (.reply { x with replyTcb := v }))}, False) := by
  show updateSkObjRef KernelObject.reply replyTcbUpdate p v σ = _
  unfold updateSkObjRef
  rw [nd_bind_one (getReply_eq hk)]
  exact setReply_eq _ hk

theorem getTcbObjRef_eq {σ : State Z} {p : ObjRef} {x : Tcb} (f : Tcb → Option ObjRef)
    (hk : σ.kheap p = some (.tcb x)) : getTcbObjRef (Z := Z) f p σ = ({(f x, σ)}, False) := threadGet_eq f hk

/-- The endpoint after the dequeue of `t` (l4v `tcb_ep_dequeue`). -/
def epDeq (x : Endpoint) (t : ObjRef) : Endpoint :=
  match removeAll t x.epQueue with
  | [] => .idleEP
  | _ => updateEpQueue x (removeAll t x.epQueue) true

/-- `tcb_ep_dequeue` of a member. -/
theorem tcbEpDequeue_eq {σ : State Z} {p t : ObjRef} {x : Endpoint}
    (hk : σ.kheap p = some (.endpoint x)) (ht : t ∈ x.epQueue) :
    tcbEpDequeue (Z := Z) t p σ = ({((), updK σ p (.endpoint (epDeq x t)))}, False) := by
  unfold tcbEpDequeue
  rw [nd_bind_one (getEndpoint_eq hk), nd_pure_bind', nd_bind_one (assert_true ht σ), nd_pure_bind',
    nd_pure_bind']
  exact setEndpoint_eq _ hk

/-- `tcb_ep_append` on TCBs: the ordered insertion by the spec's
priorities. -/
theorem tcbEpAppend_eq {σ : State Z} {t p : ObjRef} {x : Endpoint} {xt : Tcb}
    (hk : σ.kheap p = some (.endpoint x)) (hkt : σ.kheap t = some (.tcb xt)) (g : ObjRef → Priority)
    (hq : ∀ y ∈ x.epQueue, ∃ x, σ.kheap y = some (.tcb x) ∧ x.tcbPriority = g y) (isRecv : Bool) :
    tcbEpAppend (Z := Z) t p isRecv σ = ({((), updK σ p (.endpoint
      (updateEpQueue x (specIns x.epQueue g xt.tcbPriority t) isRecv)))}, False) := by
  unfold tcbEpAppend
  rw [nd_bind_one (getEndpoint_eq hk), nd_pure_bind', nd_bind_one (tcbAppend_eq hkt _ g hq)]
  exact setEndpoint_eq _ hk

end

end Fl4Proofs.P3.Endp
