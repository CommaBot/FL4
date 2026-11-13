/-
P3 (DESIGN.md §9), notifications: the spec's accessors on related objects.

On a state where `p` is a notification (resp. a TCB), `get_notification`,
`set_notification`, `get_thread_state`, `thread_set`, `as_user` with
`setRegister`, and `set_thread_state_act` have exactly one outcome and do
not fail; the lemmas here compute it. `tcb_ntfn_dequeue` on a queue member
and `tcb_append` on TCBs too.
-/
import Fl4Proofs.P3.NtfnRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Notif
open Fl4Spec Classical

noncomputable section

section
variable {σ α β : Type}
@[simp] theorem nd_pure_apply' (a : α) (s : σ) : (pure a : NonDet σ α) s = ({(a, s)}, False) := rfl
theorem nd_bind_apply' (m : NonDet σ α) (f : α → NonDet σ β) (s : σ) :
    (m >>= f) s = ({r | ∃ x ∈ (m s).1, r ∈ (f x.1 x.2).1}, (m s).2 ∨ ∃ x ∈ (m s).1, (f x.1 x.2).2) := rfl
/-- Binding after a computation with a single outcome. -/
theorem nd_bind_one {m : NonDet σ α} {s s' : σ} {a : α} (h : m s = ({(a, s')}, False)) (f : α → NonDet σ β) :
    (m >>= f) s = f a s' := by
  rw [nd_bind_apply', h]
  ext <;> simp
theorem nd_bind_one' {m : NonDet σ α} {s s' : σ} {a : α} (h : m s = ({(a, s')}, False)) (f : α → NonDet σ β) :
    NonDet.bind m f s = f a s' := nd_bind_one h f
theorem nd_pure_bind' (a : α) (f : α → NonDet σ β) (s : σ) : (pure a >>= f) s = f a s := by
  rw [nd_bind_apply']; ext <;> simp
theorem nd_gets_bind (g : σ → α) (f : α → NonDet σ β) (s : σ) : (NonDet.gets g >>= f) s = f (g s) s := by
  rw [nd_bind_apply']; ext <;> simp [NonDet.gets]
end

variable {Z : Type}

/-- The state with object `obj` at `p`. -/
def updK (σ : State Z) (p : ObjRef) (obj : KernelObject) : State Z :=
  { σ with kheap := Function.update σ.kheap p (some obj) }

@[simp] theorem updK_kheap (σ : State Z) (p : ObjRef) (obj : KernelObject) :
    (updK σ p obj).kheap = Function.update σ.kheap p (some obj) := rfl

theorem getObject_eq {σ : State Z} {p : ObjRef} {o : KernelObject} (hk : σ.kheap p = some o) :
    getObject (Z := Z) p σ = ({(o, σ)}, False) := by
  simp [getObject, NonDet.getsThe, readObject, hk, NonDet.assertOpt]; rfl

theorem setObject_eq {σ : State Z} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (ht : aType o = aType o') : setObject (Z := Z) p o' σ = ({((), updK σ p o')}, False) := by
  unfold setObject
  show (getObject p >>= _) σ = _
  rw [nd_bind_one (getObject_eq hk)]
  show (NonDet.assert _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.assert (σ := State Z) (aType o = aType o') σ = ({((), σ)}, False) by
    simp [NonDet.assert, ht])]
  show (NonDet.get >>= _) σ = _
  rw [nd_bind_one (show (NonDet.get : NonDet (State Z) (State Z)) σ = ({(σ, σ)}, False) from rfl)]
  rfl

theorem partialInv_ntfn (x : Notification) : partialInv KernelObject.notification (.notification x) = some x := by
  have hu : ∃! y, KernelObject.notification y = .notification x := ⟨x, rfl, fun y h => by cases h; rfl⟩
  unfold partialInv The
  simp only [hu, ↓reduceIte, ↓reduceDIte]
  have h := (Classical.choose_spec hu).1
  injection h with h
  rw [h]

theorem getNotification_eq {σ : State Z} {p : ObjRef} {x : Notification}
    (hk : σ.kheap p = some (.notification x)) : getNotification (Z := Z) p σ = ({(x, σ)}, False) := by
  show getSimpleKo KernelObject.notification p σ = _
  unfold getSimpleKo
  show (getObject p >>= _) σ = _
  rw [nd_bind_one (getObject_eq hk)]
  show (NonDet.assert _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.assert (σ := State Z) (isSimpleType (.notification x)) σ = ({((), σ)}, False) by
    simp [NonDet.assert, isSimpleType, aType])]
  simp only [partialInv_ntfn]; rfl

theorem setNotification_eq {σ : State Z} {p : ObjRef} {x : Notification} (y : Notification)
    (hk : σ.kheap p = some (.notification x)) :
    setNotification (Z := Z) p y σ = ({((), updK σ p (.notification y))}, False) := by
  show setSimpleKo KernelObject.notification p y σ = _
  unfold setSimpleKo
  show (getObject p >>= _) σ = _
  rw [nd_bind_one (getObject_eq hk)]
  show (NonDet.assert _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.assert (σ := State Z) (isSimpleType (.notification x)) σ = ({((), σ)}, False) by
    simp [NonDet.assert, isSimpleType, aType])]
  show (NonDet.assert _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.assert (σ := State Z)
      (partialInv KernelObject.notification (.notification x) ≠ none) σ = ({((), σ)}, False) by
    simp [NonDet.assert, partialInv_ntfn])]
  exact setObject_eq hk rfl

theorem getTcb_eq {σ : State Z} {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x)) :
    NonDet.getsThe (getTcb (Z := Z) p) σ = ({(x, σ)}, False) := by
  simp [NonDet.getsThe, getTcb, readObject, hk, NonDet.assertOpt]; rfl

theorem threadGet_eq {γ : Type} {σ : State Z} {p : ObjRef} {x : Tcb} (f : Tcb → γ)
    (hk : σ.kheap p = some (.tcb x)) : threadGet (Z := Z) f p σ = ({(f x, σ)}, False) := by
  unfold threadGet
  show (NonDet.getsThe _ >>= _) σ = _
  rw [nd_bind_one (getTcb_eq hk)]; rfl

theorem getThreadState_eq {σ : State Z} {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x)) :
    getThreadState (Z := Z) p σ = ({(x.tcbState, σ)}, False) := threadGet_eq _ hk

theorem threadSet_eq {σ : State Z} {p : ObjRef} {x : Tcb} (f : Tcb → Tcb) (hk : σ.kheap p = some (.tcb x)) :
    threadSet (Z := Z) f p σ = ({((), updK σ p (.tcb (f x)))}, False) := by
  unfold threadSet
  show (NonDet.getsThe _ >>= _) σ = _
  rw [nd_bind_one (getTcb_eq hk)]
  exact setObject_eq hk rfl

/-- The user context `uc` with register `r` set to `v`. -/
def setRegUc (uc : UserContext) (r : Register) (v : Word) : UserContext :=
  ⟨uc.userFpuState, Function.update uc.userRegs r v⟩

/-- The TCB `x` with register `r` of its user context set to `v`. -/
def setReg (x : Tcb) (r : Register) (v : Word) : Tcb :=
  { x with tcbArch := archTcbContextSet (setRegUc (archTcbContextGet x.tcbArch) r v) x.tcbArch }

theorem asUser_setRegister_eq {σ : State Z} {p : ObjRef} {x : Tcb} (r : Register) (v : Word)
    (hk : σ.kheap p = some (.tcb x)) :
    asUser (Z := Z) p (setRegister r v) σ = ({((), updK σ p (.tcb (setReg x r v)))}, False) := by
  unfold asUser
  show (NonDet.getsThe _ >>= _) σ = _
  rw [nd_bind_one (getTcb_eq hk)]
  show ((pure _ : NonDet (State Z) UserContext) >>= _) σ = _
  rw [nd_pure_bind']
  show (NonDet.selectF _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.selectF (σ := State Z) (setRegister r v (archTcbContextGet x.tcbArch)) σ =
      ({(((), ⟨(archTcbContextGet x.tcbArch).userFpuState,
        Function.update (archTcbContextGet x.tcbArch).userRegs r v⟩), σ)}, False) by
    simp only [NonDet.selectF, setRegister, NonDet.modify]
    ext ⟨a, b⟩ <;> simp)]
  show ((pure _ : NonDet (State Z) Tcb) >>= _) σ = _
  rw [nd_pure_bind']
  exact (nd_bind_one (setObject_eq (o' := KernelObject.tcb (setReg x r v)) hk rfl) _).trans rfl

/-- The outcome of `set_thread_state_act t`. -/
def stsAct (σ : State Z) (t : ObjRef) : State Z :=
  if t = σ.curThread ∧ σ.schedulerAction = .resumeCurThread ∧ ¬ schedulable t σ = true
  then { σ with schedulerAction := .chooseNewThread } else σ

theorem setThreadStateAct_eq (σ : State Z) (t : ObjRef) :
    setThreadStateAct (Z := Z) t σ = ({((), stsAct σ t)}, False) := by
  unfold setThreadStateAct
  simp only [nd_gets_bind]
  unfold stsAct NonDet.when
  split_ifs <;> rfl

end

end Fl4Proofs.P3.Notif
