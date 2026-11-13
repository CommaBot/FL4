/-
The extensible state of the abstract specification and the kernel monads.

Ports, in theory order:
- the `List_Lib` functions Deterministic_A uses;
- `spec/abstract/Deterministic_A`: the `state_ext` class, the deterministic
  instantiation `det_ext` (CDT sibling order, work units) and the
  nondeterministic one (`unit`), and the extended operations;
- `spec/abstract/Exceptions_A`: the kernel monads (`s_monad`, `f_monad`,
  `se_monad`, `lf_monad`, `p_monad`) and the lifting functions between them.

Both theories come before KHeap_A in l4v's import order (KHeap_A imports
Exceptions_A, which imports Deterministic_A), so they are ported here rather
than in Sched and Syscall. The `trans_state` simp lemmas are not ported.
-/
import Fl4Spec.Structures

namespace Fl4Spec

open Classical

noncomputable section

/-! ## List_Lib -/

/-- l4v: List_Lib.list_replace. -/
def listReplace {α : Type} [DecidableEq α] (list : List α) (a b : α) : List α :=
  list.map fun x => if x = a then b else x

/-- l4v: List_Lib.list_replace_list. -/
def listReplaceList {α : Type} [DecidableEq α] : List α → α → List α → List α
  | [], _, _ => []
  | x :: xs, a, list' => if x = a then list' ++ xs else x :: listReplaceList xs a list'

/-- l4v: List_Lib.list_swap. -/
def listSwap {α : Type} [DecidableEq α] (list : List α) (a b : α) : List α :=
  list.map fun x => if x = a then b else if x = b then a else x

/-- l4v: List_Lib.list_insert_after. -/
def listInsertAfter {α : Type} [DecidableEq α] : List α → α → α → List α
  | [], _, _ => []
  | x :: xs, a, b => if x = a then x :: b :: xs else x :: listInsertAfter xs a b

/-- l4v: List_Lib.list_remove. -/
def listRemove {α : Type} [DecidableEq α] : List α → α → List α
  | [], _ => []
  | x :: xs, a => if x = a then listRemove xs a else x :: listRemove xs a

/-- l4v: List_Lib.after_in_list. -/
def afterInList {α : Type} [DecidableEq α] : List α → α → Option α
  | [], _ => none
  | [_], _ => none
  | x :: y :: xs, a => if a = x then some y else afterInList (y :: xs) a

/-! ## Deterministic_A -/

/-- l4v: Deterministic_A.trans_state: change the extended state with `t`. -/
def transState {A B : Type} (t : A → B) (s : State A) : State B :=
  { toAbstractState := s.toAbstractState, exst := t s.exst }

/-- l4v: Deterministic_A.truncate_state (`abbreviation`). -/
abbrev truncateState {A : Type} : State A → State Unit := transState fun _ => ()

/-- l4v: Deterministic_A.cdt_list: for each CDT node, its children in
order. -/
abbrev CdtList := CslotPtr → List CslotPtr

/-- l4v: Deterministic_A.work_units_limit. -/
def workUnitsLimit : Word := 0x64

/-- l4v: Deterministic_A.det_ext: the extended state of the deterministic
abstract specification. -/
structure DetExt where
  workUnitsCompletedInternal : Word
  cdtListInternal : CdtList
deriving Inhabited

/-- l4v: Deterministic_A.det_state. -/
abbrev DetState := State DetExt

/-- l4v: Deterministic_A.work_units_completed (`abbreviation`). -/
abbrev workUnitsCompleted (s : DetState) : Word := s.exst.workUnitsCompletedInternal

/-- l4v: Deterministic_A.work_units_completed_update (`abbreviation`). -/
abbrev workUnitsCompletedUpdate (f : Word → Word) (s : DetState) : DetState :=
  transState (fun e => { e with workUnitsCompletedInternal := f e.workUnitsCompletedInternal }) s

/-- l4v: Deterministic_A.cdt_list (`abbreviation`). -/
abbrev cdtList (s : DetState) : CdtList := s.exst.cdtListInternal

/-- l4v: Deterministic_A.cdt_list_update (`abbreviation`). -/
abbrev cdtListUpdate (f : CdtList → CdtList) (s : DetState) : DetState :=
  transState (fun e => { e with cdtListInternal := f e.cdtListInternal }) s

/-- l4v: Deterministic_A.det_ext_monad. -/
abbrev DetExtMonad (α : Type) := NonDet DetState α

/-- l4v: Deterministic_A.state_ext: the instantiations of the abstract
specification, in practice the deterministic one (`DetExt`) and the
nondeterministic one (`Unit`). -/
class StateExt (A : Type) where
  unwrapExt : State A → State DetExt
  wrapExt : (DetExt → DetExt) → A → A
  wrapExtOp : DetExtMonad Unit → NonDet (State A) Unit
  wrapExtBool : DetExtMonad Bool → NonDet (State A) Bool
  selectSwitch : A → Bool
  extInit : A

/-- l4v: Deterministic_A.det_ext_ext (instantiation of `state_ext`): the
deterministic abstract specification. -/
instance : StateExt DetExt where
  unwrapExt := fun x => x
  wrapExt := fun x => x
  wrapExtOp := fun x => x
  wrapExtBool := fun x => x
  selectSwitch := fun _ => true
  extInit := { workUnitsCompletedInternal := 0, cdtListInternal := fun _ => [] }

/-- l4v: Deterministic_A.unit (instantiation of `state_ext`): the
nondeterministic abstract specification. -/
instance : StateExt Unit where
  unwrapExt := fun _ => undefined
  wrapExt := fun _ _ => ()
  wrapExtOp := fun _ => NonDet.pure ()
  wrapExtBool := fun _ => NonDet.select Set.univ
  selectSwitch := fun _ => false
  extInit := ()

/-- l4v: Deterministic_A.set_cdt_list. -/
def setCdtList (t : CdtList) : NonDet DetState Unit := do
  let s ← NonDet.get
  NonDet.put (cdtListUpdate (fun _ => t) s)

/-- l4v: Deterministic_A.update_cdt_list. -/
def updateCdtList (f : CdtList → CdtList) : NonDet DetState Unit := do
  let t ← NonDet.gets cdtList
  setCdtList (f t)

/-- l4v: Deterministic_A.next_child. -/
def nextChild (slot : CslotPtr) (t : CdtList) : Option CslotPtr :=
  match t slot with
  | [] => none
  | x :: _ => some x

/-- l4v: Deterministic_A.next_sib. -/
def nextSib (slot : CslotPtr) (t : CdtList) (m : Cdt) : Option CslotPtr :=
  match m slot with
  | none => none
  | some p => afterInList (t p) slot

/-- The graph of l4v `next_not_child` (a partial `function (domintros)`): the
least relation closed under its defining equation. -/
inductive NextNotChildGraph (t : CdtList) (m : Cdt) : CslotPtr → Option CslotPtr → Prop
  | noSibNoParent {slot} : nextSib slot t m = none → m slot = none →
      NextNotChildGraph t m slot none
  | noSibParent {slot p r} : nextSib slot t m = none → m slot = some p →
      NextNotChildGraph t m p r → NextNotChildGraph t m slot r
  | sib {slot} : nextSib slot t m ≠ none → NextNotChildGraph t m slot (nextSib slot t m)

/-- l4v: Deterministic_A.next_not_child. Isabelle defines it with
`function (domintros)` as `THE` of its graph; so does this. On its domain
(the CDT has no loops) it satisfies
`next_not_child slot t m = (if next_sib slot t m = None then case m slot of
None ⇒ None | Some p ⇒ next_not_child p t m else next_sib slot t m)`. -/
def nextNotChild (slot : CslotPtr) (t : CdtList) (m : Cdt) : Option CslotPtr :=
  The (NextNotChildGraph t m slot)

/-- l4v: Deterministic_A.next_slot: the CDT traversal of Haskell
`mdb_next`, children first. -/
def nextSlot (slot : CslotPtr) (t : CdtList) (m : Cdt) : Option CslotPtr :=
  if t slot ≠ [] then nextChild slot t else nextNotChild slot t m

/-- l4v: Deterministic_A.cap_swap_ext. -/
def capSwapExt (slot1 slot2 : CslotPtr) (slot1Op slot2Op : Option CslotPtr) :
    NonDet DetState Unit := do
  updateCdtList fun list => Function.update (Function.update list slot1 (list slot2)) slot2 (list slot1)
  updateCdtList fun list =>
    match (if slot2Op = some slot1 then some slot2
           else if slot2Op = some slot2 then some slot1 else slot2Op) with
    | none =>
      match (if slot1Op = some slot1 then some slot2
             else if slot1Op = some slot2 then some slot1 else slot1Op) with
      | none => list
      | some slot2P => Function.update list slot2P (listReplace (list slot2P) slot1 slot2)
    | some slot1P =>
      match (if slot1Op = some slot1 then some slot2
             else if slot1Op = some slot2 then some slot1 else slot1Op) with
      | none => Function.update list slot1P (listReplace (list slot1P) slot2 slot1)
      | some slot2P =>
        if slot1P = slot2P
        then Function.update list slot1P (listSwap (list slot1P) slot1 slot2)
        else Function.update (Function.update list slot1P (listReplace (list slot1P) slot2 slot1))
               slot2P (listReplace (list slot2P) slot1 slot2)

/-- l4v: Deterministic_A.cap_move_ext. -/
def capMoveExt (srcSlot destSlot : CslotPtr) (srcP destP : Option CslotPtr) :
    NonDet DetState Unit := do
  updateCdtList fun list =>
    match destP with
    | none => list
    | some p => Function.update list p (listRemove (list p) destSlot)
  if srcSlot = destSlot then NonDet.pure () else do
    updateCdtList fun list =>
      match srcP with
      | none => list
      | some p => Function.update list p (listReplace (list p) srcSlot destSlot)
    updateCdtList fun list =>
      Function.update (Function.update list srcSlot []) destSlot (list srcSlot ++ list destSlot)

/-- l4v: Deterministic_A.cap_insert_ext. -/
def capInsertExt (srcParent : Bool) (srcSlot destSlot : CslotPtr) (srcP destP : Option CslotPtr) :
    NonDet DetState Unit := do
  updateCdtList fun list =>
    match destP with
    | none => list
    | some p => Function.update list p (listRemove (list p) destSlot)
  updateCdtList fun list =>
    match srcP with
    | none => Function.update list srcSlot
        (if srcParent then [destSlot] ++ list srcSlot else list srcSlot)
    | some p => Function.update (Function.update list srcSlot
          (if srcParent then [destSlot] ++ list srcSlot else list srcSlot))
        p (if srcParent ∧ p ≠ srcSlot
           then list p
           else if srcSlot ≠ destSlot
                then listInsertAfter (list p) srcSlot destSlot
                else destSlot :: list p)

/-- l4v: Deterministic_A.empty_slot_ext. -/
def emptySlotExt (slot : CslotPtr) (slotP : Option CslotPtr) : NonDet DetState Unit :=
  updateCdtList fun list =>
    match slotP with
    | none => Function.update list slot []
    | some p =>
      if p = slot
      then Function.update list p (listRemove (list p) slot)
      else Function.update (Function.update list p (listReplaceList (list p) slot (list slot))) slot []

/-- l4v: Deterministic_A.create_cap_ext. -/
def createCapExt (untyped dest : CslotPtr) (destP : Option CslotPtr) : NonDet DetState Unit := do
  updateCdtList fun list =>
    match destP with
    | none => list
    | some p => Function.update list p (listRemove (list p) dest)
  updateCdtList fun list => Function.update list untyped ([dest] ++ list untyped)

/-- l4v: Deterministic_A.next_revoke_cap. -/
def nextRevokeCap (slot : CslotPtr) (ext : DetState) : CslotPtr := the (nextChild slot (cdtList ext))

/-- l4v: Deterministic_A.free_asid_select. -/
def freeAsidSelect {α : Type} (asidTable : AsidHighIndex → Option α) : AsidHighIndex :=
  (the ((assocs asidTable).filter fun (x, y) =>
    decide (x ≤ 2 ^ asidHighBits - 1 ∧ y = none)).head?).1

/-- l4v: Deterministic_A.free_asid_pool_select. -/
def freeAsidPoolSelect {α : Type} (pool : AsidLowIndex → Option α) (base : Asid) : AsidLowIndex :=
  (the ((assocs pool).filter fun (x, y) =>
    decide (ucast 64 x + base ≠ 0 ∧ y = none)).head?).1

/-- l4v: Deterministic_A.update_work_units. -/
def updateWorkUnits : NonDet DetState Unit :=
  NonDet.modify fun s => workUnitsCompletedUpdate (fun _ => workUnitsCompleted s + 1) s

/-- l4v: Deterministic_A.reset_work_units. -/
def resetWorkUnits : NonDet DetState Unit :=
  NonDet.modify fun s => workUnitsCompletedUpdate (fun _ => 0) s

/-- l4v: Deterministic_A.work_units_limit_reached. -/
def workUnitsLimitReached : NonDet DetState Bool := do
  let workUnits ← NonDet.gets workUnitsCompleted
  return decide (workUnitsLimit ≤ workUnits)

section
variable {Z : Type} [StateExt Z]

/-- l4v: Deterministic_A.OR_choice: run an extended operation on the
extended state, without changing it, to choose between two computations. -/
def orChoice {α : Type} (c : DetExtMonad Bool) (f g : NonDet (State Z) α) : NonDet (State Z) α := do
  let ex ← NonDet.get
  let (rv, _) ← NonDet.selectF (NonDet.mkEf (StateExt.wrapExtBool c ex))
  if rv then f else g

/-- l4v: Deterministic_A.OR_choiceE. -/
def orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Z) ε α) :
    NonDetE (State Z) ε α := do
  let ex ← NonDetE.liftE NonDet.get
  let (rv, _) ← NonDetE.liftE (NonDet.selectF (NonDet.mkEf (StateExt.wrapExtBool c ex)))
  if rv then f else g

/-- l4v: Deterministic_A.do_extended_op: run an extended operation to
update the extended state, ignoring its result. -/
def doExtendedOp (eop : DetExtMonad Unit) : NonDet (State Z) Unit := do
  let ex ← NonDet.get
  let (_, es') ← NonDet.selectF (NonDet.mkEf (StateExt.wrapExtOp eop ex))
  NonDet.modify fun state => { state with exst := es'.exst }

/-- l4v: Deterministic_A.select_ext: choose from `S` with the extended state
when `select_switch` holds, otherwise any element of `S`. -/
def selectExt {D : Type} (a : State DetExt → D) (S : Set D) : NonDet (State Z) D := do
  let s ← NonDet.get
  let x ← if StateExt.selectSwitch s.exst
          then NonDet.pure (a (StateExt.unwrapExt s))
          else NonDet.select S
  NonDet.assert (x ∈ S)
  return x

end

/-- l4v: Deterministic_A.valid_list_2. -/
def validList2 (t : CdtList) (m : Cdt) : Prop :=
  (∀ p, {c | c ∈ t p} = {c | m c = some p}) ∧ (∀ p, (t p).Nodup)

/-- l4v: Deterministic_A.valid_list (`abbreviation`). -/
abbrev validList (s : DetState) : Prop := validList2 (cdtList s) s.cdt

/-! ## Exceptions_A -/

/-- l4v: Exceptions_A.s_monad: the kernel monad without faults, interrupts
or errors. -/
abbrev SMonad (Z α : Type) := NonDet (State Z) α

/-- l4v: Exceptions_A.f_monad: may throw a fault, usually reported to the
current thread's fault handler. -/
abbrev FMonad (Z α : Type) := NonDetE (State Z) Fault α

/-- l4v: Exceptions_A.se_monad: may throw a system call error, usually
reported to the current thread as the system call result. -/
abbrev SEMonad (Z α : Type) := NonDetE (State Z) SyscallError α

/-- l4v: Exceptions_A.lf_monad: may throw a lookup failure. -/
abbrev LFMonad (Z α : Type) := NonDetE (State Z) LookupFailure α

/-- l4v: Exceptions_A.p_monad: the preemption monad, may throw an interrupt
exception. -/
abbrev PMonad (Z α : Type) := NonDetE (State Z) Unit α

section
variable {Z : Type} [StateExt Z]

/-- l4v: Exceptions_A.without_preemption. -/
def withoutPreemption {α : Type} (m : SMonad Z α) : PMonad Z α := NonDetE.liftE m

/-- l4v: Exceptions_A.cap_fault_on_failure. -/
def capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Z α) : FMonad Z α :=
  NonDetE.handleE m (NonDetE.throwError ∘ Fault.capFault cptr rp)

/-- l4v: Exceptions_A.lookup_error_on_failure. -/
def lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Z α) : SEMonad Z α :=
  NonDetE.handleE m (NonDetE.throwError ∘ SyscallError.failedLookup s)

/-- l4v: Exceptions_A.null_cap_on_failure. -/
def nullCapOnFailure (m : LFMonad Z Cap) : SMonad Z Cap :=
  NonDet.liftM (fun | .error _ => Cap.nullCap | .ok c => c) (ExceptT.run m)

/-- l4v: Exceptions_A.unify_failure. -/
def unifyFailure {F α : Type} (m : NonDetE (State Z) F α) : PMonad Z α :=
  NonDetE.handleE m fun _ => NonDetE.throwError ()

/-- l4v: Exceptions_A.empty_on_failure. -/
def emptyOnFailure {F α : Type} (m : NonDetE (State Z) F (List α)) : SMonad Z (List α) :=
  NonDetE.catch m fun _ => NonDet.pure []

/-- l4v: Exceptions_A.const_on_failure. -/
def constOnFailure {F α : Type} (c : α) (m : NonDetE (State Z) F α) : SMonad Z α :=
  NonDetE.catch m fun _ => NonDet.pure c

/-- l4v: Exceptions_A.range_check: whether `v` is between `minV` and `maxV`
(inclusive). -/
def rangeCheck (v minV maxV : Word) : SEMonad Z Unit :=
  NonDetE.unlessE (v ≥ minV ∧ v ≤ maxV) (NonDetE.throwError (SyscallError.rangeError minV maxV))

end

end

end Fl4Spec
