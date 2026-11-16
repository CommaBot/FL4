/-
P3 (DESIGN.md §9), IPC: **`handle_recv`** (syscall.rs) against l4v's
`handle_recv` (Syscall_A): the cap lookup of the cap register, the rights
checks, the reply cap of `canReply`, the bound-notification check, and the
dispatch to `receive_ipc` / `receive_signal`, or the cap fault through
`handle_fault`, for a relation `Rel` that the leaves keep:

* `RecvLeaves`: `receive_ipc` and `receive_signal` against their spec
  counterparts (the IPC theorems on `IpcRel`, IpcEp*/IpcNtfn*, for the cases
  they cover), the bound TCB of a notification, and `handle_fault` of the
  cap faults;
* `handle_recv_refines`.
-/
import Fl4Proofs.P3.ReplyFailX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section Spec
open Fl4Spec
variable {ε α : Type}

theorem mem_catch_ok {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} {σ σ' : State Unit} {a : α}
    (hx : (.ok a, σ') ∈ (m.run σ).1) : (a, σ') ∈ (NonDetE.catch m h σ).1 :=
  mem_bind_nd hx (Set.mem_singleton _)

theorem mem_catch_err {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} {σ σ' : State Unit} {e : ε}
    {y : α × State Unit} (hx : (.error e, σ') ∈ (m.run σ).1) (hy : y ∈ (h e σ').1) :
    y ∈ (NonDetE.catch m h σ).1 :=
  mem_bind_nd hx hy

theorem mem_throw {β : Type} {σ : State Unit} (e : ε) :
    ((.error e, σ) : Except ε β × State Unit) ∈ ((NonDetE.throwError e : NonDetE (State Unit) ε β).run σ).1 := by
  unfold NonDetE.throwError; rw [ExceptT.run_throw]; rfl

theorem mem_returnOk {β : Type} {σ : State Unit} (b : β) :
    ((.ok b, σ) : Except ε β × State Unit) ∈ ((NonDetE.returnOk b : NonDetE (State Unit) ε β).run σ).1 := by
  unfold NonDetE.returnOk; rw [ExceptT.run_pure]; rfl

theorem mem_getCapReg {σ : State Unit} {x : Tcb} (hk : σ.kheap σ.curThread = some (.tcb x)) (r : Register) :
    (dataToCptr (x.tcbArch.tcbContext.userRegs r), σ) ∈ (getCapReg (Z := Unit) r σ).1 := by
  unfold getCapReg
  refine mem_bind_nd (x := (σ.curThread, σ)) rfl ?_
  unfold NonDet.liftM
  exact mem_bind_nd (x := (x.tcbArch.tcbContext.userRegs r, σ)) (by rw [Endp.asUser_getRegister_eq hk]; rfl) rfl

/-- The cap-fault wrapper of a lookup with a single outcome. -/
theorem mem_capFault_ok {β : Type} {m : LFMonad Unit β} {σ : State Unit} {c : ObjRef} {rp : Bool} {b : β}
    (h : m.run σ = ({(.ok b, σ)}, False)) :
    ((.ok b, σ) : Except Fault β × State Unit) ∈ ((capFaultOnFailure (Z := Unit) c rp m).run σ).1 := by
  unfold capFaultOnFailure; rw [run_handleE_ok h]; rfl

theorem mem_capFault_err {β : Type} {m : LFMonad Unit β} {σ : State Unit} {c : ObjRef} {rp : Bool}
    {lf : LookupFailure} (h : m.run σ = ({(.error lf, σ)}, False)) :
    ((.error (.capFault c rp lf), σ) : Except Fault β × State Unit) ∈
      ((capFaultOnFailure (Z := Unit) c rp m).run σ).1 := by
  unfold capFaultOnFailure; rw [run_handleE_err h]; exact mem_throw _

/-- The body of `handle_recv` (Syscall_A), inside its `catch`. -/
def hrBody (isBlocking canReply : Bool) (thread : ObjRef) (epCptr : CapRef) : FMonad Unit Unit := do
  let epCap ← capFaultOnFailure (ofBl epCptr) true (lookupCap thread epCptr)
  let flt : FMonad Unit Unit :=
    NonDetE.throwError <| .capFault (ofBl epCptr) true (.missingCapability 0)
  match epCap with
  | .endpointCap _ref _badge rights =>
    if AllowRecv ∈ rights
    then do
      let replyCap ← if canReply then lookupReply else NonDetE.returnOk .nullCap
      NonDetE.liftE <| receiveIpc thread epCap isBlocking replyCap
    else flt
  | .notificationCap ref _badge rights =>
    (if AllowRecv ∈ rights
     then do
       let boundTCB ← NonDetE.liftE <| getNtfnObjRef Notification.ntfnBoundTcb ref
       if boundTCB = some thread ∨ boundTCB = none
       then NonDetE.liftE <| receiveSignal thread epCap isBlocking
       else flt
     else flt)
  | _ => flt

theorem handleRecv_mem {σ : State Unit} {x : Tcb} (hk : σ.kheap σ.curThread = some (.tcb x)) (isBlocking canReply : Bool)
    {y : Unit × State Unit}
    (h : y ∈ (NonDetE.catch (hrBody isBlocking canReply σ.curThread (dataToCptr (x.tcbArch.tcbContext.userRegs cap_register)))
      (handleFault σ.curThread) σ).1) : y ∈ (handleRecv (Z := Unit) isBlocking canReply σ).1 := by
  unfold handleRecv
  refine mem_bind_nd (x := (σ.curThread, σ)) rfl ?_
  refine mem_bind_nd (x := (dataToCptr (x.tcbArch.tcbContext.userRegs cap_register), σ)) ?_ h
  unfold NonDet.liftM
  exact mem_bind_nd (x := (x.tcbArch.tcbContext.userRegs cap_register, σ)) (by rw [Endp.asUser_getRegister_eq hk]; rfl) rfl

/-- `lookup_reply` with the reply register's cap. -/
theorem mem_lookupReply_ok {σ : State Unit} {x : Tcb} (hk : σ.kheap σ.curThread = some (.tcb x)) {rc : Cap}
    (hl : (lookupCap (Z := Unit) σ.curThread (dataToCptr (x.tcbArch.tcbContext.userRegs replyRegister))).run σ =
      ({(.ok rc, σ)}, False)) (hr : isReplyCap rc = true) :
    ((.ok rc, σ) : Except Fault Cap × State Unit) ∈ ((lookupReply (Z := Unit)).run σ).1 := by
  unfold lookupReply
  refine mem_bindE_ok (a := dataToCptr (x.tcbArch.tcbContext.userRegs replyRegister)) (s' := σ)
    (mem_liftE (mem_getCapReg hk _)) ?_
  refine mem_bindE_ok (a := σ.curThread) (s' := σ) (mem_liftE (x := (σ.curThread, σ)) rfl) ?_
  refine mem_bindE_ok (mem_capFault_ok hl) ?_
  rw [if_pos hr]; exact mem_returnOk _

theorem mem_lookupReply_err {σ : State Unit} {x : Tcb} (hk : σ.kheap σ.curThread = some (.tcb x)) {f : Fault}
    (h : ((.error f, σ) : Except Fault Cap × State Unit) ∈
      ((capFaultOnFailure (Z := Unit) (ofBl (dataToCptr (x.tcbArch.tcbContext.userRegs replyRegister))) true
        (lookupCap σ.curThread (dataToCptr (x.tcbArch.tcbContext.userRegs replyRegister)))).run σ).1 ∨
      ∃ rc, (lookupCap (Z := Unit) σ.curThread (dataToCptr (x.tcbArch.tcbContext.userRegs replyRegister))).run σ =
        ({(.ok rc, σ)}, False) ∧ isReplyCap rc = false ∧
        f = .capFault (ofBl (dataToCptr (x.tcbArch.tcbContext.userRegs replyRegister))) true (.missingCapability 0)) :
    ((.error f, σ) : Except Fault Cap × State Unit) ∈ ((lookupReply (Z := Unit)).run σ).1 := by
  unfold lookupReply
  refine mem_bindE_ok (a := dataToCptr (x.tcbArch.tcbContext.userRegs replyRegister)) (s' := σ)
    (mem_liftE (mem_getCapReg hk _)) ?_
  refine mem_bindE_ok (a := σ.curThread) (s' := σ) (mem_liftE (x := (σ.curThread, σ)) rfl) ?_
  rcases h with h | ⟨rc, hl, hr, rfl⟩
  · exact mem_bindE_err h
  · refine mem_bindE_ok (mem_capFault_ok hl) ?_
    rw [if_neg (by simp [hr])]; exact mem_throw _

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : P1.LawfulStore st]

/-- **The leaves of `handle_recv`** at `(s, a, σ)`, for a relation `Rel`. -/
structure RecvLeaves (Rel : S → A → Fl4Spec.State Unit → Prop) (ct : U64) (blocking : Bool) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  /-- `receive_ipc` on a related endpoint cap with the receive right, with no
  reply cap or a related reply cap. -/
  ipc : ∀ c ac rc rc', CapRel c ac → ((rc = .Null ∧ rc' = .nullCap) ∨ (CapRel rc rc' ∧ ∃ p g, rc = .Reply p g)) →
    endpoint.receive_ipc st ar s a ct c blocking rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv ac blocking rc' σ).1, Rel r.1 r.2 z.2 ⦄
  /-- `receive_signal` on a related notification cap. -/
  sig : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac →
    notification.receive_signal st ar s a ct p blocking ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac blocking σ).1, Rel r.1 r.2 z.2 ⦄
  /-- The bound TCB of a related notification cap's object. -/
  bound : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac →
    Fl4Spec.getNtfnObjRef (Z := Unit) Fl4Spec.Notification.ntfnBoundTcb p.bv σ =
      ({(Notif.optRef (L.mem s (Notif.nBoundA p)), σ)}, False)
  /-- `handle_fault` of a cap fault. -/
  flt : ∀ cptr lf lf', LookupFaultRel lf lf' →
    faults.handle_fault st ar s a ct (.Cap cptr true lf) ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
        Rel r.1 r.2 z.2 ⦄

set_option maxHeartbeats 16000000 in
/-- **FL4's `handle_recv` refines l4v's `handle_recv`** (see the module
docstring), for any relation `Rel` the leaves keep. -/
theorem handle_recv_refines (Rel : S → A → Fl4Spec.State Unit → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (blocking canReply : Bool) (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x))
    (hcapr : (L.mem s (Endp.regA ct layout.reg.CAP)).bv = x.tcbArch.tcbContext.userRegs Fl4Spec.cap_register)
    (hrepr : (L.mem s (Endp.regA ct layout.reg.REPLY)).bv = x.tcbArch.tcbContext.userRegs Fl4Spec.replyRegister)
    (hL : ∀ cptr, cspace.lookup_cap st s ct cptr ⦃ r =>
      Single ((Fl4Spec.lookupCap (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ) σ (CapResRel r) ⦄)
    (hLv : RecvLeaves (st := st) (ar := ar) Rel ct blocking s a σ) :
    syscall.handle_recv st ar s a blocking canReply ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) blocking canReply σ).1, Rel r.1 r.2 z.2 ⦄ := by
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  set cp := L.mem s (Endp.regA ct layout.reg.CAP) with hcpdef
  set rp := L.mem s (Endp.regA ct layout.reg.REPLY) with hrpdef
  have hcp : Fl4Spec.dataToCptr (x.tcbArch.tcbContext.userRegs Fl4Spec.cap_register) = Fl4Spec.toBl cp.bv := by
    rw [← hcapr]; rfl
  have hrp : Fl4Spec.dataToCptr (x.tcbArch.tcbContext.userRegs Fl4Spec.replyRegister) = Fl4Spec.toBl rp.bv := by
    rw [← hrepr]; rfl
  -- the spec side, from the body's outcome
  have top : ∀ (y : Unit × Fl4Spec.State Unit),
      y ∈ (Fl4Spec.NonDetE.catch (hrBody blocking canReply ct.bv (Fl4Spec.toBl cp.bv))
        (Fl4Spec.handleFault ct.bv) σ).1 → y ∈ (Fl4Spec.handleRecv (Z := Unit) blocking canReply σ).1 := by
    intro y hy
    apply handleRecv_mem hk'
    rw [hcp, hcur]; exact hy
  -- a cap fault on the cap register
  have fault' : ∀ (cptr : U64) lf lf', LookupFaultRel lf lf' →
      ((.error (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf'), σ) : Except Fl4Spec.Fault Unit × _) ∈
        ((hrBody blocking canReply ct.bv (Fl4Spec.toBl cp.bv)).run σ).1 →
      syscall.cap_fault_recv st ar s a cptr lf ⦃ r =>
        ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) blocking canReply σ).1, Rel r.1 r.2 z.2 ⦄ := by
    intro cptr lf lf' hlf hb
    unfold syscall.cap_fault_recv
    rw [hct]; simp only [bind_ok]
    exact WP.spec_mono (hLv.flt cptr lf lf' hlf) fun r ⟨z, hz, hR⟩ => ⟨z, top z (mem_catch_err hb hz), hR⟩
  have fault := fault' cp
  have okb : ∀ (y : Unit × Fl4Spec.State Unit), ((.ok y.1, y.2) : Except Fl4Spec.Fault Unit × _) ∈
      ((hrBody blocking canReply ct.bv (Fl4Spec.toBl cp.bv)).run σ).1 →
      y ∈ (Fl4Spec.handleRecv (Z := Unit) blocking canReply σ).1 := fun y hy => top y (mem_catch_ok hy)
  unfold syscall.handle_recv
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 rfl
  refine WP.spec_bind (hL cp) ?_
  rintro r ⟨e, he, hrel⟩
  have hmiss : LookupFaultRel (.MissingCapability 0#u64) (.missingCapability 0) := by simp [LookupFaultRel]
  cases r with
  | Err ex =>
    cases e with
    | ok _ => cases ex <;> exact hrel.elim
    | error lf' =>
      cases ex with
      | Lookup lf =>
        exact fault lf lf' hrel (by unfold hrBody; exact mem_bindE_err (mem_capFault_err he))
      | _ => exact hrel.elim
  | Ok c =>
    cases e with
    | error _ => exact hrel.elim
    | ok ac =>
      have hac := hrel.abs
      subst hac
      have hcf := mem_capFault_ok (c := Fl4Spec.ofBl (Fl4Spec.toBl cp.bv)) (rp := true) he
      cases c
      case Endpoint p b sd rv g gr =>
        have hrights : (Fl4Spec.AllowRecv ∈ rightsOf sd rv g gr) ↔ rv = true := by
          simp [rightsOf, Fl4Spec.AllowRecv]
        cases rv
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact fault _ _ hmiss (by
            unfold hrBody
            exact mem_bindE_ok hcf (by dsimp only [absCap]; rw [if_neg (by rw [hrights]; simp)]; exact mem_throw _))
        simp only [↓reduceIte]
        cases canReply
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine WP.spec_mono (hLv.ipc _ _ .Null .nullCap hrel (Or.inl ⟨rfl, rfl⟩)) fun r ⟨z, hz, hR⟩ => ⟨z, okb z ?_, hR⟩
          unfold hrBody
          refine mem_bindE_ok hcf ?_
          dsimp only [absCap]
          rw [if_pos (hrights.2 rfl)]
          exact mem_bindE_ok (mem_returnOk _) (mem_liftE hz)
        simp only [↓reduceIte]
        refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
        rintro c1 rfl
        refine WP.spec_bind (hL rp) ?_
        rintro r1 ⟨e1, he1, hrel1⟩
        have he1' : (Fl4Spec.lookupCap (Z := Unit) σ.curThread
            (Fl4Spec.dataToCptr (x.tcbArch.tcbContext.userRegs Fl4Spec.replyRegister))).run σ = ({(e1, σ)}, False) := by
          rw [hrp, hcur]; exact he1
        cases r1 with
        | Err ex =>
          cases e1 with
          | ok _ => cases ex <;> exact hrel1.elim
          | error lf' =>
            cases ex with
            | Lookup lf =>
              refine fault' rp lf lf' hrel1 ?_
              unfold hrBody
              refine mem_bindE_ok hcf ?_
              dsimp only [absCap]
              rw [if_pos (hrights.2 rfl)]
              refine mem_bindE_err ?_
              have := mem_lookupReply_err hk' (f := .capFault (Fl4Spec.ofBl (Fl4Spec.toBl rp.bv)) true lf')
                (Or.inl (by rw [hrp]; exact mem_capFault_err (by rw [← hrp]; exact he1')))
              exact this
            | _ => exact hrel1.elim
        | Ok c1 =>
          cases e1 with
          | error _ => exact hrel1.elim
          | ok ac1 =>
            have hac1 := hrel1.abs
            subst hac1
            cases c1
            case Reply rp' g' =>
              refine WP.spec_mono (hLv.ipc _ _ _ _ hrel (Or.inr ⟨hrel1, rp', g', rfl⟩)) fun r ⟨z, hz, hR⟩ =>
                ⟨z, okb z ?_, hR⟩
              unfold hrBody
              refine mem_bindE_ok hcf ?_
              dsimp only [absCap]
              rw [if_pos (hrights.2 rfl)]
              simp only [↓reduceIte]
              exact mem_bindE_ok (mem_lookupReply_ok hk' he1' rfl) (mem_liftE hz)
            all_goals
              refine fault' rp _ _ hmiss ?_
              unfold hrBody
              refine mem_bindE_ok hcf ?_
              dsimp only [absCap]
              rw [if_pos (hrights.2 rfl)]
              refine mem_bindE_err ?_
              have := mem_lookupReply_err hk' (f := .capFault (Fl4Spec.ofBl (Fl4Spec.toBl rp.bv)) true
                (.missingCapability 0)) (Or.inr ⟨_, he1', rfl, by rw [hrp]⟩)
              exact this
      case Notification p b w rd =>
        have hrights : (Fl4Spec.AllowRecv ∈ rightsOf w rd false false) ↔ rd = true := by
          simp [rightsOf, Fl4Spec.AllowRecv]
        refine WP.spec_bind (Notif.obj.Ntfn.bound_tcb.spec s p) ?_
        rintro v rfl
        have hbd := hLv.bound p b w rd _ hrel
        have hmemb : ∀ (bt : Option Fl4Spec.ObjRef), bt = Notif.optRef (L.mem s (Notif.nBoundA p)) →
            ((.ok bt, σ) : Except Fl4Spec.Fault _ × _) ∈ ((Fl4Spec.NonDetE.liftE (ε := Fl4Spec.Fault)
              (Fl4Spec.getNtfnObjRef (Z := Unit) Fl4Spec.Notification.ntfnBoundTcb p.bv)).run σ).1 := by
          rintro bt rfl; exact mem_liftE (x := (_, σ)) (by rw [hbd]; rfl)
        cases rd
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact fault _ _ hmiss (by
            unfold hrBody
            exact mem_bindE_ok hcf (by dsimp only [absCap]; rw [if_neg (by rw [hrights]; simp)]; exact mem_throw _))
        simp only [↓reduceIte]
        have sig : (Notif.optRef (L.mem s (Notif.nBoundA p)) = some ct.bv ∨
            Notif.optRef (L.mem s (Notif.nBoundA p)) = none) →
            notification.receive_signal st ar s a ct p blocking ⦃ r =>
              ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) blocking canReply σ).1, Rel r.1 r.2 z.2 ⦄ := by
          intro hok
          refine WP.spec_mono (hLv.sig p b w true _ hrel) fun r ⟨z, hz, hR⟩ => ⟨z, okb z ?_, hR⟩
          unfold hrBody
          refine mem_bindE_ok hcf ?_
          dsimp only [absCap]
          rw [if_pos (hrights.2 rfl)]
          refine mem_bindE_ok (hmemb _ rfl) ?_
          rw [if_pos hok]
          exact mem_liftE hz
        by_cases h0 : L.mem s (Notif.nBoundA p) = 0#u64
        · simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          rw [h0] at sig; exact sig (Or.inr Notif.optRef_zero)
        · have hb0 : (L.mem s (Notif.nBoundA p) != 0#u64) = true := by simp [h0]
          simp only [hb0, ↓reduceIte]
          by_cases ht : L.mem s (Notif.nBoundA p) = ct
          · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
            exact sig (Or.inl (by rw [Notif.optRef_ne h0, ht]))
          · have hbt : (L.mem s (Notif.nBoundA p) != ct) = true := by simp [ht]
            simp only [hbt, ↓reduceIte]
            exact fault _ _ hmiss (by
              unfold hrBody
              refine mem_bindE_ok hcf ?_
              dsimp only [absCap]
              rw [if_pos (hrights.2 rfl)]
              refine mem_bindE_ok (hmemb _ rfl) ?_
              rw [if_neg (by
                rw [Notif.optRef_ne h0]
                rintro (h | h)
                · exact ht (P1.eq_of_bv (by simpa using h))
                · cases h)]
              exact mem_throw _)
      all_goals
        exact fault _ _ hmiss (by
          unfold hrBody
          exact mem_bindE_ok hcf (by dsimp only [absCap]; exact mem_throw _))

end

end

end Fl4Proofs.P3
