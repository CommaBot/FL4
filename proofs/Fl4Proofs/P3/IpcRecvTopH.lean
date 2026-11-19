/-
P3 (DESIGN.md §9), IPC: IpcRecvTop's `handle_recv_refines` with the looked-up
caps' extra property `Hd` passed to the receive leaves (`RecvLeavesH`,
`handle_recv_refinesH`; at `J`: the cap is held in a slot, so its object is
covered and leaves the dead set when a receive blocks on it). A copy of
IpcRecvTop's proof (IpcRecvTop has ~290 dependents).
-/
import Fl4Proofs.P3.IpcRecvTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : P1.LawfulStore st]

/-- **The leaves of `handle_recv`** at `(s, a, σ)`, for a relation `Rel`. -/
structure RecvLeavesH (Hd : capability.Cap → Prop) (Rel : S → A → Fl4Spec.State Unit → Prop) (ct : U64) (blocking : Bool) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  /-- `receive_ipc` on an endpoint cap with the receive right whose endpoint
  exists, with no reply cap or a related reply cap whose reply exists. -/
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    Hd (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → Hd rc) →
    endpoint.receive_ipc st ar s a ct (.Endpoint p b sd true g gr) blocking rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking rc' σ).1,
        Rel r.1 r.2 z.2 ⦄
  /-- `receive_signal` on a related notification cap. -/
  sig : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
    Hd (.Notification p b w rd) →
    notification.receive_signal st ar s a ct p blocking ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac blocking σ).1, Rel r.1 r.2 z.2 ⦄
  /-- The bound TCB of a related notification cap's object. -/
  bound : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
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
theorem handle_recv_refinesH (Rel : S → A → Fl4Spec.State Unit → Prop) (Hd : capability.Cap → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (blocking canReply : Bool) (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x))
    (hcapr : (L.mem s (Endp.regA ct layout.reg.CAP)).bv = x.tcbArch.tcbContext.userRegs Fl4Spec.cap_register)
    (hrepr : (L.mem s (Endp.regA ct layout.reg.REPLY)).bv = x.tcbArch.tcbContext.userRegs Fl4Spec.replyRegister)
    (hL : ∀ cptr, cspace.lookup_cap st s ct cptr ⦃ r =>
      Single ((Fl4Spec.lookupCap (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ) σ (CapResRel r) ⦄)
    (hObj : ∀ cptr, cspace.lookup_cap st s ct cptr ⦃ r => ∀ c, r = .Ok c → CapObjE σ c ∧ Hd c ⦄)
    (hLv : RecvLeavesH (st := st) (ar := ar) Hd Rel ct blocking s a σ) :
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
  refine WP.spec_bind (WP.spec_and (hL cp) (hObj cp)) ?_
  rintro r ⟨⟨e, he, hrel⟩, hob⟩
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
          refine WP.spec_mono (hLv.ipc p b sd g gr .Null .nullCap (hob _ rfl).1 (Or.inl ⟨rfl, rfl⟩) (hob _ rfl).2
            (fun _ _ h => by cases h)) fun r ⟨z, hz, hR⟩ =>
            ⟨z, okb z ?_, hR⟩
          unfold hrBody
          refine mem_bindE_ok hcf ?_
          dsimp only [absCap]
          rw [if_pos (hrights.2 rfl)]
          exact mem_bindE_ok (mem_returnOk _) (mem_liftE hz)
        simp only [↓reduceIte]
        refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
        rintro c1 rfl
        refine WP.spec_bind (WP.spec_and (hL rp) (hObj rp)) ?_
        rintro r1 ⟨⟨e1, he1, hrel1⟩, hob1⟩
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
              refine WP.spec_mono (hLv.ipc p b sd g gr _ _ (hob _ rfl).1 (Or.inr ⟨hrel1, rp', g', rfl, (hob1 _ rfl).1⟩) (hob _ rfl).2
                (fun _ _ _ => (hob1 _ rfl).2))
                fun r ⟨z, hz, hR⟩ =>
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
        have hbd := hLv.bound p b w rd _ hrel (hob _ rfl).1
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
          refine WP.spec_mono (hLv.sig p b w true _ hrel (hob _ rfl).1 (hob _ rfl).2) fun r ⟨z, hz, hR⟩ => ⟨z, okb z ?_, hR⟩
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
