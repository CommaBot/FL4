/-
P3 (DESIGN.md §9), VSpace: **the VSpace caps at the top of
`decode_invocation`** (DecodeTop's `DecOK`, `TopPost`).

* `decode_invocation_pml4`: a PML4 cap, every label, against
  `fl4ArchDecodeInvocation` (l4h 0017 `X86PML4Flush` to `decodePml4Flush`,
  every other label l4v's `IllegalOperation`): the flush restarts the
  thread and flushes (`flushAll`, machine state only), no slot changes, so
  the CSpace relation, `MdbInv` and `FinInv` carry over (as DecodeTop's
  port caps).
-/
import Fl4Proofs.P3.DecodeTop
import Fl4Proofs.P3.VsArch
import Fl4Proofs.P3.TopF
import Fl4Proofs.P3.TopM
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- `top_of_lift2` for `TopPostM`. -/
theorem topM_of_lift2 {α β : Type} {f : α → Fl4Spec.Fl4Invocation} {g : β → α} {m : Fl4Spec.SEMonad Unit β}
    {σ : Fl4Spec.State Unit} {blk call don : Bool} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
      (∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
        ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (f (g inv))).run σ1).1, ∃ th' G',
          ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
          Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
          MdbOK (L.mem res.2.1) G')) :
    TopPostM (L := L) σ blk call don (Fl4Spec.NonDetE.liftME f (Fl4Spec.NonDetE.liftME g m)) s res := by
  rcases h with ⟨e, h1, h2, e', hr, he⟩ | ⟨inv, hr, rest⟩
  · exact Or.inl ⟨e, h1, h2, e', run_liftME_err (run_liftME_err hr), he⟩
  · exact Or.inr ⟨f (g inv), DecOut.of_eq (run_liftME_ok (run_liftME_ok hr)), rest⟩

/-- `top_of_lift2M` for `TopPostM`. -/
theorem topM_of_lift2M {α β : Type} {f : α → Fl4Spec.Fl4Invocation} {g : β → α} {m : Fl4Spec.SEMonad Unit β}
    {σ : Fl4Spec.State Unit} {blk call don : Bool} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
      (∃ inv, DecOut m σ inv ∧ ∃ σ1,
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
        ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (f (g inv))).run σ1).1, ∃ th' G',
          ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
          Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
          MdbOK (L.mem res.2.1) G')) :
    TopPostM (L := L) σ blk call don (Fl4Spec.NonDetE.liftME f (Fl4Spec.NonDetE.liftME g m)) s res := by
  rcases h with ⟨e, h1, h2, e', hr, he⟩ | ⟨inv, hr, rest⟩
  · exact Or.inl ⟨e, h1, h2, e', run_liftME_err (run_liftME_err hr), he⟩
  · exact Or.inr ⟨f (g inv), hr.liftME.liftME, rest⟩

/-- The state after an outcome: unchanged, or one with `Q` (the VSpace
footprint, through the invocations' `SR`). -/
abbrev FootQ (Q : S → Prop) (s : S) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  res.2.1 = s ∨ Q res.2.1

/-- `DecOKM` with `FootQ Q` after. -/
abbrev DecOKMQ (Q : S → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64)
    (c : capability.Cap) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    TopPostM (L := L) σ blk call don (specDec fp slbl args ci sl c excaps buffer) s res ∧ FootQ Q s res ⦄

theorem DecOKMQ.toM {Q : S → Prop} {s : S} {ar : A} {σ : Fl4Spec.State Unit} {lbl length slot : U64}
    {c : capability.Cap} {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef}
    (h : DecOKMQ (L := L) arI Q s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer) :
    DecOKM (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer :=
  WP.spec_mono h fun _ h => h.1

theorem DecOKM.toMQ {s : S} {ar : A} {σ : Fl4Spec.State Unit} {lbl length slot : U64}
    {c : capability.Cap} {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef}
    (h : DecOKM (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer) :
    DecOKMQ (L := L) arI (fun _ => True) s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps
      buffer :=
  WP.spec_mono h fun _ h => ⟨h, Or.inr trivial⟩

/-- An error outcome, the state unchanged. -/
theorem topMQ_err {α β : Type} {f : α → Fl4Spec.Fl4Invocation} {g : β → α} {m : Fl4Spec.SEMonad Unit β}
    {Q : S → Prop} {σ : Fl4Spec.State Unit} {blk call don : Bool} {s : S}
    {res : core.result.Result Unit error.Exc × S × A}
    (h : ∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') :
    TopPostM (L := L) σ blk call don (Fl4Spec.NonDetE.liftME f (Fl4Spec.NonDetE.liftME g m)) s res ∧
      FootQ Q s res := by
  obtain ⟨e, h1, h2, h3⟩ := h
  exact ⟨topM_of_lift2 (Or.inl ⟨e, h1, h2, h3⟩), Or.inl h2⟩

/-- **A PML4 cap** (see the module docstring). -/
theorem decode_invocation_pml4 (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOK (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4Pml4FlushLabel ↔ lbl = fl4_abi.label.X86PML4Flush)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hinv : ∀ (a : A) (asid : U64), ∃ a', arI.invalidate_asid a asid = ok a')
    (p asid : U64) (mp : Bool) (length slot buf : U64) (blk call don fp : Bool)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    DecOKM (L := L) arI s ar σ lbl length slot (.Pml4 p mp asid) blk call don fp buf extra slbl args ci sl excaps
      buffer := by
  unfold DecOKM syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  have hspec : specDec fp slbl args ci sl (.Pml4 p mp asid) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl args ci sl
          (.pml4Cap p.bv (if mp then some asid.bv else none)) excaps) := rfl
  rw [hspec]
  by_cases hl : lbl = fl4_abi.label.X86PML4Flush
  swap
  · rw [if_neg hl]
    have hd : Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl args ci sl
        (.pml4Cap p.bv (if mp then some asid.bv else none)) excaps =
        Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl args ci sl
          (.pml4Cap p.bv (if mp then some asid.bv else none)) excaps) := by
      unfold Fl4Spec.fl4ArchDecodeInvocation; dsimp only; rw [if_neg (fun h => hl (hlbl.1 h))]
    rw [hd]
    simp only [error.illegal, bind_ok, WP.spec_ok]
    exact topM_of_lift2 (Or.inl ⟨_, rfl, rfl, .illegalOperation, rfl, Or.inl trivial⟩)
  rw [if_pos hl]
  have hd : Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl args ci sl
      (.pml4Cap p.bv (if mp then some asid.bv else none)) excaps =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.pml4Flush
        (Fl4Spec.decodePml4Flush (Z := Unit) (.pml4Cap p.bv (if mp then some asid.bv else none))) := by
    unfold Fl4Spec.fl4ArchDecodeInvocation; dsimp only; rw [if_pos (hlbl.2 hl)]
  rw [hd]
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok, WP.spec_ok]
    exact topM_of_lift2 (Or.inl ⟨_, rfl, rfl, .invalidCapability 0, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩)
  simp only [↓reduceIte]
  refine WP.spec_bind (set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact) ?_
  intro s1 hS
  obtain ⟨a', ha'⟩ := hinv ar asid
  rw [ha']; simp only [bind_ok, WP.spec_ok]
  obtain ⟨hR, hV, hM, hC, hI⟩ := hCR
  obtain ⟨tcb, hkt, -⟩ := hR.tcb ct htcb
  obtain ⟨σ1, hst1, hR1, hV1, hM1, hC1, -, -⟩ := restart_rel hR hV hM hC hS (t := ct.bv) hkt .restart
  obtain ⟨-, ⟨⟨u, σ'⟩, hy⟩, h3⟩ := Vs.flushAll_ok p.bv asid.bv σ1
  obtain ⟨ms, e, -⟩ := h3 _ hy
  cases u
  simp only at e
  subst e
  have h0 : (([] : List Fl4Spec.Data), { σ1 with machineState := ms }) ∈
      ((do Fl4Spec.flushAll (Z := Unit) p.bv asid.bv; pure [] : Fl4Spec.SMonad Unit (List Fl4Spec.Data)) σ1).1 :=
    mem_bind_nd (x := ((), { σ1 with machineState := ms })) hy (Set.mem_singleton _)
  have hmem : ((.ok [], { σ1 with machineState := ms }) : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
        (.invokeArchObject (.pml4Flush (.flush p.bv asid.bv)))).run σ1).1 :=
    mem_liftE (ε := Unit) h0
  refine topM_of_lift2 (Or.inr ⟨.flush p.bv asid.bv, rfl, σ1, by rw [hcur]; exact hst1, _, hmem, th, G,
    Or.inl ⟨rfl, [], rfl⟩, hP, ⟨Vs.StateRel.ms hR1 ms, hV1, hM1, hC1.of_cdt rfl rfl, MdbInv.of_same hM hI hS⟩,
    hFI.of_same hM hS ((ksub_of_eq (setThreadState_nks _ _) hst1).trans (KSub.of_kheap rfl)), MdbOK.of_same hM hS hMO⟩)

end

end

end Fl4Proofs.P3
