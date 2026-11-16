/-
P3 (DESIGN.md §9), IO ports: **the IO port cap at the composite relation**
(`IoXHyp` for `.IoPort`).

* `port_out_perform`: the spec's `Out` access has an outcome changing the
  machine state's rest only (the memory kept).
* `decode_invocation_ioportX`: every label. `Out` from `port_out_refines`
  (the restart, then the port access: a spec-only kernel-state step and the
  arch operation, `ArchIrqStep`), the errors and the other labels with the
  state unchanged; `In` named (`PortInXHyp`): FL4 sets the thread
  `Running` after the access, so its statement is the replying shape
  (`DecOKRMX`), which needs `XTopAt` across `set_thread_state Running` of the
  current thread (an analogue of VSpace's `restart_top`) and, when called,
  the reply's words (`PortInCallHypM`).
-/
import Fl4Proofs.P3.XTopCaps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
open Fl4Spec

theorem mol_ex' (f : MachineRestMonad Unit) (ms : MachineState) :
    ∃ ms', ms'.underlyingMemory = ms.underlyingMemory ∧ ((), ms') ∈ (machineOpLift f ms).1 := by
  obtain ⟨mr', h⟩ := ign_ex f ms.machineStateRest
  refine ⟨{ ms with machineStateRest := mr' }, rfl, ?_⟩
  unfold machineOpLift machineRestLift
  refine mem_bind_nd (x := (ms.machineStateRest, ms)) rfl ?_
  refine mem_bind_nd (x := (((), mr'), ms)) ⟨h, rfl⟩ ?_
  refine mem_bind_nd (x := ((), { ms with machineStateRest := mr' })) (by rfl) ?_
  rfl

/-- **The spec's `Out` access has an outcome**, the memory kept. -/
theorem port_out_perform (σ : State Unit) (port : IoPort) (raw : Data) (n : Nat) :
    ∃ ms : MachineState, ms.underlyingMemory = σ.machineState.underlyingMemory ∧
      (.ok [], { σ with machineState := ms }) ∈
        ((archPerformInvocation (Z := Unit) (.invokeIOPort (.ioPortInvocation port (outData raw n)))).run σ).1 := by
  have key : ∃ ms : MachineState, ms.underlyingMemory = σ.machineState.underlyingMemory ∧
      (([] : List Data), { σ with machineState := ms }) ∈
        (performIoPortInvocation (Z := Unit) (.ioPortInvocation port (outData raw n)) σ).1 := by
    unfold outData
    split
    · obtain ⟨ms, hu, h⟩ := mol_ex' (out8Impl port (ucast 8 raw)) σ.machineState
      exact ⟨ms, hu, mem_bind_nd (dmo_ex _ σ h) rfl⟩
    · obtain ⟨ms, hu, h⟩ := mol_ex' (out16Impl port (ucast 16 raw)) σ.machineState
      exact ⟨ms, hu, mem_bind_nd (dmo_ex _ σ h) rfl⟩
    · obtain ⟨ms, hu, h⟩ := mol_ex' (out32Impl port (ucast 32 raw)) σ.machineState
      exact ⟨ms, hu, mem_bind_nd (dmo_ex _ σ h) rfl⟩
  obtain ⟨ms, hu, h⟩ := key
  refine ⟨ms, hu, ?_⟩
  unfold archPerformInvocation NonDetE.liftE
  rw [ExceptT.run_lift]
  exact mem_bind_nd h rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **Hypothesis: the IO port cap's `In` labels at `XTop`** (module
docstring). -/
def PortInXHyp (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64)
    (first last : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop :=
  XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot (.IoPort first last 0#u64) blk call don fp buf extra
    slbl args ci sl excaps buffer ct

/-- **`IoXHyp` for the IO port cap**: `Out`, the errors and the other
labels proved; `In` from `PortInXHyp`. Beyond `port_out_refines`'
hypotheses, `XTopAt` at its typed heap, `KsApart`, the current thread
runnable, the typed heap's TCBs in `Z.T`, `ARMask` and `XDelNtfnHyp`. -/
theorem decode_invocation_ioportX {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR)
    (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : PortLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (first last : U64) (hfl : first.val ≤ last.val) (hl16 : last.val < 65536) (call : Bool)
    (hout : ∀ (a : A) p z d, ∃ a', arI.port_out a p z d = ok a')
    {Z : XSets} (hth : Z.th = th) (hX0 : XTopAt (L := L) AR Z s ar σ)
    (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ) (hTh : ∀ t, th t = some .tcb → t ∈ Z.T)
    (hDel : XDelNtfnHyp (L := L) arI AR th)
    (slot : U64) (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hIn : 64 ≤ lbl.val ∧ lbl.val ≤ 66 → PortInXHyp (L := L) arI AR s ar σ lbl length slot first last blk call don fp
      buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot (.IoPort first last 0#u64) blk call don fp buf extra
      slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  by_cases hI : 64 ≤ lbl.val ∧ lbl.val ≤ 66
  · exact hIn hI
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  obtain ⟨-, hlO, hlX⟩ := hlbl
  have herr : ∀ {Q : Fl4Spec.ArchInvocation → S → A → Prop} (res : core.result.Result Unit error.Exc × S × A),
      (∀ inv s' a', (Fl4Spec.decodePortInvocation (Z := Unit) slbl (args.map UScalar.bv)
          (.ioPortCap (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val))).run σ = ({(.ok inv, σ)}, False) →
        Q inv s' a' → TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don
          (specDec fp slbl (args.map UScalar.bv) ci sl (.IoPort first last 0#u64) excaps buffer) s
          (.Ok (), s', a')) →
      PortPost σ (Fl4Spec.decodePortInvocation slbl (args.map UScalar.bv)
        (.ioPortCap (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val))) s ar Q res →
      TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don
        (specDec fp slbl (args.map UScalar.bv) ci sl (.IoPort first last 0#u64) excaps buffer) s res := by
    intro Q res hok h
    obtain ⟨r, s', a'⟩ := res
    cases r with
    | Err e =>
      obtain ⟨rfl, rfl, e', h1, h2⟩ := h
      exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err (run_liftME_err h1), h2⟩, ⟨Z, hX0⟩⟩
    | Ok u => obtain ⟨inv, hrun, hq⟩ := h; exact hok inv s' a' hrun hq
  by_cases hO : 67 ≤ lbl.val ∧ lbl.val ≤ 69
  · refine WP.spec_mono (port_out_refines arI th hP s ar σ lbl hO slbl (hlO hO) length buf ct hct args
      hlen hargs htcb hact first last hfl hl16 call hout) fun res h => herr res (fun inv s' a' hrun hq => ?_) h
    obtain ⟨port, data, raw, -, -, rfl, ha1, -, hr1⟩ := hq
    obtain ⟨x, hk, -⟩ := hX0.rel.2.1.1.tcb ct (by rw [hth]; exact htcb)
    set σ1 := Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv with hσ1
    have hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) := by
      rw [hcur, Notif.setThreadState_eq .restart hk]
    obtain ⟨ms, hu, hmem⟩ := port_out_perform σ1 (BitVec.ofNat 16 port.val) raw.bv (portSz lbl)
    have hstp : Steps (L := L) arI th s ar σ s' a' { σ1 with machineState := ms } :=
      (Steps.restart arI hcur hk htcb hr1 hst hC).trans arI
        ((Steps.ksSpec arI (s := s') (σ := σ1) (σ' := { σ1 with machineState := ms })
          (by constructor <;> first | rfl | exact hu) rfl rfl (fun h => ⟨h.st, h.node⟩) (fun h => h)).trans arI
          (Steps.arch arI (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, ha1⟩)))))))
    obtain ⟨Z', hZ'⟩ := hstp.xtop arI hAM hDel hth hX0 hKA hTh
    exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok (run_liftME_ok hrun)), σ1, hst, (.ok [], { σ1 with machineState := ms }),
      hmem, ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩, hZ'.rel.1, hZ'.rel.2.1, hZ'.rel.2.2.1, hZ'.rel.2.2.2.1,
        hZ'.rel.2.2.2.2.1⟩, ⟨Z', hZ'⟩⟩
  · have hX : lbl.val < 64 ∨ 69 < lbl.val := by omega
    exact WP.spec_mono (port_other_refines arI s ar σ lbl hX slbl (hlX hX) length buf ct hct _ first last call)
      fun res h => herr res (fun _ _ _ _ h => h.elim) h

end

end

end Fl4Proofs.P3
