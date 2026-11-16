/-
P3 (DESIGN.md §9), TCB invocations: **the Thread cap at the composite
relation** (TopXAll's `TcbXHyp`, the `XCap` of a Thread cap), for any
relation `X` kept by the decode's failure.

* `TcbOKX`, `TcbOKRX`: `tcb::decode` at one label against the spec, keeping
  `X` (`TopPostDMX`; `TopPostRMX` for the labels whose spec result is data
  and whose decode replies itself: ReadRegisters, GetBreakpoint,
  ConfigureSingleStepping, SetFlags).
* `TcbXLeaves`: one such statement per FL4 TCB label (the per-label leaves,
  for the subsystems' proofs).
* `decode_invocation_threadX`: the Thread cap's `XCap` at every label, from
  its leaf; every other label the spec's `IllegalOperation` (proved, the
  state unchanged).
-/
import Fl4Proofs.P3.XTopCnodeAll
import Fl4Proofs.P3.TcbExt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- `tcb::decode` at one label keeping `X` (`TopPostDMX`). -/
abbrev TcbOKX (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl : U64)
    (p : U64) (c : tcb.Ctx) (blk call don : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) : Prop :=
  tcb.decode st arI s ar lbl p c ⦃ res =>
    TopPostDMX (L := L) X σ blk call don (specDec false slbl args ci sl (.Thread p) excaps buffer) s res ⦄

/-- `tcb::decode` at a label replying itself, keeping `X` (`TopPostRMX`). -/
abbrev TcbOKRX (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl : U64)
    (p : U64) (c : tcb.Ctx) (blk call don : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop :=
  tcb.decode st arI s ar lbl p c ⦃ res =>
    TopPostRMX (L := L) X σ blk call don (specDec false slbl args ci sl (.Thread p) excaps buffer) ct s res ⦄

/-- **The per-label leaves of the Thread cap at `X`**: for each FL4 TCB
label, `tcb::decode` at that label keeps `X` (named premises, one per label,
for the subsystems' proofs: the CSpace labels SetTimeoutEndpoint,
SetIPCBuffer, SetSpace and Configure's installs; the scheduler's
SetPriority, SetMCPriority, SetSchedParams, Configure's scheduling part,
SetTLSBase's reschedule; the IPC side's Suspend, Resume, Bind/Unbind
Notification, Read/Write/CopyRegisters; FL4's debug and l4h labels). -/
structure TcbXLeaves (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (p : U64) (c : tcb.Ctx) (blk call don : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop where
  readRegisters : lbl = fl4_abi.label.TCBReadRegisters →
    TcbOKRX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer ct
  writeRegisters : lbl = fl4_abi.label.TCBWriteRegisters →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  copyRegisters : lbl = fl4_abi.label.TCBCopyRegisters →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  configure : lbl = fl4_abi.label.TCBConfigure →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setPriority : lbl = fl4_abi.label.TCBSetPriority →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setMCPriority : lbl = fl4_abi.label.TCBSetMCPriority →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setSchedParams : lbl = fl4_abi.label.TCBSetSchedParams →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setTimeoutEndpoint : lbl = fl4_abi.label.TCBSetTimeoutEndpoint →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setIPCBuffer : lbl = fl4_abi.label.TCBSetIPCBuffer →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setSpace : lbl = fl4_abi.label.TCBSetSpace →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  suspend : lbl = fl4_abi.label.TCBSuspend →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  resume : lbl = fl4_abi.label.TCBResume →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  bindNotification : lbl = fl4_abi.label.TCBBindNotification →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  unbindNotification : lbl = fl4_abi.label.TCBUnbindNotification →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setBreakpoint : lbl = fl4_abi.label.TCBSetBreakpoint →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  getBreakpoint : lbl = fl4_abi.label.TCBGetBreakpoint →
    TcbOKRX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer ct
  unsetBreakpoint : lbl = fl4_abi.label.TCBUnsetBreakpoint →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  configureSingleStepping : lbl = fl4_abi.label.TCBConfigureSingleStepping →
    TcbOKRX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer ct
  setTLSBase : lbl = fl4_abi.label.TCBSetTLSBase →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setFlags : lbl = fl4_abi.label.TCBSetFlags →
    TcbOKRX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer ct
  readFPU : lbl = fl4_abi.label.TCBReadFPU →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  writeFPU : lbl = fl4_abi.label.TCBWriteFPU →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setTimer : lbl = fl4_abi.label.TCBSetTimer →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer

/-- `tcb::decode` at a label of no FL4 TCB invocation: the spec's
`IllegalOperation`, the state unchanged, `X` kept. -/
theorem tcb_illegalX {X : S → A → Fl4Spec.State Unit → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX0 : X s ar σ) (lbl p : U64) (c : tcb.Ctx)
    (blk call don : Bool) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hlo : ¬ (2 ≤ lbl.val ∧ lbl.val ≤ 24)) :
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer := by
  have h2 : lbl.val ≠ 2 := by omega
  have h3 : lbl.val ≠ 3 := by omega
  have h4 : lbl.val ≠ 4 := by omega
  have h5 : lbl.val ≠ 5 := by omega
  have h6 : lbl.val ≠ 6 := by omega
  have h7 : lbl.val ≠ 7 := by omega
  have h8 : lbl.val ≠ 8 := by omega
  have h9 : lbl.val ≠ 9 := by omega
  have h10 : lbl.val ≠ 10 := by omega
  have h11 : lbl.val ≠ 11 := by omega
  have h12 : lbl.val ≠ 12 := by omega
  have h13 : lbl.val ≠ 13 := by omega
  have h14 : lbl.val ≠ 14 := by omega
  have h15 : lbl.val ≠ 15 := by omega
  have h16 : lbl.val ≠ 16 := by omega
  have h17 : lbl.val ≠ 17 := by omega
  have h18 : lbl.val ≠ 18 := by omega
  have h19 : lbl.val ≠ 19 := by omega
  have h20 : lbl.val ≠ 20 := by omega
  have h21 : lbl.val ≠ 21 := by omega
  have h22 : lbl.val ≠ 22 := by omega
  have h23 : lbl.val ≠ 23 := by omega
  have h24 : lbl.val ≠ 24 := by omega
  have hg : Fl4Spec.genInvocationType slbl = .invalidInvocation := by
    rw [hlbl]; simp [tcbLabelOf, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
  unfold TcbOKX tcb.decode
  rw [hstall]
  simp only [hNative, ↓reduceIte]
  simp only [bind_ok, u64_eq_iff, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val, lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val, lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val, lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val, lbl_tcbSetBreakpoint_val, lbl_tcbGetBreakpoint_val, lbl_tcbUnsetBreakpoint_val, lbl_tcbConfigureSingleStepping_val, lbl_tcbSetTLSBase_val, lbl_tcbSetFlags_val, lbl_tcbReadFPU_val, lbl_tcbWriteFPU_val, lbl_tcbSetTimer_val,
    h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, ↓reduceIte]
  refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hX0⟩)
  show (Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer).run σ = _
  rw [fl4DecodeTcb_spec' (by rw [hg]; decide) (by rw [hext hg]; simp [tcbExtOf, h16, h17, h18, h19, h22, h23, h24])]
  apply run_liftME_err
  unfold Fl4Spec.decodeTcbInvocation
  rw [hg]
  rfl

/-- **`TcbXHyp`: the Thread cap's `XCap` at `X`, every label**, from its
leaf (`TcbXLeaves`); the labels of no TCB invocation are the spec's
`IllegalOperation` (`tcb_illegalX`). Beyond the leaves: `X` at the start,
the stall of the target a no-op (`hstall`), the label not SetEPTRoot
(outside the native statements, `hNative`), the extension label (`hext`). -/
theorem decode_invocation_threadX {X : S → A → Fl4Spec.State Unit → Prop} (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (hX0 : X s ar σ) (lbl length slot : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hT : TcbXLeaves (L := L) arI X s ar σ lbl p ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl
      excaps buffer ct) :
    XCap (L := L) arI X s ar σ lbl length slot (.Thread p) blk call don fp buf extra slbl args ci sl excaps buffer
      ct := by
  have eq : ∀ {n : Nat} {l : U64}, l.val = n → lbl.val = n → lbl = l := fun h1 h2 =>
    UScalar.eq_of_val_eq (by rw [h1, h2])
  by_cases hR : lbl.val = 2 ∨ lbl.val = 17 ∨ lbl.val = 19 ∨ lbl.val = 21
  · right
    unfold DecOKRMX syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    cases fp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases hR with h | h | h | h
      · exact hT.readRegisters (eq lbl_tcbReadRegisters_val h)
      · exact hT.getBreakpoint (eq lbl_tcbGetBreakpoint_val h)
      · exact hT.configureSingleStepping (eq lbl_tcbConfigureSingleStepping_val h)
      · exact hT.setFlags (eq lbl_tcbSetFlags_val h)
    · simp only [↓reduceIte]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hin : 2 ≤ lbl.val ∧ lbl.val ≤ 24
    · have hc : lbl.val = 3 ∨ lbl.val = 4 ∨ lbl.val = 5 ∨ lbl.val = 6 ∨ lbl.val = 7 ∨ lbl.val = 8 ∨
          lbl.val = 9 ∨ lbl.val = 10 ∨ lbl.val = 11 ∨ lbl.val = 12 ∨ lbl.val = 13 ∨ lbl.val = 14 ∨
          lbl.val = 15 ∨ lbl.val = 16 ∨ lbl.val = 18 ∨ lbl.val = 20 ∨ lbl.val = 22 ∨ lbl.val = 23 ∨
          lbl.val = 24 := by omega
      rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact hT.writeRegisters (eq lbl_tcbWriteRegisters_val h)
      · exact hT.copyRegisters (eq lbl_tcbCopyRegisters_val h)
      · exact hT.configure (eq lbl_tcbConfigure_val h)
      · exact hT.setPriority (eq lbl_tcbSetPriority_val h)
      · exact hT.setMCPriority (eq lbl_tcbSetMCPriority_val h)
      · exact hT.setSchedParams (eq lbl_tcbSetSchedParams_val h)
      · exact hT.setTimeoutEndpoint (eq lbl_tcbSetTimeoutEndpoint_val h)
      · exact hT.setIPCBuffer (eq lbl_tcbSetIPCBuffer_val h)
      · exact hT.setSpace (eq lbl_tcbSetSpace_val h)
      · exact hT.suspend (eq lbl_tcbSuspend_val h)
      · exact hT.resume (eq lbl_tcbResume_val h)
      · exact hT.bindNotification (eq lbl_tcbBindNotification_val h)
      · exact hT.unbindNotification (eq lbl_tcbUnbindNotification_val h)
      · exact hT.setBreakpoint (eq lbl_tcbSetBreakpoint_val h)
      · exact hT.unsetBreakpoint (eq lbl_tcbUnsetBreakpoint_val h)
      · exact hT.setTLSBase (eq lbl_tcbSetTLSBase_val h)
      · exact hT.readFPU (eq lbl_tcbReadFPU_val h)
      · exact hT.writeFPU (eq lbl_tcbWriteFPU_val h)
      · exact hT.setTimer (eq lbl_tcbSetTimer_val h)
    · exact tcb_illegalX arI s ar σ hX0 lbl p _ blk call don slbl hlbl args ci sl excaps buffer hext hstall hNative hin
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

end

end

end Fl4Proofs.P3
