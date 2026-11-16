/-
P3 (DESIGN.md §9), TCB invocations: **the TCB invocations whose spec result
is empty** (for `TopPostDMX`; PerformNil's `NilInv`, extended here rather
than there).

* `NilTcb i`, `NilFl4Tcb j`: the native and FL4 TCB invocations returning
  `[]`: all but ReadRegisters and SetFlags (native), GetBreakpoint,
  ConfigureSingleStepping and SetFlags (FL4's), which return data and which
  FL4 replies itself (`DecOKRMX`).
* `NilInvT`: `NilInv` or one of these; `perform_nilT`.
* `okAll_specDec_thread`: a Thread cap's decode at a label other than
  ReadRegisters, SetFlags, GetBreakpoint and ConfigureSingleStepping gives
  only `NilInvT` invocations; `DecOKDM.toXT` gives `DecOKDMX` for `X` true.
-/
import Fl4Proofs.P3.PerformNil
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open Classical

noncomputable section

section Nil
open Fl4Spec fl4_core

/-- The native TCB invocations returning `[]`. -/
def NilTcb : TcbInvocation → Prop
  | .readRegisters .. => False
  | .setFlags .. => False
  | _ => True

/-- FL4's TCB invocations returning `[]`. -/
def NilFl4Tcb : Fl4TcbInvocation → Prop
  | .getBreakpoint .. => False
  | .configureSingleStepping .. => False
  | .setFlags .. => False
  | _ => True

/-- `NilInv`, or a TCB invocation returning `[]`. -/
def NilInvT (inv : Fl4Invocation) : Prop :=
  NilInv inv ∨ match inv with
    | .invokeTCB i => NilTcb i
    | .invokeFl4TCB j => NilFl4Tcb j
    | _ => False

theorem tcb_nil {i : TcbInvocation} (h : NilTcb i) : OkAll (· = []) (invokeTcb (Z := Unit) i) := by
  cases i with
  | readRegisters => exact absurd h id
  | setFlags => exact absurd h id
  | threadControlCaps => dsimp only [invokeTcb]; okall
  | threadControlSched => dsimp only [invokeTcb]; okall
  | notificationControl t n =>
    cases n <;> (dsimp only [invokeTcb]; exact okAll_liftE (by ndall))
  | _ => dsimp only [invokeTcb]; exact okAll_liftE (by ndall)

theorem fl4tcb_nil {j : Fl4TcbInvocation} (h : NilFl4Tcb j) : OkAll (· = []) (invokeFl4Tcb (Z := Unit) j) := by
  cases j with
  | getBreakpoint => exact absurd h id
  | configureSingleStepping => exact absurd h id
  | setFlags => exact absurd h id
  | fpuTransfer t toFrame fr =>
    dsimp only [invokeFl4Tcb]
    exact okAll_ite (fun _ => okAll_liftE (by ndall)) (fun _ => okAll_returnOk rfl)
  | _ => dsimp only [invokeFl4Tcb]; exact okAll_returnOk rfl

theorem perform_nilT (b c d : Bool) {inv : Fl4Invocation} (h : NilInvT inv) :
    OkAll (· = []) (fl4PerformInvocation (Z := Unit) b c d inv) := by
  rcases h with h | h
  · exact perform_nil b c d h
  · cases inv with
    | invokeTCB i => exact tcb_nil h
    | invokeFl4TCB j => exact fl4tcb_nil h
    | _ => exact absurd h id


/-- `okall` skipping the intermediate computations (`bind` first). -/
macro "okallb" : tactic => `(tactic| (
  repeat (first
    | exact okAll_throw
    | (refine okAll_returnOk ?_; trivial)
    | (refine okAll_pure ?_; trivial)
    | (refine okAll_bind fun _ => ?_)
    | (refine okAll_ite (fun _ => ?_) (fun _ => ?_))
    | split
    | (dsimp only))))

/-- The native decoder at a label other than ReadRegisters and SetFlags
gives only `NilTcb` invocations. -/
theorem okAll_decodeTcb {label : Data} {args : List Data} {cap : Cap} {slot : CslotPtr}
    {excs : List (Cap × CslotPtr)} (h1 : genInvocationType label ≠ .tcbReadRegisters)
    (h2 : genInvocationType label ≠ .tcbSetFlags) :
    OkAll NilTcb (decodeTcbInvocation (Z := Unit) label args cap slot excs) := by
  unfold decodeTcbInvocation
  split
  · exact absurd ‹_› h1
  all_goals first
    | exact absurd ‹_› h2
    | (first
        | unfold decodeWriteRegisters
        | unfold decodeCopyRegisters
        | unfold decodeTcbConfigure
        | unfold decodeSetPriority
        | unfold decodeSetMcpriority
        | unfold decodeSetSchedParams
        | unfold decodeSetTimeoutEp
        | unfold decodeSetIpcBuffer
        | unfold decodeSetSpace
        | unfold decodeBindNotification
        | unfold decodeUnbindNotification
        | unfold decodeSetTlsBase
        | skip)
      okallb

/-- FL4's extension decoders but GetBreakpoint and ConfigureSingleStepping
give only `NilFl4Tcb` invocations. -/
theorem okAll_decodeFl4Ext {l : Fl4TcbExtLabel} {args : List Data} {t : ObjRef} {excaps : List (Cap × CslotPtr)}
    {buf : Option ObjRef} (h1 : l ≠ .getBreakpoint) (h2 : l ≠ .configureSingleStepping) :
    OkAll NilFl4Tcb (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  cases l with
  | getBreakpoint => exact absurd rfl h1
  | configureSingleStepping => exact absurd rfl h2
  | setBreakpoint => dsimp only [decodeFl4TcbExt]; unfold decodeFl4SetBreakpoint; okallb
  | unsetBreakpoint => dsimp only [decodeFl4TcbExt]; unfold decodeFl4UnsetBreakpoint; okallb
  | readFpu => dsimp only [decodeFl4TcbExt]; unfold decodeFl4FpuTransfer; okallb
  | writeFpu => dsimp only [decodeFl4TcbExt]; unfold decodeFl4FpuTransfer; okallb
  | setTimer => dsimp only [decodeFl4TcbExt]; unfold decodeFl4SetTimer; okallb

/-- **A Thread cap's decode at a label with an empty result** gives only
`NilInvT` invocations. -/
theorem okAll_specDec_thread (fp : Bool) (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (p : U64) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef)
    (h1 : genInvocationType slbl ≠ .tcbReadRegisters) (h2 : genInvocationType slbl ≠ .tcbSetFlags)
    (h3 : fl4TcbExtLabelOf slbl ≠ some .getBreakpoint) (h4 : fl4TcbExtLabelOf slbl ≠ some .configureSingleStepping) :
    OkAll NilInvT (specDec fp slbl args ci sl (.Thread p) excaps buffer) := by
  unfold specDec
  show OkAll NilInvT (fl4DecodeInvocation (Z := Unit) fp slbl args ci sl (.threadCap p.bv) excaps buffer)
  unfold fl4DecodeInvocation
  dsimp only
  refine okAll_ite (fun _ => okAll_throw) (fun _ => ?_)
  unfold fl4DecodeTcbInvocation
  rw [if_neg h2]
  cases hl : fl4TcbExtLabelOf slbl with
  | some l =>
    exact okAll_liftME (okAll_decodeFl4Ext (fun e => h3 (by rw [hl, e])) (fun e => h4 (by rw [hl, e])))
      fun _ h => Or.inr h
  | none => exact okAll_liftME (okAll_decodeTcb h1 h2) fun _ h => Or.inr h

/-- **A `DecOKDM` producer whose decode gives only `NilInvT` invocations**
gives `DecOKDMX` for `X` true. -/
theorem DecOKDM.toXT {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] (arI : machine.Arch A)
    {s : S} {ar : A} {σ : State Unit} {lbl length slot : U64} {c : fl4_core.capability.Cap}
    {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array fl4_core.obj.Slot 3#usize} {slbl : Data}
    {args : List Data} {ci : CapRef} {sl : CslotPtr} {excaps : List (Cap × CslotPtr)} {buffer : Option ObjRef}
    (h : DecOKDM (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer)
    (hm : OkAll NilInvT (specDec fp slbl args ci sl c excaps buffer)) :
    DecOKDMX (L := L) arI (fun _ _ _ => True) s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl
      excaps buffer :=
  WP.spec_mono h fun _ hr => TopPostDMX.ofDM hr fun _ hd σ1 y hy rr hrr =>
    perform_nilT blk call don (hd.okAll hm) σ1 y hy rr hrr

end Nil

end

end Fl4Proofs.P3
