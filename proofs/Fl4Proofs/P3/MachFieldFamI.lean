/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN g4d): **the spec's invocations
of the quiet cap kinds keep the machine fields `MR` reads** (`MTK`, spec side
only): MachFieldFamS's family extended by the perform functions of the
invocations an endpoint, notification, reply, domain, SchedContext,
SchedControl or arch cap decodes to (`QInv`), and by `freeMemory` (a
`mapMx` of `storeWord`s) for ASID control's `deleteObjects`.

* `qInv_perform`: every outcome of `fl4PerformInvocation b c d inv` for a
  `QInv` invocation keeps `msFT`.
* `QuietS` (the spec cap kinds other than CNode, Untyped, Thread,
  IrqControl, IrqHandler) and `dec_quiet`: every `ok` outcome of a quiet
  cap's `fl4DecodeInvocation` is a `QInv` invocation.
* `dec_cnode_q`: a CNode cap at a label other than Revoke / Delete decodes to a
  `QInv` invocation (CNode copy / mint / move / mutate / rotate / cancel).
* `mtk_specTailG`, `mtk_fl4ReplyFromKernelErrorG`: the reply tails of
  `handle_invocation`.
-/
import Fl4Proofs.P3.MachFieldFamS
import Fl4Proofs.P3.SpecNoPre
import Fl4Proofs.P3.SpecFbX

open Classical

namespace Fl4Proofs.P3.MachT
open Fl4Spec Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF

noncomputable section

theorem mkf_mapMx_storeWord (xs : List Word) : MKF (NonDet.mapMx (fun p => storeWord p 0) xs) := by
  induction xs with
  | nil => exact mkf_pure _
  | cons x xs ih => exact mkf_bind (mkf_storeWord _ _) fun _ => ih

theorem mkf_freeMemory (p : Word) (b : Nat) : MKF (freeMemory p b) := by
  unfold freeMemory; exact mkf_mapMx_storeWord _
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_freeMemory _ _))

theorem mtk_deleteObjectsG (p : Word) (b : Nat) : MTK (deleteObjects (Z := Unit) p b) := by
  unfold deleteObjects; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_deleteObjectsG _ _)

theorem mtk_archPrepareSetDomainG (t : ObjRef) (d : Domain) : MTK (archPrepareSetDomain (Z := Unit) t d) := by
  unfold archPrepareSetDomain; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_archPrepareSetDomainG _ _)

theorem mtk_threadSetDomainG (t : ObjRef) (d : Domain) : MTK (threadSetDomain (Z := Unit) t d) := by
  unfold threadSetDomain; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_threadSetDomainG _ _)

theorem mtk_setDomainG (t : ObjRef) (d : Domain) : MTK (setDomain (Z := Unit) t d) := by
  unfold setDomain; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setDomainG _ _)

theorem mtk_invokeSetDomainG (t : ObjRef) (d : Domain) : MTK (invokeSetDomain (Z := Unit) t d) := by
  unfold invokeSetDomain; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_invokeSetDomainG _ _)

theorem mtk_domainSetStartG (i : Nat) : MTK (domainSetStart (Z := Unit) i) := by
  unfold domainSetStart; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_domainSetStartG _)

theorem mtk_domainScheduleConfigureG (i : Nat) (d : Domain) (u : DomainDuration) :
    MTK (domainScheduleConfigure (Z := Unit) i d u) := by
  unfold domainScheduleConfigure; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_domainScheduleConfigureG _ _ _)

theorem mtk_invokeDomainG (d : DomainInvocation) : MTK (invokeDomain (Z := Unit) d) := by
  cases d <;> unfold invokeDomain <;> mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_invokeDomainG _)

theorem mtk_schedContextBindTcbG (sc t : ObjRef) : MTK (schedContextBindTcb (Z := Unit) sc t) := by
  unfold schedContextBindTcb; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_schedContextBindTcbG _ _)

theorem mtk_invokeSchedContextG (i : SchedContextInvocation) : MTK (invokeSchedContext (Z := Unit) i) := by
  cases i <;> unfold invokeSchedContext <;> mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_invokeSchedContextG _)

theorem mtk_invokeSchedControlConfigureFlagsG (i : SchedControlInvocation) :
    MTK (invokeSchedControlConfigureFlags (Z := Unit) i) := by
  cases i <;> unfold invokeSchedControlConfigureFlags <;> mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_invokeSchedControlConfigureFlagsG _)

theorem mtk_performAsidControlInvocationG (i : AsidControlInvocation) :
    MTK (performAsidControlInvocation (Z := Unit) i) := by
  cases i <;> unfold performAsidControlInvocation <;> mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_performAsidControlInvocationG _)

theorem mkf_in8 (p : Word16) : MKF (in8 p) := mkf_bind (mkf_machineOpLift _) fun _ => mkf_gets _
theorem mkf_in16 (p : Word16) : MKF (in16 p) := mkf_bind (mkf_machineOpLift _) fun _ => mkf_gets _
theorem mkf_in32 (p : Word16) : MKF (in32 p) := mkf_bind (mkf_machineOpLift _) fun _ => mkf_gets _

theorem mtk_portInG {f : MachineMonad Data} (hf : MKF f) : MTK (portIn (Z := Unit) f) := by
  unfold portIn; exact dk_bind (mtk_doMachineOp hf) fun _ => dk_pure _

theorem mtk_portOutG {n : Nat} {f : BitVec n → MachineMonad Unit} (hf : ∀ w, MKF (f w)) (w : BitVec n) :
    MTK (portOut (Z := Unit) f w) := by
  unfold portOut; exact dk_bind (mtk_doMachineOp (hf w)) fun _ => dk_pure _

theorem mtk_performIoPortInvocationG (i : IoPortInvocation) : MTK (performIoPortInvocation (Z := Unit) i) := by
  obtain ⟨p, d⟩ := i
  cases d <;> unfold performIoPortInvocation
  · exact mtk_portInG (mkf_in8 _)
  · exact mtk_portInG (mkf_in16 _)
  · exact mtk_portInG (mkf_in32 _)
  · exact mtk_portOutG (fun _ => mkf_machineOpLift _) _
  · exact mtk_portOutG (fun _ => mkf_machineOpLift _) _
  · exact mtk_portOutG (fun _ => mkf_machineOpLift _) _
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_performIoPortInvocationG _)

theorem mtk_archPerformInvocationG (i : ArchInvocation) : MTKE (archPerformInvocation (Z := Unit) i) := by
  cases i <;> unfold archPerformInvocation <;> mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_archPerformInvocationG _)

/-- fb3c: one `X86PML4FrameBatch` entry, its frame `cap_delete` written out (SpecFbX). -/
theorem mtk_fbEntryX (b : Fl4FrameBatchInvocation) (w : Data × Data × Data) :
    MTKE (Fl4Proofs.P3.SInv.fbEntryX b w) := by
  unfold Fl4Proofs.P3.SInv.fbEntryX Fl4Proofs.P3.SInv.fbDeleteX Fl4Proofs.P3.SInv.fbDelX fbCode fbMap unmapPageUnflushed; mtk_auto

/-- fb3c: the batch. -/
theorem mtk_performFrameBatch (b : Fl4FrameBatchInvocation) : MTK (performFrameBatch (Z := Unit) b) :=
  Fl4Proofs.P3.SInv.rk_performFrameBatchX (R := fun σ σ' => msFT σ' = msFT σ) (fun _ => rfl)
    (fun _ _ _ h1 h2 => h2.trans h1) (fun w => mtk_fbEntryX b w) (mtk_flushAll _ _)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_performFrameBatch _)

theorem mtk_fl4ArchPerformInvocationG (i : Fl4ArchInvocation) : MTKE (fl4ArchPerformInvocation (Z := Unit) i) := by
  cases i <;> unfold fl4ArchPerformInvocation <;> mtk_auto
  all_goals first | exact mtk_performPml4Flush _ | exact mtk_performDeriveSubframe _ | exact mtk_performTestAndClearAccessed _
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_fl4ArchPerformInvocationG _)

/-- `handle_invocation`'s reply tail keeps `msFT`. -/
theorem mtk_specTailG (c : Bool) (t : ObjRef) (r : List Data) : MTK (Fl4Proofs.P3.specTail c t r) := by
  unfold Fl4Proofs.P3.specTail; mtk_auto

theorem mtk_when {c : Prop} [Decidable c] {m : NonDet (State Unit) Unit} (h : MTK m) :
    MTK (NonDet.when c m) := by
  unfold NonDet.when; split
  · exact h
  · intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

/-- The error reply of `handle_invocation` keeps `msFT`. -/
theorem mtk_fl4ReplyFromKernelErrorG (r : Bool) (t : ObjRef) (x : Data × List Data) :
    MTK (fl4ReplyFromKernelError (Z := Unit) r t x) := by
  unfold fl4ReplyFromKernelError; mtk_auto

/-- **The invocations of the quiet cap kinds** (module docstring). -/
def QInv : Fl4Invocation → Prop
  | .invokeCNode (.revokeCall _) => False
  | .invokeCNode (.deleteCall _) => False
  | .invokeCNode _ => True
  | .invokeEndpoint .. => True
  | .invokeNotification .. => True
  | .invokeReply .. => True
  | .invokeDomain _ => True
  | .invokeSchedContext _ => True
  | .invokeSchedControl _ => True
  | .invokeArchObject _ => True
  | _ => False

theorem mtk_withoutPreemptionE {α : Type} {m : SMonad Unit α} (h : MTK m) :
    MTKE (withoutPreemption (Z := Unit) m) := by
  intro σ y hy
  unfold withoutPreemption NonDetE.liftE at hy
  rw [ExceptT.run_lift] at hy
  obtain ⟨x, hx, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  exact h σ x hx

/-- **A `QInv` invocation's perform keeps `msFT`** (module docstring). -/
theorem qInv_perform (b c d : Bool) (inv : Fl4Invocation) (h : QInv inv) :
    MTKE (fl4PerformInvocation (Z := Unit) b c d inv) := by
  cases inv with
  | invokeCNode i =>
    cases i <;> simp only [QInv] at h <;> simp only [fl4PerformInvocation, invokeCnode] <;> mtk_auto
    all_goals (rename_i heq; cases heq)
  | _ => simp only [QInv] at h <;> unfold fl4PerformInvocation <;> mtk_auto

/-- **The quiet spec cap kinds** (module docstring). -/
def QuietS : Cap → Prop
  | .cnodeCap .. => False
  | .untypedCap .. => False
  | .threadCap _ => False
  | .irqControlCap => False
  | .irqHandlerCap _ => False
  | _ => True

/-- **A quiet cap decodes to a `QInv` invocation** (module docstring). -/
theorem dec_quiet (fp : Bool) (lbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (hq : QuietS cap) :
    NoPre.OkP QInv (fl4DecodeInvocation (Z := Unit) fp lbl args ci sl cap ex buf) := by
  cases cap <;> simp only [QuietS] at hq <;> simp only [fl4DecodeInvocation, NonDetE.returnOk, NonDetE.throwError] <;>
    first
    | exact NoPre.okP_throw
    | exact NoPre.okP_liftME fun _ => trivial
    | exact NoPre.okP_pure trivial
    | (split <;> first | exact NoPre.okP_throw | exact NoPre.okP_pure trivial | exact NoPre.okP_liftME fun _ => trivial)

set_option maxHeartbeats 2000000 in
/-- **A CNode cap at a label other than Revoke and Delete decodes to a `QInv`
invocation.** -/
theorem dec_cnode_q (fp : Bool) (lbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (p : ObjRef)
    (b : Nat) (g : List Bool) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef)
    (hr : genInvocationType lbl ≠ .cnodeRevoke) (hd : genInvocationType lbl ≠ .cnodeDelete) :
    NoPre.OkP QInv (fl4DecodeInvocation (Z := Unit) fp lbl args ci sl (.cnodeCap p b g) ex buf) := by
  simp only [fl4DecodeInvocation, NonDetE.throwError]
  split
  · exact NoPre.okP_throw
  · exact NoPre.okP_liftME' (NoPre.dec_cnode_noPre lbl args _ _ hr hd) fun i h => by
      cases i <;> simp_all [NoPre.PreInv, QInv]

end

end Fl4Proofs.P3.MachT
