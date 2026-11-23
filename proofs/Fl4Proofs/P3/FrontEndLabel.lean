/-
P3 (issue #16, front end): **FL4's label numbers in the spec**.

The spec decodes a message label by FL4's ABI numbers
(`Fl4Spec.InvocationLabel.fl4Numbering`, PORTING.md "Invocation label
numbers"); both sides read the same label word (FL4's `msg_info` and the
spec's `getMessageInfo`: bits 12.. of the message-info register), so
`slbl = lbl.bv` (FrontEndExtra's `JAtZ.frontJ`).

* `invocationType_eq`, `genInvocationType_eq`: the spec's label of a word is
  `fl4Lab` of its number (computable).
* `fl4_label_table`: for every `fl4_abi::label` constant, the label the spec
  decodes it to (and the l4h numbers `fl4RemappedLabel`,
  `fl4Pml4FlushLabel`, `fl4DeriveSubframeLabel`, `fl4TestAndClearLabel`,
  `fl4TcbExtLabelNum`), so a renumbering of the ABI breaks this proof.
* The decode paths' label facts at `slbl = lbl.bv`: `schedControl_label`,
  `irqControl_label`, `irqControl_remap`, `ioControl_label`, `port_label`,
  `genInvocationType_untyped_iff`.
* The paths whose label premise is an equality with an FL4-label map
  (`cnodeLabelOf`, `tcbLabelOf`, `scLabelOf`, `irqHLabelOf`, `domLabelOf`)
  hold only for the cap's own labels (FL4's label 2 on a CNode cap is the
  spec's `tcbReadRegisters`, `cnodeLabelOf 2` is invalid). Off them the
  cap's spec decoder fails with `IllegalOperation` at the message's label
  and at label 0 alike (`*Dec_out`), so the decode is identified with the
  one at label 0 (`*_canon`, `specDec_*`), whose spec label is invalid as the
  maps say; `XCapP.lbl_congr` moves the statement back.
-/
import Fl4Proofs.P3.XTopJointCnDel
import Fl4Proofs.P3.TcbDecode
import Fl4Proofs.P3.ScDecodeSc
import Fl4Proofs.P3.DomDecode
import Fl4Proofs.P3.IoPortTop
import Fl4Proofs.P3.IrqDecode
import Fl4Proofs.P3.CnodeSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Fl4Spec

noncomputable section

/-! ## The numbering -/

/-- The spec's label at FL4's label number `n`. -/
def fl4Lab (n : Nat) : InvocationLabel :=
  match InvocationLabel.fl4Numbering[n]? with
  | some (some l) => l
  | _ => .genInvocationLabel .invalidInvocation

/-- The generic label of an invocation label (`genInvocationType`'s match). -/
def genOfL : InvocationLabel → GenInvocationLabels
  | .genInvocationLabel l => l
  | .archInvocationLabel _ => .invalidInvocation

theorem numbering_length : InvocationLabel.fl4Numbering.length = 72 := by decide

theorem numbering_fromEnum (v : InvocationLabel) :
    InvocationLabel.fl4Numbering[v.fromEnum]? = some (some v) := by
  cases v with
  | genInvocationLabel l => cases l <;> decide
  | archInvocationLabel l => cases l <;> decide

theorem numbering_idx : ∀ n < 72,
    ((InvocationLabel.fl4Numbering[n]?).bind id).all (fun l => decide (l.fromEnum = n)) = true := by decide

theorem dataToNat_bv (w : U64) : dataToNat w.bv = w.val := rfl

/-- **The spec's label of a word is `fl4Lab` of its number.** -/
theorem invocationType_eq (x : Data) : invocationType x = fl4Lab (dataToNat x) := by
  unfold invocationType
  by_cases h : ∃ v : InvocationLabel, v.fromEnum = dataToNat x
  · rw [if_pos h]
    obtain ⟨v, hv⟩ := h
    unfold InvocationLabel.toEnum fl4Lab
    rw [← hv, numbering_fromEnum]; rfl
  · rw [if_neg h]
    unfold fl4Lab
    split
    · rename_i l hl
      exfalso; apply h; refine ⟨l, ?_⟩
      by_cases hlt : dataToNat x < 72
      · have := numbering_idx _ hlt; rw [hl] at this; simpa using this
      · rw [List.getElem?_eq_none (by rw [numbering_length]; omega)] at hl; cases hl
    · rfl

theorem genInvocationType_eq (x : Data) : genInvocationType x = genOfL (fl4Lab (dataToNat x)) := by
  unfold genInvocationType; rw [invocationType_eq]
  cases fl4Lab (dataToNat x) <;> rfl

theorem fl4Lab_ge {n : Nat} (h : 72 ≤ n) : fl4Lab n = .genInvocationLabel .invalidInvocation := by
  unfold fl4Lab; rw [List.getElem?_eq_none (by rw [numbering_length]; exact h)]

theorem genInvocationType_zero : genInvocationType (0 : Data) = .invalidInvocation := by
  rw [genInvocationType_eq]; rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- **Every `fl4_abi::label` constant, decoded by the spec** (and the l4h
label numbers), pinning `InvocationLabel.fl4Numbering` to the extracted
constants. -/
theorem fl4_label_table :
    Fl4Spec.invocationType fl4_abi.label.UntypedRetype.bv = .genInvocationLabel .untypedRetype ∧
    Fl4Spec.invocationType fl4_abi.label.TCBReadRegisters.bv = .genInvocationLabel .tcbReadRegisters ∧
    Fl4Spec.invocationType fl4_abi.label.TCBWriteRegisters.bv = .genInvocationLabel .tcbWriteRegisters ∧
    Fl4Spec.invocationType fl4_abi.label.TCBCopyRegisters.bv = .genInvocationLabel .tcbCopyRegisters ∧
    Fl4Spec.invocationType fl4_abi.label.TCBConfigure.bv = .genInvocationLabel .tcbConfigure ∧
    Fl4Spec.invocationType fl4_abi.label.TCBSetPriority.bv = .genInvocationLabel .tcbSetPriority ∧
    Fl4Spec.invocationType fl4_abi.label.TCBSetMCPriority.bv = .genInvocationLabel .tcbSetMCPriority ∧
    Fl4Spec.invocationType fl4_abi.label.TCBSetSchedParams.bv = .genInvocationLabel .tcbSetSchedParams ∧
    Fl4Spec.invocationType fl4_abi.label.TCBSetTimeoutEndpoint.bv = .genInvocationLabel .tcbSetTimeoutEndpoint ∧
    Fl4Spec.invocationType fl4_abi.label.TCBSetIPCBuffer.bv = .genInvocationLabel .tcbSetIPCBuffer ∧
    Fl4Spec.invocationType fl4_abi.label.TCBSetSpace.bv = .genInvocationLabel .tcbSetSpace ∧
    Fl4Spec.invocationType fl4_abi.label.TCBSuspend.bv = .genInvocationLabel .tcbSuspend ∧
    Fl4Spec.invocationType fl4_abi.label.TCBResume.bv = .genInvocationLabel .tcbResume ∧
    Fl4Spec.invocationType fl4_abi.label.TCBBindNotification.bv = .genInvocationLabel .tcbBindNotification ∧
    Fl4Spec.invocationType fl4_abi.label.TCBUnbindNotification.bv = .genInvocationLabel .tcbUnbindNotification ∧
    Fl4Spec.invocationType fl4_abi.label.TCBSetBreakpoint.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.fl4TcbExtLabelNum .setBreakpoint = fl4_abi.label.TCBSetBreakpoint.val ∧
    Fl4Spec.invocationType fl4_abi.label.TCBGetBreakpoint.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.fl4TcbExtLabelNum .getBreakpoint = fl4_abi.label.TCBGetBreakpoint.val ∧
    Fl4Spec.invocationType fl4_abi.label.TCBUnsetBreakpoint.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.fl4TcbExtLabelNum .unsetBreakpoint = fl4_abi.label.TCBUnsetBreakpoint.val ∧
    Fl4Spec.invocationType fl4_abi.label.TCBConfigureSingleStepping.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.fl4TcbExtLabelNum .configureSingleStepping = fl4_abi.label.TCBConfigureSingleStepping.val ∧
    Fl4Spec.invocationType fl4_abi.label.TCBSetTLSBase.bv = .genInvocationLabel .tcbSetTLSBase ∧
    Fl4Spec.invocationType fl4_abi.label.TCBSetFlags.bv = .genInvocationLabel .tcbSetFlags ∧
    Fl4Spec.invocationType fl4_abi.label.TCBReadFPU.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.fl4TcbExtLabelNum .readFpu = fl4_abi.label.TCBReadFPU.val ∧
    Fl4Spec.invocationType fl4_abi.label.TCBWriteFPU.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.fl4TcbExtLabelNum .writeFpu = fl4_abi.label.TCBWriteFPU.val ∧
    Fl4Spec.invocationType fl4_abi.label.TCBSetTimer.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.fl4TcbExtLabelNum .setTimer = fl4_abi.label.TCBSetTimer.val ∧
    Fl4Spec.invocationType fl4_abi.label.CNodeRevoke.bv = .genInvocationLabel .cnodeRevoke ∧
    Fl4Spec.invocationType fl4_abi.label.CNodeDelete.bv = .genInvocationLabel .cnodeDelete ∧
    Fl4Spec.invocationType fl4_abi.label.CNodeCancelBadgedSends.bv = .genInvocationLabel .cnodeCancelBadgedSends ∧
    Fl4Spec.invocationType fl4_abi.label.CNodeCopy.bv = .genInvocationLabel .cnodeCopy ∧
    Fl4Spec.invocationType fl4_abi.label.CNodeMint.bv = .genInvocationLabel .cnodeMint ∧
    Fl4Spec.invocationType fl4_abi.label.CNodeMove.bv = .genInvocationLabel .cnodeMove ∧
    Fl4Spec.invocationType fl4_abi.label.CNodeMutate.bv = .genInvocationLabel .cnodeMutate ∧
    Fl4Spec.invocationType fl4_abi.label.CNodeRotate.bv = .genInvocationLabel .cnodeRotate ∧
    Fl4Spec.invocationType fl4_abi.label.IRQIssueIRQHandler.bv = .genInvocationLabel .irqIssueIRQHandler ∧
    Fl4Spec.invocationType fl4_abi.label.IRQAckIRQ.bv = .genInvocationLabel .irqAckIRQ ∧
    Fl4Spec.invocationType fl4_abi.label.IRQSetIRQHandler.bv = .genInvocationLabel .irqSetIRQHandler ∧
    Fl4Spec.invocationType fl4_abi.label.IRQClearIRQHandler.bv = .genInvocationLabel .irqClearIRQHandler ∧
    Fl4Spec.invocationType fl4_abi.label.DomainSetSet.bv = .genInvocationLabel .domainSetSet ∧
    Fl4Spec.invocationType fl4_abi.label.DomainScheduleConfigure.bv = .genInvocationLabel .domainScheduleConfigure ∧
    Fl4Spec.invocationType fl4_abi.label.DomainScheduleSetStart.bv = .genInvocationLabel .domainScheduleSetStart ∧
    Fl4Spec.invocationType fl4_abi.label.SchedControlConfigureFlags.bv = .genInvocationLabel .schedControlConfigureFlags ∧
    Fl4Spec.invocationType fl4_abi.label.SchedContextBind.bv = .genInvocationLabel .schedContextBind ∧
    Fl4Spec.invocationType fl4_abi.label.SchedContextUnbind.bv = .genInvocationLabel .schedContextUnbind ∧
    Fl4Spec.invocationType fl4_abi.label.SchedContextUnbindObject.bv = .genInvocationLabel .schedContextUnbindObject ∧
    Fl4Spec.invocationType fl4_abi.label.SchedContextConsumed.bv = .genInvocationLabel .schedContextConsumed ∧
    Fl4Spec.invocationType fl4_abi.label.SchedContextYieldTo.bv = .genInvocationLabel .schedContextYieldTo ∧
    Fl4Spec.invocationType fl4_abi.label.X86PML4Flush.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.fl4Pml4FlushLabel = fl4_abi.label.X86PML4Flush.val ∧
    Fl4Spec.invocationType fl4_abi.label.X86PDPTMap.bv = .archInvocationLabel .x64PDPTMap ∧
    Fl4Spec.invocationType fl4_abi.label.X86PDPTUnmap.bv = .archInvocationLabel .x64PDPTUnmap ∧
    Fl4Spec.invocationType fl4_abi.label.X86VCPUReadMSR.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86VCPUWriteMSR.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86PageDirectoryMap.bv = .archInvocationLabel .x64PageDirectoryMap ∧
    Fl4Spec.invocationType fl4_abi.label.X86PageDirectoryUnmap.bv = .archInvocationLabel .x64PageDirectoryUnmap ∧
    Fl4Spec.invocationType fl4_abi.label.X86PageTableMap.bv = .archInvocationLabel .x64PageTableMap ∧
    Fl4Spec.invocationType fl4_abi.label.X86PageTableUnmap.bv = .archInvocationLabel .x64PageTableUnmap ∧
    Fl4Spec.invocationType fl4_abi.label.X86PageMap.bv = .archInvocationLabel .x64PageMap ∧
    Fl4Spec.invocationType fl4_abi.label.X86PageUnmap.bv = .archInvocationLabel .x64PageUnmap ∧
    Fl4Spec.invocationType fl4_abi.label.X86PageDeriveSubframe.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.fl4DeriveSubframeLabel = fl4_abi.label.X86PageDeriveSubframe.val ∧
    Fl4Spec.invocationType fl4_abi.label.X86PageTestAndClearAccessed.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.fl4TestAndClearLabel = fl4_abi.label.X86PageTestAndClearAccessed.val ∧
    Fl4Spec.invocationType fl4_abi.label.X86PageGetAddress.bv = .archInvocationLabel .x64PageGetAddress ∧
    Fl4Spec.invocationType fl4_abi.label.X86PageMapEPT.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86ASIDControlMakePool.bv = .archInvocationLabel .x64ASIDControlMakePool ∧
    Fl4Spec.invocationType fl4_abi.label.X86ASIDPoolAssign.bv = .archInvocationLabel .x64ASIDPoolAssign ∧
    Fl4Spec.invocationType fl4_abi.label.X86IOPortControlIssue.bv = .archInvocationLabel .x64IOPortControlIssue ∧
    Fl4Spec.invocationType fl4_abi.label.X86IOPortIn8.bv = .archInvocationLabel .x64IOPortIn8 ∧
    Fl4Spec.invocationType fl4_abi.label.X86IOPortIn16.bv = .archInvocationLabel .x64IOPortIn16 ∧
    Fl4Spec.invocationType fl4_abi.label.X86IOPortIn32.bv = .archInvocationLabel .x64IOPortIn32 ∧
    Fl4Spec.invocationType fl4_abi.label.X86IOPortOut8.bv = .archInvocationLabel .x64IOPortOut8 ∧
    Fl4Spec.invocationType fl4_abi.label.X86IOPortOut16.bv = .archInvocationLabel .x64IOPortOut16 ∧
    Fl4Spec.invocationType fl4_abi.label.X86IOPortOut32.bv = .archInvocationLabel .x64IOPortOut32 ∧
    Fl4Spec.invocationType fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC.bv = .archInvocationLabel .x64IRQIssueIRQHandlerIOAPIC ∧
    Fl4Spec.invocationType fl4_abi.label.X86IRQIssueIRQHandlerMSI.bv = .archInvocationLabel .x64IRQIssueIRQHandlerMSI ∧
    Fl4Spec.invocationType fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.fl4RemappedLabel = fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped.val ∧
    Fl4Spec.invocationType fl4_abi.label.X86VCPUSetTCB.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86VCPUReadVMCS.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86VCPUWriteVMCS.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86VCPUFlushTLB.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86VCPUReadVMCB.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86VCPUWriteVMCB.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86VCPUEnableIOPort.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86VCPUDisableIOPort.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86VCPUWriteRegisters.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86EPTPDPTMap.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86EPTPDPTUnmap.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86EPTPDMap.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86EPTPDUnmap.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86EPTPTMap.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.X86EPTPTUnmap.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.TCBSetEPTRoot.bv = .genInvocationLabel .invalidInvocation ∧
    Fl4Spec.invocationType fl4_abi.label.UntypedRetypeShared.bv = .genInvocationLabel .invalidInvocation := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.UntypedRetype.val = 1 by simp [fl4_abi.label.UntypedRetype]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBReadRegisters.val = 2 by simp [fl4_abi.label.TCBReadRegisters]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBWriteRegisters.val = 3 by simp [fl4_abi.label.TCBWriteRegisters]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBCopyRegisters.val = 4 by simp [fl4_abi.label.TCBCopyRegisters]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBConfigure.val = 5 by simp [fl4_abi.label.TCBConfigure]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBSetPriority.val = 6 by simp [fl4_abi.label.TCBSetPriority]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBSetMCPriority.val = 7 by simp [fl4_abi.label.TCBSetMCPriority]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBSetSchedParams.val = 8 by simp [fl4_abi.label.TCBSetSchedParams]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBSetTimeoutEndpoint.val = 9 by simp [fl4_abi.label.TCBSetTimeoutEndpoint]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBSetIPCBuffer.val = 10 by simp [fl4_abi.label.TCBSetIPCBuffer]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBSetSpace.val = 11 by simp [fl4_abi.label.TCBSetSpace]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBSuspend.val = 12 by simp [fl4_abi.label.TCBSuspend]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBResume.val = 13 by simp [fl4_abi.label.TCBResume]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBBindNotification.val = 14 by simp [fl4_abi.label.TCBBindNotification]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBUnbindNotification.val = 15 by simp [fl4_abi.label.TCBUnbindNotification]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBSetBreakpoint.val = 16 by simp [fl4_abi.label.TCBSetBreakpoint]]; first | rfl | decide
  · simp [fl4_abi.label.TCBSetBreakpoint, fl4TcbExtLabelNum, fl4Pml4FlushLabel, fl4DeriveSubframeLabel, fl4TestAndClearLabel, fl4RemappedLabel]
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBGetBreakpoint.val = 17 by simp [fl4_abi.label.TCBGetBreakpoint]]; first | rfl | decide
  · simp [fl4_abi.label.TCBGetBreakpoint, fl4TcbExtLabelNum, fl4Pml4FlushLabel, fl4DeriveSubframeLabel, fl4TestAndClearLabel, fl4RemappedLabel]
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBUnsetBreakpoint.val = 18 by simp [fl4_abi.label.TCBUnsetBreakpoint]]; first | rfl | decide
  · simp [fl4_abi.label.TCBUnsetBreakpoint, fl4TcbExtLabelNum, fl4Pml4FlushLabel, fl4DeriveSubframeLabel, fl4TestAndClearLabel, fl4RemappedLabel]
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBConfigureSingleStepping.val = 19 by simp [fl4_abi.label.TCBConfigureSingleStepping]]; first | rfl | decide
  · simp [fl4_abi.label.TCBConfigureSingleStepping, fl4TcbExtLabelNum, fl4Pml4FlushLabel, fl4DeriveSubframeLabel, fl4TestAndClearLabel, fl4RemappedLabel]
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBSetTLSBase.val = 20 by simp [fl4_abi.label.TCBSetTLSBase]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBSetFlags.val = 21 by simp [fl4_abi.label.TCBSetFlags]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBReadFPU.val = 22 by simp [fl4_abi.label.TCBReadFPU]]; first | rfl | decide
  · simp [fl4_abi.label.TCBReadFPU, fl4TcbExtLabelNum, fl4Pml4FlushLabel, fl4DeriveSubframeLabel, fl4TestAndClearLabel, fl4RemappedLabel]
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBWriteFPU.val = 23 by simp [fl4_abi.label.TCBWriteFPU]]; first | rfl | decide
  · simp [fl4_abi.label.TCBWriteFPU, fl4TcbExtLabelNum, fl4Pml4FlushLabel, fl4DeriveSubframeLabel, fl4TestAndClearLabel, fl4RemappedLabel]
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBSetTimer.val = 24 by simp [fl4_abi.label.TCBSetTimer]]; first | rfl | decide
  · simp [fl4_abi.label.TCBSetTimer, fl4TcbExtLabelNum, fl4Pml4FlushLabel, fl4DeriveSubframeLabel, fl4TestAndClearLabel, fl4RemappedLabel]
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.CNodeRevoke.val = 25 by simp [fl4_abi.label.CNodeRevoke]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.CNodeDelete.val = 26 by simp [fl4_abi.label.CNodeDelete]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.CNodeCancelBadgedSends.val = 27 by simp [fl4_abi.label.CNodeCancelBadgedSends]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.CNodeCopy.val = 28 by simp [fl4_abi.label.CNodeCopy]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.CNodeMint.val = 29 by simp [fl4_abi.label.CNodeMint]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.CNodeMove.val = 30 by simp [fl4_abi.label.CNodeMove]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.CNodeMutate.val = 31 by simp [fl4_abi.label.CNodeMutate]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.CNodeRotate.val = 32 by simp [fl4_abi.label.CNodeRotate]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.IRQIssueIRQHandler.val = 33 by simp [fl4_abi.label.IRQIssueIRQHandler]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.IRQAckIRQ.val = 34 by simp [fl4_abi.label.IRQAckIRQ]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.IRQSetIRQHandler.val = 35 by simp [fl4_abi.label.IRQSetIRQHandler]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.IRQClearIRQHandler.val = 36 by simp [fl4_abi.label.IRQClearIRQHandler]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.DomainSetSet.val = 37 by simp [fl4_abi.label.DomainSetSet]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.DomainScheduleConfigure.val = 38 by simp [fl4_abi.label.DomainScheduleConfigure]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.DomainScheduleSetStart.val = 39 by simp [fl4_abi.label.DomainScheduleSetStart]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.SchedControlConfigureFlags.val = 40 by simp [fl4_abi.label.SchedControlConfigureFlags]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.SchedContextBind.val = 41 by simp [fl4_abi.label.SchedContextBind]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.SchedContextUnbind.val = 42 by simp [fl4_abi.label.SchedContextUnbind]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.SchedContextUnbindObject.val = 43 by simp [fl4_abi.label.SchedContextUnbindObject]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.SchedContextConsumed.val = 44 by simp [fl4_abi.label.SchedContextConsumed]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.SchedContextYieldTo.val = 45 by simp [fl4_abi.label.SchedContextYieldTo]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86PML4Flush.val = 46 by simp [fl4_abi.label.X86PML4Flush]]; first | rfl | decide
  · simp [fl4_abi.label.X86PML4Flush, fl4TcbExtLabelNum, fl4Pml4FlushLabel, fl4DeriveSubframeLabel, fl4TestAndClearLabel, fl4RemappedLabel]
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86PDPTMap.val = 47 by simp [fl4_abi.label.X86PDPTMap]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86PDPTUnmap.val = 48 by simp [fl4_abi.label.X86PDPTUnmap]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86VCPUReadMSR.val = 49 by simp [fl4_abi.label.X86VCPUReadMSR]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86VCPUWriteMSR.val = 50 by simp [fl4_abi.label.X86VCPUWriteMSR]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86PageDirectoryMap.val = 51 by simp [fl4_abi.label.X86PageDirectoryMap]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86PageDirectoryUnmap.val = 52 by simp [fl4_abi.label.X86PageDirectoryUnmap]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86PageTableMap.val = 53 by simp [fl4_abi.label.X86PageTableMap]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86PageTableUnmap.val = 54 by simp [fl4_abi.label.X86PageTableUnmap]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86PageMap.val = 55 by simp [fl4_abi.label.X86PageMap]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86PageUnmap.val = 56 by simp [fl4_abi.label.X86PageUnmap]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86PageDeriveSubframe.val = 57 by simp [fl4_abi.label.X86PageDeriveSubframe]]; first | rfl | decide
  · simp [fl4_abi.label.X86PageDeriveSubframe, fl4TcbExtLabelNum, fl4Pml4FlushLabel, fl4DeriveSubframeLabel, fl4TestAndClearLabel, fl4RemappedLabel]
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86PageTestAndClearAccessed.val = 58 by simp [fl4_abi.label.X86PageTestAndClearAccessed]]; first | rfl | decide
  · simp [fl4_abi.label.X86PageTestAndClearAccessed, fl4TcbExtLabelNum, fl4Pml4FlushLabel, fl4DeriveSubframeLabel, fl4TestAndClearLabel, fl4RemappedLabel]
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86PageGetAddress.val = 59 by simp [fl4_abi.label.X86PageGetAddress]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86PageMapEPT.val = 60 by simp [fl4_abi.label.X86PageMapEPT]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86ASIDControlMakePool.val = 61 by simp [fl4_abi.label.X86ASIDControlMakePool]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86ASIDPoolAssign.val = 62 by simp [fl4_abi.label.X86ASIDPoolAssign]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86IOPortControlIssue.val = 63 by simp [fl4_abi.label.X86IOPortControlIssue]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86IOPortIn8.val = 64 by simp [fl4_abi.label.X86IOPortIn8]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86IOPortIn16.val = 65 by simp [fl4_abi.label.X86IOPortIn16]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86IOPortIn32.val = 66 by simp [fl4_abi.label.X86IOPortIn32]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86IOPortOut8.val = 67 by simp [fl4_abi.label.X86IOPortOut8]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86IOPortOut16.val = 68 by simp [fl4_abi.label.X86IOPortOut16]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86IOPortOut32.val = 69 by simp [fl4_abi.label.X86IOPortOut32]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC.val = 70 by simp [fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86IRQIssueIRQHandlerMSI.val = 71 by simp [fl4_abi.label.X86IRQIssueIRQHandlerMSI]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped.val = 72 by simp [fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped]]; first | rfl | decide
  · simp [fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped, fl4TcbExtLabelNum, fl4Pml4FlushLabel, fl4DeriveSubframeLabel, fl4TestAndClearLabel, fl4RemappedLabel]
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86VCPUSetTCB.val = 73 by simp [fl4_abi.label.X86VCPUSetTCB]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86VCPUReadVMCS.val = 74 by simp [fl4_abi.label.X86VCPUReadVMCS]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86VCPUWriteVMCS.val = 75 by simp [fl4_abi.label.X86VCPUWriteVMCS]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86VCPUFlushTLB.val = 76 by simp [fl4_abi.label.X86VCPUFlushTLB]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86VCPUReadVMCB.val = 77 by simp [fl4_abi.label.X86VCPUReadVMCB]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86VCPUWriteVMCB.val = 78 by simp [fl4_abi.label.X86VCPUWriteVMCB]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86VCPUEnableIOPort.val = 79 by simp [fl4_abi.label.X86VCPUEnableIOPort]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86VCPUDisableIOPort.val = 80 by simp [fl4_abi.label.X86VCPUDisableIOPort]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86VCPUWriteRegisters.val = 81 by simp [fl4_abi.label.X86VCPUWriteRegisters]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86EPTPDPTMap.val = 82 by simp [fl4_abi.label.X86EPTPDPTMap]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86EPTPDPTUnmap.val = 83 by simp [fl4_abi.label.X86EPTPDPTUnmap]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86EPTPDMap.val = 84 by simp [fl4_abi.label.X86EPTPDMap]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86EPTPDUnmap.val = 85 by simp [fl4_abi.label.X86EPTPDUnmap]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86EPTPTMap.val = 86 by simp [fl4_abi.label.X86EPTPTMap]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.X86EPTPTUnmap.val = 87 by simp [fl4_abi.label.X86EPTPTUnmap]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.TCBSetEPTRoot.val = 88 by simp [fl4_abi.label.TCBSetEPTRoot]]; first | rfl | decide
  · rw [invocationType_eq, dataToNat_bv, show fl4_abi.label.UntypedRetypeShared.val = 89 by simp [fl4_abi.label.UntypedRetypeShared]]; first | rfl | decide

/-! ## The decode paths' label facts at `slbl = lbl.bv` -/

theorem u64_val_eq {x y : U64} : x = y ↔ x.val = y.val := ⟨congrArg _, UScalar.eq_of_val_eq⟩

theorem schedControl_label (lbl : U64) :
    genInvocationType lbl.bv = .schedControlConfigureFlags ↔ lbl = fl4_abi.label.SchedControlConfigureFlags := by
  have hv : fl4_abi.label.SchedControlConfigureFlags.val = 40 := by simp [fl4_abi.label.SchedControlConfigureFlags]
  rw [u64_val_eq, hv, genInvocationType_eq, dataToNat_bv]
  generalize lbl.val = n
  rcases Nat.lt_or_ge n 72 with h | h
  · revert n; decide
  · rw [fl4Lab_ge h]; constructor <;> intro e
    · cases e
    · exact absurd e (by omega)

theorem genInvocationType_untyped_iff (lbl : U64) :
    genInvocationType lbl.bv = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype := by
  have hv : fl4_abi.label.UntypedRetype.val = 1 := by simp [fl4_abi.label.UntypedRetype]
  rw [u64_val_eq, hv, genInvocationType_eq, dataToNat_bv]
  generalize lbl.val = n
  rcases Nat.lt_or_ge n 72 with h | h
  · revert n; decide
  · rw [fl4Lab_ge h]; constructor <;> intro e
    · cases e
    · exact absurd e (by omega)

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
theorem irqControl_label (lbl : U64) : IrqCLabel lbl lbl.bv := by
  unfold IrqCLabel
  rw [genInvocationType_eq, invocationType_eq, dataToNat_bv]; simp only [ne_eq]
  generalize lbl.val = n
  rcases Nat.lt_or_ge n 72 with h | h
  · revert n; decide
  · rw [fl4Lab_ge h]
    refine ⟨fun e => absurd e (by omega), fun e => absurd e (by omega), fun e => absurd e (by omega),
      fun _ _ _ _ => ⟨?_, ?_, ?_⟩⟩ <;> decide

theorem irqControl_remap (lbl : U64) : decide (lbl.val = 72) = isFl4RemappedLabel lbl.bv := rfl

theorem ioControl_label (lbl : U64) :
    lbl.val = 63 ↔ invocationType lbl.bv = .archInvocationLabel .x64IOPortControlIssue := by
  rw [invocationType_eq, dataToNat_bv]
  generalize lbl.val = n
  rcases Nat.lt_or_ge n 72 with h | h
  · revert n; decide
  · rw [fl4Lab_ge h]; constructor <;> intro e
    · exact absurd e (by omega)
    · cases e

theorem forall_arch_ne6 (x : InvocationLabel) (a1 a2 a3 a4 a5 a6 : ArchInvocationLabel) :
    (∀ l, x = .archInvocationLabel l → l ≠ a1 ∧ l ≠ a2 ∧ l ≠ a3 ∧ l ≠ a4 ∧ l ≠ a5 ∧ l ≠ a6) ↔
      (x ≠ .archInvocationLabel a1 ∧ x ≠ .archInvocationLabel a2 ∧ x ≠ .archInvocationLabel a3 ∧
        x ≠ .archInvocationLabel a4 ∧ x ≠ .archInvocationLabel a5 ∧ x ≠ .archInvocationLabel a6) := by
  constructor
  · intro h
    exact ⟨fun e => (h _ e).1 rfl, fun e => (h _ e).2.1 rfl, fun e => (h _ e).2.2.1 rfl,
      fun e => (h _ e).2.2.2.1 rfl, fun e => (h _ e).2.2.2.2.1 rfl, fun e => (h _ e).2.2.2.2.2 rfl⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ l rfl
    exact ⟨fun e => h1 (congrArg _ e), fun e => h2 (congrArg _ e), fun e => h3 (congrArg _ e),
      fun e => h4 (congrArg _ e), fun e => h5 (congrArg _ e), fun e => h6 (congrArg _ e)⟩

theorem port_label (lbl : U64) : PortLabel lbl lbl.bv := by
  unfold PortLabel portSz
  rw [invocationType_eq, dataToNat_bv]; simp only [forall_arch_ne6]; simp only [ne_eq]
  generalize lbl.val = n
  rcases Nat.lt_or_ge n 72 with h | h
  · revert n; decide
  · rw [fl4Lab_ge h]
    exact ⟨fun e => absurd e (by omega), fun e => absurd e (by omega), fun _ => by decide⟩

/-! ## The VSpace paths' label facts (XTopJointEntry's VSpace cases) -/

theorem pt_label (lbl : U64) :
    (lbl = fl4_abi.label.X86PageTableMap → invocationType lbl.bv = .archInvocationLabel .x64PageTableMap) ∧
    (lbl = fl4_abi.label.X86PageTableUnmap → invocationType lbl.bv = .archInvocationLabel .x64PageTableUnmap) ∧
    (lbl ≠ fl4_abi.label.X86PageTableMap → lbl ≠ fl4_abi.label.X86PageTableUnmap →
      invocationType lbl.bv ≠ .archInvocationLabel .x64PageTableMap ∧ invocationType lbl.bv ≠ .archInvocationLabel .x64PageTableUnmap) := by
  have h1 : fl4_abi.label.X86PageTableMap.val = 53 := by simp [fl4_abi.label.X86PageTableMap]
  have h2 : fl4_abi.label.X86PageTableUnmap.val = 54 := by simp [fl4_abi.label.X86PageTableUnmap]
  simp only [ne_eq, u64_val_eq, h1, h2, invocationType_eq, dataToNat_bv]
  generalize lbl.val = n
  rcases Nat.lt_or_ge n 72 with h | h
  · revert n; decide
  · rw [fl4Lab_ge h]
    exact ⟨fun e => absurd e (by omega), fun e => absurd e (by omega), fun _ _ => ⟨by decide, by decide⟩⟩

theorem pd_label (lbl : U64) :
    (lbl = fl4_abi.label.X86PageDirectoryMap → invocationType lbl.bv = .archInvocationLabel .x64PageDirectoryMap) ∧
    (lbl = fl4_abi.label.X86PageDirectoryUnmap → invocationType lbl.bv = .archInvocationLabel .x64PageDirectoryUnmap) ∧
    (lbl ≠ fl4_abi.label.X86PageDirectoryMap → lbl ≠ fl4_abi.label.X86PageDirectoryUnmap →
      invocationType lbl.bv ≠ .archInvocationLabel .x64PageDirectoryMap ∧ invocationType lbl.bv ≠ .archInvocationLabel .x64PageDirectoryUnmap) := by
  have h1 : fl4_abi.label.X86PageDirectoryMap.val = 51 := by simp [fl4_abi.label.X86PageDirectoryMap]
  have h2 : fl4_abi.label.X86PageDirectoryUnmap.val = 52 := by simp [fl4_abi.label.X86PageDirectoryUnmap]
  simp only [ne_eq, u64_val_eq, h1, h2, invocationType_eq, dataToNat_bv]
  generalize lbl.val = n
  rcases Nat.lt_or_ge n 72 with h | h
  · revert n; decide
  · rw [fl4Lab_ge h]
    exact ⟨fun e => absurd e (by omega), fun e => absurd e (by omega), fun _ _ => ⟨by decide, by decide⟩⟩

theorem pdpt_label (lbl : U64) :
    (lbl = fl4_abi.label.X86PDPTMap → invocationType lbl.bv = .archInvocationLabel .x64PDPTMap) ∧
    (lbl = fl4_abi.label.X86PDPTUnmap → invocationType lbl.bv = .archInvocationLabel .x64PDPTUnmap) ∧
    (lbl ≠ fl4_abi.label.X86PDPTMap → lbl ≠ fl4_abi.label.X86PDPTUnmap →
      invocationType lbl.bv ≠ .archInvocationLabel .x64PDPTMap ∧ invocationType lbl.bv ≠ .archInvocationLabel .x64PDPTUnmap) := by
  have h1 : fl4_abi.label.X86PDPTMap.val = 47 := by simp [fl4_abi.label.X86PDPTMap]
  have h2 : fl4_abi.label.X86PDPTUnmap.val = 48 := by simp [fl4_abi.label.X86PDPTUnmap]
  simp only [ne_eq, u64_val_eq, h1, h2, invocationType_eq, dataToNat_bv]
  generalize lbl.val = n
  rcases Nat.lt_or_ge n 72 with h | h
  · revert n; decide
  · rw [fl4Lab_ge h]
    exact ⟨fun e => absurd e (by omega), fun e => absurd e (by omega), fun _ _ => ⟨by decide, by decide⟩⟩

theorem pool_label (lbl : U64) :
    lbl = fl4_abi.label.X86ASIDPoolAssign ↔ invocationType lbl.bv = .archInvocationLabel .x64ASIDPoolAssign := by
  have h1 : fl4_abi.label.X86ASIDPoolAssign.val = 62 := by simp [fl4_abi.label.X86ASIDPoolAssign]
  rw [u64_val_eq, h1, invocationType_eq, dataToNat_bv]
  generalize lbl.val = n
  rcases Nat.lt_or_ge n 72 with h | h
  · revert n; decide
  · rw [fl4Lab_ge h]; constructor <;> intro e
    · exact absurd e (by omega)
    · cases e

theorem makePool_label (lbl : U64) :
    lbl = fl4_abi.label.X86ASIDControlMakePool ↔ invocationType lbl.bv = .archInvocationLabel .x64ASIDControlMakePool := by
  have h1 : fl4_abi.label.X86ASIDControlMakePool.val = 61 := by simp [fl4_abi.label.X86ASIDControlMakePool]
  rw [u64_val_eq, h1, invocationType_eq, dataToNat_bv]
  generalize lbl.val = n
  rcases Nat.lt_or_ge n 72 with h | h
  · revert n; decide
  · rw [fl4Lab_ge h]; constructor <;> intro e
    · exact absurd e (by omega)
    · cases e

theorem getAddress_label (lbl : U64) :
    lbl = fl4_abi.label.X86PageGetAddress ↔ invocationType lbl.bv = .archInvocationLabel .x64PageGetAddress := by
  have h1 : fl4_abi.label.X86PageGetAddress.val = 59 := by simp [fl4_abi.label.X86PageGetAddress]
  rw [u64_val_eq, h1, invocationType_eq, dataToNat_bv]
  generalize lbl.val = n
  rcases Nat.lt_or_ge n 72 with h | h
  · revert n; decide
  · rw [fl4Lab_ge h]; constructor <;> intro e
    · exact absurd e (by omega)
    · cases e

theorem pml4_label (lbl : U64) : dataToNat lbl.bv = fl4Pml4FlushLabel ↔ lbl = fl4_abi.label.X86PML4Flush := by
  have h1 : fl4_abi.label.X86PML4Flush.val = 46 := by simp [fl4_abi.label.X86PML4Flush]
  rw [dataToNat_bv, u64_val_eq, h1]; rfl

/-- FrameBatch (#71): the batch's label on a PML4 cap (FL4 90 = `fl4FrameBatchLabel`). -/
theorem pml4fb_label (lbl : U64) :
    dataToNat lbl.bv = fl4FrameBatchLabel ↔ lbl = fl4_abi.label.X86PML4FrameBatch := by
  have h1 : fl4_abi.label.X86PML4FrameBatch.val = 90 := by simp [fl4_abi.label.X86PML4FrameBatch]
  rw [dataToNat_bv, u64_val_eq, h1]; rfl

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The native frame cap's labels** (VsDecFrame's `FrameLabel`), off FL4's
EPT-map label (the frame path's `[scope]` case). -/
theorem frame_label (lbl : U64) (hn : lbl ≠ fl4_abi.label.X86PageMapEPT) : FrameLabel lbl lbl.bv := by
  have h55 : fl4_abi.label.X86PageMap.val = 55 := by simp [fl4_abi.label.X86PageMap]
  have h56 : fl4_abi.label.X86PageUnmap.val = 56 := by simp [fl4_abi.label.X86PageUnmap]
  have h57 : fl4_abi.label.X86PageDeriveSubframe.val = 57 := by simp [fl4_abi.label.X86PageDeriveSubframe]
  have h58 : fl4_abi.label.X86PageTestAndClearAccessed.val = 58 := by
    simp [fl4_abi.label.X86PageTestAndClearAccessed]
  have h59 : fl4_abi.label.X86PageGetAddress.val = 59 := by simp [fl4_abi.label.X86PageGetAddress]
  have hds : fl4DeriveSubframeLabel = 57 := rfl
  have htc : fl4TestAndClearLabel = 58 := rfl
  refine ⟨hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ne_eq, u64_val_eq, h55, h56, h57, h58, h59, dataToNat_bv, hds, htc, invocationType_eq]
  · exact id
  · exact id
  · exact id
  · intro e; rw [e]; decide
  · intro e; rw [e]; decide
  · intro e; rw [e]; decide
  · exact id
  · generalize lbl.val = n
    rcases Nat.lt_or_ge n 72 with h | h
    · revert n; decide
    · rw [fl4Lab_ge h]; intros; exact ⟨by decide, by decide, by decide⟩

/-! ## The maps' labels: on the cap's own labels -/

theorem cnode_in (lbl : U64) (h1 : 25 ≤ lbl.val) (h2 : lbl.val ≤ 32) :
    genInvocationType lbl.bv = cnodeLabelOf lbl := by
  unfold cnodeLabelOf
  rw [genInvocationType_eq, dataToNat_bv]
  revert h1 h2
  generalize lbl.val = n
  intro h1 h2
  have h : n < 72 := by omega
  revert n; decide

theorem cnode_out (lbl : U64) (h : ¬ (25 ≤ lbl.val ∧ lbl.val ≤ 32)) :
    genInvocationType lbl.bv ∉ GenInvocationLabels.uptoEnum .cnodeRevoke .cnodeRotate ∧
      cnodeLabelOf lbl = .invalidInvocation := by
  refine ⟨?_, by unfold cnodeLabelOf; split_ifs <;> first | rfl | omega⟩
  rw [genInvocationType_eq, dataToNat_bv]
  revert h
  generalize lbl.val = n
  intro h
  rcases Nat.lt_or_ge n 72 with h' | h'
  · revert h; revert n; decide
  · rw [fl4Lab_ge h']; decide

theorem tcb_in (lbl : U64) (h1 : 2 ≤ lbl.val) (h2 : lbl.val ≤ 24) :
    genInvocationType lbl.bv = tcbLabelOf lbl := by
  unfold tcbLabelOf
  rw [genInvocationType_eq, dataToNat_bv]
  revert h1 h2
  generalize lbl.val = n
  intro h1 h2
  have h : n < 72 := by omega
  revert n; decide

/-- FL4's TCB labels and the spec's (`decodeTcbInvocation`'s, `SetFlags`). -/
def tcbGenList : List GenInvocationLabels :=
  [.tcbReadRegisters, .tcbWriteRegisters, .tcbCopyRegisters, .tcbSuspend, .tcbResume, .tcbConfigure,
   .tcbSetPriority, .tcbSetMCPriority, .tcbSetSchedParams, .tcbSetTimeoutEndpoint, .tcbSetIPCBuffer,
   .tcbSetSpace, .tcbBindNotification, .tcbUnbindNotification, .tcbSetTLSBase, .tcbSetFlags]

/-- The extension-label lookup of `fl4TcbExtLabelOf`, at a number. -/
def tcbExtFind (n : Nat) : Option Fl4TcbExtLabel :=
  [Fl4TcbExtLabel.setBreakpoint, .getBreakpoint, .unsetBreakpoint, .configureSingleStepping, .readFpu,
    .writeFpu, .setTimer].find? fun l => decide (n = fl4TcbExtLabelNum l)

theorem fl4TcbExtLabelOf_eq (x : Data) :
    fl4TcbExtLabelOf x = if genInvocationType x = .invalidInvocation then tcbExtFind (dataToNat x) else none := rfl

theorem tcbExtFind_hi {n : Nat} (h : 25 ≤ n) : tcbExtFind n = none := by
  unfold tcbExtFind
  simp [List.find?, fl4TcbExtLabelNum, show n ≠ 16 by omega, show n ≠ 17 by omega, show n ≠ 18 by omega,
    show n ≠ 19 by omega, show n ≠ 22 by omega, show n ≠ 23 by omega, show n ≠ 24 by omega]

theorem tcb_ext (lbl : U64) :
    genInvocationType lbl.bv = .invalidInvocation → fl4TcbExtLabelOf lbl.bv = tcbExtOf lbl := by
  rw [fl4TcbExtLabelOf_eq]
  unfold tcbExtOf
  rw [genInvocationType_eq, dataToNat_bv]
  generalize lbl.val = n
  rcases Nat.lt_or_ge n 72 with h | h
  · revert n; decide
  · intro _
    rw [fl4Lab_ge h, show genOfL (.genInvocationLabel .invalidInvocation) = .invalidInvocation from rfl, if_pos rfl,
      tcbExtFind_hi (by omega)]
    split_ifs <;> first | rfl | omega

theorem tcb_out (lbl : U64) (h : ¬ (2 ≤ lbl.val ∧ lbl.val ≤ 24)) :
    genInvocationType lbl.bv ∉ tcbGenList ∧ fl4TcbExtLabelOf lbl.bv = none ∧ tcbLabelOf lbl = .invalidInvocation ∧
      tcbExtOf lbl = none := by
  refine ⟨?_, ?_, by
    unfold tcbLabelOf; simp only [show lbl.val ≠ 2 by omega, show lbl.val ≠ 3 by omega, show lbl.val ≠ 4 by omega, show lbl.val ≠ 5 by omega, show lbl.val ≠ 6 by omega, show lbl.val ≠ 7 by omega, show lbl.val ≠ 8 by omega, show lbl.val ≠ 9 by omega, show lbl.val ≠ 10 by omega, show lbl.val ≠ 11 by omega, show lbl.val ≠ 12 by omega, show lbl.val ≠ 13 by omega, show lbl.val ≠ 14 by omega, show lbl.val ≠ 15 by omega, show lbl.val ≠ 20 by omega, show lbl.val ≠ 21 by omega, ↓reduceIte],
    by unfold tcbExtOf; split_ifs <;> first | rfl | omega⟩
  · rw [genInvocationType_eq, dataToNat_bv]
    revert h
    generalize lbl.val = n
    intro h
    rcases Nat.lt_or_ge n 72 with h' | h'
    · revert h; revert n; decide
    · rw [fl4Lab_ge h']; decide
  · rw [fl4TcbExtLabelOf_eq, genInvocationType_eq, dataToNat_bv]
    revert h
    generalize lbl.val = n
    intro h
    rcases Nat.lt_or_ge n 72 with h' | h'
    · revert h; revert n; decide
    · rw [fl4Lab_ge h', show genOfL (.genInvocationLabel .invalidInvocation) = .invalidInvocation from rfl, if_pos rfl,
        tcbExtFind_hi (by omega)]

/-- FL4's SchedContext labels and the spec's. -/
def scGenList : List GenInvocationLabels :=
  [.schedContextConsumed, .schedContextBind, .schedContextUnbindObject, .schedContextUnbind, .schedContextYieldTo]

theorem sc_in (lbl : U64) (h1 : 41 ≤ lbl.val) (h2 : lbl.val ≤ 45) :
    genInvocationType lbl.bv = Sched.scLabelOf lbl := by
  unfold Sched.scLabelOf
  rw [genInvocationType_eq, dataToNat_bv]
  revert h1 h2
  generalize lbl.val = n
  intro h1 h2
  have h : n < 72 := by omega
  revert n; decide

theorem sc_out (lbl : U64) (h : ¬ (41 ≤ lbl.val ∧ lbl.val ≤ 45)) :
    genInvocationType lbl.bv ∉ scGenList ∧ Sched.scLabelOf lbl = .invalidInvocation := by
  refine ⟨?_, by unfold Sched.scLabelOf; split_ifs <;> first | rfl | omega⟩
  rw [genInvocationType_eq, dataToNat_bv]
  revert h
  generalize lbl.val = n
  intro h
  rcases Nat.lt_or_ge n 72 with h' | h'
  · revert h; revert n; decide
  · rw [fl4Lab_ge h']; decide

/-- FL4's IRQ handler labels and the spec's. -/
def irqHGenList : List GenInvocationLabels := [.irqAckIRQ, .irqSetIRQHandler, .irqClearIRQHandler]

theorem irqH_in (lbl : U64) (h1 : 34 ≤ lbl.val) (h2 : lbl.val ≤ 36) :
    genInvocationType lbl.bv = irqHLabelOf lbl := by
  unfold irqHLabelOf
  rw [genInvocationType_eq, dataToNat_bv]
  revert h1 h2
  generalize lbl.val = n
  intro h1 h2
  have h : n < 72 := by omega
  revert n; decide

theorem irqH_out (lbl : U64) (h : ¬ (34 ≤ lbl.val ∧ lbl.val ≤ 36)) :
    genInvocationType lbl.bv ∉ irqHGenList ∧ irqHLabelOf lbl = .invalidInvocation := by
  refine ⟨?_, by unfold irqHLabelOf; split_ifs <;> first | rfl | omega⟩
  rw [genInvocationType_eq, dataToNat_bv]
  revert h
  generalize lbl.val = n
  intro h
  rcases Nat.lt_or_ge n 72 with h' | h'
  · revert h; revert n; decide
  · rw [fl4Lab_ge h']; decide

/-- FL4's domain labels and the spec's. -/
def domGenList : List GenInvocationLabels := [.domainSetSet, .domainScheduleConfigure, .domainScheduleSetStart]

theorem dom_in (lbl : U64) (h1 : 37 ≤ lbl.val) (h2 : lbl.val ≤ 39) :
    genInvocationType lbl.bv = domLabelOf lbl := by
  unfold domLabelOf
  rw [genInvocationType_eq, dataToNat_bv]
  revert h1 h2
  generalize lbl.val = n
  intro h1 h2
  have h : n < 72 := by omega
  revert n; decide

theorem dom_out (lbl : U64) (h : ¬ (37 ≤ lbl.val ∧ lbl.val ≤ 39)) :
    genInvocationType lbl.bv ∉ domGenList ∧ domLabelOf lbl = .invalidInvocation := by
  refine ⟨?_, by unfold domLabelOf; split_ifs <;> first | rfl | omega⟩
  rw [genInvocationType_eq, dataToNat_bv]
  revert h
  generalize lbl.val = n
  intro h
  rcases Nat.lt_or_ge n 72 with h' | h'
  · revert h; revert n; decide
  · rw [fl4Lab_ge h']; decide

/-! ## Off the cap's labels: the decoders fail alike -/

theorem cnodeDec_out {l : Data} (h : genInvocationType l ∉ GenInvocationLabels.uptoEnum .cnodeRevoke .cnodeRotate)
    (args : List Data) (cap : Cap) (exs : List Cap) :
    decodeCnodeInvocation (Z := Unit) l args cap exs = NonDetE.throwError .illegalOperation := by
  rw [cnodeDecode_eq]
  simp only [NonDetE.unlessE, if_neg h, NonDetE.throwError, ndE_throw_bind]

theorem tcbDec_out {l : Data} (h : genInvocationType l ∉ tcbGenList) (args : List Data) (cap : Cap)
    (slot : CslotPtr) (exs : List (Cap × CslotPtr)) :
    decodeTcbInvocation (Z := Unit) l args cap slot exs = NonDetE.throwError .illegalOperation := by
  unfold decodeTcbInvocation
  generalize genInvocationType l = g at h ⊢
  cases g <;> first | rfl | exact absurd (by decide) h

theorem fl4TcbDec_out {l : Data} (h1 : genInvocationType l ∉ tcbGenList) (h2 : fl4TcbExtLabelOf l = none)
    (args : List Data) (cap : Cap) (slot : CslotPtr) (exs : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    fl4DecodeTcbInvocation (Z := Unit) l args cap slot exs buf =
      NonDetE.liftME Fl4Invocation.invokeTCB (NonDetE.throwError .illegalOperation) := by
  have hf : genInvocationType l ≠ .tcbSetFlags := fun e => h1 (by rw [e]; decide)
  unfold fl4DecodeTcbInvocation
  rw [if_neg hf]
  simp only [h2, tcbDec_out h1]

theorem scDec_out {l : Data} (h : genInvocationType l ∉ scGenList) (sc : ObjRef) (exs : List Cap) :
    decodeSchedContextInvocation (Z := Unit) l sc exs = NonDetE.throwError .illegalOperation := by
  unfold decodeSchedContextInvocation
  generalize genInvocationType l = g at h ⊢
  cases g <;> first | rfl | exact absurd (by decide) h

theorem irqHDec_out {l : Data} (h : genInvocationType l ∉ irqHGenList) (irq : Irq) (cps : List (Cap × CslotPtr)) :
    decodeIrqHandlerInvocation (Z := Unit) l irq cps = NonDetE.throwError .illegalOperation := by
  unfold decodeIrqHandlerInvocation
  rw [if_neg (fun e => h (by rw [e]; decide)), if_neg (fun e => h (by rw [e]; decide)),
    if_neg (fun e => h (by rw [e]; decide))]

theorem domDec_out {l : Data} (h : genInvocationType l ∉ domGenList) (args : List Data) (exs : List (Cap × CslotPtr)) :
    decodeDomainInvocation (Z := Unit) l args exs = NonDetE.throwError .illegalOperation := by
  unfold decodeDomainInvocation
  generalize genInvocationType l = g at h ⊢
  cases g <;> first | rfl | exact absurd (by decide) h

/-! ## The canonical label of a path -/

theorem cnode_canon (lbl : U64) : ∃ sl : Data, genInvocationType sl = cnodeLabelOf lbl ∧
    ∀ args cap exs, decodeCnodeInvocation (Z := Unit) lbl.bv args cap exs = decodeCnodeInvocation sl args cap exs := by
  by_cases h : 25 ≤ lbl.val ∧ lbl.val ≤ 32
  · exact ⟨lbl.bv, cnode_in lbl h.1 h.2, fun _ _ _ => rfl⟩
  · obtain ⟨ho, hm⟩ := cnode_out lbl h
    refine ⟨0, by rw [genInvocationType_zero, hm], fun args cap exs => ?_⟩
    rw [cnodeDec_out ho, cnodeDec_out (by rw [genInvocationType_zero]; decide)]

theorem tcb_canon (lbl : U64) : ∃ sl : Data, genInvocationType sl = tcbLabelOf lbl ∧
    (genInvocationType sl = .invalidInvocation → fl4TcbExtLabelOf sl = tcbExtOf lbl) ∧
    ∀ args cap slot exs buf, fl4DecodeTcbInvocation (Z := Unit) lbl.bv args cap slot exs buf =
      fl4DecodeTcbInvocation sl args cap slot exs buf := by
  by_cases h : 2 ≤ lbl.val ∧ lbl.val ≤ 24
  · exact ⟨lbl.bv, tcb_in lbl h.1 h.2, tcb_ext lbl, fun _ _ _ _ _ => rfl⟩
  · obtain ⟨ho, he, hm, hx⟩ := tcb_out lbl h
    have h0 : fl4TcbExtLabelOf (0 : Data) = none := by
      rw [fl4TcbExtLabelOf_eq, genInvocationType_zero, if_pos rfl]; rfl
    refine ⟨0, by rw [genInvocationType_zero, hm], fun _ => by rw [h0, hx], fun args cap slot exs buf => ?_⟩
    rw [fl4TcbDec_out ho he, fl4TcbDec_out (by rw [genInvocationType_zero]; decide) h0]

theorem sc_canon (lbl : U64) : ∃ sl : Data, genInvocationType sl = Sched.scLabelOf lbl ∧
    (41 ≤ lbl.val ∧ lbl.val ≤ 45 → sl = lbl.bv) ∧
    ∀ sc exs, decodeSchedContextInvocation (Z := Unit) lbl.bv sc exs = decodeSchedContextInvocation sl sc exs := by
  by_cases h : 41 ≤ lbl.val ∧ lbl.val ≤ 45
  · exact ⟨lbl.bv, sc_in lbl h.1 h.2, fun _ => rfl, fun _ _ => rfl⟩
  · obtain ⟨ho, hm⟩ := sc_out lbl h
    refine ⟨0, by rw [genInvocationType_zero, hm], fun h' => absurd h' h, fun sc exs => ?_⟩
    rw [scDec_out ho, scDec_out (by rw [genInvocationType_zero]; decide)]

theorem irqH_canon (lbl : U64) : ∃ sl : Data, genInvocationType sl = irqHLabelOf lbl ∧
    ∀ irq cps, decodeIrqHandlerInvocation (Z := Unit) lbl.bv irq cps = decodeIrqHandlerInvocation sl irq cps := by
  by_cases h : 34 ≤ lbl.val ∧ lbl.val ≤ 36
  · exact ⟨lbl.bv, irqH_in lbl h.1 h.2, fun _ _ => rfl⟩
  · obtain ⟨ho, hm⟩ := irqH_out lbl h
    refine ⟨0, by rw [genInvocationType_zero, hm], fun irq cps => ?_⟩
    rw [irqHDec_out ho, irqHDec_out (by rw [genInvocationType_zero]; decide)]

theorem dom_canon (lbl : U64) : ∃ sl : Data, genInvocationType sl = domLabelOf lbl ∧
    ∀ args exs, decodeDomainInvocation (Z := Unit) lbl.bv args exs = decodeDomainInvocation sl args exs := by
  by_cases h : 37 ≤ lbl.val ∧ lbl.val ≤ 39
  · exact ⟨lbl.bv, dom_in lbl h.1 h.2, fun _ _ => rfl⟩
  · obtain ⟨ho, hm⟩ := dom_out lbl h
    refine ⟨0, by rw [genInvocationType_zero, hm], fun args exs => ?_⟩
    rw [domDec_out ho, domDec_out (by rw [genInvocationType_zero]; decide)]

/-! ## The spec's dispatch at the canonical label -/

section
variable {fp : Bool} {sl sl' : Data} {args : List Data} {ci : CapRef} {slot : CslotPtr}
  {excaps : List (Cap × CslotPtr)} {buffer : Option ObjRef}

theorem specDec_cnode (p r gs g : U64)
    (h : ∀ args cap exs, decodeCnodeInvocation (Z := Unit) sl args cap exs = decodeCnodeInvocation sl' args cap exs) :
    specDec fp sl args ci slot (.CNode p r gs g) excaps buffer = specDec fp sl' args ci slot (.CNode p r gs g) excaps buffer := by
  simp only [specDec, absCap, fl4DecodeInvocation, h]

theorem specDec_thread (p : U64)
    (h : ∀ args cap slot exs buf, fl4DecodeTcbInvocation (Z := Unit) sl args cap slot exs buf =
      fl4DecodeTcbInvocation sl' args cap slot exs buf) :
    specDec fp sl args ci slot (.Thread p) excaps buffer = specDec fp sl' args ci slot (.Thread p) excaps buffer := by
  simp only [specDec, absCap, fl4DecodeInvocation, h]

theorem specDec_sc (p sb : U64)
    (h : ∀ sc exs, decodeSchedContextInvocation (Z := Unit) sl sc exs = decodeSchedContextInvocation sl' sc exs) :
    specDec fp sl args ci slot (.SchedContext p sb) excaps buffer =
      specDec fp sl' args ci slot (.SchedContext p sb) excaps buffer := by
  simp only [specDec, absCap, fl4DecodeInvocation, h]

theorem specDec_irqH (irq : U64)
    (h : ∀ irq cps, decodeIrqHandlerInvocation (Z := Unit) sl irq cps = decodeIrqHandlerInvocation sl' irq cps) :
    specDec fp sl args ci slot (.IrqHandler irq) excaps buffer = specDec fp sl' args ci slot (.IrqHandler irq) excaps buffer := by
  simp only [specDec, absCap, fl4DecodeInvocation, h]

theorem specDec_dom
    (h : ∀ args exs, decodeDomainInvocation (Z := Unit) sl args exs = decodeDomainInvocation sl' args exs) :
    specDec fp sl args ci slot .Domain excaps buffer = specDec fp sl' args ci slot .Domain excaps buffer := by
  simp only [specDec, absCap, fl4DecodeInvocation, h]

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`XCapP` moves along the spec's decode**: it depends on the label word
only through `specDec`. -/
theorem XCapP.lbl_congr {X XP : S → A → State Unit → Prop} {s : S} {ar : A} {σ : State Unit}
    {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl slbl' : Data} {args : List Data} {ci : CapRef}
    {sl : CslotPtr} {excaps : List (Cap × CslotPtr)} {buffer : Option ObjRef} {ct : U64}
    (h : specDec fp slbl args ci sl c excaps buffer = specDec fp slbl' args ci sl c excaps buffer)
    (hx : XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl' args ci sl excaps buffer ct) :
    XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct := by
  unfold XCapP DecOKDMXP DecOKRMX at *
  rw [h]; exact hx

end

end

end Fl4Proofs.P3
