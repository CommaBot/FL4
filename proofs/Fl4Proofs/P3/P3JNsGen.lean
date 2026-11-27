/-
P3 (p3J gen 24): **`GKN` for the spec functions of the kernel entry below the invocation shell**, a scripted copy
of irqfix's SpecInvIrqBoundGen (`scratch/p3J/genNs.py`: `GKB` ↦ `GKN`), without the IRQ-control issues (which
write `IRQSignal`); the perform takes P3JCkS's `InvK` (no IRQ-control invocation) in place of `InvB`.

No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JNsKit
import Fl4Proofs.P3.P3JCkS
import Fl4Proofs.P3.SpecFbX

open Classical

namespace Fl4Proofs.P3.SInvNs
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF Fl4Proofs.P3.MachT Fl4Proofs.P3.SInvV

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem gkn_archActivateIdleThread (_t : ObjRef) : GKN (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_archActivateIdleThread)

theorem gkn_activateThread  : GKN (activateThread (Z := Unit)) := by
  unfold activateThread; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_activateThread)

theorem gkn_ensureEmpty (slot : CslotPtr) : GKNE (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_ensureEmpty)

theorem gkn_isIoportRangeFree (f l : IoPort) : GKN (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_isIoportRangeFree)

theorem gkn_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : GKNE (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeIoportControlInvocation)

theorem gkn_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GKNE (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodePageDirectoryInvocation)

theorem gkn_checkVpAlignment (sz : VMPageSize) (vptr : Word) : GKNE (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_checkVpAlignment)

theorem gkn_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (x0 : VMPageSize) (x1 : VMRights) (x2 : VMAttributes) (x3 : ObjRef) : GKNE (createMappingEntries (Z := Unit) base vptr x0 x1 x2 x3) := by
  unfold createMappingEntries; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_createMappingEntries)

theorem gkn_ensureSafeMapping (x0 : VMPageEntry × ObjRef) : GKNE (ensureSafeMapping (Z := Unit) x0) := by
  unfold ensureSafeMapping; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_ensureSafeMapping)

theorem gkn_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GKNE (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodePageInvocation)

theorem gkn_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GKNE (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodePageTableInvocation)

theorem gkn_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GKNE (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodePdptInvocation)

theorem gkn_argsAtLeast (n : Nat) (args : List Data) : GKNE (argsAtLeast (Z := Unit) n args) := by
  unfold argsAtLeast; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_argsAtLeast)

theorem gkn_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : GKNE (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_ensurePortOperationAllowed)

theorem gkn_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : GKNE (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodePortInvocation)

theorem gkn_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : GKN (selectExt (Z := Unit) a S) := by
  unfold selectExt; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_selectExt)

theorem gkn_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GKNE (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_archDecodeInvocation)

theorem gkn_getIrqState (irq : Irq) : GKN (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_getIrqState)

theorem gkn_isIrqActive (irq : Irq) : GKN (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_isIrqActive)

theorem gkn_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : GKNE (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_archDecodeIrqControlInvocation)

theorem gkn_archGetSanitiseRegisterInfo (_t : ObjRef) : GKN (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_archGetSanitiseRegisterInfo)

theorem gkn_archInvokeIrqHandler (x0 : IrqHandlerInvocation) : GKN (archInvokeIrqHandler (Z := Unit) x0) := by
  unfold archInvokeIrqHandler; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_archInvokeIrqHandler)

theorem gkn_archMaskIrqSignal (irq : Irq) : GKN (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_archMaskIrqSignal)

theorem gkn_archNoReturn {m : SMonad Unit Unit} (h : GKN m) : GKN (archNoReturn (Z := Unit) m) := by
  unfold archNoReturn; exact gkn_bind h fun _ => gkn_pure _
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible refine gkn_archNoReturn ?_)

theorem gkn_deleteObjects (ptr : Word) (bits : Nat) : GKN (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  exact gkn_bind (gkn_doMachineOp (mt_freeMemory _ _)) fun _ => gkn_modify fun _ => rfl
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_deleteObjects)

theorem gkn_performAsidControlInvocation (iv : AsidControlInvocation) : GKN (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_performAsidControlInvocation)

theorem gkn_portIn {f : MachineMonad Data} (h : MaskT f) : GKN (portIn (Z := Unit) f) := by
  unfold portIn; exact gkn_bind (gkn_doMachineOp h) fun _ => gkn_pure _
macro_rules | `(tactic| gkn_leaf) => `(tactic| (with_reducible refine gkn_portIn ?_); mt_auto; done)

theorem gkn_portOut {n : Nat} {f : BitVec n → MachineMonad Unit} (h : ∀ w, MaskT (f w)) (w : BitVec n) :
    GKN (portOut (Z := Unit) f w) := by
  unfold portOut; exact gkn_bind (gkn_doMachineOp (h w)) fun _ => gkn_pure _
macro_rules | `(tactic| gkn_leaf) => `(tactic| (with_reducible refine gkn_portOut (fun _ => ?_) _); mt_auto; done)

theorem gkn_performIoPortInvocation (i : IoPortInvocation) : GKN (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_performIoPortInvocation)

theorem gkn_archPerformInvocation (i : ArchInvocation) : GKNE (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_archPerformInvocation)

theorem gkn_lazyFpuRestore (threadPtr : ObjRef) : GKN (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_lazyFpuRestore)

theorem gkn_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : GKN (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_archPostSetFlags)

theorem gkn_archPrepareNextDomain  : GKN (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_archPrepareNextDomain)

theorem gkn_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : GKN (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_archPrepareSetDomain)

theorem gkn_archSwitchToIdleThread  : GKN (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_archSwitchToIdleThread)

theorem gkn_archSwitchToThread (t : ObjRef) : GKN (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_archSwitchToThread)

theorem gkn_tcbReleaseDequeue  : GKN (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_tcbReleaseDequeue)

theorem gkn_awaken  : GKN (awaken (Z := Unit)) := by
  unfold awaken; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_awaken)

theorem gkn_setNtfnObjRef (update : (Option ObjRef → Option ObjRef) → Notification → Notification) (ref : ObjRef) (new : Option ObjRef) : GKN (setNtfnObjRef (Z := Unit) update ref new) := by
  unfold setNtfnObjRef; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_setNtfnObjRef)

theorem gkn_setTcbObjRef (f : (Option ObjRef → Option ObjRef) → Tcb → Tcb) (ref : ObjRef) (new : Option ObjRef) : GKN (setTcbObjRef (Z := Unit) f ref new) := by
  unfold setTcbObjRef; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_setTcbObjRef)

theorem gkn_bindNotification (tcbptr ntfnptr : ObjRef) : GKN (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_bindNotification)

theorem gkn_deletedIrqHandler (irq : Irq) : GKN (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_deletedIrqHandler)

theorem gkn_postCapDeletion (cap : Cap) : GKN (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_postCapDeletion)

theorem gkn_setCdt (t : Cdt) : GKN (setCdt (Z := Unit) t) := by
  unfold setCdt; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_setCdt)

theorem gkn_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : GKN (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_emptySlot)

theorem gkn_orChoiceE {ε α : Type} (c : DetExtMonad Bool) {f g : NonDetE (State Unit) ε α} (hf : GKNE f)
    (hg : GKNE g) : GKNE (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE
  refine gkne_bind (gkne_liftE gkn_get) fun _ => gkne_bind (gkne_liftE (gkn_selectF _)) fun r => ?_
  obtain ⟨rv, _⟩ := r
  try dsimp only
  exact gkne_ite _ hf hg
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible refine gkn_orChoiceE _ ?_ ?_)

theorem gkn_preemptionPoint  : GKNE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_preemptionPoint)

/-- One step of `rec_del` keeps every `GKN` predicate, its recursive calls keeping them. -/
theorem gkn_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, GKN (f k)) (k : RecDelCall) : GKNE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, GKNE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k <;> (unfold recDelF; gkn_auto) <;> exact hrec' _

/-- **`rec_del` keeps every `GKN` predicate** (the pre-fixed point of DomRecDel's `dk_recDel`). -/
theorem gkn_recDel (c : RecDelCall) : GKNE (recDel (Z := Unit) c) := by
  intro P L σ h x hx
  let f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)) := fun _ t =>
    ({y | ∀ P, WLN P → P t → P y.2}, True)
  have hf : ∀ k t, (fun r c => recDelF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy P' L' ht => gkn_recDelF (f := f) (fun _ P'' L'' _ hs _ hz => hz P'' L'' hs) k P' L' t ht y hy,
      fun _ => trivial⟩
  exact (lfp_le_prefixed _ f hf c σ).1 hx P L h
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_recDel)

theorem gkn_capDelete (slot : CslotPtr) : GKNE (capDelete (Z := Unit) slot) := by
  unfold capDelete; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_capDelete)

/-- One step of `cap_revoke` keeps every `GKN` predicate, its recursive calls keeping them. -/
theorem gkn_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, GKN (f k)) (sl : CslotPtr) : GKNE (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, GKNE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF selectExt
  gkn_auto
  all_goals exact hrec' _

/-- **`cap_revoke` keeps every `GKN` predicate.** -/
theorem gkn_capRevoke (sl : CslotPtr) : GKNE (capRevoke (Z := Unit) sl) := by
  intro P L σ h x hx
  let f : CslotPtr → NonDet (State Unit) (Except Unit Unit) := fun _ t =>
    ({y | ∀ P, WLN P → P t → P y.2}, True)
  have hf : ∀ k t, (fun r c => capRevokeF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy P' L' ht => gkn_capRevokeF (f := f) (fun _ P'' L'' _ hs _ hz => hz P'' L'' hs) k P' L' t ht y hy,
      fun _ => trivial⟩
  exact (lfp_le_prefixed _ f hf sl σ).1 hx P L h
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_capRevoke)

theorem gkn_endTimeslice (canTimeout : Bool) : GKN (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_endTimeslice)

theorem gkn_refillResetRr (cscPtr : ObjRef) : GKN (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_refillResetRr)

theorem gkn_chargeBudget (consumed : Ticks) (canTimeout : Bool) : GKN (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_chargeBudget)

theorem gkn_checkBudget  : GKN (checkBudget (Z := Unit)) := by
  unfold checkBudget; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_checkBudget)

theorem gkn_checkBudgetRestart  : GKN (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_checkBudgetRestart)

theorem gkn_checkCapAt (cap : Cap) (slot : CslotPtr) {m : SMonad Unit Unit} (h : GKN m) :
    GKN (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; gkn_auto; all_goals exact h
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible refine gkn_checkCapAt _ _ ?_)

theorem gkn_checkDomainTime  : GKN (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_checkDomainTime)

theorem gkn_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : GKNE (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_checkHandlerEp)

theorem gkn_checkPrio (newPrio : Data) (authTcb : ObjRef) : GKNE (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_checkPrio)

theorem gkn_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : GKNE (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_checkValidIpcBuffer)

theorem gkn_nextDomain  : GKN (nextDomain (Z := Unit)) := by
  unfold nextDomain; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_nextDomain)

theorem gkn_switchToThread (t : ObjRef) : GKN (switchToThread (Z := Unit) t) := by
  unfold switchToThread; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_switchToThread)

theorem gkn_guardedSwitchTo (thread : ObjRef) : GKN (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_guardedSwitchTo)

theorem gkn_switchToIdleThread  : GKN (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_switchToIdleThread)

theorem gkn_chooseThread  : GKN (chooseThread (Z := Unit)) := by
  unfold chooseThread; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_chooseThread)

theorem gkn_getNotification (x0 : ObjRef) : GKN (getNotification (Z := Unit) x0) := by
  unfold getNotification; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_getNotification)

theorem gkn_getNtfnObjRef (update : Notification → Option ObjRef) (ref : ObjRef) : GKN (getNtfnObjRef (Z := Unit) update ref) := by
  unfold getNtfnObjRef; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_getNtfnObjRef)

theorem gkn_setNotification (x0 : ObjRef) (x1 : Notification) : GKN (setNotification (Z := Unit) x0 x1) := by
  unfold setNotification; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_setNotification)

theorem gkn_completeSignal (ntfnptr tptr : ObjRef) : GKN (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_completeSignal)

theorem gkn_dataToObjType (type : Data) : GKNE (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_dataToObjType)

theorem gkn_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : GKNE (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeBindNotification)

theorem gkn_lookupPivotSlot (x0 : Cap) (x1 : CapRef) (x2 : Nat) : GKNE (lookupPivotSlot (Z := Unit) x0 x1 x2) := by
  unfold lookupPivotSlot; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_lookupPivotSlot)

theorem gkn_lookupSourceSlot (x0 : Cap) (x1 : CapRef) (x2 : Nat) : GKNE (lookupSourceSlot (Z := Unit) x0 x1 x2) := by
  unfold lookupSourceSlot; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_lookupSourceSlot)

theorem gkn_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : GKNE (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeCnodeInvocation)

/-- At a thread cap (as `gkn_decodeReadRegisters`). -/
theorem gkn_decodeCopyRegisters (data : List Data) (p : ObjRef) (ec : List Cap) :
    GKNE (decodeCopyRegisters (Z := Unit) data (.threadCap p) ec) := by
  unfold decodeCopyRegisters; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeCopyRegisters)

theorem gkn_slotCapLongRunningDelete (slot : CslotPtr) : GKN (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_slotCapLongRunningDelete)

theorem gkn_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : GKNE (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeCvSpace)

theorem gkn_subframeNode (nodeCap : Cap) (index depth : Data) : GKNE (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_subframeNode)

theorem gkn_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : GKNE (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeDeriveSubframe)

theorem gkn_decodeDomainScheduleConfigure (args : List Data) : GKNE (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeDomainScheduleConfigure)

theorem gkn_decodeDomainScheduleSetStart (args : List Data) : GKNE (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeDomainScheduleSetStart)

theorem gkn_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : GKNE (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeDomainSet)

theorem gkn_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : GKNE (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeDomainInvocation)

theorem gkn_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : GKN (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_fl4GetMr)

theorem gkn_fl4Arg (buf : Option ObjRef) (i : Nat) : GKNE (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_fl4Arg)

theorem gkn_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : GKNE (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeFl4ConfigureSingleStepping)

theorem gkn_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : GKNE (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeFl4FpuTransfer)

theorem gkn_fl4CheckBpNum (bp : Data) : GKNE (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_fl4CheckBpNum)

theorem gkn_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : GKNE (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeFl4GetBreakpoint)

theorem gkn_decodeIrqControlInvocationWith {check : Data → SEMonad Unit Unit} (h : ∀ d, GKNE (check d))
    (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) :
    GKNE (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; gkn_auto; all_goals exact h _
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible refine gkn_decodeIrqControlInvocationWith (fun _ => ?_) _ _ _ _)

theorem gkn_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : GKNE (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeIrqControlRemapped)

theorem gkn_fl4ArchCheckIrq (irq : Data) : GKNE (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_fl4ArchCheckIrq)

theorem gkn_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : GKNE (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeFl4IrqControl)

theorem gkn_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : GKNE (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeFl4SetBreakpoint)

theorem gkn_decodeFl4SetFlags (args : List Data) (t : ObjRef) : GKNE (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeFl4SetFlags)

theorem gkn_decodeFl4SetTimer (args : List Data) (t : ObjRef) : GKNE (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeFl4SetTimer)

theorem gkn_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : GKNE (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeFl4UnsetBreakpoint)

theorem gkn_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : GKNE (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeFl4TcbExt)

theorem gkn_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : GKNE (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeIrqHandlerInvocation)

theorem gkn_decodePml4Flush (cap : ArchCap) : GKNE (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodePml4Flush)

theorem gkn_rangeCheck (v minV maxV : Word) : GKNE (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_rangeCheck)

/-- At a thread cap (its only caller, `decodeTcbInvocation` from the thread-cap
branch of `fl4DecodeInvocation`; the non-thread-cap branch is l4v's `undefined`). -/
theorem gkn_decodeReadRegisters (data : List Data) (p : ObjRef) : GKNE (decodeReadRegisters (Z := Unit) data (.threadCap p)) := by
  unfold decodeReadRegisters; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeReadRegisters)

theorem gkn_getScReleased (scPtr : ObjRef) : GKN (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_getScReleased)

theorem gkn_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : GKNE (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeSchedContextBind)

theorem gkn_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : GKNE (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeSchedContextUnbindObject)

theorem gkn_decodeSchedContextYieldTo (scPtr : ObjRef) : GKNE (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeSchedContextYieldTo)

theorem gkn_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : GKNE (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeSchedContextInvocation)

theorem gkn_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : GKNE (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeSchedControlInvocationFlags)

theorem gkn_decodeSetFlags (args : List Data) (cap : Cap) : GKNE (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeSetFlags)

theorem gkn_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : GKNE (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeSetIpcBuffer)

theorem gkn_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GKNE (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeSetMcpriority)

theorem gkn_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GKNE (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeSetPriority)

theorem gkn_isBlocked (thread : ObjRef) : GKN (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_isBlocked)

theorem gkn_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : GKNE (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeUpdateSc)

theorem gkn_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GKNE (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeSetSchedParams)

theorem gkn_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : GKNE (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeSetSpace)

theorem gkn_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GKNE (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeSetTimeoutEp)

theorem gkn_decodeSetTlsBase (args : List Data) (cap : Cap) : GKNE (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeSetTlsBase)

theorem gkn_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GKNE (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeTcbConfigure)

theorem gkn_decodeUnbindNotification (cap : Cap) : GKNE (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeUnbindNotification)

/-- At a thread cap (its only caller, `decodeTcbInvocation` from the thread-cap
branch of `fl4DecodeInvocation`; the non-thread-cap branch is l4v's `undefined`). -/
theorem gkn_decodeWriteRegisters (data : List Data) (p : ObjRef) : GKNE (decodeWriteRegisters (Z := Unit) data (.threadCap p)) := by
  unfold decodeWriteRegisters; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeWriteRegisters)

/-- At a thread cap. -/
theorem gkn_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : GKNE (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeTcbInvocation)

theorem gkn_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : GKNE (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_frameMappingSlot)

theorem gkn_decodeTestAndClearAccessed (cap : ArchCap) : GKNE (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeTestAndClearAccessed)

theorem gkn_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : GKNE (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeUntypedInvocationWith)

theorem gkn_doNbrecvFailedTransfer (thread : ObjRef) : GKN (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_doNbrecvFailedTransfer)

theorem gkn_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : GKN (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_domainScheduleConfigure)

theorem gkn_setNextInterrupt  : GKN (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_setNextInterrupt)

theorem gkn_ifConstantBandwidthRefillUnblockCheck (scOpt : Option ObjRef) : GKN (ifConstantBandwidthRefillUnblockCheck (Z := Unit) scOpt) := by
  unfold ifConstantBandwidthRefillUnblockCheck; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_ifConstantBandwidthRefillUnblockCheck)

theorem gkn_switchSchedContext  : GKN (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_switchSchedContext)

theorem gkn_scAndTimer  : GKN (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_scAndTimer)

theorem gkn_scheduleChooseNewThread  : GKN (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_scheduleChooseNewThread)

theorem gkn_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : GKN (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_scheduleSwitchThreadFastfail)

theorem gkn_scheduleSwitchThreadBranch (candidate ct : ObjRef) (ctSchdble : Bool) : GKN (scheduleSwitchThreadBranch (Z := Unit) candidate ct ctSchdble) := by
  unfold scheduleSwitchThreadBranch; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_scheduleSwitchThreadBranch)

theorem gkn_schedule  : GKN (schedule (Z := Unit)) := by
  unfold schedule; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_schedule)

theorem gkn_domainSetStart (index : Nat) : GKN (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_domainSetStart)

/-- #68: the TDX decode (`Ext/Tdx`). -/
theorem gkn_decodeTdxInvocation (label : Data) (args : List Data) (extraCaps : List (Cap × CslotPtr)) : GKNE (decodeTdxInvocation (Z := Unit) label args extraCaps) := by
  unfold decodeTdxInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeTdxInvocation)

/-- #68: the TDCALL (the frame write changes the memory only). -/
theorem gkn_performTdxInvocation (i : Fl4TdxInvocation) : GKN (performTdxInvocation (Z := Unit) i) := by
  cases i <;> unfold performTdxInvocation tdxStatus
  · exact gkn_bind (gkn_doMachineOp (mt_of_mkf (mkf_tdxFrameWrite _ _))) fun _ => by gkn_auto
  · gkn_auto
  · exact gkn_bind (gkn_doMachineOp (mt_of_mkf (mkf_tdxFrameWrite _ _))) fun _ => by gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_performTdxInvocation)
/-- fb3c: the batch's decode. -/
theorem gkn_decodeFrameBatch (args : List Data) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    GKNE (decodeFrameBatch (Z := Unit) args cap ex) := by
  unfold decodeFrameBatch; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_decodeFrameBatch)

/-- fb3c: one `X86PML4FrameBatch` entry, its frame `cap_delete` written out (SpecFbX). -/
theorem gkn_fbEntryX (b : Fl4FrameBatchInvocation) (w : Data × Data × Data) :
    GKNE (Fl4Proofs.P3.SInv.fbEntryX b w) := by
  unfold Fl4Proofs.P3.SInv.fbEntryX Fl4Proofs.P3.SInv.fbDeleteX Fl4Proofs.P3.SInv.fbDelX fbCode fbMap unmapPageUnflushed; gkn_auto

theorem gkn_flushAllFb (b : Fl4FrameBatchInvocation) : GKN (flushAll (Z := Unit) b.vspace b.asid) := by
  unfold flushAll; gkn_auto

/-- fb3c: the batch. -/
theorem gkn_performFrameBatch (b : Fl4FrameBatchInvocation) : GKN (performFrameBatch (Z := Unit) b) :=
  fun P hP => Fl4Proofs.P3.SInv.ik_performFrameBatchX (fun w => gkn_fbEntryX b w P hP) (gkn_flushAllFb b P hP)
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_performFrameBatch)

theorem gkn_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GKNE (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_fl4ArchDecodeInvocation)

theorem gkn_fl4ArchPerformInvocation (x0 : Fl4ArchInvocation) : GKNE (fl4ArchPerformInvocation (Z := Unit) x0) := by
  unfold fl4ArchPerformInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_fl4ArchPerformInvocation)

/-- **FL4's TCB timer step keeps every `GKN` predicate**: each fired timer is
a `sendSignal` (MachFieldFamT's frame) and the timer reprogram flag. -/
theorem gkn_fl4Awaken : GKN (fl4Awaken (Z := Unit)) := by
  intro P L σ h x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  show P s'
  clear hx
  induction hx' with
  | refl => exact h
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    have h2 : P σ1 := by
      rcases h1 with rfl | ⟨n, b, e⟩
      · exact ih
      · exact gkn_of_mtk (mtk_sendSignal' n b) P L _ ih ((), σ1) (by rw [e]; exact Set.mem_singleton _)
    exact L.view σ1 _ rfl h2
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible exact gkn_fl4Awaken)

/-- At a thread cap. -/
theorem gkn_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    GKNE (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excaps buffer) := by
  unfold fl4DecodeTcbInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_fl4DecodeTcbInvocation)

theorem gkn_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : GKNE (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_fl4DecodeInvocation)

theorem gkn_resetUntypedCap (srcSlot : CslotPtr) : GKNE (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_resetUntypedCap)

theorem gkn_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : GKNE (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_invokeUntypedWith)

theorem gkn_invokeCnode (i : CnodeInvocation) : GKNE (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_invokeCnode)

theorem gkn_threadSetDomain (tptr : ObjRef) (domain : Domain) : GKN (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_threadSetDomain)

theorem gkn_setDomain (tptr : ObjRef) (newDom : Domain) : GKN (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_setDomain)

theorem gkn_invokeSetDomain (thread : ObjRef) (domain : Domain) : GKN (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_invokeSetDomain)

theorem gkn_invokeDomain (domInv : DomainInvocation) : GKN (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_invokeDomain)

theorem gkn_setFlags (ref : ObjRef) (flags : TcbFlags) : GKN (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_setFlags)

theorem gkn_invokeFl4Tcb (x0 : Fl4TcbInvocation) : GKNE (invokeFl4Tcb (Z := Unit) x0) := by
  unfold invokeFl4Tcb; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_invokeFl4Tcb)

theorem gkn_invokeIrqHandler (x0 : IrqHandlerInvocation) : GKN (invokeIrqHandler (Z := Unit) x0) := by
  unfold invokeIrqHandler; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_invokeIrqHandler)

theorem gkn_ifSporadicActiveCurScTestRefillUnblockCheck (scOpt : Option ObjRef) : GKN (ifSporadicActiveCurScTestRefillUnblockCheck (Z := Unit) scOpt) := by
  unfold ifSporadicActiveCurScTestRefillUnblockCheck; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_ifSporadicActiveCurScTestRefillUnblockCheck)

theorem gkn_setScObjRef {α : Type} (f : (α → α) → SchedContext → SchedContext) (ref : ObjRef) (new : α) : GKN (setScObjRef (Z := Unit) f ref new) := by
  unfold setScObjRef; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_setScObjRef)

theorem gkn_schedContextBindTcb (scPtr tcbPtr : ObjRef) : GKN (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_schedContextBindTcb)

theorem gkn_invokeSchedContext (iv : SchedContextInvocation) : GKN (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_invokeSchedContext)

theorem gkn_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : GKNE (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_installTcbCap)

theorem gkn_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : GKNE (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_installTcbFrameCap)

theorem gkn_restart (thread : ObjRef) : GKN (restart (Z := Unit) thread) := by
  unfold restart; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_restart)

theorem gkn_setMcpriority (ref : ObjRef) (mcp : Priority) : GKN (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_setMcpriority)

theorem gkn_setPriority (tptr : ObjRef) (prio : Priority) : GKN (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_setPriority)

theorem gkn_invokeTcb (x0 : TcbInvocation) : GKNE (invokeTcb (Z := Unit) x0) := by
  unfold invokeTcb; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_invokeTcb)

/-- **The perform keeps every `GKN` predicate when the decode's carry `InvK` holds** (P3JCkS: from a `CKI`
state the decode returns no untyped, SchedControl, IRQ-control or arch invocation). -/
theorem gkn_fl4PerformInvocation (x0 : Bool) (x1 : Bool) (x2 : Bool) (x3 : Fl4Invocation) (hb : SInvCk.InvK x3) :
    GKNE (fl4PerformInvocation (Z := Unit) x0 x1 x2 x3) := by
  cases x3 with
  | invokeUntyped _ => exact hb.elim
  | invokeSchedControl _ => exact hb.elim
  | invokeIRQControl _ => exact hb.elim
  | invokeArchObject _ => exact hb.elim
  | _ => simp only [fl4PerformInvocation]; gkn_auto

theorem gkn_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : GKN (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_fl4ReplyFromKernelError)

theorem gkn_handleNoFault (tptr : ObjRef) : GKN (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_handleNoFault)

theorem gkn_handleFault (thread : ObjRef) (ex : Fault) : GKN (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_handleFault)

theorem gkn_syscall {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ}
    (h1 : GKNE mF) (h2 : ∀ f, GKN (hF f)) (h3 : ∀ a, GKNE (mE a)) (h4 : ∀ e, GKN (hE e))
    (h5 : ∀ b, GKNE (mFin b)) : GKNE (syscall (Z := Unit) mF hF mE hE mFin) := by
  unfold syscall
  refine gkne_bind (gkne_withoutPreemption h1) fun r => ?_
  cases r with
  | error f => exact gkne_withoutPreemption (h2 f)
  | ok a =>
    refine gkne_bind (gkne_withoutPreemption (h3 a)) fun r => ?_
    cases r with
    | error e => exact gkne_withoutPreemption (h4 e)
    | ok b => exact h5 b
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible refine gkn_syscall ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

end

end Fl4Proofs.P3.SInvNs
