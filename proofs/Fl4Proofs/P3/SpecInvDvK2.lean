/- s26: the object half `OBK O` of device `valid_untyped`, part 2 (SpecInvUtZK2 renamed; see SpecInvDvK1). -/
import Fl4Proofs.P3.SpecInvDvK1
open Classical

namespace Fl4Proofs.P3.SInvDV
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {OS : ObSet}



theorem ob_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : OBK OS (setPt (Z := Unit) ptr pt) := by
  unfold setPt; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setPt _ _)

theorem ob_storePte (p : ObjRef) (pte : PTE) : OBK OS (storePte (Z := Unit) p pte) := by
  unfold storePte; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_storePte _ _)

theorem ob_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : OBK OS (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_unmapPage _ _ _ _)

theorem ob_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : OBK OS (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_flushTable _ _ _ _)

theorem ob_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : OBK OS (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_invalidatePageStructureCacheAsid _ _)

theorem ob_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : OBK OS (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_unmapPageTable _ _ _)

theorem ob_flushAll (vspace : ObjRef) (asid : Asid) : OBK OS (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_flushAll _ _)

theorem ob_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : OBK OS (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_unmapPd _ _ _)

theorem ob_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : OBK OS (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setPml4 _ _)

theorem ob_storePml4e (p : ObjRef) (pte : PML4E) : OBK OS (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_storePml4e _ _)

theorem ob_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : OBK OS (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_unmapPdpt _ _ _)

theorem ob_archFinaliseCap (c : ArchCap) (x : Bool) : OBK OS (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archFinaliseCap _ _)

theorem ob_archGetSanitiseRegisterInfo (_t : ObjRef) : OBK OS (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archGetSanitiseRegisterInfo _)

theorem ob_setOriginal (slot : CslotPtr) (v : Bool) : OBK OS (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setOriginal _ _)

theorem ob_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : OBK OS (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setUntypedCapAsFull _ _ _)

theorem ob_setCdt (t : Cdt) : OBK OS (setCdt (Z := Unit) t) := by
  unfold setCdt; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setCdt _)

theorem ob_updateCdt (f : Cdt → Cdt) : OBK OS (updateCdt (Z := Unit) f) := by
  unfold updateCdt; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_updateCdt _)

theorem ob_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : OBK OS (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_capInsert _ _ _)

theorem ob_setIrqState (state : IrqState) (irq : Irq) : OBK OS (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setIrqState _ _)

theorem ob_updateIrqState (irq : Irq) (irqState : X64IRQState) : OBK OS (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_updateIrqState _ _)

theorem ob_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : OBK OS m) : OBKE OS (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; ob_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible refine ob_withoutPreemption _ ?_)

theorem ob_archInvokeIrqControl (aic : ArchIrqControlInvocation) : OBKE OS (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archInvokeIrqControl _)

theorem ob_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : OBK OS (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archInvokeIrqHandler _)

theorem ob_archMaskIrqSignal (irq : Irq) : OBK OS (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archMaskIrqSignal _)

theorem ob_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : OBK OS (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_storeAsidPoolEntry _ _ _)

theorem ob_performAsidPoolInvocation (iv : AsidPoolInvocation) : OBK OS (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_performAsidPoolInvocation _)

theorem ob_performIoPortInvocation (i : IoPortInvocation) : OBK OS (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_performIoPortInvocation _)

theorem ob_setIoportMask (f l : IoPort) (val : Bool) : OBK OS (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setIoportMask _ _ _)

theorem ob_performIoportControlInvocation (i : IoPortControlInvocation) : OBK OS (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_performIoportControlInvocation _)

theorem ob_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : OBK OS (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_performPageDirectoryInvocation _)

theorem ob_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : OBK OS (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_performPageInvocationUnmap _ _)

theorem ob_performPageInvocation (iv : PageInvocation) : OBK OS (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_performPageInvocation _)

theorem ob_performPageTableInvocation (iv : PageTableInvocation) : OBK OS (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_performPageTableInvocation _)

theorem ob_performPdptInvocation (iv : PdptInvocation) : OBK OS (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_performPdptInvocation _)

theorem ob_freeIoportRange (f l : IoPort) : OBK OS (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_freeIoportRange _ _)

theorem ob_archPostCapDeletion (ac : ArchCap) : OBK OS (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archPostCapDeletion _)

theorem ob_archPostModifyRegisters (cur t : ObjRef) : OBK OS (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archPostModifyRegisters _ _)

theorem ob_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : OBK OS (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archPostResetUntyped _ _)

theorem ob_loadFpuState (t : ObjRef) : OBK OS (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_loadFpuState _)

theorem ob_saveFpuState (t : ObjRef) : OBK OS (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_saveFpuState _)

theorem ob_setX64CurrentFpuOwner (newOwner : Option ObjRef) : OBK OS (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setX64CurrentFpuOwner _)

theorem ob_switchLocalFpuOwner (newOwner : Option ObjRef) : OBK OS (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_switchLocalFpuOwner _)

theorem ob_fpuRelease (threadPtr : ObjRef) : OBK OS (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_fpuRelease _)

theorem ob_lazyFpuRestore (threadPtr : ObjRef) : OBK OS (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_lazyFpuRestore _)

theorem ob_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : OBK OS (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archPostSetFlags _ _)

theorem ob_archPrepareNextDomain  : OBK OS (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archPrepareNextDomain)

theorem ob_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : OBK OS (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archPrepareSetDomain _ _)

theorem ob_archSwitchToIdleThread  : OBK OS (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archSwitchToIdleThread)

theorem ob_archSwitchToThread (t : ObjRef) : OBK OS (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archSwitchToThread _)

theorem ob_getScRefillReady (scPtr : ObjRef) : OBK OS (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getScRefillReady _)

theorem ob_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : OBK OS (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getScRefillSufficient _ _)

theorem ob_getTcbQueue (d : Domain) (prio : Priority) : OBK OS (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getTcbQueue _ _)

theorem ob_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : OBK OS (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setTcbQueue _ _ _)

theorem ob_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : OBK OS (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_tcbSchedAction _ _)

theorem ob_rescheduleRequired  : OBK OS (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_rescheduleRequired)

theorem ob_possibleSwitchTo (target : ObjRef) : OBK OS (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_possibleSwitchTo _)

theorem ob_tcbReleaseRemove (tcbPtr : ObjRef) : OBK OS (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_tcbReleaseRemove _)

theorem ob_tcbReleaseDequeue  : OBK OS (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_tcbReleaseDequeue)

theorem ob_awaken  : OBK OS (awaken (Z := Unit)) := by
  unfold awaken; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_awaken)

theorem ob_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : OBK OS (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getSimpleKo _ _)

theorem ob_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : OBK OS (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_updateSkObjRef _ _ _ _)

theorem ob_bindNotification (tcbptr ntfnptr : ObjRef) : OBK OS (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_bindNotification _ _)

theorem ob_bindScReply (scPtr replyPtr : ObjRef) : OBK OS (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_bindScReply _ _)

theorem ob_getBlockingObject (state : ThreadState) : OBK OS (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getBlockingObject _)

theorem ob_replyUnlinkTcb (t r : ObjRef) : OBK OS (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_replyUnlinkTcb _ _)
end

end Fl4Proofs.P3.SInvDV
