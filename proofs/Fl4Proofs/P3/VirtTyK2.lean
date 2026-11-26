/- virt gen 3: the object-type family `TYK`, part 2 (SpecInvDvK2 with `aType` for `objBits`, proofs/scratch/virt/mkty.py; see VirtTyK1). -/
import Fl4Proofs.P3.VirtTyK1
open Classical

namespace Fl4Proofs.P3.SInvTY
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {OS : TySet}



theorem ty_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : TYK OS (setPt (Z := Unit) ptr pt) := by
  unfold setPt; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setPt _ _)

theorem ty_storePte (p : ObjRef) (pte : PTE) : TYK OS (storePte (Z := Unit) p pte) := by
  unfold storePte; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_storePte _ _)

theorem ty_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : TYK OS (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_unmapPage _ _ _ _)

theorem ty_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : TYK OS (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_flushTable _ _ _ _)

theorem ty_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : TYK OS (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_invalidatePageStructureCacheAsid _ _)

theorem ty_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : TYK OS (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_unmapPageTable _ _ _)

theorem ty_flushAll (vspace : ObjRef) (asid : Asid) : TYK OS (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_flushAll _ _)

theorem ty_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : TYK OS (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_unmapPd _ _ _)

theorem ty_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : TYK OS (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setPml4 _ _)

theorem ty_storePml4e (p : ObjRef) (pte : PML4E) : TYK OS (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_storePml4e _ _)

theorem ty_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : TYK OS (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_unmapPdpt _ _ _)

theorem ty_archFinaliseCap (c : ArchCap) (x : Bool) : TYK OS (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archFinaliseCap _ _)

theorem ty_archGetSanitiseRegisterInfo (_t : ObjRef) : TYK OS (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archGetSanitiseRegisterInfo _)

theorem ty_setOriginal (slot : CslotPtr) (v : Bool) : TYK OS (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setOriginal _ _)

theorem ty_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : TYK OS (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setUntypedCapAsFull _ _ _)

theorem ty_setCdt (t : Cdt) : TYK OS (setCdt (Z := Unit) t) := by
  unfold setCdt; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setCdt _)

theorem ty_updateCdt (f : Cdt → Cdt) : TYK OS (updateCdt (Z := Unit) f) := by
  unfold updateCdt; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_updateCdt _)

theorem ty_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : TYK OS (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_capInsert _ _ _)

theorem ty_setIrqState (state : IrqState) (irq : Irq) : TYK OS (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setIrqState _ _)

theorem ty_updateIrqState (irq : Irq) (irqState : X64IRQState) : TYK OS (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_updateIrqState _ _)

theorem ty_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : TYK OS m) : TYKE OS (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; ty_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible refine ty_withoutPreemption _ ?_)

theorem ty_archInvokeIrqControl (aic : ArchIrqControlInvocation) : TYKE OS (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archInvokeIrqControl _)

theorem ty_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : TYK OS (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archInvokeIrqHandler _)

theorem ty_archMaskIrqSignal (irq : Irq) : TYK OS (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archMaskIrqSignal _)

theorem ty_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : TYK OS (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_storeAsidPoolEntry _ _ _)

theorem ty_performAsidPoolInvocation (iv : AsidPoolInvocation) : TYK OS (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_performAsidPoolInvocation _)

theorem ty_performIoPortInvocation (i : IoPortInvocation) : TYK OS (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_performIoPortInvocation _)

theorem ty_setIoportMask (f l : IoPort) (val : Bool) : TYK OS (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setIoportMask _ _ _)

theorem ty_performIoportControlInvocation (i : IoPortControlInvocation) : TYK OS (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_performIoportControlInvocation _)

theorem ty_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : TYK OS (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_performPageDirectoryInvocation _)

theorem ty_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : TYK OS (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_performPageInvocationUnmap _ _)

theorem ty_performPageInvocation (iv : PageInvocation) : TYK OS (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_performPageInvocation _)

theorem ty_performPageTableInvocation (iv : PageTableInvocation) : TYK OS (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_performPageTableInvocation _)

theorem ty_performPdptInvocation (iv : PdptInvocation) : TYK OS (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_performPdptInvocation _)

theorem ty_freeIoportRange (f l : IoPort) : TYK OS (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_freeIoportRange _ _)

theorem ty_archPostCapDeletion (ac : ArchCap) : TYK OS (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archPostCapDeletion _)

theorem ty_archPostModifyRegisters (cur t : ObjRef) : TYK OS (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archPostModifyRegisters _ _)

theorem ty_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : TYK OS (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archPostResetUntyped _ _)

theorem ty_loadFpuState (t : ObjRef) : TYK OS (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_loadFpuState _)

theorem ty_saveFpuState (t : ObjRef) : TYK OS (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_saveFpuState _)

theorem ty_setX64CurrentFpuOwner (newOwner : Option ObjRef) : TYK OS (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setX64CurrentFpuOwner _)

theorem ty_switchLocalFpuOwner (newOwner : Option ObjRef) : TYK OS (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_switchLocalFpuOwner _)

theorem ty_fpuRelease (threadPtr : ObjRef) : TYK OS (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_fpuRelease _)

theorem ty_lazyFpuRestore (threadPtr : ObjRef) : TYK OS (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_lazyFpuRestore _)

theorem ty_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : TYK OS (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archPostSetFlags _ _)

theorem ty_archPrepareNextDomain  : TYK OS (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archPrepareNextDomain)

theorem ty_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : TYK OS (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archPrepareSetDomain _ _)

theorem ty_archSwitchToIdleThread  : TYK OS (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archSwitchToIdleThread)

theorem ty_archSwitchToThread (t : ObjRef) : TYK OS (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archSwitchToThread _)

theorem ty_getScRefillReady (scPtr : ObjRef) : TYK OS (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getScRefillReady _)

theorem ty_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : TYK OS (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getScRefillSufficient _ _)

theorem ty_getTcbQueue (d : Domain) (prio : Priority) : TYK OS (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getTcbQueue _ _)

theorem ty_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : TYK OS (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setTcbQueue _ _ _)

theorem ty_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : TYK OS (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_tcbSchedAction _ _)

theorem ty_rescheduleRequired  : TYK OS (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_rescheduleRequired)

theorem ty_possibleSwitchTo (target : ObjRef) : TYK OS (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_possibleSwitchTo _)

theorem ty_tcbReleaseRemove (tcbPtr : ObjRef) : TYK OS (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_tcbReleaseRemove _)

theorem ty_tcbReleaseDequeue  : TYK OS (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_tcbReleaseDequeue)

theorem ty_awaken  : TYK OS (awaken (Z := Unit)) := by
  unfold awaken; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_awaken)

theorem ty_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : TYK OS (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getSimpleKo _ _)

theorem ty_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : TYK OS (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_updateSkObjRef _ _ _ _)

theorem ty_bindNotification (tcbptr ntfnptr : ObjRef) : TYK OS (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_bindNotification _ _)

theorem ty_bindScReply (scPtr replyPtr : ObjRef) : TYK OS (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_bindScReply _ _)

theorem ty_getBlockingObject (state : ThreadState) : TYK OS (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getBlockingObject _)

theorem ty_replyUnlinkTcb (t r : ObjRef) : TYK OS (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_replyUnlinkTcb _ _)
end

end Fl4Proofs.P3.SInvTY
