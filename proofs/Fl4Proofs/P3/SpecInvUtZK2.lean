/- g5g: the memory half `YK D F` of untyped_ranges_zero, part 2 (sg1's SpecInvSgI2 renamed; see SpecInvUtZK1). -/
import Fl4Proofs.P3.SpecInvUtZK1
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {PD : PgSet} {FS : Set Nat}


theorem yk_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : YK PD FS (setPt (Z := Unit) ptr pt) := by
  unfold setPt; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setPt _ _)

theorem yk_storePte (p : ObjRef) (pte : PTE) : YK PD FS (storePte (Z := Unit) p pte) := by
  unfold storePte; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_storePte _ _)

theorem yk_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : YK PD FS (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_unmapPage _ _ _ _)

theorem yk_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : YK PD FS (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_flushTable _ _ _ _)

theorem yk_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : YK PD FS (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_invalidatePageStructureCacheAsid _ _)

theorem yk_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : YK PD FS (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_unmapPageTable _ _ _)

theorem yk_flushAll (vspace : ObjRef) (asid : Asid) : YK PD FS (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_flushAll _ _)

theorem yk_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : YK PD FS (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_unmapPd _ _ _)

theorem yk_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : YK PD FS (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setPml4 _ _)

theorem yk_storePml4e (p : ObjRef) (pte : PML4E) : YK PD FS (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_storePml4e _ _)

theorem yk_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : YK PD FS (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_unmapPdpt _ _ _)

theorem yk_archFinaliseCap (c : ArchCap) (x : Bool) : YK PD FS (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archFinaliseCap _ _)

theorem yk_archGetSanitiseRegisterInfo (_t : ObjRef) : YK PD FS (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archGetSanitiseRegisterInfo _)

theorem yk_setOriginal (slot : CslotPtr) (v : Bool) : YK PD FS (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setOriginal _ _)

theorem yk_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : YK PD FS (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setUntypedCapAsFull _ _ _)

theorem yk_setCdt (t : Cdt) : YK PD FS (setCdt (Z := Unit) t) := by
  unfold setCdt; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setCdt _)

theorem yk_updateCdt (f : Cdt → Cdt) : YK PD FS (updateCdt (Z := Unit) f) := by
  unfold updateCdt; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_updateCdt _)

theorem yk_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : YK PD FS (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_capInsert _ _ _)

theorem yk_setIrqState (state : IrqState) (irq : Irq) : YK PD FS (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setIrqState _ _)

theorem yk_updateIrqState (irq : Irq) (irqState : X64IRQState) : YK PD FS (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_updateIrqState _ _)

theorem yk_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : YK PD FS m) : YKE PD FS (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; yk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_withoutPreemption _ ?_)

theorem yk_archInvokeIrqControl (aic : ArchIrqControlInvocation) : YKE PD FS (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archInvokeIrqControl _)

theorem yk_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : YK PD FS (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archInvokeIrqHandler _)

theorem yk_archMaskIrqSignal (irq : Irq) : YK PD FS (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archMaskIrqSignal _)

theorem yk_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : YK PD FS (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_storeAsidPoolEntry _ _ _)

theorem yk_performAsidPoolInvocation (iv : AsidPoolInvocation) : YK PD FS (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_performAsidPoolInvocation _)

theorem yk_performIoPortInvocation (i : IoPortInvocation) : YK PD FS (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_performIoPortInvocation _)

theorem yk_setIoportMask (f l : IoPort) (val : Bool) : YK PD FS (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setIoportMask _ _ _)

theorem yk_performIoportControlInvocation (i : IoPortControlInvocation) : YK PD FS (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_performIoportControlInvocation _)

theorem yk_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : YK PD FS (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_performPageDirectoryInvocation _)

theorem yk_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : YK PD FS (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_performPageInvocationUnmap _ _)

theorem yk_performPageInvocation (iv : PageInvocation) : YK PD FS (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_performPageInvocation _)

theorem yk_performPageTableInvocation (iv : PageTableInvocation) : YK PD FS (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_performPageTableInvocation _)

theorem yk_performPdptInvocation (iv : PdptInvocation) : YK PD FS (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_performPdptInvocation _)

theorem yk_freeIoportRange (f l : IoPort) : YK PD FS (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_freeIoportRange _ _)

theorem yk_archPostCapDeletion (ac : ArchCap) : YK PD FS (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archPostCapDeletion _)

theorem yk_archPostModifyRegisters (cur t : ObjRef) : YK PD FS (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archPostModifyRegisters _ _)

theorem yk_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : YK PD FS (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archPostResetUntyped _ _)

theorem yk_loadFpuState (t : ObjRef) : YK PD FS (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_loadFpuState _)

theorem yk_saveFpuState (t : ObjRef) : YK PD FS (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_saveFpuState _)

theorem yk_setX64CurrentFpuOwner (newOwner : Option ObjRef) : YK PD FS (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setX64CurrentFpuOwner _)

theorem yk_switchLocalFpuOwner (newOwner : Option ObjRef) : YK PD FS (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_switchLocalFpuOwner _)

theorem yk_fpuRelease (threadPtr : ObjRef) : YK PD FS (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_fpuRelease _)

theorem yk_lazyFpuRestore (threadPtr : ObjRef) : YK PD FS (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_lazyFpuRestore _)

theorem yk_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : YK PD FS (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archPostSetFlags _ _)

theorem yk_archPrepareNextDomain  : YK PD FS (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archPrepareNextDomain)

theorem yk_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : YK PD FS (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archPrepareSetDomain _ _)

theorem yk_archSwitchToIdleThread  : YK PD FS (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archSwitchToIdleThread)

theorem yk_archSwitchToThread (t : ObjRef) : YK PD FS (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archSwitchToThread _)

theorem yk_getScRefillReady (scPtr : ObjRef) : YK PD FS (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getScRefillReady _)

theorem yk_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : YK PD FS (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getScRefillSufficient _ _)

theorem yk_getTcbQueue (d : Domain) (prio : Priority) : YK PD FS (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getTcbQueue _ _)

theorem yk_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : YK PD FS (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setTcbQueue _ _ _)

theorem yk_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : YK PD FS (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_tcbSchedAction _ _)

theorem yk_rescheduleRequired  : YK PD FS (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_rescheduleRequired)

theorem yk_possibleSwitchTo (target : ObjRef) : YK PD FS (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_possibleSwitchTo _)

theorem yk_tcbReleaseRemove (tcbPtr : ObjRef) : YK PD FS (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_tcbReleaseRemove _)

theorem yk_tcbReleaseDequeue  : YK PD FS (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_tcbReleaseDequeue)

theorem yk_awaken  : YK PD FS (awaken (Z := Unit)) := by
  unfold awaken; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_awaken)

theorem yk_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : YK PD FS (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getSimpleKo _ _)

theorem yk_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : YK PD FS (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_updateSkObjRef _ _ _ _)

theorem yk_bindNotification (tcbptr ntfnptr : ObjRef) : YK PD FS (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_bindNotification _ _)

theorem yk_bindScReply (scPtr replyPtr : ObjRef) : YK PD FS (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_bindScReply _ _)

theorem yk_getBlockingObject (state : ThreadState) : YK PD FS (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getBlockingObject _)

theorem yk_replyUnlinkTcb (t r : ObjRef) : YK PD FS (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_replyUnlinkTcb _ _)
end

end Fl4Proofs.P3.SInvUZ
