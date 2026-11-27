/- s27: global-PML4 frame lemmas `GpK g` (sg1's SpecInvSgI2 renamed; see SpecInvGpK1). -/
import Fl4Proofs.P3.SpecInvGpK1
open Classical

namespace Fl4Proofs.P3.SInvGp
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem gpk_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : GpK N (setPt (Z := Unit) ptr pt) := by
  unfold setPt; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setPt _ _)

theorem gpk_storePte (p : ObjRef) (pte : PTE) : GpK N (storePte (Z := Unit) p pte) := by
  unfold storePte; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_storePte _ _)

theorem gpk_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : GpK N (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_unmapPage _ _ _ _)

theorem gpk_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : GpK N (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_flushTable _ _ _ _)

theorem gpk_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : GpK N (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_invalidatePageStructureCacheAsid _ _)

theorem gpk_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : GpK N (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_unmapPageTable _ _ _)

theorem gpk_flushAll (vspace : ObjRef) (asid : Asid) : GpK N (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_flushAll _ _)

theorem gpk_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : GpK N (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_unmapPd _ _ _)

theorem gpk_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : GpK N (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setPml4 _ _)

theorem gpk_storePml4e (p : ObjRef) (pte : PML4E) : GpK N (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_storePml4e _ _)

theorem gpk_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : GpK N (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_unmapPdpt _ _ _)

theorem gpk_archFinaliseCap (c : ArchCap) (x : Bool) : GpK N (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archFinaliseCap _ _)

theorem gpk_archGetSanitiseRegisterInfo (_t : ObjRef) : GpK N (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archGetSanitiseRegisterInfo _)

theorem gpk_setOriginal (slot : CslotPtr) (v : Bool) : GpK N (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setOriginal _ _)

theorem gpk_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : GpK N (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setUntypedCapAsFull _ _ _)

theorem gpk_setCdt (t : Cdt) : GpK N (setCdt (Z := Unit) t) := by
  unfold setCdt; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setCdt _)

theorem gpk_updateCdt (f : Cdt → Cdt) : GpK N (updateCdt (Z := Unit) f) := by
  unfold updateCdt; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_updateCdt _)

theorem gpk_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : GpK N (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_capInsert _ _ _)

theorem gpk_setIrqState (state : IrqState) (irq : Irq) : GpK N (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setIrqState _ _)

theorem gpk_updateIrqState (irq : Irq) (irqState : X64IRQState) : GpK N (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_updateIrqState _ _)

theorem gpk_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : GpK N m) : GpKE N (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; gpk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible refine gpk_withoutPreemption _ ?_)

theorem gpk_archInvokeIrqControl (aic : ArchIrqControlInvocation) : GpKE N (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archInvokeIrqControl _)

theorem gpk_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : GpK N (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archInvokeIrqHandler _)

theorem gpk_archMaskIrqSignal (irq : Irq) : GpK N (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archMaskIrqSignal _)

theorem gpk_performAsidControlInvocation (iv : AsidControlInvocation) : GpK N (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_performAsidControlInvocation _)

theorem gpk_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : GpK N (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_storeAsidPoolEntry _ _ _)

theorem gpk_performAsidPoolInvocation (iv : AsidPoolInvocation) : GpK N (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_performAsidPoolInvocation _)

theorem gpk_portIn (f : MachineMonad Data) : GpK N (portIn (Z := Unit) f) := by
  unfold portIn; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_portIn _)

theorem gpk_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : GpK N (portOut (Z := Unit) f w) := by
  unfold portOut; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_portOut _ _)

theorem gpk_performIoPortInvocation (i : IoPortInvocation) : GpK N (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_performIoPortInvocation _)

theorem gpk_setIoportMask (f l : IoPort) (val : Bool) : GpK N (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setIoportMask _ _ _)

theorem gpk_performIoportControlInvocation (i : IoPortControlInvocation) : GpK N (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_performIoportControlInvocation _)

theorem gpk_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : GpK N (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_performPageDirectoryInvocation _)

theorem gpk_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : GpK N (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_performPageInvocationUnmap _ _)

theorem gpk_performPageInvocation (iv : PageInvocation) : GpK N (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_performPageInvocation _)

theorem gpk_performPageTableInvocation (iv : PageTableInvocation) : GpK N (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_performPageTableInvocation _)

theorem gpk_performPdptInvocation (iv : PdptInvocation) : GpK N (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_performPdptInvocation _)

theorem gpk_archPerformInvocation (i : ArchInvocation) : GpKE N (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archPerformInvocation _)

theorem gpk_freeIoportRange (f l : IoPort) : GpK N (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_freeIoportRange _ _)

theorem gpk_archPostCapDeletion (ac : ArchCap) : GpK N (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archPostCapDeletion _)

theorem gpk_archPostModifyRegisters (cur t : ObjRef) : GpK N (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archPostModifyRegisters _ _)

theorem gpk_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : GpK N (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archPostResetUntyped _ _)

theorem gpk_loadFpuState (t : ObjRef) : GpK N (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_loadFpuState _)

theorem gpk_saveFpuState (t : ObjRef) : GpK N (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_saveFpuState _)

theorem gpk_setX64CurrentFpuOwner (newOwner : Option ObjRef) : GpK N (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setX64CurrentFpuOwner _)

theorem gpk_switchLocalFpuOwner (newOwner : Option ObjRef) : GpK N (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_switchLocalFpuOwner _)

theorem gpk_fpuRelease (threadPtr : ObjRef) : GpK N (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fpuRelease _)

theorem gpk_lazyFpuRestore (threadPtr : ObjRef) : GpK N (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_lazyFpuRestore _)

theorem gpk_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : GpK N (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archPostSetFlags _ _)

theorem gpk_archPrepareNextDomain  : GpK N (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archPrepareNextDomain)

theorem gpk_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : GpK N (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archPrepareSetDomain _ _)

theorem gpk_archSwitchToIdleThread  : GpK N (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archSwitchToIdleThread)

theorem gpk_archSwitchToThread (t : ObjRef) : GpK N (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archSwitchToThread _)

theorem gpk_getScRefillReady (scPtr : ObjRef) : GpK N (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getScRefillReady _)

theorem gpk_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : GpK N (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getScRefillSufficient _ _)

theorem gpk_getTcbQueue (d : Domain) (prio : Priority) : GpK N (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getTcbQueue _ _)

theorem gpk_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : GpK N (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setTcbQueue _ _ _)

theorem gpk_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : GpK N (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_tcbSchedAction _ _)

theorem gpk_rescheduleRequired  : GpK N (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_rescheduleRequired)

theorem gpk_possibleSwitchTo (target : ObjRef) : GpK N (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_possibleSwitchTo _)

theorem gpk_tcbReleaseRemove (tcbPtr : ObjRef) : GpK N (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_tcbReleaseRemove _)

theorem gpk_tcbReleaseDequeue  : GpK N (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_tcbReleaseDequeue)

theorem gpk_awaken  : GpK N (awaken (Z := Unit)) := by
  unfold awaken; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_awaken)

theorem gpk_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : GpK N (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getSimpleKo _ _)

theorem gpk_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : GpK N (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_updateSkObjRef _ _ _ _)

theorem gpk_bindNotification (tcbptr ntfnptr : ObjRef) : GpK N (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_bindNotification _ _)

theorem gpk_bindScReply (scPtr replyPtr : ObjRef) : GpK N (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_bindScReply _ _)

theorem gpk_getBlockingObject (state : ThreadState) : GpK N (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getBlockingObject _)

theorem gpk_replyUnlinkTcb (t r : ObjRef) : GpK N (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_replyUnlinkTcb _ _)
end

end Fl4Proofs.P3.SInvGp
