/- sg1: idle-thread frame lemmas `IoK t` (ut7's SpecInvUtNK2 renamed; see SpecInvIoK1). -/
import Fl4Proofs.P3.SpecInvIoK1
open Classical

namespace Fl4Proofs.P3.SInvIo
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : IoPort → Bool}

theorem iok_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : IoK N (setPt (Z := Unit) ptr pt) := by
  unfold setPt; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_setPt _ _)

theorem iok_storePte (p : ObjRef) (pte : PTE) : IoK N (storePte (Z := Unit) p pte) := by
  unfold storePte; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_storePte _ _)

theorem iok_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : IoK N (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_unmapPage _ _ _ _)

theorem iok_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : IoK N (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_flushTable _ _ _ _)

theorem iok_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : IoK N (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_invalidatePageStructureCacheAsid _ _)

theorem iok_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : IoK N (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_unmapPageTable _ _ _)

theorem iok_flushAll (vspace : ObjRef) (asid : Asid) : IoK N (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_flushAll _ _)

theorem iok_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : IoK N (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_unmapPd _ _ _)

theorem iok_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : IoK N (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_setPml4 _ _)

theorem iok_storePml4e (p : ObjRef) (pte : PML4E) : IoK N (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_storePml4e _ _)

theorem iok_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : IoK N (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_unmapPdpt _ _ _)

theorem iok_archFinaliseCap (c : ArchCap) (x : Bool) : IoK N (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_archFinaliseCap _ _)

theorem iok_archGetSanitiseRegisterInfo (_t : ObjRef) : IoK N (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_archGetSanitiseRegisterInfo _)

theorem iok_setOriginal (slot : CslotPtr) (v : Bool) : IoK N (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_setOriginal _ _)

theorem iok_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : IoK N (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_setUntypedCapAsFull _ _ _)

theorem iok_setCdt (t : Cdt) : IoK N (setCdt (Z := Unit) t) := by
  unfold setCdt; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_setCdt _)

theorem iok_updateCdt (f : Cdt → Cdt) : IoK N (updateCdt (Z := Unit) f) := by
  unfold updateCdt; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_updateCdt _)

theorem iok_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : IoK N (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_capInsert _ _ _)

theorem iok_setIrqState (state : IrqState) (irq : Irq) : IoK N (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_setIrqState _ _)

theorem iok_updateIrqState (irq : Irq) (irqState : X64IRQState) : IoK N (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_updateIrqState _ _)

theorem iok_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : IoK N m) : IoKE N (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; iok_auto
  all_goals first | exact h_m
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible refine iok_withoutPreemption _ ?_)

theorem iok_archInvokeIrqControl (aic : ArchIrqControlInvocation) : IoKE N (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_archInvokeIrqControl _)

theorem iok_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : IoK N (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_archInvokeIrqHandler _)

theorem iok_archMaskIrqSignal (irq : Irq) : IoK N (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_archMaskIrqSignal _)

theorem iok_performAsidControlInvocation (iv : AsidControlInvocation) : IoK N (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_performAsidControlInvocation _)

theorem iok_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : IoK N (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_storeAsidPoolEntry _ _ _)

theorem iok_performAsidPoolInvocation (iv : AsidPoolInvocation) : IoK N (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_performAsidPoolInvocation _)

theorem iok_portIn (f : MachineMonad Data) : IoK N (portIn (Z := Unit) f) := by
  unfold portIn; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_portIn _)

theorem iok_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : IoK N (portOut (Z := Unit) f w) := by
  unfold portOut; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_portOut _ _)

theorem iok_performIoPortInvocation (i : IoPortInvocation) : IoK N (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_performIoPortInvocation _)

theorem iok_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : IoK N (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_performPageDirectoryInvocation _)

theorem iok_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : IoK N (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_performPageInvocationUnmap _ _)

theorem iok_performPageInvocation (iv : PageInvocation) : IoK N (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_performPageInvocation _)

theorem iok_performPageTableInvocation (iv : PageTableInvocation) : IoK N (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_performPageTableInvocation _)

theorem iok_performPdptInvocation (iv : PdptInvocation) : IoK N (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_performPdptInvocation _)

theorem iok_archPostModifyRegisters (cur t : ObjRef) : IoK N (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_archPostModifyRegisters _ _)

theorem iok_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : IoK N (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_archPostResetUntyped _ _)

theorem iok_loadFpuState (t : ObjRef) : IoK N (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_loadFpuState _)

theorem iok_saveFpuState (t : ObjRef) : IoK N (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_saveFpuState _)

theorem iok_setX64CurrentFpuOwner (newOwner : Option ObjRef) : IoK N (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_setX64CurrentFpuOwner _)

theorem iok_switchLocalFpuOwner (newOwner : Option ObjRef) : IoK N (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_switchLocalFpuOwner _)

theorem iok_fpuRelease (threadPtr : ObjRef) : IoK N (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_fpuRelease _)

theorem iok_lazyFpuRestore (threadPtr : ObjRef) : IoK N (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_lazyFpuRestore _)

theorem iok_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : IoK N (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_archPostSetFlags _ _)

theorem iok_archPrepareNextDomain  : IoK N (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_archPrepareNextDomain)

theorem iok_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : IoK N (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_archPrepareSetDomain _ _)

theorem iok_archSwitchToIdleThread  : IoK N (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_archSwitchToIdleThread)

theorem iok_archSwitchToThread (t : ObjRef) : IoK N (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_archSwitchToThread _)

theorem iok_getScRefillReady (scPtr : ObjRef) : IoK N (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getScRefillReady _)

theorem iok_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : IoK N (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getScRefillSufficient _ _)

theorem iok_getTcbQueue (d : Domain) (prio : Priority) : IoK N (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getTcbQueue _ _)

theorem iok_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : IoK N (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_setTcbQueue _ _ _)

theorem iok_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : IoK N (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_tcbSchedAction _ _)

theorem iok_rescheduleRequired  : IoK N (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_rescheduleRequired)

theorem iok_possibleSwitchTo (target : ObjRef) : IoK N (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_possibleSwitchTo _)

theorem iok_tcbReleaseRemove (tcbPtr : ObjRef) : IoK N (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_tcbReleaseRemove _)

theorem iok_tcbReleaseDequeue  : IoK N (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_tcbReleaseDequeue)

theorem iok_awaken  : IoK N (awaken (Z := Unit)) := by
  unfold awaken; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_awaken)

theorem iok_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : IoK N (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getSimpleKo _ _)

theorem iok_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : IoK N (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_updateSkObjRef _ _ _ _)

theorem iok_bindNotification (tcbptr ntfnptr : ObjRef) : IoK N (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_bindNotification _ _)

theorem iok_bindScReply (scPtr replyPtr : ObjRef) : IoK N (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_bindScReply _ _)

theorem iok_getBlockingObject (state : ThreadState) : IoK N (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getBlockingObject _)

theorem iok_replyUnlinkTcb (t r : ObjRef) : IoK N (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_replyUnlinkTcb _ _)
end

end Fl4Proofs.P3.SInvIo
