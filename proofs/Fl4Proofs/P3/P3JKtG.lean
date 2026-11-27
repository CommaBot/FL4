/-
P3 (line p3J, gen 21): **`KQ` leaves of the spec functions** (P3JKtF's heap-type frame), a scripted copy of
SpecInvDomG (`scratch/p3J/genKt.py`), without the heap writers `retype_region` / `delete_objects` and their
callers (the untyped invocation and reset; `scratch/p3J/kt/skip.txt`).

Named premises: none. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JKtF
import Fl4Proofs.P3.SpecInvDomL
import Fl4Proofs.P3.SpecInvFbD
open Classical

namespace Fl4Proofs.P3.SInvKt
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

set_option maxRecDepth 20000

theorem kq_setCap (c : Cap) (sl : CslotPtr) : KQ (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setCap _ _)

theorem kq_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    KQ (portOut (Z := Unit) f w) := by
  unfold portOut; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_portOut _ _)

theorem kq_getPt (ptr : ObjRef) : KQ (getPt (Z := Unit) ptr) := by
  unfold getPt; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getPt _)

theorem kq_getPte (ptr : ObjRef) : KQ (getPte (Z := Unit) ptr) := by
  unfold getPte; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getPte _)

theorem kq_getPd (ptr : ObjRef) : KQ (getPd (Z := Unit) ptr) := by
  unfold getPd; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getPd _)

theorem kq_getPde (ptr : ObjRef) : KQ (getPde (Z := Unit) ptr) := by
  unfold getPde; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getPde _)

theorem kq_getPml4 (ptr : ObjRef) : KQ (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getPml4 _)

theorem kq_getPml4e (ptr : ObjRef) : KQ (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getPml4e _)

theorem kq_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : KQE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_lookupPdptSlot _ _)

theorem kq_getPdpt (ptr : ObjRef) : KQ (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getPdpt _)

theorem kq_getPdpte (ptr : ObjRef) : KQ (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getPdpte _)

theorem kq_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : KQE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_lookupPdSlot _ _)

theorem kq_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : KQE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_lookupPtSlot _ _)

theorem kq_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : KQ (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setPdpt _ _)

theorem kq_storePdpte (p : ObjRef) (pte : PDPTE) : KQ (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_storePdpte _ _)

theorem kq_getAsidPool (ptr : ObjRef) : KQ (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getAsidPool _)

theorem kq_findVspaceForAsid (asid : Asid) : KQE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_findVspaceForAsid _)

theorem kq_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : KQ (setPt (Z := Unit) ptr pt) := by
  unfold setPt; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setPt _ _)

theorem kq_storePte (p : ObjRef) (pte : PTE) : KQ (storePte (Z := Unit) p pte) := by
  unfold storePte; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_storePte _ _)

theorem kq_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : KQ (setPd (Z := Unit) ptr pd) := by
  unfold setPd; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setPd _ _)

theorem kq_storePde (p : ObjRef) (pde : PDE) : KQ (storePde (Z := Unit) p pde) := by
  unfold storePde; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_storePde _ _)

theorem kq_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : KQ (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_unmapPage _ _ _ _)

theorem kq_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : KQ (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_performPageInvocationUnmap _ _)

theorem kq_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : KQ (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setAsidPool _ _)

theorem kq_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : KQ (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_flushTable _ _ _ _)

theorem kq_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : KQ (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setPml4 _ _)

theorem kq_setOriginal (slot : CslotPtr) (v : Bool) : KQ (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setOriginal _ _)

theorem kq_updateCdt (f : Cdt → Cdt) : KQ (updateCdt (Z := Unit) f) := by
  unfold updateCdt; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_updateCdt _)

theorem kq_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : KQ (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setUntypedCapAsFull _ _ _)


theorem kq_storePml4e (p : ObjRef) (pte : PML4E) : KQ (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_storePml4e _ _)

theorem kq_flushAll (vspace : ObjRef) (asid : Asid) : KQ (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_flushAll _ _)

theorem kq_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : KQ (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_unmapPdpt _ _ _)

theorem kq_setIoportMask (f l : IoPort) (val : Bool) : KQ (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setIoportMask _ _ _)

theorem kq_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : KQ (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_invalidatePageStructureCacheAsid _ _)

theorem kq_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : KQ (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_unmapPd _ _ _)


theorem kq_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : KQ (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_capInsert _ _ _)

theorem kq_portIn (f : MachineMonad Data) : KQ (portIn (Z := Unit) f) := by
  unfold portIn; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_portIn _)

theorem kq_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : KQ (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_unmapPageTable _ _ _)

theorem kq_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : KQ (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_storeAsidPoolEntry _ _ _)

theorem kq_performPageInvocation (iv : PageInvocation) : KQ (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_performPageInvocation _)

theorem kq_performPageTableInvocation (iv : PageTableInvocation) : KQ (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_performPageTableInvocation _)

theorem kq_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : KQ (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_performPageDirectoryInvocation _)

theorem kq_performPdptInvocation (iv : PdptInvocation) : KQ (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_performPdptInvocation _)

theorem kq_performAsidPoolInvocation (iv : AsidPoolInvocation) : KQ (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_performAsidPoolInvocation _)


theorem kq_performIoPortInvocation (i : IoPortInvocation) : KQ (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_performIoPortInvocation _)

theorem kq_performIoportControlInvocation (i : IoPortControlInvocation) : KQ (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_performIoportControlInvocation _)

theorem kq_performDeriveSubframe (iv : Fl4SubframeInvocation) : KQ (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_performDeriveSubframe _)

theorem kq_performTestAndClearAccessed (_slot : ObjRef) : KQ (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_performTestAndClearAccessed _)

theorem kq_performPml4Flush (i : Fl4Pml4Invocation) : KQ (performPml4Flush (Z := Unit) i) := by
  cases i; unfold performPml4Flush; exact kq_flushAll _ _

theorem kq_threadSet' (f : Tcb → Tcb) (t : ObjRef) : KQ (threadSet (Z := Unit) f t) := by
  unfold threadSet; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_threadSet' _ _)

theorem kq_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : KQ (threadGet (Z := Unit) f t) := by
  unfold threadGet; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_threadGet' _ _)

theorem kq_setThreadState' (t : ObjRef) (ts : ThreadState) : KQ (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setThreadState' _ _)

theorem kq_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    KQ (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getSimpleKo' _ _)

theorem kq_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    KQ (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setSimpleKo' _ _ _)

theorem kq_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    KQ (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_updateSkObjRef' _ _ _ _)

theorem kq_getSchedContext' (q : ObjRef) : KQ (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getSchedContext' _)

theorem kq_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    KQ (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_updateSchedContext' _ _)

theorem kq_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : KQ (asUser (Z := Unit) t u) := by
  unfold asUser; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_asUser' _ _)

theorem kq_replyUnlinkTcb' (t r : ObjRef) : KQ (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_replyUnlinkTcb' _ _)

theorem kq_getThreadState' (t : ObjRef) : KQ (getThreadState (Z := Unit) t) := by
  unfold getThreadState; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getThreadState' _)

theorem kq_cancelIpc' (t : ObjRef) : KQ (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_cancelIpc' _)

theorem kq_suspend' (t : ObjRef) : KQ (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc tcbSchedAction getTcbQueue setTcbQueue tcbReleaseRemove
    schedContextCancelYieldTo getTcbObjRef getThreadState
  kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_suspend' _)

theorem kq_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : KQ (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getSkObjRef' _ _ _)

theorem kq_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : KQ (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getScObjRef' _ _)

theorem kq_getIrqSlot' (irq : Irq) : KQ (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getIrqSlot' _)

theorem kq_isFinalCap' (c : Cap) : KQ (isFinalCap (Z := Unit) c) := by
  unfold isFinalCap; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_isFinalCap' _)

theorem kq_hwAsidInvalidate' (a : Asid) (v : ObjRef) : KQ (hwAsidInvalidate (Z := Unit) a v) := by
  unfold hwAsidInvalidate; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_hwAsidInvalidate' _ _)

theorem kq_getCurrentCr3' : KQ (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getCurrentCr3' )

theorem kq_setCurrentCr3' (c : Cr3) : KQ (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setCurrentCr3' _)

theorem kq_setCurrentVspaceRoot' (v : ObjRef) (a : Asid) : KQ (setCurrentVspaceRoot (Z := Unit) v a) := by
  unfold setCurrentVspaceRoot; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setCurrentVspaceRoot' _ _)

theorem kq_setVmRoot' (t : ObjRef) : KQ (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setVmRoot' _)

theorem kq_freeIoportRange' (f l : IoPort) : KQ (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_freeIoportRange' _ _)

theorem kq_setIrqState' (i : IrqState) (irq : Irq) : KQ (setIrqState (Z := Unit) i irq) := by
  unfold setIrqState; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setIrqState' _ _)

theorem kq_deletedIrqHandler' (irq : Irq) : KQ (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_deletedIrqHandler' _)

theorem kq_lookupIpcBuffer' (b : Bool) (t : ObjRef) : KQ (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_lookupIpcBuffer' _ _)

theorem kq_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : KQ (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_storeWordOffs' _ _ _)

theorem kq_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : KQ (setMrs (Z := Unit) t b m) := by
  unfold setMrs; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setMrs' _ _ _)

theorem kq_setMessageInfo' (t : ObjRef) (i : MessageInfo) : KQ (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setMessageInfo' _ _)

theorem kq_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : KQ (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_archThreadSet' _ _)

theorem kq_saveFpuState' (t : ObjRef) : KQ (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_saveFpuState' _)

theorem kq_loadFpuState' (t : ObjRef) : KQ (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_loadFpuState' _)

theorem kq_setX64CurrentFpuOwner' (o : Option ObjRef) : KQ (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setX64CurrentFpuOwner' _)

theorem kq_switchLocalFpuOwner' (o : Option ObjRef) : KQ (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_switchLocalFpuOwner' _)

theorem kq_getTcbQueue' (d : Domain) (p : Priority) : KQ (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getTcbQueue' _ _)

theorem kq_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : KQ (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setTcbQueue' _ _ _)

theorem kq_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : KQ (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_tcbSchedAction' _ _)

theorem kq_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : KQ (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getTcbObjRef' _ _)

theorem kq_setSchedulerAction' (a : SchedulerAction) : KQ (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setSchedulerAction' _)

theorem kq_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : KQ (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getScRefillSufficient' _ _)

theorem kq_getScRefillReady' (sc : ObjRef) : KQ (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getScRefillReady' _)

theorem kq_tcbReleaseRemove' (t : ObjRef) : KQ (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_tcbReleaseRemove' _)

theorem kq_rescheduleRequired' : KQ (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_rescheduleRequired' )

theorem kq_testReschedule' (t : ObjRef) : KQ (testReschedule (Z := Unit) t) := by
  unfold testReschedule; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_testReschedule' _)

theorem kq_possibleSwitchTo' (t : ObjRef) : KQ (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_possibleSwitchTo' _)

theorem kq_tcbEpDequeue' (t e : ObjRef) : KQ (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_tcbEpDequeue' _ _)

theorem kq_tcbNtfnDequeue' (t n : ObjRef) : KQ (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_tcbNtfnDequeue' _ _)

theorem kq_isRoundRobin' (sc : ObjRef) : KQ (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_isRoundRobin' _)

theorem kq_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : KQ (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_updateRefillHd' _ _)

theorem kq_getRefillHead' (sc : ObjRef) : KQ (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getRefillHead' _)

theorem kq_refillPopHead' (sc : ObjRef) : KQ (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_refillPopHead' _)

theorem kq_mergeOverlappingRefills' (sc : ObjRef) : KQ (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_mergeOverlappingRefills' _)

theorem kq_refillHeadOverlappingLoop' (sc : ObjRef) : KQ (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_refillHeadOverlappingLoop' _)

theorem kq_refillUnblockCheck' (sc : ObjRef) : KQ (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_refillUnblockCheck' _)

theorem kq_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : KQ (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_ifCondRefillUnblockCheck' _ _ _)

theorem kq_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) : KQ (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem kq_restartThreadIfNoFault' (t : ObjRef) : KQ (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_restartThreadIfNoFault' _)

theorem kq_removeAndRestartEpQueuedThread' (t e : ObjRef) : KQ (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_removeAndRestartEpQueuedThread' _ _)

theorem kq_removeAndRestartNtfnQueuedThread' (t n : ObjRef) : KQ (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_removeAndRestartNtfnQueuedThread' _ _)

theorem kq_replyUnlinkSc' (sc r : ObjRef) : KQ (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_replyUnlinkSc' _ _)

theorem kq_schedContextDonate' (sc t : ObjRef) : KQ (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedContextDonate' _ _)

theorem kq_schedContextUpdateConsumed' (sc : ObjRef) : KQ (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedContextUpdateConsumed' _)

theorem kq_replyFromKernel' (t : ObjRef) (x : Data × List Data) : KQ (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_replyFromKernel' _ _)

theorem kq_setConsumed' (sc t : ObjRef) : KQ (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setConsumed' _ _)

theorem kq_schedContextCancelYieldTo' (t : ObjRef) : KQ (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedContextCancelYieldTo' _)

theorem kq_fpuRelease' (t : ObjRef) : KQ (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_fpuRelease' _)

theorem kq_deleteAsidPool' (b : Asid) (p : ObjRef) : KQ (deleteAsidPool (Z := Unit) b p) := by
  unfold deleteAsidPool; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_deleteAsidPool' _ _)

theorem kq_deleteAsid' (a : Asid) (p : ObjRef) : KQ (deleteAsid (Z := Unit) a p) := by
  unfold deleteAsid; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_deleteAsid' _ _)

theorem kq_archPostCapDeletion' (c : ArchCap) : KQ (archPostCapDeletion (Z := Unit) c) := by
  unfold archPostCapDeletion; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_archPostCapDeletion' _)

theorem kq_postCapDeletion' (c : Cap) : KQ (postCapDeletion (Z := Unit) c) := by
  unfold postCapDeletion; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_postCapDeletion' _)

theorem kq_emptySlot' (sl : CslotPtr) (c : Cap) : KQ (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_emptySlot' _ _)

theorem kq_cancelAllIpc' (e : ObjRef) : KQ (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_cancelAllIpc' _)

theorem kq_schedContextMaybeUnbindNtfn' (n : ObjRef) : KQ (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedContextMaybeUnbindNtfn' _)

theorem kq_unbindMaybeNotification' (n : ObjRef) : KQ (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_unbindMaybeNotification' _)

theorem kq_cancelAllSignals' (n : ObjRef) : KQ (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_cancelAllSignals' _)

theorem kq_replyRemove' (t r : ObjRef) : KQ (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_replyRemove' _ _)

theorem kq_unbindNotification' (t : ObjRef) : KQ (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_unbindNotification' _)

theorem kq_schedContextUnbindTcb' (sc : ObjRef) : KQ (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedContextUnbindTcb' _)

theorem kq_completeYieldTo' (t : ObjRef) : KQ (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_completeYieldTo' _)

theorem kq_unbindFromSc' (t : ObjRef) : KQ (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_unbindFromSc' _)

theorem kq_schedContextUnbindAllTcbs' (sc : ObjRef) : KQ (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedContextUnbindAllTcbs' _)

theorem kq_schedContextUnbindNtfn' (sc : ObjRef) : KQ (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedContextUnbindNtfn' _)

theorem kq_schedContextUnbindReply' (sc : ObjRef) : KQ (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedContextUnbindReply' _)

theorem kq_schedContextUnbindYieldFrom' (sc : ObjRef) : KQ (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedContextUnbindYieldFrom' _)

theorem kq_schedContextSetInactive' (sc : ObjRef) : KQ (schedContextSetInactive (Z := Unit) sc) := by
  unfold schedContextSetInactive; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedContextSetInactive' _)

theorem kq_prepareThreadDelete' (t : ObjRef) : KQ (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_prepareThreadDelete' _)

theorem kq_archFinaliseCap' (c : ArchCap) (x : Bool) : KQ (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_archFinaliseCap' _ _)

theorem kq_fastFinalise' (c : Cap) (b : Bool) : KQ (fastFinalise (Z := Unit) c b) := by
  unfold fastFinalise; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_fastFinalise' _ _)

theorem kq_capDeleteOne' (sl : CslotPtr) : KQ (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_capDeleteOne' _)

theorem kq_deletingIrqHandler' (irq : Irq) : KQ (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_deletingIrqHandler' _)

theorem kq_finaliseCap (c : Cap) (b : Bool) : KQ (finaliseCap (Z := Unit) c b) := by
  cases c <;> unfold finaliseCap <;> kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_finaliseCap _ _)

theorem kq_capSwap' (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) : KQ (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_capSwap' _ _ _ _)

theorem kq_capSwapForDelete' (s1 s2 : CslotPtr) : KQ (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_capSwapForDelete' _ _)

theorem kqe_preemptionPoint' : KQE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_preemptionPoint')

set_option maxHeartbeats 4000000 in
theorem kq_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, KQ (f k)) (k : RecDelCall) : KQE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, KQE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF; kq_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF; kq_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF
    split <;> kq_auto
    all_goals exact hrec' _

/-- `rec_del` keeps the domain list. -/
theorem kqe_recDel (c : RecDelCall) : KQE (recDel (Z := Unit) c) := by
  intro σ x hx
  let f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)) := fun _ t =>
    ({y | ktV y.2 = ktV t}, True)
  have hf : ∀ k t, (fun r c => recDelF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy => kq_recDelF (f := f) (fun _ _ _ hz => hz) k t y hy, fun _ => trivial⟩
  exact (Fl4Proofs.P3.SInvDomL.lfp_le_prefixed' _ f hf c σ).1 hx
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_recDel _)

set_option maxHeartbeats 4000000 in
theorem kq_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, KQ (f k)) (sl : CslotPtr) : KQE (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, KQE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF
  kq_auto
  all_goals exact hrec' _

/-- `cap_revoke` keeps the domain list. -/
theorem kqe_capRevoke (sl : CslotPtr) : KQE (capRevoke (Z := Unit) sl) := by
  intro σ x hx
  let f : CslotPtr → NonDet (State Unit) (Except Unit Unit) := fun _ t =>
    ({y | ktV y.2 = ktV t}, True)
  have hf : ∀ k t, (fun r c => capRevokeF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy => kq_capRevokeF (f := f) (fun _ _ _ hz => hz) k t y hy, fun _ => trivial⟩
  exact (Fl4Proofs.P3.SInvDomL.lfp_le_prefixed' _ f hf sl σ).1 hx
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_capRevoke _)

theorem kq_capDelete (sl : CslotPtr) : KQE (capDelete (Z := Unit) sl) := by
  unfold capDelete; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_capDelete _)

theorem kq_capMove' (c : Cap) (s1 s2 : CslotPtr) : KQ (capMove (Z := Unit) c s1 s2) := by
  unfold capMove; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_capMove' _ _ _)

theorem kq_removeAndRestartBadgedThread' (t e : ObjRef) (b : Badge) :
    KQ (removeAndRestartBadgedThread (Z := Unit) t e b) := by
  unfold removeAndRestartBadgedThread; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_removeAndRestartBadgedThread' _ _ _)

theorem kq_cancelBadgedSends' (e : ObjRef) (b : Badge) : KQ (cancelBadgedSends (Z := Unit) e b) := by
  unfold cancelBadgedSends; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_cancelBadgedSends' _ _)

theorem kqe_invokeCnode (i : CnodeInvocation) : KQE (invokeCnode (Z := Unit) i) := by
  cases i <;> unfold invokeCnode withoutPreemption <;> kq_auto0

theorem kq_orderedInsert' {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : KQ (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_orderedInsert' _ _ _ _)

theorem kq_readyTimesAppend' (t : ObjRef) (q : List ObjRef) : KQ (readyTimesAppend (Z := Unit) t q) := by
  unfold readyTimesAppend; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_readyTimesAppend' _ _)

theorem kq_tcbReleaseEnqueue' (t : ObjRef) : KQ (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_tcbReleaseEnqueue' _)

theorem kq_tcbAppend' (t : ObjRef) (q : List ObjRef) : KQ (tcbAppend (Z := Unit) t q) := by
  unfold tcbAppend; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_tcbAppend' _ _)

theorem kq_postpone' (sc : ObjRef) : KQ (postpone (Z := Unit) sc) := by
  unfold postpone; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_postpone' _)

theorem kq_threadSetPriority' (t : ObjRef) (p : Priority) : KQ (threadSetPriority (Z := Unit) t p) := by
  unfold threadSetPriority; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_threadSetPriority' _ _)

theorem kq_reorderEp' (e t : ObjRef) : KQ (reorderEp (Z := Unit) e t) := by
  unfold reorderEp; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_reorderEp' _ _)

theorem kq_reorderNtfn' (n t : ObjRef) : KQ (reorderNtfn (Z := Unit) n t) := by
  unfold reorderNtfn; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_reorderNtfn' _ _)

theorem kq_archPostModifyRegisters' (c t : ObjRef) : KQ (archPostModifyRegisters (Z := Unit) c t) := by
  unfold archPostModifyRegisters; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_archPostModifyRegisters' _ _)

theorem kq_schedContextResume' (sc : ObjRef) : KQ (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedContextResume' _)

theorem kq_testPossibleSwitchTo' (t : ObjRef) : KQ (testPossibleSwitchTo (Z := Unit) t) := by
  unfold testPossibleSwitchTo; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_testPossibleSwitchTo' _)

theorem kq_ifSporadicCurScTestRefillUnblockCheck' (o : Option ObjRef) : KQ (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScTestRefillUnblockCheck; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_ifSporadicCurScTestRefillUnblockCheck' _)

theorem kq_restart' (t : ObjRef) : KQ (restart (Z := Unit) t) := by
  unfold restart; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_restart' _)

theorem kq_setMcpriority' (t : ObjRef) (m : Priority) : KQ (setMcpriority (Z := Unit) t m) := by
  unfold setMcpriority; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setMcpriority' _ _)

theorem kq_setPriority' (t : ObjRef) (p : Priority) : KQ (setPriority (Z := Unit) t p) := by
  unfold setPriority; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setPriority' _ _)

theorem kq_schedContextBindTcb' (sc t : ObjRef) : KQ (schedContextBindTcb (Z := Unit) sc t) := by
  unfold schedContextBindTcb; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedContextBindTcb' _ _)

theorem kq_bindNotification' (t n : ObjRef) : KQ (bindNotification (Z := Unit) t n) := by
  unfold bindNotification; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_bindNotification' _ _)

theorem kq_setFlags' (t : ObjRef) (f : TcbFlags) : KQ (setFlags (Z := Unit) t f) := by
  unfold setFlags; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setFlags' _ _)

theorem kq_lazyFpuRestore' (t : ObjRef) : KQ (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_lazyFpuRestore' _)

theorem kq_archPostSetFlags' (t : ObjRef) (f : TcbFlags) : KQ (archPostSetFlags (Z := Unit) t f) := by
  unfold archPostSetFlags; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_archPostSetFlags' _ _)

theorem kq_checkCapAt' (c : Cap) (sl : CslotPtr) {m : SMonad Unit Unit} (h : KQ m) :
    KQ (checkCapAt (Z := Unit) c sl m) := by
  unfold checkCapAt; kq_auto0; exact h
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible refine kq_checkCapAt' _ _ ?_)

theorem kqe_installTcbCap' (t : ObjRef) (sl : CslotPtr) (n : Nat) (o : Option (Cap × CslotPtr)) :
    KQE (installTcbCap (Z := Unit) t sl n o) := by
  unfold installTcbCap; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_installTcbCap' _ _ _ _)

theorem kqe_installTcbFrameCap' (t : ObjRef) (sl : CslotPtr) (b : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    KQE (installTcbFrameCap (Z := Unit) t sl b) := by
  unfold installTcbFrameCap; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_installTcbFrameCap' _ _ _)

theorem kqe_invokeTcb (i : TcbInvocation) : KQE (invokeTcb (Z := Unit) i) := by
  cases i <;> unfold invokeTcb <;> kq_auto0

theorem kqe_invokeFl4Tcb (i : Fl4TcbInvocation) : KQE (invokeFl4Tcb (Z := Unit) i) := by
  cases i <;> unfold invokeFl4Tcb <;> kq_auto0

theorem kqe_fl4PerformTcb (blk call don : Bool) (i : TcbInvocation) :
    KQE (fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB i)) := kqe_invokeTcb i

theorem kqe_fl4PerformFl4Tcb (blk call don : Bool) (i : Fl4TcbInvocation) :
    KQE (fl4PerformInvocation (Z := Unit) blk call don (.invokeFl4TCB i)) := kqe_invokeFl4Tcb i

theorem kqe_fl4PerformCnode (blk call don : Bool) (i : CnodeInvocation) :
    KQE (fl4PerformInvocation (Z := Unit) blk call don (.invokeCNode i)) := by
  show KQE (do invokeCnode (Z := Unit) i; NonDetE.returnOk [])
  exact Vs.dke_bind (kqe_invokeCnode i) fun _ => Vs.dke_returnOk _

theorem kqe_withoutPreemption' {α : Type} {m : SMonad Unit α} (h : KQ m) :
    KQE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact dke_liftE h
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible refine kqe_withoutPreemption' ?_)

theorem kqe_resolveAddressBits (p : Cap × CapRef) : KQE (resolveAddressBits (Z := Unit) p) := kqe_rab p
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_resolveAddressBits _)

theorem kq_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : KQE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_lookupSlotForThread' _ _)

theorem kq_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : KQE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_lookupCapAndSlot' _ _)

theorem kq_lookupCap' (thread : ObjRef) (ref : CapRef) : KQE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_lookupCap' _ _)

theorem kq_captransferFromWords' (ptr : Word) : KQ (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_captransferFromWords' _)

theorem kq_loadCapTransfer' (buffer : ObjRef) : KQ (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_loadCapTransfer' _)

theorem kq_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : KQ (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setExtraBadge' _ _ _)

theorem kqe_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : KQE m) :
    KQE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible refine kqe_lookupErrorOnFailure' _ ?_)

theorem kq_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : KQE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_lookupSlotForCnodeOp' _ _ _ _)

theorem kq_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : KQE (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact kq_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_lookupTargetSlot' _ _ _)

theorem kq_archPostResetUntyped' (_isDevice : Bool) (_sz : Nat) : KQ (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_archPostResetUntyped' _ _)



theorem kq_copyGlobalMappings' (newPm : ObjRef) : KQ (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_copyGlobalMappings' _)

theorem kq_initArchObjects' (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : KQ (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_initArchObjects' _ _ _ _ _ _)

theorem kq_createCap' (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool)
    (d : CslotPtr × ObjRef) : KQ (createCap (Z := Unit) type bits untyped isDevice d) := by
  obtain ⟨dest, oref⟩ := d
  unfold createCap; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_createCap' _ _ _ _ _)

theorem kq_ensureNoChildren' (cslotPtr : CslotPtr) : KQE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_ensureNoChildren' _)

theorem kq_getRefillTail' (scPtr : ObjRef) : KQ (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getRefillTail' _)

theorem kq_getRefills' (scPtr : ObjRef) : KQ (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getRefills' _)

theorem kq_refillAddTail' (scPtr : ObjRef) (newRefill : Refill) : KQ (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_refillAddTail' _ _)

theorem kq_refillFull' (scPtr : ObjRef) : KQ (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_refillFull' _)

theorem kq_updateRefillTl' (scPtr : ObjRef) (f : Refill → Refill) : KQ (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_updateRefillTl' _ _)

theorem kq_scheduleUsed' (scPtr : ObjRef) (new : Refill) : KQ (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_scheduleUsed' _ _)

theorem kq_refillSize' (scPtr : ObjRef) : KQ (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_refillSize' _)

theorem kq_refillSingle' (scPtr : ObjRef) : KQ (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_refillSingle' _)

theorem kq_chargeEntireHeadRefill' (scPtr : ObjRef) (usage : Ticks) : KQ (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_chargeEntireHeadRefill' _ _)

theorem kq_mergeNonoverlappingHeadRefill' (scPtr : ObjRef) : KQ (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_mergeNonoverlappingHeadRefill' _)

theorem kq_updateIrqState' (irq : Irq) (irqState : X64IRQState) : KQ (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_updateIrqState' _ _)

theorem kqe_archInvokeIrqControl' (i : ArchIrqControlInvocation) : KQE (archInvokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold archInvokeIrqControl <;> kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_archInvokeIrqControl' _)

theorem kq_invokeIrqControl' (i : IrqControlInvocation) : KQE (invokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeIrqControl <;> kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_invokeIrqControl' _)



theorem kqe_invokeFl4IrqControl' (i : Fl4IrqControlInvocation) : KQE (invokeFl4IrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeFl4IrqControl <;> kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_invokeFl4IrqControl' _)

theorem kqe_archDeriveCap' (c : ArchCap) : KQE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_archDeriveCap' _)

theorem kqe_deriveCap' (sl : CslotPtr) (c : Cap) : KQE (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_deriveCap' _ _)

theorem kq_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : KQ (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_makeArchFaultMsg' _ _)

theorem kqe_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : KQE m) :
    KQE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible refine kqe_unifyFailure' ?_)

theorem kq_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : KQE m) :
    KQ (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible refine kq_emptyOnFailure' ?_)

theorem kq_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : KQE m) :
    KQ (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible refine kq_constOnFailure' _ ?_)

theorem kqe_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : KQE m) :
    KQE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible refine kqe_capFaultOnFailure' _ _ ?_)

theorem kq_loadWordOffs' (ptr : ObjRef) (offs : Nat) : KQ (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; exact kq_doMachineOp _
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_loadWordOffs' _ _)

theorem kq_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : KQ (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact dk_pure _
  · unfold getExtraCptrs; exact dk_liftM _ (dk_mapM (fun _ => kq_loadWordOffs' _ _) _)
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getExtraCptrs' _ _)

theorem kq_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : KQ (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getReceiveSlots' _ _)

theorem kq_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      KQ (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; kq_auto0
  | n, (c, sl) :: rest, slots, mi => by
    have ih := kq_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    kq_auto0
    all_goals first | exact ih _ _ | skip
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_transferCapsLoop' _ _ _ _ _ _)

theorem kq_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : KQE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_lookupExtraCaps' _ _ _)

theorem kq_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : KQ (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_copyMrs' _ _ _ _ _)

theorem kq_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : KQ (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_transferCaps' _ _ _ _ _)

theorem kq_makeFaultMsg' (f : Fault) (t : ObjRef) : KQ (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_makeFaultMsg' _ _)

theorem kq_handleOverrun' (scPtr : ObjRef) (usage : Ticks) : KQ (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_handleOverrun' _ _)

theorem kq_headInsufficientLoop' (scPtr : ObjRef) : KQ (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_headInsufficientLoop' _)

theorem kq_getMessageInfo' (thread : ObjRef) : KQ (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getMessageInfo' _)

theorem kq_tcbEpAppend' (tptr epPtr : ObjRef) (isRecv : Bool) : KQ (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_tcbEpAppend' _ _ _)

theorem kq_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : KQ (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_doNormalTransfer' _ _ _ _ _ _ _)

theorem kq_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : KQ (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_doFaultTransfer' _ _ _ _)

theorem kq_bindScReply' (scPtr replyPtr : ObjRef) : KQ (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_bindScReply' _ _)

theorem kq_isValidTimeoutHandler' (tptr : ObjRef) : KQ (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_isValidTimeoutHandler' _)

theorem kq_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : KQ (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_doIpcTransfer' _ _ _ _ _)

theorem kq_replyPush' (caller callee replyPtr : ObjRef) (canDonate : Bool) : KQ (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_replyPush' _ _ _ _)

theorem kq_sendIpcBlocked' (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : KQ (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_sendIpcBlocked' _ _ _ _ _ _)

theorem kq_sendIpc' (b c : Bool) (bd : Badge) (g gr d : Bool) (t e : ObjRef) : KQ (sendIpc (Z := Unit) b c bd g gr d t e) := by
  unfold sendIpc; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_sendIpc' _ _ _ _ _ _ _ _)

theorem kq_sendFaultIpc' (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : KQ (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_sendFaultIpc' _ _ _ _)

theorem kq_refillBudgetCheckRoundRobin' (usage : Ticks) : KQ (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_refillBudgetCheckRoundRobin' _)

theorem kq_refillBudgetCheck' (usage : Ticks) : KQ (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_refillBudgetCheck' _)

theorem kq_maybeAddEmptyTail' (scPtr : ObjRef) : KQ (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_maybeAddEmptyTail' _)

theorem kq_maybeDonateSc' (tcbPtr ntfnPtr : ObjRef) : KQ (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_maybeDonateSc' _ _)

theorem kq_updateWaitingNtfn' (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : KQ (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_updateWaitingNtfn' _ _ _)

theorem kq_handleTimeout' (tptr : ObjRef) (ex : Fault) : KQ (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_handleTimeout' _ _)

theorem kq_getMrs' (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : KQ (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getMrs' _ _ _)

theorem kq_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    KQ (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_handleFaultReply' _ _ _ _)

theorem kq_returnConsumed' (scPtr : ObjRef) : KQ (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_returnConsumed' _)

theorem kq_schedContextBindNtfn' (sc ntfn : ObjRef) : KQ (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedContextBindNtfn' _ _)

theorem kq_schedContextYieldTo' (scPtr : ObjRef) : KQ (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedContextYieldTo' _)

theorem kq_getScActive' (scPtr : ObjRef) : KQ (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getScActive' _)

theorem kq_commitTime' : KQ (commitTime (Z := Unit) ) := by
  unfold commitTime; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_commitTime' )

theorem kq_refillNew' (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : KQ (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_refillNew' _ _ _ _)

theorem kq_refillUpdate' (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : KQ (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_refillUpdate' _ _ _ _)

theorem kq_archInvokeIrqHandler' (i : IrqHandlerInvocation) : KQ (archInvokeIrqHandler (Z := Unit) i) := by
  cases i <;> unfold archInvokeIrqHandler <;> kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_archInvokeIrqHandler' _)

theorem kq_sendSignal' (n : ObjRef) (b : Badge) : KQ (sendSignal (Z := Unit) n b) := by
  unfold sendSignal; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_sendSignal' _ _)

theorem kq_doReplyTransfer' (s r : ObjRef) (g : Bool) : KQ (doReplyTransfer (Z := Unit) s r g) := by
  unfold doReplyTransfer; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_doReplyTransfer' _ _ _)

theorem kq_invokeSchedContext' (i : SchedContextInvocation) : KQ (invokeSchedContext (Z := Unit) i) := by
  cases i <;> unfold invokeSchedContext <;> kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_invokeSchedContext' _)

theorem kq_invokeSchedControlConfigureFlags' (i : SchedControlInvocation) : KQ (invokeSchedControlConfigureFlags (Z := Unit) i) := by
  cases i <;> unfold invokeSchedControlConfigureFlags <;> kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_invokeSchedControlConfigureFlags' _)

theorem kq_invokeIrqHandler' (i : IrqHandlerInvocation) : KQ (invokeIrqHandler (Z := Unit) i) := by
  cases i <;> unfold invokeIrqHandler <;> kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_invokeIrqHandler' _)

theorem kq_lookupSourceSlot' (c : Cap) (r : CapRef) (n : Nat) : KQE (lookupSourceSlot (Z := Unit) c r n) := by
  unfold lookupSourceSlot; exact kq_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_lookupSourceSlot' _ _ _)

theorem kqe_ensureEmpty' (sl : CslotPtr) : KQE (ensureEmpty (Z := Unit) sl) := by
  unfold ensureEmpty; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_ensureEmpty' _)

theorem kqe_checkVpAlignment' (sz : VMPageSize) (v : Word) : KQE (checkVpAlignment (Z := Unit) sz v) := by
  unfold checkVpAlignment; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_checkVpAlignment' _ _)

theorem kqe_createMappingEntries' (base : Paddr) (vptr : VSpaceRef) (sz : VMPageSize) (r : VMRights)
    (at' : VMAttributes) (p : ObjRef) : KQE (createMappingEntries (Z := Unit) base vptr sz r at' p) := by
  cases sz <;> unfold createMappingEntries <;> kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_createMappingEntries' _ _ _ _ _ _)

theorem kqe_ensureSafeMapping' (e : VMPageEntry × ObjRef) : KQE (ensureSafeMapping (Z := Unit) e) := by
  unfold ensureSafeMapping; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_ensureSafeMapping' _)

theorem kqe_decodePageInvocation' (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) : KQE (decodePageInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageInvocation; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_decodePageInvocation' _ _ _ _ _)

theorem kqe_fbMap (b : Fl4FrameBatchInvocation) (sl : CslotPtr) (v : Data) : KQE (fbMap (Z := Unit) b sl v) := by
  unfold fbMap; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_fbMap _ _ _)

theorem kq_unmapPageUnflushed (sz : VMPageSize) (vs : ObjRef) (v : VSpaceRef) (p : ObjRef) :
    KQ (unmapPageUnflushed (Z := Unit) sz vs v p) := by
  unfold unmapPageUnflushed; kq_auto0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_unmapPageUnflushed _ _ _ _)

theorem kqe_fbCode {α : Type} {m : SEMonad Unit α} (h : KQE m) : KQE (fbCode (Z := Unit) m) := by
  unfold fbCode; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible refine kqe_fbCode ?_)

theorem kqe_fbDelete (sl : CslotPtr) : KQE (fbDelete (Z := Unit) sl) := by
  unfold fbDelete; exact dke_handleE (kq_capDelete sl) fun _ => dke_throw _
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_fbDelete _)

/-- fb3: one `X86PML4FrameBatch` entry. -/
theorem kq_fbEntry (b : Fl4FrameBatchInvocation) (w : Data × Data × Data) : KQE (fbEntry (Z := Unit) b w) := by
  unfold fbEntry; kq_auto0

/-- fb3: the batch (SpecInvFbD's `fk_performFrameBatch`). -/
theorem kq_performFrameBatch (b : Fl4FrameBatchInvocation) : KQ (performFrameBatch (Z := Unit) b) :=
  fk_performFrameBatch (fun w => kq_fbEntry b w) (kq_flushAll _ _)
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_performFrameBatch _)


end

end Fl4Proofs.P3.SInvKt
