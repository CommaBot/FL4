/-
P3 (line p3J, gen 25): **`RQ` leaves of the spec functions** (P3JRrF's SC-period frame), a scripted copy of gen 21's
P3JKtG (`scratch/p3J/genRr.py`), without the heap writers `retype_region` / `delete_objects` and their callers and
without the period writers `refill_new` / `refill_update` and their caller `invoke_sched_control_configure_flags`
(`scratch/p3J/rr/skip.txt`); `set_cap` / `set_simple_ko` / `update_sched_context` are P3JRrF's hand leaves.

Named premises: none. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JRrF
import Fl4Proofs.P3.SpecInvDomL
import Fl4Proofs.P3.SpecInvFbD
open Classical

namespace Fl4Proofs.P3.SInvRr
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

set_option maxRecDepth 20000


theorem rq_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    RQ (portOut (Z := Unit) f w) := by
  unfold portOut; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_portOut _ _)

theorem rq_getPt (ptr : ObjRef) : RQ (getPt (Z := Unit) ptr) := by
  unfold getPt; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getPt _)

theorem rq_getPte (ptr : ObjRef) : RQ (getPte (Z := Unit) ptr) := by
  unfold getPte; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getPte _)

theorem rq_getPd (ptr : ObjRef) : RQ (getPd (Z := Unit) ptr) := by
  unfold getPd; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getPd _)

theorem rq_getPde (ptr : ObjRef) : RQ (getPde (Z := Unit) ptr) := by
  unfold getPde; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getPde _)

theorem rq_getPml4 (ptr : ObjRef) : RQ (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getPml4 _)

theorem rq_getPml4e (ptr : ObjRef) : RQ (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getPml4e _)

theorem rq_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : RQE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_lookupPdptSlot _ _)

theorem rq_getPdpt (ptr : ObjRef) : RQ (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getPdpt _)

theorem rq_getPdpte (ptr : ObjRef) : RQ (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getPdpte _)

theorem rq_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : RQE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_lookupPdSlot _ _)

theorem rq_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : RQE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_lookupPtSlot _ _)

theorem rq_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : RQ (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setPdpt _ _)

theorem rq_storePdpte (p : ObjRef) (pte : PDPTE) : RQ (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_storePdpte _ _)

theorem rq_getAsidPool (ptr : ObjRef) : RQ (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getAsidPool _)

theorem rq_findVspaceForAsid (asid : Asid) : RQE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_findVspaceForAsid _)

theorem rq_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : RQ (setPt (Z := Unit) ptr pt) := by
  unfold setPt; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setPt _ _)

theorem rq_storePte (p : ObjRef) (pte : PTE) : RQ (storePte (Z := Unit) p pte) := by
  unfold storePte; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_storePte _ _)

theorem rq_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : RQ (setPd (Z := Unit) ptr pd) := by
  unfold setPd; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setPd _ _)

theorem rq_storePde (p : ObjRef) (pde : PDE) : RQ (storePde (Z := Unit) p pde) := by
  unfold storePde; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_storePde _ _)

theorem rq_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : RQ (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_unmapPage _ _ _ _)

theorem rq_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : RQ (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_performPageInvocationUnmap _ _)

theorem rq_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : RQ (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setAsidPool _ _)

theorem rq_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : RQ (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_flushTable _ _ _ _)

theorem rq_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : RQ (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setPml4 _ _)

theorem rq_setOriginal (slot : CslotPtr) (v : Bool) : RQ (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setOriginal _ _)

theorem rq_updateCdt (f : Cdt → Cdt) : RQ (updateCdt (Z := Unit) f) := by
  unfold updateCdt; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_updateCdt _)

theorem rq_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : RQ (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setUntypedCapAsFull _ _ _)


theorem rq_storePml4e (p : ObjRef) (pte : PML4E) : RQ (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_storePml4e _ _)

theorem rq_flushAll (vspace : ObjRef) (asid : Asid) : RQ (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_flushAll _ _)

theorem rq_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : RQ (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_unmapPdpt _ _ _)

theorem rq_setIoportMask (f l : IoPort) (val : Bool) : RQ (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setIoportMask _ _ _)

theorem rq_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : RQ (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_invalidatePageStructureCacheAsid _ _)

theorem rq_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : RQ (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_unmapPd _ _ _)


theorem rq_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : RQ (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_capInsert _ _ _)

theorem rq_portIn (f : MachineMonad Data) : RQ (portIn (Z := Unit) f) := by
  unfold portIn; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_portIn _)

theorem rq_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : RQ (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_unmapPageTable _ _ _)

theorem rq_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : RQ (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_storeAsidPoolEntry _ _ _)

theorem rq_performPageInvocation (iv : PageInvocation) : RQ (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_performPageInvocation _)

theorem rq_performPageTableInvocation (iv : PageTableInvocation) : RQ (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_performPageTableInvocation _)

theorem rq_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : RQ (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_performPageDirectoryInvocation _)

theorem rq_performPdptInvocation (iv : PdptInvocation) : RQ (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_performPdptInvocation _)

theorem rq_performAsidPoolInvocation (iv : AsidPoolInvocation) : RQ (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_performAsidPoolInvocation _)


theorem rq_performIoPortInvocation (i : IoPortInvocation) : RQ (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_performIoPortInvocation _)

theorem rq_performIoportControlInvocation (i : IoPortControlInvocation) : RQ (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_performIoportControlInvocation _)

theorem rq_performDeriveSubframe (iv : Fl4SubframeInvocation) : RQ (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_performDeriveSubframe _)

theorem rq_performTestAndClearAccessed (_slot : ObjRef) : RQ (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_performTestAndClearAccessed _)

theorem rq_performPml4Flush (i : Fl4Pml4Invocation) : RQ (performPml4Flush (Z := Unit) i) := by
  cases i; unfold performPml4Flush; exact rq_flushAll _ _

theorem rq_threadSet' (f : Tcb → Tcb) (t : ObjRef) : RQ (threadSet (Z := Unit) f t) := by
  unfold threadSet; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_threadSet' _ _)

theorem rq_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : RQ (threadGet (Z := Unit) f t) := by
  unfold threadGet; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_threadGet' _ _)

theorem rq_setThreadState' (t : ObjRef) (ts : ThreadState) : RQ (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setThreadState' _ _)

theorem rq_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    RQ (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getSimpleKo' _ _)


theorem rq_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    RQ (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_updateSkObjRef' _ _ _ _)

theorem rq_getSchedContext' (q : ObjRef) : RQ (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getSchedContext' _)


theorem rq_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : RQ (asUser (Z := Unit) t u) := by
  unfold asUser; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_asUser' _ _)

theorem rq_replyUnlinkTcb' (t r : ObjRef) : RQ (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_replyUnlinkTcb' _ _)

theorem rq_getThreadState' (t : ObjRef) : RQ (getThreadState (Z := Unit) t) := by
  unfold getThreadState; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getThreadState' _)

theorem rq_cancelIpc' (t : ObjRef) : RQ (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_cancelIpc' _)

theorem rq_suspend' (t : ObjRef) : RQ (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc tcbSchedAction getTcbQueue setTcbQueue tcbReleaseRemove
    schedContextCancelYieldTo getTcbObjRef getThreadState
  zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_suspend' _)

theorem rq_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : RQ (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getSkObjRef' _ _ _)

theorem rq_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : RQ (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getScObjRef' _ _)

theorem rq_getIrqSlot' (irq : Irq) : RQ (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getIrqSlot' _)

theorem rq_isFinalCap' (c : Cap) : RQ (isFinalCap (Z := Unit) c) := by
  unfold isFinalCap; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_isFinalCap' _)

theorem rq_hwAsidInvalidate' (a : Asid) (v : ObjRef) : RQ (hwAsidInvalidate (Z := Unit) a v) := by
  unfold hwAsidInvalidate; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_hwAsidInvalidate' _ _)

theorem rq_getCurrentCr3' : RQ (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getCurrentCr3' )

theorem rq_setCurrentCr3' (c : Cr3) : RQ (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setCurrentCr3' _)

theorem rq_setCurrentVspaceRoot' (v : ObjRef) (a : Asid) : RQ (setCurrentVspaceRoot (Z := Unit) v a) := by
  unfold setCurrentVspaceRoot; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setCurrentVspaceRoot' _ _)

theorem rq_setVmRoot' (t : ObjRef) : RQ (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setVmRoot' _)

theorem rq_freeIoportRange' (f l : IoPort) : RQ (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_freeIoportRange' _ _)

theorem rq_setIrqState' (i : IrqState) (irq : Irq) : RQ (setIrqState (Z := Unit) i irq) := by
  unfold setIrqState; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setIrqState' _ _)

theorem rq_deletedIrqHandler' (irq : Irq) : RQ (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_deletedIrqHandler' _)

theorem rq_lookupIpcBuffer' (b : Bool) (t : ObjRef) : RQ (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_lookupIpcBuffer' _ _)

theorem rq_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : RQ (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_storeWordOffs' _ _ _)

theorem rq_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : RQ (setMrs (Z := Unit) t b m) := by
  unfold setMrs; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setMrs' _ _ _)

theorem rq_setMessageInfo' (t : ObjRef) (i : MessageInfo) : RQ (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setMessageInfo' _ _)

theorem rq_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : RQ (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_archThreadSet' _ _)

theorem rq_saveFpuState' (t : ObjRef) : RQ (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_saveFpuState' _)

theorem rq_loadFpuState' (t : ObjRef) : RQ (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_loadFpuState' _)

theorem rq_setX64CurrentFpuOwner' (o : Option ObjRef) : RQ (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setX64CurrentFpuOwner' _)

theorem rq_switchLocalFpuOwner' (o : Option ObjRef) : RQ (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_switchLocalFpuOwner' _)

theorem rq_getTcbQueue' (d : Domain) (p : Priority) : RQ (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getTcbQueue' _ _)

theorem rq_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : RQ (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setTcbQueue' _ _ _)

theorem rq_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : RQ (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_tcbSchedAction' _ _)

theorem rq_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : RQ (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getTcbObjRef' _ _)

theorem rq_setSchedulerAction' (a : SchedulerAction) : RQ (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setSchedulerAction' _)

theorem rq_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : RQ (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getScRefillSufficient' _ _)

theorem rq_getScRefillReady' (sc : ObjRef) : RQ (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getScRefillReady' _)

theorem rq_tcbReleaseRemove' (t : ObjRef) : RQ (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_tcbReleaseRemove' _)

theorem rq_rescheduleRequired' : RQ (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_rescheduleRequired' )

theorem rq_testReschedule' (t : ObjRef) : RQ (testReschedule (Z := Unit) t) := by
  unfold testReschedule; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_testReschedule' _)

theorem rq_possibleSwitchTo' (t : ObjRef) : RQ (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_possibleSwitchTo' _)

theorem rq_tcbEpDequeue' (t e : ObjRef) : RQ (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_tcbEpDequeue' _ _)

theorem rq_tcbNtfnDequeue' (t n : ObjRef) : RQ (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_tcbNtfnDequeue' _ _)

theorem rq_isRoundRobin' (sc : ObjRef) : RQ (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_isRoundRobin' _)

theorem rq_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : RQ (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_updateRefillHd' _ _)

theorem rq_getRefillHead' (sc : ObjRef) : RQ (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getRefillHead' _)

theorem rq_refillPopHead' (sc : ObjRef) : RQ (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_refillPopHead' _)

theorem rq_mergeOverlappingRefills' (sc : ObjRef) : RQ (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_mergeOverlappingRefills' _)

theorem rq_refillHeadOverlappingLoop' (sc : ObjRef) : RQ (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_refillHeadOverlappingLoop' _)

theorem rq_refillUnblockCheck' (sc : ObjRef) : RQ (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_refillUnblockCheck' _)

theorem rq_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : RQ (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_ifCondRefillUnblockCheck' _ _ _)

theorem rq_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) : RQ (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem rq_restartThreadIfNoFault' (t : ObjRef) : RQ (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_restartThreadIfNoFault' _)

theorem rq_removeAndRestartEpQueuedThread' (t e : ObjRef) : RQ (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_removeAndRestartEpQueuedThread' _ _)

theorem rq_removeAndRestartNtfnQueuedThread' (t n : ObjRef) : RQ (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_removeAndRestartNtfnQueuedThread' _ _)

theorem rq_replyUnlinkSc' (sc r : ObjRef) : RQ (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_replyUnlinkSc' _ _)

theorem rq_schedContextDonate' (sc t : ObjRef) : RQ (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedContextDonate' _ _)

theorem rq_schedContextUpdateConsumed' (sc : ObjRef) : RQ (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedContextUpdateConsumed' _)

theorem rq_replyFromKernel' (t : ObjRef) (x : Data × List Data) : RQ (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_replyFromKernel' _ _)

theorem rq_setConsumed' (sc t : ObjRef) : RQ (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setConsumed' _ _)

theorem rq_schedContextCancelYieldTo' (t : ObjRef) : RQ (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedContextCancelYieldTo' _)

theorem rq_fpuRelease' (t : ObjRef) : RQ (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_fpuRelease' _)

theorem rq_deleteAsidPool' (b : Asid) (p : ObjRef) : RQ (deleteAsidPool (Z := Unit) b p) := by
  unfold deleteAsidPool; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_deleteAsidPool' _ _)

theorem rq_deleteAsid' (a : Asid) (p : ObjRef) : RQ (deleteAsid (Z := Unit) a p) := by
  unfold deleteAsid; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_deleteAsid' _ _)

theorem rq_archPostCapDeletion' (c : ArchCap) : RQ (archPostCapDeletion (Z := Unit) c) := by
  unfold archPostCapDeletion; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_archPostCapDeletion' _)

theorem rq_postCapDeletion' (c : Cap) : RQ (postCapDeletion (Z := Unit) c) := by
  unfold postCapDeletion; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_postCapDeletion' _)

theorem rq_emptySlot' (sl : CslotPtr) (c : Cap) : RQ (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_emptySlot' _ _)

theorem rq_cancelAllIpc' (e : ObjRef) : RQ (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_cancelAllIpc' _)

theorem rq_schedContextMaybeUnbindNtfn' (n : ObjRef) : RQ (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedContextMaybeUnbindNtfn' _)

theorem rq_unbindMaybeNotification' (n : ObjRef) : RQ (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_unbindMaybeNotification' _)

theorem rq_cancelAllSignals' (n : ObjRef) : RQ (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_cancelAllSignals' _)

theorem rq_replyRemove' (t r : ObjRef) : RQ (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_replyRemove' _ _)

theorem rq_unbindNotification' (t : ObjRef) : RQ (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_unbindNotification' _)

theorem rq_schedContextUnbindTcb' (sc : ObjRef) : RQ (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedContextUnbindTcb' _)

theorem rq_completeYieldTo' (t : ObjRef) : RQ (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_completeYieldTo' _)

theorem rq_unbindFromSc' (t : ObjRef) : RQ (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_unbindFromSc' _)

theorem rq_schedContextUnbindAllTcbs' (sc : ObjRef) : RQ (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedContextUnbindAllTcbs' _)

theorem rq_schedContextUnbindNtfn' (sc : ObjRef) : RQ (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedContextUnbindNtfn' _)

theorem rq_schedContextUnbindReply' (sc : ObjRef) : RQ (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedContextUnbindReply' _)

theorem rq_schedContextUnbindYieldFrom' (sc : ObjRef) : RQ (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedContextUnbindYieldFrom' _)

theorem rq_schedContextSetInactive' (sc : ObjRef) : RQ (schedContextSetInactive (Z := Unit) sc) := by
  unfold schedContextSetInactive; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedContextSetInactive' _)

theorem rq_prepareThreadDelete' (t : ObjRef) : RQ (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_prepareThreadDelete' _)

theorem rq_archFinaliseCap' (c : ArchCap) (x : Bool) : RQ (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_archFinaliseCap' _ _)

theorem rq_fastFinalise' (c : Cap) (b : Bool) : RQ (fastFinalise (Z := Unit) c b) := by
  unfold fastFinalise; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_fastFinalise' _ _)

theorem rq_capDeleteOne' (sl : CslotPtr) : RQ (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_capDeleteOne' _)

theorem rq_deletingIrqHandler' (irq : Irq) : RQ (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_deletingIrqHandler' _)

theorem rq_finaliseCap (c : Cap) (b : Bool) : RQ (finaliseCap (Z := Unit) c b) := by
  cases c <;> unfold finaliseCap <;> zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_finaliseCap _ _)

theorem rq_capSwap' (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) : RQ (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_capSwap' _ _ _ _)

theorem rq_capSwapForDelete' (s1 s2 : CslotPtr) : RQ (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_capSwapForDelete' _ _)

theorem rqe_preemptionPoint' : RQE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_preemptionPoint')

set_option maxHeartbeats 4000000 in
theorem rq_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, RQ (f k)) (k : RecDelCall) : RQE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, RQE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF; zq_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF; zq_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF
    split <;> zq_auto
    all_goals exact hrec' _

/-- `rec_del` keeps the domain list. -/
theorem rqe_recDel (c : RecDelCall) : RQE (recDel (Z := Unit) c) := by
  intro σ x hx
  let f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)) := fun _ t =>
    ({y | rpV y.2 = rpV t}, True)
  have hf : ∀ k t, (fun r c => recDelF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy => rq_recDelF (f := f) (fun _ _ _ hz => hz) k t y hy, fun _ => trivial⟩
  exact (Fl4Proofs.P3.SInvDomL.lfp_le_prefixed' _ f hf c σ).1 hx
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_recDel _)

set_option maxHeartbeats 4000000 in
theorem rq_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, RQ (f k)) (sl : CslotPtr) : RQE (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, RQE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF
  zq_auto
  all_goals exact hrec' _

/-- `cap_revoke` keeps the domain list. -/
theorem rqe_capRevoke (sl : CslotPtr) : RQE (capRevoke (Z := Unit) sl) := by
  intro σ x hx
  let f : CslotPtr → NonDet (State Unit) (Except Unit Unit) := fun _ t =>
    ({y | rpV y.2 = rpV t}, True)
  have hf : ∀ k t, (fun r c => capRevokeF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy => rq_capRevokeF (f := f) (fun _ _ _ hz => hz) k t y hy, fun _ => trivial⟩
  exact (Fl4Proofs.P3.SInvDomL.lfp_le_prefixed' _ f hf sl σ).1 hx
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_capRevoke _)

theorem rq_capDelete (sl : CslotPtr) : RQE (capDelete (Z := Unit) sl) := by
  unfold capDelete; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_capDelete _)

theorem rq_capMove' (c : Cap) (s1 s2 : CslotPtr) : RQ (capMove (Z := Unit) c s1 s2) := by
  unfold capMove; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_capMove' _ _ _)

theorem rq_removeAndRestartBadgedThread' (t e : ObjRef) (b : Badge) :
    RQ (removeAndRestartBadgedThread (Z := Unit) t e b) := by
  unfold removeAndRestartBadgedThread; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_removeAndRestartBadgedThread' _ _ _)

theorem rq_cancelBadgedSends' (e : ObjRef) (b : Badge) : RQ (cancelBadgedSends (Z := Unit) e b) := by
  unfold cancelBadgedSends; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_cancelBadgedSends' _ _)

theorem rqe_invokeCnode (i : CnodeInvocation) : RQE (invokeCnode (Z := Unit) i) := by
  cases i <;> unfold invokeCnode withoutPreemption <;> zq_auto0

theorem rq_orderedInsert' {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : RQ (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_orderedInsert' _ _ _ _)

theorem rq_readyTimesAppend' (t : ObjRef) (q : List ObjRef) : RQ (readyTimesAppend (Z := Unit) t q) := by
  unfold readyTimesAppend; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_readyTimesAppend' _ _)

theorem rq_tcbReleaseEnqueue' (t : ObjRef) : RQ (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_tcbReleaseEnqueue' _)

theorem rq_tcbAppend' (t : ObjRef) (q : List ObjRef) : RQ (tcbAppend (Z := Unit) t q) := by
  unfold tcbAppend; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_tcbAppend' _ _)

theorem rq_postpone' (sc : ObjRef) : RQ (postpone (Z := Unit) sc) := by
  unfold postpone; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_postpone' _)

theorem rq_threadSetPriority' (t : ObjRef) (p : Priority) : RQ (threadSetPriority (Z := Unit) t p) := by
  unfold threadSetPriority; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_threadSetPriority' _ _)

theorem rq_reorderEp' (e t : ObjRef) : RQ (reorderEp (Z := Unit) e t) := by
  unfold reorderEp; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_reorderEp' _ _)

theorem rq_reorderNtfn' (n t : ObjRef) : RQ (reorderNtfn (Z := Unit) n t) := by
  unfold reorderNtfn; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_reorderNtfn' _ _)

theorem rq_archPostModifyRegisters' (c t : ObjRef) : RQ (archPostModifyRegisters (Z := Unit) c t) := by
  unfold archPostModifyRegisters; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_archPostModifyRegisters' _ _)

theorem rq_schedContextResume' (sc : ObjRef) : RQ (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedContextResume' _)

theorem rq_testPossibleSwitchTo' (t : ObjRef) : RQ (testPossibleSwitchTo (Z := Unit) t) := by
  unfold testPossibleSwitchTo; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_testPossibleSwitchTo' _)

theorem rq_ifSporadicCurScTestRefillUnblockCheck' (o : Option ObjRef) : RQ (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScTestRefillUnblockCheck; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_ifSporadicCurScTestRefillUnblockCheck' _)

theorem rq_restart' (t : ObjRef) : RQ (restart (Z := Unit) t) := by
  unfold restart; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_restart' _)

theorem rq_setMcpriority' (t : ObjRef) (m : Priority) : RQ (setMcpriority (Z := Unit) t m) := by
  unfold setMcpriority; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setMcpriority' _ _)

theorem rq_setPriority' (t : ObjRef) (p : Priority) : RQ (setPriority (Z := Unit) t p) := by
  unfold setPriority; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setPriority' _ _)

theorem rq_schedContextBindTcb' (sc t : ObjRef) : RQ (schedContextBindTcb (Z := Unit) sc t) := by
  unfold schedContextBindTcb; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedContextBindTcb' _ _)

theorem rq_bindNotification' (t n : ObjRef) : RQ (bindNotification (Z := Unit) t n) := by
  unfold bindNotification; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_bindNotification' _ _)

theorem rq_setFlags' (t : ObjRef) (f : TcbFlags) : RQ (setFlags (Z := Unit) t f) := by
  unfold setFlags; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setFlags' _ _)

theorem rq_lazyFpuRestore' (t : ObjRef) : RQ (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_lazyFpuRestore' _)

theorem rq_archPostSetFlags' (t : ObjRef) (f : TcbFlags) : RQ (archPostSetFlags (Z := Unit) t f) := by
  unfold archPostSetFlags; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_archPostSetFlags' _ _)

theorem rq_checkCapAt' (c : Cap) (sl : CslotPtr) {m : SMonad Unit Unit} (h : RQ m) :
    RQ (checkCapAt (Z := Unit) c sl m) := by
  unfold checkCapAt; zq_auto0; exact h
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible refine rq_checkCapAt' _ _ ?_)

theorem rqe_installTcbCap' (t : ObjRef) (sl : CslotPtr) (n : Nat) (o : Option (Cap × CslotPtr)) :
    RQE (installTcbCap (Z := Unit) t sl n o) := by
  unfold installTcbCap; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_installTcbCap' _ _ _ _)

theorem rqe_installTcbFrameCap' (t : ObjRef) (sl : CslotPtr) (b : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    RQE (installTcbFrameCap (Z := Unit) t sl b) := by
  unfold installTcbFrameCap; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_installTcbFrameCap' _ _ _)

theorem rqe_invokeTcb (i : TcbInvocation) : RQE (invokeTcb (Z := Unit) i) := by
  cases i <;> unfold invokeTcb <;> zq_auto0

theorem rqe_invokeFl4Tcb (i : Fl4TcbInvocation) : RQE (invokeFl4Tcb (Z := Unit) i) := by
  cases i <;> unfold invokeFl4Tcb <;> zq_auto0

theorem rqe_fl4PerformTcb (blk call don : Bool) (i : TcbInvocation) :
    RQE (fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB i)) := rqe_invokeTcb i

theorem rqe_fl4PerformFl4Tcb (blk call don : Bool) (i : Fl4TcbInvocation) :
    RQE (fl4PerformInvocation (Z := Unit) blk call don (.invokeFl4TCB i)) := rqe_invokeFl4Tcb i

theorem rqe_fl4PerformCnode (blk call don : Bool) (i : CnodeInvocation) :
    RQE (fl4PerformInvocation (Z := Unit) blk call don (.invokeCNode i)) := by
  show RQE (do invokeCnode (Z := Unit) i; NonDetE.returnOk [])
  exact Vs.dke_bind (rqe_invokeCnode i) fun _ => Vs.dke_returnOk _

theorem rqe_withoutPreemption' {α : Type} {m : SMonad Unit α} (h : RQ m) :
    RQE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact dke_liftE h
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible refine rqe_withoutPreemption' ?_)

theorem rqe_resolveAddressBits (p : Cap × CapRef) : RQE (resolveAddressBits (Z := Unit) p) := rqe_rab p
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_resolveAddressBits _)

theorem rq_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : RQE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_lookupSlotForThread' _ _)

theorem rq_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : RQE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_lookupCapAndSlot' _ _)

theorem rq_lookupCap' (thread : ObjRef) (ref : CapRef) : RQE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_lookupCap' _ _)

theorem rq_captransferFromWords' (ptr : Word) : RQ (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_captransferFromWords' _)

theorem rq_loadCapTransfer' (buffer : ObjRef) : RQ (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_loadCapTransfer' _)

theorem rq_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : RQ (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setExtraBadge' _ _ _)

theorem rqe_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : RQE m) :
    RQE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible refine rqe_lookupErrorOnFailure' _ ?_)

theorem rq_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : RQE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_lookupSlotForCnodeOp' _ _ _ _)

theorem rq_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : RQE (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact rq_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_lookupTargetSlot' _ _ _)

theorem rq_archPostResetUntyped' (_isDevice : Bool) (_sz : Nat) : RQ (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_archPostResetUntyped' _ _)



theorem rq_copyGlobalMappings' (newPm : ObjRef) : RQ (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_copyGlobalMappings' _)

theorem rq_initArchObjects' (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : RQ (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_initArchObjects' _ _ _ _ _ _)

theorem rq_createCap' (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool)
    (d : CslotPtr × ObjRef) : RQ (createCap (Z := Unit) type bits untyped isDevice d) := by
  obtain ⟨dest, oref⟩ := d
  unfold createCap; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_createCap' _ _ _ _ _)

theorem rq_ensureNoChildren' (cslotPtr : CslotPtr) : RQE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_ensureNoChildren' _)

theorem rq_getRefillTail' (scPtr : ObjRef) : RQ (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getRefillTail' _)

theorem rq_getRefills' (scPtr : ObjRef) : RQ (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getRefills' _)

theorem rq_refillAddTail' (scPtr : ObjRef) (newRefill : Refill) : RQ (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_refillAddTail' _ _)

theorem rq_refillFull' (scPtr : ObjRef) : RQ (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_refillFull' _)

theorem rq_updateRefillTl' (scPtr : ObjRef) (f : Refill → Refill) : RQ (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_updateRefillTl' _ _)

theorem rq_scheduleUsed' (scPtr : ObjRef) (new : Refill) : RQ (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_scheduleUsed' _ _)

theorem rq_refillSize' (scPtr : ObjRef) : RQ (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_refillSize' _)

theorem rq_refillSingle' (scPtr : ObjRef) : RQ (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_refillSingle' _)

theorem rq_chargeEntireHeadRefill' (scPtr : ObjRef) (usage : Ticks) : RQ (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_chargeEntireHeadRefill' _ _)

theorem rq_mergeNonoverlappingHeadRefill' (scPtr : ObjRef) : RQ (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_mergeNonoverlappingHeadRefill' _)

theorem rq_updateIrqState' (irq : Irq) (irqState : X64IRQState) : RQ (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_updateIrqState' _ _)

theorem rqe_archInvokeIrqControl' (i : ArchIrqControlInvocation) : RQE (archInvokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold archInvokeIrqControl <;> zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_archInvokeIrqControl' _)

theorem rq_invokeIrqControl' (i : IrqControlInvocation) : RQE (invokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeIrqControl <;> zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_invokeIrqControl' _)



theorem rqe_invokeFl4IrqControl' (i : Fl4IrqControlInvocation) : RQE (invokeFl4IrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeFl4IrqControl <;> zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_invokeFl4IrqControl' _)

theorem rqe_archDeriveCap' (c : ArchCap) : RQE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_archDeriveCap' _)

theorem rqe_deriveCap' (sl : CslotPtr) (c : Cap) : RQE (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_deriveCap' _ _)

theorem rq_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : RQ (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_makeArchFaultMsg' _ _)

theorem rqe_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : RQE m) :
    RQE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible refine rqe_unifyFailure' ?_)

theorem rq_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : RQE m) :
    RQ (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible refine rq_emptyOnFailure' ?_)

theorem rq_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : RQE m) :
    RQ (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible refine rq_constOnFailure' _ ?_)

theorem rqe_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : RQE m) :
    RQE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible refine rqe_capFaultOnFailure' _ _ ?_)

theorem rq_loadWordOffs' (ptr : ObjRef) (offs : Nat) : RQ (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; exact rq_doMachineOp _
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_loadWordOffs' _ _)

theorem rq_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : RQ (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact dk_pure _
  · unfold getExtraCptrs; exact dk_liftM _ (dk_mapM (fun _ => rq_loadWordOffs' _ _) _)
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getExtraCptrs' _ _)

theorem rq_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : RQ (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getReceiveSlots' _ _)

theorem rq_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      RQ (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; zq_auto0
  | n, (c, sl) :: rest, slots, mi => by
    have ih := rq_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    zq_auto0
    all_goals first | exact ih _ _ | skip
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_transferCapsLoop' _ _ _ _ _ _)

theorem rq_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : RQE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_lookupExtraCaps' _ _ _)

theorem rq_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : RQ (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_copyMrs' _ _ _ _ _)

theorem rq_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : RQ (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_transferCaps' _ _ _ _ _)

theorem rq_makeFaultMsg' (f : Fault) (t : ObjRef) : RQ (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_makeFaultMsg' _ _)

theorem rq_handleOverrun' (scPtr : ObjRef) (usage : Ticks) : RQ (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_handleOverrun' _ _)

theorem rq_headInsufficientLoop' (scPtr : ObjRef) : RQ (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_headInsufficientLoop' _)

theorem rq_getMessageInfo' (thread : ObjRef) : RQ (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getMessageInfo' _)

theorem rq_tcbEpAppend' (tptr epPtr : ObjRef) (isRecv : Bool) : RQ (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_tcbEpAppend' _ _ _)

theorem rq_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : RQ (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_doNormalTransfer' _ _ _ _ _ _ _)

theorem rq_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : RQ (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_doFaultTransfer' _ _ _ _)

theorem rq_bindScReply' (scPtr replyPtr : ObjRef) : RQ (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_bindScReply' _ _)

theorem rq_isValidTimeoutHandler' (tptr : ObjRef) : RQ (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_isValidTimeoutHandler' _)

theorem rq_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : RQ (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_doIpcTransfer' _ _ _ _ _)

theorem rq_replyPush' (caller callee replyPtr : ObjRef) (canDonate : Bool) : RQ (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_replyPush' _ _ _ _)

theorem rq_sendIpcBlocked' (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : RQ (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_sendIpcBlocked' _ _ _ _ _ _)

theorem rq_sendIpc' (b c : Bool) (bd : Badge) (g gr d : Bool) (t e : ObjRef) : RQ (sendIpc (Z := Unit) b c bd g gr d t e) := by
  unfold sendIpc; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_sendIpc' _ _ _ _ _ _ _ _)

theorem rq_sendFaultIpc' (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : RQ (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_sendFaultIpc' _ _ _ _)

theorem rq_refillBudgetCheckRoundRobin' (usage : Ticks) : RQ (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_refillBudgetCheckRoundRobin' _)

theorem rq_refillBudgetCheck' (usage : Ticks) : RQ (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_refillBudgetCheck' _)

theorem rq_maybeAddEmptyTail' (scPtr : ObjRef) : RQ (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_maybeAddEmptyTail' _)

theorem rq_maybeDonateSc' (tcbPtr ntfnPtr : ObjRef) : RQ (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_maybeDonateSc' _ _)

theorem rq_updateWaitingNtfn' (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : RQ (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_updateWaitingNtfn' _ _ _)

theorem rq_handleTimeout' (tptr : ObjRef) (ex : Fault) : RQ (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_handleTimeout' _ _)

theorem rq_getMrs' (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : RQ (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getMrs' _ _ _)

theorem rq_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    RQ (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_handleFaultReply' _ _ _ _)

theorem rq_returnConsumed' (scPtr : ObjRef) : RQ (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_returnConsumed' _)

theorem rq_schedContextBindNtfn' (sc ntfn : ObjRef) : RQ (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedContextBindNtfn' _ _)

theorem rq_schedContextYieldTo' (scPtr : ObjRef) : RQ (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedContextYieldTo' _)

theorem rq_getScActive' (scPtr : ObjRef) : RQ (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getScActive' _)

theorem rq_commitTime' : RQ (commitTime (Z := Unit) ) := by
  unfold commitTime; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_commitTime' )



theorem rq_archInvokeIrqHandler' (i : IrqHandlerInvocation) : RQ (archInvokeIrqHandler (Z := Unit) i) := by
  cases i <;> unfold archInvokeIrqHandler <;> zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_archInvokeIrqHandler' _)

theorem rq_sendSignal' (n : ObjRef) (b : Badge) : RQ (sendSignal (Z := Unit) n b) := by
  unfold sendSignal; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_sendSignal' _ _)

theorem rq_doReplyTransfer' (s r : ObjRef) (g : Bool) : RQ (doReplyTransfer (Z := Unit) s r g) := by
  unfold doReplyTransfer; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_doReplyTransfer' _ _ _)

theorem rq_invokeSchedContext' (i : SchedContextInvocation) : RQ (invokeSchedContext (Z := Unit) i) := by
  cases i <;> unfold invokeSchedContext <;> zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_invokeSchedContext' _)


theorem rq_invokeIrqHandler' (i : IrqHandlerInvocation) : RQ (invokeIrqHandler (Z := Unit) i) := by
  cases i <;> unfold invokeIrqHandler <;> zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_invokeIrqHandler' _)

theorem rq_lookupSourceSlot' (c : Cap) (r : CapRef) (n : Nat) : RQE (lookupSourceSlot (Z := Unit) c r n) := by
  unfold lookupSourceSlot; exact rq_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_lookupSourceSlot' _ _ _)

theorem rqe_ensureEmpty' (sl : CslotPtr) : RQE (ensureEmpty (Z := Unit) sl) := by
  unfold ensureEmpty; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_ensureEmpty' _)

theorem rqe_checkVpAlignment' (sz : VMPageSize) (v : Word) : RQE (checkVpAlignment (Z := Unit) sz v) := by
  unfold checkVpAlignment; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_checkVpAlignment' _ _)

theorem rqe_createMappingEntries' (base : Paddr) (vptr : VSpaceRef) (sz : VMPageSize) (r : VMRights)
    (at' : VMAttributes) (p : ObjRef) : RQE (createMappingEntries (Z := Unit) base vptr sz r at' p) := by
  cases sz <;> unfold createMappingEntries <;> zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_createMappingEntries' _ _ _ _ _ _)

theorem rqe_ensureSafeMapping' (e : VMPageEntry × ObjRef) : RQE (ensureSafeMapping (Z := Unit) e) := by
  unfold ensureSafeMapping; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_ensureSafeMapping' _)

theorem rqe_decodePageInvocation' (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) : RQE (decodePageInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageInvocation; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_decodePageInvocation' _ _ _ _ _)

theorem rqe_fbMap (b : Fl4FrameBatchInvocation) (sl : CslotPtr) (v : Data) : RQE (fbMap (Z := Unit) b sl v) := by
  unfold fbMap; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_fbMap _ _ _)

theorem rq_unmapPageUnflushed (sz : VMPageSize) (vs : ObjRef) (v : VSpaceRef) (p : ObjRef) :
    RQ (unmapPageUnflushed (Z := Unit) sz vs v p) := by
  unfold unmapPageUnflushed; zq_auto0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_unmapPageUnflushed _ _ _ _)

theorem rqe_fbCode {α : Type} {m : SEMonad Unit α} (h : RQE m) : RQE (fbCode (Z := Unit) m) := by
  unfold fbCode; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible refine rqe_fbCode ?_)

theorem rqe_fbDelete (sl : CslotPtr) : RQE (fbDelete (Z := Unit) sl) := by
  unfold fbDelete; exact dke_handleE (rq_capDelete sl) fun _ => dke_throw _
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_fbDelete _)

/-- fb3: one `X86PML4FrameBatch` entry. -/
theorem rq_fbEntry (b : Fl4FrameBatchInvocation) (w : Data × Data × Data) : RQE (fbEntry (Z := Unit) b w) := by
  unfold fbEntry; zq_auto0

/-- fb3: the batch (SpecInvFbD's `fk_performFrameBatch`). -/
theorem rq_performFrameBatch (b : Fl4FrameBatchInvocation) : RQ (performFrameBatch (Z := Unit) b) :=
  fk_performFrameBatch (fun w => rq_fbEntry b w) (rq_flushAll _ _)
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_performFrameBatch _)


end

end Fl4Proofs.P3.SInvRr
