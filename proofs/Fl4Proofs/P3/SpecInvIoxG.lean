/-
P3 (line p3J, gen 4): **the IOAPIC-count frame, leaves** (spec side only, outside the JAtZ cone): `SpecInvDomG` with the projection
`dlV` (the domain list) replaced by `ioxV` (`x64_num_ioapics`, `x64_ioapic_nirqs`), a scripted renaming
(`scratch/p3J/genIox.py`; VsDom's `FK` combinators are generic in the projection). No sorry.
-/
import Fl4Proofs.P3.SpecInvIoxF
import Fl4Proofs.P3.SpecInvDomL
import Fl4Proofs.P3.SpecInvFbD
open Classical

namespace Fl4Proofs.P3.SInvIox
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

set_option maxRecDepth 20000

theorem iox_setCap (c : Cap) (sl : CslotPtr) : IOX (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setCap _ _)

theorem iox_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    IOX (portOut (Z := Unit) f w) := by
  unfold portOut; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_portOut _ _)

theorem iox_getPt (ptr : ObjRef) : IOX (getPt (Z := Unit) ptr) := by
  unfold getPt; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getPt _)

theorem iox_getPte (ptr : ObjRef) : IOX (getPte (Z := Unit) ptr) := by
  unfold getPte; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getPte _)

theorem iox_getPd (ptr : ObjRef) : IOX (getPd (Z := Unit) ptr) := by
  unfold getPd; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getPd _)

theorem iox_getPde (ptr : ObjRef) : IOX (getPde (Z := Unit) ptr) := by
  unfold getPde; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getPde _)

theorem iox_getPml4 (ptr : ObjRef) : IOX (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getPml4 _)

theorem iox_getPml4e (ptr : ObjRef) : IOX (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getPml4e _)

theorem iox_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : IOXE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_lookupPdptSlot _ _)

theorem iox_getPdpt (ptr : ObjRef) : IOX (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getPdpt _)

theorem iox_getPdpte (ptr : ObjRef) : IOX (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getPdpte _)

theorem iox_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : IOXE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_lookupPdSlot _ _)

theorem iox_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : IOXE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_lookupPtSlot _ _)

theorem iox_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : IOX (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setPdpt _ _)

theorem iox_storePdpte (p : ObjRef) (pte : PDPTE) : IOX (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_storePdpte _ _)

theorem iox_getAsidPool (ptr : ObjRef) : IOX (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getAsidPool _)

theorem iox_findVspaceForAsid (asid : Asid) : IOXE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_findVspaceForAsid _)

theorem iox_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : IOX (setPt (Z := Unit) ptr pt) := by
  unfold setPt; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setPt _ _)

theorem iox_storePte (p : ObjRef) (pte : PTE) : IOX (storePte (Z := Unit) p pte) := by
  unfold storePte; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_storePte _ _)

theorem iox_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : IOX (setPd (Z := Unit) ptr pd) := by
  unfold setPd; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setPd _ _)

theorem iox_storePde (p : ObjRef) (pde : PDE) : IOX (storePde (Z := Unit) p pde) := by
  unfold storePde; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_storePde _ _)

theorem iox_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : IOX (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_unmapPage _ _ _ _)

theorem iox_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : IOX (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_performPageInvocationUnmap _ _)

theorem iox_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : IOX (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setAsidPool _ _)

theorem iox_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : IOX (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_flushTable _ _ _ _)

theorem iox_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : IOX (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setPml4 _ _)

theorem iox_setOriginal (slot : CslotPtr) (v : Bool) : IOX (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setOriginal _ _)

theorem iox_updateCdt (f : Cdt → Cdt) : IOX (updateCdt (Z := Unit) f) := by
  unfold updateCdt; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_updateCdt _)

theorem iox_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : IOX (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setUntypedCapAsFull _ _ _)

theorem iox_retypeRegion (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : IOX (retypeRegion (Z := Unit) ptr numObjects oBits type dev) := by
  unfold retypeRegion; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_retypeRegion _ _ _ _ _)

theorem iox_storePml4e (p : ObjRef) (pte : PML4E) : IOX (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_storePml4e _ _)

theorem iox_flushAll (vspace : ObjRef) (asid : Asid) : IOX (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_flushAll _ _)

theorem iox_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : IOX (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_unmapPdpt _ _ _)

theorem iox_setIoportMask (f l : IoPort) (val : Bool) : IOX (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setIoportMask _ _ _)

theorem iox_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : IOX (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_invalidatePageStructureCacheAsid _ _)

theorem iox_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : IOX (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_unmapPd _ _ _)

theorem iox_deleteObjects (ptr : Word) (bits : Nat) : IOX (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_deleteObjects _ _)

theorem iox_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : IOX (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_capInsert _ _ _)

theorem iox_portIn (f : MachineMonad Data) : IOX (portIn (Z := Unit) f) := by
  unfold portIn; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_portIn _)

theorem iox_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : IOX (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_unmapPageTable _ _ _)

theorem iox_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : IOX (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_storeAsidPoolEntry _ _ _)

theorem iox_performPageInvocation (iv : PageInvocation) : IOX (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_performPageInvocation _)

theorem iox_performPageTableInvocation (iv : PageTableInvocation) : IOX (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_performPageTableInvocation _)

theorem iox_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : IOX (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_performPageDirectoryInvocation _)

theorem iox_performPdptInvocation (iv : PdptInvocation) : IOX (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_performPdptInvocation _)

theorem iox_performAsidPoolInvocation (iv : AsidPoolInvocation) : IOX (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_performAsidPoolInvocation _)

theorem iox_performAsidControlInvocation (iv : AsidControlInvocation) : IOX (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_performAsidControlInvocation _)

theorem iox_performIoPortInvocation (i : IoPortInvocation) : IOX (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_performIoPortInvocation _)

theorem iox_performIoportControlInvocation (i : IoPortControlInvocation) : IOX (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_performIoportControlInvocation _)

theorem iox_performDeriveSubframe (iv : Fl4SubframeInvocation) : IOX (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_performDeriveSubframe _)

theorem iox_performTestAndClearAccessed (_slot : ObjRef) : IOX (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_performTestAndClearAccessed _)

theorem iox_performPml4Flush (i : Fl4Pml4Invocation) : IOX (performPml4Flush (Z := Unit) i) := by
  cases i; unfold performPml4Flush; exact iox_flushAll _ _

theorem ioxe_archPerformInvocation (i : ArchInvocation) : IOXE (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; apply dke_liftE; cases i <;> iox_auto0

theorem iox_threadSet' (f : Tcb → Tcb) (t : ObjRef) : IOX (threadSet (Z := Unit) f t) := by
  unfold threadSet; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_threadSet' _ _)

theorem iox_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : IOX (threadGet (Z := Unit) f t) := by
  unfold threadGet; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_threadGet' _ _)

theorem iox_setThreadState' (t : ObjRef) (ts : ThreadState) : IOX (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setThreadState' _ _)

theorem iox_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    IOX (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getSimpleKo' _ _)

theorem iox_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    IOX (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setSimpleKo' _ _ _)

theorem iox_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    IOX (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_updateSkObjRef' _ _ _ _)

theorem iox_getSchedContext' (q : ObjRef) : IOX (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getSchedContext' _)

theorem iox_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    IOX (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_updateSchedContext' _ _)

theorem iox_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : IOX (asUser (Z := Unit) t u) := by
  unfold asUser; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_asUser' _ _)

theorem iox_replyUnlinkTcb' (t r : ObjRef) : IOX (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_replyUnlinkTcb' _ _)

theorem iox_getThreadState' (t : ObjRef) : IOX (getThreadState (Z := Unit) t) := by
  unfold getThreadState; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getThreadState' _)

theorem iox_cancelIpc' (t : ObjRef) : IOX (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_cancelIpc' _)

theorem iox_suspend' (t : ObjRef) : IOX (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc tcbSchedAction getTcbQueue setTcbQueue tcbReleaseRemove
    schedContextCancelYieldTo getTcbObjRef getThreadState
  iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_suspend' _)

theorem iox_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : IOX (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getSkObjRef' _ _ _)

theorem iox_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : IOX (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getScObjRef' _ _)

theorem iox_getIrqSlot' (irq : Irq) : IOX (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getIrqSlot' _)

theorem iox_isFinalCap' (c : Cap) : IOX (isFinalCap (Z := Unit) c) := by
  unfold isFinalCap; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_isFinalCap' _)

theorem iox_hwAsidInvalidate' (a : Asid) (v : ObjRef) : IOX (hwAsidInvalidate (Z := Unit) a v) := by
  unfold hwAsidInvalidate; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_hwAsidInvalidate' _ _)

theorem iox_getCurrentCr3' : IOX (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getCurrentCr3' )

theorem iox_setCurrentCr3' (c : Cr3) : IOX (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setCurrentCr3' _)

theorem iox_setCurrentVspaceRoot' (v : ObjRef) (a : Asid) : IOX (setCurrentVspaceRoot (Z := Unit) v a) := by
  unfold setCurrentVspaceRoot; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setCurrentVspaceRoot' _ _)

theorem iox_setVmRoot' (t : ObjRef) : IOX (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setVmRoot' _)

theorem iox_freeIoportRange' (f l : IoPort) : IOX (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_freeIoportRange' _ _)

theorem iox_setIrqState' (i : IrqState) (irq : Irq) : IOX (setIrqState (Z := Unit) i irq) := by
  unfold setIrqState; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setIrqState' _ _)

theorem iox_deletedIrqHandler' (irq : Irq) : IOX (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_deletedIrqHandler' _)

theorem iox_lookupIpcBuffer' (b : Bool) (t : ObjRef) : IOX (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_lookupIpcBuffer' _ _)

theorem iox_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : IOX (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_storeWordOffs' _ _ _)

theorem iox_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : IOX (setMrs (Z := Unit) t b m) := by
  unfold setMrs; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setMrs' _ _ _)

theorem iox_setMessageInfo' (t : ObjRef) (i : MessageInfo) : IOX (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setMessageInfo' _ _)

theorem iox_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : IOX (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_archThreadSet' _ _)

theorem iox_saveFpuState' (t : ObjRef) : IOX (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_saveFpuState' _)

theorem iox_loadFpuState' (t : ObjRef) : IOX (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_loadFpuState' _)

theorem iox_setX64CurrentFpuOwner' (o : Option ObjRef) : IOX (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setX64CurrentFpuOwner' _)

theorem iox_switchLocalFpuOwner' (o : Option ObjRef) : IOX (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_switchLocalFpuOwner' _)

theorem iox_getTcbQueue' (d : Domain) (p : Priority) : IOX (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getTcbQueue' _ _)

theorem iox_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : IOX (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setTcbQueue' _ _ _)

theorem iox_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : IOX (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_tcbSchedAction' _ _)

theorem iox_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : IOX (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getTcbObjRef' _ _)

theorem iox_setSchedulerAction' (a : SchedulerAction) : IOX (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setSchedulerAction' _)

theorem iox_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : IOX (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getScRefillSufficient' _ _)

theorem iox_getScRefillReady' (sc : ObjRef) : IOX (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getScRefillReady' _)

theorem iox_tcbReleaseRemove' (t : ObjRef) : IOX (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_tcbReleaseRemove' _)

theorem iox_rescheduleRequired' : IOX (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_rescheduleRequired' )

theorem iox_testReschedule' (t : ObjRef) : IOX (testReschedule (Z := Unit) t) := by
  unfold testReschedule; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_testReschedule' _)

theorem iox_possibleSwitchTo' (t : ObjRef) : IOX (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_possibleSwitchTo' _)

theorem iox_tcbEpDequeue' (t e : ObjRef) : IOX (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_tcbEpDequeue' _ _)

theorem iox_tcbNtfnDequeue' (t n : ObjRef) : IOX (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_tcbNtfnDequeue' _ _)

theorem iox_isRoundRobin' (sc : ObjRef) : IOX (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_isRoundRobin' _)

theorem iox_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : IOX (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_updateRefillHd' _ _)

theorem iox_getRefillHead' (sc : ObjRef) : IOX (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getRefillHead' _)

theorem iox_refillPopHead' (sc : ObjRef) : IOX (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_refillPopHead' _)

theorem iox_mergeOverlappingRefills' (sc : ObjRef) : IOX (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_mergeOverlappingRefills' _)

theorem iox_refillHeadOverlappingLoop' (sc : ObjRef) : IOX (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_refillHeadOverlappingLoop' _)

theorem iox_refillUnblockCheck' (sc : ObjRef) : IOX (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_refillUnblockCheck' _)

theorem iox_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : IOX (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_ifCondRefillUnblockCheck' _ _ _)

theorem iox_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) : IOX (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem iox_restartThreadIfNoFault' (t : ObjRef) : IOX (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_restartThreadIfNoFault' _)

theorem iox_removeAndRestartEpQueuedThread' (t e : ObjRef) : IOX (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_removeAndRestartEpQueuedThread' _ _)

theorem iox_removeAndRestartNtfnQueuedThread' (t n : ObjRef) : IOX (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_removeAndRestartNtfnQueuedThread' _ _)

theorem iox_replyUnlinkSc' (sc r : ObjRef) : IOX (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_replyUnlinkSc' _ _)

theorem iox_schedContextDonate' (sc t : ObjRef) : IOX (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedContextDonate' _ _)

theorem iox_schedContextUpdateConsumed' (sc : ObjRef) : IOX (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedContextUpdateConsumed' _)

theorem iox_replyFromKernel' (t : ObjRef) (x : Data × List Data) : IOX (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_replyFromKernel' _ _)

theorem iox_setConsumed' (sc t : ObjRef) : IOX (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setConsumed' _ _)

theorem iox_schedContextCancelYieldTo' (t : ObjRef) : IOX (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedContextCancelYieldTo' _)

theorem iox_fpuRelease' (t : ObjRef) : IOX (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_fpuRelease' _)

theorem iox_deleteAsidPool' (b : Asid) (p : ObjRef) : IOX (deleteAsidPool (Z := Unit) b p) := by
  unfold deleteAsidPool; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_deleteAsidPool' _ _)

theorem iox_deleteAsid' (a : Asid) (p : ObjRef) : IOX (deleteAsid (Z := Unit) a p) := by
  unfold deleteAsid; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_deleteAsid' _ _)

theorem iox_archPostCapDeletion' (c : ArchCap) : IOX (archPostCapDeletion (Z := Unit) c) := by
  unfold archPostCapDeletion; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_archPostCapDeletion' _)

theorem iox_postCapDeletion' (c : Cap) : IOX (postCapDeletion (Z := Unit) c) := by
  unfold postCapDeletion; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_postCapDeletion' _)

theorem iox_emptySlot' (sl : CslotPtr) (c : Cap) : IOX (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_emptySlot' _ _)

theorem iox_cancelAllIpc' (e : ObjRef) : IOX (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_cancelAllIpc' _)

theorem iox_schedContextMaybeUnbindNtfn' (n : ObjRef) : IOX (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedContextMaybeUnbindNtfn' _)

theorem iox_unbindMaybeNotification' (n : ObjRef) : IOX (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_unbindMaybeNotification' _)

theorem iox_cancelAllSignals' (n : ObjRef) : IOX (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_cancelAllSignals' _)

theorem iox_replyRemove' (t r : ObjRef) : IOX (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_replyRemove' _ _)

theorem iox_unbindNotification' (t : ObjRef) : IOX (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_unbindNotification' _)

theorem iox_schedContextUnbindTcb' (sc : ObjRef) : IOX (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedContextUnbindTcb' _)

theorem iox_completeYieldTo' (t : ObjRef) : IOX (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_completeYieldTo' _)

theorem iox_unbindFromSc' (t : ObjRef) : IOX (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_unbindFromSc' _)

theorem iox_schedContextUnbindAllTcbs' (sc : ObjRef) : IOX (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedContextUnbindAllTcbs' _)

theorem iox_schedContextUnbindNtfn' (sc : ObjRef) : IOX (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedContextUnbindNtfn' _)

theorem iox_schedContextUnbindReply' (sc : ObjRef) : IOX (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedContextUnbindReply' _)

theorem iox_schedContextUnbindYieldFrom' (sc : ObjRef) : IOX (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedContextUnbindYieldFrom' _)

theorem iox_schedContextSetInactive' (sc : ObjRef) : IOX (schedContextSetInactive (Z := Unit) sc) := by
  unfold schedContextSetInactive; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedContextSetInactive' _)

theorem iox_prepareThreadDelete' (t : ObjRef) : IOX (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_prepareThreadDelete' _)

theorem iox_archFinaliseCap' (c : ArchCap) (x : Bool) : IOX (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_archFinaliseCap' _ _)

theorem iox_fastFinalise' (c : Cap) (b : Bool) : IOX (fastFinalise (Z := Unit) c b) := by
  unfold fastFinalise; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_fastFinalise' _ _)

theorem iox_capDeleteOne' (sl : CslotPtr) : IOX (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_capDeleteOne' _)

theorem iox_deletingIrqHandler' (irq : Irq) : IOX (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_deletingIrqHandler' _)

theorem iox_finaliseCap (c : Cap) (b : Bool) : IOX (finaliseCap (Z := Unit) c b) := by
  cases c <;> unfold finaliseCap <;> iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_finaliseCap _ _)

theorem iox_capSwap' (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) : IOX (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_capSwap' _ _ _ _)

theorem iox_capSwapForDelete' (s1 s2 : CslotPtr) : IOX (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_capSwapForDelete' _ _)

theorem ioxe_preemptionPoint' : IOXE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_preemptionPoint')

set_option maxHeartbeats 4000000 in
theorem iox_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, IOX (f k)) (k : RecDelCall) : IOXE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, IOXE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF; iox_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF; iox_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF
    split <;> iox_auto
    all_goals exact hrec' _

/-- `rec_del` keeps the domain list. -/
theorem ioxe_recDel (c : RecDelCall) : IOXE (recDel (Z := Unit) c) := by
  intro σ x hx
  let f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)) := fun _ t =>
    ({y | ioxV y.2 = ioxV t}, True)
  have hf : ∀ k t, (fun r c => recDelF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy => iox_recDelF (f := f) (fun _ _ _ hz => hz) k t y hy, fun _ => trivial⟩
  exact (Fl4Proofs.P3.SInvDomL.lfp_le_prefixed' _ f hf c σ).1 hx
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_recDel _)

set_option maxHeartbeats 4000000 in
theorem iox_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IOX (f k)) (sl : CslotPtr) : IOXE (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IOXE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF
  iox_auto
  all_goals exact hrec' _

/-- `cap_revoke` keeps the domain list. -/
theorem ioxe_capRevoke (sl : CslotPtr) : IOXE (capRevoke (Z := Unit) sl) := by
  intro σ x hx
  let f : CslotPtr → NonDet (State Unit) (Except Unit Unit) := fun _ t =>
    ({y | ioxV y.2 = ioxV t}, True)
  have hf : ∀ k t, (fun r c => capRevokeF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy => iox_capRevokeF (f := f) (fun _ _ _ hz => hz) k t y hy, fun _ => trivial⟩
  exact (Fl4Proofs.P3.SInvDomL.lfp_le_prefixed' _ f hf sl σ).1 hx
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_capRevoke _)

theorem iox_capDelete (sl : CslotPtr) : IOXE (capDelete (Z := Unit) sl) := by
  unfold capDelete; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_capDelete _)

theorem iox_capMove' (c : Cap) (s1 s2 : CslotPtr) : IOX (capMove (Z := Unit) c s1 s2) := by
  unfold capMove; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_capMove' _ _ _)

theorem iox_removeAndRestartBadgedThread' (t e : ObjRef) (b : Badge) :
    IOX (removeAndRestartBadgedThread (Z := Unit) t e b) := by
  unfold removeAndRestartBadgedThread; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_removeAndRestartBadgedThread' _ _ _)

theorem iox_cancelBadgedSends' (e : ObjRef) (b : Badge) : IOX (cancelBadgedSends (Z := Unit) e b) := by
  unfold cancelBadgedSends; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_cancelBadgedSends' _ _)

theorem ioxe_invokeCnode (i : CnodeInvocation) : IOXE (invokeCnode (Z := Unit) i) := by
  cases i <;> unfold invokeCnode withoutPreemption <;> iox_auto0

theorem iox_orderedInsert' {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : IOX (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_orderedInsert' _ _ _ _)

theorem iox_readyTimesAppend' (t : ObjRef) (q : List ObjRef) : IOX (readyTimesAppend (Z := Unit) t q) := by
  unfold readyTimesAppend; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_readyTimesAppend' _ _)

theorem iox_tcbReleaseEnqueue' (t : ObjRef) : IOX (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_tcbReleaseEnqueue' _)

theorem iox_tcbAppend' (t : ObjRef) (q : List ObjRef) : IOX (tcbAppend (Z := Unit) t q) := by
  unfold tcbAppend; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_tcbAppend' _ _)

theorem iox_postpone' (sc : ObjRef) : IOX (postpone (Z := Unit) sc) := by
  unfold postpone; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_postpone' _)

theorem iox_threadSetPriority' (t : ObjRef) (p : Priority) : IOX (threadSetPriority (Z := Unit) t p) := by
  unfold threadSetPriority; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_threadSetPriority' _ _)

theorem iox_reorderEp' (e t : ObjRef) : IOX (reorderEp (Z := Unit) e t) := by
  unfold reorderEp; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_reorderEp' _ _)

theorem iox_reorderNtfn' (n t : ObjRef) : IOX (reorderNtfn (Z := Unit) n t) := by
  unfold reorderNtfn; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_reorderNtfn' _ _)

theorem iox_archPostModifyRegisters' (c t : ObjRef) : IOX (archPostModifyRegisters (Z := Unit) c t) := by
  unfold archPostModifyRegisters; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_archPostModifyRegisters' _ _)

theorem iox_schedContextResume' (sc : ObjRef) : IOX (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedContextResume' _)

theorem iox_testPossibleSwitchTo' (t : ObjRef) : IOX (testPossibleSwitchTo (Z := Unit) t) := by
  unfold testPossibleSwitchTo; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_testPossibleSwitchTo' _)

theorem iox_ifSporadicCurScTestRefillUnblockCheck' (o : Option ObjRef) : IOX (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScTestRefillUnblockCheck; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_ifSporadicCurScTestRefillUnblockCheck' _)

theorem iox_restart' (t : ObjRef) : IOX (restart (Z := Unit) t) := by
  unfold restart; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_restart' _)

theorem iox_setMcpriority' (t : ObjRef) (m : Priority) : IOX (setMcpriority (Z := Unit) t m) := by
  unfold setMcpriority; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setMcpriority' _ _)

theorem iox_setPriority' (t : ObjRef) (p : Priority) : IOX (setPriority (Z := Unit) t p) := by
  unfold setPriority; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setPriority' _ _)

theorem iox_schedContextBindTcb' (sc t : ObjRef) : IOX (schedContextBindTcb (Z := Unit) sc t) := by
  unfold schedContextBindTcb; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedContextBindTcb' _ _)

theorem iox_bindNotification' (t n : ObjRef) : IOX (bindNotification (Z := Unit) t n) := by
  unfold bindNotification; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_bindNotification' _ _)

theorem iox_setFlags' (t : ObjRef) (f : TcbFlags) : IOX (setFlags (Z := Unit) t f) := by
  unfold setFlags; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setFlags' _ _)

theorem iox_lazyFpuRestore' (t : ObjRef) : IOX (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_lazyFpuRestore' _)

theorem iox_archPostSetFlags' (t : ObjRef) (f : TcbFlags) : IOX (archPostSetFlags (Z := Unit) t f) := by
  unfold archPostSetFlags; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_archPostSetFlags' _ _)

theorem iox_checkCapAt' (c : Cap) (sl : CslotPtr) {m : SMonad Unit Unit} (h : IOX m) :
    IOX (checkCapAt (Z := Unit) c sl m) := by
  unfold checkCapAt; iox_auto0; exact h
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible refine iox_checkCapAt' _ _ ?_)

theorem ioxe_installTcbCap' (t : ObjRef) (sl : CslotPtr) (n : Nat) (o : Option (Cap × CslotPtr)) :
    IOXE (installTcbCap (Z := Unit) t sl n o) := by
  unfold installTcbCap; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_installTcbCap' _ _ _ _)

theorem ioxe_installTcbFrameCap' (t : ObjRef) (sl : CslotPtr) (b : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    IOXE (installTcbFrameCap (Z := Unit) t sl b) := by
  unfold installTcbFrameCap; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_installTcbFrameCap' _ _ _)

theorem ioxe_invokeTcb (i : TcbInvocation) : IOXE (invokeTcb (Z := Unit) i) := by
  cases i <;> unfold invokeTcb <;> iox_auto0

theorem ioxe_invokeFl4Tcb (i : Fl4TcbInvocation) : IOXE (invokeFl4Tcb (Z := Unit) i) := by
  cases i <;> unfold invokeFl4Tcb <;> iox_auto0

theorem ioxe_fl4PerformTcb (blk call don : Bool) (i : TcbInvocation) :
    IOXE (fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB i)) := ioxe_invokeTcb i

theorem ioxe_fl4PerformFl4Tcb (blk call don : Bool) (i : Fl4TcbInvocation) :
    IOXE (fl4PerformInvocation (Z := Unit) blk call don (.invokeFl4TCB i)) := ioxe_invokeFl4Tcb i

theorem ioxe_fl4PerformCnode (blk call don : Bool) (i : CnodeInvocation) :
    IOXE (fl4PerformInvocation (Z := Unit) blk call don (.invokeCNode i)) := by
  show IOXE (do invokeCnode (Z := Unit) i; NonDetE.returnOk [])
  exact Vs.dke_bind (ioxe_invokeCnode i) fun _ => Vs.dke_returnOk _

theorem ioxe_withoutPreemption' {α : Type} {m : SMonad Unit α} (h : IOX m) :
    IOXE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact dke_liftE h
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible refine ioxe_withoutPreemption' ?_)

theorem ioxe_resolveAddressBits (p : Cap × CapRef) : IOXE (resolveAddressBits (Z := Unit) p) := ioxe_rab p
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_resolveAddressBits _)

theorem iox_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : IOXE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_lookupSlotForThread' _ _)

theorem iox_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : IOXE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_lookupCapAndSlot' _ _)

theorem iox_lookupCap' (thread : ObjRef) (ref : CapRef) : IOXE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_lookupCap' _ _)

theorem iox_captransferFromWords' (ptr : Word) : IOX (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_captransferFromWords' _)

theorem iox_loadCapTransfer' (buffer : ObjRef) : IOX (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_loadCapTransfer' _)

theorem iox_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : IOX (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setExtraBadge' _ _ _)

theorem ioxe_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : IOXE m) :
    IOXE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible refine ioxe_lookupErrorOnFailure' _ ?_)

theorem iox_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : IOXE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_lookupSlotForCnodeOp' _ _ _ _)

theorem iox_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : IOXE (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact iox_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_lookupTargetSlot' _ _ _)

theorem iox_archPostResetUntyped' (_isDevice : Bool) (_sz : Nat) : IOX (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_archPostResetUntyped' _ _)

theorem iox_resetUntypedCap' (srcSlot : CslotPtr) : IOXE (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_resetUntypedCap' _)

theorem iox_retypeRegionWith' (bitsApi : ApiObjectType → Nat → Nat) (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : IOX (retypeRegionWith (Z := Unit) bitsApi ptr numObjects oBits type dev) := by
  unfold retypeRegionWith; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_retypeRegionWith' _ _ _ _ _ _)

theorem iox_copyGlobalMappings' (newPm : ObjRef) : IOX (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_copyGlobalMappings' _)

theorem iox_initArchObjects' (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : IOX (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_initArchObjects' _ _ _ _ _ _)

theorem iox_createCap' (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool)
    (d : CslotPtr × ObjRef) : IOX (createCap (Z := Unit) type bits untyped isDevice d) := by
  obtain ⟨dest, oref⟩ := d
  unfold createCap; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_createCap' _ _ _ _ _)

theorem iox_ensureNoChildren' (cslotPtr : CslotPtr) : IOXE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_ensureNoChildren' _)

theorem iox_getRefillTail' (scPtr : ObjRef) : IOX (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getRefillTail' _)

theorem iox_getRefills' (scPtr : ObjRef) : IOX (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getRefills' _)

theorem iox_refillAddTail' (scPtr : ObjRef) (newRefill : Refill) : IOX (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_refillAddTail' _ _)

theorem iox_refillFull' (scPtr : ObjRef) : IOX (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_refillFull' _)

theorem iox_updateRefillTl' (scPtr : ObjRef) (f : Refill → Refill) : IOX (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_updateRefillTl' _ _)

theorem iox_scheduleUsed' (scPtr : ObjRef) (new : Refill) : IOX (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_scheduleUsed' _ _)

theorem iox_refillSize' (scPtr : ObjRef) : IOX (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_refillSize' _)

theorem iox_refillSingle' (scPtr : ObjRef) : IOX (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_refillSingle' _)

theorem iox_chargeEntireHeadRefill' (scPtr : ObjRef) (usage : Ticks) : IOX (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_chargeEntireHeadRefill' _ _)

theorem iox_mergeNonoverlappingHeadRefill' (scPtr : ObjRef) : IOX (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_mergeNonoverlappingHeadRefill' _)

theorem iox_updateIrqState' (irq : Irq) (irqState : X64IRQState) : IOX (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_updateIrqState' _ _)

theorem ioxe_archInvokeIrqControl' (i : ArchIrqControlInvocation) : IOXE (archInvokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold archInvokeIrqControl <;> iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_archInvokeIrqControl' _)

theorem iox_invokeIrqControl' (i : IrqControlInvocation) : IOXE (invokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeIrqControl <;> iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_invokeIrqControl' _)

theorem ioxe_invokeUntypedWith' (b : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) :
    IOXE (invokeUntypedWith (Z := Unit) b ui) := by
  cases ui; unfold invokeUntypedWith; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_invokeUntypedWith' _ _)

theorem ioxe_fl4InvokeUntyped' (ui : UntypedInvocation) : IOXE (fl4InvokeUntyped (Z := Unit) ui) :=
  ioxe_invokeUntypedWith' _ ui
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_fl4InvokeUntyped' _)

theorem ioxe_invokeFl4IrqControl' (i : Fl4IrqControlInvocation) : IOXE (invokeFl4IrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeFl4IrqControl <;> iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_invokeFl4IrqControl' _)

theorem ioxe_archDeriveCap' (c : ArchCap) : IOXE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_archDeriveCap' _)

theorem ioxe_deriveCap' (sl : CslotPtr) (c : Cap) : IOXE (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_deriveCap' _ _)

theorem iox_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : IOX (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_makeArchFaultMsg' _ _)

theorem ioxe_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : IOXE m) :
    IOXE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible refine ioxe_unifyFailure' ?_)

theorem iox_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : IOXE m) :
    IOX (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible refine iox_emptyOnFailure' ?_)

theorem iox_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : IOXE m) :
    IOX (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible refine iox_constOnFailure' _ ?_)

theorem ioxe_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : IOXE m) :
    IOXE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible refine ioxe_capFaultOnFailure' _ _ ?_)

theorem iox_loadWordOffs' (ptr : ObjRef) (offs : Nat) : IOX (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; exact iox_doMachineOp _
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_loadWordOffs' _ _)

theorem iox_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : IOX (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact dk_pure _
  · unfold getExtraCptrs; exact dk_liftM _ (dk_mapM (fun _ => iox_loadWordOffs' _ _) _)
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getExtraCptrs' _ _)

theorem iox_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : IOX (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getReceiveSlots' _ _)

theorem iox_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      IOX (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; iox_auto0
  | n, (c, sl) :: rest, slots, mi => by
    have ih := iox_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    iox_auto0
    all_goals first | exact ih _ _ | skip
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_transferCapsLoop' _ _ _ _ _ _)

theorem iox_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : IOXE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_lookupExtraCaps' _ _ _)

theorem iox_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : IOX (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_copyMrs' _ _ _ _ _)

theorem iox_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : IOX (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_transferCaps' _ _ _ _ _)

theorem iox_makeFaultMsg' (f : Fault) (t : ObjRef) : IOX (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_makeFaultMsg' _ _)

theorem iox_handleOverrun' (scPtr : ObjRef) (usage : Ticks) : IOX (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_handleOverrun' _ _)

theorem iox_headInsufficientLoop' (scPtr : ObjRef) : IOX (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_headInsufficientLoop' _)

theorem iox_getMessageInfo' (thread : ObjRef) : IOX (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getMessageInfo' _)

theorem iox_tcbEpAppend' (tptr epPtr : ObjRef) (isRecv : Bool) : IOX (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_tcbEpAppend' _ _ _)

theorem iox_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : IOX (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_doNormalTransfer' _ _ _ _ _ _ _)

theorem iox_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : IOX (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_doFaultTransfer' _ _ _ _)

theorem iox_bindScReply' (scPtr replyPtr : ObjRef) : IOX (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_bindScReply' _ _)

theorem iox_isValidTimeoutHandler' (tptr : ObjRef) : IOX (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_isValidTimeoutHandler' _)

theorem iox_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : IOX (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_doIpcTransfer' _ _ _ _ _)

theorem iox_replyPush' (caller callee replyPtr : ObjRef) (canDonate : Bool) : IOX (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_replyPush' _ _ _ _)

theorem iox_sendIpcBlocked' (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : IOX (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_sendIpcBlocked' _ _ _ _ _ _)

theorem iox_sendIpc' (b c : Bool) (bd : Badge) (g gr d : Bool) (t e : ObjRef) : IOX (sendIpc (Z := Unit) b c bd g gr d t e) := by
  unfold sendIpc; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_sendIpc' _ _ _ _ _ _ _ _)

theorem iox_sendFaultIpc' (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : IOX (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_sendFaultIpc' _ _ _ _)

theorem iox_refillBudgetCheckRoundRobin' (usage : Ticks) : IOX (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_refillBudgetCheckRoundRobin' _)

theorem iox_refillBudgetCheck' (usage : Ticks) : IOX (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_refillBudgetCheck' _)

theorem iox_maybeAddEmptyTail' (scPtr : ObjRef) : IOX (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_maybeAddEmptyTail' _)

theorem iox_maybeDonateSc' (tcbPtr ntfnPtr : ObjRef) : IOX (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_maybeDonateSc' _ _)

theorem iox_updateWaitingNtfn' (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : IOX (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_updateWaitingNtfn' _ _ _)

theorem iox_handleTimeout' (tptr : ObjRef) (ex : Fault) : IOX (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_handleTimeout' _ _)

theorem iox_getMrs' (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : IOX (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getMrs' _ _ _)

theorem iox_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    IOX (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_handleFaultReply' _ _ _ _)

theorem iox_returnConsumed' (scPtr : ObjRef) : IOX (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_returnConsumed' _)

theorem iox_schedContextBindNtfn' (sc ntfn : ObjRef) : IOX (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedContextBindNtfn' _ _)

theorem iox_schedContextYieldTo' (scPtr : ObjRef) : IOX (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedContextYieldTo' _)

theorem iox_getScActive' (scPtr : ObjRef) : IOX (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getScActive' _)

theorem iox_commitTime' : IOX (commitTime (Z := Unit) ) := by
  unfold commitTime; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_commitTime' )

theorem iox_refillNew' (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : IOX (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_refillNew' _ _ _ _)

theorem iox_refillUpdate' (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : IOX (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_refillUpdate' _ _ _ _)

theorem iox_archInvokeIrqHandler' (i : IrqHandlerInvocation) : IOX (archInvokeIrqHandler (Z := Unit) i) := by
  cases i <;> unfold archInvokeIrqHandler <;> iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_archInvokeIrqHandler' _)

theorem iox_sendSignal' (n : ObjRef) (b : Badge) : IOX (sendSignal (Z := Unit) n b) := by
  unfold sendSignal; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_sendSignal' _ _)

theorem iox_doReplyTransfer' (s r : ObjRef) (g : Bool) : IOX (doReplyTransfer (Z := Unit) s r g) := by
  unfold doReplyTransfer; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_doReplyTransfer' _ _ _)

theorem iox_invokeSchedContext' (i : SchedContextInvocation) : IOX (invokeSchedContext (Z := Unit) i) := by
  cases i <;> unfold invokeSchedContext <;> iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_invokeSchedContext' _)

theorem iox_invokeSchedControlConfigureFlags' (i : SchedControlInvocation) : IOX (invokeSchedControlConfigureFlags (Z := Unit) i) := by
  cases i <;> unfold invokeSchedControlConfigureFlags <;> iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_invokeSchedControlConfigureFlags' _)

theorem iox_invokeIrqHandler' (i : IrqHandlerInvocation) : IOX (invokeIrqHandler (Z := Unit) i) := by
  cases i <;> unfold invokeIrqHandler <;> iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_invokeIrqHandler' _)

theorem iox_lookupSourceSlot' (c : Cap) (r : CapRef) (n : Nat) : IOXE (lookupSourceSlot (Z := Unit) c r n) := by
  unfold lookupSourceSlot; exact iox_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_lookupSourceSlot' _ _ _)

theorem ioxe_ensureEmpty' (sl : CslotPtr) : IOXE (ensureEmpty (Z := Unit) sl) := by
  unfold ensureEmpty; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_ensureEmpty' _)

theorem ioxe_checkVpAlignment' (sz : VMPageSize) (v : Word) : IOXE (checkVpAlignment (Z := Unit) sz v) := by
  unfold checkVpAlignment; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_checkVpAlignment' _ _)

theorem ioxe_createMappingEntries' (base : Paddr) (vptr : VSpaceRef) (sz : VMPageSize) (r : VMRights)
    (at' : VMAttributes) (p : ObjRef) : IOXE (createMappingEntries (Z := Unit) base vptr sz r at' p) := by
  cases sz <;> unfold createMappingEntries <;> iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_createMappingEntries' _ _ _ _ _ _)

theorem ioxe_ensureSafeMapping' (e : VMPageEntry × ObjRef) : IOXE (ensureSafeMapping (Z := Unit) e) := by
  unfold ensureSafeMapping; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_ensureSafeMapping' _)

theorem ioxe_decodePageInvocation' (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) : IOXE (decodePageInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageInvocation; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_decodePageInvocation' _ _ _ _ _)

theorem ioxe_fbMap (b : Fl4FrameBatchInvocation) (sl : CslotPtr) (v : Data) : IOXE (fbMap (Z := Unit) b sl v) := by
  unfold fbMap; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_fbMap _ _ _)

theorem iox_unmapPageUnflushed (sz : VMPageSize) (vs : ObjRef) (v : VSpaceRef) (p : ObjRef) :
    IOX (unmapPageUnflushed (Z := Unit) sz vs v p) := by
  unfold unmapPageUnflushed; iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_unmapPageUnflushed _ _ _ _)

theorem ioxe_fbCode {α : Type} {m : SEMonad Unit α} (h : IOXE m) : IOXE (fbCode (Z := Unit) m) := by
  unfold fbCode; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible refine ioxe_fbCode ?_)

theorem ioxe_fbDelete (sl : CslotPtr) : IOXE (fbDelete (Z := Unit) sl) := by
  unfold fbDelete; exact dke_handleE (iox_capDelete sl) fun _ => dke_throw _
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_fbDelete _)

/-- fb3: one `X86PML4FrameBatch` entry. -/
theorem iox_fbEntry (b : Fl4FrameBatchInvocation) (w : Data × Data × Data) : IOXE (fbEntry (Z := Unit) b w) := by
  unfold fbEntry; iox_auto0

/-- fb3: the batch (SpecInvFbD's `fk_performFrameBatch`). -/
theorem iox_performFrameBatch (b : Fl4FrameBatchInvocation) : IOX (performFrameBatch (Z := Unit) b) :=
  fk_performFrameBatch (fun w => iox_fbEntry b w) (iox_flushAll _ _)
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_performFrameBatch _)

/-- **The arch invocations keep the domain list** (moved to the end for the batch's leaves). -/
theorem ioxe_fl4ArchPerformInvocation (i : Fl4ArchInvocation) : IOXE (fl4ArchPerformInvocation (Z := Unit) i) := by
  cases i with
  | frameBatch b => unfold fl4ArchPerformInvocation; exact dke_liftE (iox_performFrameBatch b)
  | spec i => exact ioxe_archPerformInvocation i
  | pml4Flush i => unfold fl4ArchPerformInvocation; apply dke_liftE; iox_auto0; exact iox_performPml4Flush i
  | deriveSubframe i => unfold fl4ArchPerformInvocation; apply dke_liftE; iox_auto0
  | testAndClearAccessed slot => unfold fl4ArchPerformInvocation; apply dke_liftE; iox_auto0
  | tdx i => unfold fl4ArchPerformInvocation; apply dke_liftE; cases i <;> unfold performTdxInvocation tdxStatus <;> iox_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_fl4ArchPerformInvocation _)

end

end Fl4Proofs.P3.SInvIox
