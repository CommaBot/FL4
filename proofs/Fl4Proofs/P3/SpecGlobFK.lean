/-
P3 (DESIGN.md §9), CSpace: **the spec's deletion steps keep the IRQ node
and the idle thread** (`GK := FK gloF`, VsDom's `FK`), spec side only. The
leaves are DomRecDel's and VsDomOps' `DK` lemmas for the projection
`gloF` (`interrupt_irq_node`, `idle_thread`), proved the same way (VsDom's
combinators are generic in the projection): `gk_finaliseCap`,
`gk_emptySlot'`, `gk_capSwapForDelete'`, `gke_preemptionPoint'`, `gk_setCap`.
For SpecGlob (the spec-only invariants carried by the deletion loop).
-/
import Fl4Proofs.P3.DomRecDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open Fl4Spec Classical

noncomputable section

/-- The fields the deletion keeps for `SpecGlob`: the IRQ node and the idle
thread. -/
def gloF (σ : State Unit) : (Irq → ObjRef) × ObjRef := (σ.interruptIrqNode, σ.idleThread)

/-- Every outcome of `m` keeps the IRQ node and the idle thread. -/
abbrev GK {α : Type} (m : NonDet (State Unit) α) : Prop := FK gloF m

/-- `GK` for the exception monad. -/
abbrev GKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := FKE gloF m

/-- A `GK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "gk_leaf" : tactic
macro_rules | `(tactic| gk_leaf) => `(tactic| fail "no gk_leaf")

macro "gk_auto" : tactic => `(tactic| repeat' (first | gk_leaf | dk_step0))

theorem gk_doMachineOp {α : Type} (mop : NonDet MachineState α) : GK (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_doMachineOp _)

theorem gk_doExtendedOp (eop : DetExtMonad Unit) : GK (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_doExtendedOp _)

/-- The kernel heap (for the steps writing no object). -/
abbrev KhK {α : Type} (m : NonDet (State Unit) α) : Prop := FK (fun σ : State Unit => σ.kheap) m

theorem kh_doMachineOp {α : Type} (mop : NonDet MachineState α) : KhK (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)

theorem kh_doExtendedOp (eop : DetExtMonad Unit) : KhK (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)

/-- `KhK` by the combinators. -/
macro "kh_auto" : tactic =>
  `(tactic| repeat' (first | with_reducible exact kh_doMachineOp _ | with_reducible exact kh_doExtendedOp _ | dk_step0))

theorem gke_pure_run {ε α : Type} (a : α) : GK (ExceptT.run (pure a : NonDetE (State Unit) ε α)) := dk_pure _

theorem gk_setObject (p : ObjRef) (o : KernelObject) : GK (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setObject _ _)

theorem gk_setCap (c : Cap) (sl : CslotPtr) : GK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setCap _ _)

theorem gk_getCap (sl : CslotPtr) : GK (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getCap _)

theorem gk_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    GK (portOut (Z := Unit) f w) := by
  unfold portOut; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_portOut _ _)

theorem gk_getPt (ptr : ObjRef) : GK (getPt (Z := Unit) ptr) := by
  unfold getPt; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getPt _)

theorem gk_getPte (ptr : ObjRef) : GK (getPte (Z := Unit) ptr) := by
  unfold getPte; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getPte _)

theorem gk_getPd (ptr : ObjRef) : GK (getPd (Z := Unit) ptr) := by
  unfold getPd; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getPd _)

theorem gk_getPde (ptr : ObjRef) : GK (getPde (Z := Unit) ptr) := by
  unfold getPde; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getPde _)

theorem gk_getPml4 (ptr : ObjRef) : GK (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getPml4 _)

theorem gk_getPml4e (ptr : ObjRef) : GK (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getPml4e _)

theorem gk_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : GKE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_lookupPdptSlot _ _)

theorem gk_getPdpt (ptr : ObjRef) : GK (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getPdpt _)

theorem gk_getPdpte (ptr : ObjRef) : GK (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getPdpte _)

theorem gk_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : GKE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_lookupPdSlot _ _)

theorem gk_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : GKE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_lookupPtSlot _ _)

theorem gk_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : GK (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setPdpt _ _)

theorem gk_storePdpte (p : ObjRef) (pte : PDPTE) : GK (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_storePdpte _ _)

theorem gk_getAsidPool (ptr : ObjRef) : GK (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getAsidPool _)

theorem gk_findVspaceForAsid (asid : Asid) : GKE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_findVspaceForAsid _)

theorem gk_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : GK (setPt (Z := Unit) ptr pt) := by
  unfold setPt; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setPt _ _)

theorem gk_storePte (p : ObjRef) (pte : PTE) : GK (storePte (Z := Unit) p pte) := by
  unfold storePte; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_storePte _ _)

theorem gk_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : GK (setPd (Z := Unit) ptr pd) := by
  unfold setPd; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setPd _ _)

theorem gk_storePde (p : ObjRef) (pde : PDE) : GK (storePde (Z := Unit) p pde) := by
  unfold storePde; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_storePde _ _)

theorem gk_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : GK (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_unmapPage _ _ _ _)

theorem gk_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : GK (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_performPageInvocationUnmap _ _)

theorem gk_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : GK (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setAsidPool _ _)

theorem gk_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : GK (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_flushTable _ _ _ _)

theorem gk_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : GK (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setPml4 _ _)

theorem gk_setOriginal (slot : CslotPtr) (v : Bool) : GK (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setOriginal _ _)

theorem gk_updateCdt (f : Cdt → Cdt) : GK (updateCdt (Z := Unit) f) := by
  unfold updateCdt; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_updateCdt _)

theorem gk_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : GK (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setUntypedCapAsFull _ _ _)

theorem gk_retypeRegion (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : GK (retypeRegion (Z := Unit) ptr numObjects oBits type dev) := by
  unfold retypeRegion; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_retypeRegion _ _ _ _ _)

theorem gk_storePml4e (p : ObjRef) (pte : PML4E) : GK (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_storePml4e _ _)

theorem gk_flushAll (vspace : ObjRef) (asid : Asid) : GK (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_flushAll _ _)

theorem gk_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : GK (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_unmapPdpt _ _ _)

theorem gk_setIoportMask (f l : IoPort) (val : Bool) : GK (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setIoportMask _ _ _)

theorem gk_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : GK (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_invalidatePageStructureCacheAsid _ _)

theorem gk_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : GK (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_unmapPd _ _ _)

theorem gk_deleteObjects (ptr : Word) (bits : Nat) : GK (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_deleteObjects _ _)

theorem gk_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : GK (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_capInsert _ _ _)

theorem gk_portIn (f : MachineMonad Data) : GK (portIn (Z := Unit) f) := by
  unfold portIn; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_portIn _)

theorem gk_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : GK (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_unmapPageTable _ _ _)

theorem gk_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : GK (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_storeAsidPoolEntry _ _ _)

theorem gk_performPageInvocation (iv : PageInvocation) : GK (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_performPageInvocation _)

theorem gk_performPageTableInvocation (iv : PageTableInvocation) : GK (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_performPageTableInvocation _)

theorem gk_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : GK (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_performPageDirectoryInvocation _)

theorem gk_performPdptInvocation (iv : PdptInvocation) : GK (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_performPdptInvocation _)

theorem gk_performAsidPoolInvocation (iv : AsidPoolInvocation) : GK (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_performAsidPoolInvocation _)

theorem gk_performAsidControlInvocation (iv : AsidControlInvocation) : GK (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_performAsidControlInvocation _)

theorem gk_performIoPortInvocation (i : IoPortInvocation) : GK (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_performIoPortInvocation _)

theorem gk_performIoportControlInvocation (i : IoPortControlInvocation) : GK (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_performIoportControlInvocation _)

theorem gk_performDeriveSubframe (iv : Fl4SubframeInvocation) : GK (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_performDeriveSubframe _)

theorem gk_performTestAndClearAccessed (_slot : ObjRef) : GK (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_performTestAndClearAccessed _)


theorem gk_performPml4Flush (i : Fl4Pml4Invocation) : GK (performPml4Flush (Z := Unit) i) := by
  cases i; unfold performPml4Flush; exact gk_flushAll _ _

theorem gke_archPerformInvocation (i : ArchInvocation) : GKE (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; apply dke_liftE; cases i <;> gk_auto

/-- **The arch invocations keep the domain schedule.** -/
theorem gke_fl4ArchPerformInvocation (i : Fl4ArchInvocation) : GKE (fl4ArchPerformInvocation (Z := Unit) i) := by
  cases i with
  | spec i => exact gke_archPerformInvocation i
  | pml4Flush i => unfold fl4ArchPerformInvocation; apply dke_liftE; gk_auto; exact gk_performPml4Flush i
  | deriveSubframe i => unfold fl4ArchPerformInvocation; apply dke_liftE; gk_auto
  | testAndClearAccessed slot => unfold fl4ArchPerformInvocation; apply dke_liftE; gk_auto


/-! ## `DK`: `suspend` keeps the domain schedule -/


theorem gk_threadSet' (f : Tcb → Tcb) (t : ObjRef) : GK (threadSet (Z := Unit) f t) := by
  unfold threadSet; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_threadSet' _ _)

theorem gk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : GK (threadGet (Z := Unit) f t) := by
  unfold threadGet; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_threadGet' _ _)

theorem gk_setThreadState' (t : ObjRef) (ts : ThreadState) : GK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setThreadState' _ _)

theorem gk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    GK (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getSimpleKo' _ _)

theorem gk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    GK (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setSimpleKo' _ _ _)

theorem gk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    GK (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_updateSkObjRef' _ _ _ _)

theorem gk_getSchedContext' (q : ObjRef) : GK (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getSchedContext' _)

theorem gk_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    GK (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_updateSchedContext' _ _)

theorem gk_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : GK (asUser (Z := Unit) t u) := by
  unfold asUser; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_asUser' _ _)

theorem gk_replyUnlinkTcb' (t r : ObjRef) : GK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_replyUnlinkTcb' _ _)

theorem gk_getThreadState' (t : ObjRef) : GK (getThreadState (Z := Unit) t) := by
  unfold getThreadState; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getThreadState' _)

theorem gk_cancelIpc' (t : ObjRef) : GK (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_cancelIpc' _)

theorem gk_suspend' (t : ObjRef) : GK (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc tcbSchedAction getTcbQueue setTcbQueue tcbReleaseRemove
    schedContextCancelYieldTo getTcbObjRef getThreadState
  gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_suspend' _)


theorem gk_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : GK (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getSkObjRef' _ _ _)

theorem gk_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : GK (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getScObjRef' _ _)

theorem gk_getIrqSlot' (irq : Irq) : GK (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getIrqSlot' _)

theorem gk_isFinalCap' (c : Cap) : GK (isFinalCap (Z := Unit) c) := by
  unfold isFinalCap; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_isFinalCap' _)

theorem gk_hwAsidInvalidate' (a : Asid) (v : ObjRef) : GK (hwAsidInvalidate (Z := Unit) a v) := by
  unfold hwAsidInvalidate; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_hwAsidInvalidate' _ _)

theorem gk_getCurrentCr3' : GK (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getCurrentCr3' )

theorem gk_setCurrentCr3' (c : Cr3) : GK (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setCurrentCr3' _)

theorem gk_setCurrentVspaceRoot' (v : ObjRef) (a : Asid) : GK (setCurrentVspaceRoot (Z := Unit) v a) := by
  unfold setCurrentVspaceRoot; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setCurrentVspaceRoot' _ _)

theorem gk_setVmRoot' (t : ObjRef) : GK (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setVmRoot' _)

theorem gk_freeIoportRange' (f l : IoPort) : GK (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_freeIoportRange' _ _)

theorem gk_setIrqState' (i : IrqState) (irq : Irq) : GK (setIrqState (Z := Unit) i irq) := by
  unfold setIrqState; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setIrqState' _ _)

theorem gk_deletedIrqHandler' (irq : Irq) : GK (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_deletedIrqHandler' _)

theorem gk_lookupIpcBuffer' (b : Bool) (t : ObjRef) : GK (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_lookupIpcBuffer' _ _)

theorem gk_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, GK (g a b)) :
    ∀ l1 l2, GK (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => dk_bind (h a b) (fun _ => gk_zipWithMx' h l1 l2)
  | [], _ => dk_pure' _
  | _ :: _, [] => dk_pure' _
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible refine gk_zipWithMx' (fun _ _ => ?_) _ _)

theorem gk_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : GK (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_storeWordOffs' _ _ _)

theorem gk_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : GK (setMrs (Z := Unit) t b m) := by
  unfold setMrs; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setMrs' _ _ _)

theorem gk_setMessageInfo' (t : ObjRef) (i : MessageInfo) : GK (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setMessageInfo' _ _)

theorem gk_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : GK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_archThreadSet' _ _)

theorem gk_saveFpuState' (t : ObjRef) : GK (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_saveFpuState' _)

theorem gk_loadFpuState' (t : ObjRef) : GK (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_loadFpuState' _)

theorem gk_setX64CurrentFpuOwner' (o : Option ObjRef) : GK (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setX64CurrentFpuOwner' _)

theorem gk_switchLocalFpuOwner' (o : Option ObjRef) : GK (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_switchLocalFpuOwner' _)

theorem gk_getTcbQueue' (d : Domain) (p : Priority) : GK (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getTcbQueue' _ _)

theorem gk_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : GK (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setTcbQueue' _ _ _)

theorem gk_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : GK (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_tcbSchedAction' _ _)

theorem gk_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : GK (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getTcbObjRef' _ _)

theorem gk_setSchedulerAction' (a : SchedulerAction) : GK (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setSchedulerAction' _)

theorem gk_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : GK (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getScRefillSufficient' _ _)

theorem gk_getScRefillReady' (sc : ObjRef) : GK (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getScRefillReady' _)

theorem gk_tcbReleaseRemove' (t : ObjRef) : GK (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_tcbReleaseRemove' _)

theorem gk_rescheduleRequired' : GK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_rescheduleRequired' )

theorem gk_testReschedule' (t : ObjRef) : GK (testReschedule (Z := Unit) t) := by
  unfold testReschedule; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_testReschedule' _)

theorem gk_possibleSwitchTo' (t : ObjRef) : GK (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_possibleSwitchTo' _)

theorem gk_tcbEpDequeue' (t e : ObjRef) : GK (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_tcbEpDequeue' _ _)

theorem gk_tcbNtfnDequeue' (t n : ObjRef) : GK (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_tcbNtfnDequeue' _ _)

theorem gk_isRoundRobin' (sc : ObjRef) : GK (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_isRoundRobin' _)

theorem gk_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : GK (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_updateRefillHd' _ _)

theorem gk_getRefillHead' (sc : ObjRef) : GK (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_getRefillHead' _)

theorem gk_refillPopHead' (sc : ObjRef) : GK (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_refillPopHead' _)

theorem gk_mergeOverlappingRefills' (sc : ObjRef) : GK (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_mergeOverlappingRefills' _)

theorem gk_refillHeadOverlappingLoop' (sc : ObjRef) : GK (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_refillHeadOverlappingLoop' _)

theorem gk_refillUnblockCheck' (sc : ObjRef) : GK (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_refillUnblockCheck' _)

theorem gk_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : GK (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_ifCondRefillUnblockCheck' _ _ _)

theorem gk_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) : GK (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem gk_restartThreadIfNoFault' (t : ObjRef) : GK (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_restartThreadIfNoFault' _)

theorem gk_removeAndRestartEpQueuedThread' (t e : ObjRef) : GK (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_removeAndRestartEpQueuedThread' _ _)

theorem gk_removeAndRestartNtfnQueuedThread' (t n : ObjRef) : GK (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_removeAndRestartNtfnQueuedThread' _ _)

theorem gk_replyUnlinkSc' (sc r : ObjRef) : GK (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_replyUnlinkSc' _ _)

theorem gk_schedContextDonate' (sc t : ObjRef) : GK (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_schedContextDonate' _ _)

theorem gk_schedContextUpdateConsumed' (sc : ObjRef) : GK (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_schedContextUpdateConsumed' _)

theorem gk_replyFromKernel' (t : ObjRef) (x : Data × List Data) : GK (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_replyFromKernel' _ _)

theorem gk_setConsumed' (sc t : ObjRef) : GK (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_setConsumed' _ _)

theorem gk_schedContextCancelYieldTo' (t : ObjRef) : GK (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_schedContextCancelYieldTo' _)

theorem gk_fpuRelease' (t : ObjRef) : GK (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_fpuRelease' _)

theorem gk_deleteAsidPool' (b : Asid) (p : ObjRef) : GK (deleteAsidPool (Z := Unit) b p) := by
  unfold deleteAsidPool; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_deleteAsidPool' _ _)

theorem gk_deleteAsid' (a : Asid) (p : ObjRef) : GK (deleteAsid (Z := Unit) a p) := by
  unfold deleteAsid; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_deleteAsid' _ _)

theorem gk_archPostCapDeletion' (c : ArchCap) : GK (archPostCapDeletion (Z := Unit) c) := by
  unfold archPostCapDeletion; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_archPostCapDeletion' _)

theorem gk_postCapDeletion' (c : Cap) : GK (postCapDeletion (Z := Unit) c) := by
  unfold postCapDeletion; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_postCapDeletion' _)

theorem gk_emptySlot' (sl : CslotPtr) (c : Cap) : GK (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_emptySlot' _ _)

theorem gk_cancelAllIpc' (e : ObjRef) : GK (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_cancelAllIpc' _)

theorem gk_schedContextMaybeUnbindNtfn' (n : ObjRef) : GK (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_schedContextMaybeUnbindNtfn' _)

theorem gk_unbindMaybeNotification' (n : ObjRef) : GK (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_unbindMaybeNotification' _)

theorem gk_cancelAllSignals' (n : ObjRef) : GK (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_cancelAllSignals' _)

theorem gk_replyRemove' (t r : ObjRef) : GK (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_replyRemove' _ _)

theorem gk_unbindNotification' (t : ObjRef) : GK (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_unbindNotification' _)

theorem gk_schedContextUnbindTcb' (sc : ObjRef) : GK (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_schedContextUnbindTcb' _)

theorem gk_completeYieldTo' (t : ObjRef) : GK (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_completeYieldTo' _)

theorem gk_unbindFromSc' (t : ObjRef) : GK (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_unbindFromSc' _)

theorem gk_schedContextUnbindAllTcbs' (sc : ObjRef) : GK (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_schedContextUnbindAllTcbs' _)

theorem gk_schedContextUnbindNtfn' (sc : ObjRef) : GK (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_schedContextUnbindNtfn' _)

theorem gk_schedContextUnbindReply' (sc : ObjRef) : GK (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_schedContextUnbindReply' _)

theorem gk_schedContextUnbindYieldFrom' (sc : ObjRef) : GK (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_schedContextUnbindYieldFrom' _)

theorem gk_schedContextSetInactive' (sc : ObjRef) : GK (schedContextSetInactive (Z := Unit) sc) := by
  unfold schedContextSetInactive; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_schedContextSetInactive' _)

theorem gk_prepareThreadDelete' (t : ObjRef) : GK (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_prepareThreadDelete' _)

theorem gk_archFinaliseCap' (c : ArchCap) (x : Bool) : GK (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_archFinaliseCap' _ _)

theorem gk_fastFinalise' (c : Cap) (b : Bool) : GK (fastFinalise (Z := Unit) c b) := by
  unfold fastFinalise; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_fastFinalise' _ _)

theorem gk_capDeleteOne' (sl : CslotPtr) : GK (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_capDeleteOne' _)

theorem gk_deletingIrqHandler' (irq : Irq) : GK (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_deletingIrqHandler' _)

/-! ## `finalise_cap` -/

theorem gk_finaliseCap (c : Cap) (b : Bool) : GK (finaliseCap (Z := Unit) c b) := by
  cases c <;> unfold finaliseCap <;> gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_finaliseCap _ _)

/-! ## `rec_del` and `cap_delete` -/

theorem gk_capSwap' (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) : GK (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_capSwap' _ _ _ _)

theorem gk_capSwapForDelete' (s1 s2 : CslotPtr) : GK (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_capSwapForDelete' _ _)

theorem gke_preemptionPoint' : GKE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gke_preemptionPoint')

theorem GK.inode {α : Type} {m : NonDet (State Unit) α} (h : GK m) {σ : State Unit} {x : α × State Unit}
    (hx : x ∈ (m σ).1) : x.2.interruptIrqNode = σ.interruptIrqNode := by
  have e := h σ x hx; simp only [gloF, Prod.mk.injEq] at e; exact e.1

theorem GK.idle {α : Type} {m : NonDet (State Unit) α} (h : GK m) {σ : State Unit} {x : α × State Unit}
    (hx : x ∈ (m σ).1) : x.2.idleThread = σ.idleThread := by
  have e := h σ x hx; simp only [gloF, Prod.mk.injEq] at e; exact e.2

end

end Fl4Proofs.P3.Vs
