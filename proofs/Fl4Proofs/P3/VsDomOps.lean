/-
P3 (DESIGN.md §9), VSpace: **`DK` for the spec's arch invocations**
(VsDom.lean): every outcome of `fl4ArchPerformInvocation` (the page, table,
ASID, IO port invocations and the l4h PML4 flush, DeriveSubframe and
TestAndClearAccessed) keeps `domain_list` and `domain_start_index`. One
lemma per spec function, bottom-up, by `dk_auto`.
-/
import Fl4Proofs.P3.VsDom
open Classical
namespace Fl4Proofs.P3.Vs
open Fl4Spec
noncomputable section

theorem dk_getPt (ptr : ObjRef) : DK (getPt (Z := Unit) ptr) := by
  unfold getPt; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getPt _)

theorem dk_getPte (ptr : ObjRef) : DK (getPte (Z := Unit) ptr) := by
  unfold getPte; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getPte _)

theorem dk_getPd (ptr : ObjRef) : DK (getPd (Z := Unit) ptr) := by
  unfold getPd; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getPd _)

theorem dk_getPde (ptr : ObjRef) : DK (getPde (Z := Unit) ptr) := by
  unfold getPde; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getPde _)

theorem dk_getPml4 (ptr : ObjRef) : DK (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getPml4 _)

theorem dk_getPml4e (ptr : ObjRef) : DK (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getPml4e _)

theorem dk_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : DKE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_lookupPdptSlot _ _)

theorem dk_getPdpt (ptr : ObjRef) : DK (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getPdpt _)

theorem dk_getPdpte (ptr : ObjRef) : DK (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getPdpte _)

theorem dk_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : DKE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_lookupPdSlot _ _)

theorem dk_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : DKE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_lookupPtSlot _ _)

theorem dk_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : DK (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setPdpt _ _)

theorem dk_storePdpte (p : ObjRef) (pte : PDPTE) : DK (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_storePdpte _ _)

theorem dk_getAsidPool (ptr : ObjRef) : DK (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getAsidPool _)

theorem dk_findVspaceForAsid (asid : Asid) : DKE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_findVspaceForAsid _)

theorem dk_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : DK (setPt (Z := Unit) ptr pt) := by
  unfold setPt; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setPt _ _)

theorem dk_storePte (p : ObjRef) (pte : PTE) : DK (storePte (Z := Unit) p pte) := by
  unfold storePte; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_storePte _ _)

theorem dk_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : DK (setPd (Z := Unit) ptr pd) := by
  unfold setPd; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setPd _ _)

theorem dk_storePde (p : ObjRef) (pde : PDE) : DK (storePde (Z := Unit) p pde) := by
  unfold storePde; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_storePde _ _)

theorem dk_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : DK (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_unmapPage _ _ _ _)

theorem dk_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : DK (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_performPageInvocationUnmap _ _)

theorem dk_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : DK (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setAsidPool _ _)

theorem dk_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : DK (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_flushTable _ _ _ _)

theorem dk_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : DK (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setPml4 _ _)

theorem dk_setOriginal (slot : CslotPtr) (v : Bool) : DK (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setOriginal _ _)

theorem dk_updateCdt (f : Cdt → Cdt) : DK (updateCdt (Z := Unit) f) := by
  unfold updateCdt; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_updateCdt _)

theorem dk_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : DK (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setUntypedCapAsFull _ _ _)

theorem dk_retypeRegion (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : DK (retypeRegion (Z := Unit) ptr numObjects oBits type dev) := by
  unfold retypeRegion; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_retypeRegion _ _ _ _ _)

theorem dk_storePml4e (p : ObjRef) (pte : PML4E) : DK (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_storePml4e _ _)

theorem dk_flushAll (vspace : ObjRef) (asid : Asid) : DK (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_flushAll _ _)

theorem dk_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : DK (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_unmapPdpt _ _ _)

theorem dk_setIoportMask (f l : IoPort) (val : Bool) : DK (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setIoportMask _ _ _)

theorem dk_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : DK (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_invalidatePageStructureCacheAsid _ _)

theorem dk_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : DK (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_unmapPd _ _ _)

theorem dk_deleteObjects (ptr : Word) (bits : Nat) : DK (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_deleteObjects _ _)

theorem dk_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : DK (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_capInsert _ _ _)

theorem dk_portIn (f : MachineMonad Data) : DK (portIn (Z := Unit) f) := by
  unfold portIn; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_portIn _)

theorem dk_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : DK (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_unmapPageTable _ _ _)

theorem dk_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : DK (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_storeAsidPoolEntry _ _ _)

theorem dk_performPageInvocation (iv : PageInvocation) : DK (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_performPageInvocation _)

theorem dk_performPageTableInvocation (iv : PageTableInvocation) : DK (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_performPageTableInvocation _)

theorem dk_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : DK (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_performPageDirectoryInvocation _)

theorem dk_performPdptInvocation (iv : PdptInvocation) : DK (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_performPdptInvocation _)

theorem dk_performAsidPoolInvocation (iv : AsidPoolInvocation) : DK (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_performAsidPoolInvocation _)

theorem dk_performAsidControlInvocation (iv : AsidControlInvocation) : DK (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_performAsidControlInvocation _)

theorem dk_performIoPortInvocation (i : IoPortInvocation) : DK (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_performIoPortInvocation _)

theorem dk_performIoportControlInvocation (i : IoPortControlInvocation) : DK (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_performIoportControlInvocation _)

theorem dk_performDeriveSubframe (iv : Fl4SubframeInvocation) : DK (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_performDeriveSubframe _)

theorem dk_performTestAndClearAccessed (_slot : ObjRef) : DK (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_performTestAndClearAccessed _)


theorem dk_performPml4Flush (i : Fl4Pml4Invocation) : DK (performPml4Flush (Z := Unit) i) := by
  cases i; unfold performPml4Flush; exact dk_flushAll _ _

theorem dke_archPerformInvocation (i : ArchInvocation) : DKE (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; apply dke_liftE; cases i <;> dk_auto

/-- **The arch invocations keep the domain schedule.** -/
theorem dke_fl4ArchPerformInvocation (i : Fl4ArchInvocation) : DKE (fl4ArchPerformInvocation (Z := Unit) i) := by
  cases i with
  | spec i => exact dke_archPerformInvocation i
  | pml4Flush i => unfold fl4ArchPerformInvocation; apply dke_liftE; dk_auto; exact dk_performPml4Flush i
  | deriveSubframe i => unfold fl4ArchPerformInvocation; apply dke_liftE; dk_auto
  | testAndClearAccessed slot => unfold fl4ArchPerformInvocation; apply dke_liftE; dk_auto
  | tdx i => unfold fl4ArchPerformInvocation; apply dke_liftE; cases i <;> unfold performTdxInvocation tdxStatus <;> dk_auto

end
end Fl4Proofs.P3.Vs
