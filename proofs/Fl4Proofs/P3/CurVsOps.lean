/-
P3 (DESIGN.md §9): **the spec keeps `cur_thread`** (`CTK`), a mechanical copy
of VsDomOps's `DK` (the domain schedule) for `cur_thread`: no step of the
arch invocations, the deletions or `install_tcb_cap` writes it.
-/
import Fl4Proofs.P3.CurVs
open Classical
namespace Fl4Proofs.P3.Vs.CurK
open Fl4Spec
noncomputable section

theorem ctk_getPt (ptr : ObjRef) : CTK (getPt (Z := Unit) ptr) := by
  unfold getPt; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getPt _)

theorem ctk_getPte (ptr : ObjRef) : CTK (getPte (Z := Unit) ptr) := by
  unfold getPte; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getPte _)

theorem ctk_getPd (ptr : ObjRef) : CTK (getPd (Z := Unit) ptr) := by
  unfold getPd; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getPd _)

theorem ctk_getPde (ptr : ObjRef) : CTK (getPde (Z := Unit) ptr) := by
  unfold getPde; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getPde _)

theorem ctk_getPml4 (ptr : ObjRef) : CTK (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getPml4 _)

theorem ctk_getPml4e (ptr : ObjRef) : CTK (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getPml4e _)

theorem ctk_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : CTKE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_lookupPdptSlot _ _)

theorem ctk_getPdpt (ptr : ObjRef) : CTK (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getPdpt _)

theorem ctk_getPdpte (ptr : ObjRef) : CTK (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getPdpte _)

theorem ctk_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : CTKE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_lookupPdSlot _ _)

theorem ctk_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : CTKE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_lookupPtSlot _ _)

theorem ctk_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : CTK (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setPdpt _ _)

theorem ctk_storePdpte (p : ObjRef) (pte : PDPTE) : CTK (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_storePdpte _ _)

theorem ctk_getAsidPool (ptr : ObjRef) : CTK (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getAsidPool _)

theorem ctk_findVspaceForAsid (asid : Asid) : CTKE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_findVspaceForAsid _)

theorem ctk_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : CTK (setPt (Z := Unit) ptr pt) := by
  unfold setPt; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setPt _ _)

theorem ctk_storePte (p : ObjRef) (pte : PTE) : CTK (storePte (Z := Unit) p pte) := by
  unfold storePte; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_storePte _ _)

theorem ctk_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : CTK (setPd (Z := Unit) ptr pd) := by
  unfold setPd; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setPd _ _)

theorem ctk_storePde (p : ObjRef) (pde : PDE) : CTK (storePde (Z := Unit) p pde) := by
  unfold storePde; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_storePde _ _)

theorem ctk_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : CTK (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_unmapPage _ _ _ _)

theorem ctk_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : CTK (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_performPageInvocationUnmap _ _)

theorem ctk_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : CTK (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setAsidPool _ _)

theorem ctk_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : CTK (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_flushTable _ _ _ _)

theorem ctk_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : CTK (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setPml4 _ _)

theorem ctk_setOriginal (slot : CslotPtr) (v : Bool) : CTK (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setOriginal _ _)

theorem ctk_updateCdt (f : Cdt → Cdt) : CTK (updateCdt (Z := Unit) f) := by
  unfold updateCdt; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_updateCdt _)

theorem ctk_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : CTK (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setUntypedCapAsFull _ _ _)

theorem ctk_retypeRegion (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : CTK (retypeRegion (Z := Unit) ptr numObjects oBits type dev) := by
  unfold retypeRegion; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_retypeRegion _ _ _ _ _)

theorem ctk_storePml4e (p : ObjRef) (pte : PML4E) : CTK (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_storePml4e _ _)

theorem ctk_flushAll (vspace : ObjRef) (asid : Asid) : CTK (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_flushAll _ _)

theorem ctk_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : CTK (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_unmapPdpt _ _ _)

theorem ctk_setIoportMask (f l : IoPort) (val : Bool) : CTK (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setIoportMask _ _ _)

theorem ctk_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : CTK (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_invalidatePageStructureCacheAsid _ _)

theorem ctk_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : CTK (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_unmapPd _ _ _)

theorem ctk_deleteObjects (ptr : Word) (bits : Nat) : CTK (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_deleteObjects _ _)

theorem ctk_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : CTK (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_capInsert _ _ _)

theorem ctk_portIn (f : MachineMonad Data) : CTK (portIn (Z := Unit) f) := by
  unfold portIn; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_portIn _)

theorem ctk_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : CTK (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_unmapPageTable _ _ _)

theorem ctk_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : CTK (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_storeAsidPoolEntry _ _ _)

theorem ctk_performPageInvocation (iv : PageInvocation) : CTK (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_performPageInvocation _)

theorem ctk_performPageTableInvocation (iv : PageTableInvocation) : CTK (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_performPageTableInvocation _)

theorem ctk_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : CTK (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_performPageDirectoryInvocation _)

theorem ctk_performPdptInvocation (iv : PdptInvocation) : CTK (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_performPdptInvocation _)

theorem ctk_performAsidPoolInvocation (iv : AsidPoolInvocation) : CTK (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_performAsidPoolInvocation _)

theorem ctk_performAsidControlInvocation (iv : AsidControlInvocation) : CTK (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_performAsidControlInvocation _)

theorem ctk_performIoPortInvocation (i : IoPortInvocation) : CTK (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_performIoPortInvocation _)

theorem ctk_performIoportControlInvocation (i : IoPortControlInvocation) : CTK (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_performIoportControlInvocation _)

theorem ctk_performDeriveSubframe (iv : Fl4SubframeInvocation) : CTK (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_performDeriveSubframe _)

theorem ctk_performTestAndClearAccessed (_slot : ObjRef) : CTK (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_performTestAndClearAccessed _)


theorem ctk_performPml4Flush (i : Fl4Pml4Invocation) : CTK (performPml4Flush (Z := Unit) i) := by
  cases i; unfold performPml4Flush; exact ctk_flushAll _ _

theorem ctke_archPerformInvocation (i : ArchInvocation) : CTKE (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; apply ctke_liftE; cases i <;> ctk_auto

/-- **The arch invocations keep the domain schedule.** -/
theorem ctke_fl4ArchPerformInvocation (i : Fl4ArchInvocation) : CTKE (fl4ArchPerformInvocation (Z := Unit) i) := by
  cases i with
  | spec i => exact ctke_archPerformInvocation i
  | pml4Flush i => unfold fl4ArchPerformInvocation; apply ctke_liftE; ctk_auto; exact ctk_performPml4Flush i
  | deriveSubframe i => unfold fl4ArchPerformInvocation; apply ctke_liftE; ctk_auto
  | testAndClearAccessed slot => unfold fl4ArchPerformInvocation; apply ctke_liftE; ctk_auto

end
end Fl4Proofs.P3.Vs.CurK
