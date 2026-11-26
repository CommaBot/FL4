/- iolay gen 5: YieldBlock frame lemmas, part 1: SpecInvYieldScopeF1's generated lemmas (gen.py `ys` mode, skip list
proofs/scratch/invA/skipYS.txt) for the strengthened invariant, without the functions that reach a blocking writer
(proofs/scratch/invA/skipYB.txt; hand-proved in SpecInvYieldBlockH). -/
import Fl4Proofs.P3.SpecInvYieldBlockT
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {L : List ObjRef}

theorem yb_archActivateIdleThread (_t : ObjRef) : YBK L (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archActivateIdleThread _)

theorem yb_archCheckIrq (_irq : Data) : YBKE L (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archCheckIrq _)

theorem yb_getCap (a0 : CslotPtr) : YBK L (getCap (Z := Unit) a0) := by
  unfold getCap; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getCap _)

theorem yb_ensureEmpty (slot : CslotPtr) : YBKE L (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_ensureEmpty _)

theorem yb_isIoportRangeFree (f l : IoPort) : YBK L (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_isIoportRangeFree _ _)

theorem yb_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : YBKE L m) : YBKE L (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; yb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible refine yb_lookupErrorOnFailure _ _ ?_)

theorem yb_resolveAddressBits' (p : Cap × CapRef) : YBKE L (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by yb_auto)) fun nc => ?_
        split
        · exact yb_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_resolveAddressBits' _)

theorem yb_resolveAddressBits (a0 : Cap × CapRef) : YBKE L (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_resolveAddressBits _)

theorem yb_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : YBKE L (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_lookupSlotForCnodeOp _ _ _ _)

theorem yb_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : YBKE L (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_lookupTargetSlot _ _ _)

theorem yb_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : YBKE L (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeIoportControlInvocation _ _ _ _ _)

theorem yb_getAsidPool (ptr : ObjRef) : YBK L (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getAsidPool _)

theorem yb_findVspaceForAsid (asid : Asid) : YBKE L (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_findVspaceForAsid _)

theorem yb_getPdpt (ptr : ObjRef) : YBK L (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getPdpt _)

theorem yb_getPdpte (ptr : ObjRef) : YBK L (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getPdpte _)

theorem yb_isFinalCap (cap : Cap) : YBK L (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_isFinalCap _)

theorem yb_getPml4 (ptr : ObjRef) : YBK L (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getPml4 _)

theorem yb_getPml4e (ptr : ObjRef) : YBK L (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getPml4e _)

theorem yb_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : YBKE L (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_lookupPdptSlot _ _)

theorem yb_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : YBKE L (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodePageDirectoryInvocation _ _ _ _ _)

theorem yb_checkVpAlignment (sz : VMPageSize) (vptr : Word) : YBKE L (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_checkVpAlignment _ _)

theorem yb_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : YBKE L (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_lookupPdSlot _ _)

theorem yb_getPd (ptr : ObjRef) : YBK L (getPd (Z := Unit) ptr) := by
  unfold getPd; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getPd _)

theorem yb_getPde (ptr : ObjRef) : YBK L (getPde (Z := Unit) ptr) := by
  unfold getPde; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getPde _)

theorem yb_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : YBKE L (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_lookupPtSlot _ _)

theorem yb_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : YBKE L (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_createMappingEntries _ _ _ _ _ _)

theorem yb_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : YBKE L (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_ensureSafeMapping _)

theorem yb_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : YBKE L (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodePageInvocation _ _ _ _ _)

theorem yb_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : YBKE L (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodePageTableInvocation _ _ _ _ _)

theorem yb_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : YBKE L (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodePdptInvocation _ _ _ _ _)

theorem yb_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : YBKE L (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_ensurePortOperationAllowed _ _ _)

theorem yb_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : YBKE L (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodePortInvocation _ _ _)

theorem yb_ensureNoChildren (cslotPtr : CslotPtr) : YBKE L (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_ensureNoChildren _)

theorem yb_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : YBK L (selectExt (Z := Unit) a S) := by
  unfold selectExt; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_selectExt _ _)

theorem yb_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : YBKE L (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archDecodeInvocation _ _ _ _ _ _)

theorem yb_getIrqState (irq : Irq) : YBK L (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getIrqState _)

theorem yb_isIrqActive (irq : Irq) : YBK L (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_isIrqActive _)

theorem yb_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : YBKE L (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archDecodeIrqControlInvocation _ _ _ _)

theorem yb_archDeriveCap (c : ArchCap) : YBKE L (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archDeriveCap _)

theorem yb_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : YBK L (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_hwAsidInvalidate _ _)

theorem yb_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : YBK L (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setAsidPool _ _)

theorem yb_getCurrentCr3  : YBK L (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getCurrentCr3)

theorem yb_setCurrentCr3 (c : Cr3) : YBK L (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setCurrentCr3 _)

theorem yb_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : YBK L (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setCurrentVspaceRoot _ _)

theorem yb_setVmRoot (tcb : ObjRef) : YBK L (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setVmRoot _)

theorem yb_deleteAsid (asid : Asid) (pml4 : ObjRef) : YBK L (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_deleteAsid _ _)

theorem yb_deleteAsidPool (base : Asid) (ptr : ObjRef) : YBK L (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_deleteAsidPool _ _)

theorem yb_getPt (ptr : ObjRef) : YBK L (getPt (Z := Unit) ptr) := by
  unfold getPt; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getPt _)

theorem yb_getPte (ptr : ObjRef) : YBK L (getPte (Z := Unit) ptr) := by
  unfold getPte; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getPte _)

theorem yb_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : YBK L (setPd (Z := Unit) ptr pd) := by
  unfold setPd; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setPd _ _)

theorem yb_storePde (p : ObjRef) (pde : PDE) : YBK L (storePde (Z := Unit) p pde) := by
  unfold storePde; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_storePde _ _)

theorem yb_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : YBK L (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setPdpt _ _)

theorem yb_storePdpte (p : ObjRef) (pte : PDPTE) : YBK L (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_storePdpte _ _)

theorem yb_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : YBK L (setPt (Z := Unit) ptr pt) := by
  unfold setPt; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setPt _ _)

theorem yb_storePte (p : ObjRef) (pte : PTE) : YBK L (storePte (Z := Unit) p pte) := by
  unfold storePte; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_storePte _ _)

theorem yb_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : YBK L (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_unmapPage _ _ _ _)

theorem yb_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : YBK L (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_flushTable _ _ _ _)

theorem yb_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : YBK L (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_invalidatePageStructureCacheAsid _ _)

theorem yb_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : YBK L (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_unmapPageTable _ _ _)

theorem yb_flushAll (vspace : ObjRef) (asid : Asid) : YBK L (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_flushAll _ _)

theorem yb_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : YBK L (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_unmapPd _ _ _)

theorem yb_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : YBK L (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setPml4 _ _)

theorem yb_storePml4e (p : ObjRef) (pte : PML4E) : YBK L (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_storePml4e _ _)

theorem yb_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : YBK L (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_unmapPdpt _ _ _)

theorem yb_archFinaliseCap (c : ArchCap) (x : Bool) : YBK L (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archFinaliseCap _ _)

theorem yb_archGetSanitiseRegisterInfo (_t : ObjRef) : YBK L (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archGetSanitiseRegisterInfo _)

theorem yb_setOriginal (slot : CslotPtr) (v : Bool) : YBK L (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setOriginal _ _)

theorem yb_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : YBK L (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setUntypedCapAsFull _ _ _)

theorem yb_setCdt (t : Cdt) : YBK L (setCdt (Z := Unit) t) := by
  unfold setCdt; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setCdt _)

theorem yb_updateCdt (f : Cdt → Cdt) : YBK L (updateCdt (Z := Unit) f) := by
  unfold updateCdt; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_updateCdt _)

theorem yb_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : YBK L (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_capInsert _ _ _)

theorem yb_setIrqState (state : IrqState) (irq : Irq) : YBK L (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setIrqState _ _)

theorem yb_updateIrqState (irq : Irq) (irqState : X64IRQState) : YBK L (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_updateIrqState _ _)

theorem yb_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : YBK L m) : YBKE L (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; yb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible refine yb_withoutPreemption _ ?_)

theorem yb_archInvokeIrqControl (aic : ArchIrqControlInvocation) : YBKE L (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archInvokeIrqControl _)

theorem yb_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : YBK L (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archInvokeIrqHandler _)

theorem yb_archMaskIrqSignal (irq : Irq) : YBK L (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archMaskIrqSignal _)

theorem yb_performAsidControlInvocation (iv : AsidControlInvocation) : YBK L (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_performAsidControlInvocation _)

theorem yb_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : YBK L (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_storeAsidPoolEntry _ _ _)

theorem yb_performAsidPoolInvocation (iv : AsidPoolInvocation) : YBK L (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_performAsidPoolInvocation _)

theorem yb_portIn (f : MachineMonad Data) : YBK L (portIn (Z := Unit) f) := by
  unfold portIn; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_portIn _)

theorem yb_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : YBK L (portOut (Z := Unit) f w) := by
  unfold portOut; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_portOut _ _)

theorem yb_performIoPortInvocation (i : IoPortInvocation) : YBK L (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_performIoPortInvocation _)

theorem yb_setIoportMask (f l : IoPort) (val : Bool) : YBK L (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setIoportMask _ _ _)

theorem yb_performIoportControlInvocation (i : IoPortControlInvocation) : YBK L (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_performIoportControlInvocation _)

theorem yb_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : YBK L (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_performPageDirectoryInvocation _)

theorem yb_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : YBK L (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_performPageInvocationUnmap _ _)

theorem yb_performPageInvocation (iv : PageInvocation) : YBK L (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_performPageInvocation _)

theorem yb_performPageTableInvocation (iv : PageTableInvocation) : YBK L (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_performPageTableInvocation _)

theorem yb_performPdptInvocation (iv : PdptInvocation) : YBK L (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_performPdptInvocation _)

theorem yb_archPerformInvocation (i : ArchInvocation) : YBKE L (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archPerformInvocation _)

theorem yb_freeIoportRange (f l : IoPort) : YBK L (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_freeIoportRange _ _)

theorem yb_archPostCapDeletion (ac : ArchCap) : YBK L (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archPostCapDeletion _)

theorem yb_archPostModifyRegisters (cur t : ObjRef) : YBK L (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archPostModifyRegisters _ _)

theorem yb_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : YBK L (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archPostResetUntyped _ _)

theorem yb_loadFpuState (t : ObjRef) : YBK L (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_loadFpuState _)

theorem yb_saveFpuState (t : ObjRef) : YBK L (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_saveFpuState _)

theorem yb_setX64CurrentFpuOwner (newOwner : Option ObjRef) : YBK L (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setX64CurrentFpuOwner _)

theorem yb_switchLocalFpuOwner (newOwner : Option ObjRef) : YBK L (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_switchLocalFpuOwner _)

theorem yb_fpuRelease (threadPtr : ObjRef) : YBK L (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_fpuRelease _)
end

end Fl4Proofs.P3.SInv
