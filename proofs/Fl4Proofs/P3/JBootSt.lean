/-
P3 (line jboot, gen 1): **a candidate spec boot state laid out for FL4, `fInitASt`** (the plan's σ0).

`initASt` is not a `JAtZ` state (JBootInitA): with the kernel-state base forced to `kernelBase + 0x2000 - 1248` by
its IRQ node, its idle TCB overlaps the block and its IRQ CNodes 128..255 lie on the IO-port bitmap.
`fInitASt` is `initASt` with **only the IRQ node moved**: FL4's kernel-state base is `fkb := kernelBase + 0x10000`,
the CNodes of IRQs 0..127 are at FL4's `nodeA fkb i = fkb + 1248 + 32 i`, those of IRQs 128..255 stay where
`initASt` has them (`kernelBase + 0x2000 + 32 i`), every other object (idle TCB, idle SC, global PML4 / PDPT / PD)
and every other field are `initASt`'s.

* **`fInitASt_irqNode`**: `IrqRel.node` at base `fkb` (the IRQ node of `JAtZ.xtop`'s `IrqRel`).
* **`fInit_place`**: every object of `fInitKheap` is an IRQ-node CNode of IRQ `< 128` at `nodeA fkb i` (inside the
  block's IRQ-node part, which `OObj` leaves out) or lies wholly below the block (start + 4096 ≤ `fkb`).
  So both `initASt` obstructions vanish: **`fInit_tcb_apart`** (`TopPlaced.tko`'s form for the spec TCBs) and
  **`fInit_cnode_off`** (no spec CNode on an `OObj` word of the block).
* `fkb` meets `IntLayout.fit` / `.align` and `JKern.nodeFit` for one core (`fkb_fit`).

Not yet done (handoff jboot.md): the spec invariants (`SInvX` …) at `fInitASt` (the `initASt` boot lemmas, ported:
`fInitASt` has the same object kinds and contents, only addresses moved) and the concrete memory image.

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootInitA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open Fl4Spec Fl4Proofs.P3

noncomputable section

/-- FL4's kernel-state base in the witness: `kernelBase + 0x10000`. -/
def fkb : U64 := ⟨18446744071562133504#64⟩

theorem fkb_val : fkb.val = 18446744071562133504 := rfl

/-- `fkb` fits the block and one core's node, 32-aligned. -/
theorem fkb_fit : fkb.val + 13568 + (0 + 1) * 4288 ≤ 2 ^ 64 ∧ fkb.val + 13568 ≤ 2 ^ 64 ∧ fkb.val % 32 = 0 := by
  rw [fkb_val]; decide

/-- The IRQ node of the witness: FL4's slots for IRQs 0..127, `initASt`'s for the rest. -/
def fIrqNode (irq : Irq) : ObjRef :=
  if irq.toNat < 128 then fkb.bv + 1248#64 + (ucast 64 irq <<< cteLevelBits)
  else initIrqNodePtr + (ucast 64 irq <<< cteLevelBits)

theorem sh_toNat (irq : Irq) : (ucast 64 irq <<< cteLevelBits).toNat = 32 * irq.toNat := by
  have := irq.isLt
  simp only [Fl4Spec.ucast, Fl4Spec.cteLevelBits, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem fIrqNode_lo {irq : Irq} (h : irq.toNat < 128) :
    (fIrqNode irq).toNat = 18446744071562133504 + 1248 + 32 * irq.toNat := by
  unfold fIrqNode
  rw [if_pos h, BitVec.toNat_add, BitVec.toNat_add, sh_toNat,
    show fkb.bv.toNat = 18446744071562133504 from rfl, show (1248#64 : BitVec 64).toNat = 1248 from rfl]
  simp only [Nat.reducePow, Nat.reduceAdd]
  omega

theorem fIrqNode_hi {irq : Irq} (h : ¬ irq.toNat < 128) :
    (fIrqNode irq).toNat = 18446744071562076160 + 32 * irq.toNat := by
  have := irq.isLt
  unfold fIrqNode
  rw [if_neg h, BitVec.toNat_add, sh_toNat, show initIrqNodePtr.toNat = 18446744071562076160 by decide]
  simp only [Nat.reducePow]
  omega

/-- **`IrqRel.node` at base `fkb`**: the witness's spec IRQ node of IRQ `i < 128` is FL4's slot `nodeA fkb i`. -/
theorem fIrqNode_node (i : U64) (hi : i.val < 128) : fIrqNode (BitVec.ofNat 8 i.val) = (nodeA fkb i).bv := by
  have e : (BitVec.ofNat 8 i.val).toNat = i.val := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [fIrqNode_lo (by rw [e]; exact hi), e]
  have hv := nodeA_val (kb := fkb) (by rw [fkb_val]; decide) hi
  rw [fkb_val] at hv
  exact hv.symm

/-- The witness's heap: `initKheap` with the IRQ CNodes at `fIrqNode`. -/
def fInitKheap : KHeap :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (fun x => if ∃ irq : Irq, fIrqNode irq = x then some (.cnode 0 (emptyCnode 0)) else none)
    idleThreadPtr (initKheap idleThreadPtr))
    idleScPtr (initKheap idleScPtr))
    initGlobalPml4 (initKheap initGlobalPml4))
    initGlobalPdpt (initKheap initGlobalPdpt))
    initGlobalPd (initKheap initGlobalPd)

/-- **The witness's spec boot state** (module docstring). -/
def fInitASt : State Unit :=
  { (initASt (Z := Unit)) with kheap := fInitKheap, interruptIrqNode := fIrqNode }

/-- **`IrqRel.node` at `fInitASt`, base `fkb`.** -/
theorem fInitASt_irqNode (i : U64) (hi : i.val < 128) :
    fInitASt.interruptIrqNode (BitVec.ofNat 8 i.val) = (nodeA fkb i).bv :=
  fIrqNode_node i hi

/-- **The witness's placement** (module docstring). -/
theorem fInit_place {o : ObjRef} {ko : KernelObject} (h : fInitKheap o = some ko) :
    (∃ irq : Irq, irq.toNat < 128 ∧ o = fIrqNode irq ∧ ko = .cnode 0 (emptyCnode 0)) ∨
      o.toNat + 4096 ≤ fkb.val := by
  unfold fInitKheap at h
  simp only [Function.update_apply] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  · right; rw [h1, fkb_val]; decide
  · right; rw [h2, fkb_val]; decide
  · right; rw [h3, fkb_val]; decide
  · right; rw [h4, fkb_val]; decide
  · right; rw [h5, fkb_val]; decide
  · obtain ⟨irq, rfl⟩ := h6
    cases h
    by_cases hl : irq.toNat < 128
    · exact Or.inl ⟨irq, hl, rfl, rfl⟩
    · right; rw [fIrqNode_hi hl, fkb_val]; have := irq.isLt; omega

/-- **The witness's spec TCBs lie below the block** (`TopPlaced.tko`'s first disjunct). -/
theorem fInit_tcb_apart {o : ObjRef} {x : Tcb} (h : fInitKheap o = some (.tcb x)) :
    o.toNat + 4096 ≤ fkb.val := by
  rcases fInit_place h with ⟨_, _, _, e⟩ | h'
  · cases e
  · exact h'

/-- **No spec CNode of the witness on an `OObj` word of the block**: a CNode lies below the block or is the IRQ
slot `nodeA fkb i`, `i < 128`, inside `[fkb + 1248, fkb + 5344)`. -/
theorem fInit_cnode_off {o : ObjRef} {r : Nat} {cs : CnodeContents} (h : fInitKheap o = some (.cnode r cs)) :
    o.toNat + 4096 ≤ fkb.val ∨ (r = 0 ∧ fkb.val + 1248 ≤ o.toNat ∧ o.toNat + 32 ≤ fkb.val + 5344) := by
  rcases fInit_place h with ⟨irq, hl, rfl, e⟩ | h'
  · cases e
    right
    refine ⟨rfl, ?_, ?_⟩ <;> rw [fIrqNode_lo hl, fkb_val] <;> omega
  · exact Or.inl h'

end

end Fl4Proofs.P3.JBoot
