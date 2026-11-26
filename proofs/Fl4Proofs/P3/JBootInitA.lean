/-
P3 (line jboot, gen 1): **the spec's dummy initial state `initASt` is not a `JAtZ` state** — for every store,
arch, arch relation and ghosts.

l4v's `init_A_st` (Fl4Spec/Init.lean) places its objects at fixed offsets from `kernelBase`:
the idle TCB at `+0x1000`, the 256 one-slot IRQ CNodes at `+0x2000 + 32 i`, the global PML4 / PDPT / PD at
`+0x4000 / +0x5000 / +0x6000`, the idle SC at `+0x7000`. FL4's relation fixes the kernel-state base from the
IRQ node: `IrqRel.node` at IRQ 0 says the spec's node pointer of IRQ 0 is `ksb + 1248` (`nodeA`), so at
`initASt` the base is forced to `kernelBase + 0x2000 - 1248`. Then:

* **`initASt_not_jAtZ`**: the idle TCB (`kernelBase + 0x1000`, a TCB of the typed heap by `KTyped`) overlaps the
  kernel-state block's first 4 KiB, against `TopPlaced.tko` (TCBs of the typed heap lie apart from
  `[ksb, ksb + 13568)`).
* **`initASt_not_jAtZ_irq128`** (independent of `tko`): the spec's CNode of IRQ 128 (`ksb + 5344`, a CNode of
  the typed heap by `KTyped`) is the first word of FL4's IO-port bitmap, an `OObj` word of the kernel-state
  block, against `TopPlaced.disj` (no `OObj` word is a `VObj` word). FL4 has 128 IRQs, the spec 256.

So the spec-side boot lemmas proved for `initASt` (`boot_sinvX`, `boot_gpmOut`, `boot_idleVtS`, …) cannot feed
`JReachU3.start` as they stand: a P3 start state needs a spec boot state laid out as FL4's kernel-state block
(the IRQ nodes 0..127 at `ksb + 1248 + 32 i`, the idle TCB, the IRQ nodes 128..255 and the global paging
structures outside the block and the per-core nodes), with `SInvX` re-proved for it (handoff jboot.md).

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JointAt
import Fl4Proofs.P3.SpecInvSbE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs

noncomputable section

/-- `initASt`'s IRQ-0 node pointer: `kernelBase + 0x2000`. -/
theorem initASt_irqNode0 :
    ((Fl4Spec.initASt (Z := Unit)).interruptIrqNode (BitVec.ofNat 8 (0#u64 : U64).val)).toNat =
      18446744071562076160 := by decide

/-- `initASt`'s idle thread pointer: `kernelBase + 0x1000`. -/
theorem initASt_idle_val : (⟨Fl4Spec.idleThreadPtr⟩ : U64).val = 18446744071562072064 := by decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- At `initASt`, `IrqRel` forces the kernel-state base to `kernelBase + 0x2000 - 1248`. -/
theorem initASt_ksb {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (Fl4Spec.initASt (Z := Unit))) :
    (L.ksb s).val + 1248 = 18446744071562076160 := by
  have hI : IrqRel (L.mem s) (L.ksb s) (Fl4Spec.initASt (Z := Unit)) := J.xtop.fin.1.1.2.2.2.1
  have hf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := J.kern.ksbFit
  have h0 := hI.node 0#u64 (by decide)
  have hv := nodeA_val hf (i := 0#u64) (by decide)
  have e : (nodeA (L.ksb s) 0#u64).val = 18446744071562076160 := by
    have h1 := congrArg BitVec.toNat h0
    rw [initASt_irqNode0] at h1
    exact h1.symm
  have z : (0#u64 : U64).val = 0 := rfl
  omega

/-- **`initASt` is not a `JAtZ` state** (module docstring): its idle TCB overlaps the kernel-state block. -/
theorem initASt_not_jAtZ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} :
    ¬ JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (Fl4Spec.initASt (Z := Unit)) := by
  intro J
  have hk := initASt_ksb arI J
  have hK : KTyped Z.th (Fl4Spec.initASt (Z := Unit)) := J.xtop.rel.2.2.1.kt
  obtain ⟨x, hx, -⟩ := SInvB.initKheap_idleThread
  have ht : Z.th ⟨Fl4Spec.idleThreadPtr⟩ = some .tcb := (hK _).2 x hx
  have h := J.xtop.fin.1.2.tko _ ht
  rw [initASt_idle_val] at h
  omega

/-- The spec's CNode of IRQ 128 in `initKheap`: `kernelBase + 0x3000`. -/
theorem initKheap_irq128 :
    Fl4Spec.initKheap (18446744071562080256#64) = some (.cnode 0 (Fl4Spec.emptyCnode 0)) := by
  unfold Fl4Spec.initKheap
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  exact if_pos ⟨128#8, by decide⟩

theorem emptyCnode0_wf : Fl4Spec.wellFormedCnodeN 0 (Fl4Spec.emptyCnode 0) := by
  unfold Fl4Spec.wellFormedCnodeN Fl4Spec.dom Fl4Spec.emptyCnode
  ext x
  simp only [Set.mem_setOf_eq]
  by_cases h : x.length = 0 <;> simp [h]

/-- **`initASt` is not a `JAtZ` state, by the IRQ node** (module docstring): the spec's CNode of IRQ 128 is the
first word of FL4's IO-port bitmap. -/
theorem initASt_not_jAtZ_irq128 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} :
    ¬ JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (Fl4Spec.initASt (Z := Unit)) := by
  intro J
  have hk := initASt_ksb arI J
  have hK : KTyped Z.th (Fl4Spec.initASt (Z := Unit)) := J.xtop.rel.2.2.1.kt
  have ht : Z.th ⟨18446744071562080256#64⟩ = some (.cnode 0) :=
    (hK _).1 0 _ initKheap_irq128 emptyCnode0_wf
  have hv : (⟨18446744071562080256#64⟩ : U64).val = 18446744071562080256 := by decide
  refine J.xtop.fin.1.2.disj ⟨18446744071562080256#64⟩ ?_ ?_
  · refine Or.inr (Or.inl ⟨?_, ?_, Or.inr ?_⟩) <;> rw [hv] <;> omega
  · exact Or.inl ⟨_, 0, ht, le_refl _, by rw [hv]; norm_num⟩

end

end

end Fl4Proofs.P3
