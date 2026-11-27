/-
# P2 (line p3mc, gen 33): `JAtZ` is false at l4v's dummy initial state `initASt` (any store, arch, ghosts)

The cheapest candidate for `hB`'s P3 boot (handoff §36c / §38a) was a store state related to Fl4Spec's
`initASt` (Fl4Spec/Init: l4v `init_A_st`), since P3 already proves every spec-side start fact there
(`boot_sinvX`, `boot_ioi`, `boot_gpmOut`, `boot_idleVtS`; `SpecUtZ`, `UtPgR`, `DevRangeS` hold vacuously: no untyped
cap). **That candidate is impossible**: `JAtZ` fixes FL4's kernel-state block relative to the spec's IRQ node and
keeps every heap TCB outside the block, and `initASt`'s addresses violate that.

* `IrqRel.node` (in `XTopAt.fin`'s `OthersRel`) at IRQ 0: the spec's `interruptIrqNode 0` is FL4's `nodeA kb 0`,
  i.e. `kb + 1248` (`nodeA_val`). At `initASt` that is `initIrqNodePtr = kernelBase + 0x2000`, so
  `kb = kernelBase + 0x1B20`, and the block is `[kernelBase + 0x1B20, kernelBase + 0x5020)` (13568 bytes).
* `JKern.cur` / `curH` / `hks`: the current thread `curW` is a TCB of `H` (bits 12) with
  `curW + 4096 ≤ kb ∨ kb + 13568 ≤ curW`. At `initASt` the current thread is `idleThreadPtr = kernelBase + 0x1000`,
  whose 4 KiB end at `kernelBase + 0x2000 > kb`.

**`jAtZ_bootLay`** (the general constraint, at every `JAtZ` state), **`jAtZ_false_l4vAddrs`** (any spec state whose
current thread is `idleThreadPtr` and whose IRQ node 0 is `initIrqNodePtr`), **`jAtZ_initASt_false`**,
**`not_start_initASt`** (no `JReachU3.start` premise bundle at `initASt`).

Neither `curThread`'s initial value nor `interruptIrqNode` is a choice of FL4: they are l4v's X64 dummy layout
(`init_irq_node_ptr = kernel_base + 0x2000`, `idle_thread_ptr = kernel_base + 0x1000`) where FL4 puts its
kernel-state block (IRQ states at +224, IRQ node at +1248, 13568 bytes) right before the IRQ node. A second,
independent clash (not proved here): `SpecCover.arch` puts `initGlobalPdpt = kernelBase + 0x5000` (4 KiB) in `H` as
an `.other` object, and `JKern.hksIn` then needs it below, above or inside the block, but it straddles the block's
end `kernelBase + 0x5020`.

Consequence: a P3 store-state boot must use a **relocated** spec boot state (handoff §38b), and every spec boot
lemma P3 proves at `initASt` must be re-proved there. Nothing here is a premise; no existing statement changed except
the root import list.
-/
import Fl4Proofs.P2.BootStore
import Fl4Proofs.P3.XTopJointKEntryU3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
  {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The layout `JAtZ` imposes on the spec's IRQ node and the current thread** (module docstring): IRQ node 0 is
FL4's kernel-state base plus 1248, the current thread is FL4's, and its 4 KiB miss the 13568-byte block. -/
theorem jAtZ_bootLay (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    (σ.interruptIrqNode (BitVec.ofNat 8 0)).toNat = (L.ksb s).val + 1248 ∧
      σ.curThread.toNat = (L.curW s).val ∧
      ((L.curW s).val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ (L.curW s).val) := by
  have hf := J.kern.ksbFit
  have hI : IrqRel (L.mem s) (L.ksb s) σ := J.xtop.fin.1.1.2.2.2.1
  have hn := hI.node 0#u64 (by decide)
  have hv := nodeA_val (kb := L.ksb s) (i := 0#u64) hf (by decide)
  have hk := J.kern.hks _ _ J.kern.curH (fun z h => by cases h)
  simp only [HKind.bits] at hk
  refine ⟨?_, ?_, ?_⟩
  · have e : (σ.interruptIrqNode (BitVec.ofNat 8 0)).toNat = (nodeA (L.ksb s) 0#u64).val := by
      rw [show (BitVec.ofNat 8 0) = BitVec.ofNat 8 (0#u64 : U64).val from rfl, hn]; rfl
    rw [e, hv]; simp
  · rw [J.kern.cur]; rfl
  · have : (2 : Nat) ^ 12 = 4096 := by norm_num
    rw [this] at hk; exact hk

/-- **`JAtZ` is false at l4v's addresses**: no state whose current thread is `idleThreadPtr` and whose IRQ node 0
is `initIrqNodePtr` (module docstring). -/
theorem jAtZ_false_l4vAddrs (hc : σ.curThread = Fl4Spec.idleThreadPtr)
    (hn : σ.interruptIrqNode (BitVec.ofNat 8 0) = Fl4Spec.initIrqNodePtr) :
    ¬ JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ := by
  intro J
  obtain ⟨h1, h2, h3⟩ := jAtZ_bootLay J
  rw [hn] at h1
  rw [hc] at h2
  have e1 : Fl4Spec.initIrqNodePtr.toNat = 18446744071562076160 := by decide
  have e2 : Fl4Spec.idleThreadPtr.toNat = 18446744071562072064 := by decide
  rw [e1] at h1
  rw [e2] at h2
  omega

/-- **`JAtZ` is false at `initASt`**, for every store, arch, arch relation and ghosts. -/
theorem jAtZ_initASt_false : ¬ JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (Fl4Spec.initASt (Z := Unit)) :=
  jAtZ_false_l4vAddrs rfl (by
    show Fl4Spec.initIrqNodePtr + (Fl4Spec.ucast 64 (BitVec.ofNat 8 0) <<< Fl4Spec.cteLevelBits) =
      Fl4Spec.initIrqNodePtr
    decide)

end

/-- **No `JReachU3.start` at `initASt`**: its premise bundle (`JAtZ ∧ VxE ∧ SInvX ∧ SInvIP ∧ MR ∧ UtPgR` at some
ghosts) is false there, for every store and arch. -/
theorem not_start_initASt {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (arI : machine.Arch A)
    (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) :
    ¬ ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (Fl4Spec.initASt (Z := Unit)) := by
  rintro ⟨Z, H, Cs, Ac, Lst, D, J⟩
  exact jAtZ_initASt_false J

end

end Fl4Proofs.P2.BootSt
