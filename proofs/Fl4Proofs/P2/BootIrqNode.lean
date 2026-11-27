/-
# P2 (line p3mc, gen 40): FL4's IRQ-node fact (`Fl4Spec/Ext/IrqNode`) at the boot states and in P3's joint relation

`Fl4Spec.IrqNodeFl4` (spec extension, no port edit): IRQs `< 128` have an injective one-slot CNode node, IRQs
`≥ 128` have no IRQ-node CNode. It replaces l4v's 256-entry `valid_irq_node` (handoff §39a). Proved here:

* **`σB_eq_initFl4`**: the boot state `σB` (P2/BootSpec) *is* `Fl4Spec.initAStFl4 irqNodeB` (l4v `init_A_st` with
  the IRQ node at `irqNodeB` and CNodes for FL4's 128 IRQs), by `rfl`; `initAStAt_l4v` (Ext) gives l4v's
  `initASt` as the same construction at l4v's node with 256 IRQs.
* **`σB_irqNodeFl4`** / **`σR_irqNodeFl4`**: `IrqNodeFl4` at both boot starts; `σB_not_l4v` / `σR_not_l4v`:
  l4v's `valid_irq_node` is false there.
* **`jAtZ_irqNodeDom`**: at every `JAtZ` state whose spec IRQ node is contiguous from FL4's `ksb + 1248` (the
  layout `IrqRel.node` forces below 128), the domain half `irqNodeDomFl4` holds, and **`jAtZ_not_validIrqNode`**:
  l4v's `valid_irq_node` is false (from gen 34's `jAtZ_false_cnodeIo`). So the restriction is not a choice made for
  the witness: P3's joint relation forces it.
* Consistency with P3's uses of `interruptIrqNode`: **`irqRel_capTable`** (`IrqRel.node`'s domain `i < 128` is
  `validIrqNodeFl4`'s: FL4's node slot `nodeA kb i` is the spec's CNode), and **`σB_irqCons`** / **`σR_irqCons`**:
  `IrqNodeFl4`, `IrqRel`, `SpecGlobS`, `IdleOutV` and `IrqOutV` at the node hold together at `σB` / `σR`.

No premise. No existing statement changed except the root import list.
-/
import Fl4Spec.Ext.IrqNode
import Fl4Proofs.P2.BootRSInv
import Fl4Proofs.P2.BootRSpecS
import Fl4Proofs.P2.BootRFinF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open Fl4Spec Classical

noncomputable section

/-- **`σB` is FL4's initial state at the relocated node** (`initAStFl4`, Fl4Spec/Ext/IrqNode). -/
theorem σB_eq_initFl4 {Z : Type} [StateExt Z] : (σB (Z := Z)) = initAStFl4 irqNodeB := rfl

/-- An IRQ node address is not an object ending at or below the block. -/
theorem node_ne_low (irq : Irq) {p : ObjRef} (hp : p.toNat + 4096 ≤ kbB.val) :
    irqNodeB + (ucast 64 irq <<< cteLevelBits) ≠ p := by
  intro e
  have h1 := σB_node_val irq
  have h2 : (σB (Z := Unit)).interruptIrqNode irq = p := e
  rw [h2] at h1
  omega

theorem kheapB_irq_some (irq : Irq) (h : irq.toNat < 128) :
    kheapB (irqNodeB + (ucast 64 irq <<< cteLevelBits)) = some (.cnode 0 (emptyCnode 0)) := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := σB_below
  unfold kheapB
  simp only [Function.update_apply]
  rw [if_neg (node_ne_low irq b4), if_neg (node_ne_low irq b3), if_neg (node_ne_low irq b2),
    if_neg (node_ne_low irq b5), if_neg (node_ne_low irq b1), if_pos ⟨irq, h, rfl⟩]

theorem wf_emptyCnode0 : wellFormedCnodeN 0 (emptyCnode 0) := by
  unfold wellFormedCnodeN emptyCnode dom
  ext x; simp

theorem σB_node_inj {i j : Irq} (e : (σB (Z := Unit)).interruptIrqNode i = (σB (Z := Unit)).interruptIrqNode j) :
    i = j := by
  have h := congrArg BitVec.toNat e
  rw [σB_node_val, σB_node_val] at h
  exact BitVec.eq_of_toNat_eq (by omega)

/-- **FL4's IRQ-node fact at `σB`.** -/
theorem σB_irqNodeFl4 : IrqNodeFl4 (σB (Z := Unit)) := by
  refine ⟨⟨fun i j _ _ e => σB_node_inj e, fun irq h => ⟨_, kheapB_irq_some irq h, wf_emptyCnode0⟩⟩, ?_⟩
  intro irq h n ⟨cs, ho, _⟩
  rcases kheapB_cases ho with ⟨-, x, e⟩ | ⟨-, y, m, e⟩ | ⟨-, a, e⟩ | ⟨⟨irq', h', e'⟩, -⟩
  · cases e
  · cases e
  · cases e
  · have e2 : (σB (Z := Unit)).interruptIrqNode irq' = (σB (Z := Unit)).interruptIrqNode irq := e'
    have := σB_node_inj e2
    subst this
    exact absurd h (by unfold fl4IrqCount; omega)

theorem σB_not_l4v : ¬ validIrqNode (σB (Z := Unit)) := σB_irqNodeFl4.not_l4v

theorem node_ne_tRp (irq : Irq) : irqNodeB + (ucast 64 irq <<< cteLevelBits) ≠ tRp :=
  node_ne_low irq (by rw [tRp_toNat, kbB_val]; omega)

theorem node_ne_scRp (irq : Irq) : irqNodeB + (ucast 64 irq <<< cteLevelBits) ≠ scRp :=
  node_ne_low irq (by rw [scRp_toNat, kbB_val]; omega)

/-- **FL4's IRQ-node fact at `σR`** (the root TCB and SC lie below the block). -/
theorem σR_irqNodeFl4 : IrqNodeFl4 (σR (Z := Unit)) := by
  obtain ⟨⟨hi, hc⟩, hd⟩ := σB_irqNodeFl4
  refine ⟨⟨hi, fun irq h => ?_⟩, fun irq h n ⟨cs, ho, hw⟩ => hd irq h n ⟨cs, ?_, hw⟩⟩
  · obtain ⟨cs, ho, hw⟩ := hc irq h
    exact ⟨cs, (kheapR_of_ne (node_ne_tRp irq) (node_ne_scRp irq)).trans ho, hw⟩
  · exact (kheapR_of_ne (node_ne_tRp irq) (node_ne_scRp irq)).symm.trans ho

theorem σR_not_l4v : ¬ validIrqNode (σR (Z := Unit)) := σR_irqNodeFl4.not_l4v

end

section
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
  {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **P3's joint relation forces FL4's domain fact** (module docstring): at a `JAtZ` state whose spec IRQ node is
contiguous from `ksb + 1248`, no IRQ `≥ 128` has an IRQ-node CNode (it would lie in the I/O-port bitmap). -/
theorem jAtZ_irqNodeDom (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hn : ∀ irq : Irq, (σ.interruptIrqNode irq).toNat = (L.ksb s).val + 1248 + 32 * irq.toNat) :
    irqNodeDomFl4 σ := by
  intro irq h n ⟨cs, ho, hw⟩
  have hl : irq.toNat < 256 := irq.isLt
  have h128 : 128 ≤ irq.toNat := h
  have e := hn irq
  exact jAtZ_false_cnodeIo J ho hw (by omega) (by omega) (by omega)

/-- **l4v's `valid_irq_node` is false at every such `JAtZ` state.** -/
theorem jAtZ_not_validIrqNode (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hn : ∀ irq : Irq, (σ.interruptIrqNode irq).toNat = (L.ksb s).val + 1248 + 32 * irq.toNat) :
    ¬ validIrqNode σ :=
  not_validIrqNode_of_dom (jAtZ_irqNodeDom J hn)

/-- **`IrqRel.node`'s domain is `validIrqNodeFl4`'s**: for `i < 128` FL4's node slot `nodeA kb i` is the spec's
one-slot CNode. -/
theorem irqRel_capTable {mem : U64 → U64} {kb : U64} (hI : IrqRel mem kb σ) (hv : validIrqNodeFl4 σ) (i : U64)
    (hi : i.val < 128) : capTableAt 0 (nodeA kb i).bv σ := by
  rw [← hI.node i hi]
  refine hv.2 _ ?_
  show (BitVec.ofNat 8 i.val).toNat < 128
  rw [BitVec.toNat_ofNat]
  exact lt_of_le_of_lt (Nat.mod_le _ _) hi

end

section
open Fl4Proofs.P3

/-- **FL4's IRQ-node fact and P3's IRQ facts hold together at `σB`**: `IrqNodeFl4`, `IrqRel` against `sB`,
`SpecGlobS`, `IdleOutV` and `IrqOutV` at the node. -/
theorem σB_irqCons : IrqNodeFl4 (σB (Z := Unit)) ∧ IrqRel (bsL.mem sB) (bsL.ksb sB) (σB (Z := Unit)) ∧
    SInvG.SpecGlobS (σB (Z := Unit)) ∧ SInvG.IdleOutV (σB (Z := Unit)) ∧
    SInvU.IrqOutV (σB (Z := Unit)).interruptIrqNode (SInvU.uV (σB (Z := Unit))) :=
  ⟨σB_irqNodeFl4, irqRel_B, SInvG.boot_specGlob_B.1, SInvG.boot_specGlob_B.2, SInvU.boot_irqOut_B _⟩

/-- **The same at `σR`.** -/
theorem σR_irqCons : IrqNodeFl4 (σR (Z := Unit)) ∧ IrqRel (bsL.mem sR) (bsL.ksb sR) (σR (Z := Unit)) ∧
    SInvG.SpecGlobS (σR (Z := Unit)) ∧ SInvG.IdleOutV (σR (Z := Unit)) ∧
    SInvU.IrqOutV (σR (Z := Unit)).interruptIrqNode (SInvU.uV (σR (Z := Unit))) :=
  ⟨σR_irqNodeFl4, uE_irqRel, uA_sg_R, idleOut_R, irqOut_R _ node_ne_tRp node_ne_scRp⟩

end

end Fl4Proofs.P2.BootSt
