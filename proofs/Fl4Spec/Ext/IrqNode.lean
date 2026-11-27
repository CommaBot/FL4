/-
FL4 differences (PORTING.md, "FL4 differences"): **the IRQ node covers FL4's 128 IRQs only**.

l4v `Invariants_AI.valid_irq_node` (MCS, X64):

    valid_irq_node s ≡ inj (interrupt_irq_node s) ∧ (∀irq. cap_table_at 0 (interrupt_irq_node s irq) s)

asks a one-slot CNode for every value of `irq` (an 8-bit word on X64: 256 CNodes), and l4v's dummy initial state
(`Init_A.X64_A.init_kheap`, ported as `initKheap`) has them all. FL4 (x86_64) has 128 IRQ numbers
(`crates/fl4-core/src/arch/x86_64/layout.rs`, `irq::COUNT = MAX + 1 = 128`) and one capability slot each, in its
kernel-state block (`crates/fl4-core/src/layout.rs`, `ks::IRQ_NODE`: `irq::COUNT * cte::SIZE` bytes, immediately
followed by `ks::IOPORT_BITMAP`; `interrupt.rs` `irq_slot`). So in FL4's configuration only the IRQs below 128 have
an IRQ-node CNode, and at the spec's contiguous layout the would-be CNodes of IRQs 128..255 lie in the I/O-port
bitmap (P2/BootSpec `jAtZ_false_cnodeIo`, `jAtZ_false_irq128`: impossible at every state of P3's joint relation).

This module states that configuration fact; it changes no ported definition.
* `capTableAt` (l4v `cap_table_at`) and `validIrqNode` (l4v `valid_irq_node`, every IRQ): ported for reference;
* **`validIrqNodeFl4`**: `valid_irq_node` over FL4's IRQs (`irq < fl4IrqCount = 128`): the node is injective there
  and each such IRQ has a one-slot CNode;
* **`irqNodeDomFl4`**: no IRQ `≥ 128` has an IRQ-node CNode (of any size);
* `IrqNodeFl4` = both: **this replaces l4v's 256-entry `valid_irq_node`** in FL4's configuration
  (`not_validIrqNode_of_dom`: the two are exclusive; `validIrqNode.toFl4`: l4v's implies the first half);
* **`initKheapAt node n` / `initIocAt` / `initAStAt node n`**: l4v's `init_kheap` / `init_ioc` / `init_A_st`
  (`Init_A.X64_A`) with the IRQ node at `node` and IRQ CNodes for `irq < n` only; `initAStAt_l4v`:
  `initAStAt initIrqNodePtr 256 = initASt` (l4v's state is the instance at l4v's node and all 256 IRQs);
  `initAStFl4 node := initAStAt node fl4IrqCount` is FL4's.

No premise. No ported module changed.
-/
import Fl4Spec.Init

namespace Fl4Spec

noncomputable section
open Classical

/-- FL4: the number of IRQs (x86_64 `irq::COUNT`, `crates/fl4-core/src/arch/x86_64/layout.rs`). -/
def fl4IrqCount : Nat := 128

variable {Z : Type}

/-- l4v: Invariants_AI.cap_table_at (`obj_at (λko. ∃cs. ko = CNode n cs ∧ well_formed_cnode_n n cs)`). -/
def capTableAt (n : Nat) (p : ObjRef) (s : State Z) : Prop :=
  ∃ cs, s.kheap p = some (.cnode n cs) ∧ wellFormedCnodeN n cs

/-- l4v: Invariants_AI.valid_irq_node (every IRQ, here 256). Not used by FL4: see `IrqNodeFl4`. -/
def validIrqNode (s : State Z) : Prop :=
  Function.Injective s.interruptIrqNode ∧ ∀ irq, capTableAt 0 (s.interruptIrqNode irq) s

/-- **FL4: `valid_irq_node` over FL4's IRQs** (l4v Invariants_AI.valid_irq_node restricted to `irq < 128`). -/
def validIrqNodeFl4 (s : State Z) : Prop :=
  (∀ i j : Irq, i.toNat < fl4IrqCount → j.toNat < fl4IrqCount →
      s.interruptIrqNode i = s.interruptIrqNode j → i = j) ∧
    ∀ irq : Irq, irq.toNat < fl4IrqCount → capTableAt 0 (s.interruptIrqNode irq) s

/-- **FL4: no IRQ outside FL4's range has an IRQ-node CNode.** -/
def irqNodeDomFl4 (s : State Z) : Prop :=
  ∀ irq : Irq, fl4IrqCount ≤ irq.toNat → ∀ n, ¬ capTableAt n (s.interruptIrqNode irq) s

/-- **FL4's IRQ-node fact** (module docstring): it replaces l4v's `valid_irq_node`. -/
def IrqNodeFl4 (s : State Z) : Prop := validIrqNodeFl4 s ∧ irqNodeDomFl4 s

/-- l4v's `valid_irq_node` gives the FL4 half on FL4's IRQs. -/
theorem validIrqNode.toFl4 {s : State Z} (h : validIrqNode s) : validIrqNodeFl4 s :=
  ⟨fun _ _ _ _ e => h.1 e, fun irq _ => h.2 irq⟩

/-- **l4v's `valid_irq_node` fails wherever FL4's domain fact holds** (IRQ 128 has no CNode). -/
theorem not_validIrqNode_of_dom {s : State Z} (h : irqNodeDomFl4 s) : ¬ validIrqNode s :=
  fun hv => h (BitVec.ofNat 8 128) (by decide) 0 (hv.2 _)

/-- So l4v's and FL4's facts are exclusive. -/
theorem IrqNodeFl4.not_l4v {s : State Z} (h : IrqNodeFl4 s) : ¬ validIrqNode s := not_validIrqNode_of_dom h.2

/-! ## The initial state with the restricted IRQ node -/

/-- l4v: Init_A.X64_A.init_kheap with the IRQ node at `node` and IRQ CNodes for `irq < n` only (every other entry
`initKheap`'s). -/
def initKheapAt (node : ObjRef) (n : Nat) : KHeap :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (fun x => if ∃ irq : Irq, irq.toNat < n ∧ node + (ucast 64 irq <<< cteLevelBits) = x
              then some (.cnode 0 (emptyCnode 0))
              else none)
    idleThreadPtr (some (.tcb
      { tcbCtable := .nullCap,
        tcbVtable := .nullCap,
        tcbIpcframe := .nullCap,
        tcbFaultHandler := .nullCap,
        tcbTimeoutHandler := .nullCap,
        tcbEpt := .nullCap,
        tcbState := .idleThreadState,
        tcbIpcBuffer := 0,
        tcbFault := none,
        tcbBoundNotification := none,
        tcbMcpriority := 0,
        tcbSchedContext := some idleScPtr,
        tcbYieldTo := none,
        tcbPriority := 0,
        tcbDomain := defaultDomain,
        tcbFlags := ∅,
        tcbArch := initArchTcb })))
    idleScPtr (some (.schedContext
      { defaultSchedContext with
        scTcb := some idleThreadPtr,
        scRefills := [{ rTime := 0, rAmount := MAX_PERIOD }, { rTime := MAX_PERIOD, rAmount := 0 }],
        scBudget := MAX_PERIOD,
        scRefillMax := MIN_REFILLS } 0)))
    initGlobalPml4 (some (.archObj (.pageMapL4 globalPml4))))
    initGlobalPdpt (some (.archObj (.pdPointerTable globalPdpt))))
    initGlobalPd (some (.archObj (.pageDirectory globalPd)))

/-- l4v: Init_A.X64_A.init_ioc over `initKheapAt node n`. -/
def initIocAt (node : ObjRef) (n : Nat) : CslotPtr → Bool := fun (a, b) =>
  decide (∃ obj, initKheapAt node n a = some obj ∧ (∃ cap, capOf obj b = some cap ∧ ¬cap = .nullCap))

/-- l4v: Init_A.X64_A.init_A_st with the IRQ node at `node` and IRQ CNodes for `irq < n` only. -/
def initAStAt [StateExt Z] (node : ObjRef) (n : Nat) : State Z :=
  { (initASt (Z := Z)) with
    kheap := initKheapAt node n,
    isOriginalCap := initIocAt node n,
    interruptIrqNode := fun irq => node + (ucast 64 irq <<< cteLevelBits) }

/-- **FL4's initial state at IRQ node `node`**: CNodes for FL4's 128 IRQs only. -/
def initAStFl4 [StateExt Z] (node : ObjRef) : State Z := initAStAt node fl4IrqCount

/-- l4v's heap is the instance at l4v's node with all 256 IRQs. -/
theorem initKheapAt_l4v : initKheapAt initIrqNodePtr 256 = initKheap := by
  have h : (fun x => if ∃ irq : Irq, irq.toNat < 256 ∧ initIrqNodePtr + (ucast 64 irq <<< cteLevelBits) = x
        then some (KernelObject.cnode 0 (emptyCnode 0)) else none) =
      (fun x => if ∃ irq : Irq, initIrqNodePtr + (ucast 64 irq <<< cteLevelBits) = x
        then some (KernelObject.cnode 0 (emptyCnode 0)) else none) := by
    funext x
    exact if_congr ⟨fun ⟨i, _, e⟩ => ⟨i, e⟩, fun ⟨i, e⟩ => ⟨i, i.isLt, e⟩⟩ rfl rfl
  unfold initKheapAt initKheap
  rw [h]

/-- **l4v's dummy initial state is the instance at l4v's node with all 256 IRQs.** -/
theorem initAStAt_l4v [StateExt Z] : initAStAt (Z := Z) initIrqNodePtr 256 = initASt := by
  unfold initAStAt initIocAt
  rw [initKheapAt_l4v]
  rfl

end

end Fl4Spec
