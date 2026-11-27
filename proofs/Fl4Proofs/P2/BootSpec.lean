/-
# P2 (line p3mc, gen 34): the relocated spec boot state `σB` (handoff §38c)

Gen 33 (`P2/BootL4vRefute`) proved `JAtZ` false at l4v's dummy initial state `initASt` (Fl4Spec/Init, l4v
`Init_A.init_A_st`) for every store: FL4's kernel-state block holds the spec's IRQ node at offset 1248, and with
`interruptIrqNode 0 = kernelBase + 0x2000` the block overlaps the idle TCB at `kernelBase + 0x1000`.

`σB` is `initASt` with **the IRQ node moved** to `irqNodeB = kbB + 1248`, `kbB = kernelBase + 0x8000`, and **only
FL4's 128 IRQs given a CNode** (`kheapB` / `iocB`: `initKheap` / `initIoc` with `initIrqNodePtr` replaced by
`irqNodeB` and the IRQ-CNode clause restricted to `irq < 128`; every other field is `initASt`'s). Not a spec change:
a state of the ported spec, defined here (l4v source of each field: `Init_A.X64_A`, as `initASt`).

**Found false (gen 34): the plan's §38c state, with all 256 IRQ CNodes, is not a `JAtZ` state either.**
`jAtZ_false_cnodeIo`: at every `JAtZ` state, no well-formed spec CNode starts at an 8-aligned address of FL4's I/O-port
bitmap `[ksb + 5344, ksb + 13536)` — `FinInv.kt` (`KTyped`) makes it a CNode of the typed heap, and `JAtZ.ioLay`
(`IoLayout.out`) keeps every bitmap word outside the typed heap's objects. With the IRQ node at `ksb + 1248`
(`IrqRel.node`, forced for `irq < 128`) and the spec's contiguous layout, IRQ `128 + j`'s CNode is at
`ksb + 5344 + 32 j`, inside the bitmap. l4v's `valid_irq_node` asks a CNode for all 256 IRQs; no P3 invariant does
(P3 reads `interruptIrqNode` only through `IrqRel` (`< 128`), `SpecGlob*` and `IrqOutV`, which constrain caps
present, not existence), so `σB` drops them.

The layout (all in `kernelBase + …`): idle TCB `[0x1000, 0x2000)`, global PML4 / PDPT / PD `0x4000 / 0x5000 / 0x6000`
(4 KiB each), idle SC `0x7000` (spec size bits 0); FL4's block `[0x8000, 0xB500)` (13568 bytes), core 0's node
`[0xB500, 0xC5C0)` (4288 bytes). The 256 spec IRQ CNodes (32 bytes each) lie in `[0x84E0, 0xA4E0)`, inside the block.

Proved (the two clashes of §38b avoided):
* **`σB_irqRel_node`**: `IrqRel.node` at base `kbB` (`σB.interruptIrqNode i = nodeA kbB i` for `i < 128`);
* **`σB_bootLay`**: the conclusion of `jAtZ_bootLay` holds at `σB` with `ksb = kbB`, `curW = idleThreadPtr`
  (the idle TCB's 4 KiB end below the block);
* **`σB_below`**: every non-IRQ object of `kheapB` (idle TCB, PML4, PDPT, PD, idle SC; 4 KiB each, the SC far
  smaller) ends at or below `kbB`: so neither the block (`JKern.hks` / `hksIn`) nor core 0's node (`JKern.hnd`) meets
  them (the PDPT / PD clash of §38b is gone);
* **`σB_irq_in`**: every spec IRQ CNode lies inside the block's IRQ-node area and misses core 0's node;
* **`jAtZ_false_cnodeIo`** (above);
* `kbB_fit`, `kbB_al` (`JKern.ksbFit` / `nodeFit` for `cpu = 0`, `IntLayout.fit` / `align`, `JKern.ksbAl`).

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootL4vRefute
import Fl4Proofs.P3.IntRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open Fl4Spec Classical

noncomputable section

/-- FL4's kernel-state base at the boot state: `kernelBase + 0x8000`. -/
def kbB : U64 := ⟨BitVec.ofNat 64 18446744071562100736⟩

/-- The relocated IRQ node (256 one-slot CNodes of 32 bytes): `kbB + 1248`, FL4's `IRQ_NODE` offset. -/
def irqNodeB : ObjRef := BitVec.ofNat 64 18446744071562101984

/-- `initKheap` (l4v `Init_A.X64_A.init_kheap`, MCS idle objects from RISCV64 `rt`) with the IRQ node at
`irqNodeB`. -/
def kheapB : KHeap :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (fun x => if ∃ irq : Irq, irq.toNat < 128 ∧ irqNodeB + (ucast 64 irq <<< cteLevelBits) = x
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

/-- `initIoc` (l4v `Init_A.X64_A.init_ioc`) over `kheapB`. -/
def iocB : CslotPtr → Bool := fun (a, b) =>
  decide (∃ obj, kheapB a = some obj ∧ (∃ cap, capOf obj b = some cap ∧ ¬cap = .nullCap))

/-- **The relocated boot state** (module docstring): `initASt` (l4v `Init_A.X64_A.init_A_st`) with the IRQ node at
`irqNodeB`. -/
def σB {Z : Type} [StateExt Z] : State Z :=
  { kheap := kheapB,
    cdt := initCdt,
    isOriginalCap := iocB,
    curThread := idleThreadPtr,
    idleThread := idleThreadPtr,
    idleSc := idleScPtr,
    consumedTime := 0,
    curTime := 0,
    curSc := idleScPtr,
    reprogramTimer := false,
    schedulerAction := .resumeCurThread,
    domainList := [(0, -1), (0, 0)],
    domainIndex := 0,
    domainStartIndex := 0,
    curDomain := 0,
    domainTime := 15,
    readyQueues := fun _ _ => [],
    releaseQueue := [],
    machineState := initMachineState,
    interruptIrqNode := fun irq => irqNodeB + (ucast 64 irq <<< cteLevelBits),
    interruptStates := fun _ => .irqInactive,
    archState := initArchState,
    exst := StateExt.extInit }

theorem kbB_val : kbB.val = 18446744071562100736 := by
  show (BitVec.ofNat 64 18446744071562100736).toNat = _; decide

theorem kbB_eq : kbB.bv = kernelBase + 0x8000 := by decide

theorem irqNodeB_eq : irqNodeB = kernelBase + 0x84E0 := by decide

theorem kbB_fit : kbB.val + 13568 + (0 + 1) * 4288 ≤ 2 ^ 64 := by rw [kbB_val]; norm_num

theorem kbB_al : kbB.val % 32 = 0 := by rw [kbB_val]

theorem kbB_al8 : kbB.val % 8 = 0 := by rw [kbB_val]

theorem kbB_fit' : kbB.val + 13568 ≤ 2 ^ 64 := by rw [kbB_val]; norm_num

/-- The spec's IRQ node of `irq`, as a number. -/
theorem σB_node_val (irq : Irq) :
    ((σB (Z := Unit)).interruptIrqNode irq).toNat = kbB.val + 1248 + 32 * irq.toNat := by
  rw [kbB_val]
  show (irqNodeB + (ucast 64 irq <<< cteLevelBits)).toNat = _
  have hi := irq.isLt
  simp only [irqNodeB, ucast, cteLevelBits, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- **`IrqRel.node` at base `kbB`**: the spec's IRQ node of `i < 128` is FL4's `nodeA kbB i`. -/
theorem σB_irqRel_node (i : U64) (hi : i.val < 128) :
    (σB (Z := Unit)).interruptIrqNode (BitVec.ofNat 8 i.val) = (P3.nodeA kbB i).bv := by
  apply BitVec.eq_of_toNat_eq
  rw [σB_node_val]
  have h := P3.nodeA_val (kb := kbB) (i := i) kbB_fit' hi
  show _ = (P3.nodeA kbB i).val
  rw [h]
  simp only [BitVec.toNat_ofNat]
  omega

/-- **`jAtZ_bootLay`'s conclusion holds at `σB`** with `ksb = kbB` and the idle thread current: IRQ node 0 is
`kbB + 1248`, and the idle TCB's 4 KiB end below the block. -/
theorem σB_bootLay :
    ((σB (Z := Unit)).interruptIrqNode (BitVec.ofNat 8 0)).toNat = kbB.val + 1248 ∧
      (σB (Z := Unit)).curThread.toNat + 4096 ≤ kbB.val := by
  refine ⟨by rw [σB_node_val]; rfl, ?_⟩
  have e : idleThreadPtr.toNat = 18446744071562072064 := by decide
  rw [kbB_val]; show idleThreadPtr.toNat + 4096 ≤ _; rw [e]; omega

/-- **Every non-IRQ object of `kheapB` ends at or below the block** (4 KiB from each of the idle TCB, PML4, PDPT,
PD and idle SC). -/
theorem σB_below : idleThreadPtr.toNat + 4096 ≤ kbB.val ∧ initGlobalPml4.toNat + 4096 ≤ kbB.val ∧
    initGlobalPdpt.toNat + 4096 ≤ kbB.val ∧ initGlobalPd.toNat + 4096 ≤ kbB.val ∧
    idleScPtr.toNat + 4096 ≤ kbB.val := by
  have e1 : idleThreadPtr.toNat = 18446744071562072064 := by decide
  have e2 : initGlobalPml4.toNat = 18446744071562084352 := by decide
  have e3 : initGlobalPdpt.toNat = 18446744071562088448 := by decide
  have e4 : initGlobalPd.toNat = 18446744071562092544 := by decide
  have e5 : idleScPtr.toNat = 18446744071562096640 := by decide
  rw [kbB_val, e1, e2, e3, e4, e5]; omega

/-- **Every spec IRQ CNode lies in the block's IRQ-node area** `[kbB + 1248, kbB + 9440)` (so inside the 13568-byte
block, below core 0's node at `kbB + 13568`). -/
theorem σB_irq_in (irq : Irq) :
    kbB.val + 1248 ≤ ((σB (Z := Unit)).interruptIrqNode irq).toNat ∧
      ((σB (Z := Unit)).interruptIrqNode irq).toNat + 32 ≤ kbB.val + 9440 := by
  rw [σB_node_val]
  have := irq.isLt
  constructor <;> omega

/-- The heap's IRQ CNode addresses are the spec's IRQ node. -/
theorem kheapB_irq {x : ObjRef} :
    (∃ irq : Irq, irq.toNat < 128 ∧ irqNodeB + (ucast 64 irq <<< cteLevelBits) = x) ↔
      ∃ irq : Irq, irq.toNat < 128 ∧ (σB (Z := Unit)).interruptIrqNode irq = x := Iff.rfl

end

section
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
  {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **No well-formed spec CNode in FL4's I/O-port bitmap** at any `JAtZ` state (module docstring): `KTyped` puts it
in the typed heap, `IoLayout.out` keeps the bitmap words outside the typed heap's objects. -/
theorem jAtZ_false_cnodeIo (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {o : BitVec 64} {r : Nat}
    {cs : CnodeContents} (ho : σ.kheap o = some (.cnode r cs)) (hw : wellFormedCnodeN r cs)
    (h1 : (L.ksb s).val + 5344 ≤ o.toNat) (h2 : o.toNat < (L.ksb s).val + 13536)
    (h8 : (o.toNat - (L.ksb s).val) % 8 = 0) : False := by
  have hf := J.kern.ksbFit
  have hkt := ((J.xtop.rel.2.2.1.kt o).1 r cs ho hw)
  have hwv : (⟨BitVec.ofNat 64 ((o.toNat - (L.ksb s).val - 5344) / 8)⟩ : U64).val =
      (o.toNat - (L.ksb s).val - 5344) / 8 := by
    show (BitVec.ofNat 64 _).toNat = _
    simp; omega
  have hwl : (⟨BitVec.ofNat 64 ((o.toNat - (L.ksb s).val - 5344) / 8)⟩ : U64).val < 1024 := by rw [hwv]; omega
  have hio := J.ioLay.out _ hwl
  have hv := ioA_val hf hwl
  rw [hwv] at hv
  have hp : 0 < 2 ^ r := Nat.two_pow_pos r
  exact hio.2 ⟨o⟩ _ hkt ⟨by show o.toNat ≤ _; rw [hv]; omega,
    by show _ < o.toNat + P3.objSize (.cnode r); simp only [P3.objSize]; rw [hv]; omega⟩

/-- In particular IRQ `128`'s CNode at the spec's contiguous layout (`ksb + 1248 + 32 · 128 = ksb + 5344`) is
impossible at every `JAtZ` state. -/
theorem jAtZ_false_irq128 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {o : BitVec 64}
    (hn : o.toNat = (L.ksb s).val + 1248 + 32 * 128) :
    σ.kheap o ≠ some (.cnode 0 (emptyCnode 0)) := by
  intro ho
  refine jAtZ_false_cnodeIo J ho ?_ (by omega) (by omega) (by omega)
  unfold wellFormedCnodeN emptyCnode dom
  ext x; simp

end

end Fl4Proofs.P2.BootSt
