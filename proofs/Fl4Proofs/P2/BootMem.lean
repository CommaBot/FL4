/-
# P2 (line p3mc, gen 34): the concrete boot memory and ghosts over `bst` (handoff §38d), and `JKern` there

The store state **`sB = BS.of memB kbB 0`** (`P2/BootStore`'s `bst`, kernel-state base `kbB = kernelBase + 0x8000`,
CPU 0) for the spec boot state `σB` (`P2/BootSpec`), with the ghosts of §38d:

* **`memB`** (`wordB` on the address): every word 0 except
  core 0's node (base `NB = kbB + 13568`): `CUR_THREAD = IDLE_THREAD = tiB`, `CUR_SC = IDLE_SC = sciB`;
  the kernel-state block: `DOMAIN_TIME = 15`, domain entry 0's duration `2^56 − 1` (`domainList = [(0, −1), (0, 0)]`),
  `FEATURES = 2` (huge pages), `KERNEL_ROOT = krootB` (the global PML4 as a physical-map pointer);
  the idle TCB `tiB = idleThreadPtr`: `STATE = 7` (idle), `SC = sciB`;
  the idle SC `sciB = idleScPtr`: `TCB = tiB`, `REFILL_MAX = 2`, `REFILL_TAIL = 1`, refills `(0, MAX_PERIOD)`,
  `(MAX_PERIOD, 0)`.
* **`HB`** (P1's heap): `tiB ↦ tcb`, `sciB ↦ sc 7`, PML4 / PDPT / PD `↦ other 12`, and the block as P3's `ksH kbB`
  (IRQ-node CNodes `other 5`, other words `other 3`).
* **`thB`** (the typed heap): `tiB ↦ tcb`, the 128 IRQ-node CNodes `↦ cnode 0`.
* **`DB`** = {PML4, PDPT, PD}, **`CsB`** = {0}.

Proved: `HB_cases`, **`heapB_ok`** (`HeapOK HB`), `thB_cases`, the store lookups (`memB_mem`, `sB_nodeAt_val`,
`sB_curW`, `sB_idleW`, `sB_cscW`, …) and **`jKern_boot`**: P3's `JKern archT HB CsB DB thB sB σB` (every field:
original caps vacuous, the current thread, the action word, the debug list, the global PML4, `H`'s placement against
the block and core 0's node, the core set, and `TdxRel archT σB`).

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootSpecInv
import Fl4Proofs.P2.LocPlatModel
import Fl4Proofs.P3.KsHeap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1 Fl4Spec Classical

noncomputable section

/-! ## Addresses (as numbers: `kbB.val = 18446744071562100736`) -/

/-- The idle TCB (`idleThreadPtr`). -/
def tiB : U64 := ⟨BitVec.ofNat 64 18446744071562072064⟩
/-- The idle SC (`idleScPtr`). -/
def sciB : U64 := ⟨BitVec.ofNat 64 18446744071562096640⟩
/-- `KERNEL_ROOT`: the global PML4's physical address in the physical map. -/
def krootB : U64 := ⟨ptrFromPAddr (addrFromKPPtr initGlobalPml4)⟩
/-- The spec's `MAX_PERIOD` as a word. -/
def maxPB : U64 := ⟨MAX_PERIOD⟩

theorem tiB_val : tiB.val = 18446744071562072064 := by
  show (BitVec.ofNat 64 18446744071562072064).toNat = _; decide
theorem sciB_val : sciB.val = 18446744071562096640 := by
  show (BitVec.ofNat 64 18446744071562096640).toNat = _; decide
theorem tiB_bv : tiB.bv = idleThreadPtr := by decide
theorem sciB_bv : sciB.bv = idleScPtr := by decide

/-- The boot words by address (module docstring). Node 0 is at `18446744071562114304 = kbB + 13568`. -/
def wordB (n : Nat) : U64 :=
  if n = 18446744071562114304 ∨ n = 18446744071562114312 then tiB
  else if n = 18446744071562114328 ∨ n = 18446744071562114336 then sciB
  else if n = 18446744071562100752 then 15#u64
  else if n = 18446744071562100936 then ⟨BitVec.ofNat 64 (2 ^ 56 - 1)⟩
  else if n = 18446744071562100808 then 2#u64
  else if n = 18446744071562100784 then krootB
  else if n = 18446744071562072064 + 3328 then 7#u64
  else if n = 18446744071562072064 + 3464 then sciB
  else if n = 18446744071562096640 + 24 then tiB
  else if n = 18446744071562096640 + 72 then 2#u64
  else if n = 18446744071562096640 + 88 then 1#u64
  else if n = 18446744071562096640 + 104 ∨ n = 18446744071562096640 + 112 then maxPB
  else 0#u64

/-- The boot memory. -/
def memB (a : U64) : U64 := wordB a.val

/-- **The boot store state.** -/
def sB : BS := BS.of memB kbB 0#u64

theorem memB_mem {a : U64} (ha : Aligned a) : bsL.mem sB a = wordB a.val := BS.of_mem memB kbB 0#u64 ha

theorem sB_ksb : bsL.ksb sB = kbB := rfl
theorem sB_cpu : bsL.cpu sB = 0#u64 := rfl

/-- Core 0's node words of `sB`. -/
theorem sB_nodeAt_val {off : U64} (ho : off.val < 4288) :
    (bsL.nodeAt sB 0#u64 off).val = 18446744071562114304 + off.val := by
  unfold LawfulStore.nodeAt
  rw [sB_ksb]
  simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, kbB_val]
  simp [U64.size, U64.numBits]
  omega

theorem sB_nodeBase (c : U64) (hc : c = 0#u64) : bsL.nodeBase sB c = 18446744071562114304 := by
  subst hc
  show (bsL.ksb sB).val + 13568 + (0#u64 : U64).val * 4288 = _
  rw [sB_ksb, kbB_val]; rfl

theorem node_aligned {off : U64} (ho : off.val < 4288) (h8 : off.val % 8 = 0) :
    Aligned (bsL.nodeAt sB 0#u64 off) := by
  show (bsL.nodeAt sB 0#u64 off).val % 8 = 0
  rw [sB_nodeAt_val ho]; omega

theorem sB_curW : bsL.curW sB = tiB := by
  unfold LawfulStore.curW
  rw [sB_cpu]
  have h0 : layout.node.CUR_THREAD.val = 0 := curth0
  rw [memB_mem (node_aligned (by omega) (by omega)), sB_nodeAt_val (by omega), h0]
  simp [wordB]

theorem sB_idleW : bsL.idleW sB = tiB := by
  unfold LawfulStore.idleW
  rw [sB_cpu]
  have h0 : layout.node.IDLE_THREAD.val = 8 := by simp [layout.node.IDLE_THREAD]
  rw [memB_mem (node_aligned (by omega) (by omega)), sB_nodeAt_val (by omega), h0]
  simp [wordB]

theorem sB_cscW : bsL.cscW sB = sciB := by
  unfold LawfulStore.cscW LawfulStore.nodeA
  rw [sB_cpu]
  have h0 : layout.node.CUR_SC.val = 24 := by simp [layout.node.CUR_SC]
  rw [memB_mem (node_aligned (by omega) (by omega)), sB_nodeAt_val (by omega), h0]
  simp [wordB]

theorem sB_act_val : (bsL.nodeAt sB (bsL.cpu sB) layout.node.SCHED_ACTION).val = 18446744071562114320 := by
  rw [sB_cpu, sB_nodeAt_val (by rw [act_val]; omega), act_val]

theorem sB_dbg_val : (bsL.nodeAt sB 0#u64 layout.node.DEBUG_TCBS).val = 18446744071562114392 := by
  rw [sB_nodeAt_val (by rw [debug_val]; omega), debug_val]

theorem sB_dbg_word : bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.DEBUG_TCBS) = 0#u64 := by
  rw [memB_mem (by show _ % 8 = 0; rw [sB_dbg_val]), sB_dbg_val]
  simp [wordB]

/-! ## The heaps -/

/-- **P1's heap at the boot** (module docstring). -/
def HB : P1.Heap := fun p =>
  if p.val = 18446744071562072064 then some .tcb
  else if p.val = 18446744071562096640 then some (.sc 7)
  else if p.val = 18446744071562084352 ∨ p.val = 18446744071562088448 ∨ p.val = 18446744071562092544 then
    some (.other 12)
  else Sched.ksH kbB p

/-- **The typed heap at the boot**: the idle TCB and the 128 IRQ-node CNodes. -/
def thB : TypedHeap := fun p =>
  if p.val = 18446744071562072064 then some .tcb
  else if 18446744071562100736 + 1248 ≤ p.val ∧ p.val < 18446744071562100736 + 5344 ∧
    (p.val - 18446744071562100736) % 32 = 0 then some (.cnode 0)
  else none

/-- The dead set: the spec's three global paging structures. -/
def DB : Set U64 := {p | p.val = 18446744071562084352 ∨ p.val = 18446744071562088448 ∨ p.val = 18446744071562092544}

/-- The core set: core 0. -/
def CsB : Set U64 := {0#u64}

theorem HB_cases {p : U64} {k : HKind} (h : HB p = some k) :
    (p.val = 18446744071562072064 ∧ k = .tcb) ∨ (p.val = 18446744071562096640 ∧ k = .sc 7) ∨
    ((p.val = 18446744071562084352 ∨ p.val = 18446744071562088448 ∨ p.val = 18446744071562092544) ∧
      k = .other 12) ∨
    (k = .other 5 ∧ 18446744071562100736 + 1248 ≤ p.val ∧ p.val < 18446744071562100736 + 5344 ∧
      (p.val - 18446744071562100736) % 32 = 0) ∨
    (k = .other 3 ∧ 18446744071562100736 ≤ p.val ∧ p.val < 18446744071562100736 + 13568 ∧
      (p.val - 18446744071562100736) % 8 = 0 ∧
      ¬ (18446744071562100736 + 1248 ≤ p.val ∧ p.val < 18446744071562100736 + 5344)) := by
  unfold HB at h
  split_ifs at h with h1 h2 h3
  · cases h; exact Or.inl ⟨h1, rfl⟩
  · cases h; exact Or.inr (Or.inl ⟨h2, rfl⟩)
  · cases h; exact Or.inr (Or.inr (Or.inl ⟨h3, rfl⟩))
  · have := Sched.ksH_some h
    rw [kbB_val] at this
    exact Or.inr (Or.inr (Or.inr this))

theorem thB_cases {p : U64} {k : ObjKind} (h : thB p = some k) :
    (p.val = 18446744071562072064 ∧ k = .tcb) ∨
    (k = .cnode 0 ∧ 18446744071562100736 + 1248 ≤ p.val ∧ p.val < 18446744071562100736 + 5344 ∧
      (p.val - 18446744071562100736) % 32 = 0) := by
  unfold thB at h
  split_ifs at h with h1 h2
  · cases h; exact Or.inl ⟨h1, rfl⟩
  · cases h; exact Or.inr ⟨rfl, h2⟩

theorem HB_ti : HB tiB = some .tcb := by unfold HB; rw [if_pos tiB_val]
theorem HB_sci : HB sciB = some (.sc 7) := by unfold HB; rw [if_neg (by rw [sciB_val]; omega), if_pos sciB_val]
theorem thB_ti : thB tiB = some .tcb := by unfold thB; rw [if_pos tiB_val]

theorem U64.ne_of_val {p q : U64} (h : p ≠ q) : p.val ≠ q.val := fun e => h (by rw [UScalar.eq_equiv]; exact e)

/-- **`HB` is well formed.** -/
theorem heapB_ok : HeapOK HB where
  align := by
    intro p k hp
    rcases HB_cases hp with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨rfl, h1, h2, h3⟩ | ⟨rfl, h1, h2, h3, -⟩ <;>
      simp only [HKind.bits, Nat.reducePow] <;> omega
  fits := by
    intro p k hp
    rcases HB_cases hp with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨rfl, h1, h2, h3⟩ | ⟨rfl, h1, h2, h3, -⟩ <;>
      simp only [HKind.bits, Nat.reducePow] <;> omega
  lt64 := by
    intro p k hp
    rcases HB_cases hp with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [HKind.bits]
  scmin := by
    intro p z hp
    rcases HB_cases hp with ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> cases e
    exact le_refl _
  disj := by
    intro p k q k' hp hq hne
    have hv := U64.ne_of_val hne
    rcases HB_cases hp with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨rfl, h1, h2, h3⟩ | ⟨rfl, h1, h2, h3, h4⟩ <;>
    rcases HB_cases hq with ⟨g1, rfl⟩ | ⟨g1, rfl⟩ | ⟨g1, rfl⟩ | ⟨rfl, g1, g2, g3⟩ | ⟨rfl, g1, g2, g3, g4⟩ <;>
      simp only [HKind.bits, Nat.reducePow] <;> omega

theorem HB_zero : HB 0#u64 = none := by
  cases h : HB 0#u64 with
  | none => rfl
  | some k =>
    have h0 : (0#u64 : U64).val = 0 := rfl
    rcases HB_cases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> omega

/-! ## `JKern` at the boot -/

/-- `σB`'s original-cap map is everywhere false: every cap of `kheapB` is null. -/
theorem iocB_false (sl : CslotPtr) : (σB (Z := Unit)).isOriginalCap sl = false := by
  obtain ⟨a, b⟩ := sl
  show iocB (a, b) = false
  unfold iocB
  rw [decide_eq_false_iff_not]
  rintro ⟨o, ho, c, hc, hn⟩
  have : c = .nullCap := by
    have hv : SInvU.capView o b = some c := by
      simp only [kheapB, Function.update_apply] at ho
      split_ifs at ho <;> (cases ho) <;> first
        | exact hc
        | (simp only [Fl4Spec.capOf] at hc; cases hc)
        | (simp only [Fl4Spec.capOf, SInvU.capView] at hc ⊢; rw [if_pos (by unfold wellFormedCnodeN emptyCnode dom; ext x; simp)];
            exact hc)
    exact SInvU.init_cv_B ho hv
  exact hn this

theorem objSize_pos (k : ObjKind) : 0 < P3.objSize k ∨ k = .other 0 := by
  cases k with
  | cnode r => left; simp only [P3.objSize]; have := Nat.two_pow_pos r; omega
  | tcb => left; simp [P3.objSize]
  | other n => cases n with
    | zero => right; rfl
    | succ n => left; simp [P3.objSize]

/-- A word of `thB`'s objects lies in the idle TCB or the IRQ node. -/
theorem thB_in {p : U64} {k : ObjKind} (hp : thB p = some k) {b : Nat} (h1 : p.val ≤ b) (h2 : b < p.val + P3.objSize k) :
    (18446744071562072064 ≤ b ∧ b < 18446744071562072064 + 4096) ∨
      (18446744071562100736 + 1248 ≤ b ∧ b < 18446744071562100736 + 5344) := by
  rcases thB_cases hp with ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩
  · simp only [P3.objSize] at h2; omega
  · simp only [P3.objSize, Nat.pow_zero] at h2; omega

/-- **P3's kernel-global placement at the boot** (`JKern`). -/
theorem jKern_boot : JKern (L := bsL) LocPlatM.archT HB CsB DB thB sB (σB (Z := Unit)) where
  orig sl h := by rw [iocB_false] at h; cases h
  cur := by rw [sB_curW, tiB_bv]; rfl
  curT := by rw [sB_curW]; exact thB_ti
  act := by
    refine ⟨by show _ % 8 = 0; rw [sB_act_val], fun p k hp ⟨h1, h2⟩ => ?_⟩
    rw [sB_act_val] at h1 h2
    rcases thB_in hp h1 h2 with h | h <;> omega
  dwAl := by show _ % 8 = 0; rw [sB_dbg_val]
  dwObj := by
    rintro a ⟨p, i, hi, rfl⟩ ⟨h1, h2⟩
    rw [sB_dbg_val] at h1 h2
    obtain ⟨k, hk, hsz⟩ := hi.size
    rcases thB_cases hk with ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩
    · simp only [P3.objSize] at hsz
      rw [slotOf_val (by omega)] at h1 h2; omega
    · simp only [P3.objSize, Nat.pow_zero] at hsz
      rw [slotOf_val (by omega)] at h1 h2; omega
  dwNe := by
    rw [sB_dbg_val, sB_act_val, sB_curW]
    have : (P1.stA tiB).val = 18446744071562072064 + 3328 := by
      rw [P1.stA_eq]; simp only [core.num.U64.wrapping_add_val_eq, tiB_val]; simp [U64.size, U64.numBits]
    rw [this]; omega
  head := Or.inl sB_dbg_word
  gpm := by
    refine ⟨globalPml4, ?_⟩
    show kheapB initGlobalPml4 = _
    unfold kheapB
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  ga := by
    show initGlobalPml4.toNat % 4096 = 0
    have e : initGlobalPml4.toNat = 18446744071562084352 := by decide
    rw [e]
  gf := by
    show initGlobalPml4.toNat + 4096 ≤ 2 ^ 64
    have e : initGlobalPml4.toNat = 18446744071562084352 := by decide
    rw [e]; norm_num
  heap := heapB_ok
  h0 := HB_zero
  hks p k hp hk := by
    rw [sB_ksb, kbB_val]
    rcases HB_cases hp with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨-, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp only [HKind.bits, Nat.reducePow]; omega
    · simp only [HKind.bits, Nat.reducePow]; omega
    · exact absurd rfl (hk 12)
    · exact absurd rfl (hk 5)
    · exact absurd rfl (hk 3)
  hksIn p z hp := by
    rw [sB_ksb, kbB_val]
    rcases HB_cases hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨h1, e⟩ | ⟨e, h1, h2, h3⟩ | ⟨e, h1, h2, h3, -⟩ <;> cases e
    · left; simp only [Nat.reducePow]; omega
    · right; right; simp only [Nat.reducePow]; omega
    · right; right; simp only [Nat.reducePow]; omega
  hnd p k hp c hc := by
    rw [sB_nodeBase c hc]
    rcases HB_cases hp with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨rfl, h1, h2, h3⟩ | ⟨rfl, h1, h2, h3, -⟩ <;>
      simp only [HKind.bits, Nat.reducePow] <;> omega
  ksbFit := by rw [sB_ksb, kbB_val]; norm_num
  ksbAl := by rw [sB_ksb, kbB_val]
  nodeFit := by rw [sB_ksb, sB_cpu, kbB_val]; norm_num
  cpuCs := by rw [sB_cpu]; rfl
  curH := by rw [sB_curW]; exact HB_ti
  cscH := by rw [sB_cscW, HB_sci]; exact Option.some_ne_none _
  csLt c hc := by rw [show c = 0#u64 from hc]; decide
  cs0 := rfl
  csN := ⟨1, fun c => by
    show c = 0#u64 ↔ c.val < 1
    constructor
    · rintro rfl; decide
    · intro h; exact UScalar.eq_of_val_eq (by show c.val = 0; omega)⟩
  tdx := ⟨fun _ => rfl, fun _ _ _ => rfl⟩

end

end Fl4Proofs.P2.BootSt
