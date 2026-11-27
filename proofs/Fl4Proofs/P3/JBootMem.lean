/-
P3 (line jboot, gen 2): **the witness's concrete FL4 memory image `w0`** on P2's word store `wst` (WitPlat), with
kernel-state base `fkb`, CPU 0, and the conjuncts of `JAtZ` that read only kernel-global words, at the spec boot
state `fInitASt` (JBootSt / JBootChar).

The image (`img`, a function of the byte address; every other word is 0):
* kernel-global block at `fkb`: `NUM_NODES` = 1, `DOMAIN_TIME` = 15 (`initASt`'s `domainTime`),
  `KERNEL_ROOT` = the global PML4's physical address in the physical window (`kRootV`), `FEATURES` = 2
  (`FEATURE_HUGE_PAGES`: `initArchState.x64Plat.hugePages = true`), the domain schedule `[(0, 2^56 - 1), (0, 0)]`
  (`initASt.domainList = [(0, -1), (0, 0)]`); IRQ states, IRQ node slots and the IO-port bitmap zero;
* core 0's node (`fkb + 13568`): `CUR_THREAD` = `IDLE_THREAD` = the idle TCB, `CUR_SC` = `IDLE_SC` = the idle SC,
  action 0 (resume), times 0, queues empty;
* the idle TCB (`idleThreadPtr`): `STATE` = 7 (idle), `SC` = the idle SC; registers, priority, domain, links 0;
* the idle SC (`idleScPtr`): `TCB` = the idle TCB, `REFILL_MAX` = 2, head 0, tail 1, refills
  `(0, MAX_PERIOD), (MAX_PERIOD, 0)`.

Proved here (handoff conjunct table): **`w0_irqRel`** (`IrqRel`, both parts), **`w0_ioRel`** (`IoRel`),
**`w0_kRootRel`** (`KRootRel`: `KRootW` and `HugeRel`), **`w0_domRel`** (`DomRel`), **`w0_ar`** (`wAR`), the
kernel-state block's numeric facts of `JKern` (**`w0_jkernNum`**: `ksbFit`, `ksbAl`, `nodeFit`, `cpuCs`, `csLt`,
`cs0`, `csN` at `Cs = {0}`), and the global PML4's `JKern.ga` / `gf` (**`fInit_gpm_al`**).

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootChar
import Fl4Proofs.P2.WitPlat
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.Vs Fl4Proofs.P2.Wit

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The image -/

/-- The kernel root word: the global PML4's physical address in the physical window
(`ptrFromPAddr (addrFromKPPtr initGlobalPml4)`). -/
def kRootV : U64 := 18446743523953754112#u64

/-- The idle SC's refill amount `MAX_PERIOD` as a word. -/
def mpW : U64 := ⟨MAX_PERIOD⟩

/-- **The memory image** (module docstring), by byte address. -/
def img (a : Nat) : U64 :=
  if a = 18446744071562133504 then 1#u64 else
  if a = 18446744071562133520 then 15#u64 else
  if a = 18446744071562133552 then kRootV else
  if a = 18446744071562133576 then 2#u64 else
  if a = 18446744071562133704 then 72057594037927935#u64 else
  if a = 18446744071562147072 then 18446744071562072064#u64 else
  if a = 18446744071562147080 then 18446744071562072064#u64 else
  if a = 18446744071562147096 then 18446744071562096640#u64 else
  if a = 18446744071562147104 then 18446744071562096640#u64 else
  if a = 18446744071562075392 then 7#u64 else
  if a = 18446744071562075528 then 18446744071562096640#u64 else
  if a = 18446744071562096664 then 18446744071562072064#u64 else
  if a = 18446744071562096712 then 2#u64 else
  if a = 18446744071562096728 then 1#u64 else
  if a = 18446744071562096744 then mpW else
  if a = 18446744071562096752 then mpW else 0#u64

/-- **The witness's FL4 store state**: the image, base `fkb`, CPU 0. -/
def w0 : WSt := { w := fun i => img (8 * i.val), kb := fkb, cpu := 0#u64 }

theorem mem_w0 (a : U64) : wL.mem w0 a = img (8 * (a.val / 8)) := rfl

theorem mem_al {a : U64} {n : Nat} (h : a.val = n) (h8 : n % 8 = 0) : wL.mem w0 a = img n := by
  rw [mem_w0, h]; congr 1; omega

theorem ksb_w0 : wL.ksb w0 = fkb := rfl
theorem cpu_w0 : wL.cpu w0 = 0#u64 := rfl

/-- `img` away from the image's nonzero words. -/
theorem img_zero {a : Nat}
    (h1 : a ≠ 18446744071562133504)
    (h2 : a ≠ 18446744071562133520)
    (h3 : a ≠ 18446744071562133552)
    (h4 : a ≠ 18446744071562133576)
    (h5 : a ≠ 18446744071562133704)
    (h6 : a ≠ 18446744071562147072)
    (h7 : a ≠ 18446744071562147080)
    (h8 : a ≠ 18446744071562147096)
    (h9 : a ≠ 18446744071562147104)
    (h10 : a ≠ 18446744071562075392)
    (h11 : a ≠ 18446744071562075528)
    (h12 : a ≠ 18446744071562096664)
    (h13 : a ≠ 18446744071562096712)
    (h14 : a ≠ 18446744071562096728)
    (h15 : a ≠ 18446744071562096744)
    (h16 : a ≠ 18446744071562096752) :
    img a = 0#u64 := by
  unfold img; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12, if_neg h13, if_neg h14, if_neg h15, if_neg h16]

/-- `img` away from the image's nonzero words, the side conditions by `omega`. -/
macro "img0" : tactic => `(tactic| (apply img_zero <;> omega))

/-! ## The interrupt, IO-port and kernel-root words -/

theorem fkb_lt : fkb.val + 13568 ≤ 2 ^ 64 := by rw [fkb_val]; decide

/-- **`IrqRel` at the witness** (the states: zero words ↔ every IRQ inactive; the node: `fInitASt_irqNode`). -/
theorem w0_irqRel : IrqRel (wL.mem w0) (wL.ksb w0) fInitASt := by
  refine ⟨fun i hi => ?_, fun i hi => fInitASt_irqNode i hi⟩
  have hv := irqStA_val (kb := fkb) fkb_lt hi
  rw [fkb_val] at hv
  rw [ksb_w0, mem_al hv (by omega), show img (18446744071562133504 + 224 + 8 * i.val) = 0#u64 by img0]
  simp [irqSt, fInitASt, initASt]

/-- **`IoRel` at the witness** (a zero bitmap, no allocated port). -/
theorem w0_ioRel : IoRel (wL.mem w0) (wL.ksb w0) fInitASt := by
  intro p hp
  have hw : (wI p).val < 1024 := by rw [wI_val hp]; omega
  have hv := ioA_val (kb := fkb) fkb_lt hw
  rw [fkb_val] at hv
  unfold bitOf
  rw [ksb_w0, mem_al hv (by omega), show img (18446744071562133504 + 5344 + 8 * (wI p).val) = 0#u64 by img0]
  simp [fInitASt, initASt, initArchState]

/-- **`KRootRel` at the witness** (`KRootW`: the root word is the global PML4; `HugeRel`: `FEATURES` = 2). -/
theorem w0_kRootRel : KRootRel (wL.mem w0) (wL.ksb w0) fInitASt := by
  refine ⟨?_, ?_⟩
  · unfold KRootW
    have hv : (core.num.U64.wrapping_add fkb layout.ks.KERNEL_ROOT).val = 18446744071562133552 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, fkb_val]
    rw [ksb_w0, mem_al hv (by omega), show img 18446744071562133552 = kRootV by decide]
    unfold globCr3
    show makeCr3 (addrFromPPtr kRootV.bv) 0 = makeCr3 (addrFromKPPtr initGlobalPml4) 0
    decide
  · unfold HugeRel
    have hv : (core.num.U64.wrapping_add fkb layout.ks.FEATURES).val = 18446744071562133576 := by
      unfold layout.ks.FEATURES
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, fkb_val]
    rw [ksb_w0, mem_al hv (by omega), show img 18446744071562133576 = 2#u64 by decide]
    unfold layout.ks.FEATURE_HUGE_PAGES
    decide

/-- **`DomRel` at the witness** (the schedule `[(0, -1), (0, 0)]`, start index 0). -/
theorem w0_domRel : DomRel (wL.mem w0) (wL.ksb w0) fInitASt := by
  have ent : ∀ i : U64, i.val < 2 → (ksW fkb (entOff i)).val = 18446744071562133504 + 192 + 16 * i.val := by
    intro i hi
    unfold ksW entOff
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, fkb_val]
    omega
  have dur : ∀ i : U64, i.val < 2 → (ksW fkb (durOff i)).val = 18446744071562133504 + 200 + 16 * i.val := by
    intro i hi
    unfold ksW durOff entOff
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, fkb_val]
    omega
  have k32 : (ksW fkb 32#u64).val = 18446744071562133536 := by
    rw [ksW_val (by rw [fkb_val]; decide), fkb_val]; rfl
  have k24 : (ksW fkb 24#u64).val = 18446744071562133528 := by
    rw [ksW_val (by rw [fkb_val]; decide), fkb_val]; rfl
  have hl : fInitASt.domainList = [((0 : BitVec 8), (-1 : BitVec 56)), (0, 0)] := rfl
  refine ⟨rfl, fun i hi => ?_, ?_, ?_⟩
  · rw [ksb_w0, mem_al (ent i hi) (by omega), mem_al (dur i hi) (by omega), hl]
    have h01 : i.val = 0 ∨ i.val = 1 := by omega
    rcases h01 with h0 | h1
    · rw [h0, show img (18446744071562133504 + 192 + 16 * 0) = 0#u64 by decide,
        show img (18446744071562133504 + 200 + 16 * 0) = 72057594037927935#u64 by decide]
      exact ⟨rfl, by decide, by decide, by decide⟩
    · rw [h1, show img (18446744071562133504 + 192 + 16 * 1) = 0#u64 by decide,
        show img (18446744071562133504 + 200 + 16 * 1) = 0#u64 by decide]
      exact ⟨rfl, by decide, by decide, fun _ => rfl⟩
  · rw [ksb_w0, mem_al k32 (by omega), show img 18446744071562133536 = 0#u64 by decide]; rfl
  · rw [ksb_w0, mem_al k24 (by omega), show img 18446744071562133528 = 0#u64 by decide]

/-- **The arch relation** (`wAR` is `True`). -/
theorem w0_ar (a : MachineState) : wAR a fInitASt.archState.x64CurrentCr3 := trivial

/-! ## `JKern`'s numeric facts -/

/-- **`JKern`'s kernel-state facts at the witness** with one core (`Cs = {0}`). -/
theorem w0_jkernNum :
    (wL.ksb w0).val + 13568 ≤ 2 ^ 64 ∧ (wL.ksb w0).val % 8 = 0 ∧
      (wL.ksb w0).val + 13568 + ((wL.cpu w0).val + 1) * 4288 ≤ 2 ^ 64 ∧ wL.cpu w0 ∈ ({0#u64} : Set U64) ∧
      (∀ c ∈ ({0#u64} : Set U64), c.val < 64) ∧ (0#u64 ∈ ({0#u64} : Set U64)) ∧
      ∃ n : Nat, ∀ c : U64, c ∈ ({0#u64} : Set U64) ↔ c.val < n := by
  refine ⟨fkb_lt, by rw [ksb_w0, fkb_val], by rw [ksb_w0, cpu_w0, fkb_val]; decide, rfl, ?_, rfl, 1, ?_⟩
  · intro c hc; rw [Set.mem_singleton_iff] at hc; subst hc; decide
  · intro c
    rw [Set.mem_singleton_iff]
    constructor
    · rintro rfl; decide
    · intro h; apply UScalar.eq_of_val_eq; show c.val = 0; omega

/-- **The global PML4 is page-aligned and fits** (`JKern.ga`, `JKern.gf`). -/
theorem fInit_gpm_al : fInitASt.archState.x64GlobalPml4.toNat % 4096 = 0 ∧
    fInitASt.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64 := by
  show initGlobalPml4.toNat % 4096 = 0 ∧ initGlobalPml4.toNat + 4096 ≤ 2 ^ 64
  decide

end

end Fl4Proofs.P3.JBoot
