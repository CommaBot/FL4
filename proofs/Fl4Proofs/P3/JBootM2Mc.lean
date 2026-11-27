/-
P3 (p3J gen 17): **a 2-core boot witness of the multicore joint predicate `JAtMc`** (P3JMc).

At the 2-core image `JBootQ.M2.w0` (JBootM2Mem: FL4's boot IRQ layout, `NUM_NODES` 2, core 0 current; core 1's node
with `CUR_THREAD` = `IDLE_THREAD` = `I1T`, `CUR_SC` = `IDLE_SC` = `I1S`; core 1's idle TCB `I1T` = `kernelBase + 0xB000`
in `TS_IDLE`, affinity 1, SC `I1S`; its idle SC `I1S` = `kernelBase + 0xC000`, core 1, TCB `I1T`, the idle SC's refills,
as FL4's `create_idle_thread` writes them, crates/fl4-core/src/boot.rs l.684-704) with the spec boot state
`JBootQ.fInitASt` and the ghosts of JBootM2Z (cores `Csw = {0, 1}`):

* **`jAtZ_w0`** (JBootM2JAt, the generated copy): `JAtZ` with `Cs = {0, 1}`;
* **`foreignIdle_w0`**: core 1's idle objects are outside the projection (`ForeignIdle … 1`);
* **`jAtMc_w2`** / **`jAtMc_w2I1`**: `JAtMc` at the 2-core witness, for every arch state (`warI` / `warI1`);
* **`jReachU40_w0I1`** (JBootM2U40, the generated copy): U40's start at the 2-core witness;
* **`runMc_w2`**: the multicore run predicate `RunMc` (P3JMcRun) at the 2-core witness.

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootM2U40
import Fl4Proofs.P3.P3JMcRun
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBootQ.M2
open Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Fl4Proofs.P3.Mc

noncomputable section

set_option maxHeartbeats 1000000

theorem i1t_val : I1T.val = 18446744071562113024 := rfl
theorem i1s_val : I1S.val = 18446744071562117120 := rfl

theorem idleOf1 : idleOf (L := wL) w0 1#u64 = I1T := idle1_w.1
theorem idleScOf1 : idleScOf (L := wL) w0 1#u64 = I1S := idle1_w.2.1

/-- A word of core 1's idle TCB, by offset. -/
theorem i1tW (K : U64) (hK : K.val < 4096) (h8 : K.val % 8 = 0) :
    wL.mem w0 (core.num.U64.wrapping_add I1T K) = img (18446744071562113024 + K.val) :=
  mem_al (by rw [wa_val (by rw [i1t_val]; omega), i1t_val]) (by omega)

/-- A word of core 1's idle SC, by offset. -/
theorem i1sW (K : U64) (hK : K.val < 128) (h8 : K.val % 8 = 0) :
    wL.mem w0 (core.num.U64.wrapping_add I1S K) = img (18446744071562117120 + K.val) :=
  mem_al (by rw [wa_val (by rw [i1s_val]; omega), i1s_val]) (by omega)

/-- No object of the spec boot heap at `o` off the idle TCB / SC, the global tables and the IRQ node. -/
theorem fInitKheap_none {o : ObjRef} (h1 : o ≠ idleThreadPtr) (h2 : o ≠ idleScPtr) (h3 : o ≠ initGlobalPml4)
    (h4 : o ≠ initGlobalPdpt) (h5 : o ≠ initGlobalPd) (h6 : ∀ irq : Irq, fIrqNode irq ≠ o) : fInitKheap o = none := by
  unfold fInitKheap
  simp only [Function.update_apply, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
  rw [if_neg (by rintro ⟨irq, e⟩; exact h6 irq e)]

/-- The IRQ node misses `[lo, lo + n)` when that range lies between the high IRQ CNodes and the block. -/
theorem fIrqNode_ne {o : ObjRef} (h1 : 18446744071562084352 ≤ o.toNat) (h2 : o.toNat < 18446744071562134752)
    (irq : Irq) : fIrqNode irq ≠ o := by
  intro e
  have := irq.isLt
  rcases fIrqNode_cases irq with ⟨_, h⟩ | ⟨_, h3, h⟩ <;> rw [e] at h <;> omega

theorem fInit_I1T : fInitASt.kheap I1T.bv = none :=
  show fInitKheap I1T.bv = none from fInitKheap_none (o := I1T.bv) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fIrqNode_ne (o := I1T.bv) (by decide) (by decide))
theorem fInit_I1S : fInitASt.kheap I1S.bv = none :=
  show fInitKheap I1S.bv = none from fInitKheap_none (o := I1S.bv) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fIrqNode_ne (o := I1S.bv) (by decide) (by decide))

/-- **Core 1's idle objects outside the 2-core witness's projection.** -/
theorem foreignIdle_w0 : ForeignIdle (L := wL) Zw Hw Csw w0 fInitASt 1#u64 where
  tSt := by
    rw [idleOf1]; unfold P1.stA layout.tcb.STATE layout.tcb.F; rw [i1tW _ (by decide) (by decide)]; decide
  tAff := by rw [idleOf1]; unfold affA; rw [i1tW _ (by decide) (by decide)]; decide
  tSc := by rw [idleOf1, idleScOf1]; unfold scA; rw [i1tW _ (by decide) (by decide)]; decide
  sTcb := by
    rw [idleOf1, idleScOf1]; unfold scTcbA layout.sc.TCB; rw [i1sW _ (by decide) (by decide)]; decide
  sCore := by rw [idleScOf1]; unfold scCoreA layout.sc.CORE; rw [i1sW _ (by decide) (by decide)]; decide
  tH p k hp := by
    rw [idleOf1, i1t_val]; unfold Apart
    hwc hp <;> simp only [HKind.bits, Nat.reducePow] <;> omega
  sH p k hp := by
    rw [idleScOf1, i1s_val]; unfold Apart
    hwc hp <;> simp only [HKind.bits, Nat.reducePow] <;> omega
  tTh q k hq := by
    rw [idleOf1, i1t_val]; unfold Apart
    thc hq <;> simp only [objSize, Nat.pow_zero, Nat.mul_one] <;> omega
  sTh q k hq := by
    rw [idleScOf1, i1s_val]; unfold Apart
    thc hq <;> simp only [objSize, Nat.pow_zero, Nat.mul_one] <;> omega
  tT := by rw [idleOf1]; intro h; have h' : I1T = idT := h; exact absurd h' (by decide)
  sC := by rw [idleScOf1]; intro h; have h' : I1S = idS := h; exact absurd h' (by decide)
  tK := by rw [idleOf1]; exact fInit_I1T
  sK := by rw [idleScOf1]; exact fInit_I1S
  tKs := by rw [idleOf1, i1t_val, ksb_w0, fkb_val]; unfold Apart; omega
  sKs := by rw [idleScOf1, i1s_val, ksb_w0, fkb_val]; unfold Apart; omega
  tN c hc := by
    rw [idleOf1, i1t_val]; unfold Apart
    rcases memCs2 hc with rfl | rfl <;> (first | rw [nodeBase_w0] | rw [nodeBase1]) <;> omega
  sN c hc := by
    rw [idleScOf1, i1s_val]; unfold Apart
    rcases memCs2 hc with rfl | rfl <;> (first | rw [nodeBase_w0] | rw [nodeBase1]) <;> omega
  ut x hx := by simp [Zw, Gw] at hx

/-- **`JAtMc` at the 2-core boot witness** (module docstring). -/
theorem jAtMc_w2 (a : MachineState) : JAtMc (L := wL) warI wAR w0 a fInitASt :=
  ⟨Zw, Hw, Csw, C0, fun _ => [], Dw, jAtZ_w0 a, Zw_vx, fun c hc hne => by
    rcases memCs2 hc with rfl | rfl
    · exact absurd cpu_w0.symm hne
    · exact foreignIdle_w0⟩

/-- **`JAtMc` at the 2-core witness, model arch `warI1`** (FL4's boot IRQ layout, `JBootM2U40`). -/
theorem jAtMc_w2I1 (a : MachineState) : JAtMc (L := wL) warI1 wAR w0 a fInitASt :=
  ⟨Zw, Hw, Csw, C0, fun _ => [], Dw, jAtZ_w0I1 a, Zw_vx, fun c hc hne => by
    rcases memCs2 hc with rfl | rfl
    · exact absurd cpu_w0.symm hne
    · exact foreignIdle_w0⟩

/-- **`CKI` at the spec boot state** (a boot state holds only null caps, `BootHeap.capOpt`). -/
theorem cki_fInit : SInvCk.CKI fInitASt := by
  intro p cref c hc
  have e : c = .nullCap := bootHeap_fInit.capOpt (N := fIrqNode) hc
  subst e
  first | trivial | simp [SInvCk.KW]

/-- **The multicore run predicate at the 2-core boot witness** (`RunMc`, P3JMcRun): U40's start
(`jReachU40_w0I1`, the 2-core copy), the cap-kind invariant (the boot heap holds only null caps) and `JAtMc`. -/
theorem runMc_w2 : RunMc (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨⟨jReachU40_w0I1, cki_fInit⟩, jAtMc_w2I1 _⟩

end

end Fl4Proofs.P3.JBootQ.M2
