/-
P3 (p3J gen 17): **core 1's node at the 2-core boot witness** `JBootQ.M2.w0` (JBootM2Mem), what the Cs-dependent
conjuncts (`SchedQueuesInv.nodes` / `ready` / `release` / `omega`, `ScExtra`'s timer tree, `JKern.hnd`, `DbgWF`)
read at core 1.

Core 1's node lies at `fkb + 13568 + 4288` (`LawfulStore.nodeBase`, FL4's `node_base` with `node::SIZE` 4288);
its only nonzero words are `CUR_THREAD` / `IDLE_THREAD` (core 1's idle TCB `I1T`) and `CUR_SC` / `IDLE_SC` (its idle
SC `I1S`), as FL4's `create_idle_thread` (crates/fl4-core/src/boot.rs l.684-704) writes them (the witness keeps
`w0`'s convention of zero times / reprogram flag, as core 0's node). So every ready and release queue of core 1 is
empty, its timer tree and debug list are empty, and the node misses every object of `Hw` and the idle TCB.

* **`nodeAt1_v`**, **`node1W_v`**, **`node1Z`**, **`nodePlaced1`**, **`rq1_nil`**, **`l1_one`**, **`l2_one`**,
  **`rel1_nil`**, **`ready1`**, **`release1`**, **`troot1`**, **`tmin1`**, **`dbg1`**, **`memCs2`**.

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootM2Z
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBootQ.M2
open Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Classical

noncomputable section

set_option maxHeartbeats 1000000

/-- Core 1's idle TCB (`kernelBase + 0xB000`). -/
def I1T : U64 := 18446744071562113024#u64
/-- Core 1's idle SC (`kernelBase + 0xC000`, FL4's `idle_base + 4096`). -/
def I1S : U64 := 18446744071562117120#u64

theorem nodeAt1_v (o : U64) (ho : o.val < 4288) : (wL.nodeAt w0 1#u64 o).val = 18446744071562151360 + o.val := by
  unfold LawfulStore.nodeAt
  rw [ksb_w0]
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, fkb_val]
  omega

/-- A node word of core 1, by offset. -/
theorem node1W_v (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    nodeW wst w0 1#u64 o = img (18446744071562151360 + o.val) :=
  mem_al (nodeAt1_v o ho) (by omega)

/-- A zero word of core 1's node. -/
theorem node1Z (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0) (h0 : o.val ≠ 0) (h1 : o.val ≠ 8)
    (h2 : o.val ≠ 24) (h3 : o.val ≠ 32) : wL.mem w0 (wL.nodeAt w0 1#u64 o) = 0#u64 := by
  rw [show wL.mem w0 (wL.nodeAt w0 1#u64 o) = nodeW wst w0 1#u64 o from rfl, node1W_v o ho h8]; img0

theorem nodeBase1 : wL.nodeBase w0 1#u64 = 18446744071562151360 := by
  simp [LawfulStore.nodeBase, ksb_w0, fkb_val]

theorem nodePlaced1 : NodePlaced wst T0 w0 1#u64 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [LawfulStore.nodeBase, ksb_w0, fkb_val]
  · simp [LawfulStore.nodeBase, ksb_w0, fkb_val]
  · intro t ht; rw [T0, Set.mem_singleton_iff] at ht; subst ht
    left; simp [LawfulStore.nodeBase, ksb_w0, fkb_val, idT_val]

theorem rq1_nil (p : U64) (hp : p.val < 256) : wL.rqQ w0 1#u64 p = ⟨0#u64, 0#u64⟩ := by
  unfold LawfulStore.rqQ
  have h1 : (rqOff p).val = 168 + 16 * p.val := by simp [rqOff]; omega
  have h2 : (rqTailOff p).val = 176 + 16 * p.val := by simp [rqTailOff]; omega
  rw [mem_al (nodeAt1_v _ (by omega)) (by omega), mem_al (nodeAt1_v _ (by omega)) (by omega), h1, h2]
  congr 1 <;> img0

theorem l1_one : wL.l1W w0 1#u64 = 0#u64 := by
  unfold LawfulStore.l1W
  have h1 : (l1Off).val = 128 := by simp [l1Off]
  rw [mem_al (nodeAt1_v _ (by omega)) (by omega), h1]; img0

theorem l2_one (g : Nat) (hg : g < 4) : wL.l2W w0 1#u64 g = 0#u64 := by
  unfold LawfulStore.l2W
  have h1 : (l2Off g).val = 136 + 8 * (3 - g) := by simp [l2Off]; omega
  rw [mem_al (nodeAt1_v _ (by omega)) (by omega), h1]; img0

theorem rel1_nil : wL.relQ w0 1#u64 = ⟨0#u64, 0#u64⟩ := by
  unfold LawfulStore.relQ
  have h1 : (layout.node.RELEASE_HEAD).val = 64 := by unfold layout.node.RELEASE_HEAD; rfl
  have h2 : (core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64).val = 72 := by
    unfold layout.node.RELEASE_HEAD; rfl
  rw [mem_al (nodeAt1_v _ (by omega)) (by omega), mem_al (nodeAt1_v _ (by omega)) (by omega), h1, h2]
  congr 1 <;> img0

/-- **Core 1's ready queues are empty.** -/
theorem ready1 : ReadyQueues wst T0 w0 1#u64 (fun _ => []) :=
  ⟨⟨fun p hp => by rw [rq1_nil p hp]; exact QueueRel.nil, fun _ _ _ _ _ x hx => (List.not_mem_nil hx).elim⟩,
    ⟨fun p hp => by
      rw [l2_one _ (by omega)]
      simp,
    fun i hi => by
      rw [l1_one]
      simp only [show (0#u64).bv.getLsbD i = false by simp, Bool.false_eq_true, false_iff, not_and, not_not]
      intro h; rw [l2_one i h]⟩⟩

/-- **Core 1's release queue is empty.** -/
theorem release1 : QueueRel (wL.mem w0) T0 .Sched (wL.relQ w0 1#u64) [] := by
  rw [rel1_nil]; exact QueueRel.nil

theorem troot1 : wL.mem w0 (wL.nodeAt w0 1#u64 layout.node.TIMER_ROOT) = 0#u64 := by
  unfold layout.node.TIMER_ROOT
  exact node1Z _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem tmin1 : wL.mem w0 (wL.nodeAt w0 1#u64 layout.node.TIMER_MIN) = 0#u64 := by
  unfold layout.node.TIMER_MIN
  exact node1Z _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem dbg1 : wL.mem w0 (wL.nodeAt w0 1#u64 layout.node.DEBUG_TCBS) = 0#u64 := by
  unfold layout.node.DEBUG_TCBS
  exact node1Z _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Core 1's `IDLE_THREAD` / `IDLE_SC` / `CUR_THREAD` / `CUR_SC` words. -/
theorem idle1_w : wL.mem w0 (wL.nodeAt w0 1#u64 layout.node.IDLE_THREAD) = I1T ∧
    wL.mem w0 (wL.nodeAt w0 1#u64 layout.node.IDLE_SC) = I1S ∧
    wL.mem w0 (wL.nodeAt w0 1#u64 layout.node.CUR_THREAD) = I1T ∧
    wL.mem w0 (wL.nodeAt w0 1#u64 layout.node.CUR_SC) = I1S := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show wL.mem w0 (wL.nodeAt w0 1#u64 _) = nodeW wst w0 1#u64 _ from rfl,
      show layout.node.IDLE_THREAD = 8#u64 by unfold layout.node.IDLE_THREAD; rfl, node1W_v _ (by decide) (by decide)]
    decide
  · rw [show wL.mem w0 (wL.nodeAt w0 1#u64 _) = nodeW wst w0 1#u64 _ from rfl,
      show layout.node.IDLE_SC = 32#u64 by unfold layout.node.IDLE_SC; rfl, node1W_v _ (by decide) (by decide)]
    decide
  · rw [show wL.mem w0 (wL.nodeAt w0 1#u64 _) = nodeW wst w0 1#u64 _ from rfl,
      show layout.node.CUR_THREAD = 0#u64 by unfold layout.node.CUR_THREAD; rfl, node1W_v _ (by decide) (by decide)]
    decide
  · rw [show wL.mem w0 (wL.nodeAt w0 1#u64 _) = nodeW wst w0 1#u64 _ from rfl,
      show layout.node.CUR_SC = 24#u64 by unfold layout.node.CUR_SC; rfl, node1W_v _ (by decide) (by decide)]
    decide

theorem memCs2 {c : U64} (h : c ∈ Csw) : c = 0#u64 ∨ c = 1#u64 := h

end

end Fl4Proofs.P3.JBootQ.M2
