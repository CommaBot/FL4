/-
P3x for virtualization (line virt, gen 24, item 2): **gen 23's `hns` [J] at a joint state**, derived from the
layout facts of `JAtZ` the way `JAtZ.hnd` / `JAtZ.hhv` (JExtVListSteps) are.

`hns` (VirtVCappedDel's `finW_nSl` / `delete_vcpu_vcapped`): the current core's `IPI_PENDING` / `SCHED_ACTION` node
words and the VCPU list head word (`VCPU_HEAD`, kernel-state block offset 80) lie in no slot of the typed heap
(`SlR`: no `y` with `IsSlot th y`, `y ≤ b < y + 32`).

* A slot lies inside a typed-heap object (`lay_slot_in`), which is an `H` object of the same size (`JAtZ.thH`).
* Node words: `L.nodeBase s cpu ≤ b < L.nodeBase s cpu + 4288` (`P1.nodeAt_val` at `JAtZ.nodePl`), and every `H`
  object misses the current core's node block (`JKern.hnd` with `JKern.cpuCs`).
* The head word: `(L.ksb s).val + 80` (`vHead_val` at `JKern.ksbFit`), and every typed-heap object misses the
  kernel-state block's first 256 bytes (`DomPlaced.apart`, JEntryKs' `JAtZ.domPlaced`). `JKern.hks` alone does not
  do: a CNode is an `.other` object of `H` (`JPlaced.cnode`), and `.other` objects may lie inside the block
  (`JKern.hksIn`; the IRQ node's radix-0 CNodes at `ksb + 1248 + 32 i`, IntRel's `IntLayout.node`).

* **`JAtZ.hns`**: `hns` from `JAtZ` alone (no `JVm` needed: slots belong to the typed heap only).
* `JAtZ.head_ne_act`: the list head word is not the `SCHED_ACTION` word (VirtUtInvV's `hna`).
* **`delete_vcpu_vcappedJ`**: VirtVCappedDel's `delete_vcpu_vcapped` at a joint state, its `Ly` / `Da` / `hnd` /
  `hhv` / `hns` from `JAtZ` + `JVm` (`JAtZ.jvLay`, `JAtZ.detAtB`, `JAtZ.hnd`, `JAtZ.hhv`, `JAtZ.hns`) and `hhc` from
  `JAtZ.hhc`, which keeps its one premise `hU` [J] (no IPC-buffer word is the head word; JExtVListSteps, unchanged).

Named premises: `hU` [J] (used unchanged, from `JAtZ.hhc` / `vcpu_finalise_vlJ`). No new premise; gen 23's `hns` [J]
is discharged at every `JAtZ` state. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtVCappedDel
import Fl4Proofs.P3.JEntryKs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtHns
open fl4_core Classical Fl4Proofs.P0.Consts Fl4Proofs.P3 Fl4Proofs.P3.VirtVCapped Fl4Proofs.P3.VirtVCappedDel

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **`hns` at a joint state** (module docstring). -/
theorem JAtZ.hns (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ b, (b = ipiA st s ∨ b = actA st s ∨ b = P1.vHeadA st s) → ¬ SlR Z.th b := by
  have hP : Placed Z.th := (J.jvLay (V := ∅) JVm.empty).pl
  rintro b hb ⟨y, hy, g1, g2⟩
  obtain ⟨p, k, hk, f1, f2, -, -⟩ := lay_slot_in hP hy
  obtain ⟨hk', hH, hbits⟩ := J.thH p k hk
  have hN := J.nodePl
  rcases hb with rfl | rfl | rfl
  · have e := P1.nodeAt_val hN (off := layout.node.IPI_PENDING) (by simp [layout.node.IPI_PENDING])
    have h4 : layout.node.IPI_PENDING.val < 4288 := by simp [layout.node.IPI_PENDING]
    have ev : (ipiA st s).val = L.nodeBase s (L.cpu s) + layout.node.IPI_PENDING.val := by unfold ipiA; rw [e]
    rcases J.kern.hnd p hk' hH (L.cpu s) J.kern.cpuCs with e' | e' <;> (try rw [hbits] at e') <;> omega
  · have e := P1.nodeAt_val hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
    have h4 : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
    have ev : (actA st s).val = L.nodeBase s (L.cpu s) + layout.node.SCHED_ACTION.val := by unfold actA; rw [e]
    rcases J.kern.hnd p hk' hH (L.cpu s) J.kern.cpuCs with e' | e' <;> (try rw [hbits] at e') <;> omega
  · have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
    rcases J.domPlaced.apart p k hk with e' | e' <;> omega

/-- The VCPU list head word is not the current core's `SCHED_ACTION` word (VirtUtInvV's `hna` at a joint state). -/
theorem JAtZ.head_ne_act (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : P1.vHeadA st s ≠ actA st s := by
  intro e
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
  have n1 := P1.nodeAt_val J.nodePl (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
  have hnb : L.nodeBase s (L.cpu s) = (L.ksb s).val + 13568 + (L.cpu s).val * 4288 := rfl
  have n2 := congrArg UScalar.val e
  unfold actA at n2
  omega

set_option maxHeartbeats 4000000 in
/-- **`delete_vcpu_vcapped` at a joint state** (module docstring): only `hU` [J] left. -/
theorem delete_vcpu_vcappedJ {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ)
    (E : JExtV (L := L) V X Z.th s) (R : RunVmB (L := L) Z.th s) (Vl : VList st V Z.th s)
    (hU : P1.vHeadA st s ∉ BufU Z σ)
    {G : MdbGhost} (hM : MdbLinks Z.th (L.mem s) G) (hVC : VCappedM V Z.th (L.mem s))
    {a' : A} {slot v : U64} {exposed : Bool} (hx : IsSlot Z.th slot) (hc : capAt (L.mem s) slot = ok (.Vcpu v))
    {y : core.result.Result Unit error.Exc × S × A} (h : cdt.delete st ar s a' slot exposed = ok y) :
    y.1 = .Ok () ∧ ∃ V', V' ⊆ V ∧ VList st V' Z.th y.2.1 ∧ VCappedM V' Z.th (L.mem y.2.1) :=
  delete_vcpu_vcapped ar hA (J.jvLay Jv) (J.detAtB Jv) E R Vl (J.hnd Jv) (J.hhv Jv) (J.hhc Jv Vl hU) (JAtZ.hns J) hM hVC
    hx hc h

end

end
end Fl4Proofs.P3.VirtHns
