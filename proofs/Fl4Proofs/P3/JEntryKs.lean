/-
P3 (DESIGN.md §9): **the kernel-global placement facts of the invocation
entry from `JAtZ`** (XTopJointEntry's former `JEntryAt` fields `cw`, `act2`,
`act3`, `actK`, `ksO`, `domPl`, all [J] premises before).

* `JAtZ.th_node`: an object of the typed heap misses the current core's node
  (TCBs and CNodes are `H` objects, `JPlaced.tcb`/`cnode`, `JKern.hnd`).
* `JAtZ.th_dom`: an object of the typed heap misses the domain schedule (the
  first 256 bytes of the kernel-state block): a TCB by `JKern.hks`, a CNode
  because a slot of it would lie in the block below the IRQ node
  (`IpcApart.ks`).
* `JAtZ.cwOut` (`hcw`), `JAtZ.act2`/`act3`/`actK` (the scheduler-action
  word apart from the IRQ states, the IO bitmap and the domain schedule:
  arithmetic on the node layout), `JAtZ.ksOut` (`hksO`), `JAtZ.domPlaced`
  (`DomPlaced`).
-/
import Fl4Proofs.P3.JointAt
import Fl4Proofs.P3.DomKeep
import Fl4Proofs.P3.DomDecode
import Fl4Proofs.P3.IoBitmap
import Fl4Proofs.P3.IntRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

namespace JAtZ

/-- A word of the current core's node. -/
theorem nodeAt_cur_val (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {off : U64} (ho : off.val < 4288) :
    (L.nodeAt s (L.cpu s) off).val = (L.ksb s).val + 13568 + (L.cpu s).val * 4288 + off.val :=
  Sched.nodeAt_val' J.kern.nodeFit ho

/-- **An object of the typed heap misses the current core's node.** -/
theorem th_node (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} {k : ObjKind}
    (hp : Z.th p = some k) :
    p.val + objSize k ≤ L.nodeBase s (L.cpu s) ∨ L.nodeBase s (L.cpu s) + 4288 ≤ p.val := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  rcases J.thk p k hp with rfl | ⟨r, rfl⟩
  · have h := J.kern.hnd p .tcb ((hJ.tcb p).1 hp) (L.cpu s) J.kern.cpuCs
    simp only [P1.HKind.bits] at h
    simp only [objSize]
    omega
  · have h := J.kern.hnd p _ (hJ.cnode p r hp) (L.cpu s) J.kern.cpuCs
    have e : (2 : Nat) ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; ring
    simp only [P1.HKind.bits, e] at h
    simp only [objSize]
    omega

/-- **An object of the typed heap misses the domain schedule** (the first
256 bytes of the kernel-state block). -/
theorem th_dom (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} {k : ObjKind}
    (hp : Z.th p = some k) :
    p.val + objSize k ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ p.val := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hP : Placed Z.th := J.xtop.rel.1
  have hIA := J.xtop.rel.2.2.2.2.2.1
  rcases J.thk p k hp with rfl | ⟨r, rfl⟩
  · have h := J.kern.hks p .tcb ((hJ.tcb p).1 hp) (fun z h => by cases h)
    simp only [P1.HKind.bits] at h
    simp only [objSize]
    omega
  · by_contra hc
    simp only [objSize, not_or, not_le] at hc
    obtain ⟨h1, h2⟩ := hc
    have hf := J.kern.ksbFit
    by_cases hle : p.val ≤ (L.ksb s).val
    · have hi : ((L.ksb s).val - p.val) / 32 < 2 ^ r := by omega
      have hAt : IsSlotAt Z.th p (((L.ksb s).val - p.val) / 32) := Or.inl ⟨r, hp, hi⟩
      have hv := hAt.val hP
      exact hIA.ks (L.ksb s) le_rfl (by omega) (Or.inl (by omega)) _ ⟨p, _, hAt, rfl⟩
        ⟨by omega, by omega⟩
    · have hAt : IsSlotAt Z.th p 0 := Or.inl ⟨r, hp, by positivity⟩
      have hv := hAt.val hP
      exact hIA.ks (slotOf p 0) (by omega) (by omega) (Or.inl (by omega)) _ ⟨p, _, hAt, rfl⟩
        ⟨le_rfl, by omega⟩

/-- **The current-thread word outside the objects** (the Thread decode's
`hcw`). -/
theorem cwOut (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) := by
  have h0 : layout.node.CUR_THREAD.val = 0 := P1.curth0
  have hv := J.nodeAt_cur_val (off := layout.node.CUR_THREAD) (by omega)
  have hal := J.kern.ksbAl
  refine ⟨?_, fun p k hp => ?_⟩
  · show (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD).val % 8 = 0
    rw [hv, h0]; omega
  · have h := J.th_node hp
    unfold P1.LawfulStore.nodeBase at h
    omega

theorem act_cur_val (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val = (L.ksb s).val + 13568 + (L.cpu s).val * 4288 + 16 := by
  have h0 : layout.node.SCHED_ACTION.val = 16 := P1.act_val
  rw [J.nodeAt_cur_val (by omega), h0]

/-- **The scheduler-action word is no IRQ state word** (the IRQ control
decode's `hact2`). -/
theorem act2 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i := by
  intro i hi e
  have h := congrArg (fun x : U64 => x.val) e
  rw [J.act_cur_val, irqStA_val J.kern.ksbFit hi] at h
  omega

/-- **The scheduler-action word is no IO bitmap word** (the IO port control
decode's `hact3`). -/
theorem act3 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w := by
  intro w hw e
  have h := congrArg (fun x : U64 => x.val) e
  rw [J.act_cur_val, ioA_val J.kern.ksbFit hw] at h
  omega

/-- **The scheduler-action word is no domain schedule word** (the domain
decode's `hactK`). -/
theorem actK (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val := by
  intro o ho h
  have hf := J.kern.ksbFit
  rw [J.act_cur_val, ksW_val (by omega)] at h
  omega

/-- **The domain schedule's words outside the objects** (the domain decode's
`hksO`). -/
theorem ksOut (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects Z.th (ksW (L.ksb s) o) := by
  intro o ho h8
  have hf := J.kern.ksbFit
  have hal := J.kern.ksbAl
  have hv : (ksW (L.ksb s) o).val = (L.ksb s).val + o.val := ksW_val (by omega)
  refine ⟨?_, fun p k hp => ?_⟩
  · show (ksW (L.ksb s) o).val % 8 = 0
    rw [hv]; omega
  · have h := J.th_dom hp
    rw [hv]; omega

/-- **`DomPlaced` from `JAtZ`** (the IRQ handler decode's `hD`). -/
theorem domPlaced (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : DomPlaced (L := L) Z.th s :=
  ⟨J.kern.ksbFit, J.kern.ksbAl, fun _ _ hp => J.th_dom hp, Or.inr (by rw [J.act_cur_val]; omega),
    J.kern.act.1⟩

end JAtZ

end

end

end Fl4Proofs.P3
