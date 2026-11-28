/-
P3 (line mmuAD, gen 42b25): **what the VT-x records need of a retype's write footprint** — the Architect's ruling
(2026-11-28 18:08Z) item 1: `RetWin` (UtScRet) is parametrised over the body's footprint `W`; each consumer states what
it needs of `W` once, and each footprint discharges it.

* **`RetFootV V th s W`** (`VcpuCore`, for `VcpuCore.ofRet`): every word of `W` misses each VCPU object of `V`
  (`[v, v + 32768)`: its `TCB` word `vTcbA`, the list links, the words `VRel` reads), the VCPU list head `vHeadA`, and
  each TCB's `VCPU` word (`tVcpuA`, x86_64/layout.rs l. 71; the x86_64 TCB has no `RUN_VCPU` field) and state word
  (`stA`, which `RunVmB` reads). The slot caps come from `RetWin` itself.
* **`RetFootE X W`** (`EptCore`, for `EptCore.growSZ`'s `hW`): every word of `W` misses each table of `X`. `EptCore`
  reads no FL4 word of the ASID table: the pools are the spec's (`σ.archState.x64AsidTable`, `GuestEntry`), kept by
  the retype's `SpecAdd` / `CnK`.
* Discharged for the footprints of the bodies: `Sched.SlotWd th` (**`JAtZB.retFootV_slot`**, **`retFootE_slot`**: a
  slot lies in its CNode / TCB, EptDelRoot's `slotWd_vcpu` / `slotWd_head` / `slotWd_tcb` / `slotWd_ept`), the window
  `WinWd lo hi` inside the free part of a RAM untyped cap of an `AbsSlot` (**`retFootV_win`**, **`retFootE_win`**: no
  spec object there, `SpecFree`, the VCPUs 2^15 and the tables 2^12 bytes; no typed-heap object, `UtCapP3.free`; the
  kernel-state block outside, `UtKsApart`), the debug-list words `DebugWd s` (**`retFootV_dbg`**,
  **`retFootE_dbg`**: core 0's `DEBUG_TCBS` node word, off the VCPUs and tables by `JVm.ks` / `EptCore.ks`, off
  every TCB by `JKern.hnd`; the old head's `DEBUG_PREV` at offset 3584 of a TCB of `H`, apart from the VCPUs by
  `JVLay.vap`, from the tables by `HeapOK.disj` (`JAtZB.eptHeap`), from the other TCBs' words by `HeapOK.disj`);
  **`retFootV_W`** / **`retFootE_W`** (`RetWdW`, PML4) and **`retFootV_T`** / **`retFootE_T`** (`RetWdT`, TCB) by
  union.
* For the later VCPU body (type 14): its footprint `CrL V B n hd` (P3/VirtLoopSharp: the window, the list head, an old
  VCPU's `PREV` word) with the window in a RAM untyped's free part and `hd` the list head satisfies `RetFootE`
  (**`JAtZB.retFootE_crl`**: the tables are off the kernel-state area, `EptCore.ks`, and apart from the VCPUs,
  `EptCore.apartV`).

No named premise. No `sorry`; only the three standard axioms.
-/
import Fl4Proofs.P3.EptDelRoot
import Fl4Proofs.P3.EptRetype
import Fl4Proofs.P3.VirtLoopSharp
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **What `VcpuCore` needs of a retype's footprint `W`** (module docstring). -/
def RetFootV (V : Set U64) (th : TypedHeap) (s : S) (W : U64 → Prop) : Prop :=
  ∀ b, W b → (∀ v ∈ V, b.val < v.val ∨ v.val + 32768 ≤ b.val) ∧ b ≠ P1.vHeadA st s ∧
    ∀ t, th t = some .tcb → b ≠ tVcpuA t ∧ b ≠ P1.stA t

/-- **What `EptCore` needs of a retype's footprint `W`** (module docstring). -/
def RetFootE (X : Set U64) (W : U64 → Prop) : Prop :=
  ∀ b, W b → ∀ u ∈ X, b.val < u.val ∨ u.val + 4096 ≤ b.val

theorem RetFootV.union {V : Set U64} {th : TypedHeap} {s : S} {W1 W2 : U64 → Prop}
    (h1 : RetFootV (L := L) V th s W1) (h2 : RetFootV (L := L) V th s W2) :
    RetFootV (L := L) V th s (fun b => W1 b ∨ W2 b) :=
  fun b hb => hb.elim (h1 b) (h2 b)

theorem RetFootE.union {X : Set U64} {W1 W2 : U64 → Prop} (h1 : RetFootE X W1) (h2 : RetFootE X W2) :
    RetFootE X (fun b => W1 b ∨ W2 b) :=
  fun b hb => hb.elim (h1 b) (h2 b)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- A TCB's `VCPU` and state words. -/
theorem JAtZB.tcbVS (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : Z.th t = some .tcb) :
    (tVcpuA t).val = t.val + 3664 ∧ (P1.stA t).val = t.val + 3328 :=
  ⟨Sched.tVcpuA_val B.ip.e.tcb (B.thT t ht), by
    rw [Sched.stA_tStA]; exact Sched.tStA_val' (B.ip.e.tcb t (B.thT t ht))⟩

/-- **The slot words** satisfy `RetFootV`. -/
theorem JAtZB.retFootV_slot (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ) :
    RetFootV (L := L) V Z.th s (SlotWd Z.th) := by
  intro b hb
  refine ⟨B.slotWd_vcpu C.vm hb, B.slotWd_head hb, fun t ht => ?_⟩
  obtain ⟨e1, e2⟩ := B.tcbVS ht
  exact ⟨B.slotWd_tcb hb ht (by rw [e1]; omega) (by rw [e1]; omega),
    B.slotWd_tcb hb ht (by rw [e2]; omega) (by rw [e2]; omega)⟩

/-- **The slot words** satisfy `RetFootE`. -/
theorem JAtZB.retFootE_slot (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (C : EptCore (L := L) X XL Z.th s σ) : RetFootE X (SlotWd Z.th) :=
  B.slotWd_ept C

/-- The window inside the free part of a RAM untyped cap of an `AbsSlot` misses every spec object, every typed-heap
object and the kernel-state block. -/
theorem JAtZB.winFree (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    {lo hi : Nat} (h1 : p.val + fi.val ≤ lo) (h2 : hi ≤ p.val + 2 ^ sb.val) :
    (∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat) ∧
    (∀ q kd, Z.th q = some kd → q.val + objSize kd ≤ lo ∨ hi ≤ q.val) ∧
    (hi ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ lo) := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := B.xtop.rel
  have hxG : cslotAddr sl ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  have hU := B.utc _ p sb fi false hAs hcap rfl
  obtain ⟨k1, -, -⟩ := B.jcov.ks _ hxG p sb fi (capV_of_capAt hcap)
  have hfl := hU.fiLe
  refine ⟨fun o ko hk => ?_, fun q kd hq => ?_, ?_⟩
  · rcases B.sfree _ hxG p sb fi (capV_of_capAt hcap) o ko hk with h | ⟨-, h⟩ <;> omega
  · rcases hU.free q kd hq with h | h <;> omega
  · omega

/-- **The window** satisfies `RetFootV`. -/
theorem JAtZB.retFootV_win (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ)
    {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    {lo hi : Nat} (h1 : p.val + fi.val ≤ lo) (h2 : hi ≤ p.val + 2 ^ sb.val) :
    RetFootV (L := L) V Z.th s (WinWd lo hi) := by
  obtain ⟨hσ, hth, hk⟩ := B.winFree hAs hcap h1 h2
  intro b ⟨g1, g2⟩
  refine ⟨fun v hv => ?_, fun e => ?_, fun t ht => ?_⟩
  · obtain ⟨x, hx⟩ := C.vm.spec v hv
    have h := hσ _ _ hx
    have e : (2 : Nat) ^ Fl4Spec.objBits (.archObj (.vcpu x)) = 32768 := by
      simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]
    have hv' : v.bv.toNat = v.val := rfl
    rw [e, hv'] at h
    omega
  · have hh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val B.kern.ksbFit
    rw [← e] at hh
    omega
  · have hf := hth t .tcb ht
    have e4 : objSize ObjKind.tcb = 4096 := rfl
    rw [e4] at hf
    obtain ⟨e1, e2⟩ := B.tcbVS ht
    exact ⟨fun e => by rw [← e] at e1; omega, fun e => by rw [← e] at e2; omega⟩

/-- **The window** satisfies `RetFootE`. -/
theorem JAtZB.retFootE_win (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    {lo hi : Nat} (h1 : p.val + fi.val ≤ lo) (h2 : hi ≤ p.val + 2 ^ sb.val) :
    RetFootE X (WinWd lo hi) := by
  obtain ⟨hσ, -, -⟩ := B.winFree hAs hcap h1 h2
  intro b ⟨g1, g2⟩ u hu
  obtain ⟨es, hk, -⟩ := C.rel.obj u hu
  have h := hσ _ _ hk
  have e : (2 : Nat) ^ Fl4Spec.objBits (.archObj (.ept (XL u) es)) = 4096 := by rw [ept_bits]; rfl
  have hu' : u.bv.toNat = u.val := rfl
  rw [e, hu'] at h
  omega

/-- Core 0's `DEBUG_TCBS` word. -/
theorem JAtZB.dwVal (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val = (L.ksb s).val + 13568 + 88 := by
  have hkf := B.kern.nodeFit
  rw [nodeAt_val' (by simp; omega) (by simp [layout.node.DEBUG_TCBS])]
  simp [layout.node.DEBUG_TCBS]

/-- A TCB of `H` misses core 0's node. -/
theorem JAtZB.tcbNode0 (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : H t = some .tcb) :
    t.val + 4096 ≤ (L.ksb s).val + 13568 ∨ (L.ksb s).val + 13568 + 4288 ≤ t.val := by
  have hd := B.kern.hnd t _ ht 0#u64 B.kern.cs0
  simp only [P1.HKind.bits, Nat.reducePow, P1.LawfulStore.nodeBase] at hd
  simpa using hd

/-- **The debug-list words** satisfy `RetFootV`. -/
theorem JAtZB.retFootV_dbg (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ) :
    RetFootV (L := L) V Z.th s (DebugWd (L := L) s) := by
  obtain ⟨Tr, Cq, hJp⟩ := B.jpl
  have hDWv := B.dwVal
  have hh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val B.kern.ksbFit
  have tH : ∀ t, Z.th t = some .tcb → H t = some .tcb := fun t ht => (hJp.tcb t).1 ht
  intro b hb
  rcases hb with rfl | ⟨hne, rfl⟩
  · refine ⟨fun v hv => ?_, fun e => ?_, fun t ht => ?_⟩
    · rcases C.vm.ks v hv with h | h <;> omega
    · have := congrArg UScalar.val e; omega
    · have hd := B.tcbNode0 (tH t ht)
      obtain ⟨e1, e2⟩ := B.tcbVS ht
      exact ⟨fun e => by have := congrArg UScalar.val e; omega, fun e => by have := congrArg UScalar.val e; omega⟩
  · obtain ⟨hh0T, hok⟩ := B.kern.head.resolve_left hne
    have hdv := dpA_v hok
    have hd0 := B.tcbNode0 (tH _ hh0T)
    refine ⟨fun v hv => ?_, fun e => ?_, fun t ht => ?_⟩
    · have h := (B.jvLay C.vm).vap v hv _ _ hh0T
      have e4 : objSize ObjKind.tcb = 4096 := rfl
      rw [e4] at h
      omega
    · have := congrArg UScalar.val e
      rcases B.kern.hks _ .tcb (tH _ hh0T) (fun z h => by cases h) with h | h <;>
        (try simp only [P1.HKind.bits, Nat.reducePow] at h) <;> omega
    · obtain ⟨e1, e2⟩ := B.tcbVS ht
      by_cases et : t = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)
      · rw [et] at e1 e2 ⊢
        exact ⟨fun e => by have := congrArg UScalar.val e; omega, fun e => by have := congrArg UScalar.val e; omega⟩
      · rcases B.kern.heap.disj _ _ _ _ (tH t ht) (tH _ hh0T) et with h | h <;>
          simp only [P1.HKind.bits, Nat.reducePow] at h <;>
          exact ⟨fun e => by have := congrArg UScalar.val e; omega, fun e => by have := congrArg UScalar.val e; omega⟩

/-- **The debug-list words** satisfy `RetFootE`. -/
theorem JAtZB.retFootE_dbg (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ) :
    RetFootE X (DebugWd (L := L) s) := by
  obtain ⟨Tr, Cq, hJp⟩ := B.jpl
  have hDWv := B.dwVal
  intro b hb u hu
  rcases hb with rfl | ⟨hne, rfl⟩
  · rcases C.ks u hu with h | h <;> omega
  · obtain ⟨hh0T, hok⟩ := B.kern.head.resolve_left hne
    have hdv := dpA_v hok
    have hT := (hJp.tcb _).1 hh0T
    have hu12 := B.eptHeap C hu
    have hne' : u ≠ L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := fun e => by
      rw [e, hT] at hu12; cases hu12
    rcases B.kern.heap.disj _ _ _ _ hu12 hT hne' with h | h <;>
      simp only [P1.HKind.bits, Nat.reducePow] at h <;> omega

/-- **The PML4 body's footprint** (`RetWdW`: slots and the window) satisfies `RetFootV`. -/
theorem JAtZB.retFootV_W (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ)
    {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    {lo hi : Nat} (h1 : p.val + fi.val ≤ lo) (h2 : hi ≤ p.val + 2 ^ sb.val) :
    RetFootV (L := L) V Z.th s (RetWdW Z.th lo hi) :=
  (B.retFootV_slot C).union (B.retFootV_win C hAs hcap h1 h2)

/-- **The PML4 body's footprint** satisfies `RetFootE`. -/
theorem JAtZB.retFootE_W (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    {lo hi : Nat} (h1 : p.val + fi.val ≤ lo) (h2 : hi ≤ p.val + 2 ^ sb.val) :
    RetFootE X (RetWdW Z.th lo hi) :=
  (B.retFootE_slot C).union (B.retFootE_win C hAs hcap h1 h2)

/-- **The TCB body's footprint** (`RetWdT`: slots, the window, the debug-list words) satisfies `RetFootV`. -/
theorem JAtZB.retFootV_T (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ)
    {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    {lo hi : Nat} (h1 : p.val + fi.val ≤ lo) (h2 : hi ≤ p.val + 2 ^ sb.val) :
    RetFootV (L := L) V Z.th s (RetWdT (L := L) Z.th s lo hi) :=
  (B.retFootV_W C hAs hcap h1 h2).union (B.retFootV_dbg C)

/-- **The TCB body's footprint** satisfies `RetFootE`. -/
theorem JAtZB.retFootE_T (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    {lo hi : Nat} (h1 : p.val + fi.val ≤ lo) (h2 : hi ≤ p.val + 2 ^ sb.val) :
    RetFootE X (RetWdT (L := L) Z.th s lo hi) :=
  (B.retFootE_W C hAs hcap h1 h2).union (B.retFootE_dbg C)

/-- **The VCPU body's footprint** (`CrL`: the window, the list head, an old VCPU's `PREV` word; type 14, later)
satisfies `RetFootE` (with its slot words, by `RetFootE.union` with `retFootE_slot`). -/
theorem JAtZB.retFootE_crl (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    (Jv : JVm (L := L) V H s σ) {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    {Bw n : Nat} (h1 : p.val + fi.val ≤ Bw) (h2 : Bw + n * 32768 ≤ p.val + 2 ^ sb.val) :
    RetFootE X (VirtLoopSharp.CrL V Bw n (P1.vHeadA st s)) := by
  intro b hb u hu
  rcases hb with hw | rfl | ⟨w, hw, e, -⟩
  · exact B.retFootE_win C hAs hcap h1 h2 b hw u hu
  · have hh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val B.kern.ksbFit
    rcases C.ks u hu with h | h <;> omega
  · rcases C.apartV Jv u hu w hw with h | h <;> omega

end

end

end Fl4Proofs.P3
