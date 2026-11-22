/-
P3 (issue #16, jc1; KENTRY-PLAN g7b-4 step 1): **the first two `JCarry` facts
and their frame lemmas**, before they become a `JAtZ` field.

* `BufObjHyp B σ` (C21, C24 bufObj; moved here from XTopJointUtEp, same
  statement): every IPC-buffer word of `B` lies in a spec object.
* `ArchFitHyp H σ` (first half of C16 / C22 / C24 heapH; moved here from
  UtEpSets, same statement): an `other` object of P1's heap at a spec arch
  object is no larger than it.
* `BufPgHyp B σ`: the carried form of `BufObjHyp`, every word of `B` in a
  **non-device data page** of `σ` (`bufObj_of_pg`). `BufObjHyp` cannot be
  carried across a frame step as stated: the frame facts every `JAtZ`
  construction has (`KSz`, backward: an object after was one of the same type
  before; `IpcFrKeep.page`, forward for non-device data pages) do not keep an
  arbitrary object, while `B`'s words are user-frame words (`B` only grows by
  the frame retype's new pages, UtFrameAdd `BNew`, and is pruned by the
  detype's `KeepB (KBOf p sb)`), so the page form is the invariant.
* `JCarry Z H σ := BufPgHyp Z.B σ ∧ ArchFitHyp H σ` with `JCarry.frame`: one
  call at a frame step, from the step's `IpcFrKeep` (as `JAtZ.fcov`'s
  `FrameCover.ipcFr`) and `KSz` (as `JAtZ.sfree`'s `SpecFree.frame`), `B`
  shrunk or kept, `H` kept.
-/
import Fl4Proofs.P3.BufDefs
import Fl4Proofs.P3.StepSem
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- **[J] Every IPC-buffer word lies in a spec object** (l4v
`valid_ipc_buffer_cap` + `obj_at`). -/
def BufObjHyp (B : Set (U64 × Fl4Spec.Word)) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ wp ∈ B, ∃ (o : Fl4Spec.ObjRef) (ko : Fl4Spec.KernelObject), σ.kheap o = some ko ∧ o.toNat ≤ wp.1.val ∧
    wp.1.val + 8 ≤ o.toNat + 2 ^ Fl4Spec.objBits ko

/-- **[J] P1's `other` objects fit their spec arch objects** (l4v arch
`obj_range`). -/
def ArchFitHyp (H : P1.Heap) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ o ao n, σ.kheap o = some (.archObj ao) → H ⟨o⟩ = some (.other n) → n ≤ Fl4Spec.objBits (.archObj ao)

/-- **Every word of `B` in a non-device data page** (the carried form of `BufObjHyp`). -/
def BufPgHyp (B : Set (U64 × Fl4Spec.Word)) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ wp ∈ B, ∃ (q : Fl4Spec.ObjRef) (vms : Fl4Spec.VMPageSize),
    σ.kheap q = some (.archObj (.dataPage false vms)) ∧ q.toNat ≤ wp.1.val ∧
    wp.1.val + 8 ≤ q.toNat + 2 ^ Fl4Spec.pageBitsForSize vms

theorem bufObj_of_pg {B : Set (U64 × Fl4Spec.Word)} {σ : Fl4Spec.State Unit} (h : BufPgHyp B σ) :
    BufObjHyp B σ := fun wp hw => by
  obtain ⟨q, vms, hq, h1, h2⟩ := h wp hw
  exact ⟨q, _, hq, h1, h2⟩

/-- `BufPgHyp` across a step keeping the non-device data pages, `B` shrunk or kept. -/
theorem BufPgHyp.frame {B B' : Set (U64 × Fl4Spec.Word)} {σ σ' : Fl4Spec.State Unit} (h : BufPgHyp B σ)
    (hB : B' ⊆ B)
    (hp : ∀ p vms, σ.kheap p = some (.archObj (.dataPage false vms)) →
      σ'.kheap p = some (.archObj (.dataPage false vms))) : BufPgHyp B' σ' := fun wp hw => by
  obtain ⟨q, vms, hq, h1, h2⟩ := h wp (hB hw)
  exact ⟨q, vms, hp q vms hq, h1, h2⟩

/-- `BufPgHyp` with `B` grown by words of new non-device pages (the frame retype's `BNew`). -/
theorem BufPgHyp.grow {B B' : Set (U64 × Fl4Spec.Word)} {σ σ' : Fl4Spec.State Unit} {Wn : U64 → Prop}
    (h : BufPgHyp B σ)
    (hB : ∀ wp ∈ B', wp ∈ B ∨ (Wn wp.1 ∧ wp.2 = wp.1.bv))
    (hp : ∀ p vms, σ.kheap p = some (.archObj (.dataPage false vms)) →
      σ'.kheap p = some (.archObj (.dataPage false vms)))
    (hn : ∀ a, Wn a → ∃ (q : Fl4Spec.ObjRef) (vms : Fl4Spec.VMPageSize),
      σ'.kheap q = some (.archObj (.dataPage false vms)) ∧ q.toNat ≤ a.val ∧
      a.val + 8 ≤ q.toNat + 2 ^ Fl4Spec.pageBitsForSize vms) : BufPgHyp B' σ' := fun wp hw => by
  rcases hB wp hw with hw | ⟨hw, -⟩
  · obtain ⟨q, vms, hq, h1, h2⟩ := h wp hw
    exact ⟨q, vms, hp q vms hq, h1, h2⟩
  · exact hn wp.1 hw

/-- The size an arch object type fixes. -/
def aaSize : Fl4Spec.AAType → Nat
  | .aASIDPool => Fl4Spec.pageBits
  | .aVcpu => 15
  | .aEpt _ => Fl4Spec.tableSize
  | .aPageTable => Fl4Spec.tableSize
  | .aPageDirectory => Fl4Spec.tableSize
  | .aPDPointerTable => Fl4Spec.tableSize
  | .aPageMapL4 => Fl4Spec.tableSize
  | .aUserData sz => Fl4Spec.pageBitsForSize sz
  | .aDeviceData sz => Fl4Spec.pageBitsForSize sz

theorem archKobjSize_aaSize (a : Fl4Spec.ArchKernelObj) : Fl4Spec.archKobjSize a = aaSize (Fl4Spec.aaType a) := by
  cases a <;> simp only [Fl4Spec.aaType, Fl4Spec.archKobjSize] <;> (try split) <;> rfl

/-- An object of the type of an arch object is an arch object of its size. -/
theorem archObj_of_aType {ko : Fl4Spec.KernelObject} {ao : Fl4Spec.ArchKernelObj}
    (h : Fl4Spec.aType ko = Fl4Spec.aType (.archObj ao)) :
    ∃ ao0, ko = .archObj ao0 ∧ Fl4Spec.objBits (.archObj ao0) = Fl4Spec.objBits (.archObj ao) := by
  cases ko with
  | archObj ao0 =>
    refine ⟨ao0, rfl, ?_⟩
    have e : Fl4Spec.aaType ao0 = Fl4Spec.aaType ao := by
      simpa only [Fl4Spec.aType, Fl4Spec.AType.aArch.injEq] using h
    show Fl4Spec.archKobjSize ao0 = Fl4Spec.archKobjSize ao
    rw [archKobjSize_aaSize, archKobjSize_aaSize, e]
  | cnode sz cs =>
    simp only [Fl4Spec.aType] at h; split at h <;> cases h
  | schedContext x n =>
    simp only [Fl4Spec.aType] at h; split at h <;> cases h
  | _ => simp [Fl4Spec.aType] at h

/-- `ArchFitHyp` across a step with `KSz`, `H` kept. -/
theorem ArchFitHyp.frame {H : P1.Heap} {σ σ' : Fl4Spec.State Unit} (h : ArchFitHyp H σ) (hk : KSz σ σ') :
    ArchFitHyp H σ' := by
  intro o ao n ho hH
  obtain ⟨ko, hko, ht⟩ := hk o _ ho
  obtain ⟨ao0, rfl, hb⟩ := archObj_of_aType ht
  rw [← hb]; exact h o ao0 n hko hH

/-- **The joint facts carried for the [J] leaves** (KENTRY-PLAN g7b-4; step 1:
C21 / C24 bufObj and the first half of C16 / C22 / C24 heapH). -/
structure JCarry (B : Set (U64 × Fl4Spec.Word)) (H : P1.Heap) (σ : Fl4Spec.State Unit) : Prop where
  /-- C21, C24 bufObj, in its carried form (`JCarry.bufObj`). -/
  bufPg : BufPgHyp B σ
  /-- C16, C22, C24 heapH (first half). -/
  archFit : ArchFitHyp H σ

theorem JCarry.bufObj {B : Set (U64 × Fl4Spec.Word)} {H : P1.Heap} {σ : Fl4Spec.State Unit}
    (h : JCarry B H σ) : BufObjHyp B σ := bufObj_of_pg h.bufPg

/-- **`JCarry` across a frame step** (module docstring). -/
theorem JCarry.frame {B B' : Set (U64 × Fl4Spec.Word)} {H : P1.Heap} {σ σ' : Fl4Spec.State Unit}
    (h : JCarry B H σ) (hB : B' ⊆ B) (hF : IpcFrKeep σ σ') (hk : KSz σ σ') : JCarry B' H σ' :=
  ⟨h.bufPg.frame hB hF.page, h.archFit.frame hk⟩

end

end Fl4Proofs.P3
