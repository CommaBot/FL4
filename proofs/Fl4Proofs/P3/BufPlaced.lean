/-
P3 (DESIGN.md §9): **the placement of the IPC-buffer words** `B` (the
pairs of FL4 and spec addresses of the mapped IPC-buffer words, EpRel's
`EPlaced`), a named hypothesis on the joint invariant for the code that
writes message registers into a caller's buffer (the error reply,
ReplyFailX; TCB ReadRegisters and GetBreakpoint):

* `BufPlaced`: apart from the notifications, the kernel-global block and
  core `c`'s node, and the SC objects;
* `BufPlaced.mono`, across a step keeping the kernel-global base and the SC
  objects;
* the projections `BufPlaced.slot` (no buffer word is a word of a slot of the
  typed heap, from `TopPlaced`, whose `OObj` holds the buffer words) and
  `BufPlaced.dom` (no buffer word is a word of the domain schedule, which
  lies in the kernel-global block's first 256 bytes).
-/
import Fl4Proofs.P3.VsTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **The placement of the IPC-buffer words** (a hypothesis on the joint
invariant): apart from the notifications, the kernel-global block and
core `c`'s node, and the SC objects. -/
structure BufPlaced (N C : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64) (s : S) (σ : Fl4Spec.State Unit) :
    Prop where
  ntfn : ∀ wp ∈ B, ∀ n ∈ N, wp.1.val + 8 ≤ n.val ∨ n.val + 64 ≤ wp.1.val
  far : ∀ wp ∈ B, wp.1.val + 8 ≤ (L.ksb s).val ∨ L.nodeBase s c + 4288 ≤ wp.1.val
  sc : ∀ wp ∈ B, ∀ sc ∈ C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) →
    wp.1.val + 8 ≤ sc.val ∨ sc.val + 2 ^ n ≤ wp.1.val

/-- The words of a slot are words of the VSpace objects. -/
theorem vobj_of_slot {th : TypedHeap} (hPl : Placed th) (P L4 L3 L2 L1 : Set U64) (ksb : U64) {x b : U64}
    (hx : IsSlot th x) (h1 : x.val ≤ b.val) (h2 : b.val < x.val + 32) : VObj th P L4 L3 L2 L1 ksb b := by
  obtain ⟨p, i, hi, rfl⟩ := hx
  have hv := hi.val hPl
  obtain ⟨k', hk', hs⟩ := hi.size
  have hf := hPl.fits p k' hk'
  rw [hv] at h1 h2
  rcases hi with ⟨r, hp, hir⟩ | ⟨hp, hit⟩
  · refine Or.inl ⟨p, r, hp, by omega, ?_⟩
    generalize 2 ^ r = M at hir
    omega
  · refine Or.inr (Or.inl ⟨p, hp, by omega, ?_⟩)
    simp [tcbSlots] at hit; omega


theorem BufPlaced.mono {s s' : S} {σ σ' : Fl4Spec.State Unit} (h : BufPlaced (L := L) N C B c s σ)
    (hk : L.ksb s' = L.ksb s)
    (hsck : ∀ q x n, σ'.kheap q = some (.schedContext x n) → σ.kheap q = some (.schedContext x n)) :
    BufPlaced (L := L) N C B c s' σ' := by
  have hnb : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hk]
  exact ⟨h.ntfn, fun wp hw => by rw [hk, hnb]; exact h.far wp hw,
    fun wp hw sc hsc x n hx => h.sc wp hw sc hsc x n (hsck _ _ _ hx)⟩


/-- **No buffer word is a slot word** (the slots are VSpace objects, apart
from `OObj`, which holds the buffer words). -/
theorem BufPlaced.slot {s : S} {σ : Fl4Spec.State Unit}
    (hP : TopPlaced st th P L4 L3 L2 L1 N T C E R B c s σ) {wp : U64 × Fl4Spec.Word} (hw : wp ∈ B)
    {x : U64} (hx : IsSlot th x) : ¬ (x.val ≤ wp.1.val ∧ wp.1.val < x.val + 32) := fun ⟨h1, h2⟩ =>
  hP.disj _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, le_refl _, by omega⟩)))))))
    (vobj_of_slot hP.pl P L4 L3 L2 L1 (L.ksb s) hx h1 h2)

/-- **No buffer word is a domain-schedule word** (those lie in the first 256
bytes of the kernel-global block). -/
theorem BufPlaced.dom {s : S} {σ : Fl4Spec.State Unit} (h : BufPlaced (L := L) N C B c s σ)
    {wp : U64 × Fl4Spec.Word} (hw : wp ∈ B) : wp.1.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ wp.1.val := by
  have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
  have := h.far wp hw; omega

end

end

end Fl4Proofs.P3.Vs
