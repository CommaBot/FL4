/-
P3 (DESIGN.md §9), scheduling contexts: `CKeep`, what the call-stack
relation reads of the spec, kept (the scheduler footprints `SFoot` and the
queue operations' footprints are in ScKFoot.lean).
-/
import Fl4Proofs.P3.ScConfig
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- What the call-stack relation reads of the spec, kept: SCs (with their
size and `sc_replies`) and replies (with `reply_sc`). -/
def CKeep (σ σ' : State Unit) : Prop :=
  (∀ q y n, σ.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
    y'.scReplies = y.scReplies) ∧
  (∀ q x, σ.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc ∧
    x'.replyTcb = x.replyTcb) ∧
  (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n))

theorem CKeep.of_kheap {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : CKeep σ σ' :=
  ⟨fun q y n hq => ⟨y, by rw [h]; exact hq, rfl⟩, fun q x hq => ⟨x, by rw [h]; exact hq, rfl, rfl⟩,
    fun p x n hp => ⟨x, by rw [← h]; exact hp⟩⟩

theorem CKeep.refl (σ : State Unit) : CKeep σ σ := CKeep.of_kheap rfl

theorem CKeep.trans {σ σ1 σ2 : State Unit} (h1 : CKeep σ σ1) (h2 : CKeep σ1 σ2) : CKeep σ σ2 := by
  refine ⟨fun q y n hq => ?_, fun q x hq => ?_, fun p x n hp => ?_⟩
  · obtain ⟨y1, h1', e1⟩ := h1.1 q y n hq; obtain ⟨y2, h2', e2⟩ := h2.1 q y1 n h1'; exact ⟨y2, h2', e2.trans e1⟩
  · obtain ⟨x1, h1', e1, f1⟩ := h1.2.1 q x hq; obtain ⟨x2, h2', e2, f2⟩ := h2.2.1 q x1 h1'
    exact ⟨x2, h2', e2.trans e1, f2.trans f1⟩
  · obtain ⟨x1, h1'⟩ := h2.2.2 p x n hp; exact h1.2.2 p x1 n h1'

/-- Replacing a TCB or a notification by a TCB or a notification. -/
theorem CKeep.updOther {σ : State Unit} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (h1 : ∀ y n, o ≠ .schedContext y n) (h2 : ∀ x, o ≠ .reply x)
    (h1' : ∀ y n, o' ≠ .schedContext y n) : CKeep σ (updK σ p o') := by
  refine ⟨fun q y n hq => ?_, fun q x hq => ?_, fun q x n hq => ?_⟩
  · have : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq; exact h1 y n rfl
    exact ⟨y, by simp [updK, this, hq], rfl⟩
  · have : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq; exact h2 x rfl
    exact ⟨x, by simp [updK, this, hq], rfl, rfl⟩
  · by_cases e : q = p
    · subst e; simp [updK] at hq; exact absurd hq (h1' x n)
    · exact ⟨x, by simpa [updK, e] using hq⟩

theorem CKeep.updSc {σ : State Unit} {p : ObjRef} {y y' : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (e : y'.scReplies = y.scReplies) :
    CKeep σ (updK σ p (.schedContext y' n)) := by
  refine ⟨fun q z m hq => ?_, fun q x hq => ?_, fun q x m hq => ?_⟩
  · by_cases h : q = p
    · subst h; rw [hk] at hq; cases hq; exact ⟨y', by simp [updK], e⟩
    · exact ⟨z, by simp [updK, h, hq], rfl⟩
  · have : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    exact ⟨x, by simp [updK, this, hq], rfl, rfl⟩
  · by_cases h : q = p
    · subst h; simp [updK] at hq; obtain ⟨-, rfl⟩ := hq; exact ⟨y, hk⟩
    · exact ⟨x, by simpa [updK, h] using hq⟩

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

end

end

end Fl4Proofs.P3.Sched
