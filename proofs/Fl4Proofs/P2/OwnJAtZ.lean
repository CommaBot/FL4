/-
P2: **`LayP` (hence `RegionOK`, `UserOK`) from the joint invariant `JAtZ`**:
the two [J] premises of `E2E.Fl4Step.ser` for the layout the joint invariant's
ghosts give (`layoutJ`): the typed heap `H`, the kernel-state base, the slots of
`Z.th`, and as user memory the words of `Z.B` (every word of every non-device
user frame, `JAtZ.fcov`; the IPC buffers are among them).

The only hypothesis beside `JAtZ` is that the cores counted are in its set `Cs`.
-/
import Fl4Proofs.P2.OwnLayout
import Fl4Proofs.P3.BufInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.OwnMap
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P2.E2E

noncomputable section
open Classical

/-- The layout of the joint invariant's ghosts, on `n` cores. -/
def layoutJ (Z : XSets) (H : Heap) (ksb : U64) (n : Nat) : KLayout where
  heap := H
  ksb := ksb
  ncores := n
  slots := {a | IsSlot Z.th a}
  user := {b | ∃ wp ∈ Z.B, wp.1 = b}

variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type}
  {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The placement from `JAtZ`.** -/
theorem layP_of_JAtZ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : Nat}
    (hn : ∀ c : U64, c.val < n → c ∈ Cs) : LayP (layoutJ Z H (L.ksb s) n) := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hB := J.bufPlacedJ
  refine ⟨hJ.heap, fun c hc p k hp => J.kern.hnd p k hp c (hn c hc), fun p hp => ?_, ?_, ?_⟩
  · obtain ⟨q, i, hqi, rfl⟩ := id hp
    exact ⟨hqi.aligned hJ.pl, hJ.slot_in hp⟩
  · rintro x ⟨wp, hw, rfl⟩ p k hp hk ⟨h1, h2⟩
    rcases hk with rfl | rfl | ⟨z, rfl⟩
    · have := J.ip.e.bt wp hw p (J.thT p ((hJ.tcb p).2 hp))
      simp only [HKind.bits] at h2; omega
    · have := hB.ntfn wp hw p (J.hset.2.1 p hp)
      simp only [HKind.bits] at h2; omega
    · have hpC : p ∈ Z.C := J.hscC p z hp
      obtain ⟨Q, R, -, hs⟩ := J.xtop.fin.1.1.1.lists
      obtain ⟨y, n', hk, -⟩ := hs.scs p hpC
      have hH := (hJ.sc p y n' (J.c0 p hpC) hk).2
      rw [show H p = some (.sc z) from hp] at hH
      have hz : z = n' + Fl4Spec.minSchedContextBits := by injection hH with e; injection e
      have := hB.sc wp hw p hpC y n' hk
      simp only [HKind.bits] at h2; rw [hz] at h2; omega
  · rintro x ⟨wp, hw, rfl⟩ p hp h
    exact Vs.BufPlaced.slot J.xtop.fin.1.2 hw hp h

/-- **`RegionOK` and `UserOK` from `JAtZ`.** -/
theorem ok_of_JAtZ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : Nat}
    (hn : ∀ c : U64, c.val < n → c ∈ Cs) :
    RegionOK (layoutJ Z H (L.ksb s) n) ∧ UserOK (layoutJ Z H (L.ksb s) n) :=
  ⟨regionOK_of (layP_of_JAtZ J hn), userOK_of (layP_of_JAtZ J hn)⟩

end
end Fl4Proofs.P2.OwnMap
