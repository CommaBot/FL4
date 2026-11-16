/-
P1: **writes of untracked words keep the invariants** — the words a reset or
retype clears after the dead objects are dropped (`QueueHeapDrop`) lie in no
object P1 tracks.  `BlkOK` only reads `Ω` through membership facts (its
words are outside the TCBs, nodes and endpoints; the SC words, the frame
words and the kernel-global words are in it), so it holds over `Ω ∪ U` for
untracked words `U` (`BlkOK.widen`), the cap-slot frame `blk_of_capw` then
covers writes of `U` (as `Ω ∖ Sg` words), and `BlkOK.narrow` returns to `Ω`.
-/
import Fl4Proofs.P1.QueueHeapDrop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- Untracked words for `BlkOK`'s sets: outside the TCBs and nodes, off the
endpoints and notifications, and not frame words. -/
structure Untracked (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (H : Heap) (Sg : Set U64)
    (s : S) (a : U64) : Prop where
  out : OutsideObjs st T Cs s a
  eps : ∀ e, (H e = some .ep ∨ H e = some .ntfn) → a.val + 8 ≤ e.val ∨ e.val + 16 ≤ a.val
  sg : a ∉ Sg

/-- **`BlkOK` over `Ω` extended by untracked words.** -/
theorem BlkOK.widen {s : S} {U : Set U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hU : ∀ a ∈ U, Untracked st T Cs H Sg s a) : BlkOK st T Cs (Ω ∪ U) H Sg Rp Scs Nt Z Ac s := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  obtain ⟨E, EQ, w1, w2, w3, w4, w5, k⟩ := h0.eps
  have k3 := k.2.2.1
  have q : SchedQueuesInv st T Cs (Ω ∪ U) H s Q R :=
    { h0 with
      eps := ⟨E, EQ, w1, w2, fun e he a ha => ha.elim (w3 e he a) fun hu => (hU a hu).eps e ((k3 e).1 he), w4, w5, k⟩
      omega := fun a ha => ha.elim (h0.omega a) fun hu => (hU a hu).out }
  have x : XInv st T Cs (Ω ∪ U) Sg Rp Scs Nt Z s :=
    ⟨{ hX.1 with scW := fun c hc b ha hin => Or.inl (hX.1.scW c hc b ha hin) }, hX.2⟩
  exact ⟨⟨Q, R, q⟩, hB, x, { hS with sub := fun b hb => Or.inl (hS.sub b hb), ksΩ := fun o h1 h2 => Or.inl (hS.ksΩ o h1 h2) },
    ⟨fun b hb => Or.inl (hSg.sub b hb), hSg.ks, fun o h1 h2 => Or.inl (hSg.ksΩ o h1 h2)⟩⟩

/-- **`BlkOK` back over `Ω`**, given its membership facts (state independent
but for the kernel-global base). -/
theorem BlkOK.narrow {s : S} {U : Set U64} (h : BlkOK st T Cs (Ω ∪ U) H Sg Rp Scs Nt Z Ac s)
    (hks : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 → core.num.U64.wrapping_add (L.ksb s) o ∈ Ω)
    (hsc : ∀ c ∈ Scs, ∀ b : U64, Aligned b → InSC c (Z c) b → b ∈ Ω) (hsg : ∀ b ∈ Sg, b ∈ Ω) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  obtain ⟨E, EQ, w1, w2, w3, w4, w5, k⟩ := h0.eps
  have q : SchedQueuesInv st T Cs Ω H s Q R :=
    { h0 with
      eps := ⟨E, EQ, w1, w2, fun e he a ha => w3 e he a (Or.inl ha), w4, w5, k⟩
      omega := fun a ha => h0.omega a (Or.inl ha) }
  have x : XInv st T Cs Ω Sg Rp Scs Nt Z s := ⟨{ hX.1 with scW := hsc }, hX.2⟩
  exact ⟨⟨Q, R, q⟩, hB, x, { hS with sub := hsg, ksΩ := hks }, ⟨hsg, hSg.ks, hks⟩⟩

/-- **Writes of untracked words keep `BlkOK`** (with `blk_of_capw`'s frames). -/
theorem blk_of_untracked {s s' : S} {B : U64 → Prop} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → Untracked st T Cs H Sg s b) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ PFr st T Sg s s' ∧
      L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧ L.actionW s' = L.actionW s ∧
      (∀ y ∈ T, ∀ K : U64, 192 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) ∧
      (∀ b ∈ Sg, L.mem s' b = L.mem s b) := by
  have hw' := h.widen (U := {b | B b}) fun a ha => hB a ha
  obtain ⟨h1, rest⟩ := blk_of_capw hw' hw fun b hb => Or.inr ⟨Or.inr hb, (hB b hb).sg⟩
  refine ⟨h1.narrow (fun o ho h8 => by rw [hw.1]; exact h.2.2.2.2.ksΩ o ho h8)
    (fun c hc b ha hin => h.2.2.1.1.scW c hc b ha hin) h.2.2.2.2.sub, rest⟩

end

end Fl4Proofs.P1
