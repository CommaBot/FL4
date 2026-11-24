/-
P1 (KENTRY-PLAN a6f, gap 1 of int6): **`ibKeep_holds`** discharges the core's
deferred `IbKeep st ar` (QueueSignal): `timer::fire`'s loop steps keep the
three words `lookup_ipc_buffer` reads of every TCB (`IbFr`).

* `timer.remove`: its `TF` frame keeps every TCB word below the timer fields
  (`TKeep`; the `IPC_BUFFER` word 3512 and the buffer slot 64/72 among them).
* the current node's `REPROGRAM` write: a node word, no TCB word.
* `send_signal`: `notification.send_signal.tinvFK` (QueueFootS) gives its
  footprint as `FootDUB` (`KWB`: `KW` without the `IPC_BUFFER` word, the debug
  lists, and the user words `U`); `BufKeep.of_blkDBU` (QueueFinal) turns that
  into the buffer words kept, `UsrW` putting `U` outside the TCBs.

No premise.
-/
import Fl4Proofs.P1.QueueFootS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- `BufKeep` (QueueFoot) is `IbFr` (QueueSignal) with the key-space base. -/
theorem IbFr.of_bufKeep {T : Set U64} {s s' : S} (hk : L.ksb s' = L.ksb s) (k : BufKeep st T s s') :
    IbFr (L := L) T s s' :=
  ⟨hk, fun y hy => k y hy⟩

/-- `timer.remove` keeps the buffer-lookup words. -/
theorem timer.remove.ibFr {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
    (s : S) (t : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    timer.remove st s t ⦃ s' => IbFr (L := L) T s s' ⦄ := by
  refine WP.spec_mono (timer.remove.tf (s0 := s) s t (TF.start h) ht) fun s' hf => ?_
  have tk := hf.2.2.2.1
  refine ⟨hf.2.1.1, fun y hy => ⟨?_, ?_, ?_⟩⟩
  · exact tk y hy 3512#u64 (by simp) (by simp) (Or.inl (by simp))
  · rw [sbWordA_eq]; exact tk y hy 64#u64 (by simp) (by simp) (Or.inl (by simp))
  · rw [sbWordA8_eq]; exact tk y hy 72#u64 (by simp) (by simp) (Or.inl (by simp))

/-- The current node's `REPROGRAM` write keeps the buffer-lookup words. -/
theorem reprogram.ibFr {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
    (s : S) (v : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    IbFr (L := L) T s (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) v) := by
  obtain ⟨⟨Q, R, h0⟩, -⟩ := h
  have hT := h0.tcbs
  have hN := h0.nodes _ h0.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have aR : Aligned (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) := nodeAt_aligned hN (by rw [rp]; omega) (by rw [rp])
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) v) (core.num.U64.wrapping_add y K) =
        L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
    L.mem_wr_ne aR (field_aligned (hT y hy) hK hK8)
      (fun e => node_ne_field hN (by rw [rp]; omega) hy (hT y hy) hK (UScalar.eq_of_val_eq e))
  refine ⟨L.ksb_wr _ _ _, fun y hy => ⟨?_, ?_, ?_⟩⟩
  · exact fld y hy 3512#u64 (by simp) (by simp)
  · rw [sbWordA_eq]; exact fld y hy 64#u64 (by simp) (by simp)
  · rw [sbWordA8_eq]; exact fld y hy 72#u64 (by simp) (by simp)

/-- `send_signal` keeps the buffer-lookup words (from its `FootDUB` footprint). -/
theorem notification.send_signal.ibFr {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
    {Ac U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (n bd : U64)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) (hH : H n = some .ntfn)
    (hBA : BufAt st T Cs H Sg Scs Z U s) :
    notification.send_signal st ar s a n bd ⦃ s' _ => IbFr (L := L) T s s' ⦄ := by
  refine WP.spec_mono (notification.send_signal.tinvFK hA s a n bd h hn hH hBA.1 hBA.2) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  have f := hr.2.1
  exact IbFr.of_bufKeep f.1 (BufKeep.of_blkDBU (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (fun b hb => (hBA.1 b hb).out)
    (WritesIn.mono f fun _ hb => by
      rcases hb with (hb | hb) | hb
      · exact Or.inl hb
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr hb)))

/-- **`IbKeep` holds** (KENTRY-PLAN int6 core / a6f). -/
theorem ibKeep_holds {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) : IbKeep st ar :=
  fun _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun s t h ht => timer.remove.ibFr s t h ht,
     fun s a n bd h hn hH hBA => notification.send_signal.ibFr hA s a n bd h hn hH hBA,
     fun s v h => reprogram.ibFr s v h⟩

end

end Fl4Proofs.P1
