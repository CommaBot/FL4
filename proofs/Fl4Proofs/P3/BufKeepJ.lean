/-
P3 (KENTRY-PLAN a6f, gap 1): **the buffer fact at the states inside
`schedule`.**

Since #80/#85 `send_signal` (inside `timer::fire`'s loop, inside `schedule`)
may complete a full-state VMEnter and write the target thread's IPC buffer,
so P1's signal lemmas need the receive-buffer fact
(`msg.lookup_ipc_buffer … ⦃ BufOK U ⦄`) at the loop's states, while P3 has it
only at the `J` state (`JAtZ.bufOK`). P1's `KWB` footprints (`KW` without the
TCBs' `IPC_BUFFER` word) keep the words the lookup reads (`BufKeep.of_footDBU`),
so the fact at `J` carries to every state reached from `J` by writes of
`KWB` words, debug-list words and the buffer words `BufU Z σ` themselves:

* `JAtZ.bufFact`: the buffer fact at `J` (P1's `BufFact`, every TCB of `H`).
* `JAtZ.bufU_outside`: the buffer words lie outside the TCBs and nodes.
* `JAtZ.bufFact_of_footDBU` / `JAtZ.bufFact_of_footDB`: the fact at any state
  `s'` with such a footprint from `J` (the fire loop's states: the loop
  carries `FootDB` from its start, plus the full-state reports' `BufU` words).

No premise.
-/
import Fl4Proofs.P3.XTopJointKEntryFF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The buffer fact at `J`**: every TCB's receive buffer in `BufU`. -/
theorem JAtZ.bufFact {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    P1.BufFact st (P1.Heap.tcbs H) (P1.BufOK (BufU Z σ)) s := fun _ hy => J.bufOK hy

/-- **The IPC-buffer words lie outside the TCBs and nodes.** -/
theorem JAtZ.bufU_outside {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (hb : b ∈ BufU Z σ) :
    P1.OutsideObjs st (P1.Heap.tcbs H) Cs s b :=
  (J.bufU_out hb).1

/-- **The buffer fact after a `KWB` / debug-list / `BufU` footprint from `J`**
(any state inside `schedule`'s fire loop). -/
theorem JAtZ.bufFact_of_footDBU {s s' : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (f : P1.WritesIn st s s' (fun b => P1.KWB st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s b ∨ P1.DbgW st (P1.Heap.tcbs H) Cs s b ∨ b ∈ BufU Z σ)) :
    P1.BufFact st (P1.Heap.tcbs H) (P1.BufOK (BufU Z σ)) s' :=
  J.bufFact.keep (P1.BufKeep.of_blkDBU J.blk (fun _ hb => J.bufU_outside hb) f)

/-- **The buffer fact after a `FootDB` footprint from `J`.** -/
theorem JAtZ.bufFact_of_footDB {s s' : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (f : P1.FootDB st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s') :
    P1.BufFact st (P1.Heap.tcbs H) (P1.BufOK (BufU Z σ)) s' :=
  J.bufFact_of_footDBU (P1.WritesIn.mono f fun _ hb => Or.elim hb Or.inl fun h => Or.inr (Or.inl h))

end

end Fl4Proofs.P3
