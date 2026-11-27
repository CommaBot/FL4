/-
# P2 (2): write footprint of the I/O port local path (line p2io)

Footprint lemmas have the shape `∀ w, ¬ Foot s w → read s' w = read s w`
(`P1.WritesIn st s s' Foot`: also the kernel base and the core index are
unchanged), with `Foot s` a predicate on (aligned) words computed from the
entry state `s`, the entry's inputs and the typed-heap sets of the P1
invariants.

`syscall.handle_ioport_local` locks nothing (fl4-sync `local_syscall`: "An
I/O port access writes only the caller and this core's state: nothing to
lock"), so its footprint is this core's words (`FootIo` = P2/FootVm's
`FootVmCore`: the node, the TCBs of this core's threads, this core's SCs)
plus the I/O port, which is an Arch effect (`port_in` / `port_out`) and not
a memory word.

* `ioport_local_decline_foot`: a declined run wrote only the current
  thread's `FAULT_IP` and the node's timestamp words, inside `FootIo`.

Not yet proved here: the accepted run (`handle_invocation` of the IoPort cap,
`after_invocation`, `finish`); P1's `ioport_local_same` reduces it to the
general entry `syscall.handle_syscall`, for which P1 has no per-core
footprint yet.

Premises: none.
-/
import Fl4Proofs.P2.FootVm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **The write footprint of the I/O port local path** at entry state `s`:
this core's node, the TCBs of its threads, its SCs (`FootVmCore`). -/
abbrev FootIo (T Scs : Set U64) (Z : U64 → Nat) (s : S) (b : U64) : Prop := FootVmCore (L := L) T Scs Z s b

variable {A : Type _} {ar : machine.Arch A}

/-- **A declined `handle_ioport_local` writes only `FootIo`** (the current
thread's `FAULT_IP` and the node's timestamp words, or nothing). -/
theorem ioport_local_decline_foot {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {number : I64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (h : syscall.handle_ioport_local st ar s a number = ok (false, s', a')) :
    WritesIn st s s' (FootIo (L := L) T Scs Z s) := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  have hN : NodePlaced st T s (L.cpu s) := hSQ.nodes _ hSQ.cur
  rcases ioport_local_decline ar h with ⟨rfl, -⟩ | ⟨hP, -⟩
  · exact WritesIn.refl _ _
  · exact localPre_foot hA hSQ.tcbs hN hSQ.curT hP

end

end Fl4Proofs.P2
