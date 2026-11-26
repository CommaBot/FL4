-- AArch64 port of Fl4Proofs.P1.QueueEntryGaps (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: the kernel entry from the decode gaps that remain after the
SchedContext, Domain and CNode families (`InvGaps2`), their named narrower
steps (`ScYieldGap`, `CnodeGaps`), the CDT placement facts (`CdtHyps`) and
`P3Place`.

a64: `InvGaps2` has the field **[J] `scBindRv`** (`ScBindRv`, QueueDecSc), passed to `decGap_sc`.
-/
import Fl4ProofsA64.P1.QueueDecCnode
import Fl4ProofsA64.P1.QueueDecTdx
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- The families whose decode P1 still does not prove, and the named steps
inside the families it does. -/
structure InvGaps2 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Adm : PSets → Prop) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  untyped : DecGapG st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok .untyped
  reply : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .reply
  thread : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .thread
  irqControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .irqControl
  irqHandler : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .irqHandler
  schedControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .schedControl
  vspace : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vspace
  vcpu : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vcpu
  ept : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ept
  ioPortControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ioPortControl
  ioPort : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ioPort
  /-- SchedContext `YieldTo`. -/
  yield : ScYieldGap st ar T Cs Ω H Sg Rp Scs Nt Z U
  /-- CNode `Delete` and `Revoke`. -/
  cnode : CnodeGaps st ar T Cs Ω H Sg Rp Scs Nt Z U
  /-- **[J] (a64)** At a decode a thread with no SC runs no VCPU (`ScBindRv`, QueueDecSc: the SC `Bind`'s
  `migrate_tcb`). -/
  scBindRv : ScBindRv st T Cs Ω H Sg Rp Scs Nt Z U

theorem InvGaps2.gaps {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (G : InvGaps2 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok :=
  ⟨G.untyped, G.reply, decGap_cnode C G.cnode, G.thread, G.irqControl, G.irqHandler, decGap_domain hA,
    decGap_sc hA E G.yield G.scBindRv, G.schedControl, G.vspace, G.vcpu, G.ept, G.ioPortControl, G.ioPort, decGap_tdx hA E⟩

-- (int6) `kernel_entry.entry_of2` moved to `P1/EntryFin` (it needs par/a6x's `EntryXGTop`).

end

end Fl4ProofsA64.P1
