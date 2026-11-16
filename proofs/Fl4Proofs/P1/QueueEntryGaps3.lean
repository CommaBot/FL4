/-
P1: the kernel entry from the decode gaps that remain after the Reply family
and CNode Delete/Revoke (`InvGaps3`), with the CDT placement facts
`CdtHyps2` and `P3Place`.  `InvGaps2` is unchanged.
-/
import Fl4Proofs.P1.QueueDecDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- The families whose decode P1 still does not prove, and the named steps
inside the families it does (SchedContext `YieldTo`; the finalisation steps
of CNode `Delete`/`Revoke`). -/
structure InvGaps3 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) : Prop where
  untyped : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .untyped
  thread : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .thread
  irqControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .irqControl
  irqHandler : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .irqHandler
  schedControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .schedControl
  vspace : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .vspace
  vcpu : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .vcpu
  ept : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .ept
  ioPortControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .ioPortControl
  ioPort : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .ioPort
  /-- SchedContext `YieldTo`. -/
  yield : ScYieldGap st ar T Cs Ω H Sg Rp Scs Nt Z U
  /-- The finalisation steps of CNode `Delete` and `Revoke`. -/
  del : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z

theorem InvGaps3.gaps {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : P3Place st ar T Cs Ω H Sg Rp Scs Nt Z U) (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z)
    (G : InvGaps3 st ar T Cs Ω H Sg Rp Scs Nt Z U) : InvGaps st ar T Cs Ω H Sg Rp Scs Nt Z U :=
  ⟨G.untyped, decGap_reply hA P.xfer P.tmoAny (fun Ac s h => (P.recvOK Ac s h).2.1), decGap_cnode2 hA C G.del,
    G.thread, G.irqControl, G.irqHandler, decGap_domain ar, decGap_sc hA P.xfer G.yield, G.schedControl, G.vspace,
    G.vcpu, G.ept, G.ioPortControl, G.ioPort⟩

/-- **Native kernel entries keep `EntryInv`**, from `InvGaps3`, `CdtHyps2`
and `P3Place`. -/
theorem kernel_entry.entry_of3 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (P : P3Place st ar T Cs Ω H Sg Rp Scs Nt Z U)
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z) (G : InvGaps3 st ar T Cs Ω H Sg Rp Scs Nt Z U)
    {Ac : Set U64} (s : S) (a : A) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄) :=
  kernel_entry.entry_of hA hNt P (G.gaps hA P C) s a h

end

end Fl4Proofs.P1
