/-
P1: the kernel entry from the decode gaps that remain after the thread
family's proved labels, CNode Delete/Revoke's finalisation dispatch and
SchedContext `YieldTo` (`InvGaps4`), with the placement facts `P3Place`,
`CdtHyps2`, `DelPlace` and `TcbPlace`.  `InvGaps3` is unchanged.
-/
import Fl4Proofs.P1.QueueDecTcb2
import Fl4Proofs.P1.QueueFinThr
import Fl4Proofs.P1.QueueSchedCtl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- The families whose decode P1 still does not prove, the thread family's
named labels (`TcbGaps`), and the named per-kind finalisations of CNode
`Delete`/`Revoke` (`FinGaps`).  `YieldTo` is no longer a gap
(`scYieldGap_holds`). -/
structure InvGaps4 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) : Prop where
  untyped : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .untyped
  thread : TcbGaps st ar T Cs Ω H Sg Rp Scs Nt Z U
  irqControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .irqControl
  irqHandler : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .irqHandler
  /-- `SchedControl`'s placement premises (the family is proved, `decGap_schedControl`). -/
  scCtl : ScCtlPlace st T Cs Ω H Sg Rp Scs Nt Z U
  vspace : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .vspace
  vcpu : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .vcpu
  ept : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .ept
  ioPortControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .ioPortControl
  ioPort : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .ioPort
  /-- The finalisations of CNode `Delete`/`Revoke` P1 does not prove. -/
  fin : FinGaps st ar T Cs Ω H Sg Rp Scs Nt Z

/-- `InvGaps4` gives `InvGaps3`. -/
theorem InvGaps4.gaps3 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z) (Pd : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V)
    (Pt : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U) (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U)
    (G : InvGaps4 st ar T Cs Ω H Sg Rp Scs Nt Z U) :
    InvGaps3 st ar T Cs Ω H Sg Rp Scs Nt Z U :=
  ⟨G.untyped, decGap_thread hA G.thread Pt E (delGaps_of hA Pd (G.fin.kinds hA Pd)) C.toCdtHyps, G.irqControl, G.irqHandler,
    decGap_schedControl hA G.scCtl, G.vspace, G.vcpu, G.ept, G.ioPortControl, G.ioPort, scYieldGap_holds hA U,
    delGaps_of hA Pd (G.fin.kinds hA Pd)⟩

/-- **Native kernel entries keep `EntryInv`**, from `InvGaps4` and the
placement facts. -/
theorem kernel_entry.entry_of4 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (P : P3Place st ar T Cs Ω H Sg Rp Scs Nt Z U)
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z) {V : U64 → Prop} (Pd : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V)
    (Pt : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U) (G : InvGaps4 st ar T Cs Ω H Sg Rp Scs Nt Z U)
    {Ac : Set U64} (s : S) (a : A) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄) :=
  kernel_entry.entry_of3 hA hNt P C (G.gaps3 hA C Pd Pt P.xfer) s a h

end

end Fl4Proofs.P1
