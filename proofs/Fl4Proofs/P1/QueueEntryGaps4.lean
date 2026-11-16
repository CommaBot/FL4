/-
P1: the kernel entry from the decode gaps that remain after the thread
family's proved labels, CNode Delete/Revoke's finalisation dispatch and
SchedContext `YieldTo` (`InvGaps4`), with the placement facts `P3Place`,
`CdtHyps2`, `DelPlace` and `TcbPlace`.  `InvGaps3` is unchanged.
-/
import Fl4Proofs.P1.QueueDecTcb2
import Fl4Proofs.P1.QueueFinThr
import Fl4Proofs.P1.QueueSchedCtl
import Fl4Proofs.P1.QueueDecIrq
import Fl4Proofs.P1.QueueDecVs
import Fl4Proofs.P1.QueueDecUt
import Fl4Proofs.P1.QueueUtRetype
import Fl4Proofs.P1.QueueFinIo
import Fl4Proofs.P1.QueueDecVcpu
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- The families whose decode P1 still does not prove, the thread family's
named labels (`TcbGaps`), and the named per-kind finalisations of CNode
`Delete`/`Revoke` (`FinGaps`).  `YieldTo` is no longer a gap
(`scYieldGap_holds`); SchedControl, IrqControl, IrqHandler, IOPortControl and
IOPort, VSpace and Untyped (down to the retype) are proved (`QueueSchedCtl`,
`QueueDecIrq`, `QueueDecVs`, `QueueDecUt`), up to their named premises
(`scCtl`, `irqPl`, `vsPl`, and P3's `utPl` for the untyped retype). -/
structure InvGaps4 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Adm : PSets → Prop) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) : Prop where
  /-- P3's facts for the untyped family's retype (the decode is proved,
  `decGap_untyped`; the retype from them, `UtRetypeP3.utPlace`), over P3's
  state fact `P3Ok`, which holds at every untyped decode's start (`UtOkAt`). -/
  utPl : ∃ P3Ok : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop,
    UtRetypeP3 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok ∧ UtOkAt st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  thread : TcbGaps st ar T Cs Ω H Sg Rp Scs Nt Z U
  /-- The IRQ handler family's placement premises (the family is proved, `decGap_irqHandler`). -/
  irqPl : IrqPlace st T Cs Ω H Sg Rp Scs Nt Z U
  /-- `SchedControl`'s placement premises (the family is proved, `decGap_schedControl`). -/
  scCtl : ScCtlPlace st T Cs Ω H Sg Rp Scs Nt Z U
  /-- The VSpace family's placement premises (the family is proved, `decGap_vspace`). -/
  vsPl : VsPlace st ar T Cs Ω H Sg Rp Scs Nt Z U
  /-- The VCPU objects' placement (the VCPU family is proved, `decGap_vcpu`; the
  I/O-port caps' finalisation from it, `VcpuPlace.ioPl`). -/
  vcpuPl : VcpuPlace st T Cs Ω H Sg Rp Scs Nt Z U
  /-- EPT (VT-x: not yet refined, DESIGN §5). -/
  ept : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .ept
  /-- The finalisations of CNode `Delete`/`Revoke` P1 does not prove: the
  VT-x kinds (VCPUs, EPTs, EPT frames; not yet refined, DESIGN §5). -/
  fin : FinGap st ar T Cs Ω H Sg Rp Scs Nt Z fun c => (∃ x1, c = .Vcpu x1) ∨
    (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨
    (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)

/-- `InvGaps4` gives `InvGaps3`. -/
theorem InvGaps4.gaps3 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {V : U64 → Prop}
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z) (Pd : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V)
    (Pt : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U) (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U)
    (G : InvGaps4 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U) :
    InvGaps3 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U :=
  ⟨decGap_untyped hA hσ (G.utPl.choose_spec.1.utPlace hA) G.utPl.choose_spec.2, decGap_thread hA G.thread Pt E (delGaps_of hA Pd ((⟨finGap_ioPort hA G.vcpuPl.ioPl, G.fin⟩ : FinGaps st ar T Cs Ω H Sg Rp Scs Nt Z).kinds hA Pd)) C.toCdtHyps,
    decGap_irqControl hA C.toCdtHyps, decGap_irqHandler hA C.toCdtHyps Pd G.irqPl,
    decGap_schedControl hA G.scCtl, decGap_vspace hA Pd G.vsPl C.toCdtHyps E G.irqPl, decGap_vcpu hA G.vcpuPl E G.irqPl.extra, G.ept, decGap_ioPortControl C.toCdtHyps,
    decGap_ioPort hA E, scYieldGap_holds hA U, delGaps_of hA Pd ((⟨finGap_ioPort hA G.vcpuPl.ioPl, G.fin⟩ : FinGaps st ar T Cs Ω H Sg Rp Scs Nt Z).kinds hA Pd)⟩

/-- The placement facts and gaps of an admissible set tuple (`InvGaps4`'s
kernel entry). -/
def Hyps4 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (Adm : PSets → Prop)
    (Cs U : Set U64) (σ : PSets) : Prop :=
  P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U ∧ CdtHyps2 st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z ∧
    (∃ V : U64 → Prop, DelPlace st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z V) ∧ TcbPlace st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U ∧
    InvGaps4 st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn

/-- **Native kernel entries keep `EntryInv`**, from `InvGaps4` and the
placement facts of every admissible tuple (`Hyps4`); the entry ends over
some admissible tuple (a retype grows the heap). -/
theorem kernel_entry.entry_of4 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps4 st ar Adm Cs U σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) :=
  kernel_entry.entry_of3 hA (fun σ h' => by
    obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, hNt⟩ := GF σ h'
    exact ⟨P, C, G.gaps3 hA h' C Pd Pt P.xfer, hNt⟩) hσ s a h

end

end Fl4Proofs.P1
