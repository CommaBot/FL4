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
import Fl4Proofs.P1.QueueDecEpt
import Fl4Proofs.P1.QueueIpcFoot
import Fl4Proofs.P1.FastDecline
import Fl4Proofs.P1.IbKeepHolds
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
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
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  /-- P3's facts for the untyped family's retype (the decode is proved,
  `decGap_untyped`; the retype from them, `UtRetypeP3.utPlace`), over P3's
  state fact `UtOk`, which holds at every untyped decode's start (`UtOkAt`). -/
  utPl : ∃ UtOk : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop,
    UtRetypeP3 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U UtOk ∧ UtOkAt st T Cs Ω H Sg Rp Scs Nt Z U P3Ok UtOk
  thread : TcbGaps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- The IRQ handler family's placement premises (the family is proved, `decGap_irqHandler`). -/
  irqPl : IrqPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- `SchedControl`'s placement premises (the family is proved, `decGap_schedControl`). -/
  scCtl : ScCtlPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- The VSpace family's placement premises (the family is proved, `decGap_vspace`). -/
  vsPl : VsPlace st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- The VCPU objects' placement (the VCPU family is proved, `decGap_vcpu`; the
  I/O-port caps' finalisation from it, `VcpuPlace.ioPl`). -/
  vcpuPl : VcpuPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- The EPT tables' placement (the EPT family is proved, `decGap_ept`). -/
  eptPl : EptPlaceH st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- The finalisations of CNode `Delete`/`Revoke` P1 does not prove: the
  VT-x kinds (VCPUs, EPTs, EPT frames; not yet refined, DESIGN §5). -/
  fin : ∀ s0, EntAt st P3Ok s0 → FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => (∃ x1, c = .Vcpu x1) ∨
    (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨
    (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)) s0

/-- `InvGaps4` gives `InvGaps3`. -/
theorem InvGaps4.gaps3 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {V : U64 → Prop}
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (Pd : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (Pt : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (G : InvGaps4 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) :
    InvGaps3 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok :=
  have DG : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok := fun s0 hE =>
    delGaps_of hA (Pd s0 hE) ((⟨finGap_ioPort hA (G.vcpuPl.ioPl s0 hE), G.fin s0 hE⟩ :
      FinGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0).kinds hA (Pd s0 hE))
  ⟨decGap_untyped hA hσ (G.utPl.choose_spec.1.utPlace hA) G.utPl.choose_spec.2, decGap_thread hA G.thread Pt E DG C.toCdtHyps,
    decGap_irqControl hA C.toCdtHyps, decGap_irqHandler hA C.toCdtHyps Pd G.irqPl,
    decGap_schedControl hA G.scCtl, decGap_vspace hA Pd G.vsPl G.eptPl.pl C.toCdtHyps E G.irqPl DG, decGap_vcpu hA G.vcpuPl E G.irqPl.extra, decGap_ept hA G.eptPl, decGap_ioPortControl C.toCdtHyps,
    decGap_ioPort hA E, scYieldGap_holds hA U, DG⟩

/-- The placement facts and gaps of an admissible set tuple (`InvGaps4`'s
kernel entry).
**Contradictory** (p1g, P1/EntryVacuous): no `EntryInv` state satisfies it (its `P3Place`); not a
specification of the kernel. -/
def Hyps4 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (Adm : PSets → Prop)
    (Cs U : Set U64) (P3Ok : S → Prop) (σ : PSets) : Prop :=
  P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ CdtHyps2 st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z P3Ok ∧
    (∃ V : U64 → Prop, DelPlace st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z V P3Ok) ∧ TcbPlace st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧
    InvGaps4 st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn

end

end Fl4Proofs.P1
