-- AArch64 port of Fl4Proofs.P1.QueueEntryGaps3 (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: the kernel entry from the decode gaps that remain after the Reply family
and CNode Delete/Revoke (`InvGaps3`), with the CDT placement facts
`CdtHyps2` and `P3Place`.  `InvGaps2` is unchanged.

a64 (AArch64 port): `InvGaps3` has one more field, **[P] `scBindOwn`** (`ScBindOwn`, QueueScBindVm; as
`InvGaps2F.scBindOwn`), because the A64 SchedContext decode is `decGap_sc_f` (A64's `decGap_sc` needs the
false [J] `ScBindRv`); `decGap_reply` takes `P.rvAt` ([J], `P3Place.rvAt`); `kernel_entry.entry_of3` is
over `TmoXGA` and `handle_syscall_general` and drops `IK : IbKeep` (as `entry_of2`). Named premises: those of
`P3Place` / `CdtHyps2` / `InvGaps3` ([J] `rvAt`, [P] `vmpl`, [P] `scBindOwn`); nothing new in kind.
-/
import Fl4ProofsA64.P1.QueueDecDel
import Fl4ProofsA64.P1.QueueDecTdx
import Fl4ProofsA64.P1.EntryFin
import Fl4ProofsA64.P1.QueueScBindVm  -- a64: `decGap_sc_f`, `ScBindOwn`
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- The families whose decode P1 still does not prove, and the named steps
inside the families it does (SchedContext `YieldTo`; the finalisation steps
of CNode `Delete`/`Revoke`). -/
structure InvGaps3 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Adm : PSets → Prop) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  untyped : DecGapG st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok .untyped
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
  /-- The finalisation steps of CNode `Delete` and `Revoke`. -/
  del : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok
  /-- **[P] (a64)** At a decode the `OWNER_CPU` word of a running VCPU is a user word (`ScBindOwn`). -/
  scBindOwn : ScBindOwn st T Cs Ω H Sg Rp Scs Nt Z U

theorem InvGaps3.gaps {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (P : P3Place st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (G : InvGaps3 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok :=
  ⟨G.untyped, decGap_reply hA P.xfer P.tmoAny (fun Ac s h => (P.blkU Ac s h).2) P.rvAt,  -- a64: [J] `rvAt`
    decGap_cnode2 hA C G.del,
    G.thread, G.irqControl, G.irqHandler, decGap_domain hA, decGap_sc_f hA P.xfer G.yield G.scBindOwn,  -- a64
    G.schedControl, G.vspace,
    G.vcpu, G.ept, G.ioPortControl, G.ioPort, decGap_tdx hA P.xfer⟩

/-- **Native kernel entries keep `EntryInv`**, from `InvGaps3`, `CdtHyps2`
and `P3Place` of every admissible tuple.
**Vacuous** (p1g): its premise bundles are contradictory with the `EntryInv` premise
(P1/EntryVacuous). Use P3's `kernel_entry_entryInvU29` (P3/XTopJointEntryInv29),
which has this conclusion from U29's premises. -/
theorem kernel_entry.entry_of3 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (TX : TmoXGA st ar)  -- a64: A form, no `IK`
    (GF : ∀ σ : PSets, Adm σ → P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ CdtHyps2 st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z P3Ok ∧
      InvGaps3 st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall_general st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) :=
  kernel_entry.entry_of hA TX (fun σ h' => ⟨(GF σ h').1, (GF σ h').2.2.1.gaps hA (GF σ h').1 (GF σ h').2.1,
    (GF σ h').2.2.2⟩) hσ s a hP h

end

end Fl4ProofsA64.P1
