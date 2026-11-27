/-
P1 (aarch64): the kernel entry from one A64 entry-gap record, `InvGaps4`, assembled directly from the newest
forms (not via `InvGaps3`, whose `del` is the old `DelGaps` with [J] `DelPlaceAt.rv`):
* reply: `decGap_reply` (P3Place's `xfer`, `tmoAny`, `blkU`, [J] `rvAt`), as `InvGaps3.gaps`;
* cnode: `W7.R.decGap_cnode_rv4` (`CdtHyps2`, `W7.R.DelPlace`, `W7.R.FinGaps4`);
* thread: `W7.R.decGap_thread4` (`SspHyps`, `TcbPlace`, `TcbPlace7`, `W7.R.DelPlace`, `W7.R.FinGaps4`);
* irqControl: `decGap_irqControl` ([P] `MaxSpi`); irqHandler: `decGap_irqHandler` (`W7.R.DelPlace`, `IrqPlace`);
* domain: `decGap_domain`; schedContext: `decGap_sc_f` (`ScYieldGap`, [P] `ScBindOwn`);
  schedControl: `decGap_schedControl` (`ScCtlPlace`, [P] `ScBindOwn`);
* untyped: `decGap_untyped` with `UtRetypeP3.utPlace` and `UtOkAt`;
* vspace: `decGap_vspace` (QueueDecVs, [J] `VsPlaceA`); ept: `decGap_ept` (no premise);
* ioPortControl / ioPort: `decGap_ioPortControl` / `decGap_ioPort`; tdx: `decGap_tdx`.
Only the `vcpu` family stays a `DecGap` field (QueueDecVcpu for the ARM VCPU not yet proved).

Named premises: those of the forms above, unchanged in statement; nothing new in kind. The record's fields
are the premises themselves (`InvGaps4`), so `InvGaps4.gaps` is a pure assembly.
-/
import Fl4ProofsA64.P1.QueueDecVs
import Fl4ProofsA64.P1.QueueUtRetype
import Fl4ProofsA64.P1.QueueEntryGaps3
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- **The A64 entry-gap record**: the premises of the newest decode forms, and the one family (`vcpu`) whose
decode P1 does not prove yet. -/
structure InvGaps4 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Adm : PSets → Prop) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  /-- [P] (as `W7.R.DelPlaceAt`) the deletion placement facts (no `rv`) and **[J] `VsPlaceA`** (the AArch64
  VSpace placements, QueueDecVs), over one set of VSpace words. -/
  place : ∃ V : U64 → Prop, W7.R.DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok ∧
    VsPlaceA st ar T Cs Ω H Sg Rp Scs Nt Z U V P3Ok
  /-- [J] `FinRvRest4` and the arch finalisation gap (`W7.R.FinGaps4`). -/
  fin : W7.R.FinGaps4 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok
  cdt2 : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok
  ssp : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  tcb : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  tcb7 : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok
  /-- [P] The GIC's largest SPI is at most 1019 (gic.rs:115–117). -/
  maxSpi : MaxSpi ar
  irq : IrqPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  yield : ScYieldGap st ar T Cs Ω H Sg Rp Scs Nt Z U
  /-- [P] At a decode the `OWNER_CPU` word of a running VCPU is a user word. -/
  scBindOwn : ScBindOwn st T Cs Ω H Sg Rp Scs Nt Z U
  scCtl : ScCtlPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- The untyped family's facts (`UtRetypeP3`, `UtOkAt`). -/
  ut : ∃ UtOk : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop,
    UtRetypeP3 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U UtOk ∧ UtOkAt st T Cs Ω H Sg Rp Scs Nt Z U P3Ok UtOk
  /-- The tuple is admissible. -/
  adm : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩
  /-- The ARM VCPU's decode (not yet proved). -/
  vcpu : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vcpu

theorem InvGaps4.gaps {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (P : P3Place st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (G : InvGaps4 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
  obtain ⟨V, Pd, Vs⟩ := G.place
  obtain ⟨UtOk, Ut, UO⟩ := G.ut
  exact ⟨decGap_untyped hA G.adm (Ut.utPlace hA) UO,
    decGap_reply hA P.xfer P.tmoAny (fun Ac s h => (P.blkU Ac s h).2) P.rvAt,
    W7.R.decGap_cnode_rv4 hA G.cdt2 Pd G.fin,
    W7.R.decGap_thread4 hA G.ssp G.tcb P.xfer Pd G.fin G.cdt2.toCdtHyps G.tcb7,
    decGap_irqControl hA G.maxSpi G.cdt2.toCdtHyps,
    decGap_irqHandler hA G.cdt2.toCdtHyps Pd G.irq,
    decGap_domain hA,
    decGap_sc_f hA P.xfer G.yield G.scBindOwn,
    decGap_schedControl hA G.scCtl G.scBindOwn,
    decGap_vspace hA Vs G.cdt2.toCdtHyps P.xfer G.irq,
    G.vcpu,
    decGap_ept hA,
    decGap_ioPortControl G.cdt2.toCdtHyps,
    decGap_ioPort hA P.xfer,
    decGap_tdx hA P.xfer⟩

/-- **Native kernel entries keep `EntryInv`**, from `InvGaps4` and `P3Place` of every admissible tuple
(`kernel_entry.entry_of`). As `kernel_entry.entry_of3`, the P1 entry composites' premise bundles are
contradictory with the `EntryInv` premise (P1/EntryVacuous); the record is what the A64 FastVm closure and
P3's entry consume. -/
theorem kernel_entry.entry_of4 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (TX : TmoXGA st ar)
    (GF : ∀ σ : PSets, Adm σ → P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧
      InvGaps4 st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall_general st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) :=
  kernel_entry.entry_of hA TX (fun σ h' => ⟨(GF σ h').1, (GF σ h').2.1.gaps hA (GF σ h').1,
    (GF σ h').2.2⟩) hσ s a hP h

end

end Fl4ProofsA64.P1
