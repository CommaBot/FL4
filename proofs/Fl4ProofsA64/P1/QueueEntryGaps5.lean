/-
P1 (aarch64): **`InvGaps5`**, the A64 entry-gap record whose deletion path has no walk field quantified over
every root (`InvGaps4.place` holds `W7.R.DelPlace`, whose `ptw` / `elw` / `ptslot` are false as stated, gen 22).

`InvGaps5` is `InvGaps4` with `place` replaced by `∃ V, W7.R.A5.DelPlace V ∧ W7.R.A5.VsDel V ∧ VsPlaceA V`
(QueueDelVs5: [J] `frm` and the root-restricted walks [J] `VsDel`) and the cnode / thread / irqHandler families
taken from `W7.R.A5.decGap_cnode_rv4`, `W7.R.A5.decGap_thread4`, `decGap_irqHandler5` (QueueDecDel5). Every
other field and family is `InvGaps4`'s (`InvGaps4.gaps`' assembly otherwise unchanged); `vcpu` stays a
`DecGap` field. `kernel_entry.entry_of5A` is `entry_of4` over it.

Named premises: the fields of `InvGaps5` (as `InvGaps4`, with `place` as above). No [J] `DelPlaceAt.ptw` / `.elw` /
`.ptslot` (any of the `DelPlaceAt`, `W7.DelPlaceAt`, `W7.R.DelPlaceAt` copies) and no [J] `DelPlaceAt.rv` on its
path.
-/
import Fl4ProofsA64.P1.QueueDecDel5
import Fl4ProofsA64.P1.QueueEntryGaps4
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- **The A64 entry-gap record with root-restricted deletion walks.** -/
structure InvGaps5 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Adm : PSets → Prop) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  /-- The deletion placements (`W7.R.A5.DelPlace`: [P] `cap` / `next` / `prev` / `pool` / `aset` / `rcw` / `irq`,
  [J] `frm`), **[J] `W7.R.A5.VsDel`** (the deletion's walks from ASID-table roots) and [J] `VsPlaceA`, over one
  set of VSpace words. -/
  place : ∃ V : U64 → Prop, W7.R.A5.DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok ∧
    W7.R.A5.VsDel st ar T Cs Ω H Sg Rp Scs Nt Z V P3Ok ∧ VsPlaceA st ar T Cs Ω H Sg Rp Scs Nt Z U V P3Ok
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

theorem InvGaps5.gaps {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (P : P3Place st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (G : InvGaps5 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
  obtain ⟨V, Pd, W, Vs⟩ := G.place
  obtain ⟨UtOk, Ut, UO⟩ := G.ut
  exact ⟨decGap_untyped hA G.adm (Ut.utPlace hA) UO,
    decGap_reply hA P.xfer P.tmoAny (fun Ac s h => (P.blkU Ac s h).2) P.rvAt,
    W7.R.A5.decGap_cnode_rv4 hA G.cdt2 Pd W G.fin,
    W7.R.A5.decGap_thread4 hA G.ssp G.tcb P.xfer Pd W G.fin G.cdt2.toCdtHyps G.tcb7,
    decGap_irqControl hA G.maxSpi G.cdt2.toCdtHyps,
    decGap_irqHandler5 hA G.cdt2.toCdtHyps Pd G.irq,
    decGap_domain hA,
    decGap_sc_f hA P.xfer G.yield G.scBindOwn,
    decGap_schedControl hA G.scCtl G.scBindOwn,
    decGap_vspace hA Vs G.cdt2.toCdtHyps P.xfer G.irq,
    G.vcpu,
    decGap_ept hA,
    decGap_ioPortControl G.cdt2.toCdtHyps,
    decGap_ioPort hA P.xfer,
    decGap_tdx hA P.xfer⟩

/-- **Native kernel entries keep `EntryInv`**, from `InvGaps5` and `P3Place` of every admissible tuple
(`kernel_entry.entry_of`, as `entry_of4`). -/
theorem kernel_entry.entry_of5A {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (TX : TmoXGA st ar)
    (GF : ∀ σ : PSets, Adm σ → P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧
      InvGaps5 st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn)
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
