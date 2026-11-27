/-
P1 (aarch64): **`InvGaps8`**, the A64 entry-gap record with **no VCPU gap**: `InvGaps7B` (the corrected
placements, QueueEntryGaps7B) with `vcpuC` (`Run`) dropped — `ARMVCPURun` is proved (QueueDecVcpuRunB) — and the
heap's notification typing `ntH` (the third component of every entry top's `GF`, here needed inside the
`vcpu` family by `vcpu::check`'s notification).

* **`InvGaps8.gaps`** (`decGap_vcpuD`), **`kernel_entry.entry_of8A`**.

Still on the path and reported false as stated (handoff §30), not fixed here: [P] `scBindOwn` and
`TcbPlace8.own` (a run VCPU's `OWNER_CPU` word taken as a user word; a VCPU is an `Ω` object).

New premises: none here.
-/
import Fl4ProofsA64.P1.QueueDecVcpuRunB
import Fl4ProofsA64.P1.QueueEntryGaps7B
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- **The A64 entry-gap record with no VCPU gap** (`InvGaps7B` without `vcpuC`, with `ntH`; as `InvGaps7` with `place` over `W7.R.A5.B.DelPlace`
([P] `vc : VcPl` for the false `rcw`, `B.FinPl` for the false thread clause), `tcb7` → [P] `tcb8 : TcbPlace8`,
`vcpuB` dropped and [P] `vcpuObj : VcpuObjA`). -/
structure InvGaps8 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Adm : PSets → Prop) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  /-- The deletion placements over the corrected forms (`W7.R.A5.B.DelPlace`), [J] `W7.R.A5.VsDel`, [J] `VsPlaceA`. -/
  place : ∃ V : U64 → Prop, W7.R.A5.B.DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok ∧
    W7.R.A5.VsDel st ar T Cs Ω H Sg Rp Scs Nt Z V P3Ok ∧ VsPlaceA st ar T Cs Ω H Sg Rp Scs Nt Z U V P3Ok
  fin : W7.R.FinGaps4 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok
  cdt2 : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok
  ssp : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  tcb : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- [P] `TcbPlace8` (`TcbPlace7` with `rcw` → `rcv`). -/
  tcb8 : TcbPlace8 st T Cs Ω H Sg Rp Scs Nt Z P3Ok
  /-- [P] The GIC's largest SPI is at most 1019. -/
  maxSpi : MaxSpi ar
  irq : IrqPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  yield : ScYieldGap st ar T Cs Ω H Sg Rp Scs Nt Z U
  /-- [P] At a decode the `OWNER_CPU` word of a running VCPU is a user word. -/
  scBindOwn : ScBindOwn st T Cs Ω H Sg Rp Scs Nt Z U
  scCtl : ScCtlPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  ut : ∃ UtOk : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop,
    UtRetypeP3 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U UtOk ∧ UtOkAt st T Cs Ω H Sg Rp Scs Nt Z U P3Ok UtOk
  adm : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩
  /-- The heap's notifications (as every entry top's `GF`). -/
  ntH : ∀ n ∈ Nt, H n = some .ntfn
  /-- [P] The invoked VCPU's words are aligned words of `Ω` off `Sg` (`VcpuW`). -/
  vcpuW : VcpuW st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- [P] The state transfers' placement facts (`VcpuStA`). -/
  vcpuSt : VcpuStA st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- [P] The invoked VCPU is a VCPU object along its decode (`VcpuObjA`). -/
  vcpuObj : VcpuObjA st T Cs Ω H Sg Rp Scs Nt Z U P3Ok

theorem InvGaps8.gaps {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (P : P3Place st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (G : InvGaps8 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
  obtain ⟨V, Pd, W, Vs⟩ := G.place
  obtain ⟨UtOk, Ut, UO⟩ := G.ut
  exact ⟨decGap_untyped hA G.adm (Ut.utPlace hA) UO,
    decGap_reply hA P.xfer P.tmoAny (fun Ac s h => (P.blkU Ac s h).2) P.rvAt,
    W7.R.A5.B.decGap_cnode_rv4 hA G.cdt2 Pd W G.fin,
    W7.R.A5.B.decGap_thread4 hA G.ssp G.tcb P.xfer Pd W G.fin G.cdt2.toCdtHyps G.tcb8,
    decGap_irqControl hA G.maxSpi G.cdt2.toCdtHyps,
    decGap_irqHandler5B hA G.cdt2.toCdtHyps Pd G.irq,
    decGap_domain hA,
    decGap_sc_f hA P.xfer G.yield G.scBindOwn,
    decGap_schedControl hA G.scCtl G.scBindOwn,
    decGap_vspace hA Vs G.cdt2.toCdtHyps P.xfer G.irq,
    decGap_vcpuD hA G.ntH P.xfer G.vcpuW G.vcpuSt G.vcpuObj Pd,
    decGap_ept hA,
    decGap_ioPortControl G.cdt2.toCdtHyps,
    decGap_ioPort hA P.xfer,
    decGap_tdx hA P.xfer⟩

/-- **Native kernel entries keep `EntryInv`**, from `InvGaps8` and `P3Place` of every admissible tuple
(`kernel_entry.entry_of`, as `entry_of7B`). **Vacuous** as every `kernel_entry.entry_of*` top: `P3Place` is
contradictory with `BXI` (`blkU`, P1/EntryVacuous's argument, the A64 `P3Place` has the same field). -/
theorem kernel_entry.entry_of8A {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (TX : TmoXGA st ar)
    (GF : ∀ σ : PSets, Adm σ → P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧
      InvGaps8 st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn)
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
