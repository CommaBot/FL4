/-
P1 (aarch64): **`InvGaps7B`**, the A64 entry-gap record over the corrected placements: neither [P] `FinPl`'s false
thread clause nor the false [P] `rcw` (`W7.R.A5.DelPlaceAt.rcw`, `TcbPlace7.rcw`) is used on its path.

* `InvGaps7B` = `InvGaps7` with `place` over `W7.R.A5.B.DelPlace` (QueueDelVsB: `B.FinPl`, [P] `vc : VcPl`),
  `tcb7` → [P] `tcb8 : TcbPlace8` (QueueDecTcbB), `vcpuB` → `vcpuC : VcpuGapsC` (`Run` only; SetTCB proved,
  QueueDecVcpuB) and [P] `vcpuObj : VcpuObjA`.
* **`InvGaps7B.gaps`**: `InvGaps` from `P3Place` and `InvGaps7B` (`B.decGap_cnode_rv4`, `B.decGap_thread4`,
  `decGap_irqHandler5B`, `decGap_vcpuC`; the other families as `InvGaps7.gaps`).
* `kernel_entry.entry_of7B`.

Still on the path and reported false as stated in the handoff (§30), not fixed here: [P] `scBindOwn`
(`ScBindOwn`: the run VCPU's `OWNER_CPU` word in the user words `U`, outside `Ω` by `DecPre.user`) and
`TcbPlace8.own` (the same word a `UserW` word) — the counterexample of `rcw` applies (a VCPU is an `Ω` object).

New premises: none here (those of the modules used).
-/
import Fl4ProofsA64.P1.QueueDecVcpuB
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- **The A64 entry-gap record over the corrected placements** (`InvGaps7` with `place` over `W7.R.A5.B.DelPlace`
([P] `vc : VcPl` for the false `rcw`, `B.FinPl` for the false thread clause), `tcb7` → [P] `tcb8 : TcbPlace8`,
`vcpuB` → `vcpuC` (`Run` only) and [P] `vcpuObj : VcpuObjA`). -/
structure InvGaps7B (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
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
  /-- The ARM VCPU's label not yet proved: `Run`. -/
  vcpuC : VcpuGapsC st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- [P] The invoked VCPU's words are aligned words of `Ω` off `Sg` (`VcpuW`). -/
  vcpuW : VcpuW st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- [P] The state transfers' placement facts (`VcpuStA`). -/
  vcpuSt : VcpuStA st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- [P] The invoked VCPU is a VCPU object along its decode (`VcpuObjA`). -/
  vcpuObj : VcpuObjA st T Cs Ω H Sg Rp Scs Nt Z U P3Ok

theorem InvGaps7B.gaps {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (P : P3Place st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (G : InvGaps7B st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
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
    decGap_vcpuC hA P.xfer G.vcpuC G.vcpuW G.vcpuSt G.vcpuObj Pd,
    decGap_ept hA,
    decGap_ioPortControl G.cdt2.toCdtHyps,
    decGap_ioPort hA P.xfer,
    decGap_tdx hA P.xfer⟩

/-- **Native kernel entries keep `EntryInv`**, from `InvGaps7B` and `P3Place` of every admissible tuple
(`kernel_entry.entry_of`, as `entry_of7A`). **Vacuous** as every `kernel_entry.entry_of*` top: `P3Place` is
contradictory with `BXI` (`blkU`, P1/EntryVacuous's argument, the A64 `P3Place` has the same field). -/
theorem kernel_entry.entry_of7B {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (TX : TmoXGA st ar)
    (GF : ∀ σ : PSets, Adm σ → P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧
      InvGaps7B st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn)
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
