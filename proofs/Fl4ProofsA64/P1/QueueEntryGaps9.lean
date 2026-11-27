/-
P1 (aarch64): **`InvGaps9`**, the A64 entry-gap record without the false [P] `scBindOwn` / `TcbPlace8.own`:
`InvGaps8` with `scBindOwn` dropped and `tcb8 : TcbPlace8` replaced by **[P] `tcb9 : TcbPlace9`** (`TcbPlace8`
minus `own`, QueueDecTcbC). The SchedContext and SchedControl families' migrations now read the run VCPU's
`OWNER_CPU` word as an `Ω \ Sg` word (QueueScBindV: `decGap_sc_fV`, `decGap_schedControlV`, over
`ScBindOwnV`, which `TcbPlace9.scBindOwnV` derives from `tcb9.rcv`), the thread family's SetSchedParams the same
way (`W7.R.A5.B.C.decGap_thread4`).

* **`InvGaps9.of8`** (`InvGaps9` is strictly weaker than `InvGaps8`), **`InvGaps9.gaps`**,
  **`kernel_entry.entry_of9A`**.

Still known false on the path (unchanged, not this module's subject): the `< 128` IrqHandler bound of
`DelCapOK` returned by `place`'s `B.DelPlaceAt.cap` (GIC IRQs go up to 5375; the IRQ widening, handoff §29/§31).
The entry tops remain vacuous through `P3Place.blkU` (P1/EntryVacuous), as every `kernel_entry.entry_of*`.

New premises: none (`tcb9` is a field-subset of the reviewed `tcb8`).
-/
import Fl4ProofsA64.P1.QueueDecTcbC
import Fl4ProofsA64.P1.QueueEntryGaps8
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- **The A64 entry-gap record without `scBindOwn` / `own`**: `InvGaps8` without `scBindOwn` and with
`tcb8` → [P] `tcb9 : TcbPlace9`. -/
structure InvGaps9 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Adm : PSets → Prop) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  /-- The deletion placements over the corrected forms (`W7.R.A5.B.DelPlace`), [J] `W7.R.A5.VsDel`, [J] `VsPlaceA`. -/
  place : ∃ V : U64 → Prop, W7.R.A5.B.DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok ∧
    W7.R.A5.VsDel st ar T Cs Ω H Sg Rp Scs Nt Z V P3Ok ∧ VsPlaceA st ar T Cs Ω H Sg Rp Scs Nt Z U V P3Ok
  fin : W7.R.FinGaps4 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok
  cdt2 : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok
  ssp : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  tcb : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- [P] `TcbPlace9` (`TcbPlace8` without the false `own`). -/
  tcb9 : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok
  /-- [P] The GIC's largest SPI is at most 1019. -/
  maxSpi : MaxSpi ar
  irq : IrqPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  yield : ScYieldGap st ar T Cs Ω H Sg Rp Scs Nt Z U
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

/-- `InvGaps9` is `InvGaps8` with fewer facts. -/
theorem InvGaps9.of8 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop}
    (G : InvGaps8 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : InvGaps9 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok :=
  ⟨G.place, G.fin, G.cdt2, G.ssp, G.tcb, TcbPlace9.of8 G.tcb8, G.maxSpi, G.irq, G.yield, G.scCtl, G.ut, G.adm,
    G.ntH, G.vcpuW, G.vcpuSt, G.vcpuObj⟩

theorem InvGaps9.gaps {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (P : P3Place st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (G : InvGaps9 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
  obtain ⟨V, Pd, W, Vs⟩ := G.place
  obtain ⟨UtOk, Ut, UO⟩ := G.ut
  exact ⟨decGap_untyped hA G.adm (Ut.utPlace hA) UO,
    decGap_reply hA P.xfer P.tmoAny (fun Ac s h => (P.blkU Ac s h).2) P.rvAt,
    W7.R.A5.B.decGap_cnode_rv4 hA G.cdt2 Pd W G.fin,
    W7.R.A5.B.C.decGap_thread4 hA G.ssp G.tcb P.xfer Pd W G.fin G.cdt2.toCdtHyps G.tcb9,
    decGap_irqControl hA G.maxSpi G.cdt2.toCdtHyps,
    decGap_irqHandler5B hA G.cdt2.toCdtHyps Pd G.irq,
    decGap_domain hA,
    decGap_sc_fV hA P.xfer G.yield G.tcb9.scBindOwnV,
    decGap_schedControlV hA G.scCtl G.tcb9.scBindOwnV,
    decGap_vspace hA Vs G.cdt2.toCdtHyps P.xfer G.irq,
    decGap_vcpuD hA G.ntH P.xfer G.vcpuW G.vcpuSt G.vcpuObj Pd,
    decGap_ept hA,
    decGap_ioPortControl G.cdt2.toCdtHyps,
    decGap_ioPort hA P.xfer,
    decGap_tdx hA P.xfer⟩

/-- **Native kernel entries keep `EntryInv`**, from `InvGaps9` and `P3Place` of every admissible tuple
(`kernel_entry.entry_of`, as `entry_of8A`). **Vacuous** as every `kernel_entry.entry_of*` top: `P3Place` is
contradictory with `BXI` (`blkU`, P1/EntryVacuous's argument). -/
theorem kernel_entry.entry_of9A {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (TX : TmoXGA st ar)
    (GF : ∀ σ : PSets, Adm σ → P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧
      InvGaps9 st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn)
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
