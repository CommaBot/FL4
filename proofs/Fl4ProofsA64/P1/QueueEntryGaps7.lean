/-
P1 (aarch64): **`InvGaps7`**, the A64 entry-gap record with the VCPU family narrowed to two labels: `ReadReg`,
`WriteReg`, `InjectIRQ` (QueueDecVcpuRegA), `ReadState` / `WriteState` (QueueDecVcpuStA) and `AckVPPI`
(QueueDecVcpuA) proved; `SetTCB` and `Run` remain gaps (`VcpuGapsB`).

* `VcpuGapsB`: `SetTCB` and `Run`, one `DecPost` shape each (as `VcpuGapsA.setTcb` / `.run`).
* `decGap_vcpuB`: the family's `DecGap` from `VcpuGapsB`, [P] `VcpuW`, [P] `VcpuStA` and P3Place's `xfer`.
* `InvGaps7` = `InvGaps6` with `vcpuA : VcpuGapsA` replaced by `vcpuB : VcpuGapsB` and **[P] `vcpuSt : VcpuStA`**;
  `InvGaps7.gaps`; **`kernel_entry.entry_of7A`** (as `entry_of6A`).

Why `SetTCB` and `Run` are not proved here (premises found false, see the handoff): a successful `SetTCB` writes the
thread's `VCPU` word (TCB + 3664, `set_bound`) with the VCPU's address, so after it [P] `FinPl`'s "thread caps
name TCBs with no bound VCPU" (read by `W7.R.A5.DelPlaceAt.cap`, the `place` field) is false; a successful `Run`
writes the caller's `RUN_VCPU` word with `vc`, after which [P] `W7.R.A5.DelPlaceAt.rcw` ("`RUN_CALLER` of a run
VCPU is a user word", hence outside `Ω`) contradicts [P] `VcpuW` (the VCPU's words are in `Ω`).

New premise: [P] `VcpuStA` (QueueDecVcpuStA). No other.
-/
import Fl4ProofsA64.P1.QueueDecVcpuStA
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- **The VCPU labels not yet proved**: `SetTCB` and `Run` (the invoked cap a `.Vcpu vc`). -/
structure VcpuGapsB (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) :
    Prop where
  setTcb : ∀ (Ac : Set U64) (s : S) (a : A) (vc : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra →
    vcpu.decode_set_tcb st ar s a vc extra ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄
  run : ∀ (Ac : Set U64) (s : S) (a : A) (vc len : U64) (call : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra →
    vcpu.decode_run st ar s a vc len call buf ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄

/-- **InvGaps' `vcpu` from `SetTCB` / `Run`**: the other six labels proved. -/
theorem decGap_vcpuB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (G : VcpuGapsB st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (W : VcpuW st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pl : VcpuStA st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vcpu := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  rename_i vc
  have hw : VcWords Ω Sg vc := W Ac s vc extra hE D
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  unfold vcpu.decode
  split
  · exact G.setTcb Ac s a vc extra hE D
  split
  · exact vcpu.decode_inject_irq.dec hA D a vc len buf hw
  split
  · exact vcpu.decode_read_reg.dec hA E D hE a vc len call buf
  split
  · exact vcpu.decode_write_reg.dec hA D a vc len buf hw
  split
  · exact vcpu.decode_ack_vppi.dec hA D a vc len buf hw
  split
  · exact vcpu.decode_state_transfer.dec hA Pl D hE hw a len buf true
  split
  · exact vcpu.decode_state_transfer.dec hA Pl D hE hw a len buf false
  split
  · exact G.run Ac s a vc len call buf extra hE D
  · simp only [error.illegal, bind_ok]; exact (WP.spec_ok _).2 (D.err _)

/-- **The A64 entry-gap record with the VCPU family down to `SetTCB` / `Run`** (`InvGaps6` with `vcpuB`,
[P] `vcpuSt`). -/
structure InvGaps7 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Adm : PSets → Prop) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  /-- The deletion placements, [J] `W7.R.A5.VsDel` and [J] `VsPlaceA` (as `InvGaps6.place`). -/
  place : ∃ V : U64 → Prop, W7.R.A5.DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok ∧
    W7.R.A5.VsDel st ar T Cs Ω H Sg Rp Scs Nt Z V P3Ok ∧ VsPlaceA st ar T Cs Ω H Sg Rp Scs Nt Z U V P3Ok
  fin : W7.R.FinGaps4 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok
  cdt2 : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok
  ssp : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  tcb : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  tcb7 : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok
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
  /-- The ARM VCPU's labels not yet proved: `SetTCB`, `Run`. -/
  vcpuB : VcpuGapsB st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- [P] The invoked VCPU's words are aligned words of `Ω` off `Sg` (`VcpuW`). -/
  vcpuW : VcpuW st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- [P] The state transfers' placement facts (`VcpuStA`). -/
  vcpuSt : VcpuStA st T Cs Ω H Sg Rp Scs Nt Z U P3Ok

theorem InvGaps7.gaps {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (P : P3Place st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (G : InvGaps7 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
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
    decGap_vcpuB hA P.xfer G.vcpuB G.vcpuW G.vcpuSt,
    decGap_ept hA,
    decGap_ioPortControl G.cdt2.toCdtHyps,
    decGap_ioPort hA P.xfer,
    decGap_tdx hA P.xfer⟩

/-- **Native kernel entries keep `EntryInv`**, from `InvGaps7` and `P3Place` of every admissible tuple
(`kernel_entry.entry_of`, as `entry_of6A`). -/
theorem kernel_entry.entry_of7A {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (TX : TmoXGA st ar)
    (GF : ∀ σ : PSets, Adm σ → P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧
      InvGaps7 st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn)
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
