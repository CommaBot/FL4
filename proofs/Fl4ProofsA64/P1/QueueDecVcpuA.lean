/-
P1 (aarch64): **the ARM VCPU family, by label** (`vcpu.decode`, crates/fl4-core/src/arch/aarch64/vcpu.rs:871–:
`SetTCB`, `InjectIRQ`, `ReadReg`, `WriteReg`, `AckVPPI`, `ReadState` / `WriteState`, `Run`), and **`InvGaps6`**,
the A64 entry-gap record whose `vcpu` field is narrowed from one `DecGap .vcpu` to per-label gaps with `AckVPPI`
proved.

* `vcpu.stall_vcpu.stalled`: `stall_vcpu` (two `remote_tcb_stall`s and the arch's `vcpu_flush`, vcpu.rs:281–291)
  from a `Stalled` state stays `Stalled` (`Stalled.stall`).
* `Stalled.restartT`: the caller's restart (`set_thread_state ct TS_RESTART`, `ct` read before the stall) after a
  stall is a `Cur0` state (as `Stalled.restart0`, which is about `tcb.restart_caller`).
* **`vcpu.decode_ack_vppi.dec`** (vcpu.rs:519–533): the argument checks (error, state kept), the stall, the
  restart, and one write of the VCPU word `vc + VPPI_MASKED` (`Cur0.capw`, the word in `Ω \ Sg` by [P]
  `VcpuW`).
* `VcpuGapsA`: the other labels, one `DecPost` shape each (not yet proved: SetTCB's unbind / `complete_run`,
  InjectIRQ's VGIC list registers, Read/WriteReg, the state transfers' frame copies, Run's `RUN_VCPU` /
  `RUN_CALLER` handover); `decGap_vcpuA`: the family's `DecGap` from them, `AckVPPI` and `VcpuW`.
* `InvGaps6` = `InvGaps5` with `vcpu : DecGap .vcpu` replaced by `vcpuA : VcpuGapsA` and **[P] `vcpuW : VcpuW`**;
  `InvGaps6.gaps`; `kernel_entry.entry_of6A` (as `entry_of5A`).

New premise: **[P] `VcpuW`**: at a decode start, the invoked `.Vcpu vc` cap's object words `vc + o` (`o < 4096`,
8-aligned) are aligned words of `Ω` off `Sg`. Source: a `Vcpu` cap is made only by retype of `ArmVcpu`
(objects.rs:51–53, `Cap::Vcpu { ptr: base }` of a fresh 2^`bits::VCPU` = 4 KiB object, `.other 12` in QueueRetype's
`newKind`), and copies keep `ptr`; `.other` objects' aligned words are `Heap.omega` words and no frame (`Sg`) word
(QueueHeap `Heap.omega` / `Heap.frame`). Not false at reachable states as far as checked (the A64 forms keep `Ω`
abstract, so this is stated rather than derived from `HeapOK` as x86's QueueDecVcpu does).
-/
import Fl4ProofsA64.P1.QueueEntryGaps5
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- **[P] (a64) The invoked VCPU's words** (module docstring): at a decode start reached from a `P3Ok` entry, the
words `vc + o` (`o < 4096`, 8-aligned) of an invoked `.Vcpu vc` cap are aligned words of `Ω` off `Sg`. -/
def VcpuW (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop :=
  ∀ (Ac : Set U64) (s : S) (vc : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra →
    ∀ o : U64, o.val < 4096 → o.val % 8 = 0 →
      Aligned (core.num.U64.wrapping_add vc o) ∧ core.num.U64.wrapping_add vc o ∈ Ω ∧
        core.num.U64.wrapping_add vc o ∉ Sg

/-- The decode's start is `Stalled` from itself. -/
theorem Stalled.refl0 {s : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s :=
  ⟨D.bxi, rfl, rfl, rfl, fun _ _ _ _ _ => rfl, WritesIn.refl _ _⟩

/-- **`stall_vcpu`** from a stalled state stays stalled. -/
theorem vcpu.stall_vcpu.stalled {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s s1 : S} {a1 : A}
    {vc : U64} (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    vcpu.stall_vcpu st ar s1 a1 vc ⦃ r => Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 ⦄ := by
  unfold vcpu.stall_vcpu
  simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s1 _) fun t _ => ?_
  refine WP.spec_bind (Pₘ := fun r : S × A => Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1) ?_ ?_
  · split
    · exact WP.spec_mono (Stalled.stall hA h1) fun r hr => by obtain ⟨s2, a2⟩ := r; exact hr
    · exact (WP.spec_ok _).2 h1
  rintro ⟨s2, a2⟩ h2
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (LawfulStore.read_spec s2 _) fun c _ => ?_
  refine WP.spec_bind (Pₘ := fun r : S × A => Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1) ?_ ?_
  · split
    · exact WP.spec_mono (Stalled.stall hA h2) fun r hr => by obtain ⟨s3, a3⟩ := r; exact hr
    · exact (WP.spec_ok _).2 h2
  rintro ⟨s3, a3⟩ h3
  try simp only [uncurry_apply_pair]
  exact WP.spec_bind (hA.vcpu_flush a3 vc) fun a4 _ => (WP.spec_ok _).2 h3

/-- The caller's restart after a stall (the thread read at the decode's start) is a `Cur0` state. -/
theorem Stalled.restartT {s s1 : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    sched.set_thread_state st s1 (L.curW s) sched.TS_RESTART ⦃ s2 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s2 ⦄ := by
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have est : L.mem s1 (stA (L.curW s)) = L.mem s (stA (L.curW s)) := by
    rw [stA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  have hr := runnable_ok D.run
  refine WP.spec_mono (sched.set_thread_state.restart_blk (Es := ∅) s1 _ h1.bxi.blk hct (est ▸ hr.1) (est ▸ hr.2))
    fun s2 ⟨h2, f2, est2, k⟩ => ?_
  refine ⟨D.hcsc, Ac, BlkOK.bxi h2, k.curW.trans h1.cur, k.cscW.trans h1.csc, Or.inl ?_, fun y hy => ?_,
    by rw [est2]; exact nbr_restart,
    Cur0W.trans (WritesIn.mono h1.node fun _ hb => NodeW.cur0w D.bxi.1.choose_spec.choose_spec.cur hb)
      (WritesIn.mono f2 fun _ hb => Or.inl (KW.mono hb (Set.empty_subset _)))⟩
  · rw [k.scf hct, scA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  · rcases k.act with e | e
    · rw [e, h1.act, D.act]; exact fun e' => notT_small hT (by simp) (e' ▸ hy)
    · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hy)

set_option maxHeartbeats 1000000 in
/-- **`AckVPPI`** keeps the invariants: the checks, the stall, the restart, the `VPPI_MASKED` word. -/
theorem vcpu.decode_ack_vppi.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S}
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (a : A) (vc len buf : U64)
    (hw : ∀ o : U64, o.val < 4096 → o.val % 8 = 0 →
      Aligned (core.num.U64.wrapping_add vc o) ∧ core.num.U64.wrapping_add vc o ∈ Ω ∧
        core.num.U64.wrapping_add vc o ∉ Sg) :
    vcpu.decode_ack_vppi st ar s a vc len buf ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.decode_ack_vppi
  split
  · simp only [error.truncated, bind_ok]; exact (WP.spec_ok _).2 (D.err _)
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun irq _ => ?_
  split
  · simp only [error.invalid_arg, bind_ok]; exact (WP.spec_ok _).2 (D.err _)
  refine WP.spec_bind (vcpu.stall_vcpu.stalled hA (Stalled.refl0 D)) ?_
  rintro ⟨s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (Stalled.restartT D h1) fun s2 h2 => ?_
  simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s2 _) fun m _ => ?_
  refine WP.spec_bind (LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
  subst e3
  have hx := hw vcpu.VPPI_MASKED (by simp [vcpu.VPPI_MASKED]) (by simp [vcpu.VPPI_MASKED])
  exact (WP.spec_ok _).2 ((h2.capw (writesIn_wr hx.1) fun b e => by subst e; exact Or.inr ⟨hx.2.1, hx.2.2⟩).post)

/-- **The VCPU labels not yet proved**, one `DecPost` shape each (the invoked cap a `.Vcpu vc`). -/
structure VcpuGapsA (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) :
    Prop where
  setTcb : ∀ (Ac : Set U64) (s : S) (a : A) (vc : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra →
    vcpu.decode_set_tcb st ar s a vc extra ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄
  injectIrq : ∀ (Ac : Set U64) (s : S) (a : A) (vc len buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra →
    vcpu.decode_inject_irq st ar s a vc len buf ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄
  readReg : ∀ (Ac : Set U64) (s : S) (a : A) (vc len : U64) (call : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra →
    vcpu.decode_read_reg st ar s a vc len call buf ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄
  writeReg : ∀ (Ac : Set U64) (s : S) (a : A) (vc len buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra →
    vcpu.decode_write_reg st ar s a vc len buf ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄
  state : ∀ (Ac : Set U64) (s : S) (a : A) (vc len buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (rd : Bool), EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra →
    vcpu.decode_state_transfer st ar s a vc len buf extra rd ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄
  run : ∀ (Ac : Set U64) (s : S) (a : A) (vc len : U64) (call : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra →
    vcpu.decode_run st ar s a vc len call buf ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄

/-- **InvGaps' `vcpu` from the per-label gaps**, `AckVPPI` proved (`vcpu.decode_ack_vppi.dec`, [P] `VcpuW`). -/
theorem decGap_vcpuA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : VcpuGapsA st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (W : VcpuW st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vcpu := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  rename_i vc
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  unfold vcpu.decode
  split
  · exact G.setTcb Ac s a vc extra hE D
  split
  · exact G.injectIrq Ac s a vc len buf extra hE D
  split
  · exact G.readReg Ac s a vc len call buf extra hE D
  split
  · exact G.writeReg Ac s a vc len buf extra hE D
  split
  · exact vcpu.decode_ack_vppi.dec hA D a vc len buf (W Ac s vc extra hE D)
  split
  · exact G.state Ac s a vc len buf extra true hE D
  split
  · exact G.state Ac s a vc len buf extra false hE D
  split
  · exact G.run Ac s a vc len call buf extra hE D
  · simp only [error.illegal, bind_ok]; exact (WP.spec_ok _).2 (D.err _)

/-- **The A64 entry-gap record with the VCPU family by label** (the earlier record with `vcpuA`, [P] `vcpuW`; `AckVPPI` proved). -/
structure InvGaps6 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
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
  /-- The ARM VCPU's labels not yet proved (`AckVPPI` is, `decGap_vcpuA`). -/
  vcpuA : VcpuGapsA st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  /-- [P] The invoked VCPU's words are aligned words of `Ω` off `Sg` (`VcpuW`). -/
  vcpuW : VcpuW st T Cs Ω H Sg Rp Scs Nt Z U P3Ok

theorem InvGaps6.gaps {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (P : P3Place st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (G : InvGaps6 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
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
    decGap_vcpuA hA G.vcpuA G.vcpuW,
    decGap_ept hA,
    decGap_ioPortControl G.cdt2.toCdtHyps,
    decGap_ioPort hA P.xfer,
    decGap_tdx hA P.xfer⟩

/-- **Native kernel entries keep `EntryInv`**, from `InvGaps6` and `P3Place` of every admissible tuple
(`kernel_entry.entry_of`, as `entry_of4`). -/
theorem kernel_entry.entry_of6A {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (TX : TmoXGA st ar)
    (GF : ∀ σ : PSets, Adm σ → P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧
      InvGaps6 st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn)
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
