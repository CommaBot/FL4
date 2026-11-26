/-
P1 (aarch64): InvGaps' `irqControl`, `irqHandler`, `ioPortControl` and `ioPort` families for the AArch64 GIC.
Rewritten from Fl4Proofs.P1.QueueDecIrq: the x86_64 ISA / MSI-check / IOAPIC arms (`decode_issue_isa`,
`check_msi`, `map_ioapic`) are gone; the A64 `decode_irq_control` (crates/fl4-core/src/arch/aarch64/interrupt.rs
4–49: `IRQIssueIRQHandler`, `ARMIRQIssueIRQHandlerTrigger`, `ARMIRQIssueIRQHandlerTriggerCore`) and
`decode_irq_control_msi` (interrupt.rs 56–90, `GetMSI`: an LPI `LPI_BASE + n`, `n < NUM_LPIS`, mapped by the ITS
last) are proved instead. The IRQ bound is the GIC's `layout::irq::COUNT` = 5376 throughout (x86_64: 128):
`interrupt.set_irq_state.blk` / `.fr` and `invoke_irq_control.blk` for `irq < 5376` (IRQ_STATE 224 + 8·irq <
43232); `layout.irq.of.lt`: `irq::of(id, cpu)` of an interrupt ID `id ≤ 1019` is below 5376 (an SPI is its own
IRQ, a banked one is `1024 + 32·(cpu % 128) + id < 5120`).

The IRQ handler family runs over the `rv`-free deletion forms (`W7.R.Cur0R`, `W7.R.DelPlaceAt`,
`W7.R.cdt.empty_slot.cur0`, `fin_ntfn_obj.rvi`): `cdt.delete_one.irq_cur0R` of the handler slot of any IRQ below
5376 (`irq_slotW_a64`), so no [J] `DelPlaceAt.rv` / `W7.DelPlaceAt.rv` and no `< 128` placement.

The I/O-port families (`ioport.decode_control`, `ioport.decode`) are the shared fl4-core code: x86_64 text.

Named premises:
* **[P] `MaxSpi`** (new, `decGap_irqControl`): the arch's `max_spi` is at most 1019. Source:
  crates/fl4-arch-aarch64/src/gic.rs:115–117 `max_spi() = (lines() - 1).min(1019)` (arch.rs:180 `fn max_spi`);
  1019 is the GIC architecture's last SPI ID. A fact about the trusted `Arch` implementation (P0's
  `ArchTotal.max_spi` only says it returns).
* **[P] `IrqPlace`** (A64 form, `decGap_irqHandler`): `irq`: an IrqHandler cap names an IRQ below 5376
  (`layout::irq::COUNT`; x86_64: 128); `extra`: as x86_64; `slot` (**[P] `IrqSlotAt`**, new): an IRQ's handler
  slot, for every IRQ below 5376, holds no cap or a notification cap (`R.DelPlaceAt.irq` widened from 128 to 5376).
  Plausibility: IrqHandler caps are made only by `invoke_irq_control` (interrupt.rs:48) with the IRQ of
  `decode_irq_control` (`irq::of(irq_w ≤ max_spi ≤ 1019, cpu) < 5120`) or of `GetMSI` (`5120 + n`, `n < 256`),
  and copied unchanged; the IRQ node's slots are written only by `SetIRQHandler` (interrupt.rs:75–84: a
  notification cap after its kind check) and emptied by `delete_one` (interrupt.rs:95, cdt.rs:320).
* `CdtHyps` ([P], as x86_64), `XferHyps` (as x86_64), `W7.R.DelPlace` ([P], unchanged).
No existing statement changed.
-/
import Fl4ProofsA64.P1.QueueSchedCtl
import Fl4ProofsA64.P1.QueueDecCnode
import Fl4ProofsA64.P1.QueueDecDom
import Fl4ProofsA64.P1.QueueFinCur
import Fl4ProofsA64.P1.QueueIrqWide
import Fl4ProofsA64.P1.QueueFinRvReply
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

theorem SlotW.capw0 {x : U64} (h : SlotW T Ω Sg x) : CapW T Ω Sg x := by
  have h0 := h.2 0#u64 (by simp) (by simp)
  have e : core.num.U64.wrapping_add x 0#u64 = x := UScalar.eq_of_val_eq (by
    simp only [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; scalar_tac)
  rwa [e] at h0

/-- The IRQ-state write of an IRQ below 5376 (a64: the GIC's `irq::COUNT`) keeps `BlkOK`. -/
theorem interrupt.set_irq_state.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (v irq : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hi : irq.val < 5376) :
    interrupt.set_irq_state st ar s a v irq ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  unfold interrupt.set_irq_state interrupt.state_off
  simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun o : U64 => o.val = 224 + 8 * irq.val) ?_ fun o ho => ?_
  · refine WP.spec_bind P0.Consts.layout.ks.IRQ_STATE.spec fun b eb => ?_
    subst eb
    refine (WP.spec_ok _).2 ?_
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
  refine WP.spec_bind (obj.ks_set.blk s o v h (by omega) (by omega)) fun s1 h1 => ?_
  exact WP.spec_bind (hA.mask_irq a irq _) fun a1 _ => (WP.spec_ok _).2 h1.1

/-- The IRQ-state write's frame (a kernel-global word). -/
theorem interrupt.set_irq_state.fr {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (v irq : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hi : irq.val < 5376) :
    interrupt.set_irq_state st ar s a v irq ⦃ r => Fr0 st T Cs Ω H Sg Scs Z s r.1 ⦄ := by
  have hb := BlkOK.bxi h
  have q := hb.1.choose_spec.choose_spec
  have hSg := hb.2.2.2.1
  unfold interrupt.set_irq_state interrupt.state_off
  simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun o : U64 => o.val = 224 + 8 * irq.val) ?_ fun o ho => ?_
  · refine WP.spec_bind P0.Consts.layout.ks.IRQ_STATE.spec fun b eb => ?_
    subst eb
    refine (WP.spec_ok _).2 ?_
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
  refine WP.spec_bind (obj.ks_set.spec s o v) fun s1 e1 => ?_
  subst e1
  have ho' : o.val < 223488 := by omega  -- a64: 13568->223488
  have h8 : o.val % 8 = 0 := by omega
  refine WP.spec_bind (hA.mask_irq a irq _) fun a1 _ => (WP.spec_ok _).2 ?_
  exact (writesIn_wr (ks_aligned q ho' h8)).mono fun b e => e ▸ Or.inr (Or.inr (Or.inl (Or.inr
    ⟨hSg.ksΩ o ho' h8, fun hb' => by have := hSg.ks _ hb'; rw [ks_val q ho'] at this; omega⟩)))

/-- **`invoke_irq_control`**: the IRQ-state write and the IrqHandler cap's
insertion under the IrqControl cap's slot. -/
theorem interrupt.invoke_irq_control.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s0 : S} (hE : EntAt st P3Ok s0) (s : S) (a : A)
    (irq handler control : U64) (hf : Fr0 st T Cs Ω H Sg Scs Z s0 s)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hi : irq.val < 5376) (hh : CapW T Ω Sg handler)
    (hc : CapW T Ω Sg control) :
    interrupt.invoke_irq_control st ar s a irq handler control ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold interrupt.invoke_irq_control
  refine WP.spec_bind (WP.spec_and (interrupt.set_irq_state.blk hA s a _ irq h hi)
    (interrupt.set_irq_state.fr hA s a _ irq h hi)) ?_
  rintro ⟨s1, a1⟩ ⟨h1, f1⟩
  try dsimp only
  refine WP.spec_bind (Pₘ := fun s2 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2) ?_ fun s2 h2 => (WP.spec_ok _).2 h2
  unfold cdt.insert
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st control s1 hS) fun c0 _ => ?_
  exact WP.spec_mono (C.ins Ac s0 s1 _ c0 control handler hE (Cur0W.trans hf f1) (BlkOK.bxi h1) hc hh) fun s2 w2 =>
    (blk_of_capw h1 w2 fun _ hb => hb).1


theorem irq_branch_ok {α β : Type} (x : α) :
    core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Ok x : core.result.Result α β) =
      ok (core.ops.control_flow.ControlFlow.Continue x) := rfl

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errI" : tactic => `(tactic| first
  | exact D.err _
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
      error.illegal, error.truncated, error.range, error.invalid_cap, error.invalid_arg]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

set_option hygiene false in
/-- The issue tail, from the target slot's lookup: the empty check, the
arch-specific step `m` (keeping `BlkOK`, or an error with `s`), then the
invocation. -/
local macro "irqtail" : tactic => `(tactic| (
  refine WP.spec_bind (C.tgt Ac s _ _ _ hE D.bxi) fun r hr => ?_
  rcases r with v | e
  swap
  · errI
  have hv := hr v rfl
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_bind (P0.cdt.ensure_empty_slot.p0 st s v hS) fun r1 _ => ?_
  rcases r1 with _ | e
  swap
  · errI
  simp only [irq_branch_ok, bind_ok]))


/-! ## The IRQ control family (AArch64 GIC) -/

/-- **[P] (a64) `MaxSpi`**: the interrupt controller's largest SPI ID is at most 1019 (the GIC architecture's
last SPI). crates/fl4-arch-aarch64/src/gic.rs:115–117: `max_spi() = (lines() - 1).min(1019)`. -/
def MaxSpi {A : Type _} (ar : machine.Arch A) : Prop := ∀ a, ar.max_spi a ⦃ m => m.val ≤ 1019 ⦄

theorem le1019_of {x m : U64} (h : ¬ x > m) (hm : m.val ≤ 1019) : x.val ≤ 1019 := by
  simp only [gt_iff_lt, not_lt] at h; scalar_tac

/-- `irq::of` of an interrupt ID up to 1019 (an SPI, or a banked SGI/PPI of the core `cpu % 128`) is an IRQ below
`layout::irq::COUNT` = 5376. -/
theorem layout.irq.of.lt {id : U64} (cpu : U64) (h : id.val ≤ 1019) :
    layout.irq.of id cpu ⦃ i => i.val < 5376 ⦄ := by
  unfold layout.irq.of
  have h1 : ¬ (id >= layout.irq.LPI_ID_BASE) := by
    simp only [layout.irq.LPI_ID_BASE, ge_iff_le, not_le]; scalar_tac
  rw [if_neg h1]
  by_cases h2 : id < layout.irq.NUM_BANKED
  · rw [if_pos h2]
    simp only [layout.irq.NUM_BANKED, layout.irq.BANKED_CORES, layout.irq.BANKED_BASE] at h2 ⊢
    step as ⟨q, hq⟩
    simp only [lift, bind_ok]
    refine (WP.spec_ok _).2 ?_
    have hq' : q.val < 128 := by scalar_tac
    have h2' : id.val < 32 := by scalar_tac
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    omega
  · rw [if_neg h2]
    exact (WP.spec_ok _).2 (by scalar_tac)

/-- The IRQ-trivial binds of the decode (labels, argument reads, the bound selections). -/
syntax "a64triv" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| a64triv) => `(tactic| first
      | exact (WP.spec_ok _).2 trivial
      | exact P0.msg.syscall_arg.p0 st s _ buf _ hS
      | exact hA.configure_irq _ _ _ _
      | (refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_; a64triv)
      | (refine spec_ite (fun _ => ?_) (fun _ => ?_) <;> a64triv)
      | (refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun _ _ => ?_ <;> a64triv))

set_option hygiene false in
/-- The A64 issue tail, from `let irq ← irq::of irq_w cpu` (with `hmx : irq_w ≤ 1019` in scope): the active
check, the target slot, the restart, the arch's trigger/route configuration, the invocation. -/
local macro "gicTail" : tactic => `(tactic| (
  refine WP.spec_bind (layout.irq.of.lt _ hmx) fun irq hi => ?_
  refine WP.spec_bind (P0.interrupt.is_irq_active.p0 st s irq hS) fun b _ => ?_
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · errI
  irqtail
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
    (runnable_ok D.run).2) fun s1 h1 => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by a64triv) fun a1 _ => ?_
  refine WP.spec_bind (interrupt.invoke_irq_control.blk hA C hE s1 a1 irq v slot
    (Foot.cur0w h1.2.1 (Set.empty_subset _)) h1.1 hi hv hslot) ?_
  rintro ⟨s2, a2⟩ h2
  exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h2))))

/-- The decode's walk: every leaf is an error with the state unchanged or the issue tail. -/
syntax "gicR" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| gicR) => `(tactic| first
      | gicTail
      | (refine WP.spec_bind (hM a) fun mx hmx0 => ?_
         refine spec_ite (fun hgt => ?_) (fun hgt => ?_)
         · errI
         have hmx := le1019_of hgt hmx0
         gicR)
      | (refine spec_ite (fun _ => ?_) (fun _ => ?_) <;> gicR)
      | (refine WP.spec_bind (P0.obj.ks_get.p0 st s _ hS) fun _ _ => ?_; gicR)
      | (refine WP.spec_bind (P0.interrupt.extra0.p0 st s extra hS) fun o _ => ?_
         rcases o with _ | c <;> gicR)
      | (refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_; gicR)
      | (refine WP.spec_bind (Pₘ := fun _ => True) (by a64triv) fun ⟨_, _, _⟩ _ => ?_; gicR)
      | (refine WP.spec_bind (Pₘ := fun _ => True) (by a64triv) fun _ _ => ?_; gicR)
      | errI)

set_option maxHeartbeats 4000000 in
/-- **`decode_irq_control_msi`** (FL4 `GetMSI`): the LPI `LPI_BASE + n` (`n < 256`, so below 5376), the target
slot, the ITS mapping (an arch call; a refusal is an error with the state unchanged), the restart, the
invocation. -/
theorem interrupt.decode_irq_control_msi.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (len src buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) (hsrc : CapW T Ω Sg src) :
    interrupt.decode_irq_control_msi st ar s a len src buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  unfold interrupt.decode_irq_control_msi
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.interrupt.extra0.p0 st s extra hS) fun o _ => ?_
  rcases o with _ | c
  · errI
  try dsimp only
  split
  swap
  · errI
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun n _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun device _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun event _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun index _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun i4 _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun cpu _ => ?_
  split
  · step as ⟨i1, _⟩
    errI
  rename_i hn
  have hn' : n.val < 256 := by simp only [layout.irq.NUM_LPIS, ge_iff_le, not_le] at hn; scalar_tac
  refine WP.spec_bind (P0.obj.ks_get.p0 st s _ hS) fun nn _ => ?_
  split
  · errI
  refine WP.spec_bind P0.Consts.layout.irq.LPI_BASE.spec fun i2 ei2 => ?_
  subst ei2
  step as ⟨irq, eirq⟩
  have hi : irq.val < 5376 := by scalar_tac
  refine WP.spec_bind (P0.interrupt.is_irq_active.p0 st s irq hS) fun b _ => ?_
  split
  · errI
  irqtail
  refine WP.spec_bind (hA.msi_map a irq device event cpu) ?_
  rintro ⟨i3, a1⟩ _
  try simp only [uncurry_apply_pair]
  try dsimp only
  split
  · refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
      (runnable_ok D.run).2) fun s1 h1 => ?_
    refine WP.spec_bind (interrupt.invoke_irq_control.blk hA C hE s1 a1 irq v src
      (Foot.cur0w h1.2.1 (Set.empty_subset _)) h1.1 hi hv hsrc) ?_
    rintro ⟨s2, a2⟩ h2
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h2))
  all_goals errI

set_option maxHeartbeats 16000000 in
/-- **`decode_irq_control`** (AArch64) keeps the invariants, from [P] `MaxSpi`. -/
theorem interrupt.decode_irq_control.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hM : MaxSpi ar) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len slot buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) (hslot : CapW T Ω Sg slot) :
    interrupt.decode_irq_control st ar s a lbl len slot buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  unfold interrupt.decode_irq_control
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · exact interrupt.decode_irq_control_msi.dec hA C a len slot buf D hE hslot
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  gicR

/-- **InvGaps' `irqControl`, discharged** (AArch64) from the CSpace placement facts and [P] `MaxSpi`. -/
theorem decGap_irqControl {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hM : MaxSpi ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .irqControl := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D hslot hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  exact interrupt.decode_irq_control.dec hA hM C a lbl len slot buf D hE (SlotW.capw0 hslot)


/-! ## The IRQ handler family (AArch64: IRQs below 5376, `rv`-free deletion forms) -/

/-- **[P] (a64) `IrqSlotAt`**: along a decode started at `s0`, the handler slot of every IRQ below
`layout::irq::COUNT` = 5376 holds no cap or a notification cap (`W7.R.DelPlaceAt.irq` for the GIC's IRQ range;
the IRQ node's slots are written only by `SetIRQHandler`, interrupt.rs:75–84, and `delete_one`). -/
def IrqSlotAt (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop :=
  ∀ (Ac : Set U64) (s : S) (i : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    i.val < 5376 →
    obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => c = .Null ∨ ∃ n b0 b1 b2, c = .Notification n b0 b1 b2 ⦄

/-- **[P] (a64) The IRQ handler family's placement facts** (P3's `valid_cap` of an IrqHandler cap: its IRQ is
below the GIC's `layout::irq::COUNT` = 5376; the extra caps' slots are cap slots, from `lookup_extra_caps`, also
the VSpace / VCPU families'; the IRQ node's slots, `IrqSlotAt`). -/
structure IrqPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  irq : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ i, cap = .IrqHandler i → i.val < 5376
  extra : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ sl ∈ extra.val, sl ≠ 0#u64 →
      CapSlotW T Ω Sg sl
  slot : ∀ s0, EntAt st P3Ok s0 → IrqSlotAt st T Cs Ω H Sg Rp Scs Nt Z s0

/-- **`delete_one` of an IRQ's handler slot** (IRQ below 5376) over `Cur0R`: no cap, or a notification cap's
finalisation (`fin_ntfn_obj.cur0` ∧ `.rvi`) and the slot's emptying (`W7.R.cdt.empty_slot.cur0`). -/
theorem cdt.delete_one.irq_cur0R {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : W7.R.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (Q : IrqSlotAt st T Cs Ω H Sg Rp Scs Nt Z s0)
    {a : A} {irq : U64} (h : W7.R.Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hi : irq.val < 5376) :
    cdt.delete_one st ar s a (irqSlotA (L.ksb s) irq) ⦃ r => W7.R.Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  have hW := W7.slotW_to7 (irq_slotW_a64 hb hi)
  unfold cdt.delete_one
  refine WP.spec_bind (WP.spec_and (Q Ac' s irq h.fr hb hi) (P.cap Ac' s _ h.fr hb hW)) fun c ⟨hc', hcd⟩ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s _ c hS) fun f _ => ?_
  rcases hc' with rfl | ⟨n, b0, b1, b2, rfl⟩
  · simp [objects.finalise_cap_object]
    exact W7.R.cdt.empty_slot.cur0 hA P h hW W7.DelCapOK.null
  · obtain ⟨hn, hH⟩ := hcd.1.1.2.1 n b0 b1 b2 rfl
    refine WP.spec_bind (WP.spec_and (fin_ntfn_obj.cur0 (ar := ar) (a := a) (fin := f) (b0 := b0) (b1 := b1)
      (b2 := b2) h.1 hn hH) (fin_ntfn_obj.rvi (ar := ar) s a n b0 b1 b2 f hb.blk hn hH h.2)) ?_
    rintro ⟨_, s1, a1⟩ ⟨⟨_, h1⟩, r1⟩
    exact W7.R.cdt.empty_slot.cur0 hA P ⟨h1, r1⟩ hW W7.DelCapOK.null

set_option maxHeartbeats 4000000 in
/-- **`decode_irq_handler`** (Ack, SetIRQHandler, ClearIRQHandler) keeps the invariants (AArch64: the IRQ below
5376; the handler slot's deletion over `W7.R.Cur0R`, so no [J] `DelPlaceAt.rv`). -/
theorem interrupt.decode_irq_handler.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {V : U64 → Prop} {s : S}
    (P : W7.R.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s) (Q : IrqSlotAt st T Cs Ω H Sg Rp Scs Nt Z s)
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl irq : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) (hi : irq.val < 5376)
    (hx : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl) :
    interrupt.decode_irq_handler st ar s a lbl irq extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold interrupt.decode_irq_handler
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  split
  · refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    refine WP.spec_bind (hA.mask_irq a irq false) fun a1 _ => ?_
    exact (WP.spec_ok _).2 h1.post
  split
  · have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl hsl => ?_
    have hmem : sl ∈ extra.val := hsl ▸ List.getElem_mem hl0
    simp only [obj.Slot.is_null, bind_ok]
    split
    · errI
    rename_i h0
    have hne : sl ≠ 0#u64 := by simpa using h0
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st sl s hS) fun c _ => ?_
    rcases c with _ | _ | _ | ⟨n, b0, b1, b2⟩
    all_goals try (simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (D.err _))
    all_goals try errI
    try dsimp only
    split
    swap
    · errI
    refine WP.spec_bind (W7.R.Cur0R.restart D) fun s1 h1 => ?_
    refine WP.spec_bind (interrupt.irq_slot.val s1 irq) fun isl e => ?_
    subst e
    obtain ⟨Ac1, hb1⟩ := h1.bxi
    have hW := (irq_slotW_a64 hb1 hi).capw0
    refine WP.spec_bind (cdt.delete_one.irq_cur0R hA P Q h1 hi) ?_
    rintro ⟨s2, a1⟩ h2
    try simp only [uncurry_apply_pair]
    obtain ⟨Ac2, hb2⟩ := h2.bxi
    refine WP.spec_bind (Pₘ := fun s3 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s3) ?_
      fun s3 h3 => (WP.spec_ok _).2 h3.post
    unfold cdt.insert
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st sl s2 hS) fun c0 _ => ?_
    exact WP.spec_mono (C.ins Ac2 s s2 _ c0 sl _ hE h2.fr hb2 (hx sl hmem hne) hW) fun s3 w =>
      h2.1.capw w fun _ hb => hb
  split
  · refine WP.spec_bind (W7.R.Cur0R.restart D) fun s1 h1 => ?_
    refine WP.spec_bind (interrupt.irq_slot.val s1 irq) fun isl e => ?_
    subst e
    refine WP.spec_bind (cdt.delete_one.irq_cur0R hA P Q h1 hi) ?_
    rintro ⟨s2, a1⟩ h2
    exact (WP.spec_ok _).2 h2.post
  · errI

/-- **InvGaps' `irqHandler`, discharged** (AArch64) from the CSpace placement facts, the `rv`-free deletion
placement `W7.R.DelPlace` and [P] `IrqPlace` (IRQs below 5376). -/
theorem decGap_irqHandler {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {V : U64 → Prop}
    (P : W7.R.DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (Pl : IrqPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .irqHandler := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  rename_i irq
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  exact interrupt.decode_irq_handler.dec hA C (P s hE) (Pl.slot s hE) a lbl irq D hE (Pl.irq _ _ _ _ hE D irq rfl)
    (fun sl h1 h2 => SlotW.capw0 (Pl.extra _ _ _ _ hE D sl h1 h2))


/-! ## The I/O port families -/

theorem mask16_lt (i : U64) : (i &&& 65535#u64).val < 65536 := by
  rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

set_option maxHeartbeats 4000000 in
/-- **`ioport.decode_control`** (IOPortControl_Issue) keeps the invariants:
the restart, the I/O-port bitmap words (`set_mask.cur0`) and the IoPort cap's
insertion under the control cap's slot. -/
theorem ioport.decode_control.dec (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {A : Type _} {ar : machine.Arch A}
    {s : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len slot buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) (hslot : CapW T Ω Sg slot) :
    ioport.decode_control st ar s a lbl len slot buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ioport.decode_control
  split
  · errI
  split
  · errI
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · errI
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun i0 _ => ?_
  simp only [lift, bind_ok]
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun i1 _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st sl s hS) fun cn _ => ?_
  split
  · errI
  rename_i hlf
  have hfl : (i0 &&& 65535#u64).val ≤ (i1 &&& 65535#u64).val := Nat.le_of_not_lt fun h => hlf h
  refine WP.spec_bind (P0.ioport.range_free.p0 st s _ _ hS) fun b1 _ => ?_
  split
  swap
  · errI
  irqtail
  refine WP.spec_bind (Cur0.restart D) fun s2 h2 => ?_
  refine WP.spec_bind (ioport.set_mask.cur0 h2 (mask16_lt i1) hfl) fun s3 h3 => ?_
  obtain ⟨Ac3, hb3⟩ := h3.bxi
  refine WP.spec_bind (Pₘ := fun s4 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s4) ?_
    fun s4 h4 => (WP.spec_ok _).2 h4.post
  unfold cdt.insert
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st slot s3 hS) fun c0 _ => ?_
  exact WP.spec_mono (C.ins Ac3 s s3 _ c0 slot v hE h3.fr hb3 hslot hv) fun s4 w => h3.capw w fun _ hb => hb

/-- **InvGaps' `ioPortControl`, discharged** from the CSpace placement facts. -/
theorem decGap_ioPortControl {A : Type _} {ar : machine.Arch A} (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ioPortControl := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D hslot hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  exact ioport.decode_control.dec C a lbl len slot buf D hE (SlotW.capw0 hslot)

set_option maxHeartbeats 4000000 in
/-- **`ioport.decode`** (the port reads and writes) keeps the invariants: the
restart, the arch's port access, for a read with a reply the current
thread's message registers (`XS`), then the thread set running. -/
theorem ioport.decode.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len : U64) (first last x : U64) (call : Bool)
    (buf : U64) (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) :
    ioport.decode st ar s a lbl len (.IoPort first last x) call buf ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  unfold ioport.decode
  try dsimp only
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.ioport.port_size.p0 lbl) fun size _ => ?_
  split
  · errI
  refine WP.spec_bind (P0.ioport.is_port_in.p0 lbl) fun isin _ => ?_
  split
  · split
    · errI
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun i0 _ => ?_
    simp only [lift, bind_ok]
    refine WP.spec_bind (P0.ioport.allowed.p0 first last _ size) fun r _ => ?_
    rcases r with _ | e
    swap
    · errI
    simp only [irq_branch_ok, bind_ok]
    refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
      (runnable_ok D.run).2) fun s1 ⟨h1, f1, hst1, _⟩ => ?_
    obtain ⟨Q, R, x1⟩ := BXI.xs (sx := 0#u64) (BlkOK.bxi h1) (D.user.ksb f1.1)
    refine WP.spec_bind (hA.port_in a _ size) ?_
    rintro ⟨v, a1⟩ _
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (Pₘ := fun s2 => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R 0#u64 s1 s2) ?_ ?_
    · split
      · refine WP.spec_bind (E.buf Ac ∅ Q R s1 _ (hE.xg.foot (f1.mono (Set.empty_subset _))) x1.1 hct) fun b hb => ?_
        refine WP.spec_bind (obj.Tcb.set_reg.xs (v := 0#u64) x1 hct (by simp [layout.reg.BADGE, layout.reg.X0]))
          fun s3 x3 => ?_
        refine WP.spec_bind (msg.set_mr.xs x3 hct hb (by simp)) ?_
        rintro ⟨n, s4⟩ ⟨x4, -⟩
        try simp only [uncurry_apply_pair]
        refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
        unfold msg.set_msg_info
        exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
          obj.Tcb.set_reg.xs (v := w) x4 hct (by simp [layout.reg.MSG_INFO, layout.reg.X1])
      · exact (WP.spec_ok _).2 x1
    intro s2 x2
    have hst : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART := by
      rw [stA_eq, x2.fr.2.2.2.2.1 _ hct _ (by simp) (by simp) (by simp) (fun _ => by simp), ← stA_eq, hst1]
    refine WP.spec_bind (sched.set_thread_state.running_bxi x2.bxi hct hst) fun s3 h3 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi h3)
  · split
    · errI
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun i0 _ => ?_
    simp only [lift, bind_ok]
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun raw _ => ?_
    refine WP.spec_bind (P0.ioport.allowed.p0 first last _ size) fun r _ => ?_
    rcases r with _ | e
    swap
    · errI
    simp only [irq_branch_ok, bind_ok]
    refine WP.spec_bind (Pₘ := fun _ => True) (by
      split
      · exact (WP.spec_ok _).2 trivial
      · split <;> exact (WP.spec_ok _).2 trivial) fun data _ => ?_
    refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
      (runnable_ok D.run).2) fun s1 h1 => ?_
    refine WP.spec_bind (hA.port_out a _ size data) fun a1 _ => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h1.1))

/-- **InvGaps' `ioPort`, discharged** from the transfer's placement facts
(the IPC buffer of a port read's reply). -/
theorem decGap_ioPort {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ioPort := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  rename_i first last x
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  exact ioport.decode.dec hA E a lbl len first last x call buf D hE

end

end Fl4ProofsA64.P1
