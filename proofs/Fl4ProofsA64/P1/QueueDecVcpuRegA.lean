/-
P1 (aarch64): the ARM VCPU's register labels — **`ReadReg`**, **`WriteReg`**, **`InjectIRQ`**
(crates/fl4-core/src/arch/aarch64/vcpu.rs:401–517) — keep the invariants.

All three are: argument checks (error, state kept), the VCPU stall (`vcpu.stall_vcpu.stalled`), the caller's
restart (`Stalled.restartT`, a `Cur0` state), then VCPU object words and a reply:

* `vcpu.reg_addr.offA`: `reg_addr vc idx` with `idx < 64` (every register index `vcpu_reg::*` is
  `< NUM = 64`) is `vc + o`, `o < 4096` 8-aligned (`REGS = 64`, vcpu.rs:22/92);
* `vcpu.reg_set.cur0A`: such a write keeps `Cur0` (`Cur0.capw`; the word is in `Ω \ Sg` by the VCPU's words
  hypothesis, `VcpuW` of QueueDecVcpuA at the decode start);
* `vcpu.sync_vgic_status.cur0A` (vcpu.rs:206–261): reads of the list registers, then three register writes
  (`VGIC_ELRSR` / `VGIC_EISR` / `VGIC_MISR`);
* `vcpu.reply1.bxiA`: `vcpu.reply1` is `vspace.reply1`'s text (vcpu.rs:367–375), so QueueDecVs's proof applies;
* **`vcpu.decode_read_reg.dec`**, **`vcpu.decode_write_reg.dec`**, **`vcpu.decode_inject_irq.dec`**.

No new premise: the VCPU words are QueueDecVcpuA's [P] `VcpuW` (passed as `hw`), the reply's facts
QueueXfer's `XferHyps` (P3Place's `xfer`).
-/
import Fl4ProofsA64.P1.QueueDecVcpuA
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- The words `vc + o` of a VCPU object (`o < 4096`, 8-aligned) are aligned words of `Ω` off `Sg`. -/
def VcWords (Ω Sg : Set U64) (vc : U64) : Prop :=
  ∀ o : U64, o.val < 4096 → o.val % 8 = 0 →
    Aligned (core.num.U64.wrapping_add vc o) ∧ core.num.U64.wrapping_add vc o ∈ Ω ∧
      core.num.U64.wrapping_add vc o ∉ Sg

/-- `wrapping_add` reassociates when the offsets do not wrap (as x86's `wadd_assoc`). -/
theorem waddA_assoc (v a b : U64) (h : a.val + b.val < 2 ^ 64) :
    core.num.U64.wrapping_add (core.num.U64.wrapping_add v a) b =
      core.num.U64.wrapping_add v (core.num.U64.wrapping_add a b) := by
  apply UScalar.eq_of_val_eq
  have ha : (core.num.U64.wrapping_add a b).val = a.val + b.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  simp only [core.num.U64.wrapping_add_val_eq, ha]
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- A register index below 64 names a VCPU word. -/
theorem vcpu.reg_addr.offA (vc idx : U64) (hi : idx.val < 64) :
    ∃ o : U64, o.val < 4096 ∧ o.val % 8 = 0 ∧
      vcpu.reg_addr vc idx = ok (core.num.U64.wrapping_add vc o) := by
  have hm : (core.num.U64.wrapping_mul idx 8#u64).val = idx.val * 8 := by
    simp [core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
  have hR : vcpu.REGS.val = 64 := by simp [vcpu.REGS]
  have ho : (core.num.U64.wrapping_add vcpu.REGS (core.num.U64.wrapping_mul idx 8#u64)).val = 64 + idx.val * 8 := by
    simp only [core.num.U64.wrapping_add_val_eq, hm, hR]
    exact Nat.mod_eq_of_lt (by simp [U64.size_def, U64.numBits]; omega)
  refine ⟨core.num.U64.wrapping_add vcpu.REGS (core.num.U64.wrapping_mul idx 8#u64), by omega, by omega, ?_⟩
  unfold vcpu.reg_addr
  simp only [lift, bind_ok]
  rw [waddA_assoc vc _ _ (by rw [hR, hm]; omega)]

/-- **A VCPU register write keeps `Cur0`.** -/
theorem vcpu.reg_set.cur0A {s0 s : S} {vc idx v : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hw : VcWords Ω Sg vc) (hi : idx.val < 64) :
    vcpu.reg_set st s vc idx v ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  obtain ⟨o, ho, h8, e⟩ := vcpu.reg_addr.offA vc idx hi
  have hx := hw o ho h8
  unfold vcpu.reg_set
  rw [e, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e' => ?_
  subst e'
  exact h.capw (writesIn_wr hx.1) fun b eb => by subst eb; exact Or.inr ⟨hx.2.1, hx.2.2⟩

set_option maxHeartbeats 2000000 in
/-- **`sync_vgic_status`** keeps `Cur0`: reads, then the `ELRSR` / `EISR` / `MISR` register writes. -/
theorem vcpu.sync_vgic_status.cur0A {s0 s : S} {vc lrs : U64} {g : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hw : VcWords Ω Sg vc) (hl : lrs.val ≤ 64) :
    vcpu.sync_vgic_status st s vc lrs g ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.sync_vgic_status
  refine WP.spec_bind (Pₘ := fun _ => True)
    (WP.spec_mono (P0.vcpu.sync_vgic_status_loop.p0 st s vc lrs g 0#u64 0#u64 0#u64 false 0#u64 hS hl
      (by simp)) fun _ _ => trivial) ?_
  rintro ⟨elrsr, eisr, vl, hp⟩ -
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (P0.vcpu.reg_get.p0 st s vc _ hS) fun hcr _ => ?_
  refine WP.spec_bind (P0.vcpu.reg_get.p0 st s vc _ hS) fun vmcr _ => ?_
  simp only [lift, bind_ok]
  repeat' (first
    | exact vcpu.reg_set.cur0A (h := by assumption) hw (by
        simp [fl4_abi.consts.vcpu_reg.VGIC_MISR])
    | (refine WP.spec_bind (vcpu.reg_set.cur0A (h := by assumption) hw (by
        simp [fl4_abi.consts.vcpu_reg.VGIC_ELRSR, fl4_abi.consts.vcpu_reg.VGIC_EISR])) fun _ _ => ?_)
    | (refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun _ _ => ?_))

/-- `vcpu.reply1` is `vspace.reply1`'s text. -/
theorem vcpu.reply1_eq (s : S) (t : U64) (call : Bool) (v : U64) :
    vcpu.reply1 st s t call v = vspace.reply1 st s t call v := by
  unfold vcpu.reply1 vspace.reply1; rfl

/-- **`reply1`** (the VCPU's): as `vspace.reply1.bxiA`. -/
theorem vcpu.reply1.bxiA (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S}
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s) {t : U64} (ht : t ∈ T)
    (hr : ¬ BlockedR (L.mem s (stA t))) (call : Bool) (v : U64) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    vcpu.reply1 st s t call v ⦃ s' => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  rw [vcpu.reply1_eq]; exact vspace.reply1.bxiA E h hU ht hr call v hG

/-- A list-register index below the GIC's count (at most 16) names a register below 64. -/
theorem vcpu.lr_idx_lt {index lrs : U64} (h : ¬ index >= lrs) (hl : lrs.val ≤ 16) :
    (core.num.U64.wrapping_add fl4_abi.consts.vcpu_reg.VGIC_LR0 index).val < 64 := by
  have hi : index.val < 16 := by scalar_tac
  have h48 : fl4_abi.consts.vcpu_reg.VGIC_LR0.val = 48 := by simp [fl4_abi.consts.vcpu_reg.VGIC_LR0]
  rw [core.num.U64.wrapping_add_val_eq, h48]
  rw [Nat.mod_eq_of_lt (by simp [U64.size_def, U64.numBits]; omega)]
  omega

/-- A field below `NUM` is below 64. -/
theorem vcpu.field_lt {field : U64} (h : ¬ field >= fl4_abi.consts.vcpu_reg.NUM) : field.val < 64 := by
  have h64 : fl4_abi.consts.vcpu_reg.NUM.val = 64 := by simp [fl4_abi.consts.vcpu_reg.NUM]
  have : field.val < fl4_abi.consts.vcpu_reg.NUM.val := by scalar_tac
  omega

set_option hygiene false in
/-- An error result with the state kept. -/
local macro "errC" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [bind_ok, bind_tc_ok, lift, error.illegal, error.truncated, error.range, error.invalid_arg]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

set_option hygiene false in
/-- The caller (`sched.cur_thread`) named `L.curW s`. -/
local macro "curC" : tactic => `(tactic| (
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e))

set_option hygiene false in
/-- A total step whose value is not needed. -/
local macro "tb" : tactic => `(tactic| (refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun _ _ => ?_))

set_option hygiene false in
/-- ReadReg's body after the checks: stall, the value, restart, the reply. -/
local macro "rdBody" : tactic => `(tactic| (
  refine WP.spec_bind (vcpu.stall_vcpu.stalled hA (Stalled.refl0 D)) ?_
  rintro ⟨s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (hA.vcpu_gic_version a1) fun gv _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun val _ => ?_
  refine WP.spec_bind (Stalled.restartT D h1) fun s2 h2 => ?_
  obtain ⟨Ac2, hb2⟩ := h2.bxi
  refine WP.spec_bind (vcpu.reply1.bxiA E hb2 (D.user.ksb h2.fr.1) hct
    (by have nb := h2.nb; rwa [h2.2.choose_spec.2.1] at nb) call val (hE.xg.of_fr h2.fr)) fun s3 h3 => ?_
  exact (WP.spec_ok _).2 (DecPost.ok_bxi h3)))

set_option maxHeartbeats 2000000 in
/-- **`ReadReg`** keeps the invariants: the checks, the stall, the value (a VCPU word or the GIC's), the
restart, the reply. -/
theorem vcpu.decode_read_reg.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra)
    (hE : EntAt st P3Ok s) (a : A) (vc len : U64) (call : Bool) (buf : U64) :
    vcpu.decode_read_reg st ar s a vc len call buf ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  unfold vcpu.decode_read_reg
  refine spec_ite (fun _ => by errC) (fun _ => ?_)
  curC
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun field _ => ?_
  refine spec_ite (fun _ => by errC) (fun _ => ?_)
  refine WP.spec_bind (P0.vcpu.num_lrs.p0 ar a hA) fun lrs _ => ?_
  refine spec_ite (fun hge => ?_) (fun _ => by rdBody)
  refine WP.spec_bind (Pₘ := fun _ => True)
    (WP.spec_mono (UScalar.sub_spec (by scalar_tac)) fun _ _ => trivial) fun i _ => ?_
  refine spec_ite (fun _ => by errC) (fun _ => by rdBody)

set_option hygiene false in
/-- WriteReg's tail after the restart (`h2 : Cur0 … s2`): the value, the write, the VGIC resync. -/
local macro "wrTail" : tactic => `(tactic| (
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun v _ => ?_
  refine WP.spec_bind (vcpu.reg_set.cur0A h2 hw hf) fun s3 h3 => ?_
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · exact WP.spec_bind (vcpu.sync_vgic_status.cur0A h3 hw (by omega)) fun s4 h4 => (WP.spec_ok _).2 h4.post
  refine spec_ite (fun _ => ?_) (fun _ => (WP.spec_ok _).2 h3.post)
  exact WP.spec_bind (vcpu.sync_vgic_status.cur0A h3 hw (by omega)) fun s4 h4 => (WP.spec_ok _).2 h4.post))

set_option maxHeartbeats 2000000 in
/-- **`WriteReg`** keeps the invariants: the checks, the stall, the restart, one VCPU register (sanitised),
the VGIC resync. -/
theorem vcpu.decode_write_reg.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S}
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (a : A) (vc len buf : U64)
    (hw : VcWords Ω Sg vc) :
    vcpu.decode_write_reg st ar s a vc len buf ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.decode_write_reg
  refine spec_ite (fun _ => by errC) (fun _ => ?_)
  curC
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun field _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun val _ => ?_
  refine spec_ite (fun _ => by errC) (fun hn => ?_)
  have hf := vcpu.field_lt hn
  refine WP.spec_bind (P0.vcpu.is_readonly_reg.p0 _) fun b _ => ?_
  refine spec_ite (fun _ => by errC) (fun _ => ?_)
  refine WP.spec_bind (P0.vcpu.num_lrs.p0 ar a hA) fun lrs hl => ?_
  refine WP.spec_bind (hA.vcpu_gic_version a) fun gv _ => ?_
  refine spec_ite (fun hge => ?_) (fun _ => ?_)
  · refine WP.spec_bind (Pₘ := fun _ => True)
      (WP.spec_mono (UScalar.sub_spec (by scalar_tac)) fun _ _ => trivial) fun i _ => ?_
    refine spec_ite (fun _ => by errC) (fun _ => ?_)
    refine WP.spec_bind (P0.vcpu.sanitize_vgic_lr.p0 _ _) fun o _ => ?_
    rcases o with _ | san
    · errC
    try dsimp only
    refine WP.spec_bind (vcpu.stall_vcpu.stalled hA (Stalled.refl0 D)) ?_
    rintro ⟨s1, a1⟩ h1
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (Stalled.restartT D h1) fun s2 h2 => ?_
    refine WP.spec_bind (vcpu.reg_set.cur0A h2 hw hf) fun s3 h3 => ?_
    exact WP.spec_bind (vcpu.sync_vgic_status.cur0A h3 hw (by omega)) fun s4 h4 => (WP.spec_ok _).2 h4.post
  refine WP.spec_bind (vcpu.stall_vcpu.stalled hA (Stalled.refl0 D)) ?_
  rintro ⟨s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (Stalled.restartT D h1) fun s2 h2 => ?_
  refine spec_ite (fun _ => by wrTail) (fun _ => ?_)
  refine WP.spec_bind (P0.vcpu.is_vgic_ap1r.p0 _) fun b1 _ => ?_
  refine spec_ite (fun _ => (WP.spec_ok _).2 h2.post) (fun _ => by wrTail)

set_option hygiene false in
/-- InjectIRQ's body after the checks: stall, the list register read, the write, the VGIC resync. -/
local macro "injBody" : tactic => `(tactic| (
  refine WP.spec_bind (vcpu.stall_vcpu.stalled hA (Stalled.refl0 D)) ?_
  rintro ⟨s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (P0.vcpu.reg_get.p0 st s1 vc _ hS) fun cur _ => ?_
  refine WP.spec_bind (P0.vcpu.lr_is_empty.p0 _ _) fun b _ => ?_
  refine spec_ite (fun _ => ?_) (fun _ => (WP.spec_ok _).2 (Stalled.cur0 D h1).post)
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun lr _ => ?_
  refine WP.spec_bind (Stalled.restartT D h1) fun s2 h2 => ?_
  refine WP.spec_bind (vcpu.reg_set.cur0A h2 hw (vcpu.lr_idx_lt hix hl)) fun s3 h3 => ?_
  exact WP.spec_bind (vcpu.sync_vgic_status.cur0A h3 hw (by omega)) fun s4 h4 => (WP.spec_ok _).2 h4.post))

set_option maxHeartbeats 4000000 in
/-- **`InjectIRQ`** keeps the invariants: the checks, the stall, one empty list register written, the VGIC
resync (or `DeleteFirst` after the stall). -/
theorem vcpu.decode_inject_irq.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S}
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (a : A) (vc len buf : U64)
    (hw : VcWords Ω Sg vc) :
    vcpu.decode_inject_irq st ar s a vc len buf ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.decode_inject_irq
  refine spec_ite (fun _ => by errC) (fun _ => ?_)
  curC
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun mr0 _ => ?_
  simp only [lift, bind_ok]
  tb
  tb
  tb
  refine WP.spec_bind (P0.vcpu.num_lrs.p0 ar a hA) fun lrs hl => ?_
  refine WP.spec_bind (hA.vcpu_gic_version a) fun gv _ => ?_
  refine spec_ite (fun _ => by errC) (fun hix => ?_)
  refine spec_ite (fun _ => by errC) (fun _ => ?_)
  refine spec_ite (fun _ => ?_) (fun _ => by injBody)
  refine spec_ite (fun _ => ?_) (fun _ => by errC)
  refine spec_ite (fun _ => by injBody) (fun _ => by errC)

end

end Fl4ProofsA64.P1
