/-
P1 (aarch64): the ARM VCPU's state transfers — **`ReadState`** / **`WriteState`** (`vcpu::decode_state_transfer`,
crates/fl4-core/src/arch/aarch64/vcpu.rs:702–747, with `read_state_to_frame` 566–625 and `write_state_from_frame`
629–700) — keep the invariants.

The decode checks its arguments and the frame cap in the first extra slot (error, state kept), stalls the VCPU,
restarts the caller, then copies:

* ReadState: VCPU registers and the bound TCB's registers into the frame (`read_state_to_frame`): the frame's
  words are user words (`U`), so VcpuCheckInv's `vcpu.read_state_to_frame.fw` and `Cur0.xf` apply
  (`vcpu.read_state_to_frame.cur0A`);
* WriteState: frame words (reads) into VCPU registers (`Cur0.capw`, [P] `VcpuW`), the `VPPI_MASKED` word, the
  VGIC resync, and the GPRs of the TCB the VCPU's `TCB` word names (`obj.Tcb.set_reg`, `Cur0.xf`)
  (`vcpu.write_state_from_frame.vcj`).

`VcJ s0 vc s`: `Cur0` from the decode start `s0`, and the VCPU's `TCB` word (vc + 0) is zero or a TCB. The stall
(current-node words), the restart (`STATE` of the caller, the node's `SCHED_ACTION`: `vckW2`) and every write of
`write_state_from_frame` (VCPU words at offsets 16 / 64.., TCB register words) miss that word: it is a word of
`Ω` (`VcpuW`), and `Ω` lies outside the TCBs and nodes (`SchedQueuesInv.omega`) (`vcpu.st_restart`, `VcJ.*`).

**`vcpu.decode_state_transfer.dec`**.

New premise, **[P] `VcpuStA`** (placement facts at a decode start of an invoked `.Vcpu vc` cap):
* `tcb`: the VCPU's `TCB` word is zero or names a TCB. Source: it is written only by `decode_set_tcb`
  (vcpu.rs:388, the TCB of a thread cap), cleared by `unbind` (vcpu.rs:306) — which every TCB's deletion runs
  through `vcpu::detach` (objects.rs `finalise_cap_object`, Thread arm) — and zero in a fresh VCPU (`vcpu::init`).
* `frame`: ReadState's frame lies in the user words: if the first extra slot holds a writable non-device frame
  cap and the offset passes the decode's checks (64-aligned, inside the frame, `vcpu_state_mask::SIZE` = 1024
  bytes to its end), the 128 words from frame + offset are in `U` (`FrU`; as VcpuCheckInv's [P] `RunBuf` for the
  run frame, and QueueDecTcb's `TcbPlace.fpu` for the FPU frame).
Not false at reachable states as far as checked.
-/
import Fl4ProofsA64.P1.QueueDecVcpuRegA
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}
variable {A : Type _} {ar : machine.Arch A}

/-- **[P] (a64) The state transfers' placement facts** (module docstring). -/
structure VcpuStA (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  /-- [P] The VCPU's `TCB` word is zero or a TCB. -/
  tcb : ∀ (Ac : Set U64) (s : S) (vc : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra →
    L.mem s (core.num.U64.wrapping_add vc vcpu.TCB) = 0#u64 ∨ L.mem s (core.num.U64.wrapping_add vc vcpu.TCB) ∈ T
  /-- [P] ReadState's frame (a writable non-device frame cap in an extra slot, at a checked offset) is in `U`. -/
  frame : ∀ (Ac : Set U64) (s : S) (vc : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra →
    ∀ x ∈ extra.val, x ≠ 0#u64 → ∀ off : U64,
      obj.Slot.cap st x s ⦃ cp => ∀ (ptr : U64) (size : capability.FrameSize) (rights : U64) (dev x1 x2 : Bool)
        (x3 x4 : U64), cp = capability.Cap.Frame ptr size rights dev x1 x2 x3 x4 → dev = false →
        rights = capability.VM_READ_WRITE → ∀ bits sz : U64, capability.FrameSize.bits size = ok bits →
        (1#u64 <<< (bits &&& 63#u64) : Result U64) = ok sz → (off &&& 63#u64) = 0#u64 → off.val < sz.val →
        1024 ≤ sz.val - off.val → FrU U (core.num.U64.wrapping_add ptr off) ⦄

/-- `Cur0` and the VCPU's `TCB` word zero or a TCB. -/
def VcJ (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (s0 : S) (vc : U64) (s : S) : Prop :=
  Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s ∧
    (L.mem s (core.num.U64.wrapping_add vc vcpu.TCB) = 0#u64 ∨ L.mem s (core.num.U64.wrapping_add vc vcpu.TCB) ∈ T)

theorem vcpu.tcb_off {vc : U64} : core.num.U64.wrapping_add vc vcpu.TCB = core.num.U64.wrapping_add vc 0#u64 := by
  simp [vcpu.TCB]

/-- A register index below 64 names a VCPU word at an offset 64 or more. -/
theorem vcpu.reg_addr.offB (vc idx : U64) (hi : idx.val < 64) :
    ∃ o : U64, 64 ≤ o.val ∧ o.val < 4096 ∧ o.val % 8 = 0 ∧
      vcpu.reg_addr vc idx = ok (core.num.U64.wrapping_add vc o) := by
  have hm : (core.num.U64.wrapping_mul idx 8#u64).val = idx.val * 8 := by
    simp [core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
  have hR : vcpu.REGS.val = 64 := by simp [vcpu.REGS]
  have ho : (core.num.U64.wrapping_add vcpu.REGS (core.num.U64.wrapping_mul idx 8#u64)).val = 64 + idx.val * 8 := by
    simp only [core.num.U64.wrapping_add_val_eq, hm, hR]
    exact Nat.mod_eq_of_lt (by simp [U64.size_def, U64.numBits]; omega)
  refine ⟨core.num.U64.wrapping_add vcpu.REGS (core.num.U64.wrapping_mul idx 8#u64), by omega, by omega, by omega, ?_⟩
  unfold vcpu.reg_addr
  simp only [lift, bind_ok]
  rw [waddA_assoc vc _ _ (by rw [hR, hm]; omega)]

/-- A VCPU word write at a nonzero offset keeps `VcJ`. -/
theorem VcJ.wr {s0 s : S} {vc o v : U64} (h : VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s) (hw : VcWords Ω Sg vc)
    (ho : o.val < 4096) (h8 : o.val % 8 = 0) (h0 : o.val ≠ 0) :
    VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc (L.wr s (core.num.U64.wrapping_add vc o) v) := by
  have hx := hw o ho h8
  have hz := hw 0#u64 (by simp) (by simp)
  have hne : (core.num.U64.wrapping_add vc o).val ≠ (core.num.U64.wrapping_add vc 0#u64).val := by
    intro e
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] at e <;> omega
  refine ⟨h.1.capw (writesIn_wr hx.1) fun b eb => by subst eb; exact Or.inr ⟨hx.2.1, hx.2.2⟩, ?_⟩
  rw [vcpu.tcb_off, L.mem_wr_ne hx.1 hz.1 hne, ← vcpu.tcb_off]
  exact h.2

/-- **A VCPU register write keeps `VcJ`.** -/
theorem VcJ.regSet {s0 s : S} {vc idx v : U64} (h : VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s)
    (hw : VcWords Ω Sg vc) (hi : idx.val < 64) :
    vcpu.reg_set st s vc idx v ⦃ s' => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s' ⦄ := by
  obtain ⟨o, h64, ho, h8, e⟩ := vcpu.reg_addr.offB vc idx hi
  unfold vcpu.reg_set
  rw [e, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e' => ?_
  subst e'
  exact h.wr hw ho h8 (by omega)

set_option maxHeartbeats 2000000 in
/-- `sync_vgic_status` keeps `VcJ` (as `vcpu.sync_vgic_status.cur0A`). -/
theorem VcJ.sync {s0 s : S} {vc lrs : U64} {g : Bool}
    (h : VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s) (hw : VcWords Ω Sg vc) (hl : lrs.val ≤ 64) :
    vcpu.sync_vgic_status st s vc lrs g ⦃ s' => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s' ⦄ := by
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
    | exact VcJ.regSet (h := by assumption) hw (by
        simp [fl4_abi.consts.vcpu_reg.VGIC_MISR])
    | (refine WP.spec_bind (VcJ.regSet (h := by assumption) hw (by
        simp [fl4_abi.consts.vcpu_reg.VGIC_ELRSR, fl4_abi.consts.vcpu_reg.VGIC_EISR])) fun _ _ => ?_)
    | (refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun _ _ => ?_))

/-- A register-range copy from a frame into the VCPU keeps `VcJ`. -/
theorem VcJ.copyFrom {s0 : S} {vc : U64} (hw : VcWords Ω Sg vc) {f lo e : U64} (he : e.val < 64) {s : S}
    (h : VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s) :
    vcpu.copy_reg_range_from_frame st s vc f lo e ⦃ s' => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s' ⦄ := by
  unfold vcpu.copy_reg_range_from_frame vcpu.copy_reg_range_from_frame_loop
  apply loop.spec_decr_nat (measure := fun x : S × U64 => e.val + 1 - x.2.val)
    (inv := fun x : S × U64 => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc x.1)
  · rintro ⟨s1, r1⟩ w1
    dsimp only at w1 ⊢
    unfold vcpu.copy_reg_range_from_frame_loop.body
    simp only [lift, bind_ok, L.read_eq]
    by_cases hr : r1 ≤ e
    · rw [if_pos hr]
      have hr' : r1.val ≤ e.val := hr
      step as ⟨i, hi⟩
      refine WP.spec_bind (VcJ.regSet w1 hw (by omega)) fun s2 h2 => ?_
      step as ⟨r2, hr2⟩
      try rw [WP.spec_ok]
      exact ⟨h2, by first | omega | (dsimp only; omega)⟩
    · rw [if_neg hr, WP.spec_ok]; exact w1
  · exact h

/-- The list-register copy from a frame (`write_state_from_frame`'s loop 0) keeps `VcJ`. -/
theorem VcJ.lrLoop0 {s0 : S} {vc : U64} (hw : VcWords Ω Sg vc) {f lrs : U64} {g : Bool} (hl : lrs.val ≤ 16)
    (s : S) (r : U64) (h : VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s) :
    vcpu.write_state_from_frame_loop0 st s vc f lrs g r ⦃ s' => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s' ⦄ := by
  unfold vcpu.write_state_from_frame_loop0
  apply loop.spec_decr_nat (measure := fun x : S × U64 => lrs.val - x.2.val)
    (inv := fun x : S × U64 => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc x.1)
  · rintro ⟨s1, r1⟩ w1
    dsimp only at w1 ⊢
    unfold vcpu.write_state_from_frame_loop0.body
    simp only [lift, bind_ok, L.read_eq, fl4_abi.consts.vcpu_reg.VGIC_LR0]
    by_cases hr : r1 < lrs
    · rw [if_pos hr]
      have hr' : r1.val < lrs.val := hr
      have hx : (core.num.U64.wrapping_add 48#u64 r1).val = 48 + r1.val := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      step as ⟨i, hi⟩
      refine WP.spec_bind (P0.vcpu.sanitize_vgic_lr.p0 _ _) fun o _ => ?_
      refine WP.spec_bind (Pₘ := fun x => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc x) ?_ fun s2 h2 => ?_
      · rcases o with _ | san
        · exact (WP.spec_ok _).2 w1
        · exact VcJ.regSet w1 hw (by rw [hx]; omega)
      step as ⟨r2, hr2⟩
      try rw [WP.spec_ok]
      exact ⟨h2, by first | omega | (dsimp only; omega)⟩
    · rw [if_neg hr, WP.spec_ok]; exact w1
  · exact h

/-- A register write of a TCB keeps `VcJ` (a user-context word, `Cur0.xf`; not the VCPU's `TCB` word). -/
theorem VcJ.setReg {s0 s : S} {vc t r v : U64} (hw : VcWords Ω Sg vc) (hU0 : UserOK st T Cs Ω H U s0)
    (h : VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s) (ht : t ∈ T) (hr : r.val < 384) :
    obj.Tcb.set_reg st t s r v ⦃ s' => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s' ⦄ := by
  obtain ⟨-, Ac', hb, -⟩ := h.1
  obtain ⟨⟨Q, R, hq⟩, -⟩ := hb
  have hta := hq.tcbs t ht
  have hz := hw 0#u64 (by simp) (by simp)
  refine WP.spec_mono (obj.Tcb.set_reg.wrS s t r v hta hr) fun s' ⟨K, hK, e⟩ => ?_
  subst e
  have hKa : Aligned (core.num.U64.wrapping_add t K) := field_aligned hta (by omega) (by omega)
  refine ⟨h.1.xf (hU0.ksb h.1.fr.1) ((writesIn_wr hKa).mono fun b eb =>
    Or.inl ⟨t, ht, K, by omega, by omega, eb⟩), ?_⟩
  rw [vcpu.tcb_off, L.mem_wr_ne hKa hz.1
    (fun e => omega_ne_field hq hz.2.1 ht (K := K) (by omega) (UScalar.eq_of_val_eq e).symm),
    ← vcpu.tcb_off]
  exact h.2

/-- The GPR copy from a frame into a TCB (`write_state_from_frame`'s loop 1) keeps `VcJ`. -/
theorem VcJ.gprLoop {s0 : S} {vc : U64} (hw : VcWords Ω Sg vc) (hU0 : UserOK st T Cs Ω H U s0) {g t : U64}
    (ht : t ∈ T) (s : S) (r : U64) (h : VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s) :
    vcpu.write_state_from_frame_loop1 st s g t r ⦃ s' => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s' ⦄ := by
  unfold vcpu.write_state_from_frame_loop1
  apply loop.spec_decr_nat (measure := fun x : S × U64 => 37 - x.2.val)
    (inv := fun x : S × U64 => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc x.1)
  · rintro ⟨s1, r1⟩ w1
    dsimp only at w1 ⊢
    unfold vcpu.write_state_from_frame_loop1.body
    simp only [lift, bind_ok, L.read_eq, layout.reg.COUNT]
    by_cases hr : r1 < 37#u64
    · rw [if_pos hr]
      have hr' : r1.val < 37 := hr
      step as ⟨i, hi⟩
      refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun v1 _ => ?_
      refine WP.spec_bind (VcJ.setReg hw hU0 w1 ht (by omega)) fun s2 h2 => ?_
      step as ⟨r2, hr2⟩
      try rw [WP.spec_ok]
      exact ⟨h2, by first | omega | (dsimp only; omega)⟩
    · rw [if_neg hr, WP.spec_ok]; exact w1
  · exact h

theorem wloop2_eq (s : S) (vc f lrs : U64) (g : Bool) (r : U64) :
    vcpu.write_state_from_frame_loop2 st s vc f lrs g r = vcpu.write_state_from_frame_loop0 st s vc f lrs g r := by
  unfold vcpu.write_state_from_frame_loop2 vcpu.write_state_from_frame_loop0
  rfl

theorem wloop3_eq (s : S) (g tp r : U64) :
    vcpu.write_state_from_frame_loop3 st s g tp r = vcpu.write_state_from_frame_loop1 st s g tp r := by
  unfold vcpu.write_state_from_frame_loop3 vcpu.write_state_from_frame_loop1
  rfl

theorem wloop4_eq (s : S) (g tp r : U64) :
    vcpu.write_state_from_frame_loop4 st s g tp r = vcpu.write_state_from_frame_loop1 st s g tp r := by
  unfold vcpu.write_state_from_frame_loop4 vcpu.write_state_from_frame_loop1
  rfl

theorem VcJ.tcbT {s0 s : S} {vc : U64} (h : VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s)
    (hne : L.mem s (core.num.U64.wrapping_add vc vcpu.TCB) ≠ 0#u64) :
    L.mem s (core.num.U64.wrapping_add vc vcpu.TCB) ∈ T :=
  h.2.resolve_left hne

set_option hygiene false in
/-- `write_state_from_frame`'s GPR tail from a `VcJ` state `hh`. -/
local macro "gprT" hh:term : tactic => `(tactic| (
  split
  · step as ⟨ig, _⟩
    refine spec_ite (fun hne => ?_) (fun _ => (WP.spec_ok _).2 $hh)
    have htp := VcJ.tcbT $hh (by simpa using hne)
    refine WP.spec_bind (VcJ.gprLoop hw hU0 htp _ _ $hh) fun s10 h10 => ?_
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st _ s10 _ L.total) fun pc _ => ?_
    exact VcJ.setReg hw hU0 h10 htp (by simp [layout.reg.FAULT_IP])
  · exact (WP.spec_ok _).2 $hh))

set_option maxHeartbeats 4000000 in
/-- **`write_state_from_frame` keeps `VcJ`**: VCPU registers, `VPPI_MASKED`, the VGIC resync, the bound TCB's
GPRs and `FAULT_IP`. -/
theorem vcpu.write_state_from_frame.vcj (hA : P0.ArchTotal ar) {s0 : S} (hU0 : UserOK st T Cs Ω H U s0)
    {vc : U64} (hw : VcWords Ω Sg vc) (s : S) (a : A) (f mask : U64)
    (h : VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s) :
    vcpu.write_state_from_frame st ar s a vc f mask ⦃ s' => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc s' ⦄ := by
  unfold vcpu.write_state_from_frame
  rw [eq_of_spec_fd P0.Consts.fl4_abi.consts.vcpu_state_mask.EL1_SYSREGS.spec,
    eq_of_spec_fd P0.Consts.fl4_abi.consts.vcpu_state_mask.HYP.spec,
    eq_of_spec_fd P0.Consts.fl4_abi.consts.vcpu_state_mask.TIMER.spec,
    eq_of_spec_fd P0.Consts.fl4_abi.consts.vcpu_state_mask.VGIC.spec,
    eq_of_spec_fd P0.Consts.fl4_abi.consts.vcpu_state_mask.GPRS.spec,
    eq_of_spec_fd P0.Consts.fl4_abi.consts.vcpu_state_mask.VGIC_LR.spec]
  simp only [lift, bind_ok, L.read_eq, L.write_eq, wloop2_eq, wloop3_eq, wloop4_eq,
    fl4_abi.consts.vcpu_reg.CSSELR_EL1, fl4_abi.consts.vcpu_reg.ACTLR_EL1, fl4_abi.consts.vcpu_reg.MDCCINT_EL1,
    fl4_abi.consts.vcpu_reg.VMPIDR_EL2, fl4_abi.consts.vcpu_reg.VDISR_EL2, fl4_abi.consts.vcpu_reg.VPIDR_EL2,
    fl4_abi.consts.vcpu_reg.HCR_EL2, fl4_abi.consts.vcpu_reg.VSESR_EL2,
    fl4_abi.consts.vcpu_reg.CNTV_CTL, fl4_abi.consts.vcpu_reg.CNTKCTL_EL1,
    fl4_abi.consts.vcpu_reg.VGIC_HCR, fl4_abi.consts.vcpu_reg.VGIC_VMCR, fl4_abi.consts.vcpu_reg.VGIC_AP0R0,
    fl4_abi.consts.vcpu_reg.VGIC_AP0R3, fl4_abi.consts.vcpu_reg.VGIC_AP1R0, fl4_abi.consts.vcpu_reg.VGIC_AP1R3]
  by_cases h0 : mask = 0#u64
  · rw [if_pos h0]; exact (WP.spec_ok _).2 h
  rw [if_neg h0]
  -- EL1 system registers
  refine WP.spec_bind (Pₘ := fun x => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc x) ?_ fun s1 h1 => ?_
  · split
    · exact WP.spec_bind (VcJ.copyFrom hw (by simp) h) fun s2 h2 => VcJ.copyFrom hw (by simp) h2
    · exact (WP.spec_ok _).2 h
  -- hypervisor registers
  refine WP.spec_bind (Pₘ := fun x => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc x) ?_ fun s2 h2 => ?_
  · split
    · step as ⟨i4, _⟩
      refine WP.spec_bind (VcJ.regSet h1 hw (by simp)) fun s3 h3 => ?_
      step as ⟨i7, _⟩
      refine WP.spec_bind (VcJ.regSet h3 hw (by simp)) fun s4 h4 => ?_
      step as ⟨i10, _⟩
      refine WP.spec_bind (VcJ.regSet h4 hw (by simp)) fun s5 h5 => ?_
      step as ⟨i13, _⟩
      refine WP.spec_bind (P0.vcpu.sanitize_hcr.p0 _) fun i16 _ => ?_
      refine WP.spec_bind (VcJ.regSet h5 hw (by simp)) fun s6 h6 => ?_
      step as ⟨i17, _⟩
      exact VcJ.regSet h6 hw (by simp)
    · exact (WP.spec_ok _).2 h1
  -- timer
  refine WP.spec_bind (Pₘ := fun x => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc x) ?_ fun s3 h3 => ?_
  · split
    · refine WP.spec_bind (VcJ.copyFrom hw (by simp) h2) fun s4 h4 => ?_
      step as ⟨i6, _⟩
      step as ⟨i7, _⟩
      have hv := VcJ.wr (v := L.mem s4 (core.num.U64.wrapping_add f i7) &&& 1#u64) h4 hw
        (o := vcpu.VPPI_MASKED) (by simp [vcpu.VPPI_MASKED]) (by simp [vcpu.VPPI_MASKED]) (by simp [vcpu.VPPI_MASKED])
      first | exact hv | exact (WP.spec_ok _).2 hv
    · exact (WP.spec_ok _).2 h2
  -- VGIC
  split
  · refine WP.spec_bind (P0.vcpu.num_lrs.p0 ar a hA) fun lrs hl => ?_
    refine WP.spec_bind (hA.vcpu_gic_version a) fun i8 _ => ?_
    step as ⟨i9, _⟩
    refine WP.spec_bind (P0.vcpu.sanitize_vgic_hcr.p0 _ _) fun i12 _ => ?_
    refine WP.spec_bind (VcJ.regSet h3 hw (by simp)) fun s4 h4 => ?_
    step as ⟨i13, _⟩
    refine WP.spec_bind (VcJ.regSet h4 hw (by simp)) fun s5 h5 => ?_
    refine WP.spec_bind (VcJ.copyFrom hw (by simp) h5) fun s6 h6 => ?_
    refine WP.spec_bind (Pₘ := fun x => VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s0 vc x) ?_ fun s7 h7 => ?_
    · split
      · exact VcJ.copyFrom hw (by simp) h6
      · exact (WP.spec_ok _).2 h6
    refine WP.spec_bind (VcJ.lrLoop0 hw hl _ _ h7) fun s8 h8 => ?_
    refine WP.spec_bind (VcJ.sync h8 hw (by omega)) fun s9 h9 => ?_
    gprT h9
  · split
    · refine WP.spec_bind (P0.vcpu.num_lrs.p0 ar a hA) fun lrs hl => ?_
      refine WP.spec_bind (hA.vcpu_gic_version a) fun i10 _ => ?_
      step as ⟨i11, _⟩
      refine WP.spec_bind (P0.vcpu.sanitize_vgic_hcr.p0 _ _) fun i14 _ => ?_
      refine WP.spec_bind (VcJ.regSet h3 hw (by simp)) fun s4 h4 => ?_
      refine WP.spec_bind (VcJ.lrLoop0 hw hl _ _ h4) fun s5 h5 => ?_
      refine WP.spec_bind (VcJ.sync h5 hw (by omega)) fun s6 h6 => ?_
      gprT h6
    · gprT h3

/-- An `Ω` word is no word of a placed node. -/
theorem out_ne_nodeA {s : S} {b c o : U64} (hO : OutsideObjs st T Cs s b) (hc : c ∈ Cs)
    (hN : NodePlaced st T s c) (ho : o.val < 4288) (e : b = L.nodeAt s c o) : False := by
  subst e
  have := nodeAt_val hN ho
  rcases hO.2.2 c hc with h | h <;> omega

/-- **The stall and the caller's restart keep the VCPU's `TCB` word**: `VcJ` after them. -/
theorem vcpu.st_restart {s s2 : S} {vc : U64} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (h2 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s2)
    (hw : VcWords Ω Sg vc)
    (hT0 : L.mem s (core.num.U64.wrapping_add vc vcpu.TCB) = 0#u64 ∨
      L.mem s (core.num.U64.wrapping_add vc vcpu.TCB) ∈ T) :
    sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART ⦃ s3 =>
      VcJ st T Cs Ω H Sg Rp Scs Nt Z Ac s vc s3 ⦄ := by
  obtain ⟨⟨Q, R, hq⟩, -⟩ := D.bxi
  have hct : L.curW s ∈ T := hq.curT
  have hTP := hq.tcbs
  have hcs := hq.cur
  have hN := hq.nodes _ hcs
  have hz := hw 0#u64 (by simp) (by simp)
  have hO := hq.omega _ hz.2.1
  have e2 : L.mem s2 (core.num.U64.wrapping_add vc 0#u64) = L.mem s (core.num.U64.wrapping_add vc 0#u64) :=
    h2.node.mem_eq hz.1 (fun ⟨o, ho, _, e⟩ => out_ne_nodeA hO hcs hN ho e)
  have hN2 : NodePlaced st T s2 (L.cpu s2) := by rw [h2.node.2.1]; exact hN.ksb h2.node.1
  refine WP.spec_mono (WP.spec_and (Stalled.restartT D h2)
    (sched.set_thread_state.vckW2 s2 (L.curW s) sched.TS_RESTART hTP hN2 hct)) fun s3 ⟨c3, w3, _, _⟩ => ⟨c3, ?_⟩
  have e3 : L.mem s3 (core.num.U64.wrapping_add vc 0#u64) = L.mem s2 (core.num.U64.wrapping_add vc 0#u64) := by
    refine w3.mem_eq hz.1 fun hb => ?_
    rcases hb with e | e
    · rw [stA_eq] at e
      exact omega_ne_field hq hz.2.1 hct (K := 3328#u64) (by simp) e
    · rw [h2.node.2.1, nodeAt_of_ksb h2.node.1] at e
      exact out_ne_nodeA hO hcs hN (by rw [act_val]; omega) e
  rw [vcpu.tcb_off, e3, e2, ← vcpu.tcb_off]
  exact hT0

/-- **`read_state_to_frame` into a `U` frame keeps `Cur0`.** -/
theorem vcpu.read_state_to_frame.cur0A (hA : P0.ArchTotal ar) {s0 s : S} {a : A} {vc f mask : U64}
    (hU0 : UserOK st T Cs Ω H U s0) (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hfr : FrU U f) :
    vcpu.read_state_to_frame st ar s a vc f mask ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hU : UserOK st T Cs Ω H U s := hU0.ksb h.fr.1
  exact WP.spec_mono (vcpu.read_state_to_frame.fw hA s a vc f mask hfr (fun b hb => (hU b hb).1.1))
    fun s' w => h.xf hU (w.mono fun b hb => Or.inr hb)

/-- The decode's size check. -/
theorem vcpu.size_ok {i6 size1 off : U64} (h6 : i6.val = size1.val - off.val)
    (hn : ¬ i6 < fl4_abi.consts.vcpu_state_mask.SIZE) : 1024 ≤ size1.val - off.val := by
  have h : fl4_abi.consts.vcpu_state_mask.SIZE.val = 1024 := by simp [fl4_abi.consts.vcpu_state_mask.SIZE]
  have : ¬ i6.val < fl4_abi.consts.vcpu_state_mask.SIZE.val := fun h' => hn (by scalar_tac)
  omega

set_option hygiene false in
/-- An error result with the state kept. -/
local macro "errS" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [bind_ok, bind_tc_ok, lift, error.illegal, error.truncated, error.range, error.invalid_arg,
      error.invalid_cap]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

set_option hygiene false in
/-- A total step whose value is not needed. -/
local macro "tbS" : tactic => `(tactic| (refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun _ _ => ?_))

set_option hygiene false in
/-- ReadState's tail: the stall, the restart, the copy into the frame. -/
local macro "stR" : tactic => `(tactic| (
  refine WP.spec_bind (vcpu.stall_vcpu.stalled hA (Stalled.refl0 D)) ?_
  rintro ⟨s2, a1⟩ h2
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (vcpu.st_restart D h2 hw hT0) fun s3 h3 => ?_
  refine spec_ite (fun _ => ?_) (fun hn => absurd htf hn)
  exact WP.spec_bind (vcpu.read_state_to_frame.cur0A hA D.user h3.1 hfr) fun s4 h4 => (WP.spec_ok _).2 h4.post))

set_option hygiene false in
/-- WriteState's tail: the stall, the restart, the copy from the frame. -/
local macro "stW" : tactic => `(tactic| (
  refine WP.spec_bind (vcpu.stall_vcpu.stalled hA (Stalled.refl0 D)) ?_
  rintro ⟨s2, a1⟩ h2
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (vcpu.st_restart D h2 hw hT0) fun s3 h3 => ?_
  refine spec_ite (fun hy => absurd hy htf) (fun _ => ?_)
  exact WP.spec_bind (vcpu.write_state_from_frame.vcj hA D.user hw _ _ _ _ h3) fun s4 h4 =>
    (WP.spec_ok _).2 h4.1.post))

set_option maxHeartbeats 8000000 in
/-- **`ReadState` / `WriteState`** keep the invariants. -/
theorem vcpu.decode_state_transfer.dec (hA : P0.ArchTotal ar) (Pl : VcpuStA st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s : S} {vc : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra) (hE : EntAt st P3Ok s)
    (hw : VcWords Ω Sg vc) (a : A) (len buf : U64) (rd : Bool) :
    vcpu.decode_state_transfer st ar s a vc len buf extra rd ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hT0 := Pl.tcb Ac s vc extra hE D
  unfold vcpu.decode_state_transfer
  refine spec_ite (fun _ => by errS) (fun _ => ?_)
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl hsl => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine spec_ite (fun _ => by errS) (fun h0 => ?_)
  have hmem : sl ∈ extra.val := hsl ▸ List.getElem_mem hl0
  have hne : sl ≠ 0#u64 := by simpa using h0
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun off _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun mask _ => ?_
  tbS
  simp only [lift, bind_ok]
  refine spec_ite (fun _ => by errS) (fun _ => ?_)
  refine WP.spec_bind (Pl.frame Ac s vc extra hE D sl hmem hne off) fun c hc => ?_
  cases c
  all_goals try errS
  rename_i ptr fsz rights dev x1 x2 x3 x4
  try dsimp only
  refine spec_ite (fun _ => by errS) (fun hdev => ?_)
  refine spec_ite (fun _ => by errS) (fun _ => ?_)
  refine spec_ite (fun htf => ?_) (fun htf => ?_)
  · refine spec_ite (fun _ => by errS) (fun hrw => ?_)
    refine WP.spec_bind (spec_eqv (P0.capability.FrameSize.bits.p0 fsz)) fun bits ⟨eb, _⟩ => ?_
    refine WP.spec_bind (spec_eqv (P := fun _ => True) (by p0_split)) fun size1 ⟨es, _⟩ => ?_
    refine spec_ite (fun _ => by errS) (fun ha => ?_)
    refine spec_ite (fun _ => by errS) (fun hlt => ?_)
    step as ⟨i6, hi6⟩
    refine spec_ite (fun _ => by errS) (fun hsz => ?_)
    have hfr : FrU U (core.num.U64.wrapping_add ptr off) :=
      hc ptr fsz rights dev x1 x2 x3 x4 rfl (by simpa using hdev) (by apply UScalar.eq_of_val_eq; simpa [capability.VM_READ_WRITE] using hrw) bits size1 eb es
        (by apply UScalar.eq_of_val_eq; simpa using ha) (by scalar_tac) (vcpu.size_ok (by scalar_tac) hsz)
    refine WP.spec_bind (P0.vcpu.num_lrs.p0 ar a hA) fun lrs hl => ?_
    refine WP.spec_bind (hA.vcpu_gic_version a) fun i7 _ => ?_
    refine spec_ite (fun _ => by stR) (fun hn => absurd htf hn)
  · refine WP.spec_bind (P0.capability.FrameSize.bits.p0 fsz) fun bits _ => ?_
    tbS
    refine spec_ite (fun _ => by errS) (fun _ => ?_)
    refine spec_ite (fun _ => by errS) (fun _ => ?_)
    tbS
    refine spec_ite (fun _ => by errS) (fun _ => ?_)
    refine WP.spec_bind (P0.vcpu.num_lrs.p0 ar a hA) fun lrs hl => ?_
    refine WP.spec_bind (hA.vcpu_gic_version a) fun i7 _ => ?_
    refine spec_ite (fun hy => absurd hy htf) (fun _ => ?_)
    tbS
    tbS
    refine spec_ite (fun _ => ?_) (fun _ => by stW)
    refine WP.spec_bind (P0.vcpu.validate_vgic_lrs.p0 st s _ lrs _ hS (by omega)) fun b1 _ => ?_
    refine spec_ite (fun _ => by stW) (fun _ => by errS)

end

end Fl4ProofsA64.P1
