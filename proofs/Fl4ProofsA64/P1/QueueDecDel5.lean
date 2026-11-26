/-
P1 (aarch64): **the thread and IRQ-handler families over the root-restricted deletion forms** (QueueDelVs5).

* Namespace `W7.R.A5`: QueueDecTcbRv's install chain (`tcb.install_tcb_cap.cur0`, `tcb.install_buffer.cur0`, the
  `SetTimeoutEndpoint` / `SetSpace` / `Configure` / `SetSchedParams` / `SetIPCBuffer` / `SetHighVSpace` decodes,
  `tcb.decode.dec`, `decGap_thread`) with `A5.DelGaps` for `W7.R.DelGaps` (its deletions are
  `A5.cdt.delete.cur0`), by script (`handoff/a64-wip/gen23/gen_decdel5.py`); **`A5.decGap_thread4`** from
  `A5.DelPlace`, [J] `A5.VsDel` and `FinGaps4`.
* Namespace `P1`: QueueDecIrq's IRQ-handler family over `A5.DelPlaceAt` (its handler-slot deletion empties the slot
  with `A5.cdt.empty_slot.cur0`): `cdt.delete_one.irq_cur0R5`, `interrupt.decode_irq_handler.dec5`,
  **`decGap_irqHandler5`**.

Named premises: those of the forms used (`SspHyps`, [P] `TcbPlace`, [P] `TcbPlace7`, `XferHyps`, `CdtHyps`,
[P] `IrqPlace`, `A5.DelPlace` with [J] `frm`, [J] `A5.VsDel`, [J] `FinRvRest4` and the `arch` gap in `FinGaps4`).
No new premise here; none of them is a walk quantified over every root.
-/
import Fl4ProofsA64.P1.QueueDelVs5
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

namespace W7
namespace R
namespace A5

/-- `reschedule_required` keeps `Cur0R` (no `STATE` / `RUN_VCPU` word written). -/
theorem Cur0R.resched {s0 s : S} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    sched.reschedule_required st s ⦃ s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  obtain ⟨Ac', hb⟩ := h.1.bxi
  obtain ⟨⟨Q, R, q⟩, hB, -, -, hSg⟩ := hb.blk
  refine WP.spec_mono (WP.spec_and (Cur0.resched h.1) (WP.spec_and
    (sched.reschedule_required.fldX (K := 3328#u64) s Q R q hB hSg (by simp) (by simp) (by simp) (by simp))
    (sched.reschedule_required.fldX (K := 3672#u64) s Q R q hB hSg (by simp) (by simp) (by simp) (by simp)))) ?_
  rintro s' ⟨c, f1, f2⟩
  exact ⟨c, h.2.rvSt fun y hy => ⟨by rw [stA_eq]; exact f1 y hy, f2 y hy⟩⟩

/-- **`install_tcb_cap`** of a TCB cap slot (a64: any of the seven, `W7`), the source a cap slot or null. -/
theorem tcb.install_tcb_cap.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s0 s : S} {a : A} {target slot index src : U64} {c : capability.Cap}
    (hE : EntAt st P3Ok s0) (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ht : target ∈ T) (hi : index.val < 7)
    (hsrc : src ≠ 0#u64 → P1.CapW T Ω Sg src) :
    tcb.install_tcb_cap st ar s a target slot index c src ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  have hT := hb.1.choose_spec.choose_spec.tcbs
  have hW := W7.tcb_slotIdxW (Ω := Ω) (Sg := Sg) hT ht hi
  unfold tcb.install_tcb_cap
  rw [tcb_slot_val]
  simp only [bind_ok]
  refine WP.spec_bind (cdt.delete.cur0 hA (G _ hE) h hW) ?_
  rintro ⟨r, s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  rcases r with _ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h1
  refine WP.spec_bind (tcb.still_valid.nz s1 target slot c src) fun b hbv => ?_
  split
  · rename_i hb'
    obtain ⟨Ac1, hb1⟩ := h1.bxi
    have hW0 : W7.CapW T Ω Sg (slotIdx target index) := by
      have := hW.2 0#u64 (by simp) (by simp)
      have h0 : core.num.U64.wrapping_add (slotIdx target index) 0#u64 = slotIdx target index := by
        apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
      rwa [h0] at this
    refine WP.spec_bind (Pₘ := fun s2 => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s2) ?_
      fun s2 h2 => (WP.spec_ok _).2 h2
    unfold cdt.insert
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st src s1 hS) fun sc _ => ?_
    exact WP.spec_mono (C.ins7 Ac1 s0 s1 c sc src _ hE h1.fr hb1 (hsrc (hbv hb')) hW0) fun s2 w2 => h1.capw7 w2 fun _ hb => hb
  · exact (WP.spec_ok _).2 h1

/-- **`install_buffer`**, the buffer's source slot a cap slot or null. -/
theorem tcb.install_buffer.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s0 s : S} {a : A} {target slot baddr : U64} {buffer : capability.Cap × obj.Slot}
    (hE : EntAt st P3Ok s0) (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ht : target ∈ T)
    (hsrc : buffer.2 ≠ 0#u64 → P1.CapW T Ω Sg buffer.2) :
    tcb.install_buffer st ar s a target slot baddr buffer ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  have hT := hb.1.choose_spec.choose_spec.tcbs
  unfold tcb.install_buffer
  rw [tcb_slot_val]
  simp only [bind_ok]
  have hW := W7.tcb_slotIdxW (Ω := Ω) (Sg := Sg) (i := layout.tcb.SLOT_BUFFER) hT ht (by simp [layout.tcb.SLOT_BUFFER])
  refine WP.spec_bind (cdt.delete.cur0 hA (G _ hE) h hW) ?_
  rintro ⟨r, s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  rcases r with _ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨Ac1, hb1⟩ := h1.bxi
  have hT1 := hb1.1.choose_spec.choose_spec.tcbs
  refine WP.spec_bind (obj.Tcb.set_ipc_buffer.wr s1 target baddr) fun s2 e2 => ?_
  subst e2
  have h2 : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr s1 (core.num.U64.wrapping_add target 3512#u64) baddr) := by
    have hct : L.curW s1 ∈ T := hb1.1.choose_spec.choose_spec.curT
    obtain ⟨an, fr⟩ := fld_wr (K := 3512#u64) (v := baddr) hb1 ht (by simp) (by simp)
    refine ⟨Cur0.mk h1.1 (bxi_field hb1 ht (by simp) (by simp) (by simp) (by simp)) an.2.2
      (cscW_wr_field hT1 (hb1.1.choose_spec.choose_spec.nodes _ hb1.1.choose_spec.choose_spec.cur) ht
        (by simp) (by simp))
      (Or.inl (by rw [scA_eq]; exact fr _ hct _ (by simp) (by simp) (fun _ => by simp)))
      (Or.inl an.1) (Or.inl (by rw [stA_eq]; exact fr _ hct _ (by simp) (by simp) (fun _ => by simp)))
      (WritesIn.mono (writesIn_wr (field_aligned (hT1 target ht) (by simp) (by simp))) fun _ hb =>
        Or.inl (hb ▸ kw_field (Es := EH H) ht (by simp) (by simp) (by simp))),
      h1.2.wr_field hT1 ht (by simp) (by simp) (by simp) (by simp)⟩
  obtain ⟨vc, vs⟩ := buffer
  simp only at hsrc
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (tcb.still_valid.nz _ target slot vc vs) fun b hbv => ?_
  refine WP.spec_bind (Pₘ := fun s3 => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s3) ?_ fun s3 h3 => ?_
  · split
    · rename_i hb'
      obtain ⟨Ac2, hb2⟩ := h2.bxi
      have hW0 : W7.CapW T Ω Sg (slotIdx target layout.tcb.SLOT_BUFFER) := by
        have := hW.2 0#u64 (by simp) (by simp)
        have h0 : core.num.U64.wrapping_add (slotIdx target layout.tcb.SLOT_BUFFER) 0#u64 =
            slotIdx target layout.tcb.SLOT_BUFFER := by
          apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
        rwa [h0] at this
      unfold cdt.insert
      refine WP.spec_bind (P0.obj.Slot.cap.p0 st vs _ hS) fun sc _ => ?_
      exact WP.spec_mono (C.ins7 Ac2 s0 _ vc sc vs _ hE h2.fr hb2 (hsrc (hbv hb')) hW0) fun s' w => h2.capw7 w fun _ hb => hb
    · exact (WP.spec_ok _).2 h2
  refine WP.spec_bind (sched.cur_thread.spec s3) fun ct _ => ?_
  simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
  split
  · exact WP.spec_bind (Cur0R.resched h3) fun s4 h4 => (WP.spec_ok _).2 h4
  · exact (WP.spec_ok _).2 h3

/-- The install step's continuation shape. -/
theorem inst_bind {A : Type _} {s0 : S} {m : Result ((core.result.Result Unit error.Exc) × S × A)}
    {k : S → A → Result ((core.result.Result Unit error.Exc) × S × A)}
    (hm : m ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄)
    (hk : ∀ s' a', Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' → k s' a' ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄) :
    (do
      let (r, s1, a1) ← m
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ => k s1 a1
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame error.Exc) residual
        ok (r1, s1, a1)) ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  refine WP.spec_bind hm ?_
  rintro ⟨r, s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  rcases r with _ | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]; exact hk s1 a1 h1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1


set_option hygiene false in
/-- An error leaf at the stalled `Cur0` state `c1`. -/
local macro "errc" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (Cur0.post c1)
  | (simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, error.invalid_cap, error.illegal, error.truncated]
     exact (WP.spec_ok _).2 (Cur0.post c1)))

set_option hygiene false in
/-- An extra-slot read with its error leaf. -/
local macro "xslot" i:term : tactic => `(tactic| (
  refine WP.spec_bind (tcb.extra_with_length.memi _ $i _ (by simp)) ?_
  rintro r hx
  rcases r with x | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm, hx0⟩ := hx x rfl))

set_option maxHeartbeats 4000000 in
/-- **`SetTimeoutEndpoint`** after the stall. -/
theorem tcb.decode_set_timeout_endpoint.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → P1.CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_set_timeout_endpoint st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_set_timeout_endpoint
  refine WP.spec_bind (tcb.extra_with_length.mem _ 0#u64) ?_
  rintro r ⟨-, hx⟩
  rcases r with x | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c1)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm, hx0⟩ := hx x rfl
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s1 hS) fun th _ => ?_
  refine WP.spec_bind (P0.faults.valid_fault_handler.p0 th) fun b _ => ?_
  split
  swap
  · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (h1.restart0R D) fun s2 c2 => ?_
  refine WP.spec_mono (P₀ := fun r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s r.2.1) ?_ fun r hr => by
    obtain ⟨r1, r2, r3⟩ := r; exact Cur0.post hr.1
  unfold tcb.thread_control_caps
  simp only [lift, bind_ok, tcb.UPDATE_FAULT, tcb.UPDATE_TIMEOUT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  simp
  exact inst_bind (tcb.install_tcb_cap.cur0 hA G C hE c2 ht (by simp [layout.tcb.SLOT_TIMEOUT_HANDLER])
    (fun _ => hxw x hxm hx0)) fun s' a' h' => (WP.spec_ok _).2 h'

set_option maxHeartbeats 8000000 in
/-- **`SetSpace`** after the stall. -/
theorem tcb.decode_set_space.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → P1.CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_set_space st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_set_space
  refine WP.spec_bind (tcb.extra_with_length.memi _ 0#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x0 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm0, hx00⟩ := hx x0 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 1#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x1 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm1, hx01⟩ := hx x1 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 2#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x2 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm2, hx02⟩ := hx x2 rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun cdata _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun vdata _ => ?_
  refine WP.spec_bind (P0.tcb.derive_roots.p0 st s1 t cdata vdata x1 x2 hS) fun r _ => ?_
  rcases r with ⟨cc, vc⟩ | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x0 s1 hS) fun fh _ => ?_
  refine WP.spec_bind (P0.faults.valid_fault_handler.p0 fh) fun b _ => ?_
  split
  swap
  · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (h1.restart0R D) fun s2 c2 => ?_
  refine WP.spec_mono (P₀ := fun r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s r.2.1) ?_ fun r hr => by
    obtain ⟨r1, r2, r3⟩ := r; exact Cur0.post hr.1
  simp only [lift, bind_ok]
  unfold tcb.thread_control_caps
  simp only [lift, bind_ok, tcb.UPDATE_FAULT, tcb.UPDATE_TIMEOUT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  simp
  refine inst_bind (tcb.install_tcb_cap.cur0 hA G C hE c2 ht (by simp [layout.tcb.SLOT_FAULT_HANDLER])
    (fun _ => hxw x0 hxm0 hx00)) fun s3 a3 c3 => ?_
  refine inst_bind (tcb.install_tcb_cap.cur0 hA G C hE c3 ht (by simp [layout.tcb.SLOT_CTABLE])
    (fun _ => hxw x1 hxm1 hx01)) fun s4 a4 c4 => ?_
  exact inst_bind (tcb.install_tcb_cap.cur0 hA G C hE c4 ht (by simp [layout.tcb.SLOT_VTABLE])
    (fun _ => hxw x2 hxm2 hx02)) fun s5 a5 c5 => (WP.spec_ok _).2 c5


set_option maxHeartbeats 8000000 in
/-- **`Configure`** after the stall. -/
theorem tcb.decode_configure.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → P1.CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_configure st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_configure
  refine WP.spec_bind (tcb.extra_with_length.memi _ 0#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x0 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm0, hx00⟩ := hx x0 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 1#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x1 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm1, hx01⟩ := hx x1 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 2#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x2 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm2, hx02⟩ := hx x2 rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun cdata _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun vdata _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun baddr _ => ?_
  refine WP.spec_bind (tcb.derive_for_buffer.slot s1 baddr x2) ?_
  rintro r hbf
  rcases r with bf | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hbf' := hbf bf rfl
  refine WP.spec_bind (P0.tcb.derive_roots.p0 st s1 t cdata vdata x0 x1 hS) fun r _ => ?_
  rcases r with ⟨cc, vc⟩ | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (h1.restart0R D) fun s2 c2 => ?_
  refine WP.spec_mono (P₀ := fun r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s r.2.1) ?_ fun r hr => by
    obtain ⟨r1, r2, r3⟩ := r; exact Cur0.post hr.1
  simp only [lift, bind_ok]
  unfold tcb.thread_control_caps
  simp only [lift, bind_ok, tcb.UPDATE_FAULT, tcb.UPDATE_TIMEOUT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  simp
  refine inst_bind (tcb.install_tcb_cap.cur0 hA G C hE c2 ht (by simp [layout.tcb.SLOT_CTABLE])
    (fun _ => hxw x0 hxm0 hx00)) fun s4 a4 c4 => ?_
  refine inst_bind (tcb.install_tcb_cap.cur0 hA G C hE c4 ht (by simp [layout.tcb.SLOT_VTABLE])
    (fun _ => hxw x1 hxm1 hx01)) fun s5 a5 c5 => ?_
  exact inst_bind (tcb.install_buffer.cur0 hA G C hE c5 ht (fun h0 => by
    rcases hbf' with e | e
    · rw [e]; exact hxw x2 hxm2 hx02
    · exact absurd e h0)) fun s6 a6 c6 => (WP.spec_ok _).2 c6

set_option maxHeartbeats 8000000 in
/-- **`SetSchedParams`** after the stall, from `SspHyps`. -/
theorem tcb.decode_set_sched_params.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (Y : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1)
    (hΩ : ∀ x ∈ Ω, L.mem s1 x = L.mem s x) (hid1 : L.idleW s1 = L.idleW s) :
    tcb.decode_set_sched_params st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have c1 := h1.cur0 D
  have hxw := P.extraW Ac s _ _ hE D
  have hb1 := h1.bxi.blk
  unfold tcb.decode_set_sched_params
  refine WP.spec_bind (tcb.extra_with_length.memi _ 0#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x0 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm0, hx00⟩ := hx x0 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 1#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x1 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm1, hx01⟩ := hx x1 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 2#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x2 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm2, hx02⟩ := hx x2 rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun mcp _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun prio _ => ?_
  refine WP.spec_bind (tcb.thread_arg.tcb (pos := 1#u64) D h1.node hxm0 hx00) ?_
  rintro r ⟨-, hT2⟩
  rcases r with auth | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hauth := hT2 auth rfl
  refine WP.spec_bind (tcb.check_prio.le s1 mcp auth) ?_
  rintro r ⟨-, -⟩
  rcases r with u | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_bind (tcb.check_prio.le s1 prio auth) ?_
  rintro r ⟨-, hle⟩
  rcases r with u | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hv : prio.val < 256 := lt_of_le_of_lt (hle rfl) (by rw [h1.fld auth hauth 3440#u64 (by simp) (by simp)]; exact P.mcp Ac s auth hE D.bxi hauth)
  refine WP.spec_bind (tcb.sched_params_sc.ok t x1 (D.extra s1 h1.node x1 hxm1 hx01) hb1.2.2.2.1) ?_
  rintro r hsp
  rcases r with v | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hsp := hsp v rfl
  simp only [lift, bind_ok]
  refine WP.spec_bind (obj.Tcb.sc.spec s1 t) fun i1 ei1 => ?_
  -- the restart, then the install and the scheduling words
  have est : L.mem s1 (stA (L.curW s1)) = L.mem s (stA (L.curW s)) := by
    rw [h1.cur, stA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  have hr := runnable_ok D.run
  have hsc0 := P.curSc Ac s _ _ hE D
  have run : ∀ (flags : U64), (flags &&& tcb.SCHED_UPDATE_FAULT) ≠ 0#u64 →
      ((flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → L.mem s1 (scA t) ≠ v) → ∀ fhc : capability.Cap,
      (do
        let s2 ← tcb.restart_caller st s1
        tcb.thread_control_sched st ar s2 a1 t slot (fhc, x2) mcp prio v flags) ⦃ r =>
          DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2.1 ⦄ := by
    intro flags hfl hfs fhc
    refine WP.spec_bind (WP.spec_and (WP.spec_and (h1.restart D) (h1.restart0R D))
      (tcb.restart_caller.blk (Es := EH H) s1 hb1 (est ▸ hr.1) (est ▸ hr.2))) ?_
    rintro s2 ⟨⟨⟨h2, hna, ec2, k⟩, c2⟩, ⟨_, f2, est2, _⟩⟩
    have agree : ∀ b, Aligned b → P1.CapW T Ω Sg b → L.mem s2 b = L.mem s b := fun b hb hw => by
      rw [f2.mem_eq hb fun hk => capw_not_kw hb1 hw hb (le_refl _) (by omega) hk]
      rcases hw with ⟨y, hy, K, hK, rfl⟩ | ⟨hm, -⟩
      · have := field_val (hT y hy) (by omega : K.val < 4096)
        have := (hT y hy).align
        unfold Aligned at hb
        exact h1.fld y hy K (by omega) (by omega)
      · exact hΩ b hm
    have einq : L.mem s2 (inqA (L.curW s)) = L.mem s (inqA (L.curW s)) := by
      rw [k.inqf hct, inqA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
    have esc : L.mem s2 (scA (L.curW s)) = L.mem s (scA (L.curW s)) := by
      rw [k.scf hct, scA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
    refine tcb.thread_control_sched.dec hA a1 t slot (fhc, x2) mcp prio v flags h2 ht hfl
      (WP.spec_and (tcb.install_tcb_cap.cai s2 a1 t slot _ fhc x2 _ (tcb_slot_val _ _) h2
          (Y.fh Ac s t extra hE D s2 agree) (fun s1' a1' hag => Y.slot Ac s t extra hE D slot x2 fhc hxm2 hx02 s1' a1'
            fun b hb hw => (hag b hb hw).trans (agree b hb hw)))
        (WP.spec_mono (tcb.install_tcb_cap.cur0 hA G C hE c2 ht (by simp [layout.tcb.SLOT_FAULT_HANDLER])
          (fun _ => hxw x2 hxm2 hx02)) fun _ hh => hh.1))
      (fun s' hb' f' hne => C.own Ac s s' t hE f' (BlkOK.bxi hb') ht hne)
      (fun _ => ⟨hv, fun e => by rw [e, ec2, einq, esc]; exact ⟨D.cb.nr, hsc0, D.cb.ac hsc0⟩⟩) ?_ ?_
    · intro hf h0
      have hne := hfs hf
      rcases hsp with ⟨e0, -⟩ | ⟨hvS, -, hc⟩
      · exact absurd e0 h0
      obtain ⟨z1, z2, z3⟩ := hc hne
      refine ⟨hvS, by rw [k.scf ht]; exact z1, by rw [(k.fix v hvS).1]; exact z2, fun hb => z3 ?_⟩
      by_cases e : t = L.curW s
      · rw [e, ← h1.cur, est2] at hb
        exact absurd hb nbr_restart
      · rwa [stA_eq, k.fld t ht _ (by simp) (by simp) (by simp) (by simp) (fun e' => absurd e' e), ← stA_eq] at hb
    · intro _ _
      refine ⟨hna t ht, ?_⟩
      rw [k.idleW, hid1]
      exact fun e => Y.idle Ac s t extra hE D e.symm
  split
  · rename_i hne
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st x2 s1 hS) fun fhc _ => ?_
    refine WP.spec_bind (P0.faults.valid_fault_handler.p0 fhc) fun b _ => ?_
    split
    swap
    · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
    exact WP.spec_mono (run _ ssp_flags.2.1 (fun _ e => by rw [ei1, e] at hne; simp at hne) fhc)
      fun r hr => by obtain ⟨r1, r2, r3⟩ := r; exact hr
  · refine WP.spec_bind (P0.obj.Slot.cap.p0 st x2 s1 hS) fun fhc _ => ?_
    refine WP.spec_bind (P0.faults.valid_fault_handler.p0 fhc) fun b _ => ?_
    split
    swap
    · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
    exact WP.spec_mono (run _ ssp_flags.1 (fun hf => absurd ssp_flags.2.2.1 hf) fhc)
      fun r hr => by obtain ⟨r1, r2, r3⟩ := r; exact hr

set_option hygiene false in
/-- An error leaf at a `Cur0` state `hc`. -/
local macro "errC" hc:term : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (Cur0.post $hc)
  | (simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, error.truncated, error.illegal]
     exact (WP.spec_ok _).2 (Cur0.post $hc)))

set_option maxHeartbeats 4000000 in
/-- **`SetIPCBuffer`** after the stall (a64: over `W7.DelGaps`), from `DelGaps` (the buffer slot's
delete), `CdtHyps` (the insert) and the extra slots' placement. -/
theorem tcb.decode_set_ipc_buffer.dec7 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → P1.CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_set_ipc_buffer st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have c1 := h1.cur0 D
  unfold tcb.decode_set_ipc_buffer
  refine WP.spec_bind (tcb.extra_with_length.mem _ 1#u64) ?_
  rintro r ⟨-, hx⟩
  rcases r with x | e
  swap
  · errC c1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm, hx0⟩ := hx x rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun baddr _ => ?_
  refine WP.spec_bind (tcb.derive_for_buffer.slot s1 baddr x) ?_
  rintro r hr
  rcases r with v | e
  swap
  · errC c1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hv2 := hr v rfl
  refine WP.spec_bind (h1.restart0R D) fun s2 c2 => ?_
  unfold tcb.thread_control_caps
  simp only [lift, bind_ok, tcb.UPDATE_FAULT, tcb.UPDATE_TIMEOUT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  simp
  refine WP.spec_bind (Pₘ := fun r : (core.result.Result Unit error.Exc) × S × A =>
    DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2.1) ?_ ?_
  swap
  · rintro ⟨r, s', a'⟩ hr
    dsimp only at hr
    try simp only [uncurry_apply_pair]
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      exact (WP.spec_ok _).2 hr
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 hr
  -- `install_buffer`
  unfold tcb.install_buffer obj.Tcb.slot
  simp only [lift, bind_ok, layout.tcb.SLOT_BUFFER, cte_size]
  refine WP.spec_bind (cdt.delete.cur0 hA (G _ hE) c2 (W7.slotW_to7 (tcb_slotW hT ht))) ?_
  rintro ⟨r, s3, a3⟩ c3
  try simp only [uncurry_apply_pair] at c3 ⊢
  replace c3 := c3.1
  rcases r with _ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c3)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨Ac3, hb3⟩ := c3.bxi
  refine WP.spec_bind (obj.Tcb.set_ipc_buffer.wr s3 t baddr) fun s4 e4 => ?_
  subst e4
  have h4 := (plainW_all (K := 3512#u64) (v := baddr) hb3.blk ht (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp)).1
  have f4 : Fr0 st T Cs Ω H Sg Scs Z s (L.wr s3 (core.num.U64.wrapping_add t 3512#u64) baddr) :=
    Cur0W.trans c3.fr (WritesIn.mono (writesIn_wr (field_aligned (hT t ht) (by simp) (by simp))) fun _ hb =>
      Or.inl (hb ▸ kw_field (Es := EH H) ht (by simp) (by simp) (by simp)))
  obtain ⟨vc, vs⟩ := v
  simp only at hv2
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (tcb.still_valid.nz _ t slot vc vs) fun b hbv => ?_
  refine WP.spec_bind (Pₘ := fun s5 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac3 s5) ?_ fun s5 h5 => ?_
  · split
    · rename_i hb
      have hvs : vs = x := hv2.resolve_right (hbv hb)
      subst hvs
      have hxW := hxw vs hxm hx0
      have hbW : P1.CapW T Ω Sg (core.num.U64.wrapping_add t (core.num.U64.wrapping_mul 2#u64 32#u64)) := by
        have := (tcb_slotW (Ω := Ω) (Sg := Sg) hT ht).2 0#u64 (by simp) (by simp)
        have h0 : ∀ y : U64, core.num.U64.wrapping_add y 0#u64 = y := fun y => by
          apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
        rwa [h0] at this
      unfold cdt.insert
      refine WP.spec_bind (P0.obj.Slot.cap.p0 st vs _ hS) fun sc _ => ?_
      exact WP.spec_mono (C.ins Ac3 s _ vc sc vs _ hE f4 (BlkOK.bxi h4) hxW hbW) fun s' w =>
        (P1.blk_of_capw h4 w fun _ hb => hb).1
    · exact (WP.spec_ok _).2 h4
  refine WP.spec_bind (sched.cur_thread.spec s5) fun ct _ => ?_
  simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
  split
  · refine WP.spec_bind (sched.reschedule_required.blk s5 h5) fun s6 h6 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h6.1))
  · exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h5))


set_option maxHeartbeats 4000000 in
/-- **`SetHighVSpace`** (AArch64, `decode_set_high_vspace`) after the stall: the caller's restart and the install
into the seventh slot `SLOT_HIGH_VSPACE` (W7 install chain), of the null cap or the derived `HighVSpace` cap. -/
theorem tcb.decode_set_high_vspace.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → P1.CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_set_high_vspace st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_set_high_vspace
  refine WP.spec_bind (tcb.extra.mem0 _) ?_
  rintro o ho
  rcases o with _ | x
  · simp only [error.truncated, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  obtain ⟨hxm, hx0⟩ := ho x rfl
  simp only
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s1 hS) fun cap _ => ?_
  cases cap <;> try (simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1))
  · -- the null cap: clear the slot
    refine WP.spec_bind (h1.restart0R D) fun s2 c2 => ?_
    exact WP.spec_mono (tcb.install_tcb_cap.cur0 hA G C hE c2 ht (by simp [layout.tcb.SLOT_HIGH_VSPACE])
      (fun _ => hxw x hxm hx0)) fun r hr => by obtain ⟨r1, r2, r3⟩ := r; exact Cur0.post hr.1
  · -- a `HighVSpace` cap
    dsimp only
    split
    · refine WP.spec_bind (P0.vspace.find_high_asid.p0 st s1 _ hS) fun r _ => ?_
      rcases r with r1 | e
      · simp only
        split
        · refine WP.spec_bind (P0.objects.derive_cap.p0 st s1 x _ hS) fun r2 _ => ?_
          rcases r2 with v | e
          · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            refine WP.spec_bind (h1.restart0R D) fun s2 c2 => ?_
            exact WP.spec_mono (tcb.install_tcb_cap.cur0 hA G C hE c2 ht (by simp [layout.tcb.SLOT_HIGH_VSPACE])
              (fun _ => hxw x hxm hx0)) fun r hr => by obtain ⟨r1, r2, r3⟩ := r; exact Cur0.post hr.1
          · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
              bind_tc_ok]
            exact (WP.spec_ok _).2 (Cur0.post c1)
        · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
      · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
    · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)

set_option maxHeartbeats 4000000 in
/-- **`tcb.decode`** keeps the invariants (a64: every label proved, `SetEPTRoot` / `SetPACKeys` /
`SetHighVSpace` included), from `SspHyps`, `TcbPlace`, `TcbPlace7`, `DelGaps` and `CdtHyps`. -/
theorem tcb.decode.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (Y : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Gd : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (TP : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s : S} {a : A} {lbl t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra)
    (hE : EntAt st P3Ok s) :
    tcb.decode st ar s a lbl t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hS : P0.StoreTotal st := L.total
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have hxw := P.extraW Ac s _ _ hE D
  unfold tcb.decode
  refine WP.spec_bind (smp.remote_tcb_stall.bxi hA s a t D.bxi) ?_
  rintro ⟨s1, a1⟩ ⟨hb1, ea, ec, eid, ecs, fld, eΩ, wn⟩
  have h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1 := ⟨hb1, ea, ec, ecs, fld, wn⟩
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  refine spec_ite (fun hc => ?_) fun hc0 => ?_
  · -- SetPACKeys
    subst hc
    unfold tcb.decode_arch
    rw [if_pos rfl]
    exact tcb.decode_set_pac_keys.dec hA D h1
  refine spec_ite (fun hc => ?_) fun _ => ?_
  · -- SetHighVSpace
    subst hc
    unfold tcb.decode_arch
    rw [if_neg hc0]
    exact tcb.decode_set_high_vspace.dec hA Gd TP hxw D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- SetEPTRoot (AArch64: a Stage-2 `Ept` cap into `SLOT_EPT`)
    have c1 := h1.cur0 D
    have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun x hx => ?_
    simp only [obj.Slot.is_null, bind_ok]
    split
    · simp only [error.truncated, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
    rename_i hx0
    have hxm : x ∈ extra.val := hx ▸ List.getElem_mem hl0
    have hx0' : x ≠ 0#u64 := by simpa using hx0
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s1 hS) fun cap _ => ?_
    cases cap <;> try (simp only [error.illegal, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1))
    dsimp only
    split
    · split
      · refine WP.spec_bind (P0.objects.derive_cap.p0 st s1 x _ hS) fun r2 _ => ?_
        rcases r2 with v | e
        swap
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
            bind_tc_ok]
          exact (WP.spec_ok _).2 (Cur0.post c1)
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, tcb_slot_val]
        have hW := W7.tcb_slotIdxW (Ω := Ω) (Sg := Sg) (i := layout.tcb.SLOT_EPT) hT ht (by simp [layout.tcb.SLOT_EPT])
        refine WP.spec_bind (cdt.delete.cur0 hA (Gd _ hE) (h1.cur0R D) hW) ?_
        rintro ⟨r3, s4, a2⟩ c4
        try simp only [uncurry_apply_pair] at c4 ⊢
        replace c4 := c4.1
        rcases r3 with _ | e
        swap
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
            bind_tc_ok]
          exact (WP.spec_ok _).2 (Cur0.post c4)
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        obtain ⟨Ac4, hb4⟩ := c4.bxi
        have hW0 : W7.CapW T Ω Sg (slotIdx t layout.tcb.SLOT_EPT) := by
          have := hW.2 0#u64 (by simp) (by simp)
          have h0 : core.num.U64.wrapping_add (slotIdx t layout.tcb.SLOT_EPT) 0#u64 = slotIdx t layout.tcb.SLOT_EPT := by
            apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
          rwa [h0] at this
        refine WP.spec_bind (Pₘ := fun s5 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s5) ?_ fun s5 c5 => ?_
        · unfold cdt.insert
          refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s4 hS) fun sc _ => ?_
          exact WP.spec_mono (TP.ins7 Ac4 s s4 v sc x _ hE c4.fr hb4 (hxw x hxm hx0') hW0) fun s' w =>
            c4.capw7 w fun _ hb => hb
        refine WP.spec_bind (sched.cur_thread.spec s5) fun ct ect => ?_
        have e : ct = L.curW s5 := ect
        subst e
        refine WP.spec_bind (Cur0.restartEnd c5) fun s6 c6 => ?_
        exact (WP.spec_ok _).2 (Cur0.post c6)
      · simp only [error.illegal, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
    · simp only [error.illegal, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine spec_ite (fun _ => tcb.decode_read_registers.dec7 E TP D hE h1) fun _ => ?_
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_write_registers.dec hA D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_copy_registers.dec hA TP D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- Suspend
    refine WP.spec_bind (WP.spec_and (h1.restart D) (h1.restart0 D)) fun s2 ⟨⟨h2, hna, _, _⟩, c2⟩ => ?_
    refine WP.spec_bind (sched.suspend.blk7 s2 a1 t h2 ht (hna t ht)
      (fun hne => TP.rcw Ac s s2 t hE c2.fr (BlkOK.bxi h2) ht hne)) ?_
    rintro ⟨s3, a2⟩ h3
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- Resume
    refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
    refine WP.spec_bind (sched.restart.tinv hA s2 a1 t h2 ht) ?_
    rintro ⟨s3, a2⟩ h3
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_configure.dec hA Gd TP hxw D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_priority.dec _ P D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_priority.dec _ P D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_sched_params.dec hA Gd TP P Y D hE h1 eΩ eid
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_ipc_buffer.dec7 hA Gd C hxw D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_space.dec hA Gd TP hxw D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_timeout_endpoint.dec hA Gd TP hxw D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_bind_notification.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- UnbindNotification
    refine WP.spec_bind (obj.Tcb.bound_ntfn.val s1 t) fun i _ => ?_
    split
    · simp only [error.illegal, bind_ok]
      exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))
    refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
    refine WP.spec_bind (notification.unbind_notification.blk s2 t h2 ht) fun s3 h3 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_configure_single_stepping.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.set_breakpoint_checked.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_get_breakpoint.dec E D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- UnsetBreakpoint
    have c1 := h1.cur0 D
    refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun bp _ => ?_
    refine WP.spec_bind (debug.check_bp_num.lt bp) ?_
    rintro r ⟨-, hbp⟩
    rcases r with _ | e
    swap
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 (Cur0.post c1)
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
    refine WP.spec_bind (debug.unset_breakpoint.rf (s := s2) hT ht (hbp rfl)) fun s3 w3 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi (blk_rf h2 w3).1))
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_tls_base.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_flags.dec hA D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.set_timer.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.fpu_transfer.dec hA P D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.fpu_transfer.dec hA P D hE h1
  exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))

/-- **InvGaps' `thread`, from `SspHyps`, `TcbPlace`, `TcbPlace7`, `DelGaps` and `CdtHyps`** (a64: no
`TcbGaps.setEPTRoot`; the AArch64 labels are proved). -/
theorem decGap_thread {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (Y : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Gd : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (TP : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .thread := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact tcb.decode.dec hA Y P E Gd C TP D hE


/-- **InvGaps' `thread`** from `A5.DelPlace`, [J] `A5.VsDel` and `FinGaps4` (with QueueDecTcb2's premises). -/
theorem decGap_thread4 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (Y : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pd : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) (W : VsDel st ar T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (G : FinGaps4 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (TP : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .thread :=
  decGap_thread hA Y P E (delGaps_of_gaps4 hA Pd W G) C TP

end A5
end R
end W7

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errI" : tactic => `(tactic| first
  | exact D.err _
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
      error.illegal, error.truncated, error.range, error.invalid_cap, error.invalid_arg]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))
/-- **`delete_one` of an IRQ's handler slot** (IRQ below 5376) over `Cur0R`: no cap, or a notification cap's
finalisation (`fin_ntfn_obj.cur0` ∧ `.rvi`) and the slot's emptying (`W7.R.A5.cdt.empty_slot.cur0`). -/
theorem cdt.delete_one.irq_cur0R5 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : W7.R.A5.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (Q : IrqSlotAt st T Cs Ω H Sg Rp Scs Nt Z s0)
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
    exact W7.R.A5.cdt.empty_slot.cur0 hA P h hW W7.DelCapOK.null
  · obtain ⟨hn, hH⟩ := hcd.1.1.2.1 n b0 b1 b2 rfl
    refine WP.spec_bind (WP.spec_and (fin_ntfn_obj.cur0 (ar := ar) (a := a) (fin := f) (b0 := b0) (b1 := b1)
      (b2 := b2) h.1 hn hH) (fin_ntfn_obj.rvi (ar := ar) s a n b0 b1 b2 f hb.blk hn hH h.2)) ?_
    rintro ⟨_, s1, a1⟩ ⟨⟨_, h1⟩, r1⟩
    exact W7.R.A5.cdt.empty_slot.cur0 hA P ⟨h1, r1⟩ hW W7.DelCapOK.null

set_option maxHeartbeats 4000000 in
/-- **`decode_irq_handler`** (Ack, SetIRQHandler, ClearIRQHandler) keeps the invariants (AArch64: the IRQ below
5376; the handler slot's deletion over `W7.R.Cur0R`, so no [J] `DelPlaceAt.rv`). -/
theorem interrupt.decode_irq_handler.dec5 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {V : U64 → Prop} {s : S}
    (P : W7.R.A5.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s) (Q : IrqSlotAt st T Cs Ω H Sg Rp Scs Nt Z s)
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
    refine WP.spec_bind (cdt.delete_one.irq_cur0R5 hA P Q h1 hi) ?_
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
    refine WP.spec_bind (cdt.delete_one.irq_cur0R5 hA P Q h1 hi) ?_
    rintro ⟨s2, a1⟩ h2
    exact (WP.spec_ok _).2 h2.post
  · errI

/-- **InvGaps' `irqHandler`, discharged** (AArch64) from the CSpace placement facts, the `rv`-free deletion
placement `W7.R.DelPlace` and [P] `IrqPlace` (IRQs below 5376). -/
theorem decGap_irqHandler5 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {V : U64 → Prop}
    (P : W7.R.A5.DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (Pl : IrqPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .irqHandler := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  rename_i irq
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  exact interrupt.decode_irq_handler.dec5 hA C (P s hE) (Pl.slot s hE) a lbl irq D hE (Pl.irq _ _ _ _ hE D irq rfl)
    (fun sl h1 h2 => SlotW.capw0 (Pl.extra _ _ _ _ hE D sl h1 h2))



end

end Fl4ProofsA64.P1
