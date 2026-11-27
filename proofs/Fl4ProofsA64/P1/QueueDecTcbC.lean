/-
P1 (aarch64): **the thread family over `TcbPlace9`** — `TcbPlace8` without its `own` field, which is **false as
stated** (handoff §30: after `ARMVCPURun(vc)` a thread's `RUN_VCPU` is `vc`, vcpu.rs:862; `own` makes
`vc + OWNER_CPU` (vcpu.rs:17) a `UserW` word, hence `∉ Ω`, but the VCPU is a `.other 12` heap object, so
`vc + 8 ∈ Ω`, as [P] `VcpuW` says at a decode of `vc`).

* **[P] `TcbPlace9`**: `TcbPlace8`'s `rcv` and `ins7`, nothing else (`TcbPlace9.of8` / `.toRcv`: a strict
  weakening; no new statement content). `TCB_SetSchedParams`' migration (`migrate_tcb`'s `OWNER_CPU := cpu + 1`,
  smp.rs:25–33) now goes through `rcv` (`VcWords`, an `Ω \ Sg` word): QueueScBindV's
  `tcb.thread_control_sched.decV`.
* By script (`handoff/a64-wip/gen27/gen_dectcbc.py`; cuts QueueDecTcbB 213–365 and 372–1188), namespace
  `W7.R.A5.B.C`: `tcb.decode_read_registers.dec8`, `tcb.decode_copy_registers.dec8`, the install chain,
  `tcb.decode_set_sched_params.dec` (over `decV`, `C.rcv` for `C.own`), `tcb.decode.dec`, `decGap_thread`,
  **`B.C.decGap_thread4`** — QueueDecTcbB's text with `TcbPlace8` → `TcbPlace9`.

Named premises: [P] `TcbPlace9` (`TcbPlace8` minus the false `own`); the others as QueueDecTcbB's.
No existing statement changed.
-/
import Fl4ProofsA64.P1.QueueDecTcbB
import Fl4ProofsA64.P1.QueueScBindV
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- **[P] The thread family's AArch64 placement facts, without the false `own`**: `TcbPlace8`'s `rcv` (a run
VCPU's words are aligned words of `Ω` off `Sg`; source QueueUnbindB's `VcPl.rcv`: `RUN_VCPU(ct) := vc` only in
`decode_run`, vcpu.rs:862, for an invoked `.Vcpu vc` cap, cleared by `cancel_run` / `complete_run` / `unbind`)
and `ins7` (QueueDecTcb2's `TcbPlace7.ins7`, unchanged). -/
structure TcbPlace9 (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop where
  rcv : ∀ (Ac : Set U64) (s0 s : S) (p : U64), EntAt st P3Ok s0 → Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → p ∈ T → L.mem s (runVcpuA p) ≠ 0#u64 →
    VcWords Ω Sg (L.mem s (runVcpuA p))
  ins7 : ∀ (Ac : Set U64) (s0 s : S) (c srcC : capability.Cap) (x y : U64), EntAt st P3Ok s0 →
    Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    CapW T Ω Sg x → W7.CapW T Ω Sg y →
    cdt.insert_with_cap st s c srcC x y ⦃ s' => WritesIn st s s' (W7.CapW T Ω Sg) ⦄

/-- `TcbPlace9` is `TcbPlace8` without `own`. -/
theorem TcbPlace9.of8 (h : TcbPlace8 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok :=
  ⟨h.rcv, h.ins7⟩

/-- **The corrected `ScBindOwn` from `TcbPlace9`** (no premise beyond `rcv`). -/
theorem TcbPlace9.scBindOwnV (h : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    ScBindOwnV st T Cs Ω H Sg Rp Scs Nt Z U P3Ok :=
  ScBindOwnV.of_rcv h.rcv

namespace W7
namespace R
namespace A5
namespace B
namespace C

set_option maxHeartbeats 4000000 in
/-- **`ReadRegisters`** after the stall, the caller's buffer from `XferHyps`. -/
theorem tcb.decode_read_registers.dec8 {A : Type _} {ar : machine.Arch A} (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (TP : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_read_registers st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have c1 := h1.cur0 D
  have est : L.mem s1 (stA (L.curW s1)) = L.mem s (stA (L.curW s)) := by
    rw [h1.cur, stA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  have hr := runnable_ok D.run
  unfold tcb.decode_read_registers
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · simp only [error.truncated, error.sys, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun flags _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun n _ => ?_
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · step as ⟨i, _⟩
    simp only [error.range, error.sys, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  step as ⟨i, _⟩
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · simp only [error.range, error.sys, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (sched.cur_thread.spec s1) fun ct ect => ?_
  simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
  split
  · simp only [error.illegal, error.sys, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  rename_i hne
  have hne' : t ≠ L.curW s := by
    intro e; apply hne; rw [e, show ct = L.curW s from ect.trans h1.cur]; simp
  refine WP.spec_bind (WP.spec_and (h1.restart D)
    (tcb.restart_caller.blk (Es := ∅) s1 h1.bxi.blk (est ▸ hr.1) (est ▸ hr.2))) ?_
  rintro s2 ⟨⟨h2, hna, ec2, -⟩, ⟨-, f2, est2, k2⟩⟩
  rw [h1.cur] at est2
  simp only [lift, bind_ok]
  have hU2 : UserOK st T Cs Ω H U s2 := D.user.ksb (f2.1.trans h1.node.1)
  have nb2 : ¬ BlockedR (L.mem s2 (stA (L.curW s2))) := by rw [ec2, est2]; exact nbr_restart
  rw [← ec2] at hct
  have FR : Fr0 st T Cs Ω H Sg Scs Z s s2 := Cur0W.trans c1.fr (Foot.cur0w f2 (Set.empty_subset _))
  refine WP.spec_bind (tcb.read_registers.bxi8 E h2 ht (hna t ht) hct nb2 hU2 ⟨s, hE, FR⟩
    (fun hne => TP.rcv Ac s s2 t hE FR (BlkOK.bxi h2) ht hne)) ?_
  rintro ⟨s3, a3⟩ h3
  exact (WP.spec_ok _).2 (DecPost.ok_bxi h3)

/-! ## `CopyRegisters` -/

set_option maxHeartbeats 2000000 in
theorem tcb.copy_registers.blk8 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A}
    {dest src flags : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hd : dest ∈ T) (hs : src ∈ T)
    (hna : L.actionW s ≠ src)
    (hrc : L.mem s (runVcpuA src) ≠ 0#u64 →
      VcWords Ω Sg (L.mem s (runVcpuA src))) :
    tcb.copy_registers st ar s a dest src flags ⦃ r => r.1 = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold tcb.copy_registers
  simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_ ?_
  · split
    · exact WP.spec_mono (sched.suspend.blk8 s a src h hs hna hrc) fun r hr => by obtain ⟨s1, a1⟩ := r; exact hr
    · exact (WP.spec_ok _).2 h
  rintro ⟨s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_ ?_
  · split
    · exact WP.spec_mono (sched.restart.tinv hA s1 a1 dest h1 hd) fun r hr => by obtain ⟨s2, a2⟩ := r; exact hr
    · exact (WP.spec_ok _).2 h1
  rintro ⟨s2, a2⟩ h2
  try simp only [uncurry_apply_pair]
  have TL : ∀ s3 : S, WritesIn st s2 s3 (XferFoot T ∅) →
      (do
        let s5 ← tcb.post_modify_registers st s3 dest
        let t ← sched.cur_thread st s5
        let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq dest t
        if b then do
          let s6 ← sched.reschedule_required st s5
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s6, a2)
        else ok (core.result.Result.Ok (), s5, a2)) ⦃ r => r.1 = .Ok () ∧
          BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ := fun s3 w3 => by
    refine WP.spec_bind (tcb.post_modify_registers.rf (s := s3) hT hd) fun s5 w5 => ?_
    have h5 := (blk_rf h2 (rf_trans w3 w5)).1
    refine WP.spec_bind (sched.cur_thread.spec s5) fun t1 _ => ?_
    simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
    split
    · exact WP.spec_bind (sched.reschedule_required.blk s5 h5) fun s6 h6 => (WP.spec_ok _).2 ⟨rfl, h6.1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, h5⟩
  split
  · refine WP.spec_bind (tcb.copy_registers_loop0.rf (s0 := s2) hT hd (WritesIn.refl _ _)) fun s3 w3 => ?_
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st dest s3 _ hS) fun pc _ => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.rf (v := pc) (s := s3) hT hd (by simp [layout.reg.NEXT_IP]))
      fun s4 w4 => ?_
    split
    · refine WP.spec_bind (tcb.copy_registers_loop1.rf (s0 := s2) hT hd (rf_trans w3 w4)) fun s5 w5 => ?_
      exact TL s5 w5
    · exact TL s4 (rf_trans w3 w4)
  · split
    · refine WP.spec_bind (tcb.copy_registers_loop2.rf (s0 := s2) hT hd (WritesIn.refl _ _)) fun s3 w3 => ?_
      exact TL s3 w3
    · exact TL s2 (WritesIn.refl _ _)

set_option maxHeartbeats 2000000 in
/-- **`CopyRegisters`** after the stall. -/
theorem tcb.decode_copy_registers.dec8 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (TP : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_copy_registers st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_copy_registers
  refine WP.spec_bind (tcb.extra_with_length.mem _ 1#u64) ?_
  rintro r ⟨-, hx⟩
  rcases r with x | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c1)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm, hx0⟩ := hx x rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun flags _ => ?_
  refine WP.spec_bind (tcb.thread_arg.tcb (pos := 1#u64) D h1.node hxm hx0) ?_
  rintro r ⟨-, hT2⟩
  rcases r with src | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c1)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hsrc := hT2 src rfl
  refine WP.spec_bind (h1.stall hA (y := src)) ?_
  rintro ⟨s1', a1'⟩ h1'
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (WP.spec_and (h1'.restart D) (h1'.restart0 D)) fun s2 ⟨⟨h2, hna, _, _⟩, c2⟩ => ?_
  refine WP.spec_mono (tcb.copy_registers.blk8 hA h2 ht hsrc (hna src hsrc)
    (fun hne => TP.rcv Ac s s2 src hE c2.fr (BlkOK.bxi h2) hsrc hne)) ?_
  rintro ⟨r, s3, a3⟩ ⟨e, h3⟩
  simp only at e h3 ⊢
  subst e
  exact DecPost.ok_bxi (BlkOK.bxi h3)

/-! ## `ConfigureSingleStepping` -/


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
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
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
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
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
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
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
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
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
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
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
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
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
    refine tcb.thread_control_sched.decV hA a1 t slot (fhc, x2) mcp prio v flags h2 ht hfl
      (WP.spec_and (tcb.install_tcb_cap.cai s2 a1 t slot _ fhc x2 _ (tcb_slot_val _ _) h2
          (Y.fh Ac s t extra hE D s2 agree) (fun s1' a1' hag => Y.slot Ac s t extra hE D slot x2 fhc hxm2 hx02 s1' a1'
            fun b hb hw => (hag b hb hw).trans (agree b hb hw)))
        (WP.spec_mono (tcb.install_tcb_cap.cur0 hA G C hE c2 ht (by simp [layout.tcb.SLOT_FAULT_HANDLER])
          (fun _ => hxw x2 hxm2 hx02)) fun _ hh => hh.1))
      (fun s' hb' f' hne => C.rcv Ac s s' t hE f' (BlkOK.bxi hb') ht hne)
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
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
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
`SetHighVSpace` included), from `SspHyps`, `TcbPlace`, `TcbPlace9`, `DelGaps` and `CdtHyps`. -/
theorem tcb.decode.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (Y : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Gd : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (TP : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
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
  refine spec_ite (fun _ => tcb.decode_read_registers.dec8 E TP D hE h1) fun _ => ?_
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_write_registers.dec hA D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_copy_registers.dec8 hA TP D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- Suspend
    refine WP.spec_bind (WP.spec_and (h1.restart D) (h1.restart0 D)) fun s2 ⟨⟨h2, hna, _, _⟩, c2⟩ => ?_
    refine WP.spec_bind (sched.suspend.blk8 s2 a1 t h2 ht (hna t ht)
      (fun hne => TP.rcv Ac s s2 t hE c2.fr (BlkOK.bxi h2) ht hne)) ?_
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

/-- **InvGaps' `thread`, from `SspHyps`, `TcbPlace`, `TcbPlace9`, `DelGaps` and `CdtHyps`** (a64: no
`TcbGaps.setEPTRoot`; the AArch64 labels are proved). -/
theorem decGap_thread {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (Y : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Gd : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (TP : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
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
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (TP : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .thread :=
  decGap_thread hA Y P E (delGaps_of_gaps4 hA Pd W G) C TP


end C
end B
end A5
end R
end W7

end

end Fl4ProofsA64.P1
