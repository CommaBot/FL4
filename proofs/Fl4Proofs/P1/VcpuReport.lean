/-
P1 (KENTRY-PLAN int6): **`vcpu.report` for any state predicate kept by its
writes** (FL4 #80 / #81, main 279c8261).

Since #80 `vcpu::report` also answers a *full-state* VMEnter caller (message
info `NUM_MRS` at entry, `vcpu::full_reply`) with 30 message registers on a
notification (`report_loop2`/`report_loop3`, `finish_notification`), and since
#81 every completion sets the fault IP to the next IP. Every write of the
report is one of four kinds: a message register of the thread (`msg.set_mr`,
`i < 30`: a register or a word of its IPC buffer, the buffer looked up at the
report's start), one of three of its registers (`MSG_INFO`, `BADGE`,
`FAULT_IP`), the VCPU's `PENDING` word, and finally the thread made running.
`vcpu.report.gen` proves the report from those four steps for any predicate
`P` (and the post `Q` of the last); the callers instantiate it (`Cur0` in
`QueueVcpu`; the signal paths in `QueueSignal` / `QueueFootS` / `TimerRBSig`).
-/
import Fl4Proofs.P0.Auto
import Fl4Proofs.P1.Store
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- The step kinds `vcpu.report` writes with, for a predicate `P` (module docstring). -/
structure RepSteps (st : machine.Store S) (t : U64) (Bok : U64 → Prop) (P : S → Prop) (vOk : U64 → Prop) : Prop where
  mr : ∀ (s1 : S) (b i v : U64), Bok b → P s1 → i.val < 30 → msg.set_mr st s1 t b i v ⦃ r => P r.2 ⦄
  reg : ∀ (s1 : S) (r v : U64), P s1 → (r = layout.reg.MSG_INFO ∨ r = layout.reg.BADGE ∨ r = layout.reg.FAULT_IP) →
    obj.Tcb.set_reg st t s1 r v ⦃ P ⦄
  pend : ∀ (s1 : S) (v : U64), P s1 → vOk v → vcpu.set st s1 v vcpu.PENDING 0#u64 ⦃ P ⦄

variable {t : U64} {Bok : U64 → Prop} {P : S → Prop} {vOk : U64 → Prop}

/-- `report_loop0`: MR `i..29` from the exit record or zero. -/
theorem vcpu.report_loop0.gen (R : RepSteps st t Bok P vOk) {s : S} {v b i : U64} {pending saved : Bool}
    (hb : Bok b) (h : P s) : vcpu.report_loop0 st s t v pending b saved i ⦃ P ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.report_loop0
  apply loop.spec_decr_nat (measure := fun y => 30 - y.2.val) (inv := fun y => P y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    unfold vcpu.report_loop0.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 30 := by simpa [vcpu.NUM_MRS] using hj
    repeat' (first
      | (refine WP.spec_bind (R.mr _ _ _ _ hb h1 hj') ?_; rintro ⟨_, s2⟩ h2
         try simp only [uncurry_apply_pair]
         step as ⟨j2, hj2⟩
         exact ⟨h2, by first | omega | (dsimp only; omega)⟩)
      | split
      | (step as ⟨_, _⟩))
  · exact h

/-- `report_loop2` (the full-state branch's copy of `report_loop0`). -/
theorem vcpu.report_loop2.gen (R : RepSteps st t Bok P vOk) {s : S} {v b i : U64} {pending saved : Bool}
    (hb : Bok b) (h : P s) : vcpu.report_loop2 st s t v pending b saved i ⦃ P ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.report_loop2
  apply loop.spec_decr_nat (measure := fun y => 30 - y.2.val) (inv := fun y => P y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    unfold vcpu.report_loop2.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 30 := by simpa [vcpu.NUM_MRS] using hj
    repeat' (first
      | (refine WP.spec_bind (R.mr _ _ _ _ hb h1 hj') ?_; rintro ⟨_, s2⟩ h2
         try simp only [uncurry_apply_pair]
         step as ⟨j2, hj2⟩
         exact ⟨h2, by first | omega | (dsimp only; omega)⟩)
      | split
      | (step as ⟨_, _⟩))
  · exact h

/-- `report_loop1`: MR `10 + j` from the guest registers. -/
theorem vcpu.report_loop1.gen (R : RepSteps st t Bok P vOk) {s : S} {v b j : U64}
    (hb : Bok b) (h : P s) : vcpu.report_loop1 st s t v b j ⦃ P ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.report_loop1
  apply loop.spec_decr_nat (measure := fun y => 15 - y.2.val) (inv := fun y => P y.1)
  · rintro ⟨s1, k⟩ h1
    simp only at h1
    unfold vcpu.report_loop1.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hk
    have hk' : k.val < 15 := by simpa using hk
    step as ⟨i0, hi0⟩
    step as ⟨i1, _⟩
    step as ⟨i2, _⟩
    refine WP.spec_bind (Fl4Proofs.P0.vcpu.get.p0 _ _ _ _ hS) fun val _ => ?_
    refine WP.spec_bind (R.mr _ _ _ _ hb h1 (by omega)) ?_
    rintro ⟨_, s2⟩ h2
    try simp only [uncurry_apply_pair]
    step as ⟨k2, hk2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

/-- `report_loop3` (the full-state branch's copy of `report_loop1`). -/
theorem vcpu.report_loop3.gen (R : RepSteps st t Bok P vOk) {s : S} {v b j : U64}
    (hb : Bok b) (h : P s) : vcpu.report_loop3 st s t v b j ⦃ P ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.report_loop3
  apply loop.spec_decr_nat (measure := fun y => 15 - y.2.val) (inv := fun y => P y.1)
  · rintro ⟨s1, k⟩ h1
    simp only at h1
    unfold vcpu.report_loop3.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hk
    have hk' : k.val < 15 := by simpa using hk
    step as ⟨i0, hi0⟩
    step as ⟨i1, _⟩
    step as ⟨i2, _⟩
    refine WP.spec_bind (Fl4Proofs.P0.vcpu.get.p0 _ _ _ _ hS) fun val _ => ?_
    refine WP.spec_bind (R.mr _ _ _ _ hb h1 (by omega)) ?_
    rintro ⟨_, s2⟩ h2
    try simp only [uncurry_apply_pair]
    step as ⟨k2, hk2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

/-- One `report` step: a write of the four kinds (`RepSteps`), a read (the
explicit P0 lemmas, so that no write is ever taken as a read), an `if` (a
state-valued one keeps `P`, a value one is a read), or pure arithmetic. -/
macro "rep_step" R:term "," hb:term "," hfin:term "," hS:term "," hA:term "," Pt:term : tactic => `(tactic| first
  | exact $hfin _ (by assumption)
  | exact (WP.spec_ok _).2 (by assumption)
  | exact (WP.spec_ok _).2 trivial
  | (refine WP.spec_bind (RepSteps.mr $R _ _ _ _ $hb (by assumption) (by simp)) ?_; rintro ⟨_, _⟩ _;
     try simp only [uncurry_apply_pair])
  | (refine WP.spec_bind (RepSteps.reg $R _ _ _ (by assumption) (by simp)) ?_; intro _ _)
  | (refine WP.spec_bind (vcpu.report_loop0.gen $R $hb (by assumption)) ?_; intro _ _)
  | (refine WP.spec_bind (vcpu.report_loop1.gen $R $hb (by assumption)) ?_; intro _ _)
  | (refine WP.spec_bind (vcpu.report_loop2.gen $R $hb (by assumption)) ?_; intro _ _)
  | (refine WP.spec_bind (vcpu.report_loop3.gen $R $hb (by assumption)) ?_; intro _ _)
  | exact Fl4Proofs.P0.vcpu.get.p0 _ _ _ _ $hS
  | exact Fl4Proofs.P0.vcpu.read_vmcs.p0 _ _ _ _ $hS
  | (refine WP.spec_bind (Fl4Proofs.P0.vcpu.get.p0 _ _ _ _ $hS) fun _ _ => ?_)
  | (refine WP.spec_bind (Fl4Proofs.P0.vcpu.read_vmcs.p0 _ _ _ _ $hS) fun _ _ => ?_)
  | (refine WP.spec_bind (Fl4Proofs.P0.obj.Tcb.reg.p0 _ _ _ _ $hS) fun _ _ => ?_)
  | (refine WP.spec_bind (Fl4Proofs.P0.msg.syscall_arg.p0 _ _ _ _ _ $hS) fun _ _ => ?_)
  | (refine WP.spec_bind (P0.ArchTotal.virtualization $hA _) fun _ _ => ?_)
  | (refine WP.spec_bind (Pₘ := $Pt) (_root_.p0_if _ _ _ _ (fun _ => ?_) (fun _ => ?_)) fun _ _ => ?_)
  | (refine WP.spec_bind (Pₘ := fun _ => True) (_root_.p0_if _ _ _ _ (fun _ => ?_) (fun _ => ?_)) fun _ _ => ?_)
  | (refine _root_.p0_if _ _ _ _ (fun _ => ?_) (fun _ => ?_))
  | (simp only [lift, bind_ok])
  | split
  | step
  | scalar_tac)

set_option maxHeartbeats 4000000 in
/-- `finish_notification` from the four step kinds. -/
theorem vcpu.finish_notification.gen {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (R : RepSteps st t Bok P vOk) {Q : S → Prop} (hfin : ∀ s1, P s1 → sched.set_thread_state st s1 t sched.TS_RUNNING ⦃ Q ⦄)
    {s : S} {a : A} {b badge : U64} {vectoring : Bool} (hb : Bok b) (h : P s) :
    vcpu.finish_notification st ar s a t b badge vectoring ⦃ Q ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.finish_notification
  refine WP.spec_bind (hA.virtualization a) fun _ _ => ?_
  refine _root_.p0_if _ _ _ _ (fun _ => ?_) (fun _ => ?_)
  all_goals repeat' (rep_step R, hb, hfin, hS, hA, P)

set_option maxHeartbeats 16000000 in
/-- **`vcpu.report` from the four step kinds** (module docstring): `P` kept by
the thread's message registers (`Bok` of the buffer looked up at the start),
its three registers and the bound VCPU's `PENDING` word (`vOk` of the TCB's
VCPU word, when nonzero), and `Q` after it is made running. -/
theorem vcpu.report.gen {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (R : RepSteps st t Bok P vOk) {Q : S → Prop} (hfin : ∀ s1, P s1 → sched.set_thread_state st s1 t sched.TS_RUNNING ⦃ Q ⦄)
    {s : S} {a : A} {badge : U64} (h : P s)
    (hbuf : msg.lookup_ipc_buffer st s true t ⦃ Bok ⦄)
    (hv : L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 → vOk (L.mem s (core.num.U64.wrapping_add t 3664#u64))) :
    vcpu.report st ar s a t badge ⦃ Q ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.report vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  have hvk : v ≠ 0#u64 → vOk v := fun hv0 => by rw [ev] at hv0 ⊢; exact hv hv0
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact WP.spec_bind (Fl4Proofs.P0.vcpu.get.p0 _ _ _ _ hS) fun _ _ => (WP.spec_ok _).2 trivial
    · exact (WP.spec_ok _).2 trivial) fun pending _ => ?_
  refine WP.spec_bind hbuf fun b hb => ?_
  refine WP.spec_bind (Fl4Proofs.P0.vcpu.full_reply.p0 _ _ _ hS) fun full _ => ?_
  have FN := fun (s1 : S) (vec : Bool) (h1 : P s1) =>
    vcpu.finish_notification.gen (a := a) (badge := badge) (vectoring := vec) hA R hfin hb h1
  have PD : ∀ s1, P s1 → v ≠ 0#u64 → vcpu.set st s1 v vcpu.PENDING 0#u64 ⦃ P ⦄ :=
    fun s1 h1 hv0 => R.pend s1 v h1 (hvk hv0)
  repeat' (first
    | exact FN _ _ (by assumption)
    | (refine WP.spec_bind (PD _ (by assumption) (by first | assumption | simpa using ‹_›)) ?_; intro _ _)
    | rep_step R, hb, hfin, hS, hA, P)

end

end Fl4Proofs.P1
