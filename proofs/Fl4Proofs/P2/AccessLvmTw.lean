/-
# P2 (line lvm, gen 8): **the acc walk of `local_vm_timer_irq`**, by reuse of the timer interrupt's walks

`localvm.handle_vm_timer_irq_local` is, by its text (`vtimer_eq`, gen 3), a block of checks (`vtimerHead`: the
timer interrupt's IRQ / plan checks, then the VM ones: `RUNNING_VM`, the bound notification `n` and quiet,
`vm_running`, `current_vm_ok`, `sched_quiet`) and the work `vtimerTail`, which is `handle_timer_irq_local`'s tail
with one `vcpu::check` of the current thread inserted before `check_budget` (and `finish` for the inline
`schedule; activate_thread; vcpu::check`). So an accepted run is

  VM head ; [`update_timestamp` … the three cases … ] ; `vcpu::check` (no-op) ; [`check_budget` ; `handle_interrupt`
  ; `schedule` ; `activate_thread`] ; `vcpu::check` (no-op)

and the bracketed parts are exactly what the timer interrupt's walks prove on the guarded store. Those walks were
split (gen 8, `P2/FootTimerIrqAcc.lean`, `P2/FootTimerIrqRG.lean`) into `irq_accG_quiet_core` /
`irq_accG_rr_core`, which take the facts `current_ok` gave instead of `current_ok` itself (the same facts
`current_vm_ok` gives) and return `IrqTailG`: every guarded call of the tail, plus the frame at the
`activate_thread` state (the current thread's non-link words, the `VFar` words). Here:

* `vm_running_true`; `vtimer_split` (the head read back), `vtimerTail_split` (the tail's
  equations, with `IrqCase` for its three cases), `vtimer_sel` (quiet, round-robin or fire, as `irq_sel`);
* `vtimerTail_replay` (the tail on another store answering each call as `st`), `vtimerHead.guardE`
  (`vtimerHead.guard` with the IRQ-state and plan answers given as equations);
* **`vtimer_accG`**: an accepted VM-timer run is the same run on any `GRd` / `GWr` store answering `IrqRd` /
  `IrqWr` (as the timer interrupt's `irq_accG`), the kernel-global words, the bound VCPU's `PENDING` and the bound
  notification's `TAIL_STATE`; both `vcpu::check`s are `vcpu.check_np` / `vcpu.check.guard_vmq` (PENDING = 0 and
  the notification quiet, the words unchanged: `IrqTailG.tK4` / `.fr4` at the `activate_thread` state, which
  `activate_id` keeps since the thread is `RUNNING_VM`). The fire case is a premise `hF` (as `irq_accG`'s).

No named premises (`hF`, the fire case, is discharged or named at the `LocalPath` level).
-/
import Fl4Proofs.P2.AccessLvmPo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (ScAcc rhA tmA RdHead NodeSt)

/-! ## The run read back -/

section split
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

/-- **`vm_running` passed**: the bound VCPU is nonzero and its `PENDING` is 0. -/
theorem vm_running_true {s : S} {ct : U64} (h : localvm.vm_running st s ct = ok true) :
    ∃ v, vcpu.bound st s ct = ok v ∧ v ≠ 0#u64 ∧ vcpu.get st s v vcpu.PENDING = ok 0#u64 := by
  unfold localvm.vm_running at h
  obtain ⟨v, ev, h⟩ := bind_eq_ok h
  by_cases hv : v = 0#u64
  · subst hv; simp at h
  · have hb : (v != 0#u64) = true := bne_iff_ne.mpr hv
    rw [if_pos hb] at h
    obtain ⟨i, ei, h⟩ := bind_eq_ok h
    have e := ok_inj_ff h
    have hi : i = 0#u64 := of_decide_eq_true e
    subst hi
    exact ⟨v, ev, hv, ei⟩

set_option maxHeartbeats 4000000 in
/-- **An accepted VM-timer run, its checks read back** (module docstring). -/
theorem vtimer_split {s s' : S} {a a' : A} {irq n : U64} {p : localtimer.TimerIrqPlan}
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (true, s', a')) :
    ∃ (mx : U64) (tip : localtimer.TimerIrqPlan), layout.irq.MAX = ok mx ∧ ¬ irq > mx ∧
      interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER ∧
      localtimer.plan_objects st s = ok tip ∧ localtimer.same_plan tip p = ok true ∧
      L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM ∧
      obj.Tcb.bound_ntfn st (L.curW s) s = ok n ∧ localvm.ntfn_quiet st s n = ok true ∧
      localvm.vm_running st s (L.curW s) = ok true ∧
      localvm.current_vm_ok st s (L.cpu s) (L.curW s) (L.cscW s) = ok true ∧
      localtimer.sched_quiet st s (L.cpu s) = ok true ∧
      vtimerTail st ar s a irq p (L.curW s) (L.cscW s) (L.cpu s) = ok (true, s', a') := by
  rw [vtimer_eq] at h
  unfold vtimerHead at h
  rw [L.cur_cpu_eq] at h
  simp only [bind_ok] at h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨mx, emx, h⟩ := bind_eq_ok h
  by_cases c1 : irq > mx
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  by_cases c2 : (i1 != interrupt.IRQ_TIMER) = true
  · rw [if_pos c2] at h; simp at h
  rw [if_neg c2] at h
  have hi1 : i1 = interrupt.IRQ_TIMER := by by_contra hne; exact c2 (bne_iff_ne.mpr hne)
  subst hi1
  obtain ⟨tip, etip, h⟩ := bind_eq_ok h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  rw [cur_thread_ok, eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s _)] at h
  simp only [bind_ok] at h
  by_cases c3 : (L.mem s (stA (L.curW s)) != sched.TS_RUNNING_VM) = true
  · rw [if_pos c3] at h; simp at h
  rw [if_neg c3] at h
  have hst : L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM := by
    by_contra hne; exact c3 (bne_iff_ne.mpr hne)
  obtain ⟨i3, e3, h⟩ := bind_eq_ok h
  by_cases c4 : (i3 != n) = true
  · rw [if_pos c4] at h; simp at h
  rw [if_neg c4] at h
  have e3' : i3 = n := by by_contra hne; exact c4 (bne_iff_ne.mpr hne)
  subst e3'
  obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b2, eb2, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b3, eb3, h⟩ := bind_eq_ok h
  cases b3
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b4, eb4, h⟩ := bind_eq_ok h
  cases b4
  · simp at h
  simp only [↓reduceIte] at h
  exact ⟨mx, tip, emx, c1, ei1, etip, eb, hst, e3, eb1, eb2, eb3, eb4, h⟩

set_option maxHeartbeats 4000000 in
/-- **The work of an accepted VM-timer run, step by step** (module docstring). -/
theorem vtimerTail_split {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan} {ct csc cpu : U64}
    (h : vtimerTail st ar s a irq p ct csc cpu = ok (true, s', a')) :
    ∃ (s1 : S) (a1 : A) (now i2 : U64) (b4 due : Bool) (s2 : S) (a2 : A) (x : Bool) (s3 : S) (a3 : A)
      (s4 : S) (a4 : A),
      sched.update_timestamp st ar s a = ok (s1, a1) ∧ sched.cur_time st s1 = ok now ∧
      localtimer.release_due st s1 cpu = ok false ∧ sched.consumed st s1 = ok i2 ∧
      sporadic.sufficient st ar s1 a1 csc i2 = ok b4 ∧ localtimer.timer_due st s1 cpu now = ok due ∧
      IrqCase st ar s1 a1 cpu ct csc p now b4 due ∧
      vcpu.check st ar s1 a1 ct = ok (s2, a2) ∧ sched.check_budget st ar s2 a2 = ok (x, s3, a3) ∧
      interrupt.handle_interrupt st ar s3 a3 irq = ok (s4, a4) ∧ localvm.finish st ar s4 a4 = ok (s', a') := by
  unfold vtimerTail at h
  obtain ⟨⟨s1, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, enow, h⟩ := bind_eq_ok h
  obtain ⟨b3, eb3, h⟩ := bind_eq_ok h
  cases b3
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  obtain ⟨b4, eb4, h⟩ := bind_eq_ok h
  obtain ⟨due, edue, h⟩ := bind_eq_ok h
  obtain ⟨ok1, eok1, h⟩ := bind_eq_ok h
  cases ok1
  · simp at h
  simp only [↓reduceIte] at h
  have hc : IrqCase st ar s1 a1 cpu ct csc p now b4 due := by
    cases b4 <;> cases due
    · simp at eok1; exact .rr rfl rfl eok1
    · simp at eok1
    · exact .quiet rfl rfl
    · simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ↓reduceIte] at eok1
      obtain ⟨b7, e7, h7⟩ := bind_eq_ok eok1
      cases b7
      · simp at h7
      · exact .fire rfl rfl e7
  obtain ⟨⟨s2, a2⟩, evc, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨x, s3, a3⟩, ecb, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨⟨s4, a4⟩, ehi, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s5, a5⟩, efin, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq, true_and] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨s1, a1, now, i2, b4, due, s2, a2, x, s3, a3, s4, a4, eu, enow, eb3, ei2, eb4, edue, hc, evc, ecb, ehi,
    efin⟩

/-- **An accepted VM-timer run is quiet, round-robin or fire** (`irq_sel`'s cases). -/
theorem vtimer_sel {s s' : S} {a a' : A} {irq n : U64} {p : localtimer.TimerIrqPlan}
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (true, s', a')) :
    IrqQuiet st ar s a ∨ IrqRR st ar s a ∨ IrqFire st ar s a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, et⟩ := vtimer_split ar h
  obtain ⟨s1, a1, now, i2, b4, due, -, -, -, -, -, -, -, eu, enow, -, ei2, eb4, edue, hc, -⟩ :=
    vtimerTail_split ar et
  have key : ∀ s1' a1' now' i2' b4' due', sched.update_timestamp st ar s a = ok (s1', a1') →
      sched.cur_time st s1' = ok now' → sched.consumed st s1' = ok i2' →
      sporadic.sufficient st ar s1' a1' (L.cscW s) i2' = ok b4' →
      localtimer.timer_due st s1' (L.cpu s) now' = ok due' → b4' = b4 ∧ due' = due := by
    intro s1' a1' now' i2' b4' due' eu' enow' ei2' eb4' edue'
    rw [eu] at eu'
    have e1 := ok_inj_ff eu'
    simp only [Prod.mk.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    rw [enow] at enow'
    obtain rfl := ok_inj_ff enow'
    rw [ei2] at ei2'
    obtain rfl := ok_inj_ff ei2'
    rw [eb4] at eb4'
    rw [edue] at edue'
    exact ⟨(ok_inj_ff eb4').symm, (ok_inj_ff edue').symm⟩
  cases hc with
  | quiet h4 hd =>
    refine Or.inl fun s1' a1' now' i2' b4' due' e1 e2 e3 e4 e5 => ?_
    obtain ⟨rfl, rfl⟩ := key s1' a1' now' i2' b4' due' e1 e2 e3 e4 e5
    exact ⟨h4, hd⟩
  | rr h4 hd _ =>
    refine Or.inr (Or.inl fun s1' a1' now' i2' b4' due' e1 e2 e3 e4 e5 => ?_)
    obtain ⟨rfl, rfl⟩ := key s1' a1' now' i2' b4' due' e1 e2 e3 e4 e5
    exact ⟨h4, hd⟩
  | fire h4 hd _ =>
    refine Or.inr (Or.inr fun s1' a1' now' i2' b4' due' e1 e2 e3 e4 e5 => ?_)
    obtain ⟨rfl, rfl⟩ := key s1' a1' now' i2' b4' due' e1 e2 e3 e4 e5
    exact ⟨h4, hd⟩

end split

/-! ## Replaying the work, and the head with given answers -/

section replay
variable {S : Type} {st st' : machine.Store S} {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **Replay of the work** on a store answering each call of an accepted run as `st`. -/
theorem vtimerTail_replay {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    {ct csc cpu now i2 : U64} {b4 due x : Bool} {s1 s2 s3 s4 : S} {a1 a2 a3 a4 : A}
    (eu : sched.update_timestamp st ar s a = ok (s1, a1))
    (gu : sched.update_timestamp st' ar s a = sched.update_timestamp st ar s a)
    (enow : sched.cur_time st s1 = ok now) (gnow : sched.cur_time st' s1 = sched.cur_time st s1)
    (eb3 : localtimer.release_due st s1 cpu = ok false)
    (gb3 : localtimer.release_due st' s1 cpu = localtimer.release_due st s1 cpu)
    (ei2 : sched.consumed st s1 = ok i2) (gi2 : sched.consumed st' s1 = sched.consumed st s1)
    (eb4 : sporadic.sufficient st ar s1 a1 csc i2 = ok b4)
    (gb4 : sporadic.sufficient st' ar s1 a1 csc i2 = sporadic.sufficient st ar s1 a1 csc i2)
    (edue : localtimer.timer_due st s1 cpu now = ok due)
    (gdue : localtimer.timer_due st' s1 cpu now = localtimer.timer_due st s1 cpu now)
    (hc : IrqCase st ar s1 a1 cpu ct csc p now b4 due)
    (grr : b4 = false → localtimer.round_robin_ok st' ar s1 a1 cpu ct csc now =
      localtimer.round_robin_ok st ar s1 a1 cpu ct csc now)
    (gfire : due = true → localtimer.fire_ok st' s1 cpu ct p now = localtimer.fire_ok st s1 cpu ct p now)
    (evc : vcpu.check st ar s1 a1 ct = ok (s2, a2))
    (gvc : vcpu.check st' ar s1 a1 ct = vcpu.check st ar s1 a1 ct)
    (ecb : sched.check_budget st ar s2 a2 = ok (x, s3, a3))
    (gcb : sched.check_budget st' ar s2 a2 = sched.check_budget st ar s2 a2)
    (ehi : interrupt.handle_interrupt st ar s3 a3 irq = ok (s4, a4))
    (ghi : interrupt.handle_interrupt st' ar s3 a3 irq = interrupt.handle_interrupt st ar s3 a3 irq)
    (gfin : localvm.finish st' ar s4 a4 = ok (s', a')) :
    vtimerTail st' ar s a irq p ct csc cpu = ok (true, s', a') := by
  unfold vtimerTail
  rw [gu, eu]
  simp only [bind_ok, uncurry_apply_pair]
  rw [gnow, enow]
  simp only [bind_ok]
  rw [gb3, eb3]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  rw [gi2, ei2]
  simp only [bind_ok]
  rw [gb4, eb4]
  simp only [bind_ok]
  rw [gdue, edue]
  simp only [bind_ok]
  cases hc with
  | quiet h4 hd =>
    subst h4 hd
    simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ↓reduceIte, bind_ok]
    rw [gvc, evc]; simp only [bind_ok, uncurry_apply_pair]
    rw [gcb, ecb]; simp only [bind_ok, uncurry_apply_pair]
    rw [ghi, ehi]; simp only [bind_ok, uncurry_apply_pair]
    rw [gfin]; simp only [bind_ok, uncurry_apply_pair]
  | fire h4 hd hf =>
    subst h4 hd
    simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ↓reduceIte, bind_ok]
    rw [gfire rfl, hf]
    simp only [bind_ok, ↓reduceIte]
    rw [gvc, evc]; simp only [bind_ok, uncurry_apply_pair]
    rw [gcb, ecb]; simp only [bind_ok, uncurry_apply_pair]
    rw [ghi, ehi]; simp only [bind_ok, uncurry_apply_pair]
    rw [gfin]; simp only [bind_ok, uncurry_apply_pair]
  | rr h4 hd hr =>
    subst h4 hd
    simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ↓reduceIte, bind_ok]
    rw [grr rfl, hr]
    simp only [bind_ok, ↓reduceIte]
    rw [gvc, evc]; simp only [bind_ok, uncurry_apply_pair]
    rw [gcb, ecb]; simp only [bind_ok, uncurry_apply_pair]
    rw [ghi, ehi]; simp only [bind_ok, uncurry_apply_pair]
    rw [gfin]; simp only [bind_ok, uncurry_apply_pair]

end replay

section headE
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- **`vtimerHead.guard` with the IRQ-state and plan answers given as equations** (`IrqTailG.gi1` / `.gtip`). -/
theorem vtimerHead.guardE (s : S) {A : Type} (a : A) (irq : U64) (p : localtimer.TimerIrqPlan) (n csc : U64)
    (gi1 : interrupt.irq_state gS s irq = interrupt.irq_state st s irq)
    (gtip : localtimer.plan_objects gS s = localtimer.plan_objects st s)
    (hcsc : sched.cur_sc st s = ok csc) (hR : LvmRd st R s (L.curW s) csc)
    (hvp : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64)) vcpu.PENDING))
    (hn : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    {T1 T2 : U64 → U64 → U64 → Result (Bool × S × A)}
    (hT : T1 (L.curW s) csc (L.cpu s) = T2 (L.curW s) csc (L.cpu s)) :
    vtimerHead gS s a irq p n T1 = vtimerHead st s a irq p n T2 := by
  unfold vtimerHead
  rw [PathObl.gst_cur_cpu, L.cur_cpu_eq]
  simp only [bind_ok]
  rw [gi1, gtip,
    PathObl.sched.cur_thread.guard s hR.cur, cur_thread_ok, PathObl.sched.cur_sc.guard s hR.curSc, hcsc]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.state.guard _ s hR.state, PathObl.obj.Tcb.bound_ntfn.guard _ s hR.bntfn,
    ntfn_quiet.guard s n hn, vm_running.guard s _ hR.vcpu hvp,
    current_vm_ok.guard s _ _ _ hR.aff hR.yld hR.sc hR.scCore hR.idle hR.dom hR.curDom,
    sched_quiet.guard s hR.act hR.domTime hR.ipi, hT]

end headE

/-! ## The walk -/

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 16000000 in
/-- **An accepted VM-timer run on the guarded store**, quiet or round-robin, the fire case a premise (module
docstring). `v` is the current thread's bound VCPU (`hvb`). -/
theorem vtimer_accG {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq n v : U64} {p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRd st Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) → W w)
    (hIq : IrqOk st s → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hKr : IrqOk st s → R (krA (L := L) s)) (hTab : IrqOk st s → PathObl.RdTab (L := L) R s)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hvb : vcpu.bound st s (L.curW s) = ok v)
    (hRp : R (core.num.U64.wrapping_add v vcpu.PENDING))
    (hRn : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (fP : VFar st T Cs Scs Z s (core.num.U64.wrapping_add v vcpu.PENDING))
    (fN : n ≠ 0#u64 → VFar st T Cs Scs Z s (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (hF : IrqFire st ar s a → localvm.handle_vm_timer_irq_local gS ar s a irq p n = ok (true, s', a'))
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (true, s', a')) :
    localvm.handle_vm_timer_irq_local gS ar s a irq p n = ok (true, s', a') := by
  have hsel := vtimer_sel ar h
  obtain ⟨mx, tip, emx, hle, ei1, etip, eb, hstv, en, enq, evr, eok, eq, et⟩ := vtimer_split ar h
  obtain ⟨s1, a1, now, i2, b4, due, s2, a2, x, s3, a3, s4, a4, eu, enow, erel, ei2, eb4, edue, hc, evc1, ecb,
    ehi, efin⟩ := vtimerTail_split ar et
  obtain ⟨s5, a5, s6, a6, t, esc, eac, ett, evc5⟩ := vfinish_split ar efin
  obtain ⟨v', ev', hv0, hp0⟩ := vm_running_true evr
  rw [hvb] at ev'
  obtain rfl := ok_inj_ff ev'
  have hnq := nq_true enq
  obtain ⟨haff, hy0, hsct, hcore⟩ := current_vm_ok_true eok
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  have hX := hI.2.2.1
  have hS := hI.2.2.2.2
  have hO := hX.1
  have hcs : L.cscW s ∈ Scs := hX.2.2.cur
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := scq_of hO hS hcs
  -- `s → s1`: the timestamp update
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
  simp only at er
  have m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b :=
    fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2
  have htcb1 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y K hy hK h8
    exact m1 _ (field_aligned (hT y hy) hK h8) (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CUR_TIME]))
      (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CONSUMED]))
  have hout1 : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b := fun b hb =>
    m1 b hb.1 (fun e => out_ne_node hb hcC hN (by simp [layout.node.CUR_TIME]) (congrArg UScalar.val e).symm)
      (fun e => out_ne_node hb hcC hN (by simp [layout.node.CONSUMED]) (congrArg UScalar.val e).symm)
  -- `vcpu.check` at `s1` reports nothing
  have eb1 : vcpu.bound st s1 (L.curW s) = ok v := by
    rw [vcpu_bound_congr (htcb1 hcT (by simp) (by simp))]; exact hvb
  have en1 : obj.Tcb.bound_ntfn st (L.curW s) s1 = ok n := by
    rw [bound_ntfn_congr (by unfold boundA; exact htcb1 hcT (by simp) (by simp))]; exact en
  have ep1 : vcpu.get st s1 v vcpu.PENDING = ok 0#u64 := by
    rw [vcpu_get_congr (hout1 _ fP.1)]; exact hp0
  have hq1 : n ≠ 0#u64 → ∀ x, obj.Ntfn.state st n s1 = ok x → x ≠ obj.NTFN_ACTIVE := fun hn x ex =>
    hnq hn x (by rw [← ntfn_state_congr (hout1 _ (fN hn).1)]; exact ex)
  have evc1' := vcpu.check_np ar s1 a1 (L.curW s) v n eb1 hv0 ep1 en1 hq1
  rw [evc1'] at evc1
  obtain ⟨rfl, rfl⟩ : s1 = s2 ∧ a1 = a2 := by
    have e := ok_inj_ff evc1
    simp only [Prod.mk.injEq] at e
    exact e
  -- the guarded store: what it admits
  have hok : IrqOk st s := ⟨haff, hsct, hcore⟩
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gRd hok _ (nodeAt_aligned hN h1 h2) (Or.inl ⟨o, h1, h2, rfl⟩)
  have cR : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      K.val ≠ 3496 → K.val ≠ 3504 → R (core.num.U64.wrapping_add (L.curW s) K) := fun K h1 h2 h3 h4 h5 h6 =>
    gRd hok _ (field_aligned ht' h2 h3) (Or.inr (Or.inl ⟨K, h1, h2, h3, h4, h5, h6, rfl⟩))
  have scR : ∀ b, InSC (L.cscW s) (Z (L.cscW s)) b → Aligned b → R b := fun b hb ha =>
    gRd hok _ ha (Or.inr (Or.inr (Or.inl hb)))
  have rSt : R (stA (L.curW s)) := by rw [stA_eq]; exact cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rVc : R (core.num.U64.wrapping_add (L.curW s) 3664#u64) :=
    cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rBn : R (core.num.U64.wrapping_add (L.curW s) 3368#u64) :=
    cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rMx : R (maxA (L.cscW s)) := scR _ hcq.2.2.2.1 hcq.2.2.2.2
  have rCore : R (scCoreA (L.cscW s)) := by
    obtain ⟨hP, hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
    have hcv : layout.sc.CORE.val = 16 := by simp [layout.sc.CORE]
    exact scR _ ⟨by unfold scCoreA; rw [hv]; omega, by unfold scCoreA; rw [hv, hcv]; omega⟩
      (by unfold Aligned scCoreA; rw [hv, hcv]; omega)
  have gvc1 : vcpu.check gS ar s1 a1 (L.curW s) = vcpu.check st ar s1 a1 (L.curW s) :=
    vcpu.check.guard_vmq ar s1 a1 (L.curW s) v n rSt rVc rBn hRp hRn eb1 hv0 ep1 en1 hq1
  have hR : LvmRd st R s (L.curW s) (L.cscW s) :=
    { cur := nR _ (by rw [curth_val]; omega) (by rw [curth_val])
      curSc := nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      vcpu := rVc
      bntfn := rBn
      aff := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      yld := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      sc := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      scCore := rCore
      idle := nR _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])
      dom := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      curDom := hD1 hok
      state := rSt
      maxA := by rw [hsct]; exact rMx
      inq := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      act := nR _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      domTime := hD2 hok
      ipi := nR _ (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]) }
  have ebv : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) = v := by
    rw [eq_of_spec_fd (vcpu.bound.spec (L := L) s _)] at hvb; exact ok_inj_ff hvb
  -- the tail, quiet or round-robin, by the timer interrupt's cores
  have ecpu : st.cur_cpu s = ok (L.cpu s) := by rw [L.cur_cpu_eq]
  have ecsc : sched.cur_sc st s = ok (L.cscW s) := eq_of_spec_fd (sched.cur_sc.spec (L := L) s)
  have hwS : IrqOk st s → L.mem s (stA (L.curW s)) = sched.TS_RESTART → ∀ X,
      L.mem X (stA (L.curW s)) = sched.TS_RESTART → L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING :=
    fun _ hr => absurd (hstv.symm.trans hr) (by simp [sched.TS_RUNNING_VM, sched.TS_RESTART])
  have fin : IrqTailG st gS ar R T Cs Scs Z s a irq (L.cpu s) (L.curW s) (L.cscW s) now i2 p b4 s1 s3 s4 s5 s6
      a1 a3 a4 a5 t → due = false →
      localvm.handle_vm_timer_irq_local gS ar s a irq p n = ok (true, s', a') := by
    intro G hd
    subst hd
    have et' := G.et
    subst et'
    -- `activate_thread` keeps the `RUNNING_VM` thread
    have hy5 : L.mem s5 (yieldA (L.curW s)) = 0#u64 := by
      unfold yieldA; rw [G.tK4 _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hy0
    have hs5 : L.mem s5 (stA (L.curW s)) = L.mem s (stA (L.curW s)) := by
      rw [stA_eq, G.tK4 _ (by simp) (by simp) (by simp) (by simp) (by simp)]
    have eac' := activate_id ar s5 a5 (by rw [G.cur4]; exact hy5)
      (by rw [G.cur4, hs5, hstv]; simp [sched.TS_RUNNING_VM, sched.TS_RESTART])
    rw [eac'] at eac
    obtain ⟨rfl, rfl⟩ : s5 = s6 ∧ a5 = a6 := by
      have e := ok_inj_ff eac
      simp only [Prod.mk.injEq] at e
      exact e
    -- the final `vcpu.check` reports nothing
    have eb5 : vcpu.bound st s5 (L.curW s) = ok v := by
      rw [vcpu_bound_congr (G.tK4 _ (by simp) (by simp) (by simp) (by simp) (by simp))]; exact hvb
    have en5 : obj.Tcb.bound_ntfn st (L.curW s) s5 = ok n := by
      rw [bound_ntfn_congr (by unfold boundA; exact G.tK4 _ (by simp) (by simp) (by simp) (by simp) (by simp))]
      exact en
    have ep5 : vcpu.get st s5 v vcpu.PENDING = ok 0#u64 := by
      rw [vcpu_get_congr (G.fr4 _ fP)]; exact hp0
    have hq5 : n ≠ 0#u64 → ∀ x, obj.Ntfn.state st n s5 = ok x → x ≠ obj.NTFN_ACTIVE := fun hn x ex =>
      hnq hn x (by rw [← ntfn_state_congr (G.fr4 _ (fN hn))]; exact ex)
    have gvc5 := vcpu.check.guard_vmq (gS := gS) ar s5 a5 (L.curW s) v n G.rSt rVc rBn hRp hRn eb5 hv0 ep5 en5 hq5
    have gfin : localvm.finish gS ar s4 a4 = ok (s', a') := by
      unfold localvm.finish
      rw [G.gsc, esc]
      simp only [bind_ok, uncurry_apply_pair]
      rw [G.gac, eac']
      simp only [bind_ok, uncurry_apply_pair]
      rw [G.gt, ett]
      simp only [bind_ok]
      rw [gvc5]
      exact evc5
    have hTl : vtimerTail gS ar s a irq p (L.curW s) (L.cscW s) (L.cpu s) =
        vtimerTail st ar s a irq p (L.curW s) (L.cscW s) (L.cpu s) := by
      rw [et]
      exact vtimerTail_replay ar eu G.gu enow G.gnow erel G.gb3 ei2 G.gi2 eb4 G.gb4 edue G.gdue hc G.grr
        (fun h => nomatch h) evc1' gvc1 ecb G.gcb ehi G.ghi gfin
    rw [vtimer_eq, vtimerHead.guardE (gS := gS) s a irq p n (L.cscW s) G.gi1 G.gtip ecsc hR
      (fun _ => by rw [ebv]; exact hRp) hRn (T1 := vtimerTail gS ar s a irq p) (T2 := vtimerTail st ar s a irq p) hTl,
      ← vtimer_eq]
    exact h
  rcases hsel with hq | hq | hq
  · obtain ⟨rfl, rfl⟩ := hq s1 a1 now i2 b4 due eu enow ei2 eb4 edue
    exact fin (irq_accG_quiet_core ar hA hI gRd gWr hIq hD1 hD2 hwS ecpu emx hle ei1 etip eb (cur_thread_ok s)
      ecsc haff hsct hcore hy0 eq eu enow erel ei2 eb4 edue ecb ehi esc eac ett) rfl
  · obtain ⟨rfl, rfl⟩ := hq s1 a1 now i2 b4 due eu enow ei2 eb4 edue
    have hrr : localtimer.round_robin_ok st ar s1 a1 (L.cpu s) (L.curW s) (L.cscW s) now = ok true := by
      cases hc with
      | quiet h4 _ => exact nomatch h4
      | fire h4 _ _ => exact nomatch h4
      | rr _ _ hr => exact hr
    exact fin (irq_accG_rr_core ar hA hI gRd gWr hIq hD1 hD2 hwS hKr hTab hAs ecpu emx hle ei1 etip eb
      (cur_thread_ok s) ecsc haff hsct hcore hy0 eq eu enow erel ei2 eb4 edue hrr ecb ehi esc eac ett) rfl
  · exact hF hq

end main

end Fl4Proofs.P2
