/-
# P2 (line lvm, gen 6): **an accepted `local_vm_exit` run, read back** (the equations the acc walk starts from)

* `current_vm_ok_true`: the head's `current_vm_ok` passed: the current thread is homed here, yields to no SC, runs
  on the current SC, which is on this core;
* `aq_true`: `awaken_quiet` passed: no timer and no release due;
* `vexit_split`: an accepted `handle_vcpu_exit_local` is its checks passing at the entry state (the current thread
  `RUNNING_VM`, bound to `v ≠ 0` and to `n`, `PENDING` read as `i3`, a quiet notification when `i3 = 0`,
  `current_vm_ok`, `is_schedulable`, `sched_quiet`) and its work `vexitTail` returning `true`;
* `vexitTail_split`, `vfinish_split`: the work's and `finish`'s steps, each an equation of the real run;
* `vcpu.check_np`: `vcpu.check` of a `RUNNING_VM` thread with `PENDING = 0` and a quiet bound notification
  changes nothing.

No named premises.
-/
import Fl4Proofs.P2.AccessLvmSets
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`current_vm_ok` passed** (module docstring). -/
theorem current_vm_ok_true {s : S} {cpu ct csc : U64} (h : localvm.current_vm_ok st s cpu ct csc = ok true) :
    L.mem s (affA ct) = cpu ∧ L.mem s (yieldA ct) = 0#u64 ∧ L.mem s (scA ct) = csc ∧
      L.mem s (scCoreA csc) = cpu := by
  unfold localvm.current_vm_ok at h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  split at h
  · simp at h
  obtain ⟨t, -, h⟩ := bind_eq_ok h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  split at h
  swap
  · simp at h
  rw [aff_ok] at h
  simp only [bind_ok] at h
  split at h
  swap
  · simp at h
  rename_i h1
  rw [eq_of_spec_fd (obj.Tcb.yield_to.spec (L := L) s ct)] at h
  simp only [bind_ok] at h
  split at h
  swap
  · simp at h
  rename_i h2
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  split at h
  · simp at h
  rw [eq_of_spec_fd (obj.Tcb.sc.spec (L := L) s ct)] at h
  simp only [bind_ok] at h
  split at h
  swap
  · simp at h
  rename_i h3
  rw [eq_of_spec_fd (obj.Sc.cpu.spec (L := L) s csc)] at h
  simp only [bind_ok] at h
  split at h
  swap
  · simp at h
  rename_i h4
  exact ⟨h1, h2, h3, h4⟩

/-- **`awaken_quiet` passed**: no timer and no release due. -/
theorem aq_true {s : S} {cpu now : U64} (h : localvm.awaken_quiet st s cpu now = ok true) :
    localtimer.timer_due st s cpu now = ok false ∧ localtimer.release_due st s cpu = ok false := by
  unfold localvm.awaken_quiet at h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
    cases b1
    · exact ⟨eb, eb1⟩
    · simp at h
  · simp at h

variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **An accepted VM exit, read back** (module docstring). -/
theorem vexit_split {s s' : S} {a a' : A} {v n : U64}
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a')) :
    ∃ i3, L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM ∧ v ≠ 0#u64 ∧
      vcpu.bound st s (L.curW s) = ok v ∧ obj.Tcb.bound_ntfn st (L.curW s) s = ok n ∧
      vcpu.get st s v vcpu.PENDING = ok i3 ∧ (i3 = 0#u64 → localvm.ntfn_quiet st s n = ok true) ∧
      localvm.current_vm_ok st s (L.cpu s) (L.curW s) (L.cscW s) = ok true ∧
      sched.is_schedulable st s (L.curW s) = ok true ∧ localtimer.sched_quiet st s (L.cpu s) = ok true ∧
      vexitTail st ar s a (L.curW s) (L.cscW s) (L.cpu s) = ok (true, s', a') := by
  rw [vexit_eq] at h
  unfold vexitHead at h
  rw [cur_thread_ok, L.cur_cpu_eq, eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at h
  simp only [bind_ok] at h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s _)] at h
  simp only [bind_ok] at h
  by_cases c1 : (L.mem s (stA (L.curW s)) != sched.TS_RUNNING_VM) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  have hst : L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM := by
    by_contra hne; exact c1 (bne_iff_ne.mpr hne)
  by_cases c2 : v = 0#u64
  · rw [if_pos c2] at h; simp at h
  rw [if_neg c2] at h
  obtain ⟨i1, e1, h⟩ := bind_eq_ok h
  by_cases c3 : (i1 != v) = true
  · rw [if_pos c3] at h; simp at h
  rw [if_neg c3] at h
  have e1' : i1 = v := by
    by_contra hne; exact c3 (bne_iff_ne.mpr hne)
  subst e1'
  obtain ⟨i2, e2, h⟩ := bind_eq_ok h
  by_cases c4 : (i2 != n) = true
  · rw [if_pos c4] at h; simp at h
  rw [if_neg c4] at h
  have e2' : i2 = n := by
    by_contra hne; exact c4 (bne_iff_ne.mpr hne)
  subst e2'
  obtain ⟨i3, e3, h⟩ := bind_eq_ok h
  have tail : ∀ {Y : Result (Bool × S × A)},
      (do
        let b1 ← localvm.current_vm_ok st s (L.cpu s) (L.curW s) (L.cscW s)
        if b1 then
          let b2 ← sched.is_schedulable st s (L.curW s)
          if b2 then
            let b3 ← localtimer.sched_quiet st s (L.cpu s)
            if b3 then vexitTail st ar s a (L.curW s) (L.cscW s) (L.cpu s) else ok (false, s, a)
          else ok (false, s, a)
        else ok (false, s, a)) = ok (true, s', a') →
      localvm.current_vm_ok st s (L.cpu s) (L.curW s) (L.cscW s) = ok true ∧
      sched.is_schedulable st s (L.curW s) = ok true ∧ localtimer.sched_quiet st s (L.cpu s) = ok true ∧
      vexitTail st ar s a (L.curW s) (L.cscW s) (L.cpu s) = ok (true, s', a') := by
    intro Y h
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
    exact ⟨eb1, eb2, eb3, h⟩
  by_cases c5 : i3 = 0#u64
  · rw [if_pos c5] at h
    obtain ⟨b, eb, h⟩ := bind_eq_ok h
    cases b
    · simp at h
    simp only [↓reduceIte] at h
    exact ⟨i3, hst, c2, e1, e2, e3, fun _ => eb, tail (Y := ok (false, s, a)) h⟩
  · rw [if_neg c5] at h
    exact ⟨i3, hst, c2, e1, e2, e3, fun e => absurd e c5, tail (Y := ok (false, s, a)) h⟩

/-- **The work of an accepted VM exit, read back.** -/
theorem vexitTail_split {s s' : S} {a a' : A} {ct csc cpu : U64}
    (h : vexitTail st ar s a ct csc cpu = ok (true, s', a')) :
    ∃ s1 a1 now i4 s2 a2 x s3 a3, sched.update_timestamp st ar s a = ok (s1, a1) ∧
      sched.cur_time st s1 = ok now ∧ sched.consumed st s1 = ok i4 ∧
      sporadic.sufficient st ar s1 a1 csc i4 = ok true ∧ localvm.awaken_quiet st s1 cpu now = ok true ∧
      vcpu.check st ar s1 a1 ct = ok (s2, a2) ∧ sched.check_budget st ar s2 a2 = ok (x, s3, a3) ∧
      localvm.finish st ar s3 a3 = ok (s', a') := by
  unfold vexitTail at h
  obtain ⟨⟨s1, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, enow, h⟩ := bind_eq_ok h
  obtain ⟨i4, ei4, h⟩ := bind_eq_ok h
  obtain ⟨b4, eb4, h⟩ := bind_eq_ok h
  cases b4
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b5, eb5, h⟩ := bind_eq_ok h
  cases b5
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨s2, a2⟩, evc, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨x, s3, a3⟩, ecb, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨⟨s4, a4⟩, efin, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq, true_and] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨s1, a1, now, i4, s2, a2, x, s3, a3, eu, enow, ei4, eb4, eb5, evc, ecb, efin⟩

/-- **`finish`, read back.** -/
theorem vfinish_split {s s' : S} {a a' : A} (h : localvm.finish st ar s a = ok (s', a')) :
    ∃ s4 a4 s5 a5 t, sched.schedule st ar s a = ok (s4, a4) ∧ sched.activate_thread st ar s4 a4 = ok (s5, a5) ∧
      sched.cur_thread st s5 = ok t ∧ vcpu.check st ar s5 a5 t = ok (s', a') := by
  unfold localvm.finish at h
  obtain ⟨⟨s4, a4⟩, e4, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s5, a5⟩, e5, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  exact ⟨s4, a4, s5, a5, t, e4, e5, et, h⟩

/-- **`vcpu.check` with nothing to report** changes nothing (module docstring). -/
theorem vcpu.check_np (s : S) (a : A) (t v n : U64) (eb : vcpu.bound st s t = ok v) (hv0 : v ≠ 0#u64)
    (ep : vcpu.get st s v vcpu.PENDING = ok 0#u64) (en : obj.Tcb.bound_ntfn st t s = ok n)
    (hq : n ≠ 0#u64 → ∀ x, obj.Ntfn.state st n s = ok x → x ≠ obj.NTFN_ACTIVE) :
    vcpu.check st ar s a t = ok (s, a) := by
  have hb : (v != 0#u64) = true := bne_iff_ne.mpr hv0
  unfold vcpu.check
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s t)]
  simp only [bind_ok]
  split
  · rfl
  rw [eb]
  simp only [bind_ok]
  rw [if_pos hb, ep]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [en]
  simp only [bind_ok]
  by_cases h0 : n = 0#u64
  · subst h0; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hv0]
  · have hb2 : (n != 0#u64) = true := bne_iff_ne.mpr h0
    rw [if_pos hb2]
    obtain ⟨x, ex, -⟩ := spec_ex_fd (obj.Ntfn.state.spec (L := L) s n)
    rw [ex]
    simp only [bind_ok]
    rw [if_neg (hq h0 x ex), if_neg hv0]


/-- The reads `vcpu.check_np` needs, moved to a state with the same words. -/
theorem vcpu_get_congr {s s1 : S} {v off : U64}
    (h : L.mem s1 (core.num.U64.wrapping_add v off) = L.mem s (core.num.U64.wrapping_add v off)) :
    vcpu.get st s1 v off = vcpu.get st s v off := by
  unfold vcpu.get
  simp only [lift, bind_ok, L.read_eq, h]

theorem ntfn_state_congr {s s1 : S} {n : U64}
    (h : L.mem s1 (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) =
      L.mem s (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE)) :
    obj.Ntfn.state st n s1 = obj.Ntfn.state st n s := by
  unfold obj.Ntfn.state obj.Ntfn.tail_state
  simp only [lift, bind_ok, L.read_eq, h]

theorem vcpu_bound_congr {s s1 : S} {t : U64}
    (h : L.mem s1 (core.num.U64.wrapping_add t 3664#u64) = L.mem s (core.num.U64.wrapping_add t 3664#u64)) :
    vcpu.bound st s1 t = vcpu.bound st s t := by
  rw [eq_of_spec_fd (vcpu.bound.spec (L := L) s1 t), eq_of_spec_fd (vcpu.bound.spec (L := L) s t), h]

theorem bound_ntfn_congr {s s1 : S} {t : U64} (h : L.mem s1 (boundA t) = L.mem s (boundA t)) :
    obj.Tcb.bound_ntfn st t s1 = obj.Tcb.bound_ntfn st t s := by
  rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s1 t), eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s t), h]

/-- **`activate_thread` of a current thread yielding to no SC and not restarting** changes nothing. -/
theorem activate_id (s : S) (a : A) (hy : L.mem s (yieldA (L.curW s)) = 0#u64)
    (hr : L.mem s (stA (L.curW s)) ≠ sched.TS_RESTART) :
    sched.activate_thread st ar s a = ok (s, a) := by
  unfold sched.activate_thread
  rw [cur_thread_ok]
  simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.yield_to.spec (L := L) s _), hy]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, uncurry_apply_pair]
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s _)]
  simp only [bind_ok]
  rw [if_neg hr]


/-- **`ntfn_quiet` passed**: a bound notification is not active. -/
theorem nq_true {s : S} {n : U64} (h : localvm.ntfn_quiet st s n = ok true) :
    n ≠ 0#u64 → ∀ x, obj.Ntfn.state st n s = ok x → x ≠ obj.NTFN_ACTIVE := by
  intro hn x ex
  unfold localvm.ntfn_quiet at h
  rw [if_neg hn, ex] at h
  simp only [bind_ok] at h
  have e := ok_inj_ff h
  exact bne_iff_ne.mp e

end

end Fl4Proofs.P2
