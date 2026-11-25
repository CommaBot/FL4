/-
# P2 (line p2lt): `AccessIoFin`'s `syscall.finish` lemmas without the I/O port invocation modules

A copy of p2io's `P2/AccessIoFin.lean` (`schedRes`, `schedule_res_eq`, `sched.awaken.guard_none`,
`vcpu.check.guard_running`, `schedRes.guard`, `syscall.finish.guard_resume`, …) in the namespace
`Fl4Proofs.P2.PathObl.LT`, importing `AccessIo` instead of `AccessIoInv`: none of it uses the invocation lemmas,
and this keeps the timer modules off `AccessIoDec` / `AccessIoInv` until the reconciled par/p2io lands; then
this module goes and the timer modules use `AccessIoFin` again.

Premises: none.
-/
import Fl4Proofs.P2.AccessTail
import Fl4Proofs.P2.AccessIo
import Fl4Proofs.P1.FastSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl.LT
open fl4_core Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]

/-- `schedule`'s tail with the action `RESUME_CURRENT`, on any store. -/
def schedRes {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s3 : S) (a2 : A) : Result (S × A) := do
  let s4 ← sched.set_action m s3 sched.ACTION_RESUME_CURRENT
  let (s5, a3) ← sched.switch_sched_context m ar s4 a2
  let c ← m.cur_cpu s5
  let i ← obj.node_get m s5 c layout.node.REPROGRAM
  let (s6, a4) ←
    if i != 0#u64
    then
      do
      let (s7, a5) ← sched.set_next_interrupt m ar s5 a3
      let s8 ← obj.node_set m s7 c layout.node.REPROGRAM 0#u64
      ok (s8, a5)
    else ok (s5, a3)
  smp.send_pending m ar s6 a4

omit L in
theorem check_domain_time_any (m : machine.Store S) (s : S) : sched.check_domain_time m s = ok s := by
  unfold sched.check_domain_time sched.is_cur_domain_expired
  rw [if_neg num_domains_one]; simp only [bind_ok, bind_tc_ok, Bool.false_eq_true, ↓reduceIte]

omit L in
/-- `schedule` with nothing due and the action `RESUME_CURRENT`, on any store. -/
theorem schedule_res_eq {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)
    (haw : sched.awaken m ar s a = ok (s, a))
    (hac : sched.action m s = ok sched.ACTION_RESUME_CURRENT) :
    sched.schedule m ar s a = schedRes m ar s a := by
  unfold sched.schedule
  rw [haw]; simp only [bind_ok, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
  rw [check_domain_time_any]; simp only [bind_ok, bind_tc_ok]
  rw [hac]; simp only [bind_ok, bind_tc_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem timer.fire.guard_none {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (hRc : R (L.nodeAt s (L.cpu s) layout.node.CUR_TIME))
    (hRt : R (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))
    (h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64) :
    timer.fire (PathObl.guard st R W) ar s a = ok (s, a) := by
  have hb : (0#u64 : U64) < timer.FIRE_BATCH := by unfold timer.FIRE_BATCH; decide
  unfold timer.fire timer.fire_loop
  simp only [guard_cur_cpu, L.cur_cpu_eq, bind_ok, bind_tc_ok]
  rw [obj.node_get.guard s _ _ hRc, node_get_ok]
  simp only [bind_ok, bind_tc_ok]
  rw [loop]
  unfold timer.fire_loop.body
  simp only [hb, ↓reduceIte, guard_cur_cpu, L.cur_cpu_eq, bind_ok, bind_tc_ok]
  rw [obj.node_get.guard s _ _ hRt, node_get_ok, h0]
  simp only [bind_ok, bind_tc_ok, is_null_ok, decide_true, ↓reduceIte]

theorem sched.awaken_loop.guard_none (s : S) (fuel : U64)
    (hRr : R (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))
    (h1 : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = 0#u64) :
    sched.awaken_loop (PathObl.guard st R W) s fuel = ok s := by
  unfold sched.awaken_loop
  rw [loop]
  unfold sched.awaken_loop.body
  by_cases hf : fuel > 0#u64
  swap
  · simp only [hf, ↓reduceIte, bind_ok, bind_tc_ok]
  obtain ⟨f1, hf1, -⟩ := spec_ex_fd (U64.sub_spec (x := fuel) (y := 1#u64) (by scalar_tac))
  simp only [hf, ↓reduceIte, hf1, guard_cur_cpu, L.cur_cpu_eq, bind_ok, bind_tc_ok]
  rw [obj.node_get.guard s _ _ hRr, node_get_ok, h1]
  simp only [bind_ok, bind_tc_ok, is_null_ok, decide_true, ↓reduceIte]

/-- **`awaken` with nothing due** on the guarded store. -/
theorem sched.awaken.guard_none {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (hRc : R (L.nodeAt s (L.cpu s) layout.node.CUR_TIME))
    (hRt : R (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))
    (hRr : R (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))
    (h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64)
    (h1 : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = 0#u64) :
    sched.awaken (PathObl.guard st R W) ar s a = ok (s, a) := by
  unfold sched.awaken
  rw [timer.fire.guard_none ar s a hRc hRt h0]
  simp only [bind_ok, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
  rw [sched.awaken_loop.guard_none s _ hRr h1]
  simp only [bind_ok, bind_tc_ok]

theorem running_ne_vm : (sched.TS_RUNNING != sched.TS_RUNNING_VM) = true := by
  unfold sched.TS_RUNNING sched.TS_RUNNING_VM; decide

/-- `vcpu.check` of a running thread: reads its state, returns. -/
theorem vcpu.check.guard_running {A : Type} (ar : machine.Arch A) (s : S) (a : A) (t : U64)
    (hr : R (stA t)) (hs : L.mem s (stA t) = sched.TS_RUNNING) :
    vcpu.check (PathObl.guard st R W) ar s a t = ok (s, a) ∧ vcpu.check st ar s a t = ok (s, a) := by
  constructor
  · unfold vcpu.check
    rw [obj.Tcb.state.guard t s hr, state_ok', hs]
    simp only [bind_ok, bind_tc_ok, running_ne_vm, ↓reduceIte]
  · unfold vcpu.check
    rw [state_ok', hs]
    simp only [bind_ok, bind_tc_ok, running_ne_vm, ↓reduceIte]

/-- The node's words at a state with the entry's kernel base and core. -/
theorem nd_at {s X : S} (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (k : L.ksb X = L.ksb s) (c : L.cpu X = L.cpu s) (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    R (L.nodeAt X (L.cpu X) o) ∧ W (L.nodeAt X (L.cpu X) o) := by
  rw [c, nodeAt_of_ksb k]; exact hNd o ho h8

/-- **`schedRes`** on the guarded store: the action word, then p2sl's
`switch_sched_context` / `set_next_interrupt` lemmas at the real run's
states (`hsw`, `hfr`), the node's `REPROGRAM` and `IPI_PENDING`. -/
theorem schedRes.guard {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hsw : ∀ s4, sched.set_action st s sched.ACTION_RESUME_CURRENT = ok s4 →
      sched.switch_sched_context (PathObl.guard st R W) ar s4 a = sched.switch_sched_context st ar s4 a)
    (hfr : ∀ s4 s5 a3, sched.set_action st s sched.ACTION_RESUME_CURRENT = ok s4 →
      sched.switch_sched_context st ar s4 a = ok (s5, a3) →
      L.ksb s5 = L.ksb s ∧ L.cpu s5 = L.cpu s ∧
      (L.mem s5 (L.nodeAt s5 (L.cpu s5) layout.node.REPROGRAM) ≠ 0#u64 →
        sched.set_next_interrupt (PathObl.guard st R W) ar s5 a3 = sched.set_next_interrupt st ar s5 a3 ∧
        ∀ s7 a5, sched.set_next_interrupt st ar s5 a3 = ok (s7, a5) → L.ksb s7 = L.ksb s ∧ L.cpu s7 = L.cpu s)) :
    schedRes (PathObl.guard st R W) ar s a = schedRes st ar s a := by
  have rp : layout.node.REPROGRAM.val < 4288 := by simp [layout.node.REPROGRAM]
  have rp8 : layout.node.REPROGRAM.val % 8 = 0 := by simp [layout.node.REPROGRAM]
  have ip : layout.node.IPI_PENDING.val < 4288 := by simp [layout.node.IPI_PENDING]
  have ip8 : layout.node.IPI_PENDING.val % 8 = 0 := by simp [layout.node.IPI_PENDING]
  have sa : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
  have sa8 : layout.node.SCHED_ACTION.val % 8 = 0 := by simp [layout.node.SCHED_ACTION]
  unfold schedRes
  rw [sched.set_action.guard s _ (hNd _ sa sa8).2]
  refine bind_guard_congr rfl fun s4 hs4 => ?_
  rw [hsw s4 hs4]
  refine bind_guard_congr rfl fun x5 hs5 => ?_
  obtain ⟨s5, a3⟩ := x5
  obtain ⟨k5, c5, hnx⟩ := hfr s4 s5 a3 hs4 hs5
  simp only [Aeneas.Std.uncurry_apply_pair]
  simp only [guard_cur_cpu, L.cur_cpu_eq, bind_ok, bind_tc_ok]
  rw [obj.node_get.guard s5 _ _ (nd_at hNd k5 c5 _ rp rp8).1, node_get_ok]
  simp only [bind_ok, bind_tc_ok]
  refine bind_guard_congr ?_ fun x6 hs6 => ?_
  · by_cases h : (L.mem s5 (L.nodeAt s5 (L.cpu s5) layout.node.REPROGRAM) != 0#u64) = true
    · rw [if_pos h, if_pos h]
      obtain ⟨e7, -⟩ := hnx (bne_iff_ne.1 h)
      rw [e7]
      refine bind_guard_congr rfl fun x7 hs7 => ?_
      obtain ⟨s7, a5⟩ := x7
      obtain ⟨k7, c7⟩ := (hnx (bne_iff_ne.1 h)).2 s7 a5 hs7
      simp only [Aeneas.Std.uncurry_apply_pair]
      rw [obj.node_set.guard s7 _ _ _ (by rw [c5, ← c7]; exact (nd_at hNd k7 c7 _ rp rp8).2)]
    · rw [if_neg h, if_neg h]
  · obtain ⟨s6, a4⟩ := x6
    have k6 : L.ksb s6 = L.ksb s ∧ L.cpu s6 = L.cpu s := by
      by_cases h : (L.mem s5 (L.nodeAt s5 (L.cpu s5) layout.node.REPROGRAM) != 0#u64) = true
      · rw [if_pos h] at hs6
        obtain ⟨⟨s7, a5⟩, hs7, hs6⟩ := bind_eq_ok hs6
        obtain ⟨k7, c7⟩ := (hnx (bne_iff_ne.1 h)).2 s7 a5 hs7
        simp only [Aeneas.Std.uncurry_apply_pair] at hs6
        obtain ⟨s8, hs8, hs6⟩ := bind_eq_ok hs6
        rw [eq_ok_of_spec (obj.node_set.spec (L := L) s7 _ _ _)] at hs8
        have e := ok_inj_ff hs6
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, -⟩ := e
        cases ok_inj_ff hs8
        exact ⟨by rw [L.ksb_wr]; exact k7, by rw [LawfulStore.cpu_wr]; exact c7⟩
      · rw [if_neg h] at hs6
        have e := ok_inj_ff hs6
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, -⟩ := e
        exact ⟨k5, c5⟩
    simp only [Aeneas.Std.uncurry_apply_pair]
    have ipd := nd_at hNd k6.1 k6.2 _ ip ip8
    exact smp.send_pending.guard ar s6 a4 ipd.1 ipd.2

/-- **`finish` after a local invocation** (module docstring): nothing due,
the action `RESUME_CURRENT`, then `schedRes.guard`'s hypotheses, p2sl's
`activate_thread.guard` at the state `schedule` reaches, and a running
current thread at the state `activate_thread` reaches. -/
theorem syscall.finish.guard_resume {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64)
    (h1 : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = 0#u64)
    (ha : L.actionW s = sched.ACTION_RESUME_CURRENT)
    (hsw : ∀ s4, sched.set_action st s sched.ACTION_RESUME_CURRENT = ok s4 →
      sched.switch_sched_context (PathObl.guard st R W) ar s4 a = sched.switch_sched_context st ar s4 a)
    (hfr : ∀ s4 s5 a3, sched.set_action st s sched.ACTION_RESUME_CURRENT = ok s4 →
      sched.switch_sched_context st ar s4 a = ok (s5, a3) →
      L.ksb s5 = L.ksb s ∧ L.cpu s5 = L.cpu s ∧
      (L.mem s5 (L.nodeAt s5 (L.cpu s5) layout.node.REPROGRAM) ≠ 0#u64 →
        sched.set_next_interrupt (PathObl.guard st R W) ar s5 a3 = sched.set_next_interrupt st ar s5 a3 ∧
        ∀ s7 a5, sched.set_next_interrupt st ar s5 a3 = ok (s7, a5) → L.ksb s7 = L.ksb s ∧ L.cpu s7 = L.cpu s))
    (hact : ∀ s1 a1, sched.schedule st ar s a = ok (s1, a1) →
      sched.activate_thread (PathObl.guard st R W) ar s1 a1 = sched.activate_thread st ar s1 a1)
    (hvc : ∀ s1 a1 s2 a2, sched.schedule st ar s a = ok (s1, a1) →
      sched.activate_thread st ar s1 a1 = ok (s2, a2) →
      R (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) ∧ R (stA (L.curW s2)) ∧
        L.mem s2 (stA (L.curW s2)) = sched.TS_RUNNING) :
    syscall.finish (PathObl.guard st R W) ar s a = syscall.finish st ar s a := by
  have ct : layout.node.CUR_TIME.val < 4288 := by simp [layout.node.CUR_TIME]
  have ct8 : layout.node.CUR_TIME.val % 8 = 0 := by simp [layout.node.CUR_TIME]
  have tm : layout.node.TIMER_MIN.val < 4288 := by simp [layout.node.TIMER_MIN]
  have tm8 : layout.node.TIMER_MIN.val % 8 = 0 := by simp [layout.node.TIMER_MIN]
  have rh : layout.node.RELEASE_HEAD.val < 4288 := by simp [layout.node.RELEASE_HEAD]
  have rh8 : layout.node.RELEASE_HEAD.val % 8 = 0 := by simp [layout.node.RELEASE_HEAD]
  have sa : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
  have sa8 : layout.node.SCHED_ACTION.val % 8 = 0 := by simp [layout.node.SCHED_ACTION]
  have hac : sched.action st s = ok sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s), ha]
  have es : sched.schedule st ar s a = schedRes st ar s a :=
    schedule_res_eq st ar s a (awaken_none ar s a (Or.inl h0) (Or.inl h1)) hac
  have eg : sched.schedule (PathObl.guard st R W) ar s a = schedRes (PathObl.guard st R W) ar s a :=
    schedule_res_eq _ ar s a
      (sched.awaken.guard_none ar s a (hNd _ ct ct8).1 (hNd _ tm tm8).1 (hNd _ rh rh8).1 h0 h1)
      (by rw [sched.action.guard s (hNd _ sa sa8).1]; exact hac)
  unfold syscall.finish
  rw [eg, schedRes.guard ar s a hNd hsw hfr, ← es]
  refine bind_guard_congr rfl fun x1 hs1 => ?_
  obtain ⟨s1, a1⟩ := x1
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [hact s1 a1 hs1]
  refine bind_guard_congr rfl fun x2 hs2 => ?_
  obtain ⟨s2, a2⟩ := x2
  simp only [Aeneas.Std.uncurry_apply_pair]
  obtain ⟨hc, hr, hs⟩ := hvc s1 a1 s2 a2 hs1 hs2
  rw [sched.cur_thread.guard s2 hc, cur_thread_ok]
  simp only [bind_ok, bind_tc_ok]
  have hv := vcpu.check.guard_running (W := W) ar s2 a2 _ hr hs
  rw [hv.1, hv.2]

end

end Fl4Proofs.P2.PathObl.LT
