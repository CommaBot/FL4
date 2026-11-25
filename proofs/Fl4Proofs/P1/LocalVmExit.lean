/-
# The x86 VM-exit entries beside the serial gate (FL4 #104, line lvm)

`localvm.handle_vcpu_exit_local` (fl4-sync's `local_vm_exit` for an exit with no
host interrupt, `irq = NO_IRQ`) and `localvm.handle_vm_timer_irq_local` (its
kernel-timer case, `local_vm_timer_irq`). If either declines, fl4-kernel's `exit`
takes the gate and runs `syscall.handle_vcpu_exit s a irq stalled`, with
`stalled = false` unless a remote stall came. As `P1/LocalTimer.lean` does for
`handle_timer_irq_local`:

* `vcpu_exit_local_same`: an accepted `handle_vcpu_exit_local` ends where
  `handle_vcpu_exit … NO_IRQ false` ends. After read-only checks it runs the
  general entry's `update_timestamp`, `vcpu.check` of the current thread,
  `check_budget` and `finish` (`localvm.finish` is `syscall.finish`'s body,
  `localvm_finish_eq`), in that order. The general entry reads the current thread
  after its `update_timestamp`. The local entry read it before. They agree on a placed
  node (`lvm_cur_thread_ut`: `update_timestamp` writes only `CUR_TIME` and
  `CONSUMED`).
* `vm_timer_local_same`: the same for `handle_vm_timer_irq_local` and
  `handle_vcpu_exit … irq false`, with `handle_interrupt` between `check_budget`
  and `finish`: an accepted `irq` is at most `irq::MAX = 127`, so it is not
  `NO_IRQ` (`lvm_irq_ne_no_irq`).
* `vcpu_exit_local_decline` / `vm_timer_local_decline`: a declined run returned
  the entry state or one `update_timestamp`. `vcpu_exit_pre_same`: from that
  update the general entry (`stalled = false`) runs as from the entry state with
  the Arch value the update left (`utW_twice`).
* `vcpu_exit_local_triple` / `vm_timer_local_triple`: every postcondition of the
  general entry holds on the local entry's `true` results.

Hypotheses: `NodePlaced` at the entry state (a P1 fact of `EntryInv`), Arch
totality and, for `pre_same`, `StoreExt`, as `LocalTimer` / `FastVmDecline` use
them. No named premises.

Scope note (`handoff/lvm.md`): these results move every P1 property of the
serial VM exit to the local one. P1 has no invariant triple for
`handle_vcpu_exit` itself yet. VT-x entries are outside the P1 top
(`P3Place.vmchk` [P], P3's `NativeScope`).
-/
import Fl4Proofs.P1.LocalTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- `update_timestamp`'s two writes miss the current-thread word. -/
theorem lvm_curW_utW {T : Set U64} {s : S} (hN : NodePlaced st T s (L.cpu s)) (n : U64) :
    L.curW (utW (L := L) s n) = L.curW s := by
  have vC := nodeAt_val hN (off := layout.node.CUR_THREAD) (by simp [layout.node.CUR_THREAD])
  have aC : Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
    nodeAt_aligned hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have vb := nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
  have vn := nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
  unfold LawfulStore.curW
  rw [utW_cpu, nodeAt_of_ksb (utW_ksb s n)]
  refine utW_mem hN n aC ?_ ?_
  · intro e
    have e' := congrArg UScalar.val e
    unfold ctA at e'
    rw [vC, vb] at e'
    simp [layout.node.CUR_THREAD, layout.node.CUR_TIME] at e'
  · intro e
    have e' := congrArg UScalar.val e
    unfold cnA at e'
    rw [vC, vn] at e'
    simp [layout.node.CUR_THREAD, layout.node.CONSUMED] at e'

/-- **`update_timestamp` keeps the current thread** (placed node). -/
theorem lvm_cur_thread_ut (hA : P0.ArchTotal ar) {T : Set U64} {s : S} {a : A} {r : S × A}
    (hN : NodePlaced st T s (L.cpu s)) (h : sched.update_timestamp st ar s a = ok r) :
    sched.cur_thread st r.1 = sched.cur_thread st s := by
  obtain ⟨n1, -, e⟩ := ut_now ar hA hN h
  rw [e, cur_thread_ok, cur_thread_ok, lvm_curW_utW hN]

omit L in
/-- `localvm::finish` is `syscall::finish`. -/
theorem localvm_finish_eq (s : S) (a : A) : localvm.finish st ar s a = syscall.finish st ar s a := by
  unfold localvm.finish syscall.finish
  rfl

/-- An IRQ number at most `irq::MAX` is not `NO_IRQ`. -/
theorem lvm_irq_ne_no_irq {irq i : U64} (hi : layout.irq.MAX = ok i) (h : ¬ irq > i) :
    (irq != syscall.NO_IRQ) = true := by
  have h127 : i = 127#u64 := by
    have hs := layout.irq.MAX.spec
    rw [hi, WP.spec_ok] at hs
    exact hs
  subst h127
  rw [bne_iff_ne]
  intro e
  have e' := congrArg UScalar.val e
  have hv : syscall.NO_IRQ.val = 2 ^ 64 - 1 := by
    unfold syscall.NO_IRQ
    rfl
  simp at h
  omega

/-! ## `handle_vcpu_exit_local` -/

set_option hygiene false in
/-- The tail of `handle_vcpu_exit_local` after its `PENDING` / notification
split (both arms are the same text), on an accepted run. -/
local macro "lvm_exit_tail" : tactic => `(tactic| (
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨s1, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, -, h⟩ := bind_eq_ok h
  obtain ⟨i4, -, h⟩ := bind_eq_ok h
  obtain ⟨b4, -, h⟩ := bind_eq_ok h
  cases b4
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b5, -, h⟩ := bind_eq_ok h
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
  have ect : sched.cur_thread st s1 = ok ct := by
    rw [show s1 = (s1, a1).1 from rfl, lvm_cur_thread_ut ar hA hN eu]; exact et
  unfold syscall.handle_vcpu_exit
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [eu]; simp only [bind_ok, uncurry_apply_pair]
  rw [ect]; simp only [bind_ok]
  rw [evc]; simp only [bind_ok, uncurry_apply_pair]
  rw [ecb]; simp only [bind_ok, uncurry_apply_pair]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok, uncurry_apply_pair]
  rw [← localvm_finish_eq]
  exact efin))

set_option maxHeartbeats 4000000 in
/-- **`vcpu_exit_local_same`: a VM exit without a host interrupt beside the
serial gate, where it ran, is `handle_vcpu_exit … NO_IRQ false`.** -/
theorem vcpu_exit_local_same (hA : P0.ArchTotal ar) {T : Set U64} {s s' : S} {a a' : A} {v n : U64}
    (hN : NodePlaced st T s (L.cpu s))
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a')) :
    syscall.handle_vcpu_exit st ar s a syscall.NO_IRQ false = ok (s', a') := by
  unfold localvm.handle_vcpu_exit_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨ct, et, h⟩ := bind_eq_ok h
  obtain ⟨cpu, -, h⟩ := bind_eq_ok h
  obtain ⟨csc, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i != sched.TS_RUNNING_VM) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  by_cases c2 : v = 0#u64
  · rw [if_pos c2] at h; simp at h
  rw [if_neg c2] at h
  obtain ⟨i1, -, h⟩ := bind_eq_ok h
  by_cases c3 : (i1 != v) = true
  · rw [if_pos c3] at h; simp at h
  rw [if_neg c3] at h
  obtain ⟨i2, -, h⟩ := bind_eq_ok h
  by_cases c4 : (i2 != n) = true
  · rw [if_pos c4] at h; simp at h
  rw [if_neg c4] at h
  obtain ⟨i3, -, h⟩ := bind_eq_ok h
  by_cases c5 : i3 = 0#u64
  · rw [if_pos c5] at h
    obtain ⟨b, -, h⟩ := bind_eq_ok h
    cases b
    · simp at h
    simp only [↓reduceIte] at h
    lvm_exit_tail
  · rw [if_neg c5] at h
    lvm_exit_tail

set_option hygiene false in
/-- The tail of `handle_vcpu_exit_local` on a declined run: the guards before
its `update_timestamp` return the entry state, the rest the update's. -/
local macro "lvm_exit_dtail" : tactic => `(tactic| (
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  right
  obtain ⟨⟨s1, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨e1, e2⟩ : s' = s1 ∧ a' = a1 := by
    have h' := spec_of_eq_fd h
    clear h
    revert h'
    decl_walk
    all_goals decl_leaf
  subst e1 e2
  exact eu))

omit L in
set_option maxHeartbeats 4000000 in
/-- **A declined VM exit**: the entry state, or one `update_timestamp`
(fl4-kernel then runs `handle_vcpu_exit` from it). -/
theorem vcpu_exit_local_decline {s s' : S} {a a' : A} {v n : U64}
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (false, s', a')) :
    (s' = s ∧ a' = a) ∨ sched.update_timestamp st ar s a = ok (s', a') := by
  unfold localvm.handle_vcpu_exit_local at h
  try simp only [lift, bind_ok] at h
  have fin : ∀ {x y : S} {u w : A}, (ok (false, x, u) : Result (Bool × S × A)) = ok (false, y, w) →
      y = x ∧ w = u := by
    intro x y u w e
    have e := ok_inj_ff e
    simp only [Prod.mk.injEq, true_and] at e
    exact ⟨e.1.symm, e.2.symm⟩
  obtain ⟨ct, -, h⟩ := bind_eq_ok h
  obtain ⟨cpu, -, h⟩ := bind_eq_ok h
  obtain ⟨csc, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i != sched.TS_RUNNING_VM) = true
  · rw [if_pos c1] at h; exact Or.inl (fin h)
  rw [if_neg c1] at h
  by_cases c2 : v = 0#u64
  · rw [if_pos c2] at h; exact Or.inl (fin h)
  rw [if_neg c2] at h
  obtain ⟨i1, -, h⟩ := bind_eq_ok h
  by_cases c3 : (i1 != v) = true
  · rw [if_pos c3] at h; exact Or.inl (fin h)
  rw [if_neg c3] at h
  obtain ⟨i2, -, h⟩ := bind_eq_ok h
  by_cases c4 : (i2 != n) = true
  · rw [if_pos c4] at h; exact Or.inl (fin h)
  rw [if_neg c4] at h
  obtain ⟨i3, -, h⟩ := bind_eq_ok h
  by_cases c5 : i3 = 0#u64
  · rw [if_pos c5] at h
    obtain ⟨b, -, h⟩ := bind_eq_ok h
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
    simp only [↓reduceIte] at h
    lvm_exit_dtail
  · rw [if_neg c5] at h
    lvm_exit_dtail

/-- **After a timestamp update the general VM-exit entry (not stalled) runs as
from the entry state** with the Arch value the update left. -/
theorem vcpu_exit_pre_same (hX : StoreExt st) (hA : P0.ArchTotal ar) {T : Set U64} {s : S}
    (hN : NodePlaced st T s (L.cpu s)) {a : A} {r : S × A} (h : sched.update_timestamp st ar s a = ok r)
    (irq : U64) :
    syscall.handle_vcpu_exit st ar r.1 r.2 irq false = syscall.handle_vcpu_exit st ar s r.2 irq false := by
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN h
  rw [er]
  obtain ⟨⟨n2, b2⟩, hn, -⟩ := spec_ex_fd (hA.now r.2)
  unfold syscall.handle_vcpu_exit
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [update_timestamp_ok ar (utW_placed hN n1) hn, update_timestamp_ok ar hN hn, utW_twice hX hN]

/-- **The VM-exit local entry where it ran: the general entry's
postconditions** (on the `true` results). -/
theorem vcpu_exit_local_triple (hA : P0.ArchTotal ar) {T : Set U64} {s : S} {a : A} {v n : U64}
    (hN : NodePlaced st T s (L.cpu s)) {P : S × A → Prop}
    (hG : syscall.handle_vcpu_exit st ar s a syscall.NO_IRQ false ⦃ P ⦄) :
    localvm.handle_vcpu_exit_local st ar s a v n ⦃ r => r.1 = true → P (r.2.1, r.2.2) ⦄ := by
  obtain ⟨⟨b, s', a'⟩, e, -⟩ := spec_ex_fd (P0.localvm.handle_vcpu_exit_local.p0 st ar s a v n L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := vcpu_exit_local_same ar hA hN e
  rw [hs, WP.spec_ok] at hG
  exact hG

/-! ## `handle_vm_timer_irq_local` (x86: the kernel timer's VM exit) -/

set_option maxHeartbeats 4000000 in
/-- **`vm_timer_local_same`: the kernel timer's VM exit beside the serial gate,
where it ran, is `handle_vcpu_exit … irq false`.** -/
theorem vm_timer_local_same (hA : P0.ArchTotal ar) {T : Set U64} {s s' : S} {a a' : A} {irq n : U64}
    {p : localtimer.TimerIrqPlan} (hN : NodePlaced st T s (L.cpu s))
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (true, s', a')) :
    syscall.handle_vcpu_exit st ar s a irq false = ok (s', a') := by
  unfold localvm.handle_vm_timer_irq_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨cpu, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  by_cases c1 : irq > i
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  have hirq := lvm_irq_ne_no_irq ei c1
  obtain ⟨i1, -, h⟩ := bind_eq_ok h
  by_cases c2 : (i1 != interrupt.IRQ_TIMER) = true
  · rw [if_pos c2] at h; simp at h
  rw [if_neg c2] at h
  obtain ⟨tip, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨ct, et, h⟩ := bind_eq_ok h
  obtain ⟨csc, -, h⟩ := bind_eq_ok h
  obtain ⟨i2, -, h⟩ := bind_eq_ok h
  by_cases c3 : (i2 != sched.TS_RUNNING_VM) = true
  · rw [if_pos c3] at h; simp at h
  rw [if_neg c3] at h
  obtain ⟨i3, -, h⟩ := bind_eq_ok h
  by_cases c4 : (i3 != n) = true
  · rw [if_pos c4] at h; simp at h
  rw [if_neg c4] at h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b4, -, h⟩ := bind_eq_ok h
  cases b4
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨s1, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, -, h⟩ := bind_eq_ok h
  obtain ⟨b5, -, h⟩ := bind_eq_ok h
  cases b5
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i4, -, h⟩ := bind_eq_ok h
  obtain ⟨b6, -, h⟩ := bind_eq_ok h
  obtain ⟨due, -, h⟩ := bind_eq_ok h
  obtain ⟨ok1, -, h⟩ := bind_eq_ok h
  cases ok1
  · simp at h
  simp only [↓reduceIte] at h
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
  have ect : sched.cur_thread st s1 = ok ct := by
    rw [show s1 = (s1, a1).1 from rfl, lvm_cur_thread_ut ar hA hN eu]; exact et
  unfold syscall.handle_vcpu_exit
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [eu]; simp only [bind_ok, uncurry_apply_pair]
  rw [ect]; simp only [bind_ok]
  rw [evc]; simp only [bind_ok, uncurry_apply_pair]
  rw [ecb]; simp only [bind_ok, uncurry_apply_pair]
  rw [if_pos hirq, ehi]; simp only [bind_ok, uncurry_apply_pair]
  rw [← localvm_finish_eq]
  exact efin

omit L in
set_option maxHeartbeats 4000000 in
/-- **A declined kernel-timer VM exit**: the entry state, or one
`update_timestamp` (fl4-kernel then runs `handle_vcpu_exit` from it). -/
theorem vm_timer_local_decline {s s' : S} {a a' : A} {irq n : U64} {p : localtimer.TimerIrqPlan}
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (false, s', a')) :
    (s' = s ∧ a' = a) ∨ sched.update_timestamp st ar s a = ok (s', a') := by
  unfold localvm.handle_vm_timer_irq_local at h
  try simp only [lift, bind_ok] at h
  have fin : ∀ {x y : S} {u w : A}, (ok (false, x, u) : Result (Bool × S × A)) = ok (false, y, w) →
      y = x ∧ w = u := by
    intro x y u w e
    have e := ok_inj_ff e
    simp only [Prod.mk.injEq, true_and] at e
    exact ⟨e.1.symm, e.2.symm⟩
  obtain ⟨cpu, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : irq > i
  · rw [if_pos c1] at h; exact Or.inl (fin h)
  rw [if_neg c1] at h
  obtain ⟨i1, -, h⟩ := bind_eq_ok h
  by_cases c2 : (i1 != interrupt.IRQ_TIMER) = true
  · rw [if_pos c2] at h; exact Or.inl (fin h)
  rw [if_neg c2] at h
  obtain ⟨tip, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨ct, -, h⟩ := bind_eq_ok h
  obtain ⟨csc, -, h⟩ := bind_eq_ok h
  obtain ⟨i2, -, h⟩ := bind_eq_ok h
  by_cases c3 : (i2 != sched.TS_RUNNING_VM) = true
  · rw [if_pos c3] at h; exact Or.inl (fin h)
  rw [if_neg c3] at h
  obtain ⟨i3, -, h⟩ := bind_eq_ok h
  by_cases c4 : (i3 != n) = true
  · rw [if_pos c4] at h; exact Or.inl (fin h)
  rw [if_neg c4] at h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨b4, -, h⟩ := bind_eq_ok h
  cases b4
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  right
  obtain ⟨⟨s1, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨e1, e2⟩ : s' = s1 ∧ a' = a1 := by
    have h' := spec_of_eq_fd h
    clear h
    revert h'
    decl_walk
    all_goals decl_leaf
  subst e1 e2
  exact eu

/-- **The kernel-timer VM-exit local entry where it ran: the general entry's
postconditions** (on the `true` results). -/
theorem vm_timer_local_triple (hA : P0.ArchTotal ar) {T : Set U64} {s : S} {a : A} {irq n : U64}
    {p : localtimer.TimerIrqPlan} (hN : NodePlaced st T s (L.cpu s)) {P : S × A → Prop}
    (hG : syscall.handle_vcpu_exit st ar s a irq false ⦃ P ⦄) :
    localvm.handle_vm_timer_irq_local st ar s a irq p n ⦃ r => r.1 = true → P (r.2.1, r.2.2) ⦄ := by
  obtain ⟨⟨b, s', a'⟩, e, -⟩ :=
    spec_ex_fd (P0.localvm.handle_vm_timer_irq_local.p0 st ar s a irq p n L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := vm_timer_local_same ar hA hN e
  rw [hs, WP.spec_ok] at hG
  exact hG

end

end Fl4Proofs.P1
