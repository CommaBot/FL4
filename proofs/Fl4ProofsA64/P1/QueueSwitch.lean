-- AArch64 port of Fl4Proofs.P1.QueueSwitch (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: `switch_to_thread` / `choose_thread` (sched.rs; seL4 `switchToThread`,
`chooseThread`) keep `SchedQueuesInv`: `set_vm_root` only touches the
architecture state, `dequeue` takes the chosen thread out of its queue, and
`set_cur_thread` writes a node word below the queues.
-/
import Fl4ProofsA64.P1.QueueChoose
import Fl4ProofsA64.P0.Auto
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {A : Type _} {ar : machine.Arch A}

include L in
theorem set_kernel_vm_root_same (hA : P0.ArchTotal ar) (s : S) (a : A) :
    vspace.set_kernel_vm_root st ar s a ⦃ s' _ => s' = s ⦄ := by
  have := L.total
  unfold vspace.set_kernel_vm_root
  step*

include L in
/-- a64: `set_stage2_root` (AArch64: a bound VCPU's guest Stage-2 root) reads the VSpace slot and makes Arch
calls only. -/
theorem set_stage2_root_same (hA : P0.ArchTotal ar) (s : S) (a : A) (t : obj.Tcb) :
    vspace.set_stage2_root st ar s a t ⦃ s' _ => s' = s ⦄ := by
  have := L.total
  unfold vspace.set_stage2_root
  repeat' (first | (step with P0.ArchTotal.set_stage2_vspace_spec hA) | step | split)
  all_goals (try subst_vars) <;> first | rfl | simp_all

include L in
/-- a64: `high_root_of` (the TTBR1 high VSpace of a thread) only reads: it is total, and it has no store
output. -/
theorem high_root_of_ro (s : S) (t : obj.Tcb) : vspace.high_root_of st s t ⦃ _ => True ⦄ :=
  P0.vspace.high_root_of.p0 st s t L.total

/-- a64: a bind whose continuation returns the store `s` with any Arch state keeps the store `s`. -/
theorem bind_pair_same {B : Type _} {m : Result B} (hm : m ⦃ _ => True ⦄) (s : S) :
    (do let t1 ← m; ok (s, t1)) ⦃ (s' : S) (_ : B) => s' = s ⦄ :=
  WP.spec_bind hm fun _ _ => (WP.spec_ok _).2 rfl

/-- a64: sequencing two store-preserving steps: if `m` returns the store `s`, and `f` keeps `s` on every
Arch state, the bind keeps `s`. -/
theorem bind_same {m : Result (S × A)} {f : S × A → Result (S × A)} {s : S}
    (hm : m ⦃ s' _ => s' = s ⦄) (hf : ∀ a, f (s, a) ⦃ s' _ => s' = s ⦄) :
    (m >>= f) ⦃ s' _ => s' = s ⦄ := by
  refine WP.spec_bind hm ?_
  rintro ⟨s', a'⟩ e
  simp only [WP.uncurry'_pair] at e
  subst e
  exact hf a'

include L in
/-- a64: the Pml4 arm of AArch64's `set_vm_root` after the ASID check: it reads the thread state and the high
VSpace, and makes two Arch calls. -/
theorem set_vm_root_pml4_same (hA : P0.ArchTotal ar) (s : S) (a : A) (t : obj.Tcb) (ptr asid : U64) :
    (do
      let i1 ← obj.Tcb.state st t s
      let high ←
        if i1 = sched.TS_RUNNING_VM
        then ok 0#u64
        else vspace.high_root_of st s t
      let t1 ←
        if high = 0#u64
        then
          do
          let a2 ← ar.set_high_vspace a 0#u64 asid
          ar.set_vspace a2 ptr asid
        else
          do
          let a2 ← ar.set_vspace a ptr asid
          ar.set_high_vspace a2 high asid
      ok (s, t1)) ⦃ s' _ => s' = s ⦄ := by
  refine WP.spec_bind (P0.obj.Tcb.state.p0 st t s L.total) fun i1 _ => ?_
  refine WP.spec_bind (show (if i1 = sched.TS_RUNNING_VM then ok 0#u64 else vspace.high_root_of st s t)
      ⦃ _ => True ⦄ from ?_) fun high _ => ?_
  · by_cases hi : i1 = sched.TS_RUNNING_VM
    · rw [if_pos hi]; exact (WP.spec_ok _).2 trivial
    · rw [if_neg hi]; exact high_root_of_ro s t
  · refine bind_pair_same ?_ s
    by_cases hh : high = 0#u64
    · rw [if_pos hh]
      exact WP.spec_bind (hA.set_high_vspace_spec _ _ _) fun _ _ => hA.set_vspace_spec _ _ _
    · rw [if_neg hh]
      exact WP.spec_bind (hA.set_vspace_spec _ _ _) fun _ _ => hA.set_high_vspace_spec _ _ _

set_option maxHeartbeats 4000000 in
include L in
/-- `set_vm_root` leaves the store alone. a64: AArch64's body (the Stage-2 root of a thread with a bound VCPU,
the TTBR1 high VSpace) is taken arm by arm: the VCPU arm, the VSpace-cap match (the Pml4 arm by
`set_vm_root_pml4_same`), then the `TS_RUNNING_VM` guest Stage-2 tail; each reads and calls the Arch only. -/
theorem set_vm_root_same (hA : P0.ArchTotal ar) (s : S) (a : A) (t : obj.Tcb) :
    vspace.set_vm_root st ar s a t ⦃ s' _ => s' = s ⦄ := by
  have := L.total
  unfold vspace.set_vm_root
  refine WP.spec_bind (P0.vcpu.bound.p0 st s t this) fun i _ => ?_
  by_cases hi : (i != 0#u64) = true
  · rw [if_pos hi]
    exact bind_same (set_kernel_vm_root_same hA s a) fun a1 => set_stage2_root_same hA s a1 t
  · rw [if_neg hi]
    refine WP.spec_bind (P0.obj.Tcb.slot.p0 t layout.tcb.SLOT_VTABLE) fun s1 _ => ?_
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st s1 s this) fun c _ => ?_
    refine bind_same ?_ ?_
    · repeat' (first
        | exact set_kernel_vm_root_same hA s a
        | exact set_vm_root_pml4_same hA s a t _ _
        | step
        | split)
    · intro a1
      try dsimp only
      repeat' (first
        | exact set_stage2_root_same hA s a1 _
        | exact (WP.spec_ok _).2 rfl
        | step
        | split)

theorem sched.idle_thread.spec' (s : S) :
    sched.idle_thread st s ⦃ v => v = L.mem s (L.nodeAt s (L.cpu s) layout.node.IDLE_THREAD) ⦄ := by
  unfold sched.idle_thread
  rw [L.cur_cpu_eq]; simp only [bind_ok]
  exact WP.spec_bind (obj.node_get.spec s _ _) fun _ h => by simp [h]

theorem curth_val : layout.node.CUR_THREAD.val = 0 := by simp [layout.node.CUR_THREAD]

@[step] theorem sched.set_cur_thread.spec (s : S) (t : obj.Tcb) :
    sched.set_cur_thread st s t ⦃ s' => s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) t ⦄ := by
  unfold sched.set_cur_thread
  rw [L.cur_cpu_eq]; simp only [bind_ok]
  exact obj.node_set.spec s _ _ t

/-- `set_cur_thread` keeps the invariant. -/
theorem inv_set_cur {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) t) Q R := by
  have hN' := h.nodes _ h.cur
  have e : L.actionW (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) t) = L.actionW s := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    rw [rd_node_wr_node hN' (by rw [curth_val]; omega) (by rw [act_val]; omega) (by rw [curth_val])
      (by rw [act_val]), if_neg (by rw [curth_val, act_val]; omega)]
  have o8 := nodeword_other (v := t) h h.cur h.cur (o := layout.node.CUR_THREAD) (o' := layout.node.IDLE_THREAD)
    (by rw [curth0]; omega) (by rw [curth0]) (by rw [idle8]; omega) (by rw [idle8])
    (fun _ => by rw [curth0, idle8]; omega)
  exact inv_wr_node_low (o := layout.node.CUR_THREAD) (v := t) h h.cur (by rw [curth_val]; omega)
    (by rw [curth_val]; omega) (by rw [curth_val])
    (by rw [e]; exact h.action) (by rw [e]; exact h.actOK)
    (by rw [L.mem_wr_same (nodeAt_aligned hN' (by rw [curth0]; omega) (by rw [curth0]))]; exact ht)
    (by rw [o8]; exact h.idleT)

/-- seL4 `switchToThread` keeps the invariant: the thread leaves its ready
queue and becomes current. -/
theorem sched.switch_to_thread.inv {Cs : Set U64} (hA : P0.ArchTotal ar) (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T) :
    sched.switch_to_thread st ar s a t ⦃ s' _ => (∃ Q', SchedQueuesInv st T Cs Ω H s' Q' R) ∧
      L.mem s' (L.nodeAt s' (L.cpu s') layout.node.CUR_THREAD) = t ⦄ := by
  unfold sched.switch_to_thread
  refine WP.spec_bind (set_vm_root_same hA s a t) ?_
  rintro ⟨s1, a1⟩ e
  simp only [WP.uncurry'_pair] at e
  subst e
  refine WP.spec_bind (sched.dequeue.inv s1 t Q R h ht) ?_
  intro s2 h2
  step with sched.set_cur_thread.spec as ⟨s3, s3_post⟩
  subst s3_post
  refine ⟨⟨_, inv_set_cur h2 ht⟩, ?_⟩
  simp only [LawfulStore.cpu_wr, nodeAt_wr]
  exact L.mem_wr_same (nodeAt_aligned (h2.nodes _ h2.cur) (by rw [curth_val]; omega) (by rw [curth_val]))

/-- seL4 `chooseThread` keeps the invariant: it switches to the head of the
highest non-empty ready queue of the current core (`choose_thread_pick`),
or to the idle thread. -/
theorem sched.choose_thread.inv {Cs : Set U64} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) :
    sched.choose_thread st ar s a ⦃ s' _ => ∃ Q', SchedQueuesInv st T Cs Ω H s' Q' R ⦄ := by
  unfold sched.choose_thread
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  rw [ite_cond_eq_false _ _ (by simp)]
  simp only [bind_ok]
  step with LawfulStore.cur_cpu_spec as ⟨cpu, cpu_post⟩
  subst cpu_post
  unfold sched.bitmap_dom
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  rw [ite_cond_eq_false _ _ (by simp)]
  simp only [bind_ok]
  step with l1_off_zero as ⟨i1, i1_post⟩
  subst i1_post
  step with obj.node_get.spec as ⟨i2, i2_post⟩
  split
  · have hne : L.l1W s (L.cpu s) ≠ 0#u64 := by
      rw [show L.l1W s (L.cpu s) = i2 from i2_post.symm]; simpa using ‹(i2 != 0#u64) = true›
    have hpick := choose_thread_pick s Q R h hne
    -- run the pick, then switch
    refine WP.spec_bind (sched.highest_prio.spec s 0#u64 _ (h.nodes _ h.cur) (h.ready _ h.cur).2 hne) ?_
    rintro p ⟨hp, hpne, -⟩
    step with sched.rq_head_off.spec as ⟨off, off_post, off_post1⟩
    step with sched.q_get.spec as ⟨q, q_post⟩
    have hq : q = L.rqQ s (L.cpu s) p := by rw [q_post, off_post1, off_post]; rfl
    have hrel := (h.ready _ h.cur).1.rel p hp
    have htT : q.head ∈ T := by
      rw [hq, hrel.head]; exact hrel.mem _ (headD_mem hpne _)
    exact WP.spec_mono (sched.switch_to_thread.inv hA s a q.head Q R h htT) fun r hr => by
      obtain ⟨s', a'⟩ := r; exact hr.1
  · unfold sched.switch_to_idle_thread
    step with sched.idle_thread.spec' as ⟨idle, idle_post⟩
    refine WP.spec_bind (set_kernel_vm_root_same (st := st) hA s a) ?_
    rintro ⟨s1, a1⟩ e
    simp only [WP.uncurry'_pair] at e
    subst e
    step with sched.set_cur_thread.spec as ⟨s2, s2_post⟩
    subst s2_post
    exact ⟨Q, inv_set_cur h (idle_post ▸ h.idleT)⟩

end

end Fl4ProofsA64.P1
