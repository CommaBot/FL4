/-
P1: `switch_to_thread` / `choose_thread` (sched.rs; seL4 `switchToThread`,
`chooseThread`) keep `SchedQueuesInv`: `set_vm_root` only touches the
architecture state, `dequeue` takes the chosen thread out of its queue, and
`set_cur_thread` writes a node word below the queues.
-/
import Fl4Proofs.P1.QueueChoose
import Fl4Proofs.P0.Auto
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}
variable {A : Type _} {ar : machine.Arch A}

include L in
theorem set_kernel_vm_root_same (hA : P0.ArchTotal ar) (s : S) (a : A) :
    vspace.set_kernel_vm_root st ar s a ⦃ s' _ => s' = s ⦄ := by
  have := L.total
  unfold vspace.set_kernel_vm_root
  step*

include L in
/-- `set_vm_root` leaves the store alone. -/
theorem set_vm_root_same (hA : P0.ArchTotal ar) (s : S) (a : A) (t : obj.Tcb) :
    vspace.set_vm_root st ar s a t ⦃ s' _ => s' = s ⦄ := by
  have := L.total
  unfold vspace.set_vm_root vspace.set_kernel_vm_root
  step*
  all_goals done

theorem sched.idle_thread.spec' (s : S) : sched.idle_thread st s ⦃ _ => True ⦄ := by
  unfold sched.idle_thread
  rw [L.cur_cpu_eq]; simp only [bind_ok]
  exact WP.spec_bind (obj.node_get.spec s _ _) fun _ _ => by simp

theorem curth_val : layout.node.CUR_THREAD.val = 0 := by simp [layout.node.CUR_THREAD]

@[step] theorem sched.set_cur_thread.spec (s : S) (t : obj.Tcb) :
    sched.set_cur_thread st s t ⦃ s' => s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) t ⦄ := by
  unfold sched.set_cur_thread
  rw [L.cur_cpu_eq]; simp only [bind_ok]
  exact obj.node_set.spec s _ _ t

/-- `set_cur_thread` keeps the invariant. -/
theorem inv_set_cur {Cs : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t : U64}
    (h : SchedQueuesInv st T Cs s Q R) :
    SchedQueuesInv st T Cs (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) t) Q R := by
  have hN' := h.nodes _ h.cur
  refine inv_wr_node_low (o := layout.node.CUR_THREAD) (v := t) h h.cur (by rw [curth_val]; omega) (by rw [curth_val]) ?_
  have e : L.actionW (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) t) = L.actionW s := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    rw [rd_node_wr_node hN' (by rw [curth_val]; omega) (by rw [act_val]; omega) (by rw [curth_val])
      (by rw [act_val]), if_neg (by rw [curth_val, act_val]; omega)]
  rw [e]; exact h.action

/-- seL4 `switchToThread` keeps the invariant: the thread leaves its ready
queue and becomes current. -/
theorem sched.switch_to_thread.inv {Cs : Set U64} (hA : P0.ArchTotal ar) (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs s Q R) (ht : t ∈ T) :
    sched.switch_to_thread st ar s a t ⦃ s' _ => (∃ Q', SchedQueuesInv st T Cs s' Q' R) ∧
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
  refine ⟨⟨_, inv_set_cur h2⟩, ?_⟩
  simp only [LawfulStore.cpu_wr, nodeAt_wr]
  exact L.mem_wr_same (nodeAt_aligned (h2.nodes _ h2.cur) (by rw [curth_val]; omega) (by rw [curth_val]))

/-- seL4 `chooseThread` keeps the invariant: it switches to the head of the
highest non-empty ready queue of the current core (`choose_thread_pick`),
or to the idle thread. -/
theorem sched.choose_thread.inv {Cs : Set U64} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs s Q R) :
    sched.choose_thread st ar s a ⦃ s' _ => ∃ Q', SchedQueuesInv st T Cs s' Q' R ⦄ := by
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
    step with sched.idle_thread.spec' as ⟨idle, _⟩
    refine WP.spec_bind (set_kernel_vm_root_same (st := st) hA s a) ?_
    rintro ⟨s1, a1⟩ e
    simp only [WP.uncurry'_pair] at e
    subst e
    step with sched.set_cur_thread.spec as ⟨s2, s2_post⟩
    subst s2_post
    exact ⟨Q, inv_set_cur h⟩

end

end Fl4Proofs.P1
