/-
P2 (p2j14, KWN step 7): **the executing core's current thread after
`schedule`** (the end facts `AllCores.step`/`step2` ask at the executing core).

* `SchCur s`: the current thread has affinity the executing core, is not
  blocked on an endpoint or notification, and, unless it is the idle thread,
  is in no ready queue (seL4 `ct_not_in_q`).
* `SchPre s`: at the end of `awaken` (`timer::fire` and the release loop):
  if the action is resume, `SchCur`; an action thread has affinity the
  executing core (`possible_switch_to` sets the action only to such a thread,
  sched.rs:369–375); the idle thread has affinity the executing core.
* `switch_to_thread.cur`, `choose_thread.cur`, `schedule_choose_new_thread.cur`,
  `cand_choose.cur`: the thread switched to is `SchCur` (it is dequeued, it was
  runnable, its affinity is the executing core's: a ready-queue head of that
  core, the action thread, or the idle thread).
* **`schedule.cur`**: given `SchPre` at the end of `awaken` (`hE`),
  `schedule` ends in `SchCur` with the action `RESUME` (P1 `schedule.tinv`).
  The frame words used: `SFootN ∅` (`P2/FootN6.lean`) keeps every thread's
  `AFFINITY` and the idle thread; the free writes of the tail
  (`switch_sched_context`, `set_next_interrupt`, `send_pending`) and the
  action write keep the current thread and its fields.

`hE` is a hypothesis of `schedule.cur` (what the entry supplies at the end of
`awaken`), not a premise of this module; no premise.
-/
import Fl4Proofs.P2.FootN6
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Kp : Set U64}
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

/-- The executing core's current thread, at the end of `schedule`. -/
structure SchCur (st : machine.Store S) [L : LawfulStore st] (s : S) : Prop where
  aff : L.mem s (affA (L.curW s)) = L.cpu s
  nb : ¬ Blocked (L.mem s (stA (L.curW s)))
  nq : L.curW s ≠ L.idleW s → (L.mem s (inqA (L.curW s)) &&& sched.Q_QUEUED) = 0#u64

/-- What `schedule` needs at the end of `awaken`. -/
structure SchPre (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) : Prop where
  res : L.actionW s = 0#u64 → SchCur st s
  act : L.actionW s ∈ T → L.mem s (affA (L.actionW s)) = L.cpu s
  idle : L.mem s (affA (L.idleW s)) = L.cpu s

/-! ## Frame facts -/

theorem SFootN.affK {s s' : S} (f : SFootN st Kp T Cs Sg Scs Z H s s') (hT : TcbPlaced T) {y : U64}
    (hy : y ∈ T) : L.mem s' (affA y) = L.mem s (affA y) :=
  f.mem_eq (by rw [affA_eq]; exact field_aligned (hT y hy) (by simp) (by simp))
    (fun hb => hb.2.2 (Or.inr ⟨trivial, Or.inl ⟨y, hy, hT y hy, Or.inr rfl⟩⟩))

theorem SFootN.idleK {s s' : S} (f : SFootN st Kp T Cs Sg Scs Z H s s') (NP : NodePlaced st T s (L.cpu s))
    (hc : L.cpu s ∈ Cs) : L.idleW s' = L.idleW s := by
  unfold LawfulStore.idleW
  rw [nodeAt_of_ksb f.1, f.2.1]
  exact f.mem_eq (nodeAt_aligned NP (by rw [idle8]; omega) (by rw [idle8]))
    (fun hb => hb.2.1 ⟨_, hc, _, Or.inl idle8, rfl⟩)

/-- The idle thread's affinity is the executing core. -/
def IdleAff (st : machine.Store S) [L : LawfulStore st] (s : S) : Prop :=
  L.mem s (affA (L.idleW s)) = L.cpu s

theorem IdleAff.step {s s' : S} (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (f : SFootN st Kp T Cs Sg Scs Z H s s') (hi : IdleAff st s) : IdleAff st s' := by
  unfold IdleAff at hi ⊢
  rw [f.idleK (h.nodes _ h.cur) h.cur, f.affK h.tcbs (y := L.idleW s) h.idleT, f.2.1]; exact hi

theorem node_fld {s : S} {c o y K v : U64} (hN : NodePlaced st T s c) (ho : o.val < 4288) (h8 : o.val % 8 = 0)
    (hT : TcbPlaced T) (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    L.mem (L.wr s (L.nodeAt s c o) v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
  (writesIn_wr (nodeAt_aligned hN ho h8)).mem_eq (field_aligned (hT y hy) hK hK8) fun e =>
    node_ne_field hN ho hy (hT y hy) hK e.symm

theorem free_fld {s s' : S} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' (L.Free s Ω Cs))
    {y K : U64} (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
  refine hw.mem_eq (field_aligned (h.tcbs y hy) hK hK8) ?_
  rintro (hm | ⟨c, hc, o, ho, e⟩)
  · exact out_ne_field (h.omega _ hm) hy (h.tcbs y hy) hK rfl
  · exact node_ne_field (h.nodes c hc) (by simp only [LowFree] at ho; omega) hy (h.tcbs y hy) hK e.symm

/-- Free writes keep `SchCur`. -/
theorem SchCur.free {s s' : S} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' (L.Free s Ω Cs))
    (c : SchCur st s) : SchCur st s' := by
  obtain ⟨-, ec, ei, -⟩ := free_keys h hw
  have hT : L.curW s ∈ T := h.curT
  have ea : L.mem s' (affA (L.curW s)) = L.mem s (affA (L.curW s)) := by
    have := free_fld h hw (y := L.curW s) (K := 3520#u64) hT (by simp) (by simp); rwa [← affA_eq] at this
  have es : L.mem s' (stA (L.curW s)) = L.mem s (stA (L.curW s)) := by
    have := free_fld h hw (y := L.curW s) (K := 3328#u64) hT (by simp) (by simp); rwa [← stA_eq] at this
  have eq : L.mem s' (inqA (L.curW s)) = L.mem s (inqA (L.curW s)) := by
    have := free_fld h hw (y := L.curW s) (K := 3592#u64) hT (by simp) (by simp); rwa [← inqA_eq] at this
  refine ⟨?_, ?_, fun hn => ?_⟩
  · rw [ec, ea, hw.2.1]; exact c.aff
  · rw [ec, es]; exact c.nb
  · rw [ec, eq]; exact c.nq (by rw [← ec, ← ei]; exact hn)

/-- A current thread `t` written into `CUR_THREAD` is `SchCur`. -/
theorem SchCur.setCur {s : S} {t : U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (ha : L.mem s (affA t) = L.cpu s) (hb : ¬ Blocked (L.mem s (stA t)))
    (hq : t ≠ L.idleW s → (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) :
    SchCur st (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) t) := by
  have hN := h.nodes _ h.cur
  have h0 : layout.node.CUR_THREAD.val < 4288 := by rw [curth0]; omega
  have h08 : layout.node.CUR_THREAD.val % 8 = 0 := by rw [curth0]
  have al := nodeAt_aligned hN h0 h08
  have ec : L.curW (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) t) = t := by
    unfold LawfulStore.curW
    rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
    exact L.mem_wr_same al
  have ei : L.idleW (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) t) = L.idleW s := by
    unfold LawfulStore.idleW
    rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
    exact (writesIn_wr al).mem_eq (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8])) fun e =>
      node_ne_node hN hN (by rw [idle8]; omega) h0 (fun _ => by rw [idle8, curth0]; omega) (congrArg UScalar.val e)
  have fl : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) t) (core.num.U64.wrapping_add t K) =
        L.mem s (core.num.U64.wrapping_add t K) := fun K hK hK8 => node_fld hN h0 h08 h.tcbs ht hK hK8
  refine ⟨?_, ?_, fun hn => ?_⟩
  · rw [ec, LawfulStore.cpu_wr]; have := fl 3520#u64 (by simp) (by simp); rw [← affA_eq] at this; rw [this]; exact ha
  · rw [ec]; have := fl 3328#u64 (by simp) (by simp); rw [← stA_eq] at this; rw [this]; exact hb
  · rw [ec] at hn ⊢; rw [ei] at hn
    have := fl 3592#u64 (by simp) (by simp); rw [← inqA_eq] at this; rw [this]; exact hq hn

/-- A write of an executing-core node word other than `CUR_THREAD` and
`IDLE_THREAD` keeps `SchCur`. -/
theorem SchCur.node {s : S} {o v : U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (h0 : o.val ≠ 0) (hi : o.val ≠ 8) (c : SchCur st s) :
    SchCur st (L.wr s (L.nodeAt s (L.cpu s) o) v) := by
  have hN := h.nodes _ h.cur
  have al := nodeAt_aligned hN ho h8
  have ec : L.curW (L.wr s (L.nodeAt s (L.cpu s) o) v) = L.curW s := by
    unfold LawfulStore.curW
    rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
    exact (writesIn_wr al).mem_eq (nodeAt_aligned hN (by rw [curth0]; omega) (by rw [curth0])) fun e =>
      node_ne_node hN hN (by rw [curth0]; omega) ho (fun _ => by rw [curth0]; omega) (congrArg UScalar.val e)
  have ei : L.idleW (L.wr s (L.nodeAt s (L.cpu s) o) v) = L.idleW s := by
    unfold LawfulStore.idleW
    rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
    exact (writesIn_wr al).mem_eq (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8])) fun e =>
      node_ne_node hN hN (by rw [idle8]; omega) ho (fun _ => by rw [idle8]; omega) (congrArg UScalar.val e)
  have hT : L.curW s ∈ T := h.curT
  have fl : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (core.num.U64.wrapping_add (L.curW s) K) =
        L.mem s (core.num.U64.wrapping_add (L.curW s) K) := fun K hK hK8 => node_fld hN ho h8 h.tcbs hT hK hK8
  refine ⟨?_, ?_, fun hn => ?_⟩
  · rw [ec, LawfulStore.cpu_wr]; have := fl 3520#u64 (by simp) (by simp); rw [← affA_eq] at this; rw [this]; exact c.aff
  · rw [ec]; have := fl 3328#u64 (by simp) (by simp); rw [← stA_eq] at this; rw [this]; exact c.nb
  · rw [ec, ei] at hn; rw [ec]
    have := fl 3592#u64 (by simp) (by simp); rw [← inqA_eq] at this; rw [this]; exact c.nq hn

theorem runnable_nb {v : U64} (hr : Runnable v) (hb : Blocked v) : False := by
  obtain ⟨r1, r2, r3, r4, r5⟩ := ts_vals
  rcases hr with e | e | e <;> rcases hb with e' | e' | e' <;> rw [e'] at e <;>
    simp_all [sched.TS_RUNNING_VM]

/-! ## The thread switched to -/

theorem sched.switch_to_thread.cur {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s)
    (ht : t ∈ T) (ha : L.mem s (affA t) = L.cpu s) (hr : Runnable (L.mem s (stA t))) :
    sched.switch_to_thread st ar s a t ⦃ s' _ => SchCur st s' ⦄ := by
  unfold sched.switch_to_thread
  refine WP.spec_bind (set_vm_root_same hA s a t) ?_
  rintro ⟨s1, a1⟩ e
  simp only [WP.uncurry'_pair] at e
  subst e
  have hc := h.aff t ht
  have hp := h.prio t ht
  refine WP.spec_bind (WP.spec_and (sched.dequeue.foot s1 t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur)
    ((h.ready _ hc).1.rel _ hp) (h.queued t ht).1) (WP.spec_and (sched.dequeue.sch s1 t Q R h hB hS ht)
    (sched.dequeue.kwN (Sg := Sg) (Kp := (∅ : Set U64)) (Nd := True) (Scs := (∅ : Set U64)) (Z := fun _ => 0) (Es := EH H)
      s1 t h ht (Set.notMem_empty _)))) ?_
  rintro s2 ⟨⟨-, hinq⟩, ⟨P2, -, -⟩, F2⟩
  obtain ⟨⟨Q2, R2, h2⟩, -, f2⟩ := P2
  refine WP.spec_bind (sched.set_cur_thread.spec s2 t) fun s3 e3 => ?_
  subst e3
  simp only [WP.spec_ok, WP.uncurry'_pair]
  refine SchCur.setCur h2 ht ?_ ?_ fun _ => ?_
  · rw [F2.sN.affK h.tcbs ht, f2.cpu]; exact ha
  · rw [f2.st t ht]; exact fun hb => runnable_nb hr hb
  · rw [hinq]
    split
    · exact andn_qq_qq _
    · rename_i hn; exact not_not.1 hn

theorem sched.choose_thread.cur {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s)
    (hi : IdleAff st s) :
    sched.choose_thread st ar s a ⦃ s' _ => SchCur st s' ⦄ := by
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
    refine WP.spec_bind (sched.highest_prio.spec s 0#u64 _ (h.nodes _ h.cur) (h.ready _ h.cur).2 hne) ?_
    rintro p ⟨hp, hpne, -⟩
    step with sched.rq_head_off.spec as ⟨off, off_post, off_post1⟩
    step with sched.q_get.spec as ⟨q, q_post⟩
    have hq : q = L.rqQ s (L.cpu s) p := by rw [q_post, off_post1, off_post]; rfl
    have hrel := (h.ready _ h.cur).1.rel p hp
    have hmem : q.head ∈ Q (L.cpu s) p := by rw [hq, hrel.head]; exact headD_mem hpne _
    have htT : q.head ∈ T := hrel.mem _ hmem
    exact sched.switch_to_thread.cur hA s a q.head h hB hS htT (h.inQ _ h.cur p hp _ hmem).1
      (h.runQ _ h.cur p hp _ hmem)
  · unfold sched.switch_to_idle_thread
    step with sched.idle_thread.spec' as ⟨idle, idle_post⟩
    refine WP.spec_bind (set_kernel_vm_root_same (st := st) hA s a) ?_
    rintro ⟨s1, a1⟩ e
    simp only [WP.uncurry'_pair] at e
    subst s1
    refine WP.spec_bind (sched.set_cur_thread.spec s idle) fun s2 e2 => ?_
    subst e2
    simp only [WP.spec_ok, WP.uncurry'_pair]
    have hiT : idle ∈ T := by rw [idle_post]; exact h.idleT
    have ie : idle = L.idleW s := idle_post
    refine SchCur.setCur h hiT (by rw [ie]; exact hi) (by rw [ie]; exact fun hb => hB.idleNB (Or.inl hb))
      fun hn => absurd ie hn

theorem sched.schedule_choose_new_thread.cur {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s)
    (hSg : ∀ c ∈ Scs, scReplyA c ∈ Sg ∧ scTcbA c ∈ Sg) (hi : IdleAff st s) :
    sched.schedule_choose_new_thread st ar s a ⦃ s' _ => SchCur st s' ⦄ := by
  unfold sched.schedule_choose_new_thread
  step with sched.domain_time.spec as ⟨i⟩
  refine WP.spec_bind (Pₘ := fun s1 => Post st T Cs Ω H Sg Ac s s1 ∧ IdleAff st s1) ?_ ?_
  · split
    · exact WP.spec_mono (WP.spec_and (sched.next_domain.sch s Q R h hB hS)
        (sched.next_domain.sN (Kp := (∅ : Set U64)) (Scs := Scs) (Z := fun _ => 0) s Q R h hB hS hSg))
        fun s1 hh => ⟨hh.1.1, hi.step h hh.2⟩
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q, R, h⟩, hB, Fr.refl _ _⟩, hi⟩
  rintro s1 ⟨⟨⟨Q1, R1, h1⟩, hB1, f1⟩, hi1⟩
  exact sched.choose_thread.cur hA s1 a h1 hB1 (hS.fr f1) hi1

theorem cand_choose.cur {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (act : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hSg : ∀ c ∈ Scs, scReplyA c ∈ Sg ∧ scTcbA c ∈ Sg) (hi : IdleAff st s)
    (hact : L.actionW s = act) (hT : act ∈ T) (app : Bool) :
    (do
      let s5 ← if app then sched.append st s act else sched.enqueue st s act
      let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
      sched.schedule_choose_new_thread st ar s6 a) ⦃ s' _ => SchCur st s' ⦄ := by
  have hok := h.actOK (hact ▸ hT)
  rw [hact] at hok
  have hr : (L.mem s (inqA act) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hc
    exact hok.2 _ (h.aff act hT) ((h.released act hT).1 hc)
  have hbd : L.mem s (scA act) ≠ 0#u64 := by have := hB.act (hact ▸ hT); rw [hact] at this; exact this
  refine WP.spec_bind (Pₘ := fun s5 => Post st T Cs Ω H Sg Ac s s5 ∧
      FootN st (∅ : Set U64) True T Cs Sg Scs Z (EH H) s s5) ?_ ?_
  · split
    · exact WP.spec_mono (WP.spec_and (sched.append.sch s act Q R h hB hS.sg hT (fun _ => hr) (fun _ => hok.1)
        (fun _ => hbd) (fun _ => by have := hB.actA (hact ▸ hT); rwa [hact] at this))
        (sched.append.kwN (Sg := Sg) (Kp := (∅ : Set U64)) (Nd := True) (Scs := Scs) (Z := Z) (Es := EH H) s act h hT
          (Set.notMem_empty _))) fun s5 h5 => ⟨h5.1.1, h5.2⟩
    · exact WP.spec_mono (WP.spec_and (sched.enqueue.sch s act Q R h hB hS.sg hT (fun _ => hr) (fun _ => hok.1)
        (fun _ => hbd) (fun _ => by have := hB.actA (hact ▸ hT); rwa [hact] at this))
        (sched.enqueue.kwN (Sg := Sg) (Kp := (∅ : Set U64)) (Nd := True) (Scs := Scs) (Z := Z) (Es := EH H) s act h hT
          (Set.notMem_empty _))) fun s5 h5 => ⟨h5.1.1, h5.2⟩
  rintro s5 ⟨⟨⟨Q5, R5, h5⟩, hB5, f5⟩, F5⟩
  rw [choose_val]
  refine WP.spec_bind (WP.spec_and (sched.set_action.sch s5 1#u64 Q5 R5 h5 hB5 (hS.fr f5).sg (Or.inr (Or.inl rfl))
    (fun hT => absurd hT (one_notT h)) (fun hT => absurd hT (one_notT h)) (fun e => by simp at e)
    (fun hT => absurd hT (one_notT h)))
    (sched.set_action.kwN (Sg := Sg) (Kp := (∅ : Set U64)) (Nd := True) (Scs := Scs) (Z := Z) (Es := EH H) s5 1#u64
      h5.nodes h5.cur (small_out h5.tcbs (by simp)))) ?_
  rintro s6 ⟨⟨⟨⟨Q6, R6, h6⟩, hB6, f6⟩, -, -, -⟩, F6⟩
  exact sched.schedule_choose_new_thread.cur hA s6 a Q6 R6 h6 hB6 ((hS.fr f5).fr f6).sg hSg
    ((hi.step h F5.sN).step h5 F6.sN)

/-- `awaken`: P1's invariants at its end. -/
theorem sched.awaken.good {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    sched.awaken st ar s a ⦃ r => Good st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  unfold sched.awaken
  refine WP.spec_bind (timer.fire.tinvF hA IK hNt s a h.tinv hBA) ?_
  rintro ⟨s1, a1⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩, -⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (sched.awaken_loop.sch s1 _ Q1 R1 h1 hB1 hS1.sg) ?_
  rintro s2 ⟨P2, -⟩
  exact (WP.spec_ok _).2 (P2.good hS1 hX1)

/-- **The current thread after `schedule`**: given `SchPre` at the end of
`awaken`, `schedule` ends with a `SchCur` current thread. -/
theorem sched.schedule.cur {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hE : ∀ r : S × A, sched.awaken st ar s a = ok r → SchPre st T r.1) :
    sched.schedule st ar s a ⦃ s' _ => SchCur st s' ⦄ := by
  have hSg : ∀ c ∈ Scs, scReplyA c ∈ Sg ∧ scTcbA c ∈ Sg := scSg h.2.2.1.1
  unfold sched.schedule
  refine WP.spec_bind (spec_eq' (sched.awaken.good hA IK hNt s a h hBA)) ?_
  rintro ⟨s1, a1⟩ ⟨hw1, ⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩⟩
  have hP : SchPre st T s1 := hE _ hw1
  have hi1 : IdleAff st s1 := hP.idle
  try simp only [WP.uncurry'_pair]
  -- `check_domain_time` does nothing with one domain
  unfold sched.check_domain_time sched.is_cur_domain_expired
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have hnd : ¬ ((1#u64) > (1#u64)) := by simp
  simp only [hnd, ↓reduceIte, bind_ok, Bool.false_eq_true]
  step with sched.action.spec as ⟨act, act_post⟩
  -- the action
  refine WP.spec_bind (Pₘ := fun r => Good st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ L.mem r.1 (scA (L.curW r.1)) ≠ 0#u64 ∧
      L.mem r.1 (scA (L.curW r.1)) ∈ Ac ∧ SchCur st r.1) ?_ ?_
  · split
    · rename_i hnr
      step with sched.cur_thread.spec as ⟨ct, ct_post⟩
      have hctT : ct ∈ T := by rw [ct_post]; exact h1.curT
      step with sched.is_schedulable.spec' as ⟨wr, wr_post⟩
      refine WP.spec_bind (Pₘ := fun s4 => Post st T Cs Ω H Sg Ac s1 s4 ∧ L.actionW s4 = L.actionW s1 ∧
          FootN st (∅ : Set U64) True T Cs Sg Scs Z (EH H) s1 s4) ?_ ?_
      · split
        · exact WP.spec_mono (WP.spec_and (sched.enqueue.sch s1 ct Q1 R1 h1 hB1 hS1.sg hctT
            (fun _ => (wr_post ‹_›).2.2.1) (fun _ => (wr_post ‹_›).1) (fun _ => (wr_post ‹_›).2.1)
            (fun _ => (hS1.act _ (hX1.2.2.bound _ hctT (wr_post ‹_›).2.1).1).2 (wr_post ‹_›).2.2.2))
            (sched.enqueue.kwN (Sg := Sg) (Kp := (∅ : Set U64)) (Nd := True) (Scs := Scs) (Z := Z) (Es := EH H) s1 ct
              h1 hctT (Set.notMem_empty _)))
            fun s4 h4 => ⟨h4.1.1, h4.1.2.1, h4.2⟩
        · exact (WP.spec_ok _).2 ⟨⟨⟨Q1, R1, h1⟩, hB1, Fr.refl _ _⟩, rfl, FootN.refl _⟩
      rintro s4 ⟨⟨⟨Q4, R4, h4⟩, hB4, f4⟩, ea4, F4⟩
      have hS4 := hS1.fr f4
      have hX4 := hX1.fr f4
      have hact4 : L.actionW s4 = act := ea4.trans act_post.symm
      have hi4 : IdleAff st s4 := hi1.step h1 F4.sN
      split
      · exact WP.spec_mono (WP.spec_and (sched.schedule_choose_new_thread.sch hA s4 a1 Q4 R4 h4 hB4 hS4 hX4)
          (sched.schedule_choose_new_thread.cur hA s4 a1 Q4 R4 h4 hB4 hS4.sg hSg hi4)) fun r hr => by
            obtain ⟨s', a'⟩ := r
            simp only [WP.uncurry'_pair] at hr ⊢
            exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, hr.2⟩
      rename_i hnc
      have hT : act ∈ T := by
        rcases h4.action with e | e | e
        · exfalso; rw [hact4] at e; rw [e, resume_val] at hnr; simp at hnr
        · exfalso; rw [hact4] at e; rw [e, choose_val] at hnc; simp at hnc
        · rw [hact4] at e; exact e
      have hT1 : L.actionW s1 ∈ T := act_post ▸ hT
      have haf : L.mem s4 (affA act) = L.cpu s4 := by
        rw [F4.sN.affK h1.tcbs hT, F4.2.1, act_post]; exact hP.act hT1
      have hbd : L.mem s4 (scA act) ≠ 0#u64 := by have := hB4.act (hact4 ▸ hT); rw [hact4] at this; exact this
      have L1 := WP.spec_and (cand_choose hA s4 a1 act Q4 R4 h4 hB4 hS4 hX4 hact4 hT true)
        (cand_choose.cur hA s4 a1 act Q4 R4 h4 hB4 hS4 hSg hi4 hact4 hT true)
      have L3 := WP.spec_and (cand_choose hA s4 a1 act Q4 R4 h4 hB4 hS4 hX4 hact4 hT false)
        (cand_choose.cur hA s4 a1 act Q4 R4 h4 hB4 hS4 hSg hi4 hact4 hT false)
      simp only [↓reduceIte, Bool.false_eq_true] at L1 L3
      replace L1 := WP.spec_mono L1 (P₁ := WP.uncurry' fun s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SchCur st s')
        fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, hr.2⟩
      replace L3 := WP.spec_mono L3 (P₁ := WP.uncurry' fun s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SchCur st s')
        fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, hr.2⟩
      have hrun : Runnable (L.mem s4 (stA act)) := by
        have := (h4.actOK (hact4 ▸ hT)).1; rwa [hact4] at this
      have L2 : sched.switch_to_thread st ar s4 a1 act ⦃ s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SchCur st s' ⦄ :=
        WP.spec_mono (WP.spec_and (sched.switch_to_thread.sch hA s4 a1 act Q4 R4 h4 hB4 hS4.sg hT hbd
          (by have := hB4.actA (hact4 ▸ hT); rwa [hact4] at this))
          (sched.switch_to_thread.cur hA s4 a1 act h4 hB4 hS4.sg hT haf hrun)) fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1.good hS4 hX4, by rw [hr.1.2.1, hr.1.1.fr.sc act hT]; exact hbd, by
            rw [hr.1.2.1, hr.1.1.fr.sc act hT]; have := hB4.actA (hact4 ▸ hT); rwa [hact4] at this, hr.2⟩
      step with sched.cur_thread.spec as ⟨ct1, _⟩
      step with sched.idle_thread.spec' as ⟨t, _⟩
      step with tcb_eq.spec as ⟨b⟩
      refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun fastfail _ => ?_
      · split
        · simp
        · step with obj.Tcb.prio.spec as ⟨i, _⟩
          step with obj.Tcb.prio.spec as ⟨i1, _⟩
          split <;> simp
      split
      · step with sched.cur_domain.spec' as ⟨i⟩
        step with obj.Tcb.prio.spec as ⟨i1, _⟩
        step with sched.is_highest_prio.ok s4 Q4 R4 h4 as ⟨b1⟩
        split
        · split
          · step with obj.Tcb.prio.spec as ⟨i2, _⟩
            split
            · exact L1
            · exact L2
          · exact L2
        · exact L3
      · split
        · step with obj.Tcb.prio.spec as ⟨i, _⟩
          step with obj.Tcb.prio.spec as ⟨i1, _⟩
          split
          · exact L1
          · exact L2
        · exact L2
    · rename_i hr0
      have e0 : L.actionW s1 = 0#u64 := by
        rw [← act_post]; rw [resume_val] at hr0
        apply UScalar.eq_of_val_eq; simpa using hr0
      exact (WP.spec_ok _).2 ⟨⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩, hB1.resume e0, hB1.curA h1.curT e0, hP.res e0⟩
  rintro ⟨s3, a2⟩ ⟨⟨⟨Q3, R3, h3⟩, hB3, hS3, hX3⟩, hcb1, hcb2, C3⟩
  have hcb := And.intro hcb1 hcb2
  try simp only [WP.uncurry'_pair]
  rw [resume_val]
  refine WP.spec_bind (WP.spec_and (sched.set_action.sch s3 0#u64 Q3 R3 h3 hB3 hS3.sg (Or.inl rfl)
    (fun hT => absurd hT (notT_small h3.tcbs (by simp))) (fun hT => absurd hT (notT_small h3.tcbs (by simp)))
    (fun _ => hcb) (fun hT => absurd hT (notT_small h3.tcbs (by simp))))
    (sched.set_action.spec s3 0#u64)) ?_
  rintro s4 ⟨⟨P4, ea4, -, -⟩, e4⟩
  have C4 : SchCur st s4 := by
    rw [e4]; exact SchCur.node h3 (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)
      (by rw [act_val]; omega) C3
  obtain ⟨⟨Q4, R4, h4⟩, hB4, hS4, hX4⟩ := P4.good hS3 hX3
  have hcT := h4.curT
  have hb4 : L.mem s4 (scA (L.curW s4)) ≠ 0#u64 := hB4.resume ea4
  have hO4 := hX4.1
  have hsub4 := hS4.sub
  have hts : L.mem s4 (scA (L.curW s4)) ∈ Scs := (hX4.2.2.bound _ hcT hb4).1
  have hcs : L.cscW s4 ∈ Scs := hX4.2.2.cur
  obtain ⟨hPc, hzc⟩ := hO4.sc _ hcs
  obtain ⟨h8c, h128c, -⟩ := sc_lo hPc hzc
  have hvc := sc_word_val hPc hzc (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hcq : SCq st s4 Ω (L.cscW s4) (Z (L.cscW s4)) := by
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO4 hcs
    exact ⟨(hS4.all _ hcs).1, fun b hb hi => hsub4 _ ((hS4.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hvc]; omega, by rw [hvc, hcv]; omega⟩, by unfold Aligned; rw [hvc, hcv]; omega⟩, ⟨a2, a3⟩, a1⟩
  have htin : SCin st s4 Ω (L.mem s4 (scA (L.curW s4))) (Z (L.mem s4 (scA (L.curW s4)))) :=
    (hS4.scin hts (hB4.curA hcT ea4)).mono hsub4
  have hN4 := h4.nodes _ h4.cur
  refine WP.spec_bind (sched.switch_sched_context.free hA s4 a2 (zt := Z (L.mem s4 (scA (L.curW s4))))
    (zc := Z (L.cscW s4)) h4.cur hN4 h4.omega hcq (fun hne => ⟨htin, hS4.disj _ hcT hb4 hne⟩)) ?_
  rintro ⟨s5, a3⟩ w5
  simp only [WP.uncurry'_pair] at w5 ⊢
  have h5 := (free_step h4 hB4 w5).1
  have C5 : SchCur st s5 := C4.free h4 w5
  step with LawfulStore.cur_cpu_spec as ⟨c, c_post⟩
  step with obj.node_get.spec as ⟨i, _⟩
  refine WP.spec_bind (Pₘ := fun r => SchedQueuesInv st T Cs Ω H r.1 Q4 R4 ∧ SchCur st r.1) ?_ ?_
  · split
    · have hB5 := (free_step h4 hB4 w5).2
      refine WP.spec_bind (sched.set_next_interrupt.free (Ω := Ω) hA s5 a3 h5.cur (h5.nodes _ h5.cur)) ?_
      rintro ⟨s7, a5⟩ w7
      simp only [WP.uncurry'_pair] at w7 ⊢
      step with obj.node_set.spec as ⟨s8, s8_post⟩
      try simp only [WP.spec_ok]
      have w8 : WritesIn st s5 s8 (L.Free s5 Ω Cs) := by
        rw [s8_post, c_post]
        exact w7.free_trans (free_node_write w7.1 h5.cur (h5.nodes _ h5.cur)
          (by simp [layout.node.REPROGRAM, LowFree]))
      exact ⟨(free_step h5 hB5 w8).1, C5.free h5 w8⟩
    · exact (WP.spec_ok _).2 ⟨h5, C5⟩
  rintro ⟨s6, a4⟩ ⟨h6, C6⟩
  try simp only [WP.uncurry'_pair]
  exact WP.spec_mono (smp.send_pending.free (Ω := Ω) hA s6 a4 h6.cur (h6.nodes _ h6.cur)) fun r w => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at w ⊢
    exact C6.free h6 w

end

end Fl4Proofs.P1
