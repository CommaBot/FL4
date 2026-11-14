/-
P1: `sched::schedule` (seL4 `schedule`) keeps `SchedQueuesInv` with
`BoundInv` (see `QueueSchedStep`) and `XInv` (reply objects and SCs, see
`QueueObjs`), given that `timer::fire` keeps them and `SCsOK`.

`timer::fire` delivers notification signals: it can wake threads and change
the ready, release and endpoint queues, so it is not footprint-disjoint
from the invariant.  Its preservation is the hypothesis `hfire`.  The rest
is proved: `awaken`'s release loop, `check_domain_time` (a no-op with one
domain), the action handling (`enqueue` of the current thread, `append` /
`enqueue` of the candidate, `switch_to_thread`, `schedule_choose_new_thread`
with `next_domain` and `choose_thread`), and the free-word steps after it
(`switch_sched_context`, `set_next_interrupt`, clearing `REPROGRAM`,
`send_pending`), by their footprints.
-/
import Fl4Proofs.P1.QueueSchedStep
import Fl4Proofs.P1.QueueObjs
import Fl4Proofs.P1.QueueSwitch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {A : Type _} {ar : machine.Arch A}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- The three invariants together. -/
def Good (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat)
    (Ac : Set U64) (s : S) :
    Prop :=
  (∃ Q R, SchedQueuesInv st T Cs Ω H s Q R) ∧ BoundInv st T Ac s ∧ SCsOK st T Ω Sg Scs Z Ac s ∧
    XInv st T Cs Ω Sg Rp Scs Nt Z s

theorem Post.good {s s' : S} (hS : SCsOK st T Ω Sg Scs Z Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (h : Post st T Cs Ω H Sg Ac s s') : Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' :=
  ⟨h.inv, h.bnd, hS.fr h.fr, hX.fr h.fr⟩

theorem sched.set_cur_thread.sch (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) (ht : t ∈ T)
    (hbd : L.actionW s = 0#u64 → L.mem s (scA t) ≠ 0#u64) (hta : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac) :
    sched.set_cur_thread st s t ⦃ s' => Post st T Cs Ω H Sg Ac s s' ∧ L.curW s' = t ∧ L.actionW s' = L.actionW s ⦄ := by
  refine WP.spec_mono (sched.set_cur_thread.spec s t) fun s' e => ?_
  subst e
  have hN' := h.nodes _ h.cur
  have hB1 := hB.wr_node h (o := layout.node.CUR_THREAD) (v := t) (by rw [curth0]; omega) (by rw [curth0])
    (by rw [curth0]; omega) (fun e => by rw [curth0] at e; omega) (fun _ => ⟨ht, hbd⟩)
    (fun _ _ h0 => Or.inr (hta h0))
  have f := fr_node (Sg := Sg) (hi8 := fun _ => by simp [layout.node.SCHED_ACTION, layout.node.REPROGRAM, layout.node.CUR_THREAD]) (v := t) h hS h.cur (by rw [curth0]; omega) (by rw [curth0])
    (hto := ⟨by rw [curth0]; omega, by rw [curth0]; omega⟩)
    (fun _ => by rw [curth0]; omega)
  have ea := rd_cur_node (v := t) h (by rw [curth0]; omega) (by rw [curth0]) (by rw [act_val]; omega)
    (by rw [act_val]) (by rw [act_val, curth0]; omega)
  have ec : L.curW (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) t) = t := by
    unfold LawfulStore.curW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_same (nodeAt_aligned hN' (by rw [curth0]; omega) (by rw [curth0]))
  exact ⟨⟨⟨Q, R, inv_set_cur h ht⟩, hB1, f⟩, ec, ea⟩

/-- seL4 `switchToThread`, for a bound thread. -/
theorem sched.switch_to_thread.sch (hA : P0.ArchTotal ar) (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) (ht : t ∈ T)
    (hbd : L.mem s (scA t) ≠ 0#u64) (hta : L.mem s (scA t) ∈ Ac) :
    sched.switch_to_thread st ar s a t ⦃ s' _ => Post st T Cs Ω H Sg Ac s s' ∧ L.curW s' = t ∧
      L.actionW s' = L.actionW s ⦄ := by
  unfold sched.switch_to_thread
  refine WP.spec_bind (set_vm_root_same hA s a t) ?_
  rintro ⟨s1, a1⟩ e
  simp only [WP.uncurry'_pair] at e
  subst e
  refine WP.spec_bind (sched.dequeue.sch s1 t Q R h hB hS ht) ?_
  rintro s2 ⟨⟨⟨Q2, R2, h2⟩, hB2, f2⟩, ea2, -⟩
  refine WP.spec_bind (sched.set_cur_thread.sch s2 t Q2 R2 h2 hB2 (hS.fr f2) ht
    (fun _ => by rw [f2.sc t ht]; exact hbd) (fun _ => by rw [f2.sc t ht]; exact hta)) ?_
  rintro s3 ⟨P3, ec3, ea3⟩
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact ⟨Post.trans f2 P3, ec3, ea3.trans ea2⟩

/-- seL4 `chooseThread`: the new current thread is bound. -/
theorem sched.choose_thread.sch (hA : P0.ArchTotal ar) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) :
    sched.choose_thread st ar s a ⦃ s' _ => Post st T Cs Ω H Sg Ac s s' ∧ L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ⦄ := by
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
    have hqq : (L.mem s (inqA q.head) &&& sched.Q_QUEUED) ≠ 0#u64 := by
      obtain ⟨e1, e2⟩ := h.inQ _ h.cur p hp _ hmem
      exact (h.queued _ htT).2 (by rw [e1, e2]; exact hmem)
    have hbd : L.mem s (scA q.head) ≠ 0#u64 := hB.q _ htT hqq
    refine WP.spec_mono (sched.switch_to_thread.sch hA s a q.head Q R h hB hS htT hbd (hB.qA htT hqq)) fun r hr => ?_
    obtain ⟨s', a'⟩ := r
    obtain ⟨P, ec, -⟩ := hr
    exact ⟨P, by rw [ec, P.fr.sc _ htT]; exact hbd, by rw [ec, P.fr.sc _ htT]; exact hB.qA htT hqq⟩
  · unfold sched.switch_to_idle_thread
    step with sched.idle_thread.spec' as ⟨idle, idle_post⟩
    refine WP.spec_bind (set_kernel_vm_root_same (st := st) hA s a) ?_
    rintro ⟨s1, a1⟩ e
    simp only [WP.uncurry'_pair] at e
    subst s1
    have hiT : idle ∈ T := by rw [idle_post]; exact h.idleT
    have hbd : L.mem s (scA idle) ≠ 0#u64 := by rw [idle_post]; exact hB.idle
    refine WP.spec_bind (sched.set_cur_thread.sch s idle Q R h hB hS hiT (fun _ => hbd)
      (fun _ => by rw [idle_post]; exact hB.idleA h.idleT)) ?_
    rintro s2 ⟨P, ec, -⟩
    simp only [WP.spec_ok, WP.uncurry'_pair]
    exact ⟨P, by rw [ec, P.fr.sc _ hiT]; exact hbd, by rw [ec, P.fr.sc _ hiT, idle_post]; exact hB.idleA h.idleT⟩

@[step] theorem sched.domain_time.spec (s : S) : sched.domain_time st s ⦃ _ => True ⦄ := by
  unfold sched.domain_time; exact WP.spec_mono (obj.ks_get.spec s _) fun _ _ => trivial

/-- seL4 `scheduleChooseNewThread`. -/
theorem sched.schedule_choose_new_thread.sch (hA : P0.ArchTotal ar) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) :
    sched.schedule_choose_new_thread st ar s a ⦃ s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ⦄ := by
  unfold sched.schedule_choose_new_thread
  step with sched.domain_time.spec as ⟨i⟩
  refine WP.spec_bind (Pₘ := fun s1 => Post st T Cs Ω H Sg Ac s s1) ?_ ?_
  · split
    · exact WP.spec_mono (sched.next_domain.sch s Q R h hB hS.sg) fun s1 h1 => h1.1
    · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, hB, Fr.refl _ _⟩
  rintro s1 ⟨⟨Q1, R1, h1⟩, hB1, f1⟩
  have hS1 := hS.fr f1
  exact WP.spec_mono (sched.choose_thread.sch hA s1 a Q1 R1 h1 hB1 hS1.sg) fun r hr => by
    obtain ⟨s', a'⟩ := r
    exact ⟨hr.1.good hS1 (hX.fr f1), hr.2⟩

/-! ## `schedule` -/

theorem tcb_eq.spec (a b : obj.Tcb) : obj.Tcb.Insts.CoreCmpPartialEqTcb.eq a b ⦃ _ => True ⦄ := by
  unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq; simp

theorem sched.cur_domain.spec' (s : S) : sched.cur_domain st s ⦃ _ => True ⦄ := by
  unfold sched.cur_domain; exact WP.spec_mono (obj.ks_get.spec s _) fun _ _ => trivial

theorem sched.is_highest_prio.ok {X : Set U64} (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (dom prio : U64) :
    sched.is_highest_prio st s dom prio ⦃ _ => True ⦄ := by
  unfold sched.is_highest_prio sched.bitmap_dom
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  rw [ite_cond_eq_false _ _ (by simp)]
  simp only [bind_ok]
  step with LawfulStore.cur_cpu_spec as ⟨cpu, cpu_post⟩
  subst cpu_post
  step with l1_off_zero as ⟨i1, i1_post⟩
  subst i1_post
  step with obj.node_get.spec as ⟨i2, i2_post⟩
  split
  · simp
  · have hne : L.l1W s (L.cpu s) ≠ 0#u64 := by
      rw [show L.l1W s (L.cpu s) = i2 from i2_post.symm]; assumption
    exact WP.spec_bind (sched.highest_prio.spec s dom _ (h.nodes _ h.cur) (h.ready _ h.cur).2 hne)
      fun _ _ => by simp

theorem free_step {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hw : WritesIn st s s' (L.Free s Ω Cs)) :
    SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T Ac s' := ⟨inv_of_free h hw, hB.free h hw⟩


/-- `SCsOK` after `switch_sched_context`: the two rings it writes stay well
formed (`switch_sched_context.fp`), the other SCs are disjoint objects, and
the new current SC is the current thread's. -/
theorem SCsOK.switch {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hb : L.mem s (scA (L.curW s)) ≠ 0#u64)
    (w : WritesIn st s s' (fun b => InRing (L.mem s (scA (L.curW s))) (Z (L.mem s (scA (L.curW s)))) b ∨
      (InRing (L.cscW s) (Z (L.cscW s)) b ∨ b = core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) ∨
      b = L.nodeA s layout.node.REPROGRAM ∨ b = L.nodeA s layout.node.CONSUMED ∨ b = L.nodeA s layout.node.CUR_SC))
    (e : L.mem s' (L.nodeA s layout.node.CUR_SC) = L.mem s (scA (L.curW s)))
    (wfc : L.rmax s (L.cscW s) ≠ 0#u64 → RefillsWF st s' (L.cscW s) (Z (L.cscW s)))
    (wft : L.mem s (scA (L.curW s)) ≠ L.cscW s →
      RefillsWF st s' (L.mem s (scA (L.curW s))) (Z (L.mem s (scA (L.curW s))))) :
    SCsOK st T Ω Sg Scs Z Ac s' := by
  obtain ⟨hO, -, hE⟩ := hX
  have hcT := h.curT
  have hN' := h.nodes _ h.cur
  set tsc := L.mem s (scA (L.curW s)) with htsc
  set csc := L.cscW s with hcsc
  have htS : tsc ∈ Scs := (hE.bound _ hcT hb).1
  have hcS : csc ∈ Scs := hE.cur
  -- TCB fields are not written
  have fld : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := by
    intro y hy
    refine w.mem_eq (scA_aligned (h.tcbs y hy)) ?_
    have nf : ∀ c ∈ Scs, ¬ InSC c (Z c) (scA y) := fun c hc hin =>
      out_ne_field (h.omega _ (hO.scW c hc _ (scA_aligned (h.tcbs y hy)) hin)) hy (h.tcbs y hy)
        (K := 3464#u64) (by decide) rfl
    rintro (hh | (hh | hh) | hh | hh | hh)
    · exact nf _ htS hh.inSC
    · exact nf _ hcS hh.inSC
    · rw [scA_eq] at hh
      obtain ⟨-, -, -, -, -, -, -, -⟩ := sc_facts hO hcS
      have hm : core.num.U64.wrapping_add y 3464#u64 ∈ Ω := by
        rw [hh]
        obtain ⟨hP, hz⟩ := hO.sc csc hcS
        obtain ⟨h8, h128, -⟩ := sc_lo hP hz
        have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
        exact hO.scW csc hcS _ (by unfold Aligned; rw [hv]; simp [layout.sc.CONSUMED]; omega)
          ⟨by rw [hv]; simp [layout.sc.CONSUMED], by rw [hv]; simp [layout.sc.CONSUMED]; omega⟩
      exact out_ne_field (h.omega _ hm) hy (h.tcbs y hy) (by simp) rfl
    all_goals rw [scA_eq] at hh; exact node_ne_field hN' (by simp [layout.node.REPROGRAM, layout.node.CONSUMED,
      layout.node.CUR_SC]) hy (h.tcbs y hy) (by simp) hh.symm
  -- an SC object other than the two keeps its ring
  have hout : ∀ c ∈ Scs, c ≠ tsc → c ≠ csc → ∀ b, Aligned b → (InRing tsc (Z tsc) b ∨
      (InRing csc (Z csc) b ∨ b = core.num.U64.wrapping_add csc layout.sc.CONSUMED) ∨
      b = L.nodeA s layout.node.REPROGRAM ∨ b = L.nodeA s layout.node.CONSUMED ∨ b = L.nodeA s layout.node.CUR_SC) →
      Outside b c (Z c) := by
    intro c hc h1 h2 b hb hh
    have dj := fun c' (hc' : c' ∈ Scs) (hne : c ≠ c') => hO.scDisj c hc c' hc' hne
    rcases hh with hh | (hh | hh) | hh | hh | hh
    · have := dj _ htS h1; unfold Outside; unfold InRing at hh; omega
    · have := dj _ hcS h2; unfold Outside; unfold InRing at hh; omega
    · have := dj _ hcS h2
      obtain ⟨hP, hz⟩ := hO.sc csc hcS
      obtain ⟨-, h128, -⟩ := sc_lo hP hz
      have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
      unfold Outside; rw [hh, hv]; simp [layout.sc.CONSUMED]; omega
    all_goals
      subst hh
      exact node_out_place (hO.scW c hc) h.omega h.cur hN'
        (by simp [layout.node.REPROGRAM, layout.node.CONSUMED, layout.node.CUR_SC])
        (by simp [layout.node.REPROGRAM, layout.node.CONSUMED, layout.node.CUR_SC])
  have other : ∀ c ∈ Scs, c ≠ tsc → c ≠ csc → RefillsWF st s c (Z c) → RefillsWF st s' c (Z c) :=
    fun c hc h1 h2 hW => hW.writesIn w (hout c hc h1 h2)
  have hcs' : L.cscW s' = tsc := by unfold LawfulStore.cscW; rw [cscW_eq w.1 w.2.1]; exact e
  -- the `REFILL_MAX` and `SPORADIC` words are not written
  have kk : ∀ c ∈ Scs, ∀ b, Aligned b → (b.val = c.val + 72 ∨ b.val = c.val + 64 ∨ b.val = c.val + 32) →
      L.mem s' b = L.mem s b := by
    intro c hc b hb hv
    have hbΩ : b ∈ Ω := by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc; obtain ⟨-, h128c, -⟩ := sc_lo hPc hzc
      exact hO.scW c hc _ hb ⟨by omega, by omega⟩
    have dj := fun c' (hc' : c' ∈ Scs) (hne : c ≠ c') => hO.scDisj c hc c' hc' hne
    have h128 := (sc_facts hO hc).1
    refine w.mem_eq hb ?_
    rintro (hh | (hh | hh) | hh | hh | hh)
    · unfold InRing at hh
      by_cases e' : c = tsc
      · subst e'; omega
      · have := dj _ htS e'; omega
    · unfold InRing at hh
      by_cases e' : c = csc
      · subst e'; omega
      · have := dj _ hcS e'; omega
    · obtain ⟨hP, hz⟩ := hO.sc csc hcS
      have hv' := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
      have := congrArg UScalar.val hh
      rw [hv'] at this; simp [layout.sc.CONSUMED] at this
      by_cases e' : c = csc
      · subst e'; omega
      · have := dj _ hcS e'; have := (sc_facts hO hcS).1; omega
    all_goals
      subst hh
      exact out_ne_node (h.omega _ hbΩ) h.cur hN'
        (by simp [layout.node.REPROGRAM, layout.node.CONSUMED, layout.node.CUR_SC]) rfl
  have kmx : ∀ c ∈ Scs, L.mem s' (maxA c) = L.mem s (maxA c) := fun c hc =>
    kk c hc _ (maxA_facts hO hc).1 (Or.inl (sc_facts hO hc).2.2.2.1)
  have ksp : ∀ c ∈ Scs, L.mem s' (sporA c) = L.mem s (sporA c) := fun c hc => by
    obtain ⟨hPc, hzc⟩ := hO.sc c hc; obtain ⟨h8c, -, -⟩ := sc_lo hPc hzc
    have := sporA_val hPc hzc
    exact kk c hc _ (by unfold Aligned; omega) (Or.inr (Or.inl this))
  refine ⟨hS.sub, fun b hb => by rw [w.1]; exact hS.ks b hb, fun o h1 h2 => by rw [w.1]; exact hS.ksΩ o h1 h2,
    fun y hy hy0 hne => ?_, fun c hc => ?_,
    fun c hc => by rw [show L.rmax s' c = L.rmax s c from kmx c hc]; exact hS.act c hc,
    fun c hc h0 => hS.spor c hc (by rw [← ksp c hc]; exact h0), hS.spSg, fun c hc h0 => hS.rep c hc (by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc; obtain ⟨h8c, -, -⟩ := sc_lo hPc hzc
      have := scReplyA_val hPc hzc
      rwa [kk c hc _ (by unfold Aligned; omega) (Or.inr (Or.inr this))] at h0), hS.repSg⟩
  · rw [fld y hy] at hy0 hne ⊢
    rw [hcs'] at hne ⊢
    intro b hin
    have := hO.scDisj _ (hE.bound y hy hy0).1 _ htS hne
    unfold Outside; unfold InSC at hin; omega
  · by_cases e1 : c = csc
    · subst e1; exact (hS.all _ hc).mk' fun hm => wfc (by
        rw [show L.rmax s (L.cscW s) = L.mem s (maxA (L.cscW s)) from rfl, ← kmx _ hc]; exact hm)
    by_cases e2 : c = tsc
    · subst e2; exact (hS.all _ hc).mk' fun _ => wft e1
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO hc
    exact (hS.all c hc).writesIn a1 ⟨a2, a3⟩ w (hout c hc e2 e1)

/-- A write to a current-node word other than `CUR_SC` keeps `SCsOK`. -/
theorem SCsOK.node {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {o : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ho : o.val < 4288) (h8 : o.val % 8 = 0)
    (h24 : o.val ≠ 24) (hto : o.val ≠ 88 ∧ o.val ≠ 104 ∧ o.val ≠ 112) (w : WritesIn st s s' (· = L.nodeAt s (L.cpu s) o))
    (hi8 : o.val ≠ 8) :
    SCsOK st T Ω Sg Scs Z Ac s' := by
  have hN' := h.nodes _ h.cur
  have k : ∀ b, Aligned b → b ≠ L.nodeAt s (L.cpu s) o → L.mem s' b = L.mem s b := fun b hb hn =>
    w.mem_eq hb (fun e => hn e)
  refine hS.fr ⟨w.1, w.2.1, fun b hb => k b (h.omega _ (hS.sub b hb)).1 (fun e =>
      out_ne_node (h.omega _ (hS.sub b hb)) h.cur hN' ho (congrArg UScalar.val e).symm),
    fun y hy => k _ (scA_aligned (h.tcbs y hy)) (fun e => by
      rw [scA_eq] at e; exact node_ne_field hN' ho hy (h.tcbs y hy) (by simp) e.symm), ?_,
    fun y hy => k _ (field_aligned (h.tcbs y hy) (by simp) (by simp)) (fun e =>
      node_ne_field hN' ho hy (h.tcbs y hy) (by simp) e.symm),
    fun y hy => k _ (by rw [stA_eq]; exact field_aligned (h.tcbs y hy) (by simp) (by simp)) (fun e => by
      rw [stA_eq] at e; exact node_ne_field hN' ho hy (h.tcbs y hy) (by simp) e.symm),
    fun y hy => k _ (field_aligned (h.tcbs y hy) (by simp) (by simp)) (fun e =>
      node_ne_field hN' ho hy (h.tcbs y hy) (by simp) e.symm),
    fun y hy K h1 h2 h3 => k _ (field_aligned (h.tcbs y hy) (by omega) h3) (fun e =>
      node_ne_field hN' ho hy (h.tcbs y hy) (by omega) e.symm),
    fun c hc o' ho' => k _ (nodeAt_aligned hc (by omega) (by omega)) (fun e =>
      node_ne_node hN' hc ho (by omega) (fun _ => by omega) (congrArg UScalar.val e).symm),
    fun y hy => k _ (field_aligned (h.tcbs y hy) (by simp) (by simp)) (fun e =>
      node_ne_field hN' ho hy (h.tcbs y hy) (by simp) e.symm), ?_⟩
  rotate_right
  · unfold LawfulStore.idleW; rw [w.2.1, nodeAt_of_ksb w.1]
    refine k _ (nodeAt_aligned hN' (by rw [idle8]; omega) (by rw [idle8])) (fun e => ?_)
    have := congrArg UScalar.val e
    rw [nodeAt_val hN' (by rw [idle8]; omega), nodeAt_val hN' ho, idle8] at this; omega
  unfold LawfulStore.cscW; rw [cscW_eq w.1 w.2.1]
  refine k _ (nodeAt_aligned hN' (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])) (fun e => ?_)
  have := congrArg UScalar.val e
  simp only [LawfulStore.nodeA] at this
  rw [nodeAt_val hN' (by simp [layout.node.CUR_SC]), nodeAt_val hN' ho] at this
  simp [layout.node.CUR_SC] at this; omega

/-- The switch-to candidate `act` of the action: appended or enqueued, then
a new thread is chosen. -/
theorem cand_choose (hA : P0.ArchTotal ar) (s : S) (a : A) (act : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hact : L.actionW s = act) (hT : act ∈ T) (app : Bool) :
    (do
      let s5 ← if app then sched.append st s act else sched.enqueue st s act
      let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
      sched.schedule_choose_new_thread st ar s6 a) ⦃ s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
        L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ⦄ := by
  have hok := h.actOK (hact ▸ hT)
  rw [hact] at hok
  have hr : (L.mem s (inqA act) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hc
    exact hok.2 _ (h.aff act hT) ((h.released act hT).1 hc)
  have hbd : L.mem s (scA act) ≠ 0#u64 := by have := hB.act (hact ▸ hT); rw [hact] at this; exact this
  refine WP.spec_bind (Pₘ := fun s5 => Post st T Cs Ω H Sg Ac s s5) ?_ ?_
  · split
    · exact WP.spec_mono (sched.append.sch s act Q R h hB hS.sg hT (fun _ => hr) (fun _ => hok.1) (fun _ => hbd)
        (fun _ => by have := hB.actA (hact ▸ hT); rwa [hact] at this)) fun s5 h5 => h5.1
    · exact WP.spec_mono (sched.enqueue.sch s act Q R h hB hS.sg hT (fun _ => hr) (fun _ => hok.1) (fun _ => hbd)
        (fun _ => by have := hB.actA (hact ▸ hT); rwa [hact] at this)) fun s5 h5 => h5.1
  rintro s5 ⟨⟨Q5, R5, h5⟩, hB5, f5⟩
  rw [choose_val]
  refine WP.spec_bind (sched.set_action.sch s5 1#u64 Q5 R5 h5 hB5 (hS.fr f5).sg (Or.inr (Or.inl rfl))
    (fun hT => absurd hT (one_notT h)) (fun hT => absurd hT (one_notT h)) (fun e => by simp at e)
    (fun hT => absurd hT (one_notT h))) ?_
  rintro s6 ⟨⟨⟨Q6, R6, h6⟩, hB6, f6⟩, -, -, -⟩
  exact sched.schedule_choose_new_thread.sch hA s6 a Q6 R6 h6 hB6 ((hS.fr f5).fr f6) ((hX.fr f5).fr f6)

/-- Writes to free words keep the current node's action and current-thread
words and the TCBs' `SC` fields. -/
theorem free_keys {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' (L.Free s Ω Cs)) :
    L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.idleW s' = L.idleW s ∧
      ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := by
  have hT := h.tcbs
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK hK8
    refine hw.mem_eq (field_aligned (hT y hy) hK hK8) ?_
    rintro (hm | ⟨c, hc, o, ho, e⟩)
    · exact out_ne_field (h.omega _ hm) hy (hT y hy) hK rfl
    · exact node_ne_field (h.nodes c hc) (by simp only [LowFree] at ho; omega) hy (hT y hy) hK e.symm
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → ¬ LowFree o.val →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 hro
    rw [hw.2.1, nodeAt_of_ksb hw.1]
    refine hw.mem_eq (nodeAt_aligned (h.nodes _ h.cur) ho h8) ?_
    rintro (hm | ⟨c', hc', o', ho', e⟩)
    · exact out_ne_node (h.omega _ hm) h.cur (h.nodes _ h.cur) ho rfl
    · by_cases ec : L.cpu s = c'
      · subst ec
        have := congrArg UScalar.val e
        rw [nodeAt_val (h.nodes _ h.cur) ho, nodeAt_val (h.nodes _ h.cur) (by simp only [LowFree] at ho'; omega)] at this
        exact hro (by have : o.val = o'.val := by omega
                      rw [this]; exact ho')
      · exact nodeAt_ne_cpu (h.nodes _ h.cur) (h.nodes _ hc') ho (by simp only [LowFree] at ho'; omega) ec e
  exact ⟨by unfold LawfulStore.actionW; exact nd _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; simp [LowFree]),
    by unfold LawfulStore.curW; exact nd _ (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; simp [LowFree]),
    by unfold LawfulStore.idleW; exact nd _ (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; simp [LowFree]),
    fun y hy => by rw [scA_eq]; exact fld y hy _ (by simp) (by simp)⟩

/-- seL4 `schedule` keeps the queue invariant (and `BoundInv`), given that
`timer::fire` keeps the invariants. -/
theorem sched.schedule.inv (hA : P0.ArchTotal ar) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hfire : timer.fire st ar s a ⦃ s1 _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ⦄) :
    sched.schedule st ar s a ⦃ s' _ => (∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R') ∧ BoundInv st T Ac s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ L.cscW s' ∈ Ac ∧
      L.actionW s' = 0#u64 ∧ L.cscW s' = L.mem s' (scA (L.curW s')) ⦄ := by
  unfold sched.schedule sched.awaken
  -- `awaken`
  refine WP.spec_bind (Pₘ := fun r => Good st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_ ?_
  · refine WP.spec_bind hfire ?_
    rintro ⟨s1, a1⟩ ⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (sched.awaken_loop.sch s1 _ Q1 R1 h1 hB1 hS1.sg) ?_
    rintro s2 ⟨P2, -⟩
    exact (WP.spec_ok _).2 (P2.good hS1 hX1)
  rintro ⟨s1, a1⟩ ⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩
  -- `check_domain_time` does nothing with one domain
  unfold sched.check_domain_time sched.is_cur_domain_expired
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have hnd : ¬ ((1#u64) > (1#u64)) := by simp
  simp only [hnd, ↓reduceIte, bind_ok, Bool.false_eq_true]
  step with sched.action.spec as ⟨act, act_post⟩
  -- the action
  refine WP.spec_bind (Pₘ := fun r => Good st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ L.mem r.1 (scA (L.curW r.1)) ≠ 0#u64 ∧
      L.mem r.1 (scA (L.curW r.1)) ∈ Ac) ?_ ?_
  · split
    · rename_i hnr
      step with sched.cur_thread.spec as ⟨ct, ct_post⟩
      have hctT : ct ∈ T := by rw [ct_post]; exact h1.curT
      step with sched.is_schedulable.spec' as ⟨wr, wr_post⟩
      refine WP.spec_bind (Pₘ := fun s4 => Post st T Cs Ω H Sg Ac s1 s4 ∧ L.actionW s4 = L.actionW s1) ?_ ?_
      · split
        · exact WP.spec_mono (sched.enqueue.sch s1 ct Q1 R1 h1 hB1 hS1.sg hctT (fun _ => (wr_post ‹_›).2.2.1)
            (fun _ => (wr_post ‹_›).1) (fun _ => (wr_post ‹_›).2.1)
            (fun _ => (hS1.act _ (hX1.2.2.bound _ hctT (wr_post ‹_›).2.1).1).2 (wr_post ‹_›).2.2.2))
            fun s4 h4 => ⟨h4.1, h4.2.1⟩
        · exact (WP.spec_ok _).2 ⟨⟨⟨Q1, R1, h1⟩, hB1, Fr.refl _ _⟩, rfl⟩
      rintro s4 ⟨⟨⟨Q4, R4, h4⟩, hB4, f4⟩, ea4⟩
      have hS4 := hS1.fr f4
      have hX4 := hX1.fr f4
      have hact4 : L.actionW s4 = act := ea4.trans act_post.symm
      split
      · exact WP.spec_mono (sched.schedule_choose_new_thread.sch hA s4 a1 Q4 R4 h4 hB4 hS4 hX4) fun r hr => hr
      rename_i hnc
      have hT : act ∈ T := by
        rcases h4.action with e | e | e
        · exfalso; rw [hact4] at e; rw [e, resume_val] at hnr; simp at hnr
        · exfalso; rw [hact4] at e; rw [e, choose_val] at hnc; simp at hnc
        · rw [hact4] at e; exact e
      have hbd : L.mem s4 (scA act) ≠ 0#u64 := by have := hB4.act (hact4 ▸ hT); rw [hact4] at this; exact this
      have L1 := cand_choose hA s4 a1 act Q4 R4 h4 hB4 hS4 hX4 hact4 hT true
      have L3 := cand_choose hA s4 a1 act Q4 R4 h4 hB4 hS4 hX4 hact4 hT false
      simp only [↓reduceIte, Bool.false_eq_true] at L1 L3
      have L2 : sched.switch_to_thread st ar s4 a1 act ⦃ s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ⦄ :=
        WP.spec_mono (sched.switch_to_thread.sch hA s4 a1 act Q4 R4 h4 hB4 hS4.sg hT hbd
          (by have := hB4.actA (hact4 ▸ hT); rwa [hact4] at this)) fun r hr => by
          obtain ⟨s', a'⟩ := r
          exact ⟨hr.1.good hS4 hX4, by rw [hr.2.1, hr.1.fr.sc act hT]; exact hbd, by
            rw [hr.2.1, hr.1.fr.sc act hT]; have := hB4.actA (hact4 ▸ hT); rwa [hact4] at this⟩
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
      exact (WP.spec_ok _).2 ⟨⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩, hB1.resume e0, hB1.curA h1.curT e0⟩
  rintro ⟨s3, a2⟩ ⟨⟨⟨Q3, R3, h3⟩, hB3, hS3, hX3⟩, hcb⟩
  try simp only [WP.uncurry'_pair]
  -- resume, then switch the SC
  rw [resume_val]
  refine WP.spec_bind (sched.set_action.sch s3 0#u64 Q3 R3 h3 hB3 hS3.sg (Or.inl rfl)
    (fun hT => absurd hT (notT_small h3.tcbs (by simp))) (fun hT => absurd hT (notT_small h3.tcbs (by simp)))
    (fun _ => hcb) (fun hT => absurd hT (notT_small h3.tcbs (by simp)))) ?_
  rintro s4 ⟨P4, ea4, -, -⟩
  obtain ⟨⟨Q4, R4, h4⟩, hB4, hS4, hX4⟩ := P4.good hS3 hX3
  have hcT := h4.curT
  have hb4 : L.mem s4 (scA (L.curW s4)) ≠ 0#u64 := hB4.resume ea4
  have hO4 := hX4.1
  have hsub4 := hS4.sub
  have hts : L.mem s4 (scA (L.curW s4)) ∈ Scs := (hX4.2.2.bound _ hcT hb4).1
  have hcs : L.cscW s4 ∈ Scs := hX4.2.2.cur
  have npn : ∀ o : U64, o.val < 4288 → ¬ Prot T Rp Scs Nt (L.nodeA s4 o) := fun o ho =>
    not_prot_node h4 hO4 hsub4 h4.cur ho
  have hcq : SCq st s4 Ω (L.cscW s4) (Z (L.cscW s4)) := by
    obtain ⟨hP, hz⟩ := hO4.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO4 hcs
    exact ⟨(hS4.all _ hcs).1, fun b hb hi => hsub4 _ ((hS4.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩, by unfold Aligned; rw [hv, hcv]; omega⟩, ⟨a2, a3⟩, a1⟩
  have htin : SCin st s4 Ω (L.mem s4 (scA (L.curW s4))) (Z (L.mem s4 (scA (L.curW s4)))) :=
    (hS4.scin hts (hB4.curA hcT ea4)).mono hsub4
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.switch_sched_context.free hA s4 a2 (zt := Z (L.mem s4 (scA (L.curW s4))))
    (zc := Z (L.cscW s4)) h4.cur (h4.nodes _ h4.cur) h4.omega hcq
    (fun hne => ⟨htin, hS4.disj _ hcT hb4 hne⟩))
    (sched.switch_sched_context.fp hA s4 a2 (zt := Z (L.mem s4 (scA (L.curW s4))))
    (zc := Z (L.cscW s4)) (B := fun b => ¬ Prot T Rp Scs Nt b) h4.cur (h4.nodes _ h4.cur) h4.omega
    hcq (fun hne => ⟨htin, hS4.disj _ hcT hb4 hne⟩)
    (npn _ (by simp [layout.node.REPROGRAM])) (npn _ (by simp [layout.node.CONSUMED]))
    (npn _ (by simp [layout.node.CUR_SC]))
    (fun _ b hb hr => not_prot_ring h4 hO4 hts hb (Or.inl hr))
    (fun b hb hr => not_prot_ring h4 hO4 hcs hb hr)))
    (sched.switch_sched_context.fp hA s4 a2 (zt := Z (L.mem s4 (scA (L.curW s4))))
      (zc := Z (L.cscW s4))
      (B := fun b => InRing (L.mem s4 (scA (L.curW s4))) (Z (L.mem s4 (scA (L.curW s4)))) b ∨
        (InRing (L.cscW s4) (Z (L.cscW s4)) b ∨ b = core.num.U64.wrapping_add (L.cscW s4) layout.sc.CONSUMED) ∨
        b = L.nodeA s4 layout.node.REPROGRAM ∨ b = L.nodeA s4 layout.node.CONSUMED ∨
        b = L.nodeA s4 layout.node.CUR_SC) h4.cur (h4.nodes _ h4.cur) h4.omega
      hcq (fun hne => ⟨htin, hS4.disj _ hcT hb4 hne⟩)
      (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (fun _ b _ hr => Or.inl hr) (fun b _ hr => Or.inr (Or.inl hr)))) ?_
  rintro ⟨s5, a3⟩ ⟨⟨w5, w5', e5, -, -⟩, w5'', e5', wfc5, wft5⟩
  simp only [WP.uncurry'_pair] at w5 w5' e5 w5'' e5' wfc5 wft5 ⊢
  have hS5 : SCsOK st T Ω Sg Scs Z Ac s5 := SCsOK.switch h4 hS4 hX4 hb4 w5'' e5' wfc5 wft5
  have hA5 : L.cscW s5 ∈ Ac := by
    unfold LawfulStore.cscW; rw [cscW_eq w5.1 w5.2.1, e5]; exact hB4.curA hcT ea4
  obtain ⟨ka5, kc5, -, ks5⟩ := free_keys h4 w5
  have ha5 : L.actionW s5 = 0#u64 := ka5.trans ea4
  have hcs5 : L.cscW s5 = L.mem s5 (scA (L.curW s5)) := by
    rw [kc5, ks5 (L.curW s4) hcT]; unfold LawfulStore.cscW; rw [cscW_eq w5.1 w5.2.1, e5]; rfl
  -- a node word other than `CUR_SC` keeps the current SC
  have cn : ∀ {s s' : S} {Q R} {o : U64}, SchedQueuesInv st T Cs Ω H s Q R →
      o.val < 4288 → o.val % 8 = 0 → o.val ≠ 24 →
      WritesIn st s s' (· = L.nodeAt s (L.cpu s) o) → L.cscW s' = L.cscW s := by
    intro s s' Q R o hh ho h8 h24 w
    have hN := hh.nodes _ hh.cur
    unfold LawfulStore.cscW; rw [cscW_eq w.1 w.2.1]; unfold LawfulStore.nodeA
    refine w.mem_eq (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])) ?_
    intro e; have := congrArg UScalar.val e
    rw [nodeAt_val hN (by simp [layout.node.CUR_SC]), nodeAt_val hN ho] at this
    simp [layout.node.CUR_SC] at this; omega
  obtain ⟨h5, hB5⟩ := free_step h4 hB4 w5
  have hΩ4 : ∀ n ∈ Nt, OutsideObjs st T Cs s4 (ntfnBtA n) := fun n hn => h4.omega _ (hsub4 _ (hO4.ntB n hn).2)
  have hX5 : XInv st T Cs Ω Sg Rp Scs Nt Z s5 := hX4.writes h4.tcbs w5' (fun b hb => hb) (by
    unfold LawfulStore.cscW; rw [cscW_eq w5.1 w5.2.1, e5]; exact hts)
    (hX4.tn_writes h4 w5'' (fun b hb hh => by
      rcases hh with hh | (hh | hh) | hh | hh | hh
      · exact notTmW_ring h4 hO4 hsub4 hts hb (Or.inl hh)
      · exact notTmW_ring h4 hO4 hsub4 hcs hb (Or.inl hh)
      · exact notTmW_ring h4 hO4 hsub4 hcs hb (Or.inr hh)
      · subst hh; exact notTmW_node h4.tcbs h4.nodes hΩ4 h4.cur (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM])
      · subst hh; exact notTmW_node h4.tcbs h4.nodes hΩ4 h4.cur (by simp [layout.node.CONSUMED])
          (by simp [layout.node.CONSUMED])
      · subst hh; exact notTmW_node h4.tcbs h4.nodes hΩ4 h4.cur (by simp [layout.node.CUR_SC])
          (by simp [layout.node.CUR_SC]))) (free_keys h4 w5).2.2.1
  -- a node word other than `CUR_SC` keeps `XInv`
  have xn : ∀ {s s' : S} {Q R} {o : U64}, SchedQueuesInv st T Cs Ω H s Q R → XInv st T Cs Ω Sg Rp Scs Nt Z s →
      o.val < 4288 → o.val % 8 = 0 → o.val ≠ 24 → (o.val ≠ 88 ∧ o.val ≠ 104 ∧ o.val ≠ 112) → o.val ≠ 8 →
      WritesIn st s s' (· = L.nodeAt s (L.cpu s) o) →
      XInv st T Cs Ω Sg Rp Scs Nt Z s' := by
    intro s s' Q R o hh hx ho h8 h24 hto hi8 w
    have hN := hh.nodes _ hh.cur
    refine hx.writes hh.tcbs w (fun b hb => hb ▸ not_prot_node hh hx.1 hsub4 hh.cur ho) ?_
      (hx.tn_writes hh w (fun b _ e => by
        subst e
        exact notTmW_node hh.tcbs hh.nodes (fun n hn => hh.omega _ (hsub4 _ (hx.1.ntB n hn).2)) hh.cur ho hto)) ?_
    rotate_left
    · unfold LawfulStore.idleW; rw [w.2.1, nodeAt_of_ksb w.1]
      refine w.mem_eq (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8])) ?_
      intro e; have := congrArg UScalar.val e
      rw [nodeAt_val hN (by rw [idle8]; omega), nodeAt_val hN ho, idle8] at this; omega
    unfold LawfulStore.cscW; rw [cscW_eq w.1 w.2.1]; unfold LawfulStore.nodeA
    rw [w.mem_eq (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])) ?_]
    · exact hx.2.2.cur
    · intro e; have := congrArg UScalar.val e
      rw [nodeAt_val hN (by simp [layout.node.CUR_SC]), nodeAt_val hN ho] at this
      simp [layout.node.CUR_SC] at this; omega
  step with LawfulStore.cur_cpu_spec as ⟨c, c_post⟩
  step with obj.node_get.spec as ⟨i, _⟩
  refine WP.spec_bind (Pₘ := fun r => SchedQueuesInv st T Cs Ω H r.1 Q4 R4 ∧ BoundInv st T Ac r.1 ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ L.cscW r.1 ∈ Ac ∧
      L.actionW r.1 = 0#u64 ∧ L.cscW r.1 = L.mem r.1 (scA (L.curW r.1))) ?_ ?_
  · split
    · refine WP.spec_bind (WP.spec_and (sched.set_next_interrupt.free (Ω := Ω) hA s5 a3 h5.cur (h5.nodes _ h5.cur))
        (sched.set_next_interrupt.fp hA s5 a3 (B := (· = L.nodeAt s5 (L.cpu s5) layout.node.ARMED))
          (h5.nodes _ h5.cur) rfl)) ?_
      rintro ⟨s7, a5⟩ ⟨w7, w7'⟩
      simp only [WP.uncurry'_pair] at w7 w7' ⊢
      have hX7 := xn h5 hX5 (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED])
        (by simp [layout.node.ARMED])
        (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED]) w7'
      have h7 := free_step h5 hB5 w7
      have hS7 := SCsOK.node (hi8 := by simp [layout.node.ARMED, layout.node.REPROGRAM, layout.node.IPI_PENDING, layout.node.CONSUMED]) h5 hS5 (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED])
        (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED]) w7'
      step with obj.node_set.spec as ⟨s8, s8_post⟩
      try simp only [WP.spec_ok]
      have w8 : WritesIn st s5 s8 (L.Free s5 Ω Cs) := by
        rw [s8_post, c_post]
        exact w7.free_trans (free_node_write w7.1 h5.cur (h5.nodes _ h5.cur)
          (by simp [layout.node.REPROGRAM, LowFree]))
      have w8' : WritesIn st s7 s8 (· = L.nodeAt s7 (L.cpu s7) layout.node.REPROGRAM) := by
        have hN7 : NodePlaced st T s7 (L.cpu s7) := by rw [w7.2.1]; exact (h5.nodes _ h5.cur).ksb w7.1
        rw [s8_post, c_post, ← w7.2.1]
        exact writesIn_wr (nodeAt_aligned hN7 (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
      have cs8 : L.cscW s8 = L.cscW s5 := by
        rw [cn h7.1 (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM]) w8', cn h5 (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED])
          (by simp [layout.node.ARMED]) w7']
      obtain ⟨ka8, kc8, -, ks8⟩ := free_keys h5 w8
      exact ⟨(free_step h5 hB5 w8).1, (free_step h5 hB5 w8).2,
        xn h7.1 hX7 (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) w8',
        SCsOK.node (hi8 := by simp [layout.node.ARMED, layout.node.REPROGRAM, layout.node.IPI_PENDING, layout.node.CONSUMED]) h7.1 hS7 (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) w8',
        by rw [cs8]; exact hA5, by rw [ka8]; exact ha5, by rw [cs8, kc8, ks8 (L.curW s5) h5.curT]; exact hcs5⟩
    · exact (WP.spec_ok _).2 ⟨h5, hB5, hX5, hS5, hA5, ha5, hcs5⟩
  rintro ⟨s6, a4⟩ ⟨h6, hB6, hX6, hS6, hA6, ha6, hcs6⟩
  try simp only [WP.uncurry'_pair]
  exact WP.spec_mono (WP.spec_and (smp.send_pending.free (Ω := Ω) hA s6 a4 h6.cur (h6.nodes _ h6.cur))
    (smp.send_pending.fp hA s6 a4 (B := (· = L.nodeAt s6 (L.cpu s6) layout.node.IPI_PENDING))
      (h6.nodes _ h6.cur) rfl)) fun r w => by
    obtain ⟨s', a'⟩ := r
    obtain ⟨w, w'⟩ := w
    have cs' : L.cscW s' = L.cscW s6 := cn h6 (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING])
        (by simp [layout.node.IPI_PENDING]) w'
    obtain ⟨ka', kc', -, ks'⟩ := free_keys h6 w
    exact ⟨⟨Q4, R4, (free_step h6 hB6 w).1⟩, (free_step h6 hB6 w).2,
      xn h6 hX6 (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING])
        (by simp [layout.node.IPI_PENDING])
        (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]) w',
      SCsOK.node (hi8 := by simp [layout.node.ARMED, layout.node.REPROGRAM, layout.node.IPI_PENDING, layout.node.CONSUMED]) h6 hS6 (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING])
        (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]) w',
      by rw [cs']; exact hA6, by rw [ka']; exact ha6, by rw [cs', kc', ks' (L.curW s6) h6.curT]; exact hcs6⟩

end

end Fl4Proofs.P1
