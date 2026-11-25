/-
P2 (p2j18, KWN step 10): **the executing core's action thread and idle
thread at the end of `awaken`** (the `act` and `idle` parts of `SchPre`,
premise `hE` of `AllCores.schedF`).

* `ActAff s`: an action thread has affinity the executing core.
* `ActAff.keep`, `ActAff.nT`, `fnAff` / `ffAff` (a `FootN True` footprint
  keeps every thread's `AFFINITY`; an `FFoot` keeps the `AFFINITY` of the
  threads of `Il`), `ActAff.fnT` / `ActAff.ffT` (a footprint protecting every
  thread makes no new action thread).
* `sched.enqueue.ap`, `sched.reschedule_required.ap`,
  **`sched.possible_switch_to.ap`**: `possible_switch_to` makes a thread the
  action only when its affinity is the executing core (sched.rs:369-375);
  otherwise it queues it (action kept) or asks for `CHOOSE_NEW`.
-/
import Fl4Proofs.P2.FootN9
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es U : Set U64}
variable {Kp Il Ks : Set U64}

/-- An action thread has affinity the executing core. -/
def ActAff (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) : Prop :=
  L.actionW s ∈ T → L.mem s (affA (L.actionW s)) = L.cpu s

theorem ActAff.keep {s s' : S} (ea : L.actionW s' = L.actionW s) (hc : L.cpu s' = L.cpu s)
    (haf : L.actionW s ∈ T → L.mem s' (affA (L.actionW s)) = L.mem s (affA (L.actionW s)))
    (ha : ActAff st T s) : ActAff st T s' := fun hA => by
  have hA' : L.actionW s ∈ T := by rw [← ea]; exact hA
  rw [ea, haf hA', hc]; exact ha hA'

theorem ActAff.nT {s : S} (h : L.actionW s ∉ T) : ActAff st T s := fun hA => absurd hA h

theorem actionW_set {s : S} {v : U64} (hN : NodePlaced st T s (L.cpu s)) :
    L.actionW (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) v) = v := by
  unfold LawfulStore.actionW
  rw [L.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
  exact L.mem_wr_same (act_aligned hN)

/-- A `FootN True` footprint keeps every thread's `AFFINITY`. -/
theorem fnAff {Nd' : Prop} {s s' : S} (hT : TcbPlaced T) (hNd : Nd')
    (f : FootN st Kp Nd' T Cs Sg Scs Z Es s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (affA y) = L.mem s (affA y) :=
  f.mem_eq (by rw [affA_eq]; exact field_aligned (hT y hy) (by simp) (by simp))
    (fun hb => hb.2 (Or.inr (Or.inr ⟨hNd, Or.inl ⟨y, hy, hT y hy, Or.inr rfl⟩⟩)))

/-- An `FFoot` keeps the `AFFINITY` of the threads of `Il`. -/
theorem ffAff {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s' : S}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (f : FFoot st Kp Il Ks T Cs Sg Scs Z Es U s s') {y : U64} (hy : y ∈ T) (hyI : y ∈ Il) :
    L.mem s' (affA y) = L.mem s (affA y) := by
  have hT := hq.tcbs
  refine f.mem_eq (by rw [affA_eq]; exact field_aligned (hT y hy) (by simp) (by simp)) ?_
  rintro (⟨-, hn⟩ | ⟨z, hzT, -, hzI, e | e⟩ | ⟨k, hk, -, e⟩)
  · exact hn (Or.inr (Or.inr ⟨trivial, Or.inl ⟨y, hy, hT y hy, Or.inr rfl⟩⟩))
  · rw [affA_eq, scA_eq] at e
    exact field_ne (hT y hy) (hT z hzT) (by simp) (by simp) (fun _ => by simp) e
  · have hyz : y = z := by
      have hv := congrArg UScalar.val e
      rw [affA_eq, affA_eq, field_val (hT y hy) (by simp), field_val (hT z hzT) (by simp)] at hv
      exact UScalar.eq_of_val_eq (by omega)
    exact hzI (by rw [← hyz]; exact hyI)
  · obtain ⟨-, ⟨a2, i2⟩⟩ := sclink_in hO hk
    exact out_ne_field (K := 3520#u64) (hq.omega _ (hO.scW _ hk _ a2 i2)) hy (hT y hy) (by simp)
      (by rw [← affA_eq, e])

/-- A `FootN` protecting every thread makes no new action thread. -/
theorem ActAff.fnT {s s' : S} (hT : TcbPlaced T) (f : FootN st T True T Cs Sg Scs Z Es s s')
    (ha : ActAff st T s) : ActAff st T s' := fun hA =>
  ActAff.keep (f.ac hA hA) f.2.1 (fun hA' => fnAff hT trivial f hA') ha hA

/-- An `FFoot` protecting every thread makes no new action thread. -/
theorem ActAff.ffT {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s' : S}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (f : FFoot st T T Ks T Cs Sg Scs Z Es U s s') (ha : ActAff st T s) : ActAff st T s' := fun hA =>
  ActAff.keep (f.ac hA hA) f.2.1 (fun hA' => ffAff hq hO f hA' hA') ha hA

/-- A `KeepT0` frame (action kept or `CHOOSE_NEW`, every `AFFINITY` kept). -/
theorem ActAff.keepT {t : U64} {s s' : S} (hT : TcbPlaced T) (k : KeepT0 st T Cs Rp Scs Nt t s s')
    (ha : ActAff st T s) : ActAff st T s' := by
  rcases k.act with e | e
  · refine ActAff.keep e k.cpu (fun hA => ?_) ha
    rw [affA_eq]
    exact k.fld _ hA _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  · exact ActAff.nT (by rw [e]; exact notT_small hT (by simp))

/-! ## The switch-to -/

theorem sched.enqueue.ap {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S) (t : obj.Tcb)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (ha : ActAff st T s) :
    sched.enqueue st s t ⦃ s' => ActAff st T s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  have hW : ∀ w ∈ t :: Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := by
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact (hR1.1.rel _ hp).mem w hw
  refine WP.spec_mono (sched.enqueue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (fun h0 => h.notQ ht h0 hc hp)) fun s' hh => ?_
  have ea := LawfulStore.QFoot.act h.tcbs h.nodes hW hc h.cur ht (fun o ho => by omega) hh.1
  have f : FootN st (∅ : Set U64) True T Cs (∅ : Set U64) (∅ : Set U64) (fun _ => 0) (∅ : Set U64) s s' := WritesIn.a (hh.1.mono fun b hb =>
    LawfulStore.QFoot.kwN h.tcbs h.nodes hW hc h.cur ht (fun o ho => by omega) (fun o ho => idOff_ge (by omega))
      (Set.notMem_empty _) hb) (AcK.of_eq ea)
  exact ActAff.keep ea f.2.1 (fun hA => fnAff h.tcbs trivial f hA) ha

theorem sched.reschedule_required.ap {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) :
    sched.reschedule_required st s ⦃ s' => ActAff st T s' ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  have hpart : (if (act != sched.ACTION_RESUME_CURRENT) = true then
      if (act != sched.ACTION_CHOOSE_NEW) = true then do
        let b ← sched.is_schedulable st s act
        if b = true then sched.enqueue st s act else ok s
      else ok s
    else ok s) ⦃ s1 => FootN st (∅ : Set U64) True T Cs (∅ : Set U64) (∅ : Set U64) (fun _ => 0) (∅ : Set U64) s s1 ⦄ := by
    split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · exact sched.enqueue.kwN s act h hT (Set.notMem_empty _)
        · exact (WP.spec_ok _).2 (FootN.refl _)
      · exact (WP.spec_ok _).2 (FootN.refl _)
    · exact (WP.spec_ok _).2 (FootN.refl _)
  refine WP.spec_bind hpart fun s1 f1 => ?_
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [f1.2.1]; exact (h.nodes _ h.cur).ksb f1.1
  refine WP.spec_mono (sched.set_action.spec s1 _) fun s2 e2 => ?_
  subst e2
  exact ActAff.nT (by rw [actionW_set hN1, choose_val]; exact notT_small h.tcbs (by simp))

/-- **`possible_switch_to` makes only a thread of the executing core the
action** (sched.rs:369-375). -/
theorem sched.possible_switch_to.ap {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S)
    (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (ha : ActAff st T s) :
    sched.possible_switch_to st s t ⦃ s' => ActAff st T s' ⦄ := by
  unfold sched.possible_switch_to
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  split
  · exact (WP.spec_ok _).2 ha
  step with sched.in_release_queue.spec as ⟨b, b_post⟩
  split
  · exact (WP.spec_ok _).2 ha
  unfold sched.cur_domain
  step with obj.ks_get.spec as ⟨i1, _⟩
  step with obj.Tcb.domain.spec as ⟨i2, _⟩
  split
  · exact sched.enqueue.ap s t h ht ha
  step with obj.Tcb.affinity.spec as ⟨i3, i3_post⟩
  step with LawfulStore.cur_cpu_spec as ⟨i4, i4_post⟩
  split
  · exact sched.enqueue.ap s t h ht ha
  rename_i haff
  have hat : L.mem s (affA t) = L.cpu s := by
    rw [← i3_post, ← i4_post]; exact UScalar.eq_of_val_eq (by simpa using haff)
  step with sched.action.spec as ⟨i5, _⟩
  split
  · refine WP.spec_bind (WP.spec_and (sched.reschedule_required.inv s Q R h) (sched.reschedule_required.ap s h)) ?_
    rintro s1 ⟨⟨⟨Q1, h1⟩, -, -⟩, a1⟩
    exact sched.enqueue.ap s1 t h1 ht a1
  · refine WP.spec_mono (sched.set_action.spec s _) fun s' e => ?_
    subst e
    have hN := h.nodes _ h.cur
    intro hA
    rw [actionW_set hN] at hA ⊢
    rw [L.cpu_wr]
    have := node_fld (v := t) hN (o := layout.node.SCHED_ACTION) (by rw [act_val]; omega) (by rw [act_val]) h.tcbs ht
      (K := 3520#u64) (by simp) (by simp)
    rw [← affA_eq] at this
    rw [this]; exact hat


/-! ## The donation, the signal tails, the VMEnter completion -/

/-- `maybe_donate_sched_context` keeps `ActAff`: the donation writes the
`AFFINITY` of the woken thread only, which is not the action thread. -/
theorem notification.maybe_donate_sched_context.ap {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hta' : L.actionW s ≠ t) (hti : L.idleW s ≠ t)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac))
    (ha : ActAff st T s) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => ActAff st T s' ⦄ := by
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => ActAff st T s' ⦄ := (WP.spec_ok _).2 ha
  unfold notification.maybe_donate_sched_context
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  split
  · rename_i hi
    step with obj.Ntfn.sc.val as ⟨i1, ei1⟩
    step with obj.Sc.is_null.spec as ⟨b, eb⟩
    split
    · exact ok0
    rename_i hb
    have hi10 : i1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    step with obj.Sc.tcb.spec as ⟨i2, ei2⟩
    split
    · rename_i hi2
      have htc0 : L.mem s (scTcbA i1) = 0#u64 := by rw [← ei2, hi2]
      obtain ⟨hS1, hcore1, hin1⟩ := hns (by rw [← ei1]; exact hi10) (by rw [← ei1]; exact htc0) (by rw [← ei, hi])
      rw [← ei1] at hS1 hin1 hcore1
      refine WP.spec_bind (WP.spec_and (schedcontext.donate.unbound hA s a i1 t Q R h hB hX hS hSg ht htq htr hS1
        hi10 htc0 hcore1 hin1 (by rw [← ei, hi]) hti)
        (schedcontext.donate.ff (Kp := (∅ : Set U64)) (Il := {y | y ≠ t}) (Ks := (∅ : Set U64))
          (Es := (∅ : Set U64)) (U := (∅ : Set U64)) hA s a i1 t h hX.dbg hX.1
          hSg.sub hS1 ht hcore1 htc0 (Set.notMem_empty _) (fun e => e rfl) (Set.notMem_empty _))) ?_
      rintro ⟨s4, a4⟩ ⟨⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, -, -, -, sc4, tc4, ea4⟩, f4⟩
      try simp only [WP.uncurry'_pair]
      have ha4 : ActAff st T s4 := ActAff.keep ea4 f4.2.1 (fun hA' => ffAff h hX.1 f4 hA' hta') ha
      have hsc : i1 ≠ 0#u64 → L.mem s4 (scTcbA i1) ≠ 0#u64 →
          L.mem s4 (scTcbA i1) ∈ T ∧ OutsideObjs st T Cs s4 (scCoreA i1) ∧ L.mem s4 (scCoreA i1) ∈ Cs ∧
            L.mem s4 (scTcbA i1) ∉ (∅ : Set U64) := fun _ _ => by
        obtain ⟨-, -, hc4⟩ := hX4.2.2.bound t ht (by rw [sc4]; exact hi10)
        rw [sc4] at hc4
        rw [tc4]
        exact ⟨ht, h4.omega _ ((objs_omega hX4.1 hSg4.sub).2 i1 hS1).2.1, hc4, Set.notMem_empty _⟩
      have hsc' : i1 ≠ 0#u64 → L.mem s4 (scTcbA i1) ≠ 0#u64 →
          L.mem s4 (scTcbA i1) ∈ T ∧ OutsideObjs st T Cs s4 (scCoreA i1) ∧ L.mem s4 (scCoreA i1) ∈ Cs ∧
            L.actionW s4 ≠ L.mem s4 (scTcbA i1) := fun a b => by
        obtain ⟨x1, x2, x3, -⟩ := hsc a b
        exact ⟨x1, x2, x3, by rw [ea4, tc4]; exact hta'⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_mono (WP.spec_and (schedcontext.resume.allF hA s4 a4 i1 Q4 R4 h4 hB4 hX4 hSg4 hS4 hsc')
        (schedcontext.resume.kwN (Sg := Sg) (Kp := (∅ : Set U64)) (Nd := True) (Scs := Scs) (Z := Z)
          (Es := (∅ : Set U64)) hA s4 a4 i1 Q4 R4 h4 hsc)) ?_
      rintro ⟨s5, a5⟩ ⟨⟨Q5, R5, h5, hB5, hX5, hSg5, f5, ea5, -, -⟩, k5⟩
      exact ActAff.keep ea5 k5.2.1 (fun hA' => fnAff h4.tcbs trivial k5 hA') ha4
    · exact ok0
  · exact ok0

theorem notification.maybe_donate_sched_context.apB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac))
    (ha : ActAff st T s) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => ActAff st T s' ⦄ := by
  by_cases h0 : L.mem s (scA t) = 0#u64
  · refine notification.maybe_donate_sched_context.ap hA s a t n Q R h hB hX hS hSg ht ?_ ?_ ?_ ?_ hns ha
    · by_contra hq; exact hB.q t ht hq h0
    · by_contra hq; exact hB.r t ht hq h0
    · intro e; exact hB.act (by rw [e]; exact ht) (by rw [e]; exact h0)
    · intro e; exact hB.idle (by rw [e]; exact h0)
  · unfold notification.maybe_donate_sched_context
    step with obj.Tcb.sc.spec as ⟨i, ei⟩
    rw [if_neg (by rw [ei]; exact h0)]
    exact (WP.spec_ok _).2 ha

/-- `signal_tail` keeps `ActAff`. -/
theorem signal_tail.ap {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s2 : S) (a1 : A)
    (dst n badge : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h2 : SchedQueuesInv st T Cs Ω H s2 Q R) (hB2 : BoundInv st T Ac s2) (hX2 : XInv st T Cs Ω Sg Rp Scs Nt Z s2)
    (hS2 : SCsOK st T Ω Sg Scs Z Ac s2) (hSg2 : SgOK st Ω Sg s2) (hd : dst ∈ T) (hn : n ∈ Nt)
    (dq : (L.mem s2 (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (dr : (L.mem s2 (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (da : L.actionW s2 ≠ dst) (di : L.idleW s2 ≠ dst) (dR : ¬ BlockedR (L.mem s2 (stA dst)))
    (ha : ActAff st T s2) :
    (do
      let s3 ← obj.Tcb.set_reg st dst s2 layout.reg.BADGE badge
      let (s4, a2) ← notification.maybe_donate_sched_context st ar s3 a1 dst n
      let b1 ← sched.is_schedulable st s4 dst
      let s5 ← if b1 then sched.possible_switch_to st s4 dst else ok s4
      let s6 ← notification.unblock_sporadic st s5 dst
      ok (s6, a2)) ⦃ s' _ => ActAff st T s' ⦄ := by
  have hT := h2.tcbs
  have hta := hT dst hd
  refine WP.spec_bind (obj.Tcb.set_reg.badge s2 dst badge hta) fun s3 e3 => ?_
  subst e3
  obtain ⟨h3, hB3, hX3, hS3, hSg3⟩ := badge_all (v := badge) h2 hB2 hX2 hS2 hSg2 hd
  have F3 : FootN st T True T Cs Sg Scs Z (∅ : Set U64) s2 (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) :=
    footN_field hT h2.nodes h2.cur hd (by simp) (by simp) (by simp) (by simp)
  have ha3 := ActAff.fnT hT F3 ha
  have iq3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (inqA dst) = L.mem s2 (inqA dst) := by
    rw [inqA_eq]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp)) (field_aligned hta (by simp) (by simp))
      (fun e => field_ne (K1 := 256#u64) (K2 := 3592#u64) hta hta (by simp) (by simp) (fun _ => by simp)
        (UScalar.eq_of_val_eq e))
  have ea3 : L.actionW (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) = L.actionW s2 :=
    act_wr_field (h2.nodes _ h2.cur) hd hta rfl (by simp) (by simp)
  have ei3 : L.idleW (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) = L.idleW s2 := by
    unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp))
      (nodeAt_aligned (h2.nodes _ h2.cur) (by rw [idle8]; omega) (by rw [idle8]))
      (fun e => node_ne_field (K := 256#u64) (h2.nodes _ h2.cur) (by rw [idle8]; omega) hd hta (by simp)
        (UScalar.eq_of_val_eq e).symm)
  have sc3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (scA dst) = L.mem s2 (scA dst) := by
    rw [scA_eq]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp)) (field_aligned hta (by simp) (by simp))
      (fun e => field_ne (K1 := 256#u64) (K2 := 3464#u64) hta hta (by simp) (by simp) (fun _ => by simp)
        (UScalar.eq_of_val_eq e))
  have hsA3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (scA dst) = 0#u64 →
      ¬ Sch st (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) dst := fun h0 hS => by
    rw [sc3] at h0
    rcases Sch.wr_field h2 hd (by simp) (by simp) (by simp) hd hS with e | e | e | e | ⟨e1, e2⟩ | e
    · exact e dq
    · exact e dr
    · exact da e
    · exact di e
    · exact hB2.resume e1 (by rw [e2]; exact h0)
    · exact dR e
  refine WP.spec_bind (WP.spec_and (notification.maybe_donate_sched_context.ff (Kp := (∅ : Set U64))
    (Il := (∅ : Set U64)) (Ks := (∅ : Set U64)) (Es := (∅ : Set U64)) (U := (∅ : Set U64)) hA _ a1 dst n Q R
    h3 hB3 hX3 hS3 hSg3 hd (by rw [iq3]; exact dq) (by rw [iq3]; exact dr) (by rw [ea3]; exact da)
    (by rw [ei3]; exact di) (ntfn_sc_ok hX3 hn hsA3) (Set.notMem_empty _) (Set.notMem_empty _)
    (fun k hk => absurd hk (Set.notMem_empty _)))
    (notification.maybe_donate_sched_context.ap hA _ a1 dst n Q R h3 hB3 hX3 hS3 hSg3 hd
      (by rw [iq3]; exact dq) (by rw [iq3]; exact dr) (by rw [ea3]; exact da)
      (by rw [ei3]; exact di) (ntfn_sc_ok hX3 hn hsA3) ha3)) ?_
  rintro ⟨s4, a2⟩ ⟨⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, -⟩, ha4⟩
  try simp only [WP.uncurry'_pair]
  step with sched.is_schedulable.spec' as ⟨b1, hb1⟩
  refine WP.spec_bind (Pₘ := fun s5 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s5 ∧ ActAff st T s5) ?_ ?_
  · split
    · rename_i hb
      refine WP.spec_mono (WP.spec_and (sched.possible_switch_to.sch s4 dst Q4 R4 h4 hB4 hSg4 hd (hb1 hb).1
        (fun _ => (hS4.act _ (hX4.2.2.bound dst hd (hb1 hb).2.1).1).2 (hb1 hb).2.2.2))
        (sched.possible_switch_to.ap s4 dst h4 hd ha4)) fun s5 hh => ?_
      obtain ⟨⟨p5, -, -⟩, k5⟩ := hh
      exact ⟨⟨p5.inv, p5.bnd, hX4.fr p5.fr, hS4.fr p5.fr, hSg4.fr p5.fr⟩, k5⟩
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, ha4⟩
  rintro s5 ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS5, hSg5⟩, ha5⟩
  refine WP.spec_bind (endpoint.unblock_sporadic.kwN (Sg := Sg) (Kp := T) (Nd := True) (Scs := Scs) (Z := Z)
    (Es := (∅ : Set U64)) s5 dst h5 hX5 hS5 hd) ?_
  intro s6 F6
  exact (WP.spec_ok _).2 (ActAff.fnT h5.tcbs F6 ha5)

/-- `vcpu.report` keeps `ActAff`: its writes are the thread's registers and
the user words, then the thread's `STATE` (and possibly `CHOOSE_NEW`). -/
theorem vcpu.report.ap {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t badge : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hvm : L.mem s (stA t) = sched.TS_RUNNING_VM)
    (hc : L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add t 3664#u64)) vcpu.PENDING) = 0#u64)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hbuf : msg.lookup_ipc_buffer st s true t ⦃ b => BufOK U b ⦄)
    (ha : ActAff st T s) :
    vcpu.report st ar s a t badge ⦃ s' => ActAff st T s' ⦄ := by
  have h0 := h
  obtain ⟨⟨Q, R, hq⟩, -, hX, -, -⟩ := h0
  refine WP.spec_mono (vcpu.report.xf hA s a t badge h ht hvm hc hU hbuf) ?_
  rintro s' ⟨s1, h1, -, w1, e⟩
  have ha1 : ActAff st T s1 := ActAff.ffT hq hX.1
    (RepW.ff (Kp := T) (Il := T) (Ks := (∅ : Set U64)) (Es := (∅ : Set U64)) (U := U) hq hX.1 ht hU w1) ha
  obtain ⟨⟨Q1, R1, hq1⟩, -, -, -, -⟩ := h1
  have K2 := sched.set_thread_state.w2 s1 t sched.TS_RUNNING hq1.tcbs (hq1.nodes _ hq1.cur) ht
  rw [e, WP.spec_ok] at K2
  obtain ⟨w2, ea2, -⟩ := K2
  rcases ea2 with ea2 | ea2
  · refine ActAff.keep ea2 w2.2.1 (fun hA' => ?_) ha1
    rw [affA_eq]
    refine w2.mem_eq (field_aligned (hq1.tcbs _ hA') (by simp) (by simp)) ?_
    rintro (e' | e')
    · rw [stA_eq] at e'
      exact field_ne (hq1.tcbs _ hA') (hq1.tcbs t ht) (by simp) (by simp) (fun _ => by simp) e'
    · exact node_ne_field (hq1.nodes _ hq1.cur) (by rw [act_val]; omega) hA' (hq1.tcbs _ hA') (by simp) e'.symm
  · exact ActAff.nT (by rw [ea2, choose_val]; exact notT_small hq1.tcbs (by simp))

end

end Fl4Proofs.P2.Stall
