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
* `maybe_donate_sched_context.ap`/`.apB`, `signal_tail.ap`, `vcpu.report.ap`,
  `signal_vm.ap`, `send_signal.ap`, `timer.fire_loop.ap`, `timer.fire.ap`,
  `awaken_loop.ap`: every piece of `awaken` keeps `ActAff` (a donation writes
  the `AFFINITY` of the woken thread only, never the action thread; the
  `KeepT` frames of `cancel_ipc`/`set_thread_state` set the action to
  `CHOOSE_NEW` at most).
* **`sched.awaken.ap`**: `ActAff` and `IdleAff` at the end of `awaken`
  (the idle thread's affinity: `fire` is an `FKI` step, whose `OKeep2.iaf`
  keeps every idle thread's `AFFINITY`; the release loop is an `SFootN` one).
* **`AllCores.schedE`**: `AllCores.schedF` with `SchPre`'s `act` and `idle`
  parts discharged. Entry end facts (as `kb`): `hao`, `hcK`, `hidl`, and
  `hsa` (`ActAff` at the body's end).

Named premises of `AllCores.schedE`: `hR` [J] (the `res` part of `SchPre`:
with action `RESUME` at the end of `awaken` the current thread is
`SchCur`), `hS0` [W].

**Finding (p2j18): `hR` does not follow from P1 without a domain invariant.**
Counterexample shape: the body ends with action `RESUME` and a current thread
`c` (affinity the executing core, `SchCur`) whose `DOMAIN` word differs from
`CUR_DOMAIN`, and either (a) `c` is `TS_RUNNING_VM` and schedulable, and a
timer fires on its bound notification (`send_signal` → `signal_completes` →
`vcpu.report`, `RUNNING`), or (b) `c` is the head of the executing core's
release queue and ready. Then `possible_switch_to c` takes the domain-mismatch
branch (sched.rs:369) and `enqueue`s `c` while the action stays `RESUME`, so
`schedule` resumes a queued current thread (`SchCur.nq` fails). In the kernel
every domain is 0 (`NUM_DOMAINS = 1`: `set_domain` rejects `dom ≥ 1`,
`create_object` copies `CUR_DOMAIN`, boot sets 0), but P1 has no invariant on
the `DOMAIN` words. With "every TCB's `DOMAIN` equals `CUR_DOMAIN`" (seL4
`ct_in_cur_domain`-like) at the body's end, framed through `awaken` (its
writes never touch a `DOMAIN` word nor `CUR_DOMAIN`), `hR` follows from
`SchCur` at the body's end when the action is `RESUME`: woken threads are
blocked hence not current; the cases (a)/(b) then make `c` the action.
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

/-- `signal_vm` keeps `ActAff`. -/
theorem signal_vm.ap {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a : A) (i n : U64)
    (h1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hiT : i ∈ T) (hn : n ∈ Nt)
    (st1 : L.mem s1 (stA i) = sched.TS_RUNNING) (ha : ActAff st T s1) :
    (do
      let (s2, a1) ← notification.maybe_donate_sched_context st ar s1 a i n
      let b2 ← sched.is_schedulable st s2 i
      let s3 ← if b2 = true then sched.possible_switch_to st s2 i else ok s2
      let i4 ← obj.Tcb.sc st i s3
      let b3 ← obj.Sc.is_null i4
      if b3 = true then ok (s3, a1)
      else do
        let b4 ← sporadic.sc_active st s3 i4
        if b4 = true then do
          let i5 ← obj.Ntfn.sc st n s3
          if i4 = i5 then do
            let b5 ← sporadic.sc_sporadic st s3 i4
            if b5 = true then do
              let s4 ← sched.cur_sc st s3
              let b6 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i4 s4
              if b6 = true then do
                let s5 ← sporadic.unblock_check st s3 i4
                ok (s5, a1)
              else ok (s3, a1)
            else ok (s3, a1)
          else ok (s3, a1)
        else ok (s3, a1)) ⦃ s' _ => ActAff st T s' ⦄ := by
  obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
  have hsA1 : L.mem s1 (scA i) = 0#u64 → ¬ Sch st s1 i := fun h0 hS => by
    rcases hS with e | e | e | e | ⟨e1, e2⟩ | e
    · exact hB1.q i hiT e h0
    · exact hB1.r i hiT e h0
    · exact hB1.act (by rw [e]; exact hiT) (by rw [e]; exact h0)
    · exact hB1.idle (by rw [e]; exact h0)
    · exact hB1.resume e1 (by rw [e2]; exact h0)
    · rw [st1] at e
      rcases e with e | e
      · exact not_blocked_running e
      · exact running_ne.1 e
  refine WP.spec_bind (WP.spec_and (notification.maybe_donate_sched_context.ffB (Kp := (∅ : Set U64))
    (Il := (∅ : Set U64)) (Ks := (∅ : Set U64)) (Es := (∅ : Set U64)) (U := (∅ : Set U64)) hA s1 a i n Q1 R1 q1
    hB1 hX1 hS1 hSg1 hiT (ntfn_sc_ok hX1 hn hsA1) (Set.notMem_empty _) (Set.notMem_empty _)
    (fun k hk => absurd hk (Set.notMem_empty _)))
    (notification.maybe_donate_sched_context.apB hA s1 a i n Q1 R1 q1 hB1 hX1 hS1 hSg1 hiT
      (ntfn_sc_ok hX1 hn hsA1) ha)) ?_
  rintro ⟨s2, a1⟩ ⟨⟨⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩, -⟩, ha2⟩
  try simp only [WP.uncurry'_pair]
  step with sched.is_schedulable.spec' as ⟨b2, hb2⟩
  refine WP.spec_bind (Pₘ := fun s3 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ ActAff st T s3) ?_ ?_
  · split
    · rename_i hb
      refine WP.spec_mono (WP.spec_and (sched.possible_switch_to.sch s2 i Q2 R2 q2 hB2 hSg2 hiT (hb2 hb).1
        (fun _ => (hS2.act _ (hX2.2.2.bound i hiT (hb2 hb).2.1).1).2 (hb2 hb).2.2.2))
        (sched.possible_switch_to.ap s2 i q2 hiT ha2)) fun s3 hh => ?_
      obtain ⟨⟨p3, -, -⟩, k3⟩ := hh
      exact ⟨⟨p3.inv, p3.bnd, hX2.fr p3.fr, hS2.fr p3.fr, hSg2.fr p3.fr⟩, k3⟩
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩, ha2⟩
  rintro s3 ⟨⟨⟨Q3, R3, q3⟩, hB3, hX3, hS3, hSg3⟩, ha3⟩
  have ok3 : (ok (s3, a1) : Result (S × A)) ⦃ s' _ => ActAff st T s' ⦄ := (WP.spec_ok _).2 ha3
  step with obj.Tcb.sc.spec as ⟨i4, ei4⟩
  step with obj.Sc.is_null.spec as ⟨b3, _hb3⟩
  refine sig_if _ _ _ _ (fun _ => ok3) (fun _ => ?_)
  refine WP.spec_bind (sporadic.sc_active.spec s3 i4) fun b4 _ => ?_
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  refine WP.spec_bind (obj.Ntfn.sc.any s3 n) fun i5 _ => ?_
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  step with sporadic.sc_sporadic.spec as ⟨b5, eb5⟩
  refine sig_if _ _ _ _ (fun hb5 => ?_) (fun _ => ok3)
  step with sched.cur_sc.spec as ⟨c4, _⟩
  step with sc_ne.spec as ⟨b6⟩
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  have hi4S : i4 ∈ Scs := (hX3.2.2.bound i hiT (by rw [← ei4]; exact (eb5 hb5).1)).1 |> fun h => by
    rw [← ei4] at h; exact h
  have hiA : i4 ∈ Ac := hS3.spor i4 hi4S (eb5 hb5).2
  have hW : RefillsWF st s3 i4 (Z i4) := hS3.wf hi4S hiA
  have hSCin : SCin st s3 Ω i4 (Z i4) := ⟨hW, hX3.1.scW i4 hi4S⟩
  have hN' := q3.nodes _ q3.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have aR : Aligned (L.nodeA s3 layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
  have oR : Outside (L.nodeA s3 layout.node.REPROGRAM) i4 (Z i4) :=
    hSCin.node_out q3.omega q3.cur hN' (by rw [rp]; omega) (by rw [rp])
  refine WP.spec_bind (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s5 w5 => ?_
  have hact : L.actionW s5 = L.actionW s3 := by
    refine actionW_of w5 hN' ?_
    rintro (hr | e)
    · exact notAct_omega q3 (hX3.1.scW i4 hi4S _ (act_aligned hN') hr.inSC)
    · exact notAct_node hN' hN' (by rw [rp]; omega) (by rw [rp]; omega) e
  have F5 : FootN st T True T Cs Sg Scs Z (∅ : Set U64) s3 s5 := by
    refine FootN.of' w5 (fun b hb hh => ?_) (AcK.of_eq hact)
    rcases hh with hr | rfl
    · exact ⟨InRing.kw hi4S hr, notIdW_ring q3 hX3 hi4S hb hr⟩
    · exact ⟨kw_node q3.cur (by rw [rp]; omega) (by rw [rp]; omega),
        notIdW_node q3.nodes q3.cur (by rw [rp]; omega)
          (idOff_cur (by rw [rp]; omega) (by rw [rp]; omega) (fun _ => by rw [rp]; omega))⟩
  exact (WP.spec_ok _).2 (ActAff.fnT q3.tcbs F5 ha3)

/-- **`send_signal` keeps `ActAff`.** -/
theorem notification.send_signal.ap {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n badge : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt)
    (hH : H n = some .ntfn) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄) (ha : ActAff st T s) :
    notification.send_signal st ar s a n badge ⦃ s' _ => ActAff st T s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hNb := hX.2.2.ntb
  have hT := h0.tcbs
  have hb0 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩
  have saK : notification.set_active st s n badge ⦃ s' => ActAff st T s' ⦄ :=
    WP.spec_mono (notification.set_active.fn (Kp := T) (Nd := True) s n badge h0 hX hSg hn hH)
      fun s' f => ActAff.fnT hT f ha
  unfold notification.send_signal
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  refine sig_if _ _ _ _ (fun hidl => ?_) (fun hnidl => ?_)
  · -- an idle notification
    step with obj.Ntfn.bound_tcb.val as ⟨i, ei⟩
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    have OLD : (do
        let s1 ← notification.set_active st s n badge
        if b = true then ok (s1, a)
        else do
          let i2 ← obj.Tcb.state st i s1
          if i2 = sched.TS_RUNNING_VM then notification.kick_guest st ar s1 a i else ok (s1, a))
        ⦃ s' _ => ActAff st T s' ⦄ := by
      refine WP.spec_bind saK fun s1 k1 => ?_
      refine sig_if _ _ _ _ (fun _ => (WP.spec_ok _).2 k1) (fun _ => ?_)
      step with obj.Tcb.state.spec
      refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => (WP.spec_ok _).2 k1)
      refine WP.spec_mono (notification.kick_guest.same hA s1 a i) fun r hr => ?_
      obtain ⟨s', a'⟩ := r
      simp only at hr
      subst hr
      exact k1
    by_cases hb : b = true
    · rw [if_pos hb, if_pos hb]
      refine WP.spec_bind saK fun s1 k1 => ?_
      rw [if_pos hb]
      exact (WP.spec_ok _).2 k1
    rw [if_neg hb]
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    have hiT : i ∈ T := by
      rcases hNb n hn with e | e
      · rw [← ei] at e; exact absurd e hi0
      · rw [← ei] at e; exact e
    have hta := hT i hiT
    step with obj.Tcb.state.spec as ⟨i1, ei1⟩
    refine sig_if _ _ _ _ (fun hrecv => ?_) (fun hnrecv => ?_)
    · have hst : L.mem s (stA i) = sched.TS_BLOCKED_ON_RECV := by rw [← ei1, hrecv]
      have hbl : Blocked (L.mem s (stA i)) := by rw [hst]; exact Or.inr (Or.inl rfl)
      obtain ⟨dq, dr, da⟩ := blocked_out h0 hiT (not_runnable_of_blocked hbl)
      refine WP.spec_bind (ipc.cancel_ipc.all s a i Q R h0 hiT hB hX hSg.sub) ?_
      rintro ⟨s1, a1⟩ ⟨h1, hB1, hX1, nb1, nr1, -, k1, -⟩
      try simp only [WP.uncurry'_pair]
      have ha1 : ActAff st T s1 := ActAff.keepT hT k1.toKeepT0 ha
      have hS1 := hS.keepT hX k1
      have hSg1 : SgOK st Ω Sg s1 := ⟨hSg.sub, fun b hb => by rw [k1.ksb]; exact hSg.ks b hb,
        fun o h1' h2' => by rw [k1.ksb]; exact hSg.ksΩ o h1' h2'⟩
      have dq1 : (L.mem s1 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by rw [k1.inqf hiT]; exact dq
      have dr1 : (L.mem s1 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by rw [k1.inqf hiT]; exact dr
      have da1 : L.actionW s1 ≠ i := by
        rcases k1.act with e | e
        · rw [e]; exact da
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hiT)
      refine WP.spec_bind (sts_all s1 i _ Q R h1 hB1 hX1 hS1 hSg1 hiT not_blocked_running running_ne
        (Or.inr nb1) (hX1.noref hta nr1 (fun e => nb1 (by rw [e]; exact Or.inr (Or.inl rfl))))
        ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩) ?_
      rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩
      have ha2 : ActAff st T s2 := ActAff.keepT hT k2.toKeepT0 ha1
      have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr
      have dq2 : (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by rw [k2.inqf hiT]; exact dq1
      have dr2 : (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by rw [k2.inqf hiT]; exact dr1
      have da2 : L.actionW s2 ≠ i := by
        rcases k2.act with e | e
        · rw [e]; exact da1
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hiT)
      exact signal_tail.ap hA s2 a1 i n badge Q R h2' hB2 hX2 hS2 hSg2 hiT hn dq2 dr2 da2
        (fun e => hB.idleNB (by rw [← k1.idleW, ← k2.idleW, e]; exact Or.inl hbl))
        (by rw [st2]; rintro (hb | hb); exact not_blocked_running hb; exact running_ne.1 hb) ha2
    · -- not receiving: the `RunningVM` completion, else active (and kicked)
      rw [if_neg hb]
      refine sig_if _ _ _ _ (fun hvm => ?_) (fun _ => OLD)
      refine WP.spec_bind (vcpu.signal_completes.blk s i) ?_
      rintro b1 hb1
      refine sig_if _ _ _ _ (fun hb1t => ?_) (fun _ => OLD)
      have hvmS : L.mem s (stA i) = sched.TS_RUNNING_VM := by rw [← ei1]; exact hvm
      refine WP.spec_bind (WP.spec_and (vcpu.report.blk hA s a i badge hb0 hiT hvmS (hb1 hb1t) hU (hbuf i hiT))
        (vcpu.report.ap hA s a i badge hb0 hiT hvmS (hb1 hb1t) hU (hbuf i hiT) ha)) ?_
      rintro s1 ⟨⟨h1, st1⟩, ha1⟩
      exact signal_vm.ap hA s1 a i n h1 hiT hn st1 ha1
  · split
    · -- a waiting notification
      rename_i hwait
      have hst1 : L.epState s n = 1#u64 := by rw [← hv, hwait]; unfold obj.NTFN_WAITING; rfl
      obtain ⟨hdT, hbe, hds⟩ := ntfn_head h0 hH hst1
      step with notification.get_queue.spec as ⟨q, eq⟩
      subst eq
      set hd := (L.epQ s n).head with hhd
      have hta := hT hd hdT
      have hbl : Blocked (L.mem s (stA hd)) := by rw [hds]; exact Or.inr (Or.inr rfl)
      obtain ⟨dq, dr, da⟩ := blocked_out h0 hdT (not_runnable_of_blocked hbl)
      have hinv := notification.ntfn_dequeue.inv s hd Q R h0 hdT (by simp) hbl
      rw [hbe] at hinv
      refine WP.spec_bind hinv ?_
      rintro s1 ⟨h1, f1, o1, n1, k1, hcp1, nc1⟩
      have tm1 : TmFr st T Cs Nt s s1 := TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
        fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
      obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
      have ha1 : ActAff st T s1 := ActAff.keep ea1 hcp1 (fun hA' => by
        rw [affA_eq]; exact f1 _ hA' _ (by simp) (by simp) (by simp) (by simp)) ha
      have st1 : L.mem s1 (stA hd) = sched.TS_BLOCKED_ON_NTFN := by
        rw [stA_eq, f1 hd hdT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hds
      have iq1 : L.mem s1 (inqA hd) = L.mem s (inqA hd) := by
        rw [inqA_eq]; exact f1 hd hdT _ (by simp) (by simp) (by simp) (by simp)
      obtain ⟨-, -, r3, -, r6⟩ := ts_vals
      refine WP.spec_bind (sts_all s1 hd _ Q R h1 hB1 hX1 hS1 hSg1 hdT not_blocked_running running_ne
        (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [st1]; exact blocked_ne_reply (Or.inr (Or.inr rfl)))
          (by rw [st1, r3, r6]; decide))
        ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩) ?_
      rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩
      have ha2 : ActAff st T s2 := ActAff.keepT hT k2.toKeepT0 ha1
      have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr'
      have dq2 : (L.mem s2 (inqA hd) &&& sched.Q_QUEUED) = 0#u64 := by rw [k2.inqf hdT, iq1]; exact dq
      have dr2 : (L.mem s2 (inqA hd) &&& sched.Q_RELEASE) = 0#u64 := by rw [k2.inqf hdT, iq1]; exact dr
      have da2 : L.actionW s2 ≠ hd := by
        rcases k2.act with e | e
        · rw [e, ea1]; exact da
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hdT)
      exact signal_tail.ap hA s2 a hd n badge Q R h2' hB2 hX2 hS2 hSg2 hdT hn dq2 dr2 da2
        (fun e => hB.idleNB (by rw [← ei1, ← k2.idleW, e]; exact Or.inl hbl))
        (by rw [st2]; rintro (hb | hb); exact not_blocked_running hb; exact running_ne.1 hb) ha2
    · -- an active notification
      step with obj.Ntfn.badge.val as ⟨i, ei⟩
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_bind (obj.Ntfn.set_badge.wr s n _) fun s1 e1 => ?_
      subst e1
      exact (WP.spec_ok _).2 (ActAff.fnT hT (ntfn_bd.fn (Kp := T) (Nd := True) (Sg := Sg)
        (Scs := Scs) (Z := Z) (Es := (∅ : Set U64)) n _ h0.nodes h0.cur hX.1 hn
        (h0.omega _ (hSg.sub _ (hX.1.ntB n hn).1))) ha)

/-! ## `timer::fire`, the release loop, `awaken` -/

theorem timer.fire_loop.ap {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (now i : U64)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) (ha : ActAff st T s) :
    timer.fire_loop st ar s a now i ⦃ s' _ => ActAff st T s' ⦄ := by
  obtain ⟨IKr, IKs, IKp⟩ := IK T Cs Ω H Sg Rp Scs Nt Z Ac U
  unfold timer.fire_loop
  refine WP.spec_mono (P₀ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
    FootDU st T Cs Sg Scs Z (EH H) U s r.1 ∧ IbFr (L := L) T s r.1 ∧ ActAff st T r.1) ?_
      fun r hr => by obtain ⟨s', a'⟩ := r; exact hr.2.2.2
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ FootDU st T Cs Sg Scs Z (EH H) U s x.1 ∧
      IbFr (L := L) T s x.1 ∧ ActAff st T x.1)
  · rintro ⟨s1, a1, i1⟩ ⟨h1, F1, f1, K1⟩
    simp only at h1 F1 f1 K1
    unfold timer.fire_loop.body
    dsimp only
    split
    · rename_i hi
      have hi32 : i1.val < 32 := by simpa using hi
      step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_get.spec as ⟨t, et⟩
      step with obj.Tcb.is_null.spec as ⟨b, eb⟩
      split
      · exact (WP.spec_ok _).2 ⟨h1, F1, f1, K1⟩
      rename_i hb
      have ht0 : t ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
      have hI1 := h1
      obtain ⟨⟨Q1, R1, h1q⟩, -, hX1, -, -⟩ := h1
      have hTm1 := hX1.2.2.tm
      have htT : t ∈ T := by
        have := hTm1.min _ h1q.cur
        rw [← ec] at this; rw [← et] at this
        rcases this with e | e
        · exact absurd e ht0
        · exact e
      step with obj.Tcb.timer_deadline.val as ⟨d, ed⟩
      split
      · exact (WP.spec_ok _).2 ⟨hI1, F1, f1, K1⟩
      step with obj.Tcb.timer_badge.val as ⟨bd, ebd⟩
      refine WP.spec_bind (WP.spec_and (timer.remove.tf (s0 := s1) s1 t (TF.start hI1) htT) (IKr s1 t hI1 htT)) ?_
      rintro s2 ⟨⟨h2, f2, -, -, w2⟩, g2⟩
      have F2 : FootDU st T Cs Sg Scs Z (EH H) U s s2 := F1.trans (FootD.u (Foot.d (f2.mono (Set.empty_subset _))))
      have f12 := f1.trans g2
      have N2 : FootN st T True T Cs Sg Scs Z ∅ s1 s2 := TW.fn h1q.tcbs h1q.nodes h1q.cur w2
      have K2 : ActAff st T s2 := ActAff.fnT h1q.tcbs N2 K1
      step with obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
          FootDU st T Cs Sg Scs Z (EH H) U s r.1 ∧ IbFr (L := L) T s r.1 ∧ ActAff st T r.1) ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (boundA t) ≠ 0#u64 := by rw [← en]; exact bne_ne hn0
          have hn : n ∈ Nt := by rw [en]; exact h2.2.2.1.2.2.bnd t htT hn0'
          have hb2 := hBA.of_fr f12
          exact WP.spec_mono (WP.spec_and (WP.spec_and
            (notification.send_signal.tinvF hA s2 a1 n bd h2 hn (hNt n hn) hb2.1 hb2.2)
            (IKs s2 a1 n bd h2 hn (hNt n hn) hb2))
            (notification.send_signal.ap hA s2 a1 n bd h2 hn (hNt n hn) hb2.1 hb2.2 K2)) fun r hr => by
            obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr
            exact ⟨hr.1.1.1, F2.trans hr.1.1.2.1, f12.trans hr.1.2, hr.2⟩
        · exact (WP.spec_ok _).2 ⟨h2, F2, f12, K2⟩
      rintro ⟨s3, a3⟩ ⟨h3, F3, f3, K3⟩
      simp only at h3 F3 f3 K3
      try simp only [WP.uncurry'_pair]
      step with LawfulStore.cur_cpu_spec as ⟨c3', ec3⟩
      step with obj.node_set.spec as ⟨s4, es4⟩
      step as ⟨i4, ei4⟩
      try simp only [WP.spec_ok]
      subst es4 ec3
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have hc3 := h3.1.choose_spec.choose_spec.cur
      have h3' := h3
      obtain ⟨⟨Q3, R3, q3⟩, -, hX3, -, -⟩ := h3'
      have N4 : FootN st T True T Cs Sg Scs Z ∅ s3
          (L.wr s3 (L.nodeAt s3 (L.cpu s3) layout.node.REPROGRAM) 1#u64) :=
        footN_node q3.nodes q3.cur (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega)
          (idOff_ge (by rw [rp]; omega)) q3.cur (by rw [rp]; omega)
      exact ⟨reprogram.tinv h3, F3.trans (FootD.u (Foot.d (foot_node (h3.1.choose_spec.choose_spec.nodes _ hc3) hc3
        (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega)))), f3.trans (IKp s3 1#u64 h3),
        ActAff.fnT q3.tcbs N4 K3, by omega⟩
    · exact (WP.spec_ok _).2 ⟨h1, F1, f1, K1⟩
  · exact ⟨h, FootD.u (Foot.d (Foot.refl _)), IbFr.refl s, ha⟩

theorem timer.fire.ap {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) (ha : ActAff st T s) :
    timer.fire st ar s a ⦃ s' _ => ActAff st T s' ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (obj.node_get.spec s c _) fun now _ => ?_
  exact timer.fire_loop.ap hA IK hNt s a now 0#u64 h hBA ha

theorem sched.awaken_loop.ap (s : S) (fuel : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) (ha : ActAff st T s) :
    sched.awaken_loop st s fuel ⦃ s' => ActAff st T s' ⦄ := by
  unfold sched.awaken_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val)
    (inv := fun x => Post st T Cs Ω H Sg Ac s x.1 ∧ ActAff st T x.1)
  · rintro ⟨s1, fu⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, f1⟩, K1⟩
    have hS1 := hS.fr f1
    unfold sched.awaken_loop.body
    dsimp only
    split
    swap
    · simp only [WP.spec_ok]; exact K1
    step as ⟨fuel1, efuel⟩
    step with LawfulStore.cur_cpu_spec as ⟨i, ei⟩
    step with obj.node_get.spec as ⟨i1, ei1⟩
    step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
    split
    · simp only [WP.spec_ok]; exact K1
    step with obj.Tcb.sc.spec as ⟨i2, _⟩
    step with sporadic.ready.spec as ⟨b1⟩
    split
    swap
    · simp only [WP.spec_ok]; exact K1
    have hR := h1.release _ h1.cur
    have hhead : i1 = (L.relQ s1 (L.cpu s1)).head := by subst_vars; rfl
    have hne : i1 ≠ 0#u64 := by simpa [b_post] using ‹¬b = true›
    have hmem : i1 ∈ R1 (L.cpu s1) := by
      rw [hhead, hR.head] at hne ⊢
      cases hR' : R1 (L.cpu s1) with
      | nil => rw [hR'] at hne; exact absurd rfl hne
      | cons x xs => simp
    have hT1 : i1 ∈ T := h1.memTR h1.cur hmem
    refine WP.spec_bind (WP.spec_and (sched.release_remove.sch s1 i1 Q1 R1 h1 hB1 hS1 hT1)
      (sched.release_remove.kwN (Sg := Sg) (Kp := (∅ : Set U64)) (Nd := True) (Scs := (∅ : Set U64))
        (Z := fun _ => 0) (Es := (∅ : Set U64)) s1 i1 h1 hT1 (Set.notMem_empty _))) ?_
    rintro s2 ⟨⟨⟨⟨Q2, R2, h2⟩, hB2, f2⟩, ea2, -, hst2⟩, F2⟩
    have K2 : ActAff st T s2 := ActAff.keep ea2 F2.2.1 (fun hA' => fnAff h1.tcbs trivial F2 hA') K1
    have hrun : Runnable (L.mem s2 (stA i1)) := by
      rw [hst2 i1 hT1]; exact h1.runR _ h1.cur i1 hmem
    have hrel : (L.mem s1 (inqA i1) &&& sched.Q_RELEASE) ≠ 0#u64 :=
      (h1.released i1 hT1).2 (by rw [h1.inR _ h1.cur i1 hmem]; exact hmem)
    refine WP.spec_bind (WP.spec_and (sched.possible_switch_to.sch s2 i1 Q2 R2 h2 hB2 (hS1.fr f2) hT1 hrun (fun h0 => by
      rw [f2.sc i1 hT1] at h0 ⊢; exact hB1.sact i1 hT1 (Or.inr (Or.inl hrel)) h0))
      (sched.possible_switch_to.ap s2 i1 h2 hT1 K2)) ?_
    rintro s3 ⟨⟨⟨hi3, hB3, f3⟩, -, -⟩, K3⟩
    simp only [WP.spec_ok]
    exact ⟨⟨hi3, hB3, f1.trans (f2.trans f3)⟩, K3, by omega⟩
  · exact ⟨⟨⟨Q, R, h⟩, hB, Fr.refl _ _⟩, ha⟩

/-- **The action thread and the idle thread at the end of `awaken`**: an
action thread has affinity the executing core (from `ActAff` at its start),
and so has the idle thread (`fire` is an `FKI` step: `OKeep2.iaf`; the release
loop is an `SFootN` one). -/
theorem sched.awaken.ap {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (c : FCtx st T Cs Scs (L.cpu s) s) (ha : ActAff st T s) (hi : IdleAff st s) :
    sched.awaken st ar s a ⦃ r => ActAff st T r.1 ∧ IdleAff st r.1 ⦄ := by
  have he := c.he
  unfold sched.awaken
  refine WP.spec_bind (WP.spec_and (WP.spec_and (timer.fire.tinvF hA IK hNt s a h hBA)
    (timer.fire.fki hA IK hNt s a h hBA c)) (timer.fire.ap hA IK hNt s a h hBA ha)) ?_
  rintro ⟨s1, a1⟩ hh
  simp only [WP.uncurry'_pair] at hh
  obtain ⟨⟨⟨⟨⟨Q1, R1, h1⟩, hB1, -, hS1, -⟩, Fd⟩, k⟩, ha1⟩ := hh
  have hc1 : L.cpu s1 = L.cpu s := Fd.2.1
  have hi1 : IdleAff st s1 := by
    have e1 : L.idleW s1 = L.idleW s := by
      show idleAt st (L.cpu s1) s1 = idleAt st (L.cpu s) s
      rw [hc1]; exact k.fk.keep.idle_eq he
    have e2 : L.mem s1 (affA (L.idleW s)) = L.mem s (affA (L.idleW s)) := k.fk.keep.iaf _ he
    unfold IdleAff
    rw [e1, e2, hc1]; exact hi
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (WP.spec_and (sched.awaken_loop.ap s1 _ Q1 R1 h1 hB1 hS1.sg ha1)
    (sched.awaken_loop.kwN (Sg := Sg) (Kp := (∅ : Set U64)) (Scs := Scs) (Z := Z) s1 _ Q1 R1 h1 hB1 hS1.sg
      (fun y hy => absurd hy (Set.notMem_empty _)) (fun _ hy => absurd hy (Set.notMem_empty _)))) ?_
  rintro s2 ⟨ha2, F2⟩
  exact (WP.spec_ok _).2 ⟨ha2, hi1.step h1 F2.sN⟩

/-- **`schedule` closes an entry, `hE` reduced** (`AllCores.schedF` with the
`act` and `idle` parts of `SchPre` discharged by `sched.awaken.ap`). Entry end
facts: `hao`, `hcK`, `hidl` (as `schedF`) and `hsa` (`ActAff` at the body's
end: an action thread the body made has affinity the executing core). Named
premises: `hR` [J] (with action `RESUME` at the end of `awaken` the current
thread is `SchCur`; false without a domain invariant, module docstring),
`hS0` [W]. -/
theorem AllCores.schedE {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) {s0 s : S} (a : A)
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (kb : OKeep2 st T Cs (L.cpu s0) s0 s) (hc : L.cpu s = L.cpu s0)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hao : ActOut st T (OtherK st T Cs (L.cpu s0) s0) s) (hcK : L.curW s ∉ OtherK st T Cs (L.cpu s0) s0)
    (hsa : ActAff st T s)
    (hR : ∀ r : S × A, sched.awaken st ar s a = ok r → L.actionW r.1 = 0#u64 → SchCur st r.1)
    (hidl : L.mem s (stA (L.idleW s)) = sched.TS_IDLE) :
    sched.schedule st ar s a ⦃ s' _ => AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have c : FCtx st T Cs Scs (L.cpu s0) s := FCtx.ofAll h0 hcpu kb hc h hidl hao
  have c' : FCtx st T Cs Scs (L.cpu s) s := by rw [hc]; exact c
  have hi : IdleAff st s := by
    show L.mem s (affA (idleAt st (L.cpu s) s)) = L.cpu s
    rw [hc, kb.idle_eq hcpu, kb.iaf _ hcpu]; exact h0.idleAff _ hcpu
  refine AllCores.schedF hA IK hNt a h0 hcpu hS0 kb hc h hBA hao hcK (fun r hr => ?_) hidl
  have w := sched.awaken.ap hA IK hNt s a h hBA c' hsa hi
  rw [hr] at w
  obtain ⟨ha', hi'⟩ := (WP.spec_ok r).1 w
  exact ⟨hR r hr, ha', hi'⟩

end

end Fl4Proofs.P2.Stall
