/-
P2 (p2j14, KWN step 6): **`schedule`'s core-separated footprint** (`SFootN`),
lifting P1's `SFoot` (`P1/QueueFootS.lean`) as `FootN`..`FootN5` lifted the
queue operations.

* `SchedWN Kp s`: P1's `SchedW` (`KW` with the heap's endpoints and
  notifications, and the kernel-global area) without the node identity words
  `IdN False` (every core's `IDLE_THREAD`/`IDLE_SC`, the other cores'
  `CUR_THREAD`/`SCHED_ACTION`/`CUR_SC`) and without the protected words
  `PrW Kp True` (the `STATE`/`IN_QUEUES` of `Kp`, every thread's `SC` and
  `AFFINITY`, every SC's `REPLY` and `TCB`). Only the executing core's own
  `CUR_THREAD` separates it from `KWN Kp True`: `schedule` switches threads
  but donates nothing. `SFootN` = `WritesA` in `SchedWN` (so with `AcK`).
* `FootN.sN`: a `KWN Kp True` footprint is an `SFootN` one; so every
  queue operation of `P2/FootN.lean` (instantiated at `Nd = True`) is.
* `KpAff Kp s`: the protected threads are TCBs of affinity other than the
  executing core; kept by `SFootN` (`KpAff.step`). Then no thread of the
  executing core's ready or release queues is protected (`KpAff.notQ`,
  `KpAff.notR`).
* `.sN` footprints: `set_cur_thread`, `switch_to_thread`, `choose_thread`,
  `next_domain`, `schedule_choose_new_thread`, the switch-to candidate's
  `cand_choose`, `awaken_loop` (as `FootN Kp True`), and **`schedule.sN`**:
  after `timer::fire` (P1's `FootDU`), the rest of `schedule` (`awaken_loop`,
  the action, `switch_sched_context`, `set_next_interrupt`, `send_pending`) is
  an `SFootN`, given at `fire`'s end `KpAff`, `ActOut` and the current thread
  unprotected (`hF`).

`hF` is a hypothesis of `schedule.sN` (what the entry must supply at the
end of `fire`), not a premise of this module; no premise.
-/
import Fl4Proofs.P2.FootN2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Es : Set U64} {Ac : Set U64} {Kp : Set U64}
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

/-- `schedule`'s word set without the node identity words of `IdN False` and
the protected words of `PrW Kp True`. -/
def SchedWN (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (T Cs Sg Scs : Set U64) (Z : U64 → Nat)
    (H : Heap) (s0 : S) (b : U64) : Prop :=
  SchedW st T Cs Sg Scs Z H s0 b ∧ ¬ IdN st False Cs s0 b ∧ ¬ PrW st Kp True T Cs Scs s0 b

/-- A footprint inside `SchedWN`, with `AcK`. -/
abbrev SFootN (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (T Cs Sg Scs : Set U64) (Z : U64 → Nat)
    (H : Heap) (s s' : S) : Prop :=
  WritesA st T Kp s s' (SchedWN st Kp T Cs Sg Scs Z H s)

/-- The protected threads are TCBs whose affinity is not the executing core. -/
def KpAff (st : machine.Store S) [L : LawfulStore st] (T Kp : Set U64) (s : S) : Prop :=
  ∀ y ∈ Kp, y ∈ T ∧ L.mem s (affA y) ≠ L.cpu s

theorem SchedWN.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (hc : L.cpu s1 = L.cpu s0)
    (h : SchedWN st Kp T Cs Sg Scs Z H s1 b) : SchedWN st Kp T Cs Sg Scs Z H s0 b :=
  ⟨SchedW.ksb hk h.1, fun hi => h.2.1 (IdN.ksb hk hc hi), fun hp => h.2.2 (PrW.ksb hk hp)⟩

theorem SFootN.refl (s : S) : SFootN st Kp T Cs Sg Scs Z H s s := WritesA.refl _ _

theorem SFootN.trans {s₁ s₂ s₃ : S} (h₁ : SFootN st Kp T Cs Sg Scs Z H s₁ s₂)
    (h₂ : SFootN st Kp T Cs Sg Scs Z H s₂ s₃) : SFootN st Kp T Cs Sg Scs Z H s₁ s₃ :=
  WritesA.mono (WritesA.trans h₁ h₂) fun b hb => Or.elim hb id fun hb => SchedWN.ksb h₁.1 h₁.2.1 hb

theorem SFootN.sfoot {s s' : S} (h : SFootN st Kp T Cs Sg Scs Z H s s') : SFoot st T Cs Sg Scs Z H s s' :=
  WritesIn.mono h.w fun _ hb => hb.1

theorem idN_mono {s : S} {b : U64} (h : IdN st False Cs s b) : IdN st True Cs s b := by
  obtain ⟨c, hc, o, ho, e⟩ := h
  refine ⟨c, hc, o, ?_, e⟩
  rcases ho with e | e | h | ⟨hf, -⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact hf.elim

theorem sN_of {s : S} {b : U64} (h : SchedW st T Cs Sg Scs Z H s b) (hn : ¬ IdW st Kp True T Cs Scs s b) :
    SchedWN st Kp T Cs Sg Scs Z H s b :=
  ⟨h, fun hi => hn (Or.inl (idN_mono hi)), fun hp => hn (Or.inr hp)⟩

/-- **A `KWN Kp True` footprint is an `SFootN` one.** -/
theorem FootN.sN {s s' : S} (f : FootN st Kp True T Cs Sg Scs Z (EH H) s s') :
    SFootN st Kp T Cs Sg Scs Z H s s' :=
  WritesA.mono f fun _ hb => sN_of (Or.inl hb.1) hb.2

/-- The executing core's node words other than the idle words and the debug
head are in `SchedWN`. -/
theorem schedWN_cur {s : S} {o : U64} (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs)
    (ho : o.val < 4288) (h88 : o.val ≠ 88) (hi8 : o.val ≠ 8) (hi32 : o.val ≠ 32) :
    SchedWN st Kp T Cs Sg Scs Z H s (L.nodeAt s (L.cpu s) o) :=
  ⟨Or.inl (kw_node hc ho h88), fun hi => notIdW_node (Kp := Kp) (Nd := False) (Scs := Scs) NP hc ho
    (idOff_cur hi8 hi32 False.elim) (Or.inl hi), notPrW_node NP hc ho⟩

theorem sN_wr {s : S} {a v : U64} (ha : Aligned a) (hk : SchedWN st Kp T Cs Sg Scs Z H s a)
    (he : L.actionW (L.wr s a v) = L.actionW s) : SFootN st Kp T Cs Sg Scs Z H s (L.wr s a v) :=
  ((writesIn_wr ha).mono fun b hb => hb ▸ hk).a (AcK.of_eq he)

/-- A write of an executing-core node word other than the idle words, the
action and the debug head. -/
theorem sN_node {s : S} {o v : U64} (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs)
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) (h88 : o.val ≠ 88) (hi8 : o.val ≠ 8) (hi32 : o.val ≠ 32)
    (h16 : o.val ≠ 16) :
    SFootN st Kp T Cs Sg Scs Z H s (L.wr s (L.nodeAt s (L.cpu s) o) v) :=
  sN_wr (nodeAt_aligned (NP _ hc) ho h8) (schedWN_cur NP hc ho h88 hi8 hi32)
    (actionW_of (writesIn_wr (nodeAt_aligned (NP _ hc) ho h8)) (NP _ hc) fun e =>
      notAct_node (NP _ hc) (NP _ hc) ho h16 e)

/-- The SC header words are frame words. -/
theorem scSg {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) : ∀ c ∈ Scs, scReplyA c ∈ Sg ∧ scTcbA c ∈ Sg :=
  fun c hc => ⟨hO.repW c hc, (hO.fixW c hc).1⟩

/-- A write to the kernel-global area. -/
theorem sN_ks {s : S} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SgOK st Ω Sg s)
    (hSg : ∀ c ∈ Scs, scReplyA c ∈ Sg ∧ scTcbA c ∈ Sg) {o v : U64} (ho : o.val < 13568) (h8 : o.val % 8 = 0) :
    SFootN st Kp T Cs Sg Scs Z H s (L.wr s (core.num.U64.wrapping_add (L.ksb s) o) v) := by
  have hv := ks_val h ho
  have hout := h.omega _ (hS.ksΩ o ho h8)
  have hn : ¬ IdW st Kp True T Cs Scs s (core.num.U64.wrapping_add (L.ksb s) o) :=
    notIdW_out h.nodes hout fun _ c hc => by
      obtain ⟨r1, r2⟩ := hSg c hc
      refine ⟨fun e => ?_, fun e => ?_⟩
      · have := hS.ks _ r1; rw [← e, hv] at this; omega
      · have := hS.ks _ r2; rw [← e, hv] at this; omega
  exact sN_wr (ks_aligned h ho h8) (sN_of (Or.inr ⟨o, ho, rfl⟩) hn) (actionW_out h.nodes h.cur hout)

/-! ## `KpAff` -/

theorem KpAff.step {s s' : S} (hT : TcbPlaced T) (f : SFootN st Kp T Cs Sg Scs Z H s s')
    (h : KpAff st T Kp s) : KpAff st T Kp s' := fun y hy => by
  obtain ⟨hyT, ha⟩ := h y hy
  refine ⟨hyT, ?_⟩
  rw [f.2.1, f.mem_eq (by rw [affA_eq]; exact field_aligned (hT y hyT) (by simp) (by simp))
    (fun hb => hb.2.2 (Or.inr ⟨trivial, Or.inl ⟨y, hyT, hT y hyT, Or.inr rfl⟩⟩))]
  exact ha

theorem KpAff.notQ {s : S} (hK : KpAff st T Kp s) (h : SchedQueuesInvX st T Cs Ω H X s Q R) {p y : U64}
    (hp : p.val < 256) (hy : y ∈ Q (L.cpu s) p) : y ∉ Kp :=
  fun hk => (hK y hk).2 (h.inQ _ h.cur p hp y hy).1

theorem KpAff.notR {s : S} (hK : KpAff st T Kp s) (h : SchedQueuesInvX st T Cs Ω H X s Q R) {y : U64}
    (hy : y ∈ R (L.cpu s)) : y ∉ Kp :=
  fun hk => (hK y hk).2 (h.inR _ h.cur y hy)

/-! ## The thread switch -/

theorem sched.set_cur_thread.sN (s : S) (t : obj.Tcb) (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs) :
    sched.set_cur_thread st s t ⦃ s' => SFootN st Kp T Cs Sg Scs Z H s s' ⦄ :=
  WP.spec_mono (sched.set_cur_thread.spec s t) fun s' e => by
    subst e
    exact sN_node NP hc (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; omega)
      (by rw [curth0]; omega) (by rw [curth0]; omega) (by rw [curth0]; omega)

theorem sched.switch_to_thread.sN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T) (htK : t ∉ Kp) :
    sched.switch_to_thread st ar s a t ⦃ s' _ => SFootN st Kp T Cs Sg Scs Z H s s' ⦄ := by
  unfold sched.switch_to_thread
  refine WP.spec_bind (set_vm_root_same hA s a t) ?_
  rintro ⟨s1, a1⟩ e
  simp only [WP.uncurry'_pair] at e
  subst e
  refine WP.spec_bind (sched.dequeue.kwN (Sg := Sg) (Kp := Kp) (Nd := True) (Scs := Scs) (Z := Z) (Es := EH H)
    s1 t h ht htK) ?_
  intro s2 f2
  refine WP.spec_bind (sched.set_cur_thread.sN (Sg := Sg) (Kp := Kp) (Scs := Scs) (Z := Z) (H := H) s2 t
    (fun c hc => (h.nodes c hc).ksb f2.1) (by rw [f2.2.1]; exact h.cur)) ?_
  intro s3 f3
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact f2.sN.trans f3

theorem sched.choose_thread.sN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hK : KpAff st T Kp s) :
    sched.choose_thread st ar s a ⦃ s' _ => SFootN st Kp T Cs Sg Scs Z H s s' ⦄ := by
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
    exact sched.switch_to_thread.sN hA s a q.head h htT (hK.notQ h hp hmem)
  · unfold sched.switch_to_idle_thread
    step with sched.idle_thread.spec' as ⟨idle, idle_post⟩
    refine WP.spec_bind (set_kernel_vm_root_same (st := st) hA s a) ?_
    rintro ⟨s1, a1⟩ e
    simp only [WP.uncurry'_pair] at e
    subst s1
    refine WP.spec_bind (sched.set_cur_thread.sN (Sg := Sg) (Kp := Kp) (Scs := Scs) (Z := Z) (H := H) s idle
      h.nodes h.cur) ?_
    intro s2 f2
    simp only [WP.spec_ok, WP.uncurry'_pair]
    exact f2

theorem sched.next_domain.sN (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s)
    (hSg : ∀ c ∈ Scs, scReplyA c ∈ Sg ∧ scTcbA c ∈ Sg) :
    sched.next_domain st s ⦃ s' => SFootN st Kp T Cs Sg Scs Z H s s' ⦄ := by
  unfold sched.next_domain
  step with obj.ks_get.spec as ⟨i, _⟩
  step as ⟨idx, _⟩
  have hST : P0.StoreTotal st := L.total
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> step*) fun idx1 _ => ?_
  refine WP.spec_bind (WP.spec_and (ks_set.sch s Q R h hB hS (o := layout.ks.DOM_SCHED_IDX) (v := idx1)
    (by simp [layout.ks.DOM_SCHED_IDX]) (by simp [layout.ks.DOM_SCHED_IDX])) (obj.ks_set.spec s _ idx1)) ?_
  rintro s1 ⟨⟨⟨h1, hB1, f1⟩, -, -⟩, e1⟩
  have F1 : SFootN st Kp T Cs Sg Scs Z H s s1 := by
    rw [e1]; exact sN_ks h hS hSg (by simp [layout.ks.DOM_SCHED_IDX]) (by simp [layout.ks.DOM_SCHED_IDX])
  refine WP.spec_bind (WP.spec_and (sched.set_reprogram.sch s1 Q R h1 hB1 (hS.fr f1))
    (sched.set_reprogram.spec s1)) ?_
  rintro s2 ⟨⟨⟨h2, hB2, f2⟩, -, -⟩, e2⟩
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have F2 : SFootN st Kp T Cs Sg Scs Z H s1 s2 := by
    rw [e2]
    exact sN_node h1.nodes h1.cur (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega) (by rw [rp]; omega)
      (by rw [rp]; omega) (by rw [rp]; omega)
  refine WP.spec_bind (WP.spec_and (ks_set.sch s2 Q R h2 hB2 ((hS.fr f1).fr f2) (o := layout.ks.WORK_UNITS)
    (v := 0#u64) (by simp [layout.ks.WORK_UNITS]) (by simp [layout.ks.WORK_UNITS])) (obj.ks_set.spec s2 _ 0#u64)) ?_
  rintro s3 ⟨⟨⟨h3, hB3, f3⟩, -, -⟩, e3⟩
  have F3 : SFootN st Kp T Cs Sg Scs Z H s2 s3 := by
    rw [e3]; exact sN_ks h2 ((hS.fr f1).fr f2) hSg (by simp [layout.ks.WORK_UNITS]) (by simp [layout.ks.WORK_UNITS])
  have hS3 := ((hS.fr f1).fr f2).fr f3
  step with sched.dom_sched_domain.spec as ⟨d⟩
  step with sched.dom_sched_duration.spec as ⟨t⟩
  refine WP.spec_bind (WP.spec_and (ks_set.sch s3 Q R h3 hB3 hS3 (o := layout.ks.CUR_DOMAIN) (v := d)
    (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])) (obj.ks_set.spec s3 _ d)) ?_
  rintro s4 ⟨⟨⟨h4, -, f4⟩, -, -⟩, e4⟩
  have F4 : SFootN st Kp T Cs Sg Scs Z H s3 s4 := by
    rw [e4]; exact sN_ks h3 hS3 hSg (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
  refine WP.spec_mono (obj.ks_set.spec s4 _ t) ?_
  intro s5 e5
  have F5 : SFootN st Kp T Cs Sg Scs Z H s4 s5 := by
    rw [e5]; exact sN_ks h4 (hS3.fr f4) hSg (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
  exact F1.trans (F2.trans (F3.trans (F4.trans F5)))

theorem sched.schedule_choose_new_thread.sN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s)
    (hSg : ∀ c ∈ Scs, scReplyA c ∈ Sg ∧ scTcbA c ∈ Sg) (hK : KpAff st T Kp s) :
    sched.schedule_choose_new_thread st ar s a ⦃ s' _ => SFootN st Kp T Cs Sg Scs Z H s s' ⦄ := by
  unfold sched.schedule_choose_new_thread
  step with sched.domain_time.spec as ⟨i⟩
  refine WP.spec_bind (Pₘ := fun s1 => (∃ Q R, SchedQueuesInv st T Cs Ω H s1 Q R) ∧
      SFootN st Kp T Cs Sg Scs Z H s s1) ?_ ?_
  · split
    · exact WP.spec_mono (WP.spec_and (sched.next_domain.sch s Q R h hB hS)
        (sched.next_domain.sN (Kp := Kp) (Scs := Scs) (Z := Z) s Q R h hB hS hSg)) fun s1 hh => ⟨hh.1.1.inv, hh.2⟩
    · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, SFootN.refl _⟩
  rintro s1 ⟨⟨Q1, R1, h1⟩, f1⟩
  exact WP.spec_mono (sched.choose_thread.sN (Sg := Sg) (Scs := Scs) (Z := Z) (H := H) hA s1 a h1
    (hK.step h.tcbs f1)) fun r hr => by obtain ⟨s', a'⟩ := r; exact f1.trans (by simpa using hr)

theorem cand_choose.sN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (act : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hSg : ∀ c ∈ Scs, scReplyA c ∈ Sg ∧ scTcbA c ∈ Sg) (hK : KpAff st T Kp s)
    (hact : L.actionW s = act) (hT : act ∈ T) (hTK : act ∉ Kp) (app : Bool) :
    (do
      let s5 ← if app then sched.append st s act else sched.enqueue st s act
      let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
      sched.schedule_choose_new_thread st ar s6 a) ⦃ s' _ => SFootN st Kp T Cs Sg Scs Z H s s' ⦄ := by
  have hok := h.actOK (hact ▸ hT)
  rw [hact] at hok
  have hr : (L.mem s (inqA act) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hc
    exact hok.2 _ (h.aff act hT) ((h.released act hT).1 hc)
  have hbd : L.mem s (scA act) ≠ 0#u64 := by have := hB.act (hact ▸ hT); rw [hact] at this; exact this
  refine WP.spec_bind (Pₘ := fun s5 => Post st T Cs Ω H Sg Ac s s5 ∧ FootN st Kp True T Cs Sg Scs Z (EH H) s s5) ?_ ?_
  · split
    · exact WP.spec_mono (WP.spec_and (sched.append.sch s act Q R h hB hS.sg hT (fun _ => hr) (fun _ => hok.1)
        (fun _ => hbd) (fun _ => by have := hB.actA (hact ▸ hT); rwa [hact] at this))
        (sched.append.kwN (Sg := Sg) (Kp := Kp) (Nd := True) (Scs := Scs) (Z := Z) (Es := EH H) s act h hT hTK))
        fun s5 h5 => ⟨h5.1.1, h5.2⟩
    · exact WP.spec_mono (WP.spec_and (sched.enqueue.sch s act Q R h hB hS.sg hT (fun _ => hr) (fun _ => hok.1)
        (fun _ => hbd) (fun _ => by have := hB.actA (hact ▸ hT); rwa [hact] at this))
        (sched.enqueue.kwN (Sg := Sg) (Kp := Kp) (Nd := True) (Scs := Scs) (Z := Z) (Es := EH H) s act h hT hTK))
        fun s5 h5 => ⟨h5.1.1, h5.2⟩
  rintro s5 ⟨⟨⟨Q5, R5, h5⟩, hB5, f5⟩, F5⟩
  rw [choose_val]
  refine WP.spec_bind (WP.spec_and (sched.set_action.sch s5 1#u64 Q5 R5 h5 hB5 (hS.fr f5).sg (Or.inr (Or.inl rfl))
    (fun hT => absurd hT (one_notT h)) (fun hT => absurd hT (one_notT h)) (fun e => by simp at e)
    (fun hT => absurd hT (one_notT h)))
    (sched.set_action.kwN (Sg := Sg) (Kp := Kp) (Nd := True) (Scs := Scs) (Z := Z) (Es := EH H) s5 1#u64 h5.nodes
      h5.cur (small_out h5.tcbs (by simp)))) ?_
  rintro s6 ⟨⟨⟨⟨Q6, R6, h6⟩, hB6, f6⟩, -, -, -⟩, F6⟩
  have F56 : SFootN st Kp T Cs Sg Scs Z H s s6 := F5.sN.trans F6.sN
  exact WP.spec_mono (sched.schedule_choose_new_thread.sN (Kp := Kp) (Scs := Scs) (Z := Z) hA s6 a Q6 R6 h6 hB6
    ((hS.fr f5).fr f6).sg hSg (hK.step h.tcbs F56)) fun r hr => by
      obtain ⟨s', a'⟩ := r; exact F56.trans (by simpa using hr)

/-- `awaken_loop` in `KWN Kp True`: it moves the executing core's released
threads (none protected, `KpAff.notR`) to the ready queues. -/
theorem sched.awaken_loop.kwN (s : S) (fuel : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s)
    (hK : KpAff st T Kp s) (hKa : ActOut st T Kp s) :
    sched.awaken_loop st s fuel ⦃ s' => FootN st Kp True T Cs Sg Scs Z (EH H) s s' ⦄ := by
  unfold sched.awaken_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val)
    (inv := fun x => Post st T Cs Ω H Sg Ac s x.1 ∧ FootN st Kp True T Cs Sg Scs Z (EH H) s x.1)
  · rintro ⟨s1, fu⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, f1⟩, F1⟩
    have hS1 := hS.fr f1
    have hK1 : KpAff st T Kp s1 := hK.step h.tcbs F1.sN
    have hKa1 : ActOut st T Kp s1 := F1.out hKa
    unfold sched.awaken_loop.body
    dsimp only
    split
    swap
    · simp only [WP.spec_ok]; exact F1
    step as ⟨fuel1, efuel⟩
    step with LawfulStore.cur_cpu_spec as ⟨i, ei⟩
    step with obj.node_get.spec as ⟨i1, ei1⟩
    step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
    split
    · simp only [WP.spec_ok]; exact F1
    step with obj.Tcb.sc.spec as ⟨i2, _⟩
    step with sporadic.ready.spec as ⟨b1⟩
    split
    swap
    · simp only [WP.spec_ok]; exact F1
    have hR := h1.release _ h1.cur
    have hhead : i1 = (L.relQ s1 (L.cpu s1)).head := by subst_vars; rfl
    have hne : i1 ≠ 0#u64 := by simpa [b_post] using ‹¬b = true›
    have hmem : i1 ∈ R1 (L.cpu s1) := by
      rw [hhead, hR.head] at hne ⊢
      cases hR' : R1 (L.cpu s1) with
      | nil => rw [hR'] at hne; exact absurd rfl hne
      | cons x xs => simp
    have hT1 : i1 ∈ T := h1.memTR h1.cur hmem
    have hK1i : i1 ∉ Kp := hK1.notR h1 hmem
    refine WP.spec_bind (WP.spec_and (sched.release_remove.sch s1 i1 Q1 R1 h1 hB1 hS1 hT1)
      (sched.release_remove.kwN (Sg := Sg) (Kp := Kp) (Nd := True) (Scs := Scs) (Z := Z) (Es := EH H) s1 i1 h1 hT1
        hK1i)) ?_
    rintro s2 ⟨⟨⟨⟨Q2, R2, h2⟩, hB2, f2⟩, -, -, hst2⟩, F2⟩
    have hrun : Runnable (L.mem s2 (stA i1)) := by
      rw [hst2 i1 hT1]; exact h1.runR _ h1.cur i1 hmem
    have hrel : (L.mem s1 (inqA i1) &&& sched.Q_RELEASE) ≠ 0#u64 :=
      (h1.released i1 hT1).2 (by rw [h1.inR _ h1.cur i1 hmem]; exact hmem)
    refine WP.spec_bind (WP.spec_and (sched.possible_switch_to.sch s2 i1 Q2 R2 h2 hB2 (hS1.fr f2) hT1 hrun (fun h0 => by
      rw [f2.sc i1 hT1] at h0 ⊢; exact hB1.sact i1 hT1 (Or.inr (Or.inl hrel)) h0))
      (sched.possible_switch_to.kwN (Sg := Sg) (Kp := Kp) (Nd := True) (Scs := Scs) (Z := Z) (Es := EH H) s2 i1 h2
        hT1 hK1i (F2.out hKa1))) ?_
    rintro s3 ⟨⟨⟨hi3, hB3, f3⟩, -, -⟩, F3⟩
    simp only [WP.spec_ok]
    exact ⟨⟨hi3, hB3, f1.trans (f2.trans f3)⟩, F1.trans (F2.trans F3), by omega⟩
  · exact ⟨⟨⟨Q, R, h⟩, hB, Fr.refl _ _⟩, FootN.refl _⟩

/-- `set_next_interrupt` writes the executing core's `ARMED`. -/
theorem sched.set_next_interrupt.sN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) :
    sched.set_next_interrupt st ar s a ⦃ s' _ => SFootN st Kp T Cs Sg Scs Z H s s' ⦄ := by
  have hv : layout.node.ARMED.val < 4288 ∧ layout.node.ARMED.val ≠ 88 ∧ layout.node.ARMED.val ≠ 8 ∧
      layout.node.ARMED.val ≠ 32 ∧ layout.node.ARMED.val ≠ 16 := by simp [layout.node.ARMED]
  refine WP.spec_mono (WP.spec_and (sched.set_next_interrupt.fp hA s a (B := SchedWN st Kp T Cs Sg Scs Z H s)
    (h.nodes _ h.cur) (schedWN_cur h.nodes h.cur hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1))
    (sched.set_next_interrupt.fp hA s a (B := (· = L.nodeAt s (L.cpu s) layout.node.ARMED)) (h.nodes _ h.cur) rfl))
    fun r hh => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hh ⊢
  exact hh.1.a (AcK.of_eq (actionW_of hh.2 (h.nodes _ h.cur) fun e =>
    notAct_node (h.nodes _ h.cur) (h.nodes _ h.cur) hv.1 hv.2.2.2.2 e))

/-- **`schedule`'s footprint past `timer::fire`.** `fire` writes P1's
`FootDU`; given, at its end, `KpAff`, `ActOut` and the current thread
unprotected (`hF`), the rest of `schedule` is an `SFootN`. -/
theorem sched.schedule.sN {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hF : ∀ rf : S × A, timer.fire st ar s a = ok rf →
      KpAff st T Kp rf.1 ∧ ActOut st T Kp rf.1 ∧ L.curW rf.1 ∉ Kp) :
    sched.schedule st ar s a ⦃ s' _ => ∃ rf : S × A, timer.fire st ar s a = ok rf ∧
      FootDU st T Cs Sg Scs Z (EH H) U s rf.1 ∧ SFootN st Kp T Cs Sg Scs Z H rf.1 s' ⦄ := by
  have hSg : ∀ c ∈ Scs, scReplyA c ∈ Sg ∧ scTcbA c ∈ Sg := scSg h.2.2.1.1
  unfold sched.schedule sched.awaken
  -- `awaken`
  refine WP.spec_bind (Pₘ := fun r => Good st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ KpAff st T Kp r.1 ∧
      ActOut st T Kp r.1 ∧ L.curW r.1 ∉ Kp ∧ ∃ rf : S × A, timer.fire st ar s a = ok rf ∧
      FootDU st T Cs Sg Scs Z (EH H) U s rf.1 ∧ SFootN st Kp T Cs Sg Scs Z H rf.1 r.1) ?_ ?_
  · refine WP.spec_bind (spec_eq' (timer.fire.tinvF hA IK hNt s a h.tinv hBA)) ?_
    rintro ⟨s1, a1⟩ ⟨hf1, ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩, F1⟩
    obtain ⟨hK1, hKa1, hc1⟩ := hF _ hf1
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (WP.spec_and (sched.awaken_loop.sch s1 _ Q1 R1 h1 hB1 hS1.sg)
      (sched.awaken_loop.kwN (Sg := Sg) (Kp := Kp) (Scs := Scs) (Z := Z) (H := H) s1 _ Q1 R1 h1 hB1 hS1.sg
        hK1 hKa1)) ?_
    rintro s2 ⟨⟨P2, ec2⟩, F2⟩
    exact (WP.spec_ok _).2 ⟨P2.good hS1 hX1, hK1.step h1.tcbs F2.sN, F2.out hKa1, by rw [ec2]; exact hc1,
      (s1, a1), hf1, F1, F2.sN⟩
  rintro ⟨s1, a1⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩, hK1, hKa1, hc1, rf, hrf, Fd, F1⟩
  -- `check_domain_time` does nothing with one domain
  unfold sched.check_domain_time sched.is_cur_domain_expired
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have hnd : ¬ ((1#u64) > (1#u64)) := by simp
  simp only [hnd, ↓reduceIte, bind_ok, Bool.false_eq_true]
  step with sched.action.spec as ⟨act, act_post⟩
  -- the action
  refine WP.spec_bind (Pₘ := fun r => Good st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ L.mem r.1 (scA (L.curW r.1)) ≠ 0#u64 ∧
      L.mem r.1 (scA (L.curW r.1)) ∈ Ac ∧ SFootN st Kp T Cs Sg Scs Z H s1 r.1) ?_ ?_
  · split
    · rename_i hnr
      step with sched.cur_thread.spec as ⟨ct, ct_post⟩
      have hctT : ct ∈ T := by rw [ct_post]; exact h1.curT
      have hctK : ct ∉ Kp := by rw [ct_post]; exact hc1
      step with sched.is_schedulable.spec' as ⟨wr, wr_post⟩
      refine WP.spec_bind (Pₘ := fun s4 => Post st T Cs Ω H Sg Ac s1 s4 ∧ L.actionW s4 = L.actionW s1 ∧
          FootN st Kp True T Cs Sg Scs Z (EH H) s1 s4) ?_ ?_
      · split
        · exact WP.spec_mono (WP.spec_and (sched.enqueue.sch s1 ct Q1 R1 h1 hB1 hS1.sg hctT
            (fun _ => (wr_post ‹_›).2.2.1) (fun _ => (wr_post ‹_›).1) (fun _ => (wr_post ‹_›).2.1)
            (fun _ => (hS1.act _ (hX1.2.2.bound _ hctT (wr_post ‹_›).2.1).1).2 (wr_post ‹_›).2.2.2))
            (sched.enqueue.kwN (Sg := Sg) (Kp := Kp) (Nd := True) (Scs := Scs) (Z := Z) (Es := EH H) s1 ct h1
              hctT hctK))
            fun s4 h4 => ⟨h4.1.1, h4.1.2.1, h4.2⟩
        · exact (WP.spec_ok _).2 ⟨⟨⟨Q1, R1, h1⟩, hB1, Fr.refl _ _⟩, rfl, FootN.refl _⟩
      rintro s4 ⟨⟨⟨Q4, R4, h4⟩, hB4, f4⟩, ea4, F4⟩
      have hS4 := hS1.fr f4
      have hX4 := hX1.fr f4
      have hact4 : L.actionW s4 = act := ea4.trans act_post.symm
      have hK4 : KpAff st T Kp s4 := hK1.step h1.tcbs F4.sN
      split
      · exact WP.spec_mono (WP.spec_and (sched.schedule_choose_new_thread.sch hA s4 a1 Q4 R4 h4 hB4 hS4 hX4)
          (sched.schedule_choose_new_thread.sN (Kp := Kp) (Scs := Scs) (Z := Z) hA s4 a1 Q4 R4 h4 hB4 hS4.sg hSg
            hK4)) fun r hr => by
            obtain ⟨s', a'⟩ := r
            simp only [WP.uncurry'_pair] at hr ⊢
            exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, F4.sN.trans hr.2⟩
      rename_i hnc
      have hT : act ∈ T := by
        rcases h4.action with e | e | e
        · exfalso; rw [hact4] at e; rw [e, resume_val] at hnr; simp at hnr
        · exfalso; rw [hact4] at e; rw [e, choose_val] at hnc; simp at hnc
        · rw [hact4] at e; exact e
      have hTK : act ∉ Kp := by
        have := hKa1 (act_post ▸ hT); rwa [act_post]
      have hbd : L.mem s4 (scA act) ≠ 0#u64 := by have := hB4.act (hact4 ▸ hT); rw [hact4] at this; exact this
      have L1 := WP.spec_and (cand_choose hA s4 a1 act Q4 R4 h4 hB4 hS4 hX4 hact4 hT true)
        (cand_choose.sN (Kp := Kp) (Scs := Scs) (Z := Z) hA s4 a1 act Q4 R4 h4 hB4 hS4 hSg hK4 hact4 hT hTK true)
      have L3 := WP.spec_and (cand_choose hA s4 a1 act Q4 R4 h4 hB4 hS4 hX4 hact4 hT false)
        (cand_choose.sN (Kp := Kp) (Scs := Scs) (Z := Z) hA s4 a1 act Q4 R4 h4 hB4 hS4 hSg hK4 hact4 hT hTK false)
      simp only [↓reduceIte, Bool.false_eq_true] at L1 L3
      replace L1 := WP.spec_mono L1 (P₁ := WP.uncurry' fun s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SFootN st Kp T Cs Sg Scs Z H s1 s')
        fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, F4.sN.trans hr.2⟩
      replace L3 := WP.spec_mono L3 (P₁ := WP.uncurry' fun s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SFootN st Kp T Cs Sg Scs Z H s1 s')
        fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, F4.sN.trans hr.2⟩
      have L2 : sched.switch_to_thread st ar s4 a1 act ⦃ s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧
          SFootN st Kp T Cs Sg Scs Z H s1 s' ⦄ :=
        WP.spec_mono (WP.spec_and (sched.switch_to_thread.sch hA s4 a1 act Q4 R4 h4 hB4 hS4.sg hT hbd
          (by have := hB4.actA (hact4 ▸ hT); rwa [hact4] at this))
          (sched.switch_to_thread.sN (Sg := Sg) (Kp := Kp) (Scs := Scs) (Z := Z) (H := H) hA s4 a1 act h4 hT hTK))
          fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1.good hS4 hX4, by rw [hr.1.2.1, hr.1.1.fr.sc act hT]; exact hbd, by
            rw [hr.1.2.1, hr.1.1.fr.sc act hT]; have := hB4.actA (hact4 ▸ hT); rwa [hact4] at this,
            F4.sN.trans hr.2⟩
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
      exact (WP.spec_ok _).2 ⟨⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩, hB1.resume e0, hB1.curA h1.curT e0, SFootN.refl _⟩
  rintro ⟨s3, a2⟩ ⟨⟨⟨Q3, R3, h3⟩, hB3, hS3, hX3⟩, hcb1, hcb2, F3⟩
  have hcb := And.intro hcb1 hcb2
  try simp only [WP.uncurry'_pair]
  -- resume, then switch the SC
  rw [resume_val]
  refine WP.spec_bind (WP.spec_and (sched.set_action.sch s3 0#u64 Q3 R3 h3 hB3 hS3.sg (Or.inl rfl)
    (fun hT => absurd hT (notT_small h3.tcbs (by simp))) (fun hT => absurd hT (notT_small h3.tcbs (by simp)))
    (fun _ => hcb) (fun hT => absurd hT (notT_small h3.tcbs (by simp))))
    (sched.set_action.kwN (Sg := Sg) (Kp := Kp) (Nd := True) (Scs := Scs) (Z := Z) (Es := EH H) s3 0#u64 h3.nodes
      h3.cur (small_out h3.tcbs (by simp)))) ?_
  rintro s4 ⟨⟨P4, ea4, -, -⟩, F4⟩
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
  have c24 : (core.num.U64.wrapping_add (L.cscW s4) layout.sc.CONSUMED).val ≠ (L.cscW s4).val + 24 := by
    rw [hvc]; simp [layout.sc.CONSUMED]
  have c32 : (core.num.U64.wrapping_add (L.cscW s4) layout.sc.CONSUMED).val ≠ (L.cscW s4).val + 32 := by
    rw [hvc]; simp [layout.sc.CONSUMED]
  have ring : ∀ {i b : U64}, i ∈ Scs → Aligned b → InRing i (Z i) b → SchedWN st Kp T Cs Sg Scs Z H s4 b :=
    fun hi hb hr => sN_of (Or.inl (kw_sc hi hr.inSC))
      (notIdW_out h4.nodes (h4.omega _ (hO4.scW _ hi _ hb hr.inSC)) (noHdr_ring hO4 hi hr))
  have nd : ∀ {o : U64}, o.val < 4288 → o.val ≠ 88 → o.val ≠ 8 → o.val ≠ 32 →
      SchedWN st Kp T Cs Sg Scs Z H s4 (L.nodeA s4 o) :=
    fun ho h88 h8 h32 => schedWN_cur h4.nodes h4.cur ho h88 h8 h32
  refine WP.spec_bind (WP.spec_and (sched.switch_sched_context.free hA s4 a2 (zt := Z (L.mem s4 (scA (L.curW s4))))
    (zc := Z (L.cscW s4)) h4.cur hN4 h4.omega hcq
    (fun hne => ⟨htin, hS4.disj _ hcT hb4 hne⟩))
    (sched.switch_sched_context.fp hA s4 a2 (zt := Z (L.mem s4 (scA (L.curW s4))))
      (zc := Z (L.cscW s4))
      (B := SchedWN st Kp T Cs Sg Scs Z H s4) h4.cur hN4 h4.omega
      hcq (fun hne => ⟨htin, hS4.disj _ hcT hb4 hne⟩)
      (nd (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
        (by simp [layout.node.REPROGRAM]))
      (nd (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
        (by simp [layout.node.CONSUMED]))
      (nd (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
        (by simp [layout.node.CUR_SC]))
      (fun _ b hb hr => ring hts hb hr)
      (fun b hb hr => by
        rcases hr with hr | rfl
        · exact ring hcs hb hr
        · have hin : InSC (L.cscW s4) (Z (L.cscW s4))
              (core.num.U64.wrapping_add (L.cscW s4) layout.sc.CONSUMED) :=
            ⟨by rw [hvc]; omega, by rw [hvc, hcv]; omega⟩
          exact sN_of (Or.inl (kw_sc hcs hin)) (notIdW_out h4.nodes (h4.omega _ (hO4.scW _ hcs _ hb hin))
            (noHdr_sc hO4 hcs hin c24 c32))))) ?_
  rintro ⟨s5, a3⟩ ⟨w5, w5', -, -, -⟩
  simp only [WP.uncurry'_pair] at w5 w5' ⊢
  have h5 := (free_step h4 hB4 w5).1
  have F5 : SFootN st Kp T Cs Sg Scs Z H s4 s5 := w5'.a (AcK.of_eq (free_keys h4 w5).1)
  step with LawfulStore.cur_cpu_spec as ⟨c, c_post⟩
  step with obj.node_get.spec as ⟨i, _⟩
  refine WP.spec_bind (Pₘ := fun r => SchedQueuesInv st T Cs Ω H r.1 Q4 R4 ∧
      SFootN st Kp T Cs Sg Scs Z H s5 r.1) ?_ ?_
  · split
    · have hB5 := (free_step h4 hB4 w5).2
      refine WP.spec_bind (WP.spec_and (sched.set_next_interrupt.free (Ω := Ω) hA s5 a3 h5.cur (h5.nodes _ h5.cur))
        (sched.set_next_interrupt.sN (Kp := Kp) (Sg := Sg) (Scs := Scs) (Z := Z) hA s5 a3 h5)) ?_
      rintro ⟨s7, a5⟩ ⟨w7, w7'⟩
      simp only [WP.uncurry'_pair] at w7 w7' ⊢
      have h7 := free_step h5 hB5 w7
      step with obj.node_set.spec as ⟨s8, s8_post⟩
      try simp only [WP.spec_ok]
      have w8 : WritesIn st s5 s8 (L.Free s5 Ω Cs) := by
        rw [s8_post, c_post]
        exact w7.free_trans (free_node_write w7.1 h5.cur (h5.nodes _ h5.cur)
          (by simp [layout.node.REPROGRAM, LowFree]))
      have F8 : SFootN st Kp T Cs Sg Scs Z H s7 s8 := by
        rw [s8_post, c_post, ← w7.2.1]
        exact sN_node h7.1.nodes h7.1.cur (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM])
      exact ⟨(free_step h5 hB5 w8).1, w7'.trans F8⟩
    · exact (WP.spec_ok _).2 ⟨h5, SFootN.refl _⟩
  rintro ⟨s6, a4⟩ ⟨h6, F6⟩
  try simp only [WP.uncurry'_pair]
  exact WP.spec_mono (smp.send_pending.kwN (Sg := Sg) (Kp := Kp) (Nd := True) (Scs := Scs) (Z := Z) (Es := EH H)
      hA s6 a4 h6.nodes h6.cur) fun r w => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at w ⊢
    exact ⟨rf, hrf, Fd, F1.trans (F3.trans ((F4.sN.trans F5).trans (F6.trans w.sN)))⟩

end

end Fl4Proofs.P1
