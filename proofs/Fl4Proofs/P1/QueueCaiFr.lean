/-
P1: what `cancel_all_ipc` (and so `finalise_cap` of a final endpoint cap)
leaves of the scheduling words (`CaiFr`): the current and idle threads, every
thread's `SC` field and the SCs' `TCB` words are kept; a thread's state is
kept, or becomes `Restart` or `Inactive`, and it is kept for every thread
that was not blocked; no release flag gets set; the scheduler action is kept
or becomes `CHOOSE_NEW`.  With it, `thread_control_sched`'s conditions on the
target carry from before the fault-handler install to after it
(`tcs_conds_of_caifr`, `tcb.thread_control_sched.blkC`).
-/
import Fl4Proofs.P1.QueueSlots
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- The scheduling words `cancel_all_ipc` keeps, with an exception `x` (the
thread being restarted) for the "not blocked, so kept" clause. -/
structure CaiFr (st : machine.Store S) [L : LawfulStore st] (T Scs : Set U64) (x : U64) (s s' : S) : Prop where
  ksb : L.ksb s' = L.ksb s
  cur : L.curW s' = L.curW s
  idle : L.idleW s' = L.idleW s
  sc : ∀ z ∈ T, L.mem s' (scA z) = L.mem s (scA z)
  st : ∀ z ∈ T, L.mem s' (stA z) = L.mem s (stA z) ∨ L.mem s' (stA z) = sched.TS_RESTART ∨
    L.mem s' (stA z) = sched.TS_INACTIVE
  nb : ∀ z ∈ T, z ≠ x → ¬ Blocked (L.mem s (stA z)) → L.mem s' (stA z) = L.mem s (stA z)
  rel : ∀ z ∈ T, (L.mem s' (inqA z) &&& sched.Q_RELEASE) ≠ 0#u64 → (L.mem s (inqA z) &&& sched.Q_RELEASE) ≠ 0#u64
  stc : ∀ c ∈ Scs, L.mem s' (scTcbA c) = L.mem s (scTcbA c)
  /-- A thread that was not blocked and is not the scheduler action keeps
  its queue word. -/
  inq : ∀ z ∈ T, z ≠ x → ¬ Blocked (L.mem s (stA z)) → z ≠ L.actionW s → L.mem s' (inqA z) = L.mem s (inqA z)
  /-- The scheduler action is kept, becomes the excepted thread or
  `CHOOSE_NEW`, or a thread that was blocked. -/
  act : L.actionW s' = L.actionW s ∨ L.actionW s' = x ∨ L.actionW s' = 1#u64 ∨
    (L.actionW s' ∈ T ∧ Blocked (L.mem s (stA (L.actionW s'))))

theorem CaiFr.refl (x : U64) (s : S) : CaiFr st T Scs x s s :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => Or.inl rfl, fun _ _ _ _ => rfl, fun _ _ h => h, fun _ _ => rfl,
    fun _ _ _ _ _ => rfl, Or.inl rfl⟩

theorem CaiFr.trans {x : U64} {s₁ s₂ s₃ : S} (h₁ : CaiFr st T Scs x s₁ s₂) (hT : TcbPlaced T)
    (h₂ : CaiFr st T Scs x s₂ s₃) : CaiFr st T Scs x s₁ s₃ where
  ksb := h₂.ksb.trans h₁.ksb
  cur := h₂.cur.trans h₁.cur
  idle := h₂.idle.trans h₁.idle
  sc z hz := (h₂.sc z hz).trans (h₁.sc z hz)
  st z hz := by
    rcases h₂.st z hz with e | e | e
    · rw [e]; exact h₁.st z hz
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  nb z hz hx hb := by
    have e1 := h₁.nb z hz hx hb
    rw [h₂.nb z hz hx (by rw [e1]; exact hb), e1]
  rel z hz hf := h₁.rel z hz (h₂.rel z hz hf)
  stc c hc := (h₂.stc c hc).trans (h₁.stc c hc)
  inq z hz hx hb hza := by
    have e1 := h₁.nb z hz hx hb
    have hza2 : z ≠ L.actionW s₂ := by
      rcases h₁.act with e | e | e | ⟨-, e⟩
      · rw [e]; exact hza
      · rw [e]; exact hx
      · rw [e]; exact fun e' => notT_small hT (by rw [e']; decide) hz
      · exact fun e' => hb (by rw [e']; exact e)
    rw [h₂.inq z hz hx (by rw [e1]; exact hb) hza2, h₁.inq z hz hx hb hza]
  act := by
    rcases h₂.act with e | e | e | ⟨ha, hbl⟩
    · rw [e]; exact h₁.act
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · by_cases ex : L.actionW s₃ = x
      · exact Or.inr (Or.inl ex)
      · refine Or.inr (Or.inr (Or.inr ⟨ha, ?_⟩))
        by_contra hn
        exact (h₁.nb _ ha ex hn ▸ hbl) |> hn

/-- The exception can be dropped when the excepted thread was blocked. -/
theorem CaiFr.close {x : U64} {s s' : S} (h : CaiFr st T Scs x s s') (hxT : x ∈ T)
    (hx : x ∈ T → Blocked (L.mem s (stA x))) (x' : U64) : CaiFr st T Scs x' s s' where
  ksb := h.ksb
  cur := h.cur
  idle := h.idle
  sc := h.sc
  st := h.st
  nb z hz _ hb := by
    by_cases e : z = x
    · subst e; exact absurd (hx hz) hb
    · exact h.nb z hz e hb
  rel := h.rel
  stc := h.stc
  inq z hz _ hb hza := by
    by_cases e : z = x
    · subst e; exact absurd (hx hz) hb
    · exact h.inq z hz e hb hza
  act := by
    rcases h.act with e | e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inr (Or.inr ⟨by rw [e]; exact hxT, by rw [e]; exact hx hxT⟩))
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr e))

theorem CaiFr.of_keepT {t : U64} {s s' : S} (k : KeepT st T Cs Rp Scs Nt t s s')
    (hv : L.mem s' (stA t) = sched.TS_RESTART ∨ L.mem s' (stA t) = sched.TS_INACTIVE) : CaiFr st T Scs t s s' where
  ksb := k.ksb
  cur := k.curW
  idle := k.idleW
  sc z hz := k.scf hz
  st z hz := by
    by_cases e : z = t
    · subst e; exact Or.inr hv
    · exact Or.inl (k.stf hz e)
  nb z hz hx _ := k.stf hz hx
  rel z hz hf := by rw [k.inqf hz] at hf; exact hf
  stc c hc := (k.fix c hc).1
  inq z hz _ _ _ := k.inqf hz
  act := by
    rcases k.act with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inr (Or.inl e))

theorem CaiFr.of_fields {x : U64} {s s' : S} (hk : L.ksb s' = L.ksb s) (ec : L.curW s' = L.curW s)
    (ei : L.idleW s' = L.idleW s) (ea : L.actionW s' = L.actionW s)
    (hsc : ∀ z ∈ T, L.mem s' (scA z) = L.mem s (scA z))
    (hst : ∀ z ∈ T, L.mem s' (stA z) = L.mem s (stA z)) (hinq : ∀ z ∈ T, L.mem s' (inqA z) = L.mem s (inqA z))
    (hstc : ∀ c ∈ Scs, L.mem s' (scTcbA c) = L.mem s (scTcbA c)) : CaiFr st T Scs x s s' where
  ksb := hk
  cur := ec
  idle := ei
  sc := hsc
  st z hz := Or.inl (hst z hz)
  nb z hz _ _ := hst z hz
  rel z hz hf := by rw [hinq z hz] at hf; exact hf
  stc := hstc
  inq z hz _ _ _ := hinq z hz
  act := Or.inl ea

theorem CaiFr.of_post {x : U64} {s s' : S} (f : Fr st T Sg s s') (ec : L.curW s' = L.curW s) (k : Keeps st T s s')
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hinq : ∀ z ∈ T, z ≠ x → z ≠ L.actionW s → L.mem s' (inqA z) = L.mem s (inqA z))
    (hact : L.actionW s' = L.actionW s ∨ L.actionW s' = x ∨ L.actionW s' = 1#u64) : CaiFr st T Scs x s s' where
  ksb := f.ksb
  cur := ec
  idle := f.idle
  sc := f.sc
  st z hz := Or.inl (f.st z hz)
  nb z hz _ _ := f.st z hz
  rel := k.2
  stc c hc := f.sig _ (hO.fixW c hc).1
  inq z hz hx _ hza := hinq z hz hx hza
  act := by
    rcases hact with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))

/-- `unblock_sporadic` keeps the SCs' `TCB` words (it writes a ring and the
core's `REPROGRAM` word). -/
theorem endpoint.unblock_sporadic.stc {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S)
    (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T) :
    endpoint.unblock_sporadic st s t ⦃ s' => L.ksb s' = L.ksb s ∧
      ∀ c ∈ Scs, L.mem s' (scTcbA c) = L.mem s (scTcbA c) ⦄ := by
  have hO := hX.1
  unfold endpoint.unblock_sporadic
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  step with sporadic.sc_sporadic.spec as ⟨b1, b1_post⟩
  split
  · rename_i hb1
    obtain ⟨hi0, hsp⟩ := b1_post hb1
    have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
    obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
    rw [← i_post] at hiS
    have hW : RefillsWF st s i (Z i) := hS.wf hiS (hS.spor i hiS hsp)
    have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
    step with sched.cur_sc.spec as ⟨c4, _⟩
    step with sc_ne.spec as ⟨b2⟩
    split
    · have hN' := h.nodes _ h.cur
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
      have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
        hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
      refine WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 => ⟨w3.1, fun c hc => ?_⟩
      have hm : scTcbA c ∈ Ω := hS.sub _ (hO.fixW c hc).1
      have ho := h.omega _ hm
      refine w3.mem_eq ho.1 ?_
      rintro (hb | hb)
      · obtain ⟨-, e24, -⟩ := sc_facts hO hc
        have h128 := (sc_facts hO hc).1
        unfold InRing at hb
        by_cases e : c = i
        · subst e; omega
        · have := hO.scDisj c hc i hiS e; omega
      · apply out_ne_node ho h.cur hN' (o := layout.node.REPROGRAM) (by rw [rp]; omega)
        rw [hb]; rfl
    · exact (WP.spec_ok _).2 ⟨rfl, fun _ _ => rfl⟩
  · exact (WP.spec_ok _).2 ⟨rfl, fun _ _ => rfl⟩

/-- `possible_switch_to t`'s queue words: only `t` and the scheduler action
are (re)queued; the action is kept, becomes `t` or `CHOOSE_NEW`. -/
theorem sched.possible_switch_to.inq (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) (ht : t ∈ T)
    (hrun : Runnable (L.mem s (stA t))) (hta : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac) :
    sched.possible_switch_to st s t ⦃ s' =>
      (∀ z ∈ T, z ≠ t → z ≠ L.actionW s → L.mem s' (inqA z) = L.mem s (inqA z)) ∧
      (L.actionW s' = L.actionW s ∨ L.actionW s' = t ∨ L.actionW s' = 1#u64) ⦄ := by
  unfold sched.possible_switch_to
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  split
  · exact (WP.spec_ok _).2 ⟨fun _ _ _ _ => rfl, Or.inl rfl⟩
  rename_i hi0
  have hbd : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
  step with sched.in_release_queue.spec as ⟨b, b_post⟩
  split
  · exact (WP.spec_ok _).2 ⟨fun _ _ _ _ => rfl, Or.inl rfl⟩
  rename_i hb
  have hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 :=
    not_not.1 (fun hc => hb (by rw [b_post]; exact decide_eq_true hc))
  have enq : ∀ s1 Q1 R1, SchedQueuesInv st T Cs Ω H s1 Q1 R1 → BoundInv st T Ac s1 → Fr st T Sg s s1 →
      Keeps st T s s1 → (∀ z ∈ T, z ≠ L.actionW s → L.mem s1 (inqA z) = L.mem s (inqA z)) →
      (L.actionW s1 = L.actionW s ∨ L.actionW s1 = 1#u64) →
      sched.enqueue st s1 t ⦃ s' => (∀ z ∈ T, z ≠ t → z ≠ L.actionW s → L.mem s' (inqA z) = L.mem s (inqA z)) ∧
        (L.actionW s' = L.actionW s ∨ L.actionW s' = t ∨ L.actionW s' = 1#u64) ⦄ := by
    intro s1 Q1 R1 h1 hB1 f1 k1 i1 a1
    have hr1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
      by_contra hc
      exact hc (by have := mt (k1.2 t ht) (not_not.2 hr0); exact not_not.1 this)
    refine WP.spec_mono (sched.enqueue.schX s1 t Q1 R1 h1 hB1 (hS.fr f1) ht (fun _ => hr1)
      (fun _ => (k1.1 t ht) ▸ hrun) (fun _ => by rw [f1.sc t ht]; exact hbd)
      (fun _ => by rw [f1.sc t ht]; exact hta hbd)) fun s' h' => ?_
    obtain ⟨-, -, -, ea', -, -, -, iq'⟩ := h'
    refine ⟨fun z hz hzt hza => (iq' z hz hzt).trans (i1 z hz hza), ?_⟩
    rw [ea']
    rcases a1 with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inr e)
  unfold sched.cur_domain
  step with obj.ks_get.spec as ⟨i1, _⟩
  step with obj.Tcb.domain.spec as ⟨i2, _⟩
  split
  · exact enq s Q R h hB (Fr.refl _ _) (Keeps.refl _) (fun _ _ _ => rfl) (Or.inl rfl)
  step with obj.Tcb.affinity.spec as ⟨i3, _⟩
  step with LawfulStore.cur_cpu_spec as ⟨i4, _⟩
  split
  · exact enq s Q R h hB (Fr.refl _ _) (Keeps.refl _) (fun _ _ _ => rfl) (Or.inl rfl)
  step with sched.action.spec as ⟨i5, _⟩
  split
  · refine WP.spec_bind (sched.reschedule_required.schX s Q R h hB hS) ?_
    rintro s1 ⟨⟨Q1, R1, h1⟩, hB1, f1, ea1, -, k1, -, i1⟩
    exact enq s1 Q1 R1 h1 hB1 f1 k1 (fun z hz hza => i1 z hz (Ne.symm hza)) (Or.inr ea1)
  · refine WP.spec_mono (sched.set_action.spec s t) fun s' e => ?_
    subst e
    have hN := h.nodes _ h.cur
    refine ⟨fun z hz _ _ => ?_, Or.inr (Or.inl ?_)⟩
    · rw [inqA_eq]
      exact field_wr_node h h.cur (by rw [act_val]; omega) (by rw [act_val]) hz (by simp) (by simp)
    · unfold LawfulStore.actionW
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact L.mem_wr_same (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val]))

theorem endpoint.restart_thread_if_no_fault.fr {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXt : ∀ y ∈ X, y = t)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t)
    (hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q c p) (hnR : ∀ c ∈ Cs, t ∉ R c) (hna : L.actionW s ≠ t)
    (htA : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' => CaiFr st T Scs t s s' ⦄ := by
  have hq : ∀ v : U64, (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∈ Q c p → Runnable v) ∧
      (∀ c ∈ Cs, t ∈ R c → Runnable v) ∧ (L.actionW s = t → Runnable v) := fun v =>
    ⟨fun c hc p hp htq => absurd htq (hnQ c hc p hp), fun c hc htr => absurd htr (hnR c hc),
      fun e => absurd e hna⟩
  have cg : ∀ y, y ∈ {y : U64 | y ∈ X ∧ y ≠ t} ↔ y ∈ (∅ : Set U64) := fun y => by
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]; exact hXt y
  unfold endpoint.restart_thread_if_no_fault
  step with obj.Tcb.fault_type.any as ⟨i, _hi⟩
  split
  · refine WP.spec_bind (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_restart restart_ne hx hnoref (hq _)) ?_
    rintro s1 ⟨h1, hB1, hX1, hS1, hSg1, st1, k1⟩
    have h1' : SchedQueuesInv st T Cs Ω H s1 Q R := h1.congrX cg
    have F1 : CaiFr st T Scs t s s1 := CaiFr.of_keepT k1 (Or.inl st1)
    refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s1 t h1' hB1 hX1 hS1 hSg1 ht)
      (endpoint.unblock_sporadic.stc s1 t h1' hX1 hS1 ht)) ?_
    rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, ea2, ec2, ei2, fk2, -⟩, kb2, stc2⟩
    have F2 : CaiFr st T Scs t s1 s2 := CaiFr.of_fields kb2 ec2 ei2 ea2
      (fun z hz => by rw [scA_eq]; exact fk2 z hz _ (by simp) (by simp))
      (fun z hz => by rw [stA_eq]; exact fk2 z hz _ (by simp) (by simp))
      (fun z hz => by rw [inqA_eq]; exact fk2 z hz _ (by simp) (by simp)) stc2
    have st2 : L.mem s2 (stA t) = sched.TS_RESTART := by
      rw [stA_eq, fk2 t ht _ (by simp) (by simp), ← stA_eq]; exact st1
    have esc2 : L.mem s2 (scA t) = L.mem s (scA t) := by
      rw [scA_eq, fk2 t ht _ (by simp) (by simp), ← scA_eq, k1.scf ht]
    refine WP.spec_mono (WP.spec_and (sched.possible_switch_to.sch (Sg := Sg) s2 t Q R h2 hB2 hSg2 ht
      (by rw [st2]; exact runnable_restart) (by rw [esc2]; exact htA))
      (sched.possible_switch_to.inq (Sg := Sg) s2 t Q R h2 hB2 hSg2 ht
      (by rw [st2]; exact runnable_restart) (by rw [esc2]; exact htA))) ?_
    rintro s3 ⟨⟨p3, ec3, k3⟩, i3, a3⟩
    exact F1.trans h.tcbs (F2.trans h.tcbs (CaiFr.of_post p3.fr ec3 k3 hX2.1 i3 a3))
  · refine WP.spec_mono (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_inactive inactive_ne hx hnoref
      (hq _)) ?_
    rintro s1 ⟨-, -, -, -, -, st1, k1⟩
    exact CaiFr.of_keepT k1 (Or.inr st1)

theorem endpoint.restart_thread_if_no_fault.bf {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXt : ∀ y ∈ X, y = t)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t)
    (hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q c p) (hnR : ∀ c ∈ Cs, t ∉ R c) (hna : L.actionW s ≠ t)
    (htA : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' =>
      (BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s') ∧ CaiFr st T Scs t s s' ⦄ :=
  WP.spec_and (endpoint.restart_thread_if_no_fault.blk s t h hXt hB hX hS hSg ht hx hnoref hnQ hnR hna htA)
    (endpoint.restart_thread_if_no_fault.fr s t h hXt hB hX hS hSg ht hx hnoref hnQ hnR hna htA)

theorem cai_round.fr {β : Type _} (s : S) (ep t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) (hst : L.epState s ep = 1#u64 ∨ L.epState s ep = 2#u64) (hhd : (L.epQ s ep).head = t) :
    (do
      let next ← tcbqueue.next_of st s .Ep t
      let s1 ← endpoint.ep_dequeue st s ep t
      let i ← obj.Tcb.state st t s1
      let s2 ← if i = sched.TS_BLOCKED_ON_RECV then do
          let i1 ← obj.Tcb.reply_obj st t s1
          if (i1 != 0#u64) = true then ipc.reply_unlink st s1 i1 t else ok s1
        else ok s1
      let s3 ← endpoint.restart_thread_if_no_fault st s2 t
      ok (ControlFlow.cont (β := β) (s3, next, fuel1))) ⦃ r => ∃ s3 next, r = .cont (s3, next, fuel1) ∧
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ Foot st T Cs Sg Scs Z {ep} s s3 ∧
        (next ≠ 0#u64 → (L.epState s3 ep = 1#u64 ∨ L.epState s3 ep = 2#u64) ∧ (L.epQ s3 ep).head = next) ∧
        CaiFr st T Scs 0#u64 s s3 ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  obtain ⟨hdT, hbe, hs1, hs2⟩ := ep_head h0 hH (w := L.epState s ep) hst rfl
  rw [hhd] at hdT hbe hs1 hs2
  have hta := hT t hdT
  obtain ⟨-, -, r3, r4, -⟩ := ts_vals
  have hsr : L.mem s (stA t) = sched.TS_BLOCKED_ON_SEND ∨ L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV := by
    rcases hst with e | e
    · exact Or.inl (hs1 e)
    · exact Or.inr (hs2 e)
  have hbl : Blocked (L.mem s (stA t)) := by
    rcases hsr with e | e
    · rw [e]; exact Or.inl rfl
    · rw [e]; exact Or.inr (Or.inl rfl)
  have hnrun := not_runnable_of_blocked hbl
  obtain ⟨-, -, da⟩ := blocked_out h0 hdT hnrun
  have hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q c p := fun c hc p hp htq => hnrun (h0.runQ c hc p hp t htq)
  have hnR : ∀ c ∈ Cs, t ∉ R c := fun c hc htr => hnrun (h0.runR c hc t htr)
  obtain ⟨E, EQ, hEW⟩ := h0.eps
  have heE : ep ∈ E := (hEW.2.2.2.2.2.2.2.1 ep).2 (Or.inl hH)
  obtain ⟨hE, -, hq⟩ := hEW.1 ep heE
  have hne : EQ ep ≠ [] := fun h0' => by
    have := (hEW.2.2.2.2.2.2.2.2.2.2 ep heE h0').1 hH
    rcases hst with e | e <;> rw [e] at this <;> exact absurd this (by decide)
  obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hne
  have hy : y = t := by rw [← hhd, hq.head, hys]; rfl
  subst hy
  rw [hys] at hq
  have hnext := hq.head_next
  unfold tcbqueue.next_of
  step with tcbqueue.next.spec as ⟨next, enext⟩
  have hdq := endpoint.ep_dequeue.inv s y Q R h0 hdT (by simp) hbl
  rw [hbe] at hdq
  refine WP.spec_bind (WP.spec_and hdq (WP.spec_and (endpoint.ep_dequeue.rel s ep y _ hT hE hq
    List.mem_cons_self) (endpoint.ep_dequeue.foot s ep y _ hT hE hq List.mem_cons_self))) ?_
  rintro s1 ⟨⟨h1, f1, o1, n1, k1, c1, nc1⟩, ⟨hq1, hst1⟩, w1⟩
  have herase : (y :: ys).erase y = ys := List.erase_cons_head y ys
  rw [herase] at hq1 hst1
  have tm1 : TmFr st T Cs Nt s s1 := ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
    fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
  have F1 : CaiFr st T Scs y s s1 := CaiFr.of_fields k1 ec1 ei1 ea1
    (fun z hz => by rw [scA_eq]; exact f1 z hz _ (by simp) (by simp) (by simp) (by simp))
    (fun z hz => by rw [stA_eq]; exact f1 z hz _ (by simp) (by simp) (by simp) (by simp))
    (fun z hz => by rw [inqA_eq]; exact f1 z hz _ (by simp) (by simp) (by simp) (by simp))
    (fun c hc => o1 _ (hSg.sub _ (hX.1.fixW c hc).1))
  have st1 : L.mem s1 (stA y) = L.mem s (stA y) := by
    rw [stA_eq]; exact f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have rp1 : L.mem s1 (replyA y) = L.mem s (replyA y) := f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have fw1 : Foot st T Cs Sg Scs Z {ep} s s1 := Foot.of w1 fun b hb => hb.kw hq.mem rfl
  have da1 : L.actionW s1 ≠ y := by rw [ea1]; exact da
  have hyA1 : L.mem s1 (scA y) ≠ 0#u64 → L.mem s1 (scA y) ∈ Ac := by
    have esc1 : L.mem s1 (scA y) = L.mem s (scA y) := by
      rw [scA_eq]; exact f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
    rw [esc1]; exact hB.sact y hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbl))))))
  -- the rest of the round, from a state `s2` with a `KW ∅` footprint from `s1`
  have tail : ∀ (s2 : S), Foot st T Cs Sg Scs Z ∅ s1 s2 → CaiFr st T Scs y s s2 →
      endpoint.restart_thread_if_no_fault st s2 y ⦃ s' =>
        (BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s2 s') ∧ CaiFr st T Scs y s2 s' ⦄ →
      (do
        let s3 ← endpoint.restart_thread_if_no_fault st s2 y
        ok (ControlFlow.cont (β := β) (s3, next, fuel1))) ⦃ r => ∃ s3 next', r = .cont (s3, next', fuel1) ∧
          BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ Foot st T Cs Sg Scs Z {ep} s s3 ∧
          (next' ≠ 0#u64 → (L.epState s3 ep = 1#u64 ∨ L.epState s3 ep = 2#u64) ∧ (L.epQ s3 ep).head = next') ∧
          CaiFr st T Scs 0#u64 s s3 ⦄ := by
    intro s2 fw2 F2 hr
    refine WP.spec_bind hr fun s3 ⟨⟨hb3, fw3⟩, F3⟩ => ?_
    have f13 : Foot st T Cs Sg Scs Z ∅ s1 s3 := fw2.trans fw3
    obtain ⟨eh, et⟩ := f13.epQ h1 hX1.1 hSg1.sub (Or.inl hH)
    refine (WP.spec_ok _).2 ⟨s3, next, rfl, hb3, fw1.trans (f13.mono (Set.empty_subset _)), fun hn0 => ?_,
      (F2.trans hT F3).close hdT (fun _ => hbl) _⟩
    have hys0 : ys ≠ [] := fun e => hn0 (by rw [enext, hnext, e]; rfl)
    have es : L.epState s3 ep = L.epState s1 ep := by simp only [LawfulStore.epState, et]
    refine ⟨by rw [es, hst1, if_neg hys0]; exact hst, ?_⟩
    rw [show (L.epQ s3 ep).head = L.mem s3 (epHeadA ep) from rfl, eh,
      show L.mem s1 (epHeadA ep) = (L.epQ s1 ep).head from rfl, hq1.head, enext, hnext]
  have cg1 : ∀ z ∈ {z : U64 | z ∈ (∅ : Set U64) ∨ z = y}, z = y := fun z hz => by simpa using hz
  step with obj.Tcb.state.spec as ⟨i, ei⟩
  split
  · rename_i hrecv
    step with obj.Tcb.reply_obj.spec as ⟨i1, ei1⟩
    split
    · rename_i hi1
      have hi10 : i1 ≠ 0#u64 := by simpa using hi1
      have hsr1 : L.mem s1 (stA y) = sched.TS_BLOCKED_ON_RECV := by rw [← ei, hrecv]
      obtain ⟨hr, hrt⟩ := hX1.2.1.recv y hdT hsr1 (by rw [← ei1]; exact hi10)
      rw [← ei1] at hr hrt
      refine WP.spec_bind (WP.spec_and (ipc.reply_unlink.inv s1 i1 y Q R h1 hdT hX1.1 hSg1.sub hr hrt
        (by rw [st1]; exact hnrun) (Or.inl (Or.inr rfl)))
        (ipc.reply_unlink.kw (Scs := Scs) (Es := ∅) s1 i1 y h1 hX1 hSg1.sub hr hdT)) ?_
      rintro s2 ⟨⟨h2, e2, k2, z2⟩, fw2⟩
      have hB2 := hB1.keepT h1 k2 (by rw [e2]; exact not_blocked_inactive) (by rw [e2]; exact inactive_ne.1)
      have hclr : ∀ r ∈ Rp, L.mem s1 (rTcbA r) = y → L.mem s2 (rTcbA r) = 0#u64 := by
        intro r hr' e
        obtain ⟨-, -, b2, -⟩ := hX1.2.1.back r hr' (by rw [e]; exact fun e0 => hta.ne0 (by rw [e0]; rfl))
        rw [e, ← ei1] at b2
        rw [← b2]; exact z2
      have hX2 := hX1.keepT k2 (by rw [e2]; exact inactive_ne) hclr
      have hS2 := hS1.keepT hX1 k2
      have hSg2 : SgOK st Ω Sg s2 := ⟨hSg1.sub, fun b hb => by rw [k2.ksb]; exact hSg1.ks b hb,
        fun o h1' h2' => by rw [k2.ksb]; exact hSg1.ksΩ o h1' h2'⟩
      have da2 : L.actionW s2 ≠ y := by
        rcases k2.act with e | e
        · rw [e]; exact da1
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hdT)
      refine tail s2 fw2 (F1.trans hT (CaiFr.of_keepT k2 (Or.inr e2))) (endpoint.restart_thread_if_no_fault.bf s2 y h2 (fun z hz => ?_) hB2 hX2 hS2 hSg2 hdT
        (Or.inr (by rw [e2]; exact not_blocked_inactive))
        (hX2.noref hta (by rw [e2]; exact inactive_ne.1) (by rw [e2]; exact inactive_ne.2)) hnQ hnR da2
        (by rw [k2.scf hdT]; exact hyA1))
      obtain ⟨hz1, hz2⟩ := hz
      exact absurd (cg1 z hz1) hz2
    · rename_i hi1
      have hz : i1 = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hi1
      have hi10 : L.mem s1 (replyA y) = 0#u64 := by rw [← ei1]; exact hz
      simp only [Aeneas.Std.bind_ok]
      exact tail s1 (Foot.refl _) F1 (endpoint.restart_thread_if_no_fault.bf s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
        (Or.inl (Or.inr rfl)) (hX1.noref0 hta hi10) hnQ hnR da1 hyA1)
  · rename_i hnrecv
    have hsend : L.mem s1 (stA y) = sched.TS_BLOCKED_ON_SEND := by
      rcases hsr with e | e
      · rw [st1, e]
      · exact absurd (by rw [ei, st1, e]) hnrecv
    have nrp : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_REPLY := by
      rw [r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide
    have nrc : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_RECV := by rw [r4, r3]; decide
    simp only [Aeneas.Std.bind_ok]
    exact tail s1 (Foot.refl _) F1 (endpoint.restart_thread_if_no_fault.bf s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
      (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [hsend]; exact nrp) (by rw [hsend]; exact nrc)) hnQ hnR da1 hyA1)


theorem endpoint.cancel_all_ipc_loop.fr (s0 s : S) (ep t fuel : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) (hf : Foot st T Cs Sg Scs Z {ep} s0 s) (hF : CaiFr st T Scs 0#u64 s0 s)
    (ht : t ≠ 0#u64 → (L.epState s ep = 1#u64 ∨ L.epState s ep = 2#u64) ∧ (L.epQ s ep).head = t) :
    endpoint.cancel_all_ipc_loop st s ep t fuel ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z {ep} s0 s' ∧ CaiFr st T Scs 0#u64 s0 s' ⦄ := by
  unfold endpoint.cancel_all_ipc_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ Foot st T Cs Sg Scs Z {ep} s0 x.1 ∧
      CaiFr st T Scs 0#u64 s0 x.1 ∧
      (x.2.1 ≠ 0#u64 → (L.epState x.1 ep = 1#u64 ∨ L.epState x.1 ep = 2#u64) ∧ (L.epQ x.1 ep).head = x.2.1))
  · rintro ⟨s1, t1, f1⟩ ⟨hb1, hf1, hF1, ht1⟩
    simp only at hb1 hf1 hF1 ht1
    unfold endpoint.cancel_all_ipc_loop.body
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 ⟨hb1, hf1, hF1⟩
    rename_i hb
    have ht0 : t1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hst1, hhd1⟩ := ht1 ht0
    split
    · rename_i hfuel
      step as ⟨fuel1, efuel⟩
      refine WP.spec_mono (cai_round.fr (β := S) s1 ep t1 fuel1 hb1 hH hst1 hhd1) ?_
      rintro r ⟨s4, next, rfl, hb4, hf4, hn4, hF4⟩
      exact ⟨hb4, hf1.trans hf4, hF1.trans hb1.1.choose_spec.choose_spec.tcbs hF4, hn4, by simp only; omega⟩
    · exact (WP.spec_ok _).2 ⟨hb1, hf1, hF1⟩
  · exact ⟨h, hf, hF, ht⟩

/-- **seL4 `cancelAllIPC` with its scheduling frame** (`CaiFr`); the
scheduler action ends kept or `CHOOSE_NEW`. -/
theorem endpoint.cancel_all_ipc.fr (s : S) (ep : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) :
    endpoint.cancel_all_ipc st s ep ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z {ep} s s' ∧ CaiFr st T Scs 0#u64 s s' ∧
      (L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64) ⦄ := by
  unfold endpoint.cancel_all_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _, CaiFr.refl _ _, Or.inl rfl⟩
  rename_i hidle
  have hst : L.epState s ep ≠ 0#u64 := by
    rw [← hv]; intro e; exact hidle (by rw [e]; unfold obj.EP_IDLE; rfl)
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, -⟩ := hI
  refine WP.spec_bind (endpoint.cancel_all_ipc_loop.fr s s ep _ _ h hH (Foot.refl _) (CaiFr.refl _ _)
    (fun _ => ⟨ep_state12 h0 hH hst, rfl⟩)) ?_
  rintro s1 ⟨h1, f1, F1⟩
  obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
  refine WP.spec_mono (WP.spec_and (sched.reschedule_required.blk s1 ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩)
    (sched.reschedule_required.schX s1 Q1 R1 q1 hB1 hSg1)) fun s2 ⟨⟨h2, f2⟩, _, _, p2, ea2, ec2, k2, _, i2⟩ =>
    ⟨h2, f1.trans (f2.mono (Set.empty_subset _)),
      F1.trans q1.tcbs (CaiFr.of_post p2 ec2 k2 hX1.1 (fun z hz _ hza => i2 z hz (Ne.symm hza))
        (Or.inr (Or.inr ea2))), Or.inr ea2⟩

/-- The threads not blocked on `ep` and other than the scheduler action keep
their queue, `SC` and state words across `cancel_all_ipc`. -/
theorem endpoint.cancel_all_ipc.keeps (s : S) (ep : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) (y : U64) (hy : y ∈ T) (hnb : ¬ Blocked (L.mem s (stA y))) (hya : y ≠ L.actionW s) :
    endpoint.cancel_all_ipc st s ep ⦃ s' => L.mem s' (inqA y) = L.mem s (inqA y) ∧
      L.mem s' (scA y) = L.mem s (scA y) ∧ L.mem s' (stA y) = L.mem s (stA y) ⦄ := by
  have hy0 : y ≠ 0#u64 := fun e => (h.1.choose_spec.choose_spec.tcbs y hy).ne0 (by rw [e]; rfl)
  exact WP.spec_mono (endpoint.cancel_all_ipc.fr s ep h hH) fun s' ⟨_, _, F, _⟩ =>
    ⟨F.inq y hy hy0 hnb hya, F.sc y hy, F.nb y hy hy0 hnb⟩

/-- `finalise_cap` of an endpoint cap, with the frame. -/
theorem fin_endpoint.fr {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (ep b0 b1 b2 b3 b4 : _)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hH : H ep = some .ep) :
    objects.finalise_cap_object st ar s a (.Endpoint ep b0 b1 b2 b3 b4) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ r.2.2 = a ∧
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ Foot st T Cs Sg Scs Z {ep} s r.2.1 ∧
      CaiFr st T Scs 0#u64 s r.2.1 ∧ (L.actionW r.2.1 = L.actionW s ∨ L.actionW r.2.1 = 1#u64) ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · refine WP.spec_bind (endpoint.cancel_all_ipc.fr s ep h hH) fun s1 ⟨h1, f1, F1, a1⟩ => ?_
    exact (WP.spec_ok _).2 ⟨rfl, rfl, h1, f1, F1, a1⟩
  · exact (WP.spec_ok _).2 ⟨rfl, rfl, h, Foot.refl _, CaiFr.refl _ _, Or.inl rfl⟩

/-- Cap-slot writes (`blk_of_capw`) have the frame too. -/
theorem CaiFr.of_capw {x : U64} {s s' : S} {B : U64 → Prop} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → CapW T Ω Sg b) : CaiFr st T Scs x s s' := by
  obtain ⟨-, pf, ec, -, ea, fld, -, sig⟩ := blk_of_capw h hw hB
  exact CaiFr.of_fields hw.1 ec pf.idle ea pf.sc pf.st
    (fun z hz => by rw [inqA_eq]; exact fld z hz _ (by simp) (by simp) (by simp))
    (fun c hc => sig _ (h.2.2.1.1.fixW c hc).1)

/-! ## `thread_control_sched` after a fault-handler install that may cancel IPC -/

/-- The target conditions of `thread_control_sched` carry across a `CaiFr`
step whose scheduler action is kept or `CHOOSE_NEW`. -/
theorem tcs_conds_of_caifr {s0 s1 : S} {target prio flags : U64} {sc : U64} (hT : TcbPlaced T) (ht : target ∈ T)
    (F : CaiFr st T Scs 0#u64 s0 s1) (ha : L.actionW s1 = L.actionW s0 ∨ L.actionW s1 = 1#u64)
    (hprio : (flags &&& tcb.SCHED_UPDATE_PRIO) ≠ 0#u64 → prio.val < 256 ∧ (target = L.curW s0 →
      (L.mem s0 (inqA target) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s0 (scA target) ≠ 0#u64 ∧
        L.mem s0 (scA target) ∈ Ac))
    (hbind : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → sc ∈ Scs ∧ L.mem s0 (scA target) = 0#u64 ∧
      L.mem s0 (scTcbA sc) = 0#u64 ∧ (BlockedR (L.mem s0 (stA target)) → sc ∈ Ac))
    (hunb : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc = 0#u64 → L.actionW s0 ≠ target ∧ L.idleW s0 ≠ target) :
    ((flags &&& tcb.SCHED_UPDATE_PRIO) ≠ 0#u64 → prio.val < 256 ∧ (target = L.curW s1 →
      (L.mem s1 (inqA target) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s1 (scA target) ≠ 0#u64 ∧
        L.mem s1 (scA target) ∈ Ac)) ∧
    ((flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → sc ∈ Scs ∧ L.mem s1 (scA target) = 0#u64 ∧
      L.mem s1 (scTcbA sc) = 0#u64 ∧ (BlockedR (L.mem s1 (stA target)) → sc ∈ Ac)) ∧
    ((flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc = 0#u64 → L.actionW s1 ≠ target ∧ L.idleW s1 ≠ target) := by
  refine ⟨fun hf => ?_, fun hf h0 => ?_, fun hf h0 => ?_⟩
  · obtain ⟨hp, hc⟩ := hprio hf
    refine ⟨hp, fun e => ?_⟩
    rw [F.cur] at e
    obtain ⟨r0, b0, a0⟩ := hc e
    refine ⟨?_, by rw [F.sc target ht]; exact b0, by rw [F.sc target ht]; exact a0⟩
    by_contra hn
    exact F.rel target ht hn r0
  · obtain ⟨hsc, h1, h2, h3⟩ := hbind hf h0
    refine ⟨hsc, by rw [F.sc target ht]; exact h1, by rw [F.stc sc hsc]; exact h2, fun hb => ?_⟩
    rcases F.st target ht with e | e | e
    · rw [e] at hb; exact h3 hb
    · rw [e] at hb
      rcases hb with hb | hb
      · exact absurd hb not_blocked_restart
      · exact absurd hb restart_ne.1
    · rw [e] at hb
      rcases hb with hb | hb
      · exact absurd hb not_blocked_inactive
      · exact absurd hb inactive_ne.1
  · obtain ⟨h1, h2⟩ := hunb hf h0
    refine ⟨?_, by rw [F.idle]; exact h2⟩
    rcases ha with e | e
    · rw [e]; exact h1
    · rw [e]; intro e'; exact notT_small hT (by rw [← e']; decide) ht

/-- **`thread_control_sched` with an install that may cancel IPC**: `hinst`
asks `BlkOK` and the `CaiFr` frame (`fin_endpoint.fr`, `CaiFr.of_capw` for
the slot writes) with the scheduler action kept or `CHOOSE_NEW`, instead of
`PFr`. -/
theorem tcb.thread_control_sched.blkC {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (target : obj.Tcb) (slot : obj.Slot) (fh : capability.Cap × obj.Slot) (mcp prio : U64) (sc : obj.Sc)
    (flags : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : target ∈ T)
    (hinst : tcb.install_tcb_cap st ar s a target slot layout.tcb.SLOT_FAULT_HANDLER fh.1 fh.2 ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ CaiFr st T Scs 0#u64 s r.2.1 ∧
      (L.actionW r.2.1 = L.actionW s ∨ L.actionW r.2.1 = 1#u64) ⦄)
    (hprio : (flags &&& tcb.SCHED_UPDATE_PRIO) ≠ 0#u64 → prio.val < 256 ∧ (target = L.curW s →
      (L.mem s (inqA target) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (scA target) ≠ 0#u64 ∧
        L.mem s (scA target) ∈ Ac))
    (hbind : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → sc ∈ Scs ∧ L.mem s (scA target) = 0#u64 ∧
      L.mem s (scTcbA sc) = 0#u64 ∧ (BlockedR (L.mem s (stA target)) → sc ∈ Ac))
    (hunb : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc = 0#u64 → L.actionW s ≠ target ∧ L.idleW s ≠ target) :
    tcb.thread_control_sched st ar s a target slot fh mcp prio sc flags ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold tcb.thread_control_sched
  simp only [lift, Aeneas.Std.bind_ok]
  split
  · obtain ⟨c, sl⟩ := fh
    refine WP.spec_bind hinst ?_
    rintro ⟨r, s2, a1⟩ ⟨h2, F2, ha2⟩
    simp only [uncurry_apply_pair] at h2 F2 ha2 ⊢
    cases r with
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.bind_ok]
      obtain ⟨hp2, hb2, hu2⟩ := tcs_conds_of_caifr hT ht F2 ha2 hprio hbind hunb
      have := tcs_tail hA s2 s2 a1 target mcp prio sc flags h2 ht (PFr.refl _ _) rfl id hp2 hb2 hu2
      simp only [lift, Aeneas.Std.bind_ok] at this
      exact this
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        Aeneas.Std.bind_ok, WP.spec_ok]
      exact WP.spec_bind (Pₘ := fun _ => True) (WP.spec_bind (Pₘ := fun _ => True) ((WP.spec_ok _).2 trivial)
        fun _ _ => (WP.spec_ok _).2 trivial) fun _ _ => (WP.spec_ok _).2 h2
  · have := tcs_tail hA s s a target mcp prio sc flags h ht (PFr.refl _ _) rfl id hprio hbind hunb
    simp only [lift, Aeneas.Std.bind_ok] at this
    exact this

end

end Fl4Proofs.P1
