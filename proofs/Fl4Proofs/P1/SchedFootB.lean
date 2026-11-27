/-
P1 (sib): **`schedule` keeps every TCB's IPC-buffer lookup words** (`IbFr`).

P1's footprint of `schedule` past `timer::fire` (`sched.schedule.sfoot`,
`SchedW`) is `KW` (every TCB field past the cap slots but the debug links)
and the kernel-global area. Here the same walk is redone with `KWB` (`KW`
without the `IPC_BUFFER` field 3512), the `.kwB` footprints P1 already has
for the queue operations (`enqueue`, `dequeue`, `append`, `set_action`,
`release_remove`, `possible_switch_to`) and `footB_node` for the node
writes:

* `SchedWB` / `SFootB`: `KWB` with the heap's endpoints and notifications,
  and the (aligned) kernel-global words.
* `set_cur_thread.kwB`, `switch_to_thread.kwB`, `choose_thread.kwB`,
  `next_domain.sfootB`, `schedule_choose_new_thread.sfootB`,
  `cand_choose.sfootB`, `awaken_loop.kwB`, **`sched.schedule.sfootB`**: the
  `SchedW` proofs of `QueueFootS` with `KWB` (nothing past `timer::fire`
  writes an `IPC_BUFFER` field).
* **`sched.schedule.ibFr`**: `timer::fire` keeps the buffer-lookup words
  (`timer.fire.tinv`, from `ibKeep_holds`), and an `SFootB` footprint keeps
  them (`KWB` words are no buffer words, `kwB_notBufW`; the kernel-global
  words lie in `Ω`, outside the TCBs).

No premise.
-/
import Fl4Proofs.P1.IbKeepHolds
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Es : Set U64} {Ac : Set U64}

/-- `SchedW` without the `IPC_BUFFER` fields: `KWB` with the heap's endpoints
and notifications, and the aligned kernel-global words. -/
def SchedWB (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (H : Heap)
    (s0 : S) (b : U64) : Prop :=
  KWB st T Cs Sg Scs Z (EH H) s0 b ∨
    ∃ o : U64, o.val < 13568 ∧ o.val % 8 = 0 ∧ b = core.num.U64.wrapping_add (L.ksb s0) o

/-- A footprint inside `SchedWB`. -/
abbrev SFootB (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (H : Heap)
    (s s' : S) : Prop :=
  WritesIn st s s' (SchedWB st T Cs Sg Scs Z H s)

theorem SchedWB.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (h : SchedWB st T Cs Sg Scs Z H s1 b) :
    SchedWB st T Cs Sg Scs Z H s0 b := by
  rcases h with h | ⟨o, ho, h8, e⟩
  · exact Or.inl (KWB.ksb hk h)
  · exact Or.inr ⟨o, ho, h8, by rw [e, hk]⟩

theorem SFootB.refl (s : S) : SFootB st T Cs Sg Scs Z H s s := WritesIn.refl _ _

theorem SFootB.trans {s₁ s₂ s₃ : S} (h₁ : SFootB st T Cs Sg Scs Z H s₁ s₂) (h₂ : SFootB st T Cs Sg Scs Z H s₂ s₃) :
    SFootB st T Cs Sg Scs Z H s₁ s₃ :=
  WritesIn.mono (WritesIn.trans h₁ h₂) fun b hb => Or.elim hb id fun hb => SchedWB.ksb h₁.1 hb

theorem FootB.sfootB {s s' : S} (h : FootB st T Cs Sg Scs Z (EH H) s s') : SFootB st T Cs Sg Scs Z H s s' :=
  WritesIn.mono h fun _ hb => Or.inl hb

theorem SFootB.footB {s₁ s₂ s₃ : S} (h₁ : SFootB st T Cs Sg Scs Z H s₁ s₂)
    (h₂ : FootB st T Cs Sg Scs Z (EH H) s₂ s₃) : SFootB st T Cs Sg Scs Z H s₁ s₃ := h₁.trans h₂.sfootB

/-- `append` in `KWB` (as `P2`'s `sched.append.kwB`). -/
theorem sched.append.kwBs {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S) (t : obj.Tcb)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.append st s t ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_mono (sched.append.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (fun h0 => h.notQ ht h0 hc hp)) fun s' hh => FootB.of hh.1 fun b hb => hb.kwB ?_ hc h.cur ht (fun o ho => by omega)
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact (hR1.1.rel _ hp).mem w hw

theorem sched.set_cur_thread.kwB (s : S) (t : obj.Tcb) (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) :
    sched.set_cur_thread st s t ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.set_cur_thread.spec s t) fun s' e => by
    subst e; exact footB_node hN hc (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; omega)

theorem sched.switch_to_thread.kwB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) {Q : U64 → U64 → List U64} {R : U64 → List U64} (h : SchedQueuesInv st T Cs Ω H s Q R)
    (ht : t ∈ T) : sched.switch_to_thread st ar s a t ⦃ s' _ => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.switch_to_thread
  refine WP.spec_bind (set_vm_root_same hA s a t) ?_
  rintro ⟨s1, a1⟩ e
  simp only [WP.uncurry'_pair] at e
  subst e
  refine WP.spec_bind (sched.dequeue.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s1 t h ht) ?_
  intro s2 f2
  refine WP.spec_bind (sched.set_cur_thread.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s2 t
    (f2.foot.curN (h.nodes _ h.cur)) (by rw [f2.2.1]; exact h.cur)) ?_
  intro s3 f3
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact f2.trans f3

theorem sched.choose_thread.kwB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    {Q : U64 → U64 → List U64} {R : U64 → List U64} (h : SchedQueuesInv st T Cs Ω H s Q R) :
    sched.choose_thread st ar s a ⦃ s' _ => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
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
    exact sched.switch_to_thread.kwB hA s a q.head h htT
  · unfold sched.switch_to_idle_thread
    step with sched.idle_thread.spec' as ⟨idle, idle_post⟩
    refine WP.spec_bind (set_kernel_vm_root_same (st := st) hA s a) ?_
    rintro ⟨s1, a1⟩ e
    simp only [WP.uncurry'_pair] at e
    subst s1
    refine WP.spec_bind (sched.set_cur_thread.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s idle
      (h.nodes _ h.cur) h.cur) ?_
    intro s2 f2
    simp only [WP.spec_ok, WP.uncurry'_pair]
    exact f2

/-- One write to the kernel-global area. -/
theorem sfootB_ks {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) {o v : U64} (ho : o.val < 13568) (h8 : o.val % 8 = 0) :
    SFootB st T Cs Sg Scs Z H s (L.wr s (core.num.U64.wrapping_add (L.ksb s) o) v) :=
  (writesIn_wr (ks_aligned h ho h8)).mono fun b hb => Or.inr ⟨o, ho, h8, hb⟩

theorem sched.next_domain.sfootB (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) :
    sched.next_domain st s ⦃ s' => SFootB st T Cs Sg Scs Z H s s' ⦄ := by
  unfold sched.next_domain
  step with obj.ks_get.spec as ⟨i, _⟩
  step as ⟨idx, _⟩
  have hST : P0.StoreTotal st := L.total
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> step*) fun idx1 _ => ?_
  refine WP.spec_bind (WP.spec_and (ks_set.sch s Q R h hB hS (o := layout.ks.DOM_SCHED_IDX) (v := idx1)
    (by simp [layout.ks.DOM_SCHED_IDX]) (by simp [layout.ks.DOM_SCHED_IDX])) (obj.ks_set.spec s _ idx1)) ?_
  rintro s1 ⟨⟨⟨h1, hB1, f1⟩, -, -⟩, e1⟩
  have F1 : SFootB st T Cs Sg Scs Z H s s1 := by
    rw [e1]; exact sfootB_ks h (by simp [layout.ks.DOM_SCHED_IDX]) (by simp [layout.ks.DOM_SCHED_IDX])
  refine WP.spec_bind (WP.spec_and (sched.set_reprogram.sch s1 Q R h1 hB1 (hS.fr f1))
    (sched.set_reprogram.spec s1)) ?_
  rintro s2 ⟨⟨⟨h2, hB2, f2⟩, -, -⟩, e2⟩
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have F2 : SFootB st T Cs Sg Scs Z H s1 s2 := by
    rw [e2]
    exact (footB_node (Es := EH H) (h1.nodes _ h1.cur) h1.cur (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega)).sfootB
  refine WP.spec_bind (WP.spec_and (ks_set.sch s2 Q R h2 hB2 ((hS.fr f1).fr f2) (o := layout.ks.WORK_UNITS) (v := 0#u64)
    (by simp [layout.ks.WORK_UNITS]) (by simp [layout.ks.WORK_UNITS])) (obj.ks_set.spec s2 _ 0#u64)) ?_
  rintro s3 ⟨⟨⟨h3, hB3, f3⟩, -, -⟩, e3⟩
  have F3 : SFootB st T Cs Sg Scs Z H s2 s3 := by
    rw [e3]; exact sfootB_ks h2 (by simp [layout.ks.WORK_UNITS]) (by simp [layout.ks.WORK_UNITS])
  have hS3 := ((hS.fr f1).fr f2).fr f3
  step with sched.dom_sched_domain.spec as ⟨d⟩
  step with sched.dom_sched_duration.spec as ⟨t⟩
  refine WP.spec_bind (WP.spec_and (ks_set.sch s3 Q R h3 hB3 hS3 (o := layout.ks.CUR_DOMAIN) (v := d)
    (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])) (obj.ks_set.spec s3 _ d)) ?_
  rintro s4 ⟨⟨⟨h4, -, -⟩, -, -⟩, e4⟩
  have F4 : SFootB st T Cs Sg Scs Z H s3 s4 := by
    rw [e4]; exact sfootB_ks h3 (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
  refine WP.spec_mono (obj.ks_set.spec s4 _ t) ?_
  intro s5 e5
  have F5 : SFootB st T Cs Sg Scs Z H s4 s5 := by
    rw [e5]; exact sfootB_ks h4 (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
  exact F1.trans (F2.trans (F3.trans (F4.trans F5)))

theorem sched.schedule_choose_new_thread.sfootB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) :
    sched.schedule_choose_new_thread st ar s a ⦃ s' _ => SFootB st T Cs Sg Scs Z H s s' ⦄ := by
  unfold sched.schedule_choose_new_thread
  step with sched.domain_time.spec as ⟨i⟩
  refine WP.spec_bind (Pₘ := fun s1 => (∃ Q R, SchedQueuesInv st T Cs Ω H s1 Q R) ∧
      SFootB st T Cs Sg Scs Z H s s1) ?_ ?_
  · split
    · exact WP.spec_mono (WP.spec_and (sched.next_domain.sch s Q R h hB hS)
        (sched.next_domain.sfootB (Scs := Scs) (Z := Z) s Q R h hB hS)) fun s1 hh => ⟨hh.1.1.inv, hh.2⟩
    · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, SFootB.refl _⟩
  rintro s1 ⟨⟨Q1, R1, h1⟩, f1⟩
  exact WP.spec_mono (sched.choose_thread.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) hA s1 a h1)
    fun r hr => by obtain ⟨s', a'⟩ := r; exact f1.footB (by simpa using hr)

theorem cand_choose.sfootB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (act : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hact : L.actionW s = act) (hT : act ∈ T) (app : Bool) :
    (do
      let s5 ← if app then sched.append st s act else sched.enqueue st s act
      let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
      sched.schedule_choose_new_thread st ar s6 a) ⦃ s' _ => SFootB st T Cs Sg Scs Z H s s' ⦄ := by
  have hok := h.actOK (hact ▸ hT)
  rw [hact] at hok
  have hr : (L.mem s (inqA act) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hc
    exact hok.2 _ (h.aff act hT) ((h.released act hT).1 hc)
  have hbd : L.mem s (scA act) ≠ 0#u64 := by have := hB.act (hact ▸ hT); rw [hact] at this; exact this
  refine WP.spec_bind (Pₘ := fun s5 => Post st T Cs Ω H Sg Ac s s5 ∧ FootB st T Cs Sg Scs Z (EH H) s s5) ?_ ?_
  · split
    · exact WP.spec_mono (WP.spec_and (sched.append.sch s act Q R h hB hS.sg hT (fun _ => hr) (fun _ => hok.1)
        (fun _ => hbd) (fun _ => by have := hB.actA (hact ▸ hT); rwa [hact] at this))
        (sched.append.kwBs (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s act h hT)) fun s5 h5 => ⟨h5.1.1, h5.2⟩
    · exact WP.spec_mono (WP.spec_and (sched.enqueue.sch s act Q R h hB hS.sg hT (fun _ => hr) (fun _ => hok.1)
        (fun _ => hbd) (fun _ => by have := hB.actA (hact ▸ hT); rwa [hact] at this))
        (sched.enqueue.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s act h hT)) fun s5 h5 => ⟨h5.1.1, h5.2⟩
  rintro s5 ⟨⟨⟨Q5, R5, h5⟩, hB5, f5⟩, F5⟩
  rw [choose_val]
  refine WP.spec_bind (WP.spec_and (sched.set_action.sch s5 1#u64 Q5 R5 h5 hB5 (hS.fr f5).sg (Or.inr (Or.inl rfl))
    (fun hT => absurd hT (one_notT h)) (fun hT => absurd hT (one_notT h)) (fun e => by simp at e)
    (fun hT => absurd hT (one_notT h)))
    (sched.set_action.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s5 1#u64 (h5.nodes _ h5.cur) h5.cur)) ?_
  rintro s6 ⟨⟨⟨⟨Q6, R6, h6⟩, hB6, f6⟩, -, -, -⟩, F6⟩
  exact WP.spec_mono (sched.schedule_choose_new_thread.sfootB (Scs := Scs) (Z := Z) hA s6 a Q6 R6 h6 hB6
    ((hS.fr f5).fr f6).sg) fun r hr => by
      obtain ⟨s', a'⟩ := r; exact (F5.sfootB.footB F6).trans (by simpa using hr)

theorem sched.awaken_loop.kwB (s : S) (fuel : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) :
    sched.awaken_loop st s fuel ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.awaken_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val)
    (inv := fun x => Post st T Cs Ω H Sg Ac s x.1 ∧ FootB st T Cs Sg Scs Z Es s x.1)
  · rintro ⟨s1, fu⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, f1⟩, F1⟩
    have hS1 := hS.fr f1
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
    refine WP.spec_bind (WP.spec_and (sched.release_remove.sch s1 i1 Q1 R1 h1 hB1 hS1 hT1)
      (sched.release_remove.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s1 i1 h1 hT1)) ?_
    rintro s2 ⟨⟨⟨⟨Q2, R2, h2⟩, hB2, f2⟩, -, -, hst2⟩, F2⟩
    have hrun : Runnable (L.mem s2 (stA i1)) := by
      rw [hst2 i1 hT1]; exact h1.runR _ h1.cur i1 hmem
    have hrel : (L.mem s1 (inqA i1) &&& sched.Q_RELEASE) ≠ 0#u64 := (h1.released i1 hT1).2 (by rw [h1.inR _ h1.cur i1 hmem]; exact hmem)
    refine WP.spec_bind (WP.spec_and (sched.possible_switch_to.sch s2 i1 Q2 R2 h2 hB2 (hS1.fr f2) hT1 hrun (fun h0 => by
      rw [f2.sc i1 hT1] at h0 ⊢; exact hB1.sact i1 hT1 (Or.inr (Or.inl hrel)) h0))
      (sched.possible_switch_to.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s2 i1 h2 hT1)) ?_
    rintro s3 ⟨⟨⟨hi3, hB3, f3⟩, -, -⟩, F3⟩
    simp only [WP.spec_ok]
    exact ⟨⟨hi3, hB3, f1.trans (f2.trans f3)⟩, F1.trans (F2.trans F3), by omega⟩
  · exact ⟨⟨⟨Q, R, h⟩, hB, Fr.refl _ _⟩, FootB.refl _⟩

theorem sched.schedule.sfootB {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    sched.schedule st ar s a ⦃ s' _ => ∃ rf : S × A, timer.fire st ar s a = ok rf ∧
      FootDU st T Cs Sg Scs Z (EH H) U s rf.1 ∧ SFootB st T Cs Sg Scs Z H rf.1 s' ⦄ := by
  unfold sched.schedule sched.awaken
  -- `awaken`
  refine WP.spec_bind (Pₘ := fun r => Good st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ ∃ rf : S × A,
      timer.fire st ar s a = ok rf ∧ FootDU st T Cs Sg Scs Z (EH H) U s rf.1 ∧ SFootB st T Cs Sg Scs Z H rf.1 r.1) ?_ ?_
  · refine WP.spec_bind (spec_eq' (timer.fire.tinvF hA IK hNt s a h.tinv hBA)) ?_
    rintro ⟨s1, a1⟩ ⟨hf1, ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩, F1⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (WP.spec_and (sched.awaken_loop.sch s1 _ Q1 R1 h1 hB1 hS1.sg)
      (sched.awaken_loop.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s1 _ Q1 R1 h1 hB1 hS1.sg)) ?_
    rintro s2 ⟨⟨P2, -⟩, F2⟩
    exact (WP.spec_ok _).2 ⟨P2.good hS1 hX1, (s1, a1), hf1, F1, F2.sfootB⟩
  rintro ⟨s1, a1⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩, rf, hrf, Fd, F1⟩
  -- `check_domain_time` does nothing with one domain
  unfold sched.check_domain_time sched.is_cur_domain_expired
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have hnd : ¬ ((1#u64) > (1#u64)) := by simp
  simp only [hnd, ↓reduceIte, bind_ok, Bool.false_eq_true]
  step with sched.action.spec as ⟨act, act_post⟩
  -- the action
  refine WP.spec_bind (Pₘ := fun r => Good st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ L.mem r.1 (scA (L.curW r.1)) ≠ 0#u64 ∧
      L.mem r.1 (scA (L.curW r.1)) ∈ Ac ∧ SFootB st T Cs Sg Scs Z H s1 r.1) ?_ ?_
  · split
    · rename_i hnr
      step with sched.cur_thread.spec as ⟨ct, ct_post⟩
      have hctT : ct ∈ T := by rw [ct_post]; exact h1.curT
      step with sched.is_schedulable.spec' as ⟨wr, wr_post⟩
      refine WP.spec_bind (Pₘ := fun s4 => Post st T Cs Ω H Sg Ac s1 s4 ∧ L.actionW s4 = L.actionW s1 ∧
          FootB st T Cs Sg Scs Z (EH H) s1 s4) ?_ ?_
      · split
        · exact WP.spec_mono (WP.spec_and (sched.enqueue.sch s1 ct Q1 R1 h1 hB1 hS1.sg hctT (fun _ => (wr_post ‹_›).2.2.1)
            (fun _ => (wr_post ‹_›).1) (fun _ => (wr_post ‹_›).2.1)
            (fun _ => (hS1.act _ (hX1.2.2.bound _ hctT (wr_post ‹_›).2.1).1).2 (wr_post ‹_›).2.2.2))
            (sched.enqueue.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s1 ct h1 hctT))
            fun s4 h4 => ⟨h4.1.1, h4.1.2.1, h4.2⟩
        · exact (WP.spec_ok _).2 ⟨⟨⟨Q1, R1, h1⟩, hB1, Fr.refl _ _⟩, rfl, FootB.refl _⟩
      rintro s4 ⟨⟨⟨Q4, R4, h4⟩, hB4, f4⟩, ea4, F4⟩
      have hS4 := hS1.fr f4
      have hX4 := hX1.fr f4
      have hact4 : L.actionW s4 = act := ea4.trans act_post.symm
      split
      · exact WP.spec_mono (WP.spec_and (sched.schedule_choose_new_thread.sch hA s4 a1 Q4 R4 h4 hB4 hS4 hX4)
          (sched.schedule_choose_new_thread.sfootB (Scs := Scs) (Z := Z) hA s4 a1 Q4 R4 h4 hB4 hS4.sg)) fun r hr => by
            obtain ⟨s', a'⟩ := r
            simp only [WP.uncurry'_pair] at hr ⊢
            exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, F4.sfootB.trans hr.2⟩
      rename_i hnc
      have hT : act ∈ T := by
        rcases h4.action with e | e | e
        · exfalso; rw [hact4] at e; rw [e, resume_val] at hnr; simp at hnr
        · exfalso; rw [hact4] at e; rw [e, choose_val] at hnc; simp at hnc
        · rw [hact4] at e; exact e
      have hbd : L.mem s4 (scA act) ≠ 0#u64 := by have := hB4.act (hact4 ▸ hT); rw [hact4] at this; exact this
      have L1 := WP.spec_and (cand_choose hA s4 a1 act Q4 R4 h4 hB4 hS4 hX4 hact4 hT true)
        (cand_choose.sfootB (Scs := Scs) (Z := Z) hA s4 a1 act Q4 R4 h4 hB4 hS4 hact4 hT true)
      have L3 := WP.spec_and (cand_choose hA s4 a1 act Q4 R4 h4 hB4 hS4 hX4 hact4 hT false)
        (cand_choose.sfootB (Scs := Scs) (Z := Z) hA s4 a1 act Q4 R4 h4 hB4 hS4 hact4 hT false)
      simp only [↓reduceIte, Bool.false_eq_true] at L1 L3
      replace L1 := WP.spec_mono L1 (P₁ := WP.uncurry' fun s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SFootB st T Cs Sg Scs Z H s1 s')
        fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, F4.sfootB.trans hr.2⟩
      replace L3 := WP.spec_mono L3 (P₁ := WP.uncurry' fun s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SFootB st T Cs Sg Scs Z H s1 s')
        fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, F4.sfootB.trans hr.2⟩
      have L2 : sched.switch_to_thread st ar s4 a1 act ⦃ s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SFootB st T Cs Sg Scs Z H s1 s' ⦄ :=
        WP.spec_mono (WP.spec_and (sched.switch_to_thread.sch hA s4 a1 act Q4 R4 h4 hB4 hS4.sg hT hbd
          (by have := hB4.actA (hact4 ▸ hT); rwa [hact4] at this))
          (sched.switch_to_thread.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) hA s4 a1 act h4 hT)) fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1.good hS4 hX4, by rw [hr.1.2.1, hr.1.1.fr.sc act hT]; exact hbd, by
            rw [hr.1.2.1, hr.1.1.fr.sc act hT]; have := hB4.actA (hact4 ▸ hT); rwa [hact4] at this,
            (F4.trans hr.2).sfootB⟩
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
      exact (WP.spec_ok _).2 ⟨⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩, hB1.resume e0, hB1.curA h1.curT e0, SFootB.refl _⟩
  rintro ⟨s3, a2⟩ ⟨⟨⟨Q3, R3, h3⟩, hB3, hS3, hX3⟩, hcb1, hcb2, F3⟩
  have hcb := And.intro hcb1 hcb2
  try simp only [WP.uncurry'_pair]
  -- resume, then switch the SC
  rw [resume_val]
  refine WP.spec_bind (WP.spec_and (sched.set_action.sch s3 0#u64 Q3 R3 h3 hB3 hS3.sg (Or.inl rfl)
    (fun hT => absurd hT (notT_small h3.tcbs (by simp))) (fun hT => absurd hT (notT_small h3.tcbs (by simp)))
    (fun _ => hcb) (fun hT => absurd hT (notT_small h3.tcbs (by simp))))
    (sched.set_action.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 0#u64 (h3.nodes _ h3.cur) h3.cur)) ?_
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
  refine WP.spec_bind (WP.spec_and (sched.switch_sched_context.free hA s4 a2 (zt := Z (L.mem s4 (scA (L.curW s4))))
    (zc := Z (L.cscW s4)) h4.cur hN4 h4.omega hcq
    (fun hne => ⟨htin, hS4.disj _ hcT hb4 hne⟩))
    (sched.switch_sched_context.fp hA s4 a2 (zt := Z (L.mem s4 (scA (L.curW s4))))
      (zc := Z (L.cscW s4))
      (B := SchedWB st T Cs Sg Scs Z H s4) h4.cur hN4 h4.omega
      hcq (fun hne => ⟨htin, hS4.disj _ hcT hb4 hne⟩)
      (Or.inl (kwB_node h4.cur (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])))
      (Or.inl (kwB_node h4.cur (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])))
      (Or.inl (kwB_node h4.cur (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])))
      (fun _ b _ hr => Or.inl (kwB_sc hts hr.inSC))
      (fun b _ hr => by
        rcases hr with hr | rfl
        · exact Or.inl (kwB_sc hcs hr.inSC)
        · exact Or.inl (kwB_sc hcs (show InSC (L.cscW s4) (Z (L.cscW s4))
            (core.num.U64.wrapping_add (L.cscW s4) layout.sc.CONSUMED) from
            ⟨by rw [hvc]; omega, by rw [hvc, hcv]; omega⟩))))) ?_
  rintro ⟨s5, a3⟩ ⟨w5, w5', -, -, -⟩
  simp only [WP.uncurry'_pair] at w5 w5' ⊢
  have h5 := (free_step h4 hB4 w5).1
  step with LawfulStore.cur_cpu_spec as ⟨c, c_post⟩
  step with obj.node_get.spec as ⟨i, _⟩
  refine WP.spec_bind (Pₘ := fun r => SchedQueuesInv st T Cs Ω H r.1 Q4 R4 ∧ SFootB st T Cs Sg Scs Z H s5 r.1) ?_ ?_
  · split
    · have hB5 := (free_step h4 hB4 w5).2
      refine WP.spec_bind (WP.spec_and (sched.set_next_interrupt.free (Ω := Ω) hA s5 a3 h5.cur (h5.nodes _ h5.cur))
        (sched.set_next_interrupt.fp hA s5 a3 (B := SchedWB st T Cs Sg Scs Z H s5) (h5.nodes _ h5.cur)
          (Or.inl (kwB_node h5.cur (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED]))))) ?_
      rintro ⟨s7, a5⟩ ⟨w7, w7'⟩
      simp only [WP.uncurry'_pair] at w7 w7' ⊢
      have h7 := free_step h5 hB5 w7
      step with obj.node_set.spec as ⟨s8, s8_post⟩
      try simp only [WP.spec_ok]
      have w8 : WritesIn st s5 s8 (L.Free s5 Ω Cs) := by
        rw [s8_post, c_post]
        exact w7.free_trans (free_node_write w7.1 h5.cur (h5.nodes _ h5.cur)
          (by simp [layout.node.REPROGRAM, LowFree]))
      have hN7 : NodePlaced st T s7 (L.cpu s7) := by rw [w7.2.1]; exact (h5.nodes _ h5.cur).ksb w7.1
      have F8 : SFootB st T Cs Sg Scs Z H s7 s8 := by
        rw [s8_post, c_post, ← w7.2.1]
        exact (footB_node (Es := EH H) hN7 (by rw [w7.2.1]; exact h5.cur) (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])).sfootB
      exact ⟨(free_step h5 hB5 w8).1, w7'.trans F8 |>.mono fun b hb => Or.elim hb id fun hb => SchedWB.ksb w7'.1 hb⟩
    · exact (WP.spec_ok _).2 ⟨h5, SFootB.refl _⟩
  rintro ⟨s6, a4⟩ ⟨h6, F6⟩
  try simp only [WP.uncurry'_pair]
  exact WP.spec_mono (smp.send_pending.fp hA s6 a4 (B := SchedWB st T Cs Sg Scs Z H s6) (h6.nodes _ h6.cur)
      (Or.inl (kwB_node h6.cur (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING])))) fun r w => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at w ⊢
    exact ⟨rf, hrf, Fd, F1.trans (F3.trans ((F4.sfootB.trans w5').trans (F6.trans w)))⟩

/-- **`schedule` keeps every TCB's buffer-lookup words** (module docstring). -/
theorem sched.schedule.ibFr {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    sched.schedule st ar s a ⦃ s' _ => IbFr (L := L) T s s' ⦄ := by
  refine WP.spec_mono (sched.schedule.sfootB hA IK hNt s a h hBA) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨rf, hrf, -, F⟩ := hh
  have Hf := timer.fire.tinv hA IK hNt s a h hBA
  rw [hrf, WP.spec_ok] at Hf
  obtain ⟨⟨⟨Q1, R1, h1⟩, -, hX1, -, hSg1⟩, I1⟩ := Hf
  have K : BufKeep st T rf.1 s' := BufKeep.of_writes h1.tcbs F fun b hal hb => by
    rcases hb with hk | ⟨o, ho, h8, e⟩
    · exact kwB_notBufW h1 hX1.1 hSg1.sub (fun _ he => he) hal hk
    · subst e; exact notBufW_out h1.tcbs (h1.omega _ (hSg1.ksΩ o ho h8))
  exact I1.trans (IbFr.of_bufKeep F.1 K)

end

end Fl4Proofs.P1
