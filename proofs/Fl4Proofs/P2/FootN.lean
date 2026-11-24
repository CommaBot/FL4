/-
P2 (p2j, KWN step 1): **`KWN`, the core-separated footprint** (built beside
P1's `KW` the way KENTRY-PLAN a6f built `KWB`; `KW`, `Foot` and every P1
lemma are untouched).

`KW` (P1 `QueueFoot`) admits a write to any node word of any core but the
debug-list head. `KWN` is `KW` without the **node identity words** `IdW`:
every core's `IDLE_THREAD` (offset 8) and `IDLE_SC` (32), and, of every core
other than the executing one, `CUR_THREAD` (0), `SCHED_ACTION` (16) and
`CUR_SC` (24). No kernel operation writes them (the idle words are written
once, at boot, `create_idle_thread`; a core's current thread, action and SC
only by that core, `smp::stall` included, which runs at the stalled core's
view). A `KWN` footprint (`FootN`) therefore keeps every core's idle thread
and idle SC, and every other core's current thread, action and current SC
(`FootN.idKeep`): the frame the stall (`P2/StallAt.lean`) and the all-cores
invariant need.

Here: the definitions and their API (`FootN.refl`/`trans`/`foot`, `FootN.of'`,
`footN_wr`/`footN_field`/`footN_node`, `notIdW_field`/`notIdW_node`/
`notIdW_out`), and the `.kwN` versions of P1's scheduler-queue footprints:
`QFoot.kwN`, `enqueue`, `dequeue`, `release_remove`, `set_action`,
`schedule_tcb`, `set_thread_state`, `reschedule_required`,
`possible_switch_to`, the two `unblock_sporadic`, `reply_unlink`. No premise.
-/
import Fl4Proofs.P1.QueueFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- The node offsets no kernel operation writes: the idle thread (8) and
idle SC (32) of every core; `CUR_THREAD` (0), `SCHED_ACTION` (16) and
`CUR_SC` (24) of a core other than the executing one (`cur` false). -/
def IdOff (cur : Prop) (o : Nat) : Prop := o = 8 ∨ o = 32 ∨ (¬ cur ∧ (o = 0 ∨ o = 16 ∨ o = 24))

theorem idOff_cur {c : U64} {o : Nat} (h8 : o ≠ 8) (h32 : o ≠ 32) : ¬ IdOff (c = c) o := by
  rintro (e | e | ⟨hne, -⟩)
  · exact h8 e
  · exact h32 e
  · exact hne rfl

theorem idOff_ge {p : Prop} {o : Nat} (h : 40 ≤ o) : ¬ IdOff p o := by
  rintro (e | e | ⟨-, e | e | e⟩) <;> omega

theorem IdOff.lt {p : Prop} {o : Nat} (h : IdOff p o) : o < 40 := by
  rcases h with e | e | ⟨-, e | e | e⟩ <;> omega

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Es : Set U64} {Ac : Set U64}

/-- The node identity words at `s0` (`IdOff`). -/
def IdW (st : machine.Store S) [L : LawfulStore st] (Cs : Set U64) (s0 : S) (b : U64) : Prop :=
  ∃ c ∈ Cs, ∃ o : U64, IdOff (c = L.cpu s0) o.val ∧ b = L.nodeAt s0 c o

/-- `KW` without the node identity words. -/
def KWN (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64)
    (s0 : S) (b : U64) : Prop :=
  KW st T Cs Sg Scs Z Es s0 b ∧ ¬ IdW st Cs s0 b

/-- A footprint inside `KWN`. -/
abbrev FootN (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64)
    (s s' : S) : Prop :=
  WritesIn st s s' (KWN st T Cs Sg Scs Z Es s)

theorem IdW.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (hc : L.cpu s1 = L.cpu s0)
    (h : IdW st Cs s0 b) : IdW st Cs s1 b := by
  obtain ⟨c, hcs, o, ho, e⟩ := h
  exact ⟨c, hcs, o, by rw [hc]; exact ho, by rw [e, nodeAt_of_ksb hk]⟩

theorem FootN.foot {s s' : S} (h : FootN st T Cs Sg Scs Z Es s s') : Foot st T Cs Sg Scs Z Es s s' :=
  WritesIn.mono h fun _ hb => hb.1

theorem FootN.refl (s : S) : FootN st T Cs Sg Scs Z Es s s := WritesIn.refl _ _

theorem FootN.trans {s₁ s₂ s₃ : S} (h₁ : FootN st T Cs Sg Scs Z Es s₁ s₂) (h₂ : FootN st T Cs Sg Scs Z Es s₂ s₃) :
    FootN st T Cs Sg Scs Z Es s₁ s₃ :=
  WritesIn.mono (WritesIn.trans h₁ h₂) fun b hb =>
    Or.elim hb id fun hb => ⟨KW.ksb h₁.1 hb.1, fun hi => hb.2 (hi.ksb h₁.1 h₁.2.1)⟩

theorem FootN.of' {s s' : S} {B : U64 → Prop} (h : WritesIn st s s' B)
    (hB : ∀ b, Aligned b → B b → KWN st T Cs Sg Scs Z Es s b) : FootN st T Cs Sg Scs Z Es s s' :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb fun hh => hn (hB b hb hh)⟩

/-- **A `KWN` footprint keeps the node identity words.** -/
theorem FootN.idKeep {s s' : S} (f : FootN st T Cs Sg Scs Z Es s s') {b : U64} (hb : Aligned b)
    (hi : IdW st Cs s b) : L.mem s' b = L.mem s b :=
  f.mem_eq hb fun hk => hk.2 hi

/-! ## Words outside `IdW` -/

theorem IdW.lt {s : S} {b : U64} (h : IdW st Cs s b) :
    ∃ c ∈ Cs, ∃ o : U64, IdOff (c = L.cpu s) o.val ∧ o.val < 40 ∧ b = L.nodeAt s c o := by
  obtain ⟨c, hc, o, ho, e⟩ := h
  exact ⟨c, hc, o, ho, ho.lt, e⟩

theorem notIdW_field {s : S} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c) {y K : U64} (hy : y ∈ T)
    (hK : K.val < 4096) : ¬ IdW st Cs s (core.num.U64.wrapping_add y K) := by
  intro h
  obtain ⟨c, hc, o, -, ho, e⟩ := h.lt
  exact node_ne_field (NP c hc) (by omega) hy (hT y hy) hK e.symm

theorem notIdW_node {s : S} (NP : ∀ c ∈ Cs, NodePlaced st T s c) {c o : U64} (hc : c ∈ Cs)
    (ho : o.val < 4288) (hn : ¬ IdOff (c = L.cpu s) o.val) : ¬ IdW st Cs s (L.nodeAt s c o) := by
  intro h
  obtain ⟨c', hc', o', ho', hlt, e⟩ := h.lt
  by_cases hcc : c = c'
  · subst hcc
    by_cases hoo : o.val = o'.val
    · rw [hoo] at hn; exact hn ho'
    · exact node_ne_node (NP c hc) (NP c hc') ho (by omega) (fun _ => hoo) (congrArg UScalar.val e)
  · exact node_ne_node (NP c hc) (NP c' hc') ho (by omega) (fun h => absurd h hcc) (congrArg UScalar.val e)

theorem notIdW_out {s : S} (NP : ∀ c ∈ Cs, NodePlaced st T s c) {a : U64} (ha : OutsideObjs st T Cs s a) :
    ¬ IdW st Cs s a := by
  intro h
  obtain ⟨c, hc, o, -, ho, e⟩ := h.lt
  exact out_ne_node ha hc (NP c hc) (by omega) (congrArg UScalar.val e).symm

theorem footN_wr {s : S} {a v : U64} (ha : Aligned a) (hk : KWN st T Cs Sg Scs Z Es s a) :
    FootN st T Cs Sg Scs Z Es s (L.wr s a v) :=
  (writesIn_wr ha).mono fun b hb => hb ▸ hk

theorem footN_field {s : S} {y K v : U64} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hy : y ∈ T)
    (hK : 192 ≤ K.val) (hK' : K.val < 4096) (hK8 : K.val % 8 = 0) (hKd : K.val ≠ 3576 ∧ K.val ≠ 3584) :
    FootN st T Cs Sg Scs Z Es s (L.wr s (core.num.U64.wrapping_add y K) v) :=
  footN_wr (field_aligned (hT y hy) hK' hK8) ⟨kw_field hy hK hK' hKd, notIdW_field hT NP hy hK'⟩

theorem footN_node {s : S} {c o v : U64} (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : c ∈ Cs) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (h88 : o.val ≠ 88) (hn : ¬ IdOff (c = L.cpu s) o.val) :
    FootN st T Cs Sg Scs Z Es s (L.wr s (L.nodeAt s c o) v) :=
  footN_wr (nodeAt_aligned (NP c hc) ho h8) ⟨kw_node hc ho h88, notIdW_node NP hc ho hn⟩

theorem LawfulStore.QFoot.kwN {s : S} {W : List U64} {c : U64} {P : Nat → Prop} {t b : U64}
    (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hW : ∀ w ∈ W, w ∈ T)
    (hc : c ∈ Cs) (hcpu : L.cpu s ∈ Cs) (ht : t ∈ T) (hP : ∀ o, P o → o ≠ 88)
    (hPi : ∀ o, P o → ¬ IdOff (c = L.cpu s) o) (h : L.QFoot s W c P t b) :
    KWN st T Cs Sg Scs Z Es s b := by
  refine ⟨h.kw hW hc hcpu ht hP, ?_⟩
  rcases h with ⟨w, hw, e | e⟩ | ⟨o, hPo, ho, -, e⟩ | e | ⟨o, hPo, ho, -, e⟩ <;> subst e
  · rw [nextA_eq']; exact notIdW_field hT NP (hW w hw) (by simp [nextOff])
  · rw [prevA_eq']; exact notIdW_field hT NP (hW w hw) (by simp [prevOff])
  · exact notIdW_node NP hc ho (hPi _ hPo)
  · rw [inqA_eq]; exact notIdW_field hT NP ht (by simp)
  · have h120 : o.val = 120 := hPo
    exact notIdW_node NP hcpu ho (idOff_ge (by omega))

/-! ## The scheduler-queue operations -/

section queues
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

theorem sched.enqueue.kwN (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.enqueue st s t ⦃ s' => FootN st T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_mono (sched.enqueue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (fun h0 => h.notQ ht h0 hc hp)) fun s' hh => hh.1.mono fun b hb =>
      LawfulStore.QFoot.kwN h.tcbs h.nodes ?_ hc h.cur ht (fun o ho => by omega) (fun o ho => idOff_ge (by omega)) hb
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact (hR1.1.rel _ hp).mem w hw

theorem sched.dequeue.kwN (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' => FootN st T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  exact WP.spec_mono (sched.dequeue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (h.queued t ht).1) fun s' hh => hh.1.mono fun b hb =>
      LawfulStore.QFoot.kwN h.tcbs h.nodes (hR1.1.rel _ hp).mem hc h.cur ht (fun o ho => by omega)
        (fun o ho => idOff_ge (by omega)) hb

theorem sched.release_remove.kwN (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.release_remove st s t ⦃ s' => FootN st T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  exact WP.spec_mono (sched.release_remove.foot s t _ h.tcbs ht (h.nodes _ hc) (h.nodes _ h.cur) (h.release _ hc)
    (h.released t ht).1) fun s' hh => hh.1.mono fun b hb =>
      LawfulStore.QFoot.kwN h.tcbs h.nodes (h.release _ hc).mem hc h.cur ht
        (fun o ho => by unfold RelOffs at ho; omega)
        (fun o ho => idOff_ge (by unfold RelOffs at ho; omega)) hb

theorem sched.set_action.kwN (s : S) (v : U64) (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs) :
    sched.set_action st s v ⦃ s' => FootN st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.set_action.spec s v) fun s' e => by
    subst e
    exact footN_node NP hc (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)
      (idOff_cur (by rw [act_val]; omega) (by rw [act_val]; omega))

theorem sched.schedule_tcb.kwN (s : S) (t : obj.Tcb) (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs) :
    sched.schedule_tcb st s t ⦃ s' => FootN st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.schedule_tcb
  step with sched.cur_thread.spec as ⟨t1, e1⟩
  step with tcb_eq.blk as ⟨b, eb⟩
  split
  · step with sched.action.spec as ⟨i, ei⟩
    split
    · step with sched.is_schedulable.spec as ⟨b1, eb1⟩
      split
      · exact (WP.spec_ok _).2 (FootN.refl _)
      · exact sched.set_action.kwN s _ NP hc
    · exact (WP.spec_ok _).2 (FootN.refl _)
  · exact (WP.spec_ok _).2 (FootN.refl _)

theorem sched.set_thread_state.kwN (s : S) (t : obj.Tcb) (v : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (ht : t ∈ T) : sched.set_thread_state st s t v ⦃ s' => FootN st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.set_thread_state
  refine WP.spec_bind (obj.Tcb.set_state.spec s t v) fun s1 e1 => ?_
  subst e1
  refine WP.spec_mono (sched.schedule_tcb.kwN (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) _ t
    (fun c hc => (h.nodes c hc).ksb (L.ksb_wr _ _ _)) (by rw [LawfulStore.cpu_wr]; exact h.cur)) fun s2 f2 => ?_
  have f1 : FootN st T Cs Sg Scs Z Es s (L.wr s (stA t) v) := by
    rw [stA_eq]; exact footN_field h.tcbs h.nodes ht (by simp) (by simp) (by simp) (by simp)
  exact f1.trans f2

theorem sched.reschedule_required.kwN (s : S) (h : SchedQueuesInvX st T Cs Ω H X s Q R) :
    sched.reschedule_required st s ⦃ s' => FootN st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  have hpart : (if (act != sched.ACTION_RESUME_CURRENT) = true then
      if (act != sched.ACTION_CHOOSE_NEW) = true then do
        let b ← sched.is_schedulable st s act
        if b = true then sched.enqueue st s act else ok s
      else ok s
    else ok s) ⦃ s1 => FootN st T Cs Sg Scs Z Es s s1 ⦄ := by
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
        · exact sched.enqueue.kwN s act h hT
        · exact (WP.spec_ok _).2 (FootN.refl _)
      · exact (WP.spec_ok _).2 (FootN.refl _)
    · exact (WP.spec_ok _).2 (FootN.refl _)
  refine WP.spec_bind hpart fun s1 f1 => ?_
  exact WP.spec_mono (sched.set_action.kwN s1 _ (fun c hc => (h.nodes c hc).ksb f1.1)
    (by rw [f1.2.1]; exact h.cur)) fun s2 f2 => f1.trans f2

theorem sched.possible_switch_to.kwN (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.possible_switch_to st s t ⦃ s' => FootN st T Cs Sg Scs Z Es s s' ⦄ := by
  have hST : P0.StoreTotal st := L.total
  unfold sched.possible_switch_to sched.cur_domain
  step as ⟨i, ei⟩
  split
  · exact (WP.spec_ok _).2 (FootN.refl _)
  step as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (FootN.refl _)
  step as ⟨i1, ei1⟩
  step as ⟨i2, ei2⟩
  split
  · exact sched.enqueue.kwN s t h ht
  step as ⟨i3, ei3⟩
  step as ⟨i4, ei4⟩
  split
  · exact sched.enqueue.kwN s t h ht
  step as ⟨i5, ei5⟩
  split
  · refine WP.spec_bind (WP.spec_and (sched.reschedule_required.inv s Q R h)
      (sched.reschedule_required.kwN (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s h)) ?_
    rintro s1 ⟨⟨⟨Q1, h1⟩, -, -⟩, f1⟩
    exact WP.spec_mono (sched.enqueue.kwN s1 t h1 ht) fun s2 f2 => f1.trans f2
  · exact sched.set_action.kwN s _ h.nodes h.cur

/-- An SC ring word is no node identity word. -/
theorem notIdW_ring {s : S} {i b : U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hiS : i ∈ Scs) (hb : Aligned b) (hr : InRing i (Z i) b) :
    ¬ IdW st Cs s b :=
  notIdW_out h.nodes (h.omega _ (hX.1.scW i hiS b hb hr.inSC))

theorem endpoint.unblock_sporadic.kwN (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T) :
    endpoint.unblock_sporadic st s t ⦃ s' => FootN st T Cs Sg Scs Z Es s s' ⦄ := by
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
      refine WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 => FootN.of' w3 fun b hb hh => ?_
      rcases hh with hh | rfl
      · exact ⟨hh.kw hiS, notIdW_ring h hX hiS hb hh⟩
      · exact ⟨kw_node h.cur (by rw [rp]; omega) (by rw [rp]; omega),
          notIdW_node h.nodes h.cur (by rw [rp]; omega) (idOff_ge (by rw [rp]; omega))⟩
    · exact (WP.spec_ok _).2 (FootN.refl _)
  · exact (WP.spec_ok _).2 (FootN.refl _)

theorem notification.unblock_sporadic.kwN (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T) :
    notification.unblock_sporadic st s t ⦃ s' => FootN st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold notification.unblock_sporadic
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
      refine WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 => FootN.of' w3 fun b hb hh => ?_
      rcases hh with hh | rfl
      · exact ⟨hh.kw hiS, notIdW_ring h hX hiS hb hh⟩
      · exact ⟨kw_node h.cur (by rw [rp]; omega) (by rw [rp]; omega),
          notIdW_node h.nodes h.cur (by rw [rp]; omega) (idOff_ge (by rw [rp]; omega))⟩
    · exact (WP.spec_ok _).2 (FootN.refl _)
  · exact (WP.spec_ok _).2 (FootN.refl _)

theorem ipc.reply_unlink.kwN (s : S) (r t : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hr : r ∈ Rp) (ht : t ∈ T) :
    ipc.reply_unlink st s r t ⦃ s' => FootN st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold ipc.reply_unlink
  refine WP.spec_bind (obj.Reply.set_tcb.spec s r 0#u64) fun s1 e1 => ?_
  subst e1
  have hm : rTcbA r ∈ Ω := hsub _ (hX.1.tcbW hr)
  have ha := (h.omega _ hm).1
  have h1 := inv_of_free h ((writesIn_wr (v := 0#u64) ha).mono fun b hb => hb ▸ Or.inl hm)
  exact WP.spec_mono (sched.set_thread_state.kwN _ t _ h1 ht) fun s2 f2 =>
    (footN_wr ha ⟨kw_sg (hX.1.tcbW hr), notIdW_out h.nodes (h.omega _ hm)⟩).trans f2

end queues

end

end Fl4Proofs.P1
