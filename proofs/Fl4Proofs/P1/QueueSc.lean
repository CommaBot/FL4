/-
P1: the refill code (sporadic.rs) writes only inside its scheduling context
(and the current core's `REPROGRAM` / `CONSUMED` words): footprints for
`refill_unblock_check`, `refill_budget_check` and `commit_time`, so that
`schedule` can be shown to leave the queues alone.
-/
import Fl4Proofs.P1.QueueCallers
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- The words of the SC object at `sc` of size `2 ^ sb`. -/
def InSC (sc : U64) (sb : Nat) (b : U64) : Prop := sc.val ≤ b.val ∧ b.val < sc.val + 2 ^ sb
/-- The words of the SC from `REFILL_MAX` on (the ring header and the ring):
all the refill code writes besides `CONSUMED`. -/
def InRing (sc : U64) (sb : Nat) (b : U64) : Prop := sc.val + 72 ≤ b.val ∧ b.val < sc.val + 2 ^ sb
theorem InRing.inSC {sc : U64} {sb : Nat} {b : U64} (h : InRing sc sb b) : InSC sc sb b := ⟨by
  have := h.1; omega, h.2⟩

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {s : S} {sc : obj.Sc} {sb : Nat}

theorem RefillsWF.frame_putS {i : U64} {r : sporadic.Refill} (h : RefillsWF st s sc sb)
    (hi : i.val < (L.rmax s sc).val) : WritesIn st s (L.putS s sc i r) (InRing sc sb) := by
  obtain ⟨h8, hm, hfit⟩ := h.bounds
  obtain ⟨-, -, -, -, -, hin⟩ := h.inside
  obtain ⟨e1, e2, e3⟩ := hin i hi
  have a1 : Aligned (rtA sc i) := by unfold Aligned; rw [e1]; omega
  have a2 : Aligned (raA sc i) := by unfold Aligned; rw [e2]; omega
  exact ((writesIn_wr a1).trans (writesIn_wr a2)).mono fun b hb => by
    rcases hb with rfl | rfl
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩

theorem RefillsWF.frame_hdr {a v : U64} (h : RefillsWF st s sc sb)
    (ha : a = headA sc ∨ a = tailA sc ∨ a = periodA sc ∨ a = maxA sc ∨
      a = core.num.U64.wrapping_add sc layout.sc.CONSUMED) :
    WritesIn st s (L.wr s a v) (InSC sc sb) := by
  obtain ⟨h8, hm, hfit⟩ := h.bounds
  obtain ⟨h96, -, -, -, -, -⟩ := h.inside
  have hv : a.val = sc.val + 80 ∨ a.val = sc.val + 88 ∨ a.val = sc.val ∨ a.val = sc.val + 72 ∨
      a.val = sc.val + 8 := by
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · left; addr
    · right; left; addr
    · right; right; left; addr
    · right; right; right; left; addr
    · right; right; right; right
      simp [layout.sc.CONSUMED, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hal : Aligned a := by unfold Aligned; omega
  exact (writesIn_wr hal).mono fun b hb => by subst hb; exact ⟨by omega, by omega⟩

theorem RefillsWF.frame_hdrR {a v : U64} (h : RefillsWF st s sc sb)
    (ha : a = headA sc ∨ a = tailA sc ∨ a = maxA sc) :
    WritesIn st s (L.wr s a v) (InRing sc sb) := by
  obtain ⟨h8, hm, hfit⟩ := h.bounds
  obtain ⟨h96, -, -, -, -, -⟩ := h.inside
  have hv : a.val = sc.val + 80 ∨ a.val = sc.val + 88 ∨ a.val = sc.val + 72 := by
    rcases ha with rfl | rfl | rfl
    · left; addr
    · right; left; addr
    · right; right; addr
  have hal : Aligned a := by unfold Aligned; omega
  exact (writesIn_wr hal).mono fun b hb => by subst hb; exact ⟨by omega, by omega⟩

theorem WritesIn.trans1 {s₁ s₂ s₃ : S} {A : U64 → Prop} (h₁ : WritesIn st s₁ s₂ A) (h₂ : WritesIn st s₂ s₃ A) :
    WritesIn st s₁ s₃ A := (h₁.trans h₂).mono fun _ hb => by rcases hb with hb | hb <;> exact hb

/-! ## The ring operations stay inside the SC -/

theorem sporadic.set_head.fr (r : sporadic.Refill) (h : RefillsWF st s sc sb) :
    sporadic.set_head st s sc r ⦃ s' => RefillsWF st s' sc sb ∧ WritesIn st s s' (InRing sc sb) ⦄ :=
  WP.spec_mono (sporadic.set_head.eq s sc r) fun s' e => by
    subst e; exact ⟨h.putS h.head_lt, h.frame_putS h.head_lt⟩

theorem sporadic.set_tail.fr (r : sporadic.Refill) (h : RefillsWF st s sc sb) :
    sporadic.set_tail st s sc r ⦃ s' => RefillsWF st s' sc sb ∧ WritesIn st s s' (InRing sc sb) ⦄ := by
  unfold sporadic.set_tail
  step with obj.Sc.refill_tail.spec as ⟨t, t_post⟩
  step with sporadic.put.spec as ⟨s', s'_post⟩
  subst t_post s'_post
  exact ⟨h.putS h.tail_lt, h.frame_putS h.tail_lt⟩

theorem sporadic.pop_head.fr (h : RefillsWF st s sc sb) :
    sporadic.pop_head st s sc ⦃ _ s' => RefillsWF st s' sc sb ∧ WritesIn st s s' (InRing sc sb) ⦄ := by
  unfold sporadic.pop_head
  step with sporadic.head.spec as ⟨r, _⟩
  step with obj.Sc.refill_head.spec as ⟨hd, hd_post⟩
  step with sporadic.next_index.spec as ⟨n, n_post⟩
  step with obj.Sc.set_refill_head.spec as ⟨s1, s1_post⟩
  subst hd_post n_post s1_post
  exact ⟨h.wr_head (nextIdx_lt h.head_lt), h.frame_hdrR (Or.inl rfl)⟩

theorem sporadic.add_tail.fr (r : sporadic.Refill) (h : RefillsWF st s sc sb) :
    sporadic.add_tail st s sc r ⦃ s' => RefillsWF st s' sc sb ∧ WritesIn st s s' (InRing sc sb) ⦄ := by
  unfold sporadic.add_tail
  step with obj.Sc.refill_tail.spec as ⟨t, t_post⟩
  step with sporadic.next_index.spec as ⟨nt, nt_post⟩
  step with obj.Sc.set_refill_tail.spec as ⟨s1, s1_post⟩
  step with sporadic.put.spec as ⟨s2, s2_post⟩
  subst t_post nt_post s1_post s2_post
  have h1 := h.wr_tail (v := nextIdx (L.rmax s sc) (L.rtail s sc)) (nextIdx_lt h.tail_lt)
  obtain ⟨h8, -, -⟩ := h.bounds
  have hi : (nextIdx (L.rmax s sc) (L.rtail s sc)).val < (L.rmax (L.wr s (tailA sc) (nextIdx (L.rmax s sc)
      (L.rtail s sc))) sc).val := by rw [rmax_wr_tail h8]; exact nextIdx_lt h.tail_lt
  exact ⟨h1.putS hi, (h.frame_hdrR (Or.inr (Or.inl rfl))).trans1 (h1.frame_putS hi)⟩

theorem sporadic.maybe_add_empty_tail.fr (h : RefillsWF st s sc sb) :
    sporadic.maybe_add_empty_tail st s sc ⦃ s' => RefillsWF st s' sc sb ∧ WritesIn st s s' (InRing sc sb) ⦄ := by
  unfold sporadic.maybe_add_empty_tail
  step with sporadic.is_round_robin.spec as ⟨b, _⟩
  split
  · step with sporadic.head.spec as ⟨r, _⟩
    exact sporadic.add_tail.fr _ h
  · simp only [WP.spec_ok]; exact ⟨h, WritesIn.refl _ _⟩

theorem sporadic.schedule_used.fr (r : sporadic.Refill) (h : RefillsWF st s sc sb) :
    sporadic.schedule_used st s sc r ⦃ s' => RefillsWF st s' sc sb ∧ WritesIn st s s' (InRing sc sb) ⦄ := by
  unfold sporadic.schedule_used
  step with sporadic.tail.spec as ⟨t, _⟩
  step as ⟨i, _⟩
  split
  · step as ⟨i1, _⟩
    exact sporadic.set_tail.fr _ h
  · step with sporadic.full.spec as ⟨b, _⟩
    split
    · step as ⟨i1, _⟩
      step as ⟨i2, _⟩
      exact sporadic.set_tail.fr _ h
    · exact sporadic.add_tail.fr _ h

attribute [local step] sporadic.set_head.fr sporadic.set_tail.fr sporadic.pop_head.fr sporadic.add_tail.fr
  sporadic.maybe_add_empty_tail.fr sporadic.schedule_used.fr

theorem sporadic.budget_check_loop0.fr (mrt period usage fuel : U64) (h : RefillsWF st s sc sb) :
    sporadic.budget_check_loop0 st s sc mrt period usage fuel ⦃ s' _ =>
      RefillsWF st s' sc sb ∧ WritesIn st s s' (InRing sc sb) ⦄ := by
  unfold sporadic.budget_check_loop0
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => RefillsWF st x.1 sc sb ∧ WritesIn st s x.1 (InRing sc sb))
  · rintro ⟨x0, x1, x2⟩ ⟨hx, hw⟩
    simp only at hx hw
    unfold sporadic.budget_check_loop0.body
    step*
    refine WP.spec_bind (Pₘ := fun s1 => RefillsWF st s1 sc sb ∧ WritesIn st x0 s1 (InRing sc sb)) ?_ ?_
    · split
      · step as ⟨i1, _⟩
        exact sporadic.set_head.fr _ hx
      · refine WP.spec_bind (sporadic.pop_head.fr hx) ?_
        rintro ⟨old, s2⟩ ⟨h2, w2⟩
        step as ⟨i1, _⟩
        exact WP.spec_mono (sporadic.schedule_used.fr _ h2) fun s3 ⟨h3, w3⟩ => ⟨h3, w2.trans1 w3⟩
    · rintro s1 ⟨h1, w1⟩
      step*
      exact ⟨h1, hw.trans1 w1, by omega⟩
  · exact ⟨h, WritesIn.refl _ _⟩

theorem sporadic.budget_check_loop1.fr (mb fuel2 : U64) (h : RefillsWF st s sc sb) :
    sporadic.budget_check_loop1 st s sc mb fuel2 ⦃ s' => RefillsWF st s' sc sb ∧ WritesIn st s s' (InRing sc sb) ⦄ := by
  unfold sporadic.budget_check_loop1
  apply loop.spec_decr_nat (measure := fun x => x.2.val)
    (inv := fun x => RefillsWF st x.1 sc sb ∧ WritesIn st s x.1 (InRing sc sb))
  · rintro ⟨x0, x1⟩ ⟨hx, hw⟩
    simp only at hx hw
    unfold sporadic.budget_check_loop1.body
    step*
    exact ⟨s2_post, (hw.trans1 old_post1).trans1 s2_post1, by omega⟩
  · exact ⟨h, WritesIn.refl _ _⟩

theorem sporadic.unblock_check_loop.fr (fuel : U64) (h : RefillsWF st s sc sb) :
    sporadic.unblock_check_loop st s sc fuel ⦃ s' => RefillsWF st s' sc sb ∧ WritesIn st s s' (InRing sc sb) ⦄ := by
  unfold sporadic.unblock_check_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val)
    (inv := fun x => RefillsWF st x.1 sc sb ∧ WritesIn st s x.1 (InRing sc sb))
  · rintro ⟨x0, x1⟩ ⟨hx, hw⟩
    simp only at hx hw
    unfold sporadic.unblock_check_loop.body
    step*
    exact ⟨s2_post, (hw.trans1 old_post1).trans1 s2_post1, by omega⟩
  · exact ⟨h, WritesIn.refl _ _⟩

/-- `refill_unblock_check` writes inside the SC and the current core's
`REPROGRAM`. -/
theorem sporadic.unblock_check.fr (h : RefillsWF st s sc sb)
    (hrep : Aligned (L.nodeA s layout.node.REPROGRAM) ∧ Outside (L.nodeA s layout.node.REPROGRAM) sc sb) :
    sporadic.unblock_check st s sc ⦃ s' =>
      WritesIn st s s' (fun b => InRing sc sb b ∨ b = L.nodeA s layout.node.REPROGRAM) ⦄ := by
  unfold sporadic.unblock_check
  step with sporadic.is_round_robin.spec as ⟨b, _⟩
  split
  · simp only [WP.spec_ok]; exact WritesIn.refl _ _
  step with sporadic.ready.spec as ⟨b1, _⟩
  split
  · step with sporadic.cur_time.spec as ⟨now, _⟩
    step with sporadic.head.spec as ⟨hd, _⟩
    refine WP.spec_bind (sporadic.set_head.fr _ h) ?_
    rintro s1 ⟨h1, w1⟩
    step with LawfulStore.cur_cpu_spec as ⟨cpu, cpu_post⟩
    step with obj.node_set.spec as ⟨s2, s2_post⟩
    have e : L.nodeAt s1 cpu layout.node.REPROGRAM = L.nodeA s layout.node.REPROGRAM := by
      rw [nodeAt_of_ksb w1.1, cpu_post, w1.2.1]; rfl
    rw [e] at s2_post
    have h2 : RefillsWF st s2 sc sb := by subst s2_post; exact h1.wr_out hrep.1 hrep.2
    have w2 : WritesIn st s1 s2 (· = L.nodeA s layout.node.REPROGRAM) := by subst s2_post; exact writesIn_wr hrep.1
    step with obj.Sc.refill_max.spec as ⟨i, _⟩
    step as ⟨fuel, _⟩
    refine WP.spec_mono (sporadic.unblock_check_loop.fr fuel h2) fun s3 ⟨_, w3⟩ => ?_
    exact ((w1.trans w2).trans w3).mono fun b hb => by
      rcases hb with (hb | hb) | hb
      · exact Or.inl hb
      · exact Or.inr hb
      · exact Or.inl hb
  · simp only [WP.spec_ok]; exact WritesIn.refl _ _

/-- `refill_budget_check` writes inside the current SC. -/
theorem sporadic.budget_check.fr {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A)
    (usage : U64) (h : RefillsWF st s sc sb) (hcur : L.mem s (L.nodeA s layout.node.CUR_SC) = sc) :
    sporadic.budget_check st ar s a usage ⦃ s' => WritesIn st s s' (InRing sc sb) ⦄ := by
  unfold sporadic.budget_check
  step with LawfulStore.cur_cpu_spec as ⟨i, i_post⟩
  step with obj.node_get.spec as ⟨i1, i1_post⟩
  have e : i1 = sc := by subst i_post i1_post; exact hcur
  subst e
  step with sporadic.max_release_time.ok hA as ⟨mrt, _⟩
  step with obj.Sc.period.spec as ⟨period, _⟩
  refine WP.spec_bind (sporadic.budget_check_loop0.fr mrt period usage layout.WALK_FUEL h) ?_
  rintro ⟨s1, us⟩ ⟨h1, w1⟩
  step with sporadic.head.spec as ⟨hd, _⟩
  refine WP.spec_bind (Pₘ := fun s2 => RefillsWF st s2 i1 sb ∧ WritesIn st s1 s2 (InRing i1 sb)) ?_ ?_
  · split
    · split
      · split
        · step as ⟨i2, _⟩
          step as ⟨i3, _⟩
          step as ⟨i4, _⟩
          refine WP.spec_bind (sporadic.set_head.fr _ h1) ?_
          rintro s3 ⟨h3, w3⟩
          exact WP.spec_mono (sporadic.schedule_used.fr _ h3) fun s4 ⟨h4, w4⟩ => ⟨h4, w3.trans1 w4⟩
        · simp only [WP.spec_ok]; exact ⟨h1, WritesIn.refl _ _⟩
      · simp only [WP.spec_ok]; exact ⟨h1, WritesIn.refl _ _⟩
    · simp only [WP.spec_ok]; exact ⟨h1, WritesIn.refl _ _⟩
  · rintro s2 ⟨h2, w2⟩
    step with sporadic.min_budget.ok hA as ⟨mb, _⟩
    step with obj.Sc.refill_max.spec as ⟨i2, _⟩
    step as ⟨fuel2, _⟩
    exact WP.spec_mono (sporadic.budget_check_loop1.fr mb fuel2 h2) fun s3 ⟨_, w3⟩ => (w1.trans1 w2).trans1 w3

@[step] theorem sched.cur_sc.spec (s : S) : sched.cur_sc st s ⦃ v => v = L.mem s (L.nodeA s layout.node.CUR_SC) ⦄ := by
  unfold sched.cur_sc; step*; simp_all [LawfulStore.nodeA]
@[step] theorem sched.idle_sc.spec (s : S) : sched.idle_sc st s ⦃ _ => True ⦄ := by
  unfold sched.idle_sc; step*
@[step] theorem sched.consumed.spec (s : S) : sched.consumed st s ⦃ _ => True ⦄ := by
  unfold sched.consumed; step*
@[step] theorem sporadic.sc_active.spec (s : S) (sc : obj.Sc) : sporadic.sc_active st s sc ⦃ _ => True ⦄ := by
  unfold sporadic.sc_active; step*
@[step] theorem obj.Sc.consumed.spec (s : S) (sc : obj.Sc) : obj.Sc.consumed st sc s ⦃ _ => True ⦄ := by
  unfold obj.Sc.consumed; step*
@[step] theorem obj.Sc.set_consumed.spec (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_consumed st sc s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add sc layout.sc.CONSUMED) v ⦄ := by
  unfold obj.Sc.set_consumed; step*; simp_all
@[step] theorem sched.set_consumed.spec (s : S) (v : U64) :
    sched.set_consumed st s v ⦃ s' => s' = L.wr s (L.nodeA s layout.node.CONSUMED) v ⦄ := by
  unfold sched.set_consumed; step*; simp_all [LawfulStore.nodeA]
@[step] theorem sc_ne.spec (a b : obj.Sc) :
    core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc a b ⦃ _ => True ⦄ := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  simp [obj.Sc.Insts.CoreCmpPartialEqSc.eq]

/-- `commit_time` writes inside the current SC and the current core's
`CONSUMED`. -/
theorem sched.commit_time.fr {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A)
    (h : RefillsWF st s sc sb) (hcur : L.mem s (L.nodeA s layout.node.CUR_SC) = sc)
    (hcons : Aligned (L.nodeA s layout.node.CONSUMED)) :
    sched.commit_time st ar s a ⦃ s' =>
      WritesIn st s s' (fun b => (InRing sc sb b ∨ b = core.num.U64.wrapping_add sc layout.sc.CONSUMED) ∨
        b = L.nodeA s layout.node.CONSUMED) ⦄ := by
  unfold sched.commit_time
  step with sched.cur_sc.spec as ⟨c0, c0_post⟩
  rw [hcur] at c0_post
  subst c0
  step with sporadic.sc_active.spec as ⟨b, _⟩
  refine WP.spec_bind (Pₘ := fun s1 => WritesIn st s s1
      (fun b => InRing sc sb b ∨ b = core.num.U64.wrapping_add sc layout.sc.CONSUMED)) ?_ ?_
  · split
    · step with sched.idle_sc.spec as ⟨s2, _⟩
      step with sc_ne.spec as ⟨b1, _⟩
      split
      · step with sched.consumed.spec as ⟨c, _⟩
        refine WP.spec_bind (Pₘ := fun s3 => RefillsWF st s3 sc sb ∧ WritesIn st s s3 (InRing sc sb)) ?_ ?_
        · split
          · step with sporadic.is_round_robin.spec as ⟨b2, _⟩
            split
            · step with obj.Sc.refill_head.spec as ⟨hi, hi_post⟩
              step with obj.Sc.refill_tail.spec as ⟨ti, ti_post⟩
              step with sporadic.get.spec as ⟨hh, _⟩
              step as ⟨i, _⟩
              step with sporadic.put.spec as ⟨s4, s4_post⟩
              subst hi_post ti_post s4_post
              have h4 := h.putS (r := { hh with amount := i }) h.head_lt
              have w4 := h.frame_putS (r := { hh with amount := i }) h.head_lt
              obtain ⟨h8, -, -⟩ := h.bounds
              obtain ⟨-, -, -, -, -, hin⟩ := h.inside
              obtain ⟨-, e2, e3⟩ := hin _ h.head_lt
              have hfit : sc.val + 96 + 16 * (L.rhead s sc).val + 16 ≤ 2 ^ 64 := by
                have := h.bounds.2.2; omega
              have htl : (L.rtail s sc).val < (L.rmax (L.putS s sc (L.rhead s sc) { hh with amount := i }) sc).val := by
                rw [rmax_putS h8 hfit]
                exact h.tail_lt
              step with sporadic.get.spec as ⟨tt, _⟩
              step as ⟨i1, _⟩
              step with sporadic.put.spec as ⟨s5, s5_post⟩
              subst s5_post
              exact ⟨h4.putS htl, w4.trans1 (h4.frame_putS htl)⟩
            · exact WP.spec_mono (WP.spec_and (sporadic.budget_check.wf hA a c h hcur)
                (sporadic.budget_check.fr hA a c h hcur)) fun s3 hh3 => hh3
          · simp only [WP.spec_ok]; exact ⟨h, WritesIn.refl _ _⟩
        · rintro s3 ⟨h3, w3⟩
          step with obj.Sc.consumed.spec as ⟨i, _⟩
          step as ⟨used, _⟩
          step with obj.Sc.set_consumed.spec as ⟨s4, s4_post⟩
          subst s4_post
          have hal : Aligned (core.num.U64.wrapping_add sc layout.sc.CONSUMED) := by
            obtain ⟨h8, -, hfit⟩ := h3.bounds
            have := h3.inside.1
            unfold Aligned
            simp [layout.sc.CONSUMED, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
          exact (w3.trans (writesIn_wr hal)).mono fun b hb => by
            rcases hb with hb | hb
            · exact Or.inl hb
            · exact Or.inr hb
      · simp only [WP.spec_ok]; exact WritesIn.refl _ _
    · simp only [WP.spec_ok]; exact WritesIn.refl _ _
  · intro s1 w1
    step with sched.set_consumed.spec as ⟨s2, s2_post⟩
    subst s2_post
    have e : L.nodeA s1 layout.node.CONSUMED = L.nodeA s layout.node.CONSUMED := by
      simp [LawfulStore.nodeA, LawfulStore.nodeAt, w1.1, w1.2.1]
    rw [e]
    exact (w1.trans (writesIn_wr hcons)).mono fun b hb => by
      rcases hb with hb | hb
      · exact Or.inl hb
      · exact Or.inr hb

/-! ## Footprints, as free words -/

section free
variable {T Ω Cs : Set U64}

theorem WritesIn.mono' {s s' : S} {A B : U64 → Prop} (h : WritesIn st s s' A)
    (hAB : ∀ b, Aligned b → A b → B b) : WritesIn st s s' B :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb (fun h' => hn (hAB b hb h'))⟩

theorem free_cur_node {s : S} {o : U64} (hcur : L.cpu s ∈ Cs) (ho : LowFree o.val) :
    L.Free s Ω Cs (L.nodeAt s (L.cpu s) o) := Or.inr ⟨_, hcur, o, ho, rfl⟩

theorem free_node_write {s s1 : S} {c o v : U64} (hk : L.ksb s1 = L.ksb s) (hc : c ∈ Cs)
    (hN : NodePlaced st T s c) (ho : LowFree o.val) :
    WritesIn st s1 (L.wr s1 (L.nodeAt s1 c o) v) (L.Free s Ω Cs) := by
  rw [nodeAt_of_ksb hk]
  exact (writesIn_wr (nodeAt_aligned hN (by simp only [LowFree] at ho; omega) (by simp only [LowFree] at ho; omega))).mono
    fun b hb => Or.inr ⟨c, hc, o, ho, hb⟩

theorem WritesIn.free_trans {s s1 s2 : S} (h1 : WritesIn st s s1 (L.Free s Ω Cs))
    (h2 : WritesIn st s1 s2 (L.Free s Ω Cs)) : WritesIn st s s2 (L.Free s Ω Cs) := h1.trans1 h2

@[step] theorem sched.cur_time.spec (s : S) : sched.cur_time st s ⦃ _ => True ⦄ := by
  unfold sched.cur_time; step*
@[step] theorem timer.earliest.spec (s : S) : timer.earliest st s ⦃ _ => True ⦄ := by
  unfold timer.earliest obj.Tcb.timer_deadline; step*

/-- `set_next_interrupt` only writes the current core's `ARMED`. -/
theorem sched.set_next_interrupt.fp {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    {B : U64 → Prop} (hN' : NodePlaced st T s (L.cpu s)) (hB : B (L.nodeAt s (L.cpu s) layout.node.ARMED)) :
    sched.set_next_interrupt st ar s a ⦃ s' _ => WritesIn st s s' B ⦄ := by
  unfold sched.set_next_interrupt
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  step*
  rw [ite_cond_eq_false _ _ (by simp)]
  simp only [bind_ok]
  step*
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> step*) fun next2 _ => ?_
  step with P0.ArchTotal.us_to_ticks_spec hA as ⟨prec, _⟩
  step as ⟨deadline, _⟩
  step with timer.earliest.spec as ⟨td, _⟩
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> (try split) <;> step*) fun deadline1 _ => ?_
  step with obj.node_get.spec as ⟨armed, _⟩
  have w : ∀ v, WritesIn st s (L.wr s (L.nodeAt s i1 layout.node.ARMED) v) B := fun v => by
    rw [i1_post]
    exact (writesIn_wr (nodeAt_aligned hN' (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED]))).mono
      fun b hb => hb ▸ hB
  split
  · split
    · simp only [WP.spec_ok, WP.uncurry'_pair]; exact WritesIn.refl _ _
    · step with obj.node_set.spec as ⟨s1, s1_post⟩
      step with P0.ArchTotal.set_deadline_spec hA as ⟨a1, _⟩
      rw [s1_post]; exact w _
  · step with obj.node_set.spec as ⟨s1, s1_post⟩
    step with P0.ArchTotal.set_deadline_spec hA as ⟨a1, _⟩
    rw [s1_post]; exact w _

theorem sched.set_next_interrupt.free {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (hcur : L.cpu s ∈ Cs) (hN' : NodePlaced st T s (L.cpu s)) :
    sched.set_next_interrupt st ar s a ⦃ s' _ => WritesIn st s s' (L.Free s Ω Cs) ⦄ :=
  sched.set_next_interrupt.fp hA s a hN' (free_cur_node hcur (by simp [layout.node.ARMED, LowFree]))

/-- `send_pending` only clears the current core's `IPI_PENDING`. -/
theorem smp.send_pending.fp {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    {B : U64 → Prop} (hN' : NodePlaced st T s (L.cpu s)) (hB : B (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING)) :
    smp.send_pending st ar s a ⦃ s' _ => WritesIn st s s' B ⦄ := by
  unfold smp.send_pending
  step with LawfulStore.cur_cpu_spec as ⟨c, c_post⟩
  step with obj.node_get.spec as ⟨m, _⟩
  split
  · step with obj.node_set.spec as ⟨s1, s1_post⟩
    step with P0.ArchTotal.send_reschedule_spec hA as ⟨a1, _⟩
    rw [s1_post, c_post]
    exact (writesIn_wr (nodeAt_aligned hN' (by simp [layout.node.IPI_PENDING])
      (by simp [layout.node.IPI_PENDING]))).mono fun b hb => hb ▸ hB
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact WritesIn.refl _ _

theorem smp.send_pending.free {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (hcur : L.cpu s ∈ Cs) (hN' : NodePlaced st T s (L.cpu s)) :
    smp.send_pending st ar s a ⦃ s' _ => WritesIn st s s' (L.Free s Ω Cs) ⦄ :=
  smp.send_pending.fp hA s a hN' (free_cur_node hcur (by simp [layout.node.IPI_PENDING, LowFree]))

/-! ## `switch_sched_context` -/

theorem sc_ne.spec' (a b : obj.Sc) :
    core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc a b ⦃ r => r = true → a ≠ b ⦄ := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  simp [obj.Sc.Insts.CoreCmpPartialEqSc.eq]

@[step] theorem sporadic.sc_constant_bandwidth.spec (s : S) (sc : obj.Sc) :
    sporadic.sc_constant_bandwidth st s sc ⦃ _ => True ⦄ := by
  unfold sporadic.sc_constant_bandwidth obj.Sc.sporadic; step*

@[step] theorem sched.set_reprogram.spec (s : S) :
    sched.set_reprogram st s ⦃ s' => s' = L.wr s (L.nodeA s layout.node.REPROGRAM) 1#u64 ⦄ := by
  unfold sched.set_reprogram; step*; simp_all [LawfulStore.nodeA]

/-- The ring invariant only reads the object's own words. -/
theorem RefillsWF.writesIn {s s' : S} {sc : obj.Sc} {sb : Nat} {A : U64 → Prop} (h : RefillsWF st s sc sb)
    (w : WritesIn st s s' A) (hA : ∀ b, Aligned b → A b → Outside b sc sb) : RefillsWF st s' sc sb := by
  obtain ⟨h8, hm, hfit⟩ := h.bounds
  have := h.min_le; simp at this
  have e : ∀ b, Aligned b → sc.val ≤ b.val → b.val < sc.val + 96 → L.mem s' b = L.mem s b :=
    fun b hb h1 h2 => w.2.2 b hb fun hAb => by
      have := hA b hb hAb; unfold Outside at this; omega
  have em : L.rmax s' sc = L.rmax s sc := e _ (by addr) (by addr) (by addr)
  refine h.of_hdr em ?_ ?_
  · rw [show L.rhead s' sc = L.rhead s sc from e _ (by addr) (by addr) (by addr)]
    exact h.head_lt
  · rw [show L.rtail s' sc = L.rtail s sc from e _ (by addr) (by addr) (by addr)]
    exact h.tail_lt

/-- The SC `sc` (of `2 ^ sb` bytes) is well formed and its words are among `Ω`. -/
def SCin (st : machine.Store S) [L : LawfulStore st] (s : S) (Ω : Set U64) (sc : obj.Sc) (sb : Nat) : Prop :=
  RefillsWF st s sc sb ∧ ∀ b, Aligned b → InSC sc sb b → b ∈ Ω

/-- A node word is outside an SC whose words are among `Ω`. -/
theorem SCin.node_out {T Ω Cs : Set U64} {sc : obj.Sc} {sb : Nat} {c o : U64} (hS : SCin st s Ω sc sb)
    (homega : ∀ a ∈ Ω, OutsideObjs st T Cs s a) (hc : c ∈ Cs) (hN : NodePlaced st T s c)
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) : Outside (L.nodeAt s c o) sc sb := by
  by_contra hn
  unfold Outside at hn
  have ha := nodeAt_aligned hN ho h8
  have := (homega _ (hS.2 _ ha ⟨by omega, by omega⟩)).2.2 c hc
  rw [nodeAt_val hN ho] at this hn
  omega

/-- `switch_sched_context` writes the ring of the thread's SC (when it is not
the current one), the ring and `CONSUMED` word of the current SC, and the
current core's `REPROGRAM`, `CONSUMED` and `CUR_SC`, which becomes the
thread's SC.  The SCs must be well formed, among `Ω` and (when distinct)
disjoint. -/
theorem sched.switch_sched_context.fp {A : Type _} {ar : machine.Arch A} {T Ω Cs : Set U64}
    (hA : P0.ArchTotal ar) (s : S) (a : A) {zt zc : Nat} {B : U64 → Prop}
    (hcur : L.cpu s ∈ Cs) (hN' : NodePlaced st T s (L.cpu s))
    (homega : ∀ a ∈ Ω, OutsideObjs st T Cs s a)
    (hc : SCin st s Ω (L.mem s (L.nodeA s layout.node.CUR_SC)) zc)
    (ht : L.mem s (scA (L.mem s (L.nodeA s layout.node.CUR_THREAD))) ≠ L.mem s (L.nodeA s layout.node.CUR_SC) →
      SCin st s Ω (L.mem s (scA (L.mem s (L.nodeA s layout.node.CUR_THREAD)))) zt ∧
      ∀ b, InSC (L.mem s (scA (L.mem s (L.nodeA s layout.node.CUR_THREAD)))) zt b →
        Outside b (L.mem s (L.nodeA s layout.node.CUR_SC)) zc)
    (hBR : B (L.nodeA s layout.node.REPROGRAM)) (hBC : B (L.nodeA s layout.node.CONSUMED))
    (hBS : B (L.nodeA s layout.node.CUR_SC))
    (hBt : L.mem s (scA (L.mem s (L.nodeA s layout.node.CUR_THREAD))) ≠ L.mem s (L.nodeA s layout.node.CUR_SC) →
      ∀ b, Aligned b → InRing (L.mem s (scA (L.mem s (L.nodeA s layout.node.CUR_THREAD)))) zt b → B b)
    (hBc : ∀ b, Aligned b → (InRing (L.mem s (L.nodeA s layout.node.CUR_SC)) zc b ∨
      b = core.num.U64.wrapping_add (L.mem s (L.nodeA s layout.node.CUR_SC)) layout.sc.CONSUMED) → B b) :
    sched.switch_sched_context st ar s a ⦃ s' _ => WritesIn st s s' B ∧
      L.mem s' (L.nodeA s layout.node.CUR_SC) = L.mem s (scA (L.mem s (L.nodeA s layout.node.CUR_THREAD))) ⦄ := by
  have nO : ∀ {sc sb} (o : U64), SCin st s Ω sc sb → o.val < 4288 → o.val % 8 = 0 →
      Outside (L.nodeA s o) sc sb := fun o hS ho h8 => hS.node_out homega hcur hN' ho h8
  have alN : ∀ (o : U64), o.val < 4288 → o.val % 8 = 0 → Aligned (L.nodeA s o) :=
    fun o ho h8 => nodeAt_aligned hN' ho h8
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have cs : layout.node.CUR_SC.val = 24 := by simp [layout.node.CUR_SC]
  have cn : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
  unfold sched.switch_sched_context
  step with sched.cur_thread.spec as ⟨ct, ct_post⟩
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  step with sched.cur_sc.spec as ⟨s1, s1_post⟩
  step with sc_ne.spec' as ⟨b, b_post⟩
  have hct : ct = L.mem s (L.nodeA s layout.node.CUR_THREAD) := ct_post
  subst hct
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s s2 B ∧
      RefillsWF st s2 s1 zc ∧ L.mem s2 (L.nodeA s layout.node.CUR_SC) = s1) ?_ ?_
  · split
    · rename_i hb
      have hne : i ≠ s1 := fun e => b_post hb e.symm
      rw [i_post, s1_post] at hne
      obtain ⟨hSt, hdis⟩ := ht hne
      have hBt' := hBt hne
      simp only [← i_post, ← s1_post] at hSt hdis hBt'
      rw [← s1_post] at hc
      step with sched.set_reprogram.spec as ⟨s3, s3_post⟩
      have aR := alN layout.node.REPROGRAM (by rw [rp]; omega) (by rw [rp])
      have oRt := nO layout.node.REPROGRAM hSt (by rw [rp]; omega) (by rw [rp])
      have oRc := nO layout.node.REPROGRAM hc (by rw [rp]; omega) (by rw [rp])
      have aC := alN layout.node.CUR_SC (by rw [cs]; omega) (by rw [cs])
      have oCt := nO layout.node.CUR_SC hSt (by rw [cs]; omega) (by rw [cs])
      have hRC : (L.nodeA s layout.node.REPROGRAM).val ≠ (L.nodeA s layout.node.CUR_SC).val := by
        simp only [LawfulStore.nodeA]; rw [nodeAt_val hN' (by rw [rp]; omega), nodeAt_val hN' (by rw [cs]; omega), rp, cs]
        omega
      have w3 : WritesIn st s s3 (· = L.nodeA s layout.node.REPROGRAM) := by subst s3_post; exact writesIn_wr aR
      have e3 : L.nodeA s3 layout.node.REPROGRAM = L.nodeA s layout.node.REPROGRAM := by
        simp [LawfulStore.nodeA, LawfulStore.nodeAt, w3.1, w3.2.1]
      have pre : WritesIn st s s3 B ∧ RefillsWF st s3 s1 zc ∧
          L.mem s3 (L.nodeA s layout.node.CUR_SC) = s1 := by
        refine ⟨w3.mono' fun b _ hb => hb ▸ hBR, ?_, ?_⟩
        · subst s3_post; exact hc.1.wr_out aR oRc
        · subst s3_post; rw [L.mem_wr_ne aR aC hRC, s1_post]
      step with sporadic.sc_constant_bandwidth.spec as ⟨b1, _⟩
      split
      · have hSt3 : RefillsWF st s3 i zt := by subst s3_post; exact hSt.1.wr_out aR oRt
        refine WP.spec_mono (sporadic.unblock_check.fr hSt3 ⟨by rw [e3]; exact aR, by rw [e3]; exact oRt⟩) fun s4 w4 => ?_
        rw [e3] at w4
        refine ⟨pre.1.trans1 (w4.mono' fun b hb h => ?_), ?_, ?_⟩
        · rcases h with h | h
          · exact hBt' b hb h
          · exact h ▸ hBR
        · refine pre.2.1.writesIn w4 fun b hb h => ?_
          rcases h with h | h
          · exact hdis b h.inSC
          · exact h ▸ oRc
        · rw [w4.mem_eq aC ?_, pre.2.2]
          rintro (h | h)
          · unfold Outside at oCt; unfold InRing at h; omega
          · exact hRC (congrArg UScalar.val h).symm
      · simp only [WP.spec_ok]; exact pre
    · simp only [WP.spec_ok]; rw [← s1_post] at hc
      exact ⟨WritesIn.refl _ _, hc.1, s1_post.symm⟩
  · rintro s2 ⟨w2, h2, e2⟩
    step with LawfulStore.cur_cpu_spec as ⟨i1, i1_post⟩
    step with obj.node_get.spec as ⟨i2, _⟩
    have eN : ∀ o, L.nodeA s2 o = L.nodeA s o := fun o => by
      simp [LawfulStore.nodeA, LawfulStore.nodeAt, w2.1, w2.2.1]
    refine WP.spec_bind (Pₘ := fun s3 => WritesIn st s s3 B ∧ L.ksb s3 = L.ksb s ∧ L.cpu s3 = L.cpu s) ?_ ?_
    · split
      · rw [← s1_post] at hc hBc
        have hcur2 : L.mem s2 (L.nodeA s2 layout.node.CUR_SC) = s1 := by rw [eN]; exact e2
        have aCn := alN layout.node.CONSUMED (by rw [cn]; omega) (by rw [cn])
        refine WP.spec_mono (sched.commit_time.fr hA a h2 hcur2 (by rw [eN]; exact aCn)) fun s3 w3 => ?_
        rw [eN] at w3
        refine ⟨w2.trans1 (w3.mono' fun b hb h => ?_), w3.1.trans w2.1, w3.2.1.trans w2.2.1⟩
        rcases h with h | h
        · exact hBc b hb h
        · exact h ▸ hBC
      · simp only [WP.spec_ok]; exact ⟨w2, w2.1, w2.2.1⟩
    · rintro s3 ⟨w3, k3, c3⟩
      step with LawfulStore.cur_cpu_spec as ⟨c, c_post⟩
      step with obj.node_set.spec as ⟨s4, s4_post⟩
      try simp only [WP.spec_ok, WP.uncurry'_pair]
      have aC := alN layout.node.CUR_SC (by rw [cs]; omega) (by rw [cs])
      have eC : L.nodeAt s3 c layout.node.CUR_SC = L.nodeA s layout.node.CUR_SC := by
        rw [c_post, c3, nodeAt_of_ksb k3]; rfl
      rw [s4_post, eC]
      refine ⟨w3.trans1 ((writesIn_wr aC).mono fun b hb => hb ▸ hBS), ?_⟩
      rw [L.mem_wr_same aC, i_post]

/-- `switch_sched_context` writes free words only. -/
theorem sched.switch_sched_context.free {A : Type _} {ar : machine.Arch A} {T Ω Cs : Set U64}
    (hA : P0.ArchTotal ar) (s : S) (a : A) {zt zc : Nat}
    (hcur : L.cpu s ∈ Cs) (hN' : NodePlaced st T s (L.cpu s))
    (homega : ∀ a ∈ Ω, OutsideObjs st T Cs s a)
    (hc : SCin st s Ω (L.mem s (L.nodeA s layout.node.CUR_SC)) zc)
    (ht : L.mem s (scA (L.mem s (L.nodeA s layout.node.CUR_THREAD))) ≠ L.mem s (L.nodeA s layout.node.CUR_SC) →
      SCin st s Ω (L.mem s (scA (L.mem s (L.nodeA s layout.node.CUR_THREAD)))) zt ∧
      ∀ b, InSC (L.mem s (scA (L.mem s (L.nodeA s layout.node.CUR_THREAD)))) zt b →
        Outside b (L.mem s (L.nodeA s layout.node.CUR_SC)) zc) :
    sched.switch_sched_context st ar s a ⦃ s' _ => WritesIn st s s' (L.Free s Ω Cs) ⦄ := by
  have fr : ∀ (o : U64), LowFree o.val → L.Free s Ω Cs (L.nodeA s o) := fun o ho => free_cur_node hcur ho
  have cin : ∀ {sc : U64} {sb : Nat}, SCin st s Ω sc sb → ∀ b, Aligned b →
      (InRing sc sb b ∨ b = core.num.U64.wrapping_add sc layout.sc.CONSUMED) → L.Free s Ω Cs b := by
    intro sc sb hS b hb h
    refine Or.inl (hS.2 b hb ?_)
    rcases h with h | rfl
    · exact h.inSC
    · obtain ⟨h8, -, hfit⟩ := hS.1.bounds
      have := hS.1.inside.1
      constructor <;> simp [layout.sc.CONSUMED, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] <;>
        omega
  exact WP.spec_mono (sched.switch_sched_context.fp hA s a (zt := zt) (zc := zc) hcur hN' homega hc ht
    (fr _ (by simp [layout.node.REPROGRAM, LowFree])) (fr _ (by simp [layout.node.CONSUMED, LowFree]))
    (fr _ (by simp [layout.node.CUR_SC, LowFree]))
    (fun hne b hb h => cin (ht hne).1 b hb (Or.inl h)) (fun b hb h => cin hc b hb h)) fun r hr => hr.1

end free

end

end Fl4Proofs.P1
