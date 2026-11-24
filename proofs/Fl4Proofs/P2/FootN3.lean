/-
P2 (p2j, KWN step 3): **the budget path in `KWN`** (P1 `QueueBudgetG`'s
`G`-versions with the frame step `KW` replaced by `KWN`): `end_suff.footN`
(`append` or `postpone`), and `end_timeslice.allGN`, `charge_budget.allGN`,
`check_budget.allGN`, `mcs_preemption_point.allGN`: the budget checks keep
`BXI` and any property `G` of the states that `KWN` steps keep (`hGF`), when
the timeout faults keep it (P1's `TmoKG`, unchanged). With `G` = "an `IpcW`
footprint from the start without node identity words" (`P2/FootN5.lean`)
this is the budget path's frame: no core's idle words, no other core's
current thread, action or current SC are written. No premise.
-/
import Fl4Proofs.P2.FootN2
import Fl4Proofs.P1.QueueBudgetG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {A : Type _} {ar : machine.Arch A} {Ac : Set U64} {Kp : Set U64} {Nd : Prop}

/-- `end_suff`'s footprint in `KWN`: `append` or `postpone`. -/
theorem end_suff.footN (hA : P0.ArchTotal ar) (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hc : CurOK st T s) :
    (do
      let b ← sporadic.ready st s (L.cscW s)
      if b = true then do
        let b1 ← sporadic.sufficient st ar s a (L.cscW s) 0#u64
        if b1 = true then do let s1 ← sched.append st s (L.curW s); ok (s1, a)
        else do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a)
      else do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a))
      ⦃ s' _ => FootN st Kp Nd T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have hcT : L.curW s ∈ T := h.curT
  obtain ⟨hSc, htc, hcore⟩ := hX.2.2.bound (L.curW s) hcT hc.bnd
  rw [← hc.csc] at hSc htc hcore
  have hco : OutsideObjs st T Cs s (scCoreA (L.cscW s)) := h.omega _ ((objs_omega hX.1 hSg.sub).2 _ hSc).2.1
  have P : (do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a))
      ⦃ s' _ => FootN st Kp Nd T Cs Sg Scs Z (EH H) s s' ⦄ :=
    WP.spec_bind (sched.postpone.kwN s _ Q R h (by rw [htc]; exact hcT) (by rw [htc]; exact hc.rel) hco hcore)
      fun s1 f1 => by simp only [WP.spec_ok, WP.uncurry'_pair]; exact f1
  have Ap : (do let s1 ← sched.append st s (L.curW s); ok (s1, a))
      ⦃ s' _ => FootN st Kp Nd T Cs Sg Scs Z (EH H) s s' ⦄ :=
    WP.spec_bind (sched.append.kwN s _ h hcT) fun s1 f1 => by simp only [WP.spec_ok, WP.uncurry'_pair]; exact f1
  step with sporadic.ready.spec as ⟨b⟩
  split
  · step with sporadic.sufficient.ok (st := st) hA as ⟨b1⟩
    split
    · exact Ap
    · exact P
  · exact P

/-- `end_suff` keeps `G`, a property `KWN` steps keep. -/
theorem end_suffGN (hA : P0.ArchTotal ar) (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hc : CurOK st T s)
    {G : S → Prop} (hGF : ∀ s1 s2 : S, G s1 → FootN st Kp Nd T Cs Sg Scs Z (EH H) s1 s2 → G s2) (hG : G s) :
    (do
      let b ← sporadic.ready st s (L.cscW s)
      if b = true then do
        let b1 ← sporadic.sufficient st ar s a (L.cscW s) 0#u64
        if b1 = true then do let s1 ← sched.append st s (L.curW s); ok (s1, a)
        else do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a)
      else do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a))
      ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ G s' ⦄ :=
  WP.spec_mono (WP.spec_and (end_suff hA s a Q R h hB hX hSg hS hc) (end_suff.footN hA s a Q R h hX hSg hc))
    fun r hr => by
      obtain ⟨s', a'⟩ := r
      simp only [WP.uncurry'_pair] at hr ⊢
      exact ⟨hr.1, hGF _ _ hG hr.2⟩

/-- seL4 `endTimeslice` (`KWN` frame). -/
theorem sched.end_timeslice.allGN (hA : P0.ArchTotal ar) (s : S) (a : A) (cto : Bool)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hc : CurOK st T s)
    {G : S → Prop} (hGF : ∀ s1 s2 : S, G s1 → FootN st Kp Nd T Cs Sg Scs Z (EH H) s1 s2 → G s2) (hG : G s)
    (htmo : TmoKG st ar T Cs Ω H Sg Rp Scs Nt Z Ac G) :
    sched.end_timeslice st ar s a cto ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ G s' ⦄ := by
  have E := end_suffGN hA s a Q R h hB hX hSg hS hc hGF hG
  unfold sched.end_timeslice
  step with sched.cur_sc.spec as ⟨sc, sc_post⟩
  step with sched.cur_thread.spec as ⟨ct, ct_post⟩
  have e1 : sc = L.cscW s := sc_post
  have e2 : ct = L.curW s := ct_post
  subst e1 e2
  step with sporadic.is_round_robin.spec as ⟨rr⟩
  step with obj.Tcb.state.spec
  refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun valid _ => ?_
  · split
    · exact P0.faults.valid_timeout_handler.p0 st s _ L.total
    · simp
  split
  · split
    · exact E
    · split
      · step with P0.obj.Sc.badge.p0 st _ s L.total as ⟨badge⟩
        exact htmo s a _ Q R h hB hX hSg hS hG
      · exact E
  · exact E

set_option maxHeartbeats 1000000 in
/-- seL4 `chargeBudget` (`KWN` frame; P1 `charge_budget.allG`). -/
theorem sched.charge_budget.allGN (hA : P0.ArchTotal ar) (s : S) (a : A) (used : U64) (cto : Bool)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hna : L.actionW s ≠ L.curW s) (hcA : L.cscW s ∈ Ac)
    {G : S → Prop} (hGF : ∀ s1 s2 : S, G s1 → FootN st Kp Nd T Cs Sg Scs Z (EH H) s1 s2 → G s2) (hG : G s)
    (htmo : TmoKG st ar T Cs Ω H Sg Rp Scs Nt Z Ac G) :
    sched.charge_budget st ar s a used cto ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ G s' ⦄ := by
  have hcS : L.cscW s ∈ Scs := hX.2.2.cur
  have hcT0 : L.curW s ∈ T := h.curT
  have hW : RefillsWF st s (L.cscW s) (Z (L.cscW s)) := hS.wf hcS hcA
  unfold sched.charge_budget
  step with sched.cur_sc.spec as ⟨sc, sc_post⟩
  have e1 : sc = L.cscW s := sc_post
  subst e1
  step with sched.idle_sc.spec as ⟨s1⟩
  step with sc_ne.spec as ⟨b⟩
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s s2 (fun b => InRing (L.cscW s) (Z (L.cscW s)) b ∨
      b = core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) ∧ RefillsWF st s2 (L.cscW s) (Z (L.cscW s))) ?_ ?_
  · split
    · step with sporadic.is_round_robin.spec as ⟨b1⟩
      refine WP.spec_bind (Pₘ := fun s3 => RefillsWF st s3 (L.cscW s) (Z (L.cscW s)) ∧
          WritesIn st s s3 (InRing (L.cscW s) (Z (L.cscW s)))) ?_ ?_
      · split
        · step with obj.Sc.refill_head.spec as ⟨hi, hi_post⟩
          step with obj.Sc.refill_tail.spec as ⟨ti, ti_post⟩
          step with sporadic.get.spec as ⟨hh, hh_post⟩
          step with sporadic.get.spec as ⟨tt, tt_post⟩
          step as ⟨i, _⟩
          step with sporadic.put.spec as ⟨s4, s4_post⟩
          subst hi_post ti_post s4_post
          have h4 := hW.putS (r := { hh with amount := i }) hW.head_lt
          have w4 := hW.frame_putS (r := { hh with amount := i }) hW.head_lt
          obtain ⟨h8, -, -⟩ := hW.bounds
          have hfit : (L.cscW s).val + 96 + 16 * (L.rhead s (L.cscW s)).val + 16 ≤ 2 ^ 64 := by
            have := hW.bounds.2.2; have := hW.inside; have := hW.head_lt; have := hW.le_abs
            have := absMax_lt (Z (L.cscW s)); obtain ⟨-, hm, -⟩ := hW.bounds; omega
          have htl : (L.rtail s (L.cscW s)).val < (L.rmax (L.putS s (L.cscW s) (L.rhead s (L.cscW s))
              { hh with amount := i }) (L.cscW s)).val := by
            rw [rmax_putS h8 hfit]; exact hW.tail_lt
          step with sporadic.put.spec as ⟨s5, s5_post⟩
          subst s5_post
          exact ⟨h4.putS htl, w4.trans1 (h4.frame_putS htl)⟩
        · exact WP.spec_mono (WP.spec_and (sporadic.budget_check.wf hA a used hW rfl)
            (sporadic.budget_check.fr hA a used hW rfl)) fun s3 hh3 => hh3
      · rintro s3 ⟨h3, w3⟩
        step with obj.Sc.consumed.spec as ⟨ci⟩
        step as ⟨total, _⟩
        step with obj.Sc.set_consumed.spec as ⟨s4, s4_post⟩
        subst s4_post
        have hal : Aligned (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) := by
          obtain ⟨hP, hz⟩ := hX.1.sc _ hcS
          obtain ⟨h8, -, -⟩ := sc_lo hP hz
          unfold Aligned; rw [sc_word_val hP hz (by simp [layout.sc.CONSUMED])]; simp [layout.sc.CONSUMED]; omega
        exact ⟨(w3.trans (writesIn_wr hal)).mono fun b hb => by
          rcases hb with hb | hb
          · exact Or.inl hb
          · exact Or.inr hb, h3.wr_cons⟩
    · simp only [WP.spec_ok]; exact ⟨WritesIn.refl _ _, hW⟩
  rintro s2 ⟨w2, wf2⟩
  have hS2 := SCsOK.ringc h hS hX hcS w2 wf2
  obtain ⟨h2, hB2, hX2, hSg2, ea2, ec2, ecs2, f2⟩ := ring_bx h hB hX hSg hcS w2
  step with sched.set_consumed.spec as ⟨s3, s3_post⟩
  rw [show L.nodeA s2 layout.node.CONSUMED = L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED from rfl] at s3_post
  obtain ⟨h3, hB3, hX3, hSg3, ea3, ec3, ecs3, f3⟩ := node_bx (o := layout.node.CONSUMED) (v := 0#u64) h2 hB2 hX2 hSg2
    (by simp [layout.node.CONSUMED, LowFree]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have hS3 : SCsOK st T Ω Sg Scs Z Ac (L.wr s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) 0#u64) := by
    have hN2 := h2.nodes _ h2.cur
    obtain ⟨-, hc⟩ := objs_omega hX2.1 hS2.sub
    have hco : (layout.node.CONSUMED).val = 40 := by simp [layout.node.CONSUMED]
    refine SCsOK.wr h2 hS2 hX2 (nodeAt_aligned hN2 (by rw [hco]; omega) (by rw [hco])) (fun y hy => ?_) ?_
      (fun c hc' => ?_) (fun c hc' => out_ne_node (h2.omega _ (spor_omega hX2.1 hc')) h2.cur hN2 (by rw [hco]; omega))
      (fun c hc' e => absurd e (out_ne_node (h2.omega _ (hS2.sub _ (hX2.1.repW c hc'))) h2.cur hN2 (by rw [hco]; omega)))
    · rw [scA_eq]; exact fun e => node_ne_field hN2 (by rw [hco]; omega) hy (h2.tcbs y hy) (by simp)
        (UScalar.eq_of_val_eq e)
    · intro e
      simp only [LawfulStore.nodeA] at e
      rw [nodeAt_val hN2 (by rw [hco]; omega), nodeAt_val hN2 (by simp [layout.node.CUR_SC]), hco] at e
      simp [layout.node.CUR_SC] at e
    · obtain ⟨-, -, c3, c4, c5⟩ := hc c hc'
      exact ⟨out_ne_node (h2.omega _ c3) h2.cur hN2 (by rw [hco]; omega),
        out_ne_node (h2.omega _ c4) h2.cur hN2 (by rw [hco]; omega),
        out_ne_node (h2.omega _ c5) h2.cur hN2 (by rw [hco]; omega)⟩
  rw [← s3_post] at h3 hB3 hX3 hSg3 ea3 ec3 ecs3 f3 hS3
  have G3 : G s3 := by
    obtain ⟨hP, hz⟩ := hX.1.sc _ hcS
    obtain ⟨-, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hN2 := h2.nodes _ h2.cur
    have wn : WritesIn st s2 s3 (fun b => b = L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) := by
      rw [s3_post]; exact writesIn_wr (nodeAt_aligned hN2 (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
    refine hGF _ _ hG (FootN.of' (w2.trans wn) fun b hb hh => ?_)
    rcases hh with (hh | rfl) | rfl
    · exact ⟨kw_sc hcS hh.inSC, notIdW_out h.nodes (h.omega _ (hX.1.scW _ hcS b hb hh.inSC)) (noHdr_ring hX.1 hcS hh)⟩
    · have hin : InSC (L.cscW s) (Z (L.cscW s)) (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) :=
        ⟨by rw [hv]; simp, by rw [hv]; simp [layout.sc.CONSUMED]; omega⟩
      exact ⟨kw_sc hcS hin, notIdW_out h.nodes (h.omega _ (hX.1.scW _ hcS _ hb hin))
        (noHdr_sc hX.1 hcS hin (by rw [hv]; simp [layout.sc.CONSUMED]) (by rw [hv]; simp [layout.sc.CONSUMED]))⟩
    · rw [nodeAt_of_ksb w2.1, w2.2.1]
      exact ⟨kw_node h.cur (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]),
        notIdW_node h.nodes h.cur (by simp [layout.node.CONSUMED]) (idOff_ge (by simp [layout.node.CONSUMED]))⟩
  step with sched.cur_thread.spec as ⟨ct, ct_post⟩
  have e2 : ct = L.curW s3 := ct_post
  subst e2
  step with sched.is_schedulable.spec' as ⟨b1, b1_post⟩
  split
  · rename_i hb1
    obtain ⟨hrun, hbd, hrl, hrm⟩ := b1_post hb1
    have hcT : L.curW s ∈ T := h.curT
    have esc : L.mem s3 (scA (L.curW s3)) = L.mem s (scA (L.curW s)) := by
      rw [ec3, ec2, (f3 _ hcT).1, (f2 _ hcT).1]
    have hc : CurOK st T s3 := ⟨hrun, hbd, hrl, by
      rw [ecs3, ecs2, esc]; exact hcsc (by rw [← esc]; exact hbd), by rw [ea3, ea2, ec3, ec2]; exact hna, hrm⟩
    refine WP.spec_bind (sched.end_timeslice.allGN hA s3 a cto Q R h3 hB3 hX3 hSg3 hS3 hc hGF G3 htmo) ?_
    rintro ⟨s4, a1⟩ ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hSg4, hS4⟩, g4⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (WP.spec_and (sched.reschedule_required.sch s4 Q4 R4 h4 hB4 hSg4)
      (sched.reschedule_required.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s4 h4)) ?_
    rintro s5 ⟨⟨⟨⟨Q5, R5, h5⟩, hB5, f5⟩, ea5, ec5, -⟩, k5⟩
    refine WP.spec_bind (WP.spec_and (sched.set_reprogram.sch s5 Q5 R5 h5 hB5 (hSg4.fr f5))
      (sched.set_reprogram.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s5 h5.nodes h5.cur)) ?_
    rintro s6 ⟨⟨⟨h6, hB6, f6⟩, ea6, ec6⟩, k6⟩
    simp only [WP.spec_ok, WP.uncurry'_pair]
    exact ⟨⟨⟨Q5, R5, h6⟩, hB6, (hX4.fr f5).fr f6, (hSg4.fr f5).fr f6, (hS4.fr f5).fr f6⟩,
      hGF _ _ (hGF _ _ g4 k5) k6⟩
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    exact ⟨⟨⟨Q, R, h3⟩, hB3, hX3, hSg3, hS3⟩, G3⟩

/-- seL4 `checkBudget` (`KWN` frame). -/
theorem sched.check_budget.allGN (hA : P0.ArchTotal ar) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hna : L.actionW s ≠ L.curW s) (hcA : L.cscW s ∈ Ac)
    {G : S → Prop} (hGF : ∀ s1 s2 : S, G s1 → FootN st Kp Nd T Cs Sg Scs Z (EH H) s1 s2 → G s2) (hG : G s)
    (htmo : TmoKG st ar T Cs Ω H Sg Rp Scs Nt Z Ac G) :
    sched.check_budget st ar s a ⦃ r s' _ => (BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ G s') ∧ (r = true → s' = s) ⦄ := by
  unfold sched.check_budget
  step with sched.cur_sc.spec as ⟨sc⟩
  step with sched.consumed.spec as ⟨c⟩
  step with sporadic.sufficient.ok (st := st) hA as ⟨b⟩
  split
  · unfold sched.is_cur_domain_expired
    simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
    have hnd : ¬ ((1#u64) > (1#u64)) := by simp
    simp only [hnd, ↓reduceIte, bind_ok, WP.spec_ok, WP.uncurry'_pair]
    have hb : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨⟨Q, R, h⟩, hB, hX, hSg, hS⟩
    first
      | exact ⟨hb, hG, fun _ => trivial⟩
      | exact ⟨⟨hb, hG⟩, fun _ => trivial⟩
      | exact ⟨⟨hb, hG⟩, fun _ => rfl⟩
      | exact ⟨hb, hG, fun _ => rfl⟩
      | exact ⟨hb, hG⟩
  · refine WP.spec_bind (sched.charge_budget.allGN hA s a c true Q R h hB hX hSg hS hcsc hna hcA hGF hG htmo) ?_
    rintro ⟨s1, a1⟩ h1
    try simp only [WP.uncurry'_pair] at h1
    obtain ⟨hb1, g1⟩ := h1
    refine (WP.spec_ok _).2 ?_
    try simp only [WP.uncurry'_pair]
    first
      | exact ⟨⟨hb1, g1⟩, fun e => absurd e (by simp)⟩
      | exact ⟨hb1, g1, fun e => absurd e (by simp)⟩
      | exact ⟨hb1, g1⟩

end

end Fl4Proofs.P1
