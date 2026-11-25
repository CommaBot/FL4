/-
P2 (p2je): **the timer-interrupt local entry ends in `AllCores`**
(`localtimer.handle_timer_irq_local`, accepted: it ran `handle_interrupt_entry`
beside the serial gate, P1 `irq_local_same`).

The body before `schedule` is `update_timestamp`, `check_budget` and
`handle_interrupt` of a timer IRQ. The local path's checks (read before it
runs them) give: the IRQ is below 128 and its state is `IRQ_TIMER`; the budget
is sufficient, or the current SC is round-robin and the current thread
schedulable (`round_robin_ok`). So `check_budget` raises no timeout fault
(`end_timeslice` takes the round-robin branch: `append` or `postpone`), and
the whole body is a `KWN` footprint (over `KI`, no-donation mode) and a `KWB`
footprint without endpoint words.

* `sched.append.kwB`, `end_suff.footB`, `sched.set_reprogram.kwB'`,
  `sched.update_timestamp.kwB`: `KWB` versions of the budget path's pieces.
* `sched.end_timeslice.rr`, `sched.charge_budget.rr`, `sched.check_budget.rr`:
  P2's `allGN` budget lemmas on a round-robin current SC, with no timeout
  premise (`TmoKC`), giving `BXI`, `FootN`, `FootB` and the action (`1` or
  kept).
* `interrupt.handle_interrupt.timer`: the timer branch (the current node's
  `REPROGRAM` and `ARMED` words).
* `ks_keepB`: a `KWB` footprint without endpoint words keeps the kernel-global
  words, given `ScKsOut` (below); so the IRQ's state is still `IRQ_TIMER` when
  `handle_interrupt` reads it.
* `rr_ok_of`: what `round_robin_ok` checked.
* **`timer_irq_local.allCores`**: from `AllCores s0`, P1's `EntryInv` and
  `BufAt` at the entry, an accepted run ends `schedule` in `AllCores`
  (followed by `finish`'s `activate_thread` and `vcpu::check`). The body end
  facts of `AllCores.schedB` come from the body's footprint
  (`AllCores.bodyEnd`); `BlkOK`/`BufAt` at the body's end from P1's lemmas and
  the `KWB` footprint; `ActAff` since the action is `1` or still no thread.

Named premises of `timer_irq_local.allCores`: `hR` [J] (as `AllCores.schedE`,
stated at the body's end, `EntryEnd`), `hS0` [W] (`0 ∉ Scs`), and **`hKS`
[W] (`ScKsOut`: no SC overlaps the kernel-global area)**. P1 places the TCBs
(`SchedQueuesInv.ksOut`), endpoints and frame words (`SgOK.ks`) outside the
kernel-global area but has no such fact for SC objects; the budget path
writes the current SC's refill ring, so without it the IRQ-state word read by
`handle_interrupt` might change. Like `hS0` it is a layout fact (kernel
objects live in untyped memory, the kernel-global area is the kernel image's);
it is to be discharged where `Scs` is instantiated, or by adding it to P1's
`ObjsOK`.
-/
import Fl4Proofs.P2.EntryEnd
import Fl4Proofs.P1.LocalTimer
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es U : Set U64}
variable {A : Type _} {ar : machine.Arch A} {Kp : Set U64} {Nd : Prop}

/-! ## `KWB` pieces -/

theorem sched.append.kwB {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S) (t : obj.Tcb)
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

theorem sched.set_reprogram.kwB' (s : S) (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) :
    sched.set_reprogram st s ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.set_reprogram.spec s) fun s' e => by
    subst e
    have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
    exact footB_node hN hc (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega)

/-- `end_suff`'s footprint in `KWB`. -/
theorem end_suff.footB (hA : P0.ArchTotal ar) (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hc : CurOK st T s) :
    (do
      let b ← sporadic.ready st s (L.cscW s)
      if b = true then do
        let b1 ← sporadic.sufficient st ar s a (L.cscW s) 0#u64
        if b1 = true then do let s1 ← sched.append st s (L.curW s); ok (s1, a)
        else do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a)
      else do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a))
      ⦃ s' _ => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  have hcT : L.curW s ∈ T := h.curT
  obtain ⟨hSc, htc, hcore⟩ := hX.2.2.bound (L.curW s) hcT hc.bnd
  rw [← hc.csc] at hSc htc hcore
  have hco : OutsideObjs st T Cs s (scCoreA (L.cscW s)) := h.omega _ ((objs_omega hX.1 hSg.sub).2 _ hSc).2.1
  have P : (do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a))
      ⦃ s' _ => FootB st T Cs Sg Scs Z Es s s' ⦄ :=
    WP.spec_bind (sched.postpone.kwB s _ Q R h (by rw [htc]; exact hcT) (by rw [htc]; exact hc.rel) hco hcore)
      fun s1 f1 => by simp only [WP.spec_ok, WP.uncurry'_pair]; exact f1
  have Ap : (do let s1 ← sched.append st s (L.curW s); ok (s1, a))
      ⦃ s' _ => FootB st T Cs Sg Scs Z Es s s' ⦄ :=
    WP.spec_bind (sched.append.kwB s _ h hcT) fun s1 f1 => by simp only [WP.spec_ok, WP.uncurry'_pair]; exact f1
  step with sporadic.ready.spec as ⟨b⟩
  split
  · step with sporadic.sufficient.ok (st := st) hA as ⟨b1⟩
    split
    · exact Ap
    · exact P
  · exact P

/-- `update_timestamp` in `KWB`. -/
theorem sched.update_timestamp.kwB (hA : P0.ArchTotal ar) (s : S) (a : A)
    (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) :
    sched.update_timestamp st ar s a ⦃ s' _ => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.update_timestamp
  step with sched.cur_time.spec as ⟨prev⟩
  refine WP.spec_bind (hA.now a) ?_
  rintro ⟨now, a1⟩ -
  try simp only [WP.uncurry'_pair]
  step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
  step with obj.node_set.spec as ⟨s1, e1⟩
  subst ec e1
  have f1 : FootB st T Cs Sg Scs Z Es s (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now) :=
    footB_node hN hc (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME])
  step as ⟨used, _⟩
  step with sched.consumed.spec as ⟨i⟩
  step as ⟨total, _⟩
  step with sched.set_consumed.spec as ⟨s2, e2⟩
  rw [show ∀ s0 : S, L.nodeA s0 layout.node.CONSUMED = L.nodeAt s0 (L.cpu s0) layout.node.CONSUMED from
    fun _ => rfl] at e2
  subst e2
  have f2 : FootB st T Cs Sg Scs Z Es (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now)
      (L.wr (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now)
        (L.nodeAt (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now)
          (L.cpu (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now)) layout.node.CONSUMED) total) :=
    footB_node (by rw [LawfulStore.cpu_wr]; exact hN.ksb (L.ksb_wr _ _ _)) (by rw [LawfulStore.cpu_wr]; exact hc)
      (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have hnd : ¬ ((1#u64) > (1#u64)) := by simp
  simp only [hnd, ↓reduceIte, WP.spec_ok, WP.uncurry'_pair]
  exact f1.trans f2

/-! ## The budget check on a round-robin SC -/

/-- `end_suff`: `BXI`, `KWN` and `KWB`. -/
theorem end_suff.nb (hA : P0.ArchTotal ar) (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hc : CurOK st T s) (hKc : L.curW s ∉ Kp) :
    (do
      let b ← sporadic.ready st s (L.cscW s)
      if b = true then do
        let b1 ← sporadic.sufficient st ar s a (L.cscW s) 0#u64
        if b1 = true then do let s1 ← sched.append st s (L.curW s); ok (s1, a)
        else do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a)
      else do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a))
      ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ FootN st Kp Nd T Cs Sg Scs Z (EH H) s s' ∧
        FootB st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (WP.spec_and (WP.spec_and (end_suff hA s a Q R h hB hX hSg hS hc)
      (end_suff.footN (Kp := Kp) (Nd := Nd) hA s a Q R h hX hSg hc hKc))
      (end_suff.footB (Es := Es) hA s a Q R h hX hSg hc)) fun r hr => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact ⟨hr.1.1, hr.1.2, hr.2⟩

/-- seL4 `endTimeslice` on a round-robin current SC: no timeout fault. -/
theorem sched.end_timeslice.rr (hA : P0.ArchTotal ar) (s : S) (a : A) (cto : Bool)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hc : CurOK st T s) (hKc : L.curW s ∉ Kp)
    (hrr : L.rperiod s (L.cscW s) = 0#u64) :
    sched.end_timeslice st ar s a cto ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootN st Kp Nd T Cs Sg Scs Z (EH H) s s' ∧ FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  have E := end_suff.nb (Kp := Kp) (Nd := Nd) (Es := Es) hA s a Q R h hB hX hSg hS hc hKc
  unfold sched.end_timeslice
  step with sched.cur_sc.spec as ⟨sc, sc_post⟩
  step with sched.cur_thread.spec as ⟨ct, ct_post⟩
  have e1 : sc = L.cscW s := sc_post
  have e2 : ct = L.curW s := ct_post
  subst e1 e2
  step with sporadic.is_round_robin.spec as ⟨rr, hrr'⟩
  step with obj.Tcb.state.spec
  refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun valid _ => ?_
  · split
    · exact P0.faults.valid_timeout_handler.p0 st s _ L.total
    · simp
  split
  · split
    · exact E
    · rename_i hrf
      exfalso
      apply hrf
      rw [hrr', hrr]
      simp
  · exact E

set_option maxHeartbeats 1000000 in
/-- seL4 `chargeBudget` on a round-robin current SC (`KWN`, `KWB`; no timeout
fault). The action is then `1` (`reschedule_required`) or kept. -/
theorem sched.charge_budget.rr (hA : P0.ArchTotal ar) (s : S) (a : A) (used : U64) (cto : Bool)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hna : L.actionW s ≠ L.curW s) (hcA : L.cscW s ∈ Ac)
    (hKc : L.curW s ∉ Kp) (hKa : ActOut st T Kp s) (hrr : L.rperiod s (L.cscW s) = 0#u64) :
    sched.charge_budget st ar s a used cto ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootN st Kp Nd T Cs Sg Scs Z (EH H) s s' ∧ FootB st T Cs Sg Scs Z Es s s' ∧
      (L.actionW s' = 1#u64 ∨ L.actionW s' = L.actionW s) ⦄ := by
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
  obtain ⟨hP, hz⟩ := hX.1.sc _ hcS
  obtain ⟨h8c, h128, -⟩ := sc_lo hP hz
  have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hN2 := h2.nodes _ h2.cur
  have hN' := h.nodes _ h.cur
  have wn : WritesIn st s2 s3 (fun b => b = L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) := by
    rw [s3_post]; exact writesIn_wr (nodeAt_aligned hN2 (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
  have hcin : InSC (L.cscW s) (Z (L.cscW s)) (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) :=
    ⟨by rw [hv]; simp, by rw [hv]; simp [layout.sc.CONSUMED]; omega⟩
  have ea30 : L.actionW s3 = L.actionW s := ea3.trans ea2
  have F3 : FootN st Kp Nd T Cs Sg Scs Z (EH H) s s3 := by
    refine FootN.of' (w2.trans wn) (fun b hb hh => ?_) (AcK.of_eq ea30)
    rcases hh with (hh | rfl) | rfl
    · exact ⟨kw_sc hcS hh.inSC, notIdW_out h.nodes (h.omega _ (hX.1.scW _ hcS b hb hh.inSC)) (noHdr_ring hX.1 hcS hh)⟩
    · exact ⟨kw_sc hcS hcin, notIdW_out h.nodes (h.omega _ (hX.1.scW _ hcS _ hb hcin))
        (noHdr_sc hX.1 hcS hcin (by rw [hv]; simp [layout.sc.CONSUMED]) (by rw [hv]; simp [layout.sc.CONSUMED]))⟩
    · rw [nodeAt_of_ksb w2.1, w2.2.1]
      exact ⟨kw_node h.cur (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]),
        notIdW_node h.nodes h.cur (by simp [layout.node.CONSUMED]) (idOff_ge (by simp [layout.node.CONSUMED]))⟩
  have B3 : FootB st T Cs Sg Scs Z Es s s3 := by
    refine FootB.of' (w2.trans wn) (fun b hb hh => ?_)
    rcases hh with (hh | rfl) | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hcS, hh.inSC⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hcS, hcin⟩)))
    · rw [nodeAt_of_ksb w2.1, w2.2.1]
      exact kwB_node h.cur (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have hper : L.rperiod s3 (L.cscW s3) = 0#u64 := by
    have hp0 : layout.sc.PERIOD.val = 0 := by simp [layout.sc.PERIOD]
    have hpv : (periodA (L.cscW s)).val = (L.cscW s).val := by
      unfold periodA; rw [sc_word_val (o := layout.sc.PERIOD) hP hz (by rw [hp0]; omega), hp0, Nat.add_zero]
    have hal : Aligned (periodA (L.cscW s)) := by unfold Aligned; rw [hpv]; exact h8c
    have hpin : InSC (L.cscW s) (Z (L.cscW s)) (periodA (L.cscW s)) := ⟨by omega, by omega⟩
    rw [ecs3, ecs2]
    unfold LawfulStore.rperiod at hrr ⊢
    rw [← hrr]
    refine (w2.trans wn).mem_eq hal ?_
    rintro ((hh | e) | e)
    · have h1 := hh.1; omega
    · have e' := congrArg UScalar.val e
      rw [hpv, hv] at e'; omega
    · rw [nodeAt_of_ksb w2.1, w2.2.1] at e
      exact out_ne_node (h.omega _ (hX.1.scW _ hcS _ hal hpin)) h.cur hN' (by simp [layout.node.CONSUMED])
        (congrArg UScalar.val e).symm
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
    have hK3 : L.curW s3 ∉ Kp := by rw [ec3, ec2]; exact hKc
    have ha3 : ActOut st T Kp s3 := hKa.step (AcK.of_eq ea30)
    refine WP.spec_bind (sched.end_timeslice.rr (Kp := Kp) (Nd := Nd) (Es := Es) hA s3 a cto Q R h3 hB3 hX3 hSg3 hS3
      hc hK3 hper) ?_
    rintro ⟨s4, a1⟩ ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hSg4, hS4⟩, F4, B4⟩
    try simp only [WP.uncurry'_pair]
    have ha4 : ActOut st T Kp s4 := WritesA.out F4 ha3
    refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.reschedule_required.sch s4 Q4 R4 h4 hB4 hSg4)
      (sched.reschedule_required.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s4 h4 ha4))
      (sched.reschedule_required.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s4 h4)) ?_
    rintro s5 ⟨⟨⟨⟨⟨Q5, R5, h5⟩, hB5, f5⟩, ea5, ec5, -⟩, k5⟩, b5⟩
    refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.set_reprogram.sch s5 Q5 R5 h5 hB5 (hSg4.fr f5))
      (sched.set_reprogram.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s5 h5.nodes h5.cur))
      (sched.set_reprogram.kwB' (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s5 (h5.nodes _ h5.cur) h5.cur)) ?_
    rintro s6 ⟨⟨⟨⟨h6, hB6, f6⟩, ea6, ec6⟩, k6⟩, b6⟩
    simp only [WP.spec_ok, WP.uncurry'_pair]
    exact ⟨⟨⟨Q5, R5, h6⟩, hB6, (hX4.fr f5).fr f6, (hSg4.fr f5).fr f6, (hS4.fr f5).fr f6⟩,
      F3.trans (F4.trans (k5.trans k6)), B3.trans (B4.trans (b5.trans b6)), Or.inl (ea6.trans ea5)⟩
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    exact ⟨⟨⟨Q, R, h3⟩, hB3, hX3, hSg3, hS3⟩, F3, B3, Or.inr ea30⟩

/-- seL4 `checkBudget` when the budget is sufficient or the current SC is
round-robin (and then the current thread is unprotected). -/
theorem sched.check_budget.rr (hA : P0.ArchTotal ar) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hna : L.actionW s ≠ L.curW s) (hcA : L.cscW s ∈ Ac) (hKa : ActOut st T Kp s)
    (hch : ∀ c : U64, sched.consumed st s = ok c → sporadic.sufficient st ar s a (L.cscW s) c = ok false →
      L.rperiod s (L.cscW s) = 0#u64 ∧ L.curW s ∉ Kp) :
    sched.check_budget st ar s a ⦃ _ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootN st Kp Nd T Cs Sg Scs Z (EH H) s s' ∧ FootB st T Cs Sg Scs Z Es s s' ∧
      (L.actionW s' = 1#u64 ∨ L.actionW s' = L.actionW s) ⦄ := by
  have esc : sched.cur_sc st s = ok (L.cscW s) := by
    obtain ⟨v, ev, hv⟩ := spec_ex_fd (sched.cur_sc.spec (st := st) s)
    subst hv; exact ev
  obtain ⟨c, ec, -⟩ := spec_ex_fd (sched.consumed.spec (st := st) s)
  obtain ⟨b, eb, -⟩ := spec_ex_fd (sporadic.sufficient.ok (st := st) hA s a (L.cscW s) c)
  unfold sched.check_budget
  rw [esc]; simp only [bind_ok]
  rw [ec]; simp only [bind_ok]
  rw [eb]; simp only [bind_ok]
  cases b
  · obtain ⟨hrr, hKc⟩ := hch c ec eb
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (sched.charge_budget.rr (Kp := Kp) (Nd := Nd) (Es := Es) hA s a c true Q R h hB hX hSg hS
      hcsc hna hcA hKc hKa hrr) ?_
    rintro ⟨s1, a1⟩ h1
    try simp only [WP.uncurry'_pair] at h1
    refine (WP.spec_ok _).2 ?_
    try simp only [WP.uncurry'_pair]
    exact h1
  · simp only [↓reduceIte]
    unfold sched.is_cur_domain_expired
    simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
    have hnd : ¬ ((1#u64) > (1#u64)) := by simp
    simp only [hnd, ↓reduceIte, bind_ok, WP.spec_ok, WP.uncurry'_pair]
    exact ⟨⟨⟨Q, R, h⟩, hB, hX, hSg, hS⟩, FootN.refl _, FootB.refl _, Or.inr trivial⟩

/-! ## The timer IRQ -/

/-- `handle_interrupt` of a timer IRQ: the current node's `REPROGRAM` and
`ARMED` words. -/
theorem interrupt.handle_interrupt.timer (hA : P0.ArchTotal ar) (s : S) (a : A) (irq : U64)
    (hle : irq.val ≤ 127) (hst : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
    (hb : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    interrupt.handle_interrupt st ar s a irq ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootN st Kp Nd T Cs Sg Scs Z Es s s' ∧ FootB st T Cs Sg Scs Z Es s s' ∧ L.actionW s' = L.actionW s ⦄ := by
  have hq := hb.1.choose_spec.choose_spec
  have hN := hq.nodes _ hq.cur
  unfold interrupt.handle_interrupt
  step with layout.irq.MAX.spec as ⟨mx, emx⟩
  have hmx : mx.val = 127 := by rw [emx]; simp
  split
  · rename_i hgt
    exfalso
    simp at hgt
    omega
  rw [hst]; simp only [bind_ok]
  refine WP.spec_bind (Pₘ := fun r : S × A => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      FootN st Kp Nd T Cs Sg Scs Z Es s r.1 ∧ FootB st T Cs Sg Scs Z Es s r.1 ∧ L.actionW r.1 = L.actionW s) ?_ ?_
  · split
    · rename_i he
      exfalso
      have := congrArg UScalar.val he
      simp [interrupt.IRQ_TIMER, interrupt.IRQ_SIGNAL] at this
    split
    swap
    · rename_i he; exact absurd trivial he
    step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
    step with obj.node_set.spec as ⟨s2, e2⟩
    subst ec e2
    step with obj.node_set.spec as ⟨s3, e3⟩
    subst e3
    have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
    have ar' : layout.node.ARMED.val = 80 := by simp [layout.node.ARMED]
    obtain ⟨⟨k1, -, -⟩, n1, -⟩ := nodew_bxc (o := layout.node.REPROGRAM) (v := 1#u64) hb
        (by simp [layout.node.REPROGRAM, LowFree]) (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
    obtain ⟨⟨k2, -, -⟩, n2, -⟩ := nodew_bxc (o := layout.node.ARMED) (v := 0#u64) k1
      (by simp [layout.node.ARMED, LowFree]) (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED])
    simp only [LawfulStore.cpu_wr] at k2 n2
    have f1 : FootN st Kp Nd T Cs Sg Scs Z Es s (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64) :=
      footN_cur hq.nodes hq.cur (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega) (by rw [rp]; omega)
        (by rw [rp]; omega) (fun _ => by rw [rp]; omega) (by rw [rp]; omega)
    have f2 : FootN st Kp Nd T Cs Sg Scs Z Es (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)
        (L.wr (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)
          (L.nodeAt (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)
            (L.cpu (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)) layout.node.ARMED) 0#u64) :=
      footN_cur (fun c hc' => (hq.nodes c hc').ksb (L.ksb_wr _ _ _)) (by rw [LawfulStore.cpu_wr]; exact hq.cur)
        (by rw [ar']; omega) (by rw [ar']) (by rw [ar']; omega) (by rw [ar']; omega)
        (by rw [ar']; omega) (fun _ => by rw [ar']; omega) (by rw [ar']; omega)
    have g1 : FootB st T Cs Sg Scs Z Es s (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64) :=
      footB_node hN hq.cur (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega)
    have g2 : FootB st T Cs Sg Scs Z Es (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)
        (L.wr (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)
          (L.nodeAt (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)
            (L.cpu (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)) layout.node.ARMED) 0#u64) :=
      footB_node (by rw [LawfulStore.cpu_wr]; exact hN.ksb (L.ksb_wr _ _ _)) (by rw [LawfulStore.cpu_wr]; exact hq.cur)
        (by rw [ar']; omega) (by rw [ar']) (by rw [ar']; omega)
    simp only [LawfulStore.cpu_wr] at f2 g2
    try simp only [WP.spec_ok]
    exact ⟨k2, f1.trans f2, g1.trans g2, n2.1.trans n1.1⟩
  · rintro ⟨s1, a1⟩ h1
    try simp only [WP.uncurry'_pair] at h1
    try dsimp only
    refine WP.spec_bind (hA.ack_irq a1 irq) fun a2 _ => ?_
    simp only [WP.spec_ok, WP.uncurry'_pair]
    exact h1

/-- **[W] No SC overlaps the kernel-global area** (module docstring; P1 has
the TCB and endpoint versions, `SchedQueuesInv.ksOut`, but none for SCs). -/
def ScKsOut (st : machine.Store S) [L : LawfulStore st] (Scs : Set U64) (Z : U64 → Nat) (s : S) : Prop :=
  ∀ c ∈ Scs, c.val + 2 ^ Z c ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ c.val

/-- A `KWB` footprint without endpoint words keeps the kernel-global words. -/
theorem ks_keepB {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInv st T Cs Ω H s Q R) (hSg : SgOK st Ω Sg s) (hKS : ScKsOut st Scs Z s)
    (f : FootB st T Cs Sg Scs Z ∅ s s') {o : U64} (ho : o.val < 13568) (h8 : o.val % 8 = 0) :
    L.mem s' (core.num.U64.wrapping_add (L.ksb s) o) = L.mem s (core.num.U64.wrapping_add (L.ksb s) o) := by
  have hv := ks_val hq ho
  have hout := hq.omega _ (hSg.ksΩ o ho h8)
  refine f.mem_eq (ks_aligned hq ho h8) ?_
  rintro (⟨y, hy, K, -, h2, -, -, -, e⟩ | ⟨c, hc, o', ho', -, e⟩ | hm | ⟨c, hc, hin⟩ | ⟨e', he', -⟩)
  · exact out_ne_field hout hy (hq.tcbs y hy) h2 (congrArg UScalar.val e).symm
  · exact out_ne_node hout hc (hq.nodes c hc) ho' (congrArg UScalar.val e).symm
  · have := hSg.ks _ hm; omega
  · have := hKS c hc; have := hin.1; have := hin.2; omega
  · exact absurd he' (Set.notMem_empty e')

/-- What `round_robin_ok` checked. -/
theorem rr_ok_of {s : S} {a : A} {cpu : U64} {ct : obj.Tcb} {csc : obj.Sc} {now : U64}
    (h : localtimer.round_robin_ok st ar s a cpu ct csc now = ok true) :
    sporadic.is_round_robin st s csc = ok true ∧ sched.is_schedulable st s ct = ok true := by
  unfold localtimer.round_robin_ok at h
  obtain ⟨s1, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨b1, e1, h⟩ := bind_eq_ok h
    cases b1
    · simp at h
    simp only [↓reduceIte] at h
    obtain ⟨b2, e2, h⟩ := bind_eq_ok h
    cases b2
    · simp at h
    exact ⟨e1, e2⟩
  · simp at h

/-- The state at the end of an entry body from `s0` (the hypothesis of `hR`):
P1's `BlkOK`, a `KWN` footprint over `KI` in no-donation mode and a `KWB`
footprint without endpoint words. -/
def EntryEnd (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (s0 s : S) : Prop :=
  BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s ∧
    FootN st (KI st T Cs (L.cpu s0) s0) True T Cs Sg Scs Z (EH H) s0 s ∧ FootB st T Cs Sg Scs Z ∅ s0 s

set_option maxHeartbeats 4000000 in
/-- **The timer-interrupt local entry ends `schedule` in `AllCores`**
(module docstring). Named premises: `hR` [J] (`SchCur` at the end of `awaken`
when the action is `RESUME`, at an `EntryEnd` state), `hS0` [W], `hKS` [W]
(`ScKsOut`). (actv) `allCoresB` also names `schedule`'s start `s3` (`BlkOK`, `BufAt`). -/
theorem timer_irq_local.allCoresB (hA : P0.ArchTotal ar) (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (hKS : ScKsOut st Scs Z s0)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0)
    (hR : ∀ (s : S) (a : A), EntryEnd st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
      ∀ r : S × A, sched.awaken st ar s a = ok r → L.actionW r.1 = 0#u64 → SchCur st r.1)
    (e : localtimer.handle_timer_irq_local st ar s0 a0 irq p = ok (true, s', a')) :
    ∃ s3 a3 s4 a4, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ BufAt st T Cs H Sg Scs Z U s3 ∧
      sched.schedule st ar s3 a3 = ok (s4, a4) ∧ AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧
      (do
        let (s5, a5) ← sched.activate_thread st ar s4 a4
        let t ← sched.cur_thread st s5
        vcpu.check st ar s5 a5 t) = ok (s', a') := by
  -- the walk of `irq_local_same`, keeping what the checks read
  have h := e
  unfold localtimer.handle_timer_irq_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨cpu, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  by_cases c1 : irq > i
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  by_cases c2 : (i1 != interrupt.IRQ_TIMER) = true
  · rw [if_pos c2] at h; simp at h
  rw [if_neg c2] at h
  obtain ⟨tip, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨ct, ect, h⟩ := bind_eq_ok h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨s1, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, -, h⟩ := bind_eq_ok h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  obtain ⟨b4, eb4, h⟩ := bind_eq_ok h
  obtain ⟨due, -, h⟩ := bind_eq_ok h
  obtain ⟨ok1, eok1, h⟩ := bind_eq_ok h
  cases ok1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨x, s2, a2⟩, ecb, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨⟨s3, a3⟩, ehi, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s4, a4⟩, esc, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s5, a5⟩, eac, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨⟨s6, a6⟩, evc, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  have e6 := ok_inj_ff h
  simp only [Prod.mk.injEq, true_and] at e6
  obtain ⟨rfl, rfl⟩ := e6
  have hrr1 : b4 = false → localtimer.round_robin_ok st ar s1 a1 cpu ct csc now = ok true := by
    intro hb; subst hb; revert eok1; cases due <;> simp
  -- the checks' values
  have hmx : i.val = 127 := by
    obtain ⟨v, ev, hv⟩ := spec_ex_fd layout.irq.MAX.spec
    rw [ei] at ev; cases ok_inj_ff ev; subst hv; simp
  have hle : irq.val ≤ 127 := by
    have c1' := c1
    simp at c1'
    omega
  have hst0 : interrupt.irq_state st s0 irq = ok interrupt.IRQ_TIMER := by
    rw [ei1]
    have e1 : i1 = interrupt.IRQ_TIMER := by
      by_contra hne
      first | exact c2 (bne_iff_ne.mpr hne) | exact c2 (by simp [hne])
    rw [e1]
  have ect' : ct = L.curW s0 := by
    obtain ⟨v, ev, hv⟩ := spec_ex_fd (sched.cur_thread.spec (st := st) s0)
    rw [ect] at ev; cases ok_inj_ff ev; exact hv
  have ecsc' : csc = L.cscW s0 := by
    obtain ⟨v, ev, hv⟩ := spec_ex_fd (sched.cur_sc.spec (st := st) s0)
    rw [ecsc] at ev; cases ok_inj_ff ev; exact hv
  -- the invariants at the entry
  have hI0c := hI0
  obtain ⟨⟨Q0, R0, hq0⟩, hB0', hX0, hS0', -, -, -, -⟩ := hI0c
  have hSg0 : SgOK st Ω Sg s0 := hS0'.sg
  have hB0 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s0 := ⟨⟨Q0, R0, hq0⟩, hB0', hX0, hS0', hSg0⟩
  have hT := hq0.tcbs
  -- `update_timestamp`
  have U1 := sched.update_timestamp.entry hA s0 a0 hI0
  have U2 := sched.update_timestamp.bxc hA s0 a0 (EntryInv.bxi hI0)
  have U3 := sched.update_timestamp.kwN (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) hA s0 a0 hq0.nodes hq0.cur
  have U4 := sched.update_timestamp.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := (∅ : Set U64)) hA s0 a0
    (hq0.nodes _ hq0.cur) hq0.cur
  rw [eu] at U1 U2 U3 U4
  simp only [WP.spec_ok, WP.uncurry'_pair] at U1 U2 U3 U4
  obtain ⟨⟨⟨Q1, R1, hq1⟩, hB1, hX1, hSg1, hS1⟩, ecs1, hcA1, hna1, hcsc1, hck1⟩ := U1
  obtain ⟨-, n1, -⟩ := U2
  have ea1 : L.actionW s1 = L.actionW s0 := n1.1
  have ecur1 : L.curW s1 = L.curW s0 := hck1.1
  have iT : idleAt st (L.cpu s0) s0 ∈ T := (h0.core hcpu).per.idleT
  -- `check_budget`
  have hKa1 : ActOut st T (KI st T Cs (L.cpu s0) s0) s1 := fun hTa _ => by
    rw [ea1] at hTa; exact h0.actNT _ hcpu hTa
  have hch : ∀ c : U64, sched.consumed st s1 = ok c → sporadic.sufficient st ar s1 a1 (L.cscW s1) c = ok false →
      L.rperiod s1 (L.cscW s1) = 0#u64 ∧ L.curW s1 ∉ KI st T Cs (L.cpu s0) s0 := by
    intro c ec ef
    rw [ei2] at ec
    cases ok_inj_ff ec
    rw [ecs1, ← ecsc', eb4] at ef
    cases ok_inj_ff ef
    obtain ⟨err, esch⟩ := rr_ok_of (hrr1 rfl)
    obtain ⟨v, ev, hv⟩ := spec_ex_fd (sporadic.is_round_robin.spec (st := st) s1 csc)
    rw [err] at ev
    cases ok_inj_ff ev
    obtain ⟨w, ew, hw⟩ := spec_ex_fd (sched.is_schedulable.spec' (st := st) s1 ct)
    rw [esch] at ew
    cases ok_inj_ff ew
    have hrun := (hw rfl).1
    refine ⟨by rw [ecs1, ← ecsc']; exact of_decide_eq_true hv.symm, ?_⟩
    rintro (hK | hI)
    · rw [ecur1] at hK
      exact h0.notK (h0.curAff _ hcpu) hK
    · have hid : L.mem s1 (stA (idleAt st (L.cpu s0) s0)) = sched.TS_IDLE :=
        (U3.idKeep (by rw [stA_eq]; exact field_aligned (hT _ iT) (by simp) (by simp))
          (Or.inr (Or.inl ⟨_, iT, hT _ iT, Or.inr rfl, Or.inl rfl⟩))).trans (h0.idleSt _ hcpu)
      rw [← hI, ecur1, ← ect'] at hid
      rw [hid] at hrun
      exact tsIdle_nr hrun
  have C := sched.check_budget.rr (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Es := (∅ : Set U64)) hA s1 a1 Q1 R1 hq1 hB1
    hX1 hSg1 hS1 hcsc1 hna1 hcA1 hKa1 hch
  rw [ecb] at C
  simp only [WP.spec_ok, WP.uncurry'_pair] at C
  obtain ⟨⟨⟨Q2, R2, hq2⟩, hB2, hX2, hSg2, hS2⟩, F2, B2, ea2⟩ := C
  have B02 : FootB st T Cs Sg Scs Z ∅ s0 s2 := U4.trans B2
  -- the IRQ state, still `IRQ_TIMER`
  have hst2 : interrupt.irq_state st s2 irq = ok interrupt.IRQ_TIMER := by
    rw [← hst0]
    unfold interrupt.irq_state interrupt.state_off
    simp only [lift, bind_ok]
    obtain ⟨bk, ebk, hbk⟩ := spec_ex_fd P0.Consts.layout.ks.IRQ_STATE.spec
    rw [ebk]; simp only [bind_ok]
    have ho : (core.num.U64.wrapping_add bk (core.num.U64.wrapping_mul irq 8#u64)).val = 224 + 8 * irq.val := by
      subst hbk
      simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
    obtain ⟨v2, ev2, hv2⟩ := spec_ex_fd (obj.ks_get.spec (st := st) s2
      (core.num.U64.wrapping_add bk (core.num.U64.wrapping_mul irq 8#u64)))
    obtain ⟨v0, ev0, hv0⟩ := spec_ex_fd (obj.ks_get.spec (st := st) s0
      (core.num.U64.wrapping_add bk (core.num.U64.wrapping_mul irq 8#u64)))
    rw [ev2, ev0, hv2, hv0, B02.1]
    rw [ks_keepB (o := core.num.U64.wrapping_add bk (core.num.U64.wrapping_mul irq 8#u64)) hq0 hSg0 hKS B02
      (by omega) (by omega)]
  -- `handle_interrupt`
  have Hi := interrupt.handle_interrupt.timer (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Es := EH H) hA s2 a2 irq hle hst2
    ⟨⟨Q2, R2, hq2⟩, hB2, hX2, hSg2, hS2⟩
  have Hb := interrupt.handle_interrupt.timer (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Es := (∅ : Set U64)) hA s2 a2 irq
    hle hst2 ⟨⟨Q2, R2, hq2⟩, hB2, hX2, hSg2, hS2⟩
  rw [ehi] at Hi Hb
  simp only [WP.spec_ok, WP.uncurry'_pair] at Hi Hb
  obtain ⟨⟨⟨Q3, R3, hq3⟩, hB3, hX3, hSg3, hS3⟩, F3, -, ea3⟩ := Hi
  obtain ⟨-, -, B3, -⟩ := Hb
  -- the body's end
  have F03 : FootN st (KI st T Cs (L.cpu s0) s0) True T Cs Sg Scs Z (EH H) s0 s3 := U3.trans (F2.trans F3)
  have B03 : FootB st T Cs Sg Scs Z ∅ s0 s3 := B02.trans B3
  have hBlk3 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 := ⟨⟨Q3, R3, hq3⟩, hB3, hX3, hS3, hSg3⟩
  have hBA3 : BufAt st T Cs H Sg Scs Z U s3 :=
    BufAt.of_fr hBA0 (IbFr.of_bufKeep B03.1
      (BufKeep.of_footB hq0 hX0.1 hSg0.sub (fun e' he' => absurd he' (Set.notMem_empty e')) B03))
  have hsa3 : ActAff st T s3 := by
    refine ActAff.nT ?_
    rw [ea3]
    rcases ea2 with e2 | e2
    · rw [e2]; exact one_notT hq0
    · rw [e2, ea1]; exact h0.actNT _ hcpu
  have W := AllCores.schedB hA IK hNt a3 h0 hcpu hS0 hB0 F03 hBlk3 hBA3 hsa3 (hR s3 a3 ⟨hBlk3, F03, B03⟩)
  rw [esc] at W
  simp only [WP.spec_ok, WP.uncurry'_pair] at W
  refine ⟨s3, a3, s4, a4, hBlk3, hBA3, esc, W, ?_⟩
  rw [eac]; simp only [bind_ok, uncurry_apply_pair]
  rw [et]; simp only [bind_ok]
  exact evc

set_option maxHeartbeats 4000000 in
/-- **The timer-interrupt local entry ends `schedule` in `AllCores`**
(module docstring). Named premises: `hR` [J] (`SchCur` at the end of `awaken`
when the action is `RESUME`, at an `EntryEnd` state), `hS0` [W], `hKS` [W]
(`ScKsOut`). -/
theorem timer_irq_local.allCores (hA : P0.ArchTotal ar) (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (hKS : ScKsOut st Scs Z s0)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0)
    (hR : ∀ (s : S) (a : A), EntryEnd st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
      ∀ r : S × A, sched.awaken st ar s a = ok r → L.actionW r.1 = 0#u64 → SchCur st r.1)
    (e : localtimer.handle_timer_irq_local st ar s0 a0 irq p = ok (true, s', a')) :
    ∃ s4 a4, AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧
      (do
        let (s5, a5) ← sched.activate_thread st ar s4 a4
        let t ← sched.cur_thread st s5
        vcpu.check st ar s5 a5 t) = ok (s', a') := by
  obtain ⟨-, -, s4, a4, -, -, -, W, E⟩ := timer_irq_local.allCoresB hA IK hNt h0 hcpu hS0 hKS hI0 hBA0 hR e
  exact ⟨s4, a4, W, E⟩

end

end Fl4Proofs.P2.Stall
