/-
P2 (wire): **the local entries that call `schedule` end in `AllCores`, with
`hR`, `hS0` and `hKS` discharged.**

`timer_irq_local.allCores[B|Exit]` (`P2/EntryIrq.lean`, `P2/EntryExit.lean`)
and `set_timer_local.allCores[B|Exit]` (`P2/EntryTmr.lean`) carry `hR` [J]
(`SchCur` at the end of `awaken` under `RESUME`), `hS0` [W] (`0 ∉ Scs`) and,
for the timer IRQ, `hKS` [W] (`ScKsOut`). Here:

* `hKS`: P1's `BlkOK.scKsOut` (par/scks) at the entry (`ScKsOut` is a def with
  the same body).
* `hS0`: P1's `ObjsOK.sc0` (no SC is at address 0) at the entry.
* `hR`: through `AllCores.schedBH` (P2/FootN11, `hR` = `sched.awaken.rc`),
  which needs, at the body's end, `DomInv` (FL4's one domain) and `RC` (with
  action `RESUME` the current thread is `SchCur`). Both are carried over the
  body from the entry: `DomInv` at the entry is an entry fact (`hD0`; P1
  `DomInv`, P3 `kernel_entry_domInvU29` at joint states), `RC` at the entry
  is `AllCores`' current-thread clauses (`AllCores.rc`).

  Each body step keeps them: the node words, the SC words (frame words, `Sg`,
  so outside the TCBs and the kernel-global area: `domFree_sg`), the TCB
  register fields and the queue footprints are `DomFree`; the steps that
  keep the action write no word `SchCur` reads (a `FootN` protecting every
  thread, `RC.fnT`), `set_thread_state` writes the current thread's `STATE`
  with a runnable value (`RC.sts`), and the round-robin budget charge ends
  with action `CHOOSE_NEW` when it runs `end_timeslice` (`RC.nz`).

* `sched.update_timestamp.dom`, `interrupt.handle_interrupt.timer.dom`,
  `sched.append.domInv`, `end_suff.dom`, `sched.end_timeslice.dom`,
  `scw_facts`, `sched.charge_budget.rrW`, `sched.check_budget.rrW`,
  `obj.Tcb.set_reg.dom`, `msg.reply_success_empty.dom`: the steps.
* **`timer_irq_local.allCoresBW`**, **`timer_irq_local.allCoresW`**,
  **`timer_irq_local.allCoresExitW`**, **`set_timer_tailBW`**,
  **`set_timer_local.allCoresBW`**, **`set_timer_local.allCoresW`**,
  **`set_timer_local.allCoresExitW`**: the wrappers with the reduced premise
  lists (the old ones are kept).

Entry facts (inputs, as `hI0`/`hBA0`): `AllCores s0`, P1's `EntryInv` and
`BufAt` at the entry, `hD0 : DomInv st T s0`. Named premises left: none for
the `B`/plain wrappers; for the `Exit` wrappers, that of `AllCores.exit`:
`hVW` [P] (`VcpuUsr`) (`SchIb` is discharged by sib, `schIb_holds`). (comb) The
`B` wrappers also export the body's `FootB` from the entry to `schedule`'s
start, as sib's `allCoresB`; `P2/EntryFinal.lean` uses it.
-/
import Fl4Proofs.P2.EntryExit
import Fl4Proofs.P2.FootN11
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es U : Set U64}
variable {A : Type _} {ar : machine.Arch A}
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

/-! ## Entry facts -/

/-- `RC` at an `AllCores` state (its current-thread clauses). -/
theorem AllCores.rc {s : S} (h : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hcpu : L.cpu s ∈ Cs) : RC st s :=
  fun _ => ⟨h.curAff _ hcpu, h.curNB _ hcpu, h.nq _ hcpu⟩

/-- `0 ∉ Scs` from P1's `ObjsOK.sc0`. -/
theorem ObjsOK.zero_notScs {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) : (0#u64) ∉ Scs :=
  fun h => hO.sc0 _ h rfl

/-! ## `DomInv` through the body steps -/

/-- `update_timestamp` (two current-node words) keeps `DomInv`. -/
theorem sched.update_timestamp.dom (hA : P0.ArchTotal ar) (s : S) (a : A)
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hD : DomInv st T s) :
    sched.update_timestamp st ar s a ⦃ s' _ => DomInv st T s' ⦄ := by
  have hN := hq.nodes _ hq.cur
  unfold sched.update_timestamp
  step with sched.cur_time.spec as ⟨prev⟩
  refine WP.spec_bind (hA.now a) ?_
  rintro ⟨now, a1⟩ -
  try simp only [WP.uncurry'_pair]
  step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
  step with obj.node_set.spec as ⟨s1, e1⟩
  subst ec e1
  have D1 : DomInv st T (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now) :=
    DomInv.wr' hD hq.tcbs hN
      (nodeAt_aligned hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (node_domFree hq.tcbs hN (by simp [layout.node.CUR_TIME]))
  step as ⟨used, _⟩
  step with sched.consumed.spec as ⟨i⟩
  step as ⟨total, _⟩
  step with sched.set_consumed.spec as ⟨s2, e2⟩
  rw [show ∀ s0 : S, L.nodeA s0 layout.node.CONSUMED = L.nodeAt s0 (L.cpu s0) layout.node.CONSUMED from
    fun _ => rfl] at e2
  subst e2
  have hN1 : NodePlaced st T (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now)
      (L.cpu (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now)) := by
    rw [LawfulStore.cpu_wr]; exact hN.ksb (L.ksb_wr _ _ _)
  have D2 := DomInv.wr' (v := total) D1 hq.tcbs hN1
    (nodeAt_aligned (off := layout.node.CONSUMED) hN1 (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
    (node_domFree (o := layout.node.CONSUMED) hq.tcbs hN1 (by simp [layout.node.CONSUMED]))
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have hnd : ¬ ((1#u64) > (1#u64)) := by simp
  simp only [hnd, ↓reduceIte, WP.spec_ok, WP.uncurry'_pair]
  exact D2

/-- `handle_interrupt` of a timer IRQ (the current node's `REPROGRAM` and
`ARMED` words) keeps `DomInv`. -/
theorem interrupt.handle_interrupt.timer.dom (hA : P0.ArchTotal ar) (s : S) (a : A) (irq : U64)
    (hle : irq.val ≤ 127) (hst : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hD : DomInv st T s) :
    interrupt.handle_interrupt st ar s a irq ⦃ s' _ => DomInv st T s' ⦄ := by
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
  refine WP.spec_bind (Pₘ := fun r : S × A => DomInv st T r.1) ?_ ?_
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
    have ar' : layout.node.ARMED.val = 80 := by simp [layout.node.ARMED]
    have D1 := (reprogram_facts (v := 1#u64) hq).2.1 hD
    have hN1 : NodePlaced st T (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)
        (L.cpu (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)) := by
      rw [LawfulStore.cpu_wr]; exact hN.ksb (L.ksb_wr _ _ _)
    have hN1' : NodePlaced st T (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64) (L.cpu s) :=
      hN.ksb (L.ksb_wr _ _ _)
    try simp only [WP.spec_ok]
    exact DomInv.wr' D1 hq.tcbs hN1 (nodeAt_aligned hN1' (by rw [ar']; omega) (by rw [ar']))
      (node_domFree hq.tcbs hN1' (by rw [ar']; omega))
  · rintro ⟨s1, a1⟩ h1
    try simp only [WP.uncurry'_pair] at h1
    try dsimp only
    refine WP.spec_bind (hA.ack_irq a1 irq) fun a2 _ => ?_
    simp only [WP.spec_ok, WP.uncurry'_pair]
    exact h1

theorem sched.append.domInv (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hD : DomInv st T s) : sched.append st s t ⦃ s' => DomInv st T s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_mono (sched.append.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (fun h0 => h.notQ ht h0 hc hp)) fun s' hh => hD.free hh.1 h.tcbs (cdomA_alignedN (h.nodes _ h.cur))
      fun b hb => QFoot.domFree h.tcbs (h.nodes _ hc) (h.nodes _ h.cur) ?_ ht h.ksOut hb
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact (hR1.1.rel _ hp).mem w hw

/-- `end_suff` (`append` or `postpone` of the current thread) keeps `DomInv`. -/
theorem end_suff.dom (hA : P0.ArchTotal ar) (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hc : CurOK st T s) (hD : DomInv st T s) :
    (do
      let b ← sporadic.ready st s (L.cscW s)
      if b = true then do
        let b1 ← sporadic.sufficient st ar s a (L.cscW s) 0#u64
        if b1 = true then do let s1 ← sched.append st s (L.curW s); ok (s1, a)
        else do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a)
      else do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a))
      ⦃ s' _ => DomInv st T s' ⦄ := by
  have hcT : L.curW s ∈ T := h.curT
  obtain ⟨hSc, htc, hcore⟩ := hX.2.2.bound (L.curW s) hcT hc.bnd
  rw [← hc.csc] at hSc htc hcore
  have hco : OutsideObjs st T Cs s (scCoreA (L.cscW s)) := h.omega _ ((objs_omega hX.1 hSg.sub).2 _ hSc).2.1
  have P : (do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a)) ⦃ s' _ => DomInv st T s' ⦄ :=
    WP.spec_bind (sched.postpone.dom s _ h (by rw [htc]; exact hcT) (by rw [htc]; exact hc.rel) hco hcore hD)
      fun s1 f1 => by simp only [WP.spec_ok, WP.uncurry'_pair]; exact f1
  have Ap : (do let s1 ← sched.append st s (L.curW s); ok (s1, a)) ⦃ s' _ => DomInv st T s' ⦄ :=
    WP.spec_bind (sched.append.domInv s _ h hcT hD) fun s1 f1 => by
      simp only [WP.spec_ok, WP.uncurry'_pair]; exact f1
  step with sporadic.ready.spec as ⟨b⟩
  split
  · step with sporadic.sufficient.ok (st := st) hA as ⟨b1⟩
    split
    · exact Ap
    · exact P
  · exact P

/-- seL4 `endTimeslice` on a round-robin current SC keeps `DomInv`. -/
theorem sched.end_timeslice.dom (hA : P0.ArchTotal ar) (s : S) (a : A) (cto : Bool)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hc : CurOK st T s) (hrr : L.rperiod s (L.cscW s) = 0#u64) (hD : DomInv st T s) :
    sched.end_timeslice st ar s a cto ⦃ s' _ => DomInv st T s' ⦄ := by
  have E := end_suff.dom hA s a Q R h hX hSg hc hD
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

/-- Writes of an SC's words keep the action, `DomInv` and `RC` (the SC's
words are frame words, outside the TCBs and the kernel-global area). -/
theorem scw_facts {s s' : S} {i : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hi : i ∈ Scs)
    (w : WritesIn st s s' (fun b => InSC i (Z i) b)) :
    L.actionW s' = L.actionW s ∧ (DomInv st T s → DomInv st T s') ∧ (RC st s → RC st s') := by
  have hN := hq.nodes _ hq.cur
  have hact : L.actionW s' = L.actionW s :=
    actionW_of w hN fun hr => notAct_omega hq (hX.1.scW i hi _ (act_aligned hN) hr)
  exact ⟨hact, fun hD => DomInv.freeA hD w hq.tcbs (cdomA_alignedN hN) fun b hb hh =>
      domFree_sg hq hS.sg ((hS.all i hi).2.2 b hb hh),
    RC.wi hq w (fun _ b hb hh => CurFree.out hq (hq.omega _ (hX.1.scW i hi b hb hh))) hact⟩

set_option maxHeartbeats 1000000 in
/-- seL4 `chargeBudget` on a round-robin current SC keeps `DomInv` and `RC`:
the SC and node words it writes are `DomFree` and `CurFree`; when it runs
`end_timeslice` it ends with action `CHOOSE_NEW`. -/
theorem sched.charge_budget.rrW (hA : P0.ArchTotal ar) (s : S) (a : A) (used : U64) (cto : Bool)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hna : L.actionW s ≠ L.curW s) (hcA : L.cscW s ∈ Ac) (hrr : L.rperiod s (L.cscW s) = 0#u64)
    (hD : DomInv st T s) (hr : RC st s) :
    sched.charge_budget st ar s a used cto ⦃ s' _ => DomInv st T s' ∧ RC st s' ⦄ := by
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
  obtain ⟨-, D2, r2⟩ := scw_facts h hX hS hcS (w2.mono fun b hb => by
    rcases hb with hb | rfl
    · exact hb.inSC
    · exact hcin)
  have D3 : DomInv st T s3 := DomInv.freeA (D2 hD) wn h2.tcbs (cdomA_alignedN hN2) fun b _ hb => by
    subst hb; exact node_domFree h2.tcbs hN2 (by simp [layout.node.CONSUMED])
  have r3 : RC st s3 := RC.wi h2 wn (fun _ b _ hb => by
    subst hb
    exact CurFree.node h2 h2.cur (by simp [layout.node.CONSUMED]) (fun _ => by simp [layout.node.CONSUMED]))
    ea3 (r2 hr)
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
    refine WP.spec_bind (WP.spec_and (sched.end_timeslice.rr (Kp := (∅ : Set U64)) (Nd := True)
      (Es := (∅ : Set U64)) hA s3 a cto Q R h3 hB3 hX3 hSg3 hS3 hc (Set.notMem_empty _) hper)
      (sched.end_timeslice.dom hA s3 a cto Q R h3 hX3 hSg3 hc hper D3)) ?_
    rintro ⟨s4, a1⟩ hh4
    try simp only [WP.uncurry'_pair] at hh4
    obtain ⟨⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hSg4, hS4⟩, -, -⟩, D4⟩ := hh4
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (WP.spec_and (sched.reschedule_required.sch s4 Q4 R4 h4 hB4 hSg4)
      (sched.reschedule_required.domInv s4 h4 D4)) ?_
    rintro s5 ⟨⟨⟨⟨Q5, R5, h5⟩, hB5, f5⟩, ea5, -, -⟩, D5⟩
    refine WP.spec_bind (sched.set_reprogram.spec s5) ?_
    rintro s6 e6
    rw [show L.nodeA s5 layout.node.REPROGRAM = L.nodeAt s5 (L.cpu s5) layout.node.REPROGRAM from rfl] at e6
    subst e6
    obtain ⟨ea6, d6, -⟩ := reprogram_facts (v := 1#u64) h5
    simp only [WP.spec_ok, WP.uncurry'_pair]
    exact ⟨d6 D5, RC.nz (by rw [ea6, ea5]; exact u1_ne0)⟩
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    exact ⟨D3, r3⟩

/-- seL4 `checkBudget` when the budget is sufficient or the current SC is
round-robin keeps `DomInv` and `RC`. -/
theorem sched.check_budget.rrW (hA : P0.ArchTotal ar) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hna : L.actionW s ≠ L.curW s) (hcA : L.cscW s ∈ Ac)
    (hch : ∀ c : U64, sched.consumed st s = ok c → sporadic.sufficient st ar s a (L.cscW s) c = ok false →
      L.rperiod s (L.cscW s) = 0#u64)
    (hD : DomInv st T s) (hr : RC st s) :
    sched.check_budget st ar s a ⦃ _ s' _ => DomInv st T s' ∧ RC st s' ⦄ := by
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
  · have hrr := hch c ec eb
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (sched.charge_budget.rrW hA s a c true Q R h hB hX hSg hS hcsc hna hcA hrr hD hr) ?_
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
    exact ⟨hD, hr⟩

/-- A register write of a TCB keeps `DomInv`. -/
theorem obj.Tcb.set_reg.dom (s : S) {t r v : U64} (hr : r.val < 384) (hq : SchedQueuesInvX st T Cs Ω H X s Q R)
    (ht : t ∈ T) (hD : DomInv st T s) : obj.Tcb.set_reg st t s r v ⦃ s' => DomInv st T s' ⦄ := by
  have hN := hq.nodes _ hq.cur
  refine WP.spec_mono (obj.Tcb.set_reg.wrK s t r v (hq.tcbs t ht) hr) ?_
  rintro s' ⟨K, hK, rfl⟩
  exact DomInv.wr' hD hq.tcbs hN (field_aligned (hq.tcbs t ht) (by omega) (by omega))
    (field_domFree hq.tcbs hN ht (hq.ksOut t ht) (by omega) (by omega))

/-- `reply_success_empty t` (two register writes of `t`) keeps `DomInv`. -/
theorem msg.reply_success_empty.dom (s : S) (t : obj.Tcb) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hD : DomInv st T s) : msg.reply_success_empty st s t ⦃ s' => DomInv st T s' ⦄ := by
  unfold msg.reply_success_empty
  refine WP.spec_bind (WP.spec_and (obj.Tcb.set_reg.blk s (r := layout.reg.BADGE)
    (by simp [layout.reg.BADGE, layout.reg.RDI]) h ht)
    (obj.Tcb.set_reg.dom s (r := layout.reg.BADGE) (by simp [layout.reg.BADGE, layout.reg.RDI])
      h.1.choose_spec.choose_spec ht hD)) fun s1 h1 => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 0#u64 0#u64 0#u64 0#u64) fun mi _ => ?_
  unfold msg.set_msg_info
  refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 mi) fun w _ => ?_
  exact obj.Tcb.set_reg.dom s1 (r := layout.reg.MSG_INFO) (by simp [layout.reg.MSG_INFO, layout.reg.RSI])
    h1.1.1.1.choose_spec.choose_spec ht h1.2

/-! ## The timer-interrupt local entry -/

set_option maxHeartbeats 4000000 in
/-- **The timer-interrupt local entry ends `schedule` in `AllCores`**
(`timer_irq_local.allCoresB` with `hR`, `hS0`, `hKS` discharged; module
docstring). Entry facts: `h0`, `hI0`, `hBA0`, `hD0` (`DomInv`). No named
premise. -/
theorem timer_irq_local.allCoresBW (hA : P0.ArchTotal ar) (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0)
    (hD0 : DomInv st T s0)
    (e : localtimer.handle_timer_irq_local st ar s0 a0 irq p = ok (true, s', a')) :
    ∃ s3 a3 s4 a4, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ BufAt st T Cs H Sg Scs Z U s3 ∧
      FootB st T Cs Sg Scs Z ∅ s0 s3 ∧ sched.schedule st ar s3 a3 = ok (s4, a4) ∧ AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧
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
  -- (wire) `hS0`, `hKS` from P1; `RC` at the entry
  have hS0 : (0#u64) ∉ Scs := ObjsOK.zero_notScs hX0.1
  have hKS : ScKsOut st Scs Z s0 := hB0.scKsOut
  have hrs0 : RC st s0 := AllCores.rc h0 hcpu
  -- `update_timestamp`
  have U5 := sched.update_timestamp.kwN (Kp := T) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) hA s0 a0 hq0.nodes hq0.cur
  have U6 := sched.update_timestamp.dom hA s0 a0 hq0 hD0
  rw [eu] at U5 U6
  simp only [WP.spec_ok, WP.uncurry'_pair] at U5 U6
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
  have D1 : DomInv st T s1 := U6
  have r1 : RC st s1 := RC.fnT hq0 U5 ea1 hrs0
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
  have CW := sched.check_budget.rrW hA s1 a1 Q1 R1 hq1 hB1 hX1 hSg1 hS1 hcsc1 hna1 hcA1
    (fun c ec ef => (hch c ec ef).1) D1 r1
  rw [ecb] at CW
  simp only [WP.spec_ok, WP.uncurry'_pair] at CW
  obtain ⟨D2, r2⟩ := CW
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
  have HT := interrupt.handle_interrupt.timer (Kp := T) (Nd := True) (Es := EH H) hA s2 a2 irq hle hst2
    ⟨⟨Q2, R2, hq2⟩, hB2, hX2, hSg2, hS2⟩
  have HD := interrupt.handle_interrupt.timer.dom hA s2 a2 irq hle hst2 hq2 D2
  rw [ehi] at HT HD
  simp only [WP.spec_ok, WP.uncurry'_pair] at HT HD
  have D3 : DomInv st T s3 := HD
  have r3 : RC st s3 := RC.fnT hq2 HT.2.1 HT.2.2.2 r2
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
  have W := AllCores.schedBH hA IK hNt a3 h0 hcpu hS0 hB0 F03 hBlk3 hBA3 hsa3 D3 r3
  rw [esc] at W
  simp only [WP.spec_ok, WP.uncurry'_pair] at W
  refine ⟨s3, a3, s4, a4, hBlk3, hBA3, B03, esc, W, ?_⟩
  rw [eac]; simp only [bind_ok, uncurry_apply_pair]
  rw [et]; simp only [bind_ok]
  exact evc

/-- **The timer-interrupt local entry ends `schedule` in `AllCores`**
(`timer_irq_local.allCores` with `hR`, `hS0`, `hKS` discharged). No named
premise. -/
theorem timer_irq_local.allCoresW (hA : P0.ArchTotal ar) (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0)
    (hD0 : DomInv st T s0)
    (e : localtimer.handle_timer_irq_local st ar s0 a0 irq p = ok (true, s', a')) :
    ∃ s4 a4, AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧
      (do
        let (s5, a5) ← sched.activate_thread st ar s4 a4
        let t ← sched.cur_thread st s5
        vcpu.check st ar s5 a5 t) = ok (s', a') := by
  obtain ⟨-, -, s4, a4, -, -, -, -, W, E⟩ := timer_irq_local.allCoresBW hA IK hNt h0 hcpu hI0 hBA0 hD0 e
  exact ⟨s4, a4, W, E⟩

/-- **The timer-interrupt local entry ends in `AllCores`** at the entry's exit
(`timer_irq_local.allCoresExit` with `hR`, `hS0`, `hKS` discharged). Named
premise: `hVW` [P] (`VcpuUsr`), as `AllCores.exit` (sib: `SchIb` discharged). -/
theorem timer_irq_local.allCoresExitW (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0)
    (hD0 : DomInv st T s0)
    (hVW : ∀ s : S, AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s → VcpuUsr st T Cs H Sg Scs Z s)
    (e : localtimer.handle_timer_irq_local st ar s0 a0 irq p = ok (true, s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨s3, a3, s4, a4, hB3, hBA3, -, esc, W, E⟩ :=
    timer_irq_local.allCoresBW hA IK hNt h0 hcpu hI0 hBA0 hD0 e
  have hS0 : (0#u64) ∉ Scs := by
    obtain ⟨-, -, hX0, -⟩ := hI0
    exact ObjsOK.zero_notScs hX0.1
  exact AllCores.exit hA IK hNt hS0 hVW hB3 hBA3 esc W E

/-! ## The `TCB_SetTimer` local entry -/

set_option maxHeartbeats 4000000 in
/-- **The body and `schedule` of an accepted `TCB_SetTimer` local entry**,
from the run's equations: `AllCores` at `schedule`'s end (`set_timer_tailB`
with `hR`, `hS0` discharged; entry fact `hD0`). No named premise. -/
theorem set_timer_tailBW (hA : P0.ArchTotal ar) (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s1 s2 s3 s4 s5 s6 s7 : S} {a0 a1 a2 : A} {t tg d bd v : U64}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0) (htg : tg ∈ T)
    (hD0 : DomInv st T s0)
    (ect : sched.cur_thread st s0 = ok t) (hrun : L.mem s0 (stA t) = sched.TS_RUNNING)
    (es1 : obj.Tcb.set_reg st t s0 layout.reg.FAULT_IP v = ok s1)
    (eu : sched.update_timestamp st ar s1 a0 = ok (s2, a1))
    (es3 : sched.set_thread_state st s2 t sched.TS_RESTART = ok s3)
    (es4 : timer.insert st s3 tg d bd = ok s4)
    (es5 : msg.reply_success_empty st s4 t = ok s5)
    (es6 : sched.set_thread_state st s5 t sched.TS_RUNNING = ok s6)
    (esc : sched.schedule st ar s6 a1 = ok (s7, a2)) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s6 ∧ BufAt st T Cs H Sg Scs Z U s6 ∧
      FootB st T Cs Sg Scs Z ∅ s0 s6 ∧ AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s7 := by
  have ect' : t = L.curW s0 := by
    obtain ⟨w, ew, hw⟩ := spec_ex_fd (sched.cur_thread.spec (st := st) s0)
    rw [ect] at ew; cases ok_inj_ff ew; exact hw
  have hI0c := hI0
  obtain ⟨⟨Q0, R0, hq0⟩, hB0', hX0, hS0', -, -, -, -⟩ := hI0c
  have hSg0 : SgOK st Ω Sg s0 := hS0'.sg
  have hB0 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s0 := ⟨⟨Q0, R0, hq0⟩, hB0', hX0, hS0', hSg0⟩
  have hT := hq0.tcbs
  have htT : t ∈ T := by rw [ect']; exact hq0.curT
  have hS0 : (0#u64) ∉ Scs := ObjsOK.zero_notScs hX0.1
  have hrs0 : RC st s0 := AllCores.rc h0 hcpu
  have hKt : t ∉ KI st T Cs (L.cpu s0) s0 := by
    rintro (hK | hI)
    · rw [ect'] at hK; exact h0.notK (h0.curAff _ hcpu) hK
    · have hid := h0.idleSt _ hcpu
      rw [← hI, hrun] at hid
      exact tsRunning_ne_idle hid
  -- the `FAULT_IP` write
  have S1 := obj.Tcb.set_reg.nb (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Es := EH H) (Eb := (∅ : Set U64)) s0
    (r := layout.reg.FAULT_IP) (v := v) (by simp [layout.reg.FAULT_IP]) hB0 htT
  rw [es1] at S1
  simp only [WP.spec_ok] at S1
  obtain ⟨hB1, F1, B1, ea1, est1⟩ := S1
  have S1T := obj.Tcb.set_reg.nb (Kp := T) (Nd := True) (Es := EH H) (Eb := (∅ : Set U64)) s0
    (r := layout.reg.FAULT_IP) (v := v) (by simp [layout.reg.FAULT_IP]) hB0 htT
  have S1D := obj.Tcb.set_reg.dom s0 (r := layout.reg.FAULT_IP) (v := v) (by simp [layout.reg.FAULT_IP]) hq0 htT hD0
  rw [es1] at S1T S1D
  simp only [WP.spec_ok] at S1T S1D
  have D1 : DomInv st T s1 := S1D
  have r1 : RC st s1 := RC.fnT hq0 S1T.2.1 ea1 hrs0
  -- `update_timestamp`
  obtain ⟨⟨Q1, R1, hq1⟩, hBd1, hX1, hS1, hSg1⟩ := hB1
  have U2 := sched.update_timestamp.bxc hA s1 a0 ⟨⟨Q1, R1, hq1⟩, hBd1, hX1, hSg1, hS1⟩
  have U3 := sched.update_timestamp.kwN (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) hA s1 a0 hq1.nodes hq1.cur
  have U3t := sched.update_timestamp.kwN (Kp := ({t} : Set U64)) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) hA s1 a0 hq1.nodes hq1.cur
  have U4 := sched.update_timestamp.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := (∅ : Set U64)) hA s1 a0
    (hq1.nodes _ hq1.cur) hq1.cur
  have U5 := sched.update_timestamp.kwN (Kp := T) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) hA s1 a0 hq1.nodes hq1.cur
  have U6 := sched.update_timestamp.dom hA s1 a0 hq1 D1
  rw [eu] at U2 U3 U3t U4 U5 U6
  simp only [WP.spec_ok, WP.uncurry'_pair] at U2 U3 U3t U4 U5 U6
  obtain ⟨⟨⟨⟨Q2, R2, hq2⟩, hBd2, hX2, hSg2, hS2⟩, -, -⟩, n2, -⟩ := U2
  have ea2 : L.actionW s2 = L.actionW s1 := n2.1
  have D2 : DomInv st T s2 := U6
  have r2 : RC st s2 := RC.fnT hq1 U5 ea2 r1
  have est2 : L.mem s2 (stA t) = sched.TS_RUNNING := by
    rw [U3t.idKeep (by rw [stA_eq]; exact field_aligned (hT t htT) (by simp) (by simp))
      (Or.inr (Or.inl ⟨t, htT, hT t htT, Set.mem_singleton t, Or.inl rfl⟩)), est1, hrun]
  have hB2 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 := ⟨⟨Q2, R2, hq2⟩, hBd2, hX2, hS2, hSg2⟩
  -- `set_thread_state t RESTART`
  have R3 := sched.set_thread_state.restart_blk (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s2 t hB2 htT
    (by rw [est2]; exact fun hb => not_runnable_of_blocked hb (Or.inl rfl)) (by rw [est2]; exact tsRunning_ne_bor)
  have N3 := sched.set_thread_state.nb (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) (Eb := (∅ : Set U64)) s2 t sched.TS_RESTART hq2 htT hKt
  rw [es3] at R3 N3
  simp only [WP.spec_ok] at R3 N3
  obtain ⟨hB3, -, est3, -⟩ := R3
  obtain ⟨F3, B3, ea3⟩ := N3
  have W3 := sched.set_thread_state.w2 s2 t sched.TS_RESTART hq2.tcbs (hq2.nodes _ hq2.cur) htT
  rw [es3] at W3
  simp only [WP.spec_ok] at W3
  have D3 : DomInv st T s3 := DomInv.sts hq2 htT W3.1 D2
  have r3 : RC st s3 := RC.sts hq2 htT W3.1 W3.2.1 W3.2.2
    (fun _ hb => not_runnable_of_blocked hb (Or.inr (Or.inl rfl))) r2
  -- `timer.insert target`
  have I4 := timer.insert.nb (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) (Eb := (∅ : Set U64)) s3 tg d bd hB3 htg
  rw [es4] at I4
  simp only [WP.spec_ok] at I4
  obtain ⟨hB4, F4, B4, ea4, est4⟩ := I4
  have I4T := timer.insert.nb (Kp := T) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) (Eb := (∅ : Set U64)) s3 tg d bd hB3 htg
  have I4F := timer.insert.foot s3 tg d bd hB3.tinv htg
  rw [es4] at I4T I4F
  simp only [WP.spec_ok] at I4T I4F
  have hq3 := hB3.1.choose_spec.choose_spec
  have hN3 := hq3.nodes _ hq3.cur
  have D4 : DomInv st T s4 := DomInv.freeA D3 I4F.2.2.1 hq3.tcbs (cdomA_alignedN hN3) fun b _ hb => by
    have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
    rcases hb with (⟨y, hy, K, h1, h2, rfl⟩ | ⟨c, hc, o, ho, rfl⟩) | rfl
    · exact field_domFree hq3.tcbs hN3 hy (hq3.ksOut y hy) (by omega) (by omega)
    · exact node_domFree hq3.tcbs (hq3.nodes c hc) (by rcases ho with h | h <;> omega)
    · exact node_domFree hq3.tcbs hN3 (by rw [rp]; omega)
  have r4 : RC st s4 := RC.fnT hq3 I4T.2.1 I4T.2.2.2.1 r3
  -- `reply_success_empty t`
  have P5 := msg.reply_success_empty.nb (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) (Eb := (∅ : Set U64)) s4 t hB4 htT
  rw [es5] at P5
  simp only [WP.spec_ok] at P5
  have P5T := msg.reply_success_empty.nb (Kp := T) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) (Eb := (∅ : Set U64)) s4 t hB4 htT
  have P5D := msg.reply_success_empty.dom s4 t hB4 htT D4
  rw [es5] at P5T P5D
  simp only [WP.spec_ok] at P5T P5D
  have D5 : DomInv st T s5 := P5D
  have r5 : RC st s5 := RC.fnT hB4.1.choose_spec.choose_spec P5T.2.1 P5T.2.2.2.1 r4
  obtain ⟨hB5, F5, B5, ea5, est5⟩ := P5
  -- `set_thread_state t RUNNING`
  obtain ⟨⟨Q5, R5, hq5⟩, hBd5, hX5, hS5, hSg5⟩ := hB5
  have R6 := sched.set_thread_state.running_bxi ⟨⟨Q5, R5, hq5⟩, hBd5, hX5, hSg5, hS5⟩ htT
    (by rw [est5, est4 t htT, est3])
  have N6 := sched.set_thread_state.nb (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) (Eb := (∅ : Set U64)) s5 t sched.TS_RUNNING hq5 htT hKt
  rw [es6] at R6 N6
  simp only [WP.spec_ok] at R6 N6
  obtain ⟨⟨Q6, R6', hq6⟩, hBd6, hX6, hSg6, hS6⟩ := R6
  obtain ⟨F6, B6, ea6⟩ := N6
  have W6 := sched.set_thread_state.w2 s5 t sched.TS_RUNNING hq5.tcbs (hq5.nodes _ hq5.cur) htT
  rw [es6] at W6
  simp only [WP.spec_ok] at W6
  have D6 : DomInv st T s6 := DomInv.sts hq5 htT W6.1 D5
  have r6 : RC st s6 := RC.sts hq5 htT W6.1 W6.2.1 W6.2.2
    (fun _ hb => not_runnable_of_blocked hb (Or.inl rfl)) r5
  -- the body's end
  have F06 : FootN st (KI st T Cs (L.cpu s0) s0) True T Cs Sg Scs Z (EH H) s0 s6 :=
    F1.trans (U3.trans (F3.trans (F4.trans (F5.trans F6))))
  have B06 : FootB st T Cs Sg Scs Z ∅ s0 s6 := B1.trans (U4.trans (B3.trans (B4.trans (B5.trans B6))))
  have hBlk6 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s6 := ⟨⟨Q6, R6', hq6⟩, hBd6, hX6, hS6, hSg6⟩
  have hBA6 : BufAt st T Cs H Sg Scs Z U s6 :=
    BufAt.of_fr hBA0 (IbFr.of_bufKeep B06.1
      (BufKeep.of_footB hq0 hX0.1 hSg0.sub (fun e' he' => absurd he' (Set.notMem_empty e')) B06))
  have hcn : sched.ACTION_CHOOSE_NEW ∉ T := notT_small hT (by simp)
  have ea05 : L.actionW s5 = L.actionW s0 ∨ L.actionW s5 = sched.ACTION_CHOOSE_NEW := by
    rw [ea5, ea4]
    rcases ea3 with e3 | e3
    · exact Or.inl (by rw [e3, ea2, ea1])
    · exact Or.inr e3
  have hsa6 : ActAff st T s6 := by
    refine ActAff.nT ?_
    rcases ea6 with e6 | e6
    · rw [e6]
      rcases ea05 with e5 | e5
      · rw [e5]; exact h0.actNT _ hcpu
      · rw [e5]; exact hcn
    · rw [e6]; exact hcn
  have W := AllCores.schedBH hA IK hNt a1 h0 hcpu hS0 hB0 F06 hBlk6 hBA6 hsa6 D6 r6
  rw [esc] at W
  simp only [WP.spec_ok, WP.uncurry'_pair] at W
  exact ⟨hBlk6, hBA6, B06, W⟩


set_option maxHeartbeats 4000000 in
/-- **The `TCB_SetTimer` local entry ends `schedule` in `AllCores`**
(`set_timer_local.allCoresB` with `hR`, `hS0` discharged; entry fact `hD0`).
No named premise. -/
theorem set_timer_local.allCoresBW (hA : P0.ArchTotal ar) (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {n : I64} {target : U64}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0) (htg : target ∈ T)
    (hD0 : DomInv st T s0)
    (e : localtimer.handle_set_timer_local st ar s0 a0 n target = ok (true, s', a')) :
    ∃ s3 a3 s4 a4, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ BufAt st T Cs H Sg Scs Z U s3 ∧
      FootB st T Cs Sg Scs Z ∅ s0 s3 ∧ sched.schedule st ar s3 a3 = ok (s4, a4) ∧ AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧
      (do
        let (s5, a5) ← sched.activate_thread st ar s4 a4
        let t ← sched.cur_thread st s5
        vcpu.check st ar s5 a5 t) = ok (s', a') := by
  have h := e
  unfold localtimer.handle_set_timer_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, ect, h⟩ := bind_eq_ok h
  obtain ⟨cpu, -, h⟩ := bind_eq_ok h
  obtain ⟨info, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases cn : (n != fl4_abi.syscall.SysCall) = true
  · rw [if_pos cn] at h; simp at h
  rw [if_neg cn] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  by_cases c2 : (info.label != fl4_abi.label.TCBSetTimer) = true
  · rw [if_pos c2] at h; simp at h
  rw [if_neg c2] at h
  by_cases c3 : (info.extra_caps != 0#u64) = true
  · rw [if_pos c3] at h; simp at h
  rw [if_neg c3] at h
  by_cases c4 : info.length < 2#u64
  · rw [if_pos c4] at h; simp at h
  rw [if_neg c4] at h
  obtain ⟨csc, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  by_cases c5 : (i2 != sched.TS_RUNNING) = true
  · rw [if_pos c5] at h; simp at h
  rw [if_neg c5] at h
  have hi2 : i2 = sched.TS_RUNNING := by simp only [bne_iff_ne, ne_eq, not_not] at c5; exact c5
  have hrun : L.mem s0 (stA t) = sched.TS_RUNNING := by
    obtain ⟨w, ew, hw⟩ := spec_ex_fd (obj.Tcb.state.spec (st := st) s0 t)
    rw [ei2] at ew
    rw [← hw, ← ok_inj_ff ew, hi2]
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨nx, -, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, -, h⟩ := bind_eq_ok h
  obtain ⟨dl, -, h⟩ := bind_eq_ok h
  obtain ⟨bd, -, h⟩ := bind_eq_ok h
  obtain ⟨cns, -, h⟩ := bind_eq_ok h
  obtain ⟨b4, -, h⟩ := bind_eq_ok h
  cases b4
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b5, -, h⟩ := bind_eq_ok h
  cases b5
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨b6, -, h⟩ := bind_eq_ok h
  cases b6
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  -- both deadline arms run the same tail (as P1 `set_timer_local_same`)
  have tail : (do
      let s3 ← sched.set_thread_state st s2 t sched.TS_RESTART
      let s4 ← timer.insert st s3 target dl bd
      let s5 ← msg.reply_success_empty st s4 t
      let s6 ← sched.set_thread_state st s5 t sched.TS_RUNNING
      let (s7, a2) ← sched.schedule st ar s6 a1
      let (s8, a3) ← sched.activate_thread st ar s7 a2
      let t1 ← sched.cur_thread st s8
      let (s9, a4) ← vcpu.check st ar s8 a3 t1
      ok (true, s9, a4)) = ok (true, s', a') := by
    by_cases cd : (dl != 0#u64) = true
    · rw [if_pos cd] at h
      by_cases cd2 : dl <= now
      · rw [if_pos cd2] at h; simp at h
      · rw [if_neg cd2] at h; exact h
    · rw [if_neg cd] at h; exact h
  clear h
  obtain ⟨s3, es3, h⟩ := bind_eq_ok tail
  obtain ⟨s4, es4, h⟩ := bind_eq_ok h
  obtain ⟨s5, es5, h⟩ := bind_eq_ok h
  obtain ⟨s6, es6, h⟩ := bind_eq_ok h
  obtain ⟨⟨s7, a2⟩, esc, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s8, a3⟩, eac, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨t1, et, h⟩ := bind_eq_ok h
  obtain ⟨⟨s9, a4⟩, evc, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  have e6 := ok_inj_ff h
  simp only [Prod.mk.injEq, true_and] at e6
  obtain ⟨rfl, rfl⟩ := e6
  obtain ⟨hB6, hBA6, B06, W⟩ := set_timer_tailBW hA IK hNt h0 hcpu hI0 hBA0 htg hD0 ect hrun es1 eu es3 es4 es5 es6 esc
  refine ⟨s6, a1, s7, a2, hB6, hBA6, B06, esc, W, ?_⟩
  rw [eac]; simp only [bind_ok, uncurry_apply_pair]
  rw [et]; simp only [bind_ok]
  exact evc


/-- **The `TCB_SetTimer` local entry ends `schedule` in `AllCores`**
(`set_timer_local.allCores` with `hR`, `hS0` discharged). No named premise. -/
theorem set_timer_local.allCoresW (hA : P0.ArchTotal ar) (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {n : I64} {target : U64}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0) (htg : target ∈ T)
    (hD0 : DomInv st T s0)
    (e : localtimer.handle_set_timer_local st ar s0 a0 n target = ok (true, s', a')) :
    ∃ s4 a4, AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧
      (do
        let (s5, a5) ← sched.activate_thread st ar s4 a4
        let t ← sched.cur_thread st s5
        vcpu.check st ar s5 a5 t) = ok (s', a') := by
  obtain ⟨-, -, s4, a4, -, -, -, -, W, E⟩ := set_timer_local.allCoresBW hA IK hNt h0 hcpu hI0 hBA0 htg hD0 e
  exact ⟨s4, a4, W, E⟩

/-- **The `TCB_SetTimer` local entry ends in `AllCores`** at the entry's exit
(`set_timer_local.allCoresExit` with `hR`, `hS0` discharged). Named premise:
`hVW` [P] (`VcpuUsr`), as `AllCores.exit` (sib: `SchIb` discharged). -/
theorem set_timer_local.allCoresExitW (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {n : I64} {target : U64}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0) (htg : target ∈ T)
    (hD0 : DomInv st T s0)
    (hVW : ∀ s : S, AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s → VcpuUsr st T Cs H Sg Scs Z s)
    (e : localtimer.handle_set_timer_local st ar s0 a0 n target = ok (true, s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨s3, a3, s4, a4, hB3, hBA3, -, esc, W, E⟩ :=
    set_timer_local.allCoresBW hA IK hNt h0 hcpu hI0 hBA0 htg hD0 e
  have hS0 : (0#u64) ∉ Scs := by
    obtain ⟨-, -, hX0, -⟩ := hI0
    exact ObjsOK.zero_notScs hX0.1
  exact AllCores.exit hA IK hNt hS0 hVW hB3 hBA3 esc W E

end

end Fl4Proofs.P2.Stall
