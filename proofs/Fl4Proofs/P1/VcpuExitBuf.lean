/-
# P1 (vexit gen 2): `handle_vcpu_exit` keeps `EntryInv`, the buffer placement carried

`syscall.handle_vcpu_exit.entry` (P1/VcpuExitInv) took the IPC-buffer placement
`BufAt` and the guard `G` of `check_budget` as premises at the run's
intermediate states, and the timeout faults as `TmoKG … G` (over every state
where `G` and the invariants hold). Here the run carries the buffer-lookup
frame `IbFr` from the entry state instead:

* `update_timestamp` writes two words of the current node (`FootB` over empty
  object sets, `footB0_fld`): every TCB word is kept, so the buffer lookups,
  the current thread's state and its VCPU word are the entry's;
* `vcpu.check`: `VckW.ibFr`;
* `check_budget`: `sched.check_budget.allGB` (this module), `QueueBudgetG`'s
  walk with the frame step `FootB` (no `IPC_BUFFER` word) and the timeout
  premise pinned to the check's start `s0` (`TmoGB s0 G`: at states reached
  from `s0` by `ChgW` writes, with `CurOK`), instantiated with `G := IbFr`
  from the check's start (`TmoIb`);
* `handle_interrupt`: `interrupt.handle_interrupt.ibx` (signal: `ibKeep_holds`;
  timer: node words; IPI: `reschedule_required.kwB`);
* `finish_old`: `sched.schedule.ibFr` (sib) and `activate_thread.tw` / `TW.ibFr`.

`IbKeep` is a theorem (`ibKeep_holds`), so it is no premise here.

**`syscall.handle_vcpu_exit.entryB`**: from `EntryInv` and `BufAt U` at the
entry state, the exit state satisfies `EntryInv`. Named premises:

* `hBA` [P] `BufAt U s` at the entry (the IPC-buffer placement; P3 facts);
* `hPd` [P] `PendAt U s` at the entry: a `TS_RUNNING_VM` current thread's bound
  VCPU `PENDING` word is in `U` (`vmpl`'s second half);
* `htk` [P] (only when not stalled) `TmoIb` at the state `check_budget` starts
  from: a timeout fault raised there (after `ChgW` writes, current thread
  schedulable) keeps `BXI` and every TCB's buffer-lookup words. Narrower than
  `TmoKG` (whose `Foot`-closed guard cannot give `CanBlock` of the current
  thread: `Foot` may make the idle thread current, P1/EntryVacuous);
* `hI` [P] (when an IRQ came) `IrqNtAt` after `vexit_pre`: the IRQ slots name
  heap notifications (`vcpu.check`'s `VckR` and the fault IPC's `CapW ∧ KG`
  words may reach the kernel-global block, so no frame keeps them here);
* `hPF` [P] `PendAt U` at the state `finish_old` leaves (the thread `schedule`
  picks; no P1 frame keeps the TCBs' VCPU words across the run, vk did that
  only in P2's `PrW`).

Discharged against `handle_vcpu_exit.entry`: `hGF`, `htmo` (replaced by the
pinned `htk`), `hUt` (all of it: `VmPl` after `update_timestamp` from
`hBA`/`hPd`, no guard), `hI`'s `BufAt`, `hF`'s `BufAt` and `finish_old`'s
`BufAt` half of `VmPl`, and `IK`.
-/
import Fl4Proofs.P1.VcpuExitInv
import Fl4Proofs.P1.SchedFootB
import Fl4Proofs.P2.EntryTail
import Fl4Proofs.P2.EntryIrq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {A : Type _} {ar : machine.Arch A} {Ac : Set U64}
variable {U : Set U64}

/-- The timeout faults a budget check from `s0` raises keep the invariants
and `G`: at a state reached from `s0` by `ChgW` writes, with the current thread
schedulable (`CurOK`) and `G` (P2's `TmoKC` shape, without `KWN`). (tmofr: over `Timeout` faults only, the fault `end_timeslice` raises; a non-timeout fault
would take the cap-transferring normal transfer.) -/
def TmoGB (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (s0 : S) (G : S → Prop) : Prop :=
  ∀ (s : S) (a : A) (f : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64),
    SchedQueuesInv st T Cs Ω H s Q R → BoundInv st T Ac s → XInv st T Cs Ω Sg Rp Scs Nt Z s → SgOK st Ω Sg s →
    SCsOK st T Ω Sg Scs Z Ac s → WritesIn st s0 s (ChgW st Scs Z s0) → CurOK st T s → G s →
    faults.handle_timeout st ar s a (L.curW s) (error.Fault.Timeout f) ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ G s' ⦄

/-- **[P] The timeout fault of a budget check from `s0` keeps the buffer-lookup
words** (and the invariants), at the states `TmoGB` names. (tmofr: over `Timeout` faults only, the fault `end_timeslice` raises; a non-timeout fault
would take the cap-transferring normal transfer.) -/
def TmoIb (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (s0 : S) : Prop :=
  ∀ (s : S) (a : A) (f : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64),
    SchedQueuesInv st T Cs Ω H s Q R → BoundInv st T Ac s → XInv st T Cs Ω Sg Rp Scs Nt Z s → SgOK st Ω Sg s →
    SCsOK st T Ω Sg Scs Z Ac s → WritesIn st s0 s (ChgW st Scs Z s0) → CurOK st T s →
    faults.handle_timeout st ar s a (L.curW s) (error.Fault.Timeout f) ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      IbFr (L := L) T s s' ⦄

theorem TmoIb.gb {s0 : S} (hT : TmoIb st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0) (sA : S) :
    TmoGB st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0 (fun s' => IbFr (L := L) T sA s') :=
  fun s a f Q R h hB hX hSg hS w hc hG => WP.spec_mono (hT s a f Q R h hB hX hSg hS w hc) fun r hr => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact ⟨hr.1, hG.trans hr.2⟩

/-- A `FootB` step from a `BXI` state keeps the buffer-lookup words. -/
theorem ibFr_footB {s0 s1 s2 : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (g : IbFr (L := L) T s0 s1)
    (f : FootB st T Cs Sg Scs Z (EH H) s1 s2) : IbFr (L := L) T s0 s2 := by
  obtain ⟨⟨Q, R, h0⟩, -, hX, hSg, -⟩ := h
  exact g.trans (IbFr.of_bufKeep f.1 (BufKeep.of_footB h0 hX.1 hSg.sub (fun _ he => he) f))

/-- A `FootB` footprint over empty object sets (node words only) keeps every
TCB word. -/
theorem footB0_fld {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInv st T Cs Ω H s Q R) {y K : U64} (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (f : FootB st ∅ Cs ∅ ∅ Z ∅ s s') :
    L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
  refine f.mem_eq (field_aligned (hq.tcbs y hy) hK hK8) ?_
  rintro (⟨y', hy', -⟩ | ⟨c, hc, o, ho, -, e⟩ | hm | ⟨c, hc, -⟩ | ⟨e', he', -⟩)
  · exact absurd hy' (Set.notMem_empty _)
  · exact node_ne_field (hq.nodes c hc) ho hy (hq.tcbs y hy) hK e.symm
  · exact absurd hm (Set.notMem_empty _)
  · exact absurd hc (Set.notMem_empty _)
  · exact absurd he' (Set.notMem_empty _)

/-- A node-words-only step keeps every buffer lookup. -/
theorem ibFr_footB0 {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInv st T Cs Ω H s Q R) (f : FootB st ∅ Cs ∅ ∅ Z ∅ s s') : IbFr (L := L) T s s' :=
  ⟨f.1, fun t ht => ⟨footB0_fld hq ht (K := 3512#u64) (by simp) (by simp) f,
    by rw [sbWordA_eq]; exact footB0_fld hq ht (by simp) (by simp) f,
    by rw [sbWordA8_eq]; exact footB0_fld hq ht (by simp) (by simp) f⟩⟩

theorem nodePlaced0 {s : S} {c : U64} (h : NodePlaced st T s c) : NodePlaced st ∅ s c :=
  ⟨h.align, h.fits, fun t ht => absurd ht (Set.notMem_empty t)⟩

/-! ## The budget check with a `FootB` frame (QueueBudgetG's walk) -/

/-- `end_suff` keeps `G`, a property `KW` steps keep. -/
theorem end_suffGB (hA : P0.ArchTotal ar) (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hc : CurOK st T s)
    {G : S → Prop} (hGF : ∀ s1 s2 : S, BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 → G s1 → FootB st T Cs Sg Scs Z (EH H) s1 s2 → G s2) (hG : G s) :
    (do
      let b ← sporadic.ready st s (L.cscW s)
      if b = true then do
        let b1 ← sporadic.sufficient st ar s a (L.cscW s) 0#u64
        if b1 = true then do let s1 ← sched.append st s (L.curW s); ok (s1, a)
        else do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a)
      else do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a))
      ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ G s' ⦄ :=
  WP.spec_mono (WP.spec_and (end_suff hA s a Q R h hB hX hSg hS hc) (Fl4Proofs.P2.Stall.end_suff.footB (Es := EH H) hA s a Q R h hX hSg hc))
    fun r hr => by
      obtain ⟨s', a'⟩ := r
      simp only [WP.uncurry'_pair] at hr ⊢
      exact ⟨hr.1, hGF _ _ ⟨⟨Q, R, h⟩, hB, hX, hSg, hS⟩ hG hr.2⟩

/-- seL4 `endTimeslice`. -/
theorem sched.end_timeslice.allGB (hA : P0.ArchTotal ar) (s : S) (a : A) (cto : Bool)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hc : CurOK st T s)
    {G : S → Prop} (hGF : ∀ s1 s2 : S, BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 → G s1 → FootB st T Cs Sg Scs Z (EH H) s1 s2 → G s2) (hG : G s)
    (s0 : S) (w0 : WritesIn st s0 s (ChgW st Scs Z s0)) (htmo : TmoGB st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0 G) :
    sched.end_timeslice st ar s a cto ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ G s' ⦄ := by
  have E := end_suffGB hA s a Q R h hB hX hSg hS hc hGF hG
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
        exact htmo s a _ Q R h hB hX hSg hS w0 hc hG
      · exact E
  · exact E

/-- seL4 `chargeBudget` keeps the invariants, when the current SC is the
current thread's (if it is schedulable), the current thread is not the
switch-to candidate, and timeout faults keep them. -/
theorem sched.charge_budget.allGB (hA : P0.ArchTotal ar) (s : S) (a : A) (used : U64) (cto : Bool)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hna : L.actionW s ≠ L.curW s) (hcA : L.cscW s ∈ Ac)
    {G : S → Prop} (hGF : ∀ s1 s2 : S, BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 → G s1 → FootB st T Cs Sg Scs Z (EH H) s1 s2 → G s2) (hG : G s)
    (htmo : TmoGB st ar T Cs Ω H Sg Rp Scs Nt Z Ac s G) :
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
  -- the ring and the SC's `CONSUMED` word
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
  -- the node's `CONSUMED`
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
  have W3 : WritesIn st s s3 (ChgW st Scs Z s) := by
    obtain ⟨hP, hz⟩ := hX.1.sc _ hcS
    obtain ⟨-, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hN2 := h2.nodes _ h2.cur
    have wn : WritesIn st s2 s3 (fun b => b = L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) := by
      rw [s3_post]; exact writesIn_wr (nodeAt_aligned hN2 (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
    refine (w2.trans wn).mono fun b hb => ?_
    rcases hb with (hh | rfl) | rfl
    · exact Or.inl ⟨_, hcS, hh.inSC⟩
    · exact Or.inl ⟨_, hcS, by rw [hv]; simp, by rw [hv]; simp [layout.sc.CONSUMED]; omega⟩
    · exact Or.inr (by rw [nodeAt_of_ksb w2.1, w2.2.1])
  have G3 : G s3 := hGF _ _ ⟨⟨Q, R, h⟩, hB, hX, hSg, hS⟩ hG (FootB.of W3 fun b hb => by
    rcases hb with ⟨c, hc', hin⟩ | e
    · exact kwB_sc hc' hin
    · rw [e]; exact kwB_node h.cur (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
  have K3 : CurK st s s3 := CurK.of h.tcbs hcT0 (ec3.trans ec2) ((f3 _ hcT0).1.trans (f2 _ hcT0).1)
    (Or.inl (ea3.trans ea2))
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
    refine WP.spec_bind (sched.end_timeslice.allGB hA s3 a cto Q R h3 hB3 hX3 hSg3 hS3 hc hGF G3 s W3 htmo) ?_
    rintro ⟨s4, a1⟩ ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hSg4, hS4⟩, g4⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (WP.spec_and (sched.reschedule_required.sch s4 Q4 R4 h4 hB4 hSg4)
      (sched.reschedule_required.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s4 h4)) ?_
    rintro s5 ⟨⟨⟨⟨Q5, R5, h5⟩, hB5, f5⟩, ea5, ec5, -⟩, k5⟩
    refine WP.spec_bind (WP.spec_and (sched.set_reprogram.sch s5 Q5 R5 h5 hB5 (hSg4.fr f5))
      (sched.set_reprogram.spec s5)) ?_
    rintro s6 ⟨⟨⟨h6, hB6, f6⟩, ea6, ec6⟩, e6⟩
    simp only [WP.spec_ok, WP.uncurry'_pair]
    have g6 : G s6 := by
      rw [e6]
      exact hGF _ _ ⟨⟨Q5, R5, h5⟩, hB5, hX4.fr f5, hSg4.fr f5, hS4.fr f5⟩
        (hGF _ _ ⟨⟨Q4, R4, h4⟩, hB4, hX4, hSg4, hS4⟩ g4 k5) (footB_node (h5.nodes _ h5.cur) h5.cur (o := layout.node.REPROGRAM)
        (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
    exact ⟨⟨⟨Q5, R5, h6⟩, hB6, (hX4.fr f5).fr f6, (hSg4.fr f5).fr f6, (hS4.fr f5).fr f6⟩, g6⟩
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    exact ⟨⟨⟨Q, R, h3⟩, hB3, hX3, hSg3, hS3⟩, G3⟩

/-- seL4 `checkBudget`. -/
theorem sched.check_budget.allGB (hA : P0.ArchTotal ar) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hna : L.actionW s ≠ L.curW s) (hcA : L.cscW s ∈ Ac)
    {G : S → Prop} (hGF : ∀ s1 s2 : S, BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 → G s1 → FootB st T Cs Sg Scs Z (EH H) s1 s2 → G s2) (hG : G s)
    (htmo : TmoGB st ar T Cs Ω H Sg Rp Scs Nt Z Ac s G) :
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
  · refine WP.spec_bind (sched.charge_budget.allGB hA s a c true Q R h hB hX hSg hS hcsc hna hcA hGF hG htmo) ?_
    rintro ⟨s1, a1⟩ h1
    try simp only [WP.uncurry'_pair] at h1
    obtain ⟨hb1, g1⟩ := h1
    refine (WP.spec_ok _).2 ?_
    try simp only [WP.uncurry'_pair]
    first
      | exact ⟨⟨hb1, g1⟩, fun e => absurd e (by simp)⟩
      | exact ⟨hb1, g1, fun e => absurd e (by simp)⟩
      | exact ⟨hb1, g1⟩

/-- **`check_budget` from an `EntryInv` state keeps the buffer-lookup words**,
when its timeout fault does (`TmoIb` at its start). -/
theorem sched.check_budget.ibx (hA : P0.ArchTotal ar) (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (htmo : TmoIb st ar T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.check_budget st ar s a ⦃ r s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IbFr (L := L) T s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, -, hcA, hna, hcsc⟩ := h
  refine WP.spec_mono (sched.check_budget.allGB hA s a Q R h0 hB hX hS.sg hS hcsc hna hcA
    (G := fun s' => IbFr (L := L) T s s') (fun _ _ b g f => ibFr_footB b g f) (IbFr.refl s) (htmo.gb s)) ?_
  rintro ⟨r, s', a'⟩ ⟨⟨h1, g1⟩, -⟩
  exact ⟨h1, g1⟩

/-- A node-word write of the current node keeps the buffer lookups. -/
theorem ibFr_node {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInv st T Cs Ω H s Q R) {o v : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0)
    (h88 : o.val ≠ 88) : IbFr (L := L) T s (L.wr s (L.nodeAt s (L.cpu s) o) v) :=
  ibFr_footB0 hq (footB_node (T := ∅) (Sg := ∅) (Scs := ∅) (Z := fun _ => 0) (Es := ∅)
    (nodePlaced0 (hq.nodes _ hq.cur)) hq.cur ho h8 h88)

/-- **`handle_interrupt` keeps the buffer-lookup words** (as
`interrupt.handle_interrupt.bxi`). -/
theorem interrupt.handle_interrupt.ibx (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (irq : U64)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hirq : IrqNtAt st Nt s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    interrupt.handle_interrupt st ar s a irq ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      IbFr (L := L) T s s' ⦄ := by
  have hST : P0.StoreTotal st := L.total
  have hq := h.1.choose_spec.choose_spec
  unfold interrupt.handle_interrupt
  step with layout.irq.MAX.spec as ⟨mx, emx⟩
  split
  · refine WP.spec_bind (hA.mask_irq a irq true) fun a1 _ => ?_
    refine WP.spec_bind (hA.ack_irq a1 irq) fun a2 _ => ?_
    exact (WP.spec_ok _).2 ⟨h, IbFr.refl s⟩
  step with P0.interrupt.irq_state.p0 st s irq hST as ⟨v⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ IbFr (L := L) T s r.1) ?_ ?_
  · split
    · rename_i hle _
      step with interrupt.irq_slot.val as ⟨sl, esl⟩
      subst esl
      have hirq' : irq.val < 128 := by
        have : mx.val = 127 := by rw [emx]; simp [layout.irq.MAX]
        simp at hle; omega
      refine WP.spec_bind (hirq irq hirq') fun c hc => ?_
      refine WP.spec_bind (Pₘ := fun r : S × A => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
        IbFr (L := L) T s r.1) ?_ ?_
      · split
        all_goals try exact (WP.spec_ok _).2 ⟨h, IbFr.refl s⟩
        rename_i ptr badge b x
        split
        · have hn := hc ptr badge b x rfl
          exact WP.spec_mono (WP.spec_and
            (notification.send_signal.tinv hA s a ptr badge h.blk hn (hNt ptr hn) hBA.1 hBA.2)
            ((ibKeep_holds hA T Cs Ω H Sg Rp Scs Nt Z Ac U).2.1 s a ptr badge h.blk hn (hNt ptr hn) hBA))
            fun r hr => by
              obtain ⟨s', a'⟩ := r
              simp only [WP.uncurry'_pair] at hr ⊢
              exact ⟨BlkOK.bxi hr.1, hr.2⟩
        · exact (WP.spec_ok _).2 ⟨h, IbFr.refl s⟩
      · rintro ⟨s3, a2⟩ h3
        try simp only [WP.uncurry'_pair]
        refine WP.spec_bind (hA.mask_irq a2 irq true) fun a3 _ => ?_
        exact (WP.spec_ok _).2 h3
    split
    · step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_set.spec as ⟨s2, e2⟩
      subst ec e2
      obtain ⟨⟨k2, -, -⟩, -, -⟩ := nodew_bxc (o := layout.node.REPROGRAM) (v := 1#u64) h
        (by simp [layout.node.REPROGRAM, LowFree]) (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      have i2 := ibFr_node (T := T) hq (o := layout.node.REPROGRAM) (v := 1#u64)
        (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      have i3 := ibFr_node (T := T) k2.1.choose_spec.choose_spec (o := layout.node.ARMED) (v := 0#u64)
        (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED])
      step with obj.node_set.spec as ⟨s3, e3⟩
      subst e3
      have k3 := nodew_bxc (o := layout.node.ARMED) (v := 0#u64) k2
        (by simp [layout.node.ARMED, LowFree]) (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED])
      have k3' := k3.1.1
      have i23 := i2.trans i3
      simp only [LawfulStore.cpu_wr, nodeAt_wr] at k3' i23 ⊢
      exact ⟨k3', i23⟩
    split
    · unfold smp.handle_ipi
      step with layout.irq.RESCHEDULE_IPI.spec as ⟨ri, eri⟩
      split
      · obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
        refine WP.spec_bind (WP.spec_and (sched.reschedule_required.sch s Q R h0 hB hSg)
          (sched.reschedule_required.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s h0)) fun s1 hh => ?_
        obtain ⟨⟨⟨hi, hB1, f1⟩, -, -, -⟩, k1⟩ := hh
        exact (WP.spec_ok _).2 ⟨⟨hi, hB1, hX.fr f1, hSg.fr f1, hS.fr f1⟩,
          ibFr_footB ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ (IbFr.refl s) k1⟩
      · exact (WP.spec_ok _).2 ⟨h, IbFr.refl s⟩
    · refine WP.spec_bind (Pₘ := fun _ : A => True) ?_ fun t _ => (WP.spec_ok _).2 ⟨h, IbFr.refl s⟩
      split
      · exact WP.spec_mono (hA.mask_irq a irq true) fun _ _ => trivial
      · exact (WP.spec_ok _).2 trivial
  · rintro ⟨s1, a1⟩ h1
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (hA.ack_irq a1 irq) fun a2 _ => ?_
    exact (WP.spec_ok _).2 h1

/-- The `PENDING` half of `VmPl` at one state: a `TS_RUNNING_VM` current
thread's bound VCPU `PENDING` word is a user word. -/
def PendAt (st : machine.Store S) [L : LawfulStore st] (U : Set U64) (s : S) : Prop :=
  L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM →
    L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64)) vcpu.PENDING ∈ U

/-- `vcpu.check` of the current thread keeps `EntryInv` and the buffer lookups. -/
theorem vexit_checkI (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hV : VmPl st T Cs H Sg Scs Z U s) :
    vcpu.check st ar s a (L.curW s) ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      IbFr (L := L) T s s' ⦄ := by
  have hq := h.1.choose_spec.choose_spec
  have hcT : L.curW s ∈ T := hq.curT
  by_cases hv : L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM
  · obtain ⟨hBA, hpw⟩ := hV hv
    refine WP.spec_mono (vcpu.check.vck hA hNt s a h hBA.1 (hBA.2 _ hcT) hpw) ?_
    rintro ⟨s', a'⟩ hh
    simp only [WP.uncurry'_pair] at hh ⊢
    exact ⟨hh.1, VckW.ibFr hq hcT hh.2.1⟩
  · rw [check_of_ne ar s a _ hv, WP.spec_ok]
    exact ⟨h, IbFr.refl s⟩

/-- **The prefix of `handle_vcpu_exit` keeps the invariants and the buffer
lookups** (from `BufAt`/`PendAt` at the entry and the pinned `TmoIb`). -/
theorem vexit_pre.ib (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (stalled : Bool) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hPd : PendAt st U s)
    (htk : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIb st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄) :
    vexit_pre st ar s a stalled ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IbFr (L := L) T s s' ⦄ := by
  unfold vexit_pre
  cases stalled with
  | true => exact (WP.spec_ok _).2 ⟨EntryInv.bxi h, IbFr.refl s⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hq := h.1.choose_spec.choose_spec
    refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.update_timestamp.bxc hA s a (EntryInv.bxi h))
      (Fl4Proofs.P2.Stall.sched.update_timestamp.kwB (T := ∅) (Sg := ∅) (Scs := ∅) (Es := ∅)
        (Z := fun _ => 0) hA s a (nodePlaced0 (hq.nodes _ hq.cur)) hq.cur)) (htk rfl)) ?_
    rintro ⟨s1, a1⟩ ⟨⟨⟨⟨hb1, c1, k1⟩, n1, f1⟩, F1⟩, T1⟩
    have E1 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := EntryInv.of_step h hb1.blk c1 n1.2.2 (Or.inl n1.1) f1
    have I1 : IbFr (L := L) T s s1 := ibFr_footB0 hq F1
    have hcur : L.curW s1 = L.curW s := k1.1
    have hcT : L.curW s ∈ T := hq.curT
    have V1 : VmPl st T Cs H Sg Scs Z U s1 := fun hv => by
      rw [hcur] at hv ⊢
      have est : L.mem s1 (stA (L.curW s)) = L.mem s (stA (L.curW s)) :=
        footB0_fld hq hcT (by simp [layout.tcb.STATE]) (by simp [layout.tcb.STATE]) F1
      have evc : L.mem s1 (core.num.U64.wrapping_add (L.curW s) 3664#u64) =
          L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) :=
        footB0_fld hq hcT (by simp) (by simp) F1
      refine ⟨hBA.of_fr I1, fun hw => ?_⟩
      rw [evc] at hw ⊢
      exact hPd (est ▸ hv) hw
    show (do
      let ct ← sched.cur_thread st s1
      let (s3, a3) ← vcpu.check st ar s1 a1 ct
      let (_, s4, a4) ← sched.check_budget st ar s3 a3
      ok (s4, a4)) ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IbFr (L := L) T s s' ⦄
    rw [cur_thread_ok]; simp only [bind_ok]
    refine WP.spec_bind (WP.spec_and (vexit_checkI hA hNt s1 a1 E1 V1) T1) ?_
    rintro ⟨s2, a2⟩ ⟨⟨E2, I2⟩, T2⟩
    refine WP.spec_bind (sched.check_budget.ibx hA s2 a2 E2 T2) ?_
    rintro ⟨r, s3, a3⟩ ⟨h3, I3⟩
    exact (WP.spec_ok _).2 ⟨h3, (I1.trans I2).trans I3⟩

/-- **`handle_vcpu_exit` up to `finish` keeps the invariants and the buffer
lookups.** -/
theorem vexit_irq.ib (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (irq : U64) (stalled : Bool) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hPd : PendAt st U s)
    (htk : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIb st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄)
    (hI : vexit_pre st ar s a stalled ⦃ s1 _ => (irq != syscall.NO_IRQ) = true → IrqNtAt st Nt s1 ⦄) :
    vexit_irq st ar s a irq stalled ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IbFr (L := L) T s s' ⦄ := by
  unfold vexit_irq
  refine WP.spec_bind (WP.spec_and (vexit_pre.ib hA hNt s a stalled h hBA hPd htk) hI) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, I1⟩, i1⟩
  try simp only [WP.uncurry'_pair] at h1 I1 i1 ⊢
  split
  · rename_i hirq
    exact WP.spec_mono (interrupt.handle_interrupt.ibx hA hNt s1 a1 irq h1 (i1 hirq) (hBA.of_fr I1))
      fun r hr => by
        obtain ⟨s', a'⟩ := r
        simp only [WP.uncurry'_pair] at hr ⊢
        exact ⟨hr.1, I1.trans hr.2⟩
  · exact (WP.spec_ok _).2 ⟨h1, I1⟩

/-- `finish_old` (`schedule`, `activate_thread`) keeps the buffer lookups. -/
theorem syscall.finish_old.ibx (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    syscall.finish_old st ar s a ⦃ s' _ => IbFr (L := L) T s s' ⦄ := by
  unfold syscall.finish_old
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  refine WP.spec_bind (WP.spec_and
    (sched.schedule.entry hA (ibKeep_holds hA) hNt s a Q R h0 hB hS hX hSg hBA)
    (sched.schedule.ibFr hA (ibKeep_holds hA) hNt s a ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ hBA)) ?_
  rintro ⟨s1, a1⟩ ⟨E1, I1⟩
  have hq1 := E1.1.choose_spec.choose_spec
  exact WP.spec_mono (Fl4Proofs.P2.Stall.sched.activate_thread.tw hA s1 a1 (EntryInv.bxi E1).blk)
    fun r hr => by
      obtain ⟨s', a'⟩ := r
      exact I1.trans (Fl4Proofs.P2.Stall.TW.ibFr hq1 hq1.curT hr.1)

/-- **(P1, vexit gen 2) The serial VM exit `handle_vcpu_exit` keeps
`EntryInv`** with the buffer placement carried from the entry (module
docstring; premises `hBA`, `hPd`, `htk`, `hI`, `hPF` [P]; no `IbKeep`, no
`TmoKG`, no guard). -/
theorem syscall.handle_vcpu_exit.entryB (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (irq : U64) (stalled : Bool) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hPd : PendAt st U s)
    (htk : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIb st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄)
    (hI : vexit_pre st ar s a stalled ⦃ s1 _ => (irq != syscall.NO_IRQ) = true → IrqNtAt st Nt s1 ⦄)
    (hPF : vexit_irq st ar s a irq stalled ⦃ s2 a2 =>
      syscall.finish_old st ar s2 a2 ⦃ s3 _ => PendAt st U s3 ⦄ ⦄) :
    syscall.handle_vcpu_exit st ar s a irq stalled ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  rw [handle_vcpu_exit_split]
  refine WP.spec_bind (WP.spec_and (vexit_irq.ib hA hNt s a irq stalled h hBA hPd htk hI) hPF) ?_
  rintro ⟨s2, a2⟩ ⟨⟨h2, I2⟩, hP2⟩
  try simp only [WP.uncurry'_pair] at h2 I2 hP2 ⊢
  have B2 : BufAt st T Cs H Sg Scs Z U s2 := hBA.of_fr I2
  exact syscall.finish.entryV hA (ibKeep_holds hA) hNt s2 a2 h2 B2
    (WP.spec_mono (WP.spec_and (syscall.finish_old.ibx hA hNt s2 a2 h2 B2) hP2) fun r hr => by
      obtain ⟨s3, a3⟩ := r
      simp only [WP.uncurry'_pair] at hr ⊢
      exact fun hv => ⟨B2.of_fr hr.1, hr.2 hv⟩)

/-- **The x86 local VM exit (no IRQ) keeps `EntryInv`** (`entryB`; no `hI`). -/
theorem vcpu_exit_local.entryB (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (v n : U64) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hPd : PendAt st U s)
    (htk : sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIb st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄)
    (hPF : vexit_irq st ar s a syscall.NO_IRQ false ⦃ s2 a2 =>
      syscall.finish_old st ar s2 a2 ⦃ s3 _ => PendAt st U s3 ⦄ ⦄) :
    localvm.handle_vcpu_exit_local st ar s a v n ⦃ r => r.1 = true →
      EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  have hI : vexit_pre st ar s a false ⦃ s1 _ => (syscall.NO_IRQ != syscall.NO_IRQ) = true →
      IrqNtAt st Nt s1 ⦄ :=
    WP.spec_mono (vexit_pre.ib hA hNt s a false h hBA hPd fun _ => htk) fun r _ => by
      obtain ⟨s', a'⟩ := r; simp
  refine vcpu_exit_local_triple ar hA (h0.nodes _ h0.cur) (P := fun r => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_
  exact WP.spec_mono (syscall.handle_vcpu_exit.entryB hA hNt s a syscall.NO_IRQ false h hBA hPd
    (fun _ => htk) hI hPF) fun r hr => by obtain ⟨s', a'⟩ := r; simpa using hr

/-- **The x86 local VM timer exit keeps `EntryInv`** (`entryB`). -/
theorem vm_timer_local.entryB (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (irq n : U64) (p : localtimer.TimerIrqPlan) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hPd : PendAt st U s)
    (htk : sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIb st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄)
    (hI : vexit_pre st ar s a false ⦃ s1 _ => (irq != syscall.NO_IRQ) = true → IrqNtAt st Nt s1 ⦄)
    (hPF : vexit_irq st ar s a irq false ⦃ s2 a2 =>
      syscall.finish_old st ar s2 a2 ⦃ s3 _ => PendAt st U s3 ⦄ ⦄) :
    localvm.handle_vm_timer_irq_local st ar s a irq p n ⦃ r => r.1 = true →
      EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  refine vm_timer_local_triple ar hA (h0.nodes _ h0.cur) (P := fun r => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_
  exact WP.spec_mono (syscall.handle_vcpu_exit.entryB hA hNt s a irq false h hBA hPd
    (fun _ => htk) hI hPF) fun r hr => by obtain ⟨s', a'⟩ := r; simpa using hr

end

end Fl4Proofs.P1
