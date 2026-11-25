/-
# P2: the quiet case of an accepted timer interrupt (budget sufficient, no timer due): the tail's first two calls

* `check_budget_suf`: with a sufficient budget `check_budget` returns `(true, s, a)` (one domain: never expired);
* `handle_interrupt_timer`: for an IRQ in range with state `IRQ_TIMER` the handler sets the node's `REPROGRAM` to 1
  and `ARMED` to 0, then acks the IRQ (`Arch`); `handle_interrupt_timer_writes`: as a `WritesIn` (this core's node
  words 56 and 80 only);
* `nodue_hw`, `action_hw`, `rel_hw`: no timer due, the scheduler action and no release due survive those writes
  (as `nodue_keep` / `rel_keep` for SetTimer's writes), for `schedule_resume` at the `schedule` state;
* `action_ut` (`update_timestamp` keeps the action) and `irq_quiet_schedule`: in the quiet case `schedule` is
  `schedTail` (P1 `FastSched`), and `BXI` holds after `update_timestamp`.

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqW
import Fl4Proofs.P2.FootTimerIrqH
import Fl4Proofs.P2.FootTimerSet
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A)

/-- **`check_budget` with a sufficient budget** writes nothing and returns `true`. -/
theorem check_budget_suf {s : S} {a : A} {csc u : U64} (ecsc : sched.cur_sc st s = ok csc)
    (eu : sched.consumed st s = ok u) (hb : sporadic.sufficient st ar s a csc u = ok true) :
    sched.check_budget st ar s a = ok (true, s, a) := by
  unfold sched.check_budget
  rw [ecsc]; simp only [bind_ok]
  rw [eu]; simp only [bind_ok]
  rw [hb]
  simp only [bind_ok, ↓reduceIte, sched.is_cur_domain_expired, if_neg num_domains_one]
  simp only [Bool.false_eq_true, not_false_eq_true, decide_true]

/-- **The handler of a timer IRQ** sets `REPROGRAM` and clears `ARMED` on the current core's node, then acks. -/
theorem handle_interrupt_timer {s s3 : S} {a a3 : A} {irq mx : U64} (emx : layout.irq.MAX = ok mx)
    (hle : ¬ irq > mx) (hst : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER) [L : LawfulStore st]
    (h : interrupt.handle_interrupt st ar s a irq = ok (s3, a3)) :
    ∃ s2, obj.node_set st s (L.cpu s) layout.node.REPROGRAM 1#u64 = ok s2 ∧
      obj.node_set st s2 (L.cpu s) layout.node.ARMED 0#u64 = ok s3 ∧ ar.ack_irq a irq = ok a3 := by
  unfold interrupt.handle_interrupt at h
  rw [emx] at h; simp only [bind_ok] at h
  rw [if_neg hle, hst] at h; simp only [bind_ok] at h
  rw [if_neg irq_timer_ne_signal] at h
  simp only [eq_self_iff_true, if_true, ↓reduceIte] at h
  obtain ⟨⟨s1, a1⟩, e1, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨a2, e2, h⟩ := bind_eq_ok h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  rw [L.cur_cpu_eq] at e1; simp only [bind_ok] at e1
  obtain ⟨s2, e3, e1⟩ := bind_eq_ok e1
  obtain ⟨s4, e4, e1⟩ := bind_eq_ok e1
  have e' := ok_inj_ff e1
  simp only [Prod.mk.injEq] at e'
  obtain ⟨rfl, rfl⟩ := e'
  exact ⟨s2, e3, e4, e2⟩

/-- **The timer handler's writes**: only this core's node words `REPROGRAM` (56) and `ARMED` (80). -/
theorem handle_interrupt_timer_writes [L : LawfulStore st] {T : Set U64} {s s2 s3 : S}
    (hN : NodePlaced st T s (L.cpu s))
    (e2 : obj.node_set st s (L.cpu s) layout.node.REPROGRAM 1#u64 = ok s2)
    (e3 : obj.node_set st s2 (L.cpu s) layout.node.ARMED 0#u64 = ok s3) :
    WritesIn st s s3 (L.NodeOf s (L.cpu s) (fun o => o = 56 ∨ o = 80)) := by
  rw [eq_of_spec_fd (obj.node_set.spec (L := L) s _ _ _)] at e2
  rw [eq_of_spec_fd (obj.node_set.spec (L := L) s2 _ _ _)] at e3
  have h2 := ok_inj_ff e2
  have h3 := ok_inj_ff e3
  subst h2 h3
  have w1 : WritesIn st s (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)
      (L.NodeOf s (L.cpu s) (fun o => o = 56 ∨ o = 80)) :=
    writesIn_wr_node (s1 := s) hN rfl (Or.inl (by simp)) (by simp) (by simp)
  have w2 := writesIn_wr_node (s1 := L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)
    (c := L.cpu s) (o := layout.node.ARMED) (v := 0#u64)
    (P := fun o => o = 56 ∨ o = 80) hN (L.ksb_wr _ _ _) (Or.inr (by simp)) (by simp) (by simp)
  exact (w1.trans w2).mono fun b hb => by rcases hb with h | h <;> exact h

end

/-! ## The schedule state's checks across the handler's writes -/

section keep
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- The handler's write set at `s0`: this core's node words 56 (`REPROGRAM`) and 80 (`ARMED`). -/
abbrev HW (st : machine.Store S) [L : LawfulStore st] (s0 : S) : U64 → Prop :=
  L.NodeOf s0 (L.cpu s0) (fun o => o = 56 ∨ o = 80)

theorem hw_tcb {s0 s : S} (hT : TcbPlaced T) (hN : NodePlaced st T s0 (L.cpu s0)) (w : WritesIn st s0 s (HW st s0))
    {y K : U64} (hy : y ∈ T) (hK : K.val < 4096) (h8 : K.val % 8 = 0) :
    L.mem s (core.num.U64.wrapping_add y K) = L.mem s0 (core.num.U64.wrapping_add y K) := by
  refine w.mem_eq (field_aligned (hT y hy) hK h8) ?_
  rintro ⟨o, -, ho, -, e⟩
  exact tcb_node_ne hN hy (hT y hy) hK ho e

theorem hw_node {s0 s : S} (hN : NodePlaced st T s0 (L.cpu s0)) (w : WritesIn st s0 s (HW st s0)) {o : U64}
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) (hn : o.val ≠ 56 ∧ o.val ≠ 80) :
    L.mem s (L.nodeAt s0 (L.cpu s0) o) = L.mem s0 (L.nodeAt s0 (L.cpu s0) o) := by
  refine w.mem_eq (nodeAt_aligned hN ho h8) ?_
  rintro ⟨o', ho', ho2, -, e⟩
  have e' := congrArg UScalar.val e
  rw [nodeAt_val hN ho, nodeAt_val hN ho2] at e'
  omega

theorem hw_outside {s0 s : S} {b : U64} (hN : NodePlaced st T s0 (L.cpu s0)) (hcC : L.cpu s0 ∈ Cs)
    (w : WritesIn st s0 s (HW st s0)) (hb : OutsideObjs st T Cs s0 b) : L.mem s b = L.mem s0 b := by
  refine w.mem_eq hb.1 ?_
  rintro ⟨o', -, ho2, -, e⟩
  exact out_ne_node hb hcC hN ho2 (congrArg UScalar.val e).symm

/-- `NoDueT` across the handler's writes. -/
theorem nodue_hw {X Y : S} {now : U64} (hT : TcbPlaced T) (hN : NodePlaced st T X (L.cpu X))
    (hm : Tz T (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) (w : WritesIn st X Y (HW st X))
    (h : NoDueT st X now) : NoDueT st Y now := by
  unfold NoDueT at h ⊢
  have eA : L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN = L.nodeAt X (L.cpu X) layout.node.TIMER_MIN := by
    rw [w.2.1, nodeAt_of_ksb w.1]
  have em : L.mem Y (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) =
      L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) :=
    hw_node hN w (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN])
  rw [eA, em]
  rcases hm with h0 | hmT
  · exact Or.inl h0
  rcases h with h | h
  · exact Or.inl h
  right
  have e : L.mem Y (tdA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) =
      L.mem X (tdA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) :=
    hw_tcb (K := 3528#u64) hT hN w hmT (by simp) (by simp)
  rw [e]; exact h

/-- The scheduler action across the handler's writes. -/
theorem action_hw {X Y : S} (hN : NodePlaced st T X (L.cpu X)) (w : WritesIn st X Y (HW st X)) :
    L.actionW Y = L.actionW X := by
  unfold LawfulStore.actionW
  rw [w.2.1, nodeAt_of_ksb w.1]
  exact hw_node hN w (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
    (by simp [layout.node.SCHED_ACTION])

/-- `RelNone` across the handler's writes, under the invariant (as `rel_keep`). -/
theorem rel_hw {X Y : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X) (w : WritesIn st X Y (HW st X))
    (h : RelNone st X) : RelNone st Y := by
  obtain ⟨⟨Q, R, hq⟩, hB, hX, -, hS⟩ := hI
  have hT := hq.tcbs
  have hcC := hq.cur
  have hN := hq.nodes _ hcC
  have eA : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt X (L.cpu X) o := fun o => by rw [w.2.1, nodeAt_of_ksb w.1]
  have eh : L.mem Y (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) :=
    hw_node hN w (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])
  have ect : L.curTime Y = L.curTime X := by
    unfold LawfulStore.curTime LawfulStore.nodeA
    rw [eA]
    exact hw_node hN w (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME])
  unfold RelNone at h ⊢
  rw [ect, eA, eh]
  generalize hh : L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = h0 at h ⊢
  rcases h with h | h
  · exact Or.inl h
  by_cases h00 : h0 = 0#u64
  · exact Or.inl h00
  right
  have hrel := hq.release _ hcC
  have hmem : h0 ∈ R (L.cpu X) := by
    have e := hrel.head
    change L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = _ at e
    rw [hh] at e
    cases hR : R (L.cpu X) with
    | nil => rw [hR] at e; exact absurd e h00
    | cons x xs => rw [hR] at e; simp only [List.headD_cons] at e; subst e; simp
  have hhT : h0 ∈ T := hq.memTR hcC hmem
  have esc : L.mem Y (scA h0) = L.mem X (scA h0) := by
    rw [scA_eq]
    exact hw_tcb hT hN w hhT (by simp) (by simp)
  rw [esc]
  have haff : L.mem X (affA h0) = L.cpu X := hq.inR _ hcC h0 hmem
  have hrb : (L.mem X (inqA h0) &&& sched.Q_RELEASE) ≠ 0#u64 := (hq.released h0 hhT).2 (by rw [haff]; exact hmem)
  have hsc0 : L.mem X (scA h0) ≠ 0#u64 := hB.r h0 hhT hrb
  have hscS : L.mem X (scA h0) ∈ Scs := (hX.2.2.bound h0 hhT hsc0).1
  have hAc : L.mem X (scA h0) ∈ Ac := hB.sact h0 hhT (Or.inr (Or.inl hrb)) hsc0
  generalize hsc : L.mem X (scA h0) = sc at h hscS hAc ⊢
  have hmax : L.rmax X sc ≠ 0#u64 := (hS.act sc hscS).1 hAc
  obtain ⟨hwf, -, hin⟩ := hS.all sc hscS
  have wf := hwf hmax
  obtain ⟨h8, hm, hfit⟩ := wf.bounds
  obtain ⟨-, -, -, hhd, -, hri⟩ := wf.inside
  have keep : ∀ b, Aligned b → InSC sc (Z sc) b → L.mem Y b = L.mem X b := fun b hb hi =>
    hw_outside hN hcC w (hq.omega b (hS.sub b (hin b hb hi)))
  have hmin := wf.min_le
  simp at hmin
  have e1 : L.rhead Y sc = L.rhead X sc := keep _ (by unfold Aligned; rw [hhd]; omega) ⟨by rw [hhd]; omega, by rw [hhd]; omega⟩
  obtain ⟨r1, r2, r3⟩ := hri (L.rhead X sc) wf.head_lt
  have e2 : L.mem Y (rtA sc (L.rhead X sc)) = L.mem X (rtA sc (L.rhead X sc)) :=
    keep _ (by unfold Aligned; rw [r1]; omega) ⟨by rw [r1]; omega, by rw [r1]; omega⟩
  simp only [LawfulStore.refill] at h ⊢
  rw [e1, e2]
  exact h

end keep

/-! ## `schedule` in the quiet case -/

section sched
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type _} (ar : machine.Arch A)

/-- `update_timestamp` keeps the scheduler action. -/
theorem action_ut (hA : P0.ArchTotal ar) {s s1 : S} {a a1 : A} (hN : NodePlaced st T s (L.cpu s))
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) : L.actionW s1 = L.actionW s := by
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
  simp only at er
  subst er
  unfold LawfulStore.actionW
  rw [utW_cpu, nodeAt_of_ksb (utW_ksb _ _)]
  refine utW_mem hN n1 (nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
    ?_ ?_
  · unfold ctA
    exact nodeAt_ne hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.SCHED_ACTION, layout.node.CUR_TIME])
  · unfold cnA
    exact nodeAt_ne hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.CONSUMED])
      (by simp [layout.node.SCHED_ACTION, layout.node.CONSUMED])

/-- **`schedule` in the quiet case is `schedTail`**: after `update_timestamp` nothing is due (`timer_due`,
`release_due` declined there), `sched_quiet` saw the action `RESUME_CURRENT`, and the timer handler's writes
(`HW`) keep all three. Also: the invariant holds after `update_timestamp`. -/
theorem irq_quiet_schedule (hA : P0.ArchTotal ar) {s s1 s3 : S} {a a1 a3 : A} {now : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (eq : localtimer.sched_quiet st s (L.cpu s) = ok true)
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) (enow : sched.cur_time st s1 = ok now)
    (erel : localtimer.release_due st s1 (L.cpu s) = ok false)
    (edue : localtimer.timer_due st s1 (L.cpu s) now = ok false) (w : WritesIn st s1 s3 (HW st s1)) :
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧ sched.schedule st ar s3 a3 = schedTail (st := st) ar s3 a3 := by
  have h0 := hI.1.choose_spec.choose_spec
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  have hB1 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := by
    have := sched.update_timestamp.bxc hA s a (BlkOK.bxi (BXI.blk hI))
    rw [eu, WP.spec_ok] at this
    try simp only [WP.uncurry'_pair] at this
    exact this.1.1
  refine ⟨hB1, ?_⟩
  have c1 : L.cpu s1 = L.cpu s := by
    obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
    simp only at er
    rw [er, utW_cpu]
  have h1 := hB1.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h1.tcbs
  have hcC1 : L.cpu s1 ∈ Cs := h1.cur
  have hN1 : NodePlaced st T s1 (L.cpu s1) := h1.nodes _ hcC1
  have hnow : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_TIME) = now := by
    rw [cur_time_ok] at enow; exact ok_inj_ff enow
  have nd1 : NoDueT st s1 now := td_false (by rw [c1]; exact edue)
  have hm1 := (TInv.tm (BXI.blk hB1)).min _ hcC1
  have nd3 : NoDueT st s3 now := nodue_hw hT hN1 hm1 w nd1
  have hct3 : L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.CUR_TIME) = now := by
    rw [w.2.1, nodeAt_of_ksb w.1,
      hw_node hN1 w (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
        (by simp [layout.node.CUR_TIME])]
    exact hnow
  have hT3 : L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.CUR_TIME) <
        L.mem s3 (tdA (L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN))) := by
    rw [hct3]; exact nd3
  have hR3 : RelNone st s3 := rel_hw hB1 w (rel_false (by rw [c1]; exact erel))
  have hact3 : L.actionW s3 = sched.ACTION_RESUME_CURRENT := by
    rw [action_hw hN1 w, action_ut ar hA hN eu]; exact sq_true eq
  exact schedule_resume ar s3 a3 hT3 hR3 hact3

end sched

end Fl4Proofs.P2
