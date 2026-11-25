/-
# P2: the round-robin case's walk: the state after `check_budget`

`rrw_keep`: the round-robin writes (`RrW`, relative to the entry state `X`) keep this core's node words below 120
other than 16, 40, 56 and 80, every TCB word other than the sched links and the queue word, and every `Ω` word
outside the current SC's ring and `CONSUMED`.

`rr_cb_state`: at a state `s1` with the P1 invariant (`BXI`) where `round_robin_ok` accepted the current thread
and SC at the current time and the budget is insufficient, `check_budget` is the round-robin `charge_budget` run
(`check_budget_ins`, `charge_budget_rr_run` with `rr_tail_F` for its `F`); it writes only `RrW`
(`rr_run_writes`), leaves the action `CHOOSE_NEW`, the current thread schedulable (`is_schedulable_rel`) and
queued, and alone in its ready queue, whose priority is the highest marked one (`highest_prio_app` after
`append`, carried by `highest_prio_agree` across the action and `REPROGRAM` writes).

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqRS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section law
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **What the round-robin writes keep** (module docstring). -/
theorem rrw_keep {T Cs Ω Xs : Set U64} {H : Heap} {Q : U64 → U64 → List U64} {Rq : U64 → List U64}
    {X Y : S} {ct csc : U64} {z : Nat}
    (h : SchedQueuesInvX st T Cs Ω H Xs X Q Rq) (hct : ct ∈ T)
    (hΩ : ∀ b, Aligned b → (InRing csc z b ∨ b = core.num.U64.wrapping_add csc layout.sc.CONSUMED) → b ∈ Ω)
    (w : WritesIn st X Y (RrW st T X ct csc z)) :
    (∀ o : U64, o.val < 120 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 40 → o.val ≠ 56 → o.val ≠ 80 →
      L.mem Y (L.nodeAt X (L.cpu X) o) = L.mem X (L.nodeAt X (L.cpu X) o)) ∧
    (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 → K.val ≠ 3592 →
      L.mem Y (core.num.U64.wrapping_add y K) = L.mem X (core.num.U64.wrapping_add y K)) ∧
    (∀ b ∈ Ω, ¬ InRing csc z b → b ≠ core.num.U64.wrapping_add csc layout.sc.CONSUMED →
      L.mem Y b = L.mem X b) := by
  have hT := h.tcbs
  have hcC := h.cur
  have hN := h.nodes _ hcC
  have hta := hT ct hct
  refine ⟨fun o ho h8 h16 h40 h56 h80 => ?_, fun y hy K hK h8 k1 k2 k3 => ?_, fun b hb n1 n2 => ?_⟩
  · have ha : Aligned (L.nodeAt X (L.cpu X) o) := nodeAt_aligned hN (by omega) h8
    refine w.mem_eq ha ?_
    rintro (hr | hr | ⟨o', ho', h1', -, e⟩ | hr | ⟨y, hy, hr | hr⟩)
    · exact out_ne_node (h.omega _ (hΩ _ ha (Or.inl hr))) hcC hN (o := o) (by omega) rfl
    · exact out_ne_node (h.omega _ (hΩ _ ha (Or.inr hr))) hcC hN (o := o) (by omega) rfl
    · have e' := congrArg UScalar.val e
      rw [nodeAt_val hN (off := o) (by omega), nodeAt_val hN h1'] at e'
      omega
    · exact tcb_node_ne hN hct hta (K := 3592#u64) (by simp) (by omega) hr.symm
    · exact tcb_node_ne hN hy (hT y hy) (K := 3480#u64) (by simp) (by omega) hr.symm
    · exact tcb_node_ne hN hy (hT y hy) (K := 3488#u64) (by simp) (by omega) hr.symm
  · have ha : Aligned (core.num.U64.wrapping_add y K) := field_aligned (hT y hy) hK h8
    refine w.mem_eq ha ?_
    rintro (hr | hr | ⟨o', -, h1', -, e⟩ | hr | ⟨y', hy', hr | hr⟩)
    · exact out_ne_field (h.omega _ (hΩ _ ha (Or.inl hr))) hy (hT y hy) hK rfl
    · exact out_ne_field (h.omega _ (hΩ _ ha (Or.inr hr))) hy (hT y hy) hK rfl
    · exact tcb_node_ne hN hy (hT y hy) hK h1' e
    · exact tcb_word_ne (hT y hy) hta (K2 := 3592#u64) hK (by simp) (fun _ e => by simp at e; omega) hr
    · exact tcb_word_ne (hT y hy) (hT y' hy') (K2 := 3480#u64) hK (by simp) (fun _ e => by simp at e; omega) hr
    · exact tcb_word_ne (hT y hy) (hT y' hy') (K2 := 3488#u64) hK (by simp) (fun _ e => by simp at e; omega) hr
  · have ho := h.omega b hb
    refine w.mem_eq ho.1 ?_
    rintro (hr | hr | ⟨o', -, h1', -, e⟩ | hr | ⟨y', hy', hr | hr⟩)
    · exact n1 hr
    · exact n2 hr
    · exact out_ne_node ho hcC hN h1' (congrArg UScalar.val e).symm
    · exact out_ne_field ho hct hta (K := 3592#u64) (by simp) (congrArg UScalar.val hr).symm
    · exact out_ne_field ho hy' (hT y' hy') (K := 3480#u64) (by simp) (congrArg UScalar.val hr).symm
    · exact out_ne_field ho hy' (hT y' hy') (K := 3488#u64) (by simp) (congrArg UScalar.val hr).symm

end law

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

set_option maxHeartbeats 4000000 in
/-- **The state after the round-robin `check_budget`** (module docstring). -/
theorem rr_cb_state {A : Type} (ar : machine.Arch A) {s1 s2 : S} {a1 a2 : A} {x : Bool}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1)
    (hrr : localtimer.round_robin_ok st ar s1 a1 (L.cpu s1) (L.curW s1) (L.cscW s1) (L.curTime s1) = ok true)
    (haff : L.mem s1 (affA (L.curW s1)) = L.cpu s1) (hsct : L.mem s1 (scA (L.curW s1)) = L.cscW s1)
    (hAc : L.cscW s1 ∈ Ac) (hact : L.actionW s1 = sched.ACTION_RESUME_CURRENT)
    (hins : ∀ c, sched.consumed st s1 = ok c → sporadic.sufficient st ar s1 a1 (L.cscW s1) c = ok false)
    (ecb : sched.check_budget st ar s1 a1 = ok (x, s2, a2)) :
    a2 = a1 ∧ WritesIn st s1 s2 (RrW st T s1 (L.curW s1) (L.cscW s1) (Z (L.cscW s1))) ∧
      L.actionW s2 = sched.ACTION_CHOOSE_NEW ∧ sched.is_schedulable st s2 (L.curW s1) = ok true ∧
      (L.mem s2 (inqA (L.curW s1)) &&& sched.Q_QUEUED) ≠ 0#u64 ∧
      sched.highest_prio st s2 0#u64 = ok (L.mem s1 (prioA (L.curW s1))) ∧ L.l1W s2 (L.cpu s1) ≠ 0#u64 ∧
      L.mem s2 (L.nodeAt s1 (L.cpu s1) (rqOff (L.mem s1 (prioA (L.curW s1))))) = L.curW s1 ∧
      L.mem s2 (L.nodeAt s1 (L.cpu s1) (rqTailOff (L.mem s1 (prioA (L.curW s1))))) = L.curW s1 := by
  obtain ⟨Qq, Rq, h1⟩ := hI.1
  have hB1 := hI.2.1
  have hX1 := hI.2.2.1
  have hSg1 := hI.2.2.2.1
  have hS1 := hI.2.2.2.2
  have hT : TcbPlaced T := h1.tcbs
  have hcC : L.cpu s1 ∈ Cs := h1.cur
  have hN1 : NodePlaced st T s1 (L.cpu s1) := h1.nodes _ hcC
  have hcT : L.curW s1 ∈ T := h1.curT
  have hcS : L.cscW s1 ∈ Scs := hX1.2.2.cur
  have hW : RefillsWF st s1 (L.cscW s1) (Z (L.cscW s1)) := hS1.wf hcS hAc
  have hp1 : (L.mem s1 (prioA (L.curW s1))).val < 256 := h1.prio _ hcT
  obtain ⟨⟨isc, eisc, hne⟩, hper, hsch1, hnq1, -, -, -, hhi1⟩ := round_robin_ok_true hrr
  -- the current SC's words
  obtain ⟨hP, hz⟩ := hX1.1.sc _ hcS
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hcv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv' : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hmv := sc_word_val hP hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
  have hmv' : layout.sc.REFILL_MAX.val = 72 := by simp [layout.sc.REFILL_MAX]
  have hal : Aligned (core.num.U64.wrapping_add (L.cscW s1) layout.sc.CONSUMED) := by
    unfold Aligned; rw [hcv, hcv']; omega
  have inΩ : ∀ b, Aligned b → (InRing (L.cscW s1) (Z (L.cscW s1)) b ∨
      b = core.num.U64.wrapping_add (L.cscW s1) layout.sc.CONSUMED) → b ∈ Ω := by
    rintro b hb (hh | rfl)
    · exact hX1.1.scW _ hcS b hb hh.inSC
    · exact hX1.1.scW _ hcS _ hb ⟨by rw [hcv]; omega, by rw [hcv, hcv']; omega⟩
  have hmΩ : maxA (L.cscW s1) ∈ Ω := hS1.sub _ (hS1.all _ hcS).2.1
  have hmR : ¬ InRing (L.cscW s1) (Z (L.cscW s1)) (maxA (L.cscW s1)) := fun h => by
    unfold InRing maxA at h; rw [hmv, hmv'] at h; omega
  have hmC : maxA (L.cscW s1) ≠ core.num.U64.wrapping_add (L.cscW s1) layout.sc.CONSUMED := fun e => by
    have e' := congrArg UScalar.val e
    unfold maxA at e'; rw [hmv, hcv, hmv', hcv'] at e'; omega
  have hco : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
  have aC : Aligned (L.nodeAt s1 (L.cpu s1) layout.node.CONSUMED) :=
    nodeAt_aligned hN1 (by rw [hco]; omega) (by rw [hco])
  -- the budget check is the round-robin `charge_budget` run
  obtain ⟨c, -, ecg⟩ := check_budget_ins ar hins ecb
  have key : ∀ s2' s3', cbRR st s1 (L.cscW s1) c = ok s2' → sched.set_consumed st s2' 0#u64 = ok s3' →
      SchedQueuesInv st T Cs Ω H s3' Qq Rq ∧ L.ksb s3' = L.ksb s1 ∧ L.cpu s3' = L.cpu s1 ∧
      L.curW s3' = L.curW s1 ∧ L.rmax s3' (L.cscW s1) = L.rmax s1 (L.cscW s1) ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s3' (core.num.U64.wrapping_add y K) = L.mem s1 (core.num.U64.wrapping_add y K)) ∧
      (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 →
        L.mem s3' (L.nodeAt s1 (L.cpu s1) o) = L.mem s1 (L.nodeAt s1 (L.cpu s1) o)) := by
    intro s2' s3' e2 e3
    obtain ⟨w2, -⟩ := cbRR_frame hW hal e2
    obtain ⟨h2, hB2, hX2, hSg2, -, cur2, -, -⟩ := ring_bx h1 hB1 hX1 hSg1 hcS w2
    have e3' : s3' = L.wr s2' (L.nodeAt s2' (L.cpu s2') layout.node.CONSUMED) 0#u64 := by
      have e := e3
      rw [eq_of_spec_fd (sched.set_consumed.spec (L := L) s2' _)] at e
      exact (ok_inj_ff e).symm
    obtain ⟨h3, -, -, -, -, cur3, -, -⟩ := node_bx (o := layout.node.CONSUMED) (v := 0#u64) h2 hB2 hX2 hSg2
      (by simp [layout.node.CONSUMED, LowFree]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
    rw [← e3'] at h3 cur3
    rw [w2.2.1, nodeAt_of_ksb w2.1] at e3'
    refine ⟨h3, by rw [e3', L.ksb_wr, w2.1], by rw [e3', LawfulStore.cpu_wr, w2.2.1], cur3.trans cur2, ?_, ?_, ?_⟩
    · unfold LawfulStore.rmax
      rw [e3', mem_wr_ne' aC (h1.omega _ hmΩ).1
        (fun e => out_ne_node (h1.omega _ hmΩ) hcC hN1 (by rw [hco]; omega) (congrArg UScalar.val e))]
      exact w2.mem_eq (h1.omega _ hmΩ).1 (fun hh => hh.elim hmR hmC)
    · intro y hy K hK hK8
      rw [e3', mem_wr_ne' aC (field_aligned (hT y hy) hK hK8)
        (Ne.symm (tcb_node_ne hN1 hy (hT y hy) hK (by rw [hco]; omega)))]
      exact w2.mem_eq (field_aligned (hT y hy) hK hK8) fun hh =>
        out_ne_field (h1.omega _ (inΩ _ (field_aligned (hT y hy) hK hK8) hh)) hy (hT y hy) hK rfl
    · intro o ho ho8 h40
      rw [e3', L.mem_wr_ne aC (nodeAt_aligned hN1 ho ho8) (by
        rw [nodeAt_val hN1 (by rw [hco]; omega), nodeAt_val hN1 ho, hco]; omega)]
      exact w2.mem_eq (nodeAt_aligned hN1 ho ho8) fun hh =>
        out_ne_node (h1.omega _ (inΩ _ (nodeAt_aligned hN1 ho ho8) hh)) hcC hN1 ho rfl
  have hsch : ∀ s2' s3', cbRR st s1 (L.cscW s1) c = ok s2' → sched.set_consumed st s2' 0#u64 = ok s3' →
      sched.is_schedulable st s3' (L.curW s3') = ok true := by
    intro s2' s3' e2 e3
    obtain ⟨-, -, -, cur3, rm3, fl3, -⟩ := key s2' s3' e2 e3
    rw [cur3, ← hsch1]
    refine is_schedulable_congr ?_ ?_ ?_ ?_
    · rw [stA_eq, fl3 _ hcT 3328#u64 (by simp) (by simp)]
    · rw [scA_eq, fl3 _ hcT 3464#u64 (by simp) (by simp)]
    · intro _; rw [hsct]; exact rm3
    · rw [inqA_eq, fl3 _ hcT 3592#u64 (by simp) (by simp)]
  have F : ∀ s2' s3', cbRR st s1 (L.cscW s1) c = ok s2' → sched.set_consumed st s2' 0#u64 = ok s3' →
      RRTail st ar T (fun _ => True) (fun _ => True) s3' a1 := fun s2' s3' e2 e3 =>
    rr_tail_F (R := fun _ => True) (W := fun _ => True) ar hI hrr haff hAc hact
      (fun _ _ _ => ⟨trivial, trivial⟩) trivial trivial trivial trivial (fun _ _ => ⟨trivial, trivial⟩)
      (by unfold PathObl.RdHead; exact ⟨trivial, trivial, trivial⟩) trivial trivial trivial trivial trivial
      trivial trivial (fun _ => trivial) e2 e3
  obtain ⟨s2', s3', s4', e2, e3, ea, e6, ha⟩ :=
    charge_budget_rr_run ar (fun i ei => by rw [eisc] at ei; rw [← ok_inj_ff ei]; exact hne) hper hsch F ecg
  obtain ⟨h3, k3, c3, cur3, -, fl3, nd3⟩ := key s2' s3' e2 e3
  have F3 := F s2' s3' e2 e3
  -- the writes, the queue word, the action
  obtain ⟨wY, hinqY, hactY⟩ := rr_run_writes ar hN1 hW hal e2 e3 F3 ea e6
  rw [cur3] at wY hinqY
  have inq3 : L.mem s3' (inqA (L.curW s1)) = L.mem s1 (inqA (L.curW s1)) := by
    rw [inqA_eq]; exact fl3 _ hcT 3592#u64 (by simp) (by simp)
  simp only [inq3, hnq1, ne_eq, not_true_eq_false, ↓reduceIte] at hinqY
  obtain ⟨kN, kT, kΩ⟩ := rrw_keep h1 hcT inΩ wY
  have hsch2 : sched.is_schedulable st s2 (L.curW s1) = ok true := by
    rw [← hsch1]
    refine is_schedulable_rel ?_ ?_ ?_ ?_
    · rw [stA_eq, kT _ hcT 3328#u64 (by simp) (by simp) (by simp) (by simp) (by simp)]
    · rw [scA_eq, kT _ hcT 3464#u64 (by simp) (by simp) (by simp) (by simp) (by simp)]
    · intro _; rw [hsct]; unfold LawfulStore.rmax; exact kΩ _ hmΩ hmR hmC
    · rw [hinqY, or_qq_qr]
  have hq2 : (L.mem s2 (inqA (L.curW s1)) &&& sched.Q_QUEUED) ≠ 0#u64 := by
    rw [hinqY, or_qq_qq]; exact qq_ne
  -- `append`: the current thread alone in its queue, the highest
  obtain ⟨xs, hr, hq⟩ := F3.rel
  obtain ⟨k4, c4, -⟩ := append_keep F3.hT F3.ct F3.prio F3.aff F3.hN hr hq ea
  rw [cur3] at ea
  have hN3 : NodePlaced st T s3' (L.cpu s3') := h3.nodes _ h3.cur
  have pr3 : L.mem s3' (prioA (L.curW s1)) = L.mem s1 (prioA (L.curW s1)) := by
    rw [prioA_eq]; exact fl3 _ hcT 3448#u64 (by simp) (by simp)
  have haff3 : L.mem s3' (affA (L.curW s1)) = L.cpu s3' := by
    rw [c3]; unfold affA; rw [fl3 _ hcT 3520#u64 (by simp) (by simp)]; exact haff
  have hnq3 : (L.mem s3' (inqA (L.curW s1)) &&& sched.Q_QUEUED) = 0#u64 := by rw [inq3]; exact hnq1
  have eL1 : layout.node.L1_BITMAP = l1Off := by unfold layout.node.L1_BITMAP l1Off w64; rfl
  have l13 : L.l1W s3' (L.cpu s1) = L.l1W s1 (L.cpu s1) := by
    unfold LawfulStore.l1W; rw [nodeAt_of_ksb k3]
    exact nd3 _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]) (by rw [l1Off_val]; omega)
  have l23 : ∀ g < 4, L.l2W s3' (L.cpu s1) g = L.l2W s1 (L.cpu s1) g := fun g hg => by
    unfold LawfulStore.l2W; rw [nodeAt_of_ksb k3]
    exact nd3 _ (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
  have hRQ1 := h1.ready _ hcC
  have hhi3 : L.l1W s3' (L.cpu s3') = 0#u64 ∨ ∃ h, sched.highest_prio st s3'
      (L.mem s1 (core.num.U64.wrapping_add (L.ksb s1) layout.ks.CUR_DOMAIN)) = ok h ∧
      h < L.mem s3' (prioA (L.curW s1)) := by
    rw [c3, l13, pr3]
    rcases hhi1 with h0 | ⟨p, hp, hlt⟩
    · left; unfold LawfulStore.l1W; rw [← eL1]; exact h0
    · by_cases h0 : L.l1W s1 (L.cpu s1) = 0#u64
      · exact Or.inl h0
      · right
        refine ⟨p, ?_, hlt⟩
        rw [highest_prio_agree (Z := s3') _ hN1 hRQ1.2 h0 k3 c3 l13 l23]
        exact hp
  obtain ⟨hp4, hl4, hh4, he4, hRQ4⟩ := highest_prio_app hT hcT (h3.prio _ hcT) hN3 haff3 (h3.ready _ h3.cur)
    hnq3 (fun p' hp' => h3.notQ hcT hnq3 h3.cur hp') hhi3 ea (hN3.ksb k4) c4
  -- the action and `REPROGRAM` writes
  have k4s : L.ksb s4' = L.ksb s1 := k4.trans k3
  have c4s : L.cpu s4' = L.cpu s1 := c4.trans c3
  have hro : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have aA : Aligned (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) :=
    nodeAt_aligned hN1 (by rw [act_val]; omega) (by rw [act_val])
  have aR : Aligned (L.nodeAt s1 (L.cpu s1) layout.node.REPROGRAM) :=
    nodeAt_aligned hN1 (by rw [hro]; omega) (by rw [hro])
  have e5 : L.nodeAt s4' (L.cpu s4') layout.node.SCHED_ACTION = L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION := by
    rw [c4s, nodeAt_of_ksb k4s]
  rw [e5] at e6
  have e6' : s2 = L.wr (L.wr s4' (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) sched.ACTION_CHOOSE_NEW)
      (L.nodeAt s1 (L.cpu s1) layout.node.REPROGRAM) 1#u64 := by
    have e := e6
    rw [eq_of_spec_fd (sched.set_reprogram.spec (L := L) _)] at e
    rw [← ok_inj_ff e]
    unfold LawfulStore.nodeA
    rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _), c4s, nodeAt_of_ksb k4s]
  have k2s : L.ksb s2 = L.ksb s1 := by rw [e6', L.ksb_wr, L.ksb_wr, k4s]
  have c2s : L.cpu s2 = L.cpu s1 := by rw [e6', LawfulStore.cpu_wr, LawfulStore.cpu_wr, c4s]
  have n24 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 56 →
      L.mem s2 (L.nodeAt s1 (L.cpu s1) o) = L.mem s4' (L.nodeAt s1 (L.cpu s1) o) := by
    intro o ho ho8 h16 h56
    rw [e6', L.mem_wr_ne aR (nodeAt_aligned hN1 ho ho8) (by
        rw [nodeAt_val hN1 (by rw [hro]; omega), nodeAt_val hN1 ho, hro]; omega),
      L.mem_wr_ne aA (nodeAt_aligned hN1 ho ho8) (by
        rw [nodeAt_val hN1 (by rw [act_val]; omega), nodeAt_val hN1 ho, act_val]; omega)]
  have hl1 : L.l1W s2 (L.cpu s4') = L.l1W s4' (L.cpu s4') := by
    unfold LawfulStore.l1W
    rw [c4s, nodeAt_of_ksb k2s, nodeAt_of_ksb k4s]
    exact n24 _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]) (by rw [l1Off_val]; omega) (by rw [l1Off_val]; omega)
  have hl2 : ∀ g < 4, L.l2W s2 (L.cpu s4') g = L.l2W s4' (L.cpu s4') g := fun g hg => by
    unfold LawfulStore.l2W
    rw [c4s, nodeAt_of_ksb k2s, nodeAt_of_ksb k4s]
    exact n24 _ (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
      (by rw [l2Off_val hg]; omega)
  have hN4 : NodePlaced st T s4' (L.cpu s4') := by rw [c4]; exact hN3.ksb k4
  have hB4 : BitmapOK st s4' (L.cpu s4') (fun p' => Function.update (Qq (L.cpu s3')) (L.mem s3' (prioA (L.curW s1)))
      [L.curW s1] p' ≠ []) := by
    rw [c4]; exact hRQ4.2
  rw [c3, nodeAt_of_ksb k4s, pr3] at hh4 he4
  rw [pr3] at hp4
  refine ⟨ha, wY, hactY, hsch2, hq2, ?_, ?_, ?_, ?_⟩
  · rw [highest_prio_agree (Z := s2) _ hN4 hB4 hl4 (k2s.trans k4s.symm) (c2s.trans c4s.symm) hl1 hl2]
    exact hp4
  · rw [← c4s, hl1]; exact hl4
  · rw [n24 (rqOff (L.mem s1 (prioA (L.curW s1)))) (by rw [rqOff_val hp1]; omega) (by rw [rqOff_val hp1]; omega) (by rw [rqOff_val hp1]; omega)
      (by rw [rqOff_val hp1]; omega)]
    exact hh4
  · rw [n24 (rqTailOff (L.mem s1 (prioA (L.curW s1)))) (by rw [rqTailOff_val hp1]; omega) (by rw [rqTailOff_val hp1]; omega)
      (by rw [rqTailOff_val hp1]; omega) (by rw [rqTailOff_val hp1]; omega)]
    exact he4

end main

end Fl4Proofs.P2
