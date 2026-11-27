/-
# P2: `RRTail` after the round-robin merge (the premise `F` of `charge_budget.guard_rrC`)

`rr_queue`: from the scheduler queue invariant, a thread of this core has its ready queue related (P1
`ReadyRel`), is in it only if queued (`notQ`), and the queue's tail is a TCB when the queue is non-empty.

`rr_tail_F`: at a state `s1` with the P1 invariant (`BXI`) where `round_robin_ok` accepted the current thread and
SC at the current time, with the current thread on this core, the current SC active and the action
`RESUME_CURRENT`, every state `s3` reached by `charge_budget`'s ring merge (`cbRR`) and the clearing of the node's
`CONSUMED` satisfies `RRTail` for the read / write sets `R` / `W`, given at `s1` the words `RRTail` asks for. The
invariants pass through the writes by P1 `ring_bx` / `node_bx`; the head refill after the merge is
`cbRR_head`'s and survives the node write (`rr_wr_out`, the node word lies outside the SC: `node_outside_sc`),
so the SC is ready (head time ≤ the unchanged current time) and sufficient (merged amount ≥ `min_budget`).

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqRW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (RdBitmap RdHead)

section law
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **The ready queue of a thread of this core** (module docstring). -/
theorem rr_queue {T Cs Ω Xs : Set U64} {H : Heap} {X : S} {Q : U64 → U64 → List U64} {Rq : U64 → List U64}
    {t : U64} (h : SchedQueuesInvX st T Cs Ω H Xs X Q Rq) (ht : t ∈ T) :
    (L.mem X (prioA t)).val < 256 ∧
      (∃ xs, QueueRel (L.mem X) T .Sched (L.rqQ X (L.cpu X) (L.mem X (prioA t))) xs ∧
        ((L.mem X (inqA t) &&& sched.Q_QUEUED) = 0#u64 → t ∉ xs)) ∧
      (L.mem X (L.nodeAt X (L.cpu X) (rqOff (L.mem X (prioA t)))) ≠ 0#u64 →
        L.mem X (L.nodeAt X (L.cpu X) (rqTailOff (L.mem X (prioA t)))) ∈ T) := by
  have hp := h.prio t ht
  have hr := (h.ready _ h.cur).1.rel _ hp
  refine ⟨hp, ⟨_, hr, fun h0 => h.notQ ht h0 h.cur hp⟩, fun hne => ?_⟩
  by_cases hn : Q (L.cpu X) (L.mem X (prioA t)) = []
  · exfalso
    apply hne
    have e1 := hr.head
    rw [hn] at e1
    exact e1
  · have hm := getLastD_mem hn 0#u64
    have e2 := hr.last
    rw [← e2] at hm
    exact hr.mem _ hm

end law

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **`RRTail` after the round-robin merge** (module docstring). -/
theorem rr_tail_F {A : Type} (ar : machine.Arch A) {R W : U64 → Prop} {s1 s2 s3 : S} {a1 : A} {used : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1)
    (hrr : localtimer.round_robin_ok st ar s1 a1 (L.cpu s1) (L.curW s1) (L.cscW s1) (L.curTime s1) = ok true)
    (haff : L.mem s1 (affA (L.curW s1)) = L.cpu s1) (hAc : L.cscW s1 ∈ Ac)
    (hact : L.actionW s1 = sched.ACTION_RESUME_CURRENT)
    (nRW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s1 (L.cpu s1) o) ∧ W (L.nodeAt s1 (L.cpu s1) o))
    (rPer : R (core.num.U64.wrapping_add (L.cscW s1) layout.sc.PERIOD))
    (rS : R (stA (L.curW s1))) (rC : R (scA (L.curW s1))) (rM : R (maxA (L.mem s1 (scA (L.curW s1)))))
    (vt : ∀ sl, obj.Tcb.slot (L.curW s1) layout.tcb.SLOT_TIMEOUT_HANDLER = ok sl →
      R sl ∧ R (core.num.U64.wrapping_add sl 8#u64))
    (hd : RdHead (L := L) R s1 (L.cscW s1))
    (rI : R (inqA (L.curW s1))) (wI : W (inqA (L.curW s1))) (rA : R (affA (L.curW s1)))
    (rD : R (domA (L.curW s1))) (rP : R (prioA (L.curW s1)))
    (wN : W (nextA .Sched (L.curW s1))) (wP : W (prevA .Sched (L.curW s1)))
    (wEn : L.mem s1 (L.nodeAt s1 (L.cpu s1) (rqOff (L.mem s1 (prioA (L.curW s1))))) ≠ 0#u64 →
      W (nextA .Sched (L.mem s1 (L.nodeAt s1 (L.cpu s1) (rqTailOff (L.mem s1 (prioA (L.curW s1))))))))
    (e2 : cbRR st s1 (L.cscW s1) used = ok s2) (e3 : sched.set_consumed st s2 0#u64 = ok s3) :
    RRTail st ar T R W s3 a1 := by
  obtain ⟨⟨Qq, Rq, h1⟩, hB1, hX1, hSg1, hS1⟩ := hI
  have hT : TcbPlaced T := h1.tcbs
  have hcC : L.cpu s1 ∈ Cs := h1.cur
  have hN1 : NodePlaced st T s1 (L.cpu s1) := h1.nodes _ hcC
  have hcT : L.curW s1 ∈ T := h1.curT
  have ht' := hT _ hcT
  have hcS : L.cscW s1 ∈ Scs := hX1.2.2.cur
  have hW : RefillsWF st s1 (L.cscW s1) (Z (L.cscW s1)) := hS1.wf hcS hAc
  obtain ⟨-, hper, -, -, hne, htime, ⟨m, hm, hle⟩, -⟩ := round_robin_ok_true hrr
  obtain ⟨hP, hz⟩ := hX1.1.sc _ hcS
  obtain ⟨-, h128, -⟩ := sc_lo hP hz
  have hcv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv' : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hal : Aligned (core.num.U64.wrapping_add (L.cscW s1) layout.sc.CONSUMED) := by
    obtain ⟨h8, -, -⟩ := sc_lo hP hz
    unfold Aligned; rw [hcv, hcv']; omega
  obtain ⟨w2, hW2⟩ := cbRR_frame hW hal e2
  obtain ⟨hd2, hp2, hr2⟩ := cbRR_head hW hne e2
  have inΩ : ∀ b, Aligned b → (InRing (L.cscW s1) (Z (L.cscW s1)) b ∨
      b = core.num.U64.wrapping_add (L.cscW s1) layout.sc.CONSUMED) → b ∈ Ω := by
    rintro b hb (hh | rfl)
    · exact hX1.1.scW _ hcS b hb hh.inSC
    · exact hX1.1.scW _ hcS _ hb ⟨by rw [hcv]; omega, by rw [hcv, hcv']; omega⟩
  have fld2 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s1 (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
    w2.mem_eq (field_aligned (hT y hy) hK hK8) fun hh =>
      out_ne_field (h1.omega _ (inΩ _ (field_aligned (hT y hy) hK hK8) hh)) hy (hT y hy) hK rfl
  have node2 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s2 (L.nodeAt s1 (L.cpu s1) o) = L.mem s1 (L.nodeAt s1 (L.cpu s1) o) := fun o ho h8 =>
    w2.mem_eq (nodeAt_aligned hN1 ho h8) fun hh =>
      out_ne_node (h1.omega _ (inΩ _ (nodeAt_aligned hN1 ho h8) hh)) hcC hN1 ho rfl
  -- the invariants at `s2` and `s3`
  obtain ⟨h2, hB2, hX2, hSg2, -, -, -, -⟩ := ring_bx h1 hB1 hX1 hSg1 hcS w2
  have hco : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
  have e3' : s3 = L.wr s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) 0#u64 := by
    have e := e3
    rw [eq_of_spec_fd (sched.set_consumed.spec (L := L) s2 _)] at e
    exact (ok_inj_ff e).symm
  obtain ⟨h3, -, -, -, -, -, -, -⟩ := node_bx (o := layout.node.CONSUMED) (v := 0#u64) h2 hB2 hX2 hSg2
    (by simp [layout.node.CONSUMED, LowFree]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  rw [← e3'] at h3
  rw [w2.2.1, nodeAt_of_ksb w2.1] at e3'
  have k3 : L.ksb s3 = L.ksb s1 := by rw [e3', L.ksb_wr, w2.1]
  have c3 : L.cpu s3 = L.cpu s1 := by rw [e3', LawfulStore.cpu_wr, w2.2.1]
  have eN : ∀ o, L.nodeAt s3 (L.cpu s3) o = L.nodeAt s1 (L.cpu s1) o := fun o => by rw [c3, nodeAt_of_ksb k3]
  have aC : Aligned (L.nodeAt s1 (L.cpu s1) layout.node.CONSUMED) :=
    nodeAt_aligned hN1 (by rw [hco]; omega) (by rw [hco])
  have fld3 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s1 (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 => by
    rw [e3', mem_wr_ne' aC (field_aligned (hT y hy) hK hK8)
      (Ne.symm (tcb_node_ne hN1 hy (hT y hy) hK (by rw [hco]; omega)))]
    exact fld2 y hy K hK hK8
  have node3 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 →
      L.mem s3 (L.nodeAt s1 (L.cpu s1) o) = L.mem s1 (L.nodeAt s1 (L.cpu s1) o) := fun o ho h8 h40 => by
    rw [e3', L.mem_wr_ne aC (nodeAt_aligned hN1 ho h8) (by
      rw [nodeAt_val hN1 (by rw [hco]; omega), nodeAt_val hN1 ho, hco]; omega)]
    exact node2 o ho h8
  have cur3 : L.curW s3 = L.curW s1 := by
    unfold LawfulStore.curW
    rw [eN]
    exact node3 _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
  have csc3 : L.cscW s3 = L.cscW s1 := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [eN]
    exact node3 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have act3 : L.actionW s3 = L.actionW s1 := by
    unfold LawfulStore.actionW
    rw [eN]
    exact node3 _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)
  have ct3 : L.curTime s3 = L.curTime s1 := by
    unfold LawfulStore.curTime LawfulStore.nodeA
    rw [eN]
    exact node3 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME])
  have prio3 : L.mem s3 (prioA (L.curW s1)) = L.mem s1 (prioA (L.curW s1)) := by
    rw [prioA_eq]; exact fld3 _ hcT _ (by simp) (by simp)
  have aff3 : L.mem s3 (affA (L.curW s1)) = L.mem s1 (affA (L.curW s1)) := by
    unfold affA; exact fld3 _ hcT _ (by simp) (by simp)
  have sc3 : L.mem s3 (scA (L.curW s1)) = L.mem s1 (scA (L.curW s1)) := by
    rw [scA_eq]; exact fld3 _ hcT _ (by simp) (by simp)
  have hp1 := h1.prio _ hcT
  have rq3 : L.mem s3 (L.nodeAt s1 (L.cpu s1) (rqOff (L.mem s1 (prioA (L.curW s1))))) =
      L.mem s1 (L.nodeAt s1 (L.cpu s1) (rqOff (L.mem s1 (prioA (L.curW s1))))) :=
    node3 _ (by rw [rqOff_val hp1]; omega) (by rw [rqOff_val hp1]; omega) (by rw [rqOff_val hp1]; omega)
  have rt3 : L.mem s3 (L.nodeAt s1 (L.cpu s1) (rqTailOff (L.mem s1 (prioA (L.curW s1))))) =
      L.mem s1 (L.nodeAt s1 (L.cpu s1) (rqTailOff (L.mem s1 (prioA (L.curW s1))))) :=
    node3 _ (by rw [rqTailOff_val hp1]; omega) (by rw [rqTailOff_val hp1]; omega) (by rw [rqTailOff_val hp1]; omega)
  -- the head refill at `s3`
  have hbO : Outside (L.nodeAt s1 (L.cpu s1) layout.node.CONSUMED) (L.cscW s1) (Z (L.cscW s1)) :=
    node_outside_sc hN1 hcC h1.omega (hX1.1.scW _ hcS) (by rw [hco]; omega) (by rw [hco])
  have ow := rr_wr_out (v := 0#u64) hW2 aC hbO
  rw [← e3'] at ow
  obtain ⟨ow1, ow2, ow3⟩ := ow
  have eh3 : L.rhead s3 (L.cscW s1) = L.rhead s1 (L.cscW s1) := ow1.trans hd2
  have er3 : L.refill s3 (L.cscW s1) (L.rhead s3 (L.cscW s1)) =
      ({ L.refill s1 (L.cscW s1) (L.rhead s1 (L.cscW s1)) with
        amount := core.num.U64.wrapping_add (L.refill s1 (L.cscW s1) (L.rhead s1 (L.cscW s1))).amount
          (L.refill s1 (L.cscW s1) (L.rtail s1 (L.cscW s1))).amount } : sporadic.Refill) := by
    calc L.refill s3 (L.cscW s1) (L.rhead s3 (L.cscW s1))
        = L.refill s3 (L.cscW s1) (L.rhead s2 (L.cscW s1)) := by rw [ow1]
      _ = L.refill s2 (L.cscW s1) (L.rhead s2 (L.cscW s1)) := ow3
      _ = L.refill s2 (L.cscW s1) (L.rhead s1 (L.cscW s1)) := by rw [hd2]
      _ = _ := hr2
  -- the queue facts at `s3`
  have hcT3 : L.curW s3 ∈ T := by rw [cur3]; exact hcT
  obtain ⟨qp, qrel, qtail⟩ := rr_queue h3 hcT3
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s3 (L.cpu s3) o) := fun o h1 h2 => by
    rw [eN]; exact (nRW o h1 h2).1
  have nW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → W (L.nodeAt s3 (L.cpu s3) o) := fun o h1 h2 => by
    rw [eN]; exact (nRW o h1 h2).2
  have qp3 : (L.mem s3 (prioA (L.curW s3))).val < 256 := qp
  exact
    { hT := hT
      hN := h3.nodes _ h3.cur
      ct := hcT3
      prio := qp
      aff := by rw [cur3, aff3, c3]; exact haff
      rel := qrel
      tail := qtail
      rr := by
        rw [eq_of_spec_fd (sporadic.is_round_robin.spec (L := L) _ _), csc3, ow2, hp2]
        simp [hper]
      rd := by
        rw [csc3]
        refine sporadic.ready_of ?_
        rw [er3, ct3]
        exact htime
      sf := by
        rw [csc3]
        refine rr_sufficient hm ?_
        rw [er3]
        exact hle
      act := by rw [act3]; exact hact
      rCS := nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      rCT := nR _ (by rw [curth_val]; omega) (by rw [curth_val])
      rPer := by rw [csc3]; exact rPer
      rS := by rw [cur3]; exact rS
      rC := by rw [cur3]; exact rC
      rM := by rw [cur3, sc3]; exact rM
      vt := by rw [cur3]; exact vt
      hd := by
        unfold PathObl.RdHead
        rw [csc3, eh3]
        exact hd
      rNow := nR _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      rI := by rw [cur3]; exact rI
      wI := by rw [cur3]; exact wI
      rA := by rw [cur3]; exact rA
      rD := by rw [cur3]; exact rD
      rP := by rw [cur3]; exact rP
      rH := nR _ (by rw [rqOff_val qp3]; omega) (by rw [rqOff_val qp3]; omega)
      wH := nW _ (by rw [rqOff_val qp3]; omega) (by rw [rqOff_val qp3]; omega)
      rE := nR _ (by rw [rqTailOff_val qp3]; omega) (by rw [rqTailOff_val qp3]; omega)
      wE := nW _ (by rw [rqTailOff_val qp3]; omega) (by rw [rqTailOff_val qp3]; omega)
      bR := ⟨nR _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]), fun inv hinv =>
        nR _ (by simp; omega) (by simp)⟩
      bW1 := nW _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])
      bW2 := fun inv hinv => nW _ (by simp; omega) (by simp)
      wN := by rw [cur3]; exact wN
      wP := by rw [cur3]; exact wP
      wEn := by
        rw [eN, eN, cur3, prio3, rq3, rt3]
        exact wEn }

end main

end Fl4Proofs.P2
