/-
P3 (DESIGN.md §9), scheduling contexts: **`charge_budget` with
`can_timeout_fault = true` when no timeout fault can be raised** (toward
KENTRY-PLAN items 10 and 7: `check_budget`'s charge, the preemption point's
schedulable branch).

`end_timeslice` raises a timeout fault only for a current thread whose
timeout-handler slot holds an endpoint cap (FL4 `valid_timeout_handler`,
spec `isValidTimeoutHandler`). Without one, both sides take the same path as
with `can_timeout_fault = false`:

* `end_timeslice_noTmo` (FL4) / `endTimeslice_noTmo` (spec): the two
  `end_timeslice`s are equal at a state where the handler is not valid.
* `charge_budget_noTmo` (SchedRel level): from `charge_budget_refinesF`'s
  premises, FL4's `charge_budget used true` equals `charge_budget used false`
  and the spec's `chargeBudget used true` equals `chargeBudget used false` (the
  handler slot is kept by the head, `TmoKeep`; the TCB by `HeadKeeps`).
* `JAtZ.chargeBudgetNJ`: ScChargeJ's `JAtZ.chargeBudgetJ` for
  `can_timeout_fault = true` when the current thread has no endpoint cap as
  its timeout handler. The other case (the current thread's own timeout-fault
  send at the state after the head charge) is KENTRY-PLAN kp2/kp3 (a).
-/
import Fl4Proofs.P3.ScChargeJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **`endTimeslice` without a valid timeout handler** does not depend on
`canTimeout`. -/
theorem endTimeslice_noTmo {σ : State Unit} {x : SchedContext} {n : Nat} {xt : Tcb}
    (hk : σ.kheap σ.curSc = some (.schedContext x n)) (hkt : σ.kheap σ.curThread = some (.tcb xt))
    (hv : isEpCap xt.tcbTimeoutHandler = false) :
    endTimeslice (Z := Unit) true σ = endTimeslice false σ := by
  unfold endTimeslice
  simp only [nd_gets_bind, nd_bind_one (isRoundRobin_eq hk), nd_bind_one (getThreadState_eq hkt)]
  by_cases hvm : xt.tcbState = .runningVM
  · simp only [hvm, ↓reduceIte, nd_pure_bind', Bool.false_eq_true, and_false]
  · simp only [hvm, ↓reduceIte, nd_bind_one (Endp.isValidTimeoutHandler_eq hkt), hv, Bool.false_eq_true,
      and_false]

/-- **`chargeBudget` without a valid timeout handler** does not depend on
`canTimeout` (the head keeps the current thread's TCB). -/
theorem chargeBudget_noTmo {σ σ2 : State Unit} (u : Ticks) (h2 : chargeHead u σ = ({((), σ2)}, False))
    (hK : HeadKeeps σ σ2 σ.curSc) {x : SchedContext} {n : Nat}
    (hk : σ.kheap σ.curSc = some (.schedContext x n)) {xt : Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xt))
    (hne : σ.curThread ≠ σ.curSc) (hv : isEpCap xt.tcbTimeoutHandler = false) :
    chargeBudget (Z := Unit) u true σ = chargeBudget u false σ := by
  obtain ⟨hcs, hcc, -, -, -, -, -, -, hfr, hsk⟩ := hK
  obtain ⟨y, hy, -, -⟩ := hsk x n hk
  rw [chargeBudget_eq, chargeBudget_eq, nd_bind_one h2, nd_bind_one h2, chargeTail_eq true σ2 rfl,
    chargeTail_eq false σ2 rfl]
  split_ifs
  · refine nd_bind_congr ?_
    refine endTimeslice_noTmo (σ := { σ2 with consumedTime := 0 }) (x := y) (n := n) (xt := xt) ?_ ?_ hv
    · show σ2.kheap σ2.curSc = _
      rw [hcs]; exact hy
    · show σ2.kheap σ2.curThread = _
      rw [hcc, hfr _ hne]; exact hkt
  · rfl

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

theorem bind_congr_spec {α β : Type} {m : Result α} {P : α → Prop} (hm : m ⦃ P ⦄) {f g : α → Result β}
    (h : ∀ x, P x → f x = g x) : m >>= f = m >>= g := by
  obtain ⟨v, hv, hP⟩ := spec_exists hm
  rw [hv]
  simp only [Bind.bind, bind_ok]
  exact h v hP

/-- **FL4's `end_timeslice` without a valid timeout handler** does not depend
on `can_timeout_fault`. -/
theorem end_timeslice_noTmo (s : S) (a : A) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hv : faults.valid_timeout_handler st s ct = ok false) :
    sched.end_timeslice st ar s a true = sched.end_timeslice st ar s a false := by
  obtain ⟨sc, hsc, -⟩ := spec_exists (sched.cur_sc.spec' (L := L) s)
  obtain ⟨rr, hrr, -⟩ := spec_exists (sporadic.is_round_robin.spec (L := L) s sc)
  obtain ⟨i, hi, -⟩ := spec_exists (Notif.obj.Tcb.state.spec (L := L) s ct)
  have hg : (if i != sched.TS_RUNNING_VM then faults.valid_timeout_handler st s ct else ok false) = ok false := by
    split
    · exact hv
    · rfl
  unfold sched.end_timeslice
  rw [hsc, hct]
  simp only [bind_ok]
  rw [hrr, hi]
  simp only [bind_ok]
  rw [hg]
  simp only [bind_ok, ↓reduceIte, Bool.false_eq_true, ite_self]

/-- **`charge_budget` with `can_timeout_fault = true` and no valid timeout
handler** is `charge_budget` with `can_timeout_fault = false`, on both sides
(module docstring; `charge_budget_refinesF`'s premises). -/
theorem charge_budget_noTmo {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hscC : nodeW st s c layout.node.CUR_SC ∈ C)
    (htw : L.mem s (scW (nodeW st s c layout.node.CUR_SC) 24#u64) = nodeW st s c layout.node.CUR_THREAD)
    (hidle : (nodeW st s c layout.node.IDLE_SC).bv = σ.idleSc)
    (hact : (nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc → ∀ x n,
      σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) → Fl4Spec.scActive x = true)
    (hnr : (nodeW st s c layout.node.CUR_THREAD).bv ∉ σ.releaseQueue)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hval : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' →
      TmoKeep st (nodeW st s c layout.node.CUR_THREAD) s σ s' σ' →
      faults.valid_timeout_handler st s' (nodeW st s c layout.node.CUR_THREAD) ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv σ' =
          ({(b, σ')}, False) ⦄)
    (hnt : ∀ xt, σ.kheap (nodeW st s c layout.node.CUR_THREAD).bv = some (.tcb xt) →
      Fl4Spec.isEpCap xt.tcbTimeoutHandler = false)
    (used : U64) :
    sched.charge_budget st ar s a used true = sched.charge_budget st ar s a used false ∧
      Fl4Spec.chargeBudget (Z := Unit) used.bv true σ = Fl4Spec.chargeBudget used.bv false σ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  set sc := nodeW st s c layout.node.CUR_SC with hscd
  set ct := nodeW st s c layout.node.CUR_THREAD with hctd
  have hct : ct ∈ T := hc.curT
  obtain ⟨xt, hkt, -⟩ := hs.tcb ct hct
  obtain ⟨x, n, hk, -⟩ := hs.scs sc hscC
  have hcts : ct.bv ≠ sc.bv := fun e => by rw [e, hk] at hkt; cases hkt
  have hb : decide (sc ≠ nodeW st s c layout.node.IDLE_SC) = decide (sc.bv ≠ σ.idleSc) := by
    rw [← hidle]
    apply decide_eq_decide.2
    exact ⟨fun h e => h (eq_of_bv e), fun h e => h (by rw [e])⟩
  have H := charge_head_refinesK s a σ hS hR hN hI hscC htw hact hnr hmrt hmb used _ hb
  obtain ⟨-, -, σ2, h2, -, -, -, -, hK2, -, -⟩ := spec_exists H
  refine ⟨?_, ?_⟩
  · obtain ⟨v1, hv1, ev1⟩ := spec_exists (sched.cur_sc.spec' (L := L) s)
    obtain ⟨v2, hv2, ev2⟩ := spec_exists (sched.idle_sc.spec' (L := L) s)
    rw [hc.cur] at ev1 ev2
    subst ev1 ev2
    unfold sched.charge_budget
    rw [hv1, hv2]
    simp only [bind_ok]
    rw [sc_ne_eq]
    simp only [bind_ok]
    refine bind_congr_spec H ?_
    rintro s2 ⟨σ2', -, hS2, -, -, -, hK, hTK, -⟩
    obtain ⟨-, hcc, -, -, -, -, -, -, hfr, -⟩ := hK
    have hc2 := hS2.lists.choose_spec.choose_spec.1.cur
    obtain ⟨s3, hs3e, hs3⟩ := spec_exists (sched.set_consumed.spec' (L := L) s2 0#u64)
    rw [hc2] at hs3
    subst hs3
    rw [hs3e]
    simp only [bind_ok]
    obtain ⟨hS3, -, -⟩ := hS2.set_node_consumed 0#u64
    have e1 : nodeW st (L.wr s2 (L.nodeAt s2 c layout.node.CONSUMED) 0#u64) c layout.node.CUR_THREAD = ct :=
      eq_of_bv (by rw [← hS3.lists.choose_spec.choose_spec.2.curThread]; exact hcc.trans hs.curThread)
    have hc3 := hS3.lists.choose_spec.choose_spec.1.cur
    obtain ⟨v3, hv3, ev3⟩ := spec_exists (sched.cur_thread.spec' (L := L) (L.wr s2 (L.nodeAt s2 c layout.node.CONSUMED) 0#u64))
    rw [hc3, e1] at ev3
    subst ev3
    rw [hv3]
    simp only [bind_ok]
    -- the handler is not valid at the state after the head
    have hK3 : TmoKeep st ct s σ (L.wr s2 (L.nodeAt s2 c layout.node.CONSUMED) 0#u64)
        { σ2' with consumedTime := (0#u64).bv } :=
      hTK.trans (TmoKeep.node_wr hS2 hct (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) 0#u64 rfl)
    obtain ⟨b, hbe, hbs⟩ := spec_exists (hval _ _ hS3 hK3)
    have hkt3 : ({ σ2' with consumedTime := (0#u64).bv } : Fl4Spec.State Unit).kheap ct.bv = some (.tcb xt) := by
      show σ2'.kheap ct.bv = _
      rw [hfr _ hcts]; exact hkt
    have hb3 : b = false := by
      have e := (Prod.mk.inj ((Endp.isValidTimeoutHandler_eq hkt3).symm.trans hbs)).1
      have e' := Set.singleton_eq_singleton_iff.1 e
      rw [← hnt xt hkt]; exact (Prod.mk.inj e').1.symm
    subst hb3
    refine bind_congr_spec (sched.is_schedulable.spec' (L := L) _ ct) ?_
    intro b1 _
    cases b1
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]
      rw [end_timeslice_noTmo _ a hv3 hbe]
  · have ecs : σ.curSc = sc.bv := hs.curSc
    have ecc : σ.curThread = ct.bv := hs.curThread
    refine chargeBudget_noTmo used.bv h2 (by rw [ecs]; exact hK2) (by rw [ecs]; exact hk) (by rw [ecc]; exact hkt)
      (by rw [ecs, ecc]; exact hcts) (hnt xt hkt)

end

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **`charge_budget` with `can_timeout_fault = true` at `J`, when the current
thread has no endpoint cap as its timeout handler** (module docstring):
`JAtZ.chargeBudgetJ` through `charge_budget_noTmo`. -/
theorem JAtZ.chargeBudgetNJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hnsw : σ.schedulerAction ≠ .switchThread σ.curThread)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hnt : ∀ xt, σ.kheap σ.curThread = some (.tcb xt) → Fl4Spec.isEpCap xt.tcbTimeoutHandler = false)
    (used : U64) :
    sched.charge_budget st arI s a used true ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.chargeBudget (Z := Unit) used.bv true σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.1 a σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, htw, -, hact, hnr, -⟩ := CurInv.facts hS J.inv hC
  have hct : nodeW st s Z.c layout.node.CUR_THREAD ∈ Z.T := hc.curT
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hthc : Z.th (nodeW st s Z.c layout.node.CUR_THREAD) = some .tcb := (hJ.tcb _).2 (J.zH.1 _ hct)
  have hval : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st Z.N Z.T Z.C Z.c s' σ' →
      TmoKeep st (nodeW st s Z.c layout.node.CUR_THREAD) s σ s' σ' →
      faults.valid_timeout_handler st s' (nodeW st s Z.c layout.node.CUR_THREAD) ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s Z.c layout.node.CUR_THREAD).bv σ' =
          ({(b, σ')}, False) ⦄ :=
    fun s' σ' _ hK => hval_of_rel J.xtop.rel.1 J.xtop.rel.2.1.1 hthc s' σ' hK
  obtain ⟨e1, e2⟩ := charge_budget_noTmo (ar := arI) s a σ hS hR J.nsc J.inv hscC htw hS.idle hact hnr hmrt hmb
    hval (fun xt hx => hnt xt (by rw [hs.curThread]; exact hx)) used
  rw [e1]
  refine WP.spec_mono (J.chargeBudgetJ hAT hC hni hnsw hmrt hmb used) ?_
  rintro r ⟨h1, σ', h2, h3⟩
  exact ⟨h1, σ', by rw [e2]; exact h2, h3⟩

end

end

end Fl4Proofs.P3
