/-
# P2 (line lvm, gen 9): **a declined `local_vm_timer_irq` on the guarded store** (`hD` of gen 8)

* **`vtimer_decG`**: from a state with P1's invariant (`BXI`), a declined run of `handle_vm_timer_irq_local` is the
  same run on any store `gS` answering as `st` the reads of `IrqRd`, the two kernel-global domain words, the IRQ's
  state word, the earliest armed thread's `TmWords` (what `plan_objects` reads), the bound VCPU's `PENDING`, the
  bound notification's `TAIL_STATE`, and a declined `fire_ok` (premise `gfire`, in the form `fire_rdG` proves), and
  writing `update_timestamp`'s two node words as `st` (`IrqDec`). The walk is `vexit_decG`'s (the VM checks) joined
  to `irq_dec_guard`'s (the timer checks, the timestamp, `release_due`, `sufficient`, `timer_due`,
  `round_robin_ok`, `fire_ok`), carrying the real run's values step by step (`tr_bind_same` / `tr_ite`). An
  accepted `ok1` cannot end in a decline (the tail then returns `true`).
* **`vtimer_dec_own`**: under `ownV`, on `guard st (VexitRS …) (IrqDec …)` from `VtmEnt`: `IrqRd` by `vexit_rd`
  (`VexitEnt.curAff` / `cscCore`, no `current_vm_ok` needed), the domain words by `VexitEnt.ksv`, the state word by
  `VtmEnt.iq`, `TmWords` by `tmw_ownV`, `PENDING` by `pending_rd`, `TAIL_STATE` by `ntfn_tail_rd`, and `fire_ok`
  by `fire_rdG` with `R = VexitRS` (each word it reads lies in a typed region, so `rpV` lifts `own`'s permission;
  `CUR_DOMAIN` by `ksv`).

Premises: `vtimer_decG` none. `vtimer_dec_own`: `VtmEnt` (`P2/AccessLvmTo.lean`), and `hNt` (P1's notifications
`Nt` are notifications of its heap `H`; `fun _ h => h` at the canonical instantiation `Nt = H.ntfns`, as
`irq_dec_guard` / `fire_rd`'s).
-/
import Fl4Proofs.P2.AccessLvmTo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (guard ScAcc rhA tmA RdHead NodeSt tr_bind tr_bind_same tr_ite)
open Fl4Proofs.P2.OwnMapV (KLayoutV ownV RegionOKV rpermV_of_own)

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 32000000 in
/-- **A declined VM-timer run on the guarded store** (module docstring). -/
theorem vtimer_decG {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq n : U64} {p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (gRd : ∀ w, Aligned w → IrqRd st Z s w → R w)
    (hD1 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hIq : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hTm : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 → ∀ w, Aligned w →
      TmWords st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) w → R w)
    (gfire : ∀ (s1 : S) (tip : localtimer.TimerIrqPlan), L.ksb s1 = L.ksb s → L.cpu s1 = L.cpu s →
      (∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b) →
      localtimer.plan_objects st s = ok tip → localtimer.same_plan tip p = ok true → ∀ (ct now : U64),
      localtimer.fire_ok gS s1 (L.cpu s) ct p now = localtimer.fire_ok st s1 (L.cpu s) ct p now)
    (hRp : vOf st s ≠ 0#u64 → R (core.num.U64.wrapping_add (vOf st s) vcpu.PENDING))
    (hRn : ∀ n', L.mem s (boundA (L.curW s)) = n' → n' ≠ 0#u64 →
      R (core.num.U64.wrapping_add n' layout.ntfn.TAIL_STATE))
    (hW1 : W (ctA (L := L) s)) (hW2 : W (cnA (L := L) s))
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (false, s', a')) :
    localvm.handle_vm_timer_irq_local gS ar s a irq p n = ok (false, s', a') := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  have hX := hI.2.2.1
  have hS := hI.2.2.2.2
  have hO := hX.1
  have hcs : L.cscW s ∈ Scs := hX.2.2.cur
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := scq_of hO hS hcs
  have hmaxΩ : maxA (L.cscW s) ∈ Ω := hcq.2.1 _ hcq.2.2.2.2 hcq.2.2.2.1
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gRd _ (nodeAt_aligned hN h1 h2) (Or.inl ⟨o, h1, h2, rfl⟩)
  have cR : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      K.val ≠ 3496 → K.val ≠ 3504 → R (core.num.U64.wrapping_add (L.curW s) K) := fun K h1 h2 h3 h4 h5 h6 =>
    gRd _ (field_aligned ht' h2 h3) (Or.inr (Or.inl ⟨K, h1, h2, h3, h4, h5, h6, rfl⟩))
  have scR : ∀ b, InSC (L.cscW s) (Z (L.cscW s)) b → Aligned b → R b := fun b hb ha =>
    gRd _ ha (Or.inr (Or.inr (Or.inl hb)))
  have hSc : ScAcc R (fun _ => True) (L.cscW s) (Z (L.cscW s)) :=
    ⟨fun b ha hb => scR b hb ha, fun _ _ _ => trivial, trivial⟩
  have rSt : R (stA (L.curW s)) := by rw [stA_eq]; exact cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rSc : R (scA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rIq : R (inqA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rYt : R (yieldA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rAf : R (affA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rDm : R (domA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rVc : R (core.num.U64.wrapping_add (L.curW s) 3664#u64) :=
    cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rBn : R (core.num.U64.wrapping_add (L.curW s) 3368#u64) :=
    cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rMx : R (maxA (L.cscW s)) := scR _ hcq.2.2.2.1 hcq.2.2.2.2
  have rCore : R (scCoreA (L.cscW s)) := by
    obtain ⟨hP, hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
    have hcv : layout.sc.CORE.val = 16 := by simp [layout.sc.CORE]
    exact scR _ ⟨by unfold scCoreA; rw [hv]; omega, by unfold scCoreA; rw [hv, hcv]; omega⟩
      (by unfold Aligned scCoreA; rw [hv, hcv]; omega)
  -- the earliest armed thread (what `plan_objects` reads)
  have tmF : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ∈ T ∧
      (∀ K : U64, (K.val = 3520 ∨ K.val = 3528 ∨ K.val = 3568 ∨ K.val = 3368) →
        R (core.num.U64.wrapping_add (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) K)) ∧
      (TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) →
        (∀ K : U64, (K.val = 3328 ∨ K.val = 3336 ∨ K.val = 3360) →
          R (core.num.U64.wrapping_add (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) K)) ∧
        (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64 →
          R (core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
            layout.ntfn.TAIL_STATE) ∧
          R (core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
            layout.ntfn.BOUND_TCB))) := by
    intro hne
    have tR := hTm hne
    have q1 := (tmin_facts (BXI.blk hI) hcC hne).1
    refine ⟨q1, fun K hK => tR _ (field_aligned (hT _ q1) (by omega) (by omega)) (Or.inl ⟨K, hK, rfl⟩),
      fun hh => ⟨fun K hK => tR _ (field_aligned (hT _ q1) (by omega) (by omega))
        (Or.inr ⟨hh, Or.inl ⟨K, hK, rfl⟩⟩), fun hb => ?_⟩⟩
    have hn := hX.2.2.bnd _ q1 hb
    obtain ⟨p1, p2⟩ := hO.ntP _ hn
    have al : ∀ K : U64, K.val < 64 → K.val % 8 = 0 →
        Aligned (core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) K) :=
      fun K h1 h2 => by unfold Aligned; rw [ntfn_word_val p1 p2 h1]; omega
    exact ⟨tR _ (al _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]))
        (Or.inr ⟨hh, Or.inr ⟨hb, Or.inl rfl⟩⟩),
      tR _ (al _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB]))
        (Or.inr ⟨hh, Or.inr ⟨hb, Or.inr rfl⟩⟩)⟩
  have gtip : localtimer.plan_objects gS s = localtimer.plan_objects st s :=
    plan_objects.guard (gS := gS) (nR _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
      (fun hne =>
        { aff := (tmF hne).2.1 3520#u64 (by simp)
          ht := (tmF hne).2.1 3568#u64 (by simp)
          bn := (tmF hne).2.1 3368#u64 (by simp)
          here := fun hh => by
            obtain ⟨H1, H2⟩ := (tmF hne).2.2 hh
            refine ⟨?_, H1 3336#u64 (by simp), H1 3360#u64 (by simp), fun n en hn => ?_⟩
            · have := H1 3328#u64 (by simp)
              rw [← stA_eq] at this
              exact this
            · rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en
              have e := ok_inj_ff en
              subst e
              exact H2 hn })
  have hcsc : sched.cur_sc st s = ok (L.cscW s) := eq_of_spec_fd (sched.cur_sc.spec (L := L) s)
  -- the head
  revert h
  rw [vtimer_eq, vtimer_eq]
  unfold vtimerHead
  rw [PathObl.gst_cur_cpu (g := gS), L.cur_cpu_eq]
  simp only [bind_ok]
  rw [num_domains_ne_one_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine tr_bind_same (fun mx emx => ?_)
  refine tr_ite (fun _ h => h) (fun hle => ?_)
  have hirq : irq.val ≤ 127 := by
    rw [eq_of_spec_fd layout.irq.MAX.spec] at emx
    have e := ok_inj_ff emx
    subst e
    scalar_tac
  obtain ⟨i, hi⟩ : ∃ i, interrupt.state_off irq = ok i := by
    unfold interrupt.state_off
    simp only [lift, bind_ok]
    rw [eq_of_spec_fd layout.ks.IRQ_STATE.spec]
    simp only [bind_ok]
    exact ⟨_, rfl⟩
  rw [interrupt.irq_state.guard (gS := gS) s irq hi (hIq (by omega) i hi)]
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [gtip]
  refine tr_bind_same (fun tip etip => ?_)
  refine tr_bind_same (fun b eb => ?_)
  refine tr_ite (fun hb => ?_) (fun _ h => h)
  subst hb
  rw [PathObl.sched.cur_thread.guard (gS := gS) s (nR _ (by rw [curth_val]; omega) (by rw [curth_val])),
    cur_thread_ok, PathObl.sched.cur_sc.guard (gS := gS) s (nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])),
    hcsc]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.state.guard (gS := gS) _ s rSt]
  refine tr_bind_same (fun i2 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [PathObl.obj.Tcb.bound_ntfn.guard (gS := gS) _ s rBn]
  refine tr_bind_same (fun i3 ei3 => ?_)
  refine tr_ite (fun _ h => h) (fun hb2 => ?_)
  have hn3 : i3 = n := by
    by_contra hne; exact hb2 (bne_iff_ne.mpr hne)
  have hbn := ei3
  rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at hbn
  have hbn' : L.mem s (boundA (L.curW s)) = n := (ok_inj_ff hbn).trans hn3
  rw [ntfn_quiet.guard (gS := gS) s n (hRn n hbn')]
  refine tr_bind_same (fun b1 _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [vm_running.guard (gS := gS) s _ rVc (fun hv => hRp hv)]
  refine tr_bind_same (fun b2 _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [current_vm_ok.guard (gS := gS) s _ _ _ rAf rYt rSc rCore
    (nR _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])) rDm hD1]
  refine tr_bind_same (fun b3 eb3 => ?_)
  refine tr_ite (fun hb3 => ?_) (fun _ h => h)
  subst hb3
  obtain ⟨-, -, hsct, -⟩ := current_vm_ok_true eb3
  rw [sched_quiet.guard (gS := gS) s (nR _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
    hD2 (nR _ (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]))]
  refine tr_bind_same (fun b4 eb4 => ?_)
  refine tr_ite (fun hb4 => ?_) (fun _ h => h)
  subst hb4
  -- the tail
  have hact0 : L.actionW s = sched.ACTION_RESUME_CURRENT := sq_true eb4
  have hsc0 : L.mem s (scA (L.curW s)) ≠ 0#u64 := hI.2.1.resume (hact0.trans resume_val)
  have hAc : L.cscW s ∈ Ac := by
    rw [← hsct]
    exact hI.2.1.sact _ hcT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hact0.trans resume_val, rfl⟩))))) hsc0
  have hmx0 : L.rmax s (L.cscW s) ≠ 0#u64 := (hS.act _ hcs).1 hAc
  unfold vtimerTail
  rw [PathObl.sched.update_timestamp.guard (gS := gS) ar s a
    (nR _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])) hW1
    (nR _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])) hW2]
  refine tr_bind_same (fun q eu => ?_)
  obtain ⟨s1, a1⟩ := q
  try simp only [uncurry_apply_pair]
  -- `s → s1`: the timestamp update
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
  simp only at er
  have k1 : L.ksb s1 = L.ksb s := by rw [er, utW_ksb]
  have c1 : L.cpu s1 = L.cpu s := by rw [er, utW_cpu]
  have m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b :=
    fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2
  have e1N : ∀ o, L.nodeAt s1 (L.cpu s1) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c1, nodeAt_of_ksb k1]
  have hnode1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 →
      L.mem s1 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h40 h48
    refine m1 _ (nodeAt_aligned hN ho h8) (fun e => ?_) (fun e => ?_)
    · have e' := congrArg UScalar.val e
      unfold ctA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CUR_TIME])] at e'
      simp [layout.node.CUR_TIME] at e'; omega
    · have e' := congrArg UScalar.val e
      unfold cnA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CONSUMED])] at e'
      simp [layout.node.CONSUMED] at e'; omega
  have htcb1 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y K hy hK h8
    exact m1 _ (field_aligned (hT y hy) hK h8) (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CUR_TIME]))
      (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CONSUMED]))
  have hout1 : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b := fun b hb =>
    m1 b hb.1 (fun e => out_ne_node hb hcC hN (by simp [layout.node.CUR_TIME]) (congrArg UScalar.val e).symm)
      (fun e => out_ne_node hb hcC hN (by simp [layout.node.CONSUMED]) (congrArg UScalar.val e).symm)
  have agΩ1 : ∀ b ∈ Ω, L.mem s1 b = L.mem s b := fun b hb => hout1 b (h0.omega b hb)
  have ndR : ∀ (Y : S), (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → ∀ o : U64, o.val < 4288 →
      o.val % 8 = 0 → R (L.nodeAt Y (L.cpu Y) o) := fun Y e o h1 h2 => by rw [e]; exact nR o h1 h2
  have scK1 : ∀ y ∈ T, L.mem s1 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact htcb1 hy (by simp) (by simp)
  have wf1 : RefillsWF st s1 (L.cscW s) (Z (L.cscW s)) :=
    (SCq.agree hcq agΩ1).1 (by unfold LawfulStore.rmax; rw [agΩ1 _ hmaxΩ]; exact hmx0)
  rw [PathObl.sched.cur_time.guard (gS := gS) s1
    (ndR s1 e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))]
  refine tr_bind_same (fun now enow => ?_)
  have grdue : localtimer.release_due gS s1 (L.cpu s) = localtimer.release_due st s1 (L.cpu s) := by
    have := release_due.guard (gS := gS) s1
      (ndR s1 e1N _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
      (fun hne => by
        have e : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.RELEASE_HEAD) =
            L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := by
          rw [e1N]
          exact hnode1 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
            (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
        rw [e] at hne ⊢
        obtain ⟨r1, -, -, r4, r5⟩ := rel_facts hI hne
        have hqr := scq_of hO hS r4
        rw [scK1 _ r1]
        refine ⟨gRd _ ?_ (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl rfl⟩)))), ?_⟩
        · rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp)
        · exact PathObl.ScAcc.head (W := fun _ => True)
            ⟨fun b ha hb => gRd _ ha (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr hb⟩)))), fun _ _ _ => trivial,
              trivial⟩
            ((SCq.agree hqr agΩ1).1 (by
              unfold LawfulStore.rmax; rw [agΩ1 _ (hqr.2.1 _ hqr.2.2.2.2 hqr.2.2.2.1)]; exact r5)))
      (ndR s1 e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    rwa [c1] at this
  rw [grdue]
  refine tr_bind_same (fun b5 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [PathObl.sched.consumed.guard (gS := gS) s1
    (ndR s1 e1N _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
  refine tr_bind_same (fun i4 _ => ?_)
  rw [PathObl.sporadic.sufficient.guard (gS := gS) ar s1 a1 (L.cscW s) i4 (hSc.head wf1)]
  refine tr_bind_same (fun b6 _ => ?_)
  have tm1e : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    rw [e1N]
    exact hnode1 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have gtdue : localtimer.timer_due gS s1 (L.cpu s) now = localtimer.timer_due st s1 (L.cpu s) now := by
    have := timer_due.guard (gS := gS) s1 now
      (ndR s1 e1N _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])) (fun hne => by
        rw [tm1e] at hne ⊢
        exact (tmF hne).2.1 3528#u64 (by simp))
    rwa [c1] at this
  rw [gtdue]
  refine tr_bind_same (fun due _ => ?_)
  have grr : localtimer.round_robin_ok gS ar s1 a1 (L.cpu s) (L.curW s) (L.cscW s) now =
      localtimer.round_robin_ok st ar s1 a1 (L.cpu s) (L.curW s) (L.cscW s) now := by
    have := round_robin_ok.guard (gS := gS) ar (s := s1) a1 (ct := L.curW s) (csc := L.cscW s) (now := now)
      (ndR s1 e1N _ (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]))
      (hSc.off wf1 _ (by simp [layout.sc.PERIOD]) (by simp [layout.sc.PERIOD]))
      rSt rSc (by rw [scK1 _ hcT, hsct]; exact rMx) rIq
      (hSc.off wf1 _ (by simp [layout.sc.REFILL_HEAD]) (by simp [layout.sc.REFILL_HEAD]))
      (hSc.off wf1 _ (by simp [layout.sc.REFILL_TAIL]) (by simp [layout.sc.REFILL_TAIL]))
      ⟨(hSc.rt wf1 wf1.head_lt).1, (hSc.rt wf1 wf1.head_lt).2.2.1⟩
      ⟨(hSc.rt wf1 wf1.tail_lt).1, (hSc.rt wf1 wf1.tail_lt).2.2.1⟩
      (ndR s1 e1N _ (by simp [layout.node.L1_BITMAP]) (by simp [layout.node.L1_BITMAP]))
      (by rw [k1]; exact hD1)
      ⟨ndR s1 e1N _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]), fun inv hinv =>
        ndR s1 e1N _ (by simp; omega) (by simp)⟩
      (cR 3448#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
    rwa [c1] at this
  have gfire1 : localtimer.fire_ok gS s1 (L.cpu s) (L.curW s) p now =
      localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now :=
    gfire s1 tip k1 c1 m1 etip eb (L.curW s) now
  refine tr_bind (fun ok1 e1 _ => ?_) (fun ok1 _ hk => ?_)
  · cases b6 <;> cases due
    · simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at e1 ⊢
      rw [grr]; exact e1
    · simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at e1 ⊢
      exact e1
    · simp only [Bool.false_eq_true, not_true_eq_false, ↓reduceIte] at e1 ⊢
      exact e1
    · simp only [Bool.false_eq_true, not_true_eq_false, ↓reduceIte] at e1 ⊢
      rw [gfire1]; exact e1
  · cases ok1
    · rw [if_neg Bool.false_ne_true] at hk ⊢; exact hk
    · exfalso
      rw [if_pos rfl] at hk
      obtain ⟨⟨s2, a2⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      obtain ⟨⟨x3, s3, a3⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      try dsimp only at hk
      obtain ⟨⟨s4, a4⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      obtain ⟨⟨s5, a5⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      have e := ok_inj_ff hk
      simp at e

end main

section own
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {A : Type} (ar : machine.Arch A) {lk : S → U64 → Prop}

/-- **A declined `local_vm_timer_irq` under `ownV`** (module docstring): `hD` of `vtimer_localPath`. -/
theorem vtimer_dec_own (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s s' : S} {a a' : A} {irq n : U64} {p : localtimer.TimerIrqPlan}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s)
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (false, s', a')) :
    localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (IrqDec st s)) ar s a irq p n =
      ok (false, s', a') := by
  have E := hE.ent
  have hI := E.inv
  have hL := E.lay
  have rD : VexitRS K st lk s (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) :=
    ⟨hL.domA, Or.inr (rpermV_of_own E.ksv.1 (rperm_none hL.dom _))⟩
  exact vtimer_decG (gS := guard st (VexitRS K st lk s) (IrqDec st s)) (R := VexitRS K st lk s)
    (W := IrqDec st s) ar hA hI
    (fun w ha hw => ⟨ha, Or.inr (vexit_rd hK hI hL E.ntw E.cs E.aff E.curAff E.cscCore hw)⟩)
    rD
    ⟨hL.dtmA, Or.inr (rpermV_of_own E.ksv.2 (rperm_none hL.dtm _))⟩
    (fun hb i hi => ⟨(hE.iq hb i hi).1,
      Or.inr (rpermV_of_own (hE.iq hb i hi).2.2 (rperm_none (hE.iq hb i hi).2.1 _))⟩)
    (fun hne w ha hw => ⟨ha, Or.inr (tmw_ownV hK hI hL E.ntw hne hw)⟩)
    (fun s1 tip k1 c1 m1 etip esp ct now =>
      fire_rdG hK.base hI hL E.ntw (lk := lk s) (fun w hp ha hr => ⟨ha, Or.inr (rpV hK hr hp)⟩) rD hNt k1 c1 m1
        etip esp ct now)
    (fun hv0 => ⟨(E.vfar hv0).1.1, Or.inr (pending_rd hK (E.vin hv0) (E.vlk hv0))⟩)
    (fun n' hbn hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL E.ntw E.curAff hn
      exact ⟨q1, Or.inr q2⟩)
    (Or.inl rfl) (Or.inr rfl) h

end own

end Fl4Proofs.P2
