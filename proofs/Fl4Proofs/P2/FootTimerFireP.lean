/-
# P2 (p2lf): an accepted timer interrupt, fire case, on the guarded store: the prefix

`irq_accG_fire_pre`: from a state with the P1 invariant (`BXI`), an accepted run of
`localtimer.handle_timer_irq_local` in the fire case (`IrqFire`: the budget sufficient and a timer due after
`update_timestamp`) is the same run on any store `gS` answering the reads of `IrqRd` and the writes of `IrqWr` as
`st` (`PathObl.GRd` / `PathObl.GWr`), given the fire case's own calls on `gS` at the real states: `fire_ok` at the
state after `update_timestamp` (`gfo`), and the tail (`gT`: `schedule` at the state after `handle_interrupt`, then
`activate_thread`, `cur_thread` and `vcpu.check` at the states they run in). Everything before the tail (the
checks, `update_timestamp`, `check_budget` with a sufficient budget, `handle_interrupt` of the timer IRQ) is
discharged as in `irq_accG_quiet_walk`.

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqLP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard ScAcc rhA tmA RdHead NodeSt)

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

/-- The fire case's tail on `gS` at the real states: `schedule` after `handle_interrupt`, `activate_thread`,
`cur_thread` and `vcpu.check`. -/
def FireTailG (st gS : machine.Store S) (ar : machine.Arch A) (s3 : S) (a3 : A) : Prop :=
  sched.schedule gS ar s3 a3 = sched.schedule st ar s3 a3 ∧
    ∀ s4 a4, sched.schedule st ar s3 a3 = ok (s4, a4) →
      sched.activate_thread gS ar s4 a4 = sched.activate_thread st ar s4 a4 ∧
      ∀ s5 a5, sched.activate_thread st ar s4 a4 = ok (s5, a5) →
        sched.cur_thread gS s5 = sched.cur_thread st s5 ∧
        ∀ t, sched.cur_thread st s5 = ok t → vcpu.check gS ar s5 a5 t = vcpu.check st ar s5 a5 t

set_option maxHeartbeats 32000000 in
/-- **The fire case of an accepted timer interrupt on the guarded store, the prefix discharged**, from
`irq_accept_walk`'s equations with `IrqCase.fire` (module docstring). -/
theorem irq_accG_fire_walk {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s1 s2 s3 s4 s5 s' : S} {a a1 a2 a3 a4 a5 a' : A}
    {cpu mx irq ct csc now i2 t : U64} {x : Bool} {tip p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRd st Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) → W w)
    (hIq : IrqOk st s → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (gfo : IrqOk st s → localtimer.fire_ok gS s1 (L.cpu s) (L.curW s) p now =
      localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now)
    (gT : IrqOk st s → FireTailG st gS ar s3 a3)
    (ecpu : st.cur_cpu s = ok cpu) (emx : layout.irq.MAX = ok mx)
    (hle : ¬ irq > mx) (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
    (etip : localtimer.plan_objects st s = ok tip) (eb : localtimer.same_plan tip p = ok true)
    (ect : sched.cur_thread st s = ok ct) (ecsc : sched.cur_sc st s = ok csc)
    (eok : localtimer.current_ok st s cpu ct csc = ok true) (eq : localtimer.sched_quiet st s cpu = ok true)
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) (enow : sched.cur_time st s1 = ok now)
    (erel : localtimer.release_due st s1 cpu = ok false) (ei2 : sched.consumed st s1 = ok i2)
    (eb4 : sporadic.sufficient st ar s1 a1 csc i2 = ok true)
    (edue : localtimer.timer_due st s1 cpu now = ok true)
    (efo : localtimer.fire_ok st s1 cpu ct p now = ok true)
    (ecb : sched.check_budget st ar s1 a1 = ok (x, s2, a2))
    (ehi : interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3))
    (esc : sched.schedule st ar s3 a3 = ok (s4, a4)) (eac : sched.activate_thread st ar s4 a4 = ok (s5, a5))
    (et : sched.cur_thread st s5 = ok t) (evc : vcpu.check st ar s5 a5 t = ok (s', a')) :
    localtimer.handle_timer_irq_local gS ar s a irq p = ok (true, s', a') := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  have ecpur := ecpu
  have ectr := ect
  have ecscr := ecsc
  have ecbr := ecb
  have etr := et
  have evcr := evc
  rw [L.cur_cpu_eq] at ecpu
  have hcpu : cpu = L.cpu s := (ok_inj_ff ecpu).symm
  subst hcpu
  rw [cur_thread_ok] at ect
  have etc : L.curW s = ct := ok_inj_ff ect
  subst etc
  rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at ecsc
  have ecs' : L.cscW s = csc := ok_inj_ff ecsc
  subst ecs'
  have ht' := hT _ hcT
  obtain ⟨hmr, hsct, hcore⟩ := current_ok_true eok
  obtain ⟨-, haff, -, -⟩ := may_run_here_true hmr
  -- the current SC
  have hX := hI.2.2.1
  have hS := hI.2.2.2.2
  have hO := hX.1
  have hcs : L.cscW s ∈ Scs := hX.2.2.cur
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := scq_of hO hS hcs
  have hact0 : L.actionW s = sched.ACTION_RESUME_CURRENT := sq_true eq
  have hsc0 : L.mem s (scA (L.curW s)) ≠ 0#u64 := hI.2.1.resume (hact0.trans resume_val)
  have hAc : L.cscW s ∈ Ac := by
    rw [← hsct]
    exact hI.2.1.sact _ hcT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hact0.trans resume_val, rfl⟩))))) hsc0
  have hmx0 : L.rmax s (L.cscW s) ≠ 0#u64 := (hS.act _ hcs).1 hAc
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
  have hout1 : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b := fun b hb =>
    m1 b hb.1 (fun e => out_ne_node hb hcC hN (by simp [layout.node.CUR_TIME]) (congrArg UScalar.val e).symm)
      (fun e => out_ne_node hb hcC hN (by simp [layout.node.CONSUMED]) (congrArg UScalar.val e).symm)
  have agΩ1 : ∀ b ∈ Ω, L.mem s1 b = L.mem s b := fun b hb => hout1 b (h0.omega b hb)
  have htcb1 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y K hy hK h8
    exact m1 _ (field_aligned (hT y hy) hK h8) (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CUR_TIME]))
      (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CONSUMED]))
  -- the IRQ's state word after the timestamp update
  have hirq : irq.val ≤ 127 := by
    rw [eq_of_spec_fd layout.irq.MAX.spec] at emx
    have e := ok_inj_ff emx
    subst e
    scalar_tac
  obtain ⟨i, hi, hiv⟩ : ∃ i, interrupt.state_off irq = ok i ∧ i.val = 224 + 8 * irq.val := by
    unfold interrupt.state_off
    simp only [lift, bind_ok]
    rw [eq_of_spec_fd layout.ks.IRQ_STATE.spec]
    simp only [bind_ok]
    refine ⟨_, rfl, ?_⟩
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits,
      UScalar.size]
    try omega
  have hi' : i.val < 13568 := by omega
  have hi8 : i.val % 8 = 0 := by omega
  have eis1 : interrupt.irq_state st s1 irq = ok interrupt.IRQ_TIMER := by
    rw [← ei1]
    unfold interrupt.irq_state
    rw [hi]
    simp only [bind_ok]
    rw [eq_of_spec_fd (obj.ks_get.spec (L := L) s1 i), eq_of_spec_fd (obj.ks_get.spec (L := L) s i), k1,
      m1 _ (ks_aligned hN hi' hi8) (ks_ne_node hN hi' (by simp [layout.node.CUR_TIME]))
        (ks_ne_node hN hi' (by simp [layout.node.CONSUMED]))]
  -- `check_budget`
  have ecs1 : sched.cur_sc st s1 = ok (L.cscW s) := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s1)]
    congr 1
    show L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_SC) = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_SC)
    rw [e1N]
    exact hnode1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  rw [check_budget_suf ar ecs1 ei2 eb4] at ecb
  have e2 := ok_inj_ff ecb
  simp only [Prod.mk.injEq] at e2
  obtain ⟨-, e2s, e2a⟩ := e2
  subst e2s e2a
  -- the guarded store: what it admits
  have hok : IrqOk st s := ⟨haff, hsct, hcore⟩
  obtain ⟨gsc, gT⟩ := gT hok
  obtain ⟨gac, gT⟩ := gT s4 a4 esc
  obtain ⟨gt, gT⟩ := gT s5 a5 eac
  have gvc := gT t et
  have gfo := gfo hok
  replace gRd := gRd hok
  replace gWr := gWr hok
  replace hIq := hIq hok i hi
  replace hD1 := hD1 hok
  replace hD2 := hD2 hok
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gRd _ (nodeAt_aligned hN h1 h2) (Or.inl ⟨o, h1, h2, rfl⟩)
  have nW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → W (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gWr _ (nodeAt_aligned hN h1 h2) (Or.inl ⟨o, h1, h2, rfl⟩) (fun e => by
      rw [stA_eq] at e; exact node_ne_field hN h1 hcT ht' (by simp) e)
  have cR : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      K.val ≠ 3496 → K.val ≠ 3504 → R (core.num.U64.wrapping_add (L.curW s) K) := fun K h1 h2 h3 h4 h5 h6 =>
    gRd _ (field_aligned ht' h2 h3) (Or.inr (Or.inl ⟨K, h1, h2, h3, h4, h5, h6, rfl⟩))
  have scR : ∀ b, InSC (L.cscW s) (Z (L.cscW s)) b → Aligned b → R b := fun b hb ha =>
    gRd _ ha (Or.inr (Or.inr (Or.inl hb)))
  have scNS : ∀ b, Aligned b → InSC (L.cscW s) (Z (L.cscW s)) b → b ≠ stA (L.curW s) := fun b ha hb e => by
    rw [stA_eq] at e
    exact out_ne_field (h0.omega b (hcq.2.1 b ha hb)) hcT ht' (by simp) (congrArg UScalar.val e).symm
  have hSc : ScAcc R W (L.cscW s) (Z (L.cscW s)) := ⟨fun b ha hb => scR b hb ha, fun b h1 h2 =>
    gWr _ h1 (Or.inr (Or.inr (Or.inl h2))) (scNS b h1 ⟨by have := h2.1; omega, h2.2⟩),
    gWr _ hcq.2.2.1.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (scNS _ hcq.2.2.1.2 hcq.2.2.1.1)⟩
  have rSt : R (stA (L.curW s)) := by rw [stA_eq]; exact cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rSc : R (scA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rYt : R (yieldA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rCore : R (scCoreA (L.cscW s)) := by
    obtain ⟨hP, hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
    have hcv : layout.sc.CORE.val = 16 := by simp [layout.sc.CORE]
    exact scR _ ⟨by unfold scCoreA; rw [hv]; omega, by unfold scCoreA; rw [hv, hcv]; omega⟩
      (by unfold Aligned scCoreA; rw [hv, hcv]; omega)
  have ndR : ∀ (Y : S), (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → ∀ o : U64, o.val < 4288 →
      o.val % 8 = 0 → R (L.nodeAt Y (L.cpu Y) o) := fun Y e o h1 h2 => by rw [e]; exact nR o h1 h2
  have hdC : ∀ Y : S, (∀ b ∈ Ω, L.mem Y b = L.mem s b) → RdHead (L := L) R Y (L.cscW s) := fun Y ag =>
    hSc.head ((SCq.agree hcq ag).1 (by
      have hmaxΩ : maxA (L.cscW s) ∈ Ω := hcq.2.1 _ hcq.2.2.2.2 hcq.2.2.2.1
      unfold LawfulStore.rmax; rw [ag _ hmaxΩ]; exact hmx0))
  -- the release head at `s1`
  have rhd1 : L.mem s1 (rhA (L := L) s1) ≠ 0#u64 → R (scA (L.mem s1 (rhA (L := L) s1))) ∧
      RdHead (L := L) R s1 (L.mem s1 (scA (L.mem s1 (rhA (L := L) s1)))) := by
    have e0 : L.mem s1 (rhA (L := L) s1) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := by
      show L.mem s1 (L.nodeAt s1 (L.cpu s1) _) = _
      rw [e1N]
      exact hnode1 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
        (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
    rw [e0]
    intro hne
    obtain ⟨r1, -, -, r4, r5⟩ := rel_facts hI hne
    have es : L.mem s1 (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) =
        L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) := by
      rw [scA_eq]; exact htcb1 r1 (by simp) (by simp)
    rw [es]
    have hqr := scq_of hO hS r4
    refine ⟨gRd _ ?_ (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl rfl⟩)))), ?_⟩
    · rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp)
    · refine PathObl.ScAcc.head (W := fun _ => True)
        ⟨fun b ha hb => gRd _ ha (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr hb⟩)))), fun _ _ _ => trivial,
          trivial⟩ ((SCq.agree hqr agΩ1).1 ?_)
      unfold LawfulStore.rmax
      rw [agΩ1 _ (hqr.2.1 _ hqr.2.2.2.2 hqr.2.2.2.1)]; exact r5
  -- the earliest timer
  have tmF : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
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
    have q1 := (tmin_facts (BXI.blk hI) hcC hne).1
    refine ⟨fun K hK => gRd _ (field_aligned (hT _ q1) (by omega) (by omega))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl ⟨K, hK, rfl⟩⟩))))), fun hh => ⟨fun K hK =>
        gRd _ (field_aligned (hT _ q1) (by omega) (by omega))
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr ⟨hh, Or.inl ⟨K, hK, rfl⟩⟩⟩))))), fun hb => ?_⟩⟩
    have hn := hX.2.2.bnd _ q1 hb
    obtain ⟨p1, p2⟩ := hO.ntP _ hn
    have al : ∀ K : U64, K.val < 64 → K.val % 8 = 0 →
        Aligned (core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) K) :=
      fun K h1 h2 => by unfold Aligned; rw [ntfn_word_val p1 p2 h1]; omega
    exact ⟨gRd _ (al _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]))
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr ⟨hh, Or.inr ⟨hb, Or.inl rfl⟩⟩⟩))))),
      gRd _ (al _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB]))
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr ⟨hh, Or.inr ⟨hb, Or.inr rfl⟩⟩⟩)))))⟩
  have tm1e : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    rw [e1N]
    exact hnode1 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  -- the guarded calls
  have gtip : localtimer.plan_objects gS s = localtimer.plan_objects st s :=
    plan_objects.guard (gS := gS) (nR _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
      (fun hne =>
        { aff := (tmF hne).1 3520#u64 (by simp)
          ht := (tmF hne).1 3568#u64 (by simp)
          bn := (tmF hne).1 3368#u64 (by simp)
          here := fun hh => by
            obtain ⟨H1, H2⟩ := (tmF hne).2 hh
            refine ⟨?_, H1 3336#u64 (by simp), H1 3360#u64 (by simp), fun n en hn => ?_⟩
            · have := H1 3328#u64 (by simp)
              rw [← stA_eq] at this
              exact this
            · rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en
              have e := ok_inj_ff en
              subst e
              exact H2 hn })
  have gcok : localtimer.current_ok gS s (L.cpu s) (L.curW s) (L.cscW s) =
      localtimer.current_ok st s (L.cpu s) (L.curW s) (L.cscW s) :=
    current_ok.guard s (L.cpu s) (L.curW s) (L.cscW s) (cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)) rSt rYt
      (cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)) rSc (by rw [hsct]; exact rCore) rCore
      (nR _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]))
      (cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)) hD1
  have gquiet : localtimer.sched_quiet gS s (L.cpu s) = localtimer.sched_quiet st s (L.cpu s) :=
    sched_quiet.guard s (nR _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])) hD2
      (nR _ (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]))
  have gtdue : localtimer.timer_due gS s1 (L.cpu s) now = localtimer.timer_due st s1 (L.cpu s) now := by
    have := timer_due.guard (gS := gS) s1 now
      (ndR s1 e1N _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])) (fun hne => by
        rw [tm1e] at hne ⊢
        exact (tmF hne).1 3528#u64 (by simp))
    rwa [c1] at this
  have grdue : localtimer.release_due gS s1 (L.cpu s) = localtimer.release_due st s1 (L.cpu s) := by
    have := release_due.guard (gS := gS) s1
      (ndR s1 e1N _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
      rhd1
      (ndR s1 e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    rwa [c1] at this
  have gcb : sched.check_budget gS ar s1 a1 = sched.check_budget st ar s1 a1 :=
    sched.check_budget.guard_suf ar s1 a1
      (ndR s1 e1N _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
      (ndR s1 e1N _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
      (fun sc e => by
        rw [ecs1] at e
        rw [← ok_inj_ff e]
        exact hdC s1 agΩ1)
      (fun sc c e1 e2 => by
        rw [ecs1] at e1
        rw [ei2] at e2
        rw [← ok_inj_ff e1, ← ok_inj_ff e2]
        exact eb4)
  have ghi : interrupt.handle_interrupt gS ar s1 a1 irq = interrupt.handle_interrupt st ar s1 a1 irq :=
    interrupt.handle_interrupt.guard_timer ar s1 a1 irq eis1
      (interrupt.irq_state.guard s1 irq hi (by rw [k1]; exact hIq))
      (by rw [e1N]; exact nW _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
      (fun s2'' e => by
        rw [eq_of_spec_fd (obj.node_set.spec (L := L) s1 _ _ _)] at e
        rw [← ok_inj_ff e, nodeAt_of_ksb (L.ksb_wr _ _ _), c1, nodeAt_of_ksb k1]
        exact nW _ (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED]))
  exact irq_replay (st := st) (st' := gS) ar ecpur ‹PathObl.GRd gS st R›.cur_cpu emx hle ei1
    (interrupt.irq_state.guard s irq hi hIq) rfl etip gtip eb ectr
    (PathObl.sched.cur_thread.guard s (nR _ (by rw [curth_val]; omega) (by rw [curth_val]))) ecscr
    (PathObl.sched.cur_sc.guard s (nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))) eok gcok
    eq gquiet eu
    (PathObl.sched.update_timestamp.guard ar s a
      (nR _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (nW _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (nR _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
      (nW _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])))
    enow (PathObl.sched.cur_time.guard s1 (ndR s1 e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])))
    erel grdue ei2
    (PathObl.sched.consumed.guard s1 (ndR s1 e1N _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])))
    eb4 (PathObl.sporadic.sufficient.guard ar s1 a1 (L.cscW s) i2 (hdC s1 agΩ1)) edue gtdue
    (IrqCase.fire rfl rfl efo) (fun h => nomatch h) (fun _ => gfo) ecbr gcb ehi ghi esc gsc eac gac etr gt evcr gvc

/-- **An accepted fire-case timer interrupt on the guarded store, the prefix discharged** (module docstring):
`fire_ok` and the tail on `gS` at the real states (`gfo`, `gT`), stated through the run's own equations. -/
theorem irq_accG_fire_pre {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hq : IrqFire st ar s a)
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRd st Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) → W w)
    (hIq : IrqOk st s → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (gfo : IrqOk st s → ∀ s1 a1 now, sched.update_timestamp st ar s a = ok (s1, a1) →
      sched.cur_time st s1 = ok now →
      localtimer.fire_ok gS s1 (L.cpu s) (L.curW s) p now = localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now)
    (gT : IrqOk st s → ∀ s1 a1 x s2 a2 s3 a3 now, sched.update_timestamp st ar s a = ok (s1, a1) →
      sched.cur_time st s1 = ok now → localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now = ok true →
      sched.check_budget st ar s1 a1 = ok (x, s2, a2) →
      interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3) → FireTailG st gS ar s3 a3)
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    localtimer.handle_timer_irq_local gS ar s a irq p = ok (true, s', a') := by
  obtain ⟨cpu, mx, i1, ct, csc, now, i2, tip, b4, due, x, s1, s2, s3, s4, s5, a1, a2, a3, a4, a5, t, ecpu, emx,
    hle, ei1, hi1, etip, eb, ect, ecsc, eok, eq, eu, enow, erel, ei2, eb4, edue, hc, ecb, ehi, esc, eac, et,
    evc⟩ := irq_accept_walk ar h
  subst hi1
  have ecp : cpu = L.cpu s := by
    have e := ecpu
    rw [L.cur_cpu_eq] at e; exact (ok_inj_ff e).symm
  have ecs : csc = L.cscW s := by
    have e := ecsc
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at e; exact (ok_inj_ff e).symm
  have ect' : ct = L.curW s := by
    have e := ect
    rw [cur_thread_ok] at e; exact (ok_inj_ff e).symm
  obtain ⟨rfl, rfl⟩ := hq s1 a1 now i2 b4 due eu enow ei2 (by rw [← ecs]; exact eb4) (by rw [← ecp]; exact edue)
  have efo : localtimer.fire_ok st s1 cpu ct p now = ok true := by
    cases hc with
    | quiet _ hd => exact absurd hd (by decide)
    | fire _ _ hf => exact hf
    | rr h4 _ _ => exact absurd h4 (by decide)
  subst ecp ect'
  exact irq_accG_fire_walk ar hA hI gRd gWr hIq hD1 hD2 (fun hok => gfo hok s1 a1 now eu enow)
    (fun hok => gT hok s1 a1 x s2 a2 s3 a3 now eu enow efo ecb ehi) ecpu emx hle ei1 etip eb ect ecsc eok eq eu enow erel
    ei2 eb4 edue efo ecb ehi esc eac et evc

end main

end Fl4Proofs.P2
