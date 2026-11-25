/-
# P2: a declined timer interrupt local path on the guarded store

* `may_run_here.guardC` / `current_ok.guardC`: `may_run_here` and `current_ok` on any store answering `R` reads as
  `st`, with the thread's words after its `AFFINITY` (and the SC words) in `R` only once `AFFINITY` is the core
  (`may_run_here` declines first otherwise), as `plan_objects.guard`'s `TmHere` split.
* `IrqDec`: the words a declined run writes (`update_timestamp`'s node `CUR_TIME` / `CONSUMED`).
* `irq_dec_guard`: at an entry state with P1's invariant and the layout facts, a declined run of
  `localtimer.handle_timer_irq_local` is the same run on `guard st (MaxR …) (IrqDec …)`, walking each decline point:
  the IRQ range / state (`IrqLay.iq`), the plan (`plan_objects.guard`, `TmWords` readable by `tmw_own`), the current
  thread (`current_ok.guardC`: its `AFFINITY` the gate's, the rest its home core's once homed here), `sched_quiet`,
  the timestamp (`IrqDec`), `release_due`, the budget / due checks and `round_robin_ok` (after `current_ok`, every
  read is `IrqRd`'s, readable by `irq_rd_own`). The fire case is a premise (`hFd`, as `irq_acc_own`'s `hF`).

Premises: `StLay` [J], `IrqLay` [J], `hAff` [J] (p2j `AffSc`), `hFd` (the fire case, p2j's line: `fire_ok` reads
the plan's notification head and its waiters' words, which a lock owns; discharging it needs the glue premise
that the plan's objects (`p.objects`) are among the locks held, `PlanLk` [P] of p2j's glue).
-/
import Fl4Proofs.P2.FootTimerIrqOwn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (guard RPerm WPerm HeldBy GateOnly ScAcc rhA RdHead tr_bind tr_bind_same tr_ite
  bind_guard_congr)

section g
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R]

/-- **`may_run_here` on the guarded store**, the words after `AFFINITY` read only once it is `cpu`. -/
theorem may_run_here.guardC (s : S) (cpu t : U64) (h1 : R (affA t))
    (h : L.mem s (affA t) = cpu → R (stA t) ∧ R (yieldA t) ∧ R (core.num.U64.wrapping_add t 3664#u64) ∧
      R (scA t) ∧ (L.mem s (scA t) ≠ 0#u64 → R (scCoreA (L.mem s (scA t))))) :
    localtimer.may_run_here gS s cpu t = localtimer.may_run_here st s cpu t := by
  unfold localtimer.may_run_here
  refine bind_guard_congr rfl fun b _ => ?_
  by_cases hb : b = true
  · rw [if_pos hb, if_pos hb]
  rw [if_neg hb, if_neg hb, PathObl.obj.Tcb.affinity.guard t s h1]
  refine bind_guard_congr rfl fun i ei => ?_
  by_cases hi : i = cpu
  swap
  · rw [if_neg hi, if_neg hi]
  rw [aff_ok] at ei
  obtain ⟨h2, h3, h4, h5, h6⟩ := h ((ok_inj_ff ei).trans hi)
  rw [if_pos hi, if_pos hi, PathObl.obj.Tcb.state.guard t s h2, PathObl.obj.Tcb.yield_to.guard t s h3,
    vcpu.bound.guardT s t h4, PathObl.obj.Tcb.sc.guard t s h5, eq_of_spec_fd (obj.Tcb.sc.spec s t)]
  simp only [bind_ok]
  by_cases h0 : L.mem s (scA t) = 0#u64
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0, PathObl.obj.Sc.cpu.guard _ s (h6 h0)]

/-- **`current_ok` on the guarded store**, the current thread's words after `AFFINITY` read only once it is
`cpu`. -/
theorem current_ok.guardC (s : S) (cpu ct csc : U64) (h1 : R (affA ct))
    (h : L.mem s (affA ct) = cpu → R (stA ct) ∧ R (yieldA ct) ∧ R (core.num.U64.wrapping_add ct 3664#u64) ∧
      R (scA ct) ∧ (L.mem s (scA ct) ≠ 0#u64 → R (scCoreA (L.mem s (scA ct)))) ∧ R (scCoreA csc) ∧
      R (L.nodeAt s (L.cpu s) layout.node.IDLE_THREAD) ∧ R (domA ct) ∧
      R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN)) :
    localtimer.current_ok gS s cpu ct csc = localtimer.current_ok st s cpu ct csc := by
  unfold localtimer.current_ok
  rw [may_run_here.guardC s cpu ct h1 (fun ha => by
    obtain ⟨a2, a3, a4, a5, a6, -⟩ := h ha
    exact ⟨a2, a3, a4, a5, a6⟩)]
  refine bind_guard_congr rfl fun b eb => ?_
  cases b
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  obtain ⟨-, haff, -, -⟩ := may_run_here_true eb
  obtain ⟨-, -, -, a5, -, a7, a8, a9, a10⟩ := h haff
  rw [if_pos rfl, if_pos rfl, PathObl.obj.Tcb.sc.guard ct s a5, PathObl.obj.Sc.cpu.guard csc s a7,
    PathObl.sched.idle_thread.guard s a8, PathObl.obj.Tcb.domain.guard ct s a9, PathObl.sched.cur_domain.guard s a10]

end g

section dec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {A : Type} (ar : machine.Arch A)

/-- The words a declined timer interrupt writes: `update_timestamp`'s node `CUR_TIME` and `CONSUMED`. -/
def IrqDec (st : machine.Store S) [L : LawfulStore st] (s : S) (w : U64) : Prop :=
  w = ctA (L := L) s ∨ w = cnA (L := L) s

set_option maxHeartbeats 32000000 in
/-- **A declined timer interrupt on the guarded store** (module docstring). -/
theorem irq_dec_guard (hA : P0.ArchTotal ar) (hK : RegionOK K) {s s' : S} {a a' : A} {irq : U64}
    {p : localtimer.TimerIrqPlan} {lk : S → U64 → Prop}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s) (hY : IrqLay K st Nt irq s)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (hFd : IrqFire st ar s a → localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (IrqDec st s)) ar s a
      irq p = ok (false, s', a'))
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (false, s', a')) :
    localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (IrqDec st s)) ar s a irq p =
      ok (false, s', a') := by
  by_cases hfire : IrqFire st ar s a
  · exact hFd hfire
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  have hX := hI.2.2.1
  have hO := hX.1
  have hS := hI.2.2.2.2
  have hcs : L.cscW s ∈ Scs := hX.2.2.cur
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := scq_of hO hS hcs
  have hmaxΩ : maxA (L.cscW s) ∈ Ω := hcq.2.1 _ hcq.2.2.2.2 hcq.2.2.2.1
  set R : U64 → Prop := MaxR K st lk s with eR
  set W : U64 → Prop := IrqDec st s with eW
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    ⟨Or.inl (held_core (hL.own_node _ h1)), nodeAt_aligned hN h1 h2⟩
  have gateR : ∀ {x : U64} {k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → GateField k.val →
      R (core.num.U64.wrapping_add x k) := fun hx h1 h2 h8 hg =>
    ⟨Or.inr (by
      have e := hL.own_tcb hT (L.mem s) hx h1 h2
      unfold fld at e
      unfold GateOnly; rw [e, tcbOwner, if_pos hg]), field_aligned (hT _ hx) h2 h8⟩
  have homeR : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) →
      k.val ≠ 3496 → k.val ≠ 3504 → L.mem s (affA (L.curW s)) = L.cpu s →
      R (core.num.U64.wrapping_add (L.curW s) k) := fun k h1 h2 h3 h4 h5 h6 ha => by
    refine ⟨?_, field_aligned ht' h2 h3⟩
    have e := hL.own_tcb hT (L.mem s) hcT h1 h2
    unfold fld at e
    unfold RPerm GateOnly
    rw [e]
    unfold tcbOwner
    by_cases hga : GateField k.val
    · rw [if_pos hga]; exact Or.inr rfl
    · rw [if_neg hga, if_neg (show ¬ TimerField k.val by unfold TimerField; omega),
        if_neg (show ¬ GField k.val by unfold GField; omega)]
      exact Or.inl ha
  have coreR : ∀ {q : U64}, q ∈ Scs → R (scCoreA q) := @fun q hq => by
    obtain ⟨hP, hz⟩ := hO.sc _ hq
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
    have hcv : layout.sc.CORE.val = 16 := by simp [layout.sc.CORE]
    have hin : InSC q (Z q) (scCoreA q) :=
      ⟨by unfold scCoreA; rw [hv]; omega, by unfold scCoreA; rw [hv, hcv]; omega⟩
    have e : own K (L.mem s) (scCoreA q) = .gate := by
      simp only [own, hL.sc q hq _ hin]
      rw [if_pos (by unfold scCoreA; rw [hv, hcv])]
    exact ⟨Or.inr e, by unfold Aligned scCoreA; rw [hv, hcv]; omega⟩
  have rD1 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) := ⟨rperm_none hL.dom _, hL.domA⟩
  have rD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME) := ⟨rperm_none hL.dtm _, hL.dtmA⟩
  have rAff : R (affA (L.curW s)) := gateR hcT (by simp) (by simp) (by simp) (Or.inl (by simp))
  -- the earliest armed thread (no `current_ok` needed)
  have tR : ∀ w, L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 → Aligned w →
      TmWords st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) w → R w :=
    fun w hne ha hw => ⟨tmw_own hK hI hL hY hne hw, ha⟩
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
    have q1 := (tmin_facts (BXI.blk hI) hcC hne).1
    refine ⟨q1, fun K hK => tR _ hne (field_aligned (hT _ q1) (by omega) (by omega)) (Or.inl ⟨K, hK, rfl⟩),
      fun hh => ⟨fun K hK => tR _ hne (field_aligned (hT _ q1) (by omega) (by omega))
        (Or.inr ⟨hh, Or.inl ⟨K, hK, rfl⟩⟩), fun hb => ?_⟩⟩
    have hn := hX.2.2.bnd _ q1 hb
    obtain ⟨p1, p2⟩ := hO.ntP _ hn
    have al : ∀ K : U64, K.val < 64 → K.val % 8 = 0 →
        Aligned (core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) K) :=
      fun K h1 h2 => by unfold Aligned; rw [ntfn_word_val p1 p2 h1]; omega
    exact ⟨tR _ hne (al _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]))
        (Or.inr ⟨hh, Or.inr ⟨hb, Or.inl rfl⟩⟩),
      tR _ hne (al _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB]))
        (Or.inr ⟨hh, Or.inr ⟨hb, Or.inr rfl⟩⟩)⟩
  have gtip : localtimer.plan_objects (guard st R W) s = localtimer.plan_objects st s :=
    plan_objects.guard (gS := guard st R W) (nR _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
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
  -- the walk
  revert h
  unfold localtimer.handle_timer_irq_local
  rw [PathObl.guard_cur_cpu, L.cur_cpu_eq]
  simp only [bind_ok, lift]
  rw [num_domains_ne_one_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine tr_bind_same (fun mx emx => ?_)
  refine tr_ite (fun _ h => h) (fun hle => ?_)
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
  rw [interrupt.irq_state.guard (gS := guard st R W) s irq hi ⟨rperm_none (hY.iq i hi).2 _, (hY.iq i hi).1⟩]
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [gtip]
  refine tr_bind_same (fun tip _ => ?_)
  refine tr_bind_same (fun b _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [PathObl.sched.cur_thread.guard (gS := guard st R W) s (nR _ (by rw [curth_val]; omega) (by rw [curth_val])),
    cur_thread_ok]
  simp only [bind_ok]
  rw [PathObl.sched.cur_sc.guard (gS := guard st R W) s (nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
  refine tr_bind_same (fun csc ecsc => ?_)
  have ecsc' : L.cscW s = csc := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at ecsc; exact ok_inj_ff ecsc
  subst ecsc'
  rw [current_ok.guardC (gS := guard st R W) s (L.cpu s) (L.curW s) (L.cscW s) rAff (fun ha =>
    ⟨by rw [stA_eq]; exact homeR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) ha,
      homeR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) ha,
      homeR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) ha,
      homeR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) ha,
      fun h0' => coreR (hX.2.2.bound _ hcT h0').1, coreR hcs,
      nR _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]),
      homeR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) ha, rD1⟩)]
  refine tr_bind_same (fun b1 eb1 => ?_)
  refine tr_ite (fun hb1 => ?_) (fun _ h => h)
  subst hb1
  -- past `current_ok`: every read is `IrqRd`'s
  obtain ⟨hmr, hsct, hcore⟩ := current_ok_true eb1
  obtain ⟨-, haff, -, -⟩ := may_run_here_true hmr
  have hok : IrqOk st s := ⟨haff, hsct, hcore⟩
  have gRd : ∀ w, Aligned w → IrqRd st Z s w → R w := fun w ha hw => ⟨irq_rd_own hK hI hL hY hAff hok hw, ha⟩
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
  have rMx : R (maxA (L.cscW s)) := scR _ hcq.2.2.2.1 hcq.2.2.2.2
  rw [sched_quiet.guard (gS := guard st R W) s (nR _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
    rD2 (nR _ (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]))]
  refine tr_bind_same (fun b2 eb2 => ?_)
  refine tr_ite (fun hb2 => ?_) (fun _ h => h)
  subst hb2
  have hact0 : L.actionW s = sched.ACTION_RESUME_CURRENT := sq_true eb2
  have hsc0 : L.mem s (scA (L.curW s)) ≠ 0#u64 := hI.2.1.resume (hact0.trans resume_val)
  have hAc : L.cscW s ∈ Ac := by
    rw [← hsct]
    exact hI.2.1.sact _ hcT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hact0.trans resume_val, rfl⟩))))) hsc0
  have hmx0 : L.rmax s (L.cscW s) ≠ 0#u64 := (hS.act _ hcs).1 hAc
  rw [PathObl.sched.update_timestamp.guard (gS := guard st R W) ar s a
    (nR _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])) (Or.inl rfl)
    (nR _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])) (Or.inr rfl)]
  refine tr_bind_same (fun q eu => ?_)
  obtain ⟨s1, a1⟩ := q
  simp only [uncurry_apply_pair]
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
  rw [PathObl.sched.cur_time.guard (gS := guard st R W) s1
    (ndR s1 e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))]
  refine tr_bind_same (fun now enow => ?_)
  -- the release head at `s1`
  have grdue : localtimer.release_due (guard st R W) s1 (L.cpu s) = localtimer.release_due st s1 (L.cpu s) := by
    have := release_due.guard (gS := guard st R W) s1
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
  refine tr_bind_same (fun b3 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [PathObl.sched.consumed.guard (gS := guard st R W) s1
    (ndR s1 e1N _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
  refine tr_bind_same (fun i2 ei2 => ?_)
  rw [PathObl.sporadic.sufficient.guard (gS := guard st R W) ar s1 a1 (L.cscW s) i2 (hSc.head wf1)]
  refine tr_bind_same (fun b4 eb4 => ?_)
  have tm1e : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    rw [e1N]
    exact hnode1 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have gtdue : localtimer.timer_due (guard st R W) s1 (L.cpu s) now = localtimer.timer_due st s1 (L.cpu s) now := by
    have := timer_due.guard (gS := guard st R W) s1 now
      (ndR s1 e1N _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])) (fun hne => by
        rw [tm1e] at hne ⊢
        exact (tmF hne).2.1 3528#u64 (by simp))
    rwa [c1] at this
  rw [gtdue]
  refine tr_bind_same (fun due edue => ?_)
  have grr : localtimer.round_robin_ok (guard st R W) ar s1 a1 (L.cpu s) (L.curW s) (L.cscW s) now =
      localtimer.round_robin_ok st ar s1 a1 (L.cpu s) (L.curW s) (L.cscW s) now := by
    have := round_robin_ok.guard (gS := guard st R W) ar (s := s1) a1 (ct := L.curW s) (csc := L.cscW s) (now := now)
      (ndR s1 e1N _ (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]))
      (hSc.off wf1 _ (by simp [layout.sc.PERIOD]) (by simp [layout.sc.PERIOD]))
      rSt rSc (by rw [scK1 _ hcT, hsct]; exact rMx) rIq
      (hSc.off wf1 _ (by simp [layout.sc.REFILL_HEAD]) (by simp [layout.sc.REFILL_HEAD]))
      (hSc.off wf1 _ (by simp [layout.sc.REFILL_TAIL]) (by simp [layout.sc.REFILL_TAIL]))
      ⟨(hSc.rt wf1 wf1.head_lt).1, (hSc.rt wf1 wf1.head_lt).2.2.1⟩
      ⟨(hSc.rt wf1 wf1.tail_lt).1, (hSc.rt wf1 wf1.tail_lt).2.2.1⟩
      (ndR s1 e1N _ (by simp [layout.node.L1_BITMAP]) (by simp [layout.node.L1_BITMAP]))
      (by rw [k1]; exact rD1)
      ⟨ndR s1 e1N _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]), fun inv hinv =>
        ndR s1 e1N _ (by simp; omega) (by simp)⟩
      (cR 3448#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
    rwa [c1] at this
  refine tr_bind (fun ok1 e1 _ => ?_) (fun ok1 _ hk => ?_)
  · cases b4 <;> cases due
    · simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at e1 ⊢
      rw [grr]; exact e1
    · simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at e1 ⊢
      exact e1
    · simp only [Bool.false_eq_true, not_true_eq_false, ↓reduceIte] at e1 ⊢
      exact e1
    · exact absurd (fun s1' a1' now' i2' b4' due' eu' enow' ei2' eb4' edue' => by
        rw [eu] at eu'
        have e := ok_inj_ff eu'
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rw [enow] at enow'
        obtain rfl := ok_inj_ff enow'
        rw [ei2] at ei2'
        obtain rfl := ok_inj_ff ei2'
        rw [eb4] at eb4'
        rw [edue] at edue'
        exact ⟨(ok_inj_ff eb4').symm, (ok_inj_ff edue').symm⟩) hfire
  · cases ok1
    · rw [if_neg Bool.false_ne_true] at hk ⊢; exact hk
    · exfalso
      rw [if_pos rfl] at hk
      obtain ⟨⟨x2, s2, a2⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      try dsimp only at hk
      obtain ⟨⟨s3, a3⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      obtain ⟨⟨s4, a4⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      obtain ⟨⟨s5, a5⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      obtain ⟨t, -, hk⟩ := bind_eq_ok hk
      obtain ⟨⟨s6, a6⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      have e := ok_inj_ff hk
      simp at e

end dec

end Fl4Proofs.P2
