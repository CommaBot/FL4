/-
# P2: an accepted timer interrupt, round-robin case, on the guarded store (`PathObl.acc`)

`irq_accG_rr`: from a state with the P1 invariant (`BXI`), an accepted run of `localtimer.handle_timer_irq_local`
whose budget check fails, finds no timer due and whose `round_robin_ok` accepts (`IrqRR`) is the same run on any
store `gS` answering the reads of `IrqRd` and the writes of `IrqWr` as `st` (as `irq_accG_quiet`), given also the
reads of `set_vm_root` of the current thread beyond its slot words: the kernel root word (`hKr`) and the ASID table
and pools (`hTab`), with P1's `AsidOff` (`hAs`) so that the round-robin writes keep the table.

The walk: `rr_s3` (the `schedule` state), `schedule_choose_eq` and `rr_choose` (the switch back to the current
thread at `Xc`), `schedTail_fp` at `Xc`, then `activate_thread` and `vcpu::check` as in the quiet case. The guards:
`round_robin_ok.guard`, `check_budget.guard_rr` with `charge_budget.guard_rrC` (`F` = `rr_tail_F`; the current
thread's ready queue is empty at `s1`, by the bitmap and `round_robin_ok`'s priority test), `handle_interrupt`
at the state after `check_budget`, `schedule.guard_choose` (choose path: `schedule_choose_new_thread.guard`,
`choose_thread.guard_ne`, `switch_to_thread.guard`, `dequeue.guard_single`; `schedRes.guard` with
`resume_hsw_hfr` at `Xc`), and `irq_replay` with `IrqCase.rr`.

Named premises: `hAs` [J] (P1 `AsidOff`: the ASID table and pool words are `Ω` words outside the SC frame `Sg`,
as `AccessFastRR`'s).
-/
import Fl4Proofs.P2.FootTimerIrqRSt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard ScAcc rhA tmA RdHead NodeSt)

/-! ## The round-robin case selected -/

section sets
variable {S : Type}

/-- The round-robin case selected at the entry state: after `update_timestamp` the budget is insufficient and no
timer is due. -/
def IrqRR (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (s : S) (a : A) : Prop :=
  ∀ s1 a1 now i2 b4 due, sched.update_timestamp st ar s a = ok (s1, a1) → sched.cur_time st s1 = ok now →
    sched.consumed st s1 = ok i2 → sporadic.sufficient st ar s1 a1 (L.cscW s) i2 = ok b4 →
    localtimer.timer_due st s1 (L.cpu s) now = ok due → b4 = false ∧ due = false

end sets

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 64000000 in
/-- **The round-robin case of an accepted timer interrupt on the guarded store**, from `irq_accept_walk`'s
equations with `IrqCase.rr` (module docstring). -/
theorem irq_accG_rr_walk {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s1 s2 s3 s4 s5 s' : S} {a a1 a2 a3 a4 a5 a' : A}
    {cpu mx irq ct csc now i2 t : U64} {x : Bool} {tip p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRd st Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) → W w)
    (hIq : IrqOk st s → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : IrqOk st s → ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART → L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hKr : IrqOk st s → R (krA (L := L) s)) (hTab : IrqOk st s → PathObl.RdTab (L := L) R s)
    (hAs : AsidOff (L := L) Ω Sg s)
    (ecpu : st.cur_cpu s = ok cpu) (emx : layout.irq.MAX = ok mx)
    (hle : ¬ irq > mx) (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
    (etip : localtimer.plan_objects st s = ok tip) (eb : localtimer.same_plan tip p = ok true)
    (ect : sched.cur_thread st s = ok ct) (ecsc : sched.cur_sc st s = ok csc)
    (eok : localtimer.current_ok st s cpu ct csc = ok true) (eq : localtimer.sched_quiet st s cpu = ok true)
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) (enow : sched.cur_time st s1 = ok now)
    (erel : localtimer.release_due st s1 cpu = ok false) (ei2 : sched.consumed st s1 = ok i2)
    (eb4 : sporadic.sufficient st ar s1 a1 csc i2 = ok false)
    (edue : localtimer.timer_due st s1 cpu now = ok false)
    (hrr : localtimer.round_robin_ok st ar s1 a1 cpu ct csc now = ok true)
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
  obtain ⟨-, haff, hnvm, -⟩ := may_run_here_true hmr
  have hy0 : L.mem s (yieldA (L.curW s)) = 0#u64 := mrh_yield hmr
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
  have hmaxΩ : maxA (L.cscW s) ∈ Ω := hcq.2.1 _ hcq.2.2.2.2 hcq.2.2.2.1
  -- `s → s1`: the timestamp update
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
  simp only at er
  have k1 : L.ksb s1 = L.ksb s := by rw [er, utW_ksb]
  have c1 : L.cpu s1 = L.cpu s := by rw [er, utW_cpu]
  have m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b :=
    fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [er]; exact utW_placed hN n1
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
  have esc0 := esc
  -- `s1`: the round-robin facts
  have cur1 : L.curW s1 = L.curW s := by
    unfold LawfulStore.curW
    rw [e1N]
    exact hnode1 _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
      (by rw [curth_val]; omega)
  have hcs1 : L.cscW s1 = L.cscW s := by
    have e := ecs1
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s1)] at e
    exact ok_inj_ff e
  have hnow : L.curTime s1 = now := by
    rw [cur_time_ok] at enow; exact ok_inj_ff enow
  have hB1 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 :=
    (irq_quiet_schedule ar (s3 := s1) (a3 := a1) hA hI eq eu enow erel edue (WritesIn.refl s1 _)).1
  have hact1 : L.actionW s1 = sched.ACTION_RESUME_CURRENT := by rw [action_ut ar hA hN eu]; exact hact0
  have haff1 : L.mem s1 (affA (L.curW s1)) = L.cpu s1 := by
    rw [cur1, c1]; unfold affA; rw [htcb1 hcT (K := 3520#u64) (by simp) (by simp)]; exact haff
  have hsct1 : L.mem s1 (scA (L.curW s1)) = L.cscW s1 := by
    rw [cur1, hcs1, scA_eq, htcb1 hcT (K := 3464#u64) (by simp) (by simp), ← scA_eq]; exact hsct
  have hrr1 : localtimer.round_robin_ok st ar s1 a1 (L.cpu s1) (L.curW s1) (L.cscW s1) (L.curTime s1) =
      ok true := by
    rw [c1, cur1, hcs1, hnow]; exact hrr
  have hins : ∀ c, sched.consumed st s1 = ok c → sporadic.sufficient st ar s1 a1 (L.cscW s1) c = ok false := by
    intro c ec
    rw [ei2] at ec
    rw [← ok_inj_ff ec, hcs1]
    exact eb4
  obtain ⟨ha2, w13, hact3, hsch3, hq3, hhp3, hl13, hH3, hE3, hWF3, hT3, hR3, eis2, k2, c2⟩ :=
    rr_s3 ar hB1 hrr1 haff1 hsct1 (by rw [hcs1]; exact hAc) hact1 hins ecb hnow (by rw [c1]; exact erel)
      (by rw [c1]; exact edue) emx hle eis1 ehi
  subst a2
  have pr1 : L.mem s1 (prioA (L.curW s)) = L.mem s (prioA (L.curW s)) := by
    rw [prioA_eq]; exact htcb1 hcT (by simp) (by simp)
  rw [cur1, hcs1] at w13
  rw [cur1] at hsch3
  rw [cur1] at hq3
  rw [cur1, pr1] at hhp3
  rw [cur1, pr1, e1N] at hH3
  rw [cur1, pr1, e1N] at hE3
  rw [hcs1] at hWF3
  -- the current SC's words
  obtain ⟨hP, hz⟩ := hO.sc _ hcs
  obtain ⟨-, h128, -⟩ := sc_lo hP hz
  have hcv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv' : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hmv := sc_word_val hP hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
  have hmv' : layout.sc.REFILL_MAX.val = 72 := by simp [layout.sc.REFILL_MAX]
  have inΩ : ∀ b, Aligned b → (InRing (L.cscW s) (Z (L.cscW s)) b ∨
      b = core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) → b ∈ Ω := by
    rintro b hb (hh | rfl)
    · exact hO.scW _ hcs b hb hh.inSC
    · exact hO.scW _ hcs _ hb ⟨by rw [hcv]; omega, by rw [hcv, hcv']; omega⟩
  have hmR : ¬ InRing (L.cscW s) (Z (L.cscW s)) (maxA (L.cscW s)) := fun h => by
    unfold InRing maxA at h; rw [hmv, hmv'] at h; omega
  have hmC : maxA (L.cscW s) ≠ core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED := fun e => by
    have e' := congrArg UScalar.val e
    unfold maxA at e'; rw [hmv, hcv, hmv', hcv'] at e'; omega
  have ksn : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 →
      ¬ InSC (L.cscW s) (Z (L.cscW s)) (core.num.U64.wrapping_add (L.ksb s) o) := fun o ho h8 hin => by
    have hsg := (hS.all _ hcs).2.2 _ (ks_aligned hN ho h8) hin
    have := hS.ks _ hsg
    rw [ks_word_val hN ho] at this
    omega
  obtain ⟨Qq, Rq, h1⟩ := hB1.1
  have kY : ∀ Y, WritesIn st s1 Y (RrWT st T s1 (L.curW s) (L.cscW s) (Z (L.cscW s))) →
      (∀ o : U64, o.val < 120 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 40 → o.val ≠ 56 → o.val ≠ 80 → o.val ≠ 48 →
        L.mem Y (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o)) ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 → K.val ≠ 3592 →
        L.mem Y (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ b ∈ Ω, ¬ InRing (L.cscW s) (Z (L.cscW s)) b →
        b ≠ core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED → L.mem Y b = L.mem s b) := by
    intro Y wY
    obtain ⟨kN, kT, kΩ⟩ := rrw_keep h1 hcT inΩ wY
    refine ⟨fun o q1 q2 q3 q4 q5 q6 q7 => ?_, fun y hy K q1 q2 q3 q4 q5 => ?_, fun b hb n1' n2' => ?_⟩
    · rw [← e1N, kN o q1 q2 q3 q4 q5 q6, e1N]
      exact hnode1 o (by omega) q2 q4 q7
    · rw [kT y hy K q1 q2 q3 q4 q5]
      exact htcb1 hy q1 q2
    · rw [kΩ b hb n1' n2']
      exact agΩ1 b hb
  have kS : ∀ Y, WritesIn st s1 Y (RrWT st T s1 (L.curW s) (L.cscW s) (Z (L.cscW s))) → ∀ b ∈ Ω,
      ¬ InSC (L.cscW s) (Z (L.cscW s)) b → L.mem Y b = L.mem s b := fun Y wY b hb hn =>
    (kY Y wY).2.2 b hb (fun hr => hn hr.inSC) (fun e => hn (by rw [e]; exact hcq.2.2.1.1))
  -- the SCs other than the current one, the release head's SC
  have wfO : ∀ Y, WritesIn st s1 Y (RrWT st T s1 (L.curW s) (L.cscW s) (Z (L.cscW s))) → ∀ c ∈ Scs,
      c ≠ L.cscW s → L.rmax Y c = L.rmax s c ∧ (c ∈ Ac → RefillsWF st Y c (Z c)) := by
    intro Y wY c hc hne
    have hd := hO.scDisj c hc _ hcs hne
    have kc : ∀ b, Aligned b → InSC c (Z c) b → L.mem Y b = L.mem s b := fun b hb hin =>
      (kY Y wY).2.2 b ((scq_of hO hS hc).2.1 b hb hin)
        (fun hr => by unfold InRing at hr; unfold InSC at hin; omega)
        (fun e => by rw [e] at hin; unfold InSC at hin; rw [hcv, hcv'] at hin; omega)
    have hqc := scq_of hO hS hc
    exact ⟨kc _ hqc.2.2.2.2 hqc.2.2.2.1, fun hac => (hS.wf hc hac).agree kc⟩
  have rhY : ∀ Y, WritesIn st s1 Y (RrWT st T s1 (L.curW s) (L.cscW s) (Z (L.cscW s))) →
      RefillsWF st Y (L.cscW s) (Z (L.cscW s)) →
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ≠ 0#u64 →
      L.mem Y (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) =
        L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) ∧
      RefillsWF st Y (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))
        (Z (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))) ∧
      L.rmax Y (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))) ≠ 0#u64 := by
    intro Y wY wfY hne
    obtain ⟨r1, -, -, r4, r5⟩ := rel_facts hI hne
    refine ⟨by rw [scA_eq]; exact (kY Y wY).2.1 _ r1 3464#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
      ?_⟩
    by_cases hsame : L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) = L.cscW s
    · rw [hsame]
      refine ⟨wfY, ?_⟩
      rw [show L.rmax Y (L.cscW s) = L.rmax s (L.cscW s) from (kY Y wY).2.2 _ hmaxΩ hmR hmC]
      exact hmx0
    · obtain ⟨e1, e2⟩ := wfO Y wY _ r4 hsame
      exact ⟨e2 ((hS.act _ r4).2 r5), by rw [e1]; exact r5⟩
  -- the `schedule` state `s3`
  have k3 : L.ksb s3 = L.ksb s := w13.1.trans k1
  have c3 : L.cpu s3 = L.cpu s := w13.2.1.trans c1
  have e3N : ∀ o, L.nodeAt s3 (L.cpu s3) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c3, nodeAt_of_ksb k3]
  obtain ⟨nd3, tc3, -⟩ := kY s3 w13
  have hN3 : NodePlaced st T s3 (L.cpu s3) := by rw [c3]; exact hN.ksb k3
  have hcC3 : L.cpu s3 ∈ Cs := by rw [c3]; exact hcC
  have hcur3 : L.curW s3 = L.curW s := by
    unfold LawfulStore.curW
    rw [e3N]
    exact nd3 _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega) (by rw [curth_val]; omega)
      (by rw [curth_val]; omega) (by rw [curth_val]; omega) (by rw [curth_val]; omega)
  have pr3 : L.mem s3 (prioA (L.curW s)) = L.mem s (prioA (L.curW s)) := by
    rw [prioA_eq]; exact tc3 _ hcT _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have hp0 : (L.mem s (prioA (L.curW s))).val < 256 := h0.prio _ hcT
  have haff3 : L.mem s3 (affA (L.curW s)) = L.cpu s3 := by
    rw [c3]; unfold affA; rw [tc3 _ hcT 3520#u64 (by simp) (by simp) (by simp) (by simp) (by simp)]; exact haff
  have scS3 : L.mem s3 (scA (L.curW s)) = L.cscW s := by
    rw [scA_eq, tc3 _ hcT 3464#u64 (by simp) (by simp) (by simp) (by simp) (by simp), ← scA_eq]; exact hsct
  have hd03 : L.mem s3 (core.num.U64.wrapping_add (L.ksb s3) layout.ks.DOMAIN_TIME) ≠ 0#u64 := by
    rw [k3, kS s3 w13 _ (hS.ksΩ _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME]))
      (ksn _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME]))]
    exact sq_dt eq
  rw [← e3N] at hH3 hE3
  -- the choose path: back to the current thread
  have hqd3 : sched.queued st s3 (L.curW s) = ok true := by
    rw [eq_of_spec_fd (sched.queued.spec (L := L) s3 _)]; simp [hq3]
  have hac3 : sched.action st s3 = ok sched.ACTION_CHOOSE_NEW := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s3), hact3]
  have es := schedule_choose_eq st ar s3 a3 (L.curW s) (awaken_none ar s3 a3 hT3 hR3) hac3
    (by rw [cur_thread_ok, hcur3]) hsch3 hqd3
  rw [es] at esc
  obtain ⟨⟨Xc, ac⟩, ecn, esr⟩ := bind_eq_ok esc
  have esr' : PathObl.LT.schedRes st ar Xc ac = ok (s4, a4) := esr
  obtain ⟨wC, curC⟩ := rr_choose hA hT hcT hN3 hcur3 hd03 hp0 hl13 hhp3 pr3 haff3 hq3 hH3 hE3 ecn
  have wXc : WritesIn st s1 Xc (RrWT st T s1 (L.curW s) (L.cscW s) (Z (L.cscW s))) :=
    w13.trans1 (wC.mono fun b hb => by
      rcases hb with ⟨o, ho, ho1, ho2, e⟩ | e | e | e
      · have ho' : 128 ≤ o.val := ho
        exact Or.inr (Or.inr (Or.inl ⟨o, by
          show o.val = 16 ∨ o.val = 40 ∨ o.val = 56 ∨ o.val = 80 ∨ 120 ≤ o.val
          omega, ho1, ho2, by rw [e, w13.2.1, nodeAt_of_ksb w13.1]⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨L.curW s, hcT, Or.inl e⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨L.curW s, hcT, Or.inr e⟩))))
  obtain ⟨kNc, kTc, kΩc⟩ := kY Xc wXc
  have kc : L.ksb Xc = L.ksb s := wXc.1.trans k1
  have cc : L.cpu Xc = L.cpu s := wXc.2.1.trans c1
  have eCN : ∀ o, L.nodeAt Xc (L.cpu Xc) o = L.nodeAt s (L.cpu s) o := fun o => by rw [cc, nodeAt_of_ksb kc]
  have hNc : NodePlaced st T Xc (L.cpu Xc) := by rw [cc]; exact hN.ksb kc
  have hcCc : L.cpu Xc ∈ Cs := by rw [cc]; exact hcC
  have hcsc : L.cscW Xc = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [eCN]
    exact kNc _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  have scC : L.mem Xc (scA (L.curW s)) = L.cscW s := by
    rw [scA_eq, kTc _ hcT 3464#u64 (by simp) (by simp) (by simp) (by simp) (by simp), ← scA_eq]; exact hsct
  have hmaxC : L.rmax Xc (L.cscW s) = L.rmax s (L.cscW s) := kΩc _ hmaxΩ hmR hmC
  have wfC : RefillsWF st Xc (L.cscW s) (Z (L.cscW s)) := hWF3.agree fun b hb hin => by
    have ho := (h0.omega b (hcq.2.1 b hb hin)).ksb k3
    refine wC.mem_eq hb fun hh => ?_
    rcases hh with ⟨o, -, ho1, -, e⟩ | e | e | e
    · exact out_ne_node ho hcC3 hN3 ho1 (congrArg UScalar.val e).symm
    · exact out_ne_field ho hcT ht' (K := 3592#u64) (by simp) (congrArg UScalar.val e).symm
    · exact out_ne_field ho hcT ht' (K := 3480#u64) (by simp) (congrArg UScalar.val e).symm
    · exact out_ne_field ho hcT ht' (K := 3488#u64) (by simp) (congrArg UScalar.val e).symm
  have hcqC : SCq st Xc Ω (L.cscW s) (Z (L.cscW s)) := ⟨fun _ => wfC, hcq.2⟩
  -- `schedule`'s tail at `Xc`
  have hst : schedTail (st := st) ar Xc ac = PathObl.LT.schedRes st ar Xc ac := rfl
  have hfp := schedTail_fp ar hA Xc ac (zc := Z (L.cscW s))
    (B := fun b => (∀ K : U64, K.val < 4096 → b ≠ core.num.U64.wrapping_add (L.curW s) K) ∧
      b ≠ L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
    hcCc hNc hT (fun b hb => (h0.omega b hb).ksb kc)
    (by rw [curC]; exact hcT) (by rw [curC, scC, hcsc]) (by rw [hcsc]; exact hcqC)
    (fun o ho h8 hz => by
      rw [eCN]
      refine ⟨fun K hK => node_ne_field hN ho hcT ht' hK, fun e => hz ?_⟩
      have e' := congrArg UScalar.val e
      rw [nodeAt_val hN ho, nodeAt_val hN (by rw [curth_val]; omega), curth_val] at e'
      omega)
    (fun b hb hin => by
      rw [hcsc] at hin
      have ho := h0.omega b (hcq.2.1 b hb hin)
      exact ⟨fun K hK e => out_ne_field ho hcT ht' hK (congrArg UScalar.val e).symm,
        fun e => out_ne_node ho hcC hN (by rw [curth_val]; omega) (congrArg UScalar.val e).symm⟩)
  rw [hst, esr', WP.spec_ok] at hfp
  have w34 := hfp
  have k4 : L.ksb s4 = L.ksb s := w34.1.trans kc
  have c4 : L.cpu s4 = L.cpu s := w34.2.1.trans cc
  have e4N : ∀ o, L.nodeAt s4 (L.cpu s4) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c4, nodeAt_of_ksb k4]
  have hcur4 : L.curW s4 = L.curW s := by
    have h3 := curC
    unfold LawfulStore.curW at h3 ⊢
    rw [eCN] at h3
    rw [w34.2.1, nodeAt_of_ksb w34.1, eCN,
      w34.mem_eq (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) (fun hb => hb.2 rfl)]
    exact h3
  have tK4 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 → K.val ≠ 3592 →
      L.mem s4 (core.num.U64.wrapping_add (L.curW s) K) = L.mem s (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K hK h8 q1 q2 q3 =>
      (w34.mem_eq (field_aligned ht' hK h8) (fun hb => hb.1 K hK rfl)).trans (kTc _ hcT K hK h8 q1 q2 q3)
  have hy4 : L.mem s4 (yieldA (L.curW s)) = 0#u64 := by
    unfold yieldA
    rw [tK4 _ (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact hy0
  have hst4 : L.mem s4 (stA (L.curW s)) = L.mem s (stA (L.curW s)) := by
    rw [stA_eq, tK4 _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  have sc4 : L.mem s4 (scA (L.curW s)) = L.cscW s := by
    rw [scA_eq, tK4 _ (by simp) (by simp) (by simp) (by simp) (by simp), ← scA_eq]; exact hsct
  have aff4 : L.mem s4 (affA (L.curW s)) = L.cpu s := by
    unfold affA; rw [tK4 _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact haff
  have hN4 : NodePlaced st T s4 (L.cpu s4) := by rw [c4]; exact hN.ksb k4
  obtain ⟨w45, hst5⟩ := activate_fp ar hT hcT hN4 hcur4 hy4 eac
  have e5N : ∀ o, L.nodeAt s5 (L.cpu s5) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [w45.2.1, nodeAt_of_ksb w45.1, e4N]
  have hst5' : L.mem s5 (stA (L.curW s)) ≠ sched.TS_RUNNING_VM := by
    rcases hst5 with e | e
    · rw [e]; simp [sched.TS_RUNNING, sched.TS_RUNNING_VM]
    · rw [e, hst4]; exact hnvm
  have hcur5 : L.curW s5 = L.curW s := by
    have e : L.curW s5 = L.curW s4 := by
      unfold LawfulStore.curW
      rw [w45.2.1, nodeAt_of_ksb w45.1]
      refine w45.mem_eq (nodeAt_aligned hN4 (by rw [curth_val]; omega) (by rw [curth_val])) ?_
      rintro (e | e | e)
      · exact tcb_node_ne hN4 hcT ht' (by simp) (by rw [curth_val]; omega) e.symm
      · rw [stA_eq] at e
        exact tcb_node_ne hN4 hcT ht' (by simp) (by rw [curth_val]; omega) e.symm
      · have e' := congrArg UScalar.val e
        rw [nodeAt_val hN4 (by rw [curth_val]; omega), nodeAt_val hN4 (by rw [act_val]; omega), curth_val,
          act_val] at e'
        omega
    rw [e, hcur4]
  rw [cur_thread_ok, hcur5] at et
  have et' := ok_inj_ff et
  subst et'
  -- the guarded store: what it admits
  have hok : IrqOk st s := ⟨haff, hsct, hcore⟩
  replace gRd := gRd hok
  replace gWr := gWr hok
  have hwS' := hwS hok
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
  have cW : ∀ K : U64, 256 ≤ K.val → K.val < 3328 → K.val % 8 = 0 → W (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K h1 h2 h3 =>
    gWr _ (field_aligned ht' (by omega) h3) (Or.inr (Or.inl ⟨K, h1, by omega, h3, rfl⟩)) (fun e => by
      rw [stA_eq] at e
      exact tcb_word_ne ht' ht' (by omega) (by simp) (fun _ h => by simp at h; omega) e)
  have rR : ∀ r : U64, r.val < 384 → R (regA (L.curW s) r) := fun r hr => by
    obtain ⟨K, hK, e⟩ := regA_eq ht' hr
    rw [e]; exact cR K (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have rW : ∀ r : U64, r.val < 384 → W (regA (L.curW s) r) := fun r hr => by
    obtain ⟨K, hK, e⟩ := regA_eq ht' hr
    rw [e]; exact cW K (by omega) (by omega) (by omega)
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
  have rIq : R (inqA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rYt : R (yieldA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rMx : R (maxA (L.cscW s)) := scR _ hcq.2.2.2.1 hcq.2.2.2.2
  have rCore : R (scCoreA (L.cscW s)) := by
    obtain ⟨hP, hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
    have hcv : layout.sc.CORE.val = 16 := by simp [layout.sc.CORE]
    exact scR _ ⟨by unfold scCoreA; rw [hv]; omega, by unfold scCoreA; rw [hv, hcv]; omega⟩
      (by unfold Aligned scCoreA; rw [hv, hcv]; omega)
  have nrm : ∀ Y : S, (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → NodeSt (L := L) R W Y := fun Y e => by
    unfold PathObl.NodeSt
    rw [e, e]
    exact ⟨nR _ (by rw [curth_val]; omega) (by rw [curth_val]), nR _ (by rw [act_val]; omega) (by rw [act_val]),
      nW _ (by rw [act_val]; omega) (by rw [act_val])⟩
  have ndR : ∀ (Y : S), (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → ∀ o : U64, o.val < 4288 →
      o.val % 8 = 0 → R (L.nodeAt Y (L.cpu Y) o) := fun Y e o h1 h2 => by rw [e]; exact nR o h1 h2
  have hdC : ∀ Y : S, (∀ b ∈ Ω, L.mem Y b = L.mem s b) → RdHead (L := L) R Y (L.cscW s) := fun Y ag =>
    hSc.head ((SCq.agree hcq ag).1 (by
      unfold LawfulStore.rmax; rw [ag _ hmaxΩ]; exact hmx0))
  -- the release head
  have hRH : ∀ Y : S, L.ksb Y = L.ksb s → L.cpu Y = L.cpu s →
      L.mem Y (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) →
      (∀ y ∈ T, L.mem Y (scA y) = L.mem s (scA y)) → (∀ b ∈ Ω, L.mem Y b = L.mem s b) →
      L.mem Y (rhA (L := L) Y) ≠ 0#u64 → L.mem Y (rhA (L := L) Y) ∈ T ∧
      R (scA (L.mem Y (rhA (L := L) Y))) ∧
      SCq st Y Ω (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) (Z (L.mem Y (scA (L.mem Y (rhA (L := L) Y))))) ∧
      L.rmax Y (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) ≠ 0#u64 ∧
      (∀ b, InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) (Z (L.mem Y (scA (L.mem Y (rhA (L := L) Y))))) b →
        Aligned b → R b) ∧
      (L.mem Y (scA (L.mem Y (rhA (L := L) Y))) ≠ L.cscW s → ∀ b,
        InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) (Z (L.mem Y (scA (L.mem Y (rhA (L := L) Y))))) b →
        Outside b (L.cscW s) (Z (L.cscW s))) := by
    intro Y kY cY eh es ag
    have e0 : L.mem Y (rhA (L := L) Y) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := by
      show L.mem Y (L.nodeAt Y (L.cpu Y) _) = _
      rw [cY, nodeAt_of_ksb kY, eh]
    rw [e0]
    intro hne
    obtain ⟨r1, -, -, r4, r5⟩ := rel_facts hI hne
    rw [es _ r1]
    have hqr := scq_of hO hS r4
    refine ⟨r1, gRd _ ?_ (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl rfl⟩)))), SCq.agree hqr ag, ?_,
      fun b hb ha => gRd _ ha (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr hb⟩)))), fun hn b hb => ?_⟩
    · rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp)
    · unfold LawfulStore.rmax
      rw [ag _ (hqr.2.1 _ hqr.2.2.2.2 hqr.2.2.2.1)]; exact r5
    · have := hO.scDisj _ r4 _ hcs hn
      unfold Outside; unfold InSC at hb; omega
  have rhd : ∀ Y : S, L.ksb Y = L.ksb s → L.cpu Y = L.cpu s →
      L.mem Y (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) →
      (∀ y ∈ T, L.mem Y (scA y) = L.mem s (scA y)) → (∀ b ∈ Ω, L.mem Y b = L.mem s b) →
      L.mem Y (rhA (L := L) Y) ≠ 0#u64 → R (scA (L.mem Y (rhA (L := L) Y))) ∧
        RdHead (L := L) R Y (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) := by
    intro Y kY cY eh es ag hne
    obtain ⟨-, q2, q3, q4, q5, -⟩ := hRH Y kY cY eh es ag hne
    exact ⟨q2, PathObl.ScAcc.head (W := fun _ => True) ⟨fun b ha hb => q5 b hb ha, fun _ _ _ => trivial, trivial⟩ (q3.1 q4)⟩
  have scK1 : ∀ y ∈ T, L.mem s1 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact htcb1 hy (by simp) (by simp)
  have rh1 : L.mem s1 (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) :=
    hnode1 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  -- the earliest timer
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
    refine ⟨q1, fun K hK => gRd _ (field_aligned (hT _ q1) (by omega) (by omega))
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
        exact (tmF hne).2.1 3528#u64 (by simp))
    rwa [c1] at this
  have grdue : localtimer.release_due gS s1 (L.cpu s) = localtimer.release_due st s1 (L.cpu s) := by
    have := release_due.guard (gS := gS) s1
      (ndR s1 e1N _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
      (fun hne => rhd s1 k1 c1 rh1 scK1 agΩ1 hne)
      (ndR s1 e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    rwa [c1] at this
  -- the round-robin case's guarded calls
  have hKr' := hKr hok
  have hTab' := hTab hok
  have nR3 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s3 (L.cpu s3) o) := fun o q1 q2 => by
    rw [e3N]; exact nR o q1 q2
  have nW3 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → W (L.nodeAt s3 (L.cpu s3) o) := fun o q1 q2 => by
    rw [e3N]; exact nW o q1 q2
  have wct : ∀ b, Aligned b →
      (b = nextA .Sched (L.curW s) ∨ b = prevA .Sched (L.curW s) ∨ b = inqA (L.curW s)) → W b :=
    fun b hb h => gWr _ hb (Or.inr (Or.inr (Or.inr (Or.inr h)))) (by
      rcases h with rfl | rfl | rfl
      · rw [stA_eq]; exact tcb_word_ne ht' ht' (K1 := 3480#u64) (by simp) (by simp) (fun _ e => by simp at e)
      · rw [stA_eq]; exact tcb_word_ne ht' ht' (K1 := 3488#u64) (by simp) (by simp) (fun _ e => by simp at e)
      · rw [stA_eq]; exact tcb_word_ne ht' ht' (K1 := 3592#u64) (by simp) (by simp) (fun _ e => by simp at e))
  have wN : W (nextA .Sched (L.curW s)) := wct _ (field_aligned ht' (K := 3480#u64) (by simp) (by simp)) (Or.inl rfl)
  have wP : W (prevA .Sched (L.curW s)) :=
    wct _ (field_aligned ht' (K := 3488#u64) (by simp) (by simp)) (Or.inr (Or.inl rfl))
  have wI : W (inqA (L.curW s)) := wct _ (field_aligned ht' (K := 3592#u64) (by simp) (by simp)) (Or.inr (Or.inr rfl))
  have rN : R (nextA .Sched (L.curW s)) := cR 3480#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rPv : R (prevA .Sched (L.curW s)) := cR 3488#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rA : R (affA (L.curW s)) := cR 3520#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rD : R (domA (L.curW s)) := cR 3432#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rP : R (prioA (L.curW s)) := cR 3448#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  -- the current thread's CNode slot words
  have slot8 : ∀ (i : U64) {sl : U64}, (core.num.U64.wrapping_mul i layout.cte.SIZE).val + 8 < 192 →
      (core.num.U64.wrapping_mul i layout.cte.SIZE).val % 32 = 0 → obj.Tcb.slot (L.curW s) i = ok sl →
      R sl ∧ R (core.num.U64.wrapping_add sl 8#u64) := by
    intro i sl hK h8 e
    have es : obj.Tcb.slot (L.curW s) i =
        ok (core.num.U64.wrapping_add (L.curW s) (core.num.U64.wrapping_mul i layout.cte.SIZE)) := by
      unfold obj.Tcb.slot; simp only [lift, bind_ok]
    rw [es] at e
    have e' := ok_inj_ff e
    subst e'
    have hv : (core.num.U64.wrapping_add (core.num.U64.wrapping_mul i layout.cte.SIZE) 8#u64).val =
        (core.num.U64.wrapping_mul i layout.cte.SIZE).val + 8 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] <;> omega
    have ea : core.num.U64.wrapping_add
        (core.num.U64.wrapping_add (L.curW s) (core.num.U64.wrapping_mul i layout.cte.SIZE)) 8#u64 =
        core.num.U64.wrapping_add (L.curW s)
          (core.num.U64.wrapping_add (core.num.U64.wrapping_mul i layout.cte.SIZE) 8#u64) := by
      apply UScalar.eq_of_val_eq
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] <;> omega
    rw [ea]
    exact ⟨gRd _ (field_aligned ht' (by omega) (by omega))
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, by omega, by omega, by omega, rfl⟩))))),
      gRd _ (field_aligned ht' (by omega) (by omega))
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, by omega, by omega, by omega, rfl⟩)))))⟩
  have hKv : (core.num.U64.wrapping_mul layout.tcb.SLOT_VTABLE layout.cte.SIZE).val = 32 := by
    unfold layout.tcb.SLOT_VTABLE layout.cte.SIZE
    simp [core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  have hKt : (core.num.U64.wrapping_mul layout.tcb.SLOT_TIMEOUT_HANDLER layout.cte.SIZE).val = 128 := by
    unfold layout.tcb.SLOT_TIMEOUT_HANDLER layout.cte.SIZE
    simp [core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  have vtR := slot8 layout.tcb.SLOT_VTABLE (by rw [hKv]; omega) (by rw [hKv]) (slot_vt _)
  have hRV3 : PathObl.RdVm (L := L) R s3 (L.curW s) := by
    refine ⟨vtR.1, vtR.2, ?_, ?_⟩
    · show R (core.num.U64.wrapping_add (L.ksb s3) _)
      rw [k3]
      exact hKr'
    · refine fun hi' hhi => ?_
      have aT := hAs hi' hhi
      rw [k3, kS s3 w13 _ aT.1 (fun hin => aT.2.1 ((hS.all _ hcs).2.2 _ (h0.omega _ aT.1).1 hin))]
      exact hTab' hi' hhi
  -- the RdBitmap / queue words at `s3`
  have bR3 : PathObl.RdBitmap (L := L) R s3 :=
    ⟨nR3 _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]), fun inv hinv => nR3 _ (by simp; omega) (by simp)⟩
  have bW1 : W (L.nodeAt s3 (L.cpu s3) l1Off) := nW3 _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])
  have bW2 : ∀ inv : U64, inv.val < 4 → W (L.nodeAt s3 (L.cpu s3) (w64 (136 + 8 * inv.val))) :=
    fun inv hinv => nW3 _ (by simp; omega) (by simp)
  have hp3 : (L.mem s3 (prioA (L.curW s))).val < 256 := by rw [pr3]; exact hp0
  have hH3s : L.mem s3 (L.nodeAt s3 (L.cpu s3) (rqOff (L.mem s3 (prioA (L.curW s))))) = L.curW s := by
    rw [pr3]; exact hH3
  have hE3s : L.mem s3 (L.nodeAt s3 (L.cpu s3) (rqTailOff (L.mem s3 (prioA (L.curW s))))) = L.curW s := by
    rw [pr3]; exact hE3
  have hdq3 : sched.dequeue gS s3 (L.curW s) = sched.dequeue st s3 (L.curW s) :=
    sched.dequeue.guard_single s3 (L.curW s) hp3 haff3 hq3 hH3s hE3s rIq wI rA rD rP
      (nR3 _ (by rw [rqOff_val hp3]; omega) (by rw [rqOff_val hp3]; omega))
      (nW3 _ (by rw [rqOff_val hp3]; omega) (by rw [rqOff_val hp3]; omega))
      (nR3 _ (by rw [rqTailOff_val hp3]; omega) (by rw [rqTailOff_val hp3]; omega))
      (nW3 _ (by rw [rqTailOff_val hp3]; omega) (by rw [rqTailOff_val hp3]; omega))
      bR3 bW1 bW2 rN rPv wN wP
  have hsw3 : sched.switch_to_thread gS ar s3 a3 (L.curW s) = sched.switch_to_thread st ar s3 a3 (L.curW s) :=
    sched.switch_to_thread.guard hA s3 a3 _ hRV3 hdq3 (fun s2'' e => by
      have w := dequeue_single_writes hT hcT hN3 hp3 haff3 hq3 hH3s hE3s e
      rw [w.2.1, nodeAt_of_ksb w.1, e3N]
      exact nW _ (by rw [curth_val]; omega) (by rw [curth_val]))
  have hcn : sched.schedule_choose_new_thread gS ar s3 a3 = sched.schedule_choose_new_thread st ar s3 a3 :=
    sched.schedule_choose_new_thread.guard ar s3 a3 (by rw [k3]; exact hD2) hd03
      (sched.choose_thread.guard_ne ar s3 a3 bR3 hl13 fun p hp => by
        rw [hhp3] at hp
        have e := ok_inj_ff hp
        subst e
        refine ⟨hp0, nR3 _ (by rw [rqOff_val hp0]; omega) (by rw [rqOff_val hp0]; omega),
          nR3 _ (by rw [rqTailOff_val hp0]; omega) (by rw [rqTailOff_val hp0]; omega), ?_⟩
        rw [hH3]
        exact hsw3)
  -- `schedRes` at `Xc`
  have tmCe : L.mem Xc (L.nodeAt Xc (L.cpu Xc) layout.node.TIMER_MIN) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    rw [eCN]
    exact kNc _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN])
  have tmC : L.mem Xc (L.nodeAt Xc (L.cpu Xc) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem Xc (L.nodeAt Xc (L.cpu Xc) layout.node.TIMER_MIN) ∈ T ∧
      R (tdA (L.mem Xc (L.nodeAt Xc (L.cpu Xc) layout.node.TIMER_MIN))) := fun hne => by
    rw [tmCe] at hne ⊢
    exact ⟨(tmF hne).1, (tmF hne).2.1 3528#u64 (by simp)⟩
  have rhCe : L.mem Xc (rhA (L := L) Xc) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := by
    show L.mem Xc (L.nodeAt Xc (L.cpu Xc) _) = _
    rw [eCN]
    exact kNc _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have hrsw := resume_hsw_hfr (gS := gS) ar hA Xc ac (zc := Z (L.cscW s)) hcCc hNc hT
    (fun b hb => (h0.omega b hb).ksb kc) (by rw [curC]; exact hcT) (by rw [curC, scC, hcsc])
    (by rw [hcsc]; exact hcqC) (by rw [hcsc, hmaxC]; exact hmx0)
    (fun o q1 q2 => by rw [eCN]; exact ⟨nR o q1 q2, nW o q1 q2⟩)
    (by rw [hcsc]; exact hSc) (by rw [curC]; exact rSc) (by rw [kc]; exact hD2)
    (fun hne => by
      rw [hcsc]
      rw [rhCe] at hne ⊢
      obtain ⟨q1, q2, q3⟩ := rhY Xc wXc wfC hne
      obtain ⟨r1, -, -, r4, -⟩ := rel_facts hI hne
      rw [q1]
      exact ⟨_, r1, gRd _ (by rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp))
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl rfl⟩)))),
        ⟨fun _ => q2, (scq_of hO hS r4).2⟩, q3,
        fun b hb ha => gRd _ ha (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr hb⟩)))),
        fun hn b hb => by have := hO.scDisj _ r4 _ hcs hn; unfold Outside; unfold InSC at hb; omega,
        fun e => by rw [e]⟩)
    (fun hne => tmC hne)
  have hres3 : ∀ (X' : S) (a' : A), sched.schedule_choose_new_thread st ar s3 a3 = ok (X', a') →
      PathObl.LT.schedRes gS ar X' a' = PathObl.LT.schedRes st ar X' a' := by
    intro X' a'' e
    rw [ecn] at e
    have e' := ok_inj_ff e
    simp only [Prod.mk.injEq] at e'
    obtain ⟨rfl, rfl⟩ := e'
    exact PathObl.LT.schedRes.guard ar Xc ac (fun o q1 q2 => by rw [eCN]; exact ⟨nR o q1 q2, nW o q1 q2⟩)
      hrsw.1 hrsw.2
  -- `schedule` at `s3`
  have tm3e : L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    rw [e3N]
    exact nd3 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN])
  have rh3e : L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := by
    rw [e3N]
    exact nd3 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have gsc : sched.schedule gS ar s3 a3 = sched.schedule st ar s3 a3 :=
    sched.schedule.guard_choose ar s3 a3 (fun o q1 q2 => ⟨nR3 o q1 q2, nW3 o q1 q2⟩)
      (fun hne => by
        rw [tm3e] at hne ⊢
        exact (tmF hne).2.1 3528#u64 (by simp))
      hT3
      (fun hne => by
        rw [rh3e] at hne ⊢
        obtain ⟨q1, q2, -⟩ := rhY s3 w13 hWF3 hne
        obtain ⟨r1, -, -, -, -⟩ := rel_facts hI hne
        rw [q1]
        exact ⟨gRd _ (by rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp))
            (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl rfl⟩)))),
          PathObl.ScAcc.head (W := fun _ => True)
            ⟨fun b ha hb => gRd _ ha (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr hb⟩)))), fun _ _ _ => trivial,
              trivial⟩ q2⟩)
      hR3 hact3 (by rw [hcur3]; exact rSt) (by rw [hcur3]; exact rSc) (by rw [hcur3, scS3]; exact rMx)
      (by rw [hcur3]; exact rIq) (by rw [hcur3]; exact hsch3) (by rw [hcur3]; exact hq3) hcn hres3
  -- `round_robin_ok` and `check_budget` at `s1`
  have wf1 : RefillsWF st s1 (L.cscW s) (Z (L.cscW s)) :=
    (SCq.agree hcq agΩ1).1 (by unfold LawfulStore.rmax; rw [agΩ1 _ hmaxΩ]; exact hmx0)
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
  obtain ⟨⟨isc, eisc, hnei⟩, hper, -, -, -, -, -, hhi⟩ := round_robin_ok_true hrr1
  rw [hcs1] at hnei hper
  have eL1 : layout.node.L1_BITMAP = l1Off := by unfold layout.node.L1_BITMAP l1Off w64; rfl
  have hcT1 : L.curW s1 ∈ T := by rw [cur1]; exact hcT
  have wEn1 : L.mem s1 (L.nodeAt s1 (L.cpu s1) (rqOff (L.mem s1 (prioA (L.curW s1))))) ≠ 0#u64 →
      W (nextA .Sched (L.mem s1 (L.nodeAt s1 (L.cpu s1) (rqTailOff (L.mem s1 (prioA (L.curW s1))))))) := by
    intro hne
    exfalso
    have hRQ := h1.ready _ h1.cur
    have hp1 := h1.prio _ hcT1
    have hr := hRQ.1.rel _ hp1
    have hne' : Qq (L.cpu s1) (L.mem s1 (prioA (L.curW s1))) ≠ [] := fun h0' => hne (by
      have e := hr.head
      rw [h0'] at e
      exact e)
    have hB := hRQ.2
    have hb := (hB.l2 _ hp1).2 hne'
    have hw : L.l2W s1 (L.cpu s1) ((L.mem s1 (prioA (L.curW s1))).val / 64) ≠ 0#u64 :=
      (ne_zero_iff_bit _).2 ⟨_, by omega, hb⟩
    have hl := (hB.l1 ((L.mem s1 (prioA (L.curW s1))).val / 64) (by omega)).2 ⟨by omega, hw⟩
    have hl1 : L.l1W s1 (L.cpu s1) ≠ 0#u64 := (ne_zero_iff_bit _).2 ⟨_, by omega, hl⟩
    rcases hhi with h0' | ⟨q, hq, hlt⟩
    · exact hl1 (by unfold LawfulStore.l1W; rw [← eL1]; exact h0')
    · obtain ⟨q', hq', -, -, hq3'⟩ := spec_ex_fd (sched.highest_prio.spec (L := L) s1 _ _ hN1 hB hl1)
      rw [hq] at hq'
      have e := ok_inj_ff hq'
      subst e
      have h3' := hq3' _ hp1 hne'
      have h2' : q.val < (L.mem s1 (prioA (L.curW s1))).val := hlt
      omega
  have gcb : sched.check_budget gS ar s1 a1 = sched.check_budget st ar s1 a1 :=
    sched.check_budget.guard_rr ar s1 a1
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
      (fun c _ => sched.charge_budget.guard_rrC ar (T := T) s1 a1 c
        (ndR s1 e1N _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
        (ndR s1 e1N _ (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]))
        (fun sc e isc' ei => by
          rw [ecs1] at e
          rw [← ok_inj_ff e]
          have eii : isc = isc' := by rw [eisc] at ei; exact ok_inj_ff ei
          subst eii
          refine ⟨hnei, hSc.off wf1 _ (by simp [layout.sc.PERIOD]) (by simp [layout.sc.PERIOD]), ?_,
            hSc.off wf1 _ (by simp [layout.sc.REFILL_HEAD]) (by simp [layout.sc.REFILL_HEAD]),
            hSc.off wf1 _ (by simp [layout.sc.REFILL_TAIL]) (by simp [layout.sc.REFILL_TAIL]), ?_,
            hSc.rd _ hcq.2.2.1.2 hcq.2.2.1.1, hSc.cons⟩
          · rw [eq_of_spec_fd (sporadic.is_round_robin.spec (L := L) s1 _)]
            simp [hper]
          · intro i hi'
            rcases hi' with hi' | hi'
            · rw [eq_of_spec_fd (obj.Sc.refill_head.spec (L := L) s1 _)] at hi'
              rw [← ok_inj_ff hi']
              have q := hSc.rt wf1 wf1.head_lt
              exact ⟨q.1, q.2.2.1, q.2.1, q.2.2.2⟩
            · rw [eq_of_spec_fd (obj.Sc.refill_tail.spec (L := L) s1 _)] at hi'
              rw [← ok_inj_ff hi']
              have q := hSc.rt wf1 wf1.tail_lt
              exact ⟨q.1, q.2.2.1, q.2.1, q.2.2.2⟩)
        (by rw [hcs1]; exact wf1) (by rw [hcs1]; exact hcq.2.2.1.2)
        (fun o q1 q2 => by rw [e1N]; exact ⟨nR o q1 q2, nW o q1 q2⟩)
        (fun s2' s3' e2 e3 => rr_tail_F ar hB1 hrr1 haff1 (by rw [hcs1]; exact hAc) hact1
          (fun o q1 q2 => by rw [e1N]; exact ⟨nR o q1 q2, nW o q1 q2⟩)
          (by rw [hcs1]; exact hSc.off wf1 _ (by simp [layout.sc.PERIOD]) (by simp [layout.sc.PERIOD]))
          (by rw [cur1]; exact rSt) (by rw [cur1]; exact rSc) (by rw [cur1, scK1 _ hcT, hsct]; exact rMx)
          (by rw [cur1]; exact fun sl e => slot8 _ (by rw [hKt]; omega) (by rw [hKt]) e)
          (by rw [hcs1]; exact hdC s1 agΩ1) (by rw [cur1]; exact rIq) (by rw [cur1]; exact wI)
          (by rw [cur1]; exact rA) (by rw [cur1]; exact rD) (by rw [cur1]; exact rP) (by rw [cur1]; exact wN)
          (by rw [cur1]; exact wP) wEn1 e2 e3))
  have k2s : L.ksb s2 = L.ksb s := k2.trans k1
  have c2s : L.cpu s2 = L.cpu s := c2.trans c1
  have ghi : interrupt.handle_interrupt gS ar s2 a1 irq = interrupt.handle_interrupt st ar s2 a1 irq :=
    interrupt.handle_interrupt.guard_timer ar s2 a1 irq eis2
      (interrupt.irq_state.guard s2 irq hi (by rw [k2s]; exact hIq))
      (by rw [c2s, nodeAt_of_ksb k2s]; exact nW _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
      (fun s2'' e => by
        rw [eq_of_spec_fd (obj.node_set.spec (L := L) s2 _ _ _)] at e
        rw [← ok_inj_ff e, nodeAt_of_ksb (L.ksb_wr _ _ _), c2s, nodeAt_of_ksb k2s]
        exact nW _ (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED]))
  have eNx : regA (L.curW s) layout.reg.NEXT_IP = core.num.U64.wrapping_add (L.curW s) 368#u64 := by
    obtain ⟨K, hK, e⟩ := regA_eq ht' (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])
    rw [e]
    congr 1
    apply UScalar.eq_of_val_eq
    rw [hK]
    simp [layout.reg.NEXT_IP]
  have aNx : Aligned (regA (L.curW s) layout.reg.NEXT_IP) := by rw [eNx]; exact field_aligned ht' (by simp) (by simp)
  have sA : Aligned (stA (L.curW s)) := by rw [stA_eq]; exact field_aligned ht' (by simp) (by simp)
  have aA : Aligned (affA (L.curW s)) := field_aligned ht' (by simp) (by simp)
  have nNs : regA (L.curW s) layout.reg.NEXT_IP ≠ stA (L.curW s) := by
    rw [eNx, stA_eq]; exact tcb_word_ne ht' ht' (by simp) (by simp) (fun _ => by simp)
  have nNa : regA (L.curW s) layout.reg.NEXT_IP ≠ affA (L.curW s) := by
    rw [eNx]; exact tcb_word_ne ht' ht' (by simp) (by simp) (fun _ => by simp)
  have gac : sched.activate_thread gS ar s4 a4 = sched.activate_thread st ar s4 a4 :=
    activate_thread.gw ar s4 a4 hcur4 ht' hy4 (nrm s4 e4N) rYt rSt (rR _ (by simp [layout.reg.FAULT_IP]))
      (rW _ (by simp [layout.reg.NEXT_IP]))
      (fun hr pc => hwS' _ (by rw [mem_wr_ne' aNx sA nNs]; exact hr) (by rw [mem_wr_ne' aNx aA nNa]; exact aff4))
      rSc (by rw [sc4]; exact rMx) rIq
  have gvc : vcpu.check gS ar s5 a5 (L.curW s) = vcpu.check st ar s5 a5 (L.curW s) :=
    vcpu.check.guard_nvm ar s5 a5 (L.curW s) rSt hst5'
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
    (IrqCase.rr rfl rfl hrr) (fun _ => grr) (fun h => nomatch h) ecbr gcb ehi ghi esc0 gsc eac gac etr
    (PathObl.sched.cur_thread.guard s5 (ndR s5 e5N _ (by rw [curth_val]; omega) (by rw [curth_val]))) evcr gvc

/-- **An accepted round-robin timer interrupt on the guarded store** (module docstring). -/
theorem irq_accG_rr {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hq : IrqRR st ar s a)
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRd st Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) → W w)
    (hIq : IrqOk st s → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : IrqOk st s → ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART → L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hKr : IrqOk st s → R (krA (L := L) s)) (hTab : IrqOk st s → PathObl.RdTab (L := L) R s)
    (hAs : AsidOff (L := L) Ω Sg s)
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
  obtain ⟨rfl, rfl⟩ := hq s1 a1 now i2 b4 due eu enow ei2 (by rw [← ecs]; exact eb4) (by rw [← ecp]; exact edue)
  have hrr : localtimer.round_robin_ok st ar s1 a1 cpu ct csc now = ok true := by
    cases hc with
    | quiet h4 _ => exact nomatch h4
    | fire h4 _ _ => exact nomatch h4
    | rr _ _ hr => exact hr
  exact irq_accG_rr_walk ar hA hI gRd gWr hIq hD1 hD2 hwS hKr hTab hAs ecpu emx hle ei1 etip eb ect ecsc eok eq eu
    enow erel ei2 eb4 edue hrr ecb ehi esc eac et evc

end main

end Fl4Proofs.P2
