/-
# P2: an accepted timer interrupt, quiet case, on the guarded store (`PathObl.acc`)

`irq_accG_quiet`: from a state with the P1 invariant (`BXI`), an accepted run of
`localtimer.handle_timer_irq_local` whose budget check passes and finds no timer due (`IrqQuiet`) is the same run
on any store `gS` answering the reads of `IrqRd` and the writes of `IrqWr` as `st` (`PathObl.GRd` / `PathObl.GWr`:
`guard st R W` for `acc`, `gd st R P` for `move`). The current thread's `STATE` write (`activate_thread` of a
thread in `Restart`) is a premise per write (`hwS`), as `set_timer_accG`'s; the kernel-global words (the IRQ's
state word, `CUR_DOMAIN`, `DOMAIN_TIME`) are premises `hIq`, `hD1`, `hD2`.

The walk is `irq_quiet_foot`'s; each guarded call is the real call at its state (the guard lemmas of
`P2/FootTimerIrqH`, `P2/FootTimerIrqF`, `P2/FootTimerSetG`, p2io / p2sl), and `irq_replay` puts the run together.
New guards: `vcpu.check.guard_nvm` (a thread not running a VM: the state word only) and `activate_thread.gw`
(p2sl's `activate_thread.guard` with the state write per write).

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqQF
import Fl4Proofs.P2.FootTimerIrqRe
import Fl4Proofs.P2.FootTimerSetAcc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard ScAcc rhA tmA RdHead NodeSt)

/-! ## Two guards -/

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- **`vcpu::check` of a thread not running a VM**: reads its state word. -/
theorem vcpu.check.guard_nvm {A : Type} (ar : machine.Arch A) (s : S) (a : A) (t : U64) (hr : R (stA t))
    (hs : L.mem s (stA t) ≠ sched.TS_RUNNING_VM) :
    vcpu.check gS ar s a t = vcpu.check st ar s a t := by
  unfold vcpu.check
  rw [PathObl.obj.Tcb.state.guard t s hr]
  refine PathObl.bind_guard_congr rfl fun v hv => ?_
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s t)] at hv
  have ev : L.mem s (stA t) = v := ok_inj_ff hv
  subst ev
  have hne : (L.mem s (stA t) != sched.TS_RUNNING_VM) = true := bne_iff_ne.mpr hs
  simp only [hne, ↓reduceIte]

/-- **`activate_thread`** of a current thread `t` yielding to no SC, the `STATE` write of a thread in `Restart`
answered as `st`'s (`hw`). -/
theorem activate_thread.gw {A : Type} (ar : machine.Arch A) (s : S) (a : A) {t : U64}
    (hcur : L.curW s = t) (hT : TcbAddr t) (hy0 : L.mem s (yieldA t) = 0#u64) (hn : NodeSt (L := L) R W s)
    (hyt : R (yieldA t)) (hst : R (stA t)) (hrg : R (regA t layout.reg.FAULT_IP))
    (hwr : W (regA t layout.reg.NEXT_IP))
    (hw : L.mem s (stA t) = sched.TS_RESTART → ∀ pc,
      gS.write (L.wr s (regA t layout.reg.NEXT_IP) pc) (stA t) sched.TS_RUNNING =
        st.write (L.wr s (regA t layout.reg.NEXT_IP) pc) (stA t) sched.TS_RUNNING)
    (h2 : R (scA t)) (h3 : R (maxA (L.mem s (scA t)))) (h4 : R (inqA t)) :
    sched.activate_thread gS ar s a = sched.activate_thread st ar s a := by
  unfold sched.activate_thread
  rw [PathObl.sched.cur_thread.guard s hn.1, cur_thread_ok, hcur]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.yield_to.guard t s hyt, PathObl.eq_ok_of_spec (obj.Tcb.yield_to.spec s t), hy0]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Aeneas.Std.uncurry_apply_pair]
  rw [PathObl.obj.Tcb.state.guard t s hst]
  refine PathObl.bind_guard_congr rfl fun v hv => ?_
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s t)] at hv
  have ev : L.mem s (stA t) = v := ok_inj_ff hv
  subst ev
  by_cases hr : L.mem s (stA t) = sched.TS_RESTART
  · rw [if_pos hr, if_pos hr, PathObl.obj.Tcb.reg.guard t s _ hrg]
    refine PathObl.bind_guard_congr rfl fun pc _ => ?_
    rw [PathObl.obj.Tcb.set_reg.guard t s _ _ hwr, PathObl.set_reg_ok' s t layout.reg.NEXT_IP pc]
    simp only [bind_ok]
    rw [set_thread_state.gw _ t _ hn.wr (hw hr pc) hst h2 (by
      rw [PathObl.st_wr_sc hT, PathObl.reg_wr_sc hT (by simp [layout.reg.NEXT_IP])]; exact h3) h4]
  · rw [if_neg hr, if_neg hr]

end gst

/-! ## The path's word sets -/

section sets
variable {S : Type}

/-- What `plan_objects` / `timer_due` read of the earliest armed thread `tm` (`PlanTm`, its deadline) and of
its bound notification. -/
def TmWords (st : machine.Store S) [L : LawfulStore st] (s : S) (tm w : U64) : Prop :=
  (∃ K : U64, (K.val = 3520 ∨ K.val = 3528 ∨ K.val = 3568 ∨ K.val = 3368 ∨ K.val = 3328 ∨ K.val = 3336 ∨
      K.val = 3360) ∧ w = core.num.U64.wrapping_add tm K) ∨
    (L.mem s (boundA tm) ≠ 0#u64 ∧
      (w = core.num.U64.wrapping_add (L.mem s (boundA tm)) layout.ntfn.TAIL_STATE ∨
        w = core.num.U64.wrapping_add (L.mem s (boundA tm)) layout.ntfn.BOUND_TCB))

/-- The words an accepted timer interrupt (quiet or round-robin) reads at its entry state `s` (current SC sized
by `Z`), besides the kernel-global ones: this core's node words, the current thread's words (`CallerW`), the
current SC, the release head's SC word and SC, `TmWords` of the earliest armed thread, and the current thread's
CNode slot words (offsets below 256: the timeout handler slot, the `VTABLE` slot). -/
def IrqRd (st : machine.Store S) [L : LawfulStore st] (Z : U64 → Nat) (s : S) (w : U64) : Prop :=
  (∃ o : U64, o.val < 4288 ∧ o.val % 8 = 0 ∧ w = L.nodeAt s (L.cpu s) o) ∨ CallerW (L.curW s) w ∨
    InSC (L.cscW s) (Z (L.cscW s)) w ∨
    (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ≠ 0#u64 ∧
      (w = scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)) ∨
        InSC (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))
          (Z (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))) w)) ∨
    (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 ∧
      TmWords st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) w) ∨
    (∃ K : U64, K.val < 256 ∧ K.val % 8 = 0 ∧ w = core.num.U64.wrapping_add (L.curW s) K)

/-- The words an accepted timer interrupt (quiet or round-robin) writes: this core's node words, the current
thread's registers and `STATE` (`CallerRegW`), the current SC's ring and `CONSUMED`, and the current thread's
sched links and queue word (offsets 3480, 3488, 3592: the round-robin `append` / `dequeue`). -/
def IrqWr (st : machine.Store S) [L : LawfulStore st] (Z : U64 → Nat) (s : S) (w : U64) : Prop :=
  (∃ o : U64, o.val < 4288 ∧ o.val % 8 = 0 ∧ w = L.nodeAt s (L.cpu s) o) ∨ CallerRegW (L.curW s) w ∨
    InRing (L.cscW s) (Z (L.cscW s)) w ∨ w = core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED ∨
    w = nextA .Sched (L.curW s) ∨ w = prevA .Sched (L.curW s) ∨ w = inqA (L.curW s)

/-- What an accepted timer interrupt checked at its entry state (`current_ok`): the current thread is on this
core and runs on the current SC, which is on this core. -/
structure IrqOk (st : machine.Store S) [L : LawfulStore st] (s : S) : Prop where
  aff : L.mem s (affA (L.curW s)) = L.cpu s
  sc : L.mem s (scA (L.curW s)) = L.cscW s
  core : L.mem s (scCoreA (L.cscW s)) = L.cpu s

/-- The quiet case selected at the entry state: after `update_timestamp` the budget is sufficient and no timer
is due. -/
def IrqQuiet (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (s : S) (a : A) : Prop :=
  ∀ s1 a1 now i2 b4 due, sched.update_timestamp st ar s a = ok (s1, a1) → sched.cur_time st s1 = ok now →
    sched.consumed st s1 = ok i2 → sporadic.sufficient st ar s1 a1 (L.cscW s) i2 = ok b4 →
    localtimer.timer_due st s1 (L.cpu s) now = ok due → b4 = true ∧ due = false

end sets

/-! ## The `schedule` state's checks -/

section pre
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type _} (ar : machine.Arch A)

/-- At the `schedule` state of the quiet case nothing is due and the action is `RESUME_CURRENT` (the facts
`irq_quiet_schedule` turns into `schedTail`). -/
theorem irq_quiet_pre (hA : P0.ArchTotal ar) {s s1 s3 : S} {a a1 : A} {now : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (eq : localtimer.sched_quiet st s (L.cpu s) = ok true)
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) (enow : sched.cur_time st s1 = ok now)
    (erel : localtimer.release_due st s1 (L.cpu s) = ok false)
    (edue : localtimer.timer_due st s1 (L.cpu s) now = ok false) (w : WritesIn st s1 s3 (HW st s1)) :
    (L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.CUR_TIME) <
        L.mem s3 (tdA (L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN)))) ∧
      RelNone st s3 ∧ L.actionW s3 = sched.ACTION_RESUME_CURRENT := by
  have h0 := hI.1.choose_spec.choose_spec
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  have hB1 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := (irq_quiet_schedule ar (a3 := a1) hA hI eq eu enow erel edue w).1
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
  refine ⟨by rw [hct3]; exact nd3, rel_hw hB1 w (rel_false (by rw [c1]; exact erel)), ?_⟩
  rw [action_hw hN1 w, action_ut ar hA hN eu]; exact sq_true eq

end pre

/-! ## The quiet case on the guarded store -/

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 32000000 in
/-- **The quiet case of an accepted timer interrupt on the guarded store**, from `irq_accept_walk`'s equations
with `IrqCase.quiet` (module docstring). -/
theorem irq_accG_quiet_walk {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
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
    (ecpu : st.cur_cpu s = ok cpu) (emx : layout.irq.MAX = ok mx)
    (hle : ¬ irq > mx) (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
    (etip : localtimer.plan_objects st s = ok tip) (eb : localtimer.same_plan tip p = ok true)
    (ect : sched.cur_thread st s = ok ct) (ecsc : sched.cur_sc st s = ok csc)
    (eok : localtimer.current_ok st s cpu ct csc = ok true) (eq : localtimer.sched_quiet st s cpu = ok true)
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) (enow : sched.cur_time st s1 = ok now)
    (erel : localtimer.release_due st s1 cpu = ok false) (ei2 : sched.consumed st s1 = ok i2)
    (eb4 : sporadic.sufficient st ar s1 a1 csc i2 = ok true)
    (edue : localtimer.timer_due st s1 cpu now = ok false)
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
  rw [check_budget_suf ar ecs1 ei2 eb4] at ecb
  have e2 := ok_inj_ff ecb
  simp only [Prod.mk.injEq] at e2
  obtain ⟨-, e2s, e2a⟩ := e2
  subst e2s e2a
  -- `handle_interrupt`
  obtain ⟨s2', eh2, eh3, -⟩ := handle_interrupt_timer ar emx hle eis1 ehi
  have w13 : WritesIn st s1 s3 (HW st s1) := handle_interrupt_timer_writes hN1 eh2 eh3
  obtain ⟨-, hsch⟩ := irq_quiet_schedule ar hA hI eq eu enow erel edue w13
  obtain ⟨hT3, hR3, hact3⟩ := irq_quiet_pre ar hA hI eq eu enow erel edue w13
  have k3 : L.ksb s3 = L.ksb s := w13.1.trans k1
  have c3 : L.cpu s3 = L.cpu s := w13.2.1.trans c1
  have e3N : ∀ o, L.nodeAt s3 (L.cpu s3) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c3, nodeAt_of_ksb k3]
  have hnode3 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 → o.val ≠ 56 → o.val ≠ 80 →
      L.mem s3 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h40 h48 h56 h80
    have := hw_node hN1 w13 ho h8 ⟨h56, h80⟩
    rw [e1N] at this
    rw [this, hnode1 o ho h8 h40 h48]
  have htcb3 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun hy hK h8 => (hw_tcb hT hN1 w13 hy hK h8).trans (htcb1 hy hK h8)
  have hcC1 : L.cpu s1 ∈ Cs := by rw [c1]; exact hcC
  have hout3 : ∀ b ∈ Ω, L.mem s3 b = L.mem s b := fun b hb =>
    (hw_outside hN1 hcC1 w13 ((h0.omega b hb).ksb k1)).trans (hout1 b (h0.omega b hb))
  have hcur3 : L.curW s3 = L.curW s := by
    unfold LawfulStore.curW
    rw [e3N]
    exact hnode3 _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
      (by rw [curth_val]; omega) (by rw [curth_val]; omega) (by rw [curth_val]; omega)
  have hcs3 : L.cscW s3 = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [e3N]
    exact hnode3 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have hsc3 : L.mem s3 (scA (L.curW s)) = L.mem s (scA (L.curW s)) := by
    rw [scA_eq]; exact htcb3 hcT (by simp) (by simp)
  have hN3 : NodePlaced st T s3 (L.cpu s3) := by rw [c3]; exact hN.ksb k3
  have hcC3 : L.cpu s3 ∈ Cs := by rw [c3]; exact hcC
  -- `schedule`
  have hfp := schedTail_fp ar hA s3 a3 (zc := Z (L.cscW s))
    (B := fun b => (∀ K : U64, K.val < 4096 → b ≠ core.num.U64.wrapping_add (L.curW s) K) ∧
      b ≠ L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
    hcC3 hN3 hT (fun b hb => (h0.omega b hb).ksb k3)
    (by rw [hcur3]; exact hcT) (by rw [hcur3, hsc3, hcs3]; exact hsct) (by rw [hcs3]; exact SCq.agree hcq hout3)
    (fun o ho h8 hz => by
      rw [e3N]
      refine ⟨fun K hK => node_ne_field hN ho hcT ht' hK, fun e => hz ?_⟩
      have e' := congrArg UScalar.val e
      rw [nodeAt_val hN ho, nodeAt_val hN (by rw [curth_val]; omega), curth_val] at e'
      omega)
    (fun b hb hin => by
      rw [hcs3] at hin
      have ho := h0.omega b (hcq.2.1 b hb hin)
      exact ⟨fun K hK e => out_ne_field ho hcT ht' hK (congrArg UScalar.val e).symm,
        fun e => out_ne_node ho hcC hN (by rw [curth_val]; omega) (congrArg UScalar.val e).symm⟩)
  rw [← hsch, esc, WP.spec_ok] at hfp
  have w34 := hfp
  have k4 : L.ksb s4 = L.ksb s := w34.1.trans k3
  have c4 : L.cpu s4 = L.cpu s := w34.2.1.trans c3
  have e4N : ∀ o, L.nodeAt s4 (L.cpu s4) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c4, nodeAt_of_ksb k4]
  have hcur4 : L.curW s4 = L.curW s := by
    have h3 := hcur3
    unfold LawfulStore.curW at h3 ⊢
    rw [e3N] at h3
    rw [w34.2.1, nodeAt_of_ksb w34.1, e3N,
      w34.mem_eq (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) (fun hb => hb.2 rfl)]
    exact h3
  have tK4 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s4 (core.num.U64.wrapping_add (L.curW s) K) = L.mem s (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K hK h8 => (w34.mem_eq (field_aligned ht' hK h8) (fun hb => hb.1 K hK rfl)).trans (htcb3 hcT hK h8)
  have hy4 : L.mem s4 (yieldA (L.curW s)) = 0#u64 := by
    unfold yieldA
    rw [tK4 _ (by simp) (by simp)]
    exact hy0
  have hst4 : L.mem s4 (stA (L.curW s)) = L.mem s (stA (L.curW s)) := by
    rw [stA_eq, tK4 _ (by simp) (by simp)]
  have sc4 : L.mem s4 (scA (L.curW s)) = L.cscW s := by
    rw [scA_eq, tK4 _ (by simp) (by simp), ← scA_eq]; exact hsct
  have aff4 : L.mem s4 (affA (L.curW s)) = L.cpu s := by
    unfold affA; rw [tK4 _ (by simp) (by simp)]; exact haff
  have hN4 : NodePlaced st T s4 (L.cpu s4) := by rw [c4]; exact hN.ksb k4
  -- `activate_thread`
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
      R (core.num.U64.wrapping_add (L.curW s) K) := fun K h1 h2 h3 h4 =>
    gRd _ (field_aligned ht' h2 h3) (Or.inr (Or.inl ⟨K, h1, h2, h3, h4, rfl⟩))
  have cW : ∀ K : U64, 256 ≤ K.val → K.val < 3328 → K.val % 8 = 0 → W (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K h1 h2 h3 =>
    gWr _ (field_aligned ht' (by omega) h3) (Or.inr (Or.inl ⟨K, h1, by omega, h3, rfl⟩)) (fun e => by
      rw [stA_eq] at e
      exact tcb_word_ne ht' ht' (by omega) (by simp) (fun _ h => by simp at h; omega) e)
  have rR : ∀ r : U64, r.val < 384 → R (regA (L.curW s) r) := fun r hr => by
    obtain ⟨K, hK, e⟩ := regA_eq ht' hr
    rw [e]; exact cR K (by omega) (by omega) (by omega) (by omega)
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
  have rSt : R (stA (L.curW s)) := by rw [stA_eq]; exact cR _ (by simp) (by simp) (by simp) (by simp)
  have rSc : R (scA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp)
  have rIq : R (inqA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp)
  have rYt : R (yieldA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp)
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
  have scK3 : ∀ y ∈ T, L.mem s3 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact htcb3 hy (by simp) (by simp)
  have rh1 : L.mem s1 (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) :=
    hnode1 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have rh3 : L.mem s3 (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) :=
    hnode3 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])
  -- the earliest timer
  have tmF : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ∈ T ∧
      (∀ K : U64, (K.val = 3520 ∨ K.val = 3528 ∨ K.val = 3568 ∨ K.val = 3368 ∨ K.val = 3328 ∨ K.val = 3336 ∨
        K.val = 3360) → R (core.num.U64.wrapping_add (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) K)) ∧
      (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64 →
        R (core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
          layout.ntfn.TAIL_STATE) ∧
        R (core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
          layout.ntfn.BOUND_TCB)) := by
    intro hne
    have q1 := (tmin_facts (BXI.blk hI) hcC hne).1
    refine ⟨q1, fun K hK => gRd _ (field_aligned (hT _ q1) (by omega) (by omega))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl ⟨K, hK, rfl⟩⟩))))), fun hb => ?_⟩
    have hn := hX.2.2.bnd _ q1 hb
    obtain ⟨p1, p2⟩ := hO.ntP _ hn
    have al : ∀ K : U64, K.val < 64 → K.val % 8 = 0 →
        Aligned (core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) K) :=
      fun K h1 h2 => by unfold Aligned; rw [ntfn_word_val p1 p2 h1]; omega
    exact ⟨gRd _ (al _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]))
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr ⟨hb, Or.inl rfl⟩⟩))))),
      gRd _ (al _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB]))
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr ⟨hb, Or.inr rfl⟩⟩)))))⟩
  have tm1e : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    rw [e1N]
    exact hnode1 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have tm3e : L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    rw [e3N]
    exact hnode3 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN])
  have tm3 : L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN) ∈ T ∧
      R (tdA (L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN))) := fun hne => by
    rw [tm3e] at hne ⊢
    exact ⟨(tmF hne).1, (tmF hne).2.1 3528#u64 (by simp)⟩
  -- the guarded calls
  have gtip : localtimer.plan_objects gS s = localtimer.plan_objects st s :=
    plan_objects.guard (gS := gS) (nR _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
      (fun hne =>
        { aff := (tmF hne).2.1 3520#u64 (by simp)
          ht := (tmF hne).2.1 3568#u64 (by simp)
          bn := (tmF hne).2.1 3368#u64 (by simp)
          stt := by
            have := (tmF hne).2.1 3328#u64 (by simp)
            rw [← stA_eq] at this
            exact this
          bo := (tmF hne).2.1 3336#u64 (by simp)
          ro := (tmF hne).2.1 3360#u64 (by simp)
          nt := fun n en hn => by
            rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en
            have e := ok_inj_ff en
            subst e
            exact (tmF hne).2.2 hn })
  have gcok : localtimer.current_ok gS s (L.cpu s) (L.curW s) (L.cscW s) =
      localtimer.current_ok st s (L.cpu s) (L.curW s) (L.cscW s) :=
    current_ok.guard s (L.cpu s) (L.curW s) (L.cscW s) (cR _ (by simp) (by simp) (by simp) (by simp)) rSt rYt
      (cR _ (by simp) (by simp) (by simp) (by simp)) rSc (by rw [hsct]; exact rCore) rCore
      (nR _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]))
      (cR _ (by simp) (by simp) (by simp) (by simp)) hD1
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
  have hres := resume_hsw_hfr (gS := gS) ar hA s3 a3 (zc := Z (L.cscW s)) hcC3 hN3 hT
    (fun b hb => (h0.omega b hb).ksb k3) (by rw [hcur3]; exact hcT) (by rw [hcur3, hsc3, hcs3]; exact hsct)
    (by rw [hcs3]; exact SCq.agree hcq hout3)
    (by rw [hcs3]; unfold LawfulStore.rmax; rw [hout3 _ hmaxΩ]; exact hmx0)
    (fun o h1 h2 => by rw [e3N]; exact ⟨nR o h1 h2, nW o h1 h2⟩)
    (by rw [hcs3]; exact hSc) (by rw [hcur3]; exact rSc) (by rw [k3]; exact hD2)
    (fun hne => by
      obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hRH s3 k3 c3 rh3 scK3 hout3 hne
      exact ⟨_, q1, q2, q3, q4, q5, by rw [hcs3]; exact q6, fun e => by rw [e, hcs3]⟩)
    (fun hne => tm3 hne)
  have gsc : sched.schedule gS ar s3 a3 = sched.schedule st ar s3 a3 :=
    sched.schedule.guard_nodue ar s3 a3 (fun o h1 h2 => by rw [e3N]; exact ⟨nR o h1 h2, nW o h1 h2⟩)
      (fun hne => (tm3 hne).2) hT3 (fun hne => rhd s3 k3 c3 rh3 scK3 hout3 hne) hR3 hact3 hres.1 hres.2
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
    (IrqCase.quiet rfl rfl) (fun h => nomatch h) (fun h => nomatch h) ecbr gcb ehi ghi esc gsc eac gac etr
    (PathObl.sched.cur_thread.guard s5 (ndR s5 e5N _ (by rw [curth_val]; omega) (by rw [curth_val]))) evcr gvc

/-- **An accepted quiet timer interrupt on the guarded store** (module docstring). -/
theorem irq_accG_quiet {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hq : IrqQuiet st ar s a)
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRd st Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) → W w)
    (hIq : IrqOk st s → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : IrqOk st s → ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART → L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    localtimer.handle_timer_irq_local gS ar s a irq p = ok (true, s', a') := by
  obtain ⟨cpu, mx, i1, ct, csc, now, i2, tip, b4, due, x, s1, s2, s3, s4, s5, a1, a2, a3, a4, a5, t, ecpu, emx,
    hle, ei1, hi1, etip, eb, ect, ecsc, eok, eq, eu, enow, erel, ei2, eb4, edue, -, ecb, ehi, esc, eac, et,
    evc⟩ := irq_accept_walk ar h
  subst hi1
  have ecp : cpu = L.cpu s := by
    have e := ecpu
    rw [L.cur_cpu_eq] at e; exact (ok_inj_ff e).symm
  have ecs : csc = L.cscW s := by
    have e := ecsc
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at e; exact (ok_inj_ff e).symm
  obtain ⟨rfl, rfl⟩ := hq s1 a1 now i2 b4 due eu enow ei2 (by rw [← ecs]; exact eb4) (by rw [← ecp]; exact edue)
  exact irq_accG_quiet_walk ar hA hI gRd gWr hIq hD1 hD2 hwS ecpu emx hle ei1 etip eb ect ecsc eok eq eu enow erel
    ei2 eb4 edue ecb ehi esc eac et evc

end main

end Fl4Proofs.P2
