/-
# P2: the quiet case of an accepted timer interrupt writes only its footprint

`irq_quiet_foot`: from a state with the P1 invariant (`BXI`), the tail of an accepted run of
`localtimer.handle_timer_irq_local` (the intermediate equations `irq_accept_walk` returns) in the quiet case
(budget sufficient, no timer due) writes only `FootLt` of its entry state:

* `update_timestamp`: this core's `CUR_TIME` and `CONSUMED`;
* `check_budget` writes nothing (`check_budget_suf`; `CUR_SC` is kept by the timestamp update);
* `handle_interrupt`: this core's `REPROGRAM` and `ARMED` (`handle_interrupt_timer_writes`; the IRQ's state word
  is a kernel-global word, kept by the timestamp update: `ks_word_val`, `ks_ne_node`);
* `schedule` is `schedTail` (`irq_quiet_schedule`), which writes this core's node words and the current SC
  (`schedTail_fp`: the current thread runs on the current SC, `current_ok`);
* `activate_thread` (`activate_fp`): a current thread in `Restart` gets its `NEXT_IP` and state written (and
  possibly the action); else nothing;
* `vcpu::check` of a thread not running a VM writes nothing (`vcpu_check_nvm`).

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqQ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-- A kernel-global word below the nodes does not wrap. -/
theorem ks_word_val {s : S} {c i : U64} (hN : NodePlaced st T s c) (hi : i.val < 13568) :
    (core.num.U64.wrapping_add (L.ksb s) i).val = (L.ksb s).val + i.val := by
  have := hN.fits
  simp only [LawfulStore.nodeBase] at this
  have hk := (L.ksb s).hBounds
  have hc := c.hBounds
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, UScalar.size] at hk hc ⊢
  omega

theorem ks_ne_node {s : S} {c i o : U64} (hN : NodePlaced st T s c) (hi : i.val < 13568) (ho : o.val < 4288) :
    core.num.U64.wrapping_add (L.ksb s) i ≠ L.nodeAt s c o := by
  intro e
  have e' := congrArg UScalar.val e
  rw [ks_word_val hN hi, nodeAt_val hN ho] at e'
  simp only [LawfulStore.nodeBase] at e'
  omega

theorem ks_aligned {s : S} {c i : U64} (hN : NodePlaced st T s c) (hi : i.val < 13568) (h8 : i.val % 8 = 0) :
    Aligned (core.num.U64.wrapping_add (L.ksb s) i) := by
  have := hN.align
  simp only [LawfulStore.nodeBase] at this
  unfold Aligned
  rw [ks_word_val hN hi]
  omega

/-- `schedule_tcb` writes nothing or sets the action to `CHOOSE_NEW`. -/
theorem schedule_tcb_cases {X Y : S} {t : U64} (h : sched.schedule_tcb st X t = ok Y) :
    Y = X ∨ Y = L.wr X (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) sched.ACTION_CHOOSE_NEW := by
  have hs : sched.schedule_tcb st X t ⦃ Y => Y = X ∨
      Y = L.wr X (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) sched.ACTION_CHOOSE_NEW ⦄ := by
    unfold sched.schedule_tcb
    step with sched.cur_thread.spec as ⟨t1, e1⟩
    step with tcb_eq.blk as ⟨b, eb⟩
    split
    · step with sched.action.spec as ⟨i, ei⟩
      split
      · step with sched.is_schedulable.spec as ⟨b1, eb1⟩
        split
        · exact (WP.spec_ok _).2 (Or.inl rfl)
        · exact WP.spec_mono (sched.set_action.spec X _) fun Y e => Or.inr e
      · exact (WP.spec_ok _).2 (Or.inl rfl)
    · exact (WP.spec_ok _).2 (Or.inl rfl)
  rw [h, WP.spec_ok] at hs
  exact hs

/-- The words `activate_thread` may write for the current thread `t` (yielding to no SC): `NEXT_IP` (register
14), the state, and the action. -/
def ActW (st : machine.Store S) [L : LawfulStore st] (s0 : S) (t b : U64) : Prop :=
  b = core.num.U64.wrapping_add t 368#u64 ∨ b = stA t ∨ b = L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION

variable {A : Type _} (ar : machine.Arch A)

/-- **`activate_thread` of a current thread yielding to no SC** writes only `ActW`; afterwards its state is
`Running` or unchanged. -/
theorem activate_fp {X Y : S} {a a' : A} {t : U64} (hT : TcbPlaced T) (ht : t ∈ T)
    (hN : NodePlaced st T X (L.cpu X)) (hct : L.curW X = t) (hy : L.mem X (yieldA t) = 0#u64)
    (h : sched.activate_thread st ar X a = ok (Y, a')) :
    WritesIn st X Y (ActW st X t) ∧
      (L.mem Y (stA t) = sched.TS_RUNNING ∨ L.mem Y (stA t) = L.mem X (stA t)) := by
  have ht' := hT t ht
  unfold sched.activate_thread at h
  rw [cur_thread_ok, hct] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (obj.Tcb.yield_to.spec (L := L) X _), hy] at h
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, uncurry_apply_pair] at h
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) X _)] at h
  simp only [bind_ok] at h
  have sA : Aligned (stA t) := by rw [stA_eq]; exact field_aligned ht' (by simp) (by simp)
  by_cases hr : L.mem X (stA t) = sched.TS_RESTART
  · rw [if_pos hr] at h
    obtain ⟨pc, -, h⟩ := bind_eq_ok h
    obtain ⟨s2, e2, h⟩ := bind_eq_ok h
    obtain ⟨s3, e3, h⟩ := bind_eq_ok h
    have e := ok_inj_ff h
    simp only [Prod.mk.injEq] at e
    obtain ⟨e4, -⟩ := e
    subst e4
    have hW := obj.Tcb.set_reg.wrK (L := L) X t layout.reg.NEXT_IP pc ht' (by simp [layout.reg.NEXT_IP])
    rw [e2, WP.spec_ok] at hW
    obtain ⟨K, hK, e2'⟩ := hW
    have hK' : K = 368#u64 := by apply UScalar.eq_of_val_eq; rw [hK]; simp [layout.reg.NEXT_IP]
    subst hK' e2'
    unfold sched.set_thread_state at e3
    rw [eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ t _)] at e3
    simp only [bind_ok] at e3
    have aR : Aligned (core.num.U64.wrapping_add t 368#u64) := field_aligned ht' (by simp) (by simp)
    have aA : Aligned (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) :=
      nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val])
    rcases schedule_tcb_cases e3 with e5 | e5 <;> subst e5
    · refine ⟨((writesIn_wr aR).trans (writesIn_wr sA)).mono fun b hb => ?_, Or.inl (L.mem_wr_same sA)⟩
      rcases hb with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · have eA : L.nodeAt (L.wr (L.wr X (core.num.U64.wrapping_add t 368#u64) pc) (stA t) sched.TS_RUNNING)
          (L.cpu (L.wr (L.wr X (core.num.U64.wrapping_add t 368#u64) pc) (stA t) sched.TS_RUNNING))
          layout.node.SCHED_ACTION = L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION := by
        rw [LawfulStore.cpu_wr, LawfulStore.cpu_wr, nodeAt_of_ksb ((L.ksb_wr _ _ _).trans (L.ksb_wr _ _ _))]
      rw [eA]
      have hne : L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION ≠ stA t := by
        rw [stA_eq]; exact node_ne_field hN (by rw [act_val]; omega) ht ht' (by simp)
      refine ⟨(((writesIn_wr aR).trans (writesIn_wr sA)).trans (writesIn_wr aA)).mono fun b hb => ?_,
        Or.inl ?_⟩
      · rcases hb with (rfl | rfl) | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · rw [mem_wr_ne' aA sA hne, L.mem_wr_same sA]
  · rw [if_neg hr] at h
    have e := ok_inj_ff h
    simp only [Prod.mk.injEq] at e
    obtain ⟨e4, -⟩ := e
    subst e4
    exact ⟨WritesIn.refl _ _, Or.inr rfl⟩

/-- `vcpu::check` of a thread not running a VM writes nothing. -/
theorem vcpu_check_nvm (X : S) (a : A) {t : U64} (hs : L.mem X (stA t) ≠ sched.TS_RUNNING_VM) :
    vcpu.check st ar X a t = ok (X, a) := by
  unfold vcpu.check
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) X _)]
  have hne : (L.mem X (stA t) != sched.TS_RUNNING_VM) = true := bne_iff_ne.mpr hs
  simp only [bind_ok, hne, ↓reduceIte]

end

section main
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type _} (ar : machine.Arch A)

set_option maxHeartbeats 16000000 in
/-- **The quiet case of an accepted timer interrupt writes only its footprint** `FootLt` (any `Lk`), from a
state with the P1 invariant; the hypotheses are `irq_accept_walk`'s equations with `IrqCase.quiet`. -/
theorem irq_quiet_foot (hA : P0.ArchTotal ar) {Lk : List (U64 × Nat)} {s s1 s2 s3 s4 s5 s' : S}
    {a a1 a2 a3 a4 a5 a' : A} {cpu mx irq ct csc now i2 t : U64} {x : Bool}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ecpu : st.cur_cpu s = ok cpu) (emx : layout.irq.MAX = ok mx)
    (hle : ¬ irq > mx) (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
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
    InFootLt st T Scs Z Lk s s' := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
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
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := by
    obtain ⟨hP, hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    obtain ⟨a1', a2', a3'⟩ := maxA_facts hO hcs
    exact ⟨(hS.all _ hcs).1, fun b hb hi => hS.sub _ ((hS.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩, by unfold Aligned; rw [hv, hcv]; omega⟩, ⟨a2', a3'⟩, a1'⟩
  -- `s → s1`: the timestamp update
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
  simp only at er
  have k1 : L.ksb s1 = L.ksb s := by rw [er, utW_ksb]
  have c1 : L.cpu s1 = L.cpu s := by rw [er, utW_cpu]
  have m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b :=
    fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [er]; exact utW_placed hN n1
  have e1N : ∀ o, L.nodeAt s1 (L.cpu s1) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c1, nodeAt_of_ksb k1]
  have f01 : WritesIn st s s1 (FootLt st T Scs Z Lk s) := by
    obtain ⟨hct, hcn, -⟩ := ct_cn hN
    rw [er]; unfold utW
    refine ((writesIn_wr hct).trans (writesIn_wr hcn)).mono fun b hb => ?_
    rcases hb with rfl | rfl
    · exact footLt_node (by simp [layout.node.CUR_TIME])
    · exact footLt_node (by simp [layout.node.CONSUMED])
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
  -- `schedule`
  have hfp := schedTail_fp ar hA s3 a3 (zc := Z (L.cscW s))
    (B := fun b => FootLt st T Scs Z Lk s b ∧
      (∀ K : U64, K.val < 4096 → b ≠ core.num.U64.wrapping_add (L.curW s) K) ∧
      b ≠ L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
    (by rw [c3]; exact hcC) (by rw [c3]; exact hN.ksb k3) hT (fun b hb => (h0.omega b hb).ksb k3)
    (by rw [hcur3]; exact hcT) (by rw [hcur3, hsc3, hcs3]; exact hsct) (by rw [hcs3]; exact SCq.agree hcq hout3)
    (fun o ho h8 hz => by
      rw [e3N]
      refine ⟨footLt_node ho, fun K hK => node_ne_field hN ho hcT ht' hK, fun e => hz ?_⟩
      have e' := congrArg UScalar.val e
      rw [nodeAt_val hN ho, nodeAt_val hN (by rw [curth_val]; omega), curth_val] at e'
      omega)
    (fun b hb hin => by
      rw [hcs3] at hin
      have ho := h0.omega b (hcq.2.1 b hb hin)
      exact ⟨footLt_sc hcs hcore hin, fun K hK e => out_ne_field ho hcT ht' hK (congrArg UScalar.val e).symm,
        fun e => out_ne_node ho hcC hN (by rw [curth_val]; omega) (congrArg UScalar.val e).symm⟩)
  rw [← hsch, esc, WP.spec_ok] at hfp
  have w34 := hfp
  have k4 : L.ksb s4 = L.ksb s := w34.1.trans k3
  have c4 : L.cpu s4 = L.cpu s := w34.2.1.trans c3
  have hcur4 : L.curW s4 = L.curW s := by
    have h3 := hcur3
    unfold LawfulStore.curW at h3 ⊢
    rw [e3N] at h3
    rw [w34.2.1, nodeAt_of_ksb w34.1, e3N,
      w34.mem_eq (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) (fun hb => hb.2.2 rfl)]
    exact h3
  have tK4 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s4 (core.num.U64.wrapping_add (L.curW s) K) = L.mem s3 (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K hK h8 => w34.mem_eq (field_aligned ht' hK h8) (fun hb => hb.2.1 K hK rfl)
  have hy4 : L.mem s4 (yieldA (L.curW s)) = 0#u64 := by
    unfold yieldA
    rw [tK4 _ (by simp) (by simp), htcb3 hcT (by simp) (by simp)]
    exact hy0
  have hst4 : L.mem s4 (stA (L.curW s)) = L.mem s (stA (L.curW s)) := by
    rw [stA_eq, tK4 _ (by simp) (by simp), htcb3 hcT (by simp) (by simp)]
  have hN4 : NodePlaced st T s4 (L.cpu s4) := by rw [c4]; exact hN.ksb k4
  -- `activate_thread`
  obtain ⟨w45, hst5⟩ := activate_fp ar hT hcT hN4 hcur4 hy4 eac
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
  have hst5' : L.mem s5 (stA (L.curW s)) ≠ sched.TS_RUNNING_VM := by
    rcases hst5 with e | e
    · rw [e]; simp [sched.TS_RUNNING, sched.TS_RUNNING_VM]
    · rw [e, hst4]; exact hnvm
  -- `vcpu::check`
  rw [cur_thread_ok, hcur5] at et
  have et' := ok_inj_ff et
  subst et'
  rw [vcpu_check_nvm ar s5 a5 hst5'] at evc
  have e9 := ok_inj_ff evc
  simp only [Prod.mk.injEq] at e9
  obtain ⟨e9a, -⟩ := e9
  subst e9a
  -- the footprint
  have f13 : WritesIn st s1 s3 (FootLt st T Scs Z Lk s) := w13.mono fun b hb => by
    obtain ⟨o, -, ho, -, rfl⟩ := hb
    rw [e1N]; exact footLt_node ho
  have f34 : WritesIn st s3 s4 (FootLt st T Scs Z Lk s) := w34.mono fun b hb => hb.1
  have f45 : WritesIn st s4 s5 (FootLt st T Scs Z Lk s) := w45.mono fun b hb => by
    rcases hb with rfl | rfl | rfl
    · exact footLt_thr hcT haff (by simp) (by simp) (by simp) (by simp)
    · rw [stA_eq]; exact footLt_thr hcT haff (by simp) (by simp) (by simp) (by simp)
    · have e : L.nodeAt s4 (L.cpu s4) layout.node.SCHED_ACTION = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION := by
        rw [c4, nodeAt_of_ksb k4]
      rw [e]; exact footLt_node (by rw [act_val]; omega)
  exact ((f01.trans1 f13).trans1 f34).trans1 f45

end main

end Fl4Proofs.P2
