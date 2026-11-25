/-
P2 (p2je): **the `TCB_SetTimer` local entry ends in `AllCores`**
(`localtimer.handle_set_timer_local`, accepted).

The body before `schedule`: the caller `t` (the current thread, `RUNNING`)
gets its `FAULT_IP` written, `update_timestamp`, `set_thread_state t
RESTART`, `timer.insert target`, `reply_success_empty t`, `set_thread_state t
RUNNING`. Each step is a `KWN` footprint over `KI` in no-donation mode (`t`
is not protected: its affinity is the executing core and it is not the idle
thread, being `RUNNING`), a `KWB` footprint without endpoint words, keeps
P1's `BlkOK`, and leaves the action kept or `CHOOSE_NEW`.

* `obj.Tcb.set_reg.nb`, `sched.set_thread_state.nb`, `timer.insert.nb`,
  `msg.reply_success_empty.nb`: the steps.
* `set_timer_tail`: from the run's equations of the body and `schedule`,
  `AllCores` at `schedule`'s end (via `AllCores.schedB`).
* **`set_timer_local.allCores`**: an accepted run ends `schedule` in
  `AllCores` (followed by `finish`'s `activate_thread` and `vcpu::check`).

Inputs: `AllCores s0`, P1's `EntryInv` and `BufAt` at the entry, and
`target ∈ T` (fl4-sync's contract: the lookup found a thread cap; as P1's
`set_timer_local_triple`). Named premises: `hR` [J] (as
`timer_irq_local.allCores`, at an `EntryEnd` state), `hS0` [W].
-/
import Fl4Proofs.P2.EntryIrq
import Fl4Proofs.P1.QueueInvAll
import Fl4Proofs.P1.QueueInvoke
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es Eb U : Set U64}
variable {A : Type _} {ar : machine.Arch A} {Kp : Set U64} {Nd : Prop}

/-- A register write of a TCB. -/
theorem obj.Tcb.set_reg.nb (s : S) {t r v : U64} (hr : r.val < 384) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) :
    obj.Tcb.set_reg st t s r v ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootN st Kp Nd T Cs Sg Scs Z Es s s' ∧ FootB st T Cs Sg Scs Z Eb s s' ∧ L.actionW s' = L.actionW s ∧
      L.mem s' (stA t) = L.mem s (stA t) ⦄ := by
  have hq := h.1.choose_spec.choose_spec
  refine WP.spec_mono (WP.spec_and (obj.Tcb.set_reg.blk s hr h ht) (obj.Tcb.set_reg.wrK s t r v (hq.tcbs t ht) hr)) ?_
  rintro s' ⟨⟨hb, hst⟩, K, hK, rfl⟩
  exact ⟨hb, footN_field hq.tcbs hq.nodes hq.cur ht (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
      (PrF.of_ne (by omega) (by omega) (by omega) (by omega)),
    footB_field hq.tcbs ht (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩,
    actionW_field hq.tcbs hq.nodes hq.cur ht (by omega) (by omega), hst⟩

/-- `set_thread_state` of an unprotected thread. -/
theorem sched.set_thread_state.nb {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S) (t : obj.Tcb) (v : U64)
    (hq : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T) (hKt : t ∉ Kp) :
    sched.set_thread_state st s t v ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ∧ FootB st T Cs Sg Scs Z Eb s s' ∧
      (L.actionW s' = L.actionW s ∨ L.actionW s' = sched.ACTION_CHOOSE_NEW) ⦄ :=
  WP.spec_mono (WP.spec_and (WP.spec_and (sched.set_thread_state.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs)
      (Z := Z) (Es := Es) s t v hq ht hKt) (sched.set_thread_state.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Eb)
      s t v hq ht)) (sched.set_thread_state.w2 s t v hq.tcbs (hq.nodes _ hq.cur) ht))
    fun _ hh => ⟨hh.1.1, hh.1.2, hh.2.2.1⟩

/-- `timer.insert`: the timer words and the current node's `REPROGRAM`. -/
theorem timer.insert.nb (s : S) (tg d bd : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : tg ∈ T) :
    timer.insert st s tg d bd ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootN st Kp Nd T Cs Sg Scs Z Es s s' ∧ FootB st T Cs Sg Scs Z Eb s s' ∧ L.actionW s' = L.actionW s ∧
      ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ⦄ := by
  have hq := h.1.choose_spec.choose_spec
  have hT := hq.tcbs
  have NP := hq.nodes
  have hN := NP _ hq.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  refine WP.spec_mono (timer.insert.foot s tg d bd h.tinv ht) ?_
  rintro s' ⟨hb, -, w, -⟩
  have ea : L.actionW s' = L.actionW s := by
    refine actionW_of w hN ?_
    rintro ((⟨y, hy, K, h1, h2, e⟩ | ⟨c, hc', o, ho, e⟩) | e)
    · exact node_ne_field hN (by rw [act_val]; omega) hy (hT y hy) (by omega) e
    · exact node_ne_node hN (NP c hc') (by rw [act_val]; omega) (by omega)
        (fun _ => by rw [act_val]; omega) (congrArg UScalar.val e)
    · exact node_ne_node hN hN (by rw [act_val]; omega) (by rw [rp]; omega)
        (fun _ => by rw [act_val, rp]; omega) (congrArg UScalar.val e)
  refine ⟨hb, FootN.of' w (fun b _ hh => ?_) (AcK.of_eq ea), FootB.of' w (fun b _ hh => ?_), ea, fun y hy => ?_⟩
  · rcases hh with hh | rfl
    · exact TW.kwN hT NP hh
    · exact ⟨kw_node hq.cur (by rw [rp]; omega) (by rw [rp]; omega),
        notIdW_node NP hq.cur (by rw [rp]; omega) (idOff_ge (by rw [rp]; omega))⟩
  · rcases hh with (⟨y, hy, K, h1, h2, rfl⟩ | ⟨c, hc, o, ho, rfl⟩) | rfl
    · exact kwB_field hy (by omega) (by omega) ⟨by omega, by omega, by omega⟩
    · exact kwB_node hc (by omega) (by omega)
    · exact kwB_node hq.cur (by rw [rp]; omega) (by rw [rp]; omega)
  · refine w.mem_eq (by rw [stA_eq]; exact field_aligned (hT y hy) (by simp) (by simp)) ?_
    rintro ((⟨y', hy', K, h1, h2, e⟩ | ⟨c, hc', o, ho, e⟩) | e)
    · rw [stA_eq] at e
      exact field_ne (hT y hy) (hT y' hy') (by simp) (by omega) (fun _ => by simp; omega) e
    · rw [stA_eq] at e
      exact node_ne_field (NP c hc') (by omega) hy (hT y hy) (by simp) e.symm
    · rw [stA_eq] at e
      exact node_ne_field hN (by rw [rp]; omega) hy (hT y hy) (by simp) e.symm

/-- `reply_success_empty t`: two register writes of `t`. -/
theorem msg.reply_success_empty.nb (s : S) (t : obj.Tcb) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    msg.reply_success_empty st s t ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootN st Kp Nd T Cs Sg Scs Z Es s s' ∧ FootB st T Cs Sg Scs Z Eb s s' ∧ L.actionW s' = L.actionW s ∧
      L.mem s' (stA t) = L.mem s (stA t) ⦄ := by
  unfold msg.reply_success_empty
  refine WP.spec_bind (obj.Tcb.set_reg.nb (Kp := Kp) (Nd := Nd) (Es := Es) (Eb := Eb) s
    (r := layout.reg.BADGE) (by simp [layout.reg.BADGE, layout.reg.RDI]) h ht) fun s1 h1 => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 0#u64 0#u64 0#u64 0#u64) fun mi _ => ?_
  unfold msg.set_msg_info
  refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 mi) fun w _ => ?_
  refine WP.spec_mono (obj.Tcb.set_reg.nb (Kp := Kp) (Nd := Nd) (Es := Es) (Eb := Eb) s1
    (r := layout.reg.MSG_INFO) (v := w) (by simp [layout.reg.MSG_INFO, layout.reg.RSI]) h1.1 ht) fun s2 h2 => ?_
  exact ⟨h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.trans h1.2.2.2.2⟩

theorem tsRunning_ne_idle : sched.TS_RUNNING ≠ sched.TS_IDLE := by
  unfold sched.TS_RUNNING sched.TS_IDLE; decide

theorem tsRunning_ne_bor : sched.TS_RUNNING ≠ sched.TS_BLOCKED_ON_REPLY := by
  unfold sched.TS_RUNNING sched.TS_BLOCKED_ON_REPLY; decide

set_option maxHeartbeats 4000000 in
/-- **The body and `schedule` of an accepted `TCB_SetTimer` local entry**,
from the run's equations: `AllCores` at `schedule`'s end. Named premises:
`hR` [J], `hS0` [W]. -/
theorem set_timer_tailB (hA : P0.ArchTotal ar) (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s1 s2 s3 s4 s5 s6 s7 : S} {a0 a1 a2 : A} {t tg d bd v : U64}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0) (htg : tg ∈ T)
    (hR : ∀ (s : S) (a : A), EntryEnd st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
      ∀ r : S × A, sched.awaken st ar s a = ok r → L.actionW r.1 = 0#u64 → SchCur st r.1)
    (ect : sched.cur_thread st s0 = ok t) (hrun : L.mem s0 (stA t) = sched.TS_RUNNING)
    (es1 : obj.Tcb.set_reg st t s0 layout.reg.FAULT_IP v = ok s1)
    (eu : sched.update_timestamp st ar s1 a0 = ok (s2, a1))
    (es3 : sched.set_thread_state st s2 t sched.TS_RESTART = ok s3)
    (es4 : timer.insert st s3 tg d bd = ok s4)
    (es5 : msg.reply_success_empty st s4 t = ok s5)
    (es6 : sched.set_thread_state st s5 t sched.TS_RUNNING = ok s6)
    (esc : sched.schedule st ar s6 a1 = ok (s7, a2)) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s6 ∧ BufAt st T Cs H Sg Scs Z U s6 ∧
      AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s7 := by
  have ect' : t = L.curW s0 := by
    obtain ⟨w, ew, hw⟩ := spec_ex_fd (sched.cur_thread.spec (st := st) s0)
    rw [ect] at ew; cases ok_inj_ff ew; exact hw
  have hI0c := hI0
  obtain ⟨⟨Q0, R0, hq0⟩, hB0', hX0, hS0', -, -, -, -⟩ := hI0c
  have hSg0 : SgOK st Ω Sg s0 := hS0'.sg
  have hB0 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s0 := ⟨⟨Q0, R0, hq0⟩, hB0', hX0, hS0', hSg0⟩
  have hT := hq0.tcbs
  have htT : t ∈ T := by rw [ect']; exact hq0.curT
  have hKt : t ∉ KI st T Cs (L.cpu s0) s0 := by
    rintro (hK | hI)
    · rw [ect'] at hK; exact h0.notK (h0.curAff _ hcpu) hK
    · have hid := h0.idleSt _ hcpu
      rw [← hI, hrun] at hid
      exact tsRunning_ne_idle hid
  -- the `FAULT_IP` write
  have S1 := obj.Tcb.set_reg.nb (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Es := EH H) (Eb := (∅ : Set U64)) s0
    (r := layout.reg.FAULT_IP) (v := v) (by simp [layout.reg.FAULT_IP]) hB0 htT
  rw [es1] at S1
  simp only [WP.spec_ok] at S1
  obtain ⟨hB1, F1, B1, ea1, est1⟩ := S1
  -- `update_timestamp`
  obtain ⟨⟨Q1, R1, hq1⟩, hBd1, hX1, hS1, hSg1⟩ := hB1
  have U2 := sched.update_timestamp.bxc hA s1 a0 ⟨⟨Q1, R1, hq1⟩, hBd1, hX1, hSg1, hS1⟩
  have U3 := sched.update_timestamp.kwN (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) hA s1 a0 hq1.nodes hq1.cur
  have U3t := sched.update_timestamp.kwN (Kp := ({t} : Set U64)) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) hA s1 a0 hq1.nodes hq1.cur
  have U4 := sched.update_timestamp.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := (∅ : Set U64)) hA s1 a0
    (hq1.nodes _ hq1.cur) hq1.cur
  rw [eu] at U2 U3 U3t U4
  simp only [WP.spec_ok, WP.uncurry'_pair] at U2 U3 U3t U4
  obtain ⟨⟨⟨⟨Q2, R2, hq2⟩, hBd2, hX2, hSg2, hS2⟩, -, -⟩, n2, -⟩ := U2
  have ea2 : L.actionW s2 = L.actionW s1 := n2.1
  have est2 : L.mem s2 (stA t) = sched.TS_RUNNING := by
    rw [U3t.idKeep (by rw [stA_eq]; exact field_aligned (hT t htT) (by simp) (by simp))
      (Or.inr (Or.inl ⟨t, htT, hT t htT, Set.mem_singleton t, Or.inl rfl⟩)), est1, hrun]
  have hB2 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 := ⟨⟨Q2, R2, hq2⟩, hBd2, hX2, hS2, hSg2⟩
  -- `set_thread_state t RESTART`
  have R3 := sched.set_thread_state.restart_blk (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s2 t hB2 htT
    (by rw [est2]; exact fun hb => not_runnable_of_blocked hb (Or.inl rfl)) (by rw [est2]; exact tsRunning_ne_bor)
  have N3 := sched.set_thread_state.nb (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) (Eb := (∅ : Set U64)) s2 t sched.TS_RESTART hq2 htT hKt
  rw [es3] at R3 N3
  simp only [WP.spec_ok] at R3 N3
  obtain ⟨hB3, -, est3, -⟩ := R3
  obtain ⟨F3, B3, ea3⟩ := N3
  -- `timer.insert target`
  have I4 := timer.insert.nb (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) (Eb := (∅ : Set U64)) s3 tg d bd hB3 htg
  rw [es4] at I4
  simp only [WP.spec_ok] at I4
  obtain ⟨hB4, F4, B4, ea4, est4⟩ := I4
  -- `reply_success_empty t`
  have P5 := msg.reply_success_empty.nb (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) (Eb := (∅ : Set U64)) s4 t hB4 htT
  rw [es5] at P5
  simp only [WP.spec_ok] at P5
  obtain ⟨hB5, F5, B5, ea5, est5⟩ := P5
  -- `set_thread_state t RUNNING`
  obtain ⟨⟨Q5, R5, hq5⟩, hBd5, hX5, hS5, hSg5⟩ := hB5
  have R6 := sched.set_thread_state.running_bxi ⟨⟨Q5, R5, hq5⟩, hBd5, hX5, hSg5, hS5⟩ htT
    (by rw [est5, est4 t htT, est3])
  have N6 := sched.set_thread_state.nb (Kp := KI st T Cs (L.cpu s0) s0) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) (Eb := (∅ : Set U64)) s5 t sched.TS_RUNNING hq5 htT hKt
  rw [es6] at R6 N6
  simp only [WP.spec_ok] at R6 N6
  obtain ⟨⟨Q6, R6', hq6⟩, hBd6, hX6, hSg6, hS6⟩ := R6
  obtain ⟨F6, B6, ea6⟩ := N6
  -- the body's end
  have F06 : FootN st (KI st T Cs (L.cpu s0) s0) True T Cs Sg Scs Z (EH H) s0 s6 :=
    F1.trans (U3.trans (F3.trans (F4.trans (F5.trans F6))))
  have B06 : FootB st T Cs Sg Scs Z ∅ s0 s6 := B1.trans (U4.trans (B3.trans (B4.trans (B5.trans B6))))
  have hBlk6 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s6 := ⟨⟨Q6, R6', hq6⟩, hBd6, hX6, hS6, hSg6⟩
  have hBA6 : BufAt st T Cs H Sg Scs Z U s6 :=
    BufAt.of_fr hBA0 (IbFr.of_bufKeep B06.1
      (BufKeep.of_footB hq0 hX0.1 hSg0.sub (fun e' he' => absurd he' (Set.notMem_empty e')) B06))
  have hcn : sched.ACTION_CHOOSE_NEW ∉ T := notT_small hT (by simp)
  have ea05 : L.actionW s5 = L.actionW s0 ∨ L.actionW s5 = sched.ACTION_CHOOSE_NEW := by
    rw [ea5, ea4]
    rcases ea3 with e3 | e3
    · exact Or.inl (by rw [e3, ea2, ea1])
    · exact Or.inr e3
  have hsa6 : ActAff st T s6 := by
    refine ActAff.nT ?_
    rcases ea6 with e6 | e6
    · rw [e6]
      rcases ea05 with e5 | e5
      · rw [e5]; exact h0.actNT _ hcpu
      · rw [e5]; exact hcn
    · rw [e6]; exact hcn
  have W := AllCores.schedB hA IK hNt a1 h0 hcpu hS0 hB0 F06 hBlk6 hBA6 hsa6 (hR s6 a1 ⟨hBlk6, F06, B06⟩)
  rw [esc] at W
  simp only [WP.spec_ok, WP.uncurry'_pair] at W
  exact ⟨hBlk6, hBA6, W⟩

/-- `set_timer_tailB`'s `AllCores` at `schedule`'s end. -/
theorem set_timer_tail (hA : P0.ArchTotal ar) (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s1 s2 s3 s4 s5 s6 s7 : S} {a0 a1 a2 : A} {t tg d bd v : U64}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0) (htg : tg ∈ T)
    (hR : ∀ (s : S) (a : A), EntryEnd st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
      ∀ r : S × A, sched.awaken st ar s a = ok r → L.actionW r.1 = 0#u64 → SchCur st r.1)
    (ect : sched.cur_thread st s0 = ok t) (hrun : L.mem s0 (stA t) = sched.TS_RUNNING)
    (es1 : obj.Tcb.set_reg st t s0 layout.reg.FAULT_IP v = ok s1)
    (eu : sched.update_timestamp st ar s1 a0 = ok (s2, a1))
    (es3 : sched.set_thread_state st s2 t sched.TS_RESTART = ok s3)
    (es4 : timer.insert st s3 tg d bd = ok s4)
    (es5 : msg.reply_success_empty st s4 t = ok s5)
    (es6 : sched.set_thread_state st s5 t sched.TS_RUNNING = ok s6)
    (esc : sched.schedule st ar s6 a1 = ok (s7, a2)) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s7 :=
  (set_timer_tailB hA IK hNt h0 hcpu hS0 hI0 hBA0 htg hR ect hrun es1 eu es3 es4 es5 es6 esc).2.2

set_option maxHeartbeats 4000000 in
/-- **The `TCB_SetTimer` local entry ends `schedule` in `AllCores`**
(module docstring). Named premises: `hR` [J], `hS0` [W]. -/
theorem set_timer_local.allCoresB (hA : P0.ArchTotal ar) (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {n : I64} {target : U64}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0) (htg : target ∈ T)
    (hR : ∀ (s : S) (a : A), EntryEnd st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
      ∀ r : S × A, sched.awaken st ar s a = ok r → L.actionW r.1 = 0#u64 → SchCur st r.1)
    (e : localtimer.handle_set_timer_local st ar s0 a0 n target = ok (true, s', a')) :
    ∃ s3 a3 s4 a4, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ BufAt st T Cs H Sg Scs Z U s3 ∧
      sched.schedule st ar s3 a3 = ok (s4, a4) ∧ AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧
      (do
        let (s5, a5) ← sched.activate_thread st ar s4 a4
        let t ← sched.cur_thread st s5
        vcpu.check st ar s5 a5 t) = ok (s', a') := by
  have h := e
  unfold localtimer.handle_set_timer_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, ect, h⟩ := bind_eq_ok h
  obtain ⟨cpu, -, h⟩ := bind_eq_ok h
  obtain ⟨info, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases cn : (n != fl4_abi.syscall.SysCall) = true
  · rw [if_pos cn] at h; simp at h
  rw [if_neg cn] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  by_cases c2 : (info.label != fl4_abi.label.TCBSetTimer) = true
  · rw [if_pos c2] at h; simp at h
  rw [if_neg c2] at h
  by_cases c3 : (info.extra_caps != 0#u64) = true
  · rw [if_pos c3] at h; simp at h
  rw [if_neg c3] at h
  by_cases c4 : info.length < 2#u64
  · rw [if_pos c4] at h; simp at h
  rw [if_neg c4] at h
  obtain ⟨csc, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  by_cases c5 : (i2 != sched.TS_RUNNING) = true
  · rw [if_pos c5] at h; simp at h
  rw [if_neg c5] at h
  have hi2 : i2 = sched.TS_RUNNING := by simp only [bne_iff_ne, ne_eq, not_not] at c5; exact c5
  have hrun : L.mem s0 (stA t) = sched.TS_RUNNING := by
    obtain ⟨w, ew, hw⟩ := spec_ex_fd (obj.Tcb.state.spec (st := st) s0 t)
    rw [ei2] at ew
    rw [← hw, ← ok_inj_ff ew, hi2]
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨nx, -, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, -, h⟩ := bind_eq_ok h
  obtain ⟨dl, -, h⟩ := bind_eq_ok h
  obtain ⟨bd, -, h⟩ := bind_eq_ok h
  obtain ⟨cns, -, h⟩ := bind_eq_ok h
  obtain ⟨b4, -, h⟩ := bind_eq_ok h
  cases b4
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b5, -, h⟩ := bind_eq_ok h
  cases b5
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨b6, -, h⟩ := bind_eq_ok h
  cases b6
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  -- both deadline arms run the same tail (as P1 `set_timer_local_same`)
  have tail : (do
      let s3 ← sched.set_thread_state st s2 t sched.TS_RESTART
      let s4 ← timer.insert st s3 target dl bd
      let s5 ← msg.reply_success_empty st s4 t
      let s6 ← sched.set_thread_state st s5 t sched.TS_RUNNING
      let (s7, a2) ← sched.schedule st ar s6 a1
      let (s8, a3) ← sched.activate_thread st ar s7 a2
      let t1 ← sched.cur_thread st s8
      let (s9, a4) ← vcpu.check st ar s8 a3 t1
      ok (true, s9, a4)) = ok (true, s', a') := by
    by_cases cd : (dl != 0#u64) = true
    · rw [if_pos cd] at h
      by_cases cd2 : dl <= now
      · rw [if_pos cd2] at h; simp at h
      · rw [if_neg cd2] at h; exact h
    · rw [if_neg cd] at h; exact h
  clear h
  obtain ⟨s3, es3, h⟩ := bind_eq_ok tail
  obtain ⟨s4, es4, h⟩ := bind_eq_ok h
  obtain ⟨s5, es5, h⟩ := bind_eq_ok h
  obtain ⟨s6, es6, h⟩ := bind_eq_ok h
  obtain ⟨⟨s7, a2⟩, esc, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s8, a3⟩, eac, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨t1, et, h⟩ := bind_eq_ok h
  obtain ⟨⟨s9, a4⟩, evc, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  have e6 := ok_inj_ff h
  simp only [Prod.mk.injEq, true_and] at e6
  obtain ⟨rfl, rfl⟩ := e6
  obtain ⟨hB6, hBA6, W⟩ := set_timer_tailB hA IK hNt h0 hcpu hS0 hI0 hBA0 htg hR ect hrun es1 eu es3 es4 es5 es6 esc
  refine ⟨s6, a1, s7, a2, hB6, hBA6, esc, W, ?_⟩
  rw [eac]; simp only [bind_ok, uncurry_apply_pair]
  rw [et]; simp only [bind_ok]
  exact evc


set_option maxHeartbeats 4000000 in
/-- **The `TCB_SetTimer` local entry ends `schedule` in `AllCores`**
(module docstring). Named premises: `hR` [J], `hS0` [W]. -/
theorem set_timer_local.allCores (hA : P0.ArchTotal ar) (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {n : I64} {target : U64}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0) (htg : target ∈ T)
    (hR : ∀ (s : S) (a : A), EntryEnd st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
      ∀ r : S × A, sched.awaken st ar s a = ok r → L.actionW r.1 = 0#u64 → SchCur st r.1)
    (e : localtimer.handle_set_timer_local st ar s0 a0 n target = ok (true, s', a')) :
    ∃ s4 a4, AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧
      (do
        let (s5, a5) ← sched.activate_thread st ar s4 a4
        let t ← sched.cur_thread st s5
        vcpu.check st ar s5 a5 t) = ok (s', a') := by
  obtain ⟨-, -, s4, a4, -, -, -, W, E⟩ := set_timer_local.allCoresB hA IK hNt h0 hcpu hS0 hI0 hBA0 htg hR e
  exact ⟨s4, a4, W, E⟩

end

end Fl4Proofs.P2.Stall
