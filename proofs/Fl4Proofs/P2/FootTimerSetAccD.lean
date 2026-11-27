/-
# P2 (line p3mc, gen 19): an accepted `TCB_SetTimer` run with the deadline write premise at the target only

`set_timer_accG` (P2/FootTimerSetAcc) asks the store `gS` to answer a `TIMER_DEADLINE` write as `st` for **every**
timer key (`hwD`: the target and the armed threads of the current core's tree, possibly other cores' threads). The
run writes the target's deadline only (`timer::remove` / `timer::insert` of the target): **`set_timer_accGD`** is
`set_timer_accG` with `hwD` asked at the target alone, the same proof over P2/FootTimerGED's `TC` (key predicate
`Kd := (· = target)` for deadline writes). A store that refuses other threads' deadline writes (and value-checks
the heights) still answers the run (P2/StAccVW).

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.FootTimerSetAcc
import Fl4Proofs.P2.FootTimerGED
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.GED
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2
open Fl4Proofs.P2.PathObl (guard guard_read ScAcc rhA tmA RdHead NodeSt)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

section main
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 32000000 in
/-- **An accepted `TCB_SetTimer` local path on the guarded store** (module docstring): `set_timer_accG` with the deadline write premise `hwD` at the target only. -/
theorem set_timer_accGD {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {n : I64}
    {target : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (htg : target ∈ T)
    (gRd : StOk st Scs s target → ∀ w, Aligned w → StRd st T Z s target w → R w)
    (gWr : StOk st Scs s target → ∀ w, Aligned w → StWr st T Z s target w → ¬ StDecW st T s target w → W w)
    (hD1 : StOk st Scs s target → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : StOk st Scs s target → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : StOk st Scs s target → ∀ X v, (v = sched.TS_RESTART ∨ v = sched.TS_RUNNING) →
      (L.mem X (stA (L.curW s)) = sched.TS_RUNNING ∨ L.mem X (stA (L.curW s)) = sched.TS_RESTART) →
      L.mem X (affA (L.curW s)) = L.cpu s → gS.write X (stA (L.curW s)) v = st.write X (stA (L.curW s)) v)
    (hwH : StOk st Scs s target → ∀ X y v, StKeys st T s target y →
      (L.mem X (tdA y) ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val ∧ v.val >>> 8 = (L.cpu s).val) →
      gS.write X (thA y) v = st.write X (thA y) v)
    (hwD : StOk st Scs s target → ∀ X v, L.mem X (affA target) = L.cpu s →
      L.mem s (affA target) = L.cpu s →
      (L.mem X (tdA target) ≠ 0#u64 ∨ v ≠ 0#u64 → (L.mem X (thA target)).val >>> 8 = (L.cpu s).val) →
      gS.write X (tdA target) v = st.write X (tdA target) v)
    (h : localtimer.handle_set_timer_local st ar s a n target = ok (true, s', a')) :
    localtimer.handle_set_timer_local gS ar s a n target = ok (true, s', a') := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  unfold localtimer.handle_set_timer_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨cpu, ecpu, h⟩ := bind_eq_ok h
  rw [L.cur_cpu_eq] at ecpu
  have hcpu : cpu = L.cpu s := (ok_inj_ff ecpu).symm
  subst hcpu
  obtain ⟨info, emi, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases cn : (n != fl4_abi.syscall.SysCall) = true
  · rw [if_pos cn] at h; simp at h
  rw [if_neg cn] at h
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
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
  have n1 := c1; have n2 := c2; have n3 := c3; have n4 := c4
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  by_cases c5 : (i2 != sched.TS_RUNNING) = true
  · rw [if_pos c5] at h; simp at h
  rw [if_neg c5] at h
  have n5 := c5
  have hrun : i2 = sched.TS_RUNNING := by simp only [bne_iff_ne, ne_eq, not_not] at c5; exact c5
  obtain ⟨b2, eb2, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b3, eb3, h⟩ := bind_eq_ok h
  cases b3
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨nx, enx, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  have es1r := es1
  try rw [insn_len_eq] at es1
  obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, enow, h⟩ := bind_eq_ok h
  obtain ⟨dl, edl, h⟩ := bind_eq_ok h
  obtain ⟨bd, ebd, h⟩ := bind_eq_ok h
  obtain ⟨cns, ecns, h⟩ := bind_eq_ok h
  obtain ⟨b4, eb4, h⟩ := bind_eq_ok h
  cases b4
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b5, eb5, h⟩ := bind_eq_ok h
  cases b5
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨b6, eb6, h⟩ := bind_eq_ok h
  cases b6
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨tail, hdl⟩ : (do
      let s3 ← sched.set_thread_state st s2 t sched.TS_RESTART
      let s4 ← timer.insert st s3 target dl bd
      let s5 ← msg.reply_success_empty st s4 t
      let s6 ← sched.set_thread_state st s5 t sched.TS_RUNNING
      let (s7, a2) ← sched.schedule st ar s6 a1
      let (s8, a3) ← sched.activate_thread st ar s7 a2
      let t1 ← sched.cur_thread st s8
      let (s9, a4) ← vcpu.check st ar s8 a3 t1
      ok (true, s9, a4)) = ok (true, s', a') ∧ (dl = 0#u64 ∨ now < dl) := by
    by_cases cd : (dl != 0#u64) = true
    · rw [if_pos cd] at h
      by_cases cd2 : dl <= now
      · rw [if_pos cd2] at h; simp at h
      · rw [if_neg cd2] at h; exact ⟨h, Or.inr (by scalar_tac)⟩
    · rw [if_neg cd] at h
      refine ⟨h, Or.inl ?_⟩
      simp only [bne_iff_ne, ne_eq, not_not] at cd; exact cd
  clear h
  obtain ⟨s3, es3, h⟩ := bind_eq_ok tail
  obtain ⟨s4, es4, h⟩ := bind_eq_ok h
  obtain ⟨s5, es5, h⟩ := bind_eq_ok h
  obtain ⟨s6, es6, h⟩ := bind_eq_ok h
  obtain ⟨⟨s7, a2⟩, es7, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s8, a3⟩, es8, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨t1, et1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s9, a4⟩, es9, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq, true_and] at e
  obtain ⟨rfl, rfl⟩ := e
  -- the checks
  have etc : L.curW s = t := by
    have et' := et
    rw [cur_thread_ok] at et'; exact ok_inj_ff et'
  have htT : t ∈ T := etc ▸ hcT
  have ht' := hT t htT
  obtain ⟨hmr, hsct, hcore⟩ := current_ok_true eb1
  obtain ⟨-, haff, -, -⟩ := may_run_here_true hmr
  have hy0 : L.mem s (yieldA t) = 0#u64 := mrh_yield hmr
  have ecsc' : L.cscW s = csc := by
    have e' := ecsc
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at e'; exact ok_inj_ff e'
  obtain ⟨haffg, hown⟩ := target_ok_facts eb
  have hact : L.actionW s = sched.ACTION_RESUME_CURRENT := sq_true eb3
  have hs := sched.is_schedulable.spec' (L := L) s t
  rw [eb2, WP.spec_ok] at hs
  obtain ⟨-, hsc0, hrel0, hmax0⟩ := hs rfl
  rw [hsct] at hsc0 hmax0
  -- the invariant at the entry
  have hX := hI.2.2.1
  have hS := hI.2.2.2.2
  have hO := hX.1
  have hcs : L.cscW s ∈ Scs := hX.2.2.cur
  have hcq : SCq st s Ω csc (Z csc) := by
    rw [← ecsc']
    obtain ⟨hP, hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    obtain ⟨a1', a2', a3'⟩ := maxA_facts hO hcs
    exact ⟨(hS.all _ hcs).1, fun b hb hi => hS.sub _ ((hS.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩, by unfold Aligned; rw [hv, hcv]; omega⟩, ⟨a2', a3'⟩, a1'⟩
  have hcsS : csc ∈ Scs := ecsc' ▸ hcs
  have hownS : L.mem s (tdA target) = 0#u64 ∨ FootLtArmed st s (L.cpu s) target := by
    by_cases hd : L.mem s (tdA target) = 0#u64
    · exact Or.inl hd
    · exact Or.inr ⟨hd, hown.resolve_left hd⟩
  -- the prefix
  obtain ⟨et2, tK, oK⟩ := inv_prefix ar hT hN hcC et htT es1 eu hA
  obtain ⟨KF, hKF, hW⟩ := lt_prefix ar hT hN htT es1 eu hA
  have uK : ∀ {u K : U64}, u ∈ T → K.val < 4096 → K.val % 8 = 0 → (u = t → K.val ≠ 392) →
      L.mem s2 (core.num.U64.wrapping_add u K) = L.mem s (core.num.U64.wrapping_add u K) :=
    fun huT hK h8 hne => lt_tcbK hKF hT hN htT hW huT hK h8 hne
  have k2 : L.ksb s2 = L.ksb s := hW.1
  have c2 : L.cpu s2 = L.cpu s := hW.2.1
  have hN2 : NodePlaced st T s2 (L.cpu s2) := by rw [c2]; exact hN.ksb k2
  have e2N : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c2, nodeAt_of_ksb k2]
  have pre_node : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 →
      L.mem s2 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h40 h48
    refine hW.mem_eq (nodeAt_aligned hN ho h8) ?_
    rintro (e | e | e)
    · exact tcb_node_ne hN htT ht' (by omega) ho e.symm
    · have e' := congrArg UScalar.val e
      unfold ctA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CUR_TIME])] at e'
      simp [layout.node.CUR_TIME] at e'; omega
    · have e' := congrArg UScalar.val e
      unfold cnA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CONSUMED])] at e'
      simp [layout.node.CONSUMED] at e'; omega
  have f02 : WritesIn st s s2 (FootLt st T Scs Z [] s) := hW.mono fun b hb => by
    rcases hb with rfl | rfl | rfl
    · exact footLt_thr htT haff (by omega) (by omega) (by omega) (by omega)
    · exact footLt_node (by simp [layout.node.CUR_TIME])
    · exact footLt_node (by simp [layout.node.CONSUMED])
  have agΩ2 : ∀ b ∈ Ω, L.mem s2 b = L.mem s b := fun b hb => oK b (h0.omega b hb)
  have hB2 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s2 := by
    have hI1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := by
      have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
        ht' (by simp [layout.reg.FAULT_IP])
      rw [es1, WP.spec_ok] at hW1
      obtain ⟨K, hK, e1⟩ := hW1
      have hK' : K.val = 392 := by rw [hK]; simp [layout.reg.FAULT_IP]
      rw [e1]; exact (regW_all (BXI.blk hI) htT (by omega) (by omega) (by omega)).1
    have := sched.update_timestamp.bxc hA s1 a (BlkOK.bxi hI1)
    rw [eu, WP.spec_ok] at this
    try simp only [WP.uncurry'_pair] at this
    exact this.1.1
  -- schedulable after a state write of the caller
  have sA : Aligned (stA t) := by rw [stA_eq]; exact field_aligned ht' (by simp) (by simp)
  have hmaxΩ : maxA csc ∈ Ω := hcq.2.1 _ hcq.2.2.2.2 hcq.2.2.2.1
  have schW : ∀ (X : S) (v : U64), L.mem X (scA t) = csc → L.mem X (inqA t) = L.mem s (inqA t) →
      (∀ b ∈ Ω, L.mem X b = L.mem s b) → Runnable v → sched.is_schedulable st (L.wr X (stA t) v) t = ok true := by
    intro X v e1 e2 e3 hv
    have nsc : stA t ≠ scA t := by
      rw [stA_eq, scA_eq]; exact tcb_word_ne ht' ht' (by simp) (by simp) (fun _ => by simp)
    have niq : stA t ≠ inqA t := by
      rw [stA_eq]; exact tcb_word_ne ht' ht' (K2 := 3592#u64) (by simp) (by simp) (fun _ => by simp)
    have nmx : stA t ≠ maxA csc := fun e' =>
      out_ne_field (h0.omega _ hmaxΩ) htT ht' (K := 3328#u64) (by simp) (by rw [← stA_eq, e'])
    have aS : Aligned (scA t) := by rw [scA_eq]; exact field_aligned ht' (by simp) (by simp)
    have aQ : Aligned (inqA t) := field_aligned (K := 3592#u64) ht' (by simp) (by simp)
    apply is_sched_of
    · rw [L.mem_wr_same sA]; exact hv
    · rw [mem_wr_ne' sA aS nsc, e1]; exact hsc0
    · rw [mem_wr_ne' sA aQ niq, e2]; exact hrel0
    · rw [mem_wr_ne' sA aS nsc, e1]
      show L.mem _ (maxA csc) ≠ 0#u64
      rw [mem_wr_ne' sA hcq.2.2.2.2 nmx, e3 _ hmaxΩ]; exact hmax0
  -- `s2 → s3`: the restart
  have est : stA t = core.num.U64.wrapping_add t 3328#u64 := stA_eq t
  have hrs2 : L.mem s2 (stA t) = sched.TS_RUNNING := by
    rw [est, uK htT (by simp) (by simp) (fun _ => by simp), ← est]
    have e' := ei2
    rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s t)] at e'
    rw [ok_inj_ff e']; exact hrun
  have sc2 : L.mem s2 (scA t) = csc := by
    rw [scA_eq, uK htT (by simp) (by simp) (fun _ => by simp), ← scA_eq, hsct]
  have iq2 : L.mem s2 (inqA t) = L.mem s (inqA t) := uK (K := 3592#u64) htT (by simp) (by simp) (fun _ => by simp)
  have e3 : s3 = L.wr s2 (stA t) sched.TS_RESTART := sts_sch (schW s2 _ sc2 iq2 agΩ2 (Or.inr (Or.inl rfl))) es3
  have w23 : WritesIn st s2 s3 (TRegW t) := by
    rw [e3]; exact (writesIn_wr sA).mono fun b e => ⟨3328#u64, by simp, by simp, by rw [e, est]⟩
  have hnb : ¬ Blocked (L.mem s2 (stA t)) := by
    rw [hrs2]; unfold Blocked
    simp [sched.TS_RUNNING, sched.TS_BLOCKED_ON_SEND, sched.TS_BLOCKED_ON_RECV, sched.TS_BLOCKED_ON_NTFN]
  have hnr : L.mem s2 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY := by
    rw [hrs2]; simp [sched.TS_RUNNING, sched.TS_BLOCKED_ON_REPLY]
  have hB3 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 :=
    (sched.set_thread_state.restart_ok (Es := ∅) (BXI.blk hB2) htT hnb hnr es3).1
  have k03 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 → (y = t → K.val < 256 ∨ 3328 < K.val) →
      L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y K hy hK h8 hne
    rw [treg_tcb hT htT w23 hy hK h8 hne, uK hy hK h8 (fun e => by have := hne e; omega)]
  have c3 : L.cpu s3 = L.cpu s := w23.2.1.trans c2
  have e3N : ∀ o, L.nodeAt s3 (L.cpu s3) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [c3, nodeAt_of_ksb (w23.1.trans k2)]
  have armed30 : ∀ {y : U64}, y ∈ T → FootLtArmed st s3 (L.cpu s3) y → FootLtArmed st s (L.cpu s) y := by
    intro y hy ⟨a1', a2'⟩
    have e1 : L.mem s3 (tdA y) = L.mem s (tdA y) := k03 (K := 3528#u64) hy (by simp) (by simp) (fun _ => by simp)
    have e2 : L.mem s3 (thA y) = L.mem s (thA y) := k03 (K := 3568#u64) hy (by simp) (by simp) (fun _ => by simp)
    rw [e1] at a1'; rw [e2, c3] at a2'
    exact ⟨a1', a2'⟩
  -- `s3 → s4`: the insert
  have hown3 : L.mem s3 (tdA target) = 0#u64 ∨ (L.mem s3 (thA target)).val >>> 8 = (L.cpu s3).val := by
    have e1 : L.mem s3 (tdA target) = L.mem s (tdA target) :=
      k03 (K := 3528#u64) htg (by simp) (by simp) (fun _ => by simp)
    have e2 : L.mem s3 (thA target) = L.mem s (thA target) :=
      k03 (K := 3568#u64) htg (by simp) (by simp) (fun _ => by simp)
    rw [e1, e2, c3]; exact hown
  obtain ⟨hB4, w34, hnd⟩ := insert_local hB3 htg hown3 es4
  have f34 : WritesIn st s3 s4 (FootLt st T Scs Z [] s) := w34.mono fun b hb => by
    rcases hb with ⟨o, ho, rfl⟩ | ⟨K, a1', a2', rfl⟩ | ⟨y, hy, -, harm, K, a1', a2', rfl⟩
    · rw [e3N]; exact footLt_node (by omega)
    · exact footLt_thr_tmr htg haffg a1' a2' hownS
    · exact footLt_tmr hy (armed30 hy harm) a1' a2'
  have m34 : WritesIn st s3 s4 (MidW st T s2 t) := w34.mono fun b hb => by
    rcases hb with ⟨o, ho, rfl⟩ | ⟨K, a1', a2', rfl⟩ | ⟨y, hy, -, -, K, a1', a2', rfl⟩
    · exact Or.inr (Or.inr ⟨o, ho, by rw [w23.2.1, nodeAt_of_ksb w23.1]⟩)
    · exact Or.inr (Or.inl ⟨target, htg, K, a1', a2', rfl⟩)
    · exact Or.inr (Or.inl ⟨y, hy, K, by omega, a2', rfl⟩)
  -- `s4 → s5 → s6`: the reply, the caller running again
  have w45 : WritesIn st s4 s5 (TRegW t) := reply_tr ht' es5
  have w25 : WritesIn st s2 s5 (MidW st T s2 t) := ((treg_mid w23).trans1 m34).trans1 (treg_mid w45)
  have hcC2 : L.cpu s2 ∈ Cs := c2 ▸ hcC
  have agΩ5 : ∀ b ∈ Ω, L.mem s5 b = L.mem s b := fun b hb =>
    (mid_out hT hN2 htT hcC2 w25 ((h0.omega b hb).ksb k2)).trans (agΩ2 b hb)
  have sc5 : L.mem s5 (scA t) = csc := by
    rw [scA_eq, mid_tcb hT hN2 htT w25 htT (by simp) (by simp) (by simp) (fun _ => by simp), ← scA_eq, sc2]
  have iq5 : L.mem s5 (inqA t) = L.mem s (inqA t) := by
    rw [← iq2]; exact mid_tcb (K := 3592#u64) hT hN2 htT w25 htT (by simp) (by simp) (by simp) (fun _ => by simp)
  have e6 : s6 = L.wr s5 (stA t) sched.TS_RUNNING := sts_sch (schW s5 _ sc5 iq5 agΩ5 (Or.inl rfl)) es6
  have w56 : WritesIn st s5 s6 (TRegW t) := by
    rw [e6]; exact (writesIn_wr sA).mono fun b e => ⟨3328#u64, by simp, by simp, by rw [e, est]⟩
  have w26 : WritesIn st s2 s6 (MidW st T s2 t) := w25.trans1 (treg_mid w56)
  -- the `schedule` state
  have e6N : ∀ o, L.nodeAt s6 (L.cpu s6) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [w26.2.1, nodeAt_of_ksb w26.1, e2N]
  have nodeK6 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 →
      (o.val ≠ 56 ∧ o.val ≠ 104 ∧ o.val ≠ 112) →
      L.mem s6 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h40 h48 hn
    have := mid_node hT hN2 htT w26 ho h8 hn
    rw [e2N] at this
    rw [this, pre_node o ho h8 h40 h48]
  have hct6 : L.curW s6 = t := by
    unfold LawfulStore.curW; rw [e6N]
    rw [nodeK6 _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
      (by rw [curth_val]; omega) (by rw [curth_val]; omega)]
    exact etc
  have hcs6 : L.cscW s6 = csc := by
    unfold LawfulStore.cscW LawfulStore.nodeA; rw [e6N]
    rw [nodeK6 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]
    exact ecsc'
  have hact6 : L.actionW s6 = sched.ACTION_RESUME_CURRENT := by
    unfold LawfulStore.actionW; rw [e6N]
    rw [nodeK6 _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega) (by rw [act_val]; omega)
      (by rw [act_val]; omega)]
    exact hact
  have hsc6 : L.mem s6 (scA t) = csc := by
    rw [scA_eq, mid_tcb hT hN2 htT w26 htT (by simp) (by simp) (by simp) (fun _ => by simp), ← scA_eq, sc2]
  have hst6 : L.mem s6 (stA t) = sched.TS_RUNNING := by rw [e6, L.mem_wr_same sA]
  have hy6 : L.mem s6 (yieldA t) = 0#u64 := by
    unfold yieldA
    rw [mid_tcb hT hN2 htT w26 htT (by simp) (by simp) (by simp) (fun _ => by simp),
      uK htT (by simp) (by simp) (fun _ => by simp)]
    exact hy0
  have agΩ6 : ∀ b ∈ Ω, L.mem s6 b = L.mem s b := fun b hb =>
    (mid_out hT hN2 htT hcC2 w26 ((h0.omega b hb).ksb k2)).trans (agΩ2 b hb)
  have k6 : L.ksb s6 = L.ksb s := w26.1.trans k2
  have c6 : L.cpu s6 = L.cpu s := w26.2.1.trans c2
  have hcC6 : L.cpu s6 ∈ Cs := c6 ▸ hcC
  have hN6 : NodePlaced st T s6 (L.cpu s6) := by rw [c6]; exact hN.ksb k6
  -- nothing due at the `schedule` state
  have hnow : L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.CUR_TIME) = now := by
    have e' := enow
    rw [cur_time_ok] at e'; exact ok_inj_ff e'
  have nd2 : NoDueT st s2 now := td_false (by rw [c2]; exact eb5)
  have hm2 := (TInv.tm (BXI.blk hB2)).min _ hcC2
  have nd3 : NoDueT st s3 now := nodue_keep hT hN2 htT hm2 w23 nd2
  have nd4 : NoDueT st s4 now := hnd now hdl nd3
  have hq4 := hB4.1.choose_spec.choose_spec
  have hN4 : NodePlaced st T s4 (L.cpu s4) := hq4.nodes _ hq4.cur
  have w46 : WritesIn st s4 s6 (TRegW t) := (w45.trans w56).mono fun b hb => hb.elim id id
  have nd6 : NoDueT st s6 now := nodue_keep hT hN4 htT ((TInv.tm hB4).min _ hq4.cur) w46 nd4
  have hct6' : L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.CUR_TIME) = now := by
    rw [w26.2.1, nodeAt_of_ksb w26.1,
      mid_node hT hN2 htT w26 (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
        (by simp [layout.node.CUR_TIME])]
    exact hnow
  have hT6 : L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.CUR_TIME) <
        L.mem s6 (tdA (L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.TIMER_MIN))) := by
    rw [hct6']; exact nd6
  have hR6 : RelNone st s6 := rel_keep hB2 htT w26 (rel_false (by rw [c2]; exact eb6))
  -- `schedule`
  have hfp := schedTail_fp ar hA s6 a1 (zc := Z csc)
    (B := fun b => FootLt st T Scs Z [] s b ∧ (∀ K : U64, K.val < 4096 → b ≠ core.num.U64.wrapping_add t K) ∧
      b ≠ L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
    hcC6 hN6 hT (fun b hb => (h0.omega b hb).ksb k6) (by rw [hct6]; exact htT) (by rw [hct6, hsc6, hcs6])
    (by rw [hcs6]; exact SCq.agree hcq agΩ6)
    (fun o ho h8 hz => by
      rw [e6N]
      refine ⟨footLt_node ho, fun K hK => node_ne_field hN ho htT ht' hK, fun e => hz ?_⟩
      have e' := congrArg UScalar.val e
      rw [nodeAt_val hN ho, nodeAt_val hN (by rw [curth_val]; omega), curth_val] at e'
      omega)
    (fun b hb hin => by
      rw [hcs6] at hin
      have ho := h0.omega b (hcq.2.1 b hb hin)
      exact ⟨footLt_sc hcsS hcore hin, fun K hK e => out_ne_field ho htT ht' hK (congrArg UScalar.val e).symm,
        fun e => out_ne_node ho hcC hN (by rw [curth_val]; omega) (congrArg UScalar.val e).symm⟩)
  rw [← schedule_resume ar s6 a1 hT6 hR6 hact6, es7, WP.spec_ok] at hfp
  have w67 := hfp
  -- `activate_thread`, `vcpu::check`
  have hcur7 : L.curW s7 = t := by
    have := hct6
    unfold LawfulStore.curW at this ⊢
    rw [e6N] at this
    rw [w67.2.1, nodeAt_of_ksb w67.1, e6N,
      w67.mem_eq (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) (fun hb => hb.2.2 rfl)]
    exact this
  have tK7 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s7 (core.num.U64.wrapping_add t K) = L.mem s6 (core.num.U64.wrapping_add t K) := fun K hK h8 =>
    w67.mem_eq (field_aligned ht' hK h8) (fun hb => hb.2.1 K hK rfl)
  have hst7 : L.mem s7 (stA t) = sched.TS_RUNNING := by rw [est, tK7 _ (by simp) (by simp), ← est, hst6]
  have hy7 : L.mem s7 (yieldA t) = 0#u64 := by unfold yieldA; rw [tK7 _ (by simp) (by simp)]; exact hy6
  have es8r := es8
  rw [activate_run ar s7 a2 (by rw [hcur7]; exact hy7) (by rw [hcur7]; exact hst7)] at es8
  have e8 := ok_inj_ff es8
  simp only [Prod.mk.injEq] at e8
  obtain ⟨rfl, rfl⟩ := e8
  have et1r := et1
  rw [cur_thread_ok, hcur7] at et1
  have et1' := ok_inj_ff et1
  subst et1'
  have es9r := es9
  rw [vcpu_check_run ar s7 a2 hst7] at es9
  have e9 := ok_inj_ff es9
  simp only [Prod.mk.injEq] at e9
  obtain ⟨rfl, rfl⟩ := e9
  -- the guarded store: what it admits
  have hok : StOk st Scs s target :=
    { aff := by rw [etc]; exact haff
      run := by
        rw [etc]
        have e' := ei2
        rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s t)] at e'
        rw [ok_inj_ff e']; exact hrun
      csc := hcs, core := by rw [ecsc']; exact hcore
      taff := haffg, town := hown }
  replace gRd := gRd hok
  replace gWr := gWr hok
  have hwS' := hwS hok
  rw [etc] at hwS'
  replace hwH := hwH hok
  replace hwD := hwD hok
  replace hD1 := hD1 hok
  replace hD2 := hD2 hok
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gRd _ (nodeAt_aligned hN h1 h2) (Or.inl (Or.inr ⟨o, h1, h2, rfl⟩))
  have nW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → W (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gWr _ (nodeAt_aligned hN h1 h2) (Or.inl (Or.inr ⟨o, h1, h2, rfl⟩)) (by
      rintro (e | ⟨y', hy', e | e⟩)
      · rw [etc, stA_eq] at e; exact node_ne_field hN h1 htT ht' (by simp) e
      · exact node_ne_field hN h1 hy'.1 (hT y' hy'.1) (K := 3528#u64) (by simp) e
      · exact node_ne_field hN h1 hy'.1 (hT y' hy'.1) (K := 3568#u64) (by simp) e)
  have cR : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      R (core.num.U64.wrapping_add t K) := fun K h1 h2 h3 h4 =>
    gRd _ (field_aligned ht' h2 h3) (Or.inr (Or.inl ⟨K, h1, h2, h3, h4, by rw [etc]⟩))
  have cW : ∀ K : U64, 256 ≤ K.val → K.val < 3328 → K.val % 8 = 0 → W (core.num.U64.wrapping_add t K) :=
    fun K h1 h2 h3 =>
    gWr _ (field_aligned ht' (by omega) h3) (Or.inr (Or.inl ⟨K, h1, by omega, h3, by rw [etc]⟩)) (by
      rintro (e | ⟨y', hy', e | e⟩)
      · rw [etc, stA_eq] at e
        exact tcb_word_ne ht' ht' (by omega) (by simp) (fun _ h => by simp at h; omega) e
      · exact tcb_word_ne ht' (hT y' hy'.1) (K2 := 3528#u64) (by omega) (by simp) (fun _ h => by simp at h; omega) e
      · exact tcb_word_ne ht' (hT y' hy'.1) (K2 := 3568#u64) (by omega) (by simp) (fun _ h => by simp at h; omega) e)
  have rR : ∀ r : U64, r.val < 384 → R (regA t r) := fun r hr => by
    obtain ⟨K, hK, e⟩ := regA_eq ht' hr
    rw [e]; exact cR K (by omega) (by omega) (by omega) (by omega)
  have rW : ∀ r : U64, r.val < 384 → W (regA t r) := fun r hr => by
    obtain ⟨K, hK, e⟩ := regA_eq ht' hr
    rw [e]; exact cW K (by omega) (by omega) (by omega)
  have scR : ∀ b, InSC csc (Z csc) b → Aligned b → R b := fun b hb ha =>
    gRd _ ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [ecsc']; exact hb)))))))
  have scND : ∀ b, Aligned b → InSC csc (Z csc) b → ¬ StDecW st T s target b := fun b ha hb => by
    have ho := h0.omega b (hcq.2.1 b ha hb)
    rintro (e | ⟨y', hy', e | e⟩)
    · rw [etc, stA_eq] at e; exact out_ne_field ho htT ht' (by simp) (congrArg UScalar.val e).symm
    · exact out_ne_field ho hy'.1 (hT y' hy'.1) (K := 3528#u64) (by simp) (congrArg UScalar.val e).symm
    · exact out_ne_field ho hy'.1 (hT y' hy'.1) (K := 3568#u64) (by simp) (congrArg UScalar.val e).symm
  have hSc : ScAcc R W csc (Z csc) := ⟨fun b ha hb => scR b hb ha, fun b h1 h2 =>
    gWr _ h1 (Or.inr (Or.inr (Or.inl (by rw [ecsc']; exact h2))))
      (scND b h1 ⟨by have := h2.1; omega, h2.2⟩),
    gWr _ hcq.2.2.1.2 (Or.inr (Or.inr (Or.inr (by rw [ecsc'])))) (scND _ hcq.2.2.1.2 hcq.2.2.1.1)⟩
  have rSt : R (stA t) := by rw [stA_eq]; exact cR _ (by simp) (by simp) (by simp) (by simp)
  have rSc : R (scA t) := cR _ (by simp) (by simp) (by simp) (by simp)
  have rIq : R (inqA t) := cR _ (by simp) (by simp) (by simp) (by simp)
  have rYt : R (yieldA t) := cR _ (by simp) (by simp) (by simp) (by simp)
  have rMx : R (maxA csc) := scR _ hcq.2.2.2.1 hcq.2.2.2.2
  have keyR : ∀ y, StKeys st T s target y → ∀ K : U64, 3528 ≤ K.val → K.val < 3576 → K.val % 8 = 0 →
      R (core.num.U64.wrapping_add y K) ∧ (K.val ≠ 3528 → K.val ≠ 3568 → W (core.num.U64.wrapping_add y K)) :=
    fun y hy K h1 h2 h3 =>
    have al := field_aligned (hT y hy.1) (K := K) (by omega) h3
    ⟨gRd _ al (Or.inl (Or.inl ⟨y, hy, K, h1, h2, h3, rfl⟩)), fun n1 n2 =>
      gWr _ al (Or.inl (Or.inl ⟨y, hy, K, h1, h2, h3, rfl⟩)) (by
        rintro (e | ⟨y', hy', e | e⟩)
        · rw [etc, stA_eq] at e
          exact tcb_word_ne (hT y hy.1) ht' (by omega) (by simp) (fun _ h => by simp at h; omega) e
        · exact tcb_word_ne (hT y hy.1) (hT y' hy'.1) (K2 := 3528#u64) (by omega) (by simp)
            (fun _ h => by simp at h; omega) e
        · exact tcb_word_ne (hT y hy.1) (hT y' hy'.1) (K2 := 3568#u64) (by omega) (by simp)
            (fun _ h => by simp at h; omega) e)⟩
  have tgK : StKeys st T s target target := ⟨htg, Or.inl rfl⟩
  have hmx0 : L.rmax s csc ≠ 0#u64 := by unfold LawfulStore.rmax; exact hmax0
  have nrm : ∀ Y : S, (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → NodeSt (L := L) R W Y := fun Y e => by
    unfold PathObl.NodeSt
    rw [e, e]
    exact ⟨nR _ (by rw [curth_val]; omega) (by rw [curth_val]), nR _ (by rw [act_val]; omega) (by rw [act_val]),
      nW _ (by rw [act_val]; omega) (by rw [act_val])⟩
  have hdC : ∀ Y : S, (∀ b ∈ Ω, L.mem Y b = L.mem s b) → RdHead (L := L) R Y csc := fun Y ag =>
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
      (L.mem Y (scA (L.mem Y (rhA (L := L) Y))) ≠ csc → ∀ b,
        InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) (Z (L.mem Y (scA (L.mem Y (rhA (L := L) Y))))) b →
        Outside b csc (Z csc)) := by
    intro Y kY cY eh es ag
    have e0 : L.mem Y (rhA (L := L) Y) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := by
      show L.mem Y (L.nodeAt Y (L.cpu Y) _) = _
      rw [cY, nodeAt_of_ksb kY, eh]
    rw [e0]
    intro hne
    obtain ⟨r1, -, -, r4, r5⟩ := rel_facts hI hne
    rw [es _ r1]
    have hqr := scq_of hO hS r4
    refine ⟨r1, gRd _ ?_ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hne, Or.inl rfl⟩)))))), SCq.agree hqr ag, ?_,
      fun b hb ha => gRd _ ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hne, Or.inr hb⟩)))))), fun hn b hb => ?_⟩
    · rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp)
    · unfold LawfulStore.rmax
      rw [ag _ (hqr.2.1 _ hqr.2.2.2.2 hqr.2.2.2.1)]; exact r5
    · have := hO.scDisj _ r4 _ hcsS hn
      unfold Outside; unfold InSC at hb; omega
  have rhd : ∀ Y : S, L.ksb Y = L.ksb s → L.cpu Y = L.cpu s →
      L.mem Y (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) →
      (∀ y ∈ T, L.mem Y (scA y) = L.mem s (scA y)) → (∀ b ∈ Ω, L.mem Y b = L.mem s b) →
      L.mem Y (rhA (L := L) Y) ≠ 0#u64 → R (scA (L.mem Y (rhA (L := L) Y))) ∧
        RdHead (L := L) R Y (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) := by
    intro Y kY cY eh es ag hne
    obtain ⟨-, q2, q3, q4, q5, -⟩ := hRH Y kY cY eh es ag hne
    exact ⟨q2, PathObl.ScAcc.head (W := fun _ => True) ⟨fun b ha hb => q5 b hb ha, fun _ _ _ => trivial, trivial⟩ (q3.1 q4)⟩
  -- the earliest timer
  have scK2 : ∀ y ∈ T, L.mem s2 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact uK hy (by simp) (by simp) (fun _ => by simp)
  have scK6 : ∀ y ∈ T, L.mem s6 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [← scK2 y hy, scA_eq]; exact mid_tcb hT hN2 htT w26 hy (by simp) (by simp) (by simp) (fun _ => by simp)
  have rh2 : L.mem s2 (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) :=
    pre_node _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have rh6 : L.mem s6 (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) :=
    nodeK6 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have arm20 : ∀ {y : U64}, y ∈ T → FootLtArmed st s2 (L.cpu s2) y → FootLtArmed st s (L.cpu s) y := by
    intro y hy ⟨a1', a2'⟩
    have e1 : L.mem s2 (tdA y) = L.mem s (tdA y) := uK (K := 3528#u64) hy (by simp) (by simp) (fun _ => by simp)
    have e2 : L.mem s2 (thA y) = L.mem s (thA y) := uK (K := 3568#u64) hy (by simp) (by simp) (fun _ => by simp)
    rw [e1] at a1'; rw [e2, c2] at a2'
    exact ⟨a1', a2'⟩
  have tm2 : L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.TIMER_MIN) ≠ 0#u64 →
      R (tdA (L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.TIMER_MIN))) := fun hne => by
    obtain ⟨q1, q2⟩ := tmin_facts (BXI.blk hB2) hcC2 hne
    exact (keyR _ ⟨q1, Or.inr (arm20 q1 q2)⟩ _ (by simp) (by simp) (by simp)).1
  have hN3 : NodePlaced st T s3 (L.cpu s3) := by rw [c3]; exact hN.ksb (w23.1.trans k2)
  have k3 : L.ksb s3 = L.ksb s := w23.1.trans k2
  have tm6 : L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.TIMER_MIN) ∈ T ∧
      R (tdA (L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.TIMER_MIN))) := by
    have e64 : L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.TIMER_MIN) =
        L.mem s4 (L.nodeAt s4 (L.cpu s4) layout.node.TIMER_MIN) := by
      rw [w46.2.1, nodeAt_of_ksb w46.1]
      refine w46.mem_eq (nodeAt_aligned hN4 (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])) ?_
      rintro ⟨K, a1', a2', e⟩
      exact node_ne_field hN4 (by simp [layout.node.TIMER_MIN]) htT ht' (by omega) e
    rw [e64]
    intro hne
    obtain ⟨q1, q2⟩ := tmin_facts hB4 hq4.cur hne
    refine ⟨q1, (keyR _ ⟨q1, ?_⟩ _ (by simp) (by simp) (by simp)).1⟩
    rcases armed_back hT hN3 htg w34 q1 q2 with e | e
    · exact Or.inl e
    · exact Or.inr (armed30 q1 e)
  -- the insert
  have gIns : timer.insert gS s3 target dl bd = timer.insert st s3 target dl bd := by
    obtain ⟨W3, ct3⟩ := (TInv.rb hB3).tree _ (c3 ▸ hcC : L.cpu s3 ∈ Cs)
    have hkey : ∀ z, (z ∈ W3.keys ∨ z = target) → StKeys st T s target z := by
      rintro z (hz | rfl)
      · exact ⟨ct3.inT z hz, Or.inr (armed30 (ct3.inT z hz) ⟨ct3.armed z hz, ct3.core z hz⟩)⟩
      · exact tgK
    have C : TC st gS T s (L.cpu s) (fun z => z ∈ W3.keys ∨ z = target) R W (fun z => z = target) :=
      { tcbs := hT, inT := fun z hz => (hkey z hz).1, node := hN
        rd := fun w hw => by
          rcases hw with ⟨z, hz, k, h1, h2, h3, rfl⟩ | ⟨o, ho, h8, rfl⟩
          · exact (keyR z (hkey z hz) k h1 h2 h3).1
          · exact nR o ho h8
        wr := fun w hw => by
          rcases hw with ⟨z, hz, k, h1, h2, h3, rfl⟩ | ⟨o, ho, h8, rfl⟩
          · exact (keyR z (hkey z hz) k (by omega) (by omega) h3).2 (by omega) (by omega)
          · exact nW o ho h8
        wh := fun X x v hx hc => hwH X x v (hkey x hx) hc
        wd := fun X x v _ (hxd : x = target) ha1 ha0 hc => by
          rw [hxd] at ha1 ha0 hc ⊢; exact hwD X v ha1 ha0 hc }
    have af3 : ∀ z ∈ T, L.mem s3 (affA z) = L.mem s (affA z) := fun z hz =>
      k03 (K := 3520#u64) hz (by simp) (by simp) (fun _ => by simp)
    have I3 : TI st s (L.cpu s) (fun z => z ∈ W3.keys) (fun z => z ∈ W3.keys) s3 :=
      { ksb := k3, cpu := c3, sub := fun _ hz => hz
        root := by
          have := ct3.rep.root_mem
          rw [c3, nodeAt_of_ksb k3] at this; exact this
        lnk := fun z hz => ct3.rep.links z hz
        hj := fun z hz _ => by rw [← c3]; exact ct3.core z hz
        af := fun z hz => af3 z (ct3.inT z hz) }
    refine (ge_insert C rfl haffg rfl ?_).1
    by_cases hd : L.mem s3 (tdA target) = 0#u64
    · unfold timer.remove
      have etd : obj.Tcb.timer_deadline st target s3 = ok 0#u64 := by
        rw [td_ok, hd]
      have gtd : obj.Tcb.timer_deadline gS target s3 = obj.Tcb.timer_deadline st target s3 :=
        PathObl.obj.Tcb.timer_deadline.guard target s3 (keyR _ tgK _ (by simp) (by simp) (by simp)).1
      rw [gtd, etd]
      simp only [bind_ok, ↓reduceIte]
      exact GE.ret ⟨I3, hd, af3 target htg⟩
    · obtain ⟨c', hc', t', ct', hkt⟩ := (TInv.rb hB3).armed target htg hd
      have hcc : c' = L.cpu s3 := by
        have h1 := ct'.core target hkt
        have h2 := hown3.resolve_left hd
        exact UScalar.eq_of_val_eq (h1.symm.trans h2)
      subst hcc
      rw [ct'.uniq ct3] at hkt
      refine GE.mono (ge_remove (C.mono fun z hz => Or.inl hz) I3 hkt rfl haffg fun i _ _ => ?_)
        (fun s' h' => ⟨h'.1, h'.2, h'.1.af target hkt⟩)
      have e := timer.core_of.rb s3 target ct3 hkt
      rw [← c3]; exact eq_of_spec_fd e
  -- `set_thread_state`
  have gSts : ∀ (Y : S) (v : U64), (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → L.mem Y (scA t) = csc →
      (v = sched.TS_RESTART ∨ v = sched.TS_RUNNING) →
      (L.mem Y (stA t) = sched.TS_RUNNING ∨ L.mem Y (stA t) = sched.TS_RESTART) → L.mem Y (affA t) = L.cpu s →
      sched.set_thread_state gS Y t v = sched.set_thread_state st Y t v := fun Y v e1 e2 hv ho ha =>
    set_thread_state.gw Y t v (nrm Y e1) (hwS' Y v hv ho ha) rSt rSc
      (by rw [PathObl.st_wr_sc ht', e2]; exact rMx) rIq
  have aff2 : L.mem s2 (affA t) = L.cpu s :=
    (uK (K := 3520#u64) htT (by simp) (by simp) (fun _ => by simp)).trans haff
  have aff5 : L.mem s5 (affA t) = L.cpu s :=
    (mid_tcb (K := 3520#u64) hT hN2 htT w25 htT (by simp) (by simp) (by simp) (fun _ => by simp)).trans aff2
  have st4 : L.mem s4 (stA t) = sched.TS_RESTART := by
    rw [w34.mem_eq sA ?_, e3, L.mem_wr_same sA]
    rintro (⟨o, ho, e⟩ | ⟨K, a1', a2', e⟩ | ⟨y, hy, -, -, K, a1', a2', e⟩)
    · exact node_ne_field hN3 (by omega) htT ht' (o := o) (K := 3328#u64) (by simp) (by rw [← stA_eq]; exact e.symm)
    · exact tcb_word_ne ht' (hT _ htg) (K1 := 3328#u64) (K2 := K) (by simp) (by omega) (fun _ h => by simp at h; omega)
        (by rw [← stA_eq]; exact e)
    · exact tcb_word_ne ht' (hT _ hy) (K1 := 3328#u64) (K2 := K) (by simp) (by omega) (fun _ h => by simp at h; omega)
        (by rw [← stA_eq]; exact e)
  have st5 : L.mem s5 (stA t) = sched.TS_RESTART := by
    rw [(reply_regs ht' es5).mem_eq sA ?_]
    · exact st4
    rintro ⟨K, a1', a2', e⟩
    exact tcb_word_ne ht' ht' (K1 := 3328#u64) (K2 := K) (by simp) (by omega) (fun _ h => by simp at h; omega)
      (by rw [← stA_eq]; exact e)
  have e5N : ∀ o, L.nodeAt s5 (L.cpu s5) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [w25.2.1, nodeAt_of_ksb w25.1, e2N]
  have e7N : ∀ o, L.nodeAt s7 (L.cpu s7) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [w67.2.1, nodeAt_of_ksb w67.1, e6N]
  -- `schedule`
  have hres := resume_hsw_hfr (gS := gS) ar hA s6 a1 (zc := Z csc) hcC6 hN6 hT
    (fun b hb => (h0.omega b hb).ksb k6) (by rw [hct6]; exact htT) (by rw [hct6, hsc6, hcs6])
    (by rw [hcs6]; exact SCq.agree hcq agΩ6)
    (by rw [hcs6]; unfold LawfulStore.rmax; rw [agΩ6 _ hmaxΩ]; exact hmx0)
    (fun o h1 h2 => by rw [e6N]; exact ⟨nR o h1 h2, nW o h1 h2⟩)
    (by rw [hcs6]; exact hSc) (by rw [hct6]; exact rSc) (by rw [k6]; exact hD2)
    (fun hne => by
      obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hRH s6 k6 c6 rh6 scK6 agΩ6 hne
      exact ⟨_, q1, q2, q3, q4, q5, by rw [hcs6]; exact q6, fun e => by rw [e, hcs6]⟩)
    (fun hne => tm6 hne)
  have gSched : sched.schedule gS ar s6 a1 = sched.schedule st ar s6 a1 :=
    sched.schedule.guard_nodue ar s6 a1 (fun o h1 h2 => by rw [e6N]; exact ⟨nR o h1 h2, nW o h1 h2⟩)
      (fun hne => (tm6 hne).2) hT6 (fun hne => rhd s6 k6 c6 rh6 scK6 agΩ6 hne) hR6 hact6 hres.1 hres.2
  obtain ⟨W0, ct0⟩ := (TInv.rb (BXI.blk hI)).tree _ hcC
  have k0 : ∀ z ∈ W0.keys, StKeys st T s target z := fun z hz =>
    ⟨ct0.inT z hz, Or.inr ⟨ct0.armed z hz, ct0.core z hz⟩⟩
  have e1s : s1 = L.wr s (regA t layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx localtimer.SYSCALL_INSN_LEN) := by
    have e := es1r
    rw [PathObl.set_reg_ok'] at e; exact (ok_inj_ff e).symm
  have e1N : ∀ o, L.nodeAt s1 (L.cpu s1) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [e1s]; exact PathObl.nd_wr _ _ _ _
  have gact : sched.activate_thread gS ar s7 a2 = sched.activate_thread st ar s7 a2 :=
    activate_thread.g_run ar s7 a2 hcur7 hy7 (nrm s7 e7N) rYt rSt hst7
  have gvc := PathObl.LT.vcpu.check.guard_running (gS := gS) ar s7 a2 t rSt hst7
  have ndR : ∀ (Y : S), (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → ∀ o : U64, o.val < 4288 →
      o.val % 8 = 0 → R (L.nodeAt Y (L.cpu Y) o) := fun Y e o h1 h2 => by rw [e]; exact nR o h1 h2
  have gcnsv : sched.consumed gS s2 = sched.consumed st s2 :=
    PathObl.sched.consumed.guard s2 (ndR s2 e2N _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
  have gtdue : localtimer.timer_due gS s2 (L.cpu s) now = localtimer.timer_due st s2 (L.cpu s) now := by
    have := timer_due.guard (gS := gS) s2 now
      (ndR s2 e2N _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])) tm2
    rwa [c2] at this
  have grdue : localtimer.release_due gS s2 (L.cpu s) = localtimer.release_due st s2 (L.cpu s) := by
    have := release_due.guard (gS := gS) s2
      (ndR s2 e2N _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
      (fun hne => rhd s2 k2 c2 rh2 scK2 agΩ2 hne)
      (ndR s2 e2N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    rwa [c2] at this
  have gquiet : localtimer.sched_quiet gS s (L.cpu s) = localtimer.sched_quiet st s (L.cpu s) :=
    sched_quiet.guard s (nR _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])) hD2
      (nR _ (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]))
  have gtgt : localtimer.set_timer_target_ok gS s (L.cpu s) target = ok true :=
    set_timer_target_ok.guard ct0 (fun w hw => by
      rcases hw with rfl | rfl | ⟨y, hy, rfl | rfl | rfl⟩
      · exact nR _ (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])
      · exact nR _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      · exact (keyR y (k0 y hy) _ (by simp) (by simp) (by simp)).1
      · exact (keyR y (k0 y hy) _ (by simp) (by simp) (by simp)).1
      · exact (keyR y (k0 y hy) _ (by simp) (by simp) (by simp)).1)
      (gRd _ (field_aligned (hT _ htg) (by simp) (by simp)) (Or.inr (Or.inr (Or.inl rfl))))
      (keyR _ tgK _ (by simp) (by simp) (by simp)).1 (keyR _ tgK _ (by simp) (by simp) (by simp)).1 eb
  have rCore : R (scCoreA csc) := by
    obtain ⟨hP, hz⟩ := hO.sc _ hcsS
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
    have hcv : layout.sc.CORE.val = 16 := by simp [layout.sc.CORE]
    exact scR _ ⟨by unfold scCoreA; rw [hv]; omega, by unfold scCoreA; rw [hv, hcv]; omega⟩
      (by unfold Aligned scCoreA; rw [hv, hcv]; omega)
  have gcok : localtimer.current_ok gS s (L.cpu s) t csc = localtimer.current_ok st s (L.cpu s) t csc :=
    current_ok.guard s (L.cpu s) t csc (cR _ (by simp) (by simp) (by simp) (by simp)) rSt rYt
      (cR _ (by simp) (by simp) (by simp) (by simp)) rSc (by rw [hsct]; exact rCore) rCore
      (nR _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]))
      (cR _ (by simp) (by simp) (by simp) (by simp)) hD1
  exact set_timer_replay (st := st) (st' := gS) ar et
    (PathObl.sched.cur_thread.guard s (nR _ (by rw [curth_val]; omega) (by rw [curth_val]))) ‹PathObl.GRd gS st R›.cur_cpu (L.cur_cpu_eq s) emi
    (PathObl.msg.msg_info.guard s t (rR _ (by simp [layout.reg.MSG_INFO]))) cn ei
    (PathObl.obj.Tcb.flags.guard t s (cR _ (by simp) (by simp) (by simp) (by simp))) n1 n2 n3 n4 ecsc
    (PathObl.sched.cur_sc.guard s (nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))) eb
    (gtgt.trans eb.symm) eb1 gcok ei2 (PathObl.obj.Tcb.state.guard t s rSt) n5 eb2
    (PathObl.sched.is_schedulable.guard s t rSt rSc (by rw [hsct]; exact rMx) rIq) eb3 gquiet enx
    (PathObl.obj.Tcb.reg.guard t s _ (rR _ (by simp [layout.reg.NEXT_IP]))) es1r
    (PathObl.obj.Tcb.set_reg.guard t s _ _ (rW _ (by simp [layout.reg.FAULT_IP]))) eu
    (PathObl.sched.update_timestamp.guard ar s1 a
      (ndR s1 e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (by show W (L.nodeAt s1 (L.cpu s1) _); rw [e1N]; exact nW _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (ndR s1 e1N _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
      (by show W (L.nodeAt s1 (L.cpu s1) _); rw [e1N]; exact nW _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])))
    enow (PathObl.sched.cur_time.guard s2 (ndR s2 e2N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])))
    edl (PathObl.msg.syscall_arg.guard_lt s2 t _ _ (by rw [PathObl.n_msg_regs]; decide) (fun r er => by
      rw [PathObl.msg_register_zero] at er; rw [← ok_inj_ff er]; exact rR _ (by simp [layout.reg.R10])))
    ebd (PathObl.msg.syscall_arg.guard_lt s2 t _ _ (by rw [PathObl.n_msg_regs]; decide) (fun r er => by
      rw [PathObl.msg_register_one] at er; rw [← ok_inj_ff er]; exact rR _ (by simp [layout.reg.R8])))
    ecns gcnsv eb4 (PathObl.sporadic.sufficient.guard ar s2 a1 csc cns (hdC s2 agΩ2)) eb5 gtdue eb6 grdue hdl es3
    (gSts s2 _ e2N sc2 (Or.inl rfl) (Or.inl hrs2) aff2) es4 gIns es5
    (PathObl.msg.reply_success_empty.guard s4 t (rW _ (by simp [layout.reg.BADGE])) (rW _ (by simp [layout.reg.MSG_INFO])))
    es6 (gSts s5 _ e5N sc5 (Or.inr rfl) (Or.inr st5) aff5) es7 gSched es8r gact et1r
    (PathObl.sched.cur_thread.guard s7 (ndR s7 e7N _ (by rw [curth_val]; omega) (by rw [curth_val])))
    es9r (gvc.1.trans gvc.2.symm)

end main

end

end Fl4Proofs.P2.GED
