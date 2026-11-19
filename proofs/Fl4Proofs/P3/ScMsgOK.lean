/-
P3 (DESIGN.md §9), scheduling contexts: **ScYieldTo's `MsgOK` holds**
(`msgOK_holds`): `set_consumed`'s message writes (`msgW`: the badge
register, `MR0` and the message info, three register words of the TCB;
`set_mr` at index 0 writes a register, never the IPC buffer) refine the
spec's `reply_from_kernel` of one word (`replyFromKernel_one`), at every
state with `SchedRel` and `NtfnStateRel`.

* `msgW_shape`: FL4's three writes (as XTopYield's `set_consumed_irel`).
* `regWr_rel`: a register word of a TCB of `T` other than the badge
  register written, the spec's register set: `SchedRel` (`SAgree`: the
  word is no scheduler field, node, kernel-state or SC word; TCBs are
  4 KiB-aligned, so distinct ones are apart) and `NtfnStateRel` (the word is
  in no notification, `NPlaced`, and no TCB field the relation reads).
  The badge register by NtfnRecv's `set_badge_reg_rel` and `SchedRel.stable`.
* The written words are `RegW` (offsets 256..448 of the TCB), none a
  `YIELD_TO` word (offset 3472); the spec side is `ArchStep`
  (`archStep_updTcb`).
-/
import Fl4Proofs.P3.XTopJointYield
import Fl4Proofs.P3.IpcCancel
import Fl4Proofs.P3.IpcSuspend
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {N T C : Set U64} {c : U64}

/-- **`msgW`'s writes**: the badge register, `MR0` and the message info. -/
theorem msgW_shape (s1 : S) (t v : U64) :
    msgW st s1 t v ⦃ s3 => ∃ w : U64,
      s3 = L.wr (L.wr (L.wr s1 (regA t (regIdx Fl4Spec.badge_register)) 0#u64)
        (regA t (regIdx (mrIdx 0))) v) (regA t (regIdx Fl4Spec.msg_info_register)) w ∧
      w.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen 1, 0, 0, 0⟩ ⦄ := by
  unfold msgW
  refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st _ true t L.total) ?_
  rintro buf -
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ t layout.reg.BADGE 0#u64) ?_
  rintro s2 rfl
  have hset : ∀ s2 : S, msg.set_mr st s2 t buf 0#u64 v ⦃ r =>
      r = (1#u64, L.wr s2 (regA t (regIdx (mrIdx 0))) v) ⦄ := by
    intro s2
    unfold msg.set_mr
    have h4 : (0#u64 : U64) < msg.N_MSG_REGISTERS := by unfold msg.N_MSG_REGISTERS; decide
    simp only [h4, ↓reduceIte]
    refine WP.spec_bind (Endp.msg_register_spec 0#u64 (by decide)) ?_
    rintro r0 rfl
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ t _ v) ?_
    rintro s3 rfl
    simp only [lift, bind_ok, WP.spec_ok]
    rfl
  refine WP.spec_bind (hset _) ?_
  rintro r rfl
  unfold msginfo.MessageInfo.new
  simp only [bind_ok]
  refine WP.spec_mono (Endp.set_msg_info_spec _ t 0#u64 1#u64 (by decide)) ?_
  rintro s3 ⟨w, rfl, hw⟩
  refine ⟨w, ?_, by rw [hw]; exact Vs.msg_info_one_bv⟩
  rw [Endp.regIdx_badge, Endp.regIdx_msgInfo]

/-- A register word as a TCB field (`RegW`'s form). -/
theorem regA_add {t i : U64} (ht : TcbAddr t) (hi : i.val < 24) :
    (core.num.U64.wrapping_sub (regA t i) t).val = 256 + 8 * i.val ∧
      regA t i = core.num.U64.wrapping_add t (core.num.U64.wrapping_sub (regA t i) t) := by
  have hv := regA_val ht hi
  have hf := ht.fits
  have h1 : (core.num.U64.wrapping_sub (regA t i) t).val = 256 + 8 * i.val := by
    rw [core.num.U64.wrapping_sub_val_eq]; simp [U64.size, U64.numBits] <;> omega
  refine ⟨h1, UScalar.eq_of_val_eq ?_⟩
  rw [core.num.U64.wrapping_add_val_eq, h1]; simp [U64.size, U64.numBits] <;> omega

set_option maxHeartbeats 4000000 in
/-- **A register write of a TCB of `T`** (not the badge register) keeps
`SchedRel` and `NtfnStateRel`, the spec's register set. -/
theorem regWr_rel {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    (hR : NtfnStateRel N T (L.mem s) σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (r : Fl4Spec.Register) (hr : r ≠ Fl4Spec.badge_register) (v : U64) :
    SchedRel st N T C c (L.wr s (regA t (regIdx r)) v) (Notif.updK σ t.bv (.tcb (Notif.setReg x r v.bv))) ∧
      NtfnStateRel N T (L.mem (L.wr s (regA t (regIdx r)) v)) (Notif.updK σ t.bv (.tcb (Notif.setReg x r v.bv))) := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hta := hT t ht
  have hil := regIdx_lt r
  have hav := regA_val hta hil
  have hwa : Aligned (regA t (regIdx r)) := (a_reg hta r).1
  have hko := hc.ksOut t ht
  have h1 := hc.node.align
  have h2 := hc.node.fits
  simp only [LawfulStore.nodeBase] at h1 h2
  have hta1 := hta.align
  have hta2 := hta.fits
  have hnd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s (regA t (regIdx r)) v) (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := fun o ho h8 =>
    rd_wr_ne hwa (nodeAt_aligned hc.node ho h8) fun e => by
      have := congrArg UScalar.val e; rw [hav] at this; have := nodeAt_out hc.node ho ht; omega
  have ha : SAgree st T C c s (L.wr s (regA t (regIdx r)) v) := by
    refine ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun o ho h8 _ _ _ _ _ => hnd o ho h8, fun y hy K' hK' => ?_, ?_, ?_,
      fun sc hsc a ha hin => rd_wr_ne hwa ha fun e => ?_⟩
    · obtain ⟨k1, k2, -⟩ := schedField_ok hK'
      refine rd_wr_ne hwa (field_aligned (hc.tcbs y hy) k1 k2) fun e => ?_
      have := congrArg UScalar.val e
      rw [hav, tfield_val (hc.tcbs y hy) k1] at this
      have hK3 : 3432 ≤ K'.val := by rcases hK' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      have := (hc.tcbs y hy).align
      by_cases eyt : y = t
      · subst eyt; omega
      · have := val_ne_of_ne eyt; omega
    · have hal : Aligned (curDomA st s) := by
        unfold Aligned curDomA
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
        omega
      refine rd_wr_ne hwa hal fun e => ?_
      have := congrArg UScalar.val e
      rw [hav] at this
      unfold curDomA at this
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] at this
      omega
    · refine rd_wr_ne hwa (dtA_aligned hc.node) fun e => ?_
      have := congrArg UScalar.val e
      rw [hav, dtA_val hc.node] at this
      omega
    · have := (hS.scOutIn hsc hin).2.2.1 t ht
      rw [← e, hav] at this; omega
  have hn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      nodeW st (L.wr s (regA t (regIdx r)) v) c o = nodeW st s c o := fun o ho h8 => by
    unfold Fl4Proofs.P3.Sched.nodeW; rw [Sched.nodeAt_ksb (st := st) (L.ksb_wr _ _ _)]
    exact hnd o ho h8
  refine ⟨hS.of_sagreeE ha (hn _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
    (hn _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])) hS.nodeNW hS.domNW hS.dtNW
    (SchedStep.updK_tcb hk rfl rfl rfl), ?_⟩
  have hw : P1.WritesIn st s (L.wr s (regA t (regIdx r)) v) (· = regA t (regIdx r)) := P1.writesIn_wr hwa
  have hbne : (regA t (regIdx r)).val ≠ (regA t (regIdx Fl4Spec.badge_register)).val := regA_ne hta hr
  refine hR.frame hS.placed (fun b hb hf => hw.mem_eq hb fun e => ?_) ⟨fun q y hq => ?_, fun q y hq => ?_⟩
  · subst e
    rcases hf with ⟨n, hn, h1, h2⟩ | ⟨y, hy, h⟩
    · have := hS.placed.disj n hn t ht; omega
    · by_cases e : y = t
      · subst e
        have hv := nfootT_val hta h
        have hb0 := regA_val hta (regIdx_lt Fl4Spec.badge_register)
        have hbi : (regIdx Fl4Spec.badge_register).val = 0 := rfl
        omega
      · have hv := nfootT_val (hT y hy) h
        have := (hT y hy).align
        have := (hT y hy).fits
        have := val_ne_of_ne e
        omega
  · by_cases e : q = t.bv
    · subst e; rw [hk] at hq; cases hq
    · simp only [Notif.updK, Function.update_of_ne e]; exact hq
  · by_cases e : q = t.bv
    · subst e; rw [hk] at hq; cases hq
      refine ⟨Notif.setReg x r v.bv, by simp [Notif.updK], rfl, ?_, rfl⟩
      unfold Notif.badgeOf
      rw [Notif.setReg_regs, Function.update_of_ne (Ne.symm hr)]
    · exact ⟨y, by simp only [Notif.updK, Function.update_of_ne e]; exact hq, rfl, rfl, rfl⟩

/-- A register word of `t ∈ T` is `RegW` and no `YIELD_TO` word. -/
theorem regA_regW {t : U64} (ht : t ∈ T) (hT : TcbPlaced T) (r : Fl4Spec.Register) :
    RegW T (regA t (regIdx r)) ∧ ¬ YW T (regA t (regIdx r)) := by
  have hta := hT t ht
  have hil := regIdx_lt r
  obtain ⟨hK, he⟩ := regA_add hta hil
  refine ⟨⟨t, ht, _, by omega, by omega, he⟩, ?_⟩
  rintro ⟨y, hy, e⟩
  have := congrArg UScalar.val e
  rw [regA_val hta hil, show yieldA y = core.num.U64.wrapping_add y 3472#u64 from rfl,
    tfield_val (hT y hy) (by simp)] at this
  have := (hT y hy).align
  have := hta.align
  have h3472 : (3472#u64 : U64).val = 3472 := rfl
  by_cases eyt : y = t
  · subst eyt; omega
  · have := val_ne_of_ne eyt; omega

set_option maxHeartbeats 4000000 in
/-- **ScYieldTo's `MsgOK` holds** (module docstring). -/
theorem msgOK_holds : MsgOK st N T C c := by
  intro s1 σ1 t v ht hS hR
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  obtain ⟨x, hk, -⟩ := hs.tcb t ht
  refine WP.spec_mono (msgW_shape s1 t v) ?_
  rintro s3 ⟨w, rfl, hw⟩
  obtain ⟨hR1, hW1, hN1⟩ := set_badge_reg_rel hS.placed hR ht hk 0#u64
  have hS1 := hS.stable hW1 hN1
  rw [badgeRegA_eq_regA] at hR1 hS1
  have hk1 : (Notif.updK σ1 t.bv (.tcb (Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv))).kheap t.bv =
      some (.tcb (Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv)) := by simp [Notif.updK]
  obtain ⟨hS2, hR2⟩ := regWr_rel hS1 hR1 ht hk1 (mrIdx 0) (by decide) v
  have hk2 : (Notif.updK (Notif.updK σ1 t.bv (.tcb (Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv))) t.bv
      (.tcb (Notif.setReg (Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv) (mrIdx 0) v.bv))).kheap t.bv =
      some (.tcb (Notif.setReg (Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv) (mrIdx 0) v.bv)) := by
    simp [Notif.updK]
  obtain ⟨hS3, hR3⟩ := regWr_rel hS2 hR2 ht hk2 Fl4Spec.msg_info_register (by decide) w
  have hxC : Notif.setReg (Notif.setReg (Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv) (mrIdx 0) v.bv)
      Fl4Spec.msg_info_register w.bv = Endp.replyTcb x v.bv := by rw [hw]; rfl
  rw [Vs.updK_updK, Vs.updK_updK, hxC] at hS3 hR3
  have hu : Fl4Spec.wordsFromTime v.bv = [v.bv] := by
    unfold Fl4Spec.wordsFromTime Fl4Spec.ucast; simp
  have hW : P1.WritesIn st s1 (L.wr (L.wr (L.wr s1 (regA t (regIdx Fl4Spec.badge_register)) 0#u64)
      (regA t (regIdx (mrIdx 0))) v) (regA t (regIdx Fl4Spec.msg_info_register)) w)
      (fun b => RegW T b ∧ ¬ YW T b) := by
    have hta := hT t ht
    refine (((writesIn_wr (a_reg hta Fl4Spec.badge_register).1).trans
      (writesIn_wr (a_reg hta (mrIdx 0)).1)).trans (writesIn_wr (a_reg hta Fl4Spec.msg_info_register).1)).mono
      fun b hb => ?_
    rcases hb with (rfl | rfl) | rfl
    · exact regA_regW ht hT _
    · exact regA_regW ht hT _
    · exact regA_regW ht hT _
  refine ⟨_, by rw [hu]; exact Endp.replyFromKernel_one hk v.bv, hS3, hR3, archStep_updTcb hk rfl,
    hW.mono fun b hb => hb.2, hW.mono fun b hb => Or.inr hb.1⟩

end

end

end Fl4Proofs.P3.Ipc
