/-
P3 (DESIGN.md §9), IPC: **the timeout fault of a thread with a scheduling
context sent to a waiting receiver** (toward XTopJointIpcJ's reply tail:
`handle_timeout` of the replied-to thread when receivers wait on its timeout
handler's endpoint).

FL4's `set_mrs_fault` of a timeout fault runs `update_consumed` on the
sender's SC (the SC's `CONSUMED` word to 0) before the two message words
(the badge and the consumed time, both message registers: no receive-buffer
word is written).

* `set_mr_rgR`: `set_mr` of a register word, its footprint and result.
* `do_ipc_transfer_tmo_rg`: FL4's footprint of the transfer from the state
  after the SC word (`tmoS`): the receiver's registers only.
* `set_mrs_fault_tmoSC_E`, `set_mrs_fault_tmoSCN_E`, `do_ipc_transfer_tmoE`:
  IpcTmo's `set_mrs_fault_tmoSC(N)` / `tmoXfer_top` with the endpoint
  hypotheses (`EpHyps`) instead of `IpcSchedHyps`, with or without a receive
  buffer, the base of the frame the state after the SC step.
* `xferTmoStepJ`: the transfer step of `send_ipc` to a waiting receiver for
  a sender with a timeout fault and an SC (as XTopJointFaultRecv's
  `xferFaultStepJ`): the spec's outcome `updK (tmoSt σ sc y n) rcv x'`, the
  FL4 footprint the SC word and the receiver's registers, P1 by
  `XS.consumed` then `xfer_all`.
-/
import Fl4Proofs.P3.XTopJointFaultRecv
import Fl4Proofs.P3.XTopJointSendBlockG
import Fl4Proofs.P3.IpcTmo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- `set_mr` of a word `i < 4` (a message register): the receiver's
registers, and the next index. -/
theorem set_mr_rgR {T : Set U64} (hT : P1.TcbPlaced T) {s0 s : S} {rcv rw i v : U64} (hr : rcv ∈ T)
    (hi : i.val < 4) (h : P1.WritesIn st s0 s (XferRegW T ∅)) :
    msg.set_mr st s rcv rw i v ⦃ r => r.1 = core.num.U64.wrapping_add i 1#u64 ∧
      P1.WritesIn st s0 r.2 (XferRegW T ∅) ⦄ := by
  have hc : i < msg.N_MSG_REGISTERS := by
    unfold msg.N_MSG_REGISTERS; scalar_tac
  unfold msg.set_mr
  rw [if_pos hc]
  refine WP.spec_bind (msg.msg_register.lt i) fun rg hrg => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.rg (v := v) (s := s) hT hr hrg) fun s2 w2 => ?_
  simp only [lift, bind_ok, WP.spec_ok]
  exact ⟨by trivial, rg_trans h w2⟩

theorem scW8_eq (sc : U64) : scW sc 8#u64 = core.num.U64.wrapping_add sc layout.sc.CONSUMED := by
  unfold scW layout.sc.CONSUMED; rfl

/-- **`do_ipc_transfer`'s footprint, a sender with a timeout fault and an
SC** (`hU`: `update_consumed` writes the SC word, `tmoS`): from the state
after it, the receiver's registers only. -/
theorem do_ipc_transfer_tmo_rg {T : Set U64} (hT : P1.TcbPlaced T) {snd rcv : U64} (hr : rcv ∈ T) (s : S) (a : A)
    (ep badge : U64) (grant : Bool) {sc : U64}
    (hty : L.mem s (tFaultA snd) = 5#u64) (hsc : L.mem s (P1.scA snd) = sc)
    (hsc0 : sc ≠ 0#u64)
    (hU : schedcontext.update_consumed st arI s a sc ⦃ r => r.2 = tmoS st s sc ⦄) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' =>
      P1.WritesIn st (tmoS st s sc) s' (XferRegW T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s true rcv hS) fun rb _ => ?_
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_
  rintro ft rfl
  rw [hty, if_neg (by unfold fl4_abi.consts.fault.NullFault; decide)]
  unfold ipc.do_fault_transfer
  refine WP.spec_bind (Pₘ := fun r : U64 × S => P1.WritesIn st (tmoS st s sc) r.2 (XferRegW T ∅)) ?_ ?_
  · unfold faults.set_mrs_fault
    refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_; rintro _ rfl
    refine WP.spec_bind (Endp.obj.Tcb.fault_w0.spec s snd) ?_; rintro _ rfl
    refine WP.spec_bind (Endp.obj.Tcb.fault_w1.spec s snd) ?_; rintro _ rfl
    refine WP.spec_bind (Endp.obj.Tcb.fault_w2.spec s snd) ?_; rintro _ rfl
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s snd _) ?_; rintro _ rfl
    rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
      ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
      ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UserException; decide),
      ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.Timeout; rfl))]
    refine WP.spec_bind (Fl4Proofs.P1.obj.Tcb.sc.spec s snd) ?_
    rintro i rfl
    unfold obj.Sc.is_null
    apply ok_bind_spec
    simp only [hsc, hsc0, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind hU ?_
    rintro ⟨cv, s1⟩ hs1
    simp only at hs1
    subst hs1
    refine WP.spec_bind (set_mr_rgR (rw := rb) (i := 0#u64) (v := L.mem s (tFw0A snd)) hT hr (by decide)
      (P1.WritesIn.refl _ _)) ?_
    rintro ⟨k, s2⟩ ⟨hk, h2⟩
    simp only at hk h2
    subst hk
    exact WP.spec_mono (set_mr_rgR hT hr (by decide) h2) fun r hr' => hr'.2
  rintro ⟨sent, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st snd s1 hS) fun ft _ => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
  refine WP.spec_bind (Pₘ := fun s3 => P1.WritesIn st (tmoS st s sc) s3 (XferRegW T ∅)) ?_
    fun s3 h3 => WP.spec_mono (obj.Tcb.set_reg.rg (s := s3) (v := badge) hT hr
      (by simp [layout.reg.BADGE, layout.reg.RDI])) fun s4 w4 => rg_trans h3 w4
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    WP.spec_mono (obj.Tcb.set_reg.rg (v := w) (s := s1) hT hr (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
      fun s4 w4 => rg_trans h1 w4

end

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 2000000 in
/-- IpcTmo's `set_mrs_fault_tmoSC` from `EpHyps`. -/
theorem set_mrs_fault_tmoSC_E (hE : EpHyps st T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))))
    (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {b : Fl4Spec.Word} (hf : xs.tcbFault = some (.timeout b)) {sc : U64} (hsc : L.mem s (scA snd) = sc)
    (hsc0 : sc ≠ 0#u64) (hscC : sc ∈ C) {y : Fl4Spec.SchedContext} {n : Nat}
    (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p) :
    faults.set_mrs_fault st ar s a snd rcv rw ⦃ r => r.1.val = [b, consumedUs y.scConsumed].length ∧
      MrInv (L := L) T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (tmoS st s sc)
        (tmoSt σ sc y n) rcv xr p r.2 [b, consumedUs y.scConsumed] ⦄ := by
  have hP := hP0.e
  have hxs := hX.1.toE.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0⟩ := hfr
  have hrsc : rcv.bv ≠ sc.bv := kheap_ne hkr hky (fun _ h1 h2 => by subst h1; cases h2)
  unfold faults.set_mrs_fault
  step with obj.Tcb.fault_type.spec as ⟨ty, hty'⟩
  step with obj.Tcb.fault_w0.spec as ⟨w0, hw0'⟩
  step with obj.Tcb.fault_w1.spec as ⟨w1, hw1'⟩
  step with obj.Tcb.fault_w2.spec as ⟨w2, hw2'⟩
  step with Endp.obj.Tcb.reg.spec as ⟨pc, hpc'⟩
  subst hty' hw0' hw1' hw2' hpc'
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UserException; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.Timeout; rfl))]
  step with obj.Tcb.sc.spec as ⟨i, hi⟩
  subst hi
  unfold obj.Sc.is_null
  apply ok_bind_spec
  simp only [hsc, hsc0, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (update_consumed_irel hP0 s a σ hX hscC hky hmax htu) ?_
  rintro ⟨cv, s1⟩ ⟨hs1, hcv, -, hI1⟩
  simp only at hs1 hcv hI1
  subst hs1
  have hkr1 : (tmoSt σ sc y n).kheap rcv.bv = some (.tcb xr) := by simp [updK, hrsc, hkr]
  have hM0 := mrInv_init (L := L) (SR := SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    hI1.1.toE ⟨hI1.2, ScRelM.of hI1.1⟩ hkr1 p
  refine WP.spec_bind (set_mr_inv (L := L) hE hP hr hkr1 hrw0 hmr hM0 0#u64 rfl (by decide)
    (L.mem s (tFw0A snd))) ?_
  rintro ⟨k, s2⟩ ⟨hk, hM1⟩
  simp only at hk hM1
  refine WP.spec_mono (set_mr_inv (L := L) hE hP hr hkr1 hrw0 hmr hM1 k (by simpa using hk) (by simp at hk; omega)
    cv) ?_
  rintro ⟨k2, s3⟩ ⟨hk2, hM2⟩
  simp only at hk2 hM2 ⊢
  rw [hw0, hcv] at hM2
  exact ⟨by simp at hk hk2 ⊢; omega, hM2⟩

set_option maxHeartbeats 2000000 in
/-- IpcTmo's `set_mrs_fault_tmoSCN` from `EpHyps`. -/
theorem set_mrs_fault_tmoSCN_E (hE : EpHyps st T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))))
    (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {b : Fl4Spec.Word} (hf : xs.tcbFault = some (.timeout b)) {sc : U64} (hsc : L.mem s (scA snd) = sc)
    (hsc0 : sc ≠ 0#u64) (hscC : sc ∈ C) {y : Fl4Spec.SchedContext} {n : Nat}
    (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    faults.set_mrs_fault st ar s a snd rcv 0#u64 ⦃ r => r.1.val = min [b, consumedUs y.scConsumed].length 4 ∧
      MrInvN (L := L) T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (tmoS st s sc)
        (tmoSt σ sc y n) rcv xr r.2 [b, consumedUs y.scConsumed] ⦄ := by
  have hP := hP0.e
  have hxs := hX.1.toE.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0⟩ := hfr
  have hrsc : rcv.bv ≠ sc.bv := kheap_ne hkr hky (fun _ h1 h2 => by subst h1; cases h2)
  unfold faults.set_mrs_fault
  step with obj.Tcb.fault_type.spec as ⟨ty, hty'⟩
  step with obj.Tcb.fault_w0.spec as ⟨w0, hw0'⟩
  step with obj.Tcb.fault_w1.spec as ⟨w1, hw1'⟩
  step with obj.Tcb.fault_w2.spec as ⟨w2, hw2'⟩
  step with Endp.obj.Tcb.reg.spec as ⟨pc, hpc'⟩
  subst hty' hw0' hw1' hw2' hpc'
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UserException; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.Timeout; rfl))]
  step with obj.Tcb.sc.spec as ⟨i, hi⟩
  subst hi
  unfold obj.Sc.is_null
  apply ok_bind_spec
  simp only [hsc, hsc0, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (update_consumed_irel hP0 s a σ hX hscC hky hmax htu) ?_
  rintro ⟨cv, s1⟩ ⟨hs1, hcv, -, hI1⟩
  simp only at hs1 hcv hI1
  subst hs1
  have hkr1 : (tmoSt σ sc y n).kheap rcv.bv = some (.tcb xr) := by simp [updK, hrsc, hkr]
  have hM0 := mrInvN_init (L := L) (SR := SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    hI1.1.toE ⟨hI1.2, ScRelM.of hI1.1⟩ hkr1
  refine WP.spec_bind (set_mr_invN (L := L) hE hP hr hkr1 hM0 0#u64 rfl (by decide)
    (L.mem s (tFw0A snd))) ?_
  rintro ⟨k, s2⟩ ⟨hk, hM1⟩
  simp only at hk hM1
  refine WP.spec_mono (set_mr_invN (L := L) hE hP hr hkr1 hM1 k (by simpa using hk) (by simp at hk; omega)
    cv) ?_
  rintro ⟨k2, s3⟩ ⟨hk2, hM2⟩
  simp only at hk2 hM2 ⊢
  rw [hw0, hcv] at hM2
  exact ⟨by simp at hk hk2 ⊢; omega, hM2⟩

set_option maxHeartbeats 4000000 in
/-- **`do_ipc_transfer` of a timeout fault from a thread with an SC on
`IRel`** (IpcTmo's `tmoXfer_top` from `EpHyps`, the receive buffer by
`lookup_buf_full` with `IpcBufCapOK` and `BufCover`): the frame's base is the
state after the SC step (`tmoS`, `tmoSt`). -/
theorem do_ipc_transfer_tmoE (hE : EpHyps st T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))))
    (hP0 : IPlaced N T E R B) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hX : IRel st th cr N T C E R B c s σ) (hOK : Endp.IpcBufCapOK σ) (hBC : Endp.BufCover T B σ)
    {t d : U64} (ht : t ∈ T) (hd : d ∈ T) (htd : t ≠ d) {xt xd : Fl4Spec.Tcb}
    (hks : σ.kheap t.bv = some (.tcb xt)) (hkd : σ.kheap d.bv = some (.tcb xd))
    {bb : Fl4Spec.Word} (hf : xt.tcbFault = some (.timeout bb)) {sc : U64} (hscx : xt.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (e bdg : U64) (g : Bool) :
    ipc.do_ipc_transfer st ar s a t e bdg g d ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) t.bv (some e.bv) bdg.bv g d.bv σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧
      SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s' σ' ∧
      Agree (L.mem (tmoS st s sc)) (L.mem s') (fun b => ¬ RcvReg d b ∧ ¬ BufW B b) ∧
      (∀ q, q ≠ d.bv → σ'.kheap q = (tmoSt σ sc y n).kheap q) ∧
      ∃ x', σ'.kheap d.bv = some (.tcb x') ∧ x'.tcbState = xd.tcbState ⦄ := by
  have hP := hP0.e
  have hR := hX.1.toE
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hsp⟩ := hS.lists
  obtain ⟨x0, hk0, -, -, hscw, -⟩ := hsp.tcb t ht
  rw [hks] at hk0; cases hk0
  have hsc0 : L.mem s (scA t) ≠ 0#u64 := (Notif.optRef_some (hscw.symm.trans hscx)).1
  have hsce : L.mem s (scA t) = sc := P1.eq_of_bv (Notif.optRef_some (hscw.symm.trans hscx)).2
  have hscC : sc ∈ C := by rw [← hsce]; exact hsp.scMem t ht hsc0
  rw [hsce] at hsc0
  have hdsc : d.bv ≠ sc.bv := kheap_ne hkd hky (fun _ h1 h2 => by subst h1; cases h2)
  have hkd' : (tmoSt σ sc y n).kheap d.bv = some (.tcb xd) := by simp [updK, hdsc, hkd]
  have hupd := schedContextUpdateConsumed_eq hky hmax
  have hmsg := makeFaultMsg_timeoutSC hks hscx hupd bb
  have hxs := hR.at_tcb ht hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  have hta := hP.tcb t ht
  have hscw8 : ScW st C c s σ (scW sc 8#u64) := Or.inl (sw_hdr hS hscC (K := 8#u64) (by simp) (by simp) (by decide))
  have hnot : ∀ b, IFoot N T E R B b → b ≠ scW sc 8#u64 := fun b hb e => scw_not_ifoot hP0 hS hX.2.2.2 (e ▸ hscw8) hb
  obtain ⟨y', n', hky', hy⟩ := hsp.scs sc hscC
  rw [hky] at hky'; cases hky'
  have hal8 : Aligned (scW sc 8#u64) := (hy.hdr (K := 8#u64) (by simp) (by simp)).1
  have hty0 : L.mem (tmoS st s sc) (tFaultA t) = 5#u64 := by
    rw [rd_wr_ne hal8 (a_fault hta).1 (fun e => hnot _ (Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl
      (a_fault hta).2⟩)))) e.symm)]
    exact hfr.1
  obtain ⟨⟨⟨G, hBt⟩, hBw⟩, -⟩ := (IpcRel.toSRN hX.1 hX.2).1.1
  have hspec : Fl4Spec.doIpcTransfer (Z := Unit) t.bv (some e.bv) bdg.bv g d.bv σ =
      Fl4Spec.doFaultTransfer (Z := Unit) bdg.bv t.bv d.bv (ipcBufOf true xd) σ := by
    unfold Fl4Spec.doIpcTransfer
    rw [nd_bind_one (lookupIpcBuffer_eq hkd true), nd_bind_one (threadGet_eq _ hks), hf]
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (lookup_buf_full s σ hBt.2.1.1 hBt.2.1.2.1 (Ipc.RelTopB.tcbT hBt hkd) hkd hOK true) ?_
  rintro rw ⟨hrw0, hrwp⟩
  step with obj.Tcb.fault_type.spec as ⟨ft, hft⟩
  have hft0 : ¬ ft = fl4_abi.consts.fault.NullFault := by
    intro h
    have : L.mem s (tFaultA t) = 0#u64 := by rw [← hft, h]; unfold fl4_abi.consts.fault.NullFault; rfl
    rw [hxs.fault0.1 this] at hf; cases hf
  simp only [hft0, ↓reduceIte]
  rw [hspec]
  cases hrb : ipcBufOf true xd with
  | none =>
    obtain rfl : rw = 0#u64 := hrw0.2 hrb
    exact do_fault_transfer_fullN hE hP s a σ ht hd htd hks hkd' hf hmsg hty0 (by rw [mask52]; decide)
      bdg (set_mrs_fault_tmoSCN_E hE hP0 s a σ hX ht hd hks hkd hf hsce hsc0 hscC hky hmax htu)
  | some rp =>
    obtain ⟨x1, hk1, hbw⟩ := hBw.bw d hd
    rw [hkd] at hk1; cases hk1
    have hrwv : rw.bv = rp := hrwp hbw rp hrb
    have hrw0' : rw ≠ 0#u64 := fun e' => by have := hrw0.1 e'; rw [hrb] at this; cases this
    have hmr : BufMap B rw rp := hBC d hd xd true rp hkd hrb rw hrwv
    have hu' : ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr rp k) (tmoSt σ sc y n) := by
      intro k hk
      obtain ⟨sz, hz⟩ := buf_frame_of_ok hOK hkd hrb k hk
      refine ⟨sz, ?_⟩
      have hne : bufAddr rp k &&& ~~~(Fl4Spec.mask (Fl4Spec.pageBitsForSize sz)) ≠ sc.bv := by
        intro e'; rw [e', hky] at hz; cases hz
      simp [updK, hne, hz]
    exact do_fault_transfer_full hE hP s a σ hR ht hd htd hks hkd' hf hmsg (by simp) hty0
      (by rw [mask52]; decide) hmr hu' bdg
      (set_mrs_fault_tmoSC_E hE hP0 s a σ hX ht hd hks hkd hf hsce hsc0 hscC hky hmax htu hrw0' hmr)

end

section SpecT
open Fl4Spec

/-- **The spec's `do_ipc_transfer` of a timeout fault from a thread with an
SC**: the SC's consumed time cleared (`tmoSt`), the receiver's TCB changed in
its user context (two message registers: no receive-buffer word). -/
theorem doIpcTransfer_tmo_eq {σ : State Unit} {snd rcv : ObjRef} {xs xr : Tcb}
    (hks : σ.kheap snd = some (.tcb xs)) (hkr : σ.kheap rcv = some (.tcb xr)) {bb : Word}
    (hf : xs.tcbFault = some (.timeout bb)) {sc : U64} (hscx : xs.tcbSchedContext = some sc.bv)
    {y : SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hmax : maxTicksToUs = core.num.U64.MAX.bv) (ep : Option ObjRef) (badge : Word) (grant : Bool) :
    ∃ x', doIpcTransfer (Z := Unit) snd ep badge grant rcv σ =
      ({((), updK (Ipc.tmoSt σ sc y n) rcv (.tcb x'))}, False) ∧ x' = { xr with tcbArch := x'.tcbArch } := by
  have hrsc : rcv ≠ sc.bv := fun e => by rw [e, hky] at hkr; cases hkr
  have hkrm : (Ipc.tmoSt σ sc y n).kheap rcv = some (.tcb xr) := by simp [updK, hrsc, hkr]
  have hmsg := makeFaultMsg_timeoutSC hks hscx (schedContextUpdateConsumed_eq hky hmax) bb
  have hspec : doIpcTransfer (Z := Unit) snd ep badge grant rcv σ =
      doFaultTransfer (Z := Unit) badge snd rcv (Endp.ipcBufOf true xr) σ := by
    unfold doIpcTransfer
    rw [nd_bind_one (Endp.lookupIpcBuffer_eq hkr true), nd_bind_one (threadGet_eq _ hks), hf]
  have hal : ∀ p, Endp.ipcBufOf true xr = some p → ∀ q ∈ Endp.mrPairs [bb, consumedUs y.scConsumed],
      (Endp.bufAddr p q.1).toNat % 8 = 0 ∧ inUserFrame (Endp.bufAddr p q.1) (Ipc.tmoSt σ sc y n) := by
    intro p _ q hq
    simp [Endp.mrPairs] at hq
  rw [hspec, doFaultTransfer_j hks hkrm hf hmsg _ hal badge]
  have key : ∀ o : KernelObject, updK (jMrSt (Ipc.tmoSt σ sc y n) rcv xr (Endp.ipcBufOf true xr)
      [bb, consumedUs y.scConsumed]) rcv o = updK (Ipc.tmoSt σ sc y n) rcv o := by
    intro o
    cases Endp.ipcBufOf true xr with
    | none => simp only [jMrSt, Endp.mrStateN, updK, Function.update_idem]
    | some p =>
      simp only [jMrSt, Endp.mrState]
      rw [updK_setUm_updK]
      rfl
  exact ⟨_, by rw [key], rfl⟩

end SpecT

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 16000000 in
/-- **The transfer step of `send_ipc` to a waiting receiver for a sender
with a timeout fault and an SC** (module docstring; XTopJointFaultRecv's
`xferFaultStepJ` for the timeout fault): on `IRel` by `do_ipc_transfer_tmoE`
(the base of the frame the state after the SC step, where `IRel` holds by
`sc_step_lift`), the spec's outcome `doIpcTransfer_tmo_eq`; FL4's footprint
the SC word, then the receiver's registers (`do_ipc_transfer_tmo_rg`); P1's
hole by `XS.consumed` and `xfer_all`. -/
theorem xferTmoStepJ {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64}
    {B : Set (U64 × Fl4Spec.Word)} {c : U64} (hP0 : Ipc.IPlaced N T E R B)
    (hHE : EpHyps st T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))))
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s σ)
    (hOK : Endp.IpcBufCapOK σ) (hBC : Endp.BufCover T B σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) {bb : Fl4Spec.Word}
    (hf : xs.tcbFault = some (.timeout bb)) {sc : U64} (hscx : xs.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (ep badge : U64) (grant : Bool)
    {T1 Cs1 Ω Sg Rp Scs Nt Ac1 X : Set U64} {H1 : P1.Heap} {Zb : U64 → Nat} {Q : U64 → U64 → List U64}
    {Rq : U64 → List U64} (hT1 : P1.TcbPlaced T1) (hr1 : rcv ∈ T1)
    (h : P1.SchedQueuesInvX st T1 Cs1 Ω H1 X s Q Rq) (hB : P1.BoundInv st T1 Ac1 s)
    (hX : P1.XInv st T1 Cs1 Ω Sg Rp Scs Nt Zb s) (hS : P1.SCsOK st T1 Ω Sg Scs Zb Ac1 s) (hSg : P1.SgOK st Ω Sg s)
    (hsc1 : sc ∈ Scs) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' => ∃ x' : Fl4Spec.Tcb,
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
        ({((), Notif.updK (Ipc.tmoSt σ sc y n) rcv.bv (.tcb x'))}, False) ∧ x' = { xr with tcbArch := x'.tcbArch } ∧
      EpStateRel T E R B (L.mem s') (Notif.updK (Ipc.tmoSt σ sc y n) rcv.bv (.tcb x')) ∧
      SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s'
        (Notif.updK (Ipc.tmoSt σ sc y n) rcv.bv (.tcb x')) ∧
      Agree (L.mem (tmoS st s sc)) (L.mem s') (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      P1.WritesIn st s s' (fun b => b = scW sc 8#u64 ∨ XferRegW T1 ∅ b) ∧
      P1.SchedQueuesInvX st T1 Cs1 Ω H1 X s' Q Rq ∧ P1.BoundInv st T1 Ac1 s' ∧ P1.XInv st T1 Cs1 Ω Sg Rp Scs Nt Zb s' ∧
      P1.SCsOK st T1 Ω Sg Scs Zb Ac1 s' ∧ P1.SgOK st Ω Sg s' ∧
      (∀ y ∈ T1, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ⦄ := by
  have hP := hP0.e
  have hXr : IRel st th cr N T C E R B c s σ := IpcRel.ofSRN hR hSR
  have hSs := hXr.2.2.1
  obtain ⟨Q0, R0, hc, hsp⟩ := hSs.lists
  obtain ⟨x0, hk0, -, -, hscw, -⟩ := hsp.tcb snd hs
  rw [hks] at hk0; cases hk0
  have hsc0 : L.mem s (scA snd) ≠ 0#u64 := (Notif.optRef_some (hscw.symm.trans hscx)).1
  have hsce : L.mem s (scA snd) = sc := P1.eq_of_bv (Notif.optRef_some (hscw.symm.trans hscx)).2
  have hscC : sc ∈ C := by rw [← hsce]; exact hsp.scMem snd hs hsc0
  rw [hsce] at hsc0
  obtain ⟨y', n', hky', hy⟩ := hsp.scs sc hscC
  rw [hky] at hky'; cases hky'
  have hal8 : P1.Aligned (scW sc 8#u64) := (hy.hdr (K := 8#u64) (by simp) (by simp)).1
  have hscw8 : ScW st C c s σ (scW sc 8#u64) := Or.inl (sw_hdr hSs hscC (K := 8#u64) (by simp) (by simp) (by decide))
  have hupd := schedContextUpdateConsumed_eq hky hmax
  have hI0 : IRel st th cr N T C E R B c (tmoS st s sc) (Ipc.tmoSt σ sc y n) := by
    obtain ⟨hS1, -, -⟩ := hSs.set_sc_consumed hscC hky 0#u64
    have hW : P1.WritesIn st s (tmoS st s sc) (fun b => ScW st C c s σ b ∨ SFootI st T c s b) :=
      (P1.writesIn_wr hal8).mono fun b hb => Or.inl (hb ▸ hscw8)
    exact sc_step_lift hP0 hXr hW (nks_schedContextUpdateConsumed sc.bv σ (_, _) (by rw [hupd]; rfl)) hS1
  have hxs := hR.at_tcb hs hks
  have hty : L.mem s (tFaultA snd) = 5#u64 := by
    have hfr := hxs.faultR
    unfold FaultRel at hfr; rw [hf] at hfr; exact hfr.1
  have hU : schedcontext.update_consumed st arI s a sc ⦃ r => r.2 = tmoS st s sc ⦄ :=
    WP.spec_mono (update_consumed_irel hP0 s a σ hXr hscC hky hmax htu) fun r hr' => hr'.1
  have hrsc : rcv.bv ≠ sc.bv := kheap_ne hkr hky (fun _ h1 h2 => by subst h1; cases h2)
  have hkr0 : (Ipc.tmoSt σ sc y n).kheap rcv.bv = some (.tcb xr) := by simp [updK, hrsc, hkr]
  obtain ⟨x', hspec, hx'⟩ := doIpcTransfer_tmo_eq hks hkr hf hscx hky hmax (some ep.bv) badge.bv grant
    (rcv := rcv.bv)
  -- P1 across the SC word
  have hXS : P1.XS st T1 Cs1 Ω H1 Sg Rp Scs Nt Zb ∅ Ac1 X Q Rq s s :=
    ⟨⟨h, hB, hX, hS, hSg, fun b hb => absurd hb (Set.notMem_empty b)⟩, P1.XferFr.refl s, P1.WritesIn.refl s _⟩
  have hXS1 := P1.XS.consumed (v := 0#u64) hXS hsc1
  rw [← scW8_eq] at hXS1
  obtain ⟨⟨h1, hB1, hX1, hS1, hSg1, hU1⟩, fr1, -⟩ := hXS1
  refine WP.spec_mono (WP.spec_and (do_ipc_transfer_tmoE (ar := arI) hHE hP0 hmax s a σ htu hXr hOK hBC hs hr hne hks hkr
    hf hscx hky ep badge grant) (do_ipc_transfer_tmo_rg (arI := arI) hT1 hr1 s a ep badge grant hty hsce hsc0 hU)) ?_
  rintro s' ⟨⟨σ', h1', h2', h3', h4', h5', x'', h6', h7'⟩, w⟩
  have eσ : σ' = Notif.updK (Ipc.tmoSt σ sc y n) rcv.bv (.tcb x') :=
    congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst (h1'.symm.trans hspec)))
  subst eσ
  obtain ⟨h2, hB2, hX2, hS2, hSg2, -, -, -, -, f2, -⟩ :=
    P1.xfer_all h1 hB1 hX1 hS1 hSg1 hU1 (w.mono fun b hb => P1.XferRegW.foot hb)
  have hN := ntfn_lift_rcv hP0.toC hI0.1.toN h2' hr h4' h5' hkr0 h6' h7'
  refine ⟨x', hspec, hx', h2', ⟨h3', hN⟩, h4', (P1.writesIn_wr hal8).trans w, h2, hB2, hX2, hS2, hSg2,
    fun y0 hy0 K k1 k2 k3 => (f2 y0 hy0 K k1 k2 k3).trans (fr1.2.2.2.2.1 y0 hy0 K k1 k2 k3)⟩

end

end

end Fl4Proofs.P3
