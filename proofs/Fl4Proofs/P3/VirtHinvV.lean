/-
P3x for virtualization (line virt, gen 21, item 1): **`VRelAt` across `handle_invocation`'s tail** for WriteMSR and
WriteVMCB — gen 20's `wrmsr_hinv` / `wrvmcb_hinv` stop at the decode's result and leave FL4's tail `hinvTail`
(syscall.rs l. 196-214) open. Here the tail is walked:

* Success tail (`.Ok`): HandleTop's `flTail` reads the caller's state word and does nothing unless it is
  `TS_RESTART`. The decode's own `vcpu.reply` (vcpu.rs l. 713-722) ends with `set_thread_state ct TS_RUNNING`, so
  after a successful decode the word is `TS_RUNNING` and the tail is the identity. A second walk of the decode
  (stall, reads, `wrmsrTail` / `wrvmcbTail`) exposes it: `reply_run` (`vcpu.reply` leaves the current thread
  `TS_RUNNING`), `ReplyPl.cur_wr` / `ReplyPl.cur_of_writes` (the current thread is kept by the VCPU-word writes and
  the stall), **`wrmsrTail_run`**, **`wrvmcbTail_run`**, **`decode_wrmsr_run`**, **`decode_wrvmcb_run`** (both
  backends), `flTail_running`, **`hinvTail_ok`** (`hinvTail … (.Ok ()) s2 a2 = ok (.Ok (), s2, a2)` once the word is
  `TS_RUNNING`).
* Error tail (`.Err (.Sys e)` with the call flag): `syscall::reply_error` (syscall.rs l. 44-59) writes the caller's
  registers (BADGE, the error MRs that fit, MSG_INFO) and, through `set_mr` / `buf_set`, words of its IPC buffer
  (the fifth lookup-failure word of a guard mismatch, the debug-string word). **`reply_error_w`**: its footprint is
  `P1.RepW t U` (register words `t + [256, 3328)` and the buffer words `U`) given the buffer lookup lands in `U`
  (`P1.BufOK U`); `set_reg_rep`, `lf_w`, `error_mrs_w`. The other error arms return the post-stall state.
  `ReplyPl.ibSame`: the stall (`IPI_PENDING` only) keeps the three words `lookup_ipc_buffer` reads, so the buffer
  fact at the entry state holds after the stall (`P1.lookup_ipc_buffer_same`).
* **`wrmsr_hinvV`**, **`wrvmcb_hinvV`** (both backends): `handle_invocation` from the syscall entry on a VCPU cap
  with the WriteMSR / WriteVMCB label: gen 20's spec-side post (spec dispatcher decode, perform outcomes) with
  **`VRelAt` at `handle_invocation`'s final state** (success: every perform outcome relates; error: the unchanged
  spec state relates), plus `res = (.Ok (), s2, a2)` for the decode's state `s2` on success.
  **`wrmsr_hinvJ`**, **`wrvmcb_hinvJ`**: the same from `JKern` + `JVLay V th U` + `JVm` (`ReplyPl` by
  `JKern.replyPl`, the buffer words off the VCPU by `offV_U` / `JVLay.ua`).

Hypothesis on the caller's IPC buffer: `hB : msg.lookup_ipc_buffer st s true t ⦃ P1.BufOK U ⦄` at the entry state,
with `U`'s words aligned and off the VCPU (in the `J` variants: `JVLay V th U`, so `U` is the layout's user set).
**`hB` [J]** (state fact of the joint relation, not derived in this line): the current thread's IPC-buffer words
(the 128 words from the address `lookup_ipc_buffer` returns) lie in the user set `U`. Justification: FL4
`msg::lookup_ipc_buffer` (msg.rs) returns 0 unless the TCB's buffer slot holds a writable non-device `Frame` cap,
and then the frame pointer plus the in-frame offset checked by `check_valid_ipc_buffer` (`IPC_BUFFER = 10` bits:
the 128 words stay in the frame); at P3's `JAtZ` it is `JAtZ.bufOK` (BufAtJ) with `U = BufU Z σ`, which is
`JAtZ.jvLay`'s user set; mmuAD's `JAtZV3` carries the same JAtZ-shaped base with `jvLay`. Not false on reachable
states: a buffer frame is a user frame, never a VCPU object (`JVLay.uv`).

Other premises: as gen 18–20 — `CapAgree ar a` [P], `CapKeepStall ar` [P], `VirtCodeAgree ar a` [P],
`VirtCodeKeepStall ar` [P]; `P0.ArchTotal ar`. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtVKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtHinvV
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtSanSvm
open Fl4Proofs.P3.VirtVcpuRel Fl4Proofs.P3.VirtMsrEq Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit
open Fl4Proofs.P3.VirtMsrStore Fl4Proofs.P3.VirtVmcbStore Fl4Proofs.P3.VirtReplyKeep Fl4Proofs.P3.VirtVmcbDec
open Fl4Proofs.P3.VirtVmcbTail Fl4Proofs.P3.VirtMsrE2E Fl4Proofs.P3.VirtVmcbE2E Fl4Proofs.P3.VirtArgsSpec
open Fl4Proofs.P3.VirtWrSys Fl4Proofs.P3.VirtWrVmcbVmx Fl4Proofs.P3.VirtMsrDec Fl4Proofs.P3.VirtDispVcpu
open Fl4Proofs.P3.VirtVKeep

noncomputable section

/-! ## The current thread across the decode's writes -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

/-- A write inside the VCPU object keeps the current thread. -/
theorem ReplyPl.cur_wr {v : U64} {s : S} (P : ReplyPl st v s) {o : Word} (ho : o.toNat < 32768)
    (h8 : o.toNat % 8 = 0) (x : U64) (hx : x.bv = v.bv + o) (y : U64) :
    L.mem (L.wr s x y) (curA st (L.wr s x y)) = L.mem s (curA st s) := by
  have ex : x = ⟨v.bv + o⟩ := by rcases x with ⟨b⟩; exact congrArg (fun b => (⟨b⟩ : U64)) hx
  have hxa : P1.Aligned x := by unfold P1.Aligned; rw [ex, vo_val P.fit ho]; have := P.fit.1; omega
  have ec : curA st (L.wr s x y) = curA st s := by
    unfold curA; rw [L.cpu_wr, P1.nodeAt_of_ksb (L.ksb_wr s x y)]
  have ne : x ≠ curA st s := by rw [ex]; exact P.vo_ne_node ho (by simp [layout.node.CUR_THREAD])
  rw [ec, L.mem_wr _ _ _ _ hxa P.curA_al, if_neg ne]

/-- A footprint missing the current-thread word keeps the current thread. -/
theorem ReplyPl.cur_of_writes {v : U64} {s s' : S} (P : ReplyPl st v s) {W : U64 → Prop}
    (h : P1.WritesIn st s s' W) (hc : ¬ W (curA st s)) : L.mem s' (curA st s') = L.mem s (curA st s) := by
  rw [curA_of h, h.2.2 _ P.curA_al hc]

/-- A word of the current thread's TCB is not the `IPI_PENDING` node word. -/
theorem ReplyPl.tw_ne_ipi {v : U64} {s : S} (P : ReplyPl st v s) {K : U64} (hK : K.val < 4096) :
    core.num.U64.wrapping_add (L.mem s (curA st s)) K ≠ ipiA st s := by
  intro e
  have h1 := lay_tw_val P.ctA hK
  have h2 := (P.node (off := layout.node.IPI_PENDING) (by simp [layout.node.IPI_PENDING])).1
  have h4 : layout.node.IPI_PENDING.val < 4288 := by simp [layout.node.IPI_PENDING]
  have h3 := P.ctN
  unfold ipiA at e
  rw [e] at h1
  omega

/-- The stall keeps the three words `lookup_ipc_buffer` reads of the current thread. -/
theorem ReplyPl.ibSame {v : U64} {s s1 : S} (P : ReplyPl st v s) (hW : P1.WritesIn st s s1 (· = ipiA st s)) :
    P1.IbSame (L := L) s s1 (L.mem s (curA st s)) := by
  refine ⟨hW.mem_eq (P1.field_aligned P.ctA (K := 3512#u64) (by simp) (by simp))
      (ReplyPl.tw_ne_ipi P (K := 3512#u64) (by simp)), ?_, ?_⟩
  · rw [P1.sbWordA_eq]
    exact hW.mem_eq (P1.field_aligned P.ctA (by simp) (by simp)) (ReplyPl.tw_ne_ipi P (by simp))
  · rw [P1.sbWordA8_eq]
    exact hW.mem_eq (P1.field_aligned P.ctA (by simp) (by simp)) (ReplyPl.tw_ne_ipi P (by simp))

/-- **`vcpu.reply` leaves the current thread `TS_RUNNING`.** -/
theorem reply_run {v : U64} {s : S} (P : ReplyPl st v s) (call : Bool) (value : U64) :
    vcpu.reply st s call value ⦃ s' => L.mem s' (P1.stA (L.mem s (curA st s))) = sched.TS_RUNNING ⦄ := by
  have hta := P.ctA
  have haa := P.actA_al
  have hne := P.act_ne_st
  unfold vcpu.reply
  refine WP.spec_bind (P1.sched.cur_thread.spec s) fun ct hct => ?_
  have hct' : ct = L.mem s (curA st s) := hct
  subst hct'
  have hsa : P1.Aligned (P1.stA (L.mem s (curA st s))) := by
    rw [P1.stA_eq]; exact P1.field_aligned hta (by simp) (by simp)
  refine WP.spec_bind (Pₘ := fun s1 => P1.WritesIn st s s1 (TW (L.mem s (curA st s)))) ?_ fun s1 h1 => ?_
  · split
    · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s true _ L.total) fun b _ => ?_
      refine WP.spec_bind (set_mr_0 s hta) fun r hr => ?_
      obtain ⟨_, s2⟩ := r
      simp only at hr ⊢
      refine WP.spec_bind (set_reg_tw s2 hta (by simp [layout.reg.BADGE, layout.reg.RDI])) fun s3 h3 => ?_
      refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
      exact WP.spec_mono (set_msg_info_w s3 hta mi) fun s4 h4 =>
        ((hr.trans h3).trans h4).mono fun b hb => hb.elim (fun h => h.elim id id) id
    · exact (WP.spec_ok _).2 (P1.WritesIn.refl _ _)
  · exact WP.spec_mono (sts_w s1 _ sched.TS_RUNNING hsa (by rw [actA_of h1]; exact haa)
      (by rw [actA_of h1]; exact hne)) fun s' hw => hw.2

/-- **WriteMSR's tail leaves the current thread `TS_RUNNING` when it succeeds** (premise `CapAgree` [P]). -/
theorem wrmsrTail_run {a1 : A} (hc : CapAgree ar a1) {s1 : S} {v : U64} (P : ReplyPl st v s1) (f value : U64)
    (amd call : Bool) :
    wrmsrTail st ar s1 a1 v f value amd call ⦃ r => r.1 = .Ok () →
      L.mem r.2.1 (P1.stA (L.mem s1 (curA st s1))) = sched.TS_RUNNING ⦄ := by
  obtain ⟨r, hr, -, haddr⟩ := fl4WriteMsr_rel hc v f value amd
  unfold wrmsrTail
  rw [hr, bind_ok]
  cases r with
  | Ok x =>
    obtain ⟨o, ho, hox⟩ := Option.map_eq_some_iff.1 (haddr x rfl)
    obtain ⟨-, h1, h2, -⟩ := msrOff_cases ho
    dsimp only
    rw [L.write_eq, bind_ok, L.read_eq, bind_ok]
    have e := ReplyPl.cur_wr P h1 h2 x hox.symm value
    refine WP.spec_bind (reply_run (P.wr h1 h2 x hox.symm value) call _) fun s3 h3 =>
      (WP.spec_ok _).2 fun _ => ?_
    rw [e] at h3; exact h3
  | Err e =>
    refine (WP.spec_ok _).2 fun h => ?_
    cases h

set_option maxHeartbeats 4000000 in
/-- **WriteVMCB's tail leaves the current thread `TS_RUNNING` when it succeeds** (premise `CapAgree` [P]). -/
theorem wrvmcbTail_run {a1 : A} (hc : CapAgree ar a1) {s1 : S} {v : U64} (P : ReplyPl st v s1) (f value : U64)
    (call : Bool) :
    wrvmcbTail st ar s1 a1 v f value call ⦃ r => r.1 = .Ok () →
      L.mem r.2.1 (P1.stA (L.mem s1 (curA st s1))) = sched.TS_RUNNING ⦄ := by
  unfold wrvmcbTail
  rw [END_eq, bind_ok, old_eq, bind_ok]
  obtain ⟨r, hr, hrel⟩ := sanitize_vmcb_rel hc f (oldF st s1 v f) value
  rw [hr, bind_ok]
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    intro h; cases h
  | Ok val =>
    rcases hs : sanitizeVmcb f.bv (oldF st s1 v f).bv value.bv with e' | val'
    · rw [hs] at hrel; exact hrel.elim
    have hwf := writable_of_ok hs
    obtain ⟨fa, fl⟩ := svm_writable_nat hwf
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (vset_eq s1 v f val) fun s2 e2 => ?_
    subst e2
    have hx1 : (core.num.U64.wrapping_add v f).bv = v.bv + f.bv := wadd_bv v f
    have P2 := P.wr (o := f.bv) (by omega) fa _ hx1 val
    have c2 := ReplyPl.cur_wr P (o := f.bv) (by omega) fa _ hx1 val
    refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun b _ => ?_
    have hx2 : (core.num.U64.wrapping_add v vcpu.SVM_CPU).bv = v.bv + (vcpu.SVM_CPU).bv := wadd_bv v _
    have hs2 : (vcpu.SVM_CPU).bv.toNat < 32768 := by rw [svmcpu_nat]; omega
    have ha2 : (vcpu.SVM_CPU).bv.toNat % 8 = 0 := by rw [svmcpu_nat]
    refine WP.spec_bind (Pₘ := fun s3 => ReplyPl st v s3 ∧ L.mem s3 (curA st s3) = L.mem s1 (curA st s1)) ?_
      fun s3 h3 => ?_
    · split
      · exact WP.spec_mono (vset_eq _ v vcpu.SVM_CPU 0#u64) fun s3 e3 => by
          subst e3
          exact ⟨P2.wr hs2 ha2 _ hx2 _, by rw [ReplyPl.cur_wr P2 hs2 ha2 _ hx2 _, c2]⟩
      · exact (WP.spec_ok _).2 ⟨P2, c2⟩
    rw [RAX_eq, bind_ok]
    have hx3 : (core.num.U64.wrapping_add v vcpu.REGS).bv = v.bv + VcpuLay.REGS := by rw [wadd_bv, regs_bv]
    have hs3 : VcpuLay.REGS.toNat < 32768 := by decide
    have ha3 : VcpuLay.REGS.toNat % 8 = 0 := by decide
    refine WP.spec_bind (Pₘ := fun s4 => ReplyPl st v s4 ∧ L.mem s4 (curA st s4) = L.mem s1 (curA st s1)) ?_
      fun s4 h4 => ?_
    · split
      · exact WP.spec_mono (vset_eq _ v vcpu.REGS val) fun s4 e4 => by
          subst e4
          exact ⟨h3.1.wr hs3 ha3 _ hx3 _, by rw [ReplyPl.cur_wr h3.1 hs3 ha3 _ hx3 _, h3.2]⟩
      · exact (WP.spec_ok _).2 h3
    refine WP.spec_bind (reply_run h4.1 call val) fun s5 h5 => (WP.spec_ok _).2 fun _ => ?_
    rw [h4.2] at h5; exact h5

set_option maxHeartbeats 1000000 in
/-- **A successful WriteMSR decode leaves the caller `TS_RUNNING`** (premises `CapAgree`, `CapKeepStall` [P]). -/
theorem decode_wrmsr_run (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) {a : A} (hc : CapAgree ar a) {s : S}
    {v : U64} (P : ReplyPl st v s) (length : U64) (call : Bool) (buf : U64) (ex : Aeneas.Std.Array obj.Slot 3#usize)
    (hlen : ¬ length < 2#u64) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteMSR length v call buf ex ⦃ r => r.1 = .Ok () →
      L.mem r.2.1 (P1.stA (L.mem s (curA st s))) = sched.TS_RUNNING ⦄ := by
  rw [decode_wrmsr_eq hA s a length v call buf ex hlen]
  obtain ⟨⟨s1, a1⟩, hp, hW, hc1⟩ := spec_ex (spec_and2 (vcpu_stall_w hA s a v P.ipiA_al) (stall_cap hK hc s v))
  rw [hp, bind_tc_ok]
  dsimp only at hW hc1 ⊢
  have P1' : ReplyPl st v s1 := P.of_writes hW fun e => P.ipi_ne_cur e.symm
  have ec : L.mem s1 (curA st s1) = L.mem s (curA st s) := ReplyPl.cur_of_writes P hW fun e => P.ipi_ne_cur e.symm
  obtain ⟨ct, hct, hcte⟩ := spec_ex (P1.sched.cur_thread.spec (L := L) s1)
  have hcte' : ct = L.mem s1 (curA st s1) := hcte
  subst hcte'
  rw [hct]; simp only [bind_ok, bind_tc_ok]
  obtain ⟨i, hi, -⟩ := spec_ex (hA.virtualization a1)
  rw [hi]; simp only [bind_ok, bind_tc_ok]
  obtain ⟨f, hf⟩ := arg_ok (st := st) s1 (L.mem s1 (curA st s1)) buf (length > 0#u64) 0#u64
  rw [hf]; simp only [bind_ok, bind_tc_ok]
  obtain ⟨value, hval⟩ := arg_ok (st := st) s1 (L.mem s1 (curA st s1)) buf (length > 1#u64) 1#u64
  rw [hval]; simp only [bind_ok, bind_tc_ok]
  rw [← ec]
  exact wrmsrTail_run hc1 P1' f value _ call

set_option maxHeartbeats 1000000 in
/-- **A successful WriteVMCB decode leaves the caller `TS_RUNNING`** (both backends; off SVM the decode fails;
premises `CapAgree`, `CapKeepStall` [P]). -/
theorem decode_wrvmcb_run (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) {a : A} (hc : CapAgree ar a) {s : S}
    {v : U64} (P : ReplyPl st v s) (length : U64) (call : Bool) (buf : U64) (ex : Aeneas.Std.Array obj.Slot 3#usize)
    (hlen : ¬ length < 2#u64) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteVMCB length v call buf ex ⦃ r => r.1 = .Ok () →
      L.mem r.2.1 (P1.stA (L.mem s (curA st s))) = sched.TS_RUNNING ⦄ := by
  rw [decode_wrvmcb_eq s a length v call buf ex hlen]
  obtain ⟨⟨s1, a1⟩, hp, hW, hc1⟩ := spec_ex (spec_and2 (vcpu_stall_w hA s a v P.ipiA_al) (stall_cap hK hc s v))
  rw [hp, bind_tc_ok]
  dsimp only at hW hc1 ⊢
  have P1' : ReplyPl st v s1 := P.of_writes hW fun e => P.ipi_ne_cur e.symm
  have ec : L.mem s1 (curA st s1) = L.mem s (curA st s) := ReplyPl.cur_of_writes P hW fun e => P.ipi_ne_cur e.symm
  obtain ⟨ct, hct, hcte⟩ := spec_ex (P1.sched.cur_thread.spec (L := L) s1)
  have hcte' : ct = L.mem s1 (curA st s1) := hcte
  subst hcte'
  rw [hct]; simp only [bind_ok, bind_tc_ok]
  obtain ⟨i, hi, -⟩ := spec_ex (hA.virtualization a1)
  rw [hi]; simp only [bind_ok, bind_tc_ok]
  obtain ⟨f, hf⟩ := arg_ok (st := st) s1 (L.mem s1 (curA st s1)) buf (length > 0#u64) 0#u64
  rw [hf]; simp only [bind_ok, bind_tc_ok]
  obtain ⟨value, hval⟩ := arg_ok (st := st) s1 (L.mem s1 (curA st s1)) buf (length > 1#u64) 1#u64
  rw [hval]; simp only [bind_ok, bind_tc_ok]
  by_cases hb : i = 2#u64
  · rw [if_pos hb, ← ec]
    exact wrvmcbTail_run hc1 P1' f value call
  · rw [if_neg hb, illegal_eq, bind_ok]
    refine (WP.spec_ok _).2 fun h => ?_
    cases h

/-- HandleTop's success tail is the identity on a `TS_RUNNING` thread. -/
theorem flTail_running {t : U64} {s2 : S} (h : L.mem s2 (P1.stA t) = sched.TS_RUNNING) (is_call : Bool)
    (a2 : A) : flTail (st := st) t is_call s2 a2 = ok (.Ok (), s2, a2) := by
  unfold flTail
  have hs : obj.Tcb.state st t s2 = ok sched.TS_RUNNING := by
    rw [← h]; exact P1.ib_eq_of_spec (P1.obj.Tcb.state.spec s2 t)
  rw [hs, bind_ok, if_neg (by simp [sched.TS_RUNNING, sched.TS_RESTART])]

/-- **`hinvTail`'s success arm is the identity on a `TS_RUNNING` thread.** -/
theorem hinvTail_ok {t : U64} {s2 : S} (h : L.mem s2 (P1.stA t) = sched.TS_RUNNING) (is_call : Bool) (a2 : A) :
    hinvTail st t is_call (.Ok ()) s2 a2 = ok (.Ok (), s2, a2) := by
  unfold hinvTail; exact flTail_running h is_call a2

end

/-! ## The error reply's footprint -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem set_reg_rep {U : Set U64} (s : S) {t r v : U64} (hta : P1.TcbAddr t) (hr : r.val < 384) :
    obj.Tcb.set_reg st t s r v ⦃ s' => P1.WritesIn st s s' (P1.RepW t U) ⦄ :=
  WP.spec_mono (P1.obj.Tcb.set_reg.wrS s t r v hta hr) fun s' ⟨K, hK, e⟩ => by
    subst e
    exact (P1.writesIn_wr (P1.field_aligned hta (by omega) (by omega))).mono fun b e =>
      Or.inl ⟨K, by omega, by omega, by omega, e⟩

/-- An accumulated message-register write. -/
theorem smr_w {U : Set U64} {s0 s : S} {t buf i x : U64} (hta : P1.TcbAddr t) (hb : P1.BufOK U buf)
    (hU : ∀ b ∈ U, P1.Aligned b) (hi : i.val < 127) (h : P1.WritesIn st s0 s (P1.RepW t U)) :
    msg.set_mr st s t buf i x ⦃ r => P1.WritesIn st s0 r.2 (P1.RepW t U) ⦄ :=
  WP.spec_mono (set_mr_w s hta hb hU hi) fun r hr => (h.trans hr).mono fun b hb => hb.elim id id

theorem lf_w {U : Set U64} {s0 s : S} {t buf : U64} (lf : error.LookupFault) (hta : P1.TcbAddr t)
    (hb : P1.BufOK U buf) (hU : ∀ b ∈ U, P1.Aligned b) (h : P1.WritesIn st s0 s (P1.RepW t U)) :
    faults.set_mrs_lookup_failure_at st s t buf lf 1#u64 ⦃ r => P1.WritesIn st s0 r.2 (P1.RepW t U) ⦄ := by
  unfold faults.set_mrs_lookup_failure_at faults.set_mrs_lookup_failure
  have hk : ∀ k : U64, k.val < 4 → (core.num.U64.wrapping_add 1#u64 k).val < 127 := fun k hk => by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine WP.spec_bind (P0.error.LookupFault.type_code.p0 lf) fun i _ => ?_
  refine WP.spec_bind (smr_w (x := i) hta hb hU (by simp) h) ?_
  rintro ⟨i1, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  split
  · exact (WP.spec_ok _).2 h1
  · try simp only [lift, bind_ok]
    exact smr_w hta hb hU (hk 1#u64 (by simp)) h1
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (smr_w hta hb hU (hk 1#u64 (by simp)) h1) ?_
    rintro ⟨_, s2⟩ h2
    simp only at h2
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    exact smr_w hta hb hU (hk 2#u64 (by simp)) h2
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (smr_w hta hb hU (hk 1#u64 (by simp)) h1) ?_
    rintro ⟨_, s2⟩ h2
    simp only at h2
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    refine WP.spec_bind (smr_w hta hb hU (hk 2#u64 (by simp)) h2) ?_
    rintro ⟨_, s3⟩ h3
    simp only at h3
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    exact smr_w hta hb hU (hk 3#u64 (by simp)) h3

theorem error_mrs_w {U : Set U64} {s0 s : S} {t buf : U64} (e : error.SysError) (hta : P1.TcbAddr t)
    (hb : P1.BufOK U buf) (hU : ∀ b ∈ U, P1.Aligned b) (h : P1.WritesIn st s0 s (P1.RepW t U)) :
    syscall.error_mrs st s t buf e ⦃ r => P1.WritesIn st s0 r.2 (P1.RepW t U) ⦄ := by
  unfold syscall.error_mrs
  split
  · exact smr_w hta hb hU (by simp) h
  · exact smr_w hta hb hU (by simp) h
  · exact (WP.spec_ok _).2 h
  · refine WP.spec_bind (smr_w hta hb hU (by simp) h) ?_
    rintro ⟨_, s1⟩ h1
    simp only at h1
    try simp only [WP.uncurry'_pair]
    exact smr_w hta hb hU (by simp) h1
  · exact (WP.spec_ok _).2 h
  · split
    · refine WP.spec_bind (smr_w hta hb hU (by simp) h) ?_
      rintro ⟨_, s1⟩ h1
      simp only at h1
      try simp only [WP.uncurry'_pair]
      exact lf_w _ hta hb hU h1
    · refine WP.spec_bind (smr_w hta hb hU (by simp) h) ?_
      rintro ⟨_, s1⟩ h1
      simp only at h1
      try simp only [WP.uncurry'_pair]
      exact lf_w _ hta hb hU h1
  · exact (WP.spec_ok _).2 h
  · exact (WP.spec_ok _).2 h
  · exact (WP.spec_ok _).2 h
  · exact smr_w hta hb hU (by simp) h

/-- **`syscall::reply_error`'s footprint**: the caller's register words and its IPC-buffer words `U`. -/
theorem reply_error_w {U : Set U64} (s : S) {t : U64} (e : error.SysError) (hta : P1.TcbAddr t)
    (hU : ∀ b ∈ U, P1.Aligned b) (hB : msg.lookup_ipc_buffer st s true t ⦃ P1.BufOK U ⦄) :
    syscall.reply_error st s t e ⦃ s' => P1.WritesIn st s s' (P1.RepW t U) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold syscall.reply_error
  refine WP.spec_bind hB fun buf hb => ?_
  refine WP.spec_bind (set_reg_rep (U := U) (v := 0#u64) s hta (by simp [layout.reg.BADGE, layout.reg.RDI]))
    fun s1 h1 => ?_
  refine WP.spec_bind (error_mrs_w (e := e) hta hb hU h1) ?_
  rintro ⟨len, s2⟩ h2
  simp only at h2
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun r : S × U64 => P1.WritesIn st s r.1 (P1.RepW t U)) ?_ ?_
  · simp only [fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC, ↓reduceIte]
    split
    · rename_i hne
      have h0 : buf ≠ 0#u64 := by simpa using hne
      simp only [syscall.DEBUG_MESSAGE_START]
      step as ⟨i, hi⟩
      refine WP.spec_bind (P0.msg.buf_get.p0 st s2 buf i hS) fun w _ => ?_
      try simp only [lift, bind_ok]
      have hi' : i.val < 128 := by omega
      have hu := hb h0 _ hi'
      unfold msg.buf_set
      simp only [lift, bind_ok]
      refine WP.spec_bind (P1.LawfulStore.write_spec s2 _ _) fun s4 e4 => ?_
      subst e4
      exact (WP.spec_ok _).2 ((h2.trans (P1.writesIn_wr (hU _ hu))).mono fun b hb =>
        hb.elim id fun e => Or.inr (e ▸ hu))
    · exact (WP.spec_ok _).2 h2
  rintro ⟨s3, len1⟩ h3
  simp only at h3
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (P0.error.SysError.code.p0 e) fun i _ => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
  unfold msg.set_msg_info
  refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ => ?_
  exact WP.spec_mono (set_reg_rep (U := U) (v := w) s3 hta (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
    fun s' h' => (h3.trans h').mono fun b hb => hb.elim id id

end

/-! ## `VRelAt` at `handle_invocation`'s final state -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {Z : Type} [StateExt Z]

/-- The error arms of `hinvTail` keep `VRelAt` (the `Sys` reply writes only the caller's registers and buffer). -/
theorem hinvTail_err_vrel {s s1 : S} {v : U64} (P : ReplyPl st v s) (hW : P1.WritesIn st s s1 (· = ipiA st s))
    {U : Set U64} (hUa : ∀ b ∈ U, P1.Aligned b) (hUv : ∀ b ∈ U, b.val + 8 ≤ v.val ∨ v.val + 32768 ≤ b.val)
    (hB : msg.lookup_ipc_buffer st s true (L.mem s (curA st s)) ⦃ P1.BufOK U ⦄) (is_call : Bool)
    (e : error.Exc) (a1 : A) {res : (core.result.Result Unit error.Exc) × S × A}
    (h : hinvTail st (L.mem s (curA st s)) is_call (.Err e) s1 a1 = ok res) {σ : State Z}
    (hR : VRelAt (memW st s1) σ v.bv) : VRelAt (memW st res.2.1) σ v.bv := by
  unfold hinvTail at h
  cases e with
  | Sys e2 =>
    dsimp only at h
    by_cases hcall : is_call = true
    · rw [if_pos hcall] at h
      obtain ⟨s', hs', -⟩ := spec_ex (P0.syscall.reply_error.p0 st s1 (L.mem s (curA st s)) e2 L.total)
      rw [hs', bind_ok] at h
      have hres := ok_inj h
      subst hres
      have hB1 : msg.lookup_ipc_buffer st s1 true (L.mem s (curA st s)) ⦃ P1.BufOK U ⦄ := by
        rw [P1.lookup_ipc_buffer_same (ReplyPl.ibSame P hW)]; exact hB
      have hw := P1.spec_at (reply_error_w s1 e2 P.ctA hUa hB1) hs'
      refine VRelAt.congrA (agreeA_of_off P.fit hw ?_) hR
      rintro b (⟨K, hK1, hK2, -, rfl⟩ | hb) -
      · have e1 := lay_tw_val P.ctA (K := K) (by omega)
        have := P.ctV
        omega
      · exact hUv b hb
    · rw [if_neg hcall] at h
      rw [← ok_inj h]; exact hR
  | Fault _ => dsimp only at h; rw [← ok_inj h]; exact hR
  | Lookup _ => dsimp only at h; rw [← ok_inj h]; exact hR
  | Preempted => dsimp only at h; rw [← ok_inj h]; exact hR

set_option maxHeartbeats 1000000 in
/-- **WriteMSR through `handle_invocation`, tail included** (module docstring; premises `CapAgree`,
`CapKeepStall`, `VirtCodeAgree`, `VirtCodeKeepStall` [P]; `hB` [J]). -/
theorem wrmsr_hinvV (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) (hKv : VirtCodeKeepStall ar) {a : A}
    (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S} (is_call blocking can_donate fp : Bool) (cptr : U64)
    {t : U64} (ht : sched.cur_thread st s = ok t) {info : msginfo.MessageInfo}
    (hinfo : msg.msg_info st s t = ok info) (hlbl : info.label = fl4_abi.label.X86VCPUWriteMSR)
    {r1 : cspace.Resolved} (hlk : cspace.lookup_slot st s t cptr = ok (.Ok r1)) {v : U64}
    (hcap : obj.Slot.cap st r1.slot s = ok (.Vcpu v)) {buf : U64}
    (hbuf : msg.lookup_ipc_buffer st s false t = ok buf) {e : Aeneas.Std.Array obj.Slot 3#usize}
    (hex : ipc.lookup_extra_caps st s t buf info = ok (.Ok e)) (hlen : ¬ msgLen info buf < 2#u64)
    (P : ReplyPl st v s) {σ : State Z} (hR : VRelAt (memW st s) σ v.bv) {regs : Register → Word}
    (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hL : (msgLen info buf).val = len) {label : Data}
    (hl : vcpuLabelOf label = some .writeMsr) (sfp : Bool) (ci : CapRef) (ssl : CslotPtr)
    (caps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (onCore : ObjRef → Bool) (sb sc sd : Bool)
    {U : Set U64} (hUa : ∀ b ∈ U, P1.Aligned b) (hUv : ∀ b ∈ U, b.val + 8 ≤ v.val ∨ v.val + 32768 ≤ b.val)
    (hB : msg.lookup_ipc_buffer st s true t ⦃ P1.BufOK U ⦄) :
    syscall.handle_invocation st ar s a is_call blocking can_donate fp cptr ⦃ res =>
      (∃ (r3 : core.result.Result Unit error.Exc) (s2 : S) (a2 : A),
        vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteMSR (msgLen info buf) v is_call buf e = ok (r3, s2, a2) ∧
        (r3 = .Ok () → res = (.Ok (), s2, a2))) ∧
      ∃ (s1 : S) (a1 : A), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ((∃ f value : U64,
            (fl4DecodeInvocationV (Z := Z) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ =
              ({(.ok (.vcpu (.writeMsr v.bv f.bv value.bv)), σ)}, False) ∧ res.1 = .Ok () ∧
            ∀ x ∈ ((fl4PerformInvocationV (Z := Z) onCore sb sc sd (.vcpu (.writeMsr v.bv f.bv value.bv))).run σ).1,
              (∃ rr, x.1 = .ok rr) ∧ VRelAt (memW st res.2.1) x.2 v.bv) ∨
          (∃ e e', (fl4DecodeInvocationV (Z := Z) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ = ({(.error e', σ)}, False) ∧
            SysErrRel e e' ∧ VRelAt (memW st res.2.1) σ v.bv)) ⦄ := by
  have htc : t = L.mem s (curA st s) := by
    have h0 := P1.spec_at (P1.sched.cur_thread.spec (L := L) s) ht; exact h0
  refine WP.spec_mono (wrmsr_hinv (Z := Z) (sbo := sbo) (um := um) hA hK hKv hc hk is_call blocking can_donate fp
    cptr ht hinfo hlbl hlk hcap hbuf hex hlen P hR hregs hL hl sfp ci ssl caps buffer onCore sb sc sd) ?_
  rintro res ⟨r3, s2, a2, hd, htl, s1, a1, hp, hW, hpost⟩
  have hrun := P1.spec_at (decode_wrmsr_run hA hK hc P (msgLen info buf) is_call buf e hlen) hd
  subst htc
  rcases hpost with ⟨f, value, hd', hr3, hperf⟩ | ⟨e1, e', hd', hE, hr3, hs2, hV⟩
  · subst hr3
    have hres : res = (.Ok (), s2, a2) := by
      rw [hinvTail_ok (hrun rfl)] at htl; exact (ok_inj htl).symm
    subst hres
    exact ⟨⟨_, s2, a2, hd, fun _ => rfl⟩, s1, a1, hp, hW, Or.inl ⟨f, value, hd', rfl, hperf⟩⟩
  · subst hr3; subst hs2
    refine ⟨⟨_, s2, a2, hd, fun h => by cases h⟩, s2, a1, hp, hW, Or.inr ⟨e1, e', hd', hE, ?_⟩⟩
    exact hinvTail_err_vrel P hW hUa hUv hB is_call e1 a2 htl hV

set_option maxHeartbeats 1000000 in
/-- **WriteVMCB through `handle_invocation`, tail included, both backends** (premises as `wrmsr_hinvV`). -/
theorem wrvmcb_hinvV (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) (hKv : VirtCodeKeepStall ar) {a : A}
    (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S} (is_call blocking can_donate fp : Bool) (cptr : U64)
    {t : U64} (ht : sched.cur_thread st s = ok t) {info : msginfo.MessageInfo}
    (hinfo : msg.msg_info st s t = ok info) (hlbl : info.label = fl4_abi.label.X86VCPUWriteVMCB)
    {r1 : cspace.Resolved} (hlk : cspace.lookup_slot st s t cptr = ok (.Ok r1)) {v : U64}
    (hcap : obj.Slot.cap st r1.slot s = ok (.Vcpu v)) {buf : U64}
    (hbuf : msg.lookup_ipc_buffer st s false t = ok buf) {e : Aeneas.Std.Array obj.Slot 3#usize}
    (hex : ipc.lookup_extra_caps st s t buf info = ok (.Ok e)) (hlen : ¬ msgLen info buf < 2#u64)
    (P : ReplyPl st v s) {σ : State Z} (hR : VRelAt (memW st s) σ v.bv) {regs : Register → Word}
    (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hL : (msgLen info buf).val = len) {label : Data}
    (hl : vcpuLabelOf label = some .writeVmcb) (sfp : Bool) (ci : CapRef) (ssl : CslotPtr)
    (caps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (onCore : ObjRef → Bool) (sb sc sd : Bool)
    {U : Set U64} (hUa : ∀ b ∈ U, P1.Aligned b) (hUv : ∀ b ∈ U, b.val + 8 ≤ v.val ∨ v.val + 32768 ≤ b.val)
    (hB : msg.lookup_ipc_buffer st s true t ⦃ P1.BufOK U ⦄) :
    syscall.handle_invocation st ar s a is_call blocking can_donate fp cptr ⦃ res =>
      (∃ (r3 : core.result.Result Unit error.Exc) (s2 : S) (a2 : A),
        vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteVMCB (msgLen info buf) v is_call buf e = ok (r3, s2, a2) ∧
        (r3 = .Ok () → res = (.Ok (), s2, a2))) ∧
      ∃ (s1 : S) (a1 : A), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ((∃ (f : U64) (val : Word),
            (fl4DecodeInvocationV (Z := Z) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ =
              ({(.ok (.vcpu (.writeVmcb v.bv f.bv val)), σ)}, False) ∧ res.1 = .Ok () ∧
            ∀ x ∈ ((fl4PerformInvocationV (Z := Z) onCore sb sc sd (.vcpu (.writeVmcb v.bv f.bv val))).run σ).1,
              (∃ rr, x.1 = .ok rr) ∧ VRelAt (memW st res.2.1) x.2 v.bv) ∨
          (∃ e e', (fl4DecodeInvocationV (Z := Z) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ = ({(.error e', σ)}, False) ∧
            SysErrRel e e' ∧ VRelAt (memW st res.2.1) σ v.bv)) ⦄ := by
  have htc : t = L.mem s (curA st s) := by
    have h0 := P1.spec_at (P1.sched.cur_thread.spec (L := L) s) ht; exact h0
  refine WP.spec_mono (wrvmcb_hinv (Z := Z) (sbo := sbo) (um := um) hA hK hKv hc hk is_call blocking can_donate fp
    cptr ht hinfo hlbl hlk hcap hbuf hex hlen P hR hregs hL hl sfp ci ssl caps buffer onCore sb sc sd) ?_
  rintro res ⟨r3, s2, a2, hd, htl, s1, a1, hp, hW, hpost⟩
  have hrun := P1.spec_at (decode_wrvmcb_run hA hK hc P (msgLen info buf) is_call buf e hlen) hd
  subst htc
  rcases hpost with ⟨f, val, hd', hr3, hperf⟩ | ⟨e1, e', hd', hE, hr3, hs2, hV⟩
  · subst hr3
    have hres : res = (.Ok (), s2, a2) := by
      rw [hinvTail_ok (hrun rfl)] at htl; exact (ok_inj htl).symm
    subst hres
    exact ⟨⟨_, s2, a2, hd, fun _ => rfl⟩, s1, a1, hp, hW, Or.inl ⟨f, val, hd', rfl, hperf⟩⟩
  · subst hr3; subst hs2
    refine ⟨⟨_, s2, a2, hd, fun h => by cases h⟩, s2, a1, hp, hW, Or.inr ⟨e1, e', hd', hE, ?_⟩⟩
    exact hinvTail_err_vrel P hW hUa hUv hB is_call e1 a2 htl hV

end

/-! ## From the joint-state records -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {AI : Type} {arI : machine.Arch AI}
variable {H : P1.Heap} {Cs D : Set U64} {th : TypedHeap} {σ : Fl4Spec.State Unit} {V U : Set U64}

/-- The user set's words are off every VCPU of `V` (`JVLay.uv`, both aligned). -/
theorem uv_off (Ly : JVLay V th U) {v : U64} (hv : v ∈ V) : ∀ b ∈ U, b.val + 8 ≤ v.val ∨ v.val + 32768 ≤ b.val :=
  fun b hb => offV_U Ly hb v hv

set_option maxHeartbeats 1000000 in
/-- **`wrmsr_hinvV` from `JKern` + `JVLay` + `JVm`** (premises as `wrmsr_hinvV`). -/
theorem wrmsr_hinvJ (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) (hKv : VirtCodeKeepStall ar) {a : A}
    (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S}
    (Kn : JKern (L := L) arI H Cs D th s σ) (Ly : JVLay V th U) (Jv : JVm (L := L) V H s σ) {v : U64} (hvV : v ∈ V)
    (is_call blocking can_donate fp : Bool) (cptr : U64)
    {t : U64} (ht : sched.cur_thread st s = ok t) {info : msginfo.MessageInfo}
    (hinfo : msg.msg_info st s t = ok info) (hlbl : info.label = fl4_abi.label.X86VCPUWriteMSR)
    {r1 : cspace.Resolved} (hlk : cspace.lookup_slot st s t cptr = ok (.Ok r1))
    (hcap : obj.Slot.cap st r1.slot s = ok (.Vcpu v)) {buf : U64}
    (hbuf : msg.lookup_ipc_buffer st s false t = ok buf) {e : Aeneas.Std.Array obj.Slot 3#usize}
    (hex : ipc.lookup_extra_caps st s t buf info = ok (.Ok e)) (hlen : ¬ msgLen info buf < 2#u64)
    (hR : VRelAt (memW st s) σ v.bv) {regs : Register → Word}
    (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hL : (msgLen info buf).val = len) {label : Data}
    (hl : vcpuLabelOf label = some .writeMsr) (sfp : Bool) (ci : CapRef) (ssl : CslotPtr)
    (caps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (onCore : ObjRef → Bool) (sb sc sd : Bool)
    (hB : msg.lookup_ipc_buffer st s true t ⦃ P1.BufOK U ⦄) :
    syscall.handle_invocation st ar s a is_call blocking can_donate fp cptr ⦃ res =>
      (∃ (r3 : core.result.Result Unit error.Exc) (s2 : S) (a2 : A),
        vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteMSR (msgLen info buf) v is_call buf e = ok (r3, s2, a2) ∧
        (r3 = .Ok () → res = (.Ok (), s2, a2))) ∧
      ∃ (s1 : S) (a1 : A), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ((∃ f value : U64,
            (fl4DecodeInvocationV (Z := Unit) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ =
              ({(.ok (.vcpu (.writeMsr v.bv f.bv value.bv)), σ)}, False) ∧ res.1 = .Ok () ∧
            ∀ x ∈ ((fl4PerformInvocationV (Z := Unit) onCore sb sc sd (.vcpu (.writeMsr v.bv f.bv value.bv))).run σ).1,
              (∃ rr, x.1 = .ok rr) ∧ VRelAt (memW st res.2.1) x.2 v.bv) ∨
          (∃ e e', (fl4DecodeInvocationV (Z := Unit) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ = ({(.error e', σ)}, False) ∧
            SysErrRel e e' ∧ VRelAt (memW st res.2.1) σ v.bv)) ⦄ :=
  wrmsr_hinvV hA hK hKv hc hk is_call blocking can_donate fp cptr ht hinfo hlbl hlk hcap hbuf hex hlen
    (JKern.replyPl Kn Ly Jv hvV) hR hregs hL hl sfp ci ssl caps buffer onCore sb sc sd Ly.ua (uv_off Ly hvV) hB

set_option maxHeartbeats 1000000 in
/-- **`wrvmcb_hinvV` from `JKern` + `JVLay` + `JVm`** (premises as `wrmsr_hinvV`). -/
theorem wrvmcb_hinvJ (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) (hKv : VirtCodeKeepStall ar) {a : A}
    (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S}
    (Kn : JKern (L := L) arI H Cs D th s σ) (Ly : JVLay V th U) (Jv : JVm (L := L) V H s σ) {v : U64} (hvV : v ∈ V)
    (is_call blocking can_donate fp : Bool) (cptr : U64)
    {t : U64} (ht : sched.cur_thread st s = ok t) {info : msginfo.MessageInfo}
    (hinfo : msg.msg_info st s t = ok info) (hlbl : info.label = fl4_abi.label.X86VCPUWriteVMCB)
    {r1 : cspace.Resolved} (hlk : cspace.lookup_slot st s t cptr = ok (.Ok r1))
    (hcap : obj.Slot.cap st r1.slot s = ok (.Vcpu v)) {buf : U64}
    (hbuf : msg.lookup_ipc_buffer st s false t = ok buf) {e : Aeneas.Std.Array obj.Slot 3#usize}
    (hex : ipc.lookup_extra_caps st s t buf info = ok (.Ok e)) (hlen : ¬ msgLen info buf < 2#u64)
    (hR : VRelAt (memW st s) σ v.bv) {regs : Register → Word}
    (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hL : (msgLen info buf).val = len) {label : Data}
    (hl : vcpuLabelOf label = some .writeVmcb) (sfp : Bool) (ci : CapRef) (ssl : CslotPtr)
    (caps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (onCore : ObjRef → Bool) (sb sc sd : Bool)
    (hB : msg.lookup_ipc_buffer st s true t ⦃ P1.BufOK U ⦄) :
    syscall.handle_invocation st ar s a is_call blocking can_donate fp cptr ⦃ res =>
      (∃ (r3 : core.result.Result Unit error.Exc) (s2 : S) (a2 : A),
        vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteVMCB (msgLen info buf) v is_call buf e = ok (r3, s2, a2) ∧
        (r3 = .Ok () → res = (.Ok (), s2, a2))) ∧
      ∃ (s1 : S) (a1 : A), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ((∃ (f : U64) (val : Word),
            (fl4DecodeInvocationV (Z := Unit) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ =
              ({(.ok (.vcpu (.writeVmcb v.bv f.bv val)), σ)}, False) ∧ res.1 = .Ok () ∧
            ∀ x ∈ ((fl4PerformInvocationV (Z := Unit) onCore sb sc sd (.vcpu (.writeVmcb v.bv f.bv val))).run σ).1,
              (∃ rr, x.1 = .ok rr) ∧ VRelAt (memW st res.2.1) x.2 v.bv) ∨
          (∃ e e', (fl4DecodeInvocationV (Z := Unit) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ = ({(.error e', σ)}, False) ∧
            SysErrRel e e' ∧ VRelAt (memW st res.2.1) σ v.bv)) ⦄ :=
  wrvmcb_hinvV hA hK hKv hc hk is_call blocking can_donate fp cptr ht hinfo hlbl hlk hcap hbuf hex hlen
    (JKern.replyPl Kn Ly Jv hvV) hR hregs hL hl sfp ci ssl caps buffer onCore sb sc sd Ly.ua (uv_off Ly hvV) hB

end

end
end Fl4Proofs.P3.VirtHinvV
