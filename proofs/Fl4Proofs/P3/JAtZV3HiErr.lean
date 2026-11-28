/-
P3 (line mmuAD, gen 41): **FL4's `reply_error` at `JAtZV3`** (syscall.rs l. 197) against the spec's
`fl4ReplyFromKernelError true` (Ext/ReplyError; `KERNEL_INVOCATION_REPORT_ERROR_IPC` is set).

* **`JAtZV3.replyErrJ3`**: XTopJointReplyTail's `JAtZ.replyErrJ` at `JAtZV3`: the badge and the message info by
  gen 33's `JAtZV3.regWr`, the error words by `error_mrs_gen` with the invariant "`JAtZV3` at the spec's `set_mrs`
  state" and gen 34's `setMrJ3` (+ `zv_setMr_ret` for the length), the debug word by gen 33's `JAtZV3.userWr`
  (`JAtZB.bufWordG` / `JAtZB.bufPlacedJ` at the words' state); the spec side `fl4ReplyErr_eq` (ReplyFailX).
  Hand-written (the source's steps over `JAtZ` replaced), so the default heartbeats apart from the proof's one
  `maxHeartbeats 4000000`.
* **`JAtZV3.replyFailJ3`**: the error reply when called (HandleTopX's `ReplyHypMX.fail` program).

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3HiRep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 4000000 in
/-- **FL4's `reply_error` at `JAtZV3`** (module docstring). -/
theorem JAtZV3.replyErrJ3 (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ)
    {ct : U64} (hcur : σ.curThread = ct.bv) (e : error.SysError) (e' : Fl4Spec.SyscallError)
    (he : ErrRel (.Sys e) e') :
    syscall.reply_error st s ct e ⦃ s2 =>
      ∃ z ∈ (Fl4Spec.fl4ReplyFromKernelError (Z := Unit) true ct.bv (Fl4Spec.msgFromSyscallError e') σ).1,
        JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s2 a z.2 ⦄ := by
  have B := J.z2.zv.base
  have hct : ct ∈ Z.T := TopSR.cur_mem B.xtop.fin.1 hcur.symm
  obtain ⟨htcb, x, hk⟩ := B.xtop.curTcb hcur
  obtain ⟨x', hk', hwx⟩ := B.buf ct hct
  rw [hk] at hk'; cases hk'
  have hOK0 := B.bok
  have hmsl : (Fl4Spec.msgFromSyscallError e').2.length ≤ 5 := msgErr_len e'
  have hflag : fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC = true := by
    unfold fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC; rfl
  have hdm : syscall.DEBUG_MESSAGE_START + 1#u64 = ok 7#u64 := by
    unfold syscall.DEBUG_MESSAGE_START; rfl
  unfold syscall.reply_error
  refine WP.spec_bind (WP.spec_and (lookup_buf_full s σ B.xtop.rel.2.1.1 B.xtop.rel.2.1.2.1 htcb hk hOK0 true)
    (J.replyBuf hct hk)) ?_
  rintro w ⟨⟨hw0, hwp⟩, hjb⟩
  have hbm : ∀ q, Endp.ipcBufOf true x = some q → Endp.BufMap Z.B w q := fun q hq =>
    bufCover_of_frameCover B.bok B.fcov ct hct x true q hk hq w (hwp hwx q hq)
  have hfr : ∀ p, Endp.ipcBufOf true x = some p →
      ∀ k, k < 128 → (Endp.bufAddr p k).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p k) σ :=
    fun p hp k hk128 => ⟨Endp.bufAddr_aligned B.xtop.fin.1.2.ep (hbm p hp) k, buf_frame_of_ok hOK0 hk hp k hk128⟩
  have hspec := fl4ReplyErr_eq hk (Fl4Spec.msgFromSyscallError e').1 (Fl4Spec.msgFromSyscallError e').2
    (by omega) hfr
  suffices hsuf : (do
      let s1 ← obj.Tcb.set_reg st ct s layout.reg.BADGE 0#u64
      let (len, s2) ← syscall.error_mrs st s1 ct w e
      let (s3, len1) ←
        if fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC
        then
          if w != 0#u64
          then
            do
            let i ← syscall.DEBUG_MESSAGE_START + 1#u64
            let w1 ← msg.buf_get st s2 w i
            let i1 ← lift (~~~255#u64)
            let i2 ← lift (w1 &&& i1)
            let s3 ← msg.buf_set st s2 w i i2
            let len1 ← lift (core.num.U64.wrapping_add len 1#u64)
            ok (s3, len1)
          else ok (s2, len)
        else ok (s2, len)
      let i ← error.SysError.code e
      let mi ← msginfo.MessageInfo.new i 0#u64 0#u64 len1
      msg.set_msg_info st s3 ct mi) ⦃ s2 =>
        JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s2 a (replyErrState σ ct.bv x (Fl4Spec.msgFromSyscallError e').1
          (Fl4Spec.msgFromSyscallError e').2) ⦄ by
    refine WP.spec_mono hsuf ?_
    intro s2 J2
    refine ⟨((), replyErrState σ ct.bv x (Fl4Spec.msgFromSyscallError e').1 (Fl4Spec.msgFromSyscallError e').2),
      ?_, J2⟩
    rw [hspec]; exact Set.mem_singleton _
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.BADGE 0#u64) ?_
  rintro s1 rfl
  -- the badge
  have J1 := J.regWr hct hk Fl4Spec.badge_register 0#u64
  rw [Endp.regIdx_badge] at J1
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  rw [e0] at J1
  set xA := Notif.setReg x Fl4Spec.badge_register 0 with hxA
  set σA := Notif.updK σ ct.bv (.tcb xA) with hσA
  have hkA : σA.kheap ct.bv = some (.tcb xA) := by simp [σA, Notif.updK]
  set s1 := L.wr s (Endp.regA ct layout.reg.BADGE) 0#u64 with hs1
  set buf := Endp.ipcBufOf true x with hbuf
  have hjb' : JBufR Z.B w buf := hjb
  -- the words
  let I : S → List Fl4Spec.Word → Prop := fun s' ms =>
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s' a (MrS σA ct.bv xA buf ms)
  have hI0 : I s1 [] := by
    show JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s1 a (MrS σA ct.bv xA buf [])
    rw [MrS_nil hkA]; exact J1
  have step : ∀ (s' : S) (ms1 : List Fl4Spec.Word), I s' ms1 → ∀ (i : U64), i.val = ms1.length →
      ms1.length < 120 → ∀ v : U64, msg.set_mr st s' ct w i v ⦃ r => r.1.val = mrLen buf (ms1.length + 1) ∧
        I r.2 (ms1 ++ [v.bv]) ⦄ := by
    intro s' ms1 J' i hi hi' v
    have J'' : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s' a (jMrSt σA ct.bv xA buf ms1) := by
      rw [← zv_MrS_jMrSt]; exact J'
    refine WP.spec_mono (WP.spec_and (setMrJ3 J'' hct (fun p h => h) hjb' i (by omega) hi' v)
      (zv_setMr_ret hjb' s' i v (by omega))) ?_
    rintro r ⟨h1, h2⟩
    have em : mrUpd ms1 i.val v.bv = ms1 ++ [v.bv] := by unfold mrUpd; rw [if_neg (by omega)]
    rw [em, ← zv_MrS_jMrSt] at h1
    exact ⟨by rw [h2, zv_jMrRet_mrLen, hi], h1⟩
  refine WP.spec_bind (error_mrs_gen ct buf w I step s1 hI0 e e' he) ?_
  rintro ⟨len, s3⟩ ⟨hlen, J3⟩
  simp only at hlen J3
  change JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s3 a (MrS σA ct.bv xA buf (Fl4Spec.msgFromSyscallError e').2) at J3
  have hkM := MrS_kheap_t σA ct.bv xA buf (Fl4Spec.msgFromSyscallError e').2
  cases hb : Endp.ipcBufOf true x with
  | none =>
    have hbn : buf = none := hb
    rw [hbn] at J3 hlen hkM
    have hw : w = 0#u64 := hw0.2 hb
    simp only [hflag, hw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine WP.spec_bind (code_label he) ?_
    rintro cd hcd
    unfold msginfo.MessageInfo.new
    simp only [bind_ok]
    have hl128 : len.val < 128 := by rw [hlen]; simp only [mrLen]; omega
    refine WP.spec_mono (Endp.set_msg_info_spec _ ct cd len hl128) ?_
    rintro s4 ⟨v, rfl, hv⟩
    rw [← Endp.regIdx_msgInfo]
    have J4 := J3.regWr hct hkM Fl4Spec.msg_info_register v
    have hvd : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen none (Fl4Spec.msgFromSyscallError e').2.length),
        0, 0, (Fl4Spec.msgFromSyscallError e').1⟩ := by
      rw [hv, hcd]; congr 2
      apply BitVec.eq_of_toNat_eq; simp only [Fl4Spec.natToLen, BitVec.toNat_ofNat, UScalar.bv_toNat, hlen, mrLen]; omega
    unfold replyErrState
    simp only [hb]
    rw [← hvd]; exact J4
  | some p =>
    have hbs : buf = some p := hb
    rw [hbs] at J3 hlen hkM
    have hw : w ≠ 0#u64 := fun h => by rw [hbs] at hw0; cases hw0.1 h
    have hbw : (w != 0#u64) = true := by simp [hw]
    simp only [hflag, hbw, ↓reduceIte, hdm, bind_ok]
    have hdbg : (do
        let w_1 ← msg.buf_get st s3 w 7#u64
        let i1 ← lift (~~~255#u64)
        let i2 ← lift (w_1 &&& i1)
        let s4 ← msg.buf_set st s3 w 7#u64 i2
        let len2 ← lift (core.num.U64.wrapping_add len 1#u64)
        ok (s4, len2)) ⦃ r => r = (L.wr s3 (Endp.fl4BufA w 7#u64) (L.mem s3 (Endp.fl4BufA w 7#u64) &&& ~~~255#u64),
          core.num.U64.wrapping_add len 1#u64) ⦄ := by
      refine WP.spec_bind (Endp.msg.buf_get.spec s3 w 7#u64) ?_
      rintro dv rfl
      simp only [lift, bind_ok]
      refine WP.spec_bind (Endp.msg.buf_set.spec s3 w 7#u64 _) ?_
      rintro s4 rfl
      simp only [bind_ok, WP.spec_ok]
    refine WP.spec_bind hdbg ?_
    rintro r rfl
    have hpair := hbm p hb 7#u64 (by decide)
    set σM := MrS σA ct.bv xA (some p) (Fl4Spec.msgFromSyscallError e').2 with hσM
    have hdv : (L.mem s3 (Endp.fl4BufA w 7#u64)).bv = Endp.loadWordAt σM.machineState.underlyingMemory (Endp.bufAddr p 7) :=
      J3.z2.zv.base.xtop.fin.1.1.2.1.buf _ hpair
    have hval : (L.mem s3 (Endp.fl4BufA w 7#u64) &&& ~~~255#u64).bv =
        Endp.loadWordAt σM.machineState.underlyingMemory (Endp.bufAddr p 7) &&& ~~~(255 : Fl4Spec.Word) := by
      rw [UScalar.bv_and]; exact congrArg₂ (· &&& ·) hdv rfl
    have hqM : Endp.ipcBufOf true (Endp.withRegs xA (Endp.mrRegs xA.tcbArch.tcbContext.userRegs
        (Fl4Spec.msgFromSyscallError e').2)) = some p := hb
    obtain ⟨hAp, hObj⟩ := J3.z2.zv.base.bufWordG J3.z2.zv.base.bok htcb hkM hqM 7 (by decide)
      (b := Endp.fl4BufA w 7#u64) (by rw [fl4BufA_bv, hwp hwx p hb]; rfl)
    have hBP3 : Vs.BufPlaced (L := L) Z.N Z.C Z.B Z.c s3 σM := J3.z2.zv.base.bufPlacedJ
    have J4 := J3.userWr hBP3 hpair hAp hObj (L.mem s3 (Endp.fl4BufA w 7#u64) &&& ~~~255#u64)
    simp only [hval] at J4
    refine WP.spec_bind (code_label he) ?_
    rintro cd hcd
    unfold msginfo.MessageInfo.new
    simp only [bind_ok]
    have hl128 : (core.num.U64.wrapping_add len 1#u64).val < 128 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hlen, mrLen]; omega
    refine WP.spec_mono (Endp.set_msg_info_spec _ ct cd _ hl128) ?_
    rintro s5 ⟨v, rfl, hv⟩
    rw [← Endp.regIdx_msgInfo]
    have hkD : (Endp.setUm σM (Endp.storeMem σM.machineState.underlyingMemory (Endp.bufAddr p 7)
        (Endp.loadWordAt σM.machineState.underlyingMemory (Endp.bufAddr p 7) &&& ~~~(255 : Fl4Spec.Word)))).kheap ct.bv =
        some (.tcb (Endp.withRegs xA (Endp.mrRegs xA.tcbArch.tcbContext.userRegs (Fl4Spec.msgFromSyscallError e').2))) :=
      hkM
    have J5 := J4.regWr hct hkD Fl4Spec.msg_info_register v
    have hvd : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen (some p)
        (Fl4Spec.msgFromSyscallError e').2.length) + 1, 0, 0, (Fl4Spec.msgFromSyscallError e').1⟩ := by
      rw [hv, hcd]; congr 2
      apply BitVec.eq_of_toNat_eq
      simp [Fl4Spec.natToLen, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hlen, mrLen]
    unfold replyErrState
    simp only [hb]
    rw [← hvd]; exact J5

/-- **The error reply when called at `JAtZV3`** (module docstring). -/
theorem JAtZV3.replyFailJ3 (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ)
    {ct : U64} (hcur : σ.curThread = ct.bv) (is_call : Bool) (e : error.SysError) (e' : Fl4Spec.SyscallError)
    (he : ErrRel (.Sys e) e') :
    ((if is_call then do
        let s2 ← syscall.reply_error st s ct e
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a)
      else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s, a)) :
      Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ res =>
      res.1 = .Ok () ∧ ∃ z ∈ ((Fl4Spec.NonDet.when is_call <|
        Fl4Spec.fl4ReplyFromKernelError true ct.bv (Fl4Spec.msgFromSyscallError e')) σ).1,
        JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D res.2.1 res.2.2 z.2 ⦄ := by
  cases is_call
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨trivial, ((), σ), ?_, J⟩
    rw [Endp.nd_when_false (by simp)]; exact Set.mem_singleton _
  simp only [↓reduceIte]
  refine WP.spec_bind (J.replyErrJ3 hcur e e' he) ?_
  rintro s2 ⟨z, hz, J2⟩
  refine (WP.spec_ok _).2 ⟨rfl, z, ?_, J2⟩
  unfold Fl4Spec.NonDet.when; simp only [↓reduceIte]; exact hz

end

end

end Fl4Proofs.P3
