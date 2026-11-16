/-
P3 (DESIGN.md §9), TCB invocations: **the scheduler-only TCB labels at
`XTop`** (TcbXRest's leaves done with the CSpace machinery).

* `tcb_set_mcpX`: SetMCPriority: ScTcb's decode correspondence
  (`tcb_set_mcp_refines`) with the restart (`XTopAt.restart'`), FL4's `MCP`
  word (`XTopAt.tcbWr`) and the spec's `set_mcpriority` (`TcbBufStep`,
  `XTopAt.bufSpec`): no relation reads the `MCP`.
-/
import Fl4Proofs.P3.XTopTcbAll
import Fl4Proofs.P3.ScTcb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **TcbXRest's SetMCPriority at `XTop`**: beyond `tcb_set_mcp_refines`'
premises (`McpRel` for the authority's MCP [J], the authority among its
TCBs [J]), `XTopAt` at the typed heap, the caller runnable [J], `DelInv`
[J], the target among the sets' TCBs [J]. -/
theorem tcb_set_mcpX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ) (hDI : DelInv Z.th (L.mem s))
    (p : U64) (hp : Z.th p = some .tcb) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetMCPriority)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    {T : Set U64} (hM : McpRel T (L.mem s) σ) (hcapT : ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ T)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSetMCPriority p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetMcpriority (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_mcp_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_priority tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length ≤ 0 := ((hXc.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetMcpriority
    rw [whenE_pos (Or.inr (by omega))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hXc.get hx0' h0
  have hexl : excaps.length ≠ 0 := by
    have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega
  by_cases h1 : length >= 1#u64
  swap
  · simp only [h0, ↓reduceIte, if_neg h1, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetMcpriority
    rw [whenE_pos (Or.inl (show (args.map UScalar.bv).length = 0 by rw [List.length_map, ← hlen]; scalar_tac))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 0#u64 y0 (by simp))
  simp only [h0, ↓reduceIte, if_pos h1, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, harg]
  by_cases hth : ∃ q, capV (L.mem s) x0 = .Thread q
  · obtain ⟨q, hq⟩ := hth
    rw [thread_arg_thread s 1#u64 hq]
    simp only [bind_ok, check_prio_eq]
    obtain ⟨xq, hkq, hmq⟩ := hM q (hcapT q hq)
    have hu : (Fl4Spec.ucast 64 xq.tcbMcpriority) = (L.mem s (mcpA q)).bv := by
      apply BitVec.eq_of_toNat_eq; simp [Fl4Spec.ucast, hmq]
      have := xq.tcbMcpriority.isLt; omega
    have hspec1 : (Fl4Spec.decodeSetMcpriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
        excaps).run σ = (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
          (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) >>= fun _ =>
          (Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none
            (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none none) : Fl4Spec.SEMonad Unit _)).run σ := by
      have he1' : e.1 = .threadCap q.bv := by rw [he1, hq]; rfl
      unfold Fl4Spec.decodeSetMcpriority
      rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1']
      show ((Fl4Spec.NonDetE.returnOk q.bv : Fl4Spec.SEMonad Unit _) >>= _).run σ = _
      rw [retOk_bind]
      have hcp : (Fl4Spec.checkPrio (Z := Unit) (Fl4Spec.the (List.map UScalar.bv (y0 :: rest))[0]?) q.bv).run σ =
          (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
            (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) : Fl4Spec.SEMonad Unit Unit).run σ := by
        unfold Fl4Spec.checkPrio
        rw [lE_bind (Notif.threadGet_eq _ hkq), hu]; rfl
      rw [ExceptT.run_bind, nd_bind_congr hcp, ExceptT.run_bind]; rfl
    by_cases hgt : y0 > L.mem s (mcpA q)
    · rw [ite_eq_left hgt]
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
      apply run_liftME_err
      rw [hspec1, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hgt)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 _) :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · rw [ite_eq_right hgt]
      simp only [bind_ok]
      obtain ⟨s1, σ1, hrc, hsts, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
      have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
        rw [← hcur]; exact hst1
      obtain ⟨hX1, -, -⟩ := hX.restart' hC hcur hsts hst1'
      rw [hrc]; simp only [bind_ok, tcs_mcp]
      refine (WP.spec_ok _).2 ?_
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetMcpriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            excaps)).run σ = ({(.ok (.invokeTCB (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none
              (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none none)), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec1, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hgt), retOk_bind]; rfl
      obtain ⟨x, hkx, -⟩ := hDS1.1.1.tcb p hp
      have hX2 := (hX1.tcbWr hpT 3440#u64 (Or.inl rfl) y0).bufSpec (tcbMcpStep_upd hkx (Fl4Spec.ucast 8 y0.bv))
      refine Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], _), ?_, ⟨Z.th, Z.G, Or.inl ⟨rfl, rfl⟩, hX2.rel.1,
        hX2.rel.2.1, hX2.rel.2.2.1, hX2.rel.2.2.2.1, hX2.rel.2.2.2.2.1⟩, ⟨Z, hX2⟩⟩
      rw [invoke_mcp_run hkx]; exact Set.mem_singleton _
  · have hne : ∀ r, absCap (capV (L.mem s) x0) ≠ .threadCap r := fun r h => by
      obtain ⟨q, hq, -⟩ := absCap_thread h; exact hth ⟨q, hq⟩
    rw [thread_arg_other s 1#u64 (fun q h => hth ⟨q, h⟩)]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetMcpriority
    rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1]
    generalize absCap (capV (L.mem s) x0) = cc at hne ⊢
    cases cc
    all_goals first
      | exact absurd rfl (hne _)
      | exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 1) :
          Fl4Spec.SEMonad Unit Fl4Spec.ObjRef)) rfl _


end

/-! ## A register write -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

set_option maxHeartbeats 8000000 in
/-- **`WX` across a register write** of a TCB's saved context (any register
but the badge register, which the notification relation reads): FL4's
register word, the spec's `as_user` (`setReg`); the endpoint relation by
`write_reg_rel`, the rest of `IRel` across the endpoint code's step
(`RelTopI.stableE`, `SchedRel.stableE`), the notification relation by its
frame, then `IRel.xtop`. -/
theorem XTopAt.regWr {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (hK : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hBT : BufTop (L := L) Z.T Z.c s σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (r : Fl4Spec.Register) (hr : r ≠ Fl4Spec.badge_register) (v : U64) :
    ∃ G', WX (L := L) AR Z.th (L.wr s (regA t (regIdx r)) v) a
      (Notif.updK σ t.bv (.tcb (Notif.setReg x r v.bv))) G' := by
  obtain ⟨hIR, hSRT⟩ := hX.irelK hK hBT
  have hP := hX.fin.1.2
  have hPe := hP.ep
  have hSch := hX.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hSch.lists
  have hT := hc.tcbs
  have hta := hT t ht
  obtain ⟨hR1, hW1, hS1⟩ := write_reg_rel hPe s σ hX.fin.1.1.2.1 ht hk r v
  have hSRT' : SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c)
      (L.wr s (regA t (regIdx r)) v) (Notif.updK σ t.bv (.tcb (Notif.setReg x r v.bv))) :=
    ⟨hSRT.1.stableE hW1 hS1, hSRT.2.1.stableE hPe hSRT.2.2 hW1 hS1, hSRT.2.2.mono hW1.1 (SzKeep.epStep hS1)⟩
  have hwv := regA_val hta (regIdx_lt r)
  have hil := regIdx_lt r
  have hwa : P1.Aligned (regA t (regIdx r)) := by unfold P1.Aligned; rw [hwv]; have := hta.align; omega
  have hw : P1.WritesIn st s (L.wr s (regA t (regIdx r)) v) (· = regA t (regIdx r)) := P1.writesIn_wr hwa
  have hbne : (regA t (regIdx r)).val ≠ (regA t (regIdx Fl4Spec.badge_register)).val := regA_ne hta hr
  have hNt' : Notif.NtfnStateRel Z.N Z.T (L.mem (L.wr s (regA t (regIdx r)) v))
      (Notif.updK σ t.bv (.tcb (Notif.setReg x r v.bv))) := by
    refine hX.fin.1.1.2.2.1.frame hSch.placed (fun b hb hf => hw.mem_eq hb fun e => ?_) ⟨fun q y hq => ?_, fun q y hq => ?_⟩
    · subst e
      rcases hf with ⟨n, hn, h1, h2⟩ | ⟨y, hy, h⟩
      · have := hSch.placed.disj n hn t ht; omega
      · by_cases e : y = t
        · subst e
          have hv := nfootT_val hta h
          have hb0 := regA_val hta (regIdx_lt Fl4Spec.badge_register)
          have hbi : (regIdx Fl4Spec.badge_register).val = 0 := rfl
          omega
        · have hv := nfootT_val (hT y hy) h
          have := tcb_disj hPe ht hy e; omega
    · by_cases e : q = t.bv
      · subst e; rw [hk] at hq; cases hq
      · simp only [Notif.updK, Function.update_of_ne e]; exact hq
    · by_cases e : q = t.bv
      · subst e; rw [hk] at hq; cases hq
        refine ⟨Notif.setReg x r v.bv, by simp [Notif.updK], rfl, ?_, rfl⟩
        unfold Notif.badgeOf
        rw [setReg_regs, Function.update_of_ne (Ne.symm hr)]
      · exact ⟨y, by simp only [Notif.updK, Function.update_of_ne e]; exact hq, rfl, rfl, rfl⟩
  have hIR' := IpcRel.of hNt' hR1 (sched_sc hSRT'.2.1)
  obtain ⟨⟨Z', h1, h2, h3, -, h5, h6, h7, -, hX'⟩, hK', -⟩ := IRel.xtop (L := L) (AR := AR) (a := a) ⟨hIR', hSRT'⟩
    hX.fin.1.1.2.2.2.2.2.2
  refine ⟨Z'.G, Z', h1, rfl, hX', ?_, fun u hu => ?_⟩
  · rw [h2, h3, h5, h6, h7]; exact hK'
  · rw [h3]; exact hTh u hu

end


/-! ## SetTLSBase -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **TcbXRest's SetTLSBase at `XTop`**: `tcb_set_tls_refines`' decode, the
restart, the `TLS_BASE` register by `XTopAt.regWr`, and for the current
thread `reschedule_required` as a scheduler step (`schedStep_resched`, given
`ActReady` at `WX` [J]); the current-thread word outside the objects [P]. -/
theorem tcb_set_tlsX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T)
    (hA : ∀ s a σ G, WX (L := L) AR Z.th s a σ G → Notif.ActReady σ)
    (hBT : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → BufTop (L := L) Z'.T Z'.c s' σ')
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetTLSBase)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSetTLSBase p ⟨length, buf, call, slot, extra⟩ blk
      call don slbl (args.map UScalar.bv) ci sl excaps buffer := by
  have hP := hX.rel.1
  have hCR := hX.rel.2.1
  have htcb := (hX.curTcb hcur).1
  have hdec0 : (specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer) =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetTlsBase (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX tcb.decode
  rw [hstall, hdec0]
  simp only [bind_ok, u64_eq_iff, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val, lbl_tcbSetBreakpoint_val,
    lbl_tcbGetBreakpoint_val, lbl_tcbUnsetBreakpoint_val, lbl_tcbConfigureSingleStepping_val,
    lbl_tcbSetTLSBase_val, lbl_tcbSetEPTRoot_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  refine let_pair_spec s ar (fun s1 => tcb.decode_set_tls_base st s1 p ⟨length, buf, call, slot, extra⟩) _ ?_
  unfold tcb.decode_set_tls_base
  by_cases h1 : length < 1#u64
  · simp only [if_pos h1, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 ?_
    apply Or.inl
    refine ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩
    apply run_liftME_err
    unfold Fl4Spec.decodeSetTlsBase
    rw [whenE_pos (show (args.map UScalar.bv).length = 0 by rw [List.length_map, ← hlen]; scalar_tac)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [if_neg h1]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
      (Fl4Spec.decodeSetTlsBase (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv))).run σ =
      ({(.ok (.invokeTCB (.setTLSBase p.bv y0.bv)), σ)}, False) := by
    apply run_liftME_ok
    unfold Fl4Spec.decodeSetTlsBase
    rw [whenE_neg (by simp), retOk_bind]
    show (Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.setTLSBase p.bv (Fl4Spec.ucast 64 y0.bv)) :
      Fl4Spec.SEMonad Unit _).run σ = _
    rw [ucast64_self]; rfl
  rw [harg]; simp only [bind_ok]
  unfold tcb.restart_caller; rw [hct]; simp only [bind_ok]
  obtain ⟨s1, hs1, hS1, hc1⟩ := spec_exists (WP.spec_and
    (set_thread_state_slots Z.th hP s ct sched.TS_RESTART htcb hact) (set_thread_state_cases s ct sched.TS_RESTART))
  rw [hs1]; simp only [bind_ok]
  obtain ⟨w, hw, hwb⟩ := sanitise_tls y0
  rw [hw]; simp only [bind_ok, set_reg_tls_eq]
  -- the current thread is unchanged
  have hctv : L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct := by
    have := cur_thread_spec' (L := L) s; rw [hct, WP.spec_ok] at this; exact this.symm
  have hpf := hP.fits p _ hp
  have hcf := hP.fits ct _ htcb
  have hpa := hP.align p _ hp
  have hca := hP.align ct _ htcb
  simp only [objSize] at hpf hcf
  have hstv : (stA ct).val = ct.val + 3328 := by
    rw [stA_eq, wordOf_val (by simp; omega)]; simp
  have hcs2 : sched.cur_thread st (L.wr s1 (tlsA p) w) = ok ct := by
    rw [cur_thread_eq]
    simp only [P1.nodeAt_wr, L.cpu_wr]
    have hcwA : P1.Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) := hcw.1
    have hn1 : L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD = L.nodeAt s (L.cpu s) layout.node.CUR_THREAD := by
      rcases hc1 with rfl | rfl <;> simp
    rw [hn1, L.mem_wr_ne (by unfold P1.Aligned; rw [tlsA_val (by omega)]; omega) hcwA
      (fun e => out_ne hcw hp (w := tlsA p) (by rw [tlsA_val (by omega)]; omega) e)]
    rcases hc1 with rfl | rfl
    · rw [L.mem_wr_ne (by unfold P1.Aligned; rw [hstv]; omega) hcwA
        (fun e => out_ne hcw htcb (by rw [hstv]; omega) e), hctv]
    · rw [L.mem_wr_ne hact.1 hcwA (fun e => cur_ne_action s e.symm),
        L.mem_wr_ne (by unfold P1.Aligned; rw [hstv]; omega) hcwA
        (fun e => out_ne hcw htcb (by rw [hstv]; omega) e), hctv]
  rw [hcs2]; simp only [bind_ok, obj.Tcb.Insts.CoreCmpPartialEqTcb.eq]
  -- the spec: restart, then the target's TCB
  obtain ⟨hR, hV, hM, hC0, hI⟩ := hCR
  obtain ⟨tcb, hkt, -⟩ := hR.tcb ct htcb
  obtain ⟨σ1, hst1, hR1, -, -, -, -, -⟩ := restart_rel hR hV hM hC0 hS1 (t := ct.bv) hkt .restart
  have hcur1 : σ1.curThread = ct.bv := by rw [setThreadState_curThread hkt hst1, hcur]
  obtain ⟨hX1, hk1, -⟩ := hX.restart' hC hcur hs1 hst1
  obtain ⟨x, hkx, -⟩ := hR1.tcb p hp
  have htl : tlsA p = regA p (regIdx Fl4Spec.tlsBaseRegister) := by
    unfold tlsA regA layout.tcb.REGS; rfl
  obtain ⟨G2, Z2, hth2, -, hX2, hK2, hTh2⟩ := hX1.regWr (by rw [hk1]; exact hKA) hTh (hBT Z _ _ _ rfl hX1)
    (hTh p hp) hkx
    Fl4Spec.tlsBaseRegister (by decide) w
  rw [← htl] at hX2 hK2
  by_cases hpc : p = ct
  · subst hpc
    simp only [decide_true, ↓reduceIte]
    have hA2 := hA _ _ _ _ ⟨Z2, hth2, rfl, hX2, hK2, hTh2⟩
    obtain ⟨σ', hres, hK', hdl', hds'⟩ := rescheduleRequired_k hA2
    have hS := hX2.fin.1.1.1
    have hN := hX2.fin.1.1.2.2.1
    obtain ⟨s3, hrun3, ⟨σ3, he3, -, -, -, -⟩, hw⟩ := spec_exists (WP.spec_and
      (Sched.reschedule_required_refines _ _ hN hS hA2) (Sched.reschedule_required_sfootI hS))
    rw [hrun3]; simp only [bind_ok]
    rw [hres] at he3
    have e3 : σ3 = σ' := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he3))).2.symm
    subst σ3
    have hX3 := hX2.schedStep hK2 (hth2 ▸ hTh2) (schedStep_resched hA2 hrun3 hres hK' hdl' hds')
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, by rw [hcur]; exact hst1, (.ok [], σ'), ?_,
      ⟨Z2.th, Z2.G, Or.inl ⟨rfl, rfl⟩, hX3.rel.1, hX3.rel.2.1, hX3.rel.2.2.1, hX3.rel.2.2.2.1,
        hX3.rel.2.2.2.2.1⟩, ⟨Z2, hX3⟩⟩)
    refine invoke_tls_mem (y := ((), σ')) hkx y0.bv ?_ blk call don
    rw [← hwb, hcur1]
    simp only [Fl4Spec.NonDet.when, if_pos trivial]
    rw [hres]; rfl
  · have hne : decide (p = ct) = false := by simp [hpc]
    rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, by rw [hcur]; exact hst1, (.ok [], _), ?_,
      ⟨Z2.th, Z2.G, Or.inl ⟨rfl, rfl⟩, hX2.rel.1, hX2.rel.2.1, hX2.rel.2.2.1, hX2.rel.2.2.2.1,
        hX2.rel.2.2.2.2.1⟩, ⟨Z2, hX2⟩⟩)
    refine invoke_tls_mem (y := ((), Notif.updK σ1 p.bv (.tcb (Notif.setReg x Fl4Spec.tlsBaseRegister w.bv))))
      hkx y0.bv ?_ blk call don
    have : ¬ p.bv = σ1.curThread := fun e => hpc (UScalar.eq_of_val_eq (by
      rw [hcur1] at e; have := congrArg BitVec.toNat e; simpa using this))
    rw [← hwb]
    simp only [Fl4Spec.NonDet.when, if_neg this]
    exact Set.mem_singleton _

end


/-! ## UnsetBreakpoint -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The TCB word of debug register `i`. -/
def dbgA (t i : U64) : U64 :=
  core.num.U64.wrapping_add (core.num.U64.wrapping_add t layout.tcb.DEBUG) (core.num.U64.wrapping_mul i 8#u64)

theorem dbgA_val {t i : U64} (ht : t.val + 4096 ≤ 2 ^ 64) (hi : i.val < 8) : (dbgA t i).val = t.val + 448 + 8 * i.val := by
  unfold dbgA layout.tcb.DEBUG
  simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
  simp [U64.size, U64.numBits]
  omega

theorem set_debug_reg_wr (s : S) (t i v : U64) : obj.Tcb.set_debug_reg st t s i v = ok (L.wr s (dbgA t i) v) := by
  unfold obj.Tcb.set_debug_reg
  simp [lift, L.write_eq, dbgA]

/-- **FL4's `unset_breakpoint`**: the `DR7` word, then the breakpoint's
address word. -/
theorem unset_bp_wr (s : S) (t bp : U64) (hbp : bp.val < 4) :
    debug.unset_breakpoint st s t bp ⦃ s2 => ∃ v, s2 = L.wr (L.wr s (dbgA t 5#u64) v) (dbgA t bp) 0#u64 ⦄ := by
  unfold debug.unset_breakpoint debug.set_dr7
  simp only [set_debug_reg_wr, debug.DR7]
  unfold debug.dr7 obj.Tcb.debug_reg debug.enable_bit debug.size_shift debug.type_shift
  step*

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **TcbXRest's UnsetBreakpoint at `XTop`**: `tcb_unset_bp_refines`' decode
(the argument by `ArgRel` [J]), the restart, the two debug-register words
(`DR7`, the breakpoint's; offsets 448..504, read by no relation:
`XTopAt.tcbWrA`); the spec keeps its state (the debug registers are not in
the model). -/
theorem tcb_unset_bpX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ) (hDI : DelInv Z.th (L.mem s))
    (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .unsetBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 1)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBUnsetBreakpoint p ⟨length, buf, call, slot, extra⟩
      blk call don slbl args ci sl excaps buffer := by
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKX
  rw [decode_unset_eq arI s ar p _ hstall, hdec0]
  obtain ⟨bp, hbp, hbs⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 0#u64 (by decide)
  rw [hbp]; simp only [bind_ok]; rw [check_bp_eq]
  simp only [bind_ok]
  have hsp : (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv).run σ =
      (Fl4Spec.fl4CheckBpNum (Z := Unit) bp.bv >>= fun _ =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TcbInvocation.unsetBreakpoint p.bv bp.bv)).run σ := by
    unfold Fl4Spec.decodeFl4UnsetBreakpoint
    exact run_bind_ok hbs _
  by_cases hb : bp ≥ 4#u64
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, bp_err⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    rw [hsp]
    exact run_bind_error (by rw [checkBp_run, if_pos hb]) _
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, -, -, -⟩ := restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
    have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
      rw [← hcur]; exact hst1
    obtain ⟨hX1, -, -⟩ := hX.restart' hC hcur hs1 hst1'
    rw [hrc1]; simp only [bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv)).run σ =
        ({(.ok (.invokeFl4TCB (.unsetBreakpoint p.bv bp.bv)), σ)}, False) := by
      apply run_liftME_ok
      rw [hsp, run_bind_ok (by rw [checkBp_run, if_neg hb])]
      rfl
    have hbpv : bp.val < 4 := by
      have : ¬ (4 ≤ bp.val) := fun h => hb (by scalar_tac)
      omega
    obtain ⟨Q, R0, hc, -⟩ := hX1.fin.1.1.1.lists
    have hpf := (hc.tcbs p hpT).fits
    refine WP.spec_bind (unset_bp_wr s1 p bp hbpv) ?_
    rintro s2 ⟨v, rfl⟩
    have hX2 := (hX1.tcbWrA hpT (dbgA p 5#u64) (448 + 40) (by omega) (by rw [dbgA_val (by omega) (by decide)]; simp)
      v).tcbWrA hpT (dbgA p bp) (448 + 8 * bp.val) (by omega) (by rw [dbgA_val (i := bp) (by omega) (by omega)]; omega) 0#u64
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ1), rfl,
      ⟨Z.th, Z.G, Or.inl ⟨rfl, rfl⟩, hX2.rel.1, hX2.rel.2.1, hX2.rel.2.2.1, hX2.rel.2.2.2.1,
        hX2.rel.2.2.2.2.1⟩, ⟨Z, hX2⟩⟩)

end


/-! ## Suspend and Resume: the decode, the invocation a leaf -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The Suspend leaf at `XTop`** (for the IPC/Sc side): from `XTop`, the
caller's restart then `sched::suspend` of the target, against the spec's
`suspend` from `σ1` (the state after the spec's restart). -/
def SuspendXLeaf (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ σ1 : Fl4Spec.State Unit) (p : U64) : Prop :=
  XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← tcb.restart_caller st s
      let (s2, a2) ← sched.suspend st arI s1 ar p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a2))
    (Fl4Spec.suspend (Z := Unit) p.bv σ1)

/-- **The Resume leaf at `XTop`**: the caller's restart then
`sched::restart` of the target, against the spec's `restart`. -/
def ResumeXLeaf (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ σ1 : Fl4Spec.State Unit) (p : U64) : Prop :=
  XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← tcb.restart_caller st s
      let (s2, a2) ← sched.restart st arI s1 ar p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a2))
    (Fl4Spec.restart (Z := Unit) p.bv σ1)

theorem decode_suspend_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBSuspend p c = (do
      let s1 ← tcb.restart_caller st s
      let (s2, a2) ← sched.suspend st arI s1 ar p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a2)) := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val,
    lbl_tcbCopyRegisters_val, lbl_tcbSuspend_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

theorem decode_resume_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBResume p c = (do
      let s1 ← tcb.restart_caller st s
      let (s2, a2) ← sched.restart st arI s1 ar p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a2)) := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val,
    lbl_tcbCopyRegisters_val, lbl_tcbSuspend_val, lbl_tcbResume_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

/-- A leaf's outcome is a `TopPostDMX` outcome of a decode with one outcome,
whose invocation's run is the leaf's spec with an empty result. -/
theorem topX_of_leaf {AR : A → Fl4Spec.Cr3 → Prop} {σ σ1 : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {inv : Fl4Spec.Fl4Invocation} {s : S}
    {spec : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hdec : m.run σ = ({(.ok inv, σ)}, False))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hrun : ∀ z ∈ spec.1, ((.ok [], z.2) : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1)
    {res : core.result.Result Unit error.Exc × S × A}
    (h : res.1 = .Ok () ∧ ∃ z ∈ spec.1, RelTopM (L := L) res.2.1 z.2 ∧ XTop (L := L) AR res.2.1 res.2.2 z.2) :
    TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don m s res := by
  obtain ⟨hr, z, hz, ⟨th', G', hPl, hCR, hFI, hD, hMO⟩, hX⟩ := h
  exact Or.inr ⟨inv, DecOut.of_eq hdec, σ1, hst, (.ok [], z.2), hrun z hz,
    ⟨th', G', Or.inl ⟨hr, rfl⟩, hPl, hCR, hFI, hD, hMO⟩, hX⟩

/-- **TcbXRest's Suspend at `XTop`**, from the leaf (`SuspendXLeaf`, the
IPC/Sc side's). -/
theorem tcb_suspendX {AR : A → Fl4Spec.Cr3 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX0 : XTop (L := L) AR s ar σ) (p : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSuspend)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (c : tcb.Ctx) (blk call don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hL : ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      SuspendXLeaf (L := L) arI AR s ar σ σ1 p) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSuspend p c blk call don slbl args ci sl excaps
      buffer := by
  have hdec : (specDec false slbl args ci sl (.Thread p) excaps buffer).run σ =
      ({(.ok (.invokeTCB (.suspend p.bv)), σ)}, False) := by
    show (Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer).run σ = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    apply run_liftME_ok
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]; rfl
  obtain ⟨σ1, hst⟩ := hX0.restart
  unfold TcbOKX
  rw [decode_suspend_eq arI s ar p c hstall]
  refine WP.spec_mono (hL σ1 hst hX0) fun res h => topX_of_leaf hdec hst (fun z hz => ?_) h
  show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
  exact mem_liftE (x := ([], z.2)) (mem_bind_nd hz rfl)

/-- **TcbXRest's Resume at `XTop`**, from the leaf (`ResumeXLeaf`). -/
theorem tcb_resumeX {AR : A → Fl4Spec.Cr3 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX0 : XTop (L := L) AR s ar σ) (p : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbResume)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (c : tcb.Ctx) (blk call don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hL : ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      ResumeXLeaf (L := L) arI AR s ar σ σ1 p) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBResume p c blk call don slbl args ci sl excaps
      buffer := by
  have hdec : (specDec false slbl args ci sl (.Thread p) excaps buffer).run σ =
      ({(.ok (.invokeTCB (.resume p.bv)), σ)}, False) := by
    show (Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer).run σ = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    apply run_liftME_ok
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]; rfl
  obtain ⟨σ1, hst⟩ := hX0.restart
  unfold TcbOKX
  rw [decode_resume_eq arI s ar p c hstall]
  refine WP.spec_mono (hL σ1 hst hX0) fun res h => topX_of_leaf hdec hst (fun z hz => ?_) h
  show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
  exact mem_liftE (x := ([], z.2)) (mem_bind_nd hz rfl)

end


/-! ## UnbindNotification: the decode, the invocation a leaf -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The UnbindNotification leaf at `XTop`** (for the IPC side): from
`XTop`, the caller's restart then `unbind_notification` of the target,
against the spec's `unbind_notification` from `σ1`. -/
def UnbindXLeaf (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ σ1 : Fl4Spec.State Unit) (p : U64) : Prop :=
  XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← tcb.restart_caller st s
      let s2 ← notification.unbind_notification st s1 p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, ar))
    (Fl4Spec.unbindNotification (Z := Unit) p.bv σ1)

/-- **TcbXRest's UnbindNotification at `XTop`**: the bound-notification check
on both sides (the TCB word against the spec's `tcb_bound_notification`, by
the endpoint relation), then the leaf (`UnbindXLeaf`, the IPC side's) when a
notification is bound. -/
theorem tcb_unbind_ntfnX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbUnbindNotification)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (length buf : U64) (call : Bool) (slot : obj.Slot)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hL : L.mem s (P1.boundA p) ≠ 0#u64 → ∀ σ1,
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      UnbindXLeaf (L := L) AR s ar σ σ1 p) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBUnbindNotification p
      ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl excaps buffer := by
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX tcb.decode
  rw [hstall, hdec0]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  show (do
    let i ← obj.Tcb.bound_ntfn st p s
    if (i : U64).val = (0#u64).val then do
        let r ← error.illegal Unit
        ok (r, s, ar)
      else do
        let s2 ← tcb.restart_caller st s
        let s3 ← notification.unbind_notification st s2 p
        ok (core.result.Result.Ok (), s3, ar)) ⦃ r => TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeUnbindNotification (Z := Unit) (Fl4Spec.Cap.threadCap p.bv))) s r ⦄
  rw [tcb_bound_eq]
  simp only [bind_ok, ← u64_eq_iff]
  obtain ⟨xp, hkp, hxp⟩ := hX.fin.1.1.2.1.tcb p hpT
  have hbp : xp.tcbBoundNotification = Notif.optRef (L.mem s (P1.boundA p)) := hxp.bound
  have hsp0 : (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv)).run σ =
      ((match Notif.optRef (L.mem s (P1.boundA p)) with
        | none => Fl4Spec.NonDetE.throwError .illegalOperation
        | some _ => Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit) >>= fun _ =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.notificationControl p.bv none)).run σ := by
    simp only [Fl4Spec.decodeUnbindNotification]
    rw [lE_bind (m := Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbBoundNotification p.bv)
      (Notif.threadGet_eq _ hkp), hbp]
    generalize Notif.optRef (L.mem s (P1.boundA p)) = o
    cases o <;> rfl
  by_cases hb0 : L.mem s (P1.boundA p) = 0#u64
  · simp only [hb0, ↓reduceIte, error.illegal, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    exact run_throw_bind _ _ _
  simp only [hb0, ↓reduceIte]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
      (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv))).run σ =
      ({(.ok (.invokeTCB (.notificationControl p.bv none)), σ)}, False) := by
    apply run_liftME_ok
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    exact (congrArg (fun m : Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation => m.run σ) (retOk_bind () _)).trans rfl
  obtain ⟨σ1, hst⟩ := XTop.restart (L := L) (AR := AR) ⟨Z, hX⟩
  refine WP.spec_mono (hL hb0 σ1 hst ⟨Z, hX⟩) fun res h => topX_of_leaf hdec hst (fun z hz => ?_) h
  show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
  exact mem_liftE (x := ([], z.2)) (mem_bind_nd hz rfl)

end


/-! ## SetPriority: the decode, the invocation a leaf -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The SetPriority leaf at `XTop`** (for the IPC/Sc side): from `XTop`,
the caller's restart then `sched::set_priority` of the target to `v`,
against the spec's `set_priority` (to `v`'s byte) from `σ1`. -/
def SetPrioXLeaf (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ σ1 : Fl4Spec.State Unit) (p v : U64) : Prop :=
  XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← tcb.restart_caller st s
      let s2 ← sched.set_priority st s1 p v
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, ar))
    (Fl4Spec.setPriority (Z := Unit) p.bv (Fl4Spec.ucast 8 v.bv) σ1)

set_option maxHeartbeats 4000000 in
/-- **TcbXRest's SetPriority at `XTop`**: ScTcb's decode correspondence
(`tcb_set_prio_refines`; `McpRel` [J], the authority among its TCBs [J]),
then the leaf (`SetPrioXLeaf`, the IPC/Sc side's: the queues reordered). -/
theorem tcb_set_prioX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hDI : DelInv Z.th (L.mem s))
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetPriority)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    {T : Set U64} (hM : McpRel T (L.mem s) σ) (hcapT : ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ T)
    (hL : ∀ σ1 (v : U64), Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      v.val < 256 → SetPrioXLeaf (L := L) AR s ar σ σ1 p v)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSetPriority p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetPriority (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_prio_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_priority tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length ≤ 0 := ((hXc.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_pos (Or.inr (by omega))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hXc.get hx0' h0
  have hexl : excaps.length ≠ 0 := by
    have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega
  by_cases h1 : length >= 1#u64
  swap
  · simp only [h0, ↓reduceIte, if_neg h1, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_pos (Or.inl (show (args.map UScalar.bv).length = 0 by rw [List.length_map, ← hlen]; scalar_tac))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 0#u64 y0 (by simp))
  simp only [h0, ↓reduceIte, if_pos h1, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, harg]
  by_cases hth : ∃ q, capV (L.mem s) x0 = .Thread q
  · obtain ⟨q, hq⟩ := hth
    rw [thread_arg_thread s 1#u64 hq]
    simp only [bind_ok, check_prio_eq]
    obtain ⟨xq, hkq, hmq⟩ := hM q (hcapT q hq)
    have hu : (Fl4Spec.ucast 64 xq.tcbMcpriority) = (L.mem s (mcpA q)).bv := by
      apply BitVec.eq_of_toNat_eq; simp [Fl4Spec.ucast, hmq]
      have := xq.tcbMcpriority.isLt; omega
    have hspec1 : (Fl4Spec.decodeSetPriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
        excaps).run σ = (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
          (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) >>= fun _ =>
          (Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none none
            (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none) : Fl4Spec.SEMonad Unit _)).run σ := by
      have he1' : e.1 = .threadCap q.bv := by rw [he1, hq]; rfl
      unfold Fl4Spec.decodeSetPriority
      rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1']
      show ((Fl4Spec.NonDetE.returnOk q.bv : Fl4Spec.SEMonad Unit _) >>= _).run σ = _
      rw [retOk_bind]
      have hcp : (Fl4Spec.checkPrio (Z := Unit) (Fl4Spec.the (List.map UScalar.bv (y0 :: rest))[0]?) q.bv).run σ =
          (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
            (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) : Fl4Spec.SEMonad Unit Unit).run σ := by
        unfold Fl4Spec.checkPrio
        rw [lE_bind (Notif.threadGet_eq _ hkq), hu]; rfl
      rw [ExceptT.run_bind, nd_bind_congr hcp, ExceptT.run_bind]; rfl
    by_cases hgt : y0 > L.mem s (mcpA q)
    · rw [ite_eq_left hgt]
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
      apply run_liftME_err
      rw [hspec1, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hgt)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 _) :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · rw [ite_eq_right hgt]
      simp only [bind_ok]
      obtain ⟨s1, σ1, hrc, -, hst1, -, -, -, -, -⟩ := restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
      have hlt : y0.val < 256 := by
        have := xq.tcbMcpriority.isLt
        have h2 : ¬ (L.mem s (mcpA q)).val < y0.val := hgt
        omega
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetPriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            excaps)).run σ = ({(.ok (.invokeTCB (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none none
              (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none)), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec1, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hgt), retOk_bind]; rfl
      have hl := hL σ1 y0 hst1 hlt ⟨Z, hX⟩
      unfold SetPrioXLeaf at hl
      rw [hrc] at hl; simp only [bind_ok] at hl
      rw [hrc]; simp only [bind_ok, tcs_prio]
      exact WP.spec_mono hl fun res h => topX_of_leaf hdec hst1 (fun z hz => invoke_prio_mem ssl _ q.bv blk call don hz) h
  · have hne : ∀ r, absCap (capV (L.mem s) x0) ≠ .threadCap r := fun r h => by
      obtain ⟨q, hq, -⟩ := absCap_thread h; exact hth ⟨q, hq⟩
    rw [thread_arg_other s 1#u64 (fun q h => hth ⟨q, h⟩)]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1]
    generalize absCap (capV (L.mem s) x0) = cc at hne ⊢
    cases cc
    all_goals first
      | exact absurd rfl (hne _)
      | exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 1) :
          Fl4Spec.SEMonad Unit Fl4Spec.ObjRef)) rfl _


end


/-! ## Write/CopyRegisters: the decode, the register work a leaf -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The WriteRegisters leaf at `XTop`** (for the IPC/Sc side): after the
caller's restart, at `XTop`, FL4's `write_registers` against the spec's
`invoke_tcb WriteRegisters` (from the state after the spec's restart),
with an empty result and `XTop` after. -/
def WriteRegsXHyp (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (σ : Fl4Spec.State Unit) (ct p buf : U64) (args : List U64)
    (blk call don : Bool) : Prop :=
  ∀ s1 σ1 (flags n : U64) (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) → n.val ≤ args.length - 2 →
    XTop (L := L) AR s1 a σ1 →
    tcb.write_registers st arI s1 a p ((flags &&& 1#u64) != 0#u64) n buf ⦃ r =>
      ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.writeRegisters p.bv
          (Fl4Spec.testBit flags.bv 0) (((args.drop 2).map UScalar.bv).take n.val)
          Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1,
        y.1 = .ok [] ∧ RelTopM (L := L) r.1 y.2 ∧ XTop (L := L) AR r.1 r.2 y.2 ⦄

/-- **The CopyRegisters leaf at `XTop`**: after the caller's restart, at
`XTop`, FL4's `copy_registers` (source `src`, a thread cap's in a slot)
against the spec's `invoke_tcb CopyRegisters`. -/
def CopyRegsXHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (ct p : U64)
    (blk call don : Bool) : Prop :=
  ∀ s1 σ1 (src flags : U64) (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    (∃ x, IsSlot th x ∧ capV (L.mem s) x = .Thread src) → XTop (L := L) AR s1 a σ1 →
    tcb.copy_registers st arI s1 a p src flags ⦃ r => r.1 = .Ok () ∧
      ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.copyRegisters p.bv src.bv
          (Fl4Spec.testBit flags.bv 0) (Fl4Spec.testBit flags.bv 1) (Fl4Spec.testBit flags.bv 2)
          (Fl4Spec.testBit flags.bv 3) Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1,
        y.1 = .ok [] ∧ RelTopM (L := L) r.2.1 y.2 ∧ XTop (L := L) AR r.2.1 r.2.2 y.2 ⦄

set_option maxHeartbeats 4000000 in
/-- **TcbXRest's WriteRegisters at `XTop`**: TcbCtl's decode
(`tcb_write_regs_refines`), the restart, then the leaf (`WriteRegsXHyp`). -/
theorem tcb_write_regsX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hC0 : CurRun σ)
    (hDI : DelInv Z.th (L.mem s)) (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbWriteRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (hW : WriteRegsXHyp (L := L) arI AR s σ ct p buf args blk call don) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBWriteRegisters p ⟨length, buf, call, slot, extra⟩ blk call don slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeWriteRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_write_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_write_registers
  by_cases h1 : length < 2#u64
  · simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    have : args.length < 2 := by scalar_tac
    match args, this with
    | [], _ => rfl
    | [_], _ => rfl
  simp only [h1, ↓reduceIte]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
    | [_], h => exfalso; simp only [List.length_singleton] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  obtain ⟨i, hi, hiv⟩ := spec_exists (U64.sub_spec (x := length) (y := 2#u64) (by scalar_tac))
  have hrl : rest.length = length.val - 2 := by simp at hlen; scalar_tac
  have hiv' : i.val = length.val - 2 := by rw [hiv.1]; rfl
  have hl2 : 2 ≤ length.val := by have : ¬ length.val < (2#u64 : U64).val := h1; exact Nat.le_of_not_lt this
  rw [ha0, ha1]; simp only [bind_ok, hi]
  have hsp : (Fl4Spec.decodeWriteRegisters (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv)) =
      (Fl4Spec.NonDetE.whenE ((rest.map UScalar.bv).length < Fl4Spec.unat y1.bv)
        (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage) >>= fun _ => do
        let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
        Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation)
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.writeRegisters p.bv (Fl4Spec.testBit y0.bv 0)
          ((rest.map UScalar.bv).take (Fl4Spec.unat y1.bv)) Fl4Spec.ArchDefaultExtraRegisters)) := by
    simp only [Fl4Spec.decodeWriteRegisters, List.map_cons, retOk_bind]
  rw [hsp]
  have hun : Fl4Spec.unat y1.bv = y1.val := by simp [Fl4Spec.unat]
  by_cases hw : i < y1
  · simp only [hw, ↓reduceIte, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    rw [whenE_pos (by rw [hun, List.length_map, hrl]; have h' : i.val < y1.val := hw; omega)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [hw, ↓reduceIte, hct, bind_ok, tcb_eq_ct]
  have hwh : (Fl4Spec.NonDetE.whenE ((rest.map UScalar.bv).length < Fl4Spec.unat y1.bv)
      (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage) : Fl4Spec.SEMonad Unit Unit).run σ = ({(.ok (), σ)}, False) := by
    rw [whenE_neg (by rw [hun, List.length_map, hrl]; have h' : ¬ i.val < y1.val := hw; omega)]; rfl
  by_cases hpc : p = ct
  · subst hpc
    simp only [decide_true, ↓reduceIte, error.illegal, bind_ok]
    refine (WP.spec_ok _).2 ?_
    apply Or.inl
    refine ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩
    apply run_liftME_err
    rw [run_bind_ok hwh, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
      s.curThread) rfl), whenE_pos (by show p.bv = σ.curThread; rw [hcur])]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  · simp only [decide_eq_false hpc, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, -, -, -⟩ := restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
    have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
      rw [← hcur]; exact hst1
    obtain ⟨hX1, -, -⟩ := hX.restart' hC0 hcur hs1 hst1'
    rw [hrc1]; simp only [bind_ok, lift]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.NonDetE.whenE ((rest.map UScalar.bv).length < Fl4Spec.unat y1.bv)
          (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage) >>= fun _ => do
          let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
          Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation)
          Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.writeRegisters p.bv (Fl4Spec.testBit y0.bv 0)
            ((rest.map UScalar.bv).take (Fl4Spec.unat y1.bv)) Fl4Spec.ArchDefaultExtraRegisters))).run σ =
        ({(.ok (.invokeTCB (.writeRegisters p.bv (Fl4Spec.testBit y0.bv 0)
          ((((y0 :: y1 :: rest).drop 2).map UScalar.bv).take y1.val) Fl4Spec.ArchDefaultExtraRegisters)), σ)},
          False) := by
      apply run_liftME_ok
      rw [run_bind_ok hwh, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
        s.curThread) rfl), whenE_neg (by show ¬ p.bv = σ.curThread; rw [hcur, bv_eq_iff']; exact hpc),
        retOk_bind, hun]
      rfl
    refine WP.spec_bind (hW s1 σ1 y0 y1 ar hs1 hst1' (by simp only [List.length_cons]; have h' : ¬ i.val < y1.val := hw; omega) ⟨Z, hX1⟩) ?_
    rintro ⟨s2, a2⟩ ⟨y, hy, hy1, ⟨th', G', hPl, hCR, hFI, hD, hMO⟩, hX2⟩
    exact (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, y, hy, ⟨th', G', Or.inl ⟨rfl, hy1⟩, hPl, hCR, hFI, hD,
      hMO⟩, hX2⟩)


set_option maxHeartbeats 4000000 in
/-- **TcbXRest's CopyRegisters at `XTop`**: TcbCtl's decode
(`tcb_copy_regs_refines`), the restart, then the leaf (`CopyRegsXHyp`). -/
theorem tcb_copy_regsX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hC0 : CurRun σ)
    (hDI : DelInv Z.th (L.mem s)) (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbCopyRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hC : CopyRegsXHyp (L := L) arI AR Z.th s σ ct p blk call don) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBCopyRegisters p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call
      don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeCopyRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) (excaps.map Prod.fst)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_copy_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_copy_registers tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have htr : args = [] ∨ excaps = [] →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeCopyRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) (excaps.map Prod.fst)))
        s res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    rcases h with rfl | rfl
    · exact copy_trunc0 σ _ _
    · cases args with
      | nil => exact copy_trunc0 σ _ _
      | cons y0 rest => exact copy_trunc1 σ _ _ _
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hXc.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact htr (Or.inr (List.eq_nil_of_length_eq_zero (by omega)))
  by_cases hl : length < 1#u64
  · simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, show ¬ (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 1#u64 by
        show ¬ length >= 1#u64; scalar_tac]
    exact htr (Or.inl (List.eq_nil_of_length_eq_zero (by scalar_tac)))
  simp only [h0, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    show (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 1#u64 by show length >= 1#u64; scalar_tac]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args, hlen with
    | y0 :: rest, _ => exact ⟨_, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  rw [ha0]; simp only [bind_ok, thread_arg_eq]
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hXc.get hx0' h0
  obtain ⟨erest, rfl⟩ : ∃ erest, excaps = e0 :: erest := by
    match excaps, he0 with
    | a :: r, h => simp at h; exact ⟨r, by rw [h]⟩
  have hsp : (Fl4Spec.decodeCopyRegisters (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv)
      ((e0 :: erest).map Prod.fst)) =
      ((match absCap (capV (L.mem s) x0) :: erest.map Prod.fst with
        | .threadCap q :: _ => Fl4Spec.NonDetE.returnOk q
        | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef) >>= fun q =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.copyRegisters p.bv q (Fl4Spec.testBit y0.bv 0)
          (Fl4Spec.testBit y0.bv 1) (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3)
          Fl4Spec.ArchDefaultExtraRegisters)) := by
    rw [List.map_cons, List.map_cons, copy_spec, he01]
    rfl
  rw [hsp]
  rcases copy_src_rel (capV (L.mem s) x0) (erest.map Prod.fst) (σ := σ) with ⟨src, hsrc, hrun⟩ | ⟨hsrc, hrun⟩
  · rw [hsrc]
    simp only [hstall' src, bind_ok]
    obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, -, -, -⟩ := restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
    have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
      rw [← hcur]; exact hst1
    obtain ⟨hX1, -, -⟩ := hX.restart' hC0 hcur hs1 hst1'
    refine let_pair2 s ar (fun s1 a1 => do let s2 ← tcb.restart_caller st s1; tcb.copy_registers st arI s2 a1 p src y0)
      _ ?_
    rw [hrc1]; simp only [bind_ok]
    have hthr : capV (L.mem s) x0 = .Thread src := by
      revert hsrc; cases capV (L.mem s) x0 <;> simp [threadArgF]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        ((match absCap (capV (L.mem s) x0) :: erest.map Prod.fst with
          | .threadCap q :: _ => Fl4Spec.NonDetE.returnOk q
          | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef) >>=
          fun q => Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.copyRegisters p.bv q (Fl4Spec.testBit y0.bv 0)
            (Fl4Spec.testBit y0.bv 1) (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3)
            Fl4Spec.ArchDefaultExtraRegisters))).run σ =
        ({(.ok (.invokeTCB (.copyRegisters p.bv src.bv (Fl4Spec.testBit y0.bv 0) (Fl4Spec.testBit y0.bv 1)
          (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3) Fl4Spec.ArchDefaultExtraRegisters)), σ)}, False) := by
      apply run_liftME_ok
      exact (run_bind_ok hrun _).trans rfl
    have hxs : IsSlot Z.th x0 := by rw [hxe0]; exact AbsSlot.isSlot ⟨ps0, hps01, Or.inl hps0⟩
    refine WP.spec_mono (hC s1 σ1 src y0 ar hs1 hst1' ⟨x0, hxs, hthr⟩ ⟨Z, hX1⟩) ?_
    rintro ⟨r2, s2, a2⟩ ⟨hr2, y, hy, hy1, ⟨th', G', hPl, hCR, hFI, hD, hMO⟩, hX2⟩
    simp only at hr2; subst hr2
    exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, y, hy, ⟨th', G', Or.inl ⟨rfl, hy1⟩, hPl, hCR, hFI, hD, hMO⟩, hX2⟩
  · rw [hsrc]
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
    exact run_liftME_err (run_bind_error hrun _)


end

end

end Fl4Proofs.P3
