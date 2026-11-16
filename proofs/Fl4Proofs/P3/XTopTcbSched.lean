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

end

end Fl4Proofs.P3
