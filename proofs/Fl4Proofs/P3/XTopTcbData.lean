/-
P3 (DESIGN.md §9), TCB invocations: **the data labels at `XTop`**
(TcbXOpen's labels whose decode replies itself), over the data tail
(XTopReply).

* `css_xtop`: FL4's `configure_single_stepping` keeps `XTop` against the
  spec's `cssState` (the debug words `SS_ENABLED`, `SS_COUNT` by
  `XTopAt.tcbWrA`; with no instruction count, the target's `FLAGS`
  register by `XTopAt.regWr`, the trap flag cleared).
* `tcb_single_stepX`: ConfigureSingleStepping at `XTop`, called or not.
* `tcb_get_bpX`: GetBreakpoint (`MR4` in the caller's IPC buffer, by IpcBuf's
  lookup, `BufWordRel`, `IpcBufCapOK`, `BufCover`, VSpace's `BufPlaced`).
* `FlagsRel` (FL4's flags word against the spec's `tcb_flags`, with
  `FlagsRel.frame`, `FlagsRel.set`), `flags_new` (the new flags word's flags),
  `tcb_set_flagsX`: SetFlags (its FPU release by XTopFpuRel's `XTopAt.fpuReleaseX`, `ARKeep` [P]).
* `TcbXOpen4`, `tcbXOpen_of`: TcbXOpen from the four labels still open.
-/
import Fl4Proofs.P3.XTopReply
import Fl4Proofs.P3.TcbDataX
import Fl4Proofs.P3.XTopFpuRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem eflags_tf_eq : debug.EFLAGS_TF = ok 256#u64 := by unfold debug.EFLAGS_TF; rfl

theorem regIdx_flags : regIdx Fl4Spec.Register.flags = layout.reg.FLAGS := by unfold layout.reg.FLAGS; rfl

set_option maxHeartbeats 4000000 in
/-- **FL4's `configure_single_stepping` keeps `XTop`**, against the spec's
`cssState`. -/
theorem css_xtop {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s1 : S} {a : A} {σ1 : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s1 a σ1) (hK : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s1))
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T)
    (hBT : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → BufWordRel Z'.T (L.mem s') σ')
    (hP0 : IPlaced Z.N Z.T Z.E Z.R Z.B) {p : U64} (hp : Z.th p = some .tcb) {xp : Fl4Spec.Tcb} (hkp : σ1.kheap p.bv = some (.tcb xp)) (bp n : U64) :
    debug.configure_single_stepping st arI s1 a p bp n false ⦃ r => r.1 = false ∧ r.2.2 = a ∧
      L.ksb r.2.1 = L.ksb s1 ∧ L.cpu r.2.1 = L.cpu s1 ∧
      ∃ G', WX (L := L) AR Z.th r.2.1 a (cssState σ1 p.bv xp n.bv) G' ⦄ := by
  have hpT := hTh p hp
  obtain ⟨Q, R0, hc, -⟩ := hX.fin.1.1.1.lists
  have hpf := (hc.tcbs p hpT).fits
  unfold debug.configure_single_stepping
  by_cases hn : n = 0#u64
  · subst hn
    simp only [↓reduceIte, set_debug_reg_wr, bind_ok]
    have hX2 := hX.tcbWrA hpT (dbgA p debug.SS_ENABLED) (448 + 48) (by omega)
      (by rw [dbgA_val (by omega) (by unfold debug.SS_ENABLED; decide)]; unfold debug.SS_ENABLED; simp) 0#u64
    simp only [Std.bind_assoc]
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec _ p layout.reg.FLAGS) ?_
    rintro i rfl
    rw [eflags_tf_eq]; simp only [bind_ok, lift]
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ p layout.reg.FLAGS _) ?_
    rintro s3 rfl
    simp only [set_debug_reg_wr, bind_ok, WP.spec_ok]
    set s2 := L.wr s1 (dbgA p debug.SS_ENABLED) 0#u64
    obtain ⟨x2, hk2, hx2⟩ := hX2.fin.1.1.2.1.tcb p hpT
    rw [hkp] at hk2; cases hk2
    have hK2 : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s2) := by rw [L.ksb_wr]; exact hK
    obtain ⟨G2, Z2, hth2, hG2, hX3, hK3, hTh3⟩ := hX2.regWr hK2 hTh (hBT Z _ _ _ rfl hX2) hP0 hpT hkp
      Fl4Spec.Register.flags (by decide) (L.mem s2 (regA p layout.reg.FLAGS) &&& ~~~256#u64)
    rw [regIdx_flags] at hX3 hK3
    have hpT2 : p ∈ Z2.T := hTh3 p hp
    obtain ⟨Q2, R2, hc2, -⟩ := hX3.fin.1.1.1.lists
    have hX4 := hX3.tcbWrA hpT2 (dbgA p debug.SS_COUNT) (448 + 56) (by omega)
      (by rw [dbgA_val (by omega) (by unfold debug.SS_COUNT; decide)]; unfold debug.SS_COUNT; simp) 0#u64
    have hflag : (L.mem s2 (regA p layout.reg.FLAGS) &&& ~~~256#u64).bv =
        xp.tcbArch.tcbContext.userRegs .flags &&& tfMask := by
      rw [UScalar.bv_and, ← regIdx_flags]
      exact congrArg₂ (· &&& ·) (hx2.regs .flags) (by rfl)
    refine ⟨by first | rfl | trivial, by first | rfl | trivial, by simp [L.ksb_wr, s2], by simp [L.cpu_wr, s2], G2, Z2, hth2, hG2, ?_, ?_, hTh3⟩
    · have e : cssState σ1 p.bv xp (0#u64).bv =
          Notif.updK σ1 p.bv (.tcb (Notif.setReg xp Fl4Spec.Register.flags
            (L.mem s2 (regA p layout.reg.FLAGS) &&& ~~~256#u64).bv)) := by
        unfold cssState; rw [if_pos (show U64.bv 0#u64 = (0 : Fl4Spec.Word) from rfl), hflag]
      rw [e]; exact hX4
    · rw [L.ksb_wr]; exact hK3
  · simp only [hn, ↓reduceIte, set_debug_reg_wr, bind_ok, WP.spec_ok]
    have hX2 := hX.tcbWrA hpT (dbgA p debug.SS_ENABLED) (448 + 48) (by omega)
      (by rw [dbgA_val (by omega) (by unfold debug.SS_ENABLED; decide)]; unfold debug.SS_ENABLED; simp) 1#u64
    have hX3 := hX2.tcbWrA hpT (dbgA p debug.SS_COUNT) (448 + 56) (by omega)
      (by rw [dbgA_val (by omega) (by unfold debug.SS_COUNT; decide)]; unfold debug.SS_COUNT; simp) n
    have e : cssState σ1 p.bv xp n.bv = σ1 := by
      unfold cssState; rw [if_neg (fun h => hn (UScalar.eq_of_val_eq (by
        have := congrArg BitVec.toNat h; simpa using this)))]
    refine ⟨by first | rfl | trivial, by first | rfl | trivial, by simp [L.ksb_wr], by simp [L.cpu_wr], Z.G, ?_⟩
    rw [e]
    exact WX.of hX3 (by simp only [L.ksb_wr]; exact hK) hTh

set_option maxHeartbeats 8000000 in
/-- **TcbXOpen's ConfigureSingleStepping at `XTop`**, called or not: the
arguments (`ArgRel` [J]), the restart, `css_xtop`, then the data tail of
`[0]` (FL4's `consumed` is always false), against the spec's
ConfigureSingleStepping at `cssState`. -/
theorem tcb_single_stepX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDI : DelInv Z.th (L.mem s))
    (hBT : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → BufWordRel Z'.T (L.mem s') σ')
    (hP0 : IPlaced Z.N Z.T Z.E Z.R Z.B) (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .configureSingleStepping)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 2)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKRX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBConfigureSingleStepping p
      ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl excaps buffer ct := by
  have hP := hX.rel.1
  obtain ⟨htcb, xc, hkc⟩ := hX.curTcb hcur
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4ConfigureSingleStepping (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKRX
  rw [decode_step_eq arI s ar p _ hstall, hdec0]
  obtain ⟨bp, hbp, hbs⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 0#u64 (by decide)
  obtain ⟨n, hn, hns⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 1#u64 (by decide)
  unfold tcb.decode_configure_single_stepping
  rw [hct]; simp only [bind_ok]; rw [hbp]; simp only [bind_ok]; rw [hn]; simp only [bind_ok]
  obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, hcu1, hk1, hc1⟩ :=
    restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
  have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
    rw [← hcur]; exact hst1
  obtain ⟨hX1, -, -⟩ := hX.restart' hC hcur hs1 hst1'
  have hσ1 : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { xc with tcbState := .restart })) ct.bv := by
    rw [Notif.setThreadState_eq .restart hkc] at hst1'
    exact ((Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hst1'))).2).symm
  have hkc1 : σ1.kheap ct.bv = some (.tcb { xc with tcbState := .restart }) := by
    rw [hσ1, Notif.stsAct_kheap]; simp [Notif.updK]
  rw [hrc1]; simp only [bind_ok]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
      (Fl4Spec.decodeFl4ConfigureSingleStepping (Z := Unit) buffer p.bv)).run σ =
      ({(.ok (.invokeFl4TCB (.configureSingleStepping p.bv bp.bv n.bv)), σ)}, False) := by
    apply run_liftME_ok
    unfold Fl4Spec.decodeFl4ConfigureSingleStepping
    rw [run_bind_ok (show (Fl4Spec.fl4Arg (Z := Unit) buffer 0).run σ = _ from hbs),
      run_bind_ok (show (Fl4Spec.fl4Arg (Z := Unit) buffer 1).run σ = _ from hns)]
    rfl
  obtain ⟨xp, hkp, -⟩ := hX1.fin.1.1.2.1.tcb p (hTh p hp)
  have hKA1 : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s1) := by rw [hk1]; exact hKA
  refine WP.spec_bind (css_xtop arI hX1 hKA1 hTh hBT hP0 hp hkp bp n) ?_
  rintro ⟨consumed, s2, a2⟩ ⟨hcons, ha2, hks2, hcp2, G2, Z2, hth2, hG2, hX2, -, -⟩
  simp only at hcons ha2 hks2 hcp2
  subst hcons ha2
  obtain ⟨xy, hky, hrsy⟩ := css_tcb hkp hkc1 n.bv
  have hcurY : ct.bv = (cssState σ1 p.bv xp n.bv).curThread := by
    unfold cssState; split <;> (show ct.bv = σ1.curThread; rw [hcu1, hcur])
  have htcb2 : Z2.th ct = some .tcb := by rw [hth2]; exact htcb
  have hact2 : OutsideObjects Z2.th (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) := by
    rw [hth2, hcp2, hc1, Sched.nodeAt_ksb (hks2.trans hk1)]; exact hact
  have hy := css_mem (bp := bp.bv) hkp n.bv
  have hy' : (.ok [0], cssState σ1 p.bv xp n.bv) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
      (.invokeFl4TCB (.configureSingleStepping p.bv bp.bv n.bv))).run σ1).1 := hy
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (nodata_tail_xtop hX2 hcurY hky (by rw [hrsy]) hact2 [0]) ?_
    rintro res ⟨hres, hne, z, hz, hRT, hXT⟩
    exact Or.inr ⟨hres, hne, _, DecOut.of_eq hdec, σ1, hst1, [0], _, hy', z, hz, hRT, hXT⟩
  · simp only [↓reduceIte]
    refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s2 true ct L.total) ?_
    rintro bf -
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hI0 : Vs.RInv (L := L) Z2.th Z2.P Z2.L4 Z2.L3 Z2.L2 Z2.L1 Z2.N Z2.T Z2.C Z2.E Z2.R Z2.B Z2.c AR Z2.G s2 a2
        (MrS (cssState σ1 p.bv xp n.bv) ct.bv xy (Endp.ipcBufOf true xy) []) := by
      rw [MrS_nil hky]; exact hX2.toRInv
    have tail : (do
        let (len, s3) ← msg.set_mr st s2 ct bf 0#u64 0#u64
        let s4 ← tcb.reply_words st s3 ct len
        let s5 ← sched.set_thread_state st s4 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a2)) ⦃ res =>
          TopPostRMX (L := L) (XTop (L := L) AR) σ blk true don (Fl4Spec.NonDetE.liftME
            Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4ConfigureSingleStepping (Z := Unit) buffer p.bv))
            ct s res ⦄ := by
      refine WP.spec_bind (setmr_reg_inv _ ct htcb2 hcurY xy _ bf s2 a2 [] hI0 0#u64 rfl (by decide) 0#u64) ?_
      rintro ⟨len, s3⟩ ⟨hlen, hI3, hk3, hc3⟩
      simp only at hlen hI3 hk3 hc3
      refine WP.spec_mono (data_tail_xtop hX2 hcurY hky (by rw [hrsy]) hact2 hI3 hk3 hc3 (by decide)
        (fun _ _ z hz => by simp [Endp.mrPairs] at hz) len
        (by cases Endp.ipcBufOf true xy <;> simp [mrLen, hlen]) (by simp only [List.length_nil] at hlen; omega)) ?_
      rintro res ⟨hres, hne, z, hz, hRT, hXT⟩
      exact Or.inr ⟨hres, hne, _, DecOut.of_eq hdec, σ1, hst1, [0], _, hy', z, hz, hRT, hXT⟩
    split <;> first | exact tail | (split <;> exact tail)

/-- **The caller's IPC-buffer words lie in its frame** (IpcBuf's
`IpcBufCapOK`, as `epBufMapHyps_top`'s frame). -/
theorem buf_frame_of_ok {σ : Fl4Spec.State Unit} (hO : Endp.IpcBufCapOK σ) {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) {p : Fl4Spec.ObjRef} (hp : Endp.ipcBufOf true x = some p) (k : Nat)
    (hk128 : k < 128) : Fl4Spec.inUserFrame (Endp.bufAddr p k) σ := by
  unfold Endp.ipcBufOf at hp
  split at hp
  · rename_i dev pb R mt vms md he
    split_ifs at hp with hc
    cases hp
    have hro : Fl4Spec.vmReadOnly ⊆ R := by
      rcases hc with h | ⟨h, -⟩
      · exact fun z hz => h (by unfold Fl4Spec.vmReadOnly Fl4Spec.vmReadWrite at *; simp at hz ⊢; simp [hz])
      · exact h
    exact (hO t x hk dev pb R mt vms md he hro).2.2.1 k hk128
  · cases hp

set_option maxHeartbeats 16000000 in
/-- **TcbXOpen's GetBreakpoint at `XTop`**, called or not: the breakpoint
number's check, the restart, the read (`GetBpHyp` [P]: total), then the
data tail of the five words (`MR4` in the caller's IPC buffer: the lookup by
IpcBuf's `lookup_buf_full` with `IpcBufCapOK` [J], the buffer word by
`BufWordRel`, the mapping by `BufCover` [J], the placement `BufPlaced` [J]),
against the spec's GetBreakpoint (any five words). -/
theorem tcb_get_bpX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ) (hDI : DelInv Z.th (L.mem s))
    (hBT : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → BufWordRel Z'.T (L.mem s') σ')
    (hOK : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → Endp.IpcBufCapOK σ')
    (hBC : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → Endp.BufCover Z'.T Z'.B σ')
    (hBPl : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' →
      Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ')
    (p : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .getBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 1) (hG : GetBpHyp (st := st) s ct p)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKRX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBGetBreakpoint p
      ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl excaps buffer ct := by
  have hP := hX.rel.1
  obtain ⟨htcb, xc, hkc⟩ := hX.curTcb hcur
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKRX
  rw [decode_getbp_eq arI s ar p _ hstall, hdec0]
  obtain ⟨bp, hbp, hbs⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 0#u64 (by decide)
  have hsp : (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv).run σ =
      (Fl4Spec.fl4CheckBpNum (Z := Unit) bp.bv >>= fun _ =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TcbInvocation.getBreakpoint p.bv bp.bv)).run σ := by
    unfold Fl4Spec.decodeFl4GetBreakpoint
    exact run_bind_ok hbs _
  unfold tcb.decode_get_breakpoint
  rw [hct]; simp only [bind_ok]; rw [hbp]; simp only [bind_ok]; rw [check_bp_eq]
  by_cases hb : bp ≥ 4#u64
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, bp_err⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    rw [hsp]
    exact run_bind_error (by rw [checkBp_run, if_pos hb]) _
  simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, hcu1, hk1, hc1⟩ :=
    restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
  have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
    rw [← hcur]; exact hst1
  obtain ⟨hX1, -, -⟩ := hX.restart' hC hcur hs1 hst1'
  have hσ1 : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { xc with tcbState := .restart })) ct.bv := by
    rw [Notif.setThreadState_eq .restart hkc] at hst1'
    exact ((Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hst1'))).2).symm
  set xr : Fl4Spec.Tcb := { xc with tcbState := .restart }
  have hkc1 : σ1.kheap ct.bv = some (.tcb xr) := by
    rw [hσ1, Notif.stsAct_kheap]; simp [Notif.updK, xr]
  have hcurY : ct.bv = σ1.curThread := by rw [hcu1, hcur]
  have hact1 : OutsideObjects Z.th (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) := by
    rw [hc1, Sched.nodeAt_ksb hk1]; exact hact
  rw [hrc1]; simp only [bind_ok]
  obtain ⟨r1, hr1⟩ := hG s1 bp hs1
  rw [hr1]; simp only [bind_ok]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
      (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv)).run σ =
      ({(.ok (.invokeFl4TCB (.getBreakpoint p.bv bp.bv)), σ)}, False) := by
    apply run_liftME_ok
    rw [hsp, run_bind_ok (by rw [checkBp_run, if_neg hb])]
    rfl
  have hy : ∀ rr : List Fl4Spec.Data, rr.length = 5 → (.ok rr, σ1) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit)
      blk call don (.invokeFl4TCB (.getBreakpoint p.bv bp.bv))).run σ1).1 :=
    fun rr h => mem_liftE (x := (rr, σ1)) ⟨h, rfl⟩
  refine WP.spec_bind (Pₘ := fun x : core.result.Result Unit error.Exc × S =>
    TopPostRMX (L := L) (XTop (L := L) AR) σ blk call don (Fl4Spec.NonDetE.liftME
      Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv)) ct s
      (x.1, x.2, ar)) ?_ fun x hx => (WP.spec_ok _).2 hx
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (nodata_tail_core hX1 hcurY hkc1 rfl hact1 [0, 0, 0, 0, 0]) ?_
    rintro s2 ⟨hne, z, hz, hRT, hXT⟩
    exact (WP.spec_ok _).2 (Or.inr ⟨rfl, hne, _, DecOut.of_eq hdec, σ1, hst1, _, σ1, hy _ rfl, z, hz, hRT, hXT⟩)
  · simp only [↓reduceIte]
    have hctT : ct ∈ Z.T := (hX1.fin.1.1.2.1.tcb ct (TopSR.cur_mem hX1.fin.1 hcurY)).elim fun _ _ =>
      TopSR.cur_mem hX1.fin.1 hcurY
    have hOK1 := hOK Z s1 ar σ1 rfl hX1
    obtain ⟨x', hk', hwx⟩ := hBT Z s1 ar σ1 rfl hX1 ct hctT
    rw [hkc1] at hk'; cases hk'
    refine WP.spec_bind (lookup_buf_full s1 σ1 hX1.rel.2.1.1 hX1.rel.2.1.2.1 htcb hkc1 hOK1 true) ?_
    rintro bf ⟨hw0, hwp⟩
    have hbm : ∀ q, Endp.ipcBufOf true xr = some q → Endp.BufMap Z.B bf q := fun q hq =>
      hBC Z s1 ar σ1 rfl hX1 ct hctT xr true q hkc1 hq bf (hwp hwx q hq)
    have hI0 : Vs.RInv (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR Z.G s1 ar
        (MrS σ1 ct.bv xr (Endp.ipcBufOf true xr) []) := by
      rw [MrS_nil hkc1]; exact hX1.toRInv
    refine WP.spec_bind (setmr_reg_inv σ1 ct htcb hcurY xr _ bf s1 ar [] hI0 0#u64 rfl (by decide) r1.vaddr) ?_
    rintro ⟨l2, s2⟩ ⟨-, hI2, hk2, hc2⟩
    refine WP.spec_bind (setmr_reg_inv σ1 ct htcb hcurY xr _ bf s2 ar _ hI2 1#u64 rfl (by simp) r1.ty) ?_
    rintro ⟨l3, s3⟩ ⟨-, hI3, hk3, hc3⟩
    refine WP.spec_bind (setmr_reg_inv σ1 ct htcb hcurY xr _ bf s3 ar _ hI3 2#u64 rfl (by simp) r1.size) ?_
    rintro ⟨l4, s4⟩ ⟨-, hI4, hk4, hc4⟩
    refine WP.spec_bind (setmr_reg_inv σ1 ct htcb hcurY xr _ bf s4 ar _ hI4 3#u64 rfl (by simp) r1.rw) ?_
    rintro ⟨l5, s5⟩ ⟨-, hI5, hk5, hc5⟩
    simp only at hI2 hk2 hc2 hI3 hk3 hc3 hI4 hk4 hc4 hI5 hk5 hc5
    have hks5 : L.ksb s5 = L.ksb s1 := hk5.trans (hk4.trans (hk3.trans hk2))
    have hcp5 : L.cpu s5 = L.cpu s1 := hc5.trans (hc4.trans (hc3.trans hc2))
    have hBP5 : Vs.BufPlaced (L := L) Z.N Z.C Z.B Z.c s5 σ1 :=
      (hBPl Z s1 ar σ1 rfl hX1).mono hks5 (fun _ _ _ h => h)
    have tail : ∀ v : U64, (do
        let (len, s6) ← msg.set_mr st s5 ct bf 4#u64 v
        let s7 ← tcb.reply_words st s6 ct len
        let s8 ← sched.set_thread_state st s7 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s8)) ⦃ res =>
          TopPostRMX (L := L) (XTop (L := L) AR) σ blk true don (Fl4Spec.NonDetE.liftME
            Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv)) ct s
            (res.1, res.2, ar) ⦄ := by
      intro v
      refine WP.spec_bind (Vs.setmr_inv σ1 ct htcb hcurY hkc1 _ bf hw0 hbm s5 ar _ hI5 hBP5 4#u64 rfl
        (by simp) v) ?_
      rintro ⟨len, s6⟩ ⟨hlen, hI6, hk6, hc6⟩
      simp only at hlen hI6 hk6 hc6
      have hfr : ∀ q, Endp.ipcBufOf true xr = some q → ∀ z ∈ Endp.mrPairs
          ([] ++ [r1.vaddr.bv] ++ [r1.ty.bv] ++ [r1.size.bv] ++ [r1.rw.bv] ++ [v.bv]),
          (Endp.bufAddr q z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr q z.1) σ1 :=
        fun q hq z hz => ⟨Endp.bufAddr_aligned hX1.fin.1.2.ep (hbm q hq) z.1,
          buf_frame_of_ok hOK1 hkc1 hq z.1 (mrPairs_lt hz)⟩
      have hl5 : ([] ++ [r1.vaddr.bv] ++ [r1.ty.bv] ++ [r1.size.bv] ++ [r1.rw.bv] ++ [v.bv]).length = 5 := rfl
      refine data_tail_k hX1 hcurY hkc1 rfl hact1 hI6 (hk6.trans hks5) (hc6.trans hcp5)
        (by rw [hl5]; decide) hfr len (by rw [hlen]; simp) (by rw [hlen]; cases Endp.ipcBufOf true xr <;>
          simp [mrLen]) _ ?_
      rintro s8 hne ⟨z, hz, hRT, hXT⟩
      exact (WP.spec_ok _).2 (Or.inr ⟨rfl, hne, _, DecOut.of_eq hdec, σ1, hst1, _, σ1, hy _ hl5, z, hz, hRT, hXT⟩)
    split
    · exact tail 1#u64
    · exact tail 0#u64

/-! ## SetFlags -/

/-- FL4's flags word of a TCB (`tcb::FLAGS`). -/
def tFlagsWA (t : U64) : U64 := core.num.U64.wrapping_add t 3456#u64

/-- **The flags relation** (as IpcBuf's `BufWordRel`): for the TCBs of `T`,
the spec's `tcb_flags` are the flags of FL4's flags word. A relation the
steps keep (`FlagsRel.frame`; SetFlags sets both sides, `FlagsRel.set`). -/
def FlagsRel (T : Set U64) (m : U64 → U64) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ t ∈ T, ∃ x, σ.kheap t.bv = some (.tcb x) ∧ Fl4Spec.wordToTcbFlags (m (tFlagsWA t)).bv = x.tcbFlags

/-- **`FlagsRel` across a step** that writes no flags word of `T` and keeps
every TCB's `tcb_flags`. -/
theorem FlagsRel.frame {T : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} (h : FlagsRel T m σ)
    (hm : ∀ t ∈ T, m' (tFlagsWA t) = m (tFlagsWA t))
    (hk : ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbFlags = x.tcbFlags) :
    FlagsRel T m' σ' := by
  intro t ht
  obtain ⟨x, hx, e⟩ := h t ht
  obtain ⟨y, hy, ey⟩ := hk _ x hx
  exact ⟨y, hy, by rw [hm t ht, ey, e]⟩

/-- **`FlagsRel` across SetFlags' writes**: FL4's flags word of `p` and the
spec's `tcb_flags` of `p` set to its flags, the other flags words and TCBs'
flags kept. -/
theorem FlagsRel.set {T : Set U64} {m m' : U64 → U64} {σ : Fl4Spec.State Unit} (h : FlagsRel T m σ)
    {p : U64} {xp : Fl4Spec.Tcb} (hkp : σ.kheap p.bv = some (.tcb xp)) (w : U64)
    (hp : m' (tFlagsWA p) = w) (hm : ∀ t ∈ T, t ≠ p → m' (tFlagsWA t) = m (tFlagsWA t)) :
    FlagsRel T m' (Notif.updK σ p.bv (.tcb { xp with tcbFlags := Fl4Spec.wordToTcbFlags w.bv })) := by
  intro t ht
  by_cases e : t = p
  · subst e; exact ⟨{ xp with tcbFlags := Fl4Spec.wordToTcbFlags w.bv }, by simp [Notif.updK], by rw [hp]⟩
  · obtain ⟨x, hx, ex⟩ := h t ht
    have hne : t.bv ≠ p.bv := fun h' => e (UScalar.eq_of_val_eq (by
      have := congrArg BitVec.toNat h'; simpa using this))
    exact ⟨x, by simp [Notif.updK, Function.update_of_ne hne, hx], by rw [hm t ht e, ex]⟩

theorem and1_ne (x : BitVec 64) : x &&& 1 ≠ 0 ↔ x.getLsbD 0 = true := by
  constructor
  · intro h
    by_contra hc
    apply h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and]
    by_cases e : i = 0
    · subst e; simpa using hc
    · simp [BitVec.getLsbD_one, e]
  · intro h e
    have := congrArg (fun y => y.getLsbD 0) e
    simp at this
    rw [BitVec.getLsbD_eq_getElem (by omega)] at h
    rw [this] at h; cases h

theorem w2f_mem (w : BitVec 64) :
    Fl4Spec.TcbFlag.fpuDisabled ∈ Fl4Spec.wordToTcbFlags w ↔ w.getLsbD 0 = true := by
  show w &&& Fl4Spec.tcbFlagToWord .fpuDisabled &&& Fl4Spec.tcbFlagMask ≠ 0 ↔ _
  have h1 : Fl4Spec.tcbFlagToWord .fpuDisabled = 1 := by decide
  have h2 : Fl4Spec.tcbFlagMask = 1 := by decide
  rw [h1, h2, BitVec.and_assoc, show (1 : BitVec 64) &&& 1 = 1 by decide, and1_ne]

/-- **FL4's new flags word has the spec's new flags.** -/
theorem flags_new (f c s : BitVec 64) :
    Fl4Spec.wordToTcbFlags ((f &&& ~~~c) ||| (s &&& 3)) =
      Fl4Spec.wordToTcbFlags f \ Fl4Spec.wordToTcbFlags c ∪ Fl4Spec.wordToTcbFlags s := by
  ext g
  cases g
  simp only [Set.mem_union, Set.mem_diff, w2f_mem, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not]
  have : (3 : BitVec 64).getLsbD 0 = true := by decide
  simp [this]

theorem flags_mask_eq : fl4_abi.consts.tcb_flag.MASK = 3#u64 := by
  unfold fl4_abi.consts.tcb_flag.MASK fl4_abi.consts.tcb_flag.FPU_DISABLED fl4_abi.consts.tcb_flag.TRAP_SYSCALLS
  rfl

theorem flags_eq (s : S) (t : U64) : obj.Tcb.flags st t s = ok (L.mem s (tFlagsWA t)) := by
  unfold obj.Tcb.flags layout.tcb.FLAGS layout.tcb.F
  have h : (3328#u64 + 128#u64 : Result U64) = ok 3456#u64 := rfl
  rw [h]; simp only [bind_ok, lift]
  exact L.read_eq _ _

set_option maxHeartbeats 16000000 in
/-- **TcbXOpen's SetFlags at `XTop`**, called or not: the restart, FL4's
flags read (`FlagsRel`, a per-`Z` relation) and write (`XTopAt.tcbWrA`)
against the spec's `set_flags` (`TcbBufStep`), the FPU release when the
FPU is disabled (XTopFpuRel's `XTopAt.fpuReleaseX`, from `ARKeep` [P]), then the data tail of the new flags
word. -/
theorem tcb_set_flagsX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T)
    (hDI : DelInv Z.th (L.mem s))
    (hFl : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → FlagsRel Z'.T (L.mem s') σ')
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetFlags)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (hK : ARKeep arI AR) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hBT : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → BufWordRel Z'.T (L.mem s') σ')
    (hP0 : IPlaced Z.N Z.T Z.E Z.R Z.B)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKRX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSetFlags p ⟨length, buf, call, slot, extra⟩
      blk call don slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hP := hX.rel.1
  obtain ⟨htcb, xc, hkc⟩ := hX.curTcb hcur
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hpT := hTh p hp
  unfold TcbOKRX
  rw [decode_flags_eq arI s ar p _ hstall, setFlags_dec slbl hlbl]
  by_cases h1 : length < 2#u64
  · unfold tcb.decode_set_flags
    simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage,
      setFlags_trunc σ p.bv _ (by rw [List.length_map, ← hlen]; scalar_tac), Or.inl trivial⟩, ⟨Z, hX⟩⟩)
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
    | [_], h => exfalso; simp only [List.length_singleton] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, hcu1, hk1, hc1⟩ :=
    restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
  have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
    rw [← hcur]; exact hst1
  obtain ⟨hX1, -, -⟩ := hX.restart' hC hcur hs1 hst1'
  have hσ1 : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { xc with tcbState := .restart })) ct.bv := by
    rw [Notif.setThreadState_eq .restart hkc] at hst1'
    exact ((Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hst1'))).2).symm
  have hkc1 : σ1.kheap ct.bv = some (.tcb { xc with tcbState := .restart }) := by
    rw [hσ1, Notif.stsAct_kheap]; simp [Notif.updK]
  have hcurY1 : σ1.curThread = ct.bv := by rw [hcu1, hcur]
  have hdec := DecOut.of_eq (setFlags_ok σ p.bv y0.bv y1.bv (rest.map UScalar.bv))
  unfold tcb.decode_set_flags
  simp only [h1, ↓reduceIte]
  rw [hct]; simp only [bind_ok]; rw [ha0]; simp only [bind_ok]; rw [ha1]; simp only [bind_ok]
  rw [hrc1]; simp only [bind_ok]
  rw [flags_eq]; simp only [bind_ok, lift, set_flags_eq]
  -- the flags, both sides
  obtain ⟨xp, hkp, hfp⟩ := hFl Z s1 ar σ1 rfl hX1 p hpT
  set f := L.mem s1 (tFlagsWA p)
  set f2 := (f &&& ~~~y0) ||| (y1 &&& fl4_abi.consts.tcb_flag.MASK) with hf2
  set nf : Fl4Spec.TcbFlags := xp.tcbFlags \ Fl4Spec.wordToTcbFlags y0.bv ∪ Fl4Spec.wordToTcbFlags y1.bv with hnf
  have hW2 : Fl4Spec.wordToTcbFlags f2.bv = nf := by
    rw [hnf, ← hfp, hf2, flags_mask_eq, UScalar.bv_or, UScalar.bv_and, UScalar.bv_and, UScalar.bv_not]
    exact flags_new _ _ _
  obtain ⟨Q, R0, hc, -⟩ := hX1.fin.1.1.1.lists
  have hpf := (hc.tcbs p hpT).fits
  set s2 := L.wr s1 (core.num.U64.wrapping_add p 3456#u64) f2
  set σ2 := Notif.updK σ1 p.bv (.tcb { xp with tcbFlags := nf })
  have hX2 : XTopAt (L := L) AR Z s2 ar σ2 :=
    (hX1.tcbWrA hpT (core.num.U64.wrapping_add p 3456#u64) 3456 (Or.inr (Or.inr (Or.inr rfl)))
      (Notif.tfield_val (hc.tcbs p hpT) (by decide)) f2).bufSpec (tcbFlagsStep_upd hkp nf)
  have hts : Fl4Spec.setFlags (Z := Unit) p.bv nf σ1 = ({((), σ2)}, False) := Notif.threadSet_eq _ hkp
  have hcur2 : σ2.curThread = ct.bv := hcurY1
  have hkc2 : ∃ y, σ2.kheap ct.bv = some (.tcb y) ∧ y.tcbState = .restart := by
    by_cases e : ct.bv = p.bv
    · rw [e] at hkc1 ⊢
      have e2 := Fl4Spec.KernelObject.tcb.inj (Option.some.inj (hkp.symm.trans hkc1))
      exact ⟨{ xp with tcbFlags := nf }, by simp [σ2, Notif.updK], by rw [e2]⟩
    · exact ⟨{ xc with tcbState := .restart }, by simp [σ2, Notif.updK, Function.update_of_ne e, hkc1], rfl⟩
  have hfpu : ((f2 &&& fl4_abi.consts.tcb_flag.FPU_DISABLED) != 0#u64) = true ↔
      Fl4Spec.TcbFlag.fpuDisabled ∈ nf := by
    rw [← hW2, w2f_mem, ← and1_ne]
    have key : ∀ x : U64, (x &&& fl4_abi.consts.tcb_flag.FPU_DISABLED) = 0#u64 ↔ x.bv &&& 1 = 0 := by
      intro x; rw [← bv_eq_iff']
      show UScalar.bv (x &&& fl4_abi.consts.tcb_flag.FPU_DISABLED) = UScalar.bv 0#u64 ↔ _
      rw [UScalar.bv_and]; unfold fl4_abi.consts.tcb_flag.FPU_DISABLED; rfl
    simp only [bne_iff_ne, ne_eq, key]
  -- the tail, from the spec's state after the FPU step
  have tail : ∀ (a1 : A) (σ3 : Fl4Spec.State Unit) (Z3 : XSets),
      ((), σ3) ∈ (Fl4Spec.NonDet.when (Fl4Spec.TcbFlag.fpuDisabled ∈ nf) (Fl4Spec.fpuRelease (Z := Unit) p.bv)
        σ2).1 → XTopAt (L := L) AR Z3 s2 a1 σ3 → Z3.th = Z.th → σ3.curThread = ct.bv →
      (∃ y, σ3.kheap ct.bv = some (.tcb y) ∧ y.tcbState = .restart) →
      (if call = true then (do
        let buf ← msg.lookup_ipc_buffer st s2 true ct
        let (len, s3) ← msg.set_mr st s2 ct buf 0#u64 f2
        let s4 ← tcb.reply_words st s3 ct len
        let s5 ← sched.set_thread_state st s4 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a1))
      else (do
        let s3 ← sched.set_thread_state st s2 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a1))) ⦃ res =>
        TopPostRMX (L := L) (XTop (L := L) AR) σ blk call don (Fl4Spec.NonDetE.liftME
          Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4SetFlags (Z := Unit)
            ((y0 :: y1 :: rest).map UScalar.bv) p.bv)) ct s res ⦄ := by
    intro a1 σ3 Z3 h3 hX3 hth3 hcur3 ⟨y3, hk3, hrs3⟩
    have hmem : (.ok [f2.bv], σ3) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
        (.invokeFl4TCB (.setFlags p.bv y0.bv y1.bv))).run σ1).1 := by
      show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
      refine mem_liftE (x := ([f2.bv], σ3)) ?_
      show ([f2.bv], σ3) ∈ ((do
        let flags ← Fl4Spec.threadGet (Z := Unit) Fl4Spec.Tcb.tcbFlags p.bv
        let newFlags ← pure (flags \ Fl4Spec.wordToTcbFlags y0.bv ∪ Fl4Spec.wordToTcbFlags y1.bv)
        Fl4Spec.setFlags p.bv newFlags
        Fl4Spec.NonDet.when (Fl4Spec.TcbFlag.fpuDisabled ∈ newFlags) (Fl4Spec.fpuRelease p.bv)
        let w ← Fl4Spec.NonDet.select {w | Fl4Spec.wordToTcbFlags w = newFlags}
        return [w]) σ1).1
      rw [Notif.nd_bind_one (Notif.threadGet_eq _ hkp), Notif.nd_pure_bind', Notif.nd_bind_one hts]
      exact mem_bind_nd (x := ((), σ3)) (by convert h3) (mem_bind_nd (x := (f2.bv, σ3)) (y := ([f2.bv], σ3)) ⟨hW2, rfl⟩
        (Set.mem_singleton _))
    have hcurY : ct.bv = σ3.curThread := hcur3.symm
    have htcb3 : Z3.th ct = some .tcb := by rw [hth3]; exact htcb
    have hact3 : OutsideObjects Z3.th (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) := by
      rw [hth3, show L.cpu s2 = L.cpu s by simp [s2, L.cpu_wr, hc1],
        Sched.nodeAt_ksb (show L.ksb s2 = L.ksb s by simp [s2, L.ksb_wr, hk1])]; exact hact
    cases call
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_mono (nodata_tail_xtop hX3 hcurY hk3 hrs3 hact3 [f2.bv]) ?_
      rintro res ⟨hres, hne, z, hz, hRT, hXT⟩
      exact Or.inr ⟨hres, hne, _, hdec, σ1, hst1, [f2.bv], σ3, hmem, z, hz, hRT, hXT⟩
    · simp only [↓reduceIte]
      refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s2 true ct L.total) ?_
      rintro bf -
      have hI0 : Vs.RInv (L := L) Z3.th Z3.P Z3.L4 Z3.L3 Z3.L2 Z3.L1 Z3.N Z3.T Z3.C Z3.E Z3.R Z3.B Z3.c AR Z3.G s2 a1
          (MrS σ3 ct.bv y3 (Endp.ipcBufOf true y3) []) := by
        rw [MrS_nil hk3]; exact hX3.toRInv
      refine WP.spec_bind (setmr_reg_inv _ ct htcb3 hcurY y3 _ bf s2 a1 [] hI0 0#u64 rfl (by decide) f2) ?_
      rintro ⟨len, s3⟩ ⟨hlen, hI3, hk3', hc3'⟩
      simp only at hlen hI3 hk3' hc3'
      refine WP.spec_mono (data_tail_xtop hX3 hcurY hk3 hrs3 hact3 hI3 hk3' hc3' (by simp [Fl4Spec.msgMaxLength])
        (fun _ _ z hz => by simp [Endp.mrPairs] at hz) len
        (by cases Endp.ipcBufOf true y3 <;> simp [mrLen, hlen]) (by simp only [List.length_nil] at hlen; omega)) ?_
      rintro res ⟨hres, hne, z, hz, hRT, hXT⟩
      exact Or.inr ⟨hres, hne, _, hdec, σ1, hst1, [f2.bv], σ3, hmem, z, hz, hRT, hXT⟩
  by_cases hF : ((f2 &&& fl4_abi.consts.tcb_flag.FPU_DISABLED) != 0#u64) = true
  · simp only [hF, ↓reduceIte]
    have hks2 : L.ksb s2 = L.ksb s := (L.ksb_wr _ _ _).trans hk1
    refine WP.spec_bind (hX2.fpuReleaseX hK (by rw [hks2]; exact hKA) (hBT Z s2 ar σ2 rfl hX2) hP0 hpT) ?_
    rintro a1 ⟨σ3, h3, hc3, hst3, V3, hX3⟩
    obtain ⟨y2, hky2, hrs2⟩ := hkc2
    obtain ⟨y3, hky3, hrs3⟩ := hst3 _ y2 hky2
    refine tail a1 σ3 (Z.mv Z.G V3) ?_ hX3 rfl (by rw [hc3]; exact hcur2) ⟨y3, hky3, by rw [hrs3, hrs2]⟩
    unfold Fl4Spec.NonDet.when; rw [if_pos (hfpu.1 hF)]; exact h3
  · simp only [Bool.not_eq_true] at hF
    simp only [hF, Bool.false_eq_true, ↓reduceIte]
    refine tail ar σ2 Z ?_ hX2 rfl hcur2 hkc2
    unfold Fl4Spec.NonDet.when
    rw [if_neg (fun h => by have := hfpu.2 h; rw [hF] at this; cases this)]
    exact Set.mem_singleton _

/-! ## The open labels with the data labels proved -/

/-- **The Thread cap's labels still open** [W] once the data labels are
proved: SetBreakpoint, ReadFPU, WriteFPU, SetTimer. -/
structure TcbXOpen4 (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (p : U64) (c : tcb.Ctx) (blk call don : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) : Prop where
  setBreakpoint : lbl = fl4_abi.label.TCBSetBreakpoint →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  readFPU : lbl = fl4_abi.label.TCBReadFPU →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  writeFPU : lbl = fl4_abi.label.TCBWriteFPU →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setTimer : lbl = fl4_abi.label.TCBSetTimer →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer

set_option maxHeartbeats 4000000 in
/-- **`TcbXOpen` with the data labels proved** (`tcb_get_bpX`,
`tcb_single_stepX`, `tcb_set_flagsX`): the four labels still open, and their
premises (`ArgRel` [J] for two arguments, `GetBpHyp` [P], `BufWordRel` and
`FlagsRel` (per-`Z` relations), `IpcBufCapOK`, `BufCover`, `BufPlaced` [J],
`ARKeep` [P] for SetFlags' FPU release). -/
theorem tcbXOpen_of {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDI : DelInv Z.th (L.mem s))
    (hBT : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → BufWordRel Z'.T (L.mem s') σ')
    (hP0 : IPlaced Z.N Z.T Z.E Z.R Z.B)
    (hOK : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → Endp.IpcBufCapOK σ')
    (hBC : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → Endp.BufCover Z'.T Z'.B σ')
    (hBPl : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' →
      Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ')
    (hFl : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → FlagsRel Z'.T (L.mem s') σ')
    (lbl length : U64) (p : U64) (hp : Z.th p = some .tcb)
    (blk call don : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hA2 : ArgRel (st := st) s σ ct buf buffer 2) (hG : GetBpHyp (st := st) s ct p)
    (hK : ARKeep arI AR)
    (hO : TcbXOpen4 (L := L) arI (XTop (L := L) AR) s ar σ lbl p ⟨length, buf, call, cslotAddr sl, extra⟩ blk call
      don slbl (argsU.map UScalar.bv) ci sl excaps buffer) :
    TcbXOpen (L := L) arI (XTop (L := L) AR) s ar σ lbl p ⟨length, buf, call, cslotAddr sl, extra⟩ blk call
      don slbl (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  refine ⟨hO.setBreakpoint, ?_, ?_, ?_, hO.readFPU, hO.writeFPU, hO.setTimer⟩
  · rintro rfl
    obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .getBreakpoint by
      simp [tcbExtOf])
    exact tcb_get_bpX arI s ar σ hX hC hDI hBT hOK hBC hBPl p slbl hg he length buf ct hct hcur hact (hstall' p)
      buffer (fun i hi => hA2 i (by omega)) hG call _ extra blk don _ ci sl excaps
  · rintro rfl
    obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .configureSingleStepping by
      simp [tcbExtOf])
    exact tcb_single_stepX arI s ar σ hX hKA hC hTh hDI hBT hP0 p hp slbl hg he length buf ct hct hcur hact (hstall' p)
      buffer hA2 call _ extra blk don _ ci sl excaps
  · rintro rfl
    exact tcb_set_flagsX arI s ar σ hX hC hTh hDI hFl p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct
      hct argsU hlen hargs hcur hact (hstall' p) hK hKA hBT hP0 call _ extra blk don ci sl excaps buffer

end

end

end Fl4Proofs.P3
