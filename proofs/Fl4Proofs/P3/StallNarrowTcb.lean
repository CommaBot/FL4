/-
P3 (p3P gen 2, finding (c) fix, lower half): **the Thread cap's decode with no `hstall'`**.

`JEntryAt.stall` (`∀ q, remote_tcb_stall s ar q = ok (s, ar)`) is false at reachable states
(`StallFinding`); its only consumer on `kernel_entry_reachU30`'s path is the Thread decode's
`hstall'`, used at the target `p` and at CopyRegisters' source. Both are TCBs of `Z.T`, where
the stall is the no-op by `remote_tcb_stall_id` from `JAtZ`'s `SchedRel` (`JAtZ.stallT`).

* `JAtZ.stallT`: `∀ q ∈ Z.T, remote_tcb_stall s a q = ok (s, a)` (proved, no premise).
* `tcb_copy_regsJT`, `decode_invocation_threadJ_stepMT`, `decode_invocation_threadJ_stepMMT`:
  XTopJointTcb's `tcb_copy_regsJ`, XTopJointMRTcbL's `decode_invocation_threadJ_stepM`,
  XTopJointKEntry40's `decode_invocation_threadJ_stepMM` without `hstall'` (generated copies:
  the target's stall `J.stallT p hpT`, the source's `J.stallT src` with the source in `Z.T` by
  its cap, `JAtZ.thT`). No new premise.
-/
import Fl4Proofs.P3.XTopJointKEntry40
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The remote stall of a TCB of `Z.T` is the no-op** (one core: every thread of `T` has the
current core's affinity, `SchedRel`; `remote_tcb_stall_id`). -/
theorem JAtZ.stallT {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ q ∈ Z.T, smp.remote_tcb_stall st arI s a q = ok (s, a) :=
  fun _ hq => spec_eq_ok (remote_tcb_stall_id (ar := arI) a J.xtop.fin.1.1.1 hq)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The CopyRegisters label at `JAt`** (as `tcb_copy_regsX`): TcbCtl's
decode with the source the first extra cap's thread, the caller's restart
(`JAtZ.restartJ`, `Entered` after by `restart_mid`), the target out of the
dead set by its cap in the invoked slot (`JAtZ.undead`, the slots kept by
the restart), then XTopJointCopyRegs' `JAtZ.copyRegsJ`. The stalls of the target and the source
are `JAtZ.stallT` (no `hstall'`). Named: the
source not idle (`hidS`), the platform's `MIN_BUDGET` [P]. -/
theorem tcb_copy_regsJT (hAT : P0.ArchTotal arI)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ)
    (hidS : ∀ (sl' : Fl4Spec.CslotPtr) q, AbsSlot Z.th sl' → capV (L.mem s) (cslotAddr sl') = .Thread q →
      q ≠ L.idleW s)
    (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbCopyRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl) (hsc : capV (L.mem s) (cslotAddr ssl) = .Thread p)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBCopyRegisters p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hX := J.xtop
  have hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T := by
    intro hx q hc
    have h0 := hXc.2 0 x0 rfl
    obtain ⟨e, he⟩ : ∃ e, excaps[0]? = some e := by
      rcases excaps with _ | ⟨e, rest⟩
      · exact absurd (h0.1.2 (by simp)) hx
      · exact ⟨e, rfl⟩
    obtain ⟨hxe, -, ps, hps, hpe⟩ := h0.2 e he
    have hA0 : AbsSlot Z.th e.2 := ⟨ps, hpe, Or.inl hps⟩
    exact J.thT q (show CapValid Z.th (.Thread q) from
      J.xtop.rel.2.1.2.1.abs hA0 (by rw [← hxe, capAt_capV, hc]))
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeCopyRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) (excaps.map Prod.fst)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_copy_eq arI s ar p _ (J.stallT p hpT), hdec0]
  unfold tcb.decode_copy_registers tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have htr : args = [] ∨ excaps = [] →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMX (L := L) (JAt (L := L) arI AR) σ blk
        call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeCopyRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) (excaps.map Prod.fst)))
        s res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
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
    have hthr0 : capV (L.mem s) x0 = .Thread src := by
      revert hsrc; cases capV (L.mem s) x0 <;> simp [threadArgF]
    simp only [J.stallT src (hcapT h0 src hthr0), bind_ok]
    obtain ⟨s1, σ1, x, hrc1, hst, hk, -, he1, -, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    obtain ⟨-, x', hk', hrun'⟩ := J.curRunnable hni hct
    rw [hk] at hk'; cases hk'
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
    have hA0 : AbsSlot Z.th e0.2 := ⟨ps0, hps01, Or.inl hps0⟩
    have hxs : IsSlot Z.th x0 := by rw [hxe0]; exact hA0.isSlot
    have hsrcT : src ∈ Z.T := J.thT src (show CapValid Z.th (.Thread src) from
      J.xtop.rel.2.1.2.1.abs hA0 (by rw [← hxe0, capAt_capV, hthr]))
    have hsI : src.bv ≠ σ1.idleThread := by rw [hid1]; exact J.ne_idle (hidS e0.2 src hA0 (by rw [← hxe0]; exact hthr))
    -- the slots kept by the caller's restart: the target's cap, so the target out of the dead set
    have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) := by
      have h := XTopAt.restart J.xtop hcur hk hrun'
      rw [hs1, WP.spec_ok] at h; exact h.2.1
    have hcap1 : capAt (L.mem s1) (cslotAddr ssl) = ok (.Thread p) := by
      rw [capAt_capV, hSS.capV hAs.isSlot, hsc]
    have hC := J.curInv (by rw [hni.2]; simp)
    have hcs : Fl4Spec.schedulable σ.curThread σ = true := ct_schedulable hC J.act J.inv (hcur ▸ hk) hrun'
    obtain ⟨hres1, -, -, -, -⟩ := restart_mid hcur hk (hcur ▸ hcs) hni.2 hC J.off J.act J.inv
    have hEn1 : Entered σ1 := ⟨by rw [hct1, hid1]; exact hni.1, by rw [he1]; exact hres1⟩
    refine WP.spec_mono ((J1.undead hAs.isSlot hcap1 hpT).copyRegsJ hAT (jCancel_send arI) (jCancel_ntfn arI)
      (jCancel_recv arI) (jCancel_reply arI) (hmb ar) hEn1 hsrcT hpT hsI (fun h => h.2 rfl) y0) ?_
    rintro ⟨r2, s2, a2⟩ ⟨hr2, -, σ', hsp, V', Ac', Lst', D', J2⟩
    simp only at hr2; subst hr2
    have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
        ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.copyRegisters p.bv src.bv
          (Fl4Spec.testBit y0.bv 0) (Fl4Spec.testBit y0.bv 1) (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3)
          Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 := by
      show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) _).run σ1).1
      rw [invokeTcb_cr]
      exact mem_liftE (x := ([], σ')) (mem_bind_nd (by rw [hsp]; exact Set.mem_singleton _) (Set.mem_singleton _))
    exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
      J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac', Lst', D', J2, inferInstance⟩⟩
  · rw [hsrc]
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, hJ0⟩)
    exact run_liftME_err (run_bind_error hrun _)


set_option maxHeartbeats 4000000 in
/-- **The Thread cap, `JAt` after** (module docstring): every label proved at
`J`, the target's stall by `JAtZ.stallT` (no `hstall'`) (no per-op `JPostHyp`, no X-level `TcbXIpc`). -/
theorem decode_invocation_threadJ_stepMT [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hFl : FlagsRel Z.T (L.mem s) σ) (hfnz : FrNZ Z.th (L.mem s))
    (lbl length : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl)
    (hsc : capV (L.mem s) (cslotAddr sl) = .Thread p)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hpI : p ≠ L.idleW s)
    (x0 x1 x2 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps) (hnc : NcHyp (st := st) Z.th s σ x0 x1 x2)
    (hnc0 : ∀ sl : Fl4Spec.CslotPtr, AbsSlot Z.th sl → x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
    (hA5 : ArgRel (st := st) s σ ct buf buffer 5) (hGb : GetBpHyp (st := st) s ct p)
    (hFJ : lbl = fl4_abi.label.TCBReadFPU → FpuFrameJHyp (L := L) Z s σ x0)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hidS : ∀ (sl' : Fl4Spec.CslotPtr) q, AbsSlot Z.th sl' → capV (L.mem s) (cslotAddr sl') = .Thread q →
      q ≠ L.idleW s)
    (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf) (hl : argsU.length ≤ 120)
    (hJDP : JDelParts (L := L) arI AR Z.th) (hsg : SpecGlob σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hmv : MRV MR ar σ)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hTA : TimeAgree arI) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) (.Thread p)
      blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ Z.T := J.thT p hp
  -- WriteRegisters: the caller's buffer mapped (`lookup_buf_full`, `BufCover`), the arguments after its restart
  have hcur : σ.curThread = ct.bv := (J.curEq hct).1
  have hctH : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have hctT : ct ∈ Z.T := J.thT ct hctH
  have hbm : buf ≠ 0#u64 → ∃ sp, BufMap Z.B buf sp := by
    intro hb0
    obtain ⟨x, hk, hwx⟩ := J.buf ct hctT
    have hL := lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 hctH hk (J.xferH.1) false
    rw [hbuf, WP.spec_ok] at hL
    cases hq : Endp.ipcBufOf false x with
    | none => exact absurd (hL.1.2 hq) hb0
    | some q => exact ⟨q, J.xferH.2.1 ct hctT x false q hk hq buf (hL.2 hwx q hq)⟩
  have hWR : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s1 ct buf i = ok x := by
    intro s1 h1 i x hx
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 hx
    obtain ⟨sp, hsp⟩ : ∃ sp, buf ≠ 0#u64 → BufMap Z.B buf sp := by
      by_cases hb : buf = 0#u64
      · exact ⟨0, fun h => absurd hb h⟩
      · obtain ⟨sp, h⟩ := hbm hb; exact ⟨sp, fun _ => h⟩
    rw [J.argsRestart (J.xferH.2.2) hctT hctH hsp (by omega) h1]
    exact hargs i x hx
  -- the cap installs' deletion at `J` (as `decode_invocation_cnodeJ_stepsL`)
  have hHp := tcbInsWM_wjl (L := L) (MR := MR) (Z := Z) (H := H) (Cs := Cs) arI hT hJDP.archRef hJDP.arKeep hJDP.vt
    hJDP.thr hnd hMP hKD hPA hARI.toMask
  have hP0 := J.ppr0_start arI hni hRd0 hnq
  have hR : RestartWJ (st := st) Z s ar σ (WMR MR (WJL (L := L) arI AR Z H Cs (L.ksb s))) :=
    fun _ hct s1 σ1 h1 h2 => ⟨WJL.restart arI J hni hsg hP0 hLv hct s1 σ1 h1 h2,
      mrv_keep hMP hmv (MachT.mtk_setThreadState' _ _ σ ((), σ1) (mem_of_single h2))⟩
  by_cases h9 : lbl = fl4_abi.label.TCBSetTimeoutEndpoint
  · subst h9
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_timeoutJM arI s ar σ J hni hsg hP0 hHp hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct
        (J.stallT p hpT) call sl hAs extra x0 x1 x2 hx0 excaps hXc _ blk don ci buffer)
  by_cases h11 : lbl = fl4_abi.label.TCBSetSpace
  · subst h11
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_spaceJM arI s ar σ J hni hsg hP0 hHp hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct
        argsU hlen hargs (J.stallT p hpT) call sl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hXc hnc blk don ci buffer)
  by_cases h10 : lbl = fl4_abi.label.TCBSetIPCBuffer
  · subst h10
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_ipcJM arI s ar σ J hni hsg hP0 hHp hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct
        hct argsU hlen hargs (J.stallT p hpT) call sl hAs extra x0 x1 x2 hx0 excaps hXc hnc0 hfnz blk don ci buffer)
  by_cases h5 : lbl = fl4_abi.label.TCBConfigure
  · subst h5
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_configureJM arI s ar σ J hni hsg hP0 hHp hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct
        hct argsU hlen hargs (J.stallT p hpT) call sl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hXc hnc hfnz blk don ci buffer)
  -- the first extra cap's thread among the TCBs (as `decode_invocation_threadJAt`)
  have hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T := by
    intro hx q hc
    have h0 := hXc.2 0 x0 rfl
    obtain ⟨e, he⟩ : ∃ e, excaps[0]? = some e := by
      rcases excaps with _ | ⟨e, rest⟩
      · exact absurd (h0.1.2 (by simp)) hx
      · exact ⟨e, rfl⟩
    obtain ⟨hxe, -, ps, hps, hpe⟩ := h0.2 e he
    have hA0 : AbsSlot Z.th e.2 := ⟨ps, hpe, Or.inl hps⟩
    exact J.thT q (show CapValid Z.th (.Thread q) from
      J.xtop.rel.2.1.2.1.abs hA0 (by rw [← hxe, capAt_capV, hc]))
  by_cases h8 : lbl = fl4_abi.label.TCBSetSchedParams
  · subst h8
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_sched_paramsJM arI s ar σ J hni hsg hP0 hHp hR hT hARI.toARKeep hTA p hp slbl
        (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen hargs hpI (J.stallT p hpT) call sl hAs hsc extra
        x0 x1 x2 hx0 hx1 hx2 excaps hXc hcapT hcapC blk don ci buffer)
  have hv : ∀ {c : U64}, lbl ≠ c → lbl.val ≠ c.val := fun hn e => hn (UScalar.eq_of_val_eq e)
  have hnpT := thread_noPre_of (fp := fp) (args := argsU.map UScalar.bv) (ci := ci) (sl := sl) (excaps := excaps)
    (buffer := buffer) (σ := σ) (p := p) hlbl
    ⟨by have := hv h5; simpa [fl4_abi.label.TCBConfigure] using this,
      by have := hv h8; simpa [fl4_abi.label.TCBSetSchedParams] using this,
      by have := hv h9; simpa [fl4_abi.label.TCBSetTimeoutEndpoint] using this,
      by have := hv h10; simpa [fl4_abi.label.TCBSetIPCBuffer] using this,
      by have := hv h11; simpa [fl4_abi.label.TCBSetSpace] using this⟩
  refine XCap.toPN arI (decode_invocation_threadX arI s ar σ hJ0 lbl length (cslotAddr sl) p blk call don fp buf extra
    ct hct slbl hlbl _ ci sl excaps buffer hext (J.stallT p hpT) hNative
    {
      readRegisters := fun h => by
        subst h
        exact tcb_read_regsJ arI s ar σ J hni p hpT hpI slbl (by rw [hlbl]; simp [tcbLabelOf])
          length buf ct hct argsU hlen hargs (J.stallT p hpT) call (cslotAddr sl) extra blk don ci sl excaps buffer,
      writeRegisters := fun h => by
        subst h
        exact tcb_write_regsJ arI hT hmb s ar σ J hni p hpT (cslotAddr sl) hAs.isSlot (by rw [capAt_capV, hsc]) slbl
          (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen hargs hbm hWR (J.stallT p hpT) call
          (cslotAddr sl) extra blk don ci sl excaps buffer,
      copyRegisters := fun h => by
        subst h
        exact tcb_copy_regsJT arI hT hmb s ar σ J hni hidS p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf
          ct hct argsU hlen hargs call sl hAs hsc extra x0 x1 x2 hx0 excaps hXc blk don ci buffer,
      configure := fun h => absurd h h5,
      setPriority := fun h => by
        subst h
        exact tcb_set_prioJ arI s ar σ J hni p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen
          hargs (J.stallT p hpT) call sl extra x0 x1 x2 hx0 excaps hXc hcapT blk don ci buffer,
      setMCPriority := fun h => by
        subst h
        exact tcb_set_mcpJ arI s ar σ J hni p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen
          hargs (J.stallT p hpT) call sl extra x0 x1 x2 hx0 excaps hXc hcapT blk don ci buffer,
      setSchedParams := fun h => absurd h h8,
      setTimeoutEndpoint := fun h => absurd h h9,
      setIPCBuffer := fun h => absurd h h10,
      setSpace := fun h => absurd h h11,
      suspend := fun h => by
        subst h
        exact tcb_suspendJ arI s ar σ J hni p hpT hpI slbl (by rw [hlbl]; simp [tcbLabelOf]) (J.stallT p hpT) ct hct _
          blk call don _ ci sl excaps buffer,
      resume := fun h => by
        subst h
        exact tcb_resumeJ arI hT hPA.minBudget s ar σ J hni p hpT (cslotAddr sl) hAs.isSlot (by rw [capAt_capV, hsc]) slbl
          (by rw [hlbl]; simp [tcbLabelOf]) (J.stallT p hpT) ct hct _ blk call don _ ci sl excaps buffer,
      bindNotification := fun h => by
        subst h
        exact tcb_bind_ntfnJ arI s ar σ J hni p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf (J.stallT p hpT) ct
          hct hAs.isSlot hsc call (cslotAddr sl) extra x0 x1 x2 hx0 excaps hXc blk don _ ci sl buffer,
      unbindNotification := fun h => by
        subst h
        exact tcb_unbind_ntfnJ arI s ar σ J hni p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) (J.stallT p hpT) ct hct
          length buf call (cslotAddr sl) extra blk don _ ci sl excaps buffer,
      setBreakpoint := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .setBreakpoint by
          simp [tcbExtOf])
        exact tcb_set_bpJ arI s ar σ J hni p hpT slbl hg he length buf ct hct (J.stallT p hpT) buffer hA5 call
          (cslotAddr sl) extra blk don _ ci sl excaps,
      getBreakpoint := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .getBreakpoint by
          simp [tcbExtOf])
        exact tcb_get_bpJ arI s ar σ J hni p slbl hg he length buf ct hct (J.stallT p hpT) buffer
          (fun i hi => hA5 i (by omega)) hGb call (cslotAddr sl) extra blk don _ ci sl excaps,
      unsetBreakpoint := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .unsetBreakpoint by
          simp [tcbExtOf])
        exact tcb_unset_bpJ arI s ar σ J hni p hpT slbl hg he length buf ct hct
          (J.stallT p hpT) buffer (fun i hi => hA5 i (by omega)) call (cslotAddr sl) extra blk don _ ci sl excaps,
      configureSingleStepping := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf])
          (show tcbExtOf _ = some .configureSingleStepping by simp [tcbExtOf])
        exact tcb_single_stepJ arI s ar σ J hni p hp slbl hg he length buf ct hct (J.stallT p hpT) buffer
          (fun i hi => hA5 i (by omega)) call (cslotAddr sl) extra blk don _ ci sl excaps,
      setTLSBase := fun h => by
        subst h
        exact tcb_set_tlsJ arI s ar σ J hni p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU
          hlen hargs hcw (J.stallT p hpT) call (cslotAddr sl) extra blk don ci sl excaps buffer,
      setFlags := fun h => by
        subst h
        exact tcb_set_flagsJ arI s ar σ J hni hFl p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU
          hlen hargs (J.stallT p hpT) hARI.toARKeep call (cslotAddr sl) extra blk don ci sl excaps buffer,
      readFPU := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .readFpu by
          simp [tcbExtOf])
        exact tcb_read_fpuJ arI s ar σ J hni hARI.toARKeep p hpT slbl hg he length buf ct hct argsU hlen hargs
          (J.stallT p hpT) call (cslotAddr sl) extra x0 x1 x2 hx0 excaps hXc (hFJ rfl) blk don ci sl buffer,
      writeFPU := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .writeFpu by
          simp [tcbExtOf])
        exact tcb_write_fpuJ arI s ar σ J hni hARI.toARKeep p hpT slbl hg he length buf ct hct argsU hlen hargs
          (J.stallT p hpT) call (cslotAddr sl) extra x0 x1 x2 hx0 excaps hXc blk don ci sl buffer,
      setTimer := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .setTimer by
          simp [tcbExtOf])
        exact tcb_set_timerJ arI s ar σ J hni p hpT (cslotAddr sl) hAs.isSlot (by rw [capAt_capV, hsc]) slbl hg he length buf ct hct argsU hlen hargs (J.stallT p hpT) call
          (cslotAddr sl) extra blk don ci sl excaps buffer }) hnpT



set_option maxHeartbeats 4000000 in
/-- **The Thread cap, `JAtM` after** (module docstring): the five installing
labels by XTopJointMRTcbM, every other non-VT-x label by `XCapP.mrG` on
`decode_invocation_threadJ_stepM` (FL4 `MKD.decode_thread_nonins`, spec
`perfF_tcbN`); the stalls by `JAtZ.stallT` (no `hstall'`). -/
theorem decode_invocation_threadJ_stepMMT [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hFl : FlagsRel Z.T (L.mem s) σ) (hfnz : FrNZ Z.th (L.mem s))
    (lbl length : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl)
    (hsc : capV (L.mem s) (cslotAddr sl) = .Thread p)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hpI : p ≠ L.idleW s)
    (x0 x1 x2 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps) (hnc : NcHyp (st := st) Z.th s σ x0 x1 x2)
    (hnc0 : ∀ sl : Fl4Spec.CslotPtr, AbsSlot Z.th sl → x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
    (hA5 : ArgRel (st := st) s σ ct buf buffer 5) (hGb : GetBpHyp (st := st) s ct p)
    (hFJ : lbl = fl4_abi.label.TCBReadFPU → FpuFrameJHyp (L := L) Z s σ x0)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hidS : ∀ (sl' : Fl4Spec.CslotPtr) q, AbsSlot Z.th sl' → capV (L.mem s) (cslotAddr sl') = .Thread q →
      q ≠ L.idleW s)
    (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf) (hl : argsU.length ≤ 120)
    (hJDP : JDelParts (L := L) arI AR Z.th) (hsg : SpecGlob σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hmv : MRV MR ar σ)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hTA : TimeAgree arI) :
    XCapP (L := L) arI (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) (.Thread p)
      blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩
  have hJ0M : JAtM (L := L) arI AR MR s ar σ := ⟨hJ0, hmv.1⟩
  have hX := decode_invocation_threadJ_stepMT arI s ar σ J hni hARI hT hFl hfnz lbl length p blk call don fp buf extra ct
    hct slbl hlbl argsU hlen hargs ci sl hAs hsc excaps buffer hext hNative hcw hpI x0 x1 x2 hx0 hx1 hx2 hXc hnc
    hnc0 hcapC hA5 hGb hFJ hmb hidS hbuf hl hJDP hsg hLv hnd hMP hKD hPA hmv hRd0 hnq hTA
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ Z.T := J.thT p hp
  -- WriteRegisters: the caller's buffer mapped (`lookup_buf_full`, `BufCover`), the arguments after its restart
  have hcur : σ.curThread = ct.bv := (J.curEq hct).1
  have hctH : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have hctT : ct ∈ Z.T := J.thT ct hctH
  have hbm : buf ≠ 0#u64 → ∃ sp, BufMap Z.B buf sp := by
    intro hb0
    obtain ⟨x, hk, hwx⟩ := J.buf ct hctT
    have hL := lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 hctH hk (J.xferH.1) false
    rw [hbuf, WP.spec_ok] at hL
    cases hq : Endp.ipcBufOf false x with
    | none => exact absurd (hL.1.2 hq) hb0
    | some q => exact ⟨q, J.xferH.2.1 ct hctT x false q hk hq buf (hL.2 hwx q hq)⟩
  have hWR : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s1 ct buf i = ok x := by
    intro s1 h1 i x hx
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 hx
    obtain ⟨sp, hsp⟩ : ∃ sp, buf ≠ 0#u64 → BufMap Z.B buf sp := by
      by_cases hb : buf = 0#u64
      · exact ⟨0, fun h => absurd hb h⟩
      · obtain ⟨sp, h⟩ := hbm hb; exact ⟨sp, fun _ => h⟩
    rw [J.argsRestart (J.xferH.2.2) hctT hctH hsp (by omega) h1]
    exact hargs i x hx
  -- the cap installs' deletion at `J` (as `decode_invocation_cnodeJ_stepsL`)
  have hHp := tcbInsWM_wjl (L := L) (MR := MR) (Z := Z) (H := H) (Cs := Cs) arI hT hJDP.archRef hJDP.arKeep hJDP.vt
    hJDP.thr hnd hMP hKD hPA hARI.toMask
  have hP0 := J.ppr0_start arI hni hRd0 hnq
  have hR : RestartWJ (st := st) Z s ar σ (WMR MR (WJL (L := L) arI AR Z H Cs (L.ksb s))) :=
    fun _ hct s1 σ1 h1 h2 => ⟨WJL.restart arI J hni hsg hP0 hLv hct s1 σ1 h1 h2,
      mrv_keep hMP hmv (MachT.mtk_setThreadState' _ _ σ ((), σ1) (mem_of_single h2))⟩
  by_cases h9 : lbl = fl4_abi.label.TCBSetTimeoutEndpoint
  · subst h9
    exact xcapP_of_tcb arI s ar σ hJ0M _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_timeoutJMM arI s ar σ J hni hsg hP0 hHp hmv.1 (fun _ _ _ _ _ h => h.2.1) hMP hKD hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct
        (J.stallT p hpT) call sl hAs extra x0 x1 x2 hx0 excaps hXc _ blk don ci buffer)
  by_cases h11 : lbl = fl4_abi.label.TCBSetSpace
  · subst h11
    exact xcapP_of_tcb arI s ar σ hJ0M _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_spaceJMM arI s ar σ J hni hsg hP0 hHp hmv.1 (fun _ _ _ _ _ h => h.2.1) hMP hKD hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct
        argsU hlen hargs (J.stallT p hpT) call sl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hXc hnc blk don ci buffer)
  by_cases h10 : lbl = fl4_abi.label.TCBSetIPCBuffer
  · subst h10
    exact xcapP_of_tcb arI s ar σ hJ0M _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_ipcJMM arI s ar σ J hni hsg hP0 hHp hmv.1 (fun _ _ _ _ _ h => h.2.1) hMP hKD hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct
        hct argsU hlen hargs (J.stallT p hpT) call sl hAs extra x0 x1 x2 hx0 excaps hXc hnc0 hfnz blk don ci buffer)
  by_cases h5 : lbl = fl4_abi.label.TCBConfigure
  · subst h5
    exact xcapP_of_tcb arI s ar σ hJ0M _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_configureJMM arI s ar σ J hni hsg hP0 hHp hmv.1 (fun _ _ _ _ _ h => h.2.1) hMP hKD hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct
        hct argsU hlen hargs (J.stallT p hpT) call sl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hXc hnc hfnz blk don ci buffer)
  -- the first extra cap's thread among the TCBs (as `decode_invocation_threadJAt`)
  have hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T := by
    intro hx q hc
    have h0 := hXc.2 0 x0 rfl
    obtain ⟨e, he⟩ : ∃ e, excaps[0]? = some e := by
      rcases excaps with _ | ⟨e, rest⟩
      · exact absurd (h0.1.2 (by simp)) hx
      · exact ⟨e, rfl⟩
    obtain ⟨hxe, -, ps, hps, hpe⟩ := h0.2 e he
    have hA0 : AbsSlot Z.th e.2 := ⟨ps, hpe, Or.inl hps⟩
    exact J.thT q (show CapValid Z.th (.Thread q) from
      J.xtop.rel.2.1.2.1.abs hA0 (by rw [← hxe, capAt_capV, hc]))
  by_cases h8 : lbl = fl4_abi.label.TCBSetSchedParams
  · subst h8
    exact xcapP_of_tcb arI s ar σ hJ0M _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_sched_paramsJMM arI s ar σ J hni hsg hP0 hHp hmv.1 (fun _ _ _ _ _ h => h.2.1) hMP hKD hR hT hARI.toARKeep hTA p hp slbl
        (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen hargs hpI (J.stallT p hpT) call sl hAs hsc extra
        x0 x1 x2 hx0 hx1 hx2 excaps hXc hcapT hcapC blk don ci buffer)
  have hv : ∀ {c : U64}, lbl ≠ c → lbl.val ≠ c.val := fun hn e => hn (UScalar.eq_of_val_eq e)
  have hl5 : lbl.val ≠ 5 ∧ lbl.val ≠ 8 ∧ lbl.val ≠ 9 ∧ lbl.val ≠ 10 ∧ lbl.val ≠ 11 :=
    ⟨by have := hv h5; simpa [fl4_abi.label.TCBConfigure] using this,
      by have := hv h8; simpa [fl4_abi.label.TCBSetSchedParams] using this,
      by have := hv h9; simpa [fl4_abi.label.TCBSetTimeoutEndpoint] using this,
      by have := hv h10; simpa [fl4_abi.label.TCBSetIPCBuffer] using this,
      by have := hv h11; simpa [fl4_abi.label.TCBSetSpace] using this⟩
  exact XCapP.mrG (f := id) hMP hX
    (WP.spec_mono (MKD.decode_thread_nonins L.total hT hKD ⟨hNative, h5, h8, h10, h11, h9⟩ hmv.1)
      fun r h => by split <;> exact h)
    (perfF_tcbN hlbl hl5 σ blk call don fp (argsU.map UScalar.bv) ci sl excaps buffer p)



end

end

end Fl4Proofs.P3
