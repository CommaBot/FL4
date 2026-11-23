/-
P3 (DESIGN.md §9), #68: **the TDX control cap at `JAt`** (KENTRY-PLAN tdx3):
FL4's `tdx::decode` against the spec's FL4 extension (`Fl4Spec/Ext/Tdx`,
`decodeTdxInvocation` / `performTdxInvocation`).

* `report_frame_cases`, `quote_frame_cases`, `quote_len_ok_eq`: FL4's frame
  and length checks are the spec's (`tdxReportFrame`, `tdxQuoteFrame` with
  the platform record's `tdxDmaRam`, `tdxQuoteLenOk`), given FL4's `dma_ram`
  answering that record (`TdxRel`, the joint relation's `JKern.tdx`).
* `tdx_perform_out`: every status word is an outcome of the spec's TDCALL,
  with the frame's bytes unchanged (the TD module's outputs are the spec's
  choices, so FL4's value needs no premise).
* `tdxTail_jat`: the success tail at `JAt`: the restart and the TDCALL as
  primitive steps (`Steps.restart`, `Steps.arch` with `TdxArchStep`), then
  `tdx::reply` (= `vspace::reply1`) by `Vs.reply1_invT` and `jReplyHyp`, as
  XTopJointPortIn's `portInTail_jat` without the machine step.
* `decode_invocation_tdxJ`: `XCap … (JAt …) … .TdxControl …`, every label:
  the errors at the start's `JAtZ` (the state unchanged), the three
  invocations by `tdxTail_jat`.
-/
import Fl4Proofs.P3.XTopJointReply
import Fl4Proofs.P3.FrontEndExtra
import Fl4Proofs.P3.FrontEndLabel
import Fl4Proofs.P3.ScTcb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-! ## The checks -/

theorem tdx_reply_eq {S : Type} (st : machine.Store S) (s : S) (ct : obj.Tcb) (call : Bool) (v : U64) :
    tdx.reply st s ct call v = vspace.reply1 st s ct call v := rfl

theorem vmRightsOf_rw {r : U64} : vmRightsOf r = Fl4Spec.vmReadWrite ↔ r.val = 3 := by
  unfold vmRightsOf
  by_cases h3 : r.val = 3
  · simp [h3]
  · rw [if_neg h3]
    refine ⟨fun h => ?_, fun h => absurd h h3⟩
    have hw := congrArg (fun R : Fl4Spec.VMRights => Fl4Spec.Rights.allowWrite ∈ R) h
    split_ifs at hw <;> simp [Fl4Spec.vmReadOnly, Fl4Spec.vmReadWrite, Fl4Spec.vmKernelOnly] at hw

theorem rw3_iff {r : U64} : r = capability.VM_READ_WRITE ↔ r.val = 3 := by
  rw [u64_eq_iff]; simp [capability.VM_READ_WRITE]

/-- **FL4's `report_frame` is the spec's `tdxReportFrame`.** -/
theorem report_frame_cases (c : capability.Cap) :
    (tdx.report_frame c = ok none ∧ Fl4Spec.tdxReportFrame (absCap c) = none) ∨
    ∃ p : U64, tdx.report_frame c = ok (some p) ∧ Fl4Spec.tdxReportFrame (absCap c) = some p.bv := by
  cases c
  case Frame p sz r d m ept asid va =>
    cases sz <;> cases d <;>
      simp only [tdx.report_frame, Fl4Spec.tdxReportFrame, absCap, frameSizeOf, Bool.false_eq_true, ↓reduceIte]
    all_goals first | (left; constructor <;> first | rfl | trivial) | skip
    by_cases h : r.val = 3
    · right; exact ⟨p, by rw [if_pos (rw3_iff.2 h)], by rw [if_pos (vmRightsOf_rw.2 h)]⟩
    · left; exact ⟨by rw [if_neg (fun e => h (rw3_iff.1 e))], by rw [if_neg (fun e => h (vmRightsOf_rw.1 e))]⟩
  all_goals left; exact ⟨rfl, rfl⟩

section
variable {A : Type} (arI : machine.Arch A)

/-- **FL4's `quote_frame` is the spec's `tdxQuoteFrame` and the platform
record's `tdxDmaRam`** (given FL4's `dma_ram` answering the record, `TdxRel`'s
second part). -/
theorem quote_frame_cases {P : Fl4Spec.X64Platform}
    (hD : ∀ a (p n : U64), arI.dma_ram a p n = ok (P.tdxDmaRam p.bv n.val)) (a : A) (c : capability.Cap) :
    (tdx.quote_frame arI a c = ok none ∧
      ∀ p n, Fl4Spec.tdxQuoteFrame (absCap c) = some (p, n) → P.tdxDmaRam p n = false) ∨
    ∃ p n : U64, tdx.quote_frame arI a c = ok (some (p, n)) ∧ Fl4Spec.tdxQuoteFrame (absCap c) = some (p.bv, n.val) ∧
      P.tdxDmaRam p.bv n.val = true := by
  cases c
  case Frame p sz r d m ept asid va =>
    cases d
    · left
      cases sz <;> exact ⟨rfl, fun _ _ h => by simp [Fl4Spec.tdxQuoteFrame, absCap, frameSizeOf] at h⟩
    cases sz
    case Huge => left; exact ⟨rfl, fun _ _ h => by simp [Fl4Spec.tdxQuoteFrame, absCap, frameSizeOf] at h⟩
    all_goals
      simp only [tdx.quote_frame, Fl4Spec.tdxQuoteFrame, absCap, frameSizeOf, ↓reduceIte]
      by_cases h : r.val = 3
      · rw [if_pos (rw3_iff.2 h), if_pos (vmRightsOf_rw.2 h), hD]
        simp only [bind_ok]
        split
        · rename_i hb; right; exact ⟨p, _, rfl, rfl, hb⟩
        · rename_i hb; left
          refine ⟨rfl, fun p' n' e => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e; simpa using hb
      · left
        rw [if_neg (fun e => h (rw3_iff.1 e)), if_neg (fun e => h (vmRightsOf_rw.1 e))]
        exact ⟨rfl, fun _ _ e => by cases e⟩
  all_goals left; exact ⟨rfl, fun _ _ h => by simp [Fl4Spec.tdxQuoteFrame, absCap] at h⟩

end

theorem quote_len_ok_eq (l n : U64) : tdx.quote_len_ok l n = ok (decide (Fl4Spec.tdxQuoteLenOk l.bv n.val)) := by
  unfold tdx.quote_len_ok Fl4Spec.tdxQuoteLenOk
  have hP : tdx.PAGE.val = 4096 := by simp [tdx.PAGE]
  by_cases h1 : l ≥ tdx.PAGE
  · rw [if_pos h1]
    obtain ⟨m, hs, hmv, -⟩ := spec_exists (U64.sub_spec (x := tdx.PAGE) (y := 1#u64) (by rw [hP]; simp))
    have hm : m = 4095#u64 := UScalar.eq_of_val_eq (by rw [hmv, hP]; rfl)
    subst hm
    rw [hs]; simp only [bind_ok, lift]
    have hand : (l &&& 4095#u64).val = l.val % 4096 := by
      rw [UScalar.val_and]
      have : (4095#u64 : U64).val = 2 ^ 12 - 1 := rfl
      rw [this, Nat.and_two_pow_sub_one_eq_mod]
    have hl : 4096 ≤ l.val := by have := h1; rw [GE.ge, UScalar.le_equiv] at this; omega
    by_cases h2 : (l &&& 4095#u64) = 0#u64
    · rw [if_pos h2]
      have h2' : l.val % 4096 = 0 := by rw [← hand, h2]; rfl
      by_cases h3 : l ≤ n
      · rw [if_pos h3]; congr 1
        have h3' : l.val ≤ n.val := by rw [UScalar.le_equiv] at h3; exact h3
        simp only [Fl4Spec.unat]; simp [UScalar.bv_toNat, hl, h2', h3']
      · rw [if_neg h3]; congr 1
        have h3' : ¬ l.val ≤ n.val := by rw [UScalar.le_equiv] at h3; exact h3
        simp only [Fl4Spec.unat]; simp [UScalar.bv_toNat, h3']
    · rw [if_neg h2]; congr 1
      have h2' : ¬ l.val % 4096 = 0 := by rw [← hand]; intro e; exact h2 (UScalar.eq_of_val_eq (by rw [e]; rfl))
      simp only [Fl4Spec.unat]; simp [UScalar.bv_toNat, h2']
  · rw [if_neg h1]; congr 1
    have hl : ¬ 4096 ≤ l.val := by rw [GE.ge, UScalar.le_equiv] at h1; omega
    simp only [Fl4Spec.unat]; simp [UScalar.bv_toNat, hl]

/-! ## The spec's TDCALL -/

open Fl4Spec in
/-- **Every status word is an outcome of the spec's TDCALL**, the state kept. -/
theorem tdx_perform_out (inv : Fl4TdxInvocation) (σ : State Unit) (v : Data) :
    ([v], σ) ∈ (performTdxInvocation (Z := Unit) inv σ).1 := by
  have hstat : ∀ σ' : State Unit, ([v], σ') ∈ (tdxStatus (Z := Unit) σ').1 := fun σ' =>
    mem_bind_nd (x := (v, σ')) ⟨trivial, rfl⟩ rfl
  have hw : ∀ (b : Word) (n : Nat), ((), σ) ∈ (doMachineOp (Z := Unit) (tdxFrameWrite b n) σ).1 := by
    intro b n
    have h := dmo_ex (tdxFrameWrite b n) σ (r := ()) (ms' := σ.machineState)
      (mem_bind_nd (x := (σ.machineState.underlyingMemory, σ.machineState)) rfl
        (mem_bind_nd (x := (σ.machineState.underlyingMemory, σ.machineState)) ⟨fun _ _ => rfl, rfl⟩ rfl))
    exact h
  cases inv with
  | getReport f d => exact mem_bind_nd (hw f 0x1000) (hstat σ)
  | extendRtmr i d => exact hstat σ
  | getQuote f l => exact mem_bind_nd (hw f (unat l)) (hstat σ)

/-! ## The spec's decode -/

/-- The decode's read of the platform record. -/
theorem tdx_dec_gets {β : Type} (σ : Fl4Spec.State Unit) (k : Fl4Spec.X64Platform → Fl4Spec.SEMonad Unit β) :
    (Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.archState.x64Plat) >>= k).run σ =
      (k σ.archState.x64Plat).run σ :=
  run_bind_ok (s := σ) (a := σ.archState.x64Plat)
    (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.archState.x64Plat) (s := σ)
      (a := σ.archState.x64Plat) rfl) k

theorem tdx_unlessE_pos {σ ε : Type} {P : Prop} [Decidable P] (h : P) (m : Fl4Spec.NonDetE σ ε Unit) :
    Fl4Spec.NonDetE.unlessE P m = Fl4Spec.NonDetE.returnOk () := by
  unfold Fl4Spec.NonDetE.unlessE; rw [if_pos h]; rfl

theorem tdx_unlessE_neg {σ ε : Type} {P : Prop} [Decidable P] (h : ¬ P) (m : Fl4Spec.NonDetE σ ε Unit) :
    Fl4Spec.NonDetE.unlessE P m = m := by
  unfold Fl4Spec.NonDetE.unlessE; rw [if_neg h]

theorem lbl_rep_iff (lbl : U64) : lbl = fl4_abi.label.X86TdxControlGetReport ↔
    Fl4Spec.dataToNat lbl.bv = Fl4Spec.fl4TdxGetReportLabel := by
  rw [u64_eq_iff, dataToNat_bv]; simp [Fl4Spec.fl4TdxGetReportLabel]

theorem lbl_rtmr_iff (lbl : U64) : lbl = fl4_abi.label.X86TdxControlExtendRTMR ↔
    Fl4Spec.dataToNat lbl.bv = Fl4Spec.fl4TdxExtendRtmrLabel := by
  rw [u64_eq_iff, dataToNat_bv]; simp [Fl4Spec.fl4TdxExtendRtmrLabel]

theorem lbl_quote_iff (lbl : U64) : lbl = fl4_abi.label.X86TdxControlGetQuote ↔
    Fl4Spec.dataToNat lbl.bv = Fl4Spec.fl4TdxGetQuoteLabel := by
  rw [u64_eq_iff, dataToNat_bv]; simp [Fl4Spec.fl4TdxGetQuoteLabel]

/-! ## The success tail -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **The TDCALL's tail at `JAt`** (module docstring). -/
theorem tdxTail_jat [Fl4Proofs.P1.PlainStore st] (hAM : ARMask arI AR) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s)) (hC : CurRun σ)
    {ct : U64} (hcur : σ.curThread = ct.bv) (call : Bool) (v : U64) (a1 : A) (hop : TdxArchStep arI ar a1)
    (inv : Fl4Spec.Fl4TdxInvocation) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let s3 ← vspace.reply1 st s2 ct call v
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a1)) ⦃ res => res.1 = .Ok () ∧
      L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧ ∀ σ1,
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
        ∃ rr σy, (.ok rr, σy) ∈ ((Fl4Spec.fl4ArchPerformInvocation (Z := Unit) (.tdx inv)).run σ1).1 ∧
        ∃ w ∈ (specTail call ct.bv rr σy).1, RelTopM (L := L) res.2.1 w.2 ∧
          JAt (L := L) arI AR res.2.1 res.2.2 w.2 ⦄ := by
  have hJS : JStepHyps (L := L) arI AR Z.th := jStepHyps arI
  have hRep : JReplyHyp (L := L) arI AR Z.th := jReplyHyp arI Z.th
  have hX := J.xtop
  obtain ⟨htcb, x, hk⟩ := hX.curTcb hcur
  set σ1 := Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv with hσ1
  have hst : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) :=
    Notif.setThreadState_eq .restart hk
  have hts := WP.spec_and (set_thread_state_cpu (L := L) s ct sched.TS_RESTART)
    (spec_self (set_thread_state_cpu (L := L) s ct sched.TS_RESTART))
  refine WP.spec_bind hts ?_
  rintro s1 ⟨⟨hk1, hc1⟩, hr1⟩
  -- the restart and the TDCALL, as primitive steps
  have hstp : Steps (L := L) arI Z.th s ar σ s1 a1 σ1 :=
    (Steps.restart arI hcur hk htcb hr1 (by rw [hcur]; exact hst) hC).trans arI
      (Steps.arch arI (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hop))))))))
  obtain ⟨G', V', Ac', Lst', D', J', -⟩ := hstp _ (stepClosed_jat arI hAM hJS) Z H Cs Ac Lst D rfl J hZB
  -- the spec's TDCALL: the status word FL4's, the state kept
  have hmem : (.ok [v.bv], σ1) ∈ ((Fl4Spec.fl4ArchPerformInvocation (Z := Unit) (.tdx inv)).run σ1).1 :=
    mem_liftE (ε := Unit) (x := ([v.bv], σ1)) (tdx_perform_out inv σ1 v.bv)
  -- `reply1`
  set Z' : XSets := Z.mv G' V'
  have hXy := J'.xtop
  have hI : Vs.RInv (L := L) Z'.th Z'.P Z'.L4 Z'.L3 Z'.L2 Z'.L1 Z'.N Z'.T Z'.C Z'.E Z'.R Z'.B Z'.c AR Z'.G s1 a1 σ1 :=
    ⟨hXy.rel.2.1, hXy.rel.2.2.1, hXy.rel.2.2.2.2.1, hXy.rel.2.2.2.1, hXy.fin⟩
  have hkY : σ1.kheap ct.bv = some (.tcb { x with tcbState := .restart }) := by
    rw [hσ1, Notif.stsAct_kheap, Notif.updK_kheap, Function.update_self]
  have hcurY : ct.bv = σ1.curThread := by
    rw [hσ1, stsAct_cur]; exact hcur.symm
  have hR1 := Vs.reply1_invT s1 a1 σ1 hI ct htcb hcurY hkY rfl J'.kern.act call v
  refine WP.spec_bind (WP.spec_and hR1 (spec_self hR1)) ?_
  rintro s3 ⟨⟨hne, hks3, w, hw, hI3, hz3⟩, heq⟩
  rw [WP.spec_ok]
  refine ⟨rfl, hne, fun σ1' hσ1' => ?_⟩
  have e : σ1' = σ1 := by
    rw [hst] at hσ1'
    exact ((Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hσ1'))).2).symm
  subst e
  have hSch := hI3.2.2.2.2.1.1.1
  have hXT : XTop (L := L) AR s3 a1 w.2 := ⟨Z', hI3.2.2.2.2, ⟨hXy.rel.1, hI3.1, hI3.2.1,
    hI3.2.2.2.1, hI3.2.2.1, by rw [hks3]; exact hXy.rel.2.2.2.2.2.1, hXy.rel.2.2.2.2.2.2.mono hz3⟩,
    IpcRel.of hI3.2.2.2.2.1.1.2.2.1 hI3.2.2.2.2.1.1.2.1 (sched_sc hSch), hXy.esa.mono hks3 hz3⟩
  refine ⟨[v.bv], σ1, hmem, w, hw, hI3.relTop, ?_⟩
  exact hRep Z' H Cs Ac' Lst' D' s1 a1 σ1 rfl J' ct _ call v hcurY.symm hkY rfl s3 w heq hw hXT

set_option maxHeartbeats 16000000 in
/-- **The TDX control cap at `JAt`, every label** (module docstring). -/
theorem decode_invocation_tdxJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s))
    (lbl length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : ExtraRel Z.th (L.mem s) (exAt extra 0) (excaps.map Prod.fst))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot .TdxControl blk call don fp buf extra lbl.bv
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hC := J.curRun.run hni
  obtain ⟨htcb, x, hk⟩ := J.xtop.curTcb hcur
  have hst : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ =
      ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv)}, False) :=
    Notif.setThreadState_eq .restart hk
  -- the errors: the spec decode's one outcome
  have herr : ∀ (e : error.Exc) (e' : Fl4Spec.SyscallError), ErrRel e e' →
      (Fl4Spec.decodeTdxInvocation (Z := Unit) lbl.bv (args.map UScalar.bv) excaps).run σ =
        ({(.error e', σ)}, False) →
      TopPostRMX (L := L) (JAt (L := L) arI AR) σ blk call don
        (specDec fp lbl.bv (args.map UScalar.bv) ci sl .TdxControl excaps buffer) ct s (.Err e, s, ar) :=
    fun e e' hE hd => Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err (run_liftME_err hd), hE⟩, hJ0⟩
  -- a success: the TDCALL's tail
  have hsucc : ∀ (inv : Fl4Spec.Fl4TdxInvocation) (v : U64) (a1 : A), TdxArchStep arI ar a1 →
      (Fl4Spec.decodeTdxInvocation (Z := Unit) lbl.bv (args.map UScalar.bv) excaps).run σ =
        ({(.ok inv, σ)}, False) →
      (do
        let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
        let s3 ← vspace.reply1 st s2 ct call v
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a1)) ⦃ res =>
        TopPostRMX (L := L) (JAt (L := L) arI AR) σ blk call don
          (specDec fp lbl.bv (args.map UScalar.bv) ci sl .TdxControl excaps buffer) ct s res ⦄ := by
    intro inv v a1 hop hd
    refine WP.spec_mono (tdxTail_jat arI hARI.toMask J hZB hC hcur call v a1 hop inv) ?_
    rintro res ⟨hres, hne, hall⟩
    obtain ⟨rr, σy, hy, z, hz, hRT, hXT⟩ := hall _ hst
    exact Or.inr ⟨hres, hne, .invokeArchObject (.tdx inv), DecOut.of_eq (run_liftME_ok (run_liftME_ok hd)), _,
      by rw [hcur]; exact hst, rr, σy, hy, z, hz, hRT, hXT⟩
  refine Or.inr ?_
  unfold DecOKRMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  unfold tdx.decode
  rw [J.kern.tdx.1 ar]; simp only [bind_ok]
  by_cases hact : σ.archState.x64Plat.tdxActive = true
  swap
  · rw [if_neg hact]; simp only [error.illegal, bind_ok, WP.spec_ok]
    refine herr _ .illegalOperation (Or.inl trivial) ?_
    unfold Fl4Spec.decodeTdxInvocation; rw [tdx_dec_gets]
    rw [tdx_unlessE_neg hact]; exact Sched.run_throw_bind _ _ _
  rw [if_pos hact]
  have hlenB : (args.map UScalar.bv).length = length.val := by rw [List.length_map, hlen]
  by_cases h91 : lbl = fl4_abi.label.X86TdxControlGetReport
  · -- GetReport
    rw [if_pos h91]
    have hd := (lbl_rep_iff lbl).1 h91
    unfold tdx.get_report
    by_cases h8 : length < 8#u64
    · rw [if_pos h8]; simp only [error.truncated, bind_ok, WP.spec_ok]
      refine herr _ .truncatedMessage (Or.inl trivial) ?_
      unfold Fl4Spec.decodeTdxInvocation; rw [tdx_dec_gets]
      rw [tdx_unlessE_pos hact, retOk_bind, if_pos hd, whenE_pos (show (args.map UScalar.bv).length < 8 ∨ excaps = [] from
        Or.inl (by rw [hlenB]; scalar_tac))]
      exact Sched.run_throw_bind _ _ _
    rw [if_neg h8, exAt_idx0 extra]; simp only [bind_ok, obj.Slot.is_null]
    rcases hex with ⟨h0, hnil⟩ | ⟨hx0n, -, c0, a0, rest, hc0, hca0, -, hcs⟩
    · rw [h0]; simp only [decide_true, ↓reduceIte, error.truncated, bind_ok, WP.spec_ok]
      refine herr _ .truncatedMessage (Or.inl trivial) ?_
      unfold Fl4Spec.decodeTdxInvocation; rw [tdx_dec_gets]
      rw [tdx_unlessE_pos hact, retOk_bind, if_pos hd, whenE_pos (show (args.map UScalar.bv).length < 8 ∨ excaps = [] from
        Or.inr (List.map_eq_nil_iff.1 hnil))]
      exact Sched.run_throw_bind _ _ _
    simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [slot_cap_eq, hc0]; simp only [bind_ok]
    obtain ⟨e0, es, rfl, he0⟩ : ∃ e0 es, excaps = e0 :: es ∧ e0.1 = a0 := by
      cases excaps with
      | nil => simp at hcs
      | cons e0 es => exact ⟨e0, es, rfl, (List.cons.inj hcs).1⟩
    have hnot : ¬ ((args.map UScalar.bv).length < 8 ∨ e0 :: es = []) := by
      rintro (h | h)
      · rw [hlenB] at h; exact h8 (by scalar_tac)
      · cases h
    have hfr : (Fl4Spec.the (e0 :: es)[0]?).1 = absCap c0 := by rw [hca0.2, ← he0] <;> rfl
    rcases report_frame_cases c0 with ⟨hn, hsn⟩ | ⟨p, hp, hsp⟩
    · rw [hn]; simp only [bind_ok, error.invalid_cap, WP.spec_ok]
      refine herr _ (.invalidCapability 1) (Or.inr ⟨1#u64, rfl, rfl⟩) ?_
      unfold Fl4Spec.decodeTdxInvocation; rw [tdx_dec_gets]
      rw [tdx_unlessE_pos hact, retOk_bind, if_pos hd, whenE_neg hnot, retOk_bind, hfr, hsn] <;> rfl
    rw [hp]; simp only [bind_ok]
    obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, rest', rfl⟩ :
        ∃ y0 y1 y2 y3 y4 y5 y6 y7 rest', args = y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: rest' := by
      match args with
      | y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: rest' => exact ⟨y0, y1, y2, y3, y4, y5, y6, y7, rest', rfl⟩
      | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] =>
        exfalso; simp at hlen; scalar_tac
    simp only [hct, hargs 0#u64 y0 (by simp), hargs 1#u64 y1 (by simp), hargs 2#u64 y2 (by simp),
      hargs 3#u64 y3 (by simp), hargs 4#u64 y4 (by simp), hargs 5#u64 y5 (by simp), hargs 6#u64 y6 (by simp),
      hargs 7#u64 y7 (by simp), bind_ok]
    obtain ⟨⟨v, a1⟩, hv, -⟩ := spec_exists (hT.tdx_report ar p y0 y1 y2 y3 y4 y5 y6 y7)
    rw [hv]; simp only [bind_ok, tdx_reply_eq]
    refine hsucc (.getReport p.bv (List.take 8 ((y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: rest').map UScalar.bv))) v a1 (Or.inl ⟨_, _, _, _, _, _, _, _, _, _, hv⟩) ?_
    unfold Fl4Spec.decodeTdxInvocation; rw [tdx_dec_gets]
    rw [tdx_unlessE_pos hact, retOk_bind, if_pos hd, whenE_neg hnot, retOk_bind, hfr, hsp] <;> rfl
  rw [if_neg h91]
  have hn91 : ¬ Fl4Spec.dataToNat lbl.bv = Fl4Spec.fl4TdxGetReportLabel := fun e => h91 ((lbl_rep_iff lbl).2 e)
  by_cases h92 : lbl = fl4_abi.label.X86TdxControlExtendRTMR
  · -- ExtendRTMR
    rw [if_pos h92]
    have hd := (lbl_rtmr_iff lbl).1 h92
    unfold tdx.extend_rtmr
    by_cases h7 : length < 7#u64
    · rw [if_pos h7]; simp only [error.truncated, bind_ok, WP.spec_ok]
      refine herr _ .truncatedMessage (Or.inl trivial) ?_
      unfold Fl4Spec.decodeTdxInvocation; rw [tdx_dec_gets]
      rw [tdx_unlessE_pos hact, retOk_bind, if_neg hn91, if_pos hd,
        whenE_pos (show (args.map UScalar.bv).length < 7 by rw [hlenB]; scalar_tac)]
      exact Sched.run_throw_bind _ _ _
    rw [if_neg h7]
    have hnot : ¬ (args.map UScalar.bv).length < 7 := by rw [hlenB]; intro h; exact h7 (by scalar_tac)
    obtain ⟨y0, y1, y2, y3, y4, y5, y6, rest', rfl⟩ :
        ∃ y0 y1 y2 y3 y4 y5 y6 rest', args = y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest' := by
      match args with
      | y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest' => exact ⟨y0, y1, y2, y3, y4, y5, y6, rest', rfl⟩
      | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] =>
        exfalso; simp at hlen; scalar_tac
    simp only [hct, hargs 0#u64 y0 (by simp), bind_ok]
    have hR : tdx.RTMR_MAX = 3#u64 := by simp [tdx.RTMR_MAX]
    rw [hR]
    by_cases hi : y0 > 3#u64
    · rw [if_pos hi]; simp only [error.invalid_arg, bind_ok, WP.spec_ok]
      refine herr _ (.invalidArgument 0) (Or.inl (by simp [SysErrRel])) ?_
      unfold Fl4Spec.decodeTdxInvocation; rw [tdx_dec_gets]
      rw [tdx_unlessE_pos hact, retOk_bind, if_neg hn91, if_pos hd, whenE_neg hnot, retOk_bind]
      have h0 : Fl4Spec.the (List.map UScalar.bv (y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest'))[0]? = y0.bv := rfl
      simp only [h0]
      rw [whenE_pos (show Fl4Spec.unat (Fl4Spec.the (List.map UScalar.bv (y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest'))[0]?) > 3 by
        show y0.val > 3; scalar_tac)]
      exact Sched.run_throw_bind _ _ _
    rw [if_neg hi]
    simp only [hargs 1#u64 y1 (by simp), hargs 2#u64 y2 (by simp), hargs 3#u64 y3 (by simp),
      hargs 4#u64 y4 (by simp), hargs 5#u64 y5 (by simp), hargs 6#u64 y6 (by simp), bind_ok]
    obtain ⟨⟨v, a1⟩, hv, -⟩ := spec_exists (hT.tdx_extend_rtmr ar y0 y1 y2 y3 y4 y5 y6)
    rw [hv]; simp only [bind_ok, tdx_reply_eq]
    refine hsucc (.extendRtmr y0.bv (List.take 6 (List.drop 1 ((y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest').map UScalar.bv)))) v a1 (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, _, hv⟩)) ?_
    unfold Fl4Spec.decodeTdxInvocation; rw [tdx_dec_gets]
    rw [tdx_unlessE_pos hact, retOk_bind, if_neg hn91, if_pos hd, whenE_neg hnot, retOk_bind]
    have h0 : Fl4Spec.the (List.map UScalar.bv (y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest'))[0]? = y0.bv := rfl
    simp only [h0]
    rw [whenE_neg (show ¬ Fl4Spec.unat (Fl4Spec.the (List.map UScalar.bv (y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest'))[0]?) > 3 by
      show ¬ y0.val > 3; scalar_tac), retOk_bind]; rfl
  rw [if_neg h92]
  have hn92 : ¬ Fl4Spec.dataToNat lbl.bv = Fl4Spec.fl4TdxExtendRtmrLabel := fun e => h92 ((lbl_rtmr_iff lbl).2 e)
  by_cases h93 : lbl = fl4_abi.label.X86TdxControlGetQuote
  swap
  · rw [if_neg h93]; simp only [error.illegal, bind_ok, WP.spec_ok]
    refine herr _ .illegalOperation (Or.inl trivial) ?_
    unfold Fl4Spec.decodeTdxInvocation; rw [tdx_dec_gets]
    rw [tdx_unlessE_pos hact, retOk_bind, if_neg hn91, if_neg hn92,
      if_neg (fun e => h93 ((lbl_quote_iff lbl).2 e))]; rfl
  -- GetQuote
  rw [if_pos h93]
  have hd := (lbl_quote_iff lbl).1 h93
  unfold tdx.get_quote
  by_cases h1 : length < 1#u64
  · rw [if_pos h1]; simp only [error.truncated, bind_ok, WP.spec_ok]
    refine herr _ .truncatedMessage (Or.inl trivial) ?_
    unfold Fl4Spec.decodeTdxInvocation; rw [tdx_dec_gets]
    rw [tdx_unlessE_pos hact, retOk_bind, if_neg hn91, if_neg hn92, if_pos hd,
      whenE_pos (show (args.map UScalar.bv).length < 1 ∨ excaps = [] from Or.inl (by rw [hlenB]; scalar_tac))]
    exact Sched.run_throw_bind _ _ _
  rw [if_neg h1, exAt_idx0 extra]; simp only [bind_ok, obj.Slot.is_null]
  rcases hex with ⟨h0, hnil⟩ | ⟨hx0n, -, c0, a0, rest, hc0, hca0, -, hcs⟩
  · rw [h0]; simp only [decide_true, ↓reduceIte, error.truncated, bind_ok, WP.spec_ok]
    refine herr _ .truncatedMessage (Or.inl trivial) ?_
    unfold Fl4Spec.decodeTdxInvocation; rw [tdx_dec_gets]
    rw [tdx_unlessE_pos hact, retOk_bind, if_neg hn91, if_neg hn92, if_pos hd,
      whenE_pos (show (args.map UScalar.bv).length < 1 ∨ excaps = [] from Or.inr (List.map_eq_nil_iff.1 hnil))]
    exact Sched.run_throw_bind _ _ _
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [slot_cap_eq, hc0]; simp only [bind_ok]
  obtain ⟨e0, es, rfl, he0⟩ : ∃ e0 es, excaps = e0 :: es ∧ e0.1 = a0 := by
    cases excaps with
    | nil => simp at hcs
    | cons e0 es => exact ⟨e0, es, rfl, (List.cons.inj hcs).1⟩
  have hnot : ¬ ((args.map UScalar.bv).length < 1 ∨ e0 :: es = []) := by
    rintro (h | h)
    · rw [hlenB] at h; exact h1 (by scalar_tac)
    · cases h
  have hfr : (Fl4Spec.the (e0 :: es)[0]?).1 = absCap c0 := by rw [hca0.2, ← he0] <;> rfl
  rcases quote_frame_cases arI J.kern.tdx.2 ar c0 with ⟨hn, hsn⟩ | ⟨p, n, hp, hsp, hdm⟩
  · rw [hn]; simp only [bind_ok, error.invalid_cap, WP.spec_ok]
    refine herr _ (.invalidCapability 1) (Or.inr ⟨1#u64, rfl, rfl⟩) ?_
    unfold Fl4Spec.decodeTdxInvocation; rw [tdx_dec_gets]
    rw [tdx_unlessE_pos hact, retOk_bind, if_neg hn91, if_neg hn92, if_pos hd, whenE_neg hnot, retOk_bind, hfr]
    cases hq : Fl4Spec.tdxQuoteFrame (absCap c0) with
    | none => rfl
    | some pb =>
      obtain ⟨p', n'⟩ := pb
      dsimp only
      rw [tdx_unlessE_neg (show ¬ (σ.archState.x64Plat.tdxDmaRam p' n' = true) by rw [hsn p' n' hq]; simp)]
      exact Sched.run_throw_bind _ _ _
  rw [hp]; simp only [bind_ok]
  obtain ⟨y0, rest', rfl⟩ : ∃ y0 rest', args = y0 :: rest' := by
    match args with
    | y0 :: rest' => exact ⟨y0, rest', rfl⟩
    | [] => exfalso; simp at hlen; scalar_tac
  simp only [hct, hargs 0#u64 y0 (by simp), bind_ok, quote_len_ok_eq]
  have hsq : (Fl4Spec.decodeTdxInvocation (Z := Unit) lbl.bv ((y0 :: rest').map UScalar.bv) (e0 :: es)).run σ =
      (Fl4Spec.NonDetE.unlessE (Fl4Spec.tdxQuoteLenOk y0.bv n.val)
          (Fl4Spec.NonDetE.throwError (.invalidArgument 0)) >>= fun _ =>
        (Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TdxInvocation.getQuote p.bv y0.bv) :
          Fl4Spec.SEMonad Unit Fl4Spec.Fl4TdxInvocation)).run σ := by
    unfold Fl4Spec.decodeTdxInvocation; rw [tdx_dec_gets]
    rw [tdx_unlessE_pos hact, retOk_bind, if_neg hn91, if_neg hn92, if_pos hd, whenE_neg hnot, retOk_bind, hfr,
      hsp]
    dsimp only
    rw [tdx_unlessE_pos hdm, retOk_bind]
    rfl
  show (if decide (Fl4Spec.tdxQuoteLenOk y0.bv n.val) = true then _ else _) ⦃ _ ⦄
  by_cases hl : Fl4Spec.tdxQuoteLenOk y0.bv n.val
  · rw [decide_eq_true hl]; simp only [↓reduceIte]
    obtain ⟨⟨v, a1⟩, hv, -⟩ := spec_exists (hT.tdx_get_quote ar p y0)
    rw [hv]; simp only [bind_ok, tdx_reply_eq]
    refine hsucc (.getQuote p.bv y0.bv) v a1 (Or.inr (Or.inr ⟨_, _, _, hv⟩)) ?_
    rw [hsq, tdx_unlessE_pos hl, retOk_bind]; rfl
  · rw [decide_eq_false hl]; simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_arg, bind_ok, WP.spec_ok]
    refine herr _ (.invalidArgument 0) (Or.inl (by simp [SysErrRel])) ?_
    rw [hsq, tdx_unlessE_neg hl]
    exact Sched.run_throw_bind _ _ _

end

end

end Fl4Proofs.P3
