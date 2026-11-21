/-
P3 (DESIGN.md §9), invariant line G4 (g4h, KENTRY-PLAN g4h; g4d's handoff):
**`JDecMRL` narrowed: the IO port, IRQ handler and IRQ control caps' decodes
with `MR` at the chosen outcome proved.**

* `XCapP.mrG` (`TopPostDMXP.mrG`, `TopPostRMX.mrG`): `XCapP.mr` for a decode
  that moves the machine fields `MR` reads by a fixed `f`: FL4's decode ends
  at `MR` of `f ms` when it succeeds (of `ms` when it fails), every perform
  outcome of every decoded invocation has the four fields of `f` at the
  restart's machine state (`MachF.mF`).
* IO port (`z = 0`): FL4 by `MKD.decode_ioport` (MachKeepG4h, under the new
  arch-only [P] `MRKeepIo`: `port_in` / `port_out` keep `MR`), spec by
  `MachT.dec_quiet` (an IO port cap is an arch cap, its invocation `QInv`).
* IRQ handler: FL4 by `MKD.decode_irq_handler_mr` (Ack: the one
  `mask_irq irq false` moves `MR` by `MachPlat.mask`; Set / Clear: arch
  kept); spec: at the Ack label the decode yields `aCKIrq irq`
  (`dec_irqH_ack`), whose perform is `maskInterrupt false irq`
  (`perf_ack_ms`); at the other labels Set / Clear (`dec_irqH_nack`), which
  keep `msFT` (`perf_irqH_nack`).
* IRQ control: `decode_invocation_irq_controlXSM` (XTopCaps' `XS` with
  IrqCtlMR's `irq_control_decode_refinesM`: `MR` at the outcome, FL4's
  `mask_irq` against the spec's `setIrqState Signal`; the IOAPIC labels under
  the new arch-only [P] `MRKeepIoapic`).
* `LoudR` (Thread, Untyped) and **`JDecMRL2`** [W]: `JDecMRL`
  asked only for `LoudR` caps. `jDecMRL_of`: at a dispatch state with the
  invocation's `JEntryGlobM` / `JEntryAt` / `JPreDecHypM` (what
  `KDispHyps13PU` gives), `JDecMRL2 → JDecMRL`.
* Copies with `hDL : JDecMRL2` (and `hIo`, `hIoa`): `dispatch_all13PUNM2`,
  `kernel_entryJ13PUGMD2`, NEW TOPS **`kernel_entryJ39`** (= `kernel_entryJ38`
  with `JDecMRL2` for `JDecMRL`, plus `hIo` / `hIoa` [P]) and
  **`kernel_entry_reachMD2`**.
-/
import Fl4Proofs.P3.XTopJointKEntry38
import Fl4Proofs.P3.MachKeepG4h
import Fl4Proofs.P3.IrqCtlMR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## The spec side of the IRQ handler cap -/

/-- The machine state with line `w` unmasked (`MachPlat.mask`'s update). -/
def unmaskMs (ms : Fl4Spec.MachineState) (w : U64) : Fl4Spec.MachineState :=
  { ms with irqMasks := Function.update ms.irqMasks (w.bv.setWidth 8) false }


section
open Fl4Spec

theorem dec_irqH_ack (fp : Bool) (lbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (i : Irq)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (h : genInvocationType lbl = .irqAckIRQ) :
    NoPre.OkP (fun inv => inv = .invokeIRQHandler (.aCKIrq i))
      (fl4DecodeInvocation (Z := Unit) fp lbl args ci sl (.irqHandlerCap i) ex buf) := by
  simp only [fl4DecodeInvocation]
  refine NoPre.okP_liftME' (Q := fun j => j = .aCKIrq i) ?_ fun x hx => by rw [hx]
  simp only [decodeIrqHandlerInvocation, if_pos h, NonDetE.returnOk]
  exact NoPre.okP_pure rfl

theorem dec_irqH_nack (fp : Bool) (lbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (i : Irq)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (h : genInvocationType lbl ≠ .irqAckIRQ) :
    NoPre.OkP (fun inv => ∃ j, inv = .invokeIRQHandler j ∧ ∀ k, j ≠ .aCKIrq k)
      (fl4DecodeInvocation (Z := Unit) fp lbl args ci sl (.irqHandlerCap i) ex buf) := by
  simp only [fl4DecodeInvocation]
  refine NoPre.okP_liftME' (Q := fun j => ∀ k, j ≠ .aCKIrq k) ?_ fun x hx => ⟨x, rfl, hx⟩
  unfold decodeIrqHandlerInvocation
  simp only [if_neg h, NonDetE.returnOk, NonDetE.throwError]
  repeat' (first
    | exact NoPre.okP_throw
    | exact NoPre.okP_pure (fun k e => by cases e)
    | split)

/-- The Ack invocation's perform unmasks the line. -/
theorem perf_ack_ms (b c d : Bool) (i : Irq) (σ1 : State Unit) {y : Except Unit (List Data) × State Unit}
    (hy : y ∈ ((fl4PerformInvocation (Z := Unit) b c d (.invokeIRQHandler (.aCKIrq i))).run σ1).1) :
    y.2.machineState = { σ1.machineState with irqMasks := Function.update σ1.machineState.irqMasks i false } := by
  have h1 : invokeIrqHandler (Z := Unit) (.aCKIrq i) σ1 = ({((), { σ1 with machineState :=
      { σ1.machineState with irqMasks := Function.update σ1.machineState.irqMasks i false } })}, False) := by
    show doMachineOp (maskInterrupt false i) σ1 = _
    exact doMachineOp_single rfl
  have h2 := run_liftE' (ε := Unit) h1
  have h3 : (fl4PerformInvocation (Z := Unit) b c d (.invokeIRQHandler (.aCKIrq i))).run σ1 =
      ({(.ok [], { σ1 with machineState :=
        { σ1.machineState with irqMasks := Function.update σ1.machineState.irqMasks i false } })}, False) := by
    rw [show fl4PerformInvocation (Z := Unit) b c d (.invokeIRQHandler (.aCKIrq i)) =
      (NonDetE.liftE (invokeIrqHandler (.aCKIrq i)) >>= fun _ => NonDetE.returnOk []) from rfl]
    rw [dec_run_bind h2]; rfl
  rw [h3] at hy
  rw [Set.mem_singleton_iff.1 hy]

/-- The Set / Clear invocations keep `msFT`. -/
theorem perf_irqH_nack (b c d : Bool) (j : IrqHandlerInvocation) (hj : ∀ k, j ≠ .aCKIrq k) :
    MachT.MTKE (fl4PerformInvocation (Z := Unit) b c d (.invokeIRQHandler j)) := by
  cases j with
  | aCKIrq k => exact absurd rfl (hj k)
  | _ => unfold fl4PerformInvocation invokeIrqHandler; mtk_auto

end

/-! ## `XCapP.mr` for a decode that moves `MR`'s fields by `f` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

theorem mF_mr (hM : MachPlat arI MR) {a : A} {ms ms' : Fl4Spec.MachineState} (hR : MR a ms)
    (h : MachF.mF ms' = MachF.mF ms) : MR a ms' := by
  simp only [MachF.mF, Prod.mk.injEq] at h
  exact hM.frame a _ _ hR h.1 h.2.1 h.2.2.1 h.2.2.2

/-- The perform outcomes' four fields are `f`'s at the decode state. -/
def PerfF (f : Fl4Spec.MachineState → Fl4Spec.MachineState) (σ : Fl4Spec.State Unit) (blk call don : Bool)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation) : Prop :=
  ∀ inv, DecOut m σ inv → ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
    ∀ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1, (∃ l, y.1 = .ok l) →
      MachF.mF y.2.machineState = MachF.mF (f σ.machineState)

theorem TopPostDMXP.mrG (hM : MachPlat arI MR) {X XP : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit}
    {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S}
    {res : core.result.Result Unit error.Exc × S × A} {f : Fl4Spec.MachineState → Fl4Spec.MachineState}
    (h : TopPostDMXP (L := L) X XP σ blk call don m s res)
    (hR : MR res.2.2 (if res.1 = .Ok () then f σ.machineState else σ.machineState))
    (hq : PerfF f σ blk call don m) :
    TopPostDMXP (L := L) (fun s a σ => X s a σ ∧ MR a σ.machineState) XP σ blk call don m s res := by
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨inv, h1, σ1, h2, y, hy, h3, h4⟩
  · refine Or.inl ⟨e, h1, h2, h3, ?_⟩
    dsimp only at h4 ⊢
    rw [h1] at hR
    rw [if_neg (by simp)] at hR
    by_cases hp : res.1 = .Err .Preempted
    · rw [if_pos hp] at h4 ⊢; exact h4
    · rw [if_neg hp] at h4 ⊢; exact ⟨h4, hR⟩
  · refine Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, ?_⟩
    dsimp only at h4 ⊢
    by_cases hp : res.1 = .Err .Preempted
    · rw [if_pos hp] at h4 ⊢; exact h4
    · rw [if_neg hp] at h4 ⊢
      obtain ⟨th', G', hc, -⟩ := h3
      have hc' : res.1 = .Ok () ∧ y.1 = .ok [] := hc.resolve_right fun ⟨e, _⟩ => hp e
      rw [if_pos hc'.1] at hR
      exact ⟨h4, mF_mr hM hR (hq inv h1 σ1 h2 y hy ⟨_, hc'.2⟩)⟩

theorem TopPostRMX.mrG (hM : MachPlat arI MR) {X : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit}
    {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {ct : U64} {s : S}
    {res : core.result.Result Unit error.Exc × S × A} {f : Fl4Spec.MachineState → Fl4Spec.MachineState}
    (h : TopPostRMX (L := L) X σ blk call don m ct s res)
    (hR : MR res.2.2 (if res.1 = .Ok () then f σ.machineState else σ.machineState))
    (hq : PerfF f σ blk call don m) :
    TopPostRMX (L := L) (fun s a σ => X s a σ ∧ MR a σ.machineState) σ blk call don m ct s res := by
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7⟩
  · rw [h1, if_neg (by simp)] at hR
    exact Or.inl ⟨e, h1, h2, h3, h4, hR⟩
  · rw [if_pos h1] at hR
    refine Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7, mF_mr hM hR ?_⟩
    have e1 := congrArg Prod.fst (MachT.mtk_specTailG call ct.bv rr σy z hz)
    simp only [MachT.msFT, MachF.msF, Prod.mk.injEq] at e1
    have e2 := hq inv h3 σ1 h4 _ h5 ⟨rr, rfl⟩
    rw [← e2]
    simp only [MachF.mF, e1.1, e1.2.1, e1.2.2.1, e1.2.2.2.1]

/-- **`XCapP` with `MR`, the fields moved by `f`** (module docstring). -/
theorem XCapP.mrG (hM : MachPlat arI MR) {X XP : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64} {f : Fl4Spec.MachineState → Fl4Spec.MachineState}
    (h : XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hW : syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ r =>
      MR r.2.2 (if r.1 = .Ok () then f σ.machineState else σ.machineState) ⦄)
    (hq : PerfF f σ blk call don (specDec fp slbl args ci sl c excaps buffer)) :
    XCapP (L := L) arI (fun s a σ => X s a σ ∧ MR a σ.machineState) XP s ar σ lbl length slot c blk call don fp buf
      extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · exact Or.inl (WP.spec_mono (WP.spec_and h hW) fun _ ⟨h1, h2⟩ => h1.mrG hM h2 hq)
  · exact Or.inr (WP.spec_mono (WP.spec_and h hW) fun _ ⟨h1, h2⟩ => h1.mrG hM h2 hq)

theorem irqAck_val : fl4_abi.label.IRQAckIRQ.val = 34 := by simp [fl4_abi.label.IRQAckIRQ]

/-- **`PerfF` of the IRQ handler cap** (module docstring). -/
theorem perfF_irqH (irq : U64) (hirq : irq.val < 128) (lbl : U64) (σ : Fl4Spec.State Unit) (blk call don fp : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    PerfF (fun ms => if lbl = fl4_abi.label.IRQAckIRQ then unmaskMs ms irq else ms) σ blk call don
      (specDec fp lbl.bv args ci sl (.IrqHandler irq) excaps buffer) := by
  intro inv hd σ1 hst y hy _
  have e1 := congrArg Prod.fst (MachT.mtk_setThreadState' _ _ σ ((), σ1) (mem_of_single hst))
  simp only [MachT.msFT, MachF.msF, Prod.mk.injEq] at e1
  by_cases hl : lbl = fl4_abi.label.IRQAckIRQ
  · have hg : Fl4Spec.genInvocationType lbl.bv = .irqAckIRQ := by
      have h34 : lbl.val = 34 := by rw [hl, irqAck_val]
      rw [irqH_in lbl (by omega) (by omega)]; unfold irqHLabelOf; rw [if_pos h34]
    have hinv := dec_irqH_ack fp lbl.bv args ci sl (BitVec.ofNat 8 irq.val) excaps buffer hg σ _ hd.1 inv rfl
    subst hinv
    rw [perf_ack_ms blk call don _ σ1 hy]
    simp only [if_pos hl]
    have hw : (irq.bv.setWidth 8 : BitVec 8) = BitVec.ofNat 8 irq.val := by
      apply BitVec.eq_of_toNat_eq; simp
    simp only [MachF.mF, unmaskMs, e1.1, e1.2.1, e1.2.2.1, e1.2.2.2.1, hw]
  · have hg : Fl4Spec.genInvocationType lbl.bv ≠ .irqAckIRQ := by
      have h34 : lbl.val ≠ 34 := fun e => hl (UScalar.eq_of_val_eq (by rw [e, irqAck_val]))
      by_cases hr : 34 ≤ lbl.val ∧ lbl.val ≤ 36
      · rw [irqH_in lbl hr.1 hr.2]; unfold irqHLabelOf; rw [if_neg h34]; split_ifs <;> decide
      · intro e; exact (irqH_out lbl hr).1 (by rw [e]; decide)
    obtain ⟨j, rfl, hj⟩ := dec_irqH_nack fp lbl.bv args ci sl (BitVec.ofNat 8 irq.val) excaps buffer hg σ _ hd.1 inv rfl
    have e2 := congrArg Prod.fst (perf_irqH_nack blk call don j hj σ1 y hy)
    simp only [MachT.msFT, MachF.msF, Prod.mk.injEq] at e2
    simp only [if_neg hl]
    simp only [MachF.mF, e2.1, e2.2.1, e2.2.2.1, e2.2.2.2.1, e1.1, e1.2.1, e1.2.2.1, e1.2.2.2.1]

end

/-! ## The IRQ control cap with `MR` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`decode_invocation_irq_controlXS` with `MR`** (IrqCtlMR's
`irq_control_decode_refinesM`). -/
theorem decode_invocation_irq_controlXSM {AR : A → Fl4Spec.Cr3 → Prop}
    (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hL : IntLayout th (L.ksb s))
    (hHA : HandlersActive (L.mem s) (L.ksb s) G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : IrqCLabel lbl slbl)
    (hrm : decide (lbl.val = 72) = Fl4Spec.isFl4RemappedLabel slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (nA : U64) (hnum : arI.num_ioapics ar = ok nA) (hnA : nA.bv = σ.archState.x64NumIoapics)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (hAR : ArchIrqRel arI ar σ) {Z : XSets} (hth : Z.th = th) (hG : Z.G = G) (hX0 : XTopAt (L := L) AR Z s ar σ)
    (hC : CurRun σ) (X : S → A → Fl4Spec.State Unit → Prop) (hXa : X s ar σ)
    (hXS : ∀ s' a' σ', Steps (L := L) arI th s ar σ s' a' σ' → X s' a' σ')
    (hXX : ∀ s a σ, X s a σ → XTop (L := L) AR s a σ) (blk call don fp : Bool) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) (hMk : MaskMR arI MR) (hfr : FrameMR MR) (hR0 : MR ar σ.machineState)
    (hIoa : MRKeepIoapic arI MR) :
    XCap (L := L) arI (fun s a σ => X s a σ ∧ MR a σ.machineState) s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IrqControl blk call don fp buf
      extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct := by
  subst hth hG
  have hP := hX0.rel.1
  have hCR := hX0.rel.2.1
  have hFI := hX0.rel.2.2.1
  have hFR := hX0.rel.2.2.2.2.1
  have hIR := hX0.fin.1.1.2.2.2.1
  have htcb : Z.th ct = some .tcb := by
    obtain ⟨t, htb, hth, -⟩ := hX0.fin.2.2.2.2
    rwa [← P1.eq_of_bv (htb.trans hcur)]
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have e : specDec fp slbl (args.map UScalar.bv) ci (ps.bv, idxs) .IrqControl excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeIRQControl
        (Fl4Spec.decodeFl4IrqControl (decide (lbl.val = 72)) slbl (args.map UScalar.bv) (ps.bv, idxs)
          (excaps.map Prod.fst)) := by
    rw [hrm]; rfl
  rw [e]
  refine WP.spec_mono (irq_control_decode_refinesM arI Z.th hP s ar σ Z.G hCR hL hIR hHA hFI hFR lbl slbl hlbl length buf ct
    hct args hlen hargs hcur htcb hact hact2 extra x0 hx0 _ hex hps hls hsrcC nA hnum hnA hmask hAR hMk hfr hR0 hIoa) ?_
  rintro ⟨r0, s', a'⟩ hq
  cases r0 with
  | Err e =>
    obtain ⟨rfl, ⟨e', h1, h2⟩, rfl⟩ := hq
    exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, h2⟩, hXa, hR0⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', hx, hmr, -, -, -, -, -, -, hstp⟩ := hq
    have hXp := hXS _ _ _ (hstp hC)
    obtain ⟨Z', hZ'⟩ := hXX _ _ _ hXp
    exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
      mem_bindE_ok hx (Set.mem_singleton _), ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩, hZ'.rel.1, hZ'.rel.2.1,
        hZ'.rel.2.2.1, hZ'.rel.2.2.2.1, hZ'.rel.2.2.2.2.1⟩, hXp, hmr⟩

end

/-! ## `JDecMRL` narrowed -/

/-- **The cap kinds whose decode with `MR` is still asked** (module docstring). -/
def LoudR : capability.Cap → Prop
  | .Thread _ => True
  | .Untyped .. => True
  | _ => False

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[W] `JDecMRL` for the `LoudR` caps** (Thread, Untyped; module docstring):
the IO port, IRQ handler and IRQ control caps are proved (`jDecMRL_of`).
l4v: `invoke_tcb_corres`, `invoke_untyped_corres` with the machine state
shared (`preemption_point` in the installs' and the reset's loops). -/
def JDecMRL2 (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  MR ar σ.machineState → ValidMachineTime σ → ValidIrqMasks σ →
  ∀ (lbl length : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64), length.val = argsU.length →
    (∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x) →
    msg.lookup_ipc_buffer st s false ct = ok buf → argsU.length ≤ 120 →
    ∀ (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
    ∀ (c : capability.Cap), capAt (L.mem s) (cslotAddr sl) = ok c → (LoudR c ∧ Vs.NativeCap c) →
    ∀ (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef),
    ExtraOK Z.th (L.mem s) extra excaps → ExtraNamed Z.th (L.mem s) extra → lbl.bv = slbl →
    ArgRel (st := st) s σ ct buf buffer 5 →
    JPathM (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c →
    XCapP (L := L) arI (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) c
      blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`JDecMRL` from `JDecMRL2`** at a dispatch state (module docstring): the
IO port cap by `XCapP.mr` (FL4 `MKD.decode_ioport` under `MRKeepIo`, spec
`dec_quiet`), the IRQ handler cap by `XCapP.mrG` (`MKD.decode_irq_handler_mr`,
`perfF_irqH`), the IRQ control cap by `decode_invocation_irq_controlXSM`,
the rest by `JDecMRL2`. -/
theorem jDecMRL_of [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hNs : NativeScope σ) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR)
    (hIoa : MRKeepIoapic arI MR) (hDL : JDecMRL2 (L := L) arI AR MR Z H Cs D s ar σ ct) :
    JDecMRL (L := L) arI AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc hcl
    excaps buffer hXO hXN hLb hA5 hN
  obtain ⟨hlo, hNat⟩ := hcl
  have hA := hG.tot
  have hX0 := decOK_JMU arI s ar σ J hG hE ct hct lbl length blk call don fp buf extra slbl argsU hlen hargs
    hbuf hl ci sl hsl c hc excaps buffer hXO hXN hLb hA5 hN hPD hR hVT hVI hNs
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨p', hp, hth⟩ := hsl; exact ⟨p', hp, Or.inl hth⟩
  cases c <;> simp only [LoudF] at hlo
  case IoPort first last z =>
    exact XCapP.mr hM hX0 (MKD.decode_ioport L.total hA hKD hIo hR)
      (fun inv hd => MachT.dec_quiet fp slbl _ ci sl _ excaps buffer (by simp [absCap, MachT.QuietS]) σ _ hd.1 inv rfl)
  case IrqHandler irq =>
    have hirq : irq.val < 128 := (slot_cap_wf J.xtop hAs (capV_of_capAt hc)).1
    subst hLb
    exact XCapP.mrG (f := fun ms => if lbl = fl4_abi.label.IRQAckIRQ then unmaskMs ms irq else ms) hM hX0 (MKD.decode_irq_handler_mr L.total hA hKD (hM.mask ar irq false _ hR (by omega)) hR)
      (perfF_irqH irq hirq lbl σ blk call don fp _ ci sl excaps buffer)
  case IrqControl =>
    subst hLb
    have hPl : Placed Z.th := J.xtop.rel.1
    have hex := ExtraOK.rel1 hPl hXO
    obtain ⟨nA, hnum, hnA⟩ := hE.ioapics
    obtain ⟨sl1, idxs⟩ := sl
    obtain ⟨p0, hp0, hth0⟩ := hsl
    try simp only at hp0 hth0
    subst hp0
    obtain ⟨hcur, -⟩ := J.curEq hct
    exact (decode_invocation_irq_controlXSM arI Z.th s ar σ Z.G J.intL hE.handlers lbl lbl.bv (irqControl_label lbl)
      (irqControl_remap lbl) length buf ct hct argsU hlen hargs hcur J.kern.act J.act2 extra _ (exAt_idx0 extra) excaps
      hex hth0 rfl hc nA hnum hnA (maskIrq_total arI hA) hE.archIrq rfl rfl J.xtop (J.curRun.run hE.ni) _
      ⟨Z, H, Cs, Ac, Lst, D, J⟩
      (fun _ _ _ h => Steps.jat arI hG.ari.toMask (jStepHyps arI) h rfl J (J.zNoBlk hE.sg)) (fun _ _ _ h => JAt.xtop arI h)
      blk call don fp ci buffer hM.mask (fun a ms ms' h e => mF_mr hM h e) hR hIoa).toPN arI (specDec_noPreK (by trivial))
  all_goals
    exact hDL hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc
      ⟨trivial, hNat⟩ excaps buffer hXO hXN hLb hA5 hN

end


/-! ## Every native dispatch with `MR` at the chosen outcome -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`dispatch_all13PUN` with `MR` at the chosen outcome** (`DispPostRM`;
module docstring): the invoking and mid syscalls by the `…M` layer, the
receiving ones and `Yield` by g4b's keeps (`JDispMR.of_keep`). -/
theorem dispatch_all13PUNM2 [Fl4Proofs.P1.PlainStore st] (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c) (hK : KDispHyps13PU (L := L) arI AR MR Z H Cs D s a σ n c)
    (hDL : ∀ ct, sched.cur_thread st s = ok ct → JDecMRL2 (L := L) arI AR MR Z H Cs D s a σ ct)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.dispatch_syscall st arI s a n ⦃ r =>
      DispPostRM (L := L) arI AR MR (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have hct := cur_thread_eq (L := L) s
  have hD := dispatch_all13PUN s a σ J hni n c hn hK hR hVI hN hARI hA hnd hM hKD.toK hPA hIA hmrt hmax htu
  rcases hn with ⟨call, bl, don, hi, rfl⟩ | ⟨bl, cr, hr, rfl⟩ | ⟨rfl, rfl⟩ | hm
  · obtain ⟨hG, hE, hP, hPD⟩ := hK.inv _ call bl don hct hi
    exact dispatch_invokeJAllMUNM s a σ J _ hct n call bl don hi hG hE hP hPD
      (jDecMRL_of arI s a σ J hG hE _ hct hPD hN hM hKD hIo hIoa (hDL _ hct)) hR hK.vmt hVI hN hARI
      hA hnd hM hKD hPA hIA hmrt
  · refine WP.spec_mono (WP.spec_and hD (JDispMR.of_keep (L := L) (AR := AR) hM
      (fun hR => dispatch_recv_mr hKD hA hr hR) ?_ hR)) fun _ ⟨h1, h2⟩ => h2 h1
    rw [fl4HandleSyscall_recv true bl cr]
    intro y hy
    obtain ⟨h1, h2⟩ := MachT.mtk_withoutPreemption (MachT.mtk_handleRecvG bl cr) y hy
    exact ⟨congrArg Prod.fst h1, h2⟩
  · refine WP.spec_mono (WP.spec_and hD (JDispMR.of_keep (L := L) (AR := AR) hM
      (fun hR => dispatch_yield_mr hKD hA hR) ?_ hR)) fun _ ⟨h1, h2⟩ => h2 h1
    have e : Fl4Spec.fl4HandleSyscall (Z := Unit) true .sysYield = Fl4Spec.withoutPreemption Fl4Spec.handleYield := rfl
    rw [e]
    intro y hy
    obtain ⟨h1, h2⟩ := MachT.mtk_withoutPreemption MachT.mtk_handleYieldG y hy
    exact ⟨congrArg Prod.fst h1, h2⟩
  · obtain ⟨rg, sr, cr, hm'⟩ := midSysR_of hm
    obtain ⟨hG, hE, hP, hW, hV, hS6, hPD⟩ := hK.mid _ rg sr cr hct hm'
    obtain ⟨hs, hq⟩ := J.midCQ hni hE
    have hS : JMidRecvHypS (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA _ rg)).bv) cr σ :=
      jMidRecvHypS_of hA (jMidLeavesHyp_of2 hA (jMidLeavesHyp_of3 hA (jMidLeavesHyp_of4 hA hmax htu
        (jMidLeavesHyp_of5 hA hmax htu (jMidLeavesHyp_of6 hA hmax htu hS6)))))
    exact dispatch_midJMUNM s a σ J hni _ hct n c rg sr cr hm' hG hE hP hW.toP
      (jMidRecvHyp_of hA hG.maxTU hG.tu hs hq hW hV hS) hPD
      (jDecMRL_of arI s a σ J hG hE _ hct hPD hN hM hKD hIo hIoa (hDL _ hct)) hR hK.vmt hVI hN hARI hA hnd hM hKD hPA hIA
      hmrt

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- **`kernel_entryJ13PUGM` without `hDM`**: the dispatch by `dispatch_all13PUNM2`
(`MR` at the chosen outcome, `JDecMRL2` [W] for the loud cap kinds). -/
theorem kernel_entryJ13PUGMD2 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hNS0 : NativeScope σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHyps13PU (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hDL : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        ∀ ct', sched.cur_thread st s' = ok ct' → JDecMRL2 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct')
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄ := by
  have hMK := hKD.toK
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, hTR⟩ := hI.1.tcb ct hctT
  have hxs := hI.1.toE.at_tcb hctT hk
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  -- the FaultIP write
  unfold syscall.handle_syscall_old
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.NEXT_IP) ?_
  rintro nx hnx
  simp only [lift, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.FAULT_IP _) ?_
  rintro s1 rfl
  generalize hv : core.num.U64.wrapping_sub nx 2#u64 = v
  have hvb : v.bv = x.tcbArch.tcbContext.userRegs .nextIP - 2 := by
    rw [← hv, core.num.U64.wrapping_sub_bv_eq, hnx, ← hxs.regs .nextIP, regIdx_nextIP]; rfl
  have hX2 := reg_wr_irel J.ip hI hctT hk Fl4Spec.Register.faultIP (by decide) v
  rw [regIdx_faultIP] at hX2
  obtain ⟨V0, J0⟩ := J.regWrJ hctT hk Fl4Spec.Register.faultIP v (by rw [regIdx_faultIP]; exact hX2)
  rw [regIdx_faultIP, hvb] at J0
  rw [← hcur] at J0
  have hF : ((), faultIPSt σ σ.curThread x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 := by
    rw [fl4SyscallFaultIP_eq hk']; exact Set.mem_singleton _
  have hni0 : Entered (faultIPSt σ σ.curThread x) := hni
  have hBu := hB x hk'
  -- the trap flag and the number range
  refine WP.spec_bind (hflag ct v hct) ?_
  rintro f hf
  simp only [hf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg hn.range.1, if_neg hn.range.2]
  -- budget_ok
  have hAK := hARI.toARKeep
  have hBud : syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) v) a ⦃ r =>
      (r.1 = true → ∃ σ', (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart)
          (faultIPSt σ σ.curThread x) = ({(true, σ')}, False) ∧
        σ'.kheap = (faultIPSt σ σ.curThread x).kheap ∧ σ'.curThread = (faultIPSt σ σ.curThread x).curThread ∧
        σ'.curSc = (faultIPSt σ σ.curThread x).curSc ∧
        σ'.schedulerAction = (faultIPSt σ σ.curThread x).schedulerAction ∧
        σ'.idleThread = (faultIPSt σ σ.curThread x).idleThread ∧
        CurInv σ' ∧ OffReady σ' ∧ ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V0) H Cs Ac' Lst' D' r.2.1 r.2.2 σ') ∧
      (r.1 = false → ∃ z ∈ (specBudget (faultIPSt σ σ.curThread x)).1, z.1 = false ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2) ⦄ := by
    exact JAtZ.budgetOkB (σ0 := faultIPSt σ σ.curThread x) J0 hni0 hBu (SInv.ns_fl4SyscallFaultIP σ.curThread σ hNS0 _ hF) hAK hA
      hnd hmrt hmb hmax htu
  refine WP.spec_bind (WP.spec_and (spec_and_eq hBud fun _ h => h) (budget_ok_mr hM hMK hA hR _)) ?_
  rintro ⟨b, s2, a1⟩ ⟨⟨⟨hTr, hFa⟩, hbeq⟩, hMRb⟩
  cases b
  · -- the budget check stops the system call
    obtain ⟨z, hz, hz1, Z', Ac', Lst', D', J'⟩ := hFa rfl
    obtain ⟨b', σb⟩ := z
    simp only at hz1; subst hz1
    show (do
      let (s3, a2) ← (if false = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    have hx : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hz mem_whenE_false))
    have F := hFin _ hx Z' H Cs Ac' Lst' D' s2 a1
      ⟨ct, v, false, s2, a1, hct, hbeq, Or.inl ⟨rfl, rfl, rfl⟩⟩ J'.toR
    have hMσb := (budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd hz hMRb hVI).1
    exact WP.spec_mono (jat_finishJRNM s2 a1 σb J'.toR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMσb)
      fun r ⟨σ', hmem, hRJ, hM'⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ, hM'⟩
  · -- the system call runs
    obtain ⟨σb, he, ekh, ect, ecs, eact, eidle, hCb, hOb, Ac', Lst', D', J'⟩ := hTr rfl
    show (do
      let (s3, a2) ← (if true = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄
    rw [if_pos rfl]
    have hb : (true, σb) ∈ (specBudget (faultIPSt σ σ.curThread x)).1 := by
      unfold specBudget
      rw [he]; exact Set.mem_singleton _
    have hBA : BudgetAt σ σb true := ⟨_, hF, hb⟩
    obtain ⟨hMRσb, hVIσb⟩ := budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd (show (true, σb) ∈ _ by rw [he]; exact Set.mem_singleton _)
      hMRb hVI
    have hnib : Entered σb := ⟨by rw [ect, eidle]; exact hni0.1, by rw [eact]; exact hni0.2⟩
    have hNSb : NativeScope σb := SInvN.ns_of_kheap ekh (SInv.ns_fl4SyscallFaultIP σ.curThread σ hNS0 _ hF)
    have hfr : KFrontB (L := L) arI s a s2 a1 := ⟨ct, v, hct, hbeq⟩
    refine WP.spec_bind (spec_and_eq (dispatch_all13PUNM2 s2 a1 σb J' hnib n c hn
      (hK σb hBA V0 _ _ _ s2 a1 hfr J') (hDL σb hBA V0 _ _ _ s2 a1 hfr J') hMRσb hVIσb hNSb hARI hA hnd hM hKD hIo hIoa hPA hIA
      hmrt hmax htu)
      fun _ h => h) ?_
    rintro ⟨s3, a2⟩ ⟨hDMp, hdeq⟩
    obtain ⟨y, hy, ⟨hy1, hR, hJ, hMy⟩ | ⟨hy1, hQ⟩⟩ := hDMp
    · obtain ⟨Zm, Hm, Csm, Acm, Lstm, Dm, JmR⟩ := hJ
      obtain ⟨u, σm⟩ := y
      simp only at hy1; subst hy1
      have hx : ((.ok (), σm) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
        mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hb (mem_whenE_true hy)))
      have F := hFin _ hx Zm Hm Csm Acm Lstm Dm s3 a2
        ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ JmR
      exact WP.spec_mono (jat_finishJRNM s3 a2 σm JmR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
        F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMy)
        fun r ⟨σ', hmem, hRJ, hM'⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ, hM'⟩
    · obtain ⟨u, σ1⟩ := y
      simp only at hy1; subst hy1
      have hPA : PreemptedAt c σ σ1 := ⟨σb, hBA, hy⟩
      refine WP.spec_mono (kPreFinAtGM (r := (s3, a2))
        (fun x hx Z' H' Cs' Ac' Lst' D' J' =>
          hFin x hx Z' H' Cs' Ac' Lst' D' s3 a2 ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ J')
        hA hnd hmb hNS0 hT hmax htu hM hKD σ1 hPA hQ) ?_
      rintro r (hfail | ⟨z, hz, σ', hmem, hRJ, hM'⟩)
      · exact Or.inl (fail_kentry hF hb hy hfail)
      · have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
          mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
        exact Or.inr ⟨σ', mem_kentry hx hmem, hRJ, hM'⟩

end

/-! ## The tops -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The newest top** (module docstring): `kernel_entryJ37` without `hDM`
(`JDispMRI` [W]): `MR` at the chosen outcome (`KPostXM`) carried through the
dispatch; in its place the narrower `hDL` [W] (`JDecMRL2`: the loud cap
kinds' decode with `MR`, at the dispatch states). Every other premise as
J36 / J37. -/
theorem kernel_entryJ39 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hX : SInvX σ)
    (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV35 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hDL : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        ∀ ct', sched.cur_thread st s' = ok ct' → JDecMRL2 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct')
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI)
    (hFast : n = fl4_abi.syscall.SysReplyRecv →
      FastRR (L := L) (arI := arI) s a n (fun r => KPostM (L := L) arI AR MR c σ r)) :
    syscall.handle_syscall st arI s a n ⦃ r => KPostXM (L := L) arI AR MR c σ r ⦄ := by
  have hni := hX.entered hct
  have hS := hX.sb
  have hE := hX.epQAll
  have hQ := hX.ctQ
  have hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x) :=
    fun _ _ => offReady_faultIPSt hX.offReady
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hG : syscall.handle_syscall_old st arI s a n ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄ :=
    kernel_entryJ13PUGMD2 s a σ J hni hR hS.1.1.vim hS.1.1.ns n c hn hflag
      (fun x hk => ⟨hM.nowAgree hR hS.1.1.vmt, curInv_faultIPSt hk hC, hB x hk, Or.inr hQ⟩)
      (fun σb hBA V' Ac' Lst' D' s' a' hfr J' =>
        ((((((((hK σb hBA V' Ac' Lst' D' s' a' hfr J').to33 J'
          (jEntryGlobM32_of _ hARI hA hnd hPA hT hmax htu hRef hPI)).to32
          (liveDN_front hnd J J.live hS hARI.toARKeep hA hfr hBA)).to31).to27b.to27 hnd hS hni hE hBA).to26
          hnd hS hni hQ hB hBA).to25 hA hmax htu hmb J' (hBA.enteredP hnd hni)).to23 hA hmax htu).to13PU J' hBA
          hA hnd hM hKD hmax htu)
      hDL
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J' =>
        (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J').to27.toR
          (fun o e => SInvAll.sinvB_front_fo true c hS hct x hx o e))
      hARI hA hnd hM hKD hIo hIoa hPA hIA hmrt hmb hT hmax htu
  have hP : syscall.handle_syscall st arI s a n ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄ := by
    by_cases hrr : n = fl4_abi.syscall.SysReplyRecv
    · exact P1.FastAgree.spec st arI (P1.FastAgree.of_acc st arI P1.LawfulStore.total hA
        (FastRR.acc hflag hn.range hrr (hFast hrr))) hG
    · rw [handle_syscall_eq_general_of hflag hn.range hrr, P1.handle_syscall_general_eq]; exact hG
  refine WP.spec_mono hP ?_
  rintro r (hF | ⟨σ', hy, hRJ, hM'⟩)
  · exact Or.inl hF
  · exact Or.inr ⟨σ', hy, hRJ, hM', kentry_sinvX hnd c hX hct _ hy⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`kernel_entry_reachM` with `kernel_entryJ39`**: no `JDispMR` input; the
per-state premises are g4a's (`hflag`, `hK`, `hFin`, `hFast` for `KPostM`)
and `hDL` [W] (`JDecMRL2` at the dispatch states). -/
theorem kernel_entry_reachMD2 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachM (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ MR a σ.machineState ∧
      ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
      (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
        ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
      (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
        (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
          KDispHypsKV35 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
      (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
        (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
          ∀ ct', sched.cur_thread st s' = ok ct' → JDecMRL2 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
      (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
        (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
          JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
          KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2) →
      (n = fl4_abi.syscall.SysReplyRecv →
        FastRR (L := L) (arI := arI) s a n (fun r => KPostM (L := L) arI AR MR c σ r)) →
      syscall.handle_syscall st arI s a n ⦃ r => (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).2 ∨
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachM (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hX, hR⟩ := jreach_invM hnd hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hR, fun n c hct hn hflag hK hDL hFin hFast => ?_⟩
  have hE := kernel_entryJ39 (MR := MR) s a σ J hct hR hX n c hn hflag hK hDL hFin hARI hA hnd hM hKD hIo hIoa hPA hIA
    hmrt hmb hT hmax htu hRef hPI hFast
  obtain ⟨⟨s', a'⟩, hv, hP⟩ := spec_exists hE
  rw [hv, WP.spec_ok]
  rcases hP with hF | ⟨σ', hy, hRJ, hM', hX'⟩
  · exact Or.inl hF
  · exact Or.inr ⟨σ', hy, hRJ, hX', hM', JReachM.step n c hJ hct hn hv hy ⟨hRJ, hM'⟩⟩

end

end

end Fl4Proofs.P3
