/-
P3 (DESIGN.md §9), interrupts: **IRQControl**, the four labels:
`IRQIssueIRQHandler` (FL4: through the legacy PIC when there is no IOAPIC,
else `IllegalOperation` as l4v), `X86IRQIssueIRQHandlerIOAPIC`, `MSI`, and
l4h's `IOAPICRemapped`, decode and invoke, against
`decodeFl4IrqControl` / `invokeFl4IrqControl` (Fl4Spec/Ext/IrqControl.lean).

Hypotheses beyond those of `CnodeCopy` (labels, message, extra caps): the
interrupt relation (`IntLayout`, `IrqRel`, `HandlersActive`); the invoked
cap is the IRQ control cap of a CNode slot; the scheduler-action word is not
an IRQ state word; and the arch operations: `mask_irq`, `ioapic_map` and
`ioapic_map_remapped` are total, `num_ioapics` and `ioapic_pins` are the
spec's `x64_num_ioapics` and `x64_ioapic_nirqs` (`ArchIrqRel`).
-/
import Fl4Proofs.P3.IrqControl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
open Fl4Spec

theorem run_liftME_err {σ ε α β : Type} {f : α → β} {m : NonDetE σ ε α} {s : σ} {e : ε}
    (h : m.run s = ({(.error e, s)}, False)) : (NonDetE.liftME f m).run s = ({(.error e, s)}, False) := by
  unfold NonDetE.liftME; rw [run_bind_error h]

theorem run_liftME_ok {σ ε α β : Type} {f : α → β} {m : NonDetE σ ε α} {s : σ} {a : α}
    (h : m.run s = ({(.ok a, s)}, False)) : (NonDetE.liftME f m).run s = ({(.ok (f a), s)}, False) := by
  unfold NonDetE.liftME; rw [run_bind_ok h]; rfl

theorem mem_liftE {σ ε α : Type} {m : NonDet σ α} {s : σ} {x : α × σ} (h : x ∈ (m s).1) :
    ((.ok x.1, x.2) : Except ε α × σ) ∈ ((NonDetE.liftE (ε := ε) m).run s).1 := by
  unfold NonDetE.liftE
  rw [ExceptT.run_lift]
  exact mem_bind_nd h rfl

theorem nd_assoc {σ α β γ : Type} (m : NonDet σ α) (f : α → NonDet σ β)
    (g : β → NonDet σ γ) (s : σ) : ((m >>= f) >>= g) s = (m >>= fun a => f a >>= g) s := by
  simp only [nd_bind_apply]
  refine Prod.ext (Set.ext fun r => ?_) (propext ?_)
  · simp only [Set.mem_setOf_eq]; constructor
    · rintro ⟨x, ⟨y, hy, hx⟩, hr⟩; exact ⟨y, hy, x, hx, hr⟩
    · rintro ⟨y, hy, x, hx, hr⟩; exact ⟨x, ⟨y, hy, hx⟩, hr⟩
  · simp only [Set.mem_setOf_eq]; constructor
    · rintro ((h | ⟨y, hy, h⟩) | ⟨x, ⟨y, hy, hx⟩, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨y, hy, Or.inl h⟩
      · exact Or.inr ⟨y, hy, Or.inr ⟨x, hx, h⟩⟩
    · rintro (h | ⟨y, hy, h | ⟨x, hx, h⟩⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨y, hy, h⟩)
      · exact Or.inr ⟨x, ⟨y, hy, hx⟩, h⟩

theorem rbind_assoc {σ ε α β γ : Type} (m : NonDetE σ ε α) (f : α → NonDetE σ ε β) (g : β → NonDetE σ ε γ)
    (s : σ) : ((m >>= f) >>= g).run s = (m >>= fun a => f a >>= g).run s := by
  simp only [ExceptT.run_bind]
  rw [nd_assoc]
  refine congrArg (fun k => (ExceptT.run m >>= k) s) (funext fun x => ?_)
  cases x with
  | ok a => rfl
  | error e => exact nd_pure_bind _ _

theorem whenE_pos {σ ε : Type} {P : Prop} [Decidable P] (h : P) (m : NonDetE σ ε Unit) :
    NonDetE.whenE P m = m := by unfold NonDetE.whenE; rw [if_pos h]

theorem whenE_neg {σ ε : Type} {P : Prop} [Decidable P] (h : ¬ P) (m : NonDetE σ ε Unit) :
    NonDetE.whenE P m = NonDetE.returnOk () := by unfold NonDetE.whenE; rw [if_neg h]; rfl

theorem bv_gt_iff (y : U64) (k : Nat) (hk : k < 2 ^ 64) : (y.bv > (BitVec.ofNat 64 k)) ↔ k < y.val := by
  rw [GT.gt, BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]; rfl

theorem whenE_run_true {σ ε : Type} {e : ε} {s : σ} :
    (NonDetE.whenE True (NonDetE.throwError (σ := σ) e)).run s = ({(.error e, s)}, False) := rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The target slot**: `lookup_target_slot` then `ensure_empty_slot`
against the spec's `lookup_target_slot` and `ensure_empty`, for any
continuation. -/
theorem target_tail {X : Type} (invk : X → Fl4Spec.PMonad Unit Unit) (th : TypedHeap) (kb : U64)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s))
    (c : capability.Cap) (ac : Fl4Spec.Cap) (hca : CapRel c ac) (hcv : CapValid th c) (idx dep : U64)
    (ks : Fl4Spec.CslotPtr → Fl4Spec.SEMonad Unit X)
    (K : obj.Slot → Result (core.result.Result Unit error.Exc × S × A))
    (hK : ∀ dsl pd, dsl.1 = pd.bv → th pd = some (.cnode dsl.2.length) →
      capAt (L.mem s) (cslotAddr dsl) = ok .Null →
      K (cslotAddr dsl) ⦃ res => CPost (L := L) arI invk th kb σ (ks dsl) s ar res ⦄) :
    (do
      let r ← cspace.lookup_target_slot st s c idx dep
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r1 ← cdt.ensure_empty_slot st s val
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ => K val
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.Exc) residual
          ok (r2, s, ar)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.Exc) residual
        ok (r1, s, ar)) ⦃ res =>
      CPost (L := L) arI invk th kb σ (Fl4Spec.lookupTargetSlot ac (Fl4Spec.dataToCptr idx.bv) (Fl4Spec.unat dep.bv) >>=
        fun d => Fl4Spec.ensureEmpty d >>= fun _ => ks d) s ar res ⦄ := by
  unfold cspace.lookup_target_slot
  obtain ⟨r1, hr1, e1, he1, hrel1⟩ := spec_exists
    (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hR hV false c ac hca hcv idx dep)
  rw [hr1]; simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  have hlt : (Fl4Spec.lookupTargetSlot (Z := Unit) ac (Fl4Spec.dataToCptr idx.bv) (Fl4Spec.unat dep.bv)).run σ =
      ({(e1, σ)}, False) := he1
  cases r1 with
  | Err e =>
    cases e1 with
    | ok _ => exact hrel1.elim
    | error e' =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.from, bind_ok, bind_tc_ok]
      exact CPost.err (run_bind_error hlt _) (Or.inl hrel1)
  | Ok dest =>
    cases e1 with
    | error _ => exact hrel1.elim
    | ok dsl =>
      obtain ⟨rfl, pd, hpd1, hpd⟩ := hrel1
      obtain ⟨cd, ad, hcd, hcad, hgd⟩ := hR.slot_cap (Z := Unit) hpd1 hpd
      unfold cdt.ensure_empty_slot
      simp only [slot_cap_eq, hcd, bind_ok]
      have hee := ensureEmpty_run dsl σ hgd
      refine CPost.congr (run_bind_ok hlt _) ?_
      by_cases hdn : cd = .Null
      swap
      · rw [cap_is_null_ne hdn]
        simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
          core.convert.FromSame.from, bind_tc_ok]
        have : ad ≠ .nullCap := fun h => hdn ((hcad.null_iff).1 h)
        simp only [this, ↓reduceIte] at hee
        exact CPost.err (run_bind_error hee _) (Or.inl trivial)
      subst hdn
      have hadn : ad = .nullCap := (hcad.null_iff).2 rfl
      simp only [hadn, ↓reduceIte] at hee
      rw [cap_is_null_null]
      simp only [bind_ok, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch]
      refine CPost.congr (run_bind_ok hee _) ?_
      exact hK dsl pd hpd1 hpd hcd

variable {arI} in
theorem CPost.liftME {X Y : Type} {f : X → Y} {invk : Y → Fl4Spec.PMonad Unit Unit} {th : TypedHeap} {kb : U64}
    {σ : Fl4Spec.State Unit} {m : Fl4Spec.SEMonad Unit X} {s : S} {ar : A} {res : core.result.Result Unit error.Exc × S × A}
    (hq : CPost (L := L) arI (invk ∘ f) th kb σ m s ar res) :
    CPost (L := L) arI invk th kb σ (Fl4Spec.NonDetE.liftME f m) s ar res := by
  obtain ⟨r, s', a'⟩ := res
  cases r with
  | Err e => obtain ⟨h1, ⟨e', h2, h3⟩, h4⟩ := hq; exact ⟨h1, ⟨e', run_liftME_err h2, h3⟩, h4⟩
  | Ok u => obtain ⟨inv, h2, h3⟩ := hq; exact ⟨f inv, run_liftME_ok h2, h3⟩

variable {arI} in
theorem CPost.liftME' {X Y : Type} {f : X → Y} {invk : Y → Fl4Spec.PMonad Unit Unit} {th : TypedHeap} {kb : U64}
    {σ : Fl4Spec.State Unit} {m : Fl4Spec.SEMonad Unit X} {s : S} {ar : A}
    {prog : Result (core.result.Result Unit error.Exc × S × A)}
    (hp : prog ⦃ res => CPost (L := L) arI (invk ∘ f) th kb σ m s ar res ⦄) :
    prog ⦃ res => CPost (L := L) arI invk th kb σ (Fl4Spec.NonDetE.liftME f m) s ar res ⦄ :=
  WP.spec_mono hp (fun _ hq => CPost.liftME hq)

@[simp] theorem lbl_issue_val : fl4_abi.label.IRQIssueIRQHandler.val = 33 := by
  simp [fl4_abi.label.IRQIssueIRQHandler]

/-- After a successful decode: `set_thread_state Restart` then
`invoke_irq_control`, against the spec's (`invoke_irq_control` of
`IRQControl`), for an inactive IRQ. -/
theorem issue_tail (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (hHA : HandlersActive (L.mem s) (L.ksb s) G) (hFI : FinInv th (L.mem s) σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (ct : U64) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i)
    (irq : U64) (hirq : irq.val < 128) (hin : L.mem s (irqStA (L.ksb s) irq) = 0#u64)
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (dsl : Fl4Spec.CslotPtr) (pd : U64) (hpd1 : dsl.1 = pd.bv) (hpd : th pd = some (.cnode dsl.2.length))
    (hdst : capAt (L.mem s) (cslotAddr dsl) = ok .Null) :
    (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← interrupt.invoke_irq_control st arI s1 ar irq (cslotAddr dsl) (cslotAddr (ps.bv, idxs))
      ok (core.result.Result.Ok (), s2, a1)) ⦃ res =>
      CPost (L := L) arI (Fl4Spec.invokeFl4IrqControl ∘ Fl4Spec.Fl4IrqControlInvocation.spec) th (L.ksb s) σ
        (Fl4Spec.NonDetE.returnOk (.irqControl (BitVec.ofNat 8 irq.val) dsl (ps.bv, idxs))) s ar res ⦄ := by
  obtain ⟨da, db⟩ := dsl
  simp only at hpd1 hpd; subst hpd1
  have hrs := restart_irq th hP s σ G hCR hL hIR ct hcur htcb hact hact2
  refine WP.spec_bind (WP.spec_and (WP.spec_and hrs (sts_dk4c hP s htcb sched.TS_RESTART)) (spec_self hrs)) ?_
  rintro s1 ⟨⟨⟨hkb, hS, σ1, hst, hCR1, hIR1, -, -, hw⟩, hdk1⟩, hs1⟩
  obtain ⟨xct, hkct, -⟩ := hCR.1.tcb ct htcb
  have hstp1 : CurRun σ → Steps (L := L) arI th s ar σ s1 ar σ1 := Steps.restart arI hcur hkct htcb hs1 hst
  have hL1 : IntLayout th (L.ksb s1) := by rw [hkb]; exact hL
  have hIR1' : IrqRel (L.mem s1) (L.ksb s1) σ1 := by rw [hkb]; exact hIR1
  have hHA1 : HandlersActive (L.mem s1) (L.ksb s1) G := by
    intro y hy i hi
    rw [hS.capV ((hCR.2.2.1.members y).1 hy).1] at hi
    obtain ⟨h1, h2⟩ := hHA y hy i hi
    rw [hkb, hw i h1]; exact ⟨h1, h2⟩
  have hin1 : L.mem s1 (irqStA (L.ksb s1) irq) = 0#u64 := by rw [hkb, hw irq hirq, hin]
  have hFI1 : FinInv th (L.mem s1) σ1 G := hFI.of_same hCR.2.2.1 hS (ksub_of_eq (setThreadState_nks _ _) hst)
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot th (pd.bv, db) := ⟨pd, rfl, Or.inl hpd⟩
  have hsrc1 : capAt (L.mem s1) (cslotAddr (ps.bv, idxs)) = ok .IrqControl := by rw [hS.capAt hAs.isSlot, hsrcC]
  have hdst1 : capAt (L.mem s1) (cslotAddr (pd.bv, db)) = ok .Null := by rw [hS.capAt hAd.isSlot, hdst]
  have hFR1 : MdbOKV (L.ksb s1) (L.mem s1) G := by rw [hkb]; exact MdbOKV.of_same hCR.2.2.1 hS hFR
  refine WP.spec_bind (WP.spec_and (invoke_ctl_rel arI th hP s1 ar σ1 G hCR1 hL1 hIR1' hHA1 hFI1 hFR1 hmask irq hirq
    hin1 hps hpd hls rfl hsrc1 hdst1)
    (invoke_ctl_dk4c arI hP s1 ar hL1 hCR1.2.2.1 hmask irq hirq hAs.isSlot hAd.isSlot hsrc1)) ?_
  rintro ⟨s2, a2⟩ ⟨⟨σ', G', hmem, hCR', hIR', -, hFI', hHA', hFR', hstp2⟩, hdk2⟩
  apply (WP.spec_ok (core.result.Result.Ok (), s2, a2)).mpr
  refine ⟨.irqControl (BitVec.ofNat 8 irq.val) (pd.bv, db) (ps.bv, idxs), rfl, σ1, hst, σ', G', ?_, hCR', ?_,
    hFI', ?_, by rw [← hkb]; exact hFR', fun hD => (hdk1 hD).trans (hdk2 (hD.toK.same (hdk1 hD).1)),
    fun hC => (hstp1 hC).trans arI hstp2⟩
  · exact mem_liftE (x := ((), σ')) hmem
  · rw [← hkb]; exact hIR'
  · rw [← hkb]; exact hHA'

/-- **`IRQIssueIRQHandler`** (label 33). -/
theorem irq_issue_refines (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (hHA : HandlersActive (L.mem s) (L.ksb s) G) (hFI : FinInv th (L.mem s) σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .irqIssueIRQHandler)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (nA : U64) (hnum : arI.num_ioapics ar = ok nA) (hnA : nA.bv = σ.archState.x64NumIoapics)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a') :
    interrupt.decode_irq_control st arI s ar fl4_abi.label.IRQIssueIRQHandler length (cslotAddr (ps.bv, idxs))
      buf extra ⦃ res =>
      CPost (L := L) arI Fl4Spec.invokeFl4IrqControl th (L.ksb s) σ
        (Fl4Spec.decodeFl4IrqControl false slbl (args.map UScalar.bv) (ps.bv, idxs) excaps) s ar res ⦄ := by
  obtain ⟨hR, hV, hM, hC, hI⟩ := hCR
  unfold interrupt.decode_irq_control
  rw [if_pos rfl]
  unfold interrupt.decode_issue_isa interrupt.extra0
  rw [hx0]; simp only [bind_ok, is_null_eq]
  unfold Fl4Spec.decodeFl4IrqControl
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine CPost.liftME' ?_
  unfold Fl4Spec.decodeIrqControlInvocationWith
  rw [if_pos hlbl]
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, c0, ac0, erest, hc0, hca0, hcv0, rfl⟩
  · simp only [decide_true, ↓reduceIte, error.truncated, bind_ok]
    rw [if_neg (show ¬ ((args.map UScalar.bv).length ≥ 3 ∧ ([] : List Fl4Spec.Cap).length ≥ 1) by simp)]
    exact CPost.err (e' := .truncatedMessage) rfl (Or.inl trivial)
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, hc0, bind_ok]
  by_cases h3 : length >= 3#u64
  swap
  · rw [if_neg h3]; simp only [error.truncated, bind_ok]
    rw [if_neg (show ¬ ((args.map UScalar.bv).length ≥ 3 ∧ (ac0 :: erest).length ≥ 1) by simp; scalar_tac)]
    exact CPost.err (e' := .truncatedMessage) rfl (Or.inl trivial)
  rw [if_pos h3]
  obtain ⟨y0, y1, y2, rest, rfl⟩ : ∃ y0 y1 y2 rest, args = y0 :: y1 :: y2 :: rest := by
    match args with
    | [] | [_] | [_, _] => exfalso; simp at hlen; scalar_tac
    | y0 :: y1 :: y2 :: rest => exact ⟨y0, y1, y2, rest, rfl⟩
  rw [if_pos (show ((y0 :: y1 :: y2 :: rest).map UScalar.bv).length ≥ 3 ∧ (ac0 :: erest).length ≥ 1 by simp)]
  simp only [hct, hargs 0#u64 y0 (by simp), hargs 1#u64 y1 (by simp), hargs 2#u64 y2 (by simp), hnum, bind_ok,
    List.map_cons]
  simp only [Fl4Spec.the, List.getElem?_cons_zero, List.getElem?_cons_succ]
  -- `arch_check_irq`
  have hck : ∀ (k : Unit → Fl4Spec.SEMonad Unit Fl4Spec.IrqControlInvocation),
      (Fl4Spec.fl4ArchCheckIrq (Z := Unit) y0.bv >>= k).run σ =
        ((if nA.bv = 0 then Fl4Spec.NonDetE.whenE (y0.bv > 15) (Fl4Spec.NonDetE.throwError (.rangeError 0 15))
          else Fl4Spec.NonDetE.throwError .illegalOperation) >>= k).run σ := by
    intro k
    unfold Fl4Spec.fl4ArchCheckIrq
    rw [rbind_assoc, run_bind_ok (run_liftE
      (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.archState.x64NumIoapics) rfl), hnA]
  refine CPost.congr (hck _) ?_
  by_cases hn0 : nA = 0#u64
  swap
  · have : (nA != 0#u64) = true := by simpa using hn0
    simp only [this, ↓reduceIte, error.illegal, bind_ok]
    have hn0' : ¬ nA.bv = 0 := fun h => hn0 (by rw [UScalar.eq_equiv_bv_eq]; exact h)
    rw [if_neg hn0']
    exact CPost.err (e' := .illegalOperation) (run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation : Fl4Spec.SEMonad Unit Unit)) rfl _)
      (Or.inl trivial)
  subst hn0
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [if_pos (show (0#u64 : U64).bv = 0 from rfl)]
  have hISA : layout.irq.ISA_MAX = 15#u64 := by unfold layout.irq.ISA_MAX; rfl
  have hISA0 : layout.irq.ISA_MIN = 0#u64 := by unfold layout.irq.ISA_MIN; rfl
  by_cases hr : y0 > layout.irq.ISA_MAX
  · rw [if_pos hr]; simp only [error.range, bind_ok]
    have : y0.bv > 15 := (bv_gt_iff y0 15 (by norm_num)).2 (by rw [hISA] at hr; scalar_tac)
    rw [whenE_pos this]
    exact CPost.err (e' := .rangeError 0 15) (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 15) : Fl4Spec.SEMonad Unit Unit)) rfl _)
      (Or.inl ⟨by rw [hISA0]; rfl, by rw [hISA]; rfl⟩)
  rw [if_neg hr]
  have hy15 : y0.val ≤ 15 := by rw [hISA] at hr; scalar_tac
  have : ¬ y0.bv > 15 := fun h => by have := (bv_gt_iff y0 15 (by norm_num)).1 h; omega
  rw [whenE_neg this]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- the IRQ must be inactive
  rw [is_irq_active_eq]; simp only [bind_ok]
  rw [ucast8_ofNat]
  refine CPost.congr (run_bind_ok (run_liftE (isIrqActive_run hIR (by omega))) _) ?_
  by_cases hact0 : L.mem s (irqStA (L.ksb s) y0) = 0#u64
  swap
  · simp only [hact0, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    rw [whenE_pos (by simpa using hact0)]
    exact CPost.err (e' := .revokeFirst) (run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.revokeFirst : Fl4Spec.SEMonad Unit Unit)) rfl _)
      (Or.inl trivial)
  simp only [hact0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [whenE_neg (by simp [hact0])]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  refine target_tail arI (Fl4Spec.invokeFl4IrqControl ∘ Fl4Spec.Fl4IrqControlInvocation.spec) th (L.ksb s) s ar σ
    hR hV c0 ac0 hca0 hcv0 y1 y2
    (fun d => Fl4Spec.NonDetE.returnOk (.irqControl (BitVec.ofNat 8 y0.val) d (ps.bv, idxs))) _ ?_
  intro dsl pd hpd1 hpd hdst
  exact issue_tail arI th hP s ar σ G ⟨hR, hV, hM, hC, hI⟩ hL hIR hHA hFI hFR hmask ct hcur htcb hact hact2 y0 (by omega)
    hact0 hps hls hsrcC dsl pd hpd1 hpd hdst

end

end

end Fl4Proofs.P3
