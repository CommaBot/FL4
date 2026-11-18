/-
P3 (DESIGN.md §9), domains: **the domain cap at the composite relation**
(`DomXHyp`, TopXAll's named `XCap` hypothesis for `.Domain`).

* `decode_invocation_domainX`: the domain cap's `XCap` at `XTop`, from
  `DomPost`'s `Steps` (the restart, then scheduler steps: the configured
  entry, the start's writes, `set_domain`, `reschedule_required`) and
  `Steps.xtop`, given `DomSetHyp` and `DomResHyp`.
* Scheduler steps from the scheduler's refinements at every family of sets
  (`schedStep_of_run`): `reschedule_required` (`schedStep_resched`, one
  outcome given `ActReady`: `rescheduleRequired_k`), `dequeue`, `enqueue`
  (`dequeue_schedStep`, `enqueue_schedStep`), a write keeping every word
  (`same_schedStep`).
* `domResHyp_of`, `domSetHyp_of`: `DomResHyp` and `DomSetHyp` discharged at
  `XTopAt` (the restart at `XTopAt`, `XTopAt.restart'`; `set_domain` of the
  one domain: the domain word and the spec's `tcb_domain` already 0, the
  arch hook a no-op), given `ActReady`.
* `decode_invocation_domainXT`: `DomXHyp` with both discharged.
-/
import Fl4Proofs.P3.XTopCaps
import Fl4Proofs.P3.IpcSchedLift
import Fl4Proofs.P1.QueueSlots
import Fl4Proofs.P1.QueueYield
import Fl4Proofs.P1.QueueFinal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- `DomStallHyp` from the scheduler relation: every TCB of the typed heap is
in `T`, whose threads have the current core's affinity. -/
theorem domStallHyp_of {th : TypedHeap} {s : S} {a : A} {N T C : Set U64} {c : U64}
    {σ : Fl4Spec.State Unit} (hS : Sched.SchedRel st N T C c s σ) (hT : ∀ t, th t = some .tcb → t ∈ T) :
    DomStallHyp (st := st) arI th s a := by
  intro p hp
  have h := Sched.remote_tcb_stall_id (ar := arI) a hS (hT p hp)
  revert h
  cases smp.remote_tcb_stall st arI s a p <;> simp [WP.spec_ok, WP.spec_vis, WP.spec_div]

/-- **The domain cap at any `X` reached by the primitive steps** (as
`decode_invocation_domainX`, from `DomPost`'s `Steps`). -/
theorem decode_invocation_domainXS {AR : A → Fl4Spec.Cr3 → Prop} (hcfg : DomConfig)
    (th : TypedHeap) (hP : Placed th) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = domLabelOf lbl)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 excs)
    (hSet : DomSetHyp (L := L) th s σ ct) (hRes : DomResHyp (L := L) th s σ ct)
    (hstall : DomStallHyp (st := st) arI th s ar) (hC : CurRun σ)
    {X : S → A → Fl4Spec.State Unit → Prop} (hX0 : X s ar σ)
    (hstep : ∀ s' a' σ', Steps (L := L) arI th s ar σ s' a' σ' → X s' a' σ')
    (hXX : ∀ s' a' σ', X s' a' σ' → XTop (L := L) AR s' a' σ')
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI X s ar σ lbl length slot .Domain blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excs buffer ct := by
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (domain_decode_refines arI hcfg th hP s ar σ G hCR hFI hDR ct hct hcur htcb hact hkf hka
      hksO hactK lbl slbl hlbl length buf args hlen hargs extra x0 hx0 excs hex hSet hRes hstall) ?_
    rintro ⟨r0, s', a'⟩ ⟨ha', hq⟩
    subst a'
    try simp only [WP.uncurry'_pair]
    rcases hq with ⟨e, he, hs', e', h1, h2⟩ | ⟨he, inv, hrun, σ1, hst, y, hy, -, -, -, -, -, hstp⟩
    · simp only at he hs'
      subst hs'
      exact Or.inl ⟨e, he, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, hX0⟩
    · have hm : ((.ok [], y.2) : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
          ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeDomain inv)).run σ1).1 := by
        show _ ∈ ((Fl4Spec.NonDetE.liftE (do Fl4Spec.invokeDomain (Z := Unit) inv; return ([] : List Fl4Spec.Data))).run
          σ1).1
        exact mem_liftE (x := ([], y.2)) (mem_bind_nd hy rfl)
      have hXa := hstep _ _ _ (hstp hC A arI ar)
      obtain ⟨Z', hZ'⟩ := hXX _ _ _ hXa
      exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], y.2), hm,
        ⟨Z'.th, Z'.G, Or.inl ⟨he, rfl⟩, hZ'.rel.1, hZ'.rel.2.1, hZ'.rel.2.2.1, hZ'.rel.2.2.2.1,
          hZ'.rel.2.2.2.2.1⟩, hXa⟩
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

/-- **`DomXHyp` for the domain cap**, every label, from `DomPost`'s `Steps`;
beyond `decode_invocation_domain`'s hypotheses, `XTopAt` at its typed heap,
`KsApart`, the current thread runnable, the typed heap's TCBs in `Z.T`,
`ARMask` and `XDelNtfnHyp`. -/
theorem decode_invocation_domainX {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) (hcfg : DomConfig)
    (th : TypedHeap) (hP : Placed th) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = domLabelOf lbl)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 excs)
    (hSet : DomSetHyp (L := L) th s σ ct) (hRes : DomResHyp (L := L) th s σ ct)
    {Z : XSets} (hth : Z.th = th) (hX0 : XTopAt (L := L) AR Z s ar σ)
    (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ) (hTh : ∀ t, th t = some .tcb → t ∈ Z.T)
    (hDel : XDelNtfnHyp (L := L) arI AR th)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot .Domain blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excs buffer ct := by
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (domain_decode_refines arI hcfg th hP s ar σ G hCR hFI hDR ct hct hcur htcb hact hkf hka
      hksO hactK lbl slbl hlbl length buf args hlen hargs extra x0 hx0 excs hex hSet hRes (domStallHyp_of arI hX0.fin.1.1.1 hTh)) ?_
    rintro ⟨r0, s', a'⟩ ⟨ha', hq⟩
    subst a'
    try simp only [WP.uncurry'_pair]
    rcases hq with ⟨e, he, hs', e', h1, h2⟩ | ⟨he, inv, hrun, σ1, hst, y, hy, -, -, -, -, -, hstp⟩
    · simp only at he hs'
      subst hs'
      exact Or.inl ⟨e, he, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ⟨Z, hX0⟩⟩
    · have hm : ((.ok [], y.2) : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
          ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeDomain inv)).run σ1).1 := by
        show _ ∈ ((Fl4Spec.NonDetE.liftE (do Fl4Spec.invokeDomain (Z := Unit) inv; return ([] : List Fl4Spec.Data))).run
          σ1).1
        exact mem_liftE (x := ([], y.2)) (mem_bind_nd hy rfl)
      obtain ⟨Z', hZ'⟩ := (hstp hC A arI ar).xtop arI hAM hDel hth hX0 hKA hTh
      exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], y.2), hm,
        ⟨Z'.th, Z'.G, Or.inl ⟨he, rfl⟩, hZ'.rel.1, hZ'.rel.2.1, hZ'.rel.2.2.1, hZ'.rel.2.2.2.1,
          hZ'.rel.2.2.2.2.1⟩, ⟨Z', hZ'⟩⟩
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨Z, hX0⟩⟩

end

/-! ## Scheduler steps from the scheduler's refinements -/

section Spec
open Fl4Spec Sched

/-- **`reschedule_required` has one outcome** (`ActReady`), changing only
the ready queues and the scheduler action. -/
theorem rescheduleRequired_k {σ : State Unit} (hA : Notif.ActReady σ) :
    ∃ σ', rescheduleRequired (Z := Unit) σ = ({((), σ')}, False) ∧ SchedK σ σ' ∧
      σ'.domainList = σ.domainList ∧ σ'.domainStartIndex = σ.domainStartIndex := by
  cases ha : σ.schedulerAction with
  | switchThread t =>
    by_cases hs : schedulable t σ = true
    · obtain ⟨x, -, -, -, hk, -⟩ := schedulable_inv hs
      have he := tcbSchedAction_gen hk tcbSchedEnqueue
      exact ⟨_, rescheduleRequired_sched ha hs hA he, by constructor <;> rfl, rfl, rfl⟩
    · exact ⟨_, rescheduleRequired_notsched ha (by simpa using hs), by constructor <;> rfl, rfl, rfl⟩
  | resumeCurThread =>
    exact ⟨_, rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h), by constructor <;> rfl, rfl, rfl⟩
  | chooseNewThread =>
    exact ⟨_, rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h), by constructor <;> rfl, rfl, rfl⟩

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

theorem sfootI_schW {T : Set U64} {c : U64} {s : S} {b : U64} (h : Sched.SFootI st T c s b) :
    SchW (L := L) T c s b := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem tfield3_val {y b : U64} (hya : P1.TcbAddr y)
    (h : b = core.num.U64.wrapping_add y 3480#u64 ∨ b = core.num.U64.wrapping_add y 3488#u64 ∨
      b = core.num.U64.wrapping_add y 3592#u64) :
    b.val = y.val + 3480 ∨ b.val = y.val + 3488 ∨ b.val = y.val + 3592 := by
  rcases h with rfl | rfl | rfl
  · exact Or.inl (by rw [Notif.tfield_val hya (by decide)]; rfl)
  · exact Or.inr (Or.inl (by rw [Notif.tfield_val hya (by decide)]; rfl))
  · exact Or.inr (Or.inr (by rw [Notif.tfield_val hya (by decide)]; rfl))

/-- The scheduler's writes keep the domain schedule's words. -/
theorem domSame_of_sfootI {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : Sched.SchedRel st N T C c s σ) (hw : P1.WritesIn st s s' (Sched.SFootI st T c s)) :
    DomSame (L.mem s) (L.mem s') (L.ksb s) := by
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hN := hc.node
  have hf := hN.fits; have hal := hN.align
  simp only [P1.LawfulStore.nodeBase] at hf hal
  apply domSame_iff
  intro o ho
  have h8 : o.val < 256 ∧ o.val % 8 = 0 := by
    simp only [domOffs, List.mem_cons, List.mem_nil_iff, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide
  have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
  refine hw.mem_eq (ksW_al (by omega) (by omega) h8.1 h8.2) fun hb => ?_
  rcases hb with ⟨y, hy, h⟩ | ⟨g1, g2, -⟩
  · have hv' := tfield3_val (hc.tcbs y hy) h
    rw [hv] at hv'
    rcases hc.ksOut y hy with h' | h' <;> omega
  · simp only [P1.LawfulStore.nodeBase] at g1 g2; omega

/-- **A scheduler step from a refinement at every family of sets**: the FL4
run ends at `s'`; at every family whose TCBs include the typed heap's, from
the scheduler and notification relations, the run ends with the scheduler
relation at the spec's `σ'` and writes only the scheduler's words
(`SFootI`); the spec changes only the scheduler's fields. -/
theorem schedStep_of_run {th : TypedHeap} {s s' : S} {σ σ' : Fl4Spec.State Unit} {prog : Result S}
    (hrun : prog = ok s') (hK : SchedK σ σ') (hdl : σ'.domainList = σ.domainList)
    (hds : σ'.domainStartIndex = σ.domainStartIndex)
    (href : ∀ (N T C : Set U64) (c : U64), (∀ t, th t = some .tcb → t ∈ T) → Sched.SchedRel st N T C c s σ →
      Notif.NtfnStateRel N T (L.mem s) σ →
      prog ⦃ s'' => Sched.SchedRel st N T C c s'' σ' ∧ P1.WritesIn st s s'' (Sched.SFootI st T c s) ⦄)
    (hQ : SchedQOK σ σ') (hB : BlkKeep (L := L) th s s') :
    SchedStep (L := L) th s σ s' σ' := by
  refine ⟨hK, fun N T C c hTh hS hN => ?_, hQ, hB⟩
  have h := href N T C c hTh hS hN
  rw [hrun, WP.spec_ok] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, h2.mono fun b hb => sfootI_schW hb, fun hD => domRel_iff.1
    ((domRel_iff.2 hD).of_same (domSame_of_sfootI hS h2) hdl hds)⟩

/-- **`reschedule_required`'s ready queues and action** (`SchedQOK`): the
switch target enqueued when schedulable, the action `chooseNewThread`. -/
theorem rescheduleRequired_qok {σ σ' : Fl4Spec.State Unit} (hA : Notif.ActReady σ)
    (he : Fl4Spec.rescheduleRequired (Z := Unit) σ = ({((), σ')}, False)) : SchedQOK σ σ' := by
  have out : ∀ {σ2 : Fl4Spec.State Unit}, Fl4Spec.rescheduleRequired (Z := Unit) σ = ({((), σ2)}, False) →
      σ' = σ2 := fun h2 =>
      (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst (he.symm.trans h2)))).2
  cases ha : σ.schedulerAction with
  | switchThread t =>
    by_cases hs : Fl4Spec.schedulable t σ = true
    · obtain ⟨x, -, -, -, hk, -⟩ := Sched.schedulable_inv hs
      have e := out (Sched.rescheduleRequired_sched ha hs hA (Sched.tcbSchedAction_gen hk Fl4Spec.tcbSchedEnqueue))
      subst e
      refine ⟨fun d p u hu => ?_, Or.inl rfl⟩
      simp only [Sched.setQ] at hu
      split_ifs at hu with hdp
      · unfold Fl4Spec.tcbSchedEnqueue at hu
        split_ifs at hu
        · exact Or.inl ⟨_, _, hu⟩
        · rcases List.mem_cons.1 hu with rfl | hu
          · exact Or.inr hs
          · exact Or.inl ⟨_, _, hu⟩
      · exact Or.inl ⟨d, p, hu⟩
    · have e := out (Sched.rescheduleRequired_notsched ha (by simpa using hs))
      subst e
      exact ⟨fun d p u hu => Or.inl ⟨d, p, hu⟩, Or.inl rfl⟩
  | resumeCurThread =>
    have e := out (Sched.rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h))
    subst e
    exact ⟨fun d p u hu => Or.inl ⟨d, p, hu⟩, Or.inl rfl⟩
  | chooseNewThread =>
    have e := out (Sched.rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h))
    subst e
    exact ⟨fun d p u hu => Or.inl ⟨d, p, hu⟩, Or.inl rfl⟩

/-- `reschedule_required` as a scheduler step (`ActReady`). -/
theorem schedStep_resched {th : TypedHeap} {s s' : S} {σ σ' : Fl4Spec.State Unit} (hA : Notif.ActReady σ)
    (hrun : sched.reschedule_required st s = ok s')
    (he : Fl4Spec.rescheduleRequired (Z := Unit) σ = ({((), σ')}, False)) (hK : SchedK σ σ')
    (hdl : σ'.domainList = σ.domainList) (hds : σ'.domainStartIndex = σ.domainStartIndex) :
    SchedStep (L := L) th s σ s' σ' :=
  schedStep_of_run hrun hK hdl hds (fun N T C c _ hS hN =>
    WP.spec_mono (WP.spec_and (Sched.reschedule_required_refines s σ hN hS hA) (Sched.reschedule_required_sfootI hS))
      fun s'' h => by
        obtain ⟨⟨σ3, he3, -, -, -, hS3⟩, hw⟩ := h
        rw [he] at he3
        have e := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he3))).2
        subst e
        exact ⟨hS3, hw⟩) (rescheduleRequired_qok hA he)
    fun _ _ _ _ _ _ _ _ _ _ _ h => by
      have h' := P1.sched.reschedule_required.blk s h
      rw [hrun, WP.spec_ok] at h'
      exact h'.1

/-- `SlotsSame` from writes of the other objects' words. -/
theorem XTopAt.slotsSame_of {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hWO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) : SlotsSame Z.th (L.mem s) (L.mem s') :=
  slotsSame_of_vobj hX.rel.1 fun b hb hv => hw.mem_eq hb fun h => hX.fin.1.2.disj b (hWO b h) hv

theorem sfootI_oobj {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {s : S}
    {σ : Fl4Spec.State Unit} (hT : P1.TcbPlaced T) {b : U64} (h : Sched.SFootI st T c s b) :
    OObj st N T C E R B c s σ b := by
  rcases h with ⟨y, hy, rfl | rfl | rfl⟩ | h
  all_goals first
    | exact tcb_oobj hy (hT y hy) (by decide) (by decide)
    | exact Or.inl ⟨h.1, h.2.1⟩

/-- The current thread of `XTopAt`: a TCB of the typed heap, in the spec. -/
theorem XTopAt.curTcb {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) {ct : U64} (hcur : σ.curThread = ct.bv) :
    Z.th ct = some .tcb ∧ ∃ x, σ.kheap ct.bv = some (.tcb x) := by
  obtain ⟨t, htb, hth, -⟩ := hX.fin.2.2.2.2
  have e : t = ct := P1.eq_of_bv (htb.trans hcur)
  subst e
  obtain ⟨x, hk, -⟩ := hX.rel.2.1.1.tcb t hth
  exact ⟨hth, x, hk⟩

/-- `set_thread_state Restart` of the current thread at `XTopAt`, the spec's
outcome given. -/
theorem XTopAt.restart' {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s1 : S} {a : A} {σ σ1 : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (hC : CurRun σ) {ct : U64} (hcur : σ.curThread = ct.bv)
    (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1)
    (hst : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False)) :
    XTopAt (L := L) AR Z s1 a σ1 ∧ L.ksb s1 = L.ksb s ∧ CurRun σ1 := by
  obtain ⟨-, x, hk⟩ := hX.curTcb hcur
  have hrun : Fl4Spec.runnable x.tcbState = true := hC x (by rw [hcur]; exact hk)
  have h := XTopAt.restart hX hcur hk hrun
  rw [hs1, WP.spec_ok] at h
  have e : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    rw [Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  subst e
  refine ⟨h.1, h.2.2, fun y hy => ?_⟩
  rw [stsAct_cur, Notif.stsAct_kheap, Notif.updK_kheap] at hy
  simp only [Notif.updK] at hy
  rw [hcur, Function.update_self] at hy
  cases hy; rfl

/-- `ActReady` across the start's updates. -/
theorem actReady_startSt {σ : Fl4Spec.State Unit} (h : Notif.ActReady σ) (n : Nat) :
    Notif.ActReady (startSt σ n) :=
  Sched.VK.actReady h ⟨fun _ x hx => ⟨x, hx, rfl, rfl⟩, fun _ y hy => ⟨y, hy⟩, fun _ _ _ => Iff.rfl, rfl, rfl, rfl,
    Or.inl rfl⟩

set_option maxHeartbeats 4000000 in
/-- **`DomResHyp` discharged** at `XTopAt`: `reschedule_required` after the
start's writes refines the spec's (`reschedule_required_refines`, given
`ActReady`), as scheduler steps. -/
theorem domResHyp_of {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hC : CurRun σ) (hA : Notif.ActReady σ) {ct : U64}
    (hcur : σ.curThread = ct.bv) : DomResHyp (L := L) Z.th s σ ct := by
  intro s1 σ1 index hs1 hst hidx
  obtain ⟨-, x, hk⟩ := hX.curTcb hcur
  have hrun : Fl4Spec.runnable x.tcbState = true := hC x (by rw [hcur]; exact hk)
  obtain ⟨hX1, hkb1, -⟩ := hX.restart' hC hcur hs1 hst
  have hP := hX.fin.1.2
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hA1 : Notif.ActReady σ1 := Sched.actReady_restart hA hk hrun hst
  have hst4 := schedStep_start (L := L) Z.th s1 σ1 index hkb1 hkf hka
  have hX4 := hX1.schedStep (by rw [hkb1]; exact hKA) hTh hst4
  set s4 := startS (L := L) s1 (L.ksb s) index
  have hk4 : L.ksb s4 = L.ksb s := by simp only [s4, startS, L.ksb_wr]; exact hkb1
  have hA4 := actReady_startSt hA1 index.val
  obtain ⟨σ', hres, hK', hdl', hds'⟩ := rescheduleRequired_k hA4
  have hS4 := hX4.fin.1.1.1
  have hN4 := hX4.fin.1.1.2.2.1
  refine WP.spec_mono (WP.spec_and (WP.spec_and (Sched.reschedule_required_refines s4 _ hN4 hS4 hA4)
    (Sched.reschedule_required_sfootI hS4)) (spec_self (Sched.reschedule_required_sfootI hS4))) ?_
  rintro s5 ⟨⟨⟨σ3, he3, -, -, -, -⟩, hw⟩, hrun5⟩
  rw [hres] at he3
  have e := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he3))).2
  subst e
  refine ⟨hX4.slotsSame_of hw fun b hb => sfootI_oobj (hS4.lists.choose_spec.choose_spec.1.tcbs) hb,
    hw.1.trans hk4, ?_, ((), σ'), by rw [hres]; rfl, KSub.of_kheap hK'.kh, fun m h => h.of_kheap hK'.kh,
    hK'.cdt, hK'.orig, hdl', hds', fun A arI a => Steps.sched arI (schedStep_resched hA4 hrun5 hres hK' hdl' hds')⟩
  have := domSame_of_sfootI hS4 hw
  rwa [hk4] at this

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-! ## `set_domain` -/

/-- `Tcb::set_domain`: a write of the TCB's domain word. -/
theorem tcb_set_domain_eq (s : S) (t v : U64) : obj.Tcb.set_domain st t s v = ok (L.wr s (P1.domA t) v) := by
  unfold obj.Tcb.set_domain
  rw [show layout.tcb.DOMAIN = ok 3432#u64 by unfold layout.tcb.DOMAIN layout.tcb.F; rfl]
  simp only [lift, bind_ok, L.write_eq]; rfl

theorem singleton_out {α : Type} {x y : α} {p : Prop}
    (h : (({x} : Set α), p) = (({y} : Set α), (p : Prop))) : x = y :=
  Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst h)

/-- **`dequeue` as a scheduler step**, at a family's scheduler relation. -/
theorem dequeue_schedStep {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} {t : U64} (htcb : th t = some .tcb)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {N T C : Set U64} {c : U64}
    (hS : Sched.SchedRel st N T C c s σ) (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' =>
      Sched.SchedRel st N T C c s' (Sched.setQ σ x.tcbDomain x.tcbPriority
        (Fl4Spec.tcbSchedDequeue t.bv (σ.readyQueues x.tcbDomain x.tcbPriority))) ∧
      Notif.FootEq N T (L.mem s) (L.mem s') ∧ P1.WritesIn st s s' (Sched.SFootI st T c s) ∧
      SchedStep (L := L) th s σ s' (Sched.setQ σ x.tcbDomain x.tcbPriority
        (Fl4Spec.tcbSchedDequeue t.bv (σ.readyQueues x.tcbDomain x.tcbPriority))) ⦄ := by
  refine WP.spec_mono (WP.spec_and (WP.spec_and (Sched.dequeue_refines s σ hS t ht) (Ipc.dequeue_sfootI hS ht))
    (spec_self (Ipc.dequeue_sfootI hS ht))) ?_
  rintro s' ⟨⟨⟨σ', he, -, -, hfe, hS'⟩, hw⟩, hrun⟩
  rw [Sched.tcbSchedAction_gen hk] at he
  have e := (Prod.mk.inj (singleton_out he)).2
  subst e
  refine ⟨hS', hfe, hw, schedStep_of_run hrun (by constructor <;> rfl) rfl rfl (fun N' T' C' c' hTh' hS'' _ => ?_)
    ⟨fun d p u hu => ?_, Or.inr rfl⟩ fun _ _ _ _ _ _ _ _ _ _ hTh' h => ?_⟩
  rotate_left
  · simp only [Sched.setQ] at hu
    split_ifs at hu with hdp
    · exact Or.inl ⟨_, _, (List.mem_filter.1 hu).1⟩
    · exact Or.inl ⟨d, p, hu⟩
  · have h' := P1.sched.dequeue.blkY s t h (hTh' t htcb)
    rw [hrun, WP.spec_ok] at h'
    exact h'.1
  refine WP.spec_mono (WP.spec_and (Sched.dequeue_refines s σ hS'' t (hTh' t htcb))
    (Ipc.dequeue_sfootI hS'' (hTh' t htcb))) fun s'' h => ?_
  obtain ⟨⟨σ3, he3, -, -, -, hS3⟩, hw3⟩ := h
  rw [Sched.tcbSchedAction_gen hk] at he3
  have e := (Prod.mk.inj (singleton_out he3)).2
  subst e
  exact ⟨hS3, hw3⟩

/-- **`enqueue` as a scheduler step**, for a thread queued or not released. -/
theorem enqueue_schedStep {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} {t : U64} (htcb : th t = some .tcb)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {N T C : Set U64} {c : U64}
    (hS : Sched.SchedRel st N T C c s σ) (ht : t ∈ T)
    (hr : (L.mem s (P1.inqA t) &&& sched.Q_QUEUED) = 0#u64 → (L.mem s (P1.inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hsch : Fl4Spec.schedulable t.bv σ = true) (hrn : P1.Runnable (L.mem s (P1.stA t)))
    (hbd : L.mem s (P1.scA t) ≠ 0#u64) (hrl : (L.mem s (P1.inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hrm : L.rmax s (L.mem s (P1.scA t)) ≠ 0#u64) :
    sched.enqueue st s t ⦃ s' =>
      Sched.SchedRel st N T C c s' (Sched.setQ σ x.tcbDomain x.tcbPriority
        (Fl4Spec.tcbSchedEnqueue t.bv (σ.readyQueues x.tcbDomain x.tcbPriority))) ∧
      Notif.FootEq N T (L.mem s) (L.mem s') ∧ P1.WritesIn st s s' (Sched.SFootI st T c s) ∧
      SchedStep (L := L) th s σ s' (Sched.setQ σ x.tcbDomain x.tcbPriority
        (Fl4Spec.tcbSchedEnqueue t.bv (σ.readyQueues x.tcbDomain x.tcbPriority))) ⦄ := by
  refine WP.spec_mono (WP.spec_and (WP.spec_and (Sched.enqueue_refines s σ hS t ht hr) (Sched.enqueue_sfootI hS ht))
    (spec_self (Sched.enqueue_sfootI hS ht))) ?_
  rintro s' ⟨⟨⟨σ', he, -, -, hfe, hS'⟩, hw⟩, hrun⟩
  rw [Sched.tcbSchedAction_gen hk] at he
  have e := (Prod.mk.inj (singleton_out he)).2
  subst e
  refine ⟨hS', hfe, hw, schedStep_of_run hrun (by constructor <;> rfl) rfl rfl (fun N' T' C' c' hTh' hS'' _ => ?_)
    ⟨fun d p u hu => ?_, Or.inr rfl⟩ fun _ _ _ _ _ _ _ _ _ _ hTh' h => ?_⟩
  rotate_left
  · simp only [Sched.setQ] at hu
    split_ifs at hu with hdp
    · unfold Fl4Spec.tcbSchedEnqueue at hu
      split_ifs at hu
      · exact Or.inl ⟨_, _, hu⟩
      · rcases List.mem_cons.1 hu with rfl | hu
        · exact Or.inr hsch
        · exact Or.inl ⟨_, _, hu⟩
    · exact Or.inl ⟨d, p, hu⟩
  · have hba := (h.2.2.2.1.act _ (h.2.2.1.2.2.bound t (hTh' t htcb) hbd).1).2 hrm
    have h' := P1.sched.enqueue.blkY s t h (hTh' t htcb) hrn hbd hba hrl
    rw [hrun, WP.spec_ok] at h'
    exact h'.1
  refine WP.spec_mono (WP.spec_and (Sched.enqueue_refines s σ hS'' t (hTh' t htcb) hr)
    (Sched.enqueue_sfootI hS'' (hTh' t htcb))) fun s'' h => ?_
  obtain ⟨⟨σ3, he3, -, -, -, hS3⟩, hw3⟩ := h
  rw [Sched.tcbSchedAction_gen hk] at he3
  have e := (Prod.mk.inj (singleton_out he3)).2
  subst e
  exact ⟨hS3, hw3⟩

/-- A write of a word with its value: no word changes. -/
theorem writesIn_same {s : S} {a : U64} (ha : P1.Aligned a) :
    P1.WritesIn st s (L.wr s a (L.mem s a)) (fun _ => False) := by
  refine ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb _ => ?_⟩
  by_cases e : b = a
  · subst e; exact L.mem_wr_same ha
  · exact L.mem_wr_ne ha hb (fun h => e (UScalar.eq_of_val_eq h).symm)

/-- **A write keeping every word** as a scheduler step. -/
theorem same_schedStep {th : TypedHeap} {s s' : S} {σ : Fl4Spec.State Unit}
    (hw : P1.WritesIn st s s' (fun _ => False)) : SchedStep (L := L) th s σ s' σ := by
  refine ⟨by constructor <;> rfl, fun N T C c _ hS _ => ?_, SchedQOK.refl σ,
    fun _ _ _ _ _ _ _ _ _ _ _ h => (P1.blk_of_capw h hw fun _ hb => hb.elim).1⟩
  have hw' : P1.WritesIn st s s' (Sched.SFootI st T c s) := hw.mono fun _ h => h.elim
  exact ⟨hS.stableW (hw.mono fun _ h => h.elim) ⟨rfl, rfl, fun _ => Or.inl rfl⟩, hw.mono fun _ h => h.elim,
    fun hD => domRel_iff.1 ((domRel_iff.2 hD).of_same (domSame_of_sfootI hS hw') rfl rfl)⟩


theorem mem_whenP {σ : Fl4Spec.State Unit} {P : Prop} [Decidable P] {m : Fl4Spec.SMonad Unit Unit}
    {z : Unit × Fl4Spec.State Unit} (h : P → z ∈ (m σ).1) (h' : ¬ P → z = ((), σ)) :
    z ∈ (Fl4Spec.NonDet.when P m σ).1 := by
  unfold Fl4Spec.NonDet.when
  by_cases hp : P
  · rw [if_pos hp]; exact h hp
  · rw [if_neg hp, h' hp]; rfl

theorem kview_of_kheap {σ σ' : Fl4Spec.State Unit} (h : σ'.kheap = σ.kheap) : Notif.KView σ σ' :=
  ⟨fun p x hx => by rw [h]; exact hx, fun p x hx => ⟨x, by rw [h]; exact hx, rfl, rfl, rfl⟩⟩

theorem vk_of {σ σ' : Fl4Spec.State Unit} (hK : SchedK σ σ') (ha : σ'.schedulerAction = σ.schedulerAction) :
    Sched.VK σ σ' :=
  ⟨fun _ x hx => ⟨x, by rw [hK.kh]; exact hx, rfl, rfl⟩, fun _ y hy => ⟨y, by rw [← hK.kh]; exact hy⟩,
    fun _ _ _ => by rw [hK.kh], hK.ct, hK.ctime, hK.rel, Or.inl ha⟩

/-- The domain field rewritten with its value: the heap unchanged. -/
theorem threadSetDomain_same {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) {d : Fl4Spec.Domain} (hd : x.tcbDomain = d) :
    ((), σ) ∈ (Fl4Spec.threadSetDomain (Z := Unit) t d σ).1 := by
  unfold Fl4Spec.threadSetDomain
  rw [Notif.threadSet_eq _ hk]
  subst hd
  have e : Notif.updK σ t (.tcb { x with tcbDomain := x.tcbDomain }) = σ := by
    unfold Notif.updK
    rw [show ({ x with tcbDomain := x.tcbDomain } : Fl4Spec.Tcb) = x from rfl, ← hk, Function.update_eq_self]
  rw [e]; rfl

set_option maxHeartbeats 16000000 in
/-- **`DomSetHyp` discharged** at `XTopAt`: FL4's `set_domain` (`dequeue`,
the domain word, `enqueue` when schedulable, `reschedule_required` for the
current thread) refines the spec's `invoke_set_domain` (the arch hook a
no-op, the domain already 0: one domain) as scheduler steps, given
`ActReady`. -/
theorem domSetHyp_of {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s ar σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hC : CurRun σ)
    (hA : Notif.ActReady σ) {ct : U64} (hcur : σ.curThread = ct.bv) : DomSetHyp (L := L) Z.th s σ ct := by
  intro s1 σ1 t d hs1 hst htcb hd
  have hd0 : d = 0#u64 := UScalar.eq_of_val_eq (by have : (0#u64 : U64).val = 0 := rfl; omega)
  subst hd0
  obtain ⟨-, x0, hk0⟩ := hX.curTcb hcur
  obtain ⟨hX1, hkb1, -⟩ := hX.restart' hC hcur hs1 hst
  have hA1 : Notif.ActReady σ1 := Sched.actReady_restart hA hk0 (hC x0 (by rw [hcur]; exact hk0)) hst
  have ht : t ∈ Z.T := hTh t htcb
  have hS1 := hX1.fin.1.1.1
  have hN1 := hX1.fin.1.1.2.2.1
  obtain ⟨Q1, R1, hc1, hs1'⟩ := hS1.lists
  have hT := hc1.tcbs
  obtain ⟨x, hkx, hxd, -, -, -⟩ := hs1'.tcb t ht
  set σa := Sched.setQ σ1 x.tcbDomain x.tcbPriority
    (Fl4Spec.tcbSchedDequeue t.bv (σ1.readyQueues x.tcbDomain x.tcbPriority)) with hσa
  have hka : σa.kheap t.bv = some (.tcb x) := hkx
  unfold sched.set_domain
  refine WP.spec_bind (dequeue_schedStep htcb hkx hS1 ht) ?_
  rintro sa ⟨hSa, hfea, hwa, hsta⟩
  rw [tcb_set_domain_eq]; simp only [bind_ok]
  -- the domain word, already 0
  obtain ⟨Qa, Ra, hca, hsa'⟩ := hSa.lists
  obtain ⟨-, -, -, hdom0, -, -⟩ := hsa'.tcb t ht
  have hdal : P1.Aligned (P1.domA t) := P1.field_aligned (hca.tcbs t ht) (by decide) (by decide)
  have hsame : P1.WritesIn st sa (L.wr sa (P1.domA t) 0#u64) (fun _ => False) := by
    have := writesIn_same (L := L) (s := sa) hdal; rwa [hdom0] at this
  set sb := L.wr sa (P1.domA t) 0#u64 with hsb
  have hSb : Sched.SchedRel st Z.N Z.T Z.C Z.c sb σa :=
    hSa.stableW (hsame.mono fun _ h => h.elim) ⟨rfl, rfl, fun _ => Or.inl rfl⟩
  have hNa : Notif.NtfnStateRel Z.N Z.T (L.mem sa) σa :=
    Notif.NtfnStateRel.frame hN1 hS1.placed hfea (kview_of_kheap rfl)
  have hNb : Notif.NtfnStateRel Z.N Z.T (L.mem sb) σa :=
    Notif.NtfnStateRel.frame hNa hS1.placed (fun a ha _ => hsame.mem_eq ha id) (kview_of_kheap rfl)
  -- `is_schedulable`, then `enqueue` when schedulable
  refine WP.spec_bind (WP.spec_and (Sched.sched.is_schedulable.spec' sb t) (P1.sched.is_schedulable.spec' sb t)) ?_
  rintro b ⟨hb, hbP⟩
  have hbs : b = Fl4Spec.schedulable t.bv σa := hb.trans (Sched.schedulable_eq hNb hSb ht)
  have hif : (if b = true then sched.enqueue st sb t else ok sb) ⦃ sc => ∃ σc,
      Sched.SchedRel st Z.N Z.T Z.C Z.c sc σc ∧ Notif.NtfnStateRel Z.N Z.T (L.mem sc) σc ∧
      P1.WritesIn st sb sc (Sched.SFootI st Z.T Z.c sb) ∧ SchedStep (L := L) Z.th sb σa sc σc ∧
      ((), σc) ∈ (Fl4Spec.NonDet.when (Fl4Spec.schedulable t.bv σa)
        (Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue t.bv) σa).1 ∧
      SchedK σa σc ∧ σc.schedulerAction = σa.schedulerAction ∧ σc.domainList = σa.domainList ∧
      σc.domainStartIndex = σa.domainStartIndex ⦄ := by
    by_cases hb1 : b = true
    · rw [if_pos hb1]
      have hb2 := hb1; rw [hb] at hb2
      have hr0 := (of_decide_eq_true hb2).2.2.2
      obtain ⟨hrn, hbd, hrl, hrm⟩ := hbP hb1
      refine WP.spec_mono (enqueue_schedStep htcb hka hSb ht (fun _ => hr0) (by rw [← hbs, hb1]) hrn hbd hrl hrm) ?_
      rintro sc ⟨hSc, hfec, hwc, hstc⟩
      refine ⟨_, hSc, Notif.NtfnStateRel.frame hNb hS1.placed hfec (kview_of_kheap rfl), hwc, hstc,
        mem_when (fun _ => by rw [Sched.tcbSchedAction_gen hka]; rfl) (fun h => by rw [← hbs, hb1] at h; cases h),
        by constructor <;> rfl, rfl, rfl, rfl⟩
    · rw [if_neg hb1, WP.spec_ok]
      refine ⟨σa, hSb, hNb, P1.WritesIn.refl _ _, same_schedStep (P1.WritesIn.refl _ _),
        mem_when (fun h => by rw [← hbs] at h; exact absurd h hb1) (fun _ => rfl), SchedK.refl _, rfl, rfl, rfl⟩
  refine WP.spec_bind hif ?_
  rintro sc ⟨σc, hSc, hNc, hwc, hstc, hmc, hKc, hac, hdlc, hdsc⟩
  -- the current thread
  refine WP.spec_bind (Sched.sched.cur_thread.spec' sc) ?_
  rintro t1 rfl
  unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
  simp only [bind_ok]
  obtain ⟨Qc, Rc, hcc, hsc'⟩ := hSc.lists
  have hct1 : σ1.curThread = (Sched.nodeW st sc (L.cpu sc) layout.node.CUR_THREAD).bv := by
    rw [hcc.cur, ← hsc'.curThread, hKc.ct]; rfl
  have hKac : SchedK σ1 σc := (show SchedK σ1 σa by constructor <;> rfl).trans hKc
  have hwsc : P1.WritesIn st s1 sc (Sched.SFootI st Z.T Z.c s1) :=
    Sched.WritesIn.sfootI_trans hwa (Sched.WritesIn.sfootI_trans (hsame.mono fun _ h => h.elim) hwc)
  -- the post, from the last step
  have post : ∀ (s2 : S) (σ2 : Fl4Spec.State Unit), P1.WritesIn st sc s2 (Sched.SFootI st Z.T Z.c sc) →
      SchedStep (L := L) Z.th sc σc s2 σ2 → SchedK σc σ2 → σ2.domainList = σc.domainList →
      σ2.domainStartIndex = σc.domainStartIndex →
      ((), σ2) ∈ (Fl4Spec.NonDet.when (t.bv = σ1.curThread) (Fl4Spec.rescheduleRequired (Z := Unit)) σc).1 →
      SlotsSame Z.th (L.mem s1) (L.mem s2) ∧ L.ksb s2 = L.ksb s1 ∧ DomSame (L.mem s1) (L.mem s2) (L.ksb s1) ∧
      ∃ y ∈ (Fl4Spec.invokeSetDomain (Z := Unit) t.bv (Fl4Spec.ucast Fl4Spec.domainLen (0#u64 : U64).bv) σ1).1,
        KSub σ1 y.2 ∧ (∀ m, StateRel Z.th m σ1 → StateRel Z.th m y.2) ∧ y.2.cdt = σ1.cdt ∧
        y.2.isOriginalCap = σ1.isOriginalCap ∧ y.2.domainList = σ1.domainList ∧
        y.2.domainStartIndex = σ1.domainStartIndex ∧
        ∀ (A : Type) (arI : machine.Arch A) (a : A), Steps (L := L) arI Z.th s1 a σ1 s2 a y.2 := by
    intro s2 σ2 hw2 hst2 hK2 hdl2 hds2 hm2
    have hwall : P1.WritesIn st s1 s2 (Sched.SFootI st Z.T Z.c s1) := Sched.WritesIn.sfootI_trans hwsc hw2
    have hK12 := hKac.trans hK2
    refine ⟨hX1.slotsSame_of hwall fun b hb => sfootI_oobj hT hb, hwall.1, domSame_of_sfootI hS1 hwall,
      ((), σ2), ?_, KSub.of_kheap hK12.kh, fun m h => h.of_kheap hK12.kh, hK12.cdt, hK12.orig,
      by rw [hdl2, hdlc]; rfl, by rw [hds2, hdsc]; rfl, fun A arI a =>
        (((Steps.sched arI hsta).trans arI (Steps.sched arI (same_schedStep hsame))).trans arI
          (Steps.sched arI hstc)).trans arI (Steps.sched arI hst2)⟩
    unfold Fl4Spec.invokeSetDomain Fl4Spec.archPrepareSetDomain Fl4Spec.setDomain
    refine mem_bind_nd (x := ((), σ1)) (mem_bind_nd (x := (σ1.curDomain, σ1)) rfl
      (mem_whenP (fun h => ?_) (fun _ => rfl))) ?_
    · exfalso
      exact h (by rw [hs1'.curDom.1]; rfl)
    · refine mem_bind_nd (x := (σ1.curThread, σ1)) rfl
        (mem_bind_nd (x := ((), σa)) (by rw [Sched.tcbSchedAction_gen hkx]; rfl)
          (mem_bind_nd (x := ((), σa)) (threadSetDomain_same hka (by rw [hxd]; rfl))
            (mem_bind_nd (x := (Fl4Spec.schedulable t.bv σa, σa)) rfl (mem_bind_nd (x := ((), σc)) hmc hm2))))
  by_cases heq : t = Sched.nodeW st sc (L.cpu sc) layout.node.CUR_THREAD
  · simp only [heq, decide_true, ↓reduceIte]
    have hAc : Notif.ActReady σc := Sched.VK.actReady hA1 (vk_of hKac hac)
    obtain ⟨σ2, hres, hK2, hdl2, hds2⟩ := rescheduleRequired_k hAc
    refine WP.spec_mono (WP.spec_and (WP.spec_and (Sched.reschedule_required_refines sc σc hNc hSc hAc)
      (Sched.reschedule_required_sfootI hSc)) (spec_self (Sched.reschedule_required_sfootI hSc))) ?_
    rintro s2 ⟨⟨-, hw2⟩, hrun2⟩
    rw [heq] at post
    exact post s2 σ2 hw2 (schedStep_resched hAc hrun2 hres hK2 hdl2 hds2) hK2 hdl2 hds2
      (mem_whenP (fun _ => by rw [hres]; rfl) (fun h => absurd (by rw [hct1]) h))
  · simp only [heq, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact post sc σc (P1.WritesIn.refl _ _) (same_schedStep (P1.WritesIn.refl _ _)) (SchedK.refl _) rfl rfl
      (mem_whenP (fun h => by
        rw [hct1] at h
        exact absurd (P1.eq_of_bv h) heq) (fun _ => rfl))

/-- **`DomXHyp` for the domain cap, discharged**: `decode_invocation_domainX`
with `DomSetHyp` and `DomResHyp` from `XTopAt` (`domSetHyp_of`,
`domResHyp_of`), at the CSpace relation of `XTopAt`; beyond the decode's
placement facts, `ActReady` (l4v `valid_sched`'s action invariant). -/
theorem decode_invocation_domainXT {AR : A → Fl4Spec.Cr3 → Prop} (arI : machine.Arch A) (hAM : ARMask arI AR)
    (hcfg : DomConfig) (s : S) (ar : A) (σ : Fl4Spec.State Unit) {Z : XSets} (hX0 : XTopAt (L := L) AR Z s ar σ)
    (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T)
    (hA : Notif.ActReady σ) (hDel : XDelNtfnHyp (L := L) arI AR Z.th)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects Z.th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = domLabelOf lbl)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel Z.th (L.mem s) x0 excs)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot .Domain blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excs buffer ct := by
  have hP := hX0.fin.1.2
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  exact decode_invocation_domainX arI hAM hcfg Z.th hX0.rel.1 s ar σ Z.G hX0.rel.2.1 hX0.rel.2.2.1
    hX0.rel.2.2.2.1 ct hct hcur (hX0.curTcb hcur).1 hact hkf hP.vs.ksb_al hksO hactK lbl slbl hlbl length buf args
    hlen hargs extra x0 hx0 excs hex (domSetHyp_of hX0 hTh hC hA hcur) (domResHyp_of hX0 hKA hTh hC hA hcur)
    rfl hX0 hKA hC hTh hDel slot blk call don fp ci sl buffer

end

end

end Fl4Proofs.P3
