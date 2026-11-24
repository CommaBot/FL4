/-
P3 (DESIGN.md §9): **spec steps that change TCBs only in their cap fields**,
for the deletion's slot edits at the composite relation (a revoked
descendant or a dying thread's own slots live in TCB slots).

The other subsystems' relations read the TCBs' non-cap fields only (the
state, the registers, the priority, the domain, the scheduling context, the
yield target), so they carry over (`TcbNonCapEq` and its bridges).

* `TcbNonCapEq`, `TcbCapStep`: TCB entries changed in their caps only, the
  rest of the state kept.
* `SchedRel.tcbFrame`, `EpStateRel.tcbFrame`, `NtfnStateRel.tcbFrame`,
  `TopSR.tcbStep`: the relations across such a step.
* `XTopAt.slotStepT`: `XTopAt.slotStep` for any `CnK` slot edit (CNode or
  TCB slots), with `CurOK` after as a premise (`CurOK.of_slot1`, or
  VsTopX's `CurOK.of_inv'` when the current thread's VSpace slot changes).
-/
import Fl4Proofs.P3.XTopStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Ipc

noncomputable section

/-- `x'` is `x` but for the six cap fields (SpecCnK's `CapsOnly`, which
`CnK` allows at TCBs). -/
abbrev TcbNonCapEq (x x' : Fl4Spec.Tcb) : Prop := Ipc.CapsOnly x x'

/-- The bridge: a TCB alike but for its caps is `x` with the caps replaced. -/
theorem TcbNonCapEq.eq {x x' : Fl4Spec.Tcb} (h : TcbNonCapEq x x') :
    x' = { x with
      tcbCtable := x'.tcbCtable, tcbVtable := x'.tcbVtable, tcbIpcframe := x'.tcbIpcframe,
      tcbFaultHandler := x'.tcbFaultHandler, tcbTimeoutHandler := x'.tcbTimeoutHandler, tcbEpt := x'.tcbEpt } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  cases x; cases x'
  simp_all

/-- **A spec step changing TCBs in their caps only**: `σ` is `σ'` with
another heap, which agrees with `σ'`'s but at TCBs whose non-cap fields
agree. -/
def TcbCapStep (σ σ' : Fl4Spec.State Unit) : Prop :=
  ∃ k, σ = { σ' with kheap := k } ∧ ∀ p, σ'.kheap p = k p ∨
    ∃ x x', k p = some (.tcb x) ∧ σ'.kheap p = some (.tcb x') ∧ TcbNonCapEq x x'

theorem TcbCapStep.szKeep {σ σ' : Fl4Spec.State Unit} (h : TcbCapStep σ σ') : Sched.SzKeep σ σ' := by
  obtain ⟨k, rfl, hk⟩ := h
  intro p x n hp
  rcases hk p with e | ⟨y, y', -, h2, -⟩
  · exact ⟨x, by change k p = _; rw [← e]; exact hp⟩
  · rw [h2] at hp; cases hp

/-- A non-TCB entry, or a TCB entry read through its non-cap fields. -/
theorem TcbCapStep.keep {σ σ' : Fl4Spec.State Unit} (h : TcbCapStep σ σ') {p : Fl4Spec.ObjRef}
    {o : Fl4Spec.KernelObject} (hp : σ.kheap p = some o) (ho : ∀ x, o ≠ .tcb x) : σ'.kheap p = some o := by
  obtain ⟨k, rfl, hk⟩ := h
  rcases hk p with e | ⟨y, y', h1, -, -⟩
  · rw [e]; exact hp
  · change k p = some o at hp
    rw [hp] at h1; cases h1; exact absurd rfl (ho y)

theorem TcbCapStep.tcb {σ σ' : Fl4Spec.State Unit} (h : TcbCapStep σ σ') {p : Fl4Spec.ObjRef}
    {x : Fl4Spec.Tcb} (hp : σ.kheap p = some (.tcb x)) : ∃ x', σ'.kheap p = some (.tcb x') ∧ TcbNonCapEq x x' := by
  obtain ⟨k, rfl, hk⟩ := h
  change k p = some (.tcb x) at hp
  rcases hk p with e | ⟨y, y', h1, h2, h3⟩
  · exact ⟨x, by rw [e]; exact hp, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · rw [hp] at h1; cases h1; exact ⟨y', h2, h3⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem SchedRel.tcbFrame {s : S} {σ σ' : Fl4Spec.State Unit} (hS : Sched.SchedRel st N T C c s σ)
    (h : TcbCapStep σ σ') : Sched.SchedRel st N T C c s σ' := by
  have hz := h.szKeep
  have hT := h
  obtain ⟨k, rfl, -⟩ := hT
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  refine ⟨hS.placed, hS.nodeNW, hS.domNW, hS.dtNW, Sched.scOut_transfer rfl hz hS.scOut,
    Sched.scDisj_transfer hz hS.scDisj, hS.actW, hS.act, hS.repr, hS.core, Q, R0, hc, ?_⟩
  refine ⟨fun p hp => hs.rq p hp, fun d p hd => hs.rqDom d p hd, hs.rel, hs.curThread, hs.curSc,
    hs.curTime, hs.consumed, hs.curDom, fun t ht => ?_, hs.scMem, fun sc hsc => ?_, hs.idleSc, hs.domTime,
    hs.idleTh⟩
  · obtain ⟨x, hk, h1⟩ := hs.tcb t ht
    obtain ⟨x', hk', hx⟩ := h.tcb hk
    refine ⟨x', hk', ?_⟩
    rw [hx.eq]; exact h1
  · obtain ⟨x, n, hk, e⟩ := hs.scs sc hsc
    exact ⟨x, n, h.keep hk (fun _ e => by cases e), e⟩

theorem EpStateRel.tcbFrame {m : U64 → U64} {σ σ' : Fl4Spec.State Unit} (hR : Endp.EpStateRel T E R B m σ)
    (h : TcbCapStep σ σ') : Endp.EpStateRel T E R B m σ' := by
  have hT := h
  obtain ⟨k, rfl, -⟩ := hT
  refine ⟨fun e he => ?_, fun r hr => ?_, fun t ht => ?_, fun wp hw => hR.buf wp hw⟩
  · obtain ⟨x, hk, h1⟩ := hR.ep e he
    exact ⟨x, h.keep hk (fun _ e => by cases e), h1⟩
  · obtain ⟨x, hk, h1⟩ := hR.reply r hr
    exact ⟨x, h.keep hk (fun _ e => by cases e), h1⟩
  · obtain ⟨x, hk, h1⟩ := hR.tcb t ht
    obtain ⟨x', hk', hx⟩ := h.tcb hk
    refine ⟨x', hk', ?_⟩
    rw [hx.eq]; exact { h1 with }

theorem NtfnStateRel.tcbFrame {m : U64 → U64} {σ σ' : Fl4Spec.State Unit} (hR : Notif.NtfnStateRel N T m σ)
    (h : TcbCapStep σ σ') : Notif.NtfnStateRel N T m σ' := by
  refine ⟨fun n hn => ?_, fun t ht => ?_⟩
  · obtain ⟨x, hk, h1⟩ := hR.ntfn n hn
    exact ⟨x, h.keep hk (fun _ e => by cases e), h1⟩
  · obtain ⟨x, hk, h1⟩ := hR.tcb t ht
    obtain ⟨x', hk', hx⟩ := h.tcb hk
    refine ⟨x', hk', ?_⟩
    rw [hx.eq]; exact { h1 with }

theorem OObj.of_tcbStep {s : S} {σ σ' : Fl4Spec.State Unit} (h : TcbCapStep σ σ') {a : U64}
    (ho : OObj st N T C E R B c s σ' a) : OObj st N T C E R B c s σ a := by
  unfold OObj at ho ⊢
  rcases ho with h' | h' | h' | h' | h' | h' | ⟨sc, hsc, x, n, hk, ho⟩ | h'
  · exact Or.inl h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr (Or.inl h'))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))
  swap
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))))
  obtain ⟨x0, hx0⟩ := h.szKeep _ _ _ hk
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x0, n, hx0, ho⟩))))))

/-- **The composite `SR` across a TCB-cap-only spec step.** -/
theorem TopSR.tcbStep {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {s : S} {a : A} {σ σ' : Fl4Spec.State Unit}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) (h : TcbCapStep σ σ') :
    TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ' := by
  obtain ⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hP⟩ := hS
  have hT := h
  obtain ⟨k, rfl, -⟩ := hT
  exact ⟨⟨SchedRel.tcbFrame hSch h, EpStateRel.tcbFrame hEp h, NtfnStateRel.tcbFrame hNt h,
    ⟨fun i hi => hIrq.st i hi, fun i hi => hIrq.node i hi⟩, fun p hp => hIo p hp,
    by unfold KRootRel KRootW HugeRel globCr3 at hKr ⊢; exact hKr, hAr⟩,
    ⟨hP.ep, hP.vs, hP.pt, hP.pl, fun x hx => hP.disj x (OObj.of_tcbStep h hx), hP.nodeE,
      hP.po, hP.ps, hP.pv, hP.vo, hP.sd, hP.tko⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- `CurOK` after a step keeping the current thread and its VSpace slot's
cap (`XTopAt.slotStepT`'s premise when the edit misses that slot; otherwise
`CurOK.of_inv'`). -/
theorem CurOK.of_slot1 {th : TypedHeap} {s s' : S} {σ σ' : Fl4Spec.State Unit} (hC : CurOK st th s σ)
    (hct : σ'.curThread = σ.curThread)
    (h : ∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 1) = capAt (L.mem s) (slotOf t 1)) :
    CurOK st th s' σ' := by
  obtain ⟨t, h1, h2, h3⟩ := hC
  exact ⟨t, h1.trans hct.symm, h2, fun p asid hc => h3 p asid (by rwa [h t h2] at hc)⟩

set_option maxHeartbeats 4000000 in
/-- **`XTopAt` across a slot edit** (CNode or TCB slots): FL4 writes only
slot words, the spec's step is `CnK` (CNodes, and TCBs in their caps only),
the CSpace relation and the current thread's `CurOK` hold after. As
`XTopAt.slotStep`, through the spec state with the TCBs' old caps (a
CNode-only step), then `TopSR.tcbStep`. -/
theorem XTopAt.slotStepT {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a : A}
    {σ σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) (hw : P1.WritesIn st s s' (Sched.SlotWd Z.th))
    (hcn : CnK σ σ') {G' : MdbGhost} (hCR : CRel Z.th (L.mem s') σ' G') (hFI : FinInv Z.th (L.mem s') σ' G')
    (hMO : MdbOKV (L.ksb s) (L.mem s') G') (hCO' : CurOK st Z.th s' σ') :
    XTopAt (L := L) AR { Z with G := G' } s' a σ' := by
  obtain ⟨⟨hS, hR, hPt, hPI, -⟩, ⟨hPl, -, -, hD, -, hIA, hSA⟩, -, hE⟩ := hX
  let km : Fl4Spec.KHeap := fun p =>
    if (∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧ CapsOnly x y) then σ.kheap p
    else σ'.kheap p
  let σm : Fl4Spec.State Unit := { σ' with kheap := km }
  have hcnm : CnK σ σm := by
    refine ⟨(rfl : abs0 σm = abs0 σ').trans hcn.1, fun p => ?_⟩
    show ObjCn (σ.kheap p) (km p)
    by_cases hc : ∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧ CapsOnly x y
    · simp only [km, if_pos hc]; exact Or.inl rfl
    · simp only [km, if_neg hc]; exact hcn.2 p
  have hkcm : KeepC σ σm := by
    intro p
    by_cases hc : ∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧ CapsOnly x y
    · exact Or.inl (if_pos hc)
    · have e : km p = σ'.kheap p := if_neg hc
      rcases hcn.2 p with e' | ⟨r, cs, cs', h1, h2⟩ | ⟨x, y, h1, h2, h3⟩
      · exact Or.inl (e.trans e')
      · exact Or.inr ⟨r, cs, cs', h1, e.trans h2⟩
      · exact absurd ⟨x, y, h1, h2, h3⟩ hc
  have hTC : TcbCapStep σm σ' := by
    refine ⟨km, rfl, fun p => ?_⟩
    by_cases hc : ∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧ CapsOnly x y
    · obtain ⟨x, y, h1, h2, h3⟩ := hc
      right
      refine ⟨x, y, ?_, h2, h3⟩
      simp only [km]; rw [if_pos ⟨x, y, h1, h2, h3⟩]; exact h1
    · left; simp only [km, if_neg hc]
  obtain ⟨hO, hms, har⟩ := ostep_of_cnk hcnm hkcm
  have har' : σ'.archState = σ.archState := har
  have hP := hS.2
  have hk : L.ksb s' = L.ksb s := hw.1
  have hS' := TopSR.tcbStep (TopSR.step0 hS (fun b h => slotWd_vobj hPl h) hw hO hms (by rw [har])) hTC
  have hSz : Sched.SzKeep σ σ' := by
    intro p x n hp
    rcases hcn.2 p with e | ⟨r, cs, cs', h1, h2⟩ | ⟨y, y', h1, h2, -⟩
    · exact ⟨x, e ▸ hp⟩
    · rw [h2] at hp; cases hp
    · rw [h2] at hp; cases hp
  have hvw : ∀ b, VsWrite Z.P (L.ksb s) b → L.mem s' b = L.mem s b := fun b hb =>
    hw.2.2 b (hP.vo b hb).1 fun h => slotWd_inObj hPl h (hP.vo b hb)
  have hkeep : ∀ q : Fl4Spec.ObjRef, (∀ r cs, σ.kheap q ≠ some (.cnode r cs)) → (∀ x, σ.kheap q ≠ some (.tcb x)) →
      σ'.kheap q = σ.kheap q := by
    intro q h1 h2
    rcases hcn.2 q with e | ⟨r, cs, cs', e1, -⟩ | ⟨x, y, e1, -, -⟩
    · exact e
    · exact absurd e1 (h1 r cs)
    · exact absurd e1 (h2 x)
  refine ⟨⟨hS', ?_, ?_, fun q hq lo hl => ?_, hCO'⟩, ⟨hPl, hCR, hFI, ?_, by rw [hk]; exact hMO,
    by rw [hk]; exact hIA, hSA.mono hSz⟩, IpcRel.of hS'.1.2.2.1 hS'.1.2.1 (sched_sc hS'.1.1), hE.mono hk hSz⟩
  · rw [hk]
    refine hR.frame hvw (by rw [har']) fun p hp => ?_
    obtain ⟨f, hf, -⟩ := hR.pool p hp
    exact hkeep _ (fun r cs h => by rw [hf] at h; cases h) (fun x h => by rw [hf] at h; cases h)
  · refine hPt.frame (fun b hb => hw.2.2 b (hP.po b hb).1 fun h => slotWd_inObj hPl h (hP.po b hb)) fun q hq => ?_
    rcases hq with hq | hq | hq | hq
    · obtain ⟨g, hg, -⟩ := hPt.l4 q hq
      exact hkeep _ (fun r cs h => by rw [hg] at h; cases h) (fun x h => by rw [hg] at h; cases h)
    · obtain ⟨g, hg, -⟩ := hPt.l3 q hq
      exact hkeep _ (fun r cs h => by rw [hg] at h; cases h) (fun x h => by rw [hg] at h; cases h)
    · obtain ⟨g, hg, -⟩ := hPt.l2 q hq
      exact hkeep _ (fun r cs h => by rw [hg] at h; cases h) (fun x h => by rw [hg] at h; cases h)
    · obtain ⟨g, hg, -⟩ := hPt.l1 q hq
      exact hkeep _ (fun r cs h => by rw [hg] at h; cases h) (fun x h => by rw [hg] at h; cases h)
  · have hwv : VsWrite Z.P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hvw _ hwv]; exact hPI q hq lo hl
  · rw [hk]
    refine hD.frame (fun o ho => ?_) (by have e := congrArg Fl4Spec.AbstractState.domainList hcn.1; exact e)
      (by have e := congrArg Fl4Spec.AbstractState.domainStartIndex hcn.1; exact e)
    have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
    have h8 := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    refine hw.2.2 _ (by unfold P1.Aligned; rw [hv]; have := hP.vs.ksb_al; omega) fun h => ?_
    obtain ⟨y, hy, g1, g2⟩ := slotWd_range hPl h
    exact hIA.ks _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) y hy ⟨g1, g2⟩

end

end

end Fl4Proofs.P3
