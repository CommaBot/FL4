/-
P3 (DESIGN.md §9), untyped: **the composite relation across a retype of
endpoints or notifications without a reset** (l4v `invoke_untyped_corres`'s
`retype_region` + `create_cap` part, for the IPC objects; first piece of
`JUtRetHyp`, handoff/utj.md "Round 2").

* `invokeUntyped_noreset_add`: every outcome of the spec's `invoke_untyped`
  without a reset, for a type other than Untyped and PML4, is the source
  state with the window's default objects added (`SpecAdd`) and then CNodes
  changed only (`CnK`, `KeepC`), given the source and destination slots'
  objects CNodes and the window free in the spec's heap.
* `TopSR.specAdd`: the VSpace hypothesis bundle `TopSR` across fresh
  spec objects that are neither SCs nor arch objects (the old sets read
  only old objects; the machine and arch state are kept).
* `XTopAt.addStep`: `XTopAt` at the OLD sets (and a new MDB ghost) across a
  step whose FL4 writes are slot words and whose spec change is `SpecAdd`
  of such objects followed by a CNode-only change (as `XTopAt.slotStep`).
-/
import Fl4Proofs.P3.XTopStep
import Fl4Proofs.P3.ScFresh
import Fl4Proofs.P3.SpecFreeRetJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-! ## The spec's `invoke_untyped` without a reset -/

section Spec
open Fl4Spec

/-- `create_cap` changes the heap at its destination's object only. -/
theorem nko_createCap {Ps : Set ObjRef} (t : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (dev : Bool)
    (x : CslotPtr × ObjRef) (hx : x.1.1 ∈ Ps) : NKO Ps (createCap (Z := Unit) t bits untyped dev x) := by
  obtain ⟨d, o⟩ := x
  unfold createCap setCdt setOriginal
  repeat (first | exact nko_setCap _ _ hx | exact nko_doExtendedOp _ |
    exact nko_pure _ | exact nko_pure' _ | exact nko_gets _ | exact nko_get |
    exact nko_get_put (fun σ => rfl) |
    exact nko_modify (fun σ => rfl) | (refine nko_bind ?_ (fun _ => ?_)))

/-- `create_cap` changes CNodes, TCBs' caps, the CDT and the original bits only. -/
theorem nkn_createCap (t : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (dev : Bool)
    (x : CslotPtr × ObjRef) : NKN (createCap (Z := Unit) t bits untyped dev x) := by
  obtain ⟨d, o⟩ := x
  unfold createCap setCdt setOriginal
  repeat (first | exact nkn_setCap _ _ | exact nkn_doExtendedOp _ |
    exact nkn_pure _ | exact nkn_pure' _ | exact nkn_gets _ | exact nkn_get |
    exact nkn_get_put (fun σ => ⟨rfl, fun _ => Or.inl rfl⟩) |
    exact nkn_modify (fun σ => ⟨rfl, fun _ => Or.inl rfl⟩) | (refine nkn_bind ?_ (fun _ => ?_)))

/-- `mapM_x` of a step changing the heap in `Ps` only (on the list's elements). -/
theorem nko_mapMx_mem {Ps : Set ObjRef} {α β : Type} {f : α → NonDet (State Unit) β} :
    ∀ l : List α, (∀ a ∈ l, NKO Ps (f a)) → NKO Ps (NonDet.mapMx f l)
  | [], _ => nko_pure' _
  | a :: l, h => nko_bind (h a (List.mem_cons_self ..)) (fun _ => nko_mapMx_mem l (fun b hb => h b (List.mem_cons_of_mem _ hb)))

/-- CnK and the heap kept outside `Ps`. -/
def CnKO (Ps : Set ObjRef) (σ σ' : State Unit) : Prop := CnK σ σ' ∧ ∀ p ∉ Ps, σ'.kheap p = σ.kheap p

theorem nall_cnko {Ps : Set ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : NKN m) (h2 : NKO Ps m)
    (σ : State Unit) : NAll m σ (fun x => CnKO Ps σ x.2) := fun x hx => ⟨h1 σ x hx, h2 σ x hx⟩

/-- **The spec's `invoke_untyped` without a reset** (module docstring). -/
theorem invokeUntyped_noreset_add (bitsApi : ApiObjectType → Nat → Nat) (sl : CslotPtr) (pb rb : ObjRef)
    (t : ApiObjectType) (us : Nat) (slots : List CslotPtr) (dev : Bool) (σ : State Unit)
    (ht : t ≠ .untyped) (hp4 : t ≠ .archObject .pml4Obj) (Ps : Set ObjRef) (hsl : sl.1 ∈ Ps)
    (hds : ∀ d ∈ slots, d.1 ∈ Ps) (hcn : ∀ p ∈ Ps, ∃ r cs, σ.kheap p = some (.cnode r cs))
    (hfree : ∀ q ∈ regionPtrs rb slots.length (2 ^ bitsApi t us), σ.kheap q = none) :
    NAll (invokeUntypedWith (Z := Unit) bitsApi (.retype sl false pb rb t us slots dev)).run σ
      (fun y => y.1 = .ok () ∧ ∃ σB, Sched.SpecAdd σ σB (fun q => q ∈ regionPtrs rb slots.length (2 ^ bitsApi t us))
        (fun _ => defaultObject t dev us σ.curDomain) ∧ CnK σB y.2 ∧ KeepC σB y.2) := by
  set ptrs := regionPtrs rb slots.length (2 ^ bitsApi t us) with hptrs
  have hpre : NAll (NonDetE.whenE (false = true) (resetUntypedCap (Z := Unit) sl)).run σ
      (fun y => y.1 = .ok () ∧ y.2 = σ) := by
    unfold NonDetE.whenE
    rw [if_neg (by decide)]
    exact nall_det rfl ⟨rfl, rfl⟩
  unfold invokeUntypedWith
  apply nallE_bind
  refine hpre.mono (fun x ⟨hx1, hx2⟩ => ?_)
  rcases x with ⟨e | u, σr⟩
  · cases hx1
  dsimp only at hx2 ⊢
  subst hx2
  apply nall_liftE
  apply nall_bind
  refine (nall_cnko (nkn_getCap sl) (nko_getCap (Ps := Ps) sl) σr).mono (fun x hx => ?_)
  apply nall_bind; refine nall_det rfl ?_
  apply nall_bind; refine nall_det rfl ?_
  apply nall_bind
  refine (nall_cnko (nkn_setCap _ sl) (nko_setCap (Ps := Ps) _ sl hsl) _).mono (fun x2 hx2 => ?_)
  apply nall_bind
  refine nall_det (retypeRegionWith_eq bitsApi rb slots.length us t dev x2.2) ?_
  rw [if_pos ht]
  apply nall_bind
  refine nall_det (show initArchObjects (Z := Unit) t dev rb slots.length us ptrs
      (regionHeap x2.2 ptrs (defaultObject t dev us x2.2.curDomain)) =
      ({((), regionHeap x2.2 ptrs (defaultObject t dev us x2.2.curDomain))}, False) by
    unfold initArchObjects NonDet.when; rw [if_neg hp4]; rfl) ?_
  intro y hy
  have hyz : ∀ a ∈ slots.zip ptrs, NKO Ps (createCap (Z := Unit) t us sl dev a) :=
    fun a ha => nko_createCap t us sl dev a (hds _ (List.of_mem_zip ha).1)
  have h3 : CnKO Ps (regionHeap x2.2 ptrs (defaultObject t dev us x2.2.curDomain)) y.2 :=
    ⟨nkn_mapMx (fun a => nkn_createCap t us sl dev a) _ _ y hy, nko_mapMx_mem _ hyz _ y hy⟩
  refine ⟨rfl, ?_⟩
  -- the two CNode steps before the region compose
  have h01 : CnKO Ps σr x2.2 := ⟨hx.1.trans hx2.1, fun p hp => (hx2.2 p hp).trans (hx.2 p hp)⟩
  have hdom : x2.2.curDomain = σr.curDomain := by
    have e := congrArg AbstractState.curDomain h01.1.1
    exact e
  rw [hdom] at h3
  set o := defaultObject t dev us σr.curDomain
  have hPsW : ∀ p ∈ Ps, p ∉ ptrs := fun p hp hw => by
    obtain ⟨r, cs, hk⟩ := hcn p hp
    rw [hfree p hw] at hk; cases hk
  have eB : ∀ p, p ∉ ptrs → (regionHeap σr ptrs o).kheap p = σr.kheap p := fun p hp => by
    dsimp only [regionHeap]; rw [foldr_update_apply, if_neg hp]
  have eX : ∀ p, p ∉ ptrs → (regionHeap x2.2 ptrs o).kheap p = x2.2.kheap p := fun p hp => by
    dsimp only [regionHeap]; rw [foldr_update_apply, if_neg hp]
  have eW : ∀ p, p ∈ ptrs → (regionHeap σr ptrs o).kheap p = (regionHeap x2.2 ptrs o).kheap p := fun p hp => by
    dsimp only [regionHeap]; rw [foldr_update_apply, foldr_update_apply, if_pos hp, if_pos hp]
  have hC : CnK (regionHeap σr ptrs o) y.2 := by
    refine ⟨(h3.1.1.trans h01.1.1 : _), fun p => ?_⟩
    by_cases hp : p ∈ ptrs
    · rw [eW p hp]; exact h3.1.2 p
    · have := h3.1.2 p
      rw [eX p hp] at this
      rw [eB p hp]
      exact (h01.1.2 p).trans this
  refine ⟨regionHeap σr ptrs o, ⟨rfl, rfl, fun p hp => ⟨hfree p hp, ?_⟩, fun p hp => eB p hp⟩, hC,
    keepC_of hC (Ps := Ps) (fun p hp => ?_) (fun p hp => ?_)⟩
  · dsimp only [regionHeap]; rw [foldr_update_apply, if_pos hp]
  · rw [h3.2 p hp]
    by_cases hw : p ∈ ptrs
    · exact (eW p hw).symm
    · rw [eX p hw, h01.2 p hp, eB p hw]
  · rw [eB p (hPsW p hp)]; exact hcn p hp
end Spec

/-! ## `TopSR` and `XTopAt` across fresh objects -/

section Add
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}
variable {σ σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop} {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject}

/-- Fresh objects that are no SCs keep the SCs and their sizes. -/
theorem Sched.SpecAdd.szKeep (h : Sched.SpecAdd σ σ' W o) (ho : ∀ p, W p → ∀ x n, o p ≠ .schedContext x n) :
    Sched.SzKeep σ σ' := fun p x n hp => by
  rcases h.kback hp with e | ⟨hw, e⟩
  · exact ⟨x, e⟩
  · exact absurd e.symm (ho p hw x n)

theorem Sched.SpecAdd.ms (h : Sched.SpecAdd σ σ' W o) : σ'.machineState = σ.machineState := by
  have e := congrArg Fl4Spec.AbstractState.machineState h.abs; exact e

theorem Sched.SpecAdd.arch (h : Sched.SpecAdd σ σ' W o) : σ'.archState = σ.archState := by
  have e := congrArg Fl4Spec.AbstractState.archState h.abs; exact e

theorem SchedRel.specAdd {s : S} (hS : Sched.SchedRel st N T C c s σ) (h : Sched.SpecAdd σ σ' W o)
    (hz : Sched.SzKeep σ σ') : Sched.SchedRel st N T C c s σ' := by
  obtain ⟨hrq, hrel, hct, hact, hcsc, hctime, hcons, hrepr, hcdom, hdtime, hidle⟩ := h.f
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  refine ⟨hS.placed, hS.nodeNW, hS.domNW, hS.dtNW, Sched.scOut_transfer rfl hz hS.scOut,
    Sched.scDisj_transfer hz hS.scDisj, hS.actW, by rw [hact]; exact hS.act,
    by rw [hrepr]; exact hS.repr, hS.core, Q, R0, hc, ?_⟩
  refine ⟨fun p hp => by rw [hrq]; exact hs.rq p hp, fun d p hd => by rw [hrq]; exact hs.rqDom d p hd,
    by rw [hrel]; exact hs.rel, by rw [hct]; exact hs.curThread, by rw [hcsc]; exact hs.curSc,
    by rw [hctime]; exact hs.curTime, by rw [hcons]; exact hs.consumed, by rw [hcdom]; exact hs.curDom,
    fun t ht => ?_, hs.scMem, fun sc hsc => ?_, hs.idleSc, by rw [hdtime]; exact hs.domTime,
    by rw [hidle]; exact hs.idleTh⟩
  · obtain ⟨x, hk, h1⟩ := hs.tcb t ht
    exact ⟨x, h.kold hk, h1⟩
  · obtain ⟨x, n, hk, e⟩ := hs.scs sc hsc
    exact ⟨x, n, h.kold hk, e⟩

theorem EpStateRel.specAdd {m : U64 → U64} (hR : Endp.EpStateRel T E R B m σ) (h : Sched.SpecAdd σ σ' W o) :
    Endp.EpStateRel T E R B m σ' := by
  refine ⟨fun e he => ?_, fun r hr => ?_, fun t ht => ?_, fun wp hw => by rw [h.ms]; exact hR.buf wp hw⟩
  · obtain ⟨x, hk, h1⟩ := hR.ep e he
    exact ⟨x, h.kold hk, h1⟩
  · obtain ⟨x, hk, h1⟩ := hR.reply r hr
    exact ⟨x, h.kold hk, h1⟩
  · obtain ⟨x, hk, h1⟩ := hR.tcb t ht
    exact ⟨x, h.kold hk, h1⟩

theorem NtfnStateRel.specAdd {m : U64 → U64} (hR : Notif.NtfnStateRel N T m σ) (h : Sched.SpecAdd σ σ' W o) :
    Notif.NtfnStateRel N T m σ' := by
  refine ⟨fun n hn => ?_, fun t ht => ?_⟩
  · obtain ⟨x, hk, h1⟩ := hR.ntfn n hn
    exact ⟨x, h.kold hk, h1⟩
  · obtain ⟨x, hk, h1⟩ := hR.tcb t ht
    exact ⟨x, h.kold hk, h1⟩

theorem OObj.of_szKeep {s : S} (hz : Sched.SzKeep σ σ') {a : U64} (h : OObj st N T C E R B c s σ' a) :
    OObj st N T C E R B c s σ a := by
  unfold OObj at h ⊢
  rcases h with h | h | h | h | h | h | ⟨sc, hsc, x, n, hk, ho⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · obtain ⟨x0, h0⟩ := hz _ x n hk
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x0, n, h0, ho⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- **`TopSR` across fresh spec objects** that are no SCs (module docstring). -/
theorem TopSR.specAdd {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {a : A}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) (h : Sched.SpecAdd σ σ' W o)
    (ho : ∀ p, W p → ∀ x n, o p ≠ .schedContext x n) :
    TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ' := by
  have hz := h.szKeep ho
  obtain ⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hP⟩ := hS
  have har := h.arch
  have hist : σ'.interruptStates = σ.interruptStates := by
    have e := congrArg Fl4Spec.AbstractState.interruptStates h.abs; exact e
  have hin : σ'.interruptIrqNode = σ.interruptIrqNode := by
    have e := congrArg Fl4Spec.AbstractState.interruptIrqNode h.abs; exact e
  refine ⟨⟨SchedRel.specAdd hSch h hz, EpStateRel.specAdd hEp h, NtfnStateRel.specAdd hNt h,
    ⟨fun i hi => by rw [hist]; exact hIrq.st i hi, fun i hi => by rw [hin]; exact hIrq.node i hi⟩,
    fun p hp => by rw [har]; exact hIo p hp, ?_, by rw [har]; exact hAr⟩,
    { hP with disj := fun x hx => hP.disj x (OObj.of_szKeep hz hx) }⟩
  unfold KRootRel globCr3 at hKr ⊢
  rw [har]; exact hKr


set_option maxHeartbeats 4000000 in
/-- **`XTopAt` across fresh objects and a CNode-only step** (module
docstring; `XTopAt.slotStep` with the spec's fresh objects `SpecAdd σ σB W o`
first): FL4 writes only slot words, the spec adds objects that are no SCs at
fresh addresses and then changes only CNodes (`CnK`, `KeepC`), the TCBs'
VSpace slots keep their PML4 caps (if one is there after), and the CSpace relation holds after. The sets
stay the old ones (the new objects are in none of them). -/
theorem XTopAt.addStep {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a : A}
    {σB : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (hw : P1.WritesIn st s s' (Sched.SlotWd Z.th))
    (hA : Sched.SpecAdd σ σB W o) (ho : ∀ p, W p → ∀ x n, o p ≠ .schedContext x n)
    (hcn : CnK σB σ') (hkc : KeepC σB σ') {G' : MdbGhost} (hCR : CRel Z.th (L.mem s') σ' G')
    (hFI : FinInv Z.th (L.mem s') σ' G') (hMO : MdbOKV (L.ksb s) (L.mem s') G')
    (hTS : ∀ t, Z.th t = some .tcb → ∀ p asid, capAt (L.mem s') (slotOf t 1) = ok (.Pml4 p true asid) →
      capAt (L.mem s) (slotOf t 1) = ok (.Pml4 p true asid)) :
    XTopAt (L := L) AR { Z with G := G' } s' a σ' := by
  obtain ⟨⟨hS, hR, hPt, hPI, hCO⟩, ⟨hPl, -, -, hD, -, hIA, hSA⟩, -, hE⟩ := hX
  obtain ⟨hO, hms, har⟩ := ostep_of_cnk hcn hkc
  have hP := hS.2
  have hk : L.ksb s' = L.ksb s := hw.1
  have hSB := TopSR.specAdd hS hA ho
  have hS' := TopSR.step0 hSB (fun b h => slotWd_vobj hPl h) hw hO hms (by rw [har])
  have hz := hA.szKeep ho
  have hSz : Sched.SzKeep σ σ' := fun p x n hp => by
    obtain ⟨x1, h1⟩ := SzKeep.of_keepC hkc p x n hp
    exact hz p x1 n h1
  have har' : σ'.archState = σ.archState := har.trans hA.arch
  have hvw : ∀ b, VsWrite Z.P (L.ksb s) b → L.mem s' b = L.mem s b := fun b hb =>
    hw.2.2 b (hP.vo b hb).1 fun h => slotWd_inObj hPl h (hP.vo b hb)
  have hcur : σ'.curThread = σ.curThread := hO.ct.trans hA.f.2.2.1
  -- an old object other than a CNode is kept
  have hkeep : ∀ q k, σ.kheap q = some k → (∀ r cs, k ≠ .cnode r cs) → σ'.kheap q = σ.kheap q := by
    intro q k hq hnc
    rcases hkc q with e | ⟨r, cs, cs', h1, -⟩
    · rw [e, hA.kold hq, hq]
    · rw [hA.kold hq] at h1; cases h1; exact absurd rfl (hnc r cs)
  have hab : Fl4Spec.AbstractState.domainList σ'.toAbstractState = σ.domainList ∧
      Fl4Spec.AbstractState.domainStartIndex σ'.toAbstractState = σ.domainStartIndex := by
    refine ⟨?_, ?_⟩
    · have e1 := congrArg Fl4Spec.AbstractState.domainList hcn.1
      have e2 := congrArg Fl4Spec.AbstractState.domainList hA.abs
      exact e1.trans e2
    · have e1 := congrArg Fl4Spec.AbstractState.domainStartIndex hcn.1
      have e2 := congrArg Fl4Spec.AbstractState.domainStartIndex hA.abs
      exact e1.trans e2
  refine ⟨⟨hS', ?_, ?_, fun q hq lo hl => ?_, ?_⟩, ⟨hPl, hCR, hFI, ?_, by rw [hk]; exact hMO,
    by rw [hk]; exact hIA, hSA.mono hSz⟩, IpcRel.of hS'.1.2.2.1 hS'.1.2.1 (sched_sc hS'.1.1), hE.mono hk hSz⟩
  · rw [hk]
    refine hR.frame hvw (by rw [har']) fun p hp => ?_
    obtain ⟨f, hf, -⟩ := hR.pool p hp
    exact hkeep _ _ hf (fun r cs e => by cases e)
  · refine hPt.frame (fun b hb => hw.2.2 b (hP.po b hb).1 fun h => slotWd_inObj hPl h (hP.po b hb)) fun q hq => ?_
    rcases hq with hq | hq | hq | hq
    · obtain ⟨g, hg, -⟩ := hPt.l4 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
    · obtain ⟨g, hg, -⟩ := hPt.l3 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
    · obtain ⟨g, hg, -⟩ := hPt.l2 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
    · obtain ⟨g, hg, -⟩ := hPt.l1 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
  · have hwv : VsWrite Z.P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hvw _ hwv]; exact hPI q hq lo hl
  · obtain ⟨t, h1, h2, h3⟩ := hCO
    exact ⟨t, h1.trans hcur.symm, h2, fun p asid hc => h3 p asid (hTS t h2 p asid hc)⟩
  · rw [hk]
    refine hD.frame (fun o ho => ?_) hab.1 hab.2
    have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
    have h8 := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    refine hw.2.2 _ (by unfold P1.Aligned; rw [hv]; have := hP.vs.ksb_al; omega) fun h => ?_
    obtain ⟨y, hy, g1, g2⟩ := slotWd_range hPl h
    exact hIA.ks _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) y hy ⟨g1, g2⟩

end Add

end

end Fl4Proofs.P3
