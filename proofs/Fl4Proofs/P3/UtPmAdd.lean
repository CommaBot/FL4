/-
P3 (DESIGN.md §9), untyped: **the pieces of a no-reset retype of PML4s at
`J`** (handoff/utj.md "uttypes (line ut22-)"; l4v `invoke_untyped_corres`
with `init_arch_objects`' `copy_global_mappings`).

* `initArch_pml4H`: `initArch_pml4` with the new PML4s still PML4s after.
* `invokeUntyped_noreset_pml4`: every outcome of the spec's `invoke_untyped`
  without a reset for PML4s is the source state with the window's new PML4s
  added (`SpecAdd`, each object a PML4: the default one with the global
  mappings copied in) and then CNodes changed only (`CnK`, `KeepC`), given the
  window free in the spec's heap and aligned, and the global PML4 a PML4
  object of the spec.
-/
import Fl4Proofs.P3.UtScAdd
import Fl4Proofs.P3.UntypedPml4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

/-- **`init_arch_objects` for new PML4s**, keeping them PML4s (`initArch_pml4`
with its invariant returned). -/
theorem initArch_pml4H (σ : State Unit) (dev : Bool) (ptr : ObjRef) (n sz : Nat) (refs : List ObjRef)
    (hg : HasPm σ σ.archState.x64GlobalPml4)
    (hga : σ.archState.x64GlobalPml4.toNat % 4096 = 0) (hgf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64)
    (hgr : σ.archState.x64GlobalPml4 ∉ refs)
    (hr : ∀ q ∈ refs, HasPm σ q ∧ q.toNat % 4096 = 0 ∧ q.toNat + 4096 ≤ 2 ^ 64) :
    ∃ k, initArchObjects (Z := Unit) (.archObject .pml4Obj) dev ptr n sz refs σ = ({((), { σ with kheap := k })}, False) ∧
      (∀ x, x ∉ refs → k x = σ.kheap x) ∧ ∀ q ∈ refs, HasPm { σ with kheap := k } q := by
  unfold initArchObjects
  simp only [NonDet.when, ↓reduceIte]
  suffices ∀ (L : List ObjRef) (k0 : ObjRef → Option KernelObject), (∀ q ∈ L, q ∈ refs) →
      (∀ x, x ∉ refs → k0 x = σ.kheap x) → (∀ q ∈ refs, HasPm { σ with kheap := k0 } q) →
      ∃ k, NonDet.mapMx copyGlobalMappings L { σ with kheap := k0 } = ({((), { σ with kheap := k })}, False) ∧
        (∀ x, x ∉ refs → k x = σ.kheap x) ∧ ∀ q ∈ refs, HasPm { σ with kheap := k } q by
    exact this refs σ.kheap (fun _ h => h) (fun _ _ => rfl) (fun q hq => (hr q hq).1)
  intro L
  induction L with
  | nil => intro k0 _ h1 h2; exact ⟨k0, rfl, h1, h2⟩
  | cons q L ih =>
    intro k0 hL h1 h2
    have hq := hL q (List.mem_cons_self ..)
    have hg0 : HasPm { σ with kheap := k0 } σ.archState.x64GlobalPml4 := by
      obtain ⟨pt, hpt⟩ := hg; exact ⟨pt, by show k0 _ = _; rw [h1 _ hgr]; exact hpt⟩
    obtain ⟨k1, hk1, hk1o, hH⟩ := copyGM_det { σ with kheap := k0 } q hg0 hga hgf (h2 q hq) (hr q hq).2.1 (hr q hq).2.2
    simp only [NonDet.mapMx]
    rw [ndb_one hk1]
    refine ih k1 (fun x hx => hL x (List.mem_cons_of_mem _ hx)) (fun x hx => ?_) (fun r hr' => ?_)
    · rw [hk1o x (fun e => hx (e ▸ hq))]; exact h1 x hx
    · by_cases hrq : r = q
      · subst hrq; exact hH
      · obtain ⟨pt, hpt⟩ := h2 r hr'
        exact ⟨pt, by show k1 r = _; rw [hk1o r hrq]; exact hpt⟩

/-- **The spec's `invoke_untyped` without a reset, for PML4s** (module
docstring). -/
theorem invokeUntyped_noreset_pml4 (bitsApi : ApiObjectType → Nat → Nat) (sl : CslotPtr) (pb rb : ObjRef)
    (us : Nat) (slots : List CslotPtr) (dev : Bool) (σ : State Unit)
    (Ps : Set ObjRef) (hsl : sl.1 ∈ Ps)
    (hds : ∀ d ∈ slots, d.1 ∈ Ps) (hcn : ∀ p ∈ Ps, ∃ r cs, σ.kheap p = some (.cnode r cs))
    (hfree : ∀ q ∈ regionPtrs rb slots.length (2 ^ bitsApi (.archObject .pml4Obj) us), σ.kheap q = none)
    (hal : ∀ q ∈ regionPtrs rb slots.length (2 ^ bitsApi (.archObject .pml4Obj) us),
      q.toNat % 4096 = 0 ∧ q.toNat + 4096 ≤ 2 ^ 64)
    (hg : HasPm σ σ.archState.x64GlobalPml4)
    (hga : σ.archState.x64GlobalPml4.toNat % 4096 = 0) (hgf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64) :
    NAll (invokeUntypedWith (Z := Unit) bitsApi (.retype sl false pb rb (.archObject .pml4Obj) us slots dev)).run σ
      (fun y => y.1 = .ok () ∧ ∃ σB o,
        Sched.SpecAdd σ σB (fun q => q ∈ regionPtrs rb slots.length (2 ^ bitsApi (.archObject .pml4Obj) us)) o ∧
        (∀ q, q ∈ regionPtrs rb slots.length (2 ^ bitsApi (.archObject .pml4Obj) us) →
          ∃ pt, o q = .archObj (.pageMapL4 pt)) ∧
        CnK σB y.2 ∧ KeepC σB y.2) := by
  set ptrs := regionPtrs rb slots.length (2 ^ bitsApi (.archObject .pml4Obj) us) with hptrs
  have hpre : NAll (NonDetE.whenE (false = true) (resetUntypedCap (Z := Unit) sl)).run σ
      (fun y => y.1 = .ok () ∧ y.2 = σ) := by
    unfold NonDetE.whenE
    rw [if_neg (by decide)]
    exact nall_det rfl ⟨rfl, rfl⟩
  have hgP : σ.archState.x64GlobalPml4 ∉ Ps := fun h => by
    obtain ⟨r, cs, hk⟩ := hcn _ h; obtain ⟨pt, hpt⟩ := hg; rw [hk] at hpt; cases hpt
  have hgW : σ.archState.x64GlobalPml4 ∉ ptrs := fun h => by
    obtain ⟨pt, hpt⟩ := hg; rw [hfree _ h] at hpt; cases hpt
  have hPsW : ∀ p ∈ Ps, p ∉ ptrs := fun p hp hw => by
    obtain ⟨r, cs, hk⟩ := hcn p hp
    rw [hfree p hw] at hk; cases hk
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
  refine nall_det (retypeRegionWith_eq bitsApi rb slots.length us (.archObject .pml4Obj) dev x2.2) ?_
  rw [if_pos (by simp)]
  have h01 : CnKO Ps σr x2.2 := ⟨hx.1.trans hx2.1, fun p hp => (hx2.2 p hp).trans (hx.2 p hp)⟩
  have har0 : x2.2.archState = σr.archState := by
    have e := congrArg AbstractState.archState h01.1.1
    exact e
  set o0 := defaultObject (.archObject .pml4Obj) dev us x2.2.curDomain with ho0
  have hR0 : ∀ q, (regionHeap x2.2 ptrs o0).kheap q = if q ∈ ptrs then some o0 else x2.2.kheap q := fun q => by
    dsimp only [regionHeap]; rw [foldr_update_apply]
  have hg0 : HasPm (regionHeap x2.2 ptrs o0) (regionHeap x2.2 ptrs o0).archState.x64GlobalPml4 := by
    show HasPm _ x2.2.archState.x64GlobalPml4
    rw [har0]
    obtain ⟨pt, hpt⟩ := hg
    exact ⟨pt, by rw [hR0, if_neg hgW, h01.2 _ hgP]; exact hpt⟩
  have hr0 : ∀ q ∈ ptrs, HasPm (regionHeap x2.2 ptrs o0) q ∧ q.toNat % 4096 = 0 ∧ q.toNat + 4096 ≤ 2 ^ 64 :=
    fun q hq => ⟨⟨fun _ => .invalidPML4E, by rw [hR0, if_pos hq]; rfl⟩, hal q hq⟩
  obtain ⟨k, hk, hko, hkH⟩ := initArch_pml4H (regionHeap x2.2 ptrs o0) dev rb slots.length us ptrs hg0
    (by show x2.2.archState.x64GlobalPml4.toNat % 4096 = 0; rw [har0]; exact hga)
    (by show x2.2.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64; rw [har0]; exact hgf)
    (by show x2.2.archState.x64GlobalPml4 ∉ ptrs; rw [har0]; exact hgW) hr0
  apply nall_bind
  refine nall_det hk ?_
  intro y hy
  have hyz : ∀ a ∈ slots.zip ptrs, NKO Ps (createCap (Z := Unit) (.archObject .pml4Obj) us sl dev a) :=
    fun a ha => nko_createCap _ us sl dev a (hds _ (List.of_mem_zip ha).1)
  have h3 : CnKO Ps { regionHeap x2.2 ptrs o0 with kheap := k } y.2 :=
    ⟨nkn_mapMx (fun a => nkn_createCap _ us sl dev a) _ _ y hy, nko_mapMx_mem _ hyz _ y hy⟩
  refine ⟨rfl, ?_⟩
  have hkx : ∀ q, q ∉ ptrs → k q = x2.2.kheap q := fun q hq => by rw [hko q hq, hR0, if_neg hq]
  refine ⟨{ σr with kheap := fun q => if q ∈ ptrs then k q else σr.kheap q }, fun q => (k q).getD o0, ?_⟩
  have hkW : ∀ q ∈ ptrs, k q = some ((k q).getD o0) := fun q hq => by
    obtain ⟨pt, hpt⟩ := hkH q hq
    have e : k q = some (.archObj (.pageMapL4 pt)) := hpt
    rw [e]; rfl
  have hC : CnK { σr with kheap := fun q => if q ∈ ptrs then k q else σr.kheap q } y.2 := by
    refine ⟨(h3.1.1.trans h01.1.1 : _), fun p => ?_⟩
    have h3p : ObjCn (k p) (y.2.kheap p) := h3.1.2 p
    by_cases hp : p ∈ ptrs
    · show ObjCn (if p ∈ ptrs then k p else σr.kheap p) _
      rw [if_pos hp]; exact h3p
    · show ObjCn (if p ∈ ptrs then k p else σr.kheap p) _
      rw [if_neg hp]
      rw [hkx p hp] at h3p
      exact (h01.1.2 p).trans h3p
  refine ⟨⟨rfl, rfl, fun p hp => ⟨hfree p hp, ?_⟩, fun p hp => ?_⟩, fun q hq => ?_, hC,
    keepC_of hC (Ps := Ps) (fun p hp => ?_) (fun p hp => ?_)⟩
  · show (if p ∈ ptrs then k p else σr.kheap p) = _
    rw [if_pos hp]; exact hkW p hp
  · show (if p ∈ ptrs then k p else σr.kheap p) = _
    rw [if_neg hp]
  · obtain ⟨pt, hpt⟩ := hkH q hq
    have e : k q = some (.archObj (.pageMapL4 pt)) := hpt
    exact ⟨pt, by show (k q).getD o0 = _; rw [e]; rfl⟩
  · have e : y.2.kheap p = k p := h3.2 p hp
    rw [e]
    show k p = if p ∈ ptrs then k p else σr.kheap p
    by_cases hw : p ∈ ptrs
    · rw [if_pos hw]
    · rw [if_neg hw, hkx p hw, h01.2 p hp]
  · show ∃ r cs, (if p ∈ ptrs then k p else σr.kheap p) = _
    rw [if_neg (hPsW p hp)]; exact hcn p hp

end Spec

/-! ## `XTopAt` across fresh objects, a CNode-only step and window writes -/

section Add
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {σ σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop} {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject}

set_option maxHeartbeats 4000000 in
/-- **`XTopAt` across fresh objects, a CNode-only step and writes to a
window** (`XTopAt.addStep` with FL4 also writing words `Win`: the new PML4s'
kernel half): the window's words are none the relations read (`¬ OObj`,
`¬ VObj`) and miss the kernel-state block. -/
theorem XTopAt.addStepW {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a : A}
    {σB : Fl4Spec.State Unit} {Win : U64 → Prop}
    (hX : XTopAt (L := L) AR Z s a σ) (hw : P1.WritesIn st s s' (fun b => Sched.SlotWd Z.th b ∨ Win b))
    (hWin : ∀ b, Win b → ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b ∧
      ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b)
    (hWk : ∀ b, Win b → b.val < (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ b.val)
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
  have hz := hA.szKeep ho
  have hkW : ∀ b, P1.Aligned b → ¬ Sched.SlotWd Z.th b → ¬ Win b → L.mem s' b = L.mem s b :=
    fun b hb h1 h2 => hw.2.2 b hb (fun h => h.elim h1 h2)
  have hS' := TopSR.step (Rw := Win) (Rg := fun _ => False) hSB hw.1 hw.2.1
    (fun b hb hv hr => hkW b hb (fun h => hv (slotWd_vobj hPl h)) hr)
    (fun b hb ho' => (hWin b hb).1 (OObj.of_szKeep hz ho')) hO (fun _ h => h.elim)
    (fun wp _ => by rw [hms]) (fun h => by rw [har]; exact h)
  have hSz : Sched.SzKeep σ σ' := fun p x n hp => by
    obtain ⟨x1, h1⟩ := SzKeep.of_keepC hkc p x n hp
    exact hz p x1 n h1
  have har' : σ'.archState = σ.archState := har.trans hA.arch
  have hvw : ∀ b, VsWrite Z.P (L.ksb s) b → L.mem s' b = L.mem s b := fun b hb =>
    hkW b (hP.vo b hb).1 (fun h => slotWd_inObj hPl h (hP.vo b hb))
      (fun h => (hWin b h).2 (vsWrite_vobj hP.vs hb))
  have hcur : σ'.curThread = σ.curThread := hO.ct.trans hA.f.2.2.1
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
  · refine hPt.frame (fun b hb => hkW b (hP.po b hb).1 (fun h => slotWd_inObj hPl h (hP.po b hb)) (fun h => ?_))
      fun q hq => ?_
    · obtain ⟨q, hq, i, hi, e⟩ := hb
      exact (hWin b h).2 (e ▸ table_vobj hP.pt hq hi _)
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
    refine hkW _ (by unfold P1.Aligned; rw [hv]; have := hP.vs.ksb_al; omega) (fun h => ?_) (fun h => ?_)
    · obtain ⟨y, hy, g1, g2⟩ := slotWd_range hPl h
      exact hIA.ks _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) y hy ⟨g1, g2⟩
    · rcases hWk _ h with h' | h' <;> rw [hv] at h' <;> omega

end Add

end

end Fl4Proofs.P3
