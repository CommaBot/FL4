/-
P3 (DESIGN.md §9), VSpace: **Frame `Unmap`, the spec side**: l4v's
`unmap_page` for each page size (`unmapPage_noVs`, `unmapPage_s/l/h_noSlot`,
`_other`: the lookups fail or the entry does not map the frame, caught;
`_match`: the entry is cleared and the translation flushed), and
`perform_page_invocation` of a `PageUnmap` (`performUnmap_mem`,
`performUnmap_none`).
-/
import Fl4Proofs.P3.VsPdptUnmapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Spec
open Fl4Spec

theorem unmapPage_noVs {sz : VMPageSize} {asid : Asid} {v : VSpaceRef} {pp : ObjRef} {σ : State Unit}
    {e : LookupFailure} (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.error e, σ)}, False)) :
    unmapPage (Z := Unit) sz asid v pp σ = ({((), σ)}, False) := by
  unfold unmapPage
  refine (catch_err (e := e) ?_).trans rfl
  exact runE_bind_err hf

theorem catch_congr' {α ε : Type} {m m' : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α}
    {σ σ' : State Unit} (hm : ExceptT.run m σ = ExceptT.run m' σ') :
    NonDetE.catch m h σ = NonDetE.catch m' h σ' := by
  unfold NonDetE.catch NonDet.bind
  rw [hm]

theorem unmapPage_s_noSlot {asid : Asid} {v : VSpaceRef} {pp vs : ObjRef} {σ : State Unit} {e : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPtSlot (Z := Unit) vs v) σ = ({(.error e, σ)}, False)) :
    unmapPage (Z := Unit) .x64SmallPage asid v pp σ = ({((), σ)}, False) := by
  unfold unmapPage
  refine (catch_err (e := e) ?_).trans rfl
  rw [runE_bind_ok hf]
  exact runE_bind_err hl

theorem unmapPage_s_other {asid : Asid} {v : VSpaceRef} {pp vs slot : ObjRef} {σ : State Unit} {x : PTE}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPtSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPte (Z := Unit) slot σ = ({(x, σ)}, False)) (hc : checkMappingPptr pp (.vmPTE x) = false) :
    unmapPage (Z := Unit) .x64SmallPage asid v pp σ = ({((), σ)}, False) := by
  unfold unmapPage
  refine (catch_err (e := .invalidRoot) ?_).trans rfl
  rw [runE_bind_ok hf]
  dsimp only
  rw [runE_bind_ok hl, runE_bind_ok (runE_liftE hg)]
  exact runE_bind_err (by rw [runE_unlessE_false (by simp [hc])]; rfl)

theorem unmapPage_s_match {asid : Asid} {v : VSpaceRef} {pp vs slot : ObjRef} {σ σ1 : State Unit} {x : PTE}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPtSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPte (Z := Unit) slot σ = ({(x, σ)}, False)) (hc : checkMappingPptr pp (.vmPTE x) = true)
    (hs : storePte (Z := Unit) slot .invalidPTE σ = ({((), σ1)}, False)) :
    unmapPage (Z := Unit) .x64SmallPage asid v pp σ =
      doMachineOp (invalidateTranslationSingleASID v (ucast 64 asid)) σ1 := by
  unfold unmapPage
  refine (catch_congr' (σ' := σ1) (m' := NonDetE.liftE (doMachineOp (invalidateTranslationSingleASID v (ucast 64 asid))))
    ?_).trans (catch_liftE _ _ _)
  rw [runE_bind_ok hf]
  dsimp only
  rw [runE_bind_ok hl, runE_bind_ok (runE_liftE hg), runE_bind_ok (runE_unlessE_true (by simp [hc]) _ σ),
    runE_bind_ok (runE_liftE hs)]

theorem unmapPage_l_noSlot {asid : Asid} {v : VSpaceRef} {pp vs : ObjRef} {σ : State Unit} {e : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) vs v) σ = ({(.error e, σ)}, False)) :
    unmapPage (Z := Unit) .x64LargePage asid v pp σ = ({((), σ)}, False) := by
  unfold unmapPage
  refine (catch_err (e := e) ?_).trans rfl
  rw [runE_bind_ok hf]
  exact runE_bind_err hl

theorem unmapPage_l_other {asid : Asid} {v : VSpaceRef} {pp vs slot : ObjRef} {σ : State Unit} {x : PDE}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPde (Z := Unit) slot σ = ({(x, σ)}, False)) (hc : checkMappingPptr pp (.vmPDE x) = false) :
    unmapPage (Z := Unit) .x64LargePage asid v pp σ = ({((), σ)}, False) := by
  unfold unmapPage
  refine (catch_err (e := .invalidRoot) ?_).trans rfl
  rw [runE_bind_ok hf]
  dsimp only
  rw [runE_bind_ok hl, runE_bind_ok (runE_liftE hg)]
  exact runE_bind_err (by rw [runE_unlessE_false (by simp [hc])]; rfl)

theorem unmapPage_l_match {asid : Asid} {v : VSpaceRef} {pp vs slot : ObjRef} {σ σ1 : State Unit} {x : PDE}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPde (Z := Unit) slot σ = ({(x, σ)}, False)) (hc : checkMappingPptr pp (.vmPDE x) = true)
    (hs : storePde (Z := Unit) slot .invalidPDE σ = ({((), σ1)}, False)) :
    unmapPage (Z := Unit) .x64LargePage asid v pp σ =
      doMachineOp (invalidateTranslationSingleASID v (ucast 64 asid)) σ1 := by
  unfold unmapPage
  refine (catch_congr' (σ' := σ1) (m' := NonDetE.liftE (doMachineOp (invalidateTranslationSingleASID v (ucast 64 asid))))
    ?_).trans (catch_liftE _ _ _)
  rw [runE_bind_ok hf]
  dsimp only
  rw [runE_bind_ok hl, runE_bind_ok (runE_liftE hg), runE_bind_ok (runE_unlessE_true (by simp [hc]) _ σ),
    runE_bind_ok (runE_liftE hs)]

theorem unmapPage_h_noSlot {asid : Asid} {v : VSpaceRef} {pp vs : ObjRef} {σ : State Unit} {e : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPdptSlot (Z := Unit) vs v) σ = ({(.error e, σ)}, False)) :
    unmapPage (Z := Unit) .x64HugePage asid v pp σ = ({((), σ)}, False) := by
  unfold unmapPage
  refine (catch_err (e := e) ?_).trans rfl
  rw [runE_bind_ok hf]
  exact runE_bind_err hl

theorem unmapPage_h_other {asid : Asid} {v : VSpaceRef} {pp vs slot : ObjRef} {σ : State Unit} {x : PDPTE}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPdptSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPdpte (Z := Unit) slot σ = ({(x, σ)}, False)) (hc : checkMappingPptr pp (.vmPDPTE x) = false) :
    unmapPage (Z := Unit) .x64HugePage asid v pp σ = ({((), σ)}, False) := by
  unfold unmapPage
  refine (catch_err (e := .invalidRoot) ?_).trans rfl
  rw [runE_bind_ok hf]
  dsimp only
  rw [runE_bind_ok hl, runE_bind_ok (runE_liftE hg)]
  exact runE_bind_err (by rw [runE_unlessE_false (by simp [hc])]; rfl)

theorem unmapPage_h_match {asid : Asid} {v : VSpaceRef} {pp vs slot : ObjRef} {σ σ1 : State Unit} {x : PDPTE}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPdptSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPdpte (Z := Unit) slot σ = ({(x, σ)}, False)) (hc : checkMappingPptr pp (.vmPDPTE x) = true)
    (hs : storePdpte (Z := Unit) slot .invalidPDPTE σ = ({((), σ1)}, False)) :
    unmapPage (Z := Unit) .x64HugePage asid v pp σ =
      doMachineOp (invalidateTranslationSingleASID v (ucast 64 asid)) σ1 := by
  unfold unmapPage
  refine (catch_congr' (σ' := σ1) (m' := NonDetE.liftE (doMachineOp (invalidateTranslationSingleASID v (ucast 64 asid))))
    ?_).trans (catch_liftE _ _ _)
  rw [runE_bind_ok hf]
  dsimp only
  rw [runE_bind_ok hl, runE_bind_ok (runE_liftE hg), runE_bind_ok (runE_unlessE_true (by simp [hc]) _ σ),
    runE_bind_ok (runE_liftE hs)]


/-- The spec's Frame Unmap perform, for a mapped frame. -/
theorem performUnmap_mem {dev : Bool} {p : ObjRef} {R : VMRights} {sz : VMPageSize} {asid : Asid} {va : VSpaceRef}
    {pc : ObjRef} {idx : List Bool} {r : Nat} {cs : CnodeContents} {σ1 σu : State Unit}
    (hnu : ¬ (unmapPage (Z := Unit) sz asid va p σ1).2)
    (hall : ∀ x σ, (x, σ) ∈ (unmapPage (Z := Unit) sz asid va p σ1).1 → σ.kheap pc = σ1.kheap pc)
    (hu : ((), σu) ∈ (unmapPage (Z := Unit) sz asid va p σ1).1)
    (hkc : σ1.kheap pc = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r)
    (hcs : cs idx = some (.archObjectCap (.pageCap dev p R .vmVSpaceMap sz (some (asid, va))))) :
    (([] : List Data), setCnodeSlot σu pc r cs idx (.archObjectCap (.pageCap dev p R .vmNoMap sz none))) ∈
      (performPageInvocation (Z := Unit) (.pageUnmap (.pageCap dev p R .vmVSpaceMap sz (some (asid, va))) (pc, idx)) σ1).1 ∧
    ¬ (performPageInvocation (Z := Unit)
        (.pageUnmap (.pageCap dev p R .vmVSpaceMap sz (some (asid, va))) (pc, idx)) σ1).2 := by
  have tailCap : ∀ σ : State Unit, σ.kheap pc = some (.cnode r cs) →
      (NonDet.liftM Cap.theArchCap (getCap (Z := Unit) (pc, idx)) >>= fun cap =>
        setCap (Cap.archObjectCap (updateMapData cap none (some .vmNoMap))) (pc, idx)) σ =
      ({((), setCnodeSlot σ pc r cs idx (.archObjectCap (.pageCap dev p R .vmNoMap sz none)))}, False) := by
    intro σ hk
    rw [nd_bind_one (by unfold NonDet.liftM; rw [nd_bind_one' (getCap_cnode hk hwf hcs)]; rfl)]
    exact setCap_cnode _ hk hwf hidx
  unfold performPageInvocation performPageInvocationUnmap
  dsimp only
  rw [nd_bind_apply', nd_bind_apply']
  refine ⟨⟨((), setCnodeSlot σu pc r cs idx (.archObjectCap (.pageCap dev p R .vmNoMap sz none))),
    ⟨((), σu), hu, ?_⟩, by simp [pure, NonDet.pure]⟩, ?_⟩
  · rw [tailCap _ ((hall _ _ hu).trans hkc)]; rfl
  · rintro ((h | ⟨y, hy, h⟩) | ⟨y, hy, h⟩)
    · exact hnu h
    · rw [tailCap _ ((hall _ _ hy).trans hkc)] at h; exact h
    · simp [pure, NonDet.pure] at h

/-- The spec's Frame Unmap perform, for an unmapped frame. -/
theorem performUnmap_none {dev : Bool} {p : ObjRef} {R : VMRights} {mt : VMMapType} {sz : VMPageSize}
    {cte : CslotPtr} {σ1 : State Unit} :
    performPageInvocation (Z := Unit) (.pageUnmap (.pageCap dev p R mt sz none) cte) σ1 =
      ({(([] : List Data), σ1)}, False) := by
  unfold performPageInvocation
  rfl

end Spec

end

end Fl4Proofs.P3.Vs
