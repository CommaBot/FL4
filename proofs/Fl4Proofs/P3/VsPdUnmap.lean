/-
P3 (DESIGN.md §9), VSpace: **PageDirectory `Unmap`, the spec side**
(VsPtUnmap one level up): the decode, `unmap_pd` (whose flush, l4v's
`flush_pd`, is `flush_all`, a machine operation), and the clearing of the
page directory in `perform_page_directory_invocation`.
-/
import Fl4Proofs.P3.VsPdMapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Spec
open Fl4Spec

open Classical in
theorem pdDecodeUnmap_final {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageDirectoryUnmap)
    (args : List Data) (cte : CslotPtr) (p : ObjRef) (ma : Option (Asid × VSpaceRef)) (ex : List (Cap × CslotPtr))
    (σ : State Unit) (hf : isFinalCap' (Cap.archObjectCap (.pageDirectoryCap p ma)) σ) :
    ExceptT.run (decodePageDirectoryInvocation (Z := Unit) lbl args cte (.pageDirectoryCap p ma) ex) σ =
      ({(.ok (.invokePageDirectory (.pageDirectoryUnmap (.archObjectCap (.pageDirectoryCap p ma)) cte)), σ)}, False) := by
  unfold decodePageDirectoryInvocation
  dsimp only
  rw [if_neg (by rw [hl]; simp), if_pos hl,
    runE_bind_ok (runE_liftE (show isFinalCap (Z := Unit) _ σ = ({(decide (isFinalCap' _ σ), σ)}, False) from rfl))]
  rw [runE_bind_ok (runE_unlessE_true (by simpa using hf) _ σ)]
  rfl

open Classical in
theorem pdDecodeUnmap_notFinal {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageDirectoryUnmap)
    (args : List Data) (cte : CslotPtr) (p : ObjRef) (ma : Option (Asid × VSpaceRef)) (ex : List (Cap × CslotPtr))
    (σ : State Unit) (hf : ¬ isFinalCap' (Cap.archObjectCap (.pageDirectoryCap p ma)) σ) :
    ExceptT.run (decodePageDirectoryInvocation (Z := Unit) lbl args cte (.pageDirectoryCap p ma) ex) σ =
      ({(.error .revokeFirst, σ)}, False) := by
  unfold decodePageDirectoryInvocation
  dsimp only
  rw [if_neg (by rw [hl]; simp), if_pos hl,
    runE_bind_ok (runE_liftE (show isFinalCap (Z := Unit) _ σ = ({(decide (isFinalCap' _ σ), σ)}, False) from rfl))]
  exact runE_bind_err (by rw [runE_unlessE_false (by simpa using hf)]; rfl)

theorem unmapPD_noVs {asid : Asid} {v : VSpaceRef} {pt : ObjRef} {σ : State Unit} {e : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.error e, σ)}, False)) :
    unmapPd (Z := Unit) asid v pt σ = ({((), σ)}, False) := by
  unfold unmapPd
  rw [catch_err (runE_bind_err hf)]
  rfl

theorem unmapPD_noSlot {asid : Asid} {v : VSpaceRef} {pt vs : ObjRef} {σ : State Unit} {e : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPdptSlot (Z := Unit) vs v) σ = ({(.error e, σ)}, False)) :
    unmapPd (Z := Unit) asid v pt σ = ({((), σ)}, False) := by
  unfold unmapPd
  rw [catch_err (by rw [runE_bind_ok hf]; exact runE_bind_err hl)]
  rfl

theorem unmapPD_other {asid : Asid} {v : VSpaceRef} {pt vs slot : ObjRef} {σ : State Unit} {pde : PDPTE}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPdptSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPdpte (Z := Unit) slot σ = ({(pde, σ)}, False))
    (hm : ∀ a b c, pde = .pageDirectoryPDPTE a b c → addrFromPPtr pt ≠ a) :
    unmapPd (Z := Unit) asid v pt σ = ({((), σ)}, False) := by
  unfold unmapPd
  refine (catch_err (e := .invalidRoot) ?_).trans rfl
  rw [runE_bind_ok hf, runE_bind_ok hl, runE_bind_ok (runE_liftE hg)]
  cases pde with
  | pageDirectoryPDPTE a b c => dsimp only; rw [if_neg (Ne.symm (hm a b c rfl))]; exact runE_bind_err (runE_throw _ σ)
  | invalidPDPTE => exact runE_bind_err (runE_throw _ σ)
  | hugePagePDPTE _ _ _ => exact runE_bind_err (runE_throw _ σ)

theorem unmapPD_match {asid : Asid} {v : VSpaceRef} {pt vs slot : ObjRef} {σ : State Unit}
    {ta : TableAttrs} {tr : CapRights}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPdptSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPdpte (Z := Unit) slot σ = ({(.pageDirectoryPDPTE (addrFromPPtr pt) ta tr, σ)}, False)) :
    unmapPd (Z := Unit) asid v pt σ = (flushPd (Z := Unit) vs asid >>= fun _ =>
      storePdpte slot .invalidPDPTE >>= fun _ => invalidatePageStructureCacheAsid (addrFromPPtr vs) asid) σ := by
  unfold unmapPd
  refine (catch_congr (m' := NonDetE.liftE (flushPd (Z := Unit) vs asid >>= fun _ =>
      storePdpte slot .invalidPDPTE >>= fun _ => invalidatePageStructureCacheAsid (addrFromPPtr vs) asid)) ?_).trans
    (catch_liftE _ _ _)
  rw [runE_bind_ok hf, runE_bind_ok hl, runE_bind_ok (runE_liftE hg)]
  dsimp only
  rw [if_pos rfl, runE_bind_ok (runE_ret _ σ)]

/-- Storing `InvalidPDE` in the slots `js` of a page directory. -/
theorem clearPd_gen {q : U64} (hq : q.val % 4096 = 0) :
    ∀ (js : List Nat), (∀ j ∈ js, j < 512) → ∀ (σ : State Unit) (f : BitVec 9 → PDE),
      σ.kheap q.bv = some (.archObj (.pageDirectory f)) →
      NonDet.mapMx (fun slot => storePde (Z := Unit) slot .invalidPDE)
        (js.map fun j => q.bv + (BitVec.ofNat 64 j <<< wordSizeBits)) σ =
      ({((), updK σ q.bv (.archObj (.pageDirectory fun k => if k.toNat ∈ js then .invalidPDE else f k)))}, False) := by
  intro js
  induction js with
  | nil =>
    intro _ σ f hk
    simp only [List.map_nil, NonDet.mapMx, List.not_mem_nil, if_false]
    rw [updK_self hk]; rfl
  | cons j js ih =>
    intro hjs σ f hk
    have hj : j < 512 := hjs j (by simp)
    set j' : U64 := ⟨BitVec.ofNat 64 j⟩
    have hj' : j'.val = j := by
      show (BitVec.ofNat 64 j).toNat = j
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [List.map_cons, NonDet.mapMx]
    rw [show NonDet.bind (storePde (Z := Unit) (q.bv + (BitVec.ofNat 64 j <<< wordSizeBits)) .invalidPDE)
        (fun _ => NonDet.mapMx (fun slot => storePde (Z := Unit) slot .invalidPDE)
          (js.map fun j => q.bv + (BitVec.ofNat 64 j <<< wordSizeBits))) σ =
        (storePde (Z := Unit) (q.bv + (j'.bv <<< wordSizeBits)) .invalidPDE >>= fun _ =>
          NonDet.mapMx (fun slot => storePde (Z := Unit) slot .invalidPDE)
          (js.map fun j => q.bv + (BitVec.ofNat 64 j <<< wordSizeBits))) σ from rfl]
    rw [nd_bind_one (storePde_at hq hk (by omega) .invalidPDE)]
    rw [ih (fun j h => hjs j (by simp [h])) _ (Function.update f (ucast 9 j'.bv) .invalidPDE) (by simp [updK]),
      updK_updK]
    have hF : (fun k : BitVec 9 => if k.toNat ∈ js then PDE.invalidPDE else Function.update f (ucast 9 j'.bv) .invalidPDE k) =
        (fun k => if k.toNat ∈ j :: js then .invalidPDE else f k) := by
      funext k
      by_cases h1 : k.toNat ∈ js
      · simp [h1]
      · by_cases h2 : k.toNat = j
        · have : (ucast 9 j'.bv : BitVec 9) = k := (ucast_ofNat hj k).2 h2
          simp [h1, h2, this]
        · have : (ucast 9 j'.bv : BitVec 9) ≠ k := fun h => h2 ((ucast_ofNat hj k).1 h)
          simp [h1, h2, Function.update_of_ne (Ne.symm this)]
    rw [hF]

theorem clearPd_eq {q : U64} (hq : q.val % 4096 = 0) {σ : State Unit} {f : BitVec 9 → PDE}
    (hk : σ.kheap q.bv = some (.archObj (.pageDirectory f))) :
    NonDet.mapMx (fun slot => storePde (Z := Unit) slot .invalidPDE)
      (uptoEnumStep q.bv (q.bv + (1 : BitVec 64) <<< wordSizeBits) (q.bv + (1 : BitVec 64) <<< pdBits - 1)) σ =
      ({((), updK σ q.bv (.archObj (.pageDirectory fun _ => .invalidPDE)))}, False) := by
  rw [show uptoEnumStep q.bv (q.bv + (1 : BitVec 64) <<< wordSizeBits) (q.bv + (1 : BitVec 64) <<< pdBits - 1) =
      uptoEnumStep q.bv (q.bv + (1 : BitVec 64) <<< wordSizeBits) (q.bv + (1 : BitVec 64) <<< ptBits - 1) from rfl, slots_eq hq, clearPd_gen hq _ (fun j h => List.mem_range.1 h) σ f hk]
  have : (fun k : BitVec 9 => if k.toNat ∈ List.range 512 then PDE.invalidPDE else f k) = fun _ => .invalidPDE := by
    funext k
    have : k.toNat < 512 := k.isLt
    simp [List.mem_range, this]
  rw [this]

/-- The spec's PageDirectory Unmap perform, for a mapped directory. -/
theorem performPdUnmap_mem {q : U64} (hq : q.val % 4096 = 0) {asid : Asid} {va : VSpaceRef}
    {pc : ObjRef} {idx : List Bool} {r : Nat} {cs : CnodeContents} {ma : Option (Asid × VSpaceRef)}
    {σ1 σu : State Unit}
    (hnu : ¬ (unmapPd (Z := Unit) asid va q.bv σ1).2)
    (hall : ∀ x σ, (x, σ) ∈ (unmapPd (Z := Unit) asid va q.bv σ1).1 →
      σ.kheap q.bv = σ1.kheap q.bv ∧ σ.kheap pc = σ1.kheap pc)
    (hu : ((), σu) ∈ (unmapPd (Z := Unit) asid va q.bv σ1).1) {f : BitVec 9 → PDE}
    (hkp : σ1.kheap q.bv = some (.archObj (.pageDirectory f))) (hkc : σ1.kheap pc = some (.cnode r cs))
    (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r) (hcs : cs idx = some (.archObjectCap (.pageDirectoryCap q.bv ma))) :
    ((), setCnodeSlot (updK σu q.bv (.archObj (.pageDirectory fun _ => .invalidPDE))) pc r cs idx
        (.archObjectCap (.pageDirectoryCap q.bv none))) ∈
      (performPageDirectoryInvocation (Z := Unit)
        (.pageDirectoryUnmap (.archObjectCap (.pageDirectoryCap q.bv (some (asid, va)))) (pc, idx)) σ1).1 ∧
    ¬ (performPageDirectoryInvocation (Z := Unit)
        (.pageDirectoryUnmap (.archObjectCap (.pageDirectoryCap q.bv (some (asid, va)))) (pc, idx)) σ1).2 := by
  have hqc : q.bv ≠ pc := kheap_ne hkp hkc (fun _ h1 h2 => by subst h1; cases h2)
  have tailCap : ∀ σ : State Unit, σ.kheap pc = some (.cnode r cs) →
      (NonDet.liftM Cap.theArchCap (getCap (Z := Unit) (pc, idx)) >>= fun cap =>
        setCap (Cap.archObjectCap (updateMapData cap none none)) (pc, idx)) σ =
      ({((), setCnodeSlot σ pc r cs idx (.archObjectCap (.pageDirectoryCap q.bv none)))}, False) := by
    intro σ hk
    rw [nd_bind_one (by unfold NonDet.liftM; rw [nd_bind_one' (getCap_cnode hk hwf hcs)]; rfl)]
    exact setCap_cnode _ hk hwf hidx
  have hkc' : ∀ σ : State Unit, σ.kheap pc = σ1.kheap pc →
      (updK σ q.bv (.archObj (.pageDirectory fun _ => .invalidPDE))).kheap pc = some (.cnode r cs) := by
    intro σ h2; simp [updK, Ne.symm hqc, h2, hkc]
  unfold performPageDirectoryInvocation
  dsimp only
  rw [nd_bind_apply']
  refine ⟨⟨((), σu), hu, ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := hall _ _ hu
    rw [nd_pure_bind', nd_pure_bind', nd_bind_one (clearPd_eq hq (h1.trans hkp)), tailCap _ (hkc' _ h2)]
    rfl
  · rintro (h | ⟨y, hy, h⟩)
    · exact hnu h
    · obtain ⟨h1, h2⟩ := hall _ _ hy
      rw [nd_pure_bind', nd_pure_bind', nd_bind_one (clearPd_eq hq (h1.trans hkp)), tailCap _ (hkc' _ h2)] at h
      exact h

end Spec

end

end Fl4Proofs.P3.Vs
