/-
P3 (DESIGN.md §9), VSpace: **Frame `Map` for large (2M) and huge (1G)
pages, the spec side**: VsFrameMap for `X64LargePage` / `X64HugePage`
(`mapTailL`/`mapTailH`, their outcomes; `ensure_safe_mapping` fails with
`DeleteFirst` on a page-table / page-directory entry), and the perform with
`store_pde` / `store_pdpte`.
-/
import Fl4Proofs.P3.VsPteL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Spec
open Fl4Spec

/-- The spec's L Frame Map after the checks on the mapped address. -/
def mapTailL (pm : ObjRef) (asid : Asid) (dev : Bool) (p : ObjRef) (R : VMRights) (vaddr rm attr : Data)
    (cte : CslotPtr) : SEMonad Unit ArchInvocation := do
  let vspace' ← lookupErrorOnFailure false <| findVspaceForAsid asid
  NonDetE.whenE (vspace' ≠ pm) <| NonDetE.throwError (.invalidCapability 1)
  let vmRights ← NonDetE.returnOk (maskVmRights R <| dataToRights rm)
  checkVpAlignment .x64LargePage vaddr
  let entries ← createMappingEntries (addrFromPPtr p) vaddr .x64LargePage vmRights (attribsFromWord attr) pm
  ensureSafeMapping entries
  NonDetE.returnOk <| .invokePage <| .pageMap
    (.archObjectCap <| .pageCap dev p R .vmVSpaceMap .x64LargePage (some (asid, vaddr))) cte entries pm

/-- The page map the spec decodes. -/
def mapInvL (pm : ObjRef) (asid : Asid) (dev : Bool) (p : ObjRef) (R : VMRights) (vaddr rm attr : Data)
    (cte : CslotPtr) (slot : ObjRef) : ArchInvocation :=
  .invokePage <| .pageMap (.archObjectCap <| .pageCap dev p R .vmVSpaceMap .x64LargePage (some (asid, vaddr))) cte
    (.vmPDE (.largePagePDE (addrFromPPtr p) (attribsFromWord attr \ attrMask) (maskVmRights R (dataToRights rm))),
      slot) pm

theorem decodeMapL_mapped {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageMap)
    (a0 a1 a2 : Data) (rest : List Data) (cte : CslotPtr) (dev : Bool) (p : ObjRef) (R : VMRights)
    (mt : VMMapType) (asid' : Asid) (vaddr' : VSpaceRef) (pm : ObjRef) (asid : Asid) (xsl : CslotPtr)
    (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    ExceptT.run (decodePageInvocation (Z := Unit) lbl (a0 :: a1 :: a2 :: rest) cte
      (.pageCap dev p R mt .x64LargePage (some (asid', vaddr'))) ((.archObjectCap (.pml4Cap pm (some asid)), xsl) :: ex)) σ =
    ExceptT.run (do
      NonDetE.whenE (asid' ≠ asid) (NonDetE.throwError (.invalidCapability 1))
      NonDetE.whenE (mt ≠ .vmVSpaceMap) (NonDetE.throwError .illegalOperation)
      let r ← NonDetE.whenE (vaddr' ≠ a0) (NonDetE.throwError (.invalidArgument 0))
      (fun (_ : Unit) => mapTailL pm asid dev p R a0 a1 a2 cte) r) σ := by
  unfold decodePageInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp)]
  exact runE_bind_ok (runE_ret _ σ)

theorem decodeMapL_unmapped {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageMap)
    (a0 a1 a2 : Data) (rest : List Data) (cte : CslotPtr) (dev : Bool) (p : ObjRef) (R : VMRights)
    (mt : VMMapType) (pm : ObjRef) (asid : Asid) (xsl : CslotPtr) (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    ExceptT.run (decodePageInvocation (Z := Unit) lbl (a0 :: a1 :: a2 :: rest) cte
      (.pageCap dev p R mt .x64LargePage none) ((.archObjectCap (.pml4Cap pm (some asid)), xsl) :: ex)) σ =
    ExceptT.run (do
      let r ← NonDetE.whenE (a0 > userVtop ∨ a0 + 2097152 > userVtop) (NonDetE.throwError (.invalidArgument 0))
      (fun (_ : Unit) => mapTailL pm asid dev p R a0 a1 a2 cte) r) σ := by
  unfold decodePageInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp)]
  refine (runE_bind_ok (runE_ret _ σ)).trans ?_
  exact runE_bind_ok (runE_ret _ σ)

theorem mapTailL_noVs {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights} {vaddr rm attr : Data}
    {cte : CslotPtr} {σ : State Unit} {lf : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.error lf, σ)}, False)) :
    ExceptT.run (mapTailL pm asid dev p R vaddr rm attr cte) σ = ({(.error (.failedLookup false lf), σ)}, False) := by
  unfold mapTailL lookupErrorOnFailure
  exact runE_bind_err (by rw [runE_handle_err hf]; rfl)

theorem mapTailL_wrongVs {pm r1 : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok r1, σ)}, False)) (hne : r1 ≠ pm) :
    ExceptT.run (mapTailL pm asid dev p R vaddr rm attr cte) σ = ({(.error (.invalidCapability 1), σ)}, False) := by
  unfold mapTailL lookupErrorOnFailure
  rw [runE_bind_ok (runE_handle_ok hf)]
  exact runE_bind_err (by rw [runE_whenE_true hne]; rfl)

theorem mapTailL_prefix {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False)) :
    ExceptT.run (mapTailL pm asid dev p R vaddr rm attr cte) σ = ExceptT.run (do
      checkVpAlignment .x64LargePage vaddr
      let entries ← createMappingEntries (addrFromPPtr p) vaddr .x64LargePage
        (maskVmRights R <| dataToRights rm) (attribsFromWord attr) pm
      ensureSafeMapping entries
      NonDetE.returnOk (ε := SyscallError) <| ArchInvocation.invokePage <| .pageMap
        (.archObjectCap <| .pageCap dev p R .vmVSpaceMap .x64LargePage (some (asid, vaddr))) cte entries pm) σ := by
  unfold mapTailL lookupErrorOnFailure
  rw [runE_bind_ok (runE_handle_ok hf), runE_bind_ok (runE_whenE_false (by simp) _ σ), runE_bind_ok (runE_ret _ σ)]

theorem mapTailL_unaligned {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False))
    (ha : ¬ isAligned vaddr 21) :
    ExceptT.run (mapTailL pm asid dev p R vaddr rm attr cte) σ = ({(.error .alignmentError, σ)}, False) := by
  have ha' : ¬ isAligned vaddr (pageBitsForSize .x64LargePage) := ha
  rw [mapTailL_prefix hf]
  unfold checkVpAlignment
  exact runE_bind_err (by rw [runE_unlessE_false ha']; rfl)

theorem mapTailL_noSlot {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False))
    (ha : isAligned vaddr 21) {lf : LookupFailure}
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) pm vaddr) σ = ({(.error lf, σ)}, False)) :
    ExceptT.run (mapTailL pm asid dev p R vaddr rm attr cte) σ = ({(.error (.failedLookup false lf), σ)}, False) := by
  have ha' : isAligned vaddr (pageBitsForSize .x64LargePage) := ha
  rw [mapTailL_prefix hf]
  unfold checkVpAlignment
  rw [runE_bind_ok (runE_unlessE_true ha' _ σ)]
  unfold createMappingEntries lookupErrorOnFailure
  exact runE_bind_err (runE_bind_err (by rw [runE_handle_err hl]; rfl))

theorem mapTailL_ok {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False))
    (ha : isAligned vaddr 21) {slot : ObjRef}
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) pm vaddr) σ = ({(.ok slot, σ)}, False)) {x : PDE}
    (hg : getPde (Z := Unit) slot σ = ({(x, σ)}, False)) (hx : x = .invalidPDE ∨ ∃ a b c, x = .largePagePDE a b c) :
    ExceptT.run (mapTailL pm asid dev p R vaddr rm attr cte) σ =
      ({(.ok (mapInvL pm asid dev p R vaddr rm attr cte slot), σ)}, False) := by
  have ha' : isAligned vaddr (pageBitsForSize .x64LargePage) := ha
  rw [mapTailL_prefix hf]
  unfold checkVpAlignment
  rw [runE_bind_ok (runE_unlessE_true ha' _ σ)]
  unfold createMappingEntries lookupErrorOnFailure
  rw [runE_bind_ok (runE_bind_ok (runE_handle_ok hl))]
  unfold ensureSafeMapping
  dsimp only
  refine (runE_bind_ok (by rw [runE_bind_ok (runE_liftE hg)]; rcases hx with rfl | ⟨a, b, c, rfl⟩ <;> rfl)).trans ?_
  rfl

theorem mapTailL_used {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False))
    (ha : isAligned vaddr 21) {slot : ObjRef}
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) pm vaddr) σ = ({(.ok slot, σ)}, False)) {a b c : _}
    (hg : getPde (Z := Unit) slot σ = ({(.pageTablePDE a b c, σ)}, False)) :
    ExceptT.run (mapTailL pm asid dev p R vaddr rm attr cte) σ = ({(.error .deleteFirst, σ)}, False) := by
  have ha' : isAligned vaddr (pageBitsForSize .x64LargePage) := ha
  rw [mapTailL_prefix hf]
  unfold checkVpAlignment
  rw [runE_bind_ok (runE_unlessE_true ha' _ σ)]
  unfold createMappingEntries lookupErrorOnFailure
  rw [runE_bind_ok (runE_bind_ok (runE_handle_ok hl))]
  unfold ensureSafeMapping
  dsimp only
  exact runE_bind_err (by rw [runE_bind_ok (runE_liftE hg)]; rfl)

theorem performLMap_mem {dev : Bool} {p : ObjRef} {R : VMRights} {sz : VMPageSize} {asid : Asid} {va : VSpaceRef}
    {cte : CslotPtr} {pte : PDE} {slot pm : ObjRef} {σ1 σ2 σ' : State Unit}
    (hsc : setCap (Z := Unit) (.archObjectCap (.pageCap dev p R .vmVSpaceMap sz (some (asid, va)))) cte σ1 =
      ({((), σ2)}, False))
    (hm : ((), σ') ∈ ((storePde (Z := Unit) slot pte >>= fun _ =>
      invalidatePageStructureCacheAsid (addrFromPPtr pm) asid) σ2).1)
    (hnf : ¬ ((storePde (Z := Unit) slot pte >>= fun _ =>
      invalidatePageStructureCacheAsid (addrFromPPtr pm) asid) σ2).2) :
    (([] : List Data), σ') ∈ (performPageInvocation (Z := Unit)
      (.pageMap (.archObjectCap (.pageCap dev p R .vmVSpaceMap sz (some (asid, va)))) cte (.vmPDE pte, slot) pm) σ1).1 ∧
    ¬ (performPageInvocation (Z := Unit)
      (.pageMap (.archObjectCap (.pageCap dev p R .vmVSpaceMap sz (some (asid, va)))) cte (.vmPDE pte, slot) pm) σ1).2 := by
  unfold performPageInvocation
  dsimp only
  rw [nd_bind_one hsc]
  rw [nd_bind_apply'] at hm hnf ⊢
  obtain ⟨x, hx, hx2⟩ := hm
  refine ⟨⟨x, hx, ?_⟩, ?_⟩
  · rw [nd_pure_bind', nd_bind_apply']
    exact ⟨((), σ'), hx2, by simp [pure, NonDet.pure]⟩
  · rintro (h | ⟨y, hy, h⟩)
    · exact hnf (Or.inl h)
    · rw [nd_pure_bind', nd_bind_apply'] at h
      rcases h with h | ⟨z, -, hz⟩
      · exact hnf (Or.inr ⟨y, hy, h⟩)
      · simp [pure, NonDet.pure] at hz


/-- The spec's H Frame Map after the checks on the mapped address. -/
def mapTailH (pm : ObjRef) (asid : Asid) (dev : Bool) (p : ObjRef) (R : VMRights) (vaddr rm attr : Data)
    (cte : CslotPtr) : SEMonad Unit ArchInvocation := do
  let vspace' ← lookupErrorOnFailure false <| findVspaceForAsid asid
  NonDetE.whenE (vspace' ≠ pm) <| NonDetE.throwError (.invalidCapability 1)
  let vmRights ← NonDetE.returnOk (maskVmRights R <| dataToRights rm)
  checkVpAlignment .x64HugePage vaddr
  let entries ← createMappingEntries (addrFromPPtr p) vaddr .x64HugePage vmRights (attribsFromWord attr) pm
  ensureSafeMapping entries
  NonDetE.returnOk <| .invokePage <| .pageMap
    (.archObjectCap <| .pageCap dev p R .vmVSpaceMap .x64HugePage (some (asid, vaddr))) cte entries pm

/-- The page map the spec decodes. -/
def mapInvH (pm : ObjRef) (asid : Asid) (dev : Bool) (p : ObjRef) (R : VMRights) (vaddr rm attr : Data)
    (cte : CslotPtr) (slot : ObjRef) : ArchInvocation :=
  .invokePage <| .pageMap (.archObjectCap <| .pageCap dev p R .vmVSpaceMap .x64HugePage (some (asid, vaddr))) cte
    (.vmPDPTE (.hugePagePDPTE (addrFromPPtr p) (attribsFromWord attr \ attrMask') (maskVmRights R (dataToRights rm))),
      slot) pm

theorem decodeMapH_mapped {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageMap)
    (a0 a1 a2 : Data) (rest : List Data) (cte : CslotPtr) (dev : Bool) (p : ObjRef) (R : VMRights)
    (mt : VMMapType) (asid' : Asid) (vaddr' : VSpaceRef) (pm : ObjRef) (asid : Asid) (xsl : CslotPtr)
    (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    ExceptT.run (decodePageInvocation (Z := Unit) lbl (a0 :: a1 :: a2 :: rest) cte
      (.pageCap dev p R mt .x64HugePage (some (asid', vaddr'))) ((.archObjectCap (.pml4Cap pm (some asid)), xsl) :: ex)) σ =
    ExceptT.run (do
      NonDetE.whenE (asid' ≠ asid) (NonDetE.throwError (.invalidCapability 1))
      NonDetE.whenE (mt ≠ .vmVSpaceMap) (NonDetE.throwError .illegalOperation)
      let r ← NonDetE.whenE (vaddr' ≠ a0) (NonDetE.throwError (.invalidArgument 0))
      (fun (_ : Unit) => mapTailH pm asid dev p R a0 a1 a2 cte) r) σ := by
  unfold decodePageInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp)]
  exact runE_bind_ok (runE_ret _ σ)

theorem decodeMapH_unmapped {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageMap)
    (a0 a1 a2 : Data) (rest : List Data) (cte : CslotPtr) (dev : Bool) (p : ObjRef) (R : VMRights)
    (mt : VMMapType) (pm : ObjRef) (asid : Asid) (xsl : CslotPtr) (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    ExceptT.run (decodePageInvocation (Z := Unit) lbl (a0 :: a1 :: a2 :: rest) cte
      (.pageCap dev p R mt .x64HugePage none) ((.archObjectCap (.pml4Cap pm (some asid)), xsl) :: ex)) σ =
    ExceptT.run (do
      let r ← NonDetE.whenE (a0 > userVtop ∨ a0 + 1073741824 > userVtop) (NonDetE.throwError (.invalidArgument 0))
      (fun (_ : Unit) => mapTailH pm asid dev p R a0 a1 a2 cte) r) σ := by
  unfold decodePageInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp)]
  refine (runE_bind_ok (runE_ret _ σ)).trans ?_
  exact runE_bind_ok (runE_ret _ σ)

theorem mapTailH_noVs {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights} {vaddr rm attr : Data}
    {cte : CslotPtr} {σ : State Unit} {lf : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.error lf, σ)}, False)) :
    ExceptT.run (mapTailH pm asid dev p R vaddr rm attr cte) σ = ({(.error (.failedLookup false lf), σ)}, False) := by
  unfold mapTailH lookupErrorOnFailure
  exact runE_bind_err (by rw [runE_handle_err hf]; rfl)

theorem mapTailH_wrongVs {pm r1 : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok r1, σ)}, False)) (hne : r1 ≠ pm) :
    ExceptT.run (mapTailH pm asid dev p R vaddr rm attr cte) σ = ({(.error (.invalidCapability 1), σ)}, False) := by
  unfold mapTailH lookupErrorOnFailure
  rw [runE_bind_ok (runE_handle_ok hf)]
  exact runE_bind_err (by rw [runE_whenE_true hne]; rfl)

theorem mapTailH_prefix {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False)) :
    ExceptT.run (mapTailH pm asid dev p R vaddr rm attr cte) σ = ExceptT.run (do
      checkVpAlignment .x64HugePage vaddr
      let entries ← createMappingEntries (addrFromPPtr p) vaddr .x64HugePage
        (maskVmRights R <| dataToRights rm) (attribsFromWord attr) pm
      ensureSafeMapping entries
      NonDetE.returnOk (ε := SyscallError) <| ArchInvocation.invokePage <| .pageMap
        (.archObjectCap <| .pageCap dev p R .vmVSpaceMap .x64HugePage (some (asid, vaddr))) cte entries pm) σ := by
  unfold mapTailH lookupErrorOnFailure
  rw [runE_bind_ok (runE_handle_ok hf), runE_bind_ok (runE_whenE_false (by simp) _ σ), runE_bind_ok (runE_ret _ σ)]

theorem mapTailH_unaligned {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False))
    (ha : ¬ isAligned vaddr 30) :
    ExceptT.run (mapTailH pm asid dev p R vaddr rm attr cte) σ = ({(.error .alignmentError, σ)}, False) := by
  have ha' : ¬ isAligned vaddr (pageBitsForSize .x64HugePage) := ha
  rw [mapTailH_prefix hf]
  unfold checkVpAlignment
  exact runE_bind_err (by rw [runE_unlessE_false ha']; rfl)

/-- `ExceptT.run (m >>= f) s` depends on `m` only through `ExceptT.run m s`. -/
theorem runE_bind_congrH {ε α β : Type} {m m' : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    {s : State Unit} (h : ExceptT.run m s = ExceptT.run m' s) :
    ExceptT.run (m >>= f) s = ExceptT.run (m' >>= f) s := by
  show NonDet.bind (ExceptT.run m) (ExceptT.bindCont f) s = NonDet.bind (ExceptT.run m') (ExceptT.bindCont f) s
  unfold NonDet.bind; rw [h]

/-- FL4 (#65): with 1 GiB pages, `createMappingEntries` of a huge page is
l4v's. -/
theorem cme_huge_ok {σ : State Unit} (hh : σ.archState.x64HugePages = true) (base : Paddr) (vptr : VSpaceRef)
    (r : VMRights) (a : VMAttributes) (pml4 : ObjRef) :
    ExceptT.run (createMappingEntries (Z := Unit) base vptr .x64HugePage r a pml4) σ =
    ExceptT.run (do
      let p ← lookupErrorOnFailure false (lookupPdptSlot (Z := Unit) pml4 vptr)
      NonDetE.returnOk (ε := SyscallError) (VMPageEntry.vmPDPTE (.hugePagePDPTE base (a \ attrMask') r), p)) σ := by
  unfold createMappingEntries
  rw [runE_bind_ok (runE_liftE (show NonDet.gets (fun s : State Unit => s.archState.x64HugePages) σ =
    ({(true, σ)}, False) by rw [← hh]; rfl)), runE_bind_ok (runE_unlessE_true rfl _ σ)]

/-- FL4 (#65): without 1 GiB pages, `createMappingEntries` of a huge page
fails with IllegalOperation. -/
theorem cme_huge_no {σ : State Unit} (hh : σ.archState.x64HugePages = false) (base : Paddr) (vptr : VSpaceRef)
    (r : VMRights) (a : VMAttributes) (pml4 : ObjRef) :
    ExceptT.run (createMappingEntries (Z := Unit) base vptr .x64HugePage r a pml4) σ =
    ExceptT.run (NonDetE.throwError (σ := State Unit) (α := VMPageEntry × ObjRef) SyscallError.illegalOperation) σ := by
  unfold createMappingEntries
  rw [runE_bind_ok (runE_liftE (show NonDet.gets (fun s : State Unit => s.archState.x64HugePages) σ =
    ({(false, σ)}, False) by rw [← hh]; rfl))]
  exact runE_bind_err (by rw [runE_unlessE_false (by simp)]; rfl)

/-- FL4 (#65): a 1 GiB map without 1 GiB pages is an illegal operation. -/
theorem mapTailH_noHuge {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False))
    (ha : isAligned vaddr 30) (hh : σ.archState.x64HugePages = false) :
    ExceptT.run (mapTailH pm asid dev p R vaddr rm attr cte) σ = ({(.error .illegalOperation, σ)}, False) := by
  have ha' : isAligned vaddr (pageBitsForSize .x64HugePage) := ha
  rw [mapTailH_prefix hf]
  unfold checkVpAlignment
  rw [runE_bind_ok (runE_unlessE_true ha' _ σ)]
  rw [runE_bind_congrH (cme_huge_no hh _ _ _ _ _)]
  exact runE_bind_err (runE_throw _ σ)

theorem mapTailH_noSlot {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False))
    (ha : isAligned vaddr 30) (hh : σ.archState.x64HugePages = true) {lf : LookupFailure}
    (hl : ExceptT.run (lookupPdptSlot (Z := Unit) pm vaddr) σ = ({(.error lf, σ)}, False)) :
    ExceptT.run (mapTailH pm asid dev p R vaddr rm attr cte) σ = ({(.error (.failedLookup false lf), σ)}, False) := by
  have ha' : isAligned vaddr (pageBitsForSize .x64HugePage) := ha
  rw [mapTailH_prefix hf]
  unfold checkVpAlignment
  rw [runE_bind_ok (runE_unlessE_true ha' _ σ)]
  rw [runE_bind_congrH (cme_huge_ok hh _ _ _ _ _)]
  unfold lookupErrorOnFailure
  exact runE_bind_err (runE_bind_err (by rw [runE_handle_err hl]; rfl))

theorem mapTailH_ok {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False))
    (ha : isAligned vaddr 30) (hh : σ.archState.x64HugePages = true) {slot : ObjRef}
    (hl : ExceptT.run (lookupPdptSlot (Z := Unit) pm vaddr) σ = ({(.ok slot, σ)}, False)) {x : PDPTE}
    (hg : getPdpte (Z := Unit) slot σ = ({(x, σ)}, False)) (hx : x = .invalidPDPTE ∨ ∃ a b c, x = .hugePagePDPTE a b c) :
    ExceptT.run (mapTailH pm asid dev p R vaddr rm attr cte) σ =
      ({(.ok (mapInvH pm asid dev p R vaddr rm attr cte slot), σ)}, False) := by
  have ha' : isAligned vaddr (pageBitsForSize .x64HugePage) := ha
  rw [mapTailH_prefix hf]
  unfold checkVpAlignment
  rw [runE_bind_ok (runE_unlessE_true ha' _ σ)]
  rw [runE_bind_congrH (cme_huge_ok hh _ _ _ _ _)]
  unfold lookupErrorOnFailure
  rw [runE_bind_ok (runE_bind_ok (runE_handle_ok hl))]
  unfold ensureSafeMapping
  dsimp only
  refine (runE_bind_ok (by rw [runE_bind_ok (runE_liftE hg)]; rcases hx with rfl | ⟨a, b, c, rfl⟩ <;> rfl)).trans ?_
  rfl

theorem mapTailH_used {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False))
    (ha : isAligned vaddr 30) (hh : σ.archState.x64HugePages = true) {slot : ObjRef}
    (hl : ExceptT.run (lookupPdptSlot (Z := Unit) pm vaddr) σ = ({(.ok slot, σ)}, False)) {a b c : _}
    (hg : getPdpte (Z := Unit) slot σ = ({(.pageDirectoryPDPTE a b c, σ)}, False)) :
    ExceptT.run (mapTailH pm asid dev p R vaddr rm attr cte) σ = ({(.error .deleteFirst, σ)}, False) := by
  have ha' : isAligned vaddr (pageBitsForSize .x64HugePage) := ha
  rw [mapTailH_prefix hf]
  unfold checkVpAlignment
  rw [runE_bind_ok (runE_unlessE_true ha' _ σ)]
  rw [runE_bind_congrH (cme_huge_ok hh _ _ _ _ _)]
  unfold lookupErrorOnFailure
  rw [runE_bind_ok (runE_bind_ok (runE_handle_ok hl))]
  unfold ensureSafeMapping
  dsimp only
  exact runE_bind_err (by rw [runE_bind_ok (runE_liftE hg)]; rfl)

theorem performHMap_mem {dev : Bool} {p : ObjRef} {R : VMRights} {sz : VMPageSize} {asid : Asid} {va : VSpaceRef}
    {cte : CslotPtr} {pte : PDPTE} {slot pm : ObjRef} {σ1 σ2 σ' : State Unit}
    (hsc : setCap (Z := Unit) (.archObjectCap (.pageCap dev p R .vmVSpaceMap sz (some (asid, va)))) cte σ1 =
      ({((), σ2)}, False))
    (hm : ((), σ') ∈ ((storePdpte (Z := Unit) slot pte >>= fun _ =>
      invalidatePageStructureCacheAsid (addrFromPPtr pm) asid) σ2).1)
    (hnf : ¬ ((storePdpte (Z := Unit) slot pte >>= fun _ =>
      invalidatePageStructureCacheAsid (addrFromPPtr pm) asid) σ2).2) :
    (([] : List Data), σ') ∈ (performPageInvocation (Z := Unit)
      (.pageMap (.archObjectCap (.pageCap dev p R .vmVSpaceMap sz (some (asid, va)))) cte (.vmPDPTE pte, slot) pm) σ1).1 ∧
    ¬ (performPageInvocation (Z := Unit)
      (.pageMap (.archObjectCap (.pageCap dev p R .vmVSpaceMap sz (some (asid, va)))) cte (.vmPDPTE pte, slot) pm) σ1).2 := by
  unfold performPageInvocation
  dsimp only
  rw [nd_bind_one hsc]
  rw [nd_bind_apply'] at hm hnf ⊢
  obtain ⟨x, hx, hx2⟩ := hm
  refine ⟨⟨x, hx, ?_⟩, ?_⟩
  · rw [nd_pure_bind', nd_bind_apply']
    exact ⟨((), σ'), hx2, by simp [pure, NonDet.pure]⟩
  · rintro (h | ⟨y, hy, h⟩)
    · exact hnf (Or.inl h)
    · rw [nd_pure_bind', nd_bind_apply'] at h
      rcases h with h | ⟨z, -, hz⟩
      · exact hnf (Or.inr ⟨y, hy, h⟩)
      · simp [pure, NonDet.pure] at hz


end Spec

end

end Fl4Proofs.P3.Vs
