/-
P3 (DESIGN.md §9), VSpace: **Frame `Map` for 4K pages, the spec side**:
l4v's `decode_page_invocation` with label `X64PageMap` on a 4K page cap
and a mapped PML4 cap, and `perform_page_invocation` of the `PageMap` it
returns.

* `decodeMap_trunc`, `decodeMap_badVs`, `decodeMap_mapped`,
  `decodeMap_unmapped`: the decode up to l4v's `find_vspace_for_asid`,
  after which both cases continue with `mapTail`;
* `mapTail_*`: the decode's outcome for each result of
  `find_vspace_for_asid`, of the alignment check and of `lookup_pt_slot`;
* `performMap_mem`: the perform after `set_cap` and `store_pte`.
-/
import Fl4Proofs.P3.VsPtWrite
import Fl4Proofs.P3.VsAssignRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Spec
open Fl4Spec

theorem runE_handle_ok {ε ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    {σ σ' : State Unit} {a : α} (hm : ExceptT.run m σ = ({(.ok a, σ')}, False)) :
    ExceptT.run (NonDetE.handleE m h) σ = ({(.ok a, σ')}, False) := by
  unfold NonDetE.handleE
  rw [ExceptT.run_mk, nd_bind_one' hm]; rfl

theorem runE_handle_err {ε ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    {σ σ' : State Unit} {e : ε} (hm : ExceptT.run m σ = ({(.error e, σ')}, False)) :
    ExceptT.run (NonDetE.handleE m h) σ = ExceptT.run (h e) σ' := by
  unfold NonDetE.handleE
  rw [ExceptT.run_mk, nd_bind_one' hm]

theorem runE_unlessE_true {ε : Type} {P : Prop} {_ : Decidable P} (h : P) (m : NonDetE (State Unit) ε Unit)
    (σ : State Unit) : ExceptT.run (NonDetE.unlessE P m) σ = ({(.ok (), σ)}, False) := by
  unfold NonDetE.unlessE; rw [if_pos h]; rfl

theorem runE_unlessE_false {ε : Type} {P : Prop} {_ : Decidable P} (h : ¬ P) (m : NonDetE (State Unit) ε Unit)
    (σ : State Unit) : ExceptT.run (NonDetE.unlessE P m) σ = ExceptT.run m σ := by
  unfold NonDetE.unlessE; rw [if_neg h]

/-- The spec's 4K Frame Map after the checks on the mapped address. -/
def mapTail (pm : ObjRef) (asid : Asid) (dev : Bool) (p : ObjRef) (R : VMRights) (vaddr rm attr : Data)
    (cte : CslotPtr) : SEMonad Unit ArchInvocation := do
  let vspace' ← lookupErrorOnFailure false <| findVspaceForAsid asid
  NonDetE.whenE (vspace' ≠ pm) <| NonDetE.throwError (.invalidCapability 1)
  let vmRights ← NonDetE.returnOk (maskVmRights R <| dataToRights rm)
  checkVpAlignment .x64SmallPage vaddr
  let entries ← createMappingEntries (addrFromPPtr p) vaddr .x64SmallPage vmRights (attribsFromWord attr) pm
  ensureSafeMapping entries
  NonDetE.returnOk <| .invokePage <| .pageMap
    (.archObjectCap <| .pageCap dev p R .vmVSpaceMap .x64SmallPage (some (asid, vaddr))) cte entries pm

/-- The page map the spec decodes. -/
def mapInv (pm : ObjRef) (asid : Asid) (dev : Bool) (p : ObjRef) (R : VMRights) (vaddr rm attr : Data)
    (cte : CslotPtr) (slot : ObjRef) : ArchInvocation :=
  .invokePage <| .pageMap (.archObjectCap <| .pageCap dev p R .vmVSpaceMap .x64SmallPage (some (asid, vaddr))) cte
    (.vmPTE (.smallPagePTE (addrFromPPtr p) (attribsFromWord attr \ attrMask) (maskVmRights R (dataToRights rm))),
      slot) pm

theorem decodeMap_trunc {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageMap)
    (args : List Data) (cte : CslotPtr) (dev : Bool) (p : ObjRef) (R : VMRights) (mt : VMMapType)
    (sz : VMPageSize) (ma : Option (Asid × VSpaceRef)) (ex : List (Cap × CslotPtr))
    (h : ¬ (args.length > 2 ∧ ex.length > 0)) (σ : State Unit) :
    ExceptT.run (decodePageInvocation (Z := Unit) lbl args cte (.pageCap dev p R mt sz ma) ex) σ =
      ({(.error .truncatedMessage, σ)}, False) := by
  unfold decodePageInvocation
  dsimp only
  rw [if_pos hl, if_neg h]
  rfl

theorem decodeMap_badVs {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageMap)
    (a0 a1 a2 : Data) (rest : List Data) (cte : CslotPtr) (dev : Bool) (p : ObjRef) (R : VMRights)
    (mt : VMMapType) (ma : Option (Asid × VSpaceRef)) (vc : Cap) (xsl : CslotPtr) (ex : List (Cap × CslotPtr))
    (hvc : ∀ pm asid, vc ≠ .archObjectCap (.pml4Cap pm (some asid))) (σ : State Unit) :
    ExceptT.run (decodePageInvocation (Z := Unit) lbl (a0 :: a1 :: a2 :: rest) cte
      (.pageCap dev p R mt .x64SmallPage ma) ((vc, xsl) :: ex)) σ = ({(.error (.invalidCapability 1), σ)}, False) := by
  unfold decodePageInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp)]
  split
  · rename_i pm asid h
    exact absurd h (hvc pm asid)
  · exact runE_bind_err (runE_throw _ σ)

theorem decodeMap_mapped {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageMap)
    (a0 a1 a2 : Data) (rest : List Data) (cte : CslotPtr) (dev : Bool) (p : ObjRef) (R : VMRights)
    (mt : VMMapType) (asid' : Asid) (vaddr' : VSpaceRef) (pm : ObjRef) (asid : Asid) (xsl : CslotPtr)
    (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    ExceptT.run (decodePageInvocation (Z := Unit) lbl (a0 :: a1 :: a2 :: rest) cte
      (.pageCap dev p R mt .x64SmallPage (some (asid', vaddr'))) ((.archObjectCap (.pml4Cap pm (some asid)), xsl) :: ex)) σ =
    ExceptT.run (do
      NonDetE.whenE (asid' ≠ asid) (NonDetE.throwError (.invalidCapability 1))
      NonDetE.whenE (mt ≠ .vmVSpaceMap) (NonDetE.throwError .illegalOperation)
      let r ← NonDetE.whenE (vaddr' ≠ a0) (NonDetE.throwError (.invalidArgument 0))
      (fun (_ : Unit) => mapTail pm asid dev p R a0 a1 a2 cte) r) σ := by
  unfold decodePageInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp)]
  exact runE_bind_ok (runE_ret _ σ)

theorem decodeMap_unmapped {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageMap)
    (a0 a1 a2 : Data) (rest : List Data) (cte : CslotPtr) (dev : Bool) (p : ObjRef) (R : VMRights)
    (mt : VMMapType) (pm : ObjRef) (asid : Asid) (xsl : CslotPtr) (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    ExceptT.run (decodePageInvocation (Z := Unit) lbl (a0 :: a1 :: a2 :: rest) cte
      (.pageCap dev p R mt .x64SmallPage none) ((.archObjectCap (.pml4Cap pm (some asid)), xsl) :: ex)) σ =
    ExceptT.run (do
      let r ← NonDetE.whenE (a0 > userVtop ∨ a0 + 4096 > userVtop) (NonDetE.throwError (.invalidArgument 0))
      (fun (_ : Unit) => mapTail pm asid dev p R a0 a1 a2 cte) r) σ := by
  unfold decodePageInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp)]
  refine (runE_bind_ok (runE_ret _ σ)).trans ?_
  exact runE_bind_ok (runE_ret _ σ)

theorem mapTail_noVs {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights} {vaddr rm attr : Data}
    {cte : CslotPtr} {σ : State Unit} {lf : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.error lf, σ)}, False)) :
    ExceptT.run (mapTail pm asid dev p R vaddr rm attr cte) σ = ({(.error (.failedLookup false lf), σ)}, False) := by
  unfold mapTail lookupErrorOnFailure
  exact runE_bind_err (by rw [runE_handle_err hf]; rfl)

theorem mapTail_wrongVs {pm r1 : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok r1, σ)}, False)) (hne : r1 ≠ pm) :
    ExceptT.run (mapTail pm asid dev p R vaddr rm attr cte) σ = ({(.error (.invalidCapability 1), σ)}, False) := by
  unfold mapTail lookupErrorOnFailure
  rw [runE_bind_ok (runE_handle_ok hf)]
  exact runE_bind_err (by rw [runE_whenE_true hne]; rfl)

theorem mapTail_prefix {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False)) :
    ExceptT.run (mapTail pm asid dev p R vaddr rm attr cte) σ = ExceptT.run (do
      checkVpAlignment .x64SmallPage vaddr
      let entries ← createMappingEntries (addrFromPPtr p) vaddr .x64SmallPage
        (maskVmRights R <| dataToRights rm) (attribsFromWord attr) pm
      ensureSafeMapping entries
      NonDetE.returnOk (ε := SyscallError) <| ArchInvocation.invokePage <| .pageMap
        (.archObjectCap <| .pageCap dev p R .vmVSpaceMap .x64SmallPage (some (asid, vaddr))) cte entries pm) σ := by
  unfold mapTail lookupErrorOnFailure
  rw [runE_bind_ok (runE_handle_ok hf), runE_bind_ok (runE_whenE_false (by simp) _ σ), runE_bind_ok (runE_ret _ σ)]

theorem mapTail_unaligned {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False))
    (ha : ¬ isAligned vaddr 12) :
    ExceptT.run (mapTail pm asid dev p R vaddr rm attr cte) σ = ({(.error .alignmentError, σ)}, False) := by
  have ha' : ¬ isAligned vaddr (pageBitsForSize .x64SmallPage) := ha
  rw [mapTail_prefix hf]
  unfold checkVpAlignment
  exact runE_bind_err (by rw [runE_unlessE_false ha']; rfl)

theorem mapTail_noSlot {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False))
    (ha : isAligned vaddr 12) {lf : LookupFailure}
    (hl : ExceptT.run (lookupPtSlot (Z := Unit) pm vaddr) σ = ({(.error lf, σ)}, False)) :
    ExceptT.run (mapTail pm asid dev p R vaddr rm attr cte) σ = ({(.error (.failedLookup false lf), σ)}, False) := by
  have ha' : isAligned vaddr (pageBitsForSize .x64SmallPage) := ha
  rw [mapTail_prefix hf]
  unfold checkVpAlignment
  rw [runE_bind_ok (runE_unlessE_true ha' _ σ)]
  unfold createMappingEntries lookupErrorOnFailure
  exact runE_bind_err (runE_bind_err (by rw [runE_handle_err hl]; rfl))

theorem mapTail_ok {pm : ObjRef} {asid : Asid} {dev : Bool} {p : ObjRef} {R : VMRights}
    {vaddr rm attr : Data} {cte : CslotPtr} {σ : State Unit}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False))
    (ha : isAligned vaddr 12) {slot : ObjRef}
    (hl : ExceptT.run (lookupPtSlot (Z := Unit) pm vaddr) σ = ({(.ok slot, σ)}, False)) :
    ExceptT.run (mapTail pm asid dev p R vaddr rm attr cte) σ =
      ({(.ok (mapInv pm asid dev p R vaddr rm attr cte slot), σ)}, False) := by
  have ha' : isAligned vaddr (pageBitsForSize .x64SmallPage) := ha
  rw [mapTail_prefix hf]
  unfold checkVpAlignment
  rw [runE_bind_ok (runE_unlessE_true ha' _ σ)]
  unfold createMappingEntries lookupErrorOnFailure
  rw [runE_bind_ok (runE_bind_ok (runE_handle_ok hl))]
  exact (runE_bind_ok (runE_ret _ σ)).trans rfl

/-- The spec after the decode: `set_thread_state cur Restart`, then the
perform; `σ'` is one of its outcomes, and it does not fail. -/
def MapSpec (σ : State Unit) (iv : ArchInvocation) (σ' : State Unit) : Prop :=
  match iv with
  | .invokePage pi =>
    (([] : List Data), σ') ∈ ((setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
      performPageInvocation pi) σ).1 ∧
    ¬ ((setThreadState (Z := Unit) σ.curThread .restart >>= fun _ => performPageInvocation pi) σ).2
  | _ => False

theorem performMap_mem {dev : Bool} {p : ObjRef} {R : VMRights} {sz : VMPageSize} {asid : Asid} {va : VSpaceRef}
    {cte : CslotPtr} {pte : PTE} {slot pm : ObjRef} {σ1 σ2 σ' : State Unit}
    (hsc : setCap (Z := Unit) (.archObjectCap (.pageCap dev p R .vmVSpaceMap sz (some (asid, va)))) cte σ1 =
      ({((), σ2)}, False))
    (hm : ((), σ') ∈ ((storePte (Z := Unit) slot pte >>= fun _ =>
      invalidatePageStructureCacheAsid (addrFromPPtr pm) asid) σ2).1)
    (hnf : ¬ ((storePte (Z := Unit) slot pte >>= fun _ =>
      invalidatePageStructureCacheAsid (addrFromPPtr pm) asid) σ2).2) :
    (([] : List Data), σ') ∈ (performPageInvocation (Z := Unit)
      (.pageMap (.archObjectCap (.pageCap dev p R .vmVSpaceMap sz (some (asid, va)))) cte (.vmPTE pte, slot) pm) σ1).1 ∧
    ¬ (performPageInvocation (Z := Unit)
      (.pageMap (.archObjectCap (.pageCap dev p R .vmVSpaceMap sz (some (asid, va)))) cte (.vmPTE pte, slot) pm) σ1).2 := by
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
