/-
P3 (DESIGN.md §9), VSpace: **PageTable `Map`, the spec side**: l4v's
`decode_page_table_invocation` with label `X64PageTableMap`, and
`perform_page_table_invocation` of the `PageTableMap` it returns.

* `ptDecode_trunc`, `ptDecode_mapped`, `ptDecode_badVs`, `ptDecode_body`:
  the decode up to the PML4 cap, after which it continues with `ptTail`;
* `ptTail_*`: the decode's outcome for each check;
* `storePde_at`, `performPtMap_mem`: the perform.
-/
import Fl4Proofs.P3.VsFrameMapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Spec
open Fl4Spec

open Classical in
/-- The spec's PageTable Map after the PML4 cap. -/
def ptTail (p pm : ObjRef) (asid : Asid) (vaddr' attr : Data) (cte : CslotPtr) : SEMonad Unit ArchInvocation := do
  NonDetE.whenE (userVtop < vaddr') (NonDetE.throwError (.invalidArgument 0))
  let pml4' ← lookupErrorOnFailure false (findVspaceForAsid asid)
  NonDetE.whenE (pml4' ≠ pm) (NonDetE.throwError (.invalidCapability 1))
  let pdSlot ← lookupErrorOnFailure false (lookupPdSlot pm vaddr')
  let oldPde ← NonDetE.liftE (getPde pdSlot)
  NonDetE.unlessE (oldPde = .invalidPDE) (NonDetE.throwError .deleteFirst)
  let pde ← NonDetE.returnOk (PDE.pageTablePDE (addrFromPPtr p)
    (filterVmAttributes (attribsFromWord attr)) vmReadWrite)
  let cap' ← NonDetE.returnOk (Cap.archObjectCap (.pageTableCap p (some (asid, vaddr'))))
  NonDetE.returnOk (.invokePageTable (.pageTableMap cap' cte pde pdSlot pm))

/-- The page-table map the spec decodes. -/
def ptInv (p pm : ObjRef) (asid : Asid) (vaddr' attr : Data) (cte : CslotPtr) (slot : ObjRef) : ArchInvocation :=
  .invokePageTable (.pageTableMap (.archObjectCap (.pageTableCap p (some (asid, vaddr')))) cte
    (.pageTablePDE (addrFromPPtr p) (filterVmAttributes (attribsFromWord attr)) vmReadWrite) slot pm)

theorem ptDecode_trunc {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageTableMap)
    (args : List Data) (cte : CslotPtr) (p : ObjRef) (ma : Option (Asid × VSpaceRef)) (ex : List (Cap × CslotPtr))
    (h : ¬ (args.length > 1 ∧ ex.length > 0)) (σ : State Unit) :
    ExceptT.run (decodePageTableInvocation (Z := Unit) lbl args cte (.pageTableCap p ma) ex) σ =
      ({(.error .truncatedMessage, σ)}, False) := by
  unfold decodePageTableInvocation
  dsimp only
  rw [if_pos hl, if_neg h]
  rfl

theorem ptDecode_mapped {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageTableMap)
    (a0 a1 : Data) (rest : List Data) (cte : CslotPtr) (p : ObjRef) (m : Asid × VSpaceRef) (xc : Cap × CslotPtr)
    (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    ExceptT.run (decodePageTableInvocation (Z := Unit) lbl (a0 :: a1 :: rest) cte (.pageTableCap p (some m))
      (xc :: ex)) σ = ({(.error (.invalidCapability 0), σ)}, False) := by
  unfold decodePageTableInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp)]
  exact runE_bind_err (by rw [runE_whenE_true (by simp)]; rfl)

theorem ptDecode_badVs {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageTableMap)
    (a0 a1 : Data) (rest : List Data) (cte : CslotPtr) (p : ObjRef) (vc : Cap) (xsl : CslotPtr)
    (ex : List (Cap × CslotPtr)) (hvc : ∀ pm asid, vc ≠ .archObjectCap (.pml4Cap pm (some asid))) (σ : State Unit) :
    ExceptT.run (decodePageTableInvocation (Z := Unit) lbl (a0 :: a1 :: rest) cte (.pageTableCap p none)
      ((vc, xsl) :: ex)) σ = ({(.error (.invalidCapability 1), σ)}, False) := by
  unfold decodePageTableInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp), runE_bind_ok (runE_whenE_false (by simp) _ σ),
    runE_bind_ok (runE_ret _ σ)]
  split
  · rename_i pm asid h
    exact absurd h (hvc pm asid)
  · exact runE_bind_err (runE_throw _ σ)

theorem ptDecode_body {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageTableMap)
    (a0 a1 : Data) (rest : List Data) (cte : CslotPtr) (p pm : ObjRef) (asid : Asid) (xsl : CslotPtr)
    (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    ExceptT.run (decodePageTableInvocation (Z := Unit) lbl (a0 :: a1 :: rest) cte (.pageTableCap p none)
      ((.archObjectCap (.pml4Cap pm (some asid)), xsl) :: ex)) σ =
      ExceptT.run (ptTail p pm asid (a0 &&& ~~~mask pdShiftBits) a1 cte) σ := by
  unfold decodePageTableInvocation
  dsimp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Fl4Spec.the]
  rw [if_pos hl, if_pos (by simp), runE_bind_ok (runE_whenE_false (by simp) _ σ),
    runE_bind_ok (runE_ret _ σ), runE_bind_ok (runE_ret _ σ)]
  rfl

theorem ptTail_top {p pm : ObjRef} {asid : Asid} {v attr : Data} {cte : CslotPtr} {σ : State Unit}
    (h : userVtop < v) :
    ExceptT.run (ptTail p pm asid v attr cte) σ = ({(.error (.invalidArgument 0), σ)}, False) := by
  unfold ptTail
  exact runE_bind_err (by rw [runE_whenE_true h]; rfl)

theorem ptTail_noVs {p pm : ObjRef} {asid : Asid} {v attr : Data} {cte : CslotPtr} {σ : State Unit}
    (h : ¬ userVtop < v) {lf : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.error lf, σ)}, False)) :
    ExceptT.run (ptTail p pm asid v attr cte) σ = ({(.error (.failedLookup false lf), σ)}, False) := by
  unfold ptTail lookupErrorOnFailure
  rw [runE_bind_ok (runE_whenE_false h _ σ)]
  exact runE_bind_err (by rw [runE_handle_err hf]; rfl)

theorem ptTail_wrongVs {p pm r1 : ObjRef} {asid : Asid} {v attr : Data} {cte : CslotPtr} {σ : State Unit}
    (h : ¬ userVtop < v)
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok r1, σ)}, False)) (hne : r1 ≠ pm) :
    ExceptT.run (ptTail p pm asid v attr cte) σ = ({(.error (.invalidCapability 1), σ)}, False) := by
  unfold ptTail lookupErrorOnFailure
  rw [runE_bind_ok (runE_whenE_false h _ σ), runE_bind_ok (runE_handle_ok hf)]
  exact runE_bind_err (by rw [runE_whenE_true hne]; rfl)

open Classical in
theorem ptTail_prefix {p pm : ObjRef} {asid : Asid} {v attr : Data} {cte : CslotPtr} {σ : State Unit}
    (h : ¬ userVtop < v)
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False)) :
    ExceptT.run (ptTail p pm asid v attr cte) σ = ExceptT.run (do
      let pdSlot ← lookupErrorOnFailure false (lookupPdSlot pm v)
      let oldPde ← NonDetE.liftE (getPde pdSlot)
      NonDetE.unlessE (oldPde = .invalidPDE) (NonDetE.throwError .deleteFirst)
      let pde ← NonDetE.returnOk (PDE.pageTablePDE (addrFromPPtr p)
        (filterVmAttributes (attribsFromWord attr)) vmReadWrite)
      let cap' ← NonDetE.returnOk (Cap.archObjectCap (.pageTableCap p (some (asid, v))))
      NonDetE.returnOk (ε := SyscallError) (ArchInvocation.invokePageTable (.pageTableMap cap' cte pde pdSlot pm))) σ := by
  unfold ptTail lookupErrorOnFailure
  rw [runE_bind_ok (runE_whenE_false h _ σ), runE_bind_ok (runE_handle_ok hf),
    runE_bind_ok (runE_whenE_false (by simp) _ σ)]

theorem ptTail_noSlot {p pm : ObjRef} {asid : Asid} {v attr : Data} {cte : CslotPtr} {σ : State Unit}
    (h : ¬ userVtop < v)
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False)) {lf : LookupFailure}
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) pm v) σ = ({(.error lf, σ)}, False)) :
    ExceptT.run (ptTail p pm asid v attr cte) σ = ({(.error (.failedLookup false lf), σ)}, False) := by
  rw [ptTail_prefix h hf]
  unfold lookupErrorOnFailure
  exact runE_bind_err (by rw [runE_handle_err hl]; rfl)

theorem ptTail_used {p pm : ObjRef} {asid : Asid} {v attr : Data} {cte : CslotPtr} {σ : State Unit}
    (h : ¬ userVtop < v)
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False)) {slot : ObjRef}
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) pm v) σ = ({(.ok slot, σ)}, False)) {pde : PDE}
    (hg : getPde (Z := Unit) slot σ = ({(pde, σ)}, False)) (hne : pde ≠ .invalidPDE) :
    ExceptT.run (ptTail p pm asid v attr cte) σ = ({(.error .deleteFirst, σ)}, False) := by
  rw [ptTail_prefix h hf]
  unfold lookupErrorOnFailure
  rw [runE_bind_ok (runE_handle_ok hl), runE_bind_ok (runE_liftE hg)]
  exact runE_bind_err (by rw [runE_unlessE_false hne]; rfl)

theorem ptTail_ok {p pm : ObjRef} {asid : Asid} {v attr : Data} {cte : CslotPtr} {σ : State Unit}
    (h : ¬ userVtop < v)
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False)) {slot : ObjRef}
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) pm v) σ = ({(.ok slot, σ)}, False))
    (hg : getPde (Z := Unit) slot σ = ({(.invalidPDE, σ)}, False)) :
    ExceptT.run (ptTail p pm asid v attr cte) σ = ({(.ok (ptInv p pm asid v attr cte slot), σ)}, False) := by
  rw [ptTail_prefix h hf]
  unfold lookupErrorOnFailure
  rw [runE_bind_ok (runE_handle_ok hl), runE_bind_ok (runE_liftE hg),
    runE_bind_ok (runE_unlessE_true rfl _ σ), runE_bind_ok (runE_ret _ σ), runE_bind_ok (runE_ret _ σ)]
  rfl

theorem storePde_at {σ : State Unit} {q : U64} (hq : q.val % 4096 = 0) {f : BitVec 9 → PDE}
    (hk : σ.kheap q.bv = some (.archObj (.pageDirectory f))) {j : U64} (hj : j.val < 512) (pde : PDE) :
    storePde (Z := Unit) (q.bv + (j.bv <<< wordSizeBits)) pde σ =
      ({((), updK σ q.bv (.archObj (.pageDirectory (Function.update f (ucast 9 j.bv) pde))))}, False) := by
  obtain ⟨h1, h2⟩ := split_slot q.bv j.bv hq hj
  unfold storePde
  rw [nd_pure_bind', nd_pure_bind']
  simp only [pdBits, tableSize, ptTranslationBits, wordSizeBits] at h1 h2 ⊢
  rw [h1, h2, nd_bind_one (show getPd (Z := Unit) q.bv σ = ({(f, σ)}, False) by
    unfold getPd; rw [nd_bind_one (getObject_eq hk)]; rfl), nd_pure_bind']
  exact setObject_eq hk rfl

/-- The spec after the decode: `set_thread_state cur Restart`, then the
perform; `σ'` is one of its outcomes, and it does not fail. -/
def PtMapSpec (σ : State Unit) (iv : ArchInvocation) (σ' : State Unit) : Prop :=
  match iv with
  | .invokePageTable pi =>
    ((), σ') ∈ ((setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
      performPageTableInvocation pi) σ).1 ∧
    ¬ ((setThreadState (Z := Unit) σ.curThread .restart >>= fun _ => performPageTableInvocation pi) σ).2
  | _ => False

theorem performPtMap_mem {p : ObjRef} {asid : Asid} {va : VSpaceRef} {cte : CslotPtr} {pde : PDE}
    {slot pm : ObjRef} {σ1 σ2 σ3 σ' : State Unit}
    (hsc : setCap (Z := Unit) (.archObjectCap (.pageTableCap p (some (asid, va)))) cte σ1 = ({((), σ2)}, False))
    (hsp : storePde (Z := Unit) slot pde σ2 = ({((), σ3)}, False))
    (hm : ((), σ') ∈ (invalidatePageStructureCacheAsid (Z := Unit) (addrFromPPtr pm) asid σ3).1)
    (hnf : ¬ (invalidatePageStructureCacheAsid (Z := Unit) (addrFromPPtr pm) asid σ3).2) :
    ((), σ') ∈ (performPageTableInvocation (Z := Unit)
      (.pageTableMap (.archObjectCap (.pageTableCap p (some (asid, va)))) cte pde slot pm) σ1).1 ∧
    ¬ (performPageTableInvocation (Z := Unit)
      (.pageTableMap (.archObjectCap (.pageTableCap p (some (asid, va)))) cte pde slot pm) σ1).2 := by
  unfold performPageTableInvocation
  dsimp only
  rw [nd_bind_one hsc, nd_bind_one hsp, nd_pure_bind']
  exact ⟨hm, hnf⟩

end Spec

end

end Fl4Proofs.P3.Vs
