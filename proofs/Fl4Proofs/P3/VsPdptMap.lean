/-
P3 (DESIGN.md §9), VSpace: **PDPT `Map`, the spec side**: l4v's
`decode_pdpt_invocation` with label `X64PDPTMap`, and
`perform_pdpt_invocation` of the `PDPTMap` it returns. As VsPdMap, except
that the PML4 slot is computed (`lookup_pml4_slot`), not looked up.

* `pdptDecode_trunc`, `pdptDecode_mapped`, `pdptDecode_badVs`, `pdptDecode_body`:
  the decode up to the PML4 cap, after which it continues with `pdptTail`;
* `pdptTail_*`: the decode's outcome for each check;
* `storePml4e_at`, `performPdptMap_mem`: the perform.
-/
import Fl4Proofs.P3.VsPdUnmapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Spec
open Fl4Spec

open Classical in
/-- The spec's PDPT Map after the PML4 cap. -/
def pdptTail (p pm : ObjRef) (asid : Asid) (vaddr' attr : Data) (cte : CslotPtr) : SEMonad Unit ArchInvocation := do
  NonDetE.whenE (userVtop < vaddr') (NonDetE.throwError (.invalidArgument 0))
  let pml4' ← lookupErrorOnFailure false (findVspaceForAsid asid)
  NonDetE.whenE (pml4' ≠ pm) (NonDetE.throwError (.invalidCapability 1))
  let pdSlot ← NonDetE.returnOk (lookupPml4Slot pm vaddr')
  let oldPde ← NonDetE.liftE (getPml4e pdSlot)
  NonDetE.unlessE (oldPde = .invalidPML4E) (NonDetE.throwError .deleteFirst)
  let pde ← NonDetE.returnOk (PML4E.pdPointerTablePML4E (addrFromPPtr p)
    (filterVmAttributes (attribsFromWord attr)) vmReadWrite)
  let cap' ← NonDetE.returnOk (Cap.archObjectCap (.pdPointerTableCap p (some (asid, vaddr'))))
  NonDetE.returnOk (.invokePDPT (.pdptMap cap' cte pde pdSlot pm))

/-- The PDPT map the spec decodes. -/
def pdptInv (p pm : ObjRef) (asid : Asid) (vaddr' attr : Data) (cte : CslotPtr) (slot : ObjRef) : ArchInvocation :=
  .invokePDPT (.pdptMap (.archObjectCap (.pdPointerTableCap p (some (asid, vaddr')))) cte
    (.pdPointerTablePML4E (addrFromPPtr p) (filterVmAttributes (attribsFromWord attr)) vmReadWrite) slot pm)

theorem pdptDecode_trunc {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PDPTMap)
    (args : List Data) (cte : CslotPtr) (p : ObjRef) (ma : Option (Asid × VSpaceRef)) (ex : List (Cap × CslotPtr))
    (h : ¬ (args.length > 1 ∧ ex.length > 0)) (σ : State Unit) :
    ExceptT.run (decodePdptInvocation (Z := Unit) lbl args cte (.pdPointerTableCap p ma) ex) σ =
      ({(.error .truncatedMessage, σ)}, False) := by
  unfold decodePdptInvocation
  dsimp only
  rw [if_pos hl, if_neg h]
  rfl

theorem pdptDecode_mapped {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PDPTMap)
    (a0 a1 : Data) (rest : List Data) (cte : CslotPtr) (p : ObjRef) (m : Asid × VSpaceRef) (xc : Cap × CslotPtr)
    (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    ExceptT.run (decodePdptInvocation (Z := Unit) lbl (a0 :: a1 :: rest) cte (.pdPointerTableCap p (some m))
      (xc :: ex)) σ = ({(.error (.invalidCapability 0), σ)}, False) := by
  unfold decodePdptInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp)]
  exact runE_bind_err (by rw [runE_whenE_true (by simp)]; rfl)

theorem pdptDecode_badVs {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PDPTMap)
    (a0 a1 : Data) (rest : List Data) (cte : CslotPtr) (p : ObjRef) (vc : Cap) (xsl : CslotPtr)
    (ex : List (Cap × CslotPtr)) (hvc : ∀ pm asid, vc ≠ .archObjectCap (.pml4Cap pm (some asid))) (σ : State Unit) :
    ExceptT.run (decodePdptInvocation (Z := Unit) lbl (a0 :: a1 :: rest) cte (.pdPointerTableCap p none)
      ((vc, xsl) :: ex)) σ = ({(.error (.invalidCapability 1), σ)}, False) := by
  unfold decodePdptInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp), runE_bind_ok (runE_whenE_false (by simp) _ σ),
    runE_bind_ok (runE_ret _ σ)]
  split
  · rename_i pm asid h
    exact absurd h (hvc pm asid)
  · exact runE_bind_err (runE_throw _ σ)

theorem pdptDecode_body {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PDPTMap)
    (a0 a1 : Data) (rest : List Data) (cte : CslotPtr) (p pm : ObjRef) (asid : Asid) (xsl : CslotPtr)
    (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    ExceptT.run (decodePdptInvocation (Z := Unit) lbl (a0 :: a1 :: rest) cte (.pdPointerTableCap p none)
      ((.archObjectCap (.pml4Cap pm (some asid)), xsl) :: ex)) σ =
      ExceptT.run (pdptTail p pm asid (a0 &&& ~~~mask pml4ShiftBits) a1 cte) σ := by
  unfold decodePdptInvocation
  dsimp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Fl4Spec.the]
  rw [if_pos hl, if_pos (by simp), runE_bind_ok (runE_whenE_false (by simp) _ σ),
    runE_bind_ok (runE_ret _ σ), runE_bind_ok (runE_ret _ σ)]
  rfl

theorem pdptTail_top {p pm : ObjRef} {asid : Asid} {v attr : Data} {cte : CslotPtr} {σ : State Unit}
    (h : userVtop < v) :
    ExceptT.run (pdptTail p pm asid v attr cte) σ = ({(.error (.invalidArgument 0), σ)}, False) := by
  unfold pdptTail
  exact runE_bind_err (by rw [runE_whenE_true h]; rfl)

theorem pdptTail_noVs {p pm : ObjRef} {asid : Asid} {v attr : Data} {cte : CslotPtr} {σ : State Unit}
    (h : ¬ userVtop < v) {lf : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.error lf, σ)}, False)) :
    ExceptT.run (pdptTail p pm asid v attr cte) σ = ({(.error (.failedLookup false lf), σ)}, False) := by
  unfold pdptTail lookupErrorOnFailure
  rw [runE_bind_ok (runE_whenE_false h _ σ)]
  exact runE_bind_err (by rw [runE_handle_err hf]; rfl)

theorem pdptTail_wrongVs {p pm r1 : ObjRef} {asid : Asid} {v attr : Data} {cte : CslotPtr} {σ : State Unit}
    (h : ¬ userVtop < v)
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok r1, σ)}, False)) (hne : r1 ≠ pm) :
    ExceptT.run (pdptTail p pm asid v attr cte) σ = ({(.error (.invalidCapability 1), σ)}, False) := by
  unfold pdptTail lookupErrorOnFailure
  rw [runE_bind_ok (runE_whenE_false h _ σ), runE_bind_ok (runE_handle_ok hf)]
  exact runE_bind_err (by rw [runE_whenE_true hne]; rfl)

open Classical in
theorem pdptTail_prefix {p pm : ObjRef} {asid : Asid} {v attr : Data} {cte : CslotPtr} {σ : State Unit}
    (h : ¬ userVtop < v)
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False)) :
    ExceptT.run (pdptTail p pm asid v attr cte) σ = ExceptT.run (do
      let oldPde ← NonDetE.liftE (getPml4e (lookupPml4Slot pm v))
      NonDetE.unlessE (oldPde = .invalidPML4E) (NonDetE.throwError .deleteFirst)
      let pde ← NonDetE.returnOk (PML4E.pdPointerTablePML4E (addrFromPPtr p)
        (filterVmAttributes (attribsFromWord attr)) vmReadWrite)
      let cap' ← NonDetE.returnOk (Cap.archObjectCap (.pdPointerTableCap p (some (asid, v))))
      NonDetE.returnOk (ε := SyscallError) (ArchInvocation.invokePDPT (.pdptMap cap' cte pde (lookupPml4Slot pm v) pm))) σ := by
  unfold pdptTail lookupErrorOnFailure
  rw [runE_bind_ok (runE_whenE_false h _ σ), runE_bind_ok (runE_handle_ok hf),
    runE_bind_ok (runE_whenE_false (by simp) _ σ), runE_bind_ok (runE_ret _ σ)]

theorem pdptTail_used {p pm : ObjRef} {asid : Asid} {v attr : Data} {cte : CslotPtr} {σ : State Unit}
    (h : ¬ userVtop < v)
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False)) {pde : PML4E}
    (hg : getPml4e (Z := Unit) (lookupPml4Slot pm v) σ = ({(pde, σ)}, False)) (hne : pde ≠ .invalidPML4E) :
    ExceptT.run (pdptTail p pm asid v attr cte) σ = ({(.error .deleteFirst, σ)}, False) := by
  rw [pdptTail_prefix h hf]
  rw [runE_bind_ok (runE_liftE hg)]
  exact runE_bind_err (by rw [runE_unlessE_false hne]; rfl)

theorem pdptTail_ok {p pm : ObjRef} {asid : Asid} {v attr : Data} {cte : CslotPtr} {σ : State Unit}
    (h : ¬ userVtop < v)
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok pm, σ)}, False))
    (hg : getPml4e (Z := Unit) (lookupPml4Slot pm v) σ = ({(.invalidPML4E, σ)}, False)) :
    ExceptT.run (pdptTail p pm asid v attr cte) σ =
      ({(.ok (pdptInv p pm asid v attr cte (lookupPml4Slot pm v)), σ)}, False) := by
  rw [pdptTail_prefix h hf]
  rw [runE_bind_ok (runE_liftE hg),
    runE_bind_ok (runE_unlessE_true rfl _ σ), runE_bind_ok (runE_ret _ σ), runE_bind_ok (runE_ret _ σ)]
  rfl

theorem storePml4e_at {σ : State Unit} {q : U64} (hq : q.val % 4096 = 0) {f : BitVec 9 → PML4E}
    (hk : σ.kheap q.bv = some (.archObj (.pageMapL4 f))) {j : U64} (hj : j.val < 512) (pde : PML4E) :
    storePml4e (Z := Unit) (q.bv + (j.bv <<< wordSizeBits)) pde σ =
      ({((), updK σ q.bv (.archObj (.pageMapL4 (Function.update f (ucast 9 j.bv) pde))))}, False) := by
  obtain ⟨h1, h2⟩ := split_slot q.bv j.bv hq hj
  unfold storePml4e
  rw [nd_pure_bind', nd_pure_bind']
  simp only [pml4Bits, tableSize, ptTranslationBits, wordSizeBits] at h1 h2 ⊢
  rw [h1, h2, nd_bind_one (show getPml4 (Z := Unit) q.bv σ = ({(f, σ)}, False) by
    unfold getPml4; rw [nd_bind_one (getObject_eq hk)]; rfl), nd_pure_bind']
  exact setObject_eq hk rfl

/-- The spec after the decode: `set_thread_state cur Restart`, then the
perform; `σ'` is one of its outcomes, and it does not fail. -/
def PdptMapSpec (σ : State Unit) (iv : ArchInvocation) (σ' : State Unit) : Prop :=
  match iv with
  | .invokePDPT pi =>
    ((), σ') ∈ ((setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
      performPdptInvocation pi) σ).1 ∧
    ¬ ((setThreadState (Z := Unit) σ.curThread .restart >>= fun _ => performPdptInvocation pi) σ).2
  | _ => False

theorem performPdptMap_mem {p : ObjRef} {asid : Asid} {va : VSpaceRef} {cte : CslotPtr} {pde : PML4E}
    {slot pm : ObjRef} {σ1 σ2 σ3 σ' : State Unit}
    (hsc : setCap (Z := Unit) (.archObjectCap (.pdPointerTableCap p (some (asid, va)))) cte σ1 = ({((), σ2)}, False))
    (hsp : storePml4e (Z := Unit) slot pde σ2 = ({((), σ3)}, False))
    (hm : ((), σ') ∈ (invalidatePageStructureCacheAsid (Z := Unit) (addrFromPPtr pm) asid σ3).1)
    (hnf : ¬ (invalidatePageStructureCacheAsid (Z := Unit) (addrFromPPtr pm) asid σ3).2) :
    ((), σ') ∈ (performPdptInvocation (Z := Unit)
      (.pdptMap (.archObjectCap (.pdPointerTableCap p (some (asid, va)))) cte pde slot pm) σ1).1 ∧
    ¬ (performPdptInvocation (Z := Unit)
      (.pdptMap (.archObjectCap (.pdPointerTableCap p (some (asid, va)))) cte pde slot pm) σ1).2 := by
  unfold performPdptInvocation
  dsimp only
  rw [nd_bind_one hsc, nd_bind_one hsp, nd_pure_bind']
  exact ⟨hm, hnf⟩

end Spec

end

end Fl4Proofs.P3.Vs
