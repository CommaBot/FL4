/-
P3 (DESIGN.md §9), CSpace: l4v `decode_cnode_invocation` split at its
binds, for the Copy, Mint, Move and Mutate labels.

`copyTail`, `copyBody` and `copyRest` are the spec's text after the target
slot lookup, after the extra-cap check and after the source cap read;
`cnodeDecode_eq` says (by `rfl`) that they are the pieces of
`decode_cnode_invocation`. The lemmas below compute them for
the four labels.
-/
import Fl4Proofs.P3.Restart
import Fl4Spec.Decode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open Classical Fl4Spec

noncomputable section

/-- The spec after the source cap is read: the per-label arguments, the
new cap, the invocation. -/
def copyRest (label : Data) (args : List Data) (srcSlot destSlot : CslotPtr) (srcCap : Cap) :
    SEMonad Unit CnodeInvocation := do
    let (rights, capData, isMove) ← (match genInvocationType label, args with
      | .cnodeCopy, rightsWord :: _ => do
        let rights ← NonDetE.returnOk <| dataToRights <| rightsWord
        NonDetE.returnOk <| (rights, none, false)
      | .cnodeMint, rightsWord :: capData :: _ => do
        let rights ← NonDetE.returnOk <| dataToRights <| rightsWord
        NonDetE.returnOk <| (rights, some capData, false)
      | .cnodeMove, _ => NonDetE.returnOk (allRights, none, true)
      | .cnodeMutate, capData :: _ => NonDetE.returnOk (allRights, some capData, true)
      | _, _ => NonDetE.throwError .truncatedMessage : SEMonad Unit (CapRights × Option Data × Bool))
    let srcCap ← NonDetE.returnOk <| maskCap rights srcCap
    let newCap ← (if isMove then NonDetE.returnOk else deriveCap srcSlot) (match capData with
      | some w => updateCapData isMove w srcCap
      | none => srcCap)
    NonDetE.whenE (newCap = .nullCap) <| NonDetE.throwError .illegalOperation
    NonDetE.returnOk <| (if isMove then CnodeInvocation.moveCall else .insertCall) newCap srcSlot destSlot

/-- The spec's Copy/Mint/Move/Mutate branch. -/
def copyBody (label : Data) (args : List Data) (excaps : List Cap) (destSlot : CslotPtr) :
    SEMonad Unit CnodeInvocation := do
    let srcIndex ← NonDetE.returnOk <| dataToCptr <| the args[0]?
    let srcDepth ← NonDetE.returnOk <| dataToNat <| the args[1]?
    let args ← NonDetE.returnOk <| args.drop 2
    let srcRootCap ← NonDetE.returnOk <| the excaps[0]?
    ensureEmpty destSlot
    let srcSlot ←
      lookupSourceSlot srcRootCap srcIndex srcDepth
    let srcCap ← NonDetE.liftE <| getCap srcSlot
    NonDetE.whenE (srcCap = .nullCap) <|
      NonDetE.throwError <| .failedLookup true <| .missingCapability srcDepth
    copyRest label args srcSlot destSlot srcCap

/-- The spec after the target slot lookup. -/
def copyTail (label : Data) (args : List Data) (excaps : List Cap) (destSlot : CslotPtr) :
    SEMonad Unit CnodeInvocation :=
  if args.length ≥ 2 ∧ excaps.length > 0
        ∧ genInvocationType label ∈ GenInvocationLabels.uptoEnum .cnodeCopy .cnodeMutate then
    copyBody label args excaps destSlot
  else if genInvocationType label = .cnodeRevoke then NonDetE.returnOk <| .revokeCall destSlot
  else if genInvocationType label = .cnodeDelete then NonDetE.returnOk <| .deleteCall destSlot
  else if genInvocationType label = .cnodeCancelBadgedSends then do
    let cap ← NonDetE.liftE <| getCap destSlot
    NonDetE.unlessE (hasCancelSendRights cap) <| NonDetE.throwError .illegalOperation
    NonDetE.returnOk <| .cancelBadgedSendsCall cap
  else if genInvocationType label = .cnodeRotate ∧ args.length > 5
          ∧ excaps.length > 1 then
  do
    let pivotNewData ← NonDetE.returnOk <| the args[0]?
    let pivotIndex ← NonDetE.returnOk <| dataToCptr <| the args[1]?
    let pivotDepth ← NonDetE.returnOk <| dataToNat <| the args[2]?
    let srcNewData ← NonDetE.returnOk <| the args[3]?
    let srcIndex ← NonDetE.returnOk <| dataToCptr <| the args[4]?
    let srcDepth ← NonDetE.returnOk <| dataToNat <| the args[5]?
    let pivotRootCap ← NonDetE.returnOk <| the excaps[0]?
    let srcRootCap ← NonDetE.returnOk <| the excaps[1]?

    let srcSlot ← lookupSourceSlot srcRootCap srcIndex srcDepth
    let pivotSlot ← lookupPivotSlot pivotRootCap pivotIndex pivotDepth

    NonDetE.whenE (pivotSlot = srcSlot ∨ pivotSlot = destSlot) <|
      NonDetE.throwError .illegalOperation

    NonDetE.unlessE (srcSlot = destSlot) <| ensureEmpty destSlot

    let srcCap ← NonDetE.liftE <| getCap srcSlot
    NonDetE.whenE (srcCap = .nullCap) <|
      NonDetE.throwError <| .failedLookup true <| .missingCapability srcDepth

    let pivotCap ← NonDetE.liftE <| getCap pivotSlot
    NonDetE.whenE (pivotCap = .nullCap) <|
      NonDetE.throwError <| .failedLookup false <| .missingCapability pivotDepth

    let newSrcCap ← NonDetE.returnOk <| updateCapData true srcNewData srcCap
    let newPivotCap ← NonDetE.returnOk <| updateCapData true pivotNewData pivotCap

    NonDetE.whenE (newSrcCap = .nullCap) <| NonDetE.throwError .illegalOperation
    NonDetE.whenE (newPivotCap = .nullCap) <| NonDetE.throwError .illegalOperation

    NonDetE.returnOk <| .rotateCall newSrcCap newPivotCap srcSlot pivotSlot destSlot
  else
    NonDetE.throwError .truncatedMessage

theorem cnodeDecode_eq (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) :
    decodeCnodeInvocation (Z := Unit) label args cap excaps = (do
      NonDetE.unlessE (genInvocationType label ∈ GenInvocationLabels.uptoEnum .cnodeRevoke .cnodeRotate) <|
        NonDetE.throwError .illegalOperation
      NonDetE.whenE (args.length < 2) (NonDetE.throwError .truncatedMessage)
      let index ← NonDetE.returnOk <| dataToCptr <| the args[0]?
      let bits ← NonDetE.returnOk <| dataToNat <| the args[1]?
      let args ← NonDetE.returnOk <| args.drop 2
      let destSlot ← lookupTargetSlot cap index bits
      copyTail label args excaps destSlot) := rfl

/-! ## Computing the pieces -/

/-- The spec's outcome after the new cap: an error, `IllegalOperation` for
a null cap, or the insert/move invocation. -/
def finishRes (mv : Bool) (srcSlot destSlot : CslotPtr) : Except SyscallError Cap →
    Except SyscallError CnodeInvocation
  | .error e => .error e
  | .ok nc => if nc = Cap.nullCap then .error .illegalOperation
      else .ok ((if mv then CnodeInvocation.moveCall else .insertCall) nc srcSlot destSlot)

theorem run_finish (m : SEMonad Unit Cap) (mv : Bool) (srcSlot destSlot : CslotPtr) (σ : State Unit)
    {r' : Except SyscallError Cap} (hm : m.run σ = ({(r', σ)}, False)) :
    (do
      let newCap ← m
      NonDetE.whenE (newCap = Cap.nullCap) <| NonDetE.throwError .illegalOperation
      NonDetE.returnOk <| (if mv then CnodeInvocation.moveCall else .insertCall) newCap srcSlot destSlot :
        SEMonad Unit CnodeInvocation).run σ =
      ({(finishRes mv srcSlot destSlot r', σ)}, False) := by
  cases r' with
  | error e => rw [run_bind_error hm]; rfl
  | ok nc =>
    rw [run_bind_ok hm]
    by_cases hn : nc = .nullCap
    · simp only [NonDetE.whenE, hn, ↓reduceIte, NonDetE.throwError, ndE_throw_bind]
      simp [finishRes]
    · simp only [NonDetE.whenE, hn, ↓reduceIte, ndE_pure_bind]
      simp [finishRes, hn]

section
variable (label : Data) (srcSlot destSlot : CslotPtr) (srcCap : Cap) (σ : State Unit)

theorem copyRest_copy (hgt : genInvocationType label = .cnodeCopy) (w : Data) (rest : List Data)
    {r' : Except SyscallError Cap}
    (hd : (deriveCap (Z := Unit) srcSlot (maskCap (dataToRights w) srcCap)).run σ = ({(r', σ)}, False)) :
    (copyRest label (w :: rest) srcSlot destSlot srcCap).run σ =
      ({(finishRes false srcSlot destSlot r', σ)}, False) := by
  unfold copyRest
  simp only [hgt, NonDetE.returnOk, ndE_pure_bind]
  exact run_finish _ false _ _ σ hd

theorem copyRest_mint (hgt : genInvocationType label = .cnodeMint) (w d : Data) (rest : List Data)
    {r' : Except SyscallError Cap}
    (hd : (deriveCap (Z := Unit) srcSlot (updateCapData false d (maskCap (dataToRights w) srcCap))).run σ =
      ({(r', σ)}, False)) :
    (copyRest label (w :: d :: rest) srcSlot destSlot srcCap).run σ =
      ({(finishRes false srcSlot destSlot r', σ)}, False) := by
  unfold copyRest
  simp only [hgt, NonDetE.returnOk, ndE_pure_bind]
  exact run_finish _ false _ _ σ hd

theorem copyRest_move (hgt : genInvocationType label = .cnodeMove) (args : List Data) :
    (copyRest label args srcSlot destSlot srcCap).run σ =
      ({(finishRes true srcSlot destSlot (.ok (maskCap allRights srcCap)), σ)}, False) := by
  unfold copyRest
  simp only [hgt, NonDetE.returnOk, ndE_pure_bind, ↓reduceIte]
  by_cases hn : maskCap allRights srcCap = Cap.nullCap
  · simp only [NonDetE.whenE, hn, ↓reduceIte, NonDetE.throwError, ndE_throw_bind]; simp [finishRes]
  · simp only [NonDetE.whenE, hn, ↓reduceIte, ndE_pure_bind]; simp [finishRes, hn]

theorem copyRest_mutate (hgt : genInvocationType label = .cnodeMutate) (d : Data) (rest : List Data) :
    (copyRest label (d :: rest) srcSlot destSlot srcCap).run σ =
      ({(finishRes true srcSlot destSlot (.ok (updateCapData true d (maskCap allRights srcCap))), σ)}, False) := by
  unfold copyRest
  simp only [hgt, NonDetE.returnOk, ndE_pure_bind, ↓reduceIte]
  by_cases hn : updateCapData true d (maskCap allRights srcCap) = Cap.nullCap
  · simp only [NonDetE.whenE, hn, ↓reduceIte, NonDetE.throwError, ndE_throw_bind]; simp [finishRes]
  · simp only [NonDetE.whenE, hn, ↓reduceIte, ndE_pure_bind]; simp [finishRes, hn]

theorem copyRest_trunc (args : List Data)
    (h : (genInvocationType label = .cnodeCopy ∧ args = []) ∨
      (genInvocationType label = .cnodeMint ∧ args.length < 2) ∨
      (genInvocationType label = .cnodeMutate ∧ args = [])) :
    (copyRest label args srcSlot destSlot srcCap).run σ = ({(.error .truncatedMessage, σ)}, False) := by
  unfold copyRest
  rcases h with ⟨hg, rfl⟩ | ⟨hg, hl⟩ | ⟨hg, rfl⟩
  · simp only [hg, NonDetE.throwError, ndE_throw_bind]; rfl
  · match args, hl with
    | [], _ => simp only [hg, NonDetE.throwError, ndE_throw_bind]; rfl
    | [_], _ => simp only [hg, NonDetE.throwError, ndE_throw_bind]; rfl
  · simp only [hg, NonDetE.throwError, ndE_throw_bind]; rfl

end

/-! ## Labels -/

/-- The four labels this file covers. -/
def IsCopyLabel (g : GenInvocationLabels) : Prop :=
  g = .cnodeCopy ∨ g = .cnodeMint ∨ g = .cnodeMove ∨ g = .cnodeMutate

theorem IsCopyLabel.facts {g : GenInvocationLabels} (h : IsCopyLabel g) :
    g ∈ GenInvocationLabels.uptoEnum .cnodeRevoke .cnodeRotate ∧
    g ∈ GenInvocationLabels.uptoEnum .cnodeCopy .cnodeMutate ∧
    g ≠ .cnodeRevoke ∧ g ≠ .cnodeDelete ∧ g ≠ .cnodeCancelBadgedSends ∧ g ≠ .cnodeRotate := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-! ## The prefix and the branch -/

section
variable (label : Data) (cap : Cap) (excaps : List Cap) (σ : State Unit)

theorem decode_short (h1 : genInvocationType label ∈ GenInvocationLabels.uptoEnum .cnodeRevoke .cnodeRotate)
    (args : List Data) (hl : args.length < 2) :
    (decodeCnodeInvocation (Z := Unit) label args cap excaps).run σ = ({(.error .truncatedMessage, σ)}, False) := by
  rw [cnodeDecode_eq]
  simp only [NonDetE.unlessE, h1, ↓reduceIte, ndE_pure_bind, NonDetE.whenE, hl, NonDetE.throwError,
    ndE_throw_bind]
  rfl

theorem decode_lookup (h1 : genInvocationType label ∈ GenInvocationLabels.uptoEnum .cnodeRevoke .cnodeRotate)
    (x0 x1 : Data) (rest : List Data) :
    decodeCnodeInvocation (Z := Unit) label (x0 :: x1 :: rest) cap excaps =
      (lookupTargetSlot cap (dataToCptr x0) (dataToNat x1) >>= fun d => copyTail label rest excaps d) := by
  rw [cnodeDecode_eq]
  simp [NonDetE.unlessE, h1, NonDetE.whenE, NonDetE.returnOk, the]

theorem copyTail_short (hg : IsCopyLabel (genInvocationType label)) (args : List Data) (d : CslotPtr)
    (h : ¬ (args.length ≥ 2 ∧ excaps.length > 0)) :
    copyTail label args excaps d = NonDetE.throwError .truncatedMessage := by
  obtain ⟨-, -, h3, h4, h5, h6⟩ := hg.facts
  unfold copyTail
  have : ¬ (args.length ≥ 2 ∧ excaps.length > 0 ∧
      genInvocationType label ∈ GenInvocationLabels.uptoEnum .cnodeCopy .cnodeMutate) :=
    fun ⟨a, b, _⟩ => h ⟨a, b⟩
  simp only [this, h3, h4, h5, false_and, ↓reduceIte, h6]

theorem copyTail_body (hg : IsCopyLabel (genInvocationType label)) (y0 y1 : Data) (rest : List Data)
    (a0 : Cap) (erest : List Cap) (d : CslotPtr) :
    copyTail label (y0 :: y1 :: rest) (a0 :: erest) d = (do
      ensureEmpty d
      let srcSlot ← lookupSourceSlot a0 (dataToCptr y0) (dataToNat y1)
      let srcCap ← NonDetE.liftE <| getCap srcSlot
      NonDetE.whenE (srcCap = .nullCap) <|
        NonDetE.throwError <| .failedLookup true <| .missingCapability (dataToNat y1)
      copyRest label rest srcSlot d srcCap) := by
  obtain ⟨-, h2, -⟩ := hg.facts
  unfold copyTail copyBody
  simp [h2, NonDetE.returnOk, the]

end

theorem ensureEmpty_run (sl : CslotPtr) (σ : State Unit) {c : Cap} (hc : getCap (Z := Unit) sl σ = ({(c, σ)}, False)) :
    (ensureEmpty (Z := Unit) sl).run σ =
      ({(if c = .nullCap then .ok () else .error .deleteFirst, σ)}, False) := by
  unfold ensureEmpty
  rw [run_bind_ok (run_liftE hc)]
  by_cases h : c = .nullCap
  · simp only [NonDetE.whenE, h, ne_eq, not_true_eq_false, ↓reduceIte]; rfl
  · simp only [NonDetE.whenE, h, ne_eq, not_false_eq_true, ↓reduceIte]; rfl

end

end Fl4Proofs.P3
