/-
P3 (issue #16, fb3j): **`decodeFrameBatch` as a pure function** (spec side
only), for the FrameBatch decode's refinement (XTopJointVsFb).

* `fbDecP p asid args ex`: the decode after the address-space check, its
  checks in the spec's order (`Except`).
* `decodeFrameBatch_noVs` / `_wrongVs`: the address-space check failing,
  `InvalidCapability 0`.
* **`decodeFrameBatch_run`**: with the ASID still naming `p`, the decode
  has the single outcome `fbDecP p asid args ex`, the state unchanged.
-/
import Fl4Proofs.P3.VsFrameMap
import Fl4Proofs.P3.VsAssign
open Classical

namespace Fl4Proofs.P3.Vs
open Fl4Spec

noncomputable section

/-- The decode after the header's checks, for the op `op`. -/
def fbDecQ (p : ObjRef) (asid : Asid) (args : List Data) (ex : List (Cap × CslotPtr)) (op : FbOp) :
    Except SyscallError Fl4FrameBatchInvocation :=
  if args.length < 1 + op.words * dataToNat ((the args[0]? >>> 8) &&& 0xff#64) then .error .truncatedMessage else
  if ex.length < 1 then .error .truncatedMessage else
  if isCnodeCap (the ex[0]?).1 = true then
  if isCnodeCap (if op = .copyMap ∧ ex.length > 1 then (the ex[1]?).1 else (the ex[0]?).1) = true then
  .ok { vspace := p, asid := asid, op := op, depth := dataToNat ((the args[0]? >>> 16) &&& 0x7f#64),
        mapRights := (the args[0]? >>> 24) &&& 0xf#64, capRights := (the args[0]? >>> 28) &&& 0xf#64,
        attr := (the args[0]? >>> 32) &&& 0x1f#64,
        deferDelete := decide (the args[0]? &&& (1#64 <<< 40) ≠ 0),
        cnode := (the ex[0]?).1,
        destCnode := if op = .copyMap ∧ ex.length > 1 then (the ex[1]?).1 else (the ex[0]?).1,
        entries := fbEntries args op.words (dataToNat ((the args[0]? >>> 8) &&& 0xff#64)) }
  else .error (.invalidCapability 2)
  else .error (.invalidCapability 1)

/-- The decode after the address-space check (`decodeFrameBatch`'s checks, in order). -/
def fbDecP (p : ObjRef) (asid : Asid) (args : List Data) (ex : List (Cap × CslotPtr)) :
    Except SyscallError Fl4FrameBatchInvocation :=
  if args.length < 1 then .error .truncatedMessage else
  match fbOpOf (dataToNat (the args[0]? &&& 0x3#64)) with
  | none => .error (.invalidArgument 0)
  | some op =>
    if the args[0]? &&& ~~~fbDefined ≠ 0 ∨ dataToNat ((the args[0]? >>> 16) &&& 0x7f#64) = 0 ∨
        dataToNat ((the args[0]? >>> 16) &&& 0x7f#64) > 64 then .error (.invalidArgument 0) else
    fbDecQ p asid args ex op

theorem fbDecP_short {p : ObjRef} {asid : Asid} {args : List Data} {ex : List (Cap × CslotPtr)}
    (h1 : args.length < 1) : fbDecP p asid args ex = .error .truncatedMessage := by
  unfold fbDecP; rw [if_pos h1]

/-- A header error. -/
theorem fbDecP_hdr {p : ObjRef} {asid : Asid} {args : List Data} {ex : List (Cap × CslotPtr)}
    (h1 : ¬ args.length < 1)
    (h : fbOpOf (dataToNat (the args[0]? &&& 0x3#64)) = none ∨
      (the args[0]? &&& ~~~fbDefined ≠ 0 ∨ dataToNat ((the args[0]? >>> 16) &&& 0x7f#64) = 0 ∨
        dataToNat ((the args[0]? >>> 16) &&& 0x7f#64) > 64)) :
    fbDecP p asid args ex = .error (.invalidArgument 0) := by
  unfold fbDecP; rw [if_neg h1]
  rcases h with h | h
  · rw [h]
  · cases hop : fbOpOf (dataToNat (the args[0]? &&& 0x3#64)) with
    | none => rfl
    | some op => exact if_pos h

/-- A good header. -/
theorem fbDecP_some {p : ObjRef} {asid : Asid} {args : List Data} {ex : List (Cap × CslotPtr)} {op : FbOp}
    (h1 : ¬ args.length < 1) (hop : fbOpOf (dataToNat (the args[0]? &&& 0x3#64)) = some op)
    (h2 : ¬ (the args[0]? &&& ~~~fbDefined ≠ 0 ∨ dataToNat ((the args[0]? >>> 16) &&& 0x7f#64) = 0 ∨
        dataToNat ((the args[0]? >>> 16) &&& 0x7f#64) > 64)) :
    fbDecP p asid args ex = fbDecQ p asid args ex op := by
  unfold fbDecP; rw [if_neg h1, hop]; exact if_neg h2

theorem fbd_whenE_bind {ε β : Type} (P : Prop) [Decidable P] (m : NonDetE (State Unit) ε Unit)
    (f : Unit → NonDetE (State Unit) ε β) (σ : State Unit) :
    ExceptT.run (NonDetE.whenE P m >>= f) σ = if P then ExceptT.run (m >>= f) σ else ExceptT.run (f ()) σ := by
  unfold NonDetE.whenE
  split
  · rfl
  · exact runE_bind_ok (runE_ret () σ)

theorem fbd_unlessE_bind {ε β : Type} (P : Prop) [Decidable P] (m : NonDetE (State Unit) ε Unit)
    (f : Unit → NonDetE (State Unit) ε β) (σ : State Unit) :
    ExceptT.run (NonDetE.unlessE P m >>= f) σ = if P then ExceptT.run (f ()) σ else ExceptT.run (m >>= f) σ := by
  unfold NonDetE.unlessE
  split
  · exact runE_bind_ok (runE_ret () σ)
  · rfl

theorem fbd_ret_bind {ε α β : Type} (x : α) (f : α → NonDetE (State Unit) ε β) (σ : State Unit) :
    ExceptT.run (NonDetE.returnOk x >>= f) σ = ExceptT.run (f x) σ := runE_bind_ok (runE_ret _ σ)

theorem fbd_throw_bind {ε α β : Type} (e : ε) (f : α → NonDetE (State Unit) ε β) (σ : State Unit) :
    ExceptT.run (NonDetE.throwError e >>= f) σ = ({(.error e, σ)}, False) :=
  runE_bind_err (runE_throw e σ)

/-- The address-space check failing (no PML4 for the ASID). -/
theorem decodeFrameBatch_noVs {p : ObjRef} {asid : Asid} {args : List Data} {ex : List (Cap × CslotPtr)}
    {σ : State Unit} {lf : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.error lf, σ)}, False)) :
    ExceptT.run (decodeFrameBatch (Z := Unit) args (.pml4Cap p (some asid)) ex) σ =
      ({(.error (.invalidCapability 0), σ)}, False) := by
  unfold decodeFrameBatch
  exact runE_bind_err (by rw [runE_handle_err hf]; rfl)

/-- The address-space check failing (the ASID names another PML4). -/
theorem decodeFrameBatch_wrongVs {p r1 : ObjRef} {asid : Asid} {args : List Data} {ex : List (Cap × CslotPtr)}
    {σ : State Unit} (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok r1, σ)}, False))
    (hne : r1 ≠ p) :
    ExceptT.run (decodeFrameBatch (Z := Unit) args (.pml4Cap p (some asid)) ex) σ =
      ({(.error (.invalidCapability 0), σ)}, False) := by
  unfold decodeFrameBatch
  rw [runE_bind_ok (runE_handle_ok hf), fbd_whenE_bind, if_pos hne]
  exact fbd_throw_bind _ _ _

/-- **The decode after the address-space check** is `fbDecP`. -/
theorem decodeFrameBatch_run {p : ObjRef} {asid : Asid} {args : List Data} {ex : List (Cap × CslotPtr)}
    {σ : State Unit} (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok p, σ)}, False)) :
    ExceptT.run (decodeFrameBatch (Z := Unit) args (.pml4Cap p (some asid)) ex) σ =
      ({(fbDecP p asid args ex, σ)}, False) := by
  unfold decodeFrameBatch fbDecP fbDecQ
  rw [runE_bind_ok (runE_handle_ok hf), fbd_whenE_bind, if_neg (show ¬ (p ≠ p) from fun h => h rfl),
    fbd_whenE_bind]
  by_cases h1 : args.length < 1
  · simp only [h1, ↓reduceIte]; exact fbd_throw_bind _ _ _
  simp only [h1, ↓reduceIte]
  cases hop : fbOpOf (dataToNat (the args[0]? &&& 0x3#64)) with
  | none => exact fbd_throw_bind _ _ _
  | some op =>
    try dsimp only
    by_cases h2 : (the args[0]? &&& ~~~fbDefined ≠ 0 ∨ dataToNat ((the args[0]? >>> 16) &&& 0x7f#64) = 0 ∨
        dataToNat ((the args[0]? >>> 16) &&& 0x7f#64) > 64)
    · simp only [h2, ↓reduceIte]; exact fbd_throw_bind _ _ _
    simp only [h2, ↓reduceIte, fbd_ret_bind, fbd_whenE_bind]
    by_cases h3 : args.length < 1 + op.words * dataToNat ((the args[0]? >>> 8) &&& 0xff#64)
    · simp only [h3, ↓reduceIte]; exact fbd_throw_bind _ _ _
    simp only [h3, ↓reduceIte, fbd_whenE_bind]
    by_cases h4 : ex.length < 1
    · simp only [h4, ↓reduceIte]; exact fbd_throw_bind _ _ _
    simp only [h4, ↓reduceIte, fbd_unlessE_bind]
    by_cases h5 : isCnodeCap (the ex[0]?).1 = true
    swap
    · simp only [h5, ↓reduceIte]; exact fbd_throw_bind _ _ _
    simp only [h5, ↓reduceIte, fbd_unlessE_bind]
    by_cases h6 : isCnodeCap (if op = .copyMap ∧ ex.length > 1 then (the ex[1]?).1 else (the ex[0]?).1) = true
    swap
    · simp only [h6, ↓reduceIte]; exact fbd_throw_bind _ _ _
    simp only [h6, ↓reduceIte]
    rfl

end

end Fl4Proofs.P3.Vs
