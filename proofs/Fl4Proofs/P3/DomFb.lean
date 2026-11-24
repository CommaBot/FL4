/-
P3 (issue #16, fb3): **`X86PML4FrameBatch` keeps the domain schedule** (`DK`,
VsDom), so the arch invocations do (`dke_fl4ArchPerformInvocation`, for
VsDomF and AllDom). The batch's entries are CNode lookups, a copy
(`deriveCap`, `capInsert`), the map (`decodePageInvocation`,
`performPageInvocation`) and `capDelete`s (DomRecDel). The lookup and
derivation leaves moved here from AllDom (unchanged), which VsDomF cannot
import.
-/
import Fl4Proofs.P3.DomRecDel
import Fl4Proofs.P3.SpecInvFbD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open Fl4Spec Classical

noncomputable section

theorem dke_rab (p : Cap × CapRef) : DKE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact dke_liftE (dk_fail)
    · refine dke_bind (dke_whenE _ (dke_throw _)) fun _ => dke_bind (dke_whenE _ (dke_throw _)) fun _ =>
        dke_bind (dke_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact dke_returnOk _
      · refine dke_bind (dke_liftE (dk_getCap _)) fun nc => ?_
        split
        · exact dke_rab _
        · exact dke_returnOk _
  · exact dke_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_rab _)

theorem dke_resolveAddressBits (p : Cap × CapRef) : DKE (resolveAddressBits (Z := Unit) p) := dke_rab p
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_resolveAddressBits _)

theorem dke_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : DKE m) :
    DKE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible refine dke_lookupErrorOnFailure' _ ?_)

theorem dk_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : DKE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_lookupSlotForCnodeOp' _ _ _ _)

theorem dk_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : DKE (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact dk_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_lookupTargetSlot' _ _ _)

theorem dke_bind_returnOk' {ε α β : Type} {a : α} {f : α → NonDetE (State Unit) ε β} (h : DKE (f a)) :
    DKE (NonDetE.returnOk a >>= f) := by
  intro σ x hx
  rw [run_bind_ok (run_returnOk a σ)] at hx
  exact h σ x hx
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible refine dke_bind_returnOk' ?_)

theorem dk_ensureNoChildren' (cslotPtr : CslotPtr) : DKE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_ensureNoChildren' _)

theorem dke_archDeriveCap' (c : ArchCap) : DKE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_archDeriveCap' _)

theorem dke_deriveCap' (sl : CslotPtr) (c : Cap) : DKE (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_deriveCap' _ _)

theorem dk_lookupSourceSlot' (c : Cap) (r : CapRef) (n : Nat) : DKE (lookupSourceSlot (Z := Unit) c r n) := by
  unfold lookupSourceSlot; exact dk_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_lookupSourceSlot' _ _ _)

theorem dke_ensureEmpty' (sl : CslotPtr) : DKE (ensureEmpty (Z := Unit) sl) := by
  unfold ensureEmpty; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_ensureEmpty' _)

theorem dke_checkVpAlignment' (sz : VMPageSize) (v : Word) : DKE (checkVpAlignment (Z := Unit) sz v) := by
  unfold checkVpAlignment; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_checkVpAlignment' _ _)

theorem dke_createMappingEntries' (base : Paddr) (vptr : VSpaceRef) (sz : VMPageSize) (r : VMRights)
    (at' : VMAttributes) (p : ObjRef) : DKE (createMappingEntries (Z := Unit) base vptr sz r at' p) := by
  cases sz <;> unfold createMappingEntries <;> dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_createMappingEntries' _ _ _ _ _ _)

theorem dke_ensureSafeMapping' (e : VMPageEntry × ObjRef) : DKE (ensureSafeMapping (Z := Unit) e) := by
  unfold ensureSafeMapping; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_ensureSafeMapping' _)

theorem dke_decodePageInvocation' (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) : DKE (decodePageInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageInvocation; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_decodePageInvocation' _ _ _ _ _)

theorem dke_fbMap (b : Fl4FrameBatchInvocation) (sl : CslotPtr) (v : Data) : DKE (fbMap (Z := Unit) b sl v) := by
  unfold fbMap; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_fbMap _ _ _)

theorem dk_unmapPageUnflushed (sz : VMPageSize) (vs : ObjRef) (v : VSpaceRef) (p : ObjRef) :
    DK (unmapPageUnflushed (Z := Unit) sz vs v p) := by
  unfold unmapPageUnflushed; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_unmapPageUnflushed _ _ _ _)

theorem dke_fbCode {α : Type} {m : SEMonad Unit α} (h : DKE m) : DKE (fbCode (Z := Unit) m) := by
  unfold fbCode; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible refine dke_fbCode ?_)

theorem dke_fbDelete (sl : CslotPtr) : DKE (fbDelete (Z := Unit) sl) := by
  unfold fbDelete; exact dke_handleE (dk_capDelete sl) fun _ => dke_throw _
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_fbDelete _)

/-- One batch entry. -/
theorem dk_fbEntry (b : Fl4FrameBatchInvocation) (w : Data × Data × Data) : DKE (fbEntry (Z := Unit) b w) := by
  unfold fbEntry; dk_auto

/-- The batch. -/
theorem dk_performFrameBatch (b : Fl4FrameBatchInvocation) : DK (performFrameBatch (Z := Unit) b) :=
  fk_performFrameBatch (fun w => dk_fbEntry b w) (dk_flushAll _ _)

/-- **The arch invocations keep the domain schedule.** -/
theorem dke_fl4ArchPerformInvocation (i : Fl4ArchInvocation) : DKE (fl4ArchPerformInvocation (Z := Unit) i) := by
  cases i with
  | frameBatch b => unfold fl4ArchPerformInvocation; exact dke_liftE (dk_performFrameBatch b)
  | _ => exact dke_fl4ArchPerformInvocation0 _ (fun _ h => nomatch h)
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_fl4ArchPerformInvocation _)

end

end Fl4Proofs.P3.Vs
