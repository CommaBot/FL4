/-
Specs for the derived `PartialEq` implementations of fl4-core's handle
types: `eq` returns whether the two values are equal. Callers' P0 proofs
need the boolean's meaning, e.g. to know that `!=` follows from `==`.
-/
import Fl4Core.Funs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P0
open fl4_core

@[step] theorem obj.Slot.Insts.CoreCmpPartialEqSlot.eq.spec (a b : obj.Slot) :
    obj.Slot.Insts.CoreCmpPartialEqSlot.eq a b ⦃ r => r = true ↔ a = b ⦄ := by
  simp [obj.Slot.Insts.CoreCmpPartialEqSlot.eq]

@[step] theorem obj.Tcb.Insts.CoreCmpPartialEqTcb.eq.spec (a b : obj.Tcb) :
    obj.Tcb.Insts.CoreCmpPartialEqTcb.eq a b ⦃ r => r = true ↔ a = b ⦄ := by
  simp [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq]

@[step] theorem obj.Sc.Insts.CoreCmpPartialEqSc.eq.spec (a b : obj.Sc) :
    obj.Sc.Insts.CoreCmpPartialEqSc.eq a b ⦃ r => r = true ↔ a = b ⦄ := by
  simp [obj.Sc.Insts.CoreCmpPartialEqSc.eq]

@[step] theorem obj.Ep.Insts.CoreCmpPartialEqEp.eq.spec (a b : obj.Ep) :
    obj.Ep.Insts.CoreCmpPartialEqEp.eq a b ⦃ r => r = true ↔ a = b ⦄ := by
  simp [obj.Ep.Insts.CoreCmpPartialEqEp.eq]

@[step] theorem obj.Ntfn.Insts.CoreCmpPartialEqNtfn.eq.spec (a b : obj.Ntfn) :
    obj.Ntfn.Insts.CoreCmpPartialEqNtfn.eq a b ⦃ r => r = true ↔ a = b ⦄ := by
  simp [obj.Ntfn.Insts.CoreCmpPartialEqNtfn.eq]

@[step] theorem obj.Reply.Insts.CoreCmpPartialEqReply.eq.spec (a b : obj.Reply) :
    obj.Reply.Insts.CoreCmpPartialEqReply.eq a b ⦃ r => r = true ↔ a = b ⦄ := by
  simp [obj.Reply.Insts.CoreCmpPartialEqReply.eq]

end Fl4Proofs.P0
