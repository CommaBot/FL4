-- Hand-written models of the library functions fl4-core uses that Aeneas
-- does not provide (listed in FunsExternal_Template.lean, which Aeneas
-- regenerates). They are definitions, not axioms, and never fail, matching
-- Rust: these functions cannot panic.
module
public import Aeneas
public import Fl4Core.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
open fl4_core

/-- `bool != bool`. -/
@[rust_fun "core::cmp::impls::{core::cmp::PartialEq<bool, bool>}::ne"]
def Bool.Insts.CoreCmpPartialEqBool.ne (a b : Bool) : Result Bool :=
  ok (a != b)

/-- Number of trailing zero bits; the width for zero. -/
def bvTrailingZeros {w : Nat} (x : BitVec w) : Nat :=
  ((List.range w).find? (fun i => x.getLsbD i)).getD w

#guard bvTrailingZeros 0#64 = 64
#guard bvTrailingZeros 8#64 = 3
#guard bvTrailingZeros 1#64 = 0

@[rust_fun "core::num::{u64}::trailing_zeros"]
def core.num.U64.trailing_zeros (x : Std.U64) : Result Std.U32 :=
  ok ⟨ bvTrailingZeros x.bv ⟩

@[rust_fun "core::result::{core::result::Result<@T, @E>}::is_err"]
def core.result.Result.is_err {T : Type _} {E : Type _} :
    core.result.Result T E → Result Bool
  | .Ok _ => ok false
  | .Err _ => ok true

/-- `?` on an `Option` (#71's `localinv`): continue with the value, or
return the `None`. -/
@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type _} :
    Option T → Result (core.ops.control_flow.ControlFlow (Option Never) T)
  | some x => ok (.Continue x)
  | none => ok (.Break none)

/-- The `None` a `?` on an `Option` returns. -/
@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<!>>}::from_residual"]
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
    (T : Type _) : Option Never → Result (Option T)
  | _ => ok none

/-- `Result::ok`. -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::ok"]
def core.result.Result.ok {T : Type _} {E : Type _} :
    core.result.Result T E → Result (Option T)
  | .Ok x => Aeneas.Std.Result.ok (some x)
  | .Err _ => Aeneas.Std.Result.ok none
