/-
# The derived `PartialEq` on caps against `Cap::Vcpu` (line lvm, gen 3)

`cap_ne_vcpu`: `c != Cap::Vcpu(v)` (the derived `PartialEq`'s default `ne`) answering `false` means
`c = Cap::Vcpu(v)`. By cases over `c`'s constructors: Aeneas's `read_discriminant` instance for `Cap` maps each
constructor to its own constant, so every other constructor compares unequal on the discriminant, and the `Vcpu`
arm compares the one `U64` field. `localvm.handle_vcpu_invocation_local` makes this test, so
`vcpu_invocation_local_same` (`P1/LocalVmInvoke.lean`) no longer needs the "slot holds `Vcpu v`" half of its
premise `hL`.

No premises.
-/
import Fl4Proofs.P1.LocalVmDecNP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

theorem cap_ne_vcpu {c : capability.Cap} {v : U64}
    (h : core.cmp.PartialEq.ne.trait_default capability.Cap.Insts.CoreCmpPartialEqCap c
      (capability.Cap.Vcpu v) = ok false) : c = capability.Cap.Vcpu v := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default at h
  cases c <;>
    simp [capability.Cap.Insts.CoreCmpPartialEqCap, capability.Cap.Insts.CoreCmpPartialEqCap.eq,
      read_discriminant, capability.Cap.read_discriminant, lift, core.cmp.impls.PartialEqU64.eq] at h ⊢ <;>
    first | exact h | (try decide) | simp_all

end Fl4Proofs.P1
