/-
P1 (aarch64, gen 39): **I/O-port caps on AArch64** — the finaliser is trivial; the caps do not arise.

Source (crates/fl4-core):
* AArch64 has no I/O ports: `vcpu::revoke_ports` is a no-op (arch/aarch64/vcpu.rs:154, QueueFinIo's
  `vcpu.revoke_ports.same`), so `finalise_cap_object` of `IoPort` (objects.rs:311–317) writes nothing and returns
  `(Null, IoPort)` when final, `(Null, Null)` otherwise (`fin_ioport.same`, `fin_ioport.nonfin`).
* The cleanup of a final `IoPort` is not trivial: `post_cap_deletion` (objects.rs:408–414) runs `free_ioports`
  (ioport.rs:33–50, `set_mask` on the kernel's I/O-port bitmap `ks + IOPORT_BITMAP`, layout.rs:163). No `IoPort` cap
  exists on AArch64, however: an `IoPort` is only made by `IOPortControl_Issue` from an `IoPortControl` cap
  (ioport.rs:102) or derived from one (objects.rs:198), and the only `IoPortControl` is written by the **x86_64** boot
  (arch/x86_64/boot.rs:62); the AArch64 boot (arch/aarch64/boot.rs:23–62) writes the VSpace, page tables, CNode,
  `Domain` and `IrqControl` caps, no `IoPortControl`. So the Zombie loop needs no `IoPort` arm (its cleanups stay
  `ClOK`); a reachability invariant "no slot holds an `IoPort` / `IoPortControl` cap" is not stated here.

No named premise; new theorems only.
-/
import Fl4ProofsA64.P1.QueueFinIo
import Fl4ProofsA64.P1.QueueFinCap
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **An `IoPort` cap's finalisation on AArch64**: state and arch state unchanged, remainder `Null`, cleanup the
cap when final, `Null` otherwise. -/
theorem fin_ioport.same {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (first last owner : U64) (fin : Bool) :
    objects.finalise_cap st ar s a (.IoPort first last owner) fin false =
      ok ((.Null, if fin then .IoPort first last owner else .Null), s, a) := by
  rw [fin_cap_eq_obj (by simp)]
  simp only [objects.finalise_cap_object, vcpu.revoke_ports.same, bind_ok]
  cases fin <;> rfl

/-- **A non-final `IoPort` cap's finalisation** is `(Null, Null)` with no write. -/
theorem fin_ioport.nonfin {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (first last owner : U64) :
    objects.finalise_cap st ar s a (.IoPort first last owner) false false = ok ((.Null, .Null), s, a) := by
  rw [fin_ioport.same]; rfl

end

end Fl4ProofsA64.P1
