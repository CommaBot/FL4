/-
# P2 (AArch64): the VM-fault body's program premise (`IsProg`, `NoZero`)

The AArch64 counterpart of the first half of `Fl4Proofs/P2/ProgGenVmLP.lean`, over `Fl4CoreA64`:

* `vm_isProg`: AArch64's `syscall.handle_vm_fault_local` is the generated tree
  `R.syscall.handle_vm_fault_local addr code` (`P2/ProgGenVf*.lean`, from
  `xtask/scripts/gen_prog.py --arch aarch64 Vf syscall.handle_vm_fault_local`) on every store and Arch
  instance;
* `vm_noZero`: that tree has no `zero` / `clr` node.

So the `IsProg F p` [P] and `NoZero p` [W] parts of the program premise `hpz` of the VM-fault local path
hold on AArch64 for `p := R.syscall.handle_vm_fault_local addr code`. The tree differs from x86_64's where the
extractions differ (the AArch64 body's extra `vcpu::bound` decline in `fastpath_vm.vm_fault`, its
`set_vm_root` with the Stage-2 and high VSpace roots, the two-word `IPI_PENDING`). The local path
(`vm_localPath`) and its remaining premises are not ported yet (handoff/a64.md §7).

No premises.
-/
import Fl4ProofsA64.P2.ProgGenVfTop
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P2.PathObl
open fl4_core_a64

/-- The VM-fault body as a family over the Arch instance (`E2E.LocalPath.F` on x86_64). -/
abbrev vmBody (S : Type) (addr code : U64) : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A →
    Result (Bool × S × A) :=
  fun ar m s a => syscall.handle_vm_fault_local m ar s a addr code

/-- **`IsProg` for AArch64's VM-fault body**: it is the generated tree, on every store and Arch instance. -/
theorem vm_isProg (S : Type) (addr code : U64) :
    IsProg (vmBody S addr code) (R.syscall.handle_vm_fault_local addr code) := by
  intro A ar st
  funext s a
  rw [R.syscall.handle_vm_fault_local_eq st ar, bind_proj3]

/-- The tree has no `zero` / `clr` node. -/
theorem vm_noZero (addr code : U64) : NoZero (R.syscall.handle_vm_fault_local addr code) :=
  R.syscall.handle_vm_fault_local_nz addr code

/-- `hpz`'s first two parts on AArch64: some tree is the VM-fault body and has no zeroing node. -/
theorem vm_prog (S : Type) (addr code : U64) :
    ∃ p : SProg Bool, IsProg (vmBody S addr code) p ∧ NoZero p :=
  ⟨_, vm_isProg S addr code, vm_noZero addr code⟩

end Fl4ProofsA64.P2.PathObl
