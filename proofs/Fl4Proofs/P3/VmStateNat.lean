/-
P3 (line mmuAD, gen 42a2): **the native embedding `JAtZ → VmState` at `V = ∅`** (architect 08:29Z: "Add trivial
embedding `JAtZ → VmState` (V = ∅)").

* **`JAtZ.noIoTcb`**: `NoIoTcb` at a native state — `JAtZ.ext.nat` makes every slot cap `NativeCap`, and a native
  IO-port cap has owner 0 (P3/VsFoot `NativeCap`).
* **`JAtZ.toVmState`**: `JAtZ` ⇒ `VmState ∅` (no `X` since 42b1; `JExtEpt ∅` is `JExtEpt.of_jext`) (`JAtZV3.of_native`, then gen 42a's bridge `JAtZV3.toVm`). Its
  hypotheses are exactly what the native invariant does not carry about the VM extension, as at the existing native
  lifts (`JAtZ.toV`, `JAtZV3.of_native`): `NativeScope σ` (no spec thread `runningVM`, the [S] of P3/JAtZV, giving
  `RunVmB` by `JAtZ.rvm_of_ns`), the empty VCPU list (`h0` / `hd`, `JAtZ.toV`'s [J]), `VOnly ∅ σ` (no spec VCPU
  object, `JAtZV3.of_native`'s hypothesis) and `RngOne` (virt gen 28, `rngOne_empty` at boot, kept by every
  `MdbStep`). `VRel ∅`, `JVm ∅`, `VBind ∅` are trivial; `JExtVcpu ∅` and `NoIoTcb` follow from `JExt`.

No named premise (the hypotheses are the existing native-lift ones). No existing statement changed.
-/
import Fl4Proofs.P3.VmState
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **`NoIoTcb` at a native state** (module docstring). -/
theorem JAtZ.noIoTcb (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : NoIoTcb Z.th (L.mem s) := by
  intro y hy f l o hc
  have h := J.ext.nat y (isSlot_thTcb hy)
  rw [hc] at h
  exact h

/-- **The native embedding into `VmState ∅`** (module docstring). -/
theorem JAtZ.toVmState (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hN : Endp.NativeScope σ)
    (h0 : L.mem s (P1.vHeadA st s) = 0#u64)
    (hd : P1.Aligned (P1.vHeadA st s) ∧ ¬ JW ∅ Z.th (P1.vHeadA st s) ∧ ¬ SW Z.th (P1.vHeadA st s))
    (hO : VOnly ∅ σ) (hR : VirtRngOne.RngOne (L.mem s) Z.G) :
    VmState (L := L) arI ∅ AR Z H Cs Ac Lst D s a σ :=
  (JAtZV3.of_native J (J.rvm_of_ns hN) (VList.empty h0 hd) hO).toVm J.noIoTcb hR

end

end

end Fl4Proofs.P3
