/-
P3: **evidence that `JAtZ` forces a cap over the idle thread** (scratch).

`JAtZ.idle_covered`: at every `JAtZ` state, some physical, non-untyped cap
of the MDB covers the current core's idle TCB. The chain: the scheduler
relation puts the idle thread (the node's `IDLE_THREAD` word, `L.idleW`) in
`Z.T` (`SchedCore.idleT`), `zH` makes it a TCB of `H`, `JCovD.h` asks it to
be covered or dead, and `DeadP` excludes the idle thread. FL4's boot
(`create_idle_thread`) gives no cap to the idle thread, so no state reachable
from boot satisfies `JAtZ`.
-/
import Fl4Proofs.P3.JointAt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- `L.idleW` is the current core's `IDLE_THREAD` node word. -/
theorem idleW_eq_node {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) : L.idleW s = nodeW st s c layout.node.IDLE_THREAD := by
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  unfold P1.LawfulStore.idleW nodeW; rw [hc.cur]

/-- **`JAtZ` forces a cap covering the idle TCB** (module docstring). -/
theorem JAtZ.idle_covered {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    Covered (L.mem s) Z.G (L.idleW s).val ((L.idleW s).val + 2 ^ P1.HKind.bits .tcb) := by
  have hS : SchedRel st Z.N Z.T Z.C Z.c s σ := J.xtop.fin.1.1.1
  have hT : L.idleW s ∈ Z.T := by
    obtain ⟨Q, R, hc, -⟩ := hS.lists
    rw [idleW_eq_node hS]; exact hc.idleT
  have hH := J.zH.1 _ hT
  rcases J.jcov.h _ _ hH with hc | hd
  · exact hc
  · exact absurd rfl ((J.jcov.dead _ hd).1 hH).2.2.2.2

end

end Fl4Proofs.P3
