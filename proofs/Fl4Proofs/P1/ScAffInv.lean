/-
P1: `ScAff` read off the IPC invariants (`XInv`, `BlkOK`): a thread with an SC
runs on its SC's core (`affA t` = the SC's `CORE` word), the fact P2's entry
paths use (`dco`, `rhc`, `uco`). `ScAff` is `ScExtra.aff` (P1/QueueObjs.lean),
kept by every kernel step; between the SC write of `bind_tcb`/`donate` (or
configure's `CORE` write) and `migrate_tcb` it holds off that thread
(`XInvW`, P1/QueueIpc.lean).
-/
import Fl4Proofs.P1.QueueBlock
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- `ScAff` at an `XInv` state. -/
theorem XInv.scAff {s : S} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) : ScAff st T s := hX.2.2.aff

/-- **A thread with an SC runs on its SC's core**, at an `XInv` state. -/
theorem XInv.core_eq {s : S} {t : U64} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (ht : t ∈ T)
    (h0 : L.mem s (scA t) ≠ 0#u64) : L.mem s (affA t) = L.mem s (scCoreA (L.mem s (scA t))) :=
  hX.2.2.aff.core_eq ht h0

/-- **A thread with an SC runs on its SC's core**, at a `BlkOK` state. -/
theorem BlkOK.core_eq {s : S} {t : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (h0 : L.mem s (scA t) ≠ 0#u64) : L.mem s (affA t) = L.mem s (scCoreA (L.mem s (scA t))) :=
  h.2.2.1.core_eq ht h0

end

end Fl4Proofs.P1
