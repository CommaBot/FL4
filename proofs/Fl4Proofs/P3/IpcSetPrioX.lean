/-
P3 (DESIGN.md §9), TCB invocations: **the bound notification of a TCB**
(`bound_ntfn_of`), for the SetPriority/Bind/UnbindNotification leaves from
`JAtZ` (IpcTcbJ's `setPrioXLeafJ`, `bindXLeafJ`, `unbindXLeafJ`; the former
`XTop` leaves `setPrioXLeaf_of`, `bindXLeaf_of`, `unbindXLeaf_of` with their
"at every `IRel`" premises are retired).
-/
import Fl4Proofs.P3.IpcSetPrio
import Fl4Proofs.P3.IpcTcbBind
import Fl4Proofs.P3.XTopTcbSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- The bound notification of a TCB on `IRel` (l4v `valid_objs`: the object
exists, `ObjCover`: it is tracked): from the TCB's bound word. -/
theorem bound_ntfn_of {Z : XSets} {cr : Fl4Spec.Cr3} {s : S} {σ : Fl4Spec.State Unit}
    (hI : IRel st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ) (hSV : SchedValid σ) (hOC : ObjCover Z.N Z.T Z.E Z.R Z.C σ)
    {p : U64} (hp : p ∈ Z.T) (h0 : L.mem s (P1.boundA p) ≠ 0#u64) :
    ∃ x xn, σ.kheap p.bv = some (.tcb x) ∧ x.tcbBoundNotification = some (L.mem s (P1.boundA p)).bv ∧
      L.mem s (P1.boundA p) ∈ Z.N ∧ σ.kheap (L.mem s (P1.boundA p)).bv = some (.notification xn) := by
  obtain ⟨x, hk, hx⟩ := hI.1.tcb p hp
  have hb : x.tcbBoundNotification = some (L.mem s (P1.boundA p)).bv := by
    rw [hx.bound, show tBoundA p = P1.boundA p from rfl]; exact Notif.optRef_ne h0
  obtain ⟨xn, hkn⟩ := hSV.tcbNtfn _ _ _ hk hb
  obtain ⟨n', hn', e⟩ := hOC.ntfn _ xn hkn
  have : n' = L.mem s (P1.boundA p) := P1.eq_of_bv e
  subst this
  exact ⟨x, xn, hk, hb, hn', hkn⟩

end

end

end Fl4Proofs.P3
