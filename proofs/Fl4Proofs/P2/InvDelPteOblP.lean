/-
# P2 (line invj, generation 7): the ownership obligations of the Delete PTE-arm path under rule 8

For the read / write sets `InvRSP` / `InvWSP` and the decline set `IoDS` at the entry states `PreP`
(P2/InvDelPteAccP.lean), at a layout with `RegionOKP`, `UserOKP` and no VCPU:

* **`invRSP_read_own`** (`PathObl.read_own` for `ownP`: `ioRSP_rperm`), **`invWSP_write_own`** (`write_own`: the
  `IoWS` words and the locked leaves by `ioWSP_wperm`, the decline set's three words are `IoWS` words),
  **`invWSP_aligned`** (`aligned`);
* **`Alt.anti`**: an alternative for a read set is one for every smaller read set (so the alternatives of
  `InvRSP s` are alternatives of `IoRSR s ⊆ IoRSP s ⊆ InvRSP s`: the declining-side obligations can be stated for
  `IoRSR`).

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvDelPteAccP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section anti
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`Alt` is antitone in the read set.** -/
theorem Alt.anti {R R' : U64 → Prop} {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64}
    {User : U64 → Prop} {s s' : S} (h : ∀ x, R' x → R x) (A : Alt st R cls ko User s s') :
    Alt st R' cls ko User s s' := by
  refine ⟨A.cpu, A.ksb, A.masks, fun x hx => A.read x (h x hx), fun x hx hu hk => ?_⟩
  by_cases hR : R x
  · rw [A.read x hR]
  · exact A.clsEq x hR hu hk

end anti

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV

section obl
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}

/-- **`read_own` of the PTE-arm path under rule 8.** -/
theorem invRSP_read_own (nv : K.vcpus = ∅) :
    ∀ s x, PreP st Cs Ω Sg Ac Locks p K m s → InvRSP st K Locks s x → ¬ x ∈ K.user →
      PathObl.RPerm (ownP K) (L.cpu s) (Locks s) (L.mem s) x :=
  fun _ _ _ hr hu => ioRSP_rperm nv (hr.2.resolve_left hu)

/-- **`write_own` of the PTE-arm path under rule 8** (the decline set's words are `IoWS` words). -/
theorem invWSP_write_own (hK : RegionOKP K) (nv : K.vcpus = ∅) :
    ∀ s x, PreP st Cs Ω Sg Ac Locks p K m s → (InvWSP st K Locks s x ∨ IoDS (st := st) s x) → ¬ x ∈ K.user →
      PathObl.WPerm (ownP K) (L.cpu s) (Locks s) (L.mem s) x := by
  intro s x hE hx hu
  refine ioWSP_wperm hK nv ?_
  rcases hx with hx | hx
  · exact hx.2.resolve_left hu
  · have PE := hE.2.1.1.1.1
    refine Or.inl ?_
    rcases hx with rfl | rfl | rfl
    · exact (PE.reg (Locks := Locks) (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])).2
    · exact (PE.nd (Locks := Locks) layout.node.CUR_TIME (by simp [layout.node.CUR_TIME])
        (by simp [layout.node.CUR_TIME])).2
    · exact (PE.nd (Locks := Locks) layout.node.CONSUMED (by simp [layout.node.CONSUMED])
        (by simp [layout.node.CONSUMED])).2

/-- **`aligned` of the PTE-arm path.** -/
theorem invWSP_aligned :
    ∀ s x, PreP st Cs Ω Sg Ac Locks p K m s → (InvWSP st K Locks s x ∨ IoDS (st := st) s x) → Aligned x := by
  intro s x hE hx
  rcases hx with hx | hx
  · exact hx.1
  · exact (IoDS.safe hE.2.1.1.1.1 hx).1

end obl

end Fl4Proofs.P2.E2EP
