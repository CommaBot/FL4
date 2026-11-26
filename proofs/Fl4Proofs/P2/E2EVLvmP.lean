/-
P2 (line vlift, gen 4): **lvm gen 7's `VexitPEnt.vfit` / `pusr` from the heap** (`handoff/lvm.md` §16; the fields
live in `P2/AccessLvmPo.lean` on `par/lvm4`, not yet on `int/j13`, so these are standalone lemmas with the fields'
statement shapes):

* **`vfit_of`**: `v ≠ 0 → v.val + 32768 ≤ 2^64` (`VexitPEnt.vfit`) for a VCPU of the layout: `VcpuHeap` [J] makes it
  a heap `.other 15` object and P1's `HeapOK.fits` keeps it below `2^64`.
* **`pusr_of`**: `v ≠ 0 → UsrW … (v + PENDING)` (`VexitPEnt.pusr`) at P1's sets convention (`T = H.tcbs`,
  `Ω = H.omega`, `Sg = H.frame`, the SCs typed), from `BXI`, `HeapOK H`, `H`'s `other` objects placed against the
  kernel-state block (P3 `JKern.hksIn`, as `vfar_pending`) and `H v = some (.other 15)`: P2's
  `Stall.usrW_vcpu` (`P2/EntryVcpu.lean`).
* Both from `v ∈ K.vcpus` with `K.heap = H`: `vfit_ofK`, `pusr_ofK`.

What remains of the two [J]s: `v ≠ 0 → v ∈ K.vcpus`, the exiting VCPU is one of the layout's (lvm's `vin` premise;
[J], P3 covers native threads only, `handoff/vlift.md` §9.3), and `VcpuHeap` [J].
-/
import Fl4Proofs.P2.E2EVHeap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayoutV}

/-- A heap `.other 15` object does not wrap. -/
theorem vfit_heap (hH : HeapOK H) {v : U64} (hv : H v = some (.other 15)) : v.val + 32768 ≤ 2 ^ 64 := by
  have hf := hH.fits v _ hv
  have e15 : (HKind.other 15).bits = 15 := rfl
  rw [e15, two15] at hf
  exact hf

/-- **lvm's `vfit`** (`VexitPEnt.vfit`) for a VCPU of the layout. -/
theorem vfit_of (hH : HeapOK K.heap) (hV : VcpuHeap K) {v : U64} (hvK : v ≠ 0#u64 → v ∈ K.vcpus) :
    v ≠ 0#u64 → v.val + 32768 ≤ 2 ^ 64 :=
  fun h0 => vfit_heap hH (hV v (hvK h0))

/-- **lvm's `pusr`** (`VexitPEnt.pusr`) at P1's sets convention, for a heap `.other 15` object. -/
theorem pusr_of (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hT : T = H.tcbs) (hΩ : Ω = H.omega)
    (hSg : Sg = H.frame) (hH : HeapOK H) (hScs : ∀ c ∈ Scs, H c = some (.sc (Z c)))
    (hKI : ∀ p z, H p = some (.other z) → p.val + 2 ^ z ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val ∨
      ((L.ksb s).val ≤ p.val ∧ p.val + 2 ^ z ≤ (L.ksb s).val + 13568))
    {v : U64} (hv : v ≠ 0#u64 → H v = some (.other 15)) :
    v ≠ 0#u64 → UsrW st T Cs H Sg Scs Z s (core.num.U64.wrapping_add v vcpu.PENDING) := by
  intro h0
  subst hT hΩ hSg
  obtain ⟨⟨Q, R, hq⟩, -⟩ := hI
  exact Stall.usrW_vcpu hH hScs hKI hq (hv h0)

/-- `pusr_of` for a VCPU of the layout (`VcpuHeap` [J], `K.heap = H`). -/
theorem pusr_ofK (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hT : T = H.tcbs) (hΩ : Ω = H.omega)
    (hSg : Sg = H.frame) (hH : HeapOK H) (hScs : ∀ c ∈ Scs, H c = some (.sc (Z c)))
    (hKI : ∀ p z, H p = some (.other z) → p.val + 2 ^ z ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val ∨
      ((L.ksb s).val ≤ p.val ∧ p.val + 2 ^ z ≤ (L.ksb s).val + 13568))
    (hKH : K.heap = H) (hV : VcpuHeap K) {v : U64} (hvK : v ≠ 0#u64 → v ∈ K.vcpus) :
    v ≠ 0#u64 → UsrW st T Cs H Sg Scs Z s (core.num.U64.wrapping_add v vcpu.PENDING) :=
  pusr_of hI hT hΩ hSg hH hScs hKI fun h0 => hKH ▸ hV v (hvK h0)

/-- `vfit_of` at `K.heap = H`. -/
theorem vfit_ofK (hH : HeapOK H) (hKH : K.heap = H) (hV : VcpuHeap K) {v : U64}
    (hvK : v ≠ 0#u64 → v ∈ K.vcpus) : v ≠ 0#u64 → v.val + 32768 ≤ 2 ^ 64 :=
  vfit_of (hKH ▸ hH) hV hvK

end

end
end Fl4Proofs.P2.E2EV
