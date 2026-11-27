/-
P2 (line vlift, gen 6): **a write of a VCPU data word keeps P3's bundle `SlJAt`** (gen 5's `VFacts.wr` [J],
now a theorem).

Lead question (gen 5 decision 2): does P3's joint invariant read the memory of `other` heap objects? Only of the
ones it tracks: the typed heap's CNodes (their slots), the VSpace tables and ASID pools of its sets, the kernel-state
block / nodes / ASID-table area, the IPC-buffer words `Z.B`, and the RAM untyped caps' free parts (`UtCapP3.zero`:
zero). A VCPU is none of these once it is placed: so the proof follows slhuf's `SlJAt.userWr`, with
`JAtZ.frameWrJ` (σ kept) in place of `JAtZ.userWrB` (σ's user memory moved):

* `JAtZ.vcpuWrJ` (P3/VcpuWrJ.lean): a word of a spec VCPU object that is an `H` `.other 15` object off the
  kernel-global area, not an IPC-buffer word, written at `J`: `JAtZ` at the same ghosts and the same σ.
* **`slJAt_vcpuWr`**: `SlJAt K s → VData K b → Aligned b → SlJAt K (L.wr s b v)`. An IPC-buffer word (a `K.user`
  word) by `SlJAt.userWr`; otherwise by `JAtZ.vcpuWrJ` at the bundle's witnesses (layout, cores, scheduler action
  kept: σ is unchanged and `ksb` is kept by a write).

Premises (both [J], of the VT-x kind `VcpuHeap` already is; `P2/E2EVHeap.lean`):
* `VcpuSpec` [J]: at every bundle state, each VCPU of the layout is a spec `vcpu` object of the bundle's σ
  (`K.vcpus` = the spec's VCPU objects; P3 is native-scoped, `JExt.nat`, and relates no VCPU). It gives the
  "inside a spec object" fact (so the write meets no RAM untyped's free part, `SpecFree`) and separates the VCPU
  from the typed heap's CNodes and the sets' tables / pools (spec objects of other kinds at other addresses).
* `VcpuKsOff` [J]: each VCPU lies off the kernel-global area `[ksb, ksb + 304384)` (block, every node slot, ASID
  table). Strengthens `VcpuTabOff`'s second part; P3 has `JKern.hksIn` (block) and `hnd` (nodes of live cores) for
  `H`'s objects but nothing for the area of absent cores' nodes or the ASID table.
-/
import Fl4Proofs.P2.SlJHuf
import Fl4Proofs.P2.E2EVHeap
import Fl4Proofs.P3.VcpuWrJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`VcpuSpec`** [J] (module docstring): at every bundle state of `K.toKLayout`, each VCPU of the layout is a spec
`vcpu` object of the bundle's spec state. -/
def VcpuSpec (L : LawfulStore st) (K : KLayoutV) : Prop :=
  ∀ (s : S) (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Cx Ax : Set U64) (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
    SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout s a' σ →
    ∀ v ∈ K.vcpus, ∃ x, σ.kheap v.bv = some (.archObj (.vcpu x))

/-- **`VcpuKsOff`** [J] (module docstring): no VCPU meets the kernel-global area `[ksb, ksb + 304384)`. -/
def VcpuKsOff (K : KLayoutV) : Prop :=
  ∀ v ∈ K.vcpus, v.val + 32768 ≤ K.ksb.val ∨ K.ksb.val + 304384 ≤ v.val

/-- **A VCPU-data-word write keeps P3's bundle** (module docstring). -/
theorem slJAt_vcpuWr {K : KLayoutV} (hV : VcpuHeap K) (hS : VcpuSpec L K) (hO : VcpuKsOff K) {s : S}
    (h : SlJAt (L := L) K.toKLayout s) {b : U64} (hb : VData K b) (hba : Aligned b) (v : U64) :
    SlJAt (L := L) K.toKLayout (L.wr s b v) := by
  by_cases hB : b ∈ K.user
  · exact h.userWr hB v
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  have hnB : ∀ wp ∈ Zx.B, wp.1 ≠ b := fun wp hw e => hB (by
    show b ∈ K.toKLayout.user
    rw [B.user]; exact ⟨wp, hw, e⟩)
  obtain ⟨p, ⟨hp, g1, g2⟩, -⟩ := hb
  have hks : p.val + 32768 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ p.val := by
    rw [B.ksb]; exact hO p hp
  have J' := B.j.vcpuWrJ (hS s A' arI AR Zx Cx Ax Lst D a' σ B p hp) (hV p hp) hks hba g1 g2 hnB v
  exact ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ,
    { j := J'
      lay := by rw [L.ksb_wr]; exact B.lay
      cs := B.cs
      res := B.res }⟩

end

end

end Fl4Proofs.P2.E2EV
