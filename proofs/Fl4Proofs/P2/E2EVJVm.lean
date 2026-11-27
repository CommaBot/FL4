/-
P2 (line vlift, gen 7): **the VM-domain layout [J]s from one P3-side fact, `JVm`** (P3/JVm.lean).

**`JVmL L K`** [J]: at every bundle of `K.toKLayout` (`SlJAtZ` witnesses), `JVm K.vcpus K.heap s σ`: each VCPU of
the layout is a spec VCPU object of that σ, the heap object `.other 15`, off `[ksb, ksb + 304384)`, and apart from
every other spec object. It is the layout half of "`K.vcpus` = the spec's VCPU objects"; it would be a field of
`JAtZ` if P3 covered VT-x states. From it (each at a bundle `B` with `J := JVmL … B`):

| [J] (gen) | derived by | P3 facts used besides `JVm` |
|---|---|---|
| `VcpuHeap` (2) | `vcpuHeap_of_jvm` | — (`JVm.heap`) |
| `VcpuSpec` (6) | `vcpuSpec_of_jvm` | — (`JVm.spec`) |
| `VcpuKsOff` (6) | `vcpuKsOff_of_jvm` | `SlJAtZ.ksb` |
| `VcpuTabOff` (2) | `vcpuTabOff_of_jvm` | `VsPlaced.ksb_fit` (the fit half: no `JVm` needed) |
| `PoolObj` (2) | `poolObj_of_jvm` | `VsRel.tmem` / `VsRel.pool`, `SpecCover.arch` (`SlJAtZ.pool`'s route); "not a VCPU": spec pool ≠ spec VCPU |
| `UserObj` (2) | `userObj_of_jvm` | `SlJAtZ.user`, `JCarry.bufPg` (user words in spec data pages); `JVm.sep` |
| lvm `hvK` / `vin` | `vOf_zero`, `vin_of_bound`, `hvK_vtimer` | `JExt.vw`, `JKern.curT`: at a bundle the current thread's VCPU word is 0 |

so **`VFacts.ofJVm`**: `JVmL` and one bundle state give the whole `VFacts` record (all six fields).
`jvmL_empty`: with no VCPU in the layout `JVmL` holds outright.

`UserObj` is restated (gen 7, `P2/E2EVHeap.lean`) as what its one consumer `user_noVcpu` uses: no user word lies in
a VCPU of the layout (gen 2's form asked a heap object of the exact P1 size around each user word; P3 bounds the
`other` size of a large page only from above, `ArchFitHyp`).

On lvm's `vin` (`VexitEnt.vin : v ≠ 0 → InVcpu K v (v + PENDING)`): at a P3 bundle no TCB is bound to a VCPU
(`JExt.vw`, `JAtZ.curVcpu0`), so the bound VCPU `vOf st s` is 0 and `vtimer`'s `vin` (stated at `vOf st s`) holds
vacuously (`hvK_vtimer`); for `local_vm_exit` (`v` an argument that the body checks against `vcpu.bound`) the same
holds when the glue picks `v := vOf st s` (`vin_of_bound`). The VM paths thus never accept at a P3 state: their
non-vacuous use needs P3 over VT-x states (separate project), and there `JVm` is the placement half.
-/
import Fl4Proofs.P2.E2EVFl4U
import Fl4Proofs.P2.AccessLvmTo
import Fl4Proofs.P3.JVm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P3 (JVm VcpuApart)

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutV}
variable {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop} {Zx : Fl4Proofs.P3.XSets}
  {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'} {σ : Fl4Spec.State Unit} {s : S}

/-- **`JVmL`** [J] (module docstring): every bundle of the layout carries `JVm` at the layout's VCPUs. -/
def JVmL (L : LawfulStore st) (K : KLayoutV) : Prop :=
  ∀ (s : S) (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Cx Ax : Set U64) (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
    SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout s a' σ → JVm (L := L) K.vcpus K.heap s σ

theorem jvmL_empty (h : K.vcpus = ∅) : JVmL L K := by
  intro s _ _ _ _ _ _ _ _ _ _ _
  rw [h]; exact JVm.empty

theorem vcpuSpec_of_jvm (hJ : JVmL L K) : VcpuSpec L K :=
  fun s A' arI AR Zx Cx Ax Lst D a' σ B v hv => (hJ s A' arI AR Zx Cx Ax Lst D a' σ B).spec v hv

theorem vcpuHeap_of_jvm (J : JVm (L := L) K.vcpus K.heap s σ) : VcpuHeap K := J.heap

theorem vcpuKsOff_of_jvm (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout s a' σ)
    (J : JVm (L := L) K.vcpus K.heap s σ) : VcpuKsOff K := fun v hv => by
  have h := J.ks v hv
  rw [B.ksb] at h
  exact h

theorem vcpuTabOff_of_jvm (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout s a' σ)
    (J : JVm (L := L) K.vcpus K.heap s σ) : VcpuTabOff K := by
  have hf := B.j.xtop.fin.1.2.vs.ksb_fit
  have hk := B.ksb
  have hO := vcpuKsOff_of_jvm B J
  refine ⟨?_, fun v hv => ?_⟩
  · have e3 : (L.ksb s).val = K.ksb.val := by rw [hk]
    omega
  · rcases hO v hv with h | h
    · left; omega
    · right; exact h

/-- **`PoolObj` at a bundle** (`SlJAtZ.pool`'s route; not a VCPU since a spec ASID pool). -/
theorem poolObj_of_jvm (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout s a' σ)
    (J : JVm (L := L) K.vcpus K.heap s σ) : PoolObj (L := L) K s := by
  intro hi hhi h0
  have e : atAF (L.ksb s) hi = Fl4Proofs.P3.Vs.atA (L.ksb s) hi := rfl
  rw [e] at h0 ⊢
  have hP := B.j.xtop.fin.2.1.tmem hi hhi h0
  generalize L.mem s (Fl4Proofs.P3.Vs.atA (L.ksb s) hi) = p at hP h0 ⊢
  obtain ⟨f, hf, -⟩ := B.j.xtop.fin.2.1.pool p hP
  obtain ⟨n, hn12, hH⟩ := B.j.cover.arch _ _ hf
  refine ⟨n, hn12, hH, fun hv => ?_⟩
  obtain ⟨x, hx⟩ := J.spec p hv
  rw [hf] at hx
  cases hx

/-- **`UserObj` at a bundle**: a user word lies in a spec data page (`JCarry.bufPg`), which `JVm.sep` keeps off
every VCPU of the layout. -/
theorem userObj_of_jvm (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout s a' σ)
    (J : JVm (L := L) K.vcpus K.heap s σ) : UserObj K := by
  rintro b hb ⟨v, hv, h1, h2⟩
  have hb' : b ∈ K.toKLayout.user := hb
  rw [B.user] at hb'
  obtain ⟨wp, hw, rfl⟩ := hb'
  obtain ⟨q, vms, hq, g1, g2⟩ := B.j.carry.bufPg wp hw
  have hne : q ≠ v.bv := fun e => by
    obtain ⟨x, hx⟩ := J.spec v hv
    rw [← e, hq] at hx
    cases hx
  have hs := J.sep v hv q _ hq hne
  unfold VcpuApart at hs
  have e : Fl4Spec.objBits (.archObj (.dataPage false vms)) = Fl4Spec.pageBitsForSize vms := rfl
  rw [e] at hs
  omega

/-- **The whole `VFacts` record from `JVmL`** and one bundle state of the layout. -/
theorem VFacts.ofJVm (hJ : JVmL L K) {s0 : S} (h0 : SlJAt (L := L) K.toKLayout s0) : VFacts L K := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h0
  have J := hJ s0 A' arI AR Zx Cx Ax Lst D a' σ B
  exact
    { heap := vcpuHeap_of_jvm J
      tab := vcpuTabOff_of_jvm B J
      user := userObj_of_jvm B J
      pool := fun s h => by
        obtain ⟨A2, arI2, AR2, Zx2, Cx2, Ax2, Lst2, D2, a2, σ2, B2⟩ := h
        exact poolObj_of_jvm B2 (hJ s A2 arI2 AR2 Zx2 Cx2 Ax2 Lst2 D2 a2 σ2 B2)
      spec := vcpuSpec_of_jvm hJ
      ks := vcpuKsOff_of_jvm B J }

/-! ## lvm's `vin` / `hvK` at P3 states -/

/-- At a P3 bundle the current thread's bound VCPU is 0 (`JExt.vw`). -/
theorem vOf_zero {K : OwnMap.KLayout} (h : SlJAt (L := L) K s) : vOf st s = 0#u64 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := h
  exact B.j.curVcpu0

/-- **lvm's `hvK` for `local_vm_timer_irq`** (stated at the bound VCPU `vOf st s`): vacuous at a bundle. -/
theorem hvK_vtimer (h : SlJAt (L := L) K.toKLayout s) : vOf st s ≠ 0#u64 → vOf st s ∈ K.vcpus :=
  fun h0 => absurd (vOf_zero h) h0

/-- **lvm's `vin` for `local_vm_exit`** when the glue's `v` is the current thread's bound VCPU. -/
theorem vin_of_bound (h : SlJAt (L := L) K.toKLayout s) {v : U64} (hv : v = vOf st s) :
    v ≠ 0#u64 → InVcpu K v (core.num.U64.wrapping_add v vcpu.PENDING) :=
  fun h0 => absurd (hv.trans (vOf_zero h)) h0

end

end

end Fl4Proofs.P2.E2EV
