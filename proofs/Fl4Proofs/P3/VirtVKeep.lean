/-
P3x for virtualization (line virt, gen 20, item 3, first module): **native steps keep the VCPU relation** — the
memory-effect form of "native kernel entries do not write VCPU memory", for the V-side top on `NoRunVM` states with
VCPUs (VCPUs present, none running).

The relation over a VCPU set `V` is `VRelAll V mem σ` (`VRelAt` at every `v ∈ V`). A step keeps it when its FL4
footprint `W` misses every VCPU object of `V` (`OffV V`, for aligned words) and its spec side keeps `vcpuAt` at
every `v ∈ V`. This module proves that frame and discharges `OffV` / the spec side for the footprints native steps
have:

* `agreeA_of_off`: a `WritesIn … W` with `W`'s aligned words off the object at `v` keeps its aligned words
  (`AgreeAtA`); `vrelAt_frame`, **`VRelAll.of_writes`** (the frame for the whole set).
* `OffV` from the placement records (state facts): **`offV_obj`** (a word inside an object of the typed heap, by
  `JVLay.vap`), `offV_slot` (inside a slot), **`offV_tcb`** (a TCB word `t + K`, `K < 4096`: registers, state,
  message info, the `VCPU` word), **`offV_U`** (a word of `JVLay`'s user set `U`: IPC buffers, frames),
  **`offV_ks`** (a kernel-global word in `[ksb, ksb + 304384)`, by `JVm.ks`), `OffV.mono` / unions (`offV_or`).
* Spec side: **`vcpuAt_updK`** (an in-place update of a non-VCPU object keeps every `vcpuAt` on `V`, by
  `JVm.ne_of`), `vcpuAt_ofKheap` (same heap); **`VRelAll.updK`** / **`VRelAll.ofKheap`**: the two spec step
  shapes of `JVm.updK` / `JVm.ofKheap` (every IPC / scheduler / CSpace object write; machine / scheduler-state
  steps) together with an `OffV` FL4 footprint keep `VRelAll`.

What remains for "every native kernel entry keeps `VRelAll`" (gen 20 handoff): each native step's proved FL4
footprint (`WFrame`, `WFr`, `WritesIn`, `FootEq` of the existing P3 steps) shown inside `obj ∪ U ∪ ks`, and its
spec step one of the `JVm` step shapes — a per-step bridge over the existing frames, no new premise expected.

No premise (no [J]/[P]/[W]): every hypothesis is a state / footprint fact. New file only; no existing statement
changed.
-/
import Fl4Proofs.P3.VirtDispVcpu
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtVKeep
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit
open Fl4Proofs.P3.VirtReplyKeep Fl4Proofs.P3.VirtDispVcpu

noncomputable section

/-- An aligned-word footprint condition: `b` is off every VCPU object of `V`. -/
def OffV (V : Set U64) (b : U64) : Prop := ∀ v ∈ V, b.val + 8 ≤ v.val ∨ v.val + 32768 ≤ b.val

/-- **The VCPU relation over a VCPU set.** -/
def VRelAll {Z : Type} (V : Set U64) (mem : Word → Word) (σ : State Z) : Prop := ∀ v ∈ V, VRelAt mem σ v.bv

theorem OffV.mono {V V' : Set U64} (h : V' ⊆ V) {b : U64} (hb : OffV V b) : OffV V' b := fun v hv => hb v (h hv)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- A write set whose aligned words are off the object at `v` keeps its aligned words. -/
theorem agreeA_of_off {v : U64} (hv : VFits v) {s s' : S} {W : U64 → Prop} (h : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → P1.Aligned b → b.val + 8 ≤ v.val ∨ v.val + 32768 ≤ b.val) :
    AgreeAtA (memW st s) (memW st s') v.bv := by
  intro o h1 h8
  have ho : o.toNat < 32768 := by
    have : VcpuLay.SIZE.toNat = 32768 := rfl
    rw [BitVec.lt_def, this] at h1; exact h1
  have e := vo_val hv ho
  have hal : P1.Aligned (⟨v.bv + o⟩ : U64) := by
    unfold P1.Aligned; rw [e]; have := hv.1; omega
  unfold memW
  refine congrArg UScalar.bv (h.2.2 _ hal fun hb => ?_)
  rcases hW _ hb hal with c | c <;> rw [e] at c <;> omega

theorem vrelAt_frame {Z : Type} {mem mem' : Word → Word} {σ σ' : State Z} {v : Word} (hm : AgreeAtA mem mem' v)
    (hs : vcpuAt σ' v = vcpuAt σ v) (h : VRelAt mem σ v) : VRelAt mem' σ' v := by
  obtain ⟨vs, hvs, h1, h2⟩ := h
  exact ⟨vs, by rw [hs]; exact hvs, fun e => VcpuRelSvm.congrA hm (h1 e), fun e => VcpuRelVmx.congrA hm (h2 e)⟩

/-- **The frame for the whole VCPU set** (module docstring). -/
theorem VRelAll.of_writes {Z : Type} {V : Set U64} (hf : ∀ v ∈ V, VFits v) {s s' : S} {σ σ' : State Z}
    (h : VRelAll V (memW st s) σ) {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → P1.Aligned b → OffV V b) (hs : ∀ v ∈ V, vcpuAt σ' v.bv = vcpuAt σ v.bv) :
    VRelAll V (memW st s') σ' := fun v hv =>
  vrelAt_frame (agreeA_of_off (hf v hv) hw fun b hb ha => hW b hb ha v hv) (hs v hv) (h v hv)

end

/-! ## `OffV` from the placement records -/

section
variable {V : Set U64} {th : TypedHeap} {U : Set U64}

/-- A word inside an object of the typed heap is off `V`'s VCPUs. -/
theorem offV_obj (Ly : JVLay V th U) {p : U64} {k : ObjKind} (hp : th p = some k) {b : U64}
    (h1 : p.val ≤ b.val) (h2 : b.val + 8 ≤ p.val + objSize k) : OffV V b := fun v hv => by
  rcases Ly.vap v hv p k hp with c | c <;> omega

/-- A word inside a slot is off `V`'s VCPUs. -/
theorem offV_slot (Ly : JVLay V th U) {y : U64} (hy : IsSlot th y) {b : U64} (h1 : y.val ≤ b.val)
    (h2 : b.val + 8 ≤ y.val + 32) : OffV V b := by
  obtain ⟨p, k, hk, hp1, hp2, -, -⟩ := lay_slot_in Ly.pl hy
  exact offV_obj Ly hk (by omega) (by omega)

/-- A TCB word `t + K` (`K < 4096`, `K + 8 ≤ 4096`) is off `V`'s VCPUs. -/
theorem offV_tcb (Ly : JVLay V th U) {t : U64} (ht : th t = some .tcb) {K : U64} (hK : K.val + 8 ≤ 4096) :
    OffV V (core.num.U64.wrapping_add t K) := by
  have hf := Ly.pl.fits t _ ht
  have e4 : objSize ObjKind.tcb = 4096 := rfl
  rw [e4] at hf
  have e : (core.num.U64.wrapping_add t K).val = t.val + K.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  exact offV_obj Ly ht (by rw [e]; omega) (by rw [e, e4]; omega)

/-- A word of the user set `U` is off `V`'s VCPUs. -/
theorem offV_U (Ly : JVLay V th U) {b : U64} (hb : b ∈ U) : OffV V b := fun v hv => by
  have ha : b.val % 8 = 0 := Ly.ua b hb
  have hv1 := (Ly.vfit v hv).1
  rcases Ly.uv b hb v hv with c | c
  · left; omega
  · right; exact c

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {V : Set U64} {H : P1.Heap} {s : S} {σ : State Unit}

/-- A kernel-global word (inside `[ksb, ksb + 304384)`) is off `V`'s VCPUs. -/
theorem offV_ks (J : JVm (L := L) V H s σ) {b : U64} (h1 : (L.ksb s).val ≤ b.val)
    (h2 : b.val + 8 ≤ (L.ksb s).val + 304384) : OffV V b := fun v hv => by
  rcases J.ks v hv with c | c <;> omega

theorem offV_or {P Q : U64 → Prop} (hP : ∀ b, P b → OffV V b) (hQ : ∀ b, Q b → OffV V b) :
    ∀ b, P b ∨ Q b → OffV V b := fun b h => h.elim (hP b) (hQ b)

/-! ## The spec side -/

/-- **An in-place update of a non-VCPU object keeps every `vcpuAt` on `V`.** -/
theorem vcpuAt_updK (J : JVm (L := L) V H s σ) {p : ObjRef} {ko ko' : KernelObject} (hp : σ.kheap p = some ko)
    (hnv : ∀ x, ko ≠ .archObj (.vcpu x)) : ∀ v ∈ V, vcpuAt (Notif.updK σ p ko') v.bv = vcpuAt σ v.bv := by
  intro v hv
  have hne := J.ne_of hp hnv v hv
  unfold vcpuAt
  rw [Notif.updK_kheap, Function.update_of_ne (Ne.symm hne)]

theorem vcpuAt_ofKheap {Z : Type} {σ1 σ2 : State Z} (he : σ2.kheap = σ1.kheap) (v : ObjRef) :
    vcpuAt σ2 v = vcpuAt σ1 v := by
  unfold vcpuAt; rw [he]

/-- **`VRelAll` across an in-place non-VCPU object update with an `OffV` FL4 footprint.** -/
theorem VRelAll.updK (J : JVm (L := L) V H s σ) (hf : ∀ v ∈ V, VFits v) {s' : S}
    (h : VRelAll V (memW st s) σ) {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → P1.Aligned b → OffV V b) {p : ObjRef} {ko ko' : KernelObject} (hp : σ.kheap p = some ko)
    (hnv : ∀ x, ko ≠ .archObj (.vcpu x)) : VRelAll V (memW st s') (Notif.updK σ p ko') :=
  VRelAll.of_writes hf h hw hW (vcpuAt_updK J hp hnv)

/-- **`VRelAll` across a step keeping the spec heap with an `OffV` FL4 footprint.** -/
theorem VRelAll.ofKheap {Z : Type} (hf : ∀ v ∈ V, VFits v) {s' : S} {σ1 σ2 : State Z}
    (h : VRelAll V (memW st s) σ1) {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → P1.Aligned b → OffV V b) (he : σ2.kheap = σ1.kheap) : VRelAll V (memW st s') σ2 :=
  VRelAll.of_writes hf h hw hW fun v _ => vcpuAt_ofKheap he v.bv

end

end
end Fl4Proofs.P3.VirtVKeep
