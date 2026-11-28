/-
P3 (line mmuAD, gen 42a): **the flat VM-epoch records `VcpuCore` and `VmState`** (architect contract mmuAD 42, item 2),
the bridge from `JAtZV3`, and the records' frame lemmas.

* **`VcpuCore V Z H s σ`** — one flat record of the VCPU facts, no nesting, no `X` (42b1 split): `extv : JExtVcpu`
  (the VCPU half of virt gen 26's `JExtV2`: `Vcpu` caps into `V`, `bnd` / `back` / `nz`; stale IO-port owners allowed), `vo : VOnly`, `vr : VRel`, `noIoTcb : NoIoTcb` (virt gen 26), `rngOne : RngOne` (virt gen
  28: kept by every `MdbStep`, true at boot, implies `VcpuOneChain` and, with `MdbInv`, `VcpuChunked` — so the
  contract's `chunked` field is the theorem **`VmState.chunked`**, not a field, per the coordinator's gen-28 note), and
  the four facts `JAtZV3` already carries that a VM step reads (`rvm : RunVmB`, `vm : JVm`, `vl : VList`,
  `vb : VBind`), so that `VmState` plus `IoOwnV` gives `JAtZV3` back (`VmState.toV3`) and every `JAtZV3` top applies.
* **`abbrev VmState := JAtZB ∧ VcpuCore`** — the base is `JAtZB` (`JAtZ` without its `ext : JExt` field), not `JAtZ`:
  `JAtZ.ext` says no slot holds a VCPU / EPT cap (`JExt`), false as soon as `V ≠ ∅` (P3/JAtZV's docstring), so
  `JAtZ ∧ VcpuCore` would only hold at `V = ∅`.
* **The split (mmuAD 42b1, architect)**: `JExtV2 V X` = `JExtVcpu V` (here, `VcpuCore.extv`) ∧ `JExtEpt X` (`Ept` caps
  into `X`, EPT-mapped frames need `X ≠ ∅`; `EptCore.exte`, P3/EptCore): **`jextV2_iff`**, via `vtxCap2_split`;
  `JExtVcpu.toV2u` (= `JExtV2 V univ`, so `JExtV2`'s step lemmas apply), `JExtEpt.of_eq`, `JExtEpt.of_jext`.
  `JExtV2` itself is unchanged.
* Bridge: **`JAtZV3.toVm`** (`JAtZV3` + `NoIoTcb` + `RngOne` ⇒ `VmState`; `JExtV.toV2`, `jextV2_iff`),
  `JAtZV3.eptExt`, **`VmState.toV3`** (`VmState` + `JExtEpt X` + `IoOwnV` ⇒ `JAtZV3`; `jExtV_iff_v2`, `jextV2_iff`), **`vmState_iff`** (both together). `NoIoTcb` and `RngOne` are
  what `JAtZV3` lacks: the bridge takes them as hypotheses, [J] at its users (virt gen 26: `NoIoTcb`, tcb.rs install
  paths; virt gen 28: `RngOne`, `rngOne_empty` at boot and `mdbStep_rngOne` per step). `IoOwnV` is what `VmState`
  lacks (false after a final VCPU delete with an owned IO-port cap left, P3/JExtV2 `not_jextV_of_stale`).
* `VmState.chunked`, `VmState.oneChain` (from `rngOne` and the base's `MdbLinks` / `MdbInv`).
* Frames, each record its own: `JAtZB.oobjV` / `JAtZB.kVv` (P3/JAtZBSched's `JAtZV.oobj_v` / P3/JAtZBSched2's
  `JAtZV.kV` with the base and `JVm` for `JAtZV`, proofs verbatim), **`VcpuCore.ofBS`** (a native step that may
  change the spec heap: `JAtZV.ofBS` + `JAtZV2.ofBS` + `JAtZV3.ofBS`'s argument with `JExtV2.of_eq`,
  `NoIoTcb.of_capEq`, `rngOne_congr` — slots are kept by `OObj` writes, `XTopAt.slotsSame_of`), **`VcpuCore.ofB`**
  (spec heap unchanged), **`VcpuCore.ofTK`** (an SC-code step, `TFoot` writes, `ScTKw`), and the `VmState`
  wrappers `VmState.ofBS` / `ofB` / `ofTK` / `archV`.

Gen 42b12 (the Architect's goal-4 fact (a)): `JExtEpt` gains the field `vtop : EptVTop` (a mapped `Ept` slot cap's
guest address is below `2^47`), which `JExtV2` does not carry. Statements changed (this module's own): `structure
JExtEpt` (+ `vtop`), `jextV2_iff` (`JExtV2 ∧ EptVTop ↔ JExtVcpu ∧ JExtEpt`), `JAtZV3.eptExt` (+ `hv : EptVTop`),
`vmState_iff` (`EptVTop` on the `JAtZV3` side). New: `EptVTop`, `JExtV2.vcpu`. `JExtVcpu.toV2u`, `JExtEpt.of_eq` /
`of_jext`, `JAtZV3.toVm`, `VmState.toV3` keep their statements.

Gen 42b13 (the Architect's `hz0` decision, option (i)): `JExtEpt` gains the field `anz : EptANz` (a mapped `Ept`
slot cap's ASID is nonzero), next to `vtop`. Statements changed (this module's own): `structure JExtEpt` (+ `anz`),
`jextV2_iff` (`JExtV2 ∧ EptVTop ∧ EptANz ↔ …`), `JAtZV3.eptExt` (+ `hz : EptANz`), `vmState_iff` (`EptANz` on the
`JAtZV3` side). New: `EptANz`.

Gen 42b15 (the Architect's decision on gen 42b14's stop): `EptVTop` extended in place (def body only, second
conjunct) to EPT-mapped frame caps (`Frame … true true a v → v < 2^47`); no new field, no new premise. Users take
`.vtop.1` for `Ept` caps, `.vtop.2` for frames. No statement up to `:=` changed in this module.

No named premise in this module (the bridge's `NoIoTcb` / `RngOne` / `IoOwnV` are hypotheses of the bridge theorems).
No JAtZV4 / V5 shell. gen 42b1 changed this module's own statements (VcpuCore / VmState lose `X`; the bridges take
`JExtEpt X`); no statement outside mmuAD 42a–42b0 changed.
-/
import Fl4Proofs.P3.JAtZV3
import Fl4Proofs.P3.JExtV2Bind
import Fl4Proofs.P3.VirtRngOne
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## The split of `JExtV2 V X` (architect, 42b1): `JExtVcpu V` ⟂ `JExtEpt X` -/

/-- The VCPU half of `VtxCap2`: a `Vcpu p` cap points into `V`. -/
def VcpuCapV (V : Set U64) : capability.Cap → Prop
  | .Vcpu p => p ∈ V
  | _ => True

/-- The EPT half of `VtxCap2`: an `Ept p …` cap points into `X`; an EPT-mapped frame cap needs `X ≠ ∅`. -/
def EptCapX (X : Set U64) : capability.Cap → Prop
  | .Ept p _ _ _ _ => p ∈ X
  | .Frame _ _ _ _ m e _ _ => m = true ∧ e = true → X.Nonempty
  | _ => True

/-- **`VtxCap2` is its VCPU half and its EPT half.** -/
theorem vtxCap2_split {V X : Set U64} {c : capability.Cap} : VtxCap2 V X c ↔ VcpuCapV V c ∧ EptCapX X c := by
  cases c with
  | Vcpu p => exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | Ept p l m a v => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | Frame p sz r d m e a v => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ => exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩

/-- Every cap is an `EptCapX univ` cap. -/
theorem eptCapX_univ (c : capability.Cap) : EptCapX Set.univ c := by
  cases c with
  | Ept p l m a v => exact Set.mem_univ p
  | Frame p sz r d m e a v => exact fun _ => Set.univ_nonempty
  | _ => trivial

/-- **A mapped `Ept` slot cap's guest address is below `2^47`, and so is an EPT-mapped frame cap's** (gen 42b12, the
Architect's goal-4 fact (a), a field of `JExtEpt`; gen 42b15, the Architect's decision: extended in place to
EPT-mapped frame caps, the second conjunct). FL4 writes a mapped `Ept` cap only in the table map (`vaddr: gpa` after
the `gpa < LIMIT` test, ept.rs l. 290-310, `LIMIT = 2^47`) and the pool assign (`vaddr: 0`, vspace.rs l. 1246); a
`Frame { mapped: true, is_ept: true }` cap only in `ept::map_frame` (`vaddr: gpa` after the `gpa >= LIMIT` test,
ept.rs l. 134, l. 173-184; unmap writes `vaddr: 0`); `derive_cap` copies both verbatim (objects.rs l. 219-224), and
Copy / Mint / DeriveSubframe only produce unmapped frames. -/
def EptVTop (th : TypedHeap) (m : U64 → U64) : Prop :=
  (∀ y, IsSlot th y → ∀ p l a v, capV m y = .Ept p l true a v → v.val < 2 ^ 47) ∧
  (∀ y, IsSlot th y → ∀ p sz r d a v, capV m y = .Frame p sz r d true true a v → v.val < 2 ^ 47)

/-- **A mapped `Ept` slot cap's ASID is nonzero** (gen 42b13, the Architect's `hz0` decision (i), a field of
`JExtEpt`): FL4 writes a mapped `Ept` cap only in the pool assign (`asid = base + i` with `base + i ≠ 0`, the
free-entry search of vspace.rs l. 1238) and the table map (the asid of the mapped root cap `extra[0]`, ept.rs
l. 290-310); `derive_cap` copies it verbatim (objects.rs l. 219-224). -/
def EptANz (th : TypedHeap) (m : U64 → U64) : Prop :=
  ∀ y, IsSlot th y → ∀ p l a v, capV m y = .Ept p l true a v → a ≠ 0#u64

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The VCPU half of `JExtV2`** (`VcpuCore`'s field): `Vcpu` slot caps point into `V`, and `JExtV2`'s binding
facts `bnd` / `back` / `nz` (all about `V`). No `X`. -/
structure JExtVcpu (V : Set U64) (th : TypedHeap) (s : S) : Prop where
  cap : ∀ y, IsSlot th y → VcpuCapV V (capV (L.mem s) y)
  bnd : ∀ t, th t = some .tcb → L.mem s (tVcpuA t) = 0#u64 ∨
    (L.mem s (tVcpuA t) ∈ V ∧ L.mem s (vTcbA (L.mem s (tVcpuA t))) = t)
  back : ∀ v ∈ V, L.mem s (vTcbA v) = 0#u64 ∨
    (th (L.mem s (vTcbA v)) = some .tcb ∧ L.mem s (tVcpuA (L.mem s (vTcbA v))) = v)
  nz : ∀ v ∈ V, v ≠ 0#u64

/-- **The EPT half of `JExtV2`** (`EptCore`'s field): `Ept` slot caps point into `X`, EPT-mapped frame caps need
`X ≠ ∅`. No `V`. -/
structure JExtEpt (X : Set U64) (th : TypedHeap) (s : S) : Prop where
  cap : ∀ y, IsSlot th y → EptCapX X (capV (L.mem s) y)
  vtop : EptVTop th (L.mem s)
  anz : EptANz th (L.mem s)

variable {V X : Set U64} {th : TypedHeap} {s s' : S}

/-- The VCPU half of `JExtV2` (gen 42b12: `jextV2_iff`'s first projection, kept as its own lemma). -/
theorem JExtV2.vcpu (E : JExtV2 (L := L) V X th s) : JExtVcpu (L := L) V th s :=
  ⟨fun y hy => (vtxCap2_split.1 (E.cap y hy)).1, E.bnd, E.back, E.nz⟩

/-- **`JExtV2 V X` with `EptVTop` ↔ `JExtVcpu V ∧ JExtEpt X`** (for the old bridges `JAtZV3.toVm` / `VmState.toV3`;
gen 42b12: `JExtEpt` carries `EptVTop`, which `JExtV2` does not). -/
theorem jextV2_iff : JExtV2 (L := L) V X th s ∧ EptVTop th (L.mem s) ∧ EptANz th (L.mem s) ↔
    JExtVcpu (L := L) V th s ∧ JExtEpt (L := L) X th s :=
  ⟨fun ⟨E, hv, hz⟩ => ⟨E.vcpu, ⟨fun y hy => (vtxCap2_split.1 (E.cap y hy)).2, hv, hz⟩⟩,
    fun ⟨E, F⟩ => ⟨⟨fun y hy => vtxCap2_split.2 ⟨E.cap y hy, F.cap y hy⟩, E.bnd, E.back, E.nz⟩, F.vtop, F.anz⟩⟩

/-- `JExtVcpu V` is `JExtV2 V univ` (so every `JExtV2` step lemma applies). -/
theorem JExtVcpu.toV2u (E : JExtVcpu (L := L) V th s) : JExtV2 (L := L) V Set.univ th s :=
  ⟨fun y hy => vtxCap2_split.2 ⟨E.cap y hy, eptCapX_univ _⟩, E.bnd, E.back, E.nz⟩

/-- `JExtEpt` with the slot caps unchanged. -/
theorem JExtEpt.of_eq (F : JExtEpt (L := L) X th s)
    (hc : ∀ y, IsSlot th y → capV (L.mem s') y = capV (L.mem s) y) : JExtEpt (L := L) X th s' :=
  ⟨fun y hy => by rw [hc y hy]; exact F.cap y hy, ⟨fun y hy p l a v h => F.vtop.1 y hy p l a v (by rw [← hc y hy]; exact h),
    fun y hy p sz r d a v h => F.vtop.2 y hy p sz r d a v (by rw [← hc y hy]; exact h)⟩,
    fun y hy p l a v h => F.anz y hy p l a v (by rw [← hc y hy]; exact h)⟩

/-- No slot holds an `Ept` cap or an EPT-mapped frame cap at a native state (`JExt`). -/
theorem JExtEpt.of_jext (E : JExt (L := L) th s) : JExtEpt (L := L) ∅ th s :=
  ⟨fun y hy => (vtxCap2_split.1 ((JExtV2.of_jext E).cap y hy)).2, ⟨fun y hy p l a v hc => by
    have h := (vtxCap2_split.1 ((JExtV2.of_jext E).cap y hy)).2
    rw [hc] at h
    exact (show p ∈ (∅ : Set U64) from h).elim, fun y hy p sz r d a v hc => by
    have h := (vtxCap2_split.1 ((JExtV2.of_jext E).cap y hy)).2
    rw [hc] at h
    exact (Set.not_nonempty_empty ((show true = true ∧ true = true → (∅ : Set U64).Nonempty from h) ⟨rfl, rfl⟩)).elim⟩, fun y hy p l a v hc => by
    have h := (vtxCap2_split.1 ((JExtV2.of_jext E).cap y hy)).2
    rw [hc] at h
    exact (show p ∈ (∅ : Set U64) from h).elim⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The VCPU facts of the VM epoch, one flat record** (module docstring). -/
structure VcpuCore (V : Set U64) (Z : XSets) (H : P1.Heap) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  extv : JExtVcpu (L := L) V Z.th s
  vo : VOnly V σ
  vr : VRel V σ (L.mem s)
  noIoTcb : NoIoTcb Z.th (L.mem s)
  rngOne : VirtRngOne.RngOne (L.mem s) Z.G
  rvm : RunVmB (L := L) Z.th s
  vm : JVm (L := L) V H s σ
  vl : VList st V Z.th s
  vb : VBind V σ (L.mem s)

/-- **The VM-epoch state: the native base without `JExt`, and the VCPU record** (module docstring). -/
abbrev VmState (V : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ VcpuCore (L := L) V Z H s σ

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-! ## The bridge -/

/-- **`JAtZV3` with `NoIoTcb` and `RngOne` is a `VmState`** (module docstring; `X` goes to `JExtEpt`). -/
theorem JAtZV3.toVm (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hN : NoIoTcb Z.th (L.mem s))
    (hR : VirtRngOne.RngOne (L.mem s) Z.G) : VmState (L := L) arI V AR Z H Cs Ac Lst D s a σ :=
  ⟨J.z2.zv.base, J.z2.zv.extv.toV2.vcpu, J.vo, J.vr, hN, hR, J.z2.zv.rvm, J.z2.zv.vm, J.z2.zv.vl,
    J.z2.vb⟩

/-- The EPT half of `JAtZV3`'s cap typing (gen 42b12: with `EptVTop`, which `JAtZV3` does not carry). -/
theorem JAtZV3.eptExt (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hv : EptVTop Z.th (L.mem s))
    (hz : EptANz Z.th (L.mem s)) : JExtEpt (L := L) X Z.th s :=
  (jextV2_iff.1 ⟨J.z2.zv.extv.toV2, hv, hz⟩).2

/-- **A `VmState` with the EPT cap typing `JExtEpt X` and every IO-port owner word 0 or listed is a `JAtZV3`**
(module docstring). -/
theorem VmState.toV3 (J : VmState (L := L) arI V AR Z H Cs Ac Lst D s a σ) (hX : JExtEpt (L := L) X Z.th s)
    (hI : IoOwnV V Z.th (L.mem s)) : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ :=
  ⟨⟨⟨J.1, jExtV_iff_v2.2 ⟨(jextV2_iff.2 ⟨J.2.extv, hX⟩).1, hI⟩, J.2.rvm, J.2.vm, J.2.vl⟩, J.2.vb⟩, J.2.vo, J.2.vr⟩

/-- **The bridge both ways.** -/
theorem vmState_iff :
    (JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ ∧ NoIoTcb Z.th (L.mem s) ∧ VirtRngOne.RngOne (L.mem s) Z.G ∧
        EptVTop Z.th (L.mem s) ∧ EptANz Z.th (L.mem s)) ↔
      (VmState (L := L) arI V AR Z H Cs Ac Lst D s a σ ∧ JExtEpt (L := L) X Z.th s ∧ IoOwnV V Z.th (L.mem s)) :=
  ⟨fun ⟨J, hN, hR, hv, hz⟩ => ⟨J.toVm hN hR, J.eptExt hv hz, (jExtV_iff_v2.1 J.z2.zv.extv).2⟩,
    fun ⟨J, hX, hI⟩ => ⟨J.toV3 hX hI, J.2.noIoTcb, J.2.rngOne, hX.vtop, hX.anz⟩⟩

/-- `VcpuOneChain` at a `VmState` (`vcpuOneChain_of_rngOne`). -/
theorem VmState.oneChain (J : VmState (L := L) arI V AR Z H Cs Ac Lst D s a σ) :
    VirtVChunkIns.VcpuOneChain Z.G (L.mem s) := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.1.xtop.rel
  exact VirtRngOne.vcpuOneChain_of_rngOne hM.tree.nodup J.2.rngOne

/-- **`VcpuChunked` at a `VmState`** (the contract's `chunked`, from `rngOne` and the base's `MdbInv`). -/
theorem VmState.chunked (J : VmState (L := L) arI V AR Z H Cs Ac Lst D s a σ) :
    VirtVChunk.VcpuChunked Z.G (L.mem s) := by
  obtain ⟨-, ⟨-, -, hM, -, hI⟩, -⟩ := J.1.xtop.rel
  exact VirtRngOne.vcpuChunked_of_rngOne hM hI J.2.rngOne

/-! ## Frames -/

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Sched

/-- `OObj` words miss every VCPU of `V` (P3/JAtZBSched's `JAtZV.oobj_v`, proof verbatim, from the base and `JVm`). -/
theorem JAtZB.oobjV (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) {v : U64}
    (hv : v ∈ V) {b : U64} (hb : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) :
    b.val < v.val ∨ v.val + 32768 ≤ b.val := by
  have hvH := Jv.heap v hv
  have dH : ∀ p k, H p = some k → k ≠ .other 15 → p.val + 2 ^ k.bits ≤ v.val ∨ v.val + 32768 ≤ p.val := by
    intro p k hp hk
    have hne : p ≠ v := fun e => by subst e; rw [hvH] at hp; cases hp; exact hk rfl
    rcases B.kern.heap.disj p k v _ hp hvH hne with h | h
    · exact Or.inl h
    · simp only [P1.HKind.bits, Nat.reducePow] at h; exact Or.inr h
  have hks := Jv.ks v hv
  rcases hb with ⟨g1, g2⟩ | ⟨g1, g2, -⟩ | ⟨t, ht, g1, g2⟩ | ⟨e, he, g1, g2⟩ | ⟨r, hr, g1, g2⟩ | ⟨n, hn, g1, g2⟩ |
      ⟨sc, hsc, x, n, hk, hso⟩ | ⟨wp, hwp, g1, g2⟩
  · obtain ⟨Q, R0, hcq, -⟩ := B.xtop.fin.1.1.1.lists
    have hcC : Z.c ∈ Cs := hcq.cur ▸ B.kern.cpuCs
    have hc64 := B.kern.csLt Z.c hcC
    have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
    rw [hnb] at g1 g2
    omega
  · omega
  · have d := dH t _ (B.zH.1 t ht) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · have d := dH e _ (B.zH.2.1 e he) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · have d := dH r _ (B.zH.2.2.1 r hr) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · have d := dH n _ (B.zH.2.2.2 n hn) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · obtain ⟨Tr, Cq, hJ⟩ := B.jpl
    have hH := (hJ.sc sc x n (B.c0 sc hsc) hk).2
    have d := dH sc _ hH (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d
    unfold Sched.ScObj at hso
    omega
  · obtain ⟨q, vms, hq, q1, q2⟩ := B.carry.bufPg wp hwp
    obtain ⟨y, hy⟩ := Jv.spec v hv
    have hne : q ≠ v.bv := fun e' => by rw [e', hy] at hq; cases hq
    have eb : Fl4Spec.objBits (.archObj (.dataPage false vms)) = Fl4Spec.pageBitsForSize vms := by
      simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]
    rcases Jv.sep v hv q _ hq hne with e1 | e1
    · rw [eb] at e1; omega
    · omega

end

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- `OObj` writes keep every VCPU's `TCB` word (P3/JAtZBSched2's `JAtZV.kV`, proof verbatim). -/
theorem JAtZB.kVv (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) {s' : S}
    {W : U64 → Prop} (hw : P1.WritesIn st s s' W) (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) :
    ∀ u ∈ V, L.mem s' (vTcbA u) = L.mem s (vTcbA u) := by
  intro u hu
  have hf := (B.jvLay Jv).vfit u hu
  have e := lay_vTcb_val hf.2
  exact hw.mem_eq (by unfold P1.Aligned; rw [e]; omega) fun hb => by
    rcases B.oobjV Jv hu (hO _ hb) with h | h <;> omega

set_option maxHeartbeats 4000000 in
/-- **`VcpuCore` across a native step that may change the spec heap** (module docstring; the arguments of
`JAtZV.ofBS`, `JAtZV2.ofBS`, `JAtZV3.ofBS`). -/
theorem VcpuCore.ofBS (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ)
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s')
    (hvk : ∀ u ∈ V, σ'.kheap u.bv = σ.kheap u.bv)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (hrv : ∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM)
    (hnv : ∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
      σ.kheap p = some (.archObj (.vcpu vs))) :
    VcpuCore (L := L) V Z H s' σ' := by
  have Ly := B.jvLay C.vm
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') := B.xtop.slotsSame_of hw hO
  have nV : ∀ u ∈ V, ∀ b, W b → b.val < u.val ∨ u.val + 32768 ≤ b.val := fun u hu b hb => B.oobjV C.vm hu (hO b hb)
  have kV := B.kVv C.vm hw hO
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := B.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have E' : JExtVcpu (L := L) V Z.th s' :=
    (C.extv.toV2u.of_eq (fun y hy => hSS.capV hy) hv kV).vcpu
  have R' : RunVmB (L := L) Z.th s' := by
    intro t ht h8
    rw [hv t ht]
    refine C.rvm t ht ?_
    obtain ⟨x', hk', -⟩ := B'.xtop.rel.2.1.1.tcb t ht
    have w' := (B'.xtop.fin.1.1.2.2.1.at_tcb (B'.thT t ht) hk').st
    rw [Sched.stA_tStA] at h8 ⊢
    rw [h8] at w'
    have hx' : x'.tcbState = .runningVM := by
      cases hx : x'.tcbState <;> rw [hx] at w' <;> simp_all [tsCode]
    obtain ⟨x, hk, hx⟩ := hrv _ x' hk' hx'
    have w0 := (B.xtop.fin.1.1.2.2.1.at_tcb (B.thT t ht) hk).st
    rw [hx] at w0
    apply UScalar.eq_of_val_eq
    rw [w0]; simp [tsCode]
  have Jv' : JVm (L := L) V H s' σ' :=
    C.vm.step (fun _ h => h) (fun _ _ => rfl) hw.1 (fun u hu => by rw [hvk u hu]; exact C.vm.spec u hu)
      (fun o ko' ho => Or.inl (hsz o ko' ho))
  have Vl' : VList st V Z.th s' := C.vl.writes hw fun b hb => by
    refine ⟨C.vl.lw_al Ly.vfit hb, fun hW => ?_⟩
    rcases hb with rfl | ⟨u, hu, rfl | rfl⟩
    · exact hh _ hW rfl
    · have := lay_next_val (Ly.vfit u hu).2
      rcases nV u hu _ hW with h | h <;> omega
    · have := lay_prev_val (Ly.vfit u hu).2
      rcases nV u hu _ hW with h | h <;> omega
  exact ⟨E', C.vo.frame hnv,
    C.vr.frame (fun u _ vs hu => hnv _ vs hu) (v3_agreeW (L := L) hw (fun u hu => (Ly.vfit u hu).2) nV),
    C.noIoTcb.of_capEq fun y hy => hSS.capV (isSlot_thTcb hy),
    VirtRngOne.rngOne_congr C.rngOne fun z hz _ => by rw [hSS.capV (hsl z hz)]; exact NoA.refl _,
    R', Jv', Vl', C.vb.ofV hvk kV⟩

/-- **`VcpuCore` across a native step keeping the spec heap.** -/
theorem VcpuCore.ofB (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ)
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s') (hke : σ'.kheap = σ.kheap) :
    VcpuCore (L := L) V Z H s' σ' :=
  C.ofBS B B' hw hO hh hv (fun u _ => by rw [hke]) (fun o ko' ho => ⟨ko', by rw [← hke]; exact ho, rfl⟩)
    (fun o x' ho hx => ⟨x', by rw [← hke]; exact ho, hx⟩) (fun p vs hp => by rw [← hke]; exact hp)

/-- **`VcpuCore` across an SC-code step** (`TFoot` writes, `ScTKw`; as `JAtZV2.ofTK` / `JAtZV3.ofTK`). -/
theorem VcpuCore.ofTK (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ)
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw (fun _ => False) σ σ') :
    VcpuCore (L := L) V Z H s' σ' := by
  have hS := B.xtop.fin.1.1.1
  obtain ⟨h1, h2, h3⟩ := zv_tk hK
  exact C.ofBS B B' hw (fun b hb => Sched.tfoot_oobj hS hb) (fun b hb => B.tfoot_nh hb) (VKeep.of_tfoot hS B.thT hw)
    (fun u hu => by obtain ⟨y, hy⟩ := C.vm.spec u hu; exact h1 _ _ hy) h2 h3 (zv_tk_v hK)

/-- `VmState` across a native step that may change the spec heap (`VcpuCore.ofBS`). -/
theorem VmState.ofBS (J : VmState (L := L) arI V AR Z H Cs Ac Lst D s a σ)
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s')
    (hvk : ∀ u ∈ V, σ'.kheap u.bv = σ.kheap u.bv)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (hrv : ∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM)
    (hnv : ∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
      σ.kheap p = some (.archObj (.vcpu vs))) :
    VmState (L := L) arI V AR Z H Cs Ac' Lst' D' s' a' σ' :=
  ⟨B', J.2.ofBS J.1 B' hw hO hh hv hvk hsz hrv hnv⟩

/-- `VmState` across a native step keeping the spec heap (`VcpuCore.ofB`). -/
theorem VmState.ofB (J : VmState (L := L) arI V AR Z H Cs Ac Lst D s a σ)
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s') (hke : σ'.kheap = σ.kheap) :
    VmState (L := L) arI V AR Z H Cs Ac' Lst' D' s' a' σ' :=
  ⟨B', J.2.ofB J.1 B' hw hO hh hv hke⟩

/-- `VmState` across an SC-code step (`VcpuCore.ofTK`). -/
theorem VmState.ofTK (J : VmState (L := L) arI V AR Z H Cs Ac Lst D s a σ)
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw (fun _ => False) σ σ') :
    VmState (L := L) arI V AR Z H Cs Ac' Lst' D' s' a' σ' :=
  ⟨B', J.2.ofTK J.1 B' hw hK⟩

/-- `VmState` with another arch state relating to the same CR3 (`JAtZB.archV`). -/
theorem VmState.archV (J : VmState (L := L) arI V AR Z H Cs Ac Lst D s a σ) {a' : A}
    (hAR : AR a' σ.archState.x64CurrentCr3) : VmState (L := L) arI V AR Z H Cs Ac Lst D s a' σ :=
  ⟨J.1.archV hAR, J.2⟩

end

end

end

end Fl4Proofs.P3
