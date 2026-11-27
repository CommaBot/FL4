/-
P3 (line mmuAD, gen 19): **`JExtV`, the VM-epoch form of the joint extension `JExt`** (scoping step of the
VT-x scope, vmscope stage 6).

## Why `JExt` reaches no guest-running state

`JAtZ.ext : JExt Z.th s` has two fields, both [S] native-scope facts:

* `nat`: every slot cap is `Vs.NativeCap` (no `Vcpu` / `Ept` cap, no EPT-mapped frame cap, no IO-port cap owned by
  a VCPU). **False in every VM epoch**: a guest runs only on a thread bound by `X86VCPUSetTCB`, which is invoked
  through a `Vcpu` cap (fl4-core vcpu.rs `decode`, l. 845), and the vCPU object came from a VT-x retype.
* `vw`: every TCB of the typed heap has its VCPU word `tVcpuA t` (`tl::VCPU`, offset 3664) zero. **False in every
  VM epoch**: `X86VCPUSetTCB` writes `v` there (vcpu.rs l. 860) and `vcpu::enter` refuses (`v == 0`) to put a
  thread in `TS_RUNNING_VM` without it (l. 1076).

What the kernel maintains instead (fl4-core vcpu.rs, checked in the Rust):

* the binding is **symmetric**: the only writers of the two words are `X86VCPUSetTCB` (detach `target`, detach
  `v`'s old thread, then `VCPU.TCB := target` and `target.VCPU := v`, l. 853-860) and `vcpu::detach` (both words
  to 0, l. 733-734; called by `X86VCPUSetTCB`, by `vcpu::finalise` of a VCPU, l. 742, and by the TCB finaliser,
  objects.rs l. 361); a TCB retype zeroes its word and `vcpu::init` leaves `TCB` (offset 0x5000) zero. So a
  nonzero `t.VCPU = v` names a VCPU whose `TCB` word is `t`, and a nonzero `v.TCB = t` names a TCB whose `VCPU`
  word is `v` (l4v ARM_HYP `sym_refs` of `tcb_vcpu` / `vcpu_tcb`; spec side `Fl4Spec.VcpuBindingInv`).
* the binding **is not tied to `TS_RUNNING_VM`**: a bound thread keeps its VCPU across VM exits, blocking, IPC,
  and so on. The coupling goes the other way: `TS_RUNNING_VM` is entered only by `vcpu::enter` with `v ≠ 0`
  (l. 1119), and `detach` of a `TS_RUNNING_VM` thread first `report`s it, which sets `TS_RUNNING` (l. 729-731,
  l. 1213), before zeroing the word. So: **state `TS_RUNNING_VM` ⇒ VCPU word nonzero** (`RunVmB` below).
  (`vcpu::check`'s `v == 0` branch, l. 1141, is a defensive path the invariant makes dead.)

## Component-by-component (what fails once a VCPU word may be nonzero, and the VM-epoch analogue)

* `JExt.nat` — fails; analogue `JExtV.cap`: every slot cap is `VtxCap V X` (a `Vcpu` cap names a VCPU of `V`, an
  `Ept` cap an EPT table of `X`, an EPT-mapped frame exists only when some EPT table does, an owned IO port's owner
  is in `V`). `VtxCap ∅ ∅ = NativeCap` (`vtxCap_empty_iff`).
* `JExt.vw` — fails; analogue `JExtV.bnd` / `JExtV.back` / `JExtV.nz` (the symmetric binding over `V`), plus
  `RunVmB` (`TS_RUNNING_VM` ⇒ bound) as the FL4-side analogue of the spec's `NativeScope`.
* `SInvX` (spec invariant carried beside `JAtZ`) — its invA part `SInvA.ns` (`NativeScopeS`: no spec TCB
  `runningVM`) fails in every VM epoch where a guest is running; more basically `SInvX` is an invariant of the
  *ported* spec (`fl4CallKernel`), which has no VCPU object and no `runningVM` step: the VM-epoch analogue must be an
  invariant of the extended spec `fl4CallKernelV` (Ext/VirtKernel) with `NativeScope` replaced by
  `VcpuBindingInv` and "`runningVM` ⇒ `tcbVcpuOf` some" (the spec mirror of `RunVmB`). The virt line's NV /
  `NoRunVM` preservation (P3/VirtR7*, VirtNvCaps) covers only `virtKind = none` / no-VCPU states, i.e. the
  `V = ∅` corner of this module; it gives no VM-epoch fact.
* `JAtZ`'s other fields — their statements do not mention VCPU words or VT-x caps, and P3 already admits VCPU
  objects in `H` (`.other 15`, `JAtZ.vcpuH`) and proves a VCPU-word write keeps `JAtZ` (`JAtZ.vcpuWrJ`). They are
  true in VM epochs per the Rust (VCPUs are separate untyped-retyped objects, never frames, slots or
  kernel-global words), but every proof that they are *kept* is a native-step proof over the ported spec that
  also threads `ext`, so none is a VM-epoch invariant yet.
* `RegionOKX` (from P3's bundle, `ok_of_JAtZ` / `SlJAtZ`) — its statement is about native objects only and stays
  true; analogue = `RegionOKX` plus the VCPU regions (`VcpuLay`, `JVmL` / `VFacts`, P2) — vmscope's `VtxBundle4`.
* `IoQ` / `IoPre` — per-core entry facts of the *current* thread; `IoPre.run` (`TS_RESTART ∨ TS_RUNNING`) is derived
  in P3 from the global `NativeScope` (`JAtZ.curRunR'`). In a VM epoch it still holds at a syscall entry (a
  `TS_RUNNING_VM` thread enters the kernel by a VM exit, not a syscall), but the analogue must come from the entry
  kind, not from a global "no thread runs a guest".

## What this module proves

* `VtxCap` (the VCPU's `TCB` word is the existing `vTcbA`, P3/XTopJointFinVtOps: `v + vcpu.TCB`, 0x5000), `VtxCap.of_native`, `VtxCap.native_of_empty`,
  `vtxCap_empty_iff`.
* **`JExtV V X th s`** (fields `cap`, `bnd`, `back`, `nz`), **`RunVmB th s`**.
* Native implication (nothing native lost): **`JExtV.of_jext`** (`JExt → JExtV ∅ ∅`), **`JExtV.toJExt`**
  (`JExtV ∅ ∅ → JExt`), **`jExtV_empty_iff`**, **`JAtZ.extV`** (every P3 joint state satisfies `JExtV ∅ ∅`),
  **`JExtV.vw_of_unbound`** (no VCPU bound ⇒ `JExt.vw`'s conclusion), `RunVmB.noRun` (no bound TCB ⇒ no FL4
  thread in `TS_RUNNING_VM`).
* Boot: **`JBoot.w0_extV`**, **`JBoot.w1_extV`**, **`JBoot.w0_rvm`**, **`JBoot.w1_rvm`** (both P3 boot witnesses;
  there `JExtV ∅ ∅` is `JExt`).
* Preservation, memory-effect level: **`JExtV.of_eq`** (caps, TCB VCPU words and `V`'s `TCB` words kept: every step
  whose footprint misses them, the analogue of `JExt.of_eq`), **`JExtV.step`** (every slot's cap afterwards native
  or an old slot's cap: copy / move / mint-as-copy of a VT-x cap), **`JExtV.bind`** (the two writes of
  `X86VCPUSetTCB` on an unbound pair, vcpu.rs l. 859-860), **`JExtV.unbind`** (the two writes of `vcpu::detach` on
  a bound pair, l. 733-734), `RunVmB.of_eq` / `RunVmB.step` (state words written only to values other than
  `TS_RUNNING_VM`, or VCPU words kept nonzero).

## Open (named, not claimed)

* **Preservation of `JExtV` / `RunVmB` by the kernel's steps** — [open]: connecting `JExtV.bind` / `unbind` to the
  extracted `vcpu.decode` (X86VCPUSetTCB) / `vcpu.detach` / `vcpu.finalise` / TCB finalise / VT-x retype
  (`create_arch_object`, `V` grows), and proving every native step keeps the VT-x words (the `VKeep` frames P3
  already has, plus `V`'s `TCB` words, which need `JVm`-style placement of `V` at the step) and keeps every
  VT-x cap's object in `V` / `X` (CSpace steps, `JExtV.step`; VT-x object deletion shrinks `V`).
* **A VM-epoch joint invariant** (`JAtZ` with `ext := JExtV`) reachable over the extended spec — the P3 VT-x scope
  (vmscope stage 6, VIRT-PLAN R0/R5/R6). Until it exists, no VM-epoch [S] item of P2 (`InvEntV9`, `VmPweU`, `ne0`,
  `PmQF ∧ PmEx`, `VtxBundle4`) can be derived from a proved invariant: deriving one from `JExtV` at a VM-epoch start
  would assume `JExtV` (or a `JAtZ`-with-`JExtV` bundle) there, i.e. swap one [S] for another. In particular `ne0`
  natively comes from `JKern.h0` / `PtRel` / `SpecCover`, none of which is about VCPUs: it needs the VM-epoch
  bundle, not `JExtV` alone. So this generation derives none of them.

No [J]/[P]/[W]/[S] premise is introduced: every theorem's hypotheses are its stated memory / state facts. No
existing statement changed.
-/
import Fl4Proofs.P3.JointAt
import Fl4Proofs.P3.JBoot1Blk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- **A cap of the VM epoch at VCPU set `V` and EPT-table set `X`** (module docstring): what `Vs.NativeCap`
becomes once VT-x objects exist. -/
def VtxCap (V X : Set U64) : capability.Cap → Prop
  | .Vcpu p => p ∈ V
  | .Ept p _ _ _ _ => p ∈ X
  | .Frame _ _ _ _ m e _ _ => m = true ∧ e = true → X.Nonempty
  | .IoPort _ _ o => o ≠ 0#u64 → o ∈ V
  | _ => True

theorem VtxCap.of_native {V X : Set U64} {c : capability.Cap} (h : Vs.NativeCap c) : VtxCap V X c := by
  cases c with
  | Vcpu p => exact False.elim h
  | Ept p l m a v => exact False.elim h
  | Frame p sz r d m e a v =>
    have h' : ¬ (m = true ∧ e = true) := h
    show m = true ∧ e = true → X.Nonempty
    exact fun hme => absurd hme h'
  | IoPort f l o =>
    have h' : o = 0#u64 := h
    show o ≠ 0#u64 → o ∈ V
    exact fun ho => absurd h' ho
  | _ => trivial

theorem VtxCap.native_of_empty {c : capability.Cap} (h : VtxCap ∅ ∅ c) : Vs.NativeCap c := by
  cases c with
  | Vcpu p => exact (show p ∈ (∅ : Set U64) from h).elim
  | Ept p l m a v => exact (show p ∈ (∅ : Set U64) from h).elim
  | Frame p sz r d m e a v =>
    have h' : m = true ∧ e = true → (∅ : Set U64).Nonempty := h
    show ¬ (m = true ∧ e = true)
    intro hme
    obtain ⟨x, hx⟩ := h' hme
    exact hx.elim
  | IoPort f l o =>
    have h' : o ≠ 0#u64 → o ∈ (∅ : Set U64) := h
    show o = 0#u64
    exact Classical.byContradiction fun ho => (h' ho).elim
  | _ => trivial

theorem vtxCap_empty_iff (c : capability.Cap) : VtxCap ∅ ∅ c ↔ Vs.NativeCap c :=
  ⟨VtxCap.native_of_empty, VtxCap.of_native⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The VM-epoch joint extension** (module docstring) at the VCPU set `V` and EPT-table set `X`. -/
structure JExtV (V X : Set U64) (th : TypedHeap) (s : S) : Prop where
  /-- Every slot's cap is a VM-epoch cap (`JExt.nat` relaxed). -/
  cap : ∀ y, IsSlot th y → VtxCap V X (capV (L.mem s) y)
  /-- A TCB's VCPU word is 0 or a VCPU of `V` whose `TCB` word is that TCB (`JExt.vw` relaxed). -/
  bnd : ∀ t, th t = some .tcb → L.mem s (tVcpuA t) = 0#u64 ∨
    (L.mem s (tVcpuA t) ∈ V ∧ L.mem s (vTcbA (L.mem s (tVcpuA t))) = t)
  /-- A VCPU's `TCB` word is 0 or a TCB whose VCPU word is that VCPU. -/
  back : ∀ v ∈ V, L.mem s (vTcbA v) = 0#u64 ∨
    (th (L.mem s (vTcbA v)) = some .tcb ∧ L.mem s (tVcpuA (L.mem s (vTcbA v))) = v)
  /-- No VCPU at address 0. -/
  nz : ∀ v ∈ V, v ≠ 0#u64

/-- **`TS_RUNNING_VM` only with a bound VCPU** (module docstring; vcpu.rs `enter` / `detach`). -/
def RunVmB (th : TypedHeap) (s : S) : Prop :=
  ∀ t, th t = some .tcb → L.mem s (P1.stA t) = 8#u64 → L.mem s (tVcpuA t) ≠ 0#u64

variable {V X : Set U64} {th : TypedHeap} {s s' : S}

/-! ## Nothing native lost -/

theorem JExtV.of_jext (E : JExt (L := L) th s) : JExtV (L := L) ∅ ∅ th s where
  cap y hy := VtxCap.of_native (E.nat y hy)
  bnd t ht := Or.inl (E.vw t ht)
  back _ h := h.elim
  nz _ h := h.elim

theorem JExtV.toJExt (E : JExtV (L := L) ∅ ∅ th s) : JExt (L := L) th s where
  nat y hy := VtxCap.native_of_empty (E.cap y hy)
  vw t ht := (E.bnd t ht).resolve_right fun h => h.1.elim

theorem jExtV_empty_iff : JExtV (L := L) ∅ ∅ th s ↔ JExt (L := L) th s :=
  ⟨JExtV.toJExt, JExtV.of_jext⟩

/-- **Every P3 joint state satisfies `JExtV ∅ ∅`.** -/
theorem JAtZ.extV {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : JExtV (L := L) ∅ ∅ Z.th s :=
  JExtV.of_jext J.ext

/-- **No VCPU bound ⇒ every TCB's VCPU word is 0** (`JExt.vw`'s conclusion at any `V`). -/
theorem JExtV.vw_of_unbound (E : JExtV (L := L) V X th s) (hu : ∀ v ∈ V, L.mem s (vTcbA v) = 0#u64)
    (h0 : th 0#u64 ≠ some .tcb) : ∀ t, th t = some .tcb → L.mem s (tVcpuA t) = 0#u64 := by
  intro t ht
  rcases E.bnd t ht with h | ⟨hv, hb⟩
  · exact h
  · rw [hu _ hv] at hb
    subst hb
    exact (h0 ht).elim

/-- No bound TCB ⇒ no FL4 thread in `TS_RUNNING_VM` (the FL4 side of `NativeScope`). -/
theorem RunVmB.noRun (R : RunVmB (L := L) th s) (hw : ∀ t, th t = some .tcb → L.mem s (tVcpuA t) = 0#u64) :
    ∀ t, th t = some .tcb → L.mem s (P1.stA t) ≠ 8#u64 :=
  fun t ht hs => R t ht hs (hw t ht)

/-! ## Preservation at the memory-effect level -/

/-- **Frame**: caps, TCB VCPU words and `V`'s `TCB` words kept. -/
theorem JExtV.of_eq (E : JExtV (L := L) V X th s)
    (hc : ∀ y, IsSlot th y → capV (L.mem s') y = capV (L.mem s) y) (hv : VKeep (L := L) th s s')
    (hb : ∀ v ∈ V, L.mem s' (vTcbA v) = L.mem s (vTcbA v)) : JExtV (L := L) V X th s' where
  cap y hy := by rw [hc y hy]; exact E.cap y hy
  bnd t ht := by
    rw [hv t ht]
    rcases E.bnd t ht with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, by rw [hb _ h1]; exact h2⟩
  back v hv' := by
    rw [hb v hv']
    rcases E.back v hv' with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, by rw [hv _ h1]; exact h2⟩
  nz := E.nz

/-- **A CSpace step**: every slot's cap afterwards is native or an old slot's cap. -/
theorem JExtV.step (E : JExtV (L := L) V X th s)
    (hT : ∀ y, IsSlot th y → Vs.NativeCap (capV (L.mem s') y) ∨
      ∃ y', IsSlot th y' ∧ capV (L.mem s') y = capV (L.mem s) y')
    (hv : VKeep (L := L) th s s') (hb : ∀ v ∈ V, L.mem s' (vTcbA v) = L.mem s (vTcbA v)) :
    JExtV (L := L) V X th s' where
  cap y hy := by
    rcases hT y hy with h | ⟨y', hy', e⟩
    · exact VtxCap.of_native h
    · rw [e]; exact E.cap y' hy'
  bnd t ht := by
    rw [hv t ht]
    rcases E.bnd t ht with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, by rw [hb _ h1]; exact h2⟩
  back v hv' := by
    rw [hb v hv']
    rcases E.back v hv' with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, by rw [hv _ h1]; exact h2⟩
  nz := E.nz

/-- **Binding** (`X86VCPUSetTCB`'s two writes, vcpu.rs l. 859-860, after both detaches): an unbound TCB `t` and
an unbound VCPU `v ∈ V` get each other's address; every other cap / VCPU word / `TCB` word kept. -/
theorem JExtV.bind (E : JExtV (L := L) V X th s) {t v : U64} (ht : th t = some .tcb) (hv : v ∈ V)
    (hw0 : L.mem s (tVcpuA t) = 0#u64) (hb0 : L.mem s (vTcbA v) = 0#u64) (h0 : th 0#u64 ≠ some .tcb)
    (hc : ∀ y, IsSlot th y → capV (L.mem s') y = capV (L.mem s) y)
    (h1 : L.mem s' (tVcpuA t) = v) (h2 : L.mem s' (vTcbA v) = t)
    (hT : ∀ t', th t' = some .tcb → t' ≠ t → L.mem s' (tVcpuA t') = L.mem s (tVcpuA t'))
    (hV : ∀ w ∈ V, w ≠ v → L.mem s' (vTcbA w) = L.mem s (vTcbA w)) : JExtV (L := L) V X th s' where
  cap y hy := by rw [hc y hy]; exact E.cap y hy
  bnd t' ht' := by
    by_cases e : t' = t
    · rw [e, h1]; exact Or.inr ⟨hv, h2⟩
    · rw [hT t' ht' e]
      rcases E.bnd t' ht' with h | ⟨hw, hb⟩
      · exact Or.inl h
      · refine Or.inr ⟨hw, ?_⟩
        have hne : L.mem s (tVcpuA t') ≠ v := by
          intro e'
          rw [e', hb0] at hb
          rw [← hb] at ht'
          exact h0 ht'
        rw [hV _ hw hne]; exact hb
  back w hw := by
    by_cases e : w = v
    · rw [e, h2]; exact Or.inr ⟨ht, h1⟩
    · rw [hV w hw e]
      rcases E.back w hw with h | ⟨htt, hb⟩
      · exact Or.inl h
      · refine Or.inr ⟨htt, ?_⟩
        have hne : L.mem s (vTcbA w) ≠ t := by
          intro e'
          rw [e', hw0] at hb
          exact E.nz w hw hb.symm
        rw [hT _ htt hne]; exact hb
  nz := E.nz

/-- **Unbinding** (`vcpu::detach`'s two writes, vcpu.rs l. 733-734): a bound pair `t ↔ v` gets both words 0;
every other cap / VCPU word / `TCB` word kept. -/
theorem JExtV.unbind (E : JExtV (L := L) V X th s) {t v : U64} (hv : v ∈ V)
    (htv : L.mem s (tVcpuA t) = v) (hvt : L.mem s (vTcbA v) = t)
    (hc : ∀ y, IsSlot th y → capV (L.mem s') y = capV (L.mem s) y)
    (h1 : L.mem s' (tVcpuA t) = 0#u64) (h2 : L.mem s' (vTcbA v) = 0#u64)
    (hT : ∀ t', th t' = some .tcb → t' ≠ t → L.mem s' (tVcpuA t') = L.mem s (tVcpuA t'))
    (hV : ∀ w ∈ V, w ≠ v → L.mem s' (vTcbA w) = L.mem s (vTcbA w)) : JExtV (L := L) V X th s' where
  cap y hy := by rw [hc y hy]; exact E.cap y hy
  bnd t' ht' := by
    by_cases e : t' = t
    · rw [e, h1]; exact Or.inl rfl
    · rw [hT t' ht' e]
      rcases E.bnd t' ht' with h | ⟨hw, hb⟩
      · exact Or.inl h
      · refine Or.inr ⟨hw, ?_⟩
        have hne : L.mem s (tVcpuA t') ≠ v := by
          intro e'
          rw [e', hvt] at hb
          exact e hb.symm
        rw [hV _ hw hne]; exact hb
  back w hw := by
    by_cases e : w = v
    · rw [e, h2]; exact Or.inl rfl
    · rw [hV w hw e]
      rcases E.back w hw with h | ⟨htt, hb⟩
      · exact Or.inl h
      · refine Or.inr ⟨htt, ?_⟩
        have hne : L.mem s (vTcbA w) ≠ t := by
          intro e'
          rw [e', htv] at hb
          exact e hb.symm
        rw [hT _ htt hne]; exact hb
  nz := E.nz

/-- **`RunVmB` kept** when every TCB in `TS_RUNNING_VM` afterwards was so before with its VCPU word kept (no step
but `vcpu::enter` writes `TS_RUNNING_VM`). -/
theorem RunVmB.step (R : RunVmB (L := L) th s)
    (hs : ∀ t, th t = some .tcb → L.mem s' (P1.stA t) = 8#u64 →
      L.mem s (P1.stA t) = 8#u64 ∧ L.mem s' (tVcpuA t) = L.mem s (tVcpuA t)) :
    RunVmB (L := L) th s' := by
  intro t ht h8
  obtain ⟨h8', hw⟩ := hs t ht h8
  rw [hw]; exact R t ht h8'

/-- **`RunVmB` at `vcpu::enter`**: `t` enters `TS_RUNNING_VM` with its VCPU word nonzero (vcpu.rs l. 1076,
1119), every other TCB as in `RunVmB.step`. -/
theorem RunVmB.enter (R : RunVmB (L := L) th s) {t : U64} (hw : L.mem s' (tVcpuA t) ≠ 0#u64)
    (hs : ∀ t', th t' = some .tcb → t' ≠ t → L.mem s' (P1.stA t') = 8#u64 →
      L.mem s (P1.stA t') = 8#u64 ∧ L.mem s' (tVcpuA t') = L.mem s (tVcpuA t')) :
    RunVmB (L := L) th s' := by
  intro t' ht h8
  by_cases e : t' = t
  · rw [e]; exact hw
  · obtain ⟨h8', hw'⟩ := hs t' ht e h8
    rw [hw']; exact R t' ht h8'

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Classical

/-- **`JExtV` at the boot witness `w0`** (there it is `JExt`, `w0_ext`). -/
theorem w0_extV : JExtV (L := wL) ∅ ∅ thW w0 := JExtV.of_jext w0_ext

/-- **`JExtV` at the richer boot witness `w1`** (`w1_ext`). -/
theorem w1_extV : JExtV (L := wL) ∅ ∅ thW1 w1 := JExtV.of_jext w1_ext

/-- **`RunVmB` at `w0`**: the idle TCB's state is 7 (`TS_IDLE`), not `TS_RUNNING_VM`. -/
theorem w0_rvm : RunVmB (L := wL) thW w0 := by
  intro t ht hs
  rcases thW_some ht with ⟨rfl, -⟩ | ⟨_, _, e⟩
  · rw [st7] at hs; exact absurd hs (by decide)
  · cases e

/-- **`RunVmB` at `w1`**: states 7 (idle) and 1 (the root thread, `TS_RUNNING`). -/
theorem w1_rvm : RunVmB (L := wL) thW1 w1 := by
  intro t ht hs
  rcases st_w1 t (thT_thW1 t ht) with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] at hs <;> exact absurd hs (by decide)

end Fl4Proofs.P3.JBoot
