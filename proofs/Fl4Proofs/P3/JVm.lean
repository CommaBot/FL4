/-
P3 (line vlift, gen 7): **VM object coverage `JVm`**: the one P3-side fact the VM-domain layout needs.

`JVm V H s σ` says of a set `V` of addresses (P2 instantiates `V := K.vcpus`, the layout's VCPUs):

* `spec`: each `v ∈ V` is a spec VCPU object of `σ` (`archObj (.vcpu _)`, 2^15 bytes);
* `heap`: it is P1's heap object `.other 15` at `v` (its full spec range: `SpecCover.arch` + `ArchFitHyp` give
  only `other n` with `12 ≤ n ≤ 15`, `JAtZ.vcpuH`);
* `ks`: it lies off the kernel-global area `[ksb, ksb + 304384)` (state block, all 64 node slots, ASID table;
  `JKern.hksIn` / `hnd` give the block and the live cores' nodes for `H`'s `other` objects, not the rest);
* `sep`: no other spec object meets its range (l4v `pspace_distinct`, restricted to the VCPUs of `V`).

It is not a field of `JAtZ` (P3's joint invariant is native-scoped, `JExt.nat`): P2 asks it at each bundle
(`P2/E2EVJVm.lean`), where it implies every VM-layout [J] of line vlift (`VcpuHeap`, `VcpuSpec`, `VcpuKsOff`,
`VcpuTabOff`, `PoolObj`, `UserObj`).

**Preservation** (statements of the step shapes P3's spec steps have; module docstring of `P2/E2EVJVm.lean` and
the handoff list which event gives which):

* `JVm.empty` / `JVm.mono`: `∅` always; subsets.
* **`JVm.step`** (general): `V' ⊆ V`, `H'` agrees on `V'`, `ksb` kept, `V'` still spec VCPUs, every object of `σ'`
  either an old one of the same size or apart from `V'`.
* **`JVm.updK`**: an in-place update of a non-VCPU object keeping its size (every IPC / scheduler / CSpace / VSpace
  object write: `Notif.updK`); **`JVm.ofKheap`**: `σ'` with the same heap (machine / scheduler-state steps);
* **`JVm.ksz`**: a step keeping every object's type (`KSz`, the shape P3 proves of its `NKZ` spec steps:
  `capInsert_nkz` etc., `P3/SpecKSz.lean`) and keeping `V`'s objects present;
* **`JVm.restrict`**: objects removed (detype): `V` cut to the VCPUs still present;
* **`JVm.create`**: new objects at addresses empty in `σ`, apart from `V` (retype of non-VCPU objects).
* `JAtZ.vcpuWord0` / `JAtZ.curVcpu0`: at every `JAtZ` state no TCB is bound to a VCPU (`JExt.vw`), so the
  "exiting VCPU ∈ V" premise of the VM paths is vacuous at P3 states.
-/
import Fl4Proofs.P3.JointAt
import Fl4Proofs.P3.SpecKSz
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- A spec object `(o, ko)` misses the 2^15 bytes at `v`. -/
def VcpuApart (v : U64) (o : Fl4Spec.ObjRef) (ko : Fl4Spec.KernelObject) : Prop :=
  o.toNat + 2 ^ Fl4Spec.objBits ko ≤ v.val ∨ v.val + 32768 ≤ o.toNat

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **VM object coverage** (module docstring). -/
structure JVm (V : Set U64) (H : P1.Heap) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  /-- Each `v ∈ V` is a spec VCPU object. -/
  spec : ∀ v ∈ V, ∃ x, σ.kheap v.bv = some (.archObj (.vcpu x))
  /-- Its P1 heap object is `.other 15`. -/
  heap : ∀ v ∈ V, H v = some (.other 15)
  /-- It lies off the kernel-global area `[ksb, ksb + 304384)`. -/
  ks : ∀ v ∈ V, v.val + 32768 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ v.val
  /-- No other spec object meets it (l4v `pspace_distinct` at `V`). -/
  sep : ∀ v ∈ V, ∀ o ko, σ.kheap o = some ko → o ≠ v.bv → VcpuApart v o ko

variable {V V' : Set U64} {H H' : P1.Heap} {s s' : S} {σ σ' : Fl4Spec.State Unit}

theorem JVm.empty : JVm (L := L) ∅ H s σ :=
  ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩

theorem JVm.mono (J : JVm (L := L) V H s σ) (h : V' ⊆ V) : JVm (L := L) V' H s σ :=
  ⟨fun v hv => J.spec v (h hv), fun v hv => J.heap v (h hv), fun v hv => J.ks v (h hv),
    fun v hv => J.sep v (h hv)⟩

/-- **Preservation, general form** (module docstring). -/
theorem JVm.step (J : JVm (L := L) V H s σ) (hV : V' ⊆ V) (hH : ∀ v ∈ V', H' v = H v)
    (hk : L.ksb s' = L.ksb s) (hS : ∀ v ∈ V', ∃ x, σ'.kheap v.bv = some (.archObj (.vcpu x)))
    (hO : ∀ o ko', σ'.kheap o = some ko' →
      (∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko) ∨
        ∀ v ∈ V', o ≠ v.bv → VcpuApart v o ko') :
    JVm (L := L) V' H' s' σ' where
  spec := hS
  heap v hv := (hH v hv).trans (J.heap v (hV hv))
  ks v hv := by rw [hk]; exact J.ks v (hV hv)
  sep v hv o ko' ho hne := by
    rcases hO o ko' ho with ⟨ko, hko, hb⟩ | h
    · unfold VcpuApart; rw [hb]; exact J.sep v (hV hv) o ko hko hne
    · exact h v hv hne

/-- The address of a non-VCPU spec object is no VCPU of `V`. -/
theorem JVm.ne_of (J : JVm (L := L) V H s σ) {p : Fl4Spec.ObjRef} {ko : Fl4Spec.KernelObject}
    (hp : σ.kheap p = some ko) (hnv : ∀ x, ko ≠ .archObj (.vcpu x)) : ∀ v ∈ V, p ≠ v.bv := by
  intro v hv e
  obtain ⟨x, hx⟩ := J.spec v hv
  rw [← e, hp] at hx
  exact hnv x (Option.some.inj hx)

/-- **Same spec heap** (steps writing only FL4 memory, the machine state or the scheduler fields). -/
theorem JVm.ofKheap (J : JVm (L := L) V H s σ) (he : σ'.kheap = σ.kheap) (hk : L.ksb s' = L.ksb s) :
    JVm (L := L) V H s' σ' :=
  J.step (fun _ h => h) (fun _ _ => rfl) hk (fun v hv => by rw [he]; exact J.spec v hv)
    fun o ko' ho => Or.inl ⟨ko', by rw [← he]; exact ho, rfl⟩

/-- **An in-place update of a non-VCPU object keeping its size** (module docstring). -/
theorem JVm.updK (J : JVm (L := L) V H s σ) {p : Fl4Spec.ObjRef} {ko ko' : Fl4Spec.KernelObject}
    (hp : σ.kheap p = some ko) (hnv : ∀ x, ko ≠ .archObj (.vcpu x))
    (hb : Fl4Spec.objBits ko' = Fl4Spec.objBits ko) (hk : L.ksb s' = L.ksb s) :
    JVm (L := L) V H s' (Notif.updK σ p ko') := by
  have hne := J.ne_of hp hnv
  refine J.step (fun _ h => h) (fun _ _ => rfl) hk (fun v hv => ?_) fun o k' ho => ?_
  · rw [Notif.updK_kheap, Function.update_of_ne (Ne.symm (hne v hv))]
    exact J.spec v hv
  · rw [Notif.updK_kheap] at ho
    by_cases hop : o = p
    · subst hop
      rw [Function.update_self] at ho
      exact Or.inl ⟨ko, hp, by rw [← Option.some.inj ho]; exact hb⟩
    · rw [Function.update_of_ne hop] at ho
      exact Or.inl ⟨k', ho, rfl⟩

/-- **Objects removed** (detype): `V` cut to the VCPUs still present (module docstring). -/
theorem JVm.restrict (J : JVm (L := L) V H s σ)
    (hsub : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko) (hk : L.ksb s' = L.ksb s)
    (hH : ∀ v ∈ V, σ'.kheap v.bv ≠ none → H' v = H v) :
    JVm (L := L) {v | v ∈ V ∧ σ'.kheap v.bv ≠ none} H' s' σ' := by
  refine J.step (fun v h => h.1) (fun v hv => hH v hv.1 hv.2) hk (fun v hv => ?_)
    fun o ko' ho => Or.inl ⟨ko', hsub o ko' ho, rfl⟩
  obtain ⟨ko, hko⟩ := Option.ne_none_iff_exists'.mp hv.2
  obtain ⟨x, hx⟩ := J.spec v hv.1
  rw [hsub _ _ hko] at hx
  exact ⟨x, hko.trans hx⟩

/-- **New objects** at addresses empty in `σ`, apart from `V` (retype of non-VCPU objects). -/
theorem JVm.create (J : JVm (L := L) V H s σ)
    (hkeep : ∀ o ko, σ.kheap o = some ko → σ'.kheap o = some ko) (hk : L.ksb s' = L.ksb s)
    (hH : ∀ v ∈ V, H' v = H v)
    (hnew : ∀ o ko', σ'.kheap o = some ko' → σ.kheap o = none → ∀ v ∈ V, VcpuApart v o ko') :
    JVm (L := L) V H' s' σ' := by
  refine J.step (fun _ h => h) hH hk (fun v hv => ?_) fun o ko' ho => ?_
  · obtain ⟨x, hx⟩ := J.spec v hv
    exact ⟨x, hkeep _ _ hx⟩
  · cases h : σ.kheap o with
    | none => exact Or.inr fun v hv _ => hnew o ko' ho h v hv
    | some ko =>
      have := hkeep _ _ h
      rw [ho] at this
      exact Or.inl ⟨ko, rfl, by rw [Option.some.inj this]⟩

/-- An object of a VCPU's type is a VCPU. -/
theorem vcpu_of_aType {x : Fl4Spec.VcpuState} {ko' : Fl4Spec.KernelObject}
    (h : Fl4Spec.aType (.archObj (.vcpu x)) = Fl4Spec.aType ko') : ∃ y, ko' = .archObj (.vcpu y) := by
  cases ko' with
  | archObj ao =>
    cases ao with
    | vcpu y => exact ⟨y, rfl⟩
    | dataPage dev sz => simp only [Fl4Spec.aType, Fl4Spec.aaType] at h; split_ifs at h <;> cases h
    | _ => simp [Fl4Spec.aType, Fl4Spec.aaType] at h
  | cnode sz cs => simp only [Fl4Spec.aType] at h; split_ifs at h <;> cases h
  | schedContext y n => simp only [Fl4Spec.aType] at h; split_ifs at h <;> cases h
  | _ => simp [Fl4Spec.aType] at h

/-- **A step keeping the objects' types** (`KSz`, P3's `NKZ` steps: every object of `σ'` an object of `σ` of the
same type, so of the same size, `objBits_of_aType`) that keeps the VCPUs of `V` present. -/
theorem JVm.ksz (J : JVm (L := L) V H s σ) (hk : KSz σ σ') (hS : ∀ v ∈ V, σ'.kheap v.bv ≠ none)
    (hks : L.ksb s' = L.ksb s) (hH : ∀ v ∈ V, H' v = H v) : JVm (L := L) V H' s' σ' := by
  refine J.step (fun _ h => h) hH hks (fun v hv => ?_) fun o ko' ho => ?_
  · obtain ⟨ko', hko'⟩ := Option.ne_none_iff_exists'.mp (hS v hv)
    obtain ⟨ko, hko, hty⟩ := hk _ _ hko'
    obtain ⟨x, hx⟩ := J.spec v hv
    rw [hx] at hko
    cases hko
    obtain ⟨y, rfl⟩ := vcpu_of_aType hty
    exact ⟨y, hko'⟩
  · obtain ⟨ko, hko, hty⟩ := hk o ko' ho
    exact Or.inl ⟨ko, hko, objBits_of_aType hty.symm⟩

end

/-! ## What `JAtZ` already gives about VCPUs -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- At a `JAtZ` state no TCB is bound to a VCPU (`JExt.vw`). -/
theorem JAtZ.vcpuWord0 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : Z.th t = some .tcb) :
    L.mem s (tVcpuA t) = 0#u64 :=
  J.ext.vw t ht

/-- The current thread's VCPU word is 0 at a `JAtZ` state. -/
theorem JAtZ.curVcpu0 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    L.mem s (tVcpuA (L.curW s)) = 0#u64 :=
  J.ext.vw _ J.kern.curT

/-- A spec VCPU is an `H` object `other n`, `12 ≤ n ≤ 15` (`SpecCover.arch`, `ArchFitHyp`): `JVm.heap` pins
`n = 15`. -/
theorem JAtZ.vcpuH (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {o : Fl4Spec.ObjRef} {x}
    (ho : σ.kheap o = some (.archObj (.vcpu x))) : ∃ n, 12 ≤ n ∧ n ≤ 15 ∧ H ⟨o⟩ = some (.other n) := by
  obtain ⟨n, hn, hH⟩ := J.cover.arch _ _ ho
  exact ⟨n, hn, J.carry.archFit _ _ _ ho hH, hH⟩

end

end

end Fl4Proofs.P3
