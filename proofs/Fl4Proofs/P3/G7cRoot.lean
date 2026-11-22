/-
P3 (DESIGN.md §9), scheduler, g7c (KENTRY-PLAN g7c (a)): **the CR3 of a
thread switch, on both sides**.

* Spec: `switchToThread t σ = {σ'}` (resp. `switchToIdleThread`) ends with
  the CR3 that `setVmRoot t σ` (resp. of the idle thread) writes
  (`switchToThread_cr3`, `switchToIdleThread_cr3`): `lazyFpuRestore`, the
  dequeue and the `curThread` write keep it (`CRK`).
* FL4: `set_vm_root t` (`set_vm_root_ar`) and `set_kernel_vm_root`
  (`set_kernel_vm_root_ar`) give `AR` at the CR3 the spec's `setVmRoot`
  writes at every spec state with the same heap, ASID table and global PML4,
  from `ArchRefines` [P] (A15: `set_vspace` yields `makeCr3`, state-free under
  `AR`), the vtable correspondence (`StateRel.tcb`'s slot 1), `VsRel` and
  `KRootRel`. VsRoot's `set_vm_root_rel` with the arch relation `AR` alone
  (no `SR` over spec states).
* The idle thread: FL4 switches to the kernel root; the spec's `setVmRoot
  idle` agrees when the idle TCB's vtable is not a mapped PML4 cap
  (`setVmRoot_idle`; `IdleVt` [J] in the module using it).
-/
import Fl4Proofs.P3.G7cCr3K
import Fl4Proofs.P3.VsArch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3 Classical

noncomputable section

section Spec
open Fl4Spec

theorem fk_mem {β α : Type} {f : State Unit → β} {m : NonDet (State Unit) α} (h : FK f m) {σ : State Unit}
    {y : α × State Unit} (hy : y ∈ (m σ).1) : f y.2 = f σ := h σ y hy

/-- **The spec's `archSwitchToThread`**: the CR3 `setVmRoot` writes. -/
theorem archSwitch_cr3 {σ : State Unit} {t : ObjRef} {c : Cr3}
    (hv : setVmRoot (Z := Unit) t σ = ({((), cr3Upd σ c)}, False)) {y : Unit × State Unit}
    (hy : y ∈ (archSwitchToThread (Z := Unit) t σ).1) : crF y.2 = crF (cr3Upd σ c) := by
  unfold archSwitchToThread at hy
  rw [nd_bind_one hv] at hy
  exact fk_mem (crk_lazyFpuRestore t) hy

/-- **The spec's `switchToThread`**: the CR3 `setVmRoot t` writes. -/
theorem switchToThread_cr3 {σ σ' : State Unit} {t : ObjRef} {c : Cr3}
    (hv : setVmRoot (Z := Unit) t σ = ({((), cr3Upd σ c)}, False))
    (h : switchToThread (Z := Unit) t σ = ({((), σ')}, False)) : σ'.archState.x64CurrentCr3 = c := by
  have hy : ((), σ') ∈ (switchToThread (Z := Unit) t σ).1 := by rw [h]; exact Set.mem_singleton _
  unfold switchToThread at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  have e1 : z1.2 = σ := fk_mem (f := id) dk_get hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  have e2 : z2.2 = z1.2 := fk_mem (f := id) (dk_assert _) hz2
  obtain ⟨z3, hz3, hy⟩ := hy
  rw [e2, e1] at hz3
  have e3 := archSwitch_cr3 hv hz3
  obtain ⟨z4, hz4, hy⟩ := hy
  have e4 := fk_mem (crk_tcbSchedAction' _ _) hz4
  have e5 : crF σ' = crF z4.2 := fk_mem (dk_modify (f := crF) (fun _ => rfl)) hy
  have := (e5.trans (e4.trans e3))
  exact congrArg Prod.fst this

/-- **The spec's `switchToIdleThread`**: the CR3 `setVmRoot idle` writes. -/
theorem switchToIdleThread_cr3 {σ σ' : State Unit} {c : Cr3}
    (hv : setVmRoot (Z := Unit) σ.idleThread σ = ({((), cr3Upd σ c)}, False))
    (h : switchToIdleThread (Z := Unit) σ = ({((), σ')}, False)) : σ'.archState.x64CurrentCr3 = c := by
  have hy : ((), σ') ∈ (switchToIdleThread (Z := Unit) σ).1 := by rw [h]; exact Set.mem_singleton _
  unfold switchToIdleThread at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain ⟨rfl⟩ : z1 = (σ.idleThread, σ) := hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  unfold archSwitchToIdleThread at hz2
  obtain ⟨z3, hz3, hz2⟩ := hz2
  obtain ⟨rfl⟩ : z3 = (σ.idleThread, σ) := hz3
  change z2 ∈ (setVmRoot (Z := Unit) σ.idleThread σ).1 at hz2
  rw [hv] at hz2
  obtain ⟨rfl⟩ : z2 = ((), cr3Upd σ c) := hz2
  have e5 : crF σ' = crF (cr3Upd σ c) := fk_mem (dk_modify (f := crF) (fun _ => rfl)) hy
  exact congrArg Prod.fst e5

/-- A cap that is no mapped PML4 cap gives a vtable `setVmRoot` ignores. -/
theorem absCap_not_pml4 {cp : capability.Cap} (h : ∀ p asid, cp ≠ .Pml4 p true asid) :
    ∀ p asid, absCap cp ≠ .archObjectCap (.pml4Cap p (some asid)) := by
  intro p asid
  cases cp with
  | Pml4 q b a =>
    cases b with
    | false => simp [absCap]
    | true => exact absurd rfl (h q a)
  | _ => simp [absCap]

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {ar : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`set_kernel_vm_root` gives `AR` at the global CR3** (`ArchRefines`,
`KRootRel`). -/
theorem set_kernel_vm_root_ar (hRef : ArchRefines ar AR) (s : S) (a : A) (σ : Fl4Spec.State Unit) {c0 : Fl4Spec.Cr3}
    (hKr : KRootRel (L.mem s) (L.ksb s) σ) (hA : AR a c0) :
    vspace.set_kernel_vm_root st ar s a ⦃ r => r.1 = s ∧ AR r.2 (globCr3 σ) ⦄ := by
  unfold vspace.set_kernel_vm_root
  rw [kernel_root_eq]
  apply ok_bind_spec
  refine WP.spec_bind (hRef.setVspace a _ _ 0#u64 hA) fun a' h => (WP.spec_ok _).2 ⟨rfl, ?_⟩
  unfold KRootRel at hKr
  rw [← hKr]; exact h

/-- **`set_vm_root t` gives `AR` at the CR3 the spec's `setVmRoot t`
writes** (module docstring). -/
theorem set_vm_root_ar (hRef : ArchRefines ar AR) {P : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    {c0 : Fl4Spec.Cr3} (hA : AR a c0) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hKr : KRootRel (L.mem s) (L.ksb s) σ)
    {t : U64} {x : Fl4Spec.Tcb} (hkx : σ.kheap t.bv = some (.tcb x)) {cp : capability.Cap}
    (hc' : capAt (L.mem s) (slotOf t 1) = ok cp) (hv : x.tcbVtable = absCap cp)
    (hasid : ∀ p asid, cp = .Pml4 p true asid → asid ≠ 0#u64) :
    vspace.set_vm_root st ar s a t ⦃ r => r.1 = s ∧ ∃ c : Fl4Spec.Cr3,
      (∀ σ' : Fl4Spec.State Unit, σ'.kheap = σ.kheap → σ'.archState.x64AsidTable = σ.archState.x64AsidTable →
        σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 →
        Fl4Spec.setVmRoot (Z := Unit) t.bv σ' = ({((), cr3Upd σ' c)}, False)) ∧ AR r.2 c ⦄ := by
  have hgl : ∀ σ' : Fl4Spec.State Unit, σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 →
      globCr3 σ' = globCr3 σ := fun σ' h => by unfold globCr3; rw [h]
  have kern : (∀ p asid, x.tcbVtable ≠ .archObjectCap (.pml4Cap p (some asid))) →
      vspace.set_kernel_vm_root st ar s a ⦃ r => r.1 = s ∧ ∃ c : Fl4Spec.Cr3,
        (∀ σ' : Fl4Spec.State Unit, σ'.kheap = σ.kheap → σ'.archState.x64AsidTable = σ.archState.x64AsidTable →
          σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 →
          Fl4Spec.setVmRoot (Z := Unit) t.bv σ' = ({((), cr3Upd σ' c)}, False)) ∧ AR r.2 c ⦄ := fun hv' =>
    WP.spec_mono (set_kernel_vm_root_ar hRef s a σ hKr hA) fun r ⟨h1, h2⟩ => ⟨h1, globCr3 σ, fun σ' hk _ hg => by
      rw [setVmRoot_other (show σ'.kheap t.bv = _ by rw [hk]; exact hkx) hv', hgl σ' hg], h2⟩
  have hVs : ∀ σ' : Fl4Spec.State Unit, σ'.kheap = σ.kheap → σ'.archState.x64AsidTable = σ.archState.x64AsidTable →
      VsRel P (L.mem s) (L.ksb s) σ' := fun σ' hk ha =>
    hR.frame (fun _ _ => rfl) ha (fun p _ => by rw [hk])
  unfold vspace.set_vm_root
  rw [tcb_slot_vtable]
  apply ok_bind_spec
  rw [slot_cap_eq, hc']
  apply ok_bind_spec
  cases cp with
  | Pml4 ptr b asid =>
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact kern (by rw [hv]; simp [absCap])
    | true =>
      simp only [↓reduceIte]
      have hv1 : x.tcbVtable = .archObjectCap (.pml4Cap ptr.bv (some asid.bv)) := by rw [hv]; rfl
      refine WP.spec_bind (find_vspace_for_asid_all (P := P) s asid (hasid ptr asid rfl)) ?_
      rintro r hr
      cases r with
      | Ok r1 =>
        dsimp only
        by_cases hpr : r1 = ptr
        · subst hpr
          simp only [↓reduceIte]
          refine WP.spec_bind (hRef.setVspace a c0 r1 asid hA) fun a1 h =>
            (WP.spec_ok _).2 ⟨rfl, _, fun σ' hk ha _ => ?_, h⟩
          rw [setVmRoot_mapped (show σ'.kheap t.bv = _ by rw [hk]; exact hkx) hv1 (hr σ' (hVs σ' hk ha))]
          simp [rootCr3, fvRes]
        · simp only [hpr, ↓reduceIte]
          refine WP.spec_mono (set_kernel_vm_root_ar hRef s a σ hKr hA) fun r ⟨h1, h2⟩ =>
            ⟨h1, globCr3 σ, fun σ' hk ha hg => ?_, h2⟩
          rw [setVmRoot_mapped (show σ'.kheap t.bv = _ by rw [hk]; exact hkx) hv1 (hr σ' (hVs σ' hk ha))]
          have hne : ptr.bv ≠ r1.bv := fun h => hpr (eq_of_bv h).symm
          simp only [rootCr3, fvRes, hne, ↓reduceIte]
          rw [hgl σ' hg]
      | Err e =>
        dsimp only
        refine WP.spec_mono (set_kernel_vm_root_ar hRef s a σ hKr hA) fun r ⟨h1, h2⟩ =>
          ⟨h1, globCr3 σ, fun σ' hk ha hg => ?_, h2⟩
        rw [setVmRoot_mapped (show σ'.kheap t.bv = _ by rw [hk]; exact hkx) hv1 (hr σ' (hVs σ' hk ha))]
        simp only [rootCr3, fvRes]
        rw [hgl σ' hg]
  | _ => exact kern (by rw [hv]; simp [absCap])

end

end

end Fl4Proofs.P3.Vs
