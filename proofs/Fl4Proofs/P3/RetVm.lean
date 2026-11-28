/-
P3 (line mmuAD, gen 42b25): **`VmEptState` across a native retype that adds no typed-heap object** — the Architect's
ruling (2026-11-28 18:08Z) item 3 (h) for the types 0, 2, 3, 5..13 (no TCB: 1, no CNode: 4; `thKindN nt us = none`,
so the typed heap is unchanged, UntypedFrameBase's `ThX`): `V`, `X`, `XL` unchanged.

* **`VcpuCore.ofRet`**: from `JAtZB` and `VcpuCore V` at the entry state, the window the body wrote (`RetWin` at the
  footprint `W`) with `RetFootV V th s W` (P3/RetFoot), the window apart from every VCPU of `V` (`hVw`; RAM windows:
  **`JAtZB.winV`**), the type not a VCPU: `VcpuCore V` after. The VCPU objects' words, the list head, the TCBs'
  `VCPU` and state words are outside the footprint; the slot caps after are old ones, the window's (`capsOf`: no
  `Vcpu` / `IoPort` cap, **`capsOf_vtx`**) or the source untyped's; the spec adds no VCPU object
  (**`defaultObject_vcpu`**) and keeps each one of `V` (`SpecAdd.kold`, `KeepC`); `RngOne` by `mdbStep_rngOne`; `JVm`
  by `JVm.step` (P1's heap keeps the VCPUs, `hout_old`; a new spec object lies in its window slot, `hob`, `hfit`).
* **`EptCore.ofRet`**: P3/EptRetype's `EptCore.growSZ` at `T = ∅`, with `RetFootE X W`, the window apart from the
  tables (`hXw`; RAM windows: **`JAtZB.winX`**): the `Ept` and EPT-mapped frame caps after are old ones (the window's
  native caps are neither, **`newCapOf_ept`**), the old `Ept` caps kept (`RetExp.keep`), no table or ASID pool added
  (**`defaultObject_native`**), the ASID table kept (`SpecAdd`, `cnK_asid`), a TCB's `SLOT_EPT` no window slot (a
  window slot is a CNode slot, `slotOf_inj`), `EptNamed` by `EptNamed.frameA`.
* **`VmEptState.ofRet`** (both), **`VmEptState.ofPost`**: from a body's `UtBodyPostB` (the spec's run, `Ok`, and
  `VmEptState V X XL` after).

Not covered: TCBs (1) and CNodes (4) (new typed-heap objects: new TCBs' `VCPU` / state words and slots, new CNode
slots), the VCPU (14), the EPT tables 15..18 (`X` grows: `growSZ` at the window).

No named premise. No `sorry`; only the three standard axioms.
-/
import Fl4Proofs.P3.RetFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- The spec's new object is a VCPU only for the VCPU type. -/
theorem defaultObject_vcpu {t : Fl4Spec.ApiObjectType} {dev : Bool} {us : Nat} {d : Fl4Spec.Domain}
    {vs : Fl4Spec.VcpuState} (ht : t ≠ .untyped) (h : Fl4Spec.defaultObject t dev us d = .archObj (.vcpu vs)) :
    t = .archObject .vcpuObj := by
  cases t with
  | archObject a => cases a <;> first | rfl | exact absurd h (fun h' => by cases h')
  | untyped => exact absurd rfl ht
  | _ => exact absurd h (fun h' => by cases h')

/-- **A native window cap** (`newCapOf`) is no `Vcpu`, `IoPort` or `Ept` cap and no mapped frame cap, and names
no EPT table (`EptCapX`). -/
theorem newCapOf_vtx (n : Nat) (base us : U64) (dev : Bool) (X : Set U64) :
    (∀ p, newCapOf n base us dev ≠ .Vcpu p) ∧ (∀ f l o, newCapOf n base us dev ≠ .IoPort f l o) ∧
    EptCapX X (newCapOf n base us dev) ∧ (∀ p l m a v, newCapOf n base us dev ≠ .Ept p l m a v) ∧
    (∀ p sz r d e a v, newCapOf n base us dev ≠ .Frame p sz r d true e a v) := by
  unfold newCapOf
  by_cases h2 : n = 2
  · rw [if_pos h2]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h), by first | trivial | exact fun h => absurd h.1 (by decide),
      fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h)⟩
  rw [if_neg h2]
  by_cases h3 : n = 3
  · rw [if_pos h3]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h), by first | trivial | exact fun h => absurd h.1 (by decide),
      fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h)⟩
  rw [if_neg h3]
  by_cases h4 : n = 4
  · rw [if_pos h4]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h), by first | trivial | exact fun h => absurd h.1 (by decide),
      fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h)⟩
  rw [if_neg h4]
  by_cases h0 : n = 0
  · rw [if_pos h0]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h), by first | trivial | exact fun h => absurd h.1 (by decide),
      fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h)⟩
  rw [if_neg h0]
  by_cases h5 : n = 5
  · rw [if_pos h5]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h), by first | trivial | exact fun h => absurd h.1 (by decide),
      fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h)⟩
  rw [if_neg h5]
  by_cases h1 : n = 1
  · rw [if_pos h1]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h), by first | trivial | exact fun h => absurd h.1 (by decide),
      fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h)⟩
  rw [if_neg h1]
  by_cases h7 : n = 7
  · rw [if_pos h7]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h), by first | trivial | exact fun h => absurd h.1 (by decide),
      fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h)⟩
  rw [if_neg h7]
  by_cases h8 : n = 8
  · rw [if_pos h8]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h), by first | trivial | exact fun h => absurd h.1 (by decide),
      fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h)⟩
  rw [if_neg h8]
  by_cases h9 : n = 9
  · rw [if_pos h9]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h), by first | trivial | exact fun h => absurd h.1 (by decide),
      fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h)⟩
  rw [if_neg h9]
  by_cases h10 : n = 10
  · rw [if_pos h10]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h), by first | trivial | exact fun h => absurd h.1 (by decide),
      fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h)⟩
  rw [if_neg h10]
  by_cases h11 : n = 11
  · rw [if_pos h11]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h), by first | trivial | exact fun h => absurd h.1 (by decide),
      fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h)⟩
  rw [if_neg h11]
  by_cases h12 : n = 12
  · rw [if_pos h12]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h), by first | trivial | exact fun h => absurd h.1 (by decide),
      fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h)⟩
  rw [if_neg h12]
  by_cases h13 : n = 13
  · rw [if_pos h13]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h), by first | trivial | exact fun h => absurd h.1 (by decide),
      fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h)⟩
  rw [if_neg h13]
  exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h), by first | trivial | exact fun h => absurd h.1 (by decide),
      fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h)⟩

/-- A retype's window cap of a type other than the VCPU is no `Vcpu` cap and no `IoPort` cap. -/
theorem capsOf_vtx {n : Nat} (hn : n ≠ 14) (us : U64) (dev : Bool) (A k j : Nat) :
    (∀ p, capsOf n us dev A k j ≠ .Vcpu p) ∧ (∀ f l o, capsOf n us dev A k j ≠ .IoPort f l o) := by
  unfold capsOf
  rw [if_neg hn]
  by_cases h15 : 15 ≤ n ∧ n ≤ 18
  · rw [if_pos h15]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
  · rw [if_neg h15]
    exact ⟨(newCapOf_vtx n _ us dev ∅).1, (newCapOf_vtx n _ us dev ∅).2.1⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V : Set U64}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **A RAM window is apart from the VCPUs** (module docstring). -/
theorem JAtZB.winV (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ)
    {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    {lo hi : Nat} (h1 : p.val + fi.val ≤ lo) (h2 : hi ≤ p.val + 2 ^ sb.val) :
    ∀ v ∈ V, v.val + 32768 ≤ lo ∨ hi ≤ v.val := by
  intro v hv
  obtain ⟨x, hx⟩ := Jv.spec v hv
  have h := (B.winFree hAs hcap h1 h2).1 _ _ hx
  have e : (2 : Nat) ^ Fl4Spec.objBits (.archObj (.vcpu x)) = 32768 := by
    simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]
  have hv' : v.bv.toNat = v.val := rfl
  rw [e, hv'] at h
  exact h

set_option maxHeartbeats 4000000 in
/-- **`VcpuCore` across a retype adding no typed-heap object** (module docstring). -/
theorem VcpuCore.ofRet (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ)
    {Z' : XSets} {H' : P1.Heap} {s' : S} {σ' : Fl4Spec.State Unit}
    {W : U64 → Prop} {xs : U64} {nt : Nat} {t : Fl4Spec.ApiObjectType} {us : Nat} {rb : Fl4Spec.ObjRef}
    {w : Nat} {dev : Bool}
    (R : RetWin (L := L) Z.th Z'.th Z.G Z'.G H H' σ σ' s s' W xs nt t us rb w dev)
    (hF : RetFootV (L := L) V Z.th s W) (hn : thKindN nt us = none) (hn14 : nt ≠ 14)
    (ht : t ≠ .archObject .vcpuObj)
    (hVw : ∀ v ∈ V, v.val + 32768 ≤ rb.toNat ∨ rb.toNat + w * 2 ^ zOf nt us ≤ v.val)
    (hob : Fl4Spec.objBits (Fl4Spec.defaultObject t dev us σ.curDomain) ≤ zOf nt us)
    (hfit : rb.toNat + w * 2 ^ zOf nt us ≤ 2 ^ 64) :
    VcpuCore (L := L) V Z' H' s' σ' := by
  obtain ⟨k, dslot, cj, hk, -, ⟨uu, -, hcj⟩, hcw, -, hw, hThX, hSt, -, hcaps, hout, ⟨σB, hA, -, hkc⟩, -, -⟩ := R
  subst hk
  have hth : Z'.th = Z.th := funext fun q => by rw [hThX.1 q, hn]; simp
  have Ly := B.jvLay C.vm
  have Pw := B.jwPl C.vm
  have nV : ∀ u ∈ V, ∀ b, W b → b.val < u.val ∨ u.val + 32768 ≤ b.val := fun u hu b hb => (hF b hb).1 u hu
  have kTV : ∀ t, Z.th t = some .tcb → L.mem s' (tVcpuA t) = L.mem s (tVcpuA t) := fun t ht =>
    hw.mem_eq (Pw.jw _ (Or.inr (Or.inl ⟨t, ht, rfl⟩))) fun hb => ((hF _ hb).2.2 t ht).1 rfl
  have kSt : ∀ t, Z.th t = some .tcb → L.mem s' (P1.stA t) = L.mem s (P1.stA t) := fun t ht =>
    hw.mem_eq (Pw.sw _ ⟨t, ht, rfl⟩) fun hb => ((hF _ hb).2.2 t ht).2 rfl
  have kVT : ∀ v ∈ V, L.mem s' (vTcbA v) = L.mem s (vTcbA v) := fun v hv =>
    hw.mem_eq (Pw.jw _ (Or.inr (Or.inr ⟨v, hv, rfl⟩))) fun hb => by
      have e := lay_vTcb_val (Ly.vfit v hv).2
      rcases nV v hv _ hb with h | h <;> omega
  -- the spec: no VCPU added, each of `V` kept
  have hvk : ∀ u ∈ V, σ'.kheap u.bv = σ.kheap u.bv := fun u hu => by
    obtain ⟨x, hx⟩ := C.vm.spec u hu
    have hB := hA.kold hx
    rcases hkc u.bv with e | ⟨r, cs, cs', e1, -⟩
    · rw [e, hB, hx]
    · rw [hB] at e1; cases e1
  have hnv : ∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
      σ.kheap p = some (.archObj (.vcpu vs)) := by
    intro p vs hp
    have hpB : σB.kheap p = some (.archObj (.vcpu vs)) := by
      rcases hkc p with e | ⟨r, cs, cs', -, e2⟩
      · rw [← e]; exact hp
      · rw [hp] at e2; cases e2
    rcases hA.kback hpB with h | ⟨⟨-, htu⟩, h⟩
    · exact h
    · exact absurd (defaultObject_vcpu htu h.symm) ht
  -- the slot caps after
  have hcap' : ∀ y, IsSlot Z.th y → capV (L.mem s') y = .Null ∨
      ((∀ p, capV (L.mem s') y ≠ .Vcpu p) ∧ (∀ f l o, capV (L.mem s') y ≠ .IoPort f l o)) ∨
      capV (L.mem s') y = capV (L.mem s) y := by
    intro y hy
    by_cases h0 : capV (L.mem s') y = .Null
    · exact Or.inl h0
    rcases hcaps y (by rw [hth]; exact hy) h0 with ⟨j, hj, rfl⟩ | ⟨-, e | ⟨-, p0, sb0, fi0, fi1, d0, -, e⟩⟩
    · right; left; rw [hcw j hj, hcj]; exact capsOf_vtx hn14 uu dev rb.toNat _ j
    · exact Or.inr (Or.inr e)
    · right; left; rw [e]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
  have E' : JExtVcpu (L := L) V Z'.th s' := by
    rw [hth]
    refine ⟨fun y hy => ?_, fun t ht => ?_, fun v hv => ?_, C.extv.nz⟩
    · rcases hcap' y hy with h | ⟨h, -⟩ | h
      · rw [h]; trivial
      · cases e : capV (L.mem s') y <;> first | trivial | exact absurd e (h _)
      · rw [h]; exact C.extv.cap y hy
    · rw [kTV t ht]
      rcases C.extv.bnd t ht with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, by rw [kVT _ h1]; exact h2⟩
    · rw [kVT v hv]
      rcases C.extv.back v hv with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, by rw [kTV _ h1]; exact h2⟩
  have hNI : NoIoTcb Z'.th (L.mem s') := by
    rw [hth]
    intro y hy f l o h
    rcases hcap' y (isSlot_thTcb hy) with h0 | ⟨-, h0⟩ | h0
    · rw [h0] at h; cases h
    · exact absurd h (h0 f l o)
    · rw [h0] at h; exact C.noIoTcb y hy f l o h
  have R' : RunVmB (L := L) Z'.th s' := by
    rw [hth]
    intro t ht h8
    rw [kTV t ht]
    exact C.rvm t ht (by rw [← kSt t ht]; exact h8)
  have hk1 : 1 ≤ 2 ^ zOf nt us := Nat.one_le_two_pow
  have Jv' : JVm (L := L) V H' s' σ' := by
    refine C.vm.step (fun _ h => h) (fun v hv => ?_) hw.1 (fun u hu => by rw [hvk u hu]; exact C.vm.spec u hu)
      (fun o ko' ho => ?_)
    · have e := hout_old hout rfl rfl hk1 (C.vm.heap v hv) (by
        simp only [P1.HKind.bits, Nat.reducePow]; exact hVw v hv)
      rw [e, C.vm.heap v hv]
    · have hB : ∃ ko0, σB.kheap o = some ko0 ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko0 := by
        rcases hkc o with e | ⟨r, cs, cs', e1, e2⟩
        · exact ⟨ko', by rw [← e]; exact ho, rfl⟩
        · rw [ho] at e2; cases e2; exact ⟨_, e1, by simp [Fl4Spec.objBits]⟩
      obtain ⟨ko0, hk0, hb0⟩ := hB
      rcases hA.kback hk0 with h | ⟨⟨hq, -⟩, hko⟩
      · exact Or.inl ⟨ko0, h, hb0⟩
      · right
        intro v hv _
        obtain ⟨j, hj, rfl⟩ := regionPtrs_mem hq
        have hjk : (j + 1) * 2 ^ zOf nt us ≤ w * 2 ^ zOf nt us := Nat.mul_le_mul_right _ hj
        rw [Nat.add_mul, Nat.one_mul] at hjk
        have e := ptrAdd_toNat (rb := rb) (n := j * 2 ^ zOf nt us) (by omega)
        have hko' : Fl4Spec.objBits ko0 = Fl4Spec.objBits (Fl4Spec.defaultObject t dev us σ.curDomain) := by
          rw [hko]
        have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) hob
        unfold VcpuApart
        rw [hb0, hko', e]
        rcases hVw v hv with h | h <;> omega
  have Vl' : VList st V Z'.th s' := by
    rw [hth]
    exact C.vl.writes hw fun b hb => by
      refine ⟨C.vl.lw_al Ly.vfit hb, fun hW => ?_⟩
      rcases hb with rfl | ⟨u, hu, rfl | rfl⟩
      · exact (hF _ hW).2.1 (by unfold P1.vHeadA; first | rfl | rw [hw.1])
      · have := lay_next_val (Ly.vfit u hu).2
        rcases nV u hu _ hW with h | h <;> omega
      · have := lay_prev_val (Ly.vfit u hu).2
        rcases nV u hu _ hW with h | h <;> omega
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := B.xtop.rel
  exact ⟨E', C.vo.frame hnv,
    C.vr.frame (fun u _ vs hu => hnv _ vs hu) (v3_agreeW (L := L) hw (fun u hu => (Ly.vfit u hu).2) nV),
    hNI, (VirtRngOne.mdbStep_rngOne hSt B.ut C.rngOne).2, R', Jv', Vl', C.vb.ofV hvk kVT⟩

end

end

/-- The spec's new object of a native type other than the untyped is no EPT table, no ASID pool, no VCPU. -/
theorem defaultObject_native {n : Nat} {t : Fl4Spec.ApiObjectType} (hty : objTypeOf n = some t) (hn : n ≤ 13)
    (htu : t ≠ .untyped) (dev : Bool) (us : Nat) (d : Fl4Spec.Domain) :
    (∀ l es, Fl4Spec.defaultObject t dev us d ≠ .archObj (.ept l es)) ∧
    (∀ f, Fl4Spec.defaultObject t dev us d ≠ .archObj (.asidPool f)) := by
  interval_cases n <;> simp [objTypeOf, Fl4Spec.archDataToObjType] at hty <;> subst hty <;>
    first | exact absurd rfl htu | exact ⟨fun l es h => (by cases h), fun f h => (by cases h)⟩

/-- A native window cap (`newCapOf`) is no `Ept` cap and no mapped frame cap, and names no EPT table. -/
theorem newCapOf_ept (n : Nat) (base us : U64) (dev : Bool) (X : Set U64) :
    EptCapX X (newCapOf n base us dev) ∧ (∀ p l m a v, newCapOf n base us dev ≠ .Ept p l m a v) ∧
    (∀ p sz r d e a v, newCapOf n base us dev ≠ .Frame p sz r d true e a v) :=
  ⟨(newCapOf_vtx n base us dev X).2.2.1, (newCapOf_vtx n base us dev X).2.2.2.1,
    (newCapOf_vtx n base us dev X).2.2.2.2⟩

/-- The type of a native type number is not the VCPU. -/
theorem objTypeOf_ne_vcpu {n : Nat} {t : Fl4Spec.ApiObjectType} (hty : objTypeOf n = some t) (hn : n ≤ 13) :
    t ≠ .archObject .vcpuObj := fun e => by
  subst e
  have := Sched.objTypeOf_inj hty (show objTypeOf 14 = some (.archObject .vcpuObj) by
    simp [objTypeOf, Fl4Spec.archDataToObjType])
  omega

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **A RAM window is apart from the tables of `X`** (P3/RetFoot's `JAtZB.winFree`). -/
theorem JAtZB.winX (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    {lo hi : Nat} (h1 : p.val + fi.val ≤ lo) (h2 : hi ≤ p.val + 2 ^ sb.val) :
    ∀ u ∈ X, u.val + 4096 ≤ lo ∨ hi ≤ u.val := by
  intro u hu
  obtain ⟨es, hk, -⟩ := C.rel.obj u hu
  have h := (B.winFree hAs hcap h1 h2).1 _ _ hk
  have e : (2 : Nat) ^ Fl4Spec.objBits (.archObj (.ept (XL u) es)) = 4096 := by rw [ept_bits]; rfl
  have hu' : u.bv.toNat = u.val := rfl
  rw [e, hu'] at h
  exact h

set_option maxHeartbeats 4000000 in
/-- **`EptCore` across a native retype adding no typed-heap object** (module docstring): `X`, `XL` unchanged. -/
theorem EptCore.ofRet (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    {Z' : XSets} {H' : P1.Heap} {s' : S} {σ' : Fl4Spec.State Unit}
    {W : U64 → Prop} {xs : U64} {nt : Nat} {t : Fl4Spec.ApiObjectType} {us : Nat} {rb : Fl4Spec.ObjRef}
    {w : Nat} {dev : Bool}
    (R : RetWin (L := L) Z.th Z'.th Z.G Z'.G H H' σ σ' s s' W xs nt t us rb w dev)
    (hF : RetFootE X W) (hn : thKindN nt us = none) (hty : objTypeOf nt = some t) (hn13 : nt ≤ 13)
    (hXw : ∀ u ∈ X, u.val + 4096 ≤ rb.toNat ∨ rb.toNat + w * 2 ^ zOf nt us ≤ u.val)
    (hob : Fl4Spec.objBits (Fl4Spec.defaultObject t dev us σ.curDomain) ≤ zOf nt us)
    (hfit : rb.toNat + w * 2 ^ zOf nt us ≤ 2 ^ 64) :
    EptCore (L := L) X XL Z'.th s' σ' := by
  obtain ⟨k, dslot, cj, hk, -, ⟨uu, -, hcj⟩, hcw, hdsC, hw, hThX, -, hE, hcaps, -, ⟨σB, hA, hcnk, hkc⟩, -, -⟩ := R
  subst hk
  have hth : Z'.th = Z.th := funext fun q => by rw [hThX.1 q, hn]; simp
  rw [hth] at hcaps ⊢
  rw [capsOf_native (Or.inl (by omega))] at hcj
  obtain ⟨hP, ⟨-, -, hM, -, -⟩, -⟩ := B.xtop.rel
  have hk1 : 1 ≤ 2 ^ zOf nt us := Nat.one_le_two_pow
  have hwin : ∀ j, j < w → capV (L.mem s') (dslot j) = newCapOf nt ⟨BitVec.ofNat 64 (rb.toNat + j * 2 ^ zOf nt us)⟩ uu dev :=
    fun j hj => by rw [hcw j hj, hcj]; rfl
  -- the `Ept` and mapped frame caps after are old ones; the old `Ept` caps are kept
  have cE : ∀ y, IsSlot Z.th y → ∀ p l (mm : Bool) a v, capV (L.mem s') y = .Ept p l mm a v →
      capV (L.mem s) y = .Ept p l mm a v := by
    intro y hy p l mm a v h
    rcases hcaps y hy (by rw [h]; exact fun e => by cases e) with ⟨j, hj, rfl⟩ | ⟨-, e | ⟨-, p0, sb0, fi0, fi1, d0, -, e⟩⟩
    · rw [hwin j hj] at h; exact absurd h ((newCapOf_ept _ _ _ _ X).2.1 _ _ _ _ _)
    · rw [← e]; exact h
    · rw [e] at h; cases h
  have cF : ∀ y, IsSlot Z.th y → ∀ p sz r d (e : Bool) a v, capV (L.mem s') y = .Frame p sz r d true e a v →
      capV (L.mem s) y = .Frame p sz r d true e a v := by
    intro y hy p sz r d e a v h
    rcases hcaps y hy (by rw [h]; exact fun e => by cases e) with ⟨j, hj, rfl⟩ | ⟨-, e' | ⟨-, p0, sb0, fi0, fi1, d0, -, e'⟩⟩
    · rw [hwin j hj] at h; exact absurd h ((newCapOf_ept _ _ _ _ X).2.2 _ _ _ _ _ _ _)
    · rw [← e']; exact h
    · rw [e'] at h; cases h
  have cK : ∀ y, IsSlot Z.th y → ∀ p l (mm : Bool) a v, capV (L.mem s) y = .Ept p l mm a v →
      capV (L.mem s') y = .Ept p l mm a v := by
    intro y hy p l mm a v h
    have hm : y ∈ Z.G.chains.flatten := (hM.members y).2 ⟨hy, _, capAt_capV _ y, by rw [h]; exact fun e => by cases e⟩
    exact (hE.keep y hm (by rw [h]; rfl)).2.trans h
  have cX : ∀ y, IsSlot Z.th y → EptCapX X (capV (L.mem s') y) := by
    intro y hy
    by_cases h0 : capV (L.mem s') y = .Null
    · rw [h0]; trivial
    rcases hcaps y hy h0 with ⟨j, hj, rfl⟩ | ⟨-, e | ⟨-, p0, sb0, fi0, fi1, d0, -, e⟩⟩
    · rw [hwin j hj]; exact (newCapOf_ept _ _ _ _ X).1
    · rw [e]; exact C.exte.cap y hy
    · rw [e]; trivial
  -- the spec: no table or pool added, the archState kept
  have hobjA : ∀ r ao, σ'.kheap r = some (.archObj ao) → σB.kheap r = some (.archObj ao) := fun r ao h => by
    rcases hkc r with e | ⟨_, _, _, -, e2⟩
    · rw [← e]; exact h
    · rw [h] at e2; cases e2
  have hobj : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) → σ.kheap r = some (.archObj (.ept l es)) :=
    fun r l es h => by
      rcases hA.kback (hobjA r _ h) with h' | ⟨⟨-, htu⟩, h'⟩
      · exact h'
      · exact absurd h'.symm ((defaultObject_native hty hn13 htu dev us _).1 l es)
  have hpoolO : ∀ r f, σ'.kheap r = some (.archObj (.asidPool f)) → σ.kheap r = some (.archObj (.asidPool f)) :=
    fun r f h => by
      rcases hA.kback (hobjA r _ h) with h' | ⟨⟨-, htu⟩, h'⟩
      · exact h'
      · exact absurd h'.symm ((defaultObject_native hty hn13 htu dev us _).2 f)
  have eB : σB.archState = σ.archState := by
    have := congrArg Fl4Spec.AbstractState.archState hA.abs; exact this
  have hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable := by
    rw [cnK_asid hcnk, eB]
  have hxk : ∀ u ∈ X, σ'.kheap u.bv = σ.kheap u.bv := fun u hu => by
    obtain ⟨es, hx, -⟩ := C.rel.obj u hu
    have hB := hA.kold hx
    rcases hkc u.bv with e | ⟨r, cs, cs', e1, -⟩
    · rw [e, hB, hx]
    · rw [hB] at e1; cases e1
  have hsep : ∀ u ∈ (∅ : Set U64) ∪ X, ∀ o ko, σ'.kheap o = some ko → o ≠ u.bv → EptApart u o ko := by
    intro u hu o ko' ho hne
    have hu : u ∈ X := hu.elim (fun h => h.elim) id
    have hB : ∃ ko0, σB.kheap o = some ko0 ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko0 := by
      rcases hkc o with e | ⟨r, cs, cs', e1, e2⟩
      · exact ⟨ko', by rw [← e]; exact ho, rfl⟩
      · rw [ho] at e2; cases e2; exact ⟨_, e1, by simp [Fl4Spec.objBits]⟩
    obtain ⟨ko0, hk0, hb0⟩ := hB
    unfold EptApart
    rw [hb0]
    rcases hA.kback hk0 with h | ⟨⟨hq, -⟩, hko⟩
    · exact C.sep u hu o ko0 h hne
    · obtain ⟨j, hj, rfl⟩ := regionPtrs_mem hq
      have hjk : (j + 1) * 2 ^ zOf nt us ≤ w * 2 ^ zOf nt us := Nat.mul_le_mul_right _ hj
      rw [Nat.add_mul, Nat.one_mul] at hjk
      have e := ptrAdd_toNat (rb := rb) (n := j * 2 ^ zOf nt us) (by omega)
      have hko' : Fl4Spec.objBits ko0 = Fl4Spec.objBits (Fl4Spec.defaultObject t dev us σ.curDomain) := by
        rw [hko]
      have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) hob
      rw [hko', e]
      rcases hXw u hu with h | h <;> omega
  have h5 : EptSlotStep Z.th Z.th (L.mem s) (L.mem s') := by
    intro t0 ht0
    have hAs : AbsSlot Z.th (t0.bv, Fl4Spec.tcbCnodeIndex 5) := ⟨t0, rfl, Or.inr ⟨ht0, 5, by decide, rfl⟩⟩
    have hy := hAs.isSlot
    rcases C.eslot t0 ht0 with h | ⟨p0, a0, v0, h⟩
    · by_cases h0 : capV (L.mem s') (cslotAddr (t0.bv, Fl4Spec.tcbCnodeIndex 5)) = .Null
      · exact Or.inl h0
      exfalso
      rcases hcaps _ hy h0 with ⟨j, hj, ey⟩ | ⟨-, e | ⟨-, p1, sb1, fi1, fi2, d1, e, -⟩⟩
      · obtain ⟨q, r, hq, i, hi, eq⟩ := hdsC j hj
        obtain ⟨p2, i2, hi2, hp2, hy2⟩ := hAs.at
        obtain ⟨e1, -⟩ := slotOf_inj hP hi2 (Or.inl ⟨r, hq, hi⟩) (hy2.symm.trans (ey.trans eq))
        have e2 : t0 = p2 := UScalar.eq_of_val_eq (congrArg BitVec.toNat hp2)
        rw [e2, e1, hq] at ht0; cases ht0
      · exact h0 (e.trans h)
      · rw [h] at e; cases e
    · exact Or.inr (Or.inr ⟨ht0, (cK _ hy _ _ _ _ _ h).trans h.symm⟩)
  have hX' : JExtEpt (L := L) ((∅ : Set U64) ∪ X) Z.th s' := by
    rw [Set.empty_union]
    exact ⟨cX, ⟨fun y hy p l a v h => C.exte.vtop.1 y hy p l a v (cE y hy _ _ _ _ _ h),
      fun y hy p sz r d a v h => C.exte.vtop.2 y hy p sz r d a v (cF y hy _ _ _ _ _ _ _ h)⟩,
      fun y hy p l a v h => C.exte.anz y hy p l a v (cE y hy _ _ _ _ _ h)⟩
  have hnm : EptNamed Z.th (L.mem s') σ' :=
    C.named.frameA hat (fun hi lo e he _ => by
        obtain ⟨p0, f, h1, h2, h3⟩ := he
        exact ⟨p0, f, by rw [← hat]; exact h1, hpoolO _ _ h2, h3⟩)
      hobj (fun y p lv a v hy hc _ => ⟨y, hy, cK y hy _ _ _ _ _ hc⟩)
      (fun y p lv mm a v hy hc => ⟨y, hy, cE y hy _ _ _ _ _ hc⟩)
  have := C.growSZ (T := ∅) (fun _ h => h.elim) XL (fun _ _ => rfl) hw hF (fun _ _ _ h => h.elim)
    (fun _ h => h.elim) (fun _ h => h.elim) (fun _ h => h.elim) hxk
    (fun r l es h => Or.inr ⟨l, es, hobj r l es h⟩)
    (fun y hy p l a v mm h => Or.inr ⟨hy, cE y hy _ _ _ _ _ h⟩) (fun _ h => h.elim) hX'
    (fun e he => by
      obtain ⟨hi, p0, f, lo, h1, h2, h3⟩ := he
      exact ⟨hi, p0, f, lo, by rw [← hat]; exact h1, hpoolO _ _ h2, h3⟩)
    (fun _ h => h.elim) hsep h5 hnm (fun _ h => h.elim)
  rwa [Set.empty_union] at this

/-- **`VmEptState` across a native retype adding no typed-heap object** (the Architect's item (h) for the types 0,
2, 3, 5..13): from `VmEptState V X XL` at the entry, `JAtZB` after and the window the body wrote, with the consumers'
footprint predicates (`RetFootV`, `RetFootE`) and the window apart from the VCPUs and tables: `VmEptState V X XL`
after (`VcpuCore.ofRet`, `EptCore.ofRet`). -/
theorem VmEptState.ofRet (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {Z' : XSets} {H' : P1.Heap} {Cs' Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (B' : JAtZB (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σ')
    {W : U64 → Prop} {xs : U64} {nt : Nat} {t : Fl4Spec.ApiObjectType} {us : Nat} {rb : Fl4Spec.ObjRef}
    {w : Nat} {dev : Bool}
    (R : RetWin (L := L) Z.th Z'.th Z.G Z'.G H H' σ σ' s s' W xs nt t us rb w dev)
    (hFV : RetFootV (L := L) V Z.th s W) (hFE : RetFootE X W) (hn : thKindN nt us = none)
    (hty : objTypeOf nt = some t) (hn13 : nt ≤ 13)
    (hVw : ∀ v ∈ V, v.val + 32768 ≤ rb.toNat ∨ rb.toNat + w * 2 ^ zOf nt us ≤ v.val)
    (hXw : ∀ u ∈ X, u.val + 4096 ≤ rb.toNat ∨ rb.toNat + w * 2 ^ zOf nt us ≤ u.val)
    (hob : Fl4Spec.objBits (Fl4Spec.defaultObject t dev us σ.curDomain) ≤ zOf nt us)
    (hfit : rb.toNat + w * 2 ^ zOf nt us ≤ 2 ^ 64) :
    VmEptState (L := L) arI V X XL AR Z' H' Cs' Ac' Lst' D' s' a' σ' :=
  ⟨⟨B', VcpuCore.ofRet J.1.1 J.1.2 R hFV hn (by omega) (objTypeOf_ne_vcpu hty hn13) hVw hob hfit⟩,
    EptCore.ofRet J.1.1 J.2 R hFE hn hty hn13 hXw hob hfit⟩

/-- **`VmEptState` after a native body's `UtBodyPostB`** (types 0, 2, 3, 5..13): the spec's outcome, `Ok`, and
`VmEptState V X XL` at the state after, from the body's post and the consumers' predicates at its footprint. -/
theorem VmEptState.ofPost (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) {nt : Nat}
    {Xp : XSets → P1.Heap → Set U64 → S → Fl4Spec.State Unit → Prop} {W : Nat → Nat → U64 → Prop}
    {src : Fl4Spec.CslotPtr} {rs : Bool} {pb rb : Fl4Spec.ObjRef} {t : Fl4Spec.ApiObjectType} {us : Nat}
    {slots : List Fl4Spec.CslotPtr} {dev : Bool} {res : core.result.Result Unit error.Exc × S × A}
    (h : UtBodyPostB (L := L) arI AR Z.th Z.G H s σ nt Xp W (.retype src rs pb rb t us slots dev) res)
    (hFV : RetFootV (L := L) V Z.th s (W rb.toNat (rb.toNat + slots.length * 2 ^ zOf nt us)))
    (hFE : RetFootE X (W rb.toNat (rb.toNat + slots.length * 2 ^ zOf nt us)))
    (hn : thKindN nt us = none) (hty : objTypeOf nt = some t) (hn13 : nt ≤ 13)
    (hVw : ∀ v ∈ V, v.val + 32768 ≤ rb.toNat ∨ rb.toNat + slots.length * 2 ^ zOf nt us ≤ v.val)
    (hXw : ∀ u ∈ X, u.val + 4096 ≤ rb.toNat ∨ rb.toNat + slots.length * 2 ^ zOf nt us ≤ u.val)
    (hob : Fl4Spec.objBits (Fl4Spec.defaultObject t dev us σ.curDomain) ≤ zOf nt us)
    (hfit : rb.toNat + slots.length * 2 ^ zOf nt us ≤ 2 ^ 64) :
    ∃ σ', (Fl4Spec.fl4InvokeUntypedV (Z := Unit) (.retype src rs pb rb t us slots dev)).run σ = ({(.ok (), σ')}, False) ∧
      res.1 = .Ok () ∧ ∃ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        VmEptState (L := L) arI V X XL AR Z' H' Cs' Ac' Lst' D' res.2.1 res.2.2 σ' := by
  obtain ⟨σ', hrun, hok, -, Z', H', Cs', Ac', Lst', D', B', -, -, -, hR⟩ := h
  exact ⟨σ', hrun, hok, Z', H', Cs', Ac', Lst', D',
    J.ofRet B' (hR _ _ _ _ _ _ _ _ rfl) hFV hFE hn hty hn13 hVw hXw hob hfit⟩

end

end Fl4Proofs.P3
