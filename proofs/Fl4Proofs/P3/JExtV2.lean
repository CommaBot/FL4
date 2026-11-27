/-
P3x for virtualization (line virt, gen 26, item 2): **`JExtV2`, the VM-epoch joint extension with stale IO-port
owners allowed** — the corrected form of P3/JExtV's `JExtV`, whose IO-port clause is false on a reachable state
(gen 25, P3/VirtVFinal; mechanised in P3/VirtJExtV2Del's `final_delete_not_jextV`).

## Why the IO-port clause goes

`JExtV.cap` asks `VtxCap V X (.IoPort f l o)`, i.e. `o ≠ 0 → o ∈ V`. FL4 keeps IO-port caps that name a deleted
VCPU: `vcpu::finalise` (vcpu.rs l. 737-753) stalls, releases, detaches and unlinks, and touches no IO-port cap;
`X86VCPUEnableIOPort` (l. 1020-1052) writes `vcpu: v` into the cap and checks a previous owner only by VCPU-list
membership ("before touching an object that may have been deleted"), as `revoke_ports` (l. 767-782) does. So
after a final `Vcpu v` delete an `IoPort f l v` cap may sit in a slot while `v` is no longer listed.

What may an owner word be on a reachable state? `0` (IoPortControl issues `vcpu: 0`, ioport.rs l. 102), a listed
VCPU, or a stale (no longer listed) address. Since `VList V` makes `V` exactly the listed set (P3/JExtVList:
`VList.lst`, `w ∈ l ↔ w ∈ V`), "0, listed, or not listed" is no constraint at all: the weakest clause is `True`,
and **no proof consumes the clause** (gen 26 audit, handoff `# gen 26`: every consumer of `JExtV.cap` uses its
`Vcpu` arm — `JAtZV3.vcpuCapV`, `delete_vcpu_vcapped`, `delete_vcpu_final_alone` — or its `IoPort` arm only at
`V = ∅`, `JExtV.toJExt`; mmuAD's EnableIOPort is scoped to `IoFresh`, owner word 0, and walks no list; the
`revoke_ports` frames, XTopJointFinVtOps, quantify over every listed VCPU and read no owner fact). So `VtxCap2`
drops it: `VtxCap2 V X (.IoPort f l o) = True` (`vtxCap2_ioPort`).

## What this module proves (memory level, no named premise)

* `VtxCap2`, `vtxCap2_ioPort`, `VtxCap.toV2`, `VtxCap2.of_native`, `VtxCap2.mono`.
* **`JExtV2 V X th s`** (fields `cap` (`VtxCap2`), `bnd`, `back`, `nz` — `JExtV`'s last three verbatim),
  **`JExtV.toV2`** (`JExtV → JExtV2`), `JExtV2.of_jext`, `JAtZ.extV2`.
* `IoOwnV V th m` (every IO-port owner word is 0 or in `V`, the dropped clause), **`jExtV_iff_v2`**
  (`JExtV ↔ JExtV2 ∧ IoOwnV`), **`not_jextV_of_stale`** (a slot holding `IoPort f l o`, `o ≠ 0`, `o ∉ V` ⇒
  `¬ JExtV V X th s`).
* Preservation, as P3/JExtV / JExtVSteps / JExtVSteps2: **`JExtV2.of_eq`**, **`JExtV2.of_writes`**,
  **`JExtV2.step`**, **`JExtV2.bind`**, **`JExtV2.unbind`**, `JExtV2.mono_X`, **`JExtV2.grow`**,
  **`JExtV2.shrink`** (deleting a VCPU needs only that no slot holds `Vcpu v`: owned IO ports may stay).
* The TCB-only typed heap bridge: `thTcb th` (the TCBs of `th`, no CNodes), `thTcb_some`, `thTcb_tcb`,
  `isSlot_thTcb`, **`NoIoTcb th m`** (no TCB cap slot holds an IO-port cap with a nonzero owner),
  **`JExtV2.toTcb`** (`JExtV2 V X th s ∧ NoIoTcb ⇒ JExtV V X (thTcb th) s`) and **`JExtV2.ofTcb`**
  (`JExtV V' X (thTcb th) s'` + `VtxCap2` for every slot of `th` ⇒ `JExtV2 V' X th s'`): any `JExtV` step lemma
  whose hypotheses only weaken when CNodes are removed from the typed heap transfers to `JExtV2`
  (P3/VirtJExtV2Del uses it for `vcpu.finalise`).

`NoIoTcb` is a state hypothesis of the bridge, discharged as the named premise of its users (P3/VirtJExtV2Del,
[J]). No existing statement changed; new file only.
-/
import Fl4Proofs.P3.JExtVSteps2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- **A cap of the VM epoch with stale IO-port owners allowed** (module docstring). -/
def VtxCap2 (V X : Set U64) : capability.Cap → Prop
  | .Vcpu p => p ∈ V
  | .Ept p _ _ _ _ => p ∈ X
  | .Frame _ _ _ _ m e _ _ => m = true ∧ e = true → X.Nonempty
  | _ => True

/-- An IO-port cap is a `VtxCap2` cap whatever its owner word (0, a listed VCPU, or a stale address). -/
theorem vtxCap2_ioPort (V X : Set U64) (f l o : U64) : VtxCap2 V X (.IoPort f l o) := trivial

theorem VtxCap.toV2 {V X : Set U64} {c : capability.Cap} (h : VtxCap V X c) : VtxCap2 V X c := by
  cases c with
  | Vcpu p => exact h
  | Ept p l m a v => exact h
  | Frame p sz r d m e a v => exact h
  | _ => trivial

theorem VtxCap2.of_native {V X : Set U64} {c : capability.Cap} (h : Vs.NativeCap c) : VtxCap2 V X c :=
  (VtxCap.of_native h).toV2

theorem VtxCap2.mono {V V' X X' : Set U64} (hV : V ⊆ V') (hX : X ⊆ X') {c : capability.Cap}
    (h : VtxCap2 V X c) : VtxCap2 V' X' c := by
  cases c with
  | Vcpu p => exact hV h
  | Ept p l m a v => exact hX h
  | Frame p sz r d m e a v =>
    have h' : m = true ∧ e = true → X.Nonempty := h
    exact fun hme => (h' hme).mono hX
  | _ => trivial

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The VM-epoch joint extension with stale IO-port owners allowed** (module docstring): `JExtV` with
`VtxCap2` for `VtxCap`. -/
structure JExtV2 (V X : Set U64) (th : TypedHeap) (s : S) : Prop where
  /-- Every slot's cap is a VM-epoch cap (IO-port owners unconstrained). -/
  cap : ∀ y, IsSlot th y → VtxCap2 V X (capV (L.mem s) y)
  /-- `JExtV.bnd`. -/
  bnd : ∀ t, th t = some .tcb → L.mem s (tVcpuA t) = 0#u64 ∨
    (L.mem s (tVcpuA t) ∈ V ∧ L.mem s (vTcbA (L.mem s (tVcpuA t))) = t)
  /-- `JExtV.back`. -/
  back : ∀ v ∈ V, L.mem s (vTcbA v) = 0#u64 ∨
    (th (L.mem s (vTcbA v)) = some .tcb ∧ L.mem s (tVcpuA (L.mem s (vTcbA v))) = v)
  /-- `JExtV.nz`. -/
  nz : ∀ v ∈ V, v ≠ 0#u64

/-- The dropped clause: every IO-port owner word in a slot is 0 or a VCPU of `V`. -/
def IoOwnV (V : Set U64) (th : TypedHeap) (m : U64 → U64) : Prop :=
  ∀ y, IsSlot th y → ∀ f l o, capV m y = .IoPort f l o → o ≠ 0#u64 → o ∈ V

variable {V X : Set U64} {th : TypedHeap} {s s' : S}

/-- **`JExtV → JExtV2`.** -/
theorem JExtV.toV2 (E : JExtV (L := L) V X th s) : JExtV2 (L := L) V X th s :=
  ⟨fun y hy => (E.cap y hy).toV2, E.bnd, E.back, E.nz⟩

theorem JExtV2.of_jext (E : JExt (L := L) th s) : JExtV2 (L := L) ∅ ∅ th s := (JExtV.of_jext E).toV2

/-- Every P3 joint state satisfies `JExtV2 ∅ ∅`. -/
theorem JAtZ.extV2 {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : JExtV2 (L := L) ∅ ∅ Z.th s :=
  J.extV.toV2

/-- **`JExtV` is `JExtV2` plus the IO-port owner clause.** -/
theorem jExtV_iff_v2 : JExtV (L := L) V X th s ↔ JExtV2 (L := L) V X th s ∧ IoOwnV V th (L.mem s) := by
  constructor
  · intro E
    refine ⟨E.toV2, fun y hy f l o hc ho => ?_⟩
    have h := E.cap y hy
    rw [hc] at h
    exact h ho
  · rintro ⟨E2, hI⟩
    refine ⟨fun y hy => ?_, E2.bnd, E2.back, E2.nz⟩
    have h2 := E2.cap y hy
    have hI' := hI y hy
    revert h2 hI'
    cases capV (L.mem s) y with
    | IoPort f l o => intro _ hI'; exact fun ho => hI' f l o rfl ho
    | Vcpu p => intro h _; exact h
    | Ept p l m a v => intro h _; exact h
    | Frame p sz r d m e a v => intro h _; exact h
    | _ => intro _ _; trivial

/-- **A stale IO-port owner refutes `JExtV`** (gen 25's counterexample, cap level). -/
theorem not_jextV_of_stale {y : U64} (hy : IsSlot th y) {f l o : U64} (hc : capV (L.mem s) y = .IoPort f l o)
    (ho : o ≠ 0#u64) (hoV : o ∉ V) : ¬ JExtV (L := L) V X th s := fun E =>
  hoV ((jExtV_iff_v2.1 E).2 y hy f l o hc ho)

/-! ## Preservation at the memory-effect level -/

/-- **Frame** (`JExtV.of_eq`). -/
theorem JExtV2.of_eq (E : JExtV2 (L := L) V X th s)
    (hc : ∀ y, IsSlot th y → capV (L.mem s') y = capV (L.mem s) y) (hv : VKeep (L := L) th s s')
    (hb : ∀ v ∈ V, L.mem s' (vTcbA v) = L.mem s (vTcbA v)) : JExtV2 (L := L) V X th s' where
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

/-- **A step writing none of the extension's words** (`JExtV.of_writes`). -/
theorem JExtV2.of_writes (E : JExtV2 (L := L) V X th s) (P : JWPl V th) {W : U64 → Prop}
    (hW : P1.WritesIn st s s' W) (hd : ∀ b, W b → ¬ JW V th b) : JExtV2 (L := L) V X th s' := by
  have k : ∀ b, JW V th b → L.mem s' b = L.mem s b := fun b hb =>
    hW.mem_eq (P.jw b hb) fun hw => hd b hw hb
  refine E.of_eq (fun y hy => ?_) (fun t ht => k _ (Or.inr (Or.inl ⟨t, ht, rfl⟩)))
    (fun v hv => k _ (Or.inr (Or.inr ⟨v, hv, rfl⟩)))
  unfold capV
  rw [k y (Or.inl ⟨y, hy, Or.inl rfl⟩), k _ (Or.inl ⟨y, hy, Or.inr rfl⟩)]

/-- **A CSpace step** (`JExtV.step`): every slot's cap afterwards native or an old slot's cap. -/
theorem JExtV2.step (E : JExtV2 (L := L) V X th s)
    (hT : ∀ y, IsSlot th y → Vs.NativeCap (capV (L.mem s') y) ∨
      ∃ y', IsSlot th y' ∧ capV (L.mem s') y = capV (L.mem s) y')
    (hv : VKeep (L := L) th s s') (hb : ∀ v ∈ V, L.mem s' (vTcbA v) = L.mem s (vTcbA v)) :
    JExtV2 (L := L) V X th s' where
  cap y hy := by
    rcases hT y hy with h | ⟨y', hy', e⟩
    · exact VtxCap2.of_native h
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

/-- **Binding** (`JExtV.bind`, `X86VCPUSetTCB`'s two writes, vcpu.rs l. 859-860). -/
theorem JExtV2.bind (E : JExtV2 (L := L) V X th s) {t v : U64} (ht : th t = some .tcb) (hv : v ∈ V)
    (hw0 : L.mem s (tVcpuA t) = 0#u64) (hb0 : L.mem s (vTcbA v) = 0#u64) (h0 : th 0#u64 ≠ some .tcb)
    (hc : ∀ y, IsSlot th y → capV (L.mem s') y = capV (L.mem s) y)
    (h1 : L.mem s' (tVcpuA t) = v) (h2 : L.mem s' (vTcbA v) = t)
    (hT : ∀ t', th t' = some .tcb → t' ≠ t → L.mem s' (tVcpuA t') = L.mem s (tVcpuA t'))
    (hV : ∀ w ∈ V, w ≠ v → L.mem s' (vTcbA w) = L.mem s (vTcbA w)) : JExtV2 (L := L) V X th s' where
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

/-- **Unbinding** (`JExtV.unbind`, `vcpu::detach`'s two writes, vcpu.rs l. 733-734). -/
theorem JExtV2.unbind (E : JExtV2 (L := L) V X th s) {t v : U64} (hv : v ∈ V)
    (htv : L.mem s (tVcpuA t) = v) (hvt : L.mem s (vTcbA v) = t)
    (hc : ∀ y, IsSlot th y → capV (L.mem s') y = capV (L.mem s) y)
    (h1 : L.mem s' (tVcpuA t) = 0#u64) (h2 : L.mem s' (vTcbA v) = 0#u64)
    (hT : ∀ t', th t' = some .tcb → t' ≠ t → L.mem s' (tVcpuA t') = L.mem s (tVcpuA t'))
    (hV : ∀ w ∈ V, w ≠ v → L.mem s' (vTcbA w) = L.mem s (vTcbA w)) : JExtV2 (L := L) V X th s' where
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

/-- **An EPT retype grows `X`** (`JExtV.mono_X`). -/
theorem JExtV2.mono_X (E : JExtV2 (L := L) V X th s) {X' : Set U64} (hX : X ⊆ X') :
    JExtV2 (L := L) V X' th s where
  cap y hy := VtxCap2.mono (fun _ h => h) hX (E.cap y hy)
  bnd := E.bnd
  back := E.back
  nz := E.nz

/-- **A VCPU retype grows `V`** (`JExtV.grow`). -/
theorem JExtV2.grow (E : JExtV2 (L := L) V X th s) (P : JWPl V th) {v : U64} (hv0 : v ≠ 0#u64)
    {th' : TypedHeap} (htc : ∀ t, th' t = some .tcb ↔ th t = some .tcb) (hsl : ∀ y, IsSlot th' y → IsSlot th y)
    {W : U64 → Prop} (hW : P1.WritesIn st s s' W) (hd : ∀ b, W b → ¬ JW V th b)
    (hb : L.mem s' (vTcbA v) = 0#u64) : JExtV2 (L := L) (insert v V) X th' s' := by
  have E' := E.of_writes P hW hd
  refine ⟨fun y hy => VtxCap2.mono (Set.subset_insert v V) (fun _ h => h) (E'.cap y (hsl y hy)),
    fun t ht => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · rcases E'.bnd t ((htc t).1 ht) with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨Set.mem_insert_of_mem v h1, h2⟩
  · rcases Set.mem_insert_iff.1 hw with rfl | hw'
    · exact Or.inl hb
    · rcases E'.back w hw' with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨(htc _).2 h1, h2⟩
  · rcases Set.mem_insert_iff.1 hw with rfl | hw'
    · exact hv0
    · exact E'.nz w hw'

/-- **Deleting a VCPU shrinks `V`** (`JExtV.shrink` without its IO-port condition): its `TCB` word 0 and no slot
holding `Vcpu v`; IO-port caps owned by `v` may stay. -/
theorem JExtV2.shrink (E : JExtV2 (L := L) V X th s) {v : U64} (hb : L.mem s (vTcbA v) = 0#u64)
    (h0 : th 0#u64 ≠ some .tcb) (hc : ∀ y, IsSlot th y → capV (L.mem s) y ≠ .Vcpu v) :
    JExtV2 (L := L) (V \ {v}) X th s := by
  refine ⟨fun y hy => ?_, fun t ht => ?_, fun w hw => E.back w hw.1, fun w hw => E.nz w hw.1⟩
  · have h := E.cap y hy
    have hc1 := hc y hy
    revert h hc1
    cases capV (L.mem s) y with
    | Vcpu p =>
      intro h hc1
      exact Set.mem_diff_of_mem h fun e => hc1 (by rw [Set.mem_singleton_iff.1 e])
    | Ept p l m a w => intro h _; exact h
    | Frame p sz r d m e a w => intro h _; exact h
    | _ => intro _ _; trivial
  · rcases E.bnd t ht with h | ⟨h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨Set.mem_diff_of_mem h1 fun e => ?_, h2⟩
      rw [Set.mem_singleton_iff.1 e, hb] at h2
      rw [← h2] at ht
      exact h0 ht

end

/-! ## The TCB-only typed heap -/

/-- **The TCBs of `th`** (no CNodes, no other objects). -/
def thTcb (th : TypedHeap) : TypedHeap := fun q => if th q = some .tcb then some .tcb else none

theorem thTcb_some {th : TypedHeap} {q : U64} {k : ObjKind} (h : thTcb th q = some k) :
    th q = some k ∧ k = .tcb := by
  unfold thTcb at h
  by_cases hq : th q = some .tcb
  · rw [if_pos hq] at h
    cases h
    exact ⟨hq, rfl⟩
  · rw [if_neg hq] at h
    cases h

theorem thTcb_tcb {th : TypedHeap} {q : U64} : thTcb th q = some .tcb ↔ th q = some .tcb := by
  constructor
  · intro h; exact (thTcb_some h).1
  · intro h; unfold thTcb; rw [if_pos h]

theorem isSlot_thTcb {th : TypedHeap} {y : U64} (h : IsSlot (thTcb th) y) : IsSlot th y := by
  obtain ⟨p, i, hi, rfl⟩ := h
  refine ⟨p, i, ?_, rfl⟩
  rcases hi with ⟨r, hr, _⟩ | ⟨ht, hi⟩
  · exact absurd (thTcb_some hr).2 (by intro e; cases e)
  · exact Or.inr ⟨thTcb_tcb.1 ht, hi⟩

theorem isSlot_thTcb_tcb {th : TypedHeap} {t : U64} (ht : th t = some .tcb) {i : Nat} (hi : i < tcbSlots) :
    IsSlot (thTcb th) (slotOf t i) :=
  ⟨t, i, Or.inr ⟨thTcb_tcb.2 ht, hi⟩, rfl⟩

/-- **No TCB cap slot holds an owned IO-port cap** (the bridge's hypothesis; module docstring). -/
def NoIoTcb (th : TypedHeap) (m : U64 → U64) : Prop :=
  ∀ y, IsSlot (thTcb th) y → ∀ f l o, capV m y = .IoPort f l o → o = 0#u64

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {V X : Set U64} {th : TypedHeap} {s s' : S}

/-- **`JExtV2` with no owned IO-port cap in a TCB slot is `JExtV` at the TCB-only heap.** -/
theorem JExtV2.toTcb (E : JExtV2 (L := L) V X th s) (hT : NoIoTcb th (L.mem s)) :
    JExtV (L := L) V X (thTcb th) s := by
  refine ⟨fun y hy => ?_, fun t ht => E.bnd t (thTcb_tcb.1 ht), fun v hv => ?_, E.nz⟩
  · have h2 := E.cap y (isSlot_thTcb hy)
    have hI := hT y hy
    revert h2 hI
    cases capV (L.mem s) y with
    | IoPort f l o => intro _ hI ho; exact absurd (hI f l o rfl) ho
    | Vcpu p => intro h _; exact h
    | Ept p l m a v => intro h _; exact h
    | Frame p sz r d m e a v => intro h _; exact h
    | _ => intro _ _; trivial
  · rcases E.back v hv with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨thTcb_tcb.2 h1, h2⟩

/-- **Back from the TCB-only heap**: its `JExtV` and `VtxCap2` at every slot of `th`. -/
theorem JExtV2.ofTcb {V' : Set U64} (E : JExtV (L := L) V' X (thTcb th) s')
    (hc : ∀ y, IsSlot th y → VtxCap2 V' X (capV (L.mem s') y)) : JExtV2 (L := L) V' X th s' := by
  refine ⟨hc, fun t ht => E.bnd t (thTcb_tcb.2 ht), fun v hv => ?_, E.nz⟩
  rcases E.back v hv with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨thTcb_tcb.1 h1, h2⟩

end

end

end Fl4Proofs.P3
