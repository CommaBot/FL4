/-
P3 (line mmuAD, gen 42b25; gen 42b26: every type but the VCPU): **`VmEptState` across a retype** — the Architect's
item (h) (rulings 2026-11-28 18:08Z, 18:58Z) for the types 0..13 and 15..18, from a body's `RetWin` (P3/UtScRet:
the footprint `W`, the spec-object predicate `O`, `RetObjOK`, the new objects' FL4 words `RetNew`).

* **`VcpuCore.ofRet`**: from `JAtZB` and `VcpuCore V` at the entry state, `JAtZB` after (`Placed`, the TCB offsets),
  the window the body wrote (`RetWin` at the footprint `W`, object predicate `O`) with `RetFootV V th s W`
  (P3/RetFoot), the window apart from every VCPU of `V` (`hVw`; RAM windows: **`JAtZB.winV`**) and from the
  kernel-state block (`hKw`), the new objects' size (`hob`), the type not the VCPU: `VcpuCore V` after. The VCPU
  objects' words, the list head, the old TCBs' `VCPU` and state words are outside the footprint; a new TCB's are 0
  (`RetNew`: unbound, `TS_INACTIVE`) and its slots null (so no `IoPort` cap); the slot caps after are old ones, the
  window's (`capsOf`: no `Vcpu` / `IoPort` cap, **`capsOf_vtx`**) or the source untyped's; the spec adds no VCPU
  object (`RetObjOK`) and keeps each one of `V` (`SpecAdd.kold`, `KeepC`); `RngOne` by `mdbStep_rngOne`; `JVm` by
  `JVm.step`; `VList` at the grown typed heap by **`VList.ofGrow`** (a new object lies in the window,
  **`ThX.retGrow`** / **`thKindN_size`**, the window off the list head).
* **`EptCore.ofRet`**: P3/EptStep2's `EptCore.growS` at `T = RetTabs` (**`RetTabs`**: the window's 4 KiB tables for
  15..18, none otherwise; levels **`RetLvl`**: `eptLvl` on them), with `RetFootE X W`, the window apart from the
  tables (`hXw`; RAM: **`JAtZB.winX`**), from every spec object (`hσw`, `JAtZB.winFree`), from the kernel-global area
  (`hKs`, **`JAtZB.winKs`**), at or above `PPTR_BASE` (`hPa`, **`JAtZB.winPa`**): the window caps are the unmapped
  `Ept` caps to `RetTabs` (**`capsOf_eptW`**) or native ones; the new tables zero (`RetNew`) and the spec's
  `.ept (eptLvl nt) 0` (`RetObjOK`); a new TCB's `SLOT_EPT` null; `EptNamed` by **`EptNamed.retGrow`** (a new table
  is on no old path, **`GPath.objW`** from `EptWalk`).
* **`VmEptState.ofRet`** (both), **`VmEptState.ofPost`** (from a body's `UtBodyPostB` with a RAM `AbsSlot` source: the
  spec's run, `Ok`, `VmEptState V (RetTabs ∪ X) (RetLvl XL)` after), **`VmEptState.ofPostN`** (0..13: `X`, `XL`
  unchanged, **`retTabs_none`**, **`retLvl_none`**).

Gen 42b27: `hob` of `VcpuCore.ofRet`, `EptCore.ofRet`, `VmEptState.ofRet`, `ofPost`, `ofPostN` asked only for
`t ≠ untyped` (the proofs read it only there; for the untyped type the spec's `defaultObject` is `undefined`, so the
unguarded form could not be given). New **`JVm.winOff`** / **`EptCore.winOff`** (`winV` / `winX`'s proofs for any range
every spec object misses; `winV`, `winX` their instances, statements unchanged). The unified retype over the bodies
is P3/RetVmAll.

Not covered: the VCPU (14; no `JAtZB` fact after FL4's VCPU retype exists, P3/RetVmAll).

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

/-- The typed-heap objects of a retype fit their window slot (`thKindN`: a TCB, 4 KiB; a CNode, `2^(5+us)`). -/
theorem thKindN_size {n us : Nat} {kd : ObjKind} (h : thKindN n us = some kd) : objSize kd ≤ 2 ^ zOf n us := by
  unfold thKindN at h
  by_cases h1 : n = 1
  · rw [if_pos h1] at h; cases h; subst h1; simp [objSize, zOf]
  · rw [if_neg h1] at h
    by_cases h4 : n = 4
    · rw [if_pos h4] at h; cases h; subst h4
      simp [objSize, zOf, pow_add]
    · rw [if_neg h4] at h; cases h

/-- **The typed heap across a retype** (`ThX`): old objects kept, a new one inside the window (its address free
before). -/
theorem ThX.retGrow {th th' : TypedHeap} {A k w n us : Nat} (hT : ThX th th' A k w n us)
    (hpos : ∀ q kd, th q = some kd → 0 < objSize kd) (hk : k = 2 ^ zOf n us) :
    (∀ q kd, th q = some kd → th' q = some kd) ∧
    ∀ q kd, th' q = some kd → th q = some kd ∨ (th q = none ∧ A ≤ q.val ∧ q.val + objSize kd ≤ A + w * k) := by
  have hk1 : 0 < k := by rw [hk]; exact Nat.two_pow_pos _
  refine ⟨fun q kd h => hT.mono hk1 hpos h, fun q kd h => ?_⟩
  rcases hT.casesI h with h1 | ⟨⟨j, hj, hq⟩, h2⟩
  · exact Or.inl h1
  · right
    have hs := thKindN_size h2
    rw [← hk] at hs
    have hjk : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    refine ⟨?_, by omega, by omega⟩
    cases e : th q with
    | none => rfl
    | some kd' =>
      exfalso
      have := hpos q kd' e
      rcases hT.2 q kd' e with h' | h' <;> omega

theorem eptCapX_mono {X Y : Set U64} (h : X ⊆ Y) {c : capability.Cap} (hc : EptCapX X c) : EptCapX Y c := by
  cases c <;> (try simp only [EptCapX] at hc ⊢) <;> first | trivial | exact h hc | exact fun e => (hc e).mono h

/-- **A retype's window cap off the VCPU type**: on 15..18 the unmapped `Ept` cap to the `j`-th 4 KiB table of the
window, else a native cap (no `Ept` cap, no mapped frame, naming no table). -/
theorem capsOf_eptW {n : Nat} (hn14 : n ≠ 14) (us : U64) (dev : Bool) (A k j : Nat) (X : Set U64) :
    (15 ≤ n → n ≤ 18 → capsOf n us dev A k j = .Ept ⟨BitVec.ofNat 64 (A + j * 4096)⟩ (eptLvl n) false 0#u64 0#u64) ∧
    ((n < 15 ∨ 18 < n) → EptCapX X (capsOf n us dev A k j) ∧ (∀ p l m a v, capsOf n us dev A k j ≠ .Ept p l m a v) ∧
      (∀ p sz r d e a v, capsOf n us dev A k j ≠ .Frame p sz r d true e a v)) := by
  refine ⟨fun h1 h2 => (by rw [capsOf_ept h1 h2]; rfl), fun h => ?_⟩
  rw [capsOf_native (by omega)]
  exact (newCapOf_vtx n _ us dev X).2.2

/-- **A table on a walk path at a nonzero level is a spec guest table** (`EptWalk`). -/
theorem GPath.objW {σ : Fl4Spec.State Unit} (hW : EptWalk σ) {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex}
    {gpa : Fl4Spec.Word} {l : Nat} {u : Fl4Spec.ObjRef} (h : GPath σ hi lo gpa l u) (hl : l ≠ 0) :
    ∃ es, σ.kheap u = some (.archObj (.ept l es)) := by
  cases h with
  | root _ _ => exact absurd rfl hl
  | step hp hk hc hw =>
    obtain ⟨e, hpa, h1, hr⟩ := hp.root_tag
    exact hW e hpa.guest h1 _ hr _ _ _ hk hw _ hc

/-- **`EptNamed` across a step adding fresh tables**: as `EptNamed.keep`, each `Ept` cap after an old one or to a
table that is no spec object before (so on no old path, `GPath.objW`). -/
theorem EptNamed.retGrow {th th' : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} (N : EptNamed th m σ)
    (hW : EptWalk σ) (hpath : ∀ hi lo gpa l u, GPath σ' hi lo gpa l u → l ≠ 0 → GPath σ hi lo gpa l u)
    (hinj : PoolInj σ')
    (hck : ∀ y p lv a v, IsSlot th y → capV m y = .Ept p lv true a v → lv.val ≠ 0 →
      ∃ y', IsSlot th' y' ∧ capV m' y' = .Ept p lv true a v)
    (hcb : ∀ y' p lv (mm : Bool) a v, IsSlot th' y' → capV m' y' = .Ept p lv mm a v →
      (∃ y, IsSlot th y ∧ capV m y = .Ept p lv mm a v) ∨ σ.kheap p.bv = none) :
    EptNamed th' m' σ' where
  ex hi lo gpa l u hg hp hl := by
    obtain ⟨y, p, lv, a, v, hy, hpu, hlv, h1, h2, h3, hc⟩ := N.ex hi lo gpa l u hg (hpath _ _ _ _ _ hp hl) hl
    obtain ⟨y', hy', hc'⟩ := hck y p lv a v hy hc (by rw [hlv]; exact hl)
    exact ⟨y', p, lv, a, v, hy', hpu, hlv, h1, h2, h3, hc'⟩
  all hi lo gpa l u hg hp hl y' p lv mm a v hy' hpu hc' := by
    have hp0 := hpath _ _ _ _ _ hp hl
    rcases hcb y' p lv mm a v hy' hc' with ⟨y, hy, hc⟩ | hn
    · exact N.all hi lo gpa l u hg hp0 hl y p lv mm a v hy hpu hc
    · obtain ⟨es, hk⟩ := GPath.objW hW hp0 hl
      rw [hpu, hk] at hn; cases hn
  inj := hinj

/-- **The guest tables a retype adds** (mmuAD gen 42b26): for the EPT types 15..18 the window's 4 KiB tables, else
none. -/
def RetTabs (nt us : Nat) (rb : Fl4Spec.ObjRef) (w : Nat) : Set U64 :=
  {u | (15 ≤ nt ∧ nt ≤ 18) ∧ ∃ j, j < w ∧ u.val = rb.toNat + j * 2 ^ zOf nt us}

open Classical in
/-- **The levels after a retype**: the type's level (`eptLvl`) on the new tables, `XL` elsewhere. -/
noncomputable def RetLvl (nt us : Nat) (rb : Fl4Spec.ObjRef) (w : Nat) (XL : U64 → Nat) (u : U64) : Nat :=
  if u ∈ RetTabs nt us rb w then (eptLvl nt).val else XL u

theorem retTabs_none {nt us : Nat} {rb : Fl4Spec.ObjRef} {w : Nat} (h : nt < 15 ∨ 18 < nt) :
    RetTabs nt us rb w = ∅ :=
  Set.ext fun _ => ⟨fun hu => absurd hu.1 (by omega), fun h => h.elim⟩

theorem retLvl_none {nt us : Nat} {rb : Fl4Spec.ObjRef} {w : Nat} (h : nt < 15 ∨ 18 < nt) (XL : U64 → Nat) :
    RetLvl nt us rb w XL = XL :=
  funext fun u => by unfold RetLvl; rw [if_neg (by rw [retTabs_none h]; exact fun h => h.elim)]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V : Set U64}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **A range every spec object misses is apart from the VCPUs** (gen 42b27: `JAtZB.winV`'s proof, any range). -/
theorem JVm.winOff (Jv : JVm (L := L) V H s σ) {lo hi : Nat}
    (hσ : ∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat) :
    ∀ v ∈ V, v.val + 32768 ≤ lo ∨ hi ≤ v.val := by
  intro v hv
  obtain ⟨x, hx⟩ := Jv.spec v hv
  have h := hσ _ _ hx
  have e : (2 : Nat) ^ Fl4Spec.objBits (.archObj (.vcpu x)) = 32768 := by
    simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]
  have hv' : v.bv.toNat = v.val := rfl
  rw [e, hv'] at h
  exact h

/-- **A RAM window is apart from the VCPUs** (module docstring). -/
theorem JAtZB.winV (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ)
    {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    {lo hi : Nat} (h1 : p.val + fi.val ≤ lo) (h2 : hi ≤ p.val + 2 ^ sb.val) :
    ∀ v ∈ V, v.val + 32768 ≤ lo ∨ hi ≤ v.val :=
  Jv.winOff (B.winFree hAs hcap h1 h2).1

/-- **`VList` at a grown typed heap**: the list head is no word of a new object (no new slot or its word 8, no new
TCB's `VCPU` or state word). -/
theorem VList.ofGrow {th th' : TypedHeap} {s : S} (Vl : VList st V th s)
    (hsl : ∀ y, IsSlot th' y → ¬ IsSlot th y → P1.vHeadA st s ≠ y ∧ P1.vHeadA st s ≠ wordOf y 8#u64)
    (htc : ∀ t, th' t = some .tcb → th t ≠ some .tcb → P1.vHeadA st s ≠ tVcpuA t ∧ P1.vHeadA st s ≠ P1.stA t) :
    VList st V th' s := by
  refine ⟨Vl.lst, Vl.hd.1, fun hJ => ?_, fun ⟨t, ht, e⟩ => ?_⟩
  · rcases hJ with ⟨y, hy, e⟩ | ⟨t, ht, e⟩ | hv
    · by_cases h0 : IsSlot th y
      · exact Vl.hd.2.1 (Or.inl ⟨y, h0, e⟩)
      · rcases e with e | e
        · exact (hsl y hy h0).1 e
        · exact (hsl y hy h0).2 e
    · by_cases h0 : th t = some .tcb
      · exact Vl.hd.2.1 (Or.inr (Or.inl ⟨t, h0, e⟩))
      · exact (htc t ht h0).1 e
    · exact Vl.hd.2.1 (Or.inr (Or.inr hv))
  · by_cases h0 : th t = some .tcb
    · exact Vl.hd.2.2 ⟨t, h0, e⟩
    · exact (htc t ht h0).2 e

set_option maxHeartbeats 4000000 in
/-- **`VcpuCore` across a retype of a type other than the VCPU** (module docstring; gen 42b26: any object predicate
`O`, the typed heap grown by TCBs / CNodes). -/
theorem VcpuCore.ofRet (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ)
    {Z' : XSets} {H' : P1.Heap} {Cs' Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (B' : JAtZB (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σ')
    {W : U64 → Prop} {O : Fl4Spec.ObjRef → Fl4Spec.KernelObject → Prop} {xs : U64} {nt : Nat}
    {t : Fl4Spec.ApiObjectType} {us : Nat} {rb : Fl4Spec.ObjRef} {w : Nat} {dev : Bool}
    (R : RetWin (L := L) Z.th Z'.th Z.G Z'.G H H' σ σ' s s' W O xs nt t us rb w dev)
    (hF : RetFootV (L := L) V Z.th s W) (hn14 : nt ≠ 14)
    (hVw : ∀ v ∈ V, v.val + 32768 ≤ rb.toNat ∨ rb.toNat + w * 2 ^ zOf nt us ≤ v.val)
    (hKw : rb.toNat + w * 2 ^ zOf nt us ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ rb.toNat)
    (hob : t ≠ .untyped → ∀ q ko, O q ko → Fl4Spec.objBits ko ≤ zOf nt us)
    (hfit : rb.toNat + w * 2 ^ zOf nt us ≤ 2 ^ 64) :
    VcpuCore (L := L) V Z' H' s' σ' := by
  obtain ⟨k, dslot, cj, hk, -, ⟨uu, -, hcj⟩, hcw, -, hw, hThX, hSt, -, hcaps, hout, ⟨σB, o, hA, hO, -, hkc⟩,
    hOK, hN, -, -⟩ := R
  subst hk
  have hpos : ∀ q kd, Z.th q = some kd → 0 < objSize kd := by
    intro q kd h
    rcases B.thk q kd h with rfl | ⟨r0, rfl⟩
    · simp [objSize]
    · simp only [objSize]; positivity
  obtain ⟨hold, hnew⟩ := hThX.retGrow hpos rfl
  have tOld : ∀ t, Z'.th t = some .tcb → Z.th t ≠ some .tcb → Z.th t = none := fun t ht hn => by
    rcases hnew t _ ht with h | ⟨h, -⟩
    · exact absurd h hn
    · exact h
  have hTV' : ∀ t, Z'.th t = some .tcb → Z.th t ≠ some .tcb →
      L.mem s' (tVcpuA t) = 0#u64 ∧ L.mem s' (P1.stA t) = 0#u64 := fun t ht hn => hN.2.1 t ht (tOld t ht hn)
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
    rcases hA.kback hpB with h | ⟨⟨hq, htu⟩, h⟩
    · exact h
    · exact absurd h.symm ((hOK htu p _ (hO p hq htu)).1 hn14 vs)
  -- the slot caps after
  have hcap' : ∀ y, IsSlot Z'.th y → capV (L.mem s') y = .Null ∨
      ((∀ p, capV (L.mem s') y ≠ .Vcpu p) ∧ (∀ f l o, capV (L.mem s') y ≠ .IoPort f l o)) ∨
      (IsSlot Z.th y ∧ capV (L.mem s') y = capV (L.mem s) y) := by
    intro y hy
    by_cases h0 : capV (L.mem s') y = .Null
    · exact Or.inl h0
    rcases hcaps y hy h0 with ⟨j, hj, rfl⟩ | ⟨hy0, e | ⟨-, p0, sb0, fi0, fi1, d0, -, e⟩⟩
    · right; left; rw [hcw j hj, hcj]; exact capsOf_vtx hn14 uu dev rb.toNat _ j
    · exact Or.inr (Or.inr ⟨hy0, e⟩)
    · right; left; rw [e]; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
  have E' : JExtVcpu (L := L) V Z'.th s' := by
    refine ⟨fun y hy => ?_, fun t ht => ?_, fun v hv => ?_, C.extv.nz⟩
    · rcases hcap' y hy with h | ⟨h, -⟩ | ⟨hy0, h⟩
      · rw [h]; trivial
      · cases e : capV (L.mem s') y <;> first | trivial | exact absurd e (h _)
      · rw [h]; exact C.extv.cap y hy0
    · by_cases hT : Z.th t = some .tcb
      · rw [kTV t hT]
        rcases C.extv.bnd t hT with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, by rw [kVT _ h1]; exact h2⟩
      · exact Or.inl (hTV' t ht hT).1
    · rw [kVT v hv]
      rcases C.extv.back v hv with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨hold _ _ h1, by rw [kTV _ h1]; exact h2⟩
  have hNI : NoIoTcb Z'.th (L.mem s') := by
    intro y hy f l o' h
    obtain ⟨p, i, hpi, rfl⟩ := hy
    have hp' : Z'.th p = some .tcb ∧ i < tcbSlots := by
      by_cases h1 : Z'.th p = some .tcb
      · rcases hpi with ⟨r, hr, -⟩ | ⟨-, hi⟩
        · simp [thTcb, h1] at hr
        · exact ⟨h1, hi⟩
      · exfalso
        rcases hpi with ⟨r, hr, -⟩ | ⟨hr, -⟩ <;> simp [thTcb, h1] at hr
    by_cases hT : Z.th p = some .tcb
    · rcases hcap' _ ⟨p, i, Or.inr hp', rfl⟩ with h0 | ⟨-, h0⟩ | ⟨-, h0⟩
      · rw [h0] at h; cases h
      · exact absurd h (h0 f l o')
      · rw [h0] at h
        exact C.noIoTcb _ ⟨p, i, Or.inr ⟨by simp [thTcb, hT], hp'.2⟩, rfl⟩ f l o' h
    · rw [hN.1 p i (Or.inr hp') (tOld p hp'.1 hT)] at h; cases h
  have R' : RunVmB (L := L) Z'.th s' := by
    intro t ht h8
    by_cases hT : Z.th t = some .tcb
    · rw [kTV t hT]; exact C.rvm t hT (by rw [← kSt t hT]; exact h8)
    · rw [(hTV' t ht hT).2] at h8; exact absurd h8 (by decide)
  have hk1 : 1 ≤ 2 ^ zOf nt us := Nat.one_le_two_pow
  have Jv' : JVm (L := L) V H' s' σ' := by
    refine C.vm.step (fun _ h => h) (fun v hv => ?_) hw.1 (fun u hu => by rw [hvk u hu]; exact C.vm.spec u hu)
      (fun o' ko' ho => ?_)
    · have e := hout_old hout rfl rfl hk1 (C.vm.heap v hv) (by
        simp only [P1.HKind.bits, Nat.reducePow]; exact hVw v hv)
      rw [e, C.vm.heap v hv]
    · have hB : ∃ ko0, σB.kheap o' = some ko0 ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko0 := by
        rcases hkc o' with e | ⟨r, cs, cs', e1, e2⟩
        · exact ⟨ko', by rw [← e]; exact ho, rfl⟩
        · rw [ho] at e2; cases e2; exact ⟨_, e1, by simp [Fl4Spec.objBits]⟩
      obtain ⟨ko0, hk0, hb0⟩ := hB
      rcases hA.kback hk0 with h | ⟨⟨hq, htu⟩, hko⟩
      · exact Or.inl ⟨ko0, h, hb0⟩
      · right
        intro v hv _
        have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) (hob htu _ _ (hO _ hq htu))
        obtain ⟨j, hj, rfl⟩ := regionPtrs_mem hq
        have hjk : (j + 1) * 2 ^ zOf nt us ≤ w * 2 ^ zOf nt us := Nat.mul_le_mul_right _ hj
        rw [Nat.add_mul, Nat.one_mul] at hjk
        have e := ptrAdd_toNat (rb := rb) (n := j * 2 ^ zOf nt us) (by omega)
        unfold VcpuApart
        rw [hb0, hko, e]
        rcases hVw v hv with h | h <;> omega
  have Vl0 : VList st V Z.th s' :=
    C.vl.writes hw fun b hb => by
      refine ⟨C.vl.lw_al Ly.vfit hb, fun hW => ?_⟩
      rcases hb with rfl | ⟨u, hu, rfl | rfl⟩
      · exact (hF _ hW).2.1 (by unfold P1.vHeadA; first | rfl | rw [hw.1])
      · have := lay_next_val (Ly.vfit u hu).2
        rcases nV u hu _ hW with h | h <;> omega
      · have := lay_prev_val (Ly.vfit u hu).2
        rcases nV u hu _ hW with h | h <;> omega
  have hP' : Placed Z'.th := B'.xtop.rel.1
  have hhd : (P1.vHeadA st s').val = (L.ksb s).val + 80 := by
    rw [show P1.vHeadA st s' = P1.vHeadA st s by unfold P1.vHeadA; rw [hw.1]]
    exact vHead_val B.kern.ksbFit
  have Vl' : VList st V Z'.th s' := Vl0.ofGrow
    (fun y hy hn => by
      obtain ⟨p, i, hpi, rfl⟩ := hy
      obtain ⟨kd, hkd, hsz⟩ := hpi.size
      rcases hnew p kd hkd with h | ⟨-, g1, g2⟩
      · refine absurd ⟨p, i, ?_, rfl⟩ hn
        have e : Z'.th p = Z.th p := hkd.trans h.symm
        unfold IsSlotAt at hpi ⊢; rw [← e]; exact hpi
      · have hv := hpi.val hP'
        have h8 : (wordOf (slotOf p i) 8#u64).val = (slotOf p i).val + 8 :=
          slot_word_val hP' ⟨p, i, hpi, rfl⟩ (Or.inr (Or.inl rfl))
        refine ⟨fun e => ?_, fun e => ?_⟩ <;> have := congrArg UScalar.val e <;>
          rcases hKw with h | h <;> omega)
    (fun t ht hn => by
      obtain ⟨-, g1, g2⟩ := (hnew t _ ht).resolve_left hn
      obtain ⟨e1, e2⟩ := B'.tcbVS ht
      have e4 : objSize ObjKind.tcb = 4096 := rfl
      rw [e4] at g2
      refine ⟨fun e => ?_, fun e => ?_⟩ <;> have := congrArg UScalar.val e <;>
        rcases hKw with h | h <;> omega)
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

/-- **A range every spec object misses is apart from the tables of `X`** (gen 42b27: `JAtZB.winX`'s proof, any
range). -/
theorem EptCore.winOff {th : TypedHeap} (C : EptCore (L := L) X XL th s σ) {lo hi : Nat}
    (hσ : ∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat) :
    ∀ u ∈ X, u.val + 4096 ≤ lo ∨ hi ≤ u.val := by
  intro u hu
  obtain ⟨es, hk, -⟩ := C.rel.obj u hu
  have h := hσ _ _ hk
  have e : (2 : Nat) ^ Fl4Spec.objBits (.archObj (.ept (XL u) es)) = 4096 := by rw [ept_bits]; rfl
  have hu' : u.bv.toNat = u.val := rfl
  rw [e, hu'] at h
  exact h

/-- **A RAM window is apart from the tables of `X`** (P3/RetFoot's `JAtZB.winFree`). -/
theorem JAtZB.winX (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    {lo hi : Nat} (h1 : p.val + fi.val ≤ lo) (h2 : hi ≤ p.val + 2 ^ sb.val) :
    ∀ u ∈ X, u.val + 4096 ≤ lo ∨ hi ≤ u.val :=
  C.winOff (B.winFree hAs hcap h1 h2).1

/-- **A RAM window misses the whole kernel-global area** `[ksb, ksb + 304384)` (the kernel-state block, the 64 cores'
nodes and the ASID table: `UtKsApart`). -/
theorem JAtZB.winKs (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    {lo hi : Nat} (h1 : p.val + fi.val ≤ lo) (h2 : hi ≤ p.val + 2 ^ sb.val) :
    hi ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ lo := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := B.xtop.rel
  have hxG : cslotAddr sl ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  obtain ⟨k1, -, k3⟩ := B.jcov.ks _ hxG p sb fi (capV_of_capAt hcap)
  have := Nat.one_le_two_pow (n := sb.val)
  rcases k1 with h | h <;> rcases k3 with h' | h' <;> omega

/-- **A RAM window lies at or above `PPTR_BASE`** (`UtWin` of the source, `MdbOKV`). -/
theorem JAtZB.winPa (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    {lo : Nat} (h1 : p.val + fi.val ≤ lo) : layout.PPTR_BASE.val ≤ lo := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -, -, hMO, -⟩ := B.xtop.rel
  have hxG : cslotAddr sl ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  have h := hMO.2.1 _ hxG
  rw [capV_of_capAt hcap] at h
  have := h.1 rfl
  omega

set_option maxHeartbeats 4000000 in
/-- **`EptCore` across a retype of a type other than the VCPU** (module docstring; gen 42b26: any object
predicate `O`, the typed heap grown by TCBs / CNodes, and for the EPT types 15..18 the window's tables added,
`RetTabs` at the levels `RetLvl`): `EptCore.growS` at `T = RetTabs`. -/
theorem EptCore.ofRet (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    {Z' : XSets} {H' : P1.Heap} {s' : S} {σ' : Fl4Spec.State Unit}
    {W : U64 → Prop} {O : Fl4Spec.ObjRef → Fl4Spec.KernelObject → Prop} {xs : U64} {nt : Nat}
    {t : Fl4Spec.ApiObjectType} {us : Nat} {rb : Fl4Spec.ObjRef} {w : Nat} {dev : Bool}
    (R : RetWin (L := L) Z.th Z'.th Z.G Z'.G H H' σ σ' s s' W O xs nt t us rb w dev)
    (hF : RetFootE X W) (hty : objTypeOf nt = some t) (hn14 : nt ≠ 14)
    (hXw : ∀ u ∈ X, u.val + 4096 ≤ rb.toNat ∨ rb.toNat + w * 2 ^ zOf nt us ≤ u.val)
    (hob : t ≠ .untyped → ∀ q ko, O q ko → Fl4Spec.objBits ko ≤ zOf nt us)
    (hfit : rb.toNat + w * 2 ^ zOf nt us ≤ 2 ^ 64)
    (hσw : 15 ≤ nt → nt ≤ 18 → ∀ o ko, σ.kheap o = some ko →
      o.toNat + 2 ^ Fl4Spec.objBits ko ≤ rb.toNat ∨ rb.toNat + w * 2 ^ zOf nt us ≤ o.toNat)
    (hKs : 15 ≤ nt → nt ≤ 18 → rb.toNat + w * 2 ^ zOf nt us ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ rb.toNat)
    (hPa : 15 ≤ nt → nt ≤ 18 → layout.PPTR_BASE.val ≤ rb.toNat) :
    EptCore (L := L) (RetTabs nt us rb w ∪ X) (RetLvl nt us rb w XL) Z'.th s' σ' := by
  obtain ⟨k, dslot, cj, hk, hAk, ⟨uu, -, hcj⟩, hcw, hdsC, hw, hThX, -, hE, hcaps, -, ⟨σB, o, hA, hO, hcnk, hkc⟩,
    hOK, hN, -, -⟩ := R
  subst hk
  obtain ⟨hP, ⟨-, -, hM, -, -⟩, -⟩ := B.xtop.rel
  have hk1 : 1 ≤ 2 ^ zOf nt us := Nat.one_le_two_pow
  have hpos : ∀ q kd, Z.th q = some kd → 0 < objSize kd := by
    intro q kd h
    rcases B.thk q kd h with rfl | ⟨r0, rfl⟩
    · simp [objSize]
    · simp only [objSize]; positivity
  obtain ⟨-, hnew⟩ := hThX.retGrow hpos rfl
  have hsl : ∀ y, IsSlot Z.th y → IsSlot Z'.th y := fun y hy => IsSlot.thMono hThX hk1 hpos hy
  have htU : 15 ≤ nt → t ≠ .untyped := fun h e => by
    have := (objTypeOf_fl4 hty 0).2.2.2.1.1 e; omega
  have h12 : 15 ≤ nt → nt ≤ 18 → 2 ^ zOf nt us = 4096 := fun h1 h2 => by simp [zOf_ept h1 h2]
  -- the new tables
  set T := RetTabs nt us rb w with hTdef
  have hTv : ∀ u ∈ T, (15 ≤ nt ∧ nt ≤ 18) ∧ ∃ j, j < w ∧ u.val = rb.toNat + j * 4096 := by
    rintro u ⟨hE', j, hj, e⟩
    exact ⟨hE', j, hj, by rw [e, h12 hE'.1 hE'.2]⟩
  have hTm : ∀ j, j < w → 15 ≤ nt → nt ≤ 18 →
      (⟨BitVec.ofNat 64 (rb.toNat + j * 4096)⟩ : U64) ∈ T ∧
      (⟨BitVec.ofNat 64 (rb.toNat + j * 4096)⟩ : U64).val = rb.toNat + j * 4096 := by
    intro j hj h1 h2
    have hjk : (j + 1) * 4096 ≤ w * 4096 := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have hf := hfit; rw [h12 h1 h2] at hf
    have e := ejOf_val (A := rb.toNat) (j := j) (by omega)
    exact ⟨⟨⟨h1, h2⟩, j, hj, by rw [e, h12 h1 h2]⟩, e⟩
  have hTb : ∀ u ∈ T, rb.toNat ≤ u.val ∧ u.val + 4096 ≤ rb.toNat + w * 2 ^ zOf nt us ∧ u.val % 4096 = 0 := by
    intro u hu
    obtain ⟨⟨h1, h2⟩, j, hj, e⟩ := hTv u hu
    have hjk : (j + 1) * 4096 ≤ w * 4096 := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have ha := hAk; rw [h12 h1 h2] at ha
    rw [h12 h1 h2]; omega
  have hTX : ∀ u ∈ T, u ∉ X := fun u hu hx => by
    have := hTb u hu
    rcases hXw u hx with h | h <;> omega
  have hTr : ∀ u ∈ T, u.bv ∈ regionPtrs rb w (2 ^ zOf nt us) := fun u hu => by
    obtain ⟨-, j, hj, e⟩ := hu
    exact (mem_regionPtrs rb rb.toNat _ w rfl hk1 hfit u).2 ⟨j, hj, e⟩
  -- the window caps
  have hwinE : ∀ j, j < w → 15 ≤ nt → nt ≤ 18 → capV (L.mem s') (dslot j) =
      .Ept ⟨BitVec.ofNat 64 (rb.toNat + j * 4096)⟩ (eptLvl nt) false 0#u64 0#u64 :=
    fun j hj h1 h2 => by rw [hcw j hj, hcj]; exact (capsOf_eptW hn14 uu dev _ _ j X).1 h1 h2
  have hwinN : ∀ j, j < w → (nt < 15 ∨ 18 < nt) → EptCapX X (capV (L.mem s') (dslot j)) ∧
      (∀ p l m a v, capV (L.mem s') (dslot j) ≠ .Ept p l m a v) ∧
      (∀ p sz r d e a v, capV (L.mem s') (dslot j) ≠ .Frame p sz r d true e a v) :=
    fun j hj h => by rw [hcw j hj, hcj]; exact (capsOf_eptW hn14 uu dev _ _ j X).2 h
  -- the `Ept` and mapped frame caps after: old ones, or a window cap to a new table
  have cE : ∀ y, IsSlot Z'.th y → ∀ p l (mm : Bool) a v, capV (L.mem s') y = .Ept p l mm a v →
      (IsSlot Z.th y ∧ capV (L.mem s) y = .Ept p l mm a v) ∨
      ((15 ≤ nt ∧ nt ≤ 18) ∧ ∃ j, j < w ∧ y = dslot j ∧ p = ⟨BitVec.ofNat 64 (rb.toNat + j * 4096)⟩ ∧
        l = eptLvl nt ∧ mm = false) := by
    intro y hy p l mm a v h
    rcases hcaps y hy (by rw [h]; exact fun e => by cases e) with ⟨j, hj, rfl⟩ | ⟨hy0, e | ⟨-, p0, sb0, fi0, fi1, d0, -, e⟩⟩
    · by_cases hE' : 15 ≤ nt ∧ nt ≤ 18
      · rw [hwinE j hj hE'.1 hE'.2] at h
        obtain ⟨rfl, rfl, rfl, -, -⟩ := capability.Cap.Ept.inj h
        exact Or.inr ⟨hE', j, hj, rfl, rfl, rfl, rfl⟩
      · exact absurd h ((hwinN j hj (by omega)).2.1 _ _ _ _ _)
    · exact Or.inl ⟨hy0, by rw [← e]; exact h⟩
    · rw [e] at h; cases h
  have cF : ∀ y, IsSlot Z'.th y → ∀ p sz r d (e : Bool) a v, capV (L.mem s') y = .Frame p sz r d true e a v →
      IsSlot Z.th y ∧ capV (L.mem s) y = .Frame p sz r d true e a v := by
    intro y hy p sz r d e a v h
    rcases hcaps y hy (by rw [h]; exact fun e => by cases e) with ⟨j, hj, rfl⟩ | ⟨hy0, e' | ⟨-, p0, sb0, fi0, fi1, d0, -, e'⟩⟩
    · by_cases hE' : 15 ≤ nt ∧ nt ≤ 18
      · rw [hwinE j hj hE'.1 hE'.2] at h; cases h
      · exact absurd h ((hwinN j hj (by omega)).2.2 _ _ _ _ _ _ _)
    · exact ⟨hy0, by rw [← e']; exact h⟩
    · rw [e'] at h; cases h
  have cK : ∀ y, IsSlot Z.th y → ∀ p l (mm : Bool) a v, capV (L.mem s) y = .Ept p l mm a v →
      capV (L.mem s') y = .Ept p l mm a v := by
    intro y hy p l mm a v h
    have hm : y ∈ Z.G.chains.flatten := (hM.members y).2 ⟨hy, _, capAt_capV _ y, by rw [h]; exact fun e => by cases e⟩
    exact (hE.keep y hm (by rw [h]; rfl)).2.trans h
  have cX : ∀ y, IsSlot Z'.th y → EptCapX (T ∪ X) (capV (L.mem s') y) := by
    intro y hy
    by_cases h0 : capV (L.mem s') y = .Null
    · rw [h0]; trivial
    rcases hcaps y hy h0 with ⟨j, hj, rfl⟩ | ⟨hy0, e | ⟨-, p0, sb0, fi0, fi1, d0, -, e⟩⟩
    · by_cases hE' : 15 ≤ nt ∧ nt ≤ 18
      · rw [hwinE j hj hE'.1 hE'.2]; exact Or.inl (hTm j hj hE'.1 hE'.2).1
      · exact eptCapX_mono Set.subset_union_right (hwinN j hj (by omega)).1
    · rw [e]; exact eptCapX_mono Set.subset_union_right (C.exte.cap y hy0)
    · rw [e]; trivial
  -- the spec: new objects are the window's (tables only for 15..18), the archState kept
  have hobjA : ∀ r ao, σ'.kheap r = some (.archObj ao) → σB.kheap r = some (.archObj ao) := fun r ao h => by
    rcases hkc r with e | ⟨_, _, _, -, e2⟩
    · rw [← e]; exact h
    · rw [h] at e2; cases e2
  have hobjN : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
      σ.kheap r = some (.archObj (.ept l es)) ∨
        (r ∈ regionPtrs rb w (2 ^ zOf nt us) ∧ (15 ≤ nt ∧ nt ≤ 18) ∧ es = fun _ => 0) := fun r l es h => by
    rcases hA.kback (hobjA r _ h) with h' | ⟨⟨hq, htu⟩, h'⟩
    · exact Or.inl h'
    · have hok := hOK htu r _ (hO r hq htu)
      rw [← h'] at hok
      obtain ⟨h1, h2⟩ := hok.2.2.1 l es rfl
      have e := hok.2.2.2 h1 h2
      cases e
      exact Or.inr ⟨hq, ⟨h1, h2⟩, rfl⟩
  have hpoolO : ∀ r f, σ'.kheap r = some (.archObj (.asidPool f)) → σ.kheap r = some (.archObj (.asidPool f)) :=
    fun r f h => by
      rcases hA.kback (hobjA r _ h) with h' | ⟨⟨hq, htu⟩, h'⟩
      · exact h'
      · exact absurd h'.symm ((hOK htu r _ (hO r hq htu)).2.1 f)
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
  have hσt : ∀ u ∈ T, σ'.kheap u.bv = some (.archObj (.ept (RetLvl nt us rb w XL u) (fun _ => 0))) := by
    intro u hu
    obtain ⟨⟨h1, h2⟩, -⟩ := hTv u hu
    have hq := hTr u hu
    have hB := (hA.new _ ⟨hq, htU h1⟩).2
    have e := (hOK (htU h1) _ _ (hO _ hq (htU h1))).2.2.2 h1 h2
    have hL : RetLvl nt us rb w XL u = (eptLvl nt).val := by unfold RetLvl; rw [if_pos hu]
    rw [hL, ← e]
    rcases hkc u.bv with e' | ⟨r, cs, cs', e1, -⟩
    · rw [e', hB]
    · rw [hB, e] at e1; cases e1
  have hXL : ∀ u ∈ X, RetLvl nt us rb w XL u = XL u := fun u hu => by
    unfold RetLvl; rw [if_neg (fun h => hTX u h hu)]
  have hu4 : ∀ j, j < w → 15 ≤ nt → nt ≤ 18 → rb.toNat + j * 4096 < 2 ^ 64 := fun j hj h1 h2 => by
    have hjk : (j + 1) * 4096 ≤ w * 4096 := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have hf := hfit; rw [h12 h1 h2] at hf; omega
  have hsep : ∀ u ∈ T ∪ X, ∀ o' ko, σ'.kheap o' = some ko → o' ≠ u.bv → EptApart u o' ko := by
    intro u hu o' ko' ho hne
    have hB : ∃ ko0, σB.kheap o' = some ko0 ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko0 := by
      rcases hkc o' with e | ⟨r, cs, cs', e1, e2⟩
      · exact ⟨ko', by rw [← e]; exact ho, rfl⟩
      · rw [ho] at e2; cases e2; exact ⟨_, e1, by simp [Fl4Spec.objBits]⟩
    obtain ⟨ko0, hk0, hb0⟩ := hB
    unfold EptApart
    rw [hb0]
    rcases hA.kback hk0 with h | ⟨⟨hq, htu⟩, hko⟩
    · rcases hu with hu | hu
      · obtain ⟨⟨h1, h2⟩, -⟩ := hTv u hu
        have := hTb u hu
        rcases hσw h1 h2 o' ko0 h with h' | h' <;> omega
      · exact C.sep u hu o' ko0 h hne
    · have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) (hob htu _ _ (hO _ hq htu))
      obtain ⟨j', hj', rfl⟩ := regionPtrs_mem hq
      have hjk : (j' + 1) * 2 ^ zOf nt us ≤ w * 2 ^ zOf nt us := Nat.mul_le_mul_right _ hj'
      rw [Nat.add_mul, Nat.one_mul] at hjk
      have e := ptrAdd_toNat (rb := rb) (n := j' * 2 ^ zOf nt us) (by omega)
      rw [hko, e]
      rcases hu with hu | hu
      · obtain ⟨⟨h1, h2⟩, j, hj, hjv⟩ := hTv u hu
        have hne' : j' ≠ j := fun ej => hne (by
          subst ej
          apply BitVec.eq_of_toNat_eq
          rw [e, h12 h1 h2]; exact hjv.symm)
        rw [h12 h1 h2] at hp hjk ⊢
        rcases Nat.lt_or_gt_of_ne hne' with hl | hl
        · have : (j' + 1) * 4096 ≤ j * 4096 := Nat.mul_le_mul_right _ hl
          omega
        · have : (j + 1) * 4096 ≤ j' * 4096 := Nat.mul_le_mul_right _ hl
          omega
      · rcases hXw u hu with h | h <;> omega
  have h5 : EptSlotStep Z.th Z'.th (L.mem s) (L.mem s') := by
    intro t0 ht0
    by_cases hT0 : Z.th t0 = some .tcb
    · have hAs : AbsSlot Z.th (t0.bv, Fl4Spec.tcbCnodeIndex 5) := ⟨t0, rfl, Or.inr ⟨hT0, 5, by decide, rfl⟩⟩
      have hy := hAs.isSlot
      rcases C.eslot t0 hT0 with h | ⟨p0, a0, v0, h⟩
      · by_cases h0 : capV (L.mem s') (cslotAddr (t0.bv, Fl4Spec.tcbCnodeIndex 5)) = .Null
        · exact Or.inl h0
        exfalso
        rcases hcaps _ (hsl _ hy) h0 with ⟨j, hj, ey⟩ | ⟨-, e | ⟨-, p1, sb1, fi1, fi2, d1, e, -⟩⟩
        · obtain ⟨q, r, hq, i, hi, eq⟩ := hdsC j hj
          obtain ⟨p2, i2, hi2, hp2, hy2⟩ := hAs.at
          obtain ⟨e1, -⟩ := slotOf_inj hP hi2 (Or.inl ⟨r, hq, hi⟩) (hy2.symm.trans (ey.trans eq))
          have e2 : t0 = p2 := UScalar.eq_of_val_eq (congrArg BitVec.toNat hp2)
          rw [e2, e1, hq] at hT0; cases hT0
        · exact h0 (e.trans h)
        · rw [h] at e; cases e
      · exact Or.inr (Or.inr ⟨hT0, (cK _ hy _ _ _ _ _ h).trans h.symm⟩)
    · have hnone := ((hnew t0 _ ht0).resolve_left hT0).1
      have hAs' : AbsSlot Z'.th (t0.bv, Fl4Spec.tcbCnodeIndex 5) := ⟨t0, rfl, Or.inr ⟨ht0, 5, by decide, rfl⟩⟩
      obtain ⟨p2, i2, hi2, hp2, hy2⟩ := hAs'.at
      have e2 : t0 = p2 := UScalar.eq_of_val_eq (congrArg BitVec.toNat hp2)
      subst e2
      exact Or.inl (by rw [hy2]; exact hN.1 t0 i2 hi2 hnone)
  have hX' : JExtEpt (L := L) (T ∪ X) Z'.th s' := by
    refine ⟨cX, ⟨fun y hy p l a v h => ?_, fun y hy p sz r d a v h => ?_⟩, fun y hy p l a v h => ?_⟩
    · rcases cE y hy _ _ _ _ _ h with ⟨hy0, h0⟩ | ⟨-, -, -, -, -, -, hm⟩
      · exact C.exte.vtop.1 y hy0 p l a v h0
      · cases hm
    · obtain ⟨hy0, h0⟩ := cF y hy _ _ _ _ _ _ _ h
      exact C.exte.vtop.2 y hy0 p sz r d a v h0
    · rcases cE y hy _ _ _ _ _ h with ⟨hy0, h0⟩ | ⟨-, -, -, -, -, -, hm⟩
      · exact C.exte.anz y hy0 p l a v h0
      · cases hm
  have hnm : EptNamed Z'.th (L.mem s') σ' :=
    C.named.retGrow C.walk
      (GPath.mono' (fun hi lo e he _ => by
          obtain ⟨p0, f, h1, h2, h3⟩ := he
          exact Or.inl ⟨p0, f, by rw [← hat]; exact h1, hpoolO _ _ h2, h3⟩)
        (fun r l es h => (hobjN r l es h).imp id fun h' => h'.2.2))
      (C.named.inj.mono hat fun hi lo e he _ => by
          obtain ⟨p0, f, h1, h2, h3⟩ := he
          exact ⟨p0, f, by rw [← hat]; exact h1, hpoolO _ _ h2, h3⟩)
      (fun y p lv a v hy hc _ => ⟨y, hsl y hy, cK y hy _ _ _ _ _ hc⟩)
      (fun y p lv mm a v hy hc => by
        rcases cE y hy _ _ _ _ _ hc with h | ⟨⟨h1, h2⟩, j, hj, -, rfl, -, -⟩
        · exact Or.inl ⟨y, h⟩
        · exact Or.inr (hA.new _ ⟨hTr _ (hTm j hj h1 h2).1, htU h1⟩).1)
  refine C.growS hTX (RetLvl nt us rb w XL) hXL hw hF (fun u hu => ?_) (fun u hu i => ?_) hσt hxk
    (fun r l es h => ?_) (fun y hy p l a v mm h => ?_) (fun u hu y y' hy hy' l1 l2 a1 a2 v1 v2 m1 m2 h1 h2 => ?_) hX'
    (fun e he => ?_) (fun u hu => ?_) hsep h5 hnm (fun u hu => ?_)
  · have := hTb u hu; exact ⟨this.2.2, by omega⟩
  · obtain ⟨⟨h1, h2⟩, -⟩ := hTv u hu
    have hb := hTb u hu
    have e := eptA_val (t := u) (by omega) i
    have hi9 := i.isLt
    exact hN.2.2 h1 h2 _ (by unfold P1.Aligned; rw [e]; omega) (by rw [e]; omega) (by rw [e]; omega)
  · rcases hobjN r l es h with h' | ⟨hq, ⟨h1, h2⟩, -⟩
    · exact Or.inr ⟨l, es, h'⟩
    · obtain ⟨j, hj, rfl⟩ := regionPtrs_mem hq
      have hjk : (j + 1) * 2 ^ zOf nt us ≤ w * 2 ^ zOf nt us := Nat.mul_le_mul_right _ hj
      rw [Nat.add_mul, Nat.one_mul] at hjk
      have e := ptrAdd_toNat (rb := rb) (n := j * 2 ^ zOf nt us) (by omega)
      exact Or.inl ⟨⟨Fl4Spec.ptrAdd rb (j * 2 ^ zOf nt us)⟩, ⟨⟨h1, h2⟩, j, hj, e⟩, rfl⟩
  · rcases cE y hy _ _ _ _ _ h with h' | ⟨⟨h1, h2⟩, j, hj, -, rfl, rfl, -⟩
    · exact Or.inr h'
    · have hL : RetLvl nt us rb w XL ⟨BitVec.ofNat 64 (rb.toNat + j * 4096)⟩ = (eptLvl nt).val := by
        unfold RetLvl; rw [if_pos (hTm j hj h1 h2).1]
      exact Or.inl ⟨(hTm j hj h1 h2).1, hL.symm⟩
  · rcases cE y hy _ _ _ _ _ h1 with ⟨hy0, h0⟩ | ⟨⟨g1, g2⟩, j, hj, ey, eu, -, -⟩
    · exact absurd (by have := C.exte.cap y hy0; rw [h0] at this; exact this) (hTX u hu)
    rcases cE y' hy' _ _ _ _ _ h2 with ⟨hy0, h0⟩ | ⟨-, j', hj', ey', eu', -, -⟩
    · exact absurd (by have := C.exte.cap y' hy0; rw [h0] at this; exact this) (hTX u hu)
    have ev1 := congrArg UScalar.val eu
    have ev2 := congrArg UScalar.val eu'
    rw [(hTm j hj g1 g2).2] at ev1
    rw [(hTm j' hj' g1 g2).2] at ev2
    have : j = j' := by omega
    rw [ey, ey', this]
  · obtain ⟨hi, p0, f, lo, h1, h2, h3⟩ := he
    exact ⟨hi, p0, f, lo, by rw [← hat]; exact h1, hpoolO _ _ h2, h3⟩
  · obtain ⟨⟨h1, h2⟩, -⟩ := hTv u hu
    have := hTb u hu
    rw [hw.1]
    rcases hKs h1 h2 with h | h <;> omega
  · obtain ⟨⟨h1, h2⟩, -⟩ := hTv u hu
    have hb := hTb u hu
    have hL : RetLvl nt us rb w XL u = (eptLvl nt).val := by unfold RetLvl; rw [if_pos hu]
    refine ⟨?_, pam_win (Or.inl rfl) Vs.mask_small_bits ((paddrN_lt (le_trans (hPa h1 h2) hb.1)).trans
      (by norm_num)) (by rw [show (2 : Nat) ^ 12 = 4096 by norm_num]; exact hb.2.2)⟩
    rw [hL]
    unfold eptLvl
    by_cases e15 : nt = 15
    · rw [if_pos e15]; left; rfl
    · rw [if_neg e15]
      by_cases e16 : nt = 16
      · rw [if_pos e16]; right; left; rfl
      · rw [if_neg e16]
        by_cases e17 : nt = 17
        · rw [if_pos e17]; right; right; left; rfl
        · rw [if_neg e17]; right; right; right; rfl

/-- **`VmEptState` across a retype of a type other than the VCPU** (the Architect's item (h), types 0..13 and
15..18): from `VmEptState V X XL` at the entry, `JAtZB` after and the window the body wrote, with the consumers'
footprint predicates (`RetFootV`, `RetFootE`), the window apart from the VCPUs, the tables, the kernel-global area and
every spec object, and the new objects' size: `VmEptState V (RetTabs ∪ X) (RetLvl XL)` after (`VcpuCore.ofRet`,
`EptCore.ofRet`). -/
theorem VmEptState.ofRet (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {Z' : XSets} {H' : P1.Heap} {Cs' Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (B' : JAtZB (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σ')
    {W : U64 → Prop} {O : Fl4Spec.ObjRef → Fl4Spec.KernelObject → Prop} {xs : U64} {nt : Nat}
    {t : Fl4Spec.ApiObjectType} {us : Nat} {rb : Fl4Spec.ObjRef} {w : Nat} {dev : Bool}
    (R : RetWin (L := L) Z.th Z'.th Z.G Z'.G H H' σ σ' s s' W O xs nt t us rb w dev)
    (hFV : RetFootV (L := L) V Z.th s W) (hFE : RetFootE X W) (hty : objTypeOf nt = some t) (hn14 : nt ≠ 14)
    (hVw : ∀ v ∈ V, v.val + 32768 ≤ rb.toNat ∨ rb.toNat + w * 2 ^ zOf nt us ≤ v.val)
    (hXw : ∀ u ∈ X, u.val + 4096 ≤ rb.toNat ∨ rb.toNat + w * 2 ^ zOf nt us ≤ u.val)
    (hKw : rb.toNat + w * 2 ^ zOf nt us ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ rb.toNat)
    (hob : t ≠ .untyped → ∀ q ko, O q ko → Fl4Spec.objBits ko ≤ zOf nt us)
    (hfit : rb.toNat + w * 2 ^ zOf nt us ≤ 2 ^ 64)
    (hσw : 15 ≤ nt → nt ≤ 18 → ∀ o ko, σ.kheap o = some ko →
      o.toNat + 2 ^ Fl4Spec.objBits ko ≤ rb.toNat ∨ rb.toNat + w * 2 ^ zOf nt us ≤ o.toNat)
    (hKs : 15 ≤ nt → nt ≤ 18 → rb.toNat + w * 2 ^ zOf nt us ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ rb.toNat)
    (hPa : 15 ≤ nt → nt ≤ 18 → layout.PPTR_BASE.val ≤ rb.toNat) :
    VmEptState (L := L) arI V (RetTabs nt us rb w ∪ X) (RetLvl nt us rb w XL) AR Z' H' Cs' Ac' Lst' D' s' a' σ' :=
  ⟨⟨B', VcpuCore.ofRet J.1.1 J.1.2 B' R hFV hn14 hVw hKw hob hfit⟩,
    EptCore.ofRet J.1.1 J.2 R hFE hty hn14 hXw hob hfit hσw hKs hPa⟩

/-- **`VmEptState` after a body's `UtBodyPostB`** (types 0..13, 15..18, RAM source): the spec's outcome, `Ok`, and
`VmEptState V (RetTabs ∪ X) (RetLvl XL)` at the state after, from the body's post, the source an `AbsSlot`, the
consumers' predicates at its footprint and the object predicate's size bound (`hob`); the window's facts from the
source (`JAtZB.winV`, `winX`, `winFree`, `winKs`, `winPa`, `UtCapP3.pfit`). -/
theorem VmEptState.ofPost (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) {nt : Nat}
    {Xp : XSets → P1.Heap → Set U64 → S → Fl4Spec.State Unit → Prop} {W : Nat → Nat → U64 → Prop}
    {O : Fl4Spec.ApiObjectType → Bool → Nat → Fl4Spec.ObjRef → Fl4Spec.KernelObject → Prop}
    {src : Fl4Spec.CslotPtr} {rs : Bool} {pb rb : Fl4Spec.ObjRef} {t : Fl4Spec.ApiObjectType} {us : Nat}
    {slots : List Fl4Spec.CslotPtr} {res : core.result.Result Unit error.Exc × S × A}
    (h : UtBodyPostB (L := L) arI AR Z.th Z.G H s σ nt Xp W O (.retype src rs pb rb t us slots false) res)
    (hAs : AbsSlot Z.th src)
    (hFV : RetFootV (L := L) V Z.th s (W rb.toNat (rb.toNat + slots.length * 2 ^ zOf nt us)))
    (hFE : RetFootE X (W rb.toNat (rb.toNat + slots.length * 2 ^ zOf nt us)))
    (hty : objTypeOf nt = some t) (hn14 : nt ≠ 14)
    (hob : t ≠ .untyped → ∀ q ko, O t false us q ko → Fl4Spec.objBits ko ≤ zOf nt us) :
    ∃ σ', (Fl4Spec.fl4InvokeUntypedV (Z := Unit) (.retype src rs pb rb t us slots false)).run σ =
        ({(.ok (), σ')}, False) ∧
      res.1 = .Ok () ∧ ∃ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        VmEptState (L := L) arI V (RetTabs nt us rb slots.length ∪ X) (RetLvl nt us rb slots.length XL) AR Z' H' Cs'
          Ac' Lst' D' res.2.1 res.2.2 σ' := by
  obtain ⟨σ', hrun, hok, -, Z', H', Cs', Ac', Lst', D', B', -, -, -, hR⟩ := h
  have R := hR _ _ _ _ _ _ _ _ rfl
  obtain ⟨k, -, -, hk, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨p, sb, fi, hsrc, h1, h2⟩, -⟩ := id R
  subst hk
  have hcap : capAt (L.mem s) (cslotAddr src) = ok (.Untyped p sb fi false) := by rw [capAt_capV, hsrc]
  have hfit := (J.1.1.utc _ p sb fi false hAs hcap rfl).pfit
  have hW := J.1.1.winFree hAs hcap h1 h2
  exact ⟨σ', hrun, hok, Z', H', Cs', Ac', Lst', D',
    J.ofRet B' R hFV hFE hty hn14 (J.1.1.winV J.1.2.vm hAs hcap h1 h2) (J.1.1.winX J.2 hAs hcap h1 h2) hW.2.2 hob
      (by omega) (fun _ _ => hW.1) (fun _ _ => J.1.1.winKs hAs hcap h1 h2) (fun _ _ => J.1.1.winPa hAs hcap h1)⟩

/-- `VmEptState.ofPost` for a type adding no guest table (0..13): `X`, `XL` unchanged. -/
theorem VmEptState.ofPostN (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) {nt : Nat}
    {Xp : XSets → P1.Heap → Set U64 → S → Fl4Spec.State Unit → Prop} {W : Nat → Nat → U64 → Prop}
    {O : Fl4Spec.ApiObjectType → Bool → Nat → Fl4Spec.ObjRef → Fl4Spec.KernelObject → Prop}
    {src : Fl4Spec.CslotPtr} {rs : Bool} {pb rb : Fl4Spec.ObjRef} {t : Fl4Spec.ApiObjectType} {us : Nat}
    {slots : List Fl4Spec.CslotPtr} {res : core.result.Result Unit error.Exc × S × A}
    (h : UtBodyPostB (L := L) arI AR Z.th Z.G H s σ nt Xp W O (.retype src rs pb rb t us slots false) res)
    (hAs : AbsSlot Z.th src)
    (hFV : RetFootV (L := L) V Z.th s (W rb.toNat (rb.toNat + slots.length * 2 ^ zOf nt us)))
    (hFE : RetFootE X (W rb.toNat (rb.toNat + slots.length * 2 ^ zOf nt us)))
    (hty : objTypeOf nt = some t) (hn13 : nt ≤ 13)
    (hob : t ≠ .untyped → ∀ q ko, O t false us q ko → Fl4Spec.objBits ko ≤ zOf nt us) :
    ∃ σ', (Fl4Spec.fl4InvokeUntypedV (Z := Unit) (.retype src rs pb rb t us slots false)).run σ =
        ({(.ok (), σ')}, False) ∧
      res.1 = .Ok () ∧ ∃ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        VmEptState (L := L) arI V X XL AR Z' H' Cs' Ac' Lst' D' res.2.1 res.2.2 σ' := by
  have hn : nt < 15 ∨ 18 < nt := Or.inl (by omega)
  have := J.ofPost h hAs hFV hFE hty (by omega) hob
  rwa [retTabs_none hn, retLvl_none hn, Set.empty_union] at this

end

end Fl4Proofs.P3
