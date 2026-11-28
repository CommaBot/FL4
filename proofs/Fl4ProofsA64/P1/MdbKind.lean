/-
P1 (aarch64, gen 47): **the cap-kind typing `KindA`** (beside `RngOneA64`) and **`hone` from the MDB facts**:
ARMPageTableUnmap's "no other slot names the table" hypothesis discharged from `is_final_capability`.

## Why a new state fact (gen 46's finding)

The exact range class `(p, 12)` of a `PageTable p` cap is shared by `Thread p` (A64 TCB bits 12), `Pml4 p`,
`PageDirectory p`, `Pdpt p`, `HighVSpace p`, `AsidPool p` caps, and `same_object_as` between a `PageTable` cap and
any of these is false (objects.rs:84–153), so `RngOneA64`'s contiguity alone does not make the two-neighbour check
of `is_final_capability` (cdt.rs:158–175) exact. Also `NmC` (the unmap's "names `ptr`") includes `Ept ptr …` caps,
whose class is `(ptr, 13)` (`STAGE2_VSPACE`), outside the `PageTable` class altogether.

**Checked first: can it be derived from the existing A64 invariants?** Only partly. `DelCapOK` (in `SlotTy`) types
`Thread p` caps (`p ∈ T`, and `T ⊆ OS` in `SlotTyEntE`), `UnmZ.pt` types *unmapped* `PageTable p` caps (`p ∈ Pt`, and
`VrOK.os`: no `VsR` word lies in an `OS` slot), so `Thread p` versus an *unmapped* `PageTable p` is contradictory
from existing facts. But no A64 invariant types the objects of *mapped* `PageTable` caps, nor of `Pml4` /
`PageDirectory` / `Pdpt` / `HighVSpace` / `AsidPool` / non-level-0 `Ept` caps (`DelCapOK` / `CapTyped` cover Thread,
CNode, Zombie, IRQ, IO-port, endpoint/notification/reply caps only; `UnmZ` / `UnmU` only unmapped or level-0 caps;
`VsTy` / `S2Ty` type tables, not caps). x86 has no direct analogue either: its `VcpuChunked` is proved for one
constructor (`Vcpu v`, `soB_vcpu_left/right`) from P3's tree invariant `MdbInv` and typed heap, neither of which
A64 carries. Hence, per the brief, a **new step-preserved state fact next to `RngOneA64`**, not in `SlotTyEnt*`:

* `kindA c`: the cap's constructor (its object kind).
* **`KindA st OS s`**: two `OS` slots holding `RngKeyA` caps (physical, not untyped, not a frame) with the same base
  `ptrA` hold caps of the same kind. (l4v: `valid_cap` against the typed heap + `obj_refs` disjointness; FL4 source:
  `create_new_objects` retypes disjoint free regions of an untyped, one object kind per region (untyped.rs), caps
  to an object are only derived from caps to it (`derive_cap` / `update_cap_data` keep the constructor and `ptr`,
  objects.rs), a region is reused only after `reset` of a childless untyped, i.e. after every cap to its old objects
  was deleted. Stated with the base, not the class, so it also separates `PageTable p` from `Ept p …`.)
* Boot `KindA.empty`; preservation `KindA.keep` (each slot's key, base and kind kept), the in-place `set_cap`
  instance `KindA.set_cap` (ARMPageTableUnmap / Map / `Assign` rewrite a `PageTable` cap as a `PageTable` cap of the
  same object: `kindA_pt`, `ptrA_pt`).

## `hone`

* `KindA.pt_of`: a `RngKeyA` cap with base `p` beside a `PageTable p` cap is a `PageTable p` cap.
* **`MdbLk.pt_nb`**: under `MdbLk ∧ RngOneA64 ∧ KindA`, if slot `x` holds `PageTable p` and another `OS` slot holds
  `PageTable p`, then a chain neighbour of `x` (its `NEXT` or its `PREV` word) is an `OS` slot holding `PageTable p`
  (`one` puts both in one chain, `chunk` fills the positions between them with class `(p, 12)` caps, `KindA` makes
  those `PageTable p` caps).
* `is_final.false_next` / `is_final.false_prev`: `is_final_capability` is `false` when a non-null neighbour holds a
  cap `same_object_as` the slot's (`so_pt`).
* **`is_final.false_nm`**: if another `OS` slot names `ptr` (`NmC`) then `is_final_capability` of a `PageTable ptr`
  slot is `false`; hence **`hone_of_final`**.
* **`vspace.decode_page_table.unmapRF`**: gen 46's `unmapR` with the `hone` hypothesis replaced by
  `MdbLk ∧ RngOneA64 ∧ KindA` and `h0` (no `OS` slot at address 0; the null test of `is_final` reads 0 as "no
  neighbour"); if `hone` fails, the cap is not final and the decode returns the state unchanged.

Not derivable from these facts: `UnmU.one` (an unmapped cap is the only cap of its object). Two adjacent unmapped
`PageTable p` caps in one chain satisfy `MdbLk`, `RngOneA64` and `KindA`; uniqueness comes from `derive_cap`
refusing unmapped `PageTable` / `Ept` caps (seL4 `Arch_deriveCap`), a fact of `cdt::insert`'s callers, not of the
chain shape. `unmapR0` (unmapped caps) keeps taking it from `UnmU`.

Named premises: none. New definitions `kindA`, `KindA` (state fact, to be conjoined as
`JV ∧ MdbLk ∧ RngOneA64 ∧ KindA`); case hypothesis `h0` of `unmapRF` (state-free placement).
-/
import Fl4ProofsA64.P1.MdbA64
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-! ## The cap's kind and `KindA` -/

/-- The cap's constructor: the kind of object it names. -/
def kindA : capability.Cap → Nat
  | .Null => 0
  | .Untyped .. => 1
  | .Endpoint .. => 2
  | .Notification .. => 3
  | .Reply .. => 4
  | .CNode .. => 5
  | .Thread .. => 6
  | .IrqControl => 7
  | .IrqHandler .. => 8
  | .Zombie .. => 9
  | .Domain => 10
  | .SchedContext .. => 11
  | .SchedControl .. => 12
  | .Frame .. => 13
  | .PageTable .. => 14
  | .PageDirectory .. => 15
  | .Pdpt .. => 16
  | .Pml4 .. => 17
  | .Vcpu .. => 18
  | .Ept .. => 19
  | .AsidControl => 20
  | .AsidPool .. => 21
  | .IoPortControl => 22
  | .IoPort .. => 23
  | .TdxControl => 24
  | .HighVSpace .. => 25

/-- **`KindA`** (module docstring): `RngKeyA` caps of one base name objects of one kind. -/
structure KindA (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) : Prop where
  kind : ∀ x ∈ OS, ∀ y ∈ OS, RngKeyA (capA st s x) → RngKeyA (capA st s y) →
    ptrA (capA st s x) = ptrA (capA st s y) → kindA (capA st s x) = kindA (capA st s y)

theorem RngKeyA.not_null : ¬ RngKeyA .Null := by
  intro h
  have e := physA_eq .Null
  simp only [objects.cap_is_physical] at e
  have := h.1; rw [← okinj e] at this; exact Bool.false_ne_true this

theorem RngKeyA.ept (p l : U64) (m : Bool) (a v : U64) : RngKeyA (.Ept p l m a v) := by
  have h := physA_eq (.Ept p l m a v)
  simp only [objects.cap_is_physical] at h
  exact ⟨(okinj h).symm, rfl, rfl⟩

theorem ptrA_pt (p : U64) (m : Bool) (a v : U64) : ptrA (.PageTable p m a v) = p := by
  have h := ptrA_eq (.PageTable p m a v)
  simp only [capability.Cap.ptr] at h
  exact (okinj h).symm

theorem ptrA_ept (p l : U64) (m : Bool) (a v : U64) : ptrA (.Ept p l m a v) = p := by
  have h := ptrA_eq (.Ept p l m a v)
  simp only [capability.Cap.ptr] at h
  exact (okinj h).symm

theorem kindA_pt (p : U64) (m : Bool) (a v : U64) : kindA (.PageTable p m a v) = 14 := rfl

/-- **Boot**: no non-null cap in `OS`. -/
theorem KindA.empty {OS : Set U64} {s : S} (h : ∀ x ∈ OS, capA st s x = .Null) : KindA st OS s :=
  ⟨fun x hx _ _ k _ _ => absurd (h x hx ▸ k) RngKeyA.not_null⟩

/-- **`KindA` with each `OS` slot's key, base and kind kept.** -/
theorem KindA.keep {OS : Set U64} {s s' : S} (h : KindA st OS s)
    (hk : ∀ x ∈ OS, (RngKeyA (capA st s' x) ↔ RngKeyA (capA st s x)) ∧
      (RngKeyA (capA st s x) → ptrA (capA st s' x) = ptrA (capA st s x) ∧
        kindA (capA st s' x) = kindA (capA st s x))) : KindA st OS s' := by
  refine ⟨fun x hx y hy kx ky hp => ?_⟩
  have kx0 := (hk x hx).1.1 kx
  have ky0 := (hk y hy).1.1 ky
  obtain ⟨px, cx⟩ := (hk x hx).2 kx0
  obtain ⟨py, cy⟩ := (hk y hy).2 ky0
  rw [cx, cy]
  exact h.kind x hx y hy kx0 ky0 (by rw [← px, ← py]; exact hp)

/-- **`KindA` along an in-place `set_cap`** of a cap with the old cap's key, base and kind. -/
theorem KindA.set_cap {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S} (h : KindA st OS s) {x0 : U64} (hx0 : x0 ∈ OS)
    {c : capability.Cap} {w0 w1 : U64} (hd : capability.Cap.decode w0 w1 = ok c)
    (hk : RngKeyA c ↔ RngKeyA (capA st s x0))
    (hcl : RngKeyA (capA st s x0) → ptrA c = ptrA (capA st s x0) ∧ kindA c = kindA (capA st s x0)) :
    KindA st OS (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) := by
  refine h.keep fun y hy => ?_
  by_cases hyx : y = x0
  · subst hyx
    have e : capA st (L.wr (L.wr s y w0) (wa y 8#u64) w1) y = c := capA_wr2_self hO hx0 hd
    rw [e]; exact ⟨hk, hcl⟩
  · rw [capA_wr2_other hO hx0 hy hyx]; exact ⟨Iff.rfl, fun _ => ⟨rfl, rfl⟩⟩

section nb
variable {OS : Set U64} {G : List (List U64)}

/-- A `RngKeyA` cap with base `p` beside a `PageTable p` cap is a `PageTable p` cap. -/
theorem KindA.pt_of {s : S} (hK : KindA st OS s) {x b p : U64} {m : Bool} {a v : U64} (hx : x ∈ OS) (hb : b ∈ OS)
    (hcx : capA st s x = .PageTable p m a v) (kb : RngKeyA (capA st s b)) (hpb : ptrA (capA st s b) = p) :
    ∃ m' a' v', capA st s b = .PageTable p m' a' v' := by
  have hkd := hK.kind x hx b hb (by rw [hcx]; exact RngKeyA.pt p m a v) kb (by rw [hcx, ptrA_pt, hpb])
  rw [hcx, kindA_pt] at hkd
  revert hkd hpb
  generalize capA st s b = cb
  intro hpb hkd
  cases cb <;> simp only [kindA] at hkd <;> try omega
  rename_i p' m' a' v'
  rw [ptrA_pt] at hpb
  exact ⟨m', a', v', by rw [hpb]⟩

theorem getElem?_of_lt {α : Type _} {l : List α} {i : Nat} (h : i < l.length) : l[i]? = some l[i] := by
  simp [h]

/-- **A chain neighbour holds the same `PageTable`** (module docstring). -/
theorem MdbLk.pt_nb {s : S} (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s)
    {x y p : U64} {m m' : Bool} {a v a' v' : U64} (hx : x ∈ OS) (hy : y ∈ OS) (hne : y ≠ x)
    (hcx : capA st s x = .PageTable p m a v) (hcy : capA st s y = .PageTable p m' a' v') :
    ∃ b ∈ OS, (∃ m a v, capA st s b = .PageTable p m a v) ∧
      (NxA st s x = b ∨ L.mem s (wa x 16#u64) = b) := by
  have kx : RngKeyA (capA st s x) := by rw [hcx]; exact RngKeyA.pt p m a v
  have ky : RngKeyA (capA st s y) := by rw [hcy]; exact RngKeyA.pt p m' a' v'
  have hxG : x ∈ G.flatten := (hM.members x).2 ⟨hx, by rw [hcx]; simp⟩
  have hyG : y ∈ G.flatten := (hM.members y).2 ⟨hy, by rw [hcy]; simp⟩
  have inOS : ∀ ch ∈ G, ∀ (n : Nat) (w : U64), ch[n]? = some w → w ∈ OS := fun ch hch n w e =>
    ((hM.members w).1 (List.mem_flatten.2 ⟨ch, hch, List.mem_of_getElem? e⟩)).1
  obtain ⟨ch, hch, hxc, hyc⟩ := hRO.one x hxG y hyG kx ky (by rw [hcx, hcy, clsA_pt, clsA_pt])
  obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hxc
  obtain ⟨k, hk, hyk⟩ := List.getElem_of_mem hyc
  have ei : ch[i]? = some x := by rw [getElem?_of_lt hi, hxi]
  have ek : ch[k]? = some y := by rw [getElem?_of_lt hk, hyk]
  have hik : i ≠ k := fun e => hne (by subst e; exact hyk.symm.trans hxi)
  have hpx : ptrA (capA st s x) = p := by rw [hcx, ptrA_pt]
  rcases Nat.lt_or_gt_of_ne hik with hlt | hlt
  · have h1 : i + 1 < ch.length := by omega
    have e1 := getElem?_of_lt h1
    have hb := inOS ch hch _ _ e1
    have hcl : RngKeyA (capA st s ch[i + 1]) ∧ ptrA (capA st s ch[i + 1]) = p := by
      by_cases e : i + 1 = k
      · have : ch[i + 1] = y := by rw [← hyk]; congr
        rw [this, hcy, ptrA_pt]; exact ⟨RngKeyA.pt p m' a' v', rfl⟩
      · obtain ⟨kb, cb⟩ := hRO.chunk ch hch i (i + 1) k x _ y ei e1 ek (by omega) (by omega) kx ky
          (by rw [hcx, hcy, clsA_pt, clsA_pt])
        exact ⟨kb, (congrArg Prod.fst cb).trans hpx⟩
    exact ⟨_, hb, hK.pt_of hx hb hcx hcl.1 hcl.2, Or.inl (hM.chain ch hch i x _ ei e1).1⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have h1 : j < ch.length := by omega
    have e1 := getElem?_of_lt h1
    have hb := inOS ch hch _ _ e1
    have hcl : RngKeyA (capA st s ch[j]) ∧ ptrA (capA st s ch[j]) = p := by
      by_cases e : j = k
      · have : ch[j] = y := by rw [← hyk]; congr
        rw [this, hcy, ptrA_pt]; exact ⟨RngKeyA.pt p m' a' v', rfl⟩
      · obtain ⟨kb, cb⟩ := hRO.chunk ch hch k j (j + 1) y _ x ek e1 ei (by omega) (by omega) ky kx
          (by rw [hcx, hcy, clsA_pt, clsA_pt])
        exact ⟨kb, (congrArg Prod.fst cb).trans (by rw [hcy, clsA_pt])⟩
    exact ⟨_, hb, hK.pt_of hx hb hcx hcl.1 hcl.2, Or.inr (hM.chain ch hch j _ x e1 ei).2⟩

end nb

/-! ## `is_final_capability` with a same-object neighbour -/

theorem so_pt (p : U64) (m : Bool) (a v : U64) (m' : Bool) (a' v' : U64) :
    objects.same_object_as (.PageTable p m a v) (.PageTable p m' a' v') = ok true := by
  simp only [objects.same_object_as, objects.same_region_as, if_true]

theorem so_total (c d : capability.Cap) : ∃ q, objects.same_object_as c d = ok q := by
  have h := P0.objects.same_object_as.p0 c d
  revert h
  cases objects.same_object_as c d <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

/-- **Not final: the `NEXT` neighbour holds a same-object cap.** -/
theorem is_final.false_next {s : S} {x b : U64} {c cb : capability.Cap} (hc : capA st s x = c)
    (hnx : NxA st s x = b) (hb0 : b ≠ 0#u64) (hcb : capA st s b = cb)
    (hso : objects.same_object_as c cb = ok true) : cdt.is_final_capability st s x = ok false := by
  unfold cdt.is_final_capability cdt.is_final_capability_with_cap
  rw [capA_eq, bind_ok, slot_prev_eq, bind_ok]
  by_cases hp : L.mem s (wa x 16#u64) = 0#u64
  · simp [obj.Slot.is_null, hp, next_eq, hnx, hb0, capA_eq, hcb, hc, hso]
  · obtain ⟨q, hq⟩ := so_total (capA st s (L.mem s (wa x 16#u64))) c
    cases q <;> simp [obj.Slot.is_null, hp, next_eq, hnx, hb0, capA_eq, hcb, hc, hso, hq]

/-- **Not final: the `PREV` neighbour holds a same-object cap.** -/
theorem is_final.false_prev {s : S} {x b : U64} {c cb : capability.Cap} (hc : capA st s x = c)
    (hpv : L.mem s (wa x 16#u64) = b) (hb0 : b ≠ 0#u64) (hcb : capA st s b = cb)
    (hso : objects.same_object_as cb c = ok true) : cdt.is_final_capability st s x = ok false := by
  unfold cdt.is_final_capability cdt.is_final_capability_with_cap
  rw [capA_eq, bind_ok, slot_prev_eq, bind_ok]
  simp [obj.Slot.is_null, hpv, hb0, capA_eq, hcb, hc, hso]

section fin
variable {OS : Set U64} {G : List (List U64)}

/-- **Another slot names `ptr` ⇒ a `PageTable ptr` slot is not final** (module docstring). -/
theorem is_final.false_nm {s : S} (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s)
    (h0 : ∀ x ∈ OS, x ≠ 0#u64) {x ptr : U64} {m : Bool} {a v : U64} (hx : x ∈ OS)
    (hc : obj.Slot.cap st x s = ok (.PageTable ptr m a v)) {y : U64} (hy : y ∈ OS) (hne : y ≠ x)
    (hn : NmC st y ptr s) : cdt.is_final_capability st s x = ok false := by
  have hcx : capA st s x = .PageTable ptr m a v := okinj ((capA_eq s x).symm.trans hc)
  rcases hn with ⟨m', a', v', hy'⟩ | ⟨l, m', a', v', hy'⟩
  · have hcy : capA st s y = .PageTable ptr m' a' v' := okinj ((capA_eq s y).symm.trans hy')
    obtain ⟨b, hb, ⟨m2, a2, v2, hcb⟩, hl⟩ := hM.pt_nb hRO hK hx hy hne hcx hcy
    rcases hl with hl | hl
    · exact is_final.false_next hcx hl (h0 b hb) hcb (so_pt _ _ _ _ _ _ _)
    · exact is_final.false_prev hcx hl (h0 b hb) hcb (so_pt _ _ _ _ _ _ _)
  · have hcy : capA st s y = .Ept ptr l m' a' v' := okinj ((capA_eq s y).symm.trans hy')
    have := hK.kind x hx y hy (by rw [hcx]; exact RngKeyA.pt _ _ _ _) (by rw [hcy]; exact RngKeyA.ept _ _ _ _ _)
      (by rw [hcx, hcy, ptrA_pt, ptrA_ept])
    rw [hcx, hcy] at this; simp [kindA] at this

/-- **`hone` from finality**: a final `PageTable ptr` slot is the only `OS` slot naming `ptr`. -/
theorem hone_of_final {s : S} (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s)
    (h0 : ∀ x ∈ OS, x ≠ 0#u64) {x ptr : U64} {m : Bool} {a v : U64} (hx : x ∈ OS)
    (hc : obj.Slot.cap st x s = ok (.PageTable ptr m a v)) (hfin : cdt.is_final_capability st s x = ok true) :
    ∀ y ∈ OS, y ≠ x → ¬ NmC st y ptr s := fun y hy hne hn => by
  have := (is_final.false_nm hM hRO hK h0 hx hc hy hne hn).symm.trans hfin
  exact Bool.false_ne_true (okinj this)

end fin

/-! ## ARMPageTableUnmap at decode level without `hone` -/

section dec
variable {OS Vc Ub : Set U64} {kb n : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A} {G : List (List U64)}

set_option maxHeartbeats 1000000 in
/-- **ARMPageTableUnmap of a mapped `PageTable` cap, `hone` discharged** (module docstring): gen 46's `unmapR` with
`hone` replaced by `MdbLk ∧ RngOneA64 ∧ KindA` at the decode's start state (and `h0`). -/
theorem vspace.decode_page_table.unmapRF (hA : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hY : VsTyR st kb Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (hU : UnmZ st OS Pt (S2Rt st Pp Te Re bits s) bits s) (hT : UnmT st OS (VsRt st Pp Hr Tb Lv s) s)
    (hV : UnmU st OS Pp s)
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) (h0 : ∀ x ∈ OS, x ≠ 0#u64)
    (a : A) (len slot buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) {ptr masid mvaddr : U64}
    (hsl : slot ∈ OS) (hc : obj.Slot.cap st slot s = ok (.PageTable ptr true masid mvaddr))
    (hF : PtFnd st hPl.ipa Pp Hr Lv Re bits s masid mvaddr ptr)
    (hptr : ptr ∈ Pt) (hal : Aligned ptr) (hfit : ptr.val + 4096 ≤ 2 ^ 64)
    (hD2 : ∀ q ∈ Te, q ≠ ptr → ∀ o o' : U64, o.val < 4096 → o.val % 8 = 0 → o'.val < 2 ^ bits q →
      o'.val % 8 = 0 → wa q o' ≠ wa ptr o)
    (hD1 : ∀ q ∈ Tb, q ≠ ptr → ∀ o o' : U64, o.val < 4096 → o.val % 8 = 0 → o'.val < 4096 → o'.val % 8 = 0 →
      wa q o' ≠ wa ptr o) :
    vspace.decode_page_table st ar s a fl4_abi.label.ARMPageTableUnmap len slot
      (.PageTable ptr true masid mvaddr) buf extra ⦃ r => r.2.1 = s ∨
        (L.ksb r.2.1 = kb ∧ VsTyR st kb Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ∧
          UnmZ st OS Pt (S2Rt st Pp Te Re bits r.2.1) bits r.2.1 ∧ UnmT st OS (VsRt st Pp Hr Tb Lv r.2.1) r.2.1 ∧
          UnmU st OS Pp r.2.1) ⦄ := by
  by_cases hh : ∀ y ∈ OS, y ≠ slot → ¬ NmC st y ptr s
  · exact vspace.decode_page_table.unmapR hA hPl hR hO q hk hPp hTb hTe hH hS hY h2 hU hT hV a len slot buf extra
      hsl hc hF hh hptr hal hfit hD2 hD1
  · simp only [not_forall, not_not] at hh
    obtain ⟨y, hy, hne, hn⟩ := hh
    have hfin := is_final.false_nm hM hRO hK h0 hsl hc hy hne hn
    unfold vspace.decode_page_table
    refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
    try dsimp only
    refine spec_ite (fun _ => ?_) (fun hne => absurd rfl hne)
    rw [hfin, bind_ok]
    refine spec_ite (fun h => absurd h (by decide)) (fun _ => (WP.spec_ok _).2 (Or.inl rfl))

end dec

end ST
end R
end W7

end

end Fl4ProofsA64.P1
