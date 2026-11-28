/-
P1 (aarch64, gen 49): **two more step-preserved MDB facts next to `RngOneA64` / `KindA`** — `NullLk` (null `OS`
slots have zero links) and `ClsA` (one base, one class) — with boot, the in-place `set_cap`, `empty_slot`, the swap
(now also with a null first slot) and insertion.

* **`NullLk st OS s`** (l4v `valid_nullcaps`: a null cap's MDB node is the null node): every `OS` slot holding the
  null cap has `PREV` word 0 and `NEXT` pointer 0. Gen 48's finding: `MdbLk` says nothing about a null slot's link
  words, and the deletion loops swap a Zombie into its first covered slot (cdt.rs:257–262, `cap_swap_for_delete
  (Slot(ptr), slot)`), which may be null; with stale links there the swap would break the chains. Source: the boot
  zeroes the slots (`NullLk.zero`), `clear` zeroes all four words of an emptied slot (cdt.rs `empty_slot`), the link
  writes of `empty_slot` / `swap` / `insert_with_cap` hit chain members only, and a swap with a null slot leaves the
  slot that becomes null with the null slot's zero links (`LkAbs.sw_null`).
* **`ClsA st OS s`**: two `OS` slots with `RngKeyA` caps of the same base `ptrA` have the same class `clsA` (base and
  size bits). Needed for the Zombie rewrite (`setz`, gen 48's table): `is_final` plus `RngOneA64` / `KindA` excludes
  other key caps of the *class* only; `CNode p r1` beside `CNode p r2` was not excluded. Source (as `KindA`):
  `create_new_objects` retypes one object of one size per region, `derive_cap` / `update_cap_data` keep
  constructor, `ptr` and size (objects.rs:200–240).
* Abstract link algebra: **`LkAbs.sw_null`** (moved from gen 48's `scratch/a64/g48/absw.lean`: with `x1` null,
  linkless and referenced by no member, `swap` renames the members' links and leaves `x2` linkless), **`LkAbs.sw_fix`**
  (a non-member other than the two slots keeps its links).
* Boot / generic: `NullLk.zero`, `NullLk.keep`, `NullLk.set_cap`; `ClsA.of` (every key cap after has a key cap of
  the same class before), `ClsA.empty`, `ClsA.set_cap`, `ClsA.rem`, `ClsA.ren`, `ClsA.ins`.
* Function level: **`cdt.empty_slot.mdbN`** (from gen 49's `cdt.empty_slot.mdbF`, MdbEmpty), **`cdt.swap.mdbN`** /
  **`cdt.cap_swap_for_delete.mdbN`** (the second slot a member, the first a member **or null**: the ghost renamed),
  **`cdt.insert_with_cap.mdbN`**, **`cdt.insert.mdbN`**: `MdbLk ∧ RngOneA64 ∧ KindA ∧ NullLk ∧ ClsA` along each.

(gen 52, in place) **`swap_post`**: `swap.mdbN`'s argument after `cdt.swap.lr` (links at `sP` / `sN`, caps
exchanged ⇒ the five facts at the renamed ghost), moved out so CNode Rotate (MdbRot) reaches it after writing the old
caps back; `swap.mdbN` (statement unchanged) applies it.

(gen 62, dedupe) **`cdt.swap.lrN`**: `cdt.swap.lr`'s facts from `MdbLk ∧ NullLk` — the common start of `swap.mdbN`
and MdbTreeZ's `swap.treeN` (both proofs in place).

Named premises: none. Case hypotheses as gen 47/48's (`h0`, canonical slot addresses, the insert's `dest` null).
-/
import Fl4ProofsA64.P1.MdbDer
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1

namespace LkAbs
variable {α : Type} [DecidableEq α]

/-- **The swap with a null `x1`** (no links, referenced by no member): the members' links are renamed and `x2`
ends linkless. -/
theorem sw_null {o : α} {M : α → Prop} {pv nx : α → α} (h : LkF o M pv nx) {x1 x2 : α} (n1 : ¬ M x1)
    (z1 : x1 ≠ o) (p1 : pv x1 = o) (q1 : nx x1 = o) (r1 : ∀ y, M y → nx y ≠ x1 ∧ pv y ≠ x1) (m2 : M x2)
    {y : α} (my : M y) :
    sN o pv nx x1 x2 (tr x1 x2 y) = tr x1 x2 (nx y) ∧ sP o pv nx x1 x2 (tr x1 x2 y) = tr x1 x2 (pv y) ∧
      sN o pv nx x1 x2 x2 = o ∧ sP o pv nx x1 x2 x2 = o := by
  have z := h.z; have nxm := h.nxm; have pvm := h.pvm; have nxpv := h.nxpv; have pvnx := h.pvnx
  have nxne := h.nxne; have pvne := h.pvne; have pn := h.pn
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold sN s3 s4 tr
    grind
  · unfold sP s3 s4 tr
    grind
  · unfold sN s3 s4
    grind
  · unfold sP s3 s4
    grind

/-- **A non-member other than the two slots keeps its links** (`x1` a member, or linkless). -/
theorem sw_fix {o : α} {M : α → Prop} {pv nx : α → α} (h : LkF o M pv nx) {x1 x2 : α} (m2 : M x2)
    (h1 : M x1 ∨ (pv x1 = o ∧ nx x1 = o)) {w : α} (nw : ¬ M w) (w1 : w ≠ x1) (w2 : w ≠ x2) :
    sN o pv nx x1 x2 w = nx w ∧ sP o pv nx x1 x2 w = pv w := by
  have z := h.z; have nxm := h.nxm; have pvm := h.pvm
  rcases h1 with m1 | ⟨p1, q1⟩
  · constructor
    · unfold sN s3 s4
      grind
    · unfold sP s3 s4
      grind
  · constructor
    · unfold sN s3 s4
      grind
    · unfold sP s3 s4
      grind

end LkAbs

open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-! ## The two facts -/

/-- **`NullLk`** (module docstring): null `OS` slots have zero links. -/
def NullLk (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) : Prop :=
  ∀ x ∈ OS, capA st s x = .Null → L.mem s (wa x 16#u64) = 0#u64 ∧ NxA st s x = 0#u64

/-- **`ClsA`** (module docstring): `RngKeyA` caps of one base have one class. -/
structure ClsA (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) : Prop where
  cls : ∀ x ∈ OS, ∀ y ∈ OS, RngKeyA (capA st s x) → RngKeyA (capA st s y) →
    ptrA (capA st s x) = ptrA (capA st s y) → clsA (capA st s x) = clsA (capA st s y)

theorem nxA_zero (s : S) (x : U64) (h : L.mem s (wa x 24#u64) = 0#u64) : NxA st s x = 0#u64 := by
  unfold NxA; rw [h]
  have := sext48_eq 0#u64
  rw [sx0] at this; exact (okinj this).symm

section gen
variable {OS : Set U64}

/-- **Boot**: null slots with zero link words (the boot zeroes the slots). -/
theorem NullLk.zero {s : S}
    (h : ∀ x ∈ OS, capA st s x = .Null → L.mem s (wa x 16#u64) = 0#u64 ∧ L.mem s (wa x 24#u64) = 0#u64) :
    NullLk st OS s := fun x hx hn => ⟨(h x hx hn).1, nxA_zero s x (h x hx hn).2⟩

/-- **`NullLk` with every slot null after null before, with its links kept.** -/
theorem NullLk.keep {s s' : S} (h : NullLk st OS s)
    (hk : ∀ x ∈ OS, capA st s' x = .Null → capA st s x = .Null ∧
      L.mem s' (wa x 16#u64) = L.mem s (wa x 16#u64) ∧ NxA st s' x = NxA st s x) : NullLk st OS s' :=
  fun x hx hn => by
    obtain ⟨n0, e16, e24⟩ := hk x hx hn
    rw [e16, e24]; exact h x hx n0

/-- **`NullLk` along an in-place `set_cap`** of a non-null cap. -/
theorem NullLk.set_cap (hO : OSOK T Ω Sg OS) {s : S} (h : NullLk st OS s) {x0 : U64} (hx0 : x0 ∈ OS)
    {c : capability.Cap} {w0 w1 : U64} (hd : capability.Cap.decode w0 w1 = ok c) (hc : c ≠ .Null) :
    NullLk st OS (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) := by
  refine h.keep fun y hy hn => ?_
  by_cases hyx : y = x0
  · subst hyx
    rw [capA_wr2_self hO hx0 hd] at hn; exact absurd hn hc
  · obtain ⟨e16, e24⟩ := set_cap_links (st := st) (s := s) (w0 := w0) (w1 := w1) hO hx0 y hy
    rw [capA_wr2_other hO hx0 hy hyx] at hn
    exact ⟨hn, e16, by unfold NxA; rw [e24]⟩

/-- **`ClsA` when every key cap after has a key cap of the same class before.** -/
theorem ClsA.of {s s' : S} (h : ClsA st OS s)
    (hc : ∀ y ∈ OS, RngKeyA (capA st s' y) → ∃ z ∈ OS, RngKeyA (capA st s z) ∧
      clsA (capA st s' y) = clsA (capA st s z)) : ClsA st OS s' := by
  refine ⟨fun x hx y hy kx ky hp => ?_⟩
  obtain ⟨zx, hzx, kzx, ex⟩ := hc x hx kx
  obtain ⟨zy, hzy, kzy, ey⟩ := hc y hy ky
  rw [ex, ey]
  exact h.cls zx hzx zy hzy kzx kzy (by rw [← ptrA_of_cls ex, ← ptrA_of_cls ey]; exact hp)

/-- **Boot**: no non-null cap in `OS`. -/
theorem ClsA.empty {s : S} (h : ∀ x ∈ OS, capA st s x = .Null) : ClsA st OS s :=
  ⟨fun x hx _ _ k _ _ => absurd (h x hx ▸ k) RngKeyA.not_null⟩

/-- **`ClsA` along an in-place `set_cap`** of a cap with the old cap's key and class. -/
theorem ClsA.set_cap (hO : OSOK T Ω Sg OS) {s : S} (h : ClsA st OS s) {x0 : U64} (hx0 : x0 ∈ OS)
    {c : capability.Cap} {w0 w1 : U64} (hd : capability.Cap.decode w0 w1 = ok c)
    (hk : RngKeyA c ↔ RngKeyA (capA st s x0)) (hcl : RngKeyA (capA st s x0) → clsA c = clsA (capA st s x0)) :
    ClsA st OS (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) := by
  refine h.of fun y hy k => ?_
  by_cases hyx : y = x0
  · subst hyx
    rw [capA_wr2_self hO hx0 hd] at k ⊢
    exact ⟨y, hx0, hk.1 k, hcl (hk.1 k)⟩
  · rw [capA_wr2_other hO hx0 hy hyx] at k ⊢
    exact ⟨y, hy, k, rfl⟩

/-- **`ClsA` along a removal**: `x`'s cap made null, the others kept. -/
theorem ClsA.rem {s s' : S} (h : ClsA st OS s) {x : U64} (hcx : capA st s' x = .Null)
    (hk : ∀ y ∈ OS, y ≠ x → capA st s' y = capA st s y) : ClsA st OS s' := by
  refine h.of fun y hy k => ?_
  by_cases e : y = x
  · subst e; rw [hcx] at k; exact absurd k RngKeyA.not_null
  · rw [hk y hy e] at k ⊢; exact ⟨y, hy, k, rfl⟩

/-- **`ClsA` along the swap renaming.** -/
theorem ClsA.ren {s s' : S} (h : ClsA st OS s) {x1 x2 : U64} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS)
    (hc : ∀ y ∈ OS, capA st s' (swp x1 x2 y) = capA st s y) : ClsA st OS s' := by
  refine h.of fun y hy k => ?_
  have e : capA st s' y = capA st s (swp x1 x2 y) := by rw [← hc _ (swp_os hx1 hx2 hy), swp_swp]
  rw [e] at k ⊢
  exact ⟨_, swp_os hx1 hx2 hy, k, rfl⟩

/-- **`ClsA` along the insertion** of a cap alike the source's. -/
theorem ClsA.ins {s s' : S} (h : ClsA st OS s) {src dest : U64} (hsrc : src ∈ OS)
    (hk : ∀ y ∈ OS, y ≠ src → y ≠ dest → capA st s' y = capA st s y)
    (hs : AlikeA (capA st s' src) (capA st s src)) (hdA : AlikeA (capA st s' dest) (capA st s src)) :
    ClsA st OS s' := by
  refine h.of fun y hy k => ?_
  by_cases hyd : y = dest
  · subst hyd
    have k0 := hdA.1.1 k
    exact ⟨src, hsrc, k0, (hdA.2 k0).1⟩
  · by_cases hys : y = src
    · subst hys
      have k0 := hs.1.1 k
      exact ⟨y, hsrc, k0, (hs.2 k0).1⟩
    · rw [hk y hy hys hyd] at k ⊢; exact ⟨y, hy, k, rfl⟩

end gen

/-! ## Function level -/

variable {OS : Set U64} {G : List (List U64)}

section emp
variable {A : Type _} {ar : machine.Arch A}

/-- **`MdbLk ∧ RngOneA64 ∧ KindA ∧ NullLk ∧ ClsA` along `cdt::empty_slot`** (from `cdt.empty_slot.mdbF`). -/
theorem cdt.empty_slot.mdbN (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S}
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) (hN : NullLk st OS s)
    (hC : ClsA st OS s) {a : A} {x : U64} (hx : x ∈ OS)
    {cl : capability.Cap} {Pw : U64 → Prop} (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => ∃ G' : List (List U64), MdbLk st OS G' r.1 ∧ RngOneA64 st G' r.1 ∧
      KindA st OS r.1 ∧ NullLk st OS r.1 ∧ ClsA st OS r.1 ⦄ := by
  refine WP.spec_mono (cdt.empty_slot.mdbF hO h0 hM hRO hK hx hpw hpcd) ?_
  rintro r ⟨G', a1, a2, a3, hcr, hsk, hx0, hxz⟩
  refine ⟨G', a1, a2, a3, fun y hy hy0 => ?_, hC.rem hx0 hcr⟩
  by_cases e : y = x
  · subst e
    rcases hxz with k | ⟨e16, e24⟩
    · rw [k.cp] at hy0
      rw [k.2.2.1, k.nx]; exact hN y hy hy0
    · exact ⟨e16, nxA_zero _ _ e24⟩
  · rw [hcr y hy e] at hy0
    have k := hsk y hy e hy0
    rw [k.2.2.1, k.nx]; exact hN y hy hy0

end emp

section swap

set_option maxHeartbeats 1000000 in
/-- (gen 52) **The swap's end state carries the MDB facts at the renamed ghost**: links at `sP` / `sN` of the start
state's, the two slots' caps exchanged, other `OS` caps kept (`swap.mdbN`'s argument after `cdt.swap.lr`, moved;
rotate reaches it through a write-back of the old caps). -/
theorem swap_post (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s s' : S} (hM : MdbLk st OS G s)
    (hRO : RngOneA64 st G s) (hK : KindA st OS s) (hN : NullLk st OS s) (hC : ClsA st OS s) {x1 x2 : U64}
    (hx1 : x1 ∈ OS) (hx2 : x2 ∈ G.flatten) (hne : x1 ≠ x2)
    (hL : LR st OS s' (LkAbs.sP 0#u64 (fun z => L.mem s (wa z 16#u64)) (NxA st s) x1 x2)
      (LkAbs.sN 0#u64 (fun z => L.mem s (wa z 16#u64)) (NxA st s) x1 x2))
    (e1 : capA st s' x1 = capA st s x2) (e2 : capA st s' x2 = capA st s x1)
    (ek : ∀ y ∈ OS, y ≠ x1 → y ≠ x2 → capA st s' y = capA st s y) :
    MdbLk st OS (renG x1 x2 G) s' ∧ RngOneA64 st (renG x1 x2 G) s' ∧
      KindA st OS s' ∧ NullLk st OS s' ∧ ClsA st OS s' := by
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have o2 := inOS x2 hx2
  have nm : ∀ y ∈ OS, y ∉ G.flatten → capA st s y = .Null := fun y hy hn => by
    by_contra h; exact hn ((hM.members y).2 ⟨hy, h⟩)
  have N1 : x1 ∈ G.flatten ∨ (L.mem s (wa x1 16#u64) = 0#u64 ∧ NxA st s x1 = 0#u64) := by
    by_cases m : x1 ∈ G.flatten
    · exact Or.inl m
    · exact Or.inr (hN x1 hx1 (nm x1 hx1 m))
  have hc : ∀ y ∈ OS, capA st s' (swp x1 x2 y) = capA st s y := by
    intro y hy
    unfold swp
    by_cases a1 : y = x1
    · rw [a1, if_pos rfl, e2]
    · rw [if_neg a1]
      by_cases a2 : y = x2
      · rw [a2, if_pos rfl, e1]
      · rw [if_neg a2]; exact ek y hy a1 a2
  have sw : ∀ y ∈ G.flatten, swp x1 x2 y ∈ OS := fun y hy => swp_os hx1 o2 (inOS y hy)
  -- the abstract renaming, both cases
  have r1 : x1 ∉ G.flatten → ∀ y, y ∈ G.flatten → NxA st s y ≠ x1 ∧ L.mem s (wa y 16#u64) ≠ x1 :=
    fun n1 y hy => ⟨fun e => n1 (by rw [← e]; exact F.nxm y hy (by rw [e]; exact h0 x1 hx1)),
      fun e => n1 (by rw [← e]; exact F.pvm y hy (by rw [e]; exact h0 x1 hx1))⟩
  have key : ∀ y ∈ G.flatten,
      LkAbs.sN 0#u64 (fun z => L.mem s (wa z 16#u64)) (NxA st s) x1 x2 (LkAbs.tr x1 x2 y) =
        LkAbs.tr x1 x2 (NxA st s y) ∧
      LkAbs.sP 0#u64 (fun z => L.mem s (wa z 16#u64)) (NxA st s) x1 x2 (LkAbs.tr x1 x2 y) =
        LkAbs.tr x1 x2 (L.mem s (wa y 16#u64)) := by
    intro y hy
    by_cases m1 : x1 ∈ G.flatten
    · exact LkAbs.sw_ok F m1 hx2 hne hy
    · obtain ⟨p1, q1⟩ := hN x1 hx1 (nm x1 hx1 m1)
      obtain ⟨a, b, -, -⟩ := LkAbs.sw_null F m1 (h0 x1 hx1) p1 q1 (r1 m1) hx2 hy
      exact ⟨a, b⟩
  refine ⟨hM.ren h0 hx1 o2 hc (fun y hy => ?_) (fun y hy => ?_), hRO.ren fun y hy => hc y (inOS y hy),
    hK.ren hx1 o2 hc, fun z hz hz0 => ?_, hC.ren hx1 o2 hc⟩
  · rw [(hL _ (sw y hy)).2, swp_tr, swp_tr]; exact (key y hy).1
  · rw [(hL _ (sw y hy)).1, swp_tr, swp_tr]; exact (key y hy).2
  · rw [(hL z hz).1, (hL z hz).2]
    by_cases a1 : z = x1
    · subst a1
      rw [e1] at hz0
      exact absurd hz0 ((hM.members x2).1 hx2).2
    by_cases a2 : z = x2
    · subst a2
      rw [e2] at hz0
      have m1 : x1 ∉ G.flatten := fun m => ((hM.members x1).1 m).2 hz0
      obtain ⟨p1, q1⟩ := hN x1 hx1 hz0
      obtain ⟨-, -, a, b⟩ := LkAbs.sw_null F m1 (h0 x1 hx1) p1 q1 (r1 m1) hx2 hx2
      exact ⟨b, a⟩
    rw [ek z hz a1 a2] at hz0
    have nz : z ∉ G.flatten := fun m => ((hM.members z).1 m).2 hz0
    have fx := LkAbs.sw_fix F hx2 N1 nz a1 a2
    rw [fx.1, fx.2]
    exact hN z hz hz0

/-- (gen 62) **`cdt.swap.lr`'s facts for `x1` a member or a null linkless slot, `x2` a member** (the common start
of `cdt.swap.mdbN` and MdbTreeZ's `cdt.swap.treeN`: the link fields of `x1` in `OS` by `NullLk` when it is no
member). -/
theorem cdt.swap.lrN (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S} (hM : MdbLk st OS G s)
    (hN : NullLk st OS s) {x1 x2 : U64} {c1 c2 : capability.Cap} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ G.flatten)
    (hne : x1 ≠ x2) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) (hc1 : capA st s x1 = c1)
    (hc2 : capA st s x2 = c2) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => LR st OS s' (LkAbs.sP 0#u64 (fun z => L.mem s (wa z 16#u64)) (NxA st s) x1 x2)
      (LkAbs.sN 0#u64 (fun z => L.mem s (wa z 16#u64)) (NxA st s) x1 x2) ∧
      capA st s' x1 = c2 ∧ capA st s' x2 = c1 ∧ ∀ y ∈ OS, y ≠ x1 → y ≠ x2 → capA st s' y = capA st s y ⦄ := by
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have o2 := inOS x2 hx2
  have nm : ∀ y ∈ OS, y ∉ G.flatten → capA st s y = .Null := fun y hy hn => by
    by_contra h; exact hn ((hM.members y).2 ⟨hy, h⟩)
  have N1 : x1 ∈ G.flatten ∨ (L.mem s (wa x1 16#u64) = 0#u64 ∧ NxA st s x1 = 0#u64) := by
    by_cases m : x1 ∈ G.flatten
    · exact Or.inl m
    · exact Or.inr (hN x1 hx1 (nm x1 hx1 m))
  have hp1 : L.mem s (wa x1 16#u64) ≠ 0#u64 → L.mem s (wa x1 16#u64) ∈ OS := fun h => by
    rcases N1 with m | ⟨e, -⟩
    · exact inOS _ (F.pvm _ m h)
    · exact absurd e h
  have hn1 : NxA st s x1 ≠ 0#u64 → NxA st s x1 ∈ OS := fun h => by
    rcases N1 with m | ⟨-, e⟩
    · exact inOS _ (F.nxm _ m h)
    · exact absurd e h
  refine WP.spec_mono (cdt.swap.lr hO (LR.self s) hx1 o2 hne hs1 hs2 hc1 hc2 hp1 hn1
    (fun h => inOS _ (F.pvm _ hx2 h)) (fun h => inOS _ (F.nxm _ hx2 h))) fun _ h => h

set_option maxHeartbeats 1000000 in
/-- **`MdbLk ∧ RngOneA64 ∧ KindA ∧ NullLk ∧ ClsA` along `cdt::swap`**: `x2` a member, `x1` a member or a null slot
(then linkless by `NullLk`); the ghost renamed by the transposition. -/
theorem cdt.swap.mdbN (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S} (hM : MdbLk st OS G s)
    (hRO : RngOneA64 st G s) (hK : KindA st OS s) (hN : NullLk st OS s) (hC : ClsA st OS s) {x1 x2 : U64}
    {c1 c2 : capability.Cap} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ G.flatten) (hne : x1 ≠ x2)
    (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) (hc1 : capA st s x1 = c1)
    (hc2 : capA st s x2 = c2) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => MdbLk st OS (renG x1 x2 G) s' ∧ RngOneA64 st (renG x1 x2 G) s' ∧
      KindA st OS s' ∧ NullLk st OS s' ∧ ClsA st OS s' ⦄ :=
  WP.spec_mono (cdt.swap.lrN hO h0 hM hN hx1 hx2 hne hs1 hs2 hc1 hc2) fun s' ⟨hL, e1, e2, ek⟩ =>
    swap_post h0 hM hRO hK hN hC hx1 hx2 hne hL (e1.trans hc2.symm) (e2.trans hc1.symm) ek

/-- **`MdbLk ∧ RngOneA64 ∧ KindA ∧ NullLk ∧ ClsA` along `cap_swap_for_delete`**: `x2` a member, `x1` any `OS`
slot (cdt.rs:96–103; the deletion loops call it with `x1 = Slot(ptr)`, possibly null, and `x2` the Zombie's slot). -/
theorem cdt.cap_swap_for_delete.mdbN (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S}
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) (hN : NullLk st OS s)
    (hC : ClsA st OS s) {x1 x2 : U64} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ G.flatten) (hs1 : obj.sext48 x1 = ok x1)
    (hs2 : obj.sext48 x2 = ok x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => ∃ G' : List (List U64), MdbLk st OS G' s' ∧ RngOneA64 st G' s' ∧
      KindA st OS s' ∧ NullLk st OS s' ∧ ClsA st OS s' ⦄ := by
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · exact (WP.spec_ok _).2 ⟨G, hM, hRO, hK, hN, hC⟩
  · rename_i hne'
    have hne : x1 ≠ x2 := by simpa using hne'
    rw [capA_eq, bind_ok, capA_eq, bind_ok]
    exact WP.spec_mono (cdt.swap.mdbN hO h0 hM hRO hK hN hC hx1 hx2 hne hs1 hs2 rfl rfl) fun s' h => ⟨_, h⟩

end swap

section ins

set_option maxHeartbeats 1000000 in
/-- **`MdbLk ∧ RngOneA64 ∧ KindA ∧ NullLk ∧ ClsA` along `cdt::insert_with_cap`** (gen 48's case hypotheses). -/
theorem cdt.insert_with_cap.mdbN (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S}
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) (hN : NullLk st OS s)
    (hC : ClsA st OS s) {src dest : U64} {nc sc : capability.Cap}
    (hsrc : src ∈ G.flatten) (hd : dest ∈ OS) (hd0 : capA st s dest = .Null) (hdc : obj.sext48 dest = ok dest)
    (hsc : capA st s src = sc) (hw : CapRt.EncWf nc) (hnc : nc ≠ .Null) (hA : AlikeA nc sc) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => MdbLk st OS (insG src dest G) s' ∧
      RngOneA64 st (insG src dest G) s' ∧ KindA st OS s' ∧ NullLk st OS s' ∧ ClsA st OS s' ⦄ := by
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have os := inOS src hsrc
  have hs0 : capA st s src ≠ .Null := ((hM.members src).1 hsrc).2
  have hsc0 : sc ≠ .Null := by rw [← hsc]; exact hs0
  have dG : dest ∉ G.flatten := fun hm => ((hM.members dest).1 hm).2 hd0
  have hsd : src ≠ dest := fun e => dG (e ▸ hsrc)
  have hNm : NxA st s src ≠ 0#u64 → NxA st s src ∈ G.flatten := F.nxm _ hsrc
  refine WP.spec_mono (WP.spec_and (cdt.insert_with_cap.mdb hO h0 hM hRO hK hsrc hd hd0 hdc hsc hw hnc hA)
    (cdt.insert_with_cap.lr hO (LR.self s) os hd hsd hdc hsc hsc0 hw (fun h => inOS _ (hNm h)))) ?_
  rintro s' ⟨⟨a1, a2, a3⟩, hL, ed, es, ns, ek, -⟩
  refine ⟨a1, a2, a3, fun z hz hz0 => ?_, hC.ins os ek (by rw [hsc]; exact es) (by rw [ed, hsc]; exact hA)⟩
  have zd : z ≠ dest := fun e => hnc (by rw [← ed, ← e]; exact hz0)
  have zs : z ≠ src := fun e => ns (by rw [← e]; exact hz0)
  rw [ek z hz zs zd] at hz0
  have nz : z ∉ G.flatten := fun m => ((hM.members z).1 m).2 hz0
  have zN : z ≠ NxA st s src := fun e => by
    by_cases h : NxA st s src = 0#u64
    · exact h0 z hz (e.trans h)
    · exact nz (e ▸ hNm h)
  obtain ⟨p0, n0⟩ := hN z hz hz0
  rw [(hL z hz).1, (hL z hz).2]
  simp only [zN, zd, zs, and_false, if_false]
  exact ⟨p0, n0⟩

/-- **`MdbLk ∧ RngOneA64 ∧ KindA ∧ NullLk ∧ ClsA` along `cdt::insert`** (the source cap read from `src`). -/
theorem cdt.insert.mdbN (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S} (hM : MdbLk st OS G s)
    (hRO : RngOneA64 st G s) (hK : KindA st OS s) (hN : NullLk st OS s) (hC : ClsA st OS s) {src dest : U64}
    {nc : capability.Cap} (hsrc : src ∈ G.flatten) (hd : dest ∈ OS) (hd0 : capA st s dest = .Null)
    (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc) (hnc : nc ≠ .Null) (hA : AlikeA nc (capA st s src)) :
    cdt.insert st s nc src dest ⦃ s' => MdbLk st OS (insG src dest G) s' ∧
      RngOneA64 st (insG src dest G) s' ∧ KindA st OS s' ∧ NullLk st OS s' ∧ ClsA st OS s' ⦄ := by
  unfold cdt.insert
  rw [capA_eq, bind_ok]
  exact cdt.insert_with_cap.mdbN hO h0 hM hRO hK hN hC hsrc hd hd0 hdc rfl hw hnc hA

end ins

end ST
end R
end W7

end

end Fl4ProofsA64.P1
