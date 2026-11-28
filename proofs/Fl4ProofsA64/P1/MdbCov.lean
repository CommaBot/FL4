/-
P1 (aarch64, gen 59): **`CoverA` (l4v `if_unsafe_then_cap` / `ex_cte_cap_wp_to`) as a state fact** (Architect
ruling): its boot case, its transfer along the cap steps, and the reset's start with it carried (no longer a case
hypothesis of the reset).

* **`CovBy c y`**: `c` is a physical non-untyped cap whose range holds all 32 bytes of slot `y` (MdbVUS's `CoverA`
  witness; `CoverA st OS s` is "every non-null `OS` slot is `CovBy` some `OS` cap").
* **`CoverA.empty`** (boot: all `OS` slots null, as `ValidUntypedA.empty`), **`CoverA.step`** (every covering cap
  before is held by some `OS` slot after — caps move, never vanish — and every slot non-null after was non-null
  before or is covered after), `CoverA.keepO` (`OSKeep`).
* Steps (cap equalities from the existing link lemmas, as MdbVU's `ValidUntypedA` steps): **`cdt.swap.cov`** /
  **`cdt.cap_swap_for_delete.cov`** (the two caps exchange places; a slot that turns non-null is covered before —
  `hc1` / `hc2`, automatic when it was non-null), **`cdt.move_cap.cov`** (the moved cap lands in `dest`; `dest`
  covered before, `hcd`), **`cdt.insert_with_cap.cov`** / **`cdt.insert_new_cap.cov`** (`dest` covered before by a
  cap other than `dest`'s own, `hcd`; the source keeps a covering cap: `set_untyped_cap_as_full` rewrites
  untypeds only, `FullA`), **`cdt.empty_slot.cov`** (the emptied slot's cap covers no other non-null slot unless
  another `OS` slot holds the same cap: `hlast`, l4v's "the last cap of an object goes only after its slots are
  emptied" — the Zombie loop's job, owed).
* **`StA`** (the carried bundle `MdbST ∧ UtRev ∧ ValidUntypedA ∧ UtZeroA ∧ CoverA`) and **`reset_startS`**: gen 58's
  `reset_start` with `CoverA` read off the carried state (gen 58's `reset_start` / `reset_null` stay).

No named premise; new definitions and theorems only (case hypotheses `hc1` / `hc2` / `hcd` / `hlast`).
-/
import Fl4ProofsA64.P1.MdbUZT
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- **A cap covering slot `y`** (module docstring). -/
def CovBy (c : capability.Cap) (y : U64) : Prop :=
  physA c = true ∧ isUtA c = false ∧ baseA c ≤ y.val ∧ y.val + 31 ≤ topA c

variable {OS : Set U64} {H : Heap}

theorem CoverA.of_cov {s : S} (h : ∀ y ∈ OS, capA st s y ≠ .Null → ∃ z ∈ OS, CovBy (capA st s z) y) :
    CoverA st OS s := h

theorem CoverA.cov {s : S} (h : CoverA st OS s) {y : U64} (hy : y ∈ OS) (hn : capA st s y ≠ .Null) :
    ∃ z ∈ OS, CovBy (capA st s z) y := h y hy hn

/-- **Boot**: null `OS` slots. -/
theorem CoverA.empty {s : S} (h : ∀ x ∈ OS, capA st s x = .Null) : CoverA st OS s :=
  fun y hy hn => absurd (h y hy) hn

/-- (gen 60) **Transfer, covering caps up to range** (`CoverA.step` with the covering cap after only required to
cover what the one before covered: `swap` / `move_cap` of an `update_cap_data` / `copied_cap` result). -/
theorem CoverA.stepG {s s' : S} (h : CoverA st OS s)
    (hk : ∀ z ∈ OS, physA (capA st s z) = true → isUtA (capA st s z) = false →
      ∃ z' ∈ OS, ∀ y, CovBy (capA st s z) y → CovBy (capA st s' z') y)
    (hn : ∀ y ∈ OS, capA st s' y ≠ .Null → capA st s y ≠ .Null ∨ ∃ z ∈ OS, CovBy (capA st s z) y) :
    CoverA st OS s' := by
  intro y hy hny
  have hc : ∃ z ∈ OS, CovBy (capA st s z) y := by
    rcases hn y hy hny with h0 | h0
    · exact h.cov hy h0
    · exact h0
  obtain ⟨z, hz, hcv⟩ := hc
  obtain ⟨z', hz', e⟩ := hk z hz hcv.1 hcv.2.1
  exact ⟨z', hz', e y hcv⟩

/-- **Transfer** (module docstring). -/
theorem CoverA.step {s s' : S} (h : CoverA st OS s)
    (hk : ∀ z ∈ OS, physA (capA st s z) = true → isUtA (capA st s z) = false → ∃ z' ∈ OS, capA st s' z' = capA st s z)
    (hn : ∀ y ∈ OS, capA st s' y ≠ .Null → capA st s y ≠ .Null ∨ ∃ z ∈ OS, CovBy (capA st s z) y) :
    CoverA st OS s' :=
  h.stepG (fun z hz hp hu => (hk z hz hp hu).elim fun z' ⟨hz', e⟩ => ⟨z', hz', fun _ hc => by rw [e]; exact hc⟩) hn

theorem CoverA.keepO {s s' : S} (h : CoverA st OS s) (k : OSKeep st OS s s') : CoverA st OS s' :=
  h.step (fun z hz _ _ => ⟨z, hz, k.capA hz⟩) fun y hy hn => Or.inl (by rw [← k.capA hy]; exact hn)

/-- (gen 60) **`swap` of any two encodable caps covering what the slots' caps covered** (CNode Rotate swaps
`update_cap_data` results; `swap.cov`'s proof, the cover transfer by `CoverA.stepG`). -/
theorem cdt.swap.covG (hO : OSOK T Ω Sg OS) {s : S} (h : CoverA st OS s) (hS : MdbS st OS s)
    {x1 x2 : U64} {c1 c2 : capability.Cap} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hne : x1 ≠ x2)
    (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) (hw1 : CapRt.EncWf c1) (hw2 : CapRt.EncWf c2)
    (hk1 : ∀ y, CovBy (capA st s x1) y → CovBy c1 y) (hk2 : ∀ y, CovBy (capA st s x2) y → CovBy c2 y)
    (hc1 : c2 ≠ .Null → ∃ z ∈ OS, CovBy (capA st s z) x1)
    (hc2 : c1 ≠ .Null → ∃ z ∈ OS, CovBy (capA st s z) x2) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => CoverA st OS s' ⦄ := by
  obtain ⟨p1, n1⟩ := hS.lnk hO hx1
  obtain ⟨p2, n2⟩ := hS.lnk hO hx2
  refine WP.spec_mono (cdt.swap.lrW hO (LR.self s) hx1 hx2 hne hs1 hs2 hw1 hw2 p1 n1 p2 n2) ?_
  rintro s' ⟨-, e1, e2, ek⟩
  refine h.stepG (fun z hz _ _ => ?_) fun y hy hn => ?_
  · by_cases a1 : z = x1
    · exact ⟨x2, hx2, fun y hy => by rw [e2]; rw [a1] at hy; exact hk1 y hy⟩
    · by_cases a2 : z = x2
      · exact ⟨x1, hx1, fun y hy => by rw [e1]; rw [a2] at hy; exact hk2 y hy⟩
      · exact ⟨z, hz, fun y hy => by rw [ek z hz a1 a2]; exact hy⟩
  · by_cases a1 : y = x1
    · subst a1; rw [e1] at hn; exact Or.inr (hc1 hn)
    · by_cases a2 : y = x2
      · subst a2; rw [e2] at hn; exact Or.inr (hc2 hn)
      · exact Or.inl (by rw [← ek y hy a1 a2]; exact hn)

/-- **`swap`** with the two caps the slots' own (as `cap_swap_for_delete` calls it). -/
theorem cdt.swap.cov (hO : OSOK T Ω Sg OS) {s : S} (h : CoverA st OS s) (hS : MdbS st OS s)
    {x1 x2 : U64} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hne : x1 ≠ x2)
    (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2)
    (hc1 : capA st s x2 ≠ .Null → ∃ z ∈ OS, CovBy (capA st s z) x1)
    (hc2 : capA st s x1 ≠ .Null → ∃ z ∈ OS, CovBy (capA st s z) x2) :
    cdt.swap st s (capA st s x1) x1 (capA st s x2) x2 ⦃ s' => CoverA st OS s' ⦄ :=
  cdt.swap.covG hO h hS hx1 hx2 hne hs1 hs2 (CapRt.decodeF_encWf _ _) (CapRt.decodeF_encWf _ _)
    (fun _ hy => hy) (fun _ hy => hy) hc1 hc2

/-- **`cap_swap_for_delete`** of two canonical `OS` slots. -/
theorem cdt.cap_swap_for_delete.cov (hO : OSOK T Ω Sg OS) {s : S} (h : CoverA st OS s) (hS : MdbS st OS s)
    {x1 x2 : U64} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2)
    (hc1 : capA st s x2 ≠ .Null → ∃ z ∈ OS, CovBy (capA st s z) x1)
    (hc2 : capA st s x1 ≠ .Null → ∃ z ∈ OS, CovBy (capA st s z) x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => CoverA st OS s' ⦄ := by
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · exact (WP.spec_ok _).2 h
  · rename_i hne'
    have hne : x1 ≠ x2 := by simpa using hne'
    rw [capA_eq, bind_ok, capA_eq, bind_ok]
    exact cdt.swap.cov hO h hS hx1 hx2 hne hs1 hs2 hc1 hc2

/-- `cap_swap_for_delete` of two non-null slots: the hypotheses from `CoverA` itself. -/
theorem cdt.cap_swap_for_delete.covNN (hO : OSOK T Ω Sg OS) {s : S} (h : CoverA st OS s) (hS : MdbS st OS s)
    {x1 x2 : U64} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2)
    (hn1 : capA st s x1 ≠ .Null) (hn2 : capA st s x2 ≠ .Null) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => CoverA st OS s' ⦄ :=
  cdt.cap_swap_for_delete.cov hO h hS hx1 hx2 hs1 hs2 (fun _ => h.cov hx1 hn1) (fun _ => h.cov hx2 hn2)

/-- (gen 60) **`move_cap` of any encodable cap covering what the source's cap covered** (CNode Move / Mutate /
Rotate move `copied_cap` / `update_cap_data` results; `move_cap.cov`'s proof, `CoverA.stepG`). -/
theorem cdt.move_cap.covG (hO : OSOK T Ω Sg OS) {s : S} (h : CoverA st OS s) (hS : MdbS st OS s)
    {src dest : U64} {nc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest)
    (hdc : obj.sext48 dest = ok dest) (hdn : capA st s dest = .Null) (hw : CapRt.EncWf nc)
    (hk : ∀ y, CovBy (capA st s src) y → CovBy nc y)
    (hcd : nc ≠ .Null → ∃ z ∈ OS, CovBy (capA st s z) dest) :
    cdt.move_cap st s nc src dest ⦃ s' => CoverA st OS s' ⦄ := by
  obtain ⟨pp, nn⟩ := hS.lnk hO hsrc
  refine WP.spec_mono (cdt.move_cap.lr hO (LR.self s) hsrc hd hsd hdc hw pp nn) ?_
  rintro s' ⟨-, ed, es, ek⟩
  refine h.stepG (fun z hz hp _ => ?_) fun y hy hn => ?_
  · by_cases a1 : z = src
    · exact ⟨dest, hd, fun y hy => by rw [ed]; rw [a1] at hy; exact hk y hy⟩
    · by_cases a2 : z = dest
      · rw [a2, hdn, physA_null] at hp; cases hp
      · exact ⟨z, hz, fun y hy => by rw [ek z hz a1 a2]; exact hy⟩
  · by_cases a1 : y = dest
    · subst a1; rw [ed] at hn; exact Or.inr (hcd hn)
    · by_cases a2 : y = src
      · subst a2; rw [es] at hn; exact absurd rfl hn
      · exact Or.inl (by rw [← ek y hy a2 a1]; exact hn)

/-- **`move_cap`** into a null `dest` (the decode's check): the source's cap lands in `dest` (`dest` covered
before, `hcd`). -/
theorem cdt.move_cap.cov (hO : OSOK T Ω Sg OS) {s : S} (h : CoverA st OS s) (hS : MdbS st OS s)
    {src dest : U64} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest)
    (hdc : obj.sext48 dest = ok dest) (hdn : capA st s dest = .Null)
    (hcd : capA st s src ≠ .Null → ∃ z ∈ OS, CovBy (capA st s z) dest) :
    cdt.move_cap st s (capA st s src) src dest ⦃ s' => CoverA st OS s' ⦄ :=
  cdt.move_cap.covG hO h hS hsrc hd hsd hdc hdn (CapRt.decodeF_encWf _ _) (fun _ hy => hy) hcd

/-- **`insert_with_cap`** into a null `dest`: `dest` covered before (`hcd`); the source keeps its cap unless it is
an untyped (`set_untyped_cap_as_full`, `FullA`), so covering caps stay. -/
theorem cdt.insert_with_cap.cov (hO : OSOK T Ω Sg OS) {s : S} (h : CoverA st OS s) (hS : MdbS st OS s)
    {src dest : U64} {nc sc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest)
    (hdc : obj.sext48 dest = ok dest) (hsc : capA st s src = sc) (hsc0 : sc ≠ .Null) (hw : CapRt.EncWf nc)
    (hdn : capA st s dest = .Null) (hcd : nc ≠ .Null → ∃ z ∈ OS, CovBy (capA st s z) dest) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => CoverA st OS s' ⦄ := by
  obtain ⟨-, nn⟩ := hS.lnk hO hsrc
  refine WP.spec_mono (spec_andA (cdt.insert_with_cap.lr hO (LR.self s) hsrc hd hsd hdc hsc hsc0 hw nn)
    (cdt.insert_with_cap.srcU hO hsrc hd hsd hsc hw nn)) ?_
  rintro s' ⟨⟨-, ed, -, -, ek, -⟩, hU⟩
  refine h.step (fun z hz hp hu => ?_) fun y hy hn => ?_
  · by_cases a1 : z = src
    · refine ⟨src, hsrc, ?_⟩
      rcases hU.1 with e | ⟨p, b, i, e', i1, e1, -, -⟩
      · rw [a1, e, hsc]
      · rw [a1, hsc, e1] at hu; simp [isUtA] at hu
    · by_cases a2 : z = dest
      · rw [a2, hdn, physA_null] at hp; cases hp
      · exact ⟨z, hz, ek z hz a1 a2⟩
  · by_cases a1 : y = dest
    · subst a1; rw [ed] at hn; exact Or.inr (hcd hn)
    · by_cases a2 : y = src
      · subst a2; exact Or.inl (by rw [hsc]; exact hsc0)
      · exact Or.inl (by rw [← ek y hy a2 a1]; exact hn)

/-- **`insert_new_cap`** (retype's step) into a null `dest` covered before (`hcd`). -/
theorem cdt.insert_new_cap.cov (hO : OSOK T Ω Sg OS) {s : S} (h : CoverA st OS s) (hS : MdbS st OS s)
    {src dest : U64} {nc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest)
    (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc) (hdn : capA st s dest = .Null)
    (hcd : nc ≠ .Null → ∃ z ∈ OS, CovBy (capA st s z) dest) :
    cdt.insert_new_cap st s src dest nc ⦃ s' => CoverA st OS s' ⦄ := by
  obtain ⟨-, nn⟩ := hS.lnk hO hsrc
  refine WP.spec_mono (cdt.insert_new_cap.lr hO (LR.self s) hsrc hd hsd hdc hw nn) ?_
  rintro s' ⟨-, ed, ek⟩
  refine h.step (fun z hz hp _ => ?_) fun y hy hn => ?_
  · by_cases a2 : z = dest
    · rw [a2, hdn, physA_null] at hp; cases hp
    · exact ⟨z, hz, ek z hz a2⟩
  · by_cases a1 : y = dest
    · subst a1; rw [ed] at hn; exact Or.inr (hcd hn)
    · exact Or.inl (by rw [← ek y hy a1]; exact hn)

section emp
variable {A : Type _} {ar : machine.Arch A}

/-- **`empty_slot`**: the emptied slot's cap is not the last cover of a non-null slot (`hlast`). -/
theorem cdt.empty_slot.cov (hO : OSOK T Ω Sg OS) {s : S} (h : CoverA st OS s) (hS : MdbS st OS s)
    {a : A} {x : U64} (hx : x ∈ OS) {cl : capability.Cap} {Pw : U64 → Prop} (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄)
    (hlast : ∀ y ∈ OS, y ≠ x → capA st s y ≠ .Null → CovBy (capA st s x) y →
      ∃ z ∈ OS, z ≠ x ∧ CovBy (capA st s z) y) :
    cdt.empty_slot st ar s a x cl ⦃ r => CoverA st OS r.1 ⦄ := by
  obtain ⟨G, hM, hRO, hK, -, -⟩ := hS
  refine WP.spec_mono (cdt.empty_slot.mdbFLG hO hO.nz hM hRO hK hx hpw hpcd) ?_
  rintro r ⟨⟨G', -, -, -, -, -, hcr, -, hx0, -⟩, -, -⟩
  intro y hy hn
  have hyx : y ≠ x := fun e => by rw [e, hx0] at hn; exact hn rfl
  have hn0 : capA st s y ≠ .Null := by rw [← hcr y hy hyx]; exact hn
  obtain ⟨z, hz, hcv⟩ := h.cov hy hn0
  by_cases hzx : z = x
  · subst hzx
    obtain ⟨z', hz', hzx', hcv'⟩ := hlast y hy hyx hn0 hcv
    exact ⟨z', hz', by rw [hcr z' hz' hzx']; exact hcv'⟩
  · exact ⟨z, hz, by rw [hcr z hz hzx]; exact hcv⟩

end emp

/-! ## The carried bundle at the reset's start -/

/-- **The carried state bundle** (module docstring). -/
def StA (st : machine.Store S) [L : LawfulStore st] (H : Heap) (OS : Set U64) (s : S) : Prop :=
  MdbST st OS s ∧ UtRev st OS s ∧ ValidUntypedA st H OS s ∧ UtZeroA st OS s ∧ CoverA st OS s

/-- **The reset's start with `CoverA` carried** (gen 58's `reset_start`, `CoverA` from the bundle). -/
theorem reset_startS {s : S} (hSt : StA st H OS s) {u p b i : U64} {d : Bool} (hu : u ∈ OS)
    (hcu : capA st s u = .Untyped p b i d) (hnd : ∀ G par, TreeA st OS G par s → ∀ y, ¬ Mdb.Desc par y u) :
    u ∈ OffR p.val (p.val + 2 ^ b.val) OS ∧
    MdbST st (OffR p.val (p.val + 2 ^ b.val) OS) s ∧ UtRev st (OffR p.val (p.val + 2 ^ b.val) OS) s ∧
    ValidUntypedA st (H.drop (RegionD H p.val (p.val + 2 ^ b.val))) (OffR p.val (p.val + 2 ^ b.val) OS) s ∧
    UtZeroA st (OffR p.val (p.val + 2 ^ b.val) OS) s ∧ CoverA st (OffR p.val (p.val + 2 ^ b.val) OS) s ∧
    ∀ x ∈ OS, x ∉ OffR p.val (p.val + 2 ^ b.val) OS → capA st s x = .Null := by
  obtain ⟨hS, hR, hV, hZ, hC⟩ := hSt
  obtain ⟨h1, h2, h3, h4, h5⟩ := reset_start hS hR hV hC hu hcu hnd
  refine ⟨h1, h2, h3, h4, hZ.sub OffR.sub, ?_, h5⟩
  intro y hy hn
  obtain ⟨z, hz, hcv⟩ := hC.cov hy.1 hn
  by_cases hzO : z ∈ OffR p.val (p.val + 2 ^ b.val) OS
  · exact ⟨z, hzO, hcv⟩
  · exact absurd (h5 z hz hzO) (fun e => by unfold CovBy at hcv; rw [e, physA_null] at hcv; cases hcv.1)

end ST
end R
end W7

end

end Fl4ProofsA64.P1
