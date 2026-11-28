/-
P1 (aarch64, gen 48): **`h0` reduced to one placement fact, and `UnmU.one` kept by `cdt::insert_with_cap` from a
`derive_cap` fact.**

* **`h0` (no `OS` slot at address 0).** `OSOK.ne0`: from `TcbPlaced T` (every TCB `TcbAddr`: nonzero, fitting) and
  `0 ∉ Ω`, every `OS` slot is nonzero — an `OS` slot's first word is a `CapW` word: a TCB-resident slot (`TLow`,
  `t + K` with `K < 224`, no wrap, `t ≠ 0`) or an `Ω` word. The TCB half is derived; **`0 ∉ Ω` is not derivable
  from the A64 invariants** (`SchedQueuesInvX.omega` only places `Ω` outside the TCBs and nodes, `EpsWit` apart from
  the endpoints; `OSOK` / `SlotTy*` add alignment and fit only). It is the exact remaining fact, stated here as a
  hypothesis (not added to `SlotTyEnt*`). Source: kernel objects, CNode slots included, are reached at kernel-window
  addresses `PPTR_BASE + paddr` (crates/fl4-core/src/arch/aarch64/layout.rs:5, `PPTR_BASE = 0xffff_8000_0000_0000`;
  crates/fl4-kernel-aarch64/src/paging.rs:215–218 maps `[start, end)` at `PPTR_BASE + start` with
  `end ≤ PPTR_TOP − PPTR_BASE`), so every `Ω` word is `≥ PPTR_BASE > 0`; `Slot::is_null` is `self.0 == 0`
  (crates/fl4-core/src/obj.rs:297–299) and `is_final_capability` (cdt.rs:163–174) reads a 0 link as "no
  neighbour".
* **`derive_cap`** (objects.rs:208–239): `DerivA nc c` — the source `c` and the derived `nc` are no unmapped
  `PageTable` / level-0 `Ept` cap (`NoUnm`), and every object `nc` names (`NmCap`) `c` names;
  **`objects.derive_cap.der`**: every `Ok nc` result of `derive_cap s slot c` has `DerivA nc c` (an unmapped table
  cap is refused, `IllegalOperation`). This is the fact the callers of `insert_with_cap` discharge (CNode Copy /
  Mint through `derive_cap`).
* **`UnmU.one` kept by insertion**: `one_ins` (data level: the new cap `DerivA` the source's, every other slot's cap
  kept or rewritten to an `Untyped`), **`cdt.insert_with_cap.one`** (function level, gen 48's
  `cdt.insert_with_cap.lr`).

No named premise; new definitions and theorems only (`0 ∉ Ω`, `DerivA` are case hypotheses).
-/
import Fl4ProofsA64.P1.MdbStepF
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-! ## `h0` -/

/-- **No `OS` slot at address 0**, from the TCB placement and `0 ∉ Ω` (module docstring). -/
theorem OSOK.ne0 {OS : Set U64} (hO : OSOK T Ω Sg OS) (hT : TcbPlaced T) (hΩ : (0#u64 : U64) ∉ Ω) :
    ∀ y ∈ OS, y ≠ 0#u64 := by
  intro y hy e
  rcases hO.cw0 hy with ⟨t, ht, K, hK, hb⟩ | ⟨hb, -⟩
  · have a := hT t ht
    have hv : (wa t K).val = t.val + K.val := by
      have := a.fits
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [← hb, e] at hv
    simp at hv
    exact a.ne0 (by omega)
  · exact hΩ (e ▸ hb)

/-! ## `derive_cap` -/

/-- Not an unmapped `PageTable` / level-0 `Ept` cap. -/
def NoUnm (c : capability.Cap) : Prop :=
  (∀ p a v, c ≠ .PageTable p false a v) ∧ (∀ p a v, c ≠ .Ept p 0#u64 false a v)

/-- A `PageTable` / `Ept` cap naming `p`. -/
def NmCap (c : capability.Cap) (p : U64) : Prop :=
  (∃ m a v, c = .PageTable p m a v) ∨ (∃ l m a v, c = .Ept p l m a v)

/-- An unmapped `PageTable` (`n = 4096`) / level-0 `Ept` (`n = 8192`) cap of `p`. -/
def UnmCap (c : capability.Cap) (p : U64) (n : Nat) : Prop :=
  (n = 4096 ∧ ∃ a v, c = .PageTable p false a v) ∨ (n = 8192 ∧ ∃ a v, c = .Ept p 0#u64 false a v)

/-- **What `derive_cap` guarantees** of a derived cap `nc` from `c` (module docstring). -/
def DerivA (nc c : capability.Cap) : Prop := NoUnm c ∧ NoUnm nc ∧ ∀ p, NmCap nc p → NmCap c p

theorem NoUnm.unm {c : capability.Cap} (h : NoUnm c) {p : U64} {n : Nat} : ¬ UnmCap c p n := by
  rintro (⟨-, a, v, e⟩ | ⟨-, a, v, e⟩)
  · exact h.1 _ _ _ e
  · exact h.2 _ _ _ e

theorem ut_unm {q b i : U64} {d : Bool} {p : U64} {n : Nat} : ¬ UnmCap (.Untyped q b i d) p n := by
  rintro (⟨-, a, v, e⟩ | ⟨-, a, v, e⟩) <;> cases e

theorem ut_nm {q b i : U64} {d : Bool} {p : U64} : ¬ NmCap (.Untyped q b i d) p := by
  rintro (⟨m, a, v, e⟩ | ⟨l, m, a, v, e⟩) <;> cases e

theorem UnmC_iff {x p : U64} {n : Nat} {s : S} : UnmC st x p n s ↔ UnmCap (capA st s x) p n := by
  unfold UnmC UnmCap; rw [capA_eq]
  constructor
  · rintro (⟨hn, a, v, e⟩ | ⟨hn, a, v, e⟩)
    · exact Or.inl ⟨hn, a, v, okinj e⟩
    · exact Or.inr ⟨hn, a, v, okinj e⟩
  · rintro (⟨hn, a, v, e⟩ | ⟨hn, a, v, e⟩)
    · exact Or.inl ⟨hn, a, v, by rw [e]⟩
    · exact Or.inr ⟨hn, a, v, by rw [e]⟩

theorem NmC_iff {x p : U64} {s : S} : NmC st x p s ↔ NmCap (capA st s x) p := by
  unfold NmC NmCap; rw [capA_eq]
  constructor
  · rintro (⟨m, a, v, e⟩ | ⟨l, m, a, v, e⟩)
    · exact Or.inl ⟨m, a, v, okinj e⟩
    · exact Or.inr ⟨l, m, a, v, okinj e⟩
  · rintro (⟨m, a, v, e⟩ | ⟨l, m, a, v, e⟩)
    · exact Or.inl ⟨m, a, v, by rw [e]⟩
    · exact Or.inr ⟨l, m, a, v, by rw [e]⟩

set_option hygiene false in
/-- `NoUnm` of a concrete cap of no unmapped table kind. -/
local macro "nu_tac" : tactic => `(tactic| (unfold NoUnm; exact ⟨fun _ _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩))

set_option hygiene false in
/-- An `Ok` result of `derive_cap` that is a cap of no unmapped table kind (closes `DerivA`). -/
local macro "der_ok" : tactic => `(tactic| (
  refine (WP.spec_ok _).2 fun nc h => ?_
  cases h
  unfold DerivA
  refine ⟨by nu_tac, by nu_tac, fun _ h => ?_⟩
  first
  | exact h
  | (exfalso; unfold NmCap at h; rcases h with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h)))

set_option maxHeartbeats 1000000 in
/-- **`derive_cap` never returns a cap derived from an unmapped table cap** (module docstring). -/
theorem objects.derive_cap.der (s : S) (slot : U64) (c : capability.Cap) :
    objects.derive_cap st s slot c ⦃ r => ∀ nc, r = .Ok nc → DerivA nc c ⦄ := by
  have hS : P0.StoreTotal st := L.total
  cases c
  case Untyped p b i d =>
    simp only [objects.derive_cap]
    refine WP.spec_bind (P0.cdt.ensure_no_children.p0 st s slot hS) fun r _ => ?_
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      der_ok
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      first
      | exact (WP.spec_ok _).2 fun nc h => (by cases h)
      | (simp only [WP.spec_ok]; intro nc h; cases h)
  case PageTable p m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      der_ok
  case PageDirectory p m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      der_ok
  case Pdpt p m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      der_ok
  case Pml4 p m a =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      der_ok
  case Ept p l m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      der_ok
  case HighVSpace p m a =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      der_ok
  all_goals (simp only [objects.derive_cap]; der_ok)

/-! ## `UnmU.one` along the insertion -/

section ins
variable {OS : Set U64}

/-- **`UnmU.one` along the insertion of a derived cap** (data level, module docstring). -/
theorem one_ins {s s' : S}
    (hU1 : ∀ x ∈ OS, ∀ y ∈ OS, ∀ p n, UnmC st x p n s → NmC st y p s → y = x) {src dest : U64}
    {nc sc : capability.Cap} (hsrc : src ∈ OS) (hsc : capA st s src = sc) (hD : DerivA nc sc)
    (hcd : capA st s' dest = nc)
    (hk : ∀ y ∈ OS, y ≠ dest → capA st s' y = capA st s y ∨ ∃ p b i d, capA st s' y = .Untyped p b i d) :
    ∀ x ∈ OS, ∀ y ∈ OS, ∀ p n, UnmC st x p n s' → NmC st y p s' → y = x := by
  have bu : ∀ z ∈ OS, z ≠ dest → ∀ p n, UnmCap (capA st s' z) p n → UnmCap (capA st s z) p n := by
    intro z hz hzd p n h
    rcases hk z hz hzd with e | ⟨q, b, i, d, e⟩
    · rwa [e] at h
    · rw [e] at h; exact absurd h ut_unm
  have bn : ∀ z ∈ OS, z ≠ dest → ∀ p, NmCap (capA st s' z) p → NmCap (capA st s z) p := by
    intro z hz hzd p h
    rcases hk z hz hzd with e | ⟨q, b, i, d, e⟩
    · rwa [e] at h
    · rw [e] at h; exact absurd h ut_nm
  intro x hx y hy p n hux hny
  rw [UnmC_iff] at hux; rw [NmC_iff] at hny
  by_cases ex : x = dest
  · rw [ex, hcd] at hux; exact absurd hux (NoUnm.unm hD.2.1)
  have ux := bu x hx ex p n hux
  by_cases ey : y = dest
  · rw [ey, hcd] at hny
    have ns := hD.2.2 p hny
    have e := hU1 x hx src hsrc p n (UnmC_iff.2 ux) (NmC_iff.2 (by rw [hsc]; exact ns))
    rw [e] at hsc
    rw [hsc] at ux; exact absurd ux (NoUnm.unm hD.1)
  · exact hU1 x hx y hy p n (UnmC_iff.2 ux) (NmC_iff.2 (bn y hy ey p hny))

variable {G : List (List U64)}

set_option maxHeartbeats 1000000 in
/-- **`UnmU.one` kept by `cdt::insert_with_cap`** of a cap derived (`DerivA`) from the source's. -/
theorem cdt.insert_with_cap.one (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S} (hM : MdbLk st OS G s)
    {Pp : Set U64} (hU : UnmU st OS Pp s) {src dest : U64} {nc sc : capability.Cap}
    (hsrc : src ∈ G.flatten) (hd : dest ∈ OS) (hd0 : capA st s dest = .Null) (hdc : obj.sext48 dest = ok dest)
    (hsc : capA st s src = sc) (hw : CapRt.EncWf nc) (hD : DerivA nc sc) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' =>
      ∀ x ∈ OS, ∀ y ∈ OS, ∀ p n, UnmC st x p n s' → NmC st y p s' → y = x ⦄ := by
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have os := inOS src hsrc
  have hs0 : capA st s src ≠ .Null := ((hM.members src).1 hsrc).2
  have hsc0 : sc ≠ .Null := by rw [← hsc]; exact hs0
  have dG : dest ∉ G.flatten := fun hm => ((hM.members dest).1 hm).2 hd0
  have hsd : src ≠ dest := fun e => dG (e ▸ hsrc)
  have hNm : NxA st s src ≠ 0#u64 → NxA st s src ∈ G.flatten := F.nxm _ hsrc
  refine WP.spec_mono (cdt.insert_with_cap.lr hO (LR.self s) os hd hsd hdc hsc hsc0 hw
    (fun h => inOS _ (hNm h))) ?_
  rintro s' ⟨-, ed, -, -, ek, u⟩
  refine one_ins hU.one os hsc hD ed fun y hy hyd => ?_
  by_cases e : y = src
  · rw [e]; exact u
  · exact Or.inl (ek y hy e hyd)

end ins

end ST
end R
end W7

end

end Fl4ProofsA64.P1
