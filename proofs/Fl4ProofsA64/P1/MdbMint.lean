/-
P1 (aarch64, gen 49): **`DerivA` through `mask_cap_rights` / `update_cap_data`** — CNode Copy / Mint's new cap
(cnode.rs:77–102, `copied_cap`) is derived (`DerivA`, MdbDer) from the *source* cap, not only from the masked /
re-badged one `derive_cap` sees; this is the hypothesis `cdt.insert_with_cap.one` (MdbDer) takes.

* `isTab` (a `PageTable` / `Ept` cap), **`TabEq m c`**: if either cap is a table cap, they are equal. `TabEq.refl`,
  `TabEq.nt` (neither a table cap), `TabEq.trans`; **`DerivA.tab`**: `DerivA nc m` and `TabEq m c` give `DerivA nc c`.
* **`capability.mask_cap_rights.tab`** (capability.rs:360–386: only `Endpoint` / `Notification` / `Reply` / `Frame`
  rights change, every other cap is returned as is) and **`objects.update_cap_data.tab`** (objects.rs:156–183: only
  `Endpoint` / `Notification` (badge, or `Null`) and `CNode` (guard, or `Null`) change): the result is `TabEq` the
  argument.
* **`cnode.copied_cap.der`**: every `Ok (nc, false)` of `copied_cap` (Copy, Mint: not a move) has `DerivA nc
  src_cap` — gen 48's `objects.derive_cap.der` composed with the two lemmas above.
* `objects.derive_cap.tab` (a table cap comes out only as it went in), `.derT`; **`cnode.copied_cap.derT`**:
  `DerivA nc src_cap ∧ TabEq nc src_cap`.
* **`UnmU.dis` / `.pool` (and `.one`) along insertion**: `VsCapA`, `VsC_iff`; **`UnmU.ins`** (data level: each slot's
  table cap after is its old slot's, `oldA`), **`cdt.insert_with_cap.unmU`** (`h0` from `OSOK.nz`).

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.MdbNz
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

namespace W7
namespace R
namespace ST

/-- A `PageTable` / `Ept` cap. -/
def isTab : capability.Cap → Bool
  | .PageTable .. => true
  | .Ept .. => true
  | _ => false

theorem isTab_of_nm {c : capability.Cap} {p : U64} (h : NmCap c p) : isTab c = true := by
  rcases h with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> rfl

/-- **If either cap is a table cap, the two are equal.** -/
def TabEq (m c : capability.Cap) : Prop := (∀ p, NmCap m p → m = c) ∧ (∀ p, NmCap c p → m = c)

theorem TabEq.refl (c : capability.Cap) : TabEq c c := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem TabEq.nt {m c : capability.Cap} (hm : isTab m = false) (hc : isTab c = false) : TabEq m c :=
  ⟨fun _ h => (by rw [isTab_of_nm h] at hm; cases hm), fun _ h => (by rw [isTab_of_nm h] at hc; cases hc)⟩

theorem TabEq.trans {m c1 c : capability.Cap} (h1 : TabEq m c1) (h2 : TabEq c1 c) : TabEq m c := by
  refine ⟨fun p h => ?_, fun p h => ?_⟩
  · have e := h1.1 p h
    rw [e] at h ⊢; exact h2.1 p h
  · have e := h2.2 p h
    rw [← e] at h ⊢; exact h1.2 p h

/-- **`DerivA` through a `TabEq` step.** -/
theorem DerivA.tab {nc m c : capability.Cap} (h : DerivA nc m) (ht : TabEq m c) : DerivA nc c := by
  refine ⟨⟨fun p a v e => h.1.1 p a v ?_, fun p a v e => h.1.2 p a v ?_⟩, h.2.1, fun p hp => ?_⟩
  · rw [ht.2 p (Or.inl ⟨false, a, v, e⟩), e]
  · rw [ht.2 p (Or.inr ⟨0#u64, false, a, v, e⟩), e]
  · have hm := h.2.2 p hp
    rwa [ht.1 p hm] at hm

/-- **`mask_cap_rights` changes no table cap and makes none.** -/
theorem capability.mask_cap_rights.tab (r : capability.Rights) (c : capability.Cap) :
    capability.mask_cap_rights r c ⦃ m => TabEq m c ⦄ := by
  cases c
  case Endpoint p b sd rc g gr =>
    cases sd <;> cases rc <;> cases g <;> cases gr <;>
      simp only [capability.mask_cap_rights, Bool.false_eq_true, ↓reduceIte, bind_ok] <;>
      exact (WP.spec_ok _).2 (TabEq.nt rfl rfl)
  case Notification p b sd rc =>
    cases sd <;> cases rc <;>
      simp only [capability.mask_cap_rights, Bool.false_eq_true, ↓reduceIte, bind_ok] <;>
      exact (WP.spec_ok _).2 (TabEq.nt rfl rfl)
  case Reply p g =>
    cases g <;> simp only [capability.mask_cap_rights, Bool.false_eq_true, ↓reduceIte] <;>
      exact (WP.spec_ok _).2 (TabEq.nt rfl rfl)
  case Frame p sz rt dv mp ep asd va =>
    simp only [capability.mask_cap_rights]
    exact WP.spec_bind (P0.capability.mask_vm_rights.p0 rt r) fun _ _ => (WP.spec_ok _).2 (TabEq.nt rfl rfl)
  all_goals (simp only [capability.mask_cap_rights]; exact (WP.spec_ok _).2 (TabEq.refl _))

/-- **`update_cap_data` changes no table cap and makes none.** -/
theorem objects.update_cap_data.tab (pr : Bool) (data : U64) (c : capability.Cap) :
    objects.update_cap_data pr data c ⦃ m => TabEq m c ⦄ := by
  cases c
  case Endpoint p b sd rc g gr =>
    simp only [objects.update_cap_data]
    split
    · exact (WP.spec_ok _).2 (TabEq.nt rfl rfl)
    · split <;> exact (WP.spec_ok _).2 (TabEq.nt rfl rfl)
  case Notification p b sd rc =>
    simp only [objects.update_cap_data]
    split
    · exact (WP.spec_ok _).2 (TabEq.nt rfl rfl)
    · split <;> exact (WP.spec_ok _).2 (TabEq.nt rfl rfl)
  case CNode p rd gs g =>
    simp only [objects.update_cap_data]
    refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
    refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
    split
    · exact (WP.spec_ok _).2 (TabEq.nt rfl rfl)
    · refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
      refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
      refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
      exact (WP.spec_ok _).2 (TabEq.nt rfl rfl)
  all_goals (simp only [objects.update_cap_data]; exact (WP.spec_ok _).2 (TabEq.refl _))

set_option maxHeartbeats 1000000 in
/-- **CNode Copy / Mint's new cap is `DerivA` the source cap** (module docstring). -/
theorem cnode.copied_cap.der (s : S) (lbl length buf src : U64) (src_cap : capability.Cap) :
    cnode.copied_cap st s lbl length buf src src_cap ⦃ r => ∀ nc, r = .Ok (nc, false) → DerivA nc src_cap ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have fin : ∀ (m : capability.Cap), TabEq m src_cap → ∀ x : core.result.Result capability.Cap error.Exc,
      (∀ nc, x = .Ok nc → DerivA nc m) →
      (do
        let cf ← core.result.Result.Insts.CoreOpsTry.branch x
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val => ok (core.result.Result.Ok (val, false))
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (capability.Cap × Bool) (core.convert.FromSame error.Exc) residual :
        Result (core.result.Result (capability.Cap × Bool) error.Exc)) ⦃ r =>
        ∀ nc, r = .Ok (nc, false) → DerivA nc src_cap ⦄ := by
    intro m ht x hx
    rcases x with v | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
      intro nc h; cases h; exact (hx v rfl).tab ht
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      first
      | exact (WP.spec_ok _).2 fun nc h => (by cases h)
      | (simp only [WP.spec_ok]; intro nc h; cases h)
  unfold cnode.copied_cap
  refine WP.spec_bind (P0.sched.cur_thread.p0 st s hS) fun ct _ => ?_
  split
  · split
    · simp only [error.truncated, WP.spec_ok]; intro nc h; cases h
    · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun i _ => ?_
      refine WP.spec_bind (P0.capability.Rights.from_word.p0 i) fun rr _ => ?_
      refine WP.spec_bind (capability.mask_cap_rights.tab rr src_cap) fun c hc => ?_
      exact WP.spec_bind (objects.derive_cap.der s src c) fun r1 h1 => fin c hc r1 h1
  · split
    · split
      · simp only [error.truncated, WP.spec_ok]; intro nc h; cases h
      · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun i _ => ?_
        refine WP.spec_bind (P0.capability.Rights.from_word.p0 i) fun rr _ => ?_
        refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun data _ => ?_
        refine WP.spec_bind (capability.mask_cap_rights.tab rr src_cap) fun c hc => ?_
        refine WP.spec_bind (objects.update_cap_data.tab false data c) fun c1 hc1 => ?_
        exact WP.spec_bind (objects.derive_cap.der s src c1) fun r1 h1 => fin c1 (hc1.trans hc) r1 h1
    · split
      · exact (WP.spec_ok _).2 fun nc h => by cases h
      · split
        · simp only [error.truncated, WP.spec_ok]; intro nc h; cases h
        · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun data _ => ?_
          exact WP.spec_bind (P0.objects.update_cap_data.p0 true data src_cap) fun _ _ =>
            (WP.spec_ok _).2 fun nc h => by cases h

/-! ## Table caps exactly kept: `derive_cap`, `copied_cap`, and `UnmU` along the insertion -/

set_option hygiene false in
/-- An `Ok` result of `derive_cap` that is the argument or no table cap (closes `TabEq`). -/
local macro "tab_ok" : tactic => `(tactic| (
  refine (WP.spec_ok _).2 fun nc h => ?_
  cases h
  first | exact TabEq.refl _ | exact TabEq.nt rfl rfl))

set_option maxHeartbeats 1000000 in
/-- **`derive_cap` returns a table cap only as it is** (objects.rs:208–239: mapped table caps unchanged, unmapped
ones refused, no other cap becomes a table cap). -/
theorem objects.derive_cap.tab (s : S) (slot : U64) (c : capability.Cap) :
    objects.derive_cap st s slot c ⦃ r => ∀ nc, r = .Ok nc → TabEq nc c ⦄ := by
  have hS : P0.StoreTotal st := L.total
  cases c
  case Untyped p b i d =>
    simp only [objects.derive_cap]
    refine WP.spec_bind (P0.cdt.ensure_no_children.p0 st s slot hS) fun r _ => ?_
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      tab_ok
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
      tab_ok
  case PageDirectory p m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      tab_ok
  case Pdpt p m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      tab_ok
  case Pml4 p m a =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      tab_ok
  case Ept p l m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      tab_ok
  case HighVSpace p m a =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      tab_ok
  all_goals (simp only [objects.derive_cap]; tab_ok)

/-- `derive_cap`'s two facts together. -/
theorem objects.derive_cap.derT (s : S) (slot : U64) (c : capability.Cap) :
    objects.derive_cap st s slot c ⦃ r => ∀ nc, r = .Ok nc → DerivA nc c ∧ TabEq nc c ⦄ :=
  WP.spec_mono (WP.spec_and (objects.derive_cap.der s slot c) (objects.derive_cap.tab s slot c))
    fun _ ⟨h1, h2⟩ nc e => ⟨h1 nc e, h2 nc e⟩

set_option maxHeartbeats 1000000 in
/-- **CNode Copy / Mint's new cap: `DerivA` and `TabEq` the source cap.** -/
theorem cnode.copied_cap.derT (s : S) (lbl length buf src : U64) (src_cap : capability.Cap) :
    cnode.copied_cap st s lbl length buf src src_cap ⦃ r => ∀ nc, r = .Ok (nc, false) →
      DerivA nc src_cap ∧ TabEq nc src_cap ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have fin : ∀ (m : capability.Cap), TabEq m src_cap → ∀ x : core.result.Result capability.Cap error.Exc,
      (∀ nc, x = .Ok nc → DerivA nc m ∧ TabEq nc m) →
      (do
        let cf ← core.result.Result.Insts.CoreOpsTry.branch x
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val => ok (core.result.Result.Ok (val, false))
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (capability.Cap × Bool) (core.convert.FromSame error.Exc) residual :
        Result (core.result.Result (capability.Cap × Bool) error.Exc)) ⦃ r =>
        ∀ nc, r = .Ok (nc, false) → DerivA nc src_cap ∧ TabEq nc src_cap ⦄ := by
    intro m ht x hx
    rcases x with v | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
      intro nc h; cases h; exact ⟨(hx v rfl).1.tab ht, (hx v rfl).2.trans ht⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      first
      | exact (WP.spec_ok _).2 fun nc h => (by cases h)
      | (simp only [WP.spec_ok]; intro nc h; cases h)
  unfold cnode.copied_cap
  refine WP.spec_bind (P0.sched.cur_thread.p0 st s hS) fun ct _ => ?_
  split
  · split
    · simp only [error.truncated, WP.spec_ok]; intro nc h; cases h
    · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun i _ => ?_
      refine WP.spec_bind (P0.capability.Rights.from_word.p0 i) fun rr _ => ?_
      refine WP.spec_bind (capability.mask_cap_rights.tab rr src_cap) fun c hc => ?_
      exact WP.spec_bind (objects.derive_cap.derT s src c) fun r1 h1 => fin c hc r1 h1
  · split
    · split
      · simp only [error.truncated, WP.spec_ok]; intro nc h; cases h
      · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun i _ => ?_
        refine WP.spec_bind (P0.capability.Rights.from_word.p0 i) fun rr _ => ?_
        refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun data _ => ?_
        refine WP.spec_bind (capability.mask_cap_rights.tab rr src_cap) fun c hc => ?_
        refine WP.spec_bind (objects.update_cap_data.tab false data c) fun c1 hc1 => ?_
        exact WP.spec_bind (objects.derive_cap.derT s src c1) fun r1 h1 => fin c1 (hc1.trans hc) r1 h1
    · split
      · exact (WP.spec_ok _).2 fun nc h => by cases h
      · split
        · simp only [error.truncated, WP.spec_ok]; intro nc h; cases h
        · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun data _ => ?_
          exact WP.spec_bind (P0.objects.update_cap_data.p0 true data src_cap) fun _ _ =>
            (WP.spec_ok _).2 fun nc h => by cases h

/-- A `PageTable` cap of `p` (`n = 4096`) or a level-0 `Ept` cap of `p` (`n = 8192`): `VsC` on a cap. -/
def VsCapA (c : capability.Cap) (p : U64) (n : Nat) : Prop :=
  (n = 4096 ∧ ∃ m a v, c = .PageTable p m a v) ∨ (n = 8192 ∧ ∃ m a v, c = .Ept p 0#u64 m a v)

theorem VsC_iff {x p : U64} {n : Nat} {s : S} : VsC st x p n s ↔ VsCapA (capA st s x) p n := by
  unfold VsC VsCapA; rw [capA_eq]
  constructor
  · rintro (⟨hn, m, a, v, e⟩ | ⟨hn, m, a, v, e⟩)
    · exact Or.inl ⟨hn, m, a, v, okinj e⟩
    · exact Or.inr ⟨hn, m, a, v, okinj e⟩
  · rintro (⟨hn, m, a, v, e⟩ | ⟨hn, m, a, v, e⟩)
    · exact Or.inl ⟨hn, m, a, v, by rw [e]⟩
    · exact Or.inr ⟨hn, m, a, v, by rw [e]⟩

theorem VsCapA.nm {c : capability.Cap} {p : U64} {n : Nat} (h : VsCapA c p n) : NmCap c p := by
  rcases h with ⟨-, m, a, v, e⟩ | ⟨-, m, a, v, e⟩
  · exact Or.inl ⟨m, a, v, e⟩
  · exact Or.inr ⟨0#u64, m, a, v, e⟩

section ins
variable {OS : Set U64}

/-- **`UnmU` along the insertion of a cap `DerivA` and `TabEq` the source's** (data level): every slot's table cap
after is the table cap of its old slot (`oldA`: `dest` ↦ `src`), so `dis` / `pool` carry over; `one` is gen 48's
`one_ins`. -/
theorem UnmU.ins {Pp : Set U64} {s s' : S} (hU : UnmU st OS Pp s) {src dest : U64} {nc sc : capability.Cap}
    (hsrc : src ∈ OS) (hsc : capA st s src = sc) (hD : DerivA nc sc) (hT : TabEq nc sc)
    (hcd : capA st s' dest = nc)
    (hk : ∀ y ∈ OS, y ≠ dest → capA st s' y = capA st s y ∨ ∃ p b i d, capA st s' y = .Untyped p b i d) :
    UnmU st OS Pp s' := by
  have old : ∀ z ∈ OS, ∀ p n, VsCapA (capA st s' z) p n → oldA src dest z ∈ OS ∧
      VsCapA (capA st s (oldA src dest z)) p n := by
    intro z hz p n h
    unfold oldA
    by_cases e : z = dest
    · rw [if_pos e]
      rw [e, hcd] at h
      refine ⟨hsrc, ?_⟩
      rw [hsc, ← hT.1 p h.nm]; exact h
    · rw [if_neg e]
      refine ⟨hz, ?_⟩
      rcases hk z hz e with e' | ⟨q, b, i, d, e'⟩
      · rwa [e'] at h
      · rw [e'] at h
        exfalso; rcases h with ⟨-, _, _, _, h⟩ | ⟨-, _, _, _, h⟩ <;> cases h
  refine ⟨one_ins hU.one hsrc hsc hD hcd hk, fun x hx y hy p q n m hx' hy' hpq => ?_, fun x hx p n hx' => ?_⟩
  · rw [VsC_iff] at hx' hy'
    obtain ⟨ox, vx⟩ := old x hx p n hx'
    obtain ⟨oy, vy⟩ := old y hy q m hy'
    exact hU.dis _ ox _ oy p q n m (VsC_iff.2 vx) (VsC_iff.2 vy) hpq
  · rw [VsC_iff] at hx'
    obtain ⟨ox, vx⟩ := old x hx p n hx'
    exact hU.pool _ ox p n (VsC_iff.2 vx)

variable {G : List (List U64)}

set_option maxHeartbeats 1000000 in
/-- **`UnmU` kept by `cdt::insert_with_cap`** of a cap `DerivA` and `TabEq` the source's (CNode Copy / Mint:
`cnode.copied_cap.derT`). -/
theorem cdt.insert_with_cap.unmU (hO : OSOK T Ω Sg OS) {s : S} (hM : MdbLk st OS G s)
    {Pp : Set U64} (hU : UnmU st OS Pp s) {src dest : U64} {nc sc : capability.Cap}
    (hsrc : src ∈ G.flatten) (hd : dest ∈ OS) (hd0 : capA st s dest = .Null) (hdc : obj.sext48 dest = ok dest)
    (hsc : capA st s src = sc) (hw : CapRt.EncWf nc) (hD : DerivA nc sc) (hT : TabEq nc sc) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => UnmU st OS Pp s' ⦄ := by
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF hO.nz
  have os := inOS src hsrc
  have hs0 : capA st s src ≠ .Null := ((hM.members src).1 hsrc).2
  have hsc0 : sc ≠ .Null := by rw [← hsc]; exact hs0
  have dG : dest ∉ G.flatten := fun hm => ((hM.members dest).1 hm).2 hd0
  have hsd : src ≠ dest := fun e => dG (e ▸ hsrc)
  have hNm : NxA st s src ≠ 0#u64 → NxA st s src ∈ G.flatten := F.nxm _ hsrc
  refine WP.spec_mono (cdt.insert_with_cap.lr hO (LR.self s) os hd hsd hdc hsc hsc0 hw
    (fun h => inOS _ (hNm h))) ?_
  rintro s' ⟨-, ed, -, -, ek, u⟩
  refine hU.ins os hsc hD hT ed fun y hy hyd => ?_
  by_cases e : y = src
  · rw [e]; exact u
  · exact Or.inl (ek y hy e hyd)

end ins

end ST
end R
end W7

end

end Fl4ProofsA64.P1
