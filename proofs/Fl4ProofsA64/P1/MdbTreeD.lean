/-
P1 (aarch64, gen 55): **`UA` of the decode tops' new caps and of the `Zombie` rewrite; `hut` from `derive_cap`** —
the hypotheses gen 54's tree steps (`cdt.insert_with_cap.tree`, `cdt.insert.tree`, `cdt.swap.tree`,
`cdt.move_cap.tree`, `TreeA.set_cap`) take on a new cap, discharged as gen 50's `AlikeA` ones are (MdbCopy).

* **`UN d c`** (MdbCopy's `AlN` for `UA`): `d` is `Null`, or `UA d c` with `c` non-null; `UN.trans`, `UN.ne`,
  **`UA.of_eqN`** (same `cap_is_physical`, `ptr`, `cap_size_bits`, both not `Untyped`: closed by `rfl` on concrete
  caps) — x86 `UtEq` from `CapAlike` (MdbStep).
* **`capability.mask_cap_rights.ua`**, **`objects.update_cap_data.ua`**, **`objects.derive_cap.ua`**,
  **`cnode.copied_cap.ua`**: each result `UN` its argument (mirrors of MdbCopy's `.al` lemmas, same case split;
  an `Untyped` cap passes all four unchanged: `UA.refl`).
* **`objects.derive_cap.noDesc`**: an `Ok` of `derive_cap` at a revocable `Untyped` slot of the tree means the slot
  has no descendants (`ensure_no_children.noDesc`) — the `hut` hypothesis of `insert_with_cap.tree`.
* **The `Zombie` rewrite** (finalise_cap, cnode.rs / objects.rs: `CNode p r` → `Zombie p r 2^r`, `Thread p` →
  `Zombie (slot p 0) ZOMBIE_TCB NUM_SLOTS`, a `Zombie`'s count changed): **`UA.zombie_cnode`** (radix `< 64`,
  `EncWf`), **`UA.zombie_thread`** (`SLOT_CTABLE = 0`, so the `Zombie`'s pointer is the TCB's),
  **`UA.zombie`**.
* (gen 62) **`cnode.copied_cap.chainG`**: the one traversal of `copied_cap`'s Copy / Mint branches, the new cap a
  `derive_cap` result (`D`) of a cap `R`-related to the source; `uaG` is its instance (proof in place), and
  **`cnode.copied_cap.nz`** (with **`objects.derive_cap.nz`**: a `Zombie` becomes `Null`): the new cap is no
  `Zombie` (`NZA`, `AlikeA.nz`).

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.MdbTreeL
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- Two non-`Untyped` caps with the same physical bit, base and size bits are alike for `UtInvA`. -/
theorem UA.of_eqN {d c : capability.Cap} (h1 : objects.cap_is_physical d = objects.cap_is_physical c)
    (h2 : capability.Cap.ptr d = capability.Cap.ptr c) (h3 : objects.cap_size_bits d = objects.cap_size_bits c)
    (h5 : isUtA d = isUtA c) (h6 : isUtA c = false) : UA d c :=
  ⟨okinj ((physA_eq d).symm.trans (h1.trans (physA_eq c))), okinj ((ptrA_eq d).symm.trans (h2.trans (ptrA_eq c))),
    okinj ((sizeA_eq d).symm.trans (h3.trans (sizeA_eq c))), h5, fun p b i e h => by
      rw [h] at h5; rw [← h5] at h6; cases h6⟩

/-- `d` is `Null`, or `UA` a non-null `c`. -/
def UN (d c : capability.Cap) : Prop := d = .Null ∨ (UA d c ∧ c ≠ .Null)

theorem UA.trans {a b c : capability.Cap} (h1 : UA a b) (h2 : UA b c) : UA a c := by
  refine ⟨h1.phys.trans h2.phys, h1.ptr.trans h2.ptr, h1.size.trans h2.size, h1.isut.trans h2.isut,
    fun p q i e h => ?_⟩
  obtain ⟨i1, e1, hb, l1, o1⟩ := h1.ut p q i e h
  obtain ⟨i0, e0, hc, l0, o0⟩ := h2.ut p q i1 e1 hb
  refine ⟨i0, e0, hc, le_trans l0 l1, ?_⟩
  rcases o1 with rfl | o1
  · exact o0
  · exact Or.inr o1

theorem UN.trans {a b c : capability.Cap} (h1 : UN a b) (h2 : UN b c) : UN a c := by
  rcases h1 with e | ⟨h1, hb⟩
  · exact Or.inl e
  · rcases h2 with e | ⟨h2, hc⟩
    · exact absurd e hb
    · exact Or.inr ⟨h1.trans h2, hc⟩

theorem UN.ne {d c : capability.Cap} (h : UN d c) (hd : d ≠ .Null) : UA d c := by
  rcases h with e | ⟨h, -⟩
  · exact absurd e hd
  · exact h

set_option hygiene false in
/-- Closes `UN` of a concrete result against a concrete argument. -/
local macro "uan" : tactic => `(tactic| (
  first
  | exact Or.inl rfl
  | exact Or.inr ⟨UA.refl _, fun e => by cases e⟩
  | exact Or.inr ⟨UA.of_eqN rfl rfl rfl rfl rfl, fun e => by cases e⟩))

/-- **`mask_cap_rights` keeps the cap `UA`** (MdbCopy `mask_cap_rights.al`). -/
theorem capability.mask_cap_rights.ua (r : capability.Rights) (c : capability.Cap) :
    capability.mask_cap_rights r c ⦃ m => UN m c ⦄ := by
  cases c
  case Endpoint p b sd rc g gr =>
    cases sd <;> cases rc <;> cases g <;> cases gr <;>
      simp only [capability.mask_cap_rights, Bool.false_eq_true, ↓reduceIte, bind_ok] <;>
      exact (WP.spec_ok _).2 (by uan)
  case Notification p b sd rc =>
    cases sd <;> cases rc <;>
      simp only [capability.mask_cap_rights, Bool.false_eq_true, ↓reduceIte, bind_ok] <;>
      exact (WP.spec_ok _).2 (by uan)
  case Reply p g =>
    cases g <;> simp only [capability.mask_cap_rights, Bool.false_eq_true, ↓reduceIte] <;>
      exact (WP.spec_ok _).2 (by uan)
  case Frame p sz rt dv mp ep asd va =>
    simp only [capability.mask_cap_rights]
    exact WP.spec_bind (P0.capability.mask_vm_rights.p0 rt r) fun _ _ => (WP.spec_ok _).2 (by uan)
  all_goals (simp only [capability.mask_cap_rights]; exact (WP.spec_ok _).2 (by uan))

/-- **`update_cap_data` keeps the cap `UA` or returns `Null`** (MdbCopy `update_cap_data.al`). -/
theorem objects.update_cap_data.ua (pr : Bool) (data : U64) (c : capability.Cap) :
    objects.update_cap_data pr data c ⦃ m => UN m c ⦄ := by
  cases c
  case Endpoint p b sd rc g gr =>
    simp only [objects.update_cap_data]
    split
    · exact (WP.spec_ok _).2 (by uan)
    · split <;> exact (WP.spec_ok _).2 (by uan)
  case Notification p b sd rc =>
    simp only [objects.update_cap_data]
    split
    · exact (WP.spec_ok _).2 (by uan)
    · split <;> exact (WP.spec_ok _).2 (by uan)
  case CNode p rd gs g =>
    simp only [objects.update_cap_data]
    refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
    refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
    split
    · exact (WP.spec_ok _).2 (by uan)
    · refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
      refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
      refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
      exact (WP.spec_ok _).2 (by uan)
  all_goals (simp only [objects.update_cap_data]; exact (WP.spec_ok _).2 (by uan))

set_option hygiene false in
/-- An `Ok` result of `derive_cap` (closes `UN`). -/
local macro "ua_ok" : tactic => `(tactic| (
  refine (WP.spec_ok _).2 fun nc h => ?_
  cases h
  uan))

set_option maxHeartbeats 1000000 in
/-- **`derive_cap` returns a cap `UA` its argument, or `Null`** (MdbCopy `derive_cap.al`). -/
theorem objects.derive_cap.ua (s : S) (slot : U64) (c : capability.Cap) :
    objects.derive_cap st s slot c ⦃ r => ∀ nc, r = .Ok nc → UN nc c ⦄ := by
  have hS : P0.StoreTotal st := L.total
  cases c
  case Untyped p b i d =>
    simp only [objects.derive_cap]
    refine WP.spec_bind (P0.cdt.ensure_no_children.p0 st s slot hS) fun r _ => ?_
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      ua_ok
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
      ua_ok
  case PageDirectory p m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      ua_ok
  case Pdpt p m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      ua_ok
  case Pml4 p m a =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      ua_ok
  case Ept p l m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      ua_ok
  case HighVSpace p m a =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      ua_ok
  all_goals (simp only [objects.derive_cap]; ua_ok)

set_option maxHeartbeats 1000000 in
/-- (gen 62) **CNode Copy / Mint's new cap is a `derive_cap` result**: for any transitive relation `R` that
`mask_cap_rights` and `update_cap_data` respect and any relation `D` of `derive_cap`'s result to its argument, every
`Ok (nc, false)` has `D nc m` for some `m` with `R m src_cap` (the one traversal of `copied_cap`'s Copy / Mint
branches; `uaG` is its instance with `D := R`, `copied_cap.nz` the one with `D` = "not a `Zombie`"). -/
theorem cnode.copied_cap.chainG {R D : capability.Cap → capability.Cap → Prop}
    (htr : ∀ {a b c : capability.Cap}, R a b → R b c → R a c)
    (hmk : ∀ (r : capability.Rights) (c : capability.Cap), capability.mask_cap_rights r c ⦃ m => R m c ⦄)
    (hup : ∀ (pr : Bool) (data : U64) (c : capability.Cap), objects.update_cap_data pr data c ⦃ m => R m c ⦄)
    (hdv : ∀ (s : S) (slot : U64) (c : capability.Cap),
      objects.derive_cap st s slot c ⦃ r => ∀ nc, r = .Ok nc → D nc c ⦄)
    (s : S) (lbl length buf src : U64) (src_cap : capability.Cap) :
    cnode.copied_cap st s lbl length buf src src_cap ⦃ r => ∀ nc, r = .Ok (nc, false) →
      ∃ m, R m src_cap ∧ D nc m ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have fin : ∀ (m : capability.Cap), R m src_cap → ∀ x : core.result.Result capability.Cap error.Exc,
      (∀ nc, x = .Ok nc → D nc m) →
      (do
        let cf ← core.result.Result.Insts.CoreOpsTry.branch x
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val => ok (core.result.Result.Ok (val, false))
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (capability.Cap × Bool) (core.convert.FromSame error.Exc) residual :
        Result (core.result.Result (capability.Cap × Bool) error.Exc)) ⦃ r =>
        ∀ nc, r = .Ok (nc, false) → ∃ m, R m src_cap ∧ D nc m ⦄ := by
    intro m ht x hx
    rcases x with v | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
      intro nc h; cases h; exact ⟨m, ht, hx v rfl⟩
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
      refine WP.spec_bind (hmk rr src_cap) fun c hc => ?_
      exact WP.spec_bind (hdv s src c) fun r1 h1 => fin c hc r1 h1
  · split
    · split
      · simp only [error.truncated, WP.spec_ok]; intro nc h; cases h
      · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun i _ => ?_
        refine WP.spec_bind (P0.capability.Rights.from_word.p0 i) fun rr _ => ?_
        refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun data _ => ?_
        refine WP.spec_bind (hmk rr src_cap) fun c hc => ?_
        refine WP.spec_bind (hup false data c) fun c1 hc1 => ?_
        exact WP.spec_bind (hdv s src c1) fun r1 h1 => fin c1 (htr hc1 hc) r1 h1
    · split
      · exact (WP.spec_ok _).2 fun nc h => by cases h
      · split
        · simp only [error.truncated, WP.spec_ok]; intro nc h; cases h
        · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun data _ => ?_
          exact WP.spec_bind (P0.objects.update_cap_data.p0 true data src_cap) fun _ _ =>
            (WP.spec_ok _).2 fun nc h => by cases h

set_option maxHeartbeats 1000000 in
/-- (gen 60) **CNode Copy / Mint's new cap is related to the source cap by any transitive relation `R` that
`mask_cap_rights`, `update_cap_data` and `derive_cap` respect** (`copied_cap.ua`'s proof, the relation abstracted;
`copied_cap.ua` is its `UN` instance, MdbUZS's `copied_cap.ue` its `UE` one). -/
theorem cnode.copied_cap.uaG {R : capability.Cap → capability.Cap → Prop}
    (htr : ∀ {a b c : capability.Cap}, R a b → R b c → R a c)
    (hmk : ∀ (r : capability.Rights) (c : capability.Cap), capability.mask_cap_rights r c ⦃ m => R m c ⦄)
    (hup : ∀ (pr : Bool) (data : U64) (c : capability.Cap), objects.update_cap_data pr data c ⦃ m => R m c ⦄)
    (hdv : ∀ (s : S) (slot : U64) (c : capability.Cap),
      objects.derive_cap st s slot c ⦃ r => ∀ nc, r = .Ok nc → R nc c ⦄)
    (s : S) (lbl length buf src : U64) (src_cap : capability.Cap) :
    cnode.copied_cap st s lbl length buf src src_cap ⦃ r => ∀ nc, r = .Ok (nc, false) → R nc src_cap ⦄ :=
  WP.spec_mono (cnode.copied_cap.chainG (R := R) (D := R) htr hmk hup hdv s lbl length buf src src_cap)
    fun r (h : ∀ nc, r = .Ok (nc, false) → ∃ m, R m src_cap ∧ R nc m) nc e => by
      obtain ⟨m, h1, h2⟩ := h nc e
      exact htr h2 h1

set_option maxHeartbeats 1000000 in
/-- **CNode Copy / Mint's new cap is `UN` the source cap** (MdbCopy `copied_cap.al`). -/
theorem cnode.copied_cap.ua (s : S) (lbl length buf src : U64) (src_cap : capability.Cap) :
    cnode.copied_cap st s lbl length buf src src_cap ⦃ r => ∀ nc, r = .Ok (nc, false) → UN nc src_cap ⦄ :=
  cnode.copied_cap.uaG (R := UN) (fun h1 h2 => UN.trans h1 h2) (fun r c => capability.mask_cap_rights.ua r c)
    (fun pr d c => objects.update_cap_data.ua pr d c) (fun s sl c => objects.derive_cap.ua s sl c) s lbl length buf src
    src_cap

/-- (gen 62) **Not a `Zombie`.** -/
def NZA (c : capability.Cap) : Prop := ∀ p t n, c ≠ .Zombie p t n

/-- (gen 62) A cap alike a non-`Zombie` cap is no `Zombie` (a `Zombie` is a key cap of its own kind). -/
theorem AlikeA.nz {d c : capability.Cap} (h : AlikeA d c) (hc : NZA c) : NZA d := by
  intro p t n e
  subst e
  have k := h.1.1 (RngKeyA.zombie p t n)
  have e2 : kindA c = 9 := (h.2 k).2.symm
  cases c <;> first | exact hc _ _ _ rfl | (simp [kindA] at e2)

/-- (gen 62) **`derive_cap` never returns a `Zombie`** (objects.rs:208–239: a `Zombie` becomes `Null`; the other
kinds are kept alike, MdbCopy `derive_cap.al`). -/
theorem objects.derive_cap.nz (s : S) (slot : U64) (c : capability.Cap) :
    objects.derive_cap st s slot c ⦃ r => ∀ nc, r = .Ok nc → NZA nc ⦄ := by
  by_cases hz : ∃ p t n, c = .Zombie p t n
  · obtain ⟨p, t, n, rfl⟩ := hz
    simp only [objects.derive_cap]
    exact (WP.spec_ok _).2 fun nc h => by cases h; exact fun _ _ _ e => by cases e
  · refine WP.spec_mono (objects.derive_cap.al s slot c) fun r h nc e => ?_
    rcases h nc e with rfl | ⟨ha, -⟩
    · exact fun _ _ _ e => by cases e
    · exact ha.nz fun p t n e => hz ⟨p, t, n, e⟩

set_option maxHeartbeats 1000000 in
/-- (gen 62) **CNode Copy / Mint's new cap is no `Zombie`** (`copied_cap.chainG` with `derive_cap.nz`). -/
theorem cnode.copied_cap.nz (s : S) (lbl length buf src : U64) (src_cap : capability.Cap) :
    cnode.copied_cap st s lbl length buf src src_cap ⦃ r => ∀ nc, r = .Ok (nc, false) → NZA nc ⦄ :=
  WP.spec_mono (cnode.copied_cap.chainG (R := fun _ _ => True) (D := fun nc _ => NZA nc) (fun _ _ => trivial)
    (fun _ _ => WP.spec_mono (P0.capability.mask_cap_rights.p0 _ _) fun _ _ => trivial)
    (fun _ _ _ => WP.spec_mono (P0.objects.update_cap_data.p0 _ _ _) fun _ _ => trivial)
    (fun s sl c => objects.derive_cap.nz s sl c) s lbl length buf src src_cap) fun _ h nc e =>
    (h nc e).elim fun _ ⟨_, h2⟩ => h2

/-! ## `hut` from `derive_cap` -/

section hut
variable {OS : Set U64} {G : List (List U64)} {par : U64 → Option U64}

/-- **`derive_cap`'s `Ok` at a revocable `Untyped` slot of the tree: no descendants** (`ensure_no_children.noDesc`;
the `hut` of `insert_with_cap.tree`). -/
theorem objects.derive_cap.noDesc (hO : OSOK T Ω Sg OS) {s : S} (h : TreeA st OS G par s) {x p b i : U64}
    {d : Bool} (hx : x ∈ OS) (hcx : capA st s x = .Untyped p b i d) (hr : obj.Slot.revocable st x s = ok true) :
    objects.derive_cap st s x (.Untyped p b i d) ⦃ r => ∀ nc, r = .Ok nc → ∀ y, ¬ Mdb.Desc par y x ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨v, hv, -⟩ := spec_exA (P0.cdt.ensure_no_children.p0 st s x hS)
  simp only [objects.derive_cap]
  rw [hv, bind_ok]
  rcases v with u | e
  · cases u
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
    intro nc _
    exact cdt.ensure_no_children.noDesc hO h hx hcx hr hv
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    first
    | exact (WP.spec_ok _).2 fun nc h => (by cases h)
    | (simp only [WP.spec_ok]; intro nc h; cases h)

end hut

/-! ## The `Zombie` rewrite -/

/-- A `CNode` becomes a `Zombie` of its radix (radix `< 64`, so not the TCB tag `65`). -/
theorem UA.zombie_cnode (p r g gs n : U64) (hr : r.val < 64) : UA (.Zombie p r n) (.CNode p r g gs) := by
  have hne : r ≠ capability.ZOMBIE_TCB := fun e => by
    rw [e] at hr; simp [capability.ZOMBIE_TCB] at hr
  have e3 : objects.cap_size_bits (.Zombie p r n) = objects.cap_size_bits (.CNode p r g gs) := by
    simp only [objects.cap_size_bits, hne, ↓reduceIte]
  exact UA.of_eqN rfl rfl e3 rfl rfl

/-- A `Thread` becomes the `Zombie` at its first slot, which is the TCB itself (`SLOT_CTABLE = 0`). -/
theorem UA.zombie_thread (p n : U64) :
    UA (.Zombie (core.num.U64.wrapping_add p (core.num.U64.wrapping_mul layout.tcb.SLOT_CTABLE layout.cte.SIZE))
      capability.ZOMBIE_TCB n) (.Thread p) := by
  have e0 : core.num.U64.wrapping_add p (core.num.U64.wrapping_mul layout.tcb.SLOT_CTABLE layout.cte.SIZE) = p := by
    apply UScalar.eq_of_val_eq
    simp [layout.tcb.SLOT_CTABLE, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq,
      U64.size_def, U64.numBits]
    try (have := p.hBounds; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits] at this; omega)
  rw [e0]
  have e3 : objects.cap_size_bits (.Zombie p capability.ZOMBIE_TCB n) = objects.cap_size_bits (.Thread p) := by
    simp [objects.cap_size_bits]
  exact UA.of_eqN rfl rfl e3 rfl rfl

/-- A `Zombie`'s count changed. -/
theorem UA.zombie (p t n n' : U64) : UA (.Zombie p t n') (.Zombie p t n) := UA.of_eqN rfl rfl rfl rfl rfl

end ST
end R
end W7

end

end Fl4ProofsA64.P1
