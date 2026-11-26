/-
P2 (line glue, gen 1): **start facts at the serial-prefix memory** (audU F1), at the level of `Serial`.

`SerialSafe.SafeStep.start` asks a started body to be `Safe` from the *physical* memory `s.mem`, and every FL4
start fact discharges it from a store state agreeing with `s.mem` (`StartAt` / `GlueAt`). While another core's body
is mid-way, `s.mem` holds its partial writes, at which P3's invariant need not hold, so no such state exists there
(audU F1). This module lets the start be stated at the **serial-prefix memory** `H` instead: Serial's own invariant
memory (`InvH`: the completed entries run in completion order), carried as a ghost index of the execution.

* `NextH s c s' H`: the ghost update, exactly `InvH.step`'s witnesses (a serial body: the new memory; a finished
  local path with writes `W`: `mix W s.mem H`; otherwise `H`). `XSafeRunH s0 s H`: executions with that ghost
  (hardware writes update `H` with the same write).
* `SafeStepH.start`: the body is `Safe` from `s.mem` **given `VEq … H s.mem`**: on every word the core may read,
  `H` and `s.mem` agree in value and owner, and on class-tracked words in class. `VEq` is proved, not assumed
  (`veq_start`), from three invariants:
  - `InvH` (Serial's): `s.mem = H` off the in-progress write sets, which their cores hold;
  - **`OwnInv s H`** (new): applying more in-progress bodies' writes to `H` (`MOf s H E`, the writes of the cores
    in `E`) moves owners only among owners those bodies hold. Kept by every step using `MoveHeld` of the ownership
    map (an argument of each core step, `SafeStepH.mh`; proved for FL4's `ownP`, `moveHeldP`), and by hardware
    writes moving no owner at any memory;
  - **`SW s`** (new): an in-progress path that has written is in a `Safe` body, so a path at `.start` has written
    nothing.
* **`serializable_safeXH`**: where an `XSafeRunH` reaches a state with no local path in progress, memory is the
  serial run of the completed entries (`SerialHw.serializable_safeX`'s conclusion).

No premises (everything is a hypothesis of the theorems). No existing statement changed.
-/
import Fl4Proofs.P2.SerialHw

namespace Fl4Proofs.P2.Serial

noncomputable section
open Classical

variable {A V C L : Type} [DecidableEq A] [DecidableEq C] [DecidableEq L]

/-! ## The sets and memories of the ghost history -/

/-- The words an in-progress local path has written (`∅` for any other phase). -/
def phW : Phase A V L → Set A
  | .loc _ _ W => W
  | _ => ∅

theorem phW_of {X : Phase A V L} {p0 p : Prog A V L} {W : Set A} (h : X = .loc p0 p W) : phW X = W := by
  subst h; rfl

theorem phW_nonloc {X : Phase A V L} (h : ¬ X.IsLoc) : phW X = ∅ := by
  cases X with
  | idle => rfl
  | arm _ => rfl
  | ser _ => rfl
  | loc _ _ _ => exact absurd trivial h

theorem phW_upd {f : C → Phase A V L} {c : C} {X : Phase A V L} (hX : phW X = phW (f c)) (e : C) :
    phW (Function.update f c X e) = phW (f e) := by
  by_cases h : e = c
  · rw [h, Function.update_self]; exact hX
  · rw [Function.update_of_ne h]

/-- The words written so far by the in-progress local paths of the cores `E`. -/
def WOf (s : Cfg A V C L) (E : Set C) : Set A := {x | ∃ e ∈ E, x ∈ phW (s.ph e)}

/-- The history `H` with the in-progress writes of the cores `E` applied. -/
def MOf (s : Cfg A V C L) (H : A → V) (E : Set C) : A → V := mix (WOf s E) s.mem H

/-- **Owners between the history and the memory**: applying the in-progress writes of more cores moves owners
only among owners those cores hold. -/
def OwnInv (s : Cfg A V C L) (H : A → V) : Prop :=
  ∀ E1 E2 : Set C, E1 ⊆ E2 → ∀ x, s.own (MOf s H E2) x ≠ s.own (MOf s H E1) x →
    ∃ e, e ∈ E2 ∧ e ∉ E1 ∧ Held s.lk e (s.own (MOf s H E2) x) ∧ Held s.lk e (s.own (MOf s H E1) x)

/-- **An in-progress path that has written is in a `Safe` body.** -/
def SW (s : Cfg A V C L) : Prop :=
  ∀ d p0 q W, s.ph d = .loc p0 q W → W ≠ ∅ →
    Safe s.own s.cls s.ko d (fun l => s.lk l = some d) s.mem q

/-- **Core `c`'s view of `ρ` and `μ` agrees**: readable owners of `ρ` are `μ`'s, readable words of `μ` have `ρ`'s
values, class-tracked words `c` reads have `ρ`'s classes. -/
def VEq (own : (A → V) → A → Owner C L) (cls : A → V → V) (ko : A → ClsOwner C) (c : C)
    (hs : L → Prop) (ρ μ : A → V) : Prop :=
  (∀ x, PO c hs (own ρ x) → own μ x = own ρ x) ∧ (∀ y, PO c hs (own μ y) → ρ y = μ y) ∧
    (∀ y, (ko y = .gate ∨ ko y = .core c) → cls y (ρ y) = cls y (μ y))

/-- **The ghost update of the history** (`InvH.step`'s witnesses). -/
def NextH (s : Cfg A V C L) (c : C) (s' : Cfg A V C L) (H : A → V) : A → V :=
  if s.gate = .closed then s'.mem else if s'.log = s.log then H else mix (phW (s.ph c)) s.mem H

theorem nextH_closed {s s' : Cfg A V C L} {c : C} {H : A → V} (hg : s.gate = .closed) :
    NextH s c s' H = s'.mem := by
  unfold NextH; rw [if_pos hg]

theorem nextH_same {s s' : Cfg A V C L} {c : C} {H : A → V} (hg : s.gate ≠ .closed) (hl : s'.log = s.log) :
    NextH s c s' H = H := by
  unfold NextH; rw [if_neg hg, if_pos hl]

theorem nextH_leave {s s' : Cfg A V C L} {c : C} {H : A → V} (hg : s.gate ≠ .closed) (hl : ¬ s'.log = s.log) :
    NextH s c s' H = mix (phW (s.ph c)) s.mem H := by
  unfold NextH; rw [if_neg hg, if_neg hl]

theorem log_ne (l : List (Prog A V L)) (p : Prog A V L) : ¬ l ++ [p] = l := by
  intro e; have := congrArg List.length e; simp at this

theorem held_uniq {lk : L → Option C} {e c : C} {o : Owner C L} (h1 : Held lk e o) (h2 : Held lk c o) :
    e = c := by
  by_contra h; exact held_disj h h1 (Or.inl h2)

section mof
variable {m0 : A → V} {s : Cfg A V C L} {H : A → V}

theorem held_phW (I : InvH m0 s H) {e : C} {x : A} (hx : x ∈ phW (s.ph e)) : Held s.lk e (s.own s.mem x) := by
  generalize hph : s.ph e = X at hx
  cases X with
  | idle => exact absurd hx (Set.notMem_empty x)
  | arm _ => exact absurd hx (Set.notMem_empty x)
  | ser _ => exact absurd hx (Set.notMem_empty x)
  | loc p0 p W => exact (I.loc e p0 p W hph).held x hx

theorem exists_W_of_ne (I : InvH m0 s H) {y : A} (hne : ¬ H y = s.mem y) :
    ∃ d, y ∈ phW (s.ph d) := by
  by_contra hno
  exact hne (I.agree y fun d q0 q U hd hyU => hno ⟨d, by rw [hd]; exact hyU⟩).symm

theorem mOf_univ (I : InvH m0 s H) : MOf s H Set.univ = s.mem := by
  funext x
  unfold MOf
  by_cases hx : x ∈ WOf s Set.univ
  · exact mix_mem hx
  · rw [mix_nmem hx]
    by_contra hne
    obtain ⟨d, hd⟩ := exists_W_of_ne I hne
    exact hx ⟨d, Set.mem_univ d, hd⟩

theorem mOf_single {c : C} (h : phW (s.ph c) = ∅) : MOf s H {c} = H := by
  funext x
  unfold MOf
  rw [mix_nmem]
  rintro ⟨e, he, hx⟩
  rw [Set.mem_singleton_iff.mp he, h] at hx
  exact Set.notMem_empty x hx

theorem mOf_noloc (hn : NoLoc s) (E : Set C) : MOf s H E = H := by
  funext x
  unfold MOf
  rw [mix_nmem]
  rintro ⟨e, -, hx⟩
  rw [phW_nonloc (hn e)] at hx
  exact Set.notMem_empty x hx

theorem ownInv_noloc (hn : NoLoc s) : OwnInv s H := by
  intro E1 E2 _ x hx
  rw [mOf_noloc hn, mOf_noloc hn] at hx
  exact absurd rfl hx

/-- **The start view** (module docstring): at a `.start`, `VEq` of the history and the memory. -/
theorem veq_start (I : InvH m0 s H) (O : OwnInv s H) (Sw : SW s) {c : C} {p0 k : Prog A V L} {W : Set A}
    (hc : s.ph c = .loc p0 (.start k) W) :
    VEq s.own s.cls s.ko c (fun l => s.lk l = some c) H s.mem := by
  have hW : W = ∅ := by
    by_contra hne
    have h := Sw c p0 _ W hc hne
    cases h
  have hW0 : phW (s.ph c) = ∅ := by rw [hc]; exact hW
  have hne : ∀ e x, x ∈ phW (s.ph e) → e ≠ c := by
    rintro e x hx rfl; rw [hW0] at hx; exact Set.notMem_empty x hx
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · by_contra hn
    have hd : s.own (MOf s H Set.univ) x ≠ s.own (MOf s H {c}) x := by
      rw [mOf_univ I, mOf_single hW0]; exact hn
    obtain ⟨e, -, he, -, h2⟩ := O {c} Set.univ (Set.subset_univ _) x hd
    rw [mOf_single hW0] at h2
    exact not_PO_of_held (fun h => he (Set.mem_singleton_iff.mpr h)) h2 hx
  · by_contra hn
    obtain ⟨d, hyd⟩ := exists_W_of_ne I hn
    exact not_PO_of_held (hne d y hyd) (held_phW I hyd) hy
  · rcases I.clsinv y with h | ⟨e, q0, q, U, he, hyU, hk⟩
    · exact h.symm
    · exfalso
      have hec : e ≠ c := hne e y (by rw [he]; exact hyU)
      rcases hy with h1 | h1 <;> rcases hk with h2 | h2 <;> rw [h1] at h2 <;>
        first | exact hec (ClsOwner.core.inj h2).symm | cases h2

end mof

/-! ## The history at the ghost update -/

theorem noLoc_step {s s' : Cfg A V C L} {c : C} (hn : NoLoc s) (hst : Step s c s') (hg : s.gate = .closed) :
    NoLoc s' := by
  intro d hd
  by_cases hdc : d = c
  · rw [hdc] at hd
    cases hst with
    | arm p _ =>
      change (Function.update s.ph c _ c).IsLoc at hd; rw [Function.update_self] at hd; exact hd
    | enter _ hg' => rw [hg] at hg'; cases hg'
    | back _ _ =>
      change (Function.update s.ph c _ c).IsLoc at hd; rw [Function.update_self] at hd; exact hd
    | rd hc => exact absurd (by rw [hc]; trivial) (hn c)
    | rds hc => exact absurd (by rw [hc]; trivial) (hn c)
    | rdc hc => exact absurd (by rw [hc]; trivial) (hn c)
    | start hc => exact absurd (by rw [hc]; trivial) (hn c)
    | wr hc => exact absurd (by rw [hc]; trivial) (hn c)
    | lock _ hc _ => exact absurd (by rw [hc]; trivial) (hn c)
    | leave hc => exact absurd (by rw [hc]; trivial) (hn c)
    | take _ _ _ =>
      change (Function.update s.ph c _ c).IsLoc at hd; rw [Function.update_self] at hd; exact hd
    | scan _ _ _ _ => exact hn c hd
    | drain _ _ _ => exact hn c hd
    | serial _ _ _ _ _ _ _ _ =>
      change (Function.update s.ph c _ c).IsLoc at hd; rw [Function.update_self] at hd; exact hd
  · rw [step_ph_other hst hdc] at hd; exact hn d hd

/-- **`InvH` at the ghost update.** -/
theorem InvH.stepN {m0 : A → V} {s s' : Cfg A V C L} {H : A → V} {c : C}
    (I : InvH m0 s H) (hal : Allowed s c) (h : Step s c s') : InvH m0 s' (NextH s c s' H) := by
  by_cases hg : s.gate = .closed
  · rw [nextH_closed hg]
    obtain ⟨H', I'⟩ := I.step hal h
    have nl' := noLoc_step (I.clo hg) h hg
    have e : s'.mem = H' := funext fun x =>
      I'.agree x (fun d q0 q U hd => absurd (by rw [hd]; trivial) (nl' d))
    rw [e]; exact I'
  · by_cases hl : s'.log = s.log
    · rw [nextH_same hg hl]
      cases h with
      | arm p hc => exact inv_phase I (Phase.arm_not_loc p) (by rw [hc]; exact Phase.idle_not_loc)
      | enter hc hg' => exact inv_enter I hc hg'
      | back hc _ => exact inv_phase I Phase.idle_not_loc (by rw [hc]; exact Phase.arm_not_loc _)
      | rd hc =>
        simp only [Allowed, hc] at hal
        exact inv_rd I hc hal
      | wr hc =>
        simp only [Allowed, hc] at hal
        exact inv_wr I hc hal.1 hal.2.1 hal.2.2
      | rdc hc =>
        simp only [Allowed, hc] at hal
        exact inv_rdc I hc hal.1 hal.2
      | lock b hc hb => exact inv_lock I hc b hb
      | rds hc => exact inv_rds I hc
      | start hc => exact inv_start I hc
      | leave hc => exact absurd hl (log_ne _ _)
      | take p hc _ => exact inv_take I p hc
      | scan d _ _ hd => exact inv_scan I d hd
      | drain _ hg' hall => exact inv_drain I hg' hall
      | serial _ _ _ _ _ hg' _ _ => exact absurd hg' hg
    · rw [nextH_leave hg hl]
      cases h
      all_goals first | exact absurd rfl hl | skip
      case leave p0 W hc => rw [phW_of hc]; exact inv_leave I hc
      case serial _ _ _ _ _ _ _ hg' _ _ => exact absurd hg' hg

/-! ## `OwnInv` along the steps -/

section own
variable {m0 : A → V} {s : Cfg A V C L} {H : A → V}

theorem ownInv_frame {s' : Cfg A V C L} (O : OwnInv s H) (hmem : s'.mem = s.mem) (hown : s'.own = s.own)
    (hph : ∀ e, phW (s'.ph e) = phW (s.ph e)) (hlk : ∀ e o, Held s.lk e o → Held s'.lk e o) :
    OwnInv s' H := by
  have hM : ∀ E, MOf s' H E = MOf s H E := by
    intro E
    have hW : WOf s' E = WOf s E := by
      ext x; simp only [WOf, Set.mem_setOf_eq, hph]
    unfold MOf; rw [hW, hmem]
  intro E1 E2 h12 x hx
  rw [hM E1, hM E2, hown] at hx
  rw [hM E1, hM E2, hown]
  obtain ⟨e, h1, h2, h3, h4⟩ := O E1 E2 h12 x hx
  exact ⟨e, h1, h2, hlk _ _ h3, hlk _ _ h4⟩

/-- **A local write keeps `OwnInv`** (the one step that needs `MoveHeld`). -/
theorem ownInv_wr (I : InvH m0 s H) (O : OwnInv s H) (hMH : MoveHeld s.own) {c : C} {p0 : Prog A V L} {a : A}
    {v : V} {k : Prog A V L} {W : Set A} (hc : s.ph c = .loc p0 (.wr a v k) W)
    (ha : Held s.lk c (s.own s.mem a))
    (hmv : ∀ x, s.own (Function.update s.mem a v) x ≠ s.own s.mem x →
        Held s.lk c (s.own s.mem x) ∧ Held s.lk c (s.own (Function.update s.mem a v) x))
    {s' : Cfg A V C L} (hmem : s'.mem = Function.update s.mem a v) (hown : s'.own = s.own)
    (hlk : s'.lk = s.lk) (hph : s'.ph = Function.update s.ph c (.loc p0 k (insert a W))) :
    OwnInv s' H := by
  have hphc : phW (s'.ph c) = insert a W := by rw [hph, Function.update_self]; rfl
  have hphe : ∀ e, e ≠ c → phW (s'.ph e) = phW (s.ph e) := fun e h => by rw [hph, Function.update_of_ne h]
  have hWc : phW (s.ph c) = W := phW_of hc
  have memW : ∀ E x, x ∈ WOf s' E ↔ (c ∈ E ∧ x = a) ∨ x ∈ WOf s E := by
    intro E x
    constructor
    · rintro ⟨e, he, hx⟩
      by_cases hec : e = c
      · rw [hec] at he hx
        rw [hphc] at hx
        rcases Set.mem_insert_iff.mp hx with h | h
        · exact Or.inl ⟨he, h⟩
        · exact Or.inr ⟨c, he, by rw [hWc]; exact h⟩
      · exact Or.inr ⟨e, he, by rw [← hphe e hec]; exact hx⟩
    · rintro (⟨hcE, hxa⟩ | ⟨e, he, hx⟩)
      · exact ⟨c, hcE, by rw [hphc, hxa]; exact Set.mem_insert _ _⟩
      · by_cases hec : e = c
        · rw [hec] at he hx
          exact ⟨c, he, by rw [hphc]; rw [hWc] at hx; exact Set.mem_insert_of_mem _ hx⟩
        · exact ⟨e, he, by rw [hphe e hec]; exact hx⟩
  have hWa : ∀ e, a ∈ phW (s.ph e) → e = c := fun e h => held_uniq (held_phW I h) ha
  have F2a : ∀ E, c ∈ E → MOf s' H E = Function.update (MOf s H E) a v := by
    intro E hcE; funext x; unfold MOf
    by_cases hxa : x = a
    · rw [hxa, Function.update_self, mix_mem ((memW E a).mpr (Or.inl ⟨hcE, rfl⟩)), hmem,
        Function.update_self]
    · rw [Function.update_of_ne hxa]
      by_cases hx : x ∈ WOf s E
      · rw [mix_mem ((memW E x).mpr (Or.inr hx)), mix_mem hx, hmem, Function.update_of_ne hxa]
      · rw [mix_nmem (fun h => ((memW E x).mp h).elim (fun h' => hxa h'.2) hx), mix_nmem hx]
  have F2b : ∀ E, c ∉ E → MOf s' H E = MOf s H E := by
    intro E hcE; funext x; unfold MOf
    by_cases hx : x ∈ WOf s E
    · rw [mix_mem ((memW E x).mpr (Or.inr hx)), mix_mem hx, hmem]
      obtain ⟨e, he, hxe⟩ := hx
      have hxa : x ≠ a := by
        rintro rfl; exact hcE (by rw [← hWa e hxe]; exact he)
      exact Function.update_of_ne hxa _ _
    · rw [mix_nmem (fun h => ((memW E x).mp h).elim (fun h' => hcE h'.1) hx), mix_nmem hx]
  have hmU := mOf_univ I
  have F3 : ∀ E, c ∈ E → s.own (MOf s H E) a = s.own s.mem a := by
    intro E hcE; by_contra hne
    obtain ⟨e, -, he, h1, -⟩ := O E Set.univ (Set.subset_univ _) a (by rw [hmU]; exact Ne.symm hne)
    rw [hmU] at h1
    exact he (by rw [held_uniq h1 ha]; exact hcE)
  have F4 : ∀ E, c ∈ E → ∀ y, PO c (fun l => s.lk l = some c) (s.own (MOf s H E) y) →
      MOf s H E y = s.mem y := by
    intro E hcE y hy
    by_contra hne
    by_cases hyW : y ∈ WOf s E
    · exact hne (mix_mem hyW)
    · have hne' : ¬ H y = s.mem y := by
        intro e; apply hne; unfold MOf; rw [mix_nmem hyW]; exact e
      obtain ⟨d, hyd⟩ := exists_W_of_ne I hne'
      have hdc : d ≠ c := fun h => hyW ⟨d, by rw [h]; exact hcE, hyd⟩
      have hHd := held_phW I hyd
      by_cases he : s.own s.mem y = s.own (MOf s H E) y
      · rw [← he] at hy; exact not_PO_of_held hdc hHd hy
      · obtain ⟨e, -, heE, -, h2⟩ := O E Set.univ (Set.subset_univ _) y (by rw [hmU]; exact he)
        exact not_PO_of_held (fun h => heE (by rw [h]; exact hcE)) h2 hy
  have F5 : ∀ E1 E2, E1 ⊆ E2 → c ∈ E1 → ∀ y,
      (PO c (fun l => s.lk l = some c) (s.own (MOf s H E1) y) ∨
        PO c (fun l => s.lk l = some c) (s.own (MOf s H E2) y)) →
      s.own (MOf s H E2) y = s.own (MOf s H E1) y := by
    intro E1 E2 h12 hc1 y hy; by_contra hne
    obtain ⟨e, -, he1, h2, h1⟩ := O E1 E2 h12 y hne
    have hec : e ≠ c := fun h => he1 (by rw [h]; exact hc1)
    rcases hy with hy | hy
    · exact not_PO_of_held hec h1 hy
    · exact not_PO_of_held hec h2 hy
  have F6 : ∀ E1 E2, E1 ⊆ E2 → c ∈ E1 → ∀ y,
      (PO c (fun l => s.lk l = some c) (s.own (MOf s H E1) y) ∨
        PO c (fun l => s.lk l = some c) (s.own (MOf s H E2) y)) →
      MOf s H E2 y = MOf s H E1 y := by
    intro E1 E2 h12 hc1 y hy
    have e5 := F5 E1 E2 h12 hc1 y hy
    have hp1 : PO c (fun l => s.lk l = some c) (s.own (MOf s H E1) y) := by
      rcases hy with hy | hy
      · exact hy
      · rw [← e5]; exact hy
    have hp2 : PO c (fun l => s.lk l = some c) (s.own (MOf s H E2) y) := by rw [e5]; exact hp1
    rw [F4 E1 hc1 y hp1, F4 E2 (h12 hc1) y hp2]
  intro E1 E2 h12 x hx
  rw [hown] at hx
  rw [hown, hlk]
  by_cases hc2 : c ∈ E2
  · have ha2 : HeldV c (fun l => s.lk l = some c) (s.own (MOf s H E2) a) := by
      rw [F3 E2 hc2]; exact heldV_of_held ha
    rw [F2a E2 hc2] at hx ⊢
    by_cases hc1 : c ∈ E1
    · have ha1 : HeldV c (fun l => s.lk l = some c) (s.own (MOf s H E1) a) := by
        rw [F3 E1 hc1]; exact heldV_of_held ha
      rw [F2a E1 hc1] at hx ⊢
      by_cases h1 : s.own (Function.update (MOf s H E1) a v) x = s.own (MOf s H E1) x
      · by_cases h2 : s.own (Function.update (MOf s H E2) a v) x = s.own (MOf s H E2) x
        · rw [h1, h2] at hx ⊢; exact O E1 E2 h12 x hx
        · exfalso
          obtain ⟨-, e2⟩ := hMH c (fun l => s.lk l = some c) (MOf s H E2) (MOf s H E1) a v x ha2
            (fun y hy => (F6 E1 E2 h12 hc1 y (Or.inr hy)).symm) h2
          exact hx e2.symm
      · exfalso
        obtain ⟨-, e2⟩ := hMH c (fun l => s.lk l = some c) (MOf s H E1) (MOf s H E2) a v x ha1
          (fun y hy => F6 E1 E2 h12 hc1 y (Or.inl hy)) h1
        exact hx e2
    · rw [F2b E1 hc1] at hx ⊢
      by_cases h2 : s.own (Function.update (MOf s H E2) a v) x = s.own (MOf s H E2) x
      · rw [h2] at hx ⊢; exact O E1 E2 h12 x hx
      · obtain ⟨e1, e2⟩ := hMH c (fun l => s.lk l = some c) (MOf s H E2) s.mem a v x ha2
          (fun y hy => (F4 E2 hc2 y hy).symm) h2
        have hch : s.own (Function.update s.mem a v) x ≠ s.own s.mem x := by rw [e1, e2]; exact h2
        obtain ⟨hA, hB⟩ := hmv x hch
        rw [e1] at hA; rw [e2] at hB
        refine ⟨c, hc2, hc1, hB, ?_⟩
        by_cases h21 : s.own (MOf s H E2) x = s.own (MOf s H E1) x
        · rw [← h21]; exact hA
        · obtain ⟨e, -, -, g2, g1⟩ := O E1 E2 h12 x h21
          rw [← held_uniq g2 hA]; exact g1
  · have hc1 : c ∉ E1 := fun h => hc2 (h12 h)
    rw [F2b E2 hc2, F2b E1 hc1] at hx ⊢
    exact O E1 E2 h12 x hx

/-- **A finished local path keeps `OwnInv`**, the history taking its writes. -/
theorem ownInv_leave (O : OwnInv s H) {c : C} {p0 : Prog A V L} {W : Set A}
    (hc : s.ph c = .loc p0 .done W) {s' : Cfg A V C L} (hmem : s'.mem = s.mem) (hown : s'.own = s.own)
    (hlk : s'.lk = release s.lk c) (hph : s'.ph = Function.update s.ph c .idle) :
    OwnInv s' (mix W s.mem H) := by
  have hphc : phW (s'.ph c) = ∅ := by rw [hph, Function.update_self]; rfl
  have hphe : ∀ e, e ≠ c → phW (s'.ph e) = phW (s.ph e) := fun e h => by rw [hph, Function.update_of_ne h]
  have hiff : ∀ E x, x ∈ WOf s (insert c E) ↔ x ∈ WOf s' E ∨ x ∈ W := by
    intro E x
    constructor
    · rintro ⟨e, he, hx⟩
      by_cases hec : e = c
      · rw [hec, phW_of hc] at hx; exact Or.inr hx
      · exact Or.inl ⟨e, (Set.mem_insert_iff.mp he).resolve_left hec, by rw [hphe e hec]; exact hx⟩
    · rintro (⟨e, he, hx⟩ | h)
      · have hec : e ≠ c := by
          rintro rfl; rw [hphc] at hx; exact Set.notMem_empty x hx
        exact ⟨e, Set.mem_insert_of_mem _ he, by rw [← hphe e hec]; exact hx⟩
      · exact ⟨c, Set.mem_insert _ _, by rw [phW_of hc]; exact h⟩
  have hM : ∀ E, MOf s' (mix W s.mem H) E = MOf s H (insert c E) := by
    intro E; funext x; unfold MOf
    by_cases h1 : x ∈ WOf s' E
    · rw [mix_mem h1, mix_mem ((hiff E x).mpr (Or.inl h1)), hmem]
    · rw [mix_nmem h1]
      by_cases h2 : x ∈ W
      · rw [mix_mem h2, mix_mem ((hiff E x).mpr (Or.inr h2))]
      · rw [mix_nmem h2, mix_nmem (fun h => ((hiff E x).mp h).elim h1 h2)]
  intro E1 E2 h12 x hx
  rw [hM E1, hM E2, hown] at hx
  rw [hM E1, hM E2, hown, hlk]
  obtain ⟨e, he2, he1, g2, g1⟩ := O (insert c E1) (insert c E2) (Set.insert_subset_insert h12) x hx
  have hec : e ≠ c := fun h => he1 (by rw [h]; exact Set.mem_insert c E1)
  exact ⟨e, (Set.mem_insert_iff.mp he2).resolve_left hec, fun h => he1 (Set.mem_insert_of_mem c h),
    held_release hec g2, held_release hec g1⟩

/-- **A hardware write keeps `OwnInv`**, the history taking the same write, given that the write moves no owner
at any memory. -/
theorem ownInv_hw (I : InvH m0 s H) (O : OwnInv s H) {a : A} {x : V} {l : L} (h : HwWr s a x l)
    (hk : ∀ m, s.own (Function.update m a x) = s.own m) :
    OwnInv (hwCfg s a x) (Function.update H a x) := by
  have hna : ∀ E, a ∉ WOf s E := by
    rintro E ⟨e, -, he⟩; exact h.ne_of_held (held_phW I he) rfl
  have hM : ∀ E, MOf (hwCfg s a x) (Function.update H a x) E = Function.update (MOf s H E) a x := by
    intro E; funext y
    show mix (WOf s E) (Function.update s.mem a x) (Function.update H a x) y =
      Function.update (mix (WOf s E) s.mem H) a x y
    by_cases hya : y = a
    · rw [hya, mix_nmem (hna E), Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hya]
      by_cases hy : y ∈ WOf s E
      · rw [mix_mem hy, mix_mem hy]; exact Function.update_of_ne hya _ _
      · rw [mix_nmem hy, mix_nmem hy]; exact Function.update_of_ne hya _ _
  intro E1 E2 h12 y hy
  have hy' : s.own (MOf s H E2) y ≠ s.own (MOf s H E1) y := by
    have h0 := hy
    rw [hM E1, hM E2] at h0
    change s.own (Function.update (MOf s H E2) a x) y ≠ s.own (Function.update (MOf s H E1) a x) y at h0
    rw [hk, hk] at h0; exact h0
  obtain ⟨e, h1, h2, g2, g1⟩ := O E1 E2 h12 y hy'
  refine ⟨e, h1, h2, ?_, ?_⟩
  · rw [hM E2]; change Held s.lk e (s.own (Function.update (MOf s H E2) a x) y); rw [hk]; exact g2
  · rw [hM E1]; change Held s.lk e (s.own (Function.update (MOf s H E1) a x) y); rw [hk]; exact g1

/-- **`OwnInv` at the ghost update.** -/
theorem ownInv_step {c : C} {s' : Cfg A V C L} (I : InvH m0 s H) (O : OwnInv s H) (hal : Allowed s c)
    (hMH : MoveHeld s.own) (hst : Step s c s') : OwnInv s' (NextH s c s' H) := by
  by_cases hg : s.gate = .closed
  · rw [nextH_closed hg]
    exact ownInv_noloc (noLoc_step (I.clo hg) hst hg)
  · by_cases hl : s'.log = s.log
    · rw [nextH_same hg hl]
      cases hst with
      | arm p hc =>
        exact ownInv_frame O rfl rfl (phW_upd (by rw [hc]; rfl)) (fun _ _ h => h)
      | enter hc _ =>
        exact ownInv_frame O rfl rfl (phW_upd (by rw [hc]; rfl)) (fun _ _ h => h)
      | back hc _ =>
        exact ownInv_frame O rfl rfl (phW_upd (by rw [hc]; rfl)) (fun _ _ h => h)
      | rd hc =>
        exact ownInv_frame O rfl rfl (phW_upd (by rw [hc]; rfl)) (fun _ _ h => h)
      | rds hc =>
        exact ownInv_frame O rfl rfl (phW_upd (by rw [hc]; rfl)) (fun _ _ h => h)
      | rdc hc =>
        exact ownInv_frame O rfl rfl (phW_upd (by rw [hc]; rfl)) (fun _ _ h => h)
      | start hc =>
        exact ownInv_frame O rfl rfl (phW_upd (by rw [hc]; rfl)) (fun _ _ h => h)
      | wr hc =>
        simp only [Allowed, hc] at hal
        exact ownInv_wr I O hMH hc hal.1 hal.2.1 rfl rfl rfl rfl
      | lock b hc hb =>
        exact ownInv_frame O rfl rfl (phW_upd (by rw [hc]; rfl)) (fun _ _ h => held_lock hb h)
      | leave hc => exact absurd hl (log_ne _ _)
      | take p hc _ =>
        exact ownInv_frame O rfl rfl (phW_upd (by rw [hc]; rfl)) (fun _ _ h => h)
      | scan _ _ _ _ => exact ownInv_frame O rfl rfl (fun _ => rfl) (fun _ _ h => h)
      | drain _ _ _ => exact ownInv_frame O rfl rfl (fun _ => rfl) (fun _ _ h => h)
      | serial _ _ _ _ _ hg' _ _ => exact absurd hg' hg
    · rw [nextH_leave hg hl]
      cases hst
      all_goals first | exact absurd rfl hl | skip
      case leave p0 W hc => rw [phW_of hc]; exact ownInv_leave O hc rfl rfl rfl rfl
      case serial _ _ _ _ _ _ _ hg' _ _ => exact absurd hg' hg

end own

/-! ## `SW` along the steps -/

theorem lock_iff {lk : L → Option C} {c d : C} {l : L} {b : Bool} (hdc : d ≠ c) (hb : b = true → lk l = none)
    (l' : L) : lk l' = some d ↔ (if b then Function.update lk l (some c) else lk) l' = some d := by
  cases b with
  | false => rw [if_neg (by decide)]
  | true =>
    rw [if_pos rfl]
    by_cases hl : l' = l
    · subst hl
      rw [Function.update_self, hb rfl]
      exact ⟨fun h => by cases h, fun h => absurd (Option.some.inj h) (Ne.symm hdc)⟩
    · rw [Function.update_of_ne hl]

theorem release_iff {lk : L → Option C} {c d : C} (hdc : d ≠ c) (l' : L) :
    lk l' = some d ↔ release lk c l' = some d := by
  show lk l' = some d ↔ (if lk l' = some c then none else lk l') = some d
  by_cases hl : lk l' = some c
  · rw [if_pos hl, hl]
    exact ⟨fun h => absurd (Option.some.inj h) (Ne.symm hdc), fun h => by cases h⟩
  · rw [if_neg hl]

/-- **`SW` is kept by every core step.** -/
theorem sw_step {s s' : Cfg A V C L} {c : C} (hno : s.gate = .closed → NoLoc s) (Sw : SW s) (I : SInv s)
    (hal : Allowed s c) (hst : Step s c s') : SW s' := by
  intro d p0 q W hd hW
  cases hst with
  | arm p hc =>
    have hd' : Function.update s.ph c (.arm p) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'; exact Sw d p0 q W hd' hW
  | back hc _ =>
    have hd' : Function.update s.ph c .idle d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'; exact Sw d p0 q W hd' hW
  | @enter p hc _ =>
    have hd' : Function.update s.ph c (.loc p p ∅) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'; exact absurd rfl hW
    · rw [Function.update_of_ne hdc] at hd'; exact Sw d p0 q W hd' hW
  | @rd p1 a k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      have hS := Sw d _ _ W1 hc hW
      cases hS with
      | rd _ h => exact h _ (.refl _)
    · rw [Function.update_of_ne hdc] at hd'; exact Sw d p0 q W hd' hW
  | @rds p1 a k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      have hS := Sw d _ _ W1 hc hW
      cases hS with
      | rds h => exact h _ (.refl _)
    · rw [Function.update_of_ne hdc] at hd'; exact Sw d p0 q W hd' hW
  | @rdc p1 a K k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      have hS := Sw d _ _ W1 hc hW
      cases hS with
      | rdc _ _ h => exact h _ (.refl _)
    · rw [Function.update_of_ne hdc] at hd'; exact Sw d p0 q W hd' hW
  | @start p1 k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 k W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      have hS := Sw d _ _ W1 hc hW
      cases hS
    · rw [Function.update_of_ne hdc] at hd'; exact Sw d p0 q W hd' hW
  | @wr p1 a v k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 k (insert a W1)) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg
      · cases hS with
        | wr _ _ _ h => exact h _ (.refl _)
    · rw [Function.update_of_ne hdc] at hd'
      have hS := Sw d p0 q W hd' hW
      simp only [Allowed, hc] at hal
      obtain ⟨hb, hmv, hcl⟩ := hal
      have hcd : c ≠ d := Ne.symm hdc
      have hF : Foreign s.own s.cls s.ko d (fun l => s.lk l = some d) s.mem a v := by
        refine ⟨not_PO_of_held hcd hb, fun x hx =>
          ⟨not_PO_of_held hcd (hmv x hx).1, not_PO_of_held hcd (hmv x hx).2⟩, ?_⟩
        rcases hcl with h | h | h
        · exact Or.inl h
        · refine Or.inr ⟨?_, ?_⟩
          · rw [h]; intro e; cases e
          · rw [h]; intro e; exact hcd (ClsOwner.core.inj e)
        · refine Or.inr ⟨?_, ?_⟩
          · rw [h]; intro e; cases e
          · rw [h]; intro e; cases e
      exact Safe.foreign (q := q) hS hF
  | @lock p1 l k W1 b hc hb =>
    have hd' : Function.update s.ph c (.loc p1 (k b) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      have hS := Sw d _ _ W1 hc hW
      cases hS
    · rw [Function.update_of_ne hdc] at hd'
      exact Safe.congr (lock_iff hdc hb) (Sw d p0 q W hd' hW)
  | @leave p1 W1 hc =>
    have hd' : Function.update s.ph c .idle d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'
      exact Safe.congr (release_iff hdc) (Sw d p0 q W hd' hW)
  | take p hc _ =>
    have hd' : Function.update s.ph c (.ser p) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'; exact Sw d p0 q W hd' hW
  | scan e _ _ _ => exact Sw d p0 q W hd hW
  | drain _ _ _ => exact Sw d p0 q W hd hW
  | serial keep own' cls' ko' _ hg _ _ =>
    have hd' : Function.update s.ph c .idle d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'
      exact absurd (by rw [hd']; trivial) (hno hg d)

/-- **`SW` is kept by a hardware write** (to every path it is `Foreign`). -/
theorem sw_hw {s : Cfg A V C L} (Sw : SW s) {a : A} {x : V} {l : L} (h : HwWr s a x l) :
    SW (hwCfg s a x) := by
  intro d p0 q W hd hW
  have hS := Sw d p0 q W hd hW
  have hF : Foreign s.own s.cls s.ko d (fun l => s.lk l = some d) s.mem a x := by
    refine ⟨?_, fun y hy => absurd (by rw [h.keep]) hy, ?_⟩
    · rw [h.own]; rintro (hl | hl)
      · change s.lk l = some d at hl; rw [h.free] at hl; cases hl
      · cases hl
    · right; rw [h.ko]; exact ⟨(fun e => by cases e), (fun e => by cases e)⟩
  exact Safe.foreign hS hF

/-! ## Executions with the ghost history -/

/-- **What is asked of a core step** (module docstring): an armed program is pure glue; a started body is `Safe`
from the memory given the core's view of the history and the memory agrees (`VEq`, proved at every start:
`veq_start`); the ownership map has `MoveHeld`. -/
structure SafeStepH (s : Cfg A V C L) (c : C) (s' : Cfg A V C L) (H : A → V) : Prop where
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W →
    VEq s.own s.cls s.ko c (fun l => s.lk l = some c) H s.mem →
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem k
  mh : MoveHeld s.own

/-- **An execution with its serial-prefix memory** (ghost `H`, updated by `NextH`; a hardware write updates it
with the same write, and moves no owner at any memory). -/
inductive XSafeRunH (s0 : Cfg A V C L) : Cfg A V C L → (A → V) → Prop
  | refl : XSafeRunH s0 s0 s0.mem
  | step {s s' : Cfg A V C L} {H : A → V} {c : C} :
      XSafeRunH s0 s H → Step s c s' → SafeStepH s c s' H → XSafeRunH s0 s' (NextH s c s' H)
  | hw {s : Cfg A V C L} {H : A → V} {a : A} {x : V} {l : L} :
      XSafeRunH s0 s H → HwWr s a x l → (∀ m, s.own (Function.update m a x) = s.own m) →
      XSafeRunH s0 (hwCfg s a x) (Function.update H a x)

/-- **The invariants along an `XSafeRunH`**: `H` is Serial's history memory (`InvH`), with `OwnInv`, `SW`, `SInv`
and `ArmInv`. -/
theorem xsafeRunH_inv {s0 s : Cfg A V C L} {H : A → V} (h0 : Init s0) (hA0 : ArmInv s0)
    (h : XSafeRunH s0 s H) :
    InvH s0.mem s H ∧ OwnInv s H ∧ SW s ∧ SInv s ∧ ArmInv s := by
  induction h with
  | refl =>
    exact ⟨inv_init h0, ownInv_noloc h0.2, fun d p0 q W hd _ => absurd (by rw [hd]; trivial) (h0.2 d),
      fun d p0 q W hd => absurd (by rw [hd]; trivial) (h0.2 d), hA0⟩
  | @step s s' H c _ hst hok ih =>
    obtain ⟨I, O, Sw, Si, Ar⟩ := ih
    have hal := allowed_of_sinv Si c
    have hB : ∀ p0 k W, s.ph c = .loc p0 (.start k) W →
        Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem k :=
      fun p0 k W hc => hok.start p0 k W hc (veq_start I O Sw hc)
    exact ⟨I.stepN hal hst, ownInv_step I O hal hok.mh hst, sw_step I.clo Sw Si hal hst,
      sinv_stepX I.clo Ar hB Si hal hst, armInv_step Ar hst ⟨hok.arm, hB⟩⟩
  | hw _ hh hk ih =>
    obtain ⟨I, O, Sw, Si, Ar⟩ := ih
    exact ⟨inv_hw I hh, ownInv_hw I O hh hk, sw_hw Sw hh, sinv_hw Si hh, Ar⟩

/-- **Every `XSafeRunH` is a serial one**: where it reaches a state with no local path in progress, memory is what
running the completed entries one after another in completion order produces (a speculative read returning any
value, as in `Serial`). -/
theorem serializable_safeXH {s0 s : Cfg A V C L} {H : A → V} (h0 : Init s0) (hA0 : ArmInv s0)
    (h : XSafeRunH s0 s H) (hq : NoLoc s) : RunAll s.log s0.mem s.mem := by
  obtain ⟨I, -⟩ := xsafeRunH_inv h0 hA0 h
  have e : s.mem = H := funext fun x =>
    I.agree x (fun d q0 q U hd => absurd (by rw [hd]; trivial) (hq d))
  rw [e]; exact I.hist

/-- **The history is the memory on every word a core may read**, at every `XSafeRunH` state (part of `VEq`, for
use outside the start). -/
theorem xsafeRunH_agree {s0 s : Cfg A V C L} {H : A → V} (h0 : Init s0) (hA0 : ArmInv s0)
    (h : XSafeRunH s0 s H) (x : A) (hx : ∀ d, ¬ Held s.lk d (s.own s.mem x)) : H x = s.mem x := by
  obtain ⟨I, -⟩ := xsafeRunH_inv h0 hA0 h
  by_contra hne
  obtain ⟨d, hd⟩ := exists_W_of_ne I hne
  exact hx d (held_phW I hd)

end

end Fl4Proofs.P2.Serial
