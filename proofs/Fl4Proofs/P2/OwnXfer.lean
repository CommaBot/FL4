/-
# P2 (line p3mc, gen 53): **owner transfer** — `Safe` / `InsA` / `InsAP` move between two owner maps that differ only
on a word set the run avoids (§57b's T1, fully abstract)

The run-relative obligations of a started body (`SerialSafe.Safe`, `SerialADR.InsA`, `SerialADP.InsAP`) take the
owner map `own` as a parameter; it enters through the reachable memories (`FReach` / `FReachA`: other cores'
`Foreign` writes, environment `ADStep`s) and through `Safe`'s per-access checks (`PO`, `HeldV`, `MoveV`). Here two
owner maps `own₁` (source) and `own₂` (target) are compared:

* **`OwnXfer W own₁ own₂`** (a `Prop` structure, hypotheses only): `own₂` = `own₁` off `W` (`off`); `own₁`'s owner of
  a word off `W` is decided by the memory off `W` (`loc`); a write to a word off `W` changes no owner of a `W` word,
  for either map (`keep₁`, `keep₂`). **`OwnXfer.symm`**: the hypotheses are symmetric (so every transfer below holds
  in both directions).
* **`Avoid W Rch μ p`**: along the run of `p` from `μ`, at every memory `Rch`-reached before an access, the access
  (`rd` / `rds` / `rdc` / `wr`) is to a word off `W` (run-relative, like `Safe`; garbage branches unconstrained).
  `Avoid.mono` (a smaller reachability), **`avoid_of_within`** (a tree-level footprint `Within Wᶜ` gives it at every
  memory and reachability).
* `EqOff W μ₂ μ₁`: the memories agree off `W`.
* Simulations: **`freach_xfer`** / **`freachA_xfer`**: a memory reached at `own₂` from `μ₂` is matched, off `W`, by
  one reached at `own₁` from any `μ₁` agreeing with `μ₂` off `W` (a `Foreign` / `ADStep` write to a `W` word is
  absorbed, one off `W` is replayed).
* **`safe_xfer`**: `Safe own₁ … μ₁ p`, `Avoid W (FReach own₁ …) μ₁ p`, `EqOff W μ₂ μ₁` ⇒ `Safe own₂ … μ₂ p`.
* **`insA_xfer`** / **`insAP_xfer`**: the same for `InsA` / `InsAP` (any done set), with `Avoid` over
  `FReachA … own₁ …`.
* **`safe_insAP_xfer`**: `Safe ∧ InsAP` together from one `Avoid` over `FReachA` (`Avoid.mono` + `FReachA.of_freach`).

`InsT` / `InsTP` (E2EADQ / E2EADQP) are store-level predicates with no owner map: nothing to transfer.

Nothing here mentions a layout, the P3 chain or a VCPU; `cls`, `ko`, the core and its locks are shared by both
sides. Named premises: none (everything is a hypothesis of the theorems). New module; no existing file touched.
-/
import Fl4Proofs.P2.SerialADP

namespace Fl4Proofs.P2.Serial

noncomputable section

variable {A V C L : Type} [DecidableEq A] [DecidableEq C] [DecidableEq L]

/-! ## Hypotheses on the two owner maps -/

/-- **Two owner maps differing only inside `W`** (module docstring). -/
structure OwnXfer (W : Set A) (own₁ own₂ : (A → V) → A → Owner C L) : Prop where
  /-- Off `W` the maps agree. -/
  off : ∀ μ x, x ∉ W → own₂ μ x = own₁ μ x
  /-- Off `W`, `own₁` reads only the memory off `W`. -/
  loc : ∀ μ μ' : A → V, (∀ y, y ∉ W → μ y = μ' y) → ∀ x, x ∉ W → own₁ μ x = own₁ μ' x
  /-- A write off `W` keeps `own₁`'s owners of `W` words. -/
  keep₁ : ∀ μ b v x, b ∉ W → x ∈ W → own₁ (Function.update μ b v) x = own₁ μ x
  /-- A write off `W` keeps `own₂`'s owners of `W` words. -/
  keep₂ : ∀ μ b v x, b ∉ W → x ∈ W → own₂ (Function.update μ b v) x = own₂ μ x

/-- The memories agree off `W`. -/
def EqOff (W : Set A) (μ₂ μ₁ : A → V) : Prop := ∀ y, y ∉ W → μ₂ y = μ₁ y

theorem eqOff_refl (W : Set A) (μ : A → V) : EqOff W μ μ := fun _ _ => rfl

theorem EqOff.symm {W : Set A} {μ₂ μ₁ : A → V} (h : EqOff W μ₂ μ₁) : EqOff W μ₁ μ₂ :=
  fun y hy => (h y hy).symm

theorem EqOff.update {W : Set A} {μ₂ μ₁ : A → V} (h : EqOff W μ₂ μ₁) (b : A) (v : V) :
    EqOff W (Function.update μ₂ b v) (Function.update μ₁ b v) := by
  intro y hy
  by_cases hyb : y = b
  · subst hyb; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hyb, Function.update_of_ne hyb]; exact h y hy

theorem EqOff.update_in {W : Set A} {μ₂ μ₁ : A → V} (h : EqOff W μ₂ μ₁) {b : A} (hb : b ∈ W) (v : V) :
    EqOff W (Function.update μ₂ b v) μ₁ := by
  intro y hy
  have hyb : y ≠ b := fun e => hy (e ▸ hb)
  rw [Function.update_of_ne hyb]; exact h y hy

namespace OwnXfer
variable {W : Set A} {own₁ own₂ : (A → V) → A → Owner C L}

/-- Off `W`, `own₂` reads only the memory off `W` too. -/
theorem loc₂ (X : OwnXfer W own₁ own₂) (μ μ' : A → V) (h : ∀ y, y ∉ W → μ y = μ' y) (x : A) (hx : x ∉ W) :
    own₂ μ x = own₂ μ' x := by
  rw [X.off μ x hx, X.off μ' x hx]; exact X.loc μ μ' h x hx

/-- **The hypotheses are symmetric.** -/
theorem symm (X : OwnXfer W own₁ own₂) : OwnXfer W own₂ own₁ where
  off μ x hx := (X.off μ x hx).symm
  loc := X.loc₂
  keep₁ := X.keep₂
  keep₂ := X.keep₁

/-- The two maps' owners of a word off `W` at memories agreeing off `W`. -/
theorem own_eq (X : OwnXfer W own₁ own₂) {μ₂ μ₁ : A → V} (h : EqOff W μ₂ μ₁) {x : A} (hx : x ∉ W) :
    own₂ μ₂ x = own₁ μ₁ x :=
  (X.off μ₂ x hx).trans (X.loc μ₂ μ₁ h x hx)

end OwnXfer

/-! ## Runs avoiding `W` -/

/-- **The run of `p` from `μ` touches no `W` word** at the memories `Rch` reaches before each access (module
docstring). -/
inductive Avoid (W : Set A) (Rch : (A → V) → (A → V) → Prop) : (A → V) → Prog A V L → Prop
  | done {μ : A → V} : Avoid W Rch μ .done
  | rd {μ : A → V} {a : A} {k : V → Prog A V L} : a ∉ W →
      (∀ μ', Rch μ μ' → Avoid W Rch μ' (k (μ' a))) → Avoid W Rch μ (.rd a k)
  | rds {μ : A → V} {a : A} {k : V → Prog A V L} : a ∉ W →
      (∀ μ', Rch μ μ' → Avoid W Rch μ' (k (μ' a))) → Avoid W Rch μ (.rds a k)
  | rdc {μ : A → V} {a : A} {K : V → V → Prop} {k : V → Prog A V L} : a ∉ W →
      (∀ μ', Rch μ μ' → Avoid W Rch μ' (k (μ' a))) → Avoid W Rch μ (.rdc a K k)
  | wr {μ : A → V} {a : A} {v : V} {k : Prog A V L} : a ∉ W →
      (∀ μ', Rch μ μ' → Avoid W Rch (Function.update μ' a v) k) → Avoid W Rch μ (.wr a v k)
  | lock {μ : A → V} {l : L} {k : Bool → Prog A V L} : (∀ b, Avoid W Rch μ (k b)) → Avoid W Rch μ (.lock l k)
  | start {μ : A → V} {k : Prog A V L} : Avoid W Rch μ k → Avoid W Rch μ (.start k)

/-- `Avoid` over a smaller reachability. -/
theorem Avoid.mono {W : Set A} {Rch Rch' : (A → V) → (A → V) → Prop} (hR : ∀ μ μ', Rch' μ μ' → Rch μ μ')
    {μ : A → V} {p : Prog A V L} (h : Avoid W Rch μ p) : Avoid W Rch' μ p := by
  induction h with
  | done => exact .done
  | rd ha _ ih => exact .rd ha fun μ' h => ih μ' (hR _ _ h)
  | rds ha _ ih => exact .rds ha fun μ' h => ih μ' (hR _ _ h)
  | rdc ha _ ih => exact .rdc ha fun μ' h => ih μ' (hR _ _ h)
  | wr ha _ ih => exact .wr ha fun μ' h => ih μ' (hR _ _ h)
  | lock _ ih => exact .lock ih
  | start _ ih => exact .start ih

/-- **A tree-level footprint off `W` gives `Avoid`** at every memory and reachability. -/
theorem avoid_of_within {W : Set A} {Rch : (A → V) → (A → V) → Prop} {p : Prog A V L} (h : Within Wᶜ p) :
    ∀ μ, Avoid W Rch μ p := by
  induction h with
  | done => exact fun _ => .done
  | rd ha _ ih => exact fun _ => .rd ha fun μ' _ => ih _ μ'
  | wr ha _ ih => exact fun _ => .wr ha fun μ' _ => ih _
  | lock _ ih => exact fun μ => .lock fun b => ih b μ
  | rds ha _ ih => exact fun _ => .rds ha fun μ' _ => ih _ μ'
  | start _ ih => exact fun μ => .start (ih μ)
  | rdc ha _ ih => exact fun _ => .rdc ha fun μ' _ => ih _ μ'

/-! ## Simulations of the reachable memories -/

section xfer
variable {W : Set A} {own₁ own₂ : (A → V) → A → Owner C L} {cls : A → V → V} {ko : A → ClsOwner C}
  {c : C} {hs : L → Prop}

/-- A `Foreign` write off `W` at `own₂` is `Foreign` at `own₁` from a memory agreeing off `W`. -/
theorem foreign_xfer (X : OwnXfer W own₁ own₂) {μ₂ μ₁ : A → V} (hE : EqOff W μ₂ μ₁) {b : A} {v : V}
    (hb : b ∉ W) (hF : Foreign own₂ cls ko c hs μ₂ b v) : Foreign own₁ cls ko c hs μ₁ b v := by
  unfold Foreign at hF ⊢
  obtain ⟨h1, h2, h3⟩ := hF
  have hE' := hE.update b v
  refine ⟨?_, fun x hx => ?_, ?_⟩
  · rw [← X.own_eq hE hb]; exact h1
  · by_cases hxW : x ∈ W
    · exact absurd (X.keep₁ μ₁ b v x hb hxW) hx
    · rw [← X.own_eq hE hxW, ← X.own_eq hE' hxW] at hx ⊢
      exact h2 x hx
  · rw [← hE b hb]; exact h3

/-- **`FReach` at `own₂` is simulated, off `W`, by `FReach` at `own₁`.** -/
theorem freach_xfer (X : OwnXfer W own₁ own₂) {μ₂ μ₂' : A → V}
    (hR : FReach own₂ cls ko c hs μ₂ μ₂') :
    ∀ μ₁, EqOff W μ₂ μ₁ → ∃ μ₁', FReach own₁ cls ko c hs μ₁ μ₁' ∧ EqOff W μ₂' μ₁' := by
  induction hR with
  | refl μ => exact fun μ₁ h => ⟨μ₁, .refl _, h⟩
  | @step μ μ' b v hF _ ih =>
    intro μ₁ hE
    by_cases hb : b ∈ W
    · exact ih μ₁ (hE.update_in hb v)
    · obtain ⟨μ₁', h1, h2⟩ := ih (Function.update μ₁ b v) (hE.update b v)
      exact ⟨μ₁', .step (foreign_xfer X hE hb hF) h1, h2⟩

variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop}

/-- An `ADStep` off `W` at `own₂` is one at `own₁` from a memory agreeing off `W`. -/
theorem adStep_xfer (X : OwnXfer W own₁ own₂) {μ₂ μ₁ : A → V} (hE : EqOff W μ₂ μ₁) {b : A} {v : V}
    (hb : b ∉ W) (hA : ADStep G Q NP own₂ ko μ₂ b v) : ADStep G Q NP own₁ ko μ₁ b v := by
  unfold ADStep at hA ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hA
  refine ⟨h1, ?_, ?_, fun m => funext fun x => ?_, h5⟩
  · rw [← hE b hb]; exact h2
  · rw [← hE b hb]; exact h3
  · by_cases hxW : x ∈ W
    · exact X.keep₁ m b v x hb hxW
    · rw [← X.off _ x hxW, ← X.off _ x hxW]; exact congrFun (h4 m) x

/-- **`FReachA` at `own₂` is simulated, off `W`, by `FReachA` at `own₁`.** -/
theorem freachA_xfer (X : OwnXfer W own₁ own₂) {μ₂ μ₂' : A → V}
    (hR : FReachA G Q NP own₂ cls ko c hs μ₂ μ₂') :
    ∀ μ₁, EqOff W μ₂ μ₁ → ∃ μ₁', FReachA G Q NP own₁ cls ko c hs μ₁ μ₁' ∧ EqOff W μ₂' μ₁' := by
  induction hR with
  | refl μ => exact fun μ₁ h => ⟨μ₁, .refl _, h⟩
  | @step μ μ' b v hF _ ih =>
    intro μ₁ hE
    by_cases hb : b ∈ W
    · exact ih μ₁ (hE.update_in hb v)
    · obtain ⟨μ₁', h1, h2⟩ := ih (Function.update μ₁ b v) (hE.update b v)
      exact ⟨μ₁', .step (foreign_xfer X hE hb hF) h1, h2⟩
  | @ad μ μ' b v hA _ ih =>
    intro μ₁ hE
    by_cases hb : b ∈ W
    · exact ih μ₁ (hE.update_in hb v)
    · obtain ⟨μ₁', h1, h2⟩ := ih (Function.update μ₁ b v) (hE.update b v)
      exact ⟨μ₁', .ad (adStep_xfer X hE hb hA) h1, h2⟩

/-! ## The transfers -/

/-- **`Safe` moves from `own₁` to `own₂`** along a run avoiding `W` (module docstring). -/
theorem safe_xfer (X : OwnXfer W own₁ own₂) {μ₁ : A → V} {p : Prog A V L}
    (hS : Safe own₁ cls ko c hs μ₁ p) :
    ∀ μ₂, Avoid W (FReach own₁ cls ko c hs) μ₁ p → EqOff W μ₂ μ₁ → Safe own₂ cls ko c hs μ₂ p := by
  induction hS with
  | done => exact fun _ _ _ => .done
  | @rd μ a k hPO _ ih =>
    intro μ₂ hAv hE
    cases hAv with
    | rd ha hk =>
      refine .rd (fun μ₂' hR => ?_) (fun μ₂' hR => ?_)
      · obtain ⟨μ₁', h1, h2⟩ := freach_xfer X hR μ hE
        rw [X.own_eq h2 ha]; exact hPO μ₁' h1
      · obtain ⟨μ₁', h1, h2⟩ := freach_xfer X hR μ hE
        rw [h2 a ha]; exact ih μ₁' h1 μ₂' (hk μ₁' h1) h2
  | @rds μ a k _ ih =>
    intro μ₂ hAv hE
    cases hAv with
    | rds ha hk =>
      refine .rds (fun μ₂' hR => ?_)
      obtain ⟨μ₁', h1, h2⟩ := freach_xfer X hR μ hE
      rw [h2 a ha]; exact ih μ₁' h1 μ₂' (hk μ₁' h1) h2
  | @rdc μ a K k hko hK _ ih =>
    intro μ₂ hAv hE
    cases hAv with
    | rdc ha hk =>
      refine .rdc hko hK (fun μ₂' hR => ?_)
      obtain ⟨μ₁', h1, h2⟩ := freach_xfer X hR μ hE
      rw [h2 a ha]; exact ih μ₁' h1 μ₂' (hk μ₁' h1) h2
  | @wr μ a v k hH hM hC _ ih =>
    intro μ₂ hAv hE
    cases hAv with
    | wr ha hk =>
      refine .wr (fun μ₂' hR => ?_) (fun μ₂' hR => ?_) (fun μ₂' hR => ?_) (fun μ₂' hR => ?_)
      · obtain ⟨μ₁', h1, h2⟩ := freach_xfer X hR μ hE
        rw [X.own_eq h2 ha]; exact hH μ₁' h1
      · obtain ⟨μ₁', h1, h2⟩ := freach_xfer X hR μ hE
        unfold MoveV
        intro x hx
        by_cases hxW : x ∈ W
        · exact absurd (X.keep₂ μ₂' a v x ha hxW) hx
        · have h2' := h2.update a v
          rw [X.own_eq h2 hxW, X.own_eq h2' hxW] at hx ⊢
          exact hM μ₁' h1 x hx
      · obtain ⟨μ₁', h1, h2⟩ := freach_xfer X hR μ hE
        rw [h2 a ha]; exact hC μ₁' h1
      · obtain ⟨μ₁', h1, h2⟩ := freach_xfer X hR μ hE
        exact ih μ₁' h1 _ (hk μ₁' h1) (h2.update a v)

/-- **`InsA` moves from `own₁` to `own₂`** along a run avoiding `W` (module docstring). -/
theorem insA_xfer (X : OwnXfer W own₁ own₂) {μ₁ : A → V} {p : Prog A V L}
    (hI : InsA G Q NP own₁ cls ko c hs μ₁ p) :
    ∀ μ₂, Avoid W (FReachA G Q NP own₁ cls ko c hs) μ₁ p → EqOff W μ₂ μ₁ →
      InsA G Q NP own₂ cls ko c hs μ₂ p := by
  induction hI with
  | done => exact fun _ _ _ => .done
  | @rd μ a k hq _ ih =>
    intro μ₂ hAv hE
    cases hAv with
    | rd ha hk =>
      refine .rd (fun hg μ₂' hR => ?_) (fun μ₂' hR => ?_)
      · obtain ⟨μ₁', h1, h2⟩ := freachA_xfer X hR μ hE
        rw [h2 a ha]; exact hq hg μ₁' h1
      · obtain ⟨μ₁', h1, h2⟩ := freachA_xfer X hR μ hE
        rw [h2 a ha]; exact ih μ₁' h1 μ₂' (hk μ₁' h1) h2
  | @rds μ a k hq _ ih =>
    intro μ₂ hAv hE
    cases hAv with
    | rds ha hk =>
      refine .rds (fun hg μ₂' hR => ?_) (fun μ₂' hR => ?_)
      · obtain ⟨μ₁', h1, h2⟩ := freachA_xfer X hR μ hE
        rw [h2 a ha]; exact hq hg μ₁' h1
      · obtain ⟨μ₁', h1, h2⟩ := freachA_xfer X hR μ hE
        rw [h2 a ha]; exact ih μ₁' h1 μ₂' (hk μ₁' h1) h2
  | @rdc μ a K k hq _ ih =>
    intro μ₂ hAv hE
    cases hAv with
    | rdc ha hk =>
      refine .rdc (fun hg μ₂' hR => ?_) (fun μ₂' hR => ?_)
      · obtain ⟨μ₁', h1, h2⟩ := freachA_xfer X hR μ hE
        rw [h2 a ha]; exact hq hg μ₁' h1
      · obtain ⟨μ₁', h1, h2⟩ := freachA_xfer X hR μ hE
        rw [h2 a ha]; exact ih μ₁' h1 μ₂' (hk μ₁' h1) h2
  | @wr μ a v k hnp _ ih =>
    intro μ₂ hAv hE
    cases hAv with
    | wr ha hk =>
      refine .wr hnp (fun μ₂' hR => ?_)
      obtain ⟨μ₁', h1, h2⟩ := freachA_xfer X hR μ hE
      exact ih μ₁' h1 _ (hk μ₁' h1) (h2.update a v)

/-- **`InsAP` moves from `own₁` to `own₂`** along a run avoiding `W`, for every done set (module docstring). -/
theorem insAP_xfer (X : OwnXfer W own₁ own₂) {D : Set A} {μ₁ : A → V} {p : Prog A V L}
    (hI : InsAP G Q NP own₁ cls ko c hs D μ₁ p) :
    ∀ μ₂, Avoid W (FReachA G Q NP own₁ cls ko c hs) μ₁ p → EqOff W μ₂ μ₁ →
      InsAP G Q NP own₂ cls ko c hs D μ₂ p := by
  induction hI with
  | done => exact fun _ _ _ => .done
  | @rd D μ a k hq _ ih =>
    intro μ₂ hAv hE
    cases hAv with
    | rd ha hk =>
      refine .rd (fun hg μ₂' hR => ?_) (fun μ₂' hR => ?_)
      · obtain ⟨μ₁', h1, h2⟩ := freachA_xfer X hR μ hE
        rw [h2 a ha]; exact hq hg μ₁' h1
      · obtain ⟨μ₁', h1, h2⟩ := freachA_xfer X hR μ hE
        rw [h2 a ha]; exact ih μ₁' h1 μ₂' (hk μ₁' h1) h2
  | @rds D μ a k hq _ ih =>
    intro μ₂ hAv hE
    cases hAv with
    | rds ha hk =>
      refine .rds (fun hg μ₂' hR => ?_) (fun μ₂' hR => ?_)
      · obtain ⟨μ₁', h1, h2⟩ := freachA_xfer X hR μ hE
        rw [h2 a ha]; exact hq hg μ₁' h1
      · obtain ⟨μ₁', h1, h2⟩ := freachA_xfer X hR μ hE
        rw [h2 a ha]; exact ih μ₁' h1 μ₂' (hk μ₁' h1) h2
  | @rdc D μ a K k hq _ ih =>
    intro μ₂ hAv hE
    cases hAv with
    | rdc ha hk =>
      refine .rdc (fun hg μ₂' hR => ?_) (fun μ₂' hR => ?_)
      · obtain ⟨μ₁', h1, h2⟩ := freachA_xfer X hR μ hE
        rw [h2 a ha]; exact hq hg μ₁' h1
      · obtain ⟨μ₁', h1, h2⟩ := freachA_xfer X hR μ hE
        rw [h2 a ha]; exact ih μ₁' h1 μ₂' (hk μ₁' h1) h2
  | @wr D μ a v k hD hf _ ih =>
    intro μ₂ hAv hE
    cases hAv with
    | wr ha hk =>
      refine .wr hD hf (fun μ₂' hR => ?_)
      obtain ⟨μ₁', h1, h2⟩ := freachA_xfer X hR μ hE
      exact ih μ₁' h1 _ (hk μ₁' h1) (h2.update a v)

/-- **`Safe ∧ InsAP` together** from one `Avoid` over `FReachA` at `own₁` (module docstring). -/
theorem safe_insAP_xfer (X : OwnXfer W own₁ own₂) {D : Set A} {μ₁ μ₂ : A → V} {p : Prog A V L}
    (h : Safe own₁ cls ko c hs μ₁ p ∧ InsAP G Q NP own₁ cls ko c hs D μ₁ p)
    (hAv : Avoid W (FReachA G Q NP own₁ cls ko c hs) μ₁ p) (hE : EqOff W μ₂ μ₁) :
    Safe own₂ cls ko c hs μ₂ p ∧ InsAP G Q NP own₂ cls ko c hs D μ₂ p :=
  ⟨safe_xfer X h.1 μ₂ (hAv.mono fun _ _ hR => FReachA.of_freach hR) hE, insAP_xfer X h.2 μ₂ hAv hE⟩

end xfer

end
end Fl4Proofs.P2.Serial
