/-
# P2 (line p3mc, gen 7): re-annotating a body with a smaller read set (`narrowSP`)

A body's annotation (`rd` / `rds` / `rdc`) is ghost: the three read nodes step alike (`Serial.Step`), and only
`Safe` distinguishes them (`rd` asks the word to be readable, `rdc` asks its class owner to be the gate or the core,
`rds` asks nothing). `narrowSP cls ko c Q Wd q` re-annotates `q` for the smaller read set `Q`:
* a plain read of a word outside `Q` and not written before (`Wd`, kept along the kernel writes) becomes a class read
  where the class owner is the gate or `c`, and a speculative read otherwise (the rule of `E2E.rdN`);
* a class read whose class owner is neither becomes a speculative read;
* everything else is kept.

* **`safe_narrow`**: re-annotating never breaks `Safe` (each change only drops a condition);
* `narrow_rd_rds`, `safe_rds_iff`: at a word outside `Q` with a class owner other than the gate and `c`, the
  re-annotated read is speculative, and `Safe` there asks only that the rest be `Safe` (no readability).

No premise.
-/
import Fl4Proofs.P2.SerialSafe

namespace Fl4Proofs.P2.Serial

noncomputable section
open Classical

variable {A V C L : Type} [DecidableEq A] [DecidableEq C] [DecidableEq L]

/-- **The body re-annotated for the read set `Q`** (module docstring). -/
def narrowSP (cls : A → V → V) (ko : A → ClsOwner C) (c : C) (Q : A → Prop) :
    Set A → Prog A V L → Prog A V L
  | _, .done => .done
  | Wd, .rd a k =>
    if Q a ∨ a ∈ Wd then .rd a (fun v => narrowSP cls ko c Q Wd (k v))
    else if ko a = .gate ∨ ko a = .core c then
      .rdc a (fun u w => cls a u = cls a w) (fun v => narrowSP cls ko c Q Wd (k v))
    else .rds a (fun v => narrowSP cls ko c Q Wd (k v))
  | Wd, .rds a k => .rds a (fun v => narrowSP cls ko c Q Wd (k v))
  | Wd, .rdc a K k =>
    if ko a = .gate ∨ ko a = .core c then .rdc a K (fun v => narrowSP cls ko c Q Wd (k v))
    else .rds a (fun v => narrowSP cls ko c Q Wd (k v))
  | Wd, .wr a v k => .wr a v (narrowSP cls ko c Q (insert a Wd) k)
  | Wd, .lock l k => .lock l (fun b => narrowSP cls ko c Q Wd (k b))
  | Wd, .start k => .start (narrowSP cls ko c Q Wd k)

variable {own : (A → V) → A → Owner C L} {cls : A → V → V} {ko : A → ClsOwner C} {c : C} {hs : L → Prop}

/-- **Re-annotating keeps `Safe`** (module docstring). -/
theorem safe_narrow (Q : A → Prop) {μ : A → V} {q : Prog A V L} (h : Safe own cls ko c hs μ q) :
    ∀ Wd, Safe own cls ko c hs μ (narrowSP cls ko c Q Wd q) := by
  induction h with
  | done => intro Wd; simp only [narrowSP]; exact .done
  | @rd μ a k hp _ ih =>
    intro Wd
    simp only [narrowSP]
    split_ifs with h1 h2
    · exact .rd hp (fun μ' hR => ih μ' hR Wd)
    · exact .rdc h2 (fun u w h => h) (fun μ' hR => ih μ' hR Wd)
    · exact .rds (fun μ' hR => ih μ' hR Wd)
  | @rds μ a k _ ih =>
    intro Wd
    simp only [narrowSP]
    exact .rds (fun μ' hR => ih μ' hR Wd)
  | @rdc μ a K k hko hK _ ih =>
    intro Wd
    simp only [narrowSP]
    rw [if_pos hko]
    exact .rdc hko hK (fun μ' hR => ih μ' hR Wd)
  | @wr μ a v k h1 h2 h3 _ ih =>
    intro Wd
    simp only [narrowSP]
    exact .wr h1 h2 h3 (fun μ' hR => ih μ' hR (insert a Wd))

/-- At a word outside `Q`, not written before, whose class owner is neither the gate nor `c`, the re-annotated
read is speculative. -/
theorem narrow_rd_rds {Q : A → Prop} {Wd : Set A} {a : A} {k : V → Prog A V L} (hQ : ¬ Q a) (hW : a ∉ Wd)
    (hko : ¬ (ko a = .gate ∨ ko a = .core c)) :
    narrowSP cls ko c Q Wd (.rd a k) = .rds a (fun v => narrowSP cls ko c Q Wd (k v)) := by
  simp only [narrowSP]
  rw [if_neg (fun h => h.elim hQ hW), if_neg hko]

/-- `Safe` at a speculative read asks only that the rest be `Safe` (no readability of the word). -/
theorem safe_rds_iff {μ : A → V} {a : A} {k : V → Prog A V L} :
    Safe own cls ko c hs μ (.rds a k) ↔ ∀ μ', FReach own cls ko c hs μ μ' → Safe own cls ko c hs μ' (k (μ' a)) := by
  constructor
  · intro h
    cases h with
    | rds h1 => exact h1
  · exact fun h => .rds h

end
end Fl4Proofs.P2.Serial
