/-
# P2 (line mmuAD, gen 2): A/D insensitivity at the program-tree level — FL4 instance of `Serial.SerialAD`

`P2/SerialAD.lean` serializes environment writes `x := y` (`ADWr`) that hit words local paths may read, given that
every started body is `ADIns G Q NP`. This module instantiates it for the page walker and lifts insensitivity
from the trait-call trees (`PathObl.SProg`, which `IsProgOn` ties to the extracted functions) through the
translation `E2E.tr` that builds every local body:

* `NotPresent v` := `v &&& 1 = 0` (P clear). `adEq_equiv`: `ADEq` is an equivalence.
* **`MmuAD.adWr`**: an `MmuAD` [P] write (present word, A/D ORed in) whose word moves no owner and has an untracked
  class is an `ADWr PW ADEq NotPresent` — the walker never writes a non-present entry.
* **`SADIns G Q NP p`**: the tree-level predicate: at each `rd` / `rdp` of a `G` word the continuation is equal for
  `Q`-equivalent values; each kernel store into a `G` word stores an `NP` value. Stores into user words, `zero`,
  `clr` and the Arch / `ksb` / `cpu` / `masks` nodes carry no condition beyond their continuations.
* **`tr_adIns`**: `SADIns p` gives `ADIns` of the translated body `tr R User cls ko c kb mk ar p Wd a` for every
  read set `R`, write set `Wd` and Arch state `a` (the translation chooses `rd` / `rdc` / `rds` by the address
  only, never by the value, and keeps the continuation). So for a `LocalPath` `P`, `SADIns P.p` gives `ADIns` of
  every body it starts (`LocalPath.body`), whatever the start state: **the per-path obligation reduces to one
  fact about the path's explicit tree.**
* `sadIns_rd_mask`: the shape every walk read has: a continuation that uses the value only through masks with bits
  5, 6 clear (`MmuADWalk.kP`…`kXD`) is `ADEq`-insensitive.

No premise beyond `MmuAD` [P] (P2/MmuADWalk.lean); no existing statement or file changed.
-/
import Fl4Proofs.P2.E2E
import Fl4Proofs.P2.SerialAD
import Fl4Proofs.P2.MmuADWalk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.MmuAD
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Prog ADIns ADWr Cfg Owner ClsOwner)
open Fl4Proofs.P2.E2E (SP tr rdN)

noncomputable section
open Classical

/-! ## The instance -/

/-- P clear: the walker never writes such an entry (SDM §4.8, `MmuAD.present`). -/
def NotPresent (v : U64) : Prop := v &&& 1#u64 = 0#u64

theorem adEq_equiv : Equivalence ADEq := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- **An `MmuAD` write is an `ADWr`** when the word moves no owner and has an untracked class. -/
theorem MmuAD.adWr {PW : U64 → Prop} {s : Cfg U64 U64 U64 U64} {a x : U64} (h : MmuAD PW s.mem a x)
    (hkeep : ∀ m, s.own (Function.update m a x) = s.own m) (hko : s.ko a = .free) :
    ADWr PW ADEq NotPresent s a x where
  g := h.pw
  np := h.present
  q := adEq_symm (adOr_adEq h.ad)
  keep := hkeep
  ko := hko

/-! ## Trees -/

/-- **A trait-call tree insensitive to `Q`-changes of the `G` words**, storing only `NP` values into kernel
`G` words. -/
inductive SADIns (G : U64 → Prop) (Q : U64 → U64 → Prop) (NP : U64 → Prop) (User : U64 → Prop) {X : Type} :
    SProg X → Prop
  | ret (x : X) : SADIns G Q NP User (.ret x)
  | err (e : Error) : SADIns G Q NP User (.err e)
  | rd {q : U64} {k : U64 → SProg X} : (G q → ∀ u w, Q u w → k u = k w) → (∀ v, SADIns G Q NP User (k v)) →
      SADIns G Q NP User (.rd q k)
  | rdp {q : U64} {k : U64 × U64 → SProg X} :
      (G q → ∀ u u' w, Q u u' → k (u, w) = k (u', w)) →
      (G (core.num.U64.wrapping_add q 8#u64) → ∀ u w w', Q w w' → k (u, w) = k (u, w')) →
      (∀ v, SADIns G Q NP User (k v)) → SADIns G Q NP User (.rdp q k)
  | wr {q v : U64} {k : SProg X} : (¬ User q → G q → NP v) → SADIns G Q NP User k →
      SADIns G Q NP User (.wr q v k)
  | zero (a n : U64) (k : SProg X) : SADIns G Q NP User (.zero a n k)
  | clr (a n : U64) (k : SProg X) : SADIns G Q NP User (.clr a n k)
  | ksb {k : U64 → SProg X} : (∀ v, SADIns G Q NP User (k v)) → SADIns G Q NP User (.ksb k)
  | cpu {k : U64 → SProg X} : (∀ v, SADIns G Q NP User (k v)) → SADIns G Q NP User (.cpu k)
  | masks {k : U64 × U64 → SProg X} : (∀ v, SADIns G Q NP User (k v)) → SADIns G Q NP User (.masks k)
  | arch {op : ArchCall} {k : AV → SProg X} : (∀ v, SADIns G Q NP User (k v)) →
      SADIns G Q NP User (.arch op k)

section tr
variable {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop}
variable (R User : U64 → Prop) (cls : U64 → U64 → U64) (ko : U64 → ClsOwner U64) (c : U64)

/-- The translated read keeps insensitivity: its kind depends on the address only. -/
theorem adIns_rdN (Wd : Set U64) {q : U64} {k : U64 → SP} (h1 : G q → ∀ u w, Q u w → k u = k w)
    (h2 : ∀ v, ADIns G Q NP (k v)) : ADIns G Q NP (rdN R User cls ko c Wd q k) := by
  unfold rdN
  by_cases ha : ¬ E2E.Racy R User Wd q
  · rw [if_pos ha]; exact .rd h1 h2
  · rw [if_neg ha]
    by_cases hb : ¬ User q ∧ (ko q = .gate ∨ ko q = .core c)
    · rw [if_pos hb]; exact .rdc h1 h2
    · rw [if_neg hb]; exact .rds h1 h2

variable (kb : U64) (mk : U64 × U64) {A X : Type} (ar : machine.Arch A)

/-- **The translation keeps insensitivity** (module docstring). -/
theorem tr_adIns {p : SProg X} (h : SADIns G Q NP User p) :
    ∀ (Wd : Set U64) (a : A), ADIns G Q NP (tr R User cls ko c kb mk ar p Wd a) := by
  induction h with
  | ret x => intro Wd a; simp only [tr]; exact .done
  | err e => intro Wd a; simp only [tr]; exact .done
  | @rd q k h1 _ ih =>
    intro Wd a; simp only [tr]
    exact adIns_rdN R User cls ko c Wd (fun hg u w hq => by rw [h1 hg u w hq]) (fun v => ih v Wd a)
  | @rdp q k h1 h1' _ ih =>
    intro Wd a; simp only [tr]
    refine adIns_rdN R User cls ko c Wd (fun hg u u' hq => ?_) (fun v => ?_)
    · have e : (fun w => tr R User cls ko c kb mk ar (k (u, w)) Wd a) =
          (fun w => tr R User cls ko c kb mk ar (k (u', w)) Wd a) :=
        funext fun w => by rw [h1 hg u u' w hq]
      beta_reduce
      rw [e]
    · exact adIns_rdN R User cls ko c Wd (fun hg w w' hq => by beta_reduce; rw [h1' hg v w w' hq])
        (fun w => ih (v, w) Wd a)
  | @wr q v k h1 _ ih =>
    intro Wd a; simp only [tr]
    by_cases hu : User q
    · rw [if_pos hu]; exact ih Wd a
    · rw [if_neg hu]; exact .wr (h1 hu) (ih _ a)
  | zero => intro Wd a; simp only [tr]; exact .done
  | clr => intro Wd a; simp only [tr]; exact .done
  | ksb _ ih => intro Wd a; simp only [tr]; exact ih _ Wd a
  | cpu _ ih => intro Wd a; simp only [tr]; exact ih _ Wd a
  | masks _ ih => intro Wd a; simp only [tr]; exact ih _ Wd a
  | @arch op k _ ih =>
    intro Wd a; simp only [tr]
    by_cases hx : ∃ r, callArch ar op a = ok r
    · rw [dif_pos hx]; exact ih _ Wd _
    · rw [dif_neg hx]; exact .done

end tr

/-- **Every body a local path starts is insensitive** when its explicit tree is. -/
theorem body_adIns {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop}
    {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64}
    {User : U64 → Prop} (P : E2E.LocalPath own cls ko User) (h : SADIns G Q NP User P.p) (σ : P.S) (a : P.A) :
    ADIns G Q NP (P.body σ a) := by
  unfold E2E.LocalPath.body
  exact tr_adIns _ User cls ko _ _ _ P.ar h ∅ a

/-- The shape of every walk read (module docstring): a continuation using the value only through three masks
with bits 5, 6 clear is `ADEq`-insensitive. -/
theorem sadIns_rd_mask {X : Type} {k : U64 → SProg X} {f : U64 → U64 → U64 → SProg X} {m1 m2 m3 : U64}
    (h1 : m1 &&& adBits = 0#u64) (h2 : m2 &&& adBits = 0#u64) (h3 : m3 &&& adBits = 0#u64)
    (hk : ∀ v, k v = f (v &&& m1) (v &&& m2) (v &&& m3)) : ∀ u w, ADEq u w → k u = k w := by
  intro u w h
  rw [hk u, hk w, and_eq_of_adEq h h1, and_eq_of_adEq h h2, and_eq_of_adEq h h3]

end

end Fl4Proofs.P2.MmuAD
