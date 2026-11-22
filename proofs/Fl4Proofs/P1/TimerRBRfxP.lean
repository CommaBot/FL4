/-
P1 (jc6d, TIMER-RB-PLAN stage 7, pure part): the `remove_fixup` invariant (CLRS 13.4, "doubly black at
`x`") on the zipper.  The loop state is in one of two modes:
- `RfA W x p f`: `W = ctx.plug tx`, `x = tx.rootKey` (`0` for a leaf), `p = ctx.par`; the path is
  red-black for a hole of black height `n + 1` (`CtxOK ctx (n + 1)`) while `tx` has black height `n`
  (`DB tx n`: black/leaf and balanced, or red with balanced children of black height `n`, possibly under a
  red parent); the root is black unless the hole is the root; and either `tx` is red (the loop stops at
  the next guard without spending fuel) or the path length is at most the fuel;
- `RfB W x`: `W` is red-black with a black root and `x` is its root (after a rotation case).
`DB`/`CtxOK` force the sibling of a doubly-black hole to have black height `≥ 1`, so it is never null:
this is why `x == left(p)` picks the right side even when `x = 0`.
Pure case lemmas: `rf_case2L/R` (sibling and its children black: recolour, `x` moves up),
`rf_case4L/R` (far nephew red: recolour + rotation ends balanced), `rfA_top`, `rfR_fin` (exits),
`UpOK` (what the path above the parent provides), `rf_init` (the state `remove` hands to the fixup,
from `DelShape`; path length `≤ 128` by the height bound).
-/
import Fl4Proofs.P1.TimerRBDelC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

namespace TRB

namespace Ctx

/-- The path length (number of path nodes above the hole). -/
def depth : Ctx → Nat
  | top => 0
  | lc _ _ _ up => up.depth + 1
  | rc _ _ _ up => up.depth + 1

theorem depth_le : ∀ (ctx : Ctx) (t : RBT), ctx.depth + t.height ≤ (ctx.plug t).height
  | top, t => by simp [depth, plug]
  | lc c k r up, t => by
    have h1 := depth_le up (.node c t k r)
    have h2 : t.height + 1 ≤ (RBT.node c t k r).height := Nat.succ_le_succ (le_max_left _ _)
    show up.depth + 1 + t.height ≤ (up.plug (.node c t k r)).height
    omega
  | rc c l k up, t => by
    have h1 := depth_le up (.node c l k t)
    have h2 : t.height + 1 ≤ (RBT.node c l k t).height := Nat.succ_le_succ (le_max_right _ _)
    show up.depth + 1 + t.height ≤ (up.plug (.node c l k t)).height
    omega

theorem depth_app : ∀ (i o : Ctx), (app i o).depth = i.depth + o.depth
  | top, o => by simp [app, depth]
  | lc c k r up, o => by
    show (app up o).depth + 1 = up.depth + 1 + o.depth
    rw [depth_app up o]; omega
  | rc c l k up, o => by
    show (app up o).depth + 1 = up.depth + 1 + o.depth
    rw [depth_app up o]; omega

/-- Away from the top, the whole tree's root is a path key. -/
theorem plug_root_mem : ∀ (ctx : Ctx), ctx ≠ top → ∀ t : RBT, (ctx.plug t).rootKey ∈ ctx.pre ++ ctx.post
  | top, h, _ => absurd rfl h
  | lc c k r up, _, t => by
    by_cases hu : up = top
    · subst hu; simp [plug, pre, post, RBT.rootKey]
    · have := plug_root_mem up hu (.node c t k r)
      show (up.plug (.node c t k r)).rootKey ∈ up.pre ++ (k :: (r.keys ++ up.post))
      simp only [List.mem_append, List.mem_cons] at this ⊢; tauto
  | rc c l k up, _, t => by
    by_cases hu : up = top
    · subst hu; simp [plug, pre, post, RBT.rootKey]
    · have := plug_root_mem up hu (.node c l k t)
      show (up.plug (.node c l k t)).rootKey ∈ up.pre ++ l.keys ++ [k] ++ up.post
      simp only [List.mem_append, List.mem_cons] at this ⊢; tauto

end Ctx

/-- Away from the top, the subtree's root word is not the whole tree's root word. -/
theorem x_ne_root {k : Links} {R : U64} {ctx : Ctx} {tx : RBT} (h : Rep k 0#u64 R (ctx.plug tx))
    (hd : (ctx.plug tx).keys.Nodup) (hc : ctx ≠ .top) : tx.rootKey ≠ R := by
  have hr := h.root
  have hm := Ctx.plug_root_mem ctx hc tx
  rw [← hr] at hm
  have hd' := hd
  rw [Ctx.plug_keys] at hd'
  intro e
  rcases tx.rootKey_mem with e0 | hx
  · have hRk : R ∈ (ctx.plug tx).keys := by
      rw [Ctx.plug_keys]; simp only [List.mem_append] at hm ⊢; tauto
    exact h.keys_ne0 R hRk (e ▸ e0)
  · exact nd_mid hd' hx hm e

/-- A colour-only fact: the root colour does not depend on a path node's key. -/
theorem plug_isRed_key (ctx : Ctx) (c : Bool) (a b : RBT) (t y : U64) :
    (ctx.plug (.node c a t b)).isRed = (ctx.plug (.node c a y b)).isRed := by
  by_cases h : ctx = .top
  · subst h; rfl
  · exact Ctx.plug_isRed ctx h _ _

/-- The subtree at a doubly-black hole: black (or a leaf) of black height `n`, or red with children of black
height `n` (blackening it then fills the hole). -/
def DB (t : RBT) (n : Nat) : Prop :=
  (t.isRed = false ∧ Bal t n) ∨ ∃ l k r, t = .node true l k r ∧ Bal l n ∧ Bal r n

theorem DB.of_bal {t : RBT} {n : Nat} (h : Bal t n) : DB t n := by
  cases h with
  | leaf => exact Or.inl ⟨rfl, .leaf⟩
  | red hl hr _ _ => exact Or.inr ⟨_, _, _, rfl, hl, hr⟩
  | black hl hr => exact Or.inl ⟨rfl, .black hl hr⟩

/-- Mode A: `x` doubly black at the hole `ctx` (see the module doc). -/
def RfA (W : RBT) (x p : U64) (f : Nat) : Prop :=
  ∃ (ctx : Ctx) (tx : RBT) (n : Nat), W = ctx.plug tx ∧ x = tx.rootKey ∧ p = ctx.par ∧ CtxOK ctx (n + 1) ∧
    DB tx n ∧ RootB ctx ∧ (tx.isRed = true ∨ ctx.depth ≤ f)

/-- Mode B (and exit): red-black with black root, `x` the root. -/
def RfB (W : RBT) (x : U64) : Prop := x = W.rootKey ∧ ∃ m, Bal W m ∧ W.isRed = false

/-- Exit on a red `x`: blackening `x` gives a red-black tree. -/
def RfR (W : RBT) (x : U64) : Prop :=
  ∃ (ctx : Ctx) (l r : RBT) (n : Nat), W = ctx.plug (.node true l x r) ∧ Bal l n ∧ Bal r n ∧
    CtxOK ctx (n + 1) ∧ RootB ctx

/-- The path above the parent `p` of the hole, for a parent colour `cp` and hole black height `n + 1`. -/
def UpC : Ctx → Bool → Nat → Prop
  | up, true, n => up.parRed = false ∧ CtxOK up (n + 1)
  | up, false, n => CtxOK up (n + 1 + 1)

def UpOK (up : Ctx) (cp : Bool) (n : Nat) : Prop := RootB up ∧ (up = .top → cp = false) ∧ UpC up cp n

theorem UpOK.of_lc {up : Ctx} {cp : Bool} {pk : U64} {S : RBT} {n : Nat} (h : CtxOK (.lc cp pk S up) (n + 1))
    (hR : RootB (.lc cp pk S up)) : UpOK up cp n ∧ Bal S (n + 1) ∧ (cp = true → S.isRed = false) := by
  cases h with
  | lcR hS hSb hp hu => exact ⟨⟨hR.lc_up, fun e => absurd e hR.lc_red, hp, hu⟩, hS, fun _ => hSb⟩
  | lcB hS hu => exact ⟨⟨hR.lc_up, fun _ => rfl, hu⟩, hS, fun e => by cases e⟩

theorem UpOK.of_rc {up : Ctx} {cp : Bool} {pk : U64} {S : RBT} {n : Nat} (h : CtxOK (.rc cp S pk up) (n + 1))
    (hR : RootB (.rc cp S pk up)) : UpOK up cp n ∧ Bal S (n + 1) ∧ (cp = true → S.isRed = false) := by
  cases h with
  | rcR hS hSb hp hu => exact ⟨⟨hR.rc_up, fun e => absurd e hR.rc_red, hp, hu⟩, hS, fun _ => hSb⟩
  | rcB hS hu => exact ⟨⟨hR.rc_up, fun _ => rfl, hu⟩, hS, fun e => by cases e⟩

/-- After the red-sibling rotation (case 1, `x` on the left): `p` is red under the old sibling `w`. -/
theorem UpOK.pushL {up : Ctx} {w : U64} {wr : RBT} {n : Nat} (h : UpOK up false n) (hwr : Bal wr (n + 1)) :
    UpOK (.lc false w wr up) true n :=
by
  refine ⟨RootB.lc_black h.1, (fun e => nomatch e), ?_⟩
  show (Ctx.lc false w wr up).parRed = false ∧ CtxOK (.lc false w wr up) (n + 1)
  exact ⟨rfl, CtxOK.lcB hwr h.2.2⟩

theorem UpOK.pushR {up : Ctx} {w : U64} {wl : RBT} {n : Nat} (h : UpOK up false n) (hwl : Bal wl (n + 1)) :
    UpOK (.rc false wl w up) true n :=
by
  refine ⟨RootB.rc_black h.1, (fun e => nomatch e), ?_⟩
  show (Ctx.rc false wl w up).parRed = false ∧ CtxOK (.rc false wl w up) (n + 1)
  exact ⟨rfl, CtxOK.rcB hwl h.2.2⟩

/-- Case 2, `x` on the left: the sibling `w` turns red, `x` moves up to `p`. -/
theorem rf_case2L {up : Ctx} {cp : Bool} {tx wl wr : RBT} {pk w : U64} {n f : Nat} (htx : Bal tx n)
    (hwl : Bal wl n) (hwr : Bal wr n) (bl : wl.isRed = false) (br : wr.isRed = false) (hU : UpOK up cp n)
    (hf : cp = true ∨ up.depth ≤ f) : RfA (up.plug (.node cp tx pk (.node true wl w wr))) pk up.par f := by
  obtain ⟨hR, -, hC⟩ := hU
  cases cp with
  | false =>
    exact ⟨up, _, n + 1, rfl, rfl, rfl, hC, Or.inl ⟨rfl, .black htx (.red hwl hwr bl br)⟩, hR,
      Or.inr (hf.resolve_left (by simp))⟩
  | true => exact ⟨up, _, n, rfl, rfl, rfl, hC.2, Or.inr ⟨_, _, _, rfl, htx, .red hwl hwr bl br⟩, hR, Or.inl rfl⟩

theorem rf_case2R {up : Ctx} {cp : Bool} {tx wl wr : RBT} {pk w : U64} {n f : Nat} (htx : Bal tx n)
    (hwl : Bal wl n) (hwr : Bal wr n) (bl : wl.isRed = false) (br : wr.isRed = false) (hU : UpOK up cp n)
    (hf : cp = true ∨ up.depth ≤ f) : RfA (up.plug (.node cp (.node true wl w wr) pk tx)) pk up.par f := by
  obtain ⟨hR, -, hC⟩ := hU
  cases cp with
  | false =>
    exact ⟨up, _, n + 1, rfl, rfl, rfl, hC, Or.inl ⟨rfl, .black (.red hwl hwr bl br) htx⟩, hR,
      Or.inr (hf.resolve_left (by simp))⟩
  | true => exact ⟨up, _, n, rfl, rfl, rfl, hC.2, Or.inr ⟨_, _, _, rfl, .red hwl hwr bl br, htx⟩, hR, Or.inl rfl⟩

/-- A node of colour `cp` with two black children of black height `n + 1` at the parent's place. -/
theorem rf_top {up : Ctx} {cp : Bool} {L R : RBT} {w : U64} {n : Nat} (hL : Bal L (n + 1)) (hR : Bal R (n + 1))
    (bL : L.isRed = false) (bR : R.isRed = false) (hU : UpOK up cp n) :
    ∃ m, Bal (up.plug (.node cp L w R)) m ∧ (up.plug (.node cp L w R)).isRed = false := by
  obtain ⟨hRB, htop, hC⟩ := hU
  cases cp with
  | false =>
    refine ⟨_, plug_bal hC (.black hL hR) (fun e => by simp [RBT.isRed] at e), ?_⟩
    by_cases hu : up = .top
    · subst hu; rfl
    · exact hRB.isRed hu _
  | true =>
    refine ⟨_, plug_bal hC.2 (.red hL hR bL bR) (fun _ => hC.1), ?_⟩
    by_cases hu : up = .top
    · exact absurd (htop hu) (by simp)
    · exact hRB.isRed hu _

/-- Case 4, `x` on the left (far nephew red): recolour and `rotate_left(p)` end balanced. -/
theorem rf_case4L {up : Ctx} {cp : Bool} {tx wl c1 d1 : RBT} {pk w k : U64} {n : Nat} (htx : Bal tx n)
    (hwl : Bal wl n) (hc1 : Bal c1 n) (hd1 : Bal d1 n) (hU : UpOK up cp n) :
    ∃ m, Bal (up.plug (.node cp (.node false tx pk wl) w (.node false c1 k d1))) m ∧
      (up.plug (.node cp (.node false tx pk wl) w (.node false c1 k d1))).isRed = false :=
  rf_top (.black htx hwl) (.black hc1 hd1) rfl rfl hU

theorem rf_case4R {up : Ctx} {cp : Bool} {tx wr c1 d1 : RBT} {pk w k : U64} {n : Nat} (htx : Bal tx n)
    (hwr : Bal wr n) (hc1 : Bal c1 n) (hd1 : Bal d1 n) (hU : UpOK up cp n) :
    ∃ m, Bal (up.plug (.node cp (.node false c1 k d1) w (.node false wr pk tx))) m ∧
      (up.plug (.node cp (.node false c1 k d1) w (.node false wr pk tx))).isRed = false :=
  rf_top (.black hc1 hd1) (.black hwr htx) rfl rfl hU

/-- Exit at the root in mode A. -/
theorem rfA_top {tx : RBT} {x : U64} {n : Nat} (hdb : DB tx n) (hx : x = tx.rootKey) : RfB tx x ∨ RfR tx x := by
  subst hx
  rcases hdb with ⟨hb, hB⟩ | ⟨l, k, r, rfl, hl, hr⟩
  · exact Or.inl ⟨rfl, n, hB, hb⟩
  · exact Or.inr ⟨.top, l, r, n, rfl, hl, hr, .top _, Or.inl rfl⟩

/-- Exit on a red `x`: blackening it gives a red-black tree with black root. -/
theorem rfR_fin {ctx : Ctx} {l r : RBT} {x : U64} {n : Nat} (hl : Bal l n) (hr : Bal r n) (hc : CtxOK ctx (n + 1))
    (hR : RootB ctx) : Bal (ctx.plug (.node false l x r)) (n + 1 + ctx.blk) ∧
      (ctx.plug (.node false l x r)).isRed = false := by
  refine ⟨plug_bal hc (.black hl hr) (fun e => by simp [RBT.isRed] at e), ?_⟩
  by_cases h : ctx = .top
  · subst h; rfl
  · exact hR.isRed h _

end TRB

/-- **The state `remove` hands to `remove_fixup`** (removed colour black): the hole `ctxX` is doubly black
for `tx`, the root is black unless the hole is the root, and the path is at most 128 long. -/
theorem rf_init {ctx : TRB.Ctx} {ct : Bool} {a b : TRB.RBT} {t : U64} {ctxX : TRB.Ctx} {tx : TRB.RBT} {m : Nat}
    (hb : TRB.Bal (ctx.plug (.node ct a t b)) m) (hbl : (ctx.plug (.node ct a t b)).isRed = false)
    (hh : (ctx.plug (.node ct a t b)).height ≤ 128) (hs : DelShape ctx ct a b ctxX tx false) :
    ∃ n, TRB.CtxOK ctxX (n + 1) ∧ TRB.DB tx n ∧ TRB.RootB ctxX ∧ ctxX.depth ≤ 128 := by
  rcases hs with ⟨rfl, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl, rfl⟩ | ⟨ctx2, cy, y, hL, -, rfl, rfl, rfl⟩
  · obtain ⟨n0, hb0, hc0, -⟩ := TRB.CtxOK.of_bal ctxX hb
    have hd := TRB.Ctx.depth_le ctxX (.node false .leaf t tx)
    have h1 : 1 ≤ (TRB.RBT.node false .leaf t tx).height := by
      show 1 ≤ max _ _ + 1; omega
    cases hb0 with
    | black hl hr =>
      cases hl
      exact ⟨0, hc0, TRB.DB.of_bal hr, TRB.RootB.of_isRed hbl, by omega⟩
  · obtain ⟨n0, hb0, hc0, -⟩ := TRB.CtxOK.of_bal ctxX hb
    have hd := TRB.Ctx.depth_le ctxX (.node false tx t .leaf)
    have h1 : 1 ≤ (TRB.RBT.node false tx t .leaf).height := by
      show 1 ≤ max _ _ + 1; omega
    cases hb0 with
    | black hl hr =>
      cases hr
      exact ⟨0, hc0, TRB.DB.of_bal hl, TRB.RootB.of_isRed hbl, by omega⟩
  · obtain ⟨n1, hb1, hc1, hr1⟩ := TRB.CtxOK.of_bal ctx hb
    have hb1' : TRB.Bal (.node ct a y (ctx2.plug (.node false .leaf y tx))) n1 := by
      cases hb1 with
      | red h1 h2 h3 h4 => exact .red h1 h2 h3 h4
      | black h1 h2 => exact .black h1 h2
    have hW' := TRB.plug_bal hc1 hb1' hr1
    have e : ctx.plug (.node ct a y (ctx2.plug (.node false .leaf y tx))) =
        (TRB.Ctx.app ctx2 (.rc ct a y ctx)).plug (.node false .leaf y tx) :=
      (TRB.Ctx.plug_app ctx2 (.rc ct a y ctx) _).symm
    rw [e] at hW'
    obtain ⟨n0, hb0, hc0, -⟩ := TRB.CtxOK.of_bal _ hW'
    have e2 : ctx.plug (.node ct a t (ctx2.plug (.node false .leaf y tx))) =
        (TRB.Ctx.app ctx2 (.rc ct a t ctx)).plug (.node false .leaf y tx) :=
      (TRB.Ctx.plug_app ctx2 (.rc ct a t ctx) _).symm
    have hd := TRB.Ctx.depth_le (TRB.Ctx.app ctx2 (.rc ct a t ctx)) (.node false .leaf y tx)
    rw [← e2, TRB.Ctx.depth_app] at hd
    simp only [TRB.Ctx.depth] at hd
    have h1 : 1 ≤ (TRB.RBT.node false .leaf y tx).height := by
      show 1 ≤ max _ _ + 1; omega
    have hdep : (TRB.Ctx.app ctx2 (.rc ct a y ctx)).depth ≤ 128 := by
      rw [TRB.Ctx.depth_app]; simp only [TRB.Ctx.depth]; omega
    have hRB : TRB.RootB (TRB.Ctx.app ctx2 (.rc ct a y ctx)) :=
      TRB.RootB.of_isRed (t := .node false .leaf y tx)
        (by rw [← e, ← TRB.plug_isRed_key ctx ct a _ t y]; exact hbl)
    cases hb0 with
    | black hl hr =>
      cases hl
      exact ⟨0, hc0, TRB.DB.of_bal hr, hRB, hdep⟩

end Fl4Proofs.P1
