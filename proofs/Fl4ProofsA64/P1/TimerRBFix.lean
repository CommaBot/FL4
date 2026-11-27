-- AArch64 port of Fl4Proofs.P1.TimerRBFix (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d, TIMER-RB-PLAN stage 5, pure part): the `insert_fixup` invariant (CLRS 13.3) on the zipper.
`CtxOK ctx n` says the path `ctx` is red-black for a subtree of black height `n` at the hole, except that a
red subtree root may sit under a red hole parent; `RootB ctx` says the whole tree's root is black unless the
hole is the root.  Plugging a balanced subtree whose root is not red under a red parent gives a red-black
tree (`plug_bal`); in any case the black height counts (`plug_balW`), so the black nodes on the path are at
most 64 (`blk_le_64`), which bounds the fixup's rounds (each round spends one fuel unit and, while the loop
goes on, removes a black path node).  `Rep.recolor`: a colour write at a node is the abstract recolouring.
-/
import Fl4ProofsA64.P1.TimerRBInsH
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64

namespace TRB

namespace Ctx

/-- The colour of the hole's parent (`false` at the top). -/
def parRed : Ctx → Bool
  | top => false
  | lc c _ _ _ => c
  | rc c _ _ _ => c

/-- The black nodes on the path. -/
def blk : Ctx → Nat
  | top => 0
  | lc true _ _ up => up.blk
  | lc false _ _ up => up.blk + 1
  | rc true _ _ up => up.blk
  | rc false _ _ up => up.blk + 1

/-- Away from the top, the root's colour does not depend on the subtree at the hole. -/
theorem plug_isRed : ∀ (ctx : Ctx), ctx ≠ top → ∀ t t' : RBT, (ctx.plug t).isRed = (ctx.plug t').isRed
  | top, h, _, _ => absurd rfl h
  | lc c k r up, _, t, t' => by
    by_cases hu : up = top
    · subst hu; rfl
    · exact plug_isRed up hu _ _
  | rc c l k up, _, t, t' => by
    by_cases hu : up = top
    · subst hu; rfl
    · exact plug_isRed up hu _ _

end Ctx

/-- The path is red-black for a black height `n` at the hole (a red–red edge is allowed only at the hole). -/
inductive CtxOK : Ctx → Nat → Prop
  | top (n : Nat) : CtxOK .top n
  | lcR {k : U64} {r : RBT} {up : Ctx} {n : Nat} : Bal r n → r.isRed = false → up.parRed = false →
      CtxOK up n → CtxOK (.lc true k r up) n
  | lcB {k : U64} {r : RBT} {up : Ctx} {n : Nat} : Bal r n → CtxOK up (n + 1) → CtxOK (.lc false k r up) n
  | rcR {l : RBT} {k : U64} {up : Ctx} {n : Nat} : Bal l n → l.isRed = false → up.parRed = false →
      CtxOK up n → CtxOK (.rc true l k up) n
  | rcB {l : RBT} {k : U64} {up : Ctx} {n : Nat} : Bal l n → CtxOK up (n + 1) → CtxOK (.rc false l k up) n

/-- The whole tree's root is black, unless the hole is the root. -/
def RootB (ctx : Ctx) : Prop := ctx = .top ∨ (ctx.plug .leaf).isRed = false

theorem RootB.isRed {ctx : Ctx} (h : RootB ctx) (hc : ctx ≠ .top) (t : RBT) : (ctx.plug t).isRed = false := by
  rcases h with h | h
  · exact absurd h hc
  · rw [Ctx.plug_isRed ctx hc t .leaf]; exact h

theorem RootB.of_isRed {ctx : Ctx} {t : RBT} (h : (ctx.plug t).isRed = false) : RootB ctx := by
  by_cases hc : ctx = .top
  · exact Or.inl hc
  · exact Or.inr (by rw [Ctx.plug_isRed ctx hc .leaf t]; exact h)

theorem RootB.lc_up {c : Bool} {k : U64} {r : RBT} {up : Ctx} (h : RootB (.lc c k r up)) : RootB up := by
  by_cases hu : up = .top
  · exact Or.inl hu
  · exact RootB.of_isRed (t := .node c .leaf k r) (h.isRed (by intro e; cases e) .leaf)

theorem RootB.rc_up {c : Bool} {l : RBT} {k : U64} {up : Ctx} (h : RootB (.rc c l k up)) : RootB up := by
  by_cases hu : up = .top
  · exact Or.inl hu
  · exact RootB.of_isRed (t := .node c l k .leaf) (h.isRed (by intro e; cases e) .leaf)

/-- A black node put on a root-black path keeps it root-black. -/
theorem RootB.lc_black {k : U64} {r : RBT} {up : Ctx} (h : RootB up) : RootB (.lc false k r up) := by
  by_cases hu : up = .top
  · subst hu; exact Or.inr rfl
  · exact Or.inr (h.isRed hu _)

theorem RootB.rc_black {l : RBT} {k : U64} {up : Ctx} (h : RootB up) : RootB (.rc false l k up) := by
  by_cases hu : up = .top
  · subst hu; exact Or.inr rfl
  · exact Or.inr (h.isRed hu _)

/-- Black height only (no colour constraint). -/
inductive BalW : RBT → Nat → Prop
  | leaf : BalW .leaf 0
  | red {l r : RBT} {k : U64} {n : Nat} : BalW l n → BalW r n → BalW (.node true l k r) n
  | black {l r : RBT} {k : U64} {n : Nat} : BalW l n → BalW r n → BalW (.node false l k r) (n + 1)

theorem Bal.w {t : RBT} {n : Nat} (h : Bal t n) : BalW t n := by
  induction h with
  | leaf => exact .leaf
  | red _ _ _ _ ihl ihr => exact .red ihl ihr
  | black _ _ ihl ihr => exact .black ihl ihr

theorem BalW.pow_le {t : RBT} {n : Nat} (h : BalW t n) : 2 ^ n ≤ t.keys.length + 1 := by
  induction h with
  | leaf => simp [RBT.keys]
  | red _ _ ihl ihr => simp only [RBT.keys, List.length_append, List.length_cons]; omega
  | black _ _ ihl ihr => simp only [RBT.keys, List.length_append, List.length_cons, pow_succ]; omega

/-- A black height of a tree with distinct keys is at most 64. -/
theorem BalW.le_64 {t : RBT} {n : Nat} (h : BalW t n) (hd : t.keys.Nodup) : n ≤ 64 := by
  have h2 := h.pow_le
  have h3 := nodup_len hd
  have e64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  have e65 : (2 : Nat) ^ 65 = 36893488147419103232 := by norm_num
  by_contra hc
  have : (2 : Nat) ^ 65 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem plug_balW : ∀ {ctx : Ctx} {n : Nat}, CtxOK ctx n → ∀ {t : RBT}, BalW t n → BalW (ctx.plug t) (n + ctx.blk)
  | _, _, .top n, t, h => h
  | _, _, .lcR hr _ _ hu, t, h => plug_balW hu (BalW.red h hr.w)
  | _, n, .lcB (k := k) (r := r) (up := up) hr hu, t, h => by
    have := plug_balW hu (t := .node false t k r) (BalW.black h hr.w)
    rwa [show n + 1 + up.blk = n + (up.blk + 1) by omega] at this
  | _, _, .rcR hl _ _ hu, t, h => plug_balW hu (BalW.red hl.w h)
  | _, n, .rcB (l := l) (k := k) (up := up) hl hu, t, h => by
    have := plug_balW hu (t := .node false l k t) (BalW.black hl.w h)
    rwa [show n + 1 + up.blk = n + (up.blk + 1) by omega] at this

/-- Plugging a balanced subtree that is not red under a red parent gives a balanced tree. -/
theorem plug_bal : ∀ {ctx : Ctx} {n : Nat}, CtxOK ctx n → ∀ {t : RBT}, Bal t n →
    (t.isRed = true → ctx.parRed = false) → Bal (ctx.plug t) (n + ctx.blk)
  | _, _, .top n, t, h, _ => h
  | _, _, .lcR hr hrb hp hu, t, h, hc => by
    have ht : t.isRed = false := by
      cases e : t.isRed
      · rfl
      · exact absurd (hc e) (by simp [Ctx.parRed])
    exact plug_bal hu (Bal.red h hr ht hrb) fun _ => hp
  | _, n, .lcB (k := k) (r := r) (up := up) hr hu, t, h, _ => by
    have := plug_bal hu (t := .node false t k r) (Bal.black h hr) fun e => by simp [RBT.isRed] at e
    rwa [show n + 1 + up.blk = n + (up.blk + 1) by omega] at this
  | _, _, .rcR hl hlb hp hu, t, h, hc => by
    have ht : t.isRed = false := by
      cases e : t.isRed
      · rfl
      · exact absurd (hc e) (by simp [Ctx.parRed])
    exact plug_bal hu (Bal.red hl h hlb ht) fun _ => hp
  | _, n, .rcB (l := l) (k := k) (up := up) hl hu, t, h, _ => by
    have := plug_bal hu (t := .node false l k t) (Bal.black hl h) fun e => by simp [RBT.isRed] at e
    rwa [show n + 1 + up.blk = n + (up.blk + 1) by omega] at this

/-- A balanced tree, split at a hole: the subtree is balanced and the path is `CtxOK`. -/
theorem CtxOK.of_bal : ∀ (ctx : Ctx) {t : RBT} {m : Nat}, Bal (ctx.plug t) m →
    ∃ n, Bal t n ∧ CtxOK ctx n ∧ (t.isRed = true → ctx.parRed = false)
  | .top, t, m, h => ⟨m, h, .top m, fun _ => rfl⟩
  | .lc c k r up, t, m, h => by
    obtain ⟨n, hb, hc, hr⟩ := CtxOK.of_bal up (t := .node c t k r) h
    cases c with
    | true =>
      cases hb with
      | red hl hr' bl br => exact ⟨n, hl, .lcR hr' br (hr rfl) hc, fun e => by rw [bl] at e; cases e⟩
    | false =>
      cases hb with
      | black hl hr' => exact ⟨_, hl, .lcB hr' hc, fun _ => rfl⟩
  | .rc c l k up, t, m, h => by
    obtain ⟨n, hb, hc, hr⟩ := CtxOK.of_bal up (t := .node c l k t) h
    cases c with
    | true =>
      cases hb with
      | red hl hr' bl br => exact ⟨n, hr', .rcR hl bl (hr rfl) hc, fun e => by rw [br] at e; cases e⟩
    | false =>
      cases hb with
      | black hl hr' => exact ⟨_, hr', .rcB hl hc, fun _ => rfl⟩

/-- The black path nodes above a hole of a tree with distinct keys: at most 64. -/
theorem blk_le_64 {ctx : Ctx} {n : Nat} {t : RBT} (hc : CtxOK ctx n) (ht : BalW t n)
    (hd : (ctx.plug t).keys.Nodup) : ctx.blk ≤ 64 := by
  have := (plug_balW hc ht).le_64 hd
  omega

/-- A colour write at a node of the tree is the abstract recolouring. -/
theorem Rep.recolor {k : Links} {R : U64} {ctx : Ctx} {c c' : Bool} {l r : RBT} {x : U64}
    (h : Rep k 0#u64 R (ctx.plug (.node c l x r))) (hd : (ctx.plug (.node c l x r)).keys.Nodup) :
    Rep (k.setRed x c') 0#u64 R (ctx.plug (.node c' l x r)) := by
  obtain ⟨hc, ht⟩ := (rep_plug ctx _).1 h
  have hd' := hd
  rw [Ctx.plug_keys] at hd'
  have hM : (l.keys ++ x :: r.keys).Nodup := nd_in hd'
  have nx : ∀ z ∈ ctx.pre ++ ctx.post, z ≠ x := fun z hz e =>
    nd_mid hd' (z := x) (by simp [RBT.keys]) hz e.symm
  have nl : ∀ z ∈ l.keys, z ≠ x := fun z hz => nd_sep hM hz (List.mem_cons_self ..)
  have nr : ∀ z ∈ r.keys, z ≠ x := fun z hz e =>
    (List.nodup_cons.1 (hM.sublist (List.sublist_append_right _ _))).1 (e ▸ hz)
  have same : ∀ z, z ≠ x → (k.setRed x c').l z = k.l z ∧ (k.setRed x c').r z = k.r z ∧
      (k.setRed x c').p z = k.p z ∧ (k.setRed x c').red z = k.red z := fun z hz =>
    ⟨rfl, rfl, rfl, Function.update_of_ne hz _ _⟩
  refine (rep_plug ctx _).2 ⟨hc.congr fun z hz => same z (nx z hz), ?_⟩
  have ht' : Rep k ctx.par x (.node c l x r) := ht
  obtain ⟨hp, -, hl, hr⟩ := Rep.node_inv ht'
  exact .node (Rep.keys_ne0 ht' x (by simp [RBT.keys])) hp (Function.update_self ..)
    (hl.congr fun z hz => same z (nl z hz)) (hr.congr fun z hz => same z (nr z hz))

theorem recolor_keys (ctx : Ctx) (c c' : Bool) (l r : RBT) (x : U64) :
    (ctx.plug (.node c' l x r)).keys = (ctx.plug (.node c l x r)).keys :=
  ctx.plug_keys_congr (by simp [RBT.keys])

end TRB

end Fl4ProofsA64.P1
