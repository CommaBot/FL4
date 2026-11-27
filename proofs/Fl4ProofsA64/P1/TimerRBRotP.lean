-- AArch64 port of Fl4Proofs.P1.TimerRBRotP (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d, TIMER-RB-PLAN stage 3c, part 2): rotations on the heap refine the abstract rotations.  If the
links change exactly as `timer::rotate_left` writes them (`x.r := b`, `b.p := x`, `y.p := x.p`, the hole's
link := `y`, `y.l := x`, `x.p := y`), the heap tree from the (possibly new) root word is the rotated tree
(`rotL_rep`); `rotR_rep` is the mirror.
-/
import Fl4ProofsA64.P1.TimerRBRot
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64

namespace TRB

/-- The nodes of a represented tree are non-null. -/
theorem Rep.keys_ne0 {k : Links} {par x : U64} {t : RBT} (h : Rep k par x t) : ∀ z ∈ t.keys, z ≠ 0#u64 := by
  induction h with
  | leaf => intro z hz; simp [RBT.keys] at hz
  | @node par x c l r hx hp hc hl hr ihl ihr =>
    intro z hz
    simp only [RBT.keys, List.mem_append, List.mem_cons] at hz
    rcases hz with hz | rfl | hz
    · exact ihl z hz
    · exact hx
    · exact ihr z hz

/-- In `P ++ M ++ Q` without duplicates, `M` and `P ++ Q` are disjoint. -/
theorem nd_mid {P M Q : List U64} (h : (P ++ M ++ Q).Nodup) {z w : U64} (hz : z ∈ M) (hw : w ∈ P ++ Q) :
    z ≠ w := by
  rcases List.mem_append.1 hw with hw | hw
  · exact (nd_sep (h.sublist (List.sublist_append_left _ _)) hw hz).symm
  · exact nd_sep h (List.mem_append_right _ hz) hw

theorem nd_out {P M Q : List U64} (h : (P ++ M ++ Q).Nodup) : (P ++ Q).Nodup :=
  h.sublist ((List.sublist_append_left P M).append (List.Sublist.refl Q))

theorem nd_in {P M Q : List U64} (h : (P ++ M ++ Q).Nodup) : M.Nodup :=
  h.sublist ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _))

/-- A subtree whose root's parent word is re-pointed (and nothing else of its nodes changed). -/
theorem Rep.reparent {k k' : Links} {p p' x : U64} {t : RBT} (h : Rep k p x t) (hn : t.keys.Nodup)
    (er : x ≠ 0#u64 → k'.l x = k.l x ∧ k'.r x = k.r x ∧ k'.p x = p' ∧ k'.red x = k.red x)
    (eo : ∀ z ∈ t.keys, z ≠ x → k'.l z = k.l z ∧ k'.r z = k.r z ∧ k'.p z = k.p z ∧ k'.red z = k.red z) :
    Rep k' p' x t := by
  cases h with
  | leaf _ _ e => exact .leaf _ _ e
  | @node _ _ c l r hx hp hc hl hr =>
    obtain ⟨e1, e2, e3, e4⟩ := er hx
    have hn0 : (l.keys ++ x :: r.keys).Nodup := hn
    have hn' : (x :: r.keys).Nodup := hn0.sublist (List.sublist_append_right _ _)
    refine .node hx e3 (e4.trans hc) ?_ ?_
    · rw [e1]
      exact hl.congr fun z hz => eo z (by simp [RBT.keys, hz]) (nd_sep hn0 hz (List.mem_cons_self ..))
    · rw [e2]
      exact hr.congr fun z hz => eo z (by simp [RBT.keys, hz])
        (fun e => (List.nodup_cons.1 hn').1 (e ▸ hz))

/-- The four links of `z` are kept. -/
abbrev Same (k k' : Links) (z : U64) : Prop :=
  k'.l z = k.l z ∧ k'.r z = k.r z ∧ k'.p z = k.p z ∧ k'.red z = k.red z

/-- **Left rotation on the heap.** -/
theorem rotL_rep {k k' : Links} {R R' : U64} {ctx : Ctx} {cx cy : Bool} {a b g : RBT} {x y : U64}
    (h : Rep k 0#u64 R (ctx.plug (.node cx a x (.node cy b y g))))
    (hd : (ctx.plug (.node cx a x (.node cy b y g))).keys.Nodup)
    (ex : k'.l x = k.l x ∧ k'.r x = b.rootKey ∧ k'.p x = y ∧ k'.red x = k.red x)
    (ey : k'.l y = x ∧ k'.r y = k.r y ∧ k'.p y = ctx.par ∧ k'.red y = k.red y)
    (eb : b.rootKey ≠ 0#u64 → k'.l b.rootKey = k.l b.rootKey ∧ k'.r b.rootKey = k.r b.rootKey ∧
      k'.p b.rootKey = x ∧ k'.red b.rootKey = k.red b.rootKey)
    (eo : ∀ z, z ≠ x → z ≠ y → z ≠ b.rootKey → z ≠ ctx.par → Same k k' z)
    (hu : HoleUpd k k' R R' ctx y) :
    Rep k' 0#u64 R' (ctx.plug (rotL (.node cx a x (.node cy b y g)))) := by
  obtain ⟨hc, ht⟩ := (rep_plug ctx _).1 h
  have hc' : CRep k R ctx x := hc
  have ht' : Rep k ctx.par x (.node cx a x (.node cy b y g)) := ht
  have n0 := h.keys_ne0
  rw [Ctx.plug_keys] at hd n0
  have hM : (a.keys ++ x :: (b.keys ++ y :: g.keys)).Nodup := nd_in hd
  have hM2 : (x :: (b.keys ++ y :: g.keys)).Nodup := hM.sublist (List.sublist_append_right _ _)
  have hM3 : (b.keys ++ y :: g.keys).Nodup := (List.nodup_cons.1 hM2).2
  have hM4 : (y :: g.keys).Nodup := hM3.sublist (List.sublist_append_right _ _)
  -- membership in the middle / in the whole tree
  have mM : ∀ z, z ∈ a.keys ∨ z = x ∨ z ∈ b.keys ∨ z = y ∨ z ∈ g.keys →
      z ∈ (RBT.node cx a x (.node cy b y g)).keys := fun z hz => by
    simp only [RBT.keys, List.mem_append, List.mem_cons]; tauto
  have nz : ∀ z, z ∈ a.keys ∨ z = x ∨ z ∈ b.keys ∨ z = y ∨ z ∈ g.keys → z ≠ 0#u64 := fun z hz =>
    n0 z (List.mem_append_left _ (List.mem_append_right _ (mM z hz)))
  have hpar : ∀ z, z ∈ a.keys ∨ z = x ∨ z ∈ b.keys ∨ z = y ∨ z ∈ g.keys → z ≠ ctx.par := fun z hz => by
    by_cases e : ctx = .top
    · subst e; exact nz z hz
    · exact nd_mid hd (mM z hz) (Ctx.par_mem ctx e)
  have nb : ∀ z, z ≠ 0#u64 → z ∉ b.keys → z ≠ b.rootKey := fun z h0 hb e => by
    rcases b.rootKey_mem with e' | e'
    · exact h0 (e.trans e')
    · exact hb (e ▸ e')
  -- distinctness inside the middle
  have ax : ∀ z ∈ a.keys, z ≠ x := fun z hz => nd_sep hM hz (by simp)
  have ay : ∀ z ∈ a.keys, z ≠ y := fun z hz => nd_sep hM hz (by simp)
  have ab : ∀ z ∈ a.keys, z ∉ b.keys := fun z hz hb => nd_sep hM hz (by simp [hb]) rfl
  have xb : x ∉ b.keys := fun hb => (List.nodup_cons.1 hM2).1 (by simp [hb])
  have xy : x ≠ y := fun e => (List.nodup_cons.1 hM2).1 (by simp [e])
  have gx : ∀ z ∈ g.keys, z ≠ x := fun z hz e =>
    (List.nodup_cons.1 hM2).1 (List.mem_append_right _ (List.mem_cons_of_mem _ (e ▸ hz)))
  have by_ : ∀ z ∈ b.keys, z ≠ y := fun z hz => nd_sep hM3 hz (by simp)
  have gb : ∀ z ∈ g.keys, z ∉ b.keys := fun z hz hb => nd_sep hM3 hb (by simp [hz]) rfl
  have gy : ∀ z ∈ g.keys, z ≠ y := fun z hz e => (List.nodup_cons.1 hM4).1 (e ▸ hz)
  cases ht' with
  | node hx0 hpx hcx ha hyy =>
    have e1 : k.r x = y := hyy.root
    rw [e1] at hyy
    cases hyy with
    | node hy0 hpy hcy hb hg =>
      have e2 : k.l y = b.rootKey := hb.root
      rw [e2] at hb
      refine (rep_plug ctx _).2 ⟨?_, ?_⟩
      · show CRep k' R' ctx y
        refine hc'.hole (nd_out hd) (fun z hz hzp => eo z ?_ ?_ ?_ hzp) hu
        · exact (nd_mid hd (mM x (Or.inr (Or.inl rfl))) hz).symm
        · exact (nd_mid hd (mM y (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hz).symm
        · exact nb z (n0 z (by simp only [List.mem_append] at hz ⊢; tauto))
            (fun hb => nd_mid hd (mM z (Or.inr (Or.inr (Or.inl hb)))) hz rfl)
      · show Rep k' ctx.par y (.node cy (.node cx a x b) y g)
        refine .node hy0 ey.2.2.1 (ey.2.2.2.trans hcy) ?_ ?_
        · rw [ey.1]
          refine .node hx0 ex.2.2.1 (ex.2.2.2.trans hcx) ?_ ?_
          · rw [ex.1]
            exact ha.congr fun z hz => eo z (ax z hz) (ay z hz) (nb z (nz z (Or.inl hz)) (ab z hz))
              (hpar z (Or.inl hz))
          · rw [ex.2.1]
            exact hb.reparent (hM3.sublist (List.sublist_append_left _ _)) eb
              fun z hz hzb => eo z (fun e => xb (e ▸ hz)) (by_ z hz) hzb (hpar z (Or.inr (Or.inr (Or.inl hz))))
        · rw [ey.2.1]
          exact hg.congr fun z hz => eo z (gx z hz) (gy z hz) (nb z (nz z (Or.inr (Or.inr (Or.inr (Or.inr hz))))) (gb z hz))
            (hpar z (Or.inr (Or.inr (Or.inr (Or.inr hz)))))

/-- **Right rotation on the heap** (mirror of `rotL_rep`). -/
theorem rotR_rep {k k' : Links} {R R' : U64} {ctx : Ctx} {cx cy : Bool} {a b g : RBT} {x y : U64}
    (h : Rep k 0#u64 R (ctx.plug (.node cx (.node cy a y b) x g)))
    (hd : (ctx.plug (.node cx (.node cy a y b) x g)).keys.Nodup)
    (ex : k'.l x = b.rootKey ∧ k'.r x = k.r x ∧ k'.p x = y ∧ k'.red x = k.red x)
    (ey : k'.l y = k.l y ∧ k'.r y = x ∧ k'.p y = ctx.par ∧ k'.red y = k.red y)
    (eb : b.rootKey ≠ 0#u64 → k'.l b.rootKey = k.l b.rootKey ∧ k'.r b.rootKey = k.r b.rootKey ∧
      k'.p b.rootKey = x ∧ k'.red b.rootKey = k.red b.rootKey)
    (eo : ∀ z, z ≠ x → z ≠ y → z ≠ b.rootKey → z ≠ ctx.par → Same k k' z)
    (hu : HoleUpd k k' R R' ctx y) :
    Rep k' 0#u64 R' (ctx.plug (rotR (.node cx (.node cy a y b) x g))) := by
  obtain ⟨hc, ht⟩ := (rep_plug ctx _).1 h
  have hc' : CRep k R ctx x := hc
  have ht' : Rep k ctx.par x (.node cx (.node cy a y b) x g) := ht
  have n0 := h.keys_ne0
  rw [Ctx.plug_keys] at hd n0
  have hM : (a.keys ++ y :: b.keys ++ x :: g.keys).Nodup := nd_in hd
  have hM1 : (a.keys ++ y :: b.keys).Nodup := hM.sublist (List.sublist_append_left _ _)
  have hM2 : (y :: b.keys).Nodup := hM1.sublist (List.sublist_append_right _ _)
  have hM4 : (x :: g.keys).Nodup := hM.sublist (List.sublist_append_right _ _)
  have mM : ∀ z, z ∈ a.keys ∨ z = y ∨ z ∈ b.keys ∨ z = x ∨ z ∈ g.keys →
      z ∈ (RBT.node cx (.node cy a y b) x g).keys := fun z hz => by
    simp only [RBT.keys, List.mem_append, List.mem_cons]; tauto
  have nz : ∀ z, z ∈ a.keys ∨ z = y ∨ z ∈ b.keys ∨ z = x ∨ z ∈ g.keys → z ≠ 0#u64 := fun z hz =>
    n0 z (List.mem_append_left _ (List.mem_append_right _ (mM z hz)))
  have hpar : ∀ z, z ∈ a.keys ∨ z = y ∨ z ∈ b.keys ∨ z = x ∨ z ∈ g.keys → z ≠ ctx.par := fun z hz => by
    by_cases e : ctx = .top
    · subst e; exact nz z hz
    · exact nd_mid hd (mM z hz) (Ctx.par_mem ctx e)
  have nb : ∀ z, z ≠ 0#u64 → z ∉ b.keys → z ≠ b.rootKey := fun z h0 hb e => by
    rcases b.rootKey_mem with e' | e'
    · exact h0 (e.trans e')
    · exact hb (e ▸ e')
  have ay : ∀ z ∈ a.keys, z ≠ y := fun z hz => nd_sep hM1 hz (by simp)
  have ax : ∀ z ∈ a.keys, z ≠ x := fun z hz => nd_sep hM (by simp [hz]) (by simp)
  have ab : ∀ z ∈ a.keys, z ∉ b.keys := fun z hz hb => nd_sep hM1 hz (by simp [hb]) rfl
  have yb : y ∉ b.keys := (List.nodup_cons.1 hM2).1
  have bx : ∀ z ∈ b.keys, z ≠ x := fun z hz => nd_sep hM (by simp [hz]) (by simp)
  have gx : ∀ z ∈ g.keys, z ≠ x := fun z hz e => (List.nodup_cons.1 hM4).1 (e ▸ hz)
  have gy : ∀ z ∈ g.keys, z ≠ y := fun z hz e => nd_sep hM (a := y) (b := z) (by simp) (by simp [hz]) e.symm
  have gb : ∀ z ∈ g.keys, z ∉ b.keys := fun z hz hb => nd_sep hM (a := z) (b := z) (by simp [hb]) (by simp [hz]) rfl
  cases ht' with
  | node hx0 hpx hcx hyy hg =>
    have e1 : k.l x = y := hyy.root
    rw [e1] at hyy
    cases hyy with
    | node hy0 hpy hcy ha hb =>
      have e2 : k.r y = b.rootKey := hb.root
      rw [e2] at hb
      refine (rep_plug ctx _).2 ⟨?_, ?_⟩
      · show CRep k' R' ctx y
        refine hc'.hole (nd_out hd) (fun z hz hzp => eo z ?_ ?_ ?_ hzp) hu
        · exact (nd_mid hd (mM x (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hz).symm
        · exact (nd_mid hd (mM y (Or.inr (Or.inl rfl))) hz).symm
        · exact nb z (n0 z (by simp only [List.mem_append] at hz ⊢; tauto))
            (fun hb => nd_mid hd (mM z (Or.inr (Or.inr (Or.inl hb)))) hz rfl)
      · show Rep k' ctx.par y (.node cy a y (.node cx b x g))
        refine .node hy0 ey.2.2.1 (ey.2.2.2.trans hcy) ?_ ?_
        · rw [ey.1]
          exact ha.congr fun z hz => eo z (ax z hz) (ay z hz) (nb z (nz z (Or.inl hz)) (ab z hz))
            (hpar z (Or.inl hz))
        · rw [ey.2.1]
          refine .node hx0 ex.2.2.1 (ex.2.2.2.trans hcx) ?_ ?_
          · rw [ex.1]
            exact hb.reparent (List.nodup_cons.1 hM2).2 eb
              fun z hz hzb => eo z (bx z hz) (fun e => yb (e ▸ hz)) hzb (hpar z (Or.inr (Or.inr (Or.inl hz))))
          · rw [ex.2.1]
            exact hg.congr fun z hz => eo z (gx z hz) (gy z hz) (nb z (nz z (Or.inr (Or.inr (Or.inr (Or.inr hz))))) (gb z hz))
              (hpar z (Or.inr (Or.inr (Or.inr (Or.inr hz)))))

end TRB

end Fl4ProofsA64.P1
