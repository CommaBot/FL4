-- AArch64 port of Fl4Proofs.P1.TimerRBRot (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d, TIMER-RB-PLAN stage 3c, part 1): the keys around a hole (`Ctx.pre`/`Ctx.post`, `plug_keys`) and
the congruence of a path (`CRep.congr`): a path reads only the links of its own nodes and siblings.
-/
import Fl4ProofsA64.P1.TimerRBZip
import Fl4ProofsA64.P1.TimerRBFrame
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64

namespace TRB

namespace Ctx

/-- The in-order keys before / after the hole. -/
def pre : Ctx → List U64
  | top => []
  | lc _ _ _ up => up.pre
  | rc _ l k up => up.pre ++ l.keys ++ [k]

def post : Ctx → List U64
  | top => []
  | lc _ k r up => k :: (r.keys ++ up.post)
  | rc _ _ _ up => up.post

theorem plug_keys : ∀ (ctx : Ctx) (t : RBT), (ctx.plug t).keys = ctx.pre ++ t.keys ++ ctx.post
  | top, t => by simp [plug, pre, post]
  | lc c k r up, t => by
    show (up.plug (.node c t k r)).keys = _
    rw [plug_keys up]; simp [pre, post, RBT.keys]
  | rc c l k up, t => by
    show (up.plug (.node c l k t)).keys = _
    rw [plug_keys up]; simp [pre, post, RBT.keys]

/-- The hole's parent is a key around the hole. -/
theorem par_mem : ∀ (ctx : Ctx), ctx ≠ top → ctx.par ∈ ctx.pre ++ ctx.post
  | top, h => absurd rfl h
  | lc _ _ _ _, _ => by simp [par, pre, post]
  | rc _ _ _ _, _ => by simp [par, pre, post]

end Ctx

/-- Two distinct parts of a list without duplicates share no element. -/
theorem nd_sep {l₁ l₂ : List U64} {a b : U64} (h : (l₁ ++ l₂).Nodup) (ha : a ∈ l₁) (hb : b ∈ l₂) : a ≠ b := by
  rintro rfl
  exact List.disjoint_of_nodup_append h ha hb

/-- A path reads only the links of the keys around the hole. -/
theorem CRep.congr {k k' : Links} {R : U64} {ctx : Ctx} {x : U64} (h : CRep k R ctx x)
    (he : ∀ z ∈ ctx.pre ++ ctx.post, k'.l z = k.l z ∧ k'.r z = k.r z ∧ k'.p z = k.p z ∧ k'.red z = k.red z) :
    CRep k' R ctx x := by
  revert he
  induction h with
  | top e => intro _; exact .top e
  | @lc c kk r up x hx hl hc hp hr hu ih =>
    intro he
    obtain ⟨e1, e2, e3, e4⟩ := he kk (by simp [Ctx.pre, Ctx.post])
    refine .lc hx (e1.trans hl) (e4.trans hc) (e3.trans hp) ?_ (ih fun z hz => he z ?_)
    · rw [e2]; exact hr.congr fun z hz => he z (by simp [Ctx.pre, Ctx.post, hz])
    · simp only [Ctx.pre, Ctx.post, List.mem_append, List.mem_cons] at hz ⊢; tauto
  | @rc c l kk up x hx hr hc hp hl hu ih =>
    intro he
    obtain ⟨e1, e2, e3, e4⟩ := he kk (by simp [Ctx.pre, Ctx.post])
    refine .rc hx (e2.trans hr) (e4.trans hc) (e3.trans hp) ?_ (ih fun z hz => he z ?_)
    · rw [e1]; exact hl.congr fun z hz => he z (by simp [Ctx.pre, Ctx.post, hz])
    · simp only [Ctx.pre, Ctx.post, List.mem_append, List.mem_cons] at hz ⊢; tauto

/-- The hole's parent link (or, at the top, the root word) changed to `y`; the parent's other words kept. -/
def HoleUpd (k k' : Links) (R R' : U64) : Ctx → U64 → Prop
  | .top, y => R' = y
  | .lc _ kk _ _, y => R' = R ∧ k'.l kk = y ∧ k'.r kk = k.r kk ∧ k'.p kk = k.p kk ∧ k'.red kk = k.red kk
  | .rc _ _ kk _, y => R' = R ∧ k'.r kk = y ∧ k'.l kk = k.l kk ∧ k'.p kk = k.p kk ∧ k'.red kk = k.red kk

/-- **Re-pointing the hole.** If only the hole's link changed (to `y`), the path is kept, now ending at `y`. -/
theorem CRep.hole {k k' : Links} {R R' : U64} {ctx : Ctx} {x y : U64} (h : CRep k R ctx x)
    (hn : (ctx.pre ++ ctx.post).Nodup)
    (he : ∀ z ∈ ctx.pre ++ ctx.post, z ≠ ctx.par →
      k'.l z = k.l z ∧ k'.r z = k.r z ∧ k'.p z = k.p z ∧ k'.red z = k.red z)
    (hu : HoleUpd k k' R R' ctx y) : CRep k' R' ctx y := by
  cases h with
  | top e => exact .top hu
  | @lc c kk r up _ hx hl hc hp hr hup =>
    obtain ⟨eR, e1, e2, e3, e4⟩ := hu
    have hn' : (kk :: (r.keys ++ up.post)).Nodup := hn.sublist (List.sublist_append_right _ _)
    have nk1 : ∀ z ∈ r.keys ++ up.post, z ≠ kk := fun z hz e => by
      subst e; exact (List.nodup_cons.1 hn').1 hz
    have nk2 : ∀ z ∈ up.pre, z ≠ kk := fun z hz => nd_sep (l₁ := up.pre) hn hz (by simp [Ctx.post])
    refine .lc hx e1 (e4.trans hc) (e3.trans hp) ?_ ?_
    · rw [e2]
      exact hr.congr fun z hz => he z (by simp [Ctx.pre, Ctx.post, hz])
        (nk1 z (List.mem_append_left _ hz))
    · rw [eR]
      refine hup.congr fun z hz => he z ?_ ?_
      · simp only [Ctx.pre, Ctx.post, List.mem_append, List.mem_cons] at hz ⊢; tauto
      · rcases List.mem_append.1 hz with hz | hz
        · exact nk2 z hz
        · exact nk1 z (List.mem_append_right _ hz)
  | @rc c l kk up _ hx hr hc hp hl hup =>
    obtain ⟨eR, e1, e2, e3, e4⟩ := hu
    have hn' : (up.pre ++ l.keys ++ [kk]).Nodup := hn.sublist (List.sublist_append_left _ _)
    have nk1 : ∀ z ∈ up.pre ++ l.keys, z ≠ kk := fun z hz => nd_sep hn' hz (by simp)
    have nk2 : ∀ z ∈ up.post, z ≠ kk := fun z hz e => nd_sep (l₁ := up.pre ++ l.keys ++ [kk]) hn
      (by simp) hz e.symm
    refine .rc hx e1 (e4.trans hc) (e3.trans hp) ?_ ?_
    · rw [e2]
      exact hl.congr fun z hz => he z (by simp [Ctx.pre, Ctx.post, hz])
        (nk1 z (List.mem_append_right _ hz))
    · rw [eR]
      refine hup.congr fun z hz => he z ?_ ?_
      · simp only [Ctx.pre, Ctx.post, List.mem_append, List.mem_cons] at hz ⊢; tauto
      · rcases List.mem_append.1 hz with hz | hz
        · exact nk1 z (List.mem_append_left _ hz)
        · exact nk2 z hz

end TRB

end Fl4ProofsA64.P1
