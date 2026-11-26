-- AArch64 port of Fl4Proofs.P1.TimerRBDelC (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d, TIMER-RB-PLAN stage 6 composed): the structural part of `timer::remove` from `TimerRB`.
For an armed `t` (a key of the tree of its core `c`, `W = ctx.plug (node ct a t b)`), `remove` reads
`c` from `t`'s core bits, sets `TIMER_MIN` to the new leftmost node when `t` was the leftmost one (the
leftmost walk of `t`'s right subtree, or `t`'s parent), then splices/transplants (`delTail.spec`): the
tree before `remove_fixup` is `ctxX.plug tx` whose keys are `W`'s without `t` (`DelShape.keys`), and the
fixup (a hypothesis here, stage 7) runs exactly when the removed colour is black; `t`'s words are cleared
last (`clrT`).  No fuel cut-off is reached (`timer.remove_loop0.lm`, heights from `CoreTree.height_le`).
-/
import Fl4ProofsA64.P1.TimerRBDelH
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

namespace TRB

/-- Every key of a tree sits at some path. -/
theorem RBT.mem_split : ∀ (W : RBT) (t : U64), t ∈ W.keys →
    ∃ (ctx : Ctx) (c : Bool) (a b : RBT), W = ctx.plug (.node c a t b)
  | .leaf, _, h => by simp [RBT.keys] at h
  | .node c l k r, t, h => by
    simp only [RBT.keys, List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · obtain ⟨ctx, c', a, b, e⟩ := RBT.mem_split l t h
      exact ⟨Ctx.app ctx (.lc c k r .top), c', a, b, by rw [Ctx.plug_app, ← e]; rfl⟩
    · subst h; exact ⟨.top, c, l, r, rfl⟩
    · obtain ⟨ctx, c', a, b, e⟩ := RBT.mem_split r t h
      exact ⟨Ctx.app ctx (.rc c l k .top), c', a, b, by rw [Ctx.plug_app, ← e]; rfl⟩

end TRB

theorem DelShape.keys {ctx : TRB.Ctx} {ct : Bool} {a b : TRB.RBT} {ctxX : TRB.Ctx} {tx : TRB.RBT} {rr : Bool}
    (h : DelShape ctx ct a b ctxX tx rr) : (ctxX.plug tx).keys = TRB.delKeys ctx a b := by
  rcases h with ⟨rfl, rfl, rfl, -⟩ | ⟨-, rfl, rfl, rfl, -⟩ | ⟨ctx2, cy, y, hL, -, rfl, rfl, -⟩
  · rw [TRB.Ctx.plug_keys]; simp [TRB.RBT.keys]
  · rw [TRB.Ctx.plug_keys]; simp [TRB.RBT.keys]
  · rw [TRB.Ctx.plug_app]
    show (ctx.plug (.node ct a y (ctx2.plug tx))).keys = _
    rw [TRB.Ctx.plug_keys]
    simp only [TRB.delKeys, TRB.RBT.keys, hL.keys_node cy y tx, List.append_assoc]

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Cs : Set U64}

/-- `core_of` of a key of core `c`'s tree is `c`. -/
theorem timer.core_of.rb (s : S) (t : U64) {c : U64} {W : TRB.RBT} (ct : CoreTree st T s c W) (htW : t ∈ W.keys) :
    timer.core_of st s t ⦃ v => v = c ⦄ := by
  unfold timer.core_of
  step with obj.Tcb.timer_height.val as ⟨i, ei⟩
  step as ⟨v, hv1, hv2⟩
  exact UScalar.eq_of_val_eq (by rw [hv1, ei]; exact ct.core t htW)

/-- **The structural part of `timer::remove`** (stage 6).  `t` unarmed: nothing happens.  `t` armed: it is
a key of the tree `ctx.plug (node ct a t b)` of its core `c ∈ Cs`; `TIMER_MIN` is updated to the leftmost
key without `t` (one node-word write, `s1`), the splice/transplant gives the state `s7` before the fixup
(`DelShape`, `DelMid`), the fixup runs iff the removed colour `rr` is black (its spec `hfix` is assumed,
stage 7), and `t`'s words are cleared. -/
theorem timer.remove.struct (s : S) (t : U64) {Q : S → S → Prop} (hT : TcbPlaced T) (ht : t ∈ T)
    (hR : TimerRB st T Cs s) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hfix : ∀ c ctx ct a b s1 ctxX tx rr s7, c ∈ Cs → CoreTree st T s c (ctx.plug (.node ct a t b)) →
      DelShape ctx ct a b ctxX tx rr → DelMid st T s1 c (ctx.plug (.node ct a t b)).keys s7 (ctxX.plug tx) →
      rr = false → timer.remove_fixup st s7 c tx.rootKey ctxX.par ⦃ s8 => Q s7 s8 ⦄) :
    timer.remove st s t ⦃ s' => (L.mem s (tdA t) = 0#u64 ∧ s' = s) ∨
      ∃ c ∈ Cs, ∃ ctx ct a b, CoreTree st T s c (ctx.plug (.node ct a t b)) ∧ ∃ s1 ctxX tx rr s7 s8,
        WritesIn st s s1 (· = L.nodeAt s c layout.node.TIMER_MIN) ∧
        L.mem s1 (L.nodeAt s1 c layout.node.TIMER_MIN) = (TRB.delKeys ctx a b).headD 0#u64 ∧
        DelShape ctx ct a b ctxX tx rr ∧ DelMid st T s1 c (ctx.plug (.node ct a t b)).keys s7 (ctxX.plug tx) ∧
        (rr = true → s8 = s7) ∧ (rr = false → Q s7 s8) ∧ s' = clrT st s8 t ⦄ := by
  have hoM : layout.node.TIMER_MIN.val < 4288 := by rw [timer_min_val]; simp
  have hoM8 : layout.node.TIMER_MIN.val % 8 = 0 := by rw [timer_min_val]
  have hoR : layout.node.TIMER_ROOT.val < 4288 := by rw [timer_root_val]; simp
  unfold timer.remove
  step with obj.Tcb.timer_deadline.val as ⟨i, ei⟩
  split
  · rename_i hi; exact (WP.spec_ok _).2 (Or.inl ⟨by rw [← ei]; exact hi, rfl⟩)
  rename_i hi
  have hd : L.mem s (tdA t) ≠ 0#u64 := by rw [← ei]; exact hi
  obtain ⟨c, hc, W, ct0, htW⟩ := hR.armed t ht hd
  obtain ⟨ctx, ct, a, b, eW⟩ := TRB.RBT.mem_split W t htW
  subst eW
  have hNc := hN c hc
  obtain ⟨-, m0, -, -, -, -, ht'⟩ := TRB.mid_facts ct0.rep ct0.nodup
  have ht' : TRB.Rep (lk st s) ctx.par t (.node ct a t b) := ht'
  have ht0 : t ≠ 0#u64 := m0 t (by simp [TRB.RBT.keys])
  obtain ⟨hpt, -, -, hrb⟩ := TRB.Rep.node_inv ht'
  have hrb2 : TRB.Rep (lk st s) t b.rootKey b := by rw [← hrb.root]; exact hrb
  step with timer.core_of.rb s t ct0 htW as ⟨cpu, ecpu⟩
  subst c
  step with obj.node_get.spec as ⟨i1, ei1⟩
  rw [ct0.min] at ei1
  -- everything after the `TIMER_MIN` update
  have TL : ∀ s1, WritesIn st s s1 (· = L.nodeAt s cpu layout.node.TIMER_MIN) →
      L.mem s1 (L.nodeAt s1 cpu layout.node.TIMER_MIN) = (TRB.delKeys ctx a b).headD 0#u64 →
      delTail st s1 cpu t ⦃ s' => (L.mem s (tdA t) = 0#u64 ∧ s' = s) ∨
      ∃ c ∈ Cs, ∃ ctx ct a b, CoreTree st T s c (ctx.plug (.node ct a t b)) ∧ ∃ s1 ctxX tx rr s7 s8,
        WritesIn st s s1 (· = L.nodeAt s c layout.node.TIMER_MIN) ∧
        L.mem s1 (L.nodeAt s1 c layout.node.TIMER_MIN) = (TRB.delKeys ctx a b).headD 0#u64 ∧
        DelShape ctx ct a b ctxX tx rr ∧ DelMid st T s1 c (ctx.plug (.node ct a t b)).keys s7 (ctxX.plug tx) ∧
        (rr = true → s8 = s7) ∧ (rr = false → Q s7 s8) ∧ s' = clrT st s8 t ⦄ := by
    intro s1 w hm
    have eb : L.nodeBase s1 cpu = L.nodeBase s cpu := by simp [LawfulStore.nodeBase, w.1]
    have hN1 : NodePlaced st T s1 cpu := ⟨by rw [eb]; exact hNc.align, by rw [eb]; exact hNc.fits, by rw [eb]; exact hNc.disj⟩
    have k := KeepOut.of_wi (X := fun _ => False) hT hNc
      (w.mono fun b hb => Or.inr ⟨_, hoM, hb⟩)
    have hroot : L.mem s1 (L.nodeAt s1 cpu layout.node.TIMER_ROOT) = L.mem s (L.nodeAt s cpu layout.node.TIMER_ROOT) := by
      rw [nodeAt_of_ksb w.1]
      refine w.mem_eq (nodeAt_aligned hNc hoR (by rw [timer_root_val])) fun e => ?_
      have := congrArg UScalar.val e
      rw [nodeAt_val hNc hoR, nodeAt_val hNc hoM, timer_min_val, timer_root_val] at this
      omega
    have hrep1 : TRB.Rep (lk st s1) 0#u64 (L.mem s1 (L.nodeAt s1 cpu layout.node.TIMER_ROOT)) (ctx.plug (.node ct a t b)) := by
      rw [hroot]
      refine ct0.rep.congr fun y hy => ?_
      have f := k.fld y (ct0.inT y hy) id
      refine ⟨f 3544#u64 (by simp) (by simp), f 3552#u64 (by simp) (by simp), f 3560#u64 (by simp) (by simp), ?_⟩
      show ((L.mem s1 (thA y) &&& 1#u64) != 0#u64) = ((L.mem s (thA y) &&& 1#u64) != 0#u64)
      rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, f 3568#u64 (by simp) (by simp)]
    refine WP.spec_mono (delTail.spec s1 cpu t (Q := Q) hT hN1 hrep1 ct0.nodup ct0.inT ct0.height_le
      fun ctxX tx rr s7 sh m hr => hfix cpu ctx ct a b s1 ctxX tx rr s7 hc ct0 sh m hr) fun s' hs => ?_
    obtain ⟨ctxX, tx, rr, s7, s8, sh, m, h1, h2, h3⟩ := hs
    exact Or.inr ⟨cpu, hc, ctx, ct, a, b, ct0, s1, ctxX, tx, rr, s7, s8, w, hm, sh, m, h1, h2, h3⟩
  split
  · rename_i heq
    have hmt : (ctx.plug (.node ct a t b)).minKey = t := ei1.symm.trans heq
    step with timer.right.rep (st := st) s ht' as ⟨nx, enx⟩
    have enx' : nx = b.rootKey := enx
    subst enx'
    step with obj.Tcb.is_null.spec as ⟨bn, ebn⟩
    split
    · rename_i hbn
      have eb : b = .leaf := hrb2.zero (by rw [ebn] at hbn; exact of_decide_eq_true hbn)
      step with timer.parent.rep (st := st) s ht' as ⟨n1, en1⟩
      rw [if_neg ht0] at en1
      refine WP.spec_bind (obj.node_set.spec s cpu _ n1) fun s1 e1 => ?_
      subst e1
      exact TL _ (writesIn_wr (nodeAt_aligned hNc hoM hoM8))
        (by rw [node_wr_eq hNc hoM hoM8, en1, TRB.min_new_par ct0.nodup hmt eb])
    · rename_i hbn
      have htr0 : b.rootKey ≠ 0#u64 := fun e => hbn (by rw [ebn, e]; rfl)
      have hbh : b.height ≤ layout.TREE_FUEL.val + 1 := by
        have h1 := TRB.Ctx.height_le ctx (.node ct a t b)
        have h2 : b.height + 1 ≤ (TRB.RBT.node ct a t b).height := Nat.succ_le_succ (le_max_right _ _)
        have h3 := ct0.height_le
        rw [layout.TREE_FUEL.val_eq]; omega
      refine WP.spec_bind (timer.remove_loop1.lm s layout.TREE_FUEL hrb2 htr0 hbh) fun y hy => ?_
      obtain ⟨ctx2, cy, g, hL, eb⟩ := hy
      refine WP.spec_bind (obj.node_set.spec s cpu _ y) fun s1 e1 => ?_
      subst e1
      have hd2 := ct0.nodup
      rw [eb] at hd2 hmt
      exact TL _ (writesIn_wr (nodeAt_aligned hNc hoM hoM8))
        (by rw [node_wr_eq hNc hoM hoM8, eb, TRB.min_new_r hd2 hmt hL])
  · rename_i hne
    exact TL s (WritesIn.refl _ _) (by rw [ct0.min]; exact (TRB.min_keep fun e => hne (ei1.trans e)).symm)

end

end Fl4ProofsA64.P1
