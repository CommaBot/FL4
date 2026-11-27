-- AArch64 port of Fl4Proofs.P1.TimerRBRmv (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d, TIMER-RB-PLAN stage 8, remove part): `timer::remove` keeps the whole timer invariant `TimerRB`
and leaves `t` unarmed with null links (`timer.remove.rb`): `timer.remove.struct` (stage 6) with the fixup
discharged by `timer.remove_fixup.rb` (stage 7, initial state `rf_init`), the red-removal case balanced by
`del_red_bal`, `t`'s clearing (`clrT`) missing the new tree (`t` is no key of it), `TIMER_MIN` the new
leftmost key, the other cores framed (`CoreTree.keep`, write footprint `XFoot` with `X` = the old keys of
`t`'s core).  `timer.insert.rb_full`: `timer.insert.rb` with `remove` discharged.
-/
import Fl4ProofsA64.P1.TimerRBRfxL
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

theorem TRB.Ctx.app_ne_top : ∀ (i : TRB.Ctx) {o : TRB.Ctx}, o ≠ .top → TRB.Ctx.app i o ≠ .top
  | .top, _, h => h
  | .lc _ _ _ _, _, _ => fun e => nomatch e
  | .rc _ _ _ _, _, _ => fun e => nomatch e

/-- Removing a red node (at most one child, or the transplanted successor `y` red): no fixup needed. -/
theorem del_red_bal {ctx : TRB.Ctx} {ct : Bool} {a b : TRB.RBT} {t : U64} {ctxX : TRB.Ctx} {tx : TRB.RBT}
    {m : Nat} (hb : TRB.Bal (ctx.plug (.node ct a t b)) m) (hbl : (ctx.plug (.node ct a t b)).isRed = false)
    (hs : DelShape ctx ct a b ctxX tx true) : ∃ m', TRB.Bal (ctxX.plug tx) m' ∧ (ctxX.plug tx).isRed = false := by
  rcases hs with ⟨rfl, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl, rfl⟩ | ⟨ctx2, cy, y, hL, -, rfl, rfl, rfl⟩
  · obtain ⟨n0, hb0, hc0, -⟩ := TRB.CtxOK.of_bal ctxX hb
    have hne : ctxX ≠ .top := by
      rintro rfl; exact absurd hbl (by simp [TRB.Ctx.plug, TRB.RBT.isRed])
    cases hb0 with
    | red hl hr _ br =>
      cases hl
      exact ⟨_, TRB.plug_bal hc0 hr (fun e => by rw [br] at e; cases e),
        by rw [TRB.Ctx.plug_isRed ctxX hne tx (.node true .leaf t tx)]; exact hbl⟩
  · obtain ⟨n0, hb0, hc0, -⟩ := TRB.CtxOK.of_bal ctxX hb
    have hne : ctxX ≠ .top := by
      rintro rfl; exact absurd hbl (by simp [TRB.Ctx.plug, TRB.RBT.isRed])
    cases hb0 with
    | red hl hr bl _ =>
      cases hr
      exact ⟨_, TRB.plug_bal hc0 hl (fun e => by rw [bl] at e; cases e),
        by rw [TRB.Ctx.plug_isRed ctxX hne tx (.node true tx t .leaf)]; exact hbl⟩
  · obtain ⟨n1, hb1, hc1, hr1⟩ := TRB.CtxOK.of_bal ctx hb
    have hb1' : TRB.Bal (.node ct a y (ctx2.plug (.node true .leaf y tx))) n1 := by
      cases hb1 with
      | red h1 h2 h3 h4 => exact .red h1 h2 h3 h4
      | black h1 h2 => exact .black h1 h2
    have hW' := TRB.plug_bal hc1 hb1' hr1
    have e : ctx.plug (.node ct a y (ctx2.plug (.node true .leaf y tx))) =
        (TRB.Ctx.app ctx2 (.rc ct a y ctx)).plug (.node true .leaf y tx) :=
      (TRB.Ctx.plug_app ctx2 (.rc ct a y ctx) _).symm
    rw [e] at hW'
    obtain ⟨n0, hb0, hc0, -⟩ := TRB.CtxOK.of_bal _ hW'
    have hne : TRB.Ctx.app ctx2 (.rc ct a y ctx) ≠ .top := TRB.Ctx.app_ne_top ctx2 (fun e => nomatch e)
    cases hb0 with
    | red hl hr _ br =>
      cases hl
      refine ⟨_, TRB.plug_bal hc0 hr (fun e => by rw [br] at e; cases e), ?_⟩
      rw [TRB.Ctx.plug_isRed _ hne tx (.node true .leaf y tx), ← e, ← TRB.plug_isRed_key ctx ct a _ t y]
      exact hbl

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Cs : Set U64}

theorem wi_fix_td {s0 s : S} {c : U64} {Ks : List U64} (hT : TcbPlaced T) (hk : ∀ y ∈ Ks, y ∈ T)
    (hN : NodePlaced st T s0 c) (w : WritesIn st s0 s (FixFoot st s0 c Ks)) {y : U64} (hy : y ∈ T) :
    L.mem s (tdA y) = L.mem s0 (tdA y) := by
  have ha := tz_aligned hT (Tz.of_mem hy) (K := 3528#u64) (by simp) (by simp)
  refine w.mem_eq ha fun hf => ?_
  rcases hf with ⟨z, hz', e | e | e | e⟩ | e
  · exact tz_ne hT (Tz.of_mem hy) (hz'.imp_right (hk z)) (K1 := 3528#u64) (K2 := 3544#u64) (by simp) (by simp)
      (by simp) (congrArg UScalar.val e)
  · exact tz_ne hT (Tz.of_mem hy) (hz'.imp_right (hk z)) (K1 := 3528#u64) (K2 := 3552#u64) (by simp) (by simp)
      (by simp) (congrArg UScalar.val e)
  · exact tz_ne hT (Tz.of_mem hy) (hz'.imp_right (hk z)) (K1 := 3528#u64) (K2 := 3560#u64) (by simp) (by simp)
      (by simp) (congrArg UScalar.val e)
  · exact tz_ne hT (Tz.of_mem hy) (hz'.imp_right (hk z)) (K1 := 3528#u64) (K2 := 3568#u64) (by simp) (by simp)
      (by simp) (congrArg UScalar.val e)
  · exact node_ne_tz hT hN (o := layout.node.TIMER_ROOT) (by rw [timer_root_val]; simp) (Tz.of_mem hy)
      (K := 3528#u64) (by simp) (congrArg UScalar.val e).symm

theorem wi_fix_min {s0 s : S} {c : U64} {Ks : List U64} (hT : TcbPlaced T) (hk : ∀ y ∈ Ks, y ∈ T)
    (hN : NodePlaced st T s0 c) (w : WritesIn st s0 s (FixFoot st s0 c Ks)) :
    L.mem s (L.nodeAt s c layout.node.TIMER_MIN) = L.mem s0 (L.nodeAt s0 c layout.node.TIMER_MIN) := by
  rw [nodeAt_of_ksb w.1]
  have ho : layout.node.TIMER_MIN.val < 4288 := by rw [timer_min_val]; simp
  have ha := nodeAt_aligned hN (off := layout.node.TIMER_MIN) ho (by rw [timer_min_val])
  refine w.mem_eq ha fun hf => ?_
  rcases hf with ⟨z, hz', e | e | e | e⟩ | e
  · exact node_ne_tz hT hN ho (hz'.imp_right (hk z)) (K := 3544#u64) (by simp) (congrArg UScalar.val e)
  · exact node_ne_tz hT hN ho (hz'.imp_right (hk z)) (K := 3552#u64) (by simp) (congrArg UScalar.val e)
  · exact node_ne_tz hT hN ho (hz'.imp_right (hk z)) (K := 3560#u64) (by simp) (congrArg UScalar.val e)
  · exact node_ne_tz hT hN ho (hz'.imp_right (hk z)) (K := 3568#u64) (by simp) (congrArg UScalar.val e)
  · have := congrArg UScalar.val e
    rw [nodeAt_val hN ho, nodeAt_val hN (by rw [timer_root_val]; simp), timer_min_val, timer_root_val] at this
    omega

/-- `remove`'s clearing writes only `t`'s words. -/
theorem clrT_wi (s : S) {t : U64} (hT : TcbPlaced T) (ht : t ∈ T) :
    WritesIn st s (clrT st s t) (fun w => ∃ K : U64, K.val < 4096 ∧ w = core.num.U64.wrapping_add t K) := by
  have a := fun (K : U64) (h1 : K.val < 4096) (h2 : K.val % 8 = 0) => tz_aligned hT (Tz.of_mem ht) h1 h2
  have w := ((((writesIn_wr (st := st) (s := s) (v := 0#u64) (a (3560#u64) (by simp) (by simp))).trans
    (writesIn_wr (v := 0#u64) (a (3544#u64) (by simp) (by simp)))).trans
    (writesIn_wr (v := 0#u64) (a (3552#u64) (by simp) (by simp)))).trans
    (writesIn_wr (v := 0#u64) (a (3528#u64) (by simp) (by simp)))).trans
    (writesIn_wr (v := 0#u64) (a (3568#u64) (by simp) (by simp)))
  refine w.mono fun b hb => ?_
  rcases hb with (((e | e) | e) | e) | e
  · exact ⟨3560#u64, by simp, e⟩
  · exact ⟨3544#u64, by simp, e⟩
  · exact ⟨3552#u64, by simp, e⟩
  · exact ⟨3528#u64, by simp, e⟩
  · exact ⟨3568#u64, by simp, e⟩

/-- After the clearing, `t` is unarmed with null links. -/
theorem clrT_t (s : S) {t : U64} (hT : TcbPlaced T) (ht : t ∈ T) :
    L.mem (clrT st s t) (tdA t) = 0#u64 ∧ L.mem (clrT st s t) (tlA t) = 0#u64 ∧
      L.mem (clrT st s t) (trA t) = 0#u64 ∧ L.mem (clrT st s t) (tpA t) = 0#u64 := by
  simp only [clrT, tdA, tlA, trA, tpA, thA]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [trb_fld_wr hT ht ht (by simp) (by simp) (by simp) (by simp), if_neg (by simp),
      trb_fld_wr hT ht ht (by simp) (by simp) (by simp) (by simp), if_pos ⟨rfl, rfl⟩]
  · rw [trb_fld_wr hT ht ht (by simp) (by simp) (by simp) (by simp), if_neg (by simp),
      trb_fld_wr hT ht ht (by simp) (by simp) (by simp) (by simp), if_neg (by simp),
      trb_fld_wr hT ht ht (by simp) (by simp) (by simp) (by simp), if_neg (by simp),
      trb_fld_wr hT ht ht (by simp) (by simp) (by simp) (by simp), if_pos ⟨rfl, rfl⟩]
  · rw [trb_fld_wr hT ht ht (by simp) (by simp) (by simp) (by simp), if_neg (by simp),
      trb_fld_wr hT ht ht (by simp) (by simp) (by simp) (by simp), if_neg (by simp),
      trb_fld_wr hT ht ht (by simp) (by simp) (by simp) (by simp), if_pos ⟨rfl, rfl⟩]
  · rw [trb_fld_wr hT ht ht (by simp) (by simp) (by simp) (by simp), if_neg (by simp),
      trb_fld_wr hT ht ht (by simp) (by simp) (by simp) (by simp), if_neg (by simp),
      trb_fld_wr hT ht ht (by simp) (by simp) (by simp) (by simp), if_neg (by simp),
      trb_fld_wr hT ht ht (by simp) (by simp) (by simp) (by simp), if_neg (by simp),
      L.mem_wr_same (tz_aligned hT (Tz.of_mem ht) (K := 3560#u64) (by simp) (by simp))]

/-- The fixup's post as `remove.struct` needs it (it may not depend on the core: the core is `t`'s). -/
def RmQ (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) (t : U64) (s7 s8 : S) : Prop :=
  ∀ c W0, (L.mem s (thA t)).val >>> 8 = c.val →
    TRB.Rep (lk st s7) 0#u64 (L.mem s7 (L.nodeAt s7 c layout.node.TIMER_ROOT)) W0 →
    ∃ W' m, FB st T s7 c W0.keys s8 W' ∧ TRB.Bal W' m ∧ W'.isRed = false

theorem delKeys_sub (ctx : TRB.Ctx) (ct : Bool) (a b : TRB.RBT) (t : U64) :
    (TRB.delKeys ctx a b).Sublist (ctx.plug (.node ct a t b)).keys := by
  rw [TRB.delKeys_eq, TRB.plug_t_keys]
  exact (List.Sublist.refl _).append (List.sublist_cons_self t _)

theorem delKeys_mem {ctx : TRB.Ctx} {ct : Bool} {a b : TRB.RBT} {t y : U64}
    (hy : y ∈ (ctx.plug (.node ct a t b)).keys) (hne : y ≠ t) : y ∈ TRB.delKeys ctx a b := by
  rw [TRB.plug_t_keys] at hy
  rw [TRB.delKeys_eq]
  simp only [List.mem_append, List.mem_cons] at hy ⊢
  rcases hy with h | h | h
  · exact Or.inl h
  · exact absurd h hne
  · exact Or.inr h

theorem delKeys_not {ctx : TRB.Ctx} {ct : Bool} {a b : TRB.RBT} {t : U64}
    (hd : (ctx.plug (.node ct a t b)).keys.Nodup) : t ∉ TRB.delKeys ctx a b := by
  rw [TRB.plug_t_keys] at hd
  rw [TRB.delKeys_eq]
  exact (List.nodup_cons.1 (List.nodup_middle.1 hd)).1

/-- **`timer::remove` keeps `TimerRB`** (stage 8, remove part): afterwards `t` is unarmed (so, by `TimerRB`,
its links are null and no timer word names it, `TimerRB.no_link`), the cores' nodes stay placed, and the
writes are `t`'s words, the words of the other keys of `t`'s core's tree and that core's node words. -/
theorem timer.remove.rb (s : S) (t : U64) (hT : TcbPlaced T) (ht : t ∈ T) (hR : TimerRB st T Cs s)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) :
    timer.remove st s t ⦃ s' => TimerRB st T Cs s' ∧ L.mem s' (tdA t) = 0#u64 ∧
      (∀ c ∈ Cs, NodePlaced st T s' c) ∧ ((L.mem s (tdA t) = 0#u64 ∧ s' = s) ∨
        ∃ c ∈ Cs, ∃ W, CoreTree st T s c W ∧ t ∈ W.keys ∧ WritesIn st s s' (XFoot st T s (· ∈ W.keys) c)) ⦄ := by
  have hoM : layout.node.TIMER_MIN.val < 4288 := by rw [timer_min_val]; simp
  have hoM8 : layout.node.TIMER_MIN.val % 8 = 0 := by rw [timer_min_val]
  have hoR : layout.node.TIMER_ROOT.val < 4288 := by rw [timer_root_val]; simp
  have hoR8 : layout.node.TIMER_ROOT.val % 8 = 0 := by rw [timer_root_val]
  refine WP.spec_mono (timer.remove.struct s t (Q := RmQ st T s t) hT ht hR hN ?_) fun s' hs => ?_
  · intro c ctx ct a b s1 ctxX tx rr s7 hc ct0 sh m hrr
    subst hrr
    have htW : t ∈ (ctx.plug (.node ct a t b)).keys := TRB.Ctx.keys_sub ctx _ t (by simp [TRB.RBT.keys])
    obtain ⟨mb, hb⟩ := ct0.bal
    obtain ⟨n, hcx, hdb, hRB, hdep⟩ := rf_init hb ct0.black ct0.height_le sh
    have ek := sh.keys
    have hsub := delKeys_sub ctx ct a b t
    have hd7 : (ctxX.plug tx).keys.Nodup := by rw [ek]; exact ct0.nodup.sublist hsub
    have hk7 : ∀ y ∈ (ctxX.plug tx).keys, y ∈ T := fun y hy => by
      rw [ek] at hy; exact ct0.inT y (hsub.subset hy)
    refine WP.spec_mono (timer.remove_fixup.rb s7 c hT m.np m.rep hd7 hk7 hcx hdb hRB (by omega))
      fun s8 ⟨W', m', hF, hb', hbl'⟩ => ?_
    intro c' W0 hc' hr0
    have ec : c' = c := UScalar.eq_of_val_eq (hc'.symm.trans (ct0.core t htW))
    subst ec
    have e0 := TRB.Rep.det m.rep hr0
    subst e0
    exact ⟨W', m', hF, hb', hbl'⟩
  rcases hs with ⟨h0, rfl⟩ | ⟨c, hc, ctx, ct, a, b, ct0, s1, ctxX, tx, rr, s7, s8, w1, hm1, sh, m, h1, h2, rfl⟩
  · exact ⟨hR, h0, hN, Or.inl ⟨h0, rfl⟩⟩
  have hNc := hN c hc
  have htW : t ∈ (ctx.plug (.node ct a t b)).keys := TRB.Ctx.keys_sub ctx _ t (by simp [TRB.RBT.keys])
  have hsub := delKeys_sub ctx ct a b t
  have hkW : ∀ y ∈ (ctx.plug (.node ct a t b)).keys, y ∈ T := ct0.inT
  -- the state `s1` (after the `TIMER_MIN` write)
  have eb1 : L.nodeBase s1 c = L.nodeBase s c := by simp [LawfulStore.nodeBase, w1.1]
  have hN1 : NodePlaced st T s1 c := ⟨by rw [eb1]; exact hNc.align, by rw [eb1]; exact hNc.fits, by rw [eb1]; exact hNc.disj⟩
  have k1 := KeepOut.of_wi (X := fun _ => False) hT hNc (w1.mono fun b hb => Or.inr ⟨_, hoM, hb⟩)
  -- the tree `W8` before the clearing
  have A : ∃ W8, TRB.Rep (lk st s8) 0#u64 (L.mem s8 (L.nodeAt s8 c layout.node.TIMER_ROOT)) W8 ∧
      W8.keys = TRB.delKeys ctx a b ∧ (∃ m8, TRB.Bal W8 m8) ∧ W8.isRed = false ∧
      WritesIn st s1 s8 (FixFoot st s1 c (ctx.plug (.node ct a t b)).keys) ∧
      (∀ y ∈ T, (L.mem s8 (thA y)).val >>> 8 = (L.mem s1 (thA y)).val >>> 8) ∧ NodePlaced st T s8 c := by
    obtain ⟨mb, hb⟩ := ct0.bal
    cases rr with
    | true =>
      have e8 := h1 rfl
      subst e8
      obtain ⟨m', hb', hbl'⟩ := del_red_bal hb ct0.black sh
      exact ⟨_, m.rep, sh.keys, ⟨m', hb'⟩, hbl', m.wi, m.core, m.np⟩
    | false =>
      obtain ⟨W', m', hF, hb', hbl'⟩ := h2 rfl c _ (ct0.core t htW) m.rep
      refine ⟨W', hF.rep, hF.keys.trans sh.keys, ⟨m', hb'⟩, hbl', ?_, fun y hy => (hF.core y hy).trans (m.core y hy),
        hF.np⟩
      refine (m.wi.trans hF.wi).mono fun w hw => hw.elim id fun hw => ?_
      rcases hw with ⟨z, hz, e⟩ | e
      · refine Or.inl ⟨z, hz.imp_right fun hz => ?_, e⟩
        rw [sh.keys] at hz; exact hsub.subset hz
      · exact Or.inr (by rw [e, nodeAt_of_ksb m.wi.1])
  obtain ⟨W8, rep8, keys8, ⟨m8, bal8⟩, black8, wi18, core18, np8⟩ := A
  -- the clearing
  have wc := clrT_wi (st := st) s8 hT ht
  have kc := KeepOut.of_wi (X := (· = t)) hT np8 (wc.mono fun w ⟨K, hK, e⟩ => (Or.inl ⟨t, Or.inr ⟨ht, rfl⟩, K, hK, e⟩ : XFoot st T s8 (· = t) c w))
  have nodec : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (clrT st s8 t) (L.nodeAt (clrT st s8 t) c o) = L.mem s8 (L.nodeAt s8 c o) := fun o ho ho8 => by
    rw [nodeAt_of_ksb wc.1]
    exact wc.mem_eq (nodeAt_aligned np8 ho ho8) fun ⟨K, hK, e⟩ =>
      node_ne_tz hT np8 ho (Tz.of_mem ht) hK (congrArg UScalar.val e)
  -- the whole footprint
  have hKx : ∀ z ∈ (ctx.plug (.node ct a t b)).keys, z ∈ T ∧ z ∈ (ctx.plug (.node ct a t b)).keys :=
    fun z hz => ⟨hkW z hz, hz⟩
  have wa : WritesIn st s s1 (XFoot st T s (· ∈ (ctx.plug (.node ct a t b)).keys) c) :=
    w1.mono fun w hw => Or.inr ⟨_, hoM, hw⟩
  have wb : WritesIn st s1 s8 (XFoot st T s (· ∈ (ctx.plug (.node ct a t b)).keys) c) :=
    wi18.mono fun w hw => (fixFoot_x hw hKx).ksb w1.1
  have wcc : WritesIn st s8 (clrT st s8 t) (XFoot st T s (· ∈ (ctx.plug (.node ct a t b)).keys) c) :=
    wc.mono fun w ⟨K, hK, e⟩ => Or.inl ⟨t, Or.inr ⟨ht, htW⟩, K, hK, e⟩
  have wall : WritesIn st s (clrT st s8 t) (XFoot st T s (· ∈ (ctx.plug (.node ct a t b)).keys) c) :=
    ((wa.trans wb).trans wcc).mono fun w hw => by rcases hw with (h | h) | h <;> exact h
  have kall := KeepOut.of_wi hT hNc wall
  -- the new tree of `c`
  have tn : t ∉ W8.keys := by rw [keys8]; exact delKeys_not ct0.nodup
  have W8sub : ∀ y ∈ W8.keys, y ∈ (ctx.plug (.node ct a t b)).keys := fun y hy => by
    rw [keys8] at hy; exact hsub.subset hy
  have yne : ∀ y ∈ W8.keys, y ≠ t := fun y hy e => tn (e ▸ hy)
  have fc : ∀ y ∈ W8.keys, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (clrT st s8 t) (core.num.U64.wrapping_add y K) = L.mem s8 (core.num.U64.wrapping_add y K) :=
    fun y hy => kc.fld y (hkW y (W8sub y hy)) (yne y hy)
  have td8 : ∀ y ∈ W8.keys, L.mem (clrT st s8 t) (tdA y) = L.mem s (tdA y) := fun y hy => by
    have hyT := hkW y (W8sub y hy)
    rw [show tdA y = core.num.U64.wrapping_add y 3528#u64 from rfl, fc y hy 3528#u64 (by simp) (by simp),
      ← show tdA y = core.num.U64.wrapping_add y 3528#u64 from rfl, wi_fix_td hT hkW hN1 wi18 hyT]
    exact k1.fld y hyT id 3528#u64 (by simp) (by simp)
  have ct8 : CoreTree st T (clrT st s8 t) c W8 := by
    refine ⟨?_, by rw [keys8]; exact ct0.nodup.sublist hsub, fun y hy => hkW y (W8sub y hy),
      fun y hy => by rw [td8 y hy]; exact ct0.armed y (W8sub y hy), fun y hy => ?_, ?_, ⟨m8, bal8⟩, black8, ?_⟩
    · rw [nodec _ hoR hoR8]
      refine rep8.congr fun y hy => ⟨fc y hy 3544#u64 (by simp) (by simp), fc y hy 3552#u64 (by simp) (by simp),
        fc y hy 3560#u64 (by simp) (by simp), ?_⟩
      show ((L.mem (clrT st s8 t) (thA y) &&& 1#u64) != 0#u64) = ((L.mem s8 (thA y) &&& 1#u64) != 0#u64)
      rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, fc y hy 3568#u64 (by simp) (by simp)]
    · have hyT := hkW y (W8sub y hy)
      rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, fc y hy 3568#u64 (by simp) (by simp),
        ← show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, core18 y hyT,
        show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, k1.fld y hyT id 3568#u64 (by simp) (by simp)]
      exact ct0.core y (W8sub y hy)
    · have hsub8 : W8.keys.Sublist (ctx.plug (.node ct a t b)).keys := by rw [keys8]; exact hsub
      have hs := ct0.sorted.sublist hsub8
      exact hs.imp_of_mem fun ha hb hab => by rw [td8 _ ha, td8 _ hb]; exact hab
    · rw [nodec _ hoM hoM8, wi_fix_min hT hkW hN1 wi18, hm1]
      unfold TRB.RBT.minKey; rw [keys8]
  -- other cores
  have oth : ∀ c' ∈ Cs, c' ≠ c → ∀ tc, CoreTree st T s c' tc → CoreTree st T (clrT st s8 t) c' tc :=
    fun c' hcC hne tc ctc => ctc.keep kall (hN c' hcC) hne fun y hy ho =>
      hne (UScalar.eq_of_val_eq ((ctc.core y hy).symm.trans (ct0.core y ho)))
  have htd' := (clrT_t (st := st) s8 hT ht).1
  refine ⟨⟨fun c' hcC => ?_, fun y hy hdy => ?_, fun y hy hdy => ?_⟩, htd', fun c' hcC => ?_,
    Or.inr ⟨c, hc, _, ct0, htW, wall⟩⟩
  · by_cases e : c' = c
    · subst e; exact ⟨W8, ct8⟩
    · obtain ⟨tc, ctc⟩ := hR.tree c' hcC
      exact ⟨tc, oth c' hcC e tc ctc⟩
  · by_cases hX : y ∈ (ctx.plug (.node ct a t b)).keys
    · by_cases ey : y = t
      · subst ey; exact absurd htd' hdy
      · exact ⟨c, hc, W8, ct8, by rw [keys8]; exact delKeys_mem hX ey⟩
    · have e : L.mem (clrT st s8 t) (tdA y) = L.mem s (tdA y) := kall.fld y hy hX 3528#u64 (by simp) (by simp)
      rw [e] at hdy
      obtain ⟨c', hcC, tc, ctc, hyc⟩ := hR.armed y hy hdy
      by_cases ec : c' = c
      · subst ec
        rw [ctc.uniq ct0] at hyc
        exact absurd hyc hX
      · exact ⟨c', hcC, tc, oth c' hcC ec tc ctc, hyc⟩
  · by_cases ey : y = t
    · subst ey
      obtain ⟨-, a1, a2, a3⟩ := clrT_t (st := st) s8 hT ht
      exact ⟨a1, a2, a3⟩
    · by_cases hX : y ∈ (ctx.plug (.node ct a t b)).keys
      · exact absurd hdy (ct8.armed y (by rw [keys8]; exact delKeys_mem hX ey))
      · have e : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
            L.mem (clrT st s8 t) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
          kall.fld y hy hX
        have e0 : L.mem (clrT st s8 t) (tdA y) = L.mem s (tdA y) := e 3528#u64 (by simp) (by simp)
        rw [e0] at hdy
        obtain ⟨a1, a2, a3⟩ := hR.idle y hy hdy
        exact ⟨(e 3544#u64 (by simp) (by simp)).trans a1, (e 3552#u64 (by simp) (by simp)).trans a2,
          (e 3560#u64 (by simp) (by simp)).trans a3⟩
  · have e : L.nodeBase (clrT st s8 t) c' = L.nodeBase s c' := by simp [LawfulStore.nodeBase, wall.1]
    exact ⟨by rw [e]; exact (hN c' hcC).align, by rw [e]; exact (hN c' hcC).fits, by rw [e]; exact (hN c' hcC).disj⟩

/-- **`timer::insert` keeps `TimerRB`**, `remove` discharged by `timer.remove.rb`: for `d ≠ 0`, `t` is a
node of the current core's tree afterwards. -/
theorem timer.insert.rb_full (s : S) (t d bd : U64) (hT : TcbPlaced T) (ht : t ∈ T) (hR : TimerRB st T Cs s)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hcpu : L.cpu s ∈ Cs) :
    timer.insert st s t d bd ⦃ s' => TimerRB st T Cs s' ∧
      (d ≠ 0#u64 → ∃ W, CoreTree st T s' (L.cpu s) W ∧ t ∈ W.keys) ⦄ := by
  have hrem := timer.remove.rb s t hT ht hR hN
  refine WP.spec_mono (timer.insert.rb s t d bd hT ht hrem fun s1 ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, ?_, h3⟩)
    fun s' ⟨hR', hs⟩ => ⟨hR', fun hd => ?_⟩
  · rcases h4 with ⟨-, rfl⟩ | ⟨c, -, W, -, -, w⟩
    · exact hcpu
    · rw [w.2.1]; exact hcpu
  · rcases hs with ⟨hd0, -⟩ | ⟨-, s1, ⟨-, -, -, h4⟩, W, ctW, htW⟩
    · exact absurd hd0 hd
    · have e : L.cpu s1 = L.cpu s := by
        rcases h4 with ⟨-, rfl⟩ | ⟨c, -, W, -, -, w⟩
        · rfl
        · exact w.2.1
      rw [e] at ctW
      exact ⟨W, ctW, htW⟩

end

end Fl4ProofsA64.P1
