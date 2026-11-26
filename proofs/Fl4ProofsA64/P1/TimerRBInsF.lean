-- AArch64 port of Fl4Proofs.P1.TimerRBInsF (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d, TIMER-RB-PLAN stage 8, insert part): `timer::insert` keeps the whole timer invariant `TimerRB`.
`XFoot T s0 X C` is a write footprint "words of the TCBs satisfying `X` (or of the null TCB) and node words
of core `C`"; `KeepOut` is what it leaves unchanged, and `CoreTree.keep` frames a core's tree through it
when the tree's keys miss `X` and the core is not `C`.  `timer.insert.coreW` is `timer.insert.core` with
the footprint (`X` = `t` and the current core's old keys), and `timer.insert.rb` the composition: other
cores' trees share no key with the current one (a key's core bits name its core), so they are framed;
armed TCBs are in some tree; unarmed ones keep their null links.  `remove`'s spec is a hypothesis.
-/
import Fl4ProofsA64.P1.TimerRBInsC
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Cs : Set U64}

/-- Words of the TCBs satisfying `X` (or of the null TCB `0`) and the node words of core `C`. -/
def XFoot (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (X : U64 → Prop) (C : U64)
    (w : U64) : Prop :=
  (∃ z, (z = 0#u64 ∨ (z ∈ T ∧ X z)) ∧ ∃ K : U64, K.val < 4096 ∧ w = core.num.U64.wrapping_add z K) ∨
    (∃ o : U64, o.val < 4288 ∧ w = L.nodeAt s0 C o)

theorem XFoot.ksb {s0 s1 : S} {X : U64 → Prop} {C w : U64} (e : L.ksb s1 = L.ksb s0)
    (h : XFoot st T s1 X C w) : XFoot st T s0 X C w := by
  rcases h with h | ⟨o, ho, e'⟩
  · exact Or.inl h
  · exact Or.inr ⟨o, ho, by rw [e', nodeAt_of_ksb e]⟩

theorem XFoot.mono {s0 : S} {X X' : U64 → Prop} {C w : U64} (hX : ∀ y ∈ T, X y → X' y)
    (h : XFoot st T s0 X C w) : XFoot st T s0 X' C w := by
  rcases h with ⟨z, hz, K, hK, e⟩ | h
  · exact Or.inl ⟨z, hz.imp_right fun h => ⟨h.1, hX z h.1 h.2⟩, K, hK, e⟩
  · exact Or.inr h

theorem xfoot_fld {s0 : S} {X : U64 → Prop} {C y K : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s0 C)
    (hy : y ∈ T) (hX : ¬ X y) (hK : K.val < 4096) : ¬ XFoot st T s0 X C (core.num.U64.wrapping_add y K) := by
  have hy0 : y ≠ 0#u64 := fun e => (hT y hy).ne0 (by rw [e]; rfl)
  rintro (⟨z, hz, K', hK', e⟩ | ⟨o, ho, e⟩)
  · have hzT : Tz T z := hz.imp_right And.left
    by_cases hk : K.val = K'.val
    · rw [show K' = K from UScalar.eq_of_val_eq hk.symm] at e
      have ez := tz_inj hT (Tz.of_mem hy) hzT hK (congrArg UScalar.val e)
      subst ez
      rcases hz with hz | hz
      · exact hy0 hz
      · exact hX hz.2
    · exact tz_ne hT (Tz.of_mem hy) hzT hK hK' hk (congrArg UScalar.val e)
  · exact node_ne_tz hT hN ho (Tz.of_mem hy) hK (congrArg UScalar.val e).symm

theorem xfoot_node {s0 : S} {X : U64 → Prop} {C c o : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s0 C)
    (hNc : NodePlaced st T s0 c) (hc : c ≠ C) (ho : o.val < 4288) : ¬ XFoot st T s0 X C (L.nodeAt s0 c o) := by
  rintro (⟨z, hz, K', hK', e⟩ | ⟨o', ho', e⟩)
  · exact node_ne_tz hT hNc ho (hz.imp_right And.left) hK' (congrArg UScalar.val e)
  · exact node_ne_node hNc hN ho ho' (fun e => absurd e hc) (congrArg UScalar.val e)

/-- Between `s` and `s'` only words of the TCBs satisfying `X` and node words of core `C` changed. -/
structure KeepOut (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s s' : S) (X : U64 → Prop)
    (C : U64) : Prop where
  ksb : L.ksb s' = L.ksb s
  fld : ∀ y ∈ T, ¬ X y → ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
    L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)
  node : ∀ c, NodePlaced st T s c → c ≠ C → ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
    L.mem s' (L.nodeAt s' c o) = L.mem s (L.nodeAt s c o)

theorem KeepOut.of_wi {s s' : S} {X : U64 → Prop} {C : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s C)
    (w : WritesIn st s s' (XFoot st T s X C)) : KeepOut st T s s' X C :=
  ⟨w.1, fun y hy hX K hK hK8 => w.mem_eq (tz_aligned hT (Tz.of_mem hy) hK hK8) (xfoot_fld hT hN hy hX hK),
    fun c hNc hc o ho ho8 => by
      rw [nodeAt_of_ksb w.1]
      exact w.mem_eq (nodeAt_aligned hNc ho ho8) (xfoot_node hT hN hNc hc ho)⟩

/-- **Frame of one core's tree** through a step that writes only words of `X`-TCBs and of another core. -/
theorem CoreTree.keep {s s' : S} {X : U64 → Prop} {C c : U64} {t : TRB.RBT} (h : CoreTree st T s c t)
    (k : KeepOut st T s s' X C) (hN : NodePlaced st T s c) (hc : c ≠ C) (hX : ∀ y ∈ t.keys, ¬ X y) :
    CoreTree st T s' c t := by
  have kT := h.inT
  have f : ∀ y ∈ t.keys, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy => k.fld y (kT y hy) (hX y hy)
  have td : ∀ y ∈ t.keys, L.mem s' (tdA y) = L.mem s (tdA y) := fun y hy => f y hy 3528#u64 (by simp) (by simp)
  have th : ∀ y ∈ t.keys, L.mem s' (thA y) = L.mem s (thA y) := fun y hy => f y hy 3568#u64 (by simp) (by simp)
  refine ⟨?_, h.nodup, h.inT, fun y hy => by rw [td y hy]; exact h.armed y hy,
    fun y hy => by rw [th y hy]; exact h.core y hy, ?_, h.bal, h.black, ?_⟩
  · rw [k.node c hN hc _ (by rw [timer_root_val]; simp) (by rw [timer_root_val])]
    refine h.rep.congr fun y hy => ⟨f y hy 3544#u64 (by simp) (by simp), f y hy 3552#u64 (by simp) (by simp),
      f y hy 3560#u64 (by simp) (by simp), ?_⟩
    show ((L.mem s' (thA y) &&& 1#u64) != 0#u64) = ((L.mem s (thA y) &&& 1#u64) != 0#u64)
    rw [th y hy]
  · exact h.sorted.imp_of_mem fun ha hb hab => by rw [td _ ha, td _ hb]; exact hab
  · rw [k.node c hN hc _ (by rw [timer_min_val]; simp) (by rw [timer_min_val])]; exact h.min

theorem insFoot_x {s1 : S} {c t p : U64} {X : U64 → Prop} (hp : p = 0#u64 ∨ (p ∈ T ∧ X p)) (hXt : X t)
    (htT : t ∈ T) {w : U64} (hw : InsFoot st s1 c t p w) : XFoot st T s1 X c w := by
  rcases hw with ⟨K, -, h2, e⟩ | e | e | e
  · exact Or.inl ⟨t, Or.inr ⟨htT, hXt⟩, K, by omega, e⟩
  · exact Or.inl ⟨p, hp, 3544#u64, by simp, e⟩
  · exact Or.inl ⟨p, hp, 3552#u64, by simp, e⟩
  · exact Or.inr ⟨_, by rw [timer_root_val]; simp, e⟩

theorem fixFoot_x {s0 : S} {c : U64} {Ks : List U64} {X : U64 → Prop} {w : U64} (hw : FixFoot st s0 c Ks w)
    (hK : ∀ z ∈ Ks, z ∈ T ∧ X z) : XFoot st T s0 X c w := by
  rcases hw with ⟨z, hz, e | e | e | e⟩ | e
  · exact Or.inl ⟨z, hz.imp_right (hK z), 3544#u64, by simp, e⟩
  · exact Or.inl ⟨z, hz.imp_right (hK z), 3552#u64, by simp, e⟩
  · exact Or.inl ⟨z, hz.imp_right (hK z), 3560#u64, by simp, e⟩
  · exact Or.inl ⟨z, hz.imp_right (hK z), 3568#u64, by simp, e⟩
  · exact Or.inr ⟨_, by rw [timer_root_val]; simp, e⟩

theorem wi_node_x {s0 s : S} {X : U64 → Prop} {c o v : U64} (e : L.ksb s = L.ksb s0) (hN : NodePlaced st T s c)
    (ho : o.val < 4288) (ho8 : o.val % 8 = 0) :
    WritesIn st s (L.wr s (L.nodeAt s c o) v) (XFoot st T s0 X c) :=
  (writesIn_wr (nodeAt_aligned hN ho ho8)).mono fun w hw => Or.inr ⟨o, ho, by rw [hw, nodeAt_of_ksb e]⟩

/-- The TCBs `insert` may write: `t` and the current core's old keys. -/
def InsX (ctx : TRB.Ctx) (t : U64) (y : U64) : Prop := y = t ∨ y ∈ (ctx.plug .leaf).keys

/-- `timer.insert.core` with its write footprint: from the state `s1` after `remove`, only the words of `t`,
of the current core's old keys and the current core's node words are written. -/
theorem timer.insert.coreW (s : S) (t d bd : U64) {P : S → Prop} (hT : TcbPlaced T) (ht : t ∈ T)
    (hrem : timer.remove st s t ⦃ s1 => P s1 ⦄)
    (hP : ∀ s1, P s1 → NodePlaced st T s1 (L.cpu s1) ∧ ∃ t0, CoreTree st T s1 (L.cpu s1) t0 ∧ t ∉ t0.keys) :
    timer.insert st s t d bd ⦃ s' => (d = 0#u64 ∧ P s') ∨
      (d ≠ 0#u64 ∧ ∃ (s1 : S) (ctx : TRB.Ctx) (W : TRB.RBT), P s1 ∧ CoreTree st T s1 (L.cpu s1) (ctx.plug .leaf) ∧
        CoreTree st T s' (L.cpu s1) W ∧ W.keys = ctx.pre ++ t :: ctx.post ∧
        WritesIn st s1 s' (XFoot st T s1 (InsX ctx t) (L.cpu s1))) ⦄ := by
  have hfix : ∀ s1 s8 ctx, P s1 → InsMid st T s1 s8 (L.cpu s1) t d ctx →
      timer.insert_fixup st s8 (L.cpu s1) t ⦃ s9 => ∃ W0 W n,
        TRB.Rep (lk st s8) 0#u64 (L.mem s8 (L.nodeAt s8 (L.cpu s8) layout.node.TIMER_ROOT)) W0 ∧
        FB st T s8 (L.cpu s8) W0.keys s9 W ∧ TRB.Bal W n ∧ W.isRed = false ⦄ := by
    intro s1 s8 ctx _ hm
    have ec : L.cpu s8 = L.cpu s1 := hm.wi.2.1
    obtain ⟨m, hb⟩ := hm.old.bal
    refine WP.spec_mono (timer.insert_fixup.rb s8 (L.cpu s1) t hT hm.np hm.rep hb hm.old.black hm.nodup hm.inT)
      fun s9 ⟨W, n, hF, hbW, hbl⟩ => ⟨_, W, n, by rw [ec]; exact hm.rep, by rw [ec]; exact hF, hbW, hbl⟩
  refine WP.spec_mono (timer.insert.attach (T := T) s t d bd (Q := fun s8 s9 => ∃ W0 W n,
      TRB.Rep (lk st s8) 0#u64 (L.mem s8 (L.nodeAt s8 (L.cpu s8) layout.node.TIMER_ROOT)) W0 ∧
      FB st T s8 (L.cpu s8) W0.keys s9 W ∧ TRB.Bal W n ∧ W.isRed = false) hT ht hrem hP hfix) fun s' hs => ?_
  rcases hs with h0 | ⟨hd0, s1, s8, ctx, s9, h1, hm, ⟨W0, W, n, hr0, hF, hb, hbl⟩, hfst, hnfst⟩
  · exact Or.inl h0
  have ec : L.cpu s8 = L.cpu s1 := hm.wi.2.1
  rw [ec] at hr0 hF
  have e0 := TRB.Rep.det hm.rep hr0
  subst e0
  -- the footprint up to the fixup's end
  have hKs : ∀ z ∈ (ctx.plug (.node true .leaf t .leaf)).keys, z ∈ T ∧ InsX ctx t z :=
    fun z hz => ⟨hm.inT z hz, (hm.keys_iff z).1 hz⟩
  have hpar : ctx.par = 0#u64 ∨ (ctx.par ∈ T ∧ InsX ctx t ctx.par) := by
    obtain ⟨-, -, mpk, -, -, -, -⟩ := TRB.mid_facts hm.old.rep hm.old.nodup
    by_cases et : ctx = .top
    · subst et; exact Or.inl rfl
    · exact Or.inr ⟨hm.old.inT _ (mpk et), Or.inr (mpk et)⟩
  have w12 : WritesIn st s1 s9 (XFoot st T s1 (InsX ctx t) (L.cpu s1)) :=
    (hm.wi.trans hF.wi).mono fun w hw =>
      hw.elim (insFoot_x hpar (Or.inl rfl) hm.tT) fun hw => (fixFoot_x hw hKs).ksb hm.wi.1
  have ek9 : L.ksb s9 = L.ksb s1 := hF.wi.1.trans hm.wi.1
  have emk : W.minKey = (ctx.plug (.node true .leaf t .leaf)).minKey := by
    unfold TRB.RBT.minKey; rw [hF.keys]
  have hN9 : NodePlaced st T s9 (L.cpu s1) := hF.np
  have hmin9 : L.mem s9 (L.nodeAt s9 (L.cpu s1) layout.node.TIMER_MIN) =
      L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) :=
    (hF.min hT hm.inT hm.np).trans (hm.min_old hT)
  by_cases hp : ctx.pre = []
  · have es := hfst hp
    subst es
    have hoM : layout.node.TIMER_MIN.val < 4288 := by rw [timer_min_val]; simp
    have hoM8 : layout.node.TIMER_MIN.val % 8 = 0 := by rw [timer_min_val]
    have hoR : layout.node.TIMER_ROOT.val < 4288 := by rw [timer_root_val]; simp
    have hoR8 : layout.node.TIMER_ROOT.val % 8 = 0 := by rw [timer_root_val]
    have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
    have hoP : layout.node.REPROGRAM.val < 4288 := by rw [rp]; simp
    have hoP8 : layout.node.REPROGRAM.val % 8 = 0 := by rw [rp]
    have hN9' : NodePlaced st T (L.wr s9 (L.nodeAt s9 (L.cpu s1) layout.node.TIMER_MIN) t) (L.cpu s1) := hN9.wr
    refine Or.inr ⟨hd0, s1, ctx, W, h1, hm.old, ?_, by rw [hF.keys, TRB.attach_keys], ?_⟩
    · refine CoreTree.of_fix hT hm hd0 hF hb hbl (fun K h1 h2 y hy => ?_) ?_ ?_
      · rw [trb_fld_wr_node hT hN9' hoP hoP8 hy h1 h2, trb_fld_wr_node hT hN9 hoM hoM8 hy h1 h2]
      · rw [node_wr_ne hN9' hoP hoP8 hoR hoR8 (by rw [rp, timer_root_val]; simp),
          node_wr_ne hN9 hoM hoM8 hoR hoR8 (by rw [timer_min_val, timer_root_val]; simp)]
      · rw [node_wr_ne hN9' hoP hoP8 hoM hoM8 (by rw [rp, timer_min_val]; simp), node_wr_eq hN9 hoM hoM8, emk,
          TRB.attach_min, if_pos hp]
    · exact ((w12.trans (wi_node_x ek9 hN9 hoM hoM8)).trans
        (wi_node_x ((L.ksb_wr _ _ _).trans ek9) hN9' hoP hoP8)).mono fun w hw =>
          hw.elim (fun hw => hw.elim id id) id
  · have es := hnfst hp
    subst es
    refine Or.inr ⟨hd0, s1, ctx, W, h1, hm.old, ?_, by rw [hF.keys, TRB.attach_keys], w12⟩
    refine CoreTree.of_fix hT hm hd0 hF hb hbl (fun _ _ _ _ _ => rfl) rfl ?_
    rw [hmin9, hm.old.min, emk, TRB.attach_min, if_neg hp]

/-- **`timer::insert` keeps `TimerRB`** (stage 8, insert part), given what `remove` leaves (`P`: `TimerRB`
with `t` unarmed, the current core one of `Cs`, the cores' nodes placed).  For `d ≠ 0`, `t` is a node of
the current core's tree afterwards. -/
theorem timer.insert.rb (s : S) (t d bd : U64) {P : S → Prop} (hT : TcbPlaced T) (ht : t ∈ T)
    (hrem : timer.remove st s t ⦃ s1 => P s1 ⦄)
    (hP : ∀ s1, P s1 → TimerRB st T Cs s1 ∧ L.mem s1 (tdA t) = 0#u64 ∧ L.cpu s1 ∈ Cs ∧
      ∀ c ∈ Cs, NodePlaced st T s1 c) :
    timer.insert st s t d bd ⦃ s' => TimerRB st T Cs s' ∧ ((d = 0#u64 ∧ P s') ∨
      (d ≠ 0#u64 ∧ ∃ s1, P s1 ∧ ∃ W, CoreTree st T s' (L.cpu s1) W ∧ t ∈ W.keys)) ⦄ := by
  refine WP.spec_mono (timer.insert.coreW s t d bd hT ht hrem fun s1 h1 => ?_) fun s' hs => ?_
  · obtain ⟨hR, htd, hc, hN⟩ := hP s1 h1
    obtain ⟨t0, ct⟩ := hR.tree _ hc
    exact ⟨hN _ hc, t0, ct, fun hm => ct.armed t hm htd⟩
  rcases hs with ⟨hd, h1⟩ | ⟨hd, s1, ctx, W, h1, cto, ctW, eW, wi⟩
  · exact ⟨(hP s' h1).1, Or.inl ⟨hd, h1⟩⟩
  obtain ⟨hR, htd, hc, hN⟩ := hP s1 h1
  have k := KeepOut.of_wi hT (hN _ hc) wi
  have hW : ∀ y, y ∈ W.keys ↔ InsX ctx t y := fun y => by
    rw [eW, InsX, TRB.Ctx.plug_keys]
    simp only [TRB.RBT.keys, List.mem_append, List.mem_cons, List.append_nil, List.not_mem_nil]
    tauto
  have oth : ∀ c ∈ Cs, c ≠ L.cpu s1 → ∀ tc, CoreTree st T s1 c tc → CoreTree st T s' c tc :=
    fun c hcC hne tc ctc => ctc.keep k (hN c hcC) hne fun y hy hX => hX.elim
      (fun e => ctc.armed y hy (by rw [e]; exact htd))
      (fun ho => hne (UScalar.eq_of_val_eq ((ctc.core y hy).symm.trans (cto.core y ho))))
  refine ⟨⟨fun c hcC => ?_, fun y hy hdy => ?_, fun y hy hdy => ?_⟩,
    Or.inr ⟨hd, s1, h1, W, ctW, (hW t).2 (Or.inl rfl)⟩⟩
  · by_cases e : c = L.cpu s1
    · subst e; exact ⟨W, ctW⟩
    · obtain ⟨tc, ctc⟩ := hR.tree c hcC
      exact ⟨tc, oth c hcC e tc ctc⟩
  · by_cases hX : InsX ctx t y
    · exact ⟨L.cpu s1, hc, W, ctW, (hW y).2 hX⟩
    · have e : L.mem s' (tdA y) = L.mem s1 (tdA y) := k.fld y hy hX 3528#u64 (by simp) (by simp)
      rw [e] at hdy
      obtain ⟨c, hcC, tc, ctc, hyc⟩ := hR.armed y hy hdy
      by_cases ec : c = L.cpu s1
      · subst ec
        rw [ctc.uniq cto] at hyc
        exact absurd (Or.inr hyc) hX
      · exact ⟨c, hcC, tc, oth c hcC ec tc ctc, hyc⟩
  · by_cases hX : InsX ctx t y
    · exact absurd hdy (ctW.armed y ((hW y).2 hX))
    · have e : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
          L.mem s' (core.num.U64.wrapping_add y K) = L.mem s1 (core.num.U64.wrapping_add y K) :=
        k.fld y hy hX
      have e0 : L.mem s' (tdA y) = L.mem s1 (tdA y) := e 3528#u64 (by simp) (by simp)
      rw [e0] at hdy
      obtain ⟨a, b, c⟩ := hR.idle y hy hdy
      exact ⟨(e 3544#u64 (by simp) (by simp)).trans a, (e 3552#u64 (by simp) (by simp)).trans b,
        (e 3560#u64 (by simp) (by simp)).trans c⟩

end

end Fl4ProofsA64.P1
