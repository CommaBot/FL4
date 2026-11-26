-- AArch64 port of Fl4Proofs.P1.TimerRBInsC (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d, TIMER-RB-PLAN stages 4+5 composed): `timer::insert` keeps the current core's tree red-black.
After `remove`, the attach (`timer.insert.attach`, `InsMid`) and `insert_fixup` (`timer.insert_fixup.rb`),
the current core's tree is a `CoreTree` over the old keys plus `t` at its in-order place
(`timer.insert.core`): the fixup writes no deadline, no `TIMER_MIN` and keeps the core bits; `TIMER_MIN`
is the leftmost key, rewritten by `insert` exactly when `t` is the new leftmost.
-/
import Fl4ProofsA64.P1.TimerRBFixL
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-- `insert_fixup`'s writes miss the deadline words. -/
theorem FB.td {s0 s : S} {c : U64} {Ks : List U64} {W : TRB.RBT} (hT : TcbPlaced T) (hk : ∀ y ∈ Ks, y ∈ T)
    (hN : NodePlaced st T s0 c) (h : FB st T s0 c Ks s W) {y : U64} (hy : y ∈ T) :
    L.mem s (tdA y) = L.mem s0 (tdA y) := by
  have ha := tz_aligned hT (Tz.of_mem hy) (K := 3528#u64) (by simp) (by simp)
  refine h.wi.mem_eq ha fun hf => ?_
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

/-- `insert_fixup`'s writes miss `TIMER_MIN`. -/
theorem FB.min {s0 s : S} {c : U64} {Ks : List U64} {W : TRB.RBT} (hT : TcbPlaced T) (hk : ∀ y ∈ Ks, y ∈ T)
    (hN : NodePlaced st T s0 c) (h : FB st T s0 c Ks s W) :
    L.mem s (L.nodeAt s c layout.node.TIMER_MIN) = L.mem s0 (L.nodeAt s0 c layout.node.TIMER_MIN) := by
  rw [nodeAt_of_ksb h.wi.1]
  have ho : layout.node.TIMER_MIN.val < 4288 := by rw [timer_min_val]; simp
  have ha := nodeAt_aligned hN (off := layout.node.TIMER_MIN) ho (by rw [timer_min_val])
  refine h.wi.mem_eq ha fun hf => ?_
  rcases hf with ⟨z, hz', e | e | e | e⟩ | e
  · exact node_ne_tz hT hN ho (hz'.imp_right (hk z)) (K := 3544#u64) (by simp) (congrArg UScalar.val e)
  · exact node_ne_tz hT hN ho (hz'.imp_right (hk z)) (K := 3552#u64) (by simp) (congrArg UScalar.val e)
  · exact node_ne_tz hT hN ho (hz'.imp_right (hk z)) (K := 3560#u64) (by simp) (congrArg UScalar.val e)
  · exact node_ne_tz hT hN ho (hz'.imp_right (hk z)) (K := 3568#u64) (by simp) (congrArg UScalar.val e)
  · have := congrArg UScalar.val e
    rw [nodeAt_val hN ho, nodeAt_val hN (by rw [timer_root_val]; simp), timer_min_val, timer_root_val] at this
    omega

theorem InsMid.np1 {s1 s8 : S} {c t d : U64} {ctx : TRB.Ctx} (hm : InsMid st T s1 s8 c t d ctx) :
    NodePlaced st T s1 c := by
  have e : L.nodeBase s8 c = L.nodeBase s1 c := by simp [LawfulStore.nodeBase, hm.wi.1]
  exact ⟨by rw [← e]; exact hm.np.align, by rw [← e]; exact hm.np.fits, by rw [← e]; exact hm.np.disj⟩

theorem InsMid.parT {s1 s8 : S} {c t d : U64} {ctx : TRB.Ctx} (hm : InsMid st T s1 s8 c t d ctx) :
    Tz T ctx.par := by
  obtain ⟨-, -, mpk, -, -, -, -⟩ := TRB.mid_facts hm.old.rep hm.old.nodup
  by_cases et : ctx = .top
  · subst et; exact Tz.zero
  · exact Tz.of_mem (hm.old.inT _ (mpk et))

/-- The attach writes no height word of another TCB. -/
theorem InsMid.th_old {s1 s8 : S} {c t d : U64} {ctx : TRB.Ctx} (hT : TcbPlaced T)
    (hm : InsMid st T s1 s8 c t d ctx) {y : U64} (hy : y ∈ T) (hyt : y ≠ t) :
    L.mem s8 (thA y) = L.mem s1 (thA y) :=
  hm.wi.mem_eq (tz_aligned hT (Tz.of_mem hy) (K := 3568#u64) (by simp) (by simp))
    (insFoot_not hT hm.np1 hm.tT hm.parT hy (K' := 3568#u64) (by simp) hyt (Or.inr ⟨by simp, by simp⟩))

/-- The attach writes no `TIMER_MIN`. -/
theorem InsMid.min_old {s1 s8 : S} {c t d : U64} {ctx : TRB.Ctx} (hT : TcbPlaced T)
    (hm : InsMid st T s1 s8 c t d ctx) :
    L.mem s8 (L.nodeAt s8 c layout.node.TIMER_MIN) = L.mem s1 (L.nodeAt s1 c layout.node.TIMER_MIN) := by
  have hN := hm.np1
  rw [nodeAt_of_ksb hm.wi.1]
  have ho : layout.node.TIMER_MIN.val < 4288 := by rw [timer_min_val]; simp
  refine hm.wi.mem_eq (nodeAt_aligned hN (off := layout.node.TIMER_MIN) ho (by rw [timer_min_val])) fun hf => ?_
  rcases hf with ⟨K, h1, h2, e⟩ | e | e | e
  · exact node_ne_tz hT hN ho (Tz.of_mem hm.tT) (K := K) (by omega) (congrArg UScalar.val e)
  · exact node_ne_tz hT hN ho hm.parT (K := 3544#u64) (by simp) (congrArg UScalar.val e)
  · exact node_ne_tz hT hN ho hm.parT (K := 3552#u64) (by simp) (congrArg UScalar.val e)
  · have := congrArg UScalar.val e
    rw [nodeAt_val hN ho, nodeAt_val hN (by rw [timer_root_val]; simp), timer_min_val, timer_root_val] at this
    omega

theorem InsMid.keys_iff {s1 s8 : S} {c t d : U64} {ctx : TRB.Ctx} (_hm : InsMid st T s1 s8 c t d ctx) (y : U64) :
    y ∈ (ctx.plug (.node true .leaf t .leaf)).keys ↔ y = t ∨ y ∈ (ctx.plug .leaf).keys := by
  rw [TRB.attach_keys, TRB.Ctx.plug_keys]
  simp only [TRB.RBT.keys, List.mem_append, List.mem_cons, List.append_nil]
  tauto

theorem InsMid.nodup {s1 s8 : S} {c t d : U64} {ctx : TRB.Ctx} (hm : InsMid st T s1 s8 c t d ctx) :
    (ctx.plug (.node true .leaf t .leaf)).keys.Nodup := by
  have eo : (ctx.plug .leaf).keys = ctx.pre ++ ctx.post := by
    rw [TRB.Ctx.plug_keys]; simp [TRB.RBT.keys]
  rw [TRB.attach_keys]
  refine List.nodup_middle.2 (List.nodup_cons.2 ⟨?_, ?_⟩)
  · rw [← eo]; exact hm.tn
  · rw [← eo]; exact hm.old.nodup

theorem InsMid.inT {s1 s8 : S} {c t d : U64} {ctx : TRB.Ctx} (hm : InsMid st T s1 s8 c t d ctx) :
    ∀ y ∈ (ctx.plug (.node true .leaf t .leaf)).keys, y ∈ T := fun y hy =>
  ((hm.keys_iff y).1 hy).elim (fun e => e ▸ hm.tT) (hm.old.inT y)

/-- The current core's tree after the fixup, read at a state `s'` that agrees with the fixup's result on
the timer words and the root word and whose `TIMER_MIN` is the leftmost key. -/
theorem CoreTree.of_fix {s1 s8 s9 s' : S} {c t d : U64} {ctx : TRB.Ctx} {W : TRB.RBT} {n : Nat}
    (hT : TcbPlaced T) (hm : InsMid st T s1 s8 c t d ctx) (hd0 : d ≠ 0#u64)
    (hF : FB st T s8 c (ctx.plug (.node true .leaf t .leaf)).keys s9 W) (hb : TRB.Bal W n)
    (hbl : W.isRed = false)
    (hag : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → ∀ y ∈ T,
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s9 (core.num.U64.wrapping_add y K))
    (hroot : L.mem s' (L.nodeAt s' c layout.node.TIMER_ROOT) = L.mem s9 (L.nodeAt s9 c layout.node.TIMER_ROOT))
    (hmin : L.mem s' (L.nodeAt s' c layout.node.TIMER_MIN) = W.minKey) :
    CoreTree st T s' c W := by
  have hk := hm.inT
  have kT : ∀ y ∈ W.keys, y ∈ T := fun y hy => hk y (by rw [← hF.keys]; exact hy)
  have hKs : ∀ y, y ∈ W.keys ↔ y = t ∨ y ∈ (ctx.plug .leaf).keys := fun y => by
    rw [hF.keys]; exact hm.keys_iff y
  have td9 : ∀ y ∈ T, L.mem s' (tdA y) = L.mem s8 (tdA y) := fun y hy =>
    (hag 3528#u64 (by simp) (by simp) y hy).trans (hF.td hT hk hm.np hy)
  refine ⟨?_, by rw [hF.keys]; exact hm.nodup, kT, fun y hy => ?_, fun y hy => ?_, ?_, ⟨n, hb⟩, hbl, hmin⟩
  · rw [hroot]
    refine hF.rep.congr fun y hy => ?_
    have hyT := kT y hy
    refine ⟨hag 3544#u64 (by simp) (by simp) y hyT, hag 3552#u64 (by simp) (by simp) y hyT,
      hag 3560#u64 (by simp) (by simp) y hyT, ?_⟩
    show ((L.mem s' (thA y) &&& 1#u64) != 0#u64) = ((L.mem s9 (thA y) &&& 1#u64) != 0#u64)
    rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, hag 3568#u64 (by simp) (by simp) y hyT]
  · rw [td9 y (kT y hy)]
    rcases (hKs y).1 hy with rfl | ho
    · rw [hm.td]; exact hd0
    · rw [hm.tdo y (kT y hy) (fun e => hm.tn (e ▸ ho))]; exact hm.old.armed y ho
  · have hyT := kT y hy
    have e1 : (L.mem s' (thA y)).val >>> 8 = (L.mem s9 (thA y)).val >>> 8 := by
      rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, hag 3568#u64 (by simp) (by simp) y hyT]
    refine e1.trans ((hF.core y hyT).trans ?_)
    rcases (hKs y).1 hy with rfl | ho
    · exact hm.th
    · rw [hm.th_old hT hyT (fun e => hm.tn (e ▸ ho))]; exact hm.old.core y ho
  · rw [hF.keys]
    exact hm.sorted.imp_of_mem fun ha hb hab => by
      rw [td9 _ (hk _ ha), td9 _ (hk _ hb)]; exact hab

theorem node_wr_ne {s : S} {c o o' v : U64} (hN : NodePlaced st T s c) (ho : o.val < 4288) (ho8 : o.val % 8 = 0)
    (ho' : o'.val < 4288) (ho8' : o'.val % 8 = 0) (hne : o'.val ≠ o.val) :
    L.mem (L.wr s (L.nodeAt s c o) v) (L.nodeAt (L.wr s (L.nodeAt s c o) v) c o') = L.mem s (L.nodeAt s c o') := by
  rw [trb_node_wr_node hN hN ho ho8 ho' ho8', if_neg (fun h => hne h.2)]

theorem node_wr_eq {s : S} {c o v : U64} (hN : NodePlaced st T s c) (ho : o.val < 4288) (ho8 : o.val % 8 = 0) :
    L.mem (L.wr s (L.nodeAt s c o) v) (L.nodeAt (L.wr s (L.nodeAt s c o) v) c o) = v := by
  rw [trb_node_wr_node hN hN ho ho8 ho ho8, if_pos ⟨rfl, rfl⟩]

/-- **`timer::insert` keeps the current core's tree red-black** (stages 4 + 5).  For `d ≠ 0`, with `s1`
the state after `remove` and `ctx` the hole the descent found in the old tree `ctx.plug leaf`, the final
state has a `CoreTree` (red-black, black root, sorted, armed, core bits, `TIMER_MIN` = leftmost) whose
in-order keys are the old ones with `t` inserted at the hole. -/
theorem timer.insert.core (s : S) (t d bd : U64) {P : S → Prop} (hT : TcbPlaced T) (ht : t ∈ T)
    (hrem : timer.remove st s t ⦃ s1 => P s1 ⦄)
    (hP : ∀ s1, P s1 → NodePlaced st T s1 (L.cpu s1) ∧ ∃ t0, CoreTree st T s1 (L.cpu s1) t0 ∧ t ∉ t0.keys) :
    timer.insert st s t d bd ⦃ s' => (d = 0#u64 ∧ P s') ∨
      (d ≠ 0#u64 ∧ ∃ (s1 : S) (ctx : TRB.Ctx) (W : TRB.RBT), P s1 ∧ CoreTree st T s1 (L.cpu s1) (ctx.plug .leaf) ∧
        CoreTree st T s' (L.cpu s1) W ∧ W.keys = ctx.pre ++ t :: ctx.post) ⦄ := by
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
  refine Or.inr ⟨hd0, s1, ctx, W, h1, hm.old, ?_, by rw [hF.keys, TRB.attach_keys]⟩
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
    refine CoreTree.of_fix hT hm hd0 hF hb hbl (fun K h1 h2 y hy => ?_) ?_ ?_
    · rw [trb_fld_wr_node hT hN9' hoP hoP8 hy h1 h2, trb_fld_wr_node hT hN9 hoM hoM8 hy h1 h2]
    · rw [node_wr_ne hN9' hoP hoP8 hoR hoR8 (by rw [rp, timer_root_val]; simp),
        node_wr_ne hN9 hoM hoM8 hoR hoR8 (by rw [timer_min_val, timer_root_val]; simp)]
    · rw [node_wr_ne hN9' hoP hoP8 hoM hoM8 (by rw [rp, timer_min_val]; simp), node_wr_eq hN9 hoM hoM8, emk,
        TRB.attach_min, if_pos hp]
  · have es := hnfst hp
    subst es
    refine CoreTree.of_fix hT hm hd0 hF hb hbl (fun _ _ _ _ _ => rfl) rfl ?_
    rw [hmin9, hm.old.min, emk, TRB.attach_min, if_neg hp]

end

end Fl4ProofsA64.P1
