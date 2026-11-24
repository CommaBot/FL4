/-
# P2 (2): the timer tree's write footprint, per word (local timer paths)

P1's `timer.remove.rb` / `timer.insert.coreW` bound the tree code's writes by whole TCBs (`XFoot`). The
local paths' footprint (DESIGN.md §7, `FootLt`) gives another core's thread armed in this core's tree only
its timer links (`TIMER_LEFT ..= TIMER_HEIGHT`), so this module re-runs their compositions keeping the
finer footprints P1 proves inside them (`FixFoot`, `InsFoot`, `clrT`): `TLX s c Ks t`, the timer links
of the keys `Ks` (and of the null handle, which P1's `FixFoot` names and the setters skip), the timer
fields of `t` and core `c`'s node words. Besides, every other thread keeps its deadline and the core
bits of its `TIMER_HEIGHT` (`timer.remove.tlx`, `timer.insert.tlx`).

No named premises.
-/
import Fl4Proofs.P2.FootTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Cs : Set U64}

/-- The words the tree code writes for `t` on core `c`'s tree with keys `Ks`. -/
def TLX (st : machine.Store S) [L : LawfulStore st] (s0 : S) (c : U64) (Ks : List U64) (t w : U64) : Prop :=
  (∃ z, (z = 0#u64 ∨ z ∈ Ks) ∧ (w = tlA z ∨ w = trA z ∨ w = tpA z ∨ w = thA z)) ∨
    (∃ K : U64, 3528 ≤ K.val ∧ K.val < 3576 ∧ w = core.num.U64.wrapping_add t K) ∨
    (∃ o : U64, o.val < 4288 ∧ w = L.nodeAt s0 c o)

theorem TLX.ksb {s0 s1 : S} {c t w : U64} {Ks : List U64} (e : L.ksb s1 = L.ksb s0) (h : TLX st s1 c Ks t w) :
    TLX st s0 c Ks t w := by
  rcases h with h | h | ⟨o, ho, e'⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨o, ho, by rw [e', nodeAt_of_ksb e]⟩)

theorem TLX.mono {s0 : S} {c t w : U64} {Ks Ks' : List U64} (hK : ∀ z ∈ Ks, z ∈ Ks') (h : TLX st s0 c Ks t w) :
    TLX st s0 c Ks' t w := by
  rcases h with ⟨z, hz, e⟩ | h
  · exact Or.inl ⟨z, hz.imp_right (hK z), e⟩
  · exact Or.inr h

theorem fixFoot_tlx {s0 : S} {c t w : U64} {Ks : List U64} (h : FixFoot st s0 c Ks w) : TLX st s0 c Ks t w := by
  rcases h with h | e
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨_, by rw [timer_root_val]; simp, e⟩)

/-- A word outside `TLX`'s TCB words: another TCB's deadline, and every TCB's core bits. -/
theorem tlx_td {s0 : S} {c t y : U64} {Ks : List U64} (hT : TcbPlaced T) (hN : NodePlaced st T s0 c)
    (hk : ∀ z ∈ Ks, z ∈ T) (ht : t ∈ T) (hy : y ∈ T) (hne : y ≠ t) : ¬ TLX st s0 c Ks t (tdA y) := by
  rintro (⟨z, hz, e | e | e | e⟩ | ⟨K, h1, h2, e⟩ | ⟨o, ho, e⟩)
  · exact tz_ne hT (Tz.of_mem hy) (hz.imp_right (hk z)) (K1 := 3528#u64) (K2 := 3544#u64) (by simp) (by simp)
      (by simp) (congrArg UScalar.val e)
  · exact tz_ne hT (Tz.of_mem hy) (hz.imp_right (hk z)) (K1 := 3528#u64) (K2 := 3552#u64) (by simp) (by simp)
      (by simp) (congrArg UScalar.val e)
  · exact tz_ne hT (Tz.of_mem hy) (hz.imp_right (hk z)) (K1 := 3528#u64) (K2 := 3560#u64) (by simp) (by simp)
      (by simp) (congrArg UScalar.val e)
  · exact tz_ne hT (Tz.of_mem hy) (hz.imp_right (hk z)) (K1 := 3528#u64) (K2 := 3568#u64) (by simp) (by simp)
      (by simp) (congrArg UScalar.val e)
  · by_cases hK : K.val = 3528
    · have e' := congrArg UScalar.val e
      rw [show (tdA y).val = (core.num.U64.wrapping_add y 3528#u64).val from rfl,
        show (core.num.U64.wrapping_add t K).val = (core.num.U64.wrapping_add t 3528#u64).val by
          rw [UScalar.eq_of_val_eq (show K.val = (3528#u64 : U64).val by simp [hK])]] at e'
      exact hne (tz_inj hT (Tz.of_mem hy) (Tz.of_mem ht) (by simp) e')
    · exact tz_ne hT (Tz.of_mem hy) (Tz.of_mem ht) (K1 := 3528#u64) (K2 := K) (by simp) (by omega)
        (by simp; omega) (congrArg UScalar.val e)
  · exact node_ne_tz hT hN ho (Tz.of_mem hy) (K := 3528#u64) (by simp) (congrArg UScalar.val e).symm

/-- `remove`'s clearing, word by word. -/
theorem clrT_wx (s : S) {t : U64} (hT : TcbPlaced T) (ht : t ∈ T) :
    WritesIn st s (clrT st s t) (fun w => ∃ K : U64, 3528 ≤ K.val ∧ K.val < 3576 ∧ w = core.num.U64.wrapping_add t K) := by
  have a := fun (K : U64) (h1 : K.val < 4096) (h2 : K.val % 8 = 0) => tz_aligned hT (Tz.of_mem ht) h1 h2
  have w := ((((writesIn_wr (st := st) (s := s) (v := 0#u64) (a (3560#u64) (by simp) (by simp))).trans
    (writesIn_wr (v := 0#u64) (a (3544#u64) (by simp) (by simp)))).trans
    (writesIn_wr (v := 0#u64) (a (3552#u64) (by simp) (by simp)))).trans
    (writesIn_wr (v := 0#u64) (a (3568#u64) (by simp) (by simp)))).trans
    (writesIn_wr (v := 0#u64) (a (3528#u64) (by simp) (by simp)))
  refine w.mono fun b hb => ?_
  rcases hb with (((e | e) | e) | e) | e
  · exact ⟨3560#u64, by simp, by simp, e⟩
  · exact ⟨3544#u64, by simp, by simp, e⟩
  · exact ⟨3552#u64, by simp, by simp, e⟩
  · exact ⟨3568#u64, by simp, by simp, e⟩
  · exact ⟨3528#u64, by simp, by simp, e⟩

/-- What the tree code keeps of every thread but `t`: its deadline and its core bits. -/
def TKeepO (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s s' : S) (t : U64) : Prop :=
  ∀ y ∈ T, y ≠ t → L.mem s' (tdA y) = L.mem s (tdA y) ∧ (L.mem s' (thA y)).val >>> 8 = (L.mem s (thA y)).val >>> 8

theorem TKeepO.trans {s1 s2 s3 : S} {t : U64} (h1 : TKeepO st T s1 s2 t) (h2 : TKeepO st T s2 s3 t) :
    TKeepO st T s1 s3 t := fun y hy hne =>
  ⟨(h2 y hy hne).1.trans (h1 y hy hne).1, (h2 y hy hne).2.trans (h1 y hy hne).2⟩

/-- **`timer::remove`, word by word**: unarmed `t`, nothing; armed in core `c`'s tree `W`, the words
`TLX s c W.keys t`, keeping every other thread's deadline and core bits. -/
theorem timer.remove.tlx (s : S) (t : U64) (hT : TcbPlaced T) (ht : t ∈ T) (hR : TimerRB st T Cs s)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) :
    timer.remove st s t ⦃ s' => (L.mem s (tdA t) = 0#u64 ∧ s' = s) ∨
      ∃ c ∈ Cs, ∃ W, CoreTree st T s c W ∧ t ∈ W.keys ∧ WritesIn st s s' (TLX st s c W.keys t) ∧
        TKeepO st T s s' t ⦄ := by
  have hoM : layout.node.TIMER_MIN.val < 4288 := by rw [timer_min_val]; simp
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
  · exact Or.inl ⟨h0, rfl⟩
  have hNc := hN c hc
  have htW : t ∈ (ctx.plug (.node ct a t b)).keys := TRB.Ctx.keys_sub ctx _ t (by simp [TRB.RBT.keys])
  have hsub := delKeys_sub ctx ct a b t
  have hkW : ∀ y ∈ (ctx.plug (.node ct a t b)).keys, y ∈ T := ct0.inT
  have eb1 : L.nodeBase s1 c = L.nodeBase s c := by simp [LawfulStore.nodeBase, w1.1]
  have hN1 : NodePlaced st T s1 c :=
    ⟨by rw [eb1]; exact hNc.align, by rw [eb1]; exact hNc.fits, by rw [eb1]; exact hNc.disj⟩
  -- the splice and the fixup
  have A : WritesIn st s1 s8 (FixFoot st s1 c (ctx.plug (.node ct a t b)).keys) ∧
      (∀ y ∈ T, (L.mem s8 (thA y)).val >>> 8 = (L.mem s1 (thA y)).val >>> 8) ∧ NodePlaced st T s8 c := by
    cases rr with
    | true =>
      have e8 := h1 rfl
      subst e8
      exact ⟨m.wi, m.core, m.np⟩
    | false =>
      obtain ⟨W', m', hF, hb', hbl'⟩ := h2 rfl c _ (ct0.core t htW) m.rep
      refine ⟨?_, fun y hy => (hF.core y hy).trans (m.core y hy), hF.np⟩
      refine (m.wi.trans hF.wi).mono fun w hw => hw.elim id fun hw => ?_
      rcases hw with ⟨z, hz, e⟩ | e
      · refine Or.inl ⟨z, hz.imp_right fun hz => ?_, e⟩
        rw [sh.keys] at hz; exact hsub.subset hz
      · exact Or.inr (by rw [e, nodeAt_of_ksb m.wi.1])
  obtain ⟨wi18, core18, np8⟩ := A
  have wc := clrT_wx (st := st) s8 hT ht
  refine Or.inr ⟨c, hc, _, ct0, htW, ?_, ?_⟩
  · have wa : WritesIn st s s1 (TLX st s c (ctx.plug (.node ct a t b)).keys t) :=
      w1.mono fun w hw => Or.inr (Or.inr ⟨_, hoM, hw⟩)
    have wb : WritesIn st s1 s8 (TLX st s c (ctx.plug (.node ct a t b)).keys t) :=
      wi18.mono fun w hw => (fixFoot_tlx hw).ksb w1.1
    have wcc : WritesIn st s8 (clrT st s8 t) (TLX st s c (ctx.plug (.node ct a t b)).keys t) :=
      wc.mono fun w hw => Or.inr (Or.inl hw)
    exact ((wa.trans wb).trans wcc).mono fun w hw => by rcases hw with (h | h) | h <;> exact h
  · intro y hy hne
    have ty := tz_aligned hT (Tz.of_mem hy) (K := 3528#u64) (by simp) (by simp)
    have hy8 := tz_aligned hT (Tz.of_mem hy) (K := 3568#u64) (by simp) (by simp)
    -- the clearing
    have c1 : L.mem (clrT st s8 t) (tdA y) = L.mem s8 (tdA y) := by
      refine wc.mem_eq ty fun ⟨K, h1, h2, e⟩ => ?_
      by_cases hK : K.val = 3528
      · exact hne (tz_inj hT (Tz.of_mem hy) (Tz.of_mem ht) (K := 3528#u64) (by simp)
          (by have := congrArg UScalar.val e; rw [show K = 3528#u64 from UScalar.eq_of_val_eq (by simp [hK])] at this
              exact this))
      · exact tz_ne hT (Tz.of_mem hy) (Tz.of_mem ht) (K1 := 3528#u64) (K2 := K) (by simp) (by omega)
          (by simp; omega) (congrArg UScalar.val e)
    have c2 : L.mem (clrT st s8 t) (thA y) = L.mem s8 (thA y) := by
      refine wc.mem_eq hy8 fun ⟨K, h1, h2, e⟩ => ?_
      by_cases hK : K.val = 3568
      · exact hne (tz_inj hT (Tz.of_mem hy) (Tz.of_mem ht) (K := 3568#u64) (by simp)
          (by have := congrArg UScalar.val e; rw [show K = 3568#u64 from UScalar.eq_of_val_eq (by simp [hK])] at this
              exact this))
      · exact tz_ne hT (Tz.of_mem hy) (Tz.of_mem ht) (K1 := 3568#u64) (K2 := K) (by simp) (by omega)
          (by simp; omega) (congrArg UScalar.val e)
    -- the `TIMER_MIN` write
    have d1 : L.mem s1 (tdA y) = L.mem s (tdA y) :=
      w1.mem_eq ty fun e => node_ne_tz hT hNc hoM (Tz.of_mem hy) (K := 3528#u64) (by simp) (congrArg UScalar.val e).symm
    have h1' : L.mem s1 (thA y) = L.mem s (thA y) :=
      w1.mem_eq hy8 fun e => node_ne_tz hT hNc hoM (Tz.of_mem hy) (K := 3568#u64) (by simp) (congrArg UScalar.val e).symm
    refine ⟨?_, ?_⟩
    · rw [c1, wi_fix_td hT hkW hN1 wi18 hy, d1]
    · rw [c2, core18 y hy, h1']


/-- A thread other than `t` keeps its deadline and core bits across words of `TLX` that are links,
`t`'s fields or node words, unless it is the link's owner (only `TIMER_HEIGHT`'s colour may change). -/
theorem tlx_th {s0 : S} {c t y : U64} {Ks : List U64} (hT : TcbPlaced T) (hN : NodePlaced st T s0 c)
    (hk : ∀ z ∈ Ks, z ∈ T) (ht : t ∈ T) (hy : y ∈ T) (hne : y ≠ t) (hyK : y ∉ Ks) :
    ¬ TLX st s0 c Ks t (thA y) := by
  rintro (⟨z, hz, e | e | e | e⟩ | ⟨K, h1, h2, e⟩ | ⟨o, ho, e⟩)
  · exact tz_ne hT (Tz.of_mem hy) (hz.imp_right (hk z)) (K1 := 3568#u64) (K2 := 3544#u64) (by simp) (by simp)
      (by simp) (congrArg UScalar.val e)
  · exact tz_ne hT (Tz.of_mem hy) (hz.imp_right (hk z)) (K1 := 3568#u64) (K2 := 3552#u64) (by simp) (by simp)
      (by simp) (congrArg UScalar.val e)
  · exact tz_ne hT (Tz.of_mem hy) (hz.imp_right (hk z)) (K1 := 3568#u64) (K2 := 3560#u64) (by simp) (by simp)
      (by simp) (congrArg UScalar.val e)
  · have ez := tz_inj hT (Tz.of_mem hy) (hz.imp_right (hk z)) (K := 3568#u64) (by simp) (congrArg UScalar.val e)
    subst ez
    rcases hz with hz | hz
    · exact (hT y hy).ne0 (by rw [hz]; rfl)
    · exact hyK hz
  · by_cases hK : K.val = 3568
    · exact hne (tz_inj hT (Tz.of_mem hy) (Tz.of_mem ht) (K := 3568#u64) (by simp)
        (by have := congrArg UScalar.val e; rw [show K = 3568#u64 from UScalar.eq_of_val_eq (by simp [hK])] at this
            exact this))
    · exact tz_ne hT (Tz.of_mem hy) (Tz.of_mem ht) (K1 := 3568#u64) (K2 := K) (by simp) (by omega)
        (by simp; omega) (congrArg UScalar.val e)
  · exact node_ne_tz hT hN ho (Tz.of_mem hy) (K := 3568#u64) (by simp) (congrArg UScalar.val e).symm

/-- A spec with its result: the run is the one that returned it. -/
theorem spec_self {α : Type _} {m : Result α} {P : α → Prop} (h : m ⦃ r => P r ⦄) : m ⦃ r => P r ∧ m = ok r ⦄ := by
  obtain ⟨v, hv, hp⟩ := spec_ex_fd h
  rw [hv, WP.spec_ok]; exact ⟨hp, rfl⟩

/-- **`timer::insert`, word by word**, given what `remove` leaves (`P`): for `d ≠ 0`, from the state `s1`
after `remove`, the words `TLX s1 c Ks t` of the current core `c`'s tree `Ks` (without `t`), keeping every
other thread's deadline and core bits; `t` is then a key of `c`'s tree, whose other keys are `Ks`. -/
theorem timer.insert.tlx (s : S) (t d bd : U64) {P : S → Prop} (hT : TcbPlaced T) (ht : t ∈ T)
    (hrem : timer.remove st s t ⦃ s1 => P s1 ⦄)
    (hP : ∀ s1, P s1 → NodePlaced st T s1 (L.cpu s1) ∧ ∃ t0, CoreTree st T s1 (L.cpu s1) t0 ∧ t ∉ t0.keys) :
    timer.insert st s t d bd ⦃ s' => (d = 0#u64 ∧ P s') ∨
      (d ≠ 0#u64 ∧ ∃ (s1 : S) (ctx : TRB.Ctx), P s1 ∧ CoreTree st T s1 (L.cpu s1) (ctx.plug .leaf) ∧
        WritesIn st s1 s' (TLX st s1 (L.cpu s1) (ctx.plug .leaf).keys t) ∧ TKeepO st T s1 s' t ∧
        L.mem s' (tdA t) = d ∧
        ∃ W, CoreTree st T s' (L.cpu s1) W ∧ ∀ y ∈ W.keys, y = t ∨ y ∈ (ctx.plug .leaf).keys) ⦄ := by
  have hfix : ∀ s1 s8 ctx, P s1 → InsMid st T s1 s8 (L.cpu s1) t d ctx →
      timer.insert_fixup st s8 (L.cpu s1) t ⦃ s9 => ∃ W0 W n,
        TRB.Rep (lk st s8) 0#u64 (L.mem s8 (L.nodeAt s8 (L.cpu s8) layout.node.TIMER_ROOT)) W0 ∧
        FB st T s8 (L.cpu s8) W0.keys s9 W ∧ TRB.Bal W n ∧ W.isRed = false ⦄ := by
    intro s1 s8 ctx _ hm
    have ec : L.cpu s8 = L.cpu s1 := hm.wi.2.1
    obtain ⟨m, hb⟩ := hm.old.bal
    refine WP.spec_mono (timer.insert_fixup.rb s8 (L.cpu s1) t hT hm.np hm.rep hb hm.old.black hm.nodup hm.inT)
      fun s9 ⟨W, n, hF, hbW, hbl⟩ => ⟨_, W, n, by rw [ec]; exact hm.rep, by rw [ec]; exact hF, hbW, hbl⟩
  refine WP.spec_mono (WP.spec_and (timer.insert.coreW s t d bd hT ht (spec_self hrem)
      fun s1 h1 => hP s1 h1.1)
    (timer.insert.attach (T := T) s t d bd (Q := fun s8 s9 => ∃ W0 W n,
      TRB.Rep (lk st s8) 0#u64 (L.mem s8 (L.nodeAt s8 (L.cpu s8) layout.node.TIMER_ROOT)) W0 ∧
      FB st T s8 (L.cpu s8) W0.keys s9 W ∧ TRB.Bal W n ∧ W.isRed = false) hT ht (spec_self hrem)
      (fun s1 h1 => hP s1 h1.1) fun s1 s8 ctx h1 hm => hfix s1 s8 ctx h1.1 hm)) fun s' ⟨hc, hs⟩ => ?_
  rcases hs with ⟨hd, h0, -⟩ | ⟨hd0, s1, s8, ctx, s9, ⟨h1, er1⟩, hm, ⟨W0, W, n, hr0, hF, hb, hbl⟩, hfst, hnfst⟩
  · exact Or.inl ⟨hd, h0⟩
  rcases hc with ⟨hd, -⟩ | ⟨-, s1', ctx', W', ⟨-, er1'⟩, cto', ctW', eW', -⟩
  · exact absurd hd hd0
  have e11 : s1 = s1' := ok_inj_ff (er1.symm.trans er1')
  subst e11
  have ectx : ctx'.plug .leaf = ctx.plug .leaf := cto'.uniq hm.old
  have ec : L.cpu s8 = L.cpu s1 := hm.wi.2.1
  rw [ec] at hr0 hF
  have e0 := TRB.Rep.det hm.rep hr0
  subst e0
  have hN1 : NodePlaced st T s1 (L.cpu s1) := hm.np1
  have hkold : ∀ z ∈ (ctx.plug .leaf).keys, z ∈ T := hm.old.inT
  have hpar : ctx.par = 0#u64 ∨ ctx.par ∈ (ctx.plug .leaf).keys := by
    obtain ⟨-, -, mpk, -, -, -, -⟩ := TRB.mid_facts hm.old.rep hm.old.nodup
    by_cases et : ctx = .top
    · subst et; exact Or.inl rfl
    · exact Or.inr (mpk et)
  have w8 : WritesIn st s1 s8 (TLX st s1 (L.cpu s1) (ctx.plug .leaf).keys t) := hm.wi.mono fun w hw => by
    rcases hw with ⟨K, h1, h2, e⟩ | e | e | e
    · exact Or.inr (Or.inl ⟨K, h1, h2, e⟩)
    · exact Or.inl ⟨_, hpar, Or.inl e⟩
    · exact Or.inl ⟨_, hpar, Or.inr (Or.inl e)⟩
    · exact Or.inr (Or.inr ⟨_, by rw [timer_root_val]; simp, e⟩)
  have w9 : WritesIn st s8 s9 (TLX st s1 (L.cpu s1) (ctx.plug .leaf).keys t) := hF.wi.mono fun w hw => by
    rcases hw with ⟨z, hz, e⟩ | e
    · rcases hz with hz | hz
      · exact Or.inl ⟨z, Or.inl hz, e⟩
      · rcases (hm.keys_iff z).1 hz with rfl | hz
        · rcases e with e | e | e | e
          · exact Or.inr (Or.inl ⟨3544#u64, by simp, by simp, e⟩)
          · exact Or.inr (Or.inl ⟨3552#u64, by simp, by simp, e⟩)
          · exact Or.inr (Or.inl ⟨3560#u64, by simp, by simp, e⟩)
          · exact Or.inr (Or.inl ⟨3568#u64, by simp, by simp, e⟩)
        · exact Or.inl ⟨z, Or.inr hz, e⟩
    · exact Or.inr (Or.inr ⟨_, by rw [timer_root_val]; simp, by rw [e, nodeAt_of_ksb hm.wi.1]⟩)
  have k9 : TKeepO st T s1 s9 t := by
    intro y hy hne
    refine ⟨by rw [wi_fix_td hT hm.inT hm.np hF.wi hy, hm.tdo y hy hne], ?_⟩
    rw [hF.core y hy]
    by_cases hyK : y ∈ (ctx.plug .leaf).keys
    · -- a key's height word may only be written by the attach as a link of the hole's parent: never
      have : L.mem s8 (thA y) = L.mem s1 (thA y) := hm.wi.mem_eq
        (tz_aligned hT (Tz.of_mem hy) (K := 3568#u64) (by simp) (by simp)) fun hw => by
          rcases hw with ⟨K, h1, h2, e⟩ | e | e | e
          · by_cases hK : K.val = 3568
            · exact hne (tz_inj hT (Tz.of_mem hy) (Tz.of_mem ht) (K := 3568#u64) (by simp)
                (by have := congrArg UScalar.val e
                    rw [show K = 3568#u64 from UScalar.eq_of_val_eq (by simp [hK])] at this; exact this))
            · exact tz_ne hT (Tz.of_mem hy) (Tz.of_mem ht) (K1 := 3568#u64) (K2 := K) (by simp) (by omega)
                (by simp; omega) (congrArg UScalar.val e)
          · exact tz_ne hT (Tz.of_mem hy) (hpar.imp_right (hkold _)) (K1 := 3568#u64) (K2 := 3544#u64) (by simp)
              (by simp) (by simp) (congrArg UScalar.val e)
          · exact tz_ne hT (Tz.of_mem hy) (hpar.imp_right (hkold _)) (K1 := 3568#u64) (K2 := 3552#u64) (by simp)
              (by simp) (by simp) (congrArg UScalar.val e)
          · exact node_ne_tz hT hN1 (by rw [timer_root_val]; simp) (Tz.of_mem hy) (K := 3568#u64) (by simp)
              (congrArg UScalar.val e).symm
      rw [this]
    · rw [w8.mem_eq (b := thA y) (tz_aligned hT (Tz.of_mem hy) (K := 3568#u64) (by simp) (by simp))
        (tlx_th hT hN1 hkold ht hy hne hyK)]
  have hkW : ∀ y ∈ W'.keys, y = t ∨ y ∈ (ctx.plug .leaf).keys := fun y hy => by
    rw [eW'] at hy
    have e2 : (ctx'.plug .leaf).keys = ctx'.pre ++ ctx'.post := by rw [TRB.Ctx.plug_keys]; simp [TRB.RBT.keys]
    rw [← ectx, e2]
    simp only [List.mem_append, List.mem_cons] at hy ⊢
    tauto
  have htd9 : L.mem s9 (tdA t) = d := by
    rw [wi_fix_td hT hm.inT hm.np hF.wi ht]; exact hm.td
  have ek9 : L.ksb s9 = L.ksb s1 := hF.wi.1.trans hm.wi.1
  have hN9 : NodePlaced st T s9 (L.cpu s1) := hF.np
  by_cases hp : ctx.pre = []
  · have es := hfst hp
    subst es
    have hoM : layout.node.TIMER_MIN.val < 4288 := by rw [timer_min_val]; simp
    have hoM8 : layout.node.TIMER_MIN.val % 8 = 0 := by rw [timer_min_val]
    have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
    have hoP : layout.node.REPROGRAM.val < 4288 := by rw [rp]; simp
    have hoP8 : layout.node.REPROGRAM.val % 8 = 0 := by rw [rp]
    have hN9' : NodePlaced st T (L.wr s9 (L.nodeAt s9 (L.cpu s1) layout.node.TIMER_MIN) t) (L.cpu s1) := hN9.wr
    have wn1 := writesIn_wr (st := st) (s := s9) (v := t) (nodeAt_aligned hN9 hoM hoM8)
    have wn2 := writesIn_wr (st := st) (s := L.wr s9 (L.nodeAt s9 (L.cpu s1) layout.node.TIMER_MIN) t)
      (v := 1#u64) (nodeAt_aligned hN9' hoP hoP8)
    have wn : WritesIn st s9 _ (fun w => w = L.nodeAt s9 (L.cpu s1) layout.node.TIMER_MIN ∨
        w = L.nodeAt (L.wr s9 (L.nodeAt s9 (L.cpu s1) layout.node.TIMER_MIN) t) (L.cpu s1) layout.node.REPROGRAM) :=
      wn1.trans wn2
    have knode : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr (L.wr s9 (L.nodeAt s9 (L.cpu s1) layout.node.TIMER_MIN) t)
          (L.nodeAt (L.wr s9 (L.nodeAt s9 (L.cpu s1) layout.node.TIMER_MIN) t) (L.cpu s1) layout.node.REPROGRAM) 1#u64)
          (core.num.U64.wrapping_add y K) = L.mem s9 (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 => by
      refine wn.mem_eq (tz_aligned hT (Tz.of_mem hy) hK hK8) ?_
      rintro (e | e)
      · exact node_ne_tz hT hN9 hoM (Tz.of_mem hy) hK (congrArg UScalar.val e).symm
      · exact node_ne_tz hT hN9' hoP (Tz.of_mem hy) hK (congrArg UScalar.val e).symm
    refine Or.inr ⟨hd0, s1, ctx, h1, hm.old, ?_, ?_, ?_, W', ctW', hkW⟩
    · refine (w8.trans w9).trans (wn.mono fun w hw => ?_) |>.mono fun w hw => by
        rcases hw with (h | h) | h <;> exact h
      rcases hw with e | e
      · exact Or.inr (Or.inr ⟨_, hoM, by rw [e, nodeAt_of_ksb ek9]⟩)
      · exact Or.inr (Or.inr ⟨_, hoP, by rw [e, nodeAt_of_ksb ((L.ksb_wr _ _ _).trans ek9)]⟩)
    · intro y hy hne
      obtain ⟨a1, a2⟩ := k9 y hy hne
      exact ⟨(knode y hy 3528#u64 (by simp) (by simp)).trans a1, by
        rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, knode y hy 3568#u64 (by simp) (by simp)]
        exact a2⟩
    · rw [show tdA t = core.num.U64.wrapping_add t 3528#u64 from rfl, knode t ht 3528#u64 (by simp) (by simp)]
      exact htd9
  · have es := hnfst hp
    subst es
    exact Or.inr ⟨hd0, s1, ctx, h1, hm.old, (w8.trans w9).mono fun w hw => hw.elim id id, k9, htd9, W', ctW', hkW⟩

/-- In a core's tree, `TIMER_MIN`'s deadline is the least. -/
theorem CoreTree.min_le {s : S} {c : U64} {W : TRB.RBT} (h : CoreTree st T s c W) {y : U64} (hy : y ∈ W.keys) :
    (L.mem s (tdA (L.mem s (L.nodeAt s c layout.node.TIMER_MIN)))).val ≤ (L.mem s (tdA y)).val := by
  rw [h.min]
  have hs := h.sorted
  unfold TRB.RBT.minKey
  generalize W.keys = l at hs hy ⊢
  cases l with
  | nil => simp at hy
  | cons m rest =>
    simp only [List.headD_cons]
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact le_refl _
    · exact (List.pairwise_cons.1 hs).1 y hy'

end

end Fl4Proofs.P2
