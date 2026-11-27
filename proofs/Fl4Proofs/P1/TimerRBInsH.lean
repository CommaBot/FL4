/-
P1 (jc6d, TIMER-RB-PLAN stage 4, rest): `timer::insert` attaches `t` on the heap.  After `remove`, the
descent finds a leaf hole `ctx` of the current core's tree; the hole's link (or the root word) is set to
`t`, then `t`'s deadline, badge, parent, children and height (red, core `cpu`) are written.  The heap then
represents `ctx.plug (node red leaf t leaf)`, sorted by deadline, with `t`'s core bits right, and only
`t`'s timer fields, the hole parent's child links and the root word written (`InsMid`).
`timer.insert.attach` states this for the whole of `timer.insert`, taking `remove`'s and `insert_fixup`'s
specs as hypotheses (`hrem`, `hfix`); the `TIMER_MIN` update is exactly `first` (`ctx.pre = []`).
-/
import Fl4Proofs.P1.TimerRBIns
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

namespace TRB

/-- The links after attaching `t` at the hole `ctx`: the hole's link := `t`, then `t.p := ctx.par`,
`t.l := 0`, `t.r := 0`, `t` red (the order of `insert`'s writes). -/
def attachK (k : Links) (ctx : Ctx) (t : U64) : Links :=
  ((((holeSet ctx t k).setP t ctx.par).setL t 0#u64).setR t 0#u64).setRed t true

theorem attachK_rep {k : Links} {R : U64} {ctx : Ctx} {t : U64}
    (h : Rep k 0#u64 R (ctx.plug .leaf)) (hd : (ctx.plug .leaf).keys.Nodup) (ht0 : t ≠ 0#u64)
    (hn : t ∉ (ctx.plug .leaf).keys) :
    Rep (attachK k ctx t) 0#u64 (holeR ctx t R) (ctx.plug (.node true .leaf t .leaf)) := by
  obtain ⟨-, -, mpk, -, -, -, -⟩ := mid_facts h hd
  have htp : t ≠ ctx.par := fun e => by
    by_cases et : ctx = .top
    · subst et; exact ht0 e
    · exact hn (by rw [e]; exact mpk et)
  refine attach_rep h hd ht0 hn ?_ ?_ ?_
  · simp [attachK]
  · intro z h1 h2
    simp [attachK, Same, Function.update_apply, h1, holeSet_l_ne h2, holeSet_r_ne h2]
  · cases ctx with
    | top => rfl
    | lc c p r up =>
      simp only [Ctx.par] at htp
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp [attachK, holeSet, Function.update_apply, htp.symm]
    | rc c l p up =>
      simp only [Ctx.par] at htp
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp [attachK, holeSet, Function.update_apply, htp.symm]

theorem attach_mem {ctx : Ctx} {t z : U64} (hz : z ∈ (ctx.plug (.node true .leaf t .leaf)).keys) :
    z = t ∨ z ∈ (ctx.plug .leaf).keys := by
  rw [attach_keys] at hz
  rw [Ctx.plug_keys]
  simp only [RBT.keys, List.append_nil, List.mem_append, List.mem_cons] at hz ⊢
  tauto

theorem pre_mem {ctx : Ctx} {z : U64} (hz : z ∈ ctx.pre) : z ∈ (ctx.plug .leaf).keys := by
  rw [Ctx.plug_keys]; simp [hz, RBT.keys]

end TRB

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-- A write of a TCB field other than the four link/colour words keeps the links. -/
theorem lk_wr_oth {s : S} {z K v : U64} (hT : TcbPlaced T) (hz : z ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (h1 : K.val ≠ 3544) (h2 : K.val ≠ 3552) (h3 : K.val ≠ 3560) (h4 : K.val ≠ 3568) :
    TRB.LinksEqOn T (lk st s) (lk st (L.wr s (core.num.U64.wrapping_add z K) v)) := by
  intro y hy
  have f : ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K'.val ≠ K.val →
      L.mem (L.wr s (core.num.U64.wrapping_add z K) v) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') :=
    fun K' a b c => by rw [trb_fld_wr hT hz hy hK hK8 a b, if_neg (fun h => c h.2)]
  refine ⟨f 3544#u64 (by simp) (by simp) (by simpa using Ne.symm h1),
    f 3552#u64 (by simp) (by simp) (by simpa using Ne.symm h2),
    f 3560#u64 (by simp) (by simp) (by simpa using Ne.symm h3), ?_⟩
  show ((L.mem (L.wr s (core.num.U64.wrapping_add z K) v) (thA y) &&& 1#u64) != 0#u64) =
    ((L.mem s (thA y) &&& 1#u64) != 0#u64)
  rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl,
    f 3568#u64 (by simp) (by simp) (by simpa using Ne.symm h4)]

/-- The links after any write of `z`'s height word: `z`'s colour is the written low bit. -/
theorem lk_wr_th {s : S} {z v : U64} (hT : TcbPlaced T) (hz : z ∈ T) :
    TRB.LinksEqOn T ((lk st s).setRed z ((v &&& 1#u64) != 0#u64)) (lk st (L.wr s (thA z) v)) := by
  intro y hy
  have f : ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K'.val ≠ 3568 →
      L.mem (L.wr s (thA z) v) (core.num.U64.wrapping_add y K') = L.mem s (core.num.U64.wrapping_add y K') :=
    fun K' h1 h2 h3 => by
      rw [show thA z = core.num.U64.wrapping_add z 3568#u64 from rfl,
        trb_fld_wr (K := 3568#u64) (K' := K') hT hz hy (by simp) (by simp) h1 h2, if_neg (fun h => h3 (by simpa using h.2))]
  refine ⟨f 3544#u64 (by simp) (by simp) (by simp), f 3552#u64 (by simp) (by simp) (by simp),
    f 3560#u64 (by simp) (by simp) (by simp), ?_⟩
  show ((L.mem (L.wr s (thA z) v) (thA y) &&& 1#u64) != 0#u64) =
    Function.update (lk st s).red z ((v &&& 1#u64) != 0#u64) y
  rw [show thA z = core.num.U64.wrapping_add z 3568#u64 from rfl, show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl,
    trb_fld_wr (K := 3568#u64) (K' := 3568#u64) hT hz hy (by simp) (by simp) (by simp) (by simp)]
  by_cases e : y = z
  · subst e
    rw [if_pos ⟨rfl, rfl⟩, Function.update_self]
  · rw [if_neg (fun h => e h.1), Function.update_of_ne e]; rfl

theorem RW.wr_oth {s0 s : S} {c R z K v : U64} {K0 : TRB.Links} {F : U64 → Prop} (h : RW st T s0 s c K0 R F)
    (hT : TcbPlaced T) (hz : z ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (h1 : K.val ≠ 3544) (h2 : K.val ≠ 3552) (h3 : K.val ≠ 3560) (h4 : K.val ≠ 3568)
    (hF : F (core.num.U64.wrapping_add z K)) :
    RW st T s0 (L.wr s (core.num.U64.wrapping_add z K) v) c K0 R F :=
  ⟨h.eq.trans (lk_wr_oth hT hz hK hK8 h1 h2 h3 h4), (root_wr_fld hT h.np hz hK hK8).trans h.root,
    (h.wi.trans (writesIn_wr (tz_aligned hT (Tz.of_mem hz) hK hK8))).mono
      fun b hb => hb.elim id fun e => by rw [e]; exact hF, h.np.wr⟩

theorem RW.wr_th {s0 s : S} {c R z v : U64} {K : TRB.Links} {F : U64 → Prop} (h : RW st T s0 s c K R F)
    (hT : TcbPlaced T) (hz : z ∈ T) (hF : F (thA z)) :
    RW st T s0 (L.wr s (thA z) v) c (K.setRed z ((v &&& 1#u64) != 0#u64)) R F :=
  ⟨(h.eq.setRed z _).trans (lk_wr_th hT hz),
    (root_wr_fld (K := 3568#u64) hT h.np hz (by simp) (by simp)).trans h.root,
    (h.wi.trans (writesIn_wr (a := thA z) (tz_aligned hT (Tz.of_mem hz) (K := 3568#u64) (by simp) (by simp)))).mono
      fun b hb => hb.elim id fun e => by rw [e]; exact hF, h.np.wr⟩

theorem or1_and1 (i : U64) : ((i ||| 1#u64) &&& 1#u64) = 1#u64 := by
  have hb : ((i ||| 1#u64) &&& 1#u64).bv = (1#u64).bv := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    by_cases h0 : j = 0 <;>
      simp [h0, UScalar.bv_and, UScalar.bv_or, BitVec.getLsbD_and, BitVec.getLsbD_or, one_bit]
  exact UScalar.eq_of_val_eq (by show ((i ||| 1#u64) &&& 1#u64).bv.toNat = (1#u64).bv.toNat; rw [hb])

theorem or1_red (i : U64) : (((i ||| 1#u64) &&& 1#u64) != 0#u64) = true := by
  rw [or1_and1]; simp

/-- A TCB field write, read at another field (or another TCB). -/
theorem fld_keep {s : S} {z y K K' v : U64} (hT : TcbPlaced T) (hz : z ∈ T) (hy : y ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) (hK' : K'.val < 4096) (hK8' : K'.val % 8 = 0)
    (hne : K'.val ≠ K.val) :
    L.mem (L.wr s (core.num.U64.wrapping_add z K) v) (core.num.U64.wrapping_add y K') =
      L.mem s (core.num.U64.wrapping_add y K') := by
  rw [trb_fld_wr hT hz hy hK hK8 hK' hK8', if_neg (fun h => hne h.2)]

/-- The words `insert` writes between the descent and the fixup: `t`'s timer fields (deadline, badge,
links, height), the hole parent's child links and core `c`'s root word. -/
def InsFoot (st : machine.Store S) [L : LawfulStore st] (s1 : S) (c t p : U64) (w : U64) : Prop :=
  (∃ K : U64, 3528 ≤ K.val ∧ K.val < 3576 ∧ w = core.num.U64.wrapping_add t K) ∨ w = tlA p ∨ w = trA p ∨
    w = L.nodeAt s1 c layout.node.TIMER_ROOT

/-- A field of another TCB lies outside `InsFoot` (the hole parent's child links excepted). -/
theorem insFoot_not {s1 : S} {c t p y K' : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s1 c) (htT : t ∈ T)
    (hp : Tz T p) (hy : y ∈ T) (hK' : K'.val < 4096) (hyt : y ≠ t)
    (hyp : y ≠ p ∨ (K'.val ≠ 3544 ∧ K'.val ≠ 3552)) :
    ¬ InsFoot st s1 c t p (core.num.U64.wrapping_add y K') := by
  rintro (⟨K, h1, h2, e⟩ | e | e | e)
  · by_cases hk : K'.val = K.val
    · rw [show K' = K from UScalar.eq_of_val_eq hk] at e
      exact hyt (tz_inj hT (Tz.of_mem hy) (Tz.of_mem htT) (by omega) (congrArg UScalar.val e))
    · exact tz_ne hT (Tz.of_mem hy) (Tz.of_mem htT) hK' (by omega) hk (congrArg UScalar.val e)
  · rw [show tlA p = core.num.U64.wrapping_add p 3544#u64 from rfl] at e
    by_cases hk : K'.val = 3544
    · rcases hyp with hyp | hyp
      · rw [show K' = 3544#u64 from UScalar.eq_of_val_eq (by simpa using hk)] at e
        exact hyp (tz_inj hT (Tz.of_mem hy) hp (by simp) (congrArg UScalar.val e))
      · exact hyp.1 hk
    · exact tz_ne hT (Tz.of_mem hy) hp hK' (by simp) (by simpa using hk) (congrArg UScalar.val e)
  · rw [show trA p = core.num.U64.wrapping_add p 3552#u64 from rfl] at e
    by_cases hk : K'.val = 3552
    · rcases hyp with hyp | hyp
      · rw [show K' = 3552#u64 from UScalar.eq_of_val_eq (by simpa using hk)] at e
        exact hyp (tz_inj hT (Tz.of_mem hy) hp (by simp) (congrArg UScalar.val e))
      · exact hyp.2 hk
    · exact tz_ne hT (Tz.of_mem hy) hp hK' (by simp) (by simpa using hk) (congrArg UScalar.val e)
  · exact node_ne_tz hT hN (by rw [timer_root_val]; simp) (Tz.of_mem hy) hK' (congrArg UScalar.val e).symm

/-- The state right before `insert_fixup`: `t` attached red at the hole `ctx` of the old tree. -/
structure InsMid (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s1 s8 : S) (c t d : U64)
    (ctx : TRB.Ctx) : Prop where
  old : CoreTree st T s1 c (ctx.plug .leaf)
  tn : t ∉ (ctx.plug .leaf).keys
  tT : t ∈ T
  pre : ∀ z ∈ ctx.pre, (L.mem s1 (tdA z)).val ≤ d.val
  post : ∀ z ∈ ctx.post, d.val < (L.mem s1 (tdA z)).val
  rep : TRB.Rep (lk st s8) 0#u64 (L.mem s8 (L.nodeAt s8 c layout.node.TIMER_ROOT))
    (ctx.plug (.node true .leaf t .leaf))
  td : L.mem s8 (tdA t) = d
  tdo : ∀ y ∈ T, y ≠ t → L.mem s8 (tdA y) = L.mem s1 (tdA y)
  th : (L.mem s8 (thA t)).val >>> 8 = c.val
  sorted : (ctx.plug (.node true .leaf t .leaf)).keys.Pairwise
    (fun a b => (L.mem s8 (tdA a)).val ≤ (L.mem s8 (tdA b)).val)
  wi : WritesIn st s1 s8 (InsFoot st s1 c t ctx.par)
  np : NodePlaced st T s8 c

/-- **`timer::insert` attaches `t`** (stage 4).  `hrem`: what `remove` leaves (`P`); `hP`: from it, the
current core's tree (without `t`) and its node placement; `hfix`: `insert_fixup`'s spec from `InsMid`.
Result: for `d = 0` just `remove`; else the attach state `InsMid`, the fixup's post `Q`, and the
`TIMER_MIN` / `REPROGRAM` writes exactly when nothing lies before the hole. -/
theorem timer.insert.attach (s : S) (t d bd : U64) {P : S → Prop} {Q : S → S → Prop}
    (hT : TcbPlaced T) (ht : t ∈ T)
    (hrem : timer.remove st s t ⦃ s1 => P s1 ⦄)
    (hP : ∀ s1, P s1 → NodePlaced st T s1 (L.cpu s1) ∧ ∃ t0, CoreTree st T s1 (L.cpu s1) t0 ∧ t ∉ t0.keys)
    (hfix : ∀ s1 s8 ctx, P s1 → InsMid st T s1 s8 (L.cpu s1) t d ctx →
      timer.insert_fixup st s8 (L.cpu s1) t ⦃ s9 => Q s8 s9 ⦄) :
    timer.insert st s t d bd ⦃ s' => (d = 0#u64 ∧ P s') ∨
      (d ≠ 0#u64 ∧ ∃ s1 s8 ctx s9, P s1 ∧ InsMid st T s1 s8 (L.cpu s1) t d ctx ∧ Q s8 s9 ∧
        (ctx.pre = [] → s' = L.wr (L.wr s9 (L.nodeAt s9 (L.cpu s1) layout.node.TIMER_MIN) t)
          (L.nodeAt (L.wr s9 (L.nodeAt s9 (L.cpu s1) layout.node.TIMER_MIN) t) (L.cpu s1) layout.node.REPROGRAM)
            1#u64) ∧
        (ctx.pre ≠ [] → s' = s9)) ⦄ := by
  have ht0 : t ≠ 0#u64 := fun e => (hT t ht).ne0 (by rw [e]; rfl)
  unfold timer.insert
  refine WP.spec_bind hrem fun s1 h1 => ?_
  split
  · rename_i hd; exact (WP.spec_ok _).2 (Or.inl ⟨hd, h1⟩)
  rename_i hd
  obtain ⟨hN, t0, ct, htn⟩ := hP s1 h1
  refine WP.spec_bind (L.cur_cpu_spec s1) fun cpu ec => ?_
  subst ec
  refine WP.spec_bind (timer.root.val s1 (L.cpu s1)) fun cur ecur => ?_
  subst ecur
  have hh : t0.height ≤ layout.TREE_FUEL.val := by rw [layout.TREE_FUEL.val_eq]; exact ct.height_le
  refine WP.spec_bind (timer.insert_loop.desc s1 d layout.TREE_FUEL ct.rep ct.sorted hh) ?_
  rintro ⟨p, gl, fst⟩ ⟨ctx, ep, epp, edir, efst, hpre, hpost⟩
  simp only at epp edir efst
  subst ep
  subst epp
  try simp only [WP.uncurry'_pair]
  obtain ⟨-, -, mpk, mp0, -, -, -⟩ := TRB.mid_facts ct.rep ct.nodup
  have hpT : Tz T ctx.par := by
    by_cases et : ctx = .top
    · subst et; exact Tz.zero
    · exact Tz.of_mem (ct.inT _ (mpk et))
  have hcs : (L.cpu s1).val < 2 ^ 56 := by
    have := hN.fits; simp only [LawfulStore.nodeBase] at this; omega
  have F1 : ∀ K : U64, 3528 ≤ K.val → K.val < 3576 →
      InsFoot st s1 (L.cpu s1) t ctx.par (core.num.U64.wrapping_add t K) := fun K a b => Or.inl ⟨K, a, b, rfl⟩
  have r0 := RW.init hN (InsFoot st s1 (L.cpu s1) t ctx.par)
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × U64 => RW st T s1 r.1 (L.cpu s1) (TRB.holeSet ctx t (lk st s1))
      (TRB.holeR ctx t (L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_ROOT)))
      (InsFoot st s1 (L.cpu s1) t ctx.par) ∧ r.2 = t) ?_ ?_
  · cases ctx with
    | top =>
      split
      · unfold timer.set_root
        refine WP.spec_bind (obj.node_set.spec s1 _ _ t) fun s3 e => ?_
        subst e
        exact (WP.spec_ok _).2 ⟨r0.wr_root hT (Or.inr (Or.inr (Or.inr rfl))), rfl⟩
      · rename_i hb; exact absurd (by rw [eb]; exact decide_eq_true rfl) hb
    | lc cp k r up =>
      have hk0 : k ≠ 0#u64 := mp0 (by intro e; cases e)
      have hkT : k ∈ T := ct.inT _ (mpk (by intro e; cases e))
      have edir' : gl = true := edir
      split
      · rename_i hb; rw [eb] at hb; exact absurd (of_decide_eq_true hb) hk0
      · refine WP.spec_bind (Pₘ := fun s2 => s2 = L.wr s1 (tlA k) t) ?_ fun s2 e => ?_
        · first
            | exact timer.set_left.on s1 k t hT hkT
            | (split
               · exact timer.set_left.on s1 k t hT hkT
               · rename_i hg; exact absurd edir' hg)
        · subst e; exact (WP.spec_ok _).2 ⟨r0.wr_tl hT hkT (Or.inr (Or.inl rfl)), rfl⟩
    | rc cp l k up =>
      have hk0 : k ≠ 0#u64 := mp0 (by intro e; cases e)
      have hkT : k ∈ T := ct.inT _ (mpk (by intro e; cases e))
      have edir' : gl = false := edir
      split
      · rename_i hb; rw [eb] at hb; exact absurd (of_decide_eq_true hb) hk0
      · refine WP.spec_bind (Pₘ := fun s2 => s2 = L.wr s1 (trA k) t) ?_ fun s2 e => ?_
        · first
            | exact timer.set_right.on s1 k t hT hkT
            | (split
               · rename_i hg; rw [edir'] at hg; exact absurd hg (by simp)
               · exact timer.set_right.on s1 k t hT hkT)
        · subst e; exact (WP.spec_ok _).2 ⟨r0.wr_tr hT hkT (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
  rintro ⟨s2, t1⟩ ⟨r2, e⟩
  simp only at r2 e
  subst e
  try simp only [WP.uncurry'_pair]
  step as ⟨i, hi1, hi2⟩
  simp only [lift, timer.RED, Aeneas.Std.bind_ok]
  refine WP.spec_bind (obj.Tcb.set_timer_height.wr s2 t1 _) fun s3 e3 => ?_
  subst e3
  have r3 := r2.wr_th (v := i ||| 1#u64) hT ht (F1 3568#u64 (by simp) (by simp))
  rw [or1_red] at r3
  refine WP.spec_bind (obj.Tcb.set_timer_deadline.wr _ t1 d) fun s4 e4 => ?_
  subst e4
  have r4 : RW st T s1 (L.wr (L.wr s2 (thA t1) (i ||| 1#u64)) (tdA t1) d) _ _ _ _ :=
    r3.wr_oth (K := 3528#u64) (v := d) hT ht (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (F1 _ (by simp) (by simp))
  refine WP.spec_bind (obj.Tcb.set_timer_badge.wr _ t1 bd) fun s5 e5 => ?_
  subst e5
  have r5 : RW st T s1 (L.wr (L.wr (L.wr s2 (thA t1) (i ||| 1#u64)) (tdA t1) d) (tbA t1) bd) _ _ _ _ :=
    r4.wr_oth (K := 3536#u64) (v := bd) hT ht (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (F1 _ (by simp) (by simp))
  refine WP.spec_bind (timer.set_parent.on _ t1 ctx.par hT ht) fun s6 e6 => ?_
  subst e6
  have r6 := r5.wr_tp (v := ctx.par) hT ht (F1 3560#u64 (by simp) (by simp))
  refine WP.spec_bind (timer.set_left.on _ t1 0#u64 hT ht) fun s7 e7 => ?_
  subst e7
  have r7 := r6.wr_tl (v := 0#u64) hT ht (F1 3544#u64 (by simp) (by simp))
  refine WP.spec_bind (timer.set_right.on _ t1 0#u64 hT ht) fun s8 e8 => ?_
  have r8 := r7.wr_tr (v := 0#u64) hT ht (F1 3552#u64 (by simp) (by simp))
  rw [← e8] at r8
  -- the deadline / height words of `t` at `s8`
  have hd8 : L.mem s8 (tdA t1) = d := by
    rw [e8]
    simp only [tdA, thA, trA, tlA, tpA, tbA]
    rw [fld_keep (K := 3552#u64) (K' := 3528#u64) hT ht ht (by simp) (by simp) (by simp) (by simp) (by simp),
      fld_keep (K := 3544#u64) (K' := 3528#u64) hT ht ht (by simp) (by simp) (by simp) (by simp) (by simp),
      fld_keep (K := 3560#u64) (K' := 3528#u64) hT ht ht (by simp) (by simp) (by simp) (by simp) (by simp),
      fld_keep (K := 3536#u64) (K' := 3528#u64) hT ht ht (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact L.mem_wr_same (tz_aligned hT (Tz.of_mem ht) (K := 3528#u64) (by simp) (by simp))
  have hth8 : L.mem s8 (thA t1) = i ||| 1#u64 := by
    rw [e8]
    simp only [tdA, thA, trA, tlA, tpA, tbA]
    rw [fld_keep (K := 3552#u64) (K' := 3568#u64) hT ht ht (by simp) (by simp) (by simp) (by simp) (by simp),
      fld_keep (K := 3544#u64) (K' := 3568#u64) hT ht ht (by simp) (by simp) (by simp) (by simp) (by simp),
      fld_keep (K := 3560#u64) (K' := 3568#u64) hT ht ht (by simp) (by simp) (by simp) (by simp) (by simp),
      fld_keep (K := 3536#u64) (K' := 3568#u64) hT ht ht (by simp) (by simp) (by simp) (by simp) (by simp),
      fld_keep (K := 3528#u64) (K' := 3568#u64) hT ht ht (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact L.mem_wr_same (tz_aligned hT (Tz.of_mem ht) (K := 3568#u64) (by simp) (by simp))
  have tdo : ∀ y ∈ T, y ≠ t1 → L.mem s8 (tdA y) = L.mem s1 (tdA y) := fun y hy hyt =>
    r8.wi.mem_eq (tz_aligned hT (Tz.of_mem hy) (K := 3528#u64) (by simp) (by simp))
      (insFoot_not (K' := 3528#u64) hT hN ht hpT hy (by simp) hyt (Or.inr ⟨by simp, by simp⟩))
  have kmem : ∀ z ∈ (ctx.plug (.node true .leaf t1 .leaf)).keys, z ∈ T := fun z hz =>
    (TRB.attach_mem hz).elim (fun e => e ▸ ht) (ct.inT z)
  have hrep : TRB.Rep (lk st s8) 0#u64 (L.mem s8 (L.nodeAt s8 (L.cpu s1) layout.node.TIMER_ROOT))
      (ctx.plug (.node true .leaf t1 .leaf)) := by
    rw [r8.root]
    exact (TRB.attachK_rep ct.rep ct.nodup ht0 htn).congr_on kmem r8.eq
  have nt : ∀ z ∈ (ctx.plug .leaf).keys, z ≠ t1 := fun z hz e => htn (e ▸ hz)
  have hsorted : (ctx.plug (.node true .leaf t1 .leaf)).keys.Pairwise
      (fun a b => (L.mem s8 (tdA a)).val ≤ (L.mem s8 (tdA b)).val) := by
    refine TRB.attach_sorted ?_ (fun z hz => ?_) (fun z hz => ?_)
    · exact ct.sorted.imp_of_mem fun ha hb hab => by
        rw [tdo _ (ct.inT _ ha) (nt _ ha), tdo _ (ct.inT _ hb) (nt _ hb)]; exact hab
    · have hz' := TRB.pre_mem hz
      rw [tdo _ (ct.inT _ hz') (nt _ hz'), hd8]; exact hpre z hz
    · have hz' : z ∈ (ctx.plug .leaf).keys := by rw [TRB.Ctx.plug_keys]; simp [hz, TRB.RBT.keys]
      rw [tdo _ (ct.inT _ hz') (nt _ hz'), hd8]; exact hpost z hz
  have mid : InsMid st T s1 s8 (L.cpu s1) t1 d ctx :=
    ⟨ct, htn, ht, hpre, hpost, hrep, hd8, tdo,
      by rw [hth8, or1_shr8, shl8_shr8 hcs hi1], hsorted, r8.wi, r8.np⟩
  refine WP.spec_bind (hfix s1 s8 ctx h1 mid) fun s9 h9 => ?_
  split
  · rename_i hf
    have hpre0 : ctx.pre = [] := efst.1 hf
    refine WP.spec_bind (obj.node_set.spec s9 _ _ t1) fun s10 e10 => ?_
    refine WP.spec_mono (obj.node_set.spec _ _ _ 1#u64) fun s11 e11 => ?_
    subst e10 e11
    exact Or.inr ⟨hd, s1, s8, ctx, s9, h1, mid, h9, fun _ => rfl, fun h => absurd hpre0 h⟩
  · rename_i hf
    exact (WP.spec_ok _).2 (Or.inr ⟨hd, s1, s8, ctx, s9, h1, mid, h9,
      fun h => absurd (efst.2 h) hf, fun _ => rfl⟩)

end

end Fl4Proofs.P1
