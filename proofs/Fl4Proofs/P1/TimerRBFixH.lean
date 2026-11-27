/-
P1 (jc6d, TIMER-RB-PLAN stage 5, heap part): the steps of `timer::insert_fixup` on the heap.  `FB` is the
walk state: the heap represents `W` from the root word, `W`'s keys are the fixed list `Ks`, the writes since
the start lie in `FixFoot` (links and height words of `Ks`, the root word), and the core bits of every
height word are kept.  A colour write (`FB.set_red`) is the abstract recolouring; a rotation
(`FB.rotL`/`FB.rotR`) the abstract rotation.
-/
import Fl4Proofs.P1.TimerRBFix
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-- The words `insert_fixup` writes: the links and height words of the tree's keys (and of the null
word), and core `c`'s root word. -/
def FixFoot (st : machine.Store S) [L : LawfulStore st] (s0 : S) (c : U64) (Ks : List U64) (w : U64) : Prop :=
  (∃ z, (z = 0#u64 ∨ z ∈ Ks) ∧ (w = tlA z ∨ w = trA z ∨ w = tpA z ∨ w = thA z)) ∨
    w = L.nodeAt s0 c layout.node.TIMER_ROOT

/-- The fixup's walk state: the heap is `W` (keys `Ks`), writes in `FixFoot`, core bits kept. -/
structure FB (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c : U64) (Ks : List U64)
    (s : S) (W : TRB.RBT) : Prop where
  rep : TRB.Rep (lk st s) 0#u64 (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)) W
  keys : W.keys = Ks
  wi : WritesIn st s0 s (FixFoot st s0 c Ks)
  core : ∀ y ∈ T, (L.mem s (thA y)).val >>> 8 = (L.mem s0 (thA y)).val >>> 8
  np : NodePlaced st T s c

theorem FB.init {s : S} {c : U64} {W : TRB.RBT} (hN : NodePlaced st T s c)
    (h : TRB.Rep (lk st s) 0#u64 (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)) W) :
    FB st T s c W.keys s W :=
  ⟨h, rfl, WritesIn.refl _ _, fun _ _ => rfl, hN⟩

theorem th_keep {s : S} {z y v : U64} (hT : TcbPlaced T) (hz : z ∈ T) (hy : y ∈ T) (hne : y ≠ z) :
    L.mem (L.wr s (thA z) v) (thA y) = L.mem s (thA y) := by
  show L.mem (L.wr s (core.num.U64.wrapping_add z 3568#u64) v) (core.num.U64.wrapping_add y 3568#u64) =
    L.mem s (core.num.U64.wrapping_add y 3568#u64)
  rw [trb_fld_wr hT hz hy (by simp) (by simp) (by simp) (by simp), if_neg (fun h => hne h.1)]

theorem FB.mem {s0 s : S} {c : U64} {Ks : List U64} {W : TRB.RBT} (h : FB st T s0 c Ks s W) {ctx : TRB.Ctx}
    {t : TRB.RBT} (e : W = ctx.plug t) {x : U64} (hx : x ∈ t.keys) : x ∈ Ks := by
  rw [← h.keys, e]; exact TRB.Ctx.keys_sub ctx t x hx

/-- **A colour write is the abstract recolouring.** -/
theorem FB.set_red {s0 s : S} {c : U64} {Ks : List U64} (ctx : TRB.Ctx) (cl : Bool) (l : TRB.RBT) (x : U64)
    (r : TRB.RBT) (hT : TcbPlaced T) (hd : Ks.Nodup) (hk : ∀ y ∈ Ks, y ∈ T)
    (h : FB st T s0 c Ks s (ctx.plug (.node cl l x r))) (b : Bool) :
    timer.set_red st s x b ⦃ s' => FB st T s0 c Ks s' (ctx.plug (.node b l x r)) ⦄ := by
  have hxK : x ∈ Ks := h.mem rfl (by simp [TRB.RBT.keys])
  have hxT := hk x hxK
  have hd' : (ctx.plug (.node cl l x r)).keys.Nodup := by rw [h.keys]; exact hd
  have ek := TRB.recolor_keys ctx cl b l r x
  refine WP.spec_mono (timer.set_red.on s x b hT hxT) fun s' e => ?_
  subst e
  refine ⟨?_, ek.trans h.keys, ?_, fun y hy => ?_, h.np.wr⟩
  · have er : L.mem (L.wr s (thA x) ((L.mem s (thA x) &&& ~~~1#u64) ||| redW b))
        (L.nodeAt (L.wr s (thA x) ((L.mem s (thA x) &&& ~~~1#u64) ||| redW b)) c layout.node.TIMER_ROOT) =
        L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) :=
      root_wr_fld (K := 3568#u64) hT h.np hxT (by simp) (by simp)
    rw [er]
    refine (TRB.Rep.recolor (c' := b) h.rep hd').congr_on (fun y hy => hk y ?_) (lk_wr_red b hT hxT)
    rw [ek, h.keys] at hy; exact hy
  · exact (h.wi.trans (writesIn_wr (a := thA x) (tz_aligned hT (Tz.of_mem hxT) (K := 3568#u64) (by simp) (by simp)))).mono
      fun w hw => hw.elim id fun e => Or.inl ⟨x, Or.inr hxK, Or.inr (Or.inr (Or.inr e))⟩
  · by_cases e : y = x
    · subst e
      rw [L.mem_wr_same (a := thA y) (tz_aligned hT (Tz.of_mem hxT) (K := 3568#u64) (by simp) (by simp)), core_wr_red]
      exact h.core y hy
    · rw [th_keep hT hxT hy e]; exact h.core y hy

/-- A rotation step (`RotFoot` writes, rotated tree with the same keys) keeps `FB`. -/
theorem FB.of_rot {s0 s s' : S} {c : U64} {Ks : List U64} {W W' : TRB.RBT} {x y bk p : U64}
    (hT : TcbPlaced T) (hk : ∀ y ∈ Ks, y ∈ T) (h : FB st T s0 c Ks s W)
    (hr : TRB.Rep (lk st s') 0#u64 (L.mem s' (L.nodeAt s' c layout.node.TIMER_ROOT)) W') (hkw : W'.keys = W.keys)
    (hw : WritesIn st s s' (RotFoot st s c x y bk p))
    (hz : ∀ z, (z = x ∨ z = y ∨ z = bk ∨ z = p) → z = 0#u64 ∨ z ∈ Ks) : FB st T s0 c Ks s' W' := by
  have hzT : ∀ z, (z = x ∨ z = y ∨ z = bk ∨ z = p) → Tz T z := fun z hz' => (hz z hz').imp_right (hk z)
  refine ⟨hr, hkw.trans h.keys, ?_, fun y' hy => ?_, ?_⟩
  · refine (h.wi.trans hw).mono fun w hw' => hw'.elim id fun hr' => ?_
    rcases hr' with ⟨z, hz', hw2⟩ | e
    · exact Or.inl ⟨z, hz z hz', by rcases hw2 with e | e | e <;> simp [e]⟩
    · exact Or.inr (by rw [e, nodeAt_of_ksb h.wi.1])
  · have ha := tz_aligned hT (Tz.of_mem hy) (K := 3568#u64) (by simp) (by simp)
    rw [hw.mem_eq (b := thA y') ha (fun hf => ?_)]
    · exact h.core y' hy
    rcases hf with ⟨z, hz', e | e | e⟩ | e
    · exact tz_ne hT (Tz.of_mem hy) (hzT z hz') (K1 := 3568#u64) (K2 := 3544#u64) (by simp) (by simp) (by simp)
        (congrArg UScalar.val e)
    · exact tz_ne hT (Tz.of_mem hy) (hzT z hz') (K1 := 3568#u64) (K2 := 3552#u64) (by simp) (by simp) (by simp)
        (congrArg UScalar.val e)
    · exact tz_ne hT (Tz.of_mem hy) (hzT z hz') (K1 := 3568#u64) (K2 := 3560#u64) (by simp) (by simp) (by simp)
        (congrArg UScalar.val e)
    · exact node_ne_tz hT h.np (o := layout.node.TIMER_ROOT) (by rw [timer_root_val]; simp) (Tz.of_mem hy)
        (K := 3568#u64) (by simp) (congrArg UScalar.val e).symm
  · have e : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hw.1]
    exact ⟨by rw [e]; exact h.np.align, by rw [e]; exact h.np.fits, by rw [e]; exact h.np.disj⟩

theorem FB.rot_z {s0 s : S} {c : U64} {Ks : List U64} {ctx : TRB.Ctx} {t : TRB.RBT} {x y : U64} {b : TRB.RBT}
    (h : FB st T s0 c Ks s (ctx.plug t)) (hd : Ks.Nodup) (hx : x ∈ t.keys) (hy : y ∈ t.keys)
    (hb : ∀ z ∈ b.keys, z ∈ t.keys) :
    ∀ z, (z = x ∨ z = y ∨ z = b.rootKey ∨ z = ctx.par) → z = 0#u64 ∨ z ∈ Ks := by
  have hd' : (ctx.plug t).keys.Nodup := by rw [h.keys]; exact hd
  obtain ⟨-, -, mpk, -, -, -, -⟩ := TRB.mid_facts h.rep hd'
  rintro z (rfl | rfl | rfl | rfl)
  · exact Or.inr (h.mem rfl hx)
  · exact Or.inr (h.mem rfl hy)
  · exact (b.rootKey_mem).imp_right fun m => h.mem rfl (hb _ m)
  · by_cases et : ctx = .top
    · subst et; exact Or.inl rfl
    · exact Or.inr (by rw [← h.keys]; exact mpk et)

/-- **`rotate_left` on the walk state.** -/
theorem FB.rotL {s0 s : S} {c : U64} {Ks : List U64} (ctx : TRB.Ctx) (cx : Bool) (a : TRB.RBT) (x : U64)
    (cy : Bool) (b : TRB.RBT) (y : U64) (g : TRB.RBT) (hT : TcbPlaced T) (hd : Ks.Nodup) (hk : ∀ y ∈ Ks, y ∈ T)
    (h : FB st T s0 c Ks s (ctx.plug (.node cx a x (.node cy b y g)))) :
    timer.rotate_left st s c x ⦃ s' => FB st T s0 c Ks s' (ctx.plug (.node cy (.node cx a x b) y g)) ⦄ := by
  have hd' : (ctx.plug (.node cx a x (.node cy b y g))).keys.Nodup := by rw [h.keys]; exact hd
  have hk' : ∀ z ∈ (ctx.plug (.node cx a x (.node cy b y g))).keys, z ∈ T := fun z hz =>
    hk z (by rw [← h.keys]; exact hz)
  refine WP.spec_mono (timer.rotate_left.rep s c hT h.np h.rep hd' hk') fun s' hs => ?_
  exact FB.of_rot hT hk h hs.1 (TRB.plug_rotL_keys ctx (.node cx a x (.node cy b y g))) hs.2
    (h.rot_z hd (by simp [TRB.RBT.keys]) (by simp [TRB.RBT.keys]) fun z hz => by simp [TRB.RBT.keys, hz])

/-- **`rotate_right` on the walk state.** -/
theorem FB.rotR {s0 s : S} {c : U64} {Ks : List U64} (ctx : TRB.Ctx) (cx : Bool) (cy : Bool) (a : TRB.RBT)
    (y : U64) (b : TRB.RBT) (x : U64) (g : TRB.RBT) (hT : TcbPlaced T) (hd : Ks.Nodup) (hk : ∀ y ∈ Ks, y ∈ T)
    (h : FB st T s0 c Ks s (ctx.plug (.node cx (.node cy a y b) x g))) :
    timer.rotate_right st s c x ⦃ s' => FB st T s0 c Ks s' (ctx.plug (.node cy a y (.node cx b x g))) ⦄ := by
  have hd' : (ctx.plug (.node cx (.node cy a y b) x g)).keys.Nodup := by rw [h.keys]; exact hd
  have hk' : ∀ z ∈ (ctx.plug (.node cx (.node cy a y b) x g)).keys, z ∈ T := fun z hz =>
    hk z (by rw [← h.keys]; exact hz)
  refine WP.spec_mono (timer.rotate_right.rep s c hT h.np h.rep hd' hk') fun s' hs => ?_
  exact FB.of_rot hT hk h hs.1 (TRB.plug_rotR_keys ctx (.node cx (.node cy a y b) x g)) hs.2
    (h.rot_z hd (by simp [TRB.RBT.keys]) (by simp [TRB.RBT.keys]) fun z hz => by simp [TRB.RBT.keys, hz])

end

end Fl4Proofs.P1
