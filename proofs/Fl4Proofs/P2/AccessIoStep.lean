/-
# P2: one write against `PathObl.move`'s check (line p2io)

`StepOK` (owners move only between held owners, value classes kept) for the
writes of the I/O port path:

* `Dec`: the words `OwnMap.own` depends on; `own_congr`: equal off them (and
  thread states that stay `Calm`, i.e. `RUNNING` / `RESTART`) keeps `own`;
* `SafeW`: words no owner depends on and whose value class nobody tracks (a
  node word, a non-deciding TCB word, an SC word but `CORE`); `stepOK_safe`: any
  aligned write of one is `StepOK`;
* `stepOK_state`: a write of a `Calm` state over a `Calm` state of a
  thread on this core is `StepOK`.

Premises: `RegionOK` [J] (`P2/OwnMap.lean`), `IoLayA` [J] (alignment of the
objects of the layout).
-/
import Fl4Proofs.P2.AccessIoOwn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region tcbOwner TcbSlot NullOrFrame slotOwner RegionOK
  oAFFINITY oSTATE oBLOCK_OBJ oREPLY_OBJ oTIMER_DEADLINE oTIMER_HEIGHT)

noncomputable section
open Classical
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {m m' : U64 → U64}

/-- **Alignment of the layout's objects** [J]. -/
structure IoLayA (K : KLayout) : Prop where
  slot8 : ∀ p ∈ K.slots, p.val % 8 = 0
  tcb : ∀ t, K.heap t = some .tcb → TcbAddr t
  ntfn8 : ∀ p, K.heap p = some .ntfn → (fld p 24#u64).val % 8 = 0
  sc8 : ∀ p b, region K b = .sc p → (fld p 16#u64).val % 8 = 0

/-- The TCB offsets an owner depends on besides `STATE`. -/
def DecOff (off : U64) : Prop :=
  off = oAFFINITY ∨ off = oBLOCK_OBJ ∨ off = oREPLY_OBJ ∨ off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT

/-- The words `own` depends on, thread states aside. -/
def Dec (K : KLayout) (b : U64) : Prop :=
  b ∈ K.slots ∨ (∃ t off, K.heap t = some .tcb ∧ DecOff off ∧ b = fld t off) ∨
    (∃ p, K.heap p = some .ntfn ∧ b = fld p 24#u64) ∨ (∃ p x, region K x = .sc p ∧ b = fld p 16#u64)

/-- `RUNNING` / `RESTART`. -/
def Calm (v : U64) : Prop := v = sched.TS_RESTART ∨ v = sched.TS_RUNNING

theorem Calm.val {v : U64} (h : Calm v) : v.val = 1 ∨ v.val = 2 := by
  rcases h with e | e <;> rw [e] <;> simp [sched.TS_RESTART, sched.TS_RUNNING]

theorem gOwner_calm {v bo ro : U64} {home : Serial.Owner U64 U64} (h : Calm v) :
    OwnMap.gOwner v bo ro home = home := by
  have hv := h.val
  have q1 : ¬ OwnMap.QueuedState v := by unfold OwnMap.QueuedState; omega
  have q2 : ¬ OwnMap.ReplyState v := by unfold OwnMap.ReplyState; omega
  unfold OwnMap.gOwner; rw [if_neg q1, if_neg q2]

/-- **`own` depends only on `Dec` words and thread states.** -/
theorem own_congr (hK : RegionOK K) (h : ∀ b, Dec K b → m' b = m b)
    (hs : ∀ t, K.heap t = some .tcb → m' (stA t) = m (stA t) ∨ (Calm (m' (stA t)) ∧ Calm (m (stA t)))) :
    own K m' = own K m := by
  funext x
  cases hR : region K x with
  | node c => simp only [own, hR]
  | obj p => simp only [own, hR]
  | none => simp only [own, hR]
  | slot p => simp only [own, hR, slotOwner]; rw [h p (Or.inl (hK.slotOf p x hR))]
  | sc p => simp only [own, hR]; rw [h (fld p 16#u64) (Or.inr (Or.inr (Or.inr ⟨p, x, hR, rfl⟩)))]
  | ntfn p =>
    simp only [own, hR, OwnMap.ntfnOwner]
    rw [h (fld p 24#u64) (Or.inr (Or.inr (Or.inl ⟨p, hK.ntfnOf p x hR, rfl⟩)))]
    by_cases hB : K.heap (m (fld p 24#u64)) = some .tcb
    · rw [h (fld (m (fld p 24#u64)) oAFFINITY) (Or.inr (Or.inl ⟨_, _, hB, Or.inl rfl, rfl⟩))]
    · simp only [if_neg hB]
  | tcb t =>
    have ht := hK.tcbOf t x hR
    have e : ∀ off, DecOff off → m' (fld t off) = m (fld t off) := fun off ho =>
      h _ (Or.inr (Or.inl ⟨t, off, ht, ho, rfl⟩))
    simp only [own, hR, tcbOwner]
    rw [e oAFFINITY (by simp [DecOff]), e oBLOCK_OBJ (by simp [DecOff]), e oREPLY_OBJ (by simp [DecOff]),
      e oTIMER_DEADLINE (by simp [DecOff]), e oTIMER_HEIGHT (by simp [DecOff]), fld_state]
    rcases hs t ht with e' | ⟨c1, c2⟩
    · rw [e']
    · rw [gOwner_calm c1, gOwner_calm c2]

theorem DecOff.lt {off : U64} (h : DecOff off) : off.val < 4096 ∧ off.val % 8 = 0 ∧
    (off.val = 3336 ∨ off.val = 3360 ∨ off.val = 3520 ∨ off.val = 3528 ∨ off.val = 3568) := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    simp [oAFFINITY, oBLOCK_OBJ, oREPLY_OBJ, oTIMER_DEADLINE, oTIMER_HEIGHT]

theorem Dec.aligned (hA : IoLayA K) {b : U64} (h : Dec K b) : Aligned b := by
  rcases h with h | ⟨t, off, ht, ho, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, x, hp, rfl⟩
  · exact hA.slot8 b h
  · exact field_aligned (hA.tcb t ht) ho.lt.1 ho.lt.2.1
  · exact hA.ntfn8 p hp
  · exact hA.sc8 p x hp

/-- Words no owner depends on and whose class nobody tracks. -/
def SafeW (K : KLayout) (b : U64) : Prop :=
  (∃ c, region K b = .node c) ∨
  (∃ t off, K.heap t = some .tcb ∧ region K b = .tcb t ∧ off < 4096 ∧ b.val = t.val + off ∧ off ≠ 3328 ∧ off ≠ 3336 ∧
    off ≠ 3360 ∧ off ≠ 3520 ∧ off ≠ 3528 ∧ off ≠ 3568) ∨
  (∃ p, region K b = .sc p ∧ b.val ≠ p.val + 16)

theorem DecOff.mem {off : U64} (h : DecOff off) : off = oAFFINITY ∨ off = oSTATE ∨ off = oBLOCK_OBJ ∨
    off = oREPLY_OBJ ∨ off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT := by
  rcases h with h | h | h | h | h <;> simp [h]

theorem SafeW.notDec (hK : RegionOK K) (hA : IoLayA K) {b : U64} (h : SafeW K b) : ¬ Dec K b := by
  rintro (hd | ⟨t, off, ht, ho, e⟩ | ⟨p, hp, e⟩ | ⟨p, x, hp, e⟩)
  · have hr := hK.slot b hd
    rcases h with ⟨c, h⟩ | ⟨t, off, -, h, -⟩ | ⟨p, h, -⟩ <;> rw [hr] at h <;> cases h
  · have hr := (hK.tcb t ht off ho.mem).1
    rw [← e] at hr
    have hv := congrArg UScalar.val e
    unfold fld at hv
    rw [tcb_wadd_val (hA.tcb t ht) ho.lt.1] at hv
    rcases h with ⟨c, h⟩ | ⟨t', off', -, h, h1, h2, h3⟩ | ⟨p, h, -⟩
    · rw [hr] at h; cases h
    · rw [hr] at h; injection h with h; subst h
      have := ho.lt.2.2; omega
    · rw [hr] at h; cases h
  · have hr := (hK.ntfn p hp).1
    rw [← e] at hr
    rcases h with ⟨c, h⟩ | ⟨t, off, -, h, -⟩ | ⟨p, h, -⟩ <;> rw [hr] at h <;> cases h
  · obtain ⟨hr, hv⟩ := hK.scw p x hp
    rw [← e] at hr hv
    rcases h with ⟨c, h⟩ | ⟨t, off, -, h, -⟩ | ⟨p', h, h16⟩
    · rw [hr] at h; cases h
    · rw [hr] at h; cases h
    · rw [hr] at h; injection h with h; subst h; exact h16 hv

theorem st_region (hK : RegionOK K) (hA : IoLayA K) {t : U64} (ht : K.heap t = some .tcb) :
    region K (stA t) = .tcb t ∧ (stA t).val = t.val + 3328 := by
  have h := (hK.tcb t ht oSTATE (by simp)).1
  rw [fld_state] at h
  refine ⟨h, ?_⟩
  unfold stA; rw [tcb_wadd_val (hA.tcb t ht) (by rw [st_val]; omega), st_val]

theorem SafeW.notSt (hK : RegionOK K) (hA : IoLayA K) {b : U64} (h : SafeW K b) {t : U64}
    (ht : K.heap t = some .tcb) : b ≠ stA t := by
  rintro rfl
  obtain ⟨hr, hv⟩ := st_region hK hA ht
  rcases h with ⟨c, h⟩ | ⟨t', off', -, h, h1, h2, h3, -⟩ | ⟨p, h, -⟩
  · rw [hr] at h; cases h
  · rw [hr] at h; injection h with h; subst h; omega
  · rw [hr] at h; cases h

/-- Unaligned words: nobody tracks their class. -/
theorem ko_unaligned (hK : RegionOK K) (hA : IoLayA K) {m0 : U64 → U64} {z : U64} (hz : ¬ Aligned z) :
    OwnMap.ko K m0 z = .free := by
  unfold OwnMap.ko
  cases hR : region K z with
  | node c => rfl
  | obj p => rfl
  | none => rfl
  | ntfn p => rfl
  | sc p => rfl
  | slot p =>
    have hp := hA.slot8 p (hK.slotOf p z hR)
    have : ¬ (z = p ∧ ¬ TcbSlot K p) := fun h => hz (by rw [h.1]; exact hp)
    simp only [if_neg this]
  | tcb t =>
    have ha := (hA.tcb t (hK.tcbOf t z hR)).align
    have : ¬ (z.val - t.val = 3328) := fun h => hz (by unfold Aligned; omega)
    simp only [if_neg this]

theorem SafeW.ko {m0 : U64 → U64} {b : U64} (h : SafeW K b) : OwnMap.ko K m0 b = .free := by
  unfold OwnMap.ko
  rcases h with ⟨c, h⟩ | ⟨t, off, -, h, h1, h2, h3, -⟩ | ⟨p, h, -⟩
  · simp only [h]
  · have : ¬ (b.val - t.val = 3328) := by omega
    simp only [h, if_neg this]
  · simp only [h]

variable {m0 : U64 → U64} {User : U64 → Prop} {c : U64} {lk : U64 → Prop} {x : S} {b v : U64}

/-- A write keeps `own` when it keeps the deciding words. -/
theorem own_wr_safe (hK : RegionOK K) (hA : IoLayA K) (hb : Aligned b) (h : SafeW K b) :
    own K (L.mem (L.wr x b v)) = own K (L.mem x) := by
  refine own_congr hK (fun z hz => mem_wr_ne' hb (hz.aligned hA) fun e => ?_) fun t ht => Or.inl ?_
  · subst e; exact h.notDec hK hA hz
  · have ha : Aligned (stA t) := field_aligned (hA.tcb t ht) (by rw [st_val]; omega) (by rw [st_val])
    exact mem_wr_ne' hb ha (h.notSt hK hA ht)

/-- **An aligned write of a safe word is `StepOK`.** -/
theorem stepOK_safe (hK : RegionOK K) (hA : IoLayA K) (hb : Aligned b) (h : SafeW K b) :
    StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0) User c lk (L.mem x) (L.mem (L.wr x b v)) := by
  refine ⟨fun z hz => absurd (by rw [own_wr_safe hK hA hb h]) hz, fun z hz _ => Or.inr (Or.inr ?_)⟩
  by_cases ha : Aligned z
  · have e : z = b := by
      by_contra hne; exact hz (mem_wr_ne' hb ha (Ne.symm hne))
    subst e; exact h.ko
  · exact ko_unaligned hK hA ha

/-- **A `Calm` state over a `Calm` state is `StepOK`.** -/
theorem stepOK_state (hK : RegionOK K) (hA : IoLayA K) {t : U64} (ht : K.heap t = some .tcb) (hv : Calm v)
    (hx : Calm (L.mem x (stA t))) (hc : m0 (affA t) = c) :
    StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0) User c lk (L.mem x) (L.mem (L.wr x (stA t) v)) := by
  have hb : Aligned (stA t) := field_aligned (hA.tcb t ht) (by rw [st_val]; omega) (by rw [st_val])
  obtain ⟨hr, hvv⟩ := st_region hK hA ht
  have e : own K (L.mem (L.wr x (stA t) v)) = own K (L.mem x) := by
    refine own_congr hK (fun z hz => mem_wr_ne' hb (hz.aligned hA) fun e => ?_) fun t' ht' => ?_
    · subst e
      rcases hz with hd | ⟨t', off, ht', ho, e⟩ | ⟨p, hp, e⟩ | ⟨p, z, hp, e⟩
      · rw [hK.slot _ hd] at hr; cases hr
      · have hr' := (hK.tcb t' ht' off ho.mem).1
        rw [← e, hr] at hr'; injection hr' with hr'; subst hr'
        have hv' := congrArg UScalar.val e
        unfold fld at hv'
        rw [tcb_wadd_val (hA.tcb t ht) ho.lt.1, hvv] at hv'
        have := ho.lt.2.2; omega
      · have hr' := (hK.ntfn p hp).1
        rw [← e, hr] at hr'; cases hr'
      · have hr' := (hK.scw p z hp).1
        rw [← e, hr] at hr'; cases hr'
    · by_cases ett : t' = t
      · subst ett; right; rw [L.mem_wr_same hb]; exact ⟨hv, hx⟩
      · left
        have ha : Aligned (stA t') := field_aligned (hA.tcb t' ht') (by rw [st_val]; omega) (by rw [st_val])
        refine mem_wr_ne' hb ha fun e => ?_
        have hr' := (st_region hK hA ht').1
        rw [← e, hr] at hr'; injection hr' with hr'; exact ett hr'.symm
  refine ⟨fun z hz => absurd (by rw [e]) hz, fun z hz _ => ?_⟩
  by_cases ha : Aligned z
  · have ez : z = stA t := by
      by_contra hne; exact hz (mem_wr_ne' hb ha (Ne.symm hne))
    subst ez
    refine Or.inr (Or.inl ?_)
    have o : (stA t).val - t.val = 3328 := by omega
    unfold OwnMap.ko
    simp only [hr, if_pos o]
    rw [← hc]; rfl
  · exact Or.inr (Or.inr (ko_unaligned hK hA ha))

/-! ## Runs on `mguard` -/

/-- The read-only and the unchecked parts: a trait-call tree whose guarded run
writes only words every write of which passes `Q` runs the same on `mguard`. -/
theorem interp_mg {A X : Type} {ar : machine.Arch A} {R W : U64 → Prop} {Q : S → S → Prop}
    (hQ : ∀ s b v, W b → Q s (L.wr s b v)) : ∀ (p : SProg X), NoZero p → ∀ (s : S) (a : A) (r : X × S × A),
      interp (PathObl.guard st R W) ar p s a = ok r → interp (mguard st Q) ar p s a = ok r := by
  intro p
  induction p with
  | ret x => intro _ s a r h; exact h
  | err e => intro _ s a r h; exact h
  | rd q k ih =>
    intro hz s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R q
    · rw [guard_read hq] at hv
      exact bok.mpr ⟨v, hv, ih v (hz v) s a r hk⟩
    · rw [guard_read_out hq] at hv; exact absurd hv fail_not_ok
  | rdp q k ih =>
    intro hz s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv' : (if R q ∧ R (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = ok v := hv
    by_cases hq : R q ∧ R (core.num.U64.wrapping_add q 8#u64)
    · rw [if_pos hq] at hv'
      exact bok.mpr ⟨v, hv', ih v (hz v) s a r hk⟩
    · rw [if_neg hq] at hv'; exact absurd hv' fail_not_ok
  | wr q v k ih =>
    intro hz s a r h
    simp only [interp] at h ⊢
    obtain ⟨s', hs', hk⟩ := bok.mp h
    by_cases hq : W q
    · rw [guard_write hq] at hs'
      have e : s' = L.wr s q v := by rw [L.write_eq] at hs'; exact (ok_inj_ff hs').symm
      exact bok.mpr ⟨s', mguard_write hs' (by rw [e]; exact hQ s q v hq), ih hz s' a r hk⟩
    · rw [guard_write_out hq] at hs'; exact absurd hs' fail_not_ok
  | zero q n k ih => intro hz; exact absurd hz id
  | clr q n k ih => intro hz; exact absurd hz id
  | ksb k ih =>
    intro hz s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v (hz v) s a r hk⟩
  | cpu k ih =>
    intro hz s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v (hz v) s a r hk⟩
  | masks k ih =>
    intro hz s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v (hz v) s a r hk⟩
  | arch op k ih =>
    intro hz s a r h
    simp only [interp] at h ⊢
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨(v, a'), hv, ih v (hz v) s a' r hk⟩

end

end Fl4Proofs.P2.PathObl
