/-
# P2 (line p2sl): the per-write check `StepOK` for `OwnMap.own`, by kind of write

`PathObl.move` checks `StepOK` (owner moves only between held owners, value
classes kept unless this core's or untracked) at every write of a local path.
For FL4's ownership map (`P2/OwnMap.lean`, v4) the words that decide owners
are few (`DecW`: a TCB's `AFFINITY`, `STATE`, `BLOCK_OBJ`, `TIMER_DEADLINE`,
`TIMER_HEIGHT`; a slot's `CAP0`; a notification's `BOUND_TCB`; an SC's `CORE`),
so a local path's writes fall into three kinds:

* a word that decides nothing (`stepOK_nondec`): no owner changes, and its
  class is untracked (`ko_free_of_nondec`): `StepOK` holds whatever the value
  and the state;
* a thread's `STATE` (`stepOK_state`): only that thread's queue links may
  change owner, between `lock <BLOCK_OBJ>` and its home core; `StepOK` holds
  when the thread is homed on this core (its `STATE` class is this core's) and
  `BLOCK_OBJ` names a held lock whenever the old or the new state is queued;
* a thread's `BLOCK_OBJ` (`stepOK_bobj`): no owner changes while the thread is
  not queued.

All are stated for the store's write (`L.wr`), through `own_congr` (owners
depend on `DecW` words only) and `mem_wr_upd` (aligned words).
`ko_aligned` is `PathSide.ko_aligned` for `OwnMap.ko`.

Premises: `OwnMap.RegionOK` [J] and `E2E.UserOK` [J] of the layout (from P1's
placement, `P2/OwnLayout.lean`).
-/
import Fl4Proofs.P2.OwnLayout
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.OwnMap
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.E2E
open Fl4Proofs.P2.Serial (Owner ClsOwner)

noncomputable section
open Classical

variable {K : KLayout}

/-- The TCB offsets `own K` reads. -/
def DecOff (off : U64) : Prop :=
  off = oAFFINITY ∨ off = oSTATE ∨ off = oBLOCK_OBJ ∨ off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT

theorem DecOff.reg {off : U64} (h : DecOff off) : off = oAFFINITY ∨ off = oSTATE ∨ off = oBLOCK_OBJ ∨
    off = oREPLY_OBJ ∨ off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT := by
  rcases h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- The words `own K` reads. -/
def DecW (K : KLayout) (d : U64) : Prop :=
  (∃ t off, K.heap t = some .tcb ∧ DecOff off ∧ d = fld t off) ∨
    d ∈ K.slots ∨ (∃ p, K.heap p = some .ntfn ∧ d = fld p 24#u64) ∨
    (∃ p b, region K b = .sc p ∧ d = fld p 16#u64)

theorem decW_tcb {t off : U64} (ht : K.heap t = some .tcb) (ho : DecOff off) : DecW K (fld t off) :=
  Or.inl ⟨t, off, ht, ho, rfl⟩

/-- `own K` reads only `DecW` words. -/
theorem own_congr (hK : RegionOK K) {m m' : U64 → U64} (h : ∀ d, DecW K d → m d = m' d) :
    own K m = own K m' := by
  funext x
  have ht : ∀ t, K.heap t = some .tcb → ∀ o, tcbOwner m t o = tcbOwner m' t o := by
    intro t ht o
    have e : ∀ off, DecOff off → m (fld t off) = m' (fld t off) :=
      fun off ho => h _ (decW_tcb ht ho)
    simp only [tcbOwner, tOwner, gOwner, e oAFFINITY (Or.inl rfl), e oSTATE (Or.inr (Or.inl rfl)),
      e oBLOCK_OBJ (Or.inr (Or.inr (Or.inl rfl))), e oTIMER_DEADLINE (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      e oTIMER_HEIGHT (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
  cases hr : region K x with
  | node c => simp only [own, hr]
  | obj p => simp only [own, hr]
  | none => simp only [own, hr]
  | slot p => simp only [own, hr, slotOwner, h p (Or.inr (Or.inl (hK.slotOf p x hr)))]
  | sc p => simp only [own, hr, h _ (Or.inr (Or.inr (Or.inr ⟨p, x, hr, rfl⟩)))]
  | tcb t => simp only [own, hr, ht t (hK.tcbOf t x hr)]
  | ntfn p =>
    have hp := hK.ntfnOf p x hr
    simp only [own, hr, ntfnOwner, h _ (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩)))]
    by_cases hq : K.heap (m' (fld p 24#u64)) = some .tcb
    · simp only [hq, h _ (decW_tcb hq (Or.inl rfl))]
    · simp only [hq, ↓reduceIte]

/-- `DecW` words are aligned kernel words. -/
theorem decW_ok (hU : UserOK K) {d : U64} (h : DecW K d) :
    Aligned d ∧ d ∉ K.user := by
  rcases h with ⟨t, off, ht, ho, rfl⟩ | h | ⟨p, hp, rfl⟩ | ⟨p, b, hb, rfl⟩
  · exact hU.tcb t ht off ho
  · exact hU.slot d h
  · exact hU.ntfn p hp
  · exact hU.sc p b hb

/-- A write of a word deciding nothing changes no owner. -/
theorem own_upd_nondec (hK : RegionOK K) {a : U64} (ha : ¬ DecW K a) (m : U64 → U64) (v : U64) :
    own K (Function.update m a v) = own K m :=
  own_congr hK fun d hd => Function.update_of_ne (fun e : d = a => ha (e ▸ hd)) _ _

/-- A word of no TCB decider offset, of no object's decider: deciding nothing. -/
theorem nondec_of_region (hK : RegionOK K) {x : U64}
    (h : (∃ t, region K x = .tcb t ∧ x.val - t.val ≠ 3520 ∧ x.val - t.val ≠ 3328 ∧ x.val - t.val ≠ 3336 ∧
        x.val - t.val ≠ 3528 ∧ x.val - t.val ≠ 3568) ∨
      (∃ c, region K x = .node c) ∨ (∃ p, region K x = .obj p) ∨ region K x = .none ∨
      (∃ p, region K x = .ntfn p ∧ x.val - p.val ≠ 24) ∨ (∃ p, region K x = .sc p ∧ x.val ≠ p.val + 16)) :
    ¬ DecW K x := by
  intro hd
  rcases hd with ⟨t, off, ht, ho, rfl⟩ | hs | ⟨p, hp, rfl⟩ | ⟨p, b, hb, rfl⟩
  · obtain ⟨hr, hv⟩ := hK.tcb t ht off ho.reg
    rcases h with ⟨t', h1, h2⟩ | ⟨c, h1⟩ | ⟨p', h1⟩ | h1 | ⟨p', h1, _⟩ | ⟨p', h1, _⟩ <;>
      rw [hr] at h1 <;> try (exact Region.noConfusion h1)
    cases h1
    rcases ho with rfl | rfl | rfl | rfl | rfl <;>
      simp only [oAFF_val, oSTATE_val, oBOBJ_val, oDL_val, oHT_val] at hv <;> omega
  · have hr := hK.slot x hs
    rcases h with ⟨t', h1, _⟩ | ⟨c, h1⟩ | ⟨p', h1⟩ | h1 | ⟨p', h1, _⟩ | ⟨p', h1, _⟩ <;>
      rw [hr] at h1 <;> exact Region.noConfusion h1
  · obtain ⟨hr, hv⟩ := hK.ntfn p hp
    rcases h with ⟨t', h1, _⟩ | ⟨c, h1⟩ | ⟨p', h1⟩ | h1 | ⟨p', h1, h2⟩ | ⟨p', h1, _⟩ <;>
      rw [hr] at h1 <;> try (exact Region.noConfusion h1)
    cases h1; exact h2 hv
  · obtain ⟨hr, hv⟩ := hK.scw p b hb
    rcases h with ⟨t', h1, _⟩ | ⟨c, h1⟩ | ⟨p', h1⟩ | h1 | ⟨p', h1, _⟩ | ⟨p', h1, h2⟩ <;>
      rw [hr] at h1 <;> try (exact Region.noConfusion h1)
    cases h1; exact h2 hv

/-- A word deciding nothing has an untracked class. -/
theorem ko_free_of_nondec (hK : RegionOK K) {a : U64} (ha : ¬ DecW K a) (m : U64 → U64) :
    ko K m a = .free := by
  unfold ko
  cases hr : region K a with
  | slot p =>
    have hp := hK.slotOf p a hr
    by_cases e : a = p ∧ ¬ TcbSlot K p
    · exact absurd (Or.inr (Or.inl (e.1 ▸ hp))) ha
    · simp only [if_neg e]
  | tcb t =>
    have ht := hK.tcbOf t a hr
    by_cases e : a.val - t.val = 3328 ∨ a.val - t.val = 3528
    · exfalso; apply ha
      have hin := (region_tcb_inv (K := K) hr).2
      rcases e with e | e
      · have h2 := (hK.tcb t ht oSTATE (Or.inr (Or.inl rfl))).2; rw [oSTATE_val] at h2
        have : a = fld t oSTATE := UScalar.eq_of_val_eq (by have := hin.1; omega)
        exact this ▸ decW_tcb ht (Or.inr (Or.inl rfl))
      · have h2 := (hK.tcb t ht oTIMER_DEADLINE (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).2
        rw [oDL_val] at h2
        have : a = fld t oTIMER_DEADLINE := UScalar.eq_of_val_eq (by have := hin.1; omega)
        exact this ▸ decW_tcb ht (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · simp only [if_neg e]
  | node c => rfl
  | ntfn p => rfl
  | obj p => rfl
  | sc p => rfl
  | none => rfl

/-- A word with a tracked class decides an owner. -/
theorem ko_dec (hK : RegionOK K) {m0 : U64 → U64} {x : U64} (h : ko K m0 x ≠ .free) : DecW K x :=
  Classical.byContradiction fun hd => h (ko_free_of_nondec hK hd m0)

/-- **`PathSide.ko_aligned`** for `OwnMap.ko`. -/
theorem ko_aligned (hK : RegionOK K) (hU : UserOK K) (m0 : U64 → U64) :
    ∀ x, ko K m0 x ≠ .free → Aligned x :=
  fun _ h => (decW_ok hU (ko_dec hK h)).1

/-- Two TCB decider words are the same word only for the same thread and offset. -/
theorem fld_inj (hK : RegionOK K) {t t' off off' : U64} (ht : K.heap t = some .tcb)
    (ht' : K.heap t' = some .tcb) (ho : DecOff off) (ho' : DecOff off') (e : fld t off = fld t' off') :
    t = t' ∧ off = off' := by
  have h1 := hK.tcb t ht off ho.reg
  have h2 := hK.tcb t' ht' off' ho'.reg
  rw [e] at h1
  have et : t = t' := Region.tcb.inj (h1.1.symm.trans h2.1)
  subst et
  exact ⟨rfl, UScalar.eq_of_val_eq (by have := h1.2; have := h2.2; omega)⟩

theorem fld_ne_off (hK : RegionOK K) {t o1 o2 : U64} (ht : K.heap t = some .tcb) (h1 : DecOff o1)
    (h2 : DecOff o2) (hv : o1.val ≠ o2.val) : fld t o1 ≠ fld t o2 :=
  fun e => hv (by rw [(fld_inj hK ht ht h1 h2 e).2])

theorem decOff_sb {off : U64} (ho : off = oSTATE ∨ off = oBLOCK_OBJ) : DecOff off := by
  rcases ho with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

/-- Another thread's owners do not read a word of no decider of it. -/
theorem tcbOwner_upd_other {m : U64 → U64} {t a v : U64} (hne : ∀ off, DecOff off → fld t off ≠ a)
    (o : Nat) : tcbOwner (Function.update m a v) t o = tcbOwner m t o := by
  unfold tcbOwner
  rw [Function.update_of_ne (hne oAFFINITY (Or.inl rfl)),
    Function.update_of_ne (hne oSTATE (Or.inr (Or.inl rfl))),
    Function.update_of_ne (hne oBLOCK_OBJ (Or.inr (Or.inr (Or.inl rfl)))),
    Function.update_of_ne (hne oTIMER_DEADLINE (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
    Function.update_of_ne (hne oTIMER_HEIGHT (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))]

/-- A thread's own words other than its queue links do not read `STATE` /
`BLOCK_OBJ`. -/
theorem tcbOwner_upd_same (hK : RegionOK K) {m : U64 → U64} {t off v : U64} (ht : K.heap t = some .tcb)
    (ho : off = oSTATE ∨ off = oBLOCK_OBJ) {o : Nat} (hg : ¬ GField o) :
    tcbOwner (Function.update m (fld t off) v) t o = tcbOwner m t o := by
  have hoD := decOff_sb ho
  have hA : fld t oAFFINITY ≠ fld t off := fld_ne_off hK ht (Or.inl rfl) hoD
    (by rcases ho with rfl | rfl <;> simp only [oAFF_val, oSTATE_val, oBOBJ_val] <;> omega)
  have hD : fld t oTIMER_DEADLINE ≠ fld t off := fld_ne_off hK ht (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hoD
    (by rcases ho with rfl | rfl <;> simp only [oDL_val, oSTATE_val, oBOBJ_val] <;> omega)
  have hH : fld t oTIMER_HEIGHT ≠ fld t off := fld_ne_off hK ht (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hoD
    (by rcases ho with rfl | rfl <;> simp only [oHT_val, oSTATE_val, oBOBJ_val] <;> omega)
  unfold tcbOwner
  rw [if_neg hg, if_neg hg, Function.update_of_ne hA, Function.update_of_ne hD, Function.update_of_ne hH]

/-- **Writing a thread's `STATE` or `BLOCK_OBJ` changes only the owners of its
queue links.** -/
theorem own_upd_tcb (hK : RegionOK K) {t off v : U64} {m : U64 → U64} (ht : K.heap t = some .tcb)
    (ho : off = oSTATE ∨ off = oBLOCK_OBJ) (x : U64)
    (hx : ¬ (region K x = .tcb t ∧ GField (x.val - t.val))) :
    own K (Function.update m (fld t off) v) x = own K m x := by
  have hoD := decOff_sb ho
  have hr0 := (hK.tcb t ht off hoD.reg).1
  have ne_reg : ∀ y, region K y ≠ .tcb t → y ≠ fld t off := fun y hy e => hy (e ▸ hr0)
  have ne_t : ∀ t' off', K.heap t' = some .tcb → DecOff off' → t' ≠ t → fld t' off' ≠ fld t off :=
    fun t' off' ht' ho' hn e => hn (fld_inj hK ht' ht ho' hoD e).1
  cases hr : region K x with
  | node c => simp only [own, hr]
  | obj p => simp only [own, hr]
  | none => simp only [own, hr]
  | slot p =>
    have hp := hK.slot p (hK.slotOf p x hr)
    simp only [own, hr, slotOwner, Function.update_of_ne (ne_reg p (by rw [hp]; intro h; cases h))]
  | sc p =>
    have hp := (hK.scw p x hr).1
    simp only [own, hr, Function.update_of_ne (ne_reg _ (by rw [hp]; intro h; cases h))]
  | ntfn p =>
    have hp := hK.ntfnOf p x hr
    have h24 := (hK.ntfn p hp).1
    simp only [own, hr, ntfnOwner, Function.update_of_ne (ne_reg _ (by rw [h24]; intro h; cases h))]
    by_cases hq : K.heap (m (fld p 24#u64)) = some .tcb
    · by_cases eb : m (fld p 24#u64) = t
      · have hA : fld (m (fld p 24#u64)) oAFFINITY ≠ fld t off := by
          rw [eb]; exact fld_ne_off hK ht (Or.inl rfl) hoD
            (by rcases ho with rfl | rfl <;> simp only [oAFF_val, oSTATE_val, oBOBJ_val] <;> omega)
        simp only [hq, Function.update_of_ne hA]
      · simp only [hq, Function.update_of_ne (ne_t _ _ hq (Or.inl rfl) eb)]
    · simp only [hq, ↓reduceIte]
  | tcb t' =>
    have ht' := hK.tcbOf t' x hr
    simp only [own, hr]
    by_cases e : t' = t
    · rw [e] at hr ⊢
      exact tcbOwner_upd_same hK ht ho (fun h => hx ⟨hr, h⟩)
    · exact tcbOwner_upd_other (fun off' ho' => ne_t t' off' ht' ho' e) _

/-- The queue links' owner is held when the home core is this one and the lock
is held whenever the thread is queued. -/
theorem held_g {c : U64} {lk : U64 → Prop} {st bo a : U64} (ha : a = c) (hq : QueuedState st → lk bo) :
    PathObl.HeldBy c lk (gOwner st bo (.core a)) := by
  unfold gOwner
  split_ifs with h
  · exact hq h
  · exact ha

section st
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem mem_wr_upd {s : S} {a v x : U64} (ha : Aligned a) (hx : Aligned x) :
    L.mem (L.wr s a v) x = Function.update (L.mem s) a v x := by
  rw [L.mem_wr s a v x ha hx]
  by_cases e : a = x
  · subst e; simp
  · rw [if_neg e, Function.update_of_ne (Ne.symm e)]

theorem own_wr (hK : RegionOK K) (hU : UserOK K) {s : S} {a v : U64} (ha : Aligned a) :
    own K (L.mem (L.wr s a v)) = own K (Function.update (L.mem s) a v) :=
  own_congr hK fun _ hd => mem_wr_upd ha (decW_ok hU hd).1

/-- **A write of a word deciding nothing passes the check**, whatever the value
and the state. -/
theorem stepOK_nondec (hK : RegionOK K) (hU : UserOK K) {m0 : U64 → U64} {c : U64} {lk : U64 → Prop}
    {s : S} {a v : U64} (ha : Aligned a) (hd : ¬ DecW K a) :
    PathObl.StepOK (own K) (cls K) (ko K m0) (· ∈ K.user) c lk (L.mem s) (L.mem (L.wr s a v)) := by
  have e : own K (L.mem (L.wr s a v)) = own K (L.mem s) := by
    rw [own_wr hK hU ha, own_upd_nondec hK hd]
  refine ⟨fun x hx => absurd (congrFun e x) hx, fun x hx _ => Or.inr (Or.inr ?_)⟩
  by_contra hf
  have hdx := ko_dec hK hf
  apply hx
  rw [mem_wr_upd ha (decW_ok hU hdx).1, Function.update_of_ne (fun h : x = a => hd (h ▸ hdx))]

/-- A write of a thread's `STATE` or `BLOCK_OBJ`, the thread homed on core `c`,
with the lock its `BLOCK_OBJ` names held whenever it is queued before or after. -/
theorem stepOK_tcb (hK : RegionOK K) (hU : UserOK K) {m0 : U64 → U64} {c : U64} {lk : U64 → Prop}
    {s : S} {t off v : U64} (ht : K.heap t = some .tcb) (ho : off = oSTATE ∨ off = oBLOCK_OBJ)
    (hc : L.mem s (fld t oAFFINITY) = c) (hc0 : m0 (fld t oAFFINITY) = c)
    (hq0 : QueuedState (L.mem s (fld t oSTATE)) → lk (L.mem s (fld t oBLOCK_OBJ)))
    (hq1 : QueuedState (Function.update (L.mem s) (fld t off) v (fld t oSTATE)) →
      lk (Function.update (L.mem s) (fld t off) v (fld t oBLOCK_OBJ))) :
    PathObl.StepOK (own K) (cls K) (ko K m0) (· ∈ K.user) c lk (L.mem s) (L.mem (L.wr s (fld t off) v)) := by
  have hoD := decOff_sb ho
  have ha : Aligned (fld t off) := (hU.tcb t ht off hoD).1
  have hA : fld t oAFFINITY ≠ fld t off := fld_ne_off hK ht (Or.inl rfl) hoD
    (by rcases ho with rfl | rfl <;> simp only [oAFF_val, oSTATE_val, oBOBJ_val] <;> omega)
  have e := own_wr (L := L) hK hU (s := s) (v := v) ha
  refine ⟨fun x hx => ?_, fun x hx _ => ?_⟩
  · rw [e] at hx ⊢
    by_cases hg : region K x = .tcb t ∧ GField (x.val - t.val)
    · obtain ⟨hr, hg⟩ := hg
      have hgn : ¬ GateField (x.val - t.val) := by unfold GateField; unfold GField at hg; omega
      have htn : ¬ TimerField (x.val - t.val) := by unfold TimerField; unfold GField at hg; omega
      have key : ∀ m' : U64 → U64, own K m' x =
          gOwner (m' (fld t oSTATE)) (m' (fld t oBLOCK_OBJ)) (.core (m' (fld t oAFFINITY))) := by
        intro m'; simp only [own, hr, tcbOwner]; rw [if_neg hgn, if_neg htn, if_pos hg]
      rw [key, key]
      exact ⟨held_g hc hq0, held_g (by rw [Function.update_of_ne hA]; exact hc) hq1⟩
    · exact absurd (own_upd_tcb hK ht ho x hg) hx
  · by_cases hf : ko K m0 x = .free
    · exact Or.inr (Or.inr hf)
    have hdx := ko_dec hK hf
    have hxa : x = fld t off := Classical.byContradiction fun hn =>
      hx (by rw [mem_wr_upd ha (decW_ok hU hdx).1, Function.update_of_ne hn])
    subst hxa
    obtain ⟨hr, hv⟩ := hK.tcb t ht off hoD.reg
    refine Or.inr (Or.inl ?_)
    rcases ho with rfl | rfl
    · simp only [ko, hr]; rw [if_pos (Or.inl (by rw [hv, oSTATE_val])), hc0]
    · exfalso; apply hf; simp only [ko, hr]; rw [if_neg (by rw [hv, oBOBJ_val]; omega)]

/-- **A write of a thread's `STATE` passes the check**: the thread homed on core
`c`, and its `BLOCK_OBJ` a held lock whenever the old or the new state is
queued. -/
theorem stepOK_state (hK : RegionOK K) (hU : UserOK K) {m0 : U64 → U64} {c : U64} {lk : U64 → Prop}
    {s : S} {t v : U64} (ht : K.heap t = some .tcb)
    (hc : L.mem s (fld t oAFFINITY) = c) (hc0 : m0 (fld t oAFFINITY) = c)
    (hq0 : QueuedState (L.mem s (fld t oSTATE)) → lk (L.mem s (fld t oBLOCK_OBJ)))
    (hq1 : QueuedState v → lk (L.mem s (fld t oBLOCK_OBJ))) :
    PathObl.StepOK (own K) (cls K) (ko K m0) (· ∈ K.user) c lk (L.mem s) (L.mem (L.wr s (fld t oSTATE) v)) := by
  have hB : fld t oBLOCK_OBJ ≠ fld t oSTATE := fld_ne_off hK ht (Or.inr (Or.inr (Or.inl rfl)))
    (Or.inr (Or.inl rfl)) (by simp only [oBOBJ_val, oSTATE_val]; omega)
  refine stepOK_tcb hK hU ht (Or.inl rfl) hc hc0 hq0 ?_
  rw [Function.update_self, Function.update_of_ne hB]
  exact hq1

/-- **A write of a thread's `BLOCK_OBJ` passes the check** while the thread is
not queued (homed on core `c`). -/
theorem stepOK_bobj (hK : RegionOK K) (hU : UserOK K) {m0 : U64 → U64} {c : U64} {lk : U64 → Prop}
    {s : S} {t v : U64} (ht : K.heap t = some .tcb)
    (hc : L.mem s (fld t oAFFINITY) = c) (hc0 : m0 (fld t oAFFINITY) = c)
    (hnq : ¬ QueuedState (L.mem s (fld t oSTATE))) :
    PathObl.StepOK (own K) (cls K) (ko K m0) (· ∈ K.user) c lk (L.mem s)
      (L.mem (L.wr s (fld t oBLOCK_OBJ) v)) := by
  have hS : fld t oSTATE ≠ fld t oBLOCK_OBJ := fld_ne_off hK ht (Or.inr (Or.inl rfl))
    (Or.inr (Or.inr (Or.inl rfl))) (by simp only [oBOBJ_val, oSTATE_val]; omega)
  refine stepOK_tcb hK hU ht (Or.inr rfl) hc hc0 (fun h => absurd h hnq) (fun h => ?_)
  rw [Function.update_of_ne hS] at h
  exact absurd h hnq

end st

end

end Fl4Proofs.P2.OwnMap
