/-
# P2 (line p2lt): `PathObl.move` against the timer tree's write order

**Finding.** `timer::remove` ends with `set_timer_height(t, 0)` *then* `set_timer_deadline(t, 0)`, and
`timer::insert` (on the thread `remove` left with `TIMER_HEIGHT = 0`) writes `set_timer_deadline(t, d)`, `d ≠ 0`,
several writes *before* `set_timer_height(t, cpu << 8 | RED)`. Between the two writes `t` has a nonzero deadline
and `TIMER_HEIGHT >> 8 = 0`, so `OwnMap.own` gives its timer fields to core **0**. On a core `c ≠ 0` the first of
the two writes moves them from `core c` to `core 0`, which the path does not hold: `PathObl.OwnMove`, checked at
every write (`PathObl.move`), fails. This is on the accepted runs of `handle_set_timer_local` (arming any thread;
re-arming or disarming an armed one) and of `handle_timer_irq_local` firing a timer.

* `height_zero_not_move` (`remove`), `arm_before_height_not_move` (`insert`): the memory-level statements;
* `set_height_zero_mguard_fails`, `set_deadline_mguard_fails`: the extracted setters on `PathObl.move`'s checking
  store fail there.

These are statements about the single write; that the accepted runs reach it is read off the extracted bodies
(not proved here). Writing `TIMER_DEADLINE` first in `remove`, and after `TIMER_HEIGHT` in `insert`, keeps the
words with the path's core at every write (`t`'s affinity is the core).

Premise: `OwnMap.RegionOK` [J] (layout facts, `P2/OwnMap.lean`).
-/
import Fl4Proofs.P2.FootTimerSetG
import Fl4Proofs.P2.OwnMap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.MoveTimer
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap
open Classical

theorem treeCore_of {v c : U64} (h : v.val / 256 = c.val) : treeCore v = c := by
  have e : ∃ x : U64, x.val = v.val / 256 := ⟨c, h.symm⟩
  have := @Classical.epsilon_spec U64 (fun x => x.val = v.val / 256) e
  exact UScalar.eq_of_val_eq (by unfold treeCore; rw [← h]; exact this)

/-- The owner of a thread's `TIMER_DEADLINE`. -/
theorem own_dl {K : KLayout} (hK : RegionOK K) {t : U64} (ht : K.heap t = some .tcb) (m : U64 → U64) :
    own K m (fld t oTIMER_DEADLINE) =
      tOwner (m (fld t oTIMER_DEADLINE)) (m (fld t oTIMER_HEIGHT)) (.core (m (fld t oAFFINITY))) := by
  rw [own_tcb_at hK ht (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), oDL_val]
  simp [tcbOwner, GateField, TimerField]

/-- **`remove`'s first write is no owner move** on a core other than 0: `t` armed in core `c`'s tree, its height
zeroed with the deadline still set. -/
theorem height_zero_not_move {K : KLayout} (hK : RegionOK K) {t : U64} (ht : K.heap t = some .tcb)
    {m m' : U64 → U64} {c : U64} {lk : U64 → Prop} (hc : c ≠ 0#u64)
    (hd : (m (fld t oTIMER_DEADLINE)).val ≠ 0) (hh : (m (fld t oTIMER_HEIGHT)).val / 256 = c.val)
    (hd' : m' (fld t oTIMER_DEADLINE) = m (fld t oTIMER_DEADLINE)) (hh' : m' (fld t oTIMER_HEIGHT) = 0#u64) :
    ¬ PathObl.OwnMove (own K) c lk m m' := by
  intro hM
  have e0 : own K m (fld t oTIMER_DEADLINE) = .core c := by
    rw [own_dl hK ht, tOwner, if_pos hd, treeCore_of hh]
  have e1 : own K m' (fld t oTIMER_DEADLINE) = .core 0#u64 := by
    rw [own_dl hK ht, tOwner, hd', if_pos hd, hh', treeCore_of (c := 0#u64) (by simp)]
  have := (hM (fld t oTIMER_DEADLINE) (by rw [e0, e1]; intro e; exact hc (Owner.core.inj e).symm)).2
  rw [e1] at this; exact hc this.symm

/-- **`insert`'s first write to `t`'s own fields is no owner move** on a core other than 0: `t` disarmed with
height 0 and affinity `c`, its deadline set. -/
theorem arm_before_height_not_move {K : KLayout} (hK : RegionOK K) {t : U64} (ht : K.heap t = some .tcb)
    {m m' : U64 → U64} {c : U64} {lk : U64 → Prop} (hc : c ≠ 0#u64)
    (hd : (m (fld t oTIMER_DEADLINE)).val = 0) (ha : m (fld t oAFFINITY) = c)
    (hd' : (m' (fld t oTIMER_DEADLINE)).val ≠ 0) (hh' : m' (fld t oTIMER_HEIGHT) = 0#u64) :
    ¬ PathObl.OwnMove (own K) c lk m m' := by
  intro hM
  have e0 : own K m (fld t oTIMER_DEADLINE) = .core c := by
    rw [own_dl hK ht, tOwner, if_neg (by simpa using hd), ha]
  have e1 : own K m' (fld t oTIMER_DEADLINE) = .core 0#u64 := by
    rw [own_dl hK ht, tOwner, if_pos hd', hh', treeCore_of (c := 0#u64) (by simp)]
  have := (hM (fld t oTIMER_DEADLINE) (by rw [e0, e1]; intro e; exact hc (Owner.core.inj e).symm)).2
  rw [e1] at this; exact hc this.symm

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayout} {t v : U64} {s : S}
variable {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {User : U64 → Prop} {c : U64} {lk : U64 → Prop}

/-- A failed check at a write. -/
theorem mguard_write_fail {Q : S → S → Prop} {a : U64} (hn : ¬ Q s (L.wr s a v)) :
    (PathObl.mguard st Q).write s a v = fail .panic := by
  show (do let s' ← st.write s a v
           if Q s s' then ok s' else fail .panic) = _
  rw [L.write_eq, bind_tc_ok, if_neg hn]

theorem fld_ne (hT : TcbAddr t) {k1 k2 : U64} (h1 : k1.val < 4096) (h2 : k2.val < 4096) (hn : k1.val ≠ k2.val) :
    fld t k1 ≠ fld t k2 := tcb_word_ne hT hT h1 h2 (fun _ => hn)

/-- **`remove`'s `set_timer_height(t, 0)` on `PathObl.move`'s checking store fails** (`c ≠ 0`). -/
theorem set_height_zero_mguard_fails (hK : RegionOK K) (ht : K.heap t = some .tcb) (hT : TcbAddr t)
    (hc : c ≠ 0#u64) (hd : (L.mem s (fld t oTIMER_DEADLINE)).val ≠ 0)
    (hh : (L.mem s (fld t oTIMER_HEIGHT)).val / 256 = c.val) :
    obj.Tcb.set_timer_height (PathObl.mguard st
      (fun x y => PathObl.StepOK (own K) cls ko User c lk (L.mem x) (L.mem y))) t s 0#u64 = fail .panic := by
  have aH : Aligned (fld t oTIMER_HEIGHT) := field_aligned hT (by simp [oTIMER_HEIGHT]) (by simp [oTIMER_HEIGHT])
  have aD : Aligned (fld t oTIMER_DEADLINE) :=
    field_aligned hT (by simp [oTIMER_DEADLINE]) (by simp [oTIMER_DEADLINE])
  have hn : ¬ PathObl.StepOK (own K) cls ko User c lk (L.mem s) (L.mem (L.wr s (fld t oTIMER_HEIGHT) 0#u64)) :=
    fun h => height_zero_not_move hK ht hc hd hh
      (mem_wr_ne' aH aD (fld_ne hT (by simp [oTIMER_HEIGHT]) (by simp [oTIMER_DEADLINE])
        (by simp [oTIMER_HEIGHT, oTIMER_DEADLINE]))) (L.mem_wr_same aH) h.1
  unfold obj.Tcb.set_timer_height
  rw [eq_of_spec_fd P0.Consts.layout.tcb.TIMER_HEIGHT.spec]
  simp only [lift, bind_ok]
  exact mguard_write_fail hn

/-- **`insert`'s `set_timer_deadline(t, d)` on `PathObl.move`'s checking store fails** (`c ≠ 0`, `d ≠ 0`, `t` of
affinity `c` with height 0, as `remove` leaves it). -/
theorem set_deadline_mguard_fails (hK : RegionOK K) (ht : K.heap t = some .tcb) (hT : TcbAddr t)
    (hc : c ≠ 0#u64) (hd : (L.mem s (fld t oTIMER_DEADLINE)).val = 0) (ha : L.mem s (fld t oAFFINITY) = c)
    (hh : L.mem s (fld t oTIMER_HEIGHT) = 0#u64) (hv : v.val ≠ 0) :
    obj.Tcb.set_timer_deadline (PathObl.mguard st
      (fun x y => PathObl.StepOK (own K) cls ko User c lk (L.mem x) (L.mem y))) t s v = fail .panic := by
  have aH : Aligned (fld t oTIMER_HEIGHT) := field_aligned hT (by simp [oTIMER_HEIGHT]) (by simp [oTIMER_HEIGHT])
  have aD : Aligned (fld t oTIMER_DEADLINE) :=
    field_aligned hT (by simp [oTIMER_DEADLINE]) (by simp [oTIMER_DEADLINE])
  have hn : ¬ PathObl.StepOK (own K) cls ko User c lk (L.mem s) (L.mem (L.wr s (fld t oTIMER_DEADLINE) v)) :=
    fun h => arm_before_height_not_move hK ht hc hd ha
      (by rw [L.mem_wr_same aD]; exact hv)
      (by rw [mem_wr_ne' aD aH (fld_ne hT (by simp [oTIMER_DEADLINE]) (by simp [oTIMER_HEIGHT])
        (by simp [oTIMER_HEIGHT, oTIMER_DEADLINE]))]; exact hh) h.1
  unfold obj.Tcb.set_timer_deadline
  rw [eq_of_spec_fd P0.Consts.layout.tcb.TIMER_DEADLINE.spec]
  simp only [lift, bind_ok]
  exact mguard_write_fail hn

end

end Fl4Proofs.P2.MoveTimer
