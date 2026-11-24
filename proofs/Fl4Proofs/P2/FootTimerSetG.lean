/-
# P2: the `TCB_SetTimer` local path's checks on the guarded store

Guarded-store equalities (`PathObl.guard st R W`, the store of `PathObl.acc`) for the read-only checks of
`localtimer.handle_set_timer_local`: `may_run_here`, `current_ok`, `sched_quiet`, `timer_due`, `release_due`,
`set_timer_target_ok` (with `in_core_timer_tree_access`), and `schedule` with nothing due and the action
`RESUME_CURRENT` (`awaken` reading the timer-min thread's deadline and the release head's head refill).
Each is stated with the words it reads in `R` (and, for `schedule`, the words p2sl / p2io's tail lemmas need).

No named premises.
-/
import Fl4Proofs.P2.FootTimerSet
import Fl4Proofs.P2.FootTimerAccLoop
import Fl4Proofs.P2.FootTimerGEIns
import Fl4Proofs.P2.AccessIoFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}

theorem vcpu.bound.guardT (s : S) (t : U64) (h : R (core.num.U64.wrapping_add t 3664#u64)) :
    vcpu.bound (guard st R W) s t = vcpu.bound st s t := by
  unfold vcpu.bound
  rw [eq_of_spec_fd layout.tcb.VCPU.spec]
  simp only [lift, bind_ok]
  exact guard_read h

theorem may_run_here.guard (s : S) (cpu t : U64) (h1 : R (affA t)) (h2 : R (stA t)) (h3 : R (yieldA t))
    (h4 : R (core.num.U64.wrapping_add t 3664#u64)) (h5 : R (scA t)) (h6 : R (scCoreA (L.mem s (scA t)))) :
    localtimer.may_run_here (guard st R W) s cpu t = localtimer.may_run_here st s cpu t := by
  unfold localtimer.may_run_here
  rw [PathObl.obj.Tcb.affinity.guard t s h1, PathObl.obj.Tcb.state.guard t s h2,
    PathObl.obj.Tcb.yield_to.guard t s h3, vcpu.bound.guardT s t h4, PathObl.obj.Tcb.sc.guard t s h5,
    eq_of_spec_fd (obj.Tcb.sc.spec s t)]
  simp only [bind_ok]
  rw [PathObl.obj.Sc.cpu.guard _ s h6]

theorem current_ok.guard (s : S) (cpu ct csc : U64) (h1 : R (affA ct)) (h2 : R (stA ct)) (h3 : R (yieldA ct))
    (h4 : R (core.num.U64.wrapping_add ct 3664#u64)) (h5 : R (scA ct)) (h6 : R (scCoreA (L.mem s (scA ct))))
    (h7 : R (scCoreA csc)) (h8 : R (L.nodeAt s (L.cpu s) layout.node.IDLE_THREAD)) (h9 : R (domA ct))
    (h10 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN)) :
    localtimer.current_ok (guard st R W) s cpu ct csc = localtimer.current_ok st s cpu ct csc := by
  unfold localtimer.current_ok
  rw [may_run_here.guard s cpu ct h1 h2 h3 h4 h5 h6, PathObl.obj.Tcb.sc.guard ct s h5,
    PathObl.obj.Sc.cpu.guard csc s h7, PathObl.sched.idle_thread.guard s h8, PathObl.obj.Tcb.domain.guard ct s h9,
    PathObl.sched.cur_domain.guard s h10]

theorem sched_quiet.guard (s : S) (h1 : R (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (h2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (h3 : R (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING)) :
    localtimer.sched_quiet (guard st R W) s (L.cpu s) = localtimer.sched_quiet st s (L.cpu s) := by
  unfold localtimer.sched_quiet
  rw [PathObl.sched.action.guard s h1, PathObl.sched.domain_time.guard s h2, PathObl.obj.node_get.guard s _ _ h3]

theorem timer_due.guard (s : S) (now : U64) (h1 : R (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))
    (h2 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      R (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) :
    localtimer.timer_due (guard st R W) s (L.cpu s) now = localtimer.timer_due st s (L.cpu s) now := by
  unfold localtimer.timer_due
  rw [PathObl.obj.node_get.guard s _ _ h1, node_get_ok]
  simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.is_null.spec _)]
  simp only [bind_ok]
  by_cases h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64
  · rw [if_pos (by simp [h0]), if_pos (by simp [h0])]
  · rw [if_neg (by simp [h0]), if_neg (by simp [h0]), PathObl.obj.Tcb.timer_deadline.guard _ s (h2 h0)]

theorem release_due.guard (s : S) (h1 : R (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))
    (h2 : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ≠ 0#u64 →
      R (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) ∧
      PathObl.RdHead (L := L) R s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))))
    (hct : R (ctA (L := L) s)) :
    localtimer.release_due (guard st R W) s (L.cpu s) = localtimer.release_due st s (L.cpu s) := by
  unfold localtimer.release_due
  rw [PathObl.obj.node_get.guard s _ _ h1, node_get_ok]
  simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.is_null.spec _)]
  simp only [bind_ok]
  by_cases h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = 0#u64
  · rw [if_pos (by simp [h0]), if_pos (by simp [h0])]
  · rw [if_neg (by simp [h0]), if_neg (by simp [h0]), PathObl.obj.Tcb.sc.guard _ s (h2 h0).1,
      eq_of_spec_fd (obj.Tcb.sc.spec s _)]
    simp only [bind_ok]
    rw [PathObl.sporadic.ready.guard s _ (h2 h0).2 hct]

theorem set_timer_target_ok.guard {T : Set U64} {s : S} {c target : U64} {Wt : TRB.RBT} {b : Bool}
    (ct : CoreTree st T s c Wt) (hR : ∀ w, TreeReads st s c Wt.keys w → R w)
    (h1 : R (affA target)) (h2 : R (tdA target)) (h3 : R (thA target))
    (h : localtimer.set_timer_target_ok st s c target = ok b) :
    localtimer.set_timer_target_ok (guard st R W) s c target = ok b := by
  unfold localtimer.set_timer_target_ok at h ⊢
  rw [PathObl.obj.Tcb.affinity.guard target s h1, PathObl.obj.Tcb.timer_deadline.guard target s h2]
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  rw [ei]; simp only [bind_ok]
  by_cases hi : (i != c) = true
  · rw [if_pos hi] at h ⊢; exact h
  rw [if_neg hi] at h ⊢
  obtain ⟨d, ed, h⟩ := bind_eq_ok h
  rw [ed]; simp only [bind_ok]
  by_cases hd : d = 0#u64
  · rw [if_pos hd] at h ⊢; exact h
  rw [if_neg hd] at h ⊢
  obtain ⟨b', eb', h⟩ := bind_eq_ok h
  rw [in_core_timer_tree_access ct hR eb']; simp only [bind_ok]
  cases b'
  · rw [if_neg Bool.false_ne_true] at h ⊢; exact h
  · rw [if_pos rfl] at h ⊢
    unfold localtimer.core_of at h ⊢
    rw [PathObl.obj.Tcb.timer_height.guard target s h3]; exact h

theorem timer.fire.guard_nodue {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (hRc : R (L.nodeAt s (L.cpu s) layout.node.CUR_TIME))
    (hRt : R (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))
    (hd : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      R (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
    (hT : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) <
        L.mem s (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) :
    timer.fire (guard st R W) ar s a = ok (s, a) := by
  have hb : (0#u64 : U64) < timer.FIRE_BATCH := by unfold timer.FIRE_BATCH; decide
  unfold timer.fire timer.fire_loop
  simp only [PathObl.guard_cur_cpu, L.cur_cpu_eq, bind_ok, bind_tc_ok]
  rw [PathObl.obj.node_get.guard s _ _ hRc, node_get_ok]
  simp only [bind_ok, bind_tc_ok]
  rw [loop]
  unfold timer.fire_loop.body
  simp only [hb, ↓reduceIte, PathObl.guard_cur_cpu, L.cur_cpu_eq, bind_ok, bind_tc_ok]
  rw [PathObl.obj.node_get.guard s _ _ hRt, node_get_ok]
  simp only [bind_ok, bind_tc_ok, is_null_ok]
  by_cases h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64
  · simp only [h0, decide_true, ↓reduceIte, bind_ok, bind_tc_ok]
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [PathObl.obj.Tcb.timer_deadline.guard _ s (hd h0), eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) s _)]
  simp only [bind_ok, bind_tc_ok]
  have h1' : L.mem s (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) >
      L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) := hT.resolve_left h0
  simp only [h1', ↓reduceIte, bind_ok, bind_tc_ok]

theorem sched.awaken_loop.guard_nodue (s : S) (fuel : U64)
    (hRr : R (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))
    (h2 : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ≠ 0#u64 →
      R (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) ∧
      PathObl.RdHead (L := L) R s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))))
    (hct : R (ctA (L := L) s))
    (h : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = 0#u64 ∨
      ¬ ((L.refill s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))
          (L.rhead s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))))).time ≤
        L.curTime s)) :
    sched.awaken_loop (guard st R W) s fuel = ok s := by
  unfold sched.awaken_loop
  rw [loop]
  unfold sched.awaken_loop.body
  by_cases hf : fuel > 0#u64
  swap
  · simp only [hf, ↓reduceIte, bind_ok, bind_tc_ok]
  obtain ⟨f1, hf1, -⟩ := spec_ex_fd (U64.sub_spec (x := fuel) (y := 1#u64) (by scalar_tac))
  simp only [hf, ↓reduceIte, hf1, PathObl.guard_cur_cpu, L.cur_cpu_eq, bind_ok, bind_tc_ok]
  rw [PathObl.obj.node_get.guard s _ _ hRr, node_get_ok]
  simp only [bind_ok, bind_tc_ok, is_null_ok]
  by_cases h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = 0#u64
  · simp only [h0, decide_true, ↓reduceIte, bind_ok, bind_tc_ok]
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [PathObl.obj.Tcb.sc.guard _ s (h2 h0).1, eq_of_spec_fd (obj.Tcb.sc.spec (L := L) s _)]
  simp only [bind_ok, bind_tc_ok]
  rw [PathObl.sporadic.ready.guard s _ (h2 h0).2 hct, eq_of_spec_fd (sporadic.ready.spec (L := L) s _)]
  simp only [bind_ok, bind_tc_ok]
  have h1 := h.resolve_left h0
  simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok, bind_tc_ok]


/-- **`schedule` with nothing due and the action `RESUME_CURRENT`** on the guarded store: `awaken` reads the
node, the timer-min thread's deadline and the release head's head refill (`timer.fire.guard_nodue`,
`awaken_loop.guard_nodue`), then p2io's `schedRes.guard` (`hsw`, `hfr`: p2sl's `switch_sched_context` /
`set_next_interrupt` lemmas at the real run's states). -/
theorem sched.schedule.guard_nodue {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hd : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      R (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
    (hT : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) <
        L.mem s (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
    (h2 : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ≠ 0#u64 →
      R (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) ∧
      PathObl.RdHead (L := L) R s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))))
    (hRel : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = 0#u64 ∨
      ¬ ((L.refill s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))
          (L.rhead s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))))).time ≤
        L.curTime s))
    (ha : L.actionW s = sched.ACTION_RESUME_CURRENT)
    (hsw : ∀ s4, sched.set_action st s sched.ACTION_RESUME_CURRENT = ok s4 →
      sched.switch_sched_context (guard st R W) ar s4 a = sched.switch_sched_context st ar s4 a)
    (hfr : ∀ s4 s5 a3, sched.set_action st s sched.ACTION_RESUME_CURRENT = ok s4 →
      sched.switch_sched_context st ar s4 a = ok (s5, a3) →
      L.ksb s5 = L.ksb s ∧ L.cpu s5 = L.cpu s ∧
      (L.mem s5 (L.nodeAt s5 (L.cpu s5) layout.node.REPROGRAM) ≠ 0#u64 →
        sched.set_next_interrupt (guard st R W) ar s5 a3 = sched.set_next_interrupt st ar s5 a3 ∧
        ∀ s7 a5, sched.set_next_interrupt st ar s5 a3 = ok (s7, a5) → L.ksb s7 = L.ksb s ∧ L.cpu s7 = L.cpu s)) :
    sched.schedule (guard st R W) ar s a = sched.schedule st ar s a := by
  have ct := hNd layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have tm := hNd layout.node.TIMER_MIN (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have rh := hNd layout.node.RELEASE_HEAD (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have sa := hNd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  have hac : sched.action st s = ok sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s), ha]
  have es : sched.schedule st ar s a = PathObl.schedRes st ar s a :=
    PathObl.schedule_res_eq st ar s a (awaken_none ar s a hT hRel) hac
  have haw : sched.awaken (guard st R W) ar s a = ok (s, a) := by
    unfold sched.awaken
    rw [timer.fire.guard_nodue ar s a ct.1 tm.1 hd hT]
    simp only [bind_ok, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
    rw [sched.awaken_loop.guard_nodue s _ rh.1 h2 ct.1 hRel]
    simp only [bind_ok, bind_tc_ok]
  have eg : sched.schedule (guard st R W) ar s a = PathObl.schedRes (guard st R W) ar s a :=
    PathObl.schedule_res_eq _ ar s a haw (by rw [PathObl.sched.action.guard s sa.1]; exact hac)
  rw [eg, es]
  exact PathObl.schedRes.guard ar s a hNd hsw hfr

end

section
variable {S : Type}

/-! ## The SetTimer path's word sets (`PathObl`'s `ReadSet` / `WriteSet` before the ownership cut)

`PathObl`'s sets are meant to be these words intersected with what the path may read / write at the entry
state (`RPerm` / `WPerm` of the ownership map), so that `read_own` / `write_own` hold by construction and
`acc` carries the content: on an accepted run every word it touches is in these sets and owned. -/

/-- The timer keys the path may touch at `s`: core `L.cpu s`'s tree members (armed, `TIMER_HEIGHT >> 8` this
core: exactly the keys of its tree under `TimerRB`) and the target. -/
def StKeys (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) (target y : U64) : Prop :=
  y ∈ T ∧ (y = target ∨ FootLtArmed st s (L.cpu s) y)

/-- The caller's own words: aligned, above its CNode slots, outside its timer fields. -/
def CallerW (t w : U64) : Prop :=
  ∃ k : U64, 256 ≤ k.val ∧ k.val < 4096 ∧ k.val % 8 = 0 ∧ (k.val < 3528 ∨ 3576 ≤ k.val) ∧
    w = core.num.U64.wrapping_add t k

/-- The caller's registers and `STATE` (aligned). -/
def CallerRegW (t w : U64) : Prop :=
  ∃ k : U64, 256 ≤ k.val ∧ k.val ≤ 3328 ∧ k.val % 8 = 0 ∧ w = core.num.U64.wrapping_add t k

/-- The words an accepted `TCB_SetTimer` local path reads (entry state `s`, current SC sized by `Z`):
the tree words `TW` of `StKeys` (this core's node words, the keys' timer fields), the caller's words, the
target's `AFFINITY`, the null handle's deadline and child words (`TreeReads` names them; never read), the
kernel's `CUR_DOMAIN` / `DOMAIN_TIME`, the current SC, and the release head's SC word and SC. -/
def StRd (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (Z : U64 → Nat) (s : S) (target w : U64) :
    Prop :=
  TW st s (L.cpu s) (StKeys st T s target) w ∨ CallerW (L.curW s) w ∨ w = affA target ∨
    w = tdA 0#u64 ∨ w = tlA 0#u64 ∨ w = trA 0#u64 ∨
    w = core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN ∨
    w = core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME ∨
    InSC (L.cscW s) (Z (L.cscW s)) w ∨
    (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ≠ 0#u64 ∧
      (w = scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)) ∨
        InSC (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))
          (Z (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))) w))

/-- The words an accepted `TCB_SetTimer` local path writes: `TW` of `StKeys`, the caller's registers and
state, the current SC. -/
def StWr (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (Z : U64 → Nat) (s : S) (target w : U64) :
    Prop :=
  TW st s (L.cpu s) (StKeys st T s target) w ∨ CallerRegW (L.curW s) w ∨ InSC (L.cscW s) (Z (L.cscW s)) w

end

end Fl4Proofs.P2
