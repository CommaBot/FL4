/-
# P2 (2): the accepted `TCB_SetTimer` local path writes only its footprint

`set_timer_accept_foot`: an accepted run of `localtimer.handle_set_timer_local` from a state with
the P1 invariant (`BXI`) writes only `FootLt` of its entry state (DESIGN.md §7). The walk is
P1's `set_timer_local_same` (`P1/LocalTimer.lean`), word by word:

* the prefix (`lt_prefix`): the caller's `FAULT_IP`, the core's `CUR_TIME` and `CONSUMED`;
* `set_thread_state t Restart` / `Running`: the caller's state word only, since the caller stays
  schedulable (`is_sched_of`, so `schedule_tcb` leaves the action alone: `sts_sch`);
* `timer::insert` (`insert_local`, P2/FootTimerIns): this core's root, min and reprogram words,
  `target`'s timer fields (`target` disarmed or armed in this core's tree: the
  `set_timer_target_ok` check, `target_ok_facts`) and the timer links of this core's tree;
* `reply_success_empty`: the caller's `BADGE` and `MSG_INFO` registers (`reply_tr`);
* `schedule`: nothing is due (`awaken_none`: the timer check `timer_due` carried to the
  `schedule` state by `nodue_keep` and `insert_local`, the release check `release_due` by
  `rel_keep`), the action is still `RESUME_CURRENT` (`sched_quiet`), so `schedule` is
  `schedTail` (`schedule_resume`), which writes only this core's node words and the current SC
  (`schedTail_fp`: the caller's SC is the current one, `current_ok`);
* `activate_thread` and `vcpu::check` of the running caller write nothing (`activate_run`,
  `vcpu_check_run`).

The words between the prefix and `schedule` are bounded by `MidW` (the caller's registers and
state, the timer fields of threads, this core's reprogram, root and min words), which keeps
every other TCB word, node word and object word (`mid_tcb`, `mid_node`, `mid_out`).

No named premises.
-/
import Fl4Proofs.P2.FootTimerIns
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-! ## Word sets between the prefix and `schedule` -/

/-- The registers and the state word of `t`. -/
def TRegW (t b : U64) : Prop := ∃ K : U64, 256 ≤ K.val ∧ K.val ≤ 3328 ∧ b = core.num.U64.wrapping_add t K

/-- `TRegW t`, the timer fields of the threads, the current core's `REPROGRAM`, `TIMER_ROOT`,
`TIMER_MIN` (at `s0`). -/
def MidW (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (t b : U64) : Prop :=
  TRegW t b ∨ (∃ y ∈ T, ∃ K : U64, 3528 ≤ K.val ∧ K.val < 3576 ∧ b = core.num.U64.wrapping_add y K) ∨
    (∃ o : U64, (o.val = 56 ∨ o.val = 104 ∨ o.val = 112) ∧ b = L.nodeAt s0 (L.cpu s0) o)

theorem mid_tcb {s0 s : S} {t : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s0 (L.cpu s0)) (ht : t ∈ T)
    (w : WritesIn st s0 s (MidW st T s0 t)) {y K : U64} (hy : y ∈ T) (hK : K.val < 4096) (h8 : K.val % 8 = 0)
    (h1 : K.val < 3528 ∨ 3576 ≤ K.val) (h2 : y = t → K.val < 256 ∨ 3328 < K.val) :
    L.mem s (core.num.U64.wrapping_add y K) = L.mem s0 (core.num.U64.wrapping_add y K) := by
  refine w.mem_eq (field_aligned (hT y hy) hK h8) ?_
  rintro (⟨K', a1, a2, e⟩ | ⟨z, hz, K', a1, a2, e⟩ | ⟨o, ho, e⟩)
  · exact tcb_word_ne (hT y hy) (hT t ht) hK (by omega) (fun e' => by have := h2 e'; omega) e
  · exact tcb_word_ne (hT y hy) (hT z hz) hK (by omega) (fun _ => by omega) e
  · exact tcb_node_ne hN hy (hT y hy) hK (by omega) e

theorem mid_node {s0 s : S} {t : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s0 (L.cpu s0)) (ht : t ∈ T)
    (w : WritesIn st s0 s (MidW st T s0 t)) {o : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0)
    (hn : o.val ≠ 56 ∧ o.val ≠ 104 ∧ o.val ≠ 112) :
    L.mem s (L.nodeAt s0 (L.cpu s0) o) = L.mem s0 (L.nodeAt s0 (L.cpu s0) o) := by
  refine w.mem_eq (nodeAt_aligned hN ho h8) ?_
  rintro (⟨K', a1, a2, e⟩ | ⟨z, hz, K', a1, a2, e⟩ | ⟨o', ho', e⟩)
  · exact tcb_node_ne hN ht (hT t ht) (by omega) ho e.symm
  · exact tcb_node_ne hN hz (hT z hz) (by omega) ho e.symm
  · have e' := congrArg UScalar.val e
    rw [nodeAt_val hN ho, nodeAt_val hN (by omega)] at e'
    omega

theorem mid_out {s0 s : S} {t b : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s0 (L.cpu s0)) (ht : t ∈ T)
    (hcC : L.cpu s0 ∈ Cs) (w : WritesIn st s0 s (MidW st T s0 t)) (hb : OutsideObjs st T Cs s0 b) :
    L.mem s b = L.mem s0 b := by
  refine w.mem_eq hb.1 ?_
  rintro (⟨K', a1, a2, e⟩ | ⟨z, hz, K', a1, a2, e⟩ | ⟨o', ho', e⟩)
  · exact out_ne_field hb ht (hT t ht) (by omega) (congrArg UScalar.val e).symm
  · exact out_ne_field hb hz (hT z hz) (by omega) (congrArg UScalar.val e).symm
  · exact out_ne_node hb hcC hN (by omega) (congrArg UScalar.val e).symm

/-- Words of the caller only. -/
theorem treg_mid {s0 s s1 : S} {t : U64} (w : WritesIn st s0 s (TRegW t)) : WritesIn st s0 s (MidW st T s1 t) :=
  w.mono fun _ h => Or.inl h

theorem treg_tcb {s0 s : S} {t : U64} (hT : TcbPlaced T) (ht : t ∈ T) (w : WritesIn st s0 s (TRegW t))
    {y K : U64} (hy : y ∈ T) (hK : K.val < 4096) (h8 : K.val % 8 = 0) (h2 : y = t → K.val < 256 ∨ 3328 < K.val) :
    L.mem s (core.num.U64.wrapping_add y K) = L.mem s0 (core.num.U64.wrapping_add y K) := by
  refine w.mem_eq (field_aligned (hT y hy) hK h8) ?_
  rintro ⟨K', a1, a2, e⟩
  exact tcb_word_ne (hT y hy) (hT t ht) hK (by omega) (fun e' => by have := h2 e'; omega) e

/-- The `TRegW` words are footprint words of a thread of this core. -/
theorem treg_foot {s0 : S} {t b : U64} {Lk : List (U64 × Nat)} (ht : t ∈ T) (ha : L.mem s0 (affA t) = L.cpu s0)
    (hb : TRegW t b) : FootLt st T Scs Z Lk s0 b := by
  obtain ⟨K, a1, a2, rfl⟩ := hb
  exact footLt_thr ht ha (by omega) (by omega) (by omega) (by omega)

/-! ## The checks, read back -/

/-- `set_timer_target_ok` passed: `target` is this core's, disarmed or in this core's tree. -/
theorem target_ok_facts {X : S} {c g : U64} (h : localtimer.set_timer_target_ok st X c g = ok true) :
    L.mem X (affA g) = c ∧ (L.mem X (tdA g) = 0#u64 ∨ (L.mem X (thA g)).val >>> 8 = c.val) := by
  unfold localtimer.set_timer_target_ok at h
  rw [aff_ok] at h; simp only [bind_ok] at h
  by_cases ca : (L.mem X (affA g) != c) = true
  · rw [if_pos ca] at h; simp at h
  rw [if_neg ca] at h
  have ha : L.mem X (affA g) = c := by simp only [bne_iff_ne, ne_eq, not_not] at ca; exact ca
  refine ⟨ha, ?_⟩
  rw [eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) X g)] at h; simp only [bind_ok] at h
  by_cases hd : L.mem X (tdA g) = 0#u64
  · exact Or.inl hd
  right
  rw [if_neg hd] at h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  unfold localtimer.core_of at h
  rw [eq_of_spec_fd (obj.Tcb.timer_height.val (L := L) X g)] at h
  simp only [bind_ok] at h
  obtain ⟨i1, e1, h⟩ := bind_eq_ok h
  have hc : i1 = c := by simpa using ok_inj_ff h
  subst hc
  have hs : ((L.mem X (thA g)) >>> 8#i32 : Result U64) ⦃ v => v.val = (L.mem X (thA g)).val >>> 8 ⦄ := by
    step as ⟨v, hv1, hv2⟩
    exact hv1
  rw [e1, WP.spec_ok] at hs
  exact hs.symm

/-- `may_run_here` passed: no yield to complete. -/
theorem mrh_yield {X : S} {c t : U64} (h : localtimer.may_run_here st X c t = ok true) :
    L.mem X (yieldA t) = 0#u64 := by
  unfold localtimer.may_run_here at h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  split at h
  · simp at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  split at h
  swap
  · simp at h
  obtain ⟨i1, -, h⟩ := bind_eq_ok h
  split at h
  swap
  · simp at h
  obtain ⟨i2, e2, h⟩ := bind_eq_ok h
  split at h
  · rename_i hy
    rw [eq_of_spec_fd (obj.Tcb.yield_to.spec (L := L) X t)] at e2
    rw [ok_inj_ff e2]; exact hy
  · simp at h

theorem sq_true {X : S} {c : U64} (h : localtimer.sched_quiet st X c = ok true) :
    L.actionW X = sched.ACTION_RESUME_CURRENT := by
  unfold localtimer.sched_quiet at h
  rw [eq_of_spec_fd (sched.action.spec (L := L) X)] at h; simp only [bind_ok] at h
  by_cases ha : L.actionW X = sched.ACTION_RESUME_CURRENT
  · exact ha
  · rw [if_neg ha] at h; simp at h

/-- `timer_due` declined: nothing of this core's tree is due at `now`. -/
theorem td_false {X : S} {now : U64} (h : localtimer.timer_due st X (L.cpu X) now = ok false) :
    NoDueT st X now := by
  unfold localtimer.timer_due at h
  rw [eq_of_spec_fd (obj.node_get.spec (L := L) X _ _)] at h; simp only [bind_ok] at h
  rw [eq_of_spec_fd (obj.Tcb.is_null.spec _)] at h; simp only [bind_ok] at h
  unfold NoDueT
  by_cases h0 : L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) = 0#u64
  · exact Or.inl h0
  right
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at h
  rw [eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) X _)] at h; simp only [bind_ok] at h
  have h' : ¬ (L.mem X (tdA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) ≤ now) := by
    simpa using ok_inj_ff h
  scalar_tac

/-- Nothing of this core's release queue is ready (`awaken_loop_none`'s condition). -/
def RelNone (st : machine.Store S) [L : LawfulStore st] (X : S) : Prop :=
  L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = 0#u64 ∨
    ¬ ((L.refill X (L.mem X (scA (L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD))))
        (L.rhead X (L.mem X (scA (L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD)))))).time ≤
      L.curTime X)

theorem rel_false {X : S} (h : localtimer.release_due st X (L.cpu X) = ok false) : RelNone st X := by
  unfold localtimer.release_due at h
  rw [eq_of_spec_fd (obj.node_get.spec (L := L) X _ _)] at h; simp only [bind_ok] at h
  rw [eq_of_spec_fd (obj.Tcb.is_null.spec _)] at h; simp only [bind_ok] at h
  unfold RelNone
  by_cases h0 : L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = 0#u64
  · exact Or.inl h0
  right
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at h
  rw [eq_of_spec_fd (obj.Tcb.sc.spec (L := L) X _)] at h; simp only [bind_ok] at h
  rw [eq_of_spec_fd (sporadic.ready.spec (L := L) X _)] at h
  simpa using ok_inj_ff h

/-! ## Carrying the checks to the `schedule` state -/

/-- `NoDueT` across writes of the caller's registers and state. -/
theorem nodue_keep {X Y : S} {t now : U64} (hT : TcbPlaced T) (hN : NodePlaced st T X (L.cpu X)) (ht : t ∈ T)
    (hm : Tz T (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) (w : WritesIn st X Y (TRegW t))
    (h : NoDueT st X now) : NoDueT st Y now := by
  unfold NoDueT at h ⊢
  have eA : L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN = L.nodeAt X (L.cpu X) layout.node.TIMER_MIN := by
    rw [w.2.1, nodeAt_of_ksb w.1]
  have em : L.mem Y (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) =
      L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) := by
    refine w.mem_eq (nodeAt_aligned hN (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])) ?_
    rintro ⟨K, a1, a2, e⟩
    exact tcb_node_ne hN ht (hT t ht) (by omega) (by simp [layout.node.TIMER_MIN]) e.symm
  rw [eA, em]
  rcases hm with h0 | hmT
  · exact Or.inl h0
  rcases h with h | h
  · exact Or.inl h
  right
  have e : L.mem Y (tdA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) =
      L.mem X (tdA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) :=
    treg_tcb (K := 3528#u64) hT ht w hmT (by simp) (by simp) (fun _ => by simp)
  rw [e]; exact h

/-- `RelNone` across `MidW` writes, under the invariant. -/
theorem rel_keep {X Y : S} {t : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X) (ht : t ∈ T)
    (w : WritesIn st X Y (MidW st T X t)) (h : RelNone st X) : RelNone st Y := by
  obtain ⟨⟨Q, R, hq⟩, hB, hX, -, hS⟩ := hI
  have hT := hq.tcbs
  have hcC := hq.cur
  have hN := hq.nodes _ hcC
  have eA : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt X (L.cpu X) o := fun o => by rw [w.2.1, nodeAt_of_ksb w.1]
  have eh : L.mem Y (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) :=
    mid_node hT hN ht w (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])
  have ect : L.curTime Y = L.curTime X := by
    unfold LawfulStore.curTime LawfulStore.nodeA
    rw [eA]
    exact mid_node hT hN ht w (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME])
  unfold RelNone at h ⊢
  rw [ect, eA, eh]
  generalize hh : L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = h0 at h ⊢
  rcases h with h | h
  · exact Or.inl h
  by_cases h00 : h0 = 0#u64
  · exact Or.inl h00
  right
  have hrel := hq.release _ hcC
  have hmem : h0 ∈ R (L.cpu X) := by
    have e := hrel.head
    change L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = _ at e
    rw [hh] at e
    cases hR : R (L.cpu X) with
    | nil => rw [hR] at e; exact absurd e h00
    | cons x xs => rw [hR] at e; simp only [List.headD_cons] at e; subst e; simp
  have hhT : h0 ∈ T := hq.memTR hcC hmem
  have esc : L.mem Y (scA h0) = L.mem X (scA h0) := by
    rw [scA_eq]
    exact mid_tcb hT hN ht w hhT (by simp) (by simp) (by simp) (fun _ => by simp)
  rw [esc]
  have haff : L.mem X (affA h0) = L.cpu X := hq.inR _ hcC h0 hmem
  have hrb : (L.mem X (inqA h0) &&& sched.Q_RELEASE) ≠ 0#u64 := (hq.released h0 hhT).2 (by rw [haff]; exact hmem)
  have hsc0 : L.mem X (scA h0) ≠ 0#u64 := hB.r h0 hhT hrb
  have hscS : L.mem X (scA h0) ∈ Scs := (hX.2.2.bound h0 hhT hsc0).1
  have hAc : L.mem X (scA h0) ∈ Ac := hB.sact h0 hhT (Or.inr (Or.inl hrb)) hsc0
  generalize hsc : L.mem X (scA h0) = sc at h hscS hAc ⊢
  have hmax : L.rmax X sc ≠ 0#u64 := (hS.act sc hscS).1 hAc
  obtain ⟨hwf, -, hin⟩ := hS.all sc hscS
  have wf := hwf hmax
  obtain ⟨h8, hm, hfit⟩ := wf.bounds
  obtain ⟨-, -, -, hhd, -, hri⟩ := wf.inside
  have keep : ∀ b, Aligned b → InSC sc (Z sc) b → L.mem Y b = L.mem X b := fun b hb hi =>
    mid_out hT hN ht hcC w (hq.omega b (hS.sub b (hin b hb hi)))
  have hmin := wf.min_le
  simp at hmin
  have e1 : L.rhead Y sc = L.rhead X sc := keep _ (by unfold Aligned; rw [hhd]; omega) ⟨by rw [hhd]; omega, by rw [hhd]; omega⟩
  obtain ⟨r1, r2, r3⟩ := hri (L.rhead X sc) wf.head_lt
  have e2 : L.mem Y (rtA sc (L.rhead X sc)) = L.mem X (rtA sc (L.rhead X sc)) :=
    keep _ (by unfold Aligned; rw [r1]; omega) ⟨by rw [r1]; omega, by rw [r1]; omega⟩
  simp only [LawfulStore.refill] at h ⊢
  rw [e1, e2]
  exact h

/-! ## Schedulability, `set_thread_state`, the reply -/

theorem is_sched_of {X : S} {t : U64} (h1 : Runnable (L.mem X (stA t))) (h2 : L.mem X (scA t) ≠ 0#u64)
    (h3 : (L.mem X (inqA t) &&& sched.Q_RELEASE) = 0#u64) (h4 : L.rmax X (L.mem X (scA t)) ≠ 0#u64) :
    sched.is_schedulable st X t = ok true := by
  unfold Runnable at h1
  unfold sched.is_schedulable
  rw [eq_of_spec_fd (sched.is_runnable.spec (L := L) X t), decide_eq_true h1]
  simp only [bind_ok, ↓reduceIte]
  rw [eq_of_spec_fd (obj.Tcb.sc.spec (L := L) X t)]
  simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Sc.is_null.spec _), decide_eq_false h2]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  unfold sporadic.sc_active
  rw [eq_of_spec_fd (obj.Sc.refill_max.spec (L := L) X _)]
  have h4' : L.rmax X (L.mem X (scA t)) > 0#u64 := by
    have : (L.rmax X (L.mem X (scA t))).val ≠ 0 := fun e => h4 (UScalar.eq_of_val_eq (by simpa using e))
    scalar_tac
  simp only [bind_ok, h4', decide_true, ↓reduceIte]
  rw [eq_of_spec_fd (sched.in_release_queue.spec (L := L) X t)]
  simp [h3]

/-- `set_thread_state` of a thread schedulable after the write is the write. -/
theorem sts_sch {X Y : S} {t v : U64} (hs : sched.is_schedulable st (L.wr X (stA t) v) t = ok true)
    (e : sched.set_thread_state st X t v = ok Y) : Y = L.wr X (stA t) v := by
  unfold sched.set_thread_state at e
  rw [eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) X t v)] at e
  simp only [bind_ok] at e
  rw [schedule_tcb_sch _ _ hs] at e
  exact (ok_inj_ff e).symm

/-- `reply_success_empty` writes the caller's `BADGE` and `MSG_INFO`. -/
theorem reply_tr {X Y : S} {t : U64} (ht : TcbAddr t) (h : msg.reply_success_empty st X t = ok Y) :
    WritesIn st X Y (TRegW t) := by
  unfold msg.reply_success_empty msg.set_msg_info at h
  obtain ⟨s1, e1, h⟩ := bind_eq_ok h
  obtain ⟨mi, -, h⟩ := bind_eq_ok h
  obtain ⟨wv, -, h⟩ := bind_eq_ok h
  have h1 := obj.Tcb.set_reg.wrK (L := L) X t layout.reg.BADGE 0#u64 ht (by simp [layout.reg.BADGE, layout.reg.RDI])
  rw [e1, WP.spec_ok] at h1
  obtain ⟨K1, hK1, rfl⟩ := h1
  have h2 := obj.Tcb.set_reg.wrK (L := L) (L.wr X (core.num.U64.wrapping_add t K1) 0#u64) t layout.reg.MSG_INFO wv ht
    (by simp [layout.reg.MSG_INFO, layout.reg.RSI])
  rw [h, WP.spec_ok] at h2
  obtain ⟨K2, hK2, rfl⟩ := h2
  have v1 : K1.val = 256 := by rw [hK1]; simp [layout.reg.BADGE, layout.reg.RDI]
  have v2 : K2.val = 264 := by rw [hK2]; simp [layout.reg.MSG_INFO, layout.reg.RSI]
  exact ((writesIn_wr (field_aligned ht (by omega) (by omega))).trans
    (writesIn_wr (field_aligned ht (by omega) (by omega)))).mono fun b hb => by
      rcases hb with e | e
      · exact ⟨K1, by omega, by omega, e⟩
      · exact ⟨K2, by omega, by omega, e⟩

/-! ## `schedule` with nothing due and the action `RESUME_CURRENT` -/

section sched
variable {A : Type _} (ar : machine.Arch A)

theorem schedule_resume (s : S) (a : A)
    (hT : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) <
        L.mem s (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
    (hR : RelNone st s) (ha : L.actionW s = sched.ACTION_RESUME_CURRENT) :
    sched.schedule st ar s a = schedTail (st := st) ar s a := by
  unfold sched.schedule
  rw [awaken_none ar s a hT hR]; simp only [bind_ok, uncurry_apply_pair]
  rw [check_domain_time_one]; simp only [bind_ok]
  rw [eq_of_spec_fd (sched.action.spec (L := L) s), ha]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem SCq.agree {X Y : S} {c : U64} {z : Nat} (h : SCq st X Ω c z) (ag : ∀ b ∈ Ω, L.mem Y b = L.mem X b) :
    SCq st Y Ω c z := by
  have em : L.rmax Y c = L.rmax X c := ag _ (h.2.1 _ h.2.2.2.2 h.2.2.2.1)
  exact ⟨fun hm => (h.1 (em ▸ hm)).agree fun b hb hin => ag b (h.2.1 b hb hin), h.2.1, h.2.2⟩

set_option maxHeartbeats 1600000 in
/-- **`schedTail` when the current thread runs on the current SC** writes only words of any `B`
holding this core's node words but `CUR_THREAD` and the current SC's words. -/
theorem schedTail_fp (hA : P0.ArchTotal ar) (X : S) (a : A) {zc : Nat} {B : U64 → Prop}
    (hcC : L.cpu X ∈ Cs) (hN : NodePlaced st T X (L.cpu X)) (hT : TcbPlaced T)
    (homega : ∀ b ∈ Ω, OutsideObjs st T Cs X b) (hct : L.curW X ∈ T)
    (hsame : L.mem X (scA (L.curW X)) = L.cscW X) (hc : SCq st X Ω (L.cscW X) zc)
    (hBn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 0 → B (L.nodeAt X (L.cpu X) o))
    (hBc : ∀ b, Aligned b → InSC (L.cscW X) zc b → B b) :
    schedTail (st := st) ar X a ⦃ r => WritesIn st X r.1 B ⦄ := by
  unfold schedTail
  refine WP.spec_bind (sched.set_action.spec X _) fun X1 e1 => ?_
  have aA : Aligned (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) :=
    nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val])
  have kX : L.ksb X1 = L.ksb X := by rw [e1, L.ksb_wr]
  have cX : L.cpu X1 = L.cpu X := by rw [e1, LawfulStore.cpu_wr]
  have eN : ∀ o, L.nodeAt X1 (L.cpu X1) o = L.nodeAt X (L.cpu X) o := fun o => by rw [cX, nodeAt_of_ksb kX]
  have w0 : WritesIn st X X1 B := by
    rw [e1]
    exact (writesIn_wr aA).mono fun b hb => hb ▸ hBn _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)
  have agN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 →
      L.mem X1 (L.nodeAt X (L.cpu X) o) = L.mem X (L.nodeAt X (L.cpu X) o) := by
    intro o ho h8 h16
    rw [e1]
    refine mem_wr_ne' aA (nodeAt_aligned hN ho h8) fun e => h16 ?_
    have e' := congrArg UScalar.val e
    rw [nodeAt_val hN (by rw [act_val]; omega), nodeAt_val hN ho, act_val] at e'
    omega
  have agΩ : ∀ b ∈ Ω, L.mem X1 b = L.mem X b := fun b hb => by
    rw [e1]
    exact mem_wr_ne' aA (homega b hb).1 fun e =>
      out_ne_node (homega b hb) hcC hN (by rw [act_val]; omega) (congrArg UScalar.val e)
  have ecur : L.curW X1 = L.curW X := by
    unfold LawfulStore.curW; rw [eN]
    exact agN _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
  have ecs : L.cscW X1 = L.cscW X := by
    unfold LawfulStore.cscW LawfulStore.nodeA; rw [eN]
    exact agN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have esc : L.mem X1 (scA (L.curW X)) = L.mem X (scA (L.curW X)) := by
    rw [e1, scA_eq]
    exact mem_wr_ne' aA (field_aligned (hT _ hct) (by simp) (by simp))
      (node_ne_field hN (by rw [act_val]; omega) hct (hT _ hct) (by simp))
  have hsame1 : L.mem X1 (scA (L.mem X1 (L.nodeA X1 layout.node.CUR_THREAD))) =
      L.mem X1 (L.nodeA X1 layout.node.CUR_SC) := by
    show L.mem X1 (scA (L.curW X1)) = L.cscW X1
    rw [ecur, esc, hsame, ecs]
  have hc1 : SCq st X1 Ω (L.mem X1 (L.nodeA X1 layout.node.CUR_SC)) zc := by
    show SCq st X1 Ω (L.cscW X1) zc
    rw [ecs]; exact SCq.agree hc agΩ
  have hN1 : NodePlaced st T X1 (L.cpu X1) := by rw [cX]; exact hN.ksb kX
  have hΩ1 : ∀ b ∈ Ω, OutsideObjs st T Cs X1 b := fun b hb => (homega b hb).ksb kX
  have hB1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 0 → B (L.nodeA X1 o) := fun o h1 h2 h3 => by
    unfold LawfulStore.nodeA; rw [eN]; exact hBn o h1 h2 h3
  refine WP.spec_bind (sched.switch_sched_context.fp hA X1 a (zt := zc) (zc := zc) (B := B) (cX ▸ hcC) hN1 hΩ1 hc1
    (fun hne => absurd hsame1 hne)
    (hB1 _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
    (hB1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
    (hB1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
    (fun hne => absurd hsame1 hne)
    (fun b hb h => by
      have e : L.mem X1 (L.nodeA X1 layout.node.CUR_SC) = L.cscW X := ecs
      rw [e] at h
      refine hBc b hb ?_
      rcases h with h | rfl
      · exact h.inSC
      · exact hc.2.2.1.1)) ?_
  rintro ⟨s5, a3⟩ ⟨w5, -⟩
  try simp only [WP.uncurry'_pair]
  have hN5 : NodePlaced st T s5 (L.cpu s5) := by rw [w5.2.1]; exact hN1.ksb w5.1
  have eN5 : ∀ o, L.nodeAt s5 (L.cpu s5) o = L.nodeAt X (L.cpu X) o := fun o => by
    rw [w5.2.1, nodeAt_of_ksb w5.1, eN]
  step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
  step with obj.node_get.spec as ⟨i, _⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => WritesIn st s5 r.1 B) ?_ ?_
  · split
    · refine WP.spec_bind (sched.set_next_interrupt.fp hA s5 a3 (B := B) hN5 (by
        rw [eN5]; exact hBn _ (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED]))) ?_
      rintro ⟨s6, a4⟩ w6
      try simp only [WP.uncurry'_pair]
      refine WP.spec_bind (obj.node_set.spec s6 c _ _) fun s7 e7 => ?_
      subst e7
      simp only [WP.spec_ok]
      have e : L.nodeAt s6 c layout.node.REPROGRAM = L.nodeAt X (L.cpu X) layout.node.REPROGRAM := by
        rw [ec, nodeAt_of_ksb w6.1, eN5]
      have w7 : WritesIn st s6 (L.wr s6 (L.nodeAt s6 c layout.node.REPROGRAM) 0#u64) B := by
        rw [e]
        exact (writesIn_wr (nodeAt_aligned hN (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM]))).mono fun b hb => hb ▸ hBn _ (by simp [layout.node.REPROGRAM])
            (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      exact (w6.trans w7).mono fun b hb => hb.elim id id
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rintro ⟨s6, a4⟩ w6
  try simp only [WP.uncurry'_pair]
  have eI : L.nodeAt s6 (L.cpu s6) layout.node.IPI_PENDING = L.nodeAt X (L.cpu X) layout.node.IPI_PENDING := by
    rw [w6.2.1, nodeAt_of_ksb w6.1, eN5]
  have hBI : B (L.nodeAt s6 (L.cpu s6) layout.node.IPI_PENDING) := by
    rw [eI]
    exact hBn _ (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING])
  have hN6 : NodePlaced st T s6 (L.cpu s6) := by rw [w6.2.1]; exact hN5.ksb w6.1
  refine WP.spec_mono (smp.send_pending.fp hA s6 a4 (B := B) hN6 hBI) fun r hr => ?_
  exact ((w0.trans w5).trans (w6.trans hr)).mono fun b hb => by
    rcases hb with (h | h) | (h | h) <;> exact h

/-- `activate_thread` of a running current thread with no yield writes nothing. -/
theorem activate_run (X : S) (a : A) (hy : L.mem X (yieldA (L.curW X)) = 0#u64)
    (hs : L.mem X (stA (L.curW X)) = sched.TS_RUNNING) : sched.activate_thread st ar X a = ok (X, a) := by
  unfold sched.activate_thread
  rw [cur_thread_ok]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.yield_to.spec (L := L) X _), hy]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, uncurry_apply_pair]
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) X _), hs]
  have hne : sched.TS_RUNNING ≠ sched.TS_RESTART := by unfold sched.TS_RUNNING sched.TS_RESTART; decide
  simp only [bind_ok, hne, ↓reduceIte]

/-- `vcpu::check` of a thread not running a VM writes nothing. -/
theorem vcpu_check_run (X : S) (a : A) {t : U64} (hs : L.mem X (stA t) = sched.TS_RUNNING) :
    vcpu.check st ar X a t = ok (X, a) := by
  unfold vcpu.check
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) X _), hs]
  have hne : (sched.TS_RUNNING != sched.TS_RUNNING_VM) = true := by
    unfold sched.TS_RUNNING sched.TS_RUNNING_VM; decide
  simp only [bind_ok, hne, ↓reduceIte]

end sched

section main
variable {A : Type _} (ar : machine.Arch A)

set_option maxHeartbeats 16000000 in
/-- **An accepted `TCB_SetTimer` local path writes only its footprint** `FootLt` (any `Lk`; the
path locks only CSpace slots, which it does not write), from a state with the P1 invariant. -/
theorem set_timer_accept_foot (hA : P0.ArchTotal ar) {Lk : List (U64 × Nat)} {s s' : S} {a a' : A} {n : I64}
    {target : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (htg : target ∈ T)
    (h : localtimer.handle_set_timer_local st ar s a n target = ok (true, s', a')) :
    InFootLt st T Scs Z Lk s s' := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  unfold localtimer.handle_set_timer_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨cpu, ecpu, h⟩ := bind_eq_ok h
  rw [L.cur_cpu_eq] at ecpu
  have hcpu : cpu = L.cpu s := (ok_inj_ff ecpu).symm
  subst hcpu
  obtain ⟨info, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases cn : (n != fl4_abi.syscall.SysCall) = true
  · rw [if_pos cn] at h; simp at h
  rw [if_neg cn] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  by_cases c2 : (info.label != fl4_abi.label.TCBSetTimer) = true
  · rw [if_pos c2] at h; simp at h
  rw [if_neg c2] at h
  by_cases c3 : (info.extra_caps != 0#u64) = true
  · rw [if_pos c3] at h; simp at h
  rw [if_neg c3] at h
  by_cases c4 : info.length < 2#u64
  · rw [if_pos c4] at h; simp at h
  rw [if_neg c4] at h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  by_cases c5 : (i2 != sched.TS_RUNNING) = true
  · rw [if_pos c5] at h; simp at h
  rw [if_neg c5] at h
  have hrun : i2 = sched.TS_RUNNING := by simp only [bne_iff_ne, ne_eq, not_not] at c5; exact c5
  obtain ⟨b2, eb2, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b3, eb3, h⟩ := bind_eq_ok h
  cases b3
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨nx, -, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  try rw [insn_len_eq] at es1
  obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, enow, h⟩ := bind_eq_ok h
  obtain ⟨dl, -, h⟩ := bind_eq_ok h
  obtain ⟨bd, -, h⟩ := bind_eq_ok h
  obtain ⟨cns, -, h⟩ := bind_eq_ok h
  obtain ⟨b4, -, h⟩ := bind_eq_ok h
  cases b4
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b5, eb5, h⟩ := bind_eq_ok h
  cases b5
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨b6, eb6, h⟩ := bind_eq_ok h
  cases b6
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨tail, hdl⟩ : (do
      let s3 ← sched.set_thread_state st s2 t sched.TS_RESTART
      let s4 ← timer.insert st s3 target dl bd
      let s5 ← msg.reply_success_empty st s4 t
      let s6 ← sched.set_thread_state st s5 t sched.TS_RUNNING
      let (s7, a2) ← sched.schedule st ar s6 a1
      let (s8, a3) ← sched.activate_thread st ar s7 a2
      let t1 ← sched.cur_thread st s8
      let (s9, a4) ← vcpu.check st ar s8 a3 t1
      ok (true, s9, a4)) = ok (true, s', a') ∧ (dl = 0#u64 ∨ now < dl) := by
    by_cases cd : (dl != 0#u64) = true
    · rw [if_pos cd] at h
      by_cases cd2 : dl <= now
      · rw [if_pos cd2] at h; simp at h
      · rw [if_neg cd2] at h; exact ⟨h, Or.inr (by scalar_tac)⟩
    · rw [if_neg cd] at h
      refine ⟨h, Or.inl ?_⟩
      simp only [bne_iff_ne, ne_eq, not_not] at cd; exact cd
  clear h
  obtain ⟨s3, es3, h⟩ := bind_eq_ok tail
  obtain ⟨s4, es4, h⟩ := bind_eq_ok h
  obtain ⟨s5, es5, h⟩ := bind_eq_ok h
  obtain ⟨s6, es6, h⟩ := bind_eq_ok h
  obtain ⟨⟨s7, a2⟩, es7, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s8, a3⟩, es8, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨t1, et1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s9, a4⟩, es9, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq, true_and] at e
  obtain ⟨rfl, rfl⟩ := e
  -- the checks
  have etc : L.curW s = t := by rw [cur_thread_ok] at et; exact ok_inj_ff et
  have htT : t ∈ T := etc ▸ hcT
  have ht' := hT t htT
  obtain ⟨hmr, hsct, hcore⟩ := current_ok_true eb1
  obtain ⟨-, haff, -, -⟩ := may_run_here_true hmr
  have hy0 : L.mem s (yieldA t) = 0#u64 := mrh_yield hmr
  have ecsc' : L.cscW s = csc := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at ecsc; exact ok_inj_ff ecsc
  obtain ⟨haffg, hown⟩ := target_ok_facts eb
  have hact : L.actionW s = sched.ACTION_RESUME_CURRENT := sq_true eb3
  have hs := sched.is_schedulable.spec' (L := L) s t
  rw [eb2, WP.spec_ok] at hs
  obtain ⟨-, hsc0, hrel0, hmax0⟩ := hs rfl
  rw [hsct] at hsc0 hmax0
  -- the invariant at the entry
  have hX := hI.2.2.1
  have hS := hI.2.2.2.2
  have hO := hX.1
  have hcs : L.cscW s ∈ Scs := hX.2.2.cur
  have hcq : SCq st s Ω csc (Z csc) := by
    rw [← ecsc']
    obtain ⟨hP, hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    obtain ⟨a1', a2', a3'⟩ := maxA_facts hO hcs
    exact ⟨(hS.all _ hcs).1, fun b hb hi => hS.sub _ ((hS.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩, by unfold Aligned; rw [hv, hcv]; omega⟩, ⟨a2', a3'⟩, a1'⟩
  have hcsS : csc ∈ Scs := ecsc' ▸ hcs
  have hownS : L.mem s (tdA target) = 0#u64 ∨ FootLtArmed st s (L.cpu s) target := by
    by_cases hd : L.mem s (tdA target) = 0#u64
    · exact Or.inl hd
    · exact Or.inr ⟨hd, hown.resolve_left hd⟩
  -- the prefix
  obtain ⟨et2, tK, oK⟩ := inv_prefix ar hT hN hcC et htT es1 eu hA
  obtain ⟨KF, hKF, hW⟩ := lt_prefix ar hT hN htT es1 eu hA
  have uK : ∀ {u K : U64}, u ∈ T → K.val < 4096 → K.val % 8 = 0 → (u = t → K.val ≠ 392) →
      L.mem s2 (core.num.U64.wrapping_add u K) = L.mem s (core.num.U64.wrapping_add u K) :=
    fun huT hK h8 hne => lt_tcbK hKF hT hN htT hW huT hK h8 hne
  have k2 : L.ksb s2 = L.ksb s := hW.1
  have c2 : L.cpu s2 = L.cpu s := hW.2.1
  have hN2 : NodePlaced st T s2 (L.cpu s2) := by rw [c2]; exact hN.ksb k2
  have e2N : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c2, nodeAt_of_ksb k2]
  have pre_node : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 →
      L.mem s2 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h40 h48
    refine hW.mem_eq (nodeAt_aligned hN ho h8) ?_
    rintro (e | e | e)
    · exact tcb_node_ne hN htT ht' (by omega) ho e.symm
    · have e' := congrArg UScalar.val e
      unfold ctA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CUR_TIME])] at e'
      simp [layout.node.CUR_TIME] at e'; omega
    · have e' := congrArg UScalar.val e
      unfold cnA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CONSUMED])] at e'
      simp [layout.node.CONSUMED] at e'; omega
  have f02 : WritesIn st s s2 (FootLt st T Scs Z Lk s) := hW.mono fun b hb => by
    rcases hb with rfl | rfl | rfl
    · exact footLt_thr htT haff (by omega) (by omega) (by omega) (by omega)
    · exact footLt_node (by simp [layout.node.CUR_TIME])
    · exact footLt_node (by simp [layout.node.CONSUMED])
  have agΩ2 : ∀ b ∈ Ω, L.mem s2 b = L.mem s b := fun b hb => oK b (h0.omega b hb)
  have hB2 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s2 := by
    have hI1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := by
      have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
        ht' (by simp [layout.reg.FAULT_IP])
      rw [es1, WP.spec_ok] at hW1
      obtain ⟨K, hK, e1⟩ := hW1
      have hK' : K.val = 392 := by rw [hK]; simp [layout.reg.FAULT_IP]
      rw [e1]; exact (regW_all (BXI.blk hI) htT (by omega) (by omega) (by omega)).1
    have := sched.update_timestamp.bxc hA s1 a (BlkOK.bxi hI1)
    rw [eu, WP.spec_ok] at this
    try simp only [WP.uncurry'_pair] at this
    exact this.1.1
  -- schedulable after a state write of the caller
  have sA : Aligned (stA t) := by rw [stA_eq]; exact field_aligned ht' (by simp) (by simp)
  have hmaxΩ : maxA csc ∈ Ω := hcq.2.1 _ hcq.2.2.2.2 hcq.2.2.2.1
  have schW : ∀ (X : S) (v : U64), L.mem X (scA t) = csc → L.mem X (inqA t) = L.mem s (inqA t) →
      (∀ b ∈ Ω, L.mem X b = L.mem s b) → Runnable v → sched.is_schedulable st (L.wr X (stA t) v) t = ok true := by
    intro X v e1 e2 e3 hv
    have nsc : stA t ≠ scA t := by
      rw [stA_eq, scA_eq]; exact tcb_word_ne ht' ht' (by simp) (by simp) (fun _ => by simp)
    have niq : stA t ≠ inqA t := by
      rw [stA_eq]; exact tcb_word_ne ht' ht' (K2 := 3592#u64) (by simp) (by simp) (fun _ => by simp)
    have nmx : stA t ≠ maxA csc := fun e' =>
      out_ne_field (h0.omega _ hmaxΩ) htT ht' (K := 3328#u64) (by simp) (by rw [← stA_eq, e'])
    have aS : Aligned (scA t) := by rw [scA_eq]; exact field_aligned ht' (by simp) (by simp)
    have aQ : Aligned (inqA t) := field_aligned (K := 3592#u64) ht' (by simp) (by simp)
    apply is_sched_of
    · rw [L.mem_wr_same sA]; exact hv
    · rw [mem_wr_ne' sA aS nsc, e1]; exact hsc0
    · rw [mem_wr_ne' sA aQ niq, e2]; exact hrel0
    · rw [mem_wr_ne' sA aS nsc, e1]
      show L.mem _ (maxA csc) ≠ 0#u64
      rw [mem_wr_ne' sA hcq.2.2.2.2 nmx, e3 _ hmaxΩ]; exact hmax0
  -- `s2 → s3`: the restart
  have est : stA t = core.num.U64.wrapping_add t 3328#u64 := stA_eq t
  have hrs2 : L.mem s2 (stA t) = sched.TS_RUNNING := by
    rw [est, uK htT (by simp) (by simp) (fun _ => by simp), ← est]
    rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s t)] at ei2
    rw [ok_inj_ff ei2]; exact hrun
  have sc2 : L.mem s2 (scA t) = csc := by
    rw [scA_eq, uK htT (by simp) (by simp) (fun _ => by simp), ← scA_eq, hsct]
  have iq2 : L.mem s2 (inqA t) = L.mem s (inqA t) := uK (K := 3592#u64) htT (by simp) (by simp) (fun _ => by simp)
  have e3 : s3 = L.wr s2 (stA t) sched.TS_RESTART := sts_sch (schW s2 _ sc2 iq2 agΩ2 (Or.inr (Or.inl rfl))) es3
  have w23 : WritesIn st s2 s3 (TRegW t) := by
    rw [e3]; exact (writesIn_wr sA).mono fun b e => ⟨3328#u64, by simp, by simp, by rw [e, est]⟩
  have hnb : ¬ Blocked (L.mem s2 (stA t)) := by
    rw [hrs2]; unfold Blocked
    simp [sched.TS_RUNNING, sched.TS_BLOCKED_ON_SEND, sched.TS_BLOCKED_ON_RECV, sched.TS_BLOCKED_ON_NTFN]
  have hnr : L.mem s2 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY := by
    rw [hrs2]; simp [sched.TS_RUNNING, sched.TS_BLOCKED_ON_REPLY]
  have hB3 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 :=
    (sched.set_thread_state.restart_ok (Es := ∅) (BXI.blk hB2) htT hnb hnr es3).1
  have k03 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 → (y = t → K.val < 256 ∨ 3328 < K.val) →
      L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y K hy hK h8 hne
    rw [treg_tcb hT htT w23 hy hK h8 hne, uK hy hK h8 (fun e => by have := hne e; omega)]
  have c3 : L.cpu s3 = L.cpu s := w23.2.1.trans c2
  have e3N : ∀ o, L.nodeAt s3 (L.cpu s3) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [c3, nodeAt_of_ksb (w23.1.trans k2)]
  have armed30 : ∀ {y : U64}, y ∈ T → FootLtArmed st s3 (L.cpu s3) y → FootLtArmed st s (L.cpu s) y := by
    intro y hy ⟨a1', a2'⟩
    have e1 : L.mem s3 (tdA y) = L.mem s (tdA y) := k03 (K := 3528#u64) hy (by simp) (by simp) (fun _ => by simp)
    have e2 : L.mem s3 (thA y) = L.mem s (thA y) := k03 (K := 3568#u64) hy (by simp) (by simp) (fun _ => by simp)
    rw [e1] at a1'; rw [e2, c3] at a2'
    exact ⟨a1', a2'⟩
  -- `s3 → s4`: the insert
  have hown3 : L.mem s3 (tdA target) = 0#u64 ∨ (L.mem s3 (thA target)).val >>> 8 = (L.cpu s3).val := by
    have e1 : L.mem s3 (tdA target) = L.mem s (tdA target) :=
      k03 (K := 3528#u64) htg (by simp) (by simp) (fun _ => by simp)
    have e2 : L.mem s3 (thA target) = L.mem s (thA target) :=
      k03 (K := 3568#u64) htg (by simp) (by simp) (fun _ => by simp)
    rw [e1, e2, c3]; exact hown
  obtain ⟨hB4, w34, hnd⟩ := insert_local hB3 htg hown3 es4
  have f34 : WritesIn st s3 s4 (FootLt st T Scs Z Lk s) := w34.mono fun b hb => by
    rcases hb with ⟨o, ho, rfl⟩ | ⟨K, a1', a2', rfl⟩ | ⟨y, hy, -, harm, K, a1', a2', rfl⟩
    · rw [e3N]; exact footLt_node (by omega)
    · exact footLt_thr_tmr htg haffg a1' a2' hownS
    · exact footLt_tmr hy (armed30 hy harm) a1' a2'
  have m34 : WritesIn st s3 s4 (MidW st T s2 t) := w34.mono fun b hb => by
    rcases hb with ⟨o, ho, rfl⟩ | ⟨K, a1', a2', rfl⟩ | ⟨y, hy, -, -, K, a1', a2', rfl⟩
    · exact Or.inr (Or.inr ⟨o, ho, by rw [w23.2.1, nodeAt_of_ksb w23.1]⟩)
    · exact Or.inr (Or.inl ⟨target, htg, K, a1', a2', rfl⟩)
    · exact Or.inr (Or.inl ⟨y, hy, K, by omega, a2', rfl⟩)
  -- `s4 → s5 → s6`: the reply, the caller running again
  have w45 : WritesIn st s4 s5 (TRegW t) := reply_tr ht' es5
  have w25 : WritesIn st s2 s5 (MidW st T s2 t) := ((treg_mid w23).trans1 m34).trans1 (treg_mid w45)
  have hcC2 : L.cpu s2 ∈ Cs := c2 ▸ hcC
  have agΩ5 : ∀ b ∈ Ω, L.mem s5 b = L.mem s b := fun b hb =>
    (mid_out hT hN2 htT hcC2 w25 ((h0.omega b hb).ksb k2)).trans (agΩ2 b hb)
  have sc5 : L.mem s5 (scA t) = csc := by
    rw [scA_eq, mid_tcb hT hN2 htT w25 htT (by simp) (by simp) (by simp) (fun _ => by simp), ← scA_eq, sc2]
  have iq5 : L.mem s5 (inqA t) = L.mem s (inqA t) := by
    rw [← iq2]; exact mid_tcb (K := 3592#u64) hT hN2 htT w25 htT (by simp) (by simp) (by simp) (fun _ => by simp)
  have e6 : s6 = L.wr s5 (stA t) sched.TS_RUNNING := sts_sch (schW s5 _ sc5 iq5 agΩ5 (Or.inl rfl)) es6
  have w56 : WritesIn st s5 s6 (TRegW t) := by
    rw [e6]; exact (writesIn_wr sA).mono fun b e => ⟨3328#u64, by simp, by simp, by rw [e, est]⟩
  have w26 : WritesIn st s2 s6 (MidW st T s2 t) := w25.trans1 (treg_mid w56)
  -- the `schedule` state
  have e6N : ∀ o, L.nodeAt s6 (L.cpu s6) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [w26.2.1, nodeAt_of_ksb w26.1, e2N]
  have nodeK6 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 →
      (o.val ≠ 56 ∧ o.val ≠ 104 ∧ o.val ≠ 112) →
      L.mem s6 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h40 h48 hn
    have := mid_node hT hN2 htT w26 ho h8 hn
    rw [e2N] at this
    rw [this, pre_node o ho h8 h40 h48]
  have hct6 : L.curW s6 = t := by
    unfold LawfulStore.curW; rw [e6N]
    rw [nodeK6 _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
      (by rw [curth_val]; omega) (by rw [curth_val]; omega)]
    exact etc
  have hcs6 : L.cscW s6 = csc := by
    unfold LawfulStore.cscW LawfulStore.nodeA; rw [e6N]
    rw [nodeK6 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]
    exact ecsc'
  have hact6 : L.actionW s6 = sched.ACTION_RESUME_CURRENT := by
    unfold LawfulStore.actionW; rw [e6N]
    rw [nodeK6 _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega) (by rw [act_val]; omega)
      (by rw [act_val]; omega)]
    exact hact
  have hsc6 : L.mem s6 (scA t) = csc := by
    rw [scA_eq, mid_tcb hT hN2 htT w26 htT (by simp) (by simp) (by simp) (fun _ => by simp), ← scA_eq, sc2]
  have hst6 : L.mem s6 (stA t) = sched.TS_RUNNING := by rw [e6, L.mem_wr_same sA]
  have hy6 : L.mem s6 (yieldA t) = 0#u64 := by
    unfold yieldA
    rw [mid_tcb hT hN2 htT w26 htT (by simp) (by simp) (by simp) (fun _ => by simp),
      uK htT (by simp) (by simp) (fun _ => by simp)]
    exact hy0
  have agΩ6 : ∀ b ∈ Ω, L.mem s6 b = L.mem s b := fun b hb =>
    (mid_out hT hN2 htT hcC2 w26 ((h0.omega b hb).ksb k2)).trans (agΩ2 b hb)
  have k6 : L.ksb s6 = L.ksb s := w26.1.trans k2
  have c6 : L.cpu s6 = L.cpu s := w26.2.1.trans c2
  have hcC6 : L.cpu s6 ∈ Cs := c6 ▸ hcC
  have hN6 : NodePlaced st T s6 (L.cpu s6) := by rw [c6]; exact hN.ksb k6
  -- nothing due at the `schedule` state
  have hnow : L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.CUR_TIME) = now := by
    rw [cur_time_ok] at enow; exact ok_inj_ff enow
  have nd2 : NoDueT st s2 now := td_false (by rw [c2]; exact eb5)
  have hm2 := (TInv.tm (BXI.blk hB2)).min _ hcC2
  have nd3 : NoDueT st s3 now := nodue_keep hT hN2 htT hm2 w23 nd2
  have nd4 : NoDueT st s4 now := hnd now hdl nd3
  have hq4 := hB4.1.choose_spec.choose_spec
  have hN4 : NodePlaced st T s4 (L.cpu s4) := hq4.nodes _ hq4.cur
  have w46 : WritesIn st s4 s6 (TRegW t) := (w45.trans w56).mono fun b hb => hb.elim id id
  have nd6 : NoDueT st s6 now := nodue_keep hT hN4 htT ((TInv.tm hB4).min _ hq4.cur) w46 nd4
  have hct6' : L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.CUR_TIME) = now := by
    rw [w26.2.1, nodeAt_of_ksb w26.1,
      mid_node hT hN2 htT w26 (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
        (by simp [layout.node.CUR_TIME])]
    exact hnow
  have hT6 : L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.CUR_TIME) <
        L.mem s6 (tdA (L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.TIMER_MIN))) := by
    rw [hct6']; exact nd6
  have hR6 : RelNone st s6 := rel_keep hB2 htT w26 (rel_false (by rw [c2]; exact eb6))
  -- `schedule`
  have hfp := schedTail_fp ar hA s6 a1 (zc := Z csc)
    (B := fun b => FootLt st T Scs Z Lk s b ∧ (∀ K : U64, K.val < 4096 → b ≠ core.num.U64.wrapping_add t K) ∧
      b ≠ L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
    hcC6 hN6 hT (fun b hb => (h0.omega b hb).ksb k6) (by rw [hct6]; exact htT) (by rw [hct6, hsc6, hcs6])
    (by rw [hcs6]; exact SCq.agree hcq agΩ6)
    (fun o ho h8 hz => by
      rw [e6N]
      refine ⟨footLt_node ho, fun K hK => node_ne_field hN ho htT ht' hK, fun e => hz ?_⟩
      have e' := congrArg UScalar.val e
      rw [nodeAt_val hN ho, nodeAt_val hN (by rw [curth_val]; omega), curth_val] at e'
      omega)
    (fun b hb hin => by
      rw [hcs6] at hin
      have ho := h0.omega b (hcq.2.1 b hb hin)
      exact ⟨footLt_sc hcsS hcore hin, fun K hK e => out_ne_field ho htT ht' hK (congrArg UScalar.val e).symm,
        fun e => out_ne_node ho hcC hN (by rw [curth_val]; omega) (congrArg UScalar.val e).symm⟩)
  rw [← schedule_resume ar s6 a1 hT6 hR6 hact6, es7, WP.spec_ok] at hfp
  have w67 := hfp
  -- `activate_thread`, `vcpu::check`
  have hcur7 : L.curW s7 = t := by
    have := hct6
    unfold LawfulStore.curW at this ⊢
    rw [e6N] at this
    rw [w67.2.1, nodeAt_of_ksb w67.1, e6N,
      w67.mem_eq (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) (fun hb => hb.2.2 rfl)]
    exact this
  have tK7 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s7 (core.num.U64.wrapping_add t K) = L.mem s6 (core.num.U64.wrapping_add t K) := fun K hK h8 =>
    w67.mem_eq (field_aligned ht' hK h8) (fun hb => hb.2.1 K hK rfl)
  have hst7 : L.mem s7 (stA t) = sched.TS_RUNNING := by rw [est, tK7 _ (by simp) (by simp), ← est, hst6]
  have hy7 : L.mem s7 (yieldA t) = 0#u64 := by unfold yieldA; rw [tK7 _ (by simp) (by simp)]; exact hy6
  rw [activate_run ar s7 a2 (by rw [hcur7]; exact hy7) (by rw [hcur7]; exact hst7)] at es8
  have e8 := ok_inj_ff es8
  simp only [Prod.mk.injEq] at e8
  obtain ⟨rfl, rfl⟩ := e8
  rw [cur_thread_ok, hcur7] at et1
  have et1' := ok_inj_ff et1
  subst et1'
  rw [vcpu_check_run ar s7 a2 hst7] at es9
  have e9 := ok_inj_ff es9
  simp only [Prod.mk.injEq] at e9
  obtain ⟨rfl, rfl⟩ := e9
  -- the footprint
  have f23 : WritesIn st s2 s3 (FootLt st T Scs Z Lk s) := w23.mono fun b hb => treg_foot htT haff hb
  have f46 : WritesIn st s4 s6 (FootLt st T Scs Z Lk s) := w46.mono fun b hb => treg_foot htT haff hb
  exact (((f02.trans1 f23).trans1 f34).trans1 f46).trans1 (w67.mono fun b hb => hb.1)

end main

end

end Fl4Proofs.P2
