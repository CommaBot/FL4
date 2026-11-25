/-
# P2 (p2lf): an accepted timer interrupt, fire case, the tail when the signal wakes no thread

The fire case's tail (`FireTailG`, `P2/FootTimerFireP`) on any store `gS` answering `R` reads and `W` writes as
`st`, when the due thread's bound notification `N` wakes nobody (`NoWake`: none, or neither idle nor waiting, or
idle with no bound thread or a bound thread not in `Recv`): `fire_tail_nw`.

* Helpers: `armed.tinv` (the node's `ARMED` word, as P1 `reprogram.tinv`), `SCq.agree'` (only the SC's words),
  `plan_facts'` (`plan_facts` with the plan's notification the due thread's bound one), `fire_ok_tail` /
  `fireTail_idle` (an accepted `fire_ok` passed `fireTail`; an idle notification's bound thread is the due one and
  does not run a VM), `send_signal_nw` (the non-waking `send_signal`: the notification's state and badge words,
  `TInv` and `TmFr` kept).
* The word sets at the entry state: `FTree` / `FTreeL` (the timer fields / links of this core's armed threads),
  `FNt` / `FNtW` (the due thread's bound notification; its words but `BOUND_TCB`), `FireRd` / `FireWr` (`IrqRd` / `IrqWr` with them).
* `rel_agree` (`RelNone` at an agreeing state), `fire_run` (`timer::fire` firing one timer on `st`: `remove`,
  the signal, `REPROGRAM`, and a second iteration that stops).
* `fire_tail_nw`: from the entry facts (P1's `BXI`, `IrqOk`) and the run's equations up to `handle_interrupt`, on
  `gS` answering `FireRd` reads and `FireWr` writes as `st` (plus the current thread's `STATE` write `RESTART →
  RUNNING` and the tree code's deadline / height writes, per write as `set_timer_accG`'s), when `NoWake`: the due
  thread's removal on `gS` is `ge_remove`'s, the signal is `send_signal.guardF`'s non-waking branches, the second
  iteration stops (`fire_stop`), `awaken_loop` releases nothing (`RelNone` kept: the release queue, the time and the
  SCs' words are not written), the action stays `RESUME_CURRENT`, so `schedule` is `schedRes` / `schedTail` at the
  post-`fire` state (`resume_hsw_hfr`), then `activate_thread` and `vcpu.check` of the unchanged current thread.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireP
import Fl4Proofs.P2.FootTimerFireSt
import Fl4Proofs.P2.FootTimerFireSch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (ScAcc rhA tmA RdHead NodeSt bind_guard_congr)

section help
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- The current core's `ARMED` word (as P1 `reprogram.tinv`). -/
theorem armed.tinv {s : S} {v : U64} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    TInv st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (L.nodeAt s (L.cpu s) layout.node.ARMED) v) := by
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have rp : layout.node.ARMED.val = 80 := by simp [layout.node.ARMED]
  have hw : WritesIn st s (L.wr s (L.nodeAt s (L.cpu s) layout.node.ARMED) v) (L.Free s Ω Cs) :=
    free_node_write rfl h0.cur (h0.nodes _ h0.cur) (by simp [rp, LowFree])
  have f := fr_node (Sg := Sg) (hi8 := fun _ => by rw [rp]; omega) (v := v) h0 hSg h0.cur (by rw [rp]; omega)
    (by rw [rp]) (fun _ => by rw [rp]; omega) ⟨by rw [rp]; omega, by rw [rp]; omega⟩
  exact hI.of_tmfr ⟨⟨Q, R, inv_of_free h0 hw⟩, hB.free h0 hw, hX.fr f, hS.fr f, hSg.fr f⟩
    (TmFr.of_fr f hX.1 h0.nodes)

/-- `SCq` at another state agreeing on the SC's own words. -/
theorem SCq.agree' {X Y : S} {c : U64} {z : Nat} (h : SCq st X Ω c z)
    (ag : ∀ b, Aligned b → InSC c z b → L.mem Y b = L.mem X b) : SCq st Y Ω c z := by
  have em : L.rmax Y c = L.rmax X c := ag _ h.2.2.2.2 h.2.2.2.1
  exact ⟨fun hm => (h.1 (em ▸ hm)).agree fun b hb hin => ag b hb hin, h.2.1, h.2.2⟩

/-- A notification of the heap: its state word is outside the TCBs and nodes. -/
theorem ntfn_ts_out {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {n : U64}
    (h0 : SchedQueuesInv st T Cs Ω H s Q R) (hn : H n = some .ntfn) :
    OutsideObjs st T Cs s (epTSA n) := by
  obtain ⟨E, EQ, hEW⟩ := h0.eps
  have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hn)
  obtain ⟨hE, hEN, -⟩ := hEW.1 n he
  exact (ep_out hE hEN).2

/-- An outside word is no timer word (`P1.TW`). -/
theorem out_not_tw {s : S} {b : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hb : OutsideObjs st T Cs s b) : ¬ Fl4Proofs.P1.TW st T Cs s b := by
  rintro (⟨y, hy, K, h1, h2, rfl⟩ | ⟨c, hc, o, ho, rfl⟩)
  · exact out_ne_field hb hy (hT y hy) (by omega) rfl
  · exact out_ne_node hb hc (hN c hc) (by rcases ho with h | h <;> omega) rfl

set_option maxHeartbeats 4000000 in
/-- **`plan_objects`' due thread**: null (with a null notification), or `TIMER_MIN` homed here (`TmHere`) with a
null notification or its bound one. -/
theorem plan_facts' {s : S} {tip : localtimer.TimerIrqPlan} (h : localtimer.plan_objects st s = ok tip) :
    (tip.tm = 0#u64 ∧ tip.ntfn = 0#u64) ∨
    (tip.tm = L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ∧ tip.tm ≠ 0#u64 ∧ TmHere st s tip.tm ∧
      tip.ntfn = L.mem s (boundA tip.tm)) := by
  unfold localtimer.plan_objects at h
  obtain ⟨cpu, ecpu, h⟩ := bind_eq_ok h
  rw [L.cur_cpu_eq] at ecpu
  obtain rfl := ok_inj_ff ecpu
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  rw [node_get_ok] at ei
  obtain rfl := ok_inj_ff ei
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  rw [is_null_ok] at eb
  obtain rfl := ok_inj_ff eb
  by_cases h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64
  · rw [if_pos (decide_eq_true h0)] at h
    obtain rfl := ok_inj_ff h
    exact Or.inl ⟨rfl, rfl⟩
  rw [if_neg (by simpa using h0)] at h
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  by_cases ha : (i1 != L.cpu s) = true
  · rw [if_pos ha] at h
    obtain rfl := ok_inj_ff h
    exact Or.inl ⟨rfl, rfl⟩
  rw [if_neg ha] at h
  have e1 : i1 = L.cpu s := by by_contra hne; exact ha (bne_iff_ne.mpr hne)
  subst e1
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  by_cases hb : (i2 != L.cpu s) = true
  · rw [if_pos hb] at h
    obtain rfl := ok_inj_ff h
    exact Or.inl ⟨rfl, rfl⟩
  rw [if_neg hb] at h
  have e2 : i2 = L.cpu s := by by_contra hne; exact hb (bne_iff_ne.mpr hne)
  subst e2
  have hh : TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) := And.intro ei1 ei2
  obtain ⟨n, en, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en
  obtain rfl := ok_inj_ff en
  by_cases hn : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) = 0#u64
  · rw [if_pos hn] at h
    obtain rfl := ok_inj_ff h
    exact Or.inr ⟨rfl, h0, hh, hn.symm⟩
  rw [if_neg hn] at h
  obtain ⟨⟨x0, bk⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨i3, -, h⟩ := bind_eq_ok h
  by_cases h3 : (i3 != obj.NTFN_IDLE) = true
  · rw [if_pos h3] at h
    obtain rfl := ok_inj_ff h
    exact Or.inr ⟨rfl, h0, hh, rfl⟩
  rw [if_neg h3] at h
  obtain ⟨i4, -, h⟩ := bind_eq_ok h
  by_cases h4 : (i4 != L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) = true
  · rw [if_pos h4] at h
    obtain rfl := ok_inj_ff h
    exact Or.inr ⟨rfl, h0, hh, rfl⟩
  rw [if_neg h4] at h
  obtain ⟨i5, -, h⟩ := bind_eq_ok h
  by_cases h5 : (i5 != sched.TS_BLOCKED_ON_RECV) = true
  · rw [if_pos h5] at h
    obtain rfl := ok_inj_ff h
    exact Or.inr ⟨rfl, h0, hh, rfl⟩
  rw [if_neg h5] at h
  obtain ⟨ep, -, h⟩ := bind_eq_ok h
  by_cases h6 : ep = 0#u64
  · rw [if_pos h6] at h
    obtain rfl := ok_inj_ff h
    exact Or.inr ⟨rfl, h0, hh, rfl⟩
  rw [if_neg h6] at h
  obtain ⟨⟨y0, bk1⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨r, -, h⟩ := bind_eq_ok h
  by_cases h7 : (r != 0#u64) = true
  · rw [if_pos h7] at h
    obtain ⟨a3, -, h⟩ := bind_eq_ok h
    obtain rfl := ok_inj_ff h
    exact Or.inr ⟨rfl, h0, hh, rfl⟩
  rw [if_neg h7] at h
  obtain rfl := ok_inj_ff h
  exact Or.inr ⟨rfl, h0, hh, rfl⟩

/-- An accepted `fire_ok` passed `fireTail`. -/
theorem fire_ok_tail {M : machine.Store S} {s : S} {cpu now : U64} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan}
    (h : localtimer.fire_ok M s cpu ct p now = ok true) : fireTail M s cpu ct p = ok true := by
  rw [fire_ok_eq] at h
  by_cases h0 : p.tm = 0#u64
  · rw [if_pos h0] at h; exact absurd (ok_inj_ff h) Bool.false_ne_true
  rw [if_neg h0] at h
  have k : ∀ d : U64, (if d <= now then ok false else fireTail M s cpu ct p) = ok true →
      fireTail M s cpu ct p = ok true := fun d hd => by
    by_cases hd' : d <= now
    · rw [if_pos hd'] at hd; exact absurd (ok_inj_ff hd) Bool.false_ne_true
    · rw [if_neg hd'] at hd; exact hd
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  obtain ⟨i1, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · rw [if_neg Bool.false_ne_true] at h
    obtain ⟨i2, -, h⟩ := bind_eq_ok h
    obtain ⟨b1, -, h⟩ := bind_eq_ok h
    cases b1
    · rw [if_neg Bool.false_ne_true] at h
      obtain ⟨d, -, h⟩ := bind_eq_ok h
      exact k d h
    · rw [if_pos rfl] at h; exact h
  · rw [if_pos rfl] at h
    obtain ⟨b1, -, h⟩ := bind_eq_ok h
    cases b1
    · rw [if_neg Bool.false_ne_true] at h
      obtain ⟨d, -, h⟩ := bind_eq_ok h
      exact k d h
    · rw [if_pos rfl] at h; exact h

/-- `fireTail` at an idle notification with a bound thread: the due thread, not running a VM. -/
theorem fireTail_idle {s : S} {cpu : U64} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan}
    (h : fireTail st s cpu ct p = ok true) (hn : p.ntfn ≠ 0#u64) (hi : L.epState s p.ntfn = obj.NTFN_IDLE)
    (hb : L.mem s (ntfnBtA p.ntfn) ≠ 0#u64) :
    L.mem s (ntfnBtA p.ntfn) = p.tm ∧ L.mem s (stA p.tm) ≠ sched.TS_RUNNING_VM := by
  unfold fireTail at h
  rw [if_neg hn, eq_of_spec_fd (obj.Ntfn.state.spec (L := L) s _), hi] at h
  simp only [bind_ok] at h
  rw [if_neg (by simp [obj.NTFN_IDLE, obj.NTFN_ACTIVE]), if_pos trivial,
    eq_of_spec_fd (obj.Ntfn.bound_tcb.val (L := L) s _)] at h
  simp only [bind_ok] at h
  rw [if_neg hb] at h
  by_cases he : (L.mem s (ntfnBtA p.ntfn) != p.tm) = true
  · rw [if_pos he] at h; exact absurd (ok_inj_ff h) Bool.false_ne_true
  rw [if_neg he] at h
  have e : L.mem s (ntfnBtA p.ntfn) = p.tm := by
    by_contra hne; exact he (bne_iff_ne.mpr hne)
  refine ⟨e, fun hv => ?_⟩
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s _)] at h
  simp only [bind_ok] at h
  rw [if_pos hv] at h; exact absurd (ok_inj_ff h) Bool.false_ne_true

/-- `set_active` writes the notification's state and badge words. -/
theorem set_active_wr {X X' : S} {n badge : U64} (aT : Aligned (epTSA n)) (aB : Aligned (ntfnBdA n))
    (h : notification.set_active st X n badge = ok X') : WritesIn st X X' (SaD n) := by
  unfold notification.set_active at h
  rw [eq_of_spec_fd (obj.Ntfn.set_state.val (L := L) X n _)] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (obj.Ntfn.set_badge.wr (L := L) _ n badge)] at h
  rw [← ok_inj_ff h]
  exact ((writesIn_wr aT).trans (writesIn_wr aB)).mono fun b hb => by
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr hb

/-- **The non-waking `send_signal`** (module docstring): the notification's state and badge words, `TInv` and the
timer frame kept, the arch state untouched. -/
theorem send_signal_nw {A : Type} (ar : machine.Arch A) (X : S) (a : A) (n badge : U64)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X) (hn : n ∈ Nt) (hH : H n = some .ntfn)
    (hw : L.epState X n ≠ obj.NTFN_WAITING)
    (hb : L.epState X n = obj.NTFN_IDLE → L.mem X (ntfnBtA n) ≠ 0#u64 →
      L.mem X (stA (L.mem X (ntfnBtA n))) ≠ sched.TS_BLOCKED_ON_RECV ∧
      L.mem X (stA (L.mem X (ntfnBtA n))) ≠ sched.TS_RUNNING_VM ∧ L.mem X (ntfnBtA n) ∈ T) :
    ∃ X', notification.send_signal st ar X a n badge = ok (X', a) ∧ WritesIn st X X' (SaD n) ∧
      TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X' ∧ TmFr st T Cs Nt X X' := by
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hst1 : L.epState X n ≠ 1#u64 := by rw [← ntfn_wait_val']; exact hw
  have oT := ntfn_ts_out h0 hH
  have aT : Aligned (epTSA n) := oT.1
  have oB : OutsideObjs st T Cs X (ntfnBdA n) := h0.omega _ (hSg.sub _ (hO.ntB n hn).1)
  have aB : Aligned (ntfnBdA n) := oB.1
  have eS : obj.Ntfn.state st n X = ok (L.epState X n) := eq_of_spec_fd (obj.Ntfn.state.spec (L := L) X n)
  have eB : obj.Ntfn.bound_tcb st n X = ok (L.mem X (ntfnBtA n)) := eq_of_spec_fd (obj.Ntfn.bound_tcb.val (L := L) X n)
  obtain ⟨X', eX', hX'⟩ := spec_ex_fd (notification.set_active.tm X n badge hI hn hH hst1)
  by_cases hi : L.epState X n = obj.NTFN_IDLE
  · rw [hi] at eS
    by_cases h0b : L.mem X (ntfnBtA n) = 0#u64
    · rw [h0b] at eB
      refine ⟨X', ?_, set_active_wr aT aB eX', hX'⟩
      rw [send_signal_idle0 st ar X a n badge eS eB, eX']
      simp only [bind_ok]
    · obtain ⟨hr, hv, hbT⟩ := hb hi h0b
      have eT : obj.Tcb.state st (L.mem X (ntfnBtA n)) X = ok (L.mem X (stA (L.mem X (ntfnBtA n)))) :=
        eq_of_spec_fd (obj.Tcb.state.spec (L := L) X _)
      have w := set_active_wr aT aB eX'
      have kS : L.mem X' (stA (L.mem X (ntfnBtA n))) = L.mem X (stA (L.mem X (ntfnBtA n))) := by
        have ht := h0.tcbs _ hbT
        refine w.mem_eq (by rw [stA_eq]; exact field_aligned ht (by simp) (by simp)) ?_
        rintro (e | e)
        · rw [stA_eq] at e
          exact out_ne_field oT hbT ht (by simp) (congrArg UScalar.val e)
        · rw [stA_eq] at e
          exact out_ne_field oB hbT ht (by simp) (congrArg UScalar.val e)
      refine ⟨X', ?_, w, hX'⟩
      rw [send_signal_bnr st ar X a n badge eS eB h0b eT hr hv, eX']
      simp only [bind_ok]
      rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) X' _), kS]
      simp only [bind_ok, if_neg hv]
  · have eN : notification.send_signal st ar X a n badge =
        ok (L.wr X (ntfnBdA n) (L.mem X (ntfnBdA n) ||| badge), a) := by
      rw [send_signal_act st ar X a n badge eS hi hw, eq_of_spec_fd (obj.Ntfn.badge.val (L := L) X n)]
      simp only [bind_ok]
      rw [eq_of_spec_fd (obj.Ntfn.set_badge.wr (L := L) X n _)]
      simp only [bind_ok]
    obtain ⟨b2, tm2⟩ := ntfn_badge_all (v := L.mem X (ntfnBdA n) ||| badge)
      (⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac X) hn
    exact ⟨_, eN, (writesIn_wr aB).mono fun b hb => Or.inr hb, b2, tm2⟩

/-- `RelNone` at a state agreeing on the release head, the time, the threads' `SC` words and the SCs' words. -/
theorem rel_agree {X Y : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X) (hk : L.ksb Y = L.ksb X)
    (hc : L.cpu Y = L.cpu X)
    (eh : L.mem Y (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD))
    (ect : L.curTime Y = L.curTime X) (esc : ∀ y ∈ T, L.mem Y (scA y) = L.mem X (scA y))
    (keep : ∀ c ∈ Scs, ∀ b, Aligned b → InSC c (Z c) b → L.mem Y b = L.mem X b)
    (h : RelNone st X) : RelNone st Y := by
  obtain ⟨⟨Q, R, hq⟩, hB, hX, -, hS⟩ := hI
  have hcC := hq.cur
  have eA : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt X (L.cpu X) o := fun o => by rw [hc, nodeAt_of_ksb hk]
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
  rw [esc h0 hhT]
  have haff : L.mem X (affA h0) = L.cpu X := hq.inR _ hcC h0 hmem
  have hrb : (L.mem X (inqA h0) &&& sched.Q_RELEASE) ≠ 0#u64 := (hq.released h0 hhT).2 (by rw [haff]; exact hmem)
  have hsc0 : L.mem X (scA h0) ≠ 0#u64 := hB.r h0 hhT hrb
  have hscS : L.mem X (scA h0) ∈ Scs := (hX.2.2.bound h0 hhT hsc0).1
  have hAc : L.mem X (scA h0) ∈ Ac := hB.sact h0 hhT (Or.inr (Or.inl hrb)) hsc0
  generalize hsc : L.mem X (scA h0) = sc at h hscS hAc ⊢
  have hmax : L.rmax X sc ≠ 0#u64 := (hS.act sc hscS).1 hAc
  obtain ⟨hwf, -, -⟩ := hS.all sc hscS
  have wf := hwf hmax
  obtain ⟨h8, hm, hfit⟩ := wf.bounds
  obtain ⟨-, -, -, hhd, -, hri⟩ := wf.inside
  have kp := keep sc hscS
  have e1 : L.rhead Y sc = L.rhead X sc := kp _ (by unfold Aligned; rw [hhd]; omega) ⟨by rw [hhd]; omega, by rw [hhd]; omega⟩
  obtain ⟨r1, r2, r3⟩ := hri (L.rhead X sc) wf.head_lt
  have e2 : L.mem Y (rtA sc (L.rhead X sc)) = L.mem X (rtA sc (L.rhead X sc)) :=
    kp _ (by unfold Aligned; rw [r1]; omega) ⟨by rw [r1]; omega, by rw [r1]; omega⟩
  simp only [LawfulStore.refill] at h ⊢
  rw [e1, e2]
  exact h

end help

/-! ## The word sets -/

section sets
variable {S : Type}

/-- The timer fields (`TIMER_DEADLINE ..= TIMER_HEIGHT`, offsets 3528–3568) of the threads armed in this core's tree
at the entry state `s`. -/
def FTree (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) (w : U64) : Prop :=
  ∃ y ∈ T, FootLtArmed st s (L.cpu s) y ∧
    ∃ K : U64, 3528 ≤ K.val ∧ K.val < 3576 ∧ K.val % 8 = 0 ∧ w = core.num.U64.wrapping_add y K

/-- Their link and badge words (offsets 3536–3560): what the tree code writes besides deadlines and heights. -/
def FTreeL (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) (w : U64) : Prop :=
  ∃ y ∈ T, FootLtArmed st s (L.cpu s) y ∧
    ∃ K : U64, 3536 ≤ K.val ∧ K.val < 3568 ∧ K.val % 8 = 0 ∧ w = core.num.U64.wrapping_add y K

/-- The words of the due thread's bound notification (`TIMER_MIN`'s `BOUND_NTFN` at `s`). -/
def FNt (st : machine.Store S) [L : LawfulStore st] (s : S) (w : U64) : Prop :=
  L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 ∧
    L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64 ∧
    ∃ K : U64, K.val < 64 ∧ K.val % 8 = 0 ∧
      w = core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) K

/-- The words of `FNt` the fire case may write: all but `BOUND_TCB` (offset 24, the gate's). -/
def FNtW (st : machine.Store S) [L : LawfulStore st] (s : S) (w : U64) : Prop :=
  L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 ∧
    L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64 ∧
    ∃ K : U64, K.val < 64 ∧ K.val % 8 = 0 ∧ K.val ≠ 24 ∧
      w = core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) K

/-- What the fire case reads at the entry state (module docstring). -/
def FireRd (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (Z : U64 → Nat) (s : S) (w : U64) : Prop :=
  IrqRd st Z s w ∨ FTree st T s w ∨ FNt st s w

/-- What the fire case writes at the entry state besides the deadlines and heights of `FTree` (module docstring). -/
def FireWr (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (Z : U64 → Nat) (s : S) (w : U64) : Prop :=
  IrqWr st Z s w ∨ FTreeL st T s w ∨ FNtW st s w

/-- The due thread's bound notification wakes nobody: none, neither idle nor waiting, or idle with no bound
thread or one not in `Recv`. -/
def NoWake (st : machine.Store S) [L : LawfulStore st] (s : S) : Prop :=
  L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) = 0#u64 ∨
  (L.epState s (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) ≠ obj.NTFN_IDLE ∧
    L.epState s (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) ≠ obj.NTFN_WAITING) ∨
  (L.epState s (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) = obj.NTFN_IDLE ∧
    (L.mem s (ntfnBtA (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))) = 0#u64 ∨
      L.mem s (stA (L.mem s (ntfnBtA (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))))))
        ≠ sched.TS_BLOCKED_ON_RECV))

end sets

/-! ## `fire` with one timer due, on `st` -/

section run
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **`timer::fire` firing one timer** at `X`: `remove`, the bound notification's signal (or nothing), the
`REPROGRAM` write, and a second iteration that stops (`FireStop`). -/
theorem fire_run {A : Type} (ar : machine.Arch A) (X : S) (a : A) {X1 X2 : S} {a2 : A} {R' : U64 → Prop}
    (h0 : L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) ≠ 0#u64)
    (hdue : ¬ L.mem X (tdA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) >
      L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME))
    (hrm : timer.remove st X (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN)) = ok X1)
    (hsg : (if L.mem X1 (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) != 0#u64 then
          notification.send_signal st ar X1 a (L.mem X1 (boundA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
            (L.mem X (tbA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
        else ok (X1, a)) = ok (X2, a2))
    (hst : FireStop st R' (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64)
      (L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME))) :
    timer.fire st ar X a = ok (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64, a2) := by
  have hb : (0#u64 : U64) < timer.FIRE_BATCH := by unfold timer.FIRE_BATCH; decide
  have hadd : (0#u64 : U64) + 1#u64 = ok 1#u64 := by
    obtain ⟨z, hz, hzv⟩ := spec_ex_fd (U64.add_spec (x := 0#u64) (y := 1#u64) (by scalar_tac))
    rw [hz]
    congr 1
    apply UScalar.eq_of_val_eq
    rw [hzv]; simp
  have e1 : timer.fire_loop.body st ar (L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME)) X a 0#u64 =
      ok (ControlFlow.cont (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64, a2, 1#u64)) := by
    unfold timer.fire_loop.body
    simp only [hb, ↓reduceIte, L.cur_cpu_eq, bind_ok, bind_tc_ok]
    rw [node_get_ok]
    simp only [bind_ok, bind_tc_ok, is_null_ok, h0, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) X _)]
    simp only [bind_ok, bind_tc_ok, hdue, ↓reduceIte]
    rw [eq_of_spec_fd (obj.Tcb.timer_badge.val (L := L) X _)]
    simp only [bind_ok, bind_tc_ok]
    rw [hrm]
    simp only [bind_ok, bind_tc_ok]
    rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) X1 _)]
    simp only [bind_ok, bind_tc_ok]
    rw [hsg]
    simp only [bind_ok, bind_tc_ok, Aeneas.Std.uncurry_apply_pair, L.cur_cpu_eq]
    rw [eq_of_spec_fd (obj.node_set.spec (L := L) X2 _ _ _)]
    simp only [bind_ok, bind_tc_ok, hadd]
  unfold timer.fire timer.fire_loop
  simp only [L.cur_cpu_eq, bind_ok, bind_tc_ok]
  rw [node_get_ok]
  simp only [bind_ok, bind_tc_ok]
  rw [loop]
  simp only [e1, bind_ok, bind_tc_ok]
  rw [loop]
  simp only [fire_body_done ar _ a2 _ 1#u64 hst, bind_ok, bind_tc_ok]

end run

/-! ## The tail when nobody is woken -/

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 64000000 in
/-- **The fire case's tail on the guarded store when the signal wakes nobody** (module docstring). -/
theorem fire_tail_nw {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s1 s2 s3 : S} {a a1 a2 a3 : A} {mx irq now i2 : U64} {x : Bool}
    {tip p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hok : IrqOk st s)
    (gRd : ∀ w, Aligned w → FireRd st T Z s w → R w)
    (gWr : ∀ w, Aligned w → FireWr st T Z s w → w ≠ stA (L.curW s) → W w)
    (hD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART → L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hwH : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y →
      (L.mem X (tdA y) ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val ∧ v.val >>> 8 = (L.cpu s).val) →
      gS.write X (thA y) v = st.write X (thA y) v)
    (hwD : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y → L.mem X (affA y) = L.cpu s →
      L.mem s (affA y) = L.cpu s →
      (L.mem X (tdA y) ≠ 0#u64 ∨ v ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val) →
      gS.write X (tdA y) v = st.write X (tdA y) v)
    (hNW : NoWake st s)
    (etip : localtimer.plan_objects st s = ok tip) (eb : localtimer.same_plan tip p = ok true)
    (eq : localtimer.sched_quiet st s (L.cpu s) = ok true)
    (eok : localtimer.current_ok st s (L.cpu s) (L.curW s) (L.cscW s) = ok true)
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) (enow : sched.cur_time st s1 = ok now)
    (erel : localtimer.release_due st s1 (L.cpu s) = ok false) (ei2 : sched.consumed st s1 = ok i2)
    (eb4 : sporadic.sufficient st ar s1 a1 (L.cscW s) i2 = ok true)
    (edue : localtimer.timer_due st s1 (L.cpu s) now = ok true)
    (efo : localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now = ok true)
    (ecb : sched.check_budget st ar s1 a1 = ok (x, s2, a2))
    (emx : layout.irq.MAX = ok mx) (hle : ¬ irq > mx)
    (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
    (ehi : interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3)) :
    FireTailG st gS ar s3 a3 := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hNa : ∀ c ∈ Cs, NodePlaced st T s c := h0.nodes
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  obtain ⟨haff, hsct, hcore⟩ := hok
  obtain ⟨hmr, -, -⟩ := current_ok_true eok
  obtain ⟨-, -, hnvm, -⟩ := may_run_here_true hmr
  have hy0 : L.mem s (yieldA (L.curW s)) = 0#u64 := mrh_yield hmr
  have hX := hI.2.2.1
  have hS := hI.2.2.2.2
  have hSg := hI.2.2.2.1
  have hO := hX.1
  have hcs : L.cscW s ∈ Scs := hX.2.2.cur
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := scq_of hO hS hcs
  have hact0 : L.actionW s = sched.ACTION_RESUME_CURRENT := sq_true eq
  have hsc0 : L.mem s (scA (L.curW s)) ≠ 0#u64 := hI.2.1.resume (hact0.trans resume_val)
  have hAc : L.cscW s ∈ Ac := by
    rw [← hsct]
    exact hI.2.1.sact _ hcT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hact0.trans resume_val, rfl⟩))))) hsc0
  have hmx0 : L.rmax s (L.cscW s) ≠ 0#u64 := (hS.act _ hcs).1 hAc
  -- `s → s1`: the timestamp update
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
  simp only at er
  have k1 : L.ksb s1 = L.ksb s := by rw [er, utW_ksb]
  have c1 : L.cpu s1 = L.cpu s := by rw [er, utW_cpu]
  have m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b :=
    fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [er]; exact utW_placed hN n1
  have e1N : ∀ o, L.nodeAt s1 (L.cpu s1) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c1, nodeAt_of_ksb k1]
  have hnode1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 →
      L.mem s1 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h40 h48
    refine m1 _ (nodeAt_aligned hN ho h8) (fun e => ?_) (fun e => ?_)
    · have e' := congrArg UScalar.val e
      unfold ctA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CUR_TIME])] at e'
      simp [layout.node.CUR_TIME] at e'; omega
    · have e' := congrArg UScalar.val e
      unfold cnA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CONSUMED])] at e'
      simp [layout.node.CONSUMED] at e'; omega
  have hout1 : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b := fun b hb =>
    m1 b hb.1 (fun e => out_ne_node hb hcC hN (by simp [layout.node.CUR_TIME]) (congrArg UScalar.val e).symm)
      (fun e => out_ne_node hb hcC hN (by simp [layout.node.CONSUMED]) (congrArg UScalar.val e).symm)
  have agΩ1 : ∀ b ∈ Ω, L.mem s1 b = L.mem s b := fun b hb => hout1 b (h0.omega b hb)
  have htcb1 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y K hy hK h8
    exact m1 _ (field_aligned (hT y hy) hK h8) (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CUR_TIME]))
      (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CONSUMED]))
  have hB1 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := by
    have := sched.update_timestamp.bxc hA s a hI
    rw [eu, WP.spec_ok] at this
    try simp only [WP.uncurry'_pair] at this
    exact this.1.1
  have hnow : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_TIME) = now := by
    rw [cur_time_ok] at enow; exact ok_inj_ff enow
  -- the IRQ's state word after the timestamp update
  have hirq : irq.val ≤ 127 := by
    rw [eq_of_spec_fd layout.irq.MAX.spec] at emx
    have e := ok_inj_ff emx
    subst e
    scalar_tac
  obtain ⟨i, hi, hiv⟩ : ∃ i, interrupt.state_off irq = ok i ∧ i.val = 224 + 8 * irq.val := by
    unfold interrupt.state_off
    simp only [lift, bind_ok]
    rw [eq_of_spec_fd layout.ks.IRQ_STATE.spec]
    simp only [bind_ok]
    refine ⟨_, rfl, ?_⟩
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    try omega
  have hi' : i.val < 13568 := by omega
  have hi8 : i.val % 8 = 0 := by omega
  have eis1 : interrupt.irq_state st s1 irq = ok interrupt.IRQ_TIMER := by
    rw [← ei1]
    unfold interrupt.irq_state
    rw [hi]
    simp only [bind_ok]
    rw [eq_of_spec_fd (obj.ks_get.spec (L := L) s1 i), eq_of_spec_fd (obj.ks_get.spec (L := L) s i), k1,
      m1 _ (ks_aligned hN hi' hi8) (ks_ne_node hN hi' (by simp [layout.node.CUR_TIME]))
        (ks_ne_node hN hi' (by simp [layout.node.CONSUMED]))]
  -- `check_budget`
  have ecs1 : sched.cur_sc st s1 = ok (L.cscW s) := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s1)]
    congr 1
    show L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_SC) = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_SC)
    rw [e1N]
    exact hnode1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  rw [check_budget_suf ar ecs1 ei2 eb4] at ecb
  have e2 := ok_inj_ff ecb
  simp only [Prod.mk.injEq] at e2
  obtain ⟨-, e2s, e2a⟩ := e2
  subst e2s e2a
  -- `handle_interrupt`: `s1 → s3`
  obtain ⟨s2', eh2, eh3, -⟩ := handle_interrupt_timer ar emx hle eis1 ehi
  have w13 : WritesIn st s1 s3 (HW st s1) := handle_interrupt_timer_writes hN1 eh2 eh3
  have hT3 : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s3 := by
    rw [eq_of_spec_fd (obj.node_set.spec (L := L) s1 _ _ _)] at eh2
    have e2 := ok_inj_ff eh2
    subst e2
    rw [eq_of_spec_fd (obj.node_set.spec (L := L) _ _ _ _)] at eh3
    rw [← ok_inj_ff eh3]
    have := armed.tinv (v := 0#u64) (reprogram.tinv (v := 1#u64) (BXI.blk hB1))
    rwa [LawfulStore.cpu_wr] at this
  have k3 : L.ksb s3 = L.ksb s := w13.1.trans k1
  have c3 : L.cpu s3 = L.cpu s := w13.2.1.trans c1
  have e3N : ∀ o, L.nodeAt s3 (L.cpu s3) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c3, nodeAt_of_ksb k3]
  have hnode3 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 → o.val ≠ 56 → o.val ≠ 80 →
      L.mem s3 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h40 h48 h56 h80
    have := hw_node hN1 w13 ho h8 ⟨h56, h80⟩
    rw [e1N] at this
    rw [this, hnode1 o ho h8 h40 h48]
  have htcb3 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun hy hK h8 => (hw_tcb hT hN1 w13 hy hK h8).trans (htcb1 hy hK h8)
  have hcC1 : L.cpu s1 ∈ Cs := by rw [c1]; exact hcC
  have hout3 : ∀ b, OutsideObjs st T Cs s b → L.mem s3 b = L.mem s b := fun b hb =>
    (hw_outside hN1 hcC1 w13 (hb.ksb k1)).trans (hout1 b hb)
  have hcC3 : L.cpu s3 ∈ Cs := by rw [c3]; exact hcC
  have hN3a : ∀ c ∈ Cs, NodePlaced st T s3 c := fun c hc => (hNa c hc).ksb k3
  have tm3 : L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    rw [e3N]
    exact hnode3 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN])
  have ct3 : L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.CUR_TIME) = now := by
    rw [w13.2.1, nodeAt_of_ksb w13.1,
      hw_node hN1 w13 (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
        (by simp [layout.node.CUR_TIME])]
    exact hnow
  -- the due thread and its notification
  obtain ⟨hpt, hpn⟩ := same_plan_tm eb
  have hp0 : p.tm ≠ 0#u64 := by
    intro e
    have h' := efo
    rw [fire_ok_eq, if_pos e] at h'
    exact Bool.false_ne_true (ok_inj_ff h')
  obtain ⟨TM, eTM⟩ : ∃ x, L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = x := ⟨_, rfl⟩
  obtain ⟨hpTM, hne, hh, hpN⟩ : p.tm = TM ∧ TM ≠ 0#u64 ∧ TmHere st s TM ∧ p.ntfn = L.mem s (boundA TM) := by
    rcases plan_facts' etip with ⟨t1, -⟩ | ⟨t1, t2, t3, t4⟩
    · exact absurd (by rw [← hpt]; exact t1) hp0
    · rw [eTM] at t1
      rw [t1] at t2 t3 t4
      exact ⟨by rw [← hpt, t1], t2, t3, by rw [← hpn, t4]⟩
  rw [eTM] at tm3
  obtain ⟨N, eN⟩ : ∃ x, L.mem s (boundA TM) = x := ⟨_, rfl⟩
  have hTMs : TM ∈ T ∧ FootLtArmed st s (L.cpu s) TM := by
    have := tmin_facts (BXI.blk hI) hcC (by rw [eTM]; exact hne)
    rwa [eTM] at this
  have haffTM : L.mem s (affA TM) = L.cpu s := by
    have e := hh.1; rw [aff_ok] at e; exact ok_inj_ff e
  unfold NoWake at hNW
  rw [eTM, eN] at hNW
  have nNt : N ≠ 0#u64 → N ∈ Nt := fun h => by
    have := hX.2.2.bnd _ hTMs.1 (by rw [eN]; exact h); rwa [eN] at this
  have oT : N ≠ 0#u64 → OutsideObjs st T Cs s (epTSA N) := fun h => ntfn_ts_out h0 (hNt N (nNt h))
  have oB : N ≠ 0#u64 → OutsideObjs st T Cs s (ntfnBdA N) := fun h => h0.omega _ (hSg.sub _ (hO.ntB N (nNt h)).1)
  have oBt : N ≠ 0#u64 → OutsideObjs st T Cs s (ntfnBtA N) := fun h => h0.omega _ (hSg.sub _ (hO.ntB N (nNt h)).2)
  have eTS : core.num.U64.wrapping_add N layout.ntfn.TAIL_STATE = epTSA N := by
    apply UScalar.eq_of_val_eq
    unfold epTSA
    simp [core.num.U64.wrapping_add_val_eq, layout.ntfn.TAIL_STATE, layout.ep.TAIL_STATE]
  -- the guarded store: what it admits
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gRd _ (nodeAt_aligned hN h1 h2) (Or.inl (Or.inl ⟨o, h1, h2, rfl⟩))
  have nW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → W (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gWr _ (nodeAt_aligned hN h1 h2) (Or.inl (Or.inl ⟨o, h1, h2, rfl⟩)) (fun e => by
      rw [stA_eq] at e; exact node_ne_field hN h1 hcT ht' (by simp) e)
  have cR : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      K.val ≠ 3496 → K.val ≠ 3504 → R (core.num.U64.wrapping_add (L.curW s) K) := fun K h1 h2 h3 h4 h5 h6 =>
    gRd _ (field_aligned ht' h2 h3) (Or.inl (Or.inr (Or.inl ⟨K, h1, h2, h3, h4, h5, h6, rfl⟩)))
  have cW : ∀ K : U64, 256 ≤ K.val → K.val < 3328 → K.val % 8 = 0 → W (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K h1 h2 h3 =>
    gWr _ (field_aligned ht' (by omega) h3) (Or.inl (Or.inr (Or.inl ⟨K, h1, by omega, h3, rfl⟩))) (fun e => by
      rw [stA_eq] at e
      exact tcb_word_ne ht' ht' (by omega) (by simp) (fun _ h => by simp at h; omega) e)
  have rR : ∀ r : U64, r.val < 384 → R (regA (L.curW s) r) := fun r hr => by
    obtain ⟨K, hK, e⟩ := regA_eq ht' hr
    rw [e]; exact cR K (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have rW : ∀ r : U64, r.val < 384 → W (regA (L.curW s) r) := fun r hr => by
    obtain ⟨K, hK, e⟩ := regA_eq ht' hr
    rw [e]; exact cW K (by omega) (by omega) (by omega)
  have scR : ∀ b, InSC (L.cscW s) (Z (L.cscW s)) b → Aligned b → R b := fun b hb ha =>
    gRd _ ha (Or.inl (Or.inr (Or.inr (Or.inl hb))))
  have scNS : ∀ b, Aligned b → InSC (L.cscW s) (Z (L.cscW s)) b → b ≠ stA (L.curW s) := fun b ha hb e => by
    rw [stA_eq] at e
    exact out_ne_field (h0.omega b (hcq.2.1 b ha hb)) hcT ht' (by simp) (congrArg UScalar.val e).symm
  have hSc : ScAcc R W (L.cscW s) (Z (L.cscW s)) := ⟨fun b ha hb => scR b hb ha, fun b h1 h2 =>
    gWr _ h1 (Or.inl (Or.inr (Or.inr (Or.inl h2)))) (scNS b h1 ⟨by have := h2.1; omega, h2.2⟩),
    gWr _ hcq.2.2.1.2 (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (scNS _ hcq.2.2.1.2 hcq.2.2.1.1)⟩
  have rSt : R (stA (L.curW s)) := by rw [stA_eq]; exact cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rSc : R (scA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rIq : R (inqA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rYt : R (yieldA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rMx : R (maxA (L.cscW s)) := scR _ hcq.2.2.2.1 hcq.2.2.2.2
  have nrm : ∀ Y : S, (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → NodeSt (L := L) R W Y := fun Y e => by
    unfold PathObl.NodeSt
    rw [e, e]
    exact ⟨nR _ (by rw [curth_val]; omega) (by rw [curth_val]), nR _ (by rw [act_val]; omega) (by rw [act_val]),
      nW _ (by rw [act_val]; omega) (by rw [act_val])⟩
  have ndR : ∀ (Y : S), (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → ∀ o : U64, o.val < 4288 →
      o.val % 8 = 0 → R (L.nodeAt Y (L.cpu Y) o) := fun Y e o h1 h2 => by rw [e]; exact nR o h1 h2
  have rT : ∀ y ∈ T, FootLtArmed st s (L.cpu s) y → ∀ K : U64, 3528 ≤ K.val → K.val < 3576 → K.val % 8 = 0 →
      R (core.num.U64.wrapping_add y K) := fun y hy ha K h1 h2 h3 =>
    gRd _ (field_aligned (hT y hy) (by omega) h3) (Or.inr (Or.inl ⟨y, hy, ha, K, h1, h2, h3, rfl⟩))
  have wT : ∀ y ∈ T, FootLtArmed st s (L.cpu s) y → ∀ K : U64, 3536 ≤ K.val → K.val < 3568 → K.val % 8 = 0 →
      W (core.num.U64.wrapping_add y K) := fun y hy ha K h1 h2 h3 =>
    gWr _ (field_aligned (hT y hy) (by omega) h3) (Or.inr (Or.inl ⟨y, hy, ha, K, h1, h2, h3, rfl⟩)) (fun e => by
      rw [stA_eq] at e
      exact field_ne (hT y hy) ht' (by omega) (by simp) (fun _ => by simp; omega) e)
  have rN : N ≠ 0#u64 → ∀ K : U64, K.val < 64 → K.val % 8 = 0 → R (core.num.U64.wrapping_add N K) := fun h K h1 h2 => by
    obtain ⟨p1, p2⟩ := hO.ntP _ (nNt h)
    exact gRd _ (by unfold Aligned; rw [ntfn_word_val p1 p2 h1]; omega)
      (Or.inr (Or.inr ⟨by rw [eTM]; exact hne, by rw [eTM, eN]; exact h, K, h1, h2, by rw [eTM, eN]⟩))
  have wN : N ≠ 0#u64 → ∀ K : U64, K.val < 64 → K.val % 8 = 0 → K.val ≠ 24 →
      core.num.U64.wrapping_add N K ≠ stA (L.curW s) → W (core.num.U64.wrapping_add N K) := fun h K h1 h2 h24 hn => by
    obtain ⟨p1, p2⟩ := hO.ntP _ (nNt h)
    exact gWr _ (by unfold Aligned; rw [ntfn_word_val p1 p2 h1]; omega)
      (Or.inr (Or.inr ⟨by rw [eTM]; exact hne, by rw [eTM, eN]; exact h, K, h1, h2, h24, by rw [eTM, eN]⟩)) hn
  have nsO : ∀ b, OutsideObjs st T Cs s b → b ≠ stA (L.curW s) := fun b hb e => by
    rw [stA_eq] at e
    exact out_ne_field hb hcT ht' (by simp) (congrArg UScalar.val e).symm
  -- `remove` of the due thread at `s3`
  obtain ⟨Wk, ctk⟩ := (TInv.rb hT3).tree _ hcC3
  have armS : ∀ z ∈ Wk.keys, FootLtArmed st s (L.cpu s) z := fun z hz => by
    have zT := ctk.inT z hz
    refine ⟨?_, ?_⟩
    · have e : L.mem s3 (tdA z) = L.mem s (tdA z) := htcb3 zT (K := 3528#u64) (by simp) (by simp)
      rw [← e]; exact ctk.armed z hz
    · have e : L.mem s3 (thA z) = L.mem s (thA z) := htcb3 zT (K := 3568#u64) (by simp) (by simp)
      rw [← e, ← c3]; exact ctk.core z hz
  have C : TC st gS T s (L.cpu s) (fun z => z ∈ Wk.keys) R W :=
    { tcbs := hT, inT := ctk.inT, node := hN
      rd := fun w hw => by
        rcases hw with ⟨z, hz, k, h1, h2, h3, rfl⟩ | ⟨o, ho, h8, rfl⟩
        · exact rT z (ctk.inT z hz) (armS z hz) k h1 h2 h3
        · exact nR o ho h8
      wr := fun w hw => by
        rcases hw with ⟨z, hz, k, h1, h2, h3, rfl⟩ | ⟨o, ho, h8, rfl⟩
        · exact wT z (ctk.inT z hz) (armS z hz) k h1 h2 h3
        · exact nW o ho h8
      wh := fun X y v hy hc => hwH X y v (ctk.inT y hy) (armS y hy) hc
      wd := fun X y v hy ha1 ha0 hc => hwD X y v (ctk.inT y hy) (armS y hy) ha1 ha0 hc }
  have I3 : TI st s (L.cpu s) (fun z => z ∈ Wk.keys) (fun z => z ∈ Wk.keys) s3 :=
    { ksb := k3, cpu := c3, sub := fun _ hz => hz
      root := by
        have := ctk.rep.root_mem
        rw [c3, nodeAt_of_ksb k3] at this; exact this
      lnk := fun z hz => ctk.rep.links z hz
      hj := fun z hz _ => by rw [← c3]; exact ctk.core z hz
      af := fun z hz => htcb3 (ctk.inT z hz) (K := 3520#u64) (by simp) (by simp) }
  have hkt : TM ∈ Wk.keys := by
    have e := ctk.min
    rw [tm3] at e
    rw [e]
    exact Wk.minKey_mem.resolve_left (by rw [← e]; exact hne)
  have hrmg : timer.remove gS s3 TM = timer.remove st s3 TM :=
    (ge_remove C I3 hkt haffTM (fun i _ _ => by
      have e := timer.core_of.rb s3 TM ctk hkt
      rw [← c3]; exact eq_of_spec_fd e)).1
  obtain ⟨X1, eX1, hT1, -, -, tk1, w31⟩ := spec_ex_fd (timer.remove.tf (s0 := s3) s3 TM (TF.start hT3) hTMs.1)
  have kO1 : ∀ b, OutsideObjs st T Cs s b → L.mem X1 b = L.mem s b := fun b hb =>
    (w31.mem_eq hb.1 (out_not_tw hT hN3a (hb.ksb k3))).trans (hout3 b hb)
  have kT1 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      L.mem X1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h1 h2 h3 => (tk1 y hy K h1 h2 h3).trans (htcb3 hy h1 h2)
  have bX1 : L.mem X1 (boundA TM) = N := by
    rw [← eN]; exact kT1 TM hTMs.1 3368#u64 (by simp) (by simp) (Or.inl (by simp))
  have sX1 : L.mem X1 (stA TM) = L.mem s (stA TM) := by
    rw [stA_eq]; exact kT1 TM hTMs.1 3328#u64 (by simp) (by simp) (Or.inl (by simp))
  -- the signal wakes nobody
  have hnwX : N ≠ 0#u64 → L.epState X1 N ≠ obj.NTFN_WAITING ∧ (L.epState X1 N = obj.NTFN_IDLE →
      L.mem X1 (ntfnBtA N) ≠ 0#u64 → L.mem X1 (ntfnBtA N) = TM ∧
        L.mem X1 (stA TM) ≠ sched.TS_BLOCKED_ON_RECV ∧ L.mem X1 (stA TM) ≠ sched.TS_RUNNING_VM) := by
    intro hN0
    have eS : L.epState X1 N = L.epState s N := by unfold LawfulStore.epState; rw [kO1 _ (oT hN0)]
    have eBt : L.mem X1 (ntfnBtA N) = L.mem s (ntfnBtA N) := kO1 _ (oBt hN0)
    rw [eS, eBt, sX1]
    rcases hNW with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h hN0
    · exact ⟨h2, fun h => absurd h h1⟩
    · refine ⟨by rw [h1]; simp [obj.NTFN_IDLE, obj.NTFN_WAITING], fun _ hb0 => ?_⟩
      have hbr := h2.resolve_left hb0
      have pn0 : p.ntfn ≠ 0#u64 := by rw [hpN, eN]; exact hN0
      have eS1 : L.epState s1 p.ntfn = obj.NTFN_IDLE := by
        rw [hpN, eN]; unfold LawfulStore.epState; rw [hout1 _ (oT hN0)]; exact h1
      have eB1 : L.mem s1 (ntfnBtA p.ntfn) = L.mem s (ntfnBtA N) := by rw [hpN, eN]; exact hout1 _ (oBt hN0)
      obtain ⟨q1, q2⟩ := fireTail_idle (fire_ok_tail efo) pn0 eS1 (by rw [eB1]; exact hb0)
      rw [eB1, hpTM] at q1
      rw [q1] at hbr
      refine ⟨q1, hbr, ?_⟩
      rw [hpTM, stA_eq, htcb1 hTMs.1 (K := 3328#u64) (by simp) (by simp), ← stA_eq] at q2
      exact q2
  obtain ⟨X2, eX2, wX2, hT2, tmf2⟩ : ∃ X2, (if L.mem X1 (boundA TM) != 0#u64 then
        notification.send_signal st ar X1 a3 (L.mem X1 (boundA TM)) (L.mem s3 (tbA TM)) else ok (X1, a3)) =
        ok (X2, a3) ∧ WritesIn st X1 X2 (fun b => N ≠ 0#u64 ∧ SaD N b) ∧ TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X2 ∧
        TmFr st T Cs Nt X1 X2 := by
    rw [bX1]
    by_cases hN0 : N = 0#u64
    · refine ⟨X1, by rw [hN0]; simp, ⟨rfl, rfl, fun b _ _ => rfl⟩, hT1, TmFr.refl X1⟩
    · obtain ⟨w1, w2⟩ := hnwX hN0
      obtain ⟨X2, e, w, t, f⟩ := send_signal_nw ar X1 a3 N (L.mem s3 (tbA TM)) hT1 (nNt hN0) (hNt N (nNt hN0)) w1
        (fun hi hb => by
          obtain ⟨q1, q2, q3⟩ := w2 hi hb
          rw [q1]; exact ⟨q2, q3, hTMs.1⟩)
      exact ⟨X2, by rw [if_pos (bne_iff_ne.mpr hN0)]; exact e, w.mono fun b hb => ⟨hN0, hb⟩, t, f⟩
  have k2 : L.ksb X2 = L.ksb s := wX2.1.trans (w31.1.trans k3)
  have c2 : L.cpu X2 = L.cpu s := wX2.2.1.trans (w31.2.1.trans c3)
  have e2N : ∀ o, L.nodeAt X2 (L.cpu X2) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c2, nodeAt_of_ksb k2]
  have hN2 : NodePlaced st T X2 (L.cpu X2) := by rw [c2]; exact hN.ksb k2
  have hcC2 : L.cpu X2 ∈ Cs := by rw [c2]; exact hcC
  -- `FireStop` after the `REPROGRAM` write
  have rD3 : ∀ y ∈ T, FootLtArmed st s3 (L.cpu s3) y → R (tdA y) := fun y hy ha => by
    obtain ⟨a1', a2'⟩ := ha
    have e1 : L.mem s3 (tdA y) = L.mem s (tdA y) := htcb3 hy (K := 3528#u64) (by simp) (by simp)
    have e2 : L.mem s3 (thA y) = L.mem s (thA y) := htcb3 hy (K := 3568#u64) (by simp) (by simp)
    rw [e1] at a1'; rw [e2, c3] at a2'
    exact rT y hy ⟨a1', a2'⟩ 3528#u64 (by simp) (by simp) (by simp)
  have hst : FireStop st R (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64) now :=
    fire_stop (R := R) (Cs := Cs) hT (TInv.rb hT3) hN3a hcC3 (by rw [tm3, hpTM]) hp0
      (fun y hy K h1 h2 h3 => by rw [htcb3 hy (by omega) h3, htcb1 hy (by omega) h3]) efo
      (by rw [hpTM]; exact eX1) ⟨TAgree.of_tmfr tmf2, wX2.1, wX2.2.1⟩
      (ndR s3 e3N _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])) rD3
  have d3 : L.mem s3 (tdA TM) = L.mem s1 (tdA TM) :=
    (htcb3 hTMs.1 (K := 3528#u64) (by simp) (by simp)).trans (htcb1 hTMs.1 (K := 3528#u64) (by simp) (by simp)).symm
  have hdue1 : L.mem s1 (tdA TM) ≤ now := by
    have h := edue
    rw [← c1] at h
    unfold localtimer.timer_due at h
    rw [eq_of_spec_fd (obj.node_get.spec (L := L) s1 _ _)] at h; simp only [bind_ok] at h
    rw [eq_of_spec_fd (obj.Tcb.is_null.spec _)] at h; simp only [bind_ok] at h
    have tm1 : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) = TM := by
      rw [e1N, ← eTM]
      exact hnode1 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
        (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
    rw [tm1] at h
    simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte] at h
    rw [eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) s1 _)] at h; simp only [bind_ok] at h
    simpa using ok_inj_ff h
  have hfire : timer.fire st ar s3 a3 = ok (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64, a3) :=
    fire_run (R' := R) ar s3 a3 (by rw [tm3]; exact hne)
      (by rw [tm3, ct3, d3]; exact not_lt.mpr hdue1) (by rw [tm3]; exact eX1) (by rw [tm3]; exact eX2)
      (by rw [ct3]; exact hst)
  -- `fire` on the guarded store
  have gfire : timer.fire gS ar s3 a3 = timer.fire st ar s3 a3 := by
    refine timer.fire.guard_one ar s3 a3
      (ndR s3 e3N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (ndR s3 e3N _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
      (by rw [tm3]; exact hne)
      (by rw [tm3]; exact rT TM hTMs.1 hTMs.2 3528#u64 (by simp) (by simp) (by simp))
      (by rw [tm3, ct3, d3]; exact not_lt.mpr hdue1)
      (by rw [tm3]; exact rT TM hTMs.1 hTMs.2 3536#u64 (by simp) (by simp) (by simp))
      (by rw [tm3]; exact hrmg) ?_
    rw [tm3]
    intro X1' e1'
    rw [eX1] at e1'
    obtain rfl := ok_inj_ff e1'
    refine ⟨?_, fun hb => ?_, fun X2' a2' e2' => ?_⟩
    · exact gRd _ (field_aligned (hT TM hTMs.1) (by simp) (by simp))
        (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [eTM]; exact hne, by
          rw [eTM]; exact Or.inl ⟨3368#u64, by simp, rfl⟩⟩))))))
    · rw [bX1] at hb ⊢
      obtain ⟨hw1, hw2⟩ := hnwX hb
      have eS : L.epState X1 N = L.epState s N := by unfold LawfulStore.epState; rw [kO1 _ (oT hb)]
      obtain ⟨p1, p2⟩ := hO.ntP _ (nNt hb)
      have wTS : W (core.num.U64.wrapping_add N layout.ntfn.TAIL_STATE) :=
        wN hb _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]) (by rw [eTS]; exact nsO _ (oT hb))
      have wBd : W (core.num.U64.wrapping_add N layout.ntfn.BADGE) :=
        wN hb _ (by simp [layout.ntfn.BADGE]) (by simp [layout.ntfn.BADGE]) (by simp [layout.ntfn.BADGE]) (nsO _ (oB hb))
      have rBd : R (core.num.U64.wrapping_add N layout.ntfn.BADGE) :=
        rN hb _ (by simp [layout.ntfn.BADGE]) (by simp [layout.ntfn.BADGE])
      refine notification.send_signal.guardF ar X1 a3 N _
        (rN hb _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE])) (oT hb).1 (oB hb).1
        (fun _ _ => ⟨rBd, wBd⟩) (fun hi => ⟨rN hb _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB]),
          fun _ => ⟨wTS, wBd⟩, fun hb0 => ?_⟩) (fun hw => absurd hw hw1)
      obtain ⟨q1, q2, q3⟩ := hw2 hi hb0
      rw [q1]
      refine ⟨gRd _ (by rw [stA_eq]; exact field_aligned (hT TM hTMs.1) (by simp) (by simp))
          (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [eTM]; exact hne, by
            rw [eTM]; exact Or.inr ⟨hh, Or.inl ⟨3328#u64, by simp, by rw [stA_eq]⟩⟩⟩)))))), q3,
        fun _ Y wY => ?_, fun hr => absurd hr q2⟩
      have hTa := hT TM hTMs.1
      rw [wY.mem_eq (by rw [stA_eq]; exact field_aligned hTa (by simp) (by simp)) (by
        rintro (e | e)
        · rw [stA_eq] at e; exact out_ne_field (oT hb) hTMs.1 hTa (by simp) (congrArg UScalar.val e)
        · rw [stA_eq] at e; exact out_ne_field (oB hb) hTMs.1 hTa (by simp) (congrArg UScalar.val e))]
      exact q3
    · rw [eX2] at e2'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff e2')
      refine ⟨by rw [e2N]; exact nW _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]), ?_⟩
      rw [ct3]; exact hst
  -- the state after `fire`
  obtain ⟨Y, eY⟩ : ∃ Y, L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64 = Y := ⟨_, rfl⟩
  rw [eY] at hst hfire
  have aRP : Aligned (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) := by
    rw [e2N]; exact nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
  have w1Y : WritesIn st s1 Y (fun b => ((HW st s1 b ∨ Fl4Proofs.P1.TW st T Cs s3 b) ∨ (N ≠ 0#u64 ∧ SaD N b)) ∨
      b = L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) := by
    rw [← eY]; exact ((w13.trans w31).trans wX2).trans (writesIn_wr aRP)
  have kY : L.ksb Y = L.ksb s := w1Y.1.trans k1
  have cY : L.cpu Y = L.cpu s := w1Y.2.1.trans c1
  have eYN : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o := fun o => by rw [cY, nodeAt_of_ksb kY]
  have hNY : NodePlaced st T Y (L.cpu Y) := by rw [cY]; exact hN.ksb kY
  have hcCY : L.cpu Y ∈ Cs := by rw [cY]; exact hcC
  -- this core's node words other than `REPROGRAM`, `ARMED` and the timer words
  have nY : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 56 → o.val ≠ 80 → o.val ≠ 104 → o.val ≠ 112 →
      L.mem Y (L.nodeAt s (L.cpu s) o) = L.mem s1 (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h56 h80 h104 h112
    refine w1Y.mem_eq (nodeAt_aligned hN ho h8) ?_
    rintro (((⟨o', hP, ho', -, e⟩ | ⟨y, hy, K, h1, h2, e⟩ | ⟨c, hc, o', ho', e⟩) | ⟨hN0, e | e⟩) | e)
    · rw [e1N] at e
      exact nodeAt_ne hN ho ho' (by rcases hP with h | h <;> omega) e
    · exact node_ne_field hN ho hy (hT y hy) (by omega) e
    · rw [nodeAt_of_ksb k3] at e
      by_cases hcc : c = L.cpu s
      · subst hcc; exact nodeAt_ne hN ho (by rcases ho' with h | h <;> omega) (by rcases ho' with h | h <;> omega) e
      · exact nodeAt_ne_cpu hN (hNa c hc) ho (by rcases ho' with h | h <;> omega) (Ne.symm hcc) e
    · exact out_ne_node (oT hN0) hcC hN ho (congrArg UScalar.val e)
    · exact out_ne_node (oB hN0) hcC hN ho (congrArg UScalar.val e)
    · rw [e2N] at e
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      exact nodeAt_ne hN ho (by omega) (by omega) e
  -- the threads' words outside the timer fields
  have tY : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      L.mem Y (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK h8 hK'
    have hya := hT y hy
    refine (w1Y.mem_eq (field_aligned hya hK h8) ?_).trans (htcb1 hy hK h8)
    rintro (((⟨o', -, ho', -, e⟩ | ⟨y', hy', K', h1, h2, e⟩ | ⟨c, hc, o', ho', e⟩) | ⟨hN0, e | e⟩) | e)
    · exact node_ne_field hN1 ho' hy hya hK e.symm
    · exact field_ne hya (hT y' hy') hK (by omega) (fun _ => by omega) e
    · exact node_ne_field (hN3a c hc) (by rcases ho' with h | h <;> omega) hy hya hK e.symm
    · exact out_ne_field (oT hN0) hy hya hK (congrArg UScalar.val e)
    · exact out_ne_field (oB hN0) hy hya hK (congrArg UScalar.val e)
    · exact node_ne_field hN2 (by simp [layout.node.REPROGRAM]) hy hya hK e.symm
  -- the SCs' words
  have scY : ∀ c ∈ Scs, ∀ b, Aligned b → InSC c (Z c) b → L.mem Y b = L.mem s b := by
    intro c hc b hb hin
    have hΩ := hO.scW c hc b hb hin
    have ho := h0.omega b hΩ
    refine (w1Y.mem_eq hb ?_).trans (hout1 b ho)
    rintro (((⟨o', -, ho', -, e⟩ | htw) | ⟨hN0, e | e⟩) | e)
    · exact out_ne_node (ho.ksb k1) hcC1 hN1 ho' (congrArg UScalar.val e).symm
    · exact out_not_tw hT hN3a (ho.ksb k3) htw
    · obtain ⟨p1, p2⟩ := hO.ntP _ (nNt hN0)
      have := hO.ntOSc N (nNt hN0) c hc
      have ev := congrArg UScalar.val e
      rw [epTSA_val' (by omega)] at ev
      unfold InSC at hin; omega
    · obtain ⟨p1, p2⟩ := hO.ntP _ (nNt hN0)
      have := hO.ntOSc N (nNt hN0) c hc
      have ev := congrArg UScalar.val e
      rw [ntfnBdA_val ⟨p1, p2⟩] at ev
      unfold InSC at hin; omega
    · exact out_ne_node (ho.ksb k2) hcC2 hN2 (by simp [layout.node.REPROGRAM]) (congrArg UScalar.val e).symm
  have hcurY : L.curW Y = L.curW s := by
    unfold LawfulStore.curW
    rw [eYN, nY _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
      (by rw [curth_val]; omega) (by rw [curth_val]; omega) (by rw [curth_val]; omega)]
    exact hnode1 _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega) (by rw [curth_val]; omega)
  have hcsY : L.cscW Y = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [eYN, nY _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]
    exact hnode1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  have actY : L.actionW Y = sched.ACTION_RESUME_CURRENT := by
    unfold LawfulStore.actionW
    rw [eYN, nY _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega) (by rw [act_val]; omega)
      (by rw [act_val]; omega) (by rw [act_val]; omega),
      hnode1 _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega) (by rw [act_val]; omega)]
    exact hact0
  have ctY : L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.CUR_TIME) = now := by
    rw [eYN, nY _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]), ← e1N]
    exact hnow
  have rhY : L.mem Y (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := by
    rw [nY _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])]
    exact hnode1 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have scaY : ∀ y ∈ T, L.mem Y (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact tY y hy _ (by simp) (by simp) (Or.inl (by simp))
  have relY : RelNone st Y := by
    have r1 : RelNone st s1 := rel_false (by rw [c1]; exact erel)
    refine rel_agree hB1 (kY.trans k1.symm) (cY.trans c1.symm) ?_ ?_ ?_ ?_ r1
    · rw [e1N, rhY]; exact (hnode1 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
        (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])).symm
    · unfold LawfulStore.curTime LawfulStore.nodeA
      rw [ctY, hnow]
    · intro y hy; rw [scaY y hy, scA_eq, htcb1 hy (K := 3464#u64) (by simp) (by simp)]
    · intro c hc b hb hin; rw [scY c hc b hb hin, (hout1 b (h0.omega b (hO.scW c hc b hb hin)))]
  have nodY : L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.CUR_TIME) <
        L.mem Y (tdA (L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN))) := by
    by_cases hz : L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN) = 0#u64
    · exact Or.inl hz
    · right; rw [ctY]; exact (hst.2 hz).2
  -- `awaken`
  have haw : sched.awaken st ar s3 a3 = ok (Y, a3) := by
    unfold sched.awaken
    rw [hfire]
    simp only [bind_ok, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
    rw [awaken_loop_none Y _ relY]
    simp only [bind_ok, bind_tc_ok]
  have hrs : ∀ hne' : L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD) ≠ 0#u64,
      R (scA (L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD))) ∧
      RdHead (L := L) R Y (L.mem Y (scA (L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD)))) := by
    intro hne'
    rw [eYN, rhY] at hne' ⊢
    obtain ⟨r1, -, -, r4, r5⟩ := rel_facts hI hne'
    rw [scaY _ r1]
    have hqr := scq_of hO hS r4
    refine ⟨gRd _ (by rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp))
      (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne', Or.inl rfl⟩))))), ?_⟩
    refine PathObl.ScAcc.head (W := fun _ => True)
      ⟨fun b ha hb => gRd _ ha (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne', Or.inr hb⟩))))), fun _ _ _ => trivial,
        trivial⟩ ((SCq.agree' hqr (fun b hb hin => scY _ r4 b hb hin)).1 ?_)
    unfold LawfulStore.rmax
    rw [scY _ r4 _ hqr.2.2.2.2 hqr.2.2.2.1]; exact r5
  have hawg : sched.awaken gS ar s3 a3 = sched.awaken st ar s3 a3 :=
    sched.awaken.guard_fire ar s3 a3 gfire (fun Y' a' e => by
      rw [hfire] at e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff e)
      rw [sched.awaken_loop.guard_nodue Y _
        (ndR Y eYN _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])) hrs
        (by unfold ctA; rw [eYN]; exact nR _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])) relY,
        awaken_loop_none Y _ relY])
  -- `schedule`'s tail at `Y`: the action is `RESUME_CURRENT`
  have hctY : L.curW Y ∈ T := by rw [hcurY]; exact hcT
  have hsameY : L.mem Y (scA (L.curW Y)) = L.cscW Y := by rw [hcurY, hcsY, scaY _ hcT]; exact hsct
  have hcY : SCq st Y Ω (L.cscW Y) (Z (L.cscW s)) := by
    rw [hcsY]; exact SCq.agree' hcq (fun b hb hin => scY _ hcs b hb hin)
  have homY : ∀ b ∈ Ω, OutsideObjs st T Cs Y b := fun b hb => (h0.omega b hb).ksb kY
  have hres := resume_hsw_hfr (gS := gS) ar hA Y a3 (zc := Z (L.cscW s)) hcCY hNY hT homY hctY hsameY hcY
    (by rw [hcsY]; unfold LawfulStore.rmax; rw [scY _ hcs _ hcq.2.2.2.2 hcq.2.2.2.1]; exact hmx0)
    (fun o h1 h2 => by rw [eYN]; exact ⟨nR o h1 h2, nW o h1 h2⟩) (by rw [hcsY]; exact hSc)
    (by rw [hcurY]; exact rSc) (by rw [kY]; exact hD2)
    (fun hne' => by
      have hne'' := hne'
      change L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD) ≠ 0#u64 at hne''
      rw [eYN, rhY] at hne''
      obtain ⟨r1, -, -, r4, r5⟩ := rel_facts hI hne''
      have hqr := scq_of hO hS r4
      have e0 : L.mem Y (rhA (L := L) Y) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := by
        show L.mem Y (L.nodeAt Y (L.cpu Y) _) = _
        rw [eYN, rhY]
      rw [e0, scaY _ r1, hcsY]
      refine ⟨_, r1, gRd _ (by rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp))
        (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne'', Or.inl rfl⟩))))),
        SCq.agree' hqr (fun b hb hin => scY _ r4 b hb hin), ?_,
        fun b hb ha => gRd _ ha (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne'', Or.inr hb⟩))))),
        fun hn b hb => ?_, fun e => by rw [e]⟩
      · unfold LawfulStore.rmax
        rw [scY _ r4 _ hqr.2.2.2.2 hqr.2.2.2.1]; exact r5
      · have := hO.scDisj _ r4 _ hcs hn
        unfold Outside; unfold InSC at hb; omega)
    (fun hne' => by
      have hz := hne'
      change L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN) ≠ 0#u64 at hz
      have e5 : L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN) =
          L.mem X2 (L.nodeAt X2 (L.cpu X2) layout.node.TIMER_MIN) := by
        rw [← eY, nodeAt_of_ksb (L.ksb_wr _ _ _), LawfulStore.cpu_wr]
        exact mem_wr_ne' aRP (nodeAt_aligned hN2 (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
          (nodeAt_ne hN2 (by simp [layout.node.REPROGRAM]) (by simp [layout.node.TIMER_MIN])
            (by simp [layout.node.REPROGRAM, layout.node.TIMER_MIN]))
      rw [e5] at hz
      have hTm : L.mem Y (tmA (L := L) Y) ∈ T := by
        rw [show tmA (L := L) Y = L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN from rfl, e5]
        exact (tmin_facts hT2 hcC2 hz).1
      exact ⟨hTm, (hst.2 hne').1⟩)
  have gsc : sched.schedule gS ar s3 a3 = sched.schedule st ar s3 a3 := by
    refine sched.schedule.guard_sw ar s3 a3 hawg fun Y' a' e => ?_
    rw [haw] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff e)
    refine ⟨ndR Y eYN _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]),
      fun h => absurd actY h, fun s3' a2' e' => ?_⟩
    rw [actY, bne_self_eq_false, if_neg Bool.false_ne_true] at e'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff e')
    exact PathObl.LT.schedRes.guard ar Y a3 (fun o h1 h2 => by rw [eYN]; exact ⟨nR o h1 h2, nW o h1 h2⟩)
      hres.1 hres.2
  -- `schedule` on `st` is `schedTail` at `Y`
  have hacY : sched.action st Y = ok sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) Y), actY]
  have esch : sched.schedule st ar s3 a3 = schedTail (st := st) ar Y a3 := by
    rw [schedule_sw_eq, haw]
    simp only [bind_ok, Aeneas.Std.uncurry_apply_pair]
    rw [hacY]
    simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact (PathObl.LT.schedule_res_eq st ar Y a3 (awaken_none ar Y a3 nodY relY) hacY).symm.trans
      (schedule_resume ar Y a3 nodY relY actY)
  unfold FireTailG
  refine ⟨gsc, fun s4 a4 esc => ?_⟩
  have hfp := schedTail_fp ar hA Y a3 (zc := Z (L.cscW s))
    (B := fun b => (∀ K : U64, K.val < 4096 → b ≠ core.num.U64.wrapping_add (L.curW s) K) ∧
      b ≠ L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
    hcCY hNY hT homY hctY hsameY hcY
    (fun o ho h8 hz => by
      rw [eYN]
      refine ⟨fun K hK => node_ne_field hN ho hcT ht' hK, fun e => hz ?_⟩
      have e' := congrArg UScalar.val e
      rw [nodeAt_val hN ho, nodeAt_val hN (by rw [curth_val]; omega), curth_val] at e'
      omega)
    (fun b hb hin => by
      rw [hcsY] at hin
      have ho := h0.omega b (hcq.2.1 b hb hin)
      exact ⟨fun K hK e => out_ne_field ho hcT ht' hK (congrArg UScalar.val e).symm,
        fun e => out_ne_node ho hcC hN (by rw [curth_val]; omega) (congrArg UScalar.val e).symm⟩)
  rw [← esch, esc, WP.spec_ok] at hfp
  have w34 := hfp
  have k4 : L.ksb s4 = L.ksb s := w34.1.trans kY
  have c4 : L.cpu s4 = L.cpu s := w34.2.1.trans cY
  have e4N : ∀ o, L.nodeAt s4 (L.cpu s4) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c4, nodeAt_of_ksb k4]
  have hcur4 : L.curW s4 = L.curW s := by
    have h3 := hcurY
    unfold LawfulStore.curW at h3 ⊢
    rw [eYN] at h3
    rw [w34.2.1, nodeAt_of_ksb w34.1, eYN,
      w34.mem_eq (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) (fun hb => hb.2 rfl)]
    exact h3
  have tK4 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      L.mem s4 (core.num.U64.wrapping_add (L.curW s) K) = L.mem s (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K hK h8 hK' => (w34.mem_eq (field_aligned ht' hK h8) (fun hb => hb.1 K hK rfl)).trans (tY _ hcT K hK h8 hK')
  have hy4 : L.mem s4 (yieldA (L.curW s)) = 0#u64 := by
    unfold yieldA
    rw [tK4 _ (by simp) (by simp) (Or.inl (by simp))]
    exact hy0
  have hst4 : L.mem s4 (stA (L.curW s)) = L.mem s (stA (L.curW s)) := by
    rw [stA_eq, tK4 _ (by simp) (by simp) (Or.inl (by simp))]
  have sc4 : L.mem s4 (scA (L.curW s)) = L.cscW s := by
    rw [scA_eq, tK4 _ (by simp) (by simp) (Or.inl (by simp)), ← scA_eq]; exact hsct
  have aff4 : L.mem s4 (affA (L.curW s)) = L.cpu s := by
    unfold affA; rw [tK4 _ (by simp) (by simp) (Or.inl (by simp))]; exact haff
  have hN4 : NodePlaced st T s4 (L.cpu s4) := by rw [c4]; exact hN.ksb k4
  have eNx : regA (L.curW s) layout.reg.NEXT_IP = core.num.U64.wrapping_add (L.curW s) 368#u64 := by
    obtain ⟨K, hK, e⟩ := regA_eq ht' (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])
    rw [e]
    congr 1
    apply UScalar.eq_of_val_eq
    rw [hK]
    simp [layout.reg.NEXT_IP]
  have aNx : Aligned (regA (L.curW s) layout.reg.NEXT_IP) := by rw [eNx]; exact field_aligned ht' (by simp) (by simp)
  have sA : Aligned (stA (L.curW s)) := by rw [stA_eq]; exact field_aligned ht' (by simp) (by simp)
  have aA : Aligned (affA (L.curW s)) := field_aligned ht' (by simp) (by simp)
  have nNs : regA (L.curW s) layout.reg.NEXT_IP ≠ stA (L.curW s) := by
    rw [eNx, stA_eq]; exact tcb_word_ne ht' ht' (by simp) (by simp) (fun _ => by simp)
  have nNa : regA (L.curW s) layout.reg.NEXT_IP ≠ affA (L.curW s) := by
    rw [eNx]; exact tcb_word_ne ht' ht' (by simp) (by simp) (fun _ => by simp)
  have gac : sched.activate_thread gS ar s4 a4 = sched.activate_thread st ar s4 a4 :=
    activate_thread.gw ar s4 a4 hcur4 ht' hy4 (nrm s4 e4N) rYt rSt (rR _ (by simp [layout.reg.FAULT_IP]))
      (rW _ (by simp [layout.reg.NEXT_IP]))
      (fun hr pc => hwS _ (by rw [mem_wr_ne' aNx sA nNs]; exact hr) (by rw [mem_wr_ne' aNx aA nNa]; exact aff4))
      rSc (by rw [sc4]; exact rMx) rIq
  refine ⟨gac, fun s5 a5 eac => ?_⟩
  obtain ⟨w45, hst5⟩ := activate_fp ar hT hcT hN4 hcur4 hy4 eac
  have e5N : ∀ o, L.nodeAt s5 (L.cpu s5) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [w45.2.1, nodeAt_of_ksb w45.1, e4N]
  have hst5' : L.mem s5 (stA (L.curW s)) ≠ sched.TS_RUNNING_VM := by
    rcases hst5 with e | e
    · rw [e]; simp [sched.TS_RUNNING, sched.TS_RUNNING_VM]
    · rw [e, hst4]; exact hnvm
  have hcur5 : L.curW s5 = L.curW s := by
    have e : L.curW s5 = L.curW s4 := by
      unfold LawfulStore.curW
      rw [w45.2.1, nodeAt_of_ksb w45.1]
      refine w45.mem_eq (nodeAt_aligned hN4 (by rw [curth_val]; omega) (by rw [curth_val])) ?_
      rintro (e | e | e)
      · exact tcb_node_ne hN4 hcT ht' (by simp) (by rw [curth_val]; omega) e.symm
      · rw [stA_eq] at e
        exact tcb_node_ne hN4 hcT ht' (by simp) (by rw [curth_val]; omega) e.symm
      · have e' := congrArg UScalar.val e
        rw [nodeAt_val hN4 (by rw [curth_val]; omega), nodeAt_val hN4 (by rw [act_val]; omega), curth_val,
          act_val] at e'
        omega
    rw [e, hcur4]
  refine ⟨PathObl.sched.cur_thread.guard s5 (ndR s5 e5N _ (by rw [curth_val]; omega) (by rw [curth_val])),
    fun t et => ?_⟩
  rw [cur_thread_ok, hcur5] at et
  have et' := ok_inj_ff et
  subst et'
  exact vcpu.check.guard_nvm ar s5 a5 (L.curW s) rSt hst5'

end main

end Fl4Proofs.P2
