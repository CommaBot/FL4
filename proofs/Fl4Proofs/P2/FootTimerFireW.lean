/-
# P2 (p2lf): waking a thread from a fired timer's signal, on the guarded store

`send_signal` wakes a thread `w` from a wait on notification `n` (its `WAITING` queue head after `ntfn_dequeue`,
or its bound thread blocked in `Recv` after `cancel_ipc`) with the same tail, `wakeTail`: `w` made `RUNNING`, the
badge register, `maybe_donate_sched_context`, `possible_switch_to` when schedulable, `unblock_sporadic`.
`wakeTail.guard`: on any store `gS` answering `R` reads and `W` writes as `st`, for a thread `w` that is not the
current thread, may run here (`fire_ok`'s `wake_ok`: this core, the current domain), takes no SC from `n`, and with
the action `RESUME_CURRENT`, `wakeTail` is its real run; the state-dependent words are premises at every state
reached from the start by writes to `w`'s `STATE`, its badge register and this core's `SCHED_ACTION` (`WkD`).

Pieces: `sched.possible_switch_to.guard_here`, `notification.maybe_donate_sched_context.guard_nd`,
`notification.unblock_sporadic.guard`.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireQ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (bind_guard_congr NodeSt ScAcc SWr)

/-- The tail of `send_signal`'s two wake-ups (`WAITING` after `ntfn_dequeue`, idle-bound after `cancel_ipc`). -/
def wakeTail {S : Type _} (M : machine.Store S) {A : Type _} (ar : machine.Arch A) (X : S) (a : A)
    (w n badge : U64) : Result (S × A) := do
  let s2 ← sched.set_thread_state M X w sched.TS_RUNNING
  let s3 ← obj.Tcb.set_reg M w s2 layout.reg.BADGE badge
  let (s4, a1) ← notification.maybe_donate_sched_context M ar s3 a w n
  let b ← sched.is_schedulable M s4 w
  let s5 ← if b then sched.possible_switch_to M s4 w else ok s4
  let s6 ← notification.unblock_sporadic M s5 w
  ok (s6, a1)

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

theorem NodeSt.of_wi {X Y : S} {D : U64 → Prop} (h : NodeSt (L := L) R W X) (w : WritesIn st X Y D) :
    NodeSt (L := L) R W Y := by
  unfold PathObl.NodeSt at h ⊢
  simp only [w.2.1, nodeAt_of_ksb w.1]
  exact h

/-- **`possible_switch_to` of a thread that may run here** in the current domain, with the action
`RESUME_CURRENT`: its `SC`, queue flags, domain and affinity, `CUR_DOMAIN`, then the action is set to it. -/
theorem sched.possible_switch_to.guard_here (X : S) (t : U64) (hn : NodeSt (L := L) R W X)
    (r1 : R (scA t)) (r2 : R (inqA t)) (r3 : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN))
    (r4 : R (domA t)) (r5 : R (affA t))
    (hd : L.mem X (domA t) = L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN))
    (ha : L.mem X (affA t) = L.cpu X) (hac : L.actionW X = sched.ACTION_RESUME_CURRENT) :
    sched.possible_switch_to gS X t = sched.possible_switch_to st X t := by
  obtain ⟨-, hra, hwa⟩ := hn
  unfold sched.possible_switch_to
  rw [PathObl.obj.Tcb.sc.guard (gS := gS) t X r1, tcb_sc_ok]
  simp only [bind_ok]
  by_cases h0 : L.mem X (scA t) = 0#u64
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0, PathObl.sched.in_release_queue.guard (gS := gS) X t r2]
  refine bind_guard_congr rfl fun b _ => ?_
  by_cases hb : b = true
  · rw [if_pos hb, if_pos hb]
  rw [if_neg hb, if_neg hb, PathObl.sched.cur_domain.guard (gS := gS) X r3, cur_domain_ok]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.domain.guard (gS := gS) t X r4, eq_of_spec_fd (obj.Tcb.domain.spec (L := L) X t)]
  simp only [bind_ok]
  rw [if_neg (by simp [hd]), if_neg (by simp [hd]), PathObl.obj.Tcb.affinity.guard (gS := gS) t X r5, aff_ok,
    PathObl.gst_cur_cpu (g := gS), L.cur_cpu_eq]
  simp only [bind_ok]
  rw [if_neg (by simp [ha]), if_neg (by simp [ha]), PathObl.sched.action.guard (gS := gS) X hra,
    eq_of_spec_fd (sched.action.spec (L := L) X), hac]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact PathObl.sched.set_action.guard (gS := gS) X _ hwa

/-- **`maybe_donate_sched_context` that donates nothing** (`t` has an SC, or `n` has none): reads `t`'s `SC` and,
when it is null, `n`'s. -/
theorem notification.maybe_donate_sched_context.guard_nd {A : Type} (ar : machine.Arch A) (X : S) (a : A)
    (t n : U64) (r1 : R (scA t)) (r2 : L.mem X (scA t) = 0#u64 → R (ntfnScA n))
    (hnd : L.mem X (scA t) = 0#u64 → L.mem X (ntfnScA n) = 0#u64) :
    notification.maybe_donate_sched_context gS ar X a t n = ok (X, a) ∧
      notification.maybe_donate_sched_context st ar X a t n = ok (X, a) := by
  have key : ∀ (M : machine.Store S), obj.Tcb.sc M t X = ok (L.mem X (scA t)) →
      (L.mem X (scA t) = 0#u64 → obj.Ntfn.sc M n X = ok (L.mem X (ntfnScA n))) →
      notification.maybe_donate_sched_context M ar X a t n = ok (X, a) := by
    intro M e1 e2
    unfold notification.maybe_donate_sched_context
    rw [e1]
    simp only [bind_ok]
    by_cases h0 : L.mem X (scA t) = 0#u64
    · rw [if_pos h0, e2 h0, hnd h0]
      simp only [bind_ok, eq_of_spec_fd (obj.Sc.is_null.spec 0#u64), decide_true, ↓reduceIte]
    · rw [if_neg h0]
  refine ⟨key gS ?_ ?_, key st (tcb_sc_ok X t) fun _ => eq_of_spec_fd (obj.Ntfn.sc.val (L := L) X n)⟩
  · rw [PathObl.obj.Tcb.sc.guard (gS := gS) t X r1, tcb_sc_ok]
  · intro h0
    rw [PathObl.obj.Ntfn.sc.guard (gS := gS) n X (r2 h0), eq_of_spec_fd (obj.Ntfn.sc.val (L := L) X n)]

theorem sporadic.sc_sporadic.guardQ (X : S) (sc : obj.Sc) (h : sc ≠ 0#u64 → R (sporA sc)) :
    sporadic.sc_sporadic gS X sc = sporadic.sc_sporadic st X sc := by
  unfold sporadic.sc_sporadic
  rw [eq_of_spec_fd (obj.Sc.is_null.spec sc)]; simp only [bind_ok]
  by_cases h0 : sc = 0#u64
  · simp only [h0, decide_true, ↓reduceIte]
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [PathObl.obj.Sc.sporadic.guard (gS := gS) sc X (h h0)]

/-- **`notification::unblock_sporadic`** (as p2sl's `endpoint.unblock_sporadic.guard`). -/
theorem notification.unblock_sporadic.guard (X : S) (d : obj.Tcb) {sb : Nat}
    (hsc : R (scA d)) (hsp : R (sporA (L.mem X (scA d))))
    (hcs : R (L.nodeAt X (L.cpu X) layout.node.CUR_SC))
    (hS : ScAcc R W (L.mem X (scA d)) sb) (hW : RefillsWF st X (L.mem X (scA d)) sb)
    (hrep : Aligned (L.nodeA X layout.node.REPROGRAM) ∧
      Outside (L.nodeA X layout.node.REPROGRAM) (L.mem X (scA d)) sb)
    (hct : R (ctA (L := L) X)) (hrp : W (L.nodeA X layout.node.REPROGRAM)) :
    notification.unblock_sporadic gS X d = notification.unblock_sporadic st X d := by
  unfold notification.unblock_sporadic
  rw [PathObl.obj.Tcb.sc.guard (gS := gS) d X hsc, eq_of_spec_fd (obj.Tcb.sc.spec (L := L) X d)]
  simp only [bind_ok]
  rw [sporadic.sc_sporadic.guardQ (gS := gS) X _ (fun _ => hsp)]
  refine bind_guard_congr rfl fun b _ => ?_
  by_cases hb : b = true
  · rw [if_pos hb, if_pos hb, PathObl.sched.cur_sc.guard (gS := gS) X hcs]
    refine bind_guard_congr rfl fun c _ => ?_
    refine bind_guard_congr rfl fun b1 _ => ?_
    by_cases hb1 : b1 = true
    · rw [if_pos hb1, if_pos hb1, PathObl.sporadic.unblock_check.guardS (gS := gS) hS hW hrep hct hrp]
    · rw [if_neg hb1, if_neg hb1]
  · rw [if_neg hb, if_neg hb]

/-- `possible_switch_to` of a thread that may run here in the current domain, with the action `RESUME_CURRENT`,
on `st`: nothing, or the action set to it. -/
theorem possible_switch_to_here_st (X : S) (t : U64)
    (hd : L.mem X (domA t) = L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN))
    (ha : L.mem X (affA t) = L.cpu X) (hac : L.actionW X = sched.ACTION_RESUME_CURRENT) :
    sched.possible_switch_to st X t = ok X ∨
      sched.possible_switch_to st X t = ok (L.wr X (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) t) := by
  unfold sched.possible_switch_to
  rw [tcb_sc_ok]
  simp only [bind_ok]
  by_cases h0 : L.mem X (scA t) = 0#u64
  · rw [if_pos h0]; exact Or.inl rfl
  rw [if_neg h0, eq_of_spec_fd (sched.in_release_queue.spec (L := L) X t)]
  simp only [bind_ok]
  by_cases hq : (L.mem X (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64
  · rw [if_pos (decide_eq_true hq)]; exact Or.inl rfl
  rw [if_neg (fun h => hq (of_decide_eq_true h))]
  rw [cur_domain_ok, eq_of_spec_fd (obj.Tcb.domain.spec (L := L) X t)]
  simp only [bind_ok]
  rw [if_neg (by simp [hd]), aff_ok, L.cur_cpu_eq]
  simp only [bind_ok]
  rw [if_neg (by simp [ha]), eq_of_spec_fd (sched.action.spec (L := L) X), hac]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact Or.inr (eq_of_spec_fd (sched.set_action.spec (L := L) X t))

/-- The words `wakeTail` writes before `unblock_sporadic`: `w`'s `STATE` and badge register, this core's
`SCHED_ACTION`. -/
def WkD (st : machine.Store S) [L : LawfulStore st] (X : S) (w b : U64) : Prop :=
  b = stA w ∨ b = regA w layout.reg.BADGE ∨ b = L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION

/-- What `wakeTail` needs at a state reached by `WkD` writes. -/
structure WkPre (st : machine.Store S) [L : LawfulStore st] (R W : U64 → Prop) (Y : S) (w n : U64) (sb : Nat) :
    Prop where
  mx : R (maxA (L.mem Y (scA w)))
  nsc : L.mem Y (scA w) = 0#u64 → R (ntfnScA n)
  nd : L.mem Y (scA w) = 0#u64 → L.mem Y (ntfnScA n) = 0#u64
  dom : L.mem Y (domA w) = L.mem Y (core.num.U64.wrapping_add (L.ksb Y) layout.ks.CUR_DOMAIN)
  aff : L.mem Y (affA w) = L.cpu Y
  sp : R (sporA (L.mem Y (scA w)))
  acc : ScAcc R W (L.mem Y (scA w)) sb
  wf : RefillsWF st Y (L.mem Y (scA w)) sb
  rep : Aligned (L.nodeA Y layout.node.REPROGRAM) ∧ Outside (L.nodeA Y layout.node.REPROGRAM) (L.mem Y (scA w)) sb
  ct : R (ctA (L := L) Y)
  rp : W (L.nodeA Y layout.node.REPROGRAM)
  cs : R (L.nodeAt Y (L.cpu Y) layout.node.CUR_SC)
  cd : R (core.num.U64.wrapping_add (L.ksb Y) layout.ks.CUR_DOMAIN)

set_option maxHeartbeats 4000000 in
/-- **`wakeTail` on the guarded store** (module docstring). -/
theorem wakeTail.guard {A : Type} (ar : machine.Arch A) (X : S) (a : A) (w n badge : U64) {sb : Nat}
    (hcur : w ≠ L.curW X) (hn : NodeSt (L := L) R W X)
    (aS : Aligned (stA w)) (aR : Aligned (regA w layout.reg.BADGE)) (nSR : stA w ≠ regA w layout.reg.BADGE)
    (aA : Aligned (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION))
    (nA1 : L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION ≠ stA w)
    (nA2 : L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION ≠ regA w layout.reg.BADGE)
    (aC : Aligned (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD))
    (nC1 : L.nodeAt X (L.cpu X) layout.node.CUR_THREAD ≠ stA w)
    (rS : R (stA w)) (wS : SWr gS st w sched.TS_RUNNING) (rSc : R (scA w)) (rI : R (inqA w))
    (rD : R (domA w)) (rA : R (affA w)) (wB : W (regA w layout.reg.BADGE))
    (hac : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (hY : ∀ Y, WritesIn st X Y (WkD st X w) → WkPre st R W Y w n sb) :
    wakeTail gS ar X a w n badge = wakeTail st ar X a w n badge := by
  -- `w` made `RUNNING` (not the current thread: no action write)
  have wi2 : WritesIn st X (L.wr X (stA w) sched.TS_RUNNING) (WkD st X w) :=
    ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hb' => mem_wr_ne' aS hb (fun e => hb' (Or.inl e.symm))⟩
  have hc2 : L.curW (L.wr X (stA w) sched.TS_RUNNING) = L.curW X := by
    unfold LawfulStore.curW
    rw [nodeAt_wr, L.cpu_wr]
    exact mem_wr_ne' aS aC (Ne.symm nC1)
  have hst2 : sched.set_thread_state st X w sched.TS_RUNNING = ok (L.wr X (stA w) sched.TS_RUNNING) := by
    unfold sched.set_thread_state
    rw [PathObl.set_state_ok']
    simp only [bind_ok]
    unfold sched.schedule_tcb
    rw [cur_thread_ok, hc2]
    simp only [bind_ok]
    rw [eq_of_spec_fd (tcb_eq.blk w (L.curW X))]
    simp only [bind_ok, hcur, decide_false, Bool.false_eq_true, ↓reduceIte]
  unfold wakeTail
  rw [PathObl.sched.set_thread_state.guardV (gS := gS) X w _ hn wS rS rSc (hY _ wi2).mx rI, hst2]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.set_reg.guard (gS := gS) w _ _ _ wB, PathObl.set_reg_ok']
  simp only [bind_ok]
  -- `X3`: the badge register written
  have wi3 : WritesIn st X (L.wr (L.wr X (stA w) sched.TS_RUNNING) (regA w layout.reg.BADGE) badge)
      (WkD st X w) :=
    ⟨by rw [L.ksb_wr, L.ksb_wr], by rw [L.cpu_wr, L.cpu_wr], fun b hb hb' => by
      rw [mem_wr_ne' aR hb (fun e => hb' (Or.inr (Or.inl e.symm)))]
      exact wi2.2.2 b hb hb'⟩
  have P3 := hY _ wi3
  obtain ⟨m1, m2⟩ := notification.maybe_donate_sched_context.guard_nd (gS := gS) ar
    (L.wr (L.wr X (stA w) sched.TS_RUNNING) (regA w layout.reg.BADGE) badge) a w n rSc P3.nsc P3.nd
  rw [m1, m2]
  simp only [bind_ok, Aeneas.Std.uncurry_apply_pair]
  rw [PathObl.sched.is_schedulable.guard (gS := gS) _ w rS rSc P3.mx rI]
  refine bind_guard_congr rfl fun b _ => ?_
  have hac3 : L.actionW (L.wr (L.wr X (stA w) sched.TS_RUNNING) (regA w layout.reg.BADGE) badge) =
      sched.ACTION_RESUME_CURRENT := by
    unfold LawfulStore.actionW
    rw [nodeAt_wr, nodeAt_wr, L.cpu_wr, L.cpu_wr, mem_wr_ne' aR aA (Ne.symm nA2), mem_wr_ne' aS aA (Ne.symm nA1)]
    exact hac
  have hn3 := NodeSt.of_wi hn wi3
  refine bind_guard_congr ?_ fun s5 h5 => ?_
  · by_cases hb : b = true
    · rw [if_pos hb, if_pos hb]
      exact sched.possible_switch_to.guard_here (gS := gS) _ w hn3 rSc rI P3.cd rD rA P3.dom P3.aff hac3
    · rw [if_neg hb, if_neg hb]
  · have wi5 : WritesIn st X s5 (WkD st X w) := by
      by_cases hb : b = true
      · rw [if_pos hb] at h5
        rcases possible_switch_to_here_st _ w P3.dom P3.aff hac3 with e | e
        · rw [e] at h5; rw [← ok_inj_ff h5]; exact wi3
        · rw [e] at h5
          rw [← ok_inj_ff h5]
          refine ⟨by rw [L.ksb_wr]; exact wi3.1, by rw [L.cpu_wr]; exact wi3.2.1, fun c hc hc' => ?_⟩
          rw [nodeAt_wr, nodeAt_wr, L.cpu_wr, L.cpu_wr, mem_wr_ne' aA hc (fun e => hc' (Or.inr (Or.inr e.symm)))]
          exact wi3.2.2 c hc hc'
      · rw [if_neg hb] at h5; rw [← ok_inj_ff h5]; exact wi3
    have P5 := hY s5 wi5
    rw [notification.unblock_sporadic.guard (gS := gS) s5 w rSc P5.sp P5.cs P5.acc P5.wf P5.rep P5.ct P5.rp]

end gst

end Fl4Proofs.P2
