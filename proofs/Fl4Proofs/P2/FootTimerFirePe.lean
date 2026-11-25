/-
# P2 (p2lf): the plan's endpoint and reply are P1 objects

* `plan_recv`: when the plan names an endpoint or a reply, the due thread `TM` (non-null) is `BLOCKED_ON_RECV`, the
  endpoint is its `BLOCK_OBJ` (non-null) and the reply its `REPLY` word at the entry state (`plan_objects`,
  localtimer.rs:333-367).
* `plan_pe_pr`: from P1 at the entry state, the plan's endpoint is a heap endpoint whose two words are aligned
  (`EpsWit`: a `RECV`-blocked thread's `BLOCK_OBJ` is in `E` and typed `.ep` by `EpTy`, placed by `EpPlaced`), and
  the plan's reply is a P1 reply (`ReplyInv.recv`) whose `TCB` word is aligned (`rp_facts`). These are the `hPE` /
  `hPR` hypotheses of `irq_acc_fire_wk` / `irq_move_fire_wk`.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireAw
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section plan
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- When the plan names an endpoint or a reply: the due thread's `RECV` state, `BLOCK_OBJ` and `REPLY`. -/
theorem plan_recv {s : S} {tip : localtimer.TimerIrqPlan} (h : localtimer.plan_objects st s = ok tip)
    (he : tip.ep ≠ 0#u64 ∨ tip.reply ≠ 0#u64) :
    tip.tm = L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ∧ tip.tm ≠ 0#u64 ∧ tip.ep ≠ 0#u64 ∧
      L.mem s (stA tip.tm) = sched.TS_BLOCKED_ON_RECV ∧ tip.ep = L.mem s (blockA tip.tm) ∧
      tip.reply = L.mem s (replyA tip.tm) := by
  have nz : ¬ ((0#u64 : U64) ≠ 0#u64 ∨ (0#u64 : U64) ≠ 0#u64) := by simp
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
    exact absurd he nz
  rw [if_neg (by simpa using h0)] at h
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  by_cases ha : (i1 != L.cpu s) = true
  · rw [if_pos ha] at h
    obtain rfl := ok_inj_ff h
    exact absurd he nz
  rw [if_neg ha] at h
  have e1 : i1 = L.cpu s := by by_contra hne; exact ha (bne_iff_ne.mpr hne)
  subst e1
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  by_cases hb : (i2 != L.cpu s) = true
  · rw [if_pos hb] at h
    obtain rfl := ok_inj_ff h
    exact absurd he nz
  rw [if_neg hb] at h
  have e2 : i2 = L.cpu s := by by_contra hne; exact hb (bne_iff_ne.mpr hne)
  subst e2
  obtain ⟨n, en, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en
  obtain rfl := ok_inj_ff en
  by_cases hn : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) = 0#u64
  · rw [if_pos hn] at h
    obtain rfl := ok_inj_ff h
    exact absurd he nz
  rw [if_neg hn] at h
  obtain ⟨⟨x0, bk⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨i3, -, h⟩ := bind_eq_ok h
  by_cases h3 : (i3 != obj.NTFN_IDLE) = true
  · rw [if_pos h3] at h
    obtain rfl := ok_inj_ff h
    exact absurd he nz
  rw [if_neg h3] at h
  obtain ⟨i4, -, h⟩ := bind_eq_ok h
  by_cases h4 : (i4 != L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) = true
  · rw [if_pos h4] at h
    obtain rfl := ok_inj_ff h
    exact absurd he nz
  rw [if_neg h4] at h
  obtain ⟨i5, ei5, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s _)] at ei5
  have ei5' := ok_inj_ff ei5
  by_cases h5 : (i5 != sched.TS_BLOCKED_ON_RECV) = true
  · rw [if_pos h5] at h
    obtain rfl := ok_inj_ff h
    exact absurd he nz
  rw [if_neg h5] at h
  have e5 : i5 = sched.TS_BLOCKED_ON_RECV := by by_contra hne; exact h5 (bne_iff_ne.mpr hne)
  obtain ⟨ep, eep, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (obj.Tcb.block_obj.spec (L := L) s _)] at eep
  have eep' := ok_inj_ff eep
  by_cases h6 : ep = 0#u64
  · rw [if_pos h6] at h
    obtain rfl := ok_inj_ff h
    exact absurd he nz
  rw [if_neg h6] at h
  obtain ⟨⟨y0, bk1⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨r, er, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (obj.Tcb.reply_obj.spec (L := L) s _)] at er
  have er' := ok_inj_ff er
  by_cases h7 : (r != 0#u64) = true
  · rw [if_pos h7] at h
    obtain ⟨a3, -, h⟩ := bind_eq_ok h
    obtain rfl := ok_inj_ff h
    exact ⟨rfl, h0, h6, by rw [ei5', e5], eep'.symm, er'.symm⟩
  rw [if_neg h7] at h
  obtain rfl := ok_inj_ff h
  have h7' : r = 0#u64 := UScalar.eq_of_val_eq (by simpa using h7)
  exact ⟨rfl, h0, h6, by rw [ei5', e5], eep'.symm, by rw [er', h7']⟩

/-- **The plan's endpoint and reply are P1 objects** (module docstring). -/
theorem plan_pe_pr {s : S} {tip p : localtimer.TimerIrqPlan} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (etip : localtimer.plan_objects st s = ok tip) (eb : localtimer.same_plan tip p = ok true) :
    (p.ep ≠ 0#u64 → H p.ep = some .ep ∧
      ∀ k : U64, k.val < 16 → k.val % 8 = 0 → Aligned (core.num.U64.wrapping_add p.ep k)) ∧
    (p.reply ≠ 0#u64 → p.reply ∈ Rp ∧ Aligned (rTcbA p.reply)) := by
  obtain ⟨-, -, -, e4, e5⟩ := same_plan_all eb
  have h0 := hI.1.choose_spec.choose_spec
  have key : tip.ep ≠ 0#u64 ∨ tip.reply ≠ 0#u64 → tip.tm ∈ T ∧
      L.mem s (stA tip.tm) = sched.TS_BLOCKED_ON_RECV ∧ tip.ep = L.mem s (blockA tip.tm) ∧
      tip.reply = L.mem s (replyA tip.tm) := fun he => by
    obtain ⟨etm, htm0, -, hst, hep, hrp⟩ := plan_recv etip he
    refine ⟨?_, hst, hep, hrp⟩
    rw [etm]
    exact (tmin_facts (BXI.blk hI) h0.cur (by rw [← etm]; exact htm0)).1
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨htT, hst, hep, -⟩ := key (Or.inl (by rw [e4]; exact hp))
    obtain ⟨E, EQ, hEW⟩ := h0.eps
    obtain ⟨hepE, -⟩ := hEW.2.2.2.2.1 _ htT (by simp) (Or.inr (Or.inl hst))
    have hH := hEW.2.2.2.2.2.1 _ htT (by simp) (Or.inr hst)
    rw [← hep] at hepE hH
    rw [← e4]
    refine ⟨hH, fun k h1 h2 => ?_⟩
    obtain ⟨hE, -, -⟩ := hEW.1 _ hepE
    have := hE.align; have := hE.fits
    unfold Aligned
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    omega
  · obtain ⟨htT, hst, -, hrp⟩ := key (Or.inr (by rw [e5]; exact hp))
    have hX := hI.2.2.1
    have hr : p.reply ∈ Rp := by
      have := (hX.2.1.recv _ htT hst (by rw [← hrp, e5]; exact hp)).1
      rwa [← hrp, e5] at this
    obtain ⟨r32, rv, -, -⟩ := rp_facts hX.1 hr
    exact ⟨hr, by unfold Aligned; rw [rv]; omega⟩

end plan

end Fl4Proofs.P2
