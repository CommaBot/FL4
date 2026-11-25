/-
# P2 (p2lf): what an accepted `fire_ok` says of a waking signal

* `ntfn_head_ok`: `Ntfn::head` reads the queue head word.
* `wake_ok_true`: an accepted `wake_ok s cpu ct w n` (`localtimer.rs`): `w` is not `ct`, may run here, is in the
  current domain, not queued, takes no SC from `n`, and `top_ok` holds.
* `fireTail_wake`: an accepted `fireTail` whose notification wakes a thread: either it is `WAITING` and `wake_ok`
  holds of its queue head, or it is idle, bound to the due thread `p.tm`, which waits in `Recv` (`p.waiter = p.tm`,
  `p.ep ≠ 0`) and `wake_ok` holds of it.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireWt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem ntfn_head_ok (X : S) (n : U64) : obj.Ntfn.head st n X = ok (L.epQ X n).head := by
  unfold obj.Ntfn.head
  simp only [lift, bind_ok, L.read_eq]
  simp [LawfulStore.epQ, epHeadA, ntfn_head_eq]

/-- **An accepted `wake_ok`** (module docstring). -/
theorem wake_ok_true {X : S} {cpu ct w n : U64} (h : localtimer.wake_ok st X cpu ct w n = ok true) :
    w ≠ ct ∧ localtimer.may_run_here st X cpu w = ok true ∧
      L.mem X (domA w) = L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN) ∧
      (L.mem X (inqA w) &&& sched.Q_QUEUED) = 0#u64 ∧
      (L.mem X (scA w) = 0#u64 → L.mem X (ntfnScA n) = 0#u64) ∧
      localtimer.top_ok st X cpu = ok true := by
  unfold localtimer.wake_ok at h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  have hb := PathObl.post_of_ok (tcb_ne.blk w ct) eb
  by_cases b0 : b = true
  swap
  · rw [if_neg b0] at h; exact absurd (ok_inj_ff h) Bool.false_ne_true
  rw [if_pos b0] at h
  obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
  by_cases b1t : b1 = true
  swap
  · rw [if_neg b1t] at h; exact absurd (ok_inj_ff h) Bool.false_ne_true
  rw [if_pos b1t] at h
  subst b1t
  rw [eq_of_spec_fd (obj.Tcb.domain.spec (L := L) X w), cur_domain_ok] at h
  simp only [bind_ok] at h
  by_cases hd : L.mem X (domA w) = L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN)
  swap
  · rw [if_neg hd] at h; exact absurd (ok_inj_ff h) Bool.false_ne_true
  rw [if_pos hd, eq_of_spec_fd (sched.queued.spec (L := L) X w)] at h
  simp only [bind_ok] at h
  by_cases hq : (L.mem X (inqA w) &&& sched.Q_QUEUED) ≠ 0#u64
  · rw [if_pos (decide_eq_true hq)] at h; exact absurd (ok_inj_ff h) Bool.false_ne_true
  rw [if_neg (fun e => hq (of_decide_eq_true e)), tcb_sc_ok] at h
  simp only [bind_ok] at h
  refine ⟨hb.1 b0, eb1, hd, not_not.mp hq, ?_⟩
  by_cases h0 : L.mem X (scA w) = 0#u64
  · rw [if_pos h0, eq_of_spec_fd (obj.Ntfn.sc.val (L := L) X n)] at h
    simp only [bind_ok] at h
    by_cases hn : L.mem X (ntfnScA n) = 0#u64
    · rw [if_neg (by simp [hn])] at h
      exact ⟨fun _ => hn, h⟩
    · rw [if_pos (bne_iff_ne.mpr hn)] at h; exact absurd (ok_inj_ff h) Bool.false_ne_true
  · rw [if_neg h0] at h
    exact ⟨fun e => absurd e h0, h⟩

/-- **An accepted `fireTail` whose notification wakes a thread** (module docstring). -/
theorem fireTail_wake {X : S} {cpu : U64} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan}
    (h : fireTail st X cpu ct p = ok true) (hn : p.ntfn ≠ 0#u64)
    (hw : L.epState X p.ntfn = obj.NTFN_WAITING ∨
      (L.epState X p.ntfn = obj.NTFN_IDLE ∧ L.mem X (ntfnBtA p.ntfn) ≠ 0#u64 ∧
        L.mem X (stA (L.mem X (ntfnBtA p.ntfn))) = sched.TS_BLOCKED_ON_RECV)) :
    (L.epState X p.ntfn = obj.NTFN_WAITING ∧
      localtimer.wake_ok st X cpu ct (L.epQ X p.ntfn).head p.ntfn = ok true) ∨
    (L.epState X p.ntfn = obj.NTFN_IDLE ∧ L.mem X (ntfnBtA p.ntfn) = p.tm ∧
      L.mem X (stA p.tm) = sched.TS_BLOCKED_ON_RECV ∧ p.waiter = p.tm ∧ p.ep ≠ 0#u64 ∧
      localtimer.wake_ok st X cpu ct p.tm p.ntfn = ok true) := by
  unfold fireTail at h
  rw [if_neg hn, eq_of_spec_fd (obj.Ntfn.state.spec (L := L) X _)] at h
  simp only [bind_ok] at h
  rcases hw with hw | ⟨hi, hb, hr⟩
  · left
    have h1 : obj.NTFN_WAITING ≠ obj.NTFN_ACTIVE := by unfold obj.NTFN_WAITING obj.NTFN_ACTIVE; decide
    rw [hw, if_neg h1, if_neg ntfn_waiting_ne_idle, if_pos rfl, ntfn_head_ok] at h
    simp only [bind_ok] at h
    exact ⟨hw, h⟩
  · right
    have h1 : obj.NTFN_IDLE ≠ obj.NTFN_ACTIVE := by unfold obj.NTFN_IDLE obj.NTFN_ACTIVE; decide
    rw [hi, if_neg h1, if_pos rfl, eq_of_spec_fd (obj.Ntfn.bound_tcb.val (L := L) X _)] at h
    simp only [bind_ok] at h
    rw [if_neg hb] at h
    by_cases he : (L.mem X (ntfnBtA p.ntfn) != p.tm) = true
    · rw [if_pos he] at h; exact absurd (ok_inj_ff h) Bool.false_ne_true
    rw [if_neg he] at h
    have e : L.mem X (ntfnBtA p.ntfn) = p.tm := by
      by_contra hne; exact he (bne_iff_ne.mpr hne)
    rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) X _), ← e, hr] at h
    simp only [bind_ok] at h
    rw [if_neg recv_ne_vm, if_pos trivial, e] at h
    by_cases hwt : p.waiter = p.tm
    swap
    · rw [if_neg hwt] at h; exact absurd (ok_inj_ff h) Bool.false_ne_true
    rw [if_pos hwt] at h
    by_cases hep : (p.ep != 0#u64) = true
    swap
    · rw [if_neg hep] at h; exact absurd (ok_inj_ff h) Bool.false_ne_true
    rw [if_pos hep] at h
    exact ⟨hi, e, by rw [← e]; exact hr, hwt, bne_iff_ne.mp hep, h⟩

end

end Fl4Proofs.P2
