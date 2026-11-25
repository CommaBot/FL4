/-
# P2 (p2lf): the waking fire case, on `st`: what the wake writes and the action it leaves

* `donate_nd_st`: `maybe_donate_sched_context` that donates nothing (the thread has an SC, or the notification
  none) returns its state.
* `wakeTail_st`: the run of `wakeTail` on `st` for a thread `w` that is not the current one and may run here, with
  the action `RESUME_CURRENT`: it returns the `Arch` unchanged, writes only `w`'s `STATE` and badge register, this
  core's `SCHED_ACTION` (`WkD`), `w`'s SC ring and this core's `REPROGRAM` (`refill_unblock_check`), and leaves the
  action `RESUME_CURRENT` or `w`.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireWk
import Fl4Proofs.P2.FootTimerFireOwn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (bind_guard_congr NodeSt ScAcc)

section st
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `maybe_donate_sched_context` that donates nothing, on `st`. -/
theorem donate_nd_st {A : Type} (ar : machine.Arch A) (X : S) (a : A) (t n : U64)
    (hnd : L.mem X (scA t) = 0#u64 → L.mem X (ntfnScA n) = 0#u64) :
    notification.maybe_donate_sched_context st ar X a t n = ok (X, a) := by
  unfold notification.maybe_donate_sched_context
  rw [tcb_sc_ok]
  simp only [bind_ok]
  by_cases h0 : L.mem X (scA t) = 0#u64
  · rw [if_pos h0, eq_of_spec_fd (obj.Ntfn.sc.val (L := L) X n), hnd h0]
    simp only [bind_ok, eq_of_spec_fd (obj.Sc.is_null.spec 0#u64), decide_true, ↓reduceIte]
  · rw [if_neg h0]

set_option maxHeartbeats 4000000 in
/-- **`wakeTail` on `st`** (module docstring). -/
theorem wakeTail_st {A : Type} (ar : machine.Arch A) (X : S) (a : A) (w n badge : U64) {sb : Nat}
    {R' W' : U64 → Prop} {X' : S} {a' : A}
    (hcur : w ≠ L.curW X)
    (aS : Aligned (stA w)) (aR : Aligned (regA w layout.reg.BADGE))
    (aA : Aligned (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION))
    (nA1 : L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION ≠ stA w)
    (nA2 : L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION ≠ regA w layout.reg.BADGE)
    (aC : Aligned (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD))
    (nC1 : L.nodeAt X (L.cpu X) layout.node.CUR_THREAD ≠ stA w)
    (hAo : Outside (L.nodeA X layout.node.SCHED_ACTION) (L.mem X (scA w)) sb)
    (nAR : L.nodeA X layout.node.SCHED_ACTION ≠ L.nodeA X layout.node.REPROGRAM)
    (eSc : ∀ Y, WritesIn st X Y (WkD st X w) → L.mem Y (scA w) = L.mem X (scA w))
    (hac : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (hY : ∀ Y, WritesIn st X Y (WkD st X w) → WkPre st R' W' Y w n sb)
    (h : wakeTail st ar X a w n badge = ok (X', a')) :
    a' = a ∧
      WritesIn st X X' (fun b => WkD st X w b ∨ InRing (L.mem X (scA w)) sb b ∨
        b = L.nodeA X layout.node.REPROGRAM) ∧
      (L.actionW X' = sched.ACTION_RESUME_CURRENT ∨ L.actionW X' = w) := by
  have wi2 : WritesIn st X (L.wr X (stA w) sched.TS_RUNNING) (WkD st X w) :=
    ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hb' => mem_wr_ne' aS hb (fun e => hb' (Or.inl e.symm))⟩
  unfold wakeTail at h
  rw [sts_ok X w _ hcur aS aC nC1] at h
  simp only [bind_ok] at h
  rw [PathObl.set_reg_ok'] at h
  simp only [bind_ok] at h
  have wi3 : WritesIn st X (L.wr (L.wr X (stA w) sched.TS_RUNNING) (regA w layout.reg.BADGE) badge)
      (WkD st X w) :=
    ⟨by rw [L.ksb_wr, L.ksb_wr], by rw [L.cpu_wr, L.cpu_wr], fun b hb hb' => by
      rw [mem_wr_ne' aR hb (fun e => hb' (Or.inr (Or.inl e.symm)))]
      exact wi2.2.2 b hb hb'⟩
  have P3 := hY _ wi3
  rw [donate_nd_st ar _ a w n P3.nd] at h
  simp only [bind_ok, Aeneas.Std.uncurry_apply_pair] at h
  have hac3 : L.actionW (L.wr (L.wr X (stA w) sched.TS_RUNNING) (regA w layout.reg.BADGE) badge) =
      sched.ACTION_RESUME_CURRENT := by
    unfold LawfulStore.actionW
    rw [nodeAt_wr, nodeAt_wr, L.cpu_wr, L.cpu_wr, mem_wr_ne' aR aA (Ne.symm nA2), mem_wr_ne' aS aA (Ne.symm nA1)]
    exact hac
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  obtain ⟨X5, h5, h⟩ := bind_eq_ok h
  obtain ⟨X6, h6, h⟩ := bind_eq_ok h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  -- `possible_switch_to`: nothing, or the action set to `w`
  have wi5 : WritesIn st X X5 (WkD st X w) ∧
      (L.actionW X5 = sched.ACTION_RESUME_CURRENT ∨ L.actionW X5 = w) := by
    by_cases hb : b = true
    · rw [if_pos hb] at h5
      rcases possible_switch_to_here_st _ w P3.dom P3.aff hac3 with e | e
      · rw [e] at h5; rw [← ok_inj_ff h5]; exact ⟨wi3, Or.inl hac3⟩
      · rw [e] at h5
        rw [← ok_inj_ff h5]
        refine ⟨⟨by rw [L.ksb_wr]; exact wi3.1, by rw [L.cpu_wr]; exact wi3.2.1, fun c hc hc' => ?_⟩, Or.inr ?_⟩
        · rw [nodeAt_wr, nodeAt_wr, L.cpu_wr, L.cpu_wr, mem_wr_ne' aA hc (fun e => hc' (Or.inr (Or.inr e.symm)))]
          exact wi3.2.2 c hc hc'
        · unfold LawfulStore.actionW
          simp only [nodeAt_wr, LawfulStore.cpu_wr]
          exact L.mem_wr_same aA
    · rw [if_neg hb] at h5; rw [← ok_inj_ff h5]; exact ⟨wi3, Or.inl hac3⟩
  obtain ⟨w5, ac5⟩ := wi5
  have P5 := hY X5 w5
  have nA5 : ∀ o, L.nodeA X5 o = L.nodeA X o := fun o => by
    show L.nodeAt X5 (L.cpu X5) o = L.nodeAt X (L.cpu X) o
    rw [w5.2.1, nodeAt_of_ksb w5.1]
  have sc5 : L.mem X5 (scA w) = L.mem X (scA w) := eSc X5 w5
  -- `unblock_sporadic`: nothing, or `refill_unblock_check` of `w`'s SC
  have w56 : WritesIn st X5 X6 (fun b => InRing (L.mem X (scA w)) sb b ∨ b = L.nodeA X layout.node.REPROGRAM) := by
    unfold notification.unblock_sporadic at h6
    rw [tcb_sc_ok] at h6
    simp only [bind_ok] at h6
    obtain ⟨b1, eb1, h6⟩ := bind_eq_ok h6
    by_cases hb1 : b1 = true
    · rw [if_pos hb1] at h6
      have h0 : L.mem X5 (scA w) ≠ 0#u64 := (sc_sporadic_true (by rw [← hb1]; exact eb1)).1
      obtain ⟨c, -, h6⟩ := bind_eq_ok h6
      obtain ⟨b2, -, h6⟩ := bind_eq_ok h6
      by_cases hb2 : b2 = true
      · rw [if_pos hb2] at h6
        have := sporadic.unblock_check.fr (st := st) (P5.wf h0) (P5.rep h0)
        rw [h6, WP.spec_ok] at this
        rw [sc5, nA5] at this
        exact this
      · rw [if_neg hb2] at h6; rw [← ok_inj_ff h6]; exact WritesIn.refl _ _
    · rw [if_neg hb1] at h6; rw [← ok_inj_ff h6]; exact WritesIn.refl _ _
  refine ⟨rfl, (w5.trans w56).mono fun b hb => ?_, ?_⟩
  · rcases hb with hb | hb | hb
    · exact Or.inl hb
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hb)
  · have : L.actionW X6 = L.actionW X5 := by
      unfold LawfulStore.actionW
      rw [w56.2.1, nodeAt_of_ksb w56.1]
      refine w56.mem_eq (by rw [w5.2.1, nodeAt_of_ksb w5.1]; exact aA) ?_
      rintro (hr | e)
      · have hO := hAo
        unfold InRing at hr
        unfold Outside at hO
        have e' : L.nodeAt X5 (L.cpu X5) layout.node.SCHED_ACTION = L.nodeA X layout.node.SCHED_ACTION := nA5 _
        rw [e'] at hr
        omega
      · have e' : L.nodeAt X5 (L.cpu X5) layout.node.SCHED_ACTION = L.nodeA X layout.node.SCHED_ACTION := nA5 _
        rw [e'] at e
        exact nAR e
    rw [this]; exact ac5

end st

end Fl4Proofs.P2
