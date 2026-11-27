/-
# P2 (line p3mc, gen 39, unit C): the spec-only `JAtZ` fields at the second boot start `σR`

Gen 34's `P2/BootSpecF` (at `σB`) ported to `σR` (P2/BootRSpec: `σB` with the running root thread `tRp` current,
bound to the root SC `scRp`) and the ghosts `ZR` (P2/BootRZ: `T = {tiB, tRw}`, `C = {sciB, scRw}`):
`inv` (`Sched.Inv`), `cur` (`CurInv`, the right disjunct: `tRp` bound to `scRp`, running, `scR` active),
`own` (`CurOwnW`: `tRw ∈ T` owns `scRp`), `off` (`OffOK`), `act` (`ActIdle`), `bsa` (`BlockedScActive`), `sv`
(`SchedValid`), `isorted` (`IpcSorted`), `slink` (`ScLinkHyp`), `curRun` (`CurRunM` via `CurRun`: `tRp` running);
each `σR_<field>`, except `cur`, named **`σR_curInv`** (`σR_cur` is P2/BootRSpec's `curThread = tRp`).

`σR`'s TCBs are the idle TCB `idleTcbB` and the root TCB `tcbR` (`uC_kheapR_tcb`), its SCs the idle SC `idleScB`
and the root SC `scR` (`uC_kheapR_sc`), no endpoint / notification / reply. `Inv.rd` at `tRp` (state `Running`,
not released, `scR` active) asks `scR` released: its head `(0, MAX_PERIOD)` is ready at time 0 and sufficient by
`MIN_BUDGET ≤ MAX_PERIOD` (P3's `SInvR.minBudget_le_maxPeriod`), as is `Inv.rr` for `scR`.

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.BootRZ
import Fl4Proofs.P2.BootSpecF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Spec Classical

noncomputable section

/-! ## `kheapR`'s objects by kind -/

theorem uC_kheapR_ti : kheapR idleThreadPtr = some (.tcb idleTcbB) := by
  rw [kheapR_of_ne tRp_ne_idle.symm (by decide)]; exact kheapB_ti

theorem uC_kheapR_sci : kheapR idleScPtr = some (.schedContext idleScB 0) := by
  rw [kheapR_of_ne (by decide) scRp_ne_idle.symm]; exact kheapB_sci

theorem uC_kheapR_tcb {o : ObjRef} {x : Tcb} (h : kheapR o = some (.tcb x)) :
    (o = idleThreadPtr ∧ x = idleTcbB) ∨ (o = tRp ∧ x = tcbR) := by
  rcases kheapR_cases h with ⟨e, he⟩ | ⟨-, he⟩ | ⟨-, -, he⟩
  · cases he; exact Or.inr ⟨e, rfl⟩
  · cases he
  · exact Or.inl (kheapB_tcb he)

theorem uC_kheapR_sc {o : ObjRef} {y : SchedContext} {n : Nat} (h : kheapR o = some (.schedContext y n)) :
    (o = idleScPtr ∧ y = idleScB ∧ n = 0) ∨ (o = scRp ∧ y = scR ∧ n = 0) := by
  rcases kheapR_cases h with ⟨-, he⟩ | ⟨e, he⟩ | ⟨-, -, he⟩
  · cases he
  · cases he; exact Or.inr ⟨e, rfl, rfl⟩
  · exact Or.inl (kheapB_sc he)

theorem uC_kheapR_noEp {o : ObjRef} {x : Endpoint} (h : kheapR o = some (.endpoint x)) : False := by
  rcases kheapR_cases h with ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, -, he⟩
  · cases he
  · cases he
  · exact kheapB_noEp he

theorem uC_kheapR_noNtfn {o : ObjRef} {x : Notification} (h : kheapR o = some (.notification x)) : False := by
  rcases kheapR_cases h with ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, -, he⟩
  · cases he
  · cases he
  · exact kheapB_noNtfn he

theorem uC_kheapR_noReply {o : ObjRef} {x : Reply} (h : kheapR o = some (.reply x)) : False := by
  rcases kheapR_cases h with ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, -, he⟩
  · cases he
  · cases he
  · exact kheapB_noReply he

theorem uC_scR_active : scActive scR = true := by decide

/-- The root SC is released at `σR` (head `(0, MAX_PERIOD)`, time 0). -/
theorem uC_scR_released : Notif.released (σR (Z := Unit)) scR := by
  refine ⟨?_, ?_⟩
  · show decide ((0 : Time) + 0 ≤ 0) = true
    decide
  · show decide (MIN_BUDGET ≤ refillCapacity 0 { rTime := 0, rAmount := MAX_PERIOD }) = true
    unfold refillCapacity
    rw [if_neg (by rw [BitVec.lt_def]; simp)]
    simpa using SInvR.minBudget_le_maxPeriod

/-! ## The fields -/

theorem σR_off : OffOK (σR (Z := Unit)) := fun h => absurd h (by decide)

theorem σR_act : ActIdle (σR (Z := Unit)) :=
  ⟨fun t h => (by cases h), ⟨idleTcbB, uC_kheapR_ti, rfl, rfl, List.not_mem_nil⟩⟩

theorem σR_curRun : CurRunM (σR (Z := Unit)) := by
  refine Or.inr (Or.inl fun x h => ?_)
  change kheapR tRp = _ at h
  rw [kheapR_tR] at h; cases h; rfl

theorem σR_isorted : IpcSorted (σR (Z := Unit)) :=
  ⟨fun _ _ h => (uC_kheapR_noEp h).elim, fun _ _ h => (uC_kheapR_noNtfn h).elim⟩

/-- `JAtZ.cur` at `σR` (`σR_cur` is taken by P2/BootRSpec's `curThread = tRp`). -/
theorem σR_curInv : (σR (Z := Unit)).schedulerAction = .chooseNewThread ∨ CurInv (σR (Z := Unit)) := by
  refine Or.inr ⟨⟨tcbR, kheapR_tR, rfl, ⟨fun _ h => (by cases h), fun _ _ h => (by cases h),
    fun _ _ _ h => (by cases h)⟩⟩, ⟨_, _, kheapR_scR⟩, fun _ x n h => ?_, List.not_mem_nil⟩
  change kheapR scRp = _ at h
  rw [kheapR_scR] at h; cases h; exact uC_scR_active

theorem σR_own : CurOwnW ZR.T ZR.C (σR (Z := Unit)) := by
  refine Or.inl ⟨tRw, ZR_T.2 (Or.inr rfl), tcbR, by rw [tRw_bv]; exact kheapR_tR, rfl, ?_, ?_⟩
  · intro x n h
    change kheapR scRp = _ at h
    rw [kheapR_scR] at h; cases h; rfl
  · intro h; exact absurd h (by decide)

theorem σR_slink : ScLinkHyp (σR (Z := Unit)) where
  scTcb sc y k f h hf := by
    rcases uC_kheapR_sc h with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
    · cases hf; exact ⟨_, uC_kheapR_ti⟩
    · cases hf; exact ⟨_, kheapR_tR⟩
  scNtfn sc y k n h hn := by
    rcases uC_kheapR_sc h with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> cases hn
  tcbNtfn t x n h hn := by
    rcases uC_kheapR_tcb h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hn
  scSpor sc y k h hs := by
    rcases uC_kheapR_sc h with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> cases hs

theorem σR_sv : SchedValid (σR (Z := Unit)) where
  epQ e x h := (uC_kheapR_noEp h).elim
  ntfnQ n x h := (uC_kheapR_noNtfn h).elim
  recvQ t x ep ro d h hs := by rcases uC_kheapR_tcb h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hs
  sendQ t x ep pl h hs := by rcases uC_kheapR_tcb h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hs
  ntfnW t x n h hs := by rcases uC_kheapR_tcb h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hs
  recvReply t x ep r d h hs := by rcases uC_kheapR_tcb h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hs
  onReply t x r h hs := by rcases uC_kheapR_tcb h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hs
  replyTcb r xr t h := (uC_kheapR_noReply h).elim
  replies sc y k r h hr := by rcases uC_kheapR_sc h with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> cases hr
  scTcb := σR_slink.scTcb
  scNtfn := σR_slink.scNtfn
  scYieldFrom sc y k t h ht := by rcases uC_kheapR_sc h with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> cases ht
  tcbYieldTo t x p h hp := by rcases uC_kheapR_tcb h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hp
  tcbNtfn := σR_slink.tcbNtfn
  ntfnTcb n xn t h := (uC_kheapR_noNtfn h).elim
  scSpor := σR_slink.scSpor

theorem σR_inv : Inv (σR (Z := Unit)) where
  rq d p u h := by cases h
  rel u h := by cases h
  sorted := List.Pairwise.nil
  rd u x h hc := by
    rcases uC_kheapR_tcb h with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hc with hc | ⟨_, hc⟩ | ⟨_, _, hc, -⟩ | ⟨_, _, _, hc⟩ <;> cases hc
    · intro x' scp y n hk hsc hky _ _
      change kheapR tRp = _ at hk
      rw [kheapR_tR] at hk; cases hk
      obtain rfl : scp = scRp := (Option.some.inj hsc).symm
      change kheapR scRp = _ at hky
      rw [kheapR_scR] at hky; cases hky
      exact uC_scR_released
  refills p y n h ha hp := by
    rcases uC_kheapR_sc h with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> exact absurd rfl hp
  back u x p h hp := by
    rcases uC_kheapR_tcb h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hp; exact ⟨_, _, uC_kheapR_sci, rfl⟩
    · cases hp; exact ⟨_, _, kheapR_scR, rfl⟩
  ntfnSc q x p h := (uC_kheapR_noNtfn h).elim
  ne p y n h ha := by
    rcases uC_kheapR_sc h with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
    · simp [idleScB]
    · simp [scR]
  rr p y n h ha hp := by
    rcases uC_kheapR_sc h with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
    · refine ⟨by simp [idleScB], ?_, ?_⟩
      · simp only [idleScB, List.map, List.sum_cons, List.sum_nil]
        have := MAX_PERIOD.isLt
        simp; omega
      · exact SInvR.minBudget_le_maxPeriod
    · refine ⟨by simp [scR], ?_, ?_⟩
      · simp only [scR, List.map, List.sum_cons, List.sum_nil]
        have := MAX_PERIOD.isLt
        simp; omega
      · exact SInvR.minBudget_le_maxPeriod

theorem σR_bsa : BlockedScActive (σR (Z := Unit)) := by
  refine ⟨fun p y n t x hp hyt hx hq => ?_, fun p y n hp hr => ?_⟩
  · rcases uC_kheapR_tcb hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact absurd hq (by decide)
  · rcases uC_kheapR_sc hp with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> exact absurd rfl hr

end

end Fl4Proofs.P2.BootSt
