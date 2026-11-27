/-
# P2 (line p3mc, gen 34): the spec-only `JAtZ` fields at the boot state `σB`

The fields of P3's `JAtZ` that read the spec state only (and the ghost sets `T = {tiB}`, `C = {sciB}`), at `σB`:
`inv` (`Sched.Inv`), `cur` (`CurInv`), `own` (`CurOwnW`), `off` (`OffOK`), `act` (`ActIdle`), `bsa`
(`BlockedScActive`, P3's `boot_bsa` ported: `boot_bsa_B`), `sv` (`SchedValid`), `isorted` (`IpcSorted`), `slink`
(`ScLinkHyp`), `curRun` (`CurRunM`); each `σB_<field>`.

`σB`'s objects (`kheapB_tcb`, `kheapB_sc`, `kheapB_noEp` / `noNtfn` / `noReply`): the idle TCB `idleTcbB` (idle
state, bound to the idle SC, no fault / notification / yield) and the idle SC `idleScB` (bound to the idle thread,
refills `(0, MAX_PERIOD)`, `(MAX_PERIOD, 0)`, `REFILL_MAX = MIN_REFILLS = 2`, period 0, not sporadic).
`Inv.rr` needs `MIN_BUDGET ≤ MAX_PERIOD`: P3's `SInvR.minBudget_le_maxPeriod` proves it from `TimeConsts`' axioms
(no new hypothesis).

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootZCheap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Spec Classical

noncomputable section

/-- The idle TCB of `kheapB` (Fl4Spec/Init `initKheap`'s). -/
def idleTcbB : Tcb :=
  { tcbCtable := .nullCap,
    tcbVtable := .nullCap,
    tcbIpcframe := .nullCap,
    tcbFaultHandler := .nullCap,
    tcbTimeoutHandler := .nullCap,
    tcbEpt := .nullCap,
    tcbState := .idleThreadState,
    tcbIpcBuffer := 0,
    tcbFault := none,
    tcbBoundNotification := none,
    tcbMcpriority := 0,
    tcbSchedContext := some idleScPtr,
    tcbYieldTo := none,
    tcbPriority := 0,
    tcbDomain := defaultDomain,
    tcbFlags := ∅,
    tcbArch := initArchTcb }

/-- The idle SC of `kheapB`. -/
def idleScB : SchedContext :=
  { defaultSchedContext with
    scTcb := some idleThreadPtr,
    scRefills := [{ rTime := 0, rAmount := MAX_PERIOD }, { rTime := MAX_PERIOD, rAmount := 0 }],
    scBudget := MAX_PERIOD,
    scRefillMax := MIN_REFILLS }

theorem kheapB_ti : kheapB idleThreadPtr = some (.tcb idleTcbB) := by
  unfold kheapB
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_self]
  try rfl

theorem kheapB_sci : kheapB idleScPtr = some (.schedContext idleScB 0) := SInvV.initKheap_idleSc_B

theorem kheapB_tcb {o : ObjRef} {x : Tcb} (h : kheapB o = some (.tcb x)) : o = idleThreadPtr ∧ x = idleTcbB := by
  rcases kheapB_cases h with ⟨e, -⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩
  · subst e; rw [kheapB_ti] at h; cases h; exact ⟨rfl, rfl⟩
  all_goals cases e

theorem kheapB_sc {o : ObjRef} {y : SchedContext} {n : Nat} (h : kheapB o = some (.schedContext y n)) :
    o = idleScPtr ∧ y = idleScB ∧ n = 0 := by
  rcases kheapB_cases h with ⟨-, _, e⟩ | ⟨e, -⟩ | ⟨-, _, e⟩ | ⟨-, e⟩
  · cases e
  · subst e; rw [kheapB_sci] at h; cases h; exact ⟨rfl, rfl, rfl⟩
  all_goals cases e

theorem kheapB_noEp {o : ObjRef} {x : Endpoint} (h : kheapB o = some (.endpoint x)) : False := by
  rcases kheapB_cases h with ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e

theorem kheapB_noNtfn {o : ObjRef} {x : Notification} (h : kheapB o = some (.notification x)) : False := by
  rcases kheapB_cases h with ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e

theorem kheapB_noReply {o : ObjRef} {x : Reply} (h : kheapB o = some (.reply x)) : False := by
  rcases kheapB_cases h with ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e

theorem idleScB_active : scActive idleScB = true := by decide

theorem σB_off : OffOK (σB (Z := Unit)) := fun h => absurd h (by decide)

theorem σB_act : ActIdle (σB (Z := Unit)) :=
  ⟨fun t h => (by cases h), ⟨idleTcbB, kheapB_ti, rfl, rfl, List.not_mem_nil⟩⟩

theorem σB_curRun : CurRunM (σB (Z := Unit)) := Or.inr (Or.inr rfl)

theorem σB_isorted : IpcSorted (σB (Z := Unit)) :=
  ⟨fun _ _ h => (kheapB_noEp h).elim, fun _ _ h => (kheapB_noNtfn h).elim⟩

theorem σB_cur : (σB (Z := Unit)).schedulerAction = .chooseNewThread ∨ CurInv (σB (Z := Unit)) :=
  Or.inr ⟨⟨idleTcbB, kheapB_ti, rfl, ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩⟩,
    ⟨_, _, kheapB_sci⟩, fun h => absurd rfl h, List.not_mem_nil⟩

theorem σB_own (G : MdbGhost) : CurOwnW (ZB G).T (ZB G).C (σB (Z := Unit)) := by
  refine Or.inl ⟨tiB, rfl, idleTcbB, by rw [tiB_bv]; exact kheapB_ti, rfl, ?_, ?_⟩
  · intro x n h
    change kheapB idleScPtr = _ at h
    rw [kheapB_sci] at h; cases h; rw [tiB_bv]; rfl
  · intro h; exact absurd h (by decide)

theorem σB_slink : ScLinkHyp (σB (Z := Unit)) where
  scTcb sc y k f h hf := by
    obtain ⟨-, rfl, -⟩ := kheapB_sc h
    cases hf; exact ⟨_, kheapB_ti⟩
  scNtfn sc y k n h hn := by
    obtain ⟨-, rfl, -⟩ := kheapB_sc h
    cases hn
  tcbNtfn t x n h hn := by
    obtain ⟨-, rfl⟩ := kheapB_tcb h
    cases hn
  scSpor sc y k h hs := by
    obtain ⟨-, rfl, -⟩ := kheapB_sc h
    cases hs

theorem σB_sv : SchedValid (σB (Z := Unit)) where
  epQ e x h := (kheapB_noEp h).elim
  ntfnQ n x h := (kheapB_noNtfn h).elim
  recvQ t x ep ro d h hs := by obtain ⟨-, rfl⟩ := kheapB_tcb h; cases hs
  sendQ t x ep pl h hs := by obtain ⟨-, rfl⟩ := kheapB_tcb h; cases hs
  ntfnW t x n h hs := by obtain ⟨-, rfl⟩ := kheapB_tcb h; cases hs
  recvReply t x ep r d h hs := by obtain ⟨-, rfl⟩ := kheapB_tcb h; cases hs
  onReply t x r h hs := by obtain ⟨-, rfl⟩ := kheapB_tcb h; cases hs
  replyTcb r xr t h := (kheapB_noReply h).elim
  replies sc y k r h hr := by obtain ⟨-, rfl, -⟩ := kheapB_sc h; cases hr
  scTcb := σB_slink.scTcb
  scNtfn := σB_slink.scNtfn
  scYieldFrom sc y k t h ht := by obtain ⟨-, rfl, -⟩ := kheapB_sc h; cases ht
  tcbYieldTo t x p h hp := by obtain ⟨-, rfl⟩ := kheapB_tcb h; cases hp
  tcbNtfn := σB_slink.tcbNtfn
  ntfnTcb n xn t h := (kheapB_noNtfn h).elim
  scSpor := σB_slink.scSpor

theorem σB_inv : Inv (σB (Z := Unit)) where
  rq d p u h := by cases h
  rel u h := by cases h
  sorted := List.Pairwise.nil
  rd u x h hc := by
    obtain ⟨-, rfl⟩ := kheapB_tcb h
    rcases hc with hc | ⟨_, hc⟩ | ⟨_, _, hc, -⟩ | ⟨_, _, _, hc⟩ <;> cases hc
  refills p y n h ha hp := by
    obtain ⟨-, rfl, -⟩ := kheapB_sc h
    exact absurd rfl hp
  back u x p h hp := by
    obtain ⟨rfl, rfl⟩ := kheapB_tcb h
    cases hp
    exact ⟨_, _, kheapB_sci, rfl⟩
  ntfnSc q x p h := (kheapB_noNtfn h).elim
  ne p y n h ha := by
    obtain ⟨-, rfl, -⟩ := kheapB_sc h
    simp [idleScB]
  rr p y n h ha hp := by
    obtain ⟨-, rfl, -⟩ := kheapB_sc h
    refine ⟨by simp [idleScB], ?_, ?_⟩
    · simp only [idleScB, List.map, List.sum_cons, List.sum_nil]
      have := MAX_PERIOD.isLt
      simp; omega
    · exact SInvR.minBudget_le_maxPeriod

theorem σB_bsa : BlockedScActive (σB (Z := Unit)) := SInvR.B8e.boot_bsa_B

end

end Fl4Proofs.P2.BootSt
