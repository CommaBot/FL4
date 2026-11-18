/-
P3 (DESIGN.md §9), IPC: **the scheduler invariants across an endpoint's
`cancel_all_ipc`** (spec side only), toward `JAtZ` after a final endpoint
cap's finalisation (`JAtZ.finEpJ`, XTopJointFinEp).

* `EFr e P`: the spec's frame of endpoint `e`'s finalisation (`EChg`
  objectwise, `Sk` for the other fields): a TCB's state kept, or a thread
  blocked on `e` (to send or to receive) made `Restart` or `Inactive`
  (`TChgE`); an SC's refills (not the current SC's); `e`'s queue (shorter,
  `e` not idle before); a reply naming a thread `t` with `P t` (the caller's:
  `t` blocked receiving at the start) to one naming nothing. Notifications,
  CNodes and the other kinds are kept.
* `rtinf_inv`: `restart_thread_if_no_fault` of a stopped thread (blocked or
  inactive) whose SC is active and released when bound: `Inv` kept (the
  restart as `inv_ntfn_iter`'s, `Inv.deactivate` for a faulted thread), the
  thread and its SC's refills changed only.
* `inv_ep_iter`: one thread of the loop (the dequeue, `Inv.updEp`; the reply
  unlink, `Inv.updReply`, `Inv.deactivate`; `rtinf_inv`), in `EFr`, with
  `SpecFinOutEp`'s `ep_iter` for the queued threads' facts (the step
  deterministic). `ep_loop_inv`, `inv_cancelAllIpc`: the loop and the
  reschedule.
* What the frame keeps: the per-kind lemmas and the scheduler facts read by
  `JRest` (`szKeep`, `ykeep`, `mcpKeep`, `bufKeep`, `nsc`, `isorted`, `own`,
  `off`, `idleOK`, `bsa`, `kback`, `ksz`, `ksub`, `callKeep`).
-/
import Fl4Proofs.P3.IpcSignalBoundFr
import Fl4Proofs.P3.IpcCancelAllIpc
import Fl4Proofs.P3.ScCallUnlink
import Fl4Proofs.P3.ScCallOps
import Fl4Proofs.P3.ScInvE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section Spec
open Fl4Spec Classical

/-! ### The frame -/

/-- **A TCB's state by endpoint `e`'s finalisation**: kept, or a thread
blocked on `e` restarted or made inactive. -/
def TChgE (e : ObjRef) (x : Tcb) (st : ThreadState) : Prop :=
  st = x.tcbState ∨ (epBlocked x.tcbState = some e ∧ (st = .restart ∨ st = .inactive))

theorem TChgE.trans {e : ObjRef} {x : Tcb} {st1 st2 : ThreadState} (h1 : TChgE e x st1)
    (h2 : TChgE e { x with tcbState := st1 } st2) : TChgE e x st2 := by
  simp only [TChgE] at h2
  rcases h2 with e2 | ⟨hb, hs⟩
  · rw [e2]; exact h1
  · rcases h1 with e1 | ⟨-, h | h⟩
    · exact Or.inr ⟨by rw [← e1]; exact hb, hs⟩
    · rw [h] at hb; cases hb
    · rw [h] at hb; cases hb

theorem TChgE.st {e : ObjRef} {x : Tcb} {st : ThreadState} (h : TChgE e x st) (hn : epBlocked x.tcbState ≠ some e) :
    st = x.tcbState := by
  rcases h with h | ⟨hb, -⟩
  · exact h
  · exact absurd hb hn

theorem TChgE.ipcQ {e : ObjRef} {x : Tcb} {st : ThreadState} (h : TChgE e x st)
    (hq : ipcQueuedThreadState st = true) : ipcQueuedThreadState x.tcbState = true := by
  rcases h with h | ⟨-, h | h⟩
  · rw [← h]; exact hq
  · rw [h] at hq; cases hq
  · rw [h] at hq; cases hq

theorem epBlocked_some {ts : ThreadState} {e : ObjRef} (h : epBlocked ts = some e) :
    (∃ d, ts = .blockedOnSend e d) ∨ (∃ ro d, ts = .blockedOnReceive e ro d) := by
  cases ts <;> simp [epBlocked] at h
  all_goals first | (subst h; exact Or.inr ⟨_, _, rfl⟩) | (subst h; exact Or.inl ⟨_, rfl⟩)

theorem epBlocked_run {ts : ThreadState} {e : ObjRef} (h : epBlocked ts = some e) : runnable ts = false := by
  rcases epBlocked_some h with ⟨d, rfl⟩ | ⟨ro, d, rfl⟩ <;> rfl

theorem epBlocked_ipcQ {ts : ThreadState} {e : ObjRef} (h : epBlocked ts = some e) :
    ipcQueuedThreadState ts = true := by
  rcases epBlocked_some h with ⟨d, rfl⟩ | ⟨ro, d, rfl⟩ <;> rfl

theorem epBlocked_inClass {ts : ThreadState} {e : ObjRef} (h : epBlocked ts = some e) : inClass ts := by
  rcases epBlocked_some h with ⟨d, rfl⟩ | ⟨ro, d, rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl⟩))

theorem TChgE.run {e : ObjRef} {x : Tcb} {st : ThreadState} (h : TChgE e x st) (hr : runnable x.tcbState = true) :
    st = x.tcbState := by
  rcases h with h | ⟨hb, -⟩
  · exact h
  · rw [epBlocked_run hb] at hr; cases hr

/-- **One object's change by endpoint `e`'s finalisation** (module docstring;
`cur` the current SC). -/
def EChg (e : ObjRef) (P : ObjRef → Prop) (cur p : ObjRef) (o o' : KernelObject) : Prop :=
  (∃ x st, o = .tcb x ∧ o' = .tcb { x with tcbState := st } ∧ TChgE e x st) ∨
  (∃ y n rf, o = .schedContext y n ∧ o' = .schedContext { y with scRefills := rf } n ∧
    (p = cur → rf = y.scRefills)) ∨
  (∃ x y, o = .endpoint x ∧ o' = .endpoint y ∧ p = e ∧ x ≠ .idleEP ∧ y.epQueue.Sublist x.epQueue) ∨
  (∃ x t, o = .reply x ∧ o' = .reply { x with replyTcb := none } ∧ x.replyTcb = some t ∧ P t)

theorem EChg.trans {e : ObjRef} {P : ObjRef → Prop} {cur p : ObjRef} {o1 o2 o3 : KernelObject}
    (h1 : EChg e P cur p o1 o2) (h2 : EChg e P cur p o2 o3) : EChg e P cur p o1 o3 := by
  rcases h1 with ⟨x, st, rfl, rfl, hc⟩ | ⟨y, n, rf, rfl, rfl, hr⟩ | ⟨x, y, rfl, rfl, hp, hx, hs⟩ |
    ⟨x, t, rfl, rfl, hx, hP⟩
  · rcases h2 with ⟨x2, st2, e2, rfl, hc2⟩ | ⟨_, _, _, e2, -⟩ | ⟨_, _, e2, -⟩ | ⟨_, _, e2, -⟩ <;> cases e2
    exact Or.inl ⟨x, st2, rfl, rfl, hc.trans hc2⟩
  · rcases h2 with ⟨_, _, e2, -⟩ | ⟨y2, n2, rf2, e2, rfl, hr2⟩ | ⟨_, _, e2, -⟩ | ⟨_, _, e2, -⟩ <;> cases e2
    exact Or.inr (Or.inl ⟨y, n, rf2, rfl, rfl, fun h => (hr2 h).trans (hr h)⟩)
  · rcases h2 with ⟨_, _, e2, -⟩ | ⟨_, _, _, e2, -⟩ | ⟨y2, z, e2, rfl, -, -, hs2⟩ | ⟨_, _, e2, -⟩ <;> cases e2
    exact Or.inr (Or.inr (Or.inl ⟨x, z, rfl, rfl, hp, hx, hs2.trans hs⟩))
  · rcases h2 with ⟨_, _, e2, -⟩ | ⟨_, _, _, e2, -⟩ | ⟨_, _, e2, -⟩ | ⟨x2, t2, e2, rfl, hx2, -⟩ <;> cases e2
    exact absurd hx2 (by simp)

/-- **The spec's frame of endpoint `e`'s finalisation** (`EChg`). -/
structure EFr (e : ObjRef) (P : ObjRef → Prop) (σ σ' : State Unit) : Prop where
  sk : Sk σ σ'
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ o o', σ.kheap p = some o ∧ σ'.kheap p = some o' ∧ EChg e P σ.curSc p o o'

theorem EFr.refl (e : ObjRef) (P : ObjRef → Prop) (σ : State Unit) : EFr e P σ σ :=
  ⟨Sk.refl σ, fun _ => Or.inl rfl⟩

theorem EFr.trans {e : ObjRef} {P : ObjRef → Prop} {σ1 σ2 σ3 : State Unit} (h1 : EFr e P σ1 σ2)
    (h2 : EFr e P σ2 σ3) : EFr e P σ1 σ3 := by
  refine ⟨h1.sk.trans h2.sk, fun p => ?_⟩
  have hc2 : σ2.curSc = σ1.curSc := h1.sk.csc
  rcases h2.kh p with e2 | ⟨o2, o3, k2, k3, c2⟩
  · rw [e2]; exact h1.kh p
  · rw [hc2] at c2
    rcases h1.kh p with e1 | ⟨o1, o2', k1, k2', c1⟩
    · exact Or.inr ⟨o2, o3, by rw [← e1]; exact k2, k3, c2⟩
    · obtain rfl := Option.some.inj (k2'.symm.trans k2)
      exact Or.inr ⟨o1, o3, k1, k3, c1.trans c2⟩

theorem QOnly.efr {e : ObjRef} {P : ObjRef → Prop} {σ σ' : State Unit} (h : QOnly σ σ') : EFr e P σ σ' := by
  obtain ⟨rq, act, rfl⟩ := h
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => Or.inl rfl⟩

/-! ### The scheduler invariant across one thread -/

/-- **Writing an endpoint keeps `Inv`.** -/
theorem Inv.updEp {σ : State Unit} (h : Inv σ) {p : ObjRef} {x y : Endpoint} (hk : σ.kheap p = some (.endpoint x)) :
    Inv (updK σ p (.endpoint y)) := by
  refine h.stepE (EpStep.ep hk) (fun u x' y' h1 h2 _ hr => ?_) (fun u x' y' h1 h2 hc => ?_)
  · have hup : u ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    have h2' : σ.kheap u = some (.tcb y') := by simpa [updK, hup] using h2
    rw [h1] at h2'; cases h2'; exact hr
  · have hup : u ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    have h2' : σ.kheap u = some (.tcb y') := by simpa [updK, hup] using h2
    exact h.rd u y' h2' hc

set_option maxHeartbeats 8000000 in
/-- **`restart_thread_if_no_fault` of a stopped thread** (module docstring). -/
theorem rtinf_inv {σ σ5 : State Unit} {t : ObjRef} {x : Tcb} (hI : Inv σ) (hkt : σ.kheap t = some (.tcb x))
    (hnr : runnable x.tcbState = false) (hrib : RelIfBound σ t)
    (hsa : ∀ p y k, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y k) → scActive y = true)
    (hm : ((), σ5) ∈ (restartThreadIfNoFault (Z := Unit) t σ).1) :
    Inv σ5 ∧ Sk σ σ5 ∧
      (∃ st5, (st5 = .restart ∨ st5 = .inactive) ∧ σ5.kheap t = some (.tcb { x with tcbState := st5 })) ∧
      (∀ p, p ≠ t → x.tcbSchedContext ≠ some p → σ5.kheap p = σ.kheap p) ∧
      (∀ c y k, x.tcbSchedContext = some c → σ.kheap c = some (.schedContext y k) →
        ∃ rf, σ5.kheap c = some (.schedContext { y with scRefills := rf } k) ∧ (c = σ.curSc → rf = y.scRefills)) := by
  have htrel : t ∉ σ.releaseQueue := fun hm' => by
    obtain ⟨x', -, -, -, h1, -, h3, -⟩ := hI.rel t hm'
    rw [hkt] at h1; cases h1; rw [hnr] at h3; cases h3
  unfold restartThreadIfNoFault at hm
  rw [nd_bind_one (threadGet_eq _ hkt)] at hm
  by_cases hf : x.tcbFault = none
  · replace hm : ((), σ5) ∈ ((setThreadState (Z := Unit) t .restart >>= fun _ => (do
        let scOpt ← getTcbObjRef Tcb.tcbSchedContext t
        ifSporadicCurScAssertRefillUnblockCheck scOpt
        possibleSwitchTo t)) σ).1 := by
      beta_reduce at hm; rw [if_pos hf] at hm; exact hm
    -- the restart
    set x' : Tcb := { x with tcbState := .restart } with hx'
    set σ2' := updK σ t (.tcb x') with hσ2'
    have hkp2 : ∀ q, q ≠ t → σ2'.kheap q = σ.kheap q := fun q hq => by simp [hσ2', updK, hq]
    have hkt2' : σ2'.kheap t = some (.tcb x') := by simp [hσ2', updK]
    have hI2' : Inv σ2' := by
      refine hI.step (NtfnStep.tcb hkt .restart x.tcbArch) (fun u x0 y h1 h2 _ hr => ?_) (fun u x0 y h1 h2 hc => ?_)
      · by_cases e : u = t
        · subst e; rw [hkt] at h1; cases h1; rw [hnr] at hr; cases hr
        · have h2' : σ.kheap u = some (.tcb y) := by simpa [hσ2', updK, e] using h2
          rw [h1] at h2'; cases h2'; exact hr
      · by_cases e : u = t
        · subst e; exact hrib
        · have h2' : σ.kheap u = some (.tcb y) := by simpa [hσ2', updK, e] using h2
          exact hI.rd u y h2' hc
    have hst := setThreadState_eq' hkt .restart
    set σ2 := stsAct σ2' t with hσ2
    obtain ⟨hk2, ht2, hr2, ha2⟩ := stsAct_heap σ2' t
    have hI2 : Inv σ2 := hI2'.qchange (qchange_stsAct σ2' t)
    have hrel2 : σ2.releaseQueue = σ.releaseQueue := by rw [hσ2, hr2]; rfl
    have hkt2 : σ2.kheap t = some (.tcb x') := by rw [hk2]; exact hkt2'
    have hkp2b : ∀ q, q ≠ t → σ2.kheap q = σ.kheap q := fun q h1 => by rw [hk2, hkp2 q h1]
    have hS2 : Sk σ σ2 := (show Sk σ σ2' from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).trans
      (Sk.stsAct σ2' t)
    rw [nd_bind_one hst,
      nd_bind_one (show getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t σ2 = _ from threadGet_eq _ hkt2)] at hm
    obtain ⟨z3, hz3, hm⟩ := hm
    obtain ⟨⟨⟩, σ3⟩ := z3
    -- the sporadic check
    have hu : ((), σ3) ∈ (specUnblock t σ2).1 := by
      rw [← Ipc.specSporadicAssert_eq]; unfold Endp.specSporadicAssert
      rw [nd_bind_one (show getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t σ2 = _ from threadGet_eq _ hkt2)]
      exact hz3
    have hsa2 : ∀ p y k, x'.tcbSchedContext = some p → σ2.kheap p = some (.schedContext y k) → scActive y = true := by
      intro p y k hp hky
      have hpt : p ≠ t := by rintro rfl; rw [hkt2] at hky; cases hky
      rw [hkp2b p hpt] at hky
      exact hsa p y k hp hky
    have hI3 : Inv σ3 := hI2.unblockTail hkt2
      (fun p y k _ _ hm' => absurd (hrel2 ▸ hm') htrel)
      (fun p y k hp hky _ => hsa2 p y k hp hky) hu
    have hK3 : MaxK.SCK σ2 σ3 := by
      have e : specUnblock t = (getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>=
          ifSporadicCurScTestRefillUnblockCheck (Z := Unit)) := rfl
      exact MaxK.mk_unblock t σ2 ((), σ3) (by rw [← e]; exact hu)
    have hdet3 : ∀ y, y ∈ (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) x'.tcbSchedContext σ2).1 →
        y = ((), σ3) :=
      fun y hy => (Det.det_ifCondRefillUnblockCheck _ _ _).det σ2 y ((), σ3) hy hz3
    have hshape : σ3 = σ2 ∨ ∃ c y z k, x.tcbSchedContext = some c ∧ σ2.kheap c = some (.schedContext y k) ∧
        σ3 = updSc { σ2 with reprogramTimer := true } c z k ∧ z = { y with scRefills := z.scRefills } ∧
        c ≠ σ2.curSc := by
      cases hxc : x.tcbSchedContext with
      | none =>
        left
        have : ((), σ2) ∈ (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) x'.tcbSchedContext σ2).1 := by
          show ((), σ2) ∈ (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) x.tcbSchedContext σ2).1
          rw [hxc]; unfold ifSporadicCurScAssertRefillUnblockCheck ifCondRefillUnblockCheck
          simp only [NonDet.maybeM]; exact Set.mem_singleton _
        exact (congrArg Prod.snd (hdet3 _ this)).symm
      | some c =>
        obtain ⟨y, k, hky, -⟩ := hI2.back t x' c hkt2 hxc
        have hne : y.scSporadic = true → y.scRefills ≠ [] := fun _ =>
          hI2.ne c y k hky (hsa2 c y k hxc hky)
        obtain ⟨σ3', hm3', hc3⟩ := unblockCur_some hky hne
        have e3 : σ3' = σ3 := congrArg Prod.snd (hdet3 _ (by show _ ∈ (_ : Set _); rw [show x'.tcbSchedContext = some c from hxc]; exact hm3'))
        subst e3
        rcases hc3 with e | ⟨z, e, -, -, hz, -, -⟩
        · exact Or.inl e
        · by_cases hcc : c = σ2.curSc
          · exact Or.inl (unblockCur_self hky hcc hm3')
          · exact Or.inr ⟨c, y, z, k, rfl, hky, e, hz, hcc⟩
    have hkt3 : σ3.kheap t = some (.tcb x') := by
      rcases hshape with e | ⟨c, y, z, k, -, hky, e, -, -⟩
      · rw [e]; exact hkt2
      · have hct : c ≠ t := by rintro rfl; rw [hkt2] at hky; cases hky
        rw [e]; simp [updSc, updK, Ne.symm hct, hkt2]
    have hS3 : Sk σ2 σ3 := by
      rcases hshape with e | ⟨c, y, z, k, -, -, e, -, -⟩
      · rw [e]; exact Sk.refl _
      · rw [e]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    -- the switch
    obtain ⟨σ6, he6, hk6, -, -, -⟩ := pst_ok hkt3 hI3.actReady
    have hm' : ((), σ5) ∈ (possibleSwitchTo (Z := Unit) t σ3).1 := hm
    have e56 : σ5 = σ6 := mem_singleton_snd (by rw [he6] at hm'; exact hm')
    subst e56
    have hI5 : Inv σ5 := by
      by_cases hs : schedulable t σ3 = true
      · exact hI3.qchange (possibleSwitchTo_qchange hI3 hs he6)
      · have hnop : possibleSwitchTo (Z := Unit) t σ3 = ({((), σ3)}, False) := by
          rw [possibleSwitchTo_unfold hkt3, if_neg]
          rintro ⟨hsc, hnr'⟩
          apply hs
          obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hsc
          obtain ⟨y3, k3, hky3, -⟩ := hI3.back t x' c hkt3 hc
          obtain ⟨y2, hky2, hm2, -⟩ := hK3 c y3 k3 hky3
          have ha2 := hsa2 c y2 k3 hc hky2
          exact schedulable_of hkt3 hc rfl hky3 (by simpa [scActive, hm2] using ha2)
            (by simpa [inReleaseQueue] using hnr')
        have : σ5 = σ3 := ((Prod.mk.inj (singleton_one_eq (hnop.symm.trans he6))).2).symm
        rw [this]; exact hI3
    obtain ⟨σ7, he7, hq7⟩ := pst_q hkt3 hI3.actReady
    have e57 : σ5 = σ7 := (Prod.mk.inj (singleton_one_eq (he6.symm.trans he7))).2
    have hS5 : Sk σ3 σ5 := by
      rw [e57]; obtain ⟨rq, act, rfl⟩ := hq7; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨hI5, hS2.trans (hS3.trans hS5), ⟨.restart, Or.inl rfl, by rw [hk6]; exact hkt3⟩, fun p hpt hpc => ?_,
      fun c y k hc hky => ?_⟩
    · rw [hk6]
      rcases hshape with e | ⟨c, y, z, k, hxc, -, e, -, -⟩
      · rw [e]; exact hkp2b p hpt
      · have hpc' : p ≠ c := by rintro rfl; exact hpc hxc
        rw [e]; simp only [updSc, updK, Function.update_of_ne hpc']; exact hkp2b p hpt
    · have hct : c ≠ t := by rintro rfl; rw [hkt] at hky; cases hky
      have hky2 : σ2.kheap c = some (.schedContext y k) := by rw [hkp2b c hct]; exact hky
      rw [hk6]
      rcases hshape with e | ⟨c', y', z, k', hxc', hky', e, hz, hcc⟩
      · exact ⟨y.scRefills, by rw [e, hky2], fun _ => rfl⟩
      · rw [hc] at hxc'; cases hxc'
        rw [hky2] at hky'; cases hky'
        refine ⟨z.scRefills, by rw [e, ← hz]; simp [updSc, updK], fun h => ?_⟩
        exact absurd (h.trans hS2.csc.symm) hcc
  · -- a faulted thread: made inactive
    replace hm : ((), σ5) ∈ (setThreadState (Z := Unit) t .inactive σ).1 := by
      beta_reduce at hm; rw [if_neg hf] at hm; exact hm
    rw [setThreadState_eq' hkt .inactive] at hm
    have e5 := mem_singleton_snd hm
    simp only at e5
    subst e5
    refine ⟨hI.deactivate hkt hnr, (show Sk σ (updK σ t (.tcb { x with tcbState := .inactive })) from
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).trans (Sk.stsAct _ t),
      ⟨.inactive, Or.inr rfl, by rw [stsAct_kheap]; simp [updK]⟩, fun p hpt _ => ?_, fun c y k _ hky => ?_⟩
    · rw [stsAct_kheap]; simp [updK, hpt]
    · have hct : c ≠ t := by rintro rfl; rw [hkt] at hky; cases hky
      exact ⟨y.scRefills, by rw [stsAct_kheap]; simp [updK, hct, hky], fun _ => rfl⟩

/-- The facts the loop carries (`P`: the caller's fact of a receiver). -/
def EpLoopInv (P : ObjRef → Prop) (σ : State Unit) (e : ObjRef) (l : List ObjRef) : Prop :=
  Inv σ ∧ BlockedScActive σ ∧ (∃ x, σ.kheap e = some (.endpoint x) ∧ x.epQueue = l) ∧ l.Nodup ∧
    (∀ u ∈ l, ∃ xu, σ.kheap u = some (.tcb xu) ∧ epBlocked xu.tcbState = some e ∧
      (receiveBlocked xu.tcbState = true → P u)) ∧
    (∀ u ∈ l, MemOK σ u ∧ RepOK σ u) ∧ ScBack σ ∧ ActReady σ

/-- `BlockedScActive` across the frame. -/
theorem EFr.bsa {e : ObjRef} {P : ObjRef → Prop} {σ σ' : State Unit} (h : EFr e P σ σ') (hB : BlockedScActive σ) :
    BlockedScActive σ' := by
  have tcbB : ∀ {p y}, σ'.kheap p = some (.tcb y) → ∃ x st, σ.kheap p = some (.tcb x) ∧
      y = { x with tcbState := st } ∧ TChgE e x st := by
    intro p y hp
    rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
    · exact ⟨y, y.tcbState, by rw [← e', hp], rfl, Or.inl rfl⟩
    · rw [hp] at h2; cases h2
      rcases hc with ⟨x, st, rfl, e2, hs⟩ | ⟨_, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
      exact ⟨x, st, h1, rfl, hs⟩
  have scB : ∀ {p z n}, σ'.kheap p = some (.schedContext z n) → ∃ y rf, σ.kheap p = some (.schedContext y n) ∧
      z = { y with scRefills := rf } := by
    intro p z n hp
    rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
    · exact ⟨z, z.scRefills, by rw [← e', hp], rfl⟩
    · rw [hp] at h2; cases h2
      rcases hc with ⟨_, _, -, e2, -⟩ | ⟨y, n', rf, rfl, e2, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
      exact ⟨y, rf, h1, rfl⟩
  refine ⟨fun p z n u y hp hyt hy hq => ?_, fun p z n hp hr => ?_⟩
  · obtain ⟨y0, rf, hy0, rfl⟩ := scB hp
    obtain ⟨x, st, hx, rfl, hs⟩ := tcbB hy
    exact hB.tcb p y0 n u x hy0 hyt hx (hs.ipcQ hq)
  · obtain ⟨y0, rf, hy0, rfl⟩ := scB hp
    exact hB.replies p y0 n hy0 hr

set_option maxHeartbeats 16000000 in
/-- **One thread of `cancel_all_ipc` keeps the loop's facts**, in `EFr`. -/
theorem inv_ep_iter {P : ObjRef → Prop} {σ σ5 : State Unit} {e t : ObjRef} {l : List ObjRef}
    (h : EpLoopInv P σ e (t :: l)) (hm : ((), σ5) ∈ (removeAndRestartEpQueuedThread (Z := Unit) t e σ).1) :
    EpLoopInv P σ5 e l ∧ EFr e P σ σ5 := by
  obtain ⟨hI, hB, ⟨x, hk, hq⟩, hnd, hbl, hmr, hBk, hA⟩ := h
  obtain ⟨σ5', hm5', ⟨x5, hk5, hq5⟩, hmr5, hBk5, hA5⟩ := ep_iter hk hq hnd hmr hBk hA
  have e55 : σ5 = σ5' := congrArg Prod.snd ((Ipc.det_removeAndRestartEp t e).det σ _ _ hm hm5')
  subst e55
  have htl : t ∉ l := (List.nodup_cons.1 hnd).1
  obtain ⟨xt, hkt, hbe, hPt⟩ := hbl t (List.mem_cons_self ..)
  have het : e ≠ t := by rintro rfl; rw [hk] at hkt; cases hkt
  have hnr : runnable xt.tcbState = false := epBlocked_run hbe
  have hxne : x ≠ .idleEP := by rintro rfl; simp [Endpoint.epQueue] at hq
  -- the dequeue
  have hdq := tcbEpDequeue_eq hk (by rw [hq]; exact List.mem_cons_self ..)
  set σ1 := updK σ e (.endpoint (epDeq x t)) with hσ1
  have hI1 : Inv σ1 := hI.updEp hk
  have hkp1 : ∀ p, p ≠ e → σ1.kheap p = σ.kheap p := fun p hp => by
    simp only [hσ1, updK, Function.update_of_ne hp]
  have hkt1 : σ1.kheap t = some (.tcb xt) := by rw [hkp1 t (Ne.symm het)]; exact hkt
  have hK1 : Ipc.SKeep σ σ1 := Ipc.SKeep.updK (fun _ h => by cases h) (fun _ _ h => by cases h)
  -- the reply
  obtain ⟨ro, hro⟩ : ∃ ro : Option ObjRef,
      ro = if isBlockedOnReceive xt.tcbState then replyObject xt.tcbState else none := ⟨_, rfl⟩
  have hroP : ∀ r, ro = some r → (∃ xr, σ.kheap r = some (.reply xr) ∧ xr.replyTcb = some t) ∧
      ∃ ep d, xt.tcbState = .blockedOnReceive ep (some r) d := by
    intro r hr
    by_cases hb : isBlockedOnReceive xt.tcbState
    · obtain ⟨ep, ro', d, hs⟩ := hb
      rw [hro, if_pos ⟨ep, ro', d, hs⟩, hs] at hr
      simp only [replyObject] at hr; subst hr
      exact ⟨(hmr t (List.mem_cons_self ..)).2 xt hkt ep r d hs, ep, d, hs⟩
    · rw [hro, if_neg hb] at hr; cases hr
  obtain ⟨σ2, st2, he2, hI2, hkt2, hst2, hkp2, hkr2, hS2, hK2⟩ : ∃ σ2 st2,
      NonDet.maybeM (replyUnlinkTcb (Z := Unit) t) ro σ1 = ({((), σ2)}, False) ∧ Inv σ2 ∧
      σ2.kheap t = some (.tcb { xt with tcbState := st2 }) ∧ (st2 = xt.tcbState ∨ st2 = .inactive) ∧
      (∀ p, p ≠ t → ro ≠ some p → σ2.kheap p = σ1.kheap p) ∧
      (∀ r, ro = some r → ∃ xr, σ1.kheap r = some (.reply xr) ∧
        σ2.kheap r = some (.reply { xr with replyTcb := none }) ∧ xr.replyTcb = some t) ∧
      Sk σ1 σ2 ∧ Ipc.SKeep σ1 σ2 := by
    rcases Option.eq_none_or_eq_some ro with hr | ⟨r, hr⟩
    · rw [hr]
      exact ⟨σ1, xt.tcbState, rfl, hI1, hkt1, Or.inl rfl, fun p _ _ => rfl, fun r h => (by cases h), Sk.refl _,
        ⟨rfl, rfl, fun p y hy => ⟨y, hy, rfl⟩, fun p y n hy => hy⟩⟩
    · obtain ⟨⟨xr, hkr, hxrt⟩, ep, d, hst⟩ := hroP r hr
      rw [hr]
      have hre : r ≠ e := by rintro rfl; rw [hk] at hkr; cases hkr
      have hkr1 : σ1.kheap r = some (.reply xr) := by rw [hkp1 r hre]; exact hkr
      have htr : t ≠ r := by rintro rfl; rw [hkt] at hkr; cases hkr
      simp only [NonDet.maybeM]
      rw [replyUnlinkTcb_eq hkr1 hxrt hkt1 (Or.inr ⟨ep, d, hst⟩) htr]
      set σ1' := updK σ1 r (.reply { xr with replyTcb := none }) with hσ1'
      have hkt1' : σ1'.kheap t = some (.tcb xt) := by
        simp only [hσ1', updK, Function.update_of_ne htr]; exact hkt1
      have hI1' : Inv σ1' := hI1.updReply hkr1
      rw [setThreadState_eq' hkt1' .inactive]
      refine ⟨_, .inactive, rfl, hI1'.deactivate hkt1' hnr, by rw [stsAct_kheap]; simp [updK], Or.inr rfl,
        fun p hpt hpr => ?_, fun r' hr' => ?_, ?_, ?_⟩
      · have hpr' : p ≠ r := fun h => hpr (by subst h; rfl)
        rw [stsAct_kheap]; simp [updK, hpt, hpr', hσ1']
      · cases hr'
        refine ⟨xr, hkr1, ?_, hxrt⟩
        rw [stsAct_kheap]; simp [updK, Ne.symm htr, hσ1']
      · exact (show Sk σ1 (updK σ1' t (.tcb { xt with tcbState := .inactive })) from
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).trans (Sk.stsAct _ t)
      · exact ((Ipc.SKeep.updK (fun _ h => by cases h) (fun _ _ h => by cases h)).trans
          (Ipc.SKeep.updK (o := .tcb { xt with tcbState := .inactive }) (fun y h => ⟨xt, hkt1', by cases h; rfl⟩)
            (fun _ _ h => by cases h))).trans (Ipc.SKeep.stsAct _ _)
  -- the restart
  have hsa2 : ∀ p y k, ({ xt with tcbState := st2 } : Tcb).tcbSchedContext = some p →
      σ2.kheap p = some (.schedContext y k) → scActive y = true := by
    intro p y k hp hky
    obtain ⟨y0, k0, hky0, hyt⟩ := hI.back t xt p hkt hp
    have hpt : p ≠ t := by rintro rfl; rw [hkt] at hky0; cases hky0
    have hpe : p ≠ e := by rintro rfl; rw [hk] at hky0; cases hky0
    have hpr : ro ≠ some p := fun hr => by
      obtain ⟨⟨xr, hkr, -⟩, -⟩ := hroP p hr
      rw [hky0] at hkr; cases hkr
    rw [hkp2 p hpt hpr, hkp1 p hpe, hky0] at hky; cases hky
    exact hB.tcb p _ _ t xt hky0 hyt hkt (epBlocked_ipcQ hbe)
  have hrib : RelIfBound σ2 t :=
    Ipc.RelIfBound.of_keep (hI.rd t xt hkt (epBlocked_inClass hbe)) (hK1.trans hK2)
  have hnr2 : runnable ({ xt with tcbState := st2 } : Tcb).tcbState = false := by
    show runnable st2 = false
    rcases hst2 with h | h
    · rw [h]; exact hnr
    · subst h; rfl
  -- the membership
  have hm2 : ((), σ5) ∈ (restartThreadIfNoFault (Z := Unit) t σ2).1 := by
    unfold removeAndRestartEpQueuedThread at hm
    rw [nd_bind_one hdq, nd_bind_one (getThreadState_eq hkt1), nd_pure_bind', ← hro, nd_bind_one he2] at hm
    exact hm
  obtain ⟨hI5, hS5, ⟨st5, hst5, hkt5⟩, hkp5, hsc5⟩ := rtinf_inv hI2 hkt2 hnr2 hrib hsa2 hm2
  -- the objects at the end
  have hkeep : ∀ p, p ≠ t → p ≠ e → ro ≠ some p → xt.tcbSchedContext ≠ some p → σ5.kheap p = σ.kheap p :=
    fun p h1 h2 h3 h4 => by rw [hkp5 p h1 h4, hkp2 p h1 h3, hkp1 p h2]
  have hS12 : Sk σ σ2 := (show Sk σ σ1 from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).trans hS2
  have hS : Sk σ σ5 := hS12.trans hS5
  have F : EFr e P σ σ5 := by
    refine ⟨hS, fun p => ?_⟩
    by_cases hpt : p = t
    · subst hpt
      refine Or.inr ⟨.tcb xt, .tcb { xt with tcbState := st5 }, hkt, hkt5, Or.inl ⟨xt, st5, rfl, rfl, Or.inr ⟨hbe, hst5⟩⟩⟩
    by_cases hpe : p = e
    · have hpt' : p ≠ t := by rw [hpe]; exact het
      have hed : xt.tcbSchedContext ≠ some p := fun hc => by
        obtain ⟨y, k, h1, -⟩ := hI.back t xt p hkt hc
        rw [hpe, hk] at h1; cases h1
      have her : ro ≠ some p := fun hr => by
        obtain ⟨⟨xr, hkr, -⟩, -⟩ := hroP p hr
        rw [hpe, hk] at hkr; cases hkr
      refine Or.inr ⟨.endpoint x, .endpoint (epDeq x t), by rw [hpe]; exact hk, ?_,
        Or.inr (Or.inr (Or.inl ⟨x, epDeq x t, rfl, rfl, hpe, hxne,
          by rw [epDeq_queue']; unfold removeAll; exact List.filter_sublist⟩))⟩
      rw [hkp5 p hpt' hed, hkp2 p hpt' her, hσ1, hpe]; simp [updK]
    by_cases hpr : ro = some p
    · obtain ⟨⟨xr, hkr, hxrt⟩, ep, d, hst⟩ := hroP p hpr
      obtain ⟨xr', hkr1, hkr2', -⟩ := hkr2 p hpr
      have exr : xr' = xr := by
        rw [hkp1 p hpe, hkr] at hkr1; injection hkr1 with h1; injection h1 with h2; exact h2.symm
      rw [exr] at hkr2'
      have hpc : xt.tcbSchedContext ≠ some p := fun hc => by
        obtain ⟨y, k, h1, -⟩ := hI.back t xt p hkt hc
        rw [hkr] at h1; cases h1
      refine Or.inr ⟨.reply xr, .reply { xr with replyTcb := none }, hkr, by rw [hkp5 p hpt hpc]; exact hkr2',
        Or.inr (Or.inr (Or.inr ⟨xr, t, rfl, rfl, hxrt, hPt (by simp [hst, receiveBlocked])⟩))⟩
    by_cases hpc : xt.tcbSchedContext = some p
    · obtain ⟨y, k, hky, -⟩ := hI.back t xt p hkt hpc
      have hky2 : σ2.kheap p = some (.schedContext y k) := by rw [hkp2 p hpt hpr, hkp1 p hpe]; exact hky
      obtain ⟨rf, hrf, hcur⟩ := hsc5 p y k hpc hky2
      exact Or.inr ⟨.schedContext y k, .schedContext { y with scRefills := rf } k, hky, hrf,
        Or.inr (Or.inl ⟨y, k, rf, rfl, rfl, fun h => hcur (h.trans hS12.csc.symm)⟩)⟩
    · exact Or.inl (hkeep p hpt hpe hpr hpc)
  refine ⟨⟨hI5, F.bsa hB, ⟨x5, hk5, hq5⟩, (List.nodup_cons.1 hnd).2, fun u hu => ?_, hmr5, hBk5, hA5⟩, F⟩
  obtain ⟨xu, hku, hbu, hPu⟩ := hbl u (List.mem_cons_of_mem _ hu)
  have hut : u ≠ t := fun h => htl (h ▸ hu)
  have hue : u ≠ e := by rintro rfl; rw [hk] at hku; cases hku
  have hur : ro ≠ some u := fun hr => by
    obtain ⟨⟨xr, hkr, -⟩, -⟩ := hroP u hr
    rw [hku] at hkr; cases hkr
  have huc : xt.tcbSchedContext ≠ some u := fun hc => by
    obtain ⟨y, k, h1, -⟩ := hI.back t xt u hkt hc
    rw [hku] at h1; cases h1
  exact ⟨xu, by rw [hkeep u hut hue hur huc]; exact hku, hbu, hPu⟩

/-- **The loop of `cancel_all_ipc` keeps the loop's facts.** -/
theorem ep_loop_inv {P : ObjRef → Prop} {e : ObjRef} : ∀ (l : List ObjRef) (σ σ' : State Unit), EpLoopInv P σ e l →
    ((), σ') ∈ (NonDet.mapMx (fun t => removeAndRestartEpQueuedThread (Z := Unit) t e) l σ).1 →
    EpLoopInv P σ' e [] ∧ EFr e P σ σ'
  | [], σ, σ', h, hm => by
    have : σ' = σ := mem_singleton_snd hm
    rw [this]; exact ⟨h, EFr.refl _ _ _⟩
  | t :: l, σ, σ', h, hm => by
    obtain ⟨y, hy, hm⟩ := (show ((), σ') ∈ ((removeAndRestartEpQueuedThread (Z := Unit) t e >>= fun _ =>
      NonDet.mapMx (fun t => removeAndRestartEpQueuedThread (Z := Unit) t e) l) σ).1 from hm)
    obtain ⟨⟨⟩, σ5⟩ := y
    obtain ⟨h5, hF5⟩ := inv_ep_iter h hy
    obtain ⟨h', hF'⟩ := ep_loop_inv l σ5 σ' h5 hm
    exact ⟨h', hF5.trans hF'⟩

set_option maxHeartbeats 4000000 in
/-- **`cancel_all_ipc` keeps `Inv` and `BlockedScActive`**, in the frame
`EFr` (`P`: a fact of each queued receiver), the action then
`choose_new_thread` unless nothing changed. -/
theorem inv_cancelAllIpc {P : ObjRef → Prop} {σ σ' : State Unit} {e : ObjRef} (hI : Inv σ)
    (hB : BlockedScActive σ) (hpre : EpPre σ e)
    (hbl : ∀ x, σ.kheap e = some (.endpoint x) → ∀ u ∈ x.epQueue, ∃ xu, σ.kheap u = some (.tcb xu) ∧
      epBlocked xu.tcbState = some e ∧ (receiveBlocked xu.tcbState = true → P u))
    (hm : ((), σ') ∈ (cancelAllIpc (Z := Unit) e σ).1) :
    Inv σ' ∧ BlockedScActive σ' ∧ EFr e P σ σ' ∧ (σ'.schedulerAction = .chooseNewThread ∨ σ' = σ) := by
  obtain ⟨x, hk, hnd, hmr, hBk, hA⟩ := hpre
  have body : ((), σ') ∈ ((NonDet.mapMx (fun t => removeAndRestartEpQueuedThread (Z := Unit) t e) x.epQueue
      >>= fun _ => rescheduleRequired (Z := Unit)) σ).1 →
      Inv σ' ∧ BlockedScActive σ' ∧ EFr e P σ σ' ∧ (σ'.schedulerAction = .chooseNewThread ∨ σ' = σ) := by
    intro hm
    obtain ⟨z, hz, hm⟩ := hm
    obtain ⟨⟨⟩, σf⟩ := z
    have h0 : EpLoopInv P σ e x.epQueue := ⟨hI, hB, ⟨x, hk, rfl⟩, hnd, hbl x hk, hmr, hBk, hA⟩
    obtain ⟨⟨hIf, hBf, -⟩, hFf⟩ := ep_loop_inv x.epQueue σ σf h0 hz
    obtain ⟨σr, hr, hq⟩ := rescheduleRequired_qchange hIf.actReady
    obtain ⟨σr', hr', hQ', ha'⟩ := resched_q hIf.actReady
    have hm' : ((), σ') ∈ (rescheduleRequired (Z := Unit) σf).1 := hm
    have e1 : σ' = σr := mem_singleton_snd (by rw [hr] at hm'; exact hm')
    have e' : σ' = σr' := mem_singleton_snd (by rw [hr'] at hm'; exact hm')
    subst e1
    refine ⟨hIf.qchange hq, ?_, hFf.trans (e' ▸ hQ'.efr), Or.inl (e' ▸ ha')⟩
    obtain ⟨hk', -⟩ := hq
    exact ⟨fun p y k t x hp hyt hx hqt => hBf.tcb p y k t x (hk' ▸ hp) hyt (hk' ▸ hx) hqt,
      fun p y k hp hr' => hBf.replies p y k (hk' ▸ hp) hr'⟩
  unfold cancelAllIpc at hm
  rw [nd_bind_one (getEndpoint_eq hk)] at hm
  cases x with
  | idleEP =>
    have : σ' = σ := mem_singleton_snd hm
    rw [this]; exact ⟨hI, hB, EFr.refl _ _ _, Or.inr rfl⟩
  | sendEP q =>
    simp only at hm; rw [nd_pure_bind'] at hm; exact body hm
  | recvEP q =>
    simp only at hm; rw [nd_pure_bind'] at hm; exact body hm

/-! ### What the frame keeps -/

section
variable {e : ObjRef} {P : ObjRef → Prop} {σ σ' : State Unit}

theorem EFr.tcbF (h : EFr e P σ σ') {p : ObjRef} {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    ∃ st, σ'.kheap p = some (.tcb { x with tcbState := st }) ∧ TChgE e x st := by
  rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x.tcbState, by rw [e', hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨x', st, e1, rfl, hs⟩ | ⟨_, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨st, h2, hs⟩

theorem EFr.tcbB (h : EFr e P σ σ') {p : ObjRef} {y : Tcb} (hp : σ'.kheap p = some (.tcb y)) :
    ∃ x st, σ.kheap p = some (.tcb x) ∧ y = { x with tcbState := st } ∧ TChgE e x st := by
  rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, y.tcbState, by rw [← e', hp], rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨x, st, rfl, e2, hs⟩ | ⟨_, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨x, st, h1, rfl, hs⟩

theorem EFr.scF (h : EFr e P σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ.kheap p = some (.schedContext y n)) :
    ∃ rf, σ'.kheap p = some (.schedContext { y with scRefills := rf } n) ∧ (p = σ.curSc → rf = y.scRefills) := by
  rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y.scRefills, by rw [e', hp], fun _ => rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, e1, -⟩ | ⟨y', n', rf, e1, rfl, hr⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨rf, h2, hr⟩

theorem EFr.scB (h : EFr e P σ σ') {p : ObjRef} {z : SchedContext} {n : Nat}
    (hp : σ'.kheap p = some (.schedContext z n)) :
    ∃ y rf, σ.kheap p = some (.schedContext y n) ∧ z = { y with scRefills := rf } ∧
      (p = σ.curSc → rf = y.scRefills) := by
  rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
  · exact ⟨z, z.scRefills, by rw [← e', hp], rfl, fun _ => rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, -, e2, -⟩ | ⟨y, n', rf, rfl, e2, hr⟩ | ⟨_, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨y, rf, h1, rfl, hr⟩

theorem EFr.epF (h : EFr e P σ σ') {p : ObjRef} {x : Endpoint} (hp : σ.kheap p = some (.endpoint x)) :
    ∃ y, σ'.kheap p = some (.endpoint y) ∧ (y = x ∨ (x ≠ .idleEP ∧ y.epQueue.Sublist x.epQueue)) := by
  rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [e', hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, e1, -⟩ | ⟨_, _, _, e1, -⟩ | ⟨x', y, e1, rfl, -, hx, hs⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨y, h2, Or.inr ⟨hx, hs⟩⟩

theorem EFr.epB (h : EFr e P σ σ') {p : ObjRef} {y : Endpoint} (hp : σ'.kheap p = some (.endpoint y)) :
    ∃ x, σ.kheap p = some (.endpoint x) ∧ (y = x ∨ y.epQueue.Sublist x.epQueue) := by
  rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e', hp], Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, -, e2, -⟩ | ⟨_, _, _, -, e2, -⟩ | ⟨x, y', rfl, e2, -, -, hs⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨x, h1, Or.inr hs⟩

theorem EFr.replyF (h : EFr e P σ σ') {p : ObjRef} {x : Reply} (hp : σ.kheap p = some (.reply x)) :
    ∃ y, σ'.kheap p = some (.reply y) ∧ y.replySc = x.replySc ∧
      (y.replyTcb = x.replyTcb ∨ ((∃ t, x.replyTcb = some t ∧ P t) ∧ y.replyTcb = none)) := by
  rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [e', hp], rfl, Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, e1, -⟩ | ⟨_, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨x', t, e1, rfl, hx, hP⟩ <;> cases e1
    exact ⟨_, h2, rfl, Or.inr ⟨⟨t, hx, hP⟩, rfl⟩⟩

theorem EFr.replyB (h : EFr e P σ σ') {p : ObjRef} {y : Reply} (hp : σ'.kheap p = some (.reply y)) :
    ∃ x, σ.kheap p = some (.reply x) ∧ y.replySc = x.replySc ∧
      (y.replyTcb = x.replyTcb ∨ ((∃ t, x.replyTcb = some t ∧ P t) ∧ y.replyTcb = none)) := by
  rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e', hp], rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, -, e2, -⟩ | ⟨_, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨x, t, rfl, e2, hx, hP⟩ <;> cases e2
    exact ⟨x, h1, rfl, Or.inr ⟨⟨t, hx, hP⟩, rfl⟩⟩

/-- The other kinds (notifications, CNodes, ...) kept. -/
theorem EFr.othF (h : EFr e P σ σ') {p : ObjRef} {o : KernelObject} (hp : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h2 : ∀ y n, o ≠ .schedContext y n) (h3 : ∀ x, o ≠ .endpoint x)
    (h4 : ∀ x, o ≠ .reply x) : σ'.kheap p = some o := by
  rcases h.kh p with e' | ⟨o0, o', k1, k2, hc⟩
  · rw [e', hp]
  · rw [hp] at k1; cases k1
    rcases hc with ⟨_, _, e1, -⟩ | ⟨_, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩
    · exact absurd e1 (h1 _)
    · exact absurd e1 (h2 _ _)
    · exact absurd e1 (h3 _)
    · exact absurd e1 (h4 _)

theorem EFr.othB (h : EFr e P σ σ') {p : ObjRef} {o' : KernelObject} (hp : σ'.kheap p = some o')
    (h1 : ∀ x, o' ≠ .tcb x) (h2 : ∀ y n, o' ≠ .schedContext y n) (h3 : ∀ x, o' ≠ .endpoint x)
    (h4 : ∀ x, o' ≠ .reply x) : σ.kheap p = some o' := by
  rcases h.kh p with e' | ⟨o, o'', k1, k2, hc⟩
  · rw [← e', hp]
  · rw [hp] at k2; cases k2
    rcases hc with ⟨_, _, -, e2, -⟩ | ⟨_, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩
    · exact absurd e2 (h1 _)
    · exact absurd e2 (h2 _ _)
    · exact absurd e2 (h3 _)
    · exact absurd e2 (h4 _)

/-- The objects' kinds and sizes kept, both ways. -/
theorem EFr.kind (h : EFr e P σ σ') (p : ObjRef) :
    (∀ o, σ.kheap p = some o → ∃ o', σ'.kheap p = some o' ∧ aType o' = aType o) ∧
    (∀ o', σ'.kheap p = some o' → ∃ o, σ.kheap p = some o ∧ aType o' = aType o) := by
  rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
  · exact ⟨fun o ho => ⟨o, by rw [e', ho], rfl⟩, fun o' ho => ⟨o', by rw [← e', ho], rfl⟩⟩
  · have ha : aType o' = aType o := by
      rcases hc with ⟨x, st, rfl, rfl, -⟩ | ⟨y, n, rf, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ | ⟨x, t, rfl, rfl, -⟩ <;> rfl
    exact ⟨fun o0 ho0 => ⟨o', h2, by rw [h1] at ho0; cases ho0; exact ha⟩,
      fun o0 ho0 => ⟨o, h1, by rw [h2] at ho0; cases ho0; exact ha⟩⟩

theorem EFr.szKeep (h : EFr e P σ σ') : SzKeep σ σ' := fun p y n hp => by
  obtain ⟨y0, -, hy0, -⟩ := h.scB hp; exact ⟨y0, hy0⟩

theorem EFr.ykeep (h : EFr e P σ σ') : YKeep σ σ' := by
  refine ⟨fun p x hp => ?_, fun p y n hp => ?_, fun p z n hp => ?_⟩
  · obtain ⟨st, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩
  · obtain ⟨rf, hp', -⟩ := h.scF hp; exact ⟨_, hp', rfl⟩
  · obtain ⟨y0, rf, hy0, rfl, -⟩ := h.scB hp; exact ⟨y0, hy0, rfl⟩

theorem EFr.mcpKeep (h : EFr e P σ σ') : McpKeep σ σ' := fun p x hp => by
  obtain ⟨st, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem EFr.bufKeep (h : EFr e P σ σ') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => by obtain ⟨st, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem EFr.prio (h : EFr e P σ σ') (u : ObjRef) : prioOf σ' u = prioOf σ u := by
  unfold prioOf
  rw [tcbsOf_eq, tcbsOf_eq]
  cases hk : σ.kheap u with
  | some o =>
    cases o with
    | tcb x =>
      obtain ⟨st, hk', -⟩ := h.tcbF hk
      rw [hk']; rfl
    | _ =>
      cases hk' : σ'.kheap u with
      | none => rfl
      | some o' => cases o' with
        | tcb y => obtain ⟨x, -, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
        | _ => rfl
  | none =>
    cases hk' : σ'.kheap u with
    | none => rfl
    | some o' => cases o' with
      | tcb y => obtain ⟨x, -, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
      | _ => rfl

theorem EFr.nsc {N C : Set U64} (h : EFr e P σ σ') (hN : NSC N C σ) : NSC N C σ' := by
  intro n hn y p hy hp
  exact hN n hn y p (h.othB hy (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
    (fun _ e => by cases e)) hp

theorem EFr.isorted (h : EFr e P σ σ') (hS : IpcSorted σ) : IpcSorted σ' := by
  refine ⟨fun p y hp => ?_, fun p y hp => ?_⟩
  · obtain ⟨x, hx, hc⟩ := h.epB hp
    rcases hc with rfl | hsub
    · exact (hS.1 p y hx).congr fun u _ => h.prio u
    · exact ((hS.1 p x hx).sublist hsub).congr fun u _ => h.prio u
  · have hp0 := h.othB hp (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e)
    exact (hS.2 p y hp0).congr fun u _ => h.prio u

theorem EFr.own {T C : Set U64} (h : EFr e P σ σ') (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · obtain ⟨st, hkt', -⟩ := h.tcbF hkt
    refine Or.inl ⟨u, hu, _, hkt', by rw [h.sk.csc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
    · rw [h.sk.csc] at hy
      obtain ⟨y0, rf, hy0, rfl, -⟩ := h.scB hy
      exact hown y0 n hy0
    · rw [h.sk.cons] at h0; rw [h.sk.rel] at hm; exact hnr h0 hm
  · refine Or.inr ⟨by rw [h.sk.csc]; exact hcs, fun y n hy => ?_⟩
    rw [h.sk.csc] at hy
    obtain ⟨y0, rf, hy0, rfl, -⟩ := h.scB hy
    exact hun y0 n hy0

theorem EFr.off (h : EFr e P σ σ') (hO : OffOK σ) : OffOK σ' := by
  intro hc y n hy ha
  rw [h.sk.cons] at hc ⊢; rw [h.sk.tm]
  rw [h.sk.csc] at hy ha
  obtain ⟨y0, rf, hy0, rfl, hr⟩ := h.scB hy
  have e' : rf = y0.scRefills := hr rfl
  subst e'
  exact hO hc y0 n hy0 ha

theorem EFr.idleOK (h : EFr e P σ σ') (hO : IdleOK σ) : IdleOK σ' := by
  obtain ⟨x, hx, h1, h2, h3⟩ := hO
  obtain ⟨st, hx', hs⟩ := h.tcbF hx
  refine ⟨{ x with tcbState := st }, by rw [h.sk.idle]; exact hx', h1, ?_, by rw [h.sk.idle, h.sk.rel]; exact h3⟩
  show st = _
  rw [hs.st (by rw [h2]; simp [epBlocked])]; exact h2

/-- What `CallRel` reads of the spec: the SCs' call stacks (and sizes), the
replies' `reply_sc`, the SCs back. -/
theorem EFr.callKeep (h : EFr e P σ σ') :
    (∀ q y n, σ.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
    (∀ q x, σ.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
    (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n)) := by
  refine ⟨fun q y n hq => ?_, fun q x hq => ?_, fun p x n hp => ?_⟩
  · obtain ⟨rf, hq', -⟩ := h.scF hq; exact ⟨_, hq', rfl⟩
  · obtain ⟨y, hy, e', -⟩ := h.replyF hq; exact ⟨y, hy, e'⟩
  · obtain ⟨y0, -, hy0, -⟩ := h.scB hp; exact ⟨y0, hy0⟩

theorem EFr.kback (h : EFr e P σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e' | ⟨ko, ko'', h1, h2, hc⟩
  · exact ⟨ko', by rw [← e', ho], id, id, id, id, id, id⟩
  · rw [ho] at h2; cases h2
    rcases hc with ⟨x, st, rfl, rfl, -⟩ | ⟨y, n, rf, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ | ⟨x, t, rfl, rfl, -⟩ <;>
      exact ⟨_, h1, by simp⟩

theorem EFr.ksz (h : EFr e P σ σ') : KSz σ σ' := fun o ko' ho => by
  obtain ⟨ko, h1, e'⟩ := (h.kind o).2 ko' ho
  exact ⟨ko, h1, e'.symm⟩

theorem EFr.ksub (h : EFr e P σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun rr cs hc hw => ⟨cs, ?_, hw⟩, fun u hu => ?_, fun hn => ?_⟩
  · exact h.othB hc (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e)
  · obtain ⟨x, -, hx, -⟩ := h.tcbB hu; exact ⟨x, hx⟩
  · rcases h.kh o with e' | ⟨ko, ko', h1, -, -⟩
    · rw [e']; exact hn
    · rw [hn] at h1; cases h1

end

end Spec

end

end Fl4Proofs.P3.Sched
