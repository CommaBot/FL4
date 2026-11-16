/-
P3 (DESIGN.md §9), IPC: **waking a thread on the merged relation**
(NtfnSched.lean's `set_thread_state_running` and `wake_refines` with
`IpcRel` and `IpcSchedHyps`). The woken thread is in no queue of either kind
(`hq`, `hqE`), so `IpcRel.upd_tcb` keeps the endpoint part; its TCB relation
after the state and badge-register writes is `TcbRel.of_words`.
-/
import Fl4Proofs.P3.IpcNtfnBase
import Fl4Proofs.P3.EpSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Notif
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Lemmas
open Fl4Spec
variable {Z : Type}

theorem IKView.stsAct (σ : State Z) (t : ObjRef) : IKView σ (stsAct σ t) :=
  ⟨Notif.KView.stsAct σ t, Endp.KView.stsAct' σ t, fun p x h => ⟨x, by rw [stsAct_kheap]; exact h, rfl⟩⟩

theorem setReg_regs (x : Tcb) (r : Register) (v : Word) :
    (setReg x r v).tcbArch.tcbContext.userRegs = Function.update x.tcbArch.tcbContext.userRegs r v := rfl

theorem noEpPayload_running : NoEpPayload .running := by simp [NoEpPayload]

/-- A TCB whose state word is not 3 or 4 is in no endpoint queue. -/
theorem IpcRel.not_ep_queued {N T E R : Set U64} {B : Set (U64 × Word)} {m : U64 → U64} {σ : State Z}
    (hR : IpcRel N T E R B m σ) {t : U64} (hs : (m (tStA t)).val ≠ 3 ∧ (m (tStA t)).val ≠ 4) :
    ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue := by
  intro e he z hz hq
  obtain ⟨z', hz', hr⟩ := hR.ep e he
  rw [hz] at hz'; injection hz' with hz'; injection hz' with hz'; subst hz'
  obtain ⟨xs, -, hq', hm⟩ := hr.queue
  rw [hq', List.mem_map] at hq
  obtain ⟨y, hy, ey⟩ := hq
  have : y = t := eq_of_bv ey
  subst this
  rcases (hm y hy).2 with h | h
  · exact hs.1 h
  · exact hs.2 h

end Lemmas

/-! ## Waking a thread -/

section Wake
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- A single write to a volatile word `a` of the TCB at `t`: memory agrees
elsewhere. -/
theorem wr_agree {s : S} {a v : U64} (ha : Aligned a) (b : U64) (hb : Aligned b) (hne : b.val ≠ a.val) :
    L.mem (L.wr s a v) b = L.mem s b :=
  rd_wr_ne ha hb (fun e => hne (e ▸ rfl))

/-- **The state word of a TCB in no queue, set to running**: related, and
`SR` kept. -/
theorem set_thread_state_runningI (hH : IpcSchedHyps st ar N T E R B SR) (hP : IPlaced N T E R B) (s : S)
    (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hq : ∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue)
    (hqE : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue)
    (hcls : inClass x.tcbState ∨ RelIfBound σ t.bv) (hni : x.tcbState ≠ .idleThreadState) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s' =>
      IpcRel N T E R B (L.mem s') (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) ∧
      SR s' (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) ⦄ := by
  unfold sched.set_thread_state
  step
  subst s1_post
  have hta := hP.e.tcb t ht
  obtain ⟨xt, hkx, hx⟩ := hR.tcb t ht
  rw [hk] at hkx; injection hkx with hkx; injection hkx with hkx; subst hkx
  obtain ⟨hw, -⟩ := twr_wr (st := st) hP.n ht (K := 3328#u64) (Or.inl rfl) s sched.TS_RUNNING
  rw [← tStA_eq] at hw
  have hsa := (a_st hta).1
  have hst := val_st hta
  have hR1 : IpcRel N T E R B (L.mem (L.wr s (tStA t) sched.TS_RUNNING))
      (updK σ t.bv (.tcb { x with tcbState := .running })) := by
    refine hR.upd_tcb hP ht _ (fun b hb ⟨_, hnt⟩ => wr_agree hsa b hb (fun e => hnt (by
      left; exact TF.of_val (a_st hta).2 e))) (Or.inl ⟨hq, hqE⟩) ?_
    refine TcbRel.of_words hta hx _ (fun b hb _ hv => wr_agree hsa b hb (fun e => hv (Or.inl (by rw [e, hst]))))
      ?_ (fun e h => by cases h) (fun n h => by cases h) (Or.inr noEpPayload_running) (fun r => ?_) rfl rfl rfl rfl
    · rw [rd_wr_eq hsa, tsVals.1]; rfl
    · rw [wr_agree hsa _ (a_reg hta r).1 (by rw [regA_val hta (regIdx_lt r), hst]; have := regIdx_lt r; omega)]
      exact hx.regs r
  have hSR1 := hH.stableN _ _ _ _ hSR hw.foot (NtfnStep.tcb hk .running x.tcbArch)
    (NoBlock.tcbUpd hk _ _ (Or.inr ⟨rfl, hni, hcls⟩))
  refine WP.spec_mono (hH.scheduleTcb _ _ t hR1.toE (ScRelM.of hR1) hSR1 ht) ?_
  rintro s2 ⟨hf, hS⟩
  exact ⟨hR1.frame hP hf (IKView.stsAct _ _), hS⟩

/-- **The wake-up of a TCB in no queue refines the spec's.** -/
theorem wake_refinesI (hH : IpcSchedHyps st ar N T E R B SR) (hP : IPlaced N T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ) {t n : U64} (ht : t ∈ T)
    (hn : n ∈ N) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hq : ∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue)
    (hqE : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) (badge : U64)
    (hcls : inClass x.tcbState ∨ RelIfBound σ t.bv) (hnr : Fl4Spec.runnable x.tcbState = false)
    (hni : x.tcbState ≠ .idleThreadState) :
    rustWake st ar s a t n badge ⦃ r => ¬ (specWake t.bv n.bv badge.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (specWake t.bv n.bv badge.bv σ).1 ∧ IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  set x1 : Fl4Spec.Tcb := { x with tcbState := .running }
  set σ2 := stsAct (updK σ t.bv (.tcb x1)) t.bv
  have hk2 : σ2.kheap t.bv = some (.tcb x1) := by simp [σ2, stsAct_kheap]
  set σ3 := updK σ2 t.bv (.tcb (setReg x1 Fl4Spec.badge_register badge.bv))
  have hspec : specWake t.bv n.bv badge.bv σ = specWakeTail t.bv n.bv σ3 := by
    unfold specWake
    rw [nd_bind_one (setThreadState_eq _ hk), nd_bind_one (asUser_setRegister_eq _ _ hk2)]
  rw [hspec]
  unfold rustWake
  refine WP.spec_bind (set_thread_state_runningI hH hP s σ hR hSR ht hk hq hqE hcls hni) ?_
  rintro s2 ⟨hR2, hSR2⟩
  step
  subst s3_post
  have hta := hP.e.tcb t ht
  obtain ⟨xt, hkx, hx1⟩ := hR2.tcb t ht
  rw [hk2] at hkx; injection hkx with hkx; injection hkx with hkx; subst hkx
  obtain ⟨hw, -⟩ := twr_wr (st := st) hP.n ht (K := 256#u64) (Or.inr (Or.inr rfl)) s2 badge
  rw [← badgeRegA_eq] at hw
  have hba : Aligned (badgeRegA t) := by rw [badgeRegA_eq_regA]; exact (a_reg hta _).1
  have hbv : (badgeRegA t).val = t.val + 256 + 8 * (regIdx Fl4Spec.badge_register).val := by
    rw [badgeRegA_eq_regA, regA_val hta (regIdx_lt _)]
  have hbi := regIdx_lt Fl4Spec.badge_register
  have hR3 : IpcRel N T E R B (L.mem (L.wr s2 (badgeRegA t) badge)) σ3 := by
    refine hR2.upd_tcb hP ht _ (fun b hb ⟨_, hnt⟩ => wr_agree hba b hb (fun e => hnt (by
      left; rw [badgeRegA_eq_regA] at e; exact TF.of_val (a_reg hta _).2 e)))
      (Or.inr ⟨wr_agree hba _ (a_st hta).1 (by rw [val_st hta, hbv]; omega),
        wr_agree hba _ (a_blk hta).1 (by rw [val_blk hta, hbv]; omega)⟩) ?_
    refine TcbRel.of_words hta hx1 _ (fun b hb hf hv => wr_agree hba b hb (fun e => hv (Or.inr (Or.inr (by
        rw [e, hbv]; omega)))))
      ?_ (fun e h => by cases h) (fun n h => by cases h) (Or.inl rfl) (fun r => ?_) rfl rfl rfl rfl
    · show (L.mem _ (tStA t)).val = tsCode (setReg x1 _ _).tcbState
      rw [setReg_state, wr_agree hba _ (a_st hta).1 (by rw [val_st hta, hbv]; omega)]; exact hx1.st
    · rw [setReg_regs]
      by_cases e : r = Fl4Spec.badge_register
      · subst e; rw [Function.update_self, ← badgeRegA_eq_regA, rd_wr_eq hba]
      · rw [Function.update_of_ne e, wr_agree hba _ (a_reg hta r).1 (by
          rw [regA_val hta (regIdx_lt r), hbv]
          intro h; exact e (regIdx_inj (by omega)))]
        exact hx1.regs r
  have hSR3 := hH.stableN _ _ _ _ hSR2 hw.foot (by
    have := NtfnStep.tcb hk2 x1.tcbState (setReg x1 Fl4Spec.badge_register badge.bv).tcbArch
    exact this) (NoBlock.tcbUpd hk2 _ _ (Or.inl rfl))
  have hk3 : σ3.kheap t.bv = some (.tcb (setReg x1 Fl4Spec.badge_register badge.bv)) := by simp [σ3]
  have hNQ : NotQueued σ3 t.bv := by
    have h0 := hH.notQueued s σ t x hR hSR hk hnr
    have e1 : σ2.readyQueues = σ.readyQueues := by
      show (stsAct _ _).readyQueues = _; unfold stsAct; split_ifs <;> rfl
    have e2 : σ2.releaseQueue = σ.releaseQueue := by
      show (stsAct _ _).releaseQueue = _; unfold stsAct; split_ifs <;> rfl
    exact ⟨fun d p => by show t.bv ∉ σ2.readyQueues d p; rw [e1]; exact h0.1 d p,
      by show t.bv ∉ σ2.releaseQueue; rw [e2]; exact h0.2⟩
  refine WP.spec_mono (hH.wakeTail _ a σ3 t n _ hR3 hSR3 ht hn hk3 rfl hNQ) ?_
  rintro r ⟨hnf, σ', hmem, hR', hS⟩
  exact ⟨hnf, σ', hmem, hR', hS⟩

end Wake

end

end Fl4Proofs.P3.Notif
