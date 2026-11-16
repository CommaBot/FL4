/-
P3 (DESIGN.md §9), IPC: **`receive_signal` and `complete_signal` on the
merged relation** (NtfnRecv.lean with `IpcRel`, `IpcSchedHyps` and the
receive-side hypotheses `IpcRecvHyps`, whose tails keep `IFoot` and
`IKView`): polling, receiving from an active notification, completing a
signal. The badge-register write keeps the TCB in its queues
(`IpcRel.upd_tcb` with the state and block words kept); the notification's
state word is the only notification word written.
-/
import Fl4Proofs.P3.IpcNtfnSched
import Fl4Proofs.P3.IpcNtfnSend
import Fl4Proofs.P3.NtfnRecv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Notif
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Hyps
variable {S A : Type} (st : machine.Store S) (ar : machine.Arch A) [L : LawfulStore st]

/-- `c` (FL4, from `s`) refines `m` (spec, from `σ`): the spec does not fail,
FL4's outcome is matched by one of the spec's, FL4 keeps the footprint, the
spec keeps `KView`, and `SR` holds after. -/
def TailRefI (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop) {α : Type}
    (fst : α → S) (s : S) (σ : Fl4Spec.State Unit) (c : Result α) (m : Fl4Spec.SMonad Unit Unit) : Prop :=
  c ⦃ r => ¬ (m σ).2 ∧ ∃ σ', ((), σ') ∈ (m σ).1 ∧ Agree (L.mem s) (L.mem (fst r)) (IFoot N T E R B) ∧
    IKView σ σ' ∧ SR (fst r) σ' ⦄

/-- The receive-side hypotheses on the other subsystems. -/
structure IpcRecvHyps (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop) :
    Prop where
  recvTail : ∀ s (a : A) σ (t n : U64), IpcRel N T E R B (L.mem s) σ → SR s σ → t ∈ T → n ∈ N →
    NotQueued σ t.bv → (∀ x, σ.kheap t.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true) → TailRefI st N T E R B SR Prod.fst s σ (rustRecvTail st ar s a t n) (specRecvTail t.bv n.bv)
  completeTail : ∀ s (a : A) σ (t n : U64), IpcRel N T E R B (L.mem s) σ → SR s σ → t ∈ T → n ∈ N →
    NotQueued σ t.bv → (∀ x, σ.kheap t.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true) → TailRefI st N T E R B SR Prod.fst s σ (rustCompleteTail st ar s a t n) (specCompleteTail t.bv n.bv)
  returnSc : ∀ s σ0 σ (t n : U64), IpcRel N T E R B (L.mem s) σ → SR s σ → t ∈ T → n ∈ N →
    ActReady σ0 → BlockStep σ0 σ t.bv n.bv → t.bv ≠ σ.idleThread →
    TailRefI st N T E R B SR id s σ (notification.maybe_return_sched_context st s n t) (Fl4Spec.maybeReturnSc n.bv t.bv)

end Hyps

/-! ## Single writes -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)}

/-- Writing the badge register of a TCB. -/
theorem set_badge_reg_relI (hP : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hR : IpcRel N T E R B (L.mem s) σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (v : U64) :
    IpcRel N T E R B (L.mem (L.wr s (badgeRegA t) v)) (updK σ t.bv (.tcb (setReg x Fl4Spec.badge_register v.bv))) ∧
      WritesIn st s (L.wr s (badgeRegA t) v) (NWrite N T) ∧
      NtfnStep σ (updK σ t.bv (.tcb (setReg x Fl4Spec.badge_register v.bv))) := by
  have hta := hP.e.tcb t ht
  obtain ⟨xt, hkx, hx⟩ := hR.tcb t ht
  rw [hk] at hkx; injection hkx with hkx; injection hkx with hkx; subst hkx
  obtain ⟨hw, -⟩ := twr_wr (st := st) hP.n ht (K := 256#u64) (Or.inr (Or.inr rfl)) s v
  rw [← badgeRegA_eq] at hw
  have hba : Aligned (badgeRegA t) := by rw [badgeRegA_eq_regA]; exact (a_reg hta _).1
  have hbv : (badgeRegA t).val = t.val + 256 + 8 * (regIdx Fl4Spec.badge_register).val := by
    rw [badgeRegA_eq_regA, regA_val hta (regIdx_lt _)]
  have hbi := regIdx_lt Fl4Spec.badge_register
  refine ⟨hR.upd_tcb hP ht _ (fun b hb ⟨_, hnt⟩ => wr_agree (st := st) hba b hb (fun e => hnt (by
      left; rw [badgeRegA_eq_regA] at e; exact TF.of_val (a_reg hta _).2 e)))
      (Or.inr ⟨wr_agree (st := st) hba _ (a_st hta).1 (by rw [val_st hta, hbv]; omega),
        wr_agree (st := st) hba _ (a_blk hta).1 (by rw [val_blk hta, hbv]; omega)⟩) ?_, hw.foot, NtfnStep.tcb hk x.tcbState _⟩
  refine TcbRel.of_words hta hx _ (fun b hb hf hv => wr_agree (st := st) hba b hb (fun e => hv (Or.inr (Or.inr (by
      rw [e, hbv]; omega))))) ?_ ?_ ?_ (Or.inl rfl) (fun r => ?_) rfl rfl rfl rfl
  · show (L.mem _ (tStA t)).val = tsCode (setReg x _ _).tcbState
    rw [setReg_state, wr_agree (st := st) hba _ (a_st hta).1 (by rw [val_st hta, hbv]; omega)]; exact hx.st
  · intro e he
    rw [wr_agree (st := st) hba _ (a_blk hta).1 (by rw [val_blk hta, hbv]; omega)]; exact hx.blkE e he
  · intro e he
    rw [wr_agree (st := st) hba _ (a_blk hta).1 (by rw [val_blk hta, hbv]; omega)]; exact hx.blkN e he
  · rw [setReg_regs]
    by_cases e : r = Fl4Spec.badge_register
    · subst e; rw [Function.update_self, ← badgeRegA_eq_regA, rd_wr_eq hba]
    · rw [Function.update_of_ne e, wr_agree (st := st) hba _ (a_reg hta r).1 (by
        rw [regA_val hta (regIdx_lt r), hbv]
        intro h; exact e (regIdx_inj (by omega)))]
      exact hx.regs r

/-- Making an active notification idle (`set_state(NTFN_IDLE)`). -/
theorem set_idle_relI (hP : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hR : IpcRel N T E R B (L.mem s) σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0) :
    let s' := L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))
    IpcRel N T E R B (L.mem s') (updK σ n.bv (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))) ∧
      WritesIn st s s' (NWrite N T) ∧
      NtfnStep σ (updK σ n.bv (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))) := by
  intro s'
  have hna := hP.n.ntfn n hn
  have h : NWr st N T n s s' := by
    show NWr st N T n s (L.wr s (epTSA n) _); rw [epTSA_eq]; exact nwr_wr hP.n hn (by simp) (by simp) _ _
  have hout : ∀ b, Aligned b → ¬ NW n b → L.mem s' b = L.mem s b := fun b hb hnw =>
    rd_wr_ne (foot_ts hP.n hn).1 hb (fun e => hnw (e ▸ (nw_words hP hn).2.1))
  have hx := hR.toN.at_ntfn hn hk
  have hobj := hx.obj
  rw [hact] at hobj
  obtain ⟨-, hq, -⟩ := hobj
  rw [queueRel_nil_iff] at hq
  have ne_ts : ∀ K : U64, K.val < 40 → K.val % 8 = 0 → K ≠ 8#u64 →
      L.mem s' (core.num.U64.wrapping_add n K) = L.mem s (core.num.U64.wrapping_add n K) := by
    intro K hK hK8 hne
    show L.mem (L.wr _ (epTSA n) _) _ = _
    rw [epTSA_eq]
    exact rd_wr_ne (nword hP.n hn (by simp) (by simp)).1 (nword hP.n hn hK hK8).1
      (nwords_ne hna (by simp) (by omega) (Ne.symm hne))
  have e_head : L.mem s' (epHeadA n) = L.mem s (epHeadA n) := by rw [epHeadA_eq, ne_ts _ (by simp) (by simp) (by simp)]
  have e_ts : L.mem s' (epTSA n) = (L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64) :=
    rd_wr_eq (foot_ts hP.n hn).1
  have e_bound : L.mem s' (nBoundA n) = L.mem s (nBoundA n) := by
    rw [nBoundA_eq, ne_ts _ (by simp) (by simp) (by simp)]
  have e_sc : L.mem s' (nScA n) = L.mem s (nScA n) := by rw [nScA_eq, ne_ts _ (by simp) (by simp) (by simp)]
  refine ⟨hR.upd_ntfn hP hn _ (fun b hb ⟨_, hnw, _⟩ => hout b hb hnw) ⟨?_, ?_, ?_, ?_⟩,
    h.foot, NtfnStep.ntfn hk rfl rfl⟩
  · show NtfnObjRel _ T n .idleNtfn
    refine ⟨?_, ?_⟩
    · rw [stOf, e_ts, ts_state]; exact zero_and3'
    · rw [queueRel_nil_iff]
      refine ⟨?_, ?_⟩
      · show L.mem s' (epHeadA n) = 0#u64
        rw [e_head]; exact hq.1
      · show L.mem s' (epTSA n) &&& ~~~3#u64 = 0#u64
        rw [e_ts, ts_end]; exact hq.2
  · show x.ntfnBoundTcb = _; rw [e_bound]; exact hx.bound
  · rw [e_bound]; exact hx.bound_mem
  · show x.ntfnSc = _; rw [e_sc]; exact hx.sc

end

/-! ## `receive_signal` -/

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **Polling** a notification that is not active: the badge register gets
0. -/
theorem receive_signal_pollI (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : IpcRel N T E R B (L.mem s) σ) {t : U64} (ht : t ∈ T) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b) (cb : Fl4Spec.Badge) (cr : Fl4Spec.CapRights) :
    notification.receive_signal st ar s a t n false ⦃ r =>
      r.2 = a ∧ SingleRelI (st := st) N T E R B s σ (Fl4Spec.receiveSignal t.bv (.notificationCap n.bv cb cr) false σ) r.1 ⦄ := by
  have hx := hR.toN.at_ntfn hn hk
  obtain ⟨xt, hkt, -⟩ := hR.tcb t ht
  have hspec : Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) false σ =
      ({((), updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register 0)))}, False) := by
    rw [receiveSignal_notActive hk hna]
    unfold Fl4Spec.receiveSignalBlocked Fl4Spec.doNbrecvFailedTransfer
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [nd_bind_one (asUser_setRegister_eq _ _ hkt)]
    rfl
  have hst : stOf (L.mem s) n = obj.NTFN_IDLE ∨ stOf (L.mem s) n = obj.NTFN_WAITING := by
    have := hx.obj
    cases h : x.ntfnObj with
    | idleNtfn => exact Or.inl (stOf_idle (T := T) (h ▸ this) rfl)
    | waitingNtfn q => exact Or.inr (stOf_waiting (T := T) (h ▸ this) rfl)
    | activeNtfn b => exact absurd h (hna b)
  obtain ⟨hR', hW, hS⟩ := set_badge_reg_relI hP hR ht hkt 0#u64
  unfold notification.receive_signal
  step
  rw [st_post, epState_eq] at *
  rcases hst with hst | hst
  · simp only [hst, ↓reduceIte, Bool.false_eq_true]
    step
    subst s1_post
    refine ⟨_, hspec, hR', hS, hW, NoBlock.of fun q x1 y1 h1 h2 => ?_⟩
    by_cases e : q = t.bv
    · subst e; rw [hkt] at h1; cases h1; simp at h2; cases h2; rfl
    · simp [e, h1] at h2; cases h2; rfl
  · simp only [hst, ntfn_consts.1, ntfn_consts.2.1, show (1#u64 : U64) ≠ 0#u64 by decide, ↓reduceIte,
      Bool.false_eq_true]
    step
    subst s1_post
    refine ⟨_, hspec, hR', hS, hW, NoBlock.of fun q x1 y1 h1 h2 => ?_⟩
    by_cases e : q = t.bv
    · subst e; rw [hkt] at h1; cases h1; simp at h2; cases h2; rfl
    · simp [e, h1] at h2; cases h2; rfl


/-- Receiving from an active notification: the badge register and the
notification after the two writes, related to the spec's. -/
theorem recv_active_prefixI (hP : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hR : IpcRel N T E R B (L.mem s) σ) {t : U64} (ht : t ∈ T) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) {b0 : Fl4Spec.Badge}
    (hact : x.ntfnObj = .activeNtfn b0) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) :
    let s1 := L.wr s (badgeRegA t) (L.mem s (nBadgeA n))
    let s2 := L.wr s1 (epTSA n) ((L.mem s1 (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))
    let σ1 := updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))
    let σ2 := updK σ1 n.bv (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))
    Fl4Spec.asUser (Z := Unit) t.bv (Fl4Spec.setRegister Fl4Spec.badge_register b0) σ = ({((), σ1)}, False) ∧
    Fl4Spec.setNotification (Z := Unit) n.bv (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x) σ1 =
      ({((), σ2)}, False) ∧
    IpcRel N T E R B (L.mem s2) σ2 ∧ WritesIn st s s2 (NWrite N T) ∧ NtfnStep σ σ2 := by
  intro s1 s2 σ1 σ2
  have hx := hR.toN.at_ntfn hn hk
  have hb0 : (L.mem s (nBadgeA n)).bv = b0 := by
    have := hx.obj; rw [hact] at this; exact this.2.2
  obtain ⟨hR1, hW1, hS1⟩ := set_badge_reg_relI hP hR ht hkt (L.mem s (nBadgeA n))
  rw [hb0] at hR1 hS1
  have hnt : n.bv ≠ t.bv := by intro e; rw [e, hkt] at hk; cases hk
  have hk1 : σ1.kheap n.bv = some (.notification x) := by simp [σ1, hnt, hk]
  obtain ⟨hR2, hW2, hS2⟩ := set_idle_relI hP hR1 hn hk1 hact
  exact ⟨asUser_setRegister_eq _ _ hkt, setNotification_eq _ hk1, hR2,
    (hW1.trans hW2).mono (fun _ h => by rcases h with h | h <;> exact h), hS1.trans hS2⟩

/-- **Receive on an active notification**: the badge goes to the badge
register, the notification becomes idle, then the scheduler tail. -/
theorem receive_signal_activeI (hH : IpcSchedHyps st ar N T E R B SR) (hV : IpcRecvHyps st ar N T E R B SR)
    (hP : IPlaced N T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (blk : Bool) (cb : Fl4Spec.Badge) (cr : Fl4Spec.CapRights) (hNQ : NotQueued σ t.bv)
    (hRun : ∀ x, σ.kheap t.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true) :
    notification.receive_signal st ar s a t n blk ⦃ r =>
      ¬ (Fl4Spec.receiveSignal t.bv (.notificationCap n.bv cb cr) blk σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveSignal t.bv (.notificationCap n.bv cb cr) blk σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.toN.at_ntfn hn hk
  obtain ⟨xt, hkt, -⟩ := hR.tcb t ht
  obtain ⟨e1, e2, hR2, hW, hS⟩ := recv_active_prefixI (st := st) hP hR ht hn hk hact hkt
  have hspec : Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) blk σ =
      specRecvTail t.bv n.bv (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
        (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))) := by
    rw [receiveSignal_cap hk]
    simp only [hact]
    rw [nd_bind_one e1, nd_bind_one e2]
  rw [hspec]
  have hnt : n.bv ≠ t.bv := by intro e; rw [e, hkt] at hk; cases hk
  have hSR2 := hH.stableN _ _ _ _ hSR hW hS (NoBlock.recvPrefix hkt hnt _ _ _)
  have hNQ2 := hNQ
  have hRun2 : ∀ z, (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
      (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))).kheap t.bv = some (.tcb z) →
      Fl4Spec.runnable z.tcbState = true := by
    intro y hy
    simp only [updK_kheap, Function.update_apply, Ne.symm hnt, ↓reduceIte] at hy
    cases hy; exact hRun xt hkt
  have hsa : stOf (L.mem s) n = obj.NTFN_ACTIVE := stOf_active hx.obj hact
  unfold notification.receive_signal
  step
  have hi : ¬ L.epState s n = obj.NTFN_IDLE := by
    rw [epState_eq, hsa, ntfn_consts.1, ntfn_consts.2.2]; decide
  have hw' : ¬ L.epState s n = obj.NTFN_WAITING := by
    rw [epState_eq, hsa, ntfn_consts.2.1, ntfn_consts.2.2]; decide
  rw [st_post]
  simp only [hi, hw', ↓reduceIte]
  step
  step
  step
  subst_vars
  refine WP.spec_mono (hV.recvTail _ a _ t n hR2 hSR2 ht hn hNQ2 hRun2) ?_
  rintro r ⟨hnf, σ', hm, hf, hv, hS'⟩
  exact ⟨hnf, σ', hm, hR2.frame hP hf hv, hS'⟩

/-- **`complete_signal` on an active notification** (bound notification at
the end of a receive): as the active receive, with `complete_signal`'s
tail. -/
theorem complete_signal_activeI (hH : IpcSchedHyps st ar N T E R B SR) (hV : IpcRecvHyps st ar N T E R B SR)
    (hP : IPlaced N T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (hNQ : NotQueued σ t.bv) (hRun : ∀ x, σ.kheap t.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true) :
    notification.complete_signal st ar s a n t ⦃ r =>
      ¬ (Fl4Spec.completeSignal n.bv t.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (Fl4Spec.completeSignal n.bv t.bv σ).1 ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.toN.at_ntfn hn hk
  obtain ⟨xt, hkt, -⟩ := hR.tcb t ht
  obtain ⟨e1, e2, hR2, hW, hS⟩ := recv_active_prefixI (st := st) hP hR ht hn hk hact hkt
  have hspec : Fl4Spec.completeSignal (Z := Unit) n.bv t.bv σ =
      specCompleteTail t.bv n.bv (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
        (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))) := by
    unfold Fl4Spec.completeSignal
    rw [nd_bind_one (getNotification_eq hk)]
    simp only [hact]
    rw [nd_bind_one e1, nd_bind_one e2]
    rfl
  rw [hspec]
  have hnt : n.bv ≠ t.bv := by intro e; rw [e, hkt] at hk; cases hk
  have hSR2 := hH.stableN _ _ _ _ hSR hW hS (NoBlock.recvPrefix hkt hnt _ _ _)
  have hNQ2 := hNQ
  have hRun2 : ∀ z, (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
      (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))).kheap t.bv = some (.tcb z) →
      Fl4Spec.runnable z.tcbState = true := by
    intro y hy
    simp only [updK_kheap, Function.update_apply, Ne.symm hnt, ↓reduceIte] at hy
    cases hy; exact hRun xt hkt
  have hsa : stOf (L.mem s) n = obj.NTFN_ACTIVE := stOf_active hx.obj hact
  have ht0 : t ≠ 0#u64 := fun e => (hP.e.tcb t ht).ne0 (by rw [e]; rfl)
  unfold notification.complete_signal
  step
  simp only [b_post, ht0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step
  rw [i_post, epState_eq, hsa]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  step
  step
  step
  subst_vars
  refine WP.spec_mono (hV.completeTail _ a _ t n hR2 hSR2 ht hn hNQ2 hRun2) ?_
  rintro r ⟨hnf, σ', hm, hf, hv, hS'⟩
  exact ⟨hnf, σ', hm, hR2.frame hP hf hv, hS'⟩

end

end

end Fl4Proofs.P3.Notif
