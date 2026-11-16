/-
P3 (DESIGN.md §9), IPC: **`send_signal` without a wake-up on the merged
relation** (NtfnSend.lean with `IpcRel`): idle unbound, idle with a bound TCB
not receiving, active. The notification's words are the only ones written
(`hout`), so `IpcRel.upd_ntfn` keeps the endpoint part.
-/
import Fl4Proofs.P3.IpcNtfnBase
import Fl4Proofs.P3.NtfnSend
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

/-! ## The store side: writing the state and the badge -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)}

/-- `set_active` on an idle notification: related to the spec's
`set_notification` of an active notification with the badge. -/
theorem set_active_relI (hP : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hR : IpcRel N T E R B (L.mem s) σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn) (b : U64) :
    let s' := L.wr (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64)))
      (nBadgeA n) b
    IpcRel N T E R B (L.mem s')
        (updK σ n.bv (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn b.bv) x))) ∧
      WritesIn st s s' (NWrite N T) := by
  intro s'
  have hna := hP.n.ntfn n hn
  have h1 : NWr st N T n s (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64))) := by
    rw [epTSA_eq]; exact nwr_wr hP.n hn (by simp) (by simp) _ _
  have h2 : NWr st N T n (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64))) s' := by
    show NWr st N T n _ (L.wr _ (nBadgeA n) b)
    rw [nBadgeA_eq]; exact nwr_wr hP.n hn (by simp) (by simp) _ _
  have h := h1.trans h2
  have hout : ∀ b, Aligned b → ¬ NW n b → L.mem s' b = L.mem s b := fun b hb hnw => by
    show L.mem (L.wr (L.wr s _ _) _ _) b = _
    rw [rd_wr_ne (foot_badge hP.n hn).1 hb (fun e => hnw (e ▸ (nw_words hP hn).2.2.1)),
      rd_wr_ne (foot_ts hP.n hn).1 hb (fun e => hnw (e ▸ (nw_words hP hn).2.1))]
  have hx := hR.toN.at_ntfn hn hk
  have hobj := hx.obj
  rw [hidle] at hobj
  obtain ⟨-, hq⟩ := hobj
  rw [queueRel_nil_iff] at hq
  -- the words of `n` after the two writes
  have ne_b : ∀ K : U64, K.val < 40 → K.val % 8 = 0 → K ≠ 16#u64 →
      L.mem s' (core.num.U64.wrapping_add n K) =
        L.mem (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64)))
          (core.num.U64.wrapping_add n K) := by
    intro K hK hK8 hne
    show L.mem (L.wr _ (nBadgeA n) b) _ = _
    rw [nBadgeA_eq]
    exact rd_wr_ne (nword hP.n hn (by simp) (by simp)).1 (nword hP.n hn hK hK8).1
      (nwords_ne hna (by simp) (by omega) (Ne.symm hne))
  have ne_ts : ∀ K : U64, K.val < 40 → K.val % 8 = 0 → K ≠ 8#u64 →
      L.mem (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64)))
          (core.num.U64.wrapping_add n K) = L.mem s (core.num.U64.wrapping_add n K) := by
    intro K hK hK8 hne
    rw [epTSA_eq]
    exact rd_wr_ne (nword hP.n hn (by simp) (by simp)).1 (nword hP.n hn hK hK8).1
      (nwords_ne hna (by simp) (by omega) (Ne.symm hne))
  have e_head : L.mem s' (epHeadA n) = L.mem s (epHeadA n) := by
    rw [epHeadA_eq, ne_b _ (by simp) (by simp) (by simp), ne_ts _ (by simp) (by simp) (by simp)]
  have e_ts : L.mem s' (epTSA n) = (L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64) := by
    rw [epTSA_eq, ne_b _ (by simp) (by simp) (by simp), ← epTSA_eq]
    exact rd_wr_eq (foot_ts hP.n hn).1
  have e_badge : L.mem s' (nBadgeA n) = b := rd_wr_eq (foot_badge hP.n hn).1
  have e_bound : L.mem s' (nBoundA n) = L.mem s (nBoundA n) := by
    rw [nBoundA_eq, ne_b _ (by simp) (by simp) (by simp), ne_ts _ (by simp) (by simp) (by simp)]
  have e_sc : L.mem s' (nScA n) = L.mem s (nScA n) := by
    rw [nScA_eq, ne_b _ (by simp) (by simp) (by simp), ne_ts _ (by simp) (by simp) (by simp)]
  refine ⟨hR.upd_ntfn hP hn _ (fun b hb ⟨_, hnw, _⟩ => hout b hb hnw) ⟨?_, ?_, ?_, ?_⟩, h.foot⟩
  · show NtfnObjRel _ T n (.activeNtfn b.bv)
    refine ⟨?_, ?_, by rw [e_badge]⟩
    · rw [stOf, e_ts, ts_state, ntfn_consts.2.2]; exact two_and3
    · rw [queueRel_nil_iff]
      refine ⟨?_, ?_⟩
      · show L.mem s' (epHeadA n) = 0#u64
        rw [e_head]; exact hq.1
      · show L.mem s' (epTSA n) &&& ~~~3#u64 = 0#u64
        rw [e_ts, ts_end]; exact hq.2
  · show x.ntfnBoundTcb = _; rw [e_bound]; exact hx.bound
  · rw [e_bound]; exact hx.bound_mem
  · show x.ntfnSc = _; rw [e_sc]; exact hx.sc

/-- Writing the badge word of an active notification (`send_signal` on an
active notification). -/
theorem set_badge_relI (hP : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hR : IpcRel N T E R B (L.mem s) σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (b : U64) :
    let s' := L.wr s (nBadgeA n) b
    IpcRel N T E R B (L.mem s')
        (updK σ n.bv (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn b.bv) x))) ∧
      WritesIn st s s' (NWrite N T) := by
  intro s'
  have hna := hP.n.ntfn n hn
  have h : NWr st N T n s s' := by show NWr st N T n s (L.wr s _ b); rw [nBadgeA_eq]; exact nwr_wr hP.n hn (by simp) (by simp) _ _
  have hout : ∀ b, Aligned b → ¬ NW n b → L.mem s' b = L.mem s b := fun b hb hnw =>
    rd_wr_ne (foot_badge hP.n hn).1 hb (fun e => hnw (e ▸ (nw_words hP hn).2.2.1))
  have hx := hR.toN.at_ntfn hn hk
  have hobj := hx.obj
  rw [hact] at hobj
  obtain ⟨hs, hq, -⟩ := hobj
  have ne_b : ∀ K : U64, K.val < 40 → K.val % 8 = 0 → K ≠ 16#u64 →
      L.mem s' (core.num.U64.wrapping_add n K) = L.mem s (core.num.U64.wrapping_add n K) := by
    intro K hK hK8 hne
    show L.mem (L.wr _ (nBadgeA n) b) _ = _
    rw [nBadgeA_eq]
    exact rd_wr_ne (nword hP.n hn (by simp) (by simp)).1 (nword hP.n hn hK hK8).1
      (nwords_ne hna (by simp) (by omega) (Ne.symm hne))
  have hnw : NWordsEq (L.mem s) (L.mem s') n ∨ True := Or.inr trivial
  clear hnw
  have e_head : L.mem s' (epHeadA n) = L.mem s (epHeadA n) := by rw [epHeadA_eq, ne_b _ (by simp) (by simp) (by simp)]
  have e_ts : L.mem s' (epTSA n) = L.mem s (epTSA n) := by rw [epTSA_eq, ne_b _ (by simp) (by simp) (by simp)]
  have e_bound : L.mem s' (nBoundA n) = L.mem s (nBoundA n) := by
    rw [nBoundA_eq, ne_b _ (by simp) (by simp) (by simp)]
  have e_sc : L.mem s' (nScA n) = L.mem s (nScA n) := by rw [nScA_eq, ne_b _ (by simp) (by simp) (by simp)]
  have hqe : qOf (L.mem s') n = qOf (L.mem s) n := by simp only [qOf, e_head, e_ts]
  refine ⟨hR.upd_ntfn hP hn _ (fun b hb ⟨_, hnw, _⟩ => hout b hb hnw) ⟨?_, ?_, ?_, ?_⟩, h.foot⟩
  · show NtfnObjRel _ T n (.activeNtfn b.bv)
    refine ⟨?_, ?_, by rw [rd_wr_eq (foot_badge hP.n hn).1]⟩
    · simp only [stOf, e_ts]; exact hs
    · rw [hqe, queueRel_nil_iff]; exact queueRel_nil_iff.1 hq
  · show x.ntfnBoundTcb = _; rw [e_bound]; exact hx.bound
  · rw [e_bound]; exact hx.bound_mem
  · show x.ntfnSc = _; rw [e_sc]; exact hx.sc

end

/-! ## `send_signal` -/

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)}

/-- What the simple refinements conclude. -/
def SingleRelI (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (s : S) (σ : Fl4Spec.State Unit)
    (spec : Set (Unit × Fl4Spec.State Unit) × Prop) (s' : S) : Prop :=
  ∃ σ', spec = ({((), σ')}, False) ∧ IpcRel N T E R B (L.mem s') σ' ∧ NtfnStep σ σ' ∧
    WritesIn st s s' (NWrite N T)

/-- **Idle, no bound TCB**: the notification becomes active with the badge. -/
theorem send_signal_idle_unboundI (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : IpcRel N T E R B (L.mem s) σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn)
    (hb : x.ntfnBoundTcb = none) (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r =>
      r.2 = a ∧ SingleRelI (st := st) N T E R B s σ (Fl4Spec.sendSignal n.bv badge.bv σ) r.1 ⦄ := by
  have hx := hR.toN.at_ntfn hn hk
  have h0 : L.mem s (nBoundA n) = 0#u64 := optRef_none (hx.bound ▸ hb)
  unfold notification.send_signal
  step
  have : st = obj.NTFN_IDLE := by rw [st_post]; exact stOf_idle hx.obj hidle
  simp only [this, ↓reduceIte]
  step
  step
  simp only [b_post, i_post, h0, decide_true, ↓reduceIte]
  step
  subst s1_post
  obtain ⟨hR', hW⟩ := set_active_relI hP hR hn hk hidle badge
  exact ⟨_, sendSignal_activate hk hidle (Or.inl hb) badge.bv, hR', NtfnStep.ntfn hk rfl rfl, hW⟩

/-- **Idle, bound TCB not receiving**: the notification becomes active with
the badge. -/
theorem send_signal_idle_bound_idleI (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : IpcRel N T E R B (L.mem s) σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn)
    {t : Fl4Spec.ObjRef} {tcb : Fl4Spec.Tcb} (hb : x.ntfnBoundTcb = some t) (hkt : σ.kheap t = some (.tcb tcb))
    (hrb : Fl4Spec.receiveBlocked tcb.tcbState = false)
    (hvm : tcb.tcbState ≠ .runningVM) (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r =>
      r.2 = a ∧ SingleRelI (st := st) N T E R B s σ (Fl4Spec.sendSignal n.bv badge.bv σ) r.1 ⦄ := by
  have hx := hR.toN.at_ntfn hn hk
  obtain ⟨hb0, hbt⟩ := optRef_some (hx.bound ▸ hb)
  have hbT := hx.bound_mem hb0
  have hy := hR.toN.at_tcb hbT (hbt ▸ hkt)
  have hns : L.mem s (tStA (L.mem s (nBoundA n))) ≠ sched.TS_BLOCKED_ON_RECV := by
    intro e
    have h3 := hy.st
    rw [e, tsVals.2.2.1] at h3
    revert hrb h3
    cases tcb.tcbState <;> simp [tsCode, Fl4Spec.receiveBlocked]
  have hnvm : L.mem s (tStA (L.mem s (nBoundA n))) ≠ sched.TS_RUNNING_VM := by
    intro e
    have h3 := hy.st
    rw [e] at h3
    simp only [sched.TS_RUNNING_VM] at h3
    cases hst : tcb.tcbState <;> simp_all [tsCode]
  unfold notification.send_signal
  step
  have : st = obj.NTFN_IDLE := by rw [st_post]; exact stOf_idle hx.obj hidle
  simp only [this, ↓reduceIte]
  step
  step
  simp only [b_post, i_post, hb0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step
  have hns2 : i1 ≠ sched.TS_BLOCKED_ON_RECV := by rw [i1_post]; exact hns
  simp only [hns2, ↓reduceIte]
  step
  subst s1_post
  obtain ⟨hR', hW⟩ := set_active_relI hP hR hn hk hidle badge
  have hst' : L.mem (L.wr (L.wr s (epTSA n)
      ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64))) (nBadgeA n) badge)
      (tStA (L.mem s (nBoundA n))) = L.mem s (tStA (L.mem s (nBoundA n))) := by
    have h1 := nwr_wr (L := L) hP.n (K := 8#u64) hn (by simp) (by simp) s
      ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64))
    rw [← epTSA_eq] at h1
    have h2 := nwr_wr (L := L) hP.n (K := 16#u64) hn (by simp) (by simp)
      (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64))) badge
    rw [← nBadgeA_eq] at h2
    exact ((h1.trans h2).tcb _ hbT).1.st
  step with Notif.obj.Tcb.state.spec as ⟨vm_state, hvs⟩
  simp only [hvs, hst', hnvm, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
  exact ⟨trivial, _, sendSignal_activate hk hidle (Or.inr ⟨t, tcb, hb, hkt, hrb⟩) badge.bv, hR',
    NtfnStep.ntfn hk rfl rfl, hW⟩

/-- **Active**: the badge is OR-ed into the pending one. -/
theorem send_signal_activeI (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : IpcRel N T E R B (L.mem s) σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r =>
      r.2 = a ∧ SingleRelI (st := st) N T E R B s σ (Fl4Spec.sendSignal n.bv badge.bv σ) r.1 ⦄ := by
  have hx := hR.toN.at_ntfn hn hk
  have hb0 : (L.mem s (nBadgeA n)).bv = b0 := by
    have := hx.obj; rw [hact] at this; exact this.2.2
  unfold notification.send_signal
  step
  have : st = obj.NTFN_ACTIVE := by rw [st_post]; exact stOf_active hx.obj hact
  simp only [this, ntfn_consts.1, ntfn_consts.2.1, ntfn_consts.2.2]
  simp only [show (2#u64 : U64) ≠ 0#u64 by decide, show (2#u64 : U64) ≠ 1#u64 by decide, ↓reduceIte]
  step
  step
  step
  subst s1_post
  obtain ⟨hR', hW⟩ := set_badge_relI hP hR hn hk hact b
  have e : b.bv = Fl4Spec.combineNtfnBadges badge.bv b0 := by
    have h := b_post1
    rw [i_post] at h
    exact h.trans ((BitVec.or_comm _ _).trans (congrArg (badge.bv ||| ·) hb0))
  rw [e] at hR'
  exact ⟨_, sendSignal_active_eq hk hact badge.bv, hR', NtfnStep.ntfn hk rfl rfl, hW⟩

end

end

end Fl4Proofs.P3.Ipc
