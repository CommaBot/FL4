/-
P3 (DESIGN.md §9), CSpace: **the spec's finalisation of a final scheduling
context cap has an outcome** (`finSc_out`, `specFinOut_sc`: the
SchedContext case of `SpecFinOut`), from `ScFinPre`: the SC exists, its
links (thread, notification, head reply, yield-from thread and that
thread's yield-to SC) are objects of their kinds, and `ActReady` (for
`sched_context_unbind_tcb`'s reschedule).

The steps (`unbindTcb_out`, `unbindNtfnSc_out`, `unbindReply_out`,
`completeYieldTo_out`, `setInactive_out`) with the frames `KF` (kinds,
thread states, queues and the reply links kept; yield links kept or cut)
and `KFy` (TCBs and SCs as such, the yield links kept or cut).
-/
import Fl4Proofs.P3.SchedValid
import Fl4Proofs.P3.EpMrs
import Fl4Proofs.P3.EpFaultNone
import Fl4Proofs.P3.EpXferSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section Spec
open Fl4Spec Classical

/-! ### Frames -/

/-- What the unbinds keep: every TCB's state (its yield-to kept or cut),
every SC's size and stack (its yield-from kept or cut), every
notification's queue, every reply's links, every endpoint. -/
structure KF (σ σ' : State Unit) : Prop where
  tcb : ∀ p x, σ.kheap p = some (.tcb x) → ∃ x', σ'.kheap p = some (.tcb x') ∧ x'.tcbState = x.tcbState ∧
    (x'.tcbYieldTo = x.tcbYieldTo ∨ x'.tcbYieldTo = none)
  sc : ∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ y', σ'.kheap p = some (.schedContext y' n) ∧
    y'.scReplies = y.scReplies ∧ (y'.scYieldFrom = y.scYieldFrom ∨ y'.scYieldFrom = none)
  ntfn : ∀ p x, σ.kheap p = some (.notification x) → ∃ x', σ'.kheap p = some (.notification x') ∧
    x'.ntfnObj = x.ntfnObj
  reply : ∀ p x, σ.kheap p = some (.reply x) → ∃ x', σ'.kheap p = some (.reply x') ∧
    x'.replyTcb = x.replyTcb ∧ x'.replySc = x.replySc
  ep : ∀ p x, σ.kheap p = some (.endpoint x) → σ'.kheap p = some (.endpoint x)
  sc' : ∀ p y n, σ'.kheap p = some (.schedContext y n) → ∃ y0, σ.kheap p = some (.schedContext y0 n) ∧
    y.scReplies = y0.scReplies

theorem KF.heq {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : KF σ σ' :=
  ⟨fun _ x hp => ⟨x, by rw [h]; exact hp, rfl, Or.inl rfl⟩, fun _ y _ hp => ⟨y, by rw [h]; exact hp, rfl, Or.inl rfl⟩,
    fun _ x hp => ⟨x, by rw [h]; exact hp, rfl⟩, fun _ x hp => ⟨x, by rw [h]; exact hp, rfl, rfl⟩,
    fun _ _ hp => by rw [h]; exact hp, fun _ y _ hp => ⟨y, by rw [← h]; exact hp, rfl⟩⟩

theorem KF.trans {σ1 σ2 σ3 : State Unit} (h1 : KF σ1 σ2) (h2 : KF σ2 σ3) : KF σ1 σ3 := by
  refine ⟨fun p x hp => ?_, fun p y n hp => ?_, fun p x hp => ?_, fun p x hp => ?_,
    fun p x hp => h2.ep p x (h1.ep p x hp), fun p y n hp => ?_⟩
  · obtain ⟨x1, h1', e1, f1⟩ := h1.tcb p x hp
    obtain ⟨x2, h2', e2, f2⟩ := h2.tcb p x1 h1'
    refine ⟨x2, h2', e2.trans e1, ?_⟩
    rcases f2 with f2 | f2
    · rw [f2]; exact f1
    · exact Or.inr f2
  · obtain ⟨y1, h1', e1, f1⟩ := h1.sc p y n hp
    obtain ⟨y2, h2', e2, f2⟩ := h2.sc p y1 n h1'
    refine ⟨y2, h2', e2.trans e1, ?_⟩
    rcases f2 with f2 | f2
    · rw [f2]; exact f1
    · exact Or.inr f2
  · obtain ⟨x1, h1', e1⟩ := h1.ntfn p x hp
    obtain ⟨x2, h2', e2⟩ := h2.ntfn p x1 h1'
    exact ⟨x2, h2', e2.trans e1⟩
  · obtain ⟨x1, h1', e1, f1⟩ := h1.reply p x hp
    obtain ⟨x2, h2', e2, f2⟩ := h2.reply p x1 h1'
    exact ⟨x2, h2', e2.trans e1, f2.trans f1⟩
  · obtain ⟨y1, h1', e1⟩ := h2.sc' p y n hp
    obtain ⟨y0, h0', e0⟩ := h1.sc' p y1 n h1'
    exact ⟨y0, h0', e1.trans e0⟩

theorem KF.uTcb {σ : State Unit} {p : ObjRef} {x x' : Tcb} (hk : σ.kheap p = some (.tcb x))
    (e1 : x'.tcbState = x.tcbState) (e2 : x'.tcbYieldTo = x.tcbYieldTo ∨ x'.tcbYieldTo = none) :
    KF σ (updK σ p (.tcb x')) := by
  have ne : ∀ q o, σ.kheap q = some o → (∀ y, o ≠ .tcb y) → (updK σ p (.tcb x')).kheap q = some o := by
    intro q o hq ho
    have hne : q ≠ p := by rintro rfl; rw [hk] at hq; exact ho x (Option.some.inj hq).symm
    simp only [updK, Function.update_of_ne hne]; exact hq
  refine ⟨fun q y hq => ?_, fun q y n hq => ⟨y, ne q _ hq (fun _ h => by cases h), rfl, Or.inl rfl⟩,
    fun q y hq => ⟨y, ne q _ hq (fun _ h => by cases h), rfl⟩,
    fun q y hq => ⟨y, ne q _ hq (fun _ h => by cases h), rfl, rfl⟩, fun q y hq => ne q _ hq (fun _ h => by cases h),
    fun q y m hq => ⟨y, ?_, rfl⟩⟩
  rotate_left
  · have hne : q ≠ p := by rintro rfl; simp [updK] at hq
    simp only [updK, Function.update_of_ne hne] at hq; exact hq
  by_cases hne : q = p
  · subst hne; rw [hk] at hq; cases hq; exact ⟨x', by simp [updK], e1, e2⟩
  · exact ⟨y, by simp only [updK, Function.update_of_ne hne]; exact hq, rfl, Or.inl rfl⟩

theorem KF.uSc {σ : State Unit} {p : ObjRef} {y z : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (e1 : z.scReplies = y.scReplies)
    (e2 : z.scYieldFrom = y.scYieldFrom ∨ z.scYieldFrom = none) : KF σ (updSc σ p z n) := by
  have ne : ∀ q o, σ.kheap q = some o → (∀ y m, o ≠ .schedContext y m) → (updSc σ p z n).kheap q = some o := by
    intro q o hq ho
    have hne : q ≠ p := by rintro rfl; rw [hk] at hq; exact ho y n (Option.some.inj hq).symm
    simp only [updSc, updK, Function.update_of_ne hne]; exact hq
  refine ⟨fun q x hq => ⟨x, ne q _ hq (fun _ _ h => by cases h), rfl, Or.inl rfl⟩, fun q y' m hq => ?_,
    fun q x hq => ⟨x, ne q _ hq (fun _ _ h => by cases h), rfl⟩,
    fun q x hq => ⟨x, ne q _ hq (fun _ _ h => by cases h), rfl, rfl⟩, fun q x hq => ne q _ hq (fun _ _ h => by cases h),
    fun q y' m hq => ?_⟩
  rotate_left
  · by_cases hne : q = p
    · subst hne; simp [updSc, updK] at hq; obtain ⟨rfl, rfl⟩ := hq; exact ⟨y, hk, e1⟩
    · simp only [updSc, updK, Function.update_of_ne hne] at hq; exact ⟨y', hq, rfl⟩
  by_cases hne : q = p
  · subst hne; rw [hk] at hq; cases hq; exact ⟨z, by simp [updSc, updK], e1, e2⟩
  · exact ⟨y', by simp only [updSc, updK, Function.update_of_ne hne]; exact hq, rfl, Or.inl rfl⟩

theorem KF.uNtfn {σ : State Unit} {p : ObjRef} {x x' : Notification} (hk : σ.kheap p = some (.notification x))
    (e : x'.ntfnObj = x.ntfnObj) : KF σ (updK σ p (.notification x')) := by
  have ne : ∀ q o, σ.kheap q = some o → (∀ y, o ≠ .notification y) →
      (updK σ p (.notification x')).kheap q = some o := by
    intro q o hq ho
    have hne : q ≠ p := by rintro rfl; rw [hk] at hq; exact ho x (Option.some.inj hq).symm
    simp only [updK, Function.update_of_ne hne]; exact hq
  refine ⟨fun q y hq => ⟨y, ne q _ hq (fun _ h => by cases h), rfl, Or.inl rfl⟩,
    fun q y m hq => ⟨y, ne q _ hq (fun _ h => by cases h), rfl, Or.inl rfl⟩, fun q y hq => ?_,
    fun q y hq => ⟨y, ne q _ hq (fun _ h => by cases h), rfl, rfl⟩, fun q y hq => ne q _ hq (fun _ h => by cases h),
    fun q y m hq => ⟨y, ?_, rfl⟩⟩
  rotate_left
  · have hne : q ≠ p := by rintro rfl; simp [updK] at hq
    simp only [updK, Function.update_of_ne hne] at hq; exact hq
  by_cases hne : q = p
  · subst hne; rw [hk] at hq; cases hq; exact ⟨x', by simp [updK], e⟩
  · exact ⟨y, by simp only [updK, Function.update_of_ne hne]; exact hq, rfl⟩

/-- What the yield steps need: TCBs and SCs as such, the yield links kept or
cut. -/
structure KFy (σ σ' : State Unit) : Prop where
  tcb : ∀ p x, σ.kheap p = some (.tcb x) → ∃ x', σ'.kheap p = some (.tcb x') ∧
    (x'.tcbYieldTo = x.tcbYieldTo ∨ x'.tcbYieldTo = none)
  sc : ∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ y', σ'.kheap p = some (.schedContext y' n) ∧
    (y'.scYieldFrom = y.scYieldFrom ∨ y'.scYieldFrom = none)

theorem KF.kfy {σ σ' : State Unit} (h : KF σ σ') : KFy σ σ' :=
  ⟨fun p x hp => by obtain ⟨x', h1, -, h3⟩ := h.tcb p x hp; exact ⟨x', h1, h3⟩,
    fun p y n hp => by obtain ⟨y', h1, -, h3⟩ := h.sc p y n hp; exact ⟨y', h1, h3⟩⟩

theorem KFy.trans {σ1 σ2 σ3 : State Unit} (h1 : KFy σ1 σ2) (h2 : KFy σ2 σ3) : KFy σ1 σ3 := by
  refine ⟨fun p x hp => ?_, fun p y n hp => ?_⟩
  · obtain ⟨x1, h1', f1⟩ := h1.tcb p x hp
    obtain ⟨x2, h2', f2⟩ := h2.tcb p x1 h1'
    refine ⟨x2, h2', ?_⟩
    rcases f2 with f2 | f2
    · rw [f2]; exact f1
    · exact Or.inr f2
  · obtain ⟨y1, h1', f1⟩ := h1.sc p y n hp
    obtain ⟨y2, h2', f2⟩ := h2.sc p y1 n h1'
    refine ⟨y2, h2', ?_⟩
    rcases f2 with f2 | f2
    · rw [f2]; exact f1
    · exact Or.inr f2

/-! ### The message and yield steps -/

/-- **`reply_from_kernel` of a one-word message**: only the thread's user
context changes. -/
theorem replyFromKernel_out {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (l w : Word) :
    ∃ σ', replyFromKernel (Z := Unit) t (l, [w]) σ = ({((), σ')}, False) ∧
      (∃ x', σ'.kheap t = some (.tcb x') ∧ x' = { x with tcbArch := x'.tcbArch }) ∧
      ∀ p, p ≠ t → σ'.kheap p = σ.kheap p := by
  unfold replyFromKernel
  rw [nd_pure_bind']
  dsimp only
  rw [nd_bind_one (lookupIpcBuffer_eq hk true), nd_bind_one (asUser_setRegister_eq _ _ hk)]
  set x1 := setReg x badge_register 0 with hx1
  have hk1 : (updK σ t (.tcb x1)).kheap t = some (.tcb x1) := by simp [updK]
  have fin : ∀ σ2 : State Unit, (∀ p, p ≠ t → σ2.kheap p = σ.kheap p) → ∀ x2 : Tcb,
      σ2.kheap t = some (.tcb x2) → x2 = { x with tcbArch := x2.tcbArch } → ∀ v,
      ∃ σ', setMessageInfo (Z := Unit) t v σ2 = ({((), σ')}, False) ∧
        (∃ x', σ'.kheap t = some (.tcb x') ∧ x' = { x with tcbArch := x'.tcbArch }) ∧
        ∀ p, p ≠ t → σ'.kheap p = σ.kheap p := by
    intro σ2 hp2 x2 hk2 hx2 v
    refine ⟨_, asUser_setRegister_eq _ _ hk2, ⟨setReg x2 msg_info_register (messageInfoToData v), by simp [updK], ?_⟩, fun p hp => ?_⟩
    · rw [hx2]; rfl
    · simp only [updK, Function.update_of_ne hp]; exact hp2 p hp
  cases hb : ipcBufOf true x with
  | none =>
    rw [nd_bind_one (setMrs_eqN hk1 _)]
    refine fin _ (fun p hp => ?_) (withRegs x1 (mrRegs x1.tcbArch.tcbContext.userRegs [w])) (by simp [mrStateN, updK]) rfl _
    simp only [mrStateN, updK, Function.update_of_ne hp]
  | some q =>
    rw [nd_bind_one (setMrs_eq hk1 q [w] (fun z hz => by simp [mrPairs] at hz))]
    refine fin _ (fun p hp => ?_) (withRegs x1 (mrRegs x1.tcbArch.tcbContext.userRegs [w])) (by simp [mrState, setUm, updK]) rfl _
    simp only [mrState, setUm, updK, Function.update_of_ne hp]


theorem KF.ofArch {σ σ' : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (h1 : ∃ x', σ'.kheap t = some (.tcb x') ∧ x' = { x with tcbArch := x'.tcbArch })
    (h2 : ∀ p, p ≠ t → σ'.kheap p = σ.kheap p) : KF σ σ' := by
  obtain ⟨x', hk', hx'⟩ := h1
  have e : σ'.kheap = (updK σ t (.tcb x')).kheap := by
    funext p
    by_cases hp : p = t
    · subst hp; rw [hk']; simp [updK]
    · rw [h2 p hp]; simp only [updK, Function.update_of_ne hp]
  exact (KF.uTcb hk (by rw [hx']) (Or.inl (by rw [hx']))).trans (KF.heq e)

/-- **`set_consumed`**: the SC's consumed time and the thread's registers;
every TCB's yield-to kept. -/
theorem setConsumed_out {σ : State Unit} {p t : ObjRef} {y : SchedContext} {n : Nat} {x : Tcb}
    (hks : σ.kheap p = some (.schedContext y n)) (hkt : σ.kheap t = some (.tcb x)) :
    ∃ σ', setConsumed (Z := Unit) p t σ = ({((), σ')}, False) ∧ KF σ σ' ∧
      ∀ q xq, σ.kheap q = some (.tcb xq) → ∃ x', σ'.kheap q = some (.tcb x') ∧ x'.tcbYieldTo = xq.tcbYieldTo := by
  have hpt : t ≠ p := by rintro rfl; rw [hkt] at hks; cases hks
  obtain ⟨c, v, hv⟩ : ∃ c v, schedContextUpdateConsumed (Z := Unit) p σ =
      ({(c, updSc σ p (scConsumedUpdate (fun _ => v) y) n)}, False) := by
    unfold schedContextUpdateConsumed
    rw [nd_bind_one (getSchedContext_eq hks), nd_pure_bind']
    split_ifs
    · rw [nd_bind_one (updateSchedContext_eq hks _)]; exact ⟨_, _, rfl⟩
    · rw [nd_bind_one (updateSchedContext_eq hks _)]; exact ⟨_, _, rfl⟩
  set σ1 := updSc σ p (scConsumedUpdate (fun _ => v) y) n with hσ1
  have hF1 : KF σ σ1 := KF.uSc hks rfl (Or.inl rfl)
  have hkp1 : ∀ q, q ≠ p → σ1.kheap q = σ.kheap q := fun q hq => by
    simp only [hσ1, updSc, updK, Function.update_of_ne hq]
  have hkt1 : σ1.kheap t = some (.tcb x) := by rw [hkp1 t hpt]; exact hkt
  obtain ⟨σ2, h2, ⟨x2, hk2, hx2⟩, h2b⟩ := replyFromKernel_out hkt1 0 (ucast 64 c)
  unfold setConsumed
  rw [nd_bind_one hv]
  refine ⟨σ2, h2, hF1.trans (KF.ofArch hkt1 ⟨x2, hk2, hx2⟩ h2b), fun q xq hq => ?_⟩
  have hqp : q ≠ p := by rintro rfl; rw [hks] at hq; cases hq
  by_cases hqt : q = t
  · subst hqt; rw [hkt] at hq; cases hq; exact ⟨x2, hk2, by rw [hx2]⟩
  · exact ⟨xq, by rw [h2b q hqt, hkp1 q hqp]; exact hq, rfl⟩

/-- **`complete_yield_to`** of a TCB whose yield-to SC (if any) exists. -/
theorem completeYieldTo_out {σ : State Unit} {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x))
    (hy : ∀ p, x.tcbYieldTo = some p → ∃ y n, σ.kheap p = some (.schedContext y n)) :
    ∃ σ', completeYieldTo (Z := Unit) t σ = ({((), σ')}, False) ∧ KF σ σ' := by
  cases hyt : x.tcbYieldTo with
  | none => exact ⟨σ, completeYieldTo_none hkt hyt, KF.heq rfl⟩
  | some p =>
    obtain ⟨y, n, hks⟩ := hy p hyt
    have hpt : p ≠ t := by rintro rfl; rw [hkt] at hks; cases hks
    rw [completeYieldTo_some hkt hyt]
    obtain ⟨σ1, h1, hF1, hyk⟩ := setConsumed_out hks hkt
    rw [nd_bind_one h1]
    obtain ⟨x1, hkt1, hyt1⟩ := hyk t x hkt
    obtain ⟨y1, hks1, -, -⟩ := hF1.sc p y n hks
    obtain ⟨x1', hkt1', hs1, -⟩ := hF1.tcb t x hkt
    rw [hkt1] at hkt1'; cases hkt1'
    rw [cancelYieldTo_some hkt1 (by rw [hyt1, hyt]) hks1 hpt]
    refine ⟨_, rfl, hF1.trans ((KF.uSc (z := { y1 with scYieldFrom := none }) hks1 rfl (Or.inr rfl)).trans
      (KF.uTcb (x := x1) (x' := { x1 with tcbYieldTo := none }) ?_ rfl (Or.inr rfl)))⟩
    simp only [updSc, updK, Function.update_of_ne (Ne.symm hpt)]; exact hkt1

/-- **`sched_context_unbind_tcb`**, from `ActReady` (its reschedule). -/
theorem unbindTcb_out {σ : State Unit} {sc t : ObjRef} {y : SchedContext} {k : Nat} {x : Tcb}
    (hks : σ.kheap sc = some (.schedContext y k)) (hy : y.scTcb = some t) (hkt : σ.kheap t = some (.tcb x))
    (hA : ActReady σ) :
    ∃ σ', ((), σ') ∈ (schedContextUnbindTcb (Z := Unit) sc σ).1 ∧ KF σ σ' ∧
      σ'.kheap sc = some (.schedContext (scTcbUpdate (fun _ => none) y) k) := by
  have hts : t ≠ sc := by rintro rfl; rw [hkt] at hks; cases hks
  unfold schedContextUnbindTcb
  rw [nd_bind_one (getSchedContext_eq hks), hy,
    nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some t) σ = ({(t, σ)}, False) from rfl),
    Notif.nd_gets_bind]
  unfold NonDet.when
  obtain ⟨σ0, he0, hk0⟩ := when_resched hA (t = σ.curThread)
  rw [nd_bind_one he0]
  have hkt0 : σ0.kheap t = some (.tcb x) := by rw [hk0]; exact hkt
  rw [nd_bind_one (tcbSchedAction_gen hkt0 _)]
  obtain ⟨σ2, h2, hk2, -, -, -⟩ := tcbReleaseRemove_out (setQ σ0 x.tcbDomain x.tcbPriority
    (tcbSchedDequeue t (σ0.readyQueues x.tcbDomain x.tcbPriority))) t
  rw [nd_bind_one h2]
  have hk2' : σ2.kheap = σ.kheap := by rw [hk2]; exact hk0
  have hkt2 : σ2.kheap t = some (.tcb x) := by rw [hk2']; exact hkt
  rw [nd_bind_one (show setTcbObjRef (Z := Unit) tcbSchedContextUpdate t none σ2 = _ from threadSet_eq _ hkt2)]
  have hks3 : (updK σ2 t (.tcb (tcbSchedContextUpdate (fun _ => none) x))).kheap sc = some (.schedContext y k) := by
    simp only [updK, Function.update_of_ne (Ne.symm hts)]; rw [hk2']; exact hks
  have e4 : setScObjRef (Z := Unit) scTcbUpdate sc none (updK σ2 t (.tcb (tcbSchedContextUpdate (fun _ => none) x))) =
      ({((), updSc (updK σ2 t (.tcb (tcbSchedContextUpdate (fun _ => none) x))) sc
        (scTcbUpdate (fun _ => none) y) k)}, False) := updateSchedContext_eq hks3 _
  rw [e4]
  refine ⟨_, Set.mem_singleton _, (KF.heq hk2').trans ((KF.uTcb (x' := tcbSchedContextUpdate (fun _ => none) x) hkt2 rfl (Or.inl rfl)).trans
    (KF.uSc (z := scTcbUpdate (fun _ => none) y) hks3 rfl (Or.inl rfl))), by simp [updSc, updK]⟩

/-- **`sched_context_unbind_ntfn`**. -/
theorem unbindNtfnSc_out {σ : State Unit} {sc : ObjRef} {y : SchedContext} {k : Nat}
    (hks : σ.kheap sc = some (.schedContext y k)) (hn : ∀ n, y.scNtfn = some n → ∃ x, σ.kheap n = some (.notification x)) :
    ∃ σ', schedContextUnbindNtfn (Z := Unit) sc σ = ({((), σ')}, False) ∧ KF σ σ' := by
  unfold schedContextUnbindNtfn
  rw [nd_bind_one (getScObjRef_eq hks _)]
  cases hyn : y.scNtfn with
  | none => exact ⟨σ, rfl, KF.heq rfl⟩
  | some n =>
    obtain ⟨xn, hkn⟩ := hn n hyn
    have hns : n ≠ sc := by rintro rfl; rw [hkn] at hks; cases hks
    show ∃ σ', (setNtfnObjRef (Z := Unit) ntfnScUpdate n none >>= fun _ => setScObjRef scNtfnUpdate sc none) σ = _ ∧ _
    rw [nd_bind_one (updateSkObjRef_ntfn_eq hkn _ none)]
    have hks1 : (updK σ n (.notification (ntfnScUpdate (fun _ => none) xn))).kheap sc = some (.schedContext y k) := by
      simp only [updK, Function.update_of_ne (Ne.symm hns)]; exact hks
    exact ⟨_, updateSchedContext_eq hks1 _, (KF.uNtfn (x' := ntfnScUpdate (fun _ => none) xn) hkn rfl).trans (KF.uSc (z := scNtfnUpdate (fun _ => none) y) hks1 rfl (Or.inl rfl))⟩

theorem KFy.uReply {σ : State Unit} {p : ObjRef} {x x' : Reply} (hk : σ.kheap p = some (.reply x)) :
    KFy σ (updK σ p (.reply x')) := by
  refine ⟨fun q y hq => ⟨y, ?_, Or.inl rfl⟩, fun q y n hq => ⟨y, ?_, Or.inl rfl⟩⟩
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    simp only [updK, Function.update_of_ne hne]; exact hq
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    simp only [updK, Function.update_of_ne hne]; exact hq

theorem KFy.uSc {σ : State Unit} {p : ObjRef} {y z : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (e : z.scYieldFrom = y.scYieldFrom) : KFy σ (updSc σ p z n) := by
  refine ⟨fun q x hq => ⟨x, ?_, Or.inl rfl⟩, fun q y' m hq => ?_⟩
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    simp only [updSc, updK, Function.update_of_ne hne]; exact hq
  · by_cases hne : q = p
    · subst hne; rw [hk] at hq; cases hq; exact ⟨z, by simp [updSc, updK], Or.inl e⟩
    · exact ⟨y', by simp only [updSc, updK, Function.update_of_ne hne]; exact hq, Or.inl rfl⟩

/-- **`sched_context_unbind_reply`**. -/
theorem unbindReply_out {σ : State Unit} {sc : ObjRef} {y : SchedContext} {k : Nat}
    (hks : σ.kheap sc = some (.schedContext y k))
    (hr : ∀ r, y.scReplies.head? = some r → ∃ x, σ.kheap r = some (.reply x)) :
    ∃ σ', schedContextUnbindReply (Z := Unit) sc σ = ({((), σ')}, False) ∧ KFy σ σ' := by
  unfold schedContextUnbindReply
  rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hks) _)]
  unfold NonDet.unless
  cases hl : y.scReplies with
  | nil => exact ⟨σ, by rw [if_pos rfl]; rfl, (KF.heq rfl).kfy⟩
  | cons r l =>
    obtain ⟨xr, hkr⟩ := hr r (by rw [hl]; rfl)
    have hrs : r ≠ sc := by rintro rfl; rw [hkr] at hks; cases hks
    rw [if_neg (by simp)]
    show ∃ σ', (setReplyObjRef (Z := Unit) replyScUpdate r none >>= fun _ => setScObjRef scRepliesUpdate sc []) σ = _ ∧ _
    rw [nd_bind_one (setReplySc_eq none hkr)]
    have hks1 : (updK σ r (.reply { xr with replySc := none })).kheap sc = some (.schedContext y k) := by
      simp only [updK, Function.update_of_ne (Ne.symm hrs)]; exact hks
    exact ⟨_, updateSchedContext_eq hks1 _, (KFy.uReply hkr).trans (KFy.uSc hks1 rfl)⟩

/-- **`sched_context_set_inactive`**. -/
theorem setInactive_out {σ : State Unit} {sc : ObjRef} {y : SchedContext} {k : Nat}
    (hks : σ.kheap sc = some (.schedContext y k)) :
    ∃ σ', ((), σ') ∈ (schedContextSetInactive (Z := Unit) sc σ).1 := by
  have us : ∀ (σ0 : State Unit) (z : SchedContext), (updSc σ0 sc z k).kheap sc = some (.schedContext z k) :=
    fun σ0 z => by simp [updSc, updK]
  unfold schedContextSetInactive
  rw [nd_bind_one (updateSchedContext_eq hks _), nd_bind_one (updateSchedContext_eq (us _ _) _),
    nd_bind_one (updateSchedContext_eq (us _ _) _), updateSchedContext_eq (us _ _)]
  exact ⟨_, Set.mem_singleton _⟩


theorem mem_of_eq {α : Type} {m : NonDet (State Unit) α} {σ σ' : State Unit} {a : α}
    (h : m σ = ({(a, σ')}, False)) : (a, σ') ∈ (m σ).1 := by rw [h]; exact Set.mem_singleton _

/-- **What the finalisation of an SC cap needs of the spec state**: the SC
exists, its thread, notification, head reply and yield-from thread are
objects of their kinds, the yield-from thread's yield-to SC exists, and
`ActReady`. -/
def ScFinPre (σ : State Unit) (sc : ObjRef) : Prop :=
  ∃ y k, σ.kheap sc = some (.schedContext y k) ∧ ActReady σ ∧
    (∀ t, y.scTcb = some t → ∃ x, σ.kheap t = some (.tcb x)) ∧
    (∀ n, y.scNtfn = some n → ∃ x, σ.kheap n = some (.notification x)) ∧
    (∀ r, y.scReplies.head? = some r → ∃ x, σ.kheap r = some (.reply x)) ∧
    (∀ t, y.scYieldFrom = some t → ∃ x, σ.kheap t = some (.tcb x) ∧
      ∀ p, x.tcbYieldTo = some p → ∃ y' n, σ.kheap p = some (.schedContext y' n))

/-- **`sched_context_unbind_all_tcbs`**. -/
theorem unbindAll_out {σ : State Unit} {sc : ObjRef} {y : SchedContext} {k : Nat}
    (hks : σ.kheap sc = some (.schedContext y k)) (hA : ActReady σ)
    (ht : ∀ t, y.scTcb = some t → ∃ x, σ.kheap t = some (.tcb x)) :
    ∃ σ1 y1, ((), σ1) ∈ (schedContextUnbindAllTcbs (Z := Unit) sc σ).1 ∧ KF σ σ1 ∧
      σ1.kheap sc = some (.schedContext y1 k) ∧ y1.scNtfn = y.scNtfn := by
  unfold schedContextUnbindAllTcbs
  rw [nd_bind_one (getSchedContext_eq hks), Notif.nd_gets_bind]
  unfold NonDet.when
  split_ifs with hc
  · obtain ⟨t, hy⟩ := Option.ne_none_iff_exists'.1 hc.1
    obtain ⟨x, hkt⟩ := ht t hy
    obtain ⟨σ1, h1, hF1, hk1⟩ := unbindTcb_out hks hy hkt hA
    exact ⟨σ1, _, h1, hF1, hk1, rfl⟩
  · exact ⟨σ, y, Set.mem_singleton _, KF.heq rfl, hks, rfl⟩

/-- **The spec's finalisation of a final SC cap has an outcome.** -/
theorem finSc_out {σ : State Unit} {sc : ObjRef} (b : Nat) (h : ScFinPre σ sc) :
    ∃ σ', ((Cap.nullCap, Cap.nullCap), σ') ∈ (finaliseCap (Z := Unit) (.schedContextCap sc b) true σ).1 := by
  obtain ⟨y, k, hks, hA, ht, hn, hr, hyf⟩ := h
  obtain ⟨σ1, y1, h1, hF1, hks1, hn1⟩ := unbindAll_out hks hA ht
  obtain ⟨σ2, h2, hF2⟩ := unbindNtfnSc_out hks1 (fun n e => by
    obtain ⟨x, hx⟩ := hn n (by rw [← hn1]; exact e)
    obtain ⟨x', hx', -⟩ := hF1.ntfn n x hx
    exact ⟨x', hx'⟩)
  have hF12 := hF1.trans hF2
  obtain ⟨y2, hks2, hrp2, -⟩ := hF12.sc sc y k hks
  obtain ⟨σ3, h3, hF3⟩ := unbindReply_out hks2 (fun r e => by
    obtain ⟨x, hx⟩ := hr r (by rw [← hrp2]; exact e)
    obtain ⟨x', hx', -⟩ := hF12.reply r x hx
    exact ⟨x', hx'⟩)
  have hFy := hF12.kfy.trans hF3
  obtain ⟨y3, hks3, hyf3⟩ := hFy.sc sc y k hks
  -- the yield-from step
  have h4 : ∃ σ4, ((), σ4) ∈ (schedContextUnbindYieldFrom (Z := Unit) sc σ3).1 ∧ KF σ3 σ4 := by
    unfold schedContextUnbindYieldFrom
    rw [nd_bind_one (getSchedContext_eq hks3)]
    cases hyt : y3.scYieldFrom with
    | none => exact ⟨σ3, Set.mem_singleton _, KF.heq rfl⟩
    | some t =>
      have hy0 : y.scYieldFrom = some t := by
        rcases hyf3 with e | e
        · rw [← e, hyt]
        · rw [hyt] at e; cases e
      obtain ⟨x, hkt, hyp⟩ := hyf t hy0
      obtain ⟨x3, hkt3, hyt3⟩ := hFy.tcb t x hkt
      obtain ⟨σ4, e4, hF4⟩ := completeYieldTo_out hkt3 (fun p e => by
        have e' : x.tcbYieldTo = some p := by
          rcases hyt3 with e3 | e3
          · rw [← e3, e]
          · rw [e] at e3; cases e3
        obtain ⟨y', n, hkp⟩ := hyp p e'
        obtain ⟨y'', hkp', -⟩ := hFy.sc p y' n hkp
        exact ⟨y'', n, hkp'⟩)
      exact ⟨σ4, mem_of_eq e4, hF4⟩
  obtain ⟨σ4, hm4, hF4⟩ := h4
  obtain ⟨y4, hks4, -, -⟩ := hF4.sc sc y3 k hks3
  obtain ⟨σ5, hm5⟩ := setInactive_out hks4
  refine ⟨σ5, ?_⟩
  unfold finaliseCap
  simp only [NonDet.when, ↓reduceIte]
  exact mem_bind_nd h1 (mem_bind_nd (mem_of_eq h2) (mem_bind_nd (mem_of_eq h3) (mem_bind_nd hm4
    (mem_bind_nd hm5 (Set.mem_singleton _)))))

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Notif

section Spec
open Fl4Spec

theorem scFinPre_of_valid {σ : State Unit} {sc : ObjRef} (hA : ActReady σ) (hV : SchedValid σ)
    (ho : ∃ y k, σ.kheap sc = some (.schedContext y k)) : ScFinPre σ sc := by
  obtain ⟨y, k, hks⟩ := ho
  refine ⟨y, k, hks, hA, fun t e => hV.scTcb sc y k t hks e, fun n e => hV.scNtfn sc y k n hks e,
    fun r e => ?_, fun t e => ?_⟩
  · obtain ⟨xr, hkr, -⟩ := hV.replies sc y k r hks (List.mem_of_mem_head? e)
    exact ⟨xr, hkr⟩
  · obtain ⟨x, hkt, -⟩ := hV.scYieldFrom sc y k t hks e
    exact ⟨x, hkt, fun p ep => hV.tcbYieldTo t x p hkt ep⟩

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`SpecFinOut` for the SC caps**, from the scheduling invariants and
`valid_cap` at related states. -/
theorem specFinOut_sc (th : TypedHeap) (hC : SchedCoupling (L := L) th) (hO : CapObjHyp (L := L) th) :
    SpecFinOut (L := L) FinScK th := by
  intro s σ G sl c hk hDS hA hc _
  obtain ⟨p, x, rfl⟩ := hk
  obtain ⟨-, hAR, hV⟩ := hC s σ G hDS
  exact finSc_out _ (scFinPre_of_valid hAR hV (hO s σ G sl _ hDS hA hc))

end

end Fl4Proofs.P3.Sched
