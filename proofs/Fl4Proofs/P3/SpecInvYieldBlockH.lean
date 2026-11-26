/-
P3 (DESIGN.md §9), invariant line YB (iolay gen 5): **YieldBlock kept by the syscall entry and by every kernel
event** (spec side only): the hand-proved functions (`proofs/scratch/invA/skipYB.txt`: skipYS's and every function
reaching a blocking writer) and the tops.

* The blocking writers, for a thread of `L`: `sendIpcBlocked`, `receiveIpcBlocked`, `receiveSignalBlocked`,
  `replyPush` (`yb_setThreadState`'s `t ∈ L`), and their callers for a thread of `L`: `sendIpc`, `sendFaultIpc`,
  `handleTimeout`, `handleFault`, `receiveSignal`. A thread *read* blocked does not yield (`ybl_cons_read`), so
  `receiveIpc`'s queued sender (made `blockedOnReply` by `replyPush`) and `doReplyTransfer`'s receiver (sent a timeout
  fault) join `L` at their state read (`ybw_rds`).
* The budget functions block the *current* thread (`endTimeslice` → `handleTimeout ct`): they run in
  `YC L := YBL L ∧ curThread ∈ L` (the current thread kept by the generic frame, `yc_of`): `endTimeslice`,
  `chargeBudget`, `checkBudget`, `checkBudgetRestart`, `handleYield`, `preemptionPath`.
* The yield (`schedContextYieldTo`) as in SpecInvYieldScopeH with `fnB ct` (not blocked); the perform phase keeps
  `YBL [ct]` on every invocation but the yield, which cannot fail (`withoutPreemption`), so every *error* result still
  has `YBL [ct]` for `preemption_path` (results `okErr (YBL []) (YBL [ct])`). The first phase never yields
  (`ro_decode_fp`), so ReplyRecv / NBSendRecv / NBSendWait keep `YBL [ct]` for the receive. The current thread at
  `handle_recv` after the first phase, at the user-fault `handle_fault`, and at `preemption_path` is ft3's bundle `B`'s.
* `activate_thread` gives `CurYieldNone`.
* Tops: **`kentry_yieldBlock`** (syscall entry), **`kcall_yieldBlock`** (non-syscall events; ft3's entry facts for
  the user-fault events), `kcallF_yieldBlock`, `kirq_yieldBlock` (interrupt, any current thread).

No premise ([J]/[P]/[W]).
-/
import Fl4Proofs.P3.SpecInvYieldBlockF4
import Fl4Proofs.P3.SpecInvYieldScopeH
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {L : List ObjRef}

/-! ## Lists -/

theorem ybl_mono {L' : List ObjRef} (h : ∀ p ∈ L', p ∈ L) {σ : State Unit} (hs : YBL L σ) : YBL L' σ :=
  fun p x hp => ⟨(hs p x hp).1, fun hm => (hs p x hp).2 (h p hm)⟩

theorem ybl_nil {σ : State Unit} (hs : YBL L σ) : YBL [] σ := ybl_mono (fun _ h => by simp at h) hs

theorem ybl_tail {σ : State Unit} {t : ObjRef} (h : YBL (t :: L) σ) : YBL L σ :=
  ybl_mono (fun _ h => List.mem_cons_of_mem _ h) h

theorem ybl_cons {σ : State Unit} (h : YBL L σ) {t : ObjRef}
    (ht : ∀ x, σ.kheap t = some (.tcb x) → x.tcbYieldTo = none) : YBL (t :: L) σ := by
  intro p x hp
  refine ⟨(h p x hp).1, fun hm => ?_⟩
  rcases List.mem_cons.1 hm with rfl | hm
  · exact ht x hp
  · exact (h p x hp).2 hm

/-- **A thread read blocked does not yield.** -/
theorem ybl_cons_read {σ : State Unit} (h : YBL L σ) {t : ObjRef} {x : Tcb} (hx : σ.kheap t = some (.tcb x))
    (hb : ¬ notBlkSt x.tcbState) : YBL (t :: L) σ :=
  ybl_cons h fun x' hx' => by
    rw [hx] at hx'; cases hx'
    by_contra hn
    exact hb ((h t x hx).1 hn)

theorem ybikp_cons {α : Type} {σ : State Unit} {t : ObjRef} {x : Tcb} {m : NonDet (State Unit) α}
    (hx : σ.kheap t = some (.tcb x)) (hb : ¬ notBlkSt x.tcbState) (hm : YBK (t :: L) m) : IKp (YBL L) σ m :=
  fun hσ y hy => ybl_tail (hm σ (ybl_cons_read hσ hx hb) y hy)

macro "yb_mem" : tactic => `(tactic| first | assumption | (simp [*]; done))

/-- A blocking `set_thread_state` on a thread of `L`. -/
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine yb_setThreadState _ _ (Or.inr ?_)); yb_mem))

/-- A state read: a blocked thread joins `L`. -/
macro "ybw_rds" : tactic => `(tactic| (show IK _ (getThreadState (Z := Unit) _ >>= _); unfold getThreadState; refine ik_threadGet_bind fun σ x hx => ?_; (try dsimp only); cases hs : x.tcbState <;> (try dsimp only) <;> first | (refine ybikp_cons hx (by rw [hs]; exact id) ?_) | (refine ikp_of_ik ?_ σ)))

theorem ybik_fail_bind {P : State Unit → Prop} {α β : Type} {g : α → NonDet (State Unit) β} :
    IK P ((NonDet.fail : NonDet (State Unit) α) >>= g) :=
  fun _ _ _ ⟨_, hy, _⟩ => hy.elim

macro "ybw_auto" : tactic => `(tactic| repeat' (first | (with_reducible exact ybik_fail_bind) | ybw_rds | yb_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

/-! ## The blocking writers -/

theorem yb_sendIpcBlocked (t ep : ObjRef) (b : Badge) (g gr c : Bool) (ht : t ∈ L) :
    YBK L (sendIpcBlocked (Z := Unit) t ep b g gr c) := by
  unfold sendIpcBlocked; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine yb_sendIpcBlocked _ _ _ _ _ _ ?_); yb_mem))

theorem yb_receiveIpcBlocked (blk : Bool) (t ep : ObjRef) (r : Option ObjRef) (ht : t ∈ L) :
    YBK L (receiveIpcBlocked (Z := Unit) blk t ep r) := by
  unfold receiveIpcBlocked
  split
  · refine ik_bind (yb_setThreadState _ _ (Or.inr ht)) fun _ => ?_
    yb_auto
  · yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine yb_receiveIpcBlocked _ _ _ _ ?_); yb_mem))

theorem yb_receiveSignalBlocked (t n : ObjRef) (blk : Bool) (ht : t ∈ L) :
    YBK L (receiveSignalBlocked (Z := Unit) t n blk) := by
  unfold receiveSignalBlocked
  split
  · refine ik_bind (yb_setThreadState _ _ (Or.inr ht)) fun _ => ?_
    yb_auto
  · yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine yb_receiveSignalBlocked _ _ _ ?_); yb_mem))

theorem yb_replyPush (caller callee r : ObjRef) (d : Bool) (ht : caller ∈ L) :
    YBK L (replyPush (Z := Unit) caller callee r d) := by
  unfold replyPush; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine yb_replyPush _ _ _ _ ?_); yb_mem))

set_option maxHeartbeats 4000000 in
theorem yb_sendIpc (bl call : Bool) (b : Badge) (g gr dn : Bool) (t ep : ObjRef) (ht : t ∈ L) :
    YBK L (sendIpc (Z := Unit) bl call b g gr dn t ep) := by
  unfold sendIpc; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine yb_sendIpc _ _ _ _ _ _ _ _ ?_); yb_mem))

theorem yb_sendFaultIpc (t : ObjRef) (c : Cap) (f : Fault) (dn : Bool) (ht : t ∈ L) :
    YBK L (sendFaultIpc (Z := Unit) t c f dn) := by
  unfold sendFaultIpc; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine yb_sendFaultIpc _ _ _ _ ?_); yb_mem))

theorem yb_handleTimeout (t : ObjRef) (f : Fault) (ht : t ∈ L) : YBK L (handleTimeout (Z := Unit) t f) := by
  unfold handleTimeout; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine yb_handleTimeout _ _ ?_); yb_mem))

theorem yb_handleFault (t : ObjRef) (f : Fault) (ht : t ∈ L) : YBK L (handleFault (Z := Unit) t f) := by
  unfold handleFault; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine yb_handleFault _ _ ?_); yb_mem))

theorem yb_receiveSignal (t : ObjRef) (c : Cap) (blk : Bool) (ht : t ∈ L) :
    YBK L (receiveSignal (Z := Unit) t c blk) := by
  unfold receiveSignal; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine yb_receiveSignal _ _ _ ?_); yb_mem))

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc`**: the queued sender is read `blockedOnSend`, so it does not yield (`ybw_rds`). -/
theorem yb_receiveIpc (t : ObjRef) (c : Cap) (blk : Bool) (rc : Cap) (ht : t ∈ L) :
    YBK L (receiveIpc (Z := Unit) t c blk rc) := by
  unfold receiveIpc; ybw_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine yb_receiveIpc _ _ _ _ ?_); yb_mem))

set_option maxHeartbeats 4000000 in
/-- **`do_reply_transfer`**: the receiver is read `blockedOnReply`, so it does not yield (its timeout fault). -/
theorem yb_doReplyTransfer (s r : ObjRef) (g : Bool) : YBK L (doReplyTransfer (Z := Unit) s r g) := by
  unfold doReplyTransfer; ybw_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_doReplyTransfer _ _ _)

/-! ## The budget: the current thread -/

/-- `YBL L`, the current thread in `L`. -/
abbrev YC (L : List ObjRef) (σ : State Unit) : Prop := YBL L σ ∧ σ.curThread ∈ L

theorem yc_of {α : Type} {m : NonDet (State Unit) α} (h1 : YBK L m)
    (h2 : ∀ c, FGK Ftriv Set.univ (· = c) m) : IK (YC L) m := by
  intro σ hσ y hy
  refine ⟨h1 σ hσ.1 y hy, ?_⟩
  have := (h2 σ.curThread σ (opg_triv rfl) y hy).2
  rw [this]; exact hσ.2

macro "yc_frame" : tactic => `(tactic| exact hk_of_ik (yc_of (by yb_auto) fun _ => by fg_auto))

theorem yb_endTimeslice (cto : Bool) : HK (YC L) (YBL L) (endTimeslice (Z := Unit) cto) := by
  unfold endTimeslice
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  intro σ hσ y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  (try dsimp only at hy)
  have hct : σ.curThread ∈ L := hσ.2
  refine ik_apply hσ.1 hy ?_
  yb_auto

theorem yb_chargeBudget (n : Ticks) (cto : Bool) : HK (YC L) (YBL L) (chargeBudget (Z := Unit) n cto) := by
  unfold chargeBudget
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  refine hk_bind (R := YC L) (by yc_frame) fun sch => ?_
  unfold NonDet.when
  split
  · exact hk_bind (yb_endTimeslice cto) fun _ => hk_of_ik (by yb_auto)
  · intro σ hσ y hy; rw [Set.mem_singleton_iff.1 hy]; exact hσ.1

theorem yb_checkBudget : HK (YC L) (YBL L) (checkBudget (Z := Unit)) := by
  unfold checkBudget
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  refine hk_bind (R := YC L) (by yc_frame) fun suf => ?_
  split
  · exact hk_post (hk_of_ik (yc_of (by yb_auto) fun _ => by fg_auto)) fun _ h => h.1
  · refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
    exact hk_bind (yb_chargeBudget _ _) fun _ => hk_of_ik (ik_pure _)

theorem yb_checkBudgetRestart : HK (YC L) (YBL L) (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart
  exact hk_bind yb_checkBudget fun _ => hk_of_ik (by yb_auto)

theorem yb_handleYield : HK (YC L) (YBL L) (handleYield (Z := Unit)) := by
  unfold handleYield
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  exact hk_bind (yb_chargeBudget _ _) fun _ => hk_of_ik (by yb_auto)

theorem yb_preemptionPath : HK (YC L) (YBL L) (preemptionPath (Z := Unit)) := by
  unfold preemptionPath
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
  dsimp only
  split
  · exact hk_bind yb_checkBudget fun _ => hk_of_ik (by yb_auto)
  · refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
    refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
    split
    · refine hk_bind (R := YC L) (by yc_frame) fun _ => ?_
      exact hk_bind (yb_chargeBudget _ _) fun _ => hk_of_ik (by yb_auto)
    · exact hk_bind (R := YBL L) (hk_post (Q := YC L) (by yc_frame) fun _ h => h.1) fun _ => hk_of_ik (by yb_auto)

/-! ## The receive -/

theorem yb_handleRecv (blk cr : Bool) {σ : State Unit} (hσ : YBL L σ) (hc : σ.curThread ∈ L)
    {y : Unit × State Unit} (hy : y ∈ (handleRecv (Z := Unit) blk cr σ).1) : YBL L y.2 := by
  unfold handleRecv at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [mem_gets h1] at hy
  (try dsimp only at hy)
  refine ik_apply hσ hy ?_
  yb_auto

/-! ## The yield -/

/-- `ct` is the current thread and is not blocked. -/
def fnB (ct : ObjRef) : FQ where
  R p _ s := p = ct → notBlkSt s
  clr _ _ _ h := h
  st _ _ _ _ _ := trivial
  dflt _ _ := trivial

/-- `YBL L` and the frame of `ct`. -/
abbrev YB2 (L : List ObjRef) (ct : ObjRef) (σ : State Unit) : Prop :=
  YBL L σ ∧ OPG (fnB ct) Set.univ (· = ct) σ

theorem yb2_of {ct : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : YBK L m)
    (h2 : FGK (fnB ct) Set.univ (· = ct) m) : IK (YB2 L ct) m := ik_and h1 h2

theorem yb2_ofE {ct : ObjRef} {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : YBKE L m)
    (h2 : FGKE (fnB ct) Set.univ (· = ct) m) : IKE (YB2 L ct) m := ik_and h1 h2

theorem notBlk_of_active {ts : ThreadState} (h : activeSt ts) : notBlkSt ts := by
  cases ts <;> simp_all [activeSt, notBlkSt]

theorem opg_fnB {σ : State Unit} (h : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState) :
    OPG (fnB σ.curThread) Set.univ (· = σ.curThread) σ := by
  refine ⟨fun p o hp => ?_, rfl⟩
  cases o with
  | tcb x => intro e; subst e; exact notBlk_of_active (h x hp)
  | notification n => exact fun _ _ => trivial
  | _ => trivial

theorem yb2_setYield (ct sc : ObjRef) :
    IK (YB2 [] ct) (setTcbObjRef (Z := Unit) tcbYieldToUpdate ct (some sc)) := by
  show IK _ (threadSet _ ct)
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => ?_
  intro hσ y hy
  have hk := getTcb_kheap hx
  rw [mem_setObject hy]
  have hr : notBlkSt x.tcbState := (hσ.2.1 ct (.tcb x) hk : (fnB ct).R ct x.tcbFault x.tcbState) rfl
  refine ⟨tp_update hσ.1 ct _ fun t ht => ?_, opg_update hσ.2 ct _ fun _ => hr⟩
  cases ht
  exact ⟨fun _ => hr, fun h => by simp at h⟩

set_option maxHeartbeats 4000000 in
theorem yb2_schedContextYieldTo (ct sc : ObjRef) : IK (YB2 [] ct) (schedContextYieldTo (Z := Unit) sc) := by
  unfold schedContextYieldTo
  refine ik_bind (yb2_of (by yb_auto) (by fg_auto)) fun _ => ?_
  refine ik_bind (yb2_of (by yb_auto) (by fg_auto)) fun _ => ?_
  refine ik_bind (yb2_of (by yb_auto) (by fg_auto)) fun _ => ?_
  refine ik_bind ?_ fun _ => yb2_of (by yb_auto) (by fg_auto)
  refine ik_bind (yb2_of (by yb_auto) (by fg_auto)) fun _ => ?_
  refine ik_bind (ik_assertOpt _) fun tcbPtr => ?_
  refine ik_gets_bind fun σ => ikp_of_ik ?_ σ
  refine ik_ite _ ?_ (ik_pure _)
  refine ik_gets_cur_bind (ct := ct) (fun s h => h.2.2) ?_
  refine ik_bind (yb2_of (by yb_auto) (by fg_auto)) fun _ => ?_
  refine ik_bind (yb2_of (by yb_auto) (by fg_auto)) fun _ => ?_
  refine ik_ite _ (yb2_of (by yb_auto) (by fg_auto)) ?_
  exact ik_bind (yb2_setYield ct sc) fun _ => yb2_of (by yb_auto) (by fg_auto)

theorem yb2_invokeSchedContext (ct : ObjRef) (i : SchedContextInvocation) :
    IK (YB2 [] ct) (invokeSchedContext (Z := Unit) i) := by
  cases i
  case invokeSchedContextYieldTo sc => exact yb2_schedContextYieldTo ct sc
  all_goals exact yb2_of (by simp only [invokeSchedContext]; yb_auto) (fg_invokeSchedContext _)

set_option maxHeartbeats 4000000 in
/-- Every invocation but a scheduling-context one keeps `YBL L`, the current thread in `L`. -/
theorem yb_fl4PerformInvocation_nSC (bl call don : Bool) (i : Fl4Invocation)
    (h : ∀ j, i ≠ .invokeSchedContext j) : HKE (YC L) (YBL L) (fl4PerformInvocation (Z := Unit) bl call don i) := by
  cases i
  case invokeSchedContext j => exact absurd rfl (h j)
  case invokeEndpoint ep bd g gr =>
    simp only [fl4PerformInvocation, withoutPreemption]
    intro σ hσ y hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    obtain ⟨y1, h1, hx⟩ := hx
    rw [mem_gets h1] at hx
    (try dsimp only at hx)
    have hct : σ.curThread ∈ L := hσ.2
    have h := ik_apply (y := x) hσ.1 hx (by yb_auto)
    exact h
  all_goals
    simp only [fl4PerformInvocation]
    exact fun σ hσ => (by yb_auto : YBKE L _) σ hσ.1

/-- Every invocation, from `YB2 [ct] ct`: errors keep `YBL [ct]` (the yield cannot fail). -/
theorem yb2_fl4PerformInvocation (ct : ObjRef) (bl call don : Bool) (i : Fl4Invocation) :
    HKR (YB2 [ct] ct) (okErr (YBL []) (YBL [ct])) (fl4PerformInvocation (Z := Unit) bl call don i) := by
  by_cases hs : ∃ j, i = .invokeSchedContext j
  · obtain ⟨j, rfl⟩ := hs
    simp only [fl4PerformInvocation, withoutPreemption]
    intro σ hσ y hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    exact (yb2_invokeSchedContext ct j σ ⟨ybl_nil hσ.1, hσ.2⟩ x hx).1
  · refine hkrG_of_hke (fun σ hσ y hy => yb_fl4PerformInvocation_nSC (L := [ct]) bl call don i
      (fun j e => hs ⟨j, e⟩) σ ⟨hσ.1, by rw [hσ.2.2]; exact List.mem_singleton_self _⟩ y hy)
      (fun _ h => ybl_nil h) (fun _ h => h)

/-! ## `handle_invocation` -/

theorem hkr_bindR {P R Q0 Qe : State Unit → Prop} {ε α β : Type} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε β} (hm : HKR P (okErr R Qe) m) (hg : ∀ a, HKR R (okErr Q0 Qe) (g a)) :
    HKR P (okErr Q0 Qe) (m >>= g) := by
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, rfl⟩⟩ := ft_mem_bindE hy
  · obtain ⟨r, s⟩ := z
    simp only at ha; subst ha
    exact hg a s (hm σ hσ _ hz) y hy
  · have := hm σ hσ _ hz
    obtain ⟨r, s⟩ := z
    simp only at he; subst he
    exact this

/-- The `syscall` shell with result-dependent posts (`ft_syscall_post`'s proof). -/
theorem syscall_postR {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ}
    {σ : State Unit} {I Q0 Qe : State Unit → Prop}
    (h1 : ∀ w ∈ ((ExceptT.run mF) σ).1, I w.2)
    (h2 : ∀ f s, I s → ∀ v ∈ (hF f s).1, Q0 v.2)
    (h3 : ∀ a s, (.ok a, s) ∈ ((ExceptT.run mF) σ).1 → ∀ w ∈ ((ExceptT.run (mE a)) s).1, I w.2)
    (h4 : ∀ e s, I s → ∀ v ∈ (hE e s).1, Q0 v.2)
    (h5 : ∀ a s b s', (.ok a, s) ∈ ((ExceptT.run mF) σ).1 → (.ok b, s') ∈ ((ExceptT.run (mE a)) s).1 →
      I s' → ∀ y ∈ ((mFin b).run s').1, okErr Q0 Qe y.1 y.2) :
    ∀ y ∈ ((syscall mF hF mE hE mFin).run σ).1, okErr Q0 Qe y.1 y.2 := by
  intro y hy
  unfold syscall withoutPreemption at hy
  obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    simp only [Except.ok.injEq] at hr
    subst hr
    obtain ⟨r, s⟩ := w
    cases r with
    | error f =>
      obtain ⟨v, hv, rfl⟩ := ft_mem_liftE hy
      exact h2 f s (h1 _ hw) v hv
    | ok a =>
      obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
      · obtain ⟨w, hw', rfl⟩ := ft_mem_liftE hz
        simp only [Except.ok.injEq] at hr
        subst hr
        obtain ⟨r, s'⟩ := w
        cases r with
        | error e =>
          obtain ⟨v, hv, rfl⟩ := ft_mem_liftE hy
          exact h4 e s' (h3 a s hw _ hw') v hv
        | ok b => exact h5 a s b s' hw hw' (h3 a s hw _ hw') y hy
      · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
        cases he
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

set_option maxHeartbeats 4000000 in
/-- **`handle_invocation` from `YB2 [ct] ct`**: `ok` ends in `YBL []`, errors in `YBL [ct]`. -/
theorem yb2_fl4HandleInvocationR (ct : ObjRef) (rep cl bl dn fp : Bool) (cptr : CapRef) :
    HKR (YB2 [ct] ct) (okErr (YBL []) (YBL [ct])) (fl4HandleInvocationR (Z := Unit) rep cl bl dn fp cptr) := by
  unfold fl4HandleInvocationR
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  swap
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz; cases he
  obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
  obtain rfl := mem_gets hw
  simp only [Except.ok.injEq] at ha; subst ha
  have hc : σ.curThread = ct := hσ.2.2
  simp only [hc, withoutPreemption] at hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  swap
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz; cases he
  obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
  simp only [Except.ok.injEq] at ha; subst ha
  have hσ' : YB2 [ct] ct w.2 := (yb2_of (by yb_auto) (by fg_auto)) σ hσ w hw
  refine syscall_postR (I := YB2 [ct] ct) (Q0 := YBL []) (Qe := YBL [ct]) ?_ ?_ ?_ ?_ ?_ y hy
  · exact (yb2_ofE (by yb_auto) (by fg_auto)) w.2 hσ'
  · intro f s hs v hv
    exact ybl_nil ((by yb_auto : YBK [ct] _) s hs.1 v hv)
  · intro a s has w' hw'
    have hs : YB2 [ct] ct s := (yb2_ofE (by yb_auto) (by fg_auto)) w.2 hσ' _ has
    obtain ⟨sl, cap, ex, buf⟩ := a
    exact (yb2_ofE (by yb_auto) (by fg_auto)) s hs w' hw'
  · intro e s hs v hv
    exact ybl_nil ((by yb_auto : YBK [ct] _) s hs.1 v hv)
  · intro a s b s' _ _ hI y hy
    refine (hkrG_bind (R := YB2 [ct] ct)
      (hk_liftE (hk_of_ik (yb2_of (yb_setThreadState ct .restart (Or.inl trivial))
        (fg_setThreadState ct .restart fun _ _ _ _ => trivial)))) (fun _ => ?_) (fun _ h => h.1)) s' hI y hy
    refine hkr_bindR (yb2_fl4PerformInvocation ct _ _ _ b) fun _ => ?_
    exact hkrG_liftE (hk_of_ik (by yb_auto))

set_option maxHeartbeats 4000000 in
/-- **The first phase keeps `YBL [ct]`** (no scheduling-context invocation, `ro_decode_fp`). -/
theorem yb2_fl4HandleInvocationR_fp (ct : ObjRef) (rep cl bl dn : Bool) (cptr : CapRef) :
    HKE (YB2 [ct] ct) (YBL [ct]) (fl4HandleInvocationR (Z := Unit) rep cl bl dn true cptr) := by
  unfold fl4HandleInvocationR
  refine hke_gets_bind fun σ hσ => ?_
  have hc : σ.curThread = ct := hσ.2.2
  simp only [hc, withoutPreemption]
  refine hke_bind (R := YB2 [ct] ct) (hk_liftE (hk_of_ik (yb2_of (by yb_auto) (by fg_auto)))) (fun info => ?_)
    (fun _ h => h.1) σ hσ
  intro σ' hσ' y0 hy0
  refine ft_syscall_post (I := YB2 [ct] ct) (Q := YBL [ct]) ?_ ?_ ?_ ?_ ?_ y0 hy0
  · exact (yb2_ofE (by yb_auto) (by fg_auto)) σ' hσ'
  · intro f s hs v hv
    exact (by yb_auto : YBK [ct] _) s hs.1 v hv
  · intro a s has w hw
    have hs : YB2 [ct] ct s := (yb2_ofE (by yb_auto) (by fg_auto)) σ' hσ' _ has
    obtain ⟨sl, cap, ex, buf⟩ := a
    exact (yb2_ofE (by yb_auto) (by fg_auto)) s hs w hw
  · intro e s hs v hv
    exact (by yb_auto : YBK [ct] _) s hs.1 v hv
  · intro a s b s' _ hd hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hb : ∀ j, b ≠ Fl4Invocation.invokeSchedContext j :=
      ro_bind (fun _ => ro_decode_fp _ _ _ _ _ _ _) s _ hd b rfl
    refine (hke_bind (R := YB2 [ct] ct)
      (hk_liftE (hk_of_ik (yb2_of (yb_setThreadState ct .restart (Or.inl trivial))
        (fg_setThreadState ct .restart fun _ _ _ _ => trivial)))) (fun _ => ?_) (fun _ h => h.1)) s' hI y hy
    refine hke_bind (R := YBL [ct])
      (fun σ1 h1 => yb_fl4PerformInvocation_nSC (L := [ct]) _ _ _ b hb σ1
        ⟨h1.1, by rw [h1.2.2]; exact List.mem_singleton_self _⟩) (fun _ => ?_) (fun _ h => h)
    exact hk_of_ik (by yb_auto)

/-! ## `handle_syscall` -/

/-- The syscall's start. -/
abbrev Q0 (ct : ObjRef) (σ : State Unit) : Prop :=
  YBL [ct] σ ∧ B [ct] [ct] [ct] (· = ct) σ ∧ OPG (fnB ct) Set.univ (· = ct) σ

theorem q0_frame {ct : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : YBK [ct] m) (h2 : GF (· = ct) m) :
    IK (Q0 ct) m :=
  fun σ hσ y hy => ⟨h1 σ hσ.1 y hy, b_of_gf h2 σ hσ.2.1 y hy, h2 _ _ σ hσ.2.2 y hy⟩

set_option maxHeartbeats 4000000 in
theorem yb_fl4HandleSyscall (ct : ObjRef) (rep : Bool) (c : Syscall) :
    HKR (Q0 ct) (okErr (YBL []) (YBL [ct])) (fl4HandleSyscall (Z := Unit) rep c) := by
  have hInv : ∀ (cl bl dn fp : Bool), HKR (Q0 ct) (okErr (YBL []) (YBL [ct])) (do
      let cptr ← NonDetE.liftE (getCapReg (Z := Unit) cap_register)
      fl4HandleInvocationR rep cl bl dn fp cptr) := by
    intro cl bl dn fp
    refine hkrG_bind (R := YB2 [ct] ct) (hk_liftE ?_) (fun cptr => yb2_fl4HandleInvocationR ct rep cl bl dn fp cptr)
      (fun _ h => h.1)
    intro σ hσ y hy
    exact ⟨(by yb_auto : YBK [ct] _) σ hσ.1 y hy,
      fg_getCapReg (Fq := fnB ct) (Sq := Set.univ) (Cq := (· = ct)) _ σ hσ.2.2 y hy⟩
  have hRecv : ∀ b r, HKR (Q0 ct) (okErr (YBL []) (YBL [ct])) (withoutPreemption (Z := Unit) (handleRecv b r)) := by
    intro b r
    refine hkrG_liftE fun σ hσ y hy => ybl_nil (yb_handleRecv b r hσ.1 ?_ hy)
    rw [hσ.2.2.2]; exact List.mem_singleton_self _
  have hRR : ∀ (m : SMonad Unit CapRef) (hm1 : YBK [ct] m) (hm2 : GF (· = ct) m) (bl : Bool),
      HKR (Q0 ct) (okErr (YBL []) (YBL [ct])) (do
        let cp ← withoutPreemption (Z := Unit) m
        fl4HandleInvocationR rep false false true true cp
        withoutPreemption <| handleRecv true bl) := by
    intro m hm1 hm2 bl
    refine hkrG_bind (R := Q0 ct) (hk_liftE (hk_of_ik (q0_frame hm1 hm2))) (fun cp => ?_) (fun _ h => h.1)
    refine hkrG_bind (R := fun s => YBL [ct] s ∧
        (B [ct] [ct] [ct] (· = ct) s ∨ (false = true ∧ B [] [] [ct] (· = ct) s)))
      (fun σ hσ y hy => ⟨yb2_fl4HandleInvocationR_fp ct rep false false true cp σ ⟨hσ.1, hσ.2.2⟩ y hy,
        b_fl4HandleInvocationR ct rep false false true true cp σ hσ.2.1 y hy⟩)
      (fun _ => ?_) (fun _ h => h.1)
    refine hkrG_liftE fun σ hσ y hy => ybl_nil (yb_handleRecv true bl hσ.1 ?_ hy)
    have hc : σ.curThread = ct := by
      rcases hσ.2 with h | h
      · exact h.1.2
      · exact absurd h.1 (by simp)
    rw [hc]; exact List.mem_singleton_self _
  cases c
  case sysSend => simp only [fl4HandleSyscall]; exact hInv _ _ _ _
  case sysNBSend => simp only [fl4HandleSyscall]; exact hInv _ _ _ _
  case sysCall => simp only [fl4HandleSyscall]; exact hInv _ _ _ _
  case sysYield =>
    simp only [fl4HandleSyscall, withoutPreemption]
    exact hkrG_liftE fun σ hσ y hy => ybl_nil (yb_handleYield σ ⟨hσ.1, by rw [hσ.2.2.2]; exact List.mem_singleton_self _⟩ y hy)
  case sysReplyRecv =>
    simp only [fl4HandleSyscall]
    exact hRR _ (by yb_auto) (fun F S => by fg_auto) true
  case sysNBSendRecv =>
    simp only [fl4HandleSyscall]
    exact hRR _ (by yb_auto) (fun F S => by fg_auto) true
  case sysNBSendWait =>
    simp only [fl4HandleSyscall]
    exact hRR _ (by yb_auto) (fun F S => by fg_auto) false
  all_goals
    simp only [fl4HandleSyscall]
    exact hRecv _ _

/-! ## The events -/

set_option maxHeartbeats 4000000 in
theorem yb_fl4HandleEvent_sys (ct : ObjRef) (rep : Bool) (c : Syscall) :
    HKR (Q0 ct) (okErr (YBL []) (YBL [ct])) (fl4HandleEvent (Z := Unit) rep (.syscallEvent c)) := by
  simp only [fl4HandleEvent]
  refine hkrG_bind (R := Q0 ct) (hk_liftE (hk_of_ik (q0_frame (by yb_auto) fun F S => fg_updateTimeStamp)))
    (fun _ => ?_) (fun _ h => h.1)
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    simp only [Except.ok.injEq] at ha; subst ha
    obtain ⟨e1, -⟩ := b_checkBudgetRestart (L := [ct]) (E := []) (K := [ct]) ct (List.mem_singleton_self _)
      (List.mem_singleton_self _) (by simp) hσ.2.1 hw
    have hw2 : YBL [ct] w.2 :=
      yb_checkBudgetRestart σ ⟨hσ.1, by rw [hσ.2.2.2]; exact List.mem_singleton_self _⟩ w hw
    unfold NonDetE.whenE at hy
    split at hy
    · rename_i hr
      rw [e1 hr] at hy
      exact yb_fl4HandleSyscall ct rep c σ hσ y hy
    · rw [Set.mem_singleton_iff.1 hy]
      exact ybl_nil hw2
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

/-- The user-fault shell (`b_evShell`'s). -/
theorem yb_evShell (ct : ObjRef) (F : ObjRef → SMonad Unit Unit) (hF : YBK [ct] (F ct)) :
    HK (fun s => YBL [ct] s ∧ B [ct] [ct] [ct] (· = ct) s) (YBL []) (do
      updateTimeStamp (Z := Unit)
      let restart ← checkBudgetRestart
      NonDet.when restart <| do
        let thread ← NonDet.gets fun s : State Unit => s.curThread
        F thread) := by
  intro σ hσ y ⟨y1, h1, hy⟩
  have hb1 := (b_of_gf (fun _ _ => by fg_auto) : BK [ct] [ct] [ct] (· = ct) (updateTimeStamp (Z := Unit))) σ hσ.2 y1 h1
  have hs1 : YBL [ct] y1.2 := (by yb_auto : YBK [ct] (updateTimeStamp (Z := Unit))) σ hσ.1 y1 h1
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨e2, -⟩ := b_checkBudgetRestart (L := [ct]) (E := []) (K := [ct]) ct (List.mem_singleton_self _)
    (List.mem_singleton_self _) (by simp) hb1 h2
  have hc : y1.2.curThread = ct := hb1.1.2
  have hs2 : YBL [ct] y2.2 := yb_checkBudgetRestart y1.2 ⟨hs1, by rw [hc]; exact List.mem_singleton_self _⟩ y2 h2
  (try dsimp only at hy)
  unfold NonDet.when at hy
  split at hy
  · rename_i hr
    rw [e2 hr] at hy
    obtain ⟨y3, h3, hy⟩ := hy
    rw [mem_gets h3] at hy
    (try dsimp only at hy)
    rw [hc] at hy
    exact ybl_nil (hF _ hs1 y hy)
  · rw [Set.mem_singleton_iff.1 hy]
    exact ybl_nil hs2

set_option maxHeartbeats 4000000 in
/-- Every user-fault event (not a syscall, not the interrupt). -/
theorem yb_handleEvent_user (ct : ObjRef) (ev : Event) (hev : ev ≠ .interrupt) (hes : ∀ c, ev ≠ .syscallEvent c) :
    HKR (fun s => YBL [ct] s ∧ B [ct] [ct] [ct] (· = ct) s) (okErr (YBL []) (YBL [ct]))
      (handleEvent (Z := Unit) ev) := by
  cases ev
  case syscallEvent c => exact absurd rfl (hes c)
  case interrupt => exact absurd rfl hev
  case unknownSyscall n =>
    simp only [handleEvent, withoutPreemption]
    exact hkrG_liftE (yb_evShell ct _ (yb_handleFault ct _ (List.mem_singleton_self _)))
  case userLevelFault w1 w2 =>
    simp only [handleEvent, withoutPreemption]
    exact hkrG_liftE (yb_evShell ct _ (yb_handleFault ct _ (List.mem_singleton_self _)))
  case vmFaultEvent ft =>
    simp only [handleEvent, withoutPreemption]
    refine hkrG_liftE (yb_evShell ct _ ?_)
    exact ik_catch (by yb_auto) fun e => yb_handleFault ct e (List.mem_singleton_self _)
  case hypervisorEvent ht =>
    simp only [handleEvent, withoutPreemption]
    exact hkrG_liftE (yb_evShell ct _ (by yb_auto))

/-- The interrupt event: the current thread is in `L` at the budget check. -/
theorem yb_handleEvent_irq (ct : ObjRef) :
    HKR (fun s => YBL [ct] s ∧ s.curThread = ct) (okErr (YBL []) (YBL [ct])) (handleEvent (Z := Unit) .interrupt) := by
  simp only [handleEvent, withoutPreemption]
  refine hkrG_liftE ?_
  refine hk_bind (R := YC [ct]) ?_ fun _ => ?_
  · intro σ hσ y hy
    exact yc_of (L := [ct]) (by yb_auto) (fun _ => by fg_auto) σ ⟨hσ.1, by rw [hσ.2]; exact List.mem_singleton_self _⟩ y hy
  refine hk_bind yb_checkBudget fun _ => ?_
  exact hk_post (hk_of_ik (by yb_auto)) fun _ h => ybl_nil h

/-! ## The kernel exit -/

theorem yb_cancelYieldTo_cons (t : ObjRef) : HK (YBL L) (YBL (t :: L)) (schedContextCancelYieldTo (Z := Unit) t) := by
  intro σ hσ y hy
  unfold schedContextCancelYieldTo at hy
  obtain ⟨y1, h1, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet h1
  (try dsimp only at hy)
  cases hyt : x.tcbYieldTo with
  | none =>
    rw [hyt] at hy
    simp only [NonDet.maybeM] at hy
    rw [Set.mem_singleton_iff.1 hy]
    exact ybl_cons hσ fun x' hx' => by rw [hx] at hx'; cases hx'; exact hyt
  | some sc =>
    rw [hyt] at hy
    simp only [NonDet.maybeM] at hy
    obtain ⟨y2, h2, hy⟩ := hy
    have hs2 : YBL L y2.2 := by refine ik_apply hσ h2 ?_; yb_auto
    exact ybl_cons (yb_clearYield t y2.2 hs2 y hy) (clearYield_post t hy)

theorem yb_completeYieldTo_cons (t : ObjRef) : HK (YBL L) (YBL (t :: L)) (completeYieldTo (Z := Unit) t) := by
  intro σ hσ y hy
  unfold completeYieldTo at hy
  obtain ⟨y1, h1, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet h1
  (try dsimp only at hy)
  cases hyt : x.tcbYieldTo with
  | none =>
    rw [hyt] at hy
    simp only [NonDet.maybeM] at hy
    rw [Set.mem_singleton_iff.1 hy]
    exact ybl_cons hσ fun x' hx' => by rw [hx] at hx'; cases hx'; exact hyt
  | some sc =>
    rw [hyt] at hy
    simp only [NonDet.maybeM] at hy
    obtain ⟨y2, h2, hy⟩ := hy
    have hs2 : YBL L y2.2 := by refine ik_apply hσ h2 ?_; yb_auto
    exact yb_cancelYieldTo_cons t y2.2 hs2 y hy

theorem yb_activateThread {σ : State Unit} (hσ : YBL [] σ) {y : Unit × State Unit}
    (hy : y ∈ (activateThread (Z := Unit) σ).1) : YieldBlockS y.2 ∧ CurYieldNone y.2 := by
  unfold activateThread at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [mem_gets h1] at hy
  (try dsimp only at hy)
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet h2
  (try dsimp only at hy)
  obtain ⟨y3, h3, hy⟩ := hy
  have hA : YBL [σ.curThread] y3.2 ∧ y3.2.curThread = σ.curThread := by
    unfold NonDet.when at h3
    split at h3
    · exact ⟨yb_completeYieldTo_cons _ σ hσ y3 h3,
        (ik_apply (opg_triv (C := (· = σ.curThread)) rfl) h3 (fg_completeYieldTo _)).2⟩
    · rename_i hn
      rw [Set.mem_singleton_iff.1 h3]
      refine ⟨ybl_cons hσ fun x' hx' => ?_, rfl⟩
      rw [hx] at hx'; cases hx'; exact not_not.1 hn
  have hY : YBL [σ.curThread] y.2 := by
    refine ik_apply hA.1 hy ?_
    yb_auto
  have hC : y.2.curThread = σ.curThread := by
    refine (ik_apply (opg_triv (C := (· = σ.curThread)) hA.2) hy ?_).2
    fg_auto
  refine ⟨(YBL.nil_iff _).1 (ybl_nil hY), fun x' hx' => ?_⟩
  rw [hC] at hx'
  exact (hY _ x' hx').2 (List.mem_singleton_self _)

/-- **`fl4CallKernel`**: the handler ends in `YBL []`, or on an error in `YBL [ct]` with `ct` current
(`preemption_path`), then `fl4Awaken`, `schedule`, `activate_thread`. -/
theorem yb_fl4CallKernel (rep : Bool) (ev : Event) (ct : ObjRef) {P : State Unit → Prop}
    (h : HKR P (okErr (YBL []) (fun s => YBL [ct] s ∧ s.curThread = ct)) (fl4HandleEvent (Z := Unit) rep ev)) :
    HK P (fun s => YieldBlockS s ∧ CurYieldNone s) (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  intro σ hσ y ⟨y1, h1, hy⟩
  have hq : YBL [] y1.2 := by
    unfold NonDetE.handleE at h1
    rw [ExceptT.run_mk] at h1
    obtain ⟨z, hz, h1⟩ := h1
    have hz' := h σ hσ z hz
    obtain ⟨r, s⟩ := z
    cases r with
    | ok a => rw [Set.mem_singleton_iff.1 h1]; exact hz'
    | error e =>
      obtain ⟨w, hw, rfl⟩ := ft_mem_liftE (m := preemptionPath (Z := Unit)) h1
      exact ybl_nil (yb_preemptionPath s ⟨hz'.1, by rw [hz'.2]; exact List.mem_singleton_self _⟩ w hw)
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 : YBL [] y2.2 := (by yb_auto : YBK [] (fl4Awaken (Z := Unit))) _ hq y2 h2
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : YBL [] y3.2 := (by yb_auto : YBK [] (schedule (Z := Unit))) _ hb2 y3 h3
  exact yb_activateThread hb3 hy

/-- Pairing a YieldBlock post with ft3's bundle post (the current thread on errors). -/
theorem hkr_pairB {P P' : State Unit → Prop} {Bo Be : State Unit → Prop} {ct : ObjRef} {ε α : Type}
    {m : NonDetE (State Unit) ε α} (h1 : HKR P (okErr (YBL []) (YBL [ct])) m)
    (h2 : HKR P' (okErr Bo Be) m) (he : ∀ s, Be s → s.curThread = ct) :
    HKR (fun s => P s ∧ P' s) (okErr (YBL []) (fun s => YBL [ct] s ∧ s.curThread = ct)) m := by
  intro σ hσ y hy
  have a1 := h1 σ hσ.1 y hy
  have a2 := h2 σ hσ.2 y hy
  obtain ⟨r, s⟩ := y
  cases r with
  | ok a => exact a1
  | error e => exact ⟨a1, he s a2⟩

/-! ## The tops -/

/-- **YieldBlock across the syscall entry**, from the entry half `CurYieldNone` and ft3's entry facts. -/
theorem kentry_yieldBlock (rep : Bool) (c : Syscall) {σ : State Unit} (hY : YieldBlockS σ) (hC : CurYieldNone σ)
    (hF : FaultTcbsS σ ∧ NQB σ) (hJ : CtEntry σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, YieldBlockS y.2 ∧ CurYieldNone y.2 := by
  intro y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hP : Q0 σ.curThread σ := ⟨YBL.ofCur hY hC, b_entry_of hF hJ, opg_fnB hJ.1⟩
  have hP2 : Q0 σ.curThread y2.2 :=
    q0_frame (by yb_auto) (fun F S => fg_fl4SyscallFaultIP _) σ hP y2 h2
  refine yb_fl4CallKernel rep _ σ.curThread (P := fun s => Q0 σ.curThread s ∧ B [σ.curThread] [σ.curThread]
    [σ.curThread] (· = σ.curThread) s) ?_ y2.2 ⟨hP2, hP2.2.1⟩ y hy
  exact hkr_pairB (yb_fl4HandleEvent_sys _ rep c) (b_fl4HandleEvent_sys _ rep c) fun s h => h.1.2

/-- **YieldBlock across a user-fault event** (not a syscall, not the interrupt). -/
theorem kcall_yieldBlock (rep : Bool) (ev : Event) (hev : ev ≠ .interrupt) (hes : ∀ c, ev ≠ .syscallEvent c)
    {σ : State Unit} (hY : YieldBlockS σ) (hC : CurYieldNone σ) (hF : FaultTcbsS σ ∧ NQB σ) (hJ : CtEntry σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, YieldBlockS y.2 ∧ CurYieldNone y.2 := by
  have hB := b_entry_of hF hJ
  refine yb_fl4CallKernel rep ev σ.curThread (P := fun s => (YBL [σ.curThread] s ∧
    B [σ.curThread] [σ.curThread] [σ.curThread] (· = σ.curThread) s) ∧
    B [σ.curThread] [σ.curThread] [σ.curThread] (· = σ.curThread) s) ?_ σ ⟨⟨YBL.ofCur hY hC, hB⟩, hB⟩
  rw [fl4HandleEvent_other rep ev hes]
  have h2 := b_fl4HandleEvent_user σ.curThread rep ev hev
  rw [fl4HandleEvent_other rep ev hes] at h2
  exact hkr_pairB (yb_handleEvent_user _ ev hev hes) h2 fun s h => h.1.2

/-- **YieldBlock across the interrupt event** (any current thread: `CurYieldNone` covers the idle thread). -/
theorem kirq_yieldBlock (rep : Bool) {σ : State Unit} (hY : YieldBlockS σ) (hC : CurYieldNone σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep .interrupt) σ).1, YieldBlockS y.2 ∧ CurYieldNone y.2 := by
  refine yb_fl4CallKernel rep .interrupt σ.curThread (P := fun s => YBL [σ.curThread] s ∧ s.curThread = σ.curThread)
    ?_ σ ⟨YBL.ofCur hY hC, rfl⟩
  have hne : ∀ c, Event.interrupt ≠ .syscallEvent c := by intro c h; cases h
  rw [fl4HandleEvent_other rep .interrupt hne]
  intro σ' hσ' y hy
  have := yb_handleEvent_irq σ.curThread σ' hσ' y hy
  obtain ⟨r, s⟩ := y
  cases r with
  | ok a => exact this
  | error e =>
    -- `handle_event .interrupt` is `withoutPreemption`: no error result
    simp only [handleEvent, withoutPreemption] at hy
    obtain ⟨w, -, hw⟩ := ft_mem_liftE hy
    simp at hw

/-- **The same after the FaultIP write** (the trap entries, user-fault events). -/
theorem kcallF_yieldBlock (rep : Bool) (ev : Event) (hev : ev ≠ .interrupt) (hes : ∀ c, ev ≠ .syscallEvent c)
    {σ : State Unit} (hY : YieldBlockS σ) (hC : CurYieldNone σ) (hF : FaultTcbsS σ ∧ NQB σ) (hJ : CtEntry σ) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) w.2).1, YieldBlockS y.2 ∧ CurYieldNone y.2 := by
  intro w hw
  have hP : Q0 σ.curThread σ := ⟨YBL.ofCur hY hC, b_entry_of hF hJ, opg_fnB hJ.1⟩
  have hP2 : Q0 σ.curThread w.2 := q0_frame (by yb_auto) (fun F S => fg_fl4SyscallFaultIP _) σ hP w hw
  have hc : w.2.curThread = σ.curThread := hP2.2.2.2
  intro y hy
  refine yb_fl4CallKernel rep ev σ.curThread (P := fun s => (YBL [σ.curThread] s ∧
    B [σ.curThread] [σ.curThread] [σ.curThread] (· = σ.curThread) s) ∧
    B [σ.curThread] [σ.curThread] [σ.curThread] (· = σ.curThread) s) ?_ w.2
    ⟨⟨hP2.1, hP2.2.1⟩, hP2.2.1⟩ y hy
  rw [fl4HandleEvent_other rep ev hes]
  have h2 := b_fl4HandleEvent_user σ.curThread rep ev hev
  rw [fl4HandleEvent_other rep ev hes] at h2
  exact hkr_pairB (yb_handleEvent_user _ ev hev hes) h2 fun s h => h.1.2

end

end Fl4Proofs.P3.SInv
