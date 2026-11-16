/-
P3 (DESIGN.md §9), CSpace: **the spec's finalisation of a final thread cap
has an outcome** (`finThread_out`, `specFinOut_thread`: the Thread case of
`SpecFinOut`), from `Inv`, `ActReady` and `SchedValid` at the state and the
TCB's existence: `unbind_notification`, `unbind_from_sc` (the SC unbind,
whose reschedule needs `ActReady`, and the yield-from's
`complete_yield_to`), `suspend` (`cancel_ipc` in every blocked state:
`blocked_cancel_ipc`, `cancel_signal`, `reply_remove_tcb`; the restart PC,
the queue removals, `sched_context_cancel_yield_to`) and
`prepare_thread_delete` (`fpu_release`).

The steps' facts are carried by the frames `KF` and `KFy` (SpecFinOutSc).
-/
import Fl4Proofs.P3.SpecFinOutSc
import Fl4Proofs.P3.IoPortTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section Spec
open Fl4Spec Classical

/-! ### Helpers -/

/-- `as_user` of a user-monad step with one outcome. -/
theorem asUser_one {α : Type} {σ : State Unit} {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x))
    (f : UserMonad α) {a : α} {uc' : UserContext} (hf : f (archTcbContextGet x.tcbArch) = ({(a, uc')}, False)) :
    asUser (Z := Unit) p f σ =
      ({(a, updK σ p (.tcb { x with tcbArch := archTcbContextSet uc' x.tcbArch }))}, False) := by
  unfold asUser
  show (NonDet.getsThe _ >>= _) σ = _
  rw [nd_bind_one (getTcb_eq hk)]
  show ((pure _ : NonDet (State Unit) UserContext) >>= _) σ = _
  rw [nd_pure_bind']
  show (NonDet.selectF _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.selectF (σ := State Unit) (f (archTcbContextGet x.tcbArch)) σ =
      ({((a, uc'), σ)}, False) by
    rw [hf]; simp only [NonDet.selectF]; ext ⟨b, c⟩ <;> simp)]
  show ((pure _ : NonDet (State Unit) Tcb) >>= _) σ = _
  rw [nd_pure_bind']
  exact (nd_bind_one (setObject_eq (o' := KernelObject.tcb { x with tcbArch := archTcbContextSet uc' x.tcbArch })
    hk rfl) _).trans rfl

theorem KFy.heq {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : KFy σ σ' := (KF.heq h).kfy

theorem KFy.uTcb {σ : State Unit} {p : ObjRef} {x x' : Tcb} (hk : σ.kheap p = some (.tcb x))
    (e : x'.tcbYieldTo = x.tcbYieldTo ∨ x'.tcbYieldTo = none) : KFy σ (updK σ p (.tcb x')) := by
  refine ⟨fun q y hq => ?_, fun q y n hq => ⟨y, ?_, Or.inl rfl⟩⟩
  · by_cases hne : q = p
    · subst hne; rw [hk] at hq; cases hq; exact ⟨x', by simp [updK], e⟩
    · exact ⟨y, by simp only [updK, Function.update_of_ne hne]; exact hq, Or.inl rfl⟩
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    simp only [updK, Function.update_of_ne hne]; exact hq

theorem KFy.uOther {σ : State Unit} {p : ObjRef} {o : KernelObject} (hk : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h2 : ∀ y n, o ≠ .schedContext y n) (o' : KernelObject) : KFy σ (updK σ p o') := by
  refine ⟨fun q y hq => ⟨y, ?_, Or.inl rfl⟩, fun q y n hq => ⟨y, ?_, Or.inl rfl⟩⟩
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; exact h1 y (Option.some.inj hq)
    simp only [updK, Function.update_of_ne hne]; exact hq
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; exact h2 y n (Option.some.inj hq)
    simp only [updK, Function.update_of_ne hne]; exact hq

theorem KFy.uScAny {σ : State Unit} {p : ObjRef} {y z : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (e : z.scYieldFrom = y.scYieldFrom) : KFy σ (updSc σ p z n) :=
  KFy.uSc hk e

/-- `set_thread_state`, keeping the yield links. -/
theorem sts_kfy {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (ts : ThreadState) :
    ∃ σ', setThreadState (Z := Unit) t ts σ = ({((), σ')}, False) ∧ KFy σ σ' ∧
      ∃ x', σ'.kheap t = some (.tcb x') := by
  refine ⟨_, setThreadState_eq' hk ts, (KFy.uTcb (x' := { x with tcbState := ts }) hk (Or.inl rfl)).trans
    (KFy.heq (stsAct_heap (updK σ t (.tcb { x with tcbState := ts })) t).1), { x with tcbState := ts }, ?_⟩
  rw [(stsAct_heap _ t).1]; simp [updK]

theorem getSkObjRef_reply_eq {σ : State Unit} {r : ObjRef} {x : Reply} (hk : σ.kheap r = some (.reply x))
    (f : Reply → Option ObjRef) : getSkObjRef (Z := Unit) KernelObject.reply f r σ = ({(f x, σ)}, False) := by
  unfold getSkObjRef
  rw [nd_bind_one (getReply_eq hk)]; rfl

/-- `tcb_ntfn_dequeue` of a member. -/
theorem tcbNtfnDequeue_mem {σ : State Unit} {t r : ObjRef} {n : Notification}
    (hk : σ.kheap r = some (.notification n)) (ht : t ∈ ntfnQueueOf n) :
    ∃ n', tcbNtfnDequeue (Z := Unit) t r σ = ({((), updK σ r (.notification n'))}, False) := by
  unfold tcbNtfnDequeue
  rw [nd_bind_one (getNotification_eq hk), nd_pure_bind',
    nd_bind_one (show NonDet.assert (σ := State Unit) (t ∈ ntfnQueueOf n) σ = ({((), σ)}, False) by
      simp [NonDet.assert, ht]),
    nd_pure_bind', nd_pure_bind']
  exact ⟨_, setNotification_eq _ hk⟩

/-! ### `cancel_ipc` -/

/-- **`blocked_cancel_ipc`** of a thread queued on its endpoint, with the
reply (if any) bound to it. -/
theorem blockedCancel_out {σ : State Unit} {t ep : ObjRef} {st : ThreadState} {ro : Option ObjRef} {x : Tcb}
    {xe : Endpoint} (hkt : σ.kheap t = some (.tcb x)) (hst : x.tcbState = st) (hb : epBlocked st = some ep)
    (hke : σ.kheap ep = some (.endpoint xe)) (hq : t ∈ xe.epQueue)
    (hro : ∀ rp, ro = some rp → ∃ xr, σ.kheap rp = some (.reply xr) ∧ xr.replyTcb = some t ∧
      ∃ d, st = .blockedOnReceive ep (some rp) d) :
    ∃ σ', ((), σ') ∈ (blockedCancelIpc (Z := Unit) st t ro σ).1 ∧ KFy σ σ' := by
  have hte : t ≠ ep := by rintro rfl; rw [hkt] at hke; cases hke
  unfold blockedCancelIpc getBlockingObject
  rw [nd_bind_one (show NonDet.assertOpt (σ := State Unit) (epBlocked st) σ = ({(ep, σ)}, False) by rw [hb]; rfl),
    nd_bind_one (tcbEpDequeue_eq hke hq)]
  set σ1 := updK σ ep (.endpoint (epDeq xe t)) with hσ1
  have hF1 : KFy σ σ1 := KFy.uOther hke (fun _ h => by cases h) (fun _ _ h => by cases h) _
  have hkt1 : σ1.kheap t = some (.tcb x) := by simp only [hσ1, updK, Function.update_of_ne hte]; exact hkt
  cases ro with
  | none =>
    obtain ⟨σ2, h2, hF2, -⟩ := sts_kfy hkt1 .inactive
    exact ⟨σ2, by dsimp only; rw [h2]; exact Set.mem_singleton _, hF1.trans hF2⟩
  | some rp =>
    obtain ⟨xr, hkr, hrt, d, hsd⟩ := hro rp rfl
    have hre : rp ≠ ep := by rintro rfl; rw [hkr] at hke; cases hke
    have htr : t ≠ rp := by rintro rfl; rw [hkt] at hkr; cases hkr
    have hkr1 : σ1.kheap rp = some (.reply xr) := by simp only [hσ1, updK, Function.update_of_ne hre]; exact hkr
    set σ2 := updK σ1 rp (.reply { xr with replyTcb := none }) with hσ2
    have hkt2 : σ2.kheap t = some (.tcb x) := by simp only [hσ2, updK, Function.update_of_ne htr]; exact hkt1
    have hF2 : KFy σ1 σ2 := KFy.uReply hkr1
    obtain ⟨σ3, h3, hF3, x3, hkt3⟩ := sts_kfy hkt2 .inactive
    obtain ⟨σ4, h4, hF4, -⟩ := sts_kfy hkt3 .inactive
    have hu : replyUnlinkTcb (Z := Unit) t rp σ1 = ({((), σ3)}, False) :=
      (replyUnlinkTcb_eq hkr1 hrt hkt1 (Or.inr ⟨ep, d, by rw [hst, hsd]⟩) htr).trans h3
    refine ⟨σ4, ?_, hF1.trans (hF2.trans (hF3.trans hF4))⟩
    dsimp only
    rw [nd_bind_one hu, h4]
    exact Set.mem_singleton _

/-- **`reply_remove_tcb`** of a thread blocked on its reply, under l4v's
assertion (the reply's SC is the stack's SC exactly when it is the head). -/
theorem replyRemoveTcb_out {σ : State Unit} {t rp : ObjRef} {x : Tcb} {xr : Reply}
    (hkt : σ.kheap t = some (.tcb x)) (hst : x.tcbState = .blockedOnReply rp)
    (hkr : σ.kheap rp = some (.reply xr)) (hrt : xr.replyTcb = some t)
    (hrep : ∀ sc y k, σ.kheap sc = some (.schedContext y k) → rp ∈ y.scReplies →
      (y.scReplies.head? = some rp → xr.replySc = some sc) ∧ (y.scReplies.head? ≠ some rp → xr.replySc = none)) :
    ∃ σ', ((), σ') ∈ (replyRemoveTcb (Z := Unit) t rp σ).1 ∧ KFy σ σ' := by
  have htr : t ≠ rp := by rintro rfl; rw [hkt] at hkr; cases hkr
  have fin : ∀ σr : State Unit, KFy σ σr → (∃ xr', σr.kheap rp = some (.reply xr') ∧ xr'.replyTcb = some t) →
      σr.kheap t = some (.tcb x) → ∃ σ', ((), σ') ∈ (replyUnlinkTcb (Z := Unit) t rp σr).1 ∧ KFy σ σ' := by
    rintro σr hFr ⟨xr', hkr', hrt'⟩ hkt'
    have hk' : (updK σr rp (.reply { xr' with replyTcb := none })).kheap t = some (.tcb x) := by
      simp only [updK, Function.update_of_ne htr]; exact hkt'
    obtain ⟨σ', h', hF', -⟩ := sts_kfy hk' .inactive
    refine ⟨σ', ?_, hFr.trans ((KFy.uReply hkr').trans hF')⟩
    rw [replyUnlinkTcb_eq hkr' hrt' hkt' (Or.inl hst) htr, h']
    exact Set.mem_singleton _
  unfold replyRemoveTcb
  rw [nd_bind_one (getThreadState_eq hkt), hst,
    nd_bind_one (show NonDet.assert (σ := State Unit) (ThreadState.blockedOnReply rp = .blockedOnReply rp) σ =
      ({((), σ)}, False) by simp [NonDet.assert]), Notif.nd_gets_bind]
  cases hw : scWithReply rp σ with
  | none =>
    obtain ⟨σ', h', hF'⟩ := fin σ (KFy.heq rfl) ⟨xr, hkr, hrt⟩ hkt
    exact ⟨σ', by dsimp only; exact h', hF'⟩
  | some sc =>
    obtain ⟨y, k, hks, hmem⟩ := scWithReply_mem hw
    obtain ⟨hh, hnh⟩ := hrep sc y k hks hmem
    obtain ⟨h0, l, hl⟩ : ∃ h0 l, y.scReplies = h0 :: l := by
      cases e : y.scReplies with
      | nil => rw [e] at hmem; cases hmem
      | cons a l => exact ⟨a, l, rfl⟩
    have hrs : rp ≠ sc := by rintro rfl; rw [hkr] at hks; cases hks
    have hts : t ≠ sc := by rintro rfl; rw [hkt] at hks; cases hks
    have hass : (if the y.scReplies.head? = rp then xr.replySc = some sc else xr.replySc = none) := by
      rw [hl, List.head?_cons, show the (some h0) = h0 from rfl]
      by_cases e : h0 = rp
      · rw [if_pos e]; exact hh (by rw [hl, e]; rfl)
      · rw [if_neg e]; exact hnh (by rw [hl]; simpa using e)
    set σ1 := updSc σ sc (scRepliesUpdate (List.takeWhile fun r => decide (r ≠ rp)) y) k with hσ1
    have hkr1 : σ1.kheap rp = some (.reply xr) := by simp only [hσ1, updSc, updK, Function.update_of_ne hrs]; exact hkr
    have hkt1 : σ1.kheap t = some (.tcb x) := by simp only [hσ1, updSc, updK, Function.update_of_ne hts]; exact hkt
    have hF1 : KFy σ σ1 := KFy.uSc hks rfl
    set σ2 := updK σ1 rp (.reply { xr with replySc := none }) with hσ2
    have hkt2 : σ2.kheap t = some (.tcb x) := by simp only [hσ2, updK, Function.update_of_ne htr]; exact hkt1
    obtain ⟨σ', h', hF'⟩ := fin σ2 (hF1.trans (KFy.uReply hkr1)) ⟨{ xr with replySc := none }, by simp [hσ2, updK], hrt⟩ hkt2
    refine ⟨σ', ?_, hF'⟩
    dsimp only
    rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hks) _), nd_bind_one (getSkObjRef_reply_eq hkr _),
      nd_bind_one (show NonDet.assert (σ := State Unit)
        (if the y.scReplies.head? = rp then xr.replySc = some sc else xr.replySc = none) σ = ({((), σ)}, False) by
          simp only [NonDet.assert, hass, true_and, not_true_eq_false]; rfl),
      nd_bind_one (updateSchedContext_eq hks _), nd_bind_one (setReplySc_eq none hkr1)]
    exact h'

/-- The blocked-state facts `cancel_ipc` needs of thread `t` with TCB `x`. -/
def CancelOK (σ : State Unit) (t : ObjRef) (x : Tcb) : Prop :=
  (∀ ep pl, x.tcbState = .blockedOnSend ep pl → ∃ xe, σ.kheap ep = some (.endpoint xe) ∧ t ∈ xe.epQueue) ∧
  (∀ ep ro d, x.tcbState = .blockedOnReceive ep ro d → ∃ xe, σ.kheap ep = some (.endpoint xe) ∧ t ∈ xe.epQueue) ∧
  (∀ ep rp d, x.tcbState = .blockedOnReceive ep (some rp) d →
    ∃ xr, σ.kheap rp = some (.reply xr) ∧ xr.replyTcb = some t) ∧
  (∀ n, x.tcbState = .blockedOnNotification n → ∃ xn, σ.kheap n = some (.notification xn) ∧ t ∈ ntfnQueueOf xn) ∧
  (∀ rp, x.tcbState = .blockedOnReply rp → ∃ xr, σ.kheap rp = some (.reply xr) ∧ xr.replyTcb = some t ∧
    ∀ sc y k, σ.kheap sc = some (.schedContext y k) → rp ∈ y.scReplies →
      (y.scReplies.head? = some rp → xr.replySc = some sc) ∧ (y.scReplies.head? ≠ some rp → xr.replySc = none))

/-- **`cancel_ipc`** in any thread state. -/
theorem cancelIpc_out {σ : State Unit} {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x))
    (hB : CancelOK σ t x) : ∃ σ', ((), σ') ∈ (cancelIpc (Z := Unit) t σ).1 ∧ KFy σ σ' := by
  obtain ⟨hs, hr, hrr, hn, hp⟩ := hB
  obtain ⟨x1, hx1⟩ : ∃ x1 : Tcb, x1 = { x with tcbFault := none } := ⟨_, rfl⟩
  obtain ⟨σ1, hσ1⟩ : ∃ σ1, σ1 = updK σ t (.tcb x1) := ⟨_, rfl⟩
  have hts : threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) t σ = ({((), σ1)}, False) := by
    rw [hσ1, hx1]; exact threadSet_eq _ hkt
  have hkt1 : σ1.kheap t = some (.tcb x1) := by rw [hσ1]; simp [updK]
  have hs1 : x1.tcbState = x.tcbState := by rw [hx1]
  have hF1 : KFy σ σ1 := by rw [hσ1]; exact KFy.uTcb hkt (Or.inl (by rw [hx1]))
  have hkp1 : ∀ q, q ≠ t → σ1.kheap q = σ.kheap q := fun q hq => by rw [hσ1]; simp only [updK, Function.update_of_ne hq]
  have tr : ∀ q o, σ.kheap q = some o → (∀ y, o ≠ .tcb y) → σ1.kheap q = some o := fun q o hq ho => by
    have hne : q ≠ t := by rintro rfl; rw [hkt] at hq; exact ho x (Option.some.inj hq).symm
    rw [hkp1 q hne]; exact hq
  have post : ∀ σ' : State Unit, KFy σ1 σ' → KFy σ σ' := fun σ' h => hF1.trans h
  unfold cancelIpc
  rw [nd_bind_one (getThreadState_eq hkt), nd_bind_one hts]
  cases hst : x.tcbState with
  | blockedOnSend ep pl =>
    obtain ⟨xe, hke, hq⟩ := hs ep pl hst
    obtain ⟨σ', h', hF'⟩ := blockedCancel_out (ro := none) hkt1 (by rw [hs1, hst]) rfl
      (tr ep _ hke (fun _ h => by cases h)) hq (fun _ h => by cases h)
    exact ⟨σ', h', post _ hF'⟩
  | blockedOnReceive ep ro d =>
    obtain ⟨xe, hke, hq⟩ := hr ep ro d hst
    obtain ⟨σ', h', hF'⟩ := blockedCancel_out (ro := ro) hkt1 (by rw [hs1, hst]) rfl
      (tr ep _ hke (fun _ h => by cases h)) hq (fun rp e => by
        subst e
        obtain ⟨xr, hkr, hrt⟩ := hrr ep rp d hst
        exact ⟨xr, tr rp _ hkr (fun _ h => by cases h), hrt, d, rfl⟩)
    exact ⟨σ', h', post _ hF'⟩
  | blockedOnNotification n =>
    obtain ⟨xn, hkn, hq⟩ := hn n hst
    have hkn1 := tr n _ hkn (fun _ h => by cases h)
    obtain ⟨n', hdq⟩ := tcbNtfnDequeue_mem hkn1 hq
    have hnt : n ≠ t := by rintro rfl; rw [hkt] at hkn; cases hkn
    have hkt2 : (updK σ1 n (.notification n')).kheap t = some (.tcb x1) := by
      simp only [updK, Function.update_of_ne (Ne.symm hnt)]; exact hkt1
    obtain ⟨σ', h', hF', -⟩ := sts_kfy hkt2 .inactive
    refine ⟨σ', ?_, post _ ((KFy.uOther hkn1 (fun _ h => by cases h) (fun _ _ h => by cases h) _).trans hF')⟩
    dsimp only
    unfold cancelSignal
    rw [nd_bind_one hdq, h']
    exact Set.mem_singleton _
  | blockedOnReply rp =>
    obtain ⟨xr, hkr, hrt, hrep⟩ := hp rp hst
    have hrep1 : ∀ sc y k, σ1.kheap sc = some (.schedContext y k) → rp ∈ y.scReplies →
        (y.scReplies.head? = some rp → xr.replySc = some sc) ∧ (y.scReplies.head? ≠ some rp → xr.replySc = none) := by
      intro sc y k hks hm
      have hsc : sc ≠ t := by rintro rfl; rw [hkt1] at hks; cases hks
      exact hrep sc y k (by rw [← hkp1 sc hsc]; exact hks) hm
    obtain ⟨σ', h', hF'⟩ := replyRemoveTcb_out hkt1 (by rw [hs1, hst]) (tr rp _ hkr (fun _ h => by cases h)) hrt hrep1
    exact ⟨σ', h', post _ hF'⟩
  | running => exact ⟨σ1, Set.mem_singleton _, hF1⟩
  | runningVM => exact ⟨σ1, Set.mem_singleton _, hF1⟩
  | inactive => exact ⟨σ1, Set.mem_singleton _, hF1⟩
  | restart => exact ⟨σ1, Set.mem_singleton _, hF1⟩
  | idleThreadState => exact ⟨σ1, Set.mem_singleton _, hF1⟩


/-! ### `suspend` -/

/-- **`sched_context_cancel_yield_to`** of a TCB whose yield-to SC (if any)
exists. -/
theorem cyt_out {σ : State Unit} {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x))
    (hy : ∀ p, x.tcbYieldTo = some p → ∃ y n, σ.kheap p = some (.schedContext y n)) :
    ∃ σ' x', schedContextCancelYieldTo (Z := Unit) t σ = ({((), σ')}, False) ∧ σ'.kheap t = some (.tcb x') := by
  cases hyt : x.tcbYieldTo with
  | none =>
    refine ⟨σ, x, ?_, hkt⟩
    unfold schedContextCancelYieldTo
    rw [nd_bind_one (getTcbObjRef_eq _ hkt), hyt]; rfl
  | some p =>
    obtain ⟨y, n, hks⟩ := hy p hyt
    have hpt : p ≠ t := by rintro rfl; rw [hkt] at hks; cases hks
    exact ⟨_, { x with tcbYieldTo := none }, cancelYieldTo_some hkt hyt hks hpt, by simp [updK]⟩

/-- **`suspend`**. -/
theorem suspend_out {σ : State Unit} {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x)) (hB : CancelOK σ t x)
    (hy : ∀ p, x.tcbYieldTo = some p → ∃ y n, σ.kheap p = some (.schedContext y n)) :
    ∃ σ', ((), σ') ∈ (suspend (Z := Unit) t σ).1 ∧ ∃ x', σ'.kheap t = some (.tcb x') := by
  obtain ⟨σ1, h1, hF1⟩ := cancelIpc_out hkt hB
  obtain ⟨x1, hkt1, hy1⟩ := hF1.tcb t x hkt
  -- the restart PC
  have h2 : ∃ σ2 x2, ((), σ2) ∈ (NonDet.when (x1.tcbState = .running) (updateRestartPc (Z := Unit) t) σ1).1 ∧
      σ2.kheap t = some (.tcb x2) ∧ x2.tcbYieldTo = x1.tcbYieldTo ∧ KFy σ1 σ2 := by
    unfold NonDet.when
    split_ifs
    · obtain ⟨uc', hf⟩ : ∃ uc', (NonDet.bind (getRegister nextInstructionRegister) (setRegister faultRegister) :
          UserMonad Unit) (archTcbContextGet x1.tcbArch) = ({((), uc')}, False) :=
        ⟨_, by rw [nd_bind_one' (show getRegister nextInstructionRegister (archTcbContextGet x1.tcbArch) =
          ({(_, archTcbContextGet x1.tcbArch)}, False) from rfl)]; rfl⟩
      refine ⟨_, { x1 with tcbArch := archTcbContextSet uc' x1.tcbArch }, ?_, by simp [updK], rfl,
        KFy.uTcb (x' := { x1 with tcbArch := archTcbContextSet uc' x1.tcbArch }) hkt1 (Or.inl rfl)⟩
      unfold updateRestartPc
      rw [asUser_one hkt1 _ hf]; exact Set.mem_singleton _
    · exact ⟨σ1, x1, Set.mem_singleton _, hkt1, rfl, KFy.heq rfl⟩
  obtain ⟨σ2, x2, hm2, hkt2, hy2, hF2⟩ := h2
  obtain ⟨σ3, h3, hk3, -, -, -⟩ := tcbReleaseRemove_out (setQ σ2 x2.tcbDomain x2.tcbPriority
    (tcbSchedDequeue t (σ2.readyQueues x2.tcbDomain x2.tcbPriority))) t
  have hk3' : σ3.kheap = σ2.kheap := hk3
  have hkt3 : σ3.kheap t = some (.tcb x2) := by rw [hk3']; exact hkt2
  obtain ⟨σ4, x4, h4, hkt4⟩ := cyt_out hkt3 (fun p e => by
    have e' : x.tcbYieldTo = some p := by
      rw [hy2] at e
      rcases hy1 with e1 | e1
      · rw [← e1, e]
      · rw [e1] at e; cases e
    obtain ⟨y, n, hks⟩ := hy p e'
    obtain ⟨y', hks', -⟩ := (hF1.trans hF2).sc p y n hks
    exact ⟨y', n, by rw [hk3']; exact hks'⟩)
  obtain ⟨σ5, h5, -, x5, hkt5⟩ := sts_kfy hkt4 .inactive
  refine ⟨σ5, ?_, x5, hkt5⟩
  unfold suspend
  refine mem_bind_nd h1 ?_
  rw [nd_bind_one (getThreadState_eq hkt1)]
  refine mem_bind_nd hm2 ?_
  rw [nd_bind_one (tcbSchedAction_gen hkt2 _), nd_bind_one h3, nd_bind_one h4, h5]
  exact Set.mem_singleton _

/-! ### `prepare_thread_delete` -/

theorem readFpu_ex (m : MachineState) (h : m.fpuEnabled = true) : ∃ v m', (v, m') ∈ (readFpuState m).1 := by
  refine ⟨readFpuStateVal m.machineStateRest, { m with machineStateRest := m.machineStateRest }, ?_⟩
  unfold readFpuState machineRestLift
  refine mem_bind_nd (x := ((), m)) (by simp [NonDet.stateAssert, NonDet.assert, h]) ?_
  refine mem_bind_nd (x := (m.machineStateRest, m)) rfl ?_
  refine mem_bind_nd (x := ((readFpuStateVal m.machineStateRest, m.machineStateRest), m)) ⟨rfl, rfl⟩ ?_
  refine mem_bind_nd (x := ((), { m with machineStateRest := m.machineStateRest })) (Set.mem_singleton _) ?_
  exact Set.mem_singleton _

theorem fpuOp_ex (f : MachineRestMonad Unit) (b : Bool) (σ : State Unit) :
    ∃ ms', ((), { σ with machineState := ms' }) ∈
      (doMachineOp (Z := Unit) (machineOpLift f >>= fun _ =>
        NonDet.modify fun s : MachineState => { s with fpuEnabled := b }) σ).1 ∧ ms'.fpuEnabled = b := by
  obtain ⟨ms1, hm1⟩ := mol_ex f σ.machineState
  exact ⟨{ ms1 with fpuEnabled := b }, dmo_ex _ σ (mem_bind_nd hm1 (Set.mem_singleton _)), rfl⟩

theorem archThreadSet_eq {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (f : ArchTcb → ArchTcb) :
    archThreadSet (Z := Unit) f t σ = ({((), updK σ t (.tcb { x with tcbArch := f x.tcbArch }))}, False) := by
  unfold archThreadSet
  rw [nd_bind_one (getTcb_eq hk)]
  exact setObject_eq hk rfl

/-- **`prepare_thread_delete`** (`fpu_release`) of a TCB. -/
theorem prepareThreadDelete_out {σ : State Unit} {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x)) :
    ∃ σ', ((), σ') ∈ (prepareThreadDelete (Z := Unit) t σ).1 := by
  unfold prepareThreadDelete fpuRelease
  rw [Notif.nd_gets_bind]
  unfold NonDet.when
  split_ifs with ho
  · unfold switchLocalFpuOwner
    rw [Notif.nd_gets_bind, ho]
    obtain ⟨ms1, hm1, he1⟩ := fpuOp_ex enableFpuImpl true σ
    set σ1 : State Unit := { σ with machineState := ms1 } with hσ1
    obtain ⟨v, ms2, hv⟩ := readFpu_ex ms1 he1
    set σ2 : State Unit := { σ1 with machineState := ms2 } with hσ2
    have hkt2 : σ2.kheap t = some (.tcb x) := hkt
    obtain ⟨uc0, huc0⟩ : ∃ uc0 : UserContext, uc0 = ⟨v, (archTcbContextGet x.tcbArch).userRegs⟩ := ⟨_, rfl⟩
    have hsv := asUser_one hkt2 (setFPUState v) (a := ()) (uc' := uc0) (by rw [huc0]; rfl)
    set σ3 := updK σ2 t (.tcb { x with tcbArch := archTcbContextSet uc0 x.tcbArch }) with hσ3
    obtain ⟨ms4, hm4, -⟩ := fpuOp_ex disableFpuImpl false σ3
    set σ4 : State Unit := { σ3 with machineState := ms4 } with hσ4
    have hkt4 : σ4.kheap t = some (.tcb { x with tcbArch := archTcbContextSet uc0 x.tcbArch }) := by
      simp [hσ4, hσ3, updK]
    have ho4 : σ4.archState.x64CurrentFpuOwner = some t := ho
    refine ⟨?_, mem_bind_nd hm1 ?_⟩
    rotate_left
    refine mem_bind_nd (x := ((), σ3)) ?_ ?_
    · show ((), σ3) ∈ ((doMachineOp readFpuState >>= fun fs => asUser t (setFPUState fs)) σ1).1
      exact mem_bind_nd (dmo_ex _ σ1 hv) (by rw [hsv]; exact Set.mem_singleton _)
    refine mem_bind_nd (x := ((), σ4)) ?_ ?_
    · dsimp only; exact hm4
    unfold setX64CurrentFpuOwner
    beta_reduce
    rw [Notif.nd_gets_bind, ho4]
    simp only [NonDet.maybeM]
    rw [nd_bind_one (archThreadSet_eq hkt4 _)]
    refine mem_bind_nd (Set.mem_singleton _) ?_
    exact Set.mem_singleton _
  · exact ⟨σ, Set.mem_singleton _⟩


/-! ### The unbinds -/

/-- **`unbind_notification`**: the scheduling parts kept (`SFr`), the
thread's SC and yield-to kept. -/
theorem unbindNotification_out {σ : State Unit} {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x))
    (hn : ∀ n, x.tcbBoundNotification = some n → ∃ xn, σ.kheap n = some (.notification xn)) :
    ∃ σ', unbindNotification (Z := Unit) t σ = ({((), σ')}, False) ∧ KF σ σ' ∧ SFr σ σ' ∧
      σ'.schedulerAction = σ.schedulerAction ∧
      ∃ x', σ'.kheap t = some (.tcb x') ∧ x'.tcbSchedContext = x.tcbSchedContext ∧ x'.tcbYieldTo = x.tcbYieldTo ∧
        x'.tcbState = x.tcbState := by
  unfold unbindNotification
  rw [nd_bind_one (getTcbObjRef_eq _ hkt)]
  cases hb : x.tcbBoundNotification with
  | none => exact ⟨σ, rfl, KF.heq rfl, SFr.refl σ, rfl, x, hkt, rfl, rfl, rfl⟩
  | some n =>
    obtain ⟨xn, hkn⟩ := hn n hb
    have hnt : n ≠ t := by rintro rfl; rw [hkt] at hkn; cases hkn
    show ∃ σ', (setNtfnObjRef (Z := Unit) ntfnBoundTcbUpdate n none >>= fun _ =>
      setTcbObjRef tcbBoundNotificationUpdate t none) σ = _ ∧ _
    rw [nd_bind_one (updateSkObjRef_ntfn_eq hkn _ none)]
    set σ1 := updK σ n (.notification (ntfnBoundTcbUpdate (fun _ => none) xn)) with hσ1
    have hkt1 : σ1.kheap t = some (.tcb x) := by simp only [hσ1, updK, Function.update_of_ne (Ne.symm hnt)]; exact hkt
    refine ⟨_, threadSet_eq _ hkt1,
      (KF.uNtfn (x' := ntfnBoundTcbUpdate (fun _ => none) xn) hkn rfl).trans
        (KF.uTcb (x' := tcbBoundNotificationUpdate (fun _ => none) x) hkt1 rfl (Or.inl rfl)),
      (SFr.updOther hkn (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ h => by cases h)
        (fun _ _ h => by cases h)).trans (SFr.updTcb hkt1 rfl rfl), rfl,
      tcbBoundNotificationUpdate (fun _ => none) x, by simp [updK], rfl, rfl, rfl⟩

/-- **`unbind_from_sc`**, from `ActReady`, the SC bound back to the thread
and its yield-from thread a TCB whose yield-to SC exists. -/
theorem unbindFromSc_out {σ : State Unit} {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x))
    (hA : ActReady σ)
    (hsc : ∀ c, x.tcbSchedContext = some c → ∃ y k, σ.kheap c = some (.schedContext y k) ∧ y.scTcb = some t ∧
      ∀ yt, y.scYieldFrom = some yt → ∃ xy, σ.kheap yt = some (.tcb xy) ∧
        ∀ p, xy.tcbYieldTo = some p → ∃ y' n, σ.kheap p = some (.schedContext y' n)) :
    ∃ σ', ((), σ') ∈ (unbindFromSc (Z := Unit) t σ).1 ∧ KF σ σ' := by
  unfold unbindFromSc
  rw [nd_bind_one (getTcbObjRef_eq _ hkt)]
  cases hc : x.tcbSchedContext with
  | none => exact ⟨σ, mem_bind_nd (Set.mem_singleton _) (Set.mem_singleton _), KF.heq rfl⟩
  | some c =>
    obtain ⟨y, k, hks, hyt, hyf⟩ := hsc c hc
    obtain ⟨σ1, h1, hF1, hks1⟩ := unbindTcb_out hks hyt hkt hA
    have h2 : ∃ σ2, ((), σ2) ∈ ((getSchedContext (Z := Unit) c >>= fun sc =>
        NonDet.maybeM completeYieldTo sc.scYieldFrom) σ1).1 ∧ KF σ1 σ2 := by
      rw [nd_bind_one (getSchedContext_eq hks1)]
      cases hyt' : (scTcbUpdate (fun _ => none) y).scYieldFrom with
      | none => exact ⟨σ1, Set.mem_singleton _, KF.heq rfl⟩
      | some yt =>
        obtain ⟨xy, hky, hyp⟩ := hyf yt hyt'
        obtain ⟨xy1, hky1, -, hyy1⟩ := hF1.tcb yt xy hky
        obtain ⟨σ2, e2, hF2⟩ := completeYieldTo_out hky1 (fun p e => by
          have e' : xy.tcbYieldTo = some p := by
            rcases hyy1 with e1 | e1
            · rw [← e1, e]
            · rw [e1] at e; cases e
          obtain ⟨y', n, hkp⟩ := hyp p e'
          obtain ⟨y'', hkp', -⟩ := hF1.sc p y' n hkp
          exact ⟨y'', n, hkp'⟩)
        exact ⟨σ2, mem_of_eq e2, hF2⟩
    obtain ⟨σ2, hm2, hF2⟩ := h2
    exact ⟨σ2, mem_bind_nd h1 hm2, hF1.trans hF2⟩

/-- `cancel_ipc`'s facts from `SchedValid` at an earlier state, across `KF`. -/
theorem cancelOK_of_valid {σ σ' : State Unit} {t : ObjRef} {x x' : Tcb} (hV : SchedValid σ)
    (hkt : σ.kheap t = some (.tcb x)) (hF : KF σ σ') (hkt' : σ'.kheap t = some (.tcb x'))
    (hs : x'.tcbState = x.tcbState) : CancelOK σ' t x' := by
  refine ⟨fun ep pl e => ?_, fun ep ro d e => ?_, fun ep rp d e => ?_, fun n e => ?_, fun rp e => ?_⟩
  · obtain ⟨xe, hke, hq⟩ := hV.sendQ t x ep pl hkt (by rw [← hs, e])
    exact ⟨xe, hF.ep ep xe hke, hq⟩
  · obtain ⟨xe, hke, hq⟩ := hV.recvQ t x ep ro d hkt (by rw [← hs, e])
    exact ⟨xe, hF.ep ep xe hke, hq⟩
  · obtain ⟨xr, hkr, hrt⟩ := hV.recvReply t x ep rp d hkt (by rw [← hs, e])
    obtain ⟨xr', hkr', e1, -⟩ := hF.reply rp xr hkr
    exact ⟨xr', hkr', by rw [e1, hrt]⟩
  · obtain ⟨xn, hkn, hq⟩ := hV.ntfnW t x n hkt (by rw [← hs, e])
    obtain ⟨xn', hkn', e1⟩ := hF.ntfn n xn hkn
    exact ⟨xn', hkn', by simp only [ntfnQueueOf, e1]; exact hq⟩
  · obtain ⟨xr, hkr, hrt⟩ := hV.onReply t x rp hkt (by rw [← hs, e])
    obtain ⟨xr', hkr', e1, e2⟩ := hF.reply rp xr hkr
    refine ⟨xr', hkr', by rw [e1, hrt], fun sc y k hks hm => ?_⟩
    obtain ⟨y0, hks0, ey⟩ := hF.sc' sc y k hks
    obtain ⟨xr0, hkr0, h1, h2⟩ := hV.replies sc y0 k rp hks0 (by rw [← ey]; exact hm)
    rw [hkr] at hkr0; cases hkr0
    rw [ey, e2]
    exact ⟨h1, h2⟩

/-- **The spec's finalisation of a final thread cap has an outcome**, from
`Inv`, `ActReady` and `SchedValid`. -/
theorem finThread_out {σ : State Unit} {r : ObjRef} {x : Tcb} (hkt : σ.kheap r = some (.tcb x)) (hI : Inv σ)
    (hA : ActReady σ) (hV : SchedValid σ) :
    ∃ σ', ((Cap.zombie r none 6, Cap.nullCap), σ') ∈ (finaliseCap (Z := Unit) (.threadCap r) true σ).1 := by
  obtain ⟨σ1, h1, hF1, hS1, ha1, x1, hkt1, hsc1, hyt1, hst1⟩ :=
    unbindNotification_out hkt (fun n e => hV.tcbNtfn r x n hkt e)
  have hA1 : ActReady σ1 := hS1.actReady hA (Or.inl ha1)
  obtain ⟨σ2, h2, hF2⟩ := unbindFromSc_out hkt1 hA1 (fun c e => by
    obtain ⟨y, k, hks, hyt⟩ := hI.back r x c hkt (by rw [← hsc1]; exact e)
    obtain ⟨y1, hks1, -, -, e3, -⟩ := hS1.sc c y k hks
    obtain ⟨y1', hks1', -, hyf1⟩ := hF1.sc c y k hks
    rw [hks1] at hks1'; cases hks1'
    refine ⟨y1, k, hks1, by rw [e3, hyt], fun yt e' => ?_⟩
    have e'' : y.scYieldFrom = some yt := by
      rcases hyf1 with f | f
      · rw [← f, e']
      · rw [f] at e'; cases e'
    obtain ⟨xy, hky, -⟩ := hV.scYieldFrom c y k yt hks e''
    obtain ⟨xy1, hky1, -, hyy⟩ := hF1.tcb yt xy hky
    refine ⟨xy1, hky1, fun p ep => ?_⟩
    have ep' : xy.tcbYieldTo = some p := by
      rcases hyy with f | f
      · rw [← f, ep]
      · rw [f] at ep; cases ep
    obtain ⟨y', n, hkp⟩ := hV.tcbYieldTo yt xy p hky ep'
    obtain ⟨y'', hkp', -⟩ := hF1.sc p y' n hkp
    exact ⟨y'', n, hkp'⟩)
  have hF12 := hF1.trans hF2
  obtain ⟨x2, hkt2, hst2, hyt2⟩ := hF12.tcb r x hkt
  obtain ⟨σ3, h3, x3, hkt3⟩ := suspend_out hkt2 (cancelOK_of_valid hV hkt hF12 hkt2 hst2) (fun p e => by
    have e' : x.tcbYieldTo = some p := by
      rcases hyt2 with f | f
      · rw [← f, e]
      · rw [f] at e; cases e
    obtain ⟨y, n, hkp⟩ := hV.tcbYieldTo r x p hkt e'
    obtain ⟨y', hkp', -⟩ := hF12.sc p y n hkp
    exact ⟨y', n, hkp'⟩)
  obtain ⟨σ4, h4⟩ := prepareThreadDelete_out hkt3
  refine ⟨σ4, ?_⟩
  unfold finaliseCap
  simp only [NonDet.when, ↓reduceIte]
  exact mem_bind_nd (mem_of_eq h1) (mem_bind_nd h2 (mem_bind_nd h3 (mem_bind_nd h4 (Set.mem_singleton _))))

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`SpecFinOut` for the thread caps**, from the scheduling invariants and
`valid_cap` at related states. -/
theorem specFinOut_thread (th : TypedHeap) (hC : SchedCoupling (L := L) th) (hO : CapObjHyp (L := L) th) :
    SpecFinOut (L := L) FinThreadK th := by
  intro s σ G sl c hk hDS hA hc _
  obtain ⟨p, rfl⟩ := hk
  obtain ⟨hI, hAR, hV⟩ := hC s σ G hDS
  obtain ⟨x, hkt⟩ := hO s σ G sl _ hDS hA hc
  have e : absCap (finRem (.Thread p) true) = .zombie p.bv none 6 := by
    show Fl4Spec.Cap.zombie p.bv (zombieBits capability.ZOMBIE_TCB) (6#u64 : U64).val = _
    rw [zombieBits_tcb zombie_tcb_val]; rfl
  rw [e]
  exact finThread_out hkt hI hAR hV

end

end Fl4Proofs.P3.Sched
