/-
P3 (DESIGN.md §9), CSpace: **the spec's finalisation of a final reply cap
has an outcome** (`finReply_out`, `specFinOut_reply`: the Reply case of
`SpecFinOut`), from `ReplyPre`: the reply exists and, if bound to a thread,
the thread is a TCB blocked on it, either

* receiving (`cancel_ipc`'s `blocked_cancel_ipc`: the thread queued on its
  endpoint), or
* on the reply (`reply_remove`): the SC holding the reply in its stack, if
  any, has the reply's `reply_sc` consistent with the stack's head (l4v
  `valid_replies`), its other replies are reply objects and its thread (if
  any) is a TCB; and `ActReady` (for `sched_context_donate`'s
  `test_reschedule`: the old holder loses its SC, so `ActReady` is kept,
  `actReady_drop`).
-/
import Fl4Proofs.P3.SpecFinOutEp
import Fl4Proofs.P3.ScCallUnlink
import Fl4Proofs.P3.ScCallCut
import Fl4Proofs.P3.ScCallOps
import Fl4Proofs.P3.ScSpecStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section Spec
open Fl4Spec Classical

theorem scWithReply_mem {σ : State Unit} {r p : ObjRef} (h : scWithReply r σ = some p) :
    ∃ y n, σ.kheap p = some (.schedContext y n) ∧ r ∈ y.scReplies := by
  unfold scWithReply partialInv at h
  split_ifs at h with hex
  obtain rfl := Option.some.inj h
  have := The_spec hex
  simpa using this

/-- What `reply_unlink_sc` keeps: the scheduling parts (`SFr`), the
scheduler action, every TCB, every reply's thread. -/
structure UFr (σ σ' : State Unit) : Prop where
  s : SFr σ σ'
  act : σ'.schedulerAction = σ.schedulerAction
  tcb : ∀ p x, σ.kheap p = some (.tcb x) → σ'.kheap p = some (.tcb x)
  rep : ∀ p x, σ.kheap p = some (.reply x) → ∃ x', σ'.kheap p = some (.reply x') ∧ x'.replyTcb = x.replyTcb

theorem UFr.trans {σ1 σ2 σ3 : State Unit} (h1 : UFr σ1 σ2) (h2 : UFr σ2 σ3) : UFr σ1 σ3 := by
  refine ⟨h1.s.trans h2.s, h2.act.trans h1.act, fun p x hp => h2.tcb p x (h1.tcb p x hp), fun p x hp => ?_⟩
  obtain ⟨x1, h1', e1⟩ := h1.rep p x hp
  obtain ⟨x2, h2', e2⟩ := h2.rep p x1 h1'
  exact ⟨x2, h2', e2.trans e1⟩

theorem UFr.updReply {σ : State Unit} {p : ObjRef} {x x' : Reply} (hk : σ.kheap p = some (.reply x))
    (e : x'.replyTcb = x.replyTcb) : UFr σ (updK σ p (.reply x')) := by
  refine ⟨SFr.updOther hk (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ h => by cases h)
    (fun _ _ h => by cases h), rfl, fun q y hq => ?_, fun q y hq => ?_⟩
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    simp only [updK, Function.update_of_ne hne]; exact hq
  · by_cases hne : q = p
    · subst hne; rw [hk] at hq; cases hq; exact ⟨x', by simp [updK], e⟩
    · exact ⟨y, by simp only [updK, Function.update_of_ne hne]; exact hq, rfl⟩

theorem UFr.updScR {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat} (hk : σ.kheap p = some (.schedContext y n))
    (f : List ObjRef → List ObjRef) : UFr σ (updSc σ p (scRepliesUpdate f y) n) := by
  refine ⟨SFr.updSc hk rfl rfl rfl rfl rfl, rfl, fun q x hq => ?_, fun q x hq => ?_⟩
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    simp only [updSc, updK, Function.update_of_ne hne]; exact hq
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    exact ⟨x, by simp only [updSc, updK, Function.update_of_ne hne]; exact hq, rfl⟩

/-- Setting a reply's SC, after a `UFr` step. -/
theorem setReplySc_ufr {σ σ1 : State Unit} (h : UFr σ σ1) {p : ObjRef} {x : Reply}
    (hk : σ.kheap p = some (.reply x)) (v : Option ObjRef) :
    ∃ σ2, setReplyObjRef (Z := Unit) replyScUpdate p v σ1 = ({((), σ2)}, False) ∧ UFr σ σ2 := by
  obtain ⟨x1, hk1, -⟩ := h.rep p x hk
  exact ⟨_, setReplySc_eq v hk1, h.trans (UFr.updReply hk1 rfl)⟩

/-- **`reply_unlink_sc`** of a reply in the SC's stack, under l4v's
assertions (the reply's SC is the SC if and only if it is the head). -/
theorem unlinkSc_out {σ : State Unit} {sc r : ObjRef} {y : SchedContext} {k : Nat} {xr : Reply}
    (hks : σ.kheap sc = some (.schedContext y k)) (hkr : σ.kheap r = some (.reply xr))
    (hmem : r ∈ y.scReplies)
    (hh : y.scReplies.head? = some r → xr.replySc = some sc)
    (hnh : y.scReplies.head? ≠ some r → xr.replySc = none)
    (htl : ∀ r' ∈ y.scReplies.tail, ∃ x', σ.kheap r' = some (.reply x')) :
    ∃ σ', replyUnlinkSc (Z := Unit) sc r σ = ({((), σ')}, False) ∧ UFr σ σ' := by
  obtain ⟨h0, l, hl⟩ : ∃ h0 l, y.scReplies = h0 :: l := by
    cases e : y.scReplies with
    | nil => rw [e] at hmem; cases hmem
    | cons a l => exact ⟨a, l, rfl⟩
  have hF0 := UFr.updScR hks (List.tail)
  unfold replyUnlinkSc
  rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hks) _), nd_bind_one (getReply_eq hkr)]
  by_cases e : h0 = r
  · subst e
    have hrs : xr.replySc = some sc := hh (by rw [hl]; rfl)
    rw [if_pos (by rw [hl]; rfl)]
    rw [nd_bind_one (show NonDet.assert (σ := State Unit) (xr.replySc = some sc) σ = ({((), σ)}, False) by
      simp [NonDet.assert, hrs])]
    rw [nd_bind_one (updateSchedContext_eq hks _)]
    rw [hl]
    cases l with
    | nil =>
      simp only [List.tail_cons]
      exact setReplySc_ufr hF0 hkr none
    | cons r' l' =>
      simp only [List.tail_cons]
      obtain ⟨x', hk'⟩ := htl r' (by rw [hl]; exact List.mem_cons_self ..)
      obtain ⟨σ2, he2, hF2⟩ := setReplySc_ufr hF0 hk' (some sc)
      rw [nd_bind_one he2]
      exact setReplySc_ufr hF2 hkr none
  · have hrs : xr.replySc = none := hnh (by rw [hl]; simpa using e)
    rw [if_neg (by rw [hl]; exact e)]
    rw [nd_bind_one (show NonDet.assert (σ := State Unit) (xr.replySc = none) σ = ({((), σ)}, False) by
      simp [NonDet.assert, hrs])]
    exact ⟨_, updateSchedContext_eq hks _, UFr.updScR hks _⟩


/-! ### `sched_context_donate` -/

/-- **`ActReady` after a thread `f` loses its SC** (and leaves the release
queue): `f` is no schedulable switch target, and the others keep what
`RdyAt` and `schedulable` read. -/
theorem actReady_drop {σ σ' : State Unit} {f : ObjRef} (hA : ActReady σ)
    (hact : σ'.schedulerAction = σ.schedulerAction) (ht : σ'.curTime = σ.curTime)
    (hk : ∀ p, p ≠ f → σ'.kheap p = σ.kheap p)
    (hf : ∃ xf, σ'.kheap f = some (.tcb xf) ∧ xf.tcbSchedContext = none)
    (hq : ∀ u, u ≠ f → u ∉ σ'.releaseQueue → u ∉ σ.releaseQueue) : ActReady σ' := by
  rw [actReady_iff] at hA ⊢
  intro u hu hs
  obtain ⟨x, c, y, n, hku, hc, hr, hky, ha, hnq⟩ := schedulable_inv hs
  obtain ⟨xf, hkf, hn⟩ := hf
  have huf : u ≠ f := by
    rintro rfl; rw [hkf] at hku; cases hku; rw [hn] at hc; cases hc
  have hcf : c ≠ f := by
    rintro rfl; rw [hkf] at hky; cases hky
  rw [hk u huf] at hku; rw [hk c hcf] at hky
  obtain ⟨x0, c0, y0, k0, h1, h2, h3, h4, h5, h6⟩ :=
    hA u (by rw [← hact]; exact hu) (schedulable_of hku hc hr hky ha (hq u huf hnq))
  have e1 : x0 = x := by rw [h1] at hku; injection hku with hku; injection hku
  subst e1
  have e2 : c0 = c := by rw [hc] at h2; injection h2 with h2; exact h2.symm
  subst e2
  exact ⟨x0, c0, y0, k0, by rw [hk u huf]; exact h1, h2, by rw [hk c0 hcf]; exact h3, h4, by rw [ht]; exact h5, h6⟩

/-- What `sched_context_donate` keeps: every TCB's state, every SC (as an
SC), every other object. -/
def DFr (σ σ' : State Unit) : Prop :=
  (∀ p x, σ.kheap p = some (.tcb x) → ∃ x', σ'.kheap p = some (.tcb x') ∧ x'.tcbState = x.tcbState) ∧
  (∀ p y k, σ.kheap p = some (.schedContext y k) → ∃ y', σ'.kheap p = some (.schedContext y' k)) ∧
  (∀ p, (∀ x, σ.kheap p ≠ some (.tcb x)) → (∀ y k, σ.kheap p ≠ some (.schedContext y k)) → σ'.kheap p = σ.kheap p)

theorem DFr.trans {σ1 σ2 σ3 : State Unit} (h1 : DFr σ1 σ2) (h2 : DFr σ2 σ3) : DFr σ1 σ3 := by
  refine ⟨fun p x hp => ?_, fun p y k hp => ?_, fun p ht hs => ?_⟩
  · obtain ⟨x1, hx1, e1⟩ := h1.1 p x hp
    obtain ⟨x2, hx2, e2⟩ := h2.1 p x1 hx1
    exact ⟨x2, hx2, e2.trans e1⟩
  · obtain ⟨y1, hy1⟩ := h1.2.1 p y k hp
    exact h2.2.1 p y1 k hy1
  · have e1 := h1.2.2 p ht hs
    rw [h2.2.2 p (fun x h => ht x (by rw [← e1]; exact h)) (fun y k h => hs y k (by rw [← e1]; exact h)), e1]

theorem DFr.heq {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : DFr σ σ' :=
  ⟨fun _ x hp => ⟨x, by rw [h]; exact hp, rfl⟩, fun _ y _ hp => ⟨y, by rw [h]; exact hp⟩, fun _ _ _ => by rw [h]⟩

theorem DFr.updTcb {σ : State Unit} {p : ObjRef} {x x' : Tcb} (hk : σ.kheap p = some (.tcb x))
    (e : x'.tcbState = x.tcbState) : DFr σ (updK σ p (.tcb x')) := by
  refine ⟨fun q y hq => ?_, fun q y k hq => ?_, fun q ht _ => ?_⟩
  · by_cases hne : q = p
    · subst hne; rw [hk] at hq; cases hq; exact ⟨x', by simp [updK], e⟩
    · exact ⟨y, by simp only [updK, Function.update_of_ne hne]; exact hq, rfl⟩
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    exact ⟨y, by simp only [updK, Function.update_of_ne hne]; exact hq⟩
  · have hne : q ≠ p := by rintro rfl; exact ht x hk
    simp only [updK, Function.update_of_ne hne]

theorem DFr.updSc {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (z : SchedContext) : DFr σ (updSc σ p z n) := by
  refine ⟨fun q x hq => ?_, fun q y' k hq => ?_, fun q _ hs => ?_⟩
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    exact ⟨x, by simp only [updSc, updK, Function.update_of_ne hne]; exact hq, rfl⟩
  · by_cases hne : q = p
    · subst hne; rw [hk] at hq; cases hq; exact ⟨z, by simp [updSc, updK]⟩
    · exact ⟨y', by simp only [updSc, updK, Function.update_of_ne hne]; exact hq⟩
  · have hne : q ≠ p := by rintro rfl; exact hs y n hk
    simp only [updSc, updK, Function.update_of_ne hne]

theorem tcbReleaseRemove_out (σ : State Unit) (t : ObjRef) :
    ∃ σ', tcbReleaseRemove (Z := Unit) t σ = ({((), σ')}, False) ∧ σ'.kheap = σ.kheap ∧
      σ'.schedulerAction = σ.schedulerAction ∧ σ'.curTime = σ.curTime ∧
      σ'.releaseQueue = tcbSchedDequeue t σ.releaseQueue := by
  unfold tcbReleaseRemove
  rw [Notif.nd_gets_bind]
  unfold NonDet.when
  split
  · rw [nd_bind_one (show NonDet.modify (fun s : State Unit => { s with reprogramTimer := true }) σ =
      ({((), { σ with reprogramTimer := true })}, False) from rfl), Notif.nd_pure_bind']
    exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl), Notif.nd_pure_bind']
    exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem when_resched {σ : State Unit} (hA : ActReady σ) (P : Prop) [Decidable P] :
    ∃ σ', (if P then rescheduleRequired (Z := Unit) else NonDet.pure ()) σ = ({((), σ')}, False) ∧
      σ'.kheap = σ.kheap := by
  split
  · obtain ⟨σ', he, hk, -⟩ := resched_ok hA; exact ⟨σ', he, hk⟩
  · exact ⟨σ, rfl, rfl⟩

/-- The binds of `sched_context_donate` after the old holder's unbind. -/
theorem donate_tail {σ σr : State Unit} {sc tp : ObjRef} (hD : DFr σ σr) {y : SchedContext} {k : Nat} {xt : Tcb}
    (hks : σ.kheap sc = some (.schedContext y k)) (hkt : σ.kheap tp = some (.tcb xt)) :
    ∃ σ', ((), σ') ∈ ((setScObjRef (Z := Unit) scTcbUpdate sc (some tp) >>= fun _ =>
      setTcbObjRef (Z := Unit) tcbSchedContextUpdate tp (some sc)) σr).1 ∧ DFr σ σ' := by
  obtain ⟨y', hks'⟩ := hD.2.1 sc y k hks
  obtain ⟨x', hkt', -⟩ := hD.1 tp xt hkt
  have hts : tp ≠ sc := by rintro rfl; rw [hkt] at hks; cases hks
  have e1 : setScObjRef (Z := Unit) scTcbUpdate sc (some tp) σr =
      ({((), updSc σr sc (scTcbUpdate (fun _ => some tp) y') k)}, False) := updateSchedContext_eq hks' _
  have hkt2 : (updSc σr sc (scTcbUpdate (fun _ => some tp) y') k).kheap tp = some (.tcb x') := by
    simp only [updSc, updK, Function.update_of_ne hts]; exact hkt'
  have e2 : setTcbObjRef (Z := Unit) tcbSchedContextUpdate tp (some sc)
      (updSc σr sc (scTcbUpdate (fun _ => some tp) y') k) =
      ({((), updK (updSc σr sc (scTcbUpdate (fun _ => some tp) y') k) tp
        (.tcb (tcbSchedContextUpdate (fun _ => some sc) x')))}, False) := threadSet_eq _ hkt2
  refine ⟨_, mem_bind_nd (x := ((), updSc σr sc (scTcbUpdate (fun _ => some tp) y') k))
    (by rw [e1]; exact Set.mem_singleton _) (by rw [e2]; exact Set.mem_singleton _), ?_⟩
  obtain ⟨x0, hx0, ex0⟩ := hD.1 tp xt hkt
  rw [hkt'] at hx0; cases hx0
  exact hD.trans ((DFr.updSc hks' _).trans (DFr.updTcb hkt2 rfl))

/-- **`sched_context_donate` has an outcome**, given the SC's thread (if
any) is a TCB and `ActReady`. -/
theorem donate_out {σ : State Unit} {sc tp : ObjRef} {y : SchedContext} {k : Nat} {xt : Tcb}
    (hks : σ.kheap sc = some (.schedContext y k)) (hkt : σ.kheap tp = some (.tcb xt))
    (hf : ∀ f, y.scTcb = some f → ∃ xf, σ.kheap f = some (.tcb xf)) (hA : ActReady σ) :
    ∃ σ', ((), σ') ∈ (schedContextDonate (Z := Unit) sc tp σ).1 ∧ DFr σ σ' := by
  unfold schedContextDonate
  rw [nd_bind_one (getScObjRef_eq hks _)]
  cases hy : y.scTcb with
  | none =>
    simp only [NonDet.when, ne_eq, not_true_eq_false, ↓reduceIte]
    obtain ⟨σ', h', hD'⟩ := donate_tail (DFr.heq rfl) hks hkt
    exact ⟨σ', mem_bind_nd (x := ((), σ)) (Set.mem_singleton _) h', hD'⟩
  | some f =>
    obtain ⟨xf, hkf⟩ := hf f hy
    simp only [NonDet.when, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte]
    set σ1 := setQ σ xf.tcbDomain xf.tcbPriority (tcbSchedDequeue f (σ.readyQueues xf.tcbDomain xf.tcbPriority))
      with hσ1
    obtain ⟨σ2, h2, hk2, ha2, ht2, hq2⟩ := tcbReleaseRemove_out σ1 f
    have hk2' : σ2.kheap = σ.kheap := hk2
    have hkf2 : σ2.kheap f = some (.tcb xf) := by rw [hk2']; exact hkf
    set σ3 := updK σ2 f (.tcb (tcbSchedContextUpdate (fun _ => none) xf)) with hσ3
    have hA3 : ActReady σ3 := by
      refine actReady_drop (f := f) hA ha2 ht2 (fun p hp => ?_) ⟨tcbSchedContextUpdate (fun _ => none) xf, by simp [hσ3, updK], rfl⟩ (fun u hu hn hm => hn ?_)
      · simp only [hσ3, updK, Function.update_of_ne hp]; rw [hk2']
      · show u ∈ σ2.releaseQueue
        rw [hq2]
        simp only [tcbSchedDequeue, List.mem_filter, decide_eq_true_eq]
        exact ⟨hm, Ne.symm hu⟩
    obtain ⟨σ4, he4, hk4⟩ : ∃ σ4, testReschedule (Z := Unit) f σ3 = ({((), σ4)}, False) ∧ σ4.kheap = σ3.kheap := by
      unfold testReschedule
      rw [Notif.nd_gets_bind, Notif.nd_gets_bind, nd_pure_bind']
      unfold NonDet.when
      exact when_resched hA3 _
    have hD4 : DFr σ σ4 := (DFr.heq hk2').trans ((DFr.updTcb (x' := tcbSchedContextUpdate (fun _ => none) xf) hkf2 rfl).trans (DFr.heq hk4))
    obtain ⟨σ', h', hD'⟩ := donate_tail hD4 hks hkt
    refine ⟨σ', mem_bind_nd (x := ((), σ4)) ?_ h', hD'⟩
    rw [nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some f) σ = ({(f, σ)}, False) from rfl),
      nd_bind_one (tcbSchedAction_gen hkf _), nd_bind_one h2,
      nd_bind_one (show setTcbObjRef (Z := Unit) tcbSchedContextUpdate f none σ2 = _ from threadSet_eq _ hkf2), he4]
    exact Set.mem_singleton _


/-! ### `reply_remove` and `cancel_ipc` -/

/-- l4v's facts on the SC holding reply `r` in its stack (`valid_replies`,
the SC's thread a TCB). -/
def ScRepOK (σ : State Unit) (r : ObjRef) (xr : Reply) : Prop :=
  ∀ sc y k, σ.kheap sc = some (.schedContext y k) → r ∈ y.scReplies →
    (y.scReplies.head? = some r → xr.replySc = some sc) ∧ (y.scReplies.head? ≠ some r → xr.replySc = none) ∧
    (∀ r' ∈ y.scReplies.tail, ∃ x', σ.kheap r' = some (.reply x')) ∧
    (∀ f, y.scTcb = some f → ∃ xf, σ.kheap f = some (.tcb xf))

/-- **`reply_remove` has an outcome.** -/
theorem replyRemove_out {σ : State Unit} {tp r : ObjRef} {xr : Reply} {xt : Tcb}
    (hkr : σ.kheap r = some (.reply xr)) (hrt : xr.replyTcb = some tp) (hkt : σ.kheap tp = some (.tcb xt))
    (hst : xt.tcbState = .blockedOnReply r) (hsc : ScRepOK σ r xr) (hA : ActReady σ) :
    ∃ σ', ((), σ') ∈ (replyRemove (Z := Unit) tp r σ).1 := by
  have htr : tp ≠ r := by rintro rfl; rw [hkt] at hkr; cases hkr
  have fin : ∀ σr : State Unit, (∃ xr', σr.kheap r = some (.reply xr') ∧ xr'.replyTcb = some tp) →
      (∃ xt', σr.kheap tp = some (.tcb xt') ∧ xt'.tcbState = .blockedOnReply r) →
      ∃ σ', ((), σ') ∈ (replyUnlinkTcb (Z := Unit) tp r σr).1 := by
    rintro σr ⟨xr', hkr', hrt'⟩ ⟨xt', hkt', hst'⟩
    have hk' : (updK σr r (.reply { xr' with replyTcb := none })).kheap tp = some (.tcb xt') := by
      simp only [updK, Function.update_of_ne htr]; exact hkt'
    rw [replyUnlinkTcb_eq hkr' hrt' hkt' (Or.inl hst') htr, setThreadState_eq' hk' .inactive]
    exact ⟨_, Set.mem_singleton _⟩
  unfold replyRemove
  rw [nd_bind_one (getReply_eq hkr), nd_bind_one (show NonDet.assert (σ := State Unit) (xr.replyTcb = some tp) σ =
    ({((), σ)}, False) by simp [NonDet.assert, hrt]), Notif.nd_gets_bind]
  cases hw : scWithReply r σ with
  | none =>
    obtain ⟨σ', h'⟩ := fin σ ⟨xr, hkr, hrt⟩ ⟨xt, hkt, hst⟩
    exact ⟨σ', by dsimp only; exact h'⟩
  | some sc =>
    obtain ⟨y, k, hks, hmem⟩ := scWithReply_mem hw
    obtain ⟨hh, hnh, htl, hf⟩ := hsc sc y k hks hmem
    obtain ⟨σU, hU, hFU⟩ := unlinkSc_out hks hkr hmem hh hnh htl
    have hktU := hFU.tcb tp xt hkt
    obtain ⟨xrU, hkrU, hrtU⟩ := hFU.rep r xr hkr
    obtain ⟨yU, hksU, -, -, hyt, -⟩ := hFU.s.sc sc y k hks
    have hAU : ActReady σU := hFU.s.actReady hA (Or.inl hFU.act)
    have hD : ∃ σD, ((), σD) ∈ (NonDet.when (the y.scReplies.head? = r ∧ xt.tcbSchedContext = none)
        (schedContextDonate (Z := Unit) sc tp) σU).1 ∧ DFr σU σD := by
      unfold NonDet.when
      split
      · exact donate_out hksU hktU (fun f e => by
          obtain ⟨xf, hxf⟩ := hf f (by rw [← hyt]; exact e); exact ⟨xf, hFU.tcb f xf hxf⟩) hAU
      · exact ⟨σU, Set.mem_singleton _, DFr.heq rfl⟩
    obtain ⟨σD, hmD, hDD⟩ := hD
    have hkrD : σD.kheap r = some (.reply xrU) := by
      rw [hDD.2.2 r (fun x h => by rw [hkrU] at h; cases h) (fun y k h => by rw [hkrU] at h; cases h)]
      exact hkrU
    obtain ⟨xtD, hktD, hstD⟩ := hDD.1 tp xt hktU
    obtain ⟨σ', h'⟩ := fin σD ⟨xrU, hkrD, by rw [hrtU, hrt]⟩ ⟨xtD, hktD, by rw [hstD, hst]⟩
    refine ⟨σ', ?_⟩
    dsimp only
    rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hks) _), nd_bind_one (getTcbObjRef_eq _ hkt),
      nd_bind_one hU]
    exact mem_bind_nd hmD h'

/-- **`cancel_ipc` of a thread receiving with reply `r`** has an outcome. -/
theorem cancelIpc_recv_out {σ : State Unit} {tp r ep : ObjRef} {d : ReceiverPayload} {xr : Reply} {xt : Tcb}
    {xe : Endpoint} (hkr : σ.kheap r = some (.reply xr)) (hrt : xr.replyTcb = some tp)
    (hkt : σ.kheap tp = some (.tcb xt)) (hst : xt.tcbState = .blockedOnReceive ep (some r) d)
    (hke : σ.kheap ep = some (.endpoint xe)) (hq : tp ∈ xe.epQueue) :
    ∃ σ', ((), σ') ∈ (cancelIpc (Z := Unit) tp σ).1 := by
  have htr : tp ≠ r := by rintro rfl; rw [hkt] at hkr; cases hkr
  have hte : tp ≠ ep := by rintro rfl; rw [hkt] at hke; cases hke
  have hre : r ≠ ep := by rintro rfl; rw [hkr] at hke; cases hke
  unfold cancelIpc
  obtain ⟨x1, hx1⟩ : ∃ x1 : Tcb, x1 = { xt with tcbFault := none } := ⟨_, rfl⟩
  obtain ⟨σ1, hσ1⟩ : ∃ σ1, σ1 = updK σ tp (.tcb x1) := ⟨_, rfl⟩
  have hts : threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) tp σ = ({((), σ1)}, False) := by
    rw [hσ1, hx1]; exact threadSet_eq _ hkt
  rw [nd_bind_one (getThreadState_eq hkt), nd_bind_one hts, hst]
  have hke1 : σ1.kheap ep = some (.endpoint xe) := by simp only [hσ1, updK, Function.update_of_ne (Ne.symm hte)]; exact hke
  set σ2 := updK σ1 ep (.endpoint (epDeq xe tp)) with hσ2
  have hkr2 : σ2.kheap r = some (.reply xr) := by
    simp only [hσ2, hσ1, updK, Function.update_of_ne hre, Function.update_of_ne (Ne.symm htr)]; exact hkr
  have hkt2 : σ2.kheap tp = some (.tcb x1) := by simp [hσ2, hσ1, updK, hte]
  set σ3 := updK σ2 r (.reply { xr with replyTcb := none }) with hσ3
  have hkt3 : σ3.kheap tp = some (.tcb x1) := by simp only [hσ3, updK, Function.update_of_ne htr]; exact hkt2
  have hx1s : x1.tcbState = .blockedOnReceive ep (some r) d := by rw [hx1]; exact hst
  have hu : replyUnlinkTcb (Z := Unit) tp r σ2 =
      ({((), stsAct (updK σ3 tp (.tcb { x1 with tcbState := .inactive })) tp)}, False) :=
    (replyUnlinkTcb_eq hkr2 hrt hkt2 (Or.inr ⟨ep, d, hx1s⟩) htr).trans (setThreadState_eq' hkt3 .inactive)
  set σ4 := stsAct (updK σ3 tp (.tcb { x1 with tcbState := .inactive })) tp with hσ4
  have hkt4 : σ4.kheap tp = some (.tcb { x1 with tcbState := .inactive }) := by
    rw [hσ4, (stsAct_heap _ tp).1]; simp [updK]
  unfold blockedCancelIpc getBlockingObject
  dsimp only
  rw [nd_bind_one (show NonDet.assertOpt (σ := State Unit) (epBlocked (.blockedOnReceive ep (some r) d)) σ1 =
      ({(ep, σ1)}, False) from rfl),
    nd_bind_one (tcbEpDequeue_eq hke1 hq)]
  rw [nd_bind_one hu, setThreadState_eq' hkt4 .inactive]
  exact ⟨_, Set.mem_singleton _⟩

/-- **What the finalisation of a reply cap needs of the spec state**: the
reply exists; its thread (if any) is a TCB blocked on it, receiving (and
queued on the endpoint) or on the reply (with `ScRepOK` and `ActReady`). -/
def ReplyPre (σ : State Unit) (r : ObjRef) : Prop :=
  ∃ xr, σ.kheap r = some (.reply xr) ∧ ∀ tp, xr.replyTcb = some tp → ∃ xt, σ.kheap tp = some (.tcb xt) ∧
    ((xt.tcbState = .blockedOnReply r ∧ ScRepOK σ r xr ∧ ActReady σ) ∨
      ∃ ep d xe, xt.tcbState = .blockedOnReceive ep (some r) d ∧ σ.kheap ep = some (.endpoint xe) ∧
        tp ∈ xe.epQueue)

/-- **The spec's finalisation of a final reply cap has an outcome.** -/
theorem finReply_out {σ : State Unit} {r : ObjRef} (R : CapRights) (h : ReplyPre σ r) :
    ∃ σ', ((Cap.nullCap, Cap.nullCap), σ') ∈ (finaliseCap (Z := Unit) (.replyCap r R) true σ).1 := by
  obtain ⟨xr, hkr, ht⟩ := h
  have hbody : ∃ σ', ((), σ') ∈ ((getReplyTcb (Z := Unit) r >>= fun tptr => match tptr with
      | none => return ()
      | some tp => do
        let state ← getThreadState tp
        match state with
        | .blockedOnReply r => replyRemove tp r
        | _ => cancelIpc tp) σ).1 := by
    rw [nd_bind_one (getReplyTcb_eq hkr)]
    cases hrt : xr.replyTcb with
    | none => exact ⟨σ, Set.mem_singleton _⟩
    | some tp =>
      obtain ⟨xt, hkt, hcase⟩ := ht tp hrt
      dsimp only
      rw [nd_bind_one (getThreadState_eq hkt)]
      rcases hcase with ⟨hst, hsc, hA⟩ | ⟨ep, d, xe, hst, hke, hq⟩
      · rw [hst]; exact replyRemove_out hkr hrt hkt hst hsc hA
      · rw [hst]; exact cancelIpc_recv_out hkr hrt hkt hst hke hq
  obtain ⟨σ', h'⟩ := hbody
  refine ⟨σ', ?_⟩
  unfold finaliseCap
  simp only [NonDet.liftM, NonDet.when, ↓reduceIte]
  exact mem_bind_nd (x := ((), σ')) h' (Set.mem_singleton _)

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The spec's side of a final reply cap's finalisation**: the spec state
meets `ReplyPre` at the reply. -/
def ReplySpecHyp (th : TypedHeap) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (p : U64) (g : Bool),
    DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Reply p g) →
    Fl4Spec.isFinalCap' (absCap (.Reply p g)) σ → ReplyPre σ p.bv

/-- **`SpecFinOut` for the reply caps.** -/
theorem specFinOut_reply (th : TypedHeap) (h : ReplySpecHyp (L := L) th) : SpecFinOut (L := L) FinReplyK th := by
  intro s σ G sl c hk hDS hA hc hfin
  obtain ⟨p, g, rfl⟩ := hk
  exact finReply_out _ (h s σ G sl p g hDS hA hc hfin)

end

end Fl4Proofs.P3.Sched
