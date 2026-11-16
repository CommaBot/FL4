/-
P3 (DESIGN.md §9), TCB invocations: **the spec side of `ReadRegisters`**
(`ReadRegsSpecHyp`).

* `XK p σ σ'`: every TCB other than `p` and every arch object is unchanged;
  `PXK p m`, every outcome of `m` is `XK p`-related to its start; built from
  the monad's combinators and `set_object` (of no arch object, and of a TCB
  only at `p`): `pxk_cancelIpc`, `pxk_suspend`, `pxk_asUser`.
* `dk_suspend`: `suspend` keeps the domain schedule (`DK`, VsDom).
* `cancelOK_off`: `cancel_ipc`'s facts carried to a state differing only at
  another TCB.
* `readRegsSpecHyp_of`: from `SchedValid` and `BufSpecHyp` at the decode's
  state, the target a TCB other than the caller.
-/
import Fl4Proofs.P3.TcbHypsX
import Fl4Proofs.P3.VsDom
import Fl4Proofs.P3.EpFaultUs
import Fl4Proofs.P3.SpecFinFrames
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

namespace Sched
open Fl4Spec

/-! ## `XK`: the other TCBs and the arch objects kept -/

/-- Every TCB other than `p`, and every arch object, unchanged. -/
def XK (p : ObjRef) (σ σ' : State Unit) : Prop :=
  (∀ q x, q ≠ p → σ.kheap q = some (.tcb x) → σ'.kheap q = some (.tcb x)) ∧
  (∀ q a, σ.kheap q = some (.archObj a) → σ'.kheap q = some (.archObj a))

theorem XK.refl (p : ObjRef) (σ : State Unit) : XK p σ σ := ⟨fun _ _ _ h => h, fun _ _ h => h⟩

theorem XK.trans {p : ObjRef} {σ1 σ2 σ3 : State Unit} (h1 : XK p σ1 σ2) (h2 : XK p σ2 σ3) : XK p σ1 σ3 :=
  ⟨fun q x hq h => h2.1 q x hq (h1.1 q x hq h), fun q a h => h2.2 q a (h1.2 q a h)⟩

theorem XK.of_kheap {p : ObjRef} {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : XK p σ σ' :=
  ⟨fun _ _ _ hk => by rw [h]; exact hk, fun _ _ hk => by rw [h]; exact hk⟩

/-- Every outcome of `m` is `XK p`-related to its start. -/
def PXK (p : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → XK p σ x.2

section Comb
variable {p : ObjRef}

theorem pxk_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : PXK p m)
    (hg : ∀ a, PXK p (g a)) : PXK p (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem pxk_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : PXK p m)
    (hg : ∀ a, PXK p (g a)) : PXK p (NonDet.bind m g) := pxk_bind hm hg

theorem pxk_pure {α : Type} (a : α) : PXK p (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact XK.refl p σ

theorem pxk_pure' {α : Type} (a : α) : PXK p (NonDet.pure a : NonDet (State Unit) α) := pxk_pure a

theorem pxk_gets {α : Type} (g : State Unit → α) : PXK p (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact XK.refl p σ

theorem pxk_assert (P : Prop) : PXK p (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact XK.refl p σ

theorem pxk_fail {α : Type} : PXK p (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem pxk_assertOpt {α : Type} (o : Option α) : PXK p (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact pxk_fail
  · exact pxk_pure' _

theorem pxk_getsThe {α : Type} (g : State Unit → Option α) : PXK p (NonDet.getsThe g) := by
  intro σ x hx; exact pxk_assertOpt (g σ) σ x hx

theorem pxk_selectF {α : Type} (S : Set α × Prop) : PXK p (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact XK.refl p σ

theorem pxk_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : PXK p m1)
    (h2 : PXK p m2) : PXK p (if P then m1 else m2) := by
  split <;> assumption

theorem pxk_when {P : Prop} {inst : Decidable P} {m : NonDet (State Unit) Unit} (h : PXK p m) :
    PXK p (@NonDet.when _ P inst m) := by
  unfold NonDet.when; split; exact h; exact pxk_pure' _

theorem pxk_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, PXK p (g a)) :
    ∀ o, PXK p (NonDet.maybeM g o)
  | none => pxk_pure' _
  | some a => h a

theorem pxk_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : PXK p m) :
    PXK p (NonDet.liftM g m) := by
  unfold NonDet.liftM; exact pxk_bind h (fun _ => pxk_pure _)

theorem pxk_modify {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap) :
    PXK p (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact XK.of_kheap (hg σ)

theorem pxk_getObject (q : ObjRef) : PXK p (getObject (Z := Unit) q) := pxk_getsThe _

/-- `set_object` of no arch object, and of a TCB only at `p`. -/
theorem pxk_setObject {q : ObjRef} {o : KernelObject} (h1 : ∀ t, o = .tcb t → q = p)
    (h2 : ∀ a, o ≠ .archObj a) : PXK p (setObject (Z := Unit) q o) := by
  intro σ x hx
  obtain ⟨k, hk, hty, e⟩ := setObject_mem hx
  rw [e]
  refine ⟨fun q' x' hq' hk' => ?_, fun q' a hk' => ?_⟩
  · by_cases h : q' = q
    · subst h
      rw [hk] at hk'; cases hk'
      exfalso
      cases o with
      | tcb t => exact hq' (h1 t rfl)
      | cnode r cs => simp only [aType] at hty; split_ifs at hty <;> cases hty
      | schedContext y n => simp only [aType] at hty; split_ifs at hty <;> cases hty
      | _ => cases hty
    · simp only [Function.update_of_ne h]; exact hk'
  · by_cases h : q' = q
    · subst h
      rw [hk] at hk'; cases hk'
      exfalso
      cases o with
      | archObj a' => exact h2 a' rfl
      | cnode r cs => simp only [aType] at hty; split_ifs at hty <;> cases hty
      | schedContext y n => simp only [aType] at hty; split_ifs at hty <;> cases hty
      | _ => cases hty
    · simp only [Function.update_of_ne h]; exact hk'

end Comb

/-! ### The spec functions of `suspend` -/

section Fns
variable {p : ObjRef}

theorem pxk_threadSet (f : Tcb → Tcb) : PXK p (threadSet (Z := Unit) f p) := by
  unfold threadSet
  exact pxk_bind (pxk_getsThe _) (fun _ => pxk_setObject (fun _ _ => rfl) (fun _ h => by cases h))

theorem pxk_threadGet {α : Type} (f : Tcb → α) (q : ObjRef) : PXK p (threadGet (Z := Unit) f q) := by
  unfold threadGet; exact pxk_bind (pxk_getsThe _) (fun _ => pxk_pure _)

theorem pxk_setThreadState (ts : ThreadState) : PXK p (setThreadState (Z := Unit) p ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction
  exact pxk_bind (pxk_threadSet _) (fun _ => pxk_bind (pxk_gets _) (fun _ => pxk_bind (pxk_gets _) (fun _ =>
    pxk_bind (pxk_gets _) (fun _ => pxk_when (pxk_modify (fun _ => rfl))))))

theorem pxk_getSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    PXK p (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo
  refine pxk_bind (pxk_getObject _) (fun _ => pxk_bind (pxk_assert _) (fun _ => ?_))
  split
  · exact pxk_pure _
  · exact pxk_fail

theorem pxk_setSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α)
    (h1 : ∀ t, C e ≠ .tcb t) (h2 : ∀ a, C e ≠ .archObj a) : PXK p (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo
  exact pxk_bind (pxk_getObject _) (fun _ => pxk_bind (pxk_assert _) (fun _ => pxk_bind (pxk_assert _)
    (fun _ => pxk_setObject (fun t h => absurd h (h1 t)) h2)))

theorem pxk_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef)
    (h1 : ∀ a t, C a ≠ .tcb t) (h2 : ∀ a b, C a ≠ .archObj b) :
    PXK p (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef
  exact pxk_bind (pxk_getSimpleKo _ _) (fun _ => pxk_setSimpleKo _ _ _ (h1 _) (h2 _))

theorem pxk_getSchedContext (q : ObjRef) : PXK p (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext
  refine pxk_bind (pxk_getObject _) (fun o => ?_)
  cases o <;> first | exact pxk_pure _ | exact pxk_fail

theorem pxk_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext) :
    PXK p (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext
  refine pxk_bind (pxk_getObject _) (fun o => ?_)
  cases o <;> first
    | exact pxk_setObject (fun _ h => by cases h) (fun _ h => by cases h)
    | exact pxk_fail

theorem pxk_replyUnlinkTcb (r : ObjRef) : PXK p (replyUnlinkTcb (Z := Unit) p r) := by
  unfold replyUnlinkTcb getThreadState
  exact pxk_bind (pxk_getSimpleKo _ _) (fun _ => pxk_bind (pxk_assert _) (fun _ =>
    pxk_bind (pxk_threadGet _ _) (fun _ => pxk_bind (pxk_assert _) (fun _ =>
      pxk_bind (pxk_updateSkObjRef _ _ _ _ (fun _ _ h => by cases h) (fun _ _ h => by cases h)) (fun _ =>
        pxk_setThreadState _)))))

theorem pxk_cancelIpc : PXK p (cancelIpc (Z := Unit) p) := by
  unfold cancelIpc getThreadState
  refine pxk_bind (pxk_threadGet _ _) (fun st => pxk_bind (pxk_threadSet _) (fun _ => ?_))
  have hb : ∀ (ts : ThreadState) (ro : Option ObjRef), PXK p (blockedCancelIpc (Z := Unit) ts p ro) := by
    intro ts ro
    unfold blockedCancelIpc getBlockingObject tcbEpDequeue
    refine pxk_bind (pxk_assertOpt _) (fun _ => pxk_bind ?_ (fun _ => ?_))
    · exact pxk_bind (pxk_getSimpleKo _ _) (fun _ => pxk_bind (pxk_pure _) (fun _ => pxk_bind (pxk_assert _)
        (fun _ => pxk_bind (pxk_pure _) (fun _ => pxk_bind (pxk_pure _) (fun _ =>
          pxk_setSimpleKo _ _ _ (fun _ h => by cases h) (fun _ h => by cases h))))))
    · cases ro <;> dsimp only
      · exact pxk_setThreadState _
      · exact pxk_bind (pxk_replyUnlinkTcb _) (fun _ => pxk_setThreadState _)
  split
  · exact hb _ _
  · exact hb _ _
  · unfold cancelSignal tcbNtfnDequeue
    refine pxk_bind ?_ (fun _ => pxk_setThreadState _)
    exact pxk_bind (pxk_getSimpleKo _ _) (fun _ => pxk_bind (pxk_pure _) (fun _ => pxk_bind (pxk_assert _)
      (fun _ => pxk_bind (pxk_pure _) (fun _ => pxk_bind (pxk_pure _) (fun _ =>
        pxk_setSimpleKo _ _ _ (fun _ h => by cases h) (fun _ h => by cases h))))))
  · unfold replyRemoveTcb getThreadState getReplyObjRef getSkObjRef
    refine pxk_bind (pxk_threadGet _ _) (fun _ => pxk_bind (pxk_assert _) (fun _ => pxk_bind (pxk_gets _)
      (fun o => ?_)))
    cases o <;> dsimp only
    · exact pxk_replyUnlinkTcb _
    · exact pxk_bind (pxk_liftM _ (pxk_getSchedContext _)) (fun _ => pxk_bind (pxk_bind (pxk_getSimpleKo _ _)
        (fun _ => pxk_pure _)) (fun _ => pxk_bind (pxk_assert _) (fun _ => pxk_bind (pxk_updateSchedContext _ _)
          (fun _ => pxk_bind (pxk_updateSkObjRef _ _ _ _ (fun _ _ h => by cases h) (fun _ _ h => by cases h))
            (fun _ => pxk_replyUnlinkTcb _)))))
  · exact pxk_pure _

theorem pxk_asUser {α : Type} (u : UserMonad α) : PXK p (asUser (Z := Unit) p u) := by
  unfold asUser
  refine pxk_bind (pxk_getsThe _) (fun _ => pxk_bind (pxk_pure _) (fun _ => pxk_bind (pxk_selectF _) (fun r => ?_)))
  obtain ⟨a, uc'⟩ := r
  exact pxk_bind (pxk_pure _) (fun _ => pxk_bind (pxk_setObject (fun _ _ => rfl) (fun _ h => by cases h))
    (fun _ => pxk_pure _))

theorem pxk_suspend : PXK p (suspend (Z := Unit) p) := by
  unfold suspend updateRestartPc tcbSchedAction getTcbQueue setTcbQueue tcbReleaseRemove
    schedContextCancelYieldTo getTcbObjRef getThreadState
  refine pxk_bind pxk_cancelIpc (fun _ => pxk_bind (pxk_threadGet _ _) (fun _ =>
    pxk_bind (pxk_when (pxk_asUser _)) (fun _ => pxk_bind ?_ (fun _ => pxk_bind ?_ (fun _ =>
      pxk_bind ?_ (fun _ => pxk_setThreadState _))))))
  · exact pxk_bind (pxk_threadGet _ _) (fun _ => pxk_bind (pxk_threadGet _ _) (fun _ => pxk_bind
      (pxk_bind (pxk_gets _) (fun _ => pxk_pure _)) (fun _ => pxk_bind (pxk_pure _) (fun _ =>
        pxk_modify (fun _ => rfl)))))
  · exact pxk_bind (pxk_gets _) (fun _ => pxk_bind (pxk_when (pxk_modify (fun _ => rfl))) (fun _ =>
      pxk_bind (pxk_pure _) (fun _ => pxk_modify (fun _ => rfl))))
  · exact pxk_bind (pxk_threadGet _ _) (fun _ => pxk_maybeM (fun _ => pxk_bind (pxk_updateSchedContext _ _)
      (fun _ => pxk_threadSet _)) _)

end Fns


/-! ## `DK`: `suspend` keeps the domain schedule -/

section DKs
open Vs

theorem dk_threadSet' (f : Tcb → Tcb) (t : ObjRef) : DK (threadSet (Z := Unit) f t) := by
  unfold threadSet; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_threadSet' _ _)

theorem dk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : DK (threadGet (Z := Unit) f t) := by
  unfold threadGet; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_threadGet' _ _)

theorem dk_setThreadState' (t : ObjRef) (ts : ThreadState) : DK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setThreadState' _ _)

theorem dk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    DK (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getSimpleKo' _ _)

theorem dk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    DK (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setSimpleKo' _ _ _)

theorem dk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    DK (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_updateSkObjRef' _ _ _ _)

theorem dk_getSchedContext' (q : ObjRef) : DK (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getSchedContext' _)

theorem dk_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    DK (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_updateSchedContext' _ _)

theorem dk_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : DK (asUser (Z := Unit) t u) := by
  unfold asUser; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_asUser' _ _)

theorem dk_replyUnlinkTcb' (t r : ObjRef) : DK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_replyUnlinkTcb' _ _)

theorem dk_getThreadState' (t : ObjRef) : DK (getThreadState (Z := Unit) t) := by
  unfold getThreadState; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getThreadState' _)

theorem dk_cancelIpc' (t : ObjRef) : DK (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_cancelIpc' _)

theorem dk_suspend' (t : ObjRef) : DK (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc tcbSchedAction getTcbQueue setTcbQueue tcbReleaseRemove
    schedContextCancelYieldTo getTcbObjRef getThreadState
  dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_suspend' _)

end DKs

/-- **`cancel_ipc`'s facts** carried to a state differing only at the TCB `c`. -/
theorem cancelOK_off {σ σ' : State Unit} {c t : ObjRef} {x xc yc : Tcb} (hc : σ.kheap c = some (.tcb xc))
    (hc' : σ'.kheap c = some (.tcb yc)) (h : ∀ q, q ≠ c → σ'.kheap q = σ.kheap q) (hB : CancelOK σ t x) :
    CancelOK σ' t x := by
  have fw : ∀ q o, σ.kheap q = some o → (∀ y, o ≠ .tcb y) → σ'.kheap q = some o := fun q o hq ho => by
    have hne : q ≠ c := by rintro rfl; rw [hc] at hq; exact ho xc (Option.some.inj hq).symm
    rw [h q hne]; exact hq
  have bw : ∀ q o, σ'.kheap q = some o → (∀ y, o ≠ .tcb y) → σ.kheap q = some o := fun q o hq ho => by
    have hne : q ≠ c := by rintro rfl; rw [hc'] at hq; exact ho yc (Option.some.inj hq).symm
    rw [← h q hne]; exact hq
  obtain ⟨h1, h2, h3, h4, h5⟩ := hB
  refine ⟨fun ep pl e => ?_, fun ep ro d e => ?_, fun ep rp d e => ?_, fun n e => ?_, fun rp e => ?_⟩
  · obtain ⟨xe, hke, hq⟩ := h1 ep pl e; exact ⟨xe, fw _ _ hke (fun _ h => by cases h), hq⟩
  · obtain ⟨xe, hke, hq⟩ := h2 ep ro d e; exact ⟨xe, fw _ _ hke (fun _ h => by cases h), hq⟩
  · obtain ⟨xr, hkr, hq⟩ := h3 ep rp d e; exact ⟨xr, fw _ _ hkr (fun _ h => by cases h), hq⟩
  · obtain ⟨xn, hkn, hq⟩ := h4 n e; exact ⟨xn, fw _ _ hkn (fun _ h => by cases h), hq⟩
  · obtain ⟨xr, hkr, hrt, hsc⟩ := h5 rp e
    exact ⟨xr, fw _ _ hkr (fun _ h => by cases h), hrt, fun sc y k hks hm =>
      hsc sc y k (bw _ _ hks (fun _ h => by cases h)) hm⟩

end Sched

open Sched in
/-- **`ReadRegsSpecHyp`**: the spec's `read_registers` of a TCB other than the
caller: `suspend` when asked (an outcome by `suspend_out`, from `SchedValid`
at the decode's state; the caps kept, `nkc_suspend`; the domain schedule,
`dk_suspend'`; the caller's TCB and the user frames, `pxk_suspend`), then
reading the target's registers (`asUser_read_eq`). -/
theorem readRegsSpecHyp_of {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {th : TypedHeap}
    {G : MdbGhost} {σ : Fl4Spec.State Unit} {ct p : U64} (hpt : th p = some .tcb)
    (hcur : σ.curThread = ct.bv) (hkt : ∃ x, σ.kheap ct.bv = some (.tcb x)) (hV : SchedValid σ)
    (hB : BufSpecHyp σ ct.bv) :
    ReadRegsSpecHyp (L := L) th G σ ct p := by
  intro s1 σ1 flags n blk call don hne hst hRL
  obtain ⟨x0, hk0⟩ := hkt
  have hk0' : σ.kheap σ.curThread = some (.tcb x0) := by rw [hcur]; exact hk0
  have e1 := Notif.setThreadState_eq (Z := Unit) .restart hk0'
  rw [hst] at e1
  have hσ1 : σ1 = Notif.stsAct (Notif.updK σ σ.curThread (.tcb { x0 with tcbState := .restart })) σ.curThread := by
    have := congrArg (fun y => y.1) e1; simpa using this
  have hk1 : σ1.kheap ct.bv = some (.tcb { x0 with tcbState := .restart }) := by
    rw [hσ1, Notif.stsAct_kheap, ← hcur]; simp [Notif.updK]
  have hoff : ∀ q, q ≠ ct.bv → σ1.kheap q = σ.kheap q := fun q hq => by
    rw [hσ1, Notif.stsAct_kheap, hcur]; simp only [Notif.updK, Function.update_of_ne hq]
  have hne' : p.bv ≠ ct.bv := by rw [Ne, bv_eq_iff']; exact hne
  obtain ⟨xp, hkp, -⟩ := hRL.1.1.tcb p hpt
  have hkp0 : σ.kheap p.bv = some (.tcb xp) := by rw [← hoff _ hne']; exact hkp
  have hB1 : BufSpecHyp σ1 ct.bv := by
    intro x' q hx' hq k hk
    rw [hk1] at hx'; cases hx'
    obtain ⟨g1, g2⟩ := hB x0 q hk0 hq k hk
    refine ⟨g1, ?_⟩
    obtain ⟨sz, hsz⟩ := g2
    refine ⟨sz, ?_⟩
    have hne : (Endp.bufAddr q k &&& ~~~(Fl4Spec.mask (Fl4Spec.pageBitsForSize sz))) ≠ ct.bv := by
      intro e; rw [e, hk0] at hsz; cases hsz
    rw [hoff _ hne]; exact hsz
  obtain ⟨σ2, h2, xp2, hkp2⟩ : ∃ σ2, ((), σ2) ∈ (Fl4Spec.NonDet.when (Fl4Spec.testBit flags.bv 0)
      (Fl4Spec.suspend (Z := Unit) p.bv) σ1).1 ∧ ∃ x, σ2.kheap p.bv = some (.tcb x) := by
    unfold Fl4Spec.NonDet.when
    split_ifs
    · have hC := cancelOK_off hk0 hk1 hoff (cancelOK_of_valid hV hkp0 (KF.heq rfl) hkp0 rfl)
      obtain ⟨σ2, h2, x2, hk2⟩ := suspend_out hkp hC (fun q e => by
        obtain ⟨y, k, hq⟩ := hV.tcbYieldTo p.bv xp q hkp0 e
        have hqc : q ≠ ct.bv := by rintro rfl; rw [hk0] at hq; cases hq
        exact ⟨y, k, by rw [hoff q hqc]; exact hq⟩)
      exact ⟨σ2, h2, x2, hk2⟩
    · exact ⟨σ1, Set.mem_singleton _, xp, hkp⟩
  have hK2 : CKeep σ1 σ2 := nkc_when (nkc_suspend _) σ1 _ h2
  have hD2 := Vs.dk_when _ (dk_suspend' p.bv) σ1 _ h2
  have hX2 : XK p.bv σ1 σ2 := pxk_when pxk_suspend σ1 _ h2
  set regs := (Fl4Spec.frame_registers ++ Fl4Spec.gp_registers).take (Fl4Spec.unat n.bv) with hregs
  have hrd := Endp.asUser_read_eq hkp2 (f := Fl4Spec.NonDet.mapM Fl4Spec.getRegister regs)
    (Endp.mapM_getRegister _ _)
  refine ⟨regs.map (Fl4Spec.archTcbContextGet xp2.tcbArch).userRegs, σ2, { x0 with tcbState := .restart },
    mem_liftE (x := (regs.map (Fl4Spec.archTcbContextGet xp2.tcbArch).userRegs, σ2)) ?_,
    ⟨⟨hRL.1.1.of_ckeep hK2, hRL.1.2.1, hRL.1.2.2.1,
      hRL.1.2.2.2.1.of_same (SlotsSame.refl _ _) hK2.cdt hK2.orig, hRL.1.2.2.2.2⟩,
      hRL.2.1.of_same hRL.1.2.2.1 (SlotsSame.refl _ _) hK2.ks, hRL.2.2.1,
      hRL.2.2.2.of_same (DomSame.refl _ _) hD2.1 hD2.2⟩,
    hX2.1 ct.bv _ (Ne.symm hne') hk1, rfl, fun _ q hq z hz => ?_⟩
  · show _ ∈ ((do
      Fl4Spec.NonDet.when (Fl4Spec.testBit flags.bv 0) (Fl4Spec.suspend p.bv)
      let _self ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
      let regs ← pure ((Fl4Spec.frame_registers ++ Fl4Spec.gp_registers).take (Fl4Spec.unat n.bv))
      Fl4Spec.asUser p.bv (Fl4Spec.NonDet.mapM Fl4Spec.getRegister regs)) σ1).1
    refine mem_bind_nd (x := ((), σ2)) (by convert h2) ?_
    rw [Notif.nd_gets_bind, Notif.nd_pure_bind', hrd]
    exact Set.mem_singleton _
  · obtain ⟨g1, sz, hsz⟩ := hB1 _ q hk1 hq z.1 (mrPairs_lt hz)
    exact ⟨g1, sz, hX2.2 _ _ hsz⟩

end

end Fl4Proofs.P3
