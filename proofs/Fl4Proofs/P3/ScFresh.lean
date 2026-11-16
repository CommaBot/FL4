/-
P3, scheduling contexts: **the relations over fresh objects** (UtXHyp's
new-object part): retype's new TCBs, notifications, endpoints and replies
join the object sets.

* `SpecAdd σ σ' W o`: the spec's state after adding the objects `o p` at the
  fresh addresses `W` (none there before), all else kept.
* `SchedCore.add_tcbs`, `SchedSpec.add_tcbs`, `SchedRel.add_tcbs`: with FL4's
  memory agreeing with the old on what the relation reads (`SAgree`), the new
  TCBs' scheduler words zero (`SchedField`), the new TCBs placed apart from the
  old ones, the node, the kernel-global block, the notifications and the SCs,
  and the spec's new TCBs `default_tcb 0`, the relation holds over `T ∪ W`.
  A new TCB's affinity word is 0, so this is for core 0 (`c = 0`).
* `SchedRel.add_ntfns`: fresh notifications, placed apart.
* `NtfnStateRel.add`: fresh notifications (idle, unbound, no SC) and TCBs
  (inactive, badge register and priority zero), the old words kept.
* `EpStateRel.add`: from the relation over the old sets at the state after,
  fresh endpoints (idle), replies (no TCB) and TCBs (inactive, no fault, no
  bound notification, `new_context`'s registers). With `NtfnStateRel.add`
  and the SC words, `IpcRel.of` gives the merged relation.

Fresh SCs are not added: `ScRel1.wf` (`RefillsWF`) asks `MIN_REFILLS ≤
REFILL_MAX` of every SC of `C`, and a fresh SC's `REFILL_MAX` is 0 (the
spec's `default_sched_context` has `sc_refill_max = 0`); P1 asks `RefillsWF`
only of active SCs.
-/
import Fl4Proofs.P3.ScXProd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-- **The spec's state with fresh objects added** (module docstring). -/
structure SpecAdd (σ σ' : Fl4Spec.State Unit) (W : Fl4Spec.ObjRef → Prop) (o : Fl4Spec.ObjRef → Fl4Spec.KernelObject) :
    Prop where
  exst : σ'.exst = σ.exst
  abs : { σ'.toAbstractState with kheap := σ.kheap } = σ.toAbstractState
  new : ∀ p, W p → σ.kheap p = none ∧ σ'.kheap p = some (o p)
  old : ∀ p, ¬ W p → σ'.kheap p = σ.kheap p

section
variable {σ σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop} {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject}

theorem SpecAdd.kold (h : SpecAdd σ σ' W o) {p : Fl4Spec.ObjRef} {k : Fl4Spec.KernelObject}
    (hk : σ.kheap p = some k) : σ'.kheap p = some k := by
  by_cases hp : W p
  · rw [(h.new p hp).1] at hk; cases hk
  · rw [h.old p hp]; exact hk

theorem SpecAdd.kback (h : SpecAdd σ σ' W o) {p : Fl4Spec.ObjRef} {k : Fl4Spec.KernelObject}
    (hk : σ'.kheap p = some k) : σ.kheap p = some k ∨ (W p ∧ k = o p) := by
  by_cases hp : W p
  · rw [(h.new p hp).2] at hk; exact Or.inr ⟨hp, (Option.some.inj hk).symm⟩
  · rw [h.old p hp] at hk; exact Or.inl hk

theorem SpecAdd.f (h : SpecAdd σ σ' W o) :
    σ'.readyQueues = σ.readyQueues ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.curThread = σ.curThread ∧
    σ'.schedulerAction = σ.schedulerAction ∧ σ'.curSc = σ.curSc ∧ σ'.curTime = σ.curTime ∧
    σ'.consumedTime = σ.consumedTime ∧ σ'.reprogramTimer = σ.reprogramTimer ∧ σ'.curDomain = σ.curDomain ∧
    σ'.domainTime = σ.domainTime ∧ σ'.idleThread = σ.idleThread := by
  have e := h.abs
  exact ⟨(by have := congrArg Fl4Spec.AbstractState.readyQueues e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.releaseQueue e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.curThread e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.schedulerAction e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.curSc e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.curTime e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.consumedTime e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.reprogramTimer e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.curDomain e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.domainTime e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.idleThread e; exact this)⟩

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem nwrite_union {N T W : Set U64} {a : U64} (h : NWrite N (T ∪ W) a) : NWrite N T a ∨ NWrite ∅ W a := by
  rcases h with h | ⟨t, ht, e⟩
  · exact Or.inl (Or.inl h)
  · rcases ht with ht | ht
    · exact Or.inl (Or.inr ⟨t, ht, e⟩)
    · exact Or.inr (Or.inr ⟨t, ht, e⟩)

/-- A new TCB's `NWrite` word is in its block. -/
theorem nwrite_new {W : Set U64} (hW : TcbPlaced W) {a : U64} (h : NWrite ∅ W a) :
    ∃ t ∈ W, t.val ≤ a.val ∧ a.val < t.val + 4096 := by
  rcases nwrite_range (⟨hW, fun _ h => h.elim, fun _ h => h.elim⟩ : NPlaced W ∅) h with ⟨n, hn, -⟩ | h
  · exact hn.elim
  · exact h

/-- **The core lists over the new TCBs** (module docstring). -/
theorem SchedCore.add_tcbs {T W : Set U64} {c : U64} {s : S} {Q : U64 → List U64} {R : List U64}
    (h : SchedCore st T c s Q R) (hW : ∀ t ∈ W, TcbAddr t ∧ t ∉ T) (hc0 : c = 0#u64)
    (hnd : ∀ t ∈ W, t.val + 2 ^ 12 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ t.val)
    (hks : ∀ t ∈ W, t.val + 2 ^ 12 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val)
    (hm : ∀ t ∈ W, ∀ K, SchedField K → L.mem s (core.num.U64.wrapping_add t K) = 0#u64) :
    SchedCore st (T ∪ W) c s Q R := by
  have hQ : ∀ p : U64, p.val < 256 → ∀ t ∈ Q p, t ∈ T := fun p hp t ht => (h.ready.1.rel p hp).mem t ht
  have hR : ∀ t ∈ R, t ∈ T := fun t ht => h.release.mem t ht
  have z : ∀ t ∈ W, ∀ K, SchedField K → L.mem s (core.num.U64.wrapping_add t K) = 0#u64 := hm
  refine ⟨fun t ht => ?_, ⟨h.node.align, h.node.fits, fun t ht => ?_⟩, h.cur, fun t ht => ?_, fun t ht => ?_,
    ⟨⟨fun p hp => ?_, h.ready.1.disj⟩, h.ready.2⟩, ?_, h.inQ, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
    Or.inl h.curT, Or.inl h.idleT, fun t ht => ?_⟩
  · rcases ht with ht | ht
    · exact h.tcbs t ht
    · exact (hW t ht).1
  · rcases ht with ht | ht
    · exact h.node.disj t ht
    · exact hnd t ht
  · rcases ht with ht | ht
    · exact h.aff t ht
    · rw [hc0]; exact z t ht 3520#u64 (by simp [SchedField])
  · rcases ht with ht | ht
    · exact h.prio t ht
    · show (L.mem s (core.num.U64.wrapping_add t 3448#u64)).val < 256
      rw [z t ht 3448#u64 (by simp [SchedField])]; decide
  · have q := h.ready.1.rel p hp
    exact ⟨q.nodup, fun t ht => Or.inl (q.mem t ht), q.head, q.last, q.seg⟩
  · have q := h.release
    exact ⟨q.nodup, fun t ht => Or.inl (q.mem t ht), q.head, q.last, q.seg⟩
  · rcases ht with ht | ht
    · exact h.queued t ht
    · have hn : t ∉ T := (hW t ht).2
      have e : L.mem s (inqA t) = 0#u64 := z t ht 3592#u64 (by simp [SchedField])
      have hp : (L.mem s (prioA t)).val < 256 := by
        show (L.mem s (core.num.U64.wrapping_add t 3448#u64)).val < 256
        rw [z t ht 3448#u64 (by simp [SchedField])]; decide
      rw [e]
      constructor
      · intro h0; exact absurd (by unfold sched.Q_QUEUED; decide : (0#u64 &&& sched.Q_QUEUED) = 0#u64) h0
      · intro hq; exact absurd (hQ _ hp t hq) hn
  · rcases ht with ht | ht
    · exact h.released t ht
    · have hn : t ∉ T := (hW t ht).2
      have e : L.mem s (inqA t) = 0#u64 := z t ht 3592#u64 (by simp [SchedField])
      rw [e]
      constructor
      · intro h0; exact absurd (by unfold sched.Q_RELEASE; decide : (0#u64 &&& sched.Q_RELEASE) = 0#u64) h0
      · intro hr; exact absurd (hR t hr) hn
  · rcases ht with ht | ht
    · exact h.excl t ht
    · intro hq
      have hp : (L.mem s (prioA t)).val < 256 := by
        show (L.mem s (core.num.U64.wrapping_add t 3448#u64)).val < 256
        rw [z t ht 3448#u64 (by simp [SchedField])]; decide
      exact absurd (hQ _ hp t hq) (hW t ht).2
  · rcases ht with ht | ht
    · exact h.ksOut t ht
    · exact hks t ht

/-- The new TCBs' addresses in the spec. -/
def TW (W : Set U64) (p : Fl4Spec.ObjRef) : Prop := ∃ t ∈ W, t.bv = p

/-- **The spec side over the new TCBs** (module docstring). -/
theorem SchedSpec.add_tcbs {T C W : Set U64} {c : U64} {s : S} {Q : U64 → List U64} {R : List U64}
    {σ σ' : Fl4Spec.State Unit} (h : SchedSpec st T C c s Q R σ)
    (hσ : SpecAdd σ σ' (TW W) (fun _ => .tcb (Fl4Spec.defaultTcb 0)))
    (hm : ∀ t ∈ W, ∀ K, SchedField K → L.mem s (core.num.U64.wrapping_add t K) = 0#u64) :
    SchedSpec st (T ∪ W) C c s Q R σ' := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hσ.f
  refine ⟨fun p hp => by rw [e1]; exact h.rq p hp, fun d p hd => by rw [e1]; exact h.rqDom d p hd,
    by rw [e2]; exact h.rel, by rw [e3]; exact h.curThread, by rw [e5]; exact h.curSc, by rw [e6]; exact h.curTime,
    by rw [e7]; exact h.consumed, by rw [e9]; exact h.curDom, fun t ht => ?_, fun t ht => ?_,
    fun sc hsc => ?_, h.idleSc, by rw [e10]; exact h.domTime, by rw [e11]; exact h.idleTh⟩
  · rcases ht with ht | ht
    · obtain ⟨x, hk, h1, h2, h3, h4⟩ := h.tcb t ht
      exact ⟨x, hσ.kold hk, h1, h2, h3, h4⟩
    · refine ⟨_, (hσ.new _ ⟨t, ht, rfl⟩).2, rfl, hm t ht 3432#u64 (by simp [SchedField]), ?_, ?_⟩
      · show none = optRef (L.mem s (core.num.U64.wrapping_add t 3464#u64))
        rw [hm t ht 3464#u64 (by simp [SchedField]), optRef_zero]
      · show (L.mem s (core.num.U64.wrapping_add t 3448#u64)).val = (Fl4Spec.defaultPriority).toNat
        rw [hm t ht 3448#u64 (by simp [SchedField])]; rfl
  · rcases ht with ht | ht
    · exact h.scMem t ht
    · intro h0; exact absurd (hm t ht 3464#u64 (by simp [SchedField])) h0
  · obtain ⟨x, n, hk, e⟩ := h.scs sc hsc
    exact ⟨x, n, hσ.kold hk, e⟩

set_option maxHeartbeats 1000000 in
/-- **The scheduler relation over the new TCBs** (module docstring). -/
theorem SchedRel.add_tcbs {N T C W : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (ha : SAgree st T C c s s')
    (hact : nodeW st s' c layout.node.SCHED_ACTION = nodeW st s c layout.node.SCHED_ACTION)
    (hrp : nodeW st s' c layout.node.REPROGRAM = nodeW st s c layout.node.REPROGRAM)
    (hW : ∀ t ∈ W, TcbAddr t ∧ t ∉ T) (hc0 : c = 0#u64)
    (hnd : ∀ t ∈ W, t.val + 2 ^ 12 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ t.val)
    (hks : ∀ t ∈ W, t.val + 2 ^ 12 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val)
    (hnt : ∀ n ∈ N, ∀ t ∈ W, t.val + 4096 ≤ n.val ∨ n.val + 64 ≤ t.val)
    (hsc : ∀ sc ∈ C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → ∀ a : U64, ScObj sc n a →
      ∀ t ∈ W, a.val < t.val ∨ t.val + 4096 ≤ a.val)
    (hm : ∀ t ∈ W, ∀ K, SchedField K → L.mem s' (core.num.U64.wrapping_add t K) = 0#u64)
    (hσ : SpecAdd σ σ' (TW W) (fun _ => .tcb (Fl4Spec.defaultTcb 0))) :
    SchedRel st N (T ∪ W) C c s' σ' := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hPW : NPlaced W N := ⟨fun t ht => (hW t ht).1, hS.placed.ntfn, hnt⟩
  have hP' : NPlaced (T ∪ W) N := ⟨fun t ht => by
      rcases ht with ht | ht
      · exact hS.placed.tcb t ht
      · exact (hW t ht).1, hS.placed.ntfn, fun n hn t ht => by
      rcases ht with ht | ht
      · exact hS.placed.disj n hn t ht
      · exact hnt n hn t ht⟩
  have hTW : TcbPlaced W := fun t ht => (hW t ht).1
  have hk := ha.ksb
  have hnb : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hk]
  have hsz : SzKeep σ σ' := fun p x n hp => by
    rcases hσ.kback hp with h | ⟨-, h⟩
    · exact ⟨x, h⟩
    · cases h
  refine ⟨hP', fun o ho hn => ?_, fun hn => ?_, fun hn => ?_, fun sc hsC x n hx a hao => ?_, ?_,
    by rw [hact]; rcases hS.actW with h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h)),
    by rw [hact, hσ.f.2.2.2.1]; exact hS.act, by rw [hrp, hσ.f.2.2.2.2.2.2.2.1]; exact hS.repr,
    hs.core_eq ha.sc hS.core, Q, R, (hc.agree ha.toC).add_tcbs hW hc0 (by rw [hnb]; exact hnd) (by rw [hk]; exact hks) hm,
    (hs.agree ha).add_tcbs hσ hm⟩
  · rcases nwrite_union hn with h | h
    · rw [nodeAt_ksb hk] at h; exact hS.nodeNW o ho h
    · obtain ⟨t, ht, g1, g2⟩ := nwrite_new hTW h
      have hv := nodeAt_val hc.node ho
      rw [nodeAt_ksb hk] at g1 g2
      rw [hv] at g1 g2
      have := hnd t ht; omega
  · rcases nwrite_union hn with h | h
    · rw [curDomA_ksb hk] at h; exact hS.domNW h
    · obtain ⟨t, ht, g1, g2⟩ := nwrite_new hTW h
      rw [curDomA_ksb hk] at g1 g2
      rw [curDomA_val hc.node] at g1 g2
      have := hks t ht; omega
  · rcases nwrite_union hn with h | h
    · rw [dtA_ksb hk] at h; exact hS.dtNW h
    · obtain ⟨t, ht, g1, g2⟩ := nwrite_new hTW h
      rw [dtA_ksb hk, dtA_val hc.node] at g1 g2
      have := hks t ht; omega
  · obtain ⟨x0, hx0⟩ := hsz _ x n hx
    obtain ⟨o1, o2, o3, o4⟩ := hS.scOut sc hsC x0 n hx0 a hao
    refine ⟨fun hn => ?_, by rw [hnb]; exact o2, fun t ht => ?_, by rw [hk]; exact o4⟩
    · rcases nwrite_union hn with h | h
      · exact o1 h
      · obtain ⟨t, ht, g1, g2⟩ := nwrite_new hTW h
        have := hsc sc hsC x0 n hx0 a hao t ht; omega
    · rcases ht with ht | ht
      · exact o3 t ht
      · exact hsc sc hsC x0 n hx0 a hao t ht
  · exact scDisj_transfer hsz hS.scDisj
theorem queueRel_monoT {m : U64 → U64} {T T' : Set U64} {l : tcbqueue.Link} {q : tcbqueue.Queue} {xs : List U64}
    (h : QueueRel m T l q xs) (hT : T ⊆ T') : QueueRel m T' l q xs :=
  ⟨h.nodup, fun t ht => hT (h.mem t ht), h.head, h.last, h.seg⟩

theorem NtfnObjRel.monoT {m : U64 → U64} {T T' : Set U64} {n : U64} {o : Fl4Spec.Ntfn} (h : NtfnObjRel m T n o)
    (hT : T ⊆ T') : NtfnObjRel m T' n o := by
  cases o with
  | idleNtfn => exact ⟨h.1, queueRel_monoT h.2 hT⟩
  | activeNtfn b => exact ⟨h.1, queueRel_monoT h.2.1 hT, h.2.2⟩
  | waitingNtfn q =>
    obtain ⟨h1, xs, h2, h3, h4, h5⟩ := h
    exact ⟨h1, xs, h2, h3, queueRel_monoT h4 hT, h5⟩

/-- **The notification relation over fresh notifications and TCBs**: the
old words kept (`FootEq`), the new notifications' words zero (idle, unbound,
no SC) and the new TCBs' state, badge register and priority words zero
(inactive, `default_tcb`'s context and priority). -/
theorem NtfnStateRel.add {N T Nn W : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit}
    (hR : NtfnStateRel N T m σ) (hP : NPlaced T N) (hm : FootEq N T m m')
    (hkold : ∀ p k, σ.kheap p = some k → σ'.kheap p = some k)
    (hkn : ∀ n ∈ Nn, σ'.kheap n.bv = some (.notification Fl4Spec.defaultNotification))
    (hkt : ∀ t ∈ W, σ'.kheap t.bv = some (.tcb (Fl4Spec.defaultTcb 0)))
    (hmn : ∀ n ∈ Nn, m' (epTSA n) = 0#u64 ∧ m' (epHeadA n) = 0#u64 ∧ m' (nBoundA n) = 0#u64 ∧ m' (nScA n) = 0#u64)
    (hmt : ∀ t ∈ W, m' (tStA t) = 0#u64 ∧ m' (badgeRegA t) = 0#u64 ∧ m' (prioA t) = 0#u64) :
    NtfnStateRel (N ∪ Nn) (T ∪ W) m' σ' := by
  have hsub : T ⊆ T ∪ W := fun _ h => Or.inl h
  refine ⟨fun n hn => ?_, fun t ht => ?_⟩
  · rcases hn with hn | hn
    · obtain ⟨x, hkx, hx⟩ := hR.ntfn n hn
      have hx' := hx.frame (hm.nwords hP hn) fun y hy _ =>
        ⟨(hm.tfields hP hy).st, (hm.tfields hP hy).blk, hm.tlinks hP hy⟩
      exact ⟨x, hkold _ _ hkx, ⟨NtfnObjRel.monoT hx'.obj hsub, hx'.bound, fun h => hsub (hx'.bound_mem h), hx'.sc⟩⟩
    · obtain ⟨e1, e2, e3, e4⟩ := hmn n hn
      refine ⟨_, hkn n hn, ⟨⟨?_, ?_⟩, by rw [e3, optRef_zero]; rfl, fun h => absurd e3 h,
        by rw [e4, optRef_zero]; rfl⟩⟩
      · show m' (epTSA n) &&& 3#u64 = 0#u64
        rw [e1]; decide
      · show QueueRel m' (T ∪ W) .Ep ⟨m' (epHeadA n), m' (epTSA n) &&& ~~~3#u64⟩ []
        rw [e1, e2]
        exact QueueRel.nil
  · rcases ht with ht | ht
    · obtain ⟨x, hkx, hx⟩ := hR.tcb t ht
      exact ⟨x, hkold _ _ hkx, hx.frame (hm.tfields hP ht)⟩
    · obtain ⟨e1, e2, e3⟩ := hmt t ht
      refine ⟨_, hkt t ht, ⟨by rw [e1]; rfl, fun n h => (by cases h), by rw [e2]; rfl, by rw [e3]; rfl⟩⟩

theorem nwrite_unionN {N Nn T : Set U64} {a : U64} (h : NWrite (N ∪ Nn) T a) :
    NWrite N T a ∨ ∃ n ∈ Nn, n.val ≤ a.val ∧ a.val < n.val + 40 := by
  rcases h with ⟨n, hn, h1, h2⟩ | h
  · rcases hn with hn | hn
    · exact Or.inl (Or.inl ⟨n, hn, h1, h2⟩)
    · exact Or.inr ⟨n, hn, h1, h2⟩
  · exact Or.inl (Or.inr h)

/-- **The scheduler relation with fresh notifications**: placed apart from
the TCBs, the node, the kernel-global block and the SCs. -/
theorem SchedRel.add_ntfns {N Nn T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hNa : ∀ n ∈ Nn, NAddr n)
    (hnt : ∀ n ∈ Nn, ∀ t ∈ T, t.val + 4096 ≤ n.val ∨ n.val + 64 ≤ t.val)
    (hnd : ∀ n ∈ Nn, n.val + 64 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ n.val)
    (hks : ∀ n ∈ Nn, n.val + 64 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hsc : ∀ sc ∈ C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → ∀ a : U64, ScObj sc n a →
      ∀ m ∈ Nn, a.val < m.val ∨ m.val + 64 ≤ a.val) :
    SchedRel st (N ∪ Nn) T C c s σ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  refine ⟨⟨hS.placed.tcb, fun n hn => ?_, fun n hn t ht => ?_⟩, fun o ho hn => ?_, fun hn => ?_, fun hn => ?_,
    fun sc hsC x n hx a hao => ?_, hS.scDisj, hS.actW, hS.act, hS.repr, hS.core, hS.lists⟩
  · rcases hn with hn | hn
    · exact hS.placed.ntfn n hn
    · exact hNa n hn
  · rcases hn with hn | hn
    · exact hS.placed.disj n hn t ht
    · exact hnt n hn t ht
  · rcases nwrite_unionN hn with h | ⟨m, hm, g1, g2⟩
    · exact hS.nodeNW o ho h
    · rw [nodeAt_val hc.node ho] at g1 g2; have := hnd m hm; omega
  · rcases nwrite_unionN hn with h | ⟨m, hm, g1, g2⟩
    · exact hS.domNW h
    · rw [curDomA_val hc.node] at g1 g2; have := hks m hm; omega
  · rcases nwrite_unionN hn with h | ⟨m, hm, g1, g2⟩
    · exact hS.dtNW h
    · rw [dtA_val hc.node] at g1 g2; have := hks m hm; omega
  · obtain ⟨o1, o2, o3, o4⟩ := hS.scOut sc hsC x n hx a hao
    refine ⟨fun hn => ?_, o2, o3, o4⟩
    rcases nwrite_unionN hn with h | ⟨m, hm, g1, g2⟩
    · exact o1 h
    · have := hsc sc hsC x n hx a hao m hm; omega

theorem EpObjRel.monoT {m : U64 → U64} {T T' : Set U64} {e : U64} {o : Fl4Spec.Endpoint}
    (h : Endp.EpObjRel m T e o) (hT : T ⊆ T') : Endp.EpObjRel m T' e o := by
  cases o with
  | idleEP => exact ⟨h.1, queueRel_monoT h.2 hT⟩
  | sendEP q =>
    obtain ⟨h1, xs, h2, h3, h4, h5⟩ := h
    exact ⟨h1, xs, h2, h3, queueRel_monoT h4 hT, h5⟩
  | recvEP q =>
    obtain ⟨h1, xs, h2, h3, h4, h5⟩ := h
    exact ⟨h1, xs, h2, h3, queueRel_monoT h4 hT, h5⟩

/-- **The endpoint relation over fresh endpoints, replies and TCBs**, from
the relation over the old sets at the state after: the new endpoints idle
(state and head words zero), the new replies with no TCB, the new TCBs
inactive with no fault and no bound notification, `default_tcb`'s
registers (`new_context`) and priority. -/
theorem EpStateRel.add {T E R W En Rn : Set U64} {B : Set (U64 × Fl4Spec.Word)} {m : U64 → U64}
    {σ : Fl4Spec.State Unit} (hR : Endp.EpStateRel T E R B m σ)
    (hke : ∀ e ∈ En, σ.kheap e.bv = some (.endpoint .idleEP))
    (hkr : ∀ r ∈ Rn, σ.kheap r.bv = some (.reply Fl4Spec.defaultReply))
    (hkt : ∀ t ∈ W, σ.kheap t.bv = some (.tcb (Fl4Spec.defaultTcb 0)))
    (hme : ∀ e ∈ En, m (epTSA e) = 0#u64 ∧ m (epHeadA e) = 0#u64)
    (hmr : ∀ r ∈ Rn, m (Endp.rTcbA r) = 0#u64)
    (hmt : ∀ t ∈ W, m (tStA t) = 0#u64 ∧ m (prioA t) = 0#u64 ∧ m (Endp.tFaultA t) = 0#u64 ∧
      m (Endp.tBoundA t) = 0#u64 ∧ ∀ r, (m (Endp.regA t (Endp.regIdx r))).bv = Fl4Spec.newContext.userRegs r) :
    Endp.EpStateRel (T ∪ W) (E ∪ En) (R ∪ Rn) B m σ := by
  have hsub : T ⊆ T ∪ W := fun _ h => Or.inl h
  refine ⟨fun e he => ?_, fun r hr => ?_, fun t ht => ?_, hR.buf⟩
  · rcases he with he | he
    · obtain ⟨x, hk, hx⟩ := hR.ep e he
      exact ⟨x, hk, EpObjRel.monoT hx hsub⟩
    · obtain ⟨e1, e2⟩ := hme e he
      refine ⟨_, hke e he, ?_, ?_⟩
      · show m (epTSA e) &&& 3#u64 = 0#u64
        rw [e1]; decide
      · show QueueRel m (T ∪ W) .Ep ⟨m (epHeadA e), m (epTSA e) &&& ~~~3#u64⟩ []
        rw [e1, e2]; exact QueueRel.nil
  · rcases hr with hr | hr
    · exact hR.reply r hr
    · exact ⟨_, hkr r hr, by rw [hmr r hr, optRef_zero]; rfl⟩
  · rcases ht with ht | ht
    · obtain ⟨x, hk, hx⟩ := hR.tcb t ht
      exact ⟨x, hk, ⟨hx.st, hx.blk, hx.send, fun e r d hs => ⟨(hx.recv e r d hs).1, fun h => Or.inl ((hx.recv e r d hs).2 h)⟩,
        hx.reply, hx.regs, hx.prio, hx.fault0, hx.faultT, hx.bound, hx.faultR⟩⟩
    · obtain ⟨e1, e2, e3, e4, e5⟩ := hmt t ht
      refine ⟨_, hkt t ht, ⟨(by rw [e1]; rfl), (fun e h => by cases h), (fun e d h => by cases h),
        (fun e r d h => by cases h), (fun r h => by cases h), e5, (by rw [e2]; rfl), (by simp [e3, Fl4Spec.defaultTcb]),
        (by simp [e3, Fl4Spec.defaultTcb]), (by rw [e4, optRef_zero]; rfl), ?_⟩⟩
      show Endp.FaultRel' _ _ _ _ _ _ _ none
      exact e3

end

end

end Fl4Proofs.P3.Sched
