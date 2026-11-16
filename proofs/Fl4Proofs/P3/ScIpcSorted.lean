/-
P3, scheduling contexts: **the spec's IPC queues sorted by priority** (l4v
MCS `sorted_ipc_queues`): every endpoint's and notification's queue is
sorted by the queued TCBs' priorities, highest first.

* `IpcSorted σ`; `IpcSorted.frame`: kept by a step that keeps every queue
  and the queued threads' priorities; `IpcSorted.ntfnStep`,
  `IpcSorted.epStep`: kept by the IPC code's spec steps (`NtfnStep`,
  `EpStep`, which keep priorities) whose changed queues are sorted.
* The queue operations: `sortedQ_specIns` (`tcb_append`), `SortedQ.sublist`
  (removal, the queue's tail), `IpcSorted.updEp`, `IpcSorted.updNtfn` (a
  queue replaced by a sorted one); `IpcSorted.epAppend`, `ntfnAppend`,
  `epDequeue`, `ntfnDequeue` on the states of `tcbEpAppend_eq`,
  `tcbNtfnAppend_eq`, `tcbEpDequeue_eq`, `tcbNtfnDequeue_eq`.
* `setPriority_sorted`: every outcome of `set_priority` keeps it (the
  thread's new priority, and its queue reordered by `reorder_ep` /
  `reorder_ntfn`), given that the thread is queued only on the object it is
  blocked on (l4v `valid_ep`, `valid_ntfn`, `sym_refs`).
* FL4 side: `epSorted_of_spec`, `ntfnSorted_of_spec` (the `hsort`
  premises of the IPC proofs) and `qSorted_of_spec` (`QSorted`), through
  the queue relation (`EpObjRel`, `NtfnObjRel`) and the priority relation
  (`TcbRelE.prio`, `TcbRel1.prio`).

`IpcSorted` is not a field of `Inv`: the IPC code's scheduler hypotheses
(`SchedHyps.stable`, `stableN`, `stableE`, `block`) keep the scheduler
relation across any `NtfnStep` / `EpStep`, and those may rewrite a queue
arbitrarily, so an `Inv` with sorted queues could not discharge them.
-/
import Fl4Proofs.P3.IpcLeaves
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1 Classical

noncomputable section

section Spec
open Fl4Spec

/-- A queue sorted by the spec's priorities, highest first. -/
def SortedQ (σ : State Unit) (q : List ObjRef) : Prop := q.Pairwise (fun a b => prioOf σ b ≤ prioOf σ a)

/-- **The spec's IPC queues are sorted** (l4v `sorted_ipc_queues`). -/
def IpcSorted (σ : State Unit) : Prop :=
  (∀ p x, σ.kheap p = some (.endpoint x) → SortedQ σ x.epQueue) ∧
  (∀ p x, σ.kheap p = some (.notification x) → SortedQ σ x.ntfnObj.ntfnQueue)

theorem SortedQ.congr {σ σ' : State Unit} {q : List ObjRef} (h : SortedQ σ q)
    (hp : ∀ u ∈ q, prioOf σ' u = prioOf σ u) : SortedQ σ' q :=
  h.imp_of_mem fun ha hb hab => by rw [hp _ ha, hp _ hb]; exact hab

theorem SortedQ.sublist {σ : State Unit} {q q' : List ObjRef} (h : SortedQ σ q) (hs : q'.Sublist q) :
    SortedQ σ q' := List.Pairwise.sublist hs h

theorem SortedQ.removeAll {σ : State Unit} {q : List ObjRef} (h : SortedQ σ q) (t : ObjRef) :
    SortedQ σ (removeAll t q) := h.sublist List.filter_sublist

theorem SortedQ.tail {σ : State Unit} {q : List ObjRef} (h : SortedQ σ q) : SortedQ σ q.tail :=
  h.sublist (List.tail_sublist q)

/-- **The ordered insertion keeps a queue sorted** (`tcb_append`). -/
theorem sortedQ_specIns {σ : State Unit} {q : List ObjRef} (h : SortedQ σ q) (t : ObjRef)
    (ht : prioOf σ t = v) : SortedQ σ (Notif.specIns q (prioOf σ) v t) := by
  unfold Notif.specIns SortedQ
  set P := fun y => @decide (prioOf σ y ≥ v) (Classical.propDecidable _)
  have hsplit := List.takeWhile_append_dropWhile (p := P) (l := q)
  have h' : (q.takeWhile P ++ q.dropWhile P).Pairwise (fun a b => prioOf σ b ≤ prioOf σ a) := by
    rw [hsplit]; exact h
  rw [List.pairwise_append] at h'
  obtain ⟨h1, h2, h3⟩ := h'
  have htw : ∀ a ∈ q.takeWhile P, v ≤ prioOf σ a := fun a ha => by
    have := List.mem_takeWhile_imp ha
    simpa [P] using this
  have hdw : ∀ b ∈ q.dropWhile P, prioOf σ b ≤ v := by
    intro b hb
    cases hd : q.dropWhile P with
    | nil => rw [hd] at hb; cases hb
    | cons c cs =>
      have hc : ¬ (prioOf σ c ≥ v) := by
        have := List.head_dropWhile_not P (l := q) (by rw [hd]; simp)
        simp only [hd, List.head_cons, P] at this
        exact (@decide_eq_false_iff_not _ (Classical.propDecidable _)).1 this
      have hcn : (prioOf σ c).toNat < v.toNat := by
        have : ¬ v.toNat ≤ (prioOf σ c).toNat := fun hh => hc (BitVec.le_def.2 hh)
        omega
      rw [hd] at hb h2
      rcases List.mem_cons.1 hb with rfl | hb'
      · exact BitVec.le_def.2 (by omega)
      · have := BitVec.le_def.1 ((List.pairwise_cons.1 h2).1 b hb')
        exact BitVec.le_def.2 (by omega)
  rw [List.pairwise_append]
  refine ⟨h1, List.pairwise_cons.2 ⟨fun b hb => by rw [ht]; exact hdw b hb, h2⟩, fun a ha b hb => ?_⟩
  rcases List.mem_cons.1 hb with rfl | hb'
  · rw [ht]; exact htw a ha
  · exact h3 a ha b hb'

theorem prioOf_upd_ne {σ : State Unit} {p u : ObjRef} {ko : KernelObject} (h : u ≠ p) :
    prioOf (Notif.updK σ p ko) u = prioOf σ u := by
  unfold prioOf; rw [tcbsOf_eq, tcbsOf_eq]; simp [Notif.updK, Function.update_of_ne h]

/-- A non-TCB at `p` replaced by a non-TCB keeps every priority. -/
theorem prioOf_upd_ntcb {σ : State Unit} {p : ObjRef} {ko : KernelObject} (hko : ∀ x, ko ≠ .tcb x)
    (hold : ∀ x, σ.kheap p ≠ some (.tcb x)) (u : ObjRef) : prioOf (Notif.updK σ p ko) u = prioOf σ u := by
  by_cases hu : u = p
  · subst hu
    unfold prioOf; rw [tcbsOf_eq, tcbsOf_eq]
    simp only [Notif.updK, Function.update_self]
    cases ko <;> (try exact absurd rfl (hko _)) <;>
    · cases e : σ.kheap u with
      | none => rfl
      | some k => cases k <;> first | rfl | exact absurd e (hold _)
  · exact prioOf_upd_ne hu

theorem prioOf_upd_ep {σ : State Unit} {p : ObjRef} {x : Endpoint} (hk : σ.kheap p = some (.endpoint x))
    (y : Endpoint) (u : ObjRef) : prioOf (Notif.updK σ p (.endpoint y)) u = prioOf σ u :=
  prioOf_upd_ntcb (fun _ e => by cases e) (fun _ e => by rw [hk] at e; cases e) u

theorem prioOf_upd_ntfn {σ : State Unit} {p : ObjRef} {x : Notification} (hk : σ.kheap p = some (.notification x))
    (y : Notification) (u : ObjRef) : prioOf (Notif.updK σ p (.notification y)) u = prioOf σ u :=
  prioOf_upd_ntcb (fun _ e => by cases e) (fun _ e => by rw [hk] at e; cases e) u

/-- **`IpcSorted` across a step keeping every queue and the queued threads'
priorities.** -/
theorem IpcSorted.frame {σ σ' : State Unit} (h : IpcSorted σ)
    (hep : ∀ p x', σ'.kheap p = some (.endpoint x') → ∃ x, σ.kheap p = some (.endpoint x) ∧ x'.epQueue = x.epQueue)
    (hn : ∀ p x', σ'.kheap p = some (.notification x') →
      ∃ x, σ.kheap p = some (.notification x) ∧ x'.ntfnObj.ntfnQueue = x.ntfnObj.ntfnQueue)
    (hpr : ∀ u, prioOf σ' u = prioOf σ u) : IpcSorted σ' := by
  refine ⟨fun p x' hk => ?_, fun p x' hk => ?_⟩
  · obtain ⟨x, h0, e⟩ := hep p x' hk
    rw [e]; exact (h.1 p x h0).congr fun u _ => hpr u
  · obtain ⟨x, h0, e⟩ := hn p x' hk
    rw [e]; exact (h.2 p x h0).congr fun u _ => hpr u

theorem IpcSorted.congr {σ σ' : State Unit} (h : IpcSorted σ) (hk : σ'.kheap = σ.kheap) : IpcSorted σ' :=
  h.frame (fun p x' e => ⟨x', by rw [← hk]; exact e, rfl⟩) (fun p x' e => ⟨x', by rw [← hk]; exact e, rfl⟩)
    (fun u => by unfold prioOf; rw [tcbsOf_eq, tcbsOf_eq, hk])

/-- **A queue replaced by a sorted one** (endpoint). -/
theorem IpcSorted.updEp {σ : State Unit} (h : IpcSorted σ) {p : ObjRef} {x x' : Endpoint}
    (hk : σ.kheap p = some (.endpoint x)) (hs : SortedQ σ x'.epQueue) :
    IpcSorted (Notif.updK σ p (.endpoint x')) := by
  have hpr := prioOf_upd_ntcb (σ := σ) (p := p) (ko := .endpoint x') (fun _ e => by cases e)
    (fun _ e => by rw [hk] at e; cases e)
  refine ⟨fun q y hq => ?_, fun q y hq => ?_⟩
  · by_cases e : q = p
    · subst e; simp [Notif.updK] at hq; subst hq; exact hs.congr fun u _ => hpr u
    · rw [Notif.updK_kheap, Function.update_of_ne e] at hq; exact (h.1 q y hq).congr fun u _ => hpr u
  · by_cases e : q = p
    · subst e; simp [Notif.updK] at hq
    · rw [Notif.updK_kheap, Function.update_of_ne e] at hq; exact (h.2 q y hq).congr fun u _ => hpr u

/-- **A queue replaced by a sorted one** (notification). -/
theorem IpcSorted.updNtfn {σ : State Unit} (h : IpcSorted σ) {p : ObjRef} {x x' : Notification}
    (hk : σ.kheap p = some (.notification x)) (hs : SortedQ σ x'.ntfnObj.ntfnQueue) :
    IpcSorted (Notif.updK σ p (.notification x')) := by
  have hpr := prioOf_upd_ntcb (σ := σ) (p := p) (ko := .notification x') (fun _ e => by cases e)
    (fun _ e => by rw [hk] at e; cases e)
  refine ⟨fun q y hq => ?_, fun q y hq => ?_⟩
  · by_cases e : q = p
    · subst e; simp [Notif.updK] at hq
    · rw [Notif.updK_kheap, Function.update_of_ne e] at hq; exact (h.1 q y hq).congr fun u _ => hpr u
  · by_cases e : q = p
    · subst e; simp [Notif.updK] at hq; subst hq; exact hs.congr fun u _ => hpr u
    · rw [Notif.updK_kheap, Function.update_of_ne e] at hq; exact (h.2 q y hq).congr fun u _ => hpr u

/-- The IPC code's notification steps keep every priority. -/
theorem NtfnStep.prioOf {σ σ' : State Unit} (h : Notif.NtfnStep σ σ') (u : ObjRef) : prioOf σ' u = prioOf σ u := by
  unfold Sched.prioOf; rw [tcbsOf_eq, tcbsOf_eq]
  rcases h.2.2 u with e | ⟨a, b, ha, hb, -⟩ | ⟨a, b, ha, hb, e⟩
  · rw [e]
  · rw [ha, hb]
  · rw [ha, hb]; simp only [Option.map_some, Option.getD_some]; rw [e]

/-- The IPC code's endpoint steps keep every priority. -/
theorem EpStep.prioOf {σ σ' : State Unit} (h : Endp.EpStep σ σ') (u : ObjRef) : prioOf σ' u = prioOf σ u := by
  unfold Sched.prioOf; rw [tcbsOf_eq, tcbsOf_eq]
  rcases h.2.2 u with e | ⟨a, b, ha, hb⟩ | ⟨a, b, ha, hb, -⟩ | ⟨a, b, ha, hb, e⟩
  · rw [e]
  · rw [ha, hb]
  · rw [ha, hb]
  · rw [ha, hb]; simp only [Option.map_some, Option.getD_some]; rw [e]

/-- **A notification step keeps `IpcSorted`** if its changed queues are sorted. -/
theorem IpcSorted.ntfnStep {σ σ' : State Unit} (h : IpcSorted σ) (hn : Notif.NtfnStep σ σ')
    (hq : ∀ p x x', σ.kheap p = some (.notification x) → σ'.kheap p = some (.notification x') →
      x'.ntfnObj.ntfnQueue ≠ x.ntfnObj.ntfnQueue → SortedQ σ x'.ntfnObj.ntfnQueue) : IpcSorted σ' := by
  have hpr := NtfnStep.prioOf hn
  refine ⟨fun p y hy => ?_, fun p y hy => ?_⟩
  · rcases hn.2.2 p with e | ⟨a, b, -, hb, -⟩ | ⟨a, b, -, hb, -⟩
    · rw [e] at hy; exact (h.1 p y hy).congr fun u _ => hpr u
    all_goals (rw [hy] at hb; cases hb)
  · rcases hn.2.2 p with e | ⟨a, b, ha, hb, -⟩ | ⟨a, b, -, hb, -⟩
    · rw [e] at hy; exact (h.2 p y hy).congr fun u _ => hpr u
    · rw [hy] at hb; cases hb
      by_cases eq : y.ntfnObj.ntfnQueue = a.ntfnObj.ntfnQueue
      · rw [eq]; exact (h.2 p a ha).congr fun u _ => hpr u
      · exact (hq p a y ha hy eq).congr fun u _ => hpr u
    · rw [hy] at hb; cases hb

/-- **An endpoint step keeps `IpcSorted`** if its changed queues are sorted. -/
theorem IpcSorted.epStep {σ σ' : State Unit} (h : IpcSorted σ) (hn : Endp.EpStep σ σ')
    (hq : ∀ p x x', σ.kheap p = some (.endpoint x) → σ'.kheap p = some (.endpoint x') →
      x'.epQueue ≠ x.epQueue → SortedQ σ x'.epQueue) : IpcSorted σ' := by
  have hpr := EpStep.prioOf hn
  refine ⟨fun p y hy => ?_, fun p y hy => ?_⟩
  · rcases hn.2.2 p with e | ⟨a, b, ha, hb⟩ | ⟨a, b, -, hb, -⟩ | ⟨a, b, -, hb, -⟩
    · rw [e] at hy; exact (h.1 p y hy).congr fun u _ => hpr u
    · rw [hy] at hb; cases hb
      by_cases eq : y.epQueue = a.epQueue
      · rw [eq]; exact (h.1 p a ha).congr fun u _ => hpr u
      · exact (hq p a y ha hy eq).congr fun u _ => hpr u
    all_goals (rw [hy] at hb; cases hb)
  · rcases hn.2.2 p with e | ⟨a, b, -, hb⟩ | ⟨a, b, -, hb, -⟩ | ⟨a, b, -, hb, -⟩
    · rw [e] at hy; exact (h.2 p y hy).congr fun u _ => hpr u
    all_goals (rw [hy] at hb; cases hb)

theorem epQueue_update (ep : Endpoint) (q : List ObjRef) (b : Bool) : (updateEpQueue ep q b).epQueue = q := by
  cases ep <;> cases b <;> rfl

/-! ## The queue operations -/

/-- **`tcb_ep_append` keeps `IpcSorted`** (`tcbEpAppend_eq`'s state). -/
theorem IpcSorted.epAppend {σ : State Unit} (h : IpcSorted σ) {t p : ObjRef} {x : Endpoint} {xt : Tcb}
    (hk : σ.kheap p = some (.endpoint x)) (hkt : σ.kheap t = some (.tcb xt)) (b : Bool) :
    IpcSorted (Notif.updK σ p (.endpoint (updateEpQueue x (Notif.specIns x.epQueue (prioOf σ) xt.tcbPriority t) b))) :=
  h.updEp hk (by rw [epQueue_update]; exact sortedQ_specIns (h.1 p x hk) t (prioOf_eq hkt))

/-- **`tcb_ntfn_append` keeps `IpcSorted`** (`tcbNtfnAppend_eq`'s state). -/
theorem IpcSorted.ntfnAppend {σ : State Unit} (h : IpcSorted σ) {t p : ObjRef} {x : Notification} {xt : Tcb}
    (hk : σ.kheap p = some (.notification x)) (hkt : σ.kheap t = some (.tcb xt)) :
    IpcSorted (Notif.updK σ p (.notification
      { x with ntfnObj := .waitingNtfn (Notif.specIns (ntfnQueueOf x) (prioOf σ) xt.tcbPriority t) })) :=
  h.updNtfn hk (sortedQ_specIns (h.2 p x hk) t (prioOf_eq hkt))

theorem epDeq_queue' (x : Endpoint) (t : ObjRef) : (Endp.epDeq x t).epQueue = removeAll t x.epQueue := by
  unfold Endp.epDeq
  split
  · rename_i e; rw [e]; rfl
  · exact epQueue_update _ _ _

/-- **`tcb_ep_dequeue` keeps `IpcSorted`** (`tcbEpDequeue_eq`'s state). -/
theorem IpcSorted.epDequeue {σ : State Unit} (h : IpcSorted σ) {t p : ObjRef} {x : Endpoint}
    (hk : σ.kheap p = some (.endpoint x)) : IpcSorted (Notif.updK σ p (.endpoint (Endp.epDeq x t))) :=
  h.updEp hk (by rw [epDeq_queue']; exact (h.1 p x hk).removeAll t)

/-- **`tcb_ntfn_dequeue` keeps `IpcSorted`** (`tcbNtfnDequeue_eq`'s state). -/
theorem IpcSorted.ntfnDequeue {σ : State Unit} (h : IpcSorted σ) {t p : ObjRef} {x : Notification}
    (hk : σ.kheap p = some (.notification x)) :
    IpcSorted (Notif.updK σ p (.notification (ntfnObjUpdate (fun _ =>
      match removeAll t (ntfnQueueOf x) with
      | [] => Ntfn.idleNtfn
      | _ => Ntfn.waitingNtfn (removeAll t (ntfnQueueOf x))) x))) := by
  refine h.updNtfn hk ?_
  have hs := (h.2 p x hk).removeAll t
  simp only [ntfnObjUpdate]
  split
  · exact List.Pairwise.nil
  · exact hs

/-! ## `set_priority` -/

/-- The thread `t` is queued only on the object it is blocked on (l4v
`valid_ep`, `valid_ntfn` with `sym_refs`). -/
def QueuedOnly (σ : State Unit) (t : ObjRef) (ts : ThreadState) : Prop :=
  (∀ p ep, σ.kheap p = some (.endpoint ep) → t ∈ ep.epQueue → epBlocked ts = some p) ∧
  (∀ p xn, σ.kheap p = some (.notification xn) → t ∈ ntfnQueueOf xn → ntfnBlocked ts = some p)

theorem epBlocked_ntfnBlocked {ts : ThreadState} {e n : ObjRef} (he : epBlocked ts = some e)
    (hn : ntfnBlocked ts = some n) : False := by
  cases ts <;> simp [epBlocked, ntfnBlocked] at he hn

/-- After the priority change, the queues not containing `t` are sorted. -/
theorem IpcSorted.prioSet {σ : State Unit} (h : IpcSorted σ) {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (pr : Priority) :
    (∀ p ep, (Notif.updK σ t (.tcb { x with tcbPriority := pr })).kheap p = some (.endpoint ep) → t ∉ ep.epQueue →
      SortedQ (Notif.updK σ t (.tcb { x with tcbPriority := pr })) ep.epQueue) ∧
    (∀ p xn, (Notif.updK σ t (.tcb { x with tcbPriority := pr })).kheap p = some (.notification xn) →
      t ∉ ntfnQueueOf xn → SortedQ (Notif.updK σ t (.tcb { x with tcbPriority := pr })) xn.ntfnObj.ntfnQueue) := by
  have hne : ∀ p, (∃ z, (Notif.updK σ t (.tcb { x with tcbPriority := pr })).kheap p = some z ∧ ∀ y, z ≠ .tcb y) →
      p ≠ t := by
    rintro p ⟨z, hz, hnz⟩ rfl; simp [Notif.updK] at hz; exact hnz _ hz.symm
  refine ⟨fun p ep hp hnt => ?_, fun p xn hp hnt => ?_⟩
  · have hpt := hne p ⟨_, hp, fun _ e => by cases e⟩
    rw [Notif.updK_kheap, Function.update_of_ne hpt] at hp
    refine (h.1 p ep hp).congr fun u hu => prioOf_upd_ne ?_
    rintro rfl; exact hnt hu
  · have hpt := hne p ⟨_, hp, fun _ e => by cases e⟩
    rw [Notif.updK_kheap, Function.update_of_ne hpt] at hp
    refine (h.2 p xn hp).congr fun u hu => prioOf_upd_ne ?_
    rintro rfl; exact hnt hu

/-- **Every outcome of `set_priority` keeps `IpcSorted`**, given `ActReady`,
`BlkQ` (as `setPriority_some`) and that the thread is queued only on the
object it is blocked on. -/
theorem setPriority_sorted {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (pr : Priority)
    (hA : Notif.ActReady σ) (hQ : BlkQ σ t x.tcbState) (hO : QueuedOnly σ t x.tcbState) (h : IpcSorted σ) :
    ∀ y ∈ (setPriority (Z := Unit) t pr σ).1, IpcSorted y.2 := by
  have hts : ∀ σ0 : State Unit, σ0.kheap t = some (.tcb x) →
      threadSetPriority (Z := Unit) t pr σ0 =
        ({((), Notif.updK σ0 t (.tcb { x with tcbPriority := pr }))}, False) := fun σ0 h0 =>
    Notif.threadSet_eq _ h0
  -- `t` in no queue: the priority change keeps `IpcSorted`
  have hfree : ∀ σ0 : State Unit, IpcSorted σ0 → σ0.kheap t = some (.tcb x) →
      (∀ p ep, σ0.kheap p = some (.endpoint ep) → t ∉ ep.epQueue) →
      (∀ p xn, σ0.kheap p = some (.notification xn) → t ∉ ntfnQueueOf xn) →
      IpcSorted (Notif.updK σ0 t (.tcb { x with tcbPriority := pr })) := by
    intro σ0 h0 hk0 he hn
    obtain ⟨g1, g2⟩ := h0.prioSet hk0 pr
    have hpt : ∀ p z, σ0.kheap p = some z → (∀ y, z ≠ .tcb y) → p ≠ t := by
      rintro p z hz hnz rfl; rw [hk0] at hz; cases hz; exact hnz _ rfl
    refine ⟨fun p ep hp => g1 p ep hp ?_, fun p xn hp => g2 p xn hp ?_⟩
    · have hpt' : p ≠ t := by rintro rfl; simp [Notif.updK] at hp
      rw [Notif.updK_kheap, Function.update_of_ne hpt'] at hp; exact he p ep hp
    · have hpt' : p ≠ t := by rintro rfl; simp [Notif.updK] at hp
      rw [Notif.updK_kheap, Function.update_of_ne hpt'] at hp; exact hn p xn hp
  unfold setPriority getThreadState
  rw [nd_bind_one (Notif.threadGet_eq _ hk)]
  split
  · rename_i hrun
    have hnoE : ∀ p ep, σ.kheap p = some (.endpoint ep) → t ∉ ep.epQueue := fun p ep hp ht => by
      have := hO.1 p ep hp ht; cases hs : x.tcbState <;> simp_all [epBlocked, runnable]
    have hnoN : ∀ p xn, σ.kheap p = some (.notification xn) → t ∉ ntfnQueueOf xn := fun p xn hp ht => by
      have := hO.2 p xn hp ht; cases hs : x.tcbState <;> simp_all [ntfnBlocked, runnable]
    rw [nd_bind_one (Notif.threadGet_eq _ hk), nd_bind_one (Notif.threadGet_eq _ hk),
      nd_bind_one (getTcbQueue_eq _ _ _), Notif.nd_gets_bind]
    split
    · rw [nd_bind_one (tcbSchedAction_gen hk _)]
      rw [nd_bind_one (hts (setQ σ x.tcbDomain x.tcbPriority _) hk)]
      rw [nd_bind_one (tcbSchedAction_gen (x := { x with tcbPriority := pr })
        (by simp [Notif.updK, setQ]) _)]
      obtain ⟨σd, hd, hqc⟩ := rescheduleRequired_qchange (actReady_upd (y := { x with tcbPriority := pr }) hA hk rfl rfl
        (σ' := setQ (Notif.updK (setQ σ x.tcbDomain x.tcbPriority _) t (.tcb { x with tcbPriority := pr }))
          x.tcbDomain pr _)
        (by simp [Notif.updK, setQ]) rfl rfl rfl)
      rw [hd]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      refine IpcSorted.congr ?_ hqc.1
      have h1 : IpcSorted (setQ σ x.tcbDomain x.tcbPriority
          (tcbSchedDequeue t (σ.readyQueues x.tcbDomain x.tcbPriority))) := h.congr rfl
      have h2 := hfree _ h1 hk hnoE hnoN
      exact h2.congr rfl
    · rw [hts _ hk]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact hfree σ h hk hnoE hnoN
  · rw [nd_bind_one (hts _ hk)]
    obtain ⟨hE, hN⟩ := hQ
    set σb := Notif.updK σ t (.tcb { x with tcbPriority := pr }) with hσb
    have hkb : σb.kheap t = some (.tcb { x with tcbPriority := pr }) := by simp [hσb, Notif.updK]
    have hkb' : ∀ u, u ≠ t → σb.kheap u = σ.kheap u := fun u hu => by
      simp [hσb, Notif.updK, Function.update_of_ne hu]
    obtain ⟨g1, g2⟩ := h.prioSet hk pr
    have hprt : prioOf σb t = pr := prioOf_eq hkb
    -- the reordered endpoint queue
    have hep : ∀ e, epBlocked x.tcbState = some e → ∃ σr, reorderEp (Z := Unit) e t σb = ({((), σr)}, False) ∧
        IpcSorted σr := by
      intro e he
      obtain ⟨ep, hke, hni, hne, hq⟩ := hE e he
      have het : e ≠ t := by rintro rfl; rw [hk] at hke; cases hke
      have hke' : σb.kheap e = some (.endpoint ep) := by rw [hkb' e het]; exact hke
      have hq' := removeAll_tcbs (σ := σb) (t := t) (qs := ep.epQueue)
        (fun u hu hut => by rw [hkb' u hut]; exact hq u hu hut)
      refine ⟨_, by
        unfold reorderEp
        rw [nd_bind_one (Endp.getEndpoint_eq hke'), nd_bind_one (assert_one hni _), Notif.nd_pure_bind',
          nd_bind_one (assert_one hne _), Notif.nd_pure_bind', nd_bind_one (Notif.tcbAppend_eq hkb _ _ hq')]
        exact Endp.setEndpoint_eq _ hke', ?_⟩
      -- σb's queues: `t` only in `e`'s
      refine ⟨fun p y hy => ?_, fun p y hy => ?_⟩
      · by_cases hpe : p = e
        · subst hpe
          simp only [Notif.updK_kheap, Function.update_self, Option.some.injEq,
            KernelObject.endpoint.injEq] at hy
          subst hy
          rw [epQueue_update]
          have hpr' := fun y => prioOf_upd_ep hke' y
          refine SortedQ.congr ?_ fun u _ => hpr' _ u
          refine sortedQ_specIns ?_ t hprt
          -- `removeAll t` of the old queue, sorted at σb
          have hs0 : SortedQ σ (removeAll t ep.epQueue) := (h.1 p ep hke).removeAll t
          refine hs0.congr fun u hu => prioOf_upd_ne ?_
          intro e'; subst e'; unfold removeAll at hu; simp at hu
        · rw [Notif.updK_kheap, Function.update_of_ne hpe] at hy
          have hpr' := fun y => prioOf_upd_ep hke' y
          refine SortedQ.congr (g1 p y hy fun ht => ?_) fun u _ => hpr' _ u
          have hpt : p ≠ t := by rintro rfl; rw [hkb] at hy; cases hy
          rw [hkb' p hpt] at hy
          exact hpe (Option.some.inj ((hO.1 p y hy ht).symm.trans he))
      · have hpe : p ≠ e := by
          rintro rfl; simp [Notif.updK, Function.update_self] at hy
        rw [Notif.updK_kheap, Function.update_of_ne hpe] at hy
        have hpr' := fun y => prioOf_upd_ep hke' y
        refine SortedQ.congr (g2 p y hy fun ht => ?_) fun u _ => hpr' _ u
        have hpt : p ≠ t := by rintro rfl; rw [hkb] at hy; cases hy
        rw [hkb' p hpt] at hy
        exact epBlocked_ntfnBlocked he (hO.2 p y hy ht)
    -- the reordered notification queue
    have hnt : ∀ n, ntfnBlocked x.tcbState = some n → ∃ σr, reorderNtfn (Z := Unit) n t σb = ({((), σr)}, False) ∧
        IpcSorted σr := by
      intro n hn
      obtain ⟨xn, hkn, hw, hne, hq⟩ := hN n hn
      have hnt : n ≠ t := by rintro rfl; rw [hk] at hkn; cases hkn
      have hkn' : σb.kheap n = some (.notification xn) := by rw [hkb' n hnt]; exact hkn
      have hq' := removeAll_tcbs (σ := σb) (t := t) (qs := ntfnQueueOf xn)
        (fun u hu hut => by rw [hkb' u hut]; exact hq u hu hut)
      refine ⟨_, by
        unfold reorderNtfn
        rw [nd_bind_one (Notif.getNotification_eq hkn'), nd_bind_one (assert_one hw _), Notif.nd_pure_bind',
          nd_bind_one (assert_one hne _), Notif.nd_pure_bind', nd_bind_one (Notif.tcbAppend_eq hkb _ _ hq')]
        exact Notif.setNotification_eq _ hkn', ?_⟩
      refine ⟨fun p y hy => ?_, fun p y hy => ?_⟩
      · have hpe : p ≠ n := by
          rintro rfl; simp [Notif.updK, Function.update_self] at hy
        rw [Notif.updK_kheap, Function.update_of_ne hpe] at hy
        have hpr' := fun y => prioOf_upd_ntfn hkn' y
        refine SortedQ.congr (g1 p y hy fun ht => ?_) fun u _ => hpr' _ u
        have hpt : p ≠ t := by rintro rfl; rw [hkb] at hy; cases hy
        rw [hkb' p hpt] at hy
        exact epBlocked_ntfnBlocked (hO.1 p y hy ht) hn
      · by_cases hpe : p = n
        · subst hpe
          simp only [Notif.updK_kheap, Function.update_self, Option.some.injEq,
            KernelObject.notification.injEq] at hy
          subst hy
          have hpr' := fun y => prioOf_upd_ntfn hkn' y
          refine SortedQ.congr ?_ fun u _ => hpr' _ u
          show SortedQ σb (Notif.specIns _ _ _ t)
          refine sortedQ_specIns ?_ t hprt
          have hs0 : SortedQ σ (removeAll t (ntfnQueueOf xn)) := (h.2 p xn hkn).removeAll t
          refine hs0.congr fun u hu => prioOf_upd_ne ?_
          intro e'; subst e'; unfold removeAll at hu; simp at hu
        · rw [Notif.updK_kheap, Function.update_of_ne hpe] at hy
          have hpr' := fun y => prioOf_upd_ntfn hkn' y
          refine SortedQ.congr (g2 p y hy fun ht => ?_) fun u _ => hpr' _ u
          have hpt : p ≠ t := by rintro rfl; rw [hkb] at hy; cases hy
          rw [hkb' p hpt] at hy
          exact hpe (Option.some.inj ((hO.2 p y hy ht).symm.trans hn))
    -- no queue holds `t`
    have hfreeB : (epBlocked x.tcbState = none) → (ntfnBlocked x.tcbState = none) → IpcSorted σb := by
      intro h1 h2
      refine hfree σ h hk (fun p ep hp ht => ?_) (fun p xn hp ht => ?_)
      · have := hO.1 p ep hp ht; rw [h1] at this; cases this
      · have := hO.2 p xn hp ht; rw [h2] at this; cases this
    cases hst : x.tcbState
    all_goals first
      | (rename_i hnr; rw [hst] at hnr; simp [runnable] at hnr; done)
      | (obtain ⟨σr, hr, hs⟩ := hep _ (by rw [hst]; rfl)
         intro y hy
         change y ∈ ((reorderEp (Z := Unit) _ t >>= fun _ => NonDet.pure ()) σb).1 at hy
         rw [nd_bind_one hr] at hy; rw [Set.mem_singleton_iff.1 hy]; exact hs)
      | (obtain ⟨σr, hr, hs⟩ := hnt _ (by rw [hst]; rfl)
         intro y hy
         change y ∈ ((NonDet.pure () >>= fun _ => reorderNtfn (Z := Unit) _ t) σb).1 at hy
         rw [nd_bind_one (show (NonDet.pure () : NonDet (State Unit) Unit) σb = ({((), σb)}, False) from rfl), hr] at hy
         rw [Set.mem_singleton_iff.1 hy]; exact hs)
      | (intro y hy
         change y ∈ ((NonDet.pure () >>= fun _ => NonDet.pure ()) σb).1 at hy
         rw [nd_bind_one (show (NonDet.pure () : NonDet (State Unit) Unit) σb = ({((), σb)}, False) from rfl)] at hy
         rw [Set.mem_singleton_iff.1 hy]
         exact hfreeB (by rw [hst]; rfl) (by rw [hst]; rfl))

end Spec

/-! ## FL4's queues sorted, from the spec's -/

section
open Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **An endpoint's FL4 queue is sorted by FL4's priorities** (the IPC
proofs' `hsort`), from `IpcSorted` through the endpoint relation. -/
theorem epSorted_of_spec {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {m : U64 → U64}
    {σ : Fl4Spec.State Unit} (hR : Endp.EpStateRel T E R B m σ) (hTP : TcbPlaced T) (hS : IpcSorted σ)
    {e : U64} (he : e ∈ E) :
    ∀ xs, QueueRel m T .Ep (qOf m e) xs → PrioSorted (fun y => m (prioA y)) xs := by
  intro xs hq
  obtain ⟨x, hk, hrel⟩ := hR.ep e he
  obtain ⟨ys, hys, hq0, -⟩ := hrel.queue
  have e1 : xs = ys := hq.unique hTP hys
  subst e1
  have hs := hS.1 _ x hk
  rw [hq0] at hs
  unfold SortedQ at hs
  rw [List.pairwise_map] at hs
  refine hs.imp_of_mem fun {a b} ha hb hab => ?_
  obtain ⟨xa, hka, ra⟩ := hR.tcb a (hq.mem a ha)
  obtain ⟨xb, hkb, rb⟩ := hR.tcb b (hq.mem b hb)
  rw [prioOf_eq hka, prioOf_eq hkb] at hab
  rw [ra.prio, rb.prio]
  exact BitVec.le_def.1 hab

/-- **A notification's FL4 queue is sorted by FL4's priorities**, from
`IpcSorted` through the notification relation. -/
theorem ntfnSorted_of_spec {N T : Set U64} {m : U64 → U64} {σ : Fl4Spec.State Unit}
    (hR : Notif.NtfnStateRel N T m σ) (hTP : TcbPlaced T) (hS : IpcSorted σ) {n : U64} (hn : n ∈ N) :
    ∀ xs, QueueRel m T .Ep (qOf m n) xs → PrioSorted (fun y => m (prioA y)) xs := by
  intro xs hq
  obtain ⟨x, hk, hrel⟩ := hR.ntfn n hn
  obtain ⟨ys, hys, hq0, -⟩ := hrel.obj.queue
  have e1 : xs = ys := hq.unique hTP hys
  subst e1
  have hs := hS.2 _ x hk
  rw [hq0] at hs
  unfold SortedQ at hs
  rw [List.pairwise_map] at hs
  refine hs.imp_of_mem fun {a b} ha hb hab => ?_
  obtain ⟨xa, hka, ra⟩ := hR.tcb a (hq.mem a ha)
  obtain ⟨xb, hkb, rb⟩ := hR.tcb b (hq.mem b hb)
  rw [prioOf_eq hka, prioOf_eq hkb] at hab
  rw [ra.prio, rb.prio]
  exact BitVec.le_def.1 hab

/-- **`QSorted` from `IpcSorted`**, for endpoints and notifications. -/
theorem qSorted_of_spec {T E R N : Set U64} {B : Set (U64 × Fl4Spec.Word)} {s : S} {σ : Fl4Spec.State Unit}
    (hRE : Endp.EpStateRel T E R B (L.mem s) σ) (hRN : Notif.NtfnStateRel N T (L.mem s) σ) (hTP : TcbPlaced T)
    (hS : IpcSorted σ) : Endp.QSorted st T (E ∪ N) s := by
  rintro e (he | hn) xs hq
  · exact epSorted_of_spec hRE hTP hS he xs hq
  · exact ntfnSorted_of_spec hRN hTP hS hn xs hq

end

end

end Fl4Proofs.P3.Sched
