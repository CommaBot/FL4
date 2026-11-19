/-
P3 (DESIGN.md §9), Untyped's reset (the drop step), part 1: **the XTop
relations at the kept part of the sets** (handoff/utj.md "Round 8"). The drop
of a childless untyped region runs in two stages:

* stage A (this file): at the same states, the relations hold for the sets
  cut down to a kept part (`KeepS K X`, `K` = "off the region"), given that
  every object a kept object names is kept (the closure premises below);
* stage B (UtDropStep): the spec's detype and FL4's zeroing touch only the
  region, which no kept object meets.

Stage A's closure premises (each is discharged at `J` from `DeadP` and the
links' symmetry, UtDropJ):

* `hKT`: a thread of `T` whose state word is not `Inactive` is kept (a dead
  thread is inactive, `DeadP`) — the endpoint and notification queues, the
  ready and release queues;
* `hKR`: the reply named by a kept thread blocked receiving is kept (l4v
  `sym_refs`: the reply's `reply_tcb` is the thread, `SchedValid.recvReply`,
  and a dead reply's TCB word is null);
* `hKB`: a kept notification's bound thread is kept (`KeptRefsP3.ntb`);
* the scheduler's: the action word's, current and idle threads kept, a kept
  thread's SC kept.
-/
import Fl4Proofs.P3.UtDropYield
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-- The kept part of a set. -/
def KeepS (K : U64 → Prop) (X : Set U64) : Set U64 := {q | q ∈ X ∧ K q}

/-- The kept part of the IPC-buffer words. -/
def KeepB (K : U64 × Fl4Spec.Word → Prop) (B : Set (U64 × Fl4Spec.Word)) : Set (U64 × Fl4Spec.Word) :=
  {wp | wp ∈ B ∧ K wp}

theorem KeepS.sub {K : U64 → Prop} {X : Set U64} {q : U64} (h : q ∈ KeepS K X) : q ∈ X := h.1
theorem KeepB.sub {K : U64 × Fl4Spec.Word → Prop} {B : Set (U64 × Fl4Spec.Word)} {wp : U64 × Fl4Spec.Word}
    (h : wp ∈ KeepB K B) : wp ∈ B := h.1

section Ipc
variable {K : U64 → Prop} {KB : U64 × Fl4Spec.Word → Prop} {m : U64 → U64}
variable {N T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

theorem QueueRel.keepS {T : Set U64} {l : tcbqueue.Link} {q : tcbqueue.Queue} {xs : List U64}
    (h : P1.QueueRel m T l q xs) (hk : ∀ t ∈ xs, K t) : P1.QueueRel m (KeepS K T) l q xs :=
  ⟨h.nodup, fun t ht => ⟨h.mem t ht, hk t ht⟩, h.head, h.last, h.seg⟩

/-- A queued thread (state word nonzero) is kept. -/
def LiveKeep (K : U64 → Prop) (T : Set U64) (m : U64 → U64) : Prop :=
  ∀ t ∈ T, m (tStA t) ≠ 0#u64 → K t

theorem Endp.EpObjRel.keepS {e : U64} {x : Fl4Spec.Endpoint} (hKT : LiveKeep K T m) (h : EpObjRel m T e x) :
    EpObjRel m (KeepS K T) e x := by
  cases x with
  | idleEP => exact ⟨h.1, QueueRel.keepS h.2 (fun t ht => by cases ht)⟩
  | sendEP q =>
    obtain ⟨h1, xs, hne, hq, hQ, hy⟩ := h
    refine ⟨h1, xs, hne, hq, QueueRel.keepS hQ fun t ht => hKT t (hQ.mem t ht) fun e => ?_, hy⟩
    have := (hy t ht).1; rw [e] at this; simp at this
  | recvEP q =>
    obtain ⟨h1, xs, hne, hq, hQ, hy⟩ := h
    refine ⟨h1, xs, hne, hq, QueueRel.keepS hQ fun t ht => hKT t (hQ.mem t ht) fun e => ?_, hy⟩
    have := (hy t ht).1; rw [e] at this; simp at this

theorem Notif.NtfnObjRel.keepS {n : U64} {x : Fl4Spec.Ntfn} (hKT : LiveKeep K T m) (h : NtfnObjRel m T n x) :
    NtfnObjRel m (KeepS K T) n x := by
  cases x with
  | idleNtfn => exact ⟨h.1, QueueRel.keepS h.2 (fun t ht => by cases ht)⟩
  | activeNtfn b => exact ⟨h.1, QueueRel.keepS h.2.1 (fun t ht => by cases ht), h.2.2⟩
  | waitingNtfn q =>
    obtain ⟨h1, xs, hne, hq, hQ, hy⟩ := h
    refine ⟨h1, xs, hne, hq, QueueRel.keepS hQ fun t ht => hKT t (hQ.mem t ht) fun e => ?_, hy⟩
    have := (hy t ht).1; rw [e] at this; simp at this

theorem Notif.NtfnRel1.keepS {n : U64} {x : Fl4Spec.Notification} (hKT : LiveKeep K T m)
    (hKB : m (nBoundA n) ≠ 0#u64 → K (m (nBoundA n))) (h : NtfnRel1 m T n x) :
    NtfnRel1 m (KeepS K T) n x :=
  ⟨h.obj.keepS hKT, h.bound, fun h0 => ⟨h.bound_mem h0, hKB h0⟩, h.sc⟩

/-- The reply a thread blocked receiving names is kept. -/
def RecvKeep (K : U64 → Prop) (m : U64 → U64) (t : U64) (x : Fl4Spec.Tcb) : Prop :=
  ∀ e r d, x.tcbState = .blockedOnReceive e (some r) d → K (m (tReplyA t))

theorem Endp.TcbRelE.keepS {t : U64} {x : Fl4Spec.Tcb} (h : TcbRelE R m t x) (hr : RecvKeep K m t x) :
    TcbRelE (KeepS K R) m t x := by
  refine ⟨h.st, h.blk, h.send, fun e r d hs => ⟨(h.recv e r d hs).1, fun hne => ?_⟩, h.reply, h.regs, h.prio,
    h.fault0, h.faultT, h.bound, h.faultR⟩
  obtain ⟨r0, rfl⟩ := Option.ne_none_iff_exists'.1 hne
  exact ⟨(h.recv e _ d hs).2 hne, hr e r0 d hs⟩

theorem Ipc.TcbRel.keepS {t : U64} {x : Fl4Spec.Tcb} (h : TcbRel R m t x) (hr : RecvKeep K m t x) :
    TcbRel (KeepS K R) m t x := by
  refine ⟨h.st, h.blkE, h.blkN, h.send, fun e r d hs => ⟨(h.recv e r d hs).1, fun hne => ?_⟩, h.reply, h.regs,
    h.prio, h.fault0, h.faultT, h.bound, h.faultR, h.sc⟩
  obtain ⟨r0, rfl⟩ := Option.ne_none_iff_exists'.1 hne
  exact ⟨(h.recv e _ d hs).2 hne, hr e r0 d hs⟩

variable {Z : Type} {σ : Fl4Spec.State Z}

/-- The receive-blocked threads' replies kept, for every kept thread. -/
def RecvKeepAll (K : U64 → Prop) (T : Set U64) (m : U64 → U64) (σ : Fl4Spec.State Z) : Prop :=
  ∀ t ∈ T, K t → ∀ x, σ.kheap t.bv = some (.tcb x) → RecvKeep K m t x

/-- The kept notifications' bound threads kept. -/
def BoundKeep (K : U64 → Prop) (N : Set U64) (m : U64 → U64) : Prop :=
  ∀ n ∈ N, K n → m (nBoundA n) ≠ 0#u64 → K (m (nBoundA n))

theorem Endp.EpStateRel.keepS (h : EpStateRel T E R B m σ) (hKT : LiveKeep K T m) (hr : RecvKeepAll K T m σ) :
    EpStateRel (KeepS K T) (KeepS K E) (KeepS K R) (KeepB KB B) m σ := by
  refine ⟨fun e he => ?_, fun r hr => h.reply r hr.1, fun t ht => ?_, fun wp hw => h.buf wp hw.1⟩
  · obtain ⟨x, hk, hx⟩ := h.ep e he.1
    exact ⟨x, hk, hx.keepS hKT⟩
  · obtain ⟨x, hk, hx⟩ := h.tcb t ht.1
    exact ⟨x, hk, hx.keepS (hr t ht.1 ht.2 x hk)⟩

theorem Notif.NtfnStateRel.keepS (h : NtfnStateRel N T m σ) (hKT : LiveKeep K T m) (hKB : BoundKeep K N m) :
    NtfnStateRel (KeepS K N) (KeepS K T) m σ := by
  refine ⟨fun n hn => ?_, fun t ht => h.tcb t ht.1⟩
  obtain ⟨x, hk, hx⟩ := h.ntfn n hn.1
  exact ⟨x, hk, hx.keepS hKT (hKB n hn.1 hn.2)⟩

theorem Ipc.IpcRel.keepS (h : IpcRel N T E R B m σ) (hKT : LiveKeep K T m) (hr : RecvKeepAll K T m σ)
    (hKB : BoundKeep K N m) :
    IpcRel (KeepS K N) (KeepS K T) (KeepS K E) (KeepS K R) (KeepB KB B) m σ := by
  refine ⟨fun t ht => ?_, fun n hn => ?_, fun e he => ?_, fun r hr => h.reply r hr.1, fun wp hw => h.buf wp hw.1⟩
  · obtain ⟨x, hk, hx⟩ := h.tcb t ht.1
    exact ⟨x, hk, hx.keepS (hr t ht.1 ht.2 x hk)⟩
  · obtain ⟨x, hk, hx⟩ := h.ntfn n hn.1
    exact ⟨x, hk, hx.keepS hKT (hKB n hn.1 hn.2)⟩
  · obtain ⟨x, hk, hx⟩ := h.ep e he.1
    exact ⟨x, hk, hx.keepS hKT⟩

end Ipc


section Sched
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : U64 → Prop} {KB : U64 × Fl4Spec.Word → Prop}
variable {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {s : S} {σ : Fl4Spec.State Unit}

theorem Notif.NWrite.of_keepS {a : U64} (h : NWrite (KeepS K N) (KeepS K T) a) : NWrite N T a := by
  rcases h with ⟨n, hn, h⟩ | ⟨t, ht, h⟩
  · exact Or.inl ⟨n, hn.1, h⟩
  · exact Or.inr ⟨t, ht.1, h⟩

theorem Notif.NPlaced.keepS (h : NPlaced T N) : NPlaced (KeepS K T) (KeepS K N) :=
  ⟨fun t ht => h.tcb t ht.1, fun n hn => h.ntfn n hn.1, fun n hn t ht => h.disj n hn.1 t ht.1⟩

/-- The scheduler's references kept (stage A's scheduler premises). -/
structure SchedKeep (st : machine.Store S) [L : LawfulStore st] (K : U64 → Prop) (T : Set U64) (c : U64) (s : S)
    (σ : Fl4Spec.State Unit) : Prop where
  q : ∀ t ∈ T, ((∃ d p, t.bv ∈ σ.readyQueues d p) ∨ t.bv ∈ σ.releaseQueue) → K t
  act : ∀ t ∈ T, Sched.nodeW st s c layout.node.SCHED_ACTION = t → K t
  cur : K (Sched.nodeW st s c layout.node.CUR_THREAD)
  idle : K (Sched.nodeW st s c layout.node.IDLE_THREAD)
  sc : ∀ t ∈ T, K t → L.mem s (scA t) ≠ 0#u64 → K (L.mem s (scA t))

/-- **The scheduler relation at the kept sets.** -/
theorem Sched.SchedRel.keepS (hS : Sched.SchedRel st N T C c s σ) (hK : SchedKeep st K T c s σ) :
    Sched.SchedRel st (KeepS K N) (KeepS K T) (KeepS K C) c s σ := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  refine ⟨Notif.NPlaced.keepS hS.placed, fun o ho h => hS.nodeNW o ho (Notif.NWrite.of_keepS h), fun h => hS.domNW (Notif.NWrite.of_keepS h),
    fun h => hS.dtNW (Notif.NWrite.of_keepS h), ?_, ?_, ?_, hS.act, hS.repr, fun sc hsc => hS.core sc hsc.1, Q, R0, ?_, ?_⟩
  · intro sc hsc x n hk a ha
    obtain ⟨h1, h2, h3, h4⟩ := hS.scOut sc hsc.1 x n hk a ha
    exact ⟨fun h => h1 (Notif.NWrite.of_keepS h), h2, fun t ht => h3 t ht.1, h4⟩
  · intro sc hsc sc' hsc' hne x n x' n' hk hk' a ha
    exact hS.scDisj sc hsc.1 sc' hsc'.1 hne x n x' n' hk hk' a ha
  · rcases hS.actW with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, hK.act _ h rfl⟩)
  · refine { hc with
      tcbs := fun t ht => hc.tcbs t ht.1
      node := ⟨hc.node.align, hc.node.fits, fun t ht => hc.node.disj t ht.1⟩
      aff := fun t ht => hc.aff t ht.1
      prio := fun t ht => hc.prio t ht.1
      ready := ⟨⟨fun p hp => QueueRel.keepS (hc.ready.1.rel p hp) fun t ht =>
          hK.q t ((hc.ready.1.rel p hp).mem t ht)
            (Or.inl ⟨0, Sched.specPrio p, by rw [hs.rq p hp]; exact List.mem_map.2 ⟨t, ht, rfl⟩⟩),
        hc.ready.1.disj⟩, hc.ready.2⟩
      release := QueueRel.keepS hc.release fun t ht =>
        hK.q t (hc.release.mem t ht) (Or.inr (by rw [hs.rel]; exact List.mem_map.2 ⟨t, ht, rfl⟩))
      queued := fun t ht => hc.queued t ht.1
      released := fun t ht => hc.released t ht.1
      excl := fun t ht => hc.excl t ht.1
      curT := ⟨hc.curT, hK.cur⟩
      idleT := ⟨hc.idleT, hK.idle⟩
      ksOut := fun t ht => hc.ksOut t ht.1 }
  · exact { hs with
      tcb := fun t ht => hs.tcb t ht.1
      scMem := fun t ht h0 => ⟨hs.scMem t ht.1 h0, hK.sc t ht.1 ht.2 h0⟩
      scs := fun sc hsc => hs.scs sc hsc.1 }

theorem Vs.OObj.of_keepS {a : U64} (h : Vs.OObj st (KeepS K N) (KeepS K T) (KeepS K C) (KeepS K E) (KeepS K R) (KeepB KB B) c s σ a) :
    Vs.OObj st N T C E R B c s σ a := by
  unfold Vs.OObj at h ⊢
  rcases h with h | h | ⟨t, ht, h⟩ | ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨n, hn, h⟩ | ⟨sc, hsc, h⟩ | ⟨wp, hw, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨t, ht.1, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he.1, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr.1, h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn.1, h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc.1, h⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw.1, h⟩))))))

theorem Endp.EFoot.of_keepS {a : U64} (h : EFoot (KeepS K T) (KeepS K E) (KeepS K R) (KeepB KB B) a) : EFoot T E R B a := by
  rcases h with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h⟩ | ⟨wp, hw, h⟩
  · exact Or.inl ⟨e, he.1, h⟩
  · exact Or.inr (Or.inl ⟨r, hr.1, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨t, ht.1, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨wp, hw.1, h⟩))

theorem Endp.EWrite.of_keepS {a : U64} (h : EWrite (KeepS K T) (KeepS K E) (KeepS K R) (KeepB KB B) a) : EWrite T E R B a := by
  rcases h with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h⟩ | ⟨wp, hw, h⟩
  · exact Or.inl ⟨e, he.1, h⟩
  · exact Or.inr (Or.inl ⟨r, hr.1, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨t, ht.1, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨wp, hw.1, h⟩))

theorem Ipc.IWords.of_keepS {a : U64} (h : Ipc.IWords (KeepS K N) (KeepS K T) (KeepS K E) (KeepS K R) (KeepB KB B) a) :
    Ipc.IWords N T E R B a := by
  rcases h with ⟨t, ht, h⟩ | ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨n, hn, h⟩ | ⟨wp, hw, h⟩
  · exact Or.inl ⟨t, ht.1, h⟩
  · exact Or.inr (Or.inl ⟨e, he.1, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨r, hr.1, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn.1, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw.1, h⟩)))

theorem Endp.EPlaced.keepS (h : EPlaced T E R B) : EPlaced (KeepS K T) (KeepS K E) (KeepS K R) (KeepB KB B) :=
  ⟨fun t ht => h.tcb t ht.1, fun e he => h.ep e he.1, fun r hr => h.rep r hr.1, fun e he t ht => h.et e he.1 t ht.1,
    fun r hr t ht => h.rt r hr.1 t ht.1, fun e he r hr => h.er e he.1 r hr.1, fun wp hw => h.balign wp hw.1,
    fun wp hw t ht => h.bt wp hw.1 t ht.1, fun wp hw e he => h.be wp hw.1 e he.1,
    fun wp hw r hr => h.br wp hw.1 r hr.1, fun wp hw wq hq => h.binj wp hw.1 wq hq.1⟩

theorem Vs.TopPlaced.keepS {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    (h : Vs.TopPlaced st th P L4 L3 L2 L1 N T C E R B c s σ) :
    Vs.TopPlaced st th P L4 L3 L2 L1 (KeepS K N) (KeepS K T) (KeepS K C) (KeepS K E) (KeepS K R) (KeepB KB B) c s σ :=
  { h with
    ep := Endp.EPlaced.keepS h.ep
    disj := fun a ha => h.disj a (Vs.OObj.of_keepS ha)
    nodeE := fun a h1 h2 he => h.nodeE a h1 h2 (Endp.EFoot.of_keepS he) }

theorem Ipc.EpSchedApart.keepS (h : Ipc.EpSchedApart st T C E R B c s σ) :
    Ipc.EpSchedApart st (KeepS K T) (KeepS K C) (KeepS K E) (KeepS K R) (KeepB KB B) c s σ :=
  ⟨fun a h1 h2 he => h.node a h1 h2 (Endp.EFoot.of_keepS he), fun he => h.dom (Endp.EWrite.of_keepS he),
    fun he => h.dt (Endp.EWrite.of_keepS he), fun sc hsc x n hk a ha he => h.sc sc hsc.1 x n hk a ha (Endp.EWrite.of_keepS he)⟩

theorem Ipc.IpcApart.keepS {th : TypedHeap} {kb : U64} (h : Ipc.IpcApart th N T E R B kb c) :
    Ipc.IpcApart th (KeepS K N) (KeepS K T) (KeepS K E) (KeepS K R) (KeepB KB B) kb c :=
  { h with slot := fun a ha => h.slot a (Ipc.IWords.of_keepS ha), dom := fun a ha => h.dom a (Ipc.IWords.of_keepS ha) }

theorem Ipc.ScApart.keepS {th : TypedHeap} (h : Ipc.ScApart th C σ) : Ipc.ScApart th (KeepS K C) σ :=
  fun sc hsc => h sc hsc.1

end Sched

section XTop
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type}
variable {K : U64 → Prop} {KB : U64 × Fl4Spec.Word → Prop}

/-- `Z` with the IPC and scheduler sets cut to their kept parts (the typed
heap, the ghost tree and the VSpace sets unchanged). -/
abbrev XSets.keep (Z : XSets) (K : U64 → Prop) (KB : U64 × Fl4Spec.Word → Prop) : XSets :=
  ⟨Z.th, Z.G, Z.P, Z.L4, Z.L3, Z.L2, Z.L1, KeepS K Z.N, KeepS K Z.T, KeepS K Z.C, KeepS K Z.E, KeepS K Z.R,
    KeepB KB Z.B, Z.c⟩

/-- Stage A's premises at `Z`, `s`, `σ`. -/
structure XKeep (st : machine.Store S) [L : LawfulStore st] (K : U64 → Prop) (Z : XSets) (s : S)
    (σ : Fl4Spec.State Unit) : Prop where
  live : LiveKeep K Z.T (L.mem s)
  recv : RecvKeepAll K Z.T (L.mem s) σ
  bound : BoundKeep K Z.N (L.mem s)
  sched : SchedKeep st K Z.T Z.c s σ

/-- **Stage A: `XTopAt` at the kept sets** (module docstring). -/
theorem XTopAt.keepS {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (hK : XKeep st K Z s σ) : XTopAt (L := L) AR (Z.keep K KB) s a σ := by
  obtain ⟨⟨⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hP⟩, hR, hPt, hPI, hCO⟩,
    ⟨hPl, hCR, hFI, hD, hMO, hIA, hSA⟩, hI, hE⟩ := hX
  exact ⟨⟨⟨⟨Sched.SchedRel.keepS hSch hK.sched, hEp.keepS hK.live hK.recv, hNt.keepS hK.live hK.bound, hIrq, hIo, hKr,
      hAr⟩, Vs.TopPlaced.keepS hP⟩, hR, hPt, hPI, hCO⟩,
    ⟨hPl, hCR, hFI, hD, hMO, IpcApart.keepS hIA, ScApart.keepS hSA⟩, hI.keepS hK.live hK.recv hK.bound,
    EpSchedApart.keepS hE⟩

end XTop

end

end Fl4Proofs.P3
