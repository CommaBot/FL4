/-
P3 (DESIGN.md §9), IPC: **the spec's frame of `send_signal`'s wake-up with
an SC donation** (spec side only), toward `SignalRestJHyp` (ScSignalJ).

The waking branches of `send_signal` (a waiting notification `r`'s head, or
`r`'s bound thread `t` blocked receiving, after its `cancel_ipc`) may donate
`r`'s SC to the woken thread `t` (`maybe_donate_sc`: `t` without an SC, the
SC bound to no thread): `schedContextDonate` sets `t`'s `tcb_sched_context`
and the SC's `sc_tcb`, `schedContextResume` may `postpone` `t` into the
release queue. `CFr` (IpcSignalBoundFr) fixes both fields and the release
queue, so:

* `SkD`: `Sk` without the release queue.
* `DChg`: `CChg`'s change, a TCB's SC and an SC's thread left free (the
  frame's `tsc` and `scb` say which may change).
* `DWFr r t`: `SkD`; the release queue grows only by `t`, whose SC was none;
  objectwise `DChg`; a TCB's SC changes only for `t`, from none; an SC's
  thread changes only for a notification's SC (so not dead) that is not the
  current one, or with `t` then owning the current SC (`CurOwnT`: its SC, the
  SC's thread, not in the release queue while time is consumed).
* `DWFr.ofCFr`, `DWFr.ofNFr`, `DWFr.trans`, the per-kind lemmas and `CFr`'s
  keep lemmas (`own`, `off`, `curInv`, `curRunW`, `idleOK`, `sched`: a TCB
  whose SC changes had none, so it is not the current thread, the owner or
  the idle thread; the current SC's thread is kept, or `t` owns it: `own`
  then takes `t` as `CurOwnW`'s owner).
* `donate_dfr`: `maybeDonateSc t r` from a state where `t` is in no queue is
  a `DWFr r t` step keeping the action, given `OffOK`: a donated current SC
  has a ready and sufficient head refill while time is consumed, so `t` is
  not postponed then.
-/
import Fl4Proofs.P3.IpcSignalBoundSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- `Sk` without the release queue. -/
structure SkD (σ σ' : State Unit) : Prop where
  ct : σ'.curThread = σ.curThread
  idle : σ'.idleThread = σ.idleThread
  cons : σ'.consumedTime = σ.consumedTime
  tm : σ'.curTime = σ.curTime
  csc : σ'.curSc = σ.curSc
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap
  arch : σ'.archState = σ.archState
  dt : σ'.domainTime = σ.domainTime

theorem SkD.refl (σ : State Unit) : SkD σ σ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SkD.trans {σ1 σ2 σ3 : State Unit} (h1 : SkD σ1 σ2) (h2 : SkD σ2 σ3) : SkD σ1 σ3 :=
  ⟨h2.ct.trans h1.ct, h2.idle.trans h1.idle, h2.cons.trans h1.cons, h2.tm.trans h1.tm, h2.csc.trans h1.csc,
    h2.cdt.trans h1.cdt, h2.orig.trans h1.orig, h2.arch.trans h1.arch, h2.dt.trans h1.dt⟩

theorem Sk.toD {σ σ' : State Unit} (h : Sk σ σ') : SkD σ σ' :=
  ⟨h.ct, h.idle, h.cons, h.tm, h.csc, h.cdt, h.orig, h.arch, h.dt⟩

/-- **One object's change** (module docstring). -/
def DChg (r t cur p : ObjRef) (o o' : KernelObject) : Prop :=
  (∃ x st bn fl ar sc, o = .tcb x ∧
    o' = .tcb { x with tcbState := st, tcbBoundNotification := bn, tcbFault := fl, tcbArch := ar, tcbSchedContext := sc } ∧ TCX r t p x st bn fl ar) ∨
  (∃ y n rf nt tc, o = .schedContext y n ∧ o' = .schedContext { y with scRefills := rf, scNtfn := nt, scTcb := tc } n ∧
    (p = cur → rf = y.scRefills) ∧ (nt = y.scNtfn ∨ nt = none)) ∨
  (∃ x y, o = .notification x ∧ o' = .notification y ∧ p = r ∧
    y.ntfnObj.ntfnQueue.Sublist x.ntfnObj.ntfnQueue ∧
    (y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none) ∧ ((∀ l, x.ntfnObj ≠ .waitingNtfn l) → NObj x.ntfnObj y.ntfnObj) ∧
    (y.ntfnBoundTcb = x.ntfnBoundTcb ∨ y.ntfnBoundTcb = none)) ∨
  (∃ x y, o = .endpoint x ∧ o' = .endpoint y ∧ y.epQueue.Sublist x.epQueue ∧ t ∈ x.epQueue) ∨
  (∃ x, o = .reply x ∧ o' = .reply { x with replyTcb := none } ∧ x.replyTcb = some t)

theorem DChg.trans {r t cur p : ObjRef} {o1 o2 o3 : KernelObject} (h1 : DChg r t cur p o1 o2)
    (h2 : DChg r t cur p o2 o3) : DChg r t cur p o1 o3 := by
  rcases h1 with ⟨x, st, bn, fl, ar, sc, rfl, rfl, hc⟩ | ⟨y, n, rf, nt, tc, rfl, rfl, hr, hn⟩ |
    ⟨x, y, rfl, rfl, hp, hq, hs, hw, hb⟩ | ⟨x, y, rfl, rfl, hs, hm⟩ | ⟨x, rfl, rfl, hx⟩
  · rcases h2 with ⟨x2, st2, bn2, fl2, ar2, sc2, e, rfl, hc2⟩ | ⟨_, _, _, _, _, e, -⟩ | ⟨_, _, e, -⟩ |
      ⟨_, _, e, -⟩ | ⟨_, e, -⟩ <;> cases e
    exact Or.inl ⟨x, st2, bn2, fl2, ar2, sc2, rfl, rfl, hc.trans hc2⟩
  · rcases h2 with ⟨_, _, _, _, _, _, e, -⟩ | ⟨y2, n2, rf2, nt2, tc2, e, rfl, hr2, hn2⟩ | ⟨_, _, e, -⟩ |
      ⟨_, _, e, -⟩ | ⟨_, e, -⟩ <;> cases e
    exact Or.inr (Or.inl ⟨y, n, rf2, nt2, tc2, rfl, rfl, fun h => (hr2 h).trans (hr h), or_none_trans hn hn2⟩)
  · rcases h2 with ⟨_, _, _, _, _, _, e, -⟩ | ⟨_, _, _, _, _, e, -⟩ | ⟨y2, z, e, rfl, -, hq2, hs2, hw2, hb2⟩ |
      ⟨_, _, e, -⟩ | ⟨_, e, -⟩ <;> cases e
    exact Or.inr (Or.inr (Or.inl ⟨x, z, rfl, rfl, hp, hq2.trans hq, or_none_trans hs hs2,
      fun h => (hw h).trans (hw2 ((hw h).nw h)), or_none_trans hb hb2⟩))
  · rcases h2 with ⟨_, _, _, _, _, _, e, -⟩ | ⟨_, _, _, _, _, e, -⟩ | ⟨_, _, e, -⟩ |
      ⟨x2, z, e, rfl, hs2, -⟩ | ⟨_, e, -⟩ <;> cases e
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, z, rfl, rfl, hs2.trans hs, hm⟩)))
  · rcases h2 with ⟨_, _, _, _, _, _, e, -⟩ | ⟨_, _, _, _, _, e, -⟩ | ⟨_, _, e, -⟩ |
      ⟨_, _, e, -⟩ | ⟨x2, e, rfl, hx2⟩ <;> cases e
    simp at hx2

/-- **`t` owns the current SC**: `t`'s SC is the current SC, the current SC's
thread is `t`, and `t` is not in the release queue while time is consumed
(`CurOwn`'s owner; after a donation of the current SC to `t`). -/
def CurOwnT (t : ObjRef) (σ : State Unit) : Prop :=
  ∃ xt, σ.kheap t = some (.tcb xt) ∧ xt.tcbSchedContext = some σ.curSc ∧
    (∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scTcb = some t) ∧
    (0 < σ.consumedTime → t ∉ σ.releaseQueue)

/-- **The spec's frame of a wake-up with a donation** (module docstring). -/
structure DWFr (r t : ObjRef) (σ σ' : State Unit) : Prop where
  sk : SkD σ σ'
  rel : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue ∨
    (u = t ∧ ∀ x, σ.kheap t = some (.tcb x) → x.tcbSchedContext = none)
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ o o', σ.kheap p = some o ∧ σ'.kheap p = some o' ∧ DChg r t σ.curSc p o o'
  tsc : ∀ p x y, σ.kheap p = some (.tcb x) → σ'.kheap p = some (.tcb y) → y.tcbSchedContext ≠ x.tcbSchedContext →
    p = t ∧ x.tcbSchedContext = none
  scb : ∀ p y n z m, σ.kheap p = some (.schedContext y n) → σ'.kheap p = some (.schedContext z m) →
    z.scTcb ≠ y.scTcb → (p ≠ σ.curSc ∨ CurOwnT t σ') ∧ ∃ q xq, σ.kheap q = some (.notification xq) ∧
      xq.ntfnSc = some p

section
variable {r t : ObjRef} {σ σ' : State Unit}

/-! ### Per kind -/

theorem DWFr.tcbF (h : DWFr r t σ σ') {p : ObjRef} {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    ∃ st bn fl ar sc, σ'.kheap p = some (.tcb { x with tcbState := st, tcbBoundNotification := bn, tcbFault := fl, tcbArch := ar, tcbSchedContext := sc }) ∧ TCX r t p x st bn fl ar := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x.tcbState, x.tcbBoundNotification, x.tcbFault, x.tcbArch, x.tcbSchedContext, by rw [e, hp],
      Or.inl ⟨Or.inl ⟨rfl, rfl⟩, rfl, Or.inl rfl⟩⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨x', st, bn, fl, ar, sc, e1, rfl, hs⟩ | ⟨_, _, _, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ |
      ⟨_, _, e1, -⟩ | ⟨_, e1, -⟩ <;> cases e1
    exact ⟨st, bn, fl, ar, sc, h2, hs⟩

theorem DWFr.tcbB (h : DWFr r t σ σ') {p : ObjRef} {y : Tcb} (hp : σ'.kheap p = some (.tcb y)) :
    ∃ x st bn fl ar sc, σ.kheap p = some (.tcb x) ∧
      y = { x with tcbState := st, tcbBoundNotification := bn, tcbFault := fl, tcbArch := ar, tcbSchedContext := sc } ∧ TCX r t p x st bn fl ar := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, y.tcbState, y.tcbBoundNotification, y.tcbFault, y.tcbArch, y.tcbSchedContext, by rw [← e, hp], rfl,
      Or.inl ⟨Or.inl ⟨rfl, rfl⟩, rfl, Or.inl rfl⟩⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨x, st, bn, fl, ar, sc, rfl, e2, hs⟩ | ⟨_, _, _, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ |
      ⟨_, _, -, e2, -⟩ | ⟨_, -, e2, -⟩ <;> cases e2
    exact ⟨x, st, bn, fl, ar, sc, h1, rfl, hs⟩

theorem DWFr.scF (h : DWFr r t σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ.kheap p = some (.schedContext y n)) :
    ∃ rf nt tc, σ'.kheap p = some (.schedContext { y with scRefills := rf, scNtfn := nt, scTcb := tc } n) ∧
      (p = σ.curSc → rf = y.scRefills) ∧ (nt = y.scNtfn ∨ nt = none) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y.scRefills, y.scNtfn, y.scTcb, by rw [e, hp], fun _ => rfl, Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, _, _, _, e1, -⟩ | ⟨y', n', rf, nt, tc, e1, rfl, hr, hn⟩ | ⟨_, _, e1, -⟩ |
      ⟨_, _, e1, -⟩ | ⟨_, e1, -⟩ <;> cases e1
    exact ⟨rf, nt, tc, h2, hr, hn⟩

theorem DWFr.scB (h : DWFr r t σ σ') {p : ObjRef} {z : SchedContext} {n : Nat}
    (hp : σ'.kheap p = some (.schedContext z n)) :
    ∃ y rf nt tc, σ.kheap p = some (.schedContext y n) ∧ z = { y with scRefills := rf, scNtfn := nt, scTcb := tc } ∧
      (p = σ.curSc → rf = y.scRefills) ∧ (nt = y.scNtfn ∨ nt = none) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨z, z.scRefills, z.scNtfn, z.scTcb, by rw [← e, hp], rfl, fun _ => rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, _, _, _, -, e2, -⟩ | ⟨y, n', rf, nt, tc, rfl, e2, hr, hn⟩ | ⟨_, _, -, e2, -⟩ |
      ⟨_, _, -, e2, -⟩ | ⟨_, -, e2, -⟩ <;> cases e2
    exact ⟨y, rf, nt, tc, h1, rfl, hr, hn⟩

theorem DWFr.ntfnB (h : DWFr r t σ σ') {p : ObjRef} {y : Notification} (hp : σ'.kheap p = some (.notification y)) :
    ∃ x, σ.kheap p = some (.notification x) ∧ (p ≠ r → y = x) ∧
      y.ntfnObj.ntfnQueue.Sublist x.ntfnObj.ntfnQueue ∧
      (y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none) ∧ ((∀ l, x.ntfnObj ≠ .waitingNtfn l) → NObj x.ntfnObj y.ntfnObj) ∧
      (y.ntfnBoundTcb = x.ntfnBoundTcb ∨ y.ntfnBoundTcb = none) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e, hp], fun _ => rfl, List.Sublist.refl _, Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, _, _, _, -, e2, -⟩ | ⟨_, _, _, _, _, -, e2, -⟩ | ⟨x, y', rfl, e2, hpr, hq, hs, hw, hb⟩ |
      ⟨_, _, -, e2, -⟩ | ⟨_, -, e2, -⟩ <;> cases e2
    exact ⟨x, h1, fun hne => absurd hpr hne, hq, hs, hw, hb⟩

theorem DWFr.ntfnF (h : DWFr r t σ σ') {p : ObjRef} {x : Notification} (hp : σ.kheap p = some (.notification x)) :
    ∃ y, σ'.kheap p = some (.notification y) ∧ (p ≠ r → y = x) ∧
      ((∀ l, x.ntfnObj ≠ .waitingNtfn l) → NObj x.ntfnObj y.ntfnObj) ∧
      (y.ntfnBoundTcb = x.ntfnBoundTcb ∨ y.ntfnBoundTcb = none) ∧ (y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [e, hp], fun _ => rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, _, _, _, e1, -⟩ | ⟨_, _, _, _, _, e1, -⟩ | ⟨x', y, e1, rfl, hpr, -, hs, hw, hb⟩ |
      ⟨_, _, e1, -⟩ | ⟨_, e1, -⟩ <;> cases e1
    exact ⟨y, h2, fun hne => absurd hpr hne, hw, hb, hs⟩

theorem DWFr.epF (h : DWFr r t σ σ') {p : ObjRef} {x : Endpoint} (hp : σ.kheap p = some (.endpoint x)) :
    ∃ y, σ'.kheap p = some (.endpoint y) ∧ (y = x ∨ (y.epQueue.Sublist x.epQueue ∧ t ∈ x.epQueue)) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [e, hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, _, _, _, e1, -⟩ | ⟨_, _, _, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ |
      ⟨x', y, e1, rfl, hs, hm⟩ | ⟨_, e1, -⟩ <;> cases e1
    exact ⟨y, h2, Or.inr ⟨hs, hm⟩⟩

theorem DWFr.epB (h : DWFr r t σ σ') {p : ObjRef} {y : Endpoint} (hp : σ'.kheap p = some (.endpoint y)) :
    ∃ x, σ.kheap p = some (.endpoint x) ∧ (y = x ∨ (y.epQueue.Sublist x.epQueue ∧ t ∈ x.epQueue)) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e, hp], Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, _, _, _, -, e2, -⟩ | ⟨_, _, _, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ |
      ⟨x, y', rfl, e2, hs, hm⟩ | ⟨_, -, e2, -⟩ <;> cases e2
    exact ⟨x, h1, Or.inr ⟨hs, hm⟩⟩

theorem DWFr.replyF (h : DWFr r t σ σ') {p : ObjRef} {x : Reply} (hp : σ.kheap p = some (.reply x)) :
    ∃ y, σ'.kheap p = some (.reply y) ∧ y.replySc = x.replySc ∧
      (y.replyTcb = x.replyTcb ∨ (x.replyTcb = some t ∧ y.replyTcb = none)) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [e, hp], rfl, Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, _, _, _, e1, -⟩ | ⟨_, _, _, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ |
      ⟨_, _, e1, -⟩ | ⟨x', e1, rfl, hx⟩ <;> cases e1
    exact ⟨_, h2, rfl, Or.inr ⟨hx, rfl⟩⟩

theorem DWFr.replyB (h : DWFr r t σ σ') {p : ObjRef} {y : Reply} (hp : σ'.kheap p = some (.reply y)) :
    ∃ x, σ.kheap p = some (.reply x) ∧ y.replySc = x.replySc ∧
      (y.replyTcb = x.replyTcb ∨ (x.replyTcb = some t ∧ y.replyTcb = none)) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e, hp], rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, _, _, _, -, e2, -⟩ | ⟨_, _, _, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ |
      ⟨_, _, -, e2, -⟩ | ⟨x, rfl, e2, hx⟩ <;> cases e2
    exact ⟨x, h1, rfl, Or.inr ⟨hx, rfl⟩⟩

/-- The other kinds kept. -/
theorem DWFr.othF (h : DWFr r t σ σ') {p : ObjRef} {o : KernelObject} (hp : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h2 : ∀ y n, o ≠ .schedContext y n) (h3 : ∀ x, o ≠ .notification x)
    (h4 : ∀ x, o ≠ .endpoint x) (h5 : ∀ x, o ≠ .reply x) : σ'.kheap p = some o := by
  rcases h.kh p with e | ⟨o0, o', k1, k2, hc⟩
  · rw [e, hp]
  · rw [hp] at k1; cases k1
    rcases hc with ⟨_, _, _, _, _, _, e1, -⟩ | ⟨_, _, _, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, e1, -⟩
    · exact absurd e1 (h1 _)
    · exact absurd e1 (h2 _ _)
    · exact absurd e1 (h3 _)
    · exact absurd e1 (h4 _)
    · exact absurd e1 (h5 _)

theorem DWFr.othB (h : DWFr r t σ σ') {p : ObjRef} {o' : KernelObject} (hp : σ'.kheap p = some o')
    (h1 : ∀ x, o' ≠ .tcb x) (h2 : ∀ y n, o' ≠ .schedContext y n) (h3 : ∀ x, o' ≠ .notification x)
    (h4 : ∀ x, o' ≠ .endpoint x) (h5 : ∀ x, o' ≠ .reply x) : σ.kheap p = some o' := by
  rcases h.kh p with e | ⟨o, o'', k1, k2, hc⟩
  · rw [← e, hp]
  · rw [hp] at k2; cases k2
    rcases hc with ⟨_, _, _, _, _, _, -, e2, -⟩ | ⟨_, _, _, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ |
      ⟨_, _, -, e2, -⟩ | ⟨_, -, e2, -⟩
    · exact absurd e2 (h1 _)
    · exact absurd e2 (h2 _ _)
    · exact absurd e2 (h3 _)
    · exact absurd e2 (h4 _)
    · exact absurd e2 (h5 _)

/-- The objects' kinds and sizes kept, both ways. -/
theorem DWFr.kind (h : DWFr r t σ σ') (p : ObjRef) :
    (∀ o, σ.kheap p = some o → ∃ o', σ'.kheap p = some o' ∧ aType o' = aType o) ∧
    (∀ o', σ'.kheap p = some o' → ∃ o, σ.kheap p = some o ∧ aType o' = aType o) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨fun o ho => ⟨o, by rw [e, ho], rfl⟩, fun o' ho => ⟨o', by rw [← e, ho], rfl⟩⟩
  · have ha : aType o' = aType o := by
      rcases hc with ⟨x, st, bn, fl, ar, sc, rfl, rfl, -⟩ | ⟨y, n, rf, nt, tc, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ |
        ⟨x, y, rfl, rfl, -⟩ | ⟨x, rfl, rfl, -⟩ <;> rfl
    exact ⟨fun o0 ho0 => ⟨o', h2, by rw [h1] at ho0; cases ho0; exact ha⟩,
      fun o0 ho0 => ⟨o, h1, by rw [h2] at ho0; cases ho0; exact ha⟩⟩

/-- A TCB with an SC keeps it. -/
theorem DWFr.tsc_some (h : DWFr r t σ σ') {p : ObjRef} {x y : Tcb} (hx : σ.kheap p = some (.tcb x))
    (hy : σ'.kheap p = some (.tcb y)) {c : ObjRef} (hc : x.tcbSchedContext = some c) :
    y.tcbSchedContext = some c := by
  by_contra hne
  have := (h.tsc p x y hx hy (fun e => hne (e.trans hc))).2
  rw [hc] at this; cases this

/-- The current SC's thread kept, unless `t` owns it after. -/
theorem DWFr.cur_tcb (h : DWFr r t σ σ') (hT : ¬ CurOwnT t σ') {y z : SchedContext} {n m : Nat}
    (hy : σ.kheap σ.curSc = some (.schedContext y n)) (hz : σ'.kheap σ.curSc = some (.schedContext z m)) :
    z.scTcb = y.scTcb := by
  by_contra hne
  exact ((h.scb _ y n z m hy hz hne).1.resolve_right hT) rfl

/-- A thread in the release queue after was there before, or is `t` without
an SC before. -/
theorem DWFr.relT (h : DWFr r t σ σ') {u : ObjRef} {x : Tcb} (hx : σ.kheap u = some (.tcb x)) {c : ObjRef}
    (hc : x.tcbSchedContext = some c) (hu : u ∈ σ'.releaseQueue) : u ∈ σ.releaseQueue := by
  rcases h.rel u hu with h' | ⟨rfl, hn⟩
  · exact h'
  · have := hn x hx; rw [hc] at this; cases this

/-- `t`'s ownership of the current SC is kept (its SC, the SC's thread unless
`t` owns it after anyway, the release queue grown only by SC-less `t`). -/
theorem DWFr.curOwnT (h : DWFr r t σ σ') (hc : CurOwnT t σ) : CurOwnT t σ' := by
  by_cases hT : CurOwnT t σ'
  · exact hT
  obtain ⟨xt, hkt, hxs, hown, hnr⟩ := hc
  obtain ⟨st, bn, fl, ar, sc, hkt', -⟩ := h.tcbF hkt
  refine ⟨_, hkt', by rw [h.sk.csc]; exact h.tsc_some hkt hkt' hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
  · rw [h.sk.csc] at hy
    obtain ⟨y0, rf, nt, tc, hy0, rfl, -⟩ := h.scB hy
    rw [h.cur_tcb hT hy0 hy]; exact hown y0 n hy0
  · rw [h.sk.cons] at h0
    exact hnr h0 (h.relT hkt hxs hm)

end

/-! ### Building the frame -/

theorem DWFr.refl (r t : ObjRef) (σ : State Unit) : DWFr r t σ σ :=
  ⟨SkD.refl σ, fun _ hu => Or.inl hu, fun _ => Or.inl rfl,
    fun p x y hx hy hne => absurd (by rw [hx] at hy; cases hy; rfl) hne,
    fun p y n z m hy hz hne => absurd (by rw [hy] at hz; cases hz; rfl) hne⟩

theorem DWFr.trans {r t : ObjRef} {σ1 σ2 σ3 : State Unit} (h1 : DWFr r t σ1 σ2) (h2 : DWFr r t σ2 σ3) :
    DWFr r t σ1 σ3 := by
  have hc2 : σ2.curSc = σ1.curSc := h1.sk.csc
  refine ⟨h1.sk.trans h2.sk, fun u hu => ?_, fun p => ?_, fun p x y hx hy hne => ?_,
    fun p y n z m hy hz hne => ?_⟩
  · rcases h2.rel u hu with h | ⟨rfl, hn⟩
    · exact h1.rel u h
    · right
      refine ⟨rfl, fun x hx => ?_⟩
      obtain ⟨st, bn, fl, ar, sc, hx2, -⟩ := h1.tcbF hx
      have h0 := hn _ hx2
      by_cases e : sc = x.tcbSchedContext
      · rw [← e]; exact h0
      · exact (h1.tsc u x _ hx hx2 e).2
  · rcases h2.kh p with e2 | ⟨o2, o3, k2, k3, c2⟩
    · rw [e2]; exact h1.kh p
    · rw [hc2] at c2
      rcases h1.kh p with e1 | ⟨o1, o2', k1, k2', c1⟩
      · exact Or.inr ⟨o2, o3, by rw [← e1]; exact k2, k3, c2⟩
      · obtain rfl := Option.some.inj (k2'.symm.trans k2)
        exact Or.inr ⟨o1, o3, k1, k3, c1.trans c2⟩
  · obtain ⟨st, bn, fl, ar, sc, hx2, -⟩ := h1.tcbF hx
    by_cases e : sc = x.tcbSchedContext
    · have e' : y.tcbSchedContext ≠ sc := fun e'' => hne (e''.trans e)
      obtain ⟨h3, h4⟩ := h2.tsc p _ y hx2 hy e'
      exact ⟨h3, e ▸ h4⟩
    · exact h1.tsc p x _ hx hx2 e
  · obtain ⟨rf, nt, tc, hy2, -⟩ := h1.scF hy
    by_cases e : tc = y.scTcb
    · have e' : z.scTcb ≠ tc := fun e'' => hne (e''.trans e)
      obtain ⟨h3, q, xq, hq, hqs⟩ := h2.scb p _ n z m hy2 hz e'
      rw [hc2] at h3
      obtain ⟨x0, hx0, -, -, hs, -⟩ := h1.ntfnB hq
      refine ⟨h3, q, x0, hx0, ?_⟩
      rcases hs with e1 | e1
      · rw [← e1]; exact hqs
      · rw [e1] at hqs; cases hqs
    · obtain ⟨h3, h4⟩ := h1.scb p y n _ n hy hy2 e
      exact ⟨h3.imp_right h2.curOwnT, h4⟩

/-- `CFr r t` is a `DWFr r t`. -/
theorem DWFr.ofCFr {r t : ObjRef} {σ σ' : State Unit} (h : CFr r t σ σ') : DWFr r t σ σ' := by
  refine ⟨Sk.toD h.sk, fun u hu => Or.inl (by rw [← h.sk.rel]; exact hu), ?_, ?_, ?_⟩
  · intro p
    rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
    · exact Or.inl e
    refine Or.inr ⟨o, o', h1, h2, ?_⟩
    rcases hc with ⟨x, st, bn, fl, ar, rfl, rfl, hc⟩ | ⟨hn, hnt⟩ | hc | hc
    · exact Or.inl ⟨x, st, bn, fl, ar, x.tcbSchedContext, rfl, rfl, hc⟩
    · rcases hn with ⟨x, _, _, _, e, -⟩ | ⟨y, n, rf, nt, rfl, rfl, hr, hn⟩ | ⟨x, y, rfl, rfl, hp, hq, -, hs, hw, hb⟩
      · exact absurd e (hnt x)
      · exact Or.inr (Or.inl ⟨y, n, rf, nt, y.scTcb, rfl, rfl, fun e => hr (Or.inl e), hn⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨x, y, rfl, rfl, hp, hq, hs, hw, hb⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hc)))
  · intro p x y hx hy hne
    obtain ⟨st, bn, fl, ar, hy', -⟩ := h.tcbF hx
    rw [hy] at hy'; cases hy'
    exact absurd rfl hne
  · intro p y n z m hy hz hne
    obtain ⟨rf, nt, hz', -⟩ := h.scF hy
    rw [hz] at hz'; cases hz'
    exact absurd rfl hne

/-- `NFr false r` is a `DWFr r t`. -/
theorem DWFr.ofNFr {r t : ObjRef} {σ σ' : State Unit} (h : NFr false r σ σ') : DWFr r t σ σ' :=
  DWFr.ofCFr (CFr.ofNFr h)

/-! ### What the frame keeps -/

section
variable {r t : ObjRef} {σ σ' : State Unit}

theorem DWFr.szKeep (h : DWFr r t σ σ') : SzKeep σ σ' := fun p y n hp => by
  obtain ⟨y0, -, -, -, hy0, -⟩ := h.scB hp; exact ⟨y0, hy0⟩

theorem DWFr.ykeep (h : DWFr r t σ σ') : YKeep σ σ' := by
  refine ⟨fun p x hp => ?_, fun p y n hp => ?_, fun p z n hp => ?_⟩
  · obtain ⟨st, bn, fl, ar, sc, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩
  · obtain ⟨rf, nt, tc, hp', -⟩ := h.scF hp; exact ⟨_, hp', rfl⟩
  · obtain ⟨y0, rf, nt, tc, hy0, rfl, -⟩ := h.scB hp; exact ⟨y0, hy0, rfl⟩

theorem DWFr.mcpKeep (h : DWFr r t σ σ') : McpKeep σ σ' := fun p x hp => by
  obtain ⟨st, bn, fl, ar, sc, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem DWFr.bufKeep (h : DWFr r t σ σ') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => by obtain ⟨st, bn, fl, ar, sc, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem DWFr.prio (h : DWFr r t σ σ') (u : ObjRef) : prioOf σ' u = prioOf σ u := by
  unfold prioOf
  rw [tcbsOf_eq, tcbsOf_eq]
  cases hk : σ.kheap u with
  | some o =>
    cases o with
    | tcb x =>
      obtain ⟨st, bn, fl, ar, sc, hk', -⟩ := h.tcbF hk
      rw [hk']; rfl
    | _ =>
      cases hk' : σ'.kheap u with
      | none => rfl
      | some o' => cases o' with
        | tcb y => obtain ⟨x, -, -, -, -, -, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
        | _ => rfl
  | none =>
    cases hk' : σ'.kheap u with
    | none => rfl
    | some o' => cases o' with
      | tcb y => obtain ⟨x, -, -, -, -, -, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
      | _ => rfl

theorem DWFr.nsc {N C : Set U64} (h : DWFr r t σ σ') (hN : NSC N C σ) : NSC N C σ' := by
  intro n hn y p hy hp
  obtain ⟨x, hx, -, -, hs, -, -⟩ := h.ntfnB hy
  rcases hs with e | e
  · exact hN n hn x p hx (e ▸ hp)
  · rw [e] at hp; cases hp

theorem DWFr.isorted (h : DWFr r t σ σ') (hS : IpcSorted σ) : IpcSorted σ' := by
  refine ⟨fun p y hp => ?_, fun p y hp => ?_⟩
  · obtain ⟨x, hx, hc⟩ := h.epB hp
    rcases hc with rfl | ⟨hsub, -⟩
    · exact (hS.1 p y hx).congr fun u _ => h.prio u
    · exact ((hS.1 p x hx).sublist hsub).congr fun u _ => h.prio u
  · obtain ⟨x, hx, -, hsub, -⟩ := h.ntfnB hp
    exact ((hS.2 p x hx).sublist hsub).congr fun u _ => h.prio u

theorem DWFr.own {T C : Set U64} (h : DWFr r t σ σ') (ht : ∃ u ∈ T, u.bv = t) (hO : CurOwnW T C σ) :
    CurOwnW T C σ' := by
  by_cases hT : CurOwnT t σ'
  · obtain ⟨u, hu, rfl⟩ := ht
    obtain ⟨xt, hkt, hxs, hown, hnr⟩ := hT
    exact Or.inl ⟨u, hu, xt, hkt, hxs, hown, hnr⟩
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · obtain ⟨st, bn, fl, ar, sc, hkt', -⟩ := h.tcbF hkt
    refine Or.inl ⟨u, hu, _, hkt', by rw [h.sk.csc]; exact h.tsc_some hkt hkt' hxs, fun y n hy => ?_,
      fun h0 hm => ?_⟩
    · rw [h.sk.csc] at hy
      obtain ⟨y0, rf, nt, tc, hy0, rfl, -⟩ := h.scB hy
      rw [h.cur_tcb hT hy0 hy]; exact hown y0 n hy0
    · rw [h.sk.cons] at h0
      exact hnr h0 (h.relT hkt hxs hm)
  · refine Or.inr ⟨by rw [h.sk.csc]; exact hcs, fun y n hy => ?_⟩
    rw [h.sk.csc] at hy
    obtain ⟨y0, rf, nt, tc, hy0, rfl, -⟩ := h.scB hy
    rw [h.cur_tcb hT hy0 hy]; exact hun y0 n hy0

theorem DWFr.off (h : DWFr r t σ σ') (hO : OffOK σ) : OffOK σ' := by
  intro hc y n hy ha
  rw [h.sk.cons] at hc ⊢; rw [h.sk.tm]
  rw [h.sk.csc] at hy ha
  obtain ⟨y0, rf, nt, tc, hy0, rfl, hr, -⟩ := h.scB hy
  have e : rf = y0.scRefills := hr rfl
  subst e
  exact hO hc y0 n hy0 ha

theorem DWFr.idleOK (h : DWFr r t σ σ') (hO : IdleOK σ) : IdleOK σ' := by
  obtain ⟨x, hx, h1, h2, h3⟩ := hO
  obtain ⟨st, bn, fl, ar, sc, hx', hs⟩ := h.tcbF hx
  refine ⟨_, by rw [h.sk.idle]; exact hx', h.tsc_some hx hx' h1, ?_,
    fun hm => h3 (h.relT hx h1 (by rw [← h.sk.idle]; exact hm))⟩
  show st = _
  rw [hs.st (by rw [h2]; nofun) (by rw [h2]; rintro (⟨_, _, _, e⟩ | e) <;> cases e)]; exact h2

theorem DWFr.curInv (h : DWFr r t σ σ') (hC : CurInv σ) : CurInv σ' := by
  obtain ⟨xt, hkt, hxs, hnb⟩ := hC.tcb
  obtain ⟨x, n, hx⟩ := hC.sc
  obtain ⟨st, bn, fl, ar, sc, hkt', hs⟩ := h.tcbF hkt
  obtain ⟨rf, nt, tc, hx', -⟩ := h.scF hx
  refine ⟨⟨_, by rw [h.sk.ct]; exact hkt', by rw [h.sk.csc]; exact h.tsc_some hkt hkt' hxs, hs.notIpc hnb⟩,
    ⟨_, n, by rw [h.sk.csc]; exact hx'⟩, fun hne y m hy => ?_, fun hm => ?_⟩
  · rw [h.sk.csc] at hne hy
    obtain ⟨y0, rf', nt', tc', hy0, rfl, -⟩ := h.scB hy
    exact hC.active hne y0 m hy0
  · rw [h.sk.ct] at hm
    exact hC.notRel (h.relT hkt hxs hm)

theorem DWFr.curRunW (h : DWFr r t σ σ') (hR : CurRunW σ) : CurRunW σ' := by
  rcases hR with hR | e
  · refine Or.inl fun y hy => ?_
    rw [h.sk.ct] at hy
    obtain ⟨x, st, bn, fl, ar, sc, hx, rfl, hs⟩ := h.tcbB hy
    show runnable st = true
    rw [hs.run (hR x hx)]; exact hR x hx
  · exact Or.inr (by rw [h.sk.ct, h.sk.idle]; exact e)

theorem DWFr.sched (h : DWFr r t σ σ') {u : ObjRef} (hs : schedulable u σ = true) : schedulable u σ' = true := by
  obtain ⟨x, scp, y, n, hk, hsc, hrun, hky, hact, hnr⟩ := schedulable_inv hs
  obtain ⟨st, bn, fl, ar, sc, hk', hst⟩ := h.tcbF hk
  obtain ⟨rf, nt, tc, hky', -⟩ := h.scF hky
  exact schedulable_of hk' (h.tsc_some hk hk' hsc) (by show runnable st = true; rw [hst.run hrun]; exact hrun)
    hky' hact (fun hm => hnr (h.relT hk hsc hm))

theorem DWFr.kback (h : DWFr r t σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e | ⟨ko, ko'', h1, h2, hc⟩
  · exact ⟨ko', by rw [← e, ho], id, id, id, id, id, id⟩
  · rw [ho] at h2; cases h2
    rcases hc with ⟨x, st, bn, fl, ar, sc, rfl, rfl, -⟩ | ⟨y, n, rf, nt, tc, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ |
      ⟨x, y, rfl, rfl, -⟩ | ⟨x, rfl, rfl, -⟩ <;> exact ⟨_, h1, by simp⟩

theorem DWFr.ksz (h : DWFr r t σ σ') : KSz σ σ' := fun o ko' ho => by
  obtain ⟨ko, h1, e⟩ := (h.kind o).2 ko' ho
  exact ⟨ko, h1, e.symm⟩

theorem DWFr.ksub (h : DWFr r t σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun rr cs hc hw => ⟨cs, ?_, hw⟩, fun u hu => ?_, fun hn => ?_⟩
  · exact h.othB hc (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e) (fun _ e => by cases e)
  · obtain ⟨x, -, -, -, -, -, hx, -⟩ := h.tcbB hu; exact ⟨x, hx⟩
  · rcases h.kh o with e | ⟨ko, ko', h1, -, -⟩
    · rw [e]; exact hn
    · rw [hn] at h1; cases h1

/-- What `CallRel` reads of the spec (`CFr.callKeep`). -/
theorem DWFr.callKeep (h : DWFr r t σ σ') :
    (∀ q y n, σ.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
    (∀ q x, σ.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
    (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n)) := by
  refine ⟨fun q y n hq => ?_, fun q x hq => ?_, fun p x n hp => ?_⟩
  · obtain ⟨rf, nt, tc, hq', -⟩ := h.scF hq; exact ⟨_, hq', rfl⟩
  · obtain ⟨y, hy, e, -⟩ := h.replyF hq; exact ⟨y, hy, e⟩
  · obtain ⟨y0, -, -, -, hy0, -⟩ := h.scB hp; exact ⟨y0, hy0⟩

end

/-! ### The donation -/

/-- `BlockedScActive` reads only the heap. -/
theorem BlockedScActive.of_kheapD {σ σ' : State Unit} (h : BlockedScActive σ) (hk : σ'.kheap = σ.kheap) :
    BlockedScActive σ' :=
  ⟨fun p z n t y hp hyt hy hq => h.tcb p z n t y (hk ▸ hp) hyt (hk ▸ hy) hq,
    fun p z n hp hr => h.replies p z n (hk ▸ hp) hr⟩

/-- **A donation's outcome is a `DWFr` step**: `t` (without an SC) given the
SC `p` (bound to no thread, `n`'s SC; not current, or `t` owns it after), the heap of `donSt`, the
release queue grown by `t` at most. -/
theorem DWFr.of_donSt {r t n p : ObjRef} {σ σ' : State Unit} {ys : SchedContext} {ns : Nat} {xt : Tcb}
    {xn : Notification} (hks : σ.kheap p = some (.schedContext ys ns)) (hkt : σ.kheap t = some (.tcb xt))
    (hpt : p ≠ t) (h0 : xt.tcbSchedContext = none) (hpc : p ≠ σ.curSc ∨ CurOwnT t σ')
    (hkn : σ.kheap n = some (.notification xn)) (hsc : xn.ntfnSc = some p)
    (hk : σ'.kheap = (donSt σ p t ys ns xt).kheap) (hs : SkD σ σ')
    (hrel : ∀ u ∈ σ'.releaseQueue, u = t ∨ u ∈ σ.releaseQueue) : DWFr r t σ σ' := by
  have kt : σ'.kheap t = some (.tcb { xt with tcbSchedContext := some p }) := by rw [hk]; simp [donSt, updK]
  have kp : σ'.kheap p = some (.schedContext { ys with scTcb := some t } ns) := by
    rw [hk]; simp [donSt, updK, hpt]
  have ko : ∀ q, q ≠ t → q ≠ p → σ'.kheap q = σ.kheap q := fun q h1 h2 => by
    rw [hk]; simp [donSt, updK, h1, h2]
  refine ⟨hs, fun u hu => ?_, fun q => ?_, fun q x y hx hy hne => ?_, fun q y m z m' hy hz hne => ?_⟩
  · rcases hrel u hu with rfl | h'
    · exact Or.inr ⟨rfl, fun x hx => by rw [hkt] at hx; cases hx; exact h0⟩
    · exact Or.inl h'
  · by_cases e1 : q = t
    · subst e1
      exact Or.inr ⟨_, _, hkt, kt, Or.inl ⟨xt, xt.tcbState, xt.tcbBoundNotification, xt.tcbFault, xt.tcbArch,
        some p, rfl, rfl, Or.inl ⟨Or.inl ⟨rfl, rfl⟩, rfl, Or.inl rfl⟩⟩⟩
    by_cases e2 : q = p
    · subst e2
      exact Or.inr ⟨_, _, hks, kp, Or.inr (Or.inl ⟨ys, ns, ys.scRefills, ys.scNtfn, some t, rfl, rfl,
        fun _ => rfl, Or.inl rfl⟩)⟩
    · exact Or.inl (ko q e1 e2)
  · by_cases e1 : q = t
    · subst e1; rw [hkt] at hx; cases hx; exact ⟨rfl, h0⟩
    · have e2 : q ≠ p := by rintro rfl; rw [hks] at hx; cases hx
      rw [ko q e1 e2, hx] at hy; cases hy; exact absurd rfl hne
  · by_cases e2 : q = p
    · subst e2; exact ⟨hpc, n, xn, hkn, hsc⟩
    · have e1 : q ≠ t := by rintro rfl; rw [hkt] at hy; cases hy
      rw [ko q e1 e2, hy] at hz; cases hz; exact absurd rfl hne

/-- A sufficient head refill at some usage is sufficient at none. -/
theorem suff0_of_suff {c : Time} {r : Refill} (h : refillSufficient c r = true) : refillSufficient 0 r = true := by
  apply suff0_of
  unfold refillSufficient refillCapacity at h
  simp only [decide_eq_true_eq] at h
  have hp := min_budget_pos
  split_ifs at h with hlt
  · bv_omega
  · bv_omega

/-- `CurOwnT` from its parts. -/
theorem curOwnT_of {t p : ObjRef} {σ : State Unit} {x : Tcb} {y : SchedContext} {n : Nat}
    (kt : σ.kheap t = some (.tcb x)) (hxs : x.tcbSchedContext = some p)
    (kp : σ.kheap p = some (.schedContext y n)) (hyt : y.scTcb = some t) (hp : p = σ.curSc)
    (hrel : 0 < σ.consumedTime → t ∉ σ.releaseQueue) : CurOwnT t σ := by
  subst hp
  exact ⟨x, kt, hxs, fun x' m hx => by rw [kp] at hx; cases hx; exact hyt, hrel⟩

set_option maxHeartbeats 4000000 in
/-- **`maybe_donate_sc` as a `DWFr` step** (module docstring), from a state
with `Inv` where `t` is in no queue: the action kept; `Inv` after, with the
release-queue fact the sporadic check needs (`Inv.donate`); and the donated
SC's facts. -/
theorem donate_dfr {σ σ' : State Unit} (h : Inv σ) {r t n : ObjRef} {xt : Tcb} {xn : Notification}
    (hkt : σ.kheap t = some (.tcb xt)) (hkn : σ.kheap n = some (.notification xn)) (hnq : NotQueued σ t)
    (hoff : OffOK σ)
    (hB : BlockedScActive σ) (hnipc : ∀ x, σ.kheap t = some (.tcb x) → ipcQueuedThreadState x.tcbState = false)
    (he : maybeDonateSc (Z := Unit) t n σ = ({((), σ')}, False)) :
    DWFr r t σ σ' ∧ σ'.schedulerAction = σ.schedulerAction ∧ σ'.curTime = σ.curTime ∧
      (∀ d q, t ∉ σ.readyQueues d q → t ∉ σ'.readyQueues d q) ∧ BlockedScActive σ' := by
  have hnt : n ≠ t := by rintro rfl; rw [hkt] at hkn; cases hkn
  have refl : DWFr r t σ σ ∧ σ.schedulerAction = σ.schedulerAction ∧ σ.curTime = σ.curTime ∧
      (∀ d q, t ∉ σ.readyQueues d q → t ∉ σ.readyQueues d q) ∧ BlockedScActive σ :=
    ⟨DWFr.refl _ _ _, rfl, rfl, fun _ _ h => h, hB⟩
  unfold maybeDonateSc getTcbObjRef at he
  rw [nd_bind_one (threadGet_eq _ hkt)] at he
  simp only [NonDet.when] at he
  split_ifs at he with h0
  swap
  · rw [pair_eq he]; exact refl
  rw [nd_bind_one' (getNtfnSc_eq hkn)] at he
  cases hsc : xn.ntfnSc with
  | none => rw [hsc] at he; rw [pair_eq he]; exact refl
  | some p =>
    rw [hsc] at he
    obtain ⟨ys, ns, hks⟩ := h.ntfnSc n xn p hkn hsc
    have hpt : p ≠ t := by rintro rfl; rw [hkt] at hks; cases hks
    simp only [NonDet.maybeM] at he
    have hg : getScObjRef (Z := Unit) SchedContext.scTcb p σ = ({(ys.scTcb, σ)}, False) := by
      unfold getScObjRef; rw [nd_bind_one (getSchedContext_eq hks)]; rfl
    rw [nd_bind_one hg] at he
    cases hst : ys.scTcb with
    | some u => rw [hst] at he; simp only [NonDet.when, reduceCtorEq, ↓reduceIte] at he; rw [pair_eq he]; exact refl
    | none =>
      rw [hst] at he
      simp only [NonDet.when, ↓reduceIte] at he
      rw [nd_bind_one (schedContextDonate_eq hks hst hkt hpt)] at he
      have hb := h.donated hks hst hkt hpt hnq
      have hBd : BlockedScActive (donSt σ p t ys ns xt) :=
        bsa_donate hB (fun _ _ _ => Or.inr hnipc) (by rw [schedContextDonate_eq hks hst hkt hpt]; exact Set.mem_singleton _)
      set σd := donSt σ p t ys ns xt with hσd
      set xt' : Tcb := { xt with tcbSchedContext := some p }
      set ys' : SchedContext := { ys with scTcb := some t }
      have kt : σd.kheap t = some (.tcb xt') := by simp [σd, donSt, updK] <;> rfl
      have kp : σd.kheap p = some (.schedContext ys' ns) := by simp [σd, donSt, updK, hpt] <;> rfl
      have hne : scActive ys' = true → ys'.scRefills ≠ [] := h.ne p ys ns hks
      rw [resume_spec_eq kp rfl kt hne
        (fun hs => by
          obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5, -⟩ := schedulable_inv hs
          rw [kt] at h1; cases h1; cases h2; rw [kp] at h4; cases h4; exact ⟨h3, h5⟩)
        (fun _ => hnq.1 _ _)] at he
      split_ifs at he with hc
      · have hact : scActive ys' = true := by
          obtain ⟨x, scp, y, m, h1, h2, -, h4, h5, -⟩ := schedulable_inv hc.1
          rw [kt] at h1; cases h1; cases h2; rw [kp] at h4; cases h4; exact h5
        obtain ⟨b, hp⟩ := postpone_eq kp rfl kt (specRt σd) (fun u hu => by
          rcases hu with rfl | hu
          · exact ⟨xt', p, ys', ns, kt, rfl, kp, hne hact, specRt_eq kt rfl kp (hne hact)⟩
          · obtain ⟨xu, scp, yu, nu, h1, h2, -, h4, h5⟩ := hb.rel u hu
            exact ⟨xu, scp, yu, nu, h1, h2, h4, hb.ne _ _ _ h4 h5, specRt_eq h1 h2 h4 (hb.ne _ _ _ h4 h5)⟩)
        rw [hp] at he
        rw [pair_eq he]
        have hcz : p = σ.curSc → ¬ 0 < σ.consumedTime := fun hpcur h0' => by
          obtain ⟨hsuf, -, hrdy⟩ := hoff h0' ys ns (by rw [← hpcur]; exact hks) (fun _ => hact)
          exact hc.2 ⟨hrdy, suff0_of_suff hsuf⟩
        refine ⟨DWFr.of_donSt hks hkt hpt h0 ?_ hkn hsc rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          (fun u hu => mem_specInsT.1 hu), rfl, rfl, fun d q hq hm => ?_, hBd.of_kheapD rfl⟩
        · by_cases hpcur : p = σ.curSc
          · exact Or.inr (curOwnT_of (by exact kt) rfl (by exact kp) rfl (by exact hpcur)
              (fun h0' => absurd (by exact h0') (hcz hpcur)))
          · exact Or.inl hpcur
        simp only [setRel, setQ] at hm
        split at hm
        · unfold tcbSchedDequeue at hm
          simp at hm
        · exact hq hm
      · rw [pair_eq he]
        have hpc' : p ≠ σ.curSc ∨ CurOwnT t σd := by
          by_cases hpcur : p = σ.curSc
          · exact Or.inr (curOwnT_of kt rfl kp rfl hpcur (fun _ => hnq.2))
          · exact Or.inl hpcur
        exact ⟨DWFr.of_donSt hks hkt hpt h0 hpc' hkn hsc rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          (fun u hu => Or.inr hu), rfl, rfl, fun d q hq => hq, hBd⟩

end Spec

end

end Fl4Proofs.P3.Sched
