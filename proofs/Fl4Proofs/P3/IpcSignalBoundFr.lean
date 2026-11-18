/-
P3 (DESIGN.md §9), IPC: **the spec's frame of `send_signal`'s wake-up of
the idle notification `r`'s bound thread `t` blocked receiving** (spec side
only), toward `SignalRestJHyp` (ScSignalJ).

The wake-up runs `cancel_ipc t` (the fault cleared, `t` dequeued from its
endpoint, its reply's `reply_tcb` cleared, `t` `Inactive`), then the same
wake as a waiting notification's (`specWake`): `t` `running` with its badge
register, the switch, the sporadic check. `NFr` cannot hold it (its TCB
change is from blocked on `r` only, endpoints and replies are fixed), so:

* `TCX`: a TCB's change: `NFr false r`'s (`TChg`, the fault kept), or `t`'s,
  receive-blocked or inactive, to `Inactive`, `running` or its state, its
  fault and context changed, its binding kept or cut.
* `CChg`: `TCX` on TCBs, `NChg false` on the other kinds but endpoints and
  replies; an endpoint holding `t` to a sub-queue; a reply naming `t` to one
  naming nothing.
* `CFr`: the frame (`Sk` and `CChg` objectwise); `CFr.ofNFr`, `CFr.trans`,
  `CFr.upd`, `CFr.sts`.
* What it keeps: the per-kind lemmas (`tcbF`, `scB`, `epB`, `replyF`, ...),
  and `NFr`'s scheduler facts (`szKeep`, `ykeep`, `mcpKeep`, `bufKeep`,
  `nsc`, `isorted`, `own`, `off`, `idleOK`, `bsa`, `curInv`, `curRunW`,
  `sched`, `kback`, `ksz`, `ksub`): a thread changed by `TCX`'s second case is
  not runnable (so not the current thread when `CurInv`, not a switch target,
  not the idle thread) and ends in no IPC queue.
-/
import Fl4Proofs.P3.IpcSignalWakeSpec
import Fl4Proofs.P3.XTopJointFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- Receive-blocked or inactive. -/
def RbIn (ts : ThreadState) : Prop := (∃ e ro d, ts = .blockedOnReceive e ro d) ∨ ts = .inactive

/-- **A TCB's change** (module docstring). -/
def TCX (r t p : ObjRef) (x : Tcb) (st : ThreadState) (bn : Option ObjRef) (fl : Option Fault) (ar : ArchTcb) :
    Prop :=
  (TChg false r x st ar ∧ fl = x.tcbFault ∧ (bn = x.tcbBoundNotification ∨ bn = none)) ∨
  ((bn = x.tcbBoundNotification ∨ bn = none) ∧ p = t ∧ RbIn x.tcbState ∧
    (st = .inactive ∨ st = .running ∨ st = x.tcbState))

theorem RbIn.not_run {ts : ThreadState} (h : RbIn ts) : runnable ts = false := by
  rcases h with ⟨e, ro, d, rfl⟩ | rfl <;> rfl

theorem RbIn.ne_ntfn {ts : ThreadState} (h : RbIn ts) (r : ObjRef) : ts ≠ .blockedOnNotification r := by
  rcases h with ⟨e, ro, d, rfl⟩ | rfl <;> nofun

theorem TCX.trans {r t p : ObjRef} {x : Tcb} {st1 st2 : ThreadState} {bn1 bn2 : Option ObjRef}
    {fl1 fl2 : Option Fault} {ar1 ar2 : ArchTcb} (h1 : TCX r t p x st1 bn1 fl1 ar1)
    (h2 : TCX r t p { x with tcbState := st1, tcbBoundNotification := bn1, tcbFault := fl1, tcbArch := ar1 } st2 bn2 fl2 ar2) :
    TCX r t p x st2 bn2 fl2 ar2 := by
  rcases h1 with ⟨t1, f1, b1⟩ | ⟨b1, xb, hx, s1⟩ <;> rcases h2 with ⟨t2, f2, b2⟩ | ⟨b2, xb2, hx2, s2⟩
  · refine Or.inl ⟨?_, f2.trans f1, or_none_trans b1 b2⟩
    rcases t2 with ⟨e1, e2⟩ | ⟨hq2, e1, e7⟩ <;> rcases t1 with ⟨e3, e4⟩ | ⟨hq1, e5, e6⟩
    · exact Or.inl ⟨e1.trans e3, e2.trans e4⟩
    · exact Or.inr ⟨hq1, e5, by rw [e1]; exact e6⟩
    · simp only at e1
      exact Or.inr ⟨hq2, by rw [← e3]; exact e1, e7⟩
    · simp only at e1; rcases e6 with e | e <;> rw [e] at e1 <;> cases e1
  · -- `NFr`'s change, then the second case
    simp only at hx2 s2
    rcases t1 with ⟨e3, -⟩ | ⟨-, -, e6⟩
    · exact Or.inr ⟨or_none_trans b1 b2, xb2, e3 ▸ hx2, by rw [← e3]; exact s2⟩
    · rcases e6 with e | e <;> rw [e] at hx2 <;> rcases hx2 with ⟨_, _, _, h⟩ | h <;> cases h
  · -- the second case, then `NFr`'s change
    have e2 : st2 = st1 := by
      rcases t2 with ⟨e, -⟩ | ⟨-, e, -⟩
      · exact e
      · simp only at e
        rcases s1 with h | h | h <;> rw [h] at e
        · cases e
        · cases e
        · exact absurd e (hx.ne_ntfn r)
    refine Or.inr ⟨?_, xb, hx, by rw [e2]; exact s1⟩
    simp only at b2
    rcases b2 with e | e
    · rw [e]; exact b1
    · exact Or.inr e
  · simp only at b2 s2
    refine Or.inr ⟨?_, xb, hx, ?_⟩
    · rcases b2 with e | e
      · rw [e]; exact b1
      · exact Or.inr e
    · rcases s2 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · rw [h]; exact s1

/-- `TCX` keeps a runnable thread's state. -/
theorem TCX.run {r t p : ObjRef} {x : Tcb} {st : ThreadState} {bn : Option ObjRef} {fl : Option Fault} {ar : ArchTcb}
    (h : TCX r t p x st bn fl ar) (hr : runnable x.tcbState = true) : st = x.tcbState := by
  rcases h with ⟨t, -, -⟩ | ⟨-, -, hx, -⟩
  · exact t.st (fun e => by rw [e] at hr; simp [runnable] at hr)
  · rw [hx.not_run] at hr; cases hr

/-- `TCX`: an IPC-queued state after was one before. -/
theorem TCX.ipcQ {r t p : ObjRef} {x : Tcb} {st : ThreadState} {bn : Option ObjRef} {fl : Option Fault} {ar : ArchTcb}
    (h : TCX r t p x st bn fl ar) (hq : ipcQueuedThreadState st = true) : ipcQueuedThreadState x.tcbState = true := by
  rcases h with ⟨t, -, -⟩ | ⟨-, -, -, h | h | h⟩
  · exact t.ipcQ hq
  · rw [h] at hq; simp [ipcQueuedThreadState] at hq
  · rw [h] at hq; simp [ipcQueuedThreadState] at hq
  · rw [← h]; exact hq

/-- `TCX` keeps `NotIpcBlk`. -/
theorem TCX.notIpc {r t p : ObjRef} {x : Tcb} {st : ThreadState} {bn : Option ObjRef} {fl : Option Fault} {ar : ArchTcb}
    (h : TCX r t p x st bn fl ar) (hn : NotIpcBlk x.tcbState) : NotIpcBlk st := by
  rcases h with ⟨t, -, -⟩ | ⟨-, -, hx, h | h | h⟩
  · rw [t.st (hn.1 r)]; exact hn
  · rw [h]; unfold NotIpcBlk; exact ⟨fun _ e => (by cases e), fun _ _ e => (by cases e), fun _ _ _ e => (by cases e)⟩
  · rw [h]; unfold NotIpcBlk; exact ⟨fun _ e => (by cases e), fun _ _ e => (by cases e), fun _ _ _ e => (by cases e)⟩
  · rw [h]; exact hn

/-- `TCX` keeps a non-`RbIn`, non-blocked-on-`r` state. -/
theorem TCX.st {r t p : ObjRef} {x : Tcb} {st : ThreadState} {bn : Option ObjRef} {fl : Option Fault} {ar : ArchTcb}
    (h : TCX r t p x st bn fl ar) (hn : x.tcbState ≠ .blockedOnNotification r) (hb : ¬ RbIn x.tcbState) :
    st = x.tcbState := by
  rcases h with ⟨t, -, -⟩ | ⟨-, -, hx, -⟩
  · exact t.st hn
  · exact absurd hx hb

/-- **One object's change** (module docstring). -/
def CChg (r t cur p : ObjRef) (o o' : KernelObject) : Prop :=
  (∃ x st bn fl ar, o = .tcb x ∧
    o' = .tcb { x with tcbState := st, tcbBoundNotification := bn, tcbFault := fl, tcbArch := ar } ∧
    TCX r t p x st bn fl ar) ∨
  (NChg false r cur p o o' ∧ ∀ x, o ≠ .tcb x) ∨
  (∃ x y, o = .endpoint x ∧ o' = .endpoint y ∧ y.epQueue.Sublist x.epQueue ∧ t ∈ x.epQueue) ∨
  (∃ x, o = .reply x ∧ o' = .reply { x with replyTcb := none } ∧ x.replyTcb = some t)

theorem CChg.trans {r t cur p : ObjRef} {o1 o2 o3 : KernelObject} (h1 : CChg r t cur p o1 o2)
    (h2 : CChg r t cur p o2 o3) : CChg r t cur p o1 o3 := by
  rcases h1 with ⟨x, st, bn, fl, ar, rfl, rfl, hc⟩ | ⟨hn1, hnt1⟩ | ⟨x, y, rfl, rfl, hs, hm⟩ | ⟨x, rfl, rfl, hx⟩
  · rcases h2 with ⟨x2, st2, bn2, fl2, ar2, e, rfl, hc2⟩ | ⟨-, hnt⟩ | ⟨_, _, e, -⟩ | ⟨_, e, -⟩
    · cases e
      exact Or.inl ⟨x, st2, bn2, fl2, ar2, rfl, rfl, hc.trans hc2⟩
    · exact absurd rfl (hnt _)
    · cases e
    · cases e
  · rcases h2 with ⟨x2, -, -, -, -, rfl, -⟩ | ⟨hn2, -⟩ | ⟨_, _, rfl, -⟩ | ⟨_, rfl, -⟩
    · rcases hn1 with ⟨_, _, _, _, e1, -, -⟩ | ⟨_, _, _, _, -, e, -⟩ | ⟨_, _, -, e, -⟩
      · exact absurd e1 (hnt1 _)
      · cases e
      · cases e
    · exact Or.inr (Or.inl ⟨hn1.trans hn2, hnt1⟩)
    · rcases hn1 with ⟨_, _, _, _, -, e, -⟩ | ⟨_, _, _, _, -, e, -⟩ | ⟨_, _, -, e, -⟩ <;> cases e
    · rcases hn1 with ⟨_, _, _, _, -, e, -⟩ | ⟨_, _, _, _, -, e, -⟩ | ⟨_, _, -, e, -⟩ <;> cases e
  · rcases h2 with ⟨_, _, _, _, _, e, -⟩ | ⟨hn2, -⟩ | ⟨x2, z, e, rfl, hs2, -⟩ | ⟨_, e, -⟩
    · cases e
    · rcases hn2 with ⟨_, _, _, _, e, -⟩ | ⟨_, _, _, _, e, -⟩ | ⟨_, _, e, -⟩ <;> cases e
    · cases e
      exact Or.inr (Or.inr (Or.inl ⟨x, z, rfl, rfl, hs2.trans hs, hm⟩))
    · cases e
  · rcases h2 with ⟨_, _, _, _, _, e, -⟩ | ⟨hn2, -⟩ | ⟨_, _, e, -⟩ | ⟨x2, e, rfl, hx2⟩
    · cases e
    · rcases hn2 with ⟨_, _, _, _, e, -⟩ | ⟨_, _, _, _, e, -⟩ | ⟨_, _, e, -⟩ <;> cases e
    · cases e
    · cases e; simp at hx2

/-- **The spec's frame of the bound-receiver wake-up** (module docstring). -/
structure CFr (r t : ObjRef) (σ σ' : State Unit) : Prop where
  sk : Sk σ σ'
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ o o', σ.kheap p = some o ∧ σ'.kheap p = some o' ∧ CChg r t σ.curSc p o o'

theorem CFr.refl (r t : ObjRef) (σ : State Unit) : CFr r t σ σ := ⟨Sk.refl σ, fun _ => Or.inl rfl⟩

theorem CFr.trans {r t : ObjRef} {σ1 σ2 σ3 : State Unit} (h1 : CFr r t σ1 σ2) (h2 : CFr r t σ2 σ3) :
    CFr r t σ1 σ3 := by
  refine ⟨h1.sk.trans h2.sk, fun p => ?_⟩
  have hc2 : σ2.curSc = σ1.curSc := h1.sk.csc
  rcases h2.kh p with e2 | ⟨o2, o3, k2, k3, c2⟩
  · rw [e2]; exact h1.kh p
  · rw [hc2] at c2
    rcases h1.kh p with e1 | ⟨o1, o2', k1, k2', c1⟩
    · exact Or.inr ⟨o2, o3, by rw [← e1]; exact k2, k3, c2⟩
    · obtain rfl := Option.some.inj (k2'.symm.trans k2)
      exact Or.inr ⟨o1, o3, k1, k3, c1.trans c2⟩

/-- `NFr false r` is a `CFr r t`. -/
theorem CFr.ofNFr {r t : ObjRef} {σ σ' : State Unit} (h : NFr false r σ σ') : CFr r t σ σ' := by
  refine ⟨h.sk, fun p => (h.kh p).imp_right fun ⟨o, o', h1, h2, hc⟩ => ⟨o, o', h1, h2, ?_⟩⟩
  rcases hc with ⟨x, st, bn, ar, rfl, rfl, hs, hb⟩ | hc | hc
  · exact Or.inl ⟨x, st, bn, x.tcbFault, ar, rfl, rfl, Or.inl ⟨hs, rfl, hb⟩⟩
  · exact Or.inr (Or.inl ⟨Or.inr (Or.inl hc), fun x e => by obtain ⟨_, _, _, _, e', -⟩ := hc; rw [e] at e'; cases e'⟩)
  · exact Or.inr (Or.inl ⟨Or.inr (Or.inr hc), fun x e => by obtain ⟨_, _, e', -⟩ := hc; rw [e] at e'; cases e'⟩)

theorem CFr.upd {r t : ObjRef} {σ : State Unit} {p : ObjRef} {o o' : KernelObject}
    (hk : σ.kheap p = some o) (hc : CChg r t σ.curSc p o o') : CFr r t σ (updK σ p o') := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun p' => ?_⟩
  by_cases e : p' = p
  · subst e; exact Or.inr ⟨o, o', hk, by simp [updK], hc⟩
  · exact Or.inl (by simp [updK, e])

theorem CFr.sts (r t : ObjRef) (σ : State Unit) (u : ObjRef) : CFr r t σ (Notif.stsAct σ u) :=
  CFr.ofNFr (NFr.sts r σ u)

/-! ### Per kind -/

section
variable {r t : ObjRef} {σ σ' : State Unit}

theorem CFr.tcbF (h : CFr r t σ σ') {p : ObjRef} {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    ∃ st bn fl ar, σ'.kheap p =
      some (.tcb { x with tcbState := st, tcbBoundNotification := bn, tcbFault := fl, tcbArch := ar }) ∧
      TCX r t p x st bn fl ar := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x.tcbState, x.tcbBoundNotification, x.tcbFault, x.tcbArch, by rw [e, hp],
      Or.inl ⟨Or.inl ⟨rfl, rfl⟩, rfl, Or.inl rfl⟩⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨x', st, bn, fl, ar, e1, rfl, hs⟩ | ⟨-, hnt⟩ | ⟨_, _, e1, -⟩ | ⟨_, e1, -⟩
    · cases e1; exact ⟨st, bn, fl, ar, h2, hs⟩
    · exact absurd rfl (hnt x)
    · cases e1
    · cases e1

theorem CFr.tcbB (h : CFr r t σ σ') {p : ObjRef} {y : Tcb} (hp : σ'.kheap p = some (.tcb y)) :
    ∃ x st bn fl ar, σ.kheap p = some (.tcb x) ∧
      y = { x with tcbState := st, tcbBoundNotification := bn, tcbFault := fl, tcbArch := ar } ∧
      TCX r t p x st bn fl ar := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, y.tcbState, y.tcbBoundNotification, y.tcbFault, y.tcbArch, by rw [← e, hp], rfl,
      Or.inl ⟨Or.inl ⟨rfl, rfl⟩, rfl, Or.inl rfl⟩⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨x, st, bn, fl, ar, rfl, e2, hs⟩ | ⟨hn, hnt⟩ | ⟨_, _, -, e2, -⟩ | ⟨_, -, e2, -⟩
    · cases e2; exact ⟨x, st, bn, fl, ar, h1, rfl, hs⟩
    · rcases hn with ⟨x, _, _, _, e1, -⟩ | ⟨_, _, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩
      · exact absurd e1 (hnt x)
      · cases e2
      · cases e2
    · cases e2
    · cases e2

theorem CFr.scF (h : CFr r t σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ.kheap p = some (.schedContext y n)) :
    ∃ rf nt, σ'.kheap p = some (.schedContext { y with scRefills := rf, scNtfn := nt } n) ∧
      (p = σ.curSc → rf = y.scRefills) ∧ (nt = y.scNtfn ∨ nt = none) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y.scRefills, y.scNtfn, by rw [e, hp], fun _ => rfl, Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, _, _, e1, -⟩ | ⟨hn, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, e1, -⟩
    · cases e1
    · rcases hn with ⟨_, _, _, _, e1, -⟩ | ⟨y', n', rf, nt, e1, rfl, hr, hnt⟩ | ⟨_, _, e1, -⟩ <;> cases e1
      exact ⟨rf, nt, h2, fun e => hr (Or.inl e), hnt⟩
    · cases e1
    · cases e1

theorem CFr.scB (h : CFr r t σ σ') {p : ObjRef} {z : SchedContext} {n : Nat}
    (hp : σ'.kheap p = some (.schedContext z n)) :
    ∃ y rf nt, σ.kheap p = some (.schedContext y n) ∧ z = { y with scRefills := rf, scNtfn := nt } ∧
      (p = σ.curSc → rf = y.scRefills) ∧ (nt = y.scNtfn ∨ nt = none) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨z, z.scRefills, z.scNtfn, by rw [← e, hp], rfl, fun _ => rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, _, _, -, e2, -⟩ | ⟨hn, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨_, -, e2, -⟩
    · cases e2
    · rcases hn with ⟨_, _, _, _, -, e2, -⟩ | ⟨y, n', rf, nt, rfl, e2, hr, hnt⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
      exact ⟨y, rf, nt, h1, rfl, fun e => hr (Or.inl e), hnt⟩
    · cases e2
    · cases e2

theorem CFr.ntfnB (h : CFr r t σ σ') {p : ObjRef} {y : Notification} (hp : σ'.kheap p = some (.notification y)) :
    ∃ x, σ.kheap p = some (.notification x) ∧ (p ≠ r → y = x) ∧
      y.ntfnObj.ntfnQueue.Sublist x.ntfnObj.ntfnQueue ∧
      (y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none) ∧ ((∀ l, x.ntfnObj ≠ .waitingNtfn l) → NObj x.ntfnObj y.ntfnObj) ∧
      (y.ntfnBoundTcb = x.ntfnBoundTcb ∨ y.ntfnBoundTcb = none) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e, hp], fun _ => rfl, List.Sublist.refl _, Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, _, _, -, e2, -⟩ | ⟨hn, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨_, -, e2, -⟩
    · cases e2
    · rcases hn with ⟨_, _, _, _, -, e2, -⟩ | ⟨_, _, _, _, -, e2, -⟩ | ⟨x, y', rfl, e2, hpr, hq, -, hs, hw, hb⟩ <;>
        cases e2
      exact ⟨x, h1, fun hne => absurd hpr hne, hq, hs, hw, hb⟩
    · cases e2
    · cases e2

theorem CFr.ntfnF (h : CFr r t σ σ') {p : ObjRef} {x : Notification} (hp : σ.kheap p = some (.notification x)) :
    ∃ y, σ'.kheap p = some (.notification y) ∧ (p ≠ r → y = x) ∧
      ((∀ l, x.ntfnObj ≠ .waitingNtfn l) → NObj x.ntfnObj y.ntfnObj) ∧
      (y.ntfnBoundTcb = x.ntfnBoundTcb ∨ y.ntfnBoundTcb = none) ∧ (y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [e, hp], fun _ => rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, _, _, e1, -⟩ | ⟨hn, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, e1, -⟩
    · cases e1
    · rcases hn with ⟨_, _, _, _, e1, -⟩ | ⟨_, _, _, _, e1, -⟩ | ⟨x', y, e1, rfl, hpr, -, -, hs, hw, hb⟩ <;> cases e1
      exact ⟨y, h2, fun hne => absurd hpr hne, hw, hb, hs⟩
    · cases e1
    · cases e1

theorem CFr.epF (h : CFr r t σ σ') {p : ObjRef} {x : Endpoint} (hp : σ.kheap p = some (.endpoint x)) :
    ∃ y, σ'.kheap p = some (.endpoint y) ∧ (y = x ∨ (y.epQueue.Sublist x.epQueue ∧ t ∈ x.epQueue)) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [e, hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, _, _, e1, -⟩ | ⟨hn, -⟩ | ⟨x', y, e1, rfl, hs, hm⟩ | ⟨_, e1, -⟩
    · cases e1
    · rcases hn with ⟨_, _, _, _, e1, -⟩ | ⟨_, _, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    · cases e1; exact ⟨y, h2, Or.inr ⟨hs, hm⟩⟩
    · cases e1

theorem CFr.epB (h : CFr r t σ σ') {p : ObjRef} {y : Endpoint} (hp : σ'.kheap p = some (.endpoint y)) :
    ∃ x, σ.kheap p = some (.endpoint x) ∧ (y = x ∨ (y.epQueue.Sublist x.epQueue ∧ t ∈ x.epQueue)) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e, hp], Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, _, _, -, e2, -⟩ | ⟨hn, -⟩ | ⟨x, y', rfl, e2, hs, hm⟩ | ⟨_, -, e2, -⟩
    · cases e2
    · rcases hn with ⟨_, _, _, _, -, e2, -⟩ | ⟨_, _, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    · cases e2; exact ⟨x, h1, Or.inr ⟨hs, hm⟩⟩
    · cases e2

theorem CFr.replyF (h : CFr r t σ σ') {p : ObjRef} {x : Reply} (hp : σ.kheap p = some (.reply x)) :
    ∃ y, σ'.kheap p = some (.reply y) ∧ y.replySc = x.replySc ∧
      (y.replyTcb = x.replyTcb ∨ (x.replyTcb = some t ∧ y.replyTcb = none)) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [e, hp], rfl, Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, _, _, e1, -⟩ | ⟨hn, -⟩ | ⟨_, _, e1, -⟩ | ⟨x', e1, rfl, hx⟩
    · cases e1
    · rcases hn with ⟨_, _, _, _, e1, -⟩ | ⟨_, _, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    · cases e1
    · cases e1; exact ⟨_, h2, rfl, Or.inr ⟨hx, rfl⟩⟩

theorem CFr.replyB (h : CFr r t σ σ') {p : ObjRef} {y : Reply} (hp : σ'.kheap p = some (.reply y)) :
    ∃ x, σ.kheap p = some (.reply x) ∧ y.replySc = x.replySc ∧
      (y.replyTcb = x.replyTcb ∨ (x.replyTcb = some t ∧ y.replyTcb = none)) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e, hp], rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, _, _, -, e2, -⟩ | ⟨hn, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨x, rfl, e2, hx⟩
    · cases e2
    · rcases hn with ⟨_, _, _, _, -, e2, -⟩ | ⟨_, _, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    · cases e2
    · cases e2; exact ⟨x, h1, rfl, Or.inr ⟨hx, rfl⟩⟩

/-- The other kinds kept. -/
theorem CFr.othF (h : CFr r t σ σ') {p : ObjRef} {o : KernelObject} (hp : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h2 : ∀ y n, o ≠ .schedContext y n) (h3 : ∀ x, o ≠ .notification x)
    (h4 : ∀ x, o ≠ .endpoint x) (h5 : ∀ x, o ≠ .reply x) : σ'.kheap p = some o := by
  rcases h.kh p with e | ⟨o0, o', k1, k2, hc⟩
  · rw [e, hp]
  · rw [hp] at k1; cases k1
    rcases hc with ⟨_, _, _, _, _, e1, -⟩ | ⟨hn, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, e1, -⟩
    · exact absurd e1 (h1 _)
    · rcases hn with ⟨_, _, _, _, e1, -⟩ | ⟨_, _, _, _, e1, -⟩ | ⟨_, _, e1, -⟩
      · exact absurd e1 (h1 _)
      · exact absurd e1 (h2 _ _)
      · exact absurd e1 (h3 _)
    · exact absurd e1 (h4 _)
    · exact absurd e1 (h5 _)

theorem CFr.othB (h : CFr r t σ σ') {p : ObjRef} {o' : KernelObject} (hp : σ'.kheap p = some o')
    (h1 : ∀ x, o' ≠ .tcb x) (h2 : ∀ y n, o' ≠ .schedContext y n) (h3 : ∀ x, o' ≠ .notification x)
    (h4 : ∀ x, o' ≠ .endpoint x) (h5 : ∀ x, o' ≠ .reply x) : σ.kheap p = some o' := by
  rcases h.kh p with e | ⟨o, o'', k1, k2, hc⟩
  · rw [← e, hp]
  · rw [hp] at k2; cases k2
    rcases hc with ⟨_, _, _, _, _, -, e2, -⟩ | ⟨hn, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨_, -, e2, -⟩
    · exact absurd e2 (h1 _)
    · rcases hn with ⟨_, _, _, _, -, e2, -⟩ | ⟨_, _, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩
      · exact absurd e2 (h1 _)
      · exact absurd e2 (h2 _ _)
      · exact absurd e2 (h3 _)
    · exact absurd e2 (h4 _)
    · exact absurd e2 (h5 _)

/-- The objects' kinds and sizes kept, both ways. -/
theorem CFr.kind (h : CFr r t σ σ') (p : ObjRef) :
    (∀ o, σ.kheap p = some o → ∃ o', σ'.kheap p = some o' ∧ aType o' = aType o) ∧
    (∀ o', σ'.kheap p = some o' → ∃ o, σ.kheap p = some o ∧ aType o' = aType o) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨fun o ho => ⟨o, by rw [e, ho], rfl⟩, fun o' ho => ⟨o', by rw [← e, ho], rfl⟩⟩
  · have ha : aType o' = aType o := by
      rcases hc with ⟨x, st, bn, fl, ar, rfl, rfl, -⟩ | ⟨hn, -⟩ | ⟨x, y, rfl, rfl, -⟩ | ⟨x, rfl, rfl, -⟩
      · rfl
      · rcases hn with ⟨x, st, bn, ar, rfl, rfl, -⟩ | ⟨y, n, rf, nt, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ <;> rfl
      · rfl
      · rfl
    exact ⟨fun o0 ho0 => ⟨o', h2, by rw [h1] at ho0; cases ho0; exact ha⟩,
      fun o0 ho0 => ⟨o, h1, by rw [h2] at ho0; cases ho0; exact ha⟩⟩

/-! ### What the frame keeps -/

theorem CFr.szKeep (h : CFr r t σ σ') : SzKeep σ σ' := fun p y n hp => by
  obtain ⟨y0, -, -, hy0, -⟩ := h.scB hp; exact ⟨y0, hy0⟩

theorem CFr.ykeep (h : CFr r t σ σ') : YKeep σ σ' := by
  refine ⟨fun p x hp => ?_, fun p y n hp => ?_, fun p z n hp => ?_⟩
  · obtain ⟨st, bn, fl, ar, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩
  · obtain ⟨rf, nt, hp', -⟩ := h.scF hp; exact ⟨_, hp', rfl⟩
  · obtain ⟨y0, rf, nt, hy0, rfl, -⟩ := h.scB hp; exact ⟨y0, hy0, rfl⟩

theorem CFr.mcpKeep (h : CFr r t σ σ') : McpKeep σ σ' := fun p x hp => by
  obtain ⟨st, bn, fl, ar, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem CFr.bufKeep (h : CFr r t σ σ') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => by obtain ⟨st, bn, fl, ar, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem CFr.prio (h : CFr r t σ σ') (u : ObjRef) : prioOf σ' u = prioOf σ u := by
  unfold prioOf
  rw [tcbsOf_eq, tcbsOf_eq]
  cases hk : σ.kheap u with
  | some o =>
    cases o with
    | tcb x =>
      obtain ⟨st, bn, fl, ar, hk', -⟩ := h.tcbF hk
      rw [hk']; rfl
    | _ =>
      cases hk' : σ'.kheap u with
      | none => rfl
      | some o' => cases o' with
        | tcb y => obtain ⟨x, -, -, -, -, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
        | _ => rfl
  | none =>
    cases hk' : σ'.kheap u with
    | none => rfl
    | some o' => cases o' with
      | tcb y => obtain ⟨x, -, -, -, -, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
      | _ => rfl

theorem CFr.nsc {N C : Set U64} (h : CFr r t σ σ') (hN : NSC N C σ) : NSC N C σ' := by
  intro n hn y p hy hp
  obtain ⟨x, hx, -, -, hs, -, -⟩ := h.ntfnB hy
  rcases hs with e | e
  · exact hN n hn x p hx (e ▸ hp)
  · rw [e] at hp; cases hp

theorem CFr.isorted (h : CFr r t σ σ') (hS : IpcSorted σ) : IpcSorted σ' := by
  refine ⟨fun p y hp => ?_, fun p y hp => ?_⟩
  · obtain ⟨x, hx, hc⟩ := h.epB hp
    rcases hc with rfl | ⟨hsub, -⟩
    · exact (hS.1 p y hx).congr fun u _ => h.prio u
    · exact ((hS.1 p x hx).sublist hsub).congr fun u _ => h.prio u
  · obtain ⟨x, hx, -, hsub, -⟩ := h.ntfnB hp
    exact ((hS.2 p x hx).sublist hsub).congr fun u _ => h.prio u

theorem CFr.own {T C : Set U64} (h : CFr r t σ σ') (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · obtain ⟨st, bn, fl, ar, hkt', -⟩ := h.tcbF hkt
    refine Or.inl ⟨u, hu, _, hkt', by rw [h.sk.csc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
    · rw [h.sk.csc] at hy
      obtain ⟨y0, rf, nt, hy0, rfl, -⟩ := h.scB hy
      exact hown y0 n hy0
    · rw [h.sk.cons] at h0; rw [h.sk.rel] at hm; exact hnr h0 hm
  · refine Or.inr ⟨by rw [h.sk.csc]; exact hcs, fun y n hy => ?_⟩
    rw [h.sk.csc] at hy
    obtain ⟨y0, rf, nt, hy0, rfl, -⟩ := h.scB hy
    exact hun y0 n hy0

theorem CFr.off (h : CFr r t σ σ') (hO : OffOK σ) : OffOK σ' := by
  intro hc y n hy ha
  rw [h.sk.cons] at hc ⊢; rw [h.sk.tm]
  rw [h.sk.csc] at hy ha
  obtain ⟨y0, rf, nt, hy0, rfl, hr, -⟩ := h.scB hy
  have e : rf = y0.scRefills := hr rfl
  subst e
  exact hO hc y0 n hy0 ha

theorem CFr.idleOK (h : CFr r t σ σ') (hO : IdleOK σ) : IdleOK σ' := by
  obtain ⟨x, hx, h1, h2, h3⟩ := hO
  obtain ⟨st, bn, fl, ar, hx', hs⟩ := h.tcbF hx
  refine ⟨{ x with tcbState := st, tcbBoundNotification := bn, tcbFault := fl, tcbArch := ar },
    by rw [h.sk.idle]; exact hx', h1, ?_, by rw [h.sk.idle, h.sk.rel]; exact h3⟩
  show st = _
  rw [hs.st (by rw [h2]; nofun) (by rw [h2]; rintro (⟨_, _, _, e⟩ | e) <;> cases e)]; exact h2

theorem CFr.bsa (h : CFr r t σ σ') (hB : BlockedScActive σ) : BlockedScActive σ' := by
  refine ⟨fun p z n u y hp hyt hy hq => ?_, fun p z n hp hr => ?_⟩
  · obtain ⟨y0, rf, nt, hy0, rfl, -⟩ := h.scB hp
    obtain ⟨x, st, bn, fl, ar, hx, rfl, hs⟩ := h.tcbB hy
    exact hB.tcb p y0 n u x hy0 hyt hx (hs.ipcQ hq)
  · obtain ⟨y0, rf, nt, hy0, rfl, -⟩ := h.scB hp
    exact hB.replies p y0 n hy0 hr

theorem CFr.curInv (h : CFr r t σ σ') (hC : CurInv σ) : CurInv σ' := by
  obtain ⟨xt, hkt, hxs, hnb⟩ := hC.tcb
  obtain ⟨x, n, hx⟩ := hC.sc
  obtain ⟨st, bn, fl, ar, hkt', hs⟩ := h.tcbF hkt
  obtain ⟨rf, nt, hx', -⟩ := h.scF hx
  refine ⟨⟨_, by rw [h.sk.ct]; exact hkt', by rw [h.sk.csc]; exact hxs, hs.notIpc hnb⟩,
    ⟨_, n, by rw [h.sk.csc]; exact hx'⟩, fun hne y m hy => ?_, by rw [h.sk.ct, h.sk.rel]; exact hC.notRel⟩
  rw [h.sk.csc] at hne hy
  obtain ⟨y0, rf', nt', hy0, rfl, -⟩ := h.scB hy
  exact hC.active hne y0 m hy0

theorem CFr.curRunW (h : CFr r t σ σ') (hR : CurRunW σ) : CurRunW σ' := by
  rcases hR with hR | e
  · refine Or.inl fun y hy => ?_
    rw [h.sk.ct] at hy
    obtain ⟨x, st, bn, fl, ar, hx, rfl, hs⟩ := h.tcbB hy
    show runnable st = true
    rw [hs.run (hR x hx)]; exact hR x hx
  · exact Or.inr (by rw [h.sk.ct, h.sk.idle]; exact e)

theorem CFr.sched (h : CFr r t σ σ') {u : ObjRef} (hs : schedulable u σ = true) : schedulable u σ' = true := by
  obtain ⟨x, scp, y, n, hk, hsc, hrun, hky, hact, hnr⟩ := schedulable_inv hs
  obtain ⟨st, bn, fl, ar, hk', hst⟩ := h.tcbF hk
  obtain ⟨rf, nt, hky', -⟩ := h.scF hky
  exact schedulable_of hk' hsc (by show runnable st = true; rw [hst.run hrun]; exact hrun) hky' hact
    (by rw [h.sk.rel]; exact hnr)

theorem CFr.kback (h : CFr r t σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e | ⟨ko, ko'', h1, h2, hc⟩
  · exact ⟨ko', by rw [← e, ho], id, id, id, id, id, id⟩
  · rw [ho] at h2; cases h2
    rcases hc with ⟨x, st, bn, fl, ar, rfl, rfl, -⟩ | ⟨hn, -⟩ | ⟨x, y, rfl, rfl, -⟩ | ⟨x, rfl, rfl, -⟩
    · exact ⟨_, h1, by simp⟩
    · rcases hn with ⟨x, st, bn, ar, rfl, rfl, -⟩ | ⟨y, n, rf, nt, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ <;>
        exact ⟨_, h1, by simp⟩
    · exact ⟨_, h1, by simp⟩
    · exact ⟨_, h1, by simp⟩

theorem CFr.ksz (h : CFr r t σ σ') : KSz σ σ' := fun o ko' ho => by
  obtain ⟨ko, h1, e⟩ := (h.kind o).2 ko' ho
  exact ⟨ko, h1, e.symm⟩

theorem CFr.ksub (h : CFr r t σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun rr cs hc hw => ⟨cs, ?_, hw⟩, fun u hu => ?_, fun hn => ?_⟩
  · exact h.othB hc (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e) (fun _ e => by cases e)
  · obtain ⟨x, -, -, -, -, hx, -⟩ := h.tcbB hu; exact ⟨x, hx⟩
  · rcases h.kh o with e | ⟨ko, ko', h1, -, -⟩
    · rw [e]; exact hn
    · rw [hn] at h1; cases h1

/-- What `CallRel` reads of the spec: the SCs' call stacks (and sizes), the
replies' `reply_sc`, the SCs back. -/
theorem CFr.callKeep (h : CFr r t σ σ') :
    (∀ q y n, σ.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
    (∀ q x, σ.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
    (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n)) := by
  refine ⟨fun q y n hq => ?_, fun q x hq => ?_, fun p x n hp => ?_⟩
  · obtain ⟨rf, nt, hq', -⟩ := h.scF hq; exact ⟨_, hq', rfl⟩
  · obtain ⟨y, hy, e, -⟩ := h.replyF hq; exact ⟨y, hy, e⟩
  · obtain ⟨y0, -, -, hy0, -⟩ := h.scB hp; exact ⟨y0, hy0⟩

end

end Spec

end

end Fl4Proofs.P3.Sched
