/-
P3 (DESIGN.md §9), IPC: **the spec's frame of `cancel_ipc` of a thread `t`
blocked sending on an endpoint or waiting on a notification** (spec side
only), toward `JAtZ.suspendJ`'s `hSd`/`hNt` (XTopJointSuspend; the J side is
XTopJointCancel).

`cancel_ipc t` clears `t`'s fault, removes `t` from its endpoint's or
notification's queue and sets it `Inactive`. IpcSignalBoundFr's `CFr` does
not hold it (its TCB change is from receive-blocked or inactive; a
notification's queue may only shrink by its own `r`'s steps), so:

* `KbIn`: blocked on an endpoint or a notification, or inactive.
* `KChg`: `t`'s TCB, `KbIn`, to `Inactive` or its state, its fault changed;
  an endpoint holding `t` to a sub-queue; a notification holding `t` to
  another object with a sub-queue (its binding and SC kept).
* `KFr`: the frame (`Sk` and `KChg` objectwise); `KFr.trans`, `KFr.upd`,
  `KFr.sts`; the per-kind lemmas and what it keeps (as `CFr`'s: `szKeep`,
  `ykeep`, `mcpKeep`, `bufKeep`, `nsc`, `isorted`, `own`, `off`, `idleOK`,
  `bsa`, `curInv`, `curRunW`, `sched`, `kback`, `ksz`, `ksub`, `callKeep`,
  `skeep`): `t` changed is not runnable (so neither current under `CurInv`,
  nor a switch target, nor idle) and ends in no IPC queue.
* `cancelIpc_send_kfr`, `cancelIpc_ntfn_kfr`: the spec's `cancel_ipc` of a
  thread blocked sending, or on a notification, in `KFr`, `t` `Inactive`
  with no fault, the action kept or `choose_new_thread`.
* `cancel_kb_inv`: `Inv` after (`ikm_cancelIpc`, `InvBut.ik`), `t`'s
  `RelIfBound` carried from before (`Inv.rd`) by `KFr.skeep`.
-/
import Fl4Proofs.P3.IpcSignalBoundSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- Blocked on an endpoint or a notification, or inactive. -/
def KbIn (ts : ThreadState) : Prop :=
  (∃ e d, ts = .blockedOnSend e d) ∨ (∃ e ro d, ts = .blockedOnReceive e ro d) ∨
    (∃ n, ts = .blockedOnNotification n) ∨ ts = .inactive

theorem KbIn.not_run {ts : ThreadState} (h : KbIn ts) : runnable ts = false := by
  rcases h with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ | rfl <;> rfl

/-- **A TCB's change** (`p`'s, `x` to `{x with tcbState := st, tcbFault := fl}`). -/
def TKc (t p : ObjRef) (x : Tcb) (st : ThreadState) (fl : Option Fault) : Prop :=
  (st = x.tcbState ∧ fl = x.tcbFault) ∨ (p = t ∧ KbIn x.tcbState ∧ (st = .inactive ∨ st = x.tcbState))

theorem TKc.run {t p : ObjRef} {x : Tcb} {st : ThreadState} {fl : Option Fault} (h : TKc t p x st fl)
    (hr : runnable x.tcbState = true) : st = x.tcbState := by
  rcases h with ⟨e, -⟩ | ⟨-, hx, -⟩
  · exact e
  · rw [hx.not_run] at hr; cases hr

theorem TKc.ipcQ {t p : ObjRef} {x : Tcb} {st : ThreadState} {fl : Option Fault} (h : TKc t p x st fl)
    (hq : ipcQueuedThreadState st = true) : ipcQueuedThreadState x.tcbState = true := by
  rcases h with ⟨e, -⟩ | ⟨-, -, e | e⟩
  · rw [← e]; exact hq
  · rw [e] at hq; simp [ipcQueuedThreadState] at hq
  · rw [← e]; exact hq

theorem TKc.notIpc {t p : ObjRef} {x : Tcb} {st : ThreadState} {fl : Option Fault} (h : TKc t p x st fl)
    (hn : NotIpcBlk x.tcbState) : NotIpcBlk st := by
  rcases h with ⟨e, -⟩ | ⟨-, -, e | e⟩
  · rw [e]; exact hn
  · rw [e]; unfold NotIpcBlk; exact ⟨fun _ e => (by cases e), fun _ _ e => (by cases e), fun _ _ _ e => (by cases e)⟩
  · rw [e]; exact hn

theorem TKc.st {t p : ObjRef} {x : Tcb} {st : ThreadState} {fl : Option Fault} (h : TKc t p x st fl)
    (hb : ¬ KbIn x.tcbState) : st = x.tcbState := by
  rcases h with ⟨e, -⟩ | ⟨-, hx, -⟩
  · exact e
  · exact absurd hx hb

/-- **One object's change** (module docstring). -/
def KChg (t p : ObjRef) (o o' : KernelObject) : Prop :=
  (∃ x st fl, o = .tcb x ∧ o' = .tcb { x with tcbState := st, tcbFault := fl } ∧ p = t ∧ KbIn x.tcbState ∧
    (st = .inactive ∨ st = x.tcbState)) ∨
  (∃ x y, o = .endpoint x ∧ o' = .endpoint y ∧ y.epQueue.Sublist x.epQueue ∧ t ∈ x.epQueue) ∨
  (∃ x ob, o = .notification x ∧ o' = .notification { x with ntfnObj := ob } ∧
    ob.ntfnQueue.Sublist x.ntfnObj.ntfnQueue ∧ t ∈ x.ntfnObj.ntfnQueue)

theorem KChg.trans {t p : ObjRef} {o1 o2 o3 : KernelObject} (h1 : KChg t p o1 o2) (h2 : KChg t p o2 o3) :
    KChg t p o1 o3 := by
  rcases h1 with ⟨x, st, fl, rfl, rfl, hp, hx, hs⟩ | ⟨x, y, rfl, rfl, hs, hm⟩ | ⟨x, ob, rfl, rfl, hs, hm⟩
  · rcases h2 with ⟨x2, st2, fl2, e, rfl, -, -, hs2⟩ | ⟨_, _, e, -⟩ | ⟨_, _, e, -⟩ <;> cases e
    refine Or.inl ⟨x, st2, fl2, rfl, rfl, hp, hx, ?_⟩
    rcases hs2 with e | e
    · exact Or.inl e
    · rw [e]; exact hs
  · rcases h2 with ⟨_, _, _, e, -⟩ | ⟨x2, z, e, rfl, hs2, -⟩ | ⟨_, _, e, -⟩ <;> cases e
    exact Or.inr (Or.inl ⟨x, z, rfl, rfl, hs2.trans hs, hm⟩)
  · rcases h2 with ⟨_, _, _, e, -⟩ | ⟨_, _, e, -⟩ | ⟨x2, ob2, e, rfl, hs2, -⟩ <;> cases e
    exact Or.inr (Or.inr ⟨x, ob2, rfl, rfl, hs2.trans hs, hm⟩)

/-- **The spec's frame of `cancel_ipc t`** (module docstring). -/
structure KFr (t : ObjRef) (σ σ' : State Unit) : Prop where
  sk : Sk σ σ'
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ o o', σ.kheap p = some o ∧ σ'.kheap p = some o' ∧ KChg t p o o'

theorem KFr.refl (t : ObjRef) (σ : State Unit) : KFr t σ σ := ⟨Sk.refl σ, fun _ => Or.inl rfl⟩

theorem KFr.trans {t : ObjRef} {σ1 σ2 σ3 : State Unit} (h1 : KFr t σ1 σ2) (h2 : KFr t σ2 σ3) :
    KFr t σ1 σ3 := by
  refine ⟨h1.sk.trans h2.sk, fun p => ?_⟩
  rcases h2.kh p with e2 | ⟨o2, o3, k2, k3, c2⟩
  · rw [e2]; exact h1.kh p
  · rcases h1.kh p with e1 | ⟨o1, o2', k1, k2', c1⟩
    · exact Or.inr ⟨o2, o3, by rw [← e1]; exact k2, k3, c2⟩
    · obtain rfl := Option.some.inj (k2'.symm.trans k2)
      exact Or.inr ⟨o1, o3, k1, k3, c1.trans c2⟩

theorem KFr.upd {t : ObjRef} {σ : State Unit} {p : ObjRef} {o o' : KernelObject}
    (hk : σ.kheap p = some o) (hc : KChg t p o o') : KFr t σ (updK σ p o') := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun p' => ?_⟩
  by_cases e : p' = p
  · subst e; exact Or.inr ⟨o, o', hk, by simp [updK], hc⟩
  · exact Or.inl (by simp [updK, e])

theorem KFr.sts (t : ObjRef) (σ : State Unit) (u : ObjRef) : KFr t σ (Notif.stsAct σ u) := by
  unfold Notif.stsAct; split
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => Or.inl rfl⟩
  · exact KFr.refl _ _

/-- `t`, `KbIn`, set `Inactive`. -/
theorem KFr.stsIn {t : ObjRef} {σ : State Unit} {y : Tcb} (hk : σ.kheap t = some (.tcb y))
    (hrb : KbIn y.tcbState) :
    KFr t σ (stsAct (updK σ t (.tcb { y with tcbState := .inactive })) t) :=
  (KFr.upd hk (Or.inl ⟨y, .inactive, y.tcbFault, rfl, rfl, rfl, hrb, Or.inl rfl⟩)).trans (KFr.sts _ _ _)

/-! ### Per kind -/

section
variable {t : ObjRef} {σ σ' : State Unit}

theorem KFr.tcbF (h : KFr t σ σ') {p : ObjRef} {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    ∃ st fl, σ'.kheap p = some (.tcb { x with tcbState := st, tcbFault := fl }) ∧ TKc t p x st fl := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x.tcbState, x.tcbFault, by rw [e, hp], Or.inl ⟨rfl, rfl⟩⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨x', st, fl, e1, rfl, hp', hx, hs⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨st, fl, h2, Or.inr ⟨hp', hx, hs⟩⟩

theorem KFr.tcbB (h : KFr t σ σ') {p : ObjRef} {y : Tcb} (hp : σ'.kheap p = some (.tcb y)) :
    ∃ x st fl, σ.kheap p = some (.tcb x) ∧ y = { x with tcbState := st, tcbFault := fl } ∧ TKc t p x st fl := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, y.tcbState, y.tcbFault, by rw [← e, hp], rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨x, st, fl, rfl, e2, hp', hx, hs⟩ | ⟨_, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨x, st, fl, h1, rfl, Or.inr ⟨hp', hx, hs⟩⟩

/-- The other kinds kept. -/
theorem KFr.othF (h : KFr t σ σ') {p : ObjRef} {o : KernelObject} (hp : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h3 : ∀ x, o ≠ .notification x) (h4 : ∀ x, o ≠ .endpoint x) :
    σ'.kheap p = some o := by
  rcases h.kh p with e | ⟨o0, o', k1, k2, hc⟩
  · rw [e, hp]
  · rw [hp] at k1; cases k1
    rcases hc with ⟨_, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩
    · exact absurd e1 (h1 _)
    · exact absurd e1 (h4 _)
    · exact absurd e1 (h3 _)

theorem KFr.othB (h : KFr t σ σ') {p : ObjRef} {o' : KernelObject} (hp : σ'.kheap p = some o')
    (h1 : ∀ x, o' ≠ .tcb x) (h3 : ∀ x, o' ≠ .notification x) (h4 : ∀ x, o' ≠ .endpoint x) :
    σ.kheap p = some o' := by
  rcases h.kh p with e | ⟨o, o'', k1, k2, hc⟩
  · rw [← e, hp]
  · rw [hp] at k2; cases k2
    rcases hc with ⟨_, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩
    · exact absurd e2 (h1 _)
    · exact absurd e2 (h4 _)
    · exact absurd e2 (h3 _)

theorem KFr.scF (h : KFr t σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ.kheap p = some (.schedContext y n)) : σ'.kheap p = some (.schedContext y n) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem KFr.scB (h : KFr t σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ'.kheap p = some (.schedContext y n)) : σ.kheap p = some (.schedContext y n) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem KFr.replyF (h : KFr t σ σ') {p : ObjRef} {x : Reply} (hp : σ.kheap p = some (.reply x)) :
    σ'.kheap p = some (.reply x) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem KFr.replyB (h : KFr t σ σ') {p : ObjRef} {x : Reply} (hp : σ'.kheap p = some (.reply x)) :
    σ.kheap p = some (.reply x) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem KFr.ntfnB (h : KFr t σ σ') {p : ObjRef} {y : Notification} (hp : σ'.kheap p = some (.notification y)) :
    ∃ x, σ.kheap p = some (.notification x) ∧ y.ntfnObj.ntfnQueue.Sublist x.ntfnObj.ntfnQueue ∧
      y.ntfnSc = x.ntfnSc ∧ y.ntfnBoundTcb = x.ntfnBoundTcb ∧ (y = x ∨ t ∈ x.ntfnObj.ntfnQueue) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e, hp], List.Sublist.refl _, rfl, rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨x, ob, rfl, e2, hs, hm⟩ <;> cases e2
    exact ⟨x, h1, hs, rfl, rfl, Or.inr hm⟩

theorem KFr.ntfnF (h : KFr t σ σ') {p : ObjRef} {x : Notification} (hp : σ.kheap p = some (.notification x)) :
    ∃ y, σ'.kheap p = some (.notification y) ∧ y.ntfnSc = x.ntfnSc ∧ y.ntfnBoundTcb = x.ntfnBoundTcb ∧
      (y = x ∨ t ∈ x.ntfnObj.ntfnQueue) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [e, hp], rfl, rfl, Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨x', ob, e1, rfl, -, hm⟩ <;> cases e1
    exact ⟨_, h2, rfl, rfl, Or.inr hm⟩

theorem KFr.epF (h : KFr t σ σ') {p : ObjRef} {x : Endpoint} (hp : σ.kheap p = some (.endpoint x)) :
    ∃ y, σ'.kheap p = some (.endpoint y) ∧ (y = x ∨ (y.epQueue.Sublist x.epQueue ∧ t ∈ x.epQueue)) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [e, hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, e1, -⟩ | ⟨x', y, e1, rfl, hs, hm⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨y, h2, Or.inr ⟨hs, hm⟩⟩

theorem KFr.epB (h : KFr t σ σ') {p : ObjRef} {y : Endpoint} (hp : σ'.kheap p = some (.endpoint y)) :
    ∃ x, σ.kheap p = some (.endpoint x) ∧ (y = x ∨ (y.epQueue.Sublist x.epQueue ∧ t ∈ x.epQueue)) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e, hp], Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, -, e2, -⟩ | ⟨x, y', rfl, e2, hs, hm⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨x, h1, Or.inr ⟨hs, hm⟩⟩

/-- The objects' kinds and sizes kept, both ways. -/
theorem KFr.kind (h : KFr t σ σ') (p : ObjRef) :
    (∀ o, σ.kheap p = some o → ∃ o', σ'.kheap p = some o' ∧ aType o' = aType o) ∧
    (∀ o', σ'.kheap p = some o' → ∃ o, σ.kheap p = some o ∧ aType o' = aType o) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨fun o ho => ⟨o, by rw [e, ho], rfl⟩, fun o' ho => ⟨o', by rw [← e, ho], rfl⟩⟩
  · have ha : aType o' = aType o := by
      rcases hc with ⟨x, st, fl, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ | ⟨x, ob, rfl, rfl, -⟩ <;> rfl
    exact ⟨fun o0 ho0 => ⟨o', h2, by rw [h1] at ho0; cases ho0; exact ha⟩,
      fun o0 ho0 => ⟨o, h1, by rw [h2] at ho0; cases ho0; exact ha⟩⟩

/-! ### What the frame keeps -/

theorem KFr.szKeep (h : KFr t σ σ') : SzKeep σ σ' := fun _ y n hp => ⟨y, h.scB hp⟩

theorem KFr.ykeep (h : KFr t σ σ') : YKeep σ σ' := by
  refine ⟨fun p x hp => ?_, fun p y n hp => ⟨y, h.scF hp, rfl⟩, fun p z n hp => ⟨z, h.scB hp, rfl⟩⟩
  obtain ⟨st, fl, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem KFr.mcpKeep (h : KFr t σ σ') : McpKeep σ σ' := fun p x hp => by
  obtain ⟨st, fl, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem KFr.bufKeep (h : KFr t σ σ') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => by obtain ⟨st, fl, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem KFr.prio (h : KFr t σ σ') (u : ObjRef) : prioOf σ' u = prioOf σ u := by
  unfold prioOf
  rw [tcbsOf_eq, tcbsOf_eq]
  cases hk : σ.kheap u with
  | some o =>
    cases o with
    | tcb x =>
      obtain ⟨st, fl, hk', -⟩ := h.tcbF hk
      rw [hk']; rfl
    | _ =>
      cases hk' : σ'.kheap u with
      | none => rfl
      | some o' => cases o' with
        | tcb y => obtain ⟨x, -, -, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
        | _ => rfl
  | none =>
    cases hk' : σ'.kheap u with
    | none => rfl
    | some o' => cases o' with
      | tcb y => obtain ⟨x, -, -, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
      | _ => rfl

theorem KFr.nsc {N C : Set U64} (h : KFr t σ σ') (hN : NSC N C σ) : NSC N C σ' := by
  intro n hn y p hy hp
  obtain ⟨x, hx, -, hs, -, -⟩ := h.ntfnB hy
  exact hN n hn x p hx (hs ▸ hp)

theorem KFr.isorted (h : KFr t σ σ') (hS : IpcSorted σ) : IpcSorted σ' := by
  refine ⟨fun p y hp => ?_, fun p y hp => ?_⟩
  · obtain ⟨x, hx, hc⟩ := h.epB hp
    rcases hc with rfl | ⟨hsub, -⟩
    · exact (hS.1 p y hx).congr fun u _ => h.prio u
    · exact ((hS.1 p x hx).sublist hsub).congr fun u _ => h.prio u
  · obtain ⟨x, hx, hsub, -⟩ := h.ntfnB hp
    exact ((hS.2 p x hx).sublist hsub).congr fun u _ => h.prio u

theorem KFr.own {T C : Set U64} (h : KFr t σ σ') (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · obtain ⟨st, fl, hkt', -⟩ := h.tcbF hkt
    refine Or.inl ⟨u, hu, _, hkt', by rw [h.sk.csc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
    · rw [h.sk.csc] at hy
      exact hown y n (h.scB hy)
    · rw [h.sk.cons] at h0; rw [h.sk.rel] at hm; exact hnr h0 hm
  · refine Or.inr ⟨by rw [h.sk.csc]; exact hcs, fun y n hy => ?_⟩
    rw [h.sk.csc] at hy
    exact hun y n (h.scB hy)

theorem KFr.off (h : KFr t σ σ') (hO : OffOK σ) : OffOK σ' := by
  intro hc y n hy ha
  rw [h.sk.cons] at hc ⊢; rw [h.sk.tm]
  rw [h.sk.csc] at hy ha
  exact hO hc y n (h.scB hy) ha

theorem KFr.idleOK (h : KFr t σ σ') (hO : IdleOK σ) : IdleOK σ' := by
  obtain ⟨x, hx, h1, h2, h3⟩ := hO
  obtain ⟨st, fl, hx', hs⟩ := h.tcbF hx
  refine ⟨{ x with tcbState := st, tcbFault := fl }, by rw [h.sk.idle]; exact hx', h1, ?_,
    by rw [h.sk.idle, h.sk.rel]; exact h3⟩
  show st = _
  rw [hs.st (by rw [h2]; rintro (⟨_, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, e⟩ | e) <;> cases e)]; exact h2

theorem KFr.bsa (h : KFr t σ σ') (hB : BlockedScActive σ) : BlockedScActive σ' := by
  refine ⟨fun p z n u y hp hyt hy hq => ?_, fun p z n hp hr => hB.replies p z n (h.scB hp) hr⟩
  obtain ⟨x, st, fl, hx, rfl, hs⟩ := h.tcbB hy
  exact hB.tcb p z n u x (h.scB hp) hyt hx (hs.ipcQ hq)

theorem KFr.curInv (h : KFr t σ σ') (hC : CurInv σ) : CurInv σ' := by
  obtain ⟨xt, hkt, hxs, hnb⟩ := hC.tcb
  obtain ⟨x, n, hx⟩ := hC.sc
  obtain ⟨st, fl, hkt', hs⟩ := h.tcbF hkt
  refine ⟨⟨_, by rw [h.sk.ct]; exact hkt', by rw [h.sk.csc]; exact hxs, hs.notIpc hnb⟩,
    ⟨x, n, by rw [h.sk.csc]; exact h.scF hx⟩, fun hne y m hy => ?_, by rw [h.sk.ct, h.sk.rel]; exact hC.notRel⟩
  rw [h.sk.csc] at hne hy
  exact hC.active hne y m (h.scB hy)

theorem KFr.curRunW (h : KFr t σ σ') (hR : CurRunW σ) : CurRunW σ' := by
  rcases hR with hR | e
  · refine Or.inl fun y hy => ?_
    rw [h.sk.ct] at hy
    obtain ⟨x, st, fl, hx, rfl, hs⟩ := h.tcbB hy
    show runnable st = true
    rw [hs.run (hR x hx)]; exact hR x hx
  · exact Or.inr (by rw [h.sk.ct, h.sk.idle]; exact e)

theorem KFr.sched (h : KFr t σ σ') {u : ObjRef} (hs : schedulable u σ = true) : schedulable u σ' = true := by
  obtain ⟨x, scp, y, n, hk, hsc, hrun, hky, hact, hnr⟩ := schedulable_inv hs
  obtain ⟨st, fl, hk', hst⟩ := h.tcbF hk
  exact schedulable_of hk' hsc (by show runnable st = true; rw [hst.run hrun]; exact hrun) (h.scF hky) hact
    (by rw [h.sk.rel]; exact hnr)

theorem KFr.kback (h : KFr t σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e | ⟨ko, ko'', h1, h2, hc⟩
  · exact ⟨ko', by rw [← e, ho], id, id, id, id, id, id⟩
  · rw [ho] at h2; cases h2
    rcases hc with ⟨x, st, fl, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ | ⟨x, ob, rfl, rfl, -⟩
    · exact ⟨_, h1, by simp⟩
    · exact ⟨_, h1, by simp⟩
    · exact ⟨_, h1, by simp⟩

theorem KFr.ksz (h : KFr t σ σ') : KSz σ σ' := fun o ko' ho => by
  obtain ⟨ko, h1, e⟩ := (h.kind o).2 ko' ho
  exact ⟨ko, h1, e.symm⟩

theorem KFr.ksub (h : KFr t σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun rr cs hc hw => ⟨cs, ?_, hw⟩, fun u hu => ?_, fun hn => ?_⟩
  · exact h.othB hc (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)
  · obtain ⟨x, -, -, hx, -⟩ := h.tcbB hu; exact ⟨x, hx⟩
  · rcases h.kh o with e | ⟨ko, ko', h1, -, -⟩
    · rw [e]; exact hn
    · rw [hn] at h1; cases h1

/-- What `CallRel` reads of the spec: the SCs' call stacks (and sizes), the
replies, the SCs back. -/
theorem KFr.callKeep (h : KFr t σ σ') :
    (∀ q y n, σ.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
    (∀ q x, σ.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
    (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n)) :=
  ⟨fun q y n hq => ⟨y, h.scF hq, rfl⟩, fun q x hq => ⟨x, h.replyF hq, rfl⟩, fun p x n hp => ⟨x, h.scB hp⟩⟩

/-- The release queue, the time, the threads' SCs and the SCs kept. -/
theorem KFr.skeep (h : KFr t σ σ') : Ipc.SKeep σ σ' := by
  refine ⟨h.sk.rel, h.sk.tm, fun p y hy => ?_, fun p y n hy => h.scB hy⟩
  obtain ⟨x, st, fl, hx, rfl, -⟩ := h.tcbB hy
  exact ⟨x, hx, rfl⟩

end

/-! ### The spec's `cancel_ipc` -/

/-- **`cancel_ipc` of a thread blocked sending** in the frame `KFr`
(module docstring). -/
theorem cancelIpc_send_kfr {σ σ1 : State Unit} {t ep : ObjRef} {d : SenderPayload}
    {x : Tcb} {xe : Endpoint} (hkt : σ.kheap t = some (.tcb x)) (hst : x.tcbState = .blockedOnSend ep d)
    (hke : σ.kheap ep = some (.endpoint xe)) (hq : t ∈ xe.epQueue)
    (hm : ((), σ1) ∈ (cancelIpc (Z := Unit) t σ).1) :
    KFr t σ σ1 ∧ σ1.kheap t = some (.tcb { x with tcbFault := none, tcbState := .inactive }) ∧
      (σ1.schedulerAction = σ.schedulerAction ∨ σ1.schedulerAction = .chooseNewThread) := by
  have hte : t ≠ ep := by rintro rfl; rw [hkt] at hke; cases hke
  have hrb : KbIn x.tcbState := Or.inl ⟨ep, d, hst⟩
  set x1 : Tcb := { x with tcbFault := none } with hx1
  set σA := updK σ t (.tcb x1) with hσA
  have hkA : σA.kheap t = some (.tcb x1) := by simp [hσA, updK]
  have hkeA : σA.kheap ep = some (.endpoint xe) := by simp [hσA, updK, Ne.symm hte, hke]
  have FA : KFr t σ σA := KFr.upd hkt (Or.inl ⟨x, x.tcbState, none, rfl, rfl, rfl, hrb, Or.inr rfl⟩)
  set σB := updK σA ep (.endpoint (Endp.epDeq xe t)) with hσB
  have hkB : σB.kheap t = some (.tcb x1) := by simp [hσB, updK, hte, hkA]
  have FB : KFr t σA σB := KFr.upd hkeA (Or.inr (Or.inl ⟨xe, Endp.epDeq xe t, rfl, rfl,
    by rw [epDeq_queue']; unfold removeAll; exact List.filter_sublist, hq⟩))
  have hdq : tcbEpDequeue (Z := Unit) t ep σA = ({((), σB)}, False) := Endp.tcbEpDequeue_eq hkeA hq
  have hrb1 : KbIn x1.tcbState := hrb
  have hts : threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) t σ = ({((), σA)}, False) :=
    threadSet_eq _ hkt
  have hasrt : NonDet.assertOpt (σ := State Unit) (epBlocked (.blockedOnSend ep d)) σA =
      ({(ep, σA)}, False) := rfl
  have e : cancelIpc (Z := Unit) t σ = ({((), stsAct (updK σB t (.tcb { x1 with tcbState := .inactive })) t)},
      False) := by
    unfold cancelIpc
    rw [nd_bind_one (getThreadState_eq hkt), nd_bind_one hts, hst]
    show blockedCancelIpc (Z := Unit) (.blockedOnSend ep d) t none σA = _
    unfold blockedCancelIpc getBlockingObject
    rw [nd_bind_one hasrt, nd_bind_one hdq]
    dsimp only
    rw [Notif.setThreadState_eq _ hkB]
  rw [e] at hm
  have e1 := (Prod.mk.inj (Set.mem_singleton_iff.1 hm)).2
  subst e1
  refine ⟨(FA.trans FB).trans (KFr.stsIn hkB hrb1), by rw [stsAct_kheap]; simp [updK, hx1], ?_⟩
  exact act_sts (Or.inl rfl)

set_option maxHeartbeats 4000000 in
/-- **`cancel_ipc` of a thread blocked on a notification** in the frame
`KFr` (module docstring). -/
theorem cancelIpc_ntfn_kfr {σ σ1 : State Unit} {t n : ObjRef} {x : Tcb} {xn : Notification}
    (hkt : σ.kheap t = some (.tcb x)) (hst : x.tcbState = .blockedOnNotification n)
    (hkn : σ.kheap n = some (.notification xn)) (hq : t ∈ ntfnQueueOf xn)
    (hm : ((), σ1) ∈ (cancelIpc (Z := Unit) t σ).1) :
    KFr t σ σ1 ∧ σ1.kheap t = some (.tcb { x with tcbFault := none, tcbState := .inactive }) ∧
      (σ1.schedulerAction = σ.schedulerAction ∨ σ1.schedulerAction = .chooseNewThread) := by
  have htn : t ≠ n := by rintro rfl; rw [hkt] at hkn; cases hkn
  have hrb : KbIn x.tcbState := Or.inr (Or.inr (Or.inl ⟨n, hst⟩))
  set x1 : Tcb := { x with tcbFault := none } with hx1
  set σA := updK σ t (.tcb x1) with hσA
  have hkA : σA.kheap t = some (.tcb x1) := by simp [hσA, updK]
  have hknA : σA.kheap n = some (.notification xn) := by simp [hσA, updK, Ne.symm htn, hkn]
  have FA : KFr t σ σA := KFr.upd hkt (Or.inl ⟨x, x.tcbState, none, rfl, rfl, rfl, hrb, Or.inr rfl⟩)
  set ob : Ntfn := match removeAll t (ntfnQueueOf xn) with
    | [] => Ntfn.idleNtfn
    | _ => Ntfn.waitingNtfn (removeAll t (ntfnQueueOf xn)) with hob
  have hsub : ob.ntfnQueue.Sublist xn.ntfnObj.ntfnQueue := by
    have hs0 : (removeAll t (ntfnQueueOf xn)).Sublist (ntfnQueueOf xn) := by
      unfold removeAll; exact List.filter_sublist
    rw [hob]
    revert hs0
    cases removeAll t (ntfnQueueOf xn) with
    | nil => intro _; exact List.nil_sublist _
    | cons a l => intro hs0; exact hs0
  set σB := updK σA n (.notification (ntfnObjUpdate (fun _ => ob) xn)) with hσB
  have hdq : tcbNtfnDequeue (Z := Unit) t n σA = ({((), σB)}, False) := tcbNtfnDequeue_eq hknA hq
  have hkB : σB.kheap t = some (.tcb x1) := by simp [hσB, updK, htn, hkA]
  have FB : KFr t σA σB := KFr.upd hknA (Or.inr (Or.inr ⟨xn, ob, rfl, rfl, hsub, hq⟩))
  have hrb1 : KbIn x1.tcbState := hrb
  have hts : threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) t σ = ({((), σA)}, False) :=
    threadSet_eq _ hkt
  have e : cancelIpc (Z := Unit) t σ = ({((), stsAct (updK σB t (.tcb { x1 with tcbState := .inactive })) t)},
      False) := by
    unfold cancelIpc
    rw [nd_bind_one (getThreadState_eq hkt), nd_bind_one hts, hst]
    show cancelSignal (Z := Unit) t n σA = _
    unfold cancelSignal
    rw [nd_bind_one hdq]
    exact Notif.setThreadState_eq .inactive hkB
  rw [e] at hm
  have e1 := (Prod.mk.inj (Set.mem_singleton_iff.1 hm)).2
  subst e1
  refine ⟨(FA.trans FB).trans (KFr.stsIn hkB hrb1), by rw [stsAct_kheap]; simp [updK, hx1], ?_⟩
  exact act_sts (Or.inl rfl)

/-- **`Inv` after `cancel_ipc` of a thread not runnable** (module docstring). -/
theorem cancel_kb_inv {σ σ1 : State Unit} {t : ObjRef} {x : Tcb} (hI : Inv σ) (hkt : σ.kheap t = some (.tcb x))
    (hnr : runnable x.tcbState = false) (hm : ((), σ1) ∈ (cancelIpc (Z := Unit) t σ).1)
    (hrib : RelIfBound σ1 t) : Inv σ1 := by
  have ik : IK t σ σ1 := ikm_cancelIpc σ ((), σ1) hm
  obtain ⟨hB, -⟩ := (hI.toBut t).ik (hI.notQueued hkt hnr) ik
  exact hB.inv fun _ _ _ => hrib

/-- `t`'s `RelIfBound` across `KFr`, from `Inv` before (`t` in `inClass`). -/
theorem KFr.rib {σ σ1 : State Unit} {t : ObjRef} {x : Tcb} (F : KFr t σ σ1) (hI : Inv σ)
    (hkt : σ.kheap t = some (.tcb x)) (hc : inClass x.tcbState) : RelIfBound σ1 t :=
  Ipc.RelIfBound.of_keep (hI.rd t x hkt hc) F.skeep

end Spec

end

end Fl4Proofs.P3.Sched
