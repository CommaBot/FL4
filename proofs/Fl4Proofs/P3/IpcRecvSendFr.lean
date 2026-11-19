/-
P3 (DESIGN.md §9), IPC: **the spec's frame of `receive_ipc` from a waiting
sender** (spec side only; toward XTopJointRecvIpcLink's `JRecvSendHyp`, l4v
`receive_ipc`'s `send_ep` branch).

The receive dequeues the head sender `t`, transfers the message into the
current thread `r` (its registers: `tcbArch`), runs the sender's sporadic
check (its SC's refills, never the current SC's) and wakes the sender (here
`Running`). Neither IpcSignalBoundFr's `CFr`/IpcSignalDonFr's `DWFr` (the
woken thread receive-blocked or inactive; only the woken thread's registers
change) nor IpcCancelFr's `KFr` (no `Running`, no register or SC change)
holds it, so:

* `RSTc`: a TCB's state and registers changed: the registers only of `r`, the
  state only of `t`, from `KbIn` to `Inactive` or `Running`.
* `RSChg`: a TCB by `RSTc`; an SC other than the current one, its refills
  only; an endpoint holding `t` to a sub-queue.
* `RSFr`: the frame (`Sk` and `RSChg` objectwise); `RSFr.trans`, `RSFr.upd`,
  `RSFr.sts`, `RSFr.um`, `RSFr.reprog`; the per-kind lemmas and what it keeps
  (as `KFr`'s: `szKeep`, `ykeep`, `mcpKeep`, `bufKeep`, `nsc`, `isorted`,
  `own`, `off`, `idleOK`, `bsa`, `curInv`, `curRunW`, `sched`, `kback`,
  `ksz`, `ksub`, `callKeep`, `khrb`): `t` changed is not runnable before (so
  neither current under `CurInv`, nor idle); the current SC is kept; an SC's
  `scActive` reads only its refill maximum.
-/
import Fl4Proofs.P3.IpcCancelFr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- **A TCB's change in a receive from a sender** (`p`'s, `x` to
`{x with tcbState := st, tcbArch := ar}`; module docstring). -/
def RSTc (t r p : ObjRef) (x : Tcb) (st : ThreadState) (ar : ArchTcb) : Prop :=
  (ar = x.tcbArch ∨ p = r) ∧ (st = x.tcbState ∨ (p = t ∧ KbIn x.tcbState ∧ (st = .inactive ∨ st = .running)))

section
variable {t r p : ObjRef} {x : Tcb} {st : ThreadState} {ar : ArchTcb}

theorem RSTc.run (h : RSTc t r p x st ar) (hr : runnable x.tcbState = true) : st = x.tcbState := by
  rcases h.2 with e | ⟨-, hx, -⟩
  · exact e
  · rw [hx.not_run] at hr; cases hr

theorem RSTc.ipcQ (h : RSTc t r p x st ar) (hq : ipcQueuedThreadState st = true) :
    ipcQueuedThreadState x.tcbState = true := by
  rcases h.2 with e | ⟨-, -, e | e⟩
  · rw [← e]; exact hq
  · rw [e] at hq; simp [ipcQueuedThreadState] at hq
  · rw [e] at hq; simp [ipcQueuedThreadState] at hq

theorem RSTc.notIpc (h : RSTc t r p x st ar) (hn : NotIpcBlk x.tcbState) : NotIpcBlk st := by
  rcases h.2 with e | ⟨-, -, e | e⟩
  · rw [e]; exact hn
  · rw [e]; unfold NotIpcBlk; exact ⟨fun _ e => (by cases e), fun _ _ e => (by cases e), fun _ _ _ e => (by cases e)⟩
  · rw [e]; unfold NotIpcBlk; exact ⟨fun _ e => (by cases e), fun _ _ e => (by cases e), fun _ _ _ e => (by cases e)⟩

theorem RSTc.stK (h : RSTc t r p x st ar) (hb : ¬ KbIn x.tcbState) : st = x.tcbState := by
  rcases h.2 with e | ⟨-, hx, -⟩
  · exact e
  · exact absurd hx hb

theorem RSTc.trans {st1 st2 : ThreadState} {ar1 ar2 : ArchTcb} (h1 : RSTc t r p x st1 ar1)
    (h2 : RSTc t r p { x with tcbState := st1, tcbArch := ar1 } st2 ar2) : RSTc t r p x st2 ar2 := by
  refine ⟨?_, ?_⟩
  · rcases h2.1 with e | e
    · have e' : ar2 = ar1 := e
      rcases h1.1 with e1 | e1
      · exact Or.inl (e'.trans e1)
      · exact Or.inr e1
    · exact Or.inr e
  · rcases h2.2 with e | ⟨hp, hk, hs⟩
    · have e' : st2 = st1 := e
      rw [e']; exact h1.2
    · have hk' : KbIn st1 := hk
      refine Or.inr ⟨hp, ?_, hs⟩
      rcases h1.2 with e1 | ⟨-, hx, h1s | h1s⟩
      · rw [← e1]; exact hk'
      · exact hx
      · rw [h1s] at hk'
        rcases hk' with ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, e⟩ | e <;> cases e

end

/-- **An object's change in a receive from a sender** (module docstring). -/
def RSChg (t r cur p : ObjRef) (o o' : KernelObject) : Prop :=
  (∃ x st ar, o = .tcb x ∧ o' = .tcb { x with tcbState := st, tcbArch := ar } ∧ RSTc t r p x st ar) ∨
  (∃ y n rf, o = .schedContext y n ∧ o' = .schedContext { y with scRefills := rf } n ∧ p ≠ cur) ∨
  (∃ x y, o = .endpoint x ∧ o' = .endpoint y ∧ y.epQueue.Sublist x.epQueue ∧ t ∈ x.epQueue)

theorem RSChg.trans {t r cur p : ObjRef} {o1 o2 o3 : KernelObject} (h1 : RSChg t r cur p o1 o2)
    (h2 : RSChg t r cur p o2 o3) : RSChg t r cur p o1 o3 := by
  rcases h1 with ⟨x, st, ar, rfl, rfl, hs⟩ | ⟨y, n, rf, rfl, rfl, hp⟩ | ⟨x, y, rfl, rfl, hs, hm⟩
  · rcases h2 with ⟨x2, st2, ar2, e, rfl, hs2⟩ | ⟨_, _, _, e, -⟩ | ⟨_, _, e, -⟩ <;> cases e
    exact Or.inl ⟨x, st2, ar2, rfl, rfl, hs.trans hs2⟩
  · rcases h2 with ⟨_, _, _, e, -⟩ | ⟨y2, n2, rf2, e, rfl, -⟩ | ⟨_, _, e, -⟩ <;> cases e
    exact Or.inr (Or.inl ⟨y, n, rf2, rfl, rfl, hp⟩)
  · rcases h2 with ⟨_, _, _, e, -⟩ | ⟨_, _, _, e, -⟩ | ⟨x2, z, e, rfl, hs2, -⟩ <;> cases e
    exact Or.inr (Or.inr ⟨x, z, rfl, rfl, hs2.trans hs, hm⟩)

/-- **The spec's frame of a receive from a sender** (module docstring). -/
structure RSFr (t r : ObjRef) (σ σ' : State Unit) : Prop where
  sk : Sk σ σ'
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ o o', σ.kheap p = some o ∧ σ'.kheap p = some o' ∧ RSChg t r σ.curSc p o o'

theorem RSFr.refl (t r : ObjRef) (σ : State Unit) : RSFr t r σ σ := ⟨Sk.refl σ, fun _ => Or.inl rfl⟩

theorem RSFr.trans {t r : ObjRef} {σ1 σ2 σ3 : State Unit} (h1 : RSFr t r σ1 σ2) (h2 : RSFr t r σ2 σ3) :
    RSFr t r σ1 σ3 := by
  refine ⟨h1.sk.trans h2.sk, fun p => ?_⟩
  have hc2 : σ2.curSc = σ1.curSc := h1.sk.csc
  rcases h2.kh p with e2 | ⟨o2, o3, k2, k3, c2⟩
  · rw [e2]; exact h1.kh p
  · rw [hc2] at c2
    rcases h1.kh p with e1 | ⟨o1, o2', k1, k2', c1⟩
    · exact Or.inr ⟨o2, o3, by rw [← e1]; exact k2, k3, c2⟩
    · obtain rfl := Option.some.inj (k2'.symm.trans k2)
      exact Or.inr ⟨o1, o3, k1, k3, c1.trans c2⟩

theorem RSFr.upd {t r : ObjRef} {σ : State Unit} {p : ObjRef} {o o' : KernelObject}
    (hk : σ.kheap p = some o) (hc : RSChg t r σ.curSc p o o') : RSFr t r σ (updK σ p o') := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun p' => ?_⟩
  by_cases e : p' = p
  · subst e; exact Or.inr ⟨o, o', hk, by simp [updK], hc⟩
  · exact Or.inl (by simp [updK, e])

theorem RSFr.sts (t r : ObjRef) (σ : State Unit) (u : ObjRef) : RSFr t r σ (Notif.stsAct σ u) := by
  unfold Notif.stsAct; split
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => Or.inl rfl⟩
  · exact RSFr.refl _ _ _

theorem RSFr.um (t r : ObjRef) (σ0 : State Unit) (um : Word → Word8) : RSFr t r σ0 (Endp.setUm σ0 um) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => Or.inl rfl⟩

theorem RSFr.reprog (t r : ObjRef) (σ0 : State Unit) : RSFr t r σ0 { σ0 with reprogramTimer := true } :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => Or.inl rfl⟩

/-- `t`, `KbIn`, set `Running`. -/
theorem RSFr.stsRun {t r : ObjRef} {σ : State Unit} {y : Tcb} (hk : σ.kheap t = some (.tcb y))
    (hrb : KbIn y.tcbState) :
    RSFr t r σ (stsAct (updK σ t (.tcb { y with tcbState := .running })) t) :=
  (RSFr.upd hk (Or.inl ⟨y, .running, y.tcbArch, rfl, rfl, Or.inl rfl, Or.inr ⟨rfl, hrb, Or.inr rfl⟩⟩)).trans
    (RSFr.sts _ _ _ _)

/-- `r`'s registers changed. -/
theorem RSFr.arch {t r : ObjRef} {σ : State Unit} {y : Tcb} (hk : σ.kheap r = some (.tcb y)) (ar : ArchTcb) :
    RSFr t r σ (updK σ r (.tcb { y with tcbArch := ar })) :=
  RSFr.upd hk (Or.inl ⟨y, y.tcbState, ar, rfl, rfl, Or.inr rfl, Or.inl rfl⟩)

/-! ### Per kind -/

section
variable {t r : ObjRef} {σ σ' : State Unit}

theorem RSFr.tcbF (h : RSFr t r σ σ') {p : ObjRef} {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    ∃ st ar, σ'.kheap p = some (.tcb { x with tcbState := st, tcbArch := ar }) ∧ RSTc t r p x st ar := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x.tcbState, x.tcbArch, by rw [e, hp], Or.inl rfl, Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨x', st, ar, e1, rfl, hs⟩ | ⟨_, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨st, ar, h2, hs⟩

theorem RSFr.tcbB (h : RSFr t r σ σ') {p : ObjRef} {y : Tcb} (hp : σ'.kheap p = some (.tcb y)) :
    ∃ x st ar, σ.kheap p = some (.tcb x) ∧ y = { x with tcbState := st, tcbArch := ar } ∧ RSTc t r p x st ar := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, y.tcbState, y.tcbArch, by rw [← e, hp], rfl, Or.inl rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨x, st, ar, rfl, e2, hs⟩ | ⟨_, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨x, st, ar, h1, rfl, hs⟩

/-- The other kinds kept. -/
theorem RSFr.othF (h : RSFr t r σ σ') {p : ObjRef} {o : KernelObject} (hp : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h2 : ∀ y n, o ≠ .schedContext y n) (h4 : ∀ x, o ≠ .endpoint x) :
    σ'.kheap p = some o := by
  rcases h.kh p with e | ⟨o0, o', k1, k2, hc⟩
  · rw [e, hp]
  · rw [hp] at k1; cases k1
    rcases hc with ⟨_, _, _, e1, -⟩ | ⟨_, _, _, e1, -⟩ | ⟨_, _, e1, -⟩
    · exact absurd e1 (h1 _)
    · exact absurd e1 (h2 _ _)
    · exact absurd e1 (h4 _)

theorem RSFr.othB (h : RSFr t r σ σ') {p : ObjRef} {o' : KernelObject} (hp : σ'.kheap p = some o')
    (h1 : ∀ x, o' ≠ .tcb x) (h2 : ∀ y n, o' ≠ .schedContext y n) (h4 : ∀ x, o' ≠ .endpoint x) :
    σ.kheap p = some o' := by
  rcases h.kh p with e | ⟨o, o'', k1, k2, hc⟩
  · rw [← e, hp]
  · rw [hp] at k2; cases k2
    rcases hc with ⟨_, _, _, -, e2, -⟩ | ⟨_, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩
    · exact absurd e2 (h1 _)
    · exact absurd e2 (h2 _ _)
    · exact absurd e2 (h4 _)

theorem RSFr.scF (h : RSFr t r σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ.kheap p = some (.schedContext y n)) :
    ∃ rf, σ'.kheap p = some (.schedContext { y with scRefills := rf } n) ∧ (rf = y.scRefills ∨ p ≠ σ.curSc) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y.scRefills, by rw [e, hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, e1, -⟩ | ⟨y', n', rf, e1, rfl, hne⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨rf, h2, Or.inr hne⟩

theorem RSFr.scB (h : RSFr t r σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ'.kheap p = some (.schedContext y n)) :
    ∃ y0, σ.kheap p = some (.schedContext y0 n) ∧ y = { y0 with scRefills := y.scRefills } ∧
      (y.scRefills = y0.scRefills ∨ p ≠ σ.curSc) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e, hp], rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, -, e2, -⟩ | ⟨y0, n0, rf, rfl, e2, hne⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨y0, h1, rfl, Or.inr hne⟩

/-- The current SC kept, both ways. -/
theorem RSFr.curF (h : RSFr t r σ σ') {y : SchedContext} {n : Nat} (hp : σ.kheap σ.curSc = some (.schedContext y n)) :
    σ'.kheap σ.curSc = some (.schedContext y n) := by
  obtain ⟨rf, h1, h2⟩ := h.scF hp
  rcases h2 with rfl | h2
  · exact h1
  · exact absurd rfl h2

theorem RSFr.curB (h : RSFr t r σ σ') {y : SchedContext} {n : Nat} (hp : σ'.kheap σ.curSc = some (.schedContext y n)) :
    σ.kheap σ.curSc = some (.schedContext y n) := by
  obtain ⟨y0, h1, e, h2⟩ := h.scB hp
  rcases h2 with h2 | h2
  · rw [e, h2]; exact h1
  · exact absurd rfl h2

theorem RSFr.replyF (h : RSFr t r σ σ') {p : ObjRef} {x : Reply} (hp : σ.kheap p = some (.reply x)) :
    σ'.kheap p = some (.reply x) :=
  h.othF hp (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)

theorem RSFr.replyB (h : RSFr t r σ σ') {p : ObjRef} {x : Reply} (hp : σ'.kheap p = some (.reply x)) :
    σ.kheap p = some (.reply x) :=
  h.othB hp (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)

theorem RSFr.ntfnF (h : RSFr t r σ σ') {p : ObjRef} {x : Notification} (hp : σ.kheap p = some (.notification x)) :
    σ'.kheap p = some (.notification x) :=
  h.othF hp (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)

theorem RSFr.ntfnB (h : RSFr t r σ σ') {p : ObjRef} {x : Notification} (hp : σ'.kheap p = some (.notification x)) :
    σ.kheap p = some (.notification x) :=
  h.othB hp (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)

theorem RSFr.epF (h : RSFr t r σ σ') {p : ObjRef} {x : Endpoint} (hp : σ.kheap p = some (.endpoint x)) :
    ∃ y, σ'.kheap p = some (.endpoint y) ∧ (y = x ∨ (y.epQueue.Sublist x.epQueue ∧ t ∈ x.epQueue)) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [e, hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, e1, -⟩ | ⟨_, _, _, e1, -⟩ | ⟨x', y, e1, rfl, hs, hm⟩ <;> cases e1
    exact ⟨y, h2, Or.inr ⟨hs, hm⟩⟩

theorem RSFr.epB (h : RSFr t r σ σ') {p : ObjRef} {y : Endpoint} (hp : σ'.kheap p = some (.endpoint y)) :
    ∃ x, σ.kheap p = some (.endpoint x) ∧ (y = x ∨ (y.epQueue.Sublist x.epQueue ∧ t ∈ x.epQueue)) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e, hp], Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, -, e2, -⟩ | ⟨_, _, _, -, e2, -⟩ | ⟨x, y', rfl, e2, hs, hm⟩ <;> cases e2
    exact ⟨x, h1, Or.inr ⟨hs, hm⟩⟩

/-- The objects' kinds and sizes kept, both ways. -/
theorem RSFr.kind (h : RSFr t r σ σ') (p : ObjRef) :
    (∀ o, σ.kheap p = some o → ∃ o', σ'.kheap p = some o' ∧ aType o' = aType o) ∧
    (∀ o', σ'.kheap p = some o' → ∃ o, σ.kheap p = some o ∧ aType o' = aType o) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨fun o ho => ⟨o, by rw [e, ho], rfl⟩, fun o' ho => ⟨o', by rw [← e, ho], rfl⟩⟩
  · have ha : aType o' = aType o := by
      rcases hc with ⟨x, st, ar, rfl, rfl, -⟩ | ⟨y, n, rf, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ <;> rfl
    exact ⟨fun o0 ho0 => ⟨o', h2, by rw [h1] at ho0; cases ho0; exact ha⟩,
      fun o0 ho0 => ⟨o, h1, by rw [h2] at ho0; cases ho0; exact ha⟩⟩

/-! ### What the frame keeps -/

theorem RSFr.szKeep (h : RSFr t r σ σ') : SzKeep σ σ' := fun _ y n hp => by
  obtain ⟨y0, h1, -⟩ := h.scB hp; exact ⟨y0, h1⟩

theorem RSFr.ykeep (h : RSFr t r σ σ') : YKeep σ σ' := by
  refine ⟨fun p x hp => ?_, fun p y n hp => ?_, fun p z n hp => ?_⟩
  · obtain ⟨st, ar, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩
  · obtain ⟨rf, hp', -⟩ := h.scF hp; exact ⟨_, hp', rfl⟩
  · obtain ⟨y0, h1, e, -⟩ := h.scB hp; exact ⟨y0, h1, by rw [e]⟩

theorem RSFr.mcpKeep (h : RSFr t r σ σ') : McpKeep σ σ' := fun p x hp => by
  obtain ⟨st, ar, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem RSFr.bufKeep (h : RSFr t r σ σ') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => by obtain ⟨st, ar, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem RSFr.prio (h : RSFr t r σ σ') (u : ObjRef) : prioOf σ' u = prioOf σ u := by
  unfold prioOf
  rw [tcbsOf_eq, tcbsOf_eq]
  cases hk : σ.kheap u with
  | some o =>
    cases o with
    | tcb x =>
      obtain ⟨st, ar, hk', -⟩ := h.tcbF hk
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

theorem RSFr.nsc {N C : Set U64} (h : RSFr t r σ σ') (hN : NSC N C σ) : NSC N C σ' := by
  intro n hn y p hy hp
  exact hN n hn y p (h.ntfnB hy) hp

theorem RSFr.isorted (h : RSFr t r σ σ') (hS : IpcSorted σ) : IpcSorted σ' := by
  refine ⟨fun p y hp => ?_, fun p y hp => ?_⟩
  · obtain ⟨x, hx, hc⟩ := h.epB hp
    rcases hc with rfl | ⟨hsub, -⟩
    · exact (hS.1 p y hx).congr fun u _ => h.prio u
    · exact ((hS.1 p x hx).sublist hsub).congr fun u _ => h.prio u
  · exact (hS.2 p y (h.ntfnB hp)).congr fun u _ => h.prio u

theorem RSFr.own {T C : Set U64} (h : RSFr t r σ σ') (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · obtain ⟨st, ar, hkt', -⟩ := h.tcbF hkt
    refine Or.inl ⟨u, hu, _, hkt', by rw [h.sk.csc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
    · rw [h.sk.csc] at hy
      exact hown y n (h.curB hy)
    · rw [h.sk.cons] at h0; rw [h.sk.rel] at hm; exact hnr h0 hm
  · refine Or.inr ⟨by rw [h.sk.csc]; exact hcs, fun y n hy => ?_⟩
    rw [h.sk.csc] at hy
    exact hun y n (h.curB hy)

theorem RSFr.off (h : RSFr t r σ σ') (hO : OffOK σ) : OffOK σ' := by
  intro hc y n hy ha
  rw [h.sk.cons] at hc ⊢; rw [h.sk.tm]
  rw [h.sk.csc] at hy; rw [h.sk.csc, h.sk.isc] at ha
  exact hO hc y n (h.curB hy) ha

theorem RSFr.idleOK (h : RSFr t r σ σ') (hO : IdleOK σ) : IdleOK σ' := by
  obtain ⟨x, hx, h1, h2, h3⟩ := hO
  obtain ⟨st, ar, hx', hs⟩ := h.tcbF hx
  refine ⟨{ x with tcbState := st, tcbArch := ar }, by rw [h.sk.idle]; exact hx', by rw [h.sk.isc]; exact h1, ?_,
    by rw [h.sk.idle, h.sk.rel]; exact h3⟩
  show st = _
  rw [hs.stK (by rw [h2]; rintro (⟨_, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, e⟩ | e) <;> cases e)]; exact h2

theorem RSFr.bsa (h : RSFr t r σ σ') (hB : BlockedScActive σ) : BlockedScActive σ' := by
  refine ⟨fun p z n u y hp hyt hy hq => ?_, fun p z n hp hr => ?_⟩
  · obtain ⟨x, st, ar, hx, rfl, hs⟩ := h.tcbB hy
    obtain ⟨z0, hz0, e, -⟩ := h.scB hp
    rw [e]
    exact hB.tcb p z0 n u x hz0 (by rw [e] at hyt; exact hyt) hx (hs.ipcQ hq)
  · obtain ⟨z0, hz0, e, -⟩ := h.scB hp
    rw [e]
    exact hB.replies p z0 n hz0 (by rw [e] at hr; exact hr)

theorem RSFr.curInv (h : RSFr t r σ σ') (hC : CurInv σ) : CurInv σ' := by
  obtain ⟨xt, hkt, hxs, hnb⟩ := hC.tcb
  obtain ⟨x, n, hx⟩ := hC.sc
  obtain ⟨st, ar, hkt', hs⟩ := h.tcbF hkt
  refine ⟨⟨_, by rw [h.sk.ct]; exact hkt', by rw [h.sk.csc]; exact hxs, hs.notIpc hnb⟩,
    ⟨x, n, by rw [h.sk.csc]; exact h.curF hx⟩, fun hne y m hy => ?_, by rw [h.sk.ct, h.sk.rel]; exact hC.notRel⟩
  rw [h.sk.csc, h.sk.isc] at hne; rw [h.sk.csc] at hy
  exact hC.active hne y m (h.curB hy)

theorem RSFr.curRunW (h : RSFr t r σ σ') (hR : CurRunW σ) : CurRunW σ' := by
  rcases hR with hR | e
  · refine Or.inl fun y hy => ?_
    rw [h.sk.ct] at hy
    obtain ⟨x, st, ar, hx, rfl, hs⟩ := h.tcbB hy
    show runnable st = true
    rw [hs.run (hR x hx)]; exact hR x hx
  · exact Or.inr (by rw [h.sk.ct, h.sk.idle]; exact e)

theorem RSFr.sched (h : RSFr t r σ σ') {u : ObjRef} (hs : schedulable u σ = true) : schedulable u σ' = true := by
  obtain ⟨x, scp, y, n, hk, hsc, hrun, hky, hact, hnr⟩ := schedulable_inv hs
  obtain ⟨st, ar, hk', hst⟩ := h.tcbF hk
  obtain ⟨rf, hky', -⟩ := h.scF hky
  exact schedulable_of hk' hsc (by show runnable st = true; rw [hst.run hrun]; exact hrun) hky' hact
    (by rw [h.sk.rel]; exact hnr)

theorem RSFr.kback (h : RSFr t r σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e | ⟨ko, ko'', h1, h2, hc⟩
  · exact ⟨ko', by rw [← e, ho], id, id, id, id, id, id⟩
  · rw [ho] at h2; cases h2
    rcases hc with ⟨x, st, ar, rfl, rfl, -⟩ | ⟨y, n, rf, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩
    · exact ⟨_, h1, by simp⟩
    · exact ⟨_, h1, by simp⟩
    · exact ⟨_, h1, by simp⟩

theorem RSFr.ksz (h : RSFr t r σ σ') : KSz σ σ' := fun o ko' ho => by
  obtain ⟨ko, h1, e⟩ := (h.kind o).2 ko' ho
  exact ⟨ko, h1, e.symm⟩

theorem RSFr.ksub (h : RSFr t r σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun rr cs hc hw => ⟨cs, ?_, hw⟩, fun u hu => ?_, fun hn => ?_⟩
  · exact h.othB hc (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
  · obtain ⟨x, -, -, hx, -⟩ := h.tcbB hu; exact ⟨x, hx⟩
  · rcases h.kh o with e | ⟨ko, ko', h1, -, -⟩
    · rw [e]; exact hn
    · rw [hn] at h1; cases h1

/-- What `CallRel` reads of the spec: the SCs' call stacks (and sizes), the
replies, the SCs back. -/
theorem RSFr.callKeep (h : RSFr t r σ σ') :
    (∀ q y n, σ.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
    (∀ q x, σ.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
    (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n)) :=
  ⟨fun q y n hq => by obtain ⟨rf, h1, -⟩ := h.scF hq; exact ⟨_, h1, rfl⟩,
    fun q x hq => ⟨x, h.replyF hq, rfl⟩, fun p x n hp => by obtain ⟨y0, h1, -⟩ := h.scB hp; exact ⟨y0, h1⟩⟩

/-- No reply bound to a receiver gained (`ScRecvLinks`' `KhRB`). -/
theorem RSFr.khrb (h : RSFr t r σ σ') : KhRB σ σ' :=
  KhRB.of_kh h.kh fun p o o' hc => by
    rcases hc with ⟨x, st, ar, rfl, rfl, hs⟩ | ⟨y, n, rf, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩
    · refine ObjRB.tcb ?_
      rcases hs.2 with e | ⟨-, -, e | e⟩
      · exact Or.inl e
      · rw [e]; exact Or.inr rfl
      · rw [e]; exact Or.inr rfl
    · exact ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)
    · exact ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)

end


/-- **`Inv` across a change of one SC's refills** (the explicit outcome of
`refill_unblock_check`, ScInvU's `unblock_result`; `Inv.unblock`'s argument
with the outcome given instead of the spec's run, for a state where the
check did not run but the same SC update applies). -/
theorem Inv.scRef {σ : State Unit} (h : Inv σ) {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ []) {z : SchedContext}
    (hzR : RefOK y → RefOK z) (hzt : (refillHd z).rTime = σ.curTime) (hzy : z = { y with scRefills := z.scRefills })
    (hzne : z.scRefills ≠ []) (hper : y.scPeriod ≠ 0)
    (hnr' : ∀ u ∈ σ.releaseQueue, ∀ x, σ.kheap u = some (.tcb x) → x.tcbSchedContext ≠ some p) :
    Inv (updSc { σ with reprogramTimer := true } p z n) := by
  have hzper : z.scPeriod = y.scPeriod := by rw [hzy]
  have hkp : ∀ q, q ≠ p → (updSc { σ with reprogramTimer := true } p z n).kheap q = σ.kheap q := fun q hq => by
    simp [updK, hq]
  have hkz : (updSc { σ with reprogramTimer := true } p z n).kheap p = some (.schedContext z n) := by simp [updK]
  have hzact : scActive z = scActive y := by rw [hzy]
  have htcb : ∀ u x, (updSc { σ with reprogramTimer := true } p z n).kheap u = some (.tcb x) →
      σ.kheap u = some (.tcb x) := fun u x hx => by
    by_cases e : u = p
    · subst e; rw [hkz] at hx; cases hx
    · rw [hkp u e] at hx; exact hx
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u x hx hc => ?_, fun q w m hw => ?_,
    fun u x q hx hq => ?_, fun q x q' hx hq => ?_, fun q w m hw => ?_, fun q w m hw => ?_⟩
  · have h0 := h.rq d q u hu
    have : u ≠ p := by obtain ⟨x, -, -, -, h1, -⟩ := h0; rintro rfl; rw [hk] at h1; cases h1
    exact RqOK.upd h0 hkp (fun y' n' h => by rw [hk] at h; cases h; exact ⟨z, hkz, hzact⟩) this
  · obtain ⟨x, scp, w, m, h1, h2, h3, h4, h5⟩ := h.rel u hu
    have hup : u ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    have hsp : scp ≠ p := fun e => hnr' u hu x h1 (e ▸ h2)
    exact ⟨x, scp, w, m, by rw [hkp u hup]; exact h1, h2, h3, by rw [hkp scp hsp]; exact h4, h5⟩
  · show σ.releaseQueue.Pairwise _
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, h5⟩ := h.rel a ha
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, g5⟩ := h.rel b hb
    have nea := h.ne _ _ _ h4 h5
    have neb := h.ne _ _ _ g4 g5
    have hap : a ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    have hbp : b ≠ p := by rintro rfl; rw [hk] at g1; cases g1
    have hpa : pa ≠ p := fun e => hnr' a ha xa h1 (e ▸ h2)
    have hpb : pb ≠ p := fun e => hnr' b hb xb g1 (e ▸ g2)
    rw [specRt_eq (by rw [hkp a hap]; exact h1) h2 (by rw [hkp pa hpa]; exact h4) nea,
      specRt_eq (by rw [hkp b hbp]; exact g1) g2 (by rw [hkp pb hpb]; exact g4) neb]
    rw [specRt_eq h1 h2 h4 nea, specRt_eq g1 g2 g4 neb] at hab
    exact hab
  · have hx0 := htcb u x hx
    intro x' scp w m h1 h2 h3 h4 h5
    rw [hx] at h1; cases h1
    by_cases e : scp = p
    · subst e
      rw [hkz] at h3; cases h3
      exact ⟨ready_now _ _ hzt, sufficient_of_refOK (hzR (h.refills _ y n hk (hzact ▸ h4) hper))⟩
    · rw [hkp scp e] at h3
      exact h.rd u x hx0 hc x scp w m hx0 h2 h3 h4 h5
  · by_cases e : q = p
    · subst e; rw [hkz] at hw; cases hw; intro ha _; exact hzR (h.refills _ y n hk (hzact ▸ ha) hper)
    · rw [hkp q e] at hw; exact h.refills q w m hw
  · obtain ⟨w, m, h1, h2⟩ := h.back u x q (htcb u x hx) hq
    by_cases e : q = p
    · subst e; rw [hk] at h1; cases h1
      exact ⟨z, n, hkz, by rw [hzy]; exact h2⟩
    · exact ⟨w, m, by rw [hkp q e]; exact h1, h2⟩
  · have hx0 : σ.kheap q = some (.notification x) := by
      by_cases e : q = p
      · subst e; rw [hkz] at hx; cases hx
      · rw [hkp q e] at hx; exact hx
    obtain ⟨w, m, h1⟩ := h.ntfnSc q x q' hx0 hq
    by_cases e : q' = p
    · subst e; exact ⟨z, n, hkz⟩
    · exact ⟨w, m, by rw [hkp q' e]; exact h1⟩
  · by_cases e : q = p
    · subst e; rw [hkz] at hw; cases hw; exact fun _ => hzne
    · rw [hkp q e] at hw; exact h.ne q w m hw
  · by_cases e : q = p
    · subst e; rw [hkz] at hw; cases hw; intro _ hp0; exact absurd (hzper.symm.trans hp0) hper
    · rw [hkp q e] at hw; exact h.rr q w m hw

end Spec

end

end Fl4Proofs.P3.Sched
