/-
P3 (DESIGN.md §9), TCB invocations: **the spec's frame of `set_priority t`**
(spec side only), toward the SetPriority label of the Thread cap at `J`
(XTopJointTcbPrio).

`set_priority t pr` changes `t`'s priority; a runnable thread queued or
current is requeued (the ready queues) and a reschedule asked; a thread
blocked on an endpoint or a notification has that object's queue reordered.

* `PChg t p o o'`: `t`'s TCB to another priority; an endpoint holding `t` to
  another endpoint; a notification holding `t` to another one with its SC and
  bound thread kept.
* `PFr t σ σ'`: the frame (`Sk`, the scheduler action kept or
  `chooseNewThread`, `PChg` objectwise); `PFr.refl`, `trans`, `upd`, `setQ`,
  `cn`; the per-kind lemmas and what it keeps (as IpcCancelFr's `KFr`:
  `szKeep`, `ykeep`, `mcpKeep`, `bufKeep`, `nsc`, `own`, `off`, `idleOK`,
  `bsa`, `curInv`, `curRunW`, `sched`, `kback`, `ksz`, `ksub`, `callKeep`).
* `setPriority_pfr`: every outcome of `set_priority` with no switch pending
  is in `PFr` (`BlkQ` for the reorders, `SchedValid` for `t` in its queue).
* `setPriority_invC`: `Inv` after `set_priority`, the target possibly the
  current thread (TcbSpecInv's `setPriority_inv` with the requeued current
  thread's facts from its active SC).
-/
import Fl4Proofs.P3.IpcCancelFr
import Fl4Proofs.P3.TcbSpecInv
import Fl4Proofs.P3.ScIpcSorted
import Fl4Proofs.P3.IpcSetPrio
import Fl4Proofs.P3.IpcFinEpInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- **One object's change** (module docstring). -/
def PChg (t p : ObjRef) (o o' : KernelObject) : Prop :=
  (∃ x pr, o = .tcb x ∧ o' = .tcb { x with tcbPriority := pr } ∧ p = t) ∨
  (∃ x y, o = .endpoint x ∧ o' = .endpoint y ∧ t ∈ x.epQueue) ∨
  (∃ x y, o = .notification x ∧ o' = .notification y ∧ y.ntfnSc = x.ntfnSc ∧ y.ntfnBoundTcb = x.ntfnBoundTcb ∧
    t ∈ ntfnQueueOf x)

theorem PChg.trans {t p : ObjRef} {o1 o2 o3 : KernelObject} (h1 : PChg t p o1 o2) (h2 : PChg t p o2 o3) :
    PChg t p o1 o3 := by
  rcases h1 with ⟨x, pr, rfl, rfl, hp⟩ | ⟨x, y, rfl, rfl, hm⟩ | ⟨x, y, rfl, rfl, e1, e2, hm⟩
  · rcases h2 with ⟨x2, pr2, e, rfl, -⟩ | ⟨_, _, e, -⟩ | ⟨_, _, e, -⟩ <;> cases e
    exact Or.inl ⟨x, pr2, rfl, rfl, hp⟩
  · rcases h2 with ⟨_, _, e, -⟩ | ⟨x2, z, e, rfl, -⟩ | ⟨_, _, e, -⟩ <;> cases e
    exact Or.inr (Or.inl ⟨x, z, rfl, rfl, hm⟩)
  · rcases h2 with ⟨_, _, e, -⟩ | ⟨_, _, e, -⟩ | ⟨x2, z, e, rfl, f1, f2, -⟩ <;> cases e
    exact Or.inr (Or.inr ⟨x, z, rfl, rfl, f1.trans e1, f2.trans e2, hm⟩)

/-- **The spec's frame of `set_priority t`** (module docstring). -/
structure PFr (t : ObjRef) (σ σ' : State Unit) : Prop where
  sk : Sk σ σ'
  act : σ'.schedulerAction = σ.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ o o', σ.kheap p = some o ∧ σ'.kheap p = some o' ∧ PChg t p o o'

theorem PFr.refl (t : ObjRef) (σ : State Unit) : PFr t σ σ := ⟨Sk.refl σ, Or.inl rfl, fun _ => Or.inl rfl⟩

theorem PFr.trans {t : ObjRef} {σ1 σ2 σ3 : State Unit} (h1 : PFr t σ1 σ2) (h2 : PFr t σ2 σ3) : PFr t σ1 σ3 := by
  refine ⟨h1.sk.trans h2.sk, ?_, fun p => ?_⟩
  · rcases h2.act with e2 | e2
    · rw [e2]; exact h1.act
    · exact Or.inr e2
  rcases h2.kh p with e2 | ⟨o2, o3, k2, k3, c2⟩
  · rw [e2]; exact h1.kh p
  · rcases h1.kh p with e1 | ⟨o1, o2', k1, k2', c1⟩
    · exact Or.inr ⟨o2, o3, by rw [← e1]; exact k2, k3, c2⟩
    · obtain rfl := Option.some.inj (k2'.symm.trans k2)
      exact Or.inr ⟨o1, o3, k1, k3, c1.trans c2⟩

theorem PFr.upd {t : ObjRef} {σ : State Unit} {p : ObjRef} {o o' : KernelObject}
    (hk : σ.kheap p = some o) (hc : PChg t p o o') : PFr t σ (updK σ p o') := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, Or.inl rfl, fun p' => ?_⟩
  by_cases e : p' = p
  · subst e; exact Or.inr ⟨o, o', hk, by simp [updK], hc⟩
  · exact Or.inl (by simp [updK, e])

theorem PFr.setq (t : ObjRef) (σ : State Unit) (d : Domain) (p : Priority) (q : List ObjRef) :
    PFr t σ (setQ σ d p q) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, Or.inl rfl, fun _ => Or.inl rfl⟩

theorem PFr.cn (t : ObjRef) (σ : State Unit) : PFr t σ { σ with schedulerAction := .chooseNewThread } :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, Or.inr rfl, fun _ => Or.inl rfl⟩

/-! ### Per kind -/

section
variable {t : ObjRef} {σ σ' : State Unit}

theorem PFr.tcbF (h : PFr t σ σ') {p : ObjRef} {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    ∃ pr, σ'.kheap p = some (.tcb { x with tcbPriority := pr }) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x.tcbPriority, by rw [e, hp]⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨x', pr, e1, rfl, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨pr, h2⟩

theorem PFr.tcbB (h : PFr t σ σ') {p : ObjRef} {y : Tcb} (hp : σ'.kheap p = some (.tcb y)) :
    ∃ x pr, σ.kheap p = some (.tcb x) ∧ y = { x with tcbPriority := pr } := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, y.tcbPriority, by rw [← e, hp], rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨x, pr, rfl, e2, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨x, pr, h1, rfl⟩

/-- The other kinds kept. -/
theorem PFr.othF (h : PFr t σ σ') {p : ObjRef} {o : KernelObject} (hp : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h3 : ∀ x, o ≠ .notification x) (h4 : ∀ x, o ≠ .endpoint x) :
    σ'.kheap p = some o := by
  rcases h.kh p with e | ⟨o0, o', k1, k2, hc⟩
  · rw [e, hp]
  · rw [hp] at k1; cases k1
    rcases hc with ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩
    · exact absurd e1 (h1 _)
    · exact absurd e1 (h4 _)
    · exact absurd e1 (h3 _)

theorem PFr.othB (h : PFr t σ σ') {p : ObjRef} {o' : KernelObject} (hp : σ'.kheap p = some o')
    (h1 : ∀ x, o' ≠ .tcb x) (h3 : ∀ x, o' ≠ .notification x) (h4 : ∀ x, o' ≠ .endpoint x) :
    σ.kheap p = some o' := by
  rcases h.kh p with e | ⟨o, o'', k1, k2, hc⟩
  · rw [← e, hp]
  · rw [hp] at k2; cases k2
    rcases hc with ⟨_, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩
    · exact absurd e2 (h1 _)
    · exact absurd e2 (h4 _)
    · exact absurd e2 (h3 _)

theorem PFr.scF (h : PFr t σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ.kheap p = some (.schedContext y n)) : σ'.kheap p = some (.schedContext y n) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem PFr.scB (h : PFr t σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ'.kheap p = some (.schedContext y n)) : σ.kheap p = some (.schedContext y n) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem PFr.replyF (h : PFr t σ σ') {p : ObjRef} {x : Reply} (hp : σ.kheap p = some (.reply x)) :
    σ'.kheap p = some (.reply x) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem PFr.replyB (h : PFr t σ σ') {p : ObjRef} {x : Reply} (hp : σ'.kheap p = some (.reply x)) :
    σ.kheap p = some (.reply x) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem PFr.ntfnB (h : PFr t σ σ') {p : ObjRef} {y : Notification} (hp : σ'.kheap p = some (.notification y)) :
    ∃ x, σ.kheap p = some (.notification x) ∧ y.ntfnSc = x.ntfnSc ∧ y.ntfnBoundTcb = x.ntfnBoundTcb ∧
      (y = x ∨ t ∈ ntfnQueueOf x) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e, hp], rfl, rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨x, y', rfl, e2, f1, f2, hm⟩ <;> cases e2
    exact ⟨x, h1, f1, f2, Or.inr hm⟩

theorem PFr.ntfnF (h : PFr t σ σ') {p : ObjRef} {x : Notification} (hp : σ.kheap p = some (.notification x)) :
    ∃ y, σ'.kheap p = some (.notification y) ∧ y.ntfnSc = x.ntfnSc ∧ y.ntfnBoundTcb = x.ntfnBoundTcb ∧
      (y = x ∨ t ∈ ntfnQueueOf x) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [e, hp], rfl, rfl, Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨x', y, e1, rfl, f1, f2, hm⟩ <;> cases e1
    exact ⟨y, h2, f1, f2, Or.inr hm⟩

theorem PFr.epF (h : PFr t σ σ') {p : ObjRef} {x : Endpoint} (hp : σ.kheap p = some (.endpoint x)) :
    ∃ y, σ'.kheap p = some (.endpoint y) ∧ (y = x ∨ t ∈ x.epQueue) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [e, hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, e1, -⟩ | ⟨x', y, e1, rfl, hm⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨y, h2, Or.inr hm⟩

theorem PFr.epB (h : PFr t σ σ') {p : ObjRef} {y : Endpoint} (hp : σ'.kheap p = some (.endpoint y)) :
    ∃ x, σ.kheap p = some (.endpoint x) ∧ (y = x ∨ t ∈ x.epQueue) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← e, hp], Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, -, e2, -⟩ | ⟨x, y', rfl, e2, hm⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨x, h1, Or.inr hm⟩

/-- The objects' kinds kept, both ways. -/
theorem PFr.kind (h : PFr t σ σ') (p : ObjRef) :
    (∀ o, σ.kheap p = some o → ∃ o', σ'.kheap p = some o' ∧ aType o' = aType o) ∧
    (∀ o', σ'.kheap p = some o' → ∃ o, σ.kheap p = some o ∧ aType o' = aType o) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨fun o ho => ⟨o, by rw [e, ho], rfl⟩, fun o' ho => ⟨o', by rw [← e, ho], rfl⟩⟩
  · have ha : aType o' = aType o := by
      rcases hc with ⟨x, pr, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ <;> rfl
    exact ⟨fun o0 ho0 => ⟨o', h2, by rw [h1] at ho0; cases ho0; exact ha⟩,
      fun o0 ho0 => ⟨o, h1, by rw [h2] at ho0; cases ho0; exact ha⟩⟩

/-! ### What the frame keeps -/

theorem PFr.szKeep (h : PFr t σ σ') : SzKeep σ σ' := fun _ y n hp => ⟨y, h.scB hp⟩

theorem PFr.ykeep (h : PFr t σ σ') : YKeep σ σ' := by
  refine ⟨fun p x hp => ?_, fun p y n hp => ⟨y, h.scF hp, rfl⟩, fun p z n hp => ⟨z, h.scB hp, rfl⟩⟩
  obtain ⟨pr, hp'⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem PFr.mcpKeep (h : PFr t σ σ') : McpKeep σ σ' := fun p x hp => by
  obtain ⟨pr, hp'⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem PFr.bufKeep (h : PFr t σ σ') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => by obtain ⟨pr, hp'⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem PFr.nsc {N C : Set U64} (h : PFr t σ σ') (hN : NSC N C σ) : NSC N C σ' := by
  intro n hn y p hy hp
  obtain ⟨x, hx, hs, -, -⟩ := h.ntfnB hy
  exact hN n hn x p hx (hs ▸ hp)

theorem PFr.own {T C : Set U64} (h : PFr t σ σ') (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · obtain ⟨pr, hkt'⟩ := h.tcbF hkt
    refine Or.inl ⟨u, hu, _, hkt', by rw [h.sk.csc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
    · rw [h.sk.csc] at hy
      exact hown y n (h.scB hy)
    · rw [h.sk.cons] at h0; rw [h.sk.rel] at hm; exact hnr h0 hm
  · refine Or.inr ⟨by rw [h.sk.csc]; exact hcs, fun y n hy => ?_⟩
    rw [h.sk.csc] at hy
    exact hun y n (h.scB hy)

theorem PFr.off (h : PFr t σ σ') (hO : OffOK σ) : OffOK σ' := by
  intro hc y n hy ha
  rw [h.sk.cons] at hc ⊢; rw [h.sk.tm]
  rw [h.sk.csc] at hy; rw [h.sk.csc, h.sk.isc] at ha
  exact hO hc y n (h.scB hy) ha

theorem PFr.idleOK (h : PFr t σ σ') (hO : IdleOK σ) : IdleOK σ' := by
  obtain ⟨x, hx, h1, h2, h3⟩ := hO
  obtain ⟨pr, hx'⟩ := h.tcbF hx
  exact ⟨{ x with tcbPriority := pr }, by rw [h.sk.idle]; exact hx', by rw [h.sk.isc]; exact h1, h2, by rw [h.sk.idle, h.sk.rel]; exact h3⟩

theorem PFr.bsa (h : PFr t σ σ') (hB : BlockedScActive σ) : BlockedScActive σ' := by
  refine ⟨fun p z n u y hp hyt hy hq => ?_, fun p z n hp hr => hB.replies p z n (h.scB hp) hr⟩
  obtain ⟨x, pr, hx, rfl⟩ := h.tcbB hy
  exact hB.tcb p z n u x (h.scB hp) hyt hx hq

theorem PFr.curInv (h : PFr t σ σ') (hC : CurInv σ) : CurInv σ' := by
  obtain ⟨xt, hkt, hxs, hnb⟩ := hC.tcb
  obtain ⟨x, n, hx⟩ := hC.sc
  obtain ⟨pr, hkt'⟩ := h.tcbF hkt
  refine ⟨⟨{ xt with tcbPriority := pr }, by rw [h.sk.ct]; exact hkt', by rw [h.sk.csc]; exact hxs, hnb⟩,
    ⟨x, n, by rw [h.sk.csc]; exact h.scF hx⟩, fun hne y m hy => ?_, by rw [h.sk.ct, h.sk.rel]; exact hC.notRel⟩
  rw [h.sk.csc, h.sk.isc] at hne; rw [h.sk.csc] at hy
  exact hC.active hne y m (h.scB hy)

theorem PFr.curRunW (h : PFr t σ σ') (hR : CurRunW σ) : CurRunW σ' := by
  rcases hR with hR | e
  · refine Or.inl fun y hy => ?_
    rw [h.sk.ct] at hy
    obtain ⟨x, pr, hx, rfl⟩ := h.tcbB hy
    exact hR x hx
  · exact Or.inr (by rw [h.sk.ct, h.sk.idle]; exact e)

theorem PFr.sched (h : PFr t σ σ') {u : ObjRef} (hs : schedulable u σ = true) : schedulable u σ' = true := by
  obtain ⟨x, scp, y, n, hk, hsc, hrun, hky, hact, hnr⟩ := schedulable_inv hs
  obtain ⟨pr, hk'⟩ := h.tcbF hk
  exact schedulable_of hk' hsc hrun (h.scF hky) hact (by rw [h.sk.rel]; exact hnr)

theorem PFr.kback (h : PFr t σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e | ⟨ko, ko'', h1, h2, hc⟩
  · exact ⟨ko', by rw [← e, ho], id, id, id, id, id, id⟩
  · rw [ho] at h2; cases h2
    rcases hc with ⟨x, pr, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩
    · exact ⟨_, h1, by simp⟩
    · exact ⟨_, h1, by simp⟩
    · exact ⟨_, h1, by simp⟩

theorem PFr.ksz (h : PFr t σ σ') : KSz σ σ' := fun o ko' ho => by
  obtain ⟨ko, h1, e⟩ := (h.kind o).2 ko' ho
  exact ⟨ko, h1, e.symm⟩

theorem PFr.ksub (h : PFr t σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun rr cs hc hw => ⟨cs, ?_, hw⟩, fun u hu => ?_, fun hn => ?_⟩
  · exact h.othB hc (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)
  · obtain ⟨x, -, hx, -⟩ := h.tcbB hu; exact ⟨x, hx⟩
  · rcases h.kh o with e | ⟨ko, ko', h1, -, -⟩
    · rw [e]; exact hn
    · rw [hn] at h1; cases h1

/-- What `CallRel` reads of the spec (as `KFr.callKeep`). -/
theorem PFr.callKeep (h : PFr t σ σ') :
    (∀ q y n, σ.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
    (∀ q x, σ.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
    (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n)) :=
  ⟨fun q y n hq => ⟨y, h.scF hq, rfl⟩, fun q x hq => ⟨x, h.replyF hq, rfl⟩, fun p x n hp => ⟨x, h.scB hp⟩⟩

/-- `ActIdle` after (the action kept or `chooseNewThread`). -/
theorem PFr.actIdle (h : PFr t σ σ') (hA : ActIdle σ) : ActIdle σ' := by
  refine ⟨fun u hu => ?_, h.idleOK hA.2⟩
  rcases h.act with e | e
  · exact h.sched (hA.1 u (by rw [← e]; exact hu))
  · rw [e] at hu; cases hu

theorem PFr.cur (h : PFr t σ σ') (hR : σ.schedulerAction = .chooseNewThread ∨ CurInv σ) :
    σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
  rcases h.act with e | e
  · exact hR.imp (fun e0 => by rw [e, e0]) h.curInv
  · exact Or.inl e

theorem PFr.curRunM (h : PFr t σ σ') (hR : CurRunM σ) : CurRunM σ' := by
  rcases h.act with e | e
  · exact hR.imp (fun e0 => by rw [e]; exact e0) h.curRunW
  · exact Or.inl (by rw [e]; intro h'; cases h')

end

/-! ### The spec's `set_priority` -/

theorem ntfnBlocked_some {ts : ThreadState} {n : ObjRef} (h : ntfnBlocked ts = some n) :
    ts = .blockedOnNotification n := by
  cases ts <;> simp [ntfnBlocked] at h
  subst h; rfl

/-- `rescheduleRequired` with no switch pending, after a `PFr` step. -/
theorem pfr_resched {t : ObjRef} {σ σc : State Unit} (h : PFr t σ σc)
    (hna : ∀ u, σc.schedulerAction ≠ .switchThread u) :
    ∀ y ∈ (rescheduleRequired (Z := Unit) σc).1, PFr t σ y.2 := by
  rw [rescheduleRequired_noswitch hna]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact h.trans (PFr.cn t σc)

set_option maxHeartbeats 4000000 in
/-- **Every outcome of `set_priority` is a `PFr` step** (module docstring),
with no switch pending, `BlkQ` of the target and `SchedValid` (the target in
the queue of the object it is blocked on). -/
theorem setPriority_pfr {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (pr : Priority)
    (hna : ∀ u, σ.schedulerAction ≠ .switchThread u) (hQ : BlkQ σ t x.tcbState) (hSV : SchedValid σ) :
    ∀ y ∈ (setPriority (Z := Unit) t pr σ).1, PFr t σ y.2 := by
  have hts : ∀ σ0 : State Unit, σ0.kheap t = some (.tcb x) →
      threadSetPriority (Z := Unit) t pr σ0 =
        ({((), Notif.updK σ0 t (.tcb { x with tcbPriority := pr }))}, False) := fun σ0 h0 =>
    Notif.threadSet_eq _ h0
  have hP0 : ∀ σ0 : State Unit, σ0.kheap t = some (.tcb x) →
      PFr t σ0 (Notif.updK σ0 t (.tcb { x with tcbPriority := pr })) :=
    fun σ0 h0 => PFr.upd h0 (Or.inl ⟨x, pr, rfl, rfl, rfl⟩)
  unfold setPriority getThreadState
  rw [nd_bind_one (Notif.threadGet_eq _ hk)]
  split
  · rw [nd_bind_one (Notif.threadGet_eq _ hk), nd_bind_one (Notif.threadGet_eq _ hk),
      nd_bind_one (getTcbQueue_eq _ _ _), Notif.nd_gets_bind]
    split
    · rw [nd_bind_one (tcbSchedAction_gen hk _)]
      rw [nd_bind_one (hts (setQ σ x.tcbDomain x.tcbPriority _) hk)]
      rw [nd_bind_one (tcbSchedAction_gen (x := { x with tcbPriority := pr })
        (by simp [Notif.updK, setQ]) _)]
      exact pfr_resched (((PFr.setq t σ _ _ _).trans (hP0 _ hk)).trans (PFr.setq t _ _ _ _)) hna
    · rw [hts _ hk]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact hP0 σ hk
  · rw [nd_bind_one (hts _ hk)]
    obtain ⟨hE, hN⟩ := hQ
    set σb := Notif.updK σ t (.tcb { x with tcbPriority := pr }) with hσb
    have hkb : σb.kheap t = some (.tcb { x with tcbPriority := pr }) := by simp [hσb, Notif.updK]
    have hkb' : ∀ u, u ≠ t → σb.kheap u = σ.kheap u := fun u hu => by
      simp [hσb, Notif.updK, Function.update_of_ne hu]
    have hPb : PFr t σ σb := hP0 σ hk
    -- the reordered endpoint queue
    have hep : ∀ e, epBlocked x.tcbState = some e → ∃ σr, reorderEp (Z := Unit) e t σb = ({((), σr)}, False) ∧
        PFr t σ σr := by
      intro e he
      obtain ⟨ep, hke, hni, hne, hq⟩ := hE e he
      have het : e ≠ t := by rintro rfl; rw [hk] at hke; cases hke
      have hke' : σb.kheap e = some (.endpoint ep) := by rw [hkb' e het]; exact hke
      have hq' := removeAll_tcbs (σ := σb) (t := t) (qs := ep.epQueue)
        (fun u hu hut => by rw [hkb' u hut]; exact hq u hu hut)
      have hin : t ∈ ep.epQueue := by
        rcases epBlocked_some he with ⟨d, hst⟩ | ⟨ro, d, hst⟩
        · obtain ⟨xe, hke2, hm⟩ := hSV.sendQ t x e d hk hst
          rw [hke] at hke2; cases hke2; exact hm
        · obtain ⟨xe, hke2, hm⟩ := hSV.recvQ t x e ro d hk hst
          rw [hke] at hke2; cases hke2; exact hm
      refine ⟨_, by
        unfold reorderEp
        rw [nd_bind_one (Endp.getEndpoint_eq hke'), nd_bind_one (assert_one hni _), Notif.nd_pure_bind',
          nd_bind_one (assert_one hne _), Notif.nd_pure_bind', nd_bind_one (Notif.tcbAppend_eq hkb _ _ hq')]
        exact Endp.setEndpoint_eq _ hke', ?_⟩
      exact hPb.trans (PFr.upd hke' (Or.inr (Or.inl ⟨ep, _, rfl, rfl, hin⟩)))
    -- the reordered notification queue
    have hnt : ∀ n, ntfnBlocked x.tcbState = some n → ∃ σr, reorderNtfn (Z := Unit) n t σb = ({((), σr)}, False) ∧
        PFr t σ σr := by
      intro n hn
      obtain ⟨xn, hkn, hw, hne, hq⟩ := hN n hn
      have hnt : n ≠ t := by rintro rfl; rw [hk] at hkn; cases hkn
      have hkn' : σb.kheap n = some (.notification xn) := by rw [hkb' n hnt]; exact hkn
      have hq' := removeAll_tcbs (σ := σb) (t := t) (qs := ntfnQueueOf xn)
        (fun u hu hut => by rw [hkb' u hut]; exact hq u hu hut)
      have hin : t ∈ ntfnQueueOf xn := by
        obtain ⟨xn2, hkn2, hm⟩ := hSV.ntfnW t x n hk (ntfnBlocked_some hn)
        rw [hkn] at hkn2; cases hkn2; exact hm
      refine ⟨_, by
        unfold reorderNtfn
        rw [nd_bind_one (Notif.getNotification_eq hkn'), nd_bind_one (assert_one hw _), Notif.nd_pure_bind',
          nd_bind_one (assert_one hne _), Notif.nd_pure_bind', nd_bind_one (Notif.tcbAppend_eq hkb _ _ hq')]
        exact Notif.setNotification_eq _ hkn', ?_⟩
      exact hPb.trans (PFr.upd hkn' (Or.inr (Or.inr ⟨xn, _, rfl, rfl, rfl, rfl, hin⟩)))
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
         exact hPb)

/-- **`BlkQ` from `SchedValid`**: a thread blocked on an endpoint or a
notification is in its queue (`sendQ`, `recvQ`, `ntfnW`), whose members are
TCBs (`epQ`, `ntfnQ`). -/
theorem blkQ_of_sv {σ : State Unit} (hSV : SchedValid σ) {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) :
    BlkQ σ t x.tcbState := by
  refine ⟨fun e he => ?_, fun n hn => ?_⟩
  · have hin : ∃ ep, σ.kheap e = some (.endpoint ep) ∧ t ∈ ep.epQueue := by
      rcases epBlocked_some he with ⟨d, hst⟩ | ⟨ro, d, hst⟩
      · exact hSV.sendQ t x e d hk hst
      · exact hSV.recvQ t x e ro d hk hst
    obtain ⟨ep, hke, hm⟩ := hin
    refine ⟨ep, hke, fun h => by rw [h] at hm; simp [Fl4Spec.Endpoint.epQueue] at hm, List.ne_nil_of_mem hm,
      fun u hu _ => ?_⟩
    obtain ⟨xu, hxu, -⟩ := (hSV.epQ e ep hke).2 u hu
    exact ⟨xu, hxu⟩
  · obtain ⟨xn, hkn, hm⟩ := hSV.ntfnW t x n hk (ntfnBlocked_some hn)
    refine ⟨xn, hkn, ?_, List.ne_nil_of_mem hm, fun u hu _ => ?_⟩
    · have hm' : t ∈ xn.ntfnObj.ntfnQueue := hm
      cases h : xn.ntfnObj with
      | idleNtfn => rw [h] at hm'; simp [Fl4Spec.Ntfn.ntfnQueue] at hm'
      | activeNtfn b => rw [h] at hm'; simp [Fl4Spec.Ntfn.ntfnQueue] at hm'
      | waitingNtfn q => rfl
    · obtain ⟨xu, hxu, -⟩ := (hSV.ntfnQ n xn hkn).2 u hu
      exact ⟨xu, hxu⟩

set_option maxHeartbeats 4000000 in
/-- **`Inv` after `set_priority`, the target possibly the current thread**
(`setPriority_inv` with the requeued current thread's facts: its SC bound and
active, `hcs`; l4v `setPriority`'s `tcbSchedEnqueue` of the current thread). -/
theorem setPriority_invC {σ σ' : State Unit} (h : Inv σ) {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hcs : t = σ.curThread → ∃ scp y n, x.tcbSchedContext = some scp ∧ σ.kheap scp = some (.schedContext y n) ∧
      scActive y = true) (pr : Priority) (hm : ((), σ') ∈ (setPriority (Z := Unit) t pr σ).1) :
    Inv σ' ∧ ∀ p, OIK (p ≠ t) (σ.kheap p) (σ'.kheap p) := by
  have hts : ∀ σ0 : State Unit, σ0.kheap t = some (.tcb x) →
      threadSetPriority (Z := Unit) t pr σ0 =
        ({((), updK σ0 t (.tcb { x with tcbPriority := pr }))}, False) := fun σ0 h0 =>
    threadSet_eq _ h0
  cases hr : runnable x.tcbState
  · rw [Ipc.setPriority_blk hk hr pr] at hm
    have hik : ∀ u, IK u σ σ' := fun u => ikm_setPriority_blk (t := u) t pr x.tcbState σ _ hm
    exact ⟨h.ikKeep (hik t) (IK.st_of_all hik), (hik t).1⟩
  rw [Ipc.setPriority_run hk hr pr] at hm
  split_ifs at hm with hq
  · rw [nd_bind_one (tcbSchedAction_gen hk _)] at hm
    set σa := setQ σ x.tcbDomain x.tcbPriority (tcbSchedDequeue t (σ.readyQueues x.tcbDomain x.tcbPriority))
      with hσa
    have hka : σa.kheap t = some (.tcb x) := hk
    have hIa : Inv σa := h.qchange (qchange_dequeue hk)
    rw [nd_bind_one (hts σa hka)] at hm
    set σb := updK σa t (.tcb { x with tcbPriority := pr }) with hσb
    have hkb : σb.kheap t = some (.tcb { x with tcbPriority := pr }) := by simp [hσb, updK]
    have hIb : Inv σb := hIa.prioUpd hka pr
    rw [nd_bind_one (tcbSchedAction_gen hkb _)] at hm
    set σc := setQ σb x.tcbDomain pr (tcbSchedEnqueue t (σb.readyQueues x.tcbDomain pr)) with hσc
    -- `t`'s ready-queue facts at `σb`
    have hRt : ∃ x scp y n, σb.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some scp ∧
        runnable x.tcbState = true ∧ σb.kheap scp = some (.schedContext y n) ∧ scActive y = true := by
      by_cases hq' : t ∈ σ.readyQueues x.tcbDomain x.tcbPriority
      · obtain ⟨x0, scp, y, n, h1, h2, h3, h4, h5⟩ := h.rq _ _ t hq'
        rw [hk] at h1; cases h1
        have hsc : scp ≠ t := by rintro rfl; rw [hk] at h4; cases h4
        exact ⟨_, scp, y, n, hkb, h2, h3, by simp [hσb, updK, hsc]; exact h4, h5⟩
      · obtain ⟨scp, y, n, h2, h4, h5⟩ := hcs (hq.resolve_left hq')
        have hsc : scp ≠ t := by rintro rfl; rw [hk] at h4; cases h4
        exact ⟨_, scp, y, n, hkb, h2, hr, by simp [hσb, updK, hsc]; exact h4, h5⟩
    have hIc : Inv σc := by
      refine hIb.congr' rfl (fun d p u hu => ?_) rfl rfl
      simp only [hσc, setQ] at hu
      split at hu
      · rename_i e
        obtain ⟨rfl, rfl⟩ := e
        unfold tcbSchedEnqueue at hu
        split at hu
        · rcases List.mem_cons.1 hu with rfl | hu
          · exact hRt
          · exact hIb.rq _ _ u hu
        · exact hIb.rq _ _ u hu
      · exact hIb.rq d p u hu
    obtain ⟨σd, hd, hqd⟩ := rescheduleRequired_qchange hIc.actReady
    rw [hd] at hm
    rw [show σ' = σd from (Prod.mk.inj (Set.mem_singleton_iff.1 hm)).2]
    refine ⟨hIc.qchange hqd, fun p => ?_⟩
    rw [hqd.1]
    exact (IK.updTcb (t := t) (σ := σ) (y := { x with tcbPriority := pr }) hk rfl rfl).1 p
  · rw [hts σ hk] at hm
    rw [show σ' = updK σ t (.tcb { x with tcbPriority := pr }) from (Prod.mk.inj (Set.mem_singleton_iff.1 hm)).2]
    exact ⟨h.prioUpd hk pr, (IK.updTcb (t := t) (y := { x with tcbPriority := pr }) hk rfl rfl).1⟩

/-- No reply bound to a receiver gained (`ScRecvLinks`' `KhRB`). -/
theorem PFr.khrb {t : ObjRef} {σ σ' : State Unit} (h : PFr t σ σ') : KhRB σ σ' :=
  KhRB.of_kh h.kh fun p o o' hc => by
    rcases hc with ⟨x, pr, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩
    · exact ObjRB.tcb (Or.inl rfl)
    · exact ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)
    · exact ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)

end Spec

end

end Fl4Proofs.P3.Sched
