/-
P3 (DESIGN.md §9), VSpace: **the spec's VSpace invocations change only arch
objects and caps** (spec side only), toward `JAtZ` after a native VSpace
cap's map, unmap or ASID assignment (XTopJointVsMap).

* `vsF`: the state's fields but the arch objects' contents, the CNodes'
  contents, the TCBs' caps and the machine state (every object kept as one of
  the same type, `aType`). `fv_performPageInvocation`,
  `fv_performPageTableInvocation`, `fv_performPageDirectoryInvocation`,
  `fv_performPdptInvocation`, `fv_performAsidPoolInvocation`,
  `fv_performPml4Flush`: every outcome keeps `vsF` (VsDom's `FK`, the
  leaves `set_object` of an arch object over one of the same type,
  `set_cap`, `get_cap`, `do_machine_op`).
* `VsFr σ σ'`: the frame `vsF` gives (as XTopJointFinVsSpec's `ArFr`, with
  CNodes and TCBs' caps changed as well).
* `VsFr.mid`: a `VsFr` step is an `ArFr` step (the arch objects) followed by
  a `CnStep` (the CNodes and the TCBs' caps), so the scheduler's spec
  invariants carry over by `….ar` and `….cn`.
-/
import Fl4Proofs.P3.XTopJointFinVsSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

/-- A TCB with its caps forgotten. -/
def eraseT (x : Tcb) : Tcb :=
  { x with
    tcbCtable := .nullCap
    tcbVtable := .nullCap
    tcbIpcframe := .nullCap
    tcbFaultHandler := .nullCap
    tcbTimeoutHandler := .nullCap
    tcbEpt := .nullCap }

/-- An object with its arch contents, CNode contents and TCB caps forgotten. -/
def eraseV : Option KernelObject → Option KernelObject
  | some (.archObj _) => none
  | some (.cnode r _) => some (.cnode r (fun _ => none))
  | some (.tcb x) => some (.tcb (eraseT x))
  | o => o

/-- **The fields a VSpace invocation keeps** (module docstring). -/
def vsF (σ : State Unit) :=
  ((fun p => eraseV (σ.kheap p)), (fun p => (σ.kheap p).map aType), σ.cdt, σ.isOriginalCap, σ.curThread,
    σ.idleThread, σ.consumedTime, σ.curTime, σ.curSc, σ.reprogramTimer, σ.schedulerAction, σ.domainList,
    σ.domainIndex, σ.domainStartIndex, σ.curDomain, σ.domainTime, σ.readyQueues, σ.releaseQueue,
    σ.interruptIrqNode, σ.interruptStates, σ.archState)

theorem vsF_upd {σ : State Unit} {p : ObjRef} {k o : KernelObject} (hk : σ.kheap p = some k)
    (ht : aType k = aType o) (he : eraseV (some o) = eraseV (some k)) :
    vsF { σ with kheap := Function.update σ.kheap p (some o) } = vsF σ := by
  unfold vsF
  have h1 : (fun q => eraseV (Function.update σ.kheap p (some o) q)) = fun q => eraseV (σ.kheap q) := by
    funext q
    by_cases e : q = p
    · subst e; rw [Function.update_self, hk, he]
    · rw [Function.update_of_ne e]
  have h2 : (fun q => (Function.update σ.kheap p (some o) q).map aType) = fun q => (σ.kheap q).map aType := by
    funext q
    by_cases e : q = p
    · subst e; rw [Function.update_self, hk]; simp [ht]
    · rw [Function.update_of_ne e]
  simp only [h1, h2]

/-- `set_object` of an arch object (over one of the same type). -/
theorem fv_setObjectA (p : ObjRef) (a : ArchKernelObj) : Vs.FK vsF (setObject (Z := Unit) p (.archObj a)) := by
  intro σ x hx
  obtain ⟨k, hk, hty, e⟩ := MaxK.mk_setObject_mem hx
  rw [e]
  refine vsF_upd hk hty ?_
  cases k with
  | archObj a0 => rfl
  | cnode r cs => simp only [aType] at hty; split at hty <;> cases hty
  | schedContext y n => simp only [aType] at hty; split at hty <;> cases hty
  | _ => simp [aType] at hty

theorem fv_doMachineOp {α : Type} (mop : NonDet MachineState α) : Vs.FK vsF (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine Vs.dk_bind (Vs.dk_gets _) (fun _ => Vs.dk_bind (Vs.dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact Vs.dk_bind (Vs.dk_modify (fun σ => rfl)) (fun _ => Vs.dk_pure _)

/-- **`set_cap` keeps `vsF`** (a CNode's slot or a TCB's cap). -/
theorem fv_setCap (cap : Cap) (sl : CslotPtr) : Vs.FK vsF (setCap (Z := Unit) cap sl) := by
  obtain ⟨o, c⟩ := sl
  unfold setCap
  intro σ x hx
  dsimp only at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk, rfl⟩ : ∃ k, σ.kheap o = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap o with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  have fin : ∀ o', eraseV (some o') = eraseV (some k) → x ∈ (setObject (Z := Unit) o o' σ).1 →
      vsF x.2 = vsF σ := fun o' he hx' => by
    obtain ⟨k', hk', hty, e⟩ := MaxK.mk_setObject_mem hx'
    rw [hk] at hk'; cases hk'
    rw [e]; exact vsF_upd hk hty he
  have pb : ∀ o', x ∈ ((pure o' >>= fun obj' => setObject (Z := Unit) o obj') σ).1 →
      x ∈ (setObject (Z := Unit) o o' σ).1 := by
    intro o' hx'; obtain ⟨z, hz, hx'⟩ := hx'; rw [Set.mem_singleton_iff.1 hz] at hx'; exact hx'
  have fb : ∀ (f : KernelObject → NonDet (State Unit) Unit), x ∈ ((NonDet.fail >>= f) σ).1 → False := by
    intro f hx'; obtain ⟨z, hz, -⟩ := hx'; exact hz
  cases k with
  | cnode r cs =>
    dsimp only at hx
    split at hx
    · exact fin _ (by rfl) (pb _ hx)
    · exact (fb _ hx).elim
  | tcb t =>
    dsimp only at hx
    repeat' split at hx
    all_goals first
      | exact (fb _ hx).elim
      | exact fin _ (by rfl) (pb _ hx)
  | _ => dsimp only at hx; exact (fb _ hx).elim

macro "fv_auto" : tactic => `(tactic| repeat' (first | exact fv_setObjectA _ _ | exact fv_setCap _ _ | exact fk_getCapG _ _ | exact fv_doMachineOp _ | dk_step0 | fk_unf | sched_unf | vs_unf))

set_option maxHeartbeats 8000000 in
theorem fv_performPageInvocation (iv : PageInvocation) : Vs.FK vsF (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation performPageInvocationUnmap; fv_auto

set_option maxHeartbeats 8000000 in
theorem fv_performPageTableInvocation (iv : PageTableInvocation) :
    Vs.FK vsF (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; fv_auto

set_option maxHeartbeats 8000000 in
theorem fv_performPageDirectoryInvocation (iv : PageDirectoryInvocation) :
    Vs.FK vsF (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; fv_auto

set_option maxHeartbeats 8000000 in
theorem fv_performPdptInvocation (iv : PdptInvocation) : Vs.FK vsF (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; fv_auto

set_option maxHeartbeats 8000000 in
theorem fv_performAsidPoolInvocation (iv : AsidPoolInvocation) :
    Vs.FK vsF (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation storeAsidPoolEntry; fv_auto

set_option maxHeartbeats 8000000 in
theorem fv_performPml4Flush (i : Fl4Pml4Invocation) : Vs.FK vsF (performPml4Flush (Z := Unit) i) := by
  cases i; unfold performPml4Flush; fv_auto

/-! ### The frame -/

/-- **The frame of a VSpace invocation** (module docstring). -/
structure VsFr (σ σ' : State Unit) : Prop where
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨
    (∃ a a', σ.kheap p = some (.archObj a) ∧ σ'.kheap p = some (.archObj a') ∧ aaType a' = aaType a) ∨
    (∃ r cs cs', σ.kheap p = some (.cnode r cs) ∧ σ'.kheap p = some (.cnode r cs')) ∨
    (∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧ CapsOnly x y)
  ty : ∀ p, (σ'.kheap p).map aType = (σ.kheap p).map aType
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap
  ct : σ'.curThread = σ.curThread
  idle : σ'.idleThread = σ.idleThread
  cons : σ'.consumedTime = σ.consumedTime
  time : σ'.curTime = σ.curTime
  csc : σ'.curSc = σ.curSc
  repr : σ'.reprogramTimer = σ.reprogramTimer
  act : σ'.schedulerAction = σ.schedulerAction
  dl : σ'.domainList = σ.domainList
  di : σ'.domainIndex = σ.domainIndex
  dsi : σ'.domainStartIndex = σ.domainStartIndex
  cdom : σ'.curDomain = σ.curDomain
  dt : σ'.domainTime = σ.domainTime
  rq : σ'.readyQueues = σ.readyQueues
  rel : σ'.releaseQueue = σ.releaseQueue
  irqN : σ'.interruptIrqNode = σ.interruptIrqNode
  irqS : σ'.interruptStates = σ.interruptStates
  arch : σ'.archState = σ.archState

theorem eraseV_tcb {x y : Tcb} (h : eraseV (some (.tcb y)) = eraseV (some (.tcb x))) : CapsOnly x y := by
  change some (KernelObject.tcb (eraseT y)) = some (KernelObject.tcb (eraseT x)) at h
  have e : eraseT y = eraseT x := by
    simp only [Option.some.injEq, KernelObject.tcb.injEq] at h; exact h
  exact ⟨(congrArg Tcb.tcbState e :), (congrArg Tcb.tcbIpcBuffer e :), (congrArg Tcb.tcbFault e :),
    (congrArg Tcb.tcbBoundNotification e :), (congrArg Tcb.tcbMcpriority e :), (congrArg Tcb.tcbSchedContext e :),
    (congrArg Tcb.tcbYieldTo e :), (congrArg Tcb.tcbPriority e :), (congrArg Tcb.tcbDomain e :), (congrArg Tcb.tcbFlags e :),
    (congrArg Tcb.tcbArch e :)⟩

theorem VsFr.of_eq {σ σ' : State Unit} (h : vsF σ' = vsF σ) : VsFr σ σ' := by
  simp only [vsF, Prod.mk.injEq] at h
  obtain ⟨h1, h2, hc, ho, hct, hid, hcons, htime, hcsc, hrep, hact, hdl, hdi, hdsi, hcd, hdt, hrq, hrel, hin, his,
    har⟩ := h
  refine ⟨fun p => ?_, fun p => congrFun h2 p, hc, ho, hct, hid, hcons, htime, hcsc, hrep, hact, hdl, hdi, hdsi, hcd,
    hdt, hrq, hrel, hin, his, har⟩
  have e1 : eraseV (σ'.kheap p) = eraseV (σ.kheap p) := congrFun h1 p
  have e2 : (σ'.kheap p).map aType = (σ.kheap p).map aType := congrFun h2 p
  cases g : σ.kheap p with
  | none =>
    rw [g] at e1 e2
    cases g' : σ'.kheap p with
    | none => exact Or.inl rfl
    | some k' => rw [g'] at e2; cases e2
  | some k =>
    rw [g] at e1 e2
    cases g' : σ'.kheap p with
    | none => rw [g'] at e2; cases e2
    | some k' =>
      rw [g'] at e1 e2
      simp only [Option.map_some, Option.some.injEq] at e2
      cases k with
      | archObj a =>
        cases k' with
        | archObj a' => exact Or.inr (Or.inl ⟨a, a', rfl, rfl, by simpa [aType] using e2⟩)
        | cnode r cs => simp only [aType] at e2; split at e2 <;> cases e2
        | schedContext y n => simp only [aType] at e2; split at e2 <;> cases e2
        | _ => simp [aType] at e2
      | cnode r cs =>
        cases k' with
        | cnode r' cs' =>
          simp only [eraseV, Option.some.injEq, KernelObject.cnode.injEq] at e1
          exact Or.inr (Or.inr (Or.inl ⟨r, cs, cs', rfl, by rw [e1.1]⟩))
        | _ => simp [eraseV] at e1
      | tcb x =>
        cases k' with
        | tcb y => exact Or.inr (Or.inr (Or.inr ⟨x, y, rfl, rfl, eraseV_tcb e1⟩))
        | _ => simp [eraseV] at e1
      | _ =>
        cases k' <;> first | (left; exact e1) | (exfalso; simp [aType] at e2; done) | (exfalso; simp only [aType] at e2; split at e2 <;> cases e2; done) | (exfalso; simp [eraseV] at e1; done)

theorem VsFr.of_fk {α : Type} {m : NonDet (State Unit) α} (hm : Vs.FK vsF m) {σ : State Unit} {x : α × State Unit}
    (hx : x ∈ (m σ).1) : VsFr σ x.2 :=
  VsFr.of_eq (hm σ x hx)

/-- The heap between: the arch objects as after, the rest as before. -/
def kmid (o o' : Option KernelObject) : Option KernelObject :=
  match o' with
  | some (.cnode _ _) => o
  | some (.tcb _) => o
  | _ => o'

/-- **A `VsFr` step through the state between** (module docstring). -/
theorem VsFr.mid {σ σ' : State Unit} (h : VsFr σ σ') :
    ∃ σm : State Unit, ArFr σ σm ∧ CnStep σm σ' := by
  refine ⟨{ σ' with kheap := fun p => kmid (σ.kheap p) (σ'.kheap p) }, ⟨fun p => ?_, h.cdt, h.orig, h.ct, h.idle,
    h.cons, h.time, h.csc, h.repr, h.act, h.dt, h.rq, h.rel, congrArg (fun a => a.x64GlobalPml4) h.arch,
    h.cdom⟩, ⟨⟨fun p => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩⟩
  · rcases h.kh p with e | ⟨a, a', h1, h2, ht⟩ | ⟨r, cs, cs', h1, h2⟩ | ⟨x, y, h1, h2, -⟩
    · left; show kmid (σ.kheap p) (σ'.kheap p) = σ.kheap p; rw [e]; unfold kmid; split <;> rfl
    · right; refine ⟨a, a', h1, ?_, ht⟩; show kmid (σ.kheap p) (σ'.kheap p) = _; rw [h2]; rfl
    · left; show kmid (σ.kheap p) (σ'.kheap p) = σ.kheap p; rw [h2]; rfl
    · left; show kmid (σ.kheap p) (σ'.kheap p) = σ.kheap p; rw [h2]; rfl
  · rcases h.kh p with e | ⟨a, a', h1, h2, ht⟩ | ⟨r, cs, cs', h1, h2⟩ | ⟨x, y, h1, h2, hc⟩
    · left; show σ'.kheap p = kmid (σ.kheap p) (σ'.kheap p); rw [e]; unfold kmid; split <;> rfl
    · left; show σ'.kheap p = kmid (σ.kheap p) (σ'.kheap p); rw [h2]; rfl
    · right; left; refine ⟨r, cs, cs', ?_, h2⟩; show kmid (σ.kheap p) (σ'.kheap p) = _; rw [h2]; exact h1
    · right; right; refine ⟨x, y, ?_, h2, hc⟩; show kmid (σ.kheap p) (σ'.kheap p) = _; rw [h2]; exact h1

variable {σ σ' : State Unit}

theorem VsFr.kback (h : VsFr σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e | ⟨a, a', h1, h2, -⟩ | ⟨r, cs, cs', h1, h2⟩ | ⟨x, y, h1, h2, -⟩
  · rw [e] at ho; exact ⟨ko', ho, id, id, id, id, id, id⟩
  all_goals (rw [h2] at ho; cases ho; refine ⟨_, h1, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp)

theorem VsFr.ksz (h : VsFr σ σ') : KSz σ σ' := by
  intro o ko' ho
  have e := h.ty o
  rw [ho] at e
  cases g : σ.kheap o with
  | none => rw [g] at e; cases e
  | some k => rw [g] at e; simp only [Option.map_some, Option.some.injEq] at e; exact ⟨k, rfl, e.symm⟩

theorem VsFr.szKeep (h : VsFr σ σ') : Sched.SzKeep σ σ' := by
  intro p x n hp
  rcases h.kh p with e | ⟨a, a', h1, h2, -⟩ | ⟨r, cs, cs', h1, h2⟩ | ⟨y, z, h1, h2, -⟩
  · exact ⟨x, by rw [← e]; exact hp⟩
  all_goals (rw [hp] at h2; cases h2)

theorem VsFr.ksub (h : VsFr σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun r cs ho hw => ?_, fun t ho => ?_, fun h0 => ?_⟩
  · rcases h.kh o with e | ⟨a, a', h1, h2, -⟩ | ⟨r', ds, ds', h1, h2⟩ | ⟨x, y, h1, h2, -⟩
    · exact ⟨cs, by rw [← e]; exact ho, hw⟩
    · rw [ho] at h2; cases h2
    · rw [ho] at h2; cases h2
      refine ⟨ds, h1, ?_⟩
      have e := h.ty o
      rw [ho, h1] at e
      simp only [Option.map_some, Option.some.injEq, aType] at e
      rw [if_pos hw] at e
      by_contra hn
      rw [if_neg hn] at e; cases e
    · rw [ho] at h2; cases h2
  · rcases h.kh o with e | ⟨a, a', h1, h2, -⟩ | ⟨r', ds, ds', h1, h2⟩ | ⟨x, y, h1, h2, -⟩
    · exact ⟨t, by rw [← e]; exact ho⟩
    · rw [ho] at h2; cases h2
    · rw [ho] at h2; cases h2
    · exact ⟨x, h1⟩
  · rcases h.kh o with e | ⟨a, a', h1, -, -⟩ | ⟨r', ds, ds', h1, -⟩ | ⟨x, y, h1, -, -⟩
    · rw [e, h0]
    all_goals (rw [h0] at h1; cases h1)

theorem VsFr.tcbF (h : VsFr σ σ') {p : ObjRef} {x : Tcb} (hx : σ.kheap p = some (.tcb x)) :
    ∃ y, σ'.kheap p = some (.tcb y) ∧ CapsOnly x y := by
  rcases h.kh p with e | ⟨a, a', h1, -, -⟩ | ⟨r, cs, cs', h1, -⟩ | ⟨x', y, h1, h2, hc⟩
  · exact ⟨x, by rw [e]; exact hx, CapsOnly.refl x⟩
  · rw [hx] at h1; cases h1
  · rw [hx] at h1; cases h1
  · rw [hx] at h1; cases h1; exact ⟨y, h2, hc⟩

theorem VsFr.look (h : VsFr σ σ') {p : ObjRef} {ko : KernelObject} (ha : ∀ a, ko ≠ .archObj a)
    (hc : ∀ r cs, ko ≠ .cnode r cs) (ht : ∀ x, ko ≠ .tcb x) : σ'.kheap p = some ko ↔ σ.kheap p = some ko := by
  rcases h.kh p with e | ⟨a, a', h1, h2, -⟩ | ⟨r, cs, cs', h1, h2⟩ | ⟨x, y, h1, h2, -⟩
  · rw [e]
  all_goals (rw [h1, h2]; constructor <;> intro e <;> cases e <;> first | exact absurd rfl (ha _) | exact absurd rfl (hc _ _) | exact absurd rfl (ht _))

theorem VsFr.hasPm (h : VsFr σ σ') {g : ObjRef} (hp : HasPm σ g) : HasPm σ' g := by
  obtain ⟨pt, hpt⟩ := hp
  rcases h.kh g with e | ⟨a, a', h1, h2, ht⟩ | ⟨r, cs, cs', h1, -⟩ | ⟨x, y, h1, -, -⟩
  · exact ⟨pt, by rw [e]; exact hpt⟩
  · rw [hpt] at h1
    cases h1
    cases a' with
    | pageMapL4 f => exact ⟨f, h2⟩
    | dataPage d sz => by_cases hd : d <;> simp [aaType, hd] at ht
    | _ => simp [aaType] at ht
  · rw [hpt] at h1; cases h1
  · rw [hpt] at h1; cases h1

theorem VsFr.trans {σ1 σ2 σ3 : State Unit} (h1 : vsF σ2 = vsF σ1) (h2 : vsF σ3 = vsF σ2) : VsFr σ1 σ3 :=
  VsFr.of_eq (h2.trans h1)

end Spec

end

end Fl4Proofs.P3
