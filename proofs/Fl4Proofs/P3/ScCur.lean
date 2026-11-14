/-
P3 (DESIGN.md §9), scheduling contexts: **the current-thread invariant**
`CurInv`, the companion of `Inv` for the current thread and SC at kernel
entry (fragments of l4v):

* `tcb`: the current thread is a TCB bound to the current SC
  (`cur_sc_tcb_are_bound`, `heap_ref_eq (cur_sc s) (cur_thread s)
  (tcb_scps_of s)`), not blocked on a notification (`ct_running s ∨ ct_idle
  s` at kernel entry);
* `sc`: the current SC is an SC;
* `active`: if it is not the idle SC, it is active (`cur_sc_active`);
* `notRel`: the current thread is not in the release queue
  (`ct_not_in_release_q`).

`CurInv.facts` turns it, with `SchedRel` and `Inv`, into FL4-side facts
(the current SC is one of `C`, nonzero, and bound to the current thread both
ways) and the spec-side hypotheses of `charge_budget_refines`.
`CurInv.keeps` / `CurInv.congr` / `CurInv.restart` are the preservation
steps; `HeadKeeps` is what the budget operations keep.
-/
import Fl4Proofs.P3.ScCharge5
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- The current-thread invariant (see the module docstring). -/
structure CurInv (σ : State Unit) : Prop where
  tcb : ∃ xt, σ.kheap σ.curThread = some (.tcb xt) ∧ xt.tcbSchedContext = some σ.curSc ∧
    ∀ q, xt.tcbState ≠ .blockedOnNotification q
  sc : ∃ x n, σ.kheap σ.curSc = some (.schedContext x n)
  active : σ.curSc ≠ idleScPtr → ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → scActive x = true
  notRel : σ.curThread ∉ σ.releaseQueue

/-- What the budget operations keep: the current SC and thread, the release
queue, the scheduler action and the time, every object but the SC at `p`, and that
SC's TCB and refill max. -/
def HeadKeeps (σ σ2 : State Unit) (p : ObjRef) : Prop :=
  σ2.curSc = σ.curSc ∧ σ2.curThread = σ.curThread ∧ σ2.releaseQueue = σ.releaseQueue ∧
    σ2.schedulerAction = σ.schedulerAction ∧ σ2.curTime = σ.curTime ∧ (∀ q, q ≠ p → σ2.kheap q = σ.kheap q) ∧
    ∀ x n, σ.kheap p = some (.schedContext x n) → ∃ y, σ2.kheap p = some (.schedContext y n) ∧
      y.scTcb = x.scTcb ∧ y.scRefillMax = x.scRefillMax

theorem HeadKeeps.refl (σ : State Unit) (p : ObjRef) : HeadKeeps σ σ p :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun x _ h => ⟨x, h, rfl, rfl⟩⟩

theorem HeadKeeps.updSc {σ : State Unit} {p : ObjRef} {x y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (hy : y.scTcb = x.scTcb) (hm : y.scRefillMax = x.scRefillMax) :
    HeadKeeps σ (updSc σ p y n) p :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun q hq => by simp [updK, hq], fun x' n' h => by
    rw [hk] at h; cases h; exact ⟨y, by simp [updK], hy, hm⟩⟩

/-- `CurInv` is kept by a step that keeps what `HeadKeeps` names, for an SC
at `p`. -/
theorem CurInv.keeps {σ σ' : State Unit} (h : CurInv σ) {p : ObjRef} (hk : HeadKeeps σ σ' p)
    (hp : ∃ x n, σ.kheap p = some (.schedContext x n)) : CurInv σ' := by
  obtain ⟨e1, e2, e3, -, -, hfr, hsc⟩ := hk
  obtain ⟨xt, hkt, hxs, hnb⟩ := h.tcb
  have hctp : σ.curThread ≠ p := by
    rintro e; obtain ⟨x, n, hx⟩ := hp; rw [← e, hkt] at hx; cases hx
  -- the current SC in `σ'`
  have hcs : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) →
      ∃ y, σ'.kheap σ.curSc = some (.schedContext y n) ∧ y.scRefillMax = x.scRefillMax := by
    intro x n hx
    by_cases e : σ.curSc = p
    · rw [e] at hx ⊢; obtain ⟨y, h1, -, h3⟩ := hsc x n hx; exact ⟨y, h1, h3⟩
    · exact ⟨x, by rw [hfr _ e]; exact hx, rfl⟩
  refine ⟨⟨xt, ?_, ?_, hnb⟩, ?_, fun hid x n hx => ?_, by rw [e2, e3]; exact h.notRel⟩
  · rw [e2, hfr _ hctp]; exact hkt
  · rw [e1]; exact hxs
  · obtain ⟨x, n, hx⟩ := h.sc
    obtain ⟨y, hy, -⟩ := hcs x n hx
    exact ⟨y, n, by rw [e1]; exact hy⟩
  · rw [e1] at hid hx
    obtain ⟨x0, n0, hx0⟩ := h.sc
    obtain ⟨y, hy, hm⟩ := hcs x0 n0 hx0
    have := h.active hid x0 n0 hx0
    rw [hy] at hx; cases hx
    unfold scActive activeSc at this ⊢; rw [hm]; exact this

/-- `CurInv` only reads the heap, the current thread and SC and the release
queue. -/
theorem CurInv.congr {σ σ' : State Unit} (h : CurInv σ) (hk : σ'.kheap = σ.kheap)
    (h1 : σ'.curThread = σ.curThread) (h2 : σ'.curSc = σ.curSc) (h3 : σ'.releaseQueue = σ.releaseQueue) :
    CurInv σ' := by
  obtain ⟨xt, hkt, hxs, hnb⟩ := h.tcb
  obtain ⟨x, n, hx⟩ := h.sc
  exact ⟨⟨xt, by rw [hk, h1]; exact hkt, by rw [h2]; exact hxs, hnb⟩, ⟨x, n, by rw [hk, h2]; exact hx⟩,
    fun hid y m hy => h.active (h2 ▸ hid) y m (by rw [hk, h2] at hy; exact hy), by rw [h1, h3]; exact h.notRel⟩

/-- **`CurInv` is kept by the notification code's steps that block no
thread** (`SchedHyps.stable`'s steps: `NtfnStep` with `NoBlock`). -/
theorem CurInv.stable {σ σ' : State Unit} (h : CurInv σ) (hn : NtfnStep σ σ') (hb : NoBlock σ σ') : CurInv σ' := by
  obtain ⟨-, e2, e3, -, e5, -, -, -, -⟩ := NtfnStep.abs hn
  obtain ⟨xt, hkt, hxs, hnb⟩ := h.tcb
  obtain ⟨x, n, hx⟩ := h.sc
  obtain ⟨y, hky, -, hys, -⟩ := NtfnStep.tcbSched hn hkt
  have hx' := NtfnStep.sc hn hx
  refine ⟨⟨y, by rw [e3]; exact hky, by rw [hys, e5]; exact hxs, fun q e => ?_⟩, ⟨x, n, by rw [e5]; exact hx'⟩,
    fun hid z m hz => ?_, by rw [e2, e3]; exact h.notRel⟩
  · rcases hb _ xt y hkt hky with e' | ⟨hr, -⟩
    · exact hnb q (e'.symm.trans e)
    · rw [e] at hr; cases hr
  · rw [e5] at hid hz; rw [hx'] at hz; cases hz; exact h.active hid x n hx

/-- Blocking the current thread asks for a new one: after `set_thread_state`'s
action step, the scheduler action is not `resume_cur_thread` if the current
thread is not schedulable. -/
theorem stsAct_cur {σ : State Unit} {t : ObjRef} (ht : t = σ.curThread) (hs : schedulable t σ = false) :
    (stsAct σ t).schedulerAction ≠ .resumeCurThread := by
  unfold stsAct
  by_cases e : σ.schedulerAction = .resumeCurThread
  · rw [if_pos ⟨ht, e, by simp [hs]⟩]; simp
  · rw [if_neg (fun h => e h.2.1)]; exact e

theorem stsAct_fields (σ : State Unit) (t : ObjRef) : (stsAct σ t).kheap = σ.kheap ∧
    (stsAct σ t).curThread = σ.curThread ∧ (stsAct σ t).curSc = σ.curSc ∧
    (stsAct σ t).releaseQueue = σ.releaseQueue := by
  unfold stsAct; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem stsAct_action (σ : State Unit) (t : ObjRef) : (stsAct σ t).schedulerAction = .chooseNewThread ∨
    (stsAct σ t).schedulerAction = σ.schedulerAction := by
  unfold stsAct; split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Restarting the current thread keeps `CurInv`. -/
theorem CurInv.restart {σ : State Unit} (h : CurInv σ) {xt : Tcb} (hk : σ.kheap σ.curThread = some (.tcb xt)) :
    CurInv (stsAct (updK σ σ.curThread (.tcb { xt with tcbState := .restart })) σ.curThread) := by
  obtain ⟨e1, e2, e3, e4⟩ := stsAct_fields (updK σ σ.curThread (.tcb { xt with tcbState := .restart })) σ.curThread
  obtain ⟨xt', hkt, hxs, -⟩ := h.tcb
  rw [hk] at hkt; cases hkt
  obtain ⟨x, n, hx⟩ := h.sc
  have hne : σ.curSc ≠ σ.curThread := by rintro e; rw [e, hk] at hx; cases hx
  have h1 : CurInv (updK σ σ.curThread (.tcb { xt with tcbState := .restart })) :=
    ⟨⟨{ xt with tcbState := .restart }, by simp [updK], hxs, fun q e => by cases e⟩, ⟨x, n, by simp [updK, hne, hx]⟩,
      fun hid y m hy => h.active hid y m (by simpa [updK, hne] using hy), h.notRel⟩
  exact h1.congr e1 e2 e3 e4

/-- l4v `cur_sc_offset_ready` / `cur_sc_offset_sufficient` (for a positive
consumed time), with the current SC's head ready: the head can pay the
consumed time, keep `MIN_BUDGET`, and is not after the current time when
moved by it. -/
def OffOK (σ : State Unit) : Prop :=
  0 < σ.consumedTime → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
    refillSufficient σ.consumedTime (refillHd y) = true ∧
    refillReady' σ.consumedTime σ.curTime (refillHd y) = true ∧ refillReady σ.curTime (refillHd y) = true

/-- The current SC's head refill plus the consumed time is not after the
current time (l4v `cur_sc_offset_ready`, without wrap-around). -/
def OffReady (σ : State Unit) : Prop :=
  ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
    (refillHd y).rTime.toNat + σ.consumedTime.toNat ≤ σ.curTime.toNat

/-- `OffReady` and a sufficient head give `OffOK`. -/
theorem OffReady.ok {σ : State Unit} (h : OffReady σ)
    (hs : ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      refillSufficient σ.consumedTime (refillHd y) = true) : OffOK σ := by
  intro _ y n hy
  have h1 := h y n hy
  refine ⟨hs y n hy, ?_, ?_⟩
  · simp only [refillReady', decide_eq_true_eq, BitVec.le_def, BitVec.toNat_add]
    have := σ.curTime.isLt
    rw [Nat.mod_eq_of_lt (by omega)]; exact h1
  · simp only [refillReady', decide_eq_true_eq, BitVec.le_def, BitVec.toNat_add]
    simp; omega

/-- Restarting a thread keeps `OffOK`. -/
theorem OffOK.restart {σ : State Unit} (h : OffOK σ) {t : ObjRef} {xt : Tcb} (ts : ThreadState) :
    OffOK (stsAct (updK σ t (.tcb { xt with tcbState := ts })) t) := by
  have ek : (stsAct (updK σ t (.tcb { xt with tcbState := ts })) t).kheap = (updK σ t (.tcb { xt with tcbState := ts })).kheap :=
    stsAct_kheap _ _
  have e2 : ∀ σ0 : State Unit, (stsAct σ0 t).consumedTime = σ0.consumedTime ∧ (stsAct σ0 t).curTime = σ0.curTime ∧
      (stsAct σ0 t).curSc = σ0.curSc := fun σ0 => by unfold stsAct; split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  obtain ⟨ec, et, es⟩ := e2 (updK σ t (.tcb { xt with tcbState := ts }))
  intro hc y n hy
  rw [ek, es] at hy; rw [ec] at hc
  have hy' : (updK σ t (.tcb { xt with tcbState := ts })).kheap σ.curSc = some (.schedContext y n) := hy
  have hne : σ.curSc ≠ t := by rintro e; rw [e] at hy'; simp [updK] at hy'
  simp only [updK_kheap, ne_eq, hne, not_false_eq_true, Function.update_of_ne] at hy'
  have := h hc y n hy'
  simp only [ec, et]; exact this

theorem rescheduleRequired_action {σ σ' : State Unit} (hA : ActReady σ)
    (h : rescheduleRequired (Z := Unit) σ = ({((), σ')}, False)) : σ'.schedulerAction = .chooseNewThread := by
  cases ha : σ.schedulerAction with
  | switchThread t =>
    by_cases hs : schedulable t σ = true
    · obtain ⟨x, -, -, -, hk, -⟩ := schedulable_inv hs
      rw [rescheduleRequired_sched ha hs hA (tcbSchedAction_gen hk tcbSchedEnqueue)] at h
      rw [pair_eq h]
    · rw [rescheduleRequired_notsched ha (by simpa using hs)] at h
      rw [pair_eq h]
  | resumeCurThread =>
    rw [rescheduleRequired_noswitch (fun t e => by rw [ha] at e; cases e)] at h
    rw [pair_eq h]
  | chooseNewThread =>
    rw [rescheduleRequired_noswitch (fun t e => by rw [ha] at e; cases e)] at h
    rw [pair_eq h]

theorem rescheduleRequired_consumed {σ σ' : State Unit} (hA : ActReady σ)
    (h : rescheduleRequired (Z := Unit) σ = ({((), σ')}, False)) : σ'.consumedTime = σ.consumedTime := by
  cases ha : σ.schedulerAction with
  | switchThread t =>
    by_cases hs : schedulable t σ = true
    · obtain ⟨x, -, -, -, hk, -⟩ := schedulable_inv hs
      rw [rescheduleRequired_sched ha hs hA (tcbSchedAction_gen hk tcbSchedEnqueue)] at h
      rw [pair_eq h]; rfl
    · rw [rescheduleRequired_notsched ha (by simpa using hs)] at h
      rw [pair_eq h]
  | resumeCurThread =>
    rw [rescheduleRequired_noswitch (fun t e => by rw [ha] at e; cases e)] at h
    rw [pair_eq h]
  | chooseNewThread =>
    rw [rescheduleRequired_noswitch (fun t e => by rw [ha] at e; cases e)] at h
    rw [pair_eq h]

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem SchedRel.idle {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) :
    (nodeW st s c layout.node.IDLE_SC).bv = Fl4Spec.idleScPtr := hS.lists.choose_spec.choose_spec.2.idleSc

theorem word24_of {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {sc t : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (hxt : x.scTcb = some t.bv) : L.mem s (scW sc 24#u64) = t := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  rw [hx.tcb] at hxt
  exact eq_of_bv (optRef_some hxt).2

theorem scA_of {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {t sc : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb xt))
    (hsc : xt.tcbSchedContext = some sc.bv) : L.mem s (scA t) = sc := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', hk', -, -, h3, -⟩ := hs.tcb t ht
  rw [hk] at hk'; cases hk'
  rw [h3] at hsc
  exact eq_of_bv (optRef_some hsc).2

/-- **The budget operations' hypotheses from `CurInv`**: the current SC is
one of `C`, nonzero and bound to the current thread both ways; it is active
unless idle; the current thread is not released and not blocked on a
notification. -/
theorem CurInv.facts {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hI : Inv σ) (h : CurInv σ) :
    nodeW st s c layout.node.CUR_SC ∈ C ∧ nodeW st s c layout.node.CUR_SC ≠ 0#u64 ∧
    L.mem s (scW (nodeW st s c layout.node.CUR_SC) 24#u64) = nodeW st s c layout.node.CUR_THREAD ∧
    L.mem s (scA (nodeW st s c layout.node.CUR_THREAD)) = nodeW st s c layout.node.CUR_SC ∧
    ((nodeW st s c layout.node.CUR_SC).bv ≠ Fl4Spec.idleScPtr → ∀ x n,
      σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) → Fl4Spec.scActive x = true) ∧
    (nodeW st s c layout.node.CUR_THREAD).bv ∉ σ.releaseQueue ∧
    (∀ xt, σ.kheap (nodeW st s c layout.node.CUR_THREAD).bv = some (.tcb xt) →
      ∀ q, xt.tcbState ≠ .blockedOnNotification q) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hct := hc.curT
  obtain ⟨xt, hkt, hxs, hnb⟩ := h.tcb
  rw [hs.curThread] at hkt
  rw [hs.curSc] at hxs
  obtain ⟨x', hk', -, -, h3, -⟩ := hs.tcb _ hct
  rw [hkt] at hk'; cases hk'
  have hxs' := hxs
  rw [h3] at hxs'
  obtain ⟨h0, hbv⟩ := optRef_some hxs'
  have hts : L.mem s (scA (nodeW st s c layout.node.CUR_THREAD)) = nodeW st s c layout.node.CUR_SC := eq_of_bv hbv
  have hscC : nodeW st s c layout.node.CUR_SC ∈ C := hts ▸ hs.scMem _ hct h0
  obtain ⟨y, n, hky, hyt⟩ := hI.back _ xt _ hkt hxs
  refine ⟨hscC, hts ▸ h0, word24_of hS hscC hky hyt, hts, fun hid x m hx => ?_, ?_, fun xt' hk q => ?_⟩
  · rw [← hs.curSc] at hid hx; exact h.active hid x m hx
  · rw [← hs.curThread]; exact h.notRel
  · rw [hkt] at hk; cases hk; exact hnb q

end

end

end Fl4Proofs.P3.Sched
