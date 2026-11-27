/-
P3 (line mmuAD, gen 41): **the spec's restart before a VCPU invocation commutes with it** (spec only) — the
extended `fl4HandleInvocationVF` (Ext/VirtKernelF) runs `setThreadState thread .restart` *before*
`fl4PerformInvocationVF … (.vcpu i)`, while the VCPU step at `JAtZV3` (P3/JAtZV3VFront's `VFrontPost`) gives the
perform from the decode's state `σ`.

* `zcR c σ`: the caller's restart as a state map (`stsAct (updK σ c (.tcb {x with tcbState := .restart})) c` when `c`
  holds a TCB `x`, P3/NtfnSched's `setThreadState_eq`); `zcDom c σ`: `c` is the current thread, a TCB not in
  `runningVM`.
* **`ZcComm c m`**: on every `zcDom` state, `m` run from `zcR c σ` has exactly the outcomes of `m` from `σ` with
  `zcR c` applied to their states (and fails exactly when `m` does), and every outcome is a `zcDom` state with `c`'s
  object kept. Closed under `pure`, `bind`, `when`, and agreement on `zcDom` states (`zc_congr`).
* Primitives: `gets` / `getsThe` of a function `zcR` keeps, `assert`, `fail`, `selectF`, a machine-state update,
  `getObject p` (`p ≠ c`), `setObject p o` for a non-SC object (`p ≠ c`, or `o` no TCB: then both sides fail),
  `stateAssert` of `inUserFrame`.
* Derived: `asUser u` (`u ≠ c`), `threadGet` / `threadSet` / `getThreadState` / `setThreadState` of `u ≠ c` (the
  act of `u ≠ cur` does nothing on `zcDom`), `lookupIpcBuffer`, `getCap` of `u`'s slots, `setMrs`, `storeWordOffs`,
  `getVcpu` / `setVcpu` / `vcpuUpdate` (any `v`: at `v = c` both sides fail), `getTcbVcpu`, `ioPortRevoke`,
  `vmReportF u` (`u ≠ c`), **`vcpuDetachF`** (any thread: for `c` itself the `runningVM` test is false on both sides,
  `c` being `running` or `restart`), **`associateVcpuTcbF`**, hence **`zc_perform`**: every
  `performVcpuInvocationF i`.
* **`zc_restart_perform`**: if `performVcpuInvocationF i σ = {(rep, σ')}` and `c = σ.curThread` holds a TCB `x` not
  in `runningVM`, then `setThreadState c .restart σ = {((), zcR c σ)}`, the extended perform from there has the one
  outcome `(.ok rep, zcR c σ')`, `σ'.kheap c = σ.kheap c` and `σ'.curThread = c` — what the spec's success tail of
  `fl4HandleInvocationVF` reads.

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3VFront
open Classical

namespace Fl4Proofs.P3
open Fl4Spec

noncomputable section

/-! ## The restart map and the commutation predicate -/

/-- The caller's restart as a state map (module docstring). -/
def zcR (c : ObjRef) (σ : State Unit) : State Unit :=
  match σ.kheap c with
  | some (.tcb x) => Notif.stsAct (Notif.updK σ c (.tcb { x with tcbState := .restart })) c
  | _ => σ

/-- `c` is the current thread, a TCB not in `runningVM`. -/
def zcDom (c : ObjRef) (σ : State Unit) : Prop :=
  σ.curThread = c ∧ ∃ x, σ.kheap c = some (.tcb x) ∧ x.tcbState ≠ .runningVM

/-- **`m` commutes with the restart of `c`** (module docstring). -/
def ZcComm {α : Type} (c : ObjRef) (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, zcDom c σ →
    m (zcR c σ) = ((fun p => (p.1, zcR c p.2)) '' (m σ).1, (m σ).2) ∧
      ∀ p ∈ (m σ).1, zcDom c p.2 ∧ p.2.kheap c = σ.kheap c

section
variable {c : ObjRef} {σ : State Unit}

theorem zcR_of {x : Tcb} (hk : σ.kheap c = some (.tcb x)) :
    zcR c σ = Notif.stsAct (Notif.updK σ c (.tcb { x with tcbState := .restart })) c := by
  unfold zcR; rw [hk]

theorem zcR_rec {x : Tcb} (hk : σ.kheap c = some (.tcb x)) :
    zcR c σ = { Notif.updK σ c (.tcb { x with tcbState := .restart }) with
      schedulerAction := (zcR c σ).schedulerAction } := by
  rw [zcR_of hk]
  exact Sched.stsAct_rec _ _

theorem zcR_kheap {x : Tcb} (hk : σ.kheap c = some (.tcb x)) :
    (zcR c σ).kheap = Function.update σ.kheap c (some (.tcb { x with tcbState := .restart })) := by
  rw [zcR_rec hk]; rfl

theorem zcR_kheap_ne (h : zcDom c σ) {p : ObjRef} (hp : p ≠ c) : (zcR c σ).kheap p = σ.kheap p := by
  obtain ⟨-, x, hk, -⟩ := h
  rw [zcR_kheap hk, Function.update_of_ne hp]

theorem zcR_cur (h : zcDom c σ) : (zcR c σ).curThread = σ.curThread := by
  obtain ⟨-, x, hk, -⟩ := h
  rw [zcR_rec hk]; rfl

theorem zcR_ms (h : zcDom c σ) : (zcR c σ).machineState = σ.machineState := by
  obtain ⟨-, x, hk, -⟩ := h
  rw [zcR_rec hk]; rfl

theorem zcDom_R (h : zcDom c σ) : zcDom c (zcR c σ) := by
  obtain ⟨hc, x, hk, hx⟩ := h
  refine ⟨by rw [zcR_cur ⟨hc, x, hk, hx⟩, hc], { x with tcbState := .restart }, ?_, fun e => by cases e⟩
  rw [zcR_kheap hk, Function.update_self]

/-- `vcpuAt` reads no TCB. -/
theorem zc_vcpuAt (h : zcDom c σ) (v : ObjRef) : vcpuAt (zcR c σ) v = vcpuAt σ v := by
  obtain ⟨hc, x, hk, hx⟩ := h
  by_cases e : v = c
  · subst e
    unfold vcpuAt
    rw [zcR_kheap hk, Function.update_self, hk]
  · unfold vcpuAt
    rw [zcR_kheap_ne ⟨hc, x, hk, hx⟩ e]

theorem zc_tcbVcpuOf (h : zcDom c σ) (t : ObjRef) : tcbVcpuOf (zcR c σ) t = tcbVcpuOf σ t := by
  have e : (zcR c σ) = (zcR c σ) := rfl
  unfold tcbVcpuOf
  simp only [zc_vcpuAt h]

theorem zc_inUserFrame (h : zcDom c σ) (p : ObjRef) : inUserFrame p (zcR c σ) ↔ inUserFrame p σ := by
  obtain ⟨hc, x, hk, hx⟩ := h
  unfold inUserFrame
  refine exists_congr fun sz => ?_
  by_cases e : (p &&& ~~~(mask (pageBitsForSize sz))) = c
  · rw [e, zcR_kheap hk, Function.update_self, hk]
    constructor <;> intro h <;> cases h
  · rw [zcR_kheap_ne ⟨hc, x, hk, hx⟩ e]

end

/-! ## Combinators -/

section
variable {c : ObjRef} {σ : State Unit}

theorem zc_pure {α : Type} (a : α) : ZcComm c (NonDet.pure a : NonDet (State Unit) α) := by
  intro σ h
  refine ⟨?_, fun p hp => ?_⟩
  · show ({(a, zcR c σ)}, False) = _
    simp [NonDet.pure]
  · simp only [NonDet.pure, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨h, rfl⟩

theorem zc_pure' {α : Type} (a : α) : ZcComm c (pure a : NonDet (State Unit) α) := zc_pure a

theorem zc_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : ZcComm c m)
    (hf : ∀ a, ZcComm c (f a)) : ZcComm c (m >>= f) := by
  intro σ h
  obtain ⟨e1, d1⟩ := hm σ h
  have hF : ∀ y ∈ (m σ).1, f y.1 (zcR c y.2) = ((fun p => (p.1, zcR c p.2)) '' (f y.1 y.2).1, (f y.1 y.2).2) :=
    fun y hy => (hf y.1 y.2 (d1 y hy).1).1
  refine ⟨?_, fun p hp => ?_⟩
  · rw [nd_bind_apply, nd_bind_apply, e1]
    refine Prod.ext ?_ ?_
    · show {r | ∃ x ∈ (fun p => (p.1, zcR c p.2)) '' (m σ).1, r ∈ (f x.1 x.2).1} =
        (fun p => (p.1, zcR c p.2)) '' {r | ∃ x ∈ (m σ).1, r ∈ (f x.1 x.2).1}
      ext r
      constructor
      · rintro ⟨x, ⟨y, hy, rfl⟩, hr⟩
        have hr' : r ∈ (f y.1 (zcR c y.2)).1 := hr
        rw [hF y hy] at hr'
        obtain ⟨z, hz, rfl⟩ := hr'
        exact ⟨z, ⟨y, hy, hz⟩, rfl⟩
      · rintro ⟨z, ⟨y, hy, hz⟩, rfl⟩
        refine ⟨(y.1, zcR c y.2), ⟨y, hy, rfl⟩, ?_⟩
        show _ ∈ (f y.1 (zcR c y.2)).1
        rw [hF y hy]
        exact ⟨z, hz, rfl⟩
    · show ((m σ).2 ∨ ∃ x ∈ (fun p => (p.1, zcR c p.2)) '' (m σ).1, (f x.1 x.2).2) =
        ((m σ).2 ∨ ∃ x ∈ (m σ).1, (f x.1 x.2).2)
      apply propext
      constructor
      · rintro (h1 | ⟨x, ⟨y, hy, rfl⟩, h2⟩)
        · exact Or.inl h1
        · have h2' : (f y.1 (zcR c y.2)).2 := h2
          rw [hF y hy] at h2'
          exact Or.inr ⟨y, hy, h2'⟩
      · rintro (h1 | ⟨y, hy, h2⟩)
        · exact Or.inl h1
        · refine Or.inr ⟨(y.1, zcR c y.2), ⟨y, hy, rfl⟩, ?_⟩
          show (f y.1 (zcR c y.2)).2
          rw [hF y hy]
          exact h2
  · rw [nd_bind_apply] at hp
    obtain ⟨y, hy, hp'⟩ := hp
    obtain ⟨d2, k2⟩ := (hf y.1 y.2 (d1 y hy).1).2 p hp'
    exact ⟨d2, k2.trans (d1 y hy).2⟩

theorem zc_congr {α : Type} {m m' : NonDet (State Unit) α} (hm : ZcComm c m')
    (he : ∀ σ, zcDom c σ → m σ = m' σ) : ZcComm c m := by
  intro σ h
  rw [he σ h, he _ (zcDom_R h)]
  exact hm σ h

theorem zc_when {P : Prop} [Decidable P] {m : NonDet (State Unit) Unit} (hm : ZcComm c m) :
    ZcComm c (NonDet.when P m) := by
  unfold NonDet.when
  split
  · exact hm
  · exact zc_pure ()

theorem zc_gets {α : Type} {g : State Unit → α} (hg : ∀ σ, zcDom c σ → g (zcR c σ) = g σ) :
    ZcComm c (NonDet.gets g) := by
  intro σ h
  refine ⟨?_, fun p hp => ?_⟩
  · show ({(g (zcR c σ), zcR c σ)}, False) = _
    rw [hg σ h]; simp [NonDet.gets]
  · simp only [NonDet.gets, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨h, rfl⟩

theorem zc_getsThe {α : Type} {g : State Unit → Option α} (hg : ∀ σ, zcDom c σ → g (zcR c σ) = g σ) :
    ZcComm c (NonDet.getsThe g) := by
  intro σ h
  unfold NonDet.getsThe
  rw [hg σ h]
  cases e : g σ with
  | none =>
    refine ⟨?_, fun p hp => ?_⟩
    · simp [NonDet.assertOpt, NonDet.fail]
    · simp [NonDet.assertOpt, NonDet.fail] at hp
  | some a =>
    refine ⟨?_, fun p hp => ?_⟩
    · simp [NonDet.assertOpt, NonDet.pure]
    · simp only [NonDet.assertOpt, NonDet.pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨h, rfl⟩

theorem zc_fail {α : Type} : ZcComm c (NonDet.fail : NonDet (State Unit) α) := by
  intro σ h
  refine ⟨?_, fun p hp => ?_⟩
  · simp [NonDet.fail]
  · simp [NonDet.fail] at hp

theorem zc_assert (P : Prop) : ZcComm c (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ h
  by_cases hP : P
  · refine ⟨?_, fun p hp => ?_⟩
    · simp [NonDet.assert, hP]
    · simp only [NonDet.assert, hP, true_and, Set.ofPred_eq_eq_singleton, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨h, rfl⟩
  · refine ⟨?_, fun p hp => ?_⟩
    · simp [NonDet.assert, hP]
    · simp [NonDet.assert, hP] at hp

theorem zc_selectF {α : Type} (S : Set α × Prop) : ZcComm c (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ h
  refine ⟨?_, fun p hp => ?_⟩
  · simp only [NonDet.selectF]
    congr 1
    ext ⟨a, s⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨ha, rfl⟩; exact ⟨a, σ, ⟨ha, rfl⟩, rfl, rfl⟩
    · rintro ⟨_, _, ⟨ha, rfl⟩, rfl, rfl⟩; exact ⟨ha, rfl⟩
  · simp only [NonDet.selectF, Set.mem_ofPred_eq] at hp
    obtain ⟨-, e⟩ := hp; rw [e]; exact ⟨h, rfl⟩

theorem zc_modify {g : State Unit → State Unit}
    (hg : ∀ σ, zcDom c σ → g (zcR c σ) = zcR c (g σ) ∧ zcDom c (g σ) ∧ (g σ).kheap c = σ.kheap c) :
    ZcComm c (NonDet.modify g) := by
  intro σ h
  refine ⟨?_, fun p hp => ?_⟩
  · show ({((), g (zcR c σ))}, False) = _
    rw [(hg σ h).1]; simp [NonDet.modify]
  · simp only [NonDet.modify, Set.mem_singleton_iff] at hp
    subst hp; exact (hg σ h).2

theorem zc_stsAct_ms (A : State Unit) (c : ObjRef) (ms : MachineState) :
    Notif.stsAct { A with machineState := ms } c = { Notif.stsAct A c with machineState := ms } := by
  unfold Notif.stsAct
  have e : (c = ({ A with machineState := ms } : State Unit).curThread ∧
      ({ A with machineState := ms } : State Unit).schedulerAction = .resumeCurThread ∧
      ¬schedulable c { A with machineState := ms } = true) ↔
      (c = A.curThread ∧ A.schedulerAction = .resumeCurThread ∧ ¬schedulable c A = true) := Iff.rfl
  by_cases h : c = A.curThread ∧ A.schedulerAction = .resumeCurThread ∧ ¬schedulable c A = true
  · rw [if_pos (e.2 h), if_pos h]
  · rw [if_neg (mt e.1 h), if_neg h]

theorem zc_ms (h : zcDom c σ) (ms : MachineState) :
    { zcR c σ with machineState := ms } = zcR c { σ with machineState := ms } := by
  obtain ⟨hc, x, hk, hx⟩ := h
  have hk' : ({ σ with machineState := ms } : State Unit).kheap c = some (.tcb x) := hk
  rw [zcR_of hk, zcR_of hk']
  exact (zc_stsAct_ms (Notif.updK σ c (.tcb { x with tcbState := .restart })) c ms).symm

theorem zc_doMachineOp {α : Type} (mop : NonDet MachineState α) :
    ZcComm c (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine zc_bind (zc_gets fun σ h => zcR_ms h) fun ms => ?_
  refine zc_bind (zc_selectF _) fun ⟨r, ms'⟩ => ?_
  refine zc_bind (zc_modify fun σ h => ⟨zc_ms h ms', ?_, rfl⟩) fun _ => zc_pure' r
  obtain ⟨hc, x, hk, hx⟩ := h
  exact ⟨hc, x, hk, hx⟩

end

/-! ## Objects -/

section
variable {c : ObjRef} {σ : State Unit}

theorem zc_sched_eq {τ A : State Unit} (h1 : τ.kheap c = A.kheap c) (h2 : scsOf τ = scsOf A)
    (h3 : τ.releaseQueue = A.releaseQueue) : schedulable c τ = schedulable c A := by
  have ht : tcbsOf τ c = tcbsOf A c := by simp only [tcbsOfKh, optMap, h1]
  have e1 : optMapSome (tcbsOf τ) Tcb.tcbState c = optMapSome (tcbsOf A) Tcb.tcbState c := v3_optMap_congr ht
  have e2 : optMap (tcbsOf τ) Tcb.tcbSchedContext c = optMap (tcbsOf A) Tcb.tcbSchedContext c := v3_optMap_congr ht
  have e3 : optMap (optMap (tcbsOf τ) Tcb.tcbSchedContext) (scsOf A) c =
      optMap (optMap (tcbsOf A) Tcb.tcbSchedContext) (scsOf A) c := v3_optMap_congr e2
  unfold schedulable
  apply decide_eq_decide.2
  unfold optPred
  rw [h2, h3, e1, e3]

theorem zc_stsAct_upd (A : State Unit) (p : ObjRef) (o : KernelObject)
    (hs : schedulable c (Notif.updK A p o) = schedulable c A) :
    Notif.stsAct (Notif.updK A p o) c = Notif.updK (Notif.stsAct A c) p o := by
  unfold Notif.stsAct
  have e : (c = (Notif.updK A p o).curThread ∧ (Notif.updK A p o).schedulerAction = .resumeCurThread ∧
      ¬schedulable c (Notif.updK A p o) = true) ↔
      (c = A.curThread ∧ A.schedulerAction = .resumeCurThread ∧ ¬schedulable c A = true) := by
    rw [hs]; exact Iff.rfl
  by_cases h : c = A.curThread ∧ A.schedulerAction = .resumeCurThread ∧ ¬schedulable c A = true
  · rw [if_pos (e.2 h), if_pos h]; rfl
  · rw [if_neg (mt e.1 h), if_neg h]

/-- **The restart commutes with a heap update of a non-SC object at `p ≠ c`.** -/
theorem zcR_updK (h : zcDom c σ) {p : ObjRef} (hp : p ≠ c) {o : KernelObject}
    (hk : ∀ k, σ.kheap p = some k → scOf k = none) (ho : scOf o = none) :
    Notif.updK (zcR c σ) p o = zcR c (Notif.updK σ p o) := by
  obtain ⟨hc, x, hkc, hx⟩ := h
  have hkc' : (Notif.updK σ p o).kheap c = some (.tcb x) := by
    rw [Notif.updK_kheap, Function.update_of_ne (Ne.symm hp)]; exact hkc
  rw [zcR_of hkc, zcR_of hkc']
  have hcomm : Notif.updK (Notif.updK σ p o) c (.tcb { x with tcbState := .restart }) =
      Notif.updK (Notif.updK σ c (.tcb { x with tcbState := .restart })) p o := by
    simp only [Notif.updK, Function.update_comm hp]
  rw [hcomm]
  refine (zc_stsAct_upd _ p o (zc_sched_eq ?_ ?_ rfl)).symm
  · rw [Notif.updK_kheap, Function.update_of_ne (Ne.symm hp)]
  · funext q
    by_cases e : q = p
    · subst e
      simp only [scsOfKh, optMap, Notif.updK_kheap, Function.update_self, Function.update_of_ne hp]
      rw [ho]
      cases e2 : σ.kheap q with
      | none => rfl
      | some k => exact (hk k e2).symm
    · simp only [scsOfKh, optMap, Notif.updK_kheap, Function.update_of_ne e]

theorem zc_aType_nsc {k o : KernelObject} (ht : aType k = aType o)
    (ho : (∃ y, o = .tcb y) ∨ (∃ ao, o = .archObj ao)) : scOf k = none := by
  rcases ho with ⟨y, rfl⟩ | ⟨ao, rfl⟩ <;> cases k <;> simp_all [aType, scOf] <;> split_ifs at ht

theorem zc_aType_tcb {k o : KernelObject} (ht : aType k = aType o) (hk : ∃ y, k = .tcb y)
    (ho : ∀ y, o ≠ .tcb y) : False := by
  obtain ⟨y, rfl⟩ := hk
  cases o <;> simp_all [aType] <;> split_ifs at ht

theorem zc_setObject_eq (σ : State Unit) (p : ObjRef) (o : KernelObject) :
    setObject (Z := Unit) p o σ =
      if ∃ k, σ.kheap p = some k ∧ aType k = aType o then ({((), Notif.updK σ p o)}, False) else (∅, True) := by
  split
  · rename_i hh
    obtain ⟨k, hk, ht⟩ := hh
    exact Notif.setObject_eq hk ht
  · rename_i hn
    unfold setObject
    rw [nd_bind_apply]
    cases hk : σ.kheap p with
    | none =>
      have h0 : getObject (Z := Unit) p σ = (∅, True) := by
        simp [getObject, NonDet.getsThe, readObject, hk, NonDet.assertOpt, NonDet.fail]
      rw [h0]; simp
    | some k =>
      rw [Notif.getObject_eq hk]
      have hne : ¬ aType k = aType o := fun e => hn ⟨k, hk, e⟩
      have h1 : (NonDet.assert (σ := State Unit) (aType k = aType o)) σ = (∅, True) := by
        simp [NonDet.assert, hne]
      simp only [Set.mem_singleton_iff, exists_eq_left, false_or]
      rw [nd_bind_apply, h1]
      simp

theorem zc_setObject {p : ObjRef} {o : KernelObject} (ho : (∃ y, o = .tcb y) ∨ (∃ ao, o = .archObj ao))
    (hp : p ≠ c ∨ ∀ y, o ≠ .tcb y) : ZcComm c (setObject (Z := Unit) p o) := by
  intro σ h
  obtain ⟨hc, x, hkc, hx⟩ := h
  have h' : zcDom c σ := ⟨hc, x, hkc, hx⟩
  by_cases hpc : p = c
  · subst hpc
    have hnt : ∀ y, o ≠ .tcb y := hp.resolve_left (fun e => e rfl)
    have n1 : ¬ ∃ k, σ.kheap p = some k ∧ aType k = aType o := fun ⟨k, hk, ht⟩ => by
      rw [hkc] at hk; cases hk; exact zc_aType_tcb ht ⟨x, rfl⟩ hnt
    have n2 : ¬ ∃ k, (zcR p σ).kheap p = some k ∧ aType k = aType o := fun ⟨k, hk, ht⟩ => by
      rw [zcR_kheap hkc, Function.update_self] at hk; cases hk; exact zc_aType_tcb ht ⟨_, rfl⟩ hnt
    rw [zc_setObject_eq, zc_setObject_eq, if_neg n1, if_neg n2]
    refine ⟨by simp, fun q hq => ?_⟩
    simp at hq
  · have hkp := zcR_kheap_ne h' hpc
    rw [zc_setObject_eq, zc_setObject_eq, hkp]
    by_cases hh : ∃ k, σ.kheap p = some k ∧ aType k = aType o
    · rw [if_pos hh, if_pos hh]
      obtain ⟨k, hk, ht⟩ := hh
      have hsk : ∀ k', σ.kheap p = some k' → scOf k' = none := by
        intro k' hk'; rw [hk] at hk'; cases hk'; exact zc_aType_nsc ht ho
      have hso : scOf o = none := by rcases ho with ⟨y, rfl⟩ | ⟨ao, rfl⟩ <;> rfl
      refine ⟨by rw [zcR_updK h' hpc hsk hso]; simp, fun q hq => ?_⟩
      simp only [Set.mem_singleton_iff] at hq
      subst hq
      refine ⟨⟨hc, x, ?_, hx⟩, ?_⟩ <;>
        simp only [Notif.updK_kheap, Function.update_of_ne (Ne.symm hpc), hkc]
    · rw [if_neg hh, if_neg hh]
      exact ⟨by simp, fun q hq => by simp at hq⟩

theorem zc_getObject {p : ObjRef} (hp : p ≠ c) : ZcComm c (getObject (Z := Unit) p) :=
  zc_getsThe fun σ h => by unfold readObject; exact zcR_kheap_ne h hp

theorem zc_getTcb {u : ObjRef} (hu : u ≠ c) : ZcComm c (NonDet.getsThe (getTcb (Z := Unit) u)) :=
  zc_getsThe fun σ h => by unfold getTcb readObject; rw [zcR_kheap_ne h hu]

theorem zc_asUser {β : Type} {u : ObjRef} (hu : u ≠ c) (f : UserMonad β) : ZcComm c (asUser (Z := Unit) u f) := by
  unfold asUser
  refine zc_bind (zc_getTcb hu) fun tcb => zc_bind (zc_pure' _) fun uc => zc_bind (zc_selectF _) fun ⟨a, uc'⟩ => ?_
  exact zc_bind (zc_pure' _) fun nt => zc_bind (zc_setObject (Or.inl ⟨_, rfl⟩) (Or.inl hu)) fun _ => zc_pure' a

theorem zc_threadGet {β : Type} {u : ObjRef} (hu : u ≠ c) (f : Tcb → β) : ZcComm c (threadGet (Z := Unit) f u) := by
  unfold threadGet
  exact zc_bind (zc_getTcb hu) fun _ => zc_pure' _

theorem zc_threadSet {u : ObjRef} (hu : u ≠ c) (f : Tcb → Tcb) : ZcComm c (threadSet (Z := Unit) f u) := by
  unfold threadSet
  exact zc_bind (zc_getTcb hu) fun _ => zc_setObject (Or.inl ⟨_, rfl⟩) (Or.inl hu)

theorem zc_setThreadState {u : ObjRef} (hu : u ≠ c) (ts : ThreadState) :
    ZcComm c (setThreadState (Z := Unit) u ts) := by
  unfold setThreadState
  refine zc_bind (zc_threadSet hu _) fun _ => zc_congr (zc_pure ()) fun σ h => ?_
  rw [Notif.setThreadStateAct_eq]
  unfold Notif.stsAct
  rw [if_neg (fun hh => hu (hh.1.trans h.1))]
  rfl

theorem zc_assertOpt {β : Type} (v : Option β) : ZcComm c (NonDet.assertOpt v : NonDet (State Unit) β) := by
  cases v
  · exact zc_fail
  · exact zc_pure _

theorem zc_getCap {u : ObjRef} (hu : u ≠ c) (cref : CnodeIndex) : ZcComm c (getCap (Z := Unit) (u, cref)) := by
  unfold getCap
  refine zc_bind (zc_getObject hu) fun obj => ?_
  cases obj with
  | cnode sz cn => exact zc_bind (zc_assert _) fun _ => zc_bind (zc_pure' _) fun _ => zc_assertOpt _
  | tcb y => exact zc_bind (zc_pure' _) fun _ => zc_assertOpt _
  | _ => exact zc_bind zc_fail fun _ => zc_assertOpt _

theorem zc_pure_bind {α β : Type} {a : α} {f : α → NonDet (State Unit) β} (h : ZcComm c (f a)) :
    ZcComm c (pure a >>= f) := by
  rw [nd_pure_bind]; exact h

theorem zc_lookupIpcBuffer {u : ObjRef} (hu : u ≠ c) (b : Bool) :
    ZcComm c (lookupIpcBuffer (Z := Unit) b u) := by
  unfold lookupIpcBuffer
  refine zc_bind (zc_threadGet hu _) fun bp => zc_pure_bind ?_
  refine zc_bind (zc_getCap hu _) fun cap => ?_
  split
  · split
    · exact zc_pure' _
    · exact zc_pure' _
  · exact zc_pure' _

theorem zc_stateAssert {P : State Unit → Prop} (hP : ∀ σ, zcDom c σ → (P (zcR c σ) ↔ P σ)) :
    ZcComm c (NonDet.stateAssert P) := by
  intro σ h
  have e : NonDet.stateAssert P (zcR c σ) = NonDet.assert (P σ) (zcR c σ) := by
    unfold NonDet.stateAssert; rw [propext (hP σ h)]
  rw [e]
  exact zc_assert (P σ) σ h

theorem zc_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) :
    ZcComm c (storeWordOffs (Z := Unit) ptr offs v) := by
  refine zc_congr (m' := NonDet.stateAssert (inUserFrame (ptr + BitVec.ofNat 64 (offs * wordSize))) >>= fun _ =>
      doMachineOp (storeWord (ptr + BitVec.ofNat 64 (offs * wordSize)) v))
    (zc_bind (zc_stateAssert fun σ h => zc_inUserFrame h _) fun _ => zc_doMachineOp _) fun σ _ => ?_
  unfold storeWordOffs
  exact Notif.nd_bind_one (show (NonDet.get : NonDet (State Unit) (State Unit)) σ = ({(σ, σ)}, False) from rfl) _

theorem zc_zipWithMx {β γ δ : Type} {f : β → γ → NonDet (State Unit) δ} (hf : ∀ a b, ZcComm c (f a b)) :
    ∀ (xs : List β) (ys : List γ), ZcComm c (NonDet.zipWithMx f xs ys) := by
  intro xs
  induction xs with
  | nil => intro ys; cases ys <;> exact zc_pure ()
  | cons a xs ih =>
    intro ys
    cases ys with
    | nil => exact zc_pure ()
    | cons b ys => exact zc_bind (hf a b) fun _ => ih ys

theorem zc_setMrs {u : ObjRef} (hu : u ≠ c) (buf : Option ObjRef) (msgs : List Data) :
    ZcComm c (setMrs (Z := Unit) u buf msgs) := by
  unfold setMrs
  refine zc_bind (zc_getTcb hu) fun tcb => zc_bind (zc_pure' _) fun _ => zc_bind (zc_pure' _) fun _ => ?_
  refine zc_bind (zc_setObject (Or.inl ⟨_, rfl⟩) (Or.inl hu)) fun _ => zc_bind (zc_pure' _) fun _ => ?_
  cases buf with
  | none => exact zc_pure' _
  | some pp => exact zc_bind (zc_zipWithMx (fun a b => zc_storeWordOffs _ _ _) _ _) fun _ => zc_pure' _

theorem zc_getVcpu (v : ObjRef) : ZcComm c (getVcpu (Z := Unit) v) := by
  by_cases hv : v = c
  · subst hv
    refine zc_congr (zc_fail) fun σ h => ?_
    obtain ⟨-, x, hk, -⟩ := h
    unfold getVcpu
    rw [Notif.nd_bind_one (Notif.getObject_eq hk)]
  · unfold getVcpu
    refine zc_bind (zc_getObject hv) fun ko => ?_
    split
    · exact zc_pure' _
    · exact zc_fail

theorem zc_setVcpu (v : ObjRef) (st : VcpuState) : ZcComm c (setVcpu (Z := Unit) v st) :=
  zc_setObject (Or.inr ⟨_, rfl⟩) (Or.inr fun y e => by cases e)

theorem zc_vcpuUpdate (v : ObjRef) (f : VcpuState → VcpuState) : ZcComm c (vcpuUpdate (Z := Unit) v f) := by
  unfold vcpuUpdate
  exact zc_bind (zc_getVcpu v) fun st => zc_setVcpu v _

theorem zc_getTcbVcpu (t : ObjRef) : ZcComm c (getTcbVcpu (Z := Unit) t) :=
  zc_gets fun σ h => zc_tcbVcpuOf h t


/-- Close a `ZcComm` goal by the combinators, the local `ZcComm` facts and case splits. -/
macro "zc_tac" : tactic => `(tactic| repeat (first
  | (with_reducible apply_assumption)
  | (with_reducible exact zc_pure _)
  | (with_reducible exact zc_pure' _)
  | (with_reducible exact zc_fail)
  | (with_reducible exact zc_assert _)
  | (with_reducible exact zc_selectF _)
  | (with_reducible exact zc_getTcbVcpu _)
  | (with_reducible exact zc_getVcpu _)
  | (with_reducible exact zc_vcpuUpdate _ _)
  | (with_reducible exact zc_setVcpu _ _)
  | (with_reducible apply zc_bind)
  | (with_reducible intro _)
  | (split)
  | (dsimp only)))

end

/-! ## The VMEnter report, the detach, SetTCB, every VCPU invocation -/

section
variable {c : ObjRef} {σ : State Unit}

theorem zc_vmFullReply {u : ObjRef} (hu : u ≠ c) : ZcComm c (vmFullReply (Z := Unit) u) := by
  unfold vmFullReply
  exact zc_bind (zc_asUser hu _) fun _ => zc_pure' _

theorem zc_vmFaultIpNext {u : ObjRef} (hu : u ≠ c) : ZcComm c (vmFaultIpNext (Z := Unit) u) := by
  unfold vmFaultIpNext
  exact zc_asUser hu _

theorem zc_vmReportF {u : ObjRef} (hu : u ≠ c) (badge : Word) : ZcComm c (vmReportF (Z := Unit) u badge) := by
  have h1 := zc_vmFullReply (c := c) hu
  have h2 := zc_lookupIpcBuffer (c := c) hu true
  have h3 : ∀ b m, ZcComm c (setMrs (Z := Unit) u b m) := zc_setMrs hu
  have h4 : ∀ f : UserMonad Unit, ZcComm c (asUser (Z := Unit) u f) := fun f => zc_asUser hu f
  have h5 : ∀ ts, ZcComm c (setThreadState (Z := Unit) u ts) := zc_setThreadState hu
  have h6 := zc_vmFaultIpNext (c := c) hu
  unfold vmReportF
  refine zc_bind (zc_getTcbVcpu u) fun vo => ?_
  cases vo with
  | none =>
    dsimp only
    exact zc_bind (zc_pure' _) fun _ => zc_bind h1 fun _ => zc_bind (zc_pure' _) fun _ => zc_bind h2 fun _ =>
      zc_bind (h3 _ _) fun _ => zc_bind (h4 _) fun _ => zc_bind (h4 _) fun _ => zc_bind (h5 _) fun _ => h6
  | some v =>
    dsimp only
    refine zc_bind (zc_getVcpu v) fun _ => zc_bind (zc_pure' _) fun _ => zc_bind h1 fun _ =>
      zc_bind (zc_pure' _) fun r => zc_bind h2 fun _ => zc_bind (h3 _ _) fun _ => ?_
    split
    · exact zc_bind (zc_vcpuUpdate _ _) fun _ => zc_bind (h4 _) fun _ => zc_bind (h4 _) fun _ =>
        zc_bind (h5 _) fun _ => h6
    · exact zc_bind (h4 _) fun _ => zc_bind (h4 _) fun _ => zc_bind (h5 _) fun _ => h6

/-- `vcpuDetachF c` on a `zcDom` state: the `runningVM` test is false. -/
theorem zc_detach_self_eq (h : zcDom c σ) :
    vcpuDetachF (Z := Unit) c σ = (do
      let vo ← getTcbVcpu (Z := Unit) c
      match vo with
      | none => return ()
      | some v => vcpuUpdate v fun s => { s with tcb := none }) σ := by
  obtain ⟨-, x, hk, hx⟩ := h
  unfold vcpuDetachF getTcbVcpu
  rw [Notif.nd_gets_bind, Notif.nd_gets_bind]
  cases tcbVcpuOf σ c with
  | none => rfl
  | some v =>
    show (getThreadState c >>= _) σ = _
    rw [Notif.nd_bind_one (Notif.getThreadState_eq hk)]
    have hw : NonDet.when (x.tcbState = .runningVM) (vmReportF (Z := Unit) c 0) = NonDet.pure () := by
      unfold NonDet.when; rw [if_neg hx]
    rw [hw]
    exact Notif.nd_pure_bind' () _ σ

theorem zc_vcpuDetachF (t : ObjRef) : ZcComm c (vcpuDetachF (Z := Unit) t) := by
  by_cases ht : t = c
  · subst ht
    refine zc_congr ?_ fun σ h => zc_detach_self_eq h
    refine zc_bind (zc_getTcbVcpu _) fun vo => ?_
    cases vo with
    | none => exact zc_pure' _
    | some v => exact zc_vcpuUpdate _ _
  · unfold vcpuDetachF
    refine zc_bind (zc_getTcbVcpu _) fun vo => ?_
    cases vo with
    | none => exact zc_pure' _
    | some v =>
      exact zc_bind (zc_threadGet ht _) fun st => zc_bind (zc_when (zc_vmReportF ht 0)) fun _ => zc_vcpuUpdate _ _

theorem zc_associate (v t : ObjRef) : ZcComm c (associateVcpuTcbF (Z := Unit) v t) := by
  have h1 : ∀ u, ZcComm c (vcpuDetachF (Z := Unit) u) := zc_vcpuDetachF
  unfold associateVcpuTcbF
  zc_tac

theorem zc_ioPortRevoke (a : ArchCap) : ZcComm c (ioPortRevoke (Z := Unit) a) := by
  unfold ioPortRevoke ioPortOwner
  exact zc_pure' _

/-- **Every VCPU invocation commutes with the caller's restart** (module docstring). -/
theorem zc_perform (i : VcpuInvocation) : ZcComm c (performVcpuInvocationF (Z := Unit) i) := by
  have h1 : ∀ v t, ZcComm c (associateVcpuTcbF (Z := Unit) v t) := zc_associate
  have h2 : ∀ a, ZcComm c (ioPortRevoke (Z := Unit) a) := zc_ioPortRevoke
  cases i <;> (unfold performVcpuInvocationF; zc_tac)

/-- **The restart before the perform** (module docstring). -/
theorem zc_restart_perform {i : VcpuInvocation} {rep : List Data} {σ' : State Unit}
    (hp : performVcpuInvocationF (Z := Unit) i σ = ({(rep, σ')}, False)) {x : Tcb}
    (hk : σ.kheap σ.curThread = some (.tcb x)) (hx : x.tcbState ≠ .runningVM)
    (onCore remoteCur : ObjRef → Bool) (bl ca cd : Bool) :
    setThreadState (Z := Unit) σ.curThread .restart σ = ({((), zcR σ.curThread σ)}, False) ∧
      ExceptT.run (fl4PerformInvocationVF (Z := Unit) onCore remoteCur bl ca cd (.vcpu i)) (zcR σ.curThread σ) =
        ({(.ok rep, zcR σ.curThread σ')}, False) ∧
      σ'.kheap σ.curThread = some (.tcb x) ∧ σ'.curThread = σ.curThread := by
  have hD : zcDom σ.curThread σ := ⟨rfl, x, hk, hx⟩
  obtain ⟨e1, d1⟩ := zc_perform (c := σ.curThread) i σ hD
  have hmem : (rep, σ') ∈ (performVcpuInvocationF (Z := Unit) i σ).1 := by rw [hp]; exact Set.mem_singleton _
  obtain ⟨⟨hc', -⟩, hk'⟩ := d1 _ hmem
  refine ⟨?_, ?_, by rw [hk']; exact hk, hc'⟩
  · rw [Notif.setThreadState_eq .restart hk, zcR_of hk]
  · rw [zv_perfV_vcpu]
    have e2 : performVcpuInvocationF (Z := Unit) i (zcR σ.curThread σ) = ({(rep, zcR σ.curThread σ')}, False) := by
      rw [e1, hp]; simp
    exact run_liftE' e2

end

end

end Fl4Proofs.P3
