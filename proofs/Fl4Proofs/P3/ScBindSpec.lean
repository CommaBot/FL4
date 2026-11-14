/-
P3 (DESIGN.md §9), scheduling contexts: **the spec's SC bind has an
outcome** (`BindSpecHyp`, ScSpecStep.lean): l4v `sched_context_bind_tcb` of
an unbound SC to a thread with no SC.

* `merge_loop_some`, `refillUnblockCheck_some`, `unblockBind_some`: the
  sporadic unblock check and its merge loop have an outcome (the loop
  shortens the refills).
* `actReady_bind`: `ActReady` before the final `reschedule_required`
  (other threads' SCs untouched; the bound thread, if still schedulable after
  `sched_context_resume`, has a ready and sufficient head refill).
* `schedContextBindTcb_some`: the bind has an outcome (`resume_spec_eq`,
  `postpone_eq` for the resume).
* `PresQ`, `setPriority_rq`: `set_priority` of a thread in no ready queue that
  is not current keeps the ready queues.
* `BindOK`, `BindOK.after` (across `set_mcpriority` and `set_priority`),
  `bindSpecHyp_of`: `BindSpecHyp` from `BindOK` after the install.
-/
import Fl4Proofs.P3.ScSpecStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Classical

noncomputable section

section Spec
open Fl4Spec

/-- **The merge loop has an outcome** (it shortens the refills). -/
theorem merge_loop_some {p : ObjRef} {n : Nat} :
    ∀ (k : Nat) (σ1 : State Unit) (z : SchedContext), z.scRefills.length ≤ k →
      σ1.kheap p = some (.schedContext z n) → z.scRefills ≠ [] →
      ∃ σ', NonDet.WhileResults (fun _ s => the (refillHeadOverlapping (Z := Unit) p s) = true)
        (fun _ => mergeOverlappingRefills (Z := Unit) p) () σ1 ((), σ')
  | k, σ1, z, hl, hk, hne => by
    by_cases hc : the (refillHeadOverlapping (Z := Unit) p σ1) = true
    · have hlen : z.scRefills.length > 1 := by
        have := hc
        rw [refillHeadOverlapping_eq hk, the_some, decide_eq_true_iff] at this
        exact this.1
      have hm := merge_eq hk hne
      have hk' : (updSc σ1 p { z with scRefills := mergeHd z } n).kheap p =
          some (.schedContext { z with scRefills := mergeHd z } n) := by simp [Notif.updK]
      obtain ⟨a, b, l, e⟩ : ∃ a b l, z.scRefills = a :: b :: l := by
        match h : z.scRefills, hlen with
        | a :: b :: l, _ => exact ⟨a, b, l, rfl⟩
      have hml : (mergeHd z).length = z.scRefills.length - 1 := by
        unfold mergeHd; rw [e]; simp
      match k with
      | 0 => omega
      | k + 1 =>
        obtain ⟨σ', h'⟩ := merge_loop_some k _ { z with scRefills := mergeHd z }
          (by simp only; rw [hml]; omega) hk' (by unfold mergeHd; simp)
        exact ⟨σ', .step hc (by rw [hm]; exact Set.mem_singleton _) h'⟩
    · exact ⟨σ1, .done hc⟩

/-- **`refill_unblock_check` has an outcome.** -/
theorem refillUnblockCheck_some {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ []) :
    ∃ σ', ((), σ') ∈ (refillUnblockCheck (Z := Unit) p σ).1 := by
  unfold refillUnblockCheck
  rw [nd_bind_one (isRoundRobin_eq hk), nd_bind_one (getScRefillReady_eq hk hne)]
  simp only [NonDet.when]
  split_ifs with hc
  · rw [Notif.nd_gets_bind, nd_bind_one (updateRefillHd_eq hk _)]
    rw [nd_bind_one (show NonDet.modify (fun s : State Unit => { s with reprogramTimer := true })
      (updSc σ p { y with scRefills := { the y.scRefills.head? with rTime := σ.curTime } :: y.scRefills.tail } n) =
      ({((), updSc { σ with reprogramTimer := true } p
        { y with scRefills := { the y.scRefills.head? with rTime := σ.curTime } :: y.scRefills.tail } n)}, False)
      from rfl)]
    obtain ⟨σ', h⟩ := merge_loop_some (p := p) (n := n) _ (updSc { σ with reprogramTimer := true } p
        { y with scRefills := { the y.scRefills.head? with rTime := σ.curTime } :: y.scRefills.tail } n)
      { y with scRefills := { the y.scRefills.head? with rTime := σ.curTime } :: y.scRefills.tail } le_rfl
      (by simp [Notif.updK]) (by simp)
    exact ⟨σ', h⟩
  · exact ⟨σ, Set.mem_singleton _⟩

/-- **The sporadic unblock check of the bind has an outcome**, an update of
the SC's refills (and possibly `reprogram_timer`). -/
theorem unblockBind_some {σ : State Unit} {c : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap c = some (.schedContext y n)) (hne : y.scRefills ≠ []) :
    ∃ σ3, ((), σ3) ∈ (ifSporadicActiveCurScTestRefillUnblockCheck (Z := Unit) (some c) σ).1 ∧
      ∃ z b, σ3 = updSc { σ with reprogramTimer := b } c z n ∧ z = { y with scRefills := z.scRefills } ∧
        z.scRefills ≠ [] := by
  rw [ifSporadicActive_some hk]
  split
  · obtain ⟨σ3, h3⟩ := refillUnblockCheck_some hk hne
    refine ⟨σ3, h3, ?_⟩
    rcases unblock_result hk hne h3 with ⟨rfl, -⟩ | ⟨z, rfl, -, -, hz, -, hzne, -⟩
    · exact ⟨y, σ3.reprogramTimer, (updSc_self hk).symm, rfl, hne⟩
    · exact ⟨z, true, rfl, hz, hzne⟩
  · exact ⟨σ, Set.mem_singleton _, y, σ.reprogramTimer, (updSc_self hk).symm, rfl, hne⟩

/-- **`ActReady` after the bind**: every other thread's SC and scheduling
facts are unchanged; the bound thread, if schedulable, has a ready and
sufficient head refill. -/
theorem actReady_bind {σ σ5 : State Unit} {t c : ObjRef} {x x1 : Tcb} {y z : SchedContext} {n : Nat}
    (hA : Notif.ActReady σ) (hkt : σ.kheap t = some (.tcb x)) (hkc : σ.kheap c = some (.schedContext y n))
    (hnot : ∀ u xu, σ.kheap u = some (.tcb xu) → xu.tcbSchedContext ≠ some c)
    (hk5 : ∀ u, u ≠ t → u ≠ c → σ5.kheap u = σ.kheap u) (hk5t : σ5.kheap t = some (.tcb x1))
    (hx1 : x1.tcbSchedContext = some c) (hk5c : σ5.kheap c = some (.schedContext z n)) (hzne : z.scRefills ≠ [])
    (hzact : scActive z = scActive y) (hct : σ5.curTime = σ.curTime)
    (hact : σ5.schedulerAction = σ.schedulerAction) (hrq : ∀ v ∈ σ.releaseQueue, v ∈ σ5.releaseQueue)
    (htt : schedulable t σ5 = true →
      refillReady σ5.curTime (refillHd z) = true ∧ refillSufficient 0 (refillHd z) = true) :
    Notif.ActReady σ5 := by
  intro u hu hs
  by_cases hut : u = t
  · subst hut
    obtain ⟨r1, r2⟩ := htt hs
    exact ⟨x1, c, hk5t, hx1, by rw [getScRefillSufficient_eq hk5c hzne, r2],
      by rw [getScRefillReady_eq hk5c hzne, r1]⟩
  have huc : u ≠ c := by
    rintro rfl
    rw [schedulable_notcb (by rw [tcbsOf_eq, hk5c])] at hs; cases hs
  have htc : t ≠ c := by rintro rfl; rw [hkt] at hkc; cases hkc
  have h1 : tcbsOf σ5 u = tcbsOf σ u := by rw [tcbsOf_eq, tcbsOf_eq, hk5 u hut huc]
  have h2 : ∀ p, Option.map scActive (scsOf σ5 p) = Option.map scActive (scsOf σ p) := by
    intro p
    rw [scsOf_eq, scsOf_eq]
    by_cases ept : p = t
    · subst ept; rw [hk5t, hkt]
    by_cases epc : p = c
    · subst epc; rw [hk5c, hkc]; simp [hzact]
    rw [hk5 p ept epc]
  have hs0 := schedulable_mono h1 h2 hrq hs
  obtain ⟨x0, scp, hk1, hsc1, h1', h2'⟩ := hA u (by rw [← hact]; exact hu) hs0
  have hsc : scp ≠ c := fun e => hnot u x0 hk1 (e ▸ hsc1)
  obtain ⟨yy, nn, hky, hne', hsuff⟩ := suff_inv h1'
  have hrdy := ready_inv h2' hky hne'
  have hst : scp ≠ t := by rintro rfl; rw [hkt] at hky; cases hky
  have hky5 : σ5.kheap scp = some (.schedContext yy nn) := by rw [hk5 scp hst hsc]; exact hky
  refine ⟨x0, scp, by rw [hk5 u hut huc]; exact hk1, hsc1, ?_, ?_⟩
  · rw [getScRefillSufficient_eq hky5 hne', hsuff]
  · rw [getScRefillReady_eq hky5 hne', hct, hrdy]

/-- **The spec's SC bind has an outcome** (l4v `sched_context_bind_tcb`), for
an unbound SC with refills and a thread with no SC, in no ready queue, when
the release queue's members are bound to SCs with refills, no TCB is bound
to the SC, and `ActReady` holds. -/
theorem schedContextBindTcb_some {σ : State Unit} {t c : ObjRef} {x : Tcb} {y : SchedContext} {n : Nat}
    (hkt : σ.kheap t = some (.tcb x)) (hxs : x.tcbSchedContext = none)
    (hkc : σ.kheap c = some (.schedContext y n)) (hyt : y.scTcb = none) (hne : y.scRefills ≠ [])
    (hnot : ∀ u xu, σ.kheap u = some (.tcb xu) → xu.tcbSchedContext ≠ some c)
    (hrq : ∀ d pr, t ∉ σ.readyQueues d pr)
    (hrel : ∀ u ∈ σ.releaseQueue, ∃ xu cu yu nu, σ.kheap u = some (.tcb xu) ∧ xu.tcbSchedContext = some cu ∧
      σ.kheap cu = some (.schedContext yu nu) ∧ yu.scRefills ≠ [])
    (hA : Notif.ActReady σ) :
    ∃ σc, ((), σc) ∈ (schedContextBindTcb (Z := Unit) c t σ).1 := by
  have htc : t ≠ c := by rintro rfl; rw [hkt] at hkc; cases hkc
  have htr : t ∉ σ.releaseQueue := by
    intro h; obtain ⟨xu, cu, -, -, hk, hs, -⟩ := hrel t h; rw [hkt] at hk; cases hk; rw [hxs] at hs; cases hs
  unfold schedContextBindTcb
  -- the links
  set x1 := tcbSchedContextUpdate (fun _ => some c) x with hx1
  rw [nd_bind_one (m := setTcbObjRef (Z := Unit) tcbSchedContextUpdate t (some c)) (Notif.threadSet_eq _ hkt)]
  set σ1 := Notif.updK σ t (.tcb x1) with hσ1
  have hk1c : σ1.kheap c = some (.schedContext y n) := by
    simp only [hσ1, Notif.updK, Function.update_of_ne (Ne.symm htc)]; exact hkc
  set y2 := scTcbUpdate (fun _ => some t) y with hy2
  rw [nd_bind_one (m := setScObjRef (Z := Unit) scTcbUpdate c (some t)) (updateSchedContext_eq hk1c _)]
  set σ2 := updSc σ1 c y2 n with hσ2
  have hk2c : σ2.kheap c = some (.schedContext y2 n) := by simp [hσ2, Notif.updK]
  -- the unblock check
  obtain ⟨σ3, hm3, z, b, hσ3, hz, hzne⟩ := unblockBind_some hk2c (by simpa [hy2, scTcbUpdate] using hne)
  refine Exists.imp (fun σc h => mem_bind_nd hm3 h) ?_
  dsimp only
  have hk3c : σ3.kheap c = some (.schedContext z n) := by simp [hσ3, Notif.updK]
  have hk3t : σ3.kheap t = some (.tcb x1) := by
    simp only [hσ3, hσ2, hσ1, Notif.updK, Function.update_of_ne htc, Function.update_self]
  have hk3 : ∀ u, u ≠ t → u ≠ c → σ3.kheap u = σ.kheap u := fun u h1 h2 => by
    simp only [hσ3, hσ2, hσ1, Notif.updK, Function.update_of_ne h1, Function.update_of_ne h2]
  have hzt : z.scTcb = some t := by rw [hz]; simp [hy2, scTcbUpdate]
  have hzact : scActive z = scActive y := by rw [hz]; simp [hy2, scTcbUpdate]
  have hrq3 : σ3.readyQueues = σ.readyQueues := by rw [hσ3]; simp [hσ2, hσ1, Notif.updK]
  have hrl3 : σ3.releaseQueue = σ.releaseQueue := by rw [hσ3]; simp [hσ2, hσ1, Notif.updK]
  have hct3 : σ3.curTime = σ.curTime := by rw [hσ3]; simp [hσ2, hσ1, Notif.updK]
  have hac3 : σ3.schedulerAction = σ.schedulerAction := by rw [hσ3]; simp [hσ2, hσ1, Notif.updK]
  have hx1c : x1.tcbSchedContext = some c := by simp [hx1, tcbSchedContextUpdate]
  have hrun : schedulable t σ3 = true → runnable x1.tcbState = true ∧ scActive z = true := by
    intro hs
    obtain ⟨x', scp, y', n', hk', hsc', hr', hky', ha', -⟩ := schedulable_inv hs
    rw [hk3t] at hk'; cases hk'
    rw [hx1c] at hsc'; cases hsc'
    rw [hk3c] at hky'; cases hky'
    exact ⟨hr', ha'⟩
  have hnq : schedulable t σ3 = true → t ∉ σ3.readyQueues x1.tcbDomain x1.tcbPriority := fun _ => by
    rw [hrq3]; exact hrq _ _
  have hres := resume_spec_eq hk3c hzt hk3t hzne hrun hnq
  -- the ready times of the release queue
  have hg : ∀ u, u = t ∨ u ∈ σ3.releaseQueue → ∃ xu scp yu nu, σ3.kheap u = some (.tcb xu) ∧
      xu.tcbSchedContext = some scp ∧ σ3.kheap scp = some (.schedContext yu nu) ∧ yu.scRefills ≠ [] ∧
      ((readTcbReadyTime (Z := Unit) u σ3).getD 0) = (refillHd yu).rTime := by
    rintro u (rfl | hu)
    · exact ⟨x1, c, z, n, hk3t, hx1c, hk3c, hzne, by rw [readTcbReadyTime_eq hk3t hx1c hk3c hzne]; rfl⟩
    · rw [hrl3] at hu
      obtain ⟨xu, cu, yu, nu, h1, h2, h3, h4⟩ := hrel u hu
      have hut : u ≠ t := fun e => htr (e ▸ hu)
      have huc : u ≠ c := by rintro rfl; rw [hkc] at h1; cases h1
      have hct' : cu ≠ t := by rintro rfl; rw [hkt] at h3; cases h3
      have hcc : cu ≠ c := fun e => hnot u xu h1 (e ▸ h2)
      have h1' : σ3.kheap u = some (.tcb xu) := by rw [hk3 u hut huc]; exact h1
      have h3' : σ3.kheap cu = some (.schedContext yu nu) := by rw [hk3 cu hct' hcc]; exact h3
      exact ⟨xu, cu, yu, nu, h1', h2, h3', h4, by rw [readTcbReadyTime_eq h1' h2 h3' h4]; rfl⟩
  -- the end: enqueue and reschedule
  have fin : ∀ σ4 : State Unit, σ4.kheap = σ3.kheap → σ4.curTime = σ.curTime →
      σ4.schedulerAction = σ.schedulerAction → (∀ v ∈ σ.releaseQueue, v ∈ σ4.releaseQueue) →
      (schedulable t σ4 = true → refillReady σ4.curTime (refillHd z) = true ∧
        refillSufficient 0 (refillHd z) = true) →
      ∃ σc, ((), σc) ∈ ((NonDet.gets (schedulable t) >>= fun sched => NonDet.when (sched = true) (do
        tcbSchedAction tcbSchedEnqueue t
        rescheduleRequired) : SMonad Unit Unit) σ4).1 := by
    intro σ4 hk4 hct4 hac4 hrl4 htt4
    rw [Notif.nd_gets_bind]
    unfold NonDet.when
    split
    · have hk4t : σ4.kheap t = some (.tcb x1) := by rw [hk4]; exact hk3t
      rw [nd_bind_one (tcbSchedAction_gen hk4t _)]
      have hA5 := actReady_bind (σ5 := setQ σ4 x1.tcbDomain x1.tcbPriority
          (tcbSchedEnqueue t (σ4.readyQueues x1.tcbDomain x1.tcbPriority))) hA hkt hkc hnot
        (fun u h1 h2 => by show σ4.kheap u = _; rw [hk4]; exact hk3 u h1 h2)
        (by show σ4.kheap t = _; exact hk4t) hx1c (by show σ4.kheap c = _; rw [hk4]; exact hk3c) hzne hzact
        hct4 hac4 hrl4 (fun hs => htt4 hs)
      obtain ⟨σ6, h6, -⟩ := rescheduleRequired_qchange hA5
      exact ⟨σ6, by rw [h6]; exact Set.mem_singleton _⟩
    · exact ⟨σ4, Set.mem_singleton _⟩
  split at hres
  · rename_i hcond
    obtain ⟨b', hb'⟩ := postpone_eq hk3c hzt hk3t _ hg
    rw [hb'] at hres
    rw [nd_bind_one hres]
    refine fin _ ?_ ?_ ?_ ?_ ?_
    · rfl
    · exact hct3
    · exact hac3
    · intro v hv; show v ∈ specInsT _ _ _; rw [mem_specInsT]; exact Or.inr (by rw [hrl3]; exact hv)
    · intro hs
      exfalso
      rw [schedulable_rel (by show t ∈ specInsT _ _ _; rw [mem_specInsT]; exact Or.inl rfl)] at hs
      cases hs
  · rename_i hcond
    rw [nd_bind_one hres]

    refine fin σ3 rfl hct3 hac3 (fun v hv => by rw [hrl3]; exact hv) ?_
    intro hs
    by_contra hc
    exact hcond ⟨hs, fun h => hc (by rw [hct3] at *; exact h)⟩

/-! ### The ready queues across `set_priority` of an unqueued, non-current thread -/

/-- Every outcome keeps the ready queues. -/
def PresQ {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → x.2.readyQueues = σ.readyQueues

theorem presQ_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : PresQ m)
    (hg : ∀ a, PresQ (g a)) : PresQ (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hg y.1 y.2 x hx).trans (hm σ y hy)

theorem presQ_pure {α : Type} (a : α) : PresQ (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

theorem presQ_gets {α : Type} (g : State Unit → α) : PresQ (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

theorem presQ_assert (P : Prop) : PresQ (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; rfl

theorem presQ_getsThe {α : Type} (g : State Unit → Option α) : PresQ (NonDet.getsThe g) := by
  intro σ x hx
  unfold NonDet.getsThe at hx
  cases h : g σ <;> rw [h] at hx
  · exact hx.elim
  · rw [Set.mem_singleton_iff.1 hx]

theorem presQ_setObject (p : ObjRef) (o : KernelObject) : PresQ (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨-, -, -, e⟩ := setObject_mem hx
  rw [e]

theorem presQ_threadSet (g : Tcb → Tcb) (t : ObjRef) : PresQ (threadSet (Z := Unit) g t) := by
  unfold threadSet
  exact presQ_bind (presQ_getsThe _) fun _ => presQ_setObject _ _

theorem presQ_getSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (p : ObjRef) :
    PresQ (getSimpleKo (Z := Unit) C p) := by
  unfold getSimpleKo
  refine presQ_bind (presQ_getsThe _) fun _ => presQ_bind (presQ_assert _) fun _ => ?_
  split
  · exact presQ_pure _
  · intro σ x hx; exact hx.elim

theorem presQ_setSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (p : ObjRef) (v : α) :
    PresQ (setSimpleKo (Z := Unit) C p v) := by
  unfold setSimpleKo
  exact presQ_bind (presQ_getsThe _) fun _ => presQ_bind (presQ_assert _) fun _ =>
    presQ_bind (presQ_assert _) fun _ => presQ_setObject _ _

theorem presQ_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, PresQ (g a)) (xs : List α) :
    PresQ (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact presQ_pure _
  | cons a xs' ih => exact presQ_bind (h a) fun _ => presQ_bind ih fun _ => presQ_pure _

theorem presQ_tcbAppend (t : ObjRef) (qs : List ObjRef) : PresQ (tcbAppend (Z := Unit) t qs) := by
  unfold tcbAppend orderedInsert
  exact presQ_bind (presQ_getsThe _) fun _ => presQ_bind (presQ_mapM (fun _ => presQ_getsThe _) _) fun _ =>
    presQ_bind (presQ_pure _) fun _ => presQ_bind (presQ_pure _) fun _ => presQ_pure _

theorem presQ_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, PresQ (g a)) (o : Option α) :
    PresQ (NonDet.maybeM g o) := by
  cases o
  · exact presQ_pure _
  · exact h _

/-- **`set_priority` of a thread in no ready queue that is not the current
thread keeps the ready queues.** -/
theorem setPriority_rq {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hnq : ∀ d pr, t ∉ σ.readyQueues d pr) (hnc : t ≠ σ.curThread) (pr : Priority) {σ' : State Unit}
    (h : ((), σ') ∈ (setPriority (Z := Unit) t pr σ).1) : σ'.readyQueues = σ.readyQueues := by
  unfold setPriority getThreadState at h
  rw [nd_bind_one (Notif.threadGet_eq _ hk)] at h
  split at h
  · rw [nd_bind_one (Notif.threadGet_eq _ hk), nd_bind_one (Notif.threadGet_eq _ hk),
      nd_bind_one (getTcbQueue_eq _ _ _), Notif.nd_gets_bind] at h
    split at h
    · rename_i hc; exact absurd hc (by simp [hnq, hnc])
    · exact presQ_threadSet _ _ σ _ h
  · refine presQ_bind (presQ_threadSet _ _) (fun _ => presQ_bind (presQ_maybeM (fun e => ?_) _)
      (fun _ => presQ_maybeM (fun n => ?_) _)) σ _ h
    · unfold reorderEp
      exact presQ_bind (presQ_getSimpleKo _ _) fun _ => presQ_bind (presQ_assert _) fun _ =>
        presQ_bind (presQ_pure _) fun _ => presQ_bind (presQ_assert _) fun _ =>
        presQ_bind (presQ_pure _) fun _ => presQ_bind (presQ_tcbAppend _ _) fun _ => presQ_setSimpleKo _ _ _
    · unfold reorderNtfn
      exact presQ_bind (presQ_getSimpleKo _ _) fun _ => presQ_bind (presQ_assert _) fun _ =>
        presQ_bind (presQ_pure _) fun _ => presQ_bind (presQ_assert _) fun _ =>
        presQ_bind (presQ_pure _) fun _ => presQ_bind (presQ_tcbAppend _ _) fun _ => presQ_setSimpleKo _ _ _

/-- The facts of the bind (`schedContextBindTcb_some`'s hypotheses). -/
def BindOK (σ : State Unit) (t c : ObjRef) : Prop :=
  ∃ x y n, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = none ∧ σ.kheap c = some (.schedContext y n) ∧
    y.scTcb = none ∧ y.scRefills ≠ [] ∧ (∀ u xu, σ.kheap u = some (.tcb xu) → xu.tcbSchedContext ≠ some c) ∧
    (∀ d pr, t ∉ σ.readyQueues d pr) ∧ t ≠ σ.curThread ∧
    (∀ u ∈ σ.releaseQueue, ∃ xu cu yu nu, σ.kheap u = some (.tcb xu) ∧ xu.tcbSchedContext = some cu ∧
      σ.kheap cu = some (.schedContext yu nu) ∧ yu.scRefills ≠ []) ∧ Notif.ActReady σ

/-- **`BindOK` across `set_mcpriority` and `set_priority`** of the thread. -/
theorem BindOK.after {σ σa σb : State Unit} {t c : ObjRef} (h : BindOK σ t c) (m pr : Priority)
    (ha : ((), σa) ∈ (setMcpriority (Z := Unit) t m σ).1) (hb : ((), σb) ∈ (setPriority (Z := Unit) t pr σa).1) :
    BindOK σb t c := by
  obtain ⟨x, y, n, hkt, hxs, hkc, hyt, hne, hnot, hrq, hnc, hrel, hA⟩ := h
  have va := presV_setMcpriority t m σ _ ha
  have vb := presV_setPriority t pr σa _ hb
  have hv := va.trans vb
  obtain ⟨xa, hka, -, -⟩ := va.tcb t x hkt
  have hqa : σa.readyQueues = σ.readyQueues := presQ_threadSet _ _ σ _ ha
  have hqb : σb.readyQueues = σa.readyQueues :=
    setPriority_rq hka (by rw [hqa]; exact hrq) (by rw [va.ct]; exact hnc) pr hb
  obtain ⟨xb, hkb, -, hsb⟩ := hv.tcb t x hkt
  have hnot' : ∀ u xu, σb.kheap u = some (.tcb xu) → xu.tcbSchedContext ≠ some c := by
    intro u xu hu
    obtain ⟨x0, hx0⟩ := hv.tcb' u xu hu
    obtain ⟨y', hy', -, hsc'⟩ := hv.tcb u x0 hx0
    rw [hu] at hy'; cases hy'
    rw [hsc']; exact hnot u x0 hx0
  refine ⟨xb, y, n, hkb, by rw [hsb, hxs], (hv.sc c y n).2 hkc, hyt, hne, hnot', by rw [hqb, hqa]; exact hrq,
    by rw [hv.ct]; exact hnc, fun u hu => ?_, hv.actReady hA⟩
  rw [hv.rq] at hu
  obtain ⟨xu, cu, yu, nu, h1, h2, h3, h4⟩ := hrel u hu
  obtain ⟨xu', h1', -, h2'⟩ := hv.tcb u xu h1
  exact ⟨xu', cu, yu, nu, h1', by rw [h2', h2], (hv.sc cu yu nu).2 h3, h4⟩

theorem scStep_some_bind {σ : State Unit} {t c : ObjRef} (h : BindOK σ t c) :
    ∃ σc, ((), σc) ∈ (scStep t (some (some c)) σ).1 := by
  obtain ⟨x, y, n, hkt, hxs, hkc, hyt, hne, hnot, hrq, -, hrel, hA⟩ := h
  exact schedContextBindTcb_some hkt hxs hkc hyt hne hnot hrq hrel hA

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`BindSpecHyp` from `BindOK` after the install** (the target with no
SC, the SC unbound with refills, no TCB on it, the target in no ready queue
and not current, the release queue's members bound, `ActReady`; l4v
`valid_sched` and the decoder's checks). -/
theorem bindSpecHyp_of (s : S) (σ : Fl4Spec.State Unit) (ct : U64)
    (hB2 : ∀ (s1 : S) (σ1 : Fl4Spec.State Unit) (a : A) (p scv x2 : U64) (ssl : Fl4Spec.CslotPtr)
      (fh : Fl4Spec.Cap × Fl4Spec.CslotPtr) (s2 : S) (a1 : A) (σ2 : Fl4Spec.State Unit),
      sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) → scv ≠ 0#u64 →
      tcb.install_tcb_cap st arI s1 a p (cslotAddr ssl) layout.tcb.SLOT_FAULT_HANDLER (capV (L.mem s) x2) x2 =
        ok (.Ok (), s2, a1) →
      (.ok (), σ2) ∈ ((Fl4Spec.installTcbCap (Z := Unit) p.bv ssl 3 (some fh)).run σ1).1 →
      BindOK σ2 p.bv scv.bv) :
    BindSpecHyp (L := L) arI s σ ct := by
  intro s1 σ1 a p mcp prio scv x2 scf ssl fh v s2 a1 σ2 σa σb hs1 hst1 _ hv hscv hins hx ha hb
  subst hv
  exact scStep_some_bind ((hB2 s1 σ1 a p scv x2 ssl fh s2 a1 σ2 hs1 hst1 hscv hins hx).after _ _ ha hb)

end

end

end Fl4Proofs.P3.Sched
