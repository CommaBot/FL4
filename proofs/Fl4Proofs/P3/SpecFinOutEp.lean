/-
P3 (DESIGN.md §9), CSpace: **the spec's finalisation of a final endpoint
cap has an outcome** (`finEp_out`, `specFinOut_ep`: the Endpoint case of
`SpecFinOut`), from `EpPre`: the endpoint exists, its queue is a
duplicate-free list of TCBs with ready and sufficient SCs (`MemOK`, l4v's
`released_ipc_queues`) and, for a receiver with a reply, the reply bound to
it (`RepOK`); `ScBack`; `ActReady`. As for notifications (SpecFinOut), with
`cancel_all_ipc`'s loop: each queued thread is dequeued, its reply (if a
receiver's) unlinked and the thread made inactive, then restarted unless it
has a fault (`restart_tail`: the restart, the refill check and the switch).
-/
import Fl4Proofs.P3.SpecFinOut
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section Spec
open Fl4Spec Classical

/-- A receiver's reply, bound to it. -/
def RepOK (σ : State Unit) (t : ObjRef) : Prop :=
  ∀ x, σ.kheap t = some (.tcb x) → ∀ ep r d, x.tcbState = .blockedOnReceive ep (some r) d →
    ∃ xr, σ.kheap r = some (.reply xr) ∧ xr.replyTcb = some t

/-- A TCB's SC facts (`MemOK`'s, for a given TCB). -/
def ScOK (σ : State Unit) (x : Tcb) : Prop :=
  ∀ c, x.tcbSchedContext = some c → ∃ y k, σ.kheap c = some (.schedContext y k) ∧
    y.scRefills ≠ [] ∧
    (scActive y = true → refillReady σ.curTime (refillHd y) = true ∧ refillSufficient 0 (refillHd y) = true) ∧
    (scActive y = true → y.scPeriod ≠ 0 → RefOK y)

/-- **The restart, the refill check and the switch** of a thread `t` whose
SC is ready and sufficient: an outcome keeping `ScBack` and `ActReady`, the
time, `t` a TCB with its SC, and every object but `t` and its SC. -/
theorem restart_tail {σ : State Unit} {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x))
    (hxs : ScOK σ x) (hB : ScBack σ) (hA : ActReady σ) :
    ∃ σ', ((), σ') ∈ ((setThreadState (Z := Unit) t .restart >>= fun _ =>
        getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= fun scOpt =>
        ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) scOpt >>= fun _ => possibleSwitchTo (Z := Unit) t) σ).1 ∧
      ScBack σ' ∧ ActReady σ' ∧ σ'.curTime = σ.curTime ∧
      (∃ x', σ'.kheap t = some (.tcb x') ∧ x'.tcbSchedContext = x.tcbSchedContext) ∧
      ∀ p, p ≠ t → x.tcbSchedContext ≠ some p → σ'.kheap p = σ.kheap p := by
  -- the restart
  set x' : Tcb := { x with tcbState := .restart } with hx'
  set σ2' := updK σ t (.tcb x') with hσ2'
  have hkp2 : ∀ p, p ≠ t → σ2'.kheap p = σ.kheap p := fun p hp => by
    simp only [hσ2', updK, Function.update_of_ne hp]
  have hkt2 : σ2'.kheap t = some (.tcb x') := by simp [hσ2', updK]
  have hT2 : schedulable t σ2' = true → RdyAt σ2' t := by
    intro hs
    obtain ⟨x0, c, y0, k0, hk0, hsc0, -, hky0, hact0, -⟩ := schedulable_inv hs
    rw [hkt2] at hk0; cases hk0
    obtain ⟨y, k, hky, hne, h12, -⟩ := hxs c hsc0
    have hct : c ≠ t := by rintro rfl; rw [hkt] at hky; cases hky
    rw [hkp2 c hct, hky] at hky0; cases hky0
    obtain ⟨h1, h2⟩ := h12 hact0
    exact ⟨x', c, _, _, hkt2, hsc0, by rw [hkp2 c hct]; exact hky, hne, h1, h2⟩
  have hA2' : ActReady σ2' := by
    rw [actReady_iff] at hA ⊢
    intro u hu hs
    by_cases e : u = t
    · subst e; exact hT2 hs
    · have hK := tcbUpd_keeps (x' := x') hkt rfl e
      exact hK.1 (hA u hu (by rw [← hK.2.2]; exact hs))
  have hst := setThreadState_eq' hkt .restart
  set σ2 := stsAct σ2' t with hσ2
  obtain ⟨hk2, ht2, hr2, ha2⟩ := stsAct_heap σ2' t
  have hF2 : SFr σ2' σ2 := SFr.of_heap hk2 ht2 hr2
  have hA2 : ActReady σ2 := hF2.actReady hA2' ha2
  have hT2'' : schedulable t σ2 = true → RdyAt σ2 t := fun hs =>
    hF2.rdyAt (hT2 (by rw [← hF2.schedulable]; exact hs))
  have hB2' : ScBack σ2' := by
    intro u xu c hku hc
    by_cases e : u = t
    · subst e; rw [hkt2] at hku; cases hku
      obtain ⟨y, k, hky, hyt, hne⟩ := hB u x c hkt hc
      have hct : c ≠ u := by rintro rfl; rw [hkt] at hky; cases hky
      exact ⟨y, k, by rw [hkp2 c hct]; exact hky, hyt, hne⟩
    · rw [hkp2 u e] at hku
      obtain ⟨y, k, hky, hyt, hne⟩ := hB u xu c hku hc
      have hct : c ≠ t := by rintro rfl; rw [hkt] at hky; cases hky
      exact ⟨y, k, by rw [hkp2 c hct]; exact hky, hyt, hne⟩
  have hB2 := hF2.scBack hB2'
  have hkt2' : σ2.kheap t = some (.tcb x') := by rw [hk2]; exact hkt2
  have hkp2' : ∀ p, p ≠ t → σ2.kheap p = σ.kheap p := fun p hp => by rw [hk2, hkp2 p hp]
  rw [nd_bind_one hst, nd_bind_one (show getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t σ2 = _ from threadGet_eq _ hkt2')]
  suffices hS : ∃ σ3, ((), σ3) ∈ (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) x'.tcbSchedContext σ2).1 ∧
      σ3.kheap t = some (.tcb x') ∧ ScBack σ3 ∧ ActReady σ3 ∧ (schedulable t σ3 = true → RdyAt σ3 t) ∧
      σ3.curTime = σ.curTime ∧ ∀ p, p ≠ t → x.tcbSchedContext ≠ some p → σ3.kheap p = σ.kheap p by
    obtain ⟨σ3, hm3, hkt3, hB3, hA3, hT3, ht3, hkp3⟩ := hS
    obtain ⟨σ4, he4, hk4, ht4, hr4, ha4⟩ := pst_ok hkt3 hA3
    have hF4 := SFr.of_heap hk4 ht4 hr4
    refine ⟨σ4, mem_bind_nd hm3 (by rw [he4]; exact Set.mem_singleton _), hF4.scBack hB3,
      pst_actReady hA3 hT3 hk4 ht4 hr4 ha4, by rw [ht4, ht3], ⟨x', by rw [hk4]; exact hkt3, rfl⟩,
      fun p hp hpc => by rw [hk4, hkp3 p hp hpc]⟩
  cases hxc : x'.tcbSchedContext with
  | none =>
    exact ⟨σ2, Set.mem_singleton _, hkt2', hB2, hA2, hT2'', by rw [ht2]; rfl, fun p hp _ => hkp2' p hp⟩
  | some c =>
    have hxc' : x.tcbSchedContext = some c := hxc
    obtain ⟨y, k, hky1, hne, -, hrf⟩ := hxs c hxc'
    have hct : c ≠ t := by rintro rfl; rw [hkt] at hky1; cases hky1
    have hky2 : σ2.kheap c = some (.schedContext y k) := by rw [hkp2' c hct]; exact hky1
    obtain ⟨σ3, hm3, hcase⟩ := unblockCur_some hky2 hne
    rcases hcase with rfl | ⟨z, rfl, hRz, hrt3, hz, hzne, hper⟩
    · exact ⟨σ2, hm3, hkt2', hB2, hA2, hT2'', by rw [ht2]; rfl, fun p hp _ => hkp2' p hp⟩
    · obtain ⟨yb, kb, hkyb, hybt, -⟩ := hB2 t x' c hkt2' hxc
      rw [hky2] at hkyb; cases hkyb
      set σ3 := updSc { σ2 with reprogramTimer := true } c z k with hσ3
      have hkp3 : ∀ p, p ≠ c → σ3.kheap p = σ2.kheap p := fun p hp => by
        simp only [hσ3, updSc, updK, Function.update_of_ne hp]
      have hkc3 : σ3.kheap c = some (.schedContext z k) := by simp [hσ3, updSc, updK]
      have hzact : scActive z = scActive y := by rw [hz]
      have hzt : z.scTcb = y.scTcb := by rw [hz]
      have hsch : ∀ u, schedulable u σ3 = schedulable u σ2 := by
        intro u
        apply schedulable_upd
        · rw [tcbsOf_eq, tcbsOf_eq]
          by_cases e : u = c
          · subst e; rw [hkc3, hky2]
          · rw [hkp3 u e]
        · intro p
          rw [scsOf_eq, scsOf_eq]
          by_cases e : p = c
          · subst e; rw [hkc3, hky2]; simp [hzact]
          · rw [hkp3 p e]
        · rfl
      have ht3 : σ3.curTime = σ2.curTime := rfl
      have hT3 : schedulable t σ3 = true → RdyAt σ3 t := by
        intro hs
        obtain ⟨x0, c0, y0, k0, hk0, hsc0, -, hky0, hact0, -⟩ := schedulable_inv hs
        rw [hkp3 t (Ne.symm hct), hkt2'] at hk0; cases hk0
        rw [hxc] at hsc0; cases hsc0
        rw [hkc3] at hky0; cases hky0
        have hRy : RefOK y := hrf (by rw [← hzact]; exact hact0) hper
        have hR := hRz hRy
        refine ⟨x', c, z, k, by rw [hkp3 t (Ne.symm hct)]; exact hkt2', hxc, hkc3, hzne, ?_, suff_of_min hR.2.2.2⟩
        rw [ht3]
        simp only [refillReady, refillReady', hrt3, decide_eq_true_eq]
        exact BitVec.le_of_eq (by simp)
      have hother : ∀ u xu cu, σ2.kheap u = some (.tcb xu) → xu.tcbSchedContext = some cu → u ≠ t → cu ≠ c := by
        intro u xu cu hku hcu hut e
        subst e
        obtain ⟨yu, ku, hkyu, hyut, -⟩ := hB2 u xu cu hku hcu
        rw [hky2] at hkyu; cases hkyu
        rw [hybt] at hyut; cases hyut; exact hut rfl
      refine ⟨σ3, hm3, by rw [hkp3 t (Ne.symm hct)]; exact hkt2', ?_, ?_, hT3, by rw [ht3, ht2]; rfl,
        fun p hp hpc => by rw [hkp3 p (fun e => hpc (by subst e; first | rfl | exact hxc')), hkp2' p hp]⟩
      · intro u xu cu hku hcu
        by_cases e : u = c
        · subst e; rw [hkc3] at hku; cases hku
        rw [hkp3 u e] at hku
        obtain ⟨yu, ku, h1, h2, h3⟩ := hB2 u xu cu hku hcu
        by_cases e2 : cu = c
        · subst e2; rw [hky2] at h1; cases h1
          exact ⟨z, _, hkc3, by rw [hzt]; exact h2, hzne⟩
        · exact ⟨yu, ku, by rw [hkp3 cu e2]; exact h1, h2, h3⟩
      · rw [actReady_iff] at hA2 ⊢
        intro u hu hs
        by_cases e : u = t
        · subst e; exact hT3 hs
        · have hu2 : σ2.schedulerAction = .switchThread u := hu
          obtain ⟨xu, cu, yu, ku, h1, h2, h3, h4, h5, h6⟩ := hA2 u hu2 (by rw [← hsch]; exact hs)
          have huc : u ≠ c := by rintro rfl; rw [hky2] at h1; cases h1
          have hcc := hother u xu cu h1 h2 e
          exact ⟨xu, cu, yu, ku, by rw [hkp3 u huc]; exact h1, h2, by rw [hkp3 cu hcc]; exact h3, h4,
            by rw [ht3]; exact h5, h6⟩

/-- **Making `t` inactive** keeps `ScBack` and `ActReady` (an inactive thread
is no schedulable switch target). -/
theorem inactive_ok {σ : State Unit} {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x)) (hB : ScBack σ)
    (hA : ActReady σ) :
    ∃ σ', setThreadState (Z := Unit) t .inactive σ = ({((), σ')}, False) ∧ ScBack σ' ∧ ActReady σ' ∧
      σ'.curTime = σ.curTime ∧ σ'.kheap t = some (.tcb { x with tcbState := .inactive }) ∧
      ∀ p, p ≠ t → σ'.kheap p = σ.kheap p := by
  set x' : Tcb := { x with tcbState := .inactive } with hx'
  set σ2' := updK σ t (.tcb x') with hσ2'
  have hkp2 : ∀ p, p ≠ t → σ2'.kheap p = σ.kheap p := fun p hp => by
    simp only [hσ2', updK, Function.update_of_ne hp]
  have hkt2 : σ2'.kheap t = some (.tcb x') := by simp [hσ2', updK]
  have hA2' : ActReady σ2' := by
    rw [actReady_iff] at hA ⊢
    intro u hu hs
    by_cases e : u = t
    · subst e
      obtain ⟨x0, -, -, -, hk0, -, hr0, -⟩ := schedulable_inv hs
      rw [hkt2] at hk0; cases hk0
      simp [hx', runnable] at hr0
    · have hK := tcbUpd_keeps (x' := x') hkt rfl e
      exact hK.1 (hA u hu (by rw [← hK.2.2]; exact hs))
  have hB2' : ScBack σ2' := by
    intro u xu c hku hc
    by_cases e : u = t
    · subst e; rw [hkt2] at hku; cases hku
      obtain ⟨y, k, hky, hyt, hne⟩ := hB u x c hkt hc
      have hct : c ≠ u := by rintro rfl; rw [hkt] at hky; cases hky
      exact ⟨y, k, by rw [hkp2 c hct]; exact hky, hyt, hne⟩
    · rw [hkp2 u e] at hku
      obtain ⟨y, k, hky, hyt, hne⟩ := hB u xu c hku hc
      have hct : c ≠ t := by rintro rfl; rw [hkt] at hky; cases hky
      exact ⟨y, k, by rw [hkp2 c hct]; exact hky, hyt, hne⟩
  obtain ⟨hk2, ht2, hr2, ha2⟩ := stsAct_heap σ2' t
  have hF2 : SFr σ2' (stsAct σ2' t) := SFr.of_heap hk2 ht2 hr2
  exact ⟨_, setThreadState_eq' hkt .inactive, hF2.scBack hB2', hF2.actReady hA2' ha2, by rw [ht2]; rfl,
    by rw [hk2]; exact hkt2, fun p hp => by rw [hk2, hkp2 p hp]⟩


/-- **`restart_thread_if_no_fault`** of a TCB with ready SC facts: an
outcome keeping `ScBack`, `ActReady`, the time, and every object but the
thread and its SC. -/
theorem rtinf_ok {σ : State Unit} {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x))
    (hxs : ScOK σ x) (hB : ScBack σ) (hA : ActReady σ) :
    ∃ σ', ((), σ') ∈ (restartThreadIfNoFault (Z := Unit) t σ).1 ∧ ScBack σ' ∧ ActReady σ' ∧
      σ'.curTime = σ.curTime ∧ ∀ p, p ≠ t → x.tcbSchedContext ≠ some p → σ'.kheap p = σ.kheap p := by
  unfold restartThreadIfNoFault
  rw [nd_bind_one (threadGet_eq _ hkt)]
  split_ifs
  · obtain ⟨σ', h, hB', hA', ht', -, hkp⟩ := restart_tail hkt hxs hB hA
    exact ⟨σ', h, hB', hA', ht', hkp⟩
  · obtain ⟨σ', he, hB', hA', ht', -, hkp⟩ := inactive_ok hkt hB hA
    exact ⟨σ', by rw [he]; exact Set.mem_singleton _, hB', hA', ht', fun p hp _ => hkp p hp⟩

theorem epDeq_queue {x : Endpoint} {t : ObjRef} {l : List ObjRef} (hq : x.epQueue = t :: l)
    (hnd : (t :: l).Nodup) : (epDeq x t).epQueue = l := by
  have hr : removeAll t x.epQueue = l := by
    have ht : t ∉ l := (List.nodup_cons.1 hnd).1
    rw [hq]; unfold removeAll
    simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact List.filter_eq_self.2 fun a ha => by
      simp only [ne_eq, decide_eq_true_eq]; rintro rfl; exact ht ha
  unfold epDeq
  rw [hr]
  cases l with
  | nil => rfl
  | cons a l => cases x <;> simp_all [updateEpQueue, Endpoint.epQueue]

/-- A queued thread's facts at a state agreeing on what they read. -/
theorem memRep_agree {σ σ' : State Unit} {u : ObjRef} (hm : MemOK σ u) (hr : RepOK σ u) (K : ObjRef → Prop)
    (hag : ∀ p, K p → σ'.kheap p = σ.kheap p) (ht : σ'.curTime = σ.curTime) (hu : K u)
    (hsc : ∀ x c, σ.kheap u = some (.tcb x) → x.tcbSchedContext = some c → K c)
    (hrep : ∀ x ep r d, σ.kheap u = some (.tcb x) → x.tcbState = .blockedOnReceive ep (some r) d → K r) :
    MemOK σ' u ∧ RepOK σ' u := by
  obtain ⟨x, hku, hc⟩ := hm
  refine ⟨⟨x, by rw [hag u hu]; exact hku, fun c e => ?_⟩, fun x' hku' ep r d hst => ?_⟩
  · obtain ⟨y, k, h1, h2⟩ := hc c e
    exact ⟨y, k, by rw [hag c (hsc x c hku e)]; exact h1, by rw [ht]; exact h2⟩
  · rw [hag u hu, hku] at hku'; cases hku'
    obtain ⟨xr, h1, h2⟩ := hr x hku ep r d hst
    exact ⟨xr, by rw [hag r (hrep x ep r d hku hst)]; exact h1, h2⟩

/-- **One thread of `cancel_all_ipc`** (`remove_and_restart_ep_queued_thread`). -/
theorem ep_iter {σ : State Unit} {e t : ObjRef} {l : List ObjRef} {x : Endpoint}
    (hk : σ.kheap e = some (.endpoint x)) (hq : x.epQueue = t :: l) (hnd : (t :: l).Nodup)
    (hm : ∀ u ∈ t :: l, MemOK σ u ∧ RepOK σ u) (hB : ScBack σ) (hA : ActReady σ) :
    ∃ σ5, ((), σ5) ∈ (removeAndRestartEpQueuedThread (Z := Unit) t e σ).1 ∧
      (∃ x5, σ5.kheap e = some (.endpoint x5) ∧ x5.epQueue = l) ∧
      (∀ u ∈ l, MemOK σ5 u ∧ RepOK σ5 u) ∧ ScBack σ5 ∧ ActReady σ5 := by
  have htl : t ∉ l := (List.nodup_cons.1 hnd).1
  obtain ⟨⟨xt, hkt, hxs⟩, hrt⟩ := hm t (List.mem_cons_self ..)
  have het : e ≠ t := by rintro rfl; rw [hk] at hkt; cases hkt
  -- the dequeue
  have hdq := tcbEpDequeue_eq hk (by rw [hq]; exact List.mem_cons_self ..)
  set σ1 := updK σ e (.endpoint (epDeq x t)) with hσ1
  have hF1 : SFr σ σ1 := SFr.updOther hk (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ h => by cases h)
    (fun _ _ h => by cases h)
  have hkp1 : ∀ p, p ≠ e → σ1.kheap p = σ.kheap p := fun p hp => by simp only [hσ1, updK, Function.update_of_ne hp]
  have hkt1 : σ1.kheap t = some (.tcb xt) := by rw [hkp1 t (Ne.symm het)]; exact hkt
  have hB1 := hF1.scBack hB
  have hA1 := hF1.actReady hA (Or.inl rfl)
  -- the reply
  obtain ⟨ro, hro⟩ : ∃ ro : Option ObjRef,
      ro = if isBlockedOnReceive xt.tcbState then replyObject xt.tcbState else none := ⟨_, rfl⟩
  have hroP : ∀ r, ro = some r → (∃ xr, σ.kheap r = some (.reply xr) ∧ xr.replyTcb = some t) ∧
      ∃ ep d, xt.tcbState = .blockedOnReceive ep (some r) d := by
    intro r hr
    by_cases hb : isBlockedOnReceive xt.tcbState
    · obtain ⟨ep, ro', d, hs⟩ := hb
      rw [hro, if_pos ⟨ep, ro', d, hs⟩, hs] at hr
      simp only [replyObject] at hr; subst hr
      exact ⟨hrt xt hkt ep r d hs, ep, d, hs⟩
    · rw [hro, if_neg hb] at hr; cases hr
  have hstep2 : ∃ σ2, NonDet.maybeM (replyUnlinkTcb (Z := Unit) t) ro σ1 = ({((), σ2)}, False) ∧
      ScBack σ2 ∧ ActReady σ2 ∧ σ2.curTime = σ.curTime ∧
      (∃ x2, σ2.kheap t = some (.tcb x2) ∧ x2.tcbSchedContext = xt.tcbSchedContext) ∧
      ∀ p, p ≠ t → ro ≠ some p → σ2.kheap p = σ1.kheap p := by
    rcases Option.eq_none_or_eq_some ro with hr | ⟨r, hr⟩
    · rw [hr]
      exact ⟨σ1, rfl, hB1, hA1, rfl, ⟨xt, hkt1, rfl⟩, fun p _ _ => rfl⟩
    · obtain ⟨⟨xr, hkr, hxrt⟩, ep, d, hst⟩ := hroP r hr
      rw [hr]
      have hre : r ≠ e := by rintro rfl; rw [hk] at hkr; cases hkr
      have hkr1 : σ1.kheap r = some (.reply xr) := by rw [hkp1 r hre]; exact hkr
      have htr : t ≠ r := by rintro rfl; rw [hkt] at hkr; cases hkr
      simp only [NonDet.maybeM]
      rw [replyUnlinkTcb_eq hkr1 hxrt hkt1 (Or.inr ⟨ep, d, hst⟩) htr]
      set σ1' := updK σ1 r (.reply { xr with replyTcb := none }) with hσ1'
      have hF1' : SFr σ1 σ1' := SFr.updOther hkr1 (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ h => by cases h) (fun _ _ h => by cases h)
      have hkt1' : σ1'.kheap t = some (.tcb xt) := by
        simp only [hσ1', updK, Function.update_of_ne htr]; exact hkt1
      obtain ⟨σ2, he2, hB2, hA2, ht2, hkt2, hkp2⟩ :=
        inactive_ok hkt1' (hF1'.scBack hB1) (hF1'.actReady hA1 (Or.inl rfl))
      refine ⟨σ2, he2, hB2, hA2, by rw [ht2]; rfl, ⟨_, hkt2, rfl⟩, fun p hpt hpr => ?_⟩
      have hpr' : p ≠ r := fun h => hpr (by subst h; rfl)
      rw [hkp2 p hpt]; simp only [hσ1', updK, Function.update_of_ne hpr']
  obtain ⟨σ2, he2, hB2, hA2, ht2, ⟨x2, hkt2, hsc2⟩, hkp2⟩ := hstep2
  have hscP : ∀ c, x2.tcbSchedContext = some c → ∃ y k, σ.kheap c = some (.schedContext y k) ∧ y.scTcb = some t := by
    intro c hc
    obtain ⟨y, k, h1, hyt, -⟩ := hB t xt c hkt (by rw [← hsc2]; exact hc)
    exact ⟨y, k, h1, hyt⟩
  have hxs2 : ScOK σ2 x2 := fun c hc => by
    obtain ⟨y, k, h1, h2⟩ := hxs c (by rw [← hsc2]; exact hc)
    have hct : c ≠ t := by rintro rfl; rw [hkt] at h1; cases h1
    have hce : c ≠ e := by rintro rfl; rw [hk] at h1; cases h1
    have hcr : ro ≠ some c := fun hr => by
      obtain ⟨⟨xr, hkr, -⟩, -⟩ := hroP c hr
      rw [h1] at hkr; cases hkr
    exact ⟨y, k, by rw [hkp2 c hct hcr, hkp1 c hce]; exact h1, by rw [ht2]; exact h2⟩
  -- the restart
  obtain ⟨σ5, hm5, hB5, hA5, ht5, hkp5⟩ := rtinf_ok hkt2 hxs2 hB2 hA2
  -- the membership
  unfold removeAndRestartEpQueuedThread
  rw [nd_bind_one hdq, nd_bind_one (getThreadState_eq hkt1), nd_pure_bind', ← hro, nd_bind_one he2]
  have hkeep : ∀ p, p ≠ t → p ≠ e → ro ≠ some p → x2.tcbSchedContext ≠ some p → σ5.kheap p = σ.kheap p :=
    fun p h1 h2 h3 h4 => by rw [hkp5 p h1 h4, hkp2 p h1 h3, hkp1 p h2]
  refine ⟨σ5, hm5, ⟨epDeq x t, ?_, epDeq_queue hq hnd⟩, fun u hu => ?_, hB5, hA5⟩
  · have hed : x2.tcbSchedContext ≠ some e := fun h => by
      obtain ⟨y, k, h1, -⟩ := hscP e h
      rw [hk] at h1; cases h1
    have her : ro ≠ some e := fun hr => by
      obtain ⟨⟨xr, hkr, -⟩, -⟩ := hroP e hr
      rw [hk] at hkr; cases hkr
    rw [hkp5 e het hed, hkp2 e het her, hσ1]
    simp [updK]
  · obtain ⟨hmu, hru⟩ := hm u (List.mem_cons_of_mem _ hu)
    have hut : u ≠ t := fun h => htl (h ▸ hu)
    obtain ⟨xu, hku, hcu⟩ := hmu
    refine memRep_agree ⟨xu, hku, hcu⟩ hru (fun p => p ≠ t ∧ p ≠ e ∧ ro ≠ some p ∧ x2.tcbSchedContext ≠ some p)
      (fun p ⟨h1, h2, h3, h4⟩ => hkeep p h1 h2 h3 h4) (by rw [ht5, ht2]) ?_ ?_ ?_
    · beta_reduce
      refine ⟨hut, (by rintro rfl; rw [hk] at hku; cases hku), fun h => ?_, fun h => ?_⟩
      · obtain ⟨⟨xr, h1, -⟩, -⟩ := hroP u h; rw [hku] at h1; cases h1
      · obtain ⟨y, k, h1, -⟩ := hscP u h; rw [hku] at h1; cases h1
    · intro x0 c hk0 hc0
      rw [hku] at hk0; cases hk0
      obtain ⟨y, k, h1, -⟩ := hcu c hc0
      beta_reduce
      refine ⟨(by rintro rfl; rw [hkt] at h1; cases h1), (by rintro rfl; rw [hk] at h1; cases h1), fun h => ?_,
        fun h => ?_⟩
      · obtain ⟨⟨xr, h2, -⟩, -⟩ := hroP c h; rw [h1] at h2; cases h2
      · obtain ⟨y', k', h2, h3⟩ := hscP c h
        rw [h1] at h2; cases h2
        obtain ⟨y'', k'', h4, h5, -⟩ := hB u xu c hku hc0
        rw [h1] at h4; cases h4
        rw [h3] at h5; cases h5; exact hut rfl
    · intro x0 ep r d hk0 hs0
      obtain ⟨xr, h1, h2⟩ := hru x0 hk0 ep r d hs0
      beta_reduce
      refine ⟨(by rintro rfl; rw [hkt] at h1; cases h1), (by rintro rfl; rw [hk] at h1; cases h1), fun h => ?_,
        fun h => ?_⟩
      · obtain ⟨⟨xr', h3, h4⟩, -⟩ := hroP r h
        rw [h1] at h3; cases h3; rw [h2] at h4; cases h4; exact hut rfl
      · obtain ⟨y, k, h3, -⟩ := hscP r h; rw [h1] at h3; cases h3


/-- **The loop of `cancel_all_ipc`** over the endpoint's queue. -/
theorem ep_loop {e : ObjRef} :
    ∀ (l : List ObjRef) (σ : State Unit), (∃ x, σ.kheap e = some (.endpoint x) ∧ x.epQueue = l) →
      l.Nodup → (∀ u ∈ l, MemOK σ u ∧ RepOK σ u) → ScBack σ → ActReady σ →
      ∃ σ', ((), σ') ∈ (NonDet.mapMx (fun t => removeAndRestartEpQueuedThread (Z := Unit) t e) l σ).1 ∧
        ActReady σ'
  | [], σ, _, _, _, _, hA => ⟨σ, Set.mem_singleton _, hA⟩
  | t :: l, σ, ⟨x, hk, hq⟩, hnd, hm, hB, hA => by
    obtain ⟨σ5, h5, hq5, hm5, hB5, hA5⟩ := ep_iter hk hq hnd hm hB hA
    obtain ⟨σ', h', hA'⟩ := ep_loop l σ5 hq5 (List.nodup_cons.1 hnd).2 hm5 hB5 hA5
    exact ⟨σ', mem_bind_nd h5 h', hA'⟩

/-- **What the finalisation of an endpoint cap needs of the spec state**:
the endpoint exists; its queue is a duplicate-free list of queued threads'
facts (`MemOK`, and a receiver's reply bound to it, `RepOK`); `ScBack`;
`ActReady`. -/
def EpPre (σ : State Unit) (r : ObjRef) : Prop :=
  ∃ x, σ.kheap r = some (.endpoint x) ∧ x.epQueue.Nodup ∧ (∀ u ∈ x.epQueue, MemOK σ u ∧ RepOK σ u) ∧
    ScBack σ ∧ ActReady σ

/-- **`cancel_all_ipc` has an outcome.** -/
theorem cia_out {σ : State Unit} {r : ObjRef} (h : EpPre σ r) :
    ∃ σ', ((), σ') ∈ (cancelAllIpc (Z := Unit) r σ).1 := by
  obtain ⟨x, hk, hnd, hm, hB, hA⟩ := h
  have hbody : ∃ σ', ((), σ') ∈ ((NonDet.mapMx (fun t => removeAndRestartEpQueuedThread (Z := Unit) t r) x.epQueue
      >>= fun _ => rescheduleRequired (Z := Unit)) σ).1 := by
    obtain ⟨σ', h', hA'⟩ := ep_loop x.epQueue σ ⟨x, hk, rfl⟩ hnd hm hB hA
    obtain ⟨σ'', he, -⟩ := resched_ok hA'
    exact ⟨σ'', mem_bind_nd h' (by rw [he]; exact Set.mem_singleton _)⟩
  unfold cancelAllIpc
  rw [nd_bind_one (getEndpoint_eq hk)]
  cases x with
  | idleEP => exact ⟨σ, Set.mem_singleton _⟩
  | sendEP q =>
    obtain ⟨σ', h'⟩ := hbody
    exact ⟨σ', by simp only; rw [nd_pure_bind']; exact h'⟩
  | recvEP q =>
    obtain ⟨σ', h'⟩ := hbody
    exact ⟨σ', by simp only; rw [nd_pure_bind']; exact h'⟩

/-- `EpPre` from the Sc side's `Inv` and `ActReady`, and the queued threads:
distinct TCBs with ready and sufficient SCs (l4v's `released_ipc_queues`),
a receiver's reply bound to it. -/
theorem epPre_of_inv {σ : State Unit} {r : ObjRef} {x : Endpoint} (hI : Inv σ) (hA : ActReady σ)
    (hk : σ.kheap r = some (.endpoint x)) (hnd : x.epQueue.Nodup)
    (hq : ∀ u ∈ x.epQueue, ∃ xu, σ.kheap u = some (.tcb xu) ∧ (∀ c, xu.tcbSchedContext = some c →
      ∀ y k, σ.kheap c = some (.schedContext y k) → scActive y = true →
        refillReady σ.curTime (refillHd y) = true ∧ refillSufficient 0 (refillHd y) = true) ∧ RepOK σ u) :
    EpPre σ r := by
  refine ⟨x, hk, hnd, fun u hu => ?_, fun u xu c hku hc => ?_, hA⟩
  · obtain ⟨xu, hku, hc, hr⟩ := hq u hu
    refine ⟨⟨xu, hku, fun c e => ?_⟩, hr⟩
    obtain ⟨y, k, hky, -⟩ := hI.back u xu c hku e
    exact ⟨y, k, hky, hI.ne c y k hky, hc c e y k hky, fun ha hp => hI.refills c y k hky ha hp⟩
  · obtain ⟨y, k, hky, hyt⟩ := hI.back u xu c hku hc
    exact ⟨y, k, hky, hyt, hI.ne c y k hky⟩

/-- **The spec's finalisation of a final endpoint cap has an outcome.** -/
theorem finEp_out {σ : State Unit} {r : ObjRef} (b : Badge) (R : CapRights) (h : EpPre σ r) :
    ∃ σ', ((Cap.nullCap, Cap.nullCap), σ') ∈ (finaliseCap (Z := Unit) (.endpointCap r b R) true σ).1 := by
  obtain ⟨σ', h'⟩ := cia_out h
  refine ⟨σ', ?_⟩
  unfold finaliseCap
  simp only [NonDet.liftM, NonDet.when, ↓reduceIte]
  exact mem_bind_nd (x := ((), σ')) h' (Set.mem_singleton _)

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The spec's side of a final endpoint cap's finalisation**: the spec
state meets `EpPre` at the endpoint. -/
def EpSpecHyp (th : TypedHeap) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (e b : U64) (x1 x2 x3 x4 : Bool),
    DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Endpoint e b x1 x2 x3 x4) →
    Fl4Spec.isFinalCap' (absCap (.Endpoint e b x1 x2 x3 x4)) σ → EpPre σ e.bv

/-- **`SpecFinOut` for the endpoint caps.** -/
theorem specFinOut_ep (th : TypedHeap) (h : EpSpecHyp (L := L) th) : SpecFinOut (L := L) FinEpK th := by
  intro s σ G sl c hk hDS hA hc hfin
  obtain ⟨e, b, x1, x2, x3, x4, rfl⟩ := hk
  exact finEp_out _ _ (h s σ G sl e b x1 x2 x3 x4 hDS hA hc hfin)

end

end Fl4Proofs.P3.Sched
