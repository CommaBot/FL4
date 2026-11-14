/-
P3 (DESIGN.md §9), scheduling contexts: **discharging `SetPrioHyp` and
`SchedTailHyp`** (ScTcb.lean) from P1's invariants and the state relations.

* FL4 side: `KWOut` (P1's write footprint `KW` lies outside the cap slots, a
  placement hypothesis), `slotsSame_of_foot`; `schedTail_foot`, the
  scheduler tail of SetSchedParams with its P1 footprint (`set_mcp.blk`,
  `set_priority.blk`, `unbind_tcb.blk`, `bind_tcb.blkF`).
* Spec side: `setPriority_some` (`set_priority` has an outcome given
  `ActReady` and `BlkQ`), `actReady_upd`, `actReady_restart`, `BlkQ.updTcb`,
  `blkQ_restart`; `blkQ_of_rels`, `BlkQ` from `NtfnStateRel`, `EpStateRel` and
  P1's `EpsWit`.
* `hB_of_restart` (P1's `restart_hB`), `setPrioHyp_of`, and
  **`setPrioHyp_of_rels`**: `SetPrioHyp` from P1's `BlkOK`, `KWOut`, the
  relations and `ActReady`.
* **`schedTailHyp_of`**: `SchedTailHyp` from `hI` (the facts after the
  fault-handler install: P1's `BlkOK`, `KWOut`, the current-thread and SC
  conditions; the spec's `ActReady`, `BlkQ`) and `ScSpecHyp` (the spec's SC
  bind/unbind has an outcome).
-/
import Fl4Proofs.P3.ScTcb
import Fl4Proofs.P3.EpSpec
import Fl4Proofs.P1.QueueInvoke
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Classical

noncomputable section

/-! ## The spec: `set_priority` has an outcome -/

section Spec
open Fl4Spec

theorem schedulable_upd {σ σ' : State Unit} {u : ObjRef}
    (h1 : (tcbsOf σ' u).map (fun z => (runnable z.tcbState, z.tcbSchedContext)) =
      (tcbsOf σ u).map (fun z => (runnable z.tcbState, z.tcbSchedContext)))
    (h2 : ∀ p, Option.map scActive (scsOf σ' p) = Option.map scActive (scsOf σ p))
    (h3 : σ'.releaseQueue = σ.releaseQueue) : schedulable u σ' = schedulable u σ := by
  unfold schedulable
  apply decide_eq_decide.2
  rw [h3]
  simp only [optPred, optMapSome, optMap]
  cases e1 : tcbsOf σ' u <;> cases e2 : tcbsOf σ u <;> rw [e1, e2] at h1 <;> simp at h1
  all_goals first
    | (simp; done)
    | (rename_i x' x
       obtain ⟨hs, hc⟩ := h1
       simp only [hs, hc]
       cases hsc : x.tcbSchedContext with
       | none => simp
       | some p =>
         have := h2 p
         cases e3 : scsOf σ' p <;> cases e4 : scsOf σ p <;> simp_all)

/-- **A TCB update keeping its state and SC keeps `ActReady`** (with the
ready queues free). -/
theorem actReady_upd {σ σ' : State Unit} (h : Notif.ActReady σ) {t : ObjRef} {x y : Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hst : runnable y.tcbState = runnable x.tcbState) (hsc : y.tcbSchedContext = x.tcbSchedContext)
    (hkh : σ'.kheap = Function.update σ.kheap t (some (.tcb y)))
    (hact : σ'.schedulerAction = σ.schedulerAction) (hct : σ'.curTime = σ.curTime)
    (hrq : σ'.releaseQueue = σ.releaseQueue) : Notif.ActReady σ' := by
  have hscs : ∀ p, scsOf σ' p = scsOf σ p := by
    intro p
    rw [scsOf_eq, scsOf_eq, hkh]
    by_cases e : p = t
    · subst e; rw [Function.update_self, hk]
    · rw [Function.update_of_ne e]
  have htc : ∀ p, (tcbsOf σ' p).map (fun z => (runnable z.tcbState, z.tcbSchedContext)) =
      (tcbsOf σ p).map (fun z => (runnable z.tcbState, z.tcbSchedContext)) := by
    intro p
    rw [tcbsOf_eq, tcbsOf_eq, hkh]
    by_cases e : p = t
    · subst e; rw [Function.update_self, hk]; simp [hst, hsc]
    · rw [Function.update_of_ne e]
  intro u hu hs
  have hs0 : schedulable u σ = true := by
    rw [← schedulable_upd (htc u) (fun p => by rw [hscs p]) hrq]; exact hs
  obtain ⟨x0, scp, hk1, hsc1, h1, h2⟩ := h u (by rw [← hact]; exact hu) hs0
  obtain ⟨yy, n, hky, hne, hsuff⟩ := suff_inv h1
  have hrdy := ready_inv h2 hky hne
  have hky' : σ'.kheap scp = some (.schedContext yy n) := by
    rw [hkh]
    by_cases e : scp = t
    · subst e; rw [hk] at hky; cases hky
    · rw [Function.update_of_ne e]; exact hky
  obtain ⟨x', hx', hsx'⟩ : ∃ x', σ'.kheap u = some (.tcb x') ∧ x'.tcbSchedContext = some scp := by
    rw [hkh]
    by_cases e : u = t
    · subst e; rw [hk] at hk1; cases hk1
      exact ⟨y, by rw [Function.update_self], by rw [hsc, hsc1]⟩
    · exact ⟨x0, by rw [Function.update_of_ne e]; exact hk1, hsc1⟩
  refine ⟨x', scp, hx', hsx', ?_, ?_⟩
  · rw [getScRefillSufficient_eq hky' hne, hsuff]
  · rw [getScRefillReady_eq hky' hne, hct, hrdy]

/-- The blocked thread's queue facts (l4v `valid_objs`/`sym_refs` for one
thread): blocked on an endpoint or a notification, the object is a
non-idle endpoint (a waiting notification) with a nonempty queue of TCBs. -/
def BlkQ (σ : State Unit) (t : ObjRef) (ts : ThreadState) : Prop :=
  (∀ e, epBlocked ts = some e → ∃ ep, σ.kheap e = some (.endpoint ep) ∧ ep ≠ .idleEP ∧ ep.epQueue ≠ [] ∧
    ∀ u ∈ ep.epQueue, u ≠ t → ∃ xu, σ.kheap u = some (.tcb xu)) ∧
  (∀ n, ntfnBlocked ts = some n → ∃ xn, σ.kheap n = some (.notification xn) ∧
    xn.ntfnObj.isWaitingNtfn = true ∧ ntfnQueueOf xn ≠ [] ∧
    ∀ u ∈ ntfnQueueOf xn, u ≠ t → ∃ xu, σ.kheap u = some (.tcb xu))

/-- The priority function of the spec's TCBs. -/
def prioOf (σ : State Unit) (u : ObjRef) : Priority := ((tcbsOf σ u).map Tcb.tcbPriority).getD 0

theorem prioOf_eq {σ : State Unit} {u : ObjRef} {x : Tcb} (h : σ.kheap u = some (.tcb x)) :
    prioOf σ u = x.tcbPriority := by
  unfold prioOf; rw [tcbsOf_eq, h]; rfl

theorem assert_one {P : Prop} (h : P) (σ : State Unit) :
    (NonDet.assert P : NonDet (State Unit) Unit) σ = ({((), σ)}, False) := by
  simp [NonDet.assert, h]

theorem removeAll_tcbs {σ : State Unit} {t : ObjRef} {qs : List ObjRef}
    (h : ∀ u ∈ qs, u ≠ t → ∃ xu, σ.kheap u = some (.tcb xu)) :
    ∀ u ∈ removeAll t qs, ∃ x, σ.kheap u = some (.tcb x) ∧ x.tcbPriority = prioOf σ u := by
  intro u hu
  unfold removeAll at hu
  obtain ⟨hm, hne⟩ := List.mem_filter.1 hu
  obtain ⟨xu, hxu⟩ := h u hm (by intro e; subst e; simp at hne)
  exact ⟨xu, hxu, (prioOf_eq hxu).symm⟩

/-- **The spec's `set_priority` has an outcome** from a state with
`ActReady` and the thread's queue facts. -/
theorem setPriority_some {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (pr : Priority)
    (hA : Notif.ActReady σ) (hQ : BlkQ σ t x.tcbState) :
    ∃ y, y ∈ (setPriority (Z := Unit) t pr σ).1 := by
  unfold setPriority getThreadState
  rw [nd_bind_one (Notif.threadGet_eq _ hk)]
  have hts : ∀ σ0 : State Unit, σ0.kheap t = some (.tcb x) →
      threadSetPriority (Z := Unit) t pr σ0 =
        ({((), Notif.updK σ0 t (.tcb { x with tcbPriority := pr }))}, False) := fun σ0 h0 =>
    Notif.threadSet_eq _ h0
  split
  · rw [nd_bind_one (Notif.threadGet_eq _ hk), nd_bind_one (Notif.threadGet_eq _ hk),
      nd_bind_one (getTcbQueue_eq _ _ _), Notif.nd_gets_bind]
    split
    · rw [nd_bind_one (tcbSchedAction_gen hk _)]
      rw [nd_bind_one (hts (setQ σ x.tcbDomain x.tcbPriority _) hk)]
      rw [nd_bind_one (tcbSchedAction_gen (x := { x with tcbPriority := pr })
        (by simp [Notif.updK, setQ]) _)]
      obtain ⟨σd, hd, -⟩ := rescheduleRequired_qchange (actReady_upd (y := { x with tcbPriority := pr }) hA hk rfl rfl
        (σ' := setQ (Notif.updK (setQ σ x.tcbDomain x.tcbPriority _) t (.tcb { x with tcbPriority := pr }))
          x.tcbDomain pr _)
        (by simp [Notif.updK, setQ]) rfl rfl rfl)
      exact ⟨((), σd), by rw [hd]; exact Set.mem_singleton _⟩
    · exact ⟨_, by rw [hts _ hk]; exact Set.mem_singleton _⟩
  · rw [nd_bind_one (hts _ hk)]
    obtain ⟨hE, hN⟩ := hQ
    have hkb : (Notif.updK σ t (.tcb { x with tcbPriority := pr })).kheap t =
        some (.tcb { x with tcbPriority := pr }) := by simp [Notif.updK]
    set σb := Notif.updK σ t (.tcb { x with tcbPriority := pr }) with hσb
    have hkb' : ∀ u, u ≠ t → σb.kheap u = σ.kheap u := fun u hu => by
      simp [hσb, Notif.updK, Function.update_of_ne hu]
    have hep : ∀ e, epBlocked x.tcbState = some e → ∃ σr, reorderEp (Z := Unit) e t σb = ({((), σr)}, False) := by
      intro e he
      obtain ⟨ep, hke, hni, hne, hq⟩ := hE e he
      have het : e ≠ t := by rintro rfl; rw [hk] at hke; cases hke
      have hke' : σb.kheap e = some (.endpoint ep) := by rw [hkb' e het]; exact hke
      have hq' := removeAll_tcbs (σ := σb) (t := t) (qs := ep.epQueue)
        (fun u hu hut => by rw [hkb' u hut]; exact hq u hu hut)
      exact ⟨_, by
        unfold reorderEp
        rw [nd_bind_one (Endp.getEndpoint_eq hke'), nd_bind_one (assert_one hni _), Notif.nd_pure_bind',
          nd_bind_one (assert_one hne _), Notif.nd_pure_bind', nd_bind_one (Notif.tcbAppend_eq hkb _ _ hq')]
        exact Endp.setEndpoint_eq _ hke'⟩
    have hnt : ∀ n, ntfnBlocked x.tcbState = some n → ∃ σr, reorderNtfn (Z := Unit) n t σb = ({((), σr)}, False) := by
      intro n hn
      obtain ⟨xn, hkn, hw, hne, hq⟩ := hN n hn
      have hnt : n ≠ t := by rintro rfl; rw [hk] at hkn; cases hkn
      have hkn' : σb.kheap n = some (.notification xn) := by rw [hkb' n hnt]; exact hkn
      have hq' := removeAll_tcbs (σ := σb) (t := t) (qs := ntfnQueueOf xn)
        (fun u hu hut => by rw [hkb' u hut]; exact hq u hu hut)
      exact ⟨_, by
        unfold reorderNtfn
        rw [nd_bind_one (Notif.getNotification_eq hkn'), nd_bind_one (assert_one hw _), Notif.nd_pure_bind',
          nd_bind_one (assert_one hne _), Notif.nd_pure_bind', nd_bind_one (Notif.tcbAppend_eq hkb _ _ hq')]
        exact Notif.setNotification_eq _ hkn'⟩
    cases hst : x.tcbState
    all_goals first
      | (rename_i hnr; rw [hst] at hnr; simp [runnable] at hnr; done)
      | (obtain ⟨σr, hr⟩ := hep _ (by rw [hst]; rfl)
         refine ⟨((), σr), ?_⟩
         show _ ∈ ((reorderEp (Z := Unit) _ t >>= fun _ => NonDet.pure ()) σb).1
         rw [nd_bind_one hr]; exact Set.mem_singleton _)
      | (obtain ⟨σr, hr⟩ := hnt _ (by rw [hst]; rfl)
         refine ⟨((), σr), ?_⟩
         show _ ∈ ((NonDet.pure () >>= fun _ => reorderNtfn (Z := Unit) _ t) σb).1
         rw [nd_bind_one (show (NonDet.pure () : NonDet (State Unit) Unit) σb = ({((), σb)}, False) from rfl), hr]; exact Set.mem_singleton _)
      | (refine ⟨((), σb), ?_⟩
         show _ ∈ ((NonDet.pure () >>= fun _ => NonDet.pure ()) σb).1
         rw [nd_bind_one (show (NonDet.pure () : NonDet (State Unit) Unit) σb = ({((), σb)}, False) from rfl)]; exact Set.mem_singleton _)

end Spec

/-! ## FL4: P1's footprints keep the slots -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **P1's kernel-write words lie outside the cap slots** (P1 QueueFoot's
docstring: a CNode slot is in a CNode, a TCB slot below offset 160, an IRQ
slot in the kernel-global area); a placement hypothesis of the typed heap. -/
def KWOut (th : TypedHeap) (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64) (s : S) : Prop :=
  ∀ a, IsSlot th a → ∀ b, P1.KW st T Cs Sg Scs Z Es s b → ¬ (a.val ≤ b.val ∧ b.val < a.val + 32)

/-- **A P1 `Foot` step keeps every slot word.** -/
theorem slotsSame_of_foot {th : TypedHeap} (hP : Placed th) {T Cs Sg Scs Es : Set U64} {Z : U64 → Nat} {s s' : S}
    (hK : KWOut (st := st) th T Cs Sg Scs Z Es s) (hw : P1.Foot st T Cs Sg Scs Z Es s s') :
    SlotsSame th (L.mem s) (L.mem s') := by
  intro a ha
  have w : ∀ k, Off k → L.mem s' (wordOf a k) = L.mem s (wordOf a k) := fun k hk =>
    hw.mem_eq (slot_word_aligned hP ha hk) fun hb => hK a ha _ hb (by
      rw [slot_word_val hP ha hk]; have := hk.lt; omega)
  refine ⟨?_, w _ (Or.inr (Or.inl rfl)), w _ (Or.inr (Or.inr (Or.inl rfl))), w _ (Or.inr (Or.inr (Or.inr rfl)))⟩
  have := w _ (Or.inl rfl)
  rwa [wordOf_zero] at this

/-- **`SetPrioHyp` discharged** from P1's `sched.set_priority.blk`: after the
caller's restart, P1's `BlkOK` with `set_priority`'s current-thread
conditions and `KWOut` (`hB`, P1's facts about the restart state), and the
spec's `ActReady` and `BlkQ` of the target (`hσ`). -/
theorem setPrioHyp_of (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit) (ct : U64)
    {T Cs Ω : Set U64} {H : P1.Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
    (hB : ∀ s1 t, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → th t = some .tcb →
      P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧ t ∈ T ∧ KWOut (st := st) th T Cs Sg Scs Z (P1.EH H) s1 ∧
      (t = L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD) →
        (L.mem s1 (P1.inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s1 (P1.scA t) ≠ 0#u64 ∧ L.mem s1 (P1.scA t) ∈ Ac))
    (hσ : ∀ σ1 t, Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) → th t = some .tcb →
      ∃ x, σ1.kheap t.bv = some (.tcb x) ∧ Notif.ActReady σ1 ∧ BlkQ σ1 t.bv x.tcbState) :
    SetPrioHyp (L := L) th s σ ct := by
  intro s1 σ1 t v hs1 hst1 ht hv
  obtain ⟨hb, htT, hKA, hcur⟩ := hB s1 t hs1 ht
  obtain ⟨x, hk, hA, hQ⟩ := hσ σ1 t hst1 ht
  refine WP.spec_mono (P1.sched.set_priority.blk s1 t v hb htT hv (fun e => (hcur e).1) (fun e => (hcur e).2.1)
    (fun e => (hcur e).2.2)) ?_
  rintro s2 ⟨-, hF, -⟩
  exact ⟨slotsSame_of_foot hP hKA hF, setPriority_some hk _ hA hQ⟩

theorem KWOut.mono {th : TypedHeap} {T Cs Sg Scs Es Es' : Set U64} {Z : U64 → Nat} {s : S}
    (h : KWOut (st := st) th T Cs Sg Scs Z Es' s) (hE : Es ⊆ Es') : KWOut (st := st) th T Cs Sg Scs Z Es s :=
  fun a ha b hb => h a ha b (P1.KW.mono hb hE)

theorem KWOut.ksb {th : TypedHeap} {T Cs Sg Scs Es : Set U64} {Z : U64 → Nat} {s s' : S}
    (h : KWOut (st := st) th T Cs Sg Scs Z Es s) (hk : L.ksb s' = L.ksb s) : KWOut (st := st) th T Cs Sg Scs Z Es s' :=
  fun a ha b hb => h a ha b (P1.KW.ksb hk hb)

/-- The SC step of `schedTail`. -/
def scTail (s4 : S) (a1 : A) (t sc : U64) (scf : Bool) : Result (core.result.Result Unit error.Exc × S × A) :=
  if scf then do
    let b ← obj.Sc.is_null sc
    if b then
      let i4 ← obj.Tcb.sc st t s4
      let b1 ← obj.Sc.is_null i4
      if b1 then ok (core.result.Result.Ok (), s4, a1)
      else
        let s5 ← schedcontext.unbind_tcb st s4 i4
        ok (core.result.Result.Ok (), s5, a1)
    else
      let (s5, a2) ← schedcontext.bind_tcb st arI s4 a1 sc t
      ok (core.result.Result.Ok (), s5, a2)
  else ok (core.result.Result.Ok (), s4, a1)

theorem schedTail_eq (s2 : S) (a1 : A) (t mcp prio sc : U64) (scf : Bool) :
    schedTail (st := st) arI s2 a1 t mcp prio sc scf = (do
      let s3 ← obj.Tcb.set_mcp st t s2 mcp
      let s4 ← sched.set_priority st s3 t prio
      scTail (st := st) arI s4 a1 t sc scf) := rfl

end

/-! ## The scheduler tail with its footprint (after P1's `tcs_tail`) -/

section
open Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {T Cs Ω : Set U64} {H : P1.Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **`schedTail` with its footprint**: P1's `tcs_tail` (`MCP`, priority,
then binding the SC or unbinding the thread's SC) with the `Foot` of each
step (`set_mcp.blk`, `set_priority.blk`, `unbind_tcb.blk`, `bind_tcb.blkF`). -/
theorem schedTail_foot (hA : P0.ArchTotal arI) (s2 : S) (a1 : A) (p mcp prio sc : U64) (scf : Bool)
    (h2 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2) (hpT : p ∈ T) (hv : prio.val < 256)
    (hcur : p = L.curW s2 → (L.mem s2 (inqA p) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s2 (scA p) ≠ 0#u64 ∧
      L.mem s2 (scA p) ∈ Ac)
    (hbind : scf = true → sc ≠ 0#u64 → sc ∈ Scs ∧ L.mem s2 (scA p) = 0#u64 ∧
      L.mem s2 (scTcbA sc) = 0#u64 ∧ (BlockedR (L.mem s2 (P1.stA p)) → sc ∈ Ac))
    (hunb : scf = true → sc = 0#u64 → L.actionW s2 ≠ p ∧ L.idleW s2 ≠ p) :
    schedTail (st := st) arI s2 a1 p mcp prio sc scf ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧
      Foot st T Cs Sg Scs Z (EH H) s2 r.2.1 ∧ r.1 = .Ok () ⦄ := by
  have hT := h2.1.choose_spec.choose_spec.tcbs
  have hta := hT p hpT
  rw [schedTail_eq]
  -- `MCP`
  refine WP.spec_bind (Pₘ := fun s3 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ PFr st T Sg s2 s3 ∧
      L.curW s3 = L.curW s2 ∧ Foot st T Cs Sg Scs Z (EH H) s2 s3 ∧
      ((L.mem s3 (inqA p) &&& sched.Q_RELEASE) ≠ 0#u64 → (L.mem s2 (inqA p) &&& sched.Q_RELEASE) ≠ 0#u64))
    ?_ ?_
  · refine WP.spec_mono (WP.spec_and (obj.Tcb.set_mcp.wr s2 p mcp) (obj.Tcb.set_mcp.blk s2 p mcp h2 hpT))
      fun s' hh => ?_
    obtain ⟨e, -, hF, -⟩ := hh
    subst e
    obtain ⟨Q1, R1, h1'⟩ := h2.1
    have hN := h1'.nodes _ h1'.cur
    refine ⟨(plainW_all (K := 3440#u64) (v := mcp) h2 hpT (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp)).1,
      PFr.of_fr (fr_field (K := 3440#u64) h1' h2.2.2.2.2 hpT (by simp) (by simp) (by simp))
        (Or.inl (act_wr_field hN hpT hta rfl (by simp) (by simp))),
      cur_wr_field hN hpT hta (by simp) (by simp), hF.mono (Set.empty_subset _), fun hf => ?_⟩
    rwa [inqA_eq, L.mem_wr_ne (field_aligned (K := 3440#u64) hta (by simp) (by simp))
      (field_aligned (K := 3592#u64) hta (by simp) (by simp))
      (fun e => field_ne (K1 := 3440#u64) (K2 := 3592#u64) hta hta (by simp) (by simp) (fun _ => by simp)
        (UScalar.eq_of_val_eq e)), ← inqA_eq] at hf
  rintro s3 ⟨h3, pf3, ec3, f3, hrel3⟩
  -- priority
  have hcur3 : p = L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.CUR_THREAD) → p = L.curW s2 :=
    fun e => e.trans ec3
  refine WP.spec_bind (sched.set_priority.blk s3 p prio h3 hpT hv
    (fun e => by by_contra hn; exact hrel3 hn (hcur (hcur3 e)).1)
    (fun e => by rw [pf3.sc p hpT]; exact (hcur (hcur3 e)).2.1)
    (fun e => by rw [pf3.sc p hpT]; exact (hcur (hcur3 e)).2.2)) ?_
  rintro s4 ⟨h4, f4, pf4'⟩
  have pf4 := pf3.trans pf4'
  have f24 := f3.trans f4
  -- the SC
  unfold scTail
  split
  · rename_i hfs
    step with obj.Sc.is_null.spec as ⟨b, eb⟩
    split
    · rename_i hb
      have hsc0 : sc = 0#u64 := by simpa [eb] using hb
      obtain ⟨hna, hid⟩ := hunb hfs hsc0
      step with obj.Tcb.sc.spec as ⟨i4, ei4⟩
      step with obj.Sc.is_null.spec as ⟨b1, eb1⟩
      split
      · exact (WP.spec_ok _).2 ⟨h4, f24, rfl⟩
      · rename_i hb1
        have hi0 : i4 ≠ 0#u64 := fun e => hb1 (by rw [eb1, e]; rfl)
        obtain ⟨hiS, hit, -⟩ := h4.2.2.1.2.2.bound p hpT (by rw [← ei4]; exact hi0)
        rw [← ei4] at hiS hit
        have hT4 := h4.1.choose_spec.choose_spec.tcbs
        refine WP.spec_bind (schedcontext.unbind_tcb.blk s4 i4 h4 hiS hi0 (fun _ => ?_) (fun _ => ?_))
          fun s5 hh => (WP.spec_ok _).2 ⟨hh.1, f24.trans (hh.2.1.mono (Set.empty_subset _)), rfl⟩
        · rw [hit]
          rcases pf4.act with e | e
          · rw [e]; exact hna
          · rw [e]; exact fun e' => notT_small hT4 (by simp) (e' ▸ hpT)
        · rw [hit, pf4.idle]; exact hid
    · rename_i hb
      have hsc0 : sc ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
      obtain ⟨hsc, ht0, hc0, hbA⟩ := hbind hfs hsc0
      refine WP.spec_bind (schedcontext.bind_tcb.blkF (Es := EH H) hA s4 a1 sc p h4 hpT hsc hsc0
        (by rw [pf4.sc p hpT]; exact ht0)
        (by rw [pf4.sig _ (h4.2.2.1.1.fixW sc hsc).1]; exact hc0)
        (fun hb' => hbA (by rw [← pf4.st p hpT]; exact hb'))) fun r hr => ?_
      obtain ⟨s5, a2⟩ := r
      exact (WP.spec_ok _).2 ⟨hr.1, f24.trans hr.2, rfl⟩
  · exact (WP.spec_ok _).2 ⟨h4, f24, rfl⟩

/-- **The restart facts of `setPrioHyp_of`** (`hB`) from P1's `restart_hB`:
the caller is the current thread, every TCB of the typed heap is in `T`,
and `KWOut` before the restart (the restart keeps the kernel-global base). -/
theorem hB_of_restart (th : TypedHeap) (s : S) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hb : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hnb : ¬ Blocked (L.mem s (P1.stA (L.curW s)))) (hnr : L.mem s (P1.stA (L.curW s)) ≠ sched.TS_BLOCKED_ON_REPLY)
    (hcur : (L.mem s (inqA (L.curW s)) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (scA (L.curW s)) ≠ 0#u64 ∧
      L.mem s (scA (L.curW s)) ∈ Ac)
    (hTh : ∀ t, th t = some .tcb → t ∈ T) (hK : KWOut (st := st) th T Cs Sg Scs Z (EH H) s) :
    ∀ s1 t, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → th t = some .tcb →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧ t ∈ T ∧ KWOut (st := st) th T Cs Sg Scs Z (EH H) s1 ∧
      (t = L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD) →
        (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s1 (scA t) ≠ 0#u64 ∧ L.mem s1 (scA t) ∈ Ac) := by
  intro s1 t hs1 ht
  have ect : ct = L.curW s := by
    rw [cur_thread_eq] at hct; exact (Result.ok_injective hct).symm
  subst ect
  obtain ⟨hb1, -, hk, hc⟩ := restart_hB (Es := EH H) s hb hnb hnr hcur s1 hs1
  exact ⟨hb1, hTh t ht, KWOut.ksb hK hk, hc t⟩

/-- **The spec's SC step of SetSchedParams** (for the spec's SC bind and
unbind): from the spec's state after the install, `set_mcpriority` and
`set_priority`, `invoke_tcb`'s SC step has an outcome. -/
def ScSpecHyp (s : S) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  ∀ (s1 : S) (σ1 : Fl4Spec.State Unit) (a : A) (p mcp prio scv x2 : U64) (scf : Bool) (ssl : Fl4Spec.CslotPtr)
    (fh : Fl4Spec.Cap × Fl4Spec.CslotPtr) (sco : Option (Option Fl4Spec.ObjRef))
    (s2 : S) (a1 : A) (σ2 σa σb : Fl4Spec.State Unit),
    sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    (sco = none ↔ scf = false) → (sco = some none → scv = 0#u64) →
    (∀ v, sco = some (some v) → v = scv.bv ∧ scv ≠ 0#u64) →
    tcb.install_tcb_cap st arI s1 a p (cslotAddr ssl) layout.tcb.SLOT_FAULT_HANDLER (capV (L.mem s) x2) x2 =
      ok (.Ok (), s2, a1) →
    (.ok (), σ2) ∈ ((Fl4Spec.installTcbCap (Z := Unit) p.bv ssl 3 (some fh)).run σ1).1 →
    ((), σa) ∈ (Fl4Spec.setMcpriority (Z := Unit) p.bv (Fl4Spec.ucast 8 mcp.bv) σ2).1 →
    ((), σb) ∈ (Fl4Spec.setPriority (Z := Unit) p.bv (Fl4Spec.ucast 8 prio.bv) σa).1 →
    ∃ σc, ((), σc) ∈ (scStep p.bv sco σb).1

/-- **`SchedTailHyp` from the install's facts and the spec's SC step**: the
FL4 tail by `schedTail_foot` (P1's footprints) and `KWOut`; the spec's
`set_mcpriority` and `set_priority` by `setPriority_some`; the SC step by
`ScSpecHyp`. What remains is `hI`, the facts after the fault-handler
install (P1's `BlkOK`, `KWOut`, `set_priority`'s and `bind_tcb`'s/
`unbind_tcb`'s conditions; the spec's `ActReady` and `BlkQ`), as P1's
`thread_control_sched.blk` assumes them. -/
theorem schedTailHyp_of (hA : P0.ArchTotal arI) (th : TypedHeap) (hP : Placed th) (s : S)
    (σ : Fl4Spec.State Unit) (ct : U64)
    (hI : ∀ (s1 : S) (σ1 : Fl4Spec.State Unit) (a : A) (p scv x2 : U64) (scf : Bool) (ssl : Fl4Spec.CslotPtr)
      (fh : Fl4Spec.Cap × Fl4Spec.CslotPtr) (sco : Option (Option Fl4Spec.ObjRef)) (s2 : S) (a1 : A)
      (σ2 : Fl4Spec.State Unit) (G2 : MdbGhost),
      sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) → th p = some .tcb →
      (sco = none ↔ scf = false) → (sco = some none → scv = 0#u64) →
      (∀ v, sco = some (some v) → v = scv.bv ∧ scv ≠ 0#u64) →
      tcb.install_tcb_cap st arI s1 a p (cslotAddr ssl) layout.tcb.SLOT_FAULT_HANDLER (capV (L.mem s) x2) x2 =
        ok (.Ok (), s2, a1) →
      (.ok (), σ2) ∈ ((Fl4Spec.installTcbCap (Z := Unit) p.bv ssl 3 (some fh)).run σ1).1 →
      DState (L := L) th s2 σ2 G2 →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 ∧ p ∈ T ∧ KWOut (st := st) th T Cs Sg Scs Z (EH H) s2 ∧
      (p = L.curW s2 → (L.mem s2 (inqA p) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s2 (scA p) ≠ 0#u64 ∧
        L.mem s2 (scA p) ∈ Ac) ∧
      (scf = true → scv ≠ 0#u64 → scv ∈ Scs ∧ L.mem s2 (scA p) = 0#u64 ∧
        L.mem s2 (scTcbA scv) = 0#u64 ∧ (BlockedR (L.mem s2 (P1.stA p)) → scv ∈ Ac)) ∧
      (scf = true → scv = 0#u64 → L.actionW s2 ≠ p ∧ L.idleW s2 ≠ p) ∧
      ∃ x, σ2.kheap p.bv = some (.tcb x) ∧ Notif.ActReady σ2 ∧ BlkQ σ2 p.bv x.tcbState)
    (hSS : ScSpecHyp (L := L) arI s σ ct) :
    SchedTailHyp (L := L) arI th s σ ct := by
  intro s1 σ1 a p mcp prio scv x2 scf ssl fh q sco s2 a1 σ2 G2 hs1 hst1 hp hm hpr h1 h2 h3 hins hx hDS2
  obtain ⟨hb2, hpT, hKA, hcur, hbind, hunb, x, hk2, hA2, hQ2⟩ :=
    hI s1 σ1 a p scv x2 scf ssl fh sco s2 a1 σ2 G2 hs1 hst1 hp h1 h2 h3 hins hx hDS2
  -- the spec: `set_mcpriority`, `set_priority`, the SC step
  set σa := Notif.updK σ2 p.bv (.tcb { x with tcbMcpriority := Fl4Spec.ucast 8 mcp.bv }) with hσa
  have ha : ((), σa) ∈ (Fl4Spec.setMcpriority (Z := Unit) p.bv (Fl4Spec.ucast 8 mcp.bv) σ2).1 := by
    show _ ∈ (Fl4Spec.threadSet (Z := Unit) _ p.bv σ2).1
    rw [Notif.threadSet_eq _ hk2]; exact Set.mem_singleton _
  have hka : σa.kheap p.bv = some (.tcb { x with tcbMcpriority := Fl4Spec.ucast 8 mcp.bv }) := by
    simp [hσa, Notif.updK]
  have hAa : Notif.ActReady σa := actReady_upd (y := { x with tcbMcpriority := Fl4Spec.ucast 8 mcp.bv }) hA2 hk2
    rfl rfl (by simp [hσa, Notif.updK]) rfl rfl rfl
  have hQa : BlkQ σa p.bv x.tcbState := by
    have hkn : ∀ u, u ≠ p.bv → σa.kheap u = σ2.kheap u := fun u hu => by
      simp [hσa, Notif.updK, Function.update_of_ne hu]
    obtain ⟨hE, hN⟩ := hQ2
    refine ⟨fun e he => ?_, fun n hn => ?_⟩
    · obtain ⟨ep, hke, h1', h2', h3'⟩ := hE e he
      have het : e ≠ p.bv := by rintro rfl; rw [hk2] at hke; cases hke
      exact ⟨ep, by rw [hkn e het]; exact hke, h1', h2', fun u hu hut => by rw [hkn u hut]; exact h3' u hu hut⟩
    · obtain ⟨xn, hkn', h1', h2', h3'⟩ := hN n hn
      have hnt : n ≠ p.bv := by rintro rfl; rw [hk2] at hkn'; cases hkn'
      exact ⟨xn, by rw [hkn n hnt]; exact hkn', h1', h2', fun u hu hut => by rw [hkn u hut]; exact h3' u hu hut⟩
  obtain ⟨⟨_, σb⟩, hb⟩ := setPriority_some hka (Fl4Spec.ucast 8 prio.bv) hAa hQa
  obtain ⟨σc, hc⟩ := hSS s1 σ1 a p mcp prio scv x2 scf ssl fh sco s2 a1 σ2 σa σb hs1 hst1 h1 h2 h3 hins hx ha hb
  -- FL4
  refine WP.spec_mono (schedTail_foot arI hA s2 a1 p mcp prio scv scf hb2 hpT hpr hcur hbind hunb) ?_
  rintro r ⟨-, hF, hr⟩
  exact ⟨slotsSame_of_foot hP hKA hF, hr, σa, σb, σc, ha, hb, hc⟩

end

/-! ## `BlkQ` from the relations -/

section Spec
open Fl4Spec

/-- `BlkQ` across a TCB update (the restart, `set_mcpriority`). -/
theorem BlkQ.updTcb {σ σ' : State Unit} {c t : ObjRef} {y y' : Tcb} {ts : ThreadState}
    (hk : σ.kheap c = some (.tcb y)) (hkh : σ'.kheap = Function.update σ.kheap c (some (.tcb y')))
    (h : BlkQ σ t ts) : BlkQ σ' t ts := by
  have hkn : ∀ u, u ≠ c → σ'.kheap u = σ.kheap u := fun u hu => by rw [hkh, Function.update_of_ne hu]
  have hmem : ∀ u, (∃ xu, σ.kheap u = some (.tcb xu)) → ∃ xu, σ'.kheap u = some (.tcb xu) := by
    rintro u ⟨xu, hu⟩
    by_cases e : u = c
    · subst e; exact ⟨y', by rw [hkh, Function.update_self]⟩
    · exact ⟨xu, by rw [hkn u e]; exact hu⟩
  obtain ⟨hE, hN⟩ := h
  refine ⟨fun e he => ?_, fun n hn => ?_⟩
  · obtain ⟨ep, hke, h1, h2, h3⟩ := hE e he
    have hec : e ≠ c := by rintro rfl; rw [hk] at hke; cases hke
    exact ⟨ep, by rw [hkn e hec]; exact hke, h1, h2, fun u hu hut => hmem u (h3 u hu hut)⟩
  · obtain ⟨xn, hkn', h1, h2, h3⟩ := hN n hn
    have hnc : n ≠ c := by rintro rfl; rw [hk] at hkn'; cases hkn'
    exact ⟨xn, by rw [hkn n hnc]; exact hkn', h1, h2, fun u hu hut => hmem u (h3 u hu hut)⟩

theorem setThreadState_eq' {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (ts : ThreadState) :
    setThreadState (Z := Unit) t ts σ =
      ({((), Notif.stsAct (Notif.updK σ t (.tcb { x with tcbState := ts })) t)}, False) := by
  unfold setThreadState
  rw [nd_bind_one (Notif.threadSet_eq _ hk)]
  rw [Notif.setThreadStateAct_eq]

/-- **The caller's restart keeps `ActReady`** (the caller runnable). -/
theorem actReady_restart {σ σ1 : State Unit} {t : ObjRef} {x : Tcb} (hA : Notif.ActReady σ)
    (hk : σ.kheap t = some (.tcb x)) (hrun : runnable x.tcbState = true)
    (h : setThreadState (Z := Unit) t .restart σ = ({((), σ1)}, False)) : Notif.ActReady σ1 := by
  rw [setThreadState_eq' hk] at h
  have e := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst h))).2
  subst e
  have h0 : Notif.ActReady (Notif.updK σ t (.tcb { x with tcbState := .restart })) :=
    actReady_upd (y := { x with tcbState := .restart }) hA hk (by show true = runnable x.tcbState; rw [hrun]) rfl (by simp [Notif.updK])
      rfl rfl rfl
  unfold Notif.stsAct
  split
  · intro u hu; simp at hu
  · exact h0

/-- `BlkQ` of the caller's restart state. -/
theorem blkQ_restart {σ σ1 : State Unit} {c t : ObjRef} {xc x : Tcb} (hkc : σ.kheap c = some (.tcb xc))
    (h : setThreadState (Z := Unit) c .restart σ = ({((), σ1)}, False)) (hk : σ.kheap t = some (.tcb x))
    (hQ : BlkQ σ t x.tcbState) : ∃ x1, σ1.kheap t = some (.tcb x1) ∧ BlkQ σ1 t x1.tcbState := by
  have hk1 := restart_kheap hkc h
  by_cases e : t = c
  · subst e
    exact ⟨_, by rw [hk1, Function.update_self],
      ⟨fun e h => by simp [epBlocked] at h, fun n h => by simp [ntfnBlocked] at h⟩⟩
  · exact ⟨x, by rw [hk1, Function.update_of_ne e]; exact hk, BlkQ.updTcb hkc hk1 hQ⟩

end Spec

section
open Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`BlkQ` from the state relations and P1's queue invariant**: a thread
blocked on an endpoint or a notification (`TcbRelE`'s state and block-object
words) is in the queue of that object (P1's `EpsWit`), which is a heap
endpoint (notification) with a send or receive (waiting) state word, so the
spec's object is a non-idle endpoint (a waiting notification) whose queue is
the related nonempty list of TCBs (`EpObjRel`, `NtfnObjRel`). -/
theorem blkQ_of_rels {s : S} {σ : Fl4Spec.State Unit} {T Cs Ω E EP R : Set U64} {N : Set U64} {H : Heap}
    {B : Set (U64 × Fl4Spec.Word)} {EQ : U64 → List U64}
    (hNR : Notif.NtfnStateRel N T (L.mem s) σ) (hER : Endp.EpStateRel T EP R B (L.mem s) σ)
    (hW : EpsWit st T Cs Ω H ∅ s E EQ)
    (hHN : ∀ n, H n = some .ntfn → n ∈ N) (hHE : ∀ e, H e = some .ep → e ∈ EP)
    {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) :
    BlkQ σ t.bv x.tcbState := by
  obtain ⟨-, -, -, -, hblk, hty⟩ := hW
  obtain ⟨xe, hke, hrel⟩ := hER.tcb t ht
  rw [hk] at hke; cases hke
  have hst := hrel.st
  have est : Notif.tStA t = stA t := rfl
  rw [est] at hst
  have tv := Notif.tsVals
  have hmT : ∀ y : U64, y ∈ T → ∃ xu, σ.kheap y.bv = some (.tcb xu) := fun y hy => by
    obtain ⟨xu, hu, -⟩ := hER.tcb y hy; exact ⟨xu, hu⟩
  have hmem : ∀ (xs : List U64), (∀ y ∈ xs, y ∈ T) → ∀ u ∈ xs.map UScalar.bv, ∃ xu, σ.kheap u = some (.tcb xu) := by
    intro xs hxs u hu
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hu
    exact hmT y (hxs y hy)
  refine ⟨fun e he => ?_, fun n hn => ?_⟩
  · have hbl := hrel.blk e he
    have hsr : L.mem s (stA t) = sched.TS_BLOCKED_ON_SEND ∨ L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV := by
      cases hts : x.tcbState <;> rw [hts] at he hst <;> simp [Fl4Spec.epBlocked] at he
      · right; rw [tv.2.2.1]; exact UScalar.eq_of_val_eq (by simpa [Notif.tsCode] using hst)
      · left; rw [tv.2.2.2.1]; exact UScalar.eq_of_val_eq (by simpa [Notif.tsCode] using hst)
    have hB : Blocked (L.mem s (stA t)) := by rcases hsr with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
    obtain ⟨hbE, htq⟩ := hblk t ht (by simp) hB
    have hH := hty.1 t ht (by simp) hsr
    have hsw := hty.2.2.2.2.1 _ hbE t htq
    obtain ⟨ep, hkep, hor⟩ := hER.ep _ (hHE _ hH)
    have he' : (L.mem s (blockA t)).bv = e := hbl
    rw [he'] at hkep
    cases ep with
    | idleEP =>
      exfalso
      have h0 : Notif.stOf (L.mem s) (L.mem s (blockA t)) = 0#u64 := hor.1
      rcases hsr with h | h
      · have := (hsw.1 h); unfold LawfulStore.epState at this; unfold Notif.stOf at h0; rw [h0] at this
        exact absurd this (by decide)
      · have := (hsw.2.1 h); unfold LawfulStore.epState at this; unfold Notif.stOf at h0; rw [h0] at this
        exact absurd this (by decide)
    | sendEP q =>
      obtain ⟨-, xs, hxs, rfl, hq, -⟩ := hor
      exact ⟨_, hkep, by simp, by simpa [Fl4Spec.Endpoint.epQueue] using hxs,
        fun u hu _ => hmem xs (fun y hy => hq.mem y hy) u hu⟩
    | recvEP q =>
      obtain ⟨-, xs, hxs, rfl, hq, -⟩ := hor
      exact ⟨_, hkep, by simp, by simpa [Fl4Spec.Endpoint.epQueue] using hxs,
        fun u hu _ => hmem xs (fun y hy => hq.mem y hy) u hu⟩
  · obtain ⟨xn1, hkn1, hrn⟩ := hNR.tcb t ht
    rw [hk] at hkn1; cases hkn1
    have hbl := hrn.blk n (by cases hts : x.tcbState <;> rw [hts] at hn <;> simp [Fl4Spec.ntfnBlocked] at hn; rw [hn])
    have hsn : L.mem s (stA t) = sched.TS_BLOCKED_ON_NTFN := by
      cases hts : x.tcbState <;> rw [hts] at hn hst <;> simp [Fl4Spec.ntfnBlocked] at hn
      rw [tv.2.2.2.2]; exact UScalar.eq_of_val_eq (by simpa [Notif.tsCode] using hst)
    obtain ⟨hbE, htq⟩ := hblk t ht (by simp) (Or.inr (Or.inr hsn))
    have hH := hty.2.1 t ht (by simp) hsn
    have hsw := (hty.2.2.2.2.1 _ hbE t htq).2.2 hsn
    obtain ⟨xn, hkn, hrel1⟩ := hNR.ntfn _ (hHN _ hH)
    have hn' : (L.mem s (blockA t)).bv = n := hbl
    rw [hn'] at hkn
    have hob := hrel1.obj
    cases ho : xn.ntfnObj with
    | idleNtfn =>
      exfalso; rw [ho] at hob
      unfold LawfulStore.epState at hsw; have h0 := hob.1; unfold Notif.stOf at h0; rw [h0] at hsw
      exact absurd hsw (by decide)
    | activeNtfn b =>
      exfalso; rw [ho] at hob
      unfold LawfulStore.epState at hsw; have h0 := hob.1; unfold Notif.stOf at h0; rw [h0] at hsw
      exact absurd hsw (by decide)
    | waitingNtfn q =>
      rw [ho] at hob
      obtain ⟨-, xs, hxs, rfl, hq, -⟩ := hob
      refine ⟨xn, hkn, by rw [ho]; rfl, by rw [Fl4Spec.ntfnQueueOf, ho]; simpa [Fl4Spec.Ntfn.ntfnQueue] using hxs,
        fun u hu _ => ?_⟩
      simp only [Fl4Spec.ntfnQueueOf, ho] at hu
      exact hmem xs (fun y hy => hq.mem y hy) u hu

/-- **`SetPrioHyp` from P1's `BlkOK` and the state relations**: `hB` by
`hB_of_restart` (P1's `restart_hB`), `ActReady` across the restart by
`actReady_restart`, `BlkQ` by `blkQ_of_rels` (P1's `EpsWit`, `NtfnStateRel`,
`EpStateRel`) and `blkQ_restart`. -/
theorem setPrioHyp_of_rels (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit) (ct : U64)
    {T Cs Ω EP R N : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
    {B : Set (U64 × Fl4Spec.Word)}
    (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (hb : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : Runnable (L.mem s (stA (L.curW s))))
    (hcs : (L.mem s (inqA (L.curW s)) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (scA (L.curW s)) ≠ 0#u64 ∧
      L.mem s (scA (L.curW s)) ∈ Ac)
    (hTh : ∀ t, th t = some .tcb → t ∈ T) (hK : KWOut (st := st) th T Cs Sg Scs Z (EH H) s)
    (hNR : Notif.NtfnStateRel N T (L.mem s) σ) (hER : Endp.EpStateRel T EP R B (L.mem s) σ)
    (hHN : ∀ n, H n = some .ntfn → n ∈ N) (hHE : ∀ e, H e = some .ep → e ∈ EP)
    (hA : Notif.ActReady σ) {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc))
    (hrun : Fl4Spec.runnable xc.tcbState = true) :
    SetPrioHyp (L := L) th s σ ct := by
  obtain ⟨Q, R0, h0⟩ := hb.1
  obtain ⟨E, EQ, hW⟩ := h0.eps
  refine setPrioHyp_of th hP s σ ct
    (hB_of_restart th s ct hct hb (runnable_ok hr).1 (runnable_ok hr).2 hcs hTh hK) ?_
  intro σ1 t hst1 ht
  obtain ⟨x, hkx, -⟩ := hER.tcb t (hTh t ht)
  obtain ⟨x1, hk1, hQ1⟩ := blkQ_restart hkc hst1 hkx (blkQ_of_rels hNR hER hW hHN hHE (hTh t ht) hkx)
  exact ⟨x1, hk1, actReady_restart hA hkc hrun hst1, hQ1⟩

end

end

end Fl4Proofs.P3.Sched
