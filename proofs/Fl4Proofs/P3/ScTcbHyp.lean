/-
P3 (DESIGN.md §9), scheduling contexts: **discharging `SetPrioHyp`**
(ScTcb.lean) from P1's `sched.set_priority.blk` and the spec's facts.

* FL4 side: `KWOut`, the P1 footprint words `KW` lie outside the cap slots
  (a placement hypothesis, as P1's QueueFoot docstring states);
  `slotsSame_of_foot`: a P1 `Foot` step keeps every slot word.
* Spec side: `setPriority_some`, the spec's `set_priority` has an outcome
  from a state with `ActReady` and the blocked thread's queue facts
  (`PrioSpecOK`, l4v `valid_objs`/`sym_refs` for that thread); on the way
  `schedulable_upd` and `actReady_upd` (a TCB update keeping its state and
  SC keeps `ActReady`).
* `setPrioHyp_of`: `SetPrioHyp` from P1's `BlkOK` (with its current-thread
  conditions) after the caller's restart, `KWOut` and `PrioSpecOK` of the
  spec's restart state.
-/
import Fl4Proofs.P3.ScTcb
import Fl4Proofs.P3.EpSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Classical

noncomputable section

/-! ## The spec: `set_priority` has an outcome -/

section Spec
open Fl4Spec

theorem schedulable_upd {σ σ' : State Unit} {u : ObjRef}
    (h1 : (tcbsOf σ' u).map (fun z => (z.tcbState, z.tcbSchedContext)) =
      (tcbsOf σ u).map (fun z => (z.tcbState, z.tcbSchedContext)))
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
    (hk : σ.kheap t = some (.tcb x)) (hst : y.tcbState = x.tcbState) (hsc : y.tcbSchedContext = x.tcbSchedContext)
    (hkh : σ'.kheap = Function.update σ.kheap t (some (.tcb y)))
    (hact : σ'.schedulerAction = σ.schedulerAction) (hct : σ'.curTime = σ.curTime)
    (hrq : σ'.releaseQueue = σ.releaseQueue) : Notif.ActReady σ' := by
  have hscs : ∀ p, scsOf σ' p = scsOf σ p := by
    intro p
    rw [scsOf_eq, scsOf_eq, hkh]
    by_cases e : p = t
    · subst e; rw [Function.update_self, hk]
    · rw [Function.update_of_ne e]
  have htc : ∀ p, (tcbsOf σ' p).map (fun z => (z.tcbState, z.tcbSchedContext)) =
      (tcbsOf σ p).map (fun z => (z.tcbState, z.tcbSchedContext)) := by
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

/-- **The SC step of SetSchedParams** (for the SC bind/unbind refinements):
after the install, `set_mcp` and `set_priority`, FL4's SC bind or unbind
keeps every slot word and succeeds, and the spec's SC step has an outcome
from the spec's state after `set_mcpriority` and `set_priority`. -/
def ScTailHyp (th : TypedHeap) (T Cs Ω : Set U64) (H : P1.Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat)
    (Ac : Set U64) : Prop :=
  ∀ (s4 : S) (a1 : A) (σb : Fl4Spec.State Unit) (p scv : U64) (scf : Bool) (sco : Option (Option Fl4Spec.ObjRef)),
    P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 → th p = some .tcb →
    (sco = none ↔ scf = false) → (sco = some none → scv = 0#u64) →
    (∀ v, sco = some (some v) → v = scv.bv ∧ scv ≠ 0#u64) →
    scTail (st := st) arI s4 a1 p scv scf ⦃ r => SlotsSame th (L.mem s4) (L.mem r.2.1) ∧ r.1 = .Ok () ∧
      ∃ σc, ((), σc) ∈ (scStep p.bv sco σb).1 ⦄

/-- **`SchedTailHyp` from P1's invariants and the SC step**: after the
fault-handler install, P1's `BlkOK` with `set_priority`'s current-thread
conditions and `KWOut`, and the spec's `ActReady` and `BlkQ` of the target
(`hI`, the install's preservation facts, as P1's `thread_control_sched.blk`
assumes them); `set_mcp` and `set_priority` are then discharged
(`obj.Tcb.set_mcp.blk`, `sched.set_priority.blk`, `setPriority_some`), the
SC step is `ScTailHyp`. -/
theorem schedTailHyp_of (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit) (ct : U64)
    {T Cs Ω : Set U64} {H : P1.Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
    (hI : ∀ (s1 : S) (σ1 : Fl4Spec.State Unit) (a : A) (p x2 : U64) (ssl : Fl4Spec.CslotPtr)
      (fh : Fl4Spec.Cap × Fl4Spec.CslotPtr) (s2 : S) (a1 : A) (σ2 : Fl4Spec.State Unit) (G2 : MdbGhost),
      sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) → th p = some .tcb →
      tcb.install_tcb_cap st arI s1 a p (cslotAddr ssl) layout.tcb.SLOT_FAULT_HANDLER (capV (L.mem s) x2) x2 =
        ok (.Ok (), s2, a1) →
      (.ok (), σ2) ∈ ((Fl4Spec.installTcbCap (Z := Unit) p.bv ssl 3 (some fh)).run σ1).1 →
      DState (L := L) th s2 σ2 G2 →
      P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 ∧ p ∈ T ∧ KWOut (st := st) th T Cs Sg Scs Z (P1.EH H) s2 ∧
      (p = L.curW s2 → (L.mem s2 (P1.inqA p) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s2 (P1.scA p) ≠ 0#u64 ∧
        L.mem s2 (P1.scA p) ∈ Ac) ∧
      ∃ x, σ2.kheap p.bv = some (.tcb x) ∧ Notif.ActReady σ2 ∧ BlkQ σ2 p.bv x.tcbState)
    (hSC : ScTailHyp (L := L) arI th T Cs Ω H Sg Rp Scs Nt Z Ac) :
    SchedTailHyp (L := L) arI th s σ ct := by
  intro s1 σ1 a p mcp prio scv x2 scf ssl fh q sco s2 a1 σ2 G2 hs1 hst1 hp hm hpr h1 h2 h3 hins hx hDS2
  obtain ⟨hb2, hpT, hKA, hcur, x, hk2, hA2, hQ2⟩ := hI s1 σ1 a p x2 ssl fh s2 a1 σ2 G2 hs1 hst1 hp hins hx hDS2
  have hta : P1.TcbAddr p := hb2.1.choose_spec.choose_spec.tcbs p hpT
  rw [schedTail_eq]
  -- `MCP`
  obtain ⟨s3, hs3, rfl⟩ := spec_exists (P1.obj.Tcb.set_mcp.wr (L := L) s2 p mcp)
  have hm3 := P1.obj.Tcb.set_mcp.blk (L := L) s2 p mcp hb2 hpT
  rw [hs3, WP.spec_ok] at hm3
  obtain ⟨hb3, hF3, hani⟩ := hm3
  rw [hs3]; simp only [bind_ok]
  have hS3 := slotsSame_of_foot hP (KWOut.mono hKA (Set.empty_subset _)) hF3
  have hne : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3440 →
      L.mem (L.wr s2 (core.num.U64.wrapping_add p 3440#u64) mcp) (core.num.U64.wrapping_add p K) =
        L.mem s2 (core.num.U64.wrapping_add p K) := fun K hK hK8 hK3 =>
    L.mem_wr_ne (P1.field_aligned hta (by simp) (by simp)) (P1.field_aligned hta hK hK8)
      (fun e => P1.field_ne (K1 := 3440#u64) (K2 := K) hta hta (by simp) hK (fun _ => by simpa using hK3.symm)
        (UScalar.eq_of_val_eq e))
  -- the priority
  have hcur3 : p = L.mem (L.wr s2 (core.num.U64.wrapping_add p 3440#u64) mcp)
      (L.nodeAt (L.wr s2 (core.num.U64.wrapping_add p 3440#u64) mcp)
        (L.cpu (L.wr s2 (core.num.U64.wrapping_add p 3440#u64) mcp)) layout.node.CUR_THREAD) → p = L.curW s2 :=
    fun e => e.trans hani.2.2
  have hprio := P1.sched.set_priority.blk (L := L) _ p prio hb3 hpT hpr
    (fun e => by rw [P1.inqA_eq, hne 3592#u64 (by simp) (by simp) (by simp), ← P1.inqA_eq]; exact (hcur (hcur3 e)).1)
    (fun e => by rw [P1.scA_eq, hne 3464#u64 (by simp) (by simp) (by simp), ← P1.scA_eq]; exact (hcur (hcur3 e)).2.1)
    (fun e => by rw [P1.scA_eq, hne 3464#u64 (by simp) (by simp) (by simp), ← P1.scA_eq]; exact (hcur (hcur3 e)).2.2)
  refine WP.spec_bind hprio ?_
  rintro s4 ⟨hb4, hF4, -⟩
  have hKA3 : KWOut (st := st) th T Cs Sg Scs Z (P1.EH H) (L.wr s2 (core.num.U64.wrapping_add p 3440#u64) mcp) :=
    KWOut.ksb hKA (L.ksb_wr _ _ _)
  have hS4 := slotsSame_of_foot hP hKA3 hF4
  -- the spec: `set_mcpriority`, `set_priority`
  set σa := Notif.updK σ2 p.bv (.tcb { x with tcbMcpriority := Fl4Spec.ucast 8 mcp.bv }) with hσa
  have ha : ((), σa) ∈ (Fl4Spec.setMcpriority (Z := Unit) p.bv (Fl4Spec.ucast 8 mcp.bv) σ2).1 := by
    show _ ∈ (Fl4Spec.threadSet (Z := Unit) _ p.bv σ2).1
    rw [Notif.threadSet_eq _ hk2]; exact Set.mem_singleton _
  have hka : σa.kheap p.bv = some (.tcb { x with tcbMcpriority := Fl4Spec.ucast 8 mcp.bv }) := by
    simp [hσa, Notif.updK]
  have hAa : Notif.ActReady σa := actReady_upd (y := { x with tcbMcpriority := Fl4Spec.ucast 8 mcp.bv }) hA2 hk2 rfl rfl
    (by simp [hσa, Notif.updK]) rfl rfl rfl
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
  refine WP.spec_mono (hSC s4 a1 σb p scv scf sco hb4 hp h1 h2 h3) ?_
  rintro r ⟨hS5, hr, σc, hc⟩
  exact ⟨(hS3.trans hS4).trans hS5, hr, σa, σb, σc, ha, hb, hc⟩

end

end

end Fl4Proofs.P3.Sched
