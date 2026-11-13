/-
P3 (DESIGN.md §9), CSpace: the CSpace relation across `set_thread_state`.

The CNode invocations set the caller's thread state to `Restart` before
changing slots (FL4 in `decode_copy`, the spec in `handle_invocation`).

* Spec side, `setThreadState_eq`: for a thread of the heap the spec's
  `set_thread_state` has a single outcome, which changes only that TCB's
  `tcb_state` (and maybe the scheduler action): `cdt`, `is_original_cap`
  and every cap are as before.
* FL4 side, `SlotsSame`: the explicit hypothesis that FL4's
  `set_thread_state` leaves the four words of every slot of the typed heap
  alone (it writes the TCB's state word and scheduler state, none of which
  lie in a slot; to be discharged with the scheduler's frame lemmas).
* `restart_rel`: under both, `StateRel`, `SlotsValid`, `MdbLinks` and
  `CdtRel` carry over to the new states.
-/
import Fl4Proofs.P3.CnodeCaps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- Hypothesis on a memory update: the words of every slot of the typed
heap are unchanged. -/
def SlotsSame (th : TypedHeap) (m m' : U64 → U64) : Prop :=
  ∀ a, IsSlot th a → m' a = m a ∧ m' (wordOf a 8#u64) = m (wordOf a 8#u64) ∧
    m' (wordOf a 16#u64) = m (wordOf a 16#u64) ∧ m' (wordOf a 24#u64) = m (wordOf a 24#u64)

section
variable {th : TypedHeap} {m m' : U64 → U64}

theorem SlotsSame.capAt (h : SlotsSame th m m') {a : U64} (ha : IsSlot th a) : capAt m' a = capAt m a := by
  obtain ⟨h0, h8, -, -⟩ := h a ha
  unfold Fl4Proofs.P3.capAt; rw [h0]; exact congrArg _ h8

theorem SlotsSame.prevOf (h : SlotsSame th m m') {a : U64} (ha : IsSlot th a) : prevOf m' a = prevOf m a :=
  (h a ha).2.2.1

theorem SlotsSame.nextOf (h : SlotsSame th m m') {a : U64} (ha : IsSlot th a) : nextOf m' a = nextOf m a := by
  unfold Fl4Proofs.P3.nextOf; rw [(h a ha).2.2.2]

theorem SlotsSame.revOf (h : SlotsSame th m m') {a : U64} (ha : IsSlot th a) : revOf m' a = revOf m a := by
  unfold Fl4Proofs.P3.revOf; rw [(h a ha).2.2.2]

theorem MdbLinks.of_same {G : MdbGhost} (hM : MdbLinks th m G) (h : SlotsSame th m m') : MdbLinks th m' G := by
  have hs : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x hx => ((hM.members x).1 hx).1
  refine ⟨hM.tree, hM.ne_nil, ?_, ?_, ?_, ?_⟩
  · intro ch hch
    apply (hM.chain ch hch).imp_of_mem_imp
    rintro a b ha hb ⟨h1, h2⟩
    have haf := hs a (List.mem_flatten.2 ⟨_, hch, ha⟩)
    have hbf := hs b (List.mem_flatten.2 ⟨_, hch, hb⟩)
    exact ⟨by rw [h.nextOf haf, h1], by rw [h.prevOf hbf, h2]⟩
  · intro ch hch hne
    rw [h.prevOf (hs _ (List.mem_flatten.2 ⟨_, hch, List.head_mem hne⟩)), hM.head ch hch hne]
  · intro ch hch hne
    rw [h.nextOf (hs _ (List.mem_flatten.2 ⟨_, hch, List.getLast_mem hne⟩)), hM.last ch hch hne]
  · intro a
    rw [hM.members a]
    constructor
    · rintro ⟨ha, c, hc, hn⟩; exact ⟨ha, c, by rw [h.capAt ha, hc], hn⟩
    · rintro ⟨ha, c, hc, hn⟩; exact ⟨ha, c, by rw [← h.capAt ha, hc], hn⟩

theorem CdtRel.of_same {Z : Type} {σ σ' : Fl4Spec.State Z} {G : MdbGhost} (hC : CdtRel th m σ G)
    (h : SlotsSame th m m') (hcdt : σ'.cdt = σ.cdt) (hio : σ'.isOriginalCap = σ.isOriginalCap) :
    CdtRel th m' σ' G := by
  refine ⟨fun sl hs => ?_, fun sl q hq => ?_, fun sl hs => ?_, hC.par_slot⟩
  · rw [hcdt]; exact hC.cdt sl hs
  · rw [hcdt] at hq; exact hC.cdt_slot sl q hq
  · rw [hio, hC.orig sl hs, h.revOf hs.isSlot]

end

/-! ## The spec's `set_thread_state` -/

section
variable {Z : Type}

theorem setThreadState_eq (σ : Fl4Spec.State Z) (t : Fl4Spec.ObjRef) (tcb : Fl4Spec.Tcb)
    (hk : σ.kheap t = some (.tcb tcb)) (ts : Fl4Spec.ThreadState) :
    ∃ σ1, Fl4Spec.setThreadState (Z := Z) t ts σ = ({((), σ1)}, False) ∧
      σ1.kheap = Function.update σ.kheap t (some (.tcb { tcb with tcbState := ts })) ∧
      σ1.cdt = σ.cdt ∧ σ1.isOriginalCap = σ.isOriginalCap := by
  set σ0 : Fl4Spec.State Z := { σ with kheap := Function.update σ.kheap t (some (.tcb { tcb with tcbState := ts })) }
  have hg : Fl4Spec.NonDet.getsThe (Fl4Spec.getTcb (Z := Z) t) σ = ({(tcb, σ)}, False) := by
    simp [Fl4Spec.NonDet.getsThe, Fl4Spec.getTcb, Fl4Spec.readObject, hk, Fl4Spec.NonDet.assertOpt]; rfl
  have ho : Fl4Spec.getObject (Z := Z) t σ = ({(.tcb tcb, σ)}, False) := by
    simp [Fl4Spec.getObject, Fl4Spec.NonDet.getsThe, Fl4Spec.readObject, hk, Fl4Spec.NonDet.assertOpt]; rfl
  have ha : (Fl4Spec.NonDet.assert (Fl4Spec.aType (.tcb tcb) = Fl4Spec.aType (.tcb { tcb with tcbState := ts })) :
      Fl4Spec.NonDet (Fl4Spec.State Z) Unit) σ = ({((), σ)}, False) := by
    simp [Fl4Spec.NonDet.assert, Fl4Spec.aType]
  have h1 : Fl4Spec.threadSet (Z := Z) (fun tcb => { tcb with tcbState := ts }) t σ = ({((), σ0)}, False) := by
    unfold Fl4Spec.threadSet
    rw [nd_bind_single hg]
    unfold Fl4Spec.setObject
    rw [nd_bind_single ho, nd_bind_single ha, nd_bind_single (show Fl4Spec.NonDet.get σ = ({(σ, σ)}, False) from rfl)]
    rfl
  unfold Fl4Spec.setThreadState
  rw [nd_bind_one h1]
  unfold Fl4Spec.setThreadStateAct
  rw [nd_bind_single (show Fl4Spec.NonDet.gets _ σ0 = _ from rfl),
    nd_bind_single (show Fl4Spec.NonDet.gets _ σ0 = _ from rfl),
    nd_bind_single (show Fl4Spec.NonDet.gets _ σ0 = _ from rfl)]
  unfold Fl4Spec.NonDet.when
  split
  · exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact ⟨σ0, rfl, rfl, rfl, rfl⟩

/-- The CSpace relation does not look at thread states. -/
theorem StateRel.tcb_state {th : TypedHeap} {m : U64 → U64} {σ σ1 : Fl4Spec.State Z} (hR : StateRel th m σ)
    {t : Fl4Spec.ObjRef} {tcb : Fl4Spec.Tcb} (hk : σ.kheap t = some (.tcb tcb)) {ts : Fl4Spec.ThreadState}
    (h1 : σ1.kheap = Function.update σ.kheap t (some (.tcb { tcb with tcbState := ts }))) :
    StateRel th m σ1 := by
  refine ⟨fun p r hp => ?_, fun t' ht' => ?_⟩
  · obtain ⟨cs, hk', hwf, hs⟩ := hR.cnode p r hp
    have hne : p.bv ≠ t := by intro e; rw [e, hk] at hk'; cases hk'
    exact ⟨cs, by rw [h1, Function.update_of_ne hne]; exact hk', hwf, hs⟩
  · obtain ⟨tcb', hk', hs⟩ := hR.tcb t' ht'
    by_cases he : t'.bv = t
    · rw [he, hk] at hk'
      cases hk'
      exact ⟨{ tcb with tcbState := ts }, by rw [h1, he, Function.update_self], fun i hi => hs i hi⟩
    · exact ⟨tcb', by rw [h1, Function.update_of_ne he]; exact hk', hs⟩

/-- **The CSpace relation across `set_thread_state`**: the spec's single
outcome, with FL4's memory satisfying `SlotsSame`. -/
theorem restart_rel {th : TypedHeap} {m m' : U64 → U64} {σ : Fl4Spec.State Z} {G : MdbGhost}
    (hR : StateRel th m σ) (hV : SlotsValid th m) (hM : MdbLinks th m G) (hC : CdtRel th m σ G)
    (hS : SlotsSame th m m') {t : Fl4Spec.ObjRef} {tcb : Fl4Spec.Tcb} (hk : σ.kheap t = some (.tcb tcb))
    (ts : Fl4Spec.ThreadState) :
    ∃ σ1, Fl4Spec.setThreadState (Z := Z) t ts σ = ({((), σ1)}, False) ∧
      StateRel th m' σ1 ∧ SlotsValid th m' ∧ MdbLinks th m' G ∧ CdtRel th m' σ1 G ∧
      σ1.cdt = σ.cdt ∧ σ1.isOriginalCap = σ.isOriginalCap := by
  obtain ⟨σ1, he, hk1, hcdt, hio⟩ := setThreadState_eq σ t tcb hk ts
  have hcap : ∀ x, IsSlot th x → capAt m' x = capAt m x := fun x hx => hS.capAt hx
  exact ⟨σ1, he, (hR.tcb_state hk hk1).of_caps hcap, hV.of_caps hcap, hM.of_same hS,
    hC.of_same hS hcdt hio, hcdt, hio⟩

end

end

end Fl4Proofs.P3
