/-
P3 (DESIGN.md §9), interrupts: **the IRQ state and IRQ node against the
spec's `interrupt_states` and `interrupt_irq_node`** (`IrqRel`), for the
IRQs FL4 has (0..127):

* the state word of IRQ `i` (kernel-state offset `IRQ_STATE + 8 i`) is the
  spec's state (`irqSt`: 0 inactive, 1 signal, 2 timer, otherwise reserved;
  FL4's IPI state 3 has no spec counterpart);
* the spec's IRQ node slot of `i` is the slot `IRQ_NODE + 32 i` of the
  kernel-state block, a radix-0 CNode of the typed heap (`IntLayout`), so
  the CSpace relation covers it.

`IntLayout` also puts the state words outside every object. The lemmas:
FL4's `is_irq_active` and `irq_slot`, the spec's `is_irq_active` and
`get_irq_slot`, and `set_irq_state` on both sides.
-/
import Fl4Proofs.P3.FinalInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- Offset of IRQ `irq`'s state word in the kernel-state block. -/
def irqOff (irq : U64) : U64 := core.num.U64.wrapping_add 224#u64 (core.num.U64.wrapping_mul irq 8#u64)

/-- Address of IRQ `irq`'s state word. -/
def irqStA (kb irq : U64) : U64 := core.num.U64.wrapping_add kb (irqOff irq)

/-- Address of IRQ `irq`'s node slot. -/
def nodeA (kb irq : U64) : U64 :=
  core.num.U64.wrapping_add (core.num.U64.wrapping_add kb 1248#u64) (core.num.U64.wrapping_mul irq 32#u64)

/-- FL4's IRQ state word as the spec's state. -/
def irqSt (w : U64) : Fl4Spec.IrqState :=
  if w = 0#u64 then .irqInactive else if w = 1#u64 then .irqSignal else if w = 2#u64 then .irqTimer
  else .irqReserved

theorem irqSt_inactive (w : U64) : irqSt w = .irqInactive ↔ w = 0#u64 := by
  unfold irqSt; split_ifs <;> simp_all

theorem irq_state_eq : layout.ks.IRQ_STATE = ok 224#u64 := by
  obtain ⟨v, hv, rfl⟩ := spec_exists P0.Consts.layout.ks.IRQ_STATE.spec; exact hv

theorem irq_node_eq : layout.ks.IRQ_NODE = ok 1248#u64 := by
  obtain ⟨v, hv, rfl⟩ := spec_exists P0.Consts.layout.ks.IRQ_NODE.spec; exact hv

theorem state_off_eq (irq : U64) : interrupt.state_off irq = ok (irqOff irq) := by
  unfold interrupt.state_off; simp only [lift, bind_ok, irq_state_eq]; rfl

/-- The kernel-state block's interrupt part, against the typed heap. -/
structure IntLayout (th : TypedHeap) (kb : U64) : Prop where
  fit : kb.val + 13568 ≤ 2 ^ 64
  align : kb.val % 32 = 0
  st_out : ∀ i : U64, i.val < 128 → OutsideObjects th (irqStA kb i)
  node : ∀ i : U64, i.val < 128 → th (nodeA kb i) = some (.cnode 0)

/-- The IRQ states and node, against the spec's. -/
structure IrqRel (mem : U64 → U64) (kb : U64) (σ : Fl4Spec.State Unit) : Prop where
  st : ∀ i : U64, i.val < 128 → σ.interruptStates (BitVec.ofNat 8 i.val) = irqSt (mem (irqStA kb i))
  node : ∀ i : U64, i.val < 128 → σ.interruptIrqNode (BitVec.ofNat 8 i.val) = (nodeA kb i).bv

theorem irqStA_val {kb i : U64} (hf : kb.val + 13568 ≤ 2 ^ 64) (hi : i.val < 128) :
    (irqStA kb i).val = kb.val + 224 + 8 * i.val := by
  unfold irqStA irqOff
  simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
  simp [U64.size, U64.numBits]
  omega

theorem nodeA_val {kb i : U64} (hf : kb.val + 13568 ≤ 2 ^ 64) (hi : i.val < 128) :
    (nodeA kb i).val = kb.val + 1248 + 32 * i.val := by
  unfold nodeA
  simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
  simp [U64.size, U64.numBits]
  omega

theorem irqStA_inj {kb i j : U64} (hf : kb.val + 13568 ≤ 2 ^ 64) (hi : i.val < 128) (hj : j.val < 128)
    (h : irqStA kb i = irqStA kb j) : i = j := by
  have h1 := irqStA_val hf hi; have h2 := irqStA_val hf hj
  rw [h] at h1
  exact UScalar.eq_of_val_eq (by omega)

theorem ofNat8_inj {i j : U64} (hi : i.val < 128) (hj : j.val < 128)
    (h : (BitVec.ofNat 8 i.val : BitVec 8) = BitVec.ofNat 8 j.val) : i = j := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  exact UScalar.eq_of_val_eq (by omega)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem irq_slot_eq (s : S) (irq : U64) : interrupt.irq_slot st s irq = ok (nodeA (L.ksb s) irq) := by
  unfold interrupt.irq_slot
  simp only [L.ks_base_eq, irq_node_eq, lift, bind_ok]
  have : layout.cte.SIZE = 32#u64 := by unfold layout.cte.SIZE; rfl
  rw [this]; rfl

theorem is_irq_active_eq (s : S) (irq : U64) :
    interrupt.is_irq_active st s irq = ok (decide (L.mem s (irqStA (L.ksb s) irq) ≠ 0#u64)) := by
  unfold interrupt.is_irq_active interrupt.irq_state obj.ks_get
  simp only [state_off_eq, L.ks_base_eq, lift, L.read_eq, bind_ok]
  by_cases h : L.mem s (irqStA (L.ksb s) irq) = 0#u64
  · unfold irqStA at h; simp [h, interrupt.IRQ_INACTIVE, irqStA]
  · unfold irqStA at h; simp [h, interrupt.IRQ_INACTIVE, irqStA]

end

/-! ## The spec side -/

section
open Fl4Spec

theorem isIrqActive_run {mem : U64 → U64} {kb : U64} {σ : State Unit} (hI : IrqRel mem kb σ) {i : U64}
    (hi : i.val < 128) :
    isIrqActive (Z := Unit) (BitVec.ofNat 8 i.val) σ = ({(decide (mem (irqStA kb i) ≠ 0#u64), σ)}, False) := by
  unfold isIrqActive getIrqState
  show (NonDet.bind (NonDet.gets _) _) σ = _
  simp only [NonDet.bind, NonDet.gets, NonDet.pure]
  rw [hI.st i hi]
  have : decide (irqSt (mem (irqStA kb i)) ≠ IrqState.irqInactive) = decide (mem (irqStA kb i) ≠ 0#u64) := by
    simp [irqSt_inactive]
  refine Prod.ext ?_ ?_
  · ext r; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, exists_eq_left]; rw [this]
  · simp

/-- The spec's `set_irq_state`: the state updated, the IRQ masked. -/
def setIrqSt (sti : IrqState) (irq : Irq) (σ : State Unit) : State Unit :=
  { σ with interruptStates := Function.update σ.interruptStates irq sti,
           machineState := { σ.machineState with
             irqMasks := Function.update σ.machineState.irqMasks irq (decide (sti = .irqInactive)) } }

theorem setIrqState_mem' (sti : IrqState) (irq : Irq) (σ : State Unit) :
    ((), setIrqSt sti irq σ) ∈ (setIrqState (Z := Unit) sti irq σ).1 := by
  let σ1 : State Unit := { σ with interruptStates := Function.update σ.interruptStates irq sti }
  let ms' : MachineState := { σ1.machineState with
    irqMasks := Function.update σ1.machineState.irqMasks irq (decide (sti = .irqInactive)) }
  unfold setIrqState doMachineOp maskInterrupt
  refine mem_bind_nd (x := ((), σ1)) rfl ?_
  refine mem_bind_nd (x := (σ1.machineState, σ1)) rfl ?_
  refine mem_bind_nd (x := (((), ms'), σ1)) ⟨rfl, rfl⟩ ?_
  refine mem_bind_nd (x := ((), { σ1 with machineState := ms' })) (Set.mem_singleton _) ?_
  rfl

theorem getIrqSlot_run (irq : Irq) (σ : State Unit) :
    getIrqSlot (Z := Unit) irq σ = ({((σ.interruptIrqNode irq, []), σ)}, False) := rfl

end

theorem cslotAddr_nil (p : U64) : cslotAddr (p.bv, []) = p := by
  unfold cslotAddr slotAddr; simp [Fl4Spec.ofBl]

/-! ## `set_irq_state` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem set_irq_state_eq (s : S) (a : A) (sv irq : U64) {a' : A}
    (hm : arI.mask_irq a irq (decide (sv = interrupt.IRQ_INACTIVE)) = ok a') :
    interrupt.set_irq_state st arI s a sv irq = ok (L.wr s (irqStA (L.ksb s) irq) sv, a') := by
  unfold interrupt.set_irq_state obj.ks_set
  simp only [state_off_eq, L.ks_base_eq, lift, L.write_eq, bind_ok]
  rw [hm]; simp only [bind_ok]; rfl

theorem IntLayout.slotsSame {th : TypedHeap} (hP : Placed th) {kb : U64} (hL : IntLayout th kb) (s : S)
    {i : U64} (hi : i.val < 128) (v : U64) :
    SlotsSame th (L.mem s) (L.mem (L.wr s (irqStA kb i) v)) := by
  have ho := hL.st_out i hi
  refine slotsSame_wr hP s _ ho.1 (fun x hx => ?_)
  obtain ⟨p, k, hk, h1, h2, -⟩ := slot_in_object hP hx
  have := ho.2 p k hk
  omega

/-- `IrqRel` after writing IRQ `i`'s state word. -/
theorem IrqRel.wr {th : TypedHeap} {kb : U64} (hL : IntLayout th kb) {s : S} {σ : Fl4Spec.State Unit}
    (hI : IrqRel (L.mem s) kb σ) {i : U64} (hi : i.val < 128) (v : U64) (σ' : Fl4Spec.State Unit)
    (hst : σ'.interruptStates = Function.update σ.interruptStates (BitVec.ofNat 8 i.val) (irqSt v))
    (hnd : σ'.interruptIrqNode = σ.interruptIrqNode) :
    IrqRel (L.mem (L.wr s (irqStA kb i) v)) kb σ' := by
  refine ⟨fun j hj => ?_, fun j hj => by rw [hnd]; exact hI.node j hj⟩
  rw [hst, L.mem_wr _ _ _ _ (hL.st_out i hi).1 (hL.st_out j hj).1]
  by_cases hij : i = j
  · subst hij; simp
  · rw [Function.update_of_ne (fun e => hij (ofNat8_inj hj hi e).symm), if_neg
      (fun e => hij (irqStA_inj hL.fit hi hj e))]
    exact hI.st j hj

end


/-! ## `set_thread_state` on both sides: the interrupt state is kept -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

attribute [local step] tcb_state_spec' sc_is_null_spec' action_spec' set_action_spec' cur_thread_spec'
  is_schedulable_spec'

/-- FL4's `set_thread_state t v`: the state word, and maybe the scheduler
action. -/
theorem set_thread_state_cases (s : S) (t v : U64) :
    sched.set_thread_state st s t v ⦃ s' => s' = L.wr s (stA t) v ∨
      s' = L.wr (L.wr s (stA t) v) (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) sched.ACTION_CHOOSE_NEW ⦄ := by
  unfold sched.set_thread_state sched.schedule_tcb
  rw [tcb_set_state_eq]; simp only [bind_ok]
  step*
  all_goals first
    | (subst_vars; exact Or.inl rfl)
    | (subst_vars; right; simp)

theorem set_thread_state_ksb (s : S) (t v : U64) :
    sched.set_thread_state st s t v ⦃ s' => L.ksb s' = L.ksb s ⦄ :=
  WP.spec_mono (set_thread_state_cases s t v) (by rintro s' (rfl | rfl) <;> simp)

end

section
open Fl4Spec

/-- The spec's `set_thread_state` keeps the interrupt state, the CDT and
the arch and machine state. -/
theorem setThreadState_keeps {σ σ1 : State Unit} {t : ObjRef} {tcb : Tcb} (hk : σ.kheap t = some (.tcb tcb))
    {ts : ThreadState} (h : setThreadState (Z := Unit) t ts σ = ({((), σ1)}, False)) :
    σ1.interruptIrqNode = σ.interruptIrqNode ∧ σ1.interruptStates = σ.interruptStates ∧
      σ1.archState = σ.archState ∧ σ1.machineState = σ.machineState ∧ σ1.curThread = σ.curThread := by
  set σ0 : State Unit := { σ with kheap := Function.update σ.kheap t (some (.tcb { tcb with tcbState := ts })) }
  have hg : NonDet.getsThe (getTcb (Z := Unit) t) σ = ({(tcb, σ)}, False) := by
    simp [NonDet.getsThe, getTcb, readObject, hk, NonDet.assertOpt]; rfl
  have ho : getObject (Z := Unit) t σ = ({(.tcb tcb, σ)}, False) := by
    simp [getObject, NonDet.getsThe, readObject, hk, NonDet.assertOpt]; rfl
  have ha : (NonDet.assert (aType (.tcb tcb) = aType (.tcb { tcb with tcbState := ts })) :
      NonDet (State Unit) Unit) σ = ({((), σ)}, False) := by
    simp [NonDet.assert, aType]
  have h1 : threadSet (Z := Unit) (fun tcb => { tcb with tcbState := ts }) t σ = ({((), σ0)}, False) := by
    unfold threadSet
    rw [nd_bind_single hg]
    unfold setObject
    rw [nd_bind_single ho, nd_bind_single ha, nd_bind_single (show NonDet.get σ = ({(σ, σ)}, False) from rfl)]
    rfl
  unfold setThreadState at h
  rw [nd_bind_one h1] at h
  unfold setThreadStateAct at h
  rw [nd_bind_single (show NonDet.gets _ σ0 = _ from rfl),
    nd_bind_single (show NonDet.gets _ σ0 = _ from rfl),
    nd_bind_single (show NonDet.gets _ σ0 = _ from rfl)] at h
  unfold NonDet.when at h
  split at h
  · have := congrArg Prod.fst h
    simp only [setSchedulerAction, NonDet.modify, Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    subst this; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · have := congrArg Prod.fst h
    simp only [NonDet.pure, Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    subst this; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end

end

end Fl4Proofs.P3
