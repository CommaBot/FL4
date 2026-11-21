/-
P3 (DESIGN.md §9), invariant line G2 (KENTRY-PLAN g2d): **`LiveDN` is false
in reachable states** (FINDING). XTopJointWJLRestart's `LiveDN` (`LiveJ` ∧
`DbgWF` ∧ `NullOrig`), the premise `hLv` of `kernel_entryJ33` [J], is
refuted at a `JAtZ` state with `SpecGlob` (l4v `valid_global_refs`, carried
by SInvB) by two situations every FL4 system reaches:

* `liveDN_idle_off`: `LiveJ.dbg` names every TCB on core 0's debug list by a
  thread cap of the MDB; no cap names the idle thread (`SpecGlob.idle`); so
  under `LiveDN` the idle thread is not on core 0's debug list. FL4's boot
  puts it there and nothing takes it off: `boot.rs` `init_core_state`
  appends every core's idle thread to that core's debug list when
  `fl4_abi::config::DEBUG_BUILD` (`true`, Fl4Core/Funs.lean), core 0's idle
  thread has affinity 0 (`create_idle_thread`); `debug_remove` runs only in a
  thread cap's finalisation and in `migrate_tcb`, neither reaches the idle
  thread (no cap names it; it has no SC to rebind). l4v's
  `if_live_then_nonz_cap` exempts the idle thread (it is not `live`).
* `liveDN_irqNode_free`: `LiveJ.slots` names the container of every slot in
  use by a CNode / thread / zombie cap of the MDB; each IRQ node slot is a
  radix-0 CNode of the typed heap (`IntLayout.node`) that no such cap names
  (`SpecGlob.ref` with `IrqRel.node`); so under `LiveDN` every IRQ node slot
  is unused (null cap, original bit clear). The IRQHandler `SetIRQHandler`
  invocation (`interrupt.rs` `decode_irq_handler`: `cdt::insert` of the
  notification cap into `irq_slot`; spec `invokeIRQHandler`'s `capInsert`)
  makes the slot non-null, so every state after a successful
  `SetIRQHandler` breaks `LiveDN`. l4v's `if_unsafe_then_cap` covers an IRQ
  node slot by the IRQ handler cap (`cte_refs (IRQHandlerCap irq)`,
  `appropriate_cte_cap` of a notification cap).

So `LiveDN` needs two exemptions before it can be carried (KENTRY-PLAN g2d):
the idle thread in `dbg`, the IRQ node CNodes in `slots`.
-/
import Fl4Proofs.P3.XTopJointWJLRestart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **Under `LiveDN` the idle thread is off core 0's debug list** (module
docstring). -/
theorem liveDN_idle_off {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hsg : SpecGlob σ)
    (hL : LiveDN (L := L) Z.th H Cs Z.G s σ) (h0 : L.idleW s ≠ 0#u64) (n : Nat) :
    dbgNth (L.mem s) n (dbgHead (L := L) s) ≠ L.idleW s := by
  intro e
  obtain ⟨y, hy, hc⟩ := hL.1.dbg n (by rw [e]; exact h0)
  rw [e] at hc
  have hys : IsSlot Z.th y := ((J.xtop.rel.2.1.2.2.1.members y).1 hy).1
  obtain ⟨sl, hA, rfl⟩ := hys.abs
  obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := J.dstate.1.1.abs_cap hA
  rw [capAt_capV, hc] at hc0; cases eq_of_ok_eq hc0
  rw [hca0.abs] at hg0
  have ha0 := (getCap_set_iff σ sl.1 sl.2 _).1 (congrArg Prod.fst hg0)
  apply hsg.idle sl.1 sl.2 _ ha0 (by simp [IsPageCap, absCap])
  rw [JAtZ.idleThread_eq arI J]; simp [absCap, Fl4Spec.objRefs]

/-- **Under `LiveDN` every IRQ node slot is unused** (module docstring). -/
theorem liveDN_irqNode_free {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hsg : SpecGlob σ)
    (hL : LiveDN (L := L) Z.th H Cs Z.G s σ) (i : U64) (hi : i.val < 128) :
    ¬ InUse (L.mem s) σ (slotOf (nodeA (L.ksb s) i) 0) := by
  intro hu
  have hIS : IsSlotAt Z.th (nodeA (L.ksb s) i) 0 := Or.inl ⟨0, J.intL.node i hi, by norm_num⟩
  obtain ⟨y, hy, hr⟩ := hL.1.slots _ 0 hIS hu
  have hys : IsSlot Z.th y := ((J.xtop.rel.2.1.2.2.1.members y).1 hy).1
  obtain ⟨sl, hA, rfl⟩ := hys.abs
  obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := J.dstate.1.1.abs_cap hA
  rw [capAt_capV] at hc0; cases eq_of_ok_eq hc0
  rw [hca0.abs] at hg0
  have ha0 := (getCap_set_iff σ sl.1 sl.2 _).1 (congrArg Prod.fst hg0)
  have hnode : σ.interruptIrqNode (BitVec.ofNat 8 i.val) = (nodeA (L.ksb s) i).bv :=
    J.xtop.fin.1.1.2.2.2.1.node i hi
  have key : ∀ c : capability.Cap, RefsObj (nodeA (L.ksb s) i) c →
      (nodeA (L.ksb s) i).bv ∈ Fl4Spec.objRefs (absCap c) ∧ ¬ IsPageCap (absCap c) := by
    intro c hc
    cases c <;> simp only [RefsObj] at hc <;> subst hc <;> simp [absCap, Fl4Spec.objRefs, IsPageCap]
  obtain ⟨hin, hnp⟩ := key _ hr
  exact hsg.ref sl.1 sl.2 _ ha0 hnp (BitVec.ofNat 8 i.val) (by rw [hnode]; exact hin)

/-- **`LiveDN` refuted by a set IRQ handler**: an IRQ node slot holding a cap
(what `SetIRQHandler` leaves) contradicts `LiveDN` (module docstring). -/
theorem not_liveDN_of_irqNode {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hsg : SpecGlob σ) (i : U64) (hi : i.val < 128)
    (hc : capV (L.mem s) (slotOf (nodeA (L.ksb s) i) 0) ≠ .Null) :
    ¬ LiveDN (L := L) Z.th H Cs Z.G s σ :=
  fun hL => liveDN_irqNode_free J hsg hL i hi (Or.inl hc)

/-- **`LiveDN` refuted by the idle thread on core 0's debug list** (what FL4's
boot leaves; module docstring). -/
theorem not_liveDN_of_idle {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hsg : SpecGlob σ) (h0 : L.idleW s ≠ 0#u64)
    (hd : ∃ n, dbgNth (L.mem s) n (dbgHead (L := L) s) = L.idleW s) :
    ¬ LiveDN (L := L) Z.th H Cs Z.G s σ :=
  fun hL => let ⟨n, hn⟩ := hd; liveDN_idle_off J hsg hL h0 n hn

end

end

end Fl4Proofs.P3
