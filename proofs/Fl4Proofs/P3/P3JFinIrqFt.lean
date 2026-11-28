/-
P3 (p3J gen 43): **bucket 3, the IRQ handler finaliser inside `ProjW`** at the deletion loop's invariant `WJL`
(the last native cap kind of `FinObjKind` without a `ProjW` footprint after P3JFinAll).

FL4 `objects.rs` l.251–259 (`finalise_cap`: an IRQ handler cap, when final, runs `deleting_irq_handler`, then
`finalise_cap_object`'s `IrqHandler` arm, which writes nothing), `interrupt.rs` l.95–98 (`deleting_irq_handler`:
`delete_one` of the IRQ's node slot). At a `WJL` state the node slot holds a null or a notification cap
(XTopJointDelR's `jIrqSlotHyp` route: `irqSlotOK_of_spec` at `JAtZ.intL` with `SpecGlob.irqNode`, l4v
`valid_irq_node`), and is a slot of the typed heap (`IntLayout.node`). A null slot: `delete_one` writes nothing; a
notification cap: gen 37's `delete_one_ntfnProjW` (P3JCapIrq).

* **`finIrqProjW`**: `finalise_cap` of `IrqHandler i` (`i < 128`, the cap's `CapWf`) at a `WJL` state writes only
  `ProjW H Cs s`.

No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JDelFt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 43) **An IRQ handler cap's finalisation at `WJL` writes only `ProjW`** (module docstring). -/
theorem finIrqProjW [Fl4Proofs.P1.PlainStore st] (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost} (hDS : DState (L := L) Z.th s σ G)
    (hW : WJL (L := L) arI AR Z H Cs kb s a σ G) {i : U64} (hi : i.val < 128) (fin ex : Bool) :
    objects.finalise_cap st arI s a (.IrqHandler i) fin ex ⦃ r =>
      P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  obtain ⟨V, Ac0, Lst0, D0, J, -, -, hsg, -⟩ := hW.1
  have hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) i) :=
    irqSlotOK_of_spec J.intL J.xtop.rel.2.1.1 J.xtop.fin.1.1.2.2.2.1 hsg.irqNode hi
  have hfo : ∀ (s1 : S) (a1 : A) (f : Bool), objects.finalise_cap_object st arI s1 a1 (.IrqHandler i) f =
      ok (if f then (.Null, .IrqHandler i) else (.Null, .Null), s1, a1) := fun _ _ f => by
    cases f <;> rfl
  unfold objects.finalise_cap
  cases fin
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    show objects.finalise_cap_object st arI s a (.IrqHandler i) false ⦃ r =>
        P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄
    rw [hfo]
    exact (WP.spec_ok _).2 (P1.WritesIn.refl _ _)
  simp only [↓reduceIte]
  unfold interrupt.deleting_irq_handler
  rw [irq_slot_eq]; simp only [bind_ok]
  have hA' : AbsSlot Z.th ((nodeA (L.ksb s) i).bv, []) := ⟨_, rfl, Or.inl (by simpa using J.intL.node i hi)⟩
  have hcs : cslotAddr ((nodeA (L.ksb s) i).bv, ([] : List Bool)) = nodeA (L.ksb s) i := cslotAddr_nil _
  rcases hok with hnull | ⟨p, b, w, r, hn⟩
  · obtain ⟨c0, ac0, hc0, -, -⟩ := hDS.1.1.abs_cap hA'
    have hcv0 := capV_of_capAt hc0
    rw [hcs] at hcv0
    rw [hcv0] at hnull; subst hnull
    have e1 : cdt.delete_one st arI s a (nodeA (L.ksb s) i) = ok (s, a) := by
      unfold cdt.delete_one
      rw [slot_cap_eq, ← hcs, hc0]
      simp only [bind_ok, cap_is_null_eq, isNullB, ↓reduceIte]
    rw [e1]; simp only [bind_ok]
    show objects.finalise_cap_object st arI s a (.IrqHandler i) true ⦃ r =>
        P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄
    rw [hfo]
    exact (WP.spec_ok _).2 (P1.WritesIn.refl _ _)
  · have hd := delete_one_ntfnProjW arI Z H Cs kb hDS hW hA' (by rw [hcs]; exact hn)
    rw [hcs] at hd
    refine WP.spec_bind hd ?_
    rintro ⟨s1, a1⟩ w1
    show objects.finalise_cap_object st arI s1 a1 (.IrqHandler i) true ⦃ r =>
        P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄
    rw [hfo]
    exact (WP.spec_ok _).2 w1

end

end Fl4Proofs.P3
