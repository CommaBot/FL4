/-
P3 (p3J gen 24): **the interrupt handler's footprint inside `ProjW`, for every line that is not a signal line.**

FL4's `interrupt.handle_interrupt … irq` (crates/fl4-core/src/interrupt.rs) branches on the IRQ state word:
a line above `layout::irq::MAX` is masked and acknowledged (no store write); `IRQ_SIGNAL` reads the handler slot
and may `send_signal`; `IRQ_TIMER` writes the current node's `REPROGRAM` / `ARMED` words (P2/EntryIrq's
`interrupt.handle_interrupt.timer`); `IRQ_IPI` runs `smp::handle_ipi` (`reschedule_required` on the reschedule
IPI: P2's `sched.reschedule_required.kwN`); every other state only masks / acknowledges.

* **`handle_interrupt_footN0`** (FL4 only): from P1's `BXI`, when the line is above `MAX` or its state word is
  not `IRQ_SIGNAL` (= 1), the handler is a P2 `FootN` step (`KWN` with no protected thread, `Kp = ∅`,
  `Nd = False`: no core's `IDLE_THREAD` / `IDLE_SC` word).
* **`JAtZ.handleIrqProjW`**: at a `JAtZ` state, if the spec state of the line (`IrqRel.st`) is not
  `IRQSignal`, the handler writes only `ProjW H Cs s` (P3JMcKwN's `projW_of_cur0wN`).
* `WritesIn.projW_trans`, `projW_ksb`: `ProjW` footprints compose along a run (`ProjW` reads the store only
  through the kernel-state base and the core number, which a `WritesIn` step keeps).

No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMcKwN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- `ProjW` reads the store only through the kernel-state base and the core number. -/
theorem projW_ksb {H : P1.Heap} {Cs : Set U64} {s s' : S} (h1 : L.ksb s' = L.ksb s) (h2 : L.cpu s' = L.cpu s)
    {b : U64} : ProjW (L := L) H Cs s' b ↔ ProjW (L := L) H Cs s b := by
  simp only [ProjW, LawfulStore.nodeBase, h1, h2]

/-- **`ProjW` footprints compose.** -/
theorem _root_.Fl4Proofs.P1.WritesIn.projW_trans {H : P1.Heap} {Cs : Set U64} {s s1 s2 : S}
    (h1 : P1.WritesIn st s s1 (ProjW (L := L) H Cs s)) (h2 : P1.WritesIn st s1 s2 (ProjW (L := L) H Cs s1)) :
    P1.WritesIn st s s2 (ProjW (L := L) H Cs s) :=
  (h1.trans h2).mono fun _ hb => hb.elim id fun hb => (projW_ksb h1.1 h1.2.1).1 hb

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {T Ω : Set U64} {H : P1.Heap} {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac Es : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`handle_interrupt` off the signal lines is a `FootN` step** (module docstring). -/
theorem handle_interrupt_footN0 (hA : P0.ArchTotal ar) (s : S) (a : A) (irq : U64)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hns : irq.val ≤ 127 → L.mem s (irqStA (L.ksb s) irq) ≠ 1#u64) :
    interrupt.handle_interrupt st ar s a irq ⦃ r => FootN st ∅ False T Cs Sg Scs Z Es s r.1 ⦄ := by
  have hq := h.1.choose_spec.choose_spec
  by_cases hle : irq.val ≤ 127
  · have hv := hns hle
    by_cases ht : L.mem s (irqStA (L.ksb s) irq) = interrupt.IRQ_TIMER
    · have hst : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER := by rw [irq_state_eq', ht]
      refine WP.spec_mono (Fl4Proofs.P2.Stall.interrupt.handle_interrupt.timer (Kp := ∅) (Nd := False) (Es := Es)
        hA s a irq hle hst h) ?_
      rintro ⟨s', a'⟩ hr
      first
        | exact hr.2.1
        | (simp only [WP.uncurry'_pair] at hr; exact hr.2.1)
    · unfold interrupt.handle_interrupt
      step with layout.irq.MAX.spec as ⟨mx, emx⟩
      have hmx : mx.val = 127 := by rw [emx]; simp
      split
      · rename_i hgt
        exfalso
        simp at hgt
        omega
      rw [irq_state_eq']
      simp only [bind_ok]
      refine WP.spec_bind (Pₘ := fun r : S × A => FootN st ∅ False T Cs Sg Scs Z Es s r.1) ?_ ?_
      · split
        · rename_i he
          exact absurd (he.trans irqSig_eq) hv
        split
        all_goals first
          | (rename_i he; exact absurd he ht)
          | (unfold smp.handle_ipi
             step with layout.irq.RESCHEDULE_IPI.spec as ⟨ri, eri⟩
             split
             · refine WP.spec_bind (sched.reschedule_required.kwN (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es)
                 (Kp := ∅) (Nd := False) s hq (fun _ h' => by simp at h')) fun s1 f1 => ?_
               exact (WP.spec_ok _).2 f1
             · exact (WP.spec_ok _).2 (FootN.refl s))
          | (refine WP.spec_bind (Pₘ := fun _ : A => True) ?_ fun t _ => (WP.spec_ok _).2 (FootN.refl s)
             first
               | exact WP.spec_mono (hA.mask_irq a irq true) fun _ _ => trivial
               | exact (WP.spec_ok _).2 trivial
               | (split
                  · exact WP.spec_mono (hA.mask_irq a irq true) fun _ _ => trivial
                  · exact (WP.spec_ok _).2 trivial))
          | (split
             all_goals first
               | (rename_i he; exact absurd he ht)
               | (unfold smp.handle_ipi
                  step with layout.irq.RESCHEDULE_IPI.spec as ⟨ri, eri⟩
                  split
                  · refine WP.spec_bind (sched.reschedule_required.kwN (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es)
                      (Kp := ∅) (Nd := False) s hq (fun _ h' => by simp at h')) fun s1 f1 => ?_
                    exact (WP.spec_ok _).2 f1
                  · exact (WP.spec_ok _).2 (FootN.refl s))
               | (refine WP.spec_bind (Pₘ := fun _ : A => True) ?_ fun t _ => (WP.spec_ok _).2 (FootN.refl s)
                  first
                    | exact WP.spec_mono (hA.mask_irq a irq true) fun _ _ => trivial
                    | exact (WP.spec_ok _).2 trivial
                    | (split
                       · exact WP.spec_mono (hA.mask_irq a irq true) fun _ _ => trivial
                       · exact (WP.spec_ok _).2 trivial))
               | (split
                  all_goals first
                    | (rename_i he; exact absurd he ht)
                    | (refine WP.spec_bind (Pₘ := fun _ : A => True) ?_ fun t _ => (WP.spec_ok _).2 (FootN.refl s)
                       first
                         | exact WP.spec_mono (hA.mask_irq a irq true) fun _ _ => trivial
                         | exact (WP.spec_ok _).2 trivial)))
      · rintro ⟨s1, a1⟩ h1
        try simp only [WP.uncurry'_pair] at h1
        try dsimp only
        refine WP.spec_bind (hA.ack_irq a1 irq) fun a2 _ => ?_
        exact (WP.spec_ok _).2 h1
  · unfold interrupt.handle_interrupt
    step with layout.irq.MAX.spec as ⟨mx, emx⟩
    have hmx : mx.val = 127 := by rw [emx]; simp
    split
    · refine WP.spec_bind (hA.mask_irq a irq true) fun a1 _ => ?_
      refine WP.spec_bind (hA.ack_irq a1 irq) fun a2 _ => ?_
      exact (WP.spec_ok _).2 (FootN.refl s)
    · rename_i hng
      exfalso
      simp at hng
      omega

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

/-- **At a `JAtZ` state, the handler of a line whose spec state is not `IRQSignal` writes only `ProjW`**
(module docstring). -/
theorem JAtZ.handleIrqProjW (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (w : U64)
    (hns : w.val ≤ 127 → σ.interruptStates (BitVec.ofNat 8 w.val) ≠ .irqSignal) :
    interrupt.handle_interrupt st arI s a w ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ := by
  have hIR : IrqRel (L.mem s) (L.ksb s) σ := J.xtop.fin.1.1.2.2.2.1
  have hb := BlkOK.bxi J.blk
  refine WP.spec_mono (handle_interrupt_footN0 (Es := EH H) hA s a w hb fun hle e => hns hle ?_) fun r hr =>
    projW_of_cur0wN J ((WritesA.w hr).mono fun _ hb => Or.inl hb)
  rw [hIR.st w (by omega), e]
  simp [irqSt]

end

end Fl4Proofs.P3.Mc
