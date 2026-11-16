/-
P3 (DESIGN.md §9), interrupts: **the IRQ handler cap at the composite
relation** (`IrqXHyp` for `.IrqHandler`).

`decode_invocation_irq_handlerX`: every label (`Ack`, `SetNotification`,
`Clear`, the others), from `HPost`'s `Steps` (the restart, the unmask, the
deletion of the IRQ slot's cap, the new cap's insertion) and `Steps.xtop`;
the kernel-global base kept by IrqDom's `irq_handler_dk4` (its `DomPlaced`
and `IrqDelP1`).
-/
import Fl4Proofs.P3.XTopCaps
import Fl4Proofs.P3.IrqDom
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`IrqXHyp` for the IRQ handler cap**: beyond
`decode_invocation_irq_handler`'s hypotheses and `irq_handler_dk4`'s,
`XTopAt` at its typed heap, `KsApart`, the current thread runnable, the
typed heap's TCBs in `Z.T`, `ARMask` and `XDelNtfnHyp`. -/
theorem decode_invocation_irq_handlerX {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR)
    (th : TypedHeap) (hP : Placed th)
    (hO : FinObjHyp (L := L) arI th) (hPD : PostDelHyp (L := L) arI th) (hK : NtfnKeepHyp (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = irqHLabelOf lbl)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (irq : U64) (hirq : irq.val < 128) (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : lbl.val = 35 → ExtraSRel th (L.mem s) x0 excaps) (hxn : lbl.val = 35 → x0 ≠ nodeA (L.ksb s) irq)
    (hFR : MdbOKV (L.ksb s) (L.mem s) G) (hD : DomPlaced (L := L) th s) (hP1 : IrqDelP1 (L := L) s ct irq)
    {Z : XSets} (hth : Z.th = th) (hX0 : XTopAt (L := L) AR Z s ar σ)
    (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ) (hTh : ∀ t, th t = some .tcb → t ∈ Z.T)
    (hDel : XDelNtfnHyp (L := L) arI AR th)
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot (.IrqHandler irq) blk call don fp buf extra slbl
      args ci sl excaps buffer ct := by
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (WP.spec_and (irq_handler_decode_refines arI th hP hO hPD hK s ar σ G hDS hL hIR lbl slbl hlbl
    ct hct hcur htcb hact hmask irq hirq hok extra x0 hx0 excaps hex hxn hFR)
    (irq_handler_dk4 arI th hP hO hPD hK s ar σ G hDS hL lbl ct hct hcur htcb hact hmask irq hirq hok extra x0 hx0
      excaps hex hxn hD hP1)) ?_
  rintro ⟨r0, s', a'⟩ ⟨hq, hdk⟩
  cases r0 with
  | Err e =>
    obtain ⟨rfl, ⟨e', h1, h2⟩, rfl⟩ := hq
    exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, h2⟩, ⟨Z, hX0⟩⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', hx, -, -, -, hstp⟩ := hq
    obtain ⟨Z', hZ'⟩ := (hstp hdk.1).xtop arI hAM hDel hth hX0 hKA hC hTh
    exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
      mem_bindE_ok (mem_liftE hx) (Set.mem_singleton _), ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩, hZ'.rel.1, hZ'.rel.2.1,
        hZ'.rel.2.2.1, hZ'.rel.2.2.2.1, hZ'.rel.2.2.2.2.1⟩, ⟨Z', hZ'⟩⟩

end

end

end Fl4Proofs.P3
