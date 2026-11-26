/-
P3 (line irqfix, part C): **the direct users of `IrqPlatA.noIpi` and of the IRQ ack's unmask,
re-proved on `MachPlatT` / `IrqPlatK`**, and the IRQ ack's per-entry fact.

* `afterInv_of_mcsIMNQ`, `afterInv_of_mcsIMNMQ` (MRPath / KEntry38, verbatim copies): the preemption
  path's IRQ take, `noIpi` now `MachPlatT.noIpi` (JBootIpi's `IpiF`) at the `MR`-related state `hR1`
  the copies already hold.
* **The IRQ ack's unmask** (`jDecMRL_of`, the IRQ handler cap at `IRQAckIRQ`: FL4's
  `decode_irq_handler` does `mask_irq irq false`). FL4's cap only bounds `irq < 128` (`CapWf`), and
  no invariant carried by U32 bounds a handler cap's line by `maxIRQ`: l4v's `valid_cap` bound is
  SpecInvG5's `SpecIrqH`, whose preservation was never proved (XTopJointKEntry36E dropped it for
  `ValidIrqHandlers`, which has no bound). So the unmask is asked per entry:
  **`IrqAckU`** [J]: at the dispatch state, unmasking the line of a handler cap in a CNode slot keeps
  `MR`. It holds under U32's `MachPlat` (`IrqAckU.of_machPlat`) and, under `MachPlatF`, from l4v's
  `valid_cap` bound `irq ≤ maxIRQ` (`IrqAckU.of_bound`). It travels with the decode premise:
  `JDecMRLKQ` / `JDecMRL2Q` = `JDecMRLK` / `JDecMRL2` `∧ IrqAckU`.
* `jDecMRL_ofQ` (KEntry39 verbatim, on IrqFixGenB's copies), the ack by `IrqAckU`;
  `jDecMRL2_ofTQ`, `jDecMRLK_ofUQ`, `jVtxHypMU_ofQ`: the decode lemmas carrying `IrqAckU` along.
No sorry.
-/
import Fl4Proofs.P3.IrqFixGenB
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
open Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- **`afterInv_of_mcsI` under `MachPlat`** (module docstring), `NativeScope` at the
state after the MCS part from `hmcs` (g3b). -/
theorem afterInv_of_mcsIMNQ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hmcs : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ∧ NativeScope σ' ⦄)
    (hM : MachPlatT arI MR) (hIP : IrqPlatK arI AR) (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI)
    (hmbA : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧ PPQJI (L := L) arI AR σ (r.2.1, r.2.2) ⦄ := by
  unfold syscall.after_invocation
  refine WP.spec_bind hmcs ?_
  rintro ⟨s1, a1⟩ ⟨σ', hm, hmf, ⟨Z', H', Cs', Ac', Lst', D', J', _⟩, hR1, hVI, hN'⟩
  have hAR1 : AR a1 σ'.archState.x64CurrentCr3 := J'.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_bind (WP.spec_and (WP.spec_and (hM.takeAt hR1) (hIP.takeAR a1 _ hAR1)) (hM.noIpi a1 _ hR1)) ?_
  rintro ⟨w, a2⟩ ⟨⟨⟨irq, ms, hIq, hnone, hsome, hum, -⟩, hAR2⟩, h126, h127⟩
  obtain ⟨Lst2, J2⟩ := J'.msArJ ms a2 hum (fun _ => hAR2)
  unfold syscall.check_interrupt
  by_cases hw : w = syscall.NO_IRQ
  · have hirq : irq = none := hnone.1 hw
    subst hirq
    have e : (w != syscall.NO_IRQ) = false := by simp [hw]
    show (do
      let (s2, a3) ← (if (w != syscall.NO_IRQ) = true then interrupt.handle_interrupt st arI s1 a2 w else ok (s1, a2))
      ok (false, s2, a3)) ⦃ _ ⦄
    rw [e]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine (WP.spec_ok _).2 ⟨rfl, ⟨((), { σ' with machineState := ms }),
      hm _ (mem_maybeHandle_none hIq), ⟨Z', H', Cs', Ac', Lst2, D', J2, inferInstance⟩⟩⟩
  · obtain ⟨i, rfl⟩ : ∃ i, irq = some i := by
      cases irq with
      | none => exact absurd (hnone.2 rfl) hw
      | some i => exact ⟨i, rfl⟩
    obtain ⟨hwi, hmask⟩ := hsome i rfl
    have e : (w != syscall.NO_IRQ) = true := by simpa using hw
    show (do
      let (s2, a3) ← (if (w != syscall.NO_IRQ) = true then interrupt.handle_interrupt st arI s1 a2 w else ok (s1, a2))
      ok (false, s2, a3)) ⦃ _ ⦄
    rw [e]
    simp only [↓reduceIte]
    refine WP.spec_bind (Fl4ProofsQ.P3.JAtZ.handleIrqJIAN hARI hAT hIP hmbA J2 hN' w i hwi h126 h127) ?_
    rintro ⟨s2, a3⟩ (hf | ⟨z, hz, hJ⟩)
    · exact absurd hf (gai_active hVI hIq i rfl)
    · exact (WP.spec_ok _).2 ⟨rfl, ⟨z, hm _ (mem_maybeHandle_some hIq hz), hJ⟩⟩

set_option maxHeartbeats 16000000 in
/-- **`afterInv_of_mcsIMN` with `MR` at the chosen outcome** (`PPQJIM`): the
IRQ take moves `MR` (`MachPlat.takeAt`), the handler by `handleIrqJIANM`. -/
theorem afterInv_of_mcsIMNMQ (hKD : MRKeepD arI MR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hmcs : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ∧ NativeScope σ' ⦄)
    (hM : MachPlatT arI MR) (hIP : IrqPlatK arI AR) (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI)
    (hmbA : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧ PPQJIM (L := L) arI AR MR σ (r.2.1, r.2.2) ⦄ := by
  unfold syscall.after_invocation
  refine WP.spec_bind hmcs ?_
  rintro ⟨s1, a1⟩ ⟨σ', hm, hmf, ⟨Z', H', Cs', Ac', Lst', D', J', _⟩, hR1, hVI, hN'⟩
  have hAR1 : AR a1 σ'.archState.x64CurrentCr3 := J'.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_bind (WP.spec_and (WP.spec_and (hM.takeAt hR1) (hIP.takeAR a1 _ hAR1)) (hM.noIpi a1 _ hR1)) ?_
  rintro ⟨w, a2⟩ ⟨⟨⟨irq, ms, hIq, hnone, hsome, hum, hR2⟩, hAR2⟩, h126, h127⟩
  obtain ⟨Lst2, J2⟩ := J'.msArJ ms a2 hum (fun _ => hAR2)
  unfold syscall.check_interrupt
  by_cases hw : w = syscall.NO_IRQ
  · have hirq : irq = none := hnone.1 hw
    subst hirq
    have e : (w != syscall.NO_IRQ) = false := by simp [hw]
    show (do
      let (s2, a3) ← (if (w != syscall.NO_IRQ) = true then interrupt.handle_interrupt st arI s1 a2 w else ok (s1, a2))
      ok (false, s2, a3)) ⦃ _ ⦄
    rw [e]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine (WP.spec_ok _).2 ⟨rfl, ⟨((), { σ' with machineState := ms }),
      hm _ (mem_maybeHandle_none hIq), ⟨Z', H', Cs', Ac', Lst2, D', J2, inferInstance⟩, hR2⟩⟩
  · obtain ⟨i, rfl⟩ : ∃ i, irq = some i := by
      cases irq with
      | none => exact absurd (hnone.2 rfl) hw
      | some i => exact ⟨i, rfl⟩
    obtain ⟨hwi, hmask⟩ := hsome i rfl
    have e : (w != syscall.NO_IRQ) = true := by simpa using hw
    show (do
      let (s2, a3) ← (if (w != syscall.NO_IRQ) = true then interrupt.handle_interrupt st arI s1 a2 w else ok (s1, a2))
      ok (false, s2, a3)) ⦃ _ ⦄
    rw [e]
    simp only [↓reduceIte]
    refine WP.spec_bind (Fl4ProofsQ.P3.JAtZ.handleIrqJIANM hM hKD hARI hAT hIP hmbA J2 hN' hR2 w i hwi h126 h127) ?_
    rintro ⟨s2, a3⟩ (hf | ⟨z, hz, hJ, hRz⟩)
    · exact absurd hf (gai_active hVI hIq i rfl)
    · exact (WP.spec_ok _).2 ⟨rfl, ⟨z, hm _ (mem_maybeHandle_some hIq hz), hJ, hRz⟩⟩



end

section
open Fl4Proofs.P3.SInvR.G4
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[J] The IRQ ack's unmask at an entry state** (module docstring): unmasking the line of an IRQ
handler cap held in a CNode slot keeps `MR`. Under U32's `MachPlat` it holds (`IrqAckU.of_machPlat`);
under `MachPlatF` it is l4v `valid_cap`'s `irq ≤ maxIRQ` for the handler caps (`IrqAckU.of_bound`). -/
def IrqAckU (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (sl : Fl4Spec.CslotPtr) (irq : U64), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
    capAt (L.mem s) (cslotAddr sl) = ok (.IrqHandler irq) → irq.val < 128 → MR ar σ.machineState →
    arI.mask_irq ar irq false ⦃ a' =>
      MR a' { σ.machineState with irqMasks := Function.update σ.machineState.irqMasks (irq.bv.setWidth 8) false } ⦄

/-- `JDecMRLK` with the IRQ ack's `IrqAckU`. -/
def JDecMRLKQ (K : capability.Cap → U64 → List U64 → Prop) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  JDecMRLK (L := L) arI K AR MR Z H Cs D s ar σ ct ∧ IrqAckU (L := L) arI MR Z s ar σ

/-- `JDecMRL2` with the IRQ ack's `IrqAckU`. -/
def JDecMRL2Q (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  JDecMRL2 (L := L) arI AR MR Z H Cs D s ar σ ct ∧ IrqAckU (L := L) arI MR Z s ar σ

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

variable {arI} in
/-- **`IrqAckU` under U32's `MachPlat`** (any line `< 256` may be unmasked). -/
theorem IrqAckU.of_machPlat (hM : MachPlat arI MR) {s : S} {ar : A} {σ : Fl4Spec.State Unit} :
    IrqAckU (L := L) arI MR Z s ar σ :=
  fun _ irq _ _ h128 hR => hM.mask ar irq false _ hR (by omega)

variable {arI} in
/-- **`IrqAckU` under `MachPlatF` from l4v `valid_cap`'s bound** (every handler cap's line `≤ maxIRQ`). -/
theorem IrqAckU.of_bound (hM : MachPlatF arI MR) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (hB : ∀ (sl : Fl4Spec.CslotPtr) (irq : U64), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
      capAt (L.mem s) (cslotAddr sl) = ok (.IrqHandler irq) → irq.val ≤ 125) :
    IrqAckU (L := L) arI MR Z s ar σ :=
  fun sl irq hsl hc _ hR => hM.mask0 ar irq _ hR (hB sl irq hsl hc)

set_option maxHeartbeats 4000000 in
/-- **`JDecMRL` from `JDecMRL2`** at a dispatch state (module docstring): the
IO port cap by `XCapP.mr` (FL4 `MKD.decode_ioport` under `MRKeepIo`, spec
`dec_quiet`), the IRQ handler cap by `XCapP.mrG` (`MKD.decode_irq_handler_mr`,
`perfF_irqH`), the IRQ control cap by `decode_invocation_irq_controlXSM`,
the rest by `JDecMRL2`. -/
theorem jDecMRL_ofQ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : Fl4ProofsI.P3.JEntryAtN (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hNs : NativeScope σ) (hM : MachPlatT arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR)
    (hIoa : MRKeepIoapic arI MR) (hDL : JDecMRL2Q (L := L) arI AR MR Z H Cs D s ar σ ct) :
    JDecMRL (L := L) arI AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc hcl
    excaps buffer hXO hXN hLb hA5 hN
  obtain ⟨hlo, hNat⟩ := hcl
  have hA := hG.tot
  have hX0 := Fl4ProofsI.P3.decOK_JMU arI s ar σ J hG hE ct hct lbl length blk call don fp buf extra slbl argsU hlen hargs
    hbuf hl ci sl hsl c hc excaps buffer hXO hXN hLb hA5 hN hPD hR hVT hVI hNs
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨p', hp, hth⟩ := hsl; exact ⟨p', hp, Or.inl hth⟩
  cases c <;> simp only [LoudF] at hlo
  case IoPort first last z =>
    exact Fl4ProofsQ.P3.XCapP.mr hM hX0 (MKD.decode_ioport L.total hA hKD hIo hR)
      (fun inv hd => MachT.dec_quiet fp slbl _ ci sl _ excaps buffer (by simp [absCap, MachT.QuietS]) σ _ hd.1 inv rfl)
  case IrqHandler irq =>
    have hirq : irq.val < 128 := (slot_cap_wf J.xtop hAs (capV_of_capAt hc)).1
    subst hLb
    exact Fl4ProofsQ.P3.XCapP.mrG (f := fun ms => if lbl = fl4_abi.label.IRQAckIRQ then unmaskMs ms irq else ms) hM hX0 (MKD.decode_irq_handler_mr L.total hA hKD (hDL.2 sl irq hsl hc hirq hR) hR)
      (perfF_irqH irq hirq lbl σ blk call don fp _ ci sl excaps buffer)
  case IrqControl =>
    subst hLb
    have hPl : Placed Z.th := J.xtop.rel.1
    have hex := ExtraOK.rel1 hPl hXO
    obtain ⟨nA, hnum, hnA⟩ := hE.ioapics
    obtain ⟨sl1, idxs⟩ := sl
    obtain ⟨p0, hp0, hth0⟩ := hsl
    try simp only at hp0 hth0
    subst hp0
    obtain ⟨hcur, -⟩ := J.curEq hct
    exact (Fl4ProofsQI.P3.decode_invocation_irq_controlXSM arI Z.th s ar σ Z.G J.intL hE.handlers lbl lbl.bv (irqControl_label lbl)
      (irqControl_remap lbl) length buf ct hct argsU hlen hargs hcur J.kern.act J.act2 extra _ (exAt_idx0 extra) excaps
      hex hth0 rfl hc nA hnum hnA (maskIrq_total arI hA) hE.archIrq rfl rfl J.xtop (J.curRun.run hE.ni) _
      ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩
      (fun _ _ _ h => Steps.jat arI hG.ari.toMask (jStepHyps arI) h rfl J (J.zNoBlk hE.sg)) (fun _ _ _ h => JAt.xtop arI h)
      blk call don fp ci buffer hM.mask (fun a ms ms' h e => Fl4ProofsQ.P3.mF_mr hM h e) hR hIoa).toPN arI (specDec_noPreK (by trivial))
  all_goals
    exact hDL.1 hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc
      ⟨trivial, hNat⟩ excaps buffer hXO hXN hLb hA5 hN

set_option maxHeartbeats 4000000 in
/-- `jDecMRL2_ofT` (its transported copy) carrying `IrqAckU`. -/
theorem jDecMRL2_ofTQ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : Fl4ProofsI.P3.JEntryAtN (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hM : MachPlatT arI MR) (hKD : MRKeepD arI MR)
    (hR3 : JDecMRLKQ (L := L) arI LoudT AR MR Z H Cs D s ar σ ct) :
    JDecMRL2Q (L := L) arI AR MR Z H Cs D s ar σ ct :=
  ⟨Fl4ProofsQI.P3.jDecMRL2_ofT arI s ar σ J hG hE ct hct hM hKD hR3.1, hR3.2⟩

set_option maxHeartbeats 4000000 in
/-- `jDecMRLK_ofU` (its transported copy) carrying `IrqAckU`. -/
theorem jDecMRLK_ofUQ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : Fl4ProofsI.P3.JEntryAtN (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hM : MachPlatT arI MR) (hKD : MRKeepD arI MR)
    (hVx : JDecMRLKQ (L := L) arI VtxK AR MR Z H Cs D s ar σ ct)
    (hUR : JUtResetHyp (L := L) arI AR MR Z H Cs D s ar σ ct) :
    JDecMRLKQ (L := L) arI LoudT AR MR Z H Cs D s ar σ ct :=
  ⟨Fl4ProofsQI.P3.jDecMRLK_ofU arI s ar σ J hG hE ct hct hM hKD hVx.1 hUR, hVx.2⟩

end

/-- `jVtxHypMU_of` on `JDecMRLKQ`. -/
theorem jVtxHypMU_ofQ {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}
    {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}
    {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit} {ct : U64}
    (h : JDecMRLKQ (L := L) arI VtxK AR MR Z H Cs D s ar σ ct) :
    JVtxHypMU (L := L) arI AR MR Z H Cs D s ar σ ct :=
  jVtxHypMU_of h.1

end

end Fl4Proofs.P3
