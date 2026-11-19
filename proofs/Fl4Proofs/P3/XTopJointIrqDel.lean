/-
P3 (DESIGN.md §9), interrupts: **the IRQ handler decode's deletion at `J`**
(`ClearIRQHandler`, `SetIRQHandler`: FL4's `delete_one` of the IRQ's node
slot after the caller's restart), so that the decode needs no ∀-state
deletion premise (DelOne's `FinObjHyp`, `PostDelHyp`, `NtfnKeepHyp`, which
DState alone does not make true: it relates no notification queue).

* `WJ.restart`: the caller's restart keeps XTopJointDelR's `WJ` (as
  XTopJointCnDel's `EJ.restart`, without `DelE` and `PPR0`): `JStepHyps.restart`,
  `SpecGlob.sts`, no switch pending from `Entered`.
* `irqDelOKJ`: IrqHandler's `IrqDelOK` at `J`: the node slot null or a
  notification cap at the restarted state (`jIrqSlotHyp` from `WJ`'s
  `SpecGlob`), a null slot's deletion doing nothing, a notification cap's
  by `delete_oneJ` (`LiveJ` [J], `JDelParts.live`).
* `irqDelDKJ`: IrqDom's `IrqDelDK` at `J` (`jFinNtfnK`: `DState` after the
  notification's finalisation).
-/
import Fl4Proofs.P3.XTopJointCnDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The caller's restart keeps `WJ`** (as `EJ.restart`). -/
theorem WJ.restart (hJ : JStepHyps (L := L) arI AR Z.th) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      WJ (L := L) arI AR Z H Cs (L.ksb s) s1 ar σ1 Z.G := by
  intro s1 σ1 hs1 hst
  have hsg1 : SpecGlob σ1 := SpecGlob.sts (mem_of_single hst) hsg
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have e : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  subst e
  have h := XTopAt.restart J.xtop hcur hk hrun
  rw [hs1, WP.spec_ok] at h
  obtain ⟨hX1, hSS, hk1⟩ := h
  obtain ⟨hkb, hkz⟩ := kback_ksz_upd (σ' := Notif.stsAct (Notif.updK σ ct.bv
    (.tcb { x with tcbState := .restart })) ct.bv) hk (by rw [stsAct_kheap]; rfl)
  obtain ⟨Ac', Lst', D', R⟩ := hJ.restart s ar σ ct x s1 hcur hk htcb hrun hs1 Z H Cs Ac Lst D rfl J hX1
  have hns1 : Vs.NoSwitch (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) := by
    intro u e
    unfold Notif.stsAct at e
    split_ifs at e
    all_goals first
      | (have e2 : σ.schedulerAction = .switchThread u := e
         rw [hni.2] at e2; cases e2)
      | cases e
  exact ⟨Z.vs, Ac', Lst', D', J.cs_frame hk1 hX1 hkb (JCs.same J hSS hkz) R (J.vsc.of_eq fun y hy => hSS.capV hy), hk1, hns1, hsg1⟩

set_option maxHeartbeats 4000000 in
/-- **`IrqDelOK` at `J`** (module docstring). -/
theorem irqDelOKJ [Fl4Proofs.P1.PlainStore st] (hLv : LiveJHyp (L := L) arI AR Z.th)
    (hJ : JStepHyps (L := L) arI AR Z.th) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (irq : U64) (hirq : irq.val < 128) :
    IrqDelOK (L := L) arI Z.th s ar σ Z.G ct irq := by
  intro s2 σ1 hs2 hst hDS1
  have hW := WJ.restart arI hJ J hni hsg hct s2 σ1 hs2 hst
  have hkb2 : L.ksb s2 = L.ksb s := by obtain ⟨_, _, _, _, _, hk, _⟩ := hW; exact hk
  have hok := jIrqSlotHyp (L := L) arI (AR := AR) (th := Z.th) Z H Cs (L.ksb s) rfl s2 ar σ1 Z.G hW irq hirq
  rw [hkb2] at hok
  have hA : AbsSlot Z.th ((nodeA (L.ksb s) irq).bv, []) := ⟨_, rfl, Or.inl (by simpa using J.intL.node irq hirq)⟩
  have hcs : cslotAddr ((nodeA (L.ksb s) irq).bv, []) = nodeA (L.ksb s) irq := cslotAddr_nil _
  rcases hok with hnull | ⟨p, b, w, r, hn⟩
  · obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := hDS1.1.1.abs_cap hA
    rw [hca0.abs] at hg0
    have hcv0 := capV_of_capAt hc0
    rw [hcs] at hcv0
    rw [hcv0] at hnull; subst hnull
    have e1 : cdt.delete_one st arI s2 ar (nodeA (L.ksb s) irq) = ok (s2, ar) := by
      unfold cdt.delete_one
      rw [slot_cap_eq, ← hcs, hc0]
      simp only [bind_ok, cap_is_null_eq, isNullB, ↓reduceIte]
    have e2 : Fl4Spec.capDeleteOne (Z := Unit) ((nodeA (L.ksb s) irq).bv, []) σ1 = ({((), σ1)}, False) := by
      unfold Fl4Spec.capDeleteOne
      rw [nd_bind_one hg0]
      simp [absCap, Fl4Spec.NonDet.unless, Fl4Spec.NonDet.pure]
    rw [e1, WP.spec_ok]
    refine ⟨⟨σ1, Z.G, by rw [e2]; exact Set.mem_singleton _, hDS1, MdbStep.refl hDS1.1.2.2.1⟩, ?_,
      fun _ _ _ => rfl⟩
    rw [← hcs]; exact capV_of_capAt hc0
  · have hd := delete_oneJ arI hLv Z H Cs (L.ksb s) rfl s2 ar σ1 Z.G hDS1 hW hA (by rw [hcs]; exact hn)
    rw [hcs] at hd
    refine WP.spec_mono hd ?_
    rintro r ⟨σ', G', h1, h2, h3, h4, h5, -⟩
    exact ⟨⟨σ', G', h1, h2, h5⟩, h3, h4⟩

/-- **`IrqDelDK` at `J`** (module docstring). -/
theorem irqDelDKJ [Fl4Proofs.P1.PlainStore st] (hJ : JStepHyps (L := L) arI AR Z.th) {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hsg : SpecGlob σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) (irq : U64) (hirq : irq.val < 128) :
    IrqDelDK (L := L) arI Z.th s ar σ Z.G ct irq := by
  intro s2 σ1 hs2 hst hDS1 p b w r e
  have hW := WJ.restart arI hJ J hni hsg hct s2 σ1 hs2 hst
  have hA : AbsSlot Z.th ((nodeA (L.ksb s) irq).bv, []) := ⟨_, rfl, Or.inl (by simpa using J.intL.node irq hirq)⟩
  refine WP.spec_mono (jFinNtfnK arI Z H Cs (L.ksb s) rfl s2 ar σ1 Z.G _ p b w r hDS1 hW hA
    (by rw [capAt_capV, cslotAddr_nil, e])) ?_
  rintro res ⟨-, -, σ', G', -, hD', -⟩
  exact ⟨σ', G', hD'⟩

end

end

end Fl4Proofs.P3
