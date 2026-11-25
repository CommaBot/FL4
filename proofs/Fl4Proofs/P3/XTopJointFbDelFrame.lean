/-
P3 (issue #16, FL4 #71), VSpace FrameBatch (KENTRY-PLAN fb3l): **the delete
of a slot holding a frame cap at `J`** (the batch's DELETE and COPY_MAP's
rollback).

* `mrKeepD_true`: MachKeepD's `MRKeepD` at the trivial relation, from
  `P0.ArchTotal`, so MachKeepG4d's `MKD.cdt_delete_frame` says FL4's
  `cdt.delete … true` of a frame-cap slot returns `Ok` (never preempted).
* `JAtZ.fbDelFrameJL`: from `JAtZ` with the deletion loop's liveness facts
  (`LiveDN`, `NoSwitch`, `SpecGlob`, `PPR0`: XTopJointWJL's `WJL`), FL4's
  delete of a frame-cap slot has an `ok` outcome of the spec's `cap_delete`,
  with `JAtZ` and the same facts after (XTopJointWJLDel's
  `JDelParts.jDelHypL`, its preempted disjunct refuted by `mrKeepD_true`).
-/
import Fl4Proofs.P3.XTopJointWJLDel
import Fl4Proofs.P3.MachKeepG4d
import Fl4Proofs.P3.XTopJointFbDefs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- `MRKeepD` at the trivial relation (every arch operation total). -/
theorem mrKeepD_true {A : Type} {arI : machine.Arch A} (hT : P0.ArchTotal arI) :
    MRKeepD arI (fun (_ : A) (_ : Unit) => True) where
  set_deadline a d _ _ := hT.set_deadline a d
  send_reschedule a m _ _ := hT.send_reschedule a m
  remote_stall a c _ _ := hT.remote_stall a c
  fpu_flush a t _ _ := hT.fpu_flush a t
  fpu_release a t _ _ := hT.fpu_release a t
  fpu_sanitise a t _ _ := hT.fpu_sanitise a t
  fpu_reload a t _ _ := hT.fpu_reload a t
  vcpu_barrier a _ _ := hT.vcpu_barrier a
  vcpu_release a v _ _ := hT.vcpu_release a v
  invalidate_ept a x y _ _ := hT.invalidate_ept a x y
  invalidate_page a x y _ _ := hT.invalidate_page a x y
  invalidate_asid a x _ _ := hT.invalidate_asid a x
  invalidate_page_structures a x _ _ := hT.invalidate_page_structures a x
  set_vspace a x y _ _ := hT.set_vspace a x y
  dma_frame a x y b _ _ := hT.dma_frame a x y b
  irq_free a x _ _ := hT.irq_free a x
  tdx_report a p d0 d1 d2 d3 d4 d5 d6 d7 _ _ := hT.tdx_report a p d0 d1 d2 d3 d4 d5 d6 d7
  tdx_extend_rtmr a i d0 d1 d2 d3 d4 d5 _ _ := hT.tdx_extend_rtmr a i d0 d1 d2 d3 d4 d5
  tdx_get_quote a p n _ _ := hT.tdx_get_quote a p n

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- FL4's delete of a frame-cap slot returns `Ok`. -/
theorem cdt_delete_frame_ok (hT : P0.ArchTotal arI) {s : S} {a : A} {x : obj.Slot} {c : capability.Cap}
    {f : vspace.FrameCap} (hc : obj.Slot.cap st x s = ok c) (hf : vspace.as_frame c = ok (some f)) :
    cdt.delete st arI s a x true ⦃ r => r.1 = .Ok () ⦄ :=
  WP.spec_mono (MKD.cdt_delete_frame (AR := fun (_ : A) (_ : Unit) => True) (c₀ := ()) L.total hT
    (mrKeepD_true hT) hc hf trivial) fun _ h => h.2

/-- **`FbFootK` from the relations at both states**: every TCB's registers and every mapped
IPC-buffer word are read off the spec's state by `JAtZ` (`EpStateRel`'s `regs` and `buf`), so a
step keeping the TCBs' arch contexts (`FbKeep`'s `CapsOnly`) and the underlying memory keeps them. -/
theorem FbFootK.of_rel {Z1 Z2 : XSets} {H1 H2 : P1.Heap} {Cs1 Cs2 Ac1 Ac2 : Set U64}
    {Lst1 Lst2 : U64 → List U64} {D1 D2 : Set U64} {s s' : S} {a a' : A} {τ τ' : Fl4Spec.State Unit}
    (J1 : JAtZ (L := L) arI AR Z1 H1 Cs1 Ac1 Lst1 D1 s a τ) (J2 : JAtZ (L := L) arI AR Z2 H2 Cs2 Ac2 Lst2 D2 s' a' τ')
    (hT : Z2.T = Z1.T) (hB : Z2.B = Z1.B) (hK : FbKeep τ τ')
    (hum : τ'.machineState.underlyingMemory = τ.machineState.underlyingMemory) : FbFootK (L := L) Z1 s s' := by
  have hR1 := (J1.xtop.irelK J1.ks J1.buf).1.toE
  have hR2 := (J2.xtop.irelK J2.ks J2.buf).1.toE
  constructor
  · intro t ht g
    obtain ⟨x, hk, -⟩ := J1.buf t ht
    obtain ⟨y, hk', hxy⟩ := hK.tcb hk
    have r1 := (hR1.at_tcb ht hk).regs g
    have r2 := (hR2.at_tcb (hT ▸ ht) hk').regs g
    apply P1.eq_of_bv
    rw [r1, r2, hxy.2.2.2.2.2.2.2.2.2.2]
  · intro wp hw
    have b1 := hR1.buf wp hw
    have b2 := hR2.buf wp (hB ▸ hw)
    apply P1.eq_of_bv
    rw [b1, b2, hum]

set_option maxHeartbeats 8000000 in
/-- **The delete of a frame-cap slot at `J`** (module docstring). -/
theorem JAtZ.fbDelFrameJL [Fl4Proofs.P1.PlainStore st] {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hDP : JDelParts (L := L) arI AR Z.th) (hT : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hPP : PPPlat arI AR) (hAM : ARMask arI AR)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) (hns : Vs.NoSwitch σ) (hsg : SpecGlob σ) (hp0 : PPR0 σ)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {c : capability.Cap}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c) {f : vspace.FrameCap} (hf : vspace.as_frame c = ok (some f)) :
    cdt.delete st arI s a (cslotAddr sl) true ⦃ r => r.1 = .Ok () ∧ ∃ (σ' : Fl4Spec.State Unit) (G' : MdbGhost)
      (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      (.ok (), σ') ∈ ((Fl4Spec.capDelete (Z := Unit) sl).run σ).1 ∧
      JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' r.2.1 r.2.2 σ' ∧
      LiveDN (L := L) Z.th H Cs G' r.2.1 σ' ∧ Vs.NoSwitch σ' ∧ SpecGlob σ' ∧ PPR0 σ' ∧ L.ksb r.2.1 = L.ksb s ⦄ := by
  obtain ⟨K, hK, hK6, hDE⟩ := J.delE
  have hCR := J.xtop.rel.2.1
  have hcn : c ≠ .Null := by
    intro e; subst e; simp [vspace.as_frame] at hf
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten := (hCR.2.2.1.members _).2 ⟨hA.isSlot, c, hc, hcn⟩
  have hE : DelE (L := L) Z.th K s σ ∧ WJL (L := L) arI AR Z H Cs (L.ksb s) s a σ Z.G :=
    ⟨hDE, ⟨⟨(Z.P, Z.L4, Z.L3, Z.L2, Z.L1), Ac, Lst, D, J, rfl, hns, hsg, hp0⟩, hLv⟩⟩
  refine WP.spec_mono (WP.spec_and (hDP.jDelHypL arI hT hnd hPP hAM Z H Cs (L.ksb s) K rfl hK hK6 s a σ Z.G sl
    hCR hE hA hxm) (cdt_delete_frame_ok arI hT (by rw [slot_cap_eq]; exact hc) hf)) ?_
  rintro ⟨r, s', a'⟩ ⟨⟨σ', G', hcase, -, hW', -⟩, hok⟩
  simp only at hok hcase hW' ⊢
  subst hok
  rcases hcase with ⟨-, hm, -⟩ | ⟨he, -⟩
  · unfold WPost at hW'
    obtain ⟨-, ⟨V', Ac', Lst', D', J', hkb, hns', hsg', hp0'⟩, hLv'⟩ := hW'
    exact ⟨rfl, σ', G', V', Ac', Lst', D', hm, J', hLv', hns', hsg', hp0', hkb⟩
  · cases he

end

end

end Fl4Proofs.P3
