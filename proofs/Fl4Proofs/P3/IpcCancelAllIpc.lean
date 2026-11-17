/-
P3 (DESIGN.md §9), IPC: **an endpoint's finalisation on `IRel`**
(`cancel_all_ipc`, toward `XFinHyps.ep`), the slots and the kernel-global
base kept (`IFrame`).

* `restart_irelF`: `restart_irel` with `IFrame`.
-/
import Fl4Proofs.P3.IpcCancelSignals
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section Restart
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 2000000 in
/-- `restart_irel` with the slots and the kernel-global base kept (`IFrame`). -/
theorem restart_irelF (hP0 : IPlaced N T E R B)
    (hAct : ∀ s σ, IRel st th cr N T C E R B c s σ → ActReady σ)
    (s : S) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hns : tsCode x.tcbState ≠ 6)
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' => ∃ σ', ((), σ') ∈ (Fl4Spec.restartThreadIfNoFault (Z := Unit) t.bv σ).1 ∧
      IRel st th cr N T C E R B c s' σ' ∧
      (∀ p y, σ.kheap p = some (.endpoint y) → σ'.kheap p = some (.endpoint y)) ∧ IFrame (L := L) th s s' ⦄ := by
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP
  have hTR := hX.1.toE.at_tcb ht hk
  have hkp : ∀ p y, σ.kheap p = some (.endpoint y) → p ≠ t.bv := fun p y hy e => by
    rw [e, hk] at hy; cases hy
  unfold endpoint.restart_thread_if_no_fault
  step with obj.Tcb.fault_type.spec as ⟨i, hi⟩
  by_cases h0 : i = fl4_abi.consts.fault.NullFault
  · rw [if_pos h0]
    have hf : x.tcbFault = none := hTR.fault0.1 (by rw [← hi, h0]; unfold fl4_abi.consts.fault.NullFault; rfl)
    have hcode : sched.TS_RESTART.val = tsCode .restart := by unfold sched.TS_RESTART; rfl
    refine WP.spec_bind (WP.spec_and (set_thread_state_c hH hP0 hP s σ hX.1.toE (IpcRel.toSRN hX.1 hX.2) ht hk hq hns
      .restart (by decide) sched.TS_RESTART hcode) (set_thread_state_sfoot hX.2.2.1 ht sched.TS_RESTART)) ?_
    rintro s1 ⟨⟨hE1, hS1⟩, hw1⟩
    have hF1 : IFrame (L := L) th s s1 :=
      IRel.iframe_of hX hw1 fun b hb => tfoot_oobj hX.2.2.1 (Or.inl (KFoot.of_sfoot hb))
    have hX1 := IpcRel.ofSRN hE1 hS1
    rw [endpoint_unblock_sporadic_eq]
    refine WP.spec_bind (WP.spec_and (unblock_irel hP0 s1 _ hX1 t ht) (unblock_sporadic_tfoot hX1.2.2.1 t ht)) ?_
    rintro s2 ⟨⟨σ2, hu, hf2, hv2, hX2⟩, hw2⟩
    have hF2 : IFrame (L := L) th s1 s2 := IRel.iframe_of hX1 hw2 fun b hb => tfoot_oobj hX1.2.2.1 hb
    refine WP.spec_mono (WP.spec_and (switch_top hP0 s2 σ2 hX2.1 hX2.2 (hAct _ _ hX2) t ht)
      (possible_switch_to_sfootI hX2.1.toN hX2.2.2.1 (hAct _ _ hX2) ht)) ?_
    rintro s3 ⟨⟨σ3, hps, hk3, hf3, hv3, hS3⟩, hw3⟩
    have hF3 : IFrame (L := L) th s2 s3 := IRel.iframe_of hX2 hw3 fun b hb => sfootI_oobj hP.tcb hb
    refine ⟨σ3, ?_, ⟨hX2.1.frame hP0 hf3 hv3, hS3⟩, fun p y hy => ?_, (hF1.trans hF2).trans hF3⟩
    · unfold Fl4Spec.restartThreadIfNoFault
      rw [nd_bind_one (threadGet_eq _ hk), hf]
      simp only [↓reduceIte]
      rw [nd_bind_one (Notif.setThreadState_eq .restart hk), restart_spec_eq, specSporadicAssert_eq,
        nd_bind_one hu, hps]
      rfl
    · have h1 : (stsAct (updK σ t.bv (.tcb { x with tcbState := .restart })) t.bv).kheap p = some (.endpoint y) := by
        rw [stsAct_kheap]; simp [updK, hkp p y hy, hy]
      rw [hk3]; exact hv2.2.1.1 _ _ h1
  · rw [if_neg h0]
    have hf : x.tcbFault ≠ none := fun e => h0 (by rw [hi, hTR.fault0.2 e]; unfold fl4_abi.consts.fault.NullFault; rfl)
    have hcode : sched.TS_INACTIVE.val = tsCode .inactive := by unfold sched.TS_INACTIVE; rfl
    refine WP.spec_mono (WP.spec_and (set_thread_state_c hH hP0 hP s σ hX.1.toE (IpcRel.toSRN hX.1 hX.2) ht hk hq hns
      .inactive (by decide) sched.TS_INACTIVE hcode) (set_thread_state_sfoot hX.2.2.1 ht sched.TS_INACTIVE)) ?_
    rintro s1 ⟨⟨hE1, hS1⟩, hw1⟩
    refine ⟨_, ?_, IpcRel.ofSRN hE1 hS1, fun p y hy => ?_,
      IRel.iframe_of hX hw1 fun b hb => tfoot_oobj hX.2.2.1 (Or.inl (KFoot.of_sfoot hb))⟩
    · unfold Fl4Spec.restartThreadIfNoFault
      rw [nd_bind_one (threadGet_eq _ hk)]
      simp only [hf, ↓reduceIte]
      rw [Notif.setThreadState_eq .inactive hk]
      rfl
    · rw [stsAct_kheap]; simp [updK, hkp p y hy, hy]

end Restart

end

end Fl4Proofs.P3.Ipc
