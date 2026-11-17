/-
P3 (DESIGN.md §9), IPC: **a notification's finalisation on `IRel`, the
slots kept** (toward `XFinHyps.ntfn`).

* `unbind_maybe_irel`: `unbind_maybe_notification` (the bound TCB's and the
  notification's bound words cleared, `bound_wr_irel`).
-/
import Fl4Proofs.P3.IpcSlotsSame
import Fl4Proofs.P3.IpcCancelSignals
import Fl4Proofs.P3.IpcTcbBind
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 4000000 in
/-- **`unbind_maybe_notification` on `IRel`**, the slots kept. -/
theorem unbind_maybe_irel (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {n : U64} (hn : n ∈ N) :
    notification.unbind_maybe_notification st s n ⦃ s' => ∃ σ',
      Fl4Spec.unbindMaybeNotification (Z := Unit) n.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c s' σ' ∧ SlotsSame th (L.mem s) (L.mem s') ⦄ := by
  obtain ⟨xn, hkn, -⟩ := hX.1.toN.ntfn n hn
  have hx := hX.1.toN.at_ntfn hn hkn
  have hg : Fl4Spec.getNtfnObjRef (Z := Unit) Fl4Spec.Notification.ntfnBoundTcb n.bv σ =
      ({(xn.ntfnBoundTcb, σ)}, False) := by
    unfold Fl4Spec.getNtfnObjRef Fl4Spec.getSkObjRef
    rw [nd_bind_one (m := Fl4Spec.getSimpleKo Fl4Spec.KernelObject.notification n.bv) (getNotification_eq hkn)]
    rfl
  unfold notification.unbind_maybe_notification
  rw [Sched.ntfn_bound_eq]
  simp only [bind_ok]
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  by_cases h0 : L.mem s (nBoundA n) = 0#u64
  · have hb' : b = true := by rw [hb, h0]; rfl
    simp only [hb', ↓reduceIte, WP.spec_ok]
    refine ⟨σ, ?_, hX, SlotsSame.refl _ _⟩
    unfold Fl4Spec.unbindMaybeNotification
    rw [nd_bind_one hg, hx.bound, h0, Notif.optRef_zero]; rfl
  have hb' : b = false := by rw [hb]; simp [h0]
  simp only [hb', Bool.false_eq_true, ↓reduceIte]
  have hiT := hx.bound_mem h0
  obtain ⟨x, hk, -⟩ := hX.1.tcb _ hiT
  have hin : (L.mem s (nBoundA n)).bv ≠ n.bv := fun e => by rw [e, hkn] at hk; cases hk
  obtain ⟨s1, h1, rfl⟩ := spec_exists (P1.obj.Ntfn.set_bound_tcb.wr (L := L) s n 0#u64)
  rw [h1]; simp only [bind_ok]
  obtain ⟨s2, h2, rfl⟩ := spec_exists (P1.obj.Tcb.set_bound_ntfn.wr (L := L) (L.wr s (P1.ntfnBtA n) 0#u64)
    (L.mem s (nBoundA n)) 0#u64)
  rw [h2, WP.spec_ok]
  have hX2 := bound_wr_irel hP0 hX hiT hn hk hkn 0#u64 0#u64 (fun h => absurd rfl h)
  rw [Notif.optRef_zero] at hX2
  have hba : Aligned (nBoundA n) := by
    rw [nBoundA_eq]; exact (nword hP0.n hn (K := 24#u64) (by simp) (by simp)).1
  have hbv : (nBoundA n).val = n.val + 24 := by rw [nBoundA_eq]; exact nfield_val (hP0.n.ntfn n hn) (by simp)
  have hpa := hP0.e.tcb _ hiT
  have hta := (a_bound hpa).1
  have hbvp := val_bound hpa
  refine ⟨_, ?_, hX2, IRel.slotsSame_of hX ((writesIn_wr (s := s) (v := 0#u64) hba).trans
    (writesIn_wr (s := L.wr s (nBoundA n) 0#u64) (v := 0#u64) hta)) fun b hb => ?_⟩
  · unfold Fl4Spec.unbindMaybeNotification
    rw [nd_bind_one hg, hx.bound, Notif.optRef_ne h0]
    show (Fl4Spec.setNtfnObjRef Fl4Spec.ntfnBoundTcbUpdate n.bv none >>= fun _ =>
      Fl4Spec.setTcbObjRef Fl4Spec.tcbBoundNotificationUpdate (L.mem s (nBoundA n)).bv none) σ = _
    rw [nd_bind_one (setNtfnObjRef_eq hkn _ _)]
    exact Notif.threadSet_eq _ (by simp only [Notif.updK, Function.update_of_ne hin]; exact hk)
  · rcases hb with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, by rw [hbv]; omega, by rw [hbv]; omega⟩)))))
    · have e : (P1.boundA (L.mem s (nBoundA n))).val = (L.mem s (nBoundA n)).val + 3368 := hbvp
      exact Or.inr (Or.inr (Or.inl ⟨_, hiT, by rw [e]; omega, by rw [e]; omega⟩))

end

end

end Fl4Proofs.P3.Ipc
