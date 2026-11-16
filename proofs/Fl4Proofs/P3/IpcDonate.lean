/-
P3 (DESIGN.md §9), IPC: **the notification wake-up's donation on `IRel`**
(`IpcWakeHyps.donate`).

* `tk_lift`: a step where FL4 writes only `TFoot` words and the spec changes
  only scheduling fields (`ScTKw`), with the scheduler and notification
  relations after, keeps `IRel`: through `XTopAt` (`IRel.xtop`, the Sc
  proofs' `xtop_sc_step`, `XTopAt.irelK`), at the arch relation "the CR3 is
  `cr`".
* `donate_irel` (`IpcWakeHyps.donate`): `maybe_donate_refinesW` (IpcDonateW:
  ScDonateRef's proof with FL4's writes) lifted by `tk_lift`, the spec step
  `ScTKw` by `nkt_maybeDonateSc`; named: `DonOK` (ScDonateRef's
  `DonatePre`, and `ActReady`).
* `ipcWakeHyps_top`: `IpcWakeHyps`, the unblock by IpcEpTail's
  `unblock_irel`.
-/
import Fl4Proofs.P3.ScXStep
import Fl4Proofs.P3.IpcXTop
import Fl4Proofs.P3.IpcDonateW
import Fl4Proofs.P3.IpcEpTail
open Aeneas Aeneas.Std Result



/-! ## The spec's donation changes only scheduling fields -/

namespace Fl4Proofs.P3.Sched
open Fl4Spec

noncomputable section

theorem ScTKw.ofFalse {P : ObjRef → Prop} {σ σ' : State Unit} (h : ScTKw (fun _ => False) σ σ') : ScTKw P σ σ' :=
  ⟨fun p => (h.kh p).mono False.elim, h.um, h.cdt, h.orig, h.dl, h.dsi, h.arch, h.ist, h.inode, h.ct⟩

theorem nkt_schedContextDonate (sc t : ObjRef) : NKT (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate testReschedule
  repeat' (first | exact nkt_rescheduleRequired | exact nkt_tcbReleaseRemove _ | nkt_step | (unfold NonDet.when; split))

theorem nkt_maybeDonateSc (t n : ObjRef) : NKT (maybeDonateSc (Z := Unit) t n) := by
  unfold maybeDonateSc getTcbObjRef getNtfnObjRef getSkObjRef getSimpleKo
  repeat' (first | exact nkt_schedContextDonate _ _ | exact nkt_schedContextResume _ | nkt_step | (unfold NonDet.when; split))

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section Lift
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **A scheduling step keeps `IRel`** (module docstring). -/
theorem tk_lift (hP0 : IPlaced N T E R B) {s s' : S} {σ σ' : Fl4Spec.State Unit} {ct : Fl4Spec.ObjRef}
    (hX : IRel st th cr N T C E R B c s σ)
    (hW : WritesIn st s s' (TFoot st T N C c s σ)) (hK : ScTKw (fun p => p = ct) σ σ')
    (hS' : SchedRel st N T C c s' σ') (hN' : NtfnStateRel N T (L.mem s') σ') :
    IRel st th cr N T C E R B c s' σ' := by
  obtain ⟨⟨Z, hth, hN, hT, hC, hE, hR, hB, hc, hZ⟩, hKA⟩ :=
    IRel.xtop (A := Unit) (AR := fun _ c' => c' = cr) (a := ()) hX rfl
  subst hth hN hT hC hE hR hB hc
  have hX' := xtop_sc_step (a' := ()) hZ hP0 (fun n hn => by have := hKA.ntfn n hn; omega) hW hK hS' hN' id
  have hks : L.ksb s' = L.ksb s := hW.1
  have hcr : σ'.archState.x64CurrentCr3 = cr := hX'.fin.1.1.2.2.2.2.2.2
  have := XTopAt.irelK hX' (by rw [hks]; exact hKA)
  rw [hcr] at this
  exact this

end Lift



section Donate
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- The facts the donation needs beyond `IRel` (ScDonateRef's `DonatePre`, l4v
invariants): the release queue's (`RelOK`), the notification's SC one of
`C`, a thread with no SC in no ready queue, and the switch target ready. -/
def DonOK (st : machine.Store S) [L : LawfulStore st] (C : Set U64) (s : S) (σ : Fl4Spec.State Unit)
    (t n : U64) : Prop :=
  RelOK σ ∧ (L.mem s (nScA n) ≠ 0#u64 → L.mem s (nScA n) ∈ C) ∧
    (L.mem s (scA t) = 0#u64 → ∀ x, σ.kheap t.bv = some (.tcb x) → t.bv ∉ σ.readyQueues x.tcbDomain x.tcbPriority) ∧
    ActReady σ

set_option maxHeartbeats 1000000 in
/-- **`maybe_donate_sched_context` on `IRel`** (`IpcWakeHyps.donate`):
`maybe_donate_refinesW` lifted by `tk_lift`. -/
theorem donate_irel (hP0 : IPlaced N T E R B)
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (t n : U64) (hR : IpcRel N T E R B (L.mem s) σ)
    (hS : SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ) (ht : t ∈ T) (hn : n ∈ N)
    (hD : DonOK st C s σ t n) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ r => ∃ σ1,
      Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ = ({((), σ1)}, False) ∧
      IpcRel N T E R B (L.mem r.1) σ1 ∧
      SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 σ1 ∧ ActReady σ1 ⦄ := by
  have hX : IRel st th cr N T C E R B c s σ := ⟨hR, hS⟩
  have hSch := hX.2.2.1
  obtain ⟨hRel, hnC, hnq, hAct⟩ := hD
  refine WP.spec_mono (maybe_donate_refinesW s a σ hR.toN hSch hRel (hmb a) t n ht hn hnC hnq) ?_
  rintro r ⟨σ1, he, hf, hv, hS1, hw, hA⟩
  have hK : ScTKw (fun p => p = σ.curThread) σ σ1 := ScTKw.ofFalse (NKT.of_eq (nkt_maybeDonateSc t.bv n.bv) he)
  have hN1 : NtfnStateRel N T (L.mem r.1) σ1 := hR.toN.frame hSch.placed hf hv
  have hI := tk_lift hP0 hX (hw.mono fun _ h => Or.inl h) hK hS1 hN1
  exact ⟨σ1, he, hI.1, hI.2, hA hAct⟩

/-- **`IpcWakeHyps` for `SRT … SRE`**: the donation by `donate_irel`, the
sporadic unblock by `unblock_irel`; named: `DonOK` and the platform's
`MIN_BUDGET`. -/
theorem ipcWakeHyps_top (hP0 : IPlaced N T E R B)
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hD : ∀ s σ (t n : U64), IpcRel N T E R B (L.mem s) σ → SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ →
      t ∈ T → n ∈ N → DonOK st C s σ t n) :
    IpcWakeHyps st ar th cr N T C E R B c :=
  ⟨fun s a σ t n _ hR hS ht hn _ _ => donate_irel hP0 hmb s a σ t n hR hS ht hn (hD s σ t n hR hS ht hn),
   fun s σ t hR hS ht => WP.spec_mono (unblock_irel hP0 s σ ⟨hR, hS⟩ t ht) fun _ ⟨σ', hu, hf, hv, hI⟩ =>
     ⟨by rw [hu]; exact id, σ', by rw [hu]; rfl, hf, hv, hI.2⟩⟩

end Donate

end

end Fl4Proofs.P3.Ipc
