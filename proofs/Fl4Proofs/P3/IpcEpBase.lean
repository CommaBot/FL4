/-
P3 (DESIGN.md §9), IPC: **the endpoint proofs on the merged relation**, the
base. The endpoint theorems are proved once over the step bundle `EpSteps`
for an abstract `SR` (EpStepsBase.lean); here they are instantiated with

  `SRN N T (SRS T SR)` = `SR` ∧ the TCBs' SC words (`ScRelM`) ∧ the
  notification relation,

so that `EpStateRel ∧ SRN N T (SRS T SR)` is `IpcRel ∧ SR`
(`IpcRel.ofSRN`, `IpcRel.toSRN`).

* `IpcSchedHyps.epHyps`: the endpoint proofs' `EpHyps` for `SRS T SR`, from
  `stableE` (the SC words are outside `EWrite` and `EpStep` keeps
  `tcbSchedContext`) and `scheduleTcb`;
* `IpcSchedHyps.schedC`: `schedule_tcb` keeping both footprints;
* `IpcEpTailHyps`: the scheduler tails of the transfers on the merged
  relation (keeping `IFoot` and `IKView`), giving `EpTailHyps` and
  `EpScHyps` for `SRN N T (SRS T SR)`.
-/
import Fl4Proofs.P3.IpcNtfnSched
import Fl4Proofs.P3.EpCombIpc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Ipc

noncomputable section

section
variable {N T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

theorem _root_.Fl4Proofs.P3.Ipc.IPlaced.toC (h : IPlaced N T E R B) : CPlaced N T E R B := ⟨h.n, h.e, h.ne, h.nr, h.nb⟩

variable {Z : Type} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Z}

/-- The SC words survive a frame of the merged footprint and view. -/
theorem _root_.Fl4Proofs.P3.Ipc.ScRelM.frame (hP : IPlaced N T E R B) (h : ScRelM T m σ) (hm : Agree m m' (IFoot N T E R B))
    (hk : IKView σ σ') : ScRelM T m' σ' := by
  intro t ht
  obtain ⟨x, hx, e⟩ := h t ht
  obtain ⟨y, hy, ey⟩ := hk.2.2 _ _ hx
  refine ⟨y, hy, ?_⟩
  rw [ey, e, hm _ (scA_aligned (hP.e.tcb t ht)) (Or.inr (Or.inr ⟨t, ht, rfl⟩))]

/-- The SC words survive the endpoint code's writes and spec steps. -/
theorem _root_.Fl4Proofs.P3.Ipc.ScRelM.ep_step (hP : IPlaced N T E R B) (h : ScRelM T m σ)
    (hW : ∀ b, Aligned b → ¬ EWrite T E R B b → m' b = m b) (hS : EpStep σ σ') : ScRelM T m' σ' := by
  intro t ht
  obtain ⟨x, hx, e⟩ := h t ht
  have hm : m' (scA t) = m (scA t) :=
    hW _ (scA_aligned (hP.e.tcb t ht)) (fun hw => scA_not_efoot hP ht hw.foot)
  rcases hS.2.2 t.bv with h1 | ⟨a, b, h1, -⟩ | ⟨a, b, h1, -⟩ | ⟨a, y, h1, h2, h3⟩
  · exact ⟨x, by rw [h1, hx], by rw [hm]; exact e⟩
  · rw [hx] at h1; cases h1
  · rw [hx] at h1; cases h1
  · rw [hx] at h1; injection h1 with h1; injection h1 with h1; subst h1
    refine ⟨y, h2, ?_⟩
    have : y.tcbSchedContext = x.tcbSchedContext := by rw [h3]
    rw [this, hm]; exact e

end

section Defs
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- `SR` together with the TCBs' SC words. -/
def SRS (T : Set U64) (SR : S → Fl4Spec.State Unit → Prop) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  SR s σ ∧ ScRelM T (L.mem s) σ

/-- The tail post-condition on the merged footprint and view. -/
def TailPostI (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop)
    (s : S) (σ : Fl4Spec.State Unit) (m : Fl4Spec.SMonad Unit Unit) (s' : S) : Prop :=
  ¬ (m σ).2 ∧ ∃ σ', ((), σ') ∈ (m σ).1 ∧ Agree (L.mem s) (L.mem s') (IFoot N T E R B) ∧ IKView σ σ' ∧ SR s' σ'

/-- **The scheduler tails of the transfers on the merged relation**
(`EpTailHyps` with `IpcRel`, keeping `IFoot` and `IKView`), and the spec's
sporadic check keeping a TCB's SC. -/
structure IpcEpTailHyps (A : Type) (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word))
    (SR : S → Fl4Spec.State Unit → Prop) : Prop where
  wakeTail : ∀ s (a : A) σ (t : U64), IpcRel N T E R B (L.mem s) σ → SR s σ → t ∈ T →
    (do
      let s1 ← endpoint.unblock_sporadic st s t
      let s2 ← sched.possible_switch_to st s1 t
      ok (s2, a)) ⦃ r => r.2 = a ∧ TailPostI st N T E R B SR s σ (specWakeTailE t.bv) r.1 ⦄
  sporadicAssert : ∀ s σ (t : U64), IpcRel N T E R B (L.mem s) σ → SR s σ → t ∈ T →
    endpoint.unblock_sporadic st s t ⦃ s' => ∃ σ', specSporadicAssert t.bv σ = ({((), σ')}, False) ∧
      Agree (L.mem s) (L.mem s') (IFoot N T E R B) ∧ IKView σ σ' ∧ SR s' σ' ⦄
  switchTo : ∀ s (a : A) σ (t : U64), IpcRel N T E R B (L.mem s) σ → SR s σ → t ∈ T →
    (do
      let s1 ← sched.possible_switch_to st s t
      ok (s1, a)) ⦃ r => r.2 = a ∧ TailPostI st N T E R B SR s σ (Fl4Spec.possibleSwitchTo t.bv) r.1 ⦄
  sporadicSc : ∀ σ σ' (t : U64) (x : Fl4Spec.Tcb), specSporadicAssert t.bv σ = ({((), σ')}, False) →
    σ.kheap t.bv = some (.tcb x) → ∃ y, σ'.kheap t.bv = some (.tcb y) ∧ y.tcbSchedContext = x.tcbSchedContext

end Defs

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- `IpcRel ∧ SR` from the endpoint relation and the instantiated `SR`. -/
theorem _root_.Fl4Proofs.P3.Ipc.IpcRel.ofSRN {s : S} {σ : Fl4Spec.State Unit} (hR : EpStateRel T E R B (L.mem s) σ)
    (hS : SRN st N T (SRS st T SR) s σ) : IpcRel N T E R B (L.mem s) σ ∧ SR s σ :=
  ⟨IpcRel.of hS.2 hR hS.1.2.all, hS.1.1⟩

theorem _root_.Fl4Proofs.P3.Ipc.IpcRel.toSRN {s : S} {σ : Fl4Spec.State Unit} (hR : IpcRel N T E R B (L.mem s) σ) (hS : SR s σ) :
    SRN st N T (SRS st T SR) s σ :=
  ⟨⟨hS, ScRelM.of hR⟩, hR.toN⟩

/-- **The endpoint proofs' `EpHyps`** for `SRS T SR`. -/
theorem _root_.Fl4Proofs.P3.Ipc.IpcSchedHyps.epHyps (hH : IpcSchedHyps st ar N T E R B SR) (hP : IPlaced N T E R B) :
    EpHyps st T E R B (SRS st T SR) :=
  ⟨fun _ _ _ _ h1 h2 h3 => ⟨hH.stableE _ _ _ _ h1.1 h2 h3, ScRelM.ep_step hP h1.2 h2.2.2 h3⟩,
   fun s σ t hR hS ht => WP.spec_mono (hH.scheduleTcb s σ t hR hS.2 hS.1 ht) fun _ ⟨hf, hS'⟩ =>
     ⟨fun a ha hfa => hf a ha (EFoot.ifoot hfa), hS', ScRelM.frame hP hS.2 hf (Notif.IKView.stsAct _ _)⟩⟩

/-- `schedule_tcb`, keeping both footprints. -/
theorem _root_.Fl4Proofs.P3.Ipc.IpcSchedHyps.schedC (hH : IpcSchedHyps st ar N T E R B SR) (hP : IPlaced N T E R B) (s : S)
    (σ : Fl4Spec.State Unit) (t : U64) (hR : EpStateRel T E R B (L.mem s) σ) (hS : SRS st T SR s σ) (ht : t ∈ T) :
    sched.schedule_tcb st s t ⦃ s' => FootEq T E R B (L.mem s) (L.mem s') ∧ Notif.FootEq N T (L.mem s) (L.mem s') ∧
      SRS st T SR s' (stsAct σ t.bv) ⦄ :=
  WP.spec_mono (hH.scheduleTcb s σ t hR hS.2 hS.1 ht) fun _ ⟨hf, hS'⟩ =>
    ⟨fun a ha hfa => hf a ha (EFoot.ifoot hfa), fun a ha hfa => hf a ha (NFoot.ifoot hP hfa), hS',
      ScRelM.frame hP hS.2 hf (Notif.IKView.stsAct _ _)⟩

theorem EpBufHyps.srs (h : EpBufHyps st T E R B SR) : EpBufHyps st T E R B (SRS st T SR) :=
  ⟨fun s σ t x b hR hS ht hk => h.lookup s σ t x b hR hS.1 ht hk⟩

theorem EpBufMapHyps.srs (h : EpBufMapHyps st T E R B SR) : EpBufMapHyps st T E R B (SRS st T SR) :=
  ⟨fun s σ t x b p hR hS ht hk hb => h.lookupMap s σ t x b p hR hS.1 ht hk hb,
   fun s σ t x p hR hS ht hk hb => h.frame s σ t x p hR hS.1 ht hk hb,
   fun s σ t x p hR hS ht hk hb => h.recvSlots s σ t x p hR hS.1 ht hk hb⟩

/-- The tails for `SRN N T (SRS T SR)`. -/
theorem IpcEpTailHyps.tail (h : IpcEpTailHyps st A N T E R B SR) (hP : IPlaced N T E R B) :
    EpTailHyps st A T E R B (SRN st N T (SRS st T SR)) :=
  ⟨fun s a σ t hR hS ht => WP.spec_mono (h.wakeTail s a σ t (IpcRel.ofSRN hR hS).1 hS.1.1 ht)
      fun _ ⟨h1, h2, σ', h3, h4, h5, h6⟩ => ⟨h1, h2, σ', h3, fun b hb hf => h4 b hb (EFoot.ifoot hf), h5.2.1,
        ⟨h6, ScRelM.frame hP hS.1.2 h4 h5⟩, hS.2.frame hP.n (fun b hb hf => h4 b hb (NFoot.ifoot hP hf)) h5.1⟩,
   fun s σ t hR hS ht => WP.spec_mono (h.sporadicAssert s σ t (IpcRel.ofSRN hR hS).1 hS.1.1 ht)
      fun _ ⟨σ', h1, h4, h5, h6⟩ => ⟨σ', h1, fun b hb hf => h4 b hb (EFoot.ifoot hf), h5.2.1,
        ⟨h6, ScRelM.frame hP hS.1.2 h4 h5⟩, hS.2.frame hP.n (fun b hb hf => h4 b hb (NFoot.ifoot hP hf)) h5.1⟩,
   fun s a σ t hR hS ht => WP.spec_mono (h.switchTo s a σ t (IpcRel.ofSRN hR hS).1 hS.1.1 ht)
      fun _ ⟨h1, h2, σ', h3, h4, h5, h6⟩ => ⟨h1, h2, σ', h3, fun b hb hf => h4 b hb (EFoot.ifoot hf), h5.2.1,
        ⟨h6, ScRelM.frame hP hS.1.2 h4 h5⟩, hS.2.frame hP.n (fun b hb hf => h4 b hb (NFoot.ifoot hP hf)) h5.1⟩⟩

/-- The SC hypotheses for `SRN N T (SRS T SR)`: the SC words are in `SRS`. -/
theorem IpcEpTailHyps.sc (h : IpcEpTailHyps st A N T E R B SR) : EpScHyps st T E R B (SRN st N T (SRS st T SR)) :=
  ⟨fun s σ t x hS hk ht => by
    rw [hS.1.2.all t ht x hk]
    exact ⟨fun e => by rw [e, optRef_zero], optRef_none⟩, h.sporadicSc⟩

end

end

end Fl4Proofs.P3.Endp
