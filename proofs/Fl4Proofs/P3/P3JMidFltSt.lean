/-
P3 (p3J gen 52): **the cap-fault receive leaf at stable ghosts at every mid state** (batch 1 of gen 51's plan), and
`MidRecvLv` narrowed to its endpoint and notification leaves.

Gen 51's `MidRecvLv` [J] asks, at the mid states `MidRecvSw` speaks of, the three blocking receive leaves
(`RecvLvSt`: endpoint receive, notification receive, cap fault) ending in `RecvRelS Z H Cs` (`RelTopM` and `JAtZR` at
`Z.mv G V` with the entry's `H`, `Cs`). The existing mid-state fault proofs (XTopJointFaultM / C / N / RecvM / RecvC /
DonM) ended in `JAtR` / `JAt` (existential ghosts). This gen each of their 24 declarations was generalised in place
over its post: `…Q` takes `Pq` with `hPq` (every `JAtZR` resp. `JAtZ` at `Z.mv G V` with the entry's `H`, `Cs` gives
`Pq`), the moved body ends in `hPq … J'` where it packed the existential, and the original (statement byte-identical)
is the one-line instance at `JAtR` / `JAt`. Every exit was already at `Z.mv _ _` with the entry's `H`, `Cs`: none
failed, so nothing found false.

* **`fltMidSt`**: `RecvLvSt.flt` at a `JAtZ` state with `MidStF`, a non-resumed action and `CtOK`: a switch
  (`MidE`) by `JAtZ.faultHypJZM3Q`, `chooseNewThread` with `CurInv` (`MidC`) by `JAtZ.faultHypJZC2Q`, `chooseNewThread`
  with ct SC-less (`MidN`) by `JAtZ.faultHypJZNQ`, each at `Pq := JStabR Z H Cs` (the case split of XTopJointKEntry17M /
  21M / 23M).
* `RecvLvIS` (the endpoint and notification fields of `RecvLvSt`) and **`MidRecvLvIS` [J]**: `MidRecvLv` without the
  cap fault. **`midRecvLvIS_of_lv`** (`MidRecvLv → MidRecvLvIS`, field projection) and **`midRecvLv_of_IS`**
  (`MidRecvLvIS → MidRecvLv` at a `VxE` entry, `CtOK` by `ctOK_disp`, the fault by `fltMidSt`): equivalent where the
  top uses it (`DispStabFootLzx.midRecvSw` has `VxE Z`). **`midRecvSw_of_IS`**: `MidRecvLvIS → MidRecvSw`.

Named premises: `MidRecvLvIS` [J] (not in a top; the top stays `kernel_entry_runMcWKR_sysLzy` with
`DispStabFootLzx` [J]). No sorry. New module; the existing statements in the six fault files are unchanged.
-/
import Fl4Proofs.P3.P3JMidRecvSh
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 52) **The cap-fault receive leaf at stable ghosts at a mid state** (module docstring). -/
theorem fltMidSt (hAT : P0.ArchTotal arI) {Z : XSets} [VxE Z] {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hF : MidStF σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hok : MidRun.CtOK σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) :
    ∀ cptr lf lf', LookupFaultRel lf lf' →
      faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
        ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
          RecvRelS (L := L) arI AR Z H Cs r.1 r.2 z.2 ⦄ := by
  intro cptr lf lf' hl
  have hPq : ∀ (G : MdbGhost) (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A)
      (σ' : Fl4Spec.State Unit), JAtZR (L := L) arI AR (Z.mv G V) H Cs Ac' Lst' D' s' a' σ' →
      JStabR (L := L) arI AR Z H Cs s' a' σ' := fun G V Ac' Lst' D' _ _ _ J' => by
        unfold JStabR; exact ⟨G, V, Ac', Lst', D', J'⟩
  cases hsa : σ.schedulerAction with
  | resumeCurThread => exact absurd hsa hsw
  | switchThread u =>
    have hE : MidE σ := ⟨hF.ni, hF.run, Or.inr ⟨u, hsa, fun hu => hF.nsw (by rw [hsa, hu])⟩⟩
    exact J.faultHypJZM3Q (Pq := JStabR (L := L) arI AR Z H Cs) hAT hE hsw hct hF.nq hF.vfh ⟨cptr, true, lf, lf', rfl, by rw [Endp.ofBl_toBl64], hl⟩ hPq
  | chooseNewThread =>
    rcases hok with hC | ⟨x, hx, h0⟩
    · have hMC : MidC σ := ⟨hF.ni, hF.run, hsa, hC⟩
      exact J.faultHypJZC2Q (Pq := JStabR (L := L) arI AR Z H Cs) hAT hMC hMC.nr hct hF.nq hF.vfh ⟨cptr, true, lf, lf', rfl, by rw [Endp.ofBl_toBl64], hl⟩ hPq
    · have hN : MidN σ := ⟨hF.ni, hF.run, hsa, fun x' hx' => by rw [hx] at hx'; cases hx'; exact h0⟩
      exact J.faultHypJZNQ (Pq := JStabR (L := L) arI AR Z H Cs) hAT hN hN.nr hct hF.nq hF.vfh ⟨cptr, true, lf, lf', rfl, by rw [Endp.ofBl_toBl64], hl⟩ hPq

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 52) **The endpoint and notification receive leaves at stable ghosts** (`RecvLvSt` without `flt`). -/
structure RecvLvIS (Z : XSets) (H : P1.Heap) (Cs : Set U64) (ct : U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) :
    Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) Z.th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc) →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RecvRelS (L := L) arI AR Z H Cs r.1 r.2 z.2 ⦄
  sig : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
    JHeld (L := L) Z.th s (.Notification p b w rd) →
    notification.receive_signal st arI s a ct p true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RecvRelS (L := L) arI AR Z H Cs r.1 r.2 z.2 ⦄

/-- (p3J gen 52) **`MidRecvLvIS` [J]**: `MidRecvLv` without the cap-fault leaf (module docstring). -/
def MidRecvLvIS (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64)
    (c : Fl4Spec.Syscall) : Prop :=
  ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
    KFrontB (L := L) arI s a s' a' → JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
    MR a' σb.machineState → SInvCk.CKI σb → SInvRr.RR σb →
    ∀ ct rg sr cr, sched.cur_thread st s' = ok ct → MidSysR n c rg sr cr →
    ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true
        (Fl4Spec.toBl (L.mem s' (Endp.regA ct rg)).bv)).run σb).1, y.1 = .ok () →
      y.2.schedulerAction ≠ .resumeCurThread → MidStF y.2 →
      ∀ (G : MdbGhost) (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s1 : S) (a1 : A),
        JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s1 a1 y.2 → ∀ ct1, sched.cur_thread st s1 = ok ct1 →
        RecvLvIS (L := L) arI AR (Z.mv G V) H Cs ct1 s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- (p3J gen 52) **`MidRecvLv → MidRecvLvIS`** (module docstring). -/
theorem midRecvLvIS_of_lv {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {n : I64} {c : Fl4Spec.Syscall} (h : MidRecvLv (L := L) arI AR MR Z H Cs s a σ n c) :
    MidRecvLvIS (L := L) arI AR MR Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF G V Ac1 Lst1 D1 s1 a1 J1 ct1
    hct1
  have hL := h σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF G V Ac1 Lst1 D1 s1 a1
    J1 ct1 hct1
  exact ⟨hL.ipc, hL.sig⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 52) **`MidRecvLvIS → MidRecvLv`** at a `VxE` entry (module docstring). -/
theorem midRecvLv_of_IS (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) {Z : XSets} [VxE Z] {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    {n : I64} {c : Fl4Spec.Syscall} (h : MidRecvLvIS (L := L) arI AR MR Z H Cs s a σ n c) :
    MidRecvLv (L := L) arI AR MR Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF G V Ac1 Lst1 D1 s1 a1 J1 ct1
    hct1
  have hL := h σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF G V Ac1 Lst1 D1 s1 a1
    J1 ct1 hct1
  exact ⟨hL.ipc, hL.sig, fltMidSt hA J1 hF hnr (ctOK_disp hnd J hX hni hBA J' _ y hy) hct1⟩

/-- (p3J gen 52) **`MidRecvLvIS → MidRecvSw`** (`midRecvLv_of_IS`, then gen 51's `midRecvSw_of_lv`). -/
theorem midRecvSw_of_IS (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) {Z : XSets} [VxE Z] {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    {n : I64} {c : Fl4Spec.Syscall} (h : MidRecvLvIS (L := L) arI AR MR Z H Cs s a σ n c) :
    MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c :=
  midRecvSw_of_lv hA hnd J hX hni (midRecvLv_of_IS hA hnd J hX hni h)

end

end

end Fl4Proofs.P3.Mc
