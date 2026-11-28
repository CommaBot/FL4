/-
P3 (p3J gen 53): **the notification receive leaf at stable ghosts at every mid state** (batch 2 of gen 51's plan),
and `MidRecvLvIS` narrowed to its endpoint leaf.

The mid-state notification receive proofs (XTopJointRecvMid / RecvSigM / RecvSigRetM / RecvSigC / RecvSigN /
RecvSigDonD) ended in `RJR` / `RJ` (`RelTopM` and existential ghosts). This gen each of their 15 declarations was
generalised in place over its post, exactly as gen 52's fault leaves: `…Q` takes `Pq` with `hPq` (every `JAtZR`
resp. `JAtZ` at `Z.mv G V` with the entry's `H`, `Cs` gives `Pq`) and ends in `RelTopM ∧ Pq`; the moved body ends
in `hPq … J'` where it packed the existential; the original (statement byte-identical up to `:=`) is the one-line
instance at `RJR` / `RJ`. Every exit was already at `Z.mv _ _` with the entry's `H`, `Cs`: nothing found false.

* **`sigMidSt`**: `RecvLvIS.sig` at a `JAtZ` state with `MidStF`, a non-resumed action and `CtOK`: a switch (`MidE`)
  by `jRecvSigHypM2_ofQ`, `chooseNewThread` with `CurInv` (`MidC`) by `jRecvSigHypC2_ofQ`, `chooseNewThread` with ct
  SC-less (`MidN`) by `jRecvSigHypDNQ`, each at `Pq := JStabR Z H Cs` (the case split of `fltMidSt`). It needs
  `hmb` (`min_budget`, the donating `MidN` case), which the top has from `TimeAgree` (`Sched.TimeAgree.mb`).
* `RecvLvI` (the endpoint field of `RecvLvSt`) and **`MidRecvLvI` [J]**: `MidRecvLvIS` without the notification
  receive. **`midRecvLvI_of_IS`** (`MidRecvLvIS → MidRecvLvI`, projection) and **`midRecvLvIS_of_I`**
  (`MidRecvLvI → MidRecvLvIS` at a `VxE` entry with `hmb`, `CtOK` by `ctOK_disp`, the notification by `sigMidSt`):
  equivalent where the top uses it. **`midRecvSw_of_I`**: `MidRecvLvI → MidRecvSw`.

Named premises: `MidRecvLvI` [J] (not in a top; the top stays `kernel_entry_runMcWKR_sysLzy` with
`DispStabFootLzx` [J]). No sorry. New module; the existing statements in the six notification files are unchanged.
-/
import Fl4Proofs.P3.P3JMidFltSt
import Fl4Proofs.P3.XTopJointRecvSigDonD
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
/-- (p3J gen 53) **The notification receive leaf at stable ghosts at a mid state** (module docstring). -/
theorem sigMidSt (hAT : P0.ArchTotal arI)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {Z : XSets} [VxE Z] {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hF : MidStF σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hok : MidRun.CtOK σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) :
    ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
      JHeld (L := L) Z.th s (.Notification p b w rd) →
      notification.receive_signal st arI s a ct p true ⦃ r =>
        ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RecvRelS (L := L) arI AR Z H Cs r.1 r.2 z.2 ⦄ := by
  intro p b w rd ac hcr hex hHd
  have hPq : ∀ (G : MdbGhost) (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A)
      (σ' : Fl4Spec.State Unit), JAtZR (L := L) arI AR (Z.mv G V) H Cs Ac' Lst' D' s' a' σ' →
      JStabR (L := L) arI AR Z H Cs s' a' σ' := fun G V Ac' Lst' D' _ _ _ J' => by
        unfold JStabR; exact ⟨G, V, Ac', Lst', D', J'⟩
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  cases hsa : σ.schedulerAction with
  | resumeCurThread => exact absurd hsa hsw
  | switchThread u =>
    have hE : MidE σ := ⟨hF.ni, hF.run, Or.inr ⟨u, hsa, fun hu => hF.nsw (by rw [hsa, hu])⟩⟩
    exact jRecvSigHypM2_ofQ (Pq := JStabR (L := L) arI AR Z H Cs) hAT J hctT hcur hE hsw hF.nq p b w rd ac hcr hex
      hHd hPq
  | chooseNewThread =>
    rcases hok with hC | ⟨x, hx, h0⟩
    · have hMC : MidC σ := ⟨hF.ni, hF.run, hsa, hC⟩
      exact jRecvSigHypC2_ofQ (Pq := JStabR (L := L) arI AR Z H Cs) hAT J hctT hcur hMC hMC.nr hF.nq p b w rd ac hcr
        hex hHd hPq
    · have hN : MidN σ := ⟨hF.ni, hF.run, hsa, fun x' hx' => by rw [hx] at hx'; cases hx'; exact h0⟩
      exact jRecvSigHypDNQ (Pq := JStabR (L := L) arI AR Z H Cs) hAT hmb J hctT hcur hN hN.nr hF.nq p b w rd ac hcr
        hex hHd hPq

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 53) **The endpoint receive leaf at stable ghosts** (`RecvLvSt` without `sig`, `flt`). -/
structure RecvLvI (Z : XSets) (H : P1.Heap) (Cs : Set U64) (ct : U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) :
    Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) Z.th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc) →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RecvRelS (L := L) arI AR Z H Cs r.1 r.2 z.2 ⦄

/-- (p3J gen 53) **`MidRecvLvI` [J]**: `MidRecvLvIS` without the notification leaf (module docstring). -/
def MidRecvLvI (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64)
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
        RecvLvI (L := L) arI AR (Z.mv G V) H Cs ct1 s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- (p3J gen 53) **`MidRecvLvIS → MidRecvLvI`** (module docstring). -/
theorem midRecvLvI_of_IS {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {n : I64} {c : Fl4Spec.Syscall} (h : MidRecvLvIS (L := L) arI AR MR Z H Cs s a σ n c) :
    MidRecvLvI (L := L) arI AR MR Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF G V Ac1 Lst1 D1 s1 a1 J1 ct1
    hct1
  exact ⟨(h σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF G V Ac1 Lst1 D1 s1 a1
    J1 ct1 hct1).ipc⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 53) **`MidRecvLvI → MidRecvLvIS`** at a `VxE` entry (module docstring). -/
theorem midRecvLvIS_of_I (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) {Z : XSets} [VxE Z]
    {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    {n : I64} {c : Fl4Spec.Syscall} (h : MidRecvLvI (L := L) arI AR MR Z H Cs s a σ n c) :
    MidRecvLvIS (L := L) arI AR MR Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF G V Ac1 Lst1 D1 s1 a1 J1 ct1
    hct1
  have hL := h σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF G V Ac1 Lst1 D1 s1 a1
    J1 ct1 hct1
  exact ⟨hL.ipc, sigMidSt hA hmb J1 hF hnr (ctOK_disp hnd J hX hni hBA J' _ y hy) hct1⟩

/-- (p3J gen 53) **`MidRecvLvI → MidRecvSw`** (`midRecvLvIS_of_I`, then gen 52's `midRecvSw_of_IS`). -/
theorem midRecvSw_of_I (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) {Z : XSets} [VxE Z]
    {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    {n : I64} {c : Fl4Spec.Syscall} (h : MidRecvLvI (L := L) arI AR MR Z H Cs s a σ n c) :
    MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c :=
  midRecvSw_of_IS hA hnd J hX hni (midRecvLvIS_of_I hA hnd hmb J hX hni h)

end

end

end Fl4Proofs.P3.Mc
