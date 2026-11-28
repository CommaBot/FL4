/-
P3 (p3J gen 53): **the endpoint receive leaf at stable ghosts at a switch mid state** (batch 3 of gen 51's plan),
and `MidRecvLvI` narrowed to the `chooseNewThread` mid states.

The switch-state endpoint receive proofs (XTopJointKEntry11M / 13M / 14M / 15M, RecvIpcBlockM, RecvRetM, RecvSendPM)
and the resumed-chain leaves they call (RecvIpcBlock, RecvSend, RecvSendF, RecvSendP, RecvSendRD, RecvSendT) ended in
`RJR` / `RJ` (`RelTopM` and existential ghosts). This gen each of their 30 declarations was generalised in place over
its post, exactly as gen 52's fault leaves: `…Q` takes `Pq` with `hPq` (every `JAtZR` resp. `JAtZ` at `Z.mv G V` with
the entry's `H`, `Cs` gives `Pq`) and ends in `RelTopM ∧ Pq`; the moved body ends in `hPq … J'` where it packed the
existential, a call of another such leaf became its `…Q` with `hPq` (or `hPq ∘ toR` from a `JAtZR`-posted caller to a
`JAtZ`-posted callee); the original (statement byte-identical up to `:=`) is the one-line instance at `RJR` / `RJ`.
Every exit, including the resumed-chain leaves reached after `cancel_ipc` / `maybe_return_sc` at `Z.mv Z.G V`, was
already at `Z.mv _ _` with the entry's `H`, `Cs`: nothing found false.

* **`ipcMidE`**: `RecvLvI.ipc` at a `JAtZ` state with `MidStF` and a pending switch (neither resume nor
  `chooseNewThread`): a null or free reply by `jRecvIpcUMQ`, a reply linked to another thread by `jRecvIpcLinkMQ`, at
  `Pq := JStabR Z H Cs` (the case split of XTopJointKEntry15M's `JRecvLeavesRN6.toRN5`).
* **`MidRecvLvIC` [J]**: `MidRecvLvI` asked only where the first phase leaves `chooseNewThread`.
  **`midRecvLvIC_of_I`** (`MidRecvLvI → MidRecvLvIC`, weakening) and **`midRecvLvI_of_IC`** (`MidRecvLvIC →
  MidRecvLvI`, the switch case by `ipcMidE`; `hmax`, `htu` are globals of the top): equivalent.
  **`midRecvSw_of_IC`**: `MidRecvLvIC → MidRecvSw`.

Named premises: `MidRecvLvIC` [J] (not in a top; the top stays `kernel_entry_runMcWKR_sysLzy` with
`DispStabFootLzx` [J]). No sorry. New module; the existing statements in the thirteen endpoint files are unchanged.
-/
import Fl4Proofs.P3.P3JMidSigSt
import Fl4Proofs.P3.XTopJointKEntry15M
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
/-- (p3J gen 53) **The endpoint receive leaf at stable ghosts at a switch mid state** (module docstring). -/
theorem ipcMidE (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {Z : XSets} [VxE Z] {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hF : MidStF σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hcn : σ.schedulerAction ≠ .chooseNewThread) {ct : U64} (hct : sched.cur_thread st s = ok ct) :
    ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
      ((rc = .Null ∧ rc' = .nullCap) ∨
        (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
      JHeld (L := L) Z.th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc) →
      endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
        ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
          RecvRelS (L := L) arI AR Z H Cs r.1 r.2 z.2 ⦄ := by
  intro p b sd g gr rc rc' hpE hrc hHd hHr
  have hPq : ∀ (G : MdbGhost) (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A)
      (σ' : Fl4Spec.State Unit), JAtZR (L := L) arI AR (Z.mv G V) H Cs Ac' Lst' D' s' a' σ' →
      JStabR (L := L) arI AR Z H Cs s' a' σ' := fun G V Ac' Lst' D' _ _ _ J' => by
        unfold JStabR; exact ⟨G, V, Ac', Lst', D', J'⟩
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hE : MidE σ := by
    refine ⟨hF.ni, hF.run, Or.inr ?_⟩
    cases e : σ.schedulerAction with
    | resumeCurThread => exact absurd e hsw
    | chooseNewThread => exact absurd e hcn
    | switchThread u => exact ⟨u, rfl, fun hu => hF.nsw (by rw [e, hu])⟩
  by_cases hun : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (rTcbA q) = 0#u64
  · exact jRecvIpcUMQ (Pq := JStabR (L := L) arI AR Z H Cs) hAT hmax (htu a) J hctT hcur hE hsw hF.nq p b sd g gr
      rc rc' hpE hrc hHd hHr hun hPq
  · rcases hrc with ⟨rfl, -⟩ | ⟨hcr, q, g', rfl, xr, hkr⟩
    · exact absurd (Or.inl rfl) hun
    · exact jRecvIpcLinkMQ (Pq := JStabR (L := L) arI AR Z H Cs) hAT hmax (htu a) J hctT hcur hE hsw hF.nq p b sd g
        gr q g' rc' hpE hcr hkr hHd (hHr q g' rfl) (fun h => hun (Or.inr ⟨q, g', rfl, h⟩)) hPq

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 53) **`MidRecvLvIC` [J]**: `MidRecvLvI` at the `chooseNewThread` mid states only (module docstring). -/
def MidRecvLvIC (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64)
    (c : Fl4Spec.Syscall) : Prop :=
  ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
    KFrontB (L := L) arI s a s' a' → JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
    MR a' σb.machineState → SInvCk.CKI σb → SInvRr.RR σb →
    ∀ ct rg sr cr, sched.cur_thread st s' = ok ct → MidSysR n c rg sr cr →
    ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true
        (Fl4Spec.toBl (L.mem s' (Endp.regA ct rg)).bv)).run σb).1, y.1 = .ok () →
      y.2.schedulerAction ≠ .resumeCurThread → MidStF y.2 → y.2.schedulerAction = .chooseNewThread →
      ∀ (G : MdbGhost) (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s1 : S) (a1 : A),
        JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s1 a1 y.2 → ∀ ct1, sched.cur_thread st s1 = ok ct1 →
        RecvLvI (L := L) arI AR (Z.mv G V) H Cs ct1 s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- (p3J gen 53) **`MidRecvLvI → MidRecvLvIC`** (module docstring). -/
theorem midRecvLvIC_of_I {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {n : I64} {c : Fl4Spec.Syscall} (h : MidRecvLvI (L := L) arI AR MR Z H Cs s a σ n c) :
    MidRecvLvIC (L := L) arI AR MR Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF _ G V Ac1 Lst1 D1 s1 a1 J1
    ct1 hct1
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF G V Ac1 Lst1 D1 s1 a1 J1
    ct1 hct1

set_option maxHeartbeats 4000000 in
/-- (p3J gen 53) **`MidRecvLvIC → MidRecvLvI`** (module docstring). -/
theorem midRecvLvI_of_IC (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {Z : XSets} [VxE Z]
    {H : P1.Heap} {Cs : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {n : I64} {c : Fl4Spec.Syscall} (h : MidRecvLvIC (L := L) arI AR MR Z H Cs s a σ n c) :
    MidRecvLvI (L := L) arI AR MR Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF G V Ac1 Lst1 D1 s1 a1 J1 ct1
    hct1
  by_cases hcn : y.2.schedulerAction = .chooseNewThread
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF hcn G V Ac1 Lst1 D1 s1
      a1 J1 ct1 hct1
  · exact ⟨ipcMidE hAT hmax htu J1 hF hnr hcn hct1⟩

/-- (p3J gen 53) **`MidRecvLvIC → MidRecvSw`** (`midRecvLvI_of_IC`, then `midRecvSw_of_I`). -/
theorem midRecvSw_of_IC (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {Z : XSets} [VxE Z]
    {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    {n : I64} {c : Fl4Spec.Syscall} (h : MidRecvLvIC (L := L) arI AR MR Z H Cs s a σ n c) :
    MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c :=
  midRecvSw_of_I hA hnd hmb J hX hni (midRecvLvI_of_IC hA hmax htu h)

end

end

end Fl4Proofs.P3.Mc
