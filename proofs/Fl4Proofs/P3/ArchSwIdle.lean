/-
P3 (line p3J, gen 9): **the idle half of `ArchSwF` is a theorem where it is used**.

`ArchSwF` [P] (ScArchF) has a thread half (`set_vm_root` against `archSwitchToThread`) and an idle half
(`set_kernel_vm_root` against `archSwitchToIdleThread` = `setVmRoot idleThread`), both asked at every
related state. The idle half is false as stated wherever the idle TCB's vtable is a mapped PML4 cap (the
spec then switches to that PML4, FL4 to the kernel root), which `SchedRel`/`NtfnStateRel`/`VsRootOK` do not
exclude. Its only use on the U-chain is G7eChain's `scnt_refines0FA`, at states where `RootFr` (hence
`RootOK.idle` = `IdleVt`) is carried.

* `ArchSwFT` = the thread half (verbatim); **`ArchSwFI`** = the idle half with one more antecedent
  `IdleVt σ` (the idle TCB is in the heap and its vtable is no mapped PML4 cap); `ArchSwF' := ArchSwFT ∧
  ArchSwFI` (same parameters as `ArchSwF`); `ArchSwF.toN : ArchSwF → ArchSwF'` (weaker).
* **`archSwFI_of : P0.ArchTotal ar → ArchSwFI st ar N T C c`** at every ghost set: no opaque step is
  involved. The spec's `setCurrentCr3` is a plain state update (VSpace.lean, l4v `set_current_cr3`), so
  `archSwitchToIdleThread σ` has the single outcome `cr3Upd σ (globCr3 σ)` (VsRoot's `setVmRoot_other`);
  FL4's `set_kernel_vm_root` keeps the store (`set_kernel_vm_root_s`) and is total (P0, `ArchTotal`);
  `SchedRel` / `NtfnStateRel` / `ArchKeeps` across a CR3-only change (`SchedRel.fpu`, `NtfnStateRel.fpu`).
  So there is no CR3-write determinism premise: the idle half is removed outright.
* Re-proved consumers on `ArchSwF'` (text copies, `scratch/p3J/genK1.py`):
  **`scnt_refines0FAI`** (G7eChain's `scnt_refines0FA`; the two idle instances take `hO.now.idle` and
  `(hO _ _ hwN haK.1 hcN).idle`); `sw_refinesFAI`, `Sched.sw_refinesFI` (G7eChain / ScScheduleF, thread half
  only: needed because a copied `hA.1` is `@And.left T I hA` with the old idle half `I`);
  **`scnt_refines0FI`** (ScNextDomF's `scnt_refines0F` + `hIV : IdleVt σ`, carried to the domain-switch
  state by `IdleVt.frame` across `ArchKeepsF`).
* Why U42 is not here (gen 9 diagnostic, P3KXport's `transportD` on U41's cone: 121 constants copied, the
  kernel rejects `sw_refinesF`, `sw_refinesFA`, `scnt_refines0F`): besides G7eChain's A-chain (which has
  `RootFr`), U41's cone still runs the pre-g7e scheduler chain ScNextDomF/ScNextDomCF/ScNextDomCFR
  (`scnt_refines0F` → `cn_refines0F` / `cn_app0F` / `cn_enq0F` / `switch_branch_refines0F` /
  `schedule_refinesWP0FR`) under XTopJointJAtZRB's `jat_scheduleWP0FZR` / `jat_scheduleFR2ZR` /
  `jat_scheduleSR2ZRP` and `jat_finishJRP` / `jat_finishJRN` / `Fl4ProofsQ.jat_finishJRNM`, reached from the
  `KFinAtR` record (XTopJointKEntry4) through `jEvRef_*` / `kPreFinAtGMS`. That chain applies the idle half
  at `σn` with no `IdleVt` in scope: it must be threaded (handoff p3J gen 9 plan).

Named premises: none new (`ArchSwFT` is `ArchSwF`'s thread half, [P] where it is assumed). No sorry.
-/
import Fl4Proofs.P3.G7eChain
import Fl4Proofs.P3.ScFpuNd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3 Fl4Proofs.P3.Vs

noncomputable section

section
variable {S A : Type}

/-- **[P] The thread half of `ArchSwF`** (verbatim). -/
def ArchSwFT (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (N T C : Set U64) (c : U64) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), SchedRel st N T C c s σ → NtfnStateRel N T (L.mem s) σ →
    FpuOwnOK σ → VsRootOK T σ →
    ∀ t ∈ T, vspace.set_vm_root st ar s a t ⦃ r => ∃ σ1, Fl4Spec.archSwitchToThread (Z := Unit) t.bv σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeepsF σ σ1 ⦄

/-- **The idle half of `ArchSwF`, at states with `IdleVt`** (a theorem: `archSwFI_of`). -/
def ArchSwFI (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (N T C : Set U64) (c : U64) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), SchedRel st N T C c s σ → NtfnStateRel N T (L.mem s) σ →
    VsRootOK T σ → IdleVt σ → vspace.set_kernel_vm_root st ar s a ⦃ r => ∃ σ1,
      Fl4Spec.archSwitchToIdleThread (Z := Unit) σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeeps σ σ1 ⦄

/-- **`ArchSwF` with the idle half narrowed to `IdleVt` states.** -/
def ArchSwF' (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (N T C : Set U64) (c : U64) : Prop :=
  ArchSwFT st ar N T C c ∧ ArchSwFI st ar N T C c

end

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

theorem ArchSwF.toN {N T C : Set U64} {c : U64} (h : ArchSwF st ar N T C c) : ArchSwF' st ar N T C c :=
  ⟨h.1, fun s a σ hS hR hv _ => h.2 s a σ hS hR hv⟩

/-- The spec's idle switch at an `IdleVt` state: CR3 to the global PML4, nothing else. -/
theorem archSwitchToIdle_eq {σ : Fl4Spec.State Unit} (hIV : IdleVt σ) :
    Fl4Spec.archSwitchToIdleThread (Z := Unit) σ = ({((), cr3Upd σ (globCr3 σ))}, False) := by
  obtain ⟨x, hx, hv⟩ := hIV
  unfold Fl4Spec.archSwitchToIdleThread
  rw [nd_gets_bind]
  exact setVmRoot_other hx hv

theorem archKeeps_cr3 (σ : Fl4Spec.State Unit) (c : Fl4Spec.Cr3) : ArchKeeps σ (cr3Upd σ c) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The idle half is a theorem** (module docstring). -/
theorem archSwFI_of (hAT : P0.ArchTotal ar) {N T C : Set U64} {c : U64} : ArchSwFI st ar N T C c := by
  intro s a σ hS hR _ hIV
  have hSt : P0.StoreTotal st := P1.LawfulStore.total
  have hk := archKeeps_cr3 σ (globCr3 σ)
  refine WP.spec_mono (P1.spec_eq' (Fl4Proofs.P0.vspace.set_kernel_vm_root.p0 st ar s a hSt hAT)) ?_
  rintro r ⟨hr, -⟩
  rw [set_kernel_vm_root_s hr]
  exact ⟨_, archSwitchToIdle_eq hIV, hS.fpu (ArchKeeps.toF hk) rfl, hR.fpu (ArchKeeps.toF hk).1, hk⟩

theorem ArchSwFT.toN (hAT : P0.ArchTotal ar) {N T C : Set U64} {c : U64} (h : ArchSwFT st ar N T C c) :
    ArchSwF' st ar N T C c :=
  ⟨h, archSwFI_of hAT⟩

end

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
  {AR : A → Fl4Spec.Cr3 → Prop}

-- BEGIN scnt
set_option maxHeartbeats 2000000 in
/-- `scnt_refines0FA` on `ArchSwF'` (the idle half at `RootOK.idle`). -/
theorem scnt_refines0FAI (hRef : ArchRefines ar AR) {N T C P : Set U64} {c : U64} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hO : RootFr (L := L) AR T P c s a σ)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSwF' st ar N T C c) (hAN : ArchNdF st N T C c) (hfo : FpuOwnOK σ) (hvr : VsRootOK T σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hdt : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) :
    sched.schedule_choose_new_thread st ar s a ⦃ r => ∃ σ', Fl4Spec.scheduleChooseNewThread (Z := Unit) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧
      P1.WritesIn st s r.1 (SFootN st T c s) ∧ AR r.2 σ'.archState.x64CurrentCr3 ⦄ := by
  by_cases hd0 : σ.domainTime ≠ 0
  · refine WP.spec_mono (schedule_choose_new_thread_refinesFA hRef s a σ hO.now hS hR hN hI (hA.1 s a σ hS hR hfo hvr)
      (hA.2 s a σ hS hR hvr hO.now.idle) hd0) ?_
    rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hAR⟩
    exact ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, TK.tk0 h10, WritesIn.sfootN_of h11, hAR⟩
  have hnd := hdt.resolve_left hd0
  have hd0' : σ.domainTime = 0 := not_not.1 hd0
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hkf, hka⟩ := ks_fit hS
  obtain ⟨hD, hV, hidx⟩ := hnd
  obtain ⟨w24, w32, wd1, we0, hl0, hu⟩ := next_domain_words hD hV hidx
  have hNc : P1.NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  unfold sched.schedule_choose_new_thread
  step with sched.domain_time.spec2 as ⟨i, hi⟩
  have hi0 : i = 0#u64 := by
    apply UScalar.eq_of_val_eq
    have e := hs.domTime
    rw [hd0', ← hi] at e
    have := congrArg BitVec.toNat e
    simpa using this.symm
  simp only [hi0, ↓reduceIte, bind_ok]
  rw [next_domain_eq s hNc w24 w32 wd1 we0]
  simp only [bind_ok]
  set t := L.mem s (ksW (L.ksb s) (durOff 0#u64))
  obtain ⟨σa, ha1, haS, haR, haK, hdl, hdi, hds, hown⟩ := hAN s σ hS hR hfo
  have hVa : DomListOK σa := hV.congr hdl hdi hds
  have hl : σa.domainList.length = 2 := by rw [hdl]; exact hD.1
  have hnx0 := nextDomain_eq (σ := σa) hl hVa (by rw [hdl]; exact hl0)
  have hnx : Fl4Spec.nextDomain (Z := Unit) σa = ({((), ndSt σa t.bv)}, False) := by rw [← hu]; exact hnx0
  set σn := ndSt σa t.bv
  have hSn : SchedRel st N T C c (ndS (L := L) s t) σn := schedRel_ndS haS t
  have hRn : NtfnStateRel N T (L.mem (ndS (L := L) s t)) σn := ntfnRel_ndS (σ' := σn) haR haS hNk rfl t
  have hNn : NSC N C σn := fun n hn x p hx hp => hN n hn x p ((haK.1.ntcb fun _ e => by cases e).1 hx) hp
  have hIn : Inv σn := Inv.fpu (σ' := σn) hI haK.1 haK.2.1 haK.2.2.1 haK.2.2.2.2.2.1
  have hfoN : FpuOwnOK σn := fun o e => by
    have e' : σa.archState.x64CurrentFpuOwner = some o := e
    rw [hown] at e'; cases e'
  have hvrN : VsRootOK T σn := hvr.ofF haK.1 (show σa.archState.x64AsidTable = σ.archState.x64AsidTable from asid_of_crk Vs.crk_archPrepareNextDomain ha1)
  have hwN : P1.WritesIn st s (ndS (L := L) s t) (SFootN st T c s) := by
    have hRa : P1.Aligned (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) :=
      P1.nodeAt_aligned hNc (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
    have hRv := P1.nodeAt_val hNc (off := layout.node.REPROGRAM) (by simp [layout.node.REPROGRAM])
    have hf := hNc.fits
    simp only [P1.LawfulStore.nodeBase] at hf
    have hw0 := ndS_writes (st := st) hkf hka hRa (fun o ho => by
        rw [hRv, ksW_val (by omega)]; simp only [P1.LawfulStore.nodeBase]; simp [layout.node.REPROGRAM]; omega)
      (by have := hs.curDom.2; rwa [curDomA_ks] at this) t
    refine hw0.mono fun b hb => ?_
    rcases hb with hb | rfl
    · exact Or.inr hb
    · refine Or.inl (Or.inr ⟨?_, ?_⟩) <;> rw [hRv, hc.cur] <;> simp [layout.node.REPROGRAM]
  have hcN : Vs.crF σn = Vs.crF σ :=
    (show Vs.crF σn = Vs.crF σa from rfl).trans (crf_of_crk Vs.crk_archPrepareNextDomain ha1)
  refine WP.spec_mono (choose_thread_refinesFA hRef (ndS (L := L) s t) a σn (hO _ _ hwN haK.1 hcN) hSn hRn hNn hIn
    (hA.1 _ a σn hSn hRn hfoN hvrN) (hA.2 _ a σn hSn hRn hvrN (hO _ _ hwN haK.1 hcN).idle) (hSn.lists.choose_spec.choose_spec.2.idleTh).symm) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, h12, hAR⟩
  refine ⟨σ', ?_, h2, h3, h4, h5, ?_, h7.trans haK.2.2.2.2.1, h8.trans haK.2.2.1, HeapEqUpToFpu.trans (σ2 := σn) haK.1 h9,
    ?_, WritesIn.sfootN_trans hwN (WritesIn.sfootN_of h12), hAR⟩
  · unfold Fl4Spec.scheduleChooseNewThread
    rw [nd_gets_bind]
    unfold Fl4Spec.NonDet.when
    rw [if_pos hd0', nd_bind_one (show (do Fl4Spec.archPrepareNextDomain; Fl4Spec.nextDomain :
      Fl4Spec.SMonad Unit Unit) σ = ({((), σn)}, False) from by rw [nd_bind_one ha1]; exact hnx), nd_bind_one h1]
    rfl
  · rcases h6 with h6 | h6
    · exact Or.inl (h6.trans haK.2.2.2.2.2.2.2.2.1)
    · exact Or.inr (by rw [← schedulable_fpu (σ' := σn) haK.1 haK.2.2.1]; exact h6)
  · exact (show TK0 σ σn from ⟨haK.2.2.2.2.2.1, haK.2.2.2.2.2.2.1, haK.2.2.2.2.2.2.2.2.1, hs.curDom.1.symm,
      haK.2.2.2.2.2.2.2.2.2.2.2⟩).trans (TK.tk0 h11)


/-- `sw_refinesFA` on `ArchSwF'` (thread half only). -/
theorem sw_refinesFAI (hRef : ArchRefines ar AR) {N T C P : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hO : RootOK (L := L) AR T P s a σ)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSwF' st ar N T C c) (hfo : FpuOwnOK σ) (hvr : VsRootOK T σ) {t : U64} (ht : t ∈ T)
    (hsch : Fl4Spec.schedulable t.bv σ = true) :
    sched.switch_to_thread st ar s a t ⦃ r => ∃ σ', (do
        Fl4Spec.guardedSwitchTo (Z := Unit) t.bv
        Fl4Spec.setSchedulerAction .resumeCurThread) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK σ σ' ∧
      WritesIn st s r.1 (SFoot st T c s) ∧ AR r.2 σ'.archState.x64CurrentCr3 ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, hk, hd, -, -, -⟩ := hs.tcb t ht
  obtain ⟨x', scp, -, -, hk', hsc, -⟩ := schedulable_inv hsch
  rw [hk] at hk'; cases hk'
  have hsw := switch_to_thread_refinesF s a σ hS hR hN ht (hA.1 s a σ hS hR hfo hvr t ht)
  refine WP.spec_mono (WP.spec_and hsw (switch_to_thread_ar hRef hO ht (WP.spec_mono hsw fun _ _ => trivial))) ?_
  rintro r ⟨⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, h12⟩, hAR⟩
  refine ⟨σ', ?_, h2, h3, h4, h5 hI, Or.inr (by rw [h6]; exact hsch), h7, h8, h9, h11, h12, hAR σ' h1⟩
  rw [nd_bind_one (by rw [guardedSwitchTo_eq hk hsc hsch (by rw [hd, hs.curDom.1])]; exact h1)]
  rfl

/-- The switch-thread branch's direct switch: `guarded_switch_to` of a
schedulable thread, then `resume_cur_thread`. -/
theorem sw_refinesFI {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSwF' st ar N T C c) (hfo : FpuOwnOK σ) (hvr : VsRootOK T σ) {t : U64} (ht : t ∈ T) (hsch : Fl4Spec.schedulable t.bv σ = true) :
    sched.switch_to_thread st ar s a t ⦃ r => ∃ σ', (do
        Fl4Spec.guardedSwitchTo (Z := Unit) t.bv
        Fl4Spec.setSchedulerAction .resumeCurThread) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, hk, hd, -, -, -⟩ := hs.tcb t ht
  obtain ⟨x', scp, -, -, hk', hsc, -⟩ := schedulable_inv hsch
  rw [hk] at hk'; cases hk'
  refine WP.spec_mono (switch_to_thread_refinesF s a σ hS hR hN ht (hA.1 s a σ hS hR hfo hvr t ht)) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, h12⟩
  refine ⟨σ', ?_, h2, h3, h4, h5 hI, Or.inr (by rw [h6]; exact hsch), h7, h8, h9, h11, h12⟩
  rw [nd_bind_one (by rw [guardedSwitchTo_eq hk hsc hsch (by rw [hd, hs.curDom.1])]; exact h1)]
  rfl
-- END scnt

end

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

-- BEGIN scntN

set_option maxHeartbeats 2000000 in
/-- ScNextDomF's `scnt_refines0F` on `ArchSwF'`, given `IdleVt σ` (carried to the domain-switch state `σn` by
`IdleVt.frame`). Original docstring: **`schedule_choose_new_thread` refines l4v's, with the domain switch**:
as `schedule_choose_new_thread_refines` when the domain time is nonzero;
when it is 0, from `NdOK` (ScNextDom: `next_domain` back to entry 0 on both
sides) and `ArchNd` [P], `next_domain` then `choose_thread` at FL4's
`ndS s t` and the spec's `ndSt σa t'` (`σa` after
`arch_prepare_next_domain`). The post keeps `TK0` (not the domain time)
and widens the footprint by `NdW` (`SFootN`). -/
theorem scnt_refines0FI {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSwF' st ar N T C c) (hAN : ArchNdF st N T C c) (hfo : FpuOwnOK σ) (hvr : VsRootOK T σ) (hIV : IdleVt σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hdt : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) :
    sched.schedule_choose_new_thread st ar s a ⦃ r => ∃ σ', Fl4Spec.scheduleChooseNewThread (Z := Unit) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧
      P1.WritesIn st s r.1 (SFootN st T c s) ⦄ := by
  by_cases hd0 : σ.domainTime ≠ 0
  · refine WP.spec_mono (schedule_choose_new_thread_refinesF s a σ hS hR hN hI (hA.1 s a σ hS hR hfo hvr) (hA.2 s a σ hS hR hvr hIV)
      hd0) ?_
    rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, TK.tk0 h10, WritesIn.sfootN_of h11⟩
  have hnd := hdt.resolve_left hd0
  have hd0' : σ.domainTime = 0 := not_not.1 hd0
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hkf, hka⟩ := ks_fit hS
  obtain ⟨hD, hV, hidx⟩ := hnd
  obtain ⟨w24, w32, wd1, we0, hl0, hu⟩ := next_domain_words hD hV hidx
  have hNc : P1.NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  unfold sched.schedule_choose_new_thread
  step with Sched.sched.domain_time.spec2 as ⟨i, hi⟩
  have hi0 : i = 0#u64 := by
    apply UScalar.eq_of_val_eq
    have e := hs.domTime
    rw [hd0', ← hi] at e
    have := congrArg BitVec.toNat e
    simpa using this.symm
  simp only [hi0, ↓reduceIte, bind_ok]
  rw [next_domain_eq s hNc w24 w32 wd1 we0]
  simp only [bind_ok]
  set t := L.mem s (ksW (L.ksb s) (durOff 0#u64))
  -- the spec: `arch_prepare_next_domain`, then `next_domain`
  obtain ⟨σa, ha1, haS, haR, haK, hdl, hdi, hds, hown⟩ := hAN s σ hS hR hfo
  have hVa : DomListOK σa := hV.congr hdl hdi hds
  have hl : σa.domainList.length = 2 := by rw [hdl]; exact hD.1
  have hnx0 := nextDomain_eq (σ := σa) hl hVa (by rw [hdl]; exact hl0)
  have hnx : Fl4Spec.nextDomain (Z := Unit) σa = ({((), ndSt σa t.bv)}, False) := by rw [← hu]; exact hnx0
  set σn := ndSt σa t.bv
  have hSn : SchedRel st N T C c (ndS (L := L) s t) σn := schedRel_ndS haS t
  have hRn : NtfnStateRel N T (L.mem (ndS (L := L) s t)) σn := ntfnRel_ndS (σ' := σn) haR haS hNk rfl t
  have hNn : NSC N C σn := fun n hn x p hx hp => hN n hn x p ((haK.1.ntcb fun _ e => by cases e).1 hx) hp
  have hIn : Inv σn := Inv.fpu (σ' := σn) hI haK.1 haK.2.1 haK.2.2.1 haK.2.2.2.2.2.1
  have hfoN : FpuOwnOK σn := fun o e => by
    have e' : σa.archState.x64CurrentFpuOwner = some o := e
    rw [hown] at e'; cases e'
  have hvrN : VsRootOK T σn := hvr.ofF haK.1 (show σa.archState.x64AsidTable = σ.archState.x64AsidTable from asid_of_crk Vs.crk_archPrepareNextDomain ha1)
  refine WP.spec_mono (choose_thread_refinesF (ndS (L := L) s t) a σn hSn hRn hNn hIn (hA.1 _ a σn hSn hRn hfoN hvrN)
    (hA.2 _ a σn hSn hRn hvrN (IdleVt.frame (σ' := σn) hIV haK.1 haK.2.2.2.2.2.2.2.2.1)) (hSn.lists.choose_spec.choose_spec.2.idleTh).symm) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, h12⟩
  refine ⟨σ', ?_, h2, h3, h4, h5, ?_, h7.trans haK.2.2.2.2.1, h8.trans haK.2.2.1, HeapEqUpToFpu.trans (σ2 := σn) haK.1 h9, ?_, ?_⟩
  · unfold Fl4Spec.scheduleChooseNewThread
    rw [nd_gets_bind]
    unfold Fl4Spec.NonDet.when
    rw [if_pos hd0', nd_bind_one (show (do Fl4Spec.archPrepareNextDomain; Fl4Spec.nextDomain :
      Fl4Spec.SMonad Unit Unit) σ = ({((), σn)}, False) from by rw [nd_bind_one ha1]; exact hnx), nd_bind_one h1]
    rfl
  · rcases h6 with h6 | h6
    · exact Or.inl (h6.trans haK.2.2.2.2.2.2.2.2.1)
    · exact Or.inr (by rw [← schedulable_fpu (σ' := σn) haK.1 haK.2.2.1]; exact h6)
  · exact (show TK0 σ σn from ⟨haK.2.2.2.2.2.1, haK.2.2.2.2.2.2.1, haK.2.2.2.2.2.2.2.2.1, hs.curDom.1.symm,
      haK.2.2.2.2.2.2.2.2.2.2.2⟩).trans (TK.tk0 h11)
  · have hRa : P1.Aligned (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) :=
      P1.nodeAt_aligned hNc (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
    have hRv := P1.nodeAt_val hNc (off := layout.node.REPROGRAM) (by simp [layout.node.REPROGRAM])
    have hf := hNc.fits
    simp only [P1.LawfulStore.nodeBase] at hf
    have hw0 := ndS_writes (st := st) hkf hka hRa (fun o ho => by
        rw [hRv, ksW_val (by omega)]; simp only [P1.LawfulStore.nodeBase]; simp [layout.node.REPROGRAM]; omega)
      (by have := hs.curDom.2; rwa [curDomA_ks] at this) t
    refine WritesIn.sfootN_trans (hw0.mono fun b hb => ?_) (WritesIn.sfootN_of h12)
    rcases hb with hb | rfl
    · exact Or.inr hb
    · refine Or.inl (Or.inr ⟨?_, ?_⟩) <;> rw [hRv, hc.cur] <;> simp [layout.node.REPROGRAM]

-- END scntN

end

end

end Fl4Proofs.P3
