/-
P3 (p3J gen 36): **a run of primitive steps writes only `ProjW`** (StepSem's `Steps`, the run every
`Steps`-producing decode leaf records: Domain, IRQ control, IO-port control, the TDX control and the IO-port `Out` /
error arms).

XTopJointStep's `stepClosed_jat` proves `JAtZ` across each primitive step (`QJ`). Here the same relation with the
footprint added, `QJW`: from a `JAtZ` state `s` (with `ZNoBlk`), `JAtZ` after (as `QJ`) **and**
`P1.WritesIn st s s' (Mc.ProjW H Cs s)`. Each step's write set is a `ProjW` set at a `JAtZ` state:

* the restart: `set_thread_state` of a TCB of the typed heap (P3JMidInv's `stsProjW`);
* a kernel-state step: `KsW (ksb s)` words, offsets `< 13568` of the kernel-state block (`ProjW`'s second clause);
* an insertion and a CNode-only step: `InSlot th` words, inside a CNode or TCB of the typed heap, hence of `H`
  (`JAtZ.inSlotProjW`: `JPlaced`'s `tcb` / `cnode`, `IsSlotAt.size`, `slotOf_val`);
* a scheduler step: `SchW Z.T Z.c s` (at `Z`'s sets, as `stepClosed_jat`'s scheduler case reads it): TCB words of
  `Z.T` (offsets 3480 / 3488 / 3592 of a 4 KiB TCB of `H`), words of the current core's node (`Z.c = cpu s`, so
  `ProjW`'s exclusion of other cores' words 8 / 32 does not apply), the domain words of the kernel-state block
  (`JAtZ.schWProjW`).

`stepClosed_jatW` (each field from `stepClosed_jat`'s and the write fact), **`Steps.jatZW`**.

No premise (`JStepHyps` is proved: XTopJointRest's `jStepHyps`). No sorry. New module; no existing statement
changed.
-/
import Fl4Proofs.P3.XTopJointStep
import Fl4Proofs.P3.P3JMidInv
import Fl4Proofs.P3.P3JMcKwN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 36) **A slot word of the typed heap is a `ProjW` word** at a `JAtZ` state (module docstring). -/
theorem JAtZ.inSlotProjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : InSlot Z.th b) : Mc.ProjW (L := L) H Cs s b := by
  obtain ⟨y, ⟨p, i, hi, rfl⟩, h1, h2⟩ := hb
  obtain ⟨k, hk, hsz⟩ := hi.size
  have hfit := J.xtop.rel.1.fits p k hk
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  rcases J.thk p k hk with rfl | ⟨r, rfl⟩
  · simp only [objSize] at hsz hfit
    have hv := slotOf_val (p := p) (i := i) (by omega)
    refine Or.inl ⟨p, .tcb, (hJ.tcb p).1 hk, by omega, ?_⟩
    simp only [P1.HKind.bits]
    omega
  · simp only [objSize] at hsz hfit
    have hv := slotOf_val (p := p) (i := i) (by omega)
    refine Or.inl ⟨p, _, hJ.cnode p r hk, by omega, ?_⟩
    have e : (2 : Nat) ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; ring
    simp only [P1.HKind.bits, e]
    omega

/-- (p3J gen 36) **A scheduler step's word (at `Z`'s sets) is a `ProjW` word** at a `JAtZ` state (module
docstring). -/
theorem JAtZ.schWProjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : SchW (L := L) Z.T Z.c s b) : Mc.ProjW (L := L) H Cs s b := by
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hcpu : L.cpu s = Z.c := hc.cur
  rcases hb with ⟨y, hy, rfl | rfl | rfl⟩ | ⟨h1, h2, -⟩ | hd
  · exact Mc.obj_projW J.kern.heap (k := .tcb) (J.zH.1 y hy) (by simp [P1.HKind.bits])
  · exact Mc.obj_projW J.kern.heap (k := .tcb) (J.zH.1 y hy) (by simp [P1.HKind.bits])
  · exact Mc.obj_projW J.kern.heap (k := .tcb) (J.zH.1 y hy) (by simp [P1.HKind.bits])
  · exact Or.inr (Or.inr ⟨Z.c, hcpu ▸ J.kern.cpuCs, h1, h2, fun h => absurd hcpu.symm h⟩)
  · have := domKW_val hd
    exact Or.inr (Or.inl ⟨by omega, by omega⟩)

variable (arI) in
/-- (p3J gen 36) **`QJ` with the `ProjW` footprint** (module docstring). -/
def QJW (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A)
    (σ' : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → ZNoBlk Z.th (L.mem s) (L.ksb s) →
    (∃ (G' : MdbGhost) (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ' ∧ ZNoBlk Z.th (L.mem s') (L.ksb s')) ∧
    P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s)

variable (arI) in
set_option maxHeartbeats 4000000 in
/-- (p3J gen 36) **`QJW` is closed under the primitive steps** (module docstring). -/
theorem stepClosed_jatW (hAM : ARMask arI AR) {th : TypedHeap} (hJ : JStepHyps (L := L) arI AR th) :
    StepClosed (L := L) arI th (QJW (L := L) arI AR th) := by
  have C := stepClosed_jat arI hAM hJ
  refine ⟨fun s1 a1 σ1 s2 a2 σ2 s3 a3 σ3 h1 h2 Z H Cs Ac Lst D hth J hZ => ?_,
    fun s a σ ct x s1 hcur hk htcb hrun hs1 Z H Cs Ac Lst D hth J hZ => ?_,
    fun s s' a a' σ σ' hw hO hdk hdl hds hirq hio harch Z H Cs Ac Lst D hth J hZ => ?_,
    fun s s' a σ σ' G' c ps pd rs rd idxs idxd hps hpd hci hld hcap hnull hnu hw hCR hFI hMO hTS hTK hT3 hDL hDl hVT
      hnn hnz hVK Z H Cs Ac Lst D hth J hZ => ?_,
    fun s s' a σ σ' hS Z H Cs Ac Lst D hth J hZ => ?_,
    fun s s' a σ σ' G' hcn hkc hCK hUK horig hw hCR hFI hMO hTS hTK hT3 hkz hDl W hW hcW hoW hUS hVT hLW hNO hVK
      Z H Cs Ac Lst D hth J hZ => ?_⟩
  · obtain ⟨⟨G1, V1, Ac1, Lst1, D1, J1, hZ1⟩, W1⟩ := h1 Z H Cs Ac Lst D hth J hZ
    obtain ⟨⟨G2, V2, Ac2, Lst2, D2, J2, hZ2⟩, W2⟩ := h2 (Z.mv G1 V1) H Cs Ac1 Lst1 D1 hth J1 hZ1
    exact ⟨⟨G2, V2, Ac2, Lst2, D2, J2, hZ2⟩, W1.projW_trans W2⟩
  · refine ⟨C.restart s a σ ct x s1 hcur hk htcb hrun hs1 Z H Cs Ac Lst D hth J hZ, ?_⟩
    subst hth
    have h := stsProjW J (J.thT ct htcb) sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h
    exact h
  · refine ⟨C.ks s s' a a' σ σ' hw hO hdk hdl hds hirq hio harch Z H Cs Ac Lst D hth J hZ, hw.mono fun b hb => ?_⟩
    obtain ⟨K, h1, h2, -, e, -⟩ := hb
    exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · refine ⟨C.slot s s' a σ σ' G' c ps pd rs rd idxs idxd hps hpd hci hld hcap hnull hnu hw hCR hFI hMO hTS hTK
      hT3 hDL hDl hVT hnn hnz hVK Z H Cs Ac Lst D hth J hZ, ?_⟩
    subst hth
    exact hw.mono fun b hb => J.inSlotProjW hb
  · refine ⟨C.sched s s' a σ σ' hS Z H Cs Ac Lst D hth J hZ, ?_⟩
    subst hth
    have hX := J.xtop
    exact (hS.2.1 Z.N Z.T Z.C Z.c J.thT hX.fin.1.1.1 hX.fin.1.1.2.2.1).2.1.mono fun b hb => J.schWProjW hb
  · refine ⟨C.cslot s s' a σ σ' G' hcn hkc hCK hUK horig hw hCR hFI hMO hTS hTK hT3 hkz hDl W hW hcW hoW hUS hVT
      hLW hNO hVK Z H Cs Ac Lst D hth J hZ, ?_⟩
    subst hth
    exact hw.mono fun b hb => J.inSlotProjW hb

variable (arI) in
/-- (p3J gen 36) **`JAtZ` and the `ProjW` footprint after a run of primitive steps** (module docstring). -/
theorem Steps.jatZW (hAM : ARMask arI AR) {th : TypedHeap} (hJ : JStepHyps (L := L) arI AR th) {s s' : S}
    {a a' : A} {σ σ' : Fl4Spec.State Unit} (h : Steps (L := L) arI th s a σ s' a' σ') (hth : Z.th = th)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hZ : ZNoBlk Z.th (L.mem s) (L.ksb s)) :
    (∃ (G' : MdbGhost) (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ' ∧ ZNoBlk Z.th (L.mem s') (L.ksb s')) ∧
    P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s) :=
  h _ (stepClosed_jatW arI hAM hJ) Z H Cs Ac Lst D hth J hZ

end

end

end Fl4Proofs.P3
