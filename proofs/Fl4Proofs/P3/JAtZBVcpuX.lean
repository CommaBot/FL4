/-
P3 (line mmuAD, gen 27): **`XTopAt` across a spec VCPU-object update** (gen 26's `hX` [J] discharged) and the
VM-epoch invariant with the binding relation, `JAtZV2`.

* **`XTopAt.vcpuSpec`**: `XTopAt AR Z s a σ` and `σ.kheap p = archObj (vcpu vs)` give `XTopAt AR Z s a σ'` for
  `σ' = updK σ p (archObj (vcpu vs'))`, FL4's state and arch state kept. Per component (as XTopBuf's
  `XTopAt.bufSpec` for an IPC-buffer step):
  - `TopSR` by VsTop's `TopSR.step0` with no FL4 write and the spec step `OStep.arch` (an arch object is
    `Passive`: none of the other subsystems' relations reads it);
  - `VsRel` / `PtRel` by their `frame` lemmas: every pool / table of the VSpace sets is a spec `asidPool` /
    table object, so it is not at `p` (a VCPU) and is kept;
  - `PoolsIn`, `CurOK`, `DomRel`, `MdbOKV`, `IpcApart` read no spec heap (unchanged by definition);
  - `StateRel` (CNodes, TCBs: not at `p`), `CRel`'s CDT parts (CDT kept), `FinInv.kt` by `ArFr.ksub`,
    `ScApart` / `EpSchedApart` by `ArFr.szKeep`; `IpcRel` rebuilt from the new `TopSR` (`IpcRel.of`).
* **`JAtZV.vcpuSpec'`**: P3/JAtZBVcpu's `JAtZV.vcpuSpec` at `a' = a` without `hX`.
* **`JAtZV2 V X …`** = `JAtZV V X …` ∧ **`VBind V σ (L.mem s)`** (gen 26's binding relation as a field).
  - Boot: **`JBoot.jAtZV2_w1`** (no premise; `VBind.empty`).
  - **`JAtZV2.of_native`**: at `V = ∅` any native `JAtZ → JAtZ` step lifts (as `JAtZV.of_native`; `VBind ∅` is
    trivial).
  - **`JAtZV2.vcpuWr`**: FL4's write of a VCPU-object word other than `TCB`/`NEXT`/`PREV` (gen 24's
    `JAtZV.vcpuWr`) keeps `JAtZV2`: no `vTcbA v` word is written (`JVLay.nJS_v`: the written word is not `JW`).
  - **`JAtZV2.vcpuSpec`**: the spec VCPU-object update keeping the binding (`vs'.tcb = vs.tcb`) keeps `JAtZV2`
    (no premise).
  - **`JAtZV2.vcpuStep`**: both together, FL4's write of a non-link VCPU word paired with the spec update.

What is **not** proved: the binding steps themselves (FL4's write of a `TCB` word paired with a spec `tcb`
change, `associateVcpuTcb` / `vcpuDetach`): FL4's write of `vTcbA p` is a `JW` word, so neither gen 24's
`vcpuWr` nor `JAtZB.vcpuWrJ` covers it (`JAtZB` across that write needs `JExtV`'s binding update — gen 20's
`JExtV.bind`/`unbind` — together with a `JAtZB` frame for a `JW` write; not built). `VBind.set` is the relation
side of that step.

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZBVcpu
import Fl4Proofs.P3.XTopBuf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Ipc Fl4Proofs.P3.Endp

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

set_option maxHeartbeats 4000000 in
/-- **`XTopAt` across a spec VCPU-object update**, FL4's state kept (module docstring). -/
theorem XTopAt.vcpuSpec {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) {p : Fl4Spec.ObjRef} {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p = some (.archObj (.vcpu vs))) (vs' : Fl4Spec.VcpuState) :
    XTopAt (L := L) AR Z s a (Notif.updK σ p (.archObj (.vcpu vs'))) := by
  have F := arFr_vcpu hk vs'
  obtain ⟨⟨hS, hR, hPt, hPI, hCO⟩, ⟨hPl, ⟨hSt, hV, hM, hC, hI⟩, hFI, hD, hMO, hIA, hSA⟩, -, hE⟩ := hX
  have hS' : TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR s a
      (Notif.updK σ p (.archObj (.vcpu vs'))) :=
    TopSR.step0 (W := fun _ => False) hS (fun _ h => h.elim) (P1.WritesIn.refl _ _)
      (OStep.arch (Or.inr (Or.inr ⟨_, hk⟩)) _) rfl rfl
  have hkeep : ∀ q : Fl4Spec.ObjRef, σ.kheap q ≠ σ.kheap p →
      (Notif.updK σ p (.archObj (.vcpu vs'))).kheap q = σ.kheap q := by
    intro q hq
    have e : q ≠ p := fun e => hq (by rw [e])
    simp [Notif.updK, e]
  refine ⟨⟨hS', ?_, ?_, hPI, hCO⟩, ⟨hPl, ⟨?_, hV, hM, ⟨hC.cdt, hC.cdt_slot, hC.orig, hC.par_slot⟩, hI⟩,
    ⟨hFI.kt.sub F.ksub, hFI.fm⟩, hD, hMO, hIA, hSA.mono F.szKeep⟩,
    IpcRel.of hS'.1.2.2.1 hS'.1.2.1 (sched_sc hS'.1.1), hE.mono rfl F.szKeep⟩
  · refine hR.frame (fun _ _ => rfl) rfl fun q hq => ?_
    obtain ⟨f, hf, -⟩ := hR.pool q hq
    exact hkeep _ (by rw [hf, hk]; intro h; cases h)
  · refine hPt.frame (fun _ _ => rfl) fun q hq => ?_
    rcases hq with hq | hq | hq | hq
    · obtain ⟨g, hg, -⟩ := hPt.l4 q hq
      exact hkeep _ (by rw [hg, hk]; intro h; cases h)
    · obtain ⟨g, hg, -⟩ := hPt.l3 q hq
      exact hkeep _ (by rw [hg, hk]; intro h; cases h)
    · obtain ⟨g, hg, -⟩ := hPt.l2 q hq
      exact hkeep _ (by rw [hg, hk]; intro h; cases h)
    · obtain ⟨g, hg, -⟩ := hPt.l1 q hq
      exact hkeep _ (by rw [hg, hk]; intro h; cases h)
  · refine ⟨fun q r hq => ?_, fun t ht => ?_⟩
    · obtain ⟨cs, hq', h1, h2⟩ := hSt.cnode q r hq
      exact ⟨cs, (hkeep _ (by rw [hq', hk]; intro h; cases h)).trans hq', h1, h2⟩
    · obtain ⟨x, hx, h1⟩ := hSt.tcb t ht
      exact ⟨x, (hkeep _ (by rw [hx, hk]; intro h; cases h)).trans hx, h1⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The VM-epoch invariant with the binding relation** (module docstring). -/
structure JAtZV2 (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  zv : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ
  vb : VBind V σ (L.mem s)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **A spec VCPU-object step at `JAtZV`**, no premise (gen 26's `vcpuSpec` with `hX` from `XTopAt.vcpuSpec`). -/
theorem JAtZV.vcpuSpec' (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (vs' : Fl4Spec.VcpuState) :
    JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a (Notif.updK σ p.bv (.archObj (.vcpu vs'))) :=
  J.vcpuSpec hp hk vs' (J.base.xtop.vcpuSpec hk vs')

/-- At `V = ∅` a native step lifts (as `JAtZV.of_native`). -/
theorem JAtZV2.of_native {Z' : XSets} {H' : P1.Heap} {Cs' Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64}
    {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (J' : JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σ')
    (R' : RunVmB (L := L) Z'.th s') (Vl' : VList st ∅ Z'.th s') :
    JAtZV2 (L := L) arI ∅ ∅ AR Z' H' Cs' Ac' Lst' D' s' a' σ' :=
  ⟨JAtZV.of_native J' R' Vl', VBind.empty _ _⟩

/-- **A non-link VCPU-word write keeps `JAtZV2`** (module docstring). -/
theorem JAtZV2.vcpuWr (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p w : U64} (hp : p ∈ V)
    (hal : P1.Aligned w) (g1 : p.val ≤ w.val) (g2 : w.val < p.val + 32768)
    (hw : w.val ≠ p.val + 20480 ∧ w.val ≠ p.val + 20488 ∧ w.val ≠ p.val + 20496) (x : U64) :
    JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s w x) a σ := by
  have Ly := J.zv.base.jvLay J.zv.vm
  have hW : P1.WritesIn st s (L.wr s w x) (· = w) := P1.writesIn_wr hal
  have nJ := (Ly.nJS_v hp g1 g2 hw.1).1
  refine ⟨J.zv.vcpuWr hp hal g1 g2 hw x, J.vb.ofKheap rfl fun v hv => ?_⟩
  have hf := Ly.vfit v hv
  refine hW.mem_eq (by unfold P1.Aligned; rw [lay_vTcb_val hf.2]; omega) fun e => ?_
  exact nJ (Or.inr (Or.inr ⟨v, hv, e.symm⟩))

/-- **A spec VCPU-object update keeping the binding keeps `JAtZV2`** (no premise). -/
theorem JAtZV2.vcpuSpec (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (vs' : Fl4Spec.VcpuState)
    (ht : Fl4Spec.VcpuState.tcb vs' = Fl4Spec.VcpuState.tcb vs) :
    JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a (Notif.updK σ p.bv (.archObj (.vcpu vs'))) := by
  refine ⟨J.zv.vcpuSpec' hp hk vs', J.vb.set vs' (fun _ _ _ => rfl) ?_⟩
  obtain ⟨vs0, h1, h2⟩ := J.vb p hp
  rw [hk] at h1
  cases h1
  rw [ht]; exact h2

/-- **FL4's non-link VCPU-word write paired with the spec's VCPU-object update** keeps `JAtZV2`. -/
theorem JAtZV2.vcpuStep (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p w : U64} (hp : p ∈ V)
    (hal : P1.Aligned w) (g1 : p.val ≤ w.val) (g2 : w.val < p.val + 32768)
    (hw : w.val ≠ p.val + 20480 ∧ w.val ≠ p.val + 20488 ∧ w.val ≠ p.val + 20496) (x : U64)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (vs' : Fl4Spec.VcpuState)
    (ht : Fl4Spec.VcpuState.tcb vs' = Fl4Spec.VcpuState.tcb vs) :
    JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s w x) a (Notif.updK σ p.bv (.archObj (.vcpu vs'))) :=
  (J.vcpuWr hp hal g1 g2 hw x).vcpuSpec hp hk vs' ht

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Classical

/-- **`JAtZV2 ∅ ∅` at the boot witness `w1`** (no premise). -/
theorem jAtZV2_w1 (a : MachineState) :
    JAtZV2 (L := wL) warI ∅ ∅ wAR Zw1 Hw1 Csw C1 (fun _ => []) Dw w1 a σ1 :=
  ⟨jAtZV_w1 a, VBind.empty _ _⟩

end Fl4Proofs.P3.JBoot
