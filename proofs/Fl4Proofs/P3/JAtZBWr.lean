/-
P3 (line mmuAD, gen 24): **a write of a VCPU word keeps `JAtZV V X` for any `V`** — the first `JAtZB`
preservation proof from a VM-epoch state (gen 23 plan item 2).

`JAtZ.vcpuWrJ` (P3/VcpuWrJ, over `JAtZ.frameWrJ` of P3/XTopJointReadFpu and the `cs_frame` family of
P3/XTopJointStep) reads `JAtZ.ext` only to rebuild `ext` at the end (`J.ext.step hvT hv` in `JAtZ.cs_frame`,
the `VKeep` argument of `cs_frameK`). This module states `frameWrJ` and `vcpuWrJ` over `JAtZB`. Since mmuAD gen
42b3 the chain they use is no longer copied here: `vsFr_other`, `tcbs_eq`, `deadY_tcb`, `deadP_keep`,
`idleW_keep`, `kern_keepA`, `notDbg'`, `notDbg`, `tcbZ`, `tdA_val'`, `jcov_keep`, `cs_frameVD`, `cs_frameV`, `bfK`,
`cs_frame`, `liveX`, `zDX`, `cs_frameK`, `vsShr`, `vsSS`, `JCs.sameB` are the originals generalised in place to
`JAtZB` (P3/JointAt, P3/ScJointFrame, P3/ScDeadStep, P3/DeadKeep, P3/ScJointRest, P3/LiveFrame, P3/XTopJointStep,
P3/XTopJointFinVs), with the `JAtZ` names their corollaries via `JAtZ.toB` (the `JExt` argument `hext` of
`cs_frameVD` / `cs_frameV` and the `VKeep` argument `hv` of `cs_frame` / `cs_frameK` only on the `JAtZ` side).

**`JAtZV.vcpuWr`**: from `J : JAtZV V X …`, writing any aligned word `w` of a VCPU `p ∈ V` other than its
`TCB` (offset 20480), `NEXT` (20488) and `PREV` (20496) words keeps `JAtZV V X` with σ unchanged (guest-state /
VMCS-shadow writes, `vcpu.decode`'s register writes, `vcpu.enter`'s VMX/SVM words). All of `vcpuWrJ`'s side
facts come from `JVm` (`spec`, `heap`, `ks`) and `JCarry.bufPg` + `JVm.sep` (no IPC-buffer word in the VCPU);
`JExtV` by `JExtV.of_writes` + `JVLay.nJS_v`; `RunVmB` as in `JAtZV.vcpuWr0`; `VList` by `VList.writes` (the list
words of other VCPUs by `JVLay.vv`, the head word by `JVm.ks`); `JVm` (it reads only `ksb`).

No named premise (the three excluded offsets are the statement's scope: those words are written only by
`vcpu.init` / `finalise` / SetTCB / detach, proved separately in gens 20–23). No existing statement changed.

(mmuAD gen 42b18) Removed (the originals are stated over `JAtZB` in place, the `JAtZ` names their corollaries with
`ext` rebuilt): P3/XTopJointReadFpu `frameWrJ`; P3/VcpuWrJ `vcpuWrJ`.
-/
import Fl4Proofs.P3.JAtZBLay
import Fl4Proofs.P3.VcpuWrJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

section
open fl4_core Classical

set_option maxHeartbeats 4000000 in
/-- **A VCPU word written at `JAtZV V X`** (module docstring; σ unchanged). -/
theorem JAtZV.vcpuWr (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p w : U64} (hp : p ∈ V)
    (hal : P1.Aligned w) (g1 : p.val ≤ w.val) (g2 : w.val < p.val + 32768)
    (hw : w.val ≠ p.val + 20480 ∧ w.val ≠ p.val + 20488 ∧ w.val ≠ p.val + 20496) (x : U64) :
    JAtZV (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s w x) a σ := by
  have B := J.base
  have Ly := B.jvLay J.vm
  have hW : P1.WritesIn st s (L.wr s w x) (· = w) := P1.writesIn_wr hal
  have hf := Ly.vfit p hp
  -- no IPC-buffer word lies in the VCPU
  have hnB : ∀ wp ∈ Z.B, wp.1 ≠ w := by
    intro wp hwp e
    obtain ⟨q, vms, hq, q1, q2⟩ := B.carry.bufPg wp hwp
    obtain ⟨y, hy⟩ := J.vm.spec p hp
    have hne : q ≠ p.bv := fun e' => by rw [e', hy] at hq; cases hq
    have eb : Fl4Spec.objBits (.archObj (.dataPage false vms)) = Fl4Spec.pageBitsForSize vms := by
      simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]
    have ev : wp.1.val = w.val := by rw [e]
    rcases J.vm.sep p hp q _ hq hne with e1 | e1
    · rw [eb] at e1; omega
    · omega
  have B' := B.vcpuWrJ (J.vm.spec p hp) (J.vm.heap p hp) (J.vm.ks p hp) hal g1 g2 hnB x
  -- the extension
  have E' : JExtV (L := L) V X Z.th (L.wr s w x) :=
    J.extv.of_writes (B.jwPl J.vm) hW fun b hb => by subst hb; exact (Ly.nJS_v hp g1 g2 hw.1).1
  have hHO := B.kern.heap
  have apT : ∀ t, Z.th t = some .tcb → t.val + 4096 ≤ p.val ∨ p.val + 32768 ≤ t.val := by
    intro t ht
    have htH : H t = some .tcb := B.zH.1 t (B.thT t ht)
    have hne : t ≠ p := fun e => by rw [e, J.vm.heap p hp] at htH; cases htH
    have d := hHO.disj t _ p _ htH (J.vm.heap p hp) hne
    simp only [P1.HKind.bits, Nat.reducePow] at d
    exact d
  have kT : ∀ t, Z.th t = some .tcb → L.mem (L.wr s w x) (P1.stA t) = L.mem s (P1.stA t) ∧
      L.mem (L.wr s w x) (tVcpuA t) = L.mem s (tVcpuA t) := by
    intro t ht
    have hta := B.ip.e.tcb t (B.thT t ht)
    have e1 := lay_stA_val hta
    have e2 := lay_tVcpu_val hta
    have ha := hta.align
    have d := apT t ht
    refine ⟨hW.mem_eq (by unfold P1.Aligned; omega) fun e => ?_, hW.mem_eq (by unfold P1.Aligned; omega) fun e => ?_⟩
    · have := congrArg UScalar.val e; omega
    · have := congrArg UScalar.val e; omega
  have R' : RunVmB (L := L) Z.th (L.wr s w x) := by
    intro t ht h8
    rw [(kT t ht).2]
    exact J.rvm t ht (by rw [← (kT t ht).1]; exact h8)
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val B.kern.ksbFit
  have Vl' : VList st V Z.th (L.wr s w x) := J.vl.writes hW fun b hb => by
    refine ⟨J.vl.lw_al Ly.vfit hb, fun e => ?_⟩
    have ew := congrArg UScalar.val e
    rcases hb with rfl | ⟨u, hu, rfl | rfl⟩
    · rcases J.vm.ks p hp with h | h <;> omega
    · rw [lay_next_val (Ly.vfit u hu).2] at ew
      by_cases hup : u = p
      · subst hup; exact hw.2.1 ew.symm
      · rcases Ly.vv u hu p hp hup with h | h <;> omega
    · rw [lay_prev_val (Ly.vfit u hu).2] at ew
      by_cases hup : u = p
      · subst hup; exact hw.2.2 ew.symm
      · rcases Ly.vv u hu p hp hup with h | h <;> omega
  have Jv' : JVm (L := L) V H (L.wr s w x) σ :=
    ⟨J.vm.spec, J.vm.heap, fun v hv => by rw [hW.1]; exact J.vm.ks v hv, J.vm.sep⟩
  exact ⟨B', E', R', Jv', Vl'⟩

end

end

end

end Fl4Proofs.P3
