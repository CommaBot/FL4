/-
P3 (line mmuAD, gen 23): **the VM-epoch joint invariant `JAtZV`** (gen 22's "Goal 4" list, first part).

* **`JAtZB`** (defined in P3/JointAt since mmuAD gen 42b3, with `JAtZ.toB` / `JAtZB.toJAtZ`): `JAtZ` (P3/JointAt) with its `ext : JExt` field dropped — the 50 other fields, statements copied
  verbatim (generated from P3/JointAt's structure). `JAtZ.toB`, `JAtZB.toJAtZ` (with a `JExt`).
* **`JAtZV V X …`**: `base : JAtZB`, `extv : JExtV V X Z.th s`, `rvm : RunVmB Z.th s`, `vm : JVm V H s σ`,
  `vl : VList st V Z.th s`. `JAtZV.toJAtZ`: at `V = X = ∅` it gives `JAtZ` back (`JExtV.toJExt`).
* **`JAtZ.toV`**: `JAtZ` ⇒ `JAtZV ∅ ∅` given `R : RunVmB` and the empty list (head word 0 + its placement). Neither
  is a `JAtZ` field: natively `RunVmB` says no TCB is `TS_RUNNING_VM`, which is P3's `NativeScope` (an [S], the
  native IPC lemmas' named premise) — **`JAtZ.rvm_of_ns`** derives `RunVmB` from it; the head word's value and
  placement are not `JAtZ` facts (no field reads `VCPU_HEAD`), so `JAtZ.toV` takes them as `h0` / `hd` [J].
* Boot: **`JBoot.jAtZV_w1`** — `JAtZV ∅ ∅` at the richer boot witness `w1` (`jAtZ_w1`, `w1_rvm`, `w1_vhead0`,
  `w1_vhd`), no premise.
* Preservation, representative steps:
  - **`JAtZV.of_native`**: at `V = ∅` every native step theorem `JAtZ → JAtZ` lifts, given the step keeps
    `RunVmB` and the list words (`VList.writes`);
  - **`JAtZV.vcpuWr0`**: a write of a VCPU object word (`JAtZ.vcpuWrJ`'s premises) keeps `JAtZV ∅ ∅` (no premise
    beyond `vcpuWrJ`'s: `RunVmB` and `VList` frames derived from the heap separation and `JVm`-style `hks`);
  - **`JAtZV.mk'`**: for `V ≠ ∅` the decomposition: a step's `JAtZB` at the post-state plus the four extension
    parts (each with its proved per-step lemma, gens 19–23) give `JAtZV`. What is **not** proved: `JAtZB`
    preservation for any step from a `JAtZV` state with `V ≠ ∅`; every existing preservation proof consumes
    `JAtZ.ext` (`JExt`), false once a VCPU cap exists, and `xtop.rel` relates FL4 to the *ported* spec
    (`SInvA.ns` / `NativeScopeS` false while a guest runs).

No [P] / [W] / [S] premise of the structure; `JAtZ.rvm_of_ns`'s `hN` is the existing [S] `NativeScope`; `JAtZ.toV`'s
`h0` / `hd` [J]. No existing statement changed. No P2 [S] discharge is claimed: `JAtZV` reachability over VM steps
is open.
-/
import Fl4Proofs.P3.JExtVListSteps
import Fl4Proofs.P3.JBoot1JAt
import Fl4Proofs.P3.VcpuWrJ
import Fl4Proofs.P3.JCurRunR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The VM-epoch joint invariant** (module docstring). -/
structure JAtZV (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  base : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ
  extv : JExtV (L := L) V X Z.th s
  rvm : RunVmB (L := L) Z.th s
  vm : JVm (L := L) V H s σ
  vl : VList st V Z.th s

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- At `V = X = ∅`, `JAtZV` gives `JAtZ`. -/
theorem JAtZV.toJAtZ (J : JAtZV (L := L) arI ∅ ∅ AR Z H Cs Ac Lst D s a σ) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ :=
  J.base.toJAtZ J.extv.toJExt

/-- **`JAtZ` ⇒ `JAtZV ∅ ∅`** (module docstring; `R` and the empty list `h0` / `hd` [J]). -/
theorem JAtZ.toV (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (R : RunVmB (L := L) Z.th s)
    (h0 : L.mem s (P1.vHeadA st s) = 0#u64)
    (hd : P1.Aligned (P1.vHeadA st s) ∧ ¬ JW ∅ Z.th (P1.vHeadA st s) ∧ ¬ SW Z.th (P1.vHeadA st s)) :
    JAtZV (L := L) arI ∅ ∅ AR Z H Cs Ac Lst D s a σ :=
  ⟨J.toB, J.extV, R, JVm.empty, VList.empty h0 hd⟩

/-- **At `V = ∅` a native step lifts** (module docstring). -/
theorem JAtZV.of_native {Z' : XSets} {H' : P1.Heap} {Cs' Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64}
    {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (J' : JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σ')
    (R' : RunVmB (L := L) Z'.th s') (Vl' : VList st ∅ Z'.th s') :
    JAtZV (L := L) arI ∅ ∅ AR Z' H' Cs' Ac' Lst' D' s' a' σ' :=
  ⟨J'.toB, J'.extV, R', JVm.empty, Vl'⟩

/-- **The decomposition** for any `V` (module docstring): the post-state's `JAtZB` and the extension's parts. -/
theorem JAtZV.mk' (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (E : JExtV (L := L) V X Z.th s)
    (R : RunVmB (L := L) Z.th s) (Jv : JVm (L := L) V H s σ) (Vl : VList st V Z.th s) :
    JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ := ⟨B, E, R, Jv, Vl⟩

/-- **`RunVmB` from `NativeScope`** (no spec thread `runningVM`, the [S]): every typed-heap TCB's state word is
the `tsCode` of its spec state, never 8. -/
theorem JAtZ.rvm_of_ns (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hN : NativeScope σ) :
    RunVmB (L := L) Z.th s := by
  intro t ht h8
  exfalso
  obtain ⟨x, hk, -⟩ := J.xtop.rel.2.1.1.tcb t ht
  have hw := (J.xtop.fin.1.1.2.2.1.at_tcb (J.thT t ht) hk).st
  have hvm := hN _ _ hk
  rw [Sched.stA_tStA] at h8
  rw [h8] at hw
  cases hx : x.tcbState <;> rw [hx] at hw hvm <;> simp_all [tsCode]

set_option maxHeartbeats 4000000 in
/-- **A VCPU word written at `JAtZV ∅ ∅`** (`JAtZ.vcpuWrJ`; module docstring). -/
theorem JAtZV.vcpuWr0 (J : JAtZV (L := L) arI ∅ ∅ AR Z H Cs Ac Lst D s a σ) {p w : U64}
    (hσ : ∃ x, σ.kheap p.bv = some (.archObj (.vcpu x))) (hH : H p = some (.other 15))
    (hks : p.val + 32768 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ p.val)
    (hal : P1.Aligned w) (g1 : p.val ≤ w.val) (g2 : w.val < p.val + 32768)
    (hnB : ∀ wp ∈ Z.B, wp.1 ≠ w) (x : U64) :
    JAtZV (L := L) arI ∅ ∅ AR Z H Cs Ac Lst D (L.wr s w x) a σ := by
  have J0 := J.toJAtZ
  have J1 := J0.vcpuWrJ hσ hH hks hal g1 g2 hnB x
  have hW : P1.WritesIn st s (L.wr s w x) (· = w) := P1.writesIn_wr hal
  have hHO := J0.kern.heap
  have apT : ∀ t, Z.th t = some .tcb → t.val + 4096 ≤ p.val ∨ p.val + 32768 ≤ t.val := by
    intro t ht
    have htH : H t = some .tcb := J0.zH.1 t (J0.thT t ht)
    have hne : t ≠ p := fun e => by rw [e, hH] at htH; cases htH
    have d := hHO.disj t _ p _ htH hH hne
    simp only [P1.HKind.bits, Nat.reducePow] at d
    exact d
  have kT : ∀ t, Z.th t = some .tcb → L.mem (L.wr s w x) (P1.stA t) = L.mem s (P1.stA t) ∧
      L.mem (L.wr s w x) (tVcpuA t) = L.mem s (tVcpuA t) := by
    intro t ht
    have hta := J0.ip.e.tcb t (J0.thT t ht)
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
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J0.kern.ksbFit
  have Vl' : VList st ∅ Z.th (L.wr s w x) := J.vl.writes hW fun b hb => by
    rcases hb with rfl | ⟨w', hw', -⟩
    · exact ⟨J.vl.hd.1, fun e => by have := congrArg UScalar.val e; omega⟩
    · exact hw'.elim
  exact ⟨J1.toB, J1.extV, R', JVm.empty, Vl'⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Classical

theorem w1_vhead_val : (P1.vHeadA wst w1).val = 18446744071562133584 := by
  unfold P1.vHeadA
  rw [ksb_w1, vHead_val (by rw [fkb_val]; norm_num), fkb_val]

/-- The VCPU list is empty at `w1`. -/
theorem w1_vhead0 : wL.mem w1 (P1.vHeadA wst w1) = 0#u64 := by
  rw [mem1_al w1_vhead_val (by norm_num)]; img1z

/-- The head word's placement at `w1`: in no slot, no TCB VCPU / state word (`thW1`'s objects off `fkb + 80`). -/
theorem w1_vhd (a : MachineState) :
    P1.Aligned (P1.vHeadA wst w1) ∧ ¬ JW ∅ thW1 (P1.vHeadA wst w1) ∧ ¬ SW thW1 (P1.vHeadA wst w1) := by
  have hv := w1_vhead_val
  have Ly := (jAtZ_w1 a).jvLay (V := ∅) JVm.empty
  refine ⟨by unfold P1.Aligned; omega, Ly.nJS (fun p k hp g1 g2 => ?_) (fun w hw => hw.elim)⟩
  exfalso
  rw [hv] at g1 g2
  thc1 hp <;> simp only [objSize, Nat.pow_zero, Nat.mul_one, Nat.pow_one] at g2 <;> omega

/-- **`JAtZV ∅ ∅` at the boot witness `w1`** (no premise). -/
theorem jAtZV_w1 (a : MachineState) :
    JAtZV (L := wL) warI ∅ ∅ wAR Zw1 Hw1 Csw C1 (fun _ => []) Dw w1 a σ1 :=
  (jAtZ_w1 a).toV w1_rvm w1_vhead0 (w1_vhd a)

end Fl4Proofs.P3.JBoot
