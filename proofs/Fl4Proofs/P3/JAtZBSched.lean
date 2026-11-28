/-
P3 (line mmuAD, gen 27): **the first native scheduler step from a VM-epoch state: `possible_switch_to` at
`JAtZV V X` for any `V`** (gen 24/25 goal 2), and the generic VM-epoch frame for native steps.

* Copies over `JAtZB` (generator `scratch/mmu24_jatzb_gen.py switchJ`; proofs verbatim): `sc_out_keep`,
  `deadP_sc_stepQm`, `ymd`, `deadP_sc_stepQ`, `kw_dbg`, `kw_dbgKeep`, `tfoot_vkeep`, `vsW`, `sc_frame`, `sc_buf`,
  `sc_apart`, `sc_jpl`, `dxKeep`, `dxk`, `tfoot_td`, `sc_jcov`, `sc_kern`, `sc_utc`, `switchJ` (the copies
  already in P3/JAtZBWr — `tcbs_eq`, `deadY_tcb`, `liveX`, `zDX`, `idleW_keep`, `tcbZ` — reused). The only
  change: `sc_frame` ends in `JAtZB` and drops its `ext` entry (`J.ext.ss hSS (J.tfoot_vkeep hw)`), the one
  `J.ext` read in the chain. **`JAtZB.switchJ`** is P3/XTopJointSwitch's `JAtZ.switchJ` over `JAtZB`.
* **`JAtZV.oobj_v`**: every word of the other subsystems' objects (`OObj`: core `Z.c`'s node, the kernel-state
  block, TCB words past 256, endpoints, replies, notifications, `Z.C`'s SCs, IPC-buffer words) lies outside every
  VCPU of `V` (`HeapOK.disj` against `JVm.heap`'s `.other 15`, `JVm.ks`, `JKern.cpuCs`/`csLt`, `JCarry.bufPg` +
  `JVm.sep`).
* **`JAtZV.ofB`** (the footprint fact of gen 24 item 2, as one lemma): from `JAtZV V X` at `(s, σ)`, a post-state
  `JAtZB` at `(s', σ')` with the same sets, FL4's writes in `OObj` words other than the VCPU-list head,
  every TCB's VCPU word kept (`VKeep`) and the spec heap unchanged give `JAtZV V X` at `(s', σ')`: slots by
  `slotsSame_of`, the VCPUs' `TCB` and list words by `oobj_v`, `RunVmB` through both states' TCB relations
  (state word = `tsCode` of the same spec state), `JVm` by the unchanged heap.
* **`JAtZV.switchJ`**: `possible_switch_to` of a schedulable thread, neither current nor idle, keeps
  `JAtZV V X` (no premise beyond `JAtZ.switchJ`'s own): `JAtZB.switchJ` + `possible_switch_to_refines`
  (heap unchanged) + `possible_switch_to_sfoot` (`SFoot` ⊆ `TFoot`: `tfoot_oobj`, `VKeep.of_tfoot`; no
  kernel-state word, `SFoot.range` + `JKern.hks`), the outcomes identified by the spec's singleton result.

No named premise. No existing statement changed.

(mmuAD gen 42b17) Copies removed (the originals are now stated over `JAtZB` in place): P3/JointAt `dxKeep`, `dxk`,
`vsW`; P3/ScDeadStep `sc_out_keep`, `ymd`; P3/ScJointFrame `tfoot_td`, `tfoot_vkeep`; P3/ScJointRest `sc_apart`,
`sc_buf`, `sc_jcov`, `sc_jpl`, `sc_utc`; P3/XTopJointFinW `kw_dbg`, `kw_dbgKeep`.

(mmuAD gen 42b17, second pass) Copies removed (originals generalised in place): P3/ScDeadStep `deadP_sc_stepQ`,
`deadP_sc_stepQm`; P3/ScJointRest `sc_kern`.

(mmuAD gen 42b18) Removed (the originals are stated over `JAtZB` in place, the `JAtZ` names their corollaries with
`ext` rebuilt): P3/ScJointFrame `sc_frame`; P3/XTopJointSwitch `switchJ`.
-/
import Fl4Proofs.P3.JAtZBWr
import Fl4Proofs.P3.XTopJointSwitch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Sched

/-- **The other subsystems' words lie outside every VCPU** (module docstring). -/
theorem JAtZV.oobj_v (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {v : U64} (hv : v ∈ V) {b : U64}
    (hb : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) : b.val < v.val ∨ v.val + 32768 ≤ b.val := by
  have B := J.base
  have hvH := J.vm.heap v hv
  have dH : ∀ p k, H p = some k → k ≠ .other 15 → p.val + 2 ^ k.bits ≤ v.val ∨ v.val + 32768 ≤ p.val := by
    intro p k hp hk
    have hne : p ≠ v := fun e => by subst e; rw [hvH] at hp; cases hp; exact hk rfl
    rcases B.kern.heap.disj p k v _ hp hvH hne with h | h
    · exact Or.inl h
    · simp only [P1.HKind.bits, Nat.reducePow] at h; exact Or.inr h
  have hks := J.vm.ks v hv
  rcases hb with ⟨g1, g2⟩ | ⟨g1, g2, -⟩ | ⟨t, ht, g1, g2⟩ | ⟨e, he, g1, g2⟩ | ⟨r, hr, g1, g2⟩ | ⟨n, hn, g1, g2⟩ |
      ⟨sc, hsc, x, n, hk, hso⟩ | ⟨wp, hwp, g1, g2⟩
  · obtain ⟨Q, R0, hcq, -⟩ := B.xtop.fin.1.1.1.lists
    have hcC : Z.c ∈ Cs := hcq.cur ▸ B.kern.cpuCs
    have hc64 := B.kern.csLt Z.c hcC
    have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
    rw [hnb] at g1 g2
    omega
  · omega
  · have d := dH t _ (B.zH.1 t ht) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · have d := dH e _ (B.zH.2.1 e he) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · have d := dH r _ (B.zH.2.2.1 r hr) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · have d := dH n _ (B.zH.2.2.2 n hn) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · obtain ⟨Tr, Cq, hJ⟩ := B.jpl
    have hH := (hJ.sc sc x n (B.c0 sc hsc) hk).2
    have d := dH sc _ hH (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d
    unfold Sched.ScObj at hso
    omega
  · obtain ⟨q, vms, hq, q1, q2⟩ := B.carry.bufPg wp hwp
    obtain ⟨y, hy⟩ := J.vm.spec v hv
    have hne : q ≠ v.bv := fun e' => by rw [e', hy] at hq; cases hq
    have eb : Fl4Spec.objBits (.archObj (.dataPage false vms)) = Fl4Spec.pageBitsForSize vms := by
      simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]
    rcases J.vm.sep v hv q _ hq hne with e1 | e1
    · rw [eb] at e1; omega
    · omega

/-- **The VM-epoch frame of a native step** (module docstring). -/
theorem JAtZV.ofB (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s') (hke : σ'.kheap = σ.kheap) :
    JAtZV (L := L) arI V X AR Z H Cs Ac' Lst' D' s' a' σ' := by
  have B := J.base
  have Ly := B.jvLay J.vm
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') := B.xtop.slotsSame_of hw hO
  have nV : ∀ u ∈ V, ∀ b, W b → b.val < u.val ∨ u.val + 32768 ≤ b.val := fun u hu b hb => J.oobj_v hu (hO b hb)
  have kV : ∀ u ∈ V, L.mem s' (vTcbA u) = L.mem s (vTcbA u) := by
    intro u hu
    have hf := Ly.vfit u hu
    have e := lay_vTcb_val hf.2
    exact hw.mem_eq (by unfold P1.Aligned; rw [e]; omega) fun hb => by rcases nV u hu _ hb with h | h <;> omega
  have E' : JExtV (L := L) V X Z.th s' := J.extv.of_eq (fun y hy => hSS.capV hy) hv kV
  have R' : RunVmB (L := L) Z.th s' := by
    intro t ht h8
    rw [hv t ht]
    refine J.rvm t ht ?_
    obtain ⟨x, hk, -⟩ := B'.xtop.rel.2.1.1.tcb t ht
    have w' := (B'.xtop.fin.1.1.2.2.1.at_tcb (B'.thT t ht) hk).st
    rw [hke] at hk
    have w0 := (B.xtop.fin.1.1.2.2.1.at_tcb (B.thT t ht) hk).st
    rw [Sched.stA_tStA] at h8 ⊢
    apply UScalar.eq_of_val_eq
    rw [w0, ← w', h8]
  have Jv' : JVm (L := L) V H s' σ' :=
    ⟨fun u hu => by rw [hke]; exact J.vm.spec u hu, J.vm.heap, fun u hu => by rw [hw.1]; exact J.vm.ks u hu,
      fun u hu o ko ho hne => J.vm.sep u hu o ko (by rw [hke] at ho; exact ho) hne⟩
  have Vl' : VList st V Z.th s' := J.vl.writes hw fun b hb => by
    refine ⟨J.vl.lw_al Ly.vfit hb, fun hW => ?_⟩
    rcases hb with rfl | ⟨u, hu, rfl | rfl⟩
    · exact hh _ hW rfl
    · have := lay_next_val (Ly.vfit u hu).2
      rcases nV u hu _ hW with h | h <;> omega
    · have := lay_prev_val (Ly.vfit u hu).2
      rcases nV u hu _ hW with h | h <;> omega
  exact ⟨B', E', R', Jv', Vl'⟩

set_option maxHeartbeats 4000000 in
/-- **`possible_switch_to` at `JAtZV V X`** (module docstring). -/
theorem JAtZV.switchJ (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (hti : t.bv ≠ σ.idleThread) (htc : t.bv ≠ σ.curThread) (hs : Fl4Spec.schedulable t.bv σ = true) :
    sched.possible_switch_to st s t ⦃ s' => ∃ σ', Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZV (L := L) arI V X AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
  have B := J.base
  have hS := B.xtop.fin.1.1.1
  have hR := B.xtop.fin.1.1.2.2.1
  refine WP.spec_mono (WP.spec_and (WP.spec_and (B.switchJ ht hti htc hs)
    (possible_switch_to_refines s σ hR hS B.inv.actReady t ht)) (possible_switch_to_sfoot hR hS B.inv.actReady ht)) ?_
  rintro s' ⟨⟨⟨σ1, he1, Lst', B'⟩, ⟨σ2, he2, hke, -, -⟩⟩, hw⟩
  have e12 : σ2 = σ1 := by
    rw [he1] at he2
    have h := congrArg Prod.fst he2
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at h
    exact h.symm
  subst e12
  have hwT : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) :=
    WritesIn.tfoot_of_kfoot (WritesIn.kfoot_of_sfoot hw)
  have hv : VKeep (L := L) Z.th s s' := VKeep.of_tfoot hS B.thT hwT
  have hvh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val B.kern.ksbFit
  have hh : ∀ b, SFoot st Z.T Z.c s b → b ≠ P1.vHeadA st s := by
    intro b hb e
    subst e
    rcases SFoot.range hS.placed.tcb hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩
    · have d := B.kern.hks y _ (B.zH.1 y hy) (fun _ h => by cases h)
      simp only [P1.HKind.bits, Nat.reducePow] at d
      omega
    · have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
      omega
  exact ⟨σ2, he1, Lst', J.ofB B' hw (fun b h => tfoot_oobj hS (Or.inl (Or.inl h))) hh hv hke⟩

end

end

end

end Fl4Proofs.P3
