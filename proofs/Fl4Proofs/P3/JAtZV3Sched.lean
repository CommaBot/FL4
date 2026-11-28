/-
P3 (line mmuAD, gen 31): **the scheduler family's yield steps at `JAtZV3`**: `set_consumed` and
`complete_yield_to` from a VM-epoch state (gen 30's "Next" item 2).

* Copies over `JAtZB` (generator `scratch/mmu24_jatzb_gen.py setConsumedJ completeYieldJ`; the other 33
  dependencies are already in P3/JAtZBWr / JAtZBSched / JAtZBYield): `finW_keeps`, `finW_scOut`, `deadP_qk`,
  `finW_irq`, `kern_keep`, `tdkeep_of`, `finW_utc`, `cs_frameB` (since mmuAD gen 42b3 `cs_frameB`, `tdkeep_of` and `kern_keep` are the originals, generalised
  in place in P3/XTopJointStep, P3/JointAt, P3/DeadKeep), `vkeep_of`, `cs_frameI`, `reg_frameF`,
  `reg_frame`, `setConsumedJ`, `completeYieldJD`, `completeYieldJ`. Proofs verbatim, except: every post ends in
  `JAtZB`; `cs_frameB` loses its `hext : JExt` argument and `cs_frameI` its `J.ext` entry (`JAtZB` has no `ext`
  field; `JAtZB.cs_frameV` takes none); `kern_keep`'s `unfold nodeW` is qualified `Sched.nodeW` (gen-24 trap).
* **`JAtZB.reg_frameFZ`**, **`JAtZB.setConsumedJV`**: `reg_frameF` / `setConsumedJ` with the post at `Z` itself
  (the existential VSpace sets of the originals are always `Z.vs`), plus the `FinW` footprint and the spec step's
  `QKY` shape (both already `have`s in the proofs).
* **`zv_qky`**: a `QKY` spec step (SC consumed/yield fields, TCB registers/yield/fault) keeps every arch object,
  every object's size, makes no new `runningVM` thread and no new or changed VCPU object — `JAtZV3.ofBS`'s
  `hvk`/`hsz`/`hrv`/`hnv`. **`JAtZB.finW_nh`**: a `FinW` word is not the VCPU-list head word.
* **`JAtZV3.setConsumedJ`**, **`JAtZV3.completeYieldJ`**: `set_consumed p y true` and `complete_yield_to y` at
  `JAtZV3 V X` for any `V`, premises exactly `JAtZ.setConsumedJ`'s / `JAtZ.completeYieldJ`'s (the latter through
  `JAtZV3.setConsumedJ` and gen 30's `JAtZV3.cancelYieldJ`).

No named premise. No existing statement changed.

(mmuAD gen 42b17) Copies removed (the originals are now stated over `JAtZB` in place): P3/XTopJointFinW `finW_irq`,
`finW_keeps`, `finW_scOut`, `finW_utc`; P3/XTopJointRegFrame `deadP_qk`; P3/XTopJointStep `vkeep_of`.

(mmuAD gen 42b18) Removed (the originals are stated over `JAtZB` in place, the `JAtZ` names their corollaries with
`ext` rebuilt): P3/XTopJointStep `cs_frameI`; P3/XTopJointRegFrame `reg_frameF`, `reg_frame`; P3/XTopJointYield
`setConsumedJ`, `completeYieldJD`, `completeYieldJ`. `reg_frameFZ` and `setConsumedJV` moved to P3/XTopJointRegFrame /
P3/XTopJointYield as the in-place generalisations (statements unchanged).
-/
import Fl4Proofs.P3.JAtZV3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- **What a `QKY` spec step keeps of the VM epoch** (module docstring). -/
theorem zv_qky {σ σ' : Fl4Spec.State Unit} (h : Sched.QKY σ σ') :
    (∀ p ao, σ.kheap p = some (.archObj ao) → σ'.kheap p = σ.kheap p) ∧
    (∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko) ∧
    (∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM) ∧
    (∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
      σ.kheap p = some (.archObj (.vcpu vs))) := by
  refine ⟨fun p ao hp => ?_, fun o ko' ho => ?_, fun o x' ho hx => ?_, fun p vs hp => ?_⟩
  · rcases h.kh p with k | ⟨x, y, h1, -⟩ | ⟨z, w, n, h1, -⟩
    · exact k
    · rw [hp] at h1; cases h1
    · rw [hp] at h1; cases h1
  · rcases h.kh o with k | ⟨x, y, h1, h2, -⟩ | ⟨z, w, n, h1, h2, -⟩
    · exact ⟨ko', by rw [← k]; exact ho, rfl⟩
    · rw [ho] at h2; cases h2
      exact ⟨_, h1, rfl⟩
    · rw [ho] at h2; cases h2
      exact ⟨_, h1, rfl⟩
  · rcases h.kh o with k | ⟨x, y, h1, h2, h3⟩ | ⟨z, w, n, h1, h2, -⟩
    · exact ⟨x', by rw [← k]; exact ho, hx⟩
    · have e : (some (Fl4Spec.KernelObject.tcb x') : Option Fl4Spec.KernelObject) = some (.tcb y) :=
        ho.symm.trans h2
      simp only [Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at e
      subst e
      refine ⟨x, h1, ?_⟩
      rw [← hx, h3]
    · rw [ho] at h2; cases h2
  · rcases h.kh p with k | ⟨x, y, h1, h2, -⟩ | ⟨z, w, n, h1, h2, -⟩
    · rw [← k]; exact hp
    · rw [hp] at h2; cases h2
    · rw [hp] at h2; cases h2

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **A `FinW` word is not the VCPU-list head word** (module docstring). -/
theorem JAtZB.finW_nh (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64}
    (h : Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ b) : b ≠ P1.vHeadA st s := by
  rcases h with hk | ⟨y, hy, K, h1, h2, -, -, -, e⟩
  · exact J.tfoot_nh (Or.inl hk)
  · intro eb
    subst eb
    have hvh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
    have d := J.kern.hks y _ (J.zH.1 y hy) (fun _ h => by cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d
    omega

/-- **`set_consumed p y true` at `JAtZV3 V X`** (module docstring). -/
theorem JAtZV3.setConsumedJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {p y : U64} (hpC : p ∈ Z.C)
    (hy : y ∈ Z.T) :
    schedcontext.set_consumed st arI s a p y true ⦃ s1 => ∃ σ1,
      Fl4Spec.setConsumed (Z := Unit) p.bv y.bv σ = ({((), σ1)}, False) ∧ YKeep σ σ1 ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s1 a σ1 ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  refine WP.spec_mono (B.setConsumedJV hAT hmax htu hpC hy) fun s1 ⟨σ1, he, hyk, hA, hwF, B'⟩ => ⟨σ1, he, hyk, ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := zv_qky hA
  exact J.ofBS B' hwF (fun b hb => Ipc.FinW.oobj hS hb) (fun b hb => B.finW_nh hb)
    (B.vkeep_of hwF fun b hb => Ipc.FinW.nv hS hb)
    (fun u hu => by obtain ⟨vu, hvu⟩ := J.z2.zv.vm.spec u hu; exact h1 _ _ hvu) h2 h3 h4

/-- **`complete_yield_to y` at `JAtZV3 V X`** (module docstring; P3/XTopJointYield's `JAtZ.completeYieldJD`
proof with the `JAtZV3` steps). -/
theorem JAtZV3.completeYieldJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {y : U64} (hy : y ∈ Z.T) :
    schedcontext.complete_yield_to st arI s a y ⦃ r => ∃ σ',
      Fl4Spec.completeYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
  have B := J.z2.zv.base
  obtain ⟨Q, R0, hc, hs⟩ := B.xtop.fin.1.1.1.lists
  have hy0 : y ≠ 0#u64 := fun e => (hc.tcbs y hy).ne0 (by rw [e]; rfl)
  obtain ⟨xy, hky, eyt⟩ := B.yld.tcb y hy
  unfold schedcontext.complete_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  have hb2' : b = false := by rw [hb]; exact decide_eq_false hy0
  rw [hb2']
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.yield_to.spec as ⟨i, hi⟩
  subst hi
  by_cases hi0 : L.mem s (yieldA y) = 0#u64
  · have : (L.mem s (yieldA y) != 0#u64) = false := by simp [hi0]
    simp only [this, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, completeYieldTo_none hky (by rw [eyt, hi0, Notif.optRef_zero]), Ac, Lst, J⟩
  obtain ⟨p, hp⟩ : ∃ p, L.mem s (yieldA y) = p := ⟨_, rfl⟩
  rw [hp] at hi0 eyt ⊢
  have hb' : (p != 0#u64) = true := by simp [hi0]
  simp only [hb', ↓reduceIte]
  obtain ⟨hpC, -⟩ := B.yld.toSc y hy (by rw [hp]; exact hi0)
  rw [hp] at hpC
  refine WP.spec_bind (J.setConsumedJ hAT hmax htu hpC hy) ?_
  rintro s1 ⟨σ1, he1, hyk, J1⟩
  have hm1 : L.mem s1 (yieldA y) = p := by
    obtain ⟨x1, hk1, e1⟩ := J1.z2.zv.base.yld.tcb y hy
    obtain ⟨x1', hk1', e1'⟩ := hyk.1 _ xy hky
    rw [hk1] at hk1'; cases hk1'
    rw [eyt, Notif.optRef_ne hi0] at e1'
    rw [e1'] at e1
    exact P1.eq_of_bv (Notif.optRef_some e1.symm).2
  refine WP.spec_bind (J1.cancelYieldJ hy hm1 hi0) ?_
  rintro s2 ⟨σ2, he2, Ac2, Lst2, J2⟩
  refine (WP.spec_ok _).2 ⟨σ2, ?_, Ac2, Lst2, J2⟩
  rw [completeYieldTo_some hky (by rw [eyt, Notif.optRef_ne hi0]), nd_bind_one he1]
  exact he2

end

end

end

end Fl4Proofs.P3
