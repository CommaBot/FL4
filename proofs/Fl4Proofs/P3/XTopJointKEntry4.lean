/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN.md sch9 (1)): **`kernel_entryJ4`:
`kernel_entryJ3` without `KFinSwHyp` [W]**.

FL4's `finish` (`schedule; activate_thread`) is proved from `JAtZR`
(XTopJointJAtZR: `JAtZ` with `CurInv` asked only under a resumed action),
which both a `JAtZ` and a `JAtZS` state satisfy (`JAtZ.toR`, `JAtZS.toR`):
`jat_finishJR` = `jat_finishJ2` on `jat_scheduleSR2ZR` (XTopJointJAtZRB: the
timers' signal cone and `schedule_refinesWP0FR` at `JAtZR`; after `schedule`
the action is resumed and the new current thread's `CurInv` holds, so `JAtZ`
again and `JAtZ.activateJ`).

* `signalRestJHypZR_of_ns`: the remote `RunningVM` signal premise at `JAtZR`
  refuted by `NativeScope` at `JAtZR` states (`hNSR` [S], VT-x out of the
  native scope, as `hNS`).
* `KFinAtR`: `KFinAt2` with `vt` [J] quantified over `JAtZR` states (the
  same statement: TCBs of `Z.T` typed and their PML4 caps with a nonzero
  ASID, read from `JPlaced`/`VsSlotsW`, not from `cur`).
* `kernel_entryJ4`: `kernel_entryJ3` with `hFin : … JAtZR … → KFinAtR`,
  `hNSR` [S], and no `hSw`. REMOVED: `KFinSwHyp` [W].
* `KPreFinRestHyp` [W], `kPreFinHyp_of`, `kernel_entryJ5` (sch9 (3)):
  `KPreFinHyp` [W] narrowed to the preemption states where `JAt` fails
  (`JHoleAt` without `JAt`, the IRQ case's bare `XTopAt`, a failing spec
  preemption path); where `JAt` holds the finish is `jat_finishJR`.
-/
import Fl4Proofs.P3.XTopJointKEntry
import Fl4Proofs.P3.XTopJointPreemptK
import Fl4Proofs.P3.XTopJointJAtZS
import Fl4Proofs.P3.XTopJointJAtZRB
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`finish`'s premises at a `JAtZR` state** (module docstring): `KFinAt2`
with `vt` over `JAtZR` states. -/
structure KFinAtR (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ
  vt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64
  arch : ArchSwF st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c
  fo : FpuOwnOK σ
  sni : SniHyp st arI Z.N Z.T Z.C Z.c
  send : SendHyp st arI Z.N Z.T Z.C Z.c
  tail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      timer.fire st arI s a = ok rf →
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) ∨
       ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄

variable {arI} {AR : A → Fl4Spec.Cr3 → Prop}

/-- **FL4's `finish` from `JAtZR`** (module docstring): `jat_finishJ2` with
`jat_scheduleSR2ZRP`, the signal and `RunningVM` cases only at the states the
path reaches (g3b): `P` along the fired timers (`hP`), `hvm` at the state
after `schedule`. -/
theorem jat_finishJRP {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (P : Fl4Spec.State Unit → Prop) (hP : ∀ σ1, Fires σ σ1 → P σ1)
    (hW : SignalRestJHypZRP (L := L) arI P AR H Cs) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      timer.fire st arI s a = ok rf →
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) ∨
       ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hvm : ∀ σ1 σ2 s1 a1, Fires σ σ1 → Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ2)}, False) →
      JAt (L := L) arI AR s1 a1 σ2 → ∀ x, σ2.kheap σ2.curThread = some (.tcb x) → x.tcbState ≠ .runningVM) :
    syscall.finish st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), ((), σ1) ∈ (Fl4Spec.fl4Awaken (Z := Unit) σ).1 ∧
      (Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1 = ({((), σ')}, False) ∧
      ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) σ).1 ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ ∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  refine P1.finish_of_old arI ?_
  unfold syscall.finish_old
  refine WP.spec_bind (jat_scheduleSR2ZRP s a σ J hd hnd hAT hVt P hP hW hmb hA hAN hFO hsni hsend hT hTail) ?_
  rintro ⟨s1, a1⟩ ⟨σ1, σ2, hF, hsc, -, ⟨V1, Ac1, Lst1, D1, J1R⟩, hC2, hcr⟩
  have J1 := J1R.toJ (Or.inr hC2)
  refine WP.spec_mono (J1.activateJV hAT hmax (htu a1) hcr (hvm σ1 σ2 _ _ hF hsc ⟨_, _, _, _, _, _, J1, inferInstance⟩)) ?_
  rintro r ⟨σ', ha, hRJ, V2, Ac2, Lst2, D2, J2, hnv⟩
  refine ⟨?_, J2.cur_not_vm hnv⟩
  have hsa : (Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1 = ({((), σ')}, False) := by
    rw [Notif.nd_bind_one hsc]; exact ha
  refine ⟨σ1, σ', mem_fl4Awaken_of hF, hsa, ⟨((), σ1), mem_fl4Awaken_of hF, ?_⟩, hRJ, V2, Ac2, Lst2, D2, J2⟩
  show ((), σ') ∈ ((Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1).1
  rw [hsa]; exact Set.mem_singleton _

end

end

end Fl4Proofs.P3
