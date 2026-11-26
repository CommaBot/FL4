/-
P3 (line mmuAD, gen 34): **what `vcpu::report` leaves of the binding words** — the last two conjuncts of
`ReportJ3` (P3/JAtZV3Report): the thread's state word is no longer 8 (`TS_RUNNING_VM`) and no `JW` word (slot
words, TCB VCPU words, VCPU `TCB` words) is written.

* **`JAtZV3.reportFoot`**: P1's generic `vcpu.report.gen` (P1/VcpuReport) with the predicate "written only outside
  `JW`": the message registers and the three registers are `RepW` words (P3/JExtVSteps' `set_mr_w`,
  `P1.obj.Tcb.set_reg.wrS`), outside `JW` by `DetPl.rep`; `PENDING` of a VCPU of `V` (the TCB's VCPU word is nonzero
  only for a VCPU of `V`, `JExtV.bnd`) by `DetPl.vc`; `set_thread_state Running` writes the state word and
  `SCHED_ACTION` (`sts_w`), outside `JW` by `JWPl.swjw` / `DetAtB.nd`; the IPC buffer looked up at the start is
  `BufOK` by `DetAtB.buf`. `DetPl` / `DetAtB` at a `JAtZB` state are gen 23's `JAtZB.detPl` / `detAtB`.

Premise `hA : P0.ArchTotal arI` (as P3/JExtVSteps' `vcpu_report_w`: `virtualization` total; P0's platform totality,
used throughout P3/JExtV*). No new named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3
import Fl4Proofs.P3.JExtVStepsB
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Classical
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 16000000 in
/-- **`vcpu.report` writes no `JW` word and leaves the thread out of `TS_RUNNING_VM`** (module docstring). -/
theorem JAtZV3.reportFoot (hA : P0.ArchTotal arI) (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64}
    (ht : Z.th t = some .tcb) (badge : U64) :
    vcpu.report st arI s a t badge ⦃ s' => L.mem s' (P1.stA t) ≠ 8#u64 ∧ ∀ b, JW V Z.th b → L.mem s' b = L.mem s b ⦄ := by
  have Jz := J.z2.zv
  have B := Jz.base
  have Dp := B.detPl Jz.vm
  have Da := B.detAtB Jz.vm
  have P := Dp.pl
  have hta := Dp.ta t ht
  have hfr : ∀ s1, P1.WritesIn st s s1 (fun b => ¬ JW V Z.th b) → ∀ b, JW V Z.th b → L.mem s1 b = L.mem s b :=
    fun s1 h b hb => h.mem_eq (P.jw b hb) fun h' => h' hb
  refine WP.spec_mono (P1.vcpu.report.gen (Bok := P1.BufOK (BufU Z σ)) (vOk := fun v => v ∈ V)
    (P := fun s1 => P1.WritesIn st s s1 (fun b => ¬ JW V Z.th b))
    (Q := fun s1 => L.mem s1 (P1.stA t) ≠ 8#u64 ∧ P1.WritesIn st s s1 (fun b => ¬ JW V Z.th b)) hA
    ⟨fun s1 b i v hb h1 hi => WP.spec_mono (set_mr_w s1 hta hb (Dp.ua t ht) (by omega)) fun r hr =>
        (h1.trans hr).mono fun b' hb' => hb'.elim id fun h => (Dp.rep t ht b' h).1,
     fun s1 r v h1 hr => WP.spec_mono (P1.obj.Tcb.set_reg.wrS s1 t r v hta (by
        rcases hr with rfl | rfl | rfl <;>
          simp [layout.reg.MSG_INFO, layout.reg.BADGE, layout.reg.FAULT_IP]))
        fun s' ⟨K, hK, e⟩ => by
          subst e
          have hr' : r.val < 384 := by
            rcases hr with rfl | rfl | rfl <;>
              simp [layout.reg.MSG_INFO, layout.reg.BADGE, layout.reg.FAULT_IP]
          exact (h1.trans (P1.writesIn_wr (P1.field_aligned hta (by omega) (by omega)))).mono fun b hb =>
            hb.elim id fun e => (Dp.rep t ht b (Or.inl ⟨K, by omega, by omega, by omega, e⟩)).1,
     fun s1 v h1 hv => by
        unfold vcpu.set
        simp only [lift, bind_ok]
        exact WP.spec_mono (P1.LawfulStore.write_spec s1 _ _) fun s' e => by
          subst e
          exact (h1.trans (P1.writesIn_wr (Dp.vca v hv).1)).mono fun b hb =>
            hb.elim id fun e => (Dp.vc v hv b (Or.inl e)).1⟩
    (fun s1 h1 => WP.spec_mono (sts_w s1 t sched.TS_RUNNING (P.sw _ ⟨t, ht, rfl⟩) (by rw [actA_of h1]; exact Da.actA_al)
      (by rw [actA_of h1]; exact fun e => (Da.nd _ (Or.inr rfl)).2 ⟨t, ht, e⟩)) fun s' ⟨w, e⟩ => ⟨by
        rw [e]; simp [sched.TS_RUNNING], by
        rw [actA_of h1] at w
        exact (h1.trans w).mono fun b hb => hb.elim id fun h => h.elim (fun e => P.swjw b ⟨t, ht, e⟩)
          fun e => (Da.nd b (Or.inr e)).1⟩)
    (P1.WritesIn.refl _ _) (Da.buf s (P1.WritesIn.refl _ _) t ht) (fun h0 _ => by
      have h0' : L.mem s (tVcpuA t) ≠ 0#u64 := h0
      exact ((Jz.extv.bnd t ht).resolve_left h0').1)) fun s' ⟨h8, hw⟩ => ⟨h8, hfr s' hw⟩

end

end

end Fl4Proofs.P3
