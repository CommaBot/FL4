/-
P3 (issue #16, g7e; KENTRY-PLAN g7d (3)): **the narrowed D6 `tail` is a
theorem** (INV-PLAN §1.U3L D6).

* `kfin_tail_of`: at a finish state `J : JAtZR … s a σ`, with the bundle's
  `hd`, `arch`, `archNd`, P1's `ArchTotal`, `ARKeep` and `ArchRefines` (A15),
  `sni`/`send` (theorems, ScSniProof), `FpuOwnOK σ` and **`IdleVt σ` [J]**
  (D7), FL4's `schedule` satisfies `KFinAtR5.tail`'s post. For a given
  post-timer state `σ1` related to the run's own `timer.fire` outcome `rf`
  (`JAtZR`, or `JAtZ` via `JAtZ.toR`), G7eChain's `schedule_refinesWP0FRA` is
  run with the fire predicate pinned to `(rf, σ1)` (its hypotheses read off
  `JAtZR` at `(rf, σ1)`; the domain time across the timers by `fire_dt`,
  `NdOK` by `ndOK_fire`, the FPU owner by `fpuOwnOK_firesZR`, `RootFr` by
  `JAtZR.rootFr` with `IdleVt` carried by `idleVt_fire`). Its outcome is
  FL4's (`schedule` is total, P0) and the spec's (`schedule σ1` is the given
  singleton), so `AR r.2 σ'.cr3`.
* `KFinAtR8`: `KFinAtR5` without `tail`, with `idle : IdleVt σ` [J];
  `KFinAtR8.to5`. `KFinEv8`: `KFinEv5` with `KFinAtR8`; `KFinEv8.to`, given
  `FpuOwnOK` at the bundle's states.
-/
import Fl4Proofs.P3.G7eChain
import Fl4Proofs.P3.XTopJointKEntryU5
import Fl4Proofs.P3.BufAtJR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- **The narrowed tail at a finish state** (module docstring). -/
theorem kfin_tail_of {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) (hnd : Fl4Spec.numDomains = 1)
    (hAT : P0.ArchTotal arI) (hK : ARKeep arI AR) (hRef : ArchRefines arI AR)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hFO : FpuOwnOK σ) (hIV : IdleVt σ) :
    sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      timer.fire st arI s a = ok rf →
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) ∨
       ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄ := by
  have hSt : P0.StoreTotal st := P1.LawfulStore.total
  refine WP.spec_mono (P1.spec_eq' (Fl4Proofs.P0.sched.schedule.p0 st arI s a hSt hAT)) ?_
  rintro r ⟨hr, -⟩ ⟨s1, a1⟩ σ1 σ' D1 hF hfr hJ1 hsc - - - - -
  obtain ⟨V1, Ac1, Lst1, D2, J1⟩ : ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
      JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 s1 a1 σ1 := by
    rcases hJ1 with h | ⟨V1, Ac1, Lst1, D2, J1⟩
    · exact h
    · exact ⟨V1, Ac1, Lst1, D2, J1.toR⟩
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun _ h => h
  have hfk := spec_ok_post (P1.timer.fire.kw hAT (P1.ibKeep_holds hAT) hNt s a J.blk J.bufAtJ) hfr
  simp only [WP.uncurry'_pair] at hfk
  have hUk := fun b hb o ho h8 => (J.bufAtJ.1 b hb).ks o ho h8
  have hm := J.fire_ks hfk hUk
  have hdt1 : σ1.domainTime ≠ 0 ∨ NdOK (L := L) s1 σ1 :=
    hd.imp (fun h => by rw [fire_dt J.xtop.fin.1.1.1 J1.xtop.fin.1.1.1 hfk.1 hm]; exact h)
      (fun h => J.ndOK_fire h hfk hUk hF)
  have hfire : timer.fire st arI s a ⦃ r => ∃ σ1', Fires σ σ1' ∧ SchedRel st Z.N Z.T Z.C Z.c r.1 σ1' ∧
      NtfnStateRel Z.N Z.T (L.mem r.1) σ1' ∧ NSC Z.N Z.C σ1' ∧ SchedPreW0R Z.T Z.C σ1' ∧
      ((σ1'.domainTime ≠ 0 ∨ NdOK (L := L) r.1 σ1') ∧
        (∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb r.1).val ∨ (L.ksb r.1).val + 13568 ≤ n.val) ∧
        (σ1' = σ1 ∧ FpuOwnOK σ1' ∧ VsRootOK Z.T σ1' ∧
          (RootFr (L := L) AR Z.T (Z.mv Z.G V1).P Z.c r.1 r.2 σ1' ∧ AR r.2 σ1'.archState.x64CurrentCr3))) ⦄ := by
    rw [hfr, WP.spec_ok]
    exact ⟨σ1, hF, J1.xtop.fin.1.1.1, J1.xtop.fin.1.1.2.2.1, J1.nsc, ⟨J1.inv, J1.cur, J1.off, J1.act, J1.own⟩,
      hdt1, J1.nk, rfl, fpuOwnOK_firesZR J hF J1.xtop.fin.1.1.2.2.1 hFO, J1.vsRootOK,
      J1.rootFr (J.idleVt_fire hAT hIV hfr hF J1), J1.xtop.fin.1.1.2.2.2.2.2.2⟩
  have hC := spec_ok_post (schedule_refinesWP0FRA hRef hSt hAT hK s a σ J.xtop.fin.1.1.1 J.xtop.fin.1.1.2.2.1 J.nsc
    hnd hfire (fun _ _ h => h.2.1) (fun _ _ h => h.2.2.1) (fun _ _ h => h.2.2.2) hA hAN hsni hsend hT) hr
  obtain ⟨σ1', σ'', -, hsc', -, -, -, -, -, -, rf', ⟨e1, -⟩, -, σ3, -, -, -, hAR⟩ := hC
  rw [e1, hsc] at hsc'
  have e2 : ((), σ') = ((), σ'') := Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hsc')
  have e3 : σ' = σ'' := congrArg Prod.snd e2
  exact ⟨by rw [e3]; exact hAR⟩

variable (arI)

/-- **`KFinAtR5` without `tail`, with `IdleVt` [J]** (module docstring). -/
structure KFinAtR8 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ
  arch : ArchSwF st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c
  /-- [J] INV-PLAN §1.U3L D7: the idle TCB's vtable is no mapped PML4 cap. -/
  idle : IdleVt σ

variable {arI}

theorem KFinAtR8.to5 {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hK : ARKeep arI AR) (hRef : ArchRefines arI AR) (hD : SetDlDet) (hT : TimeAgree arI)
    (F : KFinAtR8 (L := L) arI AR Z H Cs s a σ) (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hFO : FpuOwnOK σ) : KFinAtR5 (L := L) arI AR Z H Cs s a σ :=
  ⟨F.hd, F.arch, F.archNd,
    kfin_tail_of J F.hd hnd hAT hK hRef F.arch F.archNd (sniHyp_of hAT hD) (sendHyp_of hAT) hT hFO F.idle⟩

variable (arI)

/-- `KFinEv5` with `KFinAtR8`. -/
def KFinEv8 (AR : A → Fl4Spec.Cr3 → Prop) (ev : Fl4Spec.Event) (Kf : S → A → Prop) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
    ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
      Kf s' a' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 → KFinAtR8 (L := L) arI AR Z' H' Cs' s' a' x.2

variable {arI}

theorem KFinEv8.to {ev : Fl4Spec.Event} {Kf : S → A → Prop} {σ : Fl4Spec.State Unit}
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI) (hK : ARKeep arI AR) (hRef : ArchRefines arI AR)
    (hD : SetDlDet) (hT : TimeAgree arI)
    (hfo : ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1, FpuOwnOK x.2)
    (h : KFinEv8 (L := L) arI AR ev Kf σ) : KFinEv5 (L := L) arI AR ev Kf σ :=
  fun x hx Z' H' Cs' Ac' Lst' D' s' a' hKf J =>
    (h x hx Z' H' Cs' Ac' Lst' D' s' a' hKf J).to5 hnd hAT hK hRef hD hT J (hfo x hx)

end

end

end Fl4Proofs.P3.SInvR.G5
