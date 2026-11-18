/-
P3 (DESIGN.md §9), scheduling contexts: **SchedContext YieldTo at `J`**
(any yielder, either outcome).
-/
import Fl4Proofs.P3.ScJointConsumed
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical Fl4Proofs.P3.Notif

noncomputable section

/-- The spec's yield links of a switching YieldTo (`yieldSwitch`'s first two
steps): the caller yields to the SC, the SC is yielded from by the caller. -/
def yieldLink (ct sc : ObjRef) : SMonad Unit Unit := do
  setTcbObjRef tcbYieldToUpdate ct (some sc)
  setScObjRef scYieldFromUpdate sc (some ct)

theorem nkt_yieldLink (ct sc : ObjRef) : NKT (yieldLink ct sc) := by
  unfold yieldLink setScObjRef setTcbObjRef
  repeat' (first | nkt_step | (unfold NonDet.when; split) | split)

theorem pres_yieldLink (ct sc : ObjRef) : Pres (false, true) (yieldLink ct sc) := by
  unfold yieldLink; pres_auto

theorem yieldLink_eq {σ : State Unit} {ct sc : ObjRef} {xc : Tcb} {y : SchedContext} {n : Nat}
    (hkc : σ.kheap ct = some (.tcb xc)) (hks : σ.kheap sc = some (.schedContext y n)) (hpc : sc ≠ ct) :
    yieldLink ct sc σ = ({((), updSc (updK σ ct (.tcb { xc with tcbYieldTo := some sc })) sc
      { y with scYieldFrom := some ct } n)}, False) := by
  unfold yieldLink
  show (threadSet _ ct >>= _) σ = _
  rw [nd_bind_one (threadSet_eq _ hkc)]
  have hka : (updK σ ct (.tcb { xc with tcbYieldTo := some sc })).kheap sc = some (.schedContext y n) := by
    simp [updK, hpc, hks]
  exact updateSchedContext_eq hka _

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- A thread of `Z.T` is a TCB of the typed heap. -/
theorem JAtZ.thTcb (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) :
    Z.th t = some .tcb := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact (hJ.tcb t).2 (J.zH.1 t ht)

set_option maxHeartbeats 4000000 in
/-- **`dequeue` at `J`** (DomSched's `dequeue_schedStep`, a scheduler step:
`JAtZ.schedJ`). -/
theorem JAtZ.dequeueJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) :
    sched.dequeue st s t ⦃ s' => ∃ σ', Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedDequeue t.bv σ =
      ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s' a σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨x, hk, -⟩ := hs.tcb t ht
  refine WP.spec_mono (dequeue_schedStep (J.thTcb ht) hk hS ht) ?_
  rintro s' ⟨-, -, -, hSS⟩
  exact ⟨_, tcbSchedAction_gen hk _, J.schedJ hSS⟩

set_option maxHeartbeats 4000000 in
/-- **`enqueue` of a schedulable thread at `J`** (DomSched's
`enqueue_schedStep`; `JAtZ.schedJ`). -/
theorem JAtZ.enqueueJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (hsch : Fl4Spec.schedulable t.bv σ = true) :
    sched.enqueue st s t ⦃ s' => ∃ σ', Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue t.bv σ =
      ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s' a σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨x, hk, -⟩ := hs.tcb t ht
  have hd := (schedulable_eq hR hS ht).trans hsch
  obtain ⟨hrw, hbd, hmx, hrl⟩ := of_decide_eq_true hd
  have hrun : P1.Runnable (L.mem s (P1.stA t)) := by rw [stA_tStA]; exact hrw
  refine WP.spec_mono (enqueue_schedStep (J.thTcb ht) hk hS ht (fun _ => hrl) hsch hrun hbd hrl
    (fun e => by rw [e] at hmx; simp at hmx)) ?_
  rintro s' ⟨-, -, -, hSS⟩
  exact ⟨_, tcbSchedAction_gen hk _, J.schedJ hSS⟩

set_option maxHeartbeats 8000000 in
/-- **The yield links at `J`** (`yield_switches`' `set_yield_to` and
`set_yield_from` of a switching YieldTo; as `JAtZ.cancelYieldJ` with the
links set: `YieldRel.pair`, P1's `yield_link.blk`). -/
theorem JAtZ.linkYieldJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct sc : U64} (hct : ct ∈ Z.T)
    (hsc : sc ∈ Z.C) (hy0 : L.mem s (yieldA ct) = 0#u64) {xc : Fl4Spec.Tcb}
    (hkc : σ.kheap ct.bv = some (.tcb xc)) {y : Fl4Spec.SchedContext} {n : Nat}
    (hks : σ.kheap sc.bv = some (.schedContext y n)) (hyf : y.scYieldFrom = none) :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D'
      (L.wr (L.wr s (yieldA ct) sc) (scYieldFromA sc) ct) a
      (updSc (updK σ ct.bv (.tcb { xc with tcbYieldTo := some sc.bv })) sc.bv { y with scYieldFrom := some ct.bv } n) := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hct0 : ct ≠ 0#u64 := fun e => (hc.tcbs ct hct).ne0 (by rw [e]; rfl)
  have hsc0 : sc ≠ 0#u64 := J.c0 sc hsc
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hks] at hk'; cases hk'
  have hsw56 := sw_hdr hS hsc (K := 56#u64) (by simp) (by simp) (by decide)
  have hal56 : Aligned (scW sc 56#u64) := (hx.hdr (K := 56#u64) (by simp) (by simp)).1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hscS : sc ∈ P1.Heap.scs H := ⟨_, (hJ.sc sc y n hsc0 hks).2⟩
  have hctH : ct ∈ P1.Heap.tcbs H := J.zH.1 ct hct
  have hblk := (P1.yield_link.blk J.blk hctH hscS).1
  -- the spec side
  obtain ⟨hS1, hf1, hK1⟩ := hS.set_yt hct hkc sc
  rw [optRef_ne hsc0] at hS1 hK1
  have hpc' : sc.bv ≠ ct.bv := fun e => by rw [e, hkc] at hks; cases hks
  have hka : (updK σ ct.bv (.tcb { xc with tcbYieldTo := some sc.bv })).kheap sc.bv =
      some (.schedContext y n) := by simp [updK, hpc', hks]
  obtain ⟨hS2, hf2, hK2, hw2⟩ := hS1.set_sc_yf hsc hka ct
  rw [optRef_ne hct0] at hS2 hK2
  have hR2 := (hR.frame hS.placed hf1 hK1).frame hS1.placed hf2 hK2
  have hN2 := (J.nsc.updTcb (t := ct.bv) (x := { xc with tcbYieldTo := some sc.bv })).updSc
    (p := sc.bv) (y := { y with scYieldFrom := some ct.bv }) (n := n)
  have hI2 := (J.inv.ytUpd hkc (some sc.bv)).scFields (y' := { y with scYieldFrom := some ct.bv }) hka rfl rfl rfl rfl
  have hY2 := J.yld.pair J.c0 hct hsc hy0 hkc hks hyf
    (m' := L.mem (L.wr (L.wr s (yieldA ct) sc) (scYieldFromA sc) ct))
    (fun u hu hne => by
      rw [WritesIn.yield_keep hT hw2 u hu, L.mem_wr_ne (yieldA_aligned hT hct) (yieldA_aligned hT hu)
        (fun e => hne (yieldA_inj hT hct hu (UScalar.eq_of_val_eq e).symm))])
    (by rw [WritesIn.yield_keep hT hw2 ct hct]; exact L.mem_wr_same (yieldA_aligned hT hct))
  set σ' := updSc (updK σ ct.bv (.tcb { xc with tcbYieldTo := some sc.bv })) sc.bv
    { y with scYieldFrom := some ct.bv } n with hσ'
  have hm : ((), σ') ∈ (yieldLink ct.bv sc.bv σ).1 := by
    rw [yieldLink_eq hkc hks hpc']; exact Set.mem_singleton _
  have hK : ScTKw (fun _ => False) σ σ' := nkt_yieldLink ct.bv sc.bv σ _ hm
  have hsok : SOK (false, true) σ σ' := pres_yieldLink ct.bv sc.bv σ _ hm
  have hA : QKY σ σ' := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q => ?_⟩
    by_cases e1 : q = ct.bv
    · subst e1; exact Or.inr (Or.inl ⟨xc, _, hkc, by simp [σ', updK, Ne.symm hpc'], rfl⟩)
    by_cases e2 : q = sc.bv
    · subst e2; exact Or.inr (Or.inr ⟨y, _, n, hks, by simp [σ', updK], rfl⟩)
    · exact Or.inl (by simp [σ', updK, e1, e2])
  -- FL4's writes
  have hal' : Aligned (scYieldFromA sc) := by rw [scYieldFromA_eq]; exact hal56
  have hW : P1.WritesIn st s (L.wr (L.wr s (yieldA ct) sc) (scYieldFromA sc) ct) (TFoot st Z.T Z.N Z.C Z.c s σ) :=
    ((writesIn_wr (st := st) (s := s) (v := sc) (yieldA_aligned hT hct)).trans
      (writesIn_wr (st := st) (s := L.wr s (yieldA ct) sc) (v := ct) hal')).mono fun b hb => by
      rcases hb with rfl | rfl
      · exact Or.inr ⟨ct, hct, rfl⟩
      · exact Or.inl (KFoot.of_sw (by rw [scYieldFromA_eq]; exact hsw56))
  have hKW : P1.WritesIn st s (L.wr (L.wr s (yieldA ct) sc) (scYieldFromA sc) ct)
      (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s) :=
    ((writesIn_wr (st := st) (s := s) (v := sc) (yieldA_aligned hT hct)).trans
      (writesIn_wr (st := st) (s := L.wr s (yieldA ct) sc) (v := ct) hal')).mono fun b hb => by
      rcases hb with rfl | rfl
      · exact P1.kw_field (K := 3472#u64) hctH (by simp) (by simp) (by simp)
      · obtain ⟨h128, -, -, -, -, -, -, e56⟩ := P1.sc_facts J.blk.2.2.1.1 hscS
        have e : (scYieldFromA sc).val = sc.val + 56 := e56
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hscS, by rw [e]; omega, by rw [e]; omega⟩)))
  have hDbg := J.kw_dbg hKW
  have hX' : XTopAt (L := L) AR Z _ a σ' :=
    xtop_sc_step (ct := σ.curThread) J.xtop J.ip J.nk hW (hK.mono fun _ h => h.elim) hS2 hR2 id
  have hall := ScAll.of_tr hS J.rp J.mcp J.call J.rfree ⟨hS2, hR2, hN2, hI2⟩ hY2 (hW.mono fun b hb => Or.inl hb)
    hsok rfl
  obtain ⟨-, -, hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ := hall
  have hAI := hA.actIdle J.act
  have hdead : ∀ q ∈ D, DeadP (L := L) H (L.wr (L.wr s (yieldA ct) sc) (scYieldFromA sc) ct) q := fun q hq =>
    J.deadP_sc_step hX' hW hK (fun _ _ h => h.elim) (hA.lk (W := fun _ => False)) hA.fk hAI.1 (fun h => h)
      (J.jcov.dead q hq)
  exact ⟨Ac, Lst', D, J.sc_frame hW hK hX' hCR' hRF' hY2 hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hA.fk.2))
    (J.sc_kern hW hK hA.fk hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hN2 hI2 (hA.cur J.cur) (hA.own J.own) (hA.off J.off) hAI (hA.bsa J.bsa)
    (hA.curRunM J.curRun) hblk⟩

end

end

end Fl4Proofs.P3
