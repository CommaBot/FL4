/-
P3 (line mmuAD, gen 29): **SC-code steps at `JAtZV2`; `cancel_yield_to` lifted** (gen 28's "Next" item 3).

* **`zv_tk`**: a spec step `ScTKw (fun _ => False) σ σ'` (P3/ScTK: the SC code's steps, no thread changes state)
  keeps every arch object, keeps every object's size, and makes no new `runningVM` thread — exactly the three
  spec facts `JAtZV.ofBS` asks (`hvk`, `hsz`, `hrv`).
* **`JAtZB.tfoot_nh`**: a `TFoot` word (scheduler footprint: TCB words past 256, the current node, notification
  words, SC words) is not the VCPU-list head word `ksb + 80` (`JKern.hks`, the node base).
* **`JAtZV2.ofTK`**: the VM-epoch frame for every native step with a `TFoot` footprint and an `ScTKw (fun _ =>
  False)` spec step: `JAtZB` after ⇒ `JAtZV2` after (`JAtZV2.ofBS` with `tfoot_oobj`, `VKeep.of_tfoot`,
  `tfoot_nh`, `zv_tk`).
* **`JAtZB.deadP_sc_stepG`**, **`JAtZB.deadP_sc_step`** (P3/ScDeadStep, generated copies over `JAtZB`,
  `scratch/mmu24_jatzb_gen.py cancelYieldJD`; the other 23 dependencies are already in P3/JAtZBWr / JAtZBSched),
  **`JAtZB.cancelYieldJD`** (P3/XTopJointYield's `JAtZ.cancelYieldJD` over `JAtZB`, proof verbatim; the post
  also names the spec step's `ScTKw` and FL4's `TFoot` footprint, both already proved inside).
* **`JAtZV2.cancelYieldJ`**: `cancel_yield_to` of a yielder at `JAtZV2 V X` for any `V`, premises exactly
  `JAtZ.cancelYieldJD`'s.

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZBSched2
import Fl4Proofs.P3.XTopJointYield
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- **What an `ScTKw (fun _ => False)` spec step keeps of the VM epoch** (module docstring). -/
theorem zv_tk {σ σ' : Fl4Spec.State Unit} (h : Sched.ScTKw (fun _ => False) σ σ') :
    (∀ p ao, σ.kheap p = some (.archObj ao) → σ'.kheap p = σ.kheap p) ∧
    (∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko) ∧
    (∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM) := by
  refine ⟨fun p ao hp => ?_, fun o ko' ho => ?_, fun o x' ho hx => ?_⟩
  · have k := h.kh p
    rw [hp] at k ⊢
    cases e : σ'.kheap p with
    | none => rw [e] at k; exact k.elim
    | some o' =>
      rw [e] at k
      change Sched.TKObj False (.archObj ao) o' at k
      rcases k with k | ⟨x, y, h1, -⟩ | ⟨x, y, n, h1, -⟩ | ⟨x, y, h1, -⟩ | ⟨x, y, h1, -⟩
      · rw [k]
      all_goals cases h1
  · have k := h.kh o
    rw [ho] at k
    cases e : σ.kheap o with
    | none => rw [e] at k; exact k.elim
    | some ko =>
      rw [e] at k
      change Sched.TKObj False ko ko' at k
      refine ⟨ko, rfl, ?_⟩
      rcases k with rfl | ⟨x, y, rfl, rfl, -⟩ | ⟨x, y, n, rfl, rfl⟩ | ⟨x, y, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ <;> rfl
  · have k := h.kh o
    rw [ho] at k
    cases e : σ.kheap o with
    | none => rw [e] at k; exact k.elim
    | some ko =>
      rw [e] at k
      change Sched.TKObj False ko (.tcb x') at k
      rcases k with k | ⟨x, y, h1, h2, -, h3⟩ | ⟨_, _, _, -, h2⟩ | ⟨_, _, -, h2, -⟩ | ⟨_, _, -, h2, -⟩
      · exact ⟨x', by rw [k], hx⟩
      · cases h2
        refine ⟨x, by rw [h1], ?_⟩
        rcases h3 with h3 | ⟨h3, -⟩
        · rw [← h3]; exact hx
        · exact h3.elim
      all_goals cases h2

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **A `TFoot` word is not the VCPU-list head word** (module docstring). -/
theorem JAtZB.tfoot_nh (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64}
    (h : Sched.TFoot st Z.T Z.N Z.C Z.c s σ b) : b ≠ P1.vHeadA st s := by
  intro e
  subst e
  have hvh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
  rcases Sched.tfoot_tcb J.xtop.fin.1.1.1 h with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ |
      ⟨sc, hsc, x, n, hk, hso⟩
  · have d := J.kern.hks y _ (J.zH.1 y hy) (fun _ h => by cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d
    omega
  · have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
    omega
  · have d := J.kern.hks n _ (J.zH.2.2.2 n hn) (fun _ h => by cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d
    omega
  · obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hH := (hJ.sc sc x n (J.c0 sc hsc) hk).2
    have d := J.kern.hks sc _ hH (fun _ h => by cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d
    unfold Sched.ScObj at hso
    omega

/-- **The VM-epoch frame of an SC-code step** (module docstring). -/
theorem JAtZV2.ofTK (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {Ac' : Set U64}
    {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw (fun _ => False) σ σ') :
    JAtZV2 (L := L) arI V X AR Z H Cs Ac' Lst' D' s' a' σ' := by
  have B := J.zv.base
  have hS := B.xtop.fin.1.1.1
  obtain ⟨h1, h2, h3⟩ := zv_tk hK
  exact J.ofBS B' hw (fun b hb => Sched.tfoot_oobj hS hb) (fun b hb => B.tfoot_nh hb) (VKeep.of_tfoot hS B.thT hw)
    (fun u hu => by obtain ⟨y, hy⟩ := J.zv.vm.spec u hu; exact h1 _ _ hy) h2 h3

-- from Fl4Proofs/P3/ScDeadStep.lean
section
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 400000 in
/-- **The dead stay dead across an SC step** (module docstring); a thread
whose state may change (`P`) keeps an `Inactive` state. -/
theorem JAtZB.deadP_sc_stepG {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    {P : Fl4Spec.ObjRef → Prop} (hK : ScTKw P σ σ')
    (hP : ∀ p x, P p → σ.kheap p = some (.tcb x) → tsCode x.tcbState = 0 →
      ∀ y, σ'.kheap p = some (.tcb y) → y.tcbState = x.tcbState)
    {W : Fl4Spec.ObjRef → Prop} (hL : LK W σ σ') (hF : FK σ σ') (hAS : ActSched σ')
    (hY' : YieldRel Z.T Z.C (L.mem s') σ') {q : U64} (hYD : YDeadKeep σ σ' q.bv)
    (hW : ¬ W q.bv) (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q :=
  J.deadP_sc_stepQ hX' hw hK (fun x => hP _ x) hL hF hAS hY' hYD hW hd

end

-- from Fl4Proofs/P3/ScDeadStep.lean
section
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **The dead stay dead across an SC step** (module docstring;
`deadP_sc_stepG` with the changed threads runnable). -/
theorem JAtZB.deadP_sc_step {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    {P : Fl4Spec.ObjRef → Prop} (hK : ScTKw P σ σ')
    (hP : ∀ p x, P p → σ.kheap p = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    {W : Fl4Spec.ObjRef → Prop} (hL : LK W σ σ') (hF : FK σ σ') (hAS : ActSched σ')
    (hY' : YieldRel Z.T Z.C (L.mem s') σ') {q : U64} (hYD : YDeadKeep σ σ' q.bv)
    (hW : ¬ W q.bv) (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q :=
  J.deadP_sc_stepG hX' hw hK (fun p x hp hk h0 => absurd h0 (tsCode_ne_of_runnable (hP p x hp hk))) hL hF hAS hY'
    hYD hW hd

end

-- from Fl4Proofs/P3/XTopJointYield.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 8000000 in
/-- **`cancel_yield_to` of a yielder at `J`** (P3/XTopJointYield's `JAtZ.cancelYieldJD` over `JAtZB`; the post
also names the spec step's `ScTKw` and FL4's `TFoot` footprint). -/
theorem JAtZB.cancelYieldJD (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {y p : U64} (hy : y ∈ Z.T)
    (hp : L.mem s (yieldA y) = p) (hp0 : p ≠ 0#u64) :
    schedcontext.cancel_yield_to st s y ⦃ s' => ∃ σ',
      Fl4Spec.schedContextCancelYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      ScTKw (fun _ => False) σ σ' ∧ P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64), JAtZB (L := L) arI AR Z H Cs Ac' Lst' D s' a σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hy0 : y ≠ 0#u64 := fun e => (hc.tcbs y hy).ne0 (by rw [e]; rfl)
  obtain ⟨xy, hky, eyt⟩ := J.yld.tcb y hy
  obtain ⟨hpC, z, n, hkz, eyf⟩ := J.yld.toSc y hy (by rw [hp]; exact hp0)
  rw [hp] at hpC hkz eyt
  have hsw56 := sw_hdr hS hpC (K := 56#u64) (by simp) (by simp) (by decide)
  have hal56 : Aligned (scW p 56#u64) := by
    obtain ⟨x0, n0, -, hx0⟩ := hs.scs p hpC; exact (hx0.hdr (K := 56#u64) (by simp) (by simp)).1
  have hyT : y ∈ P1.Heap.tcbs H := by rw [← J.tcbs_eq.1]; exact hy
  have hcode : schedcontext.cancel_yield_to st s y ⦃ s' =>
      s' = L.wr (L.wr s (scYieldFromA p) 0#u64) (yieldA y) 0#u64 ⦄ := by
    unfold schedcontext.cancel_yield_to
    step with obj.Tcb.is_null.spec as ⟨b2, hb2⟩
    have hb2' : b2 = false := by rw [hb2]; exact decide_eq_false hy0
    rw [hb2']
    simp only [Bool.false_eq_true, ↓reduceIte]
    step with obj.Tcb.yield_to.spec as ⟨i2, hi2⟩
    rw [hp] at hi2
    rw [hi2]
    have hb' : (p != 0#u64) = true := by simp [hp0]
    simp only [hb', ↓reduceIte]
    exact WP.spec_bind (obj.Sc.set_yield_from.spec s _ 0#u64) fun s3 h3 => h3 ▸ obj.Tcb.set_yield_to.spec _ y 0#u64
  refine WP.spec_mono (WP.spec_and (P1.schedcontext.cancel_yield_to.blk s y J.blk hyT) hcode) ?_
  rintro s' ⟨hP, rfl⟩
  obtain ⟨hS3, hf3, hK3, hw3⟩ := hS.set_sc_yf hpC hkz 0#u64
  rw [Notif.optRef_zero] at hS3 hK3
  have hpy : p.bv ≠ y.bv := fun e => by rw [e, hky] at hkz; cases hkz
  have hkay : (updSc σ p.bv { z with scYieldFrom := none } n).kheap y.bv = some (.tcb xy) := by
    simp [updK, Ne.symm hpy, hky]
  obtain ⟨hS4, hf4, hK4⟩ := hS3.set_yt hy hkay 0#u64
  rw [Notif.optRef_zero] at hS4 hK4
  have hm4 : ∀ u ∈ Z.T, u ≠ y → L.mem (L.wr (L.wr s (scYieldFromA p) 0#u64) (yieldA y) 0#u64) (yieldA u) =
      L.mem s (yieldA u) := by
    intro u hu hne
    rw [L.mem_wr_ne (yieldA_aligned hT hy) (yieldA_aligned hT hu)
      (fun e => hne (yieldA_inj hT hy hu (UScalar.eq_of_val_eq e.symm)))]
    exact WritesIn.yield_keep hT hw3 u hu
  have hmy : L.mem (L.wr (L.wr s (scYieldFromA p) 0#u64) (yieldA y) 0#u64) (yieldA y) = 0#u64 :=
    L.mem_wr_same (yieldA_aligned hT hy)
  have hY' := J.yld.clear hy hp hp0 hky hkz hm4 hmy
  have hN' : NSC Z.N Z.C (updK (updSc σ p.bv { z with scYieldFrom := none } n) y.bv
      (.tcb { xy with tcbYieldTo := none })) := J.nsc.updSc.updTcb
  have hI' := (J.inv.scFields (y' := { z with scYieldFrom := none }) hkz rfl rfl rfl rfl).ytUpd hkay none
  have hR' := (hR.frame hS.placed hf3 hK3).frame hS3.placed hf4 hK4
  have he := cancelYieldTo_some hky (by rw [eyt, Notif.optRef_ne hp0]) hkz hpy
  have hm : ((), updK (updSc σ p.bv { z with scYieldFrom := none } n) y.bv (.tcb { xy with tcbYieldTo := none })) ∈
      (Fl4Spec.schedContextCancelYieldTo (Z := Unit) y.bv σ).1 := by rw [he]; exact Set.mem_singleton _
  have hK : ScTKw (fun _ => False) σ _ := nkt_schedContextCancelYieldTo y.bv σ _ hm
  have hA : QKY σ (updK (updSc σ p.bv { z with scYieldFrom := none } n) y.bv (.tcb { xy with tcbYieldTo := none })) :=
    QKY.upd2 hkz hky rfl rfl
  have hW : P1.WritesIn st s (L.wr (L.wr s (scYieldFromA p) 0#u64) (yieldA y) 0#u64) (TFoot st Z.T Z.N Z.C Z.c s σ) :=
    ((writesIn_wr (st := st) (s := s) (v := 0#u64)
        (show Aligned (scYieldFromA p) by rw [scYieldFromA_eq]; exact hal56)).trans
      (writesIn_wr (st := st) (s := L.wr s (scYieldFromA p) 0#u64) (v := 0#u64) (yieldA_aligned hT hy))).mono
      fun b hb => by
        rcases hb with rfl | rfl
        · exact Or.inl (KFoot.of_sw (by rw [scYieldFromA_eq]; exact hsw56))
        · exact Or.inr ⟨y, hy, rfl⟩
  have hX' : XTopAt (L := L) AR Z _ a _ :=
    xtop_sc_step (ct := σ.curThread) J.xtop J.ip J.nk hW (hK.mono fun _ h => h.elim) hS4 hR' id
  have hall := ScAll.of_tr hS J.rp J.mcp J.call J.rfree ⟨hS4, hR', hN', hI'⟩ hY' (hW.mono fun b hb => Or.inl hb)
    ((pres_schedContextCancelYieldTo y.bv).of_eq he) rfl
  obtain ⟨-, -, hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ := hall
  have hAI := hA.actIdle J.act
  have hYD : ∀ r, YDeadKeep σ (updK (updSc σ p.bv { z with scYieldFrom := none } n) y.bv
      (.tcb { xy with tcbYieldTo := none })) r := fun r =>
    YDeadKeep.upd (p := y.bv) (o := .tcb { xy with tcbYieldTo := none })
      (YDeadKeep.upd (p := p.bv) (o := .schedContext { z with scYieldFrom := none } n) (YDeadKeep.of_at rfl)
        (fun _ e => by cases e) (fun _ _ e => by cases e; rfl))
      (fun _ e => by cases e; rfl) (fun _ _ e => by cases e)
  have hdead : ∀ q ∈ D, DeadP (L := L) H (L.wr (L.wr s (scYieldFromA p) 0#u64) (yieldA y) 0#u64) q := fun q hq =>
    J.deadP_sc_step hX' hW hK (fun _ _ h => h.elim) (hA.lk (W := fun _ => False)) hA.fk hAI.1 hY' (hYD q.bv)
      (fun h => h) (J.jcov.dead q hq)
  have hDbg := J.kw_dbg (hP.2.1.mono (Set.empty_subset _))
  have hKd := J.kw_dbgKeep (hP.2.1.mono (Set.empty_subset _))
  exact ⟨_, he, hK, hW, Ac, Lst', J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK (J.idleW_keep hX'.fin.1.1.1 hA.fk.2.1 hA.fk.2.2).2) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hA.fk.2.1 hA.fk.2.2) hKd subset_rfl) (J.sc_kern hW hK hA.fk hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hN' hI' (hA.cur J.cur) (hA.own J.own) (hA.off J.off) hAI (hA.bsa J.bsa)
    (hA.curRunM J.curRun) hP.1 hKd (J.idleW_keep hX'.fin.1.1.1 hA.fk.2.1 hA.fk.2.2).1 J.zD⟩

end


section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **`cancel_yield_to` of a yielder at `JAtZV2`** (module docstring). -/
theorem JAtZV2.cancelYieldJ (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {y p : U64} (hy : y ∈ Z.T)
    (hp : L.mem s (yieldA y) = p) (hp0 : p ≠ 0#u64) :
    schedcontext.cancel_yield_to st s y ⦃ s' => ∃ σ',
      Fl4Spec.schedContextCancelYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64), JAtZV2 (L := L) arI V X AR Z H Cs Ac' Lst' D s' a σ' ⦄ :=
  WP.spec_mono (J.zv.base.cancelYieldJD hy hp hp0) fun _ ⟨σ', he, hK, hW, Ac', Lst', B'⟩ =>
    ⟨σ', he, Ac', Lst', J.ofTK B' hW hK⟩

end

end

end

end Fl4Proofs.P3
