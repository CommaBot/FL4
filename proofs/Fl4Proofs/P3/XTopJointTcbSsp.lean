/-
P3 (DESIGN.md §9), TCB: **SetSchedParams of the Thread cap at `J`**
(`tcb_set_sched_paramsJ`).

* `MidK.midN`: ScMidKeep's `MidK.mid` with the resume action at the start
  weakened to "no switch pending" (a reschedule may be pending: the
  fault-handler install's `cancel_all_ipc` asks for one).
* `JAtZ.bindTcbJ`: `schedcontext::bind_tcb` at `J` (as XTopJointFinThreadSc's
  `JAtZ.unbindTcbJ`): `bind_tcb_refines` (the relations),
  `bind_tcb.blkK` (`BlkOK` and the footprint `Foot`), `xtop_sc_step`, `ScAll.of_k`, `BlockedScActive`
  by `bka_schedContextBindTcb`, the mid-entry facts by
  `mka_schedContextBindTcb` and `MidK.midN`, the dead set by
  `deadP_sc_step` outside the bound pair and the pair covered by its caps
  (`cover_cap`), core 0's `DEBUG_TCBS` word by `JAtZ.kw_dbg`.
* `P1.schedcontext.bind_tcb.blkK`: P1's `bind_tcb.blkF` with the tighter
  footprint `Foot` (no debug-list word) when the thread's affinity is
  already the SC's core (at `JAtZ` by `SchedRel`'s one core): `migrate_tcb`
  is then a no-op (`smp.migrate_tcb.frame`).
-/
import Fl4Proofs.P3.XTopJointTcbInstall
import Fl4Proofs.P3.XTopJointTcbPrio
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

/-- **`MidK.mid` with no switch pending at the start** (instead of the
resume action; the switch target's clause of `ActSched` is the only use). -/
theorem MidK.midN {T : Set U64} {σ σ' : State Unit} (hK : MidK σ σ')
    (hnsw : ∀ u, σ.schedulerAction ≠ .switchThread u) (hC : CurInv σ) (hO : OffOK σ) (hA : ActIdle σ) (hI : Inv σ)
    (hcT : ∃ u ∈ T, u.bv = σ.curThread) :
    (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧
      (σ'.schedulerAction = .chooseNewThread → CurOwn T σ') ∧ OffOK σ' ∧ ActIdle σ' := by
  obtain ⟨xt, hkt, hsc, hnb⟩ := hC.tcb
  obtain ⟨y0, n0, hy0⟩ := hC.sc
  obtain ⟨xt', hkt', e1, e2⟩ := hK.ctT xt hkt
  obtain ⟨y0', hy0', f1, f2, f3⟩ := hK.cscS y0 n0 hy0
  have hnr' : ∀ hcn : σ'.schedulerAction ≠ .chooseNewThread ∨ 0 < σ'.consumedTime,
      σ.curThread ∉ σ'.releaseQueue := by
    intro hc hm
    rcases hK.rq _ hm with h | ⟨-, h | ⟨h0, hcn⟩⟩
    · exact hC.notRel h
    · exact h rfl
    · rcases hc with hc | hc
      · exact hc hcn
      · rw [h0] at hc; simp at hc
  refine ⟨?_, fun hcn => ?_, fun hpos y n hy _ => ?_, ⟨fun t ht => ?_, ?_⟩⟩
  · by_cases hcn : σ'.schedulerAction = .chooseNewThread
    · exact Or.inl hcn
    right
    refine ⟨⟨xt', by rw [hK.ct]; exact hkt', by rw [e1, hK.csc]; exact hsc, by rw [e2]; exact hnb⟩,
      ⟨y0', n0, by rw [hK.csc]; exact hy0'⟩, fun hid y m hy => ?_, fun hm => hnr' (Or.inl hcn) (by rw [← hK.ct]; exact hm)⟩
    rw [hK.csc, hK.isc] at hid; rw [hK.csc] at hy
    rw [hy0'] at hy; cases hy
    exact f2 (hC.active hid y0 n0 hy0)
  · obtain ⟨u, hu, hub⟩ := hcT
    obtain ⟨y1, n1, hy1, hy1t⟩ := hI.back _ xt σ.curSc hkt hsc
    rw [hy0] at hy1; cases hy1
    refine ⟨u, hu, xt', by rw [hub]; exact hkt', by rw [e1, hK.csc]; exact hsc, fun x n hx => ?_, fun hpos hm => ?_⟩
    · rw [hK.csc, hy0'] at hx; cases hx; rw [f1, hy1t, hub]
    · exact hnr' (Or.inr hpos) (by rw [← hub]; exact hm)
  · have hne : σ'.consumedTime ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    have hc := hK.consNe hne
    rw [hK.csc, hy0'] at hy; cases hy
    have hpos0 : 0 < σ.consumedTime := by rw [← hc]; exact hpos
    obtain ⟨g1, g2, g3⟩ := hO hpos0 y0 n0 hy0 (fun hid => hC.active hid y0 n0 hy0)
    have hr : refillHd y0' = refillHd y0 := by unfold refillHd; rw [f3 hne]
    rw [hr, hc, hK.time]
    exact ⟨g1, g2, g3⟩
  · exact absurd (hK.sw t ht) (hnsw t)
  · obtain ⟨xi, hki, hsi, hti, hri⟩ := hA.2
    obtain ⟨xi', hki', g1, g2⟩ := hK.idT xi hki
    refine ⟨xi', by rw [hK.idle]; exact hki', by rw [g1, hK.isc]; exact hsi, by rw [g2]; exact hti, fun hm => ?_⟩
    rw [hK.idle] at hm
    rcases hK.rq _ hm with h | ⟨h, -⟩
    · exact hri h
    · exact h rfl

/-- `CurRunM` across a `MidK` step with no switch pending at the start. -/
theorem MidK.curRunM {σ σ' : State Unit} (hK : MidK σ σ') (hnsw : ∀ u, σ.schedulerAction ≠ .switchThread u)
    (hC : CurInv σ) (hcr : CurRunM σ) : CurRunM σ' := by
  by_cases hr : σ'.schedulerAction = .resumeCurThread
  · right
    have hr0 : σ.schedulerAction = .resumeCurThread := by
      cases e : σ.schedulerAction with
      | resumeCurThread => rfl
      | chooseNewThread => rw [hK.cn e] at hr; cases hr
      | switchThread u => exact absurd e (hnsw u)
    rcases hcr with h | h | h
    · exact absurd hr0 h
    · left
      intro x hx
      obtain ⟨xt, hkt, -, -⟩ := hC.tcb
      obtain ⟨y, hy, -, e2⟩ := hK.ctT xt hkt
      rw [hK.ct, hy] at hx; cases hx
      rw [e2]; exact h xt hkt
    · exact Or.inr (by rw [hK.ct, hK.idle]; exact h)
  · exact Or.inl hr

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es : Set U64}

/-- **`bind_tcb` with the footprint `Foot`** when the thread's affinity is
already the SC's core (P1's `schedcontext.bind_tcb.blkF` with `migrate_tcb`
a no-op by `smp.migrate_tcb.frame`): no debug-list word is written. -/
theorem schedcontext.bind_tcb.blkK {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (ht0 : L.mem s (scA t) = 0#u64) (hc0 : L.mem s (scTcbA sc) = 0#u64)
    (hbA : BlockedR (L.mem s (stA t)) → sc ∈ Ac) (haff : L.mem s (affA t) = L.mem s (scCoreA sc)) :
    schedcontext.bind_tcb st ar s a sc t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hta := hT t ht
  have hO := hX.1
  have hm : scTcbA sc ∈ Ω := hSg.sub _ (hO.fixW sc hsc).1
  have ho := h0.omega _ hm
  have hal : Aligned (scTcbA sc) := by
    obtain ⟨hP, hz⟩ := hO.sc sc hsc
    have := (sc_lo hP hz).1
    unfold Aligned; rw [scTcbA_val hP hz]; omega
  have htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hq; exact hB.q t ht hq ht0
  have htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hq; exact hB.r t ht hq ht0
  have hna : L.actionW s ≠ t := fun e => hB.act (e ▸ ht) (by rw [e]; exact ht0)
  have hnb : ∀ y ∈ T, L.mem s (scA y) ≠ sc := fun y hy e => by
    obtain ⟨-, h2, -⟩ := hX.2.2.bound y hy (by rw [e]; exact hsc0)
    rw [e, hc0] at h2; exact (hT y hy).ne0 (by rw [← h2]; rfl)
  have hdisj : sc ≠ L.cscW s → ∀ b, InSC sc (Z sc) b → Outside b (L.cscW s) (Z (L.cscW s)) := by
    intro hne b hb
    have := hO.scDisj sc hsc _ hX.2.2.cur hne
    unfold Outside; unfold InSC at hb; omega
  have hcore := hX.2.2.core sc hsc
  have hsA : Sch st s t → sc ∈ Ac := by
    rintro (e | e | e | e | ⟨e1, e2⟩ | e)
    · exact absurd htq e
    · exact absurd htr e
    · exact absurd e hna
    · exact absurd (by rw [e]; exact ht0) hB.idle
    · exact absurd (by rw [e2]; exact ht0) (hB.resume e1)
    · exact hbA e
  -- the two writes
  unfold schedcontext.bind_tcb
  step with obj.Tcb.set_sc.wr as ⟨s1, e1⟩
  step with obj.Sc.set_tcb.wr as ⟨s2, e2⟩
  subst e1 e2
  have fw2 : Foot st T Cs Sg Scs Z Es s (L.wr (L.wr s (scA t) sc) (scTcbA sc) t) := by
    have f1 : Foot st T Cs Sg Scs Z Es s (L.wr s (scA t) sc) := by
      rw [scA_eq]; exact foot_field hT ht (by simp) (by simp) (by simp) (by simp)
    exact f1.trans (foot_wr hal (kw_sg (hO.fixW sc hsc).1))
  obtain ⟨p8, pB, pX, pS, pSg, -, pfl, pcore, psc, ptc, pact⟩ :=
    donate_pair h0 hB hX.x0 hX.2.2.tsc.x hX.2.2.aff ht0 hS hSg ht hsc hsc0 hnb hcore hdisj hsA
      (fun e => hB.idle (by rw [e]; exact ht0))
  have hsw := bind_swap (L := L) (s := s) (scA_aligned hta) ho.1
    (fun e => out_ne_field (K := 3464#u64) ho ht hta (by simp) e)
  obtain ⟨h2, hB2, hX2, hS2, hSg2⟩ := agree_all p8 pB pX pS pSg (by simp) (by simp) hsw
  set s2 := L.wr (L.wr s (scA t) sc) (scTcbA sc) t with hs2
  have fl2 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3464) →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 hne => (hsw _ (field_aligned (hT y hy) hK hK8)).trans (pfl y hy K hK hK8 hne)
  have sc2 : L.mem s2 (scA t) = sc := (hsw _ (scA_aligned hta)).trans psc
  have core2 : L.mem s2 (scCoreA sc) = L.mem s (scCoreA sc) :=
    (hsw _ (h0.omega _ ((objs_omega hO hSg.sub).2 sc hsc).2.1).1).trans pcore
  have ea2 : L.actionW s2 = L.actionW s := by
    have e : L.actionW s2 = L.actionW (L.wr (L.wr s (scTcbA sc) t) (scA t) sc) := by
      unfold LawfulStore.actionW
      rw [show L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION =
        L.nodeAt (L.wr (L.wr s (scTcbA sc) t) (scA t) sc) (L.cpu (L.wr (L.wr s (scTcbA sc) t) (scA t) sc))
          layout.node.SCHED_ACTION by simp [hs2, nodeAt_wr]]
      exact hsw _ (nodeAt_aligned (p8.nodes _ p8.cur) (by rw [act_val]; omega) (by rw [act_val]))
    rw [e, pact]
  have iq2 : L.mem s2 (inqA t) = L.mem s (inqA t) := by
    rw [inqA_eq]; exact fl2 t ht _ (by simp) (by simp) (fun _ => by simp)
  -- migration
  step with obj.Sc.cpu.spec as ⟨cpu, ecpu⟩
  have hc' : cpu ∈ Cs := by rw [ecpu, core2]; exact hcore
  -- the thread already on the SC's core: `migrate_tcb` is a no-op (`migrate_tcb.frame`)
  have haff2 : L.mem s2 (affA t) = cpu := by
    rw [ecpu, core2, ← haff, affA_eq]; exact fl2 t ht _ (by simp) (by simp) (fun _ => by simp)
  refine WP.spec_bind (WP.spec_and (migrate_tail hA s2 a sc t cpu Q R h2 hB2 hX2 hS2 hSg2 ht (by rw [iq2]; exact htq)
    (by rw [iq2]; exact htr) hc' hsc (fun _ => by rw [sc2, ecpu])) (smp.migrate_tcb.frame
      hA s2 a t cpu h2.tcbs h2.nodes ⟨hX2.1.2.2.tm.dn, hX2.1.2.2.tm.dp, hX2.1.2.2.tm.dh⟩ (h2.aff t ht) hc' ht)) ?_
  rintro ⟨s3, a1⟩ ⟨⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, -, -, -, sc3, -, ea3⟩, -, -, hid⟩
  try simp only [WP.uncurry'_pair]
  rw [sc2] at sc3
  have fw3' : Foot st T Cs Sg Scs Z Es s s3 := by rw [hid haff2]; exact fw2
  -- the sporadic unblock check
  step with sporadic.sc_sporadic.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun s4 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ L.mem s4 (scA t) = sc ∧
      L.actionW s4 = L.actionW s ∧ Foot st T Cs Sg Scs Z Es s s4) ?_ ?_
  · have ok3 : (ok s3 : Result S) ⦃ s4 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ L.mem s4 (scA t) = sc ∧
        L.actionW s4 = L.actionW s ∧ Foot st T Cs Sg Scs Z Es s s4 ⦄ :=
      (WP.spec_ok _).2 ⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, sc3, by rw [ea3, ea2], fw3'⟩
    split
    · step with sporadic.sc_active.val as ⟨b1, eb1⟩
      split
      · rename_i hb1
        step with sched.cur_sc.spec as ⟨c4, _⟩
        step with sc_ne.spec as ⟨b2⟩
        split
        · have hAc : sc ∈ Ac := (hS3.act sc hsc).2 (eb1 hb1)
          have hW : RefillsWF st s3 sc (Z sc) := hS3.wf hsc hAc
          have hSCin : SCin st s3 Ω sc (Z sc) := ⟨hW, hX3.1.scW sc hsc⟩
          have hN' := h3.nodes _ h3.cur
          have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
          have aR : Aligned (L.nodeA s3 layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
          have oR : Outside (L.nodeA s3 layout.node.REPROGRAM) sc (Z sc) :=
            hSCin.node_out h3.omega h3.cur hN' (by rw [rp]; omega) (by rw [rp])
          refine WP.spec_mono (WP.spec_and (sporadic.unblock_check.all s3 t sc h3 hB3 hX3 hS3 hSg3 ht sc3.symm hsc0
            hAc) (sporadic.unblock_check.fr hW ⟨aR, oR⟩)) fun s4 hh => ?_
          obtain ⟨⟨h4, hB4, hX4, hS4, hSg4, ea4, -, -, f4, -⟩, w4⟩ := hh
          have fw4 : Foot st T Cs Sg Scs Z Es s3 s4 := Foot.of w4 fun b hb => by
            rcases hb with hb | rfl
            · exact hb.kw hsc
            · exact kw_node h3.cur (by rw [rp]; omega) (by rw [rp]; omega)
          exact ⟨⟨⟨Q3, R3, h4⟩, hB4, hX4, hS4, hSg4⟩, by rw [scA_eq, f4 t ht _ (by simp) (by simp), ← scA_eq]; exact sc3,
            by rw [ea4, ea3, ea2], fw3'.trans fw4⟩
        · exact ok3
      · exact ok3
    · exact ok3
  rintro s4 ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, sc4, ea4, fw4⟩
  -- resume
  have tc4 : L.mem s4 (scTcbA sc) = t := by
    have := (hX4.2.2.bound t ht (by rw [sc4]; exact hsc0)).2.1; rwa [sc4] at this
  have hres : sc ≠ 0#u64 → L.mem s4 (scTcbA sc) ≠ 0#u64 →
      L.mem s4 (scTcbA sc) ∈ T ∧ OutsideObjs st T Cs s4 (scCoreA sc) ∧ L.mem s4 (scCoreA sc) ∈ Cs ∧
        L.actionW s4 ≠ L.mem s4 (scTcbA sc) := fun _ _ => by
    rw [tc4]
    exact ⟨ht, h4.omega _ ((objs_omega hX4.1 hSg4.sub).2 sc hsc).2.1, hX4.2.2.core sc hsc,
      by rw [ea4]; exact hna⟩
  refine WP.spec_bind (WP.spec_and (schedcontext.resume.all hA s4 a1 sc Q4 R4 h4 hB4 hX4 hSg4 hS4 hres)
    (schedcontext.resume.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) hA s4 a1 sc Q4 R4 h4 hres)) ?_
  rintro ⟨s5, a2⟩ ⟨⟨Q5, R5, h5, hB5, hX5, hSg5, f5⟩, fw5⟩
  have hS5 := hS4.fr f5
  have fw5' : Foot st T Cs Sg Scs Z Es s s5 := fw4.trans fw5
  try simp only [WP.uncurry'_pair]
  -- enqueue if schedulable
  step with sched.is_schedulable.spec' as ⟨b3, eb3⟩
  split
  · rename_i hb3
    obtain ⟨hrun, hbd, hrl, hrm⟩ := eb3 hb3
    have hA5 : L.mem s5 (scA t) ∈ Ac := (hS5.act _ (hX5.2.2.bound t ht hbd).1).2 hrm
    refine WP.spec_bind (WP.spec_and (sched.enqueue.sch s5 t Q5 R5 h5 hB5 hSg5 ht (fun _ => hrl) (fun _ => hrun)
      (fun _ => hbd) (fun _ => hA5)) (sched.enqueue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s5 t h5 ht)) ?_
    rintro s6 ⟨⟨⟨⟨Q6, R6, h6⟩, hB6, f6⟩, -, -, -⟩, fw6⟩
    refine WP.spec_bind (WP.spec_and (sched.reschedule_required.sch s6 Q6 R6 h6 hB6 (hSg5.fr f6))
      (sched.reschedule_required.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s6 h6)) ?_
    rintro s7 ⟨⟨⟨⟨Q7, R7, h7⟩, hB7, f7⟩, -, -, -⟩, fw7⟩
    exact (WP.spec_ok _).2 ⟨⟨⟨Q7, R7, h7⟩, hB7, (hX5.fr f6).fr f7, (hS5.fr f6).fr f7, (hSg5.fr f6).fr f7⟩,
      fw5'.trans (fw6.trans fw7)⟩
  · exact (WP.spec_ok _).2 ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS5, hSg5⟩, fw5'⟩

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **`bind_tcb` at `J`** (module docstring): an SC of `Z.C` bound to no
thread, a thread with no SC (not idle), a blocked thread's SC released (the
decode's check), no switch pending and `CurInv`; the pair's caps in slots
(the invoked thread cap, the SC cap). -/
theorem JAtZ.bindTcbJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hAK : ARKeep arI AR) (hTA : TimeAgree arI)
    {sc t : U64} (hsC : sc ∈ Z.C) (ht : t ∈ Z.T) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext y n)) (hy0 : y.scTcb = none)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hxt0 : xt.tcbSchedContext = none)
    (hrel : Fl4Spec.ipcQueuedThreadState xt.tcbState = true → Fl4Spec.scReleased σ.curTime y = true)
    (hnsw : ∀ u, σ.schedulerAction ≠ .switchThread u) (hC : CurInv σ)
    (htid : t.bv ≠ σ.idleThread)
    {xs ys sb : U64} (hxS : IsSlot Z.th xs) (hxc : capAt (L.mem s) xs = ok (.Thread t))
    (hyS : IsSlot Z.th ys) (hyc : capAt (L.mem s) ys = ok (.SchedContext sc sb)) (hsb : sb.val < 64)
    (hssz : n + Fl4Spec.minSchedContextBits = sb.val) :
    schedcontext.bind_tcb st arI s a sc t ⦃ r => ∃ σ',
      Fl4Spec.schedContextBindTcb (Z := Unit) sc.bv t.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hsc0 : sc ≠ 0#u64 := J.c0 sc hsC
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hscH : sc ∈ P1.Heap.scs H := ⟨_, (hJ.sc sc y n hsc0 hk).2⟩
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  -- the thread is not the current one, the SC not the current SC
  obtain ⟨xc, hkc, hxcs, -⟩ := hC.tcb
  have htc : t.bv ≠ σ.curThread := fun e => by
    rw [← e, hkt] at hkc; cases hkc; rw [hxt0] at hxcs; cases hxcs
  have hscc : sc.bv ≠ σ.curSc := fun e => by
    obtain ⟨y1, n1, hk1, hb1⟩ := J.inv.back _ xc _ hkc hxcs
    rw [← e, hk] at hk1; cases hk1; rw [hy0] at hb1; cases hb1
  -- the release check
  have hact_of : Fl4Spec.ipcQueuedThreadState xt.tcbState = true → Fl4Spec.scActive y = true := fun h => by
    have h1 := hrel h
    unfold Fl4Spec.scReleased at h1; simp only [Bool.and_eq_true] at h1; exact h1.1
  have hblk : Fl4Spec.runnable xt.tcbState = false → inClassR xt.tcbState xt.tcbFault → Fl4Spec.scActive y = true →
      released σ y := by
    intro hr hcl ha
    have hq : Fl4Spec.ipcQueuedThreadState xt.tcbState = true := by
      rcases hcl.cls with h | ⟨m, h⟩ | ⟨e, d, h⟩ | ⟨e, r, d, h⟩
      · rw [h] at hr; cases hr
      all_goals rw [h]; rfl
    have h1 := hrel hq
    unfold Fl4Spec.scReleased at h1; simp only [Bool.and_eq_true] at h1
    exact ⟨h1.2, J.inv.suff hk ha⟩
  -- FL4's side of the decode's checks
  obtain ⟨x', hk', -, -, hscw, -⟩ := hs.tcb t ht
  rw [hkt] at hk'; cases hk'
  have ht0 : L.mem s (P1.scA t) = 0#u64 := Notif.optRef_none (by rw [← hscw]; exact hxt0)
  obtain ⟨y', n', hk2, hx⟩ := hs.scs sc hsC
  rw [hk] at hk2; cases hk2
  have hc0 : L.mem s (P1.scTcbA sc) = 0#u64 := by
    rw [scTcbA_eq]; exact Notif.optRef_none (by rw [← hx.tcb]; exact hy0)
  have hbA : P1.BlockedR (L.mem s (P1.stA t)) → sc ∈ Ac := fun hb => by
    have hq := blockedR_queued (hR.at_tcb ht hkt).st hb
    have hrm := SchedRel.act_sc hS hsC hk (hact_of hq)
    exact (J.blk.2.2.2.1.act _ hscH).2 (fun h => hrm (by rw [h]; rfl))
  have hA0 : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  have haff : L.mem s (P1.affA t) = L.mem s (P1.scCoreA sc) := by
    rw [hc.aff t ht, scCoreA_eq, hS.core sc hsC]
  refine WP.spec_mono (WP.spec_and (bind_tcb_refines s a σ hS hR J.nsc J.inv hsC hsc0 hk hy0 ht hkt hxt0 hblk hTA)
    (WP.spec_and (P1.schedcontext.bind_tcb.blkK (Es := ∅) hAT s a sc t J.blk htH hscH hsc0 ht0 hc0 hbA haff)
      (AK.schedcontext_bind_tcb (P1.LawfulStore.total (st := st)) hAT hAK hA0))) ?_
  rintro ⟨s', a'⟩ ⟨⟨σ', he, hS', hR', hN', hI', -, hwk⟩, ⟨hblk', hfD⟩, hA'⟩
  have hDbg := J.kw_dbg (P1.Foot.mono hfD (Set.empty_subset _))
  have hKd := J.kw_dbgKeep (P1.Foot.mono hfD (Set.empty_subset _))
  have hm : ((), σ') ∈ (Fl4Spec.schedContextBindTcb (Z := Unit) sc.bv t.bv σ).1 := by
    rw [he]; exact Set.mem_singleton _
  have hWk : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ) := hwk
  have hW : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) := Sched.WritesIn.tfoot_of_kfoot hWk
  have hK : ScTKw (fun _ => False) σ σ' := nkt_schedContextBindTcb sc.bv t.bv σ ((), σ') hm
  have hX' : XTopAt (L := L) AR Z s' a' σ' :=
    xtop_sc_step (ct := σ.curThread) hX J.ip J.nk hW (hK.mono fun _ h => h.elim) hS' hR' (fun _ => hA')
  have hall := ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree
    ⟨⟨hS', hR', hN', hI'⟩, hWk, (pres_schedContextBindTcb (true, true) _ _).of_eq he⟩
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ := hall
  -- the mid-entry facts
  have hMid : MidK σ σ' := mka_schedContextBindTcb sc.bv t.bv σ ⟨hscc, htc, htid⟩ _ hm
  have hcT : ∃ u ∈ Z.T, u.bv = σ.curThread := ⟨_, hc.curT, hs.curThread.symm⟩
  obtain ⟨hC', hOw', hO', hAI'⟩ := hMid.midN (T := Z.T) hnsw hC J.off J.act J.inv hcT
  have hF : FK σ σ' := ⟨hMid.csc, hMid.idle, hMid.isc⟩
  have hcr' : CurRunM σ' := hMid.curRunM hnsw hC J.curRun
  have hB' : BlockedScActive σ' := by
    refine J.bsa.bk (bka_schedContextBindTcb sc.bv t.bv σ (fun y2 n2 hy2 => ?_) _ hm)
      ((pres_schedContextBindTcb (true, true) _ _).of_eq he)
    rw [hk] at hy2; cases hy2
    by_cases hq : Fl4Spec.ipcQueuedThreadState xt.tcbState = true
    · exact Or.inl (hact_of hq)
    · exact Or.inr (fun x hx => by rw [hkt] at hx; cases hx; simpa using hq)
  -- the dead set: links cut only at the pair, which is covered by its caps
  have hL : LK (fun p => p = sc.bv ∨ p = t.bv) σ σ' := lkm_schedContextBindTcb sc.bv t.bv σ _ hm
  have hH := J.kern.heap
  have covT : (∀ k, Z.th t = some k → Sched.Covered (L.mem s') Z.G t.val (t.val + max (objSize k) 1)) ∧
      (∀ k, H t = some k → Sched.Covered (L.mem s') Z.G t.val (t.val + 2 ^ k.bits)) := by
    have hHt : H t = some .tcb := J.zH.1 t ht
    have hfit := hH.fits t _ hHt
    simp only [P1.HKind.bits] at hfit
    exact J.cover_cap hW hxS hxc (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl (range_thread t hfit)
      fun k hk' => by
        rw [hHt] at hk'; cases hk'
        exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  have covS : (∀ k, Z.th sc = some k → Sched.Covered (L.mem s') Z.G sc.val (sc.val + max (objSize k) 1)) ∧
      (∀ k, H sc = some k → Sched.Covered (L.mem s') Z.G sc.val (sc.val + 2 ^ k.bits)) := by
    have hHs := (hJ.sc sc y n hsc0 hk).2
    have hfit := hH.fits sc _ hHs
    simp only [P1.HKind.bits] at hfit
    rw [hssz] at hfit
    refine J.cover_cap hW hyS hyc (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
      (range_sc sc sb hsb hfit) fun k hk' => ?_
    rw [hHs] at hk'; cases hk'
    exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  have hDead : ∀ q ∈ {q : U64 | q ∈ D ∧ ¬ (q.bv = sc.bv ∨ q.bv = t.bv)}, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_step hX' hW hK (fun _ _ h => h.elim) hL hF hAI'.1 hY'
      ((((pres_schedContextBindTcb (true, true) _ _).of_eq he).ykeep rfl).dk q.bv) hq.2 (J.jcov.dead q hq.1)
  have hCov : ∀ q ∈ D, q ∉ {q : U64 | q ∈ D ∧ ¬ (q.bv = sc.bv ∨ q.bv = t.bv)} →
      (∀ k, Z.th q = some k → Sched.Covered (L.mem s') Z.G q.val (q.val + max (objSize k) 1)) ∧
      (∀ k, H q = some k → Sched.Covered (L.mem s') Z.G q.val (q.val + 2 ^ k.bits)) := fun q hq hn => by
    have hw : q.bv = sc.bv ∨ q.bv = t.bv := by_contra fun h => hn ⟨hq, h⟩
    rcases hw with e | e
    · rw [bv_inj e]; exact covS
    · rw [bv_inj e]; exact covT
  have hIK := J.idleW_keep hS' hF.2.1 hF.2.2
  have hsub : {q : U64 | q ∈ D ∧ ¬ (q.bv = sc.bv ∨ q.bv = t.bv)} ⊆ D := fun q h => h.1
  have hjc := J.sc_jcov hW hDead hCov hIK hKd hsub
  have hkern := J.sc_kern hW hK hF hX' hDbg hsub
  exact ⟨σ', he, Ac, Lst', {q : U64 | q ∈ D ∧ ¬ (q.bv = sc.bv ∨ q.bv = t.bv)}, J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK hIK.2) hjc hkern (J.sc_utc hW hK hDbg) hN' hI' hC'
    (Or.inl (hC'.elim hOw' (curOwn_of_curInv hS' hI'))) hO' hAI' hB' hcr' hblk'
    hKd hIK.1 (fun p hp => ⟨J.zD p hp, fun e => by
      rcases e with e | e
      · exact J.not_ztcb hyS (fun _ _ _ h => by rw [capV_of_capAt hyc] at h; cases h)
          (by rw [capV_of_capAt hyc, bv_inj e]; simp [absCap, Fl4Spec.objRefs]) hp
      · exact J.not_ztcb hxS (fun _ _ _ h => by rw [capV_of_capAt hxc] at h; cases h)
          (by rw [capV_of_capAt hxc, bv_inj e]; simp [absCap, Fl4Spec.objRefs]) hp⟩)⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64}

set_option maxRecDepth 8000 in
/-- **`cdt::empty_slot` of a slot keeps every other slot's cap** (from any
state agreeing with `s` on P1's `CapW` words), with the `CapW` footprint
(ScInstFoot's `inst_hslot` with the caps: `empty_ws`, `empty_slot_mem`). -/
theorem empty_capV_frame {th : TypedHeap} (hP : Placed th) {T Ω Sg : Set U64} (hSC : SlotCapW th T Ω Sg) {s : S}
    {G : MdbGhost} (hM : MdbLinks th (L.mem s) G) {root : U64} (hr : IsSlot th root) :
    ∀ (s1 : S) (a1 : A), (∀ b, P1.Aligned b → P1.CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st arI s1 a1 root .Null ⦃ r => P1.WritesIn st s1 r.1 (P1.CapW T Ω Sg) ∧
        ∀ y, IsSlot th y → y ≠ root → capV (L.mem r.1) y = capV (L.mem s) y ⦄ := by
  intro s1 a1 hag
  have hSS : SlotsSame th (L.mem s) (L.mem s1) := fun a ha => by
    have w : ∀ k, Off k → L.mem s1 (wordOf a k) = L.mem s (wordOf a k) := fun k hk =>
      hag _ (slot_word_aligned hP ha hk) (hSC _ ⟨a, ha, k, hk, rfl⟩)
    refine ⟨by have := w _ off0; rwa [wordOf_zero] at this, w _ off8, w _ off16, w _ off24⟩
  have hM1 := hM.of_same hSS
  have hslot : ∀ y, y ∈ G.chains.flatten → IsSlot th y := fun y h => ((hM1.members y).1 h).1
  have hWm : ∀ {s' s'' : S}, P1.WritesIn st s' s'' (SlotWd th) → P1.WritesIn st s' s'' (P1.CapW T Ω Sg) :=
    fun h => h.mono hSC
  by_cases hcn : capV (L.mem s1) root = .Null
  · rw [empty_slot_null arI s1 a1 root (by rw [capAt_capV, hcn]) .Null]
    exact (WP.spec_ok _).2 ⟨P1.WritesIn.refl _ _, fun y hy _ => hSS.capV hy⟩
  have hxm := (hM1.members root).2 ⟨hr, _, capAt_capV _ _, hcn⟩
  have hnx : nextOf (L.mem s1) root = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s1) root) ∧ nextOf (L.mem s1) root ≠ root) := by
    rcases hM1.next_mem hxm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, h2⟩
  have hpv : prevOf (L.mem s1) root = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s1) root) ∧ prevOf (L.mem s1) root ≠ root) := by
    by_cases h0 : prevOf (L.mem s1) root = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM1.prev_link hxm h0
      refine Or.inr ⟨hslot _ h1, fun e => ?_⟩
      rw [e] at h2
      rcases hM1.next_mem hxm with h | ⟨-, h⟩
      · rw [h] at h2; exact hr.ne_zero hP h2.symm
      · exact h h2
  have hPN := hM1.prev_ne_next hP hxm
  have hNc : Canonical (nextOf (L.mem s1) root) := by
    rcases hnx with h | ⟨h, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  refine WP.spec_mono (WP.spec_and (empty_ws hP s1 a1 root hr (hpv.imp_right And.left) (hnx.imp_right And.left))
    (empty_slot_mem hP s1 a1 root hr _ (capAt_capV _ _) hcn hpv hnx hPN)) ?_
  rintro r ⟨hw, hW, -⟩
  refine ⟨hWm hw, fun y hy hne => ?_⟩
  have h := hW.capAt' hy
  rw [if_neg hne, capAt_capV, capAt_capV] at h
  rw [Result.ok_injective h]
  exact hSS.capV hy

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **`set_priority` at `J` with its frames** (`JAtZ.setPrioJ`): the spec's
`PFr` (`setPriority_pfr`) and the slots kept (`set_priority_irelW`'s
footprint `CnW`, words of the objects outside the slots). -/
theorem JAtZ.setPrioJS (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hna : ∀ u, σ.schedulerAction ≠ .switchThread u) {t : U64} (ht : t ∈ Z.T) (v : U64) (hv : v.val < 256)
    (hcur : σ.curThread = t.bv → t.bv ∉ σ.releaseQueue ∧ ∃ x scp y n, σ.kheap t.bv = some (.tcb x) ∧
      x.tcbSchedContext = some scp ∧ σ.kheap scp = some (.schedContext y n) ∧ Fl4Spec.scActive y = true)
    (hP1 : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (P1.inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (P1.scA t) ≠ 0#u64 ∧ L.mem s (P1.scA t) ∈ Ac) :
    sched.set_priority st s t v ⦃ s' => ∃ σ',
      Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
      PFr t.bv σ σ' ∧ SlotsSame Z.th (L.mem s) (L.mem s') ∧
      ∃ V' : XVs, JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a σ' ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  have hQ := qSorted_of_spec (L := L) hI.1.toE hI.1.toN hP0.e.tcb J.isorted
  obtain ⟨x, hk, -⟩ := hI.1.toE.tcb t ht
  refine WP.spec_mono (WP.spec_and (J.setPrioJ hna ht v hv hcur hP1) (set_priority_irelW hP0 hI ht v hv
    J.inv.actReady (fun h => (hcur h).1) J.sv J.inv J.obj (fun e he => hQ e (Or.inl he))
    (fun e he => hQ e (Or.inr he)))) ?_
  rintro s' ⟨⟨σ', hm, V', J'⟩, ⟨σ'', hm', -, hw⟩⟩
  have e : σ' = σ'' :=
    (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst (hm.symm.trans hm')))).2
  subst e
  have hm1 : ((), σ') ∈ (Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ).1 := by
    rw [hm]; exact Set.mem_singleton _
  exact ⟨σ', hm, setPriority_pfr hk _ hna (blkQ_of_sv J.sv hk) J.sv _ hm1,
    J.xtop.slotsSame_of hw (fun b h => CnW.oobj J.xtop.fin.1.1.1 h), V', J'⟩

/-- A TCB's `MCP` word is no slot word: its write keeps the slots. -/
theorem JAtZ.mcp_slots (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (v : U64) :
    SlotsSame Z.th (L.mem s) (L.mem (L.wr s (mcpA t) v)) := by
  have hT : P1.TcbPlaced Z.T := J.ip.e.tcb
  have hKt : (mcpA t).val = t.val + 3440 := mcpA_val hT ht
  refine J.xtop.slotsSame_of (P1.writesIn_wr (mcpA_aligned hT ht)) fun b hb => ?_
  subst hb
  exact Or.inr (Or.inr (Or.inl ⟨t, ht, by omega, by omega⟩))

end

/-! ## The spec's side of the fault-handler install -/

section
open Fl4Spec

/-- **`SpecPost` across the spec's fault-handler install** over a slot holding
the null cap or an endpoint cap (ScInstPost's `schedTailHyp_disch`'s
`hpost2`: `install_sk` when null or not final, `finEpSpecHyp` when final). -/
theorem specPost_install {σ1 σ2 : State Unit} {p : ObjRef} {x1 : Tcb} {sco : Option (Option ObjRef)}
    {ssl : CslotPtr} {fh : Cap × CslotPtr} {c : capability.Cap} (hk1 : σ1.kheap p = some (.tcb x1))
    (hfc : x1.tcbFaultHandler = absCap c) (hc : c = .Null ∨ ∃ ep b0 b1 b2 b3 b4, c = .Endpoint ep b0 b1 b2 b3 b4)
    (hx : (.ok (), σ2) ∈ ((installTcbCap (Z := Unit) p ssl 3 (some fh)).run σ1).1)
    (hpost : SpecPost σ1 p sco) : SpecPost σ2 p sco := by
  rcases hc with hc0 | ⟨ep, b0, b1, b2, b3, b4, hce⟩
  · exact hpost.sk (install_sk hk1 ssl fh (Or.inl (by rw [hfc, hc0]; rfl)) hx)
  · by_cases hfin : isFinalCap' x1.tcbFaultHandler σ1
    · exact finEpSpecHyp σ1 σ2 p x1 ssl fh sco hk1 ⟨_, _, _, by rw [hfc, hce]; rfl⟩ hfin hx hpost
    · refine hpost.sk (install_sk hk1 ssl fh (Or.inr ⟨by rw [hfc, hce]; simp [absCap], c, hfc,
        by rw [hce]; simp, ?_⟩) hx)
      rw [hce]
      exact ⟨rfl, by rw [← hce, ← hfc]; exact hfin⟩

/-- **What the spec's fault-handler install keeps of the scheduler** (over a
slot holding the null cap or an endpoint cap, from an `Inv` state; from
ScInstPost's `install_ik`): `CurInv` (the current thread, its SC and state,
the current SC, activity and the release queue), the time, the idle thread,
every SC bound to no thread (no TCB names it by `Inv.back`, and
`cancel_all_ipc` refill-checks only each waiter's own SC), and the target's
IPC-blocked state (it can only be restarted or made inactive). -/
theorem install_sched (σ1 σ2 : State Unit) (p : ObjRef) (x : Tcb) (ssl : CslotPtr) (fh : Cap × CslotPtr)
    (hk : σ1.kheap p = some (.tcb x))
    (hfh : x.tcbFaultHandler = .nullCap ∨ ∃ e b R, x.tcbFaultHandler = .endpointCap e b R) (hI : Inv σ1)
    (hx : (.ok (), σ2) ∈ ((installTcbCap (Z := Unit) p ssl 3 (some fh)).run σ1).1) :
    (CurInv σ1 → CurInv σ2) ∧ σ2.curTime = σ1.curTime ∧ σ2.idleThread = σ1.idleThread ∧
    (∀ c y n, σ1.kheap c = some (.schedContext y n) → y.scTcb = none →
      σ2.kheap c = some (.schedContext y n)) ∧
    (∀ x2, σ2.kheap p = some (.tcb x2) → ipcQueuedThreadState x2.tcbState = true → x2.tcbState = x.tcbState) := by
  have K := install_ik hk ssl fh hfh hx
  obtain ⟨hcs, htm, hid, his⟩ := K.fk
  refine ⟨fun hC => ?_, htm, hid, fun c y n hy hy0 => K.scU c y n hy fun u xu hu hc => ?_, fun x2 hx2 hq => ?_⟩
  · obtain ⟨xt, hkt, hsc, hnb⟩ := hC.tcb
    obtain ⟨yt, hyt, sr, hs⟩ := K.tcb _ xt hkt
    obtain ⟨y0, n0, hy0⟩ := hC.sc
    obtain ⟨y0', hy0', hm⟩ := K.sc _ y0 n0 hy0
    refine ⟨⟨yt, by rw [K.ct]; exact hyt, by rw [hs, hcs]; exact hsc, ?_⟩, ⟨y0', n0, by rw [hcs]; exact hy0'⟩,
      fun hne y1 n1 hy1 => ?_, by rw [K.ct, K.rel]; exact hC.notRel⟩
    · rcases sr with e | e | e <;> rw [e]
      · exact hnb
      all_goals exact ⟨fun q h => (by cases h), fun e d h => (by cases h), fun e r d h => (by cases h)⟩
    · rw [hcs, his] at hne
      rw [hcs, hy0'] at hy1; cases hy1
      have := hC.active hne y0 n0 hy0
      simpa [scActive, hm] using this
  · obtain ⟨y1, n1, hk1, hb1⟩ := hI.back u xu c hu hc
    rw [hy] at hk1; cases hk1
    rw [hy0] at hb1; cases hb1
  · obtain ⟨y, hy, sr, -⟩ := K.tcb p x hk
    rw [hx2] at hy; cases hy
    rcases sr with e | e | e
    · exact e
    all_goals rw [e] at hq; simp [ipcQueuedThreadState] at hq

end


end

end Fl4Proofs.P3
