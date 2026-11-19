/-
P3 (DESIGN.md §9), TCB: **`JAtZ` across a final thread cap's finalisation
without `JThreadFinHyps.utTcb`** (toward carrying XTopJointLive's `LiveJ`
through the deletion loop instead of XTopJointDelR's `JDelParts.live`).

XTopJointFinThread's `JAtZ.finThreadJ` reads `JThreadFinHyps.utTcb` (a
∀-`JAtZ` premise) once, at the state after `suspend`, for `debug_remove`
(`JAtZ.dbgRemoveJ`). `JAtZ.finThreadJU` is the same proof with each step
paired with its P1 footprint (`WP.spec_and`: `unbind_notification.blkF`,
`timer.remove.tf`, `unbind_tcb.blk`, `complete_yield_to.blk`,
`suspend.blk`), so it needs that fact only at states reached from the start
by a `KW` footprint (`DbgSuccCov`, `hU`). `JAtZ.dbgSuccCov_of_live` gives
it from `LiveJ` at the start: a `KW` footprint keeps the debug words
(`Foot.dbgKeep`) and the cap-slot words (`footD_keeps_capw`), so the head's
successor is still named by the same thread cap (`LiveJ.dbg` at `1`).
-/
import Fl4Proofs.P3.XTopJointLiveKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **Core 0's debug-list successor of the head covered by a cap** (the
fact `JAtZ.dbgRemoveJ` reads, `JThreadFinHyps.utTcb`'s conclusion). -/
abbrev DbgSuccCov (T : Set U64) (G : MdbGhost) (s : S) : Prop :=
  L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ∈ T →
    L.mem s (P1.dnA (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))) ≠ 0#u64 →
    Covered (L.mem s) G (L.mem s (P1.dnA (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)))).val
      ((L.mem s (P1.dnA (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)))).val + 1)

/-- The `KW` footprint of `H`'s blocking-object steps, from `s`. -/
abbrev FootH (H : P1.Heap) (Cs Es : Set U64) (s s' : S) : Prop :=
  P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Es s s'

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **`DbgSuccCov` after a `KW` footprint, from `LiveJ`** (module
docstring). -/
theorem JAtZ.dbgSuccCov_of_live (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hL : LiveJ (L := L) Z.th H Z.G s σ) {s' : S} (f : FootH (st := st) H Cs (P1.EH H) s s') :
    DbgSuccCov (L := L) Z.T Z.G s' := by
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' := P1.Foot.dbgKeep J.blk (fun _ h => h) f
  have hcw := P1.footD_keeps_capw J.blk (le_refl _) f.d
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    slotsSame_of_capw J.xtop.rel.1 (J.slotCapW (tLowSlots_all _)) hcw
  have hhd : dbgHead (L := L) s' = dbgHead (L := L) s := by
    unfold dbgHead
    rw [nodeAt_of_ksb hK.1]
    exact hK.2 _ (Or.inr ⟨0#u64, J.kern.cs0, rfl⟩)
  show dbgHead (L := L) s' ∈ Z.T → L.mem s' (P1.dnA (dbgHead (L := L) s')) ≠ 0#u64 →
    Covered (L.mem s') Z.G (L.mem s' (P1.dnA (dbgHead (L := L) s'))).val
      ((L.mem s' (P1.dnA (dbgHead (L := L) s'))).val + 1)
  rw [hhd]
  intro hT hn
  have hdn : L.mem s' (P1.dnA (dbgHead (L := L) s)) = L.mem s (P1.dnA (dbgHead (L := L) s)) :=
    hK.2 _ (Or.inl ⟨_, by rw [← hTe]; exact hT, Or.inl rfl⟩)
  rw [hdn] at hn ⊢
  have h0 : dbgHead (L := L) s ≠ 0#u64 := by
    intro e
    have h1 := J.zH.1 _ hT
    rw [e, J.kern.h0] at h1
    cases h1
  have e1 : dbgNth (L.mem s) 1 (dbgHead (L := L) s) = L.mem s (P1.dnA (dbgHead (L := L) s)) := by
    simp only [dbgNth, if_neg h0]
  obtain ⟨y, hy, hT'⟩ := hL.dbg 1 (by rw [e1]; exact hn)
  rw [e1] at hT'
  obtain ⟨y', hy', h1, h2, h3, h4⟩ := J.thread_cover hy hT'
  have hys : IsSlot Z.th y' := ((J.xtop.rel.2.1.2.2.1.members y').1 hy').1
  rw [← hSS.capV hys] at h1 h2 h3 h4
  exact ⟨y', hy', h1, h2, h3, h4⟩

set_option maxHeartbeats 16000000 in
/-- **`JAtZ` across a final thread cap's finalisation, `utTcb` only after a
`KW` footprint** (module docstring; XTopJointFinThread's `finThreadJ`
with `hU` for `JThreadFinHyps.utTcb`). -/
theorem JAtZ.finThreadJU (hAT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hU : ∀ s', FootH (st := st) H Cs (P1.EH H) s s' → DbgSuccCov (L := L) Z.T Z.G s')
    {p : U64} (hp : p ∈ Z.T)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) (hna : L.actionW s ≠ p) (hidle : L.idleW s ≠ p) :
    objects.finalise_cap st arI s a (.Thread p) true false ⦃ r => ∃ σ',
      ((Fl4Spec.Cap.zombie p.bv none 6, Fl4Spec.Cap.nullCap), σ') ∈
        (Fl4Spec.finaliseCap (Z := Unit) (.threadCap p.bv) true σ).1 ∧
      JTP (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
  have hfc : objects.finalise_cap st arI s a (.Thread p) true false =
      objects.finalise_cap_object st arI s a (.Thread p) true := by
    simp [objects.finalise_cap]
  rw [hfc]
  unfold objects.finalise_cap_object
  simp only [↓reduceIte]
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hpT : p ∈ P1.Heap.tcbs H := by rw [← hTe]; exact hp
  have hS0 := J.xtop.fin.1.1.1
  obtain ⟨hsa, hid⟩ := J.spec_of_words hna hidle
  -- the remote stall and the VCPU detach
  refine WP.spec_bind (remote_tcb_stall_id (ar := arI) a hS0 hp) ?_
  rintro ⟨s1, a1⟩ he1
  simp only [Prod.mk.injEq] at he1
  obtain ⟨hs1, ha1⟩ := he1
  subst s1; subst a1
  refine WP.spec_bind (vcpu_detach_none arI s a p hv0) ?_
  rintro ⟨s1, a1⟩ he1
  simp only [Prod.mk.injEq] at he1
  obtain ⟨hs1, ha1⟩ := he1
  subst s1; subst a1
  -- `unbind_notification`
  have h3 : notification.unbind_notification st s p ⦃ s3 => ∃ σ3,
      Fl4Spec.unbindNotification (Z := Unit) p.bv σ = ({((), σ3)}, False) ∧
      σ3.schedulerAction = σ.schedulerAction ∧ σ3.idleThread = σ.idleThread ∧ σ3.curThread = σ.curThread ∧
      JTP (L := L) arI AR Z H Cs s3 a σ3 ⦄ := by
    by_cases h0 : L.mem s (P1.boundA p) = 0#u64
    · rw [unbind_ntfn_zero s p h0, WP.spec_ok]
      have hI0 := J.xtop.irelK J.ks J.buf
      obtain ⟨x, hk, hx⟩ := hI0.1.tcb p hp
      refine ⟨σ, unbindNtfn_none hk ?_, rfl, rfl, rfl, Z.vs, Ac, Lst, D, J⟩
      rw [hx.bound, show tBoundA p = P1.boundA p from rfl, h0, Notif.optRef_zero]
    · exact J.unbindNJ hp h0
  refine WP.spec_bind (WP.spec_and h3 (P1.notification.unbind_notification.blkF s p J.blk hpT)) ?_
  rintro s3 ⟨⟨σ3, he3, ha3, hi3, hc3, V3, Ac3, Lst3, D3, J3⟩, -, f3, -⟩
  -- the timer-tree removal
  refine WP.spec_bind (WP.spec_and (J3.tmRemoveJ hp)
    (P1.timer.remove.tf (s0 := s3) s3 p (P1.TF.start (P1.BlkOK.tinv J3.blk)) hpT)) ?_
  rintro s4 ⟨J4, -, f4, -⟩
  have f34 : FootH (st := st) H Cs ∅ s s4 := f3.trans f4
  -- the rest, after `unbind_from_sc`
  have fin6 : ∀ (s5 : S) (a5 : A) (σ5 : Fl4Spec.State Unit), JTP (L := L) arI AR Z H Cs s5 a5 σ5 →
      Fl4Spec.unbindFromSc (Z := Unit) p.bv σ3 = ({((), σ5)}, False) →
      σ5.curThread = σ.curThread ∧ σ5.idleThread = σ.idleThread ∧
        (σ5.schedulerAction = σ.schedulerAction ∨ σ5.schedulerAction = .chooseNewThread) →
      FootH (st := st) H Cs ∅ s s5 →
      (do
        let (s6, a4) ← sched.suspend st arI s5 a5 p
        let s7 ← objects.debug_remove st s6 p
        let a6 ← arI.fpu_release a4 p
        let s8 ← obj.Tcb.slot p layout.tcb.SLOT_CTABLE
        ok ((capability.Cap.Zombie s8 capability.ZOMBIE_TCB layout.tcb.NUM_SLOTS, capability.Cap.Null), s7, a6))
        ⦃ r => ∃ σ', ((Fl4Spec.Cap.zombie p.bv none 6, Fl4Spec.Cap.nullCap), σ') ∈
            (Fl4Spec.finaliseCap (Z := Unit) (.threadCap p.bv) true σ).1 ∧
          JTP (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
    rintro s5 a5 σ5 ⟨V5, Ac5, Lst5, D5, J5⟩ he5 ⟨hc5, hi5, ha5⟩ f5
    have hsa5 : ∀ u, σ5.schedulerAction = .switchThread u → u ≠ p.bv := fun u hu => by
      rcases ha5 with e | e
      · exact hsa u (by rw [← e]; exact hu)
      · rw [e] at hu; cases hu
    have hid5 : p.bv ≠ σ5.idleThread := by rw [hi5]; exact hid
    have na5 : L.actionW s5 ≠ p := (J5.words_of_spec hp hsa5 hid5).1
    refine WP.spec_bind (WP.spec_and
      (JAtZ.suspendJ (Z := Z.mv Z.G V5) (jCancel_send arI) (jCancel_ntfn arI) (jCancel_recv arI)
        (jCancel_reply arI) J5 hp hsa5 hid5)
      (P1.sched.suspend.blk s5 a5 p J5.blk hpT na5)) ?_
    rintro ⟨s6, a6⟩ ⟨⟨ha6, σ6, he6, V6, Ac6, Lst6, D6, J6⟩, hb6⟩
    have f6 : FootH (st := st) H Cs (P1.EH H) s5 s6 := hb6.2
    simp only at ha6
    subst ha6
    refine WP.spec_bind (J6.dbgRemoveJ (hU s6 ((f5.mono (Set.empty_subset _)).trans f6)) hp) ?_
    intro s7 J7
    refine WP.spec_bind (J7.fpuReleaseJ hK hp) ?_
    rintro a8 ⟨σ8, hm8, V8, J8⟩
    simp only [P1.tcb_slot_ctable, bind_ok, WP.spec_ok]
    exact ⟨σ8, finThread_mem he3 he5 he6 hm8, V8, Ac6, Lst6, D6, J8⟩
  -- `unbind_from_sc`
  obtain ⟨Q4, R4, hc4, hs4⟩ := J4.xtop.fin.1.1.1.lists
  obtain ⟨x4, hk4, -, -, hsc4, -⟩ := hs4.tcb p hp
  step with obj.Tcb.sc.spec as ⟨i, hi⟩
  step with obj.Sc.is_null.spec' as ⟨b, hb⟩
  by_cases h0 : i = 0#u64
  · have hb' : b = true := by rw [hb, h0]; rfl
    simp only [hb', ↓reduceIte, bind_ok]
    exact fin6 s4 a σ3 ⟨V3, Ac3, Lst3, D3, J4⟩ (unbindFromSc_none hk4 (by rw [hsc4, ← hi, h0, Notif.optRef_zero]))
      ⟨hc3, hi3, Or.inl ha3⟩ f34
  have hb' : b = false := by rw [hb]; simp [h0]
  simp only [hb', Bool.false_eq_true, ↓reduceIte]
  have hiC : i ∈ Z.C := by rw [hi]; exact hs4.scMem p hp (by rw [← hi]; exact h0)
  have hsp : x4.tcbSchedContext = some i.bv := by rw [hsc4, ← hi, Notif.optRef_ne h0]
  have hsa3 : ∀ u, σ3.schedulerAction = .switchThread u → u ≠ p.bv := by rw [ha3]; exact hsa
  have hid3 : p.bv ≠ σ3.idleThread := by rw [hi3]; exact hid
  obtain ⟨na4, ni4⟩ := J4.words_of_spec hp hsa3 hid3
  obtain ⟨hiS, hit, -⟩ := J4.blk.2.2.1.2.2.bound p hpT (by rw [← hi]; exact h0)
  rw [← hi] at hiS hit
  have hin : (do
      let s6 ← schedcontext.unbind_tcb st s4 i
      let i1 ← obj.Sc.yield_from st i s6
      let b1 ← obj.Tcb.is_null i1
      if b1 = true then ok (s6, a) else schedcontext.complete_yield_to st arI s6 a i1) ⦃ r =>
      ∃ σ5, JTP (L := L) arI AR Z H Cs r.1 r.2 σ5 ∧
        Fl4Spec.unbindFromSc (Z := Unit) p.bv σ3 = ({((), σ5)}, False) ∧
        σ5.curThread = σ.curThread ∧ σ5.idleThread = σ.idleThread ∧
        (σ5.schedulerAction = σ.schedulerAction ∨ σ5.schedulerAction = .chooseNewThread) ∧
        FootH (st := st) H Cs ∅ s r.1 ⦄ := by
    refine WP.spec_bind (WP.spec_and (J4.unbindTcbJ hp hiC hk4 hsp hsa3 hid3)
      (P1.schedcontext.unbind_tcb.blk s4 i J4.blk hiS h0 (fun _ => by rw [hit]; exact na4)
        (fun _ => by rw [hit]; exact ni4))) ?_
    rintro s5 ⟨⟨σ4, he4, Ac5, Lst5, D5, J5⟩, -, f5, -⟩
    have f45 : FootH (st := st) H Cs ∅ s s5 := f34.trans f5
    have hca4 : σ4.curThread = σ.curThread ∧ σ4.idleThread = σ.idleThread ∧
        (σ4.schedulerAction = σ.schedulerAction ∨ σ4.schedulerAction = .chooseNewThread) := by
      obtain ⟨y', n', hky', hyt'⟩ := J4.inv.back p.bv x4 i.bv hk4 hsp
      obtain ⟨σ4', e4', -, -, -, ct4, -, -, -, idl4, -, -, a14, b14⟩ :=
        Sched.unbindTcb_shape J4.inv.actReady hky' hyt' hk4
      have e := the_result e4' he4
      subst e
      refine ⟨ct4.trans hc3, idl4.trans hi3, ?_⟩
      by_cases hpc : p.bv = σ3.curThread
      · exact Or.inr (a14 hpc)
      · exact Or.inl ((b14 hpc).trans ha3)
    obtain ⟨Q5, R5, hc5, hs5⟩ := J5.xtop.fin.1.1.1.lists
    obtain ⟨y5, n5, hk5, hx5⟩ := hs5.scs i hiC
    step with obj.Sc.yield_from.spec' as ⟨j, hj⟩
    step with obj.Tcb.is_null.spec as ⟨b1, hb1⟩
    by_cases j0 : j = 0#u64
    · have hb1' : b1 = true := by rw [hb1, j0]; rfl
      simp only [hb1', ↓reduceIte, WP.spec_ok]
      refine ⟨σ4, ⟨V3, Ac5, Lst5, D5, J5⟩, unbindFromSc_some hk4 hsp he4 hk5 ?_, hca4.1, hca4.2.1, hca4.2.2, f45⟩
      rw [hx5.yieldFrom, ← scYieldFromA_eq, ← hj, j0, Notif.optRef_zero]; rfl
    · have hb1' : b1 = false := by rw [hb1]; simp [j0]
      simp only [hb1', Bool.false_eq_true, ↓reduceIte]
      rw [hj]
      have hjT : L.mem s5 (scYieldFromA i) ∈ Z.T := by
        have e5 : y5.scYieldFrom = some (L.mem s5 (scYieldFromA i)).bv := by
          rw [hx5.yieldFrom, ← scYieldFromA_eq, Notif.optRef_ne (by rw [← hj]; exact j0)]
        obtain ⟨t, ht, et, -⟩ := J5.yld.frm i hiC y5 n5 hk5 _ e5
        rw [← P1.eq_of_bv et]; exact ht
      refine WP.spec_mono (WP.spec_and (J5.completeYieldJ hAT hticks.1 (hticks.2 a) hjT)
        (P1.schedcontext.complete_yield_to.blk hAT s5 a _ J5.blk (fun _ => by rw [← hTe]; exact hjT))) ?_
      rintro ⟨s6, a6⟩ ⟨⟨σ6, e6, V6, Ac6, Lst6, D6, J6⟩, hb6⟩
      have f6 : FootH (st := st) H Cs ∅ s5 s6 := hb6.2.1
      obtain ⟨xj, hkj, eyj⟩ := J5.yld.tcb _ hjT
      have hqj : ∀ q, xj.tcbYieldTo = some q → ∃ z n, σ4.kheap q = some (.schedContext z n) := by
        intro q hq
        by_cases h0 : L.mem s5 (yieldA (L.mem s5 (scYieldFromA i))) = 0#u64
        · rw [eyj, h0, Notif.optRef_zero] at hq; cases hq
        · obtain ⟨-, z, n, hkz, -⟩ := J5.yld.toSc _ hjT h0
          rw [eyj, Notif.optRef_ne h0] at hq; cases hq; exact ⟨z, n, hkz⟩
      obtain ⟨c6, a6', i6⟩ := Sched.completeYieldTo_ca hkj hqj e6
      refine ⟨σ6, ⟨V6, Ac6, Lst6, D6, J6⟩, unbindFromSc_some hk4 hsp he4 hk5 ?_, c6.trans hca4.1,
        i6.trans hca4.2.1, by rw [a6']; exact hca4.2.2, f45.trans f6⟩
      rw [hx5.yieldFrom, ← scYieldFromA_eq, Notif.optRef_ne (by rw [← hj]; exact j0)]; exact e6
  refine WP.spec_bind hin ?_
  rintro ⟨s5, a5⟩ ⟨σ5, hJ5, he5, c5, i5, a5', f5⟩
  exact fin6 s5 a5 σ5 hJ5 he5 ⟨c5, i5, a5'⟩ f5

/-- **A dead object joins the dead set** (`JCovD`'s `th`/`h` weakened, `dead`
by `hd`; no other `JAtZ` field reads `D`). Toward `LiveJ.zdead` as
"a TCB zombie's TCB is in `D`": the thread's finalisation adds it. -/
theorem JAtZ.addDead (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64}
    (hd : DeadP (L := L) H s p) : JAtZ (L := L) arI AR Z H Cs Ac Lst (insert p D) s a σ :=
  { J with
    jcov := ⟨fun q k hq => (J.jcov.th q k hq).imp_right (Or.imp_left (Set.mem_insert_of_mem p)),
      fun q k hq => (J.jcov.h q k hq).imp_right (Or.imp_left (Set.mem_insert_of_mem p)),
      fun q hq => by
        rcases hq with rfl | hq
        · exact hd
        · exact J.jcov.dead q hq,
      J.jcov.ks, J.jcov.idleOut⟩
    kern := { J.kern with } }

/-- **`finThreadJU` from `LiveJ` at the start** (`dbgSuccCov_of_live`). -/
theorem JAtZ.finThreadJL (hAT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hL : LiveJ (L := L) Z.th H Z.G s σ)
    {p : U64} (hp : p ∈ Z.T)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) (hna : L.actionW s ≠ p) (hidle : L.idleW s ≠ p) :
    objects.finalise_cap st arI s a (.Thread p) true false ⦃ r => ∃ σ',
      ((Fl4Spec.Cap.zombie p.bv none 6, Fl4Spec.Cap.nullCap), σ') ∈
        (Fl4Spec.finaliseCap (Z := Unit) (.threadCap p.bv) true σ).1 ∧
      JTP (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ :=
  J.finThreadJU hAT hK hticks (fun _ f => J.dbgSuccCov_of_live hL f) hp hv0 hna hidle

end

end

end Fl4Proofs.P3
