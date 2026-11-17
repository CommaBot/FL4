/-
P3 (DESIGN.md §9), TCB invocations: **ReadRegisters from `JAtZ`** (the
fold's re-scoping of `readRegsXHyp_of`): `JAtZ` after the caller's restart
(`jat_restart`), the source's suspend by `suspend_irelY` with its facts,
the kernel-state base and core kept by it (P1's `sched.suspend.kw`), so the
scheduler-action word outside the objects (`JKern.act`).
-/
import Fl4Proofs.P3.IpcReadRegs
import Fl4Proofs.P3.IpcSuspendJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 64000000 in
/-- **`ReadRegsXHyp` from `JAtZ`** (module docstring). Named: the source
among the TCBs, not the caller (the decode's); at every `XTopAt` of the typed
heap, the caller's IPC buffer valid (`IpcBufCapOK`, `BufCover`, `BufPlaced`)
[global, as CSpace's]. -/
theorem readRegsXHypJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit} {ct p : U64}
    {blk call don : Bool} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : σ.curThread ≠ σ.idleThread) (hJS : JStepHyps (L := L) arI AR Z.th)
    (hcur : σ.curThread = ct.bv) (hpne : p ≠ ct) (hpT : p ∈ Z.T)
    (hZ : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' →
      Endp.IpcBufCapOK σ' ∧ Endp.BufCover Z'.T Z'.B σ' ∧ Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ') :
    ReadRegsXHyp (L := L) arI AR s σ ct p blk call don := by
  intro s1 σ1 flags n a hs1 hst ⟨Zx, hXx⟩
  have hAR : AR a σ1.archState.x64CurrentCr3 := hXx.fin.1.1.2.2.2.2.2.2
  obtain ⟨Ac', Lst', D', J'⟩ := jat_restart J hni hJS hcur hs1 hst
  have hP0 := J.ip
  have hX := J'.xtop
  have hI1 := J'.xtop.irelK J'.ks J'.buf
  obtain ⟨x0, hk0, hσ1⟩ := sts_tcb hst
  have hkc1 : σ1.kheap ct.bv = some (.tcb { x0 with tcbState := .restart }) := by
    rw [hσ1, Notif.stsAct_kheap]; simp [Notif.updK]
  have hcur1 : σ1.curThread = ct.bv := by rw [hσ1, Sched.stsAct_cur']; exact hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem hX.fin.1 hcur1.symm
  have hne : p.bv ≠ ct.bv := fun e => hpne (P1.eq_of_bv e)
  unfold tcb.read_registers
  refine WP.spec_bind (cur_thread_bv hI1.2.2.1) ?_
  rintro ct' hct'
  obtain rfl : ct = ct' := (P1.eq_of_bv (hct'.trans hcur1)).symm
  rw [and1_ne0]
  -- the source's suspend
  have hsus : (if Fl4Spec.testBit flags.bv 0 = true then sched.suspend st arI s1 a p else ok (s1, a)) ⦃ r =>
      r.2 = a ∧ ∃ σy, Fl4Spec.NonDet.when (Fl4Spec.testBit flags.bv 0 = true) (Fl4Spec.suspend (Z := Unit) p.bv) σ1 =
        ({((), σy)}, False) ∧ IRel st Z.th σ1.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.1 σy ∧
        StK.OSK p.bv σ1 σy ∧ L.ksb r.1 = L.ksb s1 ∧ L.cpu r.1 = L.cpu s1 ⦄ := by
    cases Fl4Spec.testBit flags.bv 0
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨trivial, σ1, rfl, hI1, StK.OSK.refl _, by trivial, by trivial⟩
    · simp only [↓reduceIte]
      have hB := J'.blk
      rw [← J'.tcbs_eq.1] at hB
      have hB' := hB
      obtain ⟨⟨Q1, R1, h0⟩, hBd, hXI, -, hSg⟩ := hB'
      refine WP.spec_mono (WP.spec_and (suspend_irelY (ar := arI) hP0 (removeTcbHypP_ok hP0) s1 a σ1 hI1 hpT J'.sv
        J'.obj J'.inv (fun x hk => removeTcbOK_fault hP0 hI1 hpT hk J'.removeTcbOK) J'.yld hB)
        (Fl4Proofs.P1.sched.suspend.kw s1 a p h0 hpT hBd hXI hSg.sub)) ?_
      rintro ⟨s2, a2⟩ ⟨⟨h1, σy, h2, h3⟩, hF⟩
      try simp only [WP.uncurry'_pair] at hF
      refine ⟨h1, σy, by simpa [Fl4Spec.NonDet.when] using h2, h3, StK.st_suspend σ1 ((), σy) ?_, hF.1, hF.2.1⟩
      rw [h2]; exact Set.mem_singleton _
  refine WP.spec_bind hsus ?_
  rintro ⟨s2, a2⟩ ⟨ha2, σy, hsy, hXy, hosk, hks2, hcp2⟩
  obtain rfl : a = a2 := ha2.symm
  -- the caller and the source after it
  obtain ⟨xy, hky, -⟩ := hXy.1.tcb ct hctT
  obtain ⟨y0, hy0, hys⟩ := hosk.1 ct.bv xy (Ne.symm hne) hky
  rw [hkc1] at hy0; cases hy0
  have hrs : xy.tcbState = .restart := hys
  have hcury : ct.bv = σy.curThread := (hosk.2.trans hcur1).symm
  obtain ⟨xs, hks, -⟩ := hXy.1.tcb p hpT
  obtain ⟨⟨Z', hth', hN', hT', hC', hE', hR', hB', hc', hXZ⟩, -, hBWy⟩ :=
    IRel.xtop (L := L) (AR := AR) (a := a) hXy hAR
  have hpT' : p ∈ Z'.T := by rw [hT']; exact hpT
  obtain ⟨hOKb, hBC, hBPl⟩ := hZ Z' _ _ _ hth' hXZ
  have hact : OutsideObjects Z'.th (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) := by
    rw [hth', hcp2, nodeAt_ksb hks2]; exact J'.kern.act
  have htcb : Z'.th ct = some .tcb := (hXZ.curTcb hcury.symm).1
  -- the spec's ReadRegisters
  have hmem : ((.ok (rrOf xs n) : Except Unit (List Fl4Spec.Data)), σy) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.readRegisters p.bv
        (Fl4Spec.testBit flags.bv 0) n.bv Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 := by
    show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) _).run σ1).1
    unfold Fl4Spec.invokeTcb
    refine mem_liftE (x := (rrOf xs n, σy)) (mem_bind_nd (x := ((), σy)) (by rw [hsy]; rfl)
      (mem_bind_nd (x := (σy.curThread, σy)) rfl (mem_bind_nd rfl ?_)))
    rw [asUser_mapM_get hks]
    exact Set.mem_singleton _
  cases call
  · -- not called: `Running`
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (nodata_tail_core hXZ hcury hky hrs hact (rrOf xs n)) ?_
    rintro s3 ⟨hne3, z, hz, hRT, hXT⟩
    exact (WP.spec_ok _).2 ⟨hne3, rrOf xs n, σy, hmem, z, hz, hRT, hXT⟩
  -- called: the caller's buffer, the badge, the words, the message info and `Running`
  simp only [↓reduceIte]
  have hctT' : ct ∈ Z'.T := by rw [hT']; exact hctT
  obtain ⟨x', hk', hwx⟩ := hBWy ct hctT
  rw [hky] at hk'; cases hk'
  refine WP.spec_bind (lookup_buf_full s2 σy hXZ.rel.2.1.1 hXZ.rel.2.1.2.1 htcb hky hOKb true) ?_
  rintro bf ⟨hw0, hwp⟩
  have hbm : ∀ q, Endp.ipcBufOf true xy = some q → Endp.BufMap Z'.B bf q := fun q hq =>
    hBC ct hctT' xy true q hky hq bf (hwp hwx q hq)
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s2 ct _ 0#u64) ?_
  rintro s3 rfl
  rw [← Endp.regIdx_badge]
  set xb := Notif.setReg xy Fl4Spec.badge_register 0 with hxb
  set σb := Notif.updK σy ct.bv (.tcb xb) with hσb
  have hkb : σb.kheap ct.bv = some (.tcb xb) := by simp [hσb, Notif.updK]
  have hksb : σb.kheap p.bv = some (.tcb xs) := by simp [hσb, Notif.updK, hne, hks]
  have hcurb : ct.bv = σb.curThread := hcury
  have hIb := regw_inv s2 a σy hXZ.toRInv ct htcb hcury hky Fl4Spec.badge_register 0#u64
  have hI0 : Vs.RInv (L := L) Z'.th Z'.P Z'.L4 Z'.L3 Z'.L2 Z'.L1 Z'.N Z'.T Z'.C Z'.E Z'.R Z'.B Z'.c AR Z'.G
      (L.wr s2 (regA ct (regIdx Fl4Spec.badge_register)) 0#u64) a (MrS σb ct.bv xb (Endp.ipcBufOf true xy) []) := by
    rw [MrS_nil hkb]; exact hIb
  have hks3 : L.ksb (L.wr s2 (regA ct (regIdx Fl4Spec.badge_register)) 0#u64) = L.ksb s2 := L.ksb_wr _ _ _
  have hcp3 : L.cpu (L.wr s2 (regA ct (regIdx Fl4Spec.badge_register)) 0#u64) = L.cpu s2 := L.cpu_wr _ _ _
  have hlenR := rrOf_length xs n
  have hfr : ∀ q, Endp.ipcBufOf true xy = some q → ∀ z ∈ Endp.mrPairs (rrOf xs n),
      (Endp.bufAddr q z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr q z.1) σy :=
    fun q hq z hz => ⟨Endp.bufAddr_aligned hXZ.fin.1.2.ep (hbm q hq) z.1,
      buf_frame_of_ok hOKb hky hq z.1 (mrPairs_lt hz)⟩
  have fin : ∀ (s5 : S) (len : U64), Vs.RInv (L := L) Z'.th Z'.P Z'.L4 Z'.L3 Z'.L2 Z'.L1 Z'.N Z'.T Z'.C Z'.E Z'.R
      Z'.B Z'.c AR Z'.G s5 a (MrS σb ct.bv xb (Endp.ipcBufOf true xy) (rrOf xs n)) →
      L.ksb s5 = L.ksb s2 → L.cpu s5 = L.cpu s2 → len.val = mrLen (Endp.ipcBufOf true xy) (rrOf xs n).length →
      (do
        let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 len
        let s6 ← msg.set_msg_info st s5 ct mi
        let s7 ← sched.set_thread_state st s6 ct sched.TS_RUNNING
        ok (s7, a)) ⦃ r => L.mem r.1 (stA ct) ≠ sched.TS_RESTART ∧ ∃ rr σy',
        (.ok rr, σy') ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk true don (.invokeTCB (.readRegisters p.bv
          (Fl4Spec.testBit flags.bv 0) n.bv Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 ∧
        ∃ z ∈ (specTail true ct.bv rr σy').1, RelTopM (L := L) r.1 z.2 ∧ XTop (L := L) AR r.1 r.2 z.2 ⦄ := by
    intro s5 len hI5 hk5 hc5 hl
    refine WP.spec_mono (rr_tail_xtop hXZ hcury hky hrs hact hI5 hk5 hc5 (by rw [hlenR]; unfold Fl4Spec.msgMaxLength; omega) hfr len hl
      (by rw [hl]; cases Endp.ipcBufOf true xy <;> simp [mrLen, hlenR] <;> omega)) ?_
    rintro r ⟨hne5, z, hz, hRT, hXT⟩
    exact ⟨hne5, rrOf xs n, σy, hmem, z, hz, hRT, hXT⟩
  refine WP.spec_bind (rr_loop0 σb ct htcb hcurb xb _ hne hpT' hksb n _ a hI0) ?_
  rintro ⟨s4, i⟩ ⟨hiv, hI4, hk4, hc4⟩
  simp only at hiv hI4 hk4 hc4
  try simp only [uncurry_apply_pair]
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hg : tcb.N_GP.val = 2 := by unfold tcb.N_GP; rfl
  by_cases hb : bf = 0#u64
  · -- no buffer: the message registers only
    have hbn : Endp.ipcBufOf true xy = none := hw0.1 hb
    have hbb : (bf != 0#u64) = false := by simp [hb]
    simp only [hbb, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (rr_loopGR n s4 _ (fun _ _ => rfl)) ?_
    rintro ⟨s5, k⟩ hk5
    obtain ⟨rfl, rfl⟩ : s4 = s5 ∧ k = 0#u64 := ⟨(Prod.mk.inj hk5).1.symm, (Prod.mk.inj hk5).2⟩
    try simp only [uncurry_apply_pair]
    simp only [lift, bind_ok]
    refine fin s4 _ ?_ (hk4.trans hks3) (hc4.trans hcp3) ?_
    · rw [hbn] at hI4 ⊢
      by_cases hn4 : n.val ≤ 4
      · rw [hiv, show min n.val 4 = (rrOf xs n).length by rw [hlenR]; omega, List.take_length] at hI4; exact hI4
      · rw [hiv, show min n.val 4 = 4 by omega] at hI4
        simp only [MrS] at hI4 ⊢
        rw [← List.take_append_drop 4 (rrOf xs n), Endp.mrStateN_append_ge _ _ _ _ _ (by simp [hlenR]; omega)]
        exact hI4
    · rw [hbn, hlenR]
      simp [mrLen, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  · -- a buffer
    obtain ⟨q, hq⟩ : ∃ q, Endp.ipcBufOf true xy = some q := by
      cases h : Endp.ipcBufOf true xy with
      | none => exact absurd (hw0.2 h) hb
      | some q => exact ⟨q, rfl⟩
    have hbm' := hbm q hq
    have hbb : (bf != 0#u64) = true := by simp [hb]
    simp only [hbb, ↓reduceIte]
    rw [hq] at hI4
    have hBP3 : Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s4 σb :=
      hBPl.mono (hk4.trans hks3) (fun r y n hr => by
        by_cases e : r = ct.bv
        · subst e; rw [hkb] at hr; cases hr
        · simpa [hσb, Notif.updK, e] using hr)
    by_cases hin : i < n
    · -- past `MR3`: the frame registers into the buffer
      rw [if_pos hin]
      have hin' : i.val < n.val := (P1.gt_iff_val).1 hin
      have hi4 : i.val = 4 := by omega
      have hi18 : i < tcb.N_FRAME := (P1.gt_iff_val).2 (by rw [hf]; omega)
      rw [if_pos hi18]
      refine WP.spec_bind (rr_loop1 σb ct hkb q bf hbm' hne hpT' hksb n s4 a i (by omega) (by omega) hBP3 hI4) ?_
      rintro ⟨s5, i1⟩ ⟨hi1, hI5, hk5, hc5⟩
      simp only at hi1 hI5 hk5 hc5
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (rr_loopGR n s5 _ (fun _ _ => rfl)) ?_
      rintro ⟨s6, k⟩ hk6
      obtain ⟨rfl, rfl⟩ : s5 = s6 ∧ k = 0#u64 := ⟨(Prod.mk.inj hk6).1.symm, (Prod.mk.inj hk6).2⟩
      try simp only [uncurry_apply_pair]
      try simp only [hbb, ↓reduceIte]
      have hk0 : (0#u64 : U64) < tcb.N_GP := (P1.gt_iff_val).2 (by rw [hg]; decide)
      rw [if_pos hk0]
      obtain ⟨i2, h2e, h2v⟩ := spec_exists (U64.add_spec (x := 0#u64) (y := tcb.N_FRAME) (by rw [hf]; scalar_tac))
      rw [h2e, bind_ok]
      have hi2 : i2.val = 18 := by rw [← hf]; simpa using h2v
      by_cases h18 : i2 < n
      · rw [if_pos h18]
        have hn18 : 18 < n.val := by have := (P1.gt_iff_val).1 h18; omega
        rw [show i1.val = 18 by omega] at hI5
        have hBP5 : Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s5 σb := hBP3.mono hk5 (fun _ _ _ h => h)
        refine WP.spec_bind (rr_loopGB σb ct hkb q bf hbm' hne hpT' hksb n s5 a hn18 hBP5 hI5 _ (fun _ _ => rfl)) ?_
        rintro ⟨s7, k1⟩ ⟨hk1, hI7, hk7, hc7⟩
        simp only at hk1 hI7 hk7 hc7
        try simp only [uncurry_apply_pair]
        simp only [lift, bind_ok]
        refine fin s7 _ ?_ (hk7.trans (hk5.trans (hk4.trans hks3))) (hc7.trans (hc5.trans (hc4.trans hcp3))) ?_
        · rw [hq]; rw [show 18 + k1.val = (rrOf xs n).length by rw [hlenR]; omega, List.take_length] at hI7
          exact hI7
        · rw [hq, hlenR]
          simp [mrLen, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      · rw [if_neg h18]
        have hn18 : n.val ≤ 18 := by have := (P1.gt_iff_val).not.1 h18; omega
        simp only [lift, bind_ok]
        refine fin s5 _ ?_ (hk5.trans (hk4.trans hks3)) (hc5.trans (hc4.trans hcp3)) ?_
        · rw [hq]; rw [show i1.val = (rrOf xs n).length by rw [hlenR]; omega, List.take_length] at hI5
          exact hI5
        · rw [hq, hlenR]
          simp [mrLen, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · -- up to `MR3`
      rw [if_neg hin]
      have hn4 : n.val ≤ 4 := by have := (P1.gt_iff_val).not.1 hin; omega
      refine WP.spec_bind (rr_loopGR n s4 _ (fun _ _ => rfl)) ?_
      rintro ⟨s5, k⟩ hk5
      obtain ⟨rfl, rfl⟩ : s4 = s5 ∧ k = 0#u64 := ⟨(Prod.mk.inj hk5).1.symm, (Prod.mk.inj hk5).2⟩
      try simp only [uncurry_apply_pair]
      try simp only [hbb, ↓reduceIte]
      have hk0 : (0#u64 : U64) < tcb.N_GP := (P1.gt_iff_val).2 (by rw [hg]; decide)
      rw [if_pos hk0]
      obtain ⟨i2, h2e, h2v⟩ := spec_exists (U64.add_spec (x := 0#u64) (y := tcb.N_FRAME) (by rw [hf]; scalar_tac))
      rw [h2e, bind_ok]
      have hi2 : i2.val = 18 := by rw [← hf]; simpa using h2v
      have h18 : ¬ i2 < n := fun h => by have := (P1.gt_iff_val).1 h; omega
      rw [if_neg h18]
      simp only [lift, bind_ok]
      refine fin s4 _ ?_ (hk4.trans hks3) (hc4.trans hcp3) ?_
      · rw [hq]; rw [show i.val = (rrOf xs n).length by rw [hlenR]; omega, List.take_length] at hI4
        exact hI4
      · rw [hq, hlenR]
        simp [mrLen, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega


end

end

end Fl4Proofs.P3
