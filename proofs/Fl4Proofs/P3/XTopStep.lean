/-
P3 (DESIGN.md §9): **`XTopAt` across the steps the per-cap discharges are
built from** (TopXAll's named `XCap` hypotheses).

* `XTopAt.restart`: `set_thread_state Restart` of the current thread
  (VSpace's `restart_top`; the IPC part from the endpoint, notification and
  scheduler relations after).
* `XTopAt.slotStep`: a CNode-only step (a capability insert, a slot write):
  FL4 writes only slot words, the spec changes only CNodes (`CnK`,
  `KeepC`), the TCBs' VSpace slots keep their caps, the CSpace relation
  after (`TopSR.step0`, the VSpace frames).
* `XTopAt.frameStep`: FL4 writing words of the other objects that neither
  the endpoint nor the notification relation reads, the spec keeping the
  heap; the scheduler, IRQ, IO-port and domain relations after.
* `XTopAt.ksStep`: a kernel-state step (an IRQ state, the IO bitmap, the
  domain schedule): FL4 writes only `KsW` words, the spec only what
  `KsStep` allows; the IRQ, IO-port and domain relations after. Needs the
  IPC objects outside the kernel-global block (`KsApart`).
* `XTopAt.schedStep`: a scheduler step (`SchedStep`) at sets whose TCBs
  include the typed heap's.
-/
import Fl4Proofs.P3.TopXAll
import Fl4Proofs.P3.VsTopInst
import Fl4Proofs.P3.StepSem
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

theorem stsAct_cdt (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) : (Notif.stsAct σ t).cdt = σ.cdt := by
  unfold Notif.stsAct; split_ifs <;> rfl
theorem stsAct_orig (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) :
    (Notif.stsAct σ t).isOriginalCap = σ.isOriginalCap := by
  unfold Notif.stsAct; split_ifs <;> rfl
theorem stsAct_cur (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) : (Notif.stsAct σ t).curThread = σ.curThread := by
  unfold Notif.stsAct; split_ifs <;> rfl
theorem stsAct_dl (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) :
    (Notif.stsAct σ t).domainList = σ.domainList ∧ (Notif.stsAct σ t).domainStartIndex = σ.domainStartIndex := by
  unfold Notif.stsAct; split_ifs <;> exact ⟨rfl, rfl⟩

/-- Writes keeping the `VObj` words keep the slots. -/
theorem slotsSame_of_vobj {th : TypedHeap} (hPl : Placed th) {P L4 L3 L2 L1 : Set U64} {kb : U64} {s s' : S}
    (h : ∀ b, P1.Aligned b → VObj th P L4 L3 L2 L1 kb b → L.mem s' b = L.mem s b) :
    SlotsSame th (L.mem s) (L.mem s') := by
  intro a ha
  have hal := ha.align hPl
  have hfit := ha.fit hPl
  have one : ∀ k : U64, k.val < 32 → k.val % 8 = 0 → L.mem s' (wordOf a k) = L.mem s (wordOf a k) := by
    intro k hk hk8
    have hv : (wordOf a k).val = a.val + k.val := wordOf_val (by omega)
    exact h _ (by unfold P1.Aligned; rw [hv]; omega)
      (vobj_of_slot hPl P L4 L3 L2 L1 kb ha (by rw [hv]; omega) (by rw [hv]; omega))
  have h0 : wordOf a 0#u64 = a := by
    apply UScalar.eq_of_val_eq; rw [wordOf_val (by simp; omega)]; simp
  refine ⟨?_, one 8#u64 (by decide) (by decide), one 16#u64 (by decide) (by decide),
    one 24#u64 (by decide) (by decide)⟩
  have := one 0#u64 (by decide) (by decide)
  rwa [h0] at this

set_option maxHeartbeats 4000000 in
/-- **`XTopAt` across `set_thread_state Restart` of the current thread**
(VSpace's `restart_top` for `FinX`; the IPC part from the endpoint,
notification and scheduler relations after). -/
theorem XTopAt.restart {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) {ct : U64} (hcur : σ.curThread = ct.bv) {x : Fl4Spec.Tcb}
    (hk : σ.kheap ct.bv = some (.tcb x)) (hrun : Fl4Spec.runnable x.tcbState = true) :
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s1 =>
      XTopAt (L := L) AR Z s1 a (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsSame Z.th (L.mem s) (L.mem s1) ∧ L.ksb s1 = L.ksb s ⦄ := by
  obtain ⟨⟨hS, hR, hPt, hPI, hCO⟩, ⟨hPl, ⟨hSt, hV, hM, hC, hI⟩, hFI, hD, hMO, hIA, hSA⟩, -, hE⟩ := hX
  set σ1 := Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv with hσ1
  have hkh : σ1.kheap = Function.update σ.kheap ct.bv (some (.tcb { x with tcbState := .restart })) := by
    rw [hσ1, Notif.stsAct_kheap, Notif.updK_kheap]
  have hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) := by
    rw [hcur, Notif.setThreadState_eq .restart hk]
  have hP := hS.2
  obtain ⟨Q, R0, hc, -⟩ := hS.1.1.lists
  have hT : ct ∈ Z.T := by
    obtain ⟨Q', R', hc', hs'⟩ := hS.1.1.lists
    have : ct = Sched.nodeW st s Z.c layout.node.CUR_THREAD := P1.eq_of_bv (hcur.symm.trans hs'.curThread)
    rw [this]; exact hc'.curT
  have hta := hc.tcbs ct hT
  have hW1v : (stA ct).val = ct.val + 3328 := by rw [stA_eq]; exact Notif.tfield_val hta (by decide)
  have hW1a : P1.Aligned (stA ct) := by unfold P1.Aligned; rw [hW1v]; have := hta.align; omega
  have hcpu0 : L.cpu s = Z.c := hc.cur
  have hoff : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
  have hoff8 : layout.node.SCHED_ACTION.val % 8 = 0 := by simp [layout.node.SCHED_ACTION]
  have hW2v : (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val =
      (L.ksb s).val + 13568 + Z.c.val * 4288 + layout.node.SCHED_ACTION.val := by
    rw [hcpu0]; exact P1.nodeAt_val hc.node hoff
  have hW2a : P1.Aligned (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
    rw [hcpu0]; exact P1.nodeAt_aligned hc.node hoff hoff8
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hko := hc.ksOut ct hT
  have hne1 : ∀ o ∈ domOffs, (ksW (L.ksb s) o).val ≠ (stA ct).val := by
    intro o ho
    have := (domOffs_lt' ho).1
    rw [ksW_val (by omega), hW1v]; omega
  have hne2 : ∀ o ∈ domOffs, (ksW (L.ksb s) o).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val := by
    intro o ho
    have := (domOffs_lt' ho).1
    rw [ksW_val (by omega), hW2v]; omega
  refine WP.spec_mono (WP.spec_and (restart_top s a σ ct x hS hR hcur.symm hk hrun)
    (set_thread_state_cases (L := L) s ct sched.TS_RESTART)) ?_
  rintro s1 ⟨⟨hVs, hPt', hS', hk1, hmV⟩, hcase⟩
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) := slotsSame_of_vobj hPl hmV
  have hcap : ∀ y, IsSlot Z.th y → capAt (L.mem s1) y = capAt (L.mem s) y := fun y hy => hSS.capAt hy
  have hDS : DomSame (L.mem s) (L.mem s1) (L.ksb s) := by
    rcases hcase with rfl | rfl
    · exact DomSame.wr s sched.TS_RESTART hkf hka hW1a hne1
    · exact (DomSame.wr s sched.TS_RESTART hkf hka hW1a hne1).trans
        (DomSame.wr (L.wr s (stA ct) sched.TS_RESTART) _ hkf hka hW2a hne2)
  have hSz : Sched.SzKeep σ σ1 := by
    intro p y n hp
    rw [hkh] at hp
    by_cases e : p = ct.bv
    · subst e; simp at hp
    · rw [Function.update_of_ne e] at hp; exact ⟨y, hp⟩
  have hcdt : σ1.cdt = σ.cdt := by rw [hσ1, stsAct_cdt]; rfl
  have hio : σ1.isOriginalCap = σ.isOriginalCap := by rw [hσ1, stsAct_orig]; rfl
  have hcur1 : σ1.curThread = σ.curThread := by rw [hσ1, stsAct_cur]; rfl
  have hdl := stsAct_dl (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv
  have hPI' : PoolsIn Z.P Z.L4 (L.mem s1) := fun q hq lo hl => by
    have hw : VsWrite Z.P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hmV _ (hw.aligned hP.vs) (vsWrite_vobj hP.vs hw)]
    exact hPI q hq lo hl
  refine ⟨⟨⟨hS', hVs, hPt' hPt, hPI', hCO.of_same hSS hcur1⟩,
    ⟨hPl, ⟨(hSt.tcb_state hk hkh).of_caps hcap, hV.of_caps hcap, hM.of_same hSS, hC.of_same hSS hcdt hio,
      hI.of_same hM hSS⟩, hFI.of_same hM hSS (ksub_of_eq (setThreadState_nks _ _) hst),
      by rw [hk1]; exact hD.of_same hDS hdl.1 hdl.2, by rw [hk1]; exact MdbOKV.of_same hM hSS hMO,
      by rw [hk1]; exact hIA, hSA.mono hSz⟩,
    IpcRel.of hS'.1.2.2.1 hS'.1.2.1 (sched_sc hS'.1.1), hE.mono hk1 hSz⟩, hSS, hk1⟩

/-- A CNode-only spec step (`CnK`, `KeepC`) is an `OStep` keeping the machine
and arch states. -/
theorem ostep_of_cnk {σ σ' : Fl4Spec.State Unit} (hcn : CnK σ σ') (hkc : KeepC σ σ') :
    OStep (fun _ => False) σ σ' ∧ σ'.machineState = σ.machineState ∧ σ'.archState = σ.archState := by
  have h := hcn.1
  refine ⟨⟨(by have e := congrArg Fl4Spec.AbstractState.readyQueues h; exact e), (by have e := congrArg Fl4Spec.AbstractState.releaseQueue h; exact e),
    (by have e := congrArg Fl4Spec.AbstractState.curThread h; exact e), (by have e := congrArg Fl4Spec.AbstractState.schedulerAction h; exact e),
    (by have e := congrArg Fl4Spec.AbstractState.curSc h; exact e), (by have e := congrArg Fl4Spec.AbstractState.curTime h; exact e),
    (by have e := congrArg Fl4Spec.AbstractState.consumedTime h; exact e), (by have e := congrArg Fl4Spec.AbstractState.reprogramTimer h; exact e),
    (by have e := congrArg Fl4Spec.AbstractState.curDomain h; exact e), (by have e := congrArg Fl4Spec.AbstractState.domainTime h; exact e),
    (by have e := congrArg Fl4Spec.AbstractState.idleThread h; exact e), (by have e := congrArg Fl4Spec.AbstractState.interruptStates h; exact e),
    (by have e := congrArg Fl4Spec.AbstractState.interruptIrqNode h; exact e),
    (by exact congrArg (fun a => a.archState.x64AllocatedIoPorts) h), (by exact congrArg (fun a => a.archState.x64GlobalPml4) h),
    fun q hq => ?_⟩, (by have e := congrArg Fl4Spec.AbstractState.machineState h; exact e), (by have e := congrArg Fl4Spec.AbstractState.archState h; exact e)⟩
  rcases hkc q with e | ⟨r, cs, cs', h1, h2⟩
  · exact absurd e hq
  · exact ⟨Or.inr (Or.inr (Or.inl ⟨r, cs, h1⟩)), Or.inr (Or.inl ⟨r, cs', h2⟩)⟩

theorem SzKeep.of_keepC {σ σ' : Fl4Spec.State Unit} (h : KeepC σ σ') : Sched.SzKeep σ σ' := by
  intro p x n hp
  rcases h p with e | ⟨r, cs, cs', h1, h2⟩
  · exact ⟨x, e ▸ hp⟩
  · rw [h2] at hp; cases hp

theorem slotWd_vobj {th : TypedHeap} (hPl : Placed th) {P L4 L3 L2 L1 : Set U64} {kb b : U64}
    (h : Sched.SlotWd th b) : VObj th P L4 L3 L2 L1 kb b := by
  obtain ⟨y, hy, g1, g2⟩ := slotWd_range hPl h
  exact vobj_of_slot hPl P L4 L3 L2 L1 kb hy g1 g2

theorem slotWd_inObj {th : TypedHeap} (hPl : Placed th) {b : U64} (h : Sched.SlotWd th b) :
    ¬ OutsideObjects th b := by
  obtain ⟨y, hy, g1, g2⟩ := slotWd_range hPl h
  obtain ⟨q, k, hq, h3, h4, -⟩ := slot_in_object hPl hy
  rintro ⟨-, ho⟩
  exact ho q k hq ⟨by omega, by omega⟩

set_option maxHeartbeats 4000000 in
/-- **`XTopAt` across a CNode-only step** (a capability insert, a slot
write): FL4 writes only slot words, the spec changes only CNodes (`CnK`,
`KeepC`), the TCBs' VSpace slots keep their caps, and the CSpace relation
holds after. -/
theorem XTopAt.slotStep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a : A} {σ σ' : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (hw : P1.WritesIn st s s' (Sched.SlotWd Z.th)) (hcn : CnK σ σ')
    (hkc : KeepC σ σ') {G' : MdbGhost} (hCR : CRel Z.th (L.mem s') σ' G') (hFI : FinInv Z.th (L.mem s') σ' G')
    (hMO : MdbOKV (L.ksb s) (L.mem s') G')
    (hTS : ∀ t, Z.th t = some .tcb → capAt (L.mem s') (slotOf t 1) = capAt (L.mem s) (slotOf t 1)) :
    XTopAt (L := L) AR { Z with G := G' } s' a σ' := by
  obtain ⟨⟨hS, hR, hPt, hPI, hCO⟩, ⟨hPl, -, -, hD, -, hIA, hSA⟩, -, hE⟩ := hX
  obtain ⟨hO, hms, har⟩ := ostep_of_cnk hcn hkc
  have hP := hS.2
  have hk : L.ksb s' = L.ksb s := hw.1
  have hS' := TopSR.step0 hS (fun b h => slotWd_vobj hPl h) hw hO hms (by rw [har])
  have hSz := SzKeep.of_keepC hkc
  have hvw : ∀ b, VsWrite Z.P (L.ksb s) b → L.mem s' b = L.mem s b := fun b hb =>
    hw.2.2 b (hP.vo b hb).1 fun h => slotWd_inObj hPl h (hP.vo b hb)
  have hcur : σ'.curThread = σ.curThread := hO.ct
  refine ⟨⟨hS', ?_, ?_, fun q hq lo hl => ?_, ?_⟩, ⟨hPl, hCR, hFI, ?_, by rw [hk]; exact hMO,
    by rw [hk]; exact hIA, hSA.mono hSz⟩, IpcRel.of hS'.1.2.2.1 hS'.1.2.1 (sched_sc hS'.1.1), hE.mono hk hSz⟩
  · rw [hk]
    refine hR.frame hvw (by rw [har]) fun p hp => ?_
    obtain ⟨f, hf, -⟩ := hR.pool p hp
    rcases hkc p.bv with e | ⟨r, cs, cs', h1, -⟩
    · exact e
    · rw [hf] at h1; cases h1
  · refine hPt.frame (fun b hb => hw.2.2 b (hP.po b hb).1 fun h => slotWd_inObj hPl h (hP.po b hb)) fun q hq => ?_
    rcases hkc q.bv with e | ⟨r, cs, cs', h1, -⟩
    · exact e
    · rcases hq with hq | hq | hq | hq
      · obtain ⟨g, hg, -⟩ := hPt.l4 q hq; rw [hg] at h1; cases h1
      · obtain ⟨g, hg, -⟩ := hPt.l3 q hq; rw [hg] at h1; cases h1
      · obtain ⟨g, hg, -⟩ := hPt.l2 q hq; rw [hg] at h1; cases h1
      · obtain ⟨g, hg, -⟩ := hPt.l1 q hq; rw [hg] at h1; cases h1
  · have hwv : VsWrite Z.P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hvw _ hwv]; exact hPI q hq lo hl
  · obtain ⟨t, h1, h2, h3⟩ := hCO
    exact ⟨t, h1.trans hcur.symm, h2, fun p asid hc => h3 p asid (by rwa [hTS t h2] at hc)⟩
  · rw [hk]
    refine hD.frame (fun o ho => ?_) (by have e := congrArg Fl4Spec.AbstractState.domainList hcn.1; exact e)
      (by have e := congrArg Fl4Spec.AbstractState.domainStartIndex hcn.1; exact e)
    have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
    have h8 := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    refine hw.2.2 _ (by unfold P1.Aligned; rw [hv]; have := hP.vs.ksb_al; omega) fun h => ?_
    obtain ⟨y, hy, g1, g2⟩ := slotWd_range hPl h
    exact hIA.ks _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) y hy ⟨g1, g2⟩

/-! ## Writes in the kernel-global block -/

/-- The IPC objects lie outside the kernel-global block. -/
structure KsApart (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (kb : U64) : Prop where
  ep : ∀ e ∈ E, e.val + 16 ≤ kb.val ∨ kb.val + 13568 ≤ e.val
  rep : ∀ r ∈ R, r.val + 32 ≤ kb.val ∨ kb.val + 13568 ≤ r.val
  ntfn : ∀ n ∈ N, n.val + 64 ≤ kb.val ∨ kb.val + 13568 ≤ n.val
  buf : ∀ wp ∈ B, wp.1.val + 8 ≤ kb.val ∨ kb.val + 13568 ≤ wp.1.val

/-- The scheduler relation across a kernel-state spec step. -/
theorem Sched.SchedRel.ksStep {N T C : Set U64} {c : U64} {s : S} {σ σ' : Fl4Spec.State Unit}
    (hS : Sched.SchedRel st N T C c s σ) (hO : KsStep σ σ') : Sched.SchedRel st N T C c s σ' := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hz : Sched.SzKeep σ σ' := Sched.SzKeep.of_kheap hO.kh
  refine ⟨hS.placed, hS.nodeNW, hS.domNW, hS.dtNW, Sched.scOut_transfer rfl hz hS.scOut,
    Sched.scDisj_transfer hz hS.scDisj, hS.actW, by rw [hO.act]; exact hS.act,
    by rw [hO.repr]; exact hS.repr, hS.core, Q, R0, hc, ?_⟩
  refine ⟨fun p hp => by rw [hO.rq]; exact hs.rq p hp, fun d p hd => by rw [hO.rq]; exact hs.rqDom d p hd,
    by rw [hO.rel]; exact hs.rel, by rw [hO.ct]; exact hs.curThread, by rw [hO.csc]; exact hs.curSc,
    by rw [hO.ctime]; exact hs.curTime, by rw [hO.cons]; exact hs.consumed, by rw [hO.cdom]; exact hs.curDom,
    fun t ht => by rw [hO.kh]; exact hs.tcb t ht, hs.scMem, fun sc hsc => by rw [hO.kh]; exact hs.scs sc hsc,
    hs.idleSc, by rw [hO.dtime]; exact hs.domTime, by rw [hO.idle]; exact hs.idleTh⟩

/-- The scheduler relation across writes in `KsW`. -/
theorem Sched.SchedRel.ksW {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : Sched.SchedRel st N T C c s σ) (hw : P1.WritesIn st s s' (KsW (L.ksb s))) :
    Sched.SchedRel st N T C c s' σ := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hN := hc.node
  have hnot : ∀ b : U64, b.val < (L.ksb s).val + 24 ∨ (L.ksb s).val + 13568 ≤ b.val ∨ b.val < (L.ksb s).val →
      ¬ KsW (L.ksb s) b := by
    rintro b hb ⟨K, h1, h2, -, e⟩; omega
  have hnode : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) :=
    fun o ho h8 => hw.mem_eq (P1.nodeAt_aligned hN ho h8) (hnot _ (Or.inr (Or.inl (by
      rw [P1.nodeAt_val hN ho]; simp only [P1.LawfulStore.nodeBase]; omega))))
  have hf := hN.fits; have hal := hN.align
  simp only [P1.LawfulStore.nodeBase] at hf hal
  have hksb : ∀ K : U64, 0 < K.val → K.val < 24 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add (L.ksb s) K) = L.mem s (core.num.U64.wrapping_add (L.ksb s) K) := by
    intro K h1 h2 h3
    have hv : (core.num.U64.wrapping_add (L.ksb s) K).val = (L.ksb s).val + K.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    exact hw.mem_eq (by unfold P1.Aligned; rw [hv]; omega) (hnot _ (Or.inl (by rw [hv]; omega)))
  have ha' : Sched.SAgree st T C c s s' := by
    refine ⟨hw.1, hw.2.1, fun o ho h8 _ _ _ _ _ => hnode o ho h8, fun y hy K hK => ?_,
      by unfold Sched.curDomA; exact hksb 8#u64 (by simp) (by simp) (by simp),
      by unfold Sched.dtA; exact hksb 16#u64 (by simp) (by simp) (by simp), fun sc' hsc' b hb hin => ?_⟩
    · obtain ⟨h1, h2, -⟩ := Sched.schedField_ok hK
      have hya := hc.tcbs y hy
      refine hw.mem_eq (P1.field_aligned hya h1 h2) (hnot _ ?_)
      rw [Notif.tfield_val hya h1]; rcases hc.ksOut y hy with h | h <;> omega
    · exact hw.mem_eq hb (hnot _ (by rcases (hS.scOutIn hsc' hin).2.2.2 with h | h <;> omega))
  refine hS.of_sagree ha' ?_ ?_ ⟨rfl, rfl, fun _ => Or.inl rfl⟩
  · unfold Sched.nodeW; rw [Sched.nodeAt_ksb hw.1]
    exact hnode _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  · unfold Sched.nodeW; rw [Sched.nodeAt_ksb hw.1]
    exact hnode _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])

theorem not_ksW {kb b : U64} (h : b.val < kb.val + 24 ∨ kb.val + 13568 ≤ b.val ∨ b.val + 8 ≤ kb.val ∨
    b.val = kb.val + 48) : ¬ KsW kb b := by
  rintro ⟨K, h1, h2, h3, e⟩; omega

theorem OObj.of_same {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {s s' : S}
    {σ σ' : Fl4Spec.State Unit} (hk : L.ksb s' = L.ksb s) (hkh : σ'.kheap = σ.kheap) {a : U64}
    (h : OObj st N T C E R B c s' σ' a) : OObj st N T C E R B c s σ a := by
  have hnb : L.nodeBase s' c = L.nodeBase s c := by simp [P1.LawfulStore.nodeBase, hk]
  unfold OObj at h ⊢
  rw [hnb, hk, hkh] at h
  exact h

set_option maxHeartbeats 8000000 in
/-- **`XTopAt` across a step writing words of the other objects**: FL4
writes only `W` words, in the other objects (`OObj`), none read by the
endpoint or notification relations and not the kernel root; the spec keeps
the heap, the CDT, the current thread, the memory and the ASID table and
global PML4; the scheduler, IRQ, IO-port and domain relations hold after,
and the arch relation. -/
theorem XTopAt.frameStep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hWO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b)
    (hWE : ∀ b, W b → ¬ Endp.EFoot Z.T Z.E Z.R Z.B b) (hWN : ∀ b, W b → ¬ Notif.NFoot Z.N Z.T b)
    (hWK : ¬ W (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT))
    (hkh : σ'.kheap = σ.kheap) (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hct : σ'.curThread = σ.curThread)
    (hum : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory)
    (hasid : σ'.archState.x64AsidTable = σ.archState.x64AsidTable)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hSch' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ')
    (hIrq' : IrqRel (L.mem s') (L.ksb s) σ') (hIo' : IoRel (L.mem s') (L.ksb s) σ')
    (hD' : DomRel (L.mem s') (L.ksb s) σ') (hAR' : AR a' σ'.archState.x64CurrentCr3) :
    XTopAt (L := L) AR Z s' a' σ' := by
  obtain ⟨⟨⟨⟨hSch, hEp, hNt, -, -, hKr, -⟩, hP⟩, hR, hPt, hPI, hCO⟩, ⟨hPl, hCR, hFI, -, hMO, hIA, hSA⟩, -, hE⟩ := hX
  have hk : L.ksb s' = L.ksb s := hw.1
  have hvobj : ∀ b, VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b → ¬ W b :=
    fun b hv hb => hP.disj b (hWO b hb) hv
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    slotsSame_of_vobj hPl fun b hb hv => hw.mem_eq hb (hvobj b hv)
  have hEp' : Endp.EpStateRel Z.T Z.E Z.R Z.B (L.mem s') σ' :=
    Endp.EpStateRel.frame hEp hP.ep (fun b hb hf => hw.mem_eq hb fun h => hWE b h hf)
      ⟨fun p x h => by rw [hkh]; exact h, fun p x h => ⟨x, by rw [hkh]; exact h, rfl⟩,
        fun p x h => ⟨x, by rw [hkh]; exact h, rfl, rfl, rfl, rfl, rfl⟩, hum⟩
  have hNt' : Notif.NtfnStateRel Z.N Z.T (L.mem s') σ' :=
    Notif.NtfnStateRel.frame hNt hSch.placed (fun b hb hf => hw.mem_eq hb fun h => hWN b h hf)
      ⟨fun p x h => by rw [hkh]; exact h, fun p x h => ⟨x, by rw [hkh]; exact h, rfl, rfl, rfl⟩⟩
  have hKr' : KRootRel (L.mem s') (L.ksb s') σ' := by
    unfold KRootRel globCr3 at hKr ⊢
    have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
    have hka := hP.vs.ksb_al
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [hk, hw.mem_eq (by unfold P1.Aligned; rw [hkv]; omega) hWK, hgp]
    exact hKr
  have hvw : ∀ b, VsWrite Z.P (L.ksb s) b → L.mem s' b = L.mem s b := fun b hb =>
    hw.mem_eq (VsWrite.aligned hP.vs hb) (hvobj b (vsWrite_vobj hP.vs hb))
  have hSz : Sched.SzKeep σ σ' := Sched.SzKeep.of_kheap hkh
  refine ⟨⟨⟨⟨hSch', hEp', hNt', by rw [hk]; exact hIrq', by rw [hk]; exact hIo', hKr', hAR'⟩, ?_⟩, ?_, ?_,
    fun q hq lo hl => ?_, hCO.of_same hSS hct⟩,
    ⟨hPl, crel_same hCR hSS hkh hcdt horig, hFI.of_same hCR.2.2.1 hSS (KSub.of_kheap hkh),
      by rw [hk]; exact hD', by rw [hk]; exact MdbOKV.of_same hCR.2.2.1 hSS hMO, by rw [hk]; exact hIA,
      hSA.mono hSz⟩, IpcRel.of hNt' hEp' (sched_sc hSch'), hE.mono hk hSz⟩
  · refine ⟨hP.ep, by rw [hk]; exact hP.vs, hP.pt, hP.pl, fun x hx => by
      rw [hk]; exact hP.disj x (OObj.of_same hk hkh hx), fun x h1 h2 => ?_,
      hP.po, hP.ps, by rw [hk]; exact hP.pv, by rw [hk]; exact hP.vo, by rw [hk]; exact hP.sd, by rw [hk]; exact hP.tko⟩
    have hnb : L.nodeBase s' Z.c = L.nodeBase s Z.c := by simp [P1.LawfulStore.nodeBase, hk]
    rw [hnb] at h1 h2; exact hP.nodeE x h1 h2
  · rw [hk]
    refine hR.frame hvw hasid fun p hp => ?_
    rw [hkh]
  · refine hPt.frame (fun b ⟨q, hq, i, hi, e⟩ => ?_) fun q hq => by rw [hkh]
    subst e
    have hv := table_vobj (th := Z.th) (P := Z.P) hP.pt hq hi (L.ksb s)
    exact hw.mem_eq (hP.po _ ⟨q, hq, i, hi, rfl⟩).1 (hvobj _ hv)
  · have hwv : VsWrite Z.P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hvw _ hwv]; exact hPI q hq lo hl

set_option maxHeartbeats 8000000 in
/-- **`XTopAt` across a kernel-state step** (an IRQ state, the IO bitmap,
the domain schedule): FL4 writes only `KsW` words, the spec only the
interrupt states, IRQ masks, IO ports and domain schedule (`KsStep`); the
IRQ, IO-port and domain relations hold after, and the arch relation. -/
theorem XTopAt.ksStep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hw : P1.WritesIn st s s' (KsW (L.ksb s))) (hO : KsStep σ σ')
    (hIrq' : IrqRel (L.mem s') (L.ksb s) σ') (hIo' : IoRel (L.mem s') (L.ksb s) σ')
    (hD' : DomRel (L.mem s') (L.ksb s) σ') (hAR' : AR a' σ'.archState.x64CurrentCr3) :
    XTopAt (L := L) AR Z s' a' σ' := by
  have hSch := hX.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hSch.lists
  have hko : ∀ t ∈ Z.T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := fun t ht => by
    rcases hc.ksOut t ht with h | h <;> omega
  refine hX.frameStep hw (fun b hb => by obtain ⟨K, h1, h2, -, e⟩ := hb; exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    (fun b hb hf => not_ksW ?_ hb) (fun b hb hf => not_ksW ?_ hb) (not_ksW (Or.inr (Or.inr (Or.inr ?_))))
    hO.kh hO.cdt hO.orig hO.ct hO.um hO.asidT hO.gpml4 ((hSch.ksW hw).ksStep hO) hIrq' hIo' hD' hAR'
  · rcases hf with ⟨e, he, h | h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, ⟨h1, h2⟩ | h⟩ | ⟨wp, hwp, rfl⟩
    · rcases hKA.ep e he with h' | h' <;> omega
    · rcases hKA.ep e he with h' | h' <;> omega
    · rcases hKA.rep r hr with h' | h' <;> omega
    · unfold Endp.TOffN at h2; rcases hko t ht with h' | h' <;> omega
    · unfold Endp.TL at h; rcases hko t ht with h' | h' <;> omega
    · rcases hKA.buf wp hwp with h' | h' <;> omega
  · rcases hf with ⟨n, hn, h1, h2⟩ | ⟨t, ht, h | h | h | h | h | h⟩
    · rcases hKA.ntfn n hn with h' | h' <;> omega
    all_goals
      subst h
      have hta := hSch.placed.tcb t ht
      have hkt := hko t ht
      first
        | (rw [Notif.tStA_eq, Notif.tfield_val hta (by simp)]; simp; omega)
        | (rw [Notif.tBlockA_eq, Notif.tfield_val hta (by simp)]; simp; omega)
        | (rw [Notif.badgeRegA_eq, Notif.tfield_val hta (by simp)]; simp; omega)
        | (rw [Notif.prioA_eq', Notif.tfield_val hta (by simp)]; simp; omega)
        | (rw [Notif.nextEp_eq, Notif.tfield_val hta (by simp)]; simp; omega)
        | (rw [Notif.prevEp_eq, Notif.tfield_val hta (by simp)]; simp; omega)
  · have hP := hX.fin.1.2
    have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
    unfold layout.ks.KERNEL_ROOT
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-! ## Scheduler steps -/

/-- The value of a scheduler step's word. -/
theorem schW_val {T : Set U64} {c : U64} {s : S} (hT : P1.TcbPlaced T) (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64)
    {b : U64} (h : SchW (L := L) T c s b) :
    (∃ y ∈ T, b.val = y.val + 3480 ∨ b.val = y.val + 3488 ∨ b.val = y.val + 3592) ∨
    (L.nodeBase s c ≤ b.val ∧ b.val < L.nodeBase s c + 4288) ∨
    ((L.ksb s).val + 16 ≤ b.val ∧ b.val ≤ (L.ksb s).val + 216 ∧ b.val ≠ (L.ksb s).val + 48) := by
  rcases h with ⟨y, hy, rfl | rfl | rfl⟩ | h | h
  · exact Or.inl ⟨y, hy, Or.inl (by rw [Notif.tfield_val (hT y hy) (by decide)]; rfl)⟩
  · exact Or.inl ⟨y, hy, Or.inr (Or.inl (by rw [Notif.tfield_val (hT y hy) (by decide)]; rfl))⟩
  · exact Or.inl ⟨y, hy, Or.inr (Or.inr (by rw [Notif.tfield_val (hT y hy) (by decide)]; rfl))⟩
  · exact Or.inr (Or.inl ⟨h.1, h.2.1⟩)
  · have := domKW_val h
    exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)

/-- A word of core `c`'s node is a `nodeAt` word. -/
theorem node_word' {T : Set U64} {c : U64} {s : S} (hN : P1.NodePlaced st T s c) {b : U64}
    (h1 : L.nodeBase s c ≤ b.val) (h2 : b.val < L.nodeBase s c + 4288) :
    ∃ o : U64, o.val < 4288 ∧ L.nodeAt s c o = b := by
  have hb := b.hBounds
  have hv : (⟨BitVec.ofNat 64 (b.val - L.nodeBase s c)⟩ : U64).val = b.val - L.nodeBase s c := by
    show (BitVec.ofNat 64 (b.val - L.nodeBase s c)).toNat = _
    simp only [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  refine ⟨⟨BitVec.ofNat 64 (b.val - L.nodeBase s c)⟩, by rw [hv]; omega, ?_⟩
  apply UScalar.eq_of_val_eq
  rw [P1.nodeAt_val hN (by rw [hv]; omega), hv]; omega

/-- The value of a word the notification relation reads in a TCB. -/
theorem nfootT_val {t b : U64} (hta : P1.TcbAddr t)
    (h : b = Notif.tStA t ∨ b = Notif.tBlockA t ∨ b = Notif.badgeRegA t ∨ b = P1.prioA t ∨
      b = P1.nextA .Ep t ∨ b = P1.prevA .Ep t) :
    b.val = t.val + 3328 ∨ b.val = t.val + 3336 ∨ b.val = t.val + 256 ∨ b.val = t.val + 3448 ∨
      b.val = t.val + 3496 ∨ b.val = t.val + 3504 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Notif.tStA_eq, Notif.tfield_val hta (by decide)]; simp
  · rw [Notif.tBlockA_eq, Notif.tfield_val hta (by decide)]; simp
  · rw [Notif.badgeRegA_eq, Notif.tfield_val hta (by decide)]; simp
  · rw [Notif.prioA_eq', Notif.tfield_val hta (by decide)]; simp
  · rw [Notif.nextEp_eq, Notif.tfield_val hta (by decide)]; simp
  · rw [Notif.prevEp_eq, Notif.tfield_val hta (by decide)]; simp

set_option maxHeartbeats 8000000 in
/-- **`XTopAt` across a scheduler step** (`SchedStep`), at sets whose TCBs
include the typed heap's: the words written are the scheduler's (`SchW`),
apart from the endpoint and notification relations and the kernel root. -/
theorem XTopAt.schedStep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a : A}
    {σ σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hS : SchedStep (L := L) Z.th s σ s' σ') :
    XTopAt (L := L) AR Z s' a σ' := by
  obtain ⟨hK, hS, -, -⟩ := hS
  have hSch := hX.fin.1.1.1
  have hNt := hX.fin.1.1.2.2.1
  have hP := hX.fin.1.2
  have hE := hX.esa
  obtain ⟨hSch', hw, hdsi⟩ := hS Z.N Z.T Z.C Z.c hTh hSch hNt
  obtain ⟨Q, R0, hc, -⟩ := hSch.lists
  have hT := hc.tcbs
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hko : ∀ t ∈ Z.T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := fun t ht => by
    rcases hc.ksOut t ht with h | h <;> omega
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  have hnd := hc.node.disj
  have hk : L.ksb s' = L.ksb s := hw.1
  refine hX.frameStep hw (fun b hb => ?_) (fun b hb hf => ?_) (fun b hb hf => ?_) (fun hb => ?_)
    hK.kh hK.cdt hK.orig hK.ct (by rw [hK.ms]) (by rw [hK.arch]) (by rw [hK.arch]) hSch' ?_ ?_ ?_
    (by rw [hK.arch]; exact hX.fin.1.1.2.2.2.2.2.2)
  · -- the words written are the other objects'
    rcases hb with ⟨y, hy, rfl | rfl | rfl⟩ | h | h
    all_goals first
      | exact tcb_oobj hy (hT y hy) (by decide) (by decide)
      | exact Or.inl ⟨h.1, h.2.1⟩
      | (have := domKW_val h
         exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
  · -- not read by the endpoint relation
    have hPe := hP.ep
    rcases schW_val hT hkf hb with ⟨y, hy, hyv⟩ | ⟨g1, g2⟩ | hv
    · rcases hf with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hwp, h⟩
      · have := hPe.et e he y hy; omega
      · have := hPe.rt r hr y hy; omega
      · by_cases e : t = y
        · subst e; obtain ⟨-, h2⟩ := h; unfold Endp.TOffN at h2; omega
        · have := tcb_disj hPe ht hy (Ne.symm e); have := h.range; omega
      · by_cases e : t = y
        · subst e; unfold Endp.TL at h; omega
        · have := tcb_disj hPe ht hy (Ne.symm e); unfold Endp.TL at h; omega
      · have := hPe.bt wp hwp y hy; rw [← h] at this; omega
    · exact hE.node b g1 g2 hf
    · rcases hf with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, ⟨h1, h2⟩ | h⟩ | ⟨wp, hwp, rfl⟩
      · rcases hKA.ep e he with h' | h' <;> omega
      · rcases hKA.rep r hr with h' | h' <;> omega
      · unfold Endp.TOffN at h2; rcases hko t ht with h' | h' <;> omega
      · unfold Endp.TL at h; rcases hko t ht with h' | h' <;> omega
      · rcases hKA.buf wp hwp with h' | h' <;> omega
  · -- not read by the notification relation
    have hPn := hSch.placed
    rcases schW_val hT hkf hb with ⟨y, hy, hyv⟩ | ⟨g1, g2⟩ | hv
    · rcases hf with ⟨n, hn, h1, h2⟩ | ⟨t, ht, h⟩
      · have := hPn.disj n hn y hy; omega
      · have hv := nfootT_val (hT t ht) h
        by_cases e : t = y
        · subst e; omega
        · have := tcb_disj hP.ep ht hy (Ne.symm e); omega
    · obtain ⟨o, ho, rfl⟩ := node_word' hc.node g1 g2
      rcases hf with ⟨n, hn, n1, n2⟩ | ⟨t, ht, h⟩
      · exact hSch.nodeNW o ho (Or.inl ⟨n, hn, n1, n2⟩)
      · have hv := nfootT_val (hT t ht) h
        have := hnd t ht; omega
    · rcases hf with ⟨n, hn, h1, h2⟩ | ⟨t, ht, h⟩
      · rcases hKA.ntfn n hn with h' | h' <;> omega
      · have hv := nfootT_val (hT t ht) h
        rcases hko t ht with h' | h' <;> omega
  · -- not the kernel root
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rcases schW_val hT hkf hb with ⟨y, hy, hyv⟩ | ⟨g1, g2⟩ | hv
    · rcases hko y hy with h' | h' <;> omega
    · omega
    · omega
  · -- the IRQ relation
    have hI := hX.fin.1.1.2.2.2.1
    refine ⟨fun i hi => ?_, fun i hi => by rw [hK.inode]; exact hI.node i hi⟩
    have hv := irqStA_val hkf hi
    rw [hK.ist, hw.mem_eq (by unfold P1.Aligned; rw [hv]; omega) fun hb => ?_]
    · exact hI.st i hi
    rcases schW_val hT hkf hb with ⟨y, hy, hyv⟩ | ⟨g1, g2⟩ | hv'
    · rcases hko y hy with h' | h' <;> omega
    · omega
    · omega
  · -- the IO-port relation
    have hI := hX.fin.1.1.2.2.2.2.1
    intro p hp
    have hwi : (wI p).val < 1024 := by rw [wI_val hp]; omega
    have hv := ioA_val hkf hwi
    unfold bitOf
    rw [hK.arch, hw.mem_eq (by unfold P1.Aligned; rw [hv]; omega) fun hb => ?_]
    · exact hI p hp
    rcases schW_val hT hkf hb with ⟨y, hy, hyv⟩ | ⟨g1, g2⟩ | hv'
    · rcases hko y hy with h' | h' <;> omega
    · omega
    · omega
  · -- the domain schedule
    exact domRel_iff.2 (hdsi (domRel_iff.1 hX.rel.2.2.2.1))

end

end

end Fl4Proofs.P3
