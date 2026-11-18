/-
P3 (DESIGN.md §9), VSpace: **`DeriveSubframe`'s hypotheses for the
composite relation** (`VsSubHyps` with `SR := TopSR`).

* `insStable_top`: an alias insert (slot words, a spec `cap_insert`) keeps
  `TopSR` (`TopSR.step0`).
* `restart_top`: `set_thread_state Restart` of the current, runnable thread
  keeps the ASID and page-table relations and `TopSR`: the scheduler and
  notification relations by `Sched.set_thread_state_refines`, the endpoint
  relation by `Endp.write_state_rel` and the node's action word outside the
  endpoint footprint (`TopPlaced.nodeE`), the others by frames (the state
  word and the action word lie in the other objects, outside the VSpace ones
  and the kernel-state block).
* `vsSubHyps_top`.
-/
import Fl4Proofs.P3.VsSubRel
import Fl4Proofs.P3.SchedNtfn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`VsSubHyps.insStable` for the composite relation.** -/
theorem insStable_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s s' : S) (a : A)
    (σ σ' : Fl4Spec.State Unit) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hw : WritesIn st s s' (SlotWord th)) (hI : InsStep σ σ') :
    TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a σ' := by
  obtain ⟨p, r, cs, idx, a', cdt, io, hk, rfl⟩ := hI
  have hO := OStep.cnode hk idx a'
  refine TopSR.step0 hS (fun b h => ?_) hw
    ⟨hO.rq, hO.rel, hO.ct, hO.act, hO.csc, hO.ctime, hO.cons, hO.repr, hO.cdom, hO.dtime, hO.idle, hO.isc, hO.ist,
      hO.inode, hO.io, hO.gpml4, hO.kh⟩ rfl rfl
  obtain ⟨x, k, hx, hk', rfl⟩ := h
  have hf := hx.fit hS.2.pl
  have := hk'.lt
  have hv := wordOf_val (a := x) (k := k) (by omega)
  exact slot_vobj hS.2.pl hx (by rw [hv]; omega) (by rw [hv]; omega) _

/-- A runnable thread is in no notification's queue. -/
theorem runnable_not_ntfnQ {m : U64 → U64} {σ : Fl4Spec.State Unit} (hR : Notif.NtfnStateRel N T m σ)
    {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hrun : Fl4Spec.runnable x.tcbState = true) :
    ∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue := by
  intro n hn z hz hm
  obtain ⟨z', hz', hr⟩ := hR.ntfn n hn
  rw [hz] at hz'; cases hz'
  have hst := (hR.at_tcb ht hk).st
  have obj := hr.obj
  revert hm obj
  cases z.ntfnObj with
  | idleNtfn => intro hm; simp [Fl4Spec.Ntfn.ntfnQueue] at hm
  | activeNtfn b => intro hm; simp [Fl4Spec.Ntfn.ntfnQueue] at hm
  | waitingNtfn q =>
    intro hm obj
    obtain ⟨-, xs, -, rfl, -, hb⟩ := obj
    have h6 := (hb t (Sched.mem_map_bv.1 hm)).1
    rw [hst] at h6
    cases e : x.tcbState <;> simp_all [Notif.tsCode, Fl4Spec.runnable]

theorem stsAct_updK_fields (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) (o : Fl4Spec.KernelObject) :
    (Notif.stsAct (Notif.updK σ t o) t).interruptStates = σ.interruptStates ∧
    (Notif.stsAct (Notif.updK σ t o) t).interruptIrqNode = σ.interruptIrqNode ∧
    (Notif.stsAct (Notif.updK σ t o) t).archState = σ.archState ∧
    (Notif.stsAct (Notif.updK σ t o) t).machineState = σ.machineState := by
  unfold Notif.stsAct Notif.updK; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem IrqRel.ksFrame {m m' : U64 → U64} {kb : U64} {σ σ' : Fl4Spec.State Unit} (hR : IrqRel m kb σ)
    (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0)
    (hm : ∀ b : U64, Aligned b → kb.val ≤ b.val → b.val < kb.val + 13568 →
      (b.val < kb.val + 1248 ∨ kb.val + 5344 ≤ b.val) → m' b = m b)
    (h1 : σ'.interruptStates = σ.interruptStates) (h2 : σ'.interruptIrqNode = σ.interruptIrqNode) :
    IrqRel m' kb σ' := by
  refine ⟨fun i hi => ?_, fun i hi => by rw [h2]; exact hR.node i hi⟩
  have hv := irqStA_val hkf hi
  rw [h1, hm _ (by unfold Aligned; rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)]
  exact hR.st i hi

theorem IoRel.ksFrame {m m' : U64 → U64} {kb : U64} {σ σ' : Fl4Spec.State Unit} (hR : IoRel m kb σ)
    (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0)
    (hm : ∀ b : U64, Aligned b → kb.val ≤ b.val → b.val < kb.val + 13568 →
      (b.val < kb.val + 1248 ∨ kb.val + 5344 ≤ b.val) → m' b = m b)
    (h1 : σ'.archState.x64AllocatedIoPorts = σ.archState.x64AllocatedIoPorts) : IoRel m' kb σ' := by
  intro p hp
  have hw : (wI p).val < 1024 := by rw [wI_val hp]; omega
  have hv := ioA_val hkf hw
  unfold bitOf
  rw [h1, hm _ (by unfold Aligned; rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)]
  exact hR p hp

set_option maxHeartbeats 4000000 in
/-- **`set_thread_state Restart` of the current thread** for the composite
relation (see the module docstring). -/
theorem restart_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (ct : U64) (x : Fl4Spec.Tcb) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hcur : ct.bv = σ.curThread) (hk : σ.kheap ct.bv = some (.tcb x))
    (hrun : Fl4Spec.runnable x.tcbState = true) :
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      VsRel P (L.mem s') (L.ksb s') (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      (PtRel L4 L3 L2 L1 (L.mem s) σ →
        PtRel L4 L3 L2 L1 (L.mem s') (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv)) ∧
      TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a
        (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      L.ksb s' = L.ksb s ∧
      ∀ b, Aligned b → VObj th P L4 L3 L2 L1 (L.ksb s) b → L.mem s' b = L.mem s b ⦄ := by
  obtain ⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hP⟩ := hS
  obtain ⟨Q, R0, hc, hs⟩ := hSch.lists
  have hT : ct ∈ T := by
    have : ct = Sched.nodeW st s c layout.node.CUR_THREAD := eq_of_bv (hcur.trans hs.curThread)
    rw [this]; exact hc.curT
  have hta := hc.tcbs ct hT
  have hN := hc.node
  have hcpu0 : L.cpu s = c := hc.cur
  have hqN := runnable_not_ntfnQ hNt hT hk hrun
  have hqE := Endp.not_queued hEp hT hk (by
    cases e : x.tcbState <;> simp_all [Notif.tsCode, Fl4Spec.runnable])
  have hv : sched.TS_RESTART.val = Notif.tsCode .restart := by unfold sched.TS_RESTART; rfl
  set σ1 := Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv with hσ1
  obtain ⟨hist, hinode, harch, hms⟩ := stsAct_updK_fields σ ct.bv (.tcb { x with tcbState := .restart })
  rw [← hσ1] at hist hinode harch hms
  -- the two words
  have hW1v : (stA ct).val = ct.val + 3328 := by rw [stA_eq]; exact Notif.tfield_val hta (by decide)
  have hW1a : Aligned (stA ct) := by
    unfold Aligned; rw [hW1v]; have := hta.align; omega
  set W2 := L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION with hW2
  have hoff : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
  have hoff8 : layout.node.SCHED_ACTION.val % 8 = 0 := by simp [layout.node.SCHED_ACTION]
  have hW2v : W2.val = L.nodeBase s c + layout.node.SCHED_ACTION.val := by
    rw [hW2, hcpu0]; exact nodeAt_val hN hoff
  have hW2a : Aligned W2 := by rw [hW2, hcpu0]; exact nodeAt_aligned hN hoff hoff8
  have hO1 : OObj st N T C E R B c s σ (stA ct) := by
    rw [stA_eq]; exact tcb_oobj hT hta (by decide) (by decide)
  have hO2 : OObj st N T C E R B c s σ W2 := Or.inl (by rw [hW2v]; omega)
  have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hko := hc.ksOut ct hT
  refine WP.spec_mono (WP.spec_and (Sched.set_thread_state_refines s σ hNt hSch hT hk hqN _ .restart hv
    (fun n h => by cases h)) (set_thread_state_cases s ct sched.TS_RESTART)) ?_
  rintro s' ⟨⟨σ', hst, hN', hS'⟩, hcase⟩
  have e1 : σ' = σ1 := by
    rw [Notif.setThreadState_eq .restart hk] at hst
    have := congrArg Prod.fst hst
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    exact this.symm
  subst e1
  have hksb : L.ksb s' = L.ksb s := by rcases hcase with rfl | rfl <;> simp
  have hmem : ∀ b, Aligned b → b ≠ stA ct → b ≠ W2 → L.mem s' b = L.mem s b := by
    intro b hb h1 h2
    rcases hcase with rfl | rfl
    · rw [L.mem_wr _ _ _ _ hW1a hb, if_neg (Ne.symm h1)]
    · rw [L.mem_wr _ _ _ _ (by rw [← hW2]; exact hW2a) hb, if_neg (by rw [← hW2]; exact Ne.symm h2),
        L.mem_wr _ _ _ _ hW1a hb, if_neg (Ne.symm h1)]
  have hmV : ∀ b, Aligned b → VObj th P L4 L3 L2 L1 (L.ksb s) b → L.mem s' b = L.mem s b :=
    fun b hb hv => hmem b hb (fun e => hP.disj _ hO1 (e ▸ hv)) (fun e => hP.disj _ hO2 (e ▸ hv))
  have hmK : ∀ b : U64, Aligned b → (L.ksb s).val ≤ b.val → b.val < (L.ksb s).val + 13568 →
      L.mem s' b = L.mem s b :=
    fun b hb h1 h2 => hmem b hb (fun e => by rw [e, hW1v] at h1 h2; omega)
      (fun e => by rw [e, hW2v, hnb] at h1 h2; omega)
  have hkp : ∀ q : Fl4Spec.ObjRef, (∀ y, σ.kheap q ≠ some (.tcb y)) → σ1.kheap q = σ.kheap q := by
    intro q hq
    rw [hσ1, Notif.stsAct_kheap, Notif.updK_kheap, Function.update_of_ne]
    intro e; subst e; exact hq x hk
  -- the ASID and page-table relations
  have hVs : VsRel P (L.mem s') (L.ksb s') σ1 := by
    rw [hksb]
    refine hR.frame (fun b hb => hmV b (VsWrite.aligned hP.vs hb) (vsWrite_vobj hP.vs hb))
      (by rw [harch]) (fun p hp => hkp _ (fun y hy => ?_))
    obtain ⟨f, hf, -⟩ := hR.pool p hp
    rw [hf] at hy; cases hy
  have hPt' : PtRel L4 L3 L2 L1 (L.mem s) σ → PtRel L4 L3 L2 L1 (L.mem s') σ1 := fun hPt => by
    refine hPt.frame (fun b hb => hmV b (PtWAll.aligned hP.pt hb) ?_) (fun q hq => hkp _ (fun y hy => ?_))
    · obtain ⟨q, hq, i, hi, rfl⟩ := hb
      exact table_vobj hP.pt hq hi _
    · obtain ⟨ao, hao⟩ := hPt.arch hq
      rw [hao] at hy; cases hy
  -- the endpoint relation
  have hEp1 := Endp.write_state_rel hP.ep s σ hEp hT hk hqE .restart (by decide) _ hv
  have hEp' : Endp.EpStateRel T E R B (L.mem s') σ1 := by
    obtain ⟨hR1, -, -⟩ := hEp1
    have hR1' : Endp.EpStateRel T E R B (L.mem (L.wr s (stA ct) sched.TS_RESTART)) σ1 :=
      Endp.EpStateRel.frame hR1 hP.ep (fun _ _ _ => rfl) (Endp.KView.stsAct' _ _)
    rcases hcase with rfl | rfl
    · exact hR1'
    · refine Endp.EpStateRel.frame hR1' hP.ep (fun b hb hf => ?_) (Endp.KView.refl _)
      rw [L.mem_wr _ _ _ _ (by rw [← hW2]; exact hW2a) hb, if_neg]
      intro e
      have hb' : b = W2 := by rw [hW2]; simpa using e.symm
      subst hb'
      exact hP.nodeE _ (by rw [hW2v]; omega) (by rw [hW2v]; omega) hf
  have hKr' : KRootRel (L.mem s') (L.ksb s') σ1 := by
    unfold KRootRel globCr3 at hKr ⊢
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [hksb, hmK _ (by unfold Aligned; rw [hkv]; omega) (by rw [hkv]; omega) (by rw [hkv]; omega), harch]
    exact hKr
  refine ⟨hVs, hPt', ⟨⟨hS', hEp', hN', ?_, ?_, hKr', by rw [harch]; exact hAr⟩, ?_⟩, hksb, hmV⟩
  · rw [hksb]; exact IrqRel.ksFrame hIrq hkf hka (fun b hb h1 h2 _ => hmK b hb h1 h2) hist hinode
  · rw [hksb]; exact IoRel.ksFrame hIo hkf hka (fun b hb h1 h2 _ => hmK b hb h1 h2) (by rw [harch])
  · refine ⟨hP.ep, by rw [hksb]; exact hP.vs, hP.pt, hP.pl, fun y hy => ?_, fun y h1 h2 => ?_, hP.po, hP.ps,
      by rw [hksb]; exact hP.pv, by rw [hksb]; exact hP.vo, by rw [hksb]; exact hP.sd, by rw [hksb]; exact hP.tko⟩
    · rw [hksb]
      refine hP.disj y (OObj.of_kh hksb (fun q z n hq => ?_) hy)
      rw [hσ1, Notif.stsAct_kheap, Notif.updK_kheap] at hq
      by_cases e : q = ct.bv
      · subst e; rw [Function.update_self] at hq; cases hq
      · rwa [Function.update_of_ne e] at hq
    · have : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hksb]
      rw [this] at h1 h2; exact hP.nodeE y h1 h2

/-- **`VsSubHyps` for the composite relation.** -/
theorem vsSubHyps_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} :
    VsSubHyps st A P L4 L3 L2 L1 th (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  restart := fun s a σ ct x hS hR hPt hcur hk hrun =>
    WP.spec_mono (restart_top s a σ ct x hS hR hcur hk hrun) fun _ h => ⟨h.1, h.2.1 hPt, h.2.2.1, h.2.2.2.1⟩
  insStable := fun s s' a σ σ' hS hw hI => insStable_top s s' a σ σ' hS hw hI

end

end

end Fl4Proofs.P3.Vs
