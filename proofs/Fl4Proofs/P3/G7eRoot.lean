/-
P3 (issue #16, g7e; KENTRY-PLAN g7d (3), g7e): **the root facts carried
across the scheduler's writes**.

* `IdleVt σ` [J] (INV-PLAN §1.U3L D7): the idle TCB's vtable is no mapped
  PML4 cap. FL4's `switch_to_idle_thread` loads the kernel root, the spec's
  `archSwitchToIdleThread` is `setVmRoot idleThread`; they agree iff this
  holds (l4v: the idle thread is created with null caps, and no cap names it).
* `RootFr AR T P c s a σ`: G7cSwitch's `RootOK` at every state the scheduler
  reaches from `(s, σ)` before its switch: FL4 writes only `SFootN` words
  (TCB scheduler fields, the core's node, `next_domain`'s kernel-global
  words), the spec keeps the heap up to the FPU and `crF` (CR3, ASID table,
  global PML4, idle thread). `RootFr.now`, `RootFr.step`.
* **`JAtZR.rootFr`**: `RootFr` at a `JAtZR` state, given `IdleVt`. Every
  `SFootN` word is an `OObj` word (`tfoot_oobj`; `next_domain`'s words
  `ks+16/24/40` are kernel-global words), and `TopPlaced.disj` keeps them off
  every `VObj` word: the ASID table and pool words `VsRel` reads
  (`vsWrite_vobj`) and the slot words of TCBs (slot 1, the vtable). The kernel
  root word `ks+48` is no `SFootN` word (`tfoot_ksb`, and not 16/24/40). So
  the check of g7d (3)'s open point: `next_domain`'s kernel-global words are
  disjoint from the VSpace and slot words, no FINDING.
* `JAtZR.fire_ks`, `fire_dt`: FL4's timers keep the kernel-global words
  (`ndOK_fire`'s argument), hence the domain time.
* `JAtZR.idleVt_fire`: `IdleVt` at the finish state gives it after the
  timers (the idle TCB's slot 1 is kept, `slotsSame_of_footD`; both states
  relate it to the spec vtable by `StateRel.tcb`).
-/
import Fl4Proofs.P3.ScNextDomCFR
import Fl4Proofs.P3.G7cSwitch
import Fl4Proofs.P3.G7dVsRoot
import Fl4Proofs.P3.XTopJointJAtZRB
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Sched

noncomputable section

/-- **[J] `IdleVt`** (INV-PLAN §1.U3L D7; module docstring). -/
def IdleVt (σ : Fl4Spec.State Unit) : Prop :=
  ∃ x : Fl4Spec.Tcb, σ.kheap σ.idleThread = some (.tcb x) ∧
    ∀ p asid, x.tcbVtable ≠ .archObjectCap (.pml4Cap p (some asid))

theorem IdleVt.frame {σ σ' : Fl4Spec.State Unit} (h : IdleVt σ) (hk : HeapEqUpToFpu σ σ')
    (hi : σ'.idleThread = σ.idleThread) : IdleVt σ' := by
  obtain ⟨x, hx, hv⟩ := h
  obtain ⟨y, hy, e⟩ := hk.tcb hx
  have e1 : y.tcbVtable = x.tcbVtable := by have e2 := congrArg Fl4Spec.Tcb.tcbVtable e.1; exact e2
  exact ⟨y, by rw [hi]; exact hy, fun p asid h => hv p asid (e1.symm.trans h)⟩

/-- An outcome of a `CRK` spec function keeps `crF`. -/
theorem crf_of_crk {α : Type} {m : Fl4Spec.NonDet (Fl4Spec.State Unit) α} (h : Vs.CRK m)
    {σ σ' : Fl4Spec.State Unit} {a : α} {X : Prop} (he : m σ = ({(a, σ')}, X)) : Vs.crF σ' = Vs.crF σ :=
  h σ (a, σ') (by rw [he]; exact Set.mem_singleton _)

section
variable {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`RootOK` at every state the scheduler reaches before its switch**
(module docstring). -/
def RootFr (AR : A → Fl4Spec.Cr3 → Prop) (T P : Set U64) (c : U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (s' : S) (σ' : Fl4Spec.State Unit), P1.WritesIn st s s' (SFootN st T c s) → HeapEqUpToFpu σ σ' →
    Vs.crF σ' = Vs.crF σ → RootOK (L := L) AR T P s' a σ'

theorem RootFr.now {AR : A → Fl4Spec.Cr3 → Prop} {T P : Set U64} {c : U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : RootFr (L := L) AR T P c s a σ) : RootOK (L := L) AR T P s a σ :=
  h s σ (P1.WritesIn.refl _ _) (HeapEqUpToFpu.refl σ) rfl

theorem RootFr.step {AR : A → Fl4Spec.Cr3 → Prop} {T P : Set U64} {c : U64} {s s1 : S} {a : A}
    {σ σ1 : Fl4Spec.State Unit} (h : RootFr (L := L) AR T P c s a σ) (hw : P1.WritesIn st s s1 (SFootN st T c s))
    (hk : HeapEqUpToFpu σ σ1) (hc : Vs.crF σ1 = Vs.crF σ) : RootFr (L := L) AR T P c s1 a σ1 :=
  fun s' σ' hw' hk' hc' => h s' σ' (WritesIn.sfootN_trans hw hw') (hk.trans hk') (hc'.trans hc)

/-- Every `SFootN` word is a word of the other objects. -/
theorem sfootN_oobj {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) {b : U64} (h : SFootN st T c s b) :
    Vs.OObj st N T C E R B c s σ b := by
  rcases h with h | h
  · exact tfoot_oobj hS (Or.inl (KFoot.of_sfoot h))
  · right; left
    have h16 := ksW_val (kb := L.ksb s) (o := 16#u64) (by simp; omega)
    have h24 := ksW_val (kb := L.ksb s) (o := 24#u64) (by simp; omega)
    have h40 := ksW_val (kb := L.ksb s) (o := 40#u64) (by simp; omega)
    simp at h16 h24 h40
    rcases h with rfl | rfl | rfl <;> omega

/-- The `FEATURES` word (#65's 1 GiB-page bit) is no `SFootN` word. -/
theorem sfootN_feat {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) : ¬ SFootN st T c s (ksW (L.ksb s) 72#u64) := by
  have h16 := ksW_val (kb := L.ksb s) (o := 16#u64) (by simp; omega)
  have h24 := ksW_val (kb := L.ksb s) (o := 24#u64) (by simp; omega)
  have h40 := ksW_val (kb := L.ksb s) (o := 40#u64) (by simp; omega)
  have h72 := ksW_val (kb := L.ksb s) (o := 72#u64) (by simp; omega)
  simp at h16 h24 h40 h72
  rintro (h | h)
  · have := tfoot_ksb hS hNk (σ := σ) (Or.inl (KFoot.of_sfoot h)); omega
  · rcases h with e | e | e <;> (have := congrArg UScalar.val e; omega)

/-- The kernel root word is no `SFootN` word. -/
theorem sfootN_kr {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) : ¬ SFootN st T c s (ksW (L.ksb s) 48#u64) := by
  have h16 := ksW_val (kb := L.ksb s) (o := 16#u64) (by simp; omega)
  have h24 := ksW_val (kb := L.ksb s) (o := 24#u64) (by simp; omega)
  have h40 := ksW_val (kb := L.ksb s) (o := 40#u64) (by simp; omega)
  have h48 := ksW_val (kb := L.ksb s) (o := 48#u64) (by simp; omega)
  simp at h16 h24 h40 h48
  rintro (h | h)
  · have := tfoot_ksb hS hNk (σ := σ) (Or.inl (KFoot.of_sfoot h)); omega
  · rcases h with e | e | e <;> (have := congrArg UScalar.val e; omega)

variable {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 2000000 in
/-- **`RootFr` at a `JAtZR` state** (module docstring). -/
theorem JAtZR.rootFr {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (hIV : IdleVt σ) :
    RootFr (L := L) AR Z.T Z.P Z.c s a σ := by
  intro s' σ' hw hk hc
  have hS := J.xtop.fin.1.1.1
  have hTP := J.xtop.fin.1.2
  have hkf := J.kern.ksbFit
  have hka := J.kern.ksbAl
  have hks : L.ksb s' = L.ksb s := hw.1
  have hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable := congrArg (fun q => q.2.1) hc
  have hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := congrArg (fun q => q.2.2.1) hc
  have hid : σ'.idleThread = σ.idleThread := congrArg (fun q => q.2.2.2.1) hc
  have hout : ∀ b, P1.Aligned b → Vs.VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b → L.mem s' b = L.mem s b :=
    fun b hb hv => hw.mem_eq hb fun hf => hTP.disj b (sfootN_oobj hS hkf hf) hv
  refine ⟨⟨_, J.xtop.fin.1.1.2.2.2.2.2.2⟩, ?_, ?_, ?_, hIV.frame hk hid⟩
  · rw [hks]
    exact VsRel.frame J.xtop.fin.2.1 (fun b hb => hout b (VsWrite.aligned hTP.vs hb) (vsWrite_vobj hTP.vs hb)) hat
      (fun p hp => by
        obtain ⟨f, hf, -⟩ := J.xtop.fin.2.1.pool p hp
        rw [hf]; exact (hk.ntcb (fun _ e => by cases e)).2 hf)
  · obtain ⟨hR, hH⟩ := J.xtop.fin.1.1.2.2.2.2.2.1
    have hhu : σ'.archState.x64Plat = σ.archState.x64Plat := congrArg (fun q => q.2.2.2.2) hc
    unfold KRootRel
    refine ⟨?_, ?_⟩
    · unfold KRootW at hR ⊢
      have e : core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT = ksW (L.ksb s) 48#u64 := by
        unfold layout.ks.KERNEL_ROOT; rfl
      rw [hks, e, hw.mem_eq (ksW_al hkf hka (by decide) (by decide)) (sfootN_kr hS J.nk hkf)]
      rw [e] at hR
      rw [hR]; unfold globCr3; rw [hgp]
    · rw [hks]
      refine HugeRel.frame hH ?_ hhu
      have e72 : core.num.U64.wrapping_add (L.ksb s) layout.ks.FEATURES = ksW (L.ksb s) 72#u64 := by
        unfold layout.ks.FEATURES; rfl
      rw [e72]
      exact hw.mem_eq (ksW_al hkf hka (by decide) (by decide)) (sfootN_feat hS J.nk hkf)
  · intro t ht
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hth : Z.th t = some .tcb := (hJ.tcb t).2 (J.zH.1 t ht)
    obtain ⟨x, hkx, hsl⟩ := J.xtop.rel.2.1.1.tcb t hth
    obtain ⟨cp, ac, hcp, hac, hca⟩ := hsl 1 (by decide)
    rw [tcbCnodeMap_one] at hac
    have hv : x.tcbVtable = absCap cp := by injection hac with h; rw [h, hca.2]
    have hcp' : capAt (L.mem s) (slotOf t 1) = ok cp := hcp
    obtain ⟨y, hy, ey⟩ := hk.tcb hkx
    have e1 : y.tcbVtable = x.tcbVtable := by have e2 := congrArg Fl4Spec.Tcb.tcbVtable ey.1; exact e2
    have hP := J.xtop.rel.1
    have hx : IsSlot Z.th (slotOf t 1) := ⟨t, 1, Or.inr ⟨hth, by decide⟩, rfl⟩
    have hsv : (slotOf t 1).val = t.val + 32 * 1 :=
      (show IsSlotAt Z.th t 1 from Or.inr ⟨hth, by decide⟩).val hP
    have hw' : ∀ k, Off k → L.mem s' (wordOf (slotOf t 1) k) = L.mem s (wordOf (slotOf t 1) k) := fun k hk' =>
      hout _ (slot_word_aligned hP hx hk') (Or.inr (Or.inl ⟨t, hth, by rw [slot_word_val hP hx hk']; omega,
        by rw [slot_word_val hP hx hk']; have := hk'.lt; omega⟩))
    have hcap : capAt (L.mem s') (slotOf t 1) = capAt (L.mem s) (slotOf t 1) := by
      have h0 := hw' 0#u64 (Or.inl rfl)
      have h8 := hw' 8#u64 (Or.inr (Or.inl rfl))
      rw [wordOf_zero] at h0
      unfold Fl4Proofs.P3.capAt; rw [h0]; exact congrArg _ h8
    refine ⟨y, cp, hy, hcap.trans hcp', e1.trans hv, fun p asid hpe => ?_⟩
    subst hpe
    have h := J.vsc _ hx
    rw [capV_of_capAt hcp'] at h
    have h' : (true = false → p ∈ _) ∧ p ≠ 0#u64 ∧ (true = true → asid ≠ 0#u64 ∧ asid.val < 2 ^ 20) := h
    exact (h'.2.2 rfl).1

/-- **FL4's timers keep the kernel-global words** (`JAtZR.ndOK_fire`'s
argument). -/
theorem JAtZR.fire_ks {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s1 : S}
    (hf : P1.FootD st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s1) :
    ∀ o : U64, o.val < 256 → o.val % 8 = 0 → L.mem s1 (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o) := by
  have hkf := J.kern.ksbFit
  have hka := J.kern.ksbAl
  have hks := J.kern.hks
  have hH := J.kern.heap
  have hKW := J.kwApartJ (s' := s) rfl (fun c hc => J.blk.2.2.1.2.2.tm.npl c hc)
  intro o ho h8
  refine hf.mem_eq (ksW_al hkf hka ho h8) fun hb => ?_
  have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
  rcases hb with hb | hb
  · rcases hKW _ (ksW_al hkf hka ho h8) hb with e | e <;> rw [hv] at e <;> omega
  · rcases hb with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩
    · have hy' : H y = some .tcb := hy
      have hfit := hH.fits y _ hy'
      simp only [P1.HKind.bits] at hfit
      have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
      rw [h12] at hfit
      have hdv : (P1.dnA y).val = y.val + 3576 := by
        unfold P1.dnA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      have h3 := hks y .tcb hy' (fun z h => by cases h)
      simp only [P1.HKind.bits, h12] at h3
      have := congrArg UScalar.val e
      rw [hv, hdv] at this
      omega
    · have hy' : H y = some .tcb := hy
      have hfit := hH.fits y _ hy'
      simp only [P1.HKind.bits] at hfit
      have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
      rw [h12] at hfit
      have hdv : (P1.dpA y).val = y.val + 3584 := by
        unfold P1.dpA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      have h3 := hks y .tcb hy' (fun z h => by cases h)
      simp only [P1.HKind.bits, h12] at h3
      have := congrArg UScalar.val e
      rw [hv, hdv] at this
      omega
    · have hnv := P1.nodeAt_val (J.blk.2.2.1.2.2.tm.npl c hc) (off := layout.node.DEBUG_TCBS) (by simp)
      unfold P1.LawfulStore.nodeBase at hnv
      have := congrArg UScalar.val e
      rw [hv, hnv] at this
      simp [layout.node.DEBUG_TCBS] at this
      omega

/-- The domain time read from the kernel-global word. -/
theorem fire_dt {N T C : Set U64} {c : U64} {s s1 : S} {σ σ1 : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hS1 : SchedRel st N T C c s1 σ1) (hk : L.ksb s1 = L.ksb s)
    (hm : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → L.mem s1 (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o)) :
    σ1.domainTime = σ.domainTime := by
  obtain ⟨Q, R, -, hs⟩ := hS.lists
  obtain ⟨Q1, R1, -, hs1⟩ := hS1.lists
  rw [hs1.domTime, hs.domTime, dtA_ks, dtA_ks, hk, hm 16#u64 (by decide) (by decide)]

set_option maxHeartbeats 2000000 in
/-- **`IdleVt` after FL4's timers** (module docstring). -/
theorem JAtZR.idleVt_fire (hAT : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (hIV : IdleVt σ) {s1 : S} {a1 : A}
    (hfr : timer.fire st arI s a = ok (s1, a1)) {σ1 : Fl4Spec.State Unit} (hF : Fires σ σ1)
    {V1 : XVs} {Ac1 : Set U64} {Lst1 : U64 → List U64} {D1 : Set U64}
    (J1 : JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1) : IdleVt σ1 := by
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  have hit := hc.idleT
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hth : Z.th (nodeW st s Z.c layout.node.IDLE_THREAD) = some .tcb := (hJ.tcb _).2 (J.zH.1 _ hit)
  obtain ⟨x, hkx, hsl⟩ := J.xtop.rel.2.1.1.tcb _ hth
  obtain ⟨cp, ac, hcp, hac, hca⟩ := hsl 1 (by decide)
  rw [tcbCnodeMap_one] at hac
  have hv : x.tcbVtable = absCap cp := by injection hac with h; rw [h, hca.2]
  have hcp' : capAt (L.mem s) (slotOf (nodeW st s Z.c layout.node.IDLE_THREAD) 1) = ok cp := hcp
  obtain ⟨x0, hx0, hv0⟩ := hIV
  rw [hs.idleTh, hkx] at hx0
  cases hx0
  have hnp : ∀ p asid, cp ≠ .Pml4 p true asid := fun p asid e => by
    subst e; exact hv0 p.bv asid.bv hv
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun _ h => h
  have hfk := spec_ok_post (P1.timer.fire.kw hAT hNt s a J.blk) hfr
  simp only [WP.uncurry'_pair] at hfk
  obtain ⟨⟨Q', R', hq⟩, -⟩ := J.blk
  have hSS := slotsSame_of_footD J.xtop.rel.1 (hJ.kwOutBlk J.blk) hq.tcbs hq.nodes hfk
  have hx : IsSlot Z.th (slotOf (nodeW st s Z.c layout.node.IDLE_THREAD) 1) := ⟨_, 1, Or.inr ⟨hth, by decide⟩, rfl⟩
  have hc1 := (hSS.capAt hx).trans hcp'
  obtain ⟨y, hky, hsl1⟩ := J1.xtop.rel.2.1.1.tcb _ hth
  obtain ⟨cp1, ac1, hcp1, hac1, hca1⟩ := hsl1 1 (by decide)
  rw [tcbCnodeMap_one] at hac1
  have hv1 : y.tcbVtable = absCap cp1 := by injection hac1 with h; rw [h, hca1.2]
  have hcp1' : capAt (L.mem s1) (slotOf (nodeW st s Z.c layout.node.IDLE_THREAD) 1) = ok cp1 := hcp1
  have e : cp1 = cp := by
    have := hcp1'.symm.trans hc1
    simpa using this
  have hid : σ1.idleThread = σ.idleThread := congrArg (fun q => q.2.2.2.1) (Sched.crF_fires hF)
  refine ⟨y, by rw [hid, hs.idleTh]; exact hky, ?_⟩
  rw [hv1, e]; exact absCap_not_pml4 hnp

end

end

end Fl4Proofs.P3
