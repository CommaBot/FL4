/-
P3 (DESIGN.md §9), CSpace (KENTRY-PLAN g2g (a')): **every run of primitive
steps keeps `LiveDN`** (StepSem's `Steps`), so each decode that ends through
`Steps` (the CNode copy family, IRQ / IO port control, IRQ handler, domain,
IO port) can end in `LiveDN` as well as `JAtZ`.

* StepSem's `slot` (an insert) now also gives the inserted cap non-null and
  no zombie, `cslot` (a CNode copy, move or rotate) gives `CnLive` (every
  written non-null cap has the shape of a non-null cap of the written slots
  before, and every such cap survives up to its shape) and the original bit
  of a written slot left null cleared (CnodeCopy's `NullSrc`,
  XTopCnode's `invoke_nullOrig`). `shape` keeps thread and zombie caps and a
  CNode cap's object (`refs_shape`, `shape_thread`, `shape_zombie`).
* `ZNoBlk`: no zombie names an object inside the kernel-state block (the IRQ
  node's CNodes; l4v: no cap names an IRQ node CNode, `valid_global_refs`).
  It replaces "no zombie names the destination CNode" when the destination
  is in the block (`DestLive`'s right disjunct, IRQHandler's insert).
* `JAtZ.schW_notDbg`: a scheduler step's word is no debug word.
* `LiveDN.wstep`: a step writing slot words only, at the slots `W` (each in a
  live CNode, `DestLive`), keeps `LiveDN` and `ZNoBlk`: from "every zombie
  after was one before" and "every non-null cap before survives up to its
  shape", the original bits off `W` kept and `W`'s null slots unoriginal.
* `QL` / `stepClosed_jatL`: `JAtZ ∧ LiveDN ∧ ZNoBlk` is closed under the
  primitive steps, each started from `J.addDeadSet hL.1.ztcb` and taken at the
  same dead set (XTopJointRest's `jowes_restartD`, `jowes_ksD`, and the
  `JOwesD` / `JOwesCsD` forms of `jowes_ins`, `jowes_cn`, `jowes_sched`);
  `Steps.jatL`.
-/
import Fl4Proofs.P3.XTopJointLiveIns
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

theorem refs_shape (q : U64) (c : capability.Cap) : RefsObj q (shape c) ↔ RefsObj q c := by
  cases c <;> exact Iff.rfl

theorem shape_refs {c' c : capability.Cap} (h : shape c' = shape c) (q : U64) : RefsObj q c' ↔ RefsObj q c := by
  rw [← refs_shape q c', h, refs_shape]

theorem shape_thread (c : capability.Cap) (w : U64) : shape c = .Thread w ↔ c = .Thread w := by
  cases c <;> simp [shape]

theorem shape_zombie (c : capability.Cap) (p zt n : U64) : shape c = .Zombie p zt n ↔ c = .Zombie p zt n := by
  cases c <;> simp [shape]

/-- **No zombie names an object inside the kernel-state block** [J]
(module docstring). -/
def ZNoBlk (th : TypedHeap) (m : U64 → U64) (kb : U64) : Prop :=
  ∀ y, IsSlot th y → ∀ p zt n, capV m y = .Zombie p zt n → ∀ k, th p = some k →
    ¬ (kb.val ≤ p.val ∧ p.val + objSize k ≤ kb.val + 13568)

theorem ZNoBlk.of_same {th : TypedHeap} {m m' : U64 → U64} {kb kb' : U64} (h : ZNoBlk th m kb)
    (hS : SlotsSame th m m') (hk : kb' = kb) : ZNoBlk th m' kb' := by
  subst hk
  intro y hy p zt n hz
  exact h y hy p zt n (by rw [← hS.capV hy]; exact hz)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
  {D : Set U64}

/-- **A scheduler step's word is no debug word** (`SchW`: the TCBs' queue
words, the current node but its debug head, the domain words). -/
theorem JAtZ.schW_notDbg {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : SchW (L := L) Z.T Z.c s b) : ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b := by
  have hS := J.xtop.fin.1.1.1
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
  have hnb : ∀ c, L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := fun _ => rfl
  rcases hb with ⟨y, hy, e | e | e⟩ | hn | hd
  · subst e; exact P1.notDbgW_field hq.tcbs hq.nodes (hTe ▸ hy) (by simp) (by simp)
  · subst e; exact P1.notDbgW_field hq.tcbs hq.nodes (hTe ▸ hy) (by simp) (by simp)
  · subst e; exact P1.notDbgW_field hq.tcbs hq.nodes (hTe ▸ hy) (by simp) (by simp)
  · have hk : Sched.KFoot st Z.T Z.N Z.C Z.c s σ b := Sched.KFoot.of_sfoot (Or.inr ⟨hn.1, hn.2.1⟩)
    rintro (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
    · exact Sched.KFoot.ne_tcbw hS hk (by rw [hTe]; exact hy) (K := 3576#u64) (by simp)
        (by unfold Sched.SOff Sched.SOffL; decide) e
    · exact Sched.KFoot.ne_tcbw hS hk (by rw [hTe]; exact hy) (K := 3584#u64) (by simp)
        (by unfold Sched.SOff Sched.SOffL; decide) e
    · obtain ⟨h1, h2, h3⟩ := hn
      have h4 := congrArg UScalar.val e
      rw [P1.nodeAt_val (hq.nodes c hc) (by simp [P1.debug_val]), P1.debug_val] at h4
      rw [hnb] at h1 h2 h3 h4
      omega
  · have hv := domKW_val hd
    refine J.notDbg' (fun p hp => ?_) (fun c _ => ?_)
    · have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
      rw [e12]; rcases hq.ksOut p hp with h | h <;> omega
    · rw [hnb]; omega

set_option maxHeartbeats 4000000 in
/-- **A step writing slot words at the slots `W` keeps `LiveDN` and
`ZNoBlk`** (module docstring). -/
theorem LiveDN.wstep {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s))
    {G' : MdbGhost} {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (J' : JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ')
    (hD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D')
    (hid : σ'.idleThread = σ.idleThread) (hw : P1.WritesIn st s s' (InSlot Z.th))
    (W : List Fl4Spec.CslotPtr)
    (hW : ∀ sl ∈ W, ∃ p r, sl.1 = p.bv ∧ Z.th p = some (.cnode r) ∧ sl.2.length = r ∧
      DestLive Z.th (L.mem s) (L.ksb s) p)
    (hcW : ∀ y, IsSlot Z.th y → (∀ sl ∈ W, y ≠ cslotAddr sl) → capV (L.mem s') y = capV (L.mem s) y)
    (hoW : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ sl ∈ W)
    (hNO : ∀ sl ∈ W, capV (L.mem s') (cslotAddr sl) = .Null → σ'.isOriginalCap sl = false)
    (hZ : ∀ y, IsSlot Z.th y → ∀ p zt n, capV (L.mem s') y = .Zombie p zt n →
      ∃ y0, IsSlot Z.th y0 ∧ capV (L.mem s) y0 = .Zombie p zt n)
    (hK2 : ∀ y0, IsSlot Z.th y0 → capV (L.mem s) y0 ≠ .Null →
      ∃ y, IsSlot Z.th y ∧ capV (L.mem s') y ≠ .Null ∧ shape (capV (L.mem s') y) = shape (capV (L.mem s) y0)) :
    LiveDN (L := L) Z.th H Cs G' s' σ' ∧ ZNoBlk Z.th (L.mem s') (L.ksb s') := by
  obtain ⟨hL, ⟨lst, hDW⟩, hN⟩ := hLv
  have hP : Placed Z.th := J.xtop.rel.1
  have hM := J.xtop.rel.2.1.2.2.1
  have hM' := J'.xtop.rel.2.1.2.2.1
  have hFI := J.xtop.rel.2.2.1
  have hks : L.ksb s' = L.ksb s := hw.1
  have hmemS : ∀ y ∈ Z.G.chains.flatten, IsSlot Z.th y := fun y hy => ((hM.members y).1 hy).1
  have hmemN : ∀ y ∈ Z.G.chains.flatten, capV (L.mem s) y ≠ .Null := fun y hy => by
    obtain ⟨-, c0, h0, hn0⟩ := (hM.members y).1 hy
    rw [capV_of_capAt h0]; exact hn0
  have hinG' : ∀ y, IsSlot Z.th y → capV (L.mem s') y ≠ .Null → y ∈ G'.chains.flatten := fun y hy hn =>
    (hM'.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩
  -- the written slots
  have hWat : ∀ sl ∈ W, ∃ p r i, Z.th p = some (.cnode r) ∧ IsSlotAt Z.th p i ∧ cslotAddr sl = slotOf p i ∧
      AbsSlot Z.th sl ∧ DestLive Z.th (L.mem s) (L.ksb s) p := fun sl hsl => by
    obtain ⟨p, r, h1, hp, hl, hDL⟩ := hW sl hsl
    have hA : AbsSlot Z.th sl := ⟨p, h1, Or.inl (by rw [hl]; exact hp)⟩
    obtain ⟨p', i, hpi, h1', hxe⟩ := hA.at
    have e : p' = p := P1.eq_of_bv (h1'.symm.trans h1)
    subst e
    exact ⟨p', r, i, hp, hpi, hxe, hA, hDL⟩
  -- a live container stays covered
  have hcov : ∀ p r i, Z.th p = some (.cnode r) → IsSlotAt Z.th p i → DestLive Z.th (L.mem s) (L.ksb s) p →
      (∃ y ∈ G'.chains.flatten, RefsObj p (capV (L.mem s') y)) ∨ KsSlot (L.ksb s') (slotOf p i) := by
    intro p r i hp hpi hDL
    rcases hDL with ⟨y, r', gs, g, hy, hc⟩ | hb
    · obtain ⟨y', hy', hn', hsh⟩ := hK2 y hy (by rw [hc]; exact fun h => by cases h)
      exact Or.inl ⟨y', hinG' y' hy' hn', (shape_refs hsh p).2 (by rw [hc]; rfl)⟩
    · right
      obtain ⟨hb1, hb2⟩ := hb _ hp
      have hi : i < 2 ^ r := by
        rcases hpi with ⟨r'', hp', hi⟩ | ⟨hp', -⟩
        · rw [hp] at hp'; cases hp'; exact hi
        · rw [hp] at hp'; cases hp'
      have hfit := hP.fits p _ hp
      simp only [objSize] at hb2 hfit
      have hsv : (slotOf p i).val = p.val + 32 * i := slotOf_val (by omega)
      show (L.ksb s').val ≤ (slotOf p i).val ∧ (slotOf p i).val < (L.ksb s').val + 13568
      rw [hks, hsv]
      omega
  -- no zombie names a live container
  have hnz : ∀ p r, Z.th p = some (.cnode r) → DestLive Z.th (L.mem s) (L.ksb s) p →
      ∀ y, IsSlot Z.th y → ∀ zt n, capV (L.mem s) y ≠ .Zombie p zt n := by
    intro p r hp hDL y hy zt n hz
    rcases hDL with ⟨y1, r', gs, g, hy1, hc⟩ | hb
    · have hne : y1 ≠ y := fun e => by rw [e, hz] at hc; cases hc
      exact FinInv.zombie_alone hFI hM hy hz y1 hy1 hne (refsObj_objRefs (by rw [hc]; rfl))
    · exact hZB y hy p zt n hz _ hp (hb _ hp)
  -- a slot off `W` in use after was in use before
  have hU : ∀ y, IsSlot Z.th y → (∀ sl ∈ W, y ≠ cslotAddr sl) → InUse (L.mem s') σ' y → InUse (L.mem s) σ y := by
    intro y hy hyW hu
    rcases hu with hu | ⟨x, hx, ho⟩
    · exact Or.inl (by rw [← hcW y hy hyW]; exact hu)
    · rcases hoW x ho with ho' | hxW
      · exact Or.inr ⟨x, hx, ho'⟩
      · exact (hyW x hxW hx.symm).elim
  -- the debug words
  have hdk : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' := dbgKeep_of_writes J.blk hw fun _ hb => J.inSlot_notDbg hb
  have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s := ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
  have hc0 : 0#u64 ∈ Cs := J.kern.cs0
  have hhd : dbgHead (L := L) s' = dbgHead (L := L) s := by
    unfold dbgHead
    rw [nodeAt_of_ksb hdk.1]
    exact hdk.2 _ (Or.inr ⟨0#u64, hc0, rfl⟩)
  have hNt : ∀ k, dbgNth (L.mem s') k (dbgHead (L := L) s') = dbgNth (L.mem s) k (dbgHead (L := L) s) :=
    fun k => by
      rw [hhd]
      exact dbgNth_keep (fun y hy => hdk.2 _ (Or.inl ⟨y, hy, Or.inl rfl⟩)) (fun y hy => hTz.dn y hy) k _
        (hTz.dh _ hc0)
  have hL' : LiveJ (L := L) Z.th H G' s' σ' := by
    refine ⟨fun q i hqi hu => ?_, fun k hk hki => ?_, fun y hy p zt n hz i hpi hni hu => ?_,
      fun y hy p zt n hz hzt => ?_⟩
    · by_cases hyW : ∀ sl ∈ W, slotOf q i ≠ cslotAddr sl
      · rcases hL.slots q i hqi (hU _ ⟨q, i, hqi, rfl⟩ hyW hu) with ⟨y, hy, hr⟩ | hb
        · obtain ⟨y', hy', hn', hsh⟩ := hK2 y (hmemS y hy) (hmemN y hy)
          exact Or.inl ⟨y', hinG' y' hy' hn', (shape_refs hsh q).2 hr⟩
        · exact Or.inr (by rw [hks]; exact hb)
      · push_neg at hyW
        obtain ⟨sl, hsl, e⟩ := hyW
        obtain ⟨p, r, i', hp, hpi, hxe, -, hDL⟩ := hWat sl hsl
        obtain ⟨e1, e2⟩ := slotOf_inj hP hqi hpi (e.trans hxe)
        subst e1; subst e2
        exact hcov q r i hp hqi hDL
    · rw [hNt] at hk hki ⊢
      obtain ⟨y, hy, hr⟩ := hL.dbg k hk (by rw [← hid]; exact hki)
      obtain ⟨y', hy', hn', hsh⟩ := hK2 y (hmemS y hy) (hmemN y hy)
      rw [hr] at hsh
      have hsh' : shape (capV (L.mem s') y') = .Thread (dbgNth (L.mem s) k (dbgHead (L := L) s)) := hsh
      exact ⟨y', hinG' y' hy' hn', (shape_thread _ _).1 hsh'⟩
    · obtain ⟨y0, hy0, hz0⟩ := hZ y hy p zt n hz
      by_cases hyW : ∀ sl ∈ W, slotOf p i ≠ cslotAddr sl
      · exact hL.zslots y0 hy0 p zt n hz0 i hpi hni (hU _ ⟨p, i, hpi, rfl⟩ hyW hu)
      · push_neg at hyW
        obtain ⟨sl, hsl, e⟩ := hyW
        obtain ⟨p', r, i', hp, hpi', hxe, -, hDL⟩ := hWat sl hsl
        obtain ⟨e1, -⟩ := slotOf_inj hP hpi hpi' (e.trans hxe)
        subst e1
        exact hnz p r hp hDL y0 hy0 zt n hz0
    · obtain ⟨y0, hy0, hz0⟩ := hZ y hy p zt n hz
      exact J'.jcov.dead p (hD p ⟨y0, hy0, zt, n, hz0, hzt⟩)
  refine ⟨⟨hL', ⟨lst, J.dbgWF_keep J' rfl rfl hDW hdk⟩, fun sl hA h => ?_⟩, fun y hy p zt n hz => ?_⟩
  · by_cases hsW : sl ∈ W
    · exact hNO sl hsW h
    · have hne : ∀ sl' ∈ W, cslotAddr sl ≠ cslotAddr sl' := fun sl' hsl' e => by
        obtain ⟨-, -, -, -, -, -, hA', -⟩ := hWat sl' hsl'
        exact hsW (by rw [cslotAddr_inj hP hA hA' e]; exact hsl')
      have h0 : capV (L.mem s) (cslotAddr sl) = .Null := by rw [← hcW _ hA.isSlot hne]; exact h
      cases ho : σ'.isOriginalCap sl
      · rfl
      · rcases hoW sl ho with ho' | hm
        · rw [hN sl hA h0] at ho'; cases ho'
        · exact absurd hm hsW
  · obtain ⟨y0, hy0, hz0⟩ := hZ y hy p zt n hz
    rw [hks]; exact hZB y0 hy0 p zt n hz0

variable (arI) in
/-- **`JAtZ ∧ LiveDN ∧ ZNoBlk`'s instance of `StepClosed`** (module
docstring). -/
def QL (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A)
    (σ' : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → LiveDN (L := L) Z.th H Cs Z.G s σ →
    ZNoBlk Z.th (L.mem s) (L.ksb s) →
    ∃ (G' : MdbGhost) (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ' ∧ LiveDN (L := L) Z.th H Cs G' s' σ' ∧
      ZNoBlk Z.th (L.mem s') (L.ksb s')

set_option maxHeartbeats 8000000 in
/-- **`JAtZ ∧ LiveDN ∧ ZNoBlk` is closed under the primitive steps** (module
docstring). -/
theorem stepClosed_jatL (hAM : ARMask arI AR) {th : TypedHeap} :
    StepClosed (L := L) arI th (QL (L := L) arI AR th) := by
  refine ⟨fun s1 a1 σ1 s2 a2 σ2 s3 a3 σ3 h1 h2 Z H Cs Ac Lst D hth J hL hZ => ?_,
    fun s a σ ct x s1 hcur hk htcb hrun hs1 Z H Cs Ac Lst D hth J hL hZ => ?_,
    fun s s' a a' σ σ' hw hO hdk hdl hds hirq hio harch Z H Cs Ac Lst D hth J hL hZ => ?_,
    fun s s' a σ σ' G' c ps pd rs rd idxs idxd hps hpd hci hld hcap hnull hnu hw hCR hFI hMO hTS hTK hT3 hDL hDl hVT
      hnn hnz Z H Cs Ac Lst D hth J hL hZ => ?_,
    fun s s' a σ σ' hS Z H Cs Ac Lst D hth J hL hZ => ?_,
    fun s s' a σ σ' G' hcn hkc hCK hUK horig hw hCR hFI hMO hTS hTK hT3 hkz hDl W hW hcW hoW hUS hVT hLW hNO
      Z H Cs Ac Lst D hth J hL hZ => ?_⟩
  · obtain ⟨G1, V1, Ac1, Lst1, D1, J1, hL1, hZ1⟩ := h1 Z H Cs Ac Lst D hth J hL hZ
    obtain ⟨G2, V2, Ac2, Lst2, D2, J2, hL2, hZ2⟩ := h2 (Z.mv G1 V1) H Cs Ac1 Lst1 D1 hth J1 hL1 hZ1
    exact ⟨G2, V2, Ac2, Lst2, D2, J2, hL2, hZ2⟩
  · -- the restart (as XTopJointWJLRestart's `WJL.restart`)
    subst hth
    have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.1.ztcb
    have h := XTopAt.restart J.xtop hcur hk hrun
    rw [hs1, WP.spec_ok] at h
    obtain ⟨hX1, hSS, hk1⟩ := h
    obtain ⟨hkb, hkz⟩ := kback_ksz_upd (σ' := Notif.stsAct (Notif.updK σ ct.bv
      (.tcb { x with tcbState := .restart })) ct.bv) hk (by rw [stsAct_kheap]; rfl)
    obtain ⟨Lst', R⟩ := jowes_restartD arI s a σ ct x s1 hcur hk htcb hrun hs1 J0 hX1
    have J1 : JAtZ (L := L) arI AR (Z.mv Z.G Z.vs) H Cs Ac Lst' (D ∪ ZTcb (L := L) Z.th s) s1 a
        (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) :=
      J0.cs_frame (G' := Z.G) hk1 hX1 hkb
        ((IpcFrKeep.of_updTcb (y := { x with tcbState := .restart }) hk rfl rfl).trans
          (IpcFrKeep.of_kheap (by rw [stsAct_kheap])))
        (JCs.same J0 hSS hkz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (J0.vkeep_sts (J0.thT ct htcb) hs1)
    have hT : ct ∈ Z.T := J.thT ct htcb
    have hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s1 := by
      obtain ⟨x', hk', hRt⟩ := J.xtop.ipc.tcb ct hT
      rw [hk] at hk'; cases hk'
      have hnbr : ¬ P1.BlockedR (L.mem s (P1.stA ct)) := fun hb => by
        have hq := Sched.blockedR_queued hRt.st hb
        cases hx : x.tcbState <;> simp_all [Fl4Spec.runnable, Fl4Spec.ipcQueuedThreadState]
      have hTe : Z.T = P1.Heap.tcbs H := by
        obtain ⟨Tr, Cq, hJ⟩ := J.jpl
        exact Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩
      rw [hTe] at hT
      exact P1.Foot.dbgKeep J.blk (Set.empty_subset _)
        (P1.sched.set_thread_state.restart_ok (Es := ∅) J.blk hT (fun h => hnbr (Or.inl h))
          (fun h => hnbr (Or.inr h)) hs1).2.1
    exact ⟨Z.G, Z.vs, Ac, Lst', _, J1, LiveDN.of_jstep J hL J1 rfl rfl hSS hK
      (orig_eq_of_slots J.xtop.rel.2.1.2.2.2.1 J1.xtop.rel.2.1.2.2.2.1 J.kern.orig J1.kern.orig hSS)
      (by unfold Notif.stsAct; split <;> rfl) (fun p hp => Or.inr hp), hZ.of_same hSS hk1⟩
  · -- a kernel-state step
    subst hth
    have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.1.ztcb
    have hX := J.xtop
    have hDR := hX.rel.2.2.2.1
    have hAR := hX.fin.1.1.2.2.2.2.2.2
    have hX1 : XTopAt (L := L) AR Z s' a' σ' := XTopAt.ksStep hX J.ks hw hO (hirq hX.fin.1.1.2.2.2.1)
      (hio hX.fin.1.1.2.2.2.2.1) (hDR.frame (fun o ho => hdk.2 o ho) hdl hds)
      (by rw [hO.cr3]; exact hAM _ _ _ hAR harch)
    have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
      hX.slotsSame_of hw fun b hb => by obtain ⟨K, h1, h2, -, e⟩ := hb; exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)
    obtain ⟨Ac', Lst', R⟩ := jowes_ksD arI s s' a a' σ σ' hw hO Z H Cs Ac Lst _ rfl J0 hX1
    have J1 : JAtZ (L := L) arI AR (Z.mv Z.G Z.vs) H Cs Ac' Lst' (D ∪ ZTcb (L := L) Z.th s) s' a' σ' :=
      J0.cs_frame hw.1 hX1 (KBack.of_kheap hO.kh) (IpcFrKeep.of_kheap hO.kh) (JCs.same J0 hSS (KSz.of_kheap hO.kh)) R
        (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (J0.vkeep_of hw fun _ hb => J0.ksW_nv hb)
    exact ⟨Z.G, Z.vs, Ac', Lst', _, J1, LiveDN.of_jstep J hL J1 rfl rfl hSS
      (dbgKeep_of_writes J.blk hw fun _ hb => J.ksW_notDbg hb) hO.orig hO.idle (fun p hp => Or.inr hp),
      hZ.of_same hSS hw.1⟩
  · -- an insertion
    subst hth
    have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.1.ztcb
    have hX := J.xtop
    have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) c (ps.bv, idxs) (pd.bv, idxd) σ).1 := by rw [hci]; rfl
    have hcn := capInsert_nkn c _ _ σ _ hmem
    have hSt := hX.rel.2.1.1
    have hkc : KeepC σ σ' := keepC_of hcn (capInsert_nko c _ _ σ _ hmem) (by
      rintro p (rfl | hp)
      · obtain ⟨cs, h, -⟩ := hSt.cnode ps rs hps; exact ⟨rs, cs, h⟩
      · rw [Set.mem_singleton_iff.1 hp]; obtain ⟨cs, h, -⟩ := hSt.cnode pd rd hpd; exact ⟨rd, cs, h⟩)
    have hPl := hX.rel.1
    have hw' : P1.WritesIn st s s' (Sched.SlotWd Z.th) :=
      ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn (Sched.slotSpan_wd hPl hb h)⟩
    have hX1 := XTopAt.slotStep hX hw' hcn hkc hCR hFI hMO hTS
    obtain ⟨hC, Ac', Lst', R⟩ := jowes_ins arI s s' a σ σ' c ps pd rs rd idxs idxd hps hpd hci hld hcap hnull hnu hw
      hFI hMO hTK hT3 hDL hDl Z H Cs Ac Lst _ rfl J0 hX1
    have J1 : JAtZ (L := L) arI AR (Z.mv G' Z.vs) H Cs Ac' Lst' (D ∪ ZTcb (L := L) Z.th s) s' a σ' :=
      J0.cs_frame hw.1 hX1 (KBack.of_keepC hkc) (IpcFrKeep.of_keepC hkc) hC R hVT (J0.vkeep_slot hw)
    have hn0 : capV (L.mem s) (cslotAddr (pd.bv, idxd)) = .Null := capV_of_capAt hnull
    obtain ⟨hL1, hZ1⟩ := LiveDN.wstep J hL hZ J1 (fun p hp => Or.inr hp) hcn.idle hw [(pd.bv, idxd)]
      (fun sl hsl => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsl
        subst hsl; exact ⟨pd, rd, rfl, hpd, hld, hDL⟩)
      (fun y hy hne => hcap y hy (hne (pd.bv, idxd) (List.mem_singleton_self _)))
      (fun sl h => by
        by_cases e : sl = (pd.bv, idxd)
        · exact Or.inr (by simp [e])
        · exact Or.inl (by rw [← capInsert_orig c _ _ σ ((), σ') hmem sl e]; exact h))
      (fun sl hsl h => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsl
        subst hsl; exact absurd h hnn)
      (fun y hy p zt n h => by
        by_cases e : y = cslotAddr (pd.bv, idxd)
        · subst e; exact absurd h (hnz p zt n)
        · exact ⟨y, hy, by rw [← hcap y hy e]; exact h⟩)
      (fun y0 hy0 hn => by
        have e : y0 ≠ cslotAddr (pd.bv, idxd) := fun e => hn (by rw [e]; exact hn0)
        exact ⟨y0, hy0, by rw [hcap y0 hy0 e]; exact hn, by rw [hcap y0 hy0 e]⟩)
    exact ⟨G', Z.vs, Ac', Lst', _, J1, hL1, hZ1⟩
  · -- a scheduler step
    subst hth
    have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.1.ztcb
    have hX := J.xtop
    have hX1 := hX.schedStep J.ks J.thT hS
    have hW := (hS.2.1 Z.N Z.T Z.C Z.c J.thT hX.fin.1.1.1 hX.fin.1.1.2.2.1).2.1
    have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
      hX.slotsSame_of hW fun b hb => schW_oobj hX.fin.1.1.1.placed.tcb hb
    obtain ⟨Ac', Lst', R⟩ := jowes_sched arI s s' a σ σ' hS Z H Cs Ac Lst _ rfl J0 hX1
    have J1 : JAtZ (L := L) arI AR (Z.mv Z.G Z.vs) H Cs Ac' Lst' (D ∪ ZTcb (L := L) Z.th s) s' a σ' :=
      J0.cs_frame hW.1 hX1 (KBack.of_kheap hS.1.kh) (IpcFrKeep.of_kheap hS.1.kh)
        (JCs.same J0 hSS (KSz.of_kheap hS.1.kh)) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy)
        (J0.vkeep_of hW fun _ hb => J0.schW_nv hb)
    exact ⟨Z.G, Z.vs, Ac', Lst', _, J1, LiveDN.of_jstep J hL J1 rfl rfl hSS
      (dbgKeep_of_writes J.blk hW fun _ hb => J.schW_notDbg hb)
      (orig_eq_of_slots J.xtop.rel.2.1.2.2.2.1 J1.xtop.rel.2.1.2.2.2.1 J.kern.orig J1.kern.orig hSS)
      hS.1.idle (fun p hp => Or.inr hp), hZ.of_same hSS hW.1⟩
  · -- a CNode-only step
    subst hth
    have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.1.ztcb
    have hX := J.xtop
    have hPl := hX.rel.1
    have hw' : P1.WritesIn st s s' (Sched.SlotWd Z.th) :=
      ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn (Sched.slotSpan_wd hPl hb h)⟩
    have hX1 := XTopAt.slotStep hX hw' hcn hkc hCR hFI hMO hTS
    obtain ⟨hC, Ac', Lst', R⟩ := jowes_cn arI s s' a σ σ' hcn hkc hCK hUK horig hw hFI hMO hkz hTK hT3 hDl W hW hcW
      hoW hUS Z H Cs Ac Lst _ rfl J0 hX1
    have J1 : JAtZ (L := L) arI AR (Z.mv G' Z.vs) H Cs Ac' Lst' (D ∪ ZTcb (L := L) Z.th s) s' a σ' :=
      J0.cs_frame hw.1 hX1 (KBack.of_keepC hkc) (IpcFrKeep.of_keepC hkc) hC R hVT (J0.vkeep_slot hw)
    have hWs : ∀ sl ∈ W, IsSlot Z.th (cslotAddr sl) := fun sl hsl => by
      obtain ⟨p, r, h1, hp, hl, -⟩ := hW sl hsl
      exact (show AbsSlot Z.th sl from ⟨p, h1, Or.inl (by rw [hl]; exact hp)⟩).isSlot
    obtain ⟨hL1, hZ1⟩ := LiveDN.wstep J hL hZ J1 (fun p hp => Or.inr hp) hcn.idle hw W hW hcW hoW hNO
      (fun y hy p zt n h => by
        by_cases hyW : ∀ sl ∈ W, y ≠ cslotAddr sl
        · exact ⟨y, hy, by rw [← hcW y hy hyW]; exact h⟩
        · push_neg at hyW
          obtain ⟨sl, hsl, rfl⟩ := hyW
          obtain ⟨sl0, hsl0, -, hsh⟩ := hLW.1 sl hsl (by rw [h]; exact fun h' => by cases h')
          rw [h] at hsh
          have hsh' : shape (capV (L.mem s) (cslotAddr sl0)) = .Zombie p zt n := hsh.symm
          exact ⟨_, hWs sl0 hsl0, (shape_zombie _ p zt n).1 hsh'⟩)
      (fun y0 hy0 hn => by
        by_cases hyW : ∀ sl ∈ W, y0 ≠ cslotAddr sl
        · exact ⟨y0, hy0, by rw [hcW y0 hy0 hyW]; exact hn, by rw [hcW y0 hy0 hyW]⟩
        · push_neg at hyW
          obtain ⟨sl0, hsl0, rfl⟩ := hyW
          obtain ⟨sl, hsl, hn', hsh⟩ := hLW.2 sl0 hsl0 hn
          exact ⟨_, hWs sl hsl, hn', hsh⟩)
    exact ⟨G', Z.vs, Ac', Lst', _, J1, hL1, hZ1⟩

/-- **`JAtZ`, `LiveDN` and `ZNoBlk` after a run of primitive steps.** -/
theorem Steps.jatL (hAM : ARMask arI AR) {th : TypedHeap} {s s' : S} {a a' : A} {σ σ' : Fl4Spec.State Unit}
    (h : Steps (L := L) arI th s a σ s' a' σ') (hth : Z.th = th) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hL : LiveDN (L := L) Z.th H Cs Z.G s σ) (hZ : ZNoBlk Z.th (L.mem s) (L.ksb s)) :
    ∃ (G' : MdbGhost) (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ' ∧ LiveDN (L := L) Z.th H Cs G' s' σ' ∧
      ZNoBlk Z.th (L.mem s') (L.ksb s') :=
  h _ (stepClosed_jatL hAM) Z H Cs Ac Lst D hth J hL hZ

end

end

end Fl4Proofs.P3
