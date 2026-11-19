/-
P3 (DESIGN.md §9): **the IRQ handler path's premises at the invocation
entry from `JAtZ`** (XTopJointEntry's former `JIrqHPath` fields `hex` and
`hP1`, both [J] premises before).

* `ExtraNamed`, `lookup_extra_named`: every slot `lookup_extra_caps`
  returns lies in a CNode named by a CNode cap held in a slot (the lookup's
  `CnRef`, the root held in the thread's TCB slot 0: `lookup_extra_live`'s
  `DestLive` without its kernel-block disjunct).
* `JAtZ.irqExtraNe`: such a slot is no IRQ node slot (`SpecGlob.ref`: no cap
  but a frame cap names an IRQ node CNode, l4v `valid_global_refs`; the IRQ
  node CNodes are the radix-0 CNodes at `nodeA`, `IntLayout.node`,
  `IrqRel.node`).
* `JAtZ.kwApartJ`: P1's kernel-write words (`KW`) of `JAtZ`'s sets miss the
  domain schedule (`JKern.hks`: `H`'s objects but the `other` ones lie
  outside the kernel-state block; `HeapOK`; the nodes above the domain
  schedule, P1's `NodePlaced`).
* `JAtZ.irqDelP1J`: IrqDom's `IrqDelP1` (P1's `BlkOK` after the caller's
  restart, `set_thread_state.restart_ok` on `JAtZ.blk`; the IRQ slot's
  notification in P1's sets by `JPlaced.typed`; `kwApartJ`).
-/
import Fl4Proofs.P3.XTopJointGrant
import Fl4Proofs.P3.XTopJoint
import Fl4Proofs.P3.JEntryKs
import Fl4Proofs.P3.IrqDom
import Fl4Proofs.P3.IntInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Named
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- Every nonzero extra slot lies in a CNode of the typed heap named by a
CNode cap held in a slot. -/
def ExtraNamed (th : TypedHeap) (m : U64 → U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) : Prop :=
  ∀ j, j < 3 → Ipc.exAt extra j ≠ 0#u64 → ∃ ps idx, Ipc.exAt extra j = cslotAddr (ps.bv, idx) ∧
    th ps = some (.cnode idx.length) ∧ ∃ y r gs g, IsSlot th y ∧ capV m y = .CNode ps r gs g

/-- A CNode reached by a lookup from a root held in a slot is named by a
CNode cap held in a slot (`DestLive.of_cnRef`'s first disjunct). -/
theorem cnRef_named {th : TypedHeap} {mem : U64 → U64} {c0 : capability.Cap} {pd : U64}
    (h : CnRef th mem c0 pd) (hroot : ∃ y, IsSlot th y ∧ capV mem y = c0) :
    ∃ y r gs g, IsSlot th y ∧ capV mem y = .CNode pd r gs g := by
  obtain ⟨r, gs, g, hr⟩ := h
  rcases hr with ⟨p, r', idx, hp, hl, hc⟩ | e
  · exact ⟨cslotAddr (p.bv, idx), r, gs, g, AbsSlot.isSlot ⟨p, rfl, Or.inl (by rw [hl]; exact hp)⟩,
      capV_of_capAt hc⟩
  · obtain ⟨y, hy, hyc⟩ := hroot
    exact ⟨y, r, gs, g, hy, by rw [hyc, e]⟩

set_option maxHeartbeats 4000000 in
/-- **`lookup_extra_caps`' slots lie in CNodes named by caps** (as
`lookup_extra_live`: each reached by `lookup_slot` from the thread's CSpace
root, held in its TCB slot 0). -/
theorem lookup_extra_named (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) {t : U64} (ht : th t = some .tcb) (sbw : U64)
    (info : msginfo.MessageInfo) :
    ipc.lookup_extra_caps st s t sbw info ⦃ r => ∀ e, r = .Ok e → ExtraNamed th (L.mem s) e ⦄ := by
  have hroot : ∃ y, IsSlot th y ∧ capV (L.mem s) y = capOf (L.mem s) (slotAddr t.bv 0#64) :=
    ⟨slotAddr t.bv 0#64, ⟨t, 0, Or.inr ⟨ht, by decide⟩, rfl⟩, (capOf_eq (capAt_capV _ _)).symm⟩
  unfold ipc.lookup_extra_caps
  by_cases h0 : sbw = 0#u64
  · rw [if_pos h0, WP.spec_ok]
    rintro e h j hj hne
    cases h
    exact absurd (Ipc.exAt_none j hj) hne
  rw [if_neg h0]
  unfold ipc.lookup_extra_caps_loop
  refine loop.spec_decr_nat (fun x => 3 - x.2.val)
    (fun x => x.2.val ≤ 3 ∧ ExtraNamed th (L.mem s) x.1) _ _ _ (fun x hx => ?_) ?_
  · obtain ⟨arr, i⟩ := x
    obtain ⟨hi, hP⟩ := hx
    dsimp only at hi hP ⊢
    unfold ipc.lookup_extra_caps_loop.body
    by_cases hin : i < info.extra_caps
    · rw [if_pos hin]
      by_cases hi3 : i < 3#u64
      · have hi3' : i.val < 3 := by scalar_tac
        rw [if_pos hi3, Ipc.buf_caps_eq]
        simp only [lift, bind_ok]
        refine WP.spec_bind (msg.buf_get.spec s sbw _) ?_
        rintro w -
        refine WP.spec_bind (lookup_slot_refines th s σ hR hV t ht _) ?_
        rintro r ⟨e, -, hrel, hsok⟩
        cases r with
        | Ok r1 =>
          cases e with
          | error _ => exact hrel.elim
          | ok v =>
            obtain ⟨sl, rest⟩ := v
            obtain ⟨hsl, -⟩ := hrel
            obtain ⟨p, hp1, hp, hcr⟩ := hsok
            simp only []
            obtain ⟨a', ha', ha'v⟩ := spec_exists (Aeneas.Std.Array.update_spec arr (UScalar.cast .Usize i) r1.slot
              (by have hl : arr.val.length = 3 := by simpa using arr.property
                  rw [Ipc.cast_us_val i hi3']; simp [Aeneas.Std.Array.length, hl]; omega))
            rw [ha']
            simp only [bind_ok]
            obtain ⟨i4, h4e, h4v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
            rw [h4e, bind_ok, WP.spec_ok]
            have hi4 : i4.val = i.val + 1 := by simpa using h4v
            subst ha'v
            refine ⟨⟨show i4.val ≤ 3 by omega, fun j hj hne => ?_⟩, show 3 - i4.val < 3 - i.val by omega⟩
            try dsimp only at hne ⊢
            rw [Ipc.exAt_set, Ipc.cast_us_val i hi3'] at hne ⊢
            by_cases hji : i.val = j ∧ j < 3
            · rw [if_pos hji]
              exact ⟨p, sl.2, by rw [hsl, ← hp1], hp, cnRef_named hcr hroot⟩
            · rw [if_neg hji] at hne ⊢
              exact hP j hj hne
        | Err lf =>
          simp only [WP.spec_ok]
          intro e h; cases h
      · rw [if_neg hi3, WP.spec_ok]
        intro e h; cases h; exact hP
    · rw [if_neg hin, WP.spec_ok]
      intro e h; cases h; exact hP
  · exact ⟨by simp, fun j hj hne => absurd (Ipc.exAt_none j hj) hne⟩

end Named

section J
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

namespace JAtZ

/-- **A named extra slot is no IRQ node slot** (the IRQ handler's
SetNotification, XTopJointEntry's former `JIrqHPath.hex`): the slot's CNode
is named by a CNode cap of a slot, and no such cap names an IRQ node CNode
(`SpecGlob.ref`). -/
theorem irqExtraNe (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hsg : SpecGlob σ)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hN : ExtraNamed Z.th (L.mem s) extra) {irq : U64}
    (hirq : irq.val < 128) : Ipc.exAt extra 0 ≠ nodeA (L.ksb s) irq := by
  intro e
  have hP : Placed Z.th := J.xtop.rel.1
  have hAn : AbsSlot Z.th ((nodeA (L.ksb s) irq).bv, []) :=
    ⟨_, rfl, Or.inl (by simpa using J.intL.node irq hirq)⟩
  have hne : Ipc.exAt extra 0 ≠ 0#u64 := by
    have h := hAn.isSlot.ne_zero hP
    rw [cslotAddr_nil] at h
    rw [e]; exact h
  obtain ⟨ps, idx, hx, hps, y, r, gs, g, hy, hyc⟩ := hN 0 (by omega) hne
  have hAp : AbsSlot Z.th (ps.bv, idx) := ⟨ps, rfl, Or.inl hps⟩
  have hsl := cslotAddr_inj hP hAp hAn (by rw [← hx, e, cslotAddr_nil])
  have hpsb : ps.bv = (nodeA (L.ksb s) irq).bv := congrArg Prod.fst hsl
  obtain rfl : ps = nodeA (L.ksb s) irq := P1.eq_of_bv hpsb
  obtain ⟨sl0, hA0, rfl⟩ := hy.abs
  obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := J.dstate.1.1.abs_cap hA0
  rw [capAt_capV, hyc] at hc0; cases eq_of_ok_eq hc0
  rw [hca0.abs] at hg0
  have ha0 := (getCap_set_iff σ sl0.1 sl0.2 _).1 (congrArg Prod.fst hg0)
  apply hsg.ref sl0.1 sl0.2 _ ha0 (by simp [IsPageCap, absCap]) (BitVec.ofNat 8 irq.val)
  rw [J.xtop.fin.1.1.2.2.2.1.node irq hirq]
  simp [absCap, Fl4Spec.objRefs]

/-- **P1's kernel-write words of `JAtZ`'s sets miss the domain schedule**
(IrqDom's `KWApart`), at any state with the same kernel-state base whose
cores' nodes are placed (P1's `TimerOK.npl`). -/
theorem kwApartJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hk : L.ksb s' = L.ksb s)
    (hN : ∀ c ∈ Cs, P1.NodePlaced st (P1.Heap.tcbs H) s' c) :
    KWApart (L := L) (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s' := by
  have hf := J.kern.ksbFit
  have hal := J.kern.ksbAl
  have hks := J.kern.hks
  have hH := J.kern.heap
  intro b hb hkw
  unfold P1.Aligned at hb
  suffices h : b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ b.val by rw [hk]; exact h
  -- a word of an `H` object that is not an `other` one
  have hobj : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → p.val ≤ b.val → b.val < p.val + 2 ^ k.bits →
      b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ b.val := by
    intro p k hp hk' h1 h2
    have h3 := hks p k hp hk'
    generalize 2 ^ k.bits = N at h2 h3
    omega
  rcases hkw with ⟨y, hy, K, hK1, hK2, -, -, rfl⟩ | ⟨c, hc, o, ho, -, rfl⟩ | hsg | ⟨c, hc, hin⟩ |
      ⟨e, he, rfl | rfl⟩
  · -- a TCB word
    have hy' : H y = some .tcb := hy
    have hfit := hH.fits y _ hy'
    simp only [P1.HKind.bits] at hfit
    have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
    rw [h12] at hfit
    have hv : (core.num.U64.wrapping_add y K).val = y.val + K.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    refine hobj y .tcb hy' (fun z h => by cases h) (by rw [hv]; omega) ?_
    rw [hv]; simp only [P1.HKind.bits, h12]; omega
  · -- a node word
    have hv := P1.nodeAt_val (hN c hc) ho
    unfold P1.LawfulStore.nodeBase at hv
    rw [hk] at hv
    rw [hv]; omega
  · -- a reply's, SC's or notification's frame word
    obtain ⟨-, p, k, hp, hk', hin⟩ := hsg
    have hko : ∀ z, k ≠ .other z := by
      rcases hk' with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩ <;> exact fun z h => by cases h
    exact hobj p k hp hko hin.1 hin.2
  · -- an SC word
    obtain ⟨z, hz⟩ := hc
    have hzb : P1.Heap.scBits H c = z := by simp [P1.Heap.scBits, hz]
    rw [hzb] at hin
    exact hobj c (.sc z) hz (fun _ h => by cases h) hin.1 (by simpa [P1.HKind.bits] using hin.2)
  all_goals
    obtain ⟨k, hek, hk4, hko⟩ : ∃ k, H e = some k ∧ 4 ≤ k.bits ∧ ∀ z, k ≠ .other z := by
      rcases he with h | h
      · exact ⟨_, h, by simp [P1.HKind.bits], fun z h => by cases h⟩
      · exact ⟨_, h, by simp [P1.HKind.bits], fun z h => by cases h⟩
    have hfit := hH.fits e k hek
    have h16 : (16 : Nat) ≤ 2 ^ k.bits :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk4)
  · -- an endpoint's or notification's head word
    exact hobj e k hek hko (by rw [P1.epHeadA_val]) (by rw [P1.epHeadA_val]; omega)
  · -- its tail-state word
    have hv := P1.epTSA_val' (e := e) (by omega)
    rcases hks e k hek hko with h | h
    · left; rw [hv]
      generalize 2 ^ k.bits = N at h h16
      omega
    · right; rw [hv]; omega

/-- **IrqDom's `IrqDelP1` at `JAtZ`** (XTopJointEntry's former
`JIrqHPath.hP1`): after the caller's restart, P1's `BlkOK` at `JAtZ`'s sets
(`set_thread_state.restart_ok`: the current thread runnable, so neither
blocked nor waiting for a reply), the IRQ slot's notification in them
(`JPlaced.typed`; the restart keeps the slots), and `KWApart`. -/
theorem irqDelP1J (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {irq : U64} (hirq : irq.val < 128) :
    IrqDelP1 (L := L) s ct irq := by
  intro s2 hs2 p b w r hcap
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have hctT : ct ∈ Z.T := J.thT ct htcb
  obtain ⟨x', hk', hR⟩ := J.xtop.ipc.tcb ct hctT
  rw [hk] at hk'; cases hk'
  have hnbr : ¬ P1.BlockedR (L.mem s (P1.stA ct)) := fun hb => by
    have hq := Sched.blockedR_queued hR.st hb
    cases hx : x.tcbState <;> simp_all [Fl4Spec.runnable, Fl4Spec.ipcQueuedThreadState]
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hTe : Z.T = P1.Heap.tcbs H :=
    Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩
  have hctH : ct ∈ P1.Heap.tcbs H := hTe ▸ hctT
  obtain ⟨hb2, -, -, hks2, -⟩ := P1.sched.set_thread_state.restart_ok (Es := P1.EH H) J.blk hctH
    (fun h => hnbr (Or.inl h)) (fun h => hnbr (Or.inr h)) hs2
  -- the IRQ slot keeps its cap across the restart
  have hP : Placed Z.th := J.xtop.rel.1
  obtain ⟨s2', hs2', -, -, -, hSS, -⟩ :=
    restart_dk4 Z.th hP s σ Z.G J.dstate ct hcur htcb J.kern.act J.domPlaced
  obtain rfl : s2' = s2 := eq_of_ok_eq (hs2'.symm.trans hs2)
  have hAn : AbsSlot Z.th ((nodeA (L.ksb s) irq).bv, []) :=
    ⟨_, rfl, Or.inl (by simpa using J.intL.node irq hirq)⟩
  have hIs : IsSlot Z.th (nodeA (L.ksb s) irq) := by
    have h := hAn.isSlot; rwa [cslotAddr_nil] at h
  rw [hSS.capV hIs] at hcap
  obtain ⟨hpN, hpH⟩ := (hJ.typed _ hIs).2.1 p b w r hcap
  exact ⟨_, _, _, H, _, _, _, _, _, Ac, hb2, hpN, hpH, J.kwApartJ hks2 (fun c hc => hb2.2.2.1.2.2.tm.npl c hc)⟩

end JAtZ

end J

end

end Fl4Proofs.P3
