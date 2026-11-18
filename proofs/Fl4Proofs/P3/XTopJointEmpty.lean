/-
P3 (DESIGN.md §9), CSpace: **emptying a CNode slot keeps `JAtZ`, for any
cap** (`JAtZ.emptyJ`, generalising `JAtZ.emptyNtfnJ`, XTopJointDel), the
deletion's last slot edit at `J`.

* `OtherCov m G x lo hi`: the bytes `[lo, hi)` are covered by a cap of the
  MDB at a slot other than `x`.
* `EmptyReady`: the readiness of the slot being emptied, the fact the
  deletion knows after the cap's finalisation (a final cap's objects dead,
  P1's `fin_cap_*.dead`; a non-final cap's objects covered by another cap):
  each range inside the cap's is covered by another cap, or its object is
  dead (`DeadP`), as `JCovD.delete` reads it; and the current SC, when inside
  the cap's range, covered by another cap (`JKern.cscLive`).
* `JAtZ.emptyJ`: from `JAtZ` and `EmptyReady`, FL4's `empty_slot` with a
  null cleanup has a spec outcome with `XTopAt`, the kernel-state base and the
  kinds kept, and (given `DelUtFact` after, the known `valid_untyped` gap)
  `JCs` and `JRest`, the dead set grown by the objects losing their cover
  (`JCovD.delete`).
-/
import Fl4Proofs.P3.XTopJointDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- The bytes `[lo, hi)` are covered by a cap of the MDB at a slot other than `x`. -/
def OtherCov (m : U64 → U64) (G : MdbGhost) (x : U64) (lo hi : Nat) : Prop :=
  ∃ y ∈ G.chains.flatten, y ≠ x ∧ physF (capV m y) = true ∧ isUt (capV m y) = false ∧
    baseF (capV m y) ≤ lo ∧ hi ≤ topF (capV m y) + 1

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **The readiness of a slot to be emptied** (module docstring); asked of a
covering cap only (physical, not untyped: `Covered` reads no other). -/
def EmptyReady (H : P1.Heap) (G : MdbGhost) (s : S) (x : U64) : Prop :=
  physF (capV (L.mem s) x) = true → isUt (capV (L.mem s) x) = false →
  (∀ lo hi, lo < hi → baseF (capV (L.mem s) x) ≤ lo → hi ≤ topF (capV (L.mem s) x) + 1 →
    OtherCov (L.mem s) G x lo hi ∨ ∀ q : U64, q.val = lo → DeadP (L := L) H s q) ∧
  ∀ z, H (L.cscW s) = some (.sc z) → baseF (capV (L.mem s) x) ≤ (L.cscW s).val →
    (L.cscW s).val + 2 ^ (P1.HKind.sc z).bits ≤ topF (capV (L.mem s) x) + 1 →
    OtherCov (L.mem s) G x (L.cscW s).val ((L.cscW s).val + 2 ^ (P1.HKind.sc z).bits)

/-- **`JCovD.delete` with the removed cap's readiness asked only of a
covering cap.** -/
theorem Sched.JCovD.deleteG {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {D Cs : Set U64} {s : S}
    (h : Sched.JCovD (L := L) th H G D Cs s) {s' : S} {G' : MdbGhost} {x : U64}
    (hk : ∀ y ∈ G.chains.flatten, y ≠ x → physF (capV (L.mem s) y) = true → isUt (capV (L.mem s) y) = false →
      y ∈ G'.chains.flatten ∧ capV (L.mem s') y = capV (L.mem s) y)
    (hx : physF (capV (L.mem s) x) = true → isUt (capV (L.mem s) x) = false →
      ∀ lo hi, lo < hi → baseF (capV (L.mem s) x) ≤ lo → hi ≤ topF (capV (L.mem s) x) + 1 →
      Covered (L.mem s') G' lo hi ∨ (∀ q : U64, q.val = lo → DeadP (L := L) H s' q))
    (hdead : ∀ q ∈ D, DeadP (L := L) H s q → DeadP (L := L) H s' q)
    (hks : ∀ x ∈ G'.chains.flatten, ∀ p sb fi d, capV (L.mem s') x = .Untyped p sb fi d →
      (p.val + 2 ^ sb.val ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ p.val) ∧
      ∀ c ∈ Cs, p.val + 2 ^ sb.val ≤ L.nodeBase s' c ∨ L.nodeBase s' c + 4288 ≤ p.val) :
    Sched.JCovD (L := L) th H G' (D ∪ Uncov th H (L.mem s') G') Cs s' := by
  have cov : ∀ {lo hi : Nat}, lo < hi → Covered (L.mem s) G lo hi →
      Covered (L.mem s') G' lo hi ∨ (∀ q : U64, q.val = lo → DeadP (L := L) H s' q) := by
    intro lo hi hlh hc
    obtain ⟨y, hy, hp, hu, hb, ht⟩ := hc
    by_cases hyx : y = x
    · subst hyx; exact hx hp hu lo hi hlh hb ht
    · obtain ⟨hy', e⟩ := hk y hy hyx hp hu
      exact Or.inl ⟨y, hy', by rw [e]; exact hp, by rw [e]; exact hu, by rw [e]; exact hb, by rw [e]; exact ht⟩
  refine h.step (fun q hq => ?_) hdead hks
  rcases hq with ⟨k, hq, hnc⟩ | ⟨k, hq, hnc⟩
  · rcases h.th q k hq with hc | hd
    · rcases cov (by omega) hc with hc' | hd'
      · exact absurd hc' hnc
      · exact hd' q rfl
    · exact hdead q hd (h.dead q hd)
  · rcases h.h q k hq with hc | hd
    · rcases cov (by have := Nat.one_le_two_pow (n := k.bits); omega) hc with hc' | hd'
      · exact absurd hc' hnc
      · exact hd' q rfl
    · exact hdead q hd (h.dead q hd)

set_option maxHeartbeats 16000000 in
/-- **Emptying a ready CNode slot keeps `JAtZ`, relationally**: from the
facts of an `empty_slot` step (the spec's outcome, `DState` after, the slot
null and the others kept, `XTopAt` after, the slot words' frame, `CnK`),
the kernel-state base, `KBack`, and (given `DelUtFact`) `JCs` and `JRest`
after with the dead set grown. -/
theorem JAtZ.emptyJCore {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr}
    (hrd : EmptyReady (L := L) H Z.G s (cslotAddr sl))
    {s2 : S} {σ2 : Fl4Spec.State Unit} {G2 : MdbGhost} {V2 : XVs}
    (hDS2 : DState (L := L) Z.th s2 σ2 G2)
    (hnull2 : capV (L.mem s2) (cslotAddr sl) = .Null)
    (hoth2 : ∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem s2) y = capV (L.mem s) y)
    (hX2 : XTopAt (L := L) AR (Z.mv G2 V2) s2 a σ2)
    (hwS : P1.WritesIn st s s2 (Sched.SlotWd Z.th)) (hcn2 : Ipc.CnK σ σ2) (hkc : KeepCT σ σ2) (hkz : KSz σ σ2)
    (hcdt : σ2.cdt = Function.update (fun x => if σ.cdt x = some sl then σ.cdt sl else σ.cdt x) sl none)
    (horig : ∀ sl', σ2.isOriginalCap sl' = true → σ.isOriginalCap sl' = true)
    (hgp : σ2.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4) :
    L.ksb s2 = L.ksb s ∧ KBack σ σ2 ∧
      ((∀ u up usb ufi udev, AbsSlot Z.th u → capAt (L.mem s) (cslotAddr u) = ok (.Untyped up usb ufi udev) →
        σ.cdt sl = some u → (∀ x, σ.cdt x = some u → x = sl) → (∀ x, σ.cdt x ≠ some sl) →
        DelUtFact (L := L) Z.th s2 σ2 up usb ufi) →
       JCs (L := L) (Z.mv G2 V2) s2 σ2 ∧
        ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JRest (L := L) arI (Z.mv G2 V2) H Cs Ac' Lst' D' s2 σ2) := by
  have hP := J.xtop.rel.1
  have hw : P1.WritesIn st s s2 (InSlot Z.th) := hwS.mono fun b hb => slotWd_range hP hb
  obtain ⟨⟨hR2, hV2, hM2, hC2, hI2⟩, hDl2, hFI2⟩ := hDS2
  have hMO := hX2.rel.2.2.2.2.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hTK : TypedKept Z.th (L.mem s) (L.mem s2) := fun x hx => by
    by_cases e : x = cslotAddr sl
    · left; rw [e, hnull2]; rfl
    · right; exact ⟨x, hx, by rw [hoth2 x hx e]⟩
  have hT3 : ∀ t, Z.th t = some .tcb → capAt (L.mem s2) (slotOf t 3) = capAt (L.mem s) (slotOf t 3) ∨
      capV (L.mem s2) (slotOf t 3) = .Null := by
    intro t ht
    have h1 : IsSlot Z.th (slotOf t 3) := ⟨t, 3, Or.inr ⟨ht, by decide⟩, rfl⟩
    by_cases hne : slotOf t 3 = cslotAddr sl
    · right; rw [hne]; exact hnull2
    · left; rw [capAt_capV, capAt_capV, hoth2 _ h1 hne]
  have hUK : UtKept Z.th (L.mem s) (L.mem s2) := fun x hx p' sb fi d h => by
    have e : x ≠ cslotAddr sl := fun e => by rw [e, hnull2] at h; cases h
    exact ⟨x, hx, fi, d, by rw [← hoth2 x hx e]; exact h, Or.inl le_rfl⟩
  -- the cover after
  have hmemA : ∀ y, IsSlot Z.th y → capV (L.mem s2) y ≠ .Null → y ∈ G2.chains.flatten := fun y hy hn =>
    (hM2.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩
  have hk : ∀ y ∈ Z.G.chains.flatten, y ≠ cslotAddr sl → physF (capV (L.mem s) y) = true →
      isUt (capV (L.mem s) y) = false → y ∈ G2.chains.flatten ∧ capV (L.mem s2) y = capV (L.mem s) y := by
    intro y hy hyx hp _
    obtain ⟨hys, -⟩ := (J.xtop.rel.2.1.2.2.1.members y).1 hy
    have e := hoth2 y hys hyx
    refine ⟨hmemA y hys (by rw [e]; intro h; rw [h, physF_null] at hp; cases hp), e⟩
  have ocov : ∀ lo hi, OtherCov (L.mem s) Z.G (cslotAddr sl) lo hi → Covered (L.mem s2) G2 lo hi := by
    rintro lo hi ⟨y, hy, hyx, hp, hu, hb, ht⟩
    obtain ⟨hy', e⟩ := hk y hy hyx hp hu
    exact ⟨y, hy', by rw [e]; exact hp, by rw [e]; exact hu, by rw [e]; exact hb, by rw [e]; exact ht⟩
  have hx : physF (capV (L.mem s) (cslotAddr sl)) = true →
      isUt (capV (L.mem s) (cslotAddr sl)) = false →
      ∀ lo hi, lo < hi → baseF (capV (L.mem s) (cslotAddr sl)) ≤ lo →
      hi ≤ topF (capV (L.mem s) (cslotAddr sl)) + 1 →
      Covered (L.mem s2) G2 lo hi ∨ (∀ q' : U64, q'.val = lo → DeadP (L := L) H s2 q') := by
    intro hp hu lo hi hlh h1 h2
    rcases (hrd hp hu).1 lo hi hlh h1 h2 with h | h
    · exact Or.inl (ocov _ _ h)
    · exact Or.inr fun q' hq' => J.deadP_slot hX2 hcn2 hkc hw (h q' hq')
  have hks2 : ∀ x ∈ G2.chains.flatten, ∀ p' sb fi d, capV (L.mem s2) x = .Untyped p' sb fi d →
      (p'.val + 2 ^ sb.val ≤ (L.ksb s2).val ∨ (L.ksb s2).val + 13568 ≤ p'.val) ∧
      ∀ c ∈ Cs, p'.val + 2 ^ sb.val ≤ L.nodeBase s2 c ∨ L.nodeBase s2 c + 4288 ≤ p'.val := by
    intro x hx p' sb fi d hcx
    obtain ⟨hxs, c1, hc1, hn1⟩ := (hM2.members x).1 hx
    have e : x ≠ cslotAddr sl := fun e => by rw [e, hnull2] at hcx; cases hcx
    have hcx0 : capV (L.mem s) x = .Untyped p' sb fi d := by rw [← hoth2 x hxs e]; exact hcx
    have hxm : x ∈ Z.G.chains.flatten :=
      (J.xtop.rel.2.1.2.2.1.members x).2 ⟨hxs, _, capAt_capV _ _, by rw [hcx0]; nofun⟩
    obtain ⟨k1, k2⟩ := J.jcov.ks x hxm p' sb fi d hcx0
    have hks : L.ksb s2 = L.ksb s := hw.1
    have hnb : ∀ c, L.nodeBase s2 c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
    exact ⟨by rw [hks]; exact k1, fun c hc => by rw [hnb]; exact k2 c hc⟩
  have hjc := J.jcov.deleteG hk hx (fun q' _ hd => J.deadP_slot hX2 hcn2 hkc hw hd) hks2
  have hcl : L.cscW s ∉ D ∪ Uncov Z.th H (L.mem s2) G2 := by
    obtain ⟨z, hz⟩ := J.csc_sc
    rintro (h | h)
    · exact J.kern.cscLive h
    · rcases h with ⟨k, hk', hnc⟩ | ⟨k, hk', hnc⟩
      · rcases J.thk _ k hk' with rfl | ⟨r', rfl⟩
        · rw [(hJ.tcb _).1 hk'] at hz; cases hz
        · rw [hJ.cnode _ r' hk'] at hz; cases hz
      · rw [hz] at hk'; cases hk'
        rcases J.jcov.h _ _ hz with hcv | hD'
        · obtain ⟨y, hy, hp, hu, hb, ht⟩ := hcv
          by_cases hyx : y = cslotAddr sl
          · subst hyx
            exact hnc (ocov _ _ ((hrd hp hu).2 z hz hb ht))
          · obtain ⟨hy', e⟩ := hk y hy hyx hp hu
            exact hnc ⟨y, hy', by rw [e]; exact hp, by rw [e]; exact hu, by rw [e]; exact hb, by rw [e]; exact ht⟩
        · exact J.kern.cscLive hD'
  refine ⟨hw.1, KBack.of_keepCT hkc, fun hUt => ?_⟩
  have hutc := J.del_utc (G' := G2) (sl := sl) (fun y hy e => hoth2 y hy e) hnull2 hw hcdt horig hgp hM2 hUt
  obtain ⟨hJC, R⟩ := jowes_slotD J hX2 hcn2 hkc hw hFI2 hMO hkz hTK hT3 hDl2 hUK hjc hcl
    (fun sl' h => Or.inl (horig sl' h)) hutc
  exact ⟨hJC, Ac, Lst, _, R⟩
set_option maxHeartbeats 16000000 in
/-- **Emptying a CNode slot, the parts** (`emptyJCore`). -/
theorem JAtZ.emptyJR {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl)
    (hcnode : ∃ q, sl.1 = q.bv ∧ Z.th q = some (.cnode sl.2.length))
    (hcn : capV (L.mem s) (cslotAddr sl) ≠ .Null)
    (hrd : EmptyReady (L := L) H Z.G s (cslotAddr sl))
    {s2 : S} {σ2 : Fl4Spec.State Unit} {G2 : MdbGhost} {V2 : XVs}
    (hes : ((), σ2) ∈ (Fl4Spec.emptySlot (Z := Unit) sl .nullCap σ).1)
    (hDS2 : DState (L := L) Z.th s2 σ2 G2)
    (hnull2 : capV (L.mem s2) (cslotAddr sl) = .Null)
    (hoth2 : ∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem s2) y = capV (L.mem s) y)
    (hX2 : XTopAt (L := L) AR (Z.mv G2 V2) s2 a σ2)
    (hwS : P1.WritesIn st s s2 (Sched.SlotWd Z.th)) (hcn2 : Ipc.CnK σ σ2) :
    L.ksb s2 = L.ksb s ∧ KBack σ σ2 ∧
      ((∀ u up usb ufi udev, AbsSlot Z.th u → capAt (L.mem s) (cslotAddr u) = ok (.Untyped up usb ufi udev) →
        σ.cdt sl = some u → (∀ x, σ.cdt x = some u → x = sl) → (∀ x, σ.cdt x ≠ some sl) →
        DelUtFact (L := L) Z.th s2 σ2 up usb ufi) →
       JCs (L := L) (Z.mv G2 V2) s2 σ2 ∧
        ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JRest (L := L) arI (Z.mv G2 V2) H Cs Ac' Lst' D' s2 σ2) := by
  have hP := J.xtop.rel.1
  have hR := J.xtop.rel.2.1.1
  have hc : capAt (L.mem s) (cslotAddr sl) = ok (capV (L.mem s) (cslotAddr sl)) := capAt_capV _ _
  generalize capV (L.mem s) (cslotAddr sl) = c at hc hcn
  have hw : P1.WritesIn st s s2 (InSlot Z.th) := hwS.mono fun b hb => slotWd_range hP hb
  obtain ⟨q, hq1, hq2⟩ := hcnode
  obtain ⟨cs, hkq, hwf, -⟩ := hR.cnode q _ hq2
  obtain ⟨o, idx⟩ := sl
  simp only at hq1 hq2 hkq
  subst hq1
  change ((), σ2) ∈ (Fl4Spec.emptySlot (Z := Unit) (q.bv, idx) .nullCap σ).1 at hes
  have hkc : KeepC σ σ2 := keepC_of hcn2 (emptySlot_null_nko _ σ ((), σ2) hes)
    (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact ⟨_, cs, hkq⟩)
  have hkz : KSz σ σ2 := emptySlot_null_nkz _ σ ((), σ2) hes
  obtain ⟨c0, ac, hc0, hca, hg⟩ := hR.abs_cap hA
  rw [hc] at hc0
  obtain rfl : c = c0 := eq_of_ok_eq hc0
  rw [hca.abs] at hg
  have h3 : Fl4Spec.setCap (Z := Unit) .nullCap (q.bv, idx) (emptySlotCdtState σ (q.bv, idx)) =
      ({((), setCnodeSlot (emptySlotCdtState σ (q.bv, idx)) q.bv idx.length cs idx .nullCap)}, False) :=
    setCap_cnode (σ := emptySlotCdtState σ (q.bv, idx)) .nullCap hkq hwf rfl
  have he := emptySlot_eq hg (fun h => hcn (absCap_eq_null.1 h)) h3
  rw [he] at hes
  have e2 := mem_singleton_snd hes
  simp only at e2
  subst e2
  have hgp : (setCnodeSlot (emptySlotCdtState σ (q.bv, idx)) q.bv idx.length cs idx .nullCap).archState.x64GlobalPml4 =
      σ.archState.x64GlobalPml4 := rfl
  have horig : ∀ sl', (setCnodeSlot (emptySlotCdtState σ (q.bv, idx)) q.bv idx.length cs idx .nullCap).isOriginalCap sl' = true →
      σ.isOriginalCap sl' = true := fun sl' h => by
    by_cases e : sl' = (q.bv, idx)
    · subst e; simp [setCnodeSlot, emptySlotCdtState] at h
    · simpa [setCnodeSlot, emptySlotCdtState, Function.update_of_ne e] using h
  exact J.emptyJCore hrd hDS2 hnull2 hoth2 hX2 hwS hcn2 (KeepC.t hkc) hkz rfl horig hgp

set_option maxHeartbeats 16000000 in
/-- **Emptying a TCB slot, the parts** (`emptyJCore`): the spec's
`empty_slot` sets the TCB's cap (`setCap_tcb`), a step changing the TCB's
caps only (`KeepCT`). -/
theorem JAtZ.emptyJRT {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl)
    (hntc : ¬ ∃ q, sl.1 = q.bv ∧ Z.th q = some (.cnode sl.2.length))
    (hcn : capV (L.mem s) (cslotAddr sl) ≠ .Null)
    (hrd : EmptyReady (L := L) H Z.G s (cslotAddr sl))
    {s2 : S} {σ2 : Fl4Spec.State Unit} {G2 : MdbGhost} {V2 : XVs}
    (hes : ((), σ2) ∈ (Fl4Spec.emptySlot (Z := Unit) sl .nullCap σ).1)
    (hDS2 : DState (L := L) Z.th s2 σ2 G2)
    (hnull2 : capV (L.mem s2) (cslotAddr sl) = .Null)
    (hoth2 : ∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem s2) y = capV (L.mem s) y)
    (hX2 : XTopAt (L := L) AR (Z.mv G2 V2) s2 a σ2)
    (hwS : P1.WritesIn st s s2 (Sched.SlotWd Z.th)) (hcn2 : Ipc.CnK σ σ2) :
    L.ksb s2 = L.ksb s ∧ KBack σ σ2 ∧
      ((∀ u up usb ufi udev, AbsSlot Z.th u → capAt (L.mem s) (cslotAddr u) = ok (.Untyped up usb ufi udev) →
        σ.cdt sl = some u → (∀ x, σ.cdt x = some u → x = sl) → (∀ x, σ.cdt x ≠ some sl) →
        DelUtFact (L := L) Z.th s2 σ2 up usb ufi) →
       JCs (L := L) (Z.mv G2 V2) s2 σ2 ∧
        ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JRest (L := L) arI (Z.mv G2 V2) H Cs Ac' Lst' D' s2 σ2) := by
  have hR := J.xtop.rel.2.1.1
  have hkz : KSz σ σ2 := emptySlot_null_nkz _ σ ((), σ2) hes
  obtain ⟨p, hp1, hp⟩ := hA
  rcases hp with hp | ⟨ht, i, hi, hidx⟩
  · exact absurd ⟨p, hp1, hp⟩ hntc
  obtain ⟨tcb, hk, -⟩ := hR.tcb p ht
  obtain ⟨o, idx⟩ := sl
  simp only at hp1 hidx
  subst hp1 hidx
  obtain ⟨c0, ac, hc0, hca, hg⟩ := hR.abs_cap (sl := (p.bv, Fl4Spec.tcbCnodeIndex i)) ⟨p, rfl, Or.inr ⟨ht, i, hi, rfl⟩⟩
  rw [hca.abs] at hg
  have hcn0 : c0 ≠ .Null := fun h => hcn (by rw [capV_of_capAt hc0, h])
  have h3 : Fl4Spec.setCap (Z := Unit) .nullCap (p.bv, Fl4Spec.tcbCnodeIndex i)
      (emptySlotCdtState σ (p.bv, Fl4Spec.tcbCnodeIndex i)) =
      ({((), setTcbSlot (emptySlotCdtState σ (p.bv, Fl4Spec.tcbCnodeIndex i)) p.bv tcb i .nullCap)}, False) :=
    setCap_tcb (σ := emptySlotCdtState σ (p.bv, Fl4Spec.tcbCnodeIndex i)) .nullCap hk hi
  have he := emptySlot_eq hg (fun h => hcn0 (absCap_eq_null.1 h)) h3
  rw [he] at hes
  have e2 := mem_singleton_snd hes
  simp only at e2
  subst e2
  have horig : ∀ sl', (setTcbSlot (emptySlotCdtState σ (p.bv, Fl4Spec.tcbCnodeIndex i)) p.bv tcb i
      .nullCap).isOriginalCap sl' = true → σ.isOriginalCap sl' = true := fun sl' h => by
    by_cases e : sl' = (p.bv, Fl4Spec.tcbCnodeIndex i)
    · subst e; simp [setTcbSlot, emptySlotCdtState] at h
    · simpa [setTcbSlot, emptySlotCdtState, Function.update_of_ne e] using h
  exact J.emptyJCore hrd hDS2 hnull2 hoth2 hX2 hwS hcn2 (KeepCT.of_cnK hcn2) hkz rfl horig rfl

set_option maxHeartbeats 16000000 in
/-- **Emptying a CNode slot keeps `JAtZ`** (module docstring). -/
theorem JAtZ.emptyJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl)
    (hcnode : ∃ q, sl.1 = q.bv ∧ Z.th q = some (.cnode sl.2.length))
    {c : capability.Cap} (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hcn : c ≠ .Null)
    (hrd : EmptyReady (L := L) H Z.G s (cslotAddr sl)) :
    cdt.empty_slot st arI s a (cslotAddr sl) .Null ⦃ res => res.2 = a ∧ ∃ σ' G' V',
      ((), σ') ∈ (Fl4Spec.emptySlot (Z := Unit) sl .nullCap σ).1 ∧ XTopAt (L := L) AR (Z.mv G' V') res.1 res.2 σ' ∧
      L.ksb res.1 = L.ksb s ∧ KBack σ σ' ∧
      ((∀ u up usb ufi udev, AbsSlot Z.th u → capAt (L.mem s) (cslotAddr u) = ok (.Untyped up usb ufi udev) →
        σ.cdt sl = some u → (∀ x, σ.cdt x = some u → x = sl) → (∀ x, σ.cdt x ≠ some sl) →
        DelUtFact (L := L) Z.th res.1 σ' up usb ufi) →
       JCs (L := L) (Z.mv G' V') res.1 σ' ∧
        ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JRest (L := L) arI (Z.mv G' V') H Cs Ac' Lst' D' res.1 σ') ⦄ := by
  have hP := J.xtop.rel.1
  have hR := J.xtop.rel.2.1.1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩
  let W : S → A → Fl4Spec.State Unit → MdbGhost → Prop := fun s2 a2 σ2 G2 =>
    WXZ (L := L) AR Z (L.ksb s) s2 a2 σ2 G2 ∧ P1.WritesIn st s s2 (Sched.SlotWd Z.th) ∧ Ipc.CnK σ σ2 ∧ a2 = a
  have hSl : SlotHypW (L := L) (A := A) W Z.th := fun s1 s2 a1 σ1 σ2 G1 G2 hW hD1 hD2 hF hcn hSt =>
    ⟨slotHypW_XZ AR Z (L.ksb s) s1 s2 a1 σ1 σ2 G1 G2 hW.1 hD1 hD2 hF hcn hSt, hW.2.1.trans1 (SlotFrame2.writesIn hF),
      hW.2.2.1.trans hcn, hW.2.2.2⟩
  have hW0 : W s a σ Z.G := ⟨⟨⟨Z.vs, J.xtop⟩, J.ks, J.thT, rfl⟩, P1.WritesIn.refl _ _, Ipc.CnK.refl σ, rfl⟩
  refine WP.spec_mono (empty_stepW' arI W Z.th hP (cl := .Null) (fun h => absurd rfl h) hSl s a σ Z.G hDS hW0 hA
    trivial trivial) ?_
  rintro ⟨s2, a2⟩ ⟨σ2, G2, hes, hDS2, hnull2, hoth2, -, -, -, -, ⟨⟨V2, hX2⟩, -, -, -⟩, hwS, hcn2, ha2⟩
  simp only at hes hDS2 hnull2 hoth2 hX2 hwS hcn2 ha2 ⊢
  subst ha2
  obtain ⟨hks, hkb, hR2⟩ := J.emptyJR hA hcnode (by rw [capV_of_capAt hc]; exact hcn)
    hrd hes hDS2 hnull2 hoth2 hX2 hwS hcn2
  exact ⟨rfl, σ2, G2, V2, hes, hX2, hks, hkb, hR2⟩

/-- A word off `H`'s objects is dead (`DeadP` reads `H` only). -/
theorem deadP_none {H : P1.Heap} {s : S} {q : U64} (h : H q = none) : DeadP (L := L) H s q :=
  ⟨fun e => (by rw [h] at e; cases e), fun e => (by rw [h] at e; cases e), fun e => (by rw [h] at e; cases e),
    fun e => (by rw [h] at e; cases e), fun z e => (by rw [h] at e; cases e)⟩

/-- **A notification cap's slot is ready to be emptied** when the
notification is dead (after a final cap's finalisation, P1's
`fin_cap_ntfn.dead`) or another cap to it is in the MDB (a non-final cap,
`other_ntfn`): no other object of `H` meets the notification's 64 bytes. -/
theorem JAtZ.ntfn_ready {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : IsSlot Z.th x) {p b : U64} {w r : Bool}
    (hcv : capV (L.mem s) x = .Notification p b w r)
    (hpd : DeadP (L := L) H s p ∨
      ∃ y ∈ Z.G.chains.flatten, y ≠ x ∧ ∃ b' w' r', capV (L.mem s) y = .Notification p b' w' r') :
    EmptyReady (L := L) H Z.G s x := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .ntfn := ((hJ.typed _ hx).2.1 p b w r hcv).2
  have hpfit : p.val + 2 ^ 6 ≤ 2 ^ 64 := J.kern.heap.fits p _ hHp
  obtain ⟨e1, e2⟩ := range_ntfn p b w r hpfit
  unfold EmptyReady
  rw [hcv, e1, e2]
  intro _ _
  -- the other cap's cover of the whole range
  have hoc : (∃ y ∈ Z.G.chains.flatten, y ≠ x ∧ ∃ b' w' r', capV (L.mem s) y = .Notification p b' w' r') →
      ∀ lo hi, p.val ≤ lo → hi ≤ p.val + 2 ^ 6 - 1 + 1 → OtherCov (L.mem s) Z.G x lo hi := by
    rintro ⟨y, hy, hne, b', w', r', hy'⟩ lo hi h1 h2
    obtain ⟨f1, f2⟩ := range_ntfn p b' w' r' hpfit
    exact ⟨y, hy, hne, by rw [hy']; exact ok_inj (phys_eq _).symm, by rw [hy']; rfl, by rw [hy', f1]; exact h1,
      by rw [hy', f2]; exact h2⟩
  -- an object of `H` other than the notification misses its range
  have hout : ∀ q k, H q = some k → q ≠ p → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 2 ^ 6 ≤ q.val := by
    intro q k hq hne
    have := J.kern.heap.disj q k p .ntfn hq hHp hne
    simpa only [show (P1.HKind.ntfn).bits = 6 from rfl] using this
  refine ⟨fun lo hi hlh h1 h2 => ?_, fun z hz h1 h2 => ?_⟩
  · rcases hpd with hd | ho
    · right
      intro q hq
      by_cases e : q = p
      · subst e; exact hd
      · cases hk : H q with
        | none => exact deadP_none hk
        | some k =>
          exfalso
          have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
          rcases hout q k hk e with h | h <;> omega
    · exact Or.inl (hoc ho lo hi h1 h2)
  · rcases hpd with hd | ho
    · exfalso
      have hne : L.cscW s ≠ p := fun e => by rw [e, hHp] at hz; cases hz
      have : 1 ≤ 2 ^ (P1.HKind.sc z).bits := Nat.one_le_two_pow
      rcases hout _ _ hz hne with h | h <;> omega
    · exact hoc ho _ _ h1 h2

end

end

end Fl4Proofs.P3
