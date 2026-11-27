/-
P3 (DESIGN.md §9), CSpace: **emptying a ready slot keeps `WJL`**
(`EmptyHypWR` at `WJL`, XTopJointWJL), the readiness `RdLO`: XTopJointDelR's
`RdL`, `LiveOther` and `TcbReady` (no live TCB in the cap's range; with the
TCB zombies' TCBs dead, `EmptyReadyX`).

* `WJR` as `emptyHypJ` (XTopJointDelR), at a dead set holding the TCB
  zombies' TCBs (`JAtZ.addDeadSet`, `emptyJRD`/`emptyJRTD` growing it),
  `PPR0` by `PPK.of_cnK`.
* `LiveJ`: the emptied slot `x` is null and not original after (the spec's
  `empty_slot` clears its bit, the other bits kept, `emptySlot_cdt_orig`),
  so a slot in use after is one in use before other than `x`; `LiveOther`
  names it (and every debug-listed thread) by a cap at a slot other than
  `x`, kept and so in the ghost tree after. A zombie after is one before
  (not at `x`), its slots from its count on unused as before; TCB zombies'
  TCBs dead by the dead set.
* `DbgWF` (`slotFrame_dbgKeep`), `NullOrig` (`NullOrig.empty`).
-/
import Fl4Proofs.P3.XTopJointWJL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **No live TCB in the emptied cap's range** (KENTRY-PLAN jc6e, for
`EmptyReadyX`): each range inside the (covering) cap's is covered by another
cap, or each TCB at its base is a TCB zombie's (in `ZTcb`, so in the dead set
`WJL` grows by `JAtZ.addDeadSet`). FL4: the loop empties a slot only when the
finalisation's remainder is removable (`RmOK`): a non-final cap (another cap
alike it), a cap finalised without effect, a removable zombie, or a final
non-thread object cap (no TCB in its range); a final thread cap's remainder is
a zombie still naming slots. -/
def TcbReady (th : TypedHeap) (H : P1.Heap) (G : MdbGhost) (s : S) (x : U64) : Prop :=
  physF (capV (L.mem s) x) = true → isUt (capV (L.mem s) x) = false →
  ∀ lo hi, lo < hi → baseF (capV (L.mem s) x) ≤ lo → hi ≤ topF (capV (L.mem s) x) + 1 →
    OtherCov (L.mem s) G x lo hi ∨ ∀ q : U64, q.val = lo → H q = some .tcb → q ∈ ZTcb (L := L) th s

/-- `TcbReady` of a cap whose range meets no TCB of `H`. -/
theorem TcbReady.of_apart {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {s : S} {x : U64}
    (hT : ∀ q, H q = some .tcb →
      q.val + 2 ^ (P1.HKind.tcb).bits ≤ baseF (capV (L.mem s) x) ∨ topF (capV (L.mem s) x) < q.val) :
    TcbReady (L := L) th H G s x := by
  intro _ _ lo hi hlh h1 h2
  refine Or.inr fun q hq hHq => ?_
  exfalso
  have : 1 ≤ 2 ^ (P1.HKind.tcb).bits := Nat.one_le_two_pow
  rcases hT q hHq with h | h <;> omega

/-- `TcbReady` of a cap whose range meets no object of `H` but `other` ones
(as `EmptyReady.of_apartO`). -/
theorem TcbReady.of_apartO {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {s : S} {x : U64}
    (hap : ∀ q k, H q = some k → (∀ z, k ≠ .other z) →
      q.val + 2 ^ k.bits ≤ baseF (capV (L.mem s) x) ∨ topF (capV (L.mem s) x) < q.val) :
    TcbReady (L := L) th H G s x :=
  TcbReady.of_apart fun q hq => hap q _ hq (fun z e => by cases e)

/-- `TcbReady` of a cap whose range is one object `p` of `H`, not a TCB. -/
theorem TcbReady.of_obj {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {s : S} {x : U64} {p : U64} {sz : Nat}
    (hp : H p ≠ some .tcb)
    (hdisj : ∀ q, H q = some .tcb → q ≠ p → q.val + 2 ^ (P1.HKind.tcb).bits ≤ p.val ∨ p.val + sz ≤ q.val)
    (hsz : 1 ≤ sz) (e1 : baseF (capV (L.mem s) x) = p.val) (e2 : topF (capV (L.mem s) x) = p.val + sz - 1) :
    TcbReady (L := L) th H G s x := by
  refine TcbReady.of_apart fun q hq => ?_
  have hne : q ≠ p := fun e => hp (by rw [← e]; exact hq)
  rw [e1, e2]
  rcases hdisj q hq hne with h | h
  · exact Or.inl h
  · right; omega

/-- `TcbReady` of a non-physical cap. -/
theorem TcbReady.of_nonphys {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {s : S} {x : U64}
    (hp : physF (capV (L.mem s) x) = false) : TcbReady (L := L) th H G s x := by
  intro h
  rw [hp] at h
  cases h

/-- `TcbReady` when another MDB cap covers the cap's range (as
`EmptyReady.of_cover`). -/
theorem TcbReady.of_cover {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {s : S} {x y : U64}
    (hy : y ∈ G.chains.flatten)
    (hne : y ≠ x) (hp : physF (capV (L.mem s) x) = true → physF (capV (L.mem s) y) = true)
    (hu : isUt (capV (L.mem s) y) = false) (hb : baseF (capV (L.mem s) y) ≤ baseF (capV (L.mem s) x))
    (ht : topF (capV (L.mem s) x) ≤ topF (capV (L.mem s) y)) : TcbReady (L := L) th H G s x := by
  intro hpx _
  exact fun lo hi _ h1 h2 => Or.inl ⟨y, hy, hne, hp hpx, hu, le_trans hb h1, by omega⟩

/-- **The deletion loop's readiness at `WJL`**: `RdL`, `LiveOther` and
`TcbReady`. -/
abbrev RdLO (th : TypedHeap) (H : P1.Heap) : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop :=
  fun s a σ G x => RdL (L := L) (A := A) th H s a σ G x ∧ LiveOther (L := L) th s σ G x ∧
    TcbReady (L := L) th H G s x

/-- (f4g) **The loop's readiness with the VSpace naming part**: `RdLO` and, when no slot is
exempt at the loop's base sets (`vx = ∅`), `VsPend` at the slot (KENTRY-PLAN f4 (13)). -/
abbrev RdLX (th : TypedHeap) (H : P1.Heap) (vx : Set U64) : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop :=
  fun s a σ G x => RdLO (L := L) (A := A) th H s a σ G x ∧ (vx = ∅ → Vs.VsPend th (L.mem s) (L.ksb s) x)

/-- (f4g) **The deletion loop's window invariant** (DelW's `Wx` at `WJL`): `WJL` at the base sets
with some exempt set (KENTRY-PLAN f4 (13): after a final ASID pool cap's finalisation the ASID
table no longer names its pool until its `empty_slot`). -/
abbrev WJLx (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  ∃ E : Set U64, WJL (L := L) arI AR { Z with vx := E } H Cs kb s a σ G

variable {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

theorem WJL.x {Z : XSets} {H : P1.Heap} {Cs : Set U64} {kb : U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {G : MdbGhost} (h : WJL (L := L) arI AR Z H Cs kb s a σ G) : WJLx (L := L) arI AR Z H Cs kb s a σ G :=
  ⟨Z.vx, h⟩

set_option maxHeartbeats 4000000 in
/-- **Emptying a ready slot keeps `WJL`** (module docstring). -/
theorem emptyHypJL [Fl4Proofs.P1.PlainStore st] (Z : XSets)
    (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    EmptyHypWR (L := L) (WJL (L := L) arI AR Z H Cs kb) (WJLx (L := L) arI AR Z H Cs kb)
      (RdLX (L := L) (A := A) th H Z.vx) th := by
  intro s s' a σ σ' G G' sl hW hRdLO hD1 hD2 hF hes hA hxn hx0 hoth hmS
  obtain ⟨⟨⟨hRd, hRL⟩, hLO, hTR⟩, hPd⟩ := hRdLO
  subst hth
  obtain ⟨E0, ⟨V, Ac, Lst, D, Jx, hkb, hns, hsg, hp0⟩, hL, ⟨lst, hDW⟩, hN⟩ := hW
  -- (f4g) the window's exempt set made `{0}` (so `vsNamed` is vacuous through the edit), `Z.vx`
  -- restored after with `VsNamed` from `VsPend` (`Vs.VsNamed.ofPendShr`)
  set Zu : XSets := { Z with vx := {0#u64} } with hZu
  have J : JAtZ (L := L) arI AR (Zu.mv G V) H Cs Ac Lst D s a σ := Jx.vxSet (fun h => absurd h vx0_ne)
  have hP := J.xtop.rel.1
  set E : Set U64 := ZTcb (L := L) Z.th s with hE
  have J0 := J.addDeadSet (E := E) hL.ztcb (fun p hp => J.jcov.dx p (J.zD p hp))
  -- `EmptyReadyX` at the grown dead set: a TCB in the range is a TCB zombie's (`TcbReady`)
  have hrx : EmptyReadyX (L := L) H Cs (D ∪ E) G s (cslotAddr sl) := by
    intro hp hu lo hi hlh h1 h2
    refine (hTR hp hu lo hi hlh h1 h2).imp_right fun h q hq hqD => ?_
    by_cases hHq : H q = some .tcb
    · exact (hqD (Or.inr (h q hq hHq))).elim
    · exact Sched.DeadX.of_ne hHq
  have hnk := emptySlot_null_nkn _ σ ((), σ') hes
  obtain ⟨⟨V2, hX2⟩, -, -, -⟩ := slotHypW_XZ AR (Zu.mv G V) kb s s' a σ σ' G G'
    ⟨⟨V, J0.xtop⟩, J0.ks, J0.thT, hkb⟩ hD1 hD2 hF hnk hmS
  obtain ⟨hks, hkb2, hfk2, hR⟩ : L.ksb s' = L.ksb s ∧ KBack σ σ' ∧ IpcFrKeep σ σ' ∧ _ := by
    by_cases hcn : ∃ q, sl.1 = q.bv ∧ Z.th q = some (.cnode sl.2.length)
    · exact J0.emptyJRD hA hcn hxn hRd hrx hes hD2 hx0 hoth hX2 (SlotFrame2.writesIn hF) hnk
    · exact J0.emptyJRTD hA hcn hxn hRd hrx hes hD2 hx0 hoth hX2 (SlotFrame2.writesIn hF) hnk
  have hcs := emptySlot_cdt_orig J.xtop.rel.2.1.1 hA hxn hes
  have hw : P1.WritesIn st s s' (InSlot Z.th) :=
    (SlotFrame2.writesIn hF).mono fun b hb => slotWd_range J.xtop.rel.1 hb
  have hUt : ∀ u up usb ufi udev, AbsSlot Z.th u → capAt (L.mem s) (cslotAddr u) = ok (.Untyped up usb ufi udev) →
      σ.cdt sl = some u → (∀ x, σ.cdt x = some u → x = sl) → (∀ x, σ.cdt x ≠ some sl) →
      DelUtFact (L := L) Z.th s' σ' up usb ufi udev := fun u up usb ufi udev hu hcu hpar honly hleaf =>
    let ⟨h1, h2⟩ := hRL
    J0.delUtFact_of hA hD2 hX2.rel.2.2.2.2.1.1.2.1 hx0 hoth hw hcs.1 hcs.2 hu hcu hpar honly hleaf h1 h2
  obtain ⟨hC, Ac', Lst', D', hDD, R⟩ := hR hUt
  have hvT : Vs.VsSlotsT Z.th (L.mem s) (L.mem s') :=
    Vs.VsSlotsT.of_some (· = cslotAddr sl) (fun y hy hn => hoth y hy hn)
      (fun y _ e _ _ _ _ _ _ => by rw [e, hx0]; trivial) (fun y _ e _ _ => by rw [e, hx0]; trivial) (fun y _ e _ => by rw [e, hx0]; trivial) fun y _ e _ _ => by rw [e, hx0]; trivial
  have hpp : PPR0 σ' := hp0.of_ppk (PPK.of_cnK hnk)
  -- the slots in use after
  set x := cslotAddr sl with hx
  have hob : σ'.isOriginalCap = Function.update σ.isOriginalCap sl false := hcs.2
  have hU : ∀ z, IsSlot Z.th z → InUse (L.mem s') σ' z → z ≠ x ∧ InUse (L.mem s) σ z := fun z hz hu => by
    by_cases e : z = x
    · exfalso
      subst e
      rcases hu with hu | ⟨y, hy, ho⟩
      · exact hu hx0
      · rw [hob] at ho
        by_cases hys : y = sl
        · subst hys; simp at ho
        · rw [Function.update_of_ne hys] at ho
          exact hys (cslotAddr_inj hP (J.kern.orig y ho) hA hy)
    · refine ⟨e, ?_⟩
      rcases hu with hu | ⟨y, hy, ho⟩
      · exact Or.inl (by rw [← hoth z hz e]; exact hu)
      · have hys : y ≠ sl := fun h => e (by rw [← hy, h])
        rw [hob, Function.update_of_ne hys] at ho
        exact Or.inr ⟨y, hy, ho⟩
  have hmd : ∀ y, IsSlot Z.th y → capV (L.mem s') y ≠ .Null → y ∈ G'.chains.flatten := fun y hy h =>
    (hD2.1.2.2.1.members y).2 ⟨hy, _, capAt_capV _ _, h⟩
  have hmem : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hD1.1.2.2.1.members y).1 hy).1
  have hkeep : ∀ y ∈ G.chains.flatten, y ≠ x → capV (L.mem s) y ≠ .Null →
      y ∈ G'.chains.flatten ∧ capV (L.mem s') y = capV (L.mem s) y := fun y hy hyx hn => by
    have e := hoth y (hmem y hy) hyx
    exact ⟨hmd y (hmem y hy) (by rw [e]; exact hn), e⟩
  -- the debug words
  have hdk := J.slotFrame_dbgKeep hF
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
    refine ⟨fun q i hqi hu => ?_, fun k hk hki => ?_, fun y hy p' zt' n' hz' i hpi hni hu => ?_,
      fun y hy p' zt' n' hz' hzt => ?_⟩
    · obtain ⟨hne, hu⟩ := hU _ ⟨q, i, hqi, rfl⟩ hu
      rcases hLO.1 q i hqi hne hu with ⟨y, hy, hyx, hr⟩ | hb
      rotate_left
      · exact Or.inr (by rw [hdk.1]; exact hb)
      have hn : capV (L.mem s) y ≠ .Null := fun h => by rw [h] at hr; exact hr
      obtain ⟨hy', e⟩ := hkeep y hy hyx hn
      exact Or.inl ⟨y, hy', by rw [e]; exact hr⟩
    · rw [hNt] at hk hki ⊢
      obtain ⟨y, hy, hyx, hr⟩ := hLO.2 k hk (by rw [← hnk.idle]; exact hki)
      obtain ⟨hy', e⟩ := hkeep y hy hyx (by rw [hr]; simp)
      exact ⟨y, hy', by rw [e]; exact hr⟩
    · have hyx : y ≠ x := fun h => by rw [h, hx0] at hz'; cases hz'
      have hw : capV (L.mem s) y = .Zombie p' zt' n' := by rw [← hoth y hy hyx]; exact hz'
      exact hL.zslots y hy p' zt' n' hw i hpi hni (hU _ ⟨p', i, hpi, rfl⟩ hu).2
    · have hyx : y ≠ x := fun h => by rw [h, hx0] at hz'; cases hz'
      have hw : capV (L.mem s) y = .Zombie p' zt' n' := by rw [← hoth y hy hyx]; exact hz'
      exact R.jcov.dead p' (hDD (Or.inr ⟨y, hy, zt', n', hw, hzt⟩))
  have hDW' := dbgWFL_step J.xtop hX2 rfl rfl J.tcbs_eq.1 hDW hdk
  have hN' := hN.empty hP J.xtop.rel.2.1.1 hA hxn hes hoth
  have hZf : ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D' := fun p ⟨y, hy, zt', n', hz', hzt⟩ => by
    have hyx : y ≠ x := fun h => by rw [h, hx0] at hz'; cases hz'
    have hw : capV (L.mem s) y = .Zombie p zt' n' := by rw [← hoth y hy hyx]; exact hz'
    exact hDD (Or.inr ⟨y, hy, zt', n', hw, hzt⟩)
  have J' := J0.cs_frameB (hvn := fun h => absurd h vx0_ne) hks (J0.xtop.vs_backC hX2 (SlotFrame2.writesIn hF) hnk) hkb2 (J0.bfK hfk2 hvT) hC R (J0.vsc.step hvT) (J0.ext.step hvT (J0.vkeep_slot ((SlotFrame2.writesIn hF).mono fun b hb => slotWd_range J0.xtop.rel.1 hb)))
    ⟨hL', ⟨lst, hDW'⟩, hN'⟩ hZf (J0.carry.of_objCn hnk.2)
    (devFrom_kept hD1.1.2.2.1 hD2.1.2.2.1 J0.ut (utKept_ins hoth fun p0 sb0 fi0 d0 h => by rw [hx0] at h; cases h))
    (J0.carry.vsStep rfl hvT subset_rfl subset_rfl subset_rfl subset_rfl rfl hks (ArchFwd.of_objCn hnk.2)) (ArchFwd.of_objCn hnk.2)
  -- `VsNamed` after the empty from `VsPend` before
  have hXb := J0.xtop.vs_backC hX2 (SlotFrame2.writesIn hF) hnk
  have hvn' : Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s') (L.ksb s') := fun hvx => by
    have hR' : Vs.VsRel V.1 (L.mem s') (L.ksb s) σ' := by rw [← hks]; exact hXb.fin.2.1
    rw [hks]
    exact Vs.VsNamed.ofPendShr (hPd hvx) J0.vsc J0.xtop.fin.2.1 J0.xtop.fin.2.2.1 J0.xtop.fin.2.2.2.1 hR'
      hXb.fin.2.2.1 (Vs.ArchShr.of_objCn hnk.2 (by have e := congrArg Fl4Spec.AbstractState.archState hnk.1; exact e))
      (fun y hy hyx => hoth y hy hyx) (by rw [hx0]; rfl)
  have J'' : JAtZ (L := L) arI AR (Z.mv G' V) H Cs Ac' Lst' D' s' a σ' := J'.vxSet hvn'
  exact ⟨⟨V, Ac', Lst', D', J'', hks.trans hkb, (ak_emptySlot' _ _).noSwitch hes hns, SpecGlob.empty hes hsg,
    hpp⟩, hL', ⟨lst, hDW'⟩, hN'⟩

end

end

end Fl4Proofs.P3
