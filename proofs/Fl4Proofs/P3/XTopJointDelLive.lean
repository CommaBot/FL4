/-
P3 (DESIGN.md §9), CSpace: **a notification cap's deletion at `J` from
liveness** (`JStepHyps.del`), and the J decodes with the primitive steps'
closure built from it (`JStepHyps.of_ut`).

* `DelLive`: the liveness facts the empty-slot path reads (XTopJointDelR's
  `JEmptyUtHyp` (a), (b)): every slot in use but the emptied one covered by
  another cap or in the kernel-state block (`SlotLiveAt`), core 0's
  debug-list head, when not null, covered by another cap. `DelLive.of_same`:
  across a step keeping the slots, the kernel base, the original bits and
  the debug word.
* `DelUtHyp` [J]: `DelLive` at a notification cap's deletion's pre-state,
  when its slot holds an untyped cap's only child (l4v
  `if_unsafe_then_cap` with `cap_removeable`, and `if_live_then_nonz_cap`
  for the debug list; as `JEmptyUtHyp`). Was: `DelUtFact` at the state
  after, outright.
* `jowes_del`: `JStepHyps.del` from `DelUtHyp`: the finalisation (`finNtfnJ`
  when final, nothing otherwise), then the slot emptied (`emptyNtfnJ`), the
  untyped caps' facts after by `JAtZ.delUtFact_of` (XTopJointEmptyUt) from
  `DelLive` at the emptying's pre-state (`DelLive.of_same` across the
  finalisation: its slots kept, `fin_cap_ntfn.slots`' footprint for the
  debug word).
* `JStepHyps.of_ut`: `JStepHyps` from `DelUtHyp`.
* `decode_invocation_{irq_control, ioport_control, irq_handler, domain}J`:
  XTopJointStep's J decodes with `DelUtHyp` in place of `JStepHyps`.
-/
import Fl4Proofs.P3.XTopJointEmptyUt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The liveness facts of emptying the slot `sl`** (module docstring;
`JEmptyUtHyp`'s (a), (b)). -/
def DelLive (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) : Prop :=
  (∀ y, IsSlot th y → y ≠ cslotAddr sl →
    (capV (L.mem s) y ≠ .Null ∨ ∃ x, cslotAddr x = y ∧ σ.isOriginalCap x = true) →
    SlotLiveAt (L.mem s) G (L.ksb s) (cslotAddr sl) y) ∧
  (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ≠ 0#u64 →
    OtherCov (L.mem s) G (cslotAddr sl) (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val
      ((L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val + 1))

theorem OtherCov.of_same {m m' : U64 → U64} {G : MdbGhost} {x : U64} {lo hi : Nat}
    (h : OtherCov m G x lo hi) (he : ∀ y ∈ G.chains.flatten, capV m' y = capV m y) : OtherCov m' G x lo hi := by
  obtain ⟨y, hy, hyx, h1, h2, h3, h4⟩ := h
  exact ⟨y, hy, hyx, by rw [he y hy]; exact h1, by rw [he y hy]; exact h2, by rw [he y hy]; exact h3,
    by rw [he y hy]; exact h4⟩

/-- **`DelLive` across a step keeping the slots** (module docstring). -/
theorem DelLive.of_same {th : TypedHeap} {s s' : S} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    {sl : Fl4Spec.CslotPtr} (h : DelLive (L := L) th s σ G sl) (hSS : SlotsSame th (L.mem s) (L.mem s'))
    (hG : ∀ y ∈ G.chains.flatten, IsSlot th y) (hks : L.ksb s' = L.ksb s)
    (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hdbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    DelLive (L := L) th s' σ' G sl := by
  have he : ∀ y ∈ G.chains.flatten, capV (L.mem s') y = capV (L.mem s) y := fun y hy => hSS.capV (hG y hy)
  have hna : L.nodeAt s' 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    nodeAt_ksb hks _ _
  refine ⟨fun y hy hne hu => ?_, fun h0 => ?_⟩
  · have hu' : capV (L.mem s) y ≠ .Null ∨ ∃ x, cslotAddr x = y ∧ σ.isOriginalCap x = true := by
      rcases hu with hu | ⟨x, hx, ho⟩
      · exact Or.inl (by rw [← hSS.capV hy]; exact hu)
      · exact Or.inr ⟨x, hx, by rw [← horig]; exact ho⟩
    rcases h.1 y hy hne hu' with hc | hk
    · exact Or.inl (hc.of_same he)
    · exact Or.inr (by rw [hks]; exact hk)
  · rw [hna, hdbg] at h0 ⊢
    exact (h.2 h0).of_same he

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **Hypothesis: the liveness facts of a notification cap's deletion** [J]
(module docstring), at the deletion's pre-state, shaped as `JEmptyUtHyp`'s
(a), (b). -/
def DelUtHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (p b : U64) (w r : Bool),
    AbsSlot th sl → capV (L.mem s) (cslotAddr sl) = .Notification p b w r →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
      ∀ u up usb ufi udev, AbsSlot th u → capAt (L.mem s) (cslotAddr u) = ok (.Untyped up usb ufi udev) →
        σ.cdt sl = some u → (∀ x, σ.cdt x = some u → x = sl) → (∀ x, σ.cdt x ≠ some sl) →
        DelLive (L := L) th s σ Z.G sl

set_option maxHeartbeats 16000000 in
/-- **`JStepHyps.del` from `DelUtHyp`** (module docstring). -/
theorem jowes_del [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}
    (hUt : DelUtHyp (L := L) arI AR th) :
    ∀ (s s' : S) (a a' : A) (σ σ' : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (p b : U64) (w r : Bool),
      AbsSlot th sl → (∃ q, sl.1 = q.bv ∧ th q = some (.cnode sl.2.length)) →
      capV (L.mem s) (cslotAddr sl) = .Notification p b w r →
      cdt.delete_one st arI s a (cslotAddr sl) = ok (s', a') → ((), σ') ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 →
      ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → ∃ (G' : MdbGhost) (V' : XVs),
          XTopAt (L := L) AR (Z.mv G' V') s' a' σ' ∧ L.ksb s' = L.ksb s ∧ KBack σ σ' ∧
          JCs (L := L) (Z.mv G' V') s' σ' ∧
          ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
            JRest (L := L) arI (Z.mv G' V') H Cs Ac' Lst' D' s' σ' := by
  intro s s' a a' σ σ' sl p b w r hA hcnode hcv0 hrun hm Z H Cs Ac Lst D hth J
  have hU0 := hUt s a σ sl p b w r hA hcv0 Z H Cs Ac Lst D hth J
  subst hth
  have hP := J.xtop.rel.1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩
  have hGs : ∀ y ∈ Z.G.chains.flatten, IsSlot Z.th y := fun y hy => ((J.xtop.rel.2.1.2.2.1.members y).1 hy).1
  obtain ⟨c, ac, hc0, hca, hg⟩ := hDS.1.1.abs_cap hA
  rw [hca.abs] at hg
  have hcv := capV_of_capAt hc0
  rw [hcv] at hcv0; subst hcv0
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .ntfn := ((hJ.typed _ hA.isSlot).2.1 p b w r hcv).2
  have hpN : p ∈ Z.N := J.hset.2.1 p hHp
  have hcn : capability.Cap.Notification p b w r ≠ .Null := by simp
  -- the spec's deletion from the finalisation's and the emptying's outcomes
  have hspec : ∀ (σ1 σ2 : Fl4Spec.State Unit) (cl : capability.Cap),
      ((absCap .Null, absCap cl), σ1) ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Notification p b w r))
        (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ)) σ).1 →
      ((), σ2) ∈ (Fl4Spec.emptySlot (Z := Unit) sl .nullCap σ1).1 →
      ((), σ2) ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 := by
    intro σ1 σ2 cl hmem hes
    unfold Fl4Spec.capDeleteOne
    refine mem_bind_nd (x := (absCap (.Notification p b w r), σ)) (by rw [hg]; rfl) ?_
    simp only [absCap, Fl4Spec.NonDet.unless, reduceCtorEq, ↓reduceIte]
    refine mem_bind_nd (x := (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ), σ)) rfl ?_
    refine mem_bind_nd (x := ((), σ1)) (fastFinalise_of_finaliseCap hmem) ?_
    exact hes
  have key : cdt.delete_one st arI s a (cslotAddr sl) ⦃ res => ∃ σ2 G2 V2,
      ((), σ2) ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 ∧ XTopAt (L := L) AR (Z.mv G2 V2) res.1 res.2 σ2 ∧
      L.ksb res.1 = L.ksb s ∧ KBack σ σ2 ∧
      JCs (L := L) (Z.mv G2 V2) res.1 σ2 ∧
        ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JRest (L := L) arI (Z.mv G2 V2) H Cs Ac' Lst' D' res.1 σ2 ⦄ := by
    unfold cdt.delete_one
    rw [slot_cap_eq, hc0]
    simp only [bind_ok, cap_is_null_eq]
    simp only [isNullB_false hcn, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨bf, hbf, hbf2, -⟩ := finalHyp_full Z.th hP s σ Z.G sl _ hDS hA hc0 hcn
    have hNF : NeedsFin (.Notification p b w r) := Or.inl ⟨trivial, rfl⟩
    rw [hbf2 hNF] at hbf
    rw [is_final_with_cap_eq _ _ _ hc0, hbf]; simp only [bind_ok]
    rw [← finalise_cap_ntfn arI s a p b w r _ false]
    by_cases hfin : Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ
    · have hdt : decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ) = true := decide_eq_true hfin
      rw [hdt]
      refine WP.spec_bind (WP.spec_and (WP.spec_and (J.finNtfnJ hpN)
        (P1.fin_cap_ntfn.dead (ar := arI) s a p b w r false J.blk hHp hHp))
        (P1.fin_cap_ntfn.slots (ar := arI) s a p b w r true false J.blk hHp hHp)) ?_
      rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨⟨e1, e2, σ1, V1, hmem1, J1, hkb1, hSS1, hks1⟩, d1, d2, d3⟩, -, -, hfoot1, -⟩
      simp only at e1 e2 hmem1 J1 hkb1 hSS1 hks1 d1 d2 d3 hfoot1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
      subst e2
      simp only [uncurry_apply_pair]
      have hdp : DeadP (L := L) H s1 p :=
        ⟨fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h), fun _ => ⟨d1, d2, d3⟩,
          fun h => (by rw [hHp] at h; cases h), fun z h => (by rw [hHp] at h; cases h)⟩
      have hc1 : capAt (L.mem s1) (cslotAddr sl) = ok (.Notification p b w r) := by
        rw [capAt_capV, hSS1.capV hA.isSlot, hcv]
      have hck := finNtfn_nkc p.bv b.bv _ true σ _ hmem1
      have hcdt1 : σ1.cdt = σ.cdt := hck.cdt
      have hDbg1 := J.kw_dbg hfoot1
      refine WP.spec_mono (J1.emptyNtfnJ hA hcnode hc1 (Or.inl hdp)) ?_
      rintro ⟨s2, a2⟩ ⟨e3, σ2, G2, V2, hes, hX2, hks2, hkb2, hDS2, hnull2, hoth2, hw2, hcdt2, hor2, hR2⟩
      simp only at e3 hes hX2 hks2 hkb2 hDS2 hnull2 hoth2 hw2 hcdt2 hor2 hR2 ⊢
      subst e3
      refine ⟨σ2, G2, V2, hspec σ1 σ2 .Null (by rw [hdt]; exact hmem1) hes, hX2, hks2.trans hks1,
        hkb1.trans' hkb2, hR2 fun u up usb ufi udev hu hcu h1 h2 h3 => ?_⟩
      have hcu0 : capAt (L.mem s) (cslotAddr u) = ok (.Untyped up usb ufi udev) := by
        rw [capAt_capV, ← hSS1.capV hu.isSlot, ← capAt_capV]; exact hcu
      rw [hcdt1] at h1 h2 h3
      have hL := (hU0 u up usb ufi udev hu hcu0 h1 h2 h3).of_same hSS1 hGs hks1 hck.orig hDbg1
      exact J1.delUtFact_of hA hDS2 hX2.rel.2.2.2.2.1.1.2.1 hnull2 hoth2 hw2 hcdt2 hor2 hu hcu
        (by rw [hcdt1]; exact h1) (by rw [hcdt1]; exact h2) (by rw [hcdt1]; exact h3) hL.1 hL.2
    · have hdf : decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ) = false := decide_eq_false hfin
      rw [hdf]
      obtain ⟨cl, he, hmem, hcl, hrem, hnio⟩ := fin_idle (st := st) (L := L) arI s a σ (.Notification p b w r) trivial
        false (fun hw => by have := finWork_ntfn hw; cases this)
      have hcl0 : cl = .Null := hnio (fun f l e => by cases e)
      subst hcl0
      rw [he]; simp only [bind_ok]
      simp only [uncurry_apply_pair]
      refine WP.spec_mono (J.emptyNtfnJ hA hcnode hc0 (Or.inr (other_ntfn hP hDS hA hcv hfin))) ?_
      rintro ⟨s2, a2⟩ ⟨e3, σ2, G2, V2, hes, hX2, hks2, hkb2, hDS2, hnull2, hoth2, hw2, hcdt2, hor2, hR2⟩
      simp only at e3 hes hX2 hks2 hkb2 hDS2 hnull2 hoth2 hw2 hcdt2 hor2 hR2 ⊢
      subst e3
      refine ⟨σ2, G2, V2, hspec σ σ2 .Null (by rw [hdf]; exact hmem) hes, hX2, hks2, hkb2,
        hR2 fun u up usb ufi udev hu hcu h1 h2 h3 => ?_⟩
      have hL := hU0 u up usb ufi udev hu hcu h1 h2 h3
      exact J.delUtFact_of hA hDS2 hX2.rel.2.2.2.2.1.1.2.1 hnull2 hoth2 hw2 hcdt2 hor2 hu hcu h1 h2 h3 hL.1 hL.2
  rw [hrun, WP.spec_ok] at key
  obtain ⟨σ2, G2, V2, hm2, hX2, hks2, hkb2, hC2, R2⟩ := key
  have e := (Det.detAt_capDeleteOne_ntfn hg).eq hm2 hm
  have e2 : σ2 = σ' := congrArg Prod.snd e
  subst e2
  exact ⟨G2, V2, hX2, hks2, hkb2, hC2, R2⟩

/-- **`JStepHyps` from `DelUtHyp`** (`JStepHyps.of_del` with `jowes_del`):
the primitive steps' closure at `J` from the deletion's liveness facts. -/
theorem JStepHyps.of_ut [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}
    (hUt : DelUtHyp (L := L) arI AR th) : JStepHyps (L := L) arI AR th :=
  JStepHyps.of_del arI (jowes_del arI hUt)

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The IRQ control cap at `JAt`** from `DelUtHyp`
(`decode_invocation_irq_controlJ_step`, `JStepHyps.of_ut`). -/
theorem decode_invocation_irq_controlJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) (hUt : DelUtHyp (L := L) arI AR Z.th)
    (hHA : HandlersActive (L.mem s) (L.ksb s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : IrqCLabel lbl slbl)
    (hrm : decide (lbl.val = 72) = Fl4Spec.isFl4RemappedLabel slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (nA : U64) (hnum : arI.num_ioapics ar = ok nA) (hnA : nA.bv = σ.archState.x64NumIoapics)
    (hAR : ArchIrqRel arI ar σ) (blk call don fp : Bool) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IrqControl blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct :=
  decode_invocation_irq_controlJ_step arI s ar σ J hni hARI hT (JStepHyps.of_ut arI hUt) hHA lbl slbl hlbl hrm
    length buf ct hct args hlen hargs hact2 extra x0 hx0 excaps hex hps hls hsrcC nA hnum hnA hAR blk call don fp ci
    buffer

/-- **The IO port control cap at `JAt`** from `DelUtHyp`. -/
theorem decode_invocation_ioport_controlJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) (hUt : DelUtHyp (L := L) arI AR Z.th)
    (hPA : IoPortsAlloc (L.mem s) (L.ksb s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : lbl.val = 63 ↔ Fl4Spec.invocationType slbl = .archInvocationLabel .x64IOPortControlIssue)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hact3 : ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IoPortControl)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IoPortControl blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct :=
  decode_invocation_ioport_controlJ_step arI s ar σ J hni hARI hT (JStepHyps.of_ut arI hUt) hPA lbl slbl hlbl
    length buf ct hct args hlen hargs hact3 extra x0 hx0 excaps hex hps hls hsrcC blk call don fp ci buffer

/-- **The IRQ handler cap at `JAt`** from `DelUtHyp`. -/
theorem decode_invocation_irq_handlerJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) (hUt : DelUtHyp (L := L) arI AR Z.th)
    (hO : FinObjHyp (L := L) arI Z.th) (hPD : PostDelHyp (L := L) arI Z.th) (hK : NtfnKeepHyp (L := L) arI Z.th)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = irqHLabelOf lbl)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (irq : U64) (hsc : capV (L.mem s) (cslotAddr sl) = .IrqHandler irq)
    (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : lbl.val = 35 → ExtraSRel Z.th (L.mem s) x0 excaps) (hxn : lbl.val = 35 → x0 ≠ nodeA (L.ksb s) irq)
    (hD : DomPlaced (L := L) Z.th s) (hP1 : IrqDelP1 (L := L) s ct irq)
    (length buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.IrqHandler irq) blk call don fp buf
      extra slbl args ci sl excaps buffer ct :=
  decode_invocation_irq_handlerJ_step arI s ar σ J hni hARI hT (JStepHyps.of_ut arI hUt) hO hPD hK lbl slbl hlbl
    ct hct sl hAs irq hsc hok extra x0 hx0 excaps hex hxn hD hP1 length buf blk call don fp args ci buffer

/-- **The domain cap at `JAt`** from `DelUtHyp`. -/
theorem decode_invocation_domainJ [Fl4Proofs.P1.PlainStore st] (hcfg : DomConfig) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hUt : DelUtHyp (L := L) arI AR Z.th)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects Z.th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = domLabelOf lbl)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel Z.th (L.mem s) x0 excs)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot .Domain blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excs buffer ct :=
  decode_invocation_domainJ_step arI hcfg s ar σ J hni hARI (JStepHyps.of_ut arI hUt) ct hct hksO hactK lbl slbl hlbl
    length buf args hlen hargs extra x0 hx0 excs hex slot blk call don fp ci sl buffer

end

end

end Fl4Proofs.P3
