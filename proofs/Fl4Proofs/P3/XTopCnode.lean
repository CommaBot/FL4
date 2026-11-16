/-
P3 (DESIGN.md §9), CSpace: **the CNode cap at the composite relation**
(`CnodeXHyp`).

* `capMove_nko`, `capSwap_nko`, `invoke_cn`: the spec side of a copy, move
  or rotate: `CnK`, the heap changed at the invocation's slots' objects only.
* `Steps.cnTrace`: the restart and a CNode-only step (StepSem's `cslot`)
  from `CnTrace` (CnodeCopy), the CSpace relation after.
* `cnode_copyX`, `cnode_rotateX`: `cnode::decode` at the copy, mint, move,
  mutate and rotate labels, to `XTop` (`Steps.xtop`).
-/
import Fl4Proofs.P3.XTopCaps
import Fl4Proofs.P3.DomSched
import Fl4Proofs.P3.CnodeDecode
import Fl4Proofs.P3.SpecNKO
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

/-- **`cap_move` changes the heap at the source's and the destination's
objects only.** -/
theorem capMove_nko (c : Cap) (src dest : CslotPtr) :
    NKO {src.1, dest.1} (capMove (Z := Unit) c src dest) := by
  unfold capMove setCdt setOriginal
  repeat (first | exact nko_getCap _ | exact nko_setCap _ _ (by simp) | exact nko_doExtendedOp _ |
    exact nko_pure _ | exact nko_pure' _ | exact nko_fail | exact nko_gets _ | exact nko_get |
    exact nko_assert _ | exact nko_get_put (fun σ => rfl) |
    exact nko_modify (fun σ => rfl) | (refine nko_bind ?_ (fun _ => ?_)) |
    (apply nko_ite) | split)

/-- **`cap_swap` changes the heap at the two slots' objects only.** -/
theorem capSwap_nko (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) :
    NKO {s1.1, s2.1} (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt setOriginal
  repeat (first | exact nko_getCap _ | exact nko_setCap _ _ (by simp) | exact nko_doExtendedOp _ |
    exact nko_pure _ | exact nko_pure' _ | exact nko_fail | exact nko_gets _ | exact nko_get |
    exact nko_assert _ | exact nko_get_put (fun σ => rfl) |
    exact nko_modify (fun σ => rfl) | (refine nko_bind ?_ (fun _ => ?_)) |
    (apply nko_ite) | split)

theorem nko_mono {α : Type} {Ps Ps' : Set ObjRef} {m : NonDet (State Unit) α} (h : Ps ⊆ Ps') (hm : NKO Ps m) :
    NKO Ps' m := fun σ x hx p hp => hm σ x hx p (fun h' => hp (h h'))

/-- **The spec side of a CNode copy, move or rotate**: `CnK`, and the heap
kept outside the invocation's slots' objects. -/
theorem invoke_cn {inv : CnodeInvocation} (hne : invSlots inv ≠ []) {σ σ' : State Unit}
    (h : ((.ok (), σ') : Except Unit Unit × State Unit) ∈ ((invokeCnode (Z := Unit) inv).run σ).1) :
    CnK σ σ' ∧ ∀ p, (∀ sl ∈ invSlots inv, p ≠ sl.1) → σ'.kheap p = σ.kheap p := by
  cases inv with
  | insertCall c a b =>
    obtain ⟨x, hx, e⟩ := Sched.liftE_mem_inv h
    simp only at e; subst e
    refine ⟨capInsert_nkn c a b σ x hx, fun p hp => capInsert_nko c a b σ x hx p ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hp _ (by simp [invSlots]), hp _ (by simp [invSlots])⟩
  | moveCall c a b =>
    obtain ⟨x, hx, e⟩ := Sched.liftE_mem_inv h
    simp only at e; subst e
    refine ⟨capMove_nkn c a b σ x hx, fun p hp => capMove_nko c a b σ x hx p ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hp _ (by simp [invSlots]), hp _ (by simp [invSlots])⟩
  | rotateCall c1 c2 a b d =>
    obtain ⟨x, hx, e⟩ := Sched.liftE_mem_inv h
    simp only at e; subst e
    have hp3 : ∀ p, (∀ sl ∈ invSlots (.rotateCall c1 c2 a b d), p ≠ sl.1) → p ∉ ({a.1, b.1, d.1} : Set ObjRef) := by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hp _ (by simp [invSlots]), hp _ (by simp [invSlots]), hp _ (by simp [invSlots])⟩
    split_ifs at hx with hs
    · refine ⟨capSwap_nkn c1 a c2 b σ x hx, fun p hp => ?_⟩
      refine nko_mono (Ps := {a.1, b.1}) (fun q hq => ?_) (capSwap_nko c1 a c2 b) σ x hx p (hp3 p hp)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
      rcases hq with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine ⟨nkn_bind (capMove_nkn c2 b d) (fun _ => capMove_nkn c1 a b) σ x hx, fun p hp => ?_⟩
      refine nko_bind (Ps := {a.1, b.1, d.1})
        (nko_mono (fun q hq => ?_) (capMove_nko c2 b d)) (fun _ => nko_mono (fun q hq => ?_) (capMove_nko c1 a b))
        σ x hx p (hp3 p hp)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
        rcases hq with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
        rcases hq with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
  | revokeCall _ => exact absurd rfl hne
  | deleteCall _ => exact absurd rfl hne
  | cancelBadgedSendsCall _ => exact absurd rfl hne

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **A CNode copy, move or rotate as primitive steps**: the restart, then a
CNode-only step (`cslot`), from FL4's trace (`CnTrace`) and the spec's
outcome. -/
theorem Steps.cnTrace {th : TypedHeap} (hP : Placed th) {s s2 s' : S} {a : A}
    {σ σ1 σ' : Fl4Spec.State Unit} {G' : MdbGhost} {ct : U64} {x : Fl4Spec.Tcb}
    (hcur : σ.curThread = ct.bv) (hk : σ.kheap ct.bv = some (.tcb x)) (htcb : th ct = some .tcb)
    (hs2 : sched.set_thread_state st s ct sched.TS_RESTART = ok s2)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hR1 : StateRel th (L.mem s2) σ1) (hks : L.ksb s2 = L.ksb s)
    {inv : Fl4Spec.CnodeInvocation} (hne : invSlots inv ≠ [])
    (hrun : (Fl4Spec.invokeCnode (Z := Unit) inv).run σ1 = ({(.ok (), σ')}, False))
    (hF : Vs.SlotFrame2 (L := L) th s2 s')
    (hsl : ∀ sl ∈ invSlots inv, ∃ p r, sl.1 = p.bv ∧ th p = some (.cnode r) ∧ sl.2.length = r)
    (hcap : ∀ y, IsSlot th y → (∀ sl ∈ invSlots inv, y ≠ cslotAddr sl) → capV (L.mem s') y = capV (L.mem s2) y)
    (hCR : CRel th (L.mem s') σ' G') (hFI : FinInv th (L.mem s') σ' G') (hMO : MdbOKV (L.ksb s) (L.mem s') G') :
    Steps (L := L) arI th s a σ s' a σ' := by
  refine (Steps.restart arI hcur hk htcb hs2 hst).trans arI fun Q hQ => ?_
  have hmem : ((.ok (), σ') : Except Unit Unit × Fl4Spec.State Unit) ∈
      ((Fl4Spec.invokeCnode (Z := Unit) inv).run σ1).1 := by rw [hrun]; rfl
  obtain ⟨hcn, hO⟩ := invoke_cn hne hmem
  have hkc : KeepC σ1 σ' := keepC_of (Ps := {p | ∃ sl ∈ invSlots inv, p = sl.1}) hcn
    (fun p hp => hO p fun sl hs e => hp ⟨sl, hs, e⟩) (fun p ⟨sl, hs, e⟩ => by
      obtain ⟨q, r, h1, h2, -⟩ := hsl sl hs
      obtain ⟨cs, h, -⟩ := hR1.cnode q r h2
      exact ⟨r, cs, by rw [e, h1]; exact h⟩)
  refine hQ.cslot s2 s' a σ1 σ' G' hcn hkc
    ⟨hF.1, hF.2.1, fun b hb hn => hF.2.2 b hb fun ⟨y, k, hy, hk', e⟩ => hn ⟨y, hy, ?_⟩⟩ hCR hFI
    (by rw [hks]; exact hMO) fun t ht => ?_
  · have hf := hy.fit hP
    have := hk'.lt
    have hv := wordOf_val (a := y) (k := k) (by omega)
    rw [e, hv]; omega
  · have h1 : IsSlot th (slotOf t 1) := ⟨t, 1, Or.inr ⟨ht, by decide⟩, rfl⟩
    have hne' : ∀ sl ∈ invSlots inv, slotOf t 1 ≠ cslotAddr sl := by
      intro sl hsl' e
      obtain ⟨q, r, hq1, hq2, hq3⟩ := hsl sl hsl'
      obtain ⟨p, i, hi, hp1, hp2⟩ := AbsSlot.at (th := th) (sl := sl) ⟨q, hq1, Or.inl (by rw [hq3]; exact hq2)⟩
      have hpp : p = q := P1.eq_of_bv (hp1.symm.trans hq1)
      subst hpp
      have := IsSlotAt.apart hP (Or.inr ⟨ht, by decide⟩ : IsSlotAt th t 1) hi (fun hh => by
        obtain ⟨h, -⟩ := hh; subst h; rw [hq2] at ht; cases ht)
      rw [e, hp2] at this; omega
    rw [capAt_capV, capAt_capV, hcap _ h1 hne']

set_option maxHeartbeats 4000000 in
/-- **A copy, move or rotate's outcome at `XTop`**: from `InvPost` with
FL4's trace (`CnTrace`) and the arch state kept, `TopPostDMX`. -/
theorem cn_topX {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) {Z : XSets} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDel : XDelNtfnHyp (L := L) arI AR Z.th)
    {ct : U64} (hcur : σ.curThread = ct.bv) {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (hq : InvPost (L := L) Z.th σ Z.G m s (res.1, res.2.1) (CnTrace (L := L) Z.th ct s) ∧ res.2.2 = ar) :
    TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m)
      s res := by
  obtain ⟨r, s', a'⟩ := res
  obtain ⟨hq, rfl⟩ := hq
  cases r with
  | Err e =>
    obtain ⟨rfl, e', h1, h2⟩ := hq
    exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ⟨Z, hX⟩⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', hrunI, hR', hV', hM', hC', hI', hFI', hSt, s2, hne, hs2, hF, hsl, hcap⟩ := hq
    obtain ⟨htcb, x, hk⟩ := hX.curTcb hcur
    have hst' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by rw [← hcur]; exact hst
    obtain ⟨hX1, hks, -⟩ := hX.restart' hC hcur hs2 hst'
    have hstp : Steps (L := L) arI Z.th s a' σ s' a' σ' :=
      Steps.cnTrace arI hX.rel.1 hcur hk htcb hs2 hst hX1.rel.2.1.1 hks hne hrunI hF hsl hcap
        ⟨hR', hV', hM', hC', hI'⟩ hFI' (hSt.okv hX.rel.2.2.2.2.1)
    obtain ⟨Z', hZ'⟩ := hstp.xtop arI hAM hDel rfl hX hKA hC hTh
    have hx : ((.ok (), σ') : Except Unit Unit × Fl4Spec.State Unit) ∈
        ((Fl4Spec.invokeCnode (Z := Unit) inv).run σ1).1 := by rw [hrunI]; rfl
    exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
      mem_bindE_ok hx (Set.mem_singleton _), ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩, hZ'.rel.1, hZ'.rel.2.1,
        hZ'.rel.2.2.1, hZ'.rel.2.2.2.1, hZ'.rel.2.2.2.2.1⟩, ⟨Z', hZ'⟩⟩

/-- **`CnodeXHyp` at the copy, mint, move, mutate and rotate labels**
(28..32): `cnode_copy_refines`, `cnode_rotate_refines`, then `cn_topX`. -/
theorem decode_invocation_cnode_copyX {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) {Z : XSets} (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ)
    (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T)
    (hDel : XDelNtfnHyp (L := L) arI AR Z.th)
    (lbl : U64) (hl : 28 ≤ lbl.val ∧ lbl.val ≤ 32) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel2 Z.th (L.mem s) x0 x1 (excaps.map Prod.fst))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot (.CNode p r gs g) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, hFI⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hcp : 28 ≤ lbl.val ∧ lbl.val ≤ 31
    · exact WP.spec_mono (cnode_copy_refines arI Z.th s ar σ Z.G hR hV hX.rel.1 hM hCd lbl slbl hlbl hcp length buf
        ct hct args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra x0 hx0 _ hex.one hI hFI hact hcur htcb)
        fun res h => cn_topX arI hAM hX hKA hC hTh hDel hcur h
    · have e : lbl = fl4_abi.label.CNodeRotate := UScalar.eq_of_val_eq (by rw [lbl_rotate_val]; omega)
      subst e
      exact WP.spec_mono (cnode_rotate_refines arI Z.th s ar σ Z.G hR hV hX.rel.1 hM hCd slbl
        (by rw [hlbl]; simp [cnodeLabelOf]) length buf ct hct args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra x0 x1 hx0 hx1 _
        hex hI hFI hact hcur htcb) fun res h => cn_topX arI hAM hX hKA hC hTh hDel hcur h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩

end

end

end Fl4Proofs.P3
