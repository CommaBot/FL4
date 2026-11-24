/-
P3 (issue #16, F1 stage 5, item 4; KENTRY-PLAN f4): **`VsNamed` across a retype
without a reset** (the no-reset retypes of UtCnRet, UtEpRet, UtScRet, UtUtRet,
UtDevRet, UtDevUt, UtTcbRet: no new cap keyed).

* `Vs.VsKeep.retype`: a retype (`RetExp`) whose new caps are unkeyed keeps the
  keyed caps (`VsKeep`): a keyed cap is never untyped, so it is an old slot kept
  by `RetExp.keep`; every keyed cap after is old (`gmem`, `utk`, `newc`).
* `Vs.ArchShr.of_specAdd`: the spec's object creation (`SpecAdd`) keeps every
  old object and the abstract state but the heap.
* `XTopAt.vsNamedRet`: both through `Vs.VsNamed.stepShr`, the spec's
  `SpecAdd` then a CNode step (`CnK` / `KeepC`) for `ArchShr`.
* `JAtZ.vsNamedDrop` (moved here from VsNamedJ so that the drops UtDropJ2 /
  UtDevDrop can use it): `VsNamed` at the drop's typed heap.
-/
import Fl4Proofs.P3.JointAt
import Fl4Proofs.P3.ScFresh
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- **A retype with unkeyed new caps keeps the keyed caps** (`VsKeep`). -/
theorem _root_.Fl4Proofs.P3.Vs.VsKeep.retype {th th' : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost}
    {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hE : RetExp th th' m m' G G' A k w dslot cj xs) (hM : MdbLinks th m G) (hM' : MdbLinks th' m' G')
    (hnk : ∀ j, j < w → Vs.VKey (cj j) = none) : Vs.VsKeep th th' m m' := by
  have hmem : ∀ {th0 : TypedHeap} {m0 : U64 → U64} {G0 : MdbGhost}, MdbLinks th0 m0 G0 → ∀ y, IsSlot th0 y →
      Vs.VKey (capV m0 y) ≠ none → y ∈ G0.chains.flatten := fun hM0 y hy hk =>
    (hM0.members y).2 ⟨hy, _, capAt_capV _ _, fun e => hk (by rw [e]; rfl)⟩
  have hnu : ∀ c : capability.Cap, Vs.VKey c ≠ none → isUt c = false := fun c hk => by
    cases c <;> first | rfl | exact absurd rfl hk
  have hb : ∀ y, IsSlot th' y → Vs.VKey (capV m' y) ≠ none → IsSlot th y ∧ capV m' y = capV m y := by
    intro y hy hk
    rcases hE.gmem y (hmem hM' y hy hk) with hy0 | ⟨j, hj, rfl⟩
    · cases hu : isUt (capV m y)
      · exact ⟨((hM.members y).1 hy0).1, (hE.keep y hy0 hu).2⟩
      · have h1 := hE.utk y hy0 hu
        rw [hnu _ hk] at h1
        cases h1
    · exact (hk (by rw [hE.newc j hj]; exact hnk j hj)).elim
  refine ⟨fun y hy hk => ?_, fun y hy hk => ?_, fun y1 y2 hy1 hy2 hne hk hu => ?_⟩
  · have h1 := hE.keep y (hmem hM y hy hk) (hnu _ hk)
    exact ⟨y, ((hM'.members y).1 h1.1).1, by rw [h1.2], by rw [h1.2]⟩
  · obtain ⟨h1, h2⟩ := hb y hy hk
    exact ⟨y, h1, by rw [h2], by rw [h2]⟩
  · have hk1 := Vs.tabUn_key hu
    have hk2 : Vs.VKey (capV m' y2) ≠ none := by rw [← hk]; exact hk1
    obtain ⟨a1, b1⟩ := hb y1 hy1 hk1
    obtain ⟨a2, b2⟩ := hb y2 hy2 hk2
    exact ⟨y1, y2, a1, a2, hne, by rw [b1], by rw [b1], by rw [← b2, hk]⟩

/-- **`VsNamed` across a no-reset retype whose new caps may be keyed** (PML4 /
PDPT / PD / PT retypes; VsNamedPost's `stepShrGrow`): a new keyed cap is
unmapped with its table empty after (`hnew`); its key is the window address
(`RetExp.cbase`), so distinct from the other new caps' and, by `UtInv.noov`
at the source untyped cap, from every old keyed cap's (an old keyed cap is a
physical non-untyped cap off the free part `[p + fi, p + 2 ^ sb)`). -/
theorem _root_.Fl4Proofs.P3.Vs.VsNamed.retypeGrow {th : TypedHeap} {m m' : U64 → U64} {ksb : U64}
    {P L4 L3 L2 L1 : Set U64} {σ σ' : Fl4Spec.State Unit} {G G' : MdbGhost}
    {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hN : Vs.VsNamed th m ksb) (hS : Vs.VsSlotsW th P L4 L3 L2 L1 m)
    (hR : Vs.VsRel P m ksb σ) (hPt : Vs.PtRel L4 L3 L2 L1 m σ) (hPI : Vs.PoolsIn P L4 m)
    (hR' : Vs.VsRel P m' ksb σ') (hPt' : Vs.PtRel L4 L3 L2 L1 m' σ') (hsh : Vs.ArchShr σ σ')
    (hE : RetExp th th m m' G G' A k w dslot cj xs) (hM : MdbLinks th m G) (hM' : MdbLinks th m' G')
    (hU : UtInv m G) {p sb fi : U64} {d : Bool} (hxs : xs ∈ G.chains.flatten)
    (hcx : capV m xs = .Untyped p sb fi d) (hk : 0 < k) (hA1 : p.val + fi.val ≤ A)
    (hA2 : A + w * k ≤ p.val + 2 ^ sb.val)
    (hnew : ∀ j, j < w → ∀ kk q, Vs.VKey (cj j) = some (kk, q) → Vs.TabUn (cj j) ∧
      ∀ i : U64, i.val < (if kk = 4 then 256 else 512) → ¬ Vs.eP (m' (Vs.peA q i))) :
    Vs.VsNamed th m' ksb := by
  have hmem : ∀ {m0 : U64 → U64} {G0 : MdbGhost}, MdbLinks th m0 G0 → ∀ y, IsSlot th y →
      Vs.VKey (capV m0 y) ≠ none → y ∈ G0.chains.flatten := fun hM0 y hy hk =>
    (hM0.members y).2 ⟨hy, _, capAt_capV _ _, fun e => hk (by rw [e]; rfl)⟩
  have hnu : ∀ c : capability.Cap, Vs.VKey c ≠ none → isUt c = false := fun c hk => by
    cases c <;> first | rfl | exact absurd rfl hk
  have hoff : ∀ y, IsSlot th y → ∀ kk q, Vs.VKey (capV m y) = some (kk, q) →
      q.val < p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ q.val := by
    intro y hy kk q hkq
    have hyG := hmem hM y hy (by rw [hkq]; simp)
    obtain ⟨hp, -, hph, hut⟩ := Vs.vkey_tab hkq
    have hb : baseF (capV m y) = q.val := by unfold baseF; rw [hp]
    rcases hU.noov xs hxs p sb fi d hcx y hyG hph with h | ⟨h, -⟩
    · have hr := hU.reg y hyG hph
      unfold DisjR at h
      omega
    · rw [hut] at h; cases h
  have hnb : ∀ j, j < w → ∀ kk q, Vs.VKey (cj j) = some (kk, q) → q.val = A + j * k := by
    intro j hj kk q hkq
    have h := hE.cbase j hj
    unfold baseF at h; rw [(Vs.vkey_tab hkq).1] at h; exact h
  have hold : ∀ y, IsSlot th y → Vs.VKey (capV m y) ≠ none → capV m' y = capV m y := fun y hy hky =>
    (hE.keep y (hmem hM y hy hky) (hnu _ hky)).2
  have hback : ∀ y, IsSlot th y → Vs.VKey (capV m' y) ≠ none →
      capV m' y = capV m y ∨ ∃ j, j < w ∧ y = dslot j := by
    intro y hy hky
    rcases hE.gmem y (hmem hM' y hy hky) with hy0 | h
    · cases hu : isUt (capV m y)
      · exact .inl (hE.keep y hy0 hu).2
      · have h1 := hE.utk y hy0 hu
        rw [hnu _ hky] at h1; cases h1
    · exact .inr h
  refine hN.stepShrGrow hS hR hPt hPI hR' hPt' hsh (fun y hy => hy) hold (fun y hy hky => ?_)
  rcases hback y hy hky with hc | ⟨j, hj, rfl⟩
  · exact .inl ⟨hy, hc⟩
  right
  have hcj := hE.newc j hj
  obtain ⟨⟨kk, q⟩, hkq⟩ := Option.ne_none_iff_exists'.1 hky
  rw [hcj] at hkq
  obtain ⟨hu, hemp⟩ := hnew j hj kk q hkq
  have hqv := hnb j hj kk q hkq
  have hjk : j * k < w * k := Nat.mul_lt_mul_of_pos_right hj hk
  refine ⟨by rw [hcj]; exact hu, fun z hz hzne he => ?_, fun kk' q' hk' => ?_⟩
  · rw [hcj, hkq] at he
    rcases hback z hz (by rw [he]; simp) with hc | ⟨j', hj', rfl⟩
    · rw [hc] at he
      rcases hoff z hz kk q he with h | h <;> omega
    · rw [hE.newc j' hj'] at he
      have hqv' := hnb j' hj' kk q he
      have e : j' * k = j * k := by omega
      exact hzne (by rw [Nat.eq_of_mul_eq_mul_right hk e])
  · rw [hcj, hkq] at hk'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hk')
    exact hemp

/-- **The spec's object creation clears no entry** (`ArchShr`): old objects and
the ASID table kept. -/
theorem _root_.Fl4Proofs.P3.Vs.ArchShr.of_specAdd {σ σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop}
    {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject} (h : Sched.SpecAdd σ σ' W o) : Vs.ArchShr σ σ' :=
  Vs.ArchShr.of_keep (by have e := congrArg Fl4Spec.AbstractState.archState h.abs; exact congrArg (·.x64AsidTable) e)
    fun _ _ hp => (h.kold hp).trans hp.symm

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`VsNamed` across a no-reset retype with unkeyed new caps** (module
docstring): the relations after at the same VSpace sets, the spec step a
`SpecAdd` then a CNode step. -/
theorem XTopAt.vsNamedRet {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a : A}
    {σ σB σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) (hN : Vs.VsNamed Z.th (L.mem s) (L.ksb s))
    (hS : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s))
    (hR' : Vs.VsRel Z.P (L.mem s') (L.ksb s') σ') (hPt' : Vs.PtRel Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s') σ')
    (hks : L.ksb s' = L.ksb s)
    {th' : TypedHeap} {G G' : MdbGhost} {A0 k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hE : RetExp Z.th th' (L.mem s) (L.mem s') G G' A0 k w dslot cj xs) (hM : MdbLinks Z.th (L.mem s) G)
    (hM' : MdbLinks th' (L.mem s') G') (hnk : ∀ j, j < w → Vs.VKey (cj j) = none)
    {W : Fl4Spec.ObjRef → Prop} {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject}
    (hA : Sched.SpecAdd σ σB W o) (hcn : Ipc.CnK σB σ') (hkc : Ipc.KeepC σB σ') :
    Vs.VsNamed th' (L.mem s') (L.ksb s') := by
  have hsh : Vs.ArchShr σ σ' :=
    (Vs.ArchShr.of_specAdd hA).trans (Vs.ArchShr.of_objCn hcn.2 (ostep_of_cnk hcn hkc).2.2)
  rw [hks] at hR' ⊢
  exact hN.stepShr hS hX.fin.2.1 hX.fin.2.2.1 hX.fin.2.2.2.1 hR' hPt' (Vs.VsKeep.retype hE hM hM' hnk) hsh

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **(F1 stage 3) `VsNamed` at the drop's typed heap** (`JAtZ.drop`'s
`restrictTh`, same memory): the MDB's slots miss the region (`UtCapP3.ns`). -/
theorem _root_.Fl4Proofs.P3.JAtZ.vsNamedDrop (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hN : Vs.VsNamed Z.th (L.mem s) (L.ksb s)) {lo hi : Nat} (hNS : NoStraddle Z.th lo hi)
    (hns : ∀ a ∈ Z.G.chains.flatten, a.val < lo ∨ hi ≤ a.val) :
    Vs.VsNamed (restrictTh Z.th lo hi) (L.mem s) (L.ksb s) := by
  obtain ⟨hPl, ⟨-, -, hML, -, -⟩, -⟩ := J.xtop.rel
  refine hN.sub (fun y hy => hy.of_restrict) fun y hy hk => ?_
  have hne : capV (L.mem s) y ≠ .Null := fun h => hk (by rw [h]; rfl)
  have hyG : y ∈ Z.G.chains.flatten := (hML.members y).2 ⟨hy, _, capAt_capV _ _, hne⟩
  exact hy.restrict hPl hNS (hns y hyG)

end

end

end Fl4Proofs.P3
