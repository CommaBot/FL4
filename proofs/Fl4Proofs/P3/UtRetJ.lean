/-
P3 (DESIGN.md §9), untyped: **`JAtZ`'s CSpace fields after a retype**
(`JCs` at the sets of the retype's outcome, handoff/utj.md "Round 4").

* `DelInv.retype`: `DelInv` after a retype from `DelInv` before and the
  retype's `RetExp`: a zombie after is a kept non-untyped cap (the new caps
  are no zombies, untyped caps stay untyped), and the empty slots keep clear
  links (`RetExp.nclr`: the creation loop writes no link word of a slot it
  leaves empty; the new objects' slots are zero memory).
* `JCs.retype`: the four `JCs` fields after a retype.
* `RetExp.src_desc`, `RetExp.src_child`: the source cap has a child after.
* `RetExp.cap_keep`: a slot neither the source nor a new cap's keeps its cap.
* `JAtZ.ret_utc`: `JRest.utc` after a retype keeping the typed heap (the
  source at its raised free index; the other RAM caps as `ins_utcG`, with a
  set of new MDB slots).
-/
import Fl4Proofs.P3.UtEpSets
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- **`DelInv` across a retype** (module docstring). `hZ`: the old zombies'
objects are kept in the typed heap after. -/
theorem DelInv.retype {th th' : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost} {A k w : Nat}
    {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64} (hD : DelInv th m)
    (hE : RetExp th th' m m' G G' A k w dslot cj xs) (hM : MdbLinks th m G) (hM' : MdbLinks th' m' G')
    (hcj : ∀ j, j < w → ∀ p zt n, cj j ≠ .Zombie p zt n)
    (hZ : ∀ p zt n, ZOK th p zt n → ZOK th' p zt n) : DelInv th' m' := by
  -- a zombie after is the same zombie before, in an old slot
  have back : ∀ y, IsSlot th' y → ∀ p zt n, capV m' y = .Zombie p zt n →
      IsSlot th y ∧ capV m y = .Zombie p zt n := by
    intro y hy p zt n hz
    have hm : y ∈ G'.chains.flatten := (hM'.members y).2 ⟨hy, _, capAt_capV _ _, by rw [hz]; simp⟩
    rcases hE.gmem y hm with hy0 | ⟨j, hj, rfl⟩
    · refine ⟨((hM.members y).1 hy0).1, ?_⟩
      cases hu : isUt (capV m y)
      · rw [← (hE.keep y hy0 hu).2]; exact hz
      · have := hE.utk y hy0 hu; rw [hz] at this; cases this
    · exact absurd ((hE.newc j hj).symm.trans hz) (hcj j hj p zt n)
  refine ⟨fun y hy p zt n hz => ?_, fun y y' hy hy' hne p zt n p' zt' n' hz hz' => ?_, hE.nclr hD.nc⟩
  · obtain ⟨h1, h2⟩ := back y hy p zt n hz
    exact hZ p zt n (hD.zwf y h1 p zt n h2)
  · obtain ⟨h1, h2⟩ := back y hy p zt n hz
    obtain ⟨h1', h2'⟩ := back y' hy' p' zt' n' hz'
    exact hD.zu y y' h1 h1' hne p zt n p' zt' n' h2 h2'

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`JCs` after a retype**: `DelInv` by `DelInv.retype`, the untyped
invariant, finality (for any ghost of the links, `FinM.of_links`) and
`SpecFree` after (`SpecFree.retype`) at the sets with the retype's typed
heap and ghost. -/
theorem JCs.retype {Z' : XSets} {s' : S} {σ' : Fl4Spec.State Unit} {th th' : TypedHeap} {m : U64 → U64}
    {G G' : MdbGhost} {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hth : Z'.th = th') (hG : Z'.G = G') (hD : DelInv th m)
    (hE : RetExp th th' m (L.mem s') G G' A k w dslot cj xs) (hM : MdbLinks th m G) (hP' : Placed th')
    (hM' : MdbLinks th' (L.mem s') G') (hcj : ∀ j, j < w → ∀ p zt n, cj j ≠ .Zombie p zt n)
    (hZ : ∀ p zt n, ZOK th p zt n → ZOK th' p zt n) (hU' : UtInv (L.mem s') G') (hFM : FinM (L.mem s') G')
    (hSF : SpecFree (L.mem s') G' σ') : JCs (L := L) Z' s' σ' := by
  subst hth hG
  exact ⟨hD.retype hE hM hM' hcj hZ, hU', fun G2 h2 => FinM.of_links hP' hM' h2 hFM, hSF⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- The source cap of a retype has a child after it (the first new cap's
slot), `RetExp.desc`. -/
theorem RetExp.src_desc {th th' : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost} {A k w : Nat}
    {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hE : RetExp th th' m m' G G' A k w dslot cj xs) (hw : 0 < w) : Mdb.Desc G'.par (dslot 0) xs :=
  (hE.desc _ _).2 (Or.inr ⟨0, hw, rfl, Or.inl rfl⟩)

/-- The source cap's slot has a CDT child after a retype (`RetExp.src_desc`
with `CdtRel` after): `UtCapP3`'s childless clauses do not apply to it. -/
theorem RetExp.src_child {th th' : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost} {A k w : Nat}
    {dslot : Nat → U64} {cj : Nat → capability.Cap} {sl : Fl4Spec.CslotPtr} {σ' : Fl4Spec.State Unit}
    (hE : RetExp th th' m m' G G' A k w dslot cj (cslotAddr sl)) (hw : 0 < w) (hP' : Placed th')
    (hC' : CdtRel th' m' σ' G') (hsl : AbsSlot th' sl) : ∃ x, σ'.cdt x = some sl :=
  (hC'.has_child_iff hP' hsl).2 (desc_tail_child (hE.src_desc hw))

/-- **A slot that is neither the source nor a new cap's keeps its cap**
across a retype (`RetExp`'s `keep`, `usrc`, `gmem`; an empty slot stays
empty: it is in neither tree). -/
theorem RetExp.cap_keep {th th' : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost} {A k w : Nat}
    {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hE : RetExp th th' m m' G G' A k w dslot cj xs) (hM : MdbLinks th m G) (hM' : MdbLinks th' m' G')
    {y : U64} (hy : IsSlot th y) (hy' : IsSlot th' y) (hyx : y ≠ xs) (hyd : ∀ j, j < w → y ≠ dslot j) :
    capV m' y = capV m y := by
  by_cases hyG : y ∈ G.chains.flatten
  · cases hu : isUt (capV m y)
    · exact (hE.keep y hyG hu).2
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h5⟩ := hE.usrc
      exact h5 y hyG hu hyx
  · have h0 : capV m y = .Null := by
      by_contra hn
      exact hyG ((hM.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩)
    have hyG' : y ∉ G'.chains.flatten := fun h => by
      rcases hE.gmem y h with h1 | ⟨j, hj, e⟩
      · exact hyG h1
      · exact hyd j hj e
    rw [h0]
    by_contra hn
    exact hyG' ((hM'.members y).2 ⟨hy', _, capAt_capV _ _, hn⟩)

set_option maxHeartbeats 4000000 in
/-- **The untyped caps' facts after a retype that keeps the typed heap**
(the endpoints'/notifications' retype without a reset; `ins_utcG` for the
creation's insertions `Dst` and the source's free index raised from `fi0`
to `fi1`): the source keeps its facts at the higher free index (its free
part shrinks; it has a child after, `hchild`); every other untyped cap keeps
them as in `ins_utcG` (the new MDB slots miss every childless untyped
region, `hlv`, from the destination's liveness). -/
theorem JAtZ.ret_utc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost}
    {xs : Fl4Spec.CslotPtr} {p0 sb0 fi0 fi1 : U64} (hxs : AbsSlot Z.th xs)
    (hc0 : capV (L.mem s) (cslotAddr xs) = .Untyped p0 sb0 fi0 false)
    (hc1 : capV (L.mem s') (cslotAddr xs) = .Untyped p0 sb0 fi1 false) (hfi : fi0.val ≤ fi1.val)
    (hfi1 : fi1.val ≤ 2 ^ sb0.val) (Dst : Fl4Spec.CslotPtr → Prop)
    (hDa : ∀ d, Dst d → AbsSlot Z.th d) (hDn : ∀ d, Dst d → capAt (L.mem s) (cslotAddr d) = ok .Null)
    (hDu : ∀ d, Dst d → ∀ p sb fi dv, capV (L.mem s') (cslotAddr d) ≠ .Untyped p sb fi dv)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr xs → (∀ d, Dst d → y ≠ cslotAddr d) →
      capV (L.mem s') y = capV (L.mem s) y)
    (hw : P1.WritesIn st s s' (InSlot Z.th)) (hcdt : ∀ x, ¬ Dst x → σ'.cdt x = σ.cdt x)
    (horig : ∀ sl, ¬ Dst sl → σ'.isOriginalCap sl = σ.isOriginalCap sl)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hM' : MdbLinks Z.th (L.mem s') G') (hchild : ∃ x, σ'.cdt x = some xs)
    (hlv : ∀ d, Dst d → ∀ sl p sb fi dev, AbsSlot Z.th sl → capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev →
      dev = false → (¬ ∃ x, σ.cdt x = some sl) →
      ((cslotAddr d).val < p.val ∨ p.val + 2 ^ sb.val ≤ (cslotAddr d).val) ∧
        AbsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) d) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s' σ' G' sl p sb fi := by
  intro sl p sb fi dev hsl hcap' hdF
  obtain ⟨hP, ⟨-, hV, hM, hC, hI⟩, -⟩ := J.xtop.rel
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  -- a slot misses the free part of a cap with the facts `U`
  have hobjU : ∀ {sl1 : Fl4Spec.CslotPtr} {p1 sb1 fi1' : U64}, UtCapP3 (L := L) arI Z.th s σ Z.G sl1 p1 sb1 fi1' →
      ∀ y, IsSlot Z.th y → y.val + 32 ≤ p1.val + fi1'.val ∨ p1.val + 2 ^ sb1.val ≤ y.val := by
    intro sl1 p1 sb1 fi1' U y hy
    obtain ⟨q, i, hi, rfl⟩ := hy
    obtain ⟨k, hk, hs⟩ := hi.size
    have hv := hi.val hP
    rcases U.free q k hk with e | e <;> omega
  by_cases hsx : cslotAddr sl = cslotAddr xs
  · -- the source: its free index raised
    have e := cslotAddr_inj hP hsl hxs hsx
    subst e
    have hcv := capV_of_capAt hcap'
    rw [hc1] at hcv
    injection hcv with e1 e2 e3 e4
    rw [← e1, ← e2, ← e3]
    have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p0 sb0 fi0 false) := by rw [capAt_capV, hc0]
    have U := J.utc sl p0 sb0 fi0 false hsl hcap0 rfl
    have B0 : NotDev (L.mem s) (cslotAddr sl) p0 sb0 fi0 := by unfold NotDev; rw [hc0]; simp
    have hobj := hobjU U
    refine ⟨U.pal, U.pfit, hfi1, fun _ => U.high B0, fun _ => by rw [hcpu, hna]; exact U.actZ B0,
      fun q k hq => (U.free q k hq).imp (fun e => by omega) id,
      fun _ w hal h1 h2 => ?_, U.sb4, U.nostr, fun y hy => ?_, fun h0 => absurd hchild h0,
      fun k0 v0 => by simpa only [hna] using U.pp k0 v0, fun _ h0 => absurd hchild h0,
      fun _ => by rw [hna]; exact U.dwReg B0, fun _ => by rw [hgp]; exact U.gReg B0⟩
    · rw [hw.mem_eq hal fun ⟨y, hy, h1', h2'⟩ => by rcases hobj y hy with e | e <;> omega]
      exact U.zero B0 w hal (by omega) h2
    · have := hobj y ((hM'.members y).1 hy).1
      omega
  -- another untyped cap: unchanged
  have hnd : ∀ d, Dst d → cslotAddr sl ≠ cslotAddr d := fun d hd e =>
    hDu d hd p sb fi dev (by rw [← e]; exact capV_of_capAt hcap')
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hcap _ hsl.isSlot hsx hnd]; exact capV_of_capAt hcap'
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0 hdF
  have hobj := hobjU U
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  have hdnm : ∀ d, Dst d → cslotAddr d ∉ Z.G.chains.flatten := fun d hd h => by
    obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hDn d hd] at h0; exact hn (eq_of_ok_eq h0).symm
  have hnc' : (¬ ∃ x, σ'.cdt x = some sl) → ¬ ∃ x, σ.cdt x = some sl := by
    rintro h0 ⟨x, hx⟩
    apply h0
    by_cases e : Dst x
    · exfalso
      have h1 := hC.cdt _ (hDa x e)
      rw [hx] at h1
      exact hdnm x e (hM.tree.par_mem _ _ h1.symm).1
    · exact ⟨x, by rw [hcdt x e]; exact hx⟩
  have B := notDev_back (capV_of_capAt hcap') hcv
  have hxsG : cslotAddr xs ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hxs.isSlot, _, by rw [capAt_capV, hc0], by simp⟩
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free,
    fun g w hal h1 h2 => ?_, U.sb4,
    U.nostr, fun y hy => ?_, fun h0 y hy => ?_, fun k0 v0 => by simpa only [hna] using U.pp k0 v0,
    fun g h0 hf0 => ?_, fun g => by rw [hna]; exact U.dwReg (B g), fun g => by rw [hgp]; exact U.gReg (B g)⟩
  · rw [hw.mem_eq hal fun ⟨y, hy, h1', h2'⟩ => by rcases hobj y hy with e | e <;> omega]
    exact U.zero (B g) w hal h1 h2
  · have := hobj y ((hM'.members y).1 hy).1
    omega
  · have hnc := hnc' h0
    by_cases ed : ∃ d, Dst d ∧ y = cslotAddr d
    · obtain ⟨d, hd, rfl⟩ := ed
      exact (hlv d hd sl p sb fi dev hsl hcv hdF hnc).1
    · by_cases ex : y = cslotAddr xs
      · subst ex; exact U.ns hnc _ hxsG
      · obtain ⟨hys, c0, h0', hn⟩ := (hM'.members y).1 hy
        have hc0' : capAt (L.mem s) y = ok c0 := by
          rw [capAt_capV, ← hcap y hys ex (fun d hd e => ed ⟨d, hd, e⟩), ← capAt_capV]; exact h0'
        exact U.ns hnc y ((hM.members y).2 ⟨hys, c0, hc0', hn⟩)
  · have hnc := hnc' h0
    obtain ⟨r1, r3⟩ := U.rst (B g) hnc hf0
    refine ⟨fun sl' h => ?_, by rw [hna, hDbg]; exact r3⟩
    by_cases e : Dst sl'
    · exact (hlv sl' e sl p sb fi dev hsl hcv hdF hnc).2
    · exact r1 sl' (by rw [← horig sl' e]; exact h)

end

end

end Fl4Proofs.P3
