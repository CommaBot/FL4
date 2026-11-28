/-
P3 (DESIGN.md §9), untyped: **the untyped caps' facts after a TCB retype**
(handoff/utj.md "uttypes", ut39; l4v `valid_untyped` / `untyped_inc` across
`retype_region` of `TCBObject`s).

* `head_off_childless`: an address in the source's free part lies in no
  other childless RAM untyped cap's region (`UtInv.drange`: the two caps'
  ranges are disjoint, or one descends from the other; a descendant of the
  source lies below its free index, `UtInv.inc`; an ancestor has a child);
* `JAtZ.ret_utcT`: UtPmKeep's `ret_utcW` with the extra writes off the
  source's free part and core 0's debug-list head possibly changed, to an
  address off every childless RAM untyped region but the source's.
-/
import Fl4Proofs.P3.UtPmKeep
import Fl4Proofs.P3.NoChildren
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- **An address of the source's free part is in no other childless RAM
untyped region** (module docstring). -/
theorem head_off_childless {th : TypedHeap} {mem : U64 → U64} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hP : Placed th) (hM : MdbLinks th mem G) (hC : CdtRel th mem σ G) (hU : UtInv mem G)
    {xs : Fl4Spec.CslotPtr} {p0 sb0 fi0 : U64} (hxsG : cslotAddr xs ∈ G.chains.flatten)
    (hc0 : capV mem (cslotAddr xs) = .Untyped p0 sb0 fi0 false)
    {sl : Fl4Spec.CslotPtr} (hsl : AbsSlot th sl) (hne : cslotAddr sl ≠ cslotAddr xs) {p sb fi : U64}
    (hcv : capV mem (cslotAddr sl) = .Untyped p sb fi false) (hnc : ¬ ∃ x, σ.cdt x = some sl)
    {v : Nat} (hv1 : p0.val + fi0.val ≤ v) (hv2 : v < p0.val + 2 ^ sb0.val) :
    ¬ (p.val ≤ v ∧ v < p.val + 2 ^ sb.val) := by
  have hslG : cslotAddr sl ∈ G.chains.flatten :=
    (hM.members _).2 ⟨hsl.isSlot, _, by rw [capAt_capV, hcv], by simp⟩
  have hph : physF (capV mem (cslotAddr sl)) = true := by rw [hcv]; exact physF_ut _ _ _ _
  have r1 := hU.reg _ hslG hph
  have r0 := hU.reg _ hxsG (by rw [hc0]; exact physF_ut _ _ _ _)
  rw [hcv] at r1
  rw [hc0] at r0
  obtain ⟨b1, t1, -⟩ := ut_range (capV_ut_sb hcv) r1
  obtain ⟨b0, t0, -⟩ := ut_range (capV_ut_sb hc0) r0
  rintro ⟨g1, g2⟩
  by_cases hd : Disj (capV mem (cslotAddr sl)) (capV mem (cslotAddr xs))
  · rw [hcv, hc0] at hd
    unfold Disj at hd
    rw [b1, t1, b0, t0] at hd
    have := hU.fib _ hxsG _ _ _ _ hc0
    omega
  · rcases hU.drange _ hxsG p0 sb0 fi0 false hc0 _ hslG hne hph hd with h | h
    · obtain ⟨-, i1, i2⟩ := hU.inc _ hxsG p0 sb0 fi0 false hc0 _ h
      rw [hcv, b1] at i1
      rw [hcv, t1] at i2
      have : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow
      omega
    · obtain ⟨b, -, hb⟩ := Relation.TransGen.tail'_iff.1 h
      exact hnc ((hC.has_child_iff hP hsl).2 ⟨b, hb⟩)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- `ret_utcT` over `JAtZB` (mmuAD gen 42b25, in place; `JAtZ.ret_utcT` is its corollary). -/
theorem JAtZB.ret_utcT {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost}
    {xs : Fl4Spec.CslotPtr} {p0 sb0 fi0 fi1 : U64} (hxs : AbsSlot Z.th xs)
    (hc0 : capV (L.mem s) (cslotAddr xs) = .Untyped p0 sb0 fi0 false)
    (hc1 : capV (L.mem s') (cslotAddr xs) = .Untyped p0 sb0 fi1 false) (hfi : fi0.val ≤ fi1.val)
    (hfi1 : fi1.val ≤ 2 ^ sb0.val) (Dst : Fl4Spec.CslotPtr → Prop)
    (hDa : ∀ d, Dst d → AbsSlot Z.th d) (hDn : ∀ d, Dst d → capAt (L.mem s) (cslotAddr d) = ok .Null)
    (hDu : ∀ d, Dst d → ∀ p sb fi dv, capV (L.mem s') (cslotAddr d) ≠ .Untyped p sb fi dv)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr xs → (∀ d, Dst d → y ≠ cslotAddr d) →
      capV (L.mem s') y = capV (L.mem s) y)
    {Win : U64 → Prop} (hw : P1.WritesIn st s s' (fun b => InSlot Z.th b ∨ Win b))
    (hWs : ∀ b, Win b → b.val < p0.val + fi1.val ∨ p0.val + 2 ^ sb0.val ≤ b.val)
    (hWo : ∀ sl p sb fi, AbsSlot Z.th sl → cslotAddr sl ≠ cslotAddr xs →
      capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi false → ∀ b, Win b → b.val < p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ b.val)
    (hhd : ∀ sl p sb fi, AbsSlot Z.th sl → cslotAddr sl ≠ cslotAddr xs →
      capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi false → (¬ ∃ x, σ.cdt x = some sl) →
      ¬ (p.val ≤ (L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
        (L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val)) (hcdt : ∀ x, ¬ Dst x → σ'.cdt x = σ.cdt x)
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
      fun _ h0 => absurd hchild h0,
      fun _ => by rw [hna]; exact U.dwReg B0, fun _ => by rw [hgp]; exact U.gReg B0⟩
    · rw [hw.mem_eq hal fun h => h.elim (fun ⟨y, hy, h1', h2'⟩ => by rcases hobj y hy with e | e <;> omega)
        (fun h => by have := hWs w h; omega)]
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
    U.nostr, fun y hy => ?_, fun h0 y hy => ?_, 
    fun g h0 hf0 => ?_, fun g => by rw [hna]; exact U.dwReg (B g), fun g => by rw [hgp]; exact U.gReg (B g)⟩
  · rw [hw.mem_eq hal fun h => h.elim (fun ⟨y, hy, h1', h2'⟩ => by rcases hobj y hy with e | e <;> omega)
      (fun h => by
        have hdv : dev = false := hdF
        subst hdv
        rcases hWo sl p sb fi hsl hsx hcv w h with e | e <;> omega)]
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
    refine ⟨fun sl' h => ?_, by
      rw [hna]
      have hdF' : dev = false := hdF
      subst hdF'
      exact hhd sl p sb fi hsl hsx hcv hnc⟩
    by_cases e : Dst sl'
    · exact (hlv sl' e sl p sb fi dev hsl hcv hdF hnc).2
    · exact r1 sl' (by rw [← horig sl' e]; exact h)


/-- **`JAtZ.ret_utcW` for a TCB retype**: the extra words `Win` off the
source's free part (not only below its new free index), core 0's debug-list
head word possibly changed (to a new TCB), off every childless RAM untyped
region but the source's (`hhd`). Docstring of `ret_utcW`: **The untyped caps' facts after a retype that keeps the typed heap**
(`JAtZ.ret_utc` with FL4 also writing the window `Win`, below the source's new free index and off
every other RAM untyped cap's free part and the debug word; `ins_utcG` for the
creation's insertions `Dst` and the source's free index raised from `fi0`
to `fi1`): the source keeps its facts at the higher free index (its free
part shrinks; it has a child after, `hchild`); every other untyped cap keeps
them as in `ins_utcG` (the new MDB slots miss every childless untyped
region, `hlv`, from the destination's liveness). -/
theorem JAtZ.ret_utcT {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
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
    {Win : U64 → Prop} (hw : P1.WritesIn st s s' (fun b => InSlot Z.th b ∨ Win b))
    (hWs : ∀ b, Win b → b.val < p0.val + fi1.val ∨ p0.val + 2 ^ sb0.val ≤ b.val)
    (hWo : ∀ sl p sb fi, AbsSlot Z.th sl → cslotAddr sl ≠ cslotAddr xs →
      capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi false → ∀ b, Win b → b.val < p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ b.val)
    (hhd : ∀ sl p sb fi, AbsSlot Z.th sl → cslotAddr sl ≠ cslotAddr xs →
      capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi false → (¬ ∃ x, σ.cdt x = some sl) →
      ¬ (p.val ≤ (L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
        (L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val)) (hcdt : ∀ x, ¬ Dst x → σ'.cdt x = σ.cdt x)
    (horig : ∀ sl, ¬ Dst sl → σ'.isOriginalCap sl = σ.isOriginalCap sl)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hM' : MdbLinks Z.th (L.mem s') G') (hchild : ∃ x, σ'.cdt x = some xs)
    (hlv : ∀ d, Dst d → ∀ sl p sb fi dev, AbsSlot Z.th sl → capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev →
      dev = false → (¬ ∃ x, σ.cdt x = some sl) →
      ((cslotAddr d).val < p.val ∨ p.val + 2 ^ sb.val ≤ (cslotAddr d).val) ∧
        AbsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) d) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s' σ' G' sl p sb fi :=
  JAtZB.ret_utcT J.toB hxs hc0 hc1 hfi hfi1 Dst hDa hDn hDu hcap hw hWs hWo hhd hcdt horig hgp hM' hchild hlv

end

end

end Fl4Proofs.P3
