/-
P3x for virtualization (line virt, gen 19, item 2, loop step): **one step of `create_new_objects`' loop for any cap
family** — P3/UntypedLoop's `loop_step` with the cap family `cj` and the spec type `t` as parameters and the
facts `loop_step` derived from `newCapOf` taken as hypotheses (no `newCapOf`, no `objTypeOf`, any object size `k`).

* **`loop_stepC`**: from `LoopInv … cj s i`, `insert_new_cap` of `cj i` into the `i`-th window slot gives
  `LoopInv … cj s' (i + 1)`. The cap facts, each for `i < win`: `baseF (cj i) = A + i·k`, `topF (cj i) = A + i·k
  + k - 1`, `isUt (cj i) = false`, `CapRel (cj i) (defaultCap t (A + i·k) bits dev)`, `EncWf`, `NewKindV`
  (P3/VirtNewKindV: the VCPU cap included), `physF = true`, `CapValid th'`. These are parameters of the
  statement (facts of the instantiating cap family), not premises.
* The same with `insert_new_cap`'s footprint is `loop_stepC_frame` (P3/VirtLoopFrame).

Proof: `loop_step`'s, with those facts in place of `newCap_range` / `isUt_newCap` / `newCap_rel` /
`newCap_encWf` / `newKind_newCap` / `physF_newCap` / `newCap_ne_null`, and `insert_new_fullV` / `fresh_newV`.
(`isUt (cj i) = false` makes `insert_new_full`'s `hsame` vacuous: the untyped arm of the native loop is not covered
here; the native loop keeps `loop_step`.)

No named premise. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtNewKindV
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **One step of the loop for a cap family `cj`** (module docstring). -/
theorem loop_stepC (th' : TypedHeap) (hP' : Placed th') {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (t : Fl4Spec.ApiObjectType) (bits : Nat) (dev : Bool) (cj : Nat → capability.Cap)
    (off win A k : Nat) (hk1 : 1 ≤ k) (hwin : off + win ≤ 2 ^ r)
    (hfit : A + win * k ≤ 2 ^ 64)
    (hpA : p.val ≤ A) (hAp : A + win * k ≤ p.val + 2 ^ sb.val)
    (hcbF : ∀ i, i < win → baseF (cj i) = A + i * k) (hctF : ∀ i, i < win → topF (cj i) = A + i * k + k - 1)
    (hcuF : ∀ i, i < win → isUt (cj i) = false)
    (hcaF : ∀ i, i < win → CapRel (cj i) (Fl4Spec.defaultCap t (BitVec.ofNat 64 (A + i * k)) bits dev))
    (hceF : ∀ i, i < win → EncWf (cj i)) (hcnF : ∀ i, i < win → NewKindV (cj i))
    (hcpF : ∀ i, i < win → physF (cj i) = true)
    (hnewcv : ∀ i, i < win → CapValid th' (cj i))
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < win → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off + j)))
    (s : S) (i : Nat) (hi : i < win)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t bits (pp.bv, idx) dev)
      ((windowSlots dest r off win).zip (regionPtrs (BitVec.ofNat 64 A) win k))
      A k win (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off + j))) zlo zhi G0 m0 cj s i) :
    cdt.insert_new_cap st s (cslotAddr (pp.bv, idx)) (slotAddr dest.bv (BitVec.ofNat 64 (off + i))) (cj i) ⦃ s' =>
    LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t bits (pp.bv, idx) dev)
      ((windowSlots dest r off win).zip (regionPtrs (BitVec.ofNat 64 A) win k))
      A k win (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off + j))) zlo zhi G0 m0 cj s' (i + 1) ⦄ := by
  obtain ⟨σi, Gi, hchain, hR, hV, hM, hC, hI, hsrc, hnull, hno, hdd, hzr, hT1, hT1b, hT2a, hT2b, hT3, hFM,
    hCh, hRv, hNK⟩ := hinv
  have hik : (i + 1) * k ≤ win * k := Nat.mul_le_mul_right _ hi
  rw [Nat.add_mul, Nat.one_mul] at hik
  set bi : U64 := ⟨BitVec.ofNat 64 (A + i * k)⟩ with hbi
  have hbiv : bi.val = A + i * k := by
    show (BitVec.ofNat 64 (A + i * k)).toNat = _; simp; omega
  set c := cj i with hcdef
  have hcb : baseF c = A + i * k := hcbF i hi
  have hct : topF c = A + i * k + k - 1 := hctF i hi
  -- the destination slot
  have hoff : off + i < 2 ^ r := by omega
  have hdsl : slotAddr dest.bv (BitVec.ofNat 64 (off + i)) = cslotAddr (dest.bv, Fl4Spec.natToCref r (off + i)) :=
    (cslotAddr_natToCref _ _ _ hr hoff).symm
  rw [hdsl]
  obtain ⟨hsb', hst'⟩ := topF_ut p sb fi d hsb hpfit
  have hsrcC := hsrc
  have hut : isUt (capability.Cap.Untyped p sb fi d) = true := rfl
  have hdnull := hnull i (le_refl _) hi
  simp only at hdnull
  rw [hdsl] at hdnull
  have hno' : ∀ x ∈ Gi.chains.flatten, physF (capV (L.mem s) x) = true →
      Disj (capV (L.mem s) x) c ∨ (isUt (capV (L.mem s) x) = true ∧ Within (.Untyped p sb fi d) (capV (L.mem s) x)) := by
    intro x hx hp
    rcases (hno x hx hp).2 with h | h
    · left; unfold DisjR at h; unfold Disj; rw [hcb, hct]; omega
    · exact Or.inr h
  have hdd' : ∀ y, Mdb.Desc Gi.par y (cslotAddr (pp.bv, idx)) → Disj (capV (L.mem s) y) c := by
    intro y hy
    have h := hdd y hy
    unfold DisjR at h; unfold Disj; rw [hcb, hct]; omega
  have hcin : Within c (.Untyped p sb fi d) := by
    unfold Within; rw [hcb, hct, hsb', hst']; omega
  have hsame : isUt c = true → Within (.Untyped p sb fi d) c → shape c = shape (.Untyped p sb fi d) := by
    intro hu; rw [hcuF i hi] at hu; cases hu
  have hreg : ∀ x ∈ Gi.chains.flatten, physF (capV (L.mem s) x) = true →
      baseF (capV (L.mem s) x) ≤ topF (capV (L.mem s) x) := fun x hx hp => (hno x hx hp).1
  have hca := hcaF i hi
  have he : EncWf c := hceF i hi
  have hAd0 : AbsSlot th' (dest.bv, Fl4Spec.natToCref r (off + i)) :=
    ⟨dest, rfl, Or.inl (by rw [natToCref_length _ _ hr]; exact hdest)⟩
  have hAs0 : AbsSlot th' (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hnx0 : nextOf (L.mem s) (cslotAddr (pp.bv, idx)) = 0#u64 ∨ IsSlot th' (nextOf (L.mem s) (cslotAddr (pp.bv, idx))) := by
    have hsm : cslotAddr (pp.bv, idx) ∈ Gi.chains.flatten := (hM.members _).2 ⟨hAs0.isSlot, _, hsrcC, by simp⟩
    rcases hM.next_mem hsm with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ((hM.members _).1 h).1
  obtain ⟨s', hs', hfull⟩ := spec_exists (insert_new_fullV th' s σi Gi hR hV hP' hM hC hI hpp hdest hidx
    (natToCref_length _ _ hr) hsrcC hut hdnull c _ hca (hnewcv i hi) he (hcnF i hi)
    (hcpF i hi) (by rw [hcb, hct]; omega) hcin hreg hno' hdd' hsame)
  obtain ⟨s'', hs'', hfr⟩ := spec_exists (insert_new_frame (L := L) hP' s c _ _ hAs0.isSlot hAd0.isSlot hnx0)
  rw [hs'] at hs''; have := eq_of_ok_eq hs''; subst this
  rw [hs', WP.spec_ok]
  obtain ⟨σ', h1, hR', hV', hM', hC', hI', hW⟩ := hfull
  set src := cslotAddr (pp.bv, idx)
  set dsl := cslotAddr (dest.bv, Fl4Spec.natToCref r (off + i))
  have hAd : AbsSlot th' (dest.bv, Fl4Spec.natToCref r (off + i)) :=
    ⟨dest, rfl, Or.inl (by rw [natToCref_length _ _ hr]; exact hdest)⟩
  have hd : IsSlot th' dsl := hAd.isSlot
  have hAs : AbsSlot th' (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hs : IsSlot th' src := hAs.isSlot
  have hsd : src ≠ dsl := by
    intro e; rw [e, hdnull] at hsrcC; cases eq_of_ok_eq hsrcC
  have hdestm : dsl ∉ Gi.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn0⟩ := (hM.members dsl).1 h
    rw [hdnull] at h0; exact hn0 (eq_of_ok_eq h0).symm
  have hcapW : ∀ x, IsSlot th' x → capAt (L.mem s') x = if x = dsl then ok c else capAt (L.mem s) x :=
    fun x hx => hW.capAt' hx he
  have hcapV : ∀ x, IsSlot th' x → x ≠ dsl → capV (L.mem s') x = capV (L.mem s) x := by
    intro x hx hne
    have := hcapW x hx; rw [if_neg hne, capAt_capV, capAt_capV] at this; exact eq_of_ok_eq this
  have hcapD : capV (L.mem s') dsl = c := by
    have := hcapW dsl hd; rw [if_pos rfl, capAt_capV] at this; exact eq_of_ok_eq this
  have hslot : ∀ x, x ∈ Gi.chains.flatten → IsSlot th' x := fun x h => ((hM.members x).1 h).1
  have hNK' : NullKeep th' m0 (L.mem s') :=
    hNK.trans (NullKeep.ins hP' hM hW ((hM.members src).2 ⟨hs, _, hsrcC, by simp⟩) hd hdestm
      (hcnF i hi).ne_null he)
  refine ⟨σ', insG Gi src dsl true, ?_, hR', hV', hM', hC', hI', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun ch hch => ?_, fun x hx => ?_, hNK'⟩
  rotate_right
  · -- the revocable bits of the old slots
    have hx' := hT1b x hx
    rw [hW.revOf' (hslot x hx'), if_neg (fun (e : x = dsl) => hdestm (e ▸ hx'))]; exact hRv x hx
  rotate_right
  · -- the chains grow
    obtain ⟨ch1, hch1, hs1⟩ := hCh ch hch
    obtain ⟨ch2, hch2, hs2⟩ := insG_chains_sub Gi src dsl true ch1 hch1
    exact ⟨ch2, hch2, fun z hz => hs2 z (hs1 z hz)⟩
  rotate_right
  · -- finality: the new cap is fresh
    intro h0
    have hsrcm : src ∈ Gi.chains.flatten := (hM.members src).2 ⟨hs, _, hsrcC, by simp⟩
    refine (hFM h0).fresh_ins hsrcm hdestm true hM'.tree.nodup
      (fun z hz => hcapV z (hslot z hz) (fun e => hdestm (e ▸ hz))) (fun w hw => ?_)
    rw [hcapD, hcapV w (hslot w hw) (fun e => hdestm (e ▸ hw))]
    exact fresh_newV (hcnF i hi) (by rw [hcb, hct]; omega)
      (fun hp => ⟨hreg w hw hp, (hno' w hw hp).imp id (·.1)⟩)
  · -- the spec's loop
    intro σf hf
    apply hchain σf
    have hlen : i < ((windowSlots dest r off win).zip (regionPtrs (BitVec.ofNat 64 A) win k)).length := by
      simp [windowSlots, regionPtrs]; exact hi
    rw [List.drop_eq_getElem_cons hlen]
    have hget : ((windowSlots dest r off win).zip (regionPtrs (BitVec.ofNat 64 A) win k))[i] =
        ((dest.bv, Fl4Spec.natToCref r (off + i)), bi.bv) := by
      simp only [List.getElem_zip, windowSlots, regionPtrs, List.getElem_map, List.getElem_range,
        List.getElem_range']
      congr 1
      · simp
      show Fl4Spec.ptrAdd (BitVec.ofNat 64 A) (i * k) = BitVec.ofNat 64 (A + i * k)
      simp [Fl4Spec.ptrAdd, BitVec.ofNat_add]
    rw [hget, mapMx_cons_one (createCap_eq t bits (pp.bv, idx) _ dev bi.bv σi σ' h1)]
    exact hf
  · have := hcapW src hs; rw [if_neg hsd] at this; rw [this]; exact hsrcC
  · intro j hj1 hj2
    have hj : off + j < 2 ^ r := by omega
    have hdj : slotAddr dest.bv (BitVec.ofNat 64 (off + j)) = cslotAddr (dest.bv, Fl4Spec.natToCref r (off + j)) :=
      (cslotAddr_natToCref _ _ _ hr hj).symm
    have hAj : AbsSlot th' (dest.bv, Fl4Spec.natToCref r (off + j)) :=
      ⟨dest, rfl, Or.inl (by rw [natToCref_length _ _ hr]; exact hdest)⟩
    have hne : cslotAddr (dest.bv, Fl4Spec.natToCref r (off + j)) ≠ dsl := by
      intro e
      have := cslotAddr_inj hP' hAj hAd e
      simp only [Prod.mk.injEq, true_and] at this
      have h2 := congrArg (fun l => Fl4Spec.ofBl (w := 64) l) this
      rw [natToCref_eq _ _ hr, natToCref_eq _ _ hr, ofBl_bitsOf_eq, ofBl_bitsOf_eq] at h2
      have h3 := congrArg BitVec.toNat h2
      simp at h3
      have hrr : 2 ^ r ≤ 18446744073709551616 := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) hr; simpa using this
      have hj64 : off + j < 18446744073709551616 := by omega
      have hi64 : off + i < 18446744073709551616 := by omega
      simp only [Nat.mod_eq_of_lt hj64, Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hoff] at h3
      omega
    show capAt _ (slotAddr dest.bv (BitVec.ofNat 64 (off + j))) = _
    rw [hdj, hcapW _ hAj.isSlot, if_neg hne]
    have := hnull j (by omega) hj2; simp only at this; rw [hdj] at this; exact this
  · intro x hx hp
    have hsrcm : src ∈ Gi.chains.flatten := (hM.members src).2 ⟨hs, _, hsrcC, by simp⟩
    rcases (mem_flatten_ins (dest := dsl) hsrcm).1 hx with hxd | hx'
    · subst hxd
      rw [hcapD] at hp ⊢
      refine ⟨by rw [hcb, hct]; omega, Or.inl (Or.inl (by rw [hct, Nat.add_mul, Nat.one_mul]; omega))⟩
    · have hxs := hslot x hx'
      have hxd : x ≠ dsl := fun e => hdestm (e ▸ hx')
      rw [hcapV x hxs hxd] at hp ⊢
      obtain ⟨h1', h2'⟩ := hno x hx' hp
      refine ⟨h1', ?_⟩
      rcases h2' with h | h
      · left; unfold DisjR at h ⊢; rw [Nat.add_mul, Nat.one_mul]; omega
      · exact Or.inr h
  · intro y hy
    rcases (desc_insG_true hM hdestm hsd y src).1 hy with hy | ⟨rfl, -⟩
    · have hym := (desc_mem hM hy).1
      rw [hcapV y (hslot y hym) (fun e => hdestm (e ▸ hym))]
      have := hdd y hy
      unfold DisjR at this ⊢; rw [Nat.add_mul, Nat.one_mul]; omega
    · rw [hcapD]; unfold DisjR; left; rw [hct, Nat.add_mul, Nat.one_mul]; omega
  · intro w hw h1 h2
    have hout : ∀ a, (a = src ∨ a = dsl ∨ (nextOf (L.mem s) src ≠ 0#u64 ∧ a = nextOf (L.mem s) src)) →
        ¬ (a.val ≤ w.val ∧ w.val < a.val + 32) := by
      rintro a (rfl | rfl | ⟨hz, rfl⟩)
      · have := hzs _ hs; omega
      · have := hzs _ hd; omega
      · have := hzs _ (hnx0.resolve_left hz); omega
    rw [hfr w hw hout]; exact hzr w hw h1 h2
  · have hsrcm : src ∈ Gi.chains.flatten := (hM.members src).2 ⟨hs, _, hsrcC, by simp⟩
    intro x hx
    rcases (mem_flatten_ins (dest := dsl) hsrcm).1 hx with hxd | hx'
    · exact Or.inr ⟨i, by omega, by rw [hxd]; exact hdsl.symm⟩
    · rcases hT1 x hx' with h | ⟨j, hj, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, he⟩
  · have hsrcm : src ∈ Gi.chains.flatten := (hM.members src).2 ⟨hs, _, hsrcC, by simp⟩
    intro x hx
    exact (mem_flatten_ins (dest := dsl) hsrcm).2 (Or.inr (hT1b x hx))
  · intro j hj
    by_cases hji : j = i
    · subst hji; show capV _ (slotAddr dest.bv (BitVec.ofNat 64 (off + j))) = _
      rw [hdsl, hcapD]
    · have hj' : j < i := by omega
      have hdj : IsSlot th' (slotAddr dest.bv (BitVec.ofNat 64 (off + j))) :=
        ⟨dest, off + j, Or.inl ⟨r, hdest, by omega⟩, rfl⟩
      have hne : slotAddr dest.bv (BitVec.ofNat 64 (off + j)) ≠ dsl := by
        intro e
        have hc := hT2a j hj'
        simp only at hc
        rw [e] at hc
        have := hcapW dsl hd
        rw [if_pos rfl, capAt_capV] at this
        have hdn := hdnull
        rw [capAt_capV] at hdn
        have h1 := eq_of_ok_eq hdn
        rw [h1] at hc
        exact (hcnF j (by omega)).ne_null hc.symm
      show capV _ (slotAddr dest.bv (BitVec.ofNat 64 (off + j))) = _
      rw [hcapV _ hdj hne]; exact hT2a j hj'
  · intro x hx
    have hx' := hT1b x hx
    rw [hcapV x (hslot x hx') (fun e => hdestm (e ▸ hx'))]; exact hT2b x hx
  · intro y x
    rw [desc_insG_true hM hdestm hsd y x, hT3 y x]
    have hsx : ∀ x, Mdb.Desc Gi.par src x ↔ Mdb.Desc G0.par src x := by
      intro x; rw [hT3]
      constructor
      · rintro (h | ⟨j, hj, he, -⟩)
        · exact h
        · exact absurd he (hsrcd j (by omega))
      · exact Or.inl
    rw [hsx x]
    constructor
    · rintro ((h | ⟨j, hj, hy1, hy2⟩) | ⟨hy1, hy2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, hy1, hy2⟩
      · exact Or.inr ⟨i, by omega, by rw [hy1]; exact hdsl.symm, hy2⟩
    · rintro (h | ⟨j, hj, hy1, hy2⟩)
      · exact Or.inl (Or.inl h)
      · by_cases hji : j = i
        · subst hji; exact Or.inr ⟨by rw [hy1]; exact hdsl, hy2⟩
        · exact Or.inl (Or.inr ⟨j, by omega, hy1, hy2⟩)

end

end

end Fl4Proofs.P3
