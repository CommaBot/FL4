/-
P3 (DESIGN.md §9), VSpace: the ASID-table side of ASIDControl `MakePool`.

* `decode_loop0_spec`: FL4's search for a free ASID-table entry (the first
  `hi < 2048` whose word is 0, or 2048);
* `table_free_of_found`, `table_full_of_none`: against l4v's free set
  `(dom x64_asid_table)ᶜ` (l4v picks any free entry, FL4 the first);
* `VsRel.add_pool`: the relation after the pool is installed (a zeroed 4K
  frame, l4v's empty `ASIDPool`, the table entry set).

The rest of `MakePool` (the untyped's `delete_objects` / `retype_region`, the
cap insert) belongs to the Untyped and CDT refinements.
-/
import Fl4Proofs.P3.VsAssignRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem and2047_of_lt {j : U64} (h : j.val < 2048) : (j &&& 2047#u64) = j := by
  apply UScalar.eq_of_val_eq
  show (j &&& 2047#u64).bv.toNat = j.bv.toNat
  rw [UScalar.bv_and, BitVec.toNat_and, show (UScalar.bv (2047#u64 : U64)).toNat = 2 ^ 11 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by show j.val < _; omega)]

/-- FL4's search for a free ASID-table entry. -/
theorem decode_loop0_spec (s : S) :
    vspace.decode_loop0 st s 0#u64 ⦃ i => i.val ≤ 2048 ∧
      (∀ j : U64, j.val < i.val → L.mem s (atA (L.ksb s) j) ≠ 0#u64) ∧
      (i.val < 2048 → L.mem s (atA (L.ksb s) i) = 0#u64) ⦄ := by
  have hN : vspace.N_ASID_POOLS = 2048#u64 := by unfold vspace.N_ASID_POOLS; rfl
  unfold vspace.decode_loop0
  apply loop.spec_decr_nat (measure := fun i => 2048 - i.val)
    (inv := fun i => i.val ≤ 2048 ∧ ∀ j : U64, j.val < i.val → L.mem s (atA (L.ksb s) j) ≠ 0#u64)
  · rintro i ⟨hi5, hall⟩
    unfold vspace.decode_loop0.body
    rw [hN]
    by_cases h1 : i < 2048#u64
    · have hi : i.val < 2048 := by have := (gt_iff_val).1 h1; simpa using this
      simp only [h1, ↓reduceIte]
      refine WP.spec_bind (asid_table_spec s i) ?_
      rintro v rfl
      rw [and2047_of_lt hi]
      by_cases hv : L.mem s (atA (L.ksb s) i) = 0#u64
      · simp only [hv, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact (WP.spec_ok _).2 ⟨hi5, hall, fun _ => hv⟩
      · have hne : (L.mem s (atA (L.ksb s) i) != 0#u64) = true := by simp [hv]
        simp only [hne, ↓reduceIte]
        step as ⟨i2, hi2⟩
        have hi2' : i2.val = i.val + 1 := by simpa using hi2
        refine ⟨by omega, fun j hj => ?_, by omega⟩
        by_cases e : j.val = i.val
        · rw [UScalar.eq_of_val_eq e]; exact hv
        · exact hall j (by omega)
    · simp only [h1, ↓reduceIte]
      have hi : i.val = 2048 := by
        have : ¬ i.val < 2048 := fun h => h1 ((gt_iff_val).2 (by simpa using h))
        omega
      exact (WP.spec_ok _).2 ⟨hi5, hall, fun h => by omega⟩
  · exact ⟨by simp, fun j hj => by simp at hj⟩

end

/-- The found table entry is free in l4v. -/
theorem table_free_of_found {P : Set U64} {m : U64 → U64} {ksb : U64} {σ : Fl4Spec.State Unit} (hR : VsRel P m ksb σ)
    {i : U64} (hi : i.val < 2048) (h0 : m (atA ksb i) = 0#u64) :
    (Fl4Spec.ucast 11 i.bv : BitVec 11) ∈ (Fl4Spec.dom σ.archState.x64AsidTable)ᶜ := by
  show ¬ (σ.archState.x64AsidTable (Fl4Spec.ucast 11 i.bv) ≠ none)
  rw [hR.table i hi, h0, optRef_zero]; simp

/-- No free table entry in FL4: none in l4v. -/
theorem table_full_of_none {P : Set U64} {m : U64 → U64} {ksb : U64} {σ : Fl4Spec.State Unit} (hR : VsRel P m ksb σ)
    (hall : ∀ j : U64, j.val < 2048 → m (atA ksb j) ≠ 0#u64) :
    (Fl4Spec.dom σ.archState.x64AsidTable)ᶜ = ∅ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
  have hxl : x.toNat < 2048 := by have := x.isLt; simpa [Fl4Spec.asidHighLen] using this
  set j : U64 := ⟨BitVec.ofNat 64 x.toNat⟩
  have hj : j.val = x.toNat := by
    show (BitVec.ofNat 64 x.toNat).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hxj : (Fl4Spec.ucast 11 j.bv : BitVec 11) = x := by
    apply BitVec.eq_of_toNat_eq
    simp only [Fl4Spec.ucast, BitVec.toNat_setWidth]
    show j.val % 2 ^ 11 = _
    rw [hj, Nat.mod_eq_of_lt (by omega)]
  show σ.archState.x64AsidTable x ≠ none
  rw [← hxj, hR.table j (by omega)]
  unfold optRef; rw [if_neg (hall j (by omega))]; simp

/-- **The relation after `MakePool` installs a pool** `p` at table entry
`hi`: memory changes only in the table word (now `p`) and the zeroed frame
at `p`; l4v adds an empty `ASIDPool` at `p` and sets the table entry. -/
theorem VsRel.add_pool {P : Set U64} {p : U64} {m m' : U64 → U64} {ksb : U64} {σ σ' : Fl4Spec.State Unit}
    (hP : VsPlaced (insert p P) ksb) (hR : VsRel P m ksb σ) (hpP : p ∉ P) {hi : U64} (hhi : hi.val < 2048)
    (hp0 : p ≠ 0#u64)
    (hm : ∀ b, Aligned b → b ≠ atA ksb hi → ¬ (p.val ≤ b.val ∧ b.val < p.val + 4096) → m' b = m b)
    (hz : ∀ lo : U64, lo.val < 512 → m' (peA p lo) = 0#u64) (ht : m' (atA ksb hi) = p)
    (hk' : σ'.kheap p.bv = some (.archObj (.asidPool fun _ => none)))
    (hko : ∀ q ∈ P, σ'.kheap q.bv = σ.kheap q.bv)
    (ht' : σ'.archState.x64AsidTable =
      Function.update σ.archState.x64AsidTable (Fl4Spec.ucast 11 hi.bv) (some p.bv)) :
    VsRel (insert p P) m' ksb σ' := by
  obtain ⟨pa, pf⟩ := hP.pal p (Set.mem_insert _ _)
  have hptab := hP.ptab p (Set.mem_insert _ _)
  have hv := atA_val hP.ksb_fit hhi
  have hoth : ∀ hi' : U64, hi'.val < 2048 → hi' ≠ hi → m' (atA ksb hi') = m (atA ksb hi') := by
    intro hi' h' hne
    have hv' := atA_val hP.ksb_fit h'
    refine hm _ (by show _ % 8 = 0; rw [hv']; have := hP.ksb_al; omega) (fun e => hne ?_) (by rw [hv']; omega)
    have := congrArg UScalar.val e
    rw [hv', hv] at this
    exact UScalar.eq_of_val_eq (by omega)
  refine ⟨fun hi' h' => ?_, fun hi' h' h0 => ?_, fun q hq => ?_⟩
  · rw [ht']
    by_cases e : hi' = hi
    · subst e; rw [Function.update_self, ht]; unfold optRef; rw [if_neg hp0]
    · rw [Function.update_of_ne (fun h => e (ucast_inj 11 h' hhi h)), hoth hi' h' e]; exact hR.table hi' h'
  · by_cases e : hi' = hi
    · subst e; rw [ht]; exact Set.mem_insert _ _
    · rw [hoth hi' h' e] at h0 ⊢; exact Set.mem_insert_of_mem _ (hR.tmem hi' h' h0)
  · rcases hq with rfl | hq
    · exact ⟨_, hk', fun lo h => by rw [hz lo h, optRef_zero]⟩
    · obtain ⟨g, hg, hgf⟩ := hR.pool q hq
      obtain ⟨qa, qf⟩ := hP.pal q (Set.mem_insert_of_mem _ hq)
      have hqp : q ≠ p := fun e => hpP (e ▸ hq)
      have hqv : q.val ≠ p.val := fun h => hqp (UScalar.eq_of_val_eq h)
      refine ⟨g, (hko q hq).trans hg, fun lo h => ?_⟩
      rw [hgf lo h]
      have hl := peA_val qf h
      refine congrArg optRef (hm _ (by show _ % 8 = 0; rw [hl]; omega) (fun e => ?_) (by rw [hl]; omega)).symm
      have := congrArg UScalar.val e
      rw [hl, hv] at this
      have := hP.ptab q (Set.mem_insert_of_mem _ hq)
      omega

end

end Fl4Proofs.P3.Vs
