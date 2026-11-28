/-
P3 (line mmuAD, gen 42b13): **FL4's `ept::unmap` against the spec's `guestUnmap`** at `EptCore` — the shared core of
the table unmap (`ept::decode`'s unmap label, ept.rs l. 266-283), the EPT frame unmap (vspace.rs `decode_frame`'s
`X86PageUnmap` of an `is_ept` frame) and the finalise of a mapped non-root `Ept` cap (ept.rs l. 228-233).

FL4 (ept.rs l. 191-214): `find(asid)` (none: nothing), `lookup(r, gpa, level)` (a fault: nothing), the entry `e` read,
`large = !table && level > 12`, `mask` = `ADDRESS` (or `ADDRESS & !(2^level - 1)` when large); nothing when `e & 1 = 0`,
or `level ≠ 12` and the large bit (bit 7) differs from `large`, or `e & mask ≠ paddr(ptr)`; otherwise the entry is
written 0 and `invalidate(r)`. Spec (Fl4Spec/Ext/VirtEptInv `guestUnmap`): the same tests in the same order, the
entry by `storeGuestEntry tbl i 0`.

* Spec side: **`UnmapMiss`** (the spec's "nothing" test); **`guestUnmap_noRoot`**, **`guestUnmap_noSlot`**,
  **`guestUnmap_miss`**, **`guestUnmap_hit`** (the four outcomes, single outcome each).
* FL4 side: the tests' words by P3/EptLookup's `ew_and` (bits 0, 7 and the address mask miss the hardware bits 5, 6),
  the large mask (`unmapMask_bv`, `zv_gpaMask`), `paddr` (`paddr_bv`).
* **`EptCore.unmapRel`** — the top: from `EptCore`, `VsRel`, `ArchRefines` [P] (`ept::invalidate`,
  P3/XTopJointFinVtOps' `ept_invalidate_ar`), `gpa < 2^47` and `level ∈ {39, 30, 21, 12}`: FL4's `ept.unmap`
  ⦃ the arch relation kept and **`UnmapOut`**: either FL4's store and the spec state unchanged (single outcome), or a
  reachable table `t ∈ X` at level `lkLvl level` on the walk path of `asid` / `gpa` (`GPath`) whose entry
  `idx = guestIndex gpa level` passes the tests on both sides (`¬ UnmapMiss`), FL4's store is `wr s (eptA t idx) 0`
  and the spec's single outcome is `storeGuestEntry t idx 0` ⦄.

Premise: `ArchRefines arI AR` [P] (the existing arch-refinement premise of P3/VsArch, as P3/EptFinRoot). No new named
premise. New file; root import after `P3.EptFrameMapTop`. No existing statement changed.
-/
import Fl4Proofs.P3.EptFrameMapTop
import Fl4Proofs.P3.XTopJointFinVtOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The spec's `guestUnmap` -/

section
open Fl4Spec

/-- The spec's `large` flag of `guestUnmap`. -/
def unmapLarge (level : Nat) (table : Bool) : Bool := !table && decide (level > 12)

/-- The spec's entry mask of `guestUnmap`. -/
def unmapMsk (level : Nat) (table : Bool) : Word :=
  if unmapLarge level table then guestPteAddress &&& ~~~(((1 : Word) <<< level) - 1) else guestPteAddress

/-- **The spec's "nothing to unmap" test** on the entry `e` (module docstring). -/
def UnmapMiss (e : Word) (ptr : ObjRef) (level : Nat) (table : Bool) : Prop :=
  e &&& 1 = 0 ∨ (level ≠ 12 ∧ decide (e &&& 128 ≠ 0) ≠ unmapLarge level table) ∨
    e &&& unmapMsk level table ≠ addrFromPPtr ptr

theorem guestUnmap_noRoot {σ : State Unit} {asid : Asid} {gpa : Word} {ptr : ObjRef} {level : Nat} {table : Bool}
    {lf : LookupFailure} (hF : ExceptT.run (findGuestRoot (Z := Unit) asid) σ = ({(.error lf, σ)}, False)) :
    guestUnmap (Z := Unit) asid gpa ptr level table σ = ({((), σ)}, False) := by
  unfold guestUnmap
  rw [nd_bind_single hF]
  rfl

theorem guestUnmap_noSlot {σ : State Unit} {asid : Asid} {gpa : Word} {ptr : ObjRef} {level : Nat} {table : Bool}
    {root : ObjRef} {lf : LookupFailure}
    (hF : ExceptT.run (findGuestRoot (Z := Unit) asid) σ = ({(.ok root, σ)}, False))
    (hL : (guestLookupSlot (Z := Unit) root gpa level).run σ = ({(.error lf, σ)}, False)) :
    guestUnmap (Z := Unit) asid gpa ptr level table σ = ({((), σ)}, False) := by
  unfold guestUnmap
  rw [nd_bind_single hF]
  dsimp only
  rw [nd_bind_single hL]
  rfl

theorem guestUnmap_miss {σ : State Unit} {asid : Asid} {gpa : Word} {ptr : ObjRef} {level : Nat} {table : Bool}
    {root t : ObjRef} {l : Nat} {es : BitVec 9 → Word}
    (hF : ExceptT.run (findGuestRoot (Z := Unit) asid) σ = ({(.ok root, σ)}, False))
    (hL : (guestLookupSlot (Z := Unit) root gpa level).run σ = ({(.ok t, σ)}, False))
    (hk : σ.kheap t = some (.archObj (.ept l es))) (hm : UnmapMiss (es (guestIndex gpa level)) ptr level table) :
    guestUnmap (Z := Unit) asid gpa ptr level table σ = ({((), σ)}, False) := by
  unfold guestUnmap
  rw [nd_bind_single hF]
  dsimp only
  rw [nd_bind_single hL]
  dsimp only
  rw [nd_bind_single (getEpt_eq hk)]
  dsimp only
  unfold NonDet.unless
  split
  · rename_i h1
    have h1' : unmapLarge level table = true := h1
    simp only [UnmapMiss, unmapMsk, h1', ↓reduceIte] at hm
    split
    · rfl
    · rename_i h2; simp only [h1] at h2; exact absurd hm h2
  · rename_i h1
    have h1' : ¬ unmapLarge level table = true := h1
    simp only [UnmapMiss, unmapMsk, h1', Bool.false_eq_true, ↓reduceIte] at hm
    split
    · rfl
    · rename_i h2; simp only [Bool.of_not_eq_true h1] at h2; exact absurd hm h2

theorem guestUnmap_hit {σ : State Unit} {asid : Asid} {gpa : Word} {ptr : ObjRef} {level : Nat} {table : Bool}
    {root t : ObjRef} {l : Nat} {es : BitVec 9 → Word}
    (hF : ExceptT.run (findGuestRoot (Z := Unit) asid) σ = ({(.ok root, σ)}, False))
    (hL : (guestLookupSlot (Z := Unit) root gpa level).run σ = ({(.ok t, σ)}, False))
    (hk : σ.kheap t = some (.archObj (.ept l es))) (hm : ¬ UnmapMiss (es (guestIndex gpa level)) ptr level table) :
    guestUnmap (Z := Unit) asid gpa ptr level table σ = storeGuestEntry (Z := Unit) t (guestIndex gpa level) 0 σ := by
  unfold guestUnmap
  rw [nd_bind_single hF]
  dsimp only
  rw [nd_bind_single hL]
  dsimp only
  rw [nd_bind_single (getEpt_eq hk)]
  dsimp only
  unfold NonDet.unless
  split
  · rename_i h1
    have h1' : unmapLarge level table = true := h1
    simp only [UnmapMiss, unmapMsk, h1', ↓reduceIte] at hm
    split
    · rename_i h2; simp only [h1] at h2; exact absurd h2 hm
    · rfl
  · rename_i h1
    have h1' : ¬ unmapLarge level table = true := h1
    simp only [UnmapMiss, unmapMsk, h1', Bool.false_eq_true, ↓reduceIte] at hm
    split
    · rename_i h2; simp only [Bool.of_not_eq_true h1] at h2; exact absurd h2 hm
    · rfl

end

/-! ## The relation -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

/-- **The outcome relation of the two unmaps** (module docstring). -/
def UnmapOut (X : Set U64) (XL : U64 → Nat) (σ : Fl4Spec.State Unit) (s : S) (asid gpa ptr level : U64)
    (table : Bool) (s' : S) (o : Set (Unit × Fl4Spec.State Unit) × Prop) : Prop :=
  (s' = s ∧ o = ({((), σ)}, False)) ∨
  (∃ t ∈ X, ∃ es, XL t = lkLvl level.val ∧
    GPath σ (Fl4Spec.asidHighBitsOf asid.bv) (Fl4Spec.asidLowBitsOf asid.bv) gpa.bv (lkLvl level.val) t.bv ∧
    σ.kheap t.bv = some (.archObj (.ept (XL t) es)) ∧
    ¬ UnmapMiss (es (Fl4Spec.guestIndex gpa.bv level.val)) ptr.bv level.val table ∧
    s' = L.wr s (eptA t (Fl4Spec.guestIndex gpa.bv level.val)) 0#u64 ∧
    o = Fl4Spec.storeGuestEntry (Z := Unit) t.bv (Fl4Spec.guestIndex gpa.bv level.val) 0 σ)

/-- FL4's large-frame mask word is the spec's. -/
theorem unmapMask_bv {level z i2 : U64} (hl64 : level.val < 64) (hz : z.val = 2 ^ level.val)
    (hi2 : i2.val = z.val - 1) :
    (ept.ADDRESS &&& ~~~i2).bv = Fl4Spec.guestPteAddress &&& ~~~(((1 : Fl4Spec.Word) <<< level.val) - 1) := by
  have hm := zv_gpaMask hl64 hz hi2
  rw [UScalar.bv_and, UScalar.bv_not]
  exact congrArg₂ (fun x y => x &&& ~~~y) address_bv hm

theorem msk_ok (level : Nat) (table : Bool) : unmapMsk level table &&& 0x60 = 0 := by
  unfold unmapMsk
  split
  · rw [BitVec.and_assoc, BitVec.and_comm (~~~_), ← BitVec.and_assoc, maskA_ok]
    exact BitVec.zero_and
  · exact maskA_ok

/-- A U64 equality as a bit-vector equality. -/
theorem u_eq_bv (x y : U64) : x = y ↔ x.bv = y.bv :=
  ⟨fun h => h ▸ rfl, fun h => P1.eq_of_bv h⟩

variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **FL4's `ept::unmap` against `guestUnmap`** (module docstring). -/
theorem EptCore.unmapRel (C : EptCore (L := L) X XL th s σ) {P : Set U64} (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hA : ArchRefines arI AR) (a : A) {c : Fl4Spec.Cr3} (hAR : AR a c) (asid gpa ptr level : U64) (table : Bool)
    (hg : gpa.val < 2 ^ 47) (hl : level.val = 39 ∨ level.val = 30 ∨ level.val = 21 ∨ level.val = 12) :
    ept.unmap st arI s a asid gpa ptr level table ⦃ r => AR r.2 c ∧
      UnmapOut (L := L) X XL σ s asid gpa ptr level table r.1
        (Fl4Spec.guestUnmap (Z := Unit) asid.bv gpa.bv ptr.bv level.val table σ) ⦄ := by
  have hl64 : level.val < 64 := by omega
  unfold ept.unmap
  refine WP.spec_bind (ept_find_rel (st := st) s σ hR asid) ?_
  rintro r (⟨rfl, hF⟩ | ⟨w, e, rfl, hpa, he1, hwe, hF⟩)
  · simp only [WP.spec_ok]
    exact ⟨hAR, Or.inl ⟨rfl, guestUnmap_noRoot hF⟩⟩
  obtain ⟨root, hrX, hrb, -, hlk⟩ := C.lookup hpa.guest he1 hg hl
  have hrw : root = w := P1.eq_of_bv (hrb.trans hwe.symm)
  subst hrw
  rw [← hrb] at hlk
  simp only
  rcases hlk with ⟨t, ht, hXt, -, hpath, hr, ho⟩ | ⟨sh, hr, ho⟩
  · rw [hr, bind_ok]
    simp only
    rw [L.read_eq, bind_ok]
    set idx := Fl4Spec.guestIndex gpa.bv level.val with hidx
    obtain ⟨es, hk, hwd⟩ := C.rel.obj t ht
    have hrange : XL t ≠ 0 ∨ idx.toNat < 256 := by
      by_cases h0' : XL t = 0
      · right
        have h39 : level.val = 39 := by
          rw [hXt] at h0'
          rcases hl with h | h | h | h <;> rw [h] at h0' <;> first | exact h | (simp [lkLvl] at h0')
        rw [hidx, guestIndex_toNat, h39, Nat.shiftRight_eq_div_pow]
        exact eptRootIdx_lt hg
      · exact Or.inl h0'
    have hW := hwd _ hrange
    set wd := L.mem s (eptA t idx) with hwd'
    have b1 : wd.bv &&& 1 = es idx &&& 1 := ew_and hW mask1_ok
    have b128 : wd.bv &&& 128 = es idx &&& 128 := ew_and hW mask128_ok
    have bm : wd.bv &&& unmapMsk level.val table = es idx &&& unmapMsk level.val table := ew_and hW (msk_ok _ _)
    have hP := hpath _ _ hpa
    have hpad : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE).bv = Fl4Spec.addrFromPPtr ptr.bv := paddr_bv ptr
    -- the spec's outcomes
    have hmiss : UnmapMiss (es idx) ptr.bv level.val table →
        Fl4Spec.guestUnmap (Z := Unit) asid.bv gpa.bv ptr.bv level.val table σ = ({((), σ)}, False) :=
      fun h => guestUnmap_miss hF ho hk h
    have hhit : ¬ UnmapMiss (es idx) ptr.bv level.val table →
        Fl4Spec.guestUnmap (Z := Unit) asid.bv gpa.bv ptr.bv level.val table σ =
          Fl4Spec.storeGuestEntry (Z := Unit) t.bv idx 0 σ :=
      fun h => guestUnmap_hit hF ho hk h
    -- FL4's large flag as a value
    obtain ⟨lg, hlgv, hlge⟩ : ∃ lg : Bool,
        (if table then ok false else if level > 12#u64 then ok true else ok false : Result Bool) = ok lg ∧
          lg = unmapLarge level.val table := by
      by_cases htb : table = true
      · exact ⟨false, by rw [htb]; rfl, by unfold unmapLarge; rw [htb]; rfl⟩
      · have htb' : table = false := by cases table <;> simp_all
        by_cases h12 : level > 12#u64
        · refine ⟨true, by rw [htb']; simp [h12], ?_⟩
          unfold unmapLarge; rw [htb']
          have : level.val > 12 := by scalar_tac
          simp [this]
        · refine ⟨false, by rw [htb']; simp [h12], ?_⟩
          unfold unmapLarge; rw [htb']
          have : ¬ level.val > 12 := by scalar_tac
          simp [this]
    -- FL4's `mask`
    obtain ⟨mask, hmask, hmb⟩ : ∃ mask : U64,
        (if lg = true then (do
            let i ← lift (level &&& 63#u64)
            let i1 ← 1#u64 <<< i
            let i2 ← i1 - 1#u64
            let i3 ← lift (~~~ i2)
            ok (ept.ADDRESS &&& i3) : Result U64)
          else ok ept.ADDRESS) = ok mask ∧ mask.bv = unmapMsk level.val table := by
      by_cases hlg : lg = true
      · obtain ⟨z, hz2, hzv⟩ := shl_radix hl64
        have hz1 : 1 ≤ z.val := by rw [hzv]; exact (zv_pow64 hl64).1
        obtain ⟨i2, hi2, hi2v, -⟩ := spec_exists (U64.sub_spec (x := z) (y := 1#u64) (by scalar_tac))
        refine ⟨ept.ADDRESS &&& ~~~i2, ?_, ?_⟩
        · simp only [hlg, ↓reduceIte, lift, bind_ok, hz2, hi2]
        · refine (unmapMask_bv hl64 hzv (by rw [hi2v]; rfl)).trans ?_
          unfold unmapMsk; rw [if_pos (hlge.symm.trans hlg)]
      · refine ⟨ept.ADDRESS, by simp only [hlg, Bool.false_eq_true, ↓reduceIte], ?_⟩
        unfold unmapMsk; rw [if_neg (fun h => hlg (hlge.trans h))]; exact address_bv
    rw [hlgv, bind_ok, hmask, bind_ok]
    simp only [lift, bind_ok, layout.paddr]
    -- the tests
    by_cases h1 : wd &&& 1#u64 = 0#u64
    · have hs1 : es idx &&& 1 = 0 := b1.symm.trans ((u_and_zero _ _).1 h1)
      simp only [h1, ↓reduceIte, WP.spec_ok]
      exact ⟨hAR, Or.inl ⟨rfl, hmiss (Or.inl hs1)⟩⟩
    have hs1 : ¬ es idx &&& 1 = 0 := fun h => h1 ((u_and_zero _ _).2 (b1.trans h))
    simp only [h1, ↓reduceIte]
    -- the address test, common to both branches
    have haddr : (wd &&& mask != core.num.U64.wrapping_sub ptr layout.PPTR_BASE) = true ↔
        es idx &&& unmapMsk level.val table ≠ Fl4Spec.addrFromPPtr ptr.bv := by
      have e : U64.bv (wd &&& mask) = U64.bv wd &&& U64.bv mask := UScalar.bv_and wd mask
      rw [bne_iff_ne, Ne, Ne, u_eq_bv, e, hmb, hpad, bm]
    have hwrite : ∀ (hn : ¬ UnmapMiss (es idx) ptr.bv level.val table),
        (do
          let s1 ← st.write s (eptA t idx) 0#u64
          ept.invalidate st arI s1 a root) ⦃ r => AR r.2 c ∧
          UnmapOut (L := L) X XL σ s asid gpa ptr level table r.1
            (Fl4Spec.guestUnmap (Z := Unit) asid.bv gpa.bv ptr.bv level.val table σ) ⦄ := by
      intro hn
      rw [L.write_eq, bind_ok]
      refine WP.spec_mono (ept_invalidate_ar hA _ a root hAR) ?_
      rintro ⟨s2, a2⟩ ⟨e2, har2⟩
      refine ⟨har2, Or.inr ⟨t, ht, es, hXt, hP, hk, hn, e2, hhit hn⟩⟩
    by_cases h12 : level = 12#u64
    · have h12v : level.val = 12 := by rw [h12]; rfl
      have hne : (level != 12#u64) = false := by simp [h12]
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      by_cases ha : (wd &&& mask != core.num.U64.wrapping_sub ptr layout.PPTR_BASE) = true
      · simp only [ha, ↓reduceIte, WP.spec_ok]
        exact ⟨hAR, Or.inl ⟨rfl, hmiss (Or.inr (Or.inr (haddr.1 ha)))⟩⟩
      · simp only [ha, Bool.false_eq_true, ↓reduceIte]
        refine hwrite ?_
        rintro (h | ⟨h, -⟩ | h)
        · exact hs1 h
        · exact h h12v
        · exact ha (haddr.2 h)
    · have h12v : level.val ≠ 12 := fun h => h12 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      have hne : (level != 12#u64) = true := by simp [h12]
      simp only [hne, ↓reduceIte]
      have hlb : ((wd &&& 128#u64 != 0#u64) != lg) = true ↔
          decide (es idx &&& 128 ≠ 0) ≠ unmapLarge level.val table := by
        have e128' : (wd &&& 128#u64 != 0#u64) = decide (es idx &&& 128 ≠ 0) := by
          by_cases hb : es idx &&& 128 = 0
          · have h0 : wd &&& 128#u64 = 0#u64 := (u_and_zero _ _).2 (b128.trans hb)
            rw [h0, hb]; simp
          · have h0 : wd &&& 128#u64 ≠ 0#u64 := fun h => hb (b128.symm.trans ((u_and_zero _ _).1 h))
            rw [bne_iff_ne.mpr h0]
            exact (decide_eq_true hb).symm
        rw [e128', ← hlge]
        generalize decide (es idx &&& 128 ≠ 0) = b
        cases b <;> cases lg <;> decide
      by_cases hb : ((wd &&& 128#u64 != 0#u64) != lg) = true
      · simp only [hb, ↓reduceIte, WP.spec_ok]
        exact ⟨hAR, Or.inl ⟨rfl, hmiss (Or.inr (Or.inl ⟨h12v, hlb.1 hb⟩))⟩⟩
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        by_cases ha : (wd &&& mask != core.num.U64.wrapping_sub ptr layout.PPTR_BASE) = true
        · simp only [ha, ↓reduceIte, WP.spec_ok]
          exact ⟨hAR, Or.inl ⟨rfl, hmiss (Or.inr (Or.inr (haddr.1 ha)))⟩⟩
        · simp only [ha, Bool.false_eq_true, ↓reduceIte]
          refine hwrite ?_
          rintro (h | ⟨-, h⟩ | h)
          · exact hs1 h
          · exact hb (hlb.2 h)
          · exact ha (haddr.2 h)
  · rw [hr, bind_ok]
    simp only [WP.spec_ok]
    exact ⟨hAR, Or.inl ⟨rfl, guestUnmap_noSlot hF ho⟩⟩

end

end

end Fl4Proofs.P3
