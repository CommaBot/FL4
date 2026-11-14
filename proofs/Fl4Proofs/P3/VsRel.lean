/-
P3 (DESIGN.md §9), VSpace: **the ASID table and ASID pools**, and
`find_vspace_for_asid` against l4v `find_vspace_for_asid`.

FL4 keeps the ASID table in the global state, at `ks::ASID_TABLE` (288000)
from `ks_base`: word `hi` (`hi < N_ASID_POOLS = 2048`) is the pool of the
ASIDs with high bits `hi`, 0 for none. An ASID pool is a 4K frame of 512
words: word `lo` is the PML4 of ASID `hi · 512 + lo`, 0 for none. l4v
(`asid_high_len = 11`, `asid_low_len = 9`) has `x64_asid_table` in the arch
state and `ASIDPool` objects in the heap.

`VsRel P m ksb σ` relates them over the ghost set `P` of pool addresses:
* `table`: `x64_asid_table (ucast hi) = optRef (m (atA ksb hi))`;
* `tmem`: the non-zero table words are in `P`;
* `pool`: each `p ∈ P` is an `ASIDPool f` with `f (ucast lo) = optRef (m (peA p lo))`.
-/
import Fl4Proofs.P3.Ep
import Fl4Spec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

@[step] theorem layout.ks.ASID_TABLE.spec : layout.ks.ASID_TABLE ⦃ v => v = 288000#u64 ⦄ := by
  unfold layout.ks.ASID_TABLE layout.MAX_NODES fl4_abi.config.MAX_NUM_NODES
  simp only [show ¬ ((64#u64 : U64) > 64#u64) by decide, ↓reduceIte]
  step*

/-- The address of word `hi` of the ASID table. -/
def atA (ksb hi : U64) : U64 :=
  core.num.U64.wrapping_add ksb (core.num.U64.wrapping_add 288000#u64 (core.num.U64.wrapping_mul hi 8#u64))

/-- The address of word `lo` of the ASID pool at `p`. -/
def peA (p lo : U64) : U64 := core.num.U64.wrapping_add p (core.num.U64.wrapping_mul lo 8#u64)

/-- The ASID table and pools (see the module docstring). -/
structure VsRel (P : Set U64) (m : U64 → U64) (ksb : U64) (σ : Fl4Spec.State Unit) : Prop where
  table : ∀ hi : U64, hi.val < 2048 → σ.archState.x64AsidTable (Fl4Spec.ucast 11 hi.bv) = optRef (m (atA ksb hi))
  tmem : ∀ hi : U64, hi.val < 2048 → m (atA ksb hi) ≠ 0#u64 → m (atA ksb hi) ∈ P
  pool : ∀ p ∈ P, ∃ f, σ.kheap p.bv = some (.archObj (.asidPool f)) ∧
    ∀ lo : U64, lo.val < 512 → f (Fl4Spec.ucast 9 lo.bv) = optRef (m (peA p lo))

/-! ## Indices -/

theorem hi_bv (asid i : U64) (hi : i.val = asid.val >>> 9) :
    (Fl4Spec.ucast 11 (i &&& 2047#u64 : U64).bv : BitVec 11) = Fl4Spec.asidHighBitsOf asid.bv := by
  unfold Fl4Spec.asidHighBitsOf Fl4Spec.asidLowBits Fl4Spec.asidLowLen Fl4Spec.ucast
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, UScalar.bv_and, BitVec.toNat_and, BitVec.toNat_ushiftRight]
  rw [show (UScalar.bv (2047#u64 : U64)).toNat = 2 ^ 11 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by decide)]
  show i.val % 2 ^ 11 = _
  rw [hi]; rfl

theorem lo_bv (asid : U64) : (Fl4Spec.ucast 9 (asid &&& 511#u64 : U64).bv : BitVec 9) = Fl4Spec.asidLowBitsOf asid.bv := by
  unfold Fl4Spec.asidLowBitsOf Fl4Spec.asidLowLen Fl4Spec.ucast
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, UScalar.bv_and, BitVec.toNat_and]
  rw [show (UScalar.bv (511#u64 : U64)).toNat = 2 ^ 9 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by decide)]

theorem and_lt (x : U64) (k : Nat) (K : U64) (hK : K.val = 2 ^ k - 1) (hk : k < 64) : (x &&& K).val < 2 ^ k := by
  have : (x &&& K).val = x.val % 2 ^ k := by
    show (x &&& K).bv.toNat = _
    rw [UScalar.bv_and, BitVec.toNat_and, show K.bv.toNat = 2 ^ k - 1 from hK, Nat.and_two_pow_sub_one_eq_mod]; rfl
  rw [this]; exact Nat.mod_lt _ (by positivity)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem asid_table_spec (s : S) (hi : U64) :
    vspace.asid_table st s hi ⦃ v => v = L.mem s (atA (L.ksb s) (hi &&& 2047#u64)) ⦄ := by
  unfold vspace.asid_table obj.ks_get
  have hN : vspace.N_ASID_POOLS = 2048#u64 := by unfold vspace.N_ASID_POOLS; rfl
  rw [hN]
  step*
  subst_vars
  congr 4
  apply UScalar.eq_of_val_eq
  simp_all [UScalar.val_and]

theorem set_asid_table_spec (s : S) (hi pool : U64) :
    vspace.set_asid_table st s hi pool ⦃ s' => s' = L.wr s (atA (L.ksb s) (hi &&& 2047#u64)) pool ⦄ := by
  unfold vspace.set_asid_table obj.ks_set
  have hN : vspace.N_ASID_POOLS = 2048#u64 := by unfold vspace.N_ASID_POOLS; rfl
  rw [hN]
  step*
  subst_vars
  congr 4
  apply UScalar.eq_of_val_eq
  simp_all [UScalar.val_and]

end

/-! ## The spec's `find_vspace_for_asid` -/

section Spec
open Fl4Spec

theorem runE_bind_ok {ε α β : Type} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    {s s' : State Unit} {a : α} (h : ExceptT.run m s = ({(.ok a, s')}, False)) :
    ExceptT.run (m >>= f) s = ExceptT.run (f a) s' := by
  show NonDet.bind (ExceptT.run m) (ExceptT.bindCont f) s = _
  rw [nd_bind_one' h]; rfl

theorem runE_bind_err {ε α β : Type} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    {s s' : State Unit} {e : ε} (h : ExceptT.run m s = ({(.error e, s')}, False)) :
    ExceptT.run (m >>= f) s = ({(.error e, s')}, False) := by
  show NonDet.bind (ExceptT.run m) (ExceptT.bindCont f) s = _
  rw [nd_bind_one' h]; rfl

theorem runE_liftE {ε α : Type} {m : NonDet (State Unit) α} {s s' : State Unit} {a : α}
    (h : m s = ({(a, s')}, False)) : ExceptT.run (NonDetE.liftE (ε := ε) m) s = ({(.ok a, s')}, False) := by
  show NonDet.bind m (fun a => NonDet.pure (Except.ok a)) s = _
  rw [nd_bind_one' h]; rfl

theorem getAsidPool_eq {σ : State Unit} {p : ObjRef} {f : AsidLowIndex → Option ObjRef}
    (hk : σ.kheap p = some (.archObj (.asidPool f))) : getAsidPool (Z := Unit) p σ = ({(f, σ)}, False) := by
  unfold getAsidPool
  rw [nd_bind_one (getObject_eq hk)]
  rfl

/-- The result of `find_vspace_for_asid`, given the table entry and the pool. -/
def fvSpec (σ : State Unit) (asid : Asid) : Except LookupFailure ObjRef :=
  match σ.archState.x64AsidTable (asidHighBitsOf asid) with
  | none => .error .invalidRoot
  | some p => match σ.kheap p with
    | some (.archObj (.asidPool f)) => match f (asidLowBitsOf asid) with
      | some r => .ok r
      | none => .error .invalidRoot
    | _ => .error .invalidRoot

theorem findVspaceForAsid_none {σ : State Unit} {asid : Asid} (h0 : asid > 0)
    (ht : σ.archState.x64AsidTable (asidHighBitsOf asid) = none) :
    ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.error .invalidRoot, σ)}, False) := by
  unfold findVspaceForAsid NonDetE.assertE
  rw [runE_bind_ok (runE_liftE (assert_true' h0 σ)), runE_bind_ok (runE_liftE (show NonDet.gets _ σ = _ from rfl))]
  simp only [ht]
  rw [runE_bind_ok (show ExceptT.run (NonDetE.returnOk (none : Option ObjRef)) σ = ({(.ok none, σ)}, False) from rfl)]
  dsimp only
  exact runE_bind_err (show ExceptT.run (NonDetE.throwError (α := AsidLowIndex → Option ObjRef) LookupFailure.invalidRoot) σ =
    ({(.error .invalidRoot, σ)}, False) from rfl)

theorem findVspaceForAsid_some {σ : State Unit} {asid : Asid} (h0 : asid > 0) {p : ObjRef}
    (ht : σ.archState.x64AsidTable (asidHighBitsOf asid) = some p) {f : AsidLowIndex → Option ObjRef}
    (hk : σ.kheap p = some (.archObj (.asidPool f))) :
    ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ =
      ({((match f (asidLowBitsOf asid) with | some r => .ok r | none => .error .invalidRoot), σ)}, False) := by
  unfold findVspaceForAsid NonDetE.assertE
  rw [runE_bind_ok (runE_liftE (assert_true' h0 σ)), runE_bind_ok (runE_liftE (show NonDet.gets _ σ = _ from rfl))]
  simp only [ht]
  rw [runE_bind_ok (show ExceptT.run (NonDetE.returnOk (some p)) σ = _ from rfl)]
  dsimp only
  rw [runE_bind_ok (runE_liftE (getAsidPool_eq hk))]
  rw [runE_bind_ok (show ExceptT.run (NonDetE.returnOk (f (asidLowBitsOf asid))) σ = _ from rfl)]
  cases f (asidLowBitsOf asid) <;> rfl

end Spec

/-- FL4's lookup result as the spec's. -/
def fvRes : core.result.Result U64 error.LookupFault → Except Fl4Spec.LookupFailure Fl4Spec.ObjRef
  | .Ok w => .ok w.bv
  | .Err _ => .error .invalidRoot

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem optRef_eq_none {w : U64} : optRef w = none ↔ w = 0#u64 := by
  unfold optRef; split <;> simp_all

/-- **`find_vspace_for_asid` refines l4v `find_vspace_for_asid`** (for a
non-zero ASID, which l4v asserts). -/
theorem find_vspace_for_asid_rel {P : Set U64} (s : S) (σ : Fl4Spec.State Unit) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (asid : U64) (h0 : asid ≠ 0#u64) :
    vspace.find_vspace_for_asid st s asid ⦃ r =>
      ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asid.bv) σ = ({(fvRes r, σ)}, False) ⦄ := by
  have hpos : asid.bv > 0 := by
    have : asid.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by simpa using h))
    show 0 < asid.bv.toNat
    exact Nat.pos_of_ne_zero this
  unfold vspace.find_vspace_for_asid
  have hL : vspace.ASID_LOW_BITS = 9#u64 := by unfold vspace.ASID_LOW_BITS; rfl
  rw [hL]
  step as ⟨i, hi⟩
  refine WP.spec_bind (asid_table_spec s i) ?_
  rintro pool rfl
  have hiv : i.val = asid.val >>> 9 := by simpa using hi
  have hlt := and_lt i 11 2047#u64 rfl (by decide)
  have htab := hR.table _ hlt
  rw [hi_bv asid i hiv] at htab
  by_cases hp : L.mem s (atA (L.ksb s) (i &&& 2047#u64)) = 0#u64
  · rw [hp, show optRef 0#u64 = none from optRef_zero] at htab
    simp only [hp, ↓reduceIte, WP.spec_ok]
    exact findVspaceForAsid_none hpos htab
  · simp only [hp, ↓reduceIte]
    obtain ⟨f, hkf, hf⟩ := hR.pool _ (hR.tmem _ hlt hp)
    rw [optRef, if_neg hp] at htab
    have hsp := findVspaceForAsid_some hpos htab hkf
    have hlo := and_lt asid 9 511#u64 rfl (by decide)
    have hfe := hf _ hlo
    rw [lo_bv] at hfe
    unfold lift
    apply ok_bind_spec
    apply ok_bind_spec
    apply ok_bind_spec
    step as ⟨root, hroot⟩
    rw [hsp, hfe]
    have hra : root = L.mem s (peA (L.mem s (atA (L.ksb s) (i &&& 2047#u64))) (asid &&& 511#u64)) := hroot
    subst hra
    by_cases h0 : L.mem s (peA (L.mem s (atA (L.ksb s) (i &&& 2047#u64))) (asid &&& 511#u64)) = 0#u64
    · simp only [h0, ↓reduceIte, WP.spec_ok, optRef_zero]; rfl
    · simp only [h0, ↓reduceIte, WP.spec_ok, optRef]; rfl

end

end

end Fl4Proofs.P3.Vs
