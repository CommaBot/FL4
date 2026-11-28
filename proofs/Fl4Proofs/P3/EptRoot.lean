/-
P3 (line mmuAD, gen 42b9): **FL4's `ept::root` against the spec's `eptCapRoot`**: the ASID lookup with the guest tag
(crates/fl4-core/src/ept.rs l. 16-42: `find` = `vspace::find_asid` + the tag test `r & 1`, `root` = the cap test
`Ept { level: 0, mapped: true, .. }` + `find` + `r != ptr`) against Fl4Spec/Ext/VirtEptInv l. 89-106
(`findGuestRoot`, `eptCapRoot`), over the base's ASID-table relation `VsRel` (P3/VsRel: the table words and every pool
word, the tag bit included).

* `find_asid_pool`: `vspace.find_asid` returns `Err InvalidRoot` exactly where the spec's ASID table has no pool or
  the pool no entry, and otherwise `Ok w` with `w` the pool entry (`VsRel.table` / `pool`).
* Spec: `findGuestRoot_none` / `findGuestRoot_some` (the spec's lookup computed), `runE_handleE_ok` /
  `runE_handleE_err`.
* **`ept_find_rel`**: FL4's `ept.find` and the spec's `findGuestRoot` have the same single outcome: both
  `InvalidRoot`, or `Ok w` / `ok w.bv` with `w.bv = asidEntryRoot e` for a guest-tagged entry `e` of a pool of the
  ASID table (`GuestEntry σ e`, `e &&& 1 = 1`).
* **`ept_root_rel`** (any FL4 cap `c`): `ept.root st s c` and `eptCapRoot (absCap c)` have the same single outcome
  (`RootOut`): related errors (`ErrRel`: `FailedLookup false InvalidRoot` or `InvalidCapability 1`), or the success
  branch `Ok (ptr, asid)` / `ok (ptr.bv, asid.bv)` for `c = Ept ptr 0 true asid va`, with the tagged entry `e` naming
  `ptr`. σ unchanged.
* **`EptCore.rootOk`**: in the success branch, at `EptCore`, `ptr ∈ X` with `XL ptr = 0` (`EptCore.tag`), which is
  what P3/EptLookup's `EptCore.lookup` starts from.

Gen 42b10: `FindOut` / `RootOut` give the pool entry at the ASID's own indices (`PoolAt`, was `GuestEntry`).

No named premise. New file only; root import after `P3.EptLookup`.
-/
import Fl4Proofs.P3.EptLookup
import Fl4Proofs.P3.VirtFrame60
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Bits -/

theorem and1_one {e : BitVec 64} (h : ¬ e &&& 1 = 0) : e &&& 1 = 1 := by
  have h2 : (e &&& 1).toNat = e.toNat % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have h3 : (e &&& 1).toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  apply BitVec.eq_of_toNat_eq
  rw [h2] at h3 ⊢
  show e.toNat % 2 = 1
  omega

theorem and_not1_bv (w : U64) : (w &&& ~~~1#u64).bv = Fl4Spec.asidEntryRoot w.bv := by
  simp only [UScalar.bv_and, UScalar.bv_not]
  rfl

/-! ## Spec side -/

section Spec
open Fl4Spec Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif

theorem runE_handleE_ok {ε ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    {s : State Unit} {a : α} (hm : ExceptT.run m s = ({(.ok a, s)}, False)) :
    ExceptT.run (NonDetE.handleE m h) s = ({(.ok a, s)}, False) := by
  unfold NonDetE.handleE
  rw [ExceptT.run_mk, nd_bind_one' hm]; rfl

theorem runE_handleE_err {ε ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    {s : State Unit} {e : ε} (hm : ExceptT.run m s = ({(.error e, s)}, False)) :
    ExceptT.run (NonDetE.handleE m h) s = ExceptT.run (h e) s := by
  unfold NonDetE.handleE
  rw [ExceptT.run_mk, nd_bind_one' hm]

theorem findGuestRoot_none {σ : State Unit} {asid : Asid}
    (ht : σ.archState.x64AsidTable (asidHighBitsOf asid) = none) :
    ExceptT.run (findGuestRoot (Z := Unit) asid) σ = ({(.error .invalidRoot, σ)}, False) := by
  unfold findGuestRoot
  rw [runE_bind_ok (runE_liftE (show NonDet.gets _ σ = _ from rfl))]
  simp only [ht]
  exact runE_bind_err rfl

/-- The spec's lookup of a guest root from the pool entry. -/
def gRootRes : Option ObjRef → Except LookupFailure ObjRef
  | none => .error .invalidRoot
  | some e => if e &&& 1 = 0 then .error .invalidRoot else .ok (asidEntryRoot e)

theorem findGuestRoot_some {σ : State Unit} {asid : Asid} {p : ObjRef}
    (ht : σ.archState.x64AsidTable (asidHighBitsOf asid) = some p) {f : AsidLowIndex → Option ObjRef}
    (hk : σ.kheap p = some (.archObj (.asidPool f))) :
    ExceptT.run (findGuestRoot (Z := Unit) asid) σ = ({(gRootRes (f (asidLowBitsOf asid)), σ)}, False) := by
  unfold findGuestRoot
  rw [runE_bind_ok (runE_liftE (show NonDet.gets _ σ = _ from rfl))]
  simp only [ht]
  rw [runE_bind_ok (runE_liftE (getAsidPool_eq hk))]
  cases f (asidLowBitsOf asid) with
  | none => rfl
  | some e =>
    by_cases h : e &&& 1 = 0
    · simp only [gRootRes, if_pos h]; rfl
    · simp only [gRootRes, if_neg h]; rfl

end Spec

/-! ## FL4 side -/

/-- `vspace::find_asid`'s outcome against the spec's ASID table and pools. -/
def FaOut (σ : Fl4Spec.State Unit) (asid : Fl4Spec.Asid) (r : core.result.Result U64 error.LookupFault) : Prop :=
  (r = .Err .InvalidRoot ∧ (σ.archState.x64AsidTable (Fl4Spec.asidHighBitsOf asid) = none ∨
    ∃ p f, σ.archState.x64AsidTable (Fl4Spec.asidHighBitsOf asid) = some p ∧
      σ.kheap p = some (.archObj (.asidPool f)) ∧ f (Fl4Spec.asidLowBitsOf asid) = none)) ∨
  (∃ w p f, r = .Ok w ∧ σ.archState.x64AsidTable (Fl4Spec.asidHighBitsOf asid) = some p ∧
    σ.kheap p = some (.archObj (.asidPool f)) ∧ f (Fl4Spec.asidLowBitsOf asid) = some w.bv)

/-- `ept::find`'s outcome (module docstring). -/
def FindOut (σ : Fl4Spec.State Unit) (asid : Fl4Spec.Asid) (r : core.result.Result U64 error.LookupFault) : Prop :=
  (r = .Err .InvalidRoot ∧
    ExceptT.run (Fl4Spec.findGuestRoot (Z := Unit) asid) σ = ({(.error .invalidRoot, σ)}, False)) ∨
  (∃ w e, r = .Ok w ∧ PoolAt σ (Fl4Spec.asidHighBitsOf asid) (Fl4Spec.asidLowBitsOf asid) e ∧ e &&& 1 = 1 ∧ w.bv = Fl4Spec.asidEntryRoot e ∧
    ExceptT.run (Fl4Spec.findGuestRoot (Z := Unit) asid) σ = ({(.ok w.bv, σ)}, False))

/-- `ept::root`'s outcome (module docstring). -/
def RootOut (σ : Fl4Spec.State Unit) (c : capability.Cap) (r : core.result.Result (U64 × U64) error.Exc) : Prop :=
  ∃ o, (Fl4Spec.eptCapRoot (Z := Unit) (absCap c)).run σ = ({(o, σ)}, False) ∧
    ((∃ e e', r = .Err e ∧ o = .error e' ∧ ErrRel e e') ∨
     (∃ rt asid va e, c = .Ept rt 0#u64 true asid va ∧ r = .Ok (rt, asid) ∧ o = .ok (rt.bv, asid.bv) ∧
        PoolAt σ (Fl4Spec.asidHighBitsOf asid.bv) (Fl4Spec.asidLowBitsOf asid.bv) e ∧ e &&& 1 = 1 ∧
        rt.bv = Fl4Spec.asidEntryRoot e))

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
open Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

attribute [local instance_reducible] UScalar.cMax UScalar.rMax U64.rMax

/-- **`vspace::find_asid` against the spec's ASID table** (module docstring). -/
theorem find_asid_pool {P : Set U64} (s : S) (σ : Fl4Spec.State Unit) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (asid : U64) : vspace.find_asid st s asid ⦃ r => FaOut σ asid.bv r ⦄ := by
  unfold vspace.find_asid
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
  · rw [hp, show optRef 0#u64 = none by simp [optRef]] at htab
    simp only [hp, ↓reduceIte, WP.spec_ok]
    exact Or.inl ⟨rfl, Or.inl htab⟩
  · simp only [hp, ↓reduceIte]
    obtain ⟨f, hkf, hf⟩ := hR.pool _ (hR.tmem _ hlt hp)
    rw [optRef, if_neg hp] at htab
    have hlo := and_lt asid 9 511#u64 rfl (by decide)
    have hfe := hf _ hlo
    rw [lo_bv] at hfe
    unfold lift
    apply ok_bind_spec
    apply ok_bind_spec
    apply ok_bind_spec
    step as ⟨root, hroot⟩
    have hra : root = L.mem s (peA (L.mem s (atA (L.ksb s) (i &&& 2047#u64))) (asid &&& 511#u64)) := hroot
    subst hra
    by_cases h0 : L.mem s (peA (L.mem s (atA (L.ksb s) (i &&& 2047#u64))) (asid &&& 511#u64)) = 0#u64
    · simp only [h0, ↓reduceIte, WP.spec_ok]
      rw [h0, show optRef 0#u64 = none by simp [optRef]] at hfe
      exact Or.inl ⟨rfl, Or.inr ⟨_, f, htab, hkf, hfe⟩⟩
    · simp only [h0, ↓reduceIte, WP.spec_ok]
      rw [optRef, if_neg h0] at hfe
      exact Or.inr ⟨_, _, f, rfl, htab, hkf, hfe⟩

/-- **FL4's `ept::find` against the spec's `findGuestRoot`** (module docstring). -/
theorem ept_find_rel {P : Set U64} (s : S) (σ : Fl4Spec.State Unit) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (asid : U64) : ept.find st s asid ⦃ r => FindOut σ asid.bv r ⦄ := by
  unfold ept.find
  refine WP.spec_bind (find_asid_pool s σ hR asid) ?_
  unfold FaOut
  rintro r (⟨rfl, hn⟩ | ⟨w, p, f, rfl, ht, hk, hf⟩)
  · simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.convert.FromSame, lift, bind_tc_ok, bind_ok, WP.spec_ok]
    unfold FindOut
    refine Or.inl ⟨rfl, ?_⟩
    rcases hn with hn | ⟨p, f, ht, hk, hf⟩
    · exact findGuestRoot_none hn
    · rw [findGuestRoot_some ht hk, hf]; rfl
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, lift, bind_ok]
    have hsp := findGuestRoot_some (asid := asid.bv) ht hk
    rw [hf] at hsp
    by_cases htag : w &&& 1#u64 = 0#u64
    · simp only [htag, ↓reduceIte, WP.spec_ok]
      unfold FindOut
      refine Or.inl ⟨rfl, ?_⟩
      have h0 : w.bv &&& 1 = 0 := (tag_bv_iff w).mpr htag
      rw [hsp]
      simp only [gRootRes, h0, ↓reduceIte]
    · simp only [htag, ↓reduceIte, WP.spec_ok]
      unfold FindOut
      have h1 : ¬ w.bv &&& 1 = 0 := fun h => htag ((tag_bv_iff w).mp h)
      refine Or.inr ⟨_, w.bv, rfl, ⟨p, f, ht, hk, hf⟩, and1_one h1, and_not1_bv w, ?_⟩
      rw [hsp]
      simp only [gRootRes, if_neg h1, and_not1_bv]

/-- `ept::root` of a mapped level-0 `Ept` cap, its match reduced. -/
theorem ept_root_eq (s : S) (ptr asid va : U64) :
    ept.root st s (.Ept ptr 0#u64 true asid va) = (do
      let r ← ept.find st s asid
      let r1 ← core.result.Result.map_err (ept.root.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc st) r ()
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        if val != ptr then error.invalid_cap (U64 × U64) 1#u64 else ok (core.result.Result.Ok (val, asid))
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (U64 × U64) (core.convert.FromSame error.Exc) residual) := rfl

/-- **FL4's `ept::root` against the spec's `eptCapRoot`, any cap** (module docstring). -/
theorem ept_root_rel {P : Set U64} (s : S) (σ : Fl4Spec.State Unit) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (c : capability.Cap) : ept.root st s c ⦃ r => RootOut σ c r ⦄ := by
  by_cases hc : EptRootC c
  · obtain ⟨ptr, asid, va, rfl⟩ := hc
    obtain ⟨r, hr, hout⟩ := P1.spec_ex_fd (ept_find_rel (st := st) s σ hR asid)
    rw [ept_root_eq, hr, bind_ok]
    have hspec : Fl4Spec.eptCapRoot (Z := Unit) (absCap (.Ept ptr 0#u64 true asid va)) =
        (do
          let r ← Fl4Spec.NonDetE.handleE (Fl4Spec.findGuestRoot asid.bv) fun lf =>
            Fl4Spec.NonDetE.throwError (.failedLookup false lf)
          Fl4Spec.NonDetE.whenE (r ≠ ptr.bv) <| Fl4Spec.NonDetE.throwError (.invalidCapability 1)
          Fl4Spec.NonDetE.returnOk (r, asid.bv)) := rfl
    unfold FindOut at hout
    rcases hout with ⟨rfl, hn⟩ | ⟨w, e, rfl, hge, h1, hw, hsp⟩
    · simp only [core.result.Result.map_err,
        ept.root.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, core.convert.FromSame, lift, bind_tc_ok, bind_ok, WP.spec_ok]
      unfold RootOut
      refine ⟨.error (.failedLookup false .invalidRoot), ?_, Or.inl ⟨_, _, rfl, rfl, Or.inl ⟨rfl, trivial⟩⟩⟩
      rw [hspec]
      exact run_bind_error (by rw [runE_handleE_err hn]; rfl) _
    · simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have hh : ((Fl4Spec.NonDetE.handleE (Fl4Spec.findGuestRoot (Z := Unit) asid.bv) fun lf =>
          Fl4Spec.NonDetE.throwError (.failedLookup false lf)) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef).run σ =
          ({(.ok w.bv, σ)}, False) := runE_handleE_ok hsp
      have hsp2 : ∀ q : U64, (Fl4Spec.eptCapRoot (Z := Unit) (absCap (.Ept ptr 0#u64 true asid va))).run σ =
          ((Fl4Spec.NonDetE.whenE (w.bv ≠ ptr.bv) (Fl4Spec.NonDetE.throwError (.invalidCapability 1)) :
            Fl4Spec.SEMonad Unit Unit) >>= fun _ => (Fl4Spec.NonDetE.returnOk (w.bv, asid.bv) :
              Fl4Spec.SEMonad Unit (Fl4Spec.ObjRef × Fl4Spec.Asid))).run σ := fun _ => by
        rw [hspec]; exact run_bind_ok hh _
      by_cases hne : w = ptr
      · subst hne
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        unfold RootOut
        refine ⟨.ok (w.bv, asid.bv), ?_, Or.inr ⟨w, asid, va, e, rfl, rfl, rfl, hge, h1, hw⟩⟩
        rw [hsp2 w, run_whenE_throwV (w.bv ≠ w.bv) _ _ σ, if_neg (not_not.mpr rfl)]
        rfl
      · have hb : (w != ptr) = true := bne_iff_ne.mpr hne
        simp only [hb, ↓reduceIte, error.invalid_cap, WP.spec_ok]
        unfold RootOut
        refine ⟨.error (.invalidCapability 1), ?_, Or.inl ⟨_, _, rfl, rfl, Or.inr ⟨1#u64, rfl, rfl⟩⟩⟩
        have hne' : w.bv ≠ ptr.bv := fun h => hne (P1.eq_of_bv h)
        rw [hsp2 w, run_whenE_throwV (w.bv ≠ ptr.bv) _ _ σ, if_pos hne']
  · rw [ept_root_nonEpt (st := st) s hc, WP.spec_ok]
    unfold RootOut
    refine ⟨.error (.invalidCapability 1), eptCapRoot_bad (fun q m h => hc ?_) σ,
      Or.inl ⟨_, _, rfl, rfl, Or.inr ⟨1#u64, rfl, rfl⟩⟩⟩
    cases c <;> simp only [absCap, Fl4Spec.Cap.archObjectCap.injEq, reduceCtorEq] at h
    rename_i p l m a v
    obtain ⟨h1, h2, h3⟩ := Fl4Spec.ArchCap.eptCap.inj h
    cases m
    · simp at h3
    · exact ⟨p, a, v, by rw [show l = 0#u64 from UScalar.eq_of_val_eq (by rw [h2]; rfl)]⟩

end

/-! ## At `EptCore` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}

/-- **The success branch at `EptCore`** (module docstring): the root `ptr` is a level-0 table of `X`. -/
theorem EptCore.rootOk (C : EptCore (L := L) X XL th s σ) {e : Fl4Spec.ObjRef} (he : GuestEntry σ e)
    (h1 : e &&& 1 = 1) {rt : U64} (hrt : rt.bv = Fl4Spec.asidEntryRoot e) : rt ∈ X ∧ XL rt = 0 := by
  obtain ⟨t, ht, htb, h0⟩ := C.tag e he h1
  have : t = rt := P1.eq_of_bv (htb.trans hrt.symm)
  subst this
  exact ⟨ht, h0⟩

end

end

end Fl4Proofs.P3
