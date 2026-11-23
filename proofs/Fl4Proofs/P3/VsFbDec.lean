/-
P3 (issue #16, fb3j): **the FrameBatch decode's leaves** (FL4 against
SpecFbDec's `fbDecP`), for XTopJointVsFb.

* `fb_err`: an error of the decode, the state unchanged, as `TopPostRMX`'s
  error disjunct.
* `check_vspace_fb`: `check_vspace` of a mapped PML4 cap: the root and the
  spec's ASID lookup naming it, or an error and the spec decode's
  `InvalidCapability 0`.
* The header's fields: `fb_words` (`entry_words` of the op against
  `fbOpOf`), `fb_defined` (FL4's `DEFINED` is the spec's `fbDefined`),
  `fb_and_val` / `fb_shr_and_val` (a masked field's value).
-/
import Fl4Proofs.P3.SpecFbDec
import Fl4Proofs.P3.VsDecReply
import Fl4Proofs.P3.VsFrameMapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Vs

noncomputable section

/-! ## Bits of the header -/

theorem fb_OP : vspace.frame_batch.OP = 3#u64 := by simp [vspace.frame_batch.OP]

theorem fb_defined_bv : (1236942192387#u64 : U64).bv = Fl4Spec.fbDefined := by
  unfold Fl4Spec.fbDefined; decide

/-- A masked field's value is the spec's. -/
theorem fb_and_val (x m : U64) : Fl4Spec.dataToNat (x.bv &&& m.bv) = (x &&& m).val := by
  rw [← UScalar.bv_and]; rfl

/-- The header's reserved bits. -/
theorem fb_defined (x : U64) :
    ((x &&& ~~~(1236942192387#u64 : U64)) != 0#u64) = true ↔ x.bv &&& ~~~Fl4Spec.fbDefined ≠ 0 := by
  rw [← fb_defined_bv, ← UScalar.bv_not, ← UScalar.bv_and]
  constructor
  · intro h he
    have : (x &&& ~~~(1236942192387#u64 : U64)) = 0#u64 := P1.eq_of_bv (he.trans rfl)
    rw [this] at h
    simp at h
  · intro h
    have : (x &&& ~~~(1236942192387#u64 : U64)) ≠ 0#u64 := fun he => h (by rw [he]; rfl)
    simpa using this

theorem fb_defined' (x d : U64) (hd : d = 1236942192387#u64) :
    ((x &&& ~~~d) != 0#u64) = true ↔ x.bv &&& ~~~Fl4Spec.fbDefined ≠ 0 := by
  subst hd; exact fb_defined x

/-- `entry_words` of the header's op, against `fbOpOf`. -/
theorem fb_words (x : U64) :
    vspace.frame_batch.entry_words (x &&& vspace.frame_batch.OP) ⦃ w =>
      (w = 0#u64 ∧ Fl4Spec.fbOpOf (Fl4Spec.dataToNat (x.bv &&& 0x3#64)) = none) ∨
      ∃ op, Fl4Spec.fbOpOf (Fl4Spec.dataToNat (x.bv &&& 0x3#64)) = some op ∧ w.val = op.words ∧ w ≠ 0#u64 ∧
        (x &&& vspace.frame_batch.OP = vspace.frame_batch.COPY_MAP ↔ op = .copyMap) ⦄ := by
  have hd : Fl4Spec.dataToNat (x.bv &&& 0x3#64) = (x &&& vspace.frame_batch.OP).val := by
    rw [fb_OP, ← fb_and_val]; rfl
  have h4 : (x &&& vspace.frame_batch.OP).val < 4 := by
    rw [fb_OP, UScalar.val_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rw [hd]
  generalize (x &&& vspace.frame_batch.OP) = y at h4 ⊢
  unfold vspace.frame_batch.entry_words
  have hy : y.val = 0 ∨ y.val = 1 ∨ y.val = 2 ∨ y.val = 3 := by omega
  have nC : ∀ k : U64, k.val ≠ 1 → k ≠ vspace.frame_batch.COPY_MAP := fun k hk e => by
    rw [e] at hk; exact hk (by simp [vspace.frame_batch.COPY_MAP])
  have nR : ∀ k : U64, k.val ≠ 2 → k ≠ vspace.frame_batch.REMAP := fun k hk e => by
    rw [e] at hk; exact hk (by simp [vspace.frame_batch.REMAP])
  have nD : ∀ k : U64, k.val ≠ 3 → k ≠ vspace.frame_batch.DELETE := fun k hk e => by
    rw [e] at hk; exact hk (by simp [vspace.frame_batch.DELETE])
  have yC : ∀ k : U64, k.val = 1 → k = vspace.frame_batch.COPY_MAP := fun k hk =>
    UScalar.eq_of_val_eq (by rw [hk]; simp [vspace.frame_batch.COPY_MAP])
  have yR : ∀ k : U64, k.val = 2 → k = vspace.frame_batch.REMAP := fun k hk =>
    UScalar.eq_of_val_eq (by rw [hk]; simp [vspace.frame_batch.REMAP])
  have yD : ∀ k : U64, k.val = 3 → k = vspace.frame_batch.DELETE := fun k hk =>
    UScalar.eq_of_val_eq (by rw [hk]; simp [vspace.frame_batch.DELETE])
  have hz : ∀ k : U64, k.val ≠ 0 → k ≠ 0#u64 := fun k hk e => hk (by rw [e]; rfl)
  rcases hy with h | h | h | h
  · rw [if_neg (nC y (by omega)), if_neg (nR y (by omega)), if_neg (nD y (by omega))]
    refine (WP.spec_ok _).2 (Or.inl ⟨rfl, ?_⟩)
    rw [h]; rfl
  · rw [if_pos (yC y h)]
    refine (WP.spec_ok _).2 (Or.inr ⟨.copyMap, by rw [h]; rfl, rfl, hz _ (by decide),
      iff_of_true (yC y h) rfl⟩)
  · rw [if_neg (nC y (by omega)), if_pos (yR y h)]
    refine (WP.spec_ok _).2 (Or.inr ⟨.remap, by rw [h]; rfl, rfl, hz _ (by decide),
      iff_of_false (nC y (by omega)) (fun e => nomatch e)⟩)
  · rw [if_neg (nC y (by omega)), if_neg (nR y (by omega)), if_pos (yD y h)]
    refine (WP.spec_ok _).2 (Or.inr ⟨.delete, by rw [h]; rfl, rfl, hz _ (by decide),
      iff_of_false (nC y (by omega)) (fun e => nomatch e)⟩)

/-- A shifted, masked field's value is the spec's. -/
theorem fb_shr_and_val (x k m : U64) (hk : k.val < 64) :
    ∃ y, x >>> k = ok y ∧ Fl4Spec.dataToNat ((x.bv >>> k.val) &&& m.bv) = (y &&& m).val ∧
      (y &&& m).bv = (x.bv >>> k.val) &&& m.bv := by
  refine ⟨_, shr_u64_eq x k hk, ?_, ?_⟩
  · rw [← fb_and_val]
  · rw [UScalar.bv_and]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

theorem fb_mapErr_ok {S A : Type} (st : machine.Store S) (ar : machine.Arch A) (v : U64 × U64) :
    core.result.Result.map_err (vspace.decode_frame_batch.closure.Insts.CoreOpsFunctionFnOnceTupleExcExc st ar)
      (core.result.Result.Ok v : core.result.Result (U64 × U64) error.Exc) () = ok (core.result.Result.Ok v) := by
  simp [core.result.Result.map_err]

theorem fb_mapErr_err {S A : Type} (st : machine.Store S) (ar : machine.Arch A) (e : error.Exc) :
    core.result.Result.map_err (vspace.decode_frame_batch.closure.Insts.CoreOpsFunctionFnOnceTupleExcExc st ar)
      (core.result.Result.Err e : core.result.Result (U64 × U64) error.Exc) () =
      ok (core.result.Result.Err (error.Exc.Sys (error.SysError.InvalidCapability 0#u64))) := by
  simp [core.result.Result.map_err, vspace.decode_frame_batch.closure.Insts.CoreOpsFunctionFnOnceTupleExcExc,
    vspace.decode_frame_batch.closure.Insts.CoreOpsFunctionFnOnceTupleExcExc.call_once]

theorem fb_branch_ok {α β : Type} (x : α) :
    core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Ok x : core.result.Result α β) =
      ok (core.ops.control_flow.ControlFlow.Continue x) := rfl

theorem fb_branch_err {α β : Type} (e : β) :
    core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Err e : core.result.Result α β) =
      ok (core.ops.control_flow.ControlFlow.Break (core.result.Result.Err e)) := rfl

theorem fb_fromResidual (e : error.Exc) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
      (core.convert.FromSame error.Exc) (core.result.Result.Err e) = ok (core.result.Result.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
    core.convert.FromSame.from]

/-- **An error of the FrameBatch decode**, the state unchanged. -/
theorem fb_err {X : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4FrameBatchInvocation} {ct : U64} {s : S} {ar : A} {e : error.Exc}
    {e' : Fl4Spec.SyscallError} (h : m.run σ = ({(.error e', σ)}, False)) (hE : ErrRel e e') (hX : X s ar σ) :
    TopPostRMX (L := L) X σ blk call don
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.frameBatch m)) ct s (.Err e, s, ar) :=
  Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err (run_liftME_err h), hE⟩, hX⟩

/-- **`check_vspace` of a mapped PML4 cap** (the batch's address space). -/
theorem check_vspace_fb {P : Set U64} (s : S) (σ : Fl4Spec.State Unit) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (p asid : U64) (h0 : asid ≠ 0#u64) :
    vspace.check_vspace st s (.Pml4 p true asid) ⦃ r =>
      (r = .Ok (p, asid) ∧
        ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asid.bv) σ = ({(.ok p.bv, σ)}, False)) ∨
      (∃ e, r = .Err e ∧ ∀ args ex, ExceptT.run (Fl4Spec.decodeFrameBatch (Z := Unit) args
        (.pml4Cap p.bv (some asid.bv)) ex) σ = ({(.error (.invalidCapability 0), σ)}, False)) ⦄ := by
  unfold vspace.check_vspace
  simp only [↓reduceIte]
  refine WP.spec_bind (WP.spec_and (find_vspace_for_asid_rel s σ hR asid h0) (find_vspace_for_asid_err s asid)) ?_
  rintro r ⟨hf, he⟩
  cases r with
  | Ok r1 =>
    by_cases hr : r1 = p
    · subst hr
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 (Or.inl ⟨rfl, hf⟩)
    · have : (r1 != p) = true := by simp [hr]
      simp only [this, ↓reduceIte, error.invalid_cap]
      exact (WP.spec_ok _).2 (Or.inr ⟨_, rfl, fun _ _ => decodeFrameBatch_wrongVs hf (fun h => hr (P1.eq_of_bv h))⟩)
  | Err lf =>
    obtain rfl := he lf rfl
    exact (WP.spec_ok _).2 (Or.inr ⟨_, rfl, fun _ _ => decodeFrameBatch_noVs hf⟩)

end

end

end Fl4Proofs.P3
