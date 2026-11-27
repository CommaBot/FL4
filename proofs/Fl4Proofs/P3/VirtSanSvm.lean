/-
P3x for virtualization (line virt, gen 12): **VIRT-PLAN R1, SVM half — FL4's extracted `sanitize_vmcb` is the
extended spec's `sanitizeVmcb`**, bit for bit (FL4 `crates/fl4-core/src/vcpu.rs` `sanitize_vmcb` l. 596-630,
`valid_pat` l. 490-499; spec `Fl4Spec/Ext/VirtSanitize` `sanitizeVmcb`, `validPat`, table `Svm.writeRule` in
`Fl4Spec/Ext/VirtFields`).

* `valid_pat_eq`: FL4's `valid_pat` loop is the spec's `validPat` (loop lemma `valid_pat_loop_eq`).
* `valid_xcr0_eq`: FL4's `valid_xcr0` is the spec's `validXcr0` (WriteMSR's XCR0 check).
* The extraction inlines the common tail of `sanitize_vmcb` into every arm of its 51-arm match. `armPlain` is that
  tail with the arm's `(mask, forced)` as arguments, `armAddr` the canonical-checked arms' body, `arm8` (intercept
  vector), `armCr4` (`cr4_allowed`), `armShl` (forced `1 << k`: INT_CTL, EFER); `armPlain_rel`, `rel_plain`,
  `rel_addr`, `rel_arm8`, `rel_cr4`, `rel_shl24`, `rel_shl12` relate them to the spec once, outside the match. Each arm is then one `exact`
  (the arm's body is `armPlain`/`armAddr` at its constants up to unfolding; the arm's table entry by
  `Svm.writeRule`'s evaluation).
* **`sanitize_vmcb_rel`**: for every word, old value and value, `vcpu::sanitize_vmcb` returns, and its result is
  `WordResRel`-related to `sanitizeVmcb f.bv old.bv value.bv` (IllegalOperation off the table, InvalidArgument 1
  for a non-canonical address word or a reserved PAT type, otherwise the same stored word). No word differs.

Named premise: **`CapAgree ar a` [P]** (gen 11's, `Fl4Proofs.P3.VirtSanEq.CapAgree`: `Arch::vcpu_capability` is the
spec's `vcpuCapability`; used for `cr4_allowed` and the canonical width, capability 1). No other premise.
-/
import Fl4Proofs.P3.VirtSanEq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtSanSvm
open fl4_core Fl4Spec Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtSanEq

/-! ## `valid_pat` -/

/-- The PAT-entry check of `validPat` at entry `j`. -/
def patOk (p : Word) (j : Nat) : Bool :=
  let t := (p >>> (j * 8)) &&& 255
  t ≤ 1 || (4 ≤ t && t ≤ 7)

theorem validPat_eq (p : Word) : validPat p = (List.range' 0 8).all (patOk p) := by
  unfold validPat; rw [List.range_eq_range']; rfl

theorem pat_step (o : Bool) (t : U64) :
    (if o = true then (if t ≤ 1#u64 then ok true else if t ≥ 4#u64 then ok (decide (t ≤ 7#u64)) else ok false)
      else ok false : Result Bool) =
      ok (o && (decide (t.bv ≤ 1) || (decide (4 ≤ t.bv) && decide (t.bv ≤ 7)))) := by
  have b1 : decide (t.bv ≤ 1) = decide (t.val ≤ 1) := by rw [decide_eq_decide, BitVec.le_def]; exact Iff.rfl
  have b4 : decide (4 ≤ t.bv) = decide (4 ≤ t.val) := by rw [decide_eq_decide, BitVec.le_def]; exact Iff.rfl
  have b7 : decide (t.bv ≤ 7) = decide (t.val ≤ 7) := by rw [decide_eq_decide, BitVec.le_def]; exact Iff.rfl
  have u1 : (t ≤ 1#u64) ↔ t.val ≤ 1 := by constructor <;> intro h <;> scalar_tac
  have u4 : (t ≥ 4#u64) ↔ 4 ≤ t.val := by constructor <;> intro h <;> scalar_tac
  have u7 : (t ≤ 7#u64) ↔ t.val ≤ 7 := by constructor <;> intro h <;> scalar_tac
  rw [b1, b4, b7]
  cases o
  · simp
  · rw [if_pos rfl]
    by_cases h1 : t.val ≤ 1
    · rw [if_pos (u1.2 h1)]; simp [h1]
    · rw [if_neg (fun h => h1 (u1.1 h))]
      by_cases h4 : 4 ≤ t.val
      · rw [if_pos (u4.2 h4)]; by_cases h7 : t.val ≤ 7 <;> simp [h1, h4, h7, u7]
      · rw [if_neg (fun h => h4 (u4.1 h))]; simp [h1, h4]

theorem valid_pat_loop_eq (pat i : U64) (ok1 : Bool) (hi : i.val ≤ 8) :
    vcpu.valid_pat_loop pat i ok1 = ok (ok1 && (List.range' i.val (8 - i.val)).all (patOk pat.bv)) := by
  apply P1.eq_of_spec_fd
  unfold vcpu.valid_pat_loop
  apply loop.spec_decr_nat (measure := fun y : U64 × Bool => 8 - y.1.val)
    (inv := fun y => y.1.val ≤ 8 ∧
      (y.2 && (List.range' y.1.val (8 - y.1.val)).all (patOk pat.bv)) =
        (ok1 && (List.range' i.val (8 - i.val)).all (patOk pat.bv)))
  · rintro ⟨j, o⟩ ⟨hj, he⟩
    simp only at hj he
    unfold vcpu.valid_pat_loop.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : j.val < 8 := by scalar_tac
      step as ⟨i1, hi1⟩
      have hs : i1.val < 64 := by omega
      obtain ⟨i2, hz, hzv, -⟩ := spec_exists (U64.ShiftRight_spec (x := pat) (y := i1) hs)
      rw [hz]
      simp only [lift, bind_ok, pat_step]
      step as ⟨i3, hi3⟩
      refine ⟨by omega, ?_, by omega⟩
      have hb : i2.bv = pat.bv >>> (j.val * 8) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, ← hi1]
        exact hzv
      have hr : List.range' j.val (8 - j.val) = j.val :: List.range' (j.val + 1) (8 - (j.val + 1)) := by
        rw [show 8 - j.val = (8 - (j.val + 1)) + 1 by omega]; rfl
      rw [← he, hr, hi3, List.all_cons]
      simp only [patOk, UScalar.bv_and, hb, Bool.and_assoc]
      rfl
    · rename_i hge
      have : j.val = 8 := by scalar_tac
      refine (WP.spec_ok _).2 ?_
      rw [← he, this]; simp
  · exact ⟨hi, rfl⟩

theorem valid_pat_eq (pat : U64) : vcpu.valid_pat pat = ok (validPat pat.bv) := by
  unfold vcpu.valid_pat
  rw [valid_pat_loop_eq _ _ _ (by simp), validPat_eq]
  simp

/-! ## `valid_xcr0` -/

/-- A masked-word test on `.bv` is the same test on FL4's `U64`. -/
theorem u64_and_eq_iff (x : U64) (m c : U64) (w v : Word) (hw : m.bv = w) (hv : c.bv = v) :
    (x.bv &&& w = v) ↔ (x &&& m = c) := by
  subst hw hv
  constructor
  · intro h; apply u64_ext; exact h
  · intro h; exact congrArg UScalar.bv h

set_option maxHeartbeats 1000000 in
/-- FL4's `valid_xcr0` is the spec's `validXcr0`. -/
theorem valid_xcr0_eq (x host : U64) : vcpu.valid_xcr0 x host = ok (validXcr0 x.bv host.bv) := by
  have e1 : (x.bv &&& ~~~host.bv = 0) ↔ (x &&& ~~~host = 0#u64) := by
    rw [← UScalar.bv_not]; exact u64_and_eq_iff x _ _ _ _ rfl rfl
  have e2 : (x.bv &&& 1 = 0) ↔ (x &&& 1#u64 = 0#u64) := u64_and_eq_iff x _ _ _ _ rfl rfl
  have e3 : (x.bv &&& 4 = 0) ↔ (x &&& 4#u64 = 0#u64) := u64_and_eq_iff x _ _ _ _ rfl rfl
  have e4 : (x.bv &&& 2 = 0) ↔ (x &&& 2#u64 = 0#u64) := u64_and_eq_iff x _ _ _ _ rfl rfl
  have e5 : (x.bv &&& 0xe0 = 0) ↔ (x &&& 224#u64 = 0#u64) := u64_and_eq_iff x _ _ _ _ rfl rfl
  have e6 : (x.bv &&& 0xe0 = 0xe0) ↔ (x &&& 224#u64 = 224#u64) := u64_and_eq_iff x _ _ _ _ rfl rfl
  have e7 : (x.bv &&& 6 = 6) ↔ (x &&& 6#u64 = 6#u64) := u64_and_eq_iff x _ _ _ _ rfl rfl
  have e8 : (x.bv &&& 0x18 = 0) ↔ (x &&& 24#u64 = 0#u64) := u64_and_eq_iff x _ _ _ _ rfl rfl
  have e9 : (x.bv &&& 0x18 = 0x18) ↔ (x &&& 24#u64 = 24#u64) := u64_and_eq_iff x _ _ _ _ rfl rfl
  have e10 : (x.bv &&& 0x60000 = 0) ↔ (x &&& 393216#u64 = 0#u64) := u64_and_eq_iff x _ _ _ _ rfl rfl
  have e11 : (x.bv &&& 0x60000 = 0x60000) ↔ (x &&& 393216#u64 = 393216#u64) := u64_and_eq_iff x _ _ _ _ rfl rfl
  unfold vcpu.valid_xcr0 validXcr0
  simp only [lift, bind_ok, bne_iff_ne, ne_eq]
  simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  split_ifs <;> simp (config := {decide := true}) only [*, decide_true, decide_false, Bool.true_and, Bool.and_true, Bool.false_and,
    Bool.and_false, Bool.not_true, Bool.not_false, Bool.or_true, Bool.or_false, Bool.false_or,
    not_true_eq_false, not_false_eq_true, decide_not]


/-! ## The arms -/

theorem GPAT_eq : vcpu.svm.G_PAT = ok 1640#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.G_PAT.spec
theorem CR0S_eq : vcpu.svm.CR0 = ok 1368#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.CR0.spec

/-- The spec's tail of `sanitizeVmcb` after the table lookup and the canonical check. -/
def svmTail (f old value mask forced : Word) : Except SyscallError Word :=
  if f = Svm.gPat ∧ ¬ validPat value then .error (.invalidArgument 1)
  else
    let v := (old &&& ~~~mask) ||| (value &&& mask) ||| forced
    .ok (if f = Svm.cr0 then v &&& ~~~cr0Owned else v)

theorem sanitizeVmcb_eq (f old value : Word) :
    sanitizeVmcb f old value = match Svm.writeRule f with
      | none => .error .illegalOperation
      | some r =>
        if r.addr ∧ ¬ canonical value canonWidth then .error (.invalidArgument 1)
        else svmTail f old value r.mask r.forced := rfl

/-- FL4's `sanitize_vmcb` tail, as the extraction inlines it into every arm. -/
def armPlain (f old value mask forced : U64) : Result (core.result.Result U64 error.Exc) := do
  let i ← vcpu.svm.G_PAT
  if f = i
  then
    let b ← vcpu.valid_pat value
    if b
    then
      let i1 ← lift (~~~ mask)
      let i2 ← lift (old &&& i1)
      let i3 ← lift (value &&& mask)
      let i4 ← lift (i2 ||| i3)
      let v ← lift (i4 ||| forced)
      let i5 ← vcpu.svm.CR0
      if f = i5
      then
        let i6 ← vcpu.CR0_OWNED
        let i7 ← lift (~~~ i6)
        let v1 ← lift (v &&& i7)
        ok (core.result.Result.Ok v1)
      else ok (core.result.Result.Ok v)
    else error.invalid_arg Std.U64 1#u64
  else
    let i1 ← lift (~~~ mask)
    let i2 ← lift (old &&& i1)
    let i3 ← lift (value &&& mask)
    let i4 ← lift (i2 ||| i3)
    let v ← lift (i4 ||| forced)
    let i5 ← vcpu.svm.CR0
    if f = i5
    then
      let i6 ← vcpu.CR0_OWNED
      let i7 ← lift (~~~ i6)
      let v1 ← lift (v &&& i7)
      ok (core.result.Result.Ok v1)
    else ok (core.result.Result.Ok v)

theorem cr0Owned_bv : (2147155904#u64).bv = cr0Owned := by
  unfold cr0Owned; decide

theorem armPlain_rel (f old value mask forced : U64) :
    ∃ r, armPlain f old value mask forced = ok r ∧
      WordResRel r (svmTail f.bv old.bv value.bv mask.bv forced.bv) := by
  have hg : (f = 1640#u64) ↔ f.bv = Svm.gPat := ⟨fun h => by rw [h]; rfl, fun h => u64_ext h⟩
  have hc : (f = 1368#u64) ↔ f.bv = Svm.cr0 := ⟨fun h => by rw [h]; rfl, fun h => u64_ext h⟩
  unfold armPlain svmTail
  simp only [GPAT_eq, CR0S_eq, CR0O_eq, valid_pat_eq, lift, bind_ok]
  by_cases h1 : f.bv = Svm.gPat
  · have h2 : f.bv ≠ Svm.cr0 := by rw [h1]; decide
    rw [if_pos (hg.2 h1), if_neg (fun h => h2 (hc.1 h))]
    cases hv : validPat value.bv
    · refine ⟨_, rfl, ?_⟩
      simp [hv, h1, WordResRel, SysErrRel]
    · have h3 : ¬ (Svm.gPat = Svm.cr0) := by rw [← h1]; exact h2
      refine ⟨_, rfl, ?_⟩
      simp only [hv, h1, h3, if_true, if_false, WordResRel, not_true_eq_false, and_false, UScalar.bv_or,
        UScalar.bv_and, UScalar.bv_not]
  · rw [if_neg (fun h => h1 (hg.1 h))]
    by_cases h2 : f.bv = Svm.cr0
    · rw [if_pos (hc.2 h2)]
      have h3 : ¬ (Svm.cr0 = Svm.gPat) := by rw [← h2]; exact h1
      refine ⟨_, rfl, ?_⟩
      simp only [h1, h2, h3, if_true, false_and, if_false, WordResRel, UScalar.bv_or, UScalar.bv_and, UScalar.bv_not,
        cr0Owned_bv]
    · rw [if_neg (fun h => h2 (hc.1 h))]
      refine ⟨_, rfl, ?_⟩
      simp only [h1, h2, if_false, false_and, WordResRel, UScalar.bv_or, UScalar.bv_and, UScalar.bv_not]

section
variable {A : Type} {ar : machine.Arch A} {a : A}

/-- The canonical-checked arms (segment bases, LSTAR, CSTAR, KERNEL_GS_BASE, SYSENTER_ESP/EIP). -/
def armAddr (ar : machine.Arch A) (a : A) (f old value : U64) : Result (core.result.Result U64 error.Exc) := do
  let i ← ar.vcpu_capability a 1#u64
  let b ← vcpu.canonical value i
  if b
  then armPlain f old value core.num.U64.MAX 0#u64
  else error.invalid_arg Std.U64 1#u64

theorem rel_plain {f old value mask forced : U64}
    (hr : Svm.writeRule f.bv = some ⟨mask.bv, forced.bv, false⟩) :
    ∃ r, armPlain f old value mask forced = ok r ∧ WordResRel r (sanitizeVmcb f.bv old.bv value.bv) := by
  rw [sanitizeVmcb_eq, hr]
  simp only [false_and, if_false]
  exact armPlain_rel f old value mask forced

theorem rel_addr (hc : CapAgree ar a) {f old value : U64}
    (hr : Svm.writeRule f.bv = some ⟨core.num.U64.MAX.bv, (0#u64).bv, true⟩) :
    ∃ r, armAddr ar a f old value = ok r ∧ WordResRel r (sanitizeVmcb f.bv old.bv value.bv) := by
  have hc' : ∀ g, ar.vcpu_capability a g = ok ⟨vcpuCapability g.bv⟩ := hc
  have hc1 : ar.vcpu_capability a 1#u64 = ok ⟨canonWidth⟩ := hc' 1#u64
  rw [sanitizeVmcb_eq, hr]
  unfold armAddr
  rw [hc1, bind_ok, canonical_eq, bind_ok]
  dsimp only
  simp only [true_and]
  by_cases hk : canonical value.bv canonWidth = true
  · rw [if_pos hk, if_neg (by simp [hk])]
    exact armPlain_rel f old value _ _
  · rw [if_neg hk, if_pos hk]
    exact ⟨_, rfl, by simp [WordResRel, SysErrRel]⟩

/-- The intercept-vector arm (0x008): mask and forced bits computed from FL4's constants. -/
def arm8 (f old value : U64) : Result (core.result.Result U64 error.Exc) := do
  let i ← vcpu.SVM_I1_WRITABLE <<< 32#i32
  let mask ← lift (4294967295#u64 ||| i)
  let i1 ← vcpu.SVM_I1_FORCED <<< 32#i32
  let i2 ← vcpu.EXCEPTIONS
  let forced ← lift (i2 ||| i1)
  armPlain f old value mask forced

theorem rel_arm8 {f old value : U64}
    (hr : Svm.writeRule f.bv = some ⟨(4294967295#u64 ||| (⟨vcpu.SVM_I1_WRITABLE.bv <<< 32⟩ : U64)).bv,
      (393218#u64 ||| (⟨vcpu.SVM_I1_FORCED.bv <<< 32⟩ : U64)).bv, false⟩) :
    ∃ r, arm8 f old value = ok r ∧ WordResRel r (sanitizeVmcb f.bv old.bv value.bv) := by
  unfold arm8
  simp only [shl_32, EXC_eq, lift, bind_ok]
  exact rel_plain hr

/-- The CR4 arm (0x548): FL4's `cr4_allowed` mask. -/
def armCr4 (ar : machine.Arch A) (a : A) (f old value : U64) : Result (core.result.Result U64 error.Exc) := do
  let mask ← vcpu.cr4_allowed ar a
  armPlain f old value mask 0#u64

theorem rel_cr4 (hc : CapAgree ar a) {f old value : U64}
    (hr : Svm.writeRule f.bv = some ⟨cr4AllowedHost, (0#u64).bv, false⟩) :
    ∃ r, armCr4 ar a f old value = ok r ∧ WordResRel r (sanitizeVmcb f.bv old.bv value.bv) := by
  unfold armCr4
  rw [cr4_allowed_eq hc, bind_ok]
  exact rel_plain hr

/-- The arms whose forced bits are a shifted 1 (INT_CTL 0x060: `1 << 24`, EFER 0x4d0: `1 << 12`). -/
def armShl (f old value mask : U64) (k : I32) : Result (core.result.Result U64 error.Exc) := do
  let forced ← 1#u64 <<< k
  armPlain f old value mask forced

theorem rel_shl24 {f old value mask : U64}
    (hr : Svm.writeRule f.bv = some ⟨mask.bv, (⟨(1#u64).bv <<< 24⟩ : U64).bv, false⟩) :
    ∃ r, armShl f old value mask 24#i32 = ok r ∧ WordResRel r (sanitizeVmcb f.bv old.bv value.bv) := by
  unfold armShl
  rw [shl_24, bind_ok]
  exact rel_plain hr

theorem rel_shl12 {f old value mask : U64}
    (hr : Svm.writeRule f.bv = some ⟨mask.bv, (⟨(1#u64).bv <<< 12⟩ : U64).bv, false⟩) :
    ∃ r, armShl f old value mask 12#i32 = ok r ∧ WordResRel r (sanitizeVmcb f.bv old.bv value.bv) := by
  unfold armShl
  rw [shl_12, bind_ok]
  exact rel_plain hr

theorem wr_some_eq {m f m' f' : Word} {d d' : Bool} :
    (some (Svm.WriteRule.mk m f d) = some (Svm.WriteRule.mk m' f' d')) ↔ (m = m' ∧ f = f' ∧ d = d') := by
  simp

/-- `Svm.writeRule` at an arm's word: by evaluation (`rfl`), or for the intercept vector by walking the
`if` chain (one small `decide` per test) and comparing the constants. -/
macro "svm_wr" : tactic => `(tactic| first
  | rfl
  | (unfold Svm.writeRule
     repeat rw [if_neg (by decide)]
     rw [if_pos (by decide)]
     rw [wr_some_eq]
     simp only [UScalar.bv_or, and_true,
       fl4_core.vcpu.SVM_I1_WRITABLE, fl4_core.vcpu.SVM_I1_FORCED, fl4_core.vcpu.SVM_I2_FORCED, fl4_core.vcpu.SVM_EVENT]
     decide))

set_option maxRecDepth 200000 in
/-- **VIRT-PLAN R1, SVM**: FL4's `sanitize_vmcb` is the spec's `sanitizeVmcb` for every word, old value and
value (under [P] `CapAgree`). -/
theorem sanitize_vmcb_rel (hc : CapAgree ar a) (f old value : U64) :
    ∃ r, vcpu.sanitize_vmcb ar a f old value = ok r ∧
      WordResRel r (sanitizeVmcb f.bv old.bv value.bv) := by
  unfold vcpu.sanitize_vmcb
  split
  all_goals try subst_vars
  case h_51 =>
    have hr : Svm.writeRule f.bv = none := by
      rcases hw : Svm.writeRule f.bv with _ | r
      · rfl
      · exfalso
        have hm := writeRule_mem (g := f.bv) (by rw [hw]; rfl)
        simp only [svmTab, List.mem_cons, List.not_mem_nil, or_false] at hm
        repeat (rcases hm with hm | hm; · exact absurd (u64_ext (y := ⟨_⟩) hm) (by assumption))
        exact absurd (u64_ext (y := ⟨_⟩) hm) (by assumption)
    refine ⟨_, rfl, ?_⟩
    simp [WordResRel, SysErrRel, sanitizeVmcb, hr]
  all_goals first
    | exact rel_plain (by svm_wr)
    | exact rel_addr hc (by svm_wr)
    | exact rel_cr4 hc (by svm_wr)
    | exact rel_arm8 (by svm_wr)
    | exact rel_shl24 (by svm_wr)
    | exact rel_shl12 (by svm_wr)

end

end Fl4Proofs.P3.VirtSanSvm
