/-
P3 (line mmuAD, gen 40): **the EPT table-cap invocation arms at `JAtZV3` that read no guest table** — FL4's
`ept::decode` (crates/fl4-core/src/ept.rs l. 236-315) against the extended spec's `decodeEptInvocation`
(Ext/VirtEptInv), through the syscall dispatch (`syscall::decode_invocation`'s `Cap::Ept` arm, syscall.rs l. 154;
Ext/VirtDispatch's `fl4DecodeInvocationV` at `.eptCap`).

* Labels: `eptLbl level` (FL4's `(map, unmap_label)` choice, ept.rs l. 257-263) against the spec's
  `eptTableLabels level.val` (`zv_eptLbl_val`: same numbers 82..87).
* FL4 side, each arm's result with the store and arch state unchanged: `zv_eptF_l0` (level 0, l. 253: illegal),
  `zv_eptF_other` (neither label, l. 312: illegal), `zv_eptF_unmapNF` (unmap of a non-final cap, l. 266:
  RevokeFirst), `zv_eptF_len` / `zv_eptF_null` (map with `length < 2` / a null `ex[0]`, l. 284: truncated),
  `zv_eptF_mapped` (map of a mapped table cap, l. 287: invalid cap 0).
* Spec side: `zv_eD_l0`, `zv_eD_other`, `zv_eD_unmapNF`, `zv_eD_trunc0`, `zv_eD_trunc1`, `zv_eD_mapped`;
  `zv_decV_ept` (the extended decoder at an EPT cap, definitional); `zv_sysdec_ept`.
* **`EptErrArm`**: the six arm conditions in FL4 terms (level, label, finality of the invoked slot `finF`, the
  null flag of `ex[0]`, `length`, `mapped`).
* **`JAtZV3.eptErrJ`** — the top: from `JAtZV3`, the invoked slot `sl` (`AbsSlot Z.th sl`) holding
  `Ept ptr level m asid va`, under `EptErrArm`, FL4's `syscall.decode_invocation` returns an error with the store
  and arch state unchanged (so `JAtZV3` holds after), and for every spec argument list of FL4's length and extra
  caps agreeing with `ex[0]`'s null flag, the extended decoder's single outcome is a related error (`ErrRel`: `SysErrRel` or the invalid-cap index) at the same
  `σ`. The finality of the invoked cap is VsDecFrame's `fin_iff_of` (from `JAtZB.xtop.rel`'s `CRel` / `FinInv`).

**Not covered (state of the arms, nothing claimed):** the arms that read or write a guest table or the ASID
table — unmap of a final cap (`ept::unmap`, `s.zero(ptr, 4096)`, `set_cap`, l. 269-283), map past the `mapped`
check (the guest-address bound, `ept::root`'s ASID lookup `ept::find`, `ept::slot`'s walk `ept::lookup`, the entry
test `DeleteFirst`, the entry write and `set_cap`, l. 289-310). `JAtZV3` has no relation between FL4's guest-table
pages and the spec's `.ept l es` objects (its `X` is only the set of EPT cap pointers in `VtxCap`; no
`StateRel`/`VRel` component reads a guest table), so these arms' spec outcomes (`getEpt`, `guestLookupSlot`,
`storeGuestEntry`, `findGuestRoot`'s pool entry with bit 0) are not determined by FL4's memory at `JAtZV3`: an
EPT-table relation (FL4 table word `i` of `t ∈ X` ↔ `es i` of the spec's `.ept l es` at `t`, and, for `findGuestRoot`, the ASID-pool
entries with the guest tag `r ||| 1`; whether the base's VSpace relation covers tagged entries was not checked) is
what is missing. The guest-address bound arm (l. 288-292) reads no table but was
not done this generation: FL4 masks with `1 << (level & 63)`, the spec with `1 <<< level.val`, equal because a
decoded cap has `level < 64` (`Cap::decode`, capability.rs l. 205: `(w0 >> 53) & 0x3f`), a fact still to be
lifted from `capV`.

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3VFront
import Fl4Proofs.P3.VsDecFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## Labels -/

/-- FL4's `(map, unmap_label)` of a table level (ept.rs l. 257-263). -/
def eptLbl (level : U64) : U64 × U64 :=
  if level = 39#u64 then (fl4_abi.label.X86EPTPDPTMap, fl4_abi.label.X86EPTPDPTUnmap)
  else if level = 30#u64 then (fl4_abi.label.X86EPTPDMap, fl4_abi.label.X86EPTPDUnmap)
  else (fl4_abi.label.X86EPTPTMap, fl4_abi.label.X86EPTPTUnmap)

theorem zv_eptLblIf (level : U64) :
    (if level = 39#u64 then ok (fl4_abi.label.X86EPTPDPTMap, fl4_abi.label.X86EPTPDPTUnmap)
      else if level = 30#u64 then ok (fl4_abi.label.X86EPTPDMap, fl4_abi.label.X86EPTPDUnmap)
      else ok (fl4_abi.label.X86EPTPTMap, fl4_abi.label.X86EPTPTUnmap) : Result (U64 × U64)) =
      ok (eptLbl level) := by
  unfold eptLbl
  by_cases h1 : level = 39#u64
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : level = 30#u64
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]

theorem zv_eptLbl_val (level : U64) :
    (eptLbl level).1.val = (Fl4Spec.eptTableLabels level.val).1 ∧
      (eptLbl level).2.val = (Fl4Spec.eptTableLabels level.val).2 := by
  unfold eptLbl Fl4Spec.eptTableLabels
  by_cases h1 : level = 39#u64
  · subst h1
    simp [fl4_abi.label.X86EPTPDPTMap, fl4_abi.label.X86EPTPDPTUnmap, Fl4Spec.fl4EptPdptMapLabel,
      Fl4Spec.fl4EptPdptUnmapLabel]
  · have h1' : level.val ≠ 39 := fun e => h1 (UScalar.eq_of_val_eq (by rw [e]; rfl))
    rw [if_neg h1, if_neg h1']
    by_cases h2 : level = 30#u64
    · subst h2
      simp [fl4_abi.label.X86EPTPDMap, fl4_abi.label.X86EPTPDUnmap, Fl4Spec.fl4EptPdMapLabel,
        Fl4Spec.fl4EptPdUnmapLabel]
    · have h2' : level.val ≠ 30 := fun e => h2 (UScalar.eq_of_val_eq (by rw [e]; rfl))
      rw [if_neg h2, if_neg h2']
      simp [fl4_abi.label.X86EPTPTMap, fl4_abi.label.X86EPTPTUnmap, Fl4Spec.fl4EptPtMapLabel,
        Fl4Spec.fl4EptPtUnmapLabel]

theorem zv_lblNe {lbl c : U64} {n : ℕ} (hc : c.val = n) (h : lbl.val ≠ n) : lbl ≠ c :=
  fun e => h (by rw [e, hc])

theorem zv_lblEq {lbl c : U64} {n : ℕ} (hc : c.val = n) (h : lbl.val = n) : lbl = c :=
  UScalar.eq_of_val_eq (by rw [h, hc])

theorem zv_dataToNat (lbl : U64) : Fl4Spec.dataToNat lbl.bv = lbl.val := rfl

/-! ## FL4's arms -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

theorem zv_eptF_l0 (s : S) (a : A) (lbl len ptr asid va : U64) (m : Bool) (dest buf : U64)
    (ex : Array obj.Slot 3#usize) :
    ept.decode st arI s a lbl len (.Ept ptr 0#u64 m asid va) dest buf ex =
      ok (.Err (.Sys .IllegalOperation), s, a) := by
  unfold ept.decode
  simp [error.illegal]

theorem zv_eptF_other (s : S) (a : A) {lbl len ptr level asid va : U64} {m : Bool} (dest buf : U64)
    (ex : Array obj.Slot 3#usize) (h0 : level ≠ 0#u64)
    (hu : lbl.val ≠ (Fl4Spec.eptTableLabels level.val).2) (hm : lbl.val ≠ (Fl4Spec.eptTableLabels level.val).1) :
    ept.decode st arI s a lbl len (.Ept ptr level m asid va) dest buf ex =
      ok (.Err (.Sys .IllegalOperation), s, a) := by
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  have hu' : lbl ≠ (eptLbl level).2 := zv_lblNe (zv_eptLbl_val level).2 hu
  have hm' : lbl ≠ (eptLbl level).1 := zv_lblNe (zv_eptLbl_val level).1 hm
  unfold ept.decode
  dsimp only
  rw [if_pos (show (level != 0#u64) = true by simpa using h0), zv_eptLblIf, bind_ok]
  generalize eptLbl level = q at hu' hm' ⊢
  obtain ⟨mL, uL⟩ := q
  dsimp only at hu' hm'
  simp only [uncurry_apply_pair]
  rw [hct, bind_ok, if_neg hu', if_neg hm']
  simp [error.illegal]

theorem zv_eptF_unmapNF (s : S) (a : A) {lbl len ptr level asid va : U64} {m : Bool} (dest buf : U64)
    (ex : Array obj.Slot 3#usize) (h0 : level ≠ 0#u64)
    (hu : lbl.val = (Fl4Spec.eptTableLabels level.val).2) (hf : finF (L.mem s) dest = false) :
    ept.decode st arI s a lbl len (.Ept ptr level m asid va) dest buf ex =
      ok (.Err (.Sys .RevokeFirst), s, a) := by
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  have hu' : lbl = (eptLbl level).2 := zv_lblEq (zv_eptLbl_val level).2 hu
  unfold ept.decode
  dsimp only
  rw [if_pos (show (level != 0#u64) = true by simpa using h0), zv_eptLblIf, bind_ok]
  generalize eptLbl level = q at hu' ⊢
  obtain ⟨mL, uL⟩ := q
  dsimp only at hu'
  simp only [uncurry_apply_pair]
  rw [hct, bind_ok, if_pos hu', is_final_eq, bind_ok, hf]
  simp

theorem zv_eptF_map (s : S) (a : A) {lbl len ptr level asid va : U64} {m : Bool} (dest buf : U64)
    (ex : Array obj.Slot 3#usize) (h0 : level ≠ 0#u64)
    (hu : lbl.val ≠ (Fl4Spec.eptTableLabels level.val).2) (hm : lbl.val = (Fl4Spec.eptTableLabels level.val).1)
    (hE : len.val < 2 ∨ exAt ex 0 = 0#u64 ∨ (2 ≤ len.val ∧ exAt ex 0 ≠ 0#u64 ∧ m = true)) :
    ept.decode st arI s a lbl len (.Ept ptr level m asid va) dest buf ex =
      ok (.Err (.Sys (if len.val < 2 ∨ exAt ex 0 = 0#u64 then .TruncatedMessage else .InvalidCapability 0#u64)),
        s, a) := by
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  have hu' : lbl ≠ (eptLbl level).2 := zv_lblNe (zv_eptLbl_val level).2 hu
  have hm' : lbl = (eptLbl level).1 := zv_lblEq (zv_eptLbl_val level).1 hm
  unfold ept.decode
  dsimp only
  rw [if_pos (show (level != 0#u64) = true by simpa using h0), zv_eptLblIf, bind_ok]
  generalize eptLbl level = q at hu' hm' ⊢
  obtain ⟨mL, uL⟩ := q
  dsimp only at hu' hm'
  simp only [uncurry_apply_pair]
  rw [hct, bind_ok, if_neg hu', if_pos hm']
  by_cases hl : len.val < 2
  · have g2 : len < 2#u64 := by scalar_tac
    rw [if_pos g2, if_pos (Or.inl hl)]
    simp [error.truncated]
  · have g2 : ¬ len < 2#u64 := by scalar_tac
    rw [if_neg g2, zv_ex0Idx, bind_ok, zv_ex0Null, bind_ok]
    by_cases hz : exAt ex 0 = 0#u64
    · rw [if_pos (Or.inr hz)]
      simp [hz, error.truncated]
    · have hmt : m = true := by
        rcases hE with h | h | ⟨-, -, h⟩
        · exact absurd h hl
        · exact absurd h hz
        · exact h
      rw [if_neg (show ¬ (len.val < 2 ∨ exAt ex 0 = 0#u64) from by rintro (h | h) <;> contradiction)]
      subst hmt
      simp [hz, error.invalid_cap]

theorem zv_sysdec_ept (s : S) (a : A) (lbl len : U64) (slot : obj.Slot) (ptr level asid va : U64) (m : Bool)
    (block call cd fp : Bool) (buf : U64) (ex : Array obj.Slot 3#usize) :
    syscall.decode_invocation st arI s a lbl len slot (.Ept ptr level m asid va) block call cd fp buf ex =
      ept.decode st arI s a lbl len (.Ept ptr level m asid va) slot buf ex := by
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  unfold syscall.decode_invocation
  rw [hct, bind_ok]

end

/-! ## The spec's arms -/

section
open Fl4Spec

theorem zv_decV_ept (fp : Bool) (label : Data) (args : List Data) (cref : CapRef) (slot : CslotPtr) (p : ObjRef)
    (l : Nat) (mp : Option (Asid × VSpaceRef)) (ec : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    fl4DecodeInvocationV (Z := Unit) fp label args cref slot (.archObjectCap (.eptCap p l mp)) ec buffer =
      NonDetE.liftME Fl4InvocationV.ept (decodeEptInvocation label args slot (.eptCap p l mp) ec) := rfl

theorem zv_eD_l0 (label : Data) (args : List Data) (slot : CslotPtr) (p : ObjRef) (mp : Option (Asid × VSpaceRef))
    (ec : List (Cap × CslotPtr)) :
    decodeEptInvocation (Z := Unit) label args slot (.eptCap p 0 mp) ec = NonDetE.throwError .illegalOperation := by
  unfold decodeEptInvocation
  simp

theorem zv_eD_other {label : Data} (args : List Data) (slot : CslotPtr) (p : ObjRef) {l : Nat}
    (mp : Option (Asid × VSpaceRef)) (ec : List (Cap × CslotPtr)) (hl : l ≠ 0)
    (h1 : dataToNat label ≠ (eptTableLabels l).2) (h2 : dataToNat label ≠ (eptTableLabels l).1) :
    decodeEptInvocation (Z := Unit) label args slot (.eptCap p l mp) ec = NonDetE.throwError .illegalOperation := by
  unfold decodeEptInvocation
  dsimp only
  rw [if_neg hl]
  generalize eptTableLabels l = q at h1 h2 ⊢
  obtain ⟨mL, uL⟩ := q
  dsimp only at h1 h2 ⊢
  rw [if_neg h1, if_neg h2]

theorem zv_eD_unmapNF {label : Data} (args : List Data) (slot : CslotPtr) (p : ObjRef) {l : Nat}
    (mp : Option (Asid × VSpaceRef)) (ec : List (Cap × CslotPtr)) (hl : l ≠ 0)
    (h1 : dataToNat label = (eptTableLabels l).2) (σ : State Unit)
    (hnf : ¬ isFinalCap' (.archObjectCap (.eptCap p l mp)) σ) :
    ExceptT.run (decodeEptInvocation (Z := Unit) label args slot (.eptCap p l mp) ec) σ =
      ({(.error .revokeFirst, σ)}, False) := by
  unfold decodeEptInvocation
  dsimp only
  rw [if_neg hl]
  generalize eptTableLabels l = q at h1 ⊢
  obtain ⟨mL, uL⟩ := q
  dsimp only at h1 ⊢
  rw [if_pos h1]
  have hF : (isFinalCap (Z := Unit) (.archObjectCap (.eptCap p l mp))) σ = ({(false, σ)}, False) := by
    show ({(decide (isFinalCap' (Z := Unit) (.archObjectCap (.eptCap p l mp)) σ), σ)}, False) = _
    rw [decide_eq_false hnf]
  rw [run_bind_ok (run_liftE hF)]
  exact run_bind_error (by rfl) _

theorem zv_eD_trunc0 {label : Data} (args : List Data) (slot : CslotPtr) (p : ObjRef) {l : Nat}
    (mp : Option (Asid × VSpaceRef)) (hl : l ≠ 0)
    (h1 : dataToNat label ≠ (eptTableLabels l).2) (h2 : dataToNat label = (eptTableLabels l).1) :
    decodeEptInvocation (Z := Unit) label args slot (.eptCap p l mp) [] = NonDetE.throwError .truncatedMessage := by
  unfold decodeEptInvocation
  dsimp only
  rw [if_neg hl]
  generalize eptTableLabels l = q at h1 h2 ⊢
  obtain ⟨mL, uL⟩ := q
  dsimp only at h1 h2 ⊢
  rw [if_neg h1, if_pos h2]

theorem zv_eD_trunc1 {label : Data} {args : List Data} (slot : CslotPtr) (p : ObjRef) {l : Nat}
    (mp : Option (Asid × VSpaceRef)) (x : Cap × CslotPtr) (rest : List (Cap × CslotPtr)) (hl : l ≠ 0)
    (h1 : dataToNat label ≠ (eptTableLabels l).2) (h2 : dataToNat label = (eptTableLabels l).1)
    (hn : args.length < 2) :
    decodeEptInvocation (Z := Unit) label args slot (.eptCap p l mp) (x :: rest) =
      NonDetE.throwError .truncatedMessage := by
  unfold decodeEptInvocation
  dsimp only
  rw [if_neg hl]
  generalize eptTableLabels l = q at h1 h2 ⊢
  obtain ⟨mL, uL⟩ := q
  dsimp only at h1 h2 ⊢
  rw [if_neg h1, if_pos h2, if_pos hn]

theorem zv_eD_mapped {label : Data} {args : List Data} (slot : CslotPtr) (p : ObjRef) {l : Nat}
    {mp : Option (Asid × VSpaceRef)} (x : Cap × CslotPtr) (rest : List (Cap × CslotPtr)) (hl : l ≠ 0)
    (h1 : dataToNat label ≠ (eptTableLabels l).2) (h2 : dataToNat label = (eptTableLabels l).1)
    (hn : ¬ args.length < 2) (hs : mp.isSome = true) :
    decodeEptInvocation (Z := Unit) label args slot (.eptCap p l mp) (x :: rest) =
      NonDetE.throwError (.invalidCapability 0) := by
  unfold decodeEptInvocation
  dsimp only
  rw [if_neg hl]
  generalize eptTableLabels l = q at h1 h2 ⊢
  obtain ⟨mL, uL⟩ := q
  dsimp only at h1 h2 ⊢
  rw [if_neg h1, if_pos h2, if_neg hn, if_pos hs]

end

/-! ## The arms at `JAtZV3` -/

/-- **The EPT arms that read no guest table** (module docstring): `fin` is the invoked slot's FL4 finality,
`b` the null flag of `ex[0]`. -/
def EptErrArm (lbl len level : U64) (m fin b : Bool) : Prop :=
  level = 0#u64 ∨
  (level ≠ 0#u64 ∧ lbl.val ≠ (Fl4Spec.eptTableLabels level.val).2 ∧
    lbl.val ≠ (Fl4Spec.eptTableLabels level.val).1) ∨
  (level ≠ 0#u64 ∧ lbl.val = (Fl4Spec.eptTableLabels level.val).2 ∧ fin = false) ∨
  (level ≠ 0#u64 ∧ lbl.val ≠ (Fl4Spec.eptTableLabels level.val).2 ∧
    lbl.val = (Fl4Spec.eptTableLabels level.val).1 ∧ (len.val < 2 ∨ b = true ∨ m = true))

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **The EPT table-cap error arms at `JAtZV3`** (module docstring). -/
theorem JAtZV3.eptErrJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr}
    (hA : AbsSlot Z.th sl) {ptr level asid va : U64} {m : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Ept ptr level m asid va)) (lbl len : U64) (block call cd fp : Bool)
    (buf : U64) (ex : Array obj.Slot 3#usize)
    (hE : EptErrArm lbl len level m (finF (L.mem s) (cslotAddr sl)) (decide (exAt ex 0 = 0#u64))) :
    ∃ e, syscall.decode_invocation st arI s a lbl len (cslotAddr sl) (.Ept ptr level m asid va) block call cd fp
        buf ex = ok (.Err e, s, a) ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ ∧
      ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), args.length = len.val →
        (exAt ex 0 = 0#u64 → ec = []) → (exAt ex 0 ≠ 0#u64 → ec ≠ []) →
        ∀ (fp' : Bool) (cref : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef), ∃ e', ErrRel e e' ∧
          ExceptT.run (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp' lbl.bv args cref sl
            (absCap (.Ept ptr level m asid va)) ec buffer) σ = ({(.error e', σ)}, False) := by
  have hl0 : ∀ {lv : U64}, lv ≠ 0#u64 → lv.val ≠ 0 := fun h e => h (UScalar.eq_of_val_eq (by rw [e]; rfl))
  have habs : absCap (.Ept ptr level m asid va) =
      .archObjectCap (.eptCap ptr.bv level.val (if m then some (asid.bv, va.bv) else none)) := rfl
  rw [zv_sysdec_ept]
  rcases hE with h0 | ⟨h0, hu, hm⟩ | ⟨h0, hu, hf⟩ | ⟨h0, hu, hm, hE⟩
  · subst h0
    refine ⟨_, zv_eptF_l0 s a lbl len ptr asid va m _ buf ex, J, fun args ec _ _ _ fp' cref buffer =>
      ⟨.illegalOperation, Or.inl trivial, ?_⟩⟩
    rw [habs, zv_decV_ept]
    exact run_liftME_err (by rw [show (0#u64 : U64).val = 0 from rfl, zv_eD_l0]; rfl)
  · refine ⟨_, zv_eptF_other s a _ buf ex h0 hu hm, J, fun args ec _ _ _ fp' cref buffer =>
      ⟨.illegalOperation, Or.inl trivial, ?_⟩⟩
    rw [habs, zv_decV_ept]
    exact run_liftME_err (by rw [zv_eD_other _ _ _ _ _ (hl0 h0) hu hm]; rfl)
  · refine ⟨_, zv_eptF_unmapNF s a _ buf ex h0 hu hf, J, fun args ec _ _ _ fp' cref buffer =>
      ⟨.revokeFirst, Or.inl trivial, ?_⟩⟩
    have B := J.z2.zv.base
    have hfinR := fin_iff_of B.xtop.rel.1 B.xtop.rel.2.1 B.xtop.rel.2.2.1 hA hc (Or.inl ⟨trivial, rfl⟩) rfl
      (by simp)
      (fun h => by
        have : Fl4Spec.GenObjRef.objRef ptr.bv ∈ Fl4Spec.genObjRefs (absCap (.Ept ptr level m asid va)) :=
          Set.mem_union_left _ (Set.mem_union_left _ ⟨ptr.bv, by simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef], rfl⟩)
        rw [h] at this; exact this)
    have hnf : ¬ Fl4Spec.isFinalCap' (absCap (.Ept ptr level m asid va)) σ := fun h => by
      rw [← hfinR, hf] at h; cases h
    rw [habs] at hnf ⊢
    rw [zv_decV_ept]
    exact run_liftME_err (zv_eD_unmapNF _ _ _ _ _ (hl0 h0) hu σ hnf)
  · have hE' : len.val < 2 ∨ exAt ex 0 = 0#u64 ∨ (2 ≤ len.val ∧ exAt ex 0 ≠ 0#u64 ∧ m = true) := by
      by_cases h1 : len.val < 2
      · exact Or.inl h1
      by_cases h2 : exAt ex 0 = 0#u64
      · exact Or.inr (Or.inl h2)
      rcases hE with h | h | h
      · exact absurd h h1
      · exact absurd (of_decide_eq_true h) h2
      · exact Or.inr (Or.inr ⟨by omega, h2, h⟩)
    refine ⟨_, zv_eptF_map s a _ buf ex h0 hu hm hE', J, fun args ec hla hz hnz fp' cref buffer => ?_⟩
    rw [habs, zv_decV_ept]
    by_cases ht : len.val < 2 ∨ exAt ex 0 = 0#u64
    · rw [if_pos ht]
      refine ⟨.truncatedMessage, Or.inl trivial, run_liftME_err ?_⟩
      by_cases h2 : exAt ex 0 = 0#u64
      · rw [hz h2, zv_eD_trunc0 _ _ _ _ (hl0 h0) hu hm]; rfl
      · obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil (hnz h2)
        have hn : args.length < 2 := by
          rcases ht with h | h
          · omega
          · exact absurd h h2
        rw [zv_eD_trunc1 _ _ _ x rest (hl0 h0) hu hm hn]; rfl
    · rw [if_neg ht]
      refine ⟨.invalidCapability 0, Or.inr ⟨0#u64, rfl, rfl⟩, run_liftME_err ?_⟩
      have h2 : exAt ex 0 ≠ 0#u64 := fun h => ht (Or.inr h)
      obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil (hnz h2)
      have hmt : m = true := by
        rcases hE' with h | h | ⟨-, -, h⟩
        · exact absurd (Or.inl h) ht
        · exact absurd h h2
        · exact h
      subst hmt
      rw [zv_eD_mapped _ _ x rest (hl0 h0) hu hm (by omega) rfl]; rfl

end

end

end Fl4Proofs.P3
