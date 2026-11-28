/-
P3 (line mmuAD, gen 42b13): **the EPT frame map at the syscall level** — FL4's `syscall::decode_invocation` on a
`Frame` cap (syscall.rs l. 158-164: `vspace::decode`, vspace.rs l. 1155: `decode_frame`, l. 495: the label
`X86PageMapEPT` goes to `ept::map_frame`) against the extended decoder `fl4DecodeInvocationV` at a `.pageCap` with
`fl4PageMapEptLabel` (Fl4Spec/Ext/VirtDispatch l. 66-68: `decodePageMapEpt`).

* **`zv_sysdec_frameEpt`**: FL4's `decode_invocation` at a `Frame` cap with the EPT map label is `ept.map_frame`
  (the `zv_sysdec_ept` / `zv_sysdec_vcpu` analogue); **`zv_decV_frameEpt`**: the extended decoder at a page cap with
  `fl4PageMapEptLabel` is `liftME .ept (decodePageMapEpt …)` (definitional up to the label test).
* **`eptFrameMap_decode_vmEpt`** (the `eptTableMap_decode_vmEpt` analogue for frames): from `VmEptState`, the
  invoked unmapped `Frame` cap in a CNode slot, the EPT map label, P3/EptFrameMapV's scope hypotheses and spec
  arguments by `VArgs`: `syscall.decode_invocation` returns `res`, and either both sides fail with related errors,
  FL4's state unchanged, or the extended decoder has the single outcome `.ept (.frameMap nc …)` (`DecOut`), the
  restart + perform has the single outcome `σ'` (`EptFrameMapSpec`), and `VmEptState` holds after.
* **The arms before the guest-address bound** (ept.rs l. 128-148; spec `decodePageMapEpt`'s first tests, in FL4's
  order): FL4 `zv_frameF_trunc` (`length < 3` or a null `ex[0]`: `TruncatedMessage`), `zv_frameF_gpa`
  (`arg0 & !4095 ≥ LIMIT`: `InvalidArgument 0`), `zv_frameF_mapped` (a mapped frame past the bound:
  `InvalidCapability 0`); spec `zv_fD_trunc`, `zv_fD_gpa`, `zv_fD_mapped`; the top **`frameMapErr_decode`**: under
  `FrameErrArm` (any of the three), FL4's `decode_invocation` returns an error with the store and arch state unchanged
  (so `VmEptState` is kept), and for every spec argument list agreeing with FL4's words (`VArgs`) and extra caps
  agreeing with `ex[0]`'s null flag, at every spec state, the extended decoder's single outcome is a related error.

No named premise (`ZvVirtAgree` [P] as hypothesis, as in P3/EptFrameMapV). New file; root import after
`P3.EptFrameMapV`. No existing statement changed.
-/
import Fl4Proofs.P3.EptFrameMapV
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The dispatch -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- FL4's `decode_invocation` at a `Frame` cap with the EPT map label is `ept.map_frame` (module docstring). -/
theorem zv_sysdec_frameEpt {s : S} {a : A} {lbl len : U64} {slot : obj.Slot} {ptr rights asid va : U64}
    {size : capability.FrameSize} {dev m ep : Bool} {block call cd fp : Bool} {buf : U64}
    {ex : Array obj.Slot 3#usize} (hl : lbl = fl4_abi.label.X86PageMapEPT) :
    syscall.decode_invocation st arI s a lbl len slot (.Frame ptr size rights dev m ep asid va) block call cd fp buf ex =
      ept.map_frame st arI s a len (.Frame ptr size rights dev m ep asid va) slot buf ex := by
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode_frame
  simp only [vspace.as_frame, bind_ok, hl, ↓reduceIte]

/-- The EPT map label's value. -/
theorem zv_frameEptLbl : fl4_abi.label.X86PageMapEPT.val = Fl4Spec.fl4PageMapEptLabel := by
  simp [fl4_abi.label.X86PageMapEPT, Fl4Spec.fl4PageMapEptLabel]

end

section
open Fl4Spec

/-- The extended decoder at a page cap with the EPT map label (module docstring). -/
theorem zv_decV_frameEpt (fp : Bool) {label : Data} (args : List Data) (cref : CapRef) (slot : CslotPtr) (dev : Bool)
    (p : ObjRef) (R : CapRights) (mt : VMMapType) (sz : VMPageSize) (m : Option (Asid × VSpaceRef))
    (ec : List (Cap × CslotPtr)) (buffer : Option ObjRef) (h : dataToNat label = fl4PageMapEptLabel) :
    fl4DecodeInvocationV (Z := Unit) fp label args cref slot (.archObjectCap (.pageCap dev p R mt sz m)) ec buffer =
      NonDetE.liftME Fl4InvocationV.ept (decodePageMapEpt args slot (.pageCap dev p R mt sz m) ec) := by
  unfold fl4DecodeInvocationV
  dsimp only
  rw [if_pos h]

/-- Truncated: `length < 3` or no extra cap. -/
theorem zv_fD_trunc {args : List Data} (slot : CslotPtr) (c : ArchCap) {ec : List (Cap × CslotPtr)}
    (h : args.length < 3 ∨ ec = []) :
    decodePageMapEpt (Z := Unit) args slot c ec = NonDetE.throwError .truncatedMessage := by
  unfold decodePageMapEpt
  rw [if_pos h]

/-- The guest-address bound. -/
theorem zv_fD_gpa {args : List Data} (slot : CslotPtr) (c : ArchCap) {ec : List (Cap × CslotPtr)}
    (h : ¬ (args.length < 3 ∨ ec = [])) (hg : (args.getD 0 0 &&& ~~~(4095 : Word)) ≥ guestGpaLimit)
    (σ : State Unit) :
    ExceptT.run (decodePageMapEpt (Z := Unit) args slot c ec) σ = ({(.error (.invalidArgument 0), σ)}, False) := by
  unfold decodePageMapEpt
  rw [if_neg h]
  exact run_bind_error (by unfold NonDetE.whenE; rw [if_pos hg]; rfl) _

/-- A mapped page cap past the bound. -/
theorem zv_fD_mapped {args : List Data} (slot : CslotPtr) (dev : Bool) (p : ObjRef) (R : CapRights) (mt : VMMapType)
    (sz : VMPageSize) (x : Asid × VSpaceRef) {ec : List (Cap × CslotPtr)}
    (h : ¬ (args.length < 3 ∨ ec = [])) (hg : ¬ (args.getD 0 0 &&& ~~~(4095 : Word)) ≥ guestGpaLimit)
    (σ : State Unit) :
    ExceptT.run (decodePageMapEpt (Z := Unit) args slot (.pageCap dev p R mt sz (some x)) ec) σ =
      ({(.error (.invalidCapability 0), σ)}, False) := by
  unfold decodePageMapEpt
  rw [if_neg h]
  exact run_seq_ok (by unfold NonDetE.whenE; rw [if_neg hg]; rfl) rfl

end

/-! ## FL4's arms before the bound -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

theorem zv_frameF_trunc (s : S) (a : A) (len : U64) (c : capability.Cap) (dest buf : U64)
    (ex : Array obj.Slot 3#usize) (h : len.val < 3 ∨ exAt ex 0 = 0#u64) :
    ept.map_frame st arI s a len c dest buf ex = ok (.Err (.Sys .TruncatedMessage), s, a) := by
  unfold ept.map_frame
  by_cases hl : len.val < 3
  · have g3 : len < 3#u64 := by scalar_tac
    rw [if_pos g3]
    simp [error.truncated]
  · have g3 : ¬ len < 3#u64 := by scalar_tac
    have hz : exAt ex 0 = 0#u64 := h.resolve_left hl
    rw [if_neg g3, zv_ex0Idx, bind_ok, zv_ex0Null, bind_ok,
      if_pos (show decide (exAt ex 0 = 0#u64) = true by simpa using hz)]
    simp [error.truncated]

/-- FL4's guest address `arg0 & !4095` is the spec's. -/
theorem zv_frameGpa_bv (i : U64) : U64.bv (i &&& ~~~4095#u64) = (i.bv &&& ~~~(4095 : Fl4Spec.Word)) := by
  show UScalar.bv (i &&& ~~~4095#u64) = _
  rw [UScalar.bv_and, UScalar.bv_not]
  rfl

theorem zv_frameF_gpa (s : S) (a : A) (len : U64) (c : capability.Cap) (dest buf : U64)
    (ex : Array obj.Slot 3#usize) (hl : ¬ len.val < 3) (hz : exAt ex 0 ≠ 0#u64) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {i : U64} (hsa : msg.syscall_arg st s ct buf 0#u64 = ok i)
    (hg : (i.bv &&& ~~~(4095 : Fl4Spec.Word)) ≥ Fl4Spec.guestGpaLimit) :
    ept.map_frame st arI s a len c dest buf ex = ok (.Err (.Sys (.InvalidArgument 0#u64)), s, a) := by
  obtain ⟨i5, hi5, hi5v⟩ := spec_exists Fl4Proofs.P0.Consts.ept.LIMIT.spec
  have hge : (i &&& ~~~4095#u64) >= i5 := by
    subst hi5v
    show (140737488355328#u64).val ≤ (i &&& ~~~4095#u64).val
    have hv : (i &&& ~~~4095#u64).val = (i.bv &&& ~~~(4095 : Fl4Spec.Word)).toNat := by
      rw [← zv_frameGpa_bv]; rfl
    rw [hv]
    have hg' : (Fl4Spec.guestGpaLimit).toNat ≤ (i.bv &&& ~~~(4095 : Fl4Spec.Word)).toNat := hg
    have hL : (Fl4Spec.guestGpaLimit).toNat = 140737488355328 := by unfold Fl4Spec.guestGpaLimit; decide
    rw [hL] at hg'
    exact hg'
  unfold ept.map_frame
  have g3 : ¬ len < 3#u64 := by scalar_tac
  rw [if_neg g3, zv_ex0Idx, bind_ok, zv_ex0Null, bind_ok,
    if_neg (show ¬ (decide (exAt ex 0 = 0#u64) = true) by simpa using hz), hct, bind_ok, hsa, bind_ok]
  simp only [lift, bind_ok, hi5]
  rw [if_pos hge]
  simp [error.invalid_arg]

theorem zv_frameF_mapped (s : S) (a : A) (len : U64) {ptr rights asid va : U64} {size : capability.FrameSize}
    {dev ep : Bool} (dest buf : U64) (ex : Array obj.Slot 3#usize) (hl : ¬ len.val < 3) (hz : exAt ex 0 ≠ 0#u64)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) {i mask attr : U64}
    (hsa : msg.syscall_arg st s ct buf 0#u64 = ok i) (hsm : msg.syscall_arg st s ct buf 1#u64 = ok mask)
    (hsr : msg.syscall_arg st s ct buf 2#u64 = ok attr)
    (hg : ¬ (i.bv &&& ~~~(4095 : Fl4Spec.Word)) ≥ Fl4Spec.guestGpaLimit) :
    ept.map_frame st arI s a len (.Frame ptr size rights dev true ep asid va) dest buf ex =
      ok (.Err (.Sys (.InvalidCapability 0#u64)), s, a) := by
  obtain ⟨i5, hi5, hi5v⟩ := spec_exists Fl4Proofs.P0.Consts.ept.LIMIT.spec
  have hgv : (i &&& ~~~4095#u64).val < 2 ^ 47 :=
    gpa_lt_of (g := i &&& ~~~4095#u64) (by rw [zv_frameGpa_bv]; exact hg)
  have hge : ¬ (i &&& ~~~4095#u64) >= i5 := by
    subst hi5v
    show ¬ (140737488355328#u64).val ≤ (i &&& ~~~4095#u64).val
    have : (140737488355328#u64 : U64).val = 2 ^ 47 := rfl
    omega
  unfold ept.map_frame
  have g3 : ¬ len < 3#u64 := by scalar_tac
  rw [if_neg g3, zv_ex0Idx, bind_ok, zv_ex0Null, bind_ok,
    if_neg (show ¬ (decide (exAt ex 0 = 0#u64) = true) by simpa using hz), hct, bind_ok, hsa, bind_ok]
  simp only [lift, bind_ok, hi5]
  rw [if_neg hge, hsm, bind_ok, hsr, bind_ok]
  simp [error.invalid_cap]

end

/-! ## The tops -/

/-- **The frame map's arms before the guest-address bound** (module docstring): `z` the null flag of `ex[0]`,
`big` FL4's masked first argument at or above `2^47`, `m` the cap's mapped flag. -/
def FrameErrArm (len : U64) (z big m : Bool) : Prop :=
  len.val < 3 ∨ z = true ∨ big = true ∨ m = true

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Fl4Proofs.P1

/-- **The frame map's arms before the bound, at the syscall level** (module docstring). -/
theorem frameMapErr_decode (s : S) (a : A) {lbl len ptr rights asid va : U64} {size : capability.FrameSize}
    {dev m ep : Bool} (hlb : lbl.val = Fl4Spec.fl4PageMapEptLabel) (slot : obj.Slot) (block call cd fp : Bool)
    (buf : U64) (ex : Array obj.Slot 3#usize) {i mask attr : U64}
    (hsa : msg.syscall_arg st s (L.curW s) buf 0#u64 = ok i) (hsm : msg.syscall_arg st s (L.curW s) buf 1#u64 = ok mask)
    (hsr : msg.syscall_arg st s (L.curW s) buf 2#u64 = ok attr)
    (hE : FrameErrArm len (decide (exAt ex 0 = 0#u64))
      (decide ((i.bv &&& ~~~(4095 : Fl4Spec.Word)) ≥ Fl4Spec.guestGpaLimit)) m) :
    ∃ e, syscall.decode_invocation st arI s a lbl len slot (.Frame ptr size rights dev m ep asid va) block call cd fp
        buf ex = ok (.Err e, s, a) ∧
      ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), VArgs st s (L.curW s) buf len args →
        (exAt ex 0 = 0#u64 → ec = []) → (exAt ex 0 ≠ 0#u64 → ec ≠ []) →
        ∀ (fp' : Bool) (cref : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef)
          (σ : Fl4Spec.State Unit), ∃ e', ErrRel e e' ∧
          ExceptT.run (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp' lbl.bv args cref sl
            (absCap (.Frame ptr size rights dev m ep asid va)) ec buffer) σ = ({(.error e', σ)}, False) := by
  have hct := P1.cur_thread_ok (L := L) s
  have hl' : lbl = fl4_abi.label.X86PageMapEPT := zv_lblEq zv_frameEptLbl hlb
  have hdl : Fl4Spec.dataToNat lbl.bv = Fl4Spec.fl4PageMapEptLabel := by rw [zv_dataToNat]; exact hlb
  have habs : absCap (.Frame ptr size rights dev m ep asid va) =
      .archObjectCap (.pageCap dev ptr.bv (vmRightsOf rights)
        (if m then (if ep then .vmEptMap else .vmVSpaceMap) else .vmNoMap)
        (frameSizeOf size) (if m then some (asid.bv, va.bv) else none)) := rfl
  rw [zv_sysdec_frameEpt hl', habs]
  by_cases ht : len.val < 3 ∨ exAt ex 0 = 0#u64
  · refine ⟨_, zv_frameF_trunc s a len _ slot buf ex ht, fun args ec hA hz hnz fp' cref sl buffer σ =>
      ⟨.truncatedMessage, Or.inl trivial, ?_⟩⟩
    rw [zv_decV_frameEpt _ _ _ _ _ _ _ _ _ _ _ _ hdl]
    refine run_liftME_err ?_
    rw [zv_fD_trunc _ _ (by
      rcases ht with h | h
      · exact Or.inl (by rw [hA.1]; exact h)
      · exact Or.inr (hz h))]
    rfl
  have hl : ¬ len.val < 3 := fun h => ht (Or.inl h)
  have hz : exAt ex 0 ≠ 0#u64 := fun h => ht (Or.inr h)
  have hn : ∀ {args : List Fl4Spec.Data} {ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)},
      VArgs st s (L.curW s) buf len args → (exAt ex 0 ≠ 0#u64 → ec ≠ []) → ¬ (args.length < 3 ∨ ec = []) := by
    intro args ec hA hnz h
    rcases h with h | h
    · rw [hA.1] at h; exact hl h
    · exact hnz hz h
  by_cases hgg : (i.bv &&& ~~~(4095 : Fl4Spec.Word)) ≥ Fl4Spec.guestGpaLimit
  · refine ⟨_, zv_frameF_gpa s a len _ slot buf ex hl hz hct hsa hgg, fun args ec hA _ hnz fp' cref sl buffer σ =>
      ⟨.invalidArgument 0, Or.inl rfl, ?_⟩⟩
    have ha0 : args.getD 0 0 = i.bv := hA.a0 (by omega) hsa
    rw [zv_decV_frameEpt _ _ _ _ _ _ _ _ _ _ _ _ hdl]
    exact run_liftME_err (zv_fD_gpa _ _ (hn hA hnz) (by rw [ha0]; exact hgg) σ)
  have hm : m = true := by
    rcases hE with h | h | h | h
    · exact absurd h hl
    · exact absurd (of_decide_eq_true h) hz
    · exact absurd (of_decide_eq_true h) hgg
    · exact h
  subst hm
  refine ⟨_, zv_frameF_mapped s a len slot buf ex hl hz hct hsa hsm hsr hgg,
    fun args ec hA _ hnz fp' cref sl buffer σ => ⟨.invalidCapability 0, Or.inr ⟨0#u64, rfl, rfl⟩, ?_⟩⟩
  have ha0 : args.getD 0 0 = i.bv := hA.a0 (by omega) hsa
  rw [zv_decV_frameEpt _ _ _ _ _ _ _ _ _ _ _ _ hdl]
  exact run_liftME_err (zv_fD_mapped _ _ _ _ _ _ _ (hn hA hnz) (by rw [ha0]; exact hgg) σ)

set_option maxHeartbeats 4000000 in
/-- **The extended decoder and FL4's `syscall.decode_invocation` on an unmapped frame cap with the EPT map label, at
`VmEptState`** (module docstring; `zv_sysdec_frameEpt` / `zv_decV_frameEpt` + P3/EptFrameMapV's
`VmEptState.frameMap`). -/
theorem eptFrameMap_decode_vmEpt (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hVA : ZvVirtAgree arI) {lbl len ptr rights asid va : U64} {size : capability.FrameSize} {dev ep : Bool}
    (hlb : lbl.val = Fl4Spec.fl4PageMapEptLabel) (block call cd fp : Bool) (buf : U64) (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame ptr size rights dev false ep asid va))
    (hrw : 1 ≤ rights.val ∧ rights.val ≤ 3)
    (hl : ¬ len.val < 3) (hz : exAt ex 0 ≠ 0#u64) (hxe : IsSlot Z.th (exAt ex 0)) {i mask attr : U64}
    (hsa : msg.syscall_arg st s (L.curW s) buf 0#u64 = ok i) (hsm : msg.syscall_arg st s (L.curW s) buf 1#u64 = ok mask)
    (hsr : msg.syscall_arg st s (L.curW s) buf 2#u64 = ok attr)
    (hg : ¬ (i.bv &&& ~~~(4095 : Fl4Spec.Word)) ≥ Fl4Spec.guestGpaLimit)
    (args : List Fl4Spec.Data) (hA : VArgs st s (L.curW s) buf len args)
    (sl0 : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (fp' : Bool) (cref : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    ∃ g : U64, g.bv = (i.bv &&& ~~~(4095 : Fl4Spec.Word)) ∧ g.val < 2 ^ 47 ∧
    ∃ res, syscall.decode_invocation st arI s a lbl len (cslotAddr (pc.bv, idx))
        (.Frame ptr size rights dev false ep asid va) block call cd fp buf ex = ok res ∧
      ((∃ e e', res = (.Err e, s, a) ∧ ErrRel e e' ∧
        ExceptT.run (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp' lbl.bv args cref (pc.bv, idx)
          (absCap (.Frame ptr size rights dev false ep asid va)) ((absCap (capV (L.mem s) (exAt ex 0)), sl0) :: rest)
          buffer) σ = ({(.error e', σ)}, False)) ∨
      (res.1 = .Ok () ∧ ∃ (nc : Fl4Spec.ArchCap) (t : Fl4Spec.ObjRef) (gi : BitVec 9) (E : Fl4Spec.Word)
          (σ' : Fl4Spec.State Unit),
        DecOut (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp' lbl.bv args cref (pc.bv, idx)
          (absCap (.Frame ptr size rights dev false ep asid va)) ((absCap (capV (L.mem s) (exAt ex 0)), sl0) :: rest)
          buffer) σ (.ept (.frameMap nc (pc.bv, idx) t gi E)) ∧
        EptFrameMapSpec σ nc (pc.bv, idx) t gi E σ' ∧
        ∃ Lst' : U64 → List U64, VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst' D res.2.1 res.2.2 σ')) := by
  have hn : ¬ args.length < 3 := by rw [hA.1]; exact hl
  have ha0 : args.getD 0 0 = i.bv := hA.a0 (by omega) hsa
  have ha1 : args.getD 1 0 = mask.bv := hA.a1 (by omega) hsm
  have ha2 : args.getD 2 0 = attr.bv := hA.2 2 attr (by omega) hsr
  obtain ⟨g, hgb, hgv, res, hdec, hout⟩ := VmEptState.frameMap J hni hVA buf ex hpc hidx hcx hrw hl hz hxe
    hsa hsm hsr hg args ha0 ha1 ha2 hn sl0 rest
  have hl' : lbl = fl4_abi.label.X86PageMapEPT := zv_lblEq zv_frameEptLbl hlb
  have hdl : Fl4Spec.dataToNat lbl.bv = Fl4Spec.fl4PageMapEptLabel := by rw [zv_dataToNat]; exact hlb
  have habs : absCap (.Frame ptr size rights dev false ep asid va) =
      .archObjectCap (.pageCap dev ptr.bv (vmRightsOf rights) .vmNoMap (frameSizeOf size) none) := rfl
  refine ⟨g, hgb, hgv, res, by rw [zv_sysdec_frameEpt hl']; exact hdec, ?_⟩
  rw [habs, zv_decV_frameEpt _ _ _ _ _ _ _ _ _ _ _ _ hdl]
  rcases hout with ⟨e, e', h1, he, ho⟩ | ⟨h1, nc, t, gi, E, σ', ho, hS, hJ⟩
  · exact Or.inl ⟨e, e', h1, he, run_liftME_err ho⟩
  · exact Or.inr ⟨h1, nc, t, gi, E, σ', DecOut.liftME (DecOut.of_eq ho), hS, hJ⟩

end

end

end Fl4Proofs.P3
