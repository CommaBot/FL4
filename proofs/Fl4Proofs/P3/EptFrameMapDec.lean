/-
P3 (line mmuAD, gen 42b11): **the EPT frame map's decode, past the guest-address bound, at `EptCore`** — FL4's
`ept::map_frame` (crates/fl4-core/src/ept.rs l. 118-187: `ex[0]`'s root, the alignment and `Huge` tests, the walk
`ept::slot`, the `DeleteFirst` test, `mask_vm_rights`, `frame_entry`, then the caller's restart, `set_cap` of the
frame cap and the entry write) against the extended spec's `decodePageMapEpt` (Fl4Spec/Ext/VirtEptInv l. 182-203),
in the style of P3/EptMapDec's `EptCore.mapDec`.

* Frame sizes: `fbits` (`FrameSize::bits`, `bits_eq`), **`fbits_val`** (`= pageBitsForSize (frameSizeOf sz)`).
* Rights: **`vm_rights_rel`** (`mask_vm_rights v (Rights::from_word w)` is `maskVmRights (vmRightsOf v)
  (dataToRights w)`, from P3/CnodeCaps' `vm_mask` / `rightsW_spec`), `vmRightsOf_ko` / `vmRightsOf_ro`
  (`m = VM_KERNEL_ONLY` / `VM_READ_ONLY` iff its spec rights are).
* The backend: **`frame_entry_spec`** (`ZvVirtAgree`: `ept::frame_entry (virtualization a = 2) …` is the spec's entry
  with `virtKind`, P3/EptFrameEnc's `frame_entry_eq`; the kernel-only and read-only tests through `vmRightsOf`).
* **`EptCore.frameMapDec`**: from `EptCore`, `VsRel`, `ZvVirtAgree`, an unmapped `Frame ptr size rights` cap (rights
  in 1 … 3, `CapWf`), `length ≥ 3`, a non-null `ex[0]`, FL4's three argument words with the page-masked guest address
  `g` below `2^47`, and spec arguments with those words: FL4's `ept.map_frame` returns `res` and the spec decoder has a
  single outcome, related by **`FrameDecOut`**: both fail with related errors (the root, `AlignmentError`, the
  `Huge` size's `InvalidCapability 0`, the walk's `MissingCapability`, `DeleteFirst`), FL4's state unchanged; or the
  spec decodes `.frameMap newCap sl t idx entry` for `t ∈ X` at `lkLvl bits` reached along `g` from the tagged root
  (`GPath`), the entry not present on either side, FL4's rights `m` related, and FL4's state after is the frame
  cap's `set_cap` after the restart followed by the entry write of a word `val` with `val.bv = entry`.

Not here: the arms before the bound (truncation, `gpa ≥ LIMIT`, a mapped frame's `InvalidCapability 0`). The
perform half is P3/EptFrameMap (`EptCore`) and P3/EptFrameMapV (`VmEptState.frameMap`, gen 42b12).

Gen 42b13 (the Architect's `hz0` decision (i)): `EptCore.frameMapDec` takes `hxe : IsSlot th (exAt ex 0)` and
`FrameDecOut`'s success arm also gives `asid1 ≠ 0` (the root cap is a mapped `Ept` slot cap, `JExtEpt.anz`).

No named premise (`ZvVirtAgree` [P] is the gen-34 premise of P3/JAtZV3Vmcs, taken as a hypothesis here). New file;
root import after `P3.EptTableMapV`.
-/
import Fl4Proofs.P3.EptTableMapV
import Fl4Proofs.P3.CnodeCaps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Frame sizes and rights -/

/-- `FrameSize::bits`. -/
def fbits : capability.FrameSize → U64
  | .Small => 12#u64
  | .Large => 21#u64
  | .Huge => 30#u64

theorem bits_eq (sz : capability.FrameSize) : capability.FrameSize.bits sz = ok (fbits sz) := by
  cases sz <;> rfl

theorem fbits_val (sz : capability.FrameSize) : (fbits sz).val = Fl4Spec.pageBitsForSize (frameSizeOf sz) := by
  cases sz <;> rfl

theorem fbits_lt (sz : capability.FrameSize) : (fbits sz).val < 64 := by cases sz <;> decide

/-- **FL4's masked VM rights are the spec's** (`mask_vm_rights`, `Rights::from_word` ↔ `maskVmRights`,
`dataToRights`). -/
theorem vm_rights_rel (v w : U64) (hv : 1 ≤ v.val ∧ v.val ≤ 3) :
    ∃ m, capability.mask_vm_rights v (rightsW w) = ok m ∧ 1 ≤ m.val ∧ m.val ≤ 3 ∧
      vmRightsOf m = Fl4Spec.maskVmRights (vmRightsOf v) (Fl4Spec.dataToRights w.bv) := by
  obtain ⟨m, hm, h1, h3, he⟩ := vm_mask v hv (rightsW w)
  exact ⟨m, hm, h1, h3, by rw [he, rightsW_spec]; rfl⟩

theorem vmRightsOf_ko {m : U64} (h1 : 1 ≤ m.val) (h3 : m.val ≤ 3) :
    m = capability.VM_KERNEL_ONLY ↔ vmRightsOf m = Fl4Spec.vmKernelOnly := by
  have e1 : m = capability.VM_KERNEL_ONLY ↔ m.val = 1 := by
    constructor
    · rintro rfl; simp [capability.VM_KERNEL_ONLY]
    · intro h; apply UScalar.eq_of_val_eq; simp [capability.VM_KERNEL_ONLY, h]
  rw [e1]
  unfold vmRightsOf
  by_cases a3 : m.val = 3
  · rw [if_pos a3]
    refine ⟨fun h => by omega, fun h => ?_⟩
    have hw := congrArg (fun R : Fl4Spec.VMRights => Fl4Spec.Rights.allowRead ∈ R) h
    simp [Fl4Spec.vmReadWrite, Fl4Spec.vmKernelOnly] at hw
  · rw [if_neg a3]
    by_cases a2 : m.val = 2
    · rw [if_pos a2]
      refine ⟨fun h => by omega, fun h => ?_⟩
      have hw := congrArg (fun R : Fl4Spec.VMRights => Fl4Spec.Rights.allowRead ∈ R) h
      simp [Fl4Spec.vmReadOnly, Fl4Spec.vmKernelOnly] at hw
    · rw [if_neg a2]
      exact ⟨fun _ => rfl, fun _ => by omega⟩

theorem vmRightsOf_ro {m : U64} (h1 : 1 ≤ m.val) (h3 : m.val ≤ 3) :
    m = capability.VM_READ_ONLY ↔ vmRightsOf m = Fl4Spec.vmReadOnly := by
  have e2 : m = capability.VM_READ_ONLY ↔ m.val = 2 := by
    constructor
    · rintro rfl; simp [capability.VM_READ_ONLY]
    · intro h; apply UScalar.eq_of_val_eq; simp [capability.VM_READ_ONLY, h]
  rw [e2]
  unfold vmRightsOf
  by_cases a3 : m.val = 3
  · rw [if_pos a3]
    refine ⟨fun h => by omega, fun h => ?_⟩
    have hw := congrArg (fun R : Fl4Spec.VMRights => Fl4Spec.Rights.allowWrite ∈ R) h
    simp [Fl4Spec.vmReadWrite, Fl4Spec.vmReadOnly] at hw
  · rw [if_neg a3]
    by_cases a2 : m.val = 2
    · rw [if_pos a2]
      exact ⟨fun _ => rfl, fun _ => a2⟩
    · rw [if_neg a2]
      refine ⟨fun h => absurd h a2, fun h => ?_⟩
      have hw := congrArg (fun R : Fl4Spec.VMRights => Fl4Spec.Rights.allowRead ∈ R) h
      simp [Fl4Spec.vmReadOnly, Fl4Spec.vmKernelOnly] at hw

/-- The spec's EPT frame entry (`decodePageMapEpt`'s `entry`) for the rights `R'`. -/
def specFrameEntry (R' : Fl4Spec.VMRights) (p : Fl4Spec.ObjRef) (large : Bool) (attr : Fl4Spec.Word) : Fl4Spec.Word :=
  if R' = Fl4Spec.vmKernelOnly then 0 else
    Fl4Spec.GuestPte.encode Fl4Spec.virtKind (.frame (Fl4Spec.addrFromPPtr p) large (R' ≠ Fl4Spec.vmReadOnly)
      (Fl4Spec.guestMemoryType attr))

/-- **`ept::frame_entry` on the backend of `virtualization` is the spec's entry** (`ZvVirtAgree`). -/
theorem frame_entry_spec {A : Type} {arI : machine.Arch A} (hVA : ZvVirtAgree arI) (a : A) (ptr m attr : U64)
    (h1 : 1 ≤ m.val) (h3 : m.val ≤ 3) (large : Bool) :
    ∃ i val, arI.virtualization a = ok i ∧ ept.frame_entry (decide (i = 2#u64)) ptr m attr large = ok val ∧
      val.bv = specFrameEntry (vmRightsOf m) ptr.bv large attr.bv := by
  obtain ⟨i, hi, hk⟩ := hVA a
  refine ⟨i, _, hi, frame_entry_eq Fl4Spec.virtKind (amd := decide (i = 2#u64)) (by simpa using hk) ptr m attr large, ?_⟩
  unfold specFrameEntry
  by_cases hko : m = capability.VM_KERNEL_ONLY
  · rw [if_pos hko, if_pos ((vmRightsOf_ko h1 h3).1 hko)]; rfl
  · rw [if_neg hko, if_neg (fun h => hko ((vmRightsOf_ko h1 h3).2 h))]
    by_cases hro : m = capability.VM_READ_ONLY
    · have h2 := (vmRightsOf_ro h1 h3).1 hro
      have h2' : vmRightsOf capability.VM_READ_ONLY = Fl4Spec.vmReadOnly := hro ▸ h2
      simp only [ne_eq, h2, h2', hro, not_true_eq_false, decide_false]
      all_goals rfl
    · have h2 : ¬ vmRightsOf m = Fl4Spec.vmReadOnly := fun h => hro ((vmRightsOf_ro h1 h3).2 h)
      simp only [ne_eq, h2, hro, not_false_eq_true, decide_true]
      all_goals rfl

/-! ## The decode -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **The outcome of the frame map's decode past the bound** (module docstring). -/
def FrameDecOut (X : Set U64) (XL : U64 → Nat) (σ : Fl4Spec.State Unit) (s : S) (a : A) (ct dest ptr : U64)
    (size : capability.FrameSize) (rights : U64) (dev : Bool) (g mask attr : U64) (sl : Fl4Spec.CslotPtr)
    (res : core.result.Result Unit error.Exc × S × A)
    (o : Set (Except Fl4Spec.SyscallError Fl4Spec.EptInvocation × Fl4Spec.State Unit) × Prop) : Prop :=
  (∃ e e', res = (.Err e, s, a) ∧ ErrRel e e' ∧ o = ({(.error e', σ)}, False)) ∨
  (∃ t asid1 m, t ∈ X ∧ XL t = lkLvl (fbits size).val ∧ asid1.val < 2 ^ 20 ∧ asid1 ≠ 0#u64 ∧ size ≠ .Huge ∧
    GPath σ (Fl4Spec.asidHighBitsOf asid1.bv) (Fl4Spec.asidLowBitsOf asid1.bv) g.bv (lkLvl (fbits size).val) t.bv ∧
    L.mem s (eptA t (Fl4Spec.guestIndex g.bv (fbits size).val)) &&& 1#u64 = 0#u64 ∧
    (∃ es, σ.kheap t.bv = some (.archObj (.ept (XL t) es)) ∧
      es (Fl4Spec.guestIndex g.bv (fbits size).val) &&& 1 = 0) ∧
    capability.mask_vm_rights rights (rightsW mask) = ok m ∧ 1 ≤ m.val ∧ m.val ≤ 3 ∧
    vmRightsOf m = Fl4Spec.maskVmRights (vmRightsOf rights) (Fl4Spec.dataToRights mask.bv) ∧
    o = ({(.ok (.frameMap
      (if specFrameEntry (vmRightsOf m) ptr.bv (frameSizeOf size = .x64LargePage) attr.bv = 0 then
        .pageCap dev ptr.bv (vmRightsOf rights) .vmNoMap (frameSizeOf size) none
      else .pageCap dev ptr.bv (vmRightsOf rights) .vmEptMap (frameSizeOf size) (some (asid1.bv, g.bv)))
      sl t.bv (Fl4Spec.guestIndex g.bv (fbits size).val)
      (specFrameEntry (vmRightsOf m) ptr.bv (frameSizeOf size = .x64LargePage) attr.bv)), σ)}, False) ∧
    ∃ s2 val mp a' v', sched.set_thread_state st s ct sched.TS_RESTART = ok s2 ∧
      val.bv = specFrameEntry (vmRightsOf m) ptr.bv (frameSizeOf size = .x64LargePage) attr.bv ∧
      (mp, a', v') = (if (val != 0#u64) = true then (true, asid1, g) else (false, 0#u64, 0#u64)) ∧
      res = (.Ok (), L.wr (wrCap (L := L) s2 dest (.Frame ptr size rights dev mp mp a' v'))
        (eptA t (Fl4Spec.guestIndex g.bv (fbits size).val)) val, a))

variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
  Fl4Proofs.P1

theorem one_shl_val {n : Nat} (hn : n < 64) : (⟨(1#u64 : U64).bv <<< n⟩ : U64).val = 2 ^ n := by
  show ((1#u64 : U64).bv <<< n).toNat = _
  rw [show (1#u64 : U64).bv = 1#64 from rfl]
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have h2 : 2 ^ n < 2 ^ 64 := (zv_pow64 hn).2
  first
    | (simp only [BitVec.toNat_ofNat, Nat.one_mod_two_pow (by decide : 0 < 64), Nat.one_mul]
       exact Nat.mod_eq_of_lt h2)
    | (simp; exact Nat.mod_eq_of_lt h2)
    | (simp; exact h2)
    | (simp [Nat.mod_eq_of_lt h2]; exact h2)

set_option maxHeartbeats 4000000 in
/-- **The frame map's decode past the guest-address bound** (module docstring). -/
theorem EptCore.frameMapDec (C : EptCore (L := L) X XL th s σ) {P : Set U64} (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hVA : ZvVirtAgree arI) (a : A) {len ptr rights asid va : U64} {size : capability.FrameSize} {dev ep : Bool}
    (dest buf : U64) (ex : Array obj.Slot 3#usize) (hrw : 1 ≤ rights.val ∧ rights.val ≤ 3)
    (hl : ¬ len.val < 3) (hz : exAt ex 0 ≠ 0#u64) (hxe : IsSlot th (exAt ex 0)) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {i mask attr : U64}
    (hsa : msg.syscall_arg st s ct buf 0#u64 = ok i) (hsm : msg.syscall_arg st s ct buf 1#u64 = ok mask)
    (hsr : msg.syscall_arg st s ct buf 2#u64 = ok attr)
    (hg : ¬ (i.bv &&& ~~~(4095 : Fl4Spec.Word)) ≥ Fl4Spec.guestGpaLimit)
    (args : List Fl4Spec.Data) (ha0 : args.getD 0 0 = i.bv) (ha1 : args.getD 1 0 = mask.bv)
    (ha2 : args.getD 2 0 = attr.bv) (hn : ¬ args.length < 3)
    (sl sl0 : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    ∃ g : U64, g.bv = (i.bv &&& ~~~(4095 : Fl4Spec.Word)) ∧ g.val < 2 ^ 47 ∧
    ∃ res, ept.map_frame st arI s a len (.Frame ptr size rights dev false ep asid va) dest buf ex = ok res ∧
      FrameDecOut (L := L) X XL σ s a ct dest ptr size rights dev g mask attr sl res
        (ExceptT.run (Fl4Spec.decodePageMapEpt (Z := Unit) args sl
          (.pageCap dev ptr.bv (vmRightsOf rights) .vmNoMap (frameSizeOf size) none)
          ((absCap (capV (L.mem s) (exAt ex 0)), sl0) :: rest)) σ) := by
  obtain ⟨i5, hi5, hi5v⟩ := spec_exists Fl4Proofs.P0.Consts.ept.LIMIT.spec
  have hgb : U64.bv (i &&& ~~~4095#u64) = (i.bv &&& ~~~(4095 : Fl4Spec.Word)) := by
    show UScalar.bv (i &&& ~~~4095#u64) = _
    rw [UScalar.bv_and, UScalar.bv_not]
    rfl
  have hgv : (i &&& ~~~4095#u64).val < 2 ^ 47 := gpa_lt_of (g := i &&& ~~~4095#u64) (by rw [hgb]; exact hg)
  refine ⟨i &&& ~~~4095#u64, hgb, hgv, ?_⟩
  generalize hG : (i &&& ~~~4095#u64 : U64) = g at hgb hgv
  have hge : ¬ g >= i5 := by
    subst hi5v
    show ¬ (140737488355328#u64).val ≤ g.val
    have : (140737488355328#u64 : U64).val = 2 ^ 47 := rfl
    omega
  -- FL4: to the root
  unfold ept.map_frame
  have g3 : ¬ len < 3#u64 := by scalar_tac
  rw [if_neg g3, zv_ex0Idx, bind_ok, zv_ex0Null, bind_ok,
    if_neg (show ¬ (decide (exAt ex 0 = 0#u64) = true) by simpa using hz), hct, bind_ok, hsa, bind_ok]
  simp only [lift, bind_ok, hi5, hG]
  rw [if_neg hge, hsm, bind_ok, hsr, bind_ok]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [slot_cap_eq, capAt_capV, bind_ok]
  obtain ⟨r, hr, o, ho, hro⟩ := P1.spec_ex_fd (ept_root_rel (st := st) s σ hR (capV (L.mem s) (exAt ex 0)))
  rw [hr, bind_ok]
  -- the spec, to the root
  obtain ⟨gw, hgw⟩ : ∃ gw : Fl4Spec.Word, g.bv = gw := ⟨_, rfl⟩
  have hD : ExceptT.run (Fl4Spec.decodePageMapEpt (Z := Unit) args sl
      (.pageCap dev ptr.bv (vmRightsOf rights) .vmNoMap (frameSizeOf size) none)
      ((absCap (capV (L.mem s) (exAt ex 0)), sl0) :: rest)) σ =
      ExceptT.run (do
        let (r, asid) ← Fl4Spec.eptCapRoot (absCap (capV (L.mem s) (exAt ex 0)))
        let bits := Fl4Spec.pageBitsForSize (frameSizeOf size)
        Fl4Spec.NonDetE.whenE (gw &&& (((1 : Fl4Spec.Word) <<< bits) - (1 : Fl4Spec.Word)) ≠ 0) <|
          Fl4Spec.NonDetE.throwError .alignmentError
        Fl4Spec.NonDetE.whenE (frameSizeOf size = .x64HugePage) <| Fl4Spec.NonDetE.throwError (.invalidCapability 0)
        let tbl ← Fl4Spec.guestSlot r g.bv bits
        let (_, es) ← Fl4Spec.NonDetE.liftE (Fl4Spec.getEpt tbl)
        Fl4Spec.NonDetE.whenE (es (Fl4Spec.guestIndex g.bv bits) &&& 1 ≠ 0) <|
          Fl4Spec.NonDetE.throwError .deleteFirst
        let rr := Fl4Spec.maskVmRights (vmRightsOf rights) (Fl4Spec.dataToRights mask.bv)
        let entry : Fl4Spec.Word := if rr = Fl4Spec.vmKernelOnly then 0
          else Fl4Spec.GuestPte.encode Fl4Spec.virtKind
            (.frame (Fl4Spec.addrFromPPtr ptr.bv) (frameSizeOf size = .x64LargePage) (rr ≠ Fl4Spec.vmReadOnly)
              (Fl4Spec.guestMemoryType attr.bv))
        let newCap := if entry = 0 then Fl4Spec.ArchCap.pageCap dev ptr.bv (vmRightsOf rights) .vmNoMap
            (frameSizeOf size) none
          else .pageCap dev ptr.bv (vmRightsOf rights) .vmEptMap (frameSizeOf size) (some (asid, g.bv))
        Fl4Spec.NonDetE.returnOk (Fl4Spec.EptInvocation.frameMap newCap sl tbl (Fl4Spec.guestIndex g.bv bits) entry)
        : Fl4Spec.SEMonad Unit Fl4Spec.EptInvocation) σ := by
    unfold Fl4Spec.decodePageMapEpt
    rw [if_neg (fun h => h.elim hn (List.cons_ne_nil _ _)), ha0]
    refine run_seq_ok (by
      unfold Fl4Spec.NonDetE.whenE
      rw [if_neg (show ¬ (i.bv &&& ~~~(4095 : Fl4Spec.Word) ≥ Fl4Spec.guestGpaLimit) from hg)]
      rfl) ?_
    have hgb2 : UScalar.bv g = i.bv &&& ~~~(4095 : Fl4Spec.Word) := hgb
    rw [← hgw, hgb2, ha1, ha2] <;> rfl
  rw [hD]
  rcases hro with ⟨e, e', rfl, rfl, hee⟩ | ⟨rt, asid1, va1, ent, hc0, rfl, rfl, hge1, h1, hrt⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.convert.FromSame, lift, bind_tc_ok, bind_ok]
    exact ⟨_, rfl, Or.inl ⟨e, e', rfl, hee, run_seq_err ho rfl⟩⟩
  have ha20 : asid1.val < 2 ^ 20 := by
    have h := capAt_capV (L.mem s) (exAt ex 0)
    rw [capAt_words] at h
    have h2 := decode_encWf h
    rw [hc0] at h2
    exact h2.2.2.1
  have hAnz : asid1 ≠ 0#u64 := C.exte.anz _ hxe _ _ _ _ hc0
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [bits_eq]
  show ∃ res, (do let i3 ← ok (fbits size); _) = ok res ∧ _
  rw [bind_ok, shl_u64_eq _ _ (fbits_lt size), bind_ok]
  obtain ⟨i3, hi3, hi3v, -⟩ := spec_exists (U64.sub_spec (x := (⟨(1#u64 : U64).bv <<< (fbits size).val⟩ : U64)) (y := 1#u64)
    (by rw [one_shl_val (fbits_lt size)]; have := (zv_pow64 (fbits_lt size)).1; scalar_tac))
  rw [hi3, bind_ok]
  have hm3 := zv_gpaMask (fbits_lt size) (one_shl_val (fbits_lt size)) hi3v
  have hal : U64.bv (g &&& i3) = gw &&& (((1 : Fl4Spec.Word) <<< Fl4Spec.pageBitsForSize (frameSizeOf size)) - (1 : Fl4Spec.Word)) := by
    show UScalar.bv (g &&& i3) = _
    have hm3' : UScalar.bv i3 = ((1#64 : BitVec 64) <<< (fbits size).val) - (1#64 : BitVec 64) := hm3
    rw [UScalar.bv_and, hm3', fbits_val, ← hgw] <;> rfl
  have hroot : (Fl4Spec.eptCapRoot (Z := Unit) (absCap (capV (L.mem s) (exAt ex 0)))).run σ =
      ({(.ok (rt.bv, asid1.bv), σ)}, False) := ho
  by_cases hA : (g &&& i3 != 0#u64) = true
  · -- the alignment error
    rw [if_pos hA]
    refine ⟨_, rfl, Or.inl ⟨.Sys .AlignmentError, .alignmentError, rfl, Or.inl trivial, ?_⟩⟩
    refine run_seq_ok hroot ?_
    dsimp only
    refine run_seq_err ?_ rfl
    unfold Fl4Spec.NonDetE.whenE
    rw [if_pos (by
      rw [← hal]
      intro h0
      have : g &&& i3 = 0#u64 := P1.eq_of_bv (h0.trans (by rfl))
      exact (bne_iff_ne.mp hA) this)]
    rfl
  rw [if_neg hA]
  have hA0 : gw &&& (((1 : Fl4Spec.Word) <<< Fl4Spec.pageBitsForSize (frameSizeOf size)) - (1 : Fl4Spec.Word)) = 0 := by
    rw [← hal]
    have : g &&& i3 = 0#u64 := by
      by_contra hne
      exact hA (bne_iff_ne.mpr hne)
    rw [this]; rfl
  have hsp1 : (Fl4Spec.NonDetE.whenE
      (gw &&& (((1 : Fl4Spec.Word) <<< Fl4Spec.pageBitsForSize (frameSizeOf size)) - (1 : Fl4Spec.Word)) ≠ 0)
      (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.alignmentError) :
        Fl4Spec.NonDetE (Fl4Spec.State Unit) Fl4Spec.SyscallError Unit).run σ = ({(Except.ok (), σ)}, False) := by
    unfold Fl4Spec.NonDetE.whenE
    rw [if_neg (not_not.mpr hA0)]
    rfl
  cases size with
  | Huge =>
    dsimp only
    rw [bind_ok, if_pos rfl, show error.invalid_cap Unit 0#u64 = ok (.Err (.Sys (.InvalidCapability 0#u64))) from rfl,
      bind_ok]
    refine ⟨_, rfl, Or.inl ⟨.Sys (.InvalidCapability 0#u64), .invalidCapability 0, rfl, Or.inr ⟨0#u64, rfl, rfl⟩, ?_⟩⟩
    refine run_seq_ok hroot ?_
    dsimp only
    refine run_seq_ok hsp1 ?_
    refine run_seq_err ?_ rfl
    unfold Fl4Spec.NonDetE.whenE
    rw [if_pos (show frameSizeOf capability.FrameSize.Huge = .x64HugePage from rfl)]
    rfl
  | Small =>
    dsimp only
    rw [bind_ok, if_neg (by decide)]
    rw [bind_ok]
    have hsp2 : (Fl4Spec.NonDetE.whenE
        (frameSizeOf capability.FrameSize.Small = .x64HugePage) (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 0)) :
          Fl4Spec.NonDetE (Fl4Spec.State Unit) Fl4Spec.SyscallError Unit).run σ = ({(Except.ok (), σ)}, False) := by
      unfold Fl4Spec.NonDetE.whenE
      rw [if_neg (by intro h; cases h)]
      rfl
    -- the walk
    show ∃ res, (do
        let r2 ← ept.slot st s rt g (fbits capability.FrameSize.Small)
        _) = ok res ∧ _
    have hlv4 : (fbits capability.FrameSize.Small).val = 39 ∨ (fbits capability.FrameSize.Small).val = 30 ∨ (fbits capability.FrameSize.Small).val = 21 ∨ (fbits capability.FrameSize.Small).val = 12 := by
      first | (right; right; right; rfl) | (right; right; left; rfl)
    obtain ⟨root, hrX, hrb, hr0, hlk⟩ := C.lookup hge1.guest h1 hgv hlv4
    have hrr : root = rt := P1.eq_of_bv (hrb.trans hrt.symm)
    subst hrr
    unfold ept.slot
    have hbv := fbits_val capability.FrameSize.Small
    rcases hlk with ⟨t, ht, hXt, hreach, hpath, hlr, hlo⟩ | ⟨sh, hlr, hlo⟩
    · rw [hlr, bind_ok]
      simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      rw [L.read_eq, bind_ok]
      obtain ⟨es, hk, hwd⟩ := C.rel.obj t ht
      have hXt0 : XL t ≠ 0 := by
        rw [hXt]; simp [fbits, lkLvl]
      have b1 := ew_and (hwd (Fl4Spec.guestIndex g.bv (fbits capability.FrameSize.Small).val) (Or.inl hXt0)) mask1_ok
      have hslot : (Fl4Spec.guestSlot (Z := Unit) root.bv g.bv (Fl4Spec.pageBitsForSize (frameSizeOf capability.FrameSize.Small))).run σ =
          ({(.ok t.bv, σ)}, False) := by
        unfold Fl4Spec.guestSlot
        rw [hrb, ← hbv]
        exact runE_handleE_ok hlo
      have hgE : (Fl4Spec.NonDetE.liftE (ε := Fl4Spec.SyscallError) (Fl4Spec.getEpt (Z := Unit) t.bv)).run σ =
          ({(.ok (XL t, es), σ)}, False) := run_liftE (getEpt_eq hk)
      by_cases hp : L.mem s (eptA t (Fl4Spec.guestIndex g.bv (fbits capability.FrameSize.Small).val)) &&& 1#u64 = 0#u64
      · have hpb : (L.mem s (eptA t (Fl4Spec.guestIndex g.bv (fbits capability.FrameSize.Small).val)) &&& 1#u64 != 0#u64) = false := by
          simpa using hp
        have hes : es (Fl4Spec.guestIndex g.bv (fbits capability.FrameSize.Small).val) &&& 1 = 0 := by
          have := (u_and_zero _ _).1 hp
          exact b1.symm.trans this
        rw [hpb]
        simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨m, hm, hm1, hm3, hmr⟩ := vm_rights_rel rights mask hrw
        obtain ⟨vi', val', hvi', hfe', hval'⟩ := frame_entry_spec hVA a ptr m attr hm1 hm3 false
        rw [hvi', bind_ok, from_word_eq, bind_ok, hm, bind_ok]
        rw [hfe', bind_ok]
        obtain ⟨s2, hs2, -⟩ := P1.spec_ex_fd (set_thread_state_cases (L := L) s ct sched.TS_RESTART)
        rw [hs2, bind_ok]
        have hlg : false = decide (frameSizeOf capability.FrameSize.Small = .x64LargePage) := by
          rfl
        have hpage : (if (val' != 0#u64) = true then
              (ok (true, asid1, g) : Result (Bool × U64 × U64)) else ok (false, 0#u64, 0#u64)) =
            ok (if (val' != 0#u64) = true then (true, asid1, g) else (false, 0#u64, 0#u64)) := by
          split <;> rfl
        rw [hpage, bind_ok]
        generalize hT : (if (val' != 0#u64) = true then (true, asid1, g) else (false, 0#u64, 0#u64)) = T
        obtain ⟨mp, a', v'⟩ := T
        show ∃ res, (do
            let s3 ← obj.Slot.set_cap st dest s2 (capability.Cap.Frame ptr capability.FrameSize.Small rights dev mp mp a' v')
            _) = ok res ∧ _
        rw [set_cap_eq, bind_ok, L.write_eq, bind_ok]
        refine ⟨_, rfl, Or.inr ⟨t, asid1, m, ht, hXt, ha20, hAnz, (fun h => by cases h), hpath _ _ hge1, hp, ⟨es, hk, hes⟩, hm, hm1, hm3,
          hmr, ?_, s2, val', mp, a', v', hs2, hval'.trans (congrArg (fun b => specFrameEntry (vmRightsOf m) ptr.bv b attr.bv) hlg), hT.symm, rfl⟩⟩
        refine run_seq_ok hroot ?_
        dsimp only
        refine run_seq_ok hsp1 ?_
        refine run_seq_ok hsp2 ?_
        refine run_seq_ok hslot ?_
        refine run_seq_ok hgE ?_
        dsimp only
        refine run_seq_ok (by
          unfold Fl4Spec.NonDetE.whenE
          rw [← hbv, if_neg (not_not.mpr hes)]
          rfl) ?_
        rw [← hmr, ← hbv]
        rfl
      · have hpb : (L.mem s (eptA t (Fl4Spec.guestIndex g.bv (fbits capability.FrameSize.Small).val)) &&& 1#u64 != 0#u64) = true := by
          simpa using hp
        have hne : es (Fl4Spec.guestIndex g.bv (fbits capability.FrameSize.Small).val) &&& 1 ≠ 0 := by
          intro h
          exact hp ((u_and_zero _ _).2 (b1.trans h))
        rw [hpb]
        simp only [↓reduceIte]
        refine ⟨_, rfl, Or.inl ⟨.Sys .DeleteFirst, .deleteFirst, rfl, Or.inl trivial, ?_⟩⟩
        refine run_seq_ok hroot ?_
        dsimp only
        refine run_seq_ok hsp1 ?_
        refine run_seq_ok hsp2 ?_
        refine run_seq_ok hslot ?_
        refine run_seq_ok hgE ?_
        dsimp only
        exact run_seq_err (by
          unfold Fl4Spec.NonDetE.whenE
          rw [← hbv, if_pos hne]
          rfl) rfl
    · rw [hlr, bind_ok]
      simp only [core.result.Result.map_err, ept.slot.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, core.convert.FromSame, lift, bind_tc_ok, bind_ok]
      refine ⟨_, rfl, Or.inl ⟨_, .failedLookup false (.missingCapability sh.val), rfl, Or.inl ⟨rfl, rfl⟩, ?_⟩⟩
      refine run_seq_ok hroot ?_
      dsimp only
      refine run_seq_ok hsp1 ?_
      refine run_seq_ok hsp2 ?_
      refine run_seq_err ?_ rfl
      unfold Fl4Spec.guestSlot
      rw [hrb, ← hbv, runE_handleE_err hlo]
      rfl

  | Large =>
    dsimp only
    rw [bind_ok, if_neg (by decide)]
    rw [bind_ok]
    have hsp2 : (Fl4Spec.NonDetE.whenE
        (frameSizeOf capability.FrameSize.Large = .x64HugePage) (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 0)) :
          Fl4Spec.NonDetE (Fl4Spec.State Unit) Fl4Spec.SyscallError Unit).run σ = ({(Except.ok (), σ)}, False) := by
      unfold Fl4Spec.NonDetE.whenE
      rw [if_neg (by intro h; cases h)]
      rfl
    -- the walk
    show ∃ res, (do
        let r2 ← ept.slot st s rt g (fbits capability.FrameSize.Large)
        _) = ok res ∧ _
    have hlv4 : (fbits capability.FrameSize.Large).val = 39 ∨ (fbits capability.FrameSize.Large).val = 30 ∨ (fbits capability.FrameSize.Large).val = 21 ∨ (fbits capability.FrameSize.Large).val = 12 := by
      first | (right; right; right; rfl) | (right; right; left; rfl)
    obtain ⟨root, hrX, hrb, hr0, hlk⟩ := C.lookup hge1.guest h1 hgv hlv4
    have hrr : root = rt := P1.eq_of_bv (hrb.trans hrt.symm)
    subst hrr
    unfold ept.slot
    have hbv := fbits_val capability.FrameSize.Large
    rcases hlk with ⟨t, ht, hXt, hreach, hpath, hlr, hlo⟩ | ⟨sh, hlr, hlo⟩
    · rw [hlr, bind_ok]
      simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      rw [L.read_eq, bind_ok]
      obtain ⟨es, hk, hwd⟩ := C.rel.obj t ht
      have hXt0 : XL t ≠ 0 := by
        rw [hXt]; simp [fbits, lkLvl]
      have b1 := ew_and (hwd (Fl4Spec.guestIndex g.bv (fbits capability.FrameSize.Large).val) (Or.inl hXt0)) mask1_ok
      have hslot : (Fl4Spec.guestSlot (Z := Unit) root.bv g.bv (Fl4Spec.pageBitsForSize (frameSizeOf capability.FrameSize.Large))).run σ =
          ({(.ok t.bv, σ)}, False) := by
        unfold Fl4Spec.guestSlot
        rw [hrb, ← hbv]
        exact runE_handleE_ok hlo
      have hgE : (Fl4Spec.NonDetE.liftE (ε := Fl4Spec.SyscallError) (Fl4Spec.getEpt (Z := Unit) t.bv)).run σ =
          ({(.ok (XL t, es), σ)}, False) := run_liftE (getEpt_eq hk)
      by_cases hp : L.mem s (eptA t (Fl4Spec.guestIndex g.bv (fbits capability.FrameSize.Large).val)) &&& 1#u64 = 0#u64
      · have hpb : (L.mem s (eptA t (Fl4Spec.guestIndex g.bv (fbits capability.FrameSize.Large).val)) &&& 1#u64 != 0#u64) = false := by
          simpa using hp
        have hes : es (Fl4Spec.guestIndex g.bv (fbits capability.FrameSize.Large).val) &&& 1 = 0 := by
          have := (u_and_zero _ _).1 hp
          exact b1.symm.trans this
        rw [hpb]
        simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨m, hm, hm1, hm3, hmr⟩ := vm_rights_rel rights mask hrw
        obtain ⟨vi', val', hvi', hfe', hval'⟩ := frame_entry_spec hVA a ptr m attr hm1 hm3 true
        rw [hvi', bind_ok, from_word_eq, bind_ok, hm, bind_ok]
        rw [hfe', bind_ok]
        obtain ⟨s2, hs2, -⟩ := P1.spec_ex_fd (set_thread_state_cases (L := L) s ct sched.TS_RESTART)
        rw [hs2, bind_ok]
        have hlg : true = decide (frameSizeOf capability.FrameSize.Large = .x64LargePage) := by
          rfl
        have hpage : (if (val' != 0#u64) = true then
              (ok (true, asid1, g) : Result (Bool × U64 × U64)) else ok (false, 0#u64, 0#u64)) =
            ok (if (val' != 0#u64) = true then (true, asid1, g) else (false, 0#u64, 0#u64)) := by
          split <;> rfl
        rw [hpage, bind_ok]
        generalize hT : (if (val' != 0#u64) = true then (true, asid1, g) else (false, 0#u64, 0#u64)) = T
        obtain ⟨mp, a', v'⟩ := T
        show ∃ res, (do
            let s3 ← obj.Slot.set_cap st dest s2 (capability.Cap.Frame ptr capability.FrameSize.Large rights dev mp mp a' v')
            _) = ok res ∧ _
        rw [set_cap_eq, bind_ok, L.write_eq, bind_ok]
        refine ⟨_, rfl, Or.inr ⟨t, asid1, m, ht, hXt, ha20, hAnz, (fun h => by cases h), hpath _ _ hge1, hp, ⟨es, hk, hes⟩, hm, hm1, hm3,
          hmr, ?_, s2, val', mp, a', v', hs2, hval'.trans (congrArg (fun b => specFrameEntry (vmRightsOf m) ptr.bv b attr.bv) hlg), hT.symm, rfl⟩⟩
        refine run_seq_ok hroot ?_
        dsimp only
        refine run_seq_ok hsp1 ?_
        refine run_seq_ok hsp2 ?_
        refine run_seq_ok hslot ?_
        refine run_seq_ok hgE ?_
        dsimp only
        refine run_seq_ok (by
          unfold Fl4Spec.NonDetE.whenE
          rw [← hbv, if_neg (not_not.mpr hes)]
          rfl) ?_
        rw [← hmr, ← hbv]
        rfl
      · have hpb : (L.mem s (eptA t (Fl4Spec.guestIndex g.bv (fbits capability.FrameSize.Large).val)) &&& 1#u64 != 0#u64) = true := by
          simpa using hp
        have hne : es (Fl4Spec.guestIndex g.bv (fbits capability.FrameSize.Large).val) &&& 1 ≠ 0 := by
          intro h
          exact hp ((u_and_zero _ _).2 (b1.trans h))
        rw [hpb]
        simp only [↓reduceIte]
        refine ⟨_, rfl, Or.inl ⟨.Sys .DeleteFirst, .deleteFirst, rfl, Or.inl trivial, ?_⟩⟩
        refine run_seq_ok hroot ?_
        dsimp only
        refine run_seq_ok hsp1 ?_
        refine run_seq_ok hsp2 ?_
        refine run_seq_ok hslot ?_
        refine run_seq_ok hgE ?_
        dsimp only
        exact run_seq_err (by
          unfold Fl4Spec.NonDetE.whenE
          rw [← hbv, if_pos hne]
          rfl) rfl
    · rw [hlr, bind_ok]
      simp only [core.result.Result.map_err, ept.slot.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, core.convert.FromSame, lift, bind_tc_ok, bind_ok]
      refine ⟨_, rfl, Or.inl ⟨_, .failedLookup false (.missingCapability sh.val), rfl, Or.inl ⟨rfl, rfl⟩, ?_⟩⟩
      refine run_seq_ok hroot ?_
      dsimp only
      refine run_seq_ok hsp1 ?_
      refine run_seq_ok hsp2 ?_
      refine run_seq_err ?_ rfl
      unfold Fl4Spec.guestSlot
      rw [hrb, ← hbv, runE_handleE_err hlo]
      rfl

end

end

end Fl4Proofs.P3
