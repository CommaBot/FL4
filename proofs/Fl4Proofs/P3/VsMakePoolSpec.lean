/-
P3 (DESIGN.md §9), VSpace: the spec side of ASIDControl `MakePool`.

* the decode (l4v `arch_decode_invocation` for `ASIDControlCap`): after the
  ASID-table read, the free-entry choice (`mpSel`; any free entry, FL4 takes
  the first), and the checks after it (`mpRest`): the untyped cap, its size,
  no children (`ensure_no_children`), the target slot (`lookup_target_slot`,
  `ensure_empty`);
* the perform (l4v `perform_asid_control_invocation`): after
  `delete_objects`, a single outcome (`mpPerf_eq`): the untyped cap's free
  index set to its size, the pool object (`retype_region`), the cap insert
  and the ASID-table entry.
-/
import Fl4Proofs.P3.UntypedResetRetype
import Fl4Proofs.P3.VsExt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Spec
open Fl4Spec

/-- The spec's MakePool decode after the free ASID-table entry (`base`). -/
def mpRest (index depth : Data) (untyped : Cap) (parentSlot : CslotPtr) (root : Cap) (base : ObjRef) :
    SEMonad Unit ArchInvocation :=
  have jp : ObjRef × Nat → SEMonad Unit ArchInvocation := fun x =>
    match x with
    | (p, n) => do
      let frame ← (if n = pageBits then do
          ensureNoChildren parentSlot
          NonDetE.returnOk p
        else NonDetE.throwError (.invalidCapability 1) : SEMonad Unit ObjRef)
      let destSlot ← lookupTargetSlot root (toBl index) (unat depth)
      ensureEmpty destSlot
      NonDetE.returnOk (.invokeASIDControl (.makePool frame destSlot parentSlot base))
  match untyped with
  | .untypedCap false p n _f => do
    let x ← NonDetE.returnOk (p, n)
    jp x
  | _ => do
    let x ← NonDetE.throwError (.invalidCapability 1)
    jp x

theorem mpDecode_eq {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64ASIDControlMakePool)
    (a0 a1 : Data) (rest : List Data) (xs : CapRef) (cte : CslotPtr) (uc : Cap) (ps : CslotPtr) (rc : Cap)
    (rs : CslotPtr) (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    ExceptT.run (archDecodeInvocation (Z := Unit) lbl (a0 :: a1 :: rest) xs cte .asidControlCap
      ((uc, ps) :: (rc, rs) :: ex)) σ =
    ExceptT.run (do
      let asidTable ← NonDetE.liftE (NonDet.gets fun s : State Unit => s.archState.x64AsidTable)
      let freeSet ← NonDetE.returnOk (dom asidTable)ᶜ
      NonDetE.whenE (freeSet = ∅) (NonDetE.throwError (ε := SyscallError) .deleteFirst)
      let free ← NonDetE.liftE (selectExt (fun _ => freeAsidSelect asidTable) freeSet)
      let base ← NonDetE.returnOk (ucast asidRepLen free <<< asidLowBits)
      mpRest a0 a1 uc ps rc base) σ := by
  unfold archDecodeInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp)]
  rfl

theorem selectExt_eq {D : Type} {a : State DetExt → D} {S' : Set D} {σ : State Unit} :
    selectExt (Z := Unit) a S' σ = ({y | y.1 ∈ S' ∧ y.2 = σ}, False) := by
  simp only [selectExt, nd_bind_apply', NonDet.get, NonDet.select, NonDet.assert, StateExt.selectSwitch,
    NonDet.pure, pure, Bool.false_eq_true, ↓reduceIte]
  ext y
  · simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    simp
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨hx, rfl⟩
    · rintro ⟨h1, h2⟩; exact ⟨y.1, h1, Prod.ext rfl h2⟩
  · simp

theorem runE_liftE_select {ε D β : Type} {a : State DetExt → D} {S' : Set D} {f : D → NonDetE (State Unit) ε β}
    {σ : State Unit} :
    ExceptT.run (NonDetE.liftE (selectExt (Z := Unit) a S') >>= f) σ =
      ({r | ∃ x ∈ S', r ∈ (ExceptT.run (f x) σ).1}, ∃ x ∈ S', (ExceptT.run (f x) σ).2) := by
  show NonDet.bind (NonDet.bind (selectExt a S') (fun a => NonDet.pure (Except.ok a))) (ExceptT.bindCont f) σ = _
  unfold NonDet.bind NonDet.pure
  rw [selectExt_eq]
  ext r
  · simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, ⟨z, ⟨hz1, hz2⟩, rfl⟩, hy⟩
      obtain ⟨z1, z2⟩ := z
      simp only at hz1 hz2 hy
      subst hz2
      exact ⟨z1, hz1, hy⟩
    · rintro ⟨x, hx, hr⟩
      exact ⟨(.ok x, σ), ⟨(x, σ), ⟨hx, rfl⟩, rfl⟩, hr⟩
  · simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨y, ⟨z, ⟨hz1, hz2⟩, rfl⟩, hy⟩)
      · rcases h with h | ⟨_, _, h⟩
        · exact h.elim
        · exact h.elim
      · obtain ⟨z1, z2⟩ := z
        simp only at hz1 hz2 hy
        subst hz2
        exact ⟨z1, hz1, hy⟩
    · rintro ⟨x, hx, hr⟩
      exact Or.inr ⟨(.ok x, σ), ⟨(x, σ), ⟨hx, rfl⟩, rfl⟩, hr⟩

theorem runE_ret_bind {ε α β : Type} (x : α) (f : α → NonDetE (State Unit) ε β) (σ : State Unit) :
    ExceptT.run (NonDetE.returnOk x >>= f) σ = ExceptT.run (f x) σ := runE_bind_ok (runE_ret _ σ)

/-- The decode after the table read. -/
def mpSel (σ : State Unit) (a0 a1 : Data) (uc : Cap) (ps : CslotPtr) (rc : Cap) : SEMonad Unit ArchInvocation := do
  let free ← NonDetE.liftE (selectExt (fun _ => freeAsidSelect σ.archState.x64AsidTable)
    (dom σ.archState.x64AsidTable)ᶜ)
  let base ← NonDetE.returnOk (ucast asidRepLen free <<< asidLowBits)
  mpRest a0 a1 uc ps rc base

theorem mp_prefix {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64ASIDControlMakePool)
    (a0 a1 : Data) (rest : List Data) (xs : CapRef) (cte : CslotPtr) (uc : Cap) (ps : CslotPtr) (rc : Cap)
    (rs : CslotPtr) (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    ExceptT.run (archDecodeInvocation (Z := Unit) lbl (a0 :: a1 :: rest) xs cte .asidControlCap
      ((uc, ps) :: (rc, rs) :: ex)) σ =
    ExceptT.run (do
      NonDetE.whenE ((dom σ.archState.x64AsidTable)ᶜ = ∅) (NonDetE.throwError (ε := SyscallError) .deleteFirst)
      mpSel σ a0 a1 uc ps rc) σ := by
  rw [mpDecode_eq hl, runE_bind_ok (runE_liftE (show NonDet.gets _ σ = ({(σ.archState.x64AsidTable, σ)}, False) from rfl)),
    runE_bind_ok (runE_ret _ σ)]
  unfold mpSel
  rfl

theorem mp_full {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64ASIDControlMakePool)
    (a0 a1 : Data) (rest : List Data) (xs : CapRef) (cte : CslotPtr) (uc : Cap) (ps : CslotPtr) (rc : Cap)
    (rs : CslotPtr) (ex : List (Cap × CslotPtr)) (σ : State Unit) (hF : (dom σ.archState.x64AsidTable)ᶜ = ∅) :
    ExceptT.run (archDecodeInvocation (Z := Unit) lbl (a0 :: a1 :: rest) xs cte .asidControlCap
      ((uc, ps) :: (rc, rs) :: ex)) σ = ({(.error .deleteFirst, σ)}, False) := by
  rw [mp_prefix hl]
  exact runE_bind_err (by rw [runE_whenE_true hF]; rfl)

theorem mp_sel {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64ASIDControlMakePool)
    (a0 a1 : Data) (rest : List Data) (xs : CapRef) (cte : CslotPtr) (uc : Cap) (ps : CslotPtr) (rc : Cap)
    (rs : CslotPtr) (ex : List (Cap × CslotPtr)) (σ : State Unit) (hF : (dom σ.archState.x64AsidTable)ᶜ ≠ ∅) :
    ExceptT.run (archDecodeInvocation (Z := Unit) lbl (a0 :: a1 :: rest) xs cte .asidControlCap
      ((uc, ps) :: (rc, rs) :: ex)) σ = ExceptT.run (mpSel σ a0 a1 uc ps rc) σ := by
  rw [mp_prefix hl, runE_bind_ok (runE_whenE_false hF _ σ)]

theorem mpSel_eq (σ : State Unit) (a0 a1 : Data) (uc : Cap) (ps : CslotPtr) (rc : Cap) :
    ExceptT.run (mpSel σ a0 a1 uc ps rc) σ =
      ({r | ∃ f ∈ (dom σ.archState.x64AsidTable)ᶜ,
          r ∈ (ExceptT.run (mpRest a0 a1 uc ps rc (ucast asidRepLen f <<< asidLowBits)) σ).1},
        ∃ f ∈ (dom σ.archState.x64AsidTable)ᶜ,
          (ExceptT.run (mpRest a0 a1 uc ps rc (ucast asidRepLen f <<< asidLowBits)) σ).2) := by
  unfold mpSel
  rw [runE_liftE_select]
  simp only [runE_ret_bind]

/-- The selection does not matter when every choice gives the same single
outcome. -/
theorem mpSel_const {σ : State Unit} {a0 a1 : Data} {uc : Cap} {ps : CslotPtr} {rc : Cap}
    (hF : (dom σ.archState.x64AsidTable)ᶜ ≠ ∅) {r : Except SyscallError ArchInvocation}
    (hk : ∀ f ∈ (dom σ.archState.x64AsidTable)ᶜ,
      ExceptT.run (mpRest a0 a1 uc ps rc (ucast asidRepLen f <<< asidLowBits)) σ = ({(r, σ)}, False)) :
    ExceptT.run (mpSel σ a0 a1 uc ps rc) σ = ({(r, σ)}, False) := by
  obtain ⟨f0, hf0⟩ := Set.nonempty_iff_ne_empty.2 hF
  rw [mpSel_eq]
  ext x
  · constructor
    · rintro ⟨f, hf, hx⟩; rw [hk f hf] at hx; exact hx
    · intro hx; exact ⟨f0, hf0, by rw [hk f0 hf0]; exact hx⟩
  · constructor
    · rintro ⟨f, hf, hx⟩; rw [hk f hf] at hx; exact hx
    · exact False.elim

/-- One choice of the selection gives `inv`, and no choice fails. -/
theorem mpSel_mem {σ : State Unit} {a0 a1 : Data} {uc : Cap} {ps : CslotPtr} {rc : Cap}
    {f : AsidHighIndex} (hf : f ∈ (dom σ.archState.x64AsidTable)ᶜ) {inv : ArchInvocation}
    (hk : ExceptT.run (mpRest a0 a1 uc ps rc (ucast asidRepLen f <<< asidLowBits)) σ = ({(.ok inv, σ)}, False))
    (hall : ∀ f' ∈ (dom σ.archState.x64AsidTable)ᶜ,
      ¬ (ExceptT.run (mpRest a0 a1 uc ps rc (ucast asidRepLen f' <<< asidLowBits)) σ).2) :
    (.ok inv, σ) ∈ (ExceptT.run (mpSel σ a0 a1 uc ps rc) σ).1 ∧ ¬ (ExceptT.run (mpSel σ a0 a1 uc ps rc) σ).2 := by
  rw [mpSel_eq]
  exact ⟨⟨f, hf, by rw [hk]; rfl⟩, fun ⟨f', hf', h⟩ => hall f' hf' h⟩

theorem mpRest_bad {a0 a1 : Data} {uc : Cap} {ps : CslotPtr} {rc : Cap} {base : ObjRef} {σ : State Unit}
    (huc : ∀ p n fi, uc ≠ .untypedCap false p n fi) :
    ExceptT.run (mpRest a0 a1 uc ps rc base) σ = ({(.error (.invalidCapability 1), σ)}, False) := by
  unfold mpRest
  split
  · rename_i p n fi; exact absurd rfl (huc p n fi)
  · exact runE_bind_err (runE_throw _ σ)

theorem mpRest_size {a0 a1 : Data} {p : ObjRef} {n fi : Nat} {ps : CslotPtr} {rc : Cap} {base : ObjRef}
    {σ : State Unit} (hn : n ≠ pageBits) :
    ExceptT.run (mpRest a0 a1 (.untypedCap false p n fi) ps rc base) σ =
      ({(.error (.invalidCapability 1), σ)}, False) := by
  unfold mpRest
  dsimp only
  rw [runE_bind_ok (runE_ret _ σ)]
  dsimp only
  exact runE_bind_err (by rw [if_neg hn]; rfl)

theorem mpRest_frame {a0 a1 : Data} {p : ObjRef} {fi : Nat} {ps : CslotPtr} {rc : Cap} {base : ObjRef}
    {σ : State Unit} :
    ExceptT.run (mpRest a0 a1 (.untypedCap false p pageBits fi) ps rc base) σ =
      ExceptT.run ((do
          ensureNoChildren (Z := Unit) ps
          NonDetE.returnOk (ε := SyscallError) p) >>= fun frame => do
        let destSlot ← lookupTargetSlot rc (toBl a0) (unat a1)
        ensureEmpty destSlot
        NonDetE.returnOk (ε := SyscallError) (ArchInvocation.invokeASIDControl (.makePool frame destSlot ps base))) σ := by
  unfold mpRest
  dsimp only
  rw [runE_bind_ok (runE_ret _ σ)]
  dsimp only
  rw [if_pos rfl]

theorem mpRest_children {a0 a1 : Data} {p : ObjRef} {fi : Nat} {ps : CslotPtr} {rc : Cap} {base : ObjRef}
    {σ : State Unit} (hc : ∃ x, σ.cdt x = some ps) :
    ExceptT.run (mpRest a0 a1 (.untypedCap false p pageBits fi) ps rc base) σ =
      ({(.error .revokeFirst, σ)}, False) := by
  rw [mpRest_frame]
  refine runE_bind_err (runE_bind_err ?_)
  rw [ensureNoChildren_run, if_pos hc]

theorem mpRest_noch {a0 a1 : Data} {p : ObjRef} {fi : Nat} {ps : CslotPtr} {rc : Cap} {base : ObjRef}
    {σ : State Unit} (hc : ¬ ∃ x, σ.cdt x = some ps) :
    ExceptT.run (mpRest a0 a1 (.untypedCap false p pageBits fi) ps rc base) σ =
      ExceptT.run (do
        let destSlot ← lookupTargetSlot rc (toBl a0) (unat a1)
        ensureEmpty destSlot
        NonDetE.returnOk (ε := SyscallError) (ArchInvocation.invokeASIDControl (.makePool p destSlot ps base))) σ := by
  rw [mpRest_frame]
  refine runE_bind_ok ?_
  rw [runE_bind_ok (by rw [ensureNoChildren_run, if_neg hc])]
  rfl

/-- `MakePool`'s perform after `delete_objects`. -/
def mpPerf (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) : SMonad Unit Unit := do
    let pcap ← getCap parent
    setCap (maxFreeIndexUpdate pcap) parent
    let _ ← retypeRegion frame 1 0 (.archObject .asidPoolObj) false
    capInsert (.archObjectCap (.asidPoolCap frame base)) parent slot
    NonDet.assert (asidLowBitsOf base = 0)
    let asidTable ← NonDet.gets fun s : State Unit => s.archState.x64AsidTable
    let asidTable' ← pure (Function.update asidTable (asidHighBitsOf base) (some frame))
    NonDet.modify fun s => { s with archState := { s.archState with x64AsidTable := asidTable' } }

theorem performMP_eq (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) :
    performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base) =
      (deleteObjects frame page_bits >>= fun _ => mpPerf frame slot parent base) := rfl

/-- The state after `retype_region` of the pool. -/
def mpRegion (τ : State Unit) (pp : ObjRef) (rs : Nat) (cs : CnodeContents) (idx : List Bool) (p : ObjRef) :
    State Unit :=
  regionHeap (setCnodeSlot τ pp rs cs idx (.untypedCap false p 12 4096)) (regionPtrs p 1 (2 ^ 12))
    (.archObj (.asidPool fun _ => none))

/-- The ASID table update. -/
def mpTable (τ : State Unit) (p : ObjRef) (base : Asid) : State Unit :=
  let t := Function.update τ.archState.x64AsidTable (asidHighBitsOf base) (some p)
  { τ with archState := { τ.archState with x64AsidTable := t } }

theorem mpPerf_eq {τ : State Unit} {pp : ObjRef} {rs : Nat} {cs : CnodeContents} {idx : List Bool} {p : ObjRef}
    {fi : Nat} (hk : τ.kheap pp = some (.cnode rs cs)) (hwf : wellFormedCnodeN rs cs) (hidx : idx.length = rs)
    (hgc : getCap (Z := Unit) (pp, idx) τ = ({(.untypedCap false p 12 fi, τ)}, False)) {dest : CslotPtr}
    {base : Asid} {τi : State Unit}
    (hci : capInsert (Z := Unit) (.archObjectCap (.asidPoolCap p base)) (pp, idx) dest (mpRegion τ pp rs cs idx p) =
      ({((), τi)}, False)) (hlow : asidLowBitsOf base = 0) :
    mpPerf p dest (pp, idx) base τ = ({((), mpTable τi p base)}, False) := by
  unfold mpPerf
  rw [nd_bind_single hgc]
  rw [nd_bind_one (setCap_cnode _ hk hwf hidx)]
  rw [nd_bind_one (s' := mpRegion τ pp rs cs idx p) (a := regionPtrs p 1 (2 ^ 12))
    (by rw [← retypeRegionWith_objBitsApi, retypeRegionWith_eq]; rfl)]
  rw [nd_bind_one hci]
  rw [nd_bind_single (show NonDet.assert (σ := State Unit) (asidLowBitsOf base = 0) τi = ({((), τi)}, False) by
    simp [NonDet.assert, hlow])]
  rw [nd_bind_single (gets_eq _ τi), nd_pure_bind]
  rfl

/-- The pool cap is in the untyped region (l4v `same_region_as`). -/
theorem sameRegion_pool {p : ObjRef} (hfit : p.toNat + 4096 ≤ 2 ^ 64) (base : Asid) (fi : Nat) :
    sameRegionAs (.untypedCap false p 12 fi) (.archObjectCap (.asidPoolCap p base)) := by
  have h4 : (Fl4Spec.objSize (.archObjectCap (.asidPoolCap p base)) : Word) = 4096#64 := rfl
  have h1 : ((1 : Word) <<< 12) = 4096#64 := rfl
  have hr : objRefOf (.archObjectCap (.asidPoolCap p base)) = p := rfl
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> rw [hr] <;> (try rw [h4]) <;> (try rw [h1])
  · exact BitVec.le_refl _
  · rw [BitVec.le_def, BitVec.toNat_sub, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
    have hp := p.isLt
    by_cases h : p.toNat + 4096 = 2 ^ 64
    · rw [h]; simp; omega
    · rw [Nat.mod_eq_of_lt (by omega : p.toNat + 4096 < 2 ^ 64)]
      rw [show 2 ^ 64 - 1 + (p.toNat + 4096) = (p.toNat + 4095) + 2 ^ 64 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
      omega
  · exact BitVec.le_refl _

theorem sbp_pool {p : ObjRef} (hfit : p.toNat + 4096 ≤ 2 ^ 64) (base : Asid) (fi : Nat) (b : Bool) :
    shouldBeParentOf (.untypedCap false p 12 fi) true (.archObjectCap (.asidPoolCap p base)) b :=
  ⟨rfl, sameRegion_pool hfit base fi, trivial⟩

/-- FL4's pool base `i << 9`: no low bits, high bits `i`. -/
theorem base_low {b : Asid} {i : Nat} (hb : b.toNat = i * 512) : asidLowBitsOf b = 0 := by
  unfold asidLowBitsOf asidLowLen ucast
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, hb]
  simp

theorem base_high {b : Asid} {i : Data} (hi : i.toNat < 2048) (hb : b.toNat = i.toNat * 512) :
    asidHighBitsOf b = ucast 11 i := by
  unfold asidHighBitsOf asidHighLen asidLowBits asidLowLen ucast
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, hb, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 9 = 512 from rfl, Nat.mul_div_cancel _ (by decide)]


/-- After the checks of the untyped cap: the target slot. -/
theorem mpRest_slot {a0 a1 : Data} {p : ObjRef} {fi : Nat} {ps : CslotPtr} {rc : Cap} {base : ObjRef}
    {σ : State Unit} (hc : ¬ ∃ x, σ.cdt x = some ps) {r : Except SyscallError CslotPtr}
    (hlt : (lookupTargetSlot (Z := Unit) rc (toBl a0) (unat a1)).run σ = ({(r, σ)}, False)) :
    ExceptT.run (mpRest a0 a1 (.untypedCap false p pageBits fi) ps rc base) σ =
      (match r with
       | .error e => ({(.error e, σ)}, False)
       | .ok d => ExceptT.run (do
          ensureEmpty (Z := Unit) d
          NonDetE.returnOk (ε := SyscallError)
            (ArchInvocation.invokeASIDControl (.makePool p d ps base))) σ) := by
  rw [mpRest_noch hc]
  cases r with
  | error e => exact runE_bind_err hlt
  | ok d => exact runE_bind_ok hlt

theorem mpRest_ok {a0 a1 : Data} {p : ObjRef} {fi : Nat} {ps : CslotPtr} {rc : Cap} {base : ObjRef}
    {σ : State Unit} (hc : ¬ ∃ x, σ.cdt x = some ps) {d : CslotPtr}
    (hlt : (lookupTargetSlot (Z := Unit) rc (toBl a0) (unat a1)).run σ = ({(.ok d, σ)}, False))
    (hee : (ensureEmpty (Z := Unit) d).run σ = ({(.ok (), σ)}, False)) :
    ExceptT.run (mpRest a0 a1 (.untypedCap false p pageBits fi) ps rc base) σ =
      ({(.ok (.invokeASIDControl (.makePool p d ps base)), σ)}, False) := by
  rw [mpRest_slot hc hlt]
  exact (runE_bind_ok hee).trans (runE_ret _ σ)

theorem mpRest_full {a0 a1 : Data} {p : ObjRef} {fi : Nat} {ps : CslotPtr} {rc : Cap} {base : ObjRef}
    {σ : State Unit} (hc : ¬ ∃ x, σ.cdt x = some ps) {d : CslotPtr}
    (hlt : (lookupTargetSlot (Z := Unit) rc (toBl a0) (unat a1)).run σ = ({(.ok d, σ)}, False))
    (hee : (ensureEmpty (Z := Unit) d).run σ = ({(.error .deleteFirst, σ)}, False)) :
    ExceptT.run (mpRest a0 a1 (.untypedCap false p pageBits fi) ps rc base) σ =
      ({(.error .deleteFirst, σ)}, False) := by
  rw [mpRest_slot hc hlt]
  exact runE_bind_err hee


/-! ## `delete_objects`: the outcomes -/

theorem doMachineOp_mem' {α : Type} {mop : NonDet MachineState α} {σ σ' : State Unit} {r : α}
    (h : (r, σ') ∈ (doMachineOp (Z := Unit) mop σ).1) :
    ∃ ms, (r, ms) ∈ (mop σ.machineState).1 ∧ σ' = { σ with machineState := ms } := by
  unfold doMachineOp at h
  simp only [nd_bind_apply', NonDet.gets, NonDet.selectF, NonDet.modify, Set.mem_setOf_eq,
    Set.mem_singleton_iff] at h
  obtain ⟨x, rfl, y, ⟨hy1, hy⟩, z, rfl, hz⟩ := h
  subst hy
  simp only [pure, NonDet.pure, Set.mem_singleton_iff, Prod.mk.injEq] at hz
  obtain ⟨rfl, rfl⟩ := hz
  exact ⟨_, hy1, rfl⟩

theorem foldl_update_ne {β : Type} (q x : Word) (v : Int → β) :
    ∀ (l : List Int) (m : Word → β), (∀ i ∈ l, x ≠ q + BitVec.ofInt 64 i) →
      (l.foldl (fun m i => Function.update m (q + BitVec.ofInt 64 i) (v i)) m) x = m x := by
  intro l
  induction l with
  | nil => intro m _; rfl
  | cons i l ih =>
    intro m h
    simp only [List.foldl_cons]
    rw [ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj)), Function.update_of_ne (h i (List.mem_cons_self ..))]

theorem storeWord_um {q w x : Word} {ms ms' : MachineState} {r : Unit} (h : (r, ms') ∈ (storeWord q w ms).1)
    (hx : ∀ i : Int, i ∈ intUpto 0 7 → x ≠ q + BitVec.ofInt 64 i) :
    ms'.underlyingMemory x = ms.underlyingMemory x := by
  unfold storeWord at h
  simp only [nd_bind_apply', NonDet.assert, NonDet.modify, Set.mem_setOf_eq, Set.mem_singleton_iff] at h
  obtain ⟨y, ⟨-, rfl⟩, hz⟩ := h
  simp only [Prod.mk.injEq] at hz
  obtain ⟨-, rfl⟩ := hz
  exact foldl_update_ne q x _ _ _ hx

theorem mapMx_um {L : List Word} {ms ms' : MachineState} {r : Unit} {x : Word}
    (h : (r, ms') ∈ (NonDet.mapMx (fun p => storeWord p 0) L ms).1)
    (hx : ∀ q ∈ L, ∀ i : Int, i ∈ intUpto 0 7 → x ≠ q + BitVec.ofInt 64 i) :
    ms'.underlyingMemory x = ms.underlyingMemory x := by
  induction L generalizing ms with
  | nil =>
    simp only [NonDet.mapMx, NonDet.pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rw [h.2]
  | cons q L ih =>
    simp only [NonDet.mapMx, NonDet.bind, Set.mem_setOf_eq] at h
    obtain ⟨y, hy, hz⟩ := h
    rw [ih hz (fun q' hq' => hx q' (List.mem_cons_of_mem _ hq')),
      storeWord_um hy (hx q (List.mem_cons_self ..))]

theorem intUpto07 {i : Int} (h : i ∈ intUpto 0 7) : ∃ k : Nat, k < 8 ∧ i = k := by
  unfold intUpto at h
  simp only [List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨k, by omega, by simp⟩

theorem uptoEnumStep_range {a : Word} {n : Nat} (hn3 : 3 ≤ n) (hn : n < 64) (ha : a.toNat % 8 = 0)
    (hfit : a.toNat + 2 ^ n ≤ 2 ^ 64) {q : Word}
    (hq : q ∈ uptoEnumStep a (a + BitVec.ofNat 64 wordSize) (a + 2 ^ n - 1)) :
    a.toNat ≤ q.toNat ∧ q.toNat + 8 ≤ a.toNat + 2 ^ n := by
  have h2 : ((2 : BitVec 64) ^ n).toNat = 2 ^ n := by
    rw [BitVec.toNat_pow]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hn)
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hp8 : 8 ∣ 2 ^ n := by
    have : 2 ^ n = 2 ^ 3 * 2 ^ (n - 3) := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]; exact Nat.dvd_mul_right _ _
  have hc : (a + 2 ^ n - 1 - a).toNat = 2 ^ n - 1 := by
    rw [show a + 2 ^ n - 1 - a = (2 : BitVec 64) ^ n - 1 by bv_omega]
    rw [BitVec.toNat_sub, h2]; simp; omega
  have hb : a + BitVec.ofNat 64 wordSize - a = 8#64 := by rw [show wordSize = 8 from rfl]; bv_omega
  unfold uptoEnumStep at hq
  split_ifs at hq with hlt
  · simp at hq
  · obtain ⟨xv, hxv, rfl⟩ := List.mem_map.1 hq
    rw [hb] at hxv ⊢
    unfold uptoEnum at hxv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hxv
    rw [List.mem_range'] at hk
    have hdiv : ((a + 2 ^ n - 1 - a) / 8#64).toNat = (2 ^ n - 1) / 8 := by
      rw [BitVec.toNat_udiv, hc]; rfl
    simp only [BitVec.toNat_ofNat, hdiv] at hk
    have hk' : k ≤ (2 ^ n - 1) / 8 := by omega
    have hk8 : 8 * k + 8 ≤ 2 ^ n := by omega
    have hkv : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add, BitVec.toNat_mul, hkv, show (8#64 : BitVec 64).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (show k * 8 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a.toNat + k * 8 < 2 ^ 64 by omega)]
    omega

/-- **The outcomes of `delete_objects`**: the heap without the region and a
machine state whose memory outside the region is unchanged. -/
theorem deleteObjects_mem {σ : State Unit} {a : Word} {n : Nat} (hn3 : 3 ≤ n) (hn : n < 64) (ha : a.toNat % 8 = 0)
    (hfit : a.toNat + 2 ^ n ≤ 2 ^ 64) {y : Unit × State Unit} (hy : y ∈ (deleteObjects (Z := Unit) a n σ).1) :
    ∃ ms : MachineState, y.2 = detype {x | a ≤ x ∧ x ≤ a + 2 ^ n - 1} { σ with machineState := ms } ∧
      ∀ x : Word, (x.toNat < a.toNat ∨ a.toNat + 2 ^ n ≤ x.toNat) →
        ms.underlyingMemory x = σ.machineState.underlyingMemory x := by
  unfold deleteObjects at hy
  simp only [nd_bind_apply', Set.mem_setOf_eq] at hy
  obtain ⟨⟨r, σ1⟩, h1, h2⟩ := hy
  obtain ⟨ms, hms, rfl⟩ := doMachineOp_mem' h1
  simp only [NonDet.modify, Set.mem_singleton_iff] at h2
  refine ⟨ms, by rw [h2], fun x hx => ?_⟩
  refine mapMx_um hms (fun q hq i hi e => ?_)
  obtain ⟨k, hk, rfl⟩ := intUpto07 hi
  obtain ⟨h3, h4⟩ := uptoEnumStep_range hn3 hn ha hfit hq
  have : x.toNat = q.toNat + k := by
    rw [e, BitVec.toNat_add]
    simp only [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
  omega

end Spec

end

end Fl4Proofs.P3.Vs
