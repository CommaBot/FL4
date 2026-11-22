/-
P3 (DESIGN.md §9), invariant line G1 (g5g, KENTRY-PLAN g5g): **the memory
half of l4v `untyped_ranges_zero`** (spec side only; outside the `JAtZ` cone).

For a set `D` of (non-device) data pages and a set `F` of byte addresses (the
free parts of the untyped caps, SpecInvUtZW):
`YP D F σ := DisjF D F ∧ PgIn D σ ∧ MemZ F σ` — no byte of a page of `D` is in
`F`, every non-device data page of the heap is in `D`, and the memory is zero
on `F`. The family `YK D F m := IK (YP D F) m` is sg1's idle-pointer family
SpecInvSgI1..I6 mechanically renamed (proofs/scratch/g5g/mkyk.py), with new
leaves:
* `yk_setObject`: `set_object` asserts the type of the old object
  (`aType`), so a data page is replaced only by a data page of the same size
  and device flag, and no data page appears;
* machine operations: `MZ mop` (every byte keeps its value or becomes 0):
  every machine operation of the kernel but `storeWord` of a non-zero word and
  ReadFPU's `fl4FpuToFrame` (`clearMemory` / `freeMemory` write zeros);
  `yk_dmo`;
* `yk_storeWordOffs`: the store asserts `in_user_frame` and word alignment,
  so the eight bytes lie in a non-device data page of the heap, hence in a
  page of `D`, hence outside `F` (`storeWord_bytes`, `byte_inPage`);
* `yk_deleteObjects`: `freeMemory` writes zeros, `detype` removes objects;
* `yk_portIn` / `yk_portOut` take `MZ` of their machine operation.
Left out (with their callers): `retype_region` (it creates data pages),
ReadFPU's `invokeFl4Tcb` (`fl4FpuToFrame` writes a frame), and every shell
above them (the performs, `handle_invocation`, the syscalls, the events,
`fl4CallKernel`, the syscall entry): those are SpecInvUtZS's. Parts 2-6:
SpecInvUtZK2..K6.
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-! ## The predicate -/

/-- The bytes of the page at `o` of size `sz`. -/
def pgB (o : ObjRef) (sz : VMPageSize) : Set Nat := {a | o.toNat ≤ a ∧ a < o.toNat + 2 ^ pageBitsForSize sz}

/-- A set of pages (base, size). -/
abbrev PgSet := ObjRef → VMPageSize → Prop

/-- Every non-device data page of the heap is in `D`. -/
def PgIn (D : PgSet) (σ : State Unit) : Prop :=
  ∀ o sz, σ.kheap o = some (.archObj (.dataPage false sz)) → D o sz

/-- The memory is zero on `F`. -/
def MemZ (F : Set Nat) (σ : State Unit) : Prop :=
  ∀ a : Word, a.toNat ∈ F → σ.machineState.underlyingMemory a = 0

/-- No byte of a page of `D` is in `F`. -/
def DisjF (D : PgSet) (F : Set Nat) : Prop := ∀ o sz, D o sz → ∀ a, a ∈ pgB o sz → a ∉ F

/-- **The memory half** (module docstring). -/
def YP (D : PgSet) (F : Set Nat) (σ : State Unit) : Prop := DisjF D F ∧ PgIn D σ ∧ MemZ F σ

abbrev YK (D : PgSet) (F : Set Nat) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (YP D F) m
abbrev YKE (D : PgSet) (F : Set Nat) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (YP D F) m

variable {D : PgSet} {F : Set Nat}

/-! ## Machine operations writing only zeros -/

/-- Every byte keeps its value or becomes zero. -/
def MZ {α : Type} (m : NonDet MachineState α) : Prop :=
  ∀ ms x, x ∈ (m ms).1 → ∀ a, x.2.underlyingMemory a = ms.underlyingMemory a ∨ x.2.underlyingMemory a = 0

theorem mz_bind {α β : Type} {m : NonDet MachineState α} {g : α → NonDet MachineState β} (hm : MZ m)
    (hg : ∀ a, MZ (g a)) : MZ (m >>= g) := by
  intro ms x ⟨y, hy, hx⟩ a
  rcases hg y.1 y.2 x hx a with h | h
  · rw [h]; exact hm ms y hy a
  · exact Or.inr h

theorem mz_pure {α : Type} (a : α) : MZ (pure a : NonDet MachineState α) := by
  intro ms x hx a; rw [Set.mem_singleton_iff.1 hx]; exact Or.inl rfl

theorem mz_gets {α : Type} (g : MachineState → α) : MZ (NonDet.gets g) := by
  intro ms x hx a; rw [Set.mem_singleton_iff.1 hx]; exact Or.inl rfl

theorem mz_assert (P : Prop) : MZ (NonDet.assert P : NonDet MachineState Unit) := by
  intro ms x hx a; obtain ⟨-, rfl⟩ := hx; exact Or.inl rfl

theorem mz_stateAssert (P : MachineState → Prop) : MZ (NonDet.stateAssert P) := by
  intro ms x hx a; obtain ⟨-, rfl⟩ := hx; exact Or.inl rfl

theorem mz_selectF {α : Type} (S : Set α × Prop) : MZ (NonDet.selectF S : NonDet MachineState α) := by
  intro ms x hx a; obtain ⟨-, h⟩ := hx; rw [h]; exact Or.inl rfl

theorem mz_modify {g : MachineState → MachineState} (hg : ∀ ms, (g ms).underlyingMemory = ms.underlyingMemory) :
    MZ (NonDet.modify g) := by
  intro ms x hx a; rw [Set.mem_singleton_iff.1 hx]; exact Or.inl (congrFun (hg ms) a)

theorem mz_ite {α : Type} (c : Prop) [Decidable c] {m1 m2 : NonDet MachineState α} (h1 : MZ m1) (h2 : MZ m2) :
    MZ (if c then m1 else m2) := by
  split
  · exact h1
  · exact h2

theorem mz_machineRestLift {α : Type} (f : MachineRestMonad α) : MZ (machineRestLift f) := by
  unfold machineRestLift
  exact mz_bind (mz_gets _) fun _ => mz_bind (mz_selectF _) fun _ => mz_bind (mz_modify fun _ => rfl)
    fun _ => mz_pure _

theorem mz_machineOpLift (f : MachineRestMonad Unit) : MZ (machineOpLift f) := by
  unfold machineOpLift; exact mz_machineRestLift _

theorem mz_loadWord (p : Word) : MZ (loadWord p) := by
  unfold loadWord
  exact mz_bind (mz_gets _) fun _ => mz_bind (mz_assert _) fun _ => mz_pure _

/-- A fold of updates with zero values writes only zeros. -/
theorem foldl_upd_zero (f : Int → Word) (g : Int → Word8) :
    ∀ (l : List Int), (∀ i ∈ l, g i = 0) → ∀ (m : Word → Word8) (a : Word),
      (l.foldl (fun m i => Function.update m (f i) (g i)) m) a = m a ∨
        (l.foldl (fun m i => Function.update m (f i) (g i)) m) a = 0
  | [], _, m, a => Or.inl rfl
  | i :: l, hg, m, a => by
    rcases foldl_upd_zero f g l (fun j hj => hg j (List.mem_cons_of_mem _ hj)) (Function.update m (f i) (g i)) a
      with h | h
    · simp only [List.foldl_cons]
      rw [h]
      by_cases e : a = f i
      · subst e; rw [Function.update_self]; exact Or.inr (hg i (List.mem_cons_self ..))
      · rw [Function.update_of_ne e]; exact Or.inl rfl
    · exact Or.inr h

/-- A fold of updates leaves the other addresses. -/
theorem foldl_upd_other (f : Int → Word) (g : Int → Word8) :
    ∀ (l : List Int) (m : Word → Word8) (a : Word), (∀ i ∈ l, a ≠ f i) →
      (l.foldl (fun m i => Function.update m (f i) (g i)) m) a = m a
  | [], m, a, _ => rfl
  | i :: l, m, a, h => by
    simp only [List.foldl_cons]
    rw [foldl_upd_other f g l _ a (fun j hj => h j (List.mem_cons_of_mem _ hj)),
      Function.update_of_ne (h i (List.mem_cons_self ..))]

theorem getD_allZero {l : List Word8} (h : ∀ x ∈ l, x = 0) (k : Nat) : l.getD k 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases e : l[k]? with
  | none => rfl
  | some x => exact h x (List.mem_of_getElem? e)

theorem wordRsplit_zero : ∀ x ∈ (wordRsplit (0 : Word) : List Word8), x = 0 := by
  intro x hx
  unfold wordRsplit at hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  simp

theorem mz_storeWord0 (p : Word) : MZ (storeWord p 0) := by
  unfold storeWord
  refine mz_bind (mz_assert _) fun _ => ?_
  intro ms x hx a
  rw [Set.mem_singleton_iff.1 hx]
  exact foldl_upd_zero _ _ _ (fun i _ => getD_allZero wordRsplit_zero _) _ a

theorem mz_mapMx_storeWord0 (xs : List Word) : MZ (NonDet.mapMx (fun p => storeWord p 0) xs) := by
  induction xs with
  | nil => exact mz_pure _
  | cons x xs ih => exact mz_bind (mz_storeWord0 _) fun _ => ih

theorem mz_clearMemory (p : Word) (n : Nat) : MZ (clearMemory p n) := by
  unfold clearMemory; exact mz_mapMx_storeWord0 _

theorem mz_freeMemory (p : Word) (n : Nat) : MZ (freeMemory p n) := by
  unfold freeMemory; exact mz_mapMx_storeWord0 _

/-- The machine-operation combinators. -/
macro "mz_auto" : tactic => `(tactic| repeat' (first
  | exact mz_pure _ | exact mz_gets _ | exact mz_assert _ | exact mz_selectF _ | exact mz_stateAssert _
  | exact mz_machineRestLift _ | exact mz_machineOpLift _ | exact mz_storeWord0 _
  | exact mz_loadWord _ | exact mz_clearMemory _ _ | exact mz_freeMemory _ _
  | (refine mz_modify fun _ => rfl)
  | (refine mz_bind ?_ fun _ => ?_)
  | (refine mz_ite _ ?_ ?_)
  | split))

theorem mz_getCurrentTime : MZ getCurrentTime := by unfold getCurrentTime; mz_auto
theorem mz_getActiveIRQ (b : Bool) : MZ (getActiveIRQ b) := by unfold getActiveIRQ; mz_auto
theorem mz_maskInterrupt (m : Bool) (i : Irq) : MZ (maskInterrupt m i) := by unfold maskInterrupt; mz_auto
theorem mz_ackInterrupt (i : Irq) : MZ (ackInterrupt i) := by unfold ackInterrupt; mz_auto
theorem mz_ackDeadlineIRQ : MZ ackDeadlineIRQ := by unfold ackDeadlineIRQ ackInterrupt; mz_auto
theorem mz_setDeadline (d : Word64) : MZ (setDeadline d) := by unfold setDeadline; mz_auto
theorem mz_invalidateASID (v a : Word) : MZ (invalidateASID v a) := by unfold invalidateASID; mz_auto
theorem mz_invalidateTranslationSingleASID (v a : Word) : MZ (invalidateTranslationSingleASID v a) := by
  unfold invalidateTranslationSingleASID; mz_auto
theorem mz_invalidateLocalPageStructureCacheASID (v a : Word) : MZ (invalidateLocalPageStructureCacheASID v a) := by
  unfold invalidateLocalPageStructureCacheASID; mz_auto
theorem mz_readFpuState : MZ readFpuState := by unfold readFpuState; mz_auto
theorem mz_writeFpuState (v : FpuState) : MZ (writeFpuState v) := by unfold writeFpuState; mz_auto
theorem mz_enableFpu : MZ enableFpu := by unfold enableFpu; mz_auto
theorem mz_disableFpu : MZ disableFpu := by unfold disableFpu; mz_auto
theorem mz_isFpuEnable : MZ isFpuEnable := by unfold isFpuEnable; mz_auto
theorem mz_getFaultAddress : MZ getFaultAddress := by unfold getFaultAddress; mz_auto
theorem mz_in8 (p : Word16) : MZ (in8 p) := by unfold in8; mz_auto
theorem mz_in16 (p : Word16) : MZ (in16 p) := by unfold in16; mz_auto
theorem mz_in32 (p : Word16) : MZ (in32 p) := by unfold in32; mz_auto
theorem mz_out8 (p : Word16) (w : Word8) : MZ (out8 p w) := by unfold out8; mz_auto
theorem mz_out16 (p : Word16) (w : Word16) : MZ (out16 p w) := by unfold out16; mz_auto
theorem mz_out32 (p : Word16) (w : Word32) : MZ (out32 p w) := by unfold out32; mz_auto

/-- The named machine operations. -/
syntax "mz_leaf" : tactic
macro_rules | `(tactic| mz_leaf) => `(tactic| fail "no mz_leaf")
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_getCurrentTime)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_getActiveIRQ _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_maskInterrupt _ _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_ackInterrupt _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_ackDeadlineIRQ)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_setDeadline _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_invalidateASID _ _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_invalidateTranslationSingleASID _ _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_invalidateLocalPageStructureCacheASID _ _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_readFpuState)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_writeFpuState _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_enableFpu)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_disableFpu)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_isFpuEnable)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_getFaultAddress)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_in8 _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_in16 _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_in32 _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_out8 _ _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_out16 _ _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_out32 _ _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_loadWord _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_clearMemory _ _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_freeMemory _ _)
macro_rules | `(tactic| mz_leaf) => `(tactic| exact mz_machineOpLift _)
macro_rules | `(tactic| mz_leaf) => `(tactic| (mz_auto; done))

/-! ## `doMachineOp` -/

/-- A machine operation whose changed bytes miss `F` keeps `YP D F` (one start state). -/
theorem ikp_dmo_w {α : Type} {mop : NonDet MachineState α} (σ : State Unit)
    (hm : ∀ x ∈ (mop σ.machineState).1, ∀ a : Word,
      x.2.underlyingMemory a ≠ σ.machineState.underlyingMemory a → a.toNat ∈ F → x.2.underlyingMemory a = 0) :
    IKp (YP D F) σ (doMachineOp (Z := Unit) mop) := by
  intro hσ x hx
  unfold doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  have e1 := Set.mem_singleton_iff.1 h1
  simp only [Prod.mk.injEq] at e1
  obtain ⟨e1a, e1b⟩ := e1
  subst s1; subst ms0
  obtain ⟨hm2, e2⟩ := h2
  simp only at e2; subst s2
  rw [Set.mem_singleton_iff.1 h3] at hx
  rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨h1', h2', h3'⟩ := hσ
  refine ⟨h1', h2', fun a ha => ?_⟩
  show ms'.underlyingMemory a = 0
  by_cases e : ms'.underlyingMemory a = σ.machineState.underlyingMemory a
  · rw [e]; exact h3' a ha
  · exact hm _ hm2 a e ha

theorem yk_dmo {α : Type} {mop : NonDet MachineState α} (hm : MZ mop) : YK D F (doMachineOp (Z := Unit) mop) := by
  intro σ hσ
  refine ikp_dmo_w σ (fun x hx a hne _ => ?_) hσ
  rcases hm _ x hx a with e | e
  · exact absurd e hne
  · exact e

/-! ## `set_object` -/

theorem aType_dp {old : KernelObject} {sz : VMPageSize}
    (h : aType old = aType (.archObj (.dataPage false sz))) : old = .archObj (.dataPage false sz) := by
  cases old with
  | archObj ao =>
    cases ao with
    | dataPage dev sz' =>
      cases dev
      · simp only [aType, aaType, Bool.false_eq_true, ↓reduceIte, KernelObject.archObj.injEq, AType.aArch.injEq,
          AAType.aUserData.injEq] at h
        rw [h]
      · simp [aType, aaType] at h
    | _ => simp [aType, aaType] at h
  | cnode sz cs => simp only [aType] at h; split_ifs at h <;> cases h
  | schedContext s n => simp only [aType] at h; split_ifs at h <;> cases h
  | _ => simp [aType] at h

theorem yk_setObject (p : ObjRef) (o : KernelObject) : YK D F (setObject (Z := Unit) p o) := by
  unfold setObject
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨old, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨h1, h2, h3⟩ := hσ
  refine ⟨h1, fun o' sz ho' => ?_, h3⟩
  simp only [Function.update_apply] at ho'
  split_ifs at ho' with e
  · subst e
    cases ho'
    exact h2 _ _ (by rw [hk]; exact congrArg some (aType_dp hty))
  · exact h2 _ _ ho'

/-! ## The IPC buffer store -/

theorem and7_iff' (a : Word) : a &&& mask 3 = 0 ↔ a.toNat % 8 = 0 := by
  have hm : (mask 3 : BitVec 64) = 7#64 := rfl
  rw [hm]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_and] at this
    have e : (7#64 : BitVec 64).toNat = 2 ^ 3 - 1 := rfl
    rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have e : (7#64 : BitVec 64).toNat = 2 ^ 3 - 1 := rfl
    rw [e, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h

theorem pageBits_mem' (vms : VMPageSize) : pageBitsForSize vms ∈ [12, 21, 30] := by
  cases vms <;> simp [pageBitsForSize, pageBits, ptTranslationBits]

theorem and_not_mask_toNat' (x : BitVec 64) (k : Nat) (hk : k ∈ [12, 21, 30]) :
    (x &&& ~~~(mask k : BitVec 64)).toNat = x.toNat / 2 ^ k * 2 ^ k := by
  have e : ~~~(mask k : BitVec 64) = BitVec.allOnes 64 <<< k := by
    simp at hk; rcases hk with rfl | rfl | rfl <;> decide
  rw [e, ← BitVec.shiftLeft_ushiftRight]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ _) x.isLt)]

theorem intUpto07 : intUpto 0 7 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide

theorem ofInt07 {i : Int} (hi : i ∈ intUpto 0 7) : ∃ j : Nat, j < 8 ∧ BitVec.ofInt 64 i = BitVec.ofNat 64 j := by
  rw [intUpto07] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, rfl⟩
  · exact ⟨1, by omega, rfl⟩
  · exact ⟨2, by omega, rfl⟩
  · exact ⟨3, by omega, rfl⟩
  · exact ⟨4, by omega, rfl⟩
  · exact ⟨5, by omega, rfl⟩
  · exact ⟨6, by omega, rfl⟩
  · exact ⟨7, by omega, rfl⟩

/-- **A byte of an aligned word lies in the page holding the word.** -/
theorem byte_inPage {q : Word} (hq : q.toNat % 8 = 0) (sz : VMPageSize) {j : Nat} (hj : j < 8) :
    (q + BitVec.ofNat 64 j).toNat ∈ pgB (q &&& ~~~(mask (pageBitsForSize sz) : BitVec 64)) sz := by
  have hk := pageBits_mem' sz
  rw [pgB, Set.mem_setOf_eq, and_not_mask_toNat' _ _ hk, BitVec.toNat_add, BitVec.toNat_ofNat]
  have hlt := q.isLt
  have hj' : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega)
  rw [hj']
  have h64 : q.toNat + j < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h64]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with h | h | h <;> rw [h] <;> simp only [Nat.reducePow] <;> omega

/-- **The store of an aligned word in a non-device data page keeps `YP D F`.** -/
theorem ikp_dmo_store (σ : State Unit) (q v : Word)
    (hu : inUserFrame q σ) : IKp (YP D F) σ (doMachineOp (Z := Unit) (storeWord q v)) := by
  intro hσ
  obtain ⟨sz, hsz⟩ := hu
  refine ikp_dmo_w σ (fun x hx a hne ha => ?_) hσ
  exfalso
  unfold storeWord at hx
  obtain ⟨y, ⟨hq, rfl⟩, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx] at hne
  have hq' := (and7_iff' q).1 hq
  by_cases hin : ∃ i ∈ intUpto 0 7, a = q + BitVec.ofInt 64 i
  · obtain ⟨i, hi, rfl⟩ := hin
    obtain ⟨j, hj, e⟩ := ofInt07 hi
    rw [e] at ha
    exact hσ.1 _ _ (hσ.2.1 _ _ hsz) _ (byte_inPage hq' sz hj) ha
  · apply hne
    exact foldl_upd_other _ _ _ _ _ fun i hi e => hin ⟨i, hi, e⟩

theorem yk_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : YK D F (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  obtain ⟨z, ⟨hu, rfl⟩, hx⟩ := hx
  exact ikp_dmo_store σ _ v hu hσ x hx

/-! ## The other leaves -/

macro "yk_side" : tactic => `(tactic| first | (intro _ _ h; exact h) | (intro _ h; exact h) | trivial)

macro "yk0_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine yk_dmo ?_); mz_leaf)
  | ((with_reducible refine ik_doExtendedOp ?_ _); yk_side)
  | with_reducible exact ik_getObject _
  | with_reducible exact yk_setObject _ _
  | with_reducible exact yk_storeWordOffs _ _ _
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

theorem yk_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    YK D F (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo; yk0_auto

theorem yk_threadSet (f : Tcb → Tcb) (t : ObjRef) : YK D F (threadSet (Z := Unit) f t) := by
  unfold threadSet; yk0_auto

theorem yk_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : YK D F (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; yk0_auto

theorem yk_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : YK D F (asUser (Z := Unit) t u) := by
  unfold asUser; yk0_auto

theorem yk_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : YK D F (setMrs (Z := Unit) t b ms) := by
  unfold setMrs; yk0_auto

theorem yk_setCap (c : Cap) (sl : CslotPtr) : YK D F (setCap (Z := Unit) c sl) := by
  unfold setCap; yk0_auto

theorem yk_deleteObjects (ptr : Word) (bits : Nat) : YK D F (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  refine ik_bind (yk_dmo (mz_freeMemory _ _)) fun _ => ik_modify fun σ h => ?_
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun o sz ho => ?_, h3⟩
  by_cases hS : o ∈ {x | ptr ≤ x ∧ x ≤ ptr + 2 ^ bits - 1}
  · simp only [detype, if_pos hS] at ho; cases ho
  · simp only [detype, if_neg hS] at ho; exact h2 o sz ho

theorem yk_setThreadState (t : ObjRef) (ts : ThreadState) : YK D F (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (yk_threadSet _ _) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; yk0_auto

theorem yk_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α) :
    YK D F (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact yk_threadSet _ _

theorem yk_portIn (f : MachineMonad Data) (hf : MZ f) : YK D F (portIn (Z := Unit) f) := by
  unfold portIn; exact ik_bind (yk_dmo hf) fun _ => ik_pure _

theorem yk_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) (hf : MZ (f w)) :
    YK D F (portOut (Z := Unit) f w) := by
  unfold portOut; exact ik_bind (yk_dmo hf) fun _ => ik_pure _

syntax "yk_leaf" : tactic
macro_rules | `(tactic| yk_leaf) => `(tactic| fail "no yk_leaf")

macro "yk_auto" : tactic => `(tactic| repeat' (first | yk_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| yk_leaf) => `(tactic| ((with_reducible refine yk_dmo ?_); mz_leaf))
macro_rules | `(tactic| yk_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); yk_side))
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setObject _ _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_storeWordOffs _ _ _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setSimpleKo _ _ _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_threadSet _ _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archThreadSet _ _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_asUser _ _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setMrs _ _ _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setCap _ _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_deleteObjects _ _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setThreadState _ _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_optionUpdateThread _ _ _)
macro_rules | `(tactic| yk_leaf) => `(tactic| ((with_reducible refine yk_portIn _ ?_); mz_leaf))
macro_rules | `(tactic| yk_leaf) => `(tactic| ((with_reducible refine yk_portOut _ _ ?_); mz_leaf))

variable {PD : PgSet} {FS : Set Nat}

theorem yk_archActivateIdleThread (_t : ObjRef) : YK PD FS (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archActivateIdleThread _)

theorem yk_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : YK PD FS (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_threadGet _ _)

theorem yk_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : YK PD FS (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getTcbObjRef _ _)

theorem yk_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : YK PD FS (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_updateSchedContext _ _)

theorem yk_schedContextCancelYieldTo (thread : ObjRef) : YK PD FS (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextCancelYieldTo _)

theorem yk_getCap (a0 : CslotPtr) : YK PD FS (getCap (Z := Unit) a0) := by
  unfold getCap; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getCap _)

theorem yk_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : YK PD FS (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_lookupIpcBuffer _ _)

theorem yk_setMessageInfo (thread : ObjRef) (info : MessageInfo) : YK PD FS (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setMessageInfo _ _)

theorem yk_replyFromKernel (thread : ObjRef) (x : Data × List Data) : YK PD FS (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_replyFromKernel _ _)

theorem yk_getSchedContext (ptr : ObjRef) : YK PD FS (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getSchedContext _)

theorem yk_schedContextUpdateConsumed (scPtr : ObjRef) : YK PD FS (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextUpdateConsumed _)

theorem yk_setConsumed (scPtr tcbPtr : ObjRef) : YK PD FS (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setConsumed _ _)

theorem yk_completeYieldTo (tcbPtr : ObjRef) : YK PD FS (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_completeYieldTo _)

theorem yk_getThreadState (ref : ObjRef) : YK PD FS (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getThreadState _)

theorem yk_setSchedulerAction (action : SchedulerAction) : YK PD FS (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setSchedulerAction _)

theorem yk_setThreadStateAct (tcbPtr : ObjRef) : YK PD FS (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setThreadStateAct _)

theorem yk_activateThread  : YK PD FS (activateThread (Z := Unit)) := by
  unfold activateThread; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_activateThread)

theorem yk_archCheckIrq (_irq : Data) : YKE PD FS (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archCheckIrq _)

theorem yk_ensureEmpty (slot : CslotPtr) : YKE PD FS (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_ensureEmpty _)

theorem yk_isIoportRangeFree (f l : IoPort) : YK PD FS (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_isIoportRangeFree _ _)

theorem yk_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : YKE PD FS m) : YKE PD FS (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; yk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_lookupErrorOnFailure _ _ ?_)

theorem yk_resolveAddressBits' (p : Cap × CapRef) : YKE PD FS (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by yk_auto)) fun nc => ?_
        split
        · exact yk_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_resolveAddressBits' _)

theorem yk_resolveAddressBits (a0 : Cap × CapRef) : YKE PD FS (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_resolveAddressBits _)

theorem yk_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : YKE PD FS (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_lookupSlotForCnodeOp _ _ _ _)

theorem yk_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : YKE PD FS (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_lookupTargetSlot _ _ _)

theorem yk_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : YKE PD FS (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeIoportControlInvocation _ _ _ _ _)

theorem yk_getAsidPool (ptr : ObjRef) : YK PD FS (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getAsidPool _)

theorem yk_findVspaceForAsid (asid : Asid) : YKE PD FS (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_findVspaceForAsid _)

theorem yk_getPdpt (ptr : ObjRef) : YK PD FS (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getPdpt _)

theorem yk_getPdpte (ptr : ObjRef) : YK PD FS (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getPdpte _)

theorem yk_isFinalCap (cap : Cap) : YK PD FS (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_isFinalCap _)

theorem yk_getPml4 (ptr : ObjRef) : YK PD FS (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getPml4 _)

theorem yk_getPml4e (ptr : ObjRef) : YK PD FS (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getPml4e _)

theorem yk_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : YKE PD FS (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_lookupPdptSlot _ _)

theorem yk_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : YKE PD FS (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodePageDirectoryInvocation _ _ _ _ _)

theorem yk_checkVpAlignment (sz : VMPageSize) (vptr : Word) : YKE PD FS (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_checkVpAlignment _ _)

theorem yk_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : YKE PD FS (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_lookupPdSlot _ _)

theorem yk_getPd (ptr : ObjRef) : YK PD FS (getPd (Z := Unit) ptr) := by
  unfold getPd; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getPd _)

theorem yk_getPde (ptr : ObjRef) : YK PD FS (getPde (Z := Unit) ptr) := by
  unfold getPde; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getPde _)

theorem yk_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : YKE PD FS (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_lookupPtSlot _ _)

theorem yk_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : YKE PD FS (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_createMappingEntries _ _ _ _ _ _)

theorem yk_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : YKE PD FS (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_ensureSafeMapping _)

theorem yk_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : YKE PD FS (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodePageInvocation _ _ _ _ _)

theorem yk_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : YKE PD FS (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodePageTableInvocation _ _ _ _ _)

theorem yk_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : YKE PD FS (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodePdptInvocation _ _ _ _ _)

theorem yk_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : YKE PD FS (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_ensurePortOperationAllowed _ _ _)

theorem yk_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : YKE PD FS (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodePortInvocation _ _ _)

theorem yk_ensureNoChildren (cslotPtr : CslotPtr) : YKE PD FS (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_ensureNoChildren _)

theorem yk_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : YK PD FS (selectExt (Z := Unit) a S) := by
  unfold selectExt; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_selectExt _ _)

theorem yk_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : YKE PD FS (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archDecodeInvocation _ _ _ _ _ _)

theorem yk_getIrqState (irq : Irq) : YK PD FS (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getIrqState _)

theorem yk_isIrqActive (irq : Irq) : YK PD FS (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_isIrqActive _)

theorem yk_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : YKE PD FS (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archDecodeIrqControlInvocation _ _ _ _)

theorem yk_archDeriveCap (c : ArchCap) : YKE PD FS (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archDeriveCap _)

theorem yk_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : YK PD FS (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_hwAsidInvalidate _ _)

theorem yk_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : YK PD FS (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setAsidPool _ _)

theorem yk_getCurrentCr3  : YK PD FS (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getCurrentCr3)

theorem yk_setCurrentCr3 (c : Cr3) : YK PD FS (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setCurrentCr3 _)

theorem yk_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : YK PD FS (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setCurrentVspaceRoot _ _)

theorem yk_setVmRoot (tcb : ObjRef) : YK PD FS (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setVmRoot _)

theorem yk_deleteAsid (asid : Asid) (pml4 : ObjRef) : YK PD FS (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_deleteAsid _ _)

theorem yk_deleteAsidPool (base : Asid) (ptr : ObjRef) : YK PD FS (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_deleteAsidPool _ _)

theorem yk_getPt (ptr : ObjRef) : YK PD FS (getPt (Z := Unit) ptr) := by
  unfold getPt; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getPt _)

theorem yk_getPte (ptr : ObjRef) : YK PD FS (getPte (Z := Unit) ptr) := by
  unfold getPte; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getPte _)

theorem yk_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : YK PD FS (setPd (Z := Unit) ptr pd) := by
  unfold setPd; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setPd _ _)

theorem yk_storePde (p : ObjRef) (pde : PDE) : YK PD FS (storePde (Z := Unit) p pde) := by
  unfold storePde; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_storePde _ _)

theorem yk_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : YK PD FS (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setPdpt _ _)

theorem yk_storePdpte (p : ObjRef) (pte : PDPTE) : YK PD FS (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_storePdpte _ _)
end

end Fl4Proofs.P3.SInvUZ
