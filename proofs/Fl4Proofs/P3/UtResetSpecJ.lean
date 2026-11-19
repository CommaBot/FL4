/-
P3 (DESIGN.md §9), untyped: **the spec's reset at `J`, exactly** (handoff
utj.md Round 12, item 3): the reset of a childless used RAM untyped cap at
`J` relates FL4's states to spec states that are outcomes of l4v
`reset_untyped_cap` themselves, not only up to the CSpace parts (`KSame`,
UntypedResetSpec's `RCont`/`TopP`).

* `storeWord0_out`, `mapStore0_out`: storing zeros over a list of words sets
  their bytes to zero and keeps every other part of the machine state.
* `upto8_bytes`: the bytes of the words of `uptoEnumStep a (a+8) c` are the
  range `[a, c]`.
* `clear_id`: `clear_memory` over bytes already zero is the identity;
  `deleteObjects_out`: `delete_objects`' outcome is the detype of the state
  with the region's bytes zeroed (`deleteObjects_sdrop`: `SDrop` and every
  field `JAtZ.drop` asks kept).
* `pp_ksm`: every outcome of `preemption_point` keeps the heap, the CDT, the
  original bits, the arch state and the memory bytes.
* `RContX`: running the chunks `k, .., 0` from `σk` to an outcome `y` makes
  `y` an outcome of the whole reset from `σ` (exact `RCont`):
  `reset_initX` after `delete_objects`, `RContX.step`/`done`/`preempt`
  across one chunk whose clear finds its bytes zero (`chunk_memX`), and the
  small case `reset_smallX`.
-/
import Fl4Proofs.P3.UtDropX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section Mach
open Fl4Spec

/-- The bytes of the 8-byte word at `q`. -/
def B8 (q y : Word) : Prop := ∃ k : Nat, k < 8 ∧ y = q + BitVec.ofNat 64 k

theorem fold_upd0 (q : Word) (v : Int → Word8) (hv : ∀ i, v i = 0) :
    ∀ (l : List Int) (m : Word → Word8),
      l.foldl (fun m i => Function.update m (q + BitVec.ofInt 64 i) (v i)) m =
        fun y => if ∃ i ∈ l, y = q + BitVec.ofInt 64 i then 0 else m y
  | [], m => by funext y; simp
  | i :: l, m => by
    simp only [List.foldl]
    rw [fold_upd0 q v hv l]
    funext y
    have hiff : (∃ j ∈ i :: l, y = q + BitVec.ofInt 64 j) ↔ y = q + BitVec.ofInt 64 i ∨
        ∃ j ∈ l, y = q + BitVec.ofInt 64 j := by
      constructor
      · rintro ⟨j, hj, e⟩
        rcases List.mem_cons.1 hj with rfl | hj
        · exact Or.inl e
        · exact Or.inr ⟨j, hj, e⟩
      · rintro (e | ⟨j, hj, e⟩)
        · exact ⟨i, List.mem_cons.2 (Or.inl rfl), e⟩
        · exact ⟨j, List.mem_cons.2 (Or.inr hj), e⟩
    by_cases h1 : ∃ j ∈ l, y = q + BitVec.ofInt 64 j
    · rw [if_pos h1, if_pos (hiff.2 (Or.inr h1))]
    · rw [if_neg h1]
      by_cases h2 : y = q + BitVec.ofInt 64 i
      · rw [if_pos (hiff.2 (Or.inl h2)), h2, Function.update_self, hv]
      · rw [if_neg (fun h => (hiff.1 h).elim h2 h1), Function.update_of_ne h2]

theorem intUpto_bytes (q y : Word) : (∃ i ∈ intUpto 0 7, y = q + BitVec.ofInt 64 i) ↔ B8 q y := by
  have h8 : ((7 : Int) - 0 + 1).toNat = 8 := rfl
  unfold intUpto
  rw [h8]
  constructor
  · rintro ⟨i, hi, e⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hi
    refine ⟨k, List.mem_range.1 hk, ?_⟩
    rw [e]; congr 1; simp
  · rintro ⟨k, hk, e⟩
    refine ⟨(0 : Int) + (k : Int), List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩, ?_⟩
    rw [e]; congr 1; simp

theorem getD_zero8 : ∀ (l : List Word8) (k : Nat), (∀ a ∈ l, a = 0) → l.getD k 0 = 0
  | [], _, _ => rfl
  | a :: l, 0, h => h a (List.mem_cons.2 (Or.inl rfl))
  | _ :: l, k + 1, h => getD_zero8 l k (fun b hb => h b (List.mem_cons.2 (Or.inr hb)))

theorem wordRsplit0_getD (k : Nat) : ((wordRsplit (0 : Word) : List Word8)).getD k 0 = 0 := by
  refine getD_zero8 _ k (fun a ha => ?_)
  unfold wordRsplit at ha
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
  simp

/-- **Storing a zero word** (module docstring). -/
theorem storeWord0_out {q : Word} {ms : MachineState} {x : Unit × MachineState}
    (hx : x ∈ (storeWord q 0 ms).1) :
    x.2 = { ms with underlyingMemory := fun y => if B8 q y then 0 else ms.underlyingMemory y } := by
  unfold storeWord at hx
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz
  rw [Set.mem_singleton_iff.1 hx]
  dsimp only
  rw [fold_upd0 q _ (fun i => wordRsplit0_getD _)]
  refine congrArg (fun u => ({ ms with underlyingMemory := u } : MachineState)) (funext fun y => ?_)
  by_cases h : B8 q y
  · rw [if_pos ((intUpto_bytes q y).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((intUpto_bytes q y).1 h')), if_neg h]

/-- **Storing zeros over a list of words** (module docstring). -/
theorem mapStore0_out : ∀ (l : List Word) (ms : MachineState) (x : Unit × MachineState),
    x ∈ (NonDet.mapMx (fun p => storeWord p 0) l ms).1 →
    x.2 = { ms with underlyingMemory := fun y => if ∃ q ∈ l, B8 q y then 0 else ms.underlyingMemory y }
  | [], ms, x, hx => by
    rw [Set.mem_singleton_iff.1 hx]
    have e : (fun y => if ∃ q ∈ ([] : List Word), B8 q y then (0 : Word8) else ms.underlyingMemory y) =
        ms.underlyingMemory := funext fun y => by simp
    rw [e]
  | a :: l, ms, x, hx => by
    obtain ⟨z, hz, hx⟩ := hx
    rw [mapStore0_out l z.2 x hx, storeWord0_out hz]
    refine congrArg (fun u => ({ ms with underlyingMemory := u } : MachineState)) (funext fun y => ?_)
    show (if ∃ q ∈ l, B8 q y then (0 : Word8) else (if B8 a y then 0 else ms.underlyingMemory y)) = _
    have hiff : (∃ q ∈ a :: l, B8 q y) ↔ B8 a y ∨ ∃ q ∈ l, B8 q y := by
      constructor
      · rintro ⟨q, hq, e⟩
        rcases List.mem_cons.1 hq with rfl | hq
        · exact Or.inl e
        · exact Or.inr ⟨q, hq, e⟩
      · rintro (e | ⟨q, hq, e⟩)
        · exact ⟨a, List.mem_cons.2 (Or.inl rfl), e⟩
        · exact ⟨q, List.mem_cons.2 (Or.inr hq), e⟩
    by_cases h1 : ∃ q ∈ l, B8 q y
    · rw [if_pos h1, if_pos (hiff.2 (Or.inr h1))]
    · rw [if_neg h1]
      by_cases h2 : B8 a y
      · rw [if_pos h2, if_pos (hiff.2 (Or.inl h2))]
      · rw [if_neg h2, if_neg (fun h => (hiff.1 h).elim h2 h1)]

theorem toNat_add_n_sub1 {a : Word} {n : Nat} (hn0 : 0 < n) (hfit : a.toNat + n ≤ 2 ^ 64) :
    (a + BitVec.ofNat 64 n - 1).toNat = a.toNat + n - 1 := by
  have hn : n ≤ 2 ^ 64 := by omega
  rcases Nat.lt_or_ge n (2 ^ 64) with hlt | hge
  · rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have h1 : (1 : Word).toNat = 1 := rfl
    rw [h1]
    rcases Nat.lt_or_ge (a.toNat + n) (2 ^ 64) with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · have : a.toNat + n = 2 ^ 64 := by omega
      rw [this, Nat.mod_self]; omega
  · have hn' : n = 2 ^ 64 := by omega
    have ha : a.toNat = 0 := by omega
    subst hn'
    have : a = 0 := BitVec.eq_of_toNat_eq (by rw [ha]; rfl)
    subst this
    decide

/-- **The bytes of the words of `uptoEnumStep a (a + 8) c`** are `[a, c]`
(`c = a + n - 1`, `8 ∣ a`, `8 ∣ n`, no wrap). -/
theorem upto8_bytes {a c : Word} {n : Nat} (ha : a.toNat % 8 = 0) (hn : n % 8 = 0) (hn0 : 0 < n)
    (hfit : a.toNat + n ≤ 2 ^ 64) (hc : c.toNat = a.toNat + n - 1) (y : Word) :
    (∃ q ∈ uptoEnumStep a (a + BitVec.ofNat 64 wordSize) c, B8 q y) ↔
      a.toNat ≤ y.toNat ∧ y.toNat < a.toNat + n := by
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  have hca : ¬ c < a := by rw [BitVec.lt_def, hc]; omega
  have hb : a + BitVec.ofNat 64 wordSize - a = 8#64 := by
    rw [add_sub_cancel_left]; rfl
  have hd : ((c - a) / 8#64).toNat = (n - 1) / 8 := by
    rw [BitVec.toNat_udiv, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hc]; omega), hc]
    have : (8#64 : Word).toNat = 8 := rfl
    rw [this]; congr 1; omega
  unfold uptoEnumStep uptoEnum
  rw [if_neg hca, hb, hd]
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [h0]
  have hy := y.isLt
  constructor
  · rintro ⟨q, hq, k, hk, rfl⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range'_1] at hj
    have hj8 : 8 * j + 8 ≤ n := by omega
    have e : (a + BitVec.ofNat 64 j * 8#64 + BitVec.ofNat 64 k).toNat = a.toNat + 8 * j + k := by
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h64, Nat.reduceMod]
      rw [h64] at hfit
      omega
    rw [e]; omega
  · rintro ⟨h1, h2⟩
    set d := y.toNat - a.toNat with hd'
    refine ⟨a + BitVec.ofNat 64 (d / 8) * 8#64, List.mem_map.2 ⟨BitVec.ofNat 64 (d / 8),
      List.mem_map.2 ⟨d / 8, by rw [List.mem_range'_1]; omega, rfl⟩, rfl⟩, d % 8, Nat.mod_lt _ (by decide), ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h64, Nat.reduceMod]
    rw [h64] at hfit hy
    omega

/-- `doMachineOp`'s outcomes. -/
theorem dmo_mem {α : Type} {mop : NonDet MachineState α} {σ : State Unit} {z : α × State Unit}
    (hz : z ∈ (doMachineOp (Z := Unit) mop σ).1) :
    ∃ ms', (z.1, ms') ∈ (mop σ.machineState).1 ∧ z.2 = { σ with machineState := ms' } := by
  unfold doMachineOp at hz
  obtain ⟨a, ha, hz⟩ := hz
  rw [Set.mem_singleton_iff.1 ha] at hz
  obtain ⟨⟨⟨r, ms'⟩, s'⟩, ⟨hb1, hb2⟩, hz⟩ := hz
  simp only at hb2
  subst hb2
  obtain ⟨c, hc, hz⟩ := hz
  rw [Set.mem_singleton_iff.1 hc] at hz
  rw [Set.mem_singleton_iff.1 hz]
  exact ⟨ms', hb1, rfl⟩

theorem dmo_has {α : Type} {mop : NonDet MachineState α} {σ : State Unit} {r : α} {ms' : MachineState}
    (h : (r, ms') ∈ (mop σ.machineState).1) :
    (r, { σ with machineState := ms' }) ∈ (doMachineOp (Z := Unit) mop σ).1 :=
  ⟨(σ.machineState, σ), Set.mem_singleton _, ((r, ms'), σ), ⟨h, rfl⟩, ((), { σ with machineState := ms' }),
    Set.mem_singleton _, Set.mem_singleton _⟩

/-- **Clearing bytes already zero** is the identity (module docstring). -/
theorem clear_id {a : Word} {n : Nat} (ha : a.toNat % 8 = 0) (hn : n % 8 = 0) (hn0 : 0 < n)
    (hfit : a.toNat + n ≤ 2 ^ 64) {σ : State Unit}
    (hz : ∀ y : Word, a.toNat ≤ y.toNat → y.toNat < a.toNat + n → σ.machineState.underlyingMemory y = 0) :
    ∀ x ∈ (doMachineOp (Z := Unit) (clearMemory a n) σ).1, x.2 = σ := by
  intro x hx
  obtain ⟨ms', hms, e⟩ := dmo_mem hx
  rw [e]
  unfold clearMemory at hms
  have h1 := mapStore0_out _ _ _ hms
  simp only at h1
  rw [h1]
  have hfun : (fun y => if ∃ q ∈ uptoEnumStep a (a + BitVec.ofNat 64 wordSize) (a + BitVec.ofNat 64 n - 1), B8 q y
      then (0 : Word8) else σ.machineState.underlyingMemory y) = σ.machineState.underlyingMemory := by
    funext y
    split_ifs with h
    · rw [upto8_bytes ha hn hn0 hfit (toNat_add_n_sub1 hn0 hfit) y] at h
      exact (hz y h.1 h.2).symm
    · rfl
  rw [hfun]

theorem clear_has {a : Word} (ha : a.toNat % 8 = 0) (n : Nat) (σ : State Unit) :
    ∃ x, x ∈ (doMachineOp (Z := Unit) (clearMemory a n) σ).1 := by
  obtain ⟨x, hx, -⟩ := (clearMemory_nsat (Z := Unit) ha n σ).2
  exact ⟨x, hx⟩

theorem pow2_word {sz : Nat} (hsz : sz < 64) : ((2 : Word) ^ sz) = BitVec.ofNat 64 (2 ^ sz) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_pow, BitVec.toNat_ofNat]
  have : (2 : BitVec 64).toNat = 2 := rfl
  rw [this]

/-- **`delete_objects`' outcome** (module docstring). -/
theorem deleteObjects_out {pu : Word} {sz : Nat} (hp : pu.toNat % 8 = 0) (hsz : 3 ≤ sz) (hsz' : sz < 64)
    (hfit : pu.toNat + 2 ^ sz ≤ 2 ^ 64) (σ : State Unit) {y : Unit × State Unit}
    (hy : y ∈ (deleteObjects (Z := Unit) pu sz σ).1) :
    y.2 = detype (regionSet pu sz) { σ with machineState := { σ.machineState with underlyingMemory :=
      fun x => if pu.toNat ≤ x.toNat ∧ x.toNat < pu.toNat + 2 ^ sz then 0 else σ.machineState.underlyingMemory x } } := by
  unfold deleteObjects at hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  obtain ⟨ms', hms, e⟩ := dmo_mem hz
  rw [e]
  unfold freeMemory at hms
  have h1 := mapStore0_out _ _ _ hms
  simp only at h1
  rw [h1]
  have hn8 : 2 ^ sz % 8 = 0 := by
    have : 8 ∣ 2 ^ sz := by
      have := Nat.pow_dvd_pow 2 hsz; simpa using this
    omega
  have hc : (pu + 2 ^ sz - 1).toNat = pu.toNat + 2 ^ sz - 1 := by
    rw [pow2_word hsz']; exact toNat_add_n_sub1 (Nat.two_pow_pos _) hfit
  have hfun : (fun x => if ∃ q ∈ uptoEnumStep pu (pu + BitVec.ofNat 64 wordSize) (pu + 2 ^ sz - 1),
      B8 q x then (0 : Word8) else σ.machineState.underlyingMemory x) = fun x =>
      if pu.toNat ≤ x.toNat ∧ x.toNat < pu.toNat + 2 ^ sz then 0 else σ.machineState.underlyingMemory x := by
    funext x
    have hb := upto8_bytes hp hn8 (Nat.two_pow_pos _) hfit hc x
    by_cases h : ∃ q ∈ uptoEnumStep pu (pu + BitVec.ofNat 64 wordSize) (pu + 2 ^ sz - 1), B8 q x
    · rw [if_pos h, if_pos (hb.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hb.2 h'))]
  rw [hfun]

theorem deleteObjects_has {pu : Word} (hp : pu.toNat % 8 = 0) (sz : Nat) (σ : State Unit) :
    ∃ y, y ∈ (deleteObjects (Z := Unit) pu sz σ).1 := by
  obtain ⟨y, hy, -⟩ := (deleteObjects_nsat (Z := Unit) hp sz σ).2
  exact ⟨y, hy⟩

end Mach

/-! ## The detype's facts for `JAtZ.drop` -/

section Drop
open Fl4Spec

/-- The state after `delete_objects` (`deleteObjects_out`). -/
def delSt (pu : Word) (sz : Nat) (σ : State Unit) : State Unit :=
  detype (regionSet pu sz) { σ with machineState := { σ.machineState with underlyingMemory :=
    fun x => if pu.toNat ≤ x.toNat ∧ x.toNat < pu.toNat + 2 ^ sz then 0 else σ.machineState.underlyingMemory x } }

theorem regionSet_iff' (p : U64) (x : ObjRef) (n : Nat) (hn : n < 64) (hfit : p.val + 2 ^ n ≤ 2 ^ 64) :
    x ∈ regionSet p.bv n ↔ p.val ≤ x.toNat ∧ x.toNat < p.val + 2 ^ n :=
  regionSet_iff p ⟨x⟩ n hn hfit

/-- **`SDrop` and the kept fields after `delete_objects`** (module docstring). -/
theorem delSt_facts (p sb : U64) (hsb : sb.val < 64) (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (σ : State Unit) :
    SDrop (RgOf p sb) σ (delSt p.bv sb.val σ) ∧ (delSt p.bv sb.val σ).cdt = σ.cdt ∧ (delSt p.bv sb.val σ).isOriginalCap = σ.isOriginalCap ∧
      (delSt p.bv sb.val σ).reprogramTimer = σ.reprogramTimer ∧ (delSt p.bv sb.val σ).curDomain = σ.curDomain ∧ (delSt p.bv sb.val σ).domainTime = σ.domainTime ∧
      (delSt p.bv sb.val σ).interruptStates = σ.interruptStates ∧ (delSt p.bv sb.val σ).interruptIrqNode = σ.interruptIrqNode ∧
      (delSt p.bv sb.val σ).archState = σ.archState ∧ (delSt p.bv sb.val σ).domainList = σ.domainList ∧ (delSt p.bv sb.val σ).domainStartIndex = σ.domainStartIndex ∧
      (∀ x, ¬ RgOf p sb x → (delSt p.bv sb.val σ).machineState.underlyingMemory x = σ.machineState.underlyingMemory x) ∧
      (∀ x : ObjRef, p.val ≤ x.toNat → x.toNat < p.val + 2 ^ sb.val → (delSt p.bv sb.val σ).machineState.underlyingMemory x = 0) := by
  refine ⟨⟨fun q hq => ?_, fun q hq => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, fun x hx => ?_, fun x h1 h2 => ?_⟩
  · exact if_pos hq
  · exact if_neg hq
  · exact if_neg (fun h => hx ((regionSet_iff' p x sb.val hsb hfit).2 h))
  · exact if_pos ⟨h1, h2⟩

/-- Every `delete_objects` outcome is `delSt`. -/
theorem deleteObjects_delSt (p sb : U64) (hp : p.val % 8 = 0) (hsz : 3 ≤ sb.val) (hsb : sb.val < 64)
    (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (σ : State Unit) {y : Unit × State Unit}
    (hy : y ∈ (deleteObjects (Z := Unit) p.bv sb.val σ).1) : y.2 = delSt p.bv sb.val σ :=
  deleteObjects_out hp hsz hsb hfit σ hy

end Drop

/-! ## The preemption point keeps the heap and the memory -/

section PP
open Fl4Spec Fl4Proofs.P3.Vs

/-- The heap, CDT, original bits, arch state and memory bytes. -/
def ksmF (σ : State Unit) :
    (ObjRef → Option KernelObject) × (CslotPtr → Option CslotPtr) × (CslotPtr → Bool) × ArchState ×
      (Word → Word8) :=
  (σ.kheap, σ.cdt, σ.isOriginalCap, σ.archState, σ.machineState.underlyingMemory)

/-- A machine operation keeping the memory bytes. -/
def MK {α : Type} (m : NonDet MachineState α) : Prop :=
  ∀ ms x, x ∈ (m ms).1 → x.2.underlyingMemory = ms.underlyingMemory

theorem mk_bind {α β : Type} {m : NonDet MachineState α} {g : α → NonDet MachineState β} (hm : MK m)
    (hg : ∀ a, MK (g a)) : MK (m >>= g) := by
  intro ms x ⟨y, hy, hx⟩
  exact (hg y.1 y.2 x hx).trans (hm ms y hy)

theorem mk_pure {α : Type} (a : α) : MK (pure a : NonDet MachineState α) := by
  intro ms x hx; rw [Set.mem_singleton_iff.1 hx]

theorem mk_gets {α : Type} (g : MachineState → α) : MK (NonDet.gets g) := by
  intro ms x hx; rw [Set.mem_singleton_iff.1 hx]

theorem mk_modify {g : MachineState → MachineState} (hg : ∀ ms, (g ms).underlyingMemory = ms.underlyingMemory) :
    MK (NonDet.modify g) := by
  intro ms x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg ms

theorem mk_getActiveIRQ (b : Bool) : MK (getActiveIRQ b) := by
  unfold getActiveIRQ
  refine mk_bind (mk_gets _) fun _ => mk_bind (mk_modify fun _ => rfl) fun _ => mk_bind (mk_gets _) fun _ => ?_
  split
  · exact mk_pure _
  · exact mk_pure _

theorem mk_getCurrentTime : MK getCurrentTime := by
  unfold getCurrentTime
  exact mk_bind (mk_modify fun _ => rfl) fun _ => mk_bind (mk_gets _) fun _ => mk_bind (mk_gets _) fun _ =>
    mk_bind (mk_pure _) fun _ => mk_bind (mk_pure _) fun _ => mk_bind (mk_modify fun _ => rfl) fun _ => mk_pure _

theorem ksm_doMachineOp {α : Type} {mop : NonDet MachineState α} (hm : MK mop) :
    FK ksmF (doMachineOp (Z := Unit) mop) := by
  intro σ x hx
  obtain ⟨ms', hms, e⟩ := dmo_mem hx
  rw [e]
  have := hm _ _ hms
  simp only [ksmF] at this ⊢
  rw [this]

theorem ksm_doExtendedOp (eop : DetExtMonad Unit) : FK ksmF (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)

/-- **The preemption point keeps the heap, the CDT, the original bits, the
arch state and the memory bytes.** -/
theorem pp_ksm : FKE ksmF (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive
  repeat' (first
    | exact ksm_doMachineOp (mk_getActiveIRQ _)
    | exact ksm_doMachineOp mk_getCurrentTime
    | exact ksm_doExtendedOp _
    | dk_step0)

theorem pp_ksm' {σ : State Unit} {y : Except Unit Unit × State Unit}
    (hy : y ∈ ((preemptionPoint (Z := Unit)).run σ).1) :
    y.2.kheap = σ.kheap ∧ y.2.cdt = σ.cdt ∧ y.2.isOriginalCap = σ.isOriginalCap ∧ y.2.archState = σ.archState ∧
      y.2.machineState.underlyingMemory = σ.machineState.underlyingMemory := by
  have e := pp_ksm σ y hy
  simp only [ksmF, Prod.mk.injEq] at e
  exact e

end PP

/-! ## Exact continuations of the reset -/

section Reset
open Fl4Spec
variable {dev : Bool} {pu : ObjRef} {sz : Nat} {pb : ObjRef} {r : Nat} {idx : List Bool}

theorem memE_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    {s : State Unit} {x : Except ε α × State Unit} (hx : x ∈ (m.run s).1) {a : α} (ha : x.1 = .ok a)
    {y : Except ε β × State Unit} (hy : y ∈ ((f a).run x.2).1) : y ∈ ((m >>= f).run s).1 := by
  rw [ExceptT.run_bind]
  refine ⟨x, hx, ?_⟩
  obtain ⟨x1, x2⟩ := x
  simp only at ha; subst ha
  exact hy

theorem memE_bind_err {ε α β : Type} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    {s : State Unit} {x : Except ε α × State Unit} (hx : x ∈ (m.run s).1) {e : ε} (he : x.1 = .error e) :
    ((.error e, x.2) : Except ε β × State Unit) ∈ ((m >>= f).run s).1 := by
  rw [ExceptT.run_bind]
  refine ⟨x, hx, ?_⟩
  obtain ⟨x1, x2⟩ := x
  simp only at he; subst he
  exact Set.mem_singleton _

theorem memE_liftE {ε α : Type} {m : NonDet (State Unit) α} {s : State Unit} {x : α × State Unit}
    (hx : x ∈ (m s).1) : ((.ok x.1, x.2) : Except ε α × State Unit) ∈ ((NonDetE.liftE (ε := ε) m).run s).1 := by
  rw [liftE_run]
  exact ⟨x, hx, Set.mem_singleton _⟩

theorem memE_liftE_inv {ε α : Type} {m : NonDet (State Unit) α} {s : State Unit} {y : Except ε α × State Unit}
    (hy : y ∈ ((NonDetE.liftE (ε := ε) m).run s).1) : ∃ x ∈ (m s).1, y = (.ok x.1, x.2) := by
  rw [liftE_run] at hy
  obtain ⟨x, hx, hy⟩ := hy
  exact ⟨x, hx, Set.mem_singleton_iff.1 hy⟩

variable (dev pu sz pb idx) in
/-- The exact continuation (module docstring). -/
def RContX (σ : State Unit) (k : Nat) (σk : State Unit) : Prop :=
  ∀ y, y ∈ ((NonDetE.mapMEx (chunkF dev pu sz pb idx) (chunks k)).run σk).1 →
    y ∈ ((resetUntypedCap (Z := Unit) (pb, idx)).run σ).1

/-- **A chunk's outcome**, its bytes zero before: the preemption point's
outcome after the cap's new free index. -/
theorem chunk_memX (hrcb : resetChunkBits = 16) (hp8 : pu.toNat % 8 = 0) (hidx : idx.length = r) (i : Nat)
    {σ : State Unit} {cs : CnodeContents} (hk : σ.kheap pb = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs)
    (hfit : (pu + (BitVec.ofNat 64 i <<< resetChunkBits)).toNat + 2 ^ resetChunkBits ≤ 2 ^ 64)
    (hz : ∀ y : Word, (pu + (BitVec.ofNat 64 i <<< resetChunkBits)).toNat ≤ y.toNat →
      y.toNat < (pu + (BitVec.ofNat 64 i <<< resetChunkBits)).toNat + 2 ^ resetChunkBits →
      σ.machineState.underlyingMemory y = 0)
    {y : Except Unit Unit × State Unit}
    (hy : y ∈ ((preemptionPoint (Z := Unit)).run
      (setCnodeSlot σ pb r cs idx (.untypedCap dev pu sz (i * 2 ^ resetChunkBits)))).1) :
    y ∈ ((chunkF dev pu sz pb idx i).run σ).1 := by
  obtain ⟨x, hx⟩ := clear_has (pu_al hrcb hp8 i) (2 ^ resetChunkBits) σ
  have hxe : x.2 = σ := clear_id (pu_al hrcb hp8 i) (by simp [hrcb]) (Nat.two_pow_pos _) hfit hz x hx
  unfold chunkF
  refine memE_bind (memE_liftE hx) rfl ?_
  rw [hxe]
  have hsc : (((), setCnodeSlot σ pb r cs idx (.untypedCap dev pu sz (i * 2 ^ resetChunkBits))) :
      Unit × State Unit) ∈ (setCap (Z := Unit) (.untypedCap dev pu sz (i * 2 ^ resetChunkBits)) (pb, idx) σ).1 := by
    rw [setCap_cnode _ hk hwf hidx]; exact Set.mem_singleton _
  exact memE_bind (memE_liftE hsc) rfl hy

theorem RContX.step {σ σk : State Unit} {k : Nat} (hc : RContX dev pu sz pb idx σ (k + 1) σk)
    {σn : State Unit} (hy : ((.ok (), σn) : Except Unit Unit × State Unit) ∈
      ((chunkF dev pu sz pb idx (k + 1)).run σk).1) : RContX dev pu sz pb idx σ k σn := by
  intro y hy'
  apply hc
  rw [chunks_succ]
  show y ∈ (((chunkF dev pu sz pb idx (k + 1)) >>= fun _ =>
    NonDetE.mapMEx (chunkF dev pu sz pb idx) (chunks k)).run σk).1
  exact memE_bind hy rfl hy'

theorem RContX.done {σ σk : State Unit} (hc : RContX dev pu sz pb idx σ 0 σk)
    {y : Except Unit Unit × State Unit} (hy : y ∈ ((chunkF dev pu sz pb idx 0).run σk).1) :
    y ∈ ((resetUntypedCap (Z := Unit) (pb, idx)).run σ).1 := by
  apply hc
  show y ∈ (((chunkF dev pu sz pb idx 0) >>= fun _ => NonDetE.mapMEx (chunkF dev pu sz pb idx) []).run σk).1
  obtain ⟨y1, y2⟩ := y
  rcases y1 with e | u
  · exact memE_bind_err hy rfl
  · exact memE_bind hy rfl (Set.mem_singleton _)

theorem RContX.preempt {σ σk : State Unit} {k : Nat} (hc : RContX dev pu sz pb idx σ k σk)
    {σn : State Unit} (hy : ((.error (), σn) : Except Unit Unit × State Unit) ∈
      ((chunkF dev pu sz pb idx k).run σk).1) :
    ((.error (), σn) : Except Unit Unit × State Unit) ∈ ((resetUntypedCap (Z := Unit) (pb, idx)).run σ).1 := by
  apply hc
  rw [chunks_cons]
  exact memE_bind_err hy rfl

section Top
variable {σ : State Unit} {fi : Nat} {cs : CnodeContents}
  (hk : σ.kheap pb = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r)
  (hg : getCap (Z := Unit) (pb, idx) σ = ({(.untypedCap dev pu sz fi, σ)}, False)) (hfi : fi ≠ 0)
  (hp8 : pu.toNat % 8 = 0) (hpb : pb ∉ regionSet pu sz) (hrcb : resetChunkBits = 16)
include hk hwf hidx hg hfi hp8 hpb hrcb

/-- **The chunked case**: the exact continuation from `delete_objects`'
outcome. -/
theorem reset_initX (hs : ¬ (dev = true ∨ sz < resetChunkBits)) (hfs : fi ≤ 2 ^ sz)
    {yD : Unit × State Unit} (hyD : yD ∈ (deleteObjects (Z := Unit) pu sz σ).1) :
    RContX dev pu sz pb idx σ ((fi - 1) / 2 ^ resetChunkBits) yD.2 := by
  intro y hy
  have hl := chunk_list resetChunkBits sz fi (by rw [hrcb] at hs ⊢; omega) (by omega) hfs
  unfold resetUntypedCap
  refine memE_bind (by rw [top_get hk hwf hidx hg hfi hp8 hpb hrcb]; exact Set.mem_singleton _) rfl ?_
  dsimp only
  simp only [NonDetE.returnOk, ndE_pure_bind, Fl4Spec.bitsOf, Fl4Spec.objRefOf, Fl4Spec.freeIndexOf,
    Fl4Spec.isDeviceUntypedCap, hfi, ↓reduceIte]
  refine memE_bind (memE_liftE hyD) rfl ?_
  dsimp only
  rw [if_neg (by simpa using hs)]
  have hl' : ((List.range (2 ^ (sz - resetChunkBits))).filter
      (fun i => decide (i * 2 ^ resetChunkBits < fi))).reverse = chunks ((fi - 1) / 2 ^ resetChunkBits) := hl
  have key : y ∈ ((NonDetE.mapMEx (chunkF dev pu sz pb idx) (chunks ((fi - 1) / 2 ^ resetChunkBits)) >>= fun _ =>
      NonDetE.liftE (archPostResetUntyped (Z := Unit) dev sz)).run yD.2).1 := by
    rcases y with ⟨e | u, s1⟩
    · exact memE_bind_err hy rfl
    · refine memE_bind hy rfl ?_
      exact memE_liftE (m := archPostResetUntyped (Z := Unit) dev sz) (x := ((), s1)) (Set.mem_singleton _)
  convert key using 4
  all_goals first
    | rfl
    | (rw [← hl']; congr 1; try (apply List.filter_congr; intro i _; simp [Fl4Spec.freeIndexOf]))

/-- **The small RAM case** (`sz < 16`): the outcome with the free index 0,
from `delete_objects`' outcome whose region's bytes are zero. -/
theorem reset_smallX (hdv : dev = false) (hs : sz < resetChunkBits) (hfit : pu.toNat + 2 ^ sz ≤ 2 ^ 64)
    (hsz3 : 3 ≤ sz)
    {yD : Unit × State Unit} (hyD : yD ∈ (deleteObjects (Z := Unit) pu sz σ).1)
    (hz : ∀ y : Word, pu.toNat ≤ y.toNat → y.toNat < pu.toNat + 2 ^ sz → yD.2.machineState.underlyingMemory y = 0)
    {csD : CnodeContents} (hkD : yD.2.kheap pb = some (.cnode r csD)) (hwfD : wellFormedCnodeN r csD) :
    ((.ok (), setCnodeSlot yD.2 pb r csD idx (.untypedCap dev pu sz 0)) : Except Unit Unit × State Unit) ∈
      ((resetUntypedCap (Z := Unit) (pb, idx)).run σ).1 := by
  subst hdv
  unfold resetUntypedCap
  refine memE_bind (by rw [top_get hk hwf hidx hg hfi hp8 hpb hrcb]; exact Set.mem_singleton _) rfl ?_
  dsimp only
  simp only [NonDetE.returnOk, ndE_pure_bind, Fl4Spec.bitsOf, Fl4Spec.objRefOf, Fl4Spec.freeIndexOf,
    Fl4Spec.isDeviceUntypedCap, hfi, ↓reduceIte]
  refine memE_bind (memE_liftE hyD) rfl ?_
  dsimp only
  rw [if_pos (Or.inr hs)]
  have hn8 : 2 ^ sz % 8 = 0 := by
    have : 8 ∣ 2 ^ sz := by
      have := Nat.pow_dvd_pow 2 hsz3; simpa using this
    omega
  obtain ⟨x, hx⟩ := clear_has hp8 (2 ^ sz) yD.2
  have hxe : x.2 = yD.2 := clear_id hp8 hn8 (Nat.two_pow_pos _) hfit hz x hx
  have hsc : (((), setCnodeSlot yD.2 pb r csD idx (.untypedCap false pu sz 0)) :
      Unit × State Unit) ∈ (setCap (Z := Unit) (.untypedCap false pu sz 0) (pb, idx) yD.2).1 := by
    rw [setCap_cnode _ hkD hwfD hidx]; exact Set.mem_singleton _
  have hm : (((), setCnodeSlot yD.2 pb r csD idx (.untypedCap false pu sz 0)) : Unit × State Unit) ∈
      ((NonDet.unless (false = true) (doMachineOp (clearMemory pu (2 ^ sz))) >>= fun _ =>
        setCap (Z := Unit) (.untypedCap false pu sz 0) (pb, idx)) yD.2).1 := by
    refine ⟨x, ?_, ?_⟩
    · unfold NonDet.unless; rw [if_neg (by decide)]; exact hx
    · rw [hxe]; exact hsc
  refine memE_bind (memE_liftE hm) rfl ?_
  exact memE_liftE (m := archPostResetUntyped (Z := Unit) false sz) (x := ((), _)) (Set.mem_singleton _)

end Top

end Reset

end

end Fl4Proofs.P3
