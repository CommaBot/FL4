/-
# P2 (line p3mc, gen 39): the second boot start's memory and ghosts over `bst`, and `JKern` there

The store state **`sR = BS.of memR kbB 0`** for the spec state `σR` (P2/BootRSpec: `σB` with the running root
thread `tRp` current, bound to the root SC `scRp`):

* **`memR`** (`wordR` on the address): `memB` (P2/BootMem) with
  core 0's `CUR_THREAD = tRw` (`= tRp`), `CUR_SC = scRw` (`= scRp`) (`IDLE_THREAD` / `IDLE_SC` stay the idle
  objects);
  the root TCB `tRw`: slot 0 (`SLOT_CTABLE`) holds the thread cap of `tRw` (`CAP0 = 6 << 59 | (tRw & PTR_MASK)`,
  `CAP1 = 0`, `capability.rs` `encode`) with the MDB `NEXT` word `1 << 48` (revocable, no next, `obj.rs`
  `set_next_flags`), `STATE = 1` (`TS_RUNNING`), `SC = scRw`; every other word 0 (priority, domain, MCP, affinity
  (core 0), yield, debug links, queue flags);
  the root SC `scRw`: the idle SC's words with `TCB = tRw`: `REFILL_MAX = 2`, `REFILL_TAIL = 1`, refills
  `(0, MAX_PERIOD)`, `(MAX_PERIOD, 0)`, `CORE = 0`.
* **`HR`** (P1's heap): `HB` with `tRw ↦ tcb`, `scRw ↦ sc 7`. **`thR`** (the typed heap): `thB` with `tRw ↦ tcb`.
  `DB` / `CsB` unchanged (`DR`, `CsR` are the same sets).

Proved: `HR_cases`, **`heapR_ok`**, `thR_cases`, the store lookups (`memR_mem`, `sR_curW`, `sR_idleW`, `sR_cscW`,
…), the cap of the root slot (**`capV_R_root`**: `capV (bsL.mem sR) tRw = .Thread tRw`, `revOf` true, links 0) and
**`jKern_R`**: P3's `JKern archT HR CsB DB thR sR σR`.

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootRSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1 Fl4Spec Classical

noncomputable section

/-! ## Addresses -/

/-- The root TCB (`tRp`) as a word. -/
def tRw : U64 := ⟨BitVec.ofNat 64 18446744071562076160⟩
/-- The root SC (`scRp`) as a word. -/
def scRw : U64 := ⟨BitVec.ofNat 64 18446744071562080256⟩
/-- The thread cap of `tRw`, first word: `6 << 59 | (tRw & 0xffff_ffff_ffff)`. -/
def capTRw : U64 := ⟨BitVec.ofNat 64 3459045986649776128⟩
/-- The root slot's `NEXT` word: revocable (bit 48), no next. -/
def revW : U64 := ⟨BitVec.ofNat 64 281474976710656⟩

theorem tRw_val : tRw.val = 18446744071562076160 := by
  show (BitVec.ofNat 64 18446744071562076160).toNat = _; decide
theorem scRw_val : scRw.val = 18446744071562080256 := by
  show (BitVec.ofNat 64 18446744071562080256).toNat = _; decide
theorem tRw_bv : tRw.bv = tRp := rfl
theorem scRw_bv : scRw.bv = scRp := rfl

/-- The second boot start's words by address (module docstring). -/
def wordR (n : Nat) : U64 :=
  if n = 18446744071562114304 then tRw
  else if n = 18446744071562114328 then scRw
  else if n = 18446744071562076160 then capTRw
  else if n = 18446744071562076160 + 24 then revW
  else if n = 18446744071562076160 + 3328 then 1#u64
  else if n = 18446744071562076160 + 3464 then scRw
  else if n = 18446744071562080256 + 24 then tRw
  else if n = 18446744071562080256 + 72 then 2#u64
  else if n = 18446744071562080256 + 88 then 1#u64
  else if n = 18446744071562080256 + 104 ∨ n = 18446744071562080256 + 112 then maxPB
  else wordB n

/-- The second boot start's memory. -/
def memR (a : U64) : U64 := wordR a.val

/-- **The second boot start's store state.** -/
def sR : BS := BS.of memR kbB 0#u64

theorem memR_mem {a : U64} (ha : Aligned a) : bsL.mem sR a = wordR a.val := BS.of_mem memR kbB 0#u64 ha

theorem sR_ksb : bsL.ksb sR = kbB := rfl
theorem sR_cpu : bsL.cpu sR = 0#u64 := rfl

/-- `wordR` is `wordB` off its eleven new words. -/
theorem wordR_of {n : Nat}
    (hs : n ≠ 18446744071562114304 ∧ n ≠ 18446744071562114328 ∧ n ≠ 18446744071562076160 ∧
      n ≠ 18446744071562076160 + 24 ∧ n ≠ 18446744071562076160 + 3328 ∧ n ≠ 18446744071562076160 + 3464 ∧
      n ≠ 18446744071562080256 + 24 ∧ n ≠ 18446744071562080256 + 72 ∧ n ≠ 18446744071562080256 + 88 ∧
      n ≠ 18446744071562080256 + 104 ∧ n ≠ 18446744071562080256 + 112) :
    wordR n = wordB n := by
  unfold wordR
  rw [if_neg (show ¬ n = 18446744071562114304 by omega),
    if_neg (show ¬ n = 18446744071562114328 by omega),
    if_neg (show ¬ n = 18446744071562076160 by omega),
    if_neg (show ¬ n = 18446744071562076160 + 24 by omega),
    if_neg (show ¬ n = 18446744071562076160 + 3328 by omega),
    if_neg (show ¬ n = 18446744071562076160 + 3464 by omega),
    if_neg (show ¬ n = 18446744071562080256 + 24 by omega),
    if_neg (show ¬ n = 18446744071562080256 + 72 by omega),
    if_neg (show ¬ n = 18446744071562080256 + 88 by omega),
    if_neg (show ¬ (n = 18446744071562080256 + 104 ∨ n = 18446744071562080256 + 112) by omega)]

/-- `wordR` is 0 off its 24 nonzero words. -/
theorem wordR_zero_of {n : Nat}
    (hs : n ≠ 18446744071562114304 ∧ n ≠ 18446744071562114312 ∧ n ≠ 18446744071562114328 ∧ n ≠ 18446744071562114336 ∧
    n ≠ 18446744071562100752 ∧ n ≠ 18446744071562100936 ∧ n ≠ 18446744071562100808 ∧ n ≠ 18446744071562100784 ∧
    n ≠ 18446744071562072064 + 3328 ∧ n ≠ 18446744071562072064 + 3464 ∧ n ≠ 18446744071562096640 + 24 ∧
    n ≠ 18446744071562096640 + 72 ∧ n ≠ 18446744071562096640 + 88 ∧ n ≠ 18446744071562096640 + 104 ∧
    n ≠ 18446744071562096640 + 112 ∧
    n ≠ 18446744071562076160 ∧
      n ≠ 18446744071562076160 + 24 ∧ n ≠ 18446744071562076160 + 3328 ∧ n ≠ 18446744071562076160 + 3464 ∧
      n ≠ 18446744071562080256 + 24 ∧ n ≠ 18446744071562080256 + 72 ∧ n ≠ 18446744071562080256 + 88 ∧
      n ≠ 18446744071562080256 + 104 ∧ n ≠ 18446744071562080256 + 112) :
    wordR n = 0#u64 := by
  rw [wordR_of (by omega)]; exact wordB_zero_of (by omega)

/-- Core 0's node words of `sR`. -/
theorem sR_nodeAt_val {off : U64} (ho : off.val < 4288) :
    (bsL.nodeAt sR 0#u64 off).val = 18446744071562114304 + off.val := by
  unfold LawfulStore.nodeAt
  rw [sR_ksb]
  simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, kbB_val]
  simp [U64.size, U64.numBits]
  omega

theorem sR_nodeBase (c : U64) (hc : c = 0#u64) : bsL.nodeBase sR c = 18446744071562114304 := by
  subst hc
  show (bsL.ksb sR).val + 13568 + (0#u64 : U64).val * 4288 = _
  rw [sR_ksb, kbB_val]; rfl

theorem nodeR_aligned {off : U64} (ho : off.val < 4288) (h8 : off.val % 8 = 0) :
    Aligned (bsL.nodeAt sR 0#u64 off) := by
  show (bsL.nodeAt sR 0#u64 off).val % 8 = 0
  rw [sR_nodeAt_val ho]; omega

theorem sR_curW : bsL.curW sR = tRw := by
  unfold LawfulStore.curW
  rw [sR_cpu]
  have h0 : layout.node.CUR_THREAD.val = 0 := curth0
  rw [memR_mem (nodeR_aligned (by omega) (by omega)), sR_nodeAt_val (by omega), h0]
  simp [wordR]

theorem sR_idleW : bsL.idleW sR = tiB := by
  unfold LawfulStore.idleW
  rw [sR_cpu]
  have h0 : layout.node.IDLE_THREAD.val = 8 := by simp [layout.node.IDLE_THREAD]
  rw [memR_mem (nodeR_aligned (by omega) (by omega)), sR_nodeAt_val (by omega), h0]
  rw [wordR_of (by omega)]
  simp [wordB]

theorem sR_cscW : bsL.cscW sR = scRw := by
  unfold LawfulStore.cscW LawfulStore.nodeA
  rw [sR_cpu]
  have h0 : layout.node.CUR_SC.val = 24 := by simp [layout.node.CUR_SC]
  rw [memR_mem (nodeR_aligned (by omega) (by omega)), sR_nodeAt_val (by omega), h0]
  simp [wordR]

theorem sR_act_val : (bsL.nodeAt sR (bsL.cpu sR) layout.node.SCHED_ACTION).val = 18446744071562114320 := by
  rw [sR_cpu, sR_nodeAt_val (by rw [act_val]; omega), act_val]

theorem sR_dbg_val : (bsL.nodeAt sR 0#u64 layout.node.DEBUG_TCBS).val = 18446744071562114392 := by
  rw [sR_nodeAt_val (by rw [debug_val]; omega), debug_val]

theorem sR_dbg_word : bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.DEBUG_TCBS) = 0#u64 := by
  rw [memR_mem (by show _ % 8 = 0; rw [sR_dbg_val]), sR_dbg_val]
  exact wordR_zero_of (by omega)

/-- The two node words that differ: `CUR_THREAD` (the root thread) and `IDLE_THREAD` (the idle thread). -/
theorem sR_cur_ne_idle : bsL.curW sR ≠ bsL.idleW sR := by
  rw [sR_curW, sR_idleW]
  intro e
  have := congrArg UScalar.val e
  rw [tRw_val, tiB_val] at this
  omega

/-! ## The root slot -/

theorem tRw_word8 : (wordOf tRw 8#u64).val = 18446744071562076160 + 8 := by
  show (core.num.U64.wrapping_add tRw 8#u64).val = _
  simp only [core.num.U64.wrapping_add_val_eq, tRw_val]; simp [U64.size, U64.numBits]

theorem tRw_word16 : (wordOf tRw 16#u64).val = 18446744071562076160 + 16 := by
  show (core.num.U64.wrapping_add tRw 16#u64).val = _
  simp only [core.num.U64.wrapping_add_val_eq, tRw_val]; simp [U64.size, U64.numBits]

theorem tRw_word24 : (wordOf tRw 24#u64).val = 18446744071562076160 + 24 := by
  show (core.num.U64.wrapping_add tRw 24#u64).val = _
  simp only [core.num.U64.wrapping_add_val_eq, tRw_val]; simp [U64.size, U64.numBits]

theorem memR_tRw0 : bsL.mem sR tRw = capTRw := by
  rw [memR_mem (by show _ % 8 = 0; rw [tRw_val]), tRw_val]; simp [wordR]

theorem memR_tRw8 : bsL.mem sR (wordOf tRw 8#u64) = 0#u64 := by
  rw [memR_mem (by show _ % 8 = 0; rw [tRw_word8]), tRw_word8]; exact wordR_zero_of (by omega)

theorem memR_tRw16 : bsL.mem sR (wordOf tRw 16#u64) = 0#u64 := by
  rw [memR_mem (by show _ % 8 = 0; rw [tRw_word16]), tRw_word16]; exact wordR_zero_of (by omega)

theorem memR_tRw24 : bsL.mem sR (wordOf tRw 24#u64) = revW := by
  rw [memR_mem (by show _ % 8 = 0; rw [tRw_word24]), tRw_word24]
  unfold wordR
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- **The root slot holds the thread cap of the root thread.** -/
theorem capV_R_root : capV (bsL.mem sR) tRw = .Thread tRw := by
  unfold capV
  rw [memR_tRw0, memR_tRw8]
  first | rfl | decide

theorem revOf_R_root : revOf (bsL.mem sR) tRw = true := by
  unfold revOf; rw [memR_tRw24]; decide

theorem nextOf_R_root : nextOf (bsL.mem sR) tRw = 0#u64 := by
  unfold nextOf; rw [memR_tRw24]; first | rfl | decide

theorem prevOf_R_root : prevOf (bsL.mem sR) tRw = 0#u64 := by
  unfold prevOf; exact memR_tRw16

theorem fbOf_R_root : fbOf (bsL.mem sR) tRw = false := by
  unfold fbOf; rw [memR_tRw24]; decide

/-! ## The heaps -/

/-- **P1's heap at the second boot start**: `HB` with the root TCB and the root SC. -/
def HR : P1.Heap := fun p =>
  if p.val = 18446744071562076160 then some .tcb
  else if p.val = 18446744071562080256 then some (.sc 7)
  else HB p

/-- **The typed heap at the second boot start**: `thB` with the root TCB. -/
def thR : TypedHeap := fun p =>
  if p.val = 18446744071562076160 then some .tcb
  else thB p

theorem HR_cases {p : U64} {k : HKind} (h : HR p = some k) :
    (p.val = 18446744071562076160 ∧ k = .tcb) ∨ (p.val = 18446744071562080256 ∧ k = .sc 7) ∨
    (p.val = 18446744071562072064 ∧ k = .tcb) ∨ (p.val = 18446744071562096640 ∧ k = .sc 7) ∨
    ((p.val = 18446744071562084352 ∨ p.val = 18446744071562088448 ∨ p.val = 18446744071562092544) ∧
      k = .other 12) ∨
    (k = .other 5 ∧ 18446744071562100736 + 1248 ≤ p.val ∧ p.val < 18446744071562100736 + 5344 ∧
      (p.val - 18446744071562100736) % 32 = 0) ∨
    (k = .other 3 ∧ 18446744071562100736 ≤ p.val ∧ p.val < 18446744071562100736 + 13568 ∧
      (p.val - 18446744071562100736) % 8 = 0 ∧
      ¬ (18446744071562100736 + 1248 ≤ p.val ∧ p.val < 18446744071562100736 + 5344)) := by
  unfold HR at h
  split_ifs at h with h1 h2
  · cases h; exact Or.inl ⟨h1, rfl⟩
  · cases h; exact Or.inr (Or.inl ⟨h2, rfl⟩)
  · exact Or.inr (Or.inr (HB_cases h))

theorem thR_cases {p : U64} {k : ObjKind} (h : thR p = some k) :
    (p.val = 18446744071562076160 ∧ k = .tcb) ∨ (p.val = 18446744071562072064 ∧ k = .tcb) ∨
    (k = .cnode 0 ∧ 18446744071562100736 + 1248 ≤ p.val ∧ p.val < 18446744071562100736 + 5344 ∧
      (p.val - 18446744071562100736) % 32 = 0) := by
  unfold thR at h
  split_ifs at h with h1
  · cases h; exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (thB_cases h)

theorem HR_tR : HR tRw = some .tcb := by unfold HR; rw [if_pos tRw_val]
theorem HR_scR : HR scRw = some (.sc 7) := by
  unfold HR; rw [if_neg (by rw [scRw_val]; omega), if_pos scRw_val]
theorem HR_ti : HR tiB = some .tcb := by
  unfold HR; rw [if_neg (by rw [tiB_val]; omega), if_neg (by rw [tiB_val]; omega)]; exact HB_ti
theorem HR_sci : HR sciB = some (.sc 7) := by
  unfold HR; rw [if_neg (by rw [sciB_val]; omega), if_neg (by rw [sciB_val]; omega)]; exact HB_sci
theorem thR_tR : thR tRw = some .tcb := by unfold thR; rw [if_pos tRw_val]
theorem thR_ti : thR tiB = some .tcb := by unfold thR; rw [if_neg (by rw [tiB_val]; omega)]; exact thB_ti

/-- **`HR` is well formed.** -/
theorem heapR_ok : HeapOK HR where
  align := by
    intro p k hp
    rcases HR_cases hp with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨rfl, h1, h2, h3⟩ |
      ⟨rfl, h1, h2, h3, -⟩ <;> simp only [HKind.bits, Nat.reducePow] <;> omega
  fits := by
    intro p k hp
    rcases HR_cases hp with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨rfl, h1, h2, h3⟩ |
      ⟨rfl, h1, h2, h3, -⟩ <;> simp only [HKind.bits, Nat.reducePow] <;> omega
  lt64 := by
    intro p k hp
    rcases HR_cases hp with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      simp [HKind.bits]
  scmin := by
    intro p z hp
    rcases HR_cases hp with ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> cases e
    · exact le_refl _
    · exact le_refl _
  disj := by
    intro p k q k' hp hq hne
    have hv := U64.ne_of_val hne
    rcases HR_cases hp with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨rfl, h1, h2, h3⟩ |
      ⟨rfl, h1, h2, h3, h4⟩ <;>
    rcases HR_cases hq with ⟨g1, rfl⟩ | ⟨g1, rfl⟩ | ⟨g1, rfl⟩ | ⟨g1, rfl⟩ | ⟨g1, rfl⟩ | ⟨rfl, g1, g2, g3⟩ |
      ⟨rfl, g1, g2, g3, g4⟩ <;>
      simp only [HKind.bits, Nat.reducePow] <;> omega

theorem HR_zero : HR 0#u64 = none := by
  cases h : HR 0#u64 with
  | none => rfl
  | some k =>
    have h0 : (0#u64 : U64).val = 0 := rfl
    rcases HR_cases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> omega

/-- A word of `thR`'s objects lies in a TCB or the IRQ node. -/
theorem thR_in {p : U64} {k : ObjKind} (hp : thR p = some k) {b : Nat} (h1 : p.val ≤ b)
    (h2 : b < p.val + P3.objSize k) :
    (18446744071562076160 ≤ b ∧ b < 18446744071562076160 + 4096) ∨
    (18446744071562072064 ≤ b ∧ b < 18446744071562072064 + 4096) ∨
      (18446744071562100736 + 1248 ≤ b ∧ b < 18446744071562100736 + 5344) := by
  rcases thR_cases hp with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩
  · simp only [P3.objSize] at h2; omega
  · simp only [P3.objSize] at h2; omega
  · simp only [P3.objSize, Nat.pow_zero] at h2; omega

/-- The root slot as an abstract slot of `thR`. -/
theorem absSlot_R_root : AbsSlot thR (tRp, tcbCnodeIndex 0) :=
  ⟨tRw, rfl, Or.inr ⟨thR_tR, 0, by decide, rfl⟩⟩

/-! ## `JKern` at the second boot start -/

/-- **P3's kernel-global placement at the second boot start** (`JKern`). -/
theorem jKern_R : JKern (L := bsL) LocPlatM.archT HR CsB DB thR sR (σR (Z := Unit)) where
  orig sl h := by rw [(iocR_iff sl).1 h]; exact absSlot_R_root
  cur := by rw [sR_curW, tRw_bv]; rfl
  curT := by rw [sR_curW]; exact thR_tR
  act := by
    refine ⟨by show _ % 8 = 0; rw [sR_act_val], fun p k hp ⟨h1, h2⟩ => ?_⟩
    rw [sR_act_val] at h1 h2
    rcases thR_in hp h1 h2 with h | h | h <;> omega
  dwAl := by show _ % 8 = 0; rw [sR_dbg_val]
  dwObj := by
    rintro a ⟨p, i, hi, rfl⟩ ⟨h1, h2⟩
    rw [sR_dbg_val] at h1 h2
    obtain ⟨k, hk, hsz⟩ := hi.size
    rcases thR_cases hk with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩
    · simp only [P3.objSize] at hsz
      rw [slotOf_val (by omega)] at h1 h2; omega
    · simp only [P3.objSize] at hsz
      rw [slotOf_val (by omega)] at h1 h2; omega
    · simp only [P3.objSize, Nat.pow_zero] at hsz
      rw [slotOf_val (by omega)] at h1 h2; omega
  dwNe := by
    rw [sR_dbg_val, sR_act_val, sR_curW]
    have : (P1.stA tRw).val = 18446744071562076160 + 3328 := by
      rw [P1.stA_eq]; simp only [core.num.U64.wrapping_add_val_eq, tRw_val]; simp [U64.size, U64.numBits]
    rw [this]; omega
  head := Or.inl sR_dbg_word
  gpm := by
    refine ⟨globalPml4, ?_⟩
    show kheapR initGlobalPml4 = _
    rw [kheapR_of_ne (by decide) (by decide)]
    unfold kheapB
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  ga := by
    show initGlobalPml4.toNat % 4096 = 0
    have e : initGlobalPml4.toNat = 18446744071562084352 := by decide
    rw [e]
  gf := by
    show initGlobalPml4.toNat + 4096 ≤ 2 ^ 64
    have e : initGlobalPml4.toNat = 18446744071562084352 := by decide
    rw [e]; norm_num
  heap := heapR_ok
  h0 := HR_zero
  hks p k hp hk := by
    rw [sR_ksb, kbB_val]
    rcases HR_cases hp with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨-, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp only [HKind.bits, Nat.reducePow]; omega
    · simp only [HKind.bits, Nat.reducePow]; omega
    · simp only [HKind.bits, Nat.reducePow]; omega
    · simp only [HKind.bits, Nat.reducePow]; omega
    · exact absurd rfl (hk 12)
    · exact absurd rfl (hk 5)
    · exact absurd rfl (hk 3)
  hksIn p z hp := by
    rw [sR_ksb, kbB_val]
    rcases HR_cases hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨h1, e⟩ | ⟨e, h1, h2, h3⟩ | ⟨e, h1, h2, h3, -⟩ <;>
      cases e
    · left; simp only [Nat.reducePow]; omega
    · right; right; simp only [Nat.reducePow]; omega
    · right; right; simp only [Nat.reducePow]; omega
  hnd p k hp c hc := by
    rw [sR_nodeBase c hc]
    rcases HR_cases hp with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨rfl, h1, h2, h3⟩ |
      ⟨rfl, h1, h2, h3, -⟩ <;> simp only [HKind.bits, Nat.reducePow] <;> omega
  ksbFit := by rw [sR_ksb, kbB_val]; norm_num
  ksbAl := by rw [sR_ksb, kbB_val]
  nodeFit := by rw [sR_ksb, sR_cpu, kbB_val]; norm_num
  cpuCs := by rw [sR_cpu]; rfl
  curH := by rw [sR_curW]; exact HR_tR
  cscH := by rw [sR_cscW, HR_scR]; exact Option.some_ne_none _
  csLt c hc := by rw [show c = 0#u64 from hc]; decide
  cs0 := rfl
  csN := ⟨1, fun c => by
    show c = 0#u64 ↔ c.val < 1
    constructor
    · rintro rfl; decide
    · intro h; exact UScalar.eq_of_val_eq (by show c.val = 0; omega)⟩
  tdx := ⟨fun _ => rfl, fun _ _ _ => rfl⟩

end

end Fl4Proofs.P2.BootSt
