/-
P1 (aarch64, gen 51): **the kernel window — canonical `OS` slots** (Architect ruling, option 1': a standalone static
placement predicate carried beside the invariants, like `RngOneA64`; no `[J]`, no change to `Cur0R` / `HeapOK` /
`TcbAddr` / `OSOK` / `J.witness`).

FL4's kernel objects live in the kernel window `[PPTR_BASE, PPTR_TOP)`: the kernel reaches physical memory only
through `pptr(paddr) = PPTR_BASE + paddr` (crates/fl4-core/src/arch/aarch64/layout.rs:5, 20–22; the boot map
crates/fl4-kernel-aarch64/src/paging.rs:215–218 maps `[start, end)` at `PPTR_BASE + start` with
`end ≤ PPTR_TOP − PPTR_BASE`), and every untyped region handed to userland is such a window range (retype carves new
objects out of it). `PPTR_BASE = 0xffff_8000_0000_0000` is exactly the lowest canonical upper-half address, so
every window address is canonical: `obj.sext48 x = x` (the MDB `NEXT` / `PREV` words keep 48 bits and sign-extend
from bit 47, obj.rs `sext48`).

* **`WinOK T Ω`** (structure, static — it mentions no state): every TCB of `T` lies with its 4 KiB in the window,
  every `Ω` word in the window. Ordinary steps do not change `T` / `Ω`, so it is carried unchanged.
* **`canon_of_ge`**: `PPTR_BASE ≤ x` gives `obj.sext48 x = ok x` (bit reasoning, `hi_bits`).
* **`OSOK.canon`**: `OSOK T Ω Sg OS ∧ WinOK T Ω` gives every `OS` slot canonical (an `OS` slot's first word is a
  `W7.CapW` word: a TCB low word `t + K`, `K < 224`, or an `Ω` word).
* Establishing it: **`HeapWin H`** (every heap object with its extent in the window), **`WinOK.ofHeap`**
  (`WinOK H.tcbs H.omega`: the set tuple of a heap, `PSets.ofHeap`, at boot and after retype),
  **`HeapWin.drop`** (the reset drops objects), **`HeapWin.retype`** (the retype's new objects lie in the
  untyped region `[lo, hi)`, which lies in the window: same shape hypothesis `hsh` as `retype_heapOK`).

The untyped region in the window (`PPTR_BASE ≤ lo`, `hi ≤ PPTR_TOP`) is a case hypothesis of `HeapWin.retype`
(the untyped cap's pointer is `pptr` of its physical base, objects.rs / boot untypeds). No named premise.
-/
import Fl4ProofsA64.P1.QueueSlotTy
import Fl4ProofsA64.P1.QueueRetype
import Mathlib.Tactic.IntervalCases
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

/-- **The kernel window** (module docstring): every TCB with its 4 KiB, and every `Ω` word, in
`[PPTR_BASE, PPTR_TOP)`. Static: no state. -/
structure WinOK (T Ω : Set U64) : Prop where
  tcb : ∀ t ∈ T, layout.PPTR_BASE.val ≤ t.val ∧ t.val + 2 ^ 12 ≤ layout.PPTR_TOP.val
  omega : ∀ b ∈ Ω, layout.PPTR_BASE.val ≤ b.val ∧ b.val < layout.PPTR_TOP.val

/-- **Every heap object with its extent in the kernel window.** -/
def HeapWin (H : Heap) : Prop :=
  ∀ p k, H p = some k → layout.PPTR_BASE.val ≤ p.val ∧ p.val + 2 ^ k.bits ≤ layout.PPTR_TOP.val

/-- The set tuple of a window heap is in the window. -/
theorem WinOK.ofHeap {H : Heap} (h : HeapWin H) : WinOK H.tcbs H.omega := by
  refine ⟨fun t ht => ?_, fun b hb => ?_⟩
  · have := h t _ ht; simpa [HKind.bits] using this
  · obtain ⟨-, p, k, hp, -, hin⟩ := hb
    have := h p k hp
    simp only [InObj] at hin
    exact ⟨le_trans this.1 hin.1, lt_of_lt_of_le hin.2 this.2⟩

/-- Smaller sets stay in the window. -/
theorem WinOK.mono {T Ω T' Ω' : Set U64} (h : WinOK T Ω) (hT : T' ⊆ T) (hΩ : Ω' ⊆ Ω) : WinOK T' Ω' :=
  ⟨fun t ht => h.tcb t (hT ht), fun b hb => h.omega b (hΩ hb)⟩

/-- The empty heap. -/
theorem HeapWin.empty : HeapWin (fun _ => none) := fun _ _ h => by cases h

/-- The reset drops objects. -/
theorem HeapWin.drop {H : Heap} {D : U64 → Prop} (h : HeapWin H) : HeapWin (H.drop D) :=
  fun p k hp => h p k (Heap.drop_eq_some.1 hp).2

/-- **Retype keeps the heap in the window**: kept objects were, new objects lie in the untyped region `[lo, hi)`,
itself in the window (the shape hypothesis `hsh` as `retype_heapOK`'s). -/
theorem HeapWin.retype {H1 H' : Heap} {lo hi A k w n us : Nat} (hH : HeapWin H1)
    (hlo : lo ≤ A) (hhi : A + w * k ≤ hi) (hbits : ∀ kd, newKind n us = some kd → 2 ^ kd.bits ≤ k)
    (hwl : layout.PPTR_BASE.val ≤ lo) (hwh : hi ≤ layout.PPTR_TOP.val)
    (hsh : ∀ q kd, H' q = some kd → (H1 q = some kd ∧ ¬ MeetsR lo hi q.val (q.val + 2 ^ kd.bits)) ∨
      (NewAt A k w q ∧ newKind n us = some kd)) :
    HeapWin H' := by
  intro q kd hq
  rcases hsh q kd hq with ⟨h1, -⟩ | ⟨⟨j, hj, hv⟩, hk⟩
  · exact hH q kd h1
  · have hb := hbits kd hk
    have hjk : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    constructor <;> omega

namespace W7
namespace R
namespace ST

/-- The bits 47 … 63 of a word `≥ PPTR_BASE` are set. -/
theorem hi_bits (x : U64) (h : 18446603336221196288 ≤ x.val) (i : Nat) (h1 : 47 ≤ i) (h2 : i < 64) :
    x.bv.getLsbD i = true := by
  have hv : x.bv.toNat = x.val := rfl
  have hlt : x.bv.toNat < 2 ^ 64 := x.bv.isLt
  rw [hv] at hlt
  simp only [BitVec.getLsbD, hv]
  first
  | rw [Nat.testBit_to_div_mod]
  | rw [Nat.testBit_eq_decide_div_mod_eq]
  rw [decide_eq_true_eq]
  interval_cases i <;> omega

theorem cM (i : Nat) (hi : i < 64) : (281474976710655#u64).bv.getLsbD i = decide (i < 48) := by
  interval_cases i <;> first | rfl | decide

theorem cH (i : Nat) (hi : i < 64) : (18446462598732840960#u64).bv.getLsbD i = decide (48 ≤ i) := by
  interval_cases i <;> first | rfl | decide

theorem cB (i : Nat) (hi : i < 64) : (140737488355328#u64).bv.getLsbD i = decide (i = 47) := by
  interval_cases i <;> first | rfl | decide

/-- **A window address is canonical**: `PPTR_BASE ≤ x` gives `sext48 x = x`. -/
theorem canon_of_ge (x : U64) (h : layout.PPTR_BASE.val ≤ x.val) : obj.sext48 x = ok x := by
  rw [layout.PPTR_BASE.val_eq] at h
  rw [sx_val]
  have hand : ((x &&& 281474976710655#u64) &&& 140737488355328#u64 != 0#u64) = true := by
    rw [bne_iff_ne]; intro e
    have := congrArg (fun z : U64 => z.bv.getLsbD 47) e
    simp only [UScalar.bv_and, BitVec.getLsbD_and] at this
    rw [hi_bits x h 47 (le_refl _) (by norm_num), cM 47 (by norm_num), cB 47 (by norm_num)] at this
    revert this; first | decide | simp
  rw [if_pos hand]
  congr 1
  rw [UScalar.eq_equiv_bv_eq]; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_or, BitVec.getLsbD_and, BitVec.getLsbD_or, cM i hi, cH i hi]
  by_cases h48 : i < 48
  · simp [h48, show ¬ 48 ≤ i by omega]
  · simp [h48, show 48 ≤ i by omega, hi_bits x h i (by omega) hi]

section
variable {T Ω Sg OS : Set U64}

/-- An `OS` slot lies in the window. -/
theorem OSOK.win (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω) {x : U64} (hx : x ∈ OS) :
    layout.PPTR_BASE.val ≤ x.val := by
  rcases hO.cw0 hx with ⟨t, ht, K, hK, e⟩ | ⟨hΩ, -⟩
  · obtain ⟨h1, h2⟩ := hW.tcb t ht
    have hT : layout.PPTR_TOP.val < 2 ^ 64 := by rw [layout.PPTR_TOP.val_eq]; norm_num
    have : x.val = t.val + K.val := by
      rw [e, core.num.U64.wrapping_add_val_eq]
      first
      | rw [Nat.mod_eq_of_lt (by omega)]
      | (simp only [U64.size_def, U64.numBits]; rw [Nat.mod_eq_of_lt (by omega)])
      | (simp [U64.size_def, U64.numBits]; omega)
    omega
  · exact (hW.omega x hΩ).1

/-- **Every `OS` slot is canonical** under `WinOK`. -/
theorem OSOK.canon (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω) {x : U64} (hx : x ∈ OS) : obj.sext48 x = ok x :=
  canon_of_ge x (hO.win hW hx)

end

end ST
end R
end W7

end Fl4ProofsA64.P1
