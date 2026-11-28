/-
P3 (line mmuAD, gen 42b9): **the guest-table entry encodings, FL4 against the spec** — goal 3's first half and the
table map's entry.

* **`tblEntry_bv`**: the table map's entry `layout::paddr(ptr) | 7` (crates/fl4-core/src/ept.rs l. 300) is the spec's
  `GuestPte.encode k (.table (addrFromPPtr ptr))` (Fl4Spec/Ext/VirtEpt `encode`, `.table p => p ||| 7`), for every
  backend `k`.
* **`memory_type_eq`**: `ept::memory_type` (ept.rs l. 88-94) is the spec's `guestMemoryType`.
* **`frame_entry_eq`**: `ept::frame_entry amd ptr rights attr large` (ept.rs l. 95-116) is 0 for kernel-only rights
  and otherwise the spec's `GuestPte.encode k (.frame (addrFromPPtr ptr) large (rights ≠ VM_READ_ONLY)
  (guestMemoryType attr))`, given `amd = true ↔ k = .svm` (FL4 passes `a.virtualization() == 2`, ept.rs l. 162; the
  spec's backend is `virtKind`; P3/JAtZV3Vmcs's `ZvVirtAgree` relates the two). The spec's `decodePageMapEpt` (Ext/
  VirtEptInv l. 195-198) writes `0` exactly for `vmKernelOnly` rights and this word otherwise; relating FL4's
  rights word to the spec's `maskVmRights` is the frame map's decode (not here).

No named premise. New file only; root import after `P3.EptMapDec`.
-/
import Fl4Proofs.P3.EptMapDec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- **The table map's entry** (module docstring). -/
theorem tblEntry_bv (k : Fl4Spec.VirtKind) (ptr : U64) :
    (core.num.U64.wrapping_sub ptr layout.PPTR_BASE ||| 7#u64).bv =
      Fl4Spec.GuestPte.encode k (.table (Fl4Spec.addrFromPPtr ptr.bv)) := by
  have e : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE).bv = ptr.bv - Fl4Spec.pptrBase := by
    rw [core.num.U64.wrapping_sub_bv_eq, pptrBase_bv]
  simp only [UScalar.bv_or, e]
  rfl

/-- **`ept::memory_type` is `guestMemoryType`** (module docstring). -/
theorem memory_type_eq (attr : U64) : ept.memory_type attr = ok ⟨Fl4Spec.guestMemoryType attr.bv⟩ := by
  unfold ept.memory_type Fl4Spec.guestMemoryType
  split
  all_goals simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  all_goals first
    | (congr 1; done)
    | (congr 1; apply P1.eq_of_bv; decide)
    | (rename_i a b c d
       congr 1
       apply P1.eq_of_bv
       rw [if_neg]
       · rfl
       · rintro (e | e | e | e)
         all_goals first
           | exact a (P1.eq_of_bv (by rw [e]; rfl))
           | exact b (P1.eq_of_bv (by rw [e]; rfl))
           | exact c (P1.eq_of_bv (by rw [e]; rfl))
           | exact d (P1.eq_of_bv (by rw [e]; rfl)))

theorem gmt_cases (w : Fl4Spec.Word) :
    Fl4Spec.guestMemoryType w = 0 ∨ Fl4Spec.guestMemoryType w = 1 ∨ Fl4Spec.guestMemoryType w = 4 ∨
      Fl4Spec.guestMemoryType w = 6 := by
  unfold Fl4Spec.guestMemoryType
  by_cases h : w = 0 ∨ w = 1 ∨ w = 4 ∨ w = 6
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact Or.inr (Or.inr (Or.inr rfl))

theorem npT_0 : Fl4Spec.npTPatIndex 0 = 3 := by decide
theorem npT_1 : Fl4Spec.npTPatIndex 1 = 4 := by decide
theorem npT_4 : Fl4Spec.npTPatIndex 4 = 1 := by decide
theorem npT_6 : Fl4Spec.npTPatIndex 6 = 0 := by decide

theorem fe_shl (x : U64) (k : I32) (h0 : 0 ≤ k.val) (h : k.val < 64) : x <<< k = ok ⟨x.bv <<< k.toNat⟩ :=
  shl_eq x k h0 h

/-- The FL4 write bit is the spec's. -/
theorem fe_write (rights : U64) :
    (if rights = capability.VM_READ_ONLY then (ok 0#u64 : Result U64) else ok 2#u64) =
      ok ⟨if decide (rights ≠ capability.VM_READ_ONLY) = true then 2 else 0⟩ := by
  by_cases h : rights = capability.VM_READ_ONLY
  · rw [if_pos h]; simp [h]; rfl
  · rw [if_neg h]; simp [h]; rfl

theorem fe_ps (large : Bool) :
    (if large = true then (ok 128#u64 : Result U64) else ok 0#u64) = ok ⟨if large = true then 128 else 0⟩ := by
  cases large <;> rfl

set_option maxHeartbeats 4000000 in
/-- **`ept::frame_entry` is the spec's frame entry** (module docstring). -/
theorem frame_entry_eq (k : Fl4Spec.VirtKind) {amd : Bool} (hk : amd = true ↔ k = .svm) (ptr rights attr : U64)
    (large : Bool) :
    ept.frame_entry amd ptr rights attr large =
      ok (if rights = capability.VM_KERNEL_ONLY then 0#u64 else
        ⟨Fl4Spec.GuestPte.encode k (.frame (Fl4Spec.addrFromPPtr ptr.bv) large (rights ≠ capability.VM_READ_ONLY)
          (Fl4Spec.guestMemoryType attr.bv))⟩) := by
  have e : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE).bv = ptr.bv - Fl4Spec.pptrBase := by
    rw [core.num.U64.wrapping_sub_bv_eq, pptrBase_bv]
  unfold ept.frame_entry
  by_cases hko : rights = capability.VM_KERNEL_ONLY
  · rw [if_pos hko, if_pos hko]
  rw [if_neg hko, if_neg hko, fe_write, bind_ok, fe_ps, bind_ok]
  cases amd
  · have hk' : k ≠ .svm := fun e => by simpa using hk.2 e
    simp only [Bool.false_eq_true, ↓reduceIte, layout.paddr, lift, bind_ok, memory_type_eq,
      fe_shl _ 3#i32 (by decide) (by decide)]
    congr 1
    apply P1.eq_of_bv
    simp only [UScalar.bv_or, e, Fl4Spec.GuestPte.encode, if_neg hk']
    rfl
  · have hk' : k = .svm := hk.1 rfl
    simp only [↓reduceIte, memory_type_eq, bind_ok]
    have g4 := gmt_cases attr.bv
    cases large
    all_goals
      split
      all_goals
        first
          | (rename_i heq
             have hmt := congrArg UScalar.bv heq
             try simp only at hmt
             rcases g4 with g | g | g | g <;> rw [g] at hmt <;> first | (exfalso; revert hmt; decide) | skip)
          | (rename_i a b c d
             rcases g4 with g | g | g | g
             all_goals first
               | exact absurd (P1.eq_of_bv (show Fl4Spec.guestMemoryType attr.bv = _ by rw [g]; rfl)) a
               | exact absurd (P1.eq_of_bv (show Fl4Spec.guestMemoryType attr.bv = _ by rw [g]; rfl)) b
               | exact absurd (P1.eq_of_bv (show Fl4Spec.guestMemoryType attr.bv = _ by rw [g]; rfl)) c
               | skip)
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte, lift, bind_ok, layout.paddr,
        fe_shl _ 3#i32 (by decide) (by decide), fe_shl _ 5#i32 (by decide) (by decide),
        fe_shl _ 10#i32 (by decide) (by decide)]
      congr 1
      apply P1.eq_of_bv
      simp only [UScalar.bv_or, UScalar.bv_and, e, Fl4Spec.GuestPte.encode, if_pos hk', g, npT_0, npT_1, npT_4,
        npT_6]
      rfl

end

end Fl4Proofs.P3
