/-
# P2 (line mmuAD, gen 1): the page walker's accessed / dirty bits — hardware semantics and walk insensitivity

The x86 MMU writes kernel words that no kernel step writes: the accessed bit (A, bit 5) of every paging-structure
entry a translation uses, and the dirty bit (D, bit 6) of the leaf entry of a write. This module states that
write (`MmuAD` [P]) and proves the sequential half of "the kernel does not care": every lookup the page-table walks
of `vspace.rs` make decides only from bits other than 5 and 6.

* `adBits` = `0x60`, `adKeep` = its complement. `ADOr v x`: `x` is `v` with some A/D bits ORed in. `ADEq v w`:
  `v` and `w` agree off bits 5 and 6. `ADEqM m m'`: memories agreeing word by word off bits 5 and 6.
* **`or_and_eq`**, **`and_eq_of_adEq`**: a mask with bits 5, 6 clear (`k &&& adBits = 0`) sees the same bits of
  `v` and of `v ||| b` (`b` an A/D set), and of two `ADEq` words. `adOr_adEq`, `adOr_present`.
  Every mask the walks / unmaps / maps test is such a mask (`kP`, `kPS`, `kADDR`, `kLarge`, `kHuge`, `kRW`, `kUS`,
  `kXD`, `kPWT`, `kPCD`, `kPATL`).
* **`MmuAD PW m a x`** [P] (the hardware semantics, below): the MMU may at any time replace a *present* word `a`
  of the paging-structure set `PW` by `m a ||| b`, `b ⊆ {A, D}`, atomically.
* **`lookup_pdpt_slot_ad`**, **`lookup_pd_slot_ad`**, **`lookup_pt_slot_ad`**: the three walks of
  `crates/fl4-core/src/arch/x86_64/vspace.rs` (l. 119-143, used by `small_page_entry`, `unmap_page`,
  `unmap_page_unflushed`, `page_entry_slot`, `mapped_entry`, `localinv::plan_with`) give the same result on two
  stores whose memories are `ADEqM` (they read entries only through `& P_PRESENT`, `& P_PS`, `& ADDR_MASK`).
  `small_page_entry_ad`.

No premise beyond `MmuAD`'s [P]; no existing statement or file changed.

## `MmuAD` [P] — its basis
Intel SDM Vol. 3A (Order 253668) §4.8 "Accessed and Dirty Flags": "Whenever the processor uses a paging-structure
entry as part of linear-address translation, it sets the accessed flag in that entry (if it is not already set)";
"Whenever there is a write to a linear address, the processor sets the dirty flag (if it is not already set) in
the paging-structure entry that identifies the final physical address"; the flags are sticky (only software
clears them). §9.1.2.1 "Automatic Locking" (§8.1.2.1 in older editions): "When updating page-directory and
page-table entries ... the processor uses locked cycles to set the accessed and dirty flag" — so the update is an
atomic read-modify-write (`m a ||| b` of the value at that instant). §4.7 / §4.5: a walk that meets a non-present
entry (P = 0) stops with a page fault and uses no entry below; A/D are set only in entries the translation uses,
which are present. Bit 6 of a non-leaf PML4E / PDPTE / PDE is ignored and never set; `MmuAD` over-approximates by
allowing A and D on every present entry (more behaviours: sound). AMD APM Vol. 2 §5.4.2 is the same for AMD
long-mode tables. EPT entries get A/D only with EPTP bit 6 (SDM §30.3.5); FL4 writes EPTP = `root | 6 | 3 << 3`
(bit 6 clear, `fl4-arch-x86_64/src/vm.rs` l. 1002, 1216), so Intel EPT words are never hardware-written. On AMD the
EPT objects are nested page tables (`NESTED_CR3`, vm.rs l. 1163), which the nested walk does write; that happens
only while a guest runs (a VCPU), outside this model's scope (`vcpus = ∅`). Known deviation not modelled: Intel
Knights Landing erratum (A/D may be set on a non-present entry); FL4 does not claim that part.
-/
import Fl4Proofs.P3.VsPt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.MmuAD
open fl4_core Fl4Proofs.P1

/-! ## Bits -/

/-- The accessed and dirty bits (5 and 6). -/
def adBits : U64 := 96#u64
/-- Every bit but 5 and 6. -/
def adKeep : U64 := 18446744073709551519#u64

/-- `x` is `v` with some A/D bits ORed in. -/
def ADOr (v x : U64) : Prop := ∃ b : U64, b &&& adKeep = 0#u64 ∧ x = v ||| b

/-- `v` and `w` agree off bits 5 and 6. -/
def ADEq (v w : U64) : Prop := v &&& adKeep = w &&& adKeep

/-- Two memories agree word by word off bits 5 and 6. -/
def ADEqM (m m' : U64 → U64) : Prop := ∀ a, ADEq (m a) (m' a)

theorem keep_or_bits (i : Nat) (hi : i < 64) :
    ((18446744073709551519#64 : BitVec 64)[i] || (96#64 : BitVec 64)[i]) = true := by
  have e : (18446744073709551519#64 : BitVec 64) ||| 96#64 = BitVec.allOnes 64 := by decide
  have h := congrArg (fun y : BitVec 64 => y[i]'hi) e
  simpa only [BitVec.getElem_or, BitVec.getElem_allOnes] using h

theorem bv_or_and (v b k : BitVec 64) (hb : b &&& 18446744073709551519#64 = 0#64) (hk : k &&& 96#64 = 0#64) :
    (v ||| b) &&& k = v &&& k := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  have h1 := congrArg (fun y : BitVec 64 => y[i]'hi) hb
  have h2 := congrArg (fun y : BitVec 64 => y[i]'hi) hk
  have h3 := keep_or_bits i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero] at h1 h2 h3 ⊢
  cases hv : v[i] <;> cases hb' : b[i] <;> cases hk' : k[i] <;>
    cases e1 : (18446744073709551519#64 : BitVec 64)[i] <;> cases e2 : (96#64 : BitVec 64)[i] <;> simp_all

theorem bv_and_of_keep (v w k : BitVec 64) (h : v &&& 18446744073709551519#64 = w &&& 18446744073709551519#64)
    (hk : k &&& 96#64 = 0#64) : v &&& k = w &&& k := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  have h1 := congrArg (fun y : BitVec 64 => y[i]'hi) h
  have h2 := congrArg (fun y : BitVec 64 => y[i]'hi) hk
  have h3 := keep_or_bits i hi
  simp only [BitVec.getElem_and, BitVec.getElem_zero] at h1 h2 h3 ⊢
  cases hv : v[i] <;> cases hw : w[i] <;> cases hk' : k[i] <;>
    cases e1 : (18446744073709551519#64 : BitVec 64)[i] <;> cases e2 : (96#64 : BitVec 64)[i] <;> simp_all

/-- **A mask with bits 5 and 6 clear sees the same bits of `v` and `v ||| b`** for an A/D set `b`. -/
theorem or_and_eq {v b k : U64} (hb : b &&& adKeep = 0#u64) (hk : k &&& adBits = 0#u64) :
    (v ||| b) &&& k = v &&& k := by
  have hb' := congrArg UScalar.bv hb
  have hk' := congrArg UScalar.bv hk
  change b.bv &&& 18446744073709551519#64 = 0#64 at hb'
  change k.bv &&& 96#64 = 0#64 at hk'
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  change (v.bv ||| b.bv) &&& k.bv = v.bv &&& k.bv
  exact bv_or_and v.bv b.bv k.bv hb' hk'

/-- **A mask with bits 5 and 6 clear sees the same bits of two `ADEq` words.** -/
theorem and_eq_of_adEq {v w k : U64} (h : ADEq v w) (hk : k &&& adBits = 0#u64) : v &&& k = w &&& k := by
  have h' := congrArg UScalar.bv h
  have hk' := congrArg UScalar.bv hk
  change v.bv &&& 18446744073709551519#64 = w.bv &&& 18446744073709551519#64 at h'
  change k.bv &&& 96#64 = 0#64 at hk'
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  change v.bv &&& k.bv = w.bv &&& k.bv
  exact bv_and_of_keep v.bv w.bv k.bv h' hk'

theorem kKeep : adKeep &&& adBits = 0#u64 := by decide

/-- An A/D update keeps every other bit. -/
theorem adOr_adEq {v x : U64} (h : ADOr v x) : ADEq x v := by
  obtain ⟨b, hb, rfl⟩ := h
  exact or_and_eq hb kKeep

theorem adEq_symm {v w : U64} (h : ADEq v w) : ADEq w v := h.symm

theorem adEq_trans {u v w : U64} (h1 : ADEq u v) (h2 : ADEq v w) : ADEq u w := h1.trans h2

theorem adEqM_refl (m : U64 → U64) : ADEqM m m := fun _ => rfl

/-- The masks the walks and the unmap / map checks of `vspace.rs` / `ept.rs` test: none has bit 5 or 6. -/
theorem kP : (1#u64 : U64) &&& adBits = 0#u64 := by decide
theorem kPS : (128#u64 : U64) &&& adBits = 0#u64 := by decide
theorem kADDR : vspace.ADDR_MASK &&& adBits = 0#u64 := by unfold vspace.ADDR_MASK; decide
theorem kLarge : (4503599625273344#u64 : U64) &&& adBits = 0#u64 := by decide
theorem kHuge : (4503598553628672#u64 : U64) &&& adBits = 0#u64 := by decide
theorem kRW : (2#u64 : U64) &&& adBits = 0#u64 := by decide
theorem kUS : (4#u64 : U64) &&& adBits = 0#u64 := by decide
theorem kPWT : (8#u64 : U64) &&& adBits = 0#u64 := by decide
theorem kPCD : (16#u64 : U64) &&& adBits = 0#u64 := by decide
theorem kPATL : (4096#u64 : U64) &&& adBits = 0#u64 := by decide
theorem kXD : (9223372036854775808#u64 : U64) &&& adBits = 0#u64 := by decide

/-- An A/D update keeps the present bit. -/
theorem adOr_present {v x : U64} (h : ADOr v x) : x &&& 1#u64 = v &&& 1#u64 :=
  and_eq_of_adEq (adOr_adEq h) kP

/-! ## The hardware step -/

/-- **`MmuAD`** [P] (module docstring, Intel SDM Vol. 3A §4.8, §9.1.2.1; AMD APM Vol. 2 §5.4.2): the page walker
may, between any two steps of any core, replace a present word `a` of the paging-structure set `PW` by
`m a ||| b` with `b` a set of A/D bits, atomically (a locked read-modify-write of the value at that instant).
`chg`: a write that changes nothing is no step. -/
structure MmuAD (PW : U64 → Prop) (m : U64 → U64) (a x : U64) : Prop where
  pw : PW a
  present : m a &&& 1#u64 ≠ 0#u64
  ad : ADOr (m a) x
  chg : x ≠ m a

/-- An A/D step leaves memory `ADEqM` to what it was. -/
theorem MmuAD.adEqM {PW : U64 → Prop} {m : U64 → U64} {a x : U64} (h : MmuAD PW m a x) :
    ADEqM m (Function.update m a x) := by
  intro y
  by_cases hy : y = a
  · subst hy; rw [Function.update_self]; exact adEq_symm (adOr_adEq h.ad)
  · rw [Function.update_of_ne hy]; rfl

/-- A word an A/D step writes is present before and after. -/
theorem MmuAD.present' {PW : U64 → Prop} {m : U64 → U64} {a x : U64} (h : MmuAD PW m a x) :
    x &&& 1#u64 ≠ 0#u64 := by
  rw [adOr_present h.ad]; exact h.present

/-! ## The walks decide only from bits other than A and D -/

section walk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
open Fl4Proofs.P3.Vs (P_PRESENT_eq P_PS_eq)

theorem lookup_pdpt_slot_ad {σ σ' : S} (h : ADEqM (L.mem σ) (L.mem σ')) (r v : U64) :
    vspace.lookup_pdpt_slot st σ r v = vspace.lookup_pdpt_slot st σ' r v := by
  have h1 : ∀ a, L.mem σ a &&& 1#u64 = L.mem σ' a &&& 1#u64 := fun a => and_eq_of_adEq (h a) kP
  have hA : ∀ a, L.mem σ a &&& vspace.ADDR_MASK = L.mem σ' a &&& vspace.ADDR_MASK :=
    fun a => and_eq_of_adEq (h a) kADDR
  unfold vspace.lookup_pdpt_slot vspace.entry vspace.table_of
  simp only [L.read_eq, P_PRESENT_eq, lift, bind_ok, bind_tc_ok, h1, hA]

theorem lookup_pd_slot_ad {σ σ' : S} (h : ADEqM (L.mem σ) (L.mem σ')) (r v : U64) :
    vspace.lookup_pd_slot st σ r v = vspace.lookup_pd_slot st σ' r v := by
  have h1 : ∀ a, L.mem σ a &&& 1#u64 = L.mem σ' a &&& 1#u64 := fun a => and_eq_of_adEq (h a) kP
  have h7 : ∀ a, L.mem σ a &&& 128#u64 = L.mem σ' a &&& 128#u64 := fun a => and_eq_of_adEq (h a) kPS
  have hA : ∀ a, L.mem σ a &&& vspace.ADDR_MASK = L.mem σ' a &&& vspace.ADDR_MASK :=
    fun a => and_eq_of_adEq (h a) kADDR
  unfold vspace.lookup_pd_slot vspace.table_of
  rw [lookup_pdpt_slot_ad h]
  simp only [L.read_eq, P_PRESENT_eq, P_PS_eq, lift, bind_ok, bind_tc_ok, h1, h7, hA]

theorem lookup_pt_slot_ad {σ σ' : S} (h : ADEqM (L.mem σ) (L.mem σ')) (r v : U64) :
    vspace.lookup_pt_slot st σ r v = vspace.lookup_pt_slot st σ' r v := by
  have h1 : ∀ a, L.mem σ a &&& 1#u64 = L.mem σ' a &&& 1#u64 := fun a => and_eq_of_adEq (h a) kP
  have h7 : ∀ a, L.mem σ a &&& 128#u64 = L.mem σ' a &&& 128#u64 := fun a => and_eq_of_adEq (h a) kPS
  have hA : ∀ a, L.mem σ a &&& vspace.ADDR_MASK = L.mem σ' a &&& vspace.ADDR_MASK :=
    fun a => and_eq_of_adEq (h a) kADDR
  unfold vspace.lookup_pt_slot vspace.table_of
  rw [lookup_pd_slot_ad h]
  simp only [L.read_eq, P_PRESENT_eq, P_PS_eq, lift, bind_ok, bind_tc_ok, h1, h7, hA]

theorem small_page_entry_ad {σ σ' : S} (h : ADEqM (L.mem σ) (L.mem σ')) (r v : U64) :
    vspace.small_page_entry st σ r v = vspace.small_page_entry st σ' r v := by
  unfold vspace.small_page_entry
  rw [lookup_pt_slot_ad h]

end walk

end Fl4Proofs.P2.MmuAD
