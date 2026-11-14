/-
P3 (DESIGN.md §9), VSpace: **the contents of a 4K page entry**.

FL4's `make_user_page` builds a PTE word from the frame's physical address,
the mapping attributes and the VM rights: the address bits, `P` (bit 0),
`RW` (1, unless read-only), `US` (2, unless kernel-only), `PWT` (3), `PCD`
(4), `PAT` (7, for a 4K page) from attribute bits 0..2, and `XD` (63) from
FL4's `EXECUTE_NEVER` attribute (bit 3) when NX is enabled.

l4v's `SmallPagePTE frame attrs rights` (`create_mapping_entries`: `attrs =
attribs_from_word attr - attr_mask`) has no execute-disable attribute in
mappings it creates (`attr_mask` removes it), so `XD` is not related: FL4's
`EXECUTE_NEVER` is beyond l4v's X64 model.

* `lowBits`: the low bits FL4 sets; `lowBits_bits` reads them back;
* `make_user_page_4k`: the word is `(paddr & ADDR_MASK) | lowBits …`;
* `PteRights`, `PteAttrs`: the rights and the cache attributes of a word.
-/
import Fl4Proofs.P3.VsPt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

/-- The low bits of a 4K PTE (FL4 `make_user_page`, in its `|` order). -/
def lowBits (pwt pcd pat us rw xd : Bool) : BitVec 64 :=
  (if pwt then 8 else 0) ||| ((if pcd then 16 else 0) ||| ((if pat then 128 else 0) |||
    ((if us then 4 else 0) ||| ((if rw then 2 else 0) ||| (1 ||| (0 ||| (if xd then 0x8000000000000000 else 0)))))))

theorem lowBits_bits (pwt pcd pat us rw xd : Bool) :
    (lowBits pwt pcd pat us rw xd).getLsbD 0 = true ∧ (lowBits pwt pcd pat us rw xd).getLsbD 1 = rw ∧
    (lowBits pwt pcd pat us rw xd).getLsbD 2 = us ∧ (lowBits pwt pcd pat us rw xd).getLsbD 3 = pwt ∧
    (lowBits pwt pcd pat us rw xd).getLsbD 4 = pcd ∧ (lowBits pwt pcd pat us rw xd).getLsbD 7 = pat ∧
    (lowBits pwt pcd pat us rw xd) &&& 4503599627366400#64 = 0 := by
  cases pwt <;> cases pcd <;> cases pat <;> cases us <;> cases rw <;> cases xd <;> decide

theorem shl_c0 : (1#u64 <<< 0#i32) = ok 1#u64 := by rw [shl_eq _ _ (by decide) (by decide)]; rfl
theorem shl_c1 : (1#u64 <<< 1#i32) = ok 2#u64 := by rw [shl_eq _ _ (by decide) (by decide)]; rfl
theorem shl_c2 : (1#u64 <<< 2#i32) = ok 4#u64 := by rw [shl_eq _ _ (by decide) (by decide)]; rfl
theorem shl_c3 : (1#u64 <<< 3#i32) = ok 8#u64 := by rw [shl_eq _ _ (by decide) (by decide)]; rfl
theorem shl_c4 : (1#u64 <<< 4#i32) = ok 16#u64 := by rw [shl_eq _ _ (by decide) (by decide)]; rfl
theorem shl_c7 : (1#u64 <<< 7#i32) = ok 128#u64 := by rw [shl_eq _ _ (by decide) (by decide)]; rfl
theorem shl_c63 : (1#u64 <<< 63#i32) = ok 9223372036854775808#u64 := by rw [shl_eq _ _ (by decide) (by decide)]; rfl

theorem ite_ok {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then ok a else ok b : Result α) = ok (if c then a else b) := by split <;> rfl

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`make_user_page` of a 4K page.** -/
theorem make_user_page_4k (s : S) (paddr attr rights : U64) :
    vspace.make_user_page st s paddr attr rights false ⦃ e => ∃ xd : Bool, e.bv =
      (paddr.bv &&& 4503599627366400#64) ||| lowBits ((attr &&& 1#u64) != 0#u64) ((attr &&& 2#u64) != 0#u64)
        ((attr &&& 4#u64) != 0#u64) (decide (rights ≠ capability.VM_KERNEL_ONLY))
        (decide (rights ≠ capability.VM_READ_ONLY)) xd ⦄ := by
  unfold vspace.make_user_page vspace.attr_bits vspace.super_user vspace.writable vspace.xd_bit vspace.nx_enabled
    vspace.P_PAT_4K vspace.P_PWT vspace.P_PCD vspace.P_US vspace.P_RW vspace.P_PRESENT vspace.P_XD vspace.ADDR_MASK
    obj.ks_get
  simp only [Bool.false_eq_true, ↓reduceIte, lift, bind_ok, shl_c0, shl_c1, shl_c2, shl_c3, shl_c4, shl_c7,
    shl_c63, ite_ok, LawfulStore.ks_base_eq, LawfulStore.read_eq]
  refine (WP.spec_ok _).2 ⟨((attr &&& fl4_abi.consts.vm_attr.EXECUTE_NEVER) != 0#u64) &&
    ((L.mem s (core.num.U64.wrapping_add (L.ksb s) layout.ks.FEATURES) &&& layout.ks.FEATURE_NX) != 0#u64), ?_⟩
  generalize (attr &&& 1#u64 != 0#u64) = b1
  generalize (attr &&& 2#u64 != 0#u64) = b2
  generalize (attr &&& 4#u64 != 0#u64) = b3
  generalize (attr &&& fl4_abi.consts.vm_attr.EXECUTE_NEVER != 0#u64) = b4
  generalize (L.mem s (core.num.U64.wrapping_add (L.ksb s) layout.ks.FEATURES) &&& layout.ks.FEATURE_NX != 0#u64) = b5
  by_cases hk : rights = capability.VM_KERNEL_ONLY <;> by_cases hr : rights = capability.VM_READ_ONLY <;>
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
  simp [hk, hr, lowBits, UScalar.bv_or, BitVec.or_assoc]


end

/-! ## The entry `make_user_page` builds -/

theorem and_ne0 (w : U64) (k : Nat) (hk : k < 64) (c : U64) (hc : c.bv = BitVec.twoPow 64 k) :
    ((w &&& c) != 0#u64) = w.bv.getLsbD k := by
  have h : (w &&& c).bv = if w.bv.getLsbD k then BitVec.twoPow 64 k else 0 := by
    simp only [UScalar.bv_and, hc]
    exact BitVec.and_twoPow _ _
  cases hb : w.bv.getLsbD k
  · rw [hb] at h
    have : (w &&& c) = 0#u64 := UScalar.eq_of_val_eq (by
      show (w &&& c).bv.toNat = 0; rw [h]; simp)
    rw [this]; rfl
  · rw [hb] at h
    have hne : (w &&& c) ≠ 0#u64 := fun e => by
      have h3 : (w &&& c).bv = 0#64 := by rw [e]; rfl
      rw [h, if_pos rfl] at h3
      have h4 : (BitVec.twoPow 64 k).getLsbD k = (0#64).getLsbD k := by rw [h3]
      rw [BitVec.getLsbD_twoPow, BitVec.getLsbD_zero] at h4
      simp [hk] at h4
    simpa using hne

theorem or_bit (a b : BitVec 64) (k : Nat) : (a ||| b).getLsbD k = (a.getLsbD k || b.getLsbD k) := BitVec.getLsbD_or

theorem addr_lowbit (p : U64) (k : Nat) (hk : k < 12) : (p.bv &&& 4503599627366400#64).getLsbD k = false := by
  rw [BitVec.getLsbD_and]
  have : (4503599627366400#64 : BitVec 64).getLsbD k = false := by
    interval_cases k <;> decide
  rw [this]; simp

theorem addr_bit63 (p : U64) : (p.bv &&& 4503599627366400#64).getLsbD 63 = false := by
  rw [BitVec.getLsbD_and]
  have : (4503599627366400#64 : BitVec 64).getLsbD 63 = false := by decide
  rw [this]; simp

/-- The FL4 VM rights encodings. -/
def VmRightsOk (vm : U64) : Prop := vm = capability.VM_KERNEL_ONLY ∨ vm = capability.VM_READ_ONLY ∨
  vm = capability.VM_READ_WRITE

theorem vmRightsOf_eq {vm : U64} (h : VmRightsOk vm) :
    vmRightsOf vm = if decide (vm ≠ capability.VM_KERNEL_ONLY) = false then Fl4Spec.vmKernelOnly
      else if decide (vm ≠ capability.VM_READ_ONLY) then Fl4Spec.vmReadWrite else Fl4Spec.vmReadOnly := by
  unfold VmRightsOk at h
  unfold capability.VM_KERNEL_ONLY capability.VM_READ_ONLY capability.VM_READ_WRITE at *
  rcases h with rfl | rfl | rfl <;> simp (config := {decide := true}) [vmRightsOf]

theorem attrs_mem (attr : U64) :
    (Fl4Spec.VMAttribute.ptAttr .writeThrough ∈ Fl4Spec.attribsFromWord attr.bv \ Fl4Spec.attrMask ↔
      attr.bv.getLsbD 0 = true) ∧
    (Fl4Spec.VMAttribute.ptAttr .cacheDisabled ∈ Fl4Spec.attribsFromWord attr.bv \ Fl4Spec.attrMask ↔
      attr.bv.getLsbD 1 = true) ∧
    (Fl4Spec.VMAttribute.pat ∈ Fl4Spec.attribsFromWord attr.bv \ Fl4Spec.attrMask ↔ attr.bv.getLsbD 2 = true) := by
  unfold Fl4Spec.attribsFromWord Fl4Spec.attrMask Fl4Spec.testBit
  cases h0 : attr.bv.getLsbD 0 <;> cases h1 : attr.bv.getLsbD 1 <;> cases h2 : attr.bv.getLsbD 2 <;>
    simp [Set.mem_sdiff, Set.mem_insert_iff]

/-- **The 4K entry FL4 builds is l4v's**: `make_user_page paddr attr vm`
relates to `SmallPagePTE (paddr & ADDR_MASK) (attribs_from_word attr -
attr_mask) (vm_rights vm)`. -/
theorem pte_of_make {paddr attr vm e : U64} (hvm : VmRightsOk vm) {xd : Bool}
    (he : e.bv = (paddr.bv &&& 4503599627366400#64) ||| lowBits ((attr &&& 1#u64) != 0#u64) ((attr &&& 2#u64) != 0#u64)
        ((attr &&& 4#u64) != 0#u64) (decide (vm ≠ capability.VM_KERNEL_ONLY))
        (decide (vm ≠ capability.VM_READ_ONLY)) xd) :
    PTERel e (.smallPagePTE (paddr &&& 4503599627366400#u64).bv (Fl4Spec.attribsFromWord attr.bv \ Fl4Spec.attrMask)
      (vmRightsOf vm)) := by
  obtain ⟨b0, b1, b2, b3, b4, b7, bm⟩ := lowBits_bits ((attr &&& 1#u64) != 0#u64) ((attr &&& 2#u64) != 0#u64)
    ((attr &&& 4#u64) != 0#u64) (decide (vm ≠ capability.VM_KERNEL_ONLY)) (decide (vm ≠ capability.VM_READ_ONLY)) xd
  have hbit : ∀ k, k < 12 → e.bv.getLsbD k = (lowBits ((attr &&& 1#u64) != 0#u64) ((attr &&& 2#u64) != 0#u64)
        ((attr &&& 4#u64) != 0#u64) (decide (vm ≠ capability.VM_KERNEL_ONLY))
        (decide (vm ≠ capability.VM_READ_ONLY)) xd).getLsbD k := by
    intro k hk; rw [he, or_bit, addr_lowbit _ _ hk]; simp
  have hc1 : ((attr &&& 1#u64) != 0#u64) = attr.bv.getLsbD 0 := and_ne0 attr 0 (by decide) _ (by decide)
  have hc2 : ((attr &&& 2#u64) != 0#u64) = attr.bv.getLsbD 1 := and_ne0 attr 1 (by decide) _ (by decide)
  have hc3 : ((attr &&& 4#u64) != 0#u64) = attr.bv.getLsbD 2 := and_ne0 attr 2 (by decide) _ (by decide)
  obtain ⟨a1, a2, a3⟩ := attrs_mem attr
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (e &&& 1#u64) ≠ 0#u64
    have := and_ne0 e 0 (by decide) 1#u64 (by decide)
    rw [hbit 0 (by decide), b0] at this
    intro h; rw [h] at this; exact absurd this (by decide)
  · show (e &&& 4503599627366400#u64).bv = (paddr &&& 4503599627366400#u64).bv
    have hM : (4503599627366400#u64 : U64).bv = 4503599627366400#64 := rfl
    simp only [UScalar.bv_and, he, hM, BitVec.and_or_distrib_right, bm, BitVec.and_assoc,
      BitVec.and_self]
    simp
  · unfold PteRights bitL
    rw [hbit 2 (by decide), hbit 1 (by decide), b2, b1]
    exact vmRightsOf_eq hvm
  · unfold PteAttrs bitL
    rw [hbit 3 (by decide), hbit 4 (by decide), hbit 7 (by decide), b3, b4, b7, hc1, hc2, hc3]
    exact ⟨a1, a2, a3⟩

end

end Fl4Proofs.P3.Vs
