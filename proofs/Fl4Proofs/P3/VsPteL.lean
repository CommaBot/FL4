/-
P3 (DESIGN.md §9), VSpace: **large and huge page entries** (FL4
`make_user_page` with `large`): the low bits `lowBitsL` (PAT at bit 12, PS
set), and the entries against l4v's `LargePagePDE` (`pde_of_make_large`) and
`HugePagePDPTE` (`pdpte_of_make_huge`, without PAT: l4v's `attr_mask'`
drops it for huge pages, FL4 sets bit 12 as C seL4 does).
-/
import Fl4Proofs.P3.VsFrameUnmapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

/-- The low bits of a large or huge page entry (FL4 `make_user_page`, in its
`|` order). -/
def lowBitsL (pwt pcd pat us rw xd : Bool) : BitVec 64 :=
  (if pwt then 8 else 0) ||| ((if pcd then 16 else 0) ||| ((if pat then 4096 else 0) |||
    ((if us then 4 else 0) ||| ((if rw then 2 else 0) ||| (1 ||| (128 ||| (if xd then 0x8000000000000000 else 0)))))))

theorem lowBitsL_bits (pwt pcd pat us rw xd : Bool) :
    (lowBitsL pwt pcd pat us rw xd).getLsbD 0 = true ∧ (lowBitsL pwt pcd pat us rw xd).getLsbD 1 = rw ∧
    (lowBitsL pwt pcd pat us rw xd).getLsbD 2 = us ∧ (lowBitsL pwt pcd pat us rw xd).getLsbD 3 = pwt ∧
    (lowBitsL pwt pcd pat us rw xd).getLsbD 4 = pcd ∧ (lowBitsL pwt pcd pat us rw xd).getLsbD 7 = true ∧
    (lowBitsL pwt pcd pat us rw xd).getLsbD 12 = pat ∧
    (lowBitsL pwt pcd pat us rw xd) &&& 4503599625273344#64 = 0 ∧
    (lowBitsL pwt pcd pat us rw xd) &&& 4503598553628672#64 = 0 := by
  cases pwt <;> cases pcd <;> cases pat <;> cases us <;> cases rw <;> cases xd <;> decide

theorem shl_c12 : (1#u64 <<< 12#i32) = ok 4096#u64 := by rw [shl_eq _ _ (by decide) (by decide)]; rfl

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`make_user_page` of a large or huge page.** -/
theorem make_user_page_large (s : S) (paddr attr rights : U64) :
    vspace.make_user_page st s paddr attr rights true ⦃ e => ∃ xd : Bool, e.bv =
      (paddr.bv &&& 4503599627366400#64) ||| lowBitsL ((attr &&& 1#u64) != 0#u64) ((attr &&& 2#u64) != 0#u64)
        ((attr &&& 4#u64) != 0#u64) (decide (rights ≠ capability.VM_KERNEL_ONLY))
        (decide (rights ≠ capability.VM_READ_ONLY)) xd ⦄ := by
  unfold vspace.make_user_page vspace.attr_bits vspace.super_user vspace.writable vspace.xd_bit vspace.nx_enabled
    vspace.P_PAT_LARGE vspace.P_PWT vspace.P_PCD vspace.P_US vspace.P_RW vspace.P_PRESENT vspace.P_XD vspace.ADDR_MASK
    vspace.P_PS obj.ks_get
  simp only [↓reduceIte, lift, bind_ok, shl_c0, shl_c1, shl_c2, shl_c3, shl_c4, shl_c7, shl_c12,
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
  simp [hk, hr, lowBitsL, UScalar.bv_or, BitVec.or_assoc]

end

theorem attrs_mem' (attr : U64) :
    (Fl4Spec.VMAttribute.ptAttr .writeThrough ∈ Fl4Spec.attribsFromWord attr.bv \ Fl4Spec.attrMask' ↔
      attr.bv.getLsbD 0 = true) ∧
    (Fl4Spec.VMAttribute.ptAttr .cacheDisabled ∈ Fl4Spec.attribsFromWord attr.bv \ Fl4Spec.attrMask' ↔
      attr.bv.getLsbD 1 = true) := by
  unfold Fl4Spec.attribsFromWord Fl4Spec.attrMask' Fl4Spec.attrMask Fl4Spec.testBit
  cases h0 : attr.bv.getLsbD 0 <;> cases h1 : attr.bv.getLsbD 1 <;> cases h2 : attr.bv.getLsbD 2 <;>
    simp [Set.mem_sdiff, Set.mem_insert_iff]

/-- Low bits of an address with the given mask. -/
theorem masked_low {p : U64} {m : U64} (hp : (p &&& m) = p) {k : Nat} (hm : m.bv.getLsbD k = false) :
    p.bv.getLsbD k = false := by
  have : (p &&& m).bv.getLsbD k = p.bv.getLsbD k := by rw [hp]
  rw [UScalar.bv_and, BitVec.getLsbD_and, hm, Bool.and_false] at this
  exact this.symm

section Ents
variable {paddr attr vm e : U64} {xd : Bool}

theorem large_bit {k : Nat} (hk : k < 21) (hpa : (paddr &&& 4503599625273344#u64) = paddr)
    (he : e.bv = (paddr.bv &&& 4503599627366400#64) ||| lowBitsL ((attr &&& 1#u64) != 0#u64) ((attr &&& 2#u64) != 0#u64)
        ((attr &&& 4#u64) != 0#u64) (decide (vm ≠ capability.VM_KERNEL_ONLY))
        (decide (vm ≠ capability.VM_READ_ONLY)) xd) :
    e.bv.getLsbD k = (lowBitsL ((attr &&& 1#u64) != 0#u64) ((attr &&& 2#u64) != 0#u64)
        ((attr &&& 4#u64) != 0#u64) (decide (vm ≠ capability.VM_KERNEL_ONLY))
        (decide (vm ≠ capability.VM_READ_ONLY)) xd).getLsbD k := by
  have hm : (4503599625273344#u64 : U64).bv.getLsbD k = false := by
    show (4503599625273344#64 : BitVec 64).getLsbD k = false
    interval_cases k <;> decide
  rw [he, or_bit, BitVec.getLsbD_and, masked_low hpa hm]; simp

/-- **The large page entry FL4 builds is l4v's**. -/
theorem pde_of_make_large {L1 : Set U64} (hvm : VmRightsOk vm) (hpa : (paddr &&& 4503599625273344#u64) = paddr)
    (he : e.bv = (paddr.bv &&& 4503599627366400#64) ||| lowBitsL ((attr &&& 1#u64) != 0#u64) ((attr &&& 2#u64) != 0#u64)
        ((attr &&& 4#u64) != 0#u64) (decide (vm ≠ capability.VM_KERNEL_ONLY))
        (decide (vm ≠ capability.VM_READ_ONLY)) xd) :
    PDERel L1 e (.largePagePDE paddr.bv (Fl4Spec.attribsFromWord attr.bv \ Fl4Spec.attrMask) (vmRightsOf vm)) := by
  obtain ⟨b0, b1, b2, b3, b4, b7, b12, bm, -⟩ := lowBitsL_bits ((attr &&& 1#u64) != 0#u64) ((attr &&& 2#u64) != 0#u64)
    ((attr &&& 4#u64) != 0#u64) (decide (vm ≠ capability.VM_KERNEL_ONLY)) (decide (vm ≠ capability.VM_READ_ONLY)) xd
  have hbit := fun k hk => large_bit (k := k) hk hpa he
  have hc1 : ((attr &&& 1#u64) != 0#u64) = attr.bv.getLsbD 0 := and_ne0 attr 0 (by decide) _ (by decide)
  have hc2 : ((attr &&& 2#u64) != 0#u64) = attr.bv.getLsbD 1 := and_ne0 attr 1 (by decide) _ (by decide)
  have hc3 : ((attr &&& 4#u64) != 0#u64) = attr.bv.getLsbD 2 := and_ne0 attr 2 (by decide) _ (by decide)
  obtain ⟨a1, a2, a3⟩ := attrs_mem attr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (e &&& 1#u64) ≠ 0#u64
    have := and_ne0 e 0 (by decide) 1#u64 (by decide)
    rw [hbit 0 (by decide), b0] at this
    intro h; rw [h] at this; exact absurd this (by decide)
  · show (e &&& 128#u64) ≠ 0#u64
    have := and_ne0 e 7 (by decide) 128#u64 (by decide)
    rw [hbit 7 (by decide), b7] at this
    intro h; rw [h] at this; exact absurd this (by decide)
  · show (e &&& 4503599625273344#u64).bv = paddr.bv
    have hM : (4503599625273344#u64 : U64).bv = 4503599625273344#64 := rfl
    have hpa' : paddr.bv &&& 4503599625273344#64 = paddr.bv := by
      have := congrArg UScalar.bv hpa; rwa [UScalar.bv_and] at this
    have hMM : (4503599627366400#64 : BitVec 64) &&& 4503599625273344#64 = 4503599625273344#64 := by decide
    simp only [UScalar.bv_and, he, hM, BitVec.and_or_distrib_right, bm, BitVec.and_assoc, hMM, hpa']
    simp
  · unfold PteRights bitL
    rw [hbit 2 (by decide), hbit 1 (by decide), b2, b1]
    exact vmRightsOf_eq hvm
  · unfold PteAttrsL bitL
    rw [hbit 3 (by decide), hbit 4 (by decide), hbit 12 (by decide), b3, b4, b12, hc1, hc2, hc3]
    exact ⟨a1, a2, a3⟩

/-- **The huge page entry FL4 builds is l4v's** (PAT aside). -/
theorem pdpte_of_make_huge {L2 : Set U64} (hvm : VmRightsOk vm) (hpa : (paddr &&& 4503598553628672#u64) = paddr)
    (he : e.bv = (paddr.bv &&& 4503599627366400#64) ||| lowBitsL ((attr &&& 1#u64) != 0#u64) ((attr &&& 2#u64) != 0#u64)
        ((attr &&& 4#u64) != 0#u64) (decide (vm ≠ capability.VM_KERNEL_ONLY))
        (decide (vm ≠ capability.VM_READ_ONLY)) xd) :
    PDPTERel L2 e (.hugePagePDPTE paddr.bv (Fl4Spec.attribsFromWord attr.bv \ Fl4Spec.attrMask') (vmRightsOf vm)) := by
  obtain ⟨b0, b1, b2, b3, b4, b7, -, -, bm⟩ := lowBitsL_bits ((attr &&& 1#u64) != 0#u64) ((attr &&& 2#u64) != 0#u64)
    ((attr &&& 4#u64) != 0#u64) (decide (vm ≠ capability.VM_KERNEL_ONLY)) (decide (vm ≠ capability.VM_READ_ONLY)) xd
  have hpaL : (paddr &&& 4503599625273344#u64) = paddr := by
    apply eq_of_bv
    show UScalar.bv (paddr &&& 4503599625273344#u64) = UScalar.bv paddr
    have h1 : (paddr &&& 4503599625273344#u64).bv = paddr.bv &&& 4503599625273344#64 := rfl
    have h2 : (paddr &&& 4503598553628672#u64).bv = paddr.bv := by rw [hpa]
    have h3 : (paddr &&& 4503598553628672#u64).bv = paddr.bv &&& 4503598553628672#64 := rfl
    rw [h3] at h2
    rw [h1, ← h2, BitVec.and_assoc,
      show (4503598553628672#64 : BitVec 64) &&& 4503599625273344#64 = 4503598553628672#64 by decide]
    exact h2
  have hbit := fun k hk => large_bit (k := k) hk hpaL he
  have hc1 : ((attr &&& 1#u64) != 0#u64) = attr.bv.getLsbD 0 := and_ne0 attr 0 (by decide) _ (by decide)
  have hc2 : ((attr &&& 2#u64) != 0#u64) = attr.bv.getLsbD 1 := and_ne0 attr 1 (by decide) _ (by decide)
  obtain ⟨a1, a2⟩ := attrs_mem' attr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (e &&& 1#u64) ≠ 0#u64
    have := and_ne0 e 0 (by decide) 1#u64 (by decide)
    rw [hbit 0 (by decide), b0] at this
    intro h; rw [h] at this; exact absurd this (by decide)
  · show (e &&& 128#u64) ≠ 0#u64
    have := and_ne0 e 7 (by decide) 128#u64 (by decide)
    rw [hbit 7 (by decide), b7] at this
    intro h; rw [h] at this; exact absurd this (by decide)
  · show (e &&& 4503598553628672#u64).bv = paddr.bv
    have hM : (4503598553628672#u64 : U64).bv = 4503598553628672#64 := rfl
    have hpa' : paddr.bv &&& 4503598553628672#64 = paddr.bv := by
      have := congrArg UScalar.bv hpa; rwa [UScalar.bv_and] at this
    have hMM : (4503599627366400#64 : BitVec 64) &&& 4503598553628672#64 = 4503598553628672#64 := by decide
    simp only [UScalar.bv_and, he, hM, BitVec.and_or_distrib_right, bm, BitVec.and_assoc, hMM, hpa']
    simp
  · unfold PteRights bitL
    rw [hbit 2 (by decide), hbit 1 (by decide), b2, b1]
    exact vmRightsOf_eq hvm
  · unfold PteAttrsH bitL
    rw [hbit 3 (by decide), hbit 4 (by decide), b3, b4, hc1, hc2]
    exact ⟨a1, a2⟩

end Ents

end

end Fl4Proofs.P3.Vs
