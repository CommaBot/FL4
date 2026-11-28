/-
P3 (DESIGN.md §9), untyped: **the reset's chunk loop at `J`** (handoff utj.md
Round 12, items 3c/3d).

FL4's `reset_untyped` loop (`reset_untyped_loop`, chunks of 64 KiB from the
top of the used part down): clear the chunk (`JAtZ.zeroRg`: the region is
clear of every ghost, `RgClear`), lower the cap's free index to the chunk's
base (`JAtZ.setFiJ`), and between chunks the preemption point at `J`
(XTopJointPP's `JAtZ.ppJ`, platform `PPPlat` [P]; `PPR0` carried, kept by the
slot write). The spec takes the chunks of l4v `reset_untyped_cap` exactly
(UtResetSpecJ's `RContX`, `chunk_memX`: the chunk's clear finds its bytes
zero, `delete_objects` having zeroed the region; the preemption point's
outcome is FL4's, the last chunk's the one keeping the state, `pp_ok`).

* `RgClear`: the region is clear of `H`'s objects, the VSpace sets, the
  IPC-buffer words, the kernel-state block, every core's node and the
  ASID-table area (what `JAtZ.zeroJR` asks, for any part of the region).
* `JAtZ.ppJS`: `JAtZ.ppJ` with FL4's slots kept and every other word but the
  kernel-state block's and the current core's node's.
* `JAtZ.reset_loopJ`: the loop at `J`: done with the cap's free index 0, the
  region zero, `JAtZ` at the same sets and a spec outcome `Ok` of the whole
  reset; or preempted with `JAtPre` and a spec outcome `error`.
-/
import Fl4Proofs.P3.UtResetJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The region `[p, p + 2 ^ sb)` is clear of every ghost** (module
docstring), the kernel-state base `kb`. -/
structure RgClear (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb p sb : U64) : Prop where
  h : ∀ r k, H r = some k → p.val + 2 ^ sb.val ≤ r.val ∨ r.val + 2 ^ k.bits ≤ p.val
  v : ∀ x : U64, (x ∈ Z.P ∨ x ∈ Z.L4 ∨ x ∈ Z.L3 ∨ x ∈ Z.L2 ∨ x ∈ Z.L1) →
    p.val + 2 ^ sb.val ≤ x.val ∨ x.val + 4096 ≤ p.val
  b : ∀ wp ∈ Z.B, wp.1.val + 8 ≤ p.val ∨ p.val + 2 ^ sb.val ≤ wp.1.val
  ks : p.val + 2 ^ sb.val ≤ kb.val ∨ kb.val + 13568 ≤ p.val
  nd : ∀ c ∈ Cs, p.val + 2 ^ sb.val ≤ kb.val + 13568 + c.val * 4288 ∨ kb.val + 13568 + c.val * 4288 + 4288 ≤ p.val
  asid : p.val + 2 ^ sb.val ≤ kb.val + 288000 ∨ kb.val + 288000 + 16384 ≤ p.val

theorem PPR0.setCn {σ : Fl4Spec.State Unit} (h : PPR0 σ) {pb : Fl4Spec.ObjRef} {r : Nat} {cs : Fl4Spec.CnodeContents}
    (hk : σ.kheap pb = some (.cnode r cs)) (hwf : Fl4Spec.wellFormedCnodeN r cs) {idx : List Bool}
    (hidx : idx.length = r) (c : Fl4Spec.Cap) : PPR0 (setCnodeSlot σ pb r cs idx c) := by
  have hmem : ((), setCnodeSlot σ pb r cs idx c) ∈ (Fl4Spec.setCap (Z := Unit) c (pb, idx) σ).1 := by
    rw [setCap_cnode _ hk hwf hidx]; exact Set.mem_singleton _
  exact h.of_ppk (PPK.of_cnK (nkn_setCap _ _ σ _ hmem))

theorem chunk_base {p : U64} {k : Nat} (hrcb : Fl4Spec.resetChunkBits = 16)
    (hfit : p.val + k * 65536 + 65536 ≤ 2 ^ 64) :
    (p.bv + (BitVec.ofNat 64 k <<< Fl4Spec.resetChunkBits)).toNat = p.val + k * 65536 := by
  rw [hrcb, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  have h16 : (2 : Nat) ^ 16 = 65536 := by norm_num
  rw [h64, h16]
  rw [h64] at hfit
  show (p.val + k % 18446744073709551616 * 65536 % 18446744073709551616) % 18446744073709551616 = _
  omega

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **A part of a clear region cleared at `J`** (`JAtZ.zeroJR`). -/
theorem JAtZ.zeroRg (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p sb : U64}
    (hR : RgClear Z H Cs (L.ksb s) p sb) (hc0 : Z.c = 0#u64) (hpf : p.val + 2 ^ sb.val ≤ 2 ^ 64) {q n : U64}
    (hal : P1.Aligned q) (hn8 : n.val % 8 = 0) (h1 : p.val ≤ q.val) (h2 : q.val + n.val ≤ p.val + 2 ^ sb.val) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D (L.zr s q n) a σ := by
  refine J.zeroJR hal hn8 (by omega) hc0 (fun r k hr => ?_) (fun x hx => ?_) (fun wp hw => ?_) ?_ (fun c hc => ?_) ?_
  · rcases hR.h r k hr with e | e <;> omega
  · rcases hR.v x hx with e | e <;> omega
  · rcases hR.b wp hw with e | e <;> omega
  · rcases hR.ks with e | e <;> omega
  · have := hR.nd c hc
    show q.val + n.val ≤ (L.ksb s).val + 13568 + c.val * 4288 ∨ (L.ksb s).val + 13568 + c.val * 4288 + 4288 ≤ q.val
    omega
  · rcases hR.asid with e | e <;> omega


/-- A slot other than `x` keeps its cap across writes off `x`'s two words. -/
theorem capAt_frame2 {th : TypedHeap} (hP : Placed th) {m m' : U64 → U64} {x y : U64} (hx : IsSlot th x)
    (hy : IsSlot th y) (hne : y ≠ x)
    (hm : ∀ w : U64, P1.Aligned w → w.val ≠ x.val → w.val ≠ x.val + 8 → m' w = m w) : capAt m' y = capAt m y := by
  have ax := hx.align hP
  have ay := hy.align hP
  have fy := hy.fit hP
  have hne' : y.val ≠ x.val := fun e => hne (UScalar.eq_of_val_eq e)
  have h8 : (core.num.U64.wrapping_add y 8#u64).val = y.val + 8 := by
    rw [core.num.U64.wrapping_add_val_eq]; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
  unfold capAt
  rw [hm y (by unfold P1.Aligned; omega) hne' (by omega),
    hm _ (by unfold P1.Aligned; rw [h8]; omega) (by rw [h8]; omega) (by rw [h8]; omega)]

end

end

end Fl4Proofs.P3
