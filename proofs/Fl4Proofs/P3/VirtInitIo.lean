/-
P3x for virtualization (line virt, gen 13, item 3, first piece): **the FL4 program walk of `vcpu::init`, its I/O
bitmap loop** (FL4 `crates/fl4-core/src/vcpu.rs` `init` l. 653-656, `while i < 1024 { set(s, v, IO + i * 8,
u64::MAX) }`, extracted `vcpu.init_loop0`), against gen 11's image `InitImgVmx.io` (P3/VirtSanRel).

* `IoR v b n`: `b` is one of the first `n` I/O-bitmap words of the VCPU at `v` (`[v + IO, v + IO + 8n)`, by value).
* **`init_loop0_io`**: for a VCPU address `v` (`VFits`, mmuAD's P3/JExtVInit: 2^15-aligned, fitting) and any store,
  `vcpu.init_loop0 st s v 0` returns, and every aligned word of the result is `u64::MAX` on the 1024 bitmap words
  and the start's value everywhere else (the loop's exact effect; mmuAD's `vcpu.init_loop0.foot` is its footprint
  half).
* **`init_loop0_img`**: so the result satisfies `InitImgVmx.io` read through the store,
  `∀ p, (L.mem s' (v + vcpuIoOff p)).bv = ~~~0`, and leaves every word outside the bitmap as it was.

Premise: `VFits v` (a state fact the caller has: mmuAD's retype layout). No [J]/[P]/[W]/[S]. New file only.

Not here (rest of gen 11's item 2): the `WRITE_FIELDS` loop (`init_loop1`, 73 `sanitize_vmcs(f, 0)` writes; values
by `sanitize_vmcs_rel`, places distinct by `vmcsOff_inj`), the ENTRY/RFLAGS/PAT rewrites, `reset_svm`, the list
words, and the assembly into `InitImgVmx` / `InitImgSvm`.
-/
import Fl4Proofs.P3.JExtVInit
import Fl4Proofs.P3.VirtSanSvm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtInitIo
open fl4_core Fl4Spec Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- `b` is one of the first `n` I/O-bitmap words of the VCPU at `v`. -/
def IoR (v b : U64) (n : Nat) : Prop := v.val + 24576 ≤ b.val ∧ b.val < v.val + 24576 + 8 * n

/-- **`init`'s I/O-bitmap loop, exactly**: all 1024 bitmap words `u64::MAX`, every other aligned word kept. -/
theorem init_loop0_io {v : U64} (hv : VFits v) (s : S) :
    vcpu.init_loop0 st s v 0#u64 ⦃ s' => ∀ b, P1.Aligned b →
      L.mem s' b = if IoR v b 1024 then core.num.U64.MAX else L.mem s b ⦄ := by
  have hv0 : v.val % 32768 = 0 := hv.1
  have hv1 : v.val + 32768 ≤ 2 ^ 64 := hv.2
  unfold vcpu.init_loop0
  apply loop.spec_decr_nat (measure := fun x : S × U64 => 1024 - x.2.val)
    (inv := fun x => x.2.val ≤ 1024 ∧ ∀ b, P1.Aligned b →
      L.mem x.1 b = if IoR v b x.2.val then core.num.U64.MAX else L.mem s b)
  · rintro ⟨x0, x1⟩ ⟨hle, hx⟩
    dsimp only at hle hx ⊢
    unfold vcpu.init_loop0.body
    split
    · rename_i hlt
      have hlt' : x1.val < 1024 := by simpa using hlt
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      have hio : i2.val = 24576 + i1.val := by rw [hi2]; simp [vcpu.IO]
      unfold vcpu.set
      simp only [lift, bind_ok]
      refine WP.spec_bind (P1.LawfulStore.write_spec x0 _ _) fun s1 e => ?_
      subst e
      step as ⟨i3, hi3⟩
      have ha := (vw_of_off hv (o := i2) (by omega) (by omega) (by omega)).2
      have hav := vfits_wadd hv (o := i2) (by omega)
      refine ⟨by omega, fun b hb => ?_, by omega⟩
      have hb8 : b.val % 8 = 0 := hb
      rw [P1.LawfulStore.mem_wr_val ha hb, hx b hb]
      unfold IoR
      by_cases h1 : (core.num.U64.wrapping_add v i2).val = b.val
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1]
        by_cases h2 : v.val + 24576 ≤ b.val ∧ b.val < v.val + 24576 + 8 * x1.val
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
    · rename_i hge
      have hge' : ¬ x1.val < 1024 := by simpa using hge
      have e : x1.val = 1024 := by omega
      refine (WP.spec_ok _).2 fun b hb => ?_
      simp only [hx b hb, e]
  · refine ⟨by simp, fun b hb => ?_⟩
    rw [if_neg (by unfold IoR; simp)]

/-- **After `init`'s I/O-bitmap loop the image satisfies `InitImgVmx.io`** read through the store (`L.mem` at
`v + vcpuIoOff p`, the address FL4's `ports` uses), and every word outside the bitmap is the start's. -/
theorem init_loop0_img {v : U64} (hv : VFits v) (s : S) :
    vcpu.init_loop0 st s v 0#u64 ⦃ s' =>
      (∀ p : BitVec 16, (L.mem s' ⟨v.bv + vcpuIoOff p⟩).bv = ~~~0) ∧
      ∀ b, P1.Aligned b → ¬ IoR v b 1024 → L.mem s' b = L.mem s b ⦄ := by
  have hv0 : v.val % 32768 = 0 := hv.1
  have hv1 : v.val + 32768 ≤ 2 ^ 64 := hv.2
  refine WP.spec_mono (init_loop0_io (L := L) hv s) fun s' h => ⟨fun p => ?_, fun b hb hn => by rw [h b hb, if_neg hn]⟩
  have hp : p.toNat < 65536 := p.isLt
  have hval : (⟨v.bv + vcpuIoOff p⟩ : U64).val = v.val + 24576 + 8 * (p.toNat / 64) := by
    show (v.bv + vcpuIoOff p).toNat = _
    unfold vcpuIoOff VcpuLay.IO
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    have h1 : (24576 : Word).toNat = 24576 := rfl
    have h8 : (8 : Word).toNat = 8 := rfl
    have hvb : v.bv.toNat = v.val := rfl
    rw [h1, h8, hvb]
    have hq : p.toNat / 64 < 1024 := by omega
    rw [Nat.mod_eq_of_lt (a := p.toNat / 64) (by omega), Nat.mod_eq_of_lt (a := p.toNat / 64 * 8) (by omega),
      Nat.mod_eq_of_lt (a := 24576 + p.toNat / 64 * 8) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hal : P1.Aligned (⟨v.bv + vcpuIoOff p⟩ : U64) := by
    unfold P1.Aligned; rw [hval]; omega
  rw [h _ hal, if_pos (by unfold IoR; rw [hval]; omega)]
  exact VirtSanEq.MAX_bv

end

end

end Fl4Proofs.P3.VirtInitIo
