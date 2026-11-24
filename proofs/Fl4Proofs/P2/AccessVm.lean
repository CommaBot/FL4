/-
# P2: guarded-store lemma for `vspace.set_vm_root`

`vspace.set_vm_root.guard`: `set_vm_root t` on `guard st R W` is the run on
`st` when `R` holds the words it may read (`RdVm`): the thread's VTABLE
slot's two words, the kernel root, and, for the ASID table and pool words
`find_asid` can read, the table word `hi < 2048` and (when it is a pool) the
pool word `lo < 512` (P1 `FastFin`'s `VmOff` / `TabOff` sets). It writes no
word. Generic over the Arch instance (no Arch premise).

No premises.
-/
import Fl4Proofs.P2.AccessSched
import Fl4Proofs.P1.FastFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]

/-- The ASID table and pool words `find_asid` may read. -/
def RdTab (R : U64 → Prop) (s : S) : Prop :=
  ∀ hi : U64, hi.val < 2048 → R (atAF (L.ksb s) hi) ∧
    ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
      R (peAF (L.mem s (atAF (L.ksb s) hi)) lo)

/-- The words `set_vm_root t` may read. -/
def RdVm (R : U64 → Prop) (s : S) (t : U64) : Prop :=
  R (vtA t) ∧ R (core.num.U64.wrapping_add (vtA t) 8#u64) ∧ R (krA (L := L) s) ∧ RdTab (L := L) R s

theorem vspace.asid_table.guard (s : S) (hi : U64) (h : R (atAF (L.ksb s) (hi &&& 2047#u64))) :
    vspace.asid_table (guard st R W) s hi = vspace.asid_table st s hi := by
  have hN : vspace.N_ASID_POOLS = 2048#u64 := by unfold vspace.N_ASID_POOLS; rfl
  unfold vspace.asid_table
  rw [hN]
  refine bind_guard_congr rfl fun i hi1 => ?_
  simp only [lift, bind_ok]
  rw [eq_ok_of_spec asid_table_base_fs]
  simp only [bind_ok]
  apply obj.ks_get.guard
  have e : i = 2047#u64 := by
    obtain ⟨z, hz, hv⟩ := spec_ex_fd (U64.sub_spec (x := 2048#u64) (y := 1#u64) (by scalar_tac))
    rw [hz] at hi1
    have := ok_inj_ff hi1; subst this
    apply UScalar.eq_of_val_eq; rw [hv.1]; simp
  subst e
  exact h

theorem vspace.find_asid.guard (s : S) (asid : U64) (h : RdTab (L := L) R s) :
    vspace.find_asid (guard st R W) s asid = vspace.find_asid st s asid := by
  unfold vspace.find_asid
  refine bind_guard_congr rfl fun i _ => ?_
  obtain ⟨h1, h2⟩ := h (i &&& 2047#u64) (and2047_lt i)
  rw [vspace.asid_table.guard s i h1, asid_table_eq]
  simp only [bind_ok]
  by_cases hp : L.mem s (atAF (L.ksb s) (i &&& 2047#u64)) = 0#u64
  · simp only [hp, ↓reduceIte]
  · simp only [hp, ↓reduceIte, lift, bind_ok]
    have h3 := h2 (asid &&& 511#u64) (and511_lt asid) hp
    unfold peAF at h3
    rw [guard_read h3]

theorem vspace.find_vspace_for_asid.guard (s : S) (asid : U64) (h : RdTab (L := L) R s) :
    vspace.find_vspace_for_asid (guard st R W) s asid = vspace.find_vspace_for_asid st s asid := by
  unfold vspace.find_vspace_for_asid
  rw [vspace.find_asid.guard s asid h]

/-- **`set_vm_root t`** reads only `RdVm` and writes nothing. -/
theorem vspace.set_vm_root.guard {A : Type} (ar : machine.Arch A) (s : S) (a : A) (t : U64)
    (h : RdVm (L := L) R s t) :
    vspace.set_vm_root (guard st R W) ar s a t = vspace.set_vm_root st ar s a t := by
  obtain ⟨h0, h8, hk, ht⟩ := h
  have K : vspace.set_kernel_vm_root (PathObl.guard st R W) ar s a = vspace.set_kernel_vm_root st ar s a :=
    vspace.set_kernel_vm_root.guard ar s a hk
  unfold vspace.set_vm_root
  rw [slot_vt]
  simp only [bind_ok]
  rw [obj.Slot.cap.guard _ s h0 h8]
  refine bind_guard_congr rfl fun c hc => ?_
  cases c
  all_goals try exact K
  rename_i ptr b asid
  cases b
  · simp only [Bool.false_eq_true, ite_false]; exact K
  · simp only [ite_true]
    rw [vspace.find_vspace_for_asid.guard s asid ht]
    refine bind_guard_congr rfl fun r _ => ?_
    rcases r with r1 | e
    · by_cases e1 : r1 = ptr
      · simp only [e1, ite_true]
      · simp only [e1, ite_false]; exact K
    · exact K

end

end Fl4Proofs.P2.PathObl
