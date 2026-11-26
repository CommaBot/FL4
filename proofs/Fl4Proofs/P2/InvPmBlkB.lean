/-
# P2 (line pte, generation 15): the outcomes of the PageMap decode on `st` (`blk`, second part)

At the decode state `x`, for a small, non-EPT frame cap whose `extra[0]` is a mapped PML4 cap that `check_vspace`
accepts and whose small-page walk answers the leaf `e`, `decode_page_map` on `st` either

* returns a `Sys` error with the state and the Arch state unchanged (every error arm: truncated, invalid cap or
  argument, alignment, illegal), or
* returns `Ok ()` after `set_thread_state RESTART` of the caller, one `set_cap` of the invoked slot and one
  `write_mapping` of `e` (**`dpm_run`**, a WP walk as P1/QueueDecVs's `decode_page_map.dec`).

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmBlkA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl

noncomputable section

/-- A total computation's result is the one it returns. -/
theorem spec_selfPm {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) : m ⦃ v => m = ok v ⦄ := by
  obtain ⟨v, hv, -⟩ := spec_ex_fd h
  rw [hv]
  exact (WP.spec_ok _).2 rfl

section run
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

variable (st) in
/-- The outcomes of the PageMap decode (module docstring). -/
def DpmOut (x : S) (a : A) (t slot e : U64) (y : (core.result.Result Unit error.Exc) × S × A) : Prop :=
  (y.2.1 = x ∧ y.2.2 = a ∧ ∃ se, y.1 = .Err (.Sys se)) ∨
  (y.1 = .Ok () ∧ ∃ s1 s2 c pte as' va' d, sched.set_thread_state st x t sched.TS_RESTART = ok s1 ∧
    obj.Slot.set_cap st slot s1 c = ok s2 ∧ vspace.write_mapping st ar s2 a e pte as' va' d = ok (y.2.1, y.2.2))

set_option hygiene false in
/-- An error leaf of the decode. -/
local macro "pmleaf" : tactic => `(tactic| (
  try simp only [error.illegal, error.truncated, error.invalid_cap, error.invalid_arg, bind_ok]
  exact (WP.spec_ok _).2 (Or.inl ⟨rfl, rfl, _, rfl⟩)))

set_option hygiene false in
/-- The decode's tail after the alignment check: the frame address, the entry, the restart, the cap's update and
the entry's write. -/
local macro "pmrest" : tactic => `(tactic| (
  split
  · pmleaf
  try simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_bind (P0.vspace.frame_address.p0 st ar x a _ hS hA) fun _ _ => ?_
  refine WP.spec_bind (P0.vspace.make_user_page.p0 st x _ _ _ _ hS) fun _ _ => ?_
  refine WP.spec_bind (spec_selfPm (P0.sched.set_thread_state.p0 st x t _ hS)) fun _ h1 => ?_
  refine WP.spec_bind (spec_selfPm (P0.obj.Slot.set_cap.p0 st slot _ _ hS)) fun _ h2 => ?_
  refine WP.spec_bind (spec_selfPm (P0.vspace.write_mapping.p0 st ar _ a e _ _ _ _ hS hA)) ?_
  rintro ⟨s3, a3⟩ h3
  exact (WP.spec_ok _).2 (Or.inr ⟨rfl, _, _, _, _, _, _, _, h1, h2, h3⟩)))

set_option hygiene false in
/-- The rights, the size and the alignment mask, then `pmrest`. -/
local macro "pmtail" : tactic => `(tactic| (
  refine WP.spec_bind (P0.capability.Rights.from_word.p0 _) fun _ _ => ?_
  refine WP.spec_bind (P0.capability.mask_vm_rights.p0 _ _) fun _ _ => ?_
  try refine WP.spec_bind (P0.capability.FrameSize.bits.p0 _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (Fl4Proofs.P1.shl_and63 _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  pmrest))

set_option hygiene false in
/-- The unmapped (or ASID-0) arm: the size, the two range checks, then `pmtail`. -/
local macro "pmtop" : tactic => `(tactic| (
  refine WP.spec_bind (P0.capability.FrameSize.bits.p0 _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (Fl4Proofs.P1.shl_and63 _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  split
  · pmleaf
  split
  · pmleaf
  try simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  pmtail))

/-- **The outcomes of the PageMap decode on `st`** (module docstring). -/
theorem dpm_run (hA : P0.ArchTotal ar) {x : S} {a : A} {length buf : U64} {slot : obj.Slot}
    {ex : Array obj.Slot 3#usize} {fp rt asid va : U64} {mp : Bool} {t x0 root rasid v0 v1 v2 e : U64}
    (hc : sched.cur_thread st x = ok t) (hx0 : vspace.extra ex 0#usize = ok (some x0))
    (ha0 : msg.syscall_arg st x t buf 0#u64 = ok v0) (ha1 : msg.syscall_arg st x t buf 1#u64 = ok v1)
    (ha2 : msg.syscall_arg st x t buf 2#u64 = ok v2)
    (hk : obj.Slot.cap st x0 x = ok (.Pml4 root true rasid))
    (hcv : vspace.check_vspace st x (.Pml4 root true rasid) = ok (.Ok (root, rasid)))
    (hp : vspace.page_entry_slot st x root v0 .Small = ok (.Ok e)) :
    vspace.decode_page_map st ar x a length slot
        { ptr := fp, size := .Small, rights := rt, is_device := false, mapped := mp, is_ept := false, asid,
          vaddr := va } buf ex ⦃ y => DpmOut st ar x a t slot e y ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.decode_page_map
  by_cases hl3 : length ≥ 3#u64
  swap
  · simp only [hc, hx0, bind_ok, if_neg hl3]
    pmleaf
  cases mp
  · simp only [hc, hx0, ha0, ha1, ha2, hk, hcv, hp, bind_ok, vspace.mapped_root, uncurry_apply_pair,
      Bool.false_eq_true, ↓reduceIte, lift, core.result.Result.Insts.CoreOpsTry.branch, if_pos hl3]
    pmtop
  · simp only [hc, hx0, ha0, ha1, ha2, hk, hcv, hp, bind_ok, vspace.mapped_root, uncurry_apply_pair,
      Bool.false_eq_true, ↓reduceIte, lift, core.result.Result.Insts.CoreOpsTry.branch, if_pos hl3]
    split
    · split
      · pmleaf
      split
      · pmleaf
      pmtail
    · pmtop

end run

end
end Fl4Proofs.P2.E2EP
