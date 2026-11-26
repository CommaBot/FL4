/-
# P2 (line pte, generation 16): the PageMap decode's errors write register MRs only (`roA`, first part)

* `PmNoLk e`: `e` is not a `FailedLookup` (the only `SysError` whose MRs reach the IPC buffer);
* **`dpm_run2`**: gen 15's `dpm_run` (P2/InvPmBlkB.lean, its script with the error leaf extended) with the error arm's
  `SysError` a `PmNoLk` one (`DpmOut2`, `dpmOut_of2`): at the accepted run's state `check_vspace` and the walk
  answer `Ok`, so every error is a pure check's (truncated, invalid cap / argument, alignment, illegal);
* **`syscall.error_mrs.guardN`**: for a `PmNoLk` error, `error_mrs` on a guarded store is `st`'s given only the
  receiver's registers (`set_mr` below `N_MSG_REGISTERS`), no buffer word.

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmBlkB
import Fl4Proofs.P2.InvCMG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl

noncomputable section

/-- A `SysError` that is not a lookup failure. -/
def PmNoLk (e : error.SysError) : Prop := ∀ b lf, e ≠ .FailedLookup b lf

section run2
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

variable (st) in
/-- `DpmOut` with the error arm's `SysError` not a lookup failure. -/
def DpmOut2 (x : S) (a : A) (t slot e : U64) (y : (core.result.Result Unit error.Exc) × S × A) : Prop :=
  (y.2.1 = x ∧ y.2.2 = a ∧ ∃ se, y.1 = .Err (.Sys se) ∧ PmNoLk se) ∨
  (y.1 = .Ok () ∧ ∃ s1 s2 c pte as' va' d, sched.set_thread_state st x t sched.TS_RESTART = ok s1 ∧
    obj.Slot.set_cap st slot s1 c = ok s2 ∧ vspace.write_mapping st ar s2 a e pte as' va' d = ok (y.2.1, y.2.2))

set_option hygiene false in
/-- An error leaf of the decode. -/
local macro "pmleaf" : tactic => `(tactic| (
  try simp only [error.illegal, error.truncated, error.invalid_cap, error.invalid_arg, bind_ok]
  exact (WP.spec_ok _).2 (Or.inl ⟨rfl, rfl, _, rfl, fun _ _ h => by cases h⟩)))

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

/-- **`dpm_run` with the errors named**: no error arm is a lookup failure (module docstring). -/
theorem dpm_run2 (hA : P0.ArchTotal ar) {x : S} {a : A} {length buf : U64} {slot : obj.Slot}
    {ex : Array obj.Slot 3#usize} {fp rt asid va : U64} {mp : Bool} {t x0 root rasid v0 v1 v2 e : U64}
    (hc : sched.cur_thread st x = ok t) (hx0 : vspace.extra ex 0#usize = ok (some x0))
    (ha0 : msg.syscall_arg st x t buf 0#u64 = ok v0) (ha1 : msg.syscall_arg st x t buf 1#u64 = ok v1)
    (ha2 : msg.syscall_arg st x t buf 2#u64 = ok v2)
    (hk : obj.Slot.cap st x0 x = ok (.Pml4 root true rasid))
    (hcv : vspace.check_vspace st x (.Pml4 root true rasid) = ok (.Ok (root, rasid)))
    (hp : vspace.page_entry_slot st x root v0 .Small = ok (.Ok e)) :
    vspace.decode_page_map st ar x a length slot
        { ptr := fp, size := .Small, rights := rt, is_device := false, mapped := mp, is_ept := false, asid,
          vaddr := va } buf ex ⦃ y => DpmOut2 st ar x a t slot e y ⦄ := by
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

end run2

section run3
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {ar : machine.Arch A}

theorem dpmOut_of2 {x : S} {a : A} {t slot e : U64} {y : (core.result.Result Unit error.Exc) × S × A}
    (h : DpmOut2 st ar x a t slot e y) : DpmOut st ar x a t slot e y := by
  rcases h with ⟨h1, h2, se, h3, -⟩ | h
  · exact Or.inl ⟨h1, h2, se, h3⟩
  · exact Or.inr h

end run3

section g
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

/-- **`error_mrs` of a `PmNoLk` error on the guarded store** (module docstring). -/
theorem syscall.error_mrs.guardN (s : S) (t buf : U64) (e : error.SysError) (he : PmNoLk e)
    (hrw : Regs W t) :
    syscall.error_mrs gS s t buf e = syscall.error_mrs st s t buf e := by
  have em : ∀ x (i v : U64), i < msg.N_MSG_REGISTERS → msg.set_mr gS x t buf i v = msg.set_mr st x t buf i v :=
    fun x i v hi => msg.set_mr.guard_reg x t buf i v hi
      (fun r hr => hrw r (post_of_ok (msg.msg_register.lt _) hr))
  have h0 : (0#u64 : U64) < msg.N_MSG_REGISTERS := by simp [msg.N_MSG_REGISTERS]
  have h1 : (1#u64 : U64) < msg.N_MSG_REGISTERS := by simp [msg.N_MSG_REGISTERS]
  unfold syscall.error_mrs
  cases e with
  | FailedLookup b lf => exact absurd rfl (he b lf)
  | _ => first | rfl | simp only [em _ 0#u64 _ h0, em _ 1#u64 _ h1]

end g

end
end Fl4Proofs.P2.E2EP
