/-
# P2 (line mmuAD, gen 12): **the PageMap decode is `InsTP` along its run** (`insTP_decPm`)

The decode block of an accepted PageMap run (`R.decPmG` → `R.vspace.decode_page_map`, x86_64 `vspace.rs` l. 551) for
the plan's small, non-EPT frame cap, walked in `InsTP G ADEq NotPresent User` from the empty done set to the done
set `{b | G b}`, for any word set `G` off the words the block reads and writes outside its walk:

* every call but the walk is run alike on `guard st (¬ G) (¬ G)` (`insTP_gstep`): the current thread, the three
  message arguments (registers), `extra[0]`'s cap, `check_vspace` (given as `hcv`), the frame masks, the `FEATURES`
  word, the caller's `set_thread_state` (given as `hsts`) and the invoked slot's `set_cap`;
* the small-page `page_entry_slot` is insensitive on every branch (`sIns_pesSmall`: `lookup_pt_slot` and the `blk 1`
  `true`), so `InsT` (`insT_of_sIns`) and `InsTP` from `∅` (`insTP_of_insT`);
* `write_mapping` (vspace.rs l. 444) is `insTP_write_mapping` from `∅`: its leaf store joins the done set.

No premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.MmuADPmT
import Fl4Proofs.P2.InvPmBlkC
import Fl4Proofs.P2.InvPmDecG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.E2E (InsT InsTP insTP_sbind insTP_of_insT)
open Fl4Proofs.P2.MmuAD (ADEq NotPresent)
open Fl4Proofs.P2.Serial (dU)

noncomputable section

section tools
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} {G : U64 → Prop} {Q : U64 → U64 → Prop}
  {NP User : U64 → Prop} {E : Set U64}

/-- A pure step alone. -/
theorem insTP_liftR {X : Type} {D : Set U64} {r : Result X} {s : S} {a : A} (h : D ⊆ E) :
    InsTP st ar G Q NP User E D (SProg.liftR r) s a := by
  unfold SProg.liftR
  by_cases h1 : ∃ v, r = ok v
  · rw [dif_pos h1]; simp only [InsTP]; exact h
  · rw [dif_neg h1]
    by_cases h2 : ∃ e, r = fail e
    · rw [dif_pos h2]; simp only [InsTP]
    · rw [dif_neg h2]; simp only [InsTP]

/-- Sequencing with the run hypothesis. -/
theorem insTP_sbindR {X Y : Type} {D E' : Set U64} {p : SProg X} {k : X → SProg Y} {s : S} {a : A}
    {r' : Y × S × A} (h : interp st ar (p.sbind k) s a = ok r') (hp : InsTP st ar G Q NP User E' D p s a)
    (hk : ∀ r, interp st ar p s a = ok r → interp st ar (k r.1) r.2.1 r.2.2 = ok r' →
      InsTP st ar G Q NP User E E' (k r.1) r.2.1 r.2.2) :
    InsTP st ar G Q NP User E D (p.sbind k) s a := by
  rw [interp_sbind] at h
  obtain ⟨r0, h0, hk0⟩ := bind_eq_ok' h
  refine insTP_sbind p k D s a hp fun r hr => ?_
  rw [h0] at hr
  cases ok_inj_ff hr
  exact hk r0 h0 hk0

theorem dU_sub_G {D : Set U64} (hD : ∀ x ∈ D, G x) (q v : U64) : dU G NP D q v ⊆ {b | G b} := by
  rintro z (hz | ⟨rfl, hg, -⟩)
  · exact hD z hz
  · exact hg

end tools

/-- **The small-page `page_entry_slot` is insensitive on every branch.** -/
theorem sIns_pesSmall (root va : U64) : SInsQ ADEq (R.vspace.page_entry_slot root va .Small) := by
  unfold R.vspace.page_entry_slot
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.blk, SProg.sbind]
  refine sIns_sbind (sIns_lookup_pt_slot root va) fun r => ?_
  rcases r with x | lf
  · simp only [SProg.sbind, ↓reduceIte]; exact .ret _
  · exact sIns_liftR

set_option hygiene false in
/-- An error leaf. -/
local macro "pmleafP" : tactic => `(tactic| first
  | (simp only [InsTP, Set.empty_subset]; done)
  | exact insTP_ret (Set.empty_subset _)
  | exact insTP_liftR (Set.empty_subset _)
  | exact insTP_liftR_sbind fun _ => insTP_ret (Set.empty_subset _)
  | exact insTP_liftR_sbind fun _ => insTP_liftR (Set.empty_subset _))


set_option hygiene false in
/-- The unmapped (or ASID-0) arm up to `check_vspace`: the size, the two range checks. -/
local macro "pmtop" : tactic => `(tactic| (
  repeat' (refine insTP_liftRR h (fun _ _ h => ?_))
  refine insTP_iteR h (fun _ _ => by pmleafP) (fun _ h => ?_)
  refine insTP_iteR h (fun _ _ => by pmleafP) (fun _ h => ?_)))

set_option hygiene false in
/-- From `check_vspace` on: the rights, the alignment, the walk, the entry, the restart, the cap, the leaf. -/
local macro "pmcheck" : tactic => `(tactic| (
  refine insTP_gstep hGU hD hR0 hR0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.vspace.check_vspace_eq] at h1 ⊢; rw [hcv]; exact h1
  replace h := hk
  rw [R.vspace.check_vspace_eq] at h1
  obtain ⟨cr, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insTP_liftRR h (fun cf _ h => ?_)
  cases cf with
  | Break res => pmleafP
  | Continue u =>
    dsimp only at h ⊢
    try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
    repeat' (refine insTP_liftRR h (fun _ _ h => ?_))
    refine insTP_iteR h (fun _ _ => by pmleafP) (fun _ h => ?_)
    try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
    refine insTP_sbindR h (insTP_of_insT hGU _ ∅ x a (insT_of_sIns (sIns_pesSmall _ _) x a)) (fun r hr h => ?_)
    rw [R.vspace.page_entry_slot_eq] at hr
    obtain ⟨pv, -, rfl⟩ := bind_shape hr
    dsimp only at h ⊢
    refine insTP_liftRR h (fun cf1 _ h => ?_)
    cases cf1 with
    | Break res1 => pmleafP
    | Continue val =>
      dsimp only at h ⊢
      try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
      refine insTP_gstep hGU hD hR0 hR0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
      · rw [R.vspace.frame_address_eq] at h1 ⊢
        rw [vspace.frame_address.guardK (gS := guard st (fun b => ¬ G b) (fun b => ¬ G b)) ar x a]
        exact h1
      replace h := hk
      rw [R.vspace.frame_address_eq] at h1
      obtain ⟨i7, -, rfl⟩ := bind_shape h1
      dsimp only at h ⊢
      refine insTP_gstep hGU hD hR0 hR0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
      · rw [R.vspace.make_user_page_eq] at h1 ⊢
        rw [vspace.make_user_page.guardF (gS := guard st (fun b => ¬ G b) (fun b => ¬ G b)) x hFt]
        exact h1
      replace h := hk
      rw [R.vspace.make_user_page_eq] at h1
      obtain ⟨e7, -, rfl⟩ := bind_shape h1
      dsimp only at h ⊢
      refine insTP_gstep hGU hD hR0 hR0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
      · rw [R.sched.set_thread_state_eq] at h1 ⊢
        rw [hsts]
        exact h1
      replace h := hk
      rw [R.sched.set_thread_state_eq] at h1
      obtain ⟨x1, -, rfl⟩ := bind_shape h1
      dsimp only at h ⊢
      refine insTP_gstep hGU hD hR0 hR0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
      · rw [R.obj.Slot.set_cap_eq] at h1 ⊢
        rw [obj.Slot.set_cap.guard (gS := guard st (fun b => ¬ G b) (fun b => ¬ G b)) slot x1 _ hs0 hs8]
        exact h1
      replace h := hk
      rw [R.obj.Slot.set_cap_eq] at h1
      obtain ⟨x2, -, rfl⟩ := bind_shape h1
      dsimp only at h ⊢
      exact insTP_sbind _ _ ∅ _ _ (insTP_write_mapping _ _ _ _ _ (fun _ => Set.notMem_empty _)
        (dU_sub_G hD _ _) _ _) (fun _ _ => insTP_ret subset_rfl)))

section walk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 8000000 in
/-- **`decode_page_map` of the plan's small frame cap is `InsTP` from `∅` to `{b | G b}`** (module docstring). -/
theorem insTP_dpm {G User : U64 → Prop} (hGU : ∀ x, G x → ¬ User x)
    {x : S} {a : A} {length buf : U64} {slot : obj.Slot} {ex : Array obj.Slot 3#usize}
    {fp rt asid va : U64} {mp : Bool} {x0 root rasid : U64} {r' : (core.result.Result Unit error.Exc) × S × A}
    (hct : ¬ G (L.nodeAt x (L.cpu x) layout.node.CUR_THREAD))
    (hx0 : vspace.extra ex 0#usize = ok (some x0))
    (hreg : ∀ r : U64, r.val < 384 → ¬ G (regA (L.curW x) r))
    (hk0 : ¬ G x0) (hk8 : ¬ G (core.num.U64.wrapping_add x0 8#u64))
    (hcx : obj.Slot.cap st x0 x = ok (.Pml4 root true rasid))
    (hcv : vspace.check_vspace (guard st (fun b => ¬ G b) (fun b => ¬ G b)) x (.Pml4 root true rasid) =
      vspace.check_vspace st x (.Pml4 root true rasid))
    (hFt : ¬ G (core.num.U64.wrapping_add (L.ksb x) layout.ks.FEATURES))
    (hsts : sched.set_thread_state (guard st (fun b => ¬ G b) (fun b => ¬ G b)) x (L.curW x) sched.TS_RESTART =
      sched.set_thread_state st x (L.curW x) sched.TS_RESTART)
    (hs0 : ¬ G slot) (hs8 : ¬ G (core.num.U64.wrapping_add slot 8#u64))
    (h : interp st ar (R.vspace.decode_page_map length slot
        { ptr := fp, size := .Small, rights := rt, is_device := false, mapped := mp, is_ept := false, asid,
          vaddr := va } buf ex) x a = ok r') :
    InsTP st ar G ADEq NotPresent User {b | G b} ∅ (R.vspace.decode_page_map length slot
        { ptr := fp, size := .Small, rights := rt, is_device := false, mapped := mp, is_ept := false, asid,
          vaddr := va } buf ex) x a := by
  have hR0 : ∀ q, (fun b => ¬ G b) q → ¬ G q := fun q h => h
  have hD : ∀ y ∈ (∅ : Set U64), G y := fun y hy => absurd hy (Set.notMem_empty y)
  unfold R.vspace.decode_page_map at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.blk,
    Bool.false_eq_true, ↓reduceIte] at h ⊢
  -- the current thread
  refine insTP_gstep hGU hD hR0 hR0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := guard st (fun b => ¬ G b) (fun b => ¬ G b)) x hct]
    exact h1
  replace h := hk
  rw [R.sched.cur_thread_eq, cur_thread_ok] at h1
  obtain ⟨t, et, rfl⟩ := bind_shape h1
  cases ok_inj_ff et
  dsimp only at h ⊢
  -- `extra[0]`
  refine insTP_liftRR h (fun o eo h => ?_)
  rw [hx0] at eo
  cases ok_inj_ff eo
  dsimp only at h ⊢
  refine insTP_iteR h (fun _ h => ?_) (fun _ _ => by pmleafP)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the three message arguments
  have hNr : (0#u64 : U64) < msg.N_MSG_REGISTERS ∧ (1#u64 : U64) < msg.N_MSG_REGISTERS ∧
      (2#u64 : U64) < msg.N_MSG_REGISTERS := by simp [msg.N_MSG_REGISTERS]
  refine insTP_gstep hGU hD hR0 hR0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.msg.syscall_arg_eq] at h1 ⊢
    rw [msg.syscall_arg.guard_lt (gS := guard st (fun b => ¬ G b) (fun b => ¬ G b)) x (L.curW x) buf 0#u64
      hNr.1 (fun r hr => hreg r (msgReg_lt hr))]
    exact h1
  replace h := hk
  rw [R.msg.syscall_arg_eq] at h1
  obtain ⟨v0, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insTP_gstep hGU hD hR0 hR0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.msg.syscall_arg_eq] at h1 ⊢
    rw [msg.syscall_arg.guard_lt (gS := guard st (fun b => ¬ G b) (fun b => ¬ G b)) x (L.curW x) buf 1#u64
      hNr.2.1 (fun r hr => hreg r (msgReg_lt hr))]
    exact h1
  replace h := hk
  rw [R.msg.syscall_arg_eq] at h1
  obtain ⟨v1, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insTP_gstep hGU hD hR0 hR0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.msg.syscall_arg_eq] at h1 ⊢
    rw [msg.syscall_arg.guard_lt (gS := guard st (fun b => ¬ G b) (fun b => ¬ G b)) x (L.curW x) buf 2#u64
      hNr.2.2 (fun r hr => hreg r (msgReg_lt hr))]
    exact h1
  replace h := hk
  rw [R.msg.syscall_arg_eq] at h1
  obtain ⟨v2, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `extra[0]`'s cap
  refine insTP_gstep hGU hD hR0 hR0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.obj.Slot.cap_eq] at h1 ⊢
    rw [obj.Slot.cap.guard (gS := guard st (fun b => ¬ G b) (fun b => ¬ G b)) x0 x hk0 hk8]
    exact h1
  replace h := hk
  rw [R.obj.Slot.cap_eq, hcx] at h1
  obtain ⟨vc, evc, rfl⟩ := bind_shape h1
  cases ok_inj_ff evc
  dsimp only at h ⊢
  -- `mapped_root`
  refine insTP_liftRR h (fun o1 _ h => ?_)
  rcases o1 with _ | r0
  · pmleafP
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the three arms, up to `check_vspace`
  refine insTP_iteR h (fun _ h => ?_) (fun _ h => ?_)
  · refine insTP_iteR h (fun _ h => ?_) (fun _ h => ?_)
    · refine insTP_iteR h (fun _ _ => by pmleafP) (fun _ h => ?_)
      refine insTP_iteR h (fun _ _ => by pmleafP) (fun _ h => ?_)
      pmcheck
    · pmtop
      pmcheck
  · pmtop
    pmcheck

set_option maxHeartbeats 4000000 in
/-- **The PageMap decode block of the plan's small frame cap is `InsTP` from `∅` to `{b | G b}`** (`insTP_dpm`
after the two current-thread reads of `R.decPmG`). -/
theorem insTP_decPm {G User : U64 → Prop} (hGU : ∀ x, G x → ¬ User x)
    {x : S} {a : A} {lbl length buf : U64} {slot : obj.Slot} {ex : Array obj.Slot 3#usize}
    {fp rt asid va : U64} {mp : Bool} {x0 root rasid : U64} {r' : (core.result.Result Unit error.Exc) × S × A}
    (hlbl : lbl = fl4_abi.label.X86PageMap)
    (hct : ¬ G (L.nodeAt x (L.cpu x) layout.node.CUR_THREAD))
    (hx0 : vspace.extra ex 0#usize = ok (some x0))
    (hreg : ∀ r : U64, r.val < 384 → ¬ G (regA (L.curW x) r))
    (hk0 : ¬ G x0) (hk8 : ¬ G (core.num.U64.wrapping_add x0 8#u64))
    (hcx : obj.Slot.cap st x0 x = ok (.Pml4 root true rasid))
    (hcv : vspace.check_vspace (guard st (fun b => ¬ G b) (fun b => ¬ G b)) x (.Pml4 root true rasid) =
      vspace.check_vspace st x (.Pml4 root true rasid))
    (hFt : ¬ G (core.num.U64.wrapping_add (L.ksb x) layout.ks.FEATURES))
    (hsts : sched.set_thread_state (guard st (fun b => ¬ G b) (fun b => ¬ G b)) x (L.curW x) sched.TS_RESTART =
      sched.set_thread_state st x (L.curW x) sched.TS_RESTART)
    (hs0 : ¬ G slot) (hs8 : ¬ G (core.num.U64.wrapping_add slot 8#u64))
    (h : interp st ar (R.decPmG lbl length slot (.Frame fp .Small rt false mp false asid va) true true true false
      buf ex) x a = ok r') :
    InsTP st ar G ADEq NotPresent User {b | G b} ∅
      (R.decPmG lbl length slot (.Frame fp .Small rt false mp false asid va) true true true false buf ex) x a := by
  have hR0 : ∀ q, (fun b => ¬ G b) q → ¬ G q := fun q h => h
  have hD : ∀ y ∈ (∅ : Set U64), G y := fun y hy => absurd hy (Set.notMem_empty y)
  subst hlbl
  unfold R.decPmG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, ↓reduceIte,
    Bool.false_eq_true, ite_self] at h ⊢
  refine insTP_gstep hGU hD hR0 hR0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := guard st (fun b => ¬ G b) (fun b => ¬ G b)) x hct]
    exact h1
  replace h := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insTP_gstep hGU hD hR0 hR0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := guard st (fun b => ¬ G b) (fun b => ¬ G b)) x hct]
    exact h1
  replace h := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t', -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  exact insTP_dpm hGU hct hx0 hreg hk0 hk8 hcx hcv hFt hsts hs0 hs8 h

end walk

end
end Fl4Proofs.P2.E2EP
