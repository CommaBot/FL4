/-
# P2 (line mmuAD, gen 7): **`InsT` of the CNodeDelete decode block of a frame cap, tree by tree**

The decode onward of an accepted CNodeDelete (`invCMRest`, length ≥ 2, the target holding a small RAM frame cap)
walked for `E2EADQ.InsT`, one generated tree per lemma, each from the run of that tree and guard facts about the
calls it makes on `guard st R0 W0` (`R0`, `W0` off `G`):

* **`insT_finCap`**: `R.objects.finalise_cap` of the frame cap: no access unless the cap is mapped with a non-zero
  ASID; then `unmap_page` (`MmuADStep.insT_unmap_page`: `find_vspace_for_asid` on a store guarded to `R0`, the
  walk and the leaf insensitive, the store `0`);
* **`insT_finImm`**: `R.cdt.finalise_slot_immediate` (one loop round: the slot's cap, `is_null`, the finality
  check, `finalise_cap`, `cap_removable` of `Null`);
* **`insT_cdtDel`**: `R.cdt.delete dest true` (finalisation, then `empty_slot … Null`);
* **`insT_decCNG`**: `R.decCNG` of a CNodeDelete on a CNode cap with length ≥ 2 (current thread, the label and
  length checks, two `syscall_arg`s, `lookup_target_slot`, `set_thread_state RESTART`, `cdt.delete`);
* **`insT_restDel`**: `invCMRest` (the decode, then the `Ok` reply `invPostG`, `after_invocation`, `finish`).

No premise: every guard fact is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.MmuADEnt
import Fl4Proofs.P2.InvDelPteAccX
import Fl4Proofs.P2.InvDelNoPteR
import Fl4Proofs.P2.InvCMDecOnce
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.MmuAD (ADEq NotPresent)
open Fl4Proofs.P2.E2E (InsT insT_sbind)

section trees
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {ar : machine.Arch A}
  {G User : U64 → Prop}

/-- **`finalise_cap` of a small RAM frame cap** (module docstring). -/
theorem insT_finCap {R0 : U64 → Prop} (hR0 : ∀ q, R0 q → ¬ G q) {x : S} {a : A} {fp rt asid va : U64}
    {mp fin : Bool} {y : (capability.Cap × capability.Cap) × S × A}
    (hfv : mp = true → asid ≠ 0#u64 → ∀ r, vspace.find_vspace_for_asid st x asid = ok r →
      vspace.find_vspace_for_asid (guard st R0 (fun _ => False)) x asid = ok r)
    (h : interp st ar (R.objects.finalise_cap (.Frame fp .Small rt false mp false asid va) fin false) x a = ok y) :
    InsT st ar G ADEq NotPresent User
      (R.objects.finalise_cap (.Frame fp .Small rt false mp false asid va) fin false) x a := by
  unfold R.objects.finalise_cap R.objects.finalise_cap_object at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.blk, SProg.sbind_assoc, SProg.sbind] at h ⊢
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte, SProg.sbind] at h ⊢
    cases fin <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> trivial
  · by_cases hA : asid = 0#u64
    · have hA' : (asid != 0#u64) = false := by simp [hA]
      simp only [hA', Bool.false_eq_true, ↓reduceIte, SProg.sbind] at h ⊢
      cases fin <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> trivial
    · have hA' : (asid != 0#u64) = true := by simpa using hA
      simp only [hA', Bool.false_eq_true, ↓reduceIte, SProg.sbind] at h ⊢
      exact insT_unmap_page hR0 _ _ _ _ h (hfv rfl hA) (fun r _ _ => by
        cases fin <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> trivial)

/-- `finalise_cap` of such a cap returns `(Null, Null)`. -/
theorem finCap_frame_nullAD {x : S} {a : A} {fp rt asid va : U64} {mp fin : Bool}
    {y : (capability.Cap × capability.Cap) × S × A}
    (h : objects.finalise_cap st ar x a (.Frame fp .Small rt false mp false asid va) fin false = ok y) :
    y.1 = (.Null, .Null) := by
  cases mp
  · rw [finCap_frame_keep ar (Or.inl rfl) h]
  · by_cases hA : asid = 0#u64
    · rw [finCap_frame_keep ar (Or.inr (Or.inl hA)) h]
    · exact (finCap_frame_pte ar hA h).1

/-- One round of a tree loop (stated for a variable budget, so no literal is reduced). -/
theorem iter_succ' {X Y : Type} (body : X → SProg (ControlFlow X Y)) (n : Nat) (x : X) :
    SProg.iter body (n + 1) x = (body x).sbind (fun c => match c with
      | .cont x' => SProg.iter body n x'
      | .done y => .ret y) := rfl

/-- **`finalise_slot_immediate` of a slot holding a small RAM frame cap** (module docstring). -/
theorem insT_finImm {R0 W0 Rf : U64 → Prop} (hR0 : ∀ q, R0 q → ¬ G q) (hW0 : ∀ q, W0 q → ¬ G q)
    (hRf : ∀ q, Rf q → ¬ G q) {x : S} {a : A}
    {slot fp rt asid va : U64} {mp : Bool} {y : core.result.Result cdt.Finalised error.Exc × S × A}
    (hc : obj.Slot.cap st slot x = ok (.Frame fp .Small rt false mp false asid va))
    (r0 : R0 slot) (r8 : R0 (core.num.U64.wrapping_add slot 8#u64))
    (hfg : ∀ fin, cdt.is_final_capability_with_cap st x slot (.Frame fp .Small rt false mp false asid va) = ok fin →
      cdt.is_final_capability_with_cap (guard st R0 W0) x slot (.Frame fp .Small rt false mp false asid va) = ok fin)
    (hfv : mp = true → asid ≠ 0#u64 → ∀ r, vspace.find_vspace_for_asid st x asid = ok r →
      vspace.find_vspace_for_asid (guard st Rf (fun _ => False)) x asid = ok r)
    (h : interp st ar (R.cdt.finalise_slot_immediate slot) x a = ok y) :
    InsT st ar G ADEq NotPresent User (R.cdt.finalise_slot_immediate slot) x a := by
  have hfu : layout.WALK_FUEL > 0#u64 := by simp [layout.WALK_FUEL, U64.rMax]
  unfold R.cdt.finalise_slot_immediate R.cdt.finalise_slot_immediate_loop at h ⊢
  rw [iter_succ'] at h ⊢
  unfold R.cdt.finalise_slot_immediate_loop.body at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  rw [if_pos hfu] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine insT_liftR h (fun v _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the slot's cap
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.obj.Slot.cap_eq] at h1 ⊢
    rw [obj.Slot.cap.guard (gS := guard st R0 W0) slot x r0 r8]
    exact h1
  replace h := hk
  rw [R.obj.Slot.cap_eq] at h1
  obtain ⟨c, ec, rfl⟩ := bind_shape h1
  rw [hc] at ec
  cases ok_inj_ff ec
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `is_null`
  refine insT_liftR h (fun b hb h => ?_)
  have eb : b = false := by simp only [capability.Cap.is_null] at hb; exact (ok_inj_ff hb).symm
  subst eb
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the finality check
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.cdt.is_final_capability_with_cap_eq] at h1 ⊢
    obtain ⟨fin, ef, rfl⟩ := bind_shape h1
    rw [hfg fin ef]
    exact bok.mpr ⟨_, rfl, rfl⟩
  replace h := hk
  rw [R.cdt.is_final_capability_with_cap_eq] at h1
  obtain ⟨fin, ef, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `finalise_cap`
  have h' := h
  rw [interp_sbind] at h'
  obtain ⟨y0, hy0, hK⟩ := bind_eq_ok' h'
  refine insT_sbind _ _ x a (insT_finCap hRf hfv hy0) (fun r hr => ?_)
  rw [hy0] at hr
  cases ok_inj_ff hr
  have hy0' := hy0
  rw [R.objects.finalise_cap_eq] at hy0'
  obtain ⟨y1, ey1, e1⟩ := bind_eq_ok' hy0'
  cases ok_inj_ff e1
  have hn := finCap_frame_nullAD ey1
  obtain ⟨⟨rem, cl⟩, x1, a1⟩ := y1
  simp only [Prod.mk.injEq] at hn
  obtain ⟨rfl, rfl⟩ := hn
  dsimp only at hK ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at hK ⊢
  refine insT_liftR hK (fun b1 hb1 h => ?_)
  have eb1 : b1 = true := by simp only [cdt.cap_removable] at hb1; exact (ok_inj_ff hb1).symm
  subst eb1
  simp only [↓reduceIte, SProg.sbind]
  trivial

/-- **`cdt.delete dest true` of a slot holding a small RAM frame cap** (module docstring). -/
theorem insT_cdtDel {R0 W0 Rf : U64 → Prop} (hR0 : ∀ q, R0 q → ¬ G q) (hW0 : ∀ q, W0 q → ¬ G q)
    (hRf : ∀ q, Rf q → ¬ G q) {x : S} {a : A}
    {dest fp rt asid va : U64} {mp : Bool} {y : core.result.Result Unit error.Exc × S × A}
    (hc : obj.Slot.cap st dest x = ok (.Frame fp .Small rt false mp false asid va))
    (r0 : R0 dest) (r8 : R0 (core.num.U64.wrapping_add dest 8#u64))
    (hfg : ∀ fin, cdt.is_final_capability_with_cap st x dest (.Frame fp .Small rt false mp false asid va) = ok fin →
      cdt.is_final_capability_with_cap (guard st R0 W0) x dest (.Frame fp .Small rt false mp false asid va) = ok fin)
    (hfv : mp = true → asid ≠ 0#u64 → ∀ r, vspace.find_vspace_for_asid st x asid = ok r →
      vspace.find_vspace_for_asid (guard st Rf (fun _ => False)) x asid = ok r)
    (hfin : ∀ y0, cdt.finalise_slot_immediate st ar x a dest = ok y0 →
      y0.1 = .Ok { success := true, cleanup := .Null })
    (hes : ∀ y0, cdt.finalise_slot_immediate st ar x a dest = ok y0 → ∀ y',
      cdt.empty_slot st ar y0.2.1 y0.2.2 dest .Null = ok y' →
      cdt.empty_slot (guard st R0 W0) ar y0.2.1 y0.2.2 dest .Null = ok y')
    (h : interp st ar (R.cdt.delete dest true) x a = ok y) :
    InsT st ar G ADEq NotPresent User (R.cdt.delete dest true) x a := by
  unfold R.cdt.delete at h ⊢
  simp only [↓reduceIte, SProg.bind_eq_sbind, SProg.pure_eq_ret] at h ⊢
  have h' := h
  rw [interp_sbind] at h'
  obtain ⟨y0, hy0, hK⟩ := bind_eq_ok' h'
  refine insT_sbind _ _ x a (insT_finImm hR0 hW0 hRf hc r0 r8 hfg hfv hy0) (fun r hr => ?_)
  rw [hy0] at hr
  cases ok_inj_ff hr
  have hy0' := hy0
  rw [R.cdt.finalise_slot_immediate_eq] at hy0'
  obtain ⟨y1, ey1, e1⟩ := bind_eq_ok' hy0'
  cases ok_inj_ff e1
  have hf1 := hfin y1 ey1
  have hes1 := hes y1 ey1
  obtain ⟨r1, x1, a1⟩ := y1
  dsimp only at hf1 hK hes1 ⊢
  subst hf1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, SProg.liftR_ok, SProg.sbind] at hK ⊢
  try dsimp only at hK ⊢
  refine insT_gstep hR0 hW0 hK (fun r h1 => ?_) (fun r _ _ => trivial)
  rw [R.cdt.empty_slot_eq] at h1 ⊢
  obtain ⟨y', ey', rfl⟩ := bind_shape h1
  rw [hes1 y' ey']
  exact bok.mpr ⟨_, rfl, rfl⟩

/-- **`decCNG` of a CNodeDelete on a CNode cap, length ≥ 2** (module docstring). -/
theorem insT_decCNG {R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → ¬ G q) (hW0 : ∀ q, W0 q → ¬ G q) {x : S} {a : A}
    {length slot buf cp cr cg cgb : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    {y : core.result.Result Unit error.Exc × S × A} (hlen : ¬ length < 2#u64)
    (hct : R0 (L.nodeAt x (L.cpu x) layout.node.CUR_THREAD))
    (hreg : ∀ i : U64, i.val < 2 → ∀ r, msg.msg_register i = ok r → R0 (regA (L.curW x) r))
    (hlk : ∀ idx depth, msg.syscall_arg st x (L.curW x) buf 0#u64 = ok idx →
      msg.syscall_arg st x (L.curW x) buf 1#u64 = ok depth → ∃ dest,
        cspace.lookup_target_slot st x (.CNode cp cr cg cgb) idx depth = ok (.Ok dest) ∧
        cspace.lookup_target_slot (guard st R0 W0) x (.CNode cp cr cg cgb) idx depth = ok (.Ok dest) ∧
        (∀ y, sched.set_thread_state st x (L.curW x) sched.TS_RESTART = ok y →
          sched.set_thread_state (guard st R0 W0) x (L.curW x) sched.TS_RESTART = ok y) ∧
        ∀ s3 y, sched.set_thread_state st x (L.curW x) sched.TS_RESTART = ok s3 →
          interp st ar (R.cdt.delete dest true) s3 a = ok y →
          InsT st ar G ADEq NotPresent User (R.cdt.delete dest true) s3 a)
    (h : interp st ar (R.decCNG fl4_abi.label.CNodeDelete length slot (.CNode cp cr cg cgb) true true true false
      buf extra) x a = ok y) :
    InsT st ar G ADEq NotPresent User
      (R.decCNG fl4_abi.label.CNodeDelete length slot (.CNode cp cr cg cgb) true true true false buf extra) x a := by
  unfold R.decCNG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret] at h ⊢
  -- the current thread
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := guard st R0 W0) x hct]
    exact h1
  replace h := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t0, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  -- `cnode.decode`
  unfold R.cnode.decode at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  rw [if_neg lblD1, if_neg lblD2, if_neg hlen] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := guard st R0 W0) x hct]
    exact h1
  replace h := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t, et, rfl⟩ := bind_shape h1
  rw [cur_thread_ok] at et
  cases ok_inj_ff et
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the two arguments
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.msg.syscall_arg_eq] at h1 ⊢
    rw [msg.syscall_arg.guard_lt (gS := guard st R0 W0) x (L.curW x) buf 0#u64 (by simp [msg.N_MSG_REGISTERS])
      (hreg 0#u64 (by simp))]
    exact h1
  replace h := hk
  rw [R.msg.syscall_arg_eq] at h1
  obtain ⟨idx, eidx, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.msg.syscall_arg_eq] at h1 ⊢
    rw [msg.syscall_arg.guard_lt (gS := guard st R0 W0) x (L.curW x) buf 1#u64 (by simp [msg.N_MSG_REGISTERS])
      (hreg 1#u64 (by simp))]
    exact h1
  replace h := hk
  rw [R.msg.syscall_arg_eq] at h1
  obtain ⟨depth, edepth, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  obtain ⟨dest, hl1, hl2, hsts, hdel⟩ := hlk idx depth eidx edepth
  -- the target slot
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.cspace.lookup_target_slot_eq] at h1 ⊢
    obtain ⟨lr, elr, rfl⟩ := bind_shape h1
    rw [hl1] at elr
    cases ok_inj_ff elr
    rw [hl2]
    exact bok.mpr ⟨_, rfl, rfl⟩
  replace h := hk
  rw [R.cspace.lookup_target_slot_eq] at h1
  obtain ⟨lr, elr, rfl⟩ := bind_shape h1
  rw [hl1] at elr
  cases ok_inj_ff elr
  dsimp only at h ⊢
  simp only [core.result.Result.Insts.CoreOpsTry.branch, SProg.liftR_ok, SProg.sbind] at h ⊢
  rw [if_neg lblD3, if_neg lblD4] at h ⊢
  simp only [↓reduceIte] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `set_thread_state RESTART`, then the deletion
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.set_thread_state_eq] at h1 ⊢
    obtain ⟨s3, es3, rfl⟩ := bind_shape h1
    rw [hsts s3 es3]
    exact bok.mpr ⟨_, rfl, rfl⟩
  rw [R.sched.set_thread_state_eq] at h1
  obtain ⟨s3, es3, rfl⟩ := bind_shape h1
  dsimp only at hk ⊢
  exact hdel s3 _ es3 hk

/-- After a CNodeDelete decode with result `Ok ()`: the reply, `after_invocation` and `finish`, given that the
reply and `finish` run alike on `guard st R0 W0`. -/
theorem insT_tailOk {R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → ¬ G q) (hW0 : ∀ q, W0 q → ¬ G q) {t : U64}
    {x : S} {a : A} {r' : Bool × S × A}
    (h : interp st ar ((R.invPostG t (.Ok ())).sbind fun r1 =>
      (R.syscall.after_invocation r1).sbind fun _ => R.syscall.finish.sbind fun _ => SProg.ret true) x a = ok r')
    (hI : ∀ z, invPostG st x a t (.Ok ()) = ok z →
      invPostG (guard st R0 W0) x a t (.Ok ()) = ok z ∧
      ∀ y, syscall.finish st ar z.1 z.2.1 = ok y → syscall.finish (guard st R0 W0) ar z.1 z.2.1 = ok y) :
    InsT st ar G ADEq NotPresent User ((R.invPostG t (.Ok ())).sbind fun r1 =>
      (R.syscall.after_invocation r1).sbind fun _ => R.syscall.finish.sbind fun _ => SProg.ret true) x a := by
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.invPostG_eq] at h1 ⊢
    obtain ⟨z, ez, rfl⟩ := bind_shape h1
    rw [(hI z ez).1]
    exact bok.mpr ⟨_, rfl, rfl⟩
  rw [R.invPostG_eq] at h1
  obtain ⟨z, ez, rfl⟩ := bind_shape h1
  dsimp only at hk ⊢
  rw [invPostG_okR ez] at hk ⊢
  refine insT_gstep hR0 hW0 hk (fun r h1 => ?_) (fun r h1 hk2 => ?_)
  · rw [R.syscall.after_invocation_eq] at h1 ⊢
    rw [syscall.after_invocation.ok_eq] at h1 ⊢
    exact h1
  rw [R.syscall.after_invocation_eq, syscall.after_invocation.ok_eq] at h1
  obtain ⟨y, ey, rfl⟩ := bind_shape h1
  cases ok_inj_ff ey
  dsimp only at hk2 ⊢
  refine insT_gstep hR0 hW0 hk2 (fun r h1 => ?_) (fun r _ _ => trivial)
  rw [R.syscall.finish_eq] at h1 ⊢
  obtain ⟨y, ey, rfl⟩ := bind_shape h1
  rw [(hI z ez).2 y ey]
  exact bok.mpr ⟨_, rfl, rfl⟩

/-- **`invCMRest` of a CNodeDelete** (module docstring): the decode tree's `InsT`, then the `Ok` tail. -/
theorem insT_restDel {R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → ¬ G q) (hW0 : ∀ q, W0 q → ¬ G q) {t : U64}
    {info : msginfo.MessageInfo} {p : localinv.Plan} {buf length : U64} {cap : capability.Cap} {x : S} {a : A}
    {r' : Bool × S × A} (h : interp st ar (invCMRest t info p buf length cap) x a = ok r')
    (hdec : ∀ y, interp st ar (R.decCNG info.label length p.slot cap true true true false buf p.extra) x a = ok y →
      InsT st ar G ADEq NotPresent User
        (R.decCNG info.label length p.slot cap true true true false buf p.extra) x a)
    (hpost : ∀ y, decCNG st ar x a info.label length p.slot cap true true true false buf p.extra = ok y →
      y.1 = .Ok () ∧ ∀ z, invPostG st y.2.1 y.2.2 t (.Ok ()) = ok z →
        invPostG (guard st R0 W0) y.2.1 y.2.2 t (.Ok ()) = ok z ∧
        ∀ w, syscall.finish st ar z.1 z.2.1 = ok w → syscall.finish (guard st R0 W0) ar z.1 z.2.1 = ok w) :
    InsT st ar G ADEq NotPresent User (invCMRest t info p buf length cap) x a := by
  unfold invCMRest at h ⊢
  have h' := h
  rw [interp_sbind] at h'
  obtain ⟨y0, hy0, hK⟩ := bind_eq_ok' h'
  refine insT_sbind _ _ x a (hdec y0 hy0) (fun r hr => ?_)
  rw [hy0] at hr
  cases ok_inj_ff hr
  have hy0' := hy0
  rw [R.decCNG_eq] at hy0'
  obtain ⟨y1, ey1, e1⟩ := bind_eq_ok' hy0'
  cases ok_inj_ff e1
  obtain ⟨hr1, hI⟩ := hpost y1 ey1
  obtain ⟨r1, x1, a1⟩ := y1
  dsimp only at hr1 hI hK ⊢
  subst hr1
  exact insT_tailOk hR0 hW0 hK hI

end trees

end Fl4Proofs.P2.PathObl
