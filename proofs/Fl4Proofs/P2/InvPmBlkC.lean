/-
# P2 (line pte, generation 15): the PageMap decode's facts at the decode state (`blk`, third part)

At a `PmPreG` entry `s`, after the prefix and the checks (`InvChk`, decode state `s2`):

* **`pm_s2`**: the invoked slot holds (at `s` and `s2`) the plan's small non-device non-EPT Frame cap, `extra[0]` is a
  slot `x0` holding at `s2` the plan's mapped PML4 cap `Pml4 root true rasid`, `check_vspace` of it accepts at `s2`,
  the small-page walk from `root` at the caller's `R10` answers at `s2` the plan's leaf `e`, and `e` is a locked
  PTE word in `PmRS` / `PmWS` (`e ≠ 0` from `SlJAtZ.spe_ne0`; `pm_leaf_pte`);
* `vspace.make_user_page.guardF`, `vspace.huge_pages.guardF` (their only store read is the `FEATURES` word),
  `invRep.guard_errPm` (an error reply runs alike given `reply_error` does; as slhuf's `invRep.guard_err8`).

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmBlkB
import Fl4Proofs.P2.InvPmFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP

noncomputable section

section g
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop} {gS : machine.Store S}

/-- `make_user_page` reads only the `FEATURES` word. -/
theorem vspace.make_user_page.guardF [GRd gS st R] (x : S)
    (h : R (core.num.U64.wrapping_add (L.ksb x) layout.ks.FEATURES)) (p at0 r : U64) (l : Bool) :
    vspace.make_user_page gS x p at0 r l = vspace.make_user_page st x p at0 r l := by
  unfold vspace.make_user_page vspace.xd_bit vspace.nx_enabled
  simp only [obj.ks_get.guard (gS := gS) x _ h]

/-- `huge_pages` reads only the `FEATURES` word. -/
theorem vspace.huge_pages.guardF [GRd gS st R] (x : S)
    (h : R (core.num.U64.wrapping_add (L.ksb x) layout.ks.FEATURES)) :
    vspace.huge_pages gS x = vspace.huge_pages st x := by
  unfold vspace.huge_pages
  simp only [obj.ks_get.guard (gS := gS) x _ h]

/-- An error reply runs alike when `reply_error` does. -/
theorem invRep.guard_errPm {A : Type} {x : S} {a : A} {t : U64} (e : error.Exc)
    (hre : ∀ e1, syscall.reply_error gS x t e1 = syscall.reply_error st x t e1) :
    invRep gS t x a (.Err e) = invRep st t x a (.Err e) := by
  unfold invRep
  cases e <;> (try simp only [hre]) <;> rfl

end g

section s2
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **The PageMap decode's facts at the decode state** (module docstring). -/
theorem pm_s2 (hA : P0.ArchTotal ar) {s : S} {a : A} {nx : U64} {s1 s2 : S} {a1 : A}
    (hE : PmPreG st Cs Ω Sg Ac Locks p K μ s) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1) :
    ∃ (fp rt asid va : U64) (mp : Bool) (x0 root rasid e : U64),
      obj.Slot.cap st p.slot s = ok (.Frame fp .Small rt false mp false asid va) ∧
      obj.Slot.cap st p.slot s2 = ok (.Frame fp .Small rt false mp false asid va) ∧
      vspace.extra p.extra 0#usize = ok (some x0) ∧ x0 ∈ K.slots ∧
      obj.Slot.cap st x0 s2 = ok (.Pml4 root true rasid) ∧
      vspace.check_vspace st s2 (.Pml4 root true rasid) = ok (.Ok (root, rasid)) ∧
      vspace.page_entry_slot st s2 root (L.mem s2 (regA (L.curW s) layout.reg.R10)) .Small = ok (.Ok e) ∧
      e ∈ K.ptes ∧ Locks s e ∧ PmRS st K Locks s e ∧ PmWS st K Locks s e ∧
      ¬ L.mem s2 (regA (L.curW s) layout.reg.R10) > fl4_abi.consts.USER_TOP ∧
      vspace.find_vspace_for_asid st s rasid = ok (.Ok root) ∧
      p.slot ∈ K.slots ∧ Locks s p.slot ∧ OutsideObjs st K.heap.tcbs Cs s p.slot := by
  obtain ⟨⟨hJ, hq, hG⟩, hEx, hRt⟩ := hE
  have Pb := hq.1.1.1
  obtain ⟨-, es1, eu, -, -, -, -⟩ := C
  have w0 := prefix_writes ar hA Pb.tp Pb.np Pb.cT es1 eu
  have hL : Slot8 K.toKLayout := fun q hq => Pb.lay.slot8 q hq
  have ag : ∀ b, SlotW K.toKLayout b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact Pb.slot_keep w0 hq hbq hb
  obtain ⟨-, -, -, -, -, -, hsl, -, hlkS, -⟩ := pm_core hq
  have hsl0 : Locks s p.slot := hlkS (fun e => slJAt_slot0 hJ (e ▸ hsl))
  have hO : OutsideObjs st K.heap.tcbs Cs s p.slot := by
    obtain ⟨x, hx, hxs⟩ := hq.2
    obtain ⟨Cw, hroot, hcl, hC⟩ := Pb.walk
    obtain ⟨q0, r0, m0, y0, hq0, hm0, hs0⟩ := lookup_slot_cn hroot hcl hx
    rw [← hxs, hs0]; exact (hC q0 r0 m0 y0 hq0 hm0).2.1
  have hq0 := hq
  obtain ⟨⟨-, ⟨t, info, ex, ht, hi, hpw⟩, harm, hlk⟩, -⟩ := hq0
  have et : t = L.curW s := by rw [cur_thread_ok] at ht; exact (ok_inj_ff ht).symm
  subst et
  rw [(harm _ info (cur_thread_ok s) hi).1] at hpw
  obtain ⟨fp, rt, asid, va, root, rasid, mp, x0, e, hcs, hx0, hx00, hcx, hpe, -, hpte, -⟩ := plan_with_mapF hpw
  have hkp := (plan_with_kp hpw).2
  rw [← hkp] at hx0
  obtain ⟨x0', hx0', hxK⟩ := pmEx_slots Pb hEx
  rw [hx0] at hx0'
  obtain rfl := ok_inj_ff hx0'
  have hf : vspace.find_vspace_for_asid st s rasid = ok (.Ok root) := hRt x0 root rasid hx0 hcx
  -- the walk at `s2` is the walk at `s`
  have hu : ¬ L.mem s (regA (L.curW s) layout.reg.R10) > fl4_abi.consts.USER_TOP := by
    intro hu
    unfold localinv.page_entry at hpe
    rw [if_pos hu] at hpe
    simp at hpe
  have hV := pm_vsRd ⟨hJ, hq, hG⟩ rasid (L.mem s (regA (L.curW s) layout.reg.R10)) (userV_of_not_gt hu)
  have hrs : ∀ b, (VsW K.toKLayout b ∧ ¬ b ∈ K.ptes) → st.read s2 b = st.read s b := fun b hb => by
    rw [L.read_eq, L.read_eq, w0.2.2 b hb.1.1 (Pb.vs_notPreW hb.1)]
  have hks : st.ks_base s2 = st.ks_base s := by rw [L.ks_base_eq, L.ks_base_eq, w0.1]
  have T2 := vsRdG_tr hV hrs hks
  have hl : vspace.lookup_pt_slot st s root (L.mem s (regA (L.curW s) layout.reg.R10)) = ok (.Ok e) := by
    unfold localinv.page_entry at hpe
    rw [if_neg hu] at hpe
    unfold vspace.small_page_entry at hpe
    obtain ⟨r, hr, hpe⟩ := bind_eq_ok hpe
    cases r with
    | Ok y =>
      have : y = e := by simpa [core.result.Result.ok] using hpe
      rw [hr, this]
    | Err _ => simp [core.result.Result.ok] at hpe
  have tk : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 → k.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add (L.curW s) k) = L.mem s (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 h3 => w0.2.2 _ (field_aligned Pb.tA h1 h2) (preW_tcb Pb.tA Pb.np Pb.cT h1 h3)
  have r10 : L.mem s2 (regA (L.curW s) layout.reg.R10) = L.mem s (regA (L.curW s) layout.reg.R10) := by
    have e := reg_keepK (st := st) Pb.tA (r := layout.reg.R10) (by simp [layout.reg.R10])
      (by simp [layout.reg.R10]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  -- the leaf
  have hne : e ≠ 0#u64 := by
    obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
    intro h0
    apply B.spe_ne0 rasid (L.mem s (regA (L.curW s) layout.reg.R10))
    unfold localinv.small_page_entry
    simp only [hf, bind_ok, core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    rw [hpe, h0]
  have hpt := pm_leaf_pte hJ hG hf (userV_of_not_gt hu) hl
  obtain ⟨hn, hle⟩ := hpte hne
  have hlk' := hlk _ e hn hle
  obtain ⟨m1, ⟨-, hpe1⟩, -⟩ := hG
  have hR : e ∈ ptesR K m1 := hpe1 ▸ hpt
  refine ⟨fp, rt, asid, va, mp, x0, root, rasid, e, hcs, by rw [cap_agree hL hsl ag]; exact hcs, ?_, hxK,
    by rw [cap_agree hL hxK ag]; exact hcx, ?_, ?_, hpt, hlk', ⟨hR.2.2.2.1, hR.2.2.2.2.1, rpermP_pte hpt hlk'⟩,
    ⟨hR.2.2.2.1, wpermP_pte hpt hlk'⟩, by rw [r10]; exact hu, hf, hsl, hsl0, hO⟩
  · unfold vspace.extra obj.Slot.is_null
    simp only [show ¬ (0#usize ≥ 3#usize) by decide, ↓reduceIte, hx0, bind_ok, decide_eq_true_eq, hx00]
  · rw [check_vspace_tr (m' := st) (x' := s2) (s := s) (root := root) T2.1]
    unfold vspace.check_vspace
    simp [hf]
  · rw [r10, page_entry_slot_small_tr (m' := st) (x' := s2) (s := s) (T2.2 root hf)]
    unfold vspace.page_entry_slot
    simp only [hl, bind_ok, ↓reduceIte]

end s2

end
end Fl4Proofs.P2.E2EP
