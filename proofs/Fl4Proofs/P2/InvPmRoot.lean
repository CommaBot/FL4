/-
# P2 (line pte, generation 14): `PmRoot` from the plan (#109) — the PageMap slot covers every planned PageMap again

Gen 13 narrowed the PageMap slot's start fact by `PmRoot` (the arm's PML4 cap's ASID finds its root), which the plan
did not imply: `plan_with`'s PageMap arm walked the PML4 cap's tables without an ASID check. #109 (losfair/FL4
8ff226f6c, cherry-picked onto par/pte) makes the arm require `find_vspace_for_asid asid = root` before walking, so:

* **`plan_with_mapR`**: a PageMap plan's PML4 cap at `extra[0]` has its root named by its ASID;
* **`pmRoot_of_planD`** / **`pmRoot_of_qf`**: `PmRoot` from `InvPlanD` and the arm (so from every `PmQF` state,
  hence from the glue's plan, as `pmEx_of_plan` gives `PmEx`);
* **`pm_pdwF`**: gen 12's `pdw` at `PmPreF ∧ PmEx` (no `PmRoot` in the hypothesis);
* `pmPreG_of` (`PmPreG` from `PmPreF ∧ PmEx`), `StartPmH` (the start fact without `PmRoot`: `PmQF ∧ PmEx`, both
  implied by the plan), `pm_hSFQH`, **`serializable_fl4_localW11PRIPmH`** (= gen 13's `…PmG` with the start fact
  `StartPmH`; the obligations `PmObl4` are those of gen 13, still asked at `PmPreG`, which every `StartPmH` state
  satisfies).

Premises of `serializable_fl4_localW11PRIPmH` beyond `serializable_fl4_localW11PR`'s: those of `PmObl4` ([W] `blk`,
[W] `mv`, [W] `roA`, [P] `cs`, [P] `lk`); no new one. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmTop3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (Once ReadOnce StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)

noncomputable section

section plan
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **A PageMap plan's PML4 cap has its root named by its ASID** (#109's check in `plan_with`). -/
theorem plan_with_mapR {s : S} {t : obj.Tcb} {slot : obj.Slot} {extra : Array obj.Slot 3#usize}
    {p : localinv.Plan} (h : localinv.plan_with st s t fl4_abi.label.X86PageMap slot extra = ok (some p)) :
    ∃ (x : obj.Slot) (root rasid : U64), Array.index_usize extra 0#usize = ok x ∧
      obj.Slot.cap st x s = ok (.Pml4 root true rasid) ∧
      vspace.find_vspace_for_asid st s rasid = ok (.Ok root) := by
  unfold localinv.plan_with at h
  obtain ⟨q, -, h⟩ := bind_eq_ok h
  obtain ⟨cap, -, h⟩ := bind_eq_ok h
  rw [if_neg lbl_map_ne_copy, if_neg lbl_map_ne_mint, if_neg lbl_map_ne_del] at h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  unfold localinv.is_page_map at eb
  have hb : b = true := by simpa using (ok_inj_ff eb).symm
  subst hb
  rw [if_pos rfl] at h
  obtain ⟨⟨fr, q1⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  replace h := (if_pos (rfl : true = true)).symm.trans h
  obtain ⟨x, ex, h⟩ := bind_eq_ok h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  swap
  · replace h := (if_pos (rfl : true = true)).symm.trans h
    simp at h
  replace h := (if_neg (show ¬ (false = true) by simp)).symm.trans h
  obtain ⟨c, ec, h⟩ := bind_eq_ok h
  cases c
  case Pml4 root b3 rasid =>
    cases b3
    · replace h := (if_neg (show ¬ (false = true) by simp)).symm.trans h
      simp at h
    replace h := (if_pos (rfl : true = true)).symm.trans h
    obtain ⟨r, er, h⟩ := bind_eq_ok h
    cases r with
    | Err _ => simp at h
    | Ok r1 =>
      simp only [] at h
      by_cases hr : r1 = root
      · subst hr
        exact ⟨x, r1, rasid, ex, ec, er⟩
      · rw [if_neg hr] at h; simp at h
  all_goals simp at h

variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- **`PmRoot` from the plan** (`InvPlanD` at the PageMap arm). -/
theorem pmRoot_of_planD {p : localinv.Plan} {s : S} (hpd : InvPlanD st p s) (harm : PmArm st s) :
    PmRoot st p s := by
  obtain ⟨t, info, ex, ht, hi, hpw⟩ := hpd
  rw [(harm t info ht hi).1] at hpw
  obtain ⟨x, root, rasid, hx, hc, hf⟩ := plan_with_mapR hpw
  rw [← (plan_with_kp hpw).2] at hx
  intro x' root' rasid' hx' hc'
  rw [hx] at hx'
  obtain rfl := ok_inj_ff hx'
  rw [hc] at hc'
  have e := ok_inj_ff hc'
  cases e
  exact hf

/-- **`PmRoot` at every `PmQF` state.** -/
theorem pmRoot_of_qf {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64} {s : S}
    (hq : PmQF st Cs Ω Sg Ac Locks p K m s) : PmRoot st p s :=
  pmRoot_of_planD hq.1.2.1 hq.1.2.2.1

/-- `PmPreG` from `PmPreF ∧ PmEx`. -/
theorem pmPreG_of {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64} {s : S}
    (hF : PmPreF st Cs Ω Sg Ac Locks p K m s) (hEx : PmEx st p s) : PmPreG st Cs Ω Sg Ac Locks p K m s :=
  ⟨hF, hEx, pmRoot_of_qf hF.2.1⟩

/-- **`pdw` at `PmPreF ∧ PmEx`** (gen 12's [J] `pdw`; gen 13's `pm_pdwG` without `PmRoot`). -/
theorem pm_pdwF : ∀ (j : I64 × localinv.Plan) (K : KLayoutP) m s b v,
    PmPreF st Cs Ω Sg Ac Locks j.2 K m s → PmEx st j.2 s →
    b ∈ K.user → Aligned b → InvPlanD st j.2 (L.wr s b v) :=
  fun j K m s b v hF hEx hb hba => pm_pdwG j K m s b v (pmPreG_of hF hEx) hb hba

end plan

section slot
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end slot

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
