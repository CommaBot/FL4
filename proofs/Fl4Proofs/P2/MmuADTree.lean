/-
# P2 (line mmuAD, gen 6): **the walk trees are insensitive to bits 5 and 6 on every branch**

The remaining obligation of the masked bridge (`E2EPU3e.AccIns`) is tree-level along the accepted runs of delPte and
CNodeDelete: every paging-word read there is one of the `unmap_page` walk's. This module proves the walk sites:

* `SInsQ Q p`: every read of `p` (on every branch) has a continuation equal for `Q`-equivalent values; `p` makes no
  pair read, store, zeroing or Arch call. `sIns_sbind`, `sIns_liftR_sbind` (a pure step), **`insT_of_sIns`**
  (an `SInsQ` tree is `InsT` for every word set, store, state and Arch state), and with `E2EADQ.insT_sbind`
  a walk call inside a larger tree costs nothing beyond the rest of the run.
* **`sIns_lookup_pdpt_slot`**, **`sIns_lookup_pd_slot`**, **`sIns_lookup_pt_slot`**: the generated trees
  `R.vspace.lookup_*_slot` read paging entries only through `&&& 1` (present), `&&& 128` (PS) and `table_of`
  (`&&& ADDR_MASK`), so they are `SInsQ ADEq` (`MmuADWalk.and_eq_of_adEq` with `kP`, `kPS`, `kADDR`).

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.E2EADQ
import Fl4Proofs.P2.MmuADWalk
import Fl4Proofs.P2.ProgGenCd9
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.MmuAD (ADEq and_eq_of_adEq kP kPS kADDR)
open Fl4Proofs.P3.Vs (P_PRESENT_eq P_PS_eq)
open Fl4Proofs.P2.E2E (InsT)

noncomputable section

/-- **Insensitive on every branch** (module docstring). -/
inductive SInsQ (Q : U64 → U64 → Prop) {X : Type} : SProg X → Prop
  | ret (x : X) : SInsQ Q (.ret x)
  | err (e : Error) : SInsQ Q (.err e)
  | rd {q : U64} {k : U64 → SProg X} : (∀ u v, Q u v → k u = k v) → (∀ v, SInsQ Q (k v)) → SInsQ Q (.rd q k)

variable {Q : U64 → U64 → Prop}

theorem sIns_sbind {X Y : Type} {p : SProg X} {f : X → SProg Y} (hp : SInsQ Q p) (hf : ∀ x, SInsQ Q (f x)) :
    SInsQ Q (p.sbind f) := by
  induction hp with
  | ret x => exact hf x
  | err e => exact .err e
  | rd hk _ ih => exact .rd (fun u v huv => by simp only [hk u v huv]) ih

theorem sIns_liftR_sbind {X Y : Type} {r : Result X} {f : X → SProg Y} (hf : ∀ x, SInsQ Q (f x)) :
    SInsQ Q ((SProg.liftR r).sbind f) := by
  unfold SProg.liftR
  by_cases h1 : ∃ v, r = ok v
  · rw [dif_pos h1]; exact hf _
  · rw [dif_neg h1]
    by_cases h2 : ∃ e, r = fail e
    · rw [dif_pos h2]; exact .err _
    · rw [dif_neg h2]; exact .err _

theorem sIns_liftR {X : Type} {r : Result X} : SInsQ Q (SProg.liftR r) := by
  unfold SProg.liftR
  by_cases h1 : ∃ v, r = ok v
  · rw [dif_pos h1]; exact .ret _
  · rw [dif_neg h1]
    by_cases h2 : ∃ e, r = fail e
    · rw [dif_pos h2]; exact .err _
    · rw [dif_neg h2]; exact .err _

theorem sIns_ite {X : Type} {c : Prop} [Decidable c] {p q : SProg X} (hp : SInsQ Q p) (hq : SInsQ Q q) :
    SInsQ Q (if c then p else q) := by
  by_cases h : c
  · rw [if_pos h]; exact hp
  · rw [if_neg h]; exact hq

/-- **An everywhere-insensitive tree is `InsT`** for every word set, at every state. -/
theorem insT_of_sIns {S A X : Type} {st : machine.Store S} {ar : machine.Arch A} {G NP User : U64 → Prop}
    {p : SProg X} (hp : SInsQ Q p) : ∀ (s : S) (a : A), InsT st ar G Q NP User p s a := by
  induction hp with
  | ret x => intros; trivial
  | err e => intros; trivial
  | rd hk _ ih =>
    intro s a
    simp only [InsT]
    exact fun v _ => ⟨fun _ u huv => hk u v huv, ih v s a⟩

section walk

theorem table_of_adEq {u v : U64} (h : ADEq u v) : vspace.table_of u = vspace.table_of v := by
  unfold vspace.table_of; rw [and_eq_of_adEq h kADDR]

/-- **`lookup_pdpt_slot`'s tree** (module docstring). -/
theorem sIns_lookup_pdpt_slot (pml4 vaddr : U64) : SInsQ ADEq (R.vspace.lookup_pdpt_slot pml4 vaddr) := by
  unfold R.vspace.lookup_pdpt_slot R.vspace.entry
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind, SProg.read]
  refine sIns_liftR_sbind fun i => .rd (fun u v huv => ?_) (fun v => ?_)
  · simp only [P_PRESENT_eq, SProg.liftR_ok, SProg.sbind, and_eq_of_adEq huv kP, table_of_adEq huv]
  · simp only [P_PRESENT_eq, SProg.liftR_ok, SProg.sbind]
    refine sIns_ite (.ret _) (sIns_liftR_sbind fun _ => sIns_liftR_sbind fun _ => sIns_liftR_sbind fun _ => .ret _)

/-- **`lookup_pd_slot`'s tree** (module docstring). -/
theorem sIns_lookup_pd_slot (pml4 vaddr : U64) : SInsQ ADEq (R.vspace.lookup_pd_slot pml4 vaddr) := by
  unfold R.vspace.lookup_pd_slot
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind, SProg.read]
  refine sIns_sbind (sIns_lookup_pdpt_slot pml4 vaddr) fun r => sIns_liftR_sbind fun cf => ?_
  rcases cf with val | res
  · simp only [SProg.sbind]
    refine .rd (fun u v huv => ?_) (fun v => ?_)
    · simp only [P_PRESENT_eq, P_PS_eq, SProg.liftR_ok, SProg.sbind, and_eq_of_adEq huv kP,
        and_eq_of_adEq huv kPS, table_of_adEq huv]
    · simp only [P_PRESENT_eq, P_PS_eq, SProg.liftR_ok, SProg.sbind]
      exact sIns_ite (.ret _) (sIns_ite (.ret _)
        (sIns_liftR_sbind fun _ => sIns_liftR_sbind fun _ => sIns_liftR_sbind fun _ => .ret _))
  · first
      | exact sIns_liftR
      | exact sIns_liftR_sbind fun _ => .ret _

/-- **`lookup_pt_slot`'s tree** (module docstring). -/
theorem sIns_lookup_pt_slot (pml4 vaddr : U64) : SInsQ ADEq (R.vspace.lookup_pt_slot pml4 vaddr) := by
  unfold R.vspace.lookup_pt_slot
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind, SProg.read]
  refine sIns_sbind (sIns_lookup_pd_slot pml4 vaddr) fun r => sIns_liftR_sbind fun cf => ?_
  rcases cf with val | res
  · simp only [SProg.sbind]
    refine .rd (fun u v huv => ?_) (fun v => ?_)
    · simp only [P_PRESENT_eq, P_PS_eq, SProg.liftR_ok, SProg.sbind, and_eq_of_adEq huv kP,
        and_eq_of_adEq huv kPS, table_of_adEq huv]
    · simp only [P_PRESENT_eq, P_PS_eq, SProg.liftR_ok, SProg.sbind]
      exact sIns_ite (.ret _) (sIns_ite (.ret _)
        (sIns_liftR_sbind fun _ => sIns_liftR_sbind fun _ => sIns_liftR_sbind fun _ => .ret _))
  · first
      | exact sIns_liftR
      | exact sIns_liftR_sbind fun _ => .ret _

end walk

end
end Fl4Proofs.P2.PathObl
