/-
P3 (DESIGN.md §9), VSpace, line hpzg gen 9: **the ASID / page-table walk reads no user word**.

The local frame-cap invocation's plan (P2's `localinv.plan_with`, CNodeDelete arm) asks
`localinv.small_page_entry` (`find_vspace_for_asid`, then `lookup_pt_slot` for a user address). At a
`JAtZ` state every word that walk reads is a word of the VSpace objects `VObj` (the ASID table block, an ASID
pool of `Z.P`, a table of `Z.L4` / `Z.L3` / `Z.L2`), and `TopPlaced.disj` puts every IPC-buffer word (`Z.B`)
outside `VObj`. So:

* `VsAg x s`: same kernel base, equal on every `VObj` word; `tab_vobj`, `pool_vobj`, `atA_vobj`: the walk's words
  are `VObj` words;
* `lookup_pdpt_slot_ag`, `lookup_pd_slot_ag`, `lookup_pt_slot_ag` (from a PML4 of `L4`, a user address, `PtRel`),
  `find_asid_ag`, `find_vspace_for_asid_ag` (`VsRel`), `small_page_entry_ag`: the walk answers alike at two `VsAg`
  states;
* **`JAtZ.userNotVObj`**: an IPC-buffer word is no `VObj` word (`TopPlaced.disj`);
* **`JAtZ.smallPageEntry_userWr`**: at a `JAtZ` state, writing an aligned word of `Z.B` leaves
  `localinv.small_page_entry` unchanged.

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P3.JointAt
import Fl4Proofs.P3.VsPtUnmapRel
import Fl4Proofs.P3.VsFrameMapRel
import Fl4Proofs.P1.FastDecline
import Fl4Proofs.P1.FastSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}

/-- Two states with the same kernel base, equal on every aligned word of the VSpace objects. -/
def VsAg (th : TypedHeap) (P L4 L3 L2 L1 : Set U64) (x s : S) : Prop :=
  L.ksb x = L.ksb s ∧ ∀ a, VObj th P L4 L3 L2 L1 (L.ksb s) a → Aligned a → L.mem x a = L.mem s a

theorem tab_vobj {ksb q i : U64} (hq : q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) (hal : q.val % 4096 = 0)
    (hi : i.val < 512) : VObj th P L4 L3 L2 L1 ksb (peA q i) ∧ Aligned (peA q i) := by
  have hb := q.hBounds
  have hf : q.val + 4096 ≤ 2 ^ 64 := by simp only [UScalarTy.numBits] at hb; omega
  have hv := peA_val hf hi
  exact ⟨Or.inr (Or.inr (Or.inl ⟨q, Or.inr hq, by omega, by omega⟩)), by unfold Aligned; omega⟩

theorem pool_vobj {ksb p lo : U64} (hp : p ∈ P) (hal : p.val % 4096 = 0) (hf : p.val + 4096 ≤ 2 ^ 64)
    (hlo : lo.val < 512) : VObj th P L4 L3 L2 L1 ksb (peA p lo) ∧ Aligned (peA p lo) := by
  have hv := peA_val hf hlo
  exact ⟨Or.inr (Or.inr (Or.inl ⟨p, Or.inl hp, by omega, by omega⟩)), by unfold Aligned; omega⟩

theorem atA_vobj {ksb hi : U64} (hk : ksb.val + 288000 + 16384 ≤ 2 ^ 64) (hal : ksb.val % 8 = 0)
    (h : hi.val < 2048) : VObj th P L4 L3 L2 L1 ksb (atA ksb hi) ∧ Aligned (atA ksb hi) := by
  have hv := atA_val hk h
  exact ⟨Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)), by unfold Aligned; omega⟩

variable {x s : S}

theorem lookup_pdpt_slot_ag (hA : VsAg (L := L) th P L4 L3 L2 L1 x s) (hP : PtPlaced L4 L3 L2 L1) {pm : U64}
    (hpm : pm ∈ L4) (vaddr : U64) : vspace.lookup_pdpt_slot st x pm vaddr = vspace.lookup_pdpt_slot st s pm vaddr := by
  unfold vspace.lookup_pdpt_slot
  rw [show vspace.idx vaddr 39#u64 = ok (vIdx vaddr 39) from idx_eq _ _ (by decide)]
  simp only [bind_ok]
  have hw := tab_vobj (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (ksb := L.ksb s) (Or.inl hpm) (hP pm (Or.inl hpm)) (vIdx_lt vaddr 39)
  rw [entry_eq x pm _ (vIdx_lt _ _), entry_eq s pm _ (vIdx_lt _ _), hA.2 _ hw.1 hw.2]

theorem lookup_pd_slot_ag (hA : VsAg (L := L) th P L4 L3 L2 L1 x s) {σ : Fl4Spec.State Unit}
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) {pm : U64} (hpm : pm ∈ L4) (vaddr : U64)
    (hv : UserV vaddr) : vspace.lookup_pd_slot st x pm vaddr = vspace.lookup_pd_slot st s pm vaddr := by
  unfold vspace.lookup_pd_slot
  rw [lookup_pdpt_slot_ag hA hP hpm vaddr]
  obtain ⟨r, hr, -, hsl, -⟩ := spec_ex_fd (lookup_pdpt_slot_rel s σ hR hP hpm vaddr hv)
  rw [hr]
  simp only [bind_ok]
  cases r with
  | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  | Ok y =>
    obtain ⟨q, hq, rfl⟩ := hsl _ rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have hw := tab_vobj (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (ksb := L.ksb s) (Or.inr (Or.inl hq)) (hP q (Or.inr (Or.inl hq)))
      (vIdx_lt vaddr 30)
    rw [L.read_eq, L.read_eq, hA.2 _ hw.1 hw.2]

theorem lookup_pt_slot_ag (hA : VsAg (L := L) th P L4 L3 L2 L1 x s) {σ : Fl4Spec.State Unit}
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) {pm : U64} (hpm : pm ∈ L4) (vaddr : U64)
    (hv : UserV vaddr) : vspace.lookup_pt_slot st x pm vaddr = vspace.lookup_pt_slot st s pm vaddr := by
  unfold vspace.lookup_pt_slot
  rw [lookup_pd_slot_ag hA hR hP hpm vaddr hv]
  obtain ⟨r, hr, -, hsl, -⟩ := spec_ex_fd (lookup_pd_slot_rel s σ hR hP hpm vaddr hv)
  rw [hr]
  simp only [bind_ok]
  cases r with
  | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  | Ok y =>
    obtain ⟨q, hq, rfl⟩ := hsl _ rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have hw := tab_vobj (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (ksb := L.ksb s) (Or.inr (Or.inr (Or.inl hq)))
      (hP q (Or.inr (Or.inr (Or.inl hq)))) (vIdx_lt vaddr 21)
    rw [L.read_eq, L.read_eq, hA.2 _ hw.1 hw.2]

theorem find_asid_ag (hA : VsAg (L := L) th P L4 L3 L2 L1 x s) {σ : Fl4Spec.State Unit}
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hV : VsPlaced P (L.ksb s)) (asid : U64) :
    vspace.find_asid st x asid = vspace.find_asid st s asid := by
  unfold vspace.find_asid
  congr 1
  funext i
  obtain ⟨v1, h1, rfl⟩ := spec_ex_fd (asid_table_spec (st := st) x i)
  obtain ⟨v2, h2, rfl⟩ := spec_ex_fd (asid_table_spec (st := st) s i)
  rw [h1, h2]
  simp only [bind_ok]
  have hlt := and_lt i 11 2047#u64 rfl (by decide)
  have hw := atA_vobj (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) hV.ksb_fit hV.ksb_al hlt
  rw [hA.1, hA.2 _ hw.1 hw.2]
  by_cases hp : L.mem s (atA (L.ksb s) (i &&& 2047#u64)) = 0#u64
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp]
    have hpP := hR.tmem _ hlt hp
    have hlo := and_lt asid 9 511#u64 rfl (by decide)
    simp only [lift, bind_ok]
    have hw := pool_vobj (th := th) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (ksb := L.ksb s) hpP
      (hV.pal _ hpP).1 (hV.pal _ hpP).2 hlo
    rw [L.read_eq, L.read_eq]
    simp only [bind_ok]
    rw [show core.num.U64.wrapping_add (L.mem s (atA (L.ksb s) (i &&& 2047#u64)))
        (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64) =
        peA (L.mem s (atA (L.ksb s) (i &&& 2047#u64))) (asid &&& 511#u64) from rfl, hA.2 _ hw.1 hw.2]

theorem find_vspace_for_asid_ag (hA : VsAg (L := L) th P L4 L3 L2 L1 x s) {σ : Fl4Spec.State Unit}
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hV : VsPlaced P (L.ksb s)) (asid : U64) :
    vspace.find_vspace_for_asid st x asid = vspace.find_vspace_for_asid st s asid := by
  unfold vspace.find_vspace_for_asid
  rw [find_asid_ag hA hR hV asid]

/-- **`localinv.small_page_entry` answers alike at two `VsAg` states** (the VSpace relations at `s`). -/
theorem small_page_entry_ag (hA : VsAg (L := L) th P L4 L3 L2 L1 x s) {σ : Fl4Spec.State Unit}
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hV : VsPlaced P (L.ksb s)) (hT : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hP : PtPlaced L4 L3 L2 L1) (hPI : PoolsIn P L4 (L.mem s)) (asid vaddr : U64) :
    localinv.small_page_entry st x asid vaddr = localinv.small_page_entry st s asid vaddr := by
  unfold localinv.small_page_entry
  rw [find_vspace_for_asid_ag hA hR hV asid]
  obtain ⟨r, hr, hL4⟩ := spec_ex_fd (find_vspace_for_asid_L4 (st := st) s σ hR hPI asid)
  rw [hr]
  simp only [bind_ok]
  cases r with
  | Err e => simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok]
  | Ok root =>
    have hroot := hL4 root rfl
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok]
    unfold localinv.page_entry
    by_cases hu : vaddr > fl4_abi.consts.USER_TOP
    · rw [if_pos hu, if_pos hu]
    · rw [if_neg hu, if_neg hu]
      have hv : UserV vaddr := by
        unfold UserV
        have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
        have : ¬ fl4_abi.consts.USER_TOP.val < vaddr.val := hu
        omega
      unfold vspace.small_page_entry
      rw [lookup_pt_slot_ag hA hT hP hroot vaddr hv]

end

end Fl4Proofs.P3.Vs

namespace Fl4Proofs.P3
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Vs

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **An IPC-buffer word is no VSpace-object word** at a `JAtZ` state (`TopPlaced.disj`). -/
theorem JAtZ.userNotVObj (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {wp : U64 × Fl4Spec.Word}
    (hw : wp ∈ Z.B) : ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) wp.1 :=
  J.xtop.fin.1.2.disj wp.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, le_refl _, by omega⟩)))))))

/-- (hpzg gen 9) **The ASID / page-table walk of `localinv.small_page_entry` reads no user word**: at a `JAtZ`
state, writing an aligned word of `Z.B` leaves it unchanged. -/
theorem JAtZ.smallPageEntry_userWr (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {wp : U64 × Fl4Spec.Word}
    (hw : wp ∈ Z.B) (hal : Aligned wp.1) (v asid vaddr : U64) :
    localinv.small_page_entry st (L.wr s wp.1 v) asid vaddr = localinv.small_page_entry st s asid vaddr := by
  obtain ⟨hSR, hVs, hPt, hPI, -⟩ := J.xtop.fin
  have hTP := hSR.2
  have hA : VsAg (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.wr s wp.1 v) s := by
    refine ⟨L.ksb_wr s wp.1 v, fun b hb => ?_⟩
    intro hba
    exact mem_wr_ne' hal hba (fun e => J.userNotVObj hw (e ▸ hb))
  exact small_page_entry_ag hA hVs hTP.vs hPt hTP.pt hPI asid vaddr

end

end Fl4Proofs.P3
