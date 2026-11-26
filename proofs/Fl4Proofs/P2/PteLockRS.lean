/-
# P2 (line pte, gen 8): the PTE-lock read set — shared by the PageMap arm (pte) and the Delete PTE arm (invj)

Both local paths that write a leaf page-table entry under fl4-sync's 8-byte PTE lock (`local_invocation`, plan
`localinv.rs` `add_pte`) find the entry by the same walk: `localinv.page_entry root vaddr` (PageMap; and the Delete
arm's `small_page_entry asid vaddr` after `find_vspace_for_asid`) = `vspace.lookup_pt_slot` for a user address. This
module holds what both need.

**1. The walk's read set** (namespace `PathObl`). With P3's page-table relation `PtRel L4 L3 L2 L1` at a state `s`:
* **`UpAg L4 L3 L2 x s`**: `x` and `s` agree on every entry of the upper three levels' tables (the leaf tables
  `L1`, which the locked paths write, are not asked);
* `lookup_pdpt_slot_up` / `lookup_pd_slot_up` / **`lookup_pt_slot_up`**, **`page_entry_up`**: the walk answers alike
  at two `UpAg` states (the `lookup_pt_slot` read-set lemma: only upper-level entries are read; sharper than P3's
  `lookup_pt_slot_ag`, whose `VsAg` asks every VSpace word);
* **`page_entry_ptw`** / **`page_entry_ptw_ag`**: a walk from a PML4 of `L4` that finds an entry finds a leaf entry
  (`PtW L1 e`, `lookup_pt_slot_rel`'s landing clause), also at a state agreeing with `s` on the upper levels;
* **`ptw_up_ne`**: a leaf entry is no upper-level entry (4 KiB-aligned tables; a table is of one kind).

**0. The plan builder** (namespace `PathObl`; the one copy for both lines, statements and proofs as invj's
`InvDelPte` f4dbf5ac3): `plan_add_at` (one `Plan.add`: a zero address keeps the plan; otherwise the address is
`locks[n]` and `n` grows, from below `MAX_LOCKS`), `plan_add_n4` (`n ≤ 4` is kept).

**2. Ownership under `ownP` with a leaf PTE set** (namespace `E2EP`; the ptesE convention, nscope `E2EPJEp2`, with
the leaf choice of `pteConv_of`: `K.ptes ⊆ {b | PtW Zx.L1 b}`), at a bundle state of `K.toKLayout` with ghost `Zx`:
* **`gateW_up`**: every upper-level entry is `GateW` (region `.none` by `region_none_ptw`, off `K.ptes` by
  `ptw_up_ne`): unchanged in the epoch (`exec_epoch`), readable by every local path (**`rpermP_gate`**);
* **`upAg_of_gate`**: two states agreeing on aligned `GateW` words are `UpAg` for the ghost's levels;
* **`ptesE_leaf`**: a leaf entry that is no ASID word of `m` is in `ptesE K {PtW Zx.L1} m`;
* the leaf entry's owner is `.lock e` (`OwnMapPte.ownP_pte`), written / read when its lock is held
  (`wpermP_pte` / `rpermP_pte`): the existing facts, not restated.

No named premise. New module; no existing statement changes; no `kernel_entry_reach*` touched.
-/
import Fl4Proofs.P2.E2EPJEp2
import Fl4Proofs.P2.InvSeen
import Fl4Proofs.P3.VsUserApart
open Aeneas Aeneas.Std Result


/-! ## 0. The plan builder -/

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section plan
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **One `Plan.add`**, exactly: a zero address keeps the plan; otherwise the address is `locks[n]` and `n` grows. -/
theorem plan_add_at {q : localinv.Plan} {a : U64} {x : Bool × localinv.Plan}
    (h : localinv.Plan.add q a = ok x) (ht : x.1 = true) :
    (a = 0#u64 → x.2 = q) ∧
      (a ≠ 0#u64 → x.2.locks.val[q.n.val]? = some a ∧ x.2.n.val = q.n.val + 1 ∧ q.n.val < 4) := by
  unfold localinv.Plan.add at h
  by_cases h0 : a = 0#u64
  · rw [if_pos h0] at h
    cases ok_inj_ff h
    exact ⟨fun _ => rfl, fun hn => absurd h0 hn⟩
  rw [if_neg h0] at h
  by_cases h1 : q.n >= localinv.MAX_LOCKS
  · rw [if_pos h1] at h
    cases ok_inj_ff h
    simp at ht
  rw [if_neg h1] at h
  have hn : q.n.val < 4 := by
    have h2 : ¬ localinv.MAX_LOCKS.val ≤ q.n.val := fun hc => h1 hc
    rw [maxLocks_val] at h2; omega
  have hlen : q.locks.val.length = 4 := by have hp := q.locks.property; simpa using hp
  have hl : q.n.val < q.locks.length := by
    simp only [Aeneas.Std.Array.length]; omega
  obtain ⟨a1, ea1, h⟩ := bind_eq_ok h
  obtain ⟨n1, en1, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (Aeneas.Std.Array.update_spec q.locks q.n a hl)] at ea1
  have ha1 : q.locks.set q.n a = a1 := ok_inj_ff ea1
  obtain ⟨z, ze, zv⟩ := spec_ex_fd (Usize.add_spec (x := q.n) (y := 1#usize) (by scalar_tac))
  rw [ze] at en1
  have hz : z = n1 := ok_inj_ff en1
  subst hz ha1
  cases ok_inj_ff h
  have hzv : z.val = q.n.val + 1 := by simpa using zv
  refine ⟨fun e => absurd e h0, fun _ => ⟨?_, hzv, hn⟩⟩
  simp only [Aeneas.Std.Array.set_val_eq]
  rw [List.getElem?_set_self (by omega)]

theorem plan_add_n4 {q : localinv.Plan} {a : U64} {x : Bool × localinv.Plan}
    (h : localinv.Plan.add q a = ok x) (ht : x.1 = true) (hq : q.n.val ≤ 4) : x.2.n.val ≤ 4 := by
  obtain ⟨h0, h1⟩ := plan_add_at h ht
  by_cases ha : a = 0#u64
  · rw [h0 ha]; exact hq
  · obtain ⟨-, hn, hl⟩ := h1 ha
    omega

end plan

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Vs

section walk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {L4 L3 L2 L1 : Set U64}

/-- **Two states agreeing on every entry of the upper three levels' tables.** -/
def UpAg (L4 L3 L2 : Set U64) (x s : S) : Prop :=
  ∀ q, (q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2) → ∀ i : U64, i.val < 512 → L.mem x (peA q i) = L.mem s (peA q i)

variable {x s : S}

theorem lookup_pdpt_slot_up (hA : UpAg (L := L) L4 L3 L2 x s) {pm : U64} (hpm : pm ∈ L4) (vaddr : U64) :
    vspace.lookup_pdpt_slot st x pm vaddr = vspace.lookup_pdpt_slot st s pm vaddr := by
  unfold vspace.lookup_pdpt_slot
  rw [show vspace.idx vaddr 39#u64 = ok (vIdx vaddr 39) from idx_eq _ _ (by decide)]
  simp only [bind_ok]
  rw [entry_eq x pm _ (vIdx_lt _ _), entry_eq s pm _ (vIdx_lt _ _), hA pm (Or.inl hpm) _ (vIdx_lt _ _)]

theorem lookup_pd_slot_up (hA : UpAg (L := L) L4 L3 L2 x s) {σ : Fl4Spec.State Unit}
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) {pm : U64} (hpm : pm ∈ L4) (vaddr : U64)
    (hv : UserV vaddr) : vspace.lookup_pd_slot st x pm vaddr = vspace.lookup_pd_slot st s pm vaddr := by
  unfold vspace.lookup_pd_slot
  rw [lookup_pdpt_slot_up hA hpm vaddr]
  obtain ⟨r, hr, -, hsl, -⟩ := spec_ex_fd (lookup_pdpt_slot_rel s σ hR hP hpm vaddr hv)
  rw [hr]
  simp only [bind_ok]
  cases r with
  | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  | Ok y =>
    obtain ⟨q, hq, rfl⟩ := hsl _ rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [L.read_eq, L.read_eq, hA q (Or.inr (Or.inl hq)) _ (vIdx_lt vaddr 30)]

theorem lookup_pt_slot_up (hA : UpAg (L := L) L4 L3 L2 x s) {σ : Fl4Spec.State Unit}
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) {pm : U64} (hpm : pm ∈ L4) (vaddr : U64)
    (hv : UserV vaddr) : vspace.lookup_pt_slot st x pm vaddr = vspace.lookup_pt_slot st s pm vaddr := by
  unfold vspace.lookup_pt_slot
  rw [lookup_pd_slot_up hA hR hP hpm vaddr hv]
  obtain ⟨r, hr, -, hsl, -⟩ := spec_ex_fd (lookup_pd_slot_rel s σ hR hP hpm vaddr hv)
  rw [hr]
  simp only [bind_ok]
  cases r with
  | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  | Ok y =>
    obtain ⟨q, hq, rfl⟩ := hsl _ rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [L.read_eq, L.read_eq, hA q (Or.inr (Or.inr hq)) _ (vIdx_lt vaddr 21)]

theorem userV_of_not_gt {vaddr : U64} (hu : ¬ vaddr > fl4_abi.consts.USER_TOP) : UserV vaddr := by
  unfold UserV
  have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
  have : ¬ fl4_abi.consts.USER_TOP.val < vaddr.val := hu
  omega

/-- **The plan's walk answers alike at two states agreeing on the upper levels.** -/
theorem page_entry_up (hA : UpAg (L := L) L4 L3 L2 x s) {σ : Fl4Spec.State Unit}
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) {root : U64} (hroot : root ∈ L4)
    (vaddr : U64) : localinv.page_entry st x root vaddr = localinv.page_entry st s root vaddr := by
  unfold localinv.page_entry
  by_cases hu : vaddr > fl4_abi.consts.USER_TOP
  · rw [if_pos hu, if_pos hu]
  · rw [if_neg hu, if_neg hu]
    unfold vspace.small_page_entry
    rw [lookup_pt_slot_up hA hR hP hroot vaddr (userV_of_not_gt hu)]

/-- **A found walk entry is a leaf entry** (`PtW L1`). -/
theorem page_entry_ptw {σ : Fl4Spec.State Unit} (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1)
    {root : U64} (hroot : root ∈ L4) {vaddr e : U64}
    (h : localinv.page_entry st s root vaddr = ok (some e)) : PtW L1 e := by
  unfold localinv.page_entry at h
  by_cases hu : vaddr > fl4_abi.consts.USER_TOP
  · rw [if_pos hu] at h
    simp at h
  rw [if_neg hu] at h
  unfold vspace.small_page_entry at h
  obtain ⟨r, hr, -, hsl, -⟩ := spec_ex_fd (lookup_pt_slot_rel s σ hR hP hroot vaddr (userV_of_not_gt hu))
  rw [hr] at h
  simp only [bind_ok] at h
  cases r with
  | Err e' => simp [core.result.Result.ok] at h
  | Ok y =>
    have hy : y = e := by simpa [core.result.Result.ok] using h
    subst hy
    obtain ⟨q, hq, rfl⟩ := hsl _ rfl
    exact ⟨q, hq, vIdx vaddr 12, vIdx_lt _ _, rfl⟩

/-- **The plan's walk at a state agreeing with `s` on the upper levels lands in `s`'s leaf tables.** -/
theorem page_entry_ptw_ag (hA : UpAg (L := L) L4 L3 L2 x s) {σ : Fl4Spec.State Unit}
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) {root : U64} (hroot : root ∈ L4)
    {vaddr e : U64} (h : localinv.page_entry st x root vaddr = ok (some e)) : PtW L1 e :=
  page_entry_ptw hR hP hroot ((page_entry_up hA hR hP hroot vaddr).symm.trans h)

end walk

end Fl4Proofs.P2.PathObl

/-! ## 1b. Levels are apart -/

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Vs

section lv
variable {L4 L3 L2 L1 : Set U64}

theorem up_all {q : U64} (h : q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2) : q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1 := by
  rcases h with h | h | h
  exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h))]

/-- **A leaf entry is no upper-level entry.** -/
theorem ptw_up_ne {m : U64 → U64} {σ : Fl4Spec.State Unit} (hR : PtRel L4 L3 L2 L1 m σ)
    (hP : PtPlaced L4 L3 L2 L1) {q q' : U64} (hq : q ∈ L1) (hq' : q' ∈ L4 ∨ q' ∈ L3 ∨ q' ∈ L2) {i j : U64}
    (hi : i.val < 512) (hj : j.val < 512) : peA q i ≠ peA q' j := by
  intro he
  have ha := hP q (Or.inr (Or.inr (Or.inr hq)))
  have ha' := hP q' (up_all (L1 := L1) hq')
  have v1 := peA_val (tbl_fit ha) hi
  have v2 := peA_val (tbl_fit ha') hj
  have hv : (peA q i).val = (peA q' j).val := by rw [he]
  have hqq : q = q' := UScalar.eq_of_val_eq (by omega)
  subst hqq
  obtain ⟨f, hk, -⟩ := hR.l1 q hq
  rcases hq' with h | h | h
  · obtain ⟨f', hk', -⟩ := hR.l4 q h; rw [hk] at hk'; simp at hk'
  · obtain ⟨f', hk', -⟩ := hR.l3 q h; rw [hk] at hk'; simp at hk'
  · obtain ⟨f', hk', -⟩ := hR.l2 q h; rw [hk] at hk'; simp at hk'

end lv

end Fl4Proofs.P2.PathObl

/-! ## 2. Ownership with a leaf PTE set -/

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P3.Vs (PtW PtWAll peA PtRel PtPlaced)

section own
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A' : Type} {arI : machine.Arch A'}
  {AR : A' → Fl4Spec.Cr3 → Prop} {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64}
  {D : Set U64} {s : S} {a' : A'} {σ : Fl4Spec.State Unit} {K : KLayoutP}

/-- **Every upper-level entry is a gate word** under a leaf PTE set. -/
theorem gateW_up (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout s a' σ)
    (hsub : ∀ b ∈ K.ptes, PtW Zx.L1 b) (nv : K.vcpus = ∅) {q : U64} (hq : q ∈ Zx.L4 ∨ q ∈ Zx.L3 ∨ q ∈ Zx.L2)
    {i : U64} (hi : i.val < 512) : GateW K (peA q i) := by
  have hTP := B.j.xtop.fin.1.2
  have hPR := B.j.xtop.fin.2.2.1
  have hw : PtWAll Zx.L4 Zx.L3 Zx.L2 Zx.L1 (peA q i) :=
    ⟨q, up_all (L1 := Zx.L1) hq, i, hi, rfl⟩
  refine gateW_of_region (region_none_ptw B hw) (fun hp => ?_) nv
  obtain ⟨q', hq', j, hj, he⟩ := hsub _ hp
  exact ptw_up_ne hPR hTP.pt hq' hq hj hi he.symm

/-- A gate word is readable by every local path. -/
theorem rpermP_gate {x c : U64} {lk : U64 → Prop} (h : GateW K x) (m : U64 → U64) :
    PathObl.RPerm (ownP K) c lk m x :=
  Or.inr (h m)

/-- **Agreement on the aligned gate words gives `UpAg`** for the ghost's levels. -/
theorem upAg_of_gate (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout s a' σ)
    (hsub : ∀ b ∈ K.ptes, PtW Zx.L1 b) (nv : K.vcpus = ∅) {x : S}
    (hag : ∀ w, GateW K w → Aligned w → L.mem x w = L.mem s w) : UpAg (L := L) Zx.L4 Zx.L3 Zx.L2 x s := by
  intro q hq i hi
  have hTP := B.j.xtop.fin.1.2
  have ha : q.val % 4096 = 0 := hTP.pt q (up_all (L1 := Zx.L1) hq)
  have hv := Fl4Proofs.P3.Vs.peA_val (Fl4Proofs.P3.Vs.tbl_fit ha) hi
  exact hag _ (gateW_up B hsub nv hq hi) (by show (peA q i).val % 8 = 0; rw [hv]; omega)

/-- **A leaf entry that is no ASID word of `m` is in the leaf convention's set.** -/
theorem ptesE_leaf {L1 : Set U64} {m : U64 → U64} {e : U64} (hw : PtW L1 e)
    (hna : ∀ hi : U64, hi.val < 2048 → e ≠ atAF K.ksb hi ∧
      (m (atAF K.ksb hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 → e ≠ peAF (m (atAF K.ksb hi)) lo)) :
    e ∈ ptesE K {b | PtW L1 b} m :=
  ⟨hw, hna⟩

end own

end Fl4Proofs.P2.E2EP
