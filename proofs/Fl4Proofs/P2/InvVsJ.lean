/-
# P2 (line invj, generation 1): `InvVsJ` from the joint invariant (`invVsJ_of`)

stpost gen 14's [J] `InvVsJ` (P2/InvVs.lean) asks, at a state of `Pre`, for every mapped small RAM frame cap with a
non-zero ASID in a capability slot: `vaddr ≤ USER_TOP`, `small_page_entry` never `some 0`, and `VsRd` (the ASID /
page-table walk runs alike on the store guarded to `VsW K`, the aligned, region-less, non-user words). All three
hold at every `SlJAt` state:

* **`vaddr ≤ USER_TOP`**: P3's weakened VSpace cap placement `JAtZ.vsc` (`VsSlotsW`; for a frame cap `VCapOK`:
  a mapped frame cap's `vaddr` is `UserV`, l4v `valid_cap`'s `wellformed_mapdata`, set by the frame map's
  `vaddr > USER_TOP` check);
* **`small_page_entry ≠ some 0`** (`SlJAtZ.spe_ne0`): a found entry is the address of an entry of an `L1` table
  (`lookup_pt_slot_rel`), a spec page table (`PtRel.l1`), hence an `other` object of `H` (`SpecCover.arch`),
  so not at 0 (`JKern.h0`), 4K-aligned (`PtPlaced`), so the entry address is at least 4096;
* **`VsRd`** (`SlJAtZ.vsRd`): the walk's words are the ASID table (`SlJAtZ.asid`), ASID pools (`SlJAtZ.pool`)
  and the entries of the `L4` / `L3` / `L2` tables (`SlJAtZ.tabVsW`: outside the objects of `Zx.th`,
  `TopPlaced.po`; off the endpoint / notification / SC sets, `TopPlaced.disj`; off the nodes, as an `other`
  object of `H`, `JKern.hnd`), none of them a user word (`JAtZ.userNotVObj`, hpzg gen 9); then the guarded-store
  lemmas `vspace.find_vspace_for_asid.guard` (P2/AccessVm.lean) and the new `vsj_entry_guard`,
  `vsj_pdpt_guard`, `vsj_pd_guard`, `vsj_pt_guard`.

* **`invVsJ_of`**: `InvVsJ st K P` for every `P` implying `SlJAt K`. No premise.

No existing statement changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvPD
import Fl4Proofs.P2.AccessVm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region)

/-! ## The page-table walk on a guarded store -/

section ptg
variable {S : Type} {st : machine.Store S} {R : U64 → Prop} {gS : machine.Store S} [GRd gS st R]
  [L : LawfulStore st]

theorem vsj_entry_guard (s : S) (t i : U64) (hi : i.val < 512) (h : R (Fl4Proofs.P3.Vs.peA t i)) :
    vspace.entry gS s t i = vspace.entry st s t i := by
  unfold vspace.entry
  simp only [lift, bind_ok]
  rw [Fl4Proofs.P3.Vs.and511_of_lt hi]
  exact gst_read h

theorem vsj_pdpt_guard (s : S) (pm vaddr : U64)
    (h : R (Fl4Proofs.P3.Vs.peA pm (Fl4Proofs.P3.Vs.vIdx vaddr 39))) :
    vspace.lookup_pdpt_slot gS s pm vaddr = vspace.lookup_pdpt_slot st s pm vaddr := by
  unfold vspace.lookup_pdpt_slot
  rw [show vspace.idx vaddr 39#u64 = ok (Fl4Proofs.P3.Vs.vIdx vaddr 39) from
    Fl4Proofs.P3.Vs.idx_eq _ _ (by decide)]
  simp only [bind_ok]
  rw [vsj_entry_guard s pm _ (Fl4Proofs.P3.Vs.vIdx_lt _ _) h]

theorem vsj_pd_guard (s : S) (pm vaddr : U64)
    (h1 : R (Fl4Proofs.P3.Vs.peA pm (Fl4Proofs.P3.Vs.vIdx vaddr 39)))
    (h2 : ∀ y, vspace.lookup_pdpt_slot st s pm vaddr = ok (.Ok y) → R y) :
    vspace.lookup_pd_slot gS s pm vaddr = vspace.lookup_pd_slot st s pm vaddr := by
  unfold vspace.lookup_pd_slot
  rw [vsj_pdpt_guard s pm vaddr h1]
  refine bind_guard_congr rfl fun r hr => ?_
  cases r with
  | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  | Ok y =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [gst_read (h2 y hr)]

theorem vsj_pt_guard (s : S) (pm vaddr : U64)
    (h1 : R (Fl4Proofs.P3.Vs.peA pm (Fl4Proofs.P3.Vs.vIdx vaddr 39)))
    (h2 : ∀ y, vspace.lookup_pdpt_slot st s pm vaddr = ok (.Ok y) → R y)
    (h3 : ∀ y, vspace.lookup_pd_slot st s pm vaddr = ok (.Ok y) → R y) :
    vspace.lookup_pt_slot gS s pm vaddr = vspace.lookup_pt_slot st s pm vaddr := by
  unfold vspace.lookup_pt_slot
  rw [vsj_pd_guard s pm vaddr h1 h2]
  refine bind_guard_congr rfl fun r hr => ?_
  cases r with
  | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  | Ok y =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [gst_read (h3 y hr)]

end ptg

/-! ## The walk's words at a bundle state -/

section words
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit}

/-- **A VSpace-object word outside the objects of `Zx.th` and off the nodes is in no region** (`SlJAtZ.vsNone`'s
argument, for any such word). -/
theorem SlJAtZ.vobjNone (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {b : U64}
    (hO : Fl4Proofs.P3.OutsideObjects Zx.th b)
    (hV : Fl4Proofs.P3.Vs.VObj Zx.th Zx.P Zx.L4 Zx.L3 Zx.L2 Zx.L1 (L.ksb s) b)
    (hn : ∀ c, ¬ InNode K c b) : region K b = .none := by
  have hTP := B.j.xtop.fin.1.2
  obtain ⟨Tr, Cq, hJ⟩ := B.j.jpl
  have hnd : ¬ ∃ c, InNode K c b := fun ⟨c, hc⟩ => hn c hc
  have hslot : ¬ ∃ p ∈ K.slots, InW p 32 b := by
    rintro ⟨p, hp, g1, g2⟩
    rw [B.slots] at hp
    obtain ⟨q, i, hqi, rfl⟩ := hp
    obtain ⟨k, hk', hsz⟩ := hqi.size
    have hv := hqi.val hJ.pl
    exact hO.2 q k hk' ⟨by omega, by omega⟩
  have htcb : ¬ ∃ t, K.heap t = some .tcb ∧ InW t (2 ^ 12) b := by
    rintro ⟨t, ht, g1, g2⟩
    exact hO.2 t .tcb ((hJ.tcb t).2 ht) ⟨g1, by simp only [Fl4Proofs.P3.objSize]; omega⟩
  have hnt : ¬ ∃ p, K.heap p = some .ntfn ∧ InW p (2 ^ 6) b := by
    rintro ⟨p, hp, g1, g2⟩
    exact hTP.disj b (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, B.j.hset.2.1 p hp, g1, by omega⟩)))))) hV
  have hob : ¬ ∃ p, (K.heap p = some .ep ∧ InW p (2 ^ 4) b) ∨ (K.heap p = some .reply ∧ InW p (2 ^ 5) b) := by
    rintro ⟨p, ⟨hp, g1, g2⟩ | ⟨hp, g1, g2⟩⟩
    · exact hTP.disj b (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, B.j.hset.1 p hp, g1, by omega⟩)))) hV
    · exact hTP.disj b (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, B.j.hset.2.2 p hp, g1, by omega⟩))))) hV
  have hsc : ¬ ∃ p z, K.heap p = some (.sc z) ∧ InW p (2 ^ z) b := by
    rintro ⟨p, z, hp, g1, g2⟩
    have hpC := B.j.hscC p z hp
    obtain ⟨Q, R0, hc, hs⟩ := B.j.xtop.fin.1.1.1.lists
    obtain ⟨x, n, hk, -⟩ := hs.scs p hpC
    have e := (hJ.sc p x n (B.j.c0 p hpC) hk).2
    rw [hp] at e
    have ez : z = n + Fl4Spec.minSchedContextBits := by
      injection e with e; injection e
    exact hTP.disj b (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, hpC, x, n, hk, g1, by rw [← ez]; exact g2⟩))))))) hV
  unfold region
  rw [dif_neg hnd, dif_neg hslot, dif_neg htcb, dif_neg hnt, dif_neg hob, dif_neg hsc]

/-- A VSpace-object word is no user word of the layout (`JAtZ.userNotVObj`). -/
theorem SlJAtZ.vobj_nu (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {b : U64}
    (hV : Fl4Proofs.P3.Vs.VObj Zx.th Zx.P Zx.L4 Zx.L3 Zx.L2 Zx.L1 (L.ksb s) b) : b ∉ K.user := by
  intro hb
  rw [B.user] at hb
  obtain ⟨wp, hw, rfl⟩ := hb
  exact B.j.userNotVObj hw hV

/-- **A page-table entry word is a `VsW` word** (module docstring). -/
theorem SlJAtZ.tabVsW (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {q i : U64}
    (hq : q ∈ Zx.L4 ∨ q ∈ Zx.L3 ∨ q ∈ Zx.L2 ∨ q ∈ Zx.L1) (hi : i.val < 512) :
    VsW K (Fl4Proofs.P3.Vs.peA q i) := by
  have hTP := B.j.xtop.fin.1.2
  have hPt := B.j.xtop.fin.2.2.1
  have hal := hTP.pt q hq
  have hw := Fl4Proofs.P3.Vs.tab_vobj (th := Zx.th) (P := Zx.P) (L4 := Zx.L4) (L3 := Zx.L3) (L2 := Zx.L2)
    (L1 := Zx.L1) (ksb := L.ksb s) hq hal hi
  have hO := hTP.po _ ⟨q, hq, i, hi, rfl⟩
  have hk := B.ksb
  have hArch : ∃ ao, σ.kheap q.bv = some (.archObj ao) := by
    rcases hq with h | h | h | h
    · obtain ⟨f, hf, -⟩ := hPt.l4 q h; exact ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hPt.l3 q h; exact ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hPt.l2 q h; exact ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hPt.l1 q h; exact ⟨_, hf⟩
  obtain ⟨ao, hf⟩ := hArch
  obtain ⟨n, hn12, hH⟩ := B.j.cover.arch _ _ hf
  have hH' : K.heap q = some (.other n) := hH
  have hb := q.hBounds
  have hfit : q.val + 4096 ≤ 2 ^ 64 := by simp only [UScalarTy.numBits] at hb; omega
  have hv : (Fl4Proofs.P3.Vs.peA q i).val = q.val + 8 * i.val := Fl4Proofs.P3.Vs.peA_val hfit hi
  have h4 : (4096 : Nat) ≤ 2 ^ n :=
    calc (4096 : Nat) = 2 ^ 12 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn12
  refine ⟨hw.2, B.vobjNone hO hw.1 fun c ⟨hc, h1, h2⟩ => ?_, B.vobj_nu hw.1⟩
  have hnd := B.j.kern.hnd _ _ hH' c ((B.cs c).2 hc)
  simp only [HKind.bits, LawfulStore.nodeBase] at hnd
  rw [hv, ← hk] at h1 h2
  omega

/-- **The ASID table and pool words are `VsW` words** (`RdTab (VsW K)`). -/
theorem SlJAtZ.rdTab (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) : RdTab (L := L) (VsW K) s := by
  have hk := B.ksb
  have hTP := B.j.xtop.fin.1.2
  intro hi hhi
  have hA := B.asid hi hhi
  rw [← hk] at hA
  have hw := Fl4Proofs.P3.Vs.atA_vobj (th := Zx.th) (P := Zx.P) (L4 := Zx.L4) (L3 := Zx.L3) (L2 := Zx.L2)
    (L1 := Zx.L1) hTP.vs.ksb_fit hTP.vs.ksb_al hhi
  refine ⟨⟨hA.2, hA.1, B.vobj_nu hw.1⟩, fun lo hlo h0 => ?_⟩
  have h0' : L.mem s (atAF K.ksb hi) ≠ 0#u64 := by rw [← hk]; exact h0
  have hP := B.pool hi hhi h0' lo hlo
  rw [← hk] at hP
  have hpP := B.j.xtop.fin.2.1.tmem hi hhi h0
  have hpw := Fl4Proofs.P3.Vs.pool_vobj (th := Zx.th) (L4 := Zx.L4) (L3 := Zx.L3) (L2 := Zx.L2) (L1 := Zx.L1)
    (ksb := L.ksb s) hpP (hTP.vs.pal _ hpP).1 (hTP.vs.pal _ hpP).2 hlo
  exact ⟨hP.1, hP.2, B.vobj_nu hpw.1⟩

/-- **`VsRd` at a bundle state**, for a user address. -/
theorem SlJAtZ.vsRd (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) (asid va : U64)
    (hv : Fl4Proofs.P3.Vs.UserV va) : VsRd st K s asid va := by
  obtain ⟨hSR, hVs, hPt, hPI, -⟩ := B.j.xtop.fin
  have hTP := hSR.2
  refine ⟨vspace.find_vspace_for_asid.guard s asid B.rdTab, fun root hroot => ?_⟩
  obtain ⟨r, hr, hL4⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.find_vspace_for_asid_L4 (st := st) s σ hVs hPI asid)
  rw [hr] at hroot
  have hrm : root ∈ Zx.L4 := hL4 root (ok_inj_ff hroot)
  refine vsj_pt_guard s root va (B.tabVsW (Or.inl hrm) (Fl4Proofs.P3.Vs.vIdx_lt _ _)) (fun y hy => ?_)
    (fun y hy => ?_)
  · obtain ⟨r2, hr2, -, hsl, -⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.lookup_pdpt_slot_rel s σ hPt hTP.pt hrm va hv)
    rw [hr2] at hy
    obtain ⟨q, hq, e⟩ := hsl y (ok_inj_ff hy)
    rw [e]
    exact B.tabVsW (Or.inr (Or.inl hq)) (Fl4Proofs.P3.Vs.vIdx_lt _ _)
  · obtain ⟨r2, hr2, -, hsl, -⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.lookup_pd_slot_rel s σ hPt hTP.pt hrm va hv)
    rw [hr2] at hy
    obtain ⟨q, hq, e⟩ := hsl y (ok_inj_ff hy)
    rw [e]
    exact B.tabVsW (Or.inr (Or.inr (Or.inl hq))) (Fl4Proofs.P3.Vs.vIdx_lt _ _)

/-- **`small_page_entry` never names address 0** at a bundle state (module docstring). -/
theorem SlJAtZ.spe_ne0 (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) (asid va : U64) :
    localinv.small_page_entry st s asid va ≠ ok (some 0#u64) := by
  obtain ⟨hSR, hVs, hPt, hPI, -⟩ := B.j.xtop.fin
  have hTP := hSR.2
  intro hc
  unfold localinv.small_page_entry at hc
  obtain ⟨r, hr, hL4⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.find_vspace_for_asid_L4 (st := st) s σ hVs hPI asid)
  rw [hr] at hc
  cases r with
  | Err e =>
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual] at hc
    exact absurd (ok_inj_ff hc) (by simp)
  | Ok root =>
    have hroot := hL4 root rfl
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok] at hc
    unfold localinv.page_entry at hc
    by_cases hu : va > fl4_abi.consts.USER_TOP
    · rw [if_pos hu] at hc
      exact absurd (ok_inj_ff hc) (by simp)
    · rw [if_neg hu] at hc
      have hv : Fl4Proofs.P3.Vs.UserV va := by
        unfold Fl4Proofs.P3.Vs.UserV
        have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
        have : ¬ fl4_abi.consts.USER_TOP.val < va.val := hu
        omega
      unfold vspace.small_page_entry at hc
      obtain ⟨r2, hr2, -, hsl, -⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.lookup_pt_slot_rel s σ hPt hTP.pt hroot va hv)
      rw [hr2] at hc
      simp only [bind_ok] at hc
      cases r2 with
      | Err e =>
        simp only [core.result.Result.ok] at hc
        exact absurd (ok_inj_ff hc) (by simp)
      | Ok x =>
        simp only [core.result.Result.ok] at hc
        have ex : x = 0#u64 := Option.some.inj (ok_inj_ff hc)
        obtain ⟨q, hq, e⟩ := hsl x rfl
        obtain ⟨f, hf, -⟩ := hPt.l1 q hq
        obtain ⟨n, -, hH⟩ := B.j.cover.arch _ _ hf
        have hq0 : q ≠ 0#u64 := by
          intro e0
          have h0 := B.j.kern.h0
          have hH' : K.heap q = some (.other n) := hH
          rw [e0, h0] at hH'
          cases hH'
        have hal := hTP.pt q (Or.inr (Or.inr (Or.inr hq)))
        have hb := q.hBounds
        have hfit : q.val + 4096 ≤ 2 ^ 64 := by simp only [UScalarTy.numBits] at hb; omega
        have hv' := Fl4Proofs.P3.Vs.peA_val hfit (Fl4Proofs.P3.Vs.vIdx_lt va 12)
        have hqv : q.val ≠ 0 := fun h => hq0 (UScalar.eq_of_val_eq (by simpa using h))
        have hx : x.val = 0 := by rw [ex]; rfl
        rw [e, hv'] at hx
        omega

end words

/-! ## `InvVsJ` -/

section inv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (invj gen 1) **`InvVsJ` discharged** for every `P` implying `SlJAt K` (module docstring). No premise. -/
theorem invVsJ_of {K : KLayout} {P : S → Prop} (hP : ∀ s, P s → SlJAt (L := L) K s) : InvVsJ st K P := by
  intro s sl fp rt asid va hs hsl hc _
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hP s hs
  have hsl' : Fl4Proofs.P3.IsSlot Zx.th sl := by rw [B.slots] at hsl; exact hsl
  have hcv := Fl4Proofs.P3.capV_of_capAt (mem := L.mem s) (a := sl)
    (by rw [← Fl4Proofs.P3.slot_cap_eq (st := st) sl s]; exact hc)
  have h := B.j.vsc _ hsl'
  rw [hcv] at h
  have h' : (true = true → asid ≠ 0#u64) ∧ Fl4Proofs.P3.Vs.PaM fp (Fl4Proofs.P3.Vs.frameMaskOf .Small) ∧
      (true = true → Fl4Proofs.P3.Vs.UserV va) := h
  have hu := h'.2.2 rfl
  refine ⟨?_, B.spe_ne0 asid va, B.vsRd asid va hu⟩
  have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
  show va.val ≤ fl4_abi.consts.USER_TOP.val
  rw [hU]
  exact hu

end inv

end Fl4Proofs.P2.PathObl
