/-
# P2 (line invj, generation 6): the Delete PTE arm's walk reads no leaf entry (`VsRdG`, `SlJAtZ.vsRdX`)

gen 4's `unmap_pte` asks `VsRd` (InvVs): the ASID / page-table walk runs alike on the store guarded to `VsW K`, the
aligned, region-less, non-user words. Under pte's rule 8 (`ownP`) the leaf page-table entries `K.ptes` are region
`.none` too, but `lock b`'s, so a local path may read only the leaf it locked. This module sharpens the walk's read
set to the `VsW` words **off** any set `X` of leaf entries (`X ⊆ PtW Zx.L1`, e.g. `K.ptes` under pte's conventions,
`ptesR_sub`):

* **`VsRdG st V s asid va`**: `VsRd` for any word set `V`; **`unmap_pteG`**: `unmap_pte` for it (same proof, the
  InvVs `*.trV` transfers are stated for any `V`);
* **`SlJAtZ.vsRdX`**: at every bundle state, for a user address, `VsRdG st (VsW K ∧ ¬ X)` — the walk reads the
  ASID-table words and the named pools' words (`SlJAtZ.rdTab`; no leaf entry: `TopPlaced.pv`) and the entries of
  `L4` / `L3` / `L2` tables (`SlJAtZ.tabVsW`; no leaf entry: `ptw_up_ne`, a table is of one level). So **no leaf
  entry is ever read by the walk**: a proof, not an assumption.
* `IoRSX K Locks X e s`: `IoRS` minus every `X` word other than `e` (IoRS unchanged); `IoRSX.of`.

No named premise. New module; no existing statement changes; no `kernel_entry_reach*` touched.
-/
import Fl4Proofs.P2.InvDelPteR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region)
open Fl4Proofs.P3.Vs (PtW PtWAll peA UserV)

section g
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- **`VsRd` for any word set `V`**: the walk at `s` runs alike on the store guarded to `V`. -/
def VsRdG (V : U64 → Prop) (s : S) (asid va : U64) : Prop :=
  vspace.find_vspace_for_asid (PathObl.guard st V (fun _ => False)) s asid = vspace.find_vspace_for_asid st s asid ∧
    ∀ root, vspace.find_vspace_for_asid st s asid = ok (.Ok root) →
      vspace.lookup_pt_slot (PathObl.guard st V (fun _ => False)) s root va = vspace.lookup_pt_slot st s root va

variable (st) in
/-- `IoRS` minus every word of `X` other than `e` (`IoRS` itself unchanged). -/
def IoRSX (K : KLayout) (Locks : S → U64 → Prop) (X : U64 → Prop) (e : U64) (s : S) (b : U64) : Prop :=
  IoRS (st := st) K Locks s b ∧ (X b → b = e)

theorem IoRSX.of {K : KLayout} {Locks : S → U64 → Prop} {X : U64 → Prop} {e : U64} {s : S} {b : U64}
    (h : IoRS (st := st) K Locks s b) (hx : ¬ X b) : IoRSX st K Locks X e s b :=
  ⟨h, fun h' => absurd h' hx⟩

end g

section run
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- (invj gen 6) **`unmap_pte` for any walk read set `V`** (module docstring). -/
theorem unmap_pteG {V : U64 → Prop} {m' : machine.Store S} {x' s : S} {asid va fp e : U64}
    (hr : ∀ a, V a → m'.read x' a = st.read s a) (hk : m'.ks_base x' = st.ks_base s)
    (hV : VsRdG st V s asid va) (hva : va ≤ fl4_abi.consts.USER_TOP)
    (he : localinv.small_page_entry st s asid va = ok (some e)) (a : A) :
    vspace.unmap_page m' ar x' a .Small asid va fp = unmapLeaf m' ar x' a e asid va fp := by
  unfold localinv.small_page_entry at he
  obtain ⟨r, er, he⟩ := bind_eq_ok he
  have er' : vspace.find_vspace_for_asid m' x' asid = ok r :=
    vspace.find_vspace_for_asid.trV hr hk (by rw [hV.1]; exact er)
  cases r with
  | Err e0 =>
    simp only [core.result.Result.ok, bind_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual] at he
    exact absurd (ok_inj_ff he) (by simp)
  | Ok root =>
    simp only [core.result.Result.ok, bind_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch] at he
    unfold localinv.page_entry at he
    have hnt : ¬ va > fl4_abi.consts.USER_TOP := by
      intro hg; exact absurd hva (not_le.mpr hg)
    rw [if_neg hnt] at he
    unfold vspace.small_page_entry at he
    obtain ⟨r2, er2, he⟩ := bind_eq_ok he
    cases r2 with
    | Err e2 =>
      simp only [core.result.Result.ok] at he
      exact absurd (ok_inj_ff he) (by simp)
    | Ok x =>
      simp only [core.result.Result.ok] at he
      have hx : x = e := Option.some.inj (ok_inj_ff he)
      subst hx
      have er2' : vspace.lookup_pt_slot m' x' root va = ok (.Ok x) :=
        vspace.lookup_pt_slot.trV hr (by rw [hV.2 root er]; exact er2)
      unfold vspace.unmap_page unmapLeaf
      simp only [er', er2', layout.paddr, bind_ok, not_true_eq_false, ↓reduceIte]

end run

section words
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit} {X : U64 → Prop}

theorem ptw_all_of {L4 L3 L2 L1 : Set U64} {b : U64} (h : PtW L1 b) : PtWAll L4 L3 L2 L1 b := by
  obtain ⟨q, hq, i, hi, rfl⟩ := h
  exact ⟨q, Or.inr (Or.inr (Or.inr hq)), i, hi, rfl⟩

/-- **An upper-level entry is no leaf entry of `X`.** -/
theorem SlJAtZ.notX_up (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) (hsub : ∀ b, X b → PtW Zx.L1 b)
    {q i : U64} (hq : q ∈ Zx.L4 ∨ q ∈ Zx.L3 ∨ q ∈ Zx.L2) (hi : i.val < 512) : ¬ X (peA q i) := by
  intro hx
  have hTP := B.j.xtop.fin.1.2
  have hPR := B.j.xtop.fin.2.2.1
  obtain ⟨q', hq', j, hj, he⟩ := hsub _ hx
  exact ptw_up_ne hPR hTP.pt hq' hq hj hi he.symm

theorem SlJAtZ.gw_up (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) (hsub : ∀ b, X b → PtW Zx.L1 b)
    {q i : U64} (hq : q ∈ Zx.L4 ∨ q ∈ Zx.L3 ∨ q ∈ Zx.L2) (hi : i.val < 512) :
    VsW K (peA q i) ∧ ¬ X (peA q i) :=
  ⟨B.tabVsW (up_all (L1 := Zx.L1) hq) hi, B.notX_up hsub hq hi⟩

/-- **The ASID-table and pool words are `VsW` words and no leaf entry of `X`.** -/
theorem SlJAtZ.rdTabX (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) (hsub : ∀ b, X b → PtW Zx.L1 b) :
    RdTab (L := L) (fun b => VsW K b ∧ ¬ X b) s := by
  have hTP := B.j.xtop.fin.1.2
  have hR := B.rdTab
  intro hi hhi
  refine ⟨⟨(hR hi hhi).1, fun hx => hTP.pv _ (ptw_all_of (hsub _ hx)) (Or.inl ⟨hi, hhi, rfl⟩)⟩,
    fun lo hlo h0 => ⟨(hR hi hhi).2 lo hlo h0, fun hx => ?_⟩⟩
  have hpP := B.j.xtop.fin.2.1.tmem hi hhi h0
  exact hTP.pv _ (ptw_all_of (hsub _ hx)) (Or.inr ⟨_, hpP, lo, hlo, rfl⟩)

/-- (invj gen 6) **The walk at a bundle state reads only `VsW` words off `X`**, for a user address (module
docstring). No premise. -/
theorem SlJAtZ.vsRdX (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) (hsub : ∀ b, X b → PtW Zx.L1 b)
    (asid va : U64) (hv : UserV va) : VsRdG st (fun b => VsW K b ∧ ¬ X b) s asid va := by
  obtain ⟨hSR, hVs, hPt, hPI, -⟩ := B.j.xtop.fin
  have hTP := hSR.2
  refine ⟨vspace.find_vspace_for_asid.guard s asid (B.rdTabX hsub), fun root hroot => ?_⟩
  obtain ⟨r, hr, hL4⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.find_vspace_for_asid_L4 (st := st) s σ hVs hPI asid)
  rw [hr] at hroot
  have hrm : root ∈ Zx.L4 := hL4 root (ok_inj_ff hroot)
  refine vsj_pt_guard s root va (B.gw_up hsub (Or.inl hrm) (Fl4Proofs.P3.Vs.vIdx_lt _ _)) (fun y hy => ?_)
    (fun y hy => ?_)
  · obtain ⟨r2, hr2, -, hsl, -⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.lookup_pdpt_slot_rel s σ hPt hTP.pt hrm va hv)
    rw [hr2] at hy
    obtain ⟨q, hq, e⟩ := hsl y (ok_inj_ff hy)
    rw [e]
    exact B.gw_up hsub (Or.inr (Or.inl hq)) (Fl4Proofs.P3.Vs.vIdx_lt _ _)
  · obtain ⟨r2, hr2, -, hsl, -⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.lookup_pd_slot_rel s σ hPt hTP.pt hrm va hv)
    rw [hr2] at hy
    obtain ⟨q, hq, e⟩ := hsl y (ok_inj_ff hy)
    rw [e]
    exact B.gw_up hsub (Or.inr (Or.inr hq)) (Fl4Proofs.P3.Vs.vIdx_lt _ _)

end words

end Fl4Proofs.P2.PathObl
