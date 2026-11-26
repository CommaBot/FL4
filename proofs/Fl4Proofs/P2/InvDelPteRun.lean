/-
# P2 (line invj, generation 4): the leaf `unmap_page` of the CNodeDelete **PTE arm**

At the decode state the frame finalisation runs `vspace.unmap_page … .Small asid va fp`. Its ASID / page-table walk
reads only gate-owned words (`VsW`), unchanged since the entry (InvVs's `*.trV` transfers), so it finds the same
leaf `e` the plan locked (`small_page_entry st s asid va = some e`). Then:

* `unmapLeaf`: the tail of `unmap_page` from the leaf on (read `e`; if present and naming the frame, write `e := 0`
  and `invalidate_page`), stated for any store;
* **`unmap_pte`**: `unmap_page` on a store `m'` at `x'` reading the walk's words as `st` at `s` is `unmapLeaf` at `e`;
* **`unmapLeaf.guard`**: on a store answering `e`'s read / write and the frame masks as `st`, `unmapLeaf` is `st`'s;
* **`unmapLeaf_st`**: on `st` the result state is the decode state or that state with `e := 0`, and the Arch state is
  either unchanged or `invalidate_page`'s.

No named premise. No existing statement changes.
-/
import Fl4Proofs.P2.InvDelPteEnt
import Fl4Proofs.P2.InvVsJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout)

section leaf
variable {S : Type} {A : Type}

/-- The leaf part of `unmap_page` (module docstring). -/
def unmapLeaf (m : machine.Store S) (ar : machine.Arch A) (x : S) (a : A) (e asid va fp : U64) : Result (S × A) := do
  let v ← m.read x e
  let i ← vspace.P_PRESENT
  let i1 ← lift (v &&& i)
  if i1 = 0#u64 then ok (x, a)
  else
    let i2 ← vspace.frame_base v capability.FrameSize.Small
    let i3 ← vspace.frame_gpa m x i2
    if i3 != core.num.U64.wrapping_sub fp layout.PPTR_BASE then ok (x, a)
    else
      let s1 ← m.write x e 0#u64
      let a1 ← ar.invalidate_page a asid va
      ok (s1, a1)

end leaf

section run
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- (invj gen 4) **`unmap_page` of a mapped frame whose leaf the plan found** (module docstring). -/
theorem unmap_pte {K : KLayout} {m' : machine.Store S} {x' s : S} {asid va fp e : U64}
    (hr : ∀ a, VsW K a → m'.read x' a = st.read s a) (hk : m'.ks_base x' = st.ks_base s)
    (hV : VsRd st K s asid va) (hva : va ≤ fl4_abi.consts.USER_TOP)
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

/-- **`unmapLeaf` on a store answering the leaf's read / write and the frame masks as `st`.** -/
theorem unmapLeaf.guard {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (x : S) (a : A) {e : U64} (asid va fp : U64) (hR : R e) (hW : W e) :
    unmapLeaf gS ar x a e asid va fp = unmapLeaf st ar x a e asid va fp := by
  unfold unmapLeaf vspace.frame_gpa
  rw [gst_read hR, gst_frame_masks]
  simp only [gst_write hW]

/-- **What `unmapLeaf` does on `st`**: the state is kept or gets `e := 0`; the Arch state is kept or
`invalidate_page`'s. -/
theorem unmapLeaf_st {x y : S} {a a' : A} {e asid va fp : U64}
    (h : unmapLeaf st ar x a e asid va fp = ok (y, a')) :
    (y = x ∧ a' = a) ∨ (y = L.wr x e 0#u64 ∧ ar.invalidate_page a asid va = ok a') := by
  unfold unmapLeaf at h
  rw [L.read_eq] at h
  simp only [bind_ok] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  simp only [lift, bind_ok] at h
  by_cases h0 : (L.mem x e &&& i) = 0#u64
  · rw [if_pos h0] at h
    have e1 := ok_inj_ff h
    simp only [Prod.mk.injEq] at e1
    exact Or.inl ⟨e1.1.symm, e1.2.symm⟩
  · rw [if_neg h0] at h
    obtain ⟨i2, -, h⟩ := bind_eq_ok h
    obtain ⟨i3, -, h⟩ := bind_eq_ok h
    by_cases h1 : (i3 != core.num.U64.wrapping_sub fp layout.PPTR_BASE) = true
    · rw [if_pos h1] at h
      have e1 := ok_inj_ff h
      simp only [Prod.mk.injEq] at e1
      exact Or.inl ⟨e1.1.symm, e1.2.symm⟩
    · rw [if_neg h1] at h
      rw [L.write_eq] at h
      simp only [bind_ok] at h
      obtain ⟨a1, ea1, h⟩ := bind_eq_ok h
      have e1 := ok_inj_ff h
      simp only [Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      exact Or.inr ⟨rfl, ea1⟩

end run

end Fl4Proofs.P2.PathObl
