/-
# P2 (line p3mc, gen 8): the narrowed annotation of a translated body vs the translation with the smaller read set

U9 arms `annV k0 = narrowSP cls kt c Q ∅ k0` (`P2/E2EPU9.lean`) where `k0 = tr R User cls kv c … p ∅ a` is a
translated body (`E2E.tr`) annotated with the read set `R` and the class owner `kv` (the path's, at the view).
**`safe_narrow_tr`**: `annV`'s body is `Safe` wherever the translation **with the read set `R ∧ Q` and the class owner
`kt`** (the target's) is: node by node, a read the translation with `R ∧ Q` makes plain is plain in the
re-annotation, a class read there is a class read or a speculative read here (the latter only where `kv` is neither
the gate nor `c`), and a speculative read there is one here (`narrow_rdN`). So a proof of `VSafe9` may certify
`tr (R ∧ Q) … kt` instead, with no reference to the view's class owner `kv`.

Helpers: `safe_rd_cont`, `safe_rdc_cont`, `safe_rds_cont`, `safe_rds_of_rdc` (a read node's `Safe` with a weaker
continuation, or a class read weakened to a speculative one).

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.E2E
import Fl4Proofs.P2.NarrowSP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner Prog Safe FReach narrowSP)

noncomputable section
open Classical

section
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {kv kt : U64 → ClsOwner U64} {c : U64} {hs : U64 → Prop} {R Q User : U64 → Prop}

theorem safe_rd_cont {μ : U64 → U64} {q : U64} {k k' : U64 → SP}
    (hk : ∀ v μ, Safe own cls kt c hs μ (k' v) → Safe own cls kt c hs μ (k v))
    (h : Safe own cls kt c hs μ (.rd q k')) : Safe own cls kt c hs μ (.rd q k) := by
  cases h with
  | rd h1 h2 => exact .rd h1 fun μ' hR => hk _ _ (h2 μ' hR)

theorem safe_rdc_cont {μ : U64 → U64} {q : U64} {K : U64 → U64 → Prop} {k k' : U64 → SP}
    (hk : ∀ v μ, Safe own cls kt c hs μ (k' v) → Safe own cls kt c hs μ (k v))
    (h : Safe own cls kt c hs μ (.rdc q K k')) : Safe own cls kt c hs μ (.rdc q K k) := by
  cases h with
  | rdc h1 h2 h3 => exact .rdc h1 h2 fun μ' hR => hk _ _ (h3 μ' hR)

theorem safe_rds_cont {μ : U64 → U64} {q : U64} {k k' : U64 → SP}
    (hk : ∀ v μ, Safe own cls kt c hs μ (k' v) → Safe own cls kt c hs μ (k v))
    (h : Safe own cls kt c hs μ (.rds q k')) : Safe own cls kt c hs μ (.rds q k) := by
  cases h with
  | rds h1 => exact .rds fun μ' hR => hk _ _ (h1 μ' hR)

theorem safe_rds_of_rdc {μ : U64 → U64} {q : U64} {K : U64 → U64 → Prop} {k k' : U64 → SP}
    (hk : ∀ v μ, Safe own cls kt c hs μ (k' v) → Safe own cls kt c hs μ (k v))
    (h : Safe own cls kt c hs μ (.rdc q K k')) : Safe own cls kt c hs μ (.rds q k) := by
  cases h with
  | rdc _ _ h3 => exact .rds fun μ' hR => hk _ _ (h3 μ' hR)

/-- **One translated read**: the re-annotation of `rdN` with `R` and `kv` is `Safe` where `rdN` with `R ∧ Q` and `kt`
is, given the same for the continuations. -/
theorem narrow_rdN {Wd : Set U64} {q : U64} {K0 K' : U64 → SP} {μ : U64 → U64}
    (hk : ∀ v μ, Safe own cls kt c hs μ (K' v) → Safe own cls kt c hs μ (narrowSP cls kt c Q Wd (K0 v)))
    (h : Safe own cls kt c hs μ (rdN (fun x => R x ∧ Q x) User cls kt c Wd q K')) :
    Safe own cls kt c hs μ (narrowSP cls kt c Q Wd (rdN R User cls kv c Wd q K0)) := by
  unfold rdN Racy at h ⊢
  by_cases hA : ¬ User q ∧ (R q ∨ q ∈ Wd)
  · rw [if_pos (not_not_intro hA)]
    simp only [narrowSP]
    by_cases hB : Q q ∨ q ∈ Wd
    · have hA' : ¬ User q ∧ ((R q ∧ Q q) ∨ q ∈ Wd) := by
        refine ⟨hA.1, ?_⟩
        by_cases hw : q ∈ Wd
        · exact Or.inr hw
        · exact Or.inl ⟨hA.2.resolve_right hw, hB.resolve_right hw⟩
      rw [if_pos (not_not_intro hA')] at h
      rw [if_pos hB]
      exact safe_rd_cont hk h
    · have hn : ¬ ¬ ¬ (¬ User q ∧ ((R q ∧ Q q) ∨ q ∈ Wd)) := fun hh => hh fun hx =>
        hx.2.elim (fun h3 => hB (Or.inl h3.2)) (fun h3 => hB (Or.inr h3))
      rw [if_neg hn] at h
      rw [if_neg hB]
      by_cases h3 : kt q = .gate ∨ kt q = .core c
      · rw [if_pos h3]
        rw [if_pos ⟨hA.1, h3⟩] at h
        exact safe_rdc_cont hk h
      · rw [if_neg h3]
        rw [if_neg (fun hh => h3 hh.2)] at h
        exact safe_rds_cont hk h
  · rw [if_neg (fun hh => hh hA)]
    have hn : ¬ ¬ ¬ (¬ User q ∧ ((R q ∧ Q q) ∨ q ∈ Wd)) := fun hh => hh fun hx =>
      hA ⟨hx.1, hx.2.imp_left And.left⟩
    rw [if_neg hn] at h
    by_cases h2 : ¬ User q ∧ (kv q = .gate ∨ kv q = .core c)
    · rw [if_pos h2]
      simp only [narrowSP]
      by_cases h3 : kt q = .gate ∨ kt q = .core c
      · rw [if_pos h3]
        rw [if_pos ⟨h2.1, h3⟩] at h
        exact safe_rdc_cont hk h
      · rw [if_neg h3]
        rw [if_neg (fun hh => h3 hh.2)] at h
        exact safe_rds_cont hk h
    · rw [if_neg h2]
      simp only [narrowSP]
      by_cases h3 : ¬ User q ∧ (kt q = .gate ∨ kt q = .core c)
      · rw [if_pos h3] at h
        exact safe_rds_of_rdc hk h
      · rw [if_neg h3] at h
        exact safe_rds_cont hk h

/-- **The re-annotated translation is `Safe` where the translation with `R ∧ Q` and `kt` is** (module docstring). -/
theorem safe_narrow_tr {kb : U64} {mk : U64 × U64} {A X : Type} (ar : machine.Arch A) (p : SProg X) :
    ∀ (Wd : Set U64) (a : A) (μ : U64 → U64),
      Safe own cls kt c hs μ (tr (fun x => R x ∧ Q x) User cls kt c kb mk ar p Wd a) →
      Safe own cls kt c hs μ (narrowSP cls kt c Q Wd (tr R User cls kv c kb mk ar p Wd a)) := by
  induction p with
  | ret x => intro Wd a μ _; simp only [tr, narrowSP]; exact .done
  | err e => intro Wd a μ _; simp only [tr, narrowSP]; exact .done
  | zero q n k _ => intro Wd a μ _; simp only [tr, narrowSP]; exact .done
  | clr q n k _ => intro Wd a μ _; simp only [tr, narrowSP]; exact .done
  | rd q k ih =>
    intro Wd a μ h
    simp only [tr] at h ⊢
    exact narrow_rdN (fun v μ h' => ih v Wd a μ h') h
  | rdp q k ih =>
    intro Wd a μ h
    simp only [tr] at h ⊢
    exact narrow_rdN (fun v μ1 h1 => narrow_rdN (fun w μ2 h2 => ih (v, w) Wd a μ2 h2) h1) h
  | wr q v k ih =>
    intro Wd a μ h
    simp only [tr] at h ⊢
    by_cases hu : User q
    · rw [if_pos hu] at h ⊢
      exact ih Wd a μ h
    · rw [if_neg hu] at h ⊢
      simp only [narrowSP]
      cases h with
      | wr h1 h2 h3 h4 => exact .wr h1 h2 h3 fun μ' hR => ih _ a _ (h4 μ' hR)
  | ksb k ih => intro Wd a μ h; simp only [tr] at h ⊢; exact ih kb Wd a μ h
  | cpu k ih => intro Wd a μ h; simp only [tr] at h ⊢; exact ih c Wd a μ h
  | masks k ih => intro Wd a μ h; simp only [tr] at h ⊢; exact ih mk Wd a μ h
  | arch op k ih =>
    intro Wd a μ h
    simp only [tr] at h ⊢
    by_cases hca : ∃ r, callArch ar op a = ok r
    · rw [dif_pos hca] at h ⊢
      exact ih _ Wd _ μ h
    · rw [dif_neg hca]
      simp only [narrowSP]
      exact .done

end

end
end Fl4Proofs.P2.E2E
