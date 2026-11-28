/-
# P2 (line p3mc, gen 51): `InsV15V` at every CNodeDelete and every PTE-delete start

The CNodeDelete / PTE-delete certificates `inv_del_annA` / `inv_pte_annA` (U26 / U28) read upper paging words
(`unmap_page`'s walk, and for PTE delete the locked leaf), so the `RTK` cut of gen 50 does not apply (handoff §55d).
Their `InsA` twins take gen 46's `PathObl.insA_narrow_tr_wrU` **with** `InsT`, the route §55d laid out:

* **`E2E.insT_agree`** (generic): `InsT` moves between two states agreeing on the words the run reads (and on the
  kernel base, the core, the masks), along a run inside a read / write set (induction on `SProg`, as
  `interp_agree_gd`).
* **`del_insT_view`** / **`pte_insT_view`**: at a view start (`σ'` of gen 51's oracle splits `del_hgoX` /
  `pte_hgoX`, P2/InvDelAnnA / P2/InvDelPteAnnA) the run is `InsT (PWE K E) ADEq NotPresent`: `QPs (KU K E)` by
  gen 48's `qPs_ku_of` (the ASID table words of the view are `E`'s, `atAF_view`); accepted runs by mmuAD's
  `accIns_invR` / `accIns_delR` (P2/E2EPU3f, used read-only); declined runs by `inv_dec` / `delPte_dec` (they touch no
  paging word) and `insT_of_within`.
* **`inv_del_insA`** / **`inv_pte_insA`**: U26's / U28's armed programs are `InsA (PWE K E)` at a view start:
  `insA_narrow_tr_wrU` on the oracle of `del_hgoX` / `pte_hgoX`, whose `InsT` is `del_insT_view` / `pte_insT_view` at
  `σ'` moved to the oracle state by `insT_agree`.
* glue **`del_insA_annV`** / **`pte_insA_annV`** (as `inv_annV_delA` / `inv_annV_pteA`), `DelPm`, `PtePm`,
  **`insAP_del_view`**, **`insAP_pte_view`** (`InsV15V`'s obligation of `nativePmKAD B` at every CNodeDelete /
  PTE-delete start without a VCPU).

## The open set and the top
* `Open53 s K c ρ k0 i := Open52 … ∧ ¬ DelPm i ∧ ¬ PtePm i` (only the PageMap starts `.inr _` remain).
* **`insV15NOV53_of_52`** (`Open53 ⊆ Open52`), **`insV15NOV52_of_53`** (at the CNodeDelete / PTE-delete starts by
  `insAP_del_view` / `insAP_pte_view`): equivalent for `nativePmKAD B`.
* **`serializable_fl4_V15_pmKADD`** (authoritative): `serializable_fl4_V15_pmKADO` with `InsV15NOV … Open53` [J] for
  `InsV15NOV … Open52` [J], all other premises unchanged; **`serializable_fl4_V15_pmKADOofD`**: the previous statement
  from it.

Named premises: `InsV15NOV … Open53` [J] (replaces `InsV15NOV … Open52` [J]; justification as `InsV15` [J],
P2/E2EPV15AD). New module; existing files touched: P2/InvDelAnnA, P2/InvDelPteAnnA (in-place splits, every existing
statement byte-identical).

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `insV15NOV53_of_52`,
`serializable_fl4_V15_pmKADD`, `serializable_fl4_V15_pmKADOofD`.
-/
import Fl4Proofs.P2.InsV15Io
import Fl4Proofs.P2.InvDelPteAnnA
import Fl4Proofs.P2.E2EPU3f
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl

noncomputable section
open Classical

section agree
variable {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
  {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop} {User : U64 → Prop}

/-- **`InsT` moves between states agreeing on the run's reads** (module docstring). -/
theorem insT_agree (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s) {R W : U64 → Prop}
    (hRal : ∀ w, R w → Aligned w) (hWal : ∀ w, W w → Aligned w) (p : SProg X) :
    ∀ (s s' : S) (a : A), Within st ar R W p s a → L.ksb s' = L.ksb s → L.cpu s' = L.cpu s →
      st.frame_masks s' = st.frame_masks s → (∀ w, R w → L.mem s' w = L.mem s w) →
      InsT st ar G Q NP User p s a → InsT st ar G Q NP User p s' a := by
  induction p with
  | ret x => intros; trivial
  | err e => intros; trivial
  | zero q n k ih => intros; trivial
  | clr q n k ih => intros; trivial
  | rd q k ih =>
    intro s s' a hW e1 e2 e3 e4 h
    simp only [Within] at hW
    simp only [InsT] at h ⊢
    intro v hv
    have hv0 : st.read s q = ok v := by
      rw [L.read_eq] at hv ⊢; rw [← e4 q hW.1]; exact hv
    exact ⟨(h v hv0).1, ih v s s' a (hW.2 v hv0) e1 e2 e3 e4 (h v hv0).2⟩
  | rdp q k ih =>
    intro s s' a hW e1 e2 e3 e4 h
    simp only [Within] at hW
    simp only [InsT] at h ⊢
    refine ⟨h.1, h.2.1, fun v hv => ?_⟩
    have hv0 : st.read_pair s q = ok v := by
      rw [L.read_pair_eq] at hv ⊢; rw [← e4 q hW.1, ← e4 _ hW.2.1]; exact hv
    exact ih v s s' a (hW.2.2 v hv0) e1 e2 e3 e4 (h.2.2 v hv0)
  | wr q v k ih =>
    intro s s' a hW e1 e2 e3 e4 h
    simp only [Within] at hW
    simp only [InsT] at h ⊢
    refine ⟨h.1, fun s1 hs1 => ?_⟩
    rw [L.write_eq] at hs1
    obtain rfl := Result.ok_injective hs1
    have ha := hWal q hW.1
    exact ih (L.wr s q v) (L.wr s' q v) a (hW.2 _ (L.write_eq s q v)) (by rw [L.ksb_wr, L.ksb_wr, e1])
      (by rw [L.cpu_wr, L.cpu_wr, e2]) (by rw [hm, hm, e3])
      (fun w hw => by rw [L.mem_wr _ _ _ _ ha (hRal w hw), L.mem_wr _ _ _ _ ha (hRal w hw), e4 w hw])
      (h.2 _ (L.write_eq s q v))
  | ksb k ih =>
    intro s s' a hW e1 e2 e3 e4 h
    simp only [Within] at hW
    simp only [InsT] at h ⊢
    intro v hv
    have hv0 : st.ks_base s = ok v := by
      rw [L.ks_base_eq] at hv ⊢; rw [← e1]; exact hv
    exact ih v s s' a (hW v hv0) e1 e2 e3 e4 (h v hv0)
  | cpu k ih =>
    intro s s' a hW e1 e2 e3 e4 h
    simp only [Within] at hW
    simp only [InsT] at h ⊢
    intro v hv
    have hv0 : st.cur_cpu s = ok v := by
      rw [L.cur_cpu_eq] at hv ⊢; rw [← e2]; exact hv
    exact ih v s s' a (hW v hv0) e1 e2 e3 e4 (h v hv0)
  | masks k ih =>
    intro s s' a hW e1 e2 e3 e4 h
    simp only [Within] at hW
    simp only [InsT] at h ⊢
    intro v hv
    have hv0 : st.frame_masks s = ok v := by rw [← e3]; exact hv
    exact ih v s s' a (hW v hv0) e1 e2 e3 e4 (h v hv0)
  | arch op k ih =>
    intro s s' a hW e1 e2 e3 e4 h
    simp only [Within] at hW
    simp only [InsT] at h ⊢
    exact fun v a' hv => ih v s s' a' (hW v a' hv) e1 e2 e3 e4 (h v a' hv)

end agree

end
end Fl4Proofs.P2.E2E

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath tr masksOf InsT insT_of_within)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll VEq Safe InsA InsAP insAP_of_insA narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN vn_of_nf nf_none)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The CNodeDelete run at a view start is `InsT` at the epoch's paging words** (module docstring). -/
theorem del_insT_view (hA : P0.ArchTotal ar) (j : InvArg S) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {m E : U64 → U64} (h : InvPremW st j K.toKLayoutV m) (hcv : K.ptes = ptesR K E) {σ : S} (a : A)
    (hJ : SlJAt (L := L) K.toKLayout σ) (hq : InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m σ)
    (hqu : QU st K σ) (hT : ∀ hi : U64, hi.val < 2048 → L.mem σ (atAF K.ksb hi) = E (atAF K.ksb hi)) :
    InsT st ar (PWE K E) ADEq NotPresent (· ∈ K.user) (R.invBodyG j.number j.p) σ a := by
  have hqK : QPs (KU K E) st σ := qPs_ku_of hcv hqu.1 hT
  obtain ⟨r, hr⟩ := inv_total (st := st) hA j.number j.p σ a
  by_cases hacc : r.1 = true
  · exact accIns_invR st ar hA (masksWr_plain st) j (E := E) hK hU h σ a r ⟨⟨⟨hJ, hq⟩, hqu⟩, hqK⟩ hr hacc
  · exact insT_of_within _ σ a (inv_dec st ar hA (masksWr_plain st) j (E := E) hK hU h σ σ a r ⟨⟨hJ, hq⟩, hqu⟩ hr
      hacc (Alt.refl (L := L) σ))

set_option maxHeartbeats 4000000 in
/-- **The PTE-delete run at a view start is `InsT` at the epoch's paging words** (module docstring). -/
theorem pte_insT_view (hA : P0.ArchTotal ar) (j : InvArg S) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {m E : U64 → U64} (h : DelPtePrem st j K) (hcv : K.ptes = ptesR K E) {σ : S} (a : A)
    (hP : PreP st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m σ) (hqu : QU st K σ)
    (hT : ∀ hi : U64, hi.val < 2048 → L.mem σ (atAF K.ksb hi) = E (atAF K.ksb hi)) :
    InsT st ar (PWE K E) ADEq NotPresent (· ∈ K.user) (R.invBodyG j.number j.p) σ a := by
  have hqK : QPs (KU K E) st σ := qPs_ku_of hcv hqu.1 hT
  obtain ⟨r, hr⟩ := inv_total (st := st) hA j.number j.p σ a
  by_cases hacc : r.1 = true
  · exact accIns_delR st ar hA (masksWr_plain st) j (E := E) (m := m) hK hU h σ a r ⟨hP, hqK⟩ hr hacc
  · exact insT_of_within _ σ a (delPte_dec st ar hA (masksWr_plain st) j (E := E) (m := m) hK hU h σ σ a r hP hr
      hacc (Alt.refl (L := L) σ))

set_option maxHeartbeats 4000000 in
/-- **U26's armed CNodeDelete program is `InsA` at a view start** (module docstring). -/
theorem inv_del_insA (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (j : InvArg S)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64} (h : InvPremW st j K.toKLayoutV (view K.toKLayout c ρ))
    (E : U64 → U64) (hcv : K.ptes = ptesR K E)
    (hTv : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi))
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ) {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (hq : InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout (view K.toKLayout c ρ) σ) (hqu : QU st K σ)
    (hc : L.cpu σ = c) (hl : j.Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    InsA (PWE K E) ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (fun x => InvCMRS (st := st) K.toKLayout j.Locks σ x ∧ ¬ x ∈ K.ptes) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.invBodyG j.number j.p) ∅ a)) := by
  obtain ⟨hWd, hRPO⟩ := cm_own (st := st) (Locks := j.Locks) hK hU h.nv hV hc hl hmm
  have hgoX := del_hgoX ar hA hK hU h.nv hV (number := j.number) (a := a) (h.hCs st) h.lk hJ hq hqu hc hmm
  let Rd : U64 → Prop := fun b => IoRS (st := st) K.toKLayout j.Locks σ b ∧ SR K c ρ b
  have hR0 : ∀ q, Rd q →
      ((InvCMRS (st := st) K.toKLayout j.Locks σ q ∧ ¬ q ∈ K.ptes) ∧ VO K c ρ q) ∧ ¬ q ∈ K.user := fun q hq' =>
    ⟨⟨⟨ioRS_cm hq'.1, hq'.2.2⟩, hq'.2.1.2⟩, hq'.1.2.1⟩
  have hal : ∀ b, Rd b → Aligned b := fun b hb => hb.1.1
  refine PathObl.insA_narrow_tr_wrU (own := ownP K) (cls := OwnMap.cls K.toKLayout)
    (kt := OwnMap.ko K.toKLayout μ) (User := (· ∈ K.user)) ar adEq_equiv (moveHeldP hK) (ownDepP hK hU)
    (masksWr_plain st) (pwe_own hK) (fun x hx => pwe_ko hK μ hx) (fun b hb => pwe_user hU hb) (a := a)
    (R.invBodyG j.number j.p) hc (R0 := fun x => InvCMRS (st := st) K.toKLayout j.Locks σ x ∧ ¬ x ∈ K.ptes)
    (Qv := VO K c ρ) (Rd := Rd) (Ru := PathObl.UserW K.toKLayout)
    (Wd := DelWd K c ρ (IoWS (st := st) K.toKLayout j.Locks σ)) (fun b hb => vo_of_pwe hK hb) hal hR0
    (fun b h => h.1) (fun b h => h.2) hWd hRPO (fun x hx => hV.2.1 x hx) ?_
  intro s h1 h2 h3
  obtain ⟨r, g1, g2, g3, σ', hJ', hq', hqu', hmm', e1, e2, e3, hag, hW⟩ := hgoX s h1 h2 h3
  refine ⟨r, g1, g2, g3, ?_⟩
  have hT' : ∀ hi : U64, hi.val < 2048 → L.mem σ' (atAF K.ksb hi) = E (atAF K.ksb hi) := fun hi hhi => by
    rw [hmm' _ (hqu'.1.al hi hhi) (fun hu => hqu'.1.uoff _ (Or.inl hu) hi hhi rfl)]; exact hTv hi hhi
  exact E2E.insT_agree (masksWr_plain st) (fun b h => h.elim (fun h => h.1.1) (fun h => h.1))
    (fun b h => h.elim (fun h => h.1.1) (fun h => h.1)) _ σ' s a hW e1 e2 e3 hag
    (del_insT_view ar hA j hK hU h hcv a hJ' hq' hqu' hT')

set_option maxHeartbeats 4000000 in
/-- **U28's armed PTE-delete program is `InsA` at a view start** (module docstring). -/
theorem inv_pte_insA (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (j : InvArg S)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64} (h : DelPtePrem st j K)
    (E : U64 → U64) (hcv : K.ptes = ptesR K E)
    (hTv : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi))
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ) {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (hq : InvQFP st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout (view K.toKLayout c ρ) σ) (hqu : QU st K σ)
    (hc : L.cpu σ = c) (hl : j.Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    InsA (PWE K E) ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (InvRSP st K j.Locks σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.invBodyG j.number j.p) ∅ a)) := by
  have nv := h.nv
  have hgoX := pte_hgoX ar hA hK hU nv hV (number := j.number) (a := a) (h.hCs st) h.lk hJ hq hqu hc hmm
  -- the read sets (as `inv_pte_annA`)
  have kPte : ∀ b, b ∈ K.ptes → Aligned b ∧ b ∉ K.user := fun b hb => hU.kern b hb
  have oPte : ∀ b, b ∈ K.ptes → VO K c ρ b := fun b hb => by unfold VO; rw [ownP_pte hb, ownP_pte hb]
  let Rd : U64 → Prop := fun b =>
    (IoRS (st := st) K.toKLayout j.Locks σ b ∧ SR K c ρ b) ∨ PteRd K (j.Locks σ) b
  let Ro : U64 → Prop := fun q => InvRSP st K j.Locks σ q ∧ VO K c ρ q
  have hR0 : ∀ q, Rd q → Ro q ∧ ¬ q ∈ K.user := by
    rintro q (⟨h1, h2⟩ | ⟨hp, hl'⟩)
    · exact ⟨⟨⟨h1.1, Or.inr ⟨h1, fun hp => absurd hp h2.2⟩⟩, h2.1.2⟩, h1.2.1⟩
    · exact ⟨⟨⟨(kPte q hp).1, Or.inr ⟨VsW.ioRS ⟨(kPte q hp).1, hK.none q hp, (kPte q hp).2⟩, fun _ => hl'⟩⟩,
        oPte q hp⟩, (kPte q hp).2⟩
  have hal : ∀ b, Rd b → Aligned b := by
    rintro b (hb | hb)
    · exact hb.1.1
    · exact (kPte b hb.1).1
  let Wd : U64 → Prop := DelWdP K c ρ (IoWS (st := st) K.toKLayout j.Locks σ) (j.Locks σ)
  -- ownership of the read and written words at the physical memory (as `inv_pte_annA`)
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hWd : ∀ x, Wd x → Aligned x ∧ (¬ x ∈ K.user → HeldV c hs (ownP K μ x)) := by
    rintro x ((⟨⟨ha, hw⟩, hp, hvo⟩ | hu) | ⟨hp, hlx⟩)
    · refine ⟨ha, fun _ => ?_⟩
      have h1 : HeldV c hs (ownP K (L.mem σ) x) := by
        rw [ownP_eq_own nv hp, ← hc, ← hl]
        exact heldV_of_heldBy hw
      rw [eown, hvo] at h1
      rw [hV.1 x (Or.inl h1)]
      exact h1
    · exact ⟨hu.1, fun h => absurd hu.2 h⟩
    · refine ⟨(kPte x hp).1, fun _ => ?_⟩
      rw [ownP_pte hp]
      show hs x
      rw [← hl]; exact hlx
  have hRPO : ∀ x, ¬ x ∈ K.user → Ro x → PO c hs (ownP K μ x) := by
    intro x hu hx
    have hio : IoRSP st K j.Locks σ x := hx.1.2.resolve_left hu
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      have := po_of_rperm (ioRSP_rperm nv hio)
      rw [hc, hl] at this
      exact this
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  refine PathObl.insA_narrow_tr_wrU (own := ownP K) (cls := OwnMap.cls K.toKLayout)
    (kt := OwnMap.ko K.toKLayout μ) (User := (· ∈ K.user)) ar adEq_equiv (moveHeldP hK) (ownDepP hK hU)
    (masksWr_plain st) (pwe_own hK) (fun x hx => pwe_ko hK μ hx) (fun b hb => pwe_user hU hb) (a := a)
    (R.invBodyG j.number j.p) hc (R0 := InvRSP st K j.Locks σ)
    (Qv := VO K c ρ) (Rd := Rd) (Ru := PathObl.UserW K.toKLayout)
    (Wd := Wd) (fun b hb => vo_of_pwe hK hb) hal hR0
    (fun b h => h.1) (fun b h => h.2) hWd hRPO (fun x hx => hV.2.1 x hx) ?_
  intro s h1 h2 h3
  obtain ⟨r, g1, g2, g3, σ', hP', hqu', hmm', e1, e2, e3, hag, hW⟩ := hgoX s h1 h2 h3
  refine ⟨r, g1, g2, g3, ?_⟩
  have hT' : ∀ hi : U64, hi.val < 2048 → L.mem σ' (atAF K.ksb hi) = E (atAF K.ksb hi) := fun hi hhi => by
    rw [hmm' _ (hqu'.1.al hi hhi) (fun hu => hqu'.1.uoff _ (Or.inl hu) hi hhi rfl)]; exact hTv hi hhi
  have hWal : ∀ b, Wd b → Aligned b := by
    rintro b ((h | h) | h)
    · exact h.1.1
    · exact h.1
    · exact (kPte b h.1).1
  exact E2E.insT_agree (masksWr_plain st) (fun b h => Or.elim h (hal b) (fun h => h.1)) hWal _ σ' s a hW e1 e2
    e3 hag (pte_insT_view ar hA j hK hU h hcv a hP' hqu' hT')

end main

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **U9's re-annotated body is `InsA` at every CNodeDelete start** (module docstring; glue as `inv_annV_delA`). -/
theorem del_insA_annV {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {j : InvArg S} (E : U64 → U64) (hcv : K.ptes = ptesR K E)
    (hTv : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi))
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
      (.inr (.inl (.inr j))))
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  obtain ⟨σe, hC'⟩ := hC
  have hσe : Ch σe := by
    obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
    exact h'
  have hsf' := hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v
  obtain ⟨q0, ⟨h, σ, a, he, hc, hl, hμ, e⟩, rfl⟩ := hsf'
  subst e
  have hJ : SlJAt (L := L) K.toKLayout σ := ChainOf.bun hC' σ he.1
  have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x := hμ
  have hqu : QU st K σ :=
    qU_startN st ⟨σe, ChainOf.bun hC' σe hσe⟩ hJ hE (fun x hx hu => hμ x hx hu)
  have hc' : L.cpu σ = c := hc
  have hl' : j.Locks σ = (fun l => s.lk l = some c) := hl
  unfold annV
  rw [hM.own, hM.cls, hM.ko] at hV ⊢
  have h1 := inv_del_insA ar hA hK hU j h E hcv hTv hV (a := a) hJ he.2 hqu hc' hl' hmm
  rw [tr_cut (InvCMRS (st := st) K.toKLayout j.Locks σ) (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout)
    (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
    (R.invBodyG j.number j.p) ∅ a] at h1
  have eRS : (invPathVU st ar hA (masksWr_plain st) j K (view K.toKLayout c ρ) hK hU h).RS σ =
      InvCMRS (st := st) K.toKLayout j.Locks σ :=
    funext fun x => propext ⟨fun h' => h'.1, fun h' => ⟨h', not_vData_empty h.nv⟩⟩
  convert h1 using 3
  unfold LocalPath.body
  rw [hc, eRS]
  all_goals rfl

set_option maxHeartbeats 4000000 in
/-- **U9's re-annotated body is `InsA` at every PTE-delete start** (module docstring; glue as `inv_annV_pteA`). -/
theorem pte_insA_annV {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {j : InvArg S} (E : U64 → U64) (hcv : K.ptes = ptesR K E)
    (hTv : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi))
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
      (.inr (.inl (.inl j))))
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  obtain ⟨σe, hC'⟩ := hC
  have hσe : Ch σe := by
    obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
    exact h'
  have hsf' := hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v
  obtain ⟨h, σ, a, he, hc, hl, hμ, e⟩ := hsf'
  subst e
  have hJ : SlJAt (L := L) K.toKLayout σ := ChainOf.bun hC' σ he.1
  have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x := hμ
  have hqu : QU st K σ :=
    qU_startN st ⟨σe, ChainOf.bun hC' σe hσe⟩ hJ hE (fun x hx hu => hμ x hx hu)
  have hc' : L.cpu σ = c := hc
  have hl' : j.Locks σ = (fun l => s.lk l = some c) := hl
  unfold annV
  rw [hM.own, hM.cls, hM.ko] at hV ⊢
  have h1 := inv_pte_insA ar hA hK hU j h E hcv hTv hV (a := a) hJ he.2 hqu hc' hl' hmm
  convert h1 using 3
  unfold LocalPath.body
  rw [hc]
  all_goals rfl

end all

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The CNodeDelete indices of the PageMap index type. -/
def DelPm : IxV13Pm S → Prop
  | .inl (.inr (.inl (.inr _))) => True
  | _ => False

/-- The PTE-delete indices of the PageMap index type. -/
def PtePm : IxV13Pm S → Prop
  | .inl (.inr (.inl (.inl _))) => True
  | _ => False

set_option maxHeartbeats 4000000 in
/-- **`InsV15V`'s obligation of `nativePmKAD B` at every CNodeDelete start** (module docstring). -/
theorem insAP_del_view (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    {E : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : DelPm (S := S) i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with ((j | ((j | j) | j)) | j)
  all_goals try exact False.elim hx
  have hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inl (.inr (.inl (.inr j)))) := fun h => h
  rw [if_pos hn]
  have hsf0 : StartV13 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 (.inr (.inl (.inr j))) := hsf
  have hsf' := startV2C_of_V13 st ar hA a0 hC hsf0
  have hTv : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi) :=
    fun hi hhi => atAF_view L J nv hM hV (bun_of_chain st (arI := arI) (AR := AR) (MR := MR) hC) hhi
  exact insAP_of_insA (del_insA_annV st ar hA a0 E J.conv hTv hC (epochPteN_view_of J nv hM hV) hsf' hM hV)

set_option maxHeartbeats 4000000 in
/-- **`InsV15V`'s obligation of `nativePmKAD B` at every PTE-delete start** (module docstring). -/
theorem insAP_pte_view (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    {E : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : PtePm (S := S) i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with ((j | ((j | j) | j)) | j)
  all_goals try exact False.elim hx
  have hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inl (.inr (.inl (.inl j)))) := fun h => h
  rw [if_pos hn]
  have hsf0 : StartV13 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 (.inr (.inl (.inl j))) := hsf
  have hsf' := startV2C_of_V13 st ar hA a0 hC hsf0
  have hTv : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi) :=
    fun hi hhi => atAF_view L J nv hM hV (bun_of_chain st (arI := arI) (AR := AR) (MR := MR) hC) hhi
  exact insAP_of_insA (pte_insA_annV st ar hA a0 E J.conv hTv hC (epochPteN_view_of J nv hM hV) hsf' hM hV)

/-- **The view starts at which the obligation is still asked after gen 51's CNodeDelete / PTE-delete step**: the
PageMap starts only (module docstring). -/
def Open53 (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64) (ρ : U64 → U64) (k0 : SP) (i : IxV13Pm S) : Prop :=
  Open52 st s K c ρ k0 i ∧ ¬ DelPm (S := S) i ∧ ¬ PtePm (S := S) i

set_option maxHeartbeats 4000000 in
/-- **`InsV15NOV … Open53` gives `InsV15NOV … Open52`** for `nativePmKAD B` (module docstring). -/
theorem insV15NOV52_of_53 (B : PmObl7 st Cs Ω Sg Ac Locks)
    (h : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open53 st)) :
    InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open52 st) := by
  intro Ch s K E hK hU c k0 ρ i nv hO hC J hM hVq hi
  by_cases hd : DelPm (S := S) i
  · exact insAP_del_view st ar hA a0 B nv hd hC J hM hVq hi
  by_cases hp : PtePm (S := S) i
  · exact insAP_pte_view st ar hA a0 B nv hp hC J hM hVq hi
  exact h Ch s K E hK hU c k0 ρ i nv ⟨hO, hd, hp⟩ hC J hM hVq hi

end pm

end
end Fl4Proofs.P2.E2EP
