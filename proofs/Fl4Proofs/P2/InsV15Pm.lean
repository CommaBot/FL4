/-
# P2 (line p3mc, gen 51): `InsV15V` at every PageMap start; **the start obligation `InsV15NOV … Open52` [J] proved**

The PageMap certificate `pm_annA` (P2/InvPmAnnV, gen 44) reads upper paging words (the walk) and the locked leaf, and
stores a present entry into the leaf (`write_mapping`), so its `InsA` twin is an **`InsAP`** one with the done set
(`InsTP`, mmuAD gen 9), by the CNodeDelete / PTE-delete pattern of P2/InsV15Del:

## 1. The certificate with a done set (generic)
* **`Serial.insRunP_narrow`**: `InsRunP` survives a re-annotation keeping every `G` word in the read set (as gen 46's
  `insRun_narrow`).
* **`E2E.insAP_narrow_tr_of_states`**: gen 46's `insA_narrow_tr_of_states` with `InsTP … Set.univ ∅` for `InsT`,
  concluding `InsAP … ∅` (`SafeCertADQP.insAP_of_runsQP`, `insTP_sim`, `insRunP_narrow`).
* **`PathObl.insAP_narrow_tr_wrU`**: gen 46's `insA_narrow_tr_wrU` with `InsTP` in the run oracle.
* **`E2E.insTP_agree`**: `InsTP` moves between states agreeing on the run's reads (as `insT_agree`).

## 2. PageMap
* **`pm_insTP_view`**: at a PageMap view start the run is `InsTP (PWE K E) ADEq NotPresent … Set.univ ∅`: accepted
  runs by mmuAD's `pmAccIns` (P2/E2EPU3j, used read-only), declined ones by `pm_decR` and `insTP_of_within`
  (`QPs (KU K E)` by `qPs_ku_of`).
* **`pm_insAP`**: the PageMap program is `InsAP (PWE K E) … ∅` at a view start: `insAP_narrow_tr_wrU` on gen 51's
  oracle split `pm_hgoX` (P2/InvPmAnnV, with `pmGdV_holds`), `InsTP` at the user-word variant `σ'` moved by
  `insTP_agree`.
* glue **`pm_insAP_annV`** (as `pmFhK_of_gd`), `PmPm`, **`insAP_pm_view`**.

## 3. The open set is empty; the [J] is a theorem
* `Open54 := Open53 ∧ ¬ PmPm`; **`open54_empty`**: no index satisfies it (gen 47–51 closed every summand of
  `IxV13Pm`), so **`insV15NOV54_holds`**: `InsV15NOV … Open54` holds outright, and with the chain of the gen 47–51
  implications **`insV15NOV52_holds`**: **the [J] `InsV15NOV … Open52` of `serializable_fl4_V15_pmKADO` is proved**
  (from `B` alone); further down the chain, **`insV15V_holds`**: gen 48's [J] `InsV15V` of `nativePmKAD B` holds
  (from `P`, `hIoa`, `B`).
* **`serializable_fl4_V15_pmKADZ`** (authoritative): `serializable_fl4_V15_pmKADO` **without** the [J] premise: its
  premises are `P`, [P] `hIoa`, `B : PmObl7` ([P] `cs` / `lk`), `h0`, `hA0`, `hB`, `hc0`, `hM0`, the execution `h`
  (`ExecV15 (nativePmKAD B)`, [P] `MmuAD` in its A/D step) and `hq`. **`serializable_fl4_V15_pmKADOofZ`** (the previous
  top's statement from it) and **`serializable_fl4_V15_pmKADZofO`** (it from the previous top and `insV15NOV52_holds`).

Named premises: none new; the [J] `InsV15NOV … Open52` / `Open53` is discharged. New module; existing file touched:
P2/InvPmAnnV (in-place split, every existing statement byte-identical).

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `serializable_fl4_V15_pmKADOofZ`,
`serializable_fl4_V15_pmKADZofO`.
-/
import Fl4Proofs.P2.InsV15Del
import Fl4Proofs.P2.InvPmGdV
import Fl4Proofs.P2.E2EPU3j
import Fl4Proofs.P2.E2EADQP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Serial

noncomputable section
open Classical

variable {A V C L : Type} [DecidableEq A] [DecidableEq C] [DecidableEq L]
variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop} {cls' : A → V → V} {ko' : A → ClsOwner C} {c' : C}

/-- **`InsRunP` survives a re-annotation keeping every `G` word in the read set** (module docstring §1). -/
theorem insRunP_narrow {Qv : A → Prop} (hGQ : ∀ a, G a → Qv a) (q : Prog A V L) :
    ∀ (D Wd : Set A) (ν : A → V), InsRunP G Q NP D q ν → InsRunP G Q NP D (narrowSP cls' ko' c' Qv Wd q) ν := by
  induction q with
  | done => intros; simp only [narrowSP, InsRunP]
  | lock l k _ => intros; simp only [narrowSP, InsRunP]
  | start k _ => intros; simp only [narrowSP, InsRunP]
  | rd a k ih =>
    intro D Wd ν h
    simp only [InsRunP] at h
    simp only [narrowSP]
    split_ifs with h1
    · simp only [InsRunP]
      exact ⟨fun hg u hu => congrArg (narrowSP cls' ko' c' Qv Wd) (h.1 hg u hu), ih _ D Wd ν h.2⟩
    · simp only [InsRunP]
      exact ⟨fun hg => h1 (Or.inl (hGQ a hg)), ih _ D Wd ν h.2⟩
    · simp only [InsRunP]
      exact ⟨fun hg => h1 (Or.inl (hGQ a hg)), ih _ D Wd ν h.2⟩
  | rds a k ih =>
    intro D Wd ν h
    simp only [InsRunP] at h
    simp only [narrowSP, InsRunP]
    exact ⟨h.1, ih _ D Wd ν h.2⟩
  | rdc a K k ih =>
    intro D Wd ν h
    simp only [InsRunP] at h
    simp only [narrowSP]
    split_ifs
    · simp only [InsRunP]; exact ⟨h.1, ih _ D Wd ν h.2⟩
    · simp only [InsRunP]; exact ⟨h.1, ih _ D Wd ν h.2⟩
  | wr a v k ih =>
    intro D Wd ν h
    simp only [InsRunP] at h
    simp only [narrowSP, InsRunP]
    exact ⟨h.1, ih _ (insert a Wd) _ h.2⟩

end
end Fl4Proofs.P2.Serial

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner Prog HeldV PO Safe MoveHeld AltRun Adm Diff RInv InsAP InsRunP DInvQP
  insAP_of_runsQP narrowSP AnnLe altRun_annLe insRunP_narrow dU)

noncomputable section
open Classical

section agree
variable {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
  {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop} {User : U64 → Prop} {E : Set U64}

/-- **`InsTP` moves between states agreeing on the run's reads** (module docstring §1). -/
theorem insTP_agree (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s) {R W : U64 → Prop}
    (hRal : ∀ w, R w → Aligned w) (hWal : ∀ w, W w → Aligned w) (p : SProg X) :
    ∀ (D : Set U64) (s s' : S) (a : A), Within st ar R W p s a → L.ksb s' = L.ksb s → L.cpu s' = L.cpu s →
      st.frame_masks s' = st.frame_masks s → (∀ w, R w → L.mem s' w = L.mem s w) →
      InsTP st ar G Q NP User E D p s a → InsTP st ar G Q NP User E D p s' a := by
  induction p with
  | ret x => intro D s s' a _ _ _ _ _ h; exact h
  | err e => intros; trivial
  | zero q n k ih => intros; trivial
  | clr q n k ih => intros; trivial
  | rd q k ih =>
    intro D s s' a hW e1 e2 e3 e4 h
    simp only [Within] at hW
    simp only [InsTP] at h ⊢
    intro v hv
    have hv0 : st.read s q = ok v := by
      rw [L.read_eq] at hv ⊢; rw [← e4 q hW.1]; exact hv
    exact ⟨(h v hv0).1, ih v D s s' a (hW.2 v hv0) e1 e2 e3 e4 (h v hv0).2⟩
  | rdp q k ih =>
    intro D s s' a hW e1 e2 e3 e4 h
    simp only [Within] at hW
    simp only [InsTP] at h ⊢
    refine ⟨h.1, h.2.1, fun v hv => ?_⟩
    have hv0 : st.read_pair s q = ok v := by
      rw [L.read_pair_eq] at hv ⊢; rw [← e4 q hW.1, ← e4 _ hW.2.1]; exact hv
    exact ih v D s s' a (hW.2.2 v hv0) e1 e2 e3 e4 (h.2.2 v hv0)
  | wr q v k ih =>
    intro D s s' a hW e1 e2 e3 e4 h
    simp only [Within] at hW
    simp only [InsTP] at h ⊢
    refine ⟨h.1, fun s1 hs1 => ?_⟩
    rw [L.write_eq] at hs1
    obtain rfl := Result.ok_injective hs1
    have ha := hWal q hW.1
    exact ih _ (L.wr s q v) (L.wr s' q v) a (hW.2 _ (L.write_eq s q v)) (by rw [L.ksb_wr, L.ksb_wr, e1])
      (by rw [L.cpu_wr, L.cpu_wr, e2]) (by rw [hm, hm, e3])
      (fun w hw => by rw [L.mem_wr _ _ _ _ ha (hRal w hw), L.mem_wr _ _ _ _ ha (hRal w hw), e4 w hw])
      (h.2 _ (L.write_eq s q v))
  | ksb k ih =>
    intro D s s' a hW e1 e2 e3 e4 h
    simp only [Within] at hW
    simp only [InsTP] at h ⊢
    intro v hv
    have hv0 : st.ks_base s = ok v := by
      rw [L.ks_base_eq] at hv ⊢; rw [← e1]; exact hv
    exact ih v D s s' a (hW v hv0) e1 e2 e3 e4 (h v hv0)
  | cpu k ih =>
    intro D s s' a hW e1 e2 e3 e4 h
    simp only [Within] at hW
    simp only [InsTP] at h ⊢
    intro v hv
    have hv0 : st.cur_cpu s = ok v := by
      rw [L.cur_cpu_eq] at hv ⊢; rw [← e2]; exact hv
    exact ih v D s s' a (hW v hv0) e1 e2 e3 e4 (h v hv0)
  | masks k ih =>
    intro D s s' a hW e1 e2 e3 e4 h
    simp only [Within] at hW
    simp only [InsTP] at h ⊢
    intro v hv
    have hv0 : st.frame_masks s = ok v := by rw [← e3]; exact hv
    exact ih v D s s' a (hW v hv0) e1 e2 e3 e4 (h v hv0)
  | arch op k ih =>
    intro D s s' a hW e1 e2 e3 e4 h
    simp only [Within] at hW
    simp only [InsTP] at h ⊢
    exact fun v a' hv => ih v D s s' a' (hW v a' hv) e1 e2 e3 e4 (h v a' hv)

end agree

section cert
variable {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {kt : U64 → ClsOwner U64} {User : U64 → Prop}

set_option maxHeartbeats 4000000 in
/-- **`InsAP` of the re-annotated translated body from runs at real-valued states** (module docstring §1). -/
theorem insAP_narrow_tr_of_states {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop} (hQ : Equivalence Q)
    (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → kt x = .free)
    (hGU : ∀ x, G x → ¬ User x)
    {Qv : U64 → Prop} (hGQ : ∀ b, G b → Qv b) {kv : U64 → ClsOwner U64}
    {c : U64} {hs : U64 → Prop} {kb : U64} {mk : U64 × U64} {R Hp : U64 → Prop} (p : SProg X) (a : A)
    {μ : U64 → U64}
    (hH : ∀ x, Hp x → HeldV c hs (own μ x)) (hR : ∀ x, ¬ User x → (R x ∧ Qv x) → PO c hs (own μ x))
    (hrun : ∀ ν, Adm own cls kt c hs μ (fun _ => none) ν → ∃ (s : S) (Wr : U64 → Prop),
      L.cpu s = c ∧ L.ksb s = kb ∧ st.frame_masks s = ok mk ∧
      Within st ar Aligned Wr p s a ∧
      WithinM st ar (fun x y => StepOK own cls kt User c hs (L.mem x) (L.mem y)) p s a ∧
      Once st ar (fun x => R x ∧ Qv x) User ∅ ∅ p s a ∧ (∀ x, Wr x → Aligned x ∧ (¬ User x → Hp x)) ∧
      (∀ x ∈ reads (tr (fun x => R x ∧ Qv x) User cls kt c kb mk ar p ∅ a) ν, Aligned x → L.mem s x = ν x) ∧
      (∀ x, Aligned x → ¬ User x → L.mem s x ≠ μ x → ¬ PO c hs (own μ x)) ∧
      InsTP st ar G Q NP User Set.univ ∅ p s a ∧
      Within st ar (fun b => G b → (R b ∧ Qv b) ∧ ¬ User b) (fun _ => True) p s a) :
    InsAP G Q NP own cls kt c hs ∅ μ (narrowSP cls kt c Qv ∅ (tr R User cls kv c kb mk ar p ∅ a)) := by
  have hRI : RInv own c hs (RpOf (fun x => (R x ∧ Qv x) ∧ True) User Hp) Hp μ :=
    ⟨hH, fun x hx => hx.elim (fun h => hR x h.1 h.2.1) (fun h => Or.inl (hH x h))⟩
  have hAnn := annLe_tr (R := R) (Qv := Qv) (User := User) (cls := cls) (kt := kt) (kv := kv) (c := c) kb mk ar
    p ∅ a
  refine insAP_of_runsQP hQ hL hGo hGko (Rp := RpOf (fun x => (R x ∧ Qv x) ∧ True) User Hp) (Hp := Hp) _ ∅ ∅ μ
    (fun _ => none) ⟨fun ν hν => ?_, fun y u hu => (by cases hu), fun y u hu => (by cases hu),
      fun y u hu => (by cases hu), hRI, fun y u hu => (by cases hu)⟩
  obtain ⟨s, Wr, hc, hk, hm, hW, hM, hN, hWr, hν', hD, hI, hGR⟩ := hrun ν hν
  have eR : reads (tr R User cls kv c kb mk ar p ∅ a) ν =
      reads (tr (fun x => R x ∧ Qv x) User cls kt c kb mk ar p ∅ a) ν := by
    rw [reads_annLe hAnn ν, reads_narrow]
  refine ⟨fun x => if Aligned x ∧ ¬ User x then L.mem s x else μ x, fun y hy hpo => ?_, ?_, ?_⟩
  · dsimp only at hy
    by_cases h : Aligned y ∧ ¬ User y
    · rw [if_pos h] at hy; exact hD y h.1 h.2 hy hpo
    · rw [if_neg h] at hy; exact hy rfl
  · refine altRun_annLe hAnn _ _ _ ?_
    exact simN (L := L) hmk (N := fun _ => True) (Kc := fun _ => True) (kt := kt) (ko := kt)
      (Rr := fun _ => True) (Wr := Wr) (D := fun _ => False) (DD := fun _ => False)
      (fun x hx => ⟨(hWr x hx).1, (hWr x hx).2, trivial, trivial⟩) (fun x _ => ⟨trivial, Or.inr trivial⟩)
      (fun x _ h => h) (fun x _ => rfl)
      (fun m m' h y _ => congrFun (hO m m' fun x hx hu => h x hx hu id) y)
      (fun q _ m v y hy => hy.elim) p s a ∅ ∅ ∅ ν _
      (Within.mono (fun b hb => ⟨hb, trivial⟩) (fun b hb => hb) p s a hW) hM hN
      (fun x hx => absurd hx (Set.notMem_empty x)) subset_rfl hm hk hc
      (fun x hx hu _ => by
        show (if Aligned x ∧ ¬ User x then L.mem s x else μ x) = _
        rw [if_pos ⟨hx, hu⟩])
      (fun x hx hxa _ _ => hν' x hx hxa)
  · refine insRunP_narrow hGQ _ ∅ ∅ ν ?_
    exact insTP_sim (L := L) hmk (R := R) (ko := kv) (Rr := fun _ => True) (Wr := Wr) (E := Set.univ)
      (fun x hx => (hWr x hx).1) hGU p ∅ s a ∅ ∅ ν
      (Within.mono (fun b hb => ⟨hb, trivial⟩) (fun b hb => hb) p s a hW) hI
      (Within.mono (fun b hb hg => ⟨(hb hg).1.1, (hb hg).2⟩) (fun _ h => h) p s a hGR)
      (once_monoR (R := fun x => R x ∧ Qv x) (R' := R) (fun b hb => hb.1) p ∅ ∅ ∅ s a hN subset_rfl)
      hm hk hc (fun x hx hxa _ _ => hν' x (by rw [← eR]; exact hx) hxa)

end cert

end
end Fl4Proofs.P2.E2E

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once tr reads exists_mem_state OwnDep MasksWr masksOf masksOf_eq InsTP
  insAP_narrow_tr_of_states)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm InsAP narrowSP)

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **`InsAP` of the re-annotated body from `safe_tr_wrU`'s data with `InsTP`** (module docstring §1). -/
theorem insAP_narrow_tr_wrU {X : Type} {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt kv : U64 → ClsOwner U64} {User : U64 → Prop} {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop}
    (hQ : Equivalence Q) (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → kt x = .free)
    (hGU : ∀ b, G b → ¬ User b)
    {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64} {σ : S} {a : A} (p : SProg X)
    (hc : L.cpu σ = c) {R0 Qv Rd Ru Wd : U64 → Prop} (hGQ : ∀ b, G b → Qv b)
    (hal : ∀ b, Rd b → Aligned b) (hR0 : ∀ q, Rd q → (R0 q ∧ Qv q) ∧ ¬ User q) (hUa : ∀ b, Ru b → Aligned b)
    (hRuU : ∀ b, Ru b → User b)
    (hWd : ∀ x, Wd x → Aligned x ∧ (¬ User x → HeldV c hs (own μ x)))
    (hRPO : ∀ x, ¬ User x → (R0 x ∧ Qv x) → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∃ r, interp (guard st (fun b => Rd b ∨ Ru b) Wd) ar p s a = ok r ∧
        WithinM st ar (fun x y => StepOK own cls kt User c hs (L.mem x) (L.mem y)) p s a ∧
        Once st ar (fun x => R0 x ∧ Qv x) User ∅ ∅ p s a ∧ InsTP st ar G Q NP User Set.univ ∅ p s a) :
    InsAP G Q NP own cls kt c hs ∅ μ
      (narrowSP cls kt c Qv ∅ (tr R0 User cls kv c (L.ksb σ) (masksOf st σ) ar p ∅ a)) := by
  refine insAP_narrow_tr_of_states hQ hL hO hmk hGo hGko hGU hGQ (Hp := fun x => Wd x ∧ ¬ User x) p a
    (fun x hx => (hWd x hx.1).2 hx.2) hRPO ?_
  intro ν hν
  generalize hq : tr (fun x => R0 x ∧ Qv x) User cls kt c (L.ksb σ) (masksOf st σ) ar p ∅ a = q
  obtain ⟨s, sc, sk, sm, hmem0⟩ := exists_mem_state hmk σ (fun x => if x ∈ reads q ν then ν x else ρ x)
  have hmem : ∀ x, Aligned x → L.mem s x = if x ∈ reads q ν then ν x else ρ x := hmem0
  have eR : ∀ b, (R0 b ∧ Qv b) → ¬ User b → (if b ∈ reads q ν then ν b else ρ b) = ρ b := by
    intro b hb hu'
    split_ifs
    · exact (hν.1 b (hRPO b hu' hb)).trans (hρμ b (hRPO b hu' hb)).symm
    · rfl
  have hag : ∀ b, Rd b → L.mem s b = ρ b := fun b hb => by
    rw [hmem b (hal b hb), eR b (hR0 b hb).1 (hR0 b hb).2]
  obtain ⟨r, hg, hWM, hOnce, hI⟩ := hgo s sc sk hag
  have hW := (interp_guard _ s a r hg).2
  refine ⟨s, Wd, sc.trans hc, sk, sm.trans (masksOf_eq st σ),
    Within.mono (fun b hb => hb.elim (hal b) (hUa b)) (fun b hb => hb) _ s a hW, hWM, hOnce,
    fun x hx => ⟨(hWd x hx).1, fun hu => ⟨hx, hu⟩⟩, fun x hx hxa => by rw [hmem x hxa, if_pos hx],
    fun x hxa hu' hne hpo => hne ?_, hI,
    Within.mono (fun b hb hg => hb.elim (fun h => hR0 b h) (fun h => absurd (hRuU b h) (hGU b hg)))
      (fun _ _ => trivial) _ s a hW⟩
  rw [hmem x hxa]
  split_ifs
  · exact hν.1 x hpo
  · exact hρμ x hpo

end

end
end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath tr masksOf InsTP insTP_of_within)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll VEq Safe InsAP narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN vn_of_nf nf_none)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The PageMap run at a view start is `InsTP` at the epoch's paging words** (module docstring §2). -/
theorem pm_insTP_view (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
    (B : PmObl7 st Cs Ω Sg Ac Locks) (j : I64 × localinv.Plan) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {m E : U64 → U64} (hcv : K.ptes = ptesR K E) {σ : S} (a : A)
    (hPre : PmPreG st Cs Ω Sg Ac Locks j.2 K m σ) (hqu : QU st K σ)
    (hT : ∀ hi : U64, hi.val < 2048 → L.mem σ (atAF K.ksb hi) = E (atAF K.ksb hi)) :
    InsTP st ar (PWE K E) ADEq NotPresent (· ∈ K.user) Set.univ ∅ (R.invBodyPmG j.1 j.2) σ a := by
  have hqK : QPs (KU K E) st σ := qPs_ku_of hcv hqu.1 hT
  obtain ⟨r, hr⟩ := inv_total (st := st) hA j.1 j.2 σ a
  by_cases hacc : r.1 = true
  · exact pmAccIns st ar hA (masksWr_plain st) B j K E m hK hU σ a r ⟨hPre, hqK⟩ hr hacc
  · exact insTP_of_within (fun x hx => pwe_user hU hx) (fun x hx => absurd hx (Set.notMem_empty x))
      (Set.empty_subset _) _ σ a (pm_decR hA (masksWr_plain st) B j (E := E) (m := m) hK hU σ σ a r ⟨hPre, hqK⟩
        hr hacc (Alt.refl (L := L) σ))

set_option maxHeartbeats 4000000 in
/-- **The PageMap program is `InsAP` at every PageMap view start** (module docstring §2). -/
theorem pm_insAP (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64} {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
    (B : PmObl7 st Cs Ω Sg Ac Locks) (E : U64 → U64) (hcv : K.ptes = ptesR K E)
    (hTv : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi))
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {j : I64 × localinv.Plan} {σ : S} {a : A}
    (hPre : PmPreG st Cs Ω Sg Ac Locks j.2 K (view K.toKLayout c ρ) σ) (hqu : QU st K σ)
    (hc : L.cpu σ = c) (hl : Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    InsAP (PWE K E) ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ∅ μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (PmRSU st K Locks σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.invBodyPmG j.1 j.2) ∅ a)) := by
  have nv : K.vcpus = ∅ := hPre.1.2.2.nv
  have hgoX := pm_hgoX ar hA hK hU hV (j := j) (a := a) B.cs B.lk (pmGdV_holds ar hA) hPre hqu hc hmm
  -- the read sets (as `pm_annA`)
  have kPte : ∀ b, b ∈ K.ptes → Aligned b ∧ b ∉ K.user := fun b hb => hU.kern b hb
  have oPte : ∀ b, b ∈ K.ptes → VO K c ρ b := fun b hb => by unfold VO; rw [ownP_pte hb, ownP_pte hb]
  let Rd : U64 → Prop := fun b => (IoRS (st := st) K.toKLayout Locks σ b ∧ SR K c ρ b) ∨ PteRd K (Locks σ) b
  let Ro : U64 → Prop := fun q => PmRSU st K Locks σ q ∧ VO K c ρ q
  have hR0 : ∀ q, Rd q → Ro q ∧ ¬ q ∈ K.user := by
    rintro q (⟨h1, h2⟩ | ⟨hp, hl'⟩)
    · have hio : IoRSP st K Locks σ q := ⟨h1, fun hp => absurd hp h2.2⟩
      exact ⟨⟨⟨h1.1, Or.inr ⟨h1.1, h1.2.1, ioRSP_rperm nv hio⟩⟩, h2.1.2⟩, h1.2.1⟩
    · have hio : IoRSP st K Locks σ q :=
        ⟨VsW.ioRS ⟨(kPte q hp).1, hK.none q hp, (kPte q hp).2⟩, fun _ => hl'⟩
      exact ⟨⟨⟨(kPte q hp).1, Or.inr ⟨(kPte q hp).1, (kPte q hp).2, ioRSP_rperm nv hio⟩⟩, oPte q hp⟩,
        (kPte q hp).2⟩
  have hal : ∀ b, Rd b → Aligned b := by
    rintro b (hb | hb)
    · exact hb.1.1
    · exact (kPte b hb.1).1
  let Wd : U64 → Prop := DelWdP K c ρ (IoWS (st := st) K.toKLayout Locks σ) (Locks σ)
  have hWal : ∀ b, Wd b → Aligned b := by
    rintro b ((h | h) | h)
    · exact h.1.1
    · exact h.1
    · exact (kPte b h.1).1
  -- ownership of the read and written words at the physical memory (as `pm_annA`)
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
    have hrs : PmRS st K Locks σ x := pmRSU_nu hx.1 hu
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      have := po_of_rperm hrs.2.2
      rw [hc, hl] at this
      exact this
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  refine PathObl.insAP_narrow_tr_wrU (own := ownP K) (cls := OwnMap.cls K.toKLayout)
    (kt := OwnMap.ko K.toKLayout μ) (User := (· ∈ K.user)) ar adEq_equiv (moveHeldP hK) (ownDepP hK hU)
    (masksWr_plain st) (pwe_own hK) (fun x hx => pwe_ko hK μ hx) (fun b hb => pwe_user hU hb) (a := a)
    (R.invBodyPmG j.1 j.2) hc (R0 := PmRSU st K Locks σ)
    (Qv := VO K c ρ) (Rd := Rd) (Ru := PathObl.UserW K.toKLayout)
    (Wd := Wd) (fun b hb => vo_of_pwe hK hb) hal hR0
    (fun b h => h.1) (fun b h => h.2) hWd hRPO (fun x hx => hV.2.1 x hx) ?_
  intro s h1 h2 h3
  obtain ⟨r, g1, g2, g3, σ', hP', hqu', hmm', e1, e2, e3, hag, hW⟩ := hgoX s h1 h2 h3
  refine ⟨r, g1, g2, g3, ?_⟩
  have hT' : ∀ hi : U64, hi.val < 2048 → L.mem σ' (atAF K.ksb hi) = E (atAF K.ksb hi) := fun hi hhi => by
    rw [hmm' _ (hqu'.1.al hi hhi) (fun hu => hqu'.1.uoff _ (Or.inl hu) hi hhi rfl)]; exact hTv hi hhi
  exact E2E.insTP_agree (masksWr_plain st) (fun b h => Or.elim h (hal b) (fun h => h.1)) hWal _ ∅ σ' s a hW e1 e2
    e3 hag (pm_insTP_view ar hA B j hK hU hcv a hP' hqu' hT')

end main

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

set_option maxHeartbeats 4000000 in
/-- **U9's re-annotated body is `InsAP` at every PageMap start** (module docstring §2; glue as `pmFhK_of_gd`). -/
theorem pm_insAP_annV (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP} {ρ : U64 → U64} {j : I64 × localinv.Plan}
    (E : U64 → U64) (hcv : K.ptes = ptesR K E)
    (hTv : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi))
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartPmK hA (masksWr_plain st) B Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c)
      k j)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem (annV s K c ρ k) := by
  obtain ⟨σe, hC'⟩ := hC
  have hσe : Ch σe := by
    obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
    exact h'
  obtain ⟨σ, a, hCh, hQ, hEx, hc, hl, hμ, e⟩ := hsf
  subst e
  have hJ : SlJAt (L := L) K.toKLayout σ := ChainOf.bun hC' σ hCh
  have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = CoreView.view K.toKLayout c ρ x := hμ
  have hqu : QU st K σ :=
    qU_startN st ⟨σe, ChainOf.bun hC' σe hσe⟩ hJ hE (fun x hx hu => hμ x hx hu)
  have hPre : PmPreG st Cs Ω Sg Ac Locks j.2 K (CoreView.view K.toKLayout c ρ) σ :=
    ⟨⟨hJ, hQ, gateEp_viewStart hJ hE hμ⟩, hEx, pmRoot_of_qf hQ⟩
  subst hc
  unfold annV
  rw [hM.own, hM.cls, hM.ko] at hV ⊢
  exact pm_insAP ar hA hK hU B E hcv hTv hV (j := j) (a := a) hPre hqu rfl hl hmm

/-- The PageMap indices of the PageMap index type. -/
def PmPm : IxV13Pm S → Prop
  | .inr _ => True
  | _ => False

set_option maxHeartbeats 4000000 in
/-- **`InsV15V`'s obligation of `nativePmKAD B` at every PageMap start** (module docstring §2). -/
theorem insAP_pm_view (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    {E : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : PmPm (S := S) i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with (i | j)
  · exact False.elim hx
  have hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inr j) := trivial
  rw [if_pos hn]
  have hsf0 : StartPmK hA (masksWr_plain st) B Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 j := hsf
  have hTv : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi) :=
    fun hi hhi => atAF_view L J nv hM hV (bun_of_chain st (arI := arI) (AR := AR) (MR := MR) hC) hhi
  exact pm_insAP_annV st ar hA B E J.conv hTv hC (epochPteN_view_of J nv hM hV) hsf0 hM hV

/-- **The view starts left after gen 51's PageMap step** (module docstring §3): none (`open54_empty`). -/
def Open54 (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64) (ρ : U64 → U64) (k0 : SP) (i : IxV13Pm S) : Prop :=
  Open53 st s K c ρ k0 i ∧ ¬ PmPm (S := S) i

/-- **No start is left open** (module docstring §3): every summand of `IxV13Pm` is closed by gen 47–51's predicates
(the `st` starts by `StFPm` / `StHPm` on the target's home, the irq starts by `irqCPm_irq`). -/
theorem open54_empty (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64) (ρ : U64 → U64) (k0 : SP) (i : IxV13Pm S) :
    ¬ Open54 st s K c ρ k0 i := by
  intro h
  unfold Open54 Open53 Open52 Open51 Open50 Open49S Open49 Open48V Open48 Open47 at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hVx, hVt, hStF⟩, hStH⟩, hSlH, hVmRH⟩, hVmF, hVmR⟩, hSl⟩, hIrq⟩, hCm⟩, hIo⟩, hDel, hPte⟩,
    hPm⟩ := h
  rcases i with ((i | ((j | j) | j)) | j)
  · cases i with
    | vmF j => exact hVmF trivial
    | vmR j => exact hVmR trivial
    | io j => exact hIo trivial
    | st j =>
      by_cases e : ρ (fld j.target oAFFINITY) = c
      · exact hStH e
      · exact hStF e
    | irq j => exact hIrq (irqCPm_irq K c ρ j)
    | sl j => exact hSl trivial
    | vq j =>
      rcases j with j | j
      · exact hVx trivial
      · exact hVt trivial
  · exact hPte trivial
  · exact hDel trivial
  · exact hCm trivial
  · exact hPm trivial

/-- **`InsV15NOV … Open54` holds** (`open54_empty`). -/
theorem insV15NOV54_holds (B : PmObl7 st Cs Ω Sg Ac Locks) :
    InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open54 st) :=
  fun _ s K _ _ _ c k0 ρ i _ hO => absurd hO (open54_empty st s K c ρ k0 i)

set_option maxHeartbeats 4000000 in
/-- **`InsV15NOV … Open54` gives `InsV15NOV … Open53`** for `nativePmKAD B` (at the PageMap starts by
`insAP_pm_view`). -/
theorem insV15NOV53_of_54 (B : PmObl7 st Cs Ω Sg Ac Locks)
    (h : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open54 st)) :
    InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open53 st) := by
  intro Ch s K E hK hU c k0 ρ i nv hO hC J hM hVq hi
  by_cases hp : PmPm (S := S) i
  · exact insAP_pm_view st ar hA a0 B nv hp hC J hM hVq hi
  exact h Ch s K E hK hU c k0 ρ i nv ⟨hO, hp⟩ hC J hM hVq hi

/-- **The [J] `InsV15NOV … Open52` of `serializable_fl4_V15_pmKADO` holds** (module docstring §3). -/
theorem insV15NOV52_holds (B : PmObl7 st Cs Ω Sg Ac Locks) :
    InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open52 st) :=
  insV15NOV52_of_53 st ar hA a0 B (insV15NOV53_of_54 st ar hA a0 B (insV15NOV54_holds st ar hA a0 B))

/-- **The V15 start obligation `InsV15V` of `nativePmKAD B` holds** (gen 48's [J], through the gen 47–51 chain;
module docstring §3). -/
theorem insV15V_holds (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks) :
    InsV15V (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) :=
  insV15V_of_NOV st ar hA a0 P hIoa B (insV15NOV48V_of_49 st ar hA a0 P hIoa B (insV15NOV49_of_49S st ar hA a0 P hIoa B
    (insV15NOV49S_of_50 st ar hA a0 B (insV15NOV50_of_51 st ar hA a0 B (insV15NOV51_of_52 st ar hA a0 P hIoa B
      (insV15NOV52_holds st ar hA a0 B))))))

/-- **`serializable_fl4_V15_pmKADZ` on the re-based platform**
(gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem serializable_fl4_V15_pmKADZ_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitC P.toC K0.toKLayoutV (Ch0 e))
    (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15C (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) P.toC s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_V15_pmKADO_C st ar hA a0 P B (insV15NOV52_holds st ar hA a0 B) h0 hA0 hB hc0 hM0 h hq

/-- **FL4 end to end over V13's slots and PageMap on CoreView with the walker's A/D writes, without the start
obligation** (module docstring §3): `serializable_fl4_V15_pmKADO` with its [J] discharged (`insV15NOV52_holds`). -/
theorem serializable_fl4_V15_pmKADZ (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15 (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) P s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_V15_pmKADZ_C st ar hA a0 (locPlatCR_of P hIoa) B h0 hA0 hB hc0 hM0 h.toC hq

end all

end
end Fl4Proofs.P2.E2EP
