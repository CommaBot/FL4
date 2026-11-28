/-
# P2 (line p3mc, gen 46): `InsV15`'s generic half — the re-annotation keeps `InsAP`, and an `InsA` certificate at
real-valued states for the re-annotated translated body (the `InsA` counterpart of `safe_tr_of_states` /
`safe_tr_wrU`)

`InsV15` [J] (P2/E2EPV15AD) asks, at every CoreView start, `InsAP (PWE K E) ADEq NotPresent … ∅` at the physical
memory of the armed program: the body `k0` (a translation `tr RS … kv p ∅ a` started at the view, class owner `kv`
the view's) or its re-annotation `annV s K c ρ k0 = narrowSP s.cls s.ko c (VO K c ρ) ∅ k0`. mmuAD proves its
`InsA` instances (`insA_w11`, `insA_delR`, `insA_invR`, `insA_cm`, `insAP_pmR`) through `LocalPath.insA` /
`insAQ` / `insAQP`, i.e. `body_insA(Q)`, whose hypothesis `hμ` is that the start state agrees with the memory the
fact is stated at **on every aligned kernel word**. At a view start the state agrees with the *view*, which differs
from the physical memory on the words the view rewrites (another core's thread's `AFFINITY`, …), and the physical
run takes branches (the `AFFINITY` decline) the view run never takes; so those proofs do not transfer by
congruence, and the transfer is the certificate route the `VSafe9` discharges (U19–U28, gen 44) take for `Safe`.

## 1. The re-annotation (`narrowSP`) keeps `InsA` / `InsAP` (handoff §50c plan, step 1)
* **`insA_narrow`**, **`insAP_narrow`**: `narrowSP cls' ko' c' Qv Wd q` is `InsA` / `InsAP` wherever `q` is (any
  re-annotation parameters): `InsA`'s three read clauses are the same, and a continuation equality `k u = k w`
  gives `narrowSP … (k u) = narrowSP … (k w)`. **`insAP_annV`**: `InsAP` of `k0` gives `InsAP` of `annV s K c ρ k0`.
  So `InsV15`'s `annV` disjunct follows from its `k0` disjunct wherever the latter is asked (not where `NoV i`, the
  only case `ExecV15` arms `annV k0` without `k0` being `Safe`).

## 2. The certificate (for step 2)
* `AnnLe cls q1 q2`: `q2` is `q1` with weaker annotations (a class read may become speculative);
  `altRun_annLe` (`AltRun` survives), `reads_annLe`, `reads_narrow`.
* **`annLe_tr`**: `tr (R ∧ Qv) … kt p Wd a` ≤ `narrowSP cls kt c Qv Wd (tr R … kv p Wd a)` — the tree the `VSafe9`
  certificates certify (`safe_tr_wrU` at `Ro = R ∧ VO`, class owner `kt` the physical one) against the armed tree
  (`annV` of the view-started body).
* `insRun_narrow` (`InsRun` survives a re-annotation keeping every `G` word in `Qv`).
* **`insA_narrow_tr_of_states`**: `InsA G Q NP own cls kt c hs μ (narrowSP cls kt c Qv ∅ (tr R … kv p ∅ a))` from
  `safe_tr_of_states`'s run data at every admissible `ν` (with `R ∧ Qv` as the certificate's read set) plus, per run,
  `InsT` of the store run (`G` reads insensitive, `G` stores `NP`) and its `G` reads inside `R ∧ Qv`;
  `SafeCertADQ.insA_of_runsQ`, the `AltRun` from `simN` and `altRun_annLe`, the `InsRun` from `insT_sim` and
  `insRun_narrow`.
* **`insA_narrow_tr_wrU`**: the same from `safe_tr_wrU`'s data (`hgo`: at every state carrying `ρ` on the read set
  `Rd`, the run on `guard st (Rd ∪ Ru) Wd` is ok, `StepOK` per write, `Once` for `R ∧ Qv`) plus `InsT` in `hgo`;
  **`insA_narrow_tr_wrU_noG`**: `InsT` derived when `Rd` and `Wd` avoid `G` (`insT_of_within`).

What a slot then needs (handoff §51a): its `VSafe9` certificate's `hgo` (each of U19–U28's `…_annA` / `…_fh`
proofs builds one inline) with the read / write sets cut off `PWE K E` (W11 slots, Copy / Mint) or with `InsT`
(delPte, CNodeDelete, PageMap: masked walk reads, `InsTP` for PageMap's present store).

No named premise; no existing statement changed (new module).
-/
import Fl4Proofs.P2.E2EPV15AD
import Fl4Proofs.P2.ViewSafeReal
import Fl4Proofs.P2.E2EADQ
import Fl4Proofs.P2.SlOnceL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Serial

noncomputable section
open Classical

variable {A V C L : Type} [DecidableEq A] [DecidableEq C] [DecidableEq L]

/-! ## 1. The re-annotation keeps `InsA` / `InsAP` -/

section narrow
variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop} {own : (A → V) → A → Owner C L}
  {cls : A → V → V} {ko : A → ClsOwner C} {c : C} {hs : L → Prop}
variable {cls' : A → V → V} {ko' : A → ClsOwner C} {c' : C}

/-- **The re-annotation keeps `InsA`** (module docstring §1). -/
theorem insA_narrow (Qv : A → Prop) {μ : A → V} {q : Prog A V L} (h : InsA G Q NP own cls ko c hs μ q) :
    ∀ Wd, InsA G Q NP own cls ko c hs μ (narrowSP cls' ko' c' Qv Wd q) := by
  induction h with
  | done => intro Wd; simp only [narrowSP]; exact .done
  | @rd μ a k h1 _ ih =>
    intro Wd
    have e1 : G a → ∀ μ', FReachA G Q NP own cls ko c hs μ μ' → ∀ u, Q u (μ' a) →
        narrowSP cls' ko' c' Qv Wd (k u) = narrowSP cls' ko' c' Qv Wd (k (μ' a)) :=
      fun hg μ' hR u hu => congrArg (narrowSP cls' ko' c' Qv Wd) (h1 hg μ' hR u hu)
    simp only [narrowSP]
    split_ifs
    · exact .rd e1 (fun μ' hR => ih μ' hR Wd)
    · exact .rdc e1 (fun μ' hR => ih μ' hR Wd)
    · exact .rds e1 (fun μ' hR => ih μ' hR Wd)
  | @rds μ a k h1 _ ih =>
    intro Wd
    simp only [narrowSP]
    exact .rds (fun hg μ' hR u hu => congrArg (narrowSP cls' ko' c' Qv Wd) (h1 hg μ' hR u hu))
      (fun μ' hR => ih μ' hR Wd)
  | @rdc μ a K k h1 _ ih =>
    intro Wd
    have e1 : G a → ∀ μ', FReachA G Q NP own cls ko c hs μ μ' → ∀ u, Q u (μ' a) →
        narrowSP cls' ko' c' Qv Wd (k u) = narrowSP cls' ko' c' Qv Wd (k (μ' a)) :=
      fun hg μ' hR u hu => congrArg (narrowSP cls' ko' c' Qv Wd) (h1 hg μ' hR u hu)
    simp only [narrowSP]
    split_ifs
    · exact .rdc e1 (fun μ' hR => ih μ' hR Wd)
    · exact .rds e1 (fun μ' hR => ih μ' hR Wd)
  | @wr μ a v k h1 _ ih =>
    intro Wd
    simp only [narrowSP]
    exact .wr h1 (fun μ' hR => ih μ' hR (insert a Wd))

/-- **The re-annotation keeps `InsAP`** (module docstring §1; handoff §50c plan step 1). -/
theorem insAP_narrow (Qv : A → Prop) {D : Set A} {μ : A → V} {q : Prog A V L}
    (h : InsAP G Q NP own cls ko c hs D μ q) :
    ∀ Wd, InsAP G Q NP own cls ko c hs D μ (narrowSP cls' ko' c' Qv Wd q) := by
  induction h with
  | done => intro Wd; simp only [narrowSP]; exact .done
  | @rd D μ a k h1 _ ih =>
    intro Wd
    have e1 : G a → ∀ μ', FReachA G Q NP own cls ko c hs μ μ' → ∀ u, Q u (μ' a) →
        narrowSP cls' ko' c' Qv Wd (k u) = narrowSP cls' ko' c' Qv Wd (k (μ' a)) :=
      fun hg μ' hR u hu => congrArg (narrowSP cls' ko' c' Qv Wd) (h1 hg μ' hR u hu)
    simp only [narrowSP]
    split_ifs
    · exact .rd e1 (fun μ' hR => ih μ' hR Wd)
    · exact .rdc e1 (fun μ' hR => ih μ' hR Wd)
    · exact .rds e1 (fun μ' hR => ih μ' hR Wd)
  | @rds D μ a k h1 _ ih =>
    intro Wd
    simp only [narrowSP]
    exact .rds (fun hg μ' hR u hu => congrArg (narrowSP cls' ko' c' Qv Wd) (h1 hg μ' hR u hu))
      (fun μ' hR => ih μ' hR Wd)
  | @rdc D μ a K k h1 _ ih =>
    intro Wd
    have e1 : G a → ∀ μ', FReachA G Q NP own cls ko c hs μ μ' → ∀ u, Q u (μ' a) →
        narrowSP cls' ko' c' Qv Wd (k u) = narrowSP cls' ko' c' Qv Wd (k (μ' a)) :=
      fun hg μ' hR u hu => congrArg (narrowSP cls' ko' c' Qv Wd) (h1 hg μ' hR u hu)
    simp only [narrowSP]
    split_ifs
    · exact .rdc e1 (fun μ' hR => ih μ' hR Wd)
    · exact .rds e1 (fun μ' hR => ih μ' hR Wd)
  | @wr D μ a v k h0 h1 _ ih =>
    intro Wd
    simp only [narrowSP]
    exact .wr h0 h1 (fun μ' hR => ih μ' hR (insert a Wd))

/-- **`InsRun` survives a re-annotation keeping every `G` word in the read set** (module docstring §2). -/
theorem insRun_narrow {Qv : A → Prop} (hGQ : ∀ a, G a → Qv a) (q : Prog A V L) :
    ∀ (Wd : Set A) (ν : A → V), InsRun G Q NP q ν → InsRun G Q NP (narrowSP cls' ko' c' Qv Wd q) ν := by
  induction q with
  | done => intros; simp only [narrowSP, InsRun]
  | lock l k _ => intros; simp only [narrowSP, InsRun]
  | start k _ => intros; simp only [narrowSP, InsRun]
  | rd a k ih =>
    intro Wd ν h
    simp only [InsRun] at h
    simp only [narrowSP]
    split_ifs with h1
    · simp only [InsRun]
      exact ⟨fun hg u hu => congrArg (narrowSP cls' ko' c' Qv Wd) (h.1 hg u hu), ih _ Wd ν h.2⟩
    · simp only [InsRun]
      exact ⟨fun hg => h1 (Or.inl (hGQ a hg)), ih _ Wd ν h.2⟩
    · simp only [InsRun]
      exact ⟨fun hg => h1 (Or.inl (hGQ a hg)), ih _ Wd ν h.2⟩
  | rds a k ih =>
    intro Wd ν h
    simp only [InsRun] at h
    simp only [narrowSP, InsRun]
    exact ⟨h.1, ih _ Wd ν h.2⟩
  | rdc a K k ih =>
    intro Wd ν h
    simp only [InsRun] at h
    simp only [narrowSP]
    split_ifs
    · simp only [InsRun]; exact ⟨h.1, ih _ Wd ν h.2⟩
    · simp only [InsRun]; exact ⟨h.1, ih _ Wd ν h.2⟩
  | wr a v k ih =>
    intro Wd ν h
    simp only [InsRun] at h
    simp only [narrowSP, InsRun]
    exact ⟨h.1, ih (insert a Wd) _ h.2⟩

end narrow

/-! ## 2. Weaker annotations -/

/-- **`q2` is `q1` with weaker annotations** (module docstring §2): the same reads, writes and continuations, a
class read possibly speculative, a class read's relation containing the class equality. -/
inductive AnnLe (cls : A → V → V) : Prog A V L → Prog A V L → Prop
  | done : AnnLe cls .done .done
  | rd {a : A} {k1 k2 : V → Prog A V L} : (∀ v, AnnLe cls (k1 v) (k2 v)) → AnnLe cls (.rd a k1) (.rd a k2)
  | rds {a : A} {k1 k2 : V → Prog A V L} : (∀ v, AnnLe cls (k1 v) (k2 v)) → AnnLe cls (.rds a k1) (.rds a k2)
  | rdc {a : A} {K1 K2 : V → V → Prop} {k1 k2 : V → Prog A V L} : (∀ u w, cls a u = cls a w → K2 u w) →
      (∀ v, AnnLe cls (k1 v) (k2 v)) → AnnLe cls (.rdc a K1 k1) (.rdc a K2 k2)
  | rdcs {a : A} {K1 : V → V → Prop} {k1 k2 : V → Prog A V L} : (∀ v, AnnLe cls (k1 v) (k2 v)) →
      AnnLe cls (.rdc a K1 k1) (.rds a k2)
  | wr {a : A} {v : V} {k1 k2 : Prog A V L} : AnnLe cls k1 k2 → AnnLe cls (.wr a v k1) (.wr a v k2)

section ann
variable {own : (A → V) → A → Owner C L} {cls : A → V → V} {ko : A → ClsOwner C} {c : C} {hs : L → Prop}

/-- **`AltRun` survives a weakening of the annotations.** -/
theorem altRun_annLe {Rp Hp : A → Prop} {q1 q2 : Prog A V L} (h : AnnLe cls q1 q2) :
    ∀ (P : Set A) (ν κ : A → V), AltRun own cls ko c hs Rp Hp P q1 ν κ → AltRun own cls ko c hs Rp Hp P q2 ν κ := by
  induction h with
  | done => intros; simp only [AltRun]
  | rd _ ih =>
    intro P ν κ h
    simp only [AltRun] at h ⊢
    exact ⟨h.1, ih _ P ν κ h.2⟩
  | rds _ ih =>
    intro P ν κ h
    simp only [AltRun] at h ⊢
    exact ⟨h.1, ih _ _ ν κ h.2⟩
  | rdc hK _ ih =>
    intro P ν κ h
    simp only [AltRun] at h ⊢
    exact ⟨h.1, h.2.1, hK, ih _ _ ν κ h.2.2.2⟩
  | rdcs _ ih =>
    intro P ν κ h
    simp only [AltRun] at h ⊢
    exact ⟨h.1, ih _ _ ν κ h.2.2.2⟩
  | wr _ ih =>
    intro P ν κ h
    simp only [AltRun] at h ⊢
    exact ⟨h.1, h.2.1, ih _ _ _ h.2.2⟩

end ann

end
end Fl4Proofs.P2.Serial

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner Prog HeldV PO Safe MoveHeld AltRun Adm Diff RInv InsA InsRun DInvQ
  insA_of_runsQ narrowSP AnnLe altRun_annLe insRun_narrow)

noncomputable section
open Classical

/-- `AnnLe` keeps the words read. -/
theorem reads_annLe {cls : U64 → U64 → U64} {q1 q2 : SP} (h : AnnLe cls q1 q2) :
    ∀ ν, reads q1 ν = reads q2 ν := by
  induction h with
  | done => intro; rfl
  | rd _ ih => intro ν; simp only [reads]; rw [ih]
  | rds _ ih => intro ν; simp only [reads]; rw [ih]
  | rdc _ _ ih => intro ν; simp only [reads]; rw [ih]
  | rdcs _ ih => intro ν; simp only [reads]; rw [ih]
  | wr _ ih => intro ν; simp only [reads]; rw [ih]

/-- The re-annotation keeps the words read. -/
theorem reads_narrow {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {c : U64} {Qv : U64 → Prop} (q : SP) :
    ∀ (Wd : Set U64) (ν : U64 → U64), reads (narrowSP cls ko c Qv Wd q) ν = reads q ν := by
  induction q with
  | done => intros; rfl
  | lock l k _ => intros; rfl
  | start k _ => intros; rfl
  | rd a k ih => intro Wd ν; simp only [narrowSP]; split_ifs <;> simp only [reads] <;> rw [ih]
  | rds a k ih => intro Wd ν; simp only [narrowSP, reads]; rw [ih]
  | rdc a K k ih => intro Wd ν; simp only [narrowSP]; split_ifs <;> simp only [reads] <;> rw [ih]
  | wr a v k ih => intro Wd ν; simp only [narrowSP, reads]; rw [ih]

section annTr
variable {R Qv User : U64 → Prop} {cls : U64 → U64 → U64} {kt kv : U64 → ClsOwner U64} {c : U64}

/-- One read: the certificate's annotation (read set `R ∧ Qv`, class owner `kt`) is at least the armed one's
(`narrowSP … kt … Qv` of the read set `R`, class owner `kv`). -/
theorem annLe_rdN {Wd : Set U64} {q : U64} {k1 k2 : U64 → SP}
    (h : ∀ v, AnnLe cls (k1 v) (narrowSP cls kt c Qv Wd (k2 v))) :
    AnnLe cls (rdN (fun x => R x ∧ Qv x) User cls kt c Wd q k1)
      (narrowSP cls kt c Qv Wd (rdN R User cls kv c Wd q k2)) := by
  have hK : ∀ u w, cls q u = cls q w → (fun u w => cls q u = cls q w) u w := fun _ _ e => e
  unfold rdN
  by_cases c1 : ¬ Racy (fun x => R x ∧ Qv x) User Wd q
  · have c1' : ¬ User q ∧ ((R q ∧ Qv q) ∨ q ∈ Wd) := by unfold Racy at c1; exact not_not.mp c1
    have c2 : ¬ Racy R User Wd q := by
      unfold Racy; exact not_not.mpr ⟨c1'.1, c1'.2.imp_left And.left⟩
    have c3 : Qv q ∨ q ∈ Wd := c1'.2.imp_left And.right
    rw [if_pos c1, if_pos c2]
    simp only [narrowSP]
    rw [if_pos c3]
    exact .rd h
  · rw [if_neg c1]
    have c1' : ¬ (¬ User q ∧ ((R q ∧ Qv q) ∨ q ∈ Wd)) := by unfold Racy at c1; exact not_not.mp c1
    by_cases c2 : ¬ Racy R User Wd q
    · have c2' : ¬ User q ∧ (R q ∨ q ∈ Wd) := by unfold Racy at c2; exact not_not.mp c2
      have hW : q ∉ Wd := fun hw => c1' ⟨c2'.1, Or.inr hw⟩
      have hQ : ¬ (Qv q ∨ q ∈ Wd) := by
        rintro (hq | hw)
        · exact c1' ⟨c2'.1, Or.inl ⟨c2'.2.resolve_right hW, hq⟩⟩
        · exact hW hw
      rw [if_pos c2]
      simp only [narrowSP]
      rw [if_neg hQ]
      by_cases hk : kt q = .gate ∨ kt q = .core c
      · rw [if_pos (show ¬ User q ∧ (kt q = .gate ∨ kt q = .core c) from ⟨c2'.1, hk⟩), if_pos hk]
        exact .rdc hK h
      · rw [if_neg (show ¬ (¬ User q ∧ (kt q = .gate ∨ kt q = .core c)) from fun h' => hk h'.2), if_neg hk]
        exact .rds h
    · rw [if_neg c2]
      by_cases hkv : ¬ User q ∧ (kv q = .gate ∨ kv q = .core c)
      · rw [if_pos hkv]
        simp only [narrowSP]
        by_cases hk : kt q = .gate ∨ kt q = .core c
        · rw [if_pos (show ¬ User q ∧ (kt q = .gate ∨ kt q = .core c) from ⟨hkv.1, hk⟩), if_pos hk]
          exact .rdc hK h
        · rw [if_neg (show ¬ (¬ User q ∧ (kt q = .gate ∨ kt q = .core c)) from fun h' => hk h'.2), if_neg hk]
          exact .rds h
      · rw [if_neg hkv]
        simp only [narrowSP]
        by_cases hk : ¬ User q ∧ (kt q = .gate ∨ kt q = .core c)
        · rw [if_pos hk]; exact .rdcs h
        · rw [if_neg hk]; exact .rds h

variable {A X : Type} (kb : U64) (mk : U64 × U64) (ar : machine.Arch A)

/-- **The certificate's tree is at least the armed one** (module docstring §2). -/
theorem annLe_tr (p : SProg X) :
    ∀ (Wd : Set U64) (a : A), AnnLe cls (tr (fun x => R x ∧ Qv x) User cls kt c kb mk ar p Wd a)
      (narrowSP cls kt c Qv Wd (tr R User cls kv c kb mk ar p Wd a)) := by
  induction p with
  | ret x => intros; simp only [tr, narrowSP]; exact .done
  | err e => intros; simp only [tr, narrowSP]; exact .done
  | zero q n k _ => intros; simp only [tr, narrowSP]; exact .done
  | clr q n k _ => intros; simp only [tr, narrowSP]; exact .done
  | rd q k ih => intro Wd a; simp only [tr]; exact annLe_rdN (fun v => ih v Wd a)
  | rdp q k ih =>
    intro Wd a; simp only [tr]; exact annLe_rdN (fun v => annLe_rdN (fun w => ih (v, w) Wd a))
  | wr q v k ih =>
    intro Wd a
    simp only [tr]
    by_cases hu : User q
    · simp only [hu, ↓reduceIte]; exact ih Wd a
    · simp only [hu, ↓reduceIte, narrowSP]; exact .wr (ih (insert q Wd) a)
  | ksb k ih => intro Wd a; simp only [tr]; exact ih kb Wd a
  | cpu k ih => intro Wd a; simp only [tr]; exact ih c Wd a
  | masks k ih => intro Wd a; simp only [tr]; exact ih mk Wd a
  | arch op k ih =>
    intro Wd a
    by_cases h : ∃ r, callArch ar op a = ok r
    · simp only [tr, dif_pos h]; exact ih _ Wd _
    · simp only [tr, dif_neg h, narrowSP]; exact .done

end annTr

section cert
variable {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {kt : U64 → ClsOwner U64} {User : U64 → Prop}

set_option maxHeartbeats 4000000 in
/-- **`InsA` of the re-annotated translated body from runs at real-valued states** (module docstring §2). -/
theorem insA_narrow_tr_of_states {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop} (hQ : Equivalence Q)
    (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → kt x = .free)
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
      InsT st ar G Q NP User p s a ∧
      Within st ar (fun b => G b → (R b ∧ Qv b) ∧ ¬ User b) (fun _ => True) p s a) :
    InsA G Q NP own cls kt c hs μ (narrowSP cls kt c Qv ∅ (tr R User cls kv c kb mk ar p ∅ a)) := by
  have hRI : RInv own c hs (RpOf (fun x => (R x ∧ Qv x) ∧ True) User Hp) Hp μ :=
    ⟨hH, fun x hx => hx.elim (fun h => hR x h.1 h.2.1) (fun h => Or.inl (hH x h))⟩
  have hAnn := annLe_tr (R := R) (Qv := Qv) (User := User) (cls := cls) (kt := kt) (kv := kv) (c := c) kb mk ar
    p ∅ a
  refine insA_of_runsQ hQ hL hGo hGko (Rp := RpOf (fun x => (R x ∧ Qv x) ∧ True) User Hp) (Hp := Hp) _ ∅ μ
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
  · refine insRun_narrow hGQ _ ∅ ν ?_
    exact insT_sim (L := L) hmk (R := R) (ko := kv) (Rr := fun _ => True) (Wr := Wr)
      (fun x hx => (hWr x hx).1) p s a ∅ ∅ ν
      (Within.mono (fun b hb => ⟨hb, trivial⟩) (fun b hb => hb) p s a hW) hI
      (Within.mono (fun b hb hg => ⟨(hb hg).1.1, (hb hg).2⟩) (fun _ h => h) p s a hGR)
      (once_monoR (R := fun x => R x ∧ Qv x) (R' := R) (fun b hb => hb.1) p ∅ ∅ ∅ s a hN subset_rfl)
      hm hk hc (fun x hx hxa _ _ => hν' x (by rw [← eR]; exact hx) hxa)

end cert

end
end Fl4Proofs.P2.E2E

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once tr reads exists_mem_state OwnDep MasksWr masksOf masksOf_eq InsT insT_of_within
  insA_narrow_tr_of_states)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm InsA narrowSP)

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **`InsA` of the re-annotated body from `safe_tr_wrU`'s data with `InsT`** (module docstring §2). -/
theorem insA_narrow_tr_wrU {X : Type} {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
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
        Once st ar (fun x => R0 x ∧ Qv x) User ∅ ∅ p s a ∧ InsT st ar G Q NP User p s a) :
    InsA G Q NP own cls kt c hs μ
      (narrowSP cls kt c Qv ∅ (tr R0 User cls kv c (L.ksb σ) (masksOf st σ) ar p ∅ a)) := by
  refine insA_narrow_tr_of_states hQ hL hO hmk hGo hGko hGQ (Hp := fun x => Wd x ∧ ¬ User x) p a
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

/-- **`insA_narrow_tr_wrU` when the guard's read and write sets avoid `G`** (module docstring §2): `InsT` by
`insT_of_within`, so `hgo` is exactly `safe_tr_wrU`'s (with `Once` for `R0 ∧ Qv`). -/
theorem insA_narrow_tr_wrU_noG {X : Type} {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt kv : U64 → ClsOwner U64} {User : U64 → Prop} {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop}
    (hQ : Equivalence Q) (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → kt x = .free)
    (hGU : ∀ b, G b → ¬ User b)
    {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64} {σ : S} {a : A} (p : SProg X)
    (hc : L.cpu σ = c) {R0 Qv Rd Ru Wd : U64 → Prop} (hGQ : ∀ b, G b → Qv b)
    (hal : ∀ b, Rd b → Aligned b) (hR0 : ∀ q, Rd q → (R0 q ∧ Qv q) ∧ ¬ User q) (hUa : ∀ b, Ru b → Aligned b)
    (hRuU : ∀ b, Ru b → User b) (hRdG : ∀ b, Rd b → ¬ G b) (hWdG : ∀ b, Wd b → User b ∨ ¬ G b)
    (hWd : ∀ x, Wd x → Aligned x ∧ (¬ User x → HeldV c hs (own μ x)))
    (hRPO : ∀ x, ¬ User x → (R0 x ∧ Qv x) → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∃ r, interp (guard st (fun b => Rd b ∨ Ru b) Wd) ar p s a = ok r ∧
        WithinM st ar (fun x y => StepOK own cls kt User c hs (L.mem x) (L.mem y)) p s a ∧
        Once st ar (fun x => R0 x ∧ Qv x) User ∅ ∅ p s a) :
    InsA G Q NP own cls kt c hs μ
      (narrowSP cls kt c Qv ∅ (tr R0 User cls kv c (L.ksb σ) (masksOf st σ) ar p ∅ a)) := by
  refine insA_narrow_tr_wrU ar hQ hL hO hmk hGo hGko hGU p hc hGQ hal hR0 hUa hRuU hWd hRPO hρμ ?_
  intro s h1 h2 h3
  obtain ⟨r, hg, hWM, hOnce⟩ := hgo s h1 h2 h3
  refine ⟨r, hg, hWM, hOnce, insT_of_within p s a ?_⟩
  exact Within.mono (fun b hb => hb.elim (hRdG b) (fun h hg => hGU b hg (hRuU b h))) hWdG p s a
    (interp_guard _ s a r hg).2

end

end
end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open Fl4Proofs.P2.Serial (InsAP Cfg insAP_narrow)
open Fl4Proofs.P2.E2E (SP)

/-- **`InsAP` of the armed body gives `InsAP` of its re-annotation `annV`** (module docstring §1). -/
theorem insAP_annV {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop} {s : Cfg U64 U64 U64 U64}
    {K : OwnMapP.KLayoutP} {c : U64} {ρ : U64 → U64} {k0 : SP} {D : Set U64} {μ : U64 → U64}
    (h : InsAP G Q NP s.own s.cls s.ko c (fun l => s.lk l = some c) D μ k0) :
    InsAP G Q NP s.own s.cls s.ko c (fun l => s.lk l = some c) D μ (annV s K c ρ k0) :=
  insAP_narrow _ h ∅

end Fl4Proofs.P2.E2EP
