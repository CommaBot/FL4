/-
P2 (line nscope, gen 7): **`StartQPB` discharged** — `serializable_fl4_localW11PJ2`, whose start fact is W11's
`StartP3W11` [P] with the armed program the PTE-cut relabelling of its annotation.

**Are the two bodies equal?** No, not in general. `LocalPath.body P σ a` is `tr (P.RS σ) …`, the trait-call tree
translated *with the path's read set*: a read of `q` becomes `.rd` when `q` is a non-user word of `RS` (or written
before), else `.rdc` / `.rds` (`rdN`). The cut path has the read set `rsE E RS = RS ∖ E` (`LocalPath.cutE`; `restrQ`,
`liftP` keep `F`, `p`, `ar`, the store), so every read node of the ownV body at a PTE word that the path has not
written becomes `.rds` (PTEs have `ko = .free`) in the cut body. The tree branches over every read value, so some
branch of every slot whose addresses depend on read values reaches a PTE word: the bodies differ as trees for all
eight slots alike (not specially sl / vt; the program, `F` and `p`, is the same `Fl4Core` call).

**But the cut body is a function of the ownV body.** `cutP E User cls ko c Wd q0` relabels, along the tree (tracking
the words written, `Wd`), each `.rd` of a word of `E` not in `Wd` to the read kind `rdN` gives an unpermitted word
(`.rdc` if the class owner is the gate or this core, else `.rds`), and keeps every other node. **`tr_cut`**:
`tr (RS ∖ E) … t Wd a = cutP E … Wd (tr RS … t Wd a)` (induction on the trait-call tree; `rdN_cut` at a read).
**`body_cutLiftP`**: the cut-and-lifted path's body is `cutP (· ∈ K.ptes) … (P.L.cpu σ) (P.body σ a) ∅`.
So the glue can pick the cut body definitionally: **`StartP3W11JC`** = `∃ q0, StartP3W11 … q0 i ∧ q = cutP … c q0 ∅`
— the armed program is computed from W11's annotation `q0` (the relabelling changes only read kinds: the same
addresses, the same memory effect; the `.rds` reads are of PTE words, which the path never reads, `allW11J`).
**`startQPB_of`**: that `q` satisfies `StartQPB` at every start state. **`ExecWPJ.mono`**, and
**`serializable_fl4_localW11PJ2`**: `serializable_fl4_localW11PJ` with `StartP3W11JC` starts. Premises: as W11PJ
with `StartP3W11` [P] in place of `StartP3W11` [P] ∧ `StartQPB` [P].

No new premise; no existing statement or file changed.
-/
import Fl4Proofs.P2.E2EPW11J
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep tr rdN Racy masksOf)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg Prog)

noncomputable section
open Classical

/-! ## The relabelling -/

/-- **The PTE-cut relabelling of a translated body** (module docstring). -/
def cutP (E User : U64 → Prop) (cls : U64 → U64 → U64) (ko : U64 → ClsOwner U64) (c : U64) : SP → Set U64 → SP
  | .done, _ => .done
  | .rd q k, Wd =>
      if E q ∧ q ∉ Wd then
        (if ¬ User q ∧ (ko q = .gate ∨ ko q = .core c) then
          .rdc q (fun u w => cls q u = cls q w) (fun v => cutP E User cls ko c (k v) Wd)
        else .rds q (fun v => cutP E User cls ko c (k v) Wd))
      else .rd q (fun v => cutP E User cls ko c (k v) Wd)
  | .wr q v k, Wd => .wr q v (cutP E User cls ko c k (insert q Wd))
  | .lock l k, Wd => .lock l (fun b => cutP E User cls ko c (k b) Wd)
  | .rds q k, Wd => .rds q (fun v => cutP E User cls ko c (k v) Wd)
  | .start k, Wd => .start (cutP E User cls ko c k Wd)
  | .rdc q K k, Wd => .rdc q K (fun v => cutP E User cls ko c (k v) Wd)

section trcut
variable (R E User : U64 → Prop) (cls : U64 → U64 → U64) (ko : U64 → ClsOwner U64) (c : U64)

/-- **One read**: the cut read set's translation is the relabelled one. -/
theorem rdN_cut (Wd : Set U64) (q : U64) (k : U64 → SP) :
    rdN (fun x => R x ∧ ¬ E x) User cls ko c Wd q (fun v => cutP E User cls ko c (k v) Wd) =
      cutP E User cls ko c (rdN R User cls ko c Wd q k) Wd := by
  simp only [rdN, Racy]
  by_cases h1 : ¬ ¬ (¬ User q ∧ (R q ∨ q ∈ Wd))
  · by_cases h2 : E q ∧ q ∉ Wd
    · have h3 : ¬ ¬ ¬ (¬ User q ∧ ((R q ∧ ¬ E q) ∨ q ∈ Wd)) := by
        intro hn; apply hn; rintro ⟨-, h | h⟩
        · exact h.2 h2.1
        · exact h2.2 h
      simp only [eq_true h1, eq_false h3, eq_true h2, cutP, ↓reduceIte]
    · have h3 : ¬ ¬ (¬ User q ∧ ((R q ∧ ¬ E q) ∨ q ∈ Wd)) := by
        intro hn; apply hn
        have h1' := not_not.mp h1
        refine ⟨h1'.1, ?_⟩
        by_cases hw : q ∈ Wd
        · exact Or.inr hw
        · rcases h1'.2 with hr | hw'
          · exact Or.inl ⟨hr, fun he => h2 ⟨he, hw⟩⟩
          · exact absurd hw' hw
      simp only [eq_true h1, eq_true h3, eq_false h2, cutP, ↓reduceIte]
  · have h3 : ¬ ¬ ¬ (¬ User q ∧ ((R q ∧ ¬ E q) ∨ q ∈ Wd)) := by
      intro hn; apply h1; intro hn'; apply hn; intro ⟨hu, h⟩
      apply hn'; refine ⟨hu, ?_⟩
      rcases h with h | h
      · exact Or.inl h.1
      · exact Or.inr h
    by_cases h4 : ¬ User q ∧ (ko q = .gate ∨ ko q = .core c)
    · simp only [eq_false h1, eq_false h3, eq_true h4, cutP, ↓reduceIte]
    · simp only [eq_false h1, eq_false h3, eq_false h4, cutP, ↓reduceIte]

variable (kb : U64) (mk : U64 × U64) {A X : Type} (ar : machine.Arch A)

/-- **The cut read set's translation is the relabelled translation** (module docstring). -/
theorem tr_cut (t : SProg X) (Wd : Set U64) (a : A) :
    tr (fun x => R x ∧ ¬ E x) User cls ko c kb mk ar t Wd a =
      cutP E User cls ko c (tr R User cls ko c kb mk ar t Wd a) Wd := by
  induction t generalizing Wd a with
  | ret x => simp only [tr, cutP]
  | err e => simp only [tr, cutP]
  | rd q k ih =>
    simp only [tr]
    rw [← rdN_cut]
    congr 1
    funext v
    exact ih v Wd a
  | rdp q k ih =>
    simp only [tr]
    rw [← rdN_cut]
    congr 1
    funext v
    rw [← rdN_cut]
    congr 1
    funext w
    exact ih (v, w) Wd a
  | wr q v k ih =>
    simp only [tr]
    by_cases hu : User q
    · rw [@if_pos _ _ hu, @if_pos _ _ hu]; exact ih Wd a
    · rw [@if_neg _ _ hu, @if_neg _ _ hu]; simp only [cutP]; rw [ih]
  | zero _ _ _ _ => simp only [tr, cutP]
  | clr _ _ _ _ => simp only [tr, cutP]
  | ksb k ih => simp only [tr]; exact ih _ Wd a
  | cpu k ih => simp only [tr]; exact ih _ Wd a
  | masks k ih => simp only [tr]; exact ih _ Wd a
  | arch op k ih =>
    simp only [tr]
    by_cases h : ∃ r, callArch ar op a = ok r
    · rw [dif_pos h, dif_pos h]; exact ih _ Wd _
    · rw [dif_neg h, dif_neg h]; simp only [cutP]

end trcut

/-- **The cut-and-lifted path's body is the relabelled body.** -/
theorem body_cutLiftP {K : KLayoutP} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop}
    (hK : RegionOKP K) (hU : UserOKP K) (hko : ∀ x, x ∈ K.ptes → ko x = .free)
    (P : E2E.LocalPath (ownV K.toKLayoutV) cls ko User) (hAv : AvoidP K P) (σ : P.S) (a : P.A) :
    (LocalPath.cutLiftP hK hU hko P hAv).body σ a =
      cutP (· ∈ K.ptes) User cls ko (P.L.cpu σ) (P.body σ a) ∅ := by
  letI := P.L
  exact tr_cut (P.RS σ) (· ∈ K.ptes) User cls ko (P.L.cpu σ) (P.L.ksb σ) (masksOf P.st σ) P.ar P.p ∅ a

/-! ## The start fact and the top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The W11 start fact, the armed program cut** (module docstring): `StartP3W11` [P] for some annotation `q0`, the
armed program its PTE-cut relabelling. -/
def StartP3W11JC (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K)
    (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : Fl4IxW (S := S)) : Prop :=
  ∃ q0, StartP3W11 st ar hA hm hSt a0 arI AR MR Ch K.toKLayoutV m hK.base hU.base c hs q0 i ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

variable {arI AR MR}

/-- **The relabelled annotation is the cut body at every start state** (`StartQPB` discharged). -/
theorem startQPB_of (i : Fl4IxW (S := S)) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (c : U64) (hs : U64 → Prop) (q0 : SP) :
    StartQPB ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
      (fl4LocW11J st ar hA hm hSt a0 i K m hK hU) rfl rfl c hs m q0
      (cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅) := by
  intro σ a _ hc _ _ e
  show _ = (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (allW11J st ar hA hm hSt a0 i K m hK hU)).body σ a
  refine Eq.trans ?_ (body_cutLiftP hK hU (fun x hx => ko_pte hK hx m) _
    (allW11J st ar hA hm hSt a0 i K m hK hU) σ a).symm
  change _ = cutP _ _ _ _
    (((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).L.cpu σ)
    (((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).body σ a) ∅
  rw [hc, ← e]

/-- **`ExecWPJ` is monotone in the start fact.** -/
theorem ExecWPJ.mono {ι : Type} {LP : PathsP ι}
    {SF SF' : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι →
      Prop}
    (hSF : ∀ Ch K m hK hU c hs q i, SF Ch K m hK hU c hs q i → SF' Ch K m hK hU c hs q i)
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop}
    (h : ExecWPJ LP SF P s0 K0 Ch0 s K Ch) : ExecWPJ LP SF' P s0 K0 Ch0 s K Ch := by
  induction h with
  | refl => exact .refl
  | step _ hS g ih =>
    refine .step ih hS ⟨g.arm, fun p0 k W hph hK hU => ?_, g.serX, g.serC, g.serG, g.keep⟩
    obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
    exact ⟨i, hSF _ _ _ _ _ _ _ _ _ hi⟩
  | hw _ hH ih => exact .hw ih hH

/-- **FL4 end to end, W11's family and glue, rule 8 with the PTE set by convention, W11's start fact** (module
docstring): `serializable_fl4_localW11PJ` with the start fact `StartP3W11JC` (`StartP3W11` [P], armed program the
relabelled annotation); `StartQPB` gone. -/
theorem serializable_fl4_localW11PJ2 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesCanon st K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPJ (fl4LocW11J st ar hA hm hSt a0) (StartP3W11JC st ar hA hm hSt a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  have hm' : ExecWPJ (fl4LocW11J st ar hA hm hSt a0) (StartP3W11JB st ar hA hm hSt a0 arI AR MR) P s0 K0 Ch0 s K Ch := by
    refine ExecWPJ.mono st (fun Ch K m hK hU c hs q i hsf => ?_) h
    obtain ⟨q0, hW, rfl⟩ := hsf
    exact ⟨q0, hW, startQPB_of st ar hA hm hSt a0 i K m hK hU c hs q0⟩
  exact serializable_fl4_localW11PJ st ar hA hm hSt a0 P hIoa h0 hA0 hB hc0 hM0 hm' hq

end top

end
end Fl4Proofs.P2.E2EP
