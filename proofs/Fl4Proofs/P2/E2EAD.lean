/-
# P2 (line mmuAD, gen 4): **a started body is run-relatively insensitive when its store runs touch no `G` word**

`SafeCertAD.insA_of_runs` gives `SerialADR.InsA` from sequential-run certificates that read and write no `G` word.
This module builds those certificates from a local path's obligations, exactly as `E2E.body_safe` builds `Safe`'s,
with one extra per-path hypothesis about the real store:

* **`hNG`**: from every entry state `s` satisfying `Pre` and every alternative `s'` of it (`PathObl.Alt`: equal on
  the read set, same core, constants and classes), the store run of the path's tree reads no `G` word and writes
  no non-user `G` word (`Within (¬ G) (User ∨ ¬ G)`). This is the shape of `E2EPCut.back_withinE`'s conclusion
  (from an `AvoidE G` fact) plus the write half.
* `hGo`: owners ignore `G` words (for FL4's rule-8 owners and the paging words: they decide no owner).

Results:
* `noG_rdN`, **`noG_sim`**: the translated body's run on `ν` touches no `G` word when the store run it follows
  (`E2E.sim`'s correspondence: the same values on the words it reads) does not.
* **`body_insA`**: `E2E.body_safe`'s statement with `InsA G Q NP` for `Safe` (any `Q`, `NP`), from `hNG` and `hGo`.
* **`LocalPath.insA`**: a body a local path starts (`StartAt`) is `InsA`.

No premise: everything is a hypothesis of the theorems. No existing statement changed.
-/
import Fl4Proofs.P2.E2E
import Fl4Proofs.P2.SafeCertAD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner Prog HeldV PO MoveV Safe MoveHeld AltRun Adm
  Diff RInv WrOK NoGRun InsA DInvG insA_of_runs)

noncomputable section
open Classical

section sim
variable {G : U64 → Prop} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {c : U64} {R User : U64 → Prop}

theorem noG_rdN {Wd : Set U64} {q : U64} {k : U64 → SP} {ν : U64 → U64} (hg : ¬ G q)
    (h : NoGRun G (k (ν q)) ν) : NoGRun G (rdN R User cls ko c Wd q k) ν := by
  unfold rdN
  by_cases ha : ¬ Racy R User Wd q
  · rw [if_pos ha]; exact ⟨hg, h⟩
  · rw [if_neg ha]
    by_cases hb : ¬ User q ∧ (ko q = .gate ∨ ko q = .core c)
    · rw [if_pos hb]; exact ⟨hg, h⟩
    · rw [if_neg hb]; exact ⟨hg, h⟩

variable {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}

/-- **The translated body's run on `ν` touches no `G` word when the store run it follows does not**
(`E2E.sim`'s correspondence hypotheses). -/
theorem noG_sim (hmk : MasksWr st) {kb : U64} {mk : U64 × U64} {Rr Wr : U64 → Prop}
    (hWr : ∀ x, Wr x → Aligned x) (p : SProg X) :
    ∀ (s : S) (a : A) (Wd T : Set U64) (ν : U64 → U64),
      Within st ar (fun b => Aligned b ∧ Rr b) Wr p s a →
      Within st ar (fun b => ¬ G b) (fun b => User b ∨ ¬ G b) p s a →
      Once st ar R User Wd T p s a →
      st.frame_masks s = ok mk → L.ksb s = kb → L.cpu s = c →
      (∀ x ∈ reads (tr R User cls ko c kb mk ar p Wd a) ν, Aligned x → Rr x →
        (¬ User x ∨ x ∉ T) → L.mem s x = ν x) →
      NoGRun G (tr R User cls ko c kb mk ar p Wd a) ν := by
  induction p with
  | ret x => intros; simp only [tr, NoGRun]
  | err e => intros; simp only [tr, NoGRun]
  | zero q n k ih => intros; simp only [tr, NoGRun]
  | clr q n k ih => intros; simp only [tr, NoGRun]
  | rd q k ih =>
    intro s a Wd T ν hW hG hN hm hk hc hν
    simp only [Within] at hW hG
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    rw [reads_rdN] at hν
    obtain ⟨⟨hal, hr⟩, hW⟩ := hW
    obtain ⟨hg, hG⟩ := hG
    obtain ⟨ho, hN⟩ := hN
    have hu : ¬ User q ∨ q ∉ T := by
      by_cases hu : User q
      · exact Or.inr (ho fun h => h.1 hu)
      · exact Or.inl hu
    have e : L.mem s q = ν q := hν q (List.mem_cons_self ..) hal hr hu
    have hrd : st.read s q = ok (ν q) := by rw [← e]; exact L.read_eq s q
    refine noG_rdN hg (ih (ν q) s a Wd _ ν (hW _ hrd) (hG _ hrd) (hN _ hrd) hm hk hc ?_)
    intro x hx hxa hxr hxu
    exact hν x (List.mem_cons_of_mem _ hx) hxa hxr (hxu.imp_right fun h hT => h (tch_sub hT))
  | rdp q k ih =>
    intro s a Wd T ν hW hG hN hm hk hc hν
    simp only [Within] at hW hG
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    rw [reads_rdN, reads_rdN] at hν
    have hrp := L.read_pair_eq s q
    generalize core.num.U64.wrapping_add q 8#u64 = q8 at *
    obtain ⟨⟨hal, hr⟩, ⟨hal8, hr8⟩, hW⟩ := hW
    obtain ⟨hg, hg8, hG⟩ := hG
    obtain ⟨ho, ho8, hN⟩ := hN
    have hu : ¬ User q ∨ q ∉ T := by
      by_cases hu : User q
      · exact Or.inr (ho fun h => h.1 hu)
      · exact Or.inl hu
    have hu8 : ¬ User q8 ∨ q8 ∉ T := by
      by_cases hu : User q8
      · exact Or.inr fun h => ho8 (fun h => h.1 hu) (tch_sub h)
      · exact Or.inl hu
    have e : L.mem s q = ν q := hν q (List.mem_cons_self ..) hal hr hu
    have e8 : L.mem s q8 = ν q8 :=
      hν q8 (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hal8 hr8 hu8
    have hrd : st.read_pair s q = ok (ν q, ν q8) := by rw [hrp, e, e8]
    refine noG_rdN hg (noG_rdN hg8 (ih (ν q, ν q8) s a Wd _ ν (hW _ hrd) (hG _ hrd) (hN _ hrd) hm hk hc ?_))
    intro x hx hxa hxr hxu
    exact hν x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) hxa hxr
      (hxu.imp_right fun h hT => h (tch_sub (tch_sub hT)))
  | wr q v k ih =>
    intro s a Wd T ν hW hG hN hm hk hc hν
    simp only [Within] at hW hG
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    have hw := L.write_eq s q v
    obtain ⟨hWq, hW⟩ := hW
    have hW := hW _ hw
    obtain ⟨hGq, hG⟩ := hG
    have hG := hG _ hw
    have hN := hN _ hw
    have hal := hWr q hWq
    have hm' : st.frame_masks (L.wr s q v) = ok mk := by rw [hmk]; exact hm
    have hk' : L.ksb (L.wr s q v) = kb := by rw [L.ksb_wr]; exact hk
    have hc' : L.cpu (L.wr s q v) = c := by rw [L.cpu_wr]; exact hc
    by_cases hu : User q
    · rw [if_pos hu] at hN hν ⊢
      rw [if_pos hu] at hN
      refine ih _ a Wd _ ν hW hG hN hm' hk' hc' ?_
      intro x hx hxa hxr hxu
      have hne : q ≠ x := by
        rintro rfl
        rcases hxu with h | h
        · exact h hu
        · exact h (Set.mem_insert _ _)
      rw [L.mem_wr s q v x hal hxa, if_neg hne]
      exact hν x hx hxa hxr (hxu.imp_right fun h hT => h (Set.mem_insert_of_mem _ hT))
    · rw [if_neg hu] at hN hν ⊢
      rw [if_neg hu] at hN
      simp only [reads] at hν
      simp only [NoGRun]
      refine ⟨hGq.resolve_left hu, ih _ a _ T _ hW hG hN hm' hk' hc' ?_⟩
      intro x hx hxa hxr hxu
      rw [L.mem_wr s q v x hal hxa]
      by_cases hne : q = x
      · subst hne; rw [if_pos rfl, Function.update_self]
      · rw [if_neg hne, Function.update_of_ne (Ne.symm hne)]; exact hν x hx hxa hxr hxu
  | ksb k ih =>
    intro s a Wd T ν hW hG hN hm hk hc hν
    simp only [Within] at hW hG
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    have h : st.ks_base s = ok kb := by rw [← hk]; exact L.ks_base_eq s
    exact ih kb s a Wd T ν (hW _ h) (hG _ h) (hN _ h) hm hk hc hν
  | cpu k ih =>
    intro s a Wd T ν hW hG hN hm hk hc hν
    simp only [Within] at hW hG
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    have h : st.cur_cpu s = ok c := by rw [← hc]; exact L.cur_cpu_eq s
    exact ih c s a Wd T ν (hW _ h) (hG _ h) (hN _ h) hm hk hc hν
  | masks k ih =>
    intro s a Wd T ν hW hG hN hm hk hc hν
    simp only [Within] at hW hG
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    exact ih mk s a Wd T ν (hW _ hm) (hG _ hm) (hN _ hm) hm hk hc hν
  | arch op k ih =>
    intro s a Wd T ν hW hG hN hm hk hc hν
    simp only [Within] at hW hG
    simp only [Once] at hN
    by_cases hca : ∃ r, callArch ar op a = ok r
    · have e := hca.choose_spec
      simp only [tr, dif_pos hca] at hν ⊢
      exact ih _ s _ Wd T ν (hW _ _ e) (hG _ _ e) (hN _ _ e) hm hk hc hν
    · simp only [tr, dif_neg hca, NoGRun]

end sim

/-! ## A started body is run-relatively insensitive -/

section body
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {User : U64 → Prop}
  {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
  {F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (X × S × A)}
  {p : SProg X} {Acc : X → Prop} {Locks : S → U64 → Prop} {Pre : S → Prop}
  {RS WS DS : S → U64 → Prop}

/-- **A body is `InsA` when it starts** (`body_safe` with `InsA` for `Safe`), from its per-path obligations
and `hNG`: its store runs from every alternative of an entry state touch no `G` word. -/
theorem body_insA {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop}
    (hL : MoveHeld own) (hO : OwnDep own User)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m')
    (hp : IsProgOn (F ar) ar st (AltOf st Pre RS cls ko User) p)
    (O : PathObl st (F ar) Acc own cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS)
    (hN : ReadOnce st ar p cls ko User Pre RS) (hT : ∀ s a, ∃ r, F ar st s a = ok r)
    (hmk : MasksWr st)
    (hNG : ∀ s s' a, Pre s → Alt st (RS s) cls ko User s s' →
      Within st ar (fun b => ¬ G b) (fun b => User b ∨ ¬ G b) p s' a)
    {σ : S} {a : A} (hpre : Pre σ) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → ¬ User x → L.mem σ x = μ x) :
    InsA G Q NP own cls ko (L.cpu σ) (Locks σ) μ
      (tr (RS σ) User cls ko (L.cpu σ) (L.ksb σ) (masksOf st σ) ar p ∅ a) := by
  have e0 : own (L.mem σ) = own μ := hO _ _ hμ
  let Hp : U64 → Prop := fun x => ¬ User x ∧ (WS σ x ∨ DS σ x)
  have hRI : RInv own (L.cpu σ) (Locks σ) (RpOf (RS σ) User Hp) Hp μ := by
    have hH : ∀ x, Hp x → HeldV (L.cpu σ) (Locks σ) (own μ x) := by
      intro x hx
      rw [← e0]; exact heldBy_iff.mp (O.write_own σ x hpre hx.2 hx.1)
    refine ⟨hH, fun x hx => ?_⟩
    rcases hx with ⟨hu, hr⟩ | hx
    · rw [← e0]
      rcases O.read_own σ x hpre hr hu with h | h
      · exact Or.inl (heldBy_iff.mp h)
      · exact Or.inr h
    · exact Or.inl (hH x hx)
  refine insA_of_runs hL hGo (Rp := RpOf (RS σ) User Hp) (Hp := Hp) _ ∅ μ
    (fun _ => none) ⟨fun ν hν => ?_, fun y u hu => (by cases hu), fun y u hu => (by cases hu),
      fun y u hu => (by cases hu), hRI, fun y u hu => (by cases hu)⟩
  have hνR : ∀ x, ¬ User x → RS σ x → ν x = μ x := fun x hu hr => hν.1 x (hRI.2 x (Or.inl ⟨hu, hr⟩))
  generalize hq : tr (RS σ) User cls ko (L.cpu σ) (L.ksb σ) (masksOf st σ) ar p ∅ a = q
  let rl := (reads q ν).filter (fun x => decide (Aligned x))
  let ul := rl.filter (fun x => decide (User x))
  let kl := rl.filter (fun x => decide (¬ User x))
  have hul : ∀ x, x ∈ ul ↔ (x ∈ reads q ν ∧ Aligned x) ∧ User x := by
    intro x; simp only [ul, rl, List.mem_filter, decide_eq_true_eq]
  have hkl : ∀ x, x ∈ kl ↔ (x ∈ reads q ν ∧ Aligned x) ∧ ¬ User x := by
    intro x; simp only [kl, rl, List.mem_filter, decide_eq_true_eq]
  obtain ⟨σu, hσu⟩ : ∃ s, s = wrs st ν ul σ := ⟨_, rfl⟩
  obtain ⟨σν, hσν⟩ : ∃ s, s = wrs st ν kl σu := ⟨_, rfl⟩
  obtain ⟨uP, uL, uR, uW, uD⟩ := wrs_user st Sd (ν := ν) ul σ
    (fun x hx => ⟨((hul x).mp hx).2, ((hul x).mp hx).1.2⟩) hpre
  obtain ⟨uc, ub, um⟩ := wrs_const st (ν := ν) hmk ul σ
  have uM := wrs_mem st (ν := ν) ul σ (fun x hx => ((hul x).mp hx).1.2)
  rw [← hσu] at uP uL uR uW uD uc ub um uM
  obtain ⟨kc, kb, km⟩ := wrs_const st (ν := ν) hmk kl σu
  have kM := wrs_mem st (ν := ν) kl σu (fun x hx => ((hkl x).mp hx).1.2)
  rw [← hσν] at kc kb km kM
  have hmσ := masksOf_eq st σ
  have uMk : ∀ x, Aligned x → ¬ User x → L.mem σu x = μ x := by
    intro x hx hu
    rw [uM x hx, if_neg (fun h => hu ((hul x).mp h).2)]; exact hμ x hx hu
  obtain ⟨ru, hru⟩ := hT σu a
  by_cases hacc : Acc ru.1
  · -- accepted at `σu`
    have gu : AltOf st Pre RS cls ko User σu := AltOf.pre uP
    have hW := O.acc σu a ru uP hru hacc
    rw [hp _ (Narrow.guard _ _ _) σu gu a] at hW
    have hW := (interp_guard p σu a ru hW).2
    have hA := Sd.read_aligned σu σu a ru uP (Alt.refl σu) hru
    rw [hp _ (Narrow.guard _ _ _) σu gu a] at hA
    have hA := (interp_guard p σu a ru hA).2
    have hM := O.move_steps hp uP gu hru
    have hO1 := hN σu σu a ru uP (Alt.refl σu) (by rw [← hp _ (Narrow.self st) σu gu a]; exact hru)
    have hG := hNG σu σu a uP (Alt.refl σu)
    rw [uR] at hW hO1; rw [uW] at hW; rw [uc, uL] at hM
    have hWa : ∀ x, True ∧ WS σ x → Aligned x ∧ (¬ User x → Hp x) := fun x hx =>
      ⟨O.aligned σ x hpre (Or.inl hx.2), fun hu => ⟨hu, Or.inl hx.2⟩⟩
    have hνa : ∀ x ∈ reads q ν, Aligned x → RS σ x → (¬ User x ∨ x ∉ (∅ : Set U64)) →
        L.mem σu x = ν x := by
      intro x hx hxa hxr _
      by_cases hu : User x
      · rw [uM x hxa, if_pos ((hul x).mpr ⟨⟨hx, hxa⟩, hu⟩)]
      · rw [uMk x hxa hu, hνR x hu hxr]
    rw [← hq] at hνa ⊢
    exact ⟨μ, fun y hy => absurd rfl hy,
      sim (L := L) hO hmk (Rr := RS σ) (Wr := fun x => True ∧ WS σ x) hWa p σu a ∅ ∅ ∅ ν μ
        (within_and p σu a hA hW) hM hO1 (fun x hx => absurd hx (Set.notMem_empty x)) subset_rfl
        (um.trans hmσ) ub uc (fun x hx hu => (uMk x hx hu).symm) hνa,
      noG_sim (L := L) hmk (Rr := RS σ) (Wr := fun x => True ∧ WS σ x) (fun x hx => (hWa x hx).1) p σu a
        ∅ ∅ ν (within_and p σu a hA hW) hG hO1 (um.trans hmσ) ub uc hνa⟩
  · -- declined at `σu`
    have hAlt : Alt st (RS σu) cls ko User σu σν := by
      refine ⟨kc, kb, km, fun x hx => ?_, fun x hx hu hko => ?_⟩
      · have hxa := Sd.rs_aligned σu x uP hx
        rw [uR] at hx
        rw [kM x hxa]
        split_ifs with h
        · have hu := ((hkl x).mp h).2
          rw [hνR x hu hx, uMk x hxa hu]
        · rfl
      · have hxa : Aligned x := Sd.ko_aligned x (by rcases hko with h | h <;> rw [h] <;> simp)
        rw [kM x hxa]
        split_ifs with h
        · rw [uc] at hko
          rw [hν.2.2 x hko, uMk x hxa hu]
        · rfl
    obtain ⟨rν, hrν⟩ := hT σν a
    have gν : AltOf st Pre RS cls ko User σν := ⟨σu, uP, hAlt⟩
    obtain ⟨-, hW, hM⟩ := O.dec_alt σu a ru uP hru hacc σν rν hAlt hrν
    rw [hp _ (Narrow.guard _ _ _) σν gν a] at hW
    rw [hp _ (Narrow.mguard _ _) σν gν a] at hM
    have hW := (interp_guard p σν a rν hW).2
    have hM := (interp_mguard p σν a rν hM).2
    have hA := Sd.read_aligned σu σν a rν uP hAlt hrν
    rw [hp _ (Narrow.guard _ _ _) σν gν a] at hA
    have hA := (interp_guard p σν a rν hA).2
    have hO1 := hN σu σν a rν uP hAlt (by rw [← hp _ (Narrow.self st) σν gν a]; exact hrν)
    have hG := hNG σu σν a uP hAlt
    rw [uR] at hO1; rw [uD] at hW; rw [uc, uL] at hM
    have hWa : ∀ x, True ∧ DS σ x → Aligned x ∧ (¬ User x → Hp x) := fun x hx =>
      ⟨O.aligned σ x hpre (Or.inr hx.2), fun hu => ⟨hu, Or.inr hx.2⟩⟩
    have hνa : ∀ x ∈ reads q ν, Aligned x → True → (¬ User x ∨ x ∉ (∅ : Set U64)) →
        L.mem σν x = ν x := by
      intro x hx hxa _ _
      rw [kM x hxa]
      by_cases hu : User x
      · rw [if_neg (fun h => ((hkl x).mp h).2 hu), uM x hxa,
          if_pos ((hul x).mpr ⟨⟨hx, hxa⟩, hu⟩)]
      · rw [if_pos ((hkl x).mpr ⟨⟨hx, hxa⟩, hu⟩)]
    refine ⟨fun x => if Aligned x ∧ ¬ User x then L.mem σν x else μ x, fun y hy hpo => ?_, ?_⟩
    · apply hy
      beta_reduce
      split_ifs with h
      · rw [kM y h.1, uMk y h.1 h.2]
        split_ifs
        · exact hν.1 y hpo
        · rfl
      · rfl
    · rw [← hq] at hνa ⊢
      exact ⟨sim (L := L) hO hmk (Rr := fun _ => True) (Wr := fun x => True ∧ DS σ x) hWa p σν a
        ∅ ∅ ∅ ν _ (within_and p σν a hA hW) hM hO1 (fun x hx => absurd hx (Set.notMem_empty x))
        subset_rfl (km.trans (um.trans hmσ)) (kb.trans ub) (kc.trans uc)
        (fun x hx hu => if_pos ⟨hx, hu⟩) hνa,
        noG_sim (L := L) hmk (Rr := fun _ => True) (Wr := fun x => True ∧ DS σ x) (fun x hx => (hWa x hx).1)
          p σν a ∅ ∅ ν (within_and p σν a hA hW) hG hO1 (km.trans (um.trans hmσ)) (kb.trans ub)
          (kc.trans uc) hνa⟩

end body

section top
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **A body a local path starts is run-relatively insensitive** to `G`, when its store runs from every
alternative of an entry state touch no `G` word (`hNG`) and owners ignore `G` words (`hGo`). -/
theorem LocalPath.insA (P : LocalPath own cls ko User) {G : U64 → Prop} {Q : U64 → U64 → Prop}
    {NP : U64 → Prop} (hL : MoveHeld own) (hO : OwnDep own User)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m')
    (hNG : ∀ s s' a, P.Pre s → @Alt P.S P.st P.L (P.RS s) cls ko User s s' →
      Within P.st P.ar (fun b => ¬ G b) (fun b => User b ∨ ¬ G b) P.p s' a)
    {c : U64} {hs : U64 → Prop} {μ : U64 → U64} {q : SP}
    (h : StartAt P c hs μ q) : InsA G Q NP own cls ko c hs μ q := by
  obtain ⟨σ, a, hpre, rfl, rfl, hμ, rfl⟩ := h
  let _ := P.L
  exact body_insA hL hO hGo P.isProg P.obl P.side P.once P.total P.masks hNG hpre hμ

end top

end

end Fl4Proofs.P2.E2E
