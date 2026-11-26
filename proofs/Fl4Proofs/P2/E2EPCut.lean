/-
P2 (line pte, gen 2): **cutting a path's read set off an arbitrary excluded word set `E`** (`LocalPath.cutE`), the
generalisation of `E2EVCutP.cutV` (which cuts `VData K` off a path for `OwnMap.own`; it stays as it is), and its
**instance for rule 8** (`LocalPath.cutLiftP`, `PathsP.ofVCut`): every `ownV` path lifts to `ownP` with the PTE
words cut out of its read set, given **`AvoidP` [W]** (its runs read no PTE word).

Generic part (`E2EVCutP`'s argument with `VData K` replaced by `E` and `OwnMap.own K` by any `own`):
* `rsE E RS s x := RS s x ∧ ¬ E x`; `AvAccE` / `AvDecE` / **`AvoidE` [W]** (`acc`: an accepted run is a run on the
  store guarded to `rsE E RS s`; `dec`: from every alternative of a declining entry the run reads no `E` word;
  `prog` [P]: the program premise at the cut set's alternatives);
* `alt_backE`, `dec_withinE`, `acc_withinE`, `back_withinE`, `cut_read_alignedE`, `cut_onceE`, `stepOK_agoffE`,
  `cut_dec_altE`: as `E2EVCutP`'s, with two hypotheses in place of `RegionOKV` / `UserOKV`: `hoc` (`own` reads no
  `E` word: two memories equal on the aligned words outside `E` have the same owners) and `hko` (`ko` is `.free`
  on `E`);
* **`LocalPath.cutE hoc hko P hAv`**: `P` with `ReadSet := rsE E P.RS`; `avoidE_of_noPre` (a path that never starts),
  `avoidE_bot` (`E = ⊥`: every path, from its own obligations).

Rule 8 (`E := (· ∈ K.ptes)` on an `ownV` path at `K.toKLayoutV`): `hoc` is `ownV_congr` (a `DecW` word is aligned,
not user, not a PTE: `pte_nondec`), `hko` is `ko_pte`; the cut path has `NoPteRd` by definition, so `liftP` applies:
**`LocalPath.cutLiftP`**, **`PathsP.ofVCut LP hAv`** (each `ownV` path cut and lifted, given `AvoidP` [W] at every
layout), `avoidP_empty` (`K.ptes = ∅`: no premise).

Premises: `AvoidP` [W] per lifted path and layout (`AvoidE` at `E = (· ∈ K.ptes)`); `RegionOKP` / `UserOKP` [J].
-/
import Fl4Proofs.P2.E2EP
import Fl4Proofs.P2.E2EVCutP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.Serial (Owner ClsOwner)

noncomputable section
open Classical

/-- The read set `RS` cut off the words of `E`. -/
def rsE {S : Type} (E : U64 → Prop) (RS : S → U64 → Prop) (s : S) (x : U64) : Prop := RS s x ∧ ¬ E x

/-- Aligned words outside `E`. -/
def GE (E : U64 → Prop) (b : U64) : Prop := Aligned b ∧ ¬ E b

/-- Alternatives of an entry for the old read set or for the cut one. -/
def AltCutE {S : Type} (E : U64 → Prop) (st : machine.Store S) [LawfulStore st] (Pre : S → Prop)
    (RS : S → U64 → Prop) (cls : U64 → U64 → U64) (ko : U64 → ClsOwner U64) (User : U64 → Prop) (σ : S) : Prop :=
  AltOf st Pre RS cls ko User σ ∨ AltOf st Pre (rsE E RS) cls ko User σ

section cut
variable {own : (U64 → U64) → U64 → Owner U64 U64} {E : U64 → Prop} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop}
  {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
  {F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (X × S × A)}
  {p : SProg X} {Acc : X → Prop} {Locks : S → U64 → Prop} {Pre : S → Prop}
  {RS WS DS : S → U64 → Prop}

theorem alt_backE (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS) (hmk : MasksWr st) {s s' : S}
    (hs : Pre s) (hA : Alt st (rsE E RS s) cls ko User s s') :
    ∃ s'', Alt st (RS s) cls ko User s s'' ∧ AgOff st E s' s'' := by
  let D : Set U64 := {x | Aligned x ∧ RS s x ∧ E x}
  let l := (Set.toFinite D).toFinset.toList
  have hl : ∀ x, x ∈ l ↔ x ∈ D := fun x => by
    simp only [l, Finset.mem_toList, Set.Finite.mem_toFinset]
  have hla : ∀ x ∈ l, Aligned x := fun x hx => ((hl x).mp hx).1
  have hm := wrs_mem st (ν := L.mem s) l s' hla
  obtain ⟨c1, c2, c3⟩ := wrs_const st (ν := L.mem s) hmk l s'
  refine ⟨wrs st (L.mem s) l s', ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨c1.symm, c2.symm, c3.symm, ?_⟩⟩
  · rw [c1, hA.cpu]
  · rw [c2, hA.ksb]
  · rw [c3, hA.masks]
  · intro x hx
    have ha := Sd.rs_aligned s x hs hx
    rw [hm x ha]
    split_ifs with h
    · rfl
    · have hv : ¬ E x := fun hv => h ((hl x).mpr ⟨ha, hx, hv⟩)
      exact hA.read x ⟨hx, hv⟩
  · intro x hx hu hk
    have ha : Aligned x := Sd.ko_aligned x (by rcases hk with h | h <;> rw [h] <;> intro e <;> cases e)
    have hnl : x ∉ l := fun h => hx ((hl x).mp h).2.1
    rw [hm x ha, if_neg hnl]
    exact hA.clsEq x (fun h => hx h.1) hu hk
  · intro b hb hv
    have hnl : b ∉ l := fun h => hv ((hl b).mp h).2.2
    rw [hm b hb, if_neg hnl]

/-- `AvoidV`'s two halves, stated on the body. -/
def AvAccE (E : U64 → Prop) (st : machine.Store S) (F : machine.Store S → S → A → Result (X × S × A))
    (Acc : X → Prop) (Pre : S → Prop) (RS WS : S → U64 → Prop) : Prop :=
  ∀ s a r, Pre s → F st s a = ok r → Acc r.1 → F (guard st (rsE E RS s) (WS s)) s a = ok r

def AvDecE (E : U64 → Prop) (st : machine.Store S) [LawfulStore st] (F : machine.Store S → S → A → Result (X × S × A))
    (Acc : X → Prop) (cls : U64 → U64 → U64) (ko : U64 → ClsOwner U64) (User : U64 → Prop)
    (Pre : S → Prop) (RS : S → U64 → Prop) : Prop :=
  ∀ s a r, Pre s → F st s a = ok r → ¬ Acc r.1 → ∀ s' r', Alt st (RS s) cls ko User s s' →
    F st s' a = ok r' → F (guard st (fun b => ¬ E b) (fun _ => True)) s' a = ok r'

theorem dec_withinE (hp : IsProgOn (F ar) ar st (AltCutE E st Pre RS cls ko User) p) (O : PathObl st (F ar) Acc (own) cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS) (hD : AvDecE E st (F ar) Acc cls ko User Pre RS)
    {s s'' : S} {a : A} {r r'' : X × S × A} (hs : Pre s) (h : F ar st s a = ok r) (hd : ¬ Acc r.1)
    (hA : Alt st (RS s) cls ko User s s'') (h'' : F ar st s'' a = ok r'') :
    Within st ar (GE E) (DS s) p s'' a := by
  have e := fun (st' : machine.Store S) (N : Narrow st st') => hp st' N s'' (.inl ⟨s, hs, hA⟩) a
  have w1 := (interp_guard p s'' a r'' ((e _ (Narrow.guard _ _ _)).symm.trans (hD s a r hs h hd s'' r'' hA h''))).2
  have w2 := (interp_guard p s'' a r'' ((e _ (Narrow.guard _ _ _)).symm.trans (Sd.read_aligned s s'' a r'' hs hA h''))).2
  have w3 := (interp_guard p s'' a r'' ((e _ (Narrow.guard _ _ _)).symm.trans (O.dec_alt s a r hs h hd s'' r'' hA h'').2.1)).2
  exact Within.mono (fun b hb => ⟨hb.1.2, hb.1.1⟩) (fun b hb => hb.2) p s'' a
    (within_and p s'' a (within_and p s'' a w1 w2) w3)

theorem acc_withinE (hp : IsProgOn (F ar) ar st (AltCutE E st Pre RS cls ko User) p) (O : PathObl st (F ar) Acc (own) cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS) (hN : ReadOnce st ar p cls ko User Pre RS)
    (hmk : MasksWr st) (hAc : AvAccE E st (F ar) Acc Pre RS WS)
    {s s'' : S} {a : A} {r : X × S × A} (hs : Pre s) (h : F ar st s a = ok r) (hac : Acc r.1)
    (hA : Alt st (RS s) cls ko User s s'') :
    Within st ar (GE E) (WS s) p s'' a := by
  have e := fun (st' : machine.Store S) (N : Narrow st st') (σ : S) (g : AltCutE E st Pre RS cls ko User σ) =>
    hp st' N σ g a
  have w := (interp_guard p s a r ((e _ (Narrow.guard _ _ _) s (.inl (AltOf.pre hs))).symm.trans (hAc s a r hs h hac))).2
  have hO := hN s s a r hs (Alt.refl (R := RS s) (cls := cls) (ko := ko) (User := User) s) ((e st (Narrow.self st) s (.inl (AltOf.pre hs))).symm.trans h)
  have hAg : AgOff st (fun b => ¬ RS s b) s'' s :=
    ⟨hA.cpu, hA.ksb, hA.masks, fun b _ hb => hA.read b (not_not.mp hb)⟩
  have w' := (sim_off hmk (G := rsE E RS s) (W := WS s)
    (fun b hb => ⟨Sd.rs_aligned s b hs hb.1, not_not.mpr hb.1⟩)
    (fun b hb => O.aligned s b hs (Or.inl hb)) p s'' s a ∅ ∅ hAg w hO).1
  exact Within.mono (fun b hb => ⟨Sd.rs_aligned s b hs hb.1, hb.2⟩) (fun _ h => h) p s'' a w'

/-- The run from a written-back state reads only `GV` words and writes only `WS s` / `DS s`. -/
theorem back_withinE (hp : IsProgOn (F ar) ar st (AltCutE E st Pre RS cls ko User) p) (O : PathObl st (F ar) Acc (own) cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS) (hN : ReadOnce st ar p cls ko User Pre RS)
    (hT : ∀ s a, ∃ r, F ar st s a = ok r) (hmk : MasksWr st)
    (hAc : AvAccE E st (F ar) Acc Pre RS WS) (hD : AvDecE E st (F ar) Acc cls ko User Pre RS)
    {s s'' : S} {a : A} (hs : Pre s) (hA : Alt st (RS s) cls ko User s s'') :
    Within st ar (GE E) (fun b => WS s b ∨ DS s b) p s'' a := by
  obtain ⟨r, h⟩ := hT s a
  by_cases hac : Acc r.1
  · exact Within.mono (fun _ h => h) (fun _ h => Or.inl h) p s'' a (acc_withinE hp O Sd hN hmk hAc hs h hac hA)
  · obtain ⟨r'', h''⟩ := hT s'' a
    exact Within.mono (fun _ h => h) (fun _ h => Or.inr h) p s'' a (dec_withinE hp O Sd hD hs h hac hA h'')

theorem ge_ok : ∀ b, GE E b → Aligned b ∧ ¬ E b := fun _ h => h

/-- **`read_aligned` for the cut set.** -/
theorem cut_read_alignedE (hp : IsProgOn (F ar) ar st (AltCutE E st Pre RS cls ko User) p) (O : PathObl st (F ar) Acc (own) cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS) (hN : ReadOnce st ar p cls ko User Pre RS)
    (hT : ∀ s a, ∃ r, F ar st s a = ok r) (hmk : MasksWr st)
    (hAc : AvAccE E st (F ar) Acc Pre RS WS) (hD : AvDecE E st (F ar) Acc cls ko User Pre RS)
    (s s' : S) (a : A) (r' : X × S × A) (hs : Pre s) (hA : Alt st (rsE E RS s) cls ko User s s')
    (h' : F ar st s' a = ok r') : F ar (guard st (fun b => Aligned b) (fun _ => True)) s' a = ok r' := by
  have e := fun (st' : machine.Store S) (N : Narrow st st') (σ : S) (g : AltCutE E st Pre RS cls ko User σ) =>
    hp st' N σ g a
  obtain ⟨s'', hA'', hAg⟩ := alt_backE Sd hmk hs hA
  obtain ⟨r'', h''⟩ := hT s'' a
  have hO := hN s s'' a r'' hs hA'' ((e st (Narrow.self st) s'' (.inl ⟨s, hs, hA''⟩)).symm.trans h'')
  have w := (sim_off hmk ge_ok (fun b hb => hb.elim (fun h => O.aligned s b hs (Or.inl h))
    (fun h => O.aligned s b hs (Or.inr h))) p s' s'' a ∅ ∅ hAg
    (back_withinE hp O Sd hN hT hmk hAc hD hs hA'') hO).1
  exact (e _ (Narrow.guard _ _ _) s' (.inr ⟨s, hs, hA⟩)).trans (guard_of_within p s' a r'
      ((e st (Narrow.self st) s' (.inr ⟨s, hs, hA⟩)).symm.trans h')
    (Within.mono (fun b hb => hb.1) (fun _ _ => trivial) p s' a w))

/-- **`ReadOnce` for the cut set.** -/
theorem cut_onceE (hp : IsProgOn (F ar) ar st (AltCutE E st Pre RS cls ko User) p) (O : PathObl st (F ar) Acc (own) cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS) (hN : ReadOnce st ar p cls ko User Pre RS)
    (hT : ∀ s a, ∃ r, F ar st s a = ok r) (hmk : MasksWr st)
    (hAc : AvAccE E st (F ar) Acc Pre RS WS) (hD : AvDecE E st (F ar) Acc cls ko User Pre RS) :
    ReadOnce st ar p cls ko User Pre (rsE E RS) := by
  intro s s' a r' hs hA _
  have e := fun (st' : machine.Store S) (N : Narrow st st') (σ : S) (g : AltCutE E st Pre RS cls ko User σ) =>
    hp st' N σ g a
  obtain ⟨s'', hA'', hAg⟩ := alt_backE Sd hmk hs hA
  obtain ⟨r'', h''⟩ := hT s'' a
  have hO := hN s s'' a r'' hs hA'' ((e st (Narrow.self st) s'' (.inl ⟨s, hs, hA''⟩)).symm.trans h'')
  exact sim_offO ge_ok (fun b hb => hb.elim (fun h => O.aligned s b hs (Or.inl h))
    (fun h => O.aligned s b hs (Or.inr h))) hmk (R1 := rsE E RS s) (R2 := RS s)
    (fun q hq => ⟨fun h => h.1, fun h => ⟨h, hq.2⟩⟩) p s' s'' a ∅ ∅ hAg
    (back_withinE hp O Sd hN hT hmk hAc hD hs hA'') hO

/-- **The per-write check is the same at two states equal off the VCPU data words.** -/
theorem stepOK_agoffE (hoc : ∀ m m' : U64 → U64, (∀ b, Aligned b → ¬ E b → m b = m' b) → own m = own m')
    (hko : ∀ x, E x → ko x = .free)
    (hka : ∀ x, ko x ≠ .free → Aligned x) (hmk : MasksWr st) {c : U64} {lk : U64 → Prop} {σ1 σ2 : S}
    (hA : AgOff st E σ1 σ2) {q v : U64} (hq : Aligned q)
    (h : StepOK (own) cls ko User c lk (L.mem σ2) (L.mem (L.wr σ2 q v))) :
    StepOK (own) cls ko User c lk (L.mem σ1) (L.mem (L.wr σ1 q v)) := by
  have hA' := hA.wr hmk hq v
  have oc : ∀ {τ1 τ2 : S}, AgOff st E τ1 τ2 →
      own (L.mem τ1) = own (L.mem τ2) := fun hh => hoc _ _ fun b hb he => hh.mem b hb he
  refine ⟨fun x hx => ?_, fun x hx hu => ?_⟩
  · rw [oc hA, oc hA'] at hx ⊢; exact h.1 x hx
  · by_cases hf : ko x = .free
    · exact Or.inr (Or.inr hf)
    · have ha := hka x hf
      have hv : ¬ E x := fun hv => hf (hko x hv)
      rw [hA'.mem x ha hv, hA.mem x ha hv] at hx ⊢
      exact h.2 x hx hu

/-- **`dec_alt` for the cut set.** -/
theorem cut_dec_altE (hoc : ∀ m m' : U64 → U64, (∀ b, Aligned b → ¬ E b → m b = m' b) → own m = own m')
    (hko : ∀ x, E x → ko x = .free)
    (hp : IsProgOn (F ar) ar st (AltCutE E st Pre RS cls ko User) p) (O : PathObl st (F ar) Acc (own) cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS) (hN : ReadOnce st ar p cls ko User Pre RS)
    (hT : ∀ s a, ∃ r, F ar st s a = ok r) (hmk : MasksWr st) (hD : AvDecE E st (F ar) Acc cls ko User Pre RS)
    (s : S) (a : A) (r : X × S × A) (hs : Pre s) (h : F ar st s a = ok r) (hd : ¬ Acc r.1)
    (s' : S) (r' : X × S × A) (hA : Alt st (rsE E RS s) cls ko User s s') (h' : F ar st s' a = ok r') :
    ¬ Acc r'.1 ∧ F ar (guard st (fun _ => True) (DS s)) s' a = ok r' ∧
      F ar (mguard st (fun x y => StepOK (own) cls ko User (L.cpu s) (Locks s)
        (L.mem x) (L.mem y))) s' a = ok r' := by
  have e := fun (st' : machine.Store S) (N : Narrow st st') (σ : S) (g : AltCutE E st Pre RS cls ko User σ) =>
    hp st' N σ g a
  obtain ⟨s'', hA'', hAg⟩ := alt_backE Sd hmk hs hA
  obtain ⟨r'', h''⟩ := hT s'' a
  obtain ⟨n1, n2, n3⟩ := O.dec_alt s a r hs h hd s'' r'' hA'' h''
  have hO := hN s s'' a r'' hs hA'' ((e st (Narrow.self st) s'' (.inl ⟨s, hs, hA''⟩)).symm.trans h'')
  have hW : ∀ b, DS s b → Aligned b := fun b hb => O.aligned s b hs (Or.inr hb)
  have w := dec_withinE hp O Sd hD hs h hd hA'' h''
  have S1 := sim_off hmk ge_ok hW p s' s'' a ∅ ∅ hAg w hO
  obtain ⟨σ1', h1, -⟩ := S1.2 r'' ((e st (Narrow.self st) s'' (.inl ⟨s, hs, hA''⟩)).symm.trans h'')
  have er : r' = (r''.1, σ1', r''.2.2) := Result.ok_injective (((e st (Narrow.self st) s' (.inr ⟨s, hs, hA⟩)).symm.trans h').symm.trans h1)
  refine ⟨by rw [er]; exact n1, ?_, ?_⟩
  · exact (e _ (Narrow.guard _ _ _) s' (.inr ⟨s, hs, hA⟩)).trans (guard_of_within p s' a r'
      ((e st (Narrow.self st) s' (.inr ⟨s, hs, hA⟩)).symm.trans h')
      (Within.mono (fun _ _ => trivial) (fun _ h => h) p s' a S1.1))
  · have m2 := (interp_mguard p s'' a r'' ((e _ (Narrow.mguard _ _) s'' (.inl ⟨s, hs, hA''⟩)).symm.trans n3)).2
    have m1 := sim_offM hmk ge_ok hW
      (Q2 := fun x y => StepOK (own) cls ko User (L.cpu s) (Locks s) (L.mem x) (L.mem y))
      (Q1 := fun x y => StepOK (own) cls ko User (L.cpu s) (Locks s) (L.mem x) (L.mem y))
      (fun σ1 σ2 q v hh hq hQ => stepOK_agoffE hoc hko Sd.ko_aligned hmk hh (hW q hq) hQ)
      p s' s'' a ∅ ∅ hAg w hO m2
    exact (e _ (Narrow.mguard _ _) s' (.inr ⟨s, hs, hA⟩)).trans (mguard_of_withinM p s' a r'
      ((e st (Narrow.self st) s' (.inr ⟨s, hs, hA⟩)).symm.trans h') m1)

end cut

/-! ## The cut path -/

section path
variable {own : (U64 → U64) → U64 → Owner U64 U64} {E : U64 → Prop} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **`AvoidE`** [W] (per path): the path's runs read no `E` word (`acc`: the accepted run within `rsE E RS s`;
`dec`: the declining runs from every alternative of the old set outside `E`; `prog` [P]: the program premise at
the cut set's alternatives). -/
structure AvoidE (E : U64 → Prop) (P : LocalPath own cls ko User) : Prop where
  acc : AvAccE E P.st (P.F P.ar) P.Acc P.Pre P.RS P.WS
  dec : @AvDecE P.S P.A P.X E P.st P.L (P.F P.ar) P.Acc cls ko User P.Pre P.RS
  prog : IsProgOn (P.F P.ar) P.ar P.st (@AltOf P.S P.st P.L P.Pre (rsE E P.RS) cls ko User) P.p

theorem AvoidE.progCut {P : LocalPath own cls ko User} (hAv : AvoidE E P) :
    IsProgOn (P.F P.ar) P.ar P.st (@AltCutE P.S E P.st P.L P.Pre P.RS cls ko User) P.p :=
  fun st' N σ g a => g.elim (fun h => P.isProg st' N σ h a) (fun h => hAv.prog st' N σ h a)

/-- **The path with its read set cut to `rsE E RS`**, from `AvoidE`. -/
def LocalPath.cutE (hoc : ∀ m m' : U64 → U64, (∀ b, Aligned b → ¬ E b → m b = m' b) → own m = own m')
    (hko : ∀ x, E x → ko x = .free) (P : LocalPath own cls ko User) (hAv : AvoidE E P) :
    LocalPath own cls ko User where
  S := P.S
  A := P.A
  X := P.X
  st := P.st
  L := P.L
  ar := P.ar
  F := P.F
  p := P.p
  Acc := P.Acc
  Locks := P.Locks
  Pre := P.Pre
  RS := rsE E P.RS
  WS := P.WS
  DS := P.DS
  isProg := hAv.prog
  obl := by
    letI := P.L
    exact {
      acc := hAv.acc
      dec_alt := cut_dec_altE hoc hko hAv.progCut P.obl P.side P.once P.total P.masks hAv.dec
      read_own := fun s x hp hr hu => P.obl.read_own s x hp hr.1 hu
      write_own := P.obl.write_own
      aligned := P.obl.aligned
      move := P.obl.move }
  side := by
    letI := P.L
    exact {
      read_aligned := cut_read_alignedE hAv.progCut P.obl P.side P.once P.total P.masks hAv.acc hAv.dec
      rs_aligned := fun s x hp hr => P.side.rs_aligned s x hp hr.1
      ko_aligned := P.side.ko_aligned
      user_free := fun s b v hp hb ha => by
        obtain ⟨h1, h2, h3, h4, h5⟩ := P.side.user_free s b v hp hb ha
        refine ⟨h1, h2, ?_, h4, h5⟩
        funext x; unfold rsE; rw [h3] }
  once := by
    letI := P.L
    exact cut_onceE hAv.progCut P.obl P.side P.once P.total P.masks hAv.acc hAv.dec
  total := P.total
  masks := P.masks

/-- **A path that never starts avoids every set.** -/
theorem avoidE_of_noPre {P : LocalPath own cls ko User} (h : ∀ s, ¬ P.Pre s) : AvoidE E P where
  acc s _ _ hs := absurd hs (h s)
  dec s _ _ hs := absurd hs (h s)
  prog _ _ _ g _ := absurd g.choose_spec.1 (h _)

theorem rsE_bot {S : Type} (RS : S → U64 → Prop) : rsE (fun _ => False) RS = RS := by
  funext s x; apply propext; exact ⟨fun h => h.1, fun h => ⟨h, id⟩⟩

/-- `guard st ⊤ ⊤` is the store itself, on every run that succeeds there (`read_aligned`'s form with no read
restriction). -/
theorem avDecE_bot {P : LocalPath own cls ko User} :
    @AvDecE P.S P.A P.X (fun _ => False) P.st P.L (P.F P.ar) P.Acc cls ko User P.Pre P.RS := by
  letI := P.L
  intro s a r hs h hd s' r' hA h'
  have hp := P.isProg
  have e1 := hp _ (Narrow.guard _ (fun b => ¬ False) (fun _ => True)) s' ⟨s, hs, hA⟩ a
  have e0 := hp _ (Narrow.self P.st) s' ⟨s, hs, hA⟩ a
  have hra := P.side.read_aligned s s' a r' hs hA h'
  have e2 := hp _ (Narrow.guard _ (fun b => Aligned b) (fun _ => True)) s' ⟨s, hs, hA⟩ a
  have w := (interp_guard P.p s' a r' (e2.symm.trans hra)).2
  exact e1.trans (guard_of_within P.p s' a r' (e0.symm.trans h')
    (Within.mono (fun _ _ => id) (fun _ h => h) P.p s' a w))

/-- **`E = ⊥`: every path avoids it**, from its own obligations. -/
theorem avoidE_bot (P : LocalPath own cls ko User) : AvoidE (fun _ => False) P where
  acc s a r hs h hac := by letI := P.L; rw [rsE_bot]; exact P.obl.acc s a r hs h hac
  dec := avDecE_bot
  prog := by rw [rsE_bot]; exact P.isProg

end path

/-! ## Rule 8: the PTE cut of an `ownV` path, lifted to `ownP` -/

section pte
variable {K : KLayoutP} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop}

/-- `ownV` reads no PTE word. -/
theorem ownV_ocP (hK : RegionOKP K) (hU : UserOKP K) :
    ∀ m m' : U64 → U64, (∀ b, Aligned b → ¬ b ∈ K.ptes → m b = m' b) → ownV K.toKLayoutV m = ownV K.toKLayoutV m' :=
  fun _ _ h => OwnMapV.ownV_congr hK.base fun d hd =>
    h d (OwnMap.decW_ok hU.base.base hd).1 (fun hp => pte_nondec hK hp hd)

/-- **`AvoidP`** [W] (per path and layout): the `ownV` path's runs read no PTE word (`AvoidE` at the PTE set). -/
abbrev AvoidP (K : KLayoutP) (P : LocalPath (ownV K.toKLayoutV) cls ko User) : Prop := AvoidE (· ∈ K.ptes) P

theorem avoidP_empty (h : K.ptes = ∅) (P : LocalPath (ownV K.toKLayoutV) cls ko User) : AvoidP K P := by
  have e : (fun x => x ∈ K.ptes) = fun _ : U64 => False := by
    funext x; rw [h]; exact propext ⟨fun h' => Set.notMem_empty x h', False.elim⟩
  unfold AvoidP
  rw [e]; exact avoidE_bot P

/-- **An `ownV` path, its PTE words cut out of the read set, lifted to `ownP`**. -/
def LocalPath.cutLiftP (hK : RegionOKP K) (hU : UserOKP K) (hko : ∀ x, x ∈ K.ptes → ko x = .free)
    (P : LocalPath (ownV K.toKLayoutV) cls ko User) (hAv : AvoidP K P) : LocalPath (ownP K) cls ko User :=
  LocalPath.liftP hK (LocalPath.cutE (ownV_ocP hK hU) hko P hAv) (fun _ _ _ hr _ => hr.2)

/-- **The `ownV` paths, PTE-cut and lifted to `ownP`**, given `AvoidP` [W] of each at every layout. -/
def PathsP.ofVCut {ι : Type} (LP : PathsV ι)
    (hAv : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), AvoidP K (LP i K.toKLayoutV m hK.base hU.base)) :
    PathsP ι :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (hAv i K m hK hU)

/-- **Starting a cut-and-lifted path**: a start of the `ownV` path is one of its cut lift (same states, `Pre`,
core, locks, body). -/
theorem startAt_ofVCut {ι : Type} {LP : PathsV ι}
    {hAv : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), AvoidP K (LP i K.toKLayoutV m hK.base hU.base)}
    {i : ι} {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop}
    {μ : U64 → U64} {q : SP} (h : StartAt (LP i K.toKLayoutV m hK.base hU.base) c hs μ q) :
    ∃ q', StartAt (PathsP.ofVCut LP hAv i K m hK hU) c hs μ q' := by
  obtain ⟨σ, a, hP, hc, hl, hμ, -⟩ := h
  exact ⟨_, σ, a, hP, hc, hl, hμ, rfl⟩

end pte

end
end Fl4Proofs.P2.E2EP
