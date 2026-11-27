/-
P2 (line vlift): **`LocalPath.cutV`**, a local path for `own` with its read set cut to `rsV K RS`, from the
path and **`AvoidV`** [W] (its runs read no VCPU data word: the accepted run within `rsV K RS s`, the declined
runs from every alternative of the old set outside `VData`). Module docstring of `P2/E2EVCut.lean` for the
argument; here the obligations, one by one:

* `alt_back`: an alternative for the cut set, with the VCPU data words of `RS` written back to the entry's
  values (`E2E.wrs`), is an alternative for the old set and equal to it off `VData` (`AgOff`);
* `dec_within` / `acc_within`: from such a state the run reads only aligned non-`VData` words and writes only
  `DS s` (declining entry: `AvoidV.dec`, `read_aligned`, `dec_alt`) or `WS s` (accepting entry: the accepted
  run's trace, `sim_off` against the entry);
* `stepOK_agoff`: the per-write check is the same at two states equal off `VData` (`own` reads no VCPU word,
  `ko` is `.free` on them, `PathSide.ko_aligned` for unaligned words);
* `cut_read_aligned`, `cut_once`, `cut_dec_alt`: the old obligations at the written-back state, carried to
  the alternative by `sim_off` / `sim_offO` / `sim_offM`;
* **`LocalPath.cutV`**, `noVcpuRd_cutV`, **`LocalPath.cutLiftV`** (the cut path lifted to `ownV`).

Premises: `AvoidV` [W] per path (with its `prog` [P] part: the relativised program premise at the cut set's
alternatives, int13); `RegionOKV` / `UserOKV` [J] (as everywhere in `E2EV`); `hko` (the path's
`ko` is `.free` on VCPU data words: `OwnMapV.ko_vcpu` for `OwnMap.ko`).
-/
import Fl4Proofs.P2.E2EVCut
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.Serial (Owner ClsOwner)

noncomputable section
open Classical

/-- Aligned words outside the VCPU data words. -/
def GV (K : KLayoutV) (b : U64) : Prop := Aligned b ∧ ¬ VData K b

/-- The states the cut path's program premise covers: alternatives of an entry for the old read set `RS` or
for the cut one `rsV K RS`. -/
def AltCut {S : Type} (K : KLayoutV) (st : machine.Store S) [LawfulStore st] (Pre : S → Prop)
    (RS : S → U64 → Prop) (cls : U64 → U64 → U64) (ko : U64 → ClsOwner U64) (User : U64 → Prop) (σ : S) : Prop :=
  AltOf st Pre RS cls ko User σ ∨ AltOf st Pre (rsV K RS) cls ko User σ

section cut
variable {K : KLayoutV} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop}
  {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
  {F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (X × S × A)}
  {p : SProg X} {Acc : X → Prop} {Locks : S → U64 → Prop} {Pre : S → Prop}
  {RS WS DS : S → U64 → Prop}

theorem alt_back (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS) (hmk : MasksWr st) {s s' : S}
    (hs : Pre s) (hA : Alt st (rsV K RS s) cls ko User s s') :
    ∃ s'', Alt st (RS s) cls ko User s s'' ∧ AgOff st (VData K) s' s'' := by
  let D : Set U64 := {x | Aligned x ∧ RS s x ∧ VData K x}
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
    · have hv : ¬ VData K x := fun hv => h ((hl x).mpr ⟨ha, hx, hv⟩)
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
def AvAcc (K : KLayoutV) (st : machine.Store S) (F : machine.Store S → S → A → Result (X × S × A))
    (Acc : X → Prop) (Pre : S → Prop) (RS WS : S → U64 → Prop) : Prop :=
  ∀ s a r, Pre s → F st s a = ok r → Acc r.1 → F (guard st (rsV K RS s) (WS s)) s a = ok r

def AvDec (K : KLayoutV) (st : machine.Store S) [LawfulStore st] (F : machine.Store S → S → A → Result (X × S × A))
    (Acc : X → Prop) (cls : U64 → U64 → U64) (ko : U64 → ClsOwner U64) (User : U64 → Prop)
    (Pre : S → Prop) (RS : S → U64 → Prop) : Prop :=
  ∀ s a r, Pre s → F st s a = ok r → ¬ Acc r.1 → ∀ s' r', Alt st (RS s) cls ko User s s' →
    F st s' a = ok r' → F (guard st (fun b => ¬ VData K b) (fun _ => True)) s' a = ok r'

theorem dec_within (hp : IsProgOn (F ar) ar st (AltCut K st Pre RS cls ko User) p) (O : PathObl st (F ar) Acc (OwnMap.own K.toKLayout) cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS) (hD : AvDec K st (F ar) Acc cls ko User Pre RS)
    {s s'' : S} {a : A} {r r'' : X × S × A} (hs : Pre s) (h : F ar st s a = ok r) (hd : ¬ Acc r.1)
    (hA : Alt st (RS s) cls ko User s s'') (h'' : F ar st s'' a = ok r'') :
    Within st ar (GV K) (DS s) p s'' a := by
  have e := fun (st' : machine.Store S) (N : Narrow st st') => hp st' N s'' (.inl ⟨s, hs, hA⟩) a
  have w1 := (interp_guard p s'' a r'' ((e _ (Narrow.guard _ _ _)).symm.trans (hD s a r hs h hd s'' r'' hA h''))).2
  have w2 := (interp_guard p s'' a r'' ((e _ (Narrow.guard _ _ _)).symm.trans (Sd.read_aligned s s'' a r'' hs hA h''))).2
  have w3 := (interp_guard p s'' a r'' ((e _ (Narrow.guard _ _ _)).symm.trans (O.dec_alt s a r hs h hd s'' r'' hA h'').2.1)).2
  exact Within.mono (fun b hb => ⟨hb.1.2, hb.1.1⟩) (fun b hb => hb.2) p s'' a
    (within_and p s'' a (within_and p s'' a w1 w2) w3)

theorem acc_within (hp : IsProgOn (F ar) ar st (AltCut K st Pre RS cls ko User) p) (O : PathObl st (F ar) Acc (OwnMap.own K.toKLayout) cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS) (hN : ReadOnce st ar p cls ko User Pre RS)
    (hmk : MasksWr st) (hAc : AvAcc K st (F ar) Acc Pre RS WS)
    {s s'' : S} {a : A} {r : X × S × A} (hs : Pre s) (h : F ar st s a = ok r) (hac : Acc r.1)
    (hA : Alt st (RS s) cls ko User s s'') :
    Within st ar (GV K) (WS s) p s'' a := by
  have e := fun (st' : machine.Store S) (N : Narrow st st') (σ : S) (g : AltCut K st Pre RS cls ko User σ) =>
    hp st' N σ g a
  have w := (interp_guard p s a r ((e _ (Narrow.guard _ _ _) s (.inl (AltOf.pre hs))).symm.trans (hAc s a r hs h hac))).2
  have hO := hN s s a r hs (Alt.refl (R := RS s) (cls := cls) (ko := ko) (User := User) s) ((e st (Narrow.self st) s (.inl (AltOf.pre hs))).symm.trans h)
  have hAg : AgOff st (fun b => ¬ RS s b) s'' s :=
    ⟨hA.cpu, hA.ksb, hA.masks, fun b _ hb => hA.read b (not_not.mp hb)⟩
  have w' := (sim_off hmk (G := rsV K RS s) (W := WS s)
    (fun b hb => ⟨Sd.rs_aligned s b hs hb.1, not_not.mpr hb.1⟩)
    (fun b hb => O.aligned s b hs (Or.inl hb)) p s'' s a ∅ ∅ hAg w hO).1
  exact Within.mono (fun b hb => ⟨Sd.rs_aligned s b hs hb.1, hb.2⟩) (fun _ h => h) p s'' a w'

/-- The run from a written-back state reads only `GV` words and writes only `WS s` / `DS s`. -/
theorem back_within (hp : IsProgOn (F ar) ar st (AltCut K st Pre RS cls ko User) p) (O : PathObl st (F ar) Acc (OwnMap.own K.toKLayout) cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS) (hN : ReadOnce st ar p cls ko User Pre RS)
    (hT : ∀ s a, ∃ r, F ar st s a = ok r) (hmk : MasksWr st)
    (hAc : AvAcc K st (F ar) Acc Pre RS WS) (hD : AvDec K st (F ar) Acc cls ko User Pre RS)
    {s s'' : S} {a : A} (hs : Pre s) (hA : Alt st (RS s) cls ko User s s'') :
    Within st ar (GV K) (fun b => WS s b ∨ DS s b) p s'' a := by
  obtain ⟨r, h⟩ := hT s a
  by_cases hac : Acc r.1
  · exact Within.mono (fun _ h => h) (fun _ h => Or.inl h) p s'' a (acc_within hp O Sd hN hmk hAc hs h hac hA)
  · obtain ⟨r'', h''⟩ := hT s'' a
    exact Within.mono (fun _ h => h) (fun _ h => Or.inr h) p s'' a (dec_within hp O Sd hD hs h hac hA h'')

theorem gv_ok : ∀ b, GV K b → Aligned b ∧ ¬ VData K b := fun _ h => h

/-- **`read_aligned` for the cut set.** -/
theorem cut_read_aligned (hp : IsProgOn (F ar) ar st (AltCut K st Pre RS cls ko User) p) (O : PathObl st (F ar) Acc (OwnMap.own K.toKLayout) cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS) (hN : ReadOnce st ar p cls ko User Pre RS)
    (hT : ∀ s a, ∃ r, F ar st s a = ok r) (hmk : MasksWr st)
    (hAc : AvAcc K st (F ar) Acc Pre RS WS) (hD : AvDec K st (F ar) Acc cls ko User Pre RS)
    (s s' : S) (a : A) (r' : X × S × A) (hs : Pre s) (hA : Alt st (rsV K RS s) cls ko User s s')
    (h' : F ar st s' a = ok r') : F ar (guard st (fun b => Aligned b) (fun _ => True)) s' a = ok r' := by
  have e := fun (st' : machine.Store S) (N : Narrow st st') (σ : S) (g : AltCut K st Pre RS cls ko User σ) =>
    hp st' N σ g a
  obtain ⟨s'', hA'', hAg⟩ := alt_back Sd hmk hs hA
  obtain ⟨r'', h''⟩ := hT s'' a
  have hO := hN s s'' a r'' hs hA'' ((e st (Narrow.self st) s'' (.inl ⟨s, hs, hA''⟩)).symm.trans h'')
  have w := (sim_off hmk gv_ok (fun b hb => hb.elim (fun h => O.aligned s b hs (Or.inl h))
    (fun h => O.aligned s b hs (Or.inr h))) p s' s'' a ∅ ∅ hAg
    (back_within hp O Sd hN hT hmk hAc hD hs hA'') hO).1
  exact (e _ (Narrow.guard _ _ _) s' (.inr ⟨s, hs, hA⟩)).trans (guard_of_within p s' a r'
      ((e st (Narrow.self st) s' (.inr ⟨s, hs, hA⟩)).symm.trans h')
    (Within.mono (fun b hb => hb.1) (fun _ _ => trivial) p s' a w))

/-- **`ReadOnce` for the cut set.** -/
theorem cut_once (hp : IsProgOn (F ar) ar st (AltCut K st Pre RS cls ko User) p) (O : PathObl st (F ar) Acc (OwnMap.own K.toKLayout) cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS) (hN : ReadOnce st ar p cls ko User Pre RS)
    (hT : ∀ s a, ∃ r, F ar st s a = ok r) (hmk : MasksWr st)
    (hAc : AvAcc K st (F ar) Acc Pre RS WS) (hD : AvDec K st (F ar) Acc cls ko User Pre RS) :
    ReadOnce st ar p cls ko User Pre (rsV K RS) := by
  intro s s' a r' hs hA _
  have e := fun (st' : machine.Store S) (N : Narrow st st') (σ : S) (g : AltCut K st Pre RS cls ko User σ) =>
    hp st' N σ g a
  obtain ⟨s'', hA'', hAg⟩ := alt_back Sd hmk hs hA
  obtain ⟨r'', h''⟩ := hT s'' a
  have hO := hN s s'' a r'' hs hA'' ((e st (Narrow.self st) s'' (.inl ⟨s, hs, hA''⟩)).symm.trans h'')
  exact sim_offO gv_ok (fun b hb => hb.elim (fun h => O.aligned s b hs (Or.inl h))
    (fun h => O.aligned s b hs (Or.inr h))) hmk (R1 := rsV K RS s) (R2 := RS s)
    (fun q hq => ⟨fun h => h.1, fun h => ⟨h, hq.2⟩⟩) p s' s'' a ∅ ∅ hAg
    (back_within hp O Sd hN hT hmk hAc hD hs hA'') hO

/-- **The per-write check is the same at two states equal off the VCPU data words.** -/
theorem stepOK_agoff (hK : RegionOKV K) (hU : UserOKV K) (hko : ∀ x, VData K x → ko x = .free)
    (hka : ∀ x, ko x ≠ .free → Aligned x) (hmk : MasksWr st) {c : U64} {lk : U64 → Prop} {σ1 σ2 : S}
    (hA : AgOff st (VData K) σ1 σ2) {q v : U64} (hq : Aligned q)
    (h : StepOK (OwnMap.own K.toKLayout) cls ko User c lk (L.mem σ2) (L.mem (L.wr σ2 q v))) :
    StepOK (OwnMap.own K.toKLayout) cls ko User c lk (L.mem σ1) (L.mem (L.wr σ1 q v)) := by
  have hA' := hA.wr hmk hq v
  have oc : ∀ {τ1 τ2 : S}, AgOff st (VData K) τ1 τ2 →
      OwnMap.own K.toKLayout (L.mem τ1) = OwnMap.own K.toKLayout (L.mem τ2) := fun hh =>
    OwnMap.own_congr hK.base fun d hd =>
      hh.mem d (OwnMap.decW_ok hU.base hd).1 (fun ⟨_, hw, _⟩ => vcpu_nondec hK hw hd)
  refine ⟨fun x hx => ?_, fun x hx hu => ?_⟩
  · rw [oc hA, oc hA'] at hx ⊢; exact h.1 x hx
  · by_cases hf : ko x = .free
    · exact Or.inr (Or.inr hf)
    · have ha := hka x hf
      have hv : ¬ VData K x := fun hv => hf (hko x hv)
      rw [hA'.mem x ha hv, hA.mem x ha hv] at hx ⊢
      exact h.2 x hx hu

/-- **`dec_alt` for the cut set.** -/
theorem cut_dec_alt (hK : RegionOKV K) (hU : UserOKV K) (hko : ∀ x, VData K x → ko x = .free)
    (hp : IsProgOn (F ar) ar st (AltCut K st Pre RS cls ko User) p) (O : PathObl st (F ar) Acc (OwnMap.own K.toKLayout) cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS) (hN : ReadOnce st ar p cls ko User Pre RS)
    (hT : ∀ s a, ∃ r, F ar st s a = ok r) (hmk : MasksWr st) (hD : AvDec K st (F ar) Acc cls ko User Pre RS)
    (s : S) (a : A) (r : X × S × A) (hs : Pre s) (h : F ar st s a = ok r) (hd : ¬ Acc r.1)
    (s' : S) (r' : X × S × A) (hA : Alt st (rsV K RS s) cls ko User s s') (h' : F ar st s' a = ok r') :
    ¬ Acc r'.1 ∧ F ar (guard st (fun _ => True) (DS s)) s' a = ok r' ∧
      F ar (mguard st (fun x y => StepOK (OwnMap.own K.toKLayout) cls ko User (L.cpu s) (Locks s)
        (L.mem x) (L.mem y))) s' a = ok r' := by
  have e := fun (st' : machine.Store S) (N : Narrow st st') (σ : S) (g : AltCut K st Pre RS cls ko User σ) =>
    hp st' N σ g a
  obtain ⟨s'', hA'', hAg⟩ := alt_back Sd hmk hs hA
  obtain ⟨r'', h''⟩ := hT s'' a
  obtain ⟨n1, n2, n3⟩ := O.dec_alt s a r hs h hd s'' r'' hA'' h''
  have hO := hN s s'' a r'' hs hA'' ((e st (Narrow.self st) s'' (.inl ⟨s, hs, hA''⟩)).symm.trans h'')
  have hW : ∀ b, DS s b → Aligned b := fun b hb => O.aligned s b hs (Or.inr hb)
  have w := dec_within hp O Sd hD hs h hd hA'' h''
  have S1 := sim_off hmk gv_ok hW p s' s'' a ∅ ∅ hAg w hO
  obtain ⟨σ1', h1, -⟩ := S1.2 r'' ((e st (Narrow.self st) s'' (.inl ⟨s, hs, hA''⟩)).symm.trans h'')
  have er : r' = (r''.1, σ1', r''.2.2) := Result.ok_injective (((e st (Narrow.self st) s' (.inr ⟨s, hs, hA⟩)).symm.trans h').symm.trans h1)
  refine ⟨by rw [er]; exact n1, ?_, ?_⟩
  · exact (e _ (Narrow.guard _ _ _) s' (.inr ⟨s, hs, hA⟩)).trans (guard_of_within p s' a r'
      ((e st (Narrow.self st) s' (.inr ⟨s, hs, hA⟩)).symm.trans h')
      (Within.mono (fun _ _ => trivial) (fun _ h => h) p s' a S1.1))
  · have m2 := (interp_mguard p s'' a r'' ((e _ (Narrow.mguard _ _) s'' (.inl ⟨s, hs, hA''⟩)).symm.trans n3)).2
    have m1 := sim_offM hmk gv_ok hW
      (Q2 := fun x y => StepOK (OwnMap.own K.toKLayout) cls ko User (L.cpu s) (Locks s) (L.mem x) (L.mem y))
      (Q1 := fun x y => StepOK (OwnMap.own K.toKLayout) cls ko User (L.cpu s) (Locks s) (L.mem x) (L.mem y))
      (fun σ1 σ2 q v hh hq hQ => stepOK_agoff hK hU hko Sd.ko_aligned hmk hh (hW q hq) hQ)
      p s' s'' a ∅ ∅ hAg w hO m2
    exact (e _ (Narrow.mguard _ _) s' (.inr ⟨s, hs, hA⟩)).trans (mguard_of_withinM p s' a r'
      ((e st (Narrow.self st) s' (.inr ⟨s, hs, hA⟩)).symm.trans h') m1)

end cut

/-! ## The cut path -/

section path
variable {K : KLayoutV} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **`AvoidV`** [W] (per path): the path's runs read no VCPU data word. `acc`: an accepted run is a run on the
store guarded to the cut set `rsV K RS s` (the path's own `acc` walk, each read word shown outside the VCPUs);
`dec`: from every alternative (for the path's own `RS`) of a declining entry, the run reads no `VData` word;
`prog` [P]: the path's program premise also at the alternatives for the cut set (`P.isProg` covers those for the
old `RS` only; since hpzf the premise is relativised, `IsProgOn`, so it does not carry over by itself; a path
built from an unrelativised `IsProg` gets it by `IsProg.on`). -/
structure AvoidV (K : KLayoutV) (P : LocalPath (OwnMap.own K.toKLayout) cls ko User) : Prop where
  acc : AvAcc K P.st (P.F P.ar) P.Acc P.Pre P.RS P.WS
  dec : @AvDec P.S P.A P.X K P.st P.L (P.F P.ar) P.Acc cls ko User P.Pre P.RS
  prog : IsProgOn (P.F P.ar) P.ar P.st (@AltOf P.S P.st P.L P.Pre (rsV K P.RS) cls ko User) P.p

theorem AvoidV.progCut {K : KLayoutV} {P : LocalPath (OwnMap.own K.toKLayout) cls ko User} (hAv : AvoidV K P) :
    IsProgOn (P.F P.ar) P.ar P.st (@AltCut P.S K P.st P.L P.Pre P.RS cls ko User) P.p :=
  fun st' N σ g a => g.elim (fun h => P.isProg st' N σ h a) (fun h => hAv.prog st' N σ h a)

/-- **The path with its read set cut to `rsV K RS`**, from `AvoidV`. -/
def LocalPath.cutV (hK : RegionOKV K) (hU : UserOKV K) (hko : ∀ x, VData K x → ko x = .free)
    (P : LocalPath (OwnMap.own K.toKLayout) cls ko User) (hAv : AvoidV K P) :
    LocalPath (OwnMap.own K.toKLayout) cls ko User where
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
  RS := rsV K P.RS
  WS := P.WS
  DS := P.DS
  isProg := hAv.prog
  obl := by
    letI := P.L
    exact {
      acc := hAv.acc
      dec_alt := cut_dec_alt hK hU hko hAv.progCut P.obl P.side P.once P.total P.masks hAv.dec
      read_own := fun s x hp hr hu => P.obl.read_own s x hp hr.1 hu
      write_own := P.obl.write_own
      aligned := P.obl.aligned
      move := P.obl.move }
  side := by
    letI := P.L
    exact {
      read_aligned := cut_read_aligned hAv.progCut P.obl P.side P.once P.total P.masks hAv.acc hAv.dec
      rs_aligned := fun s x hp hr => P.side.rs_aligned s x hp hr.1
      ko_aligned := P.side.ko_aligned
      user_free := fun s b v hp hb ha => by
        obtain ⟨h1, h2, h3, h4, h5⟩ := P.side.user_free s b v hp hb ha
        refine ⟨h1, h2, ?_, h4, h5⟩
        funext x; unfold rsV; rw [h3] }
  once := by
    letI := P.L
    exact cut_once hAv.progCut P.obl P.side P.once P.total P.masks hAv.acc hAv.dec
  total := P.total
  masks := P.masks

theorem noVcpuRd_cutV (hK : RegionOKV K) (hU : UserOKV K) (hko : ∀ x, VData K x → ko x = .free)
    (P : LocalPath (OwnMap.own K.toKLayout) cls ko User) (hAv : AvoidV K P) :
    NoVcpuRd K (LocalPath.cutV hK hU hko P hAv) :=
  noVcpuRd_of fun _ _ hr => hr.2

/-- **The cut path lifted to `ownV`.** -/
def LocalPath.cutLiftV (hK : RegionOKV K) (hU : UserOKV K) (hko : ∀ x, VData K x → ko x = .free)
    (P : LocalPath (OwnMap.own K.toKLayout) cls ko User) (hAv : AvoidV K P) :
    LocalPath (ownV K) cls ko User :=
  LocalPath.liftV hK (LocalPath.cutV hK hU hko P hAv) (noVcpuRd_cutV hK hU hko P hAv)

end path

/-- **The existing paths, cut and lifted**: each path of `LP` (at `K`'s base layout) cut to `rsV` by
`AvoidV` [W] and lifted to `ownV`. -/
def PathsV.ofPathsCut {ι : Type} (LP : Paths ι)
    (hAv : ∀ i (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K),
      AvoidV K (LP i K.toKLayout m hK.base hU.base)) : PathsV ι :=
  fun i K m hK hU => LocalPath.cutLiftV hK hU (fun x ⟨_, hv, _⟩ => ko_vcpu hK hv m) _ (hAv i K m hK hU)

end
end Fl4Proofs.P2.E2EV
