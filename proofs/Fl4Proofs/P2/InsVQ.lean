/-
# P2 (line p3mc, gen 48): the `InsA` counterpart of the view certificates `body_safeVW` / `LocalPath.safeVQW` /
`LocalPath.safeVQ`

`InsV15N` [J] (P2/InsV15N) asks, at a CoreView start, `InsA (PWE K E) ADEq NotPresent …` of the armed program at the
physical memory. The homed starts of st, sl, vmF and vmR prove `Safe` of the body there through `LocalPath.safeVQ` /
`safeVQW` (P2/SafeVQ, P2/SafeVQW), i.e. `body_safeVW`: at every admissible memory `ν` a store run from a start state
of the view (or an alternative of one) certifies the body's run on `ν` (`AltRun`). The same run certifies `InsA` once
it touches no `G` word: then the body's run on `ν` reads `G` words insensitively (`InsRun`, by `insT_sim` from
`insT_of_within`), and `insA_of_runsQ` applies.

* `body_runVW` (P2/ViewSafeGenW, split out of `body_safeVW`'s proof in place this generation, statement of
  `body_safeVW` unchanged): the read invariant and, per admissible `ν`, the certificate with its store run.
* **`body_insAVW`**: `body_safeVW`'s hypotheses plus `hNG` (every run from a start state of the view, or from an
  alternative of one, reads and writes no `G` word but user words), `G` ignored by the owner map (`hGo`), `G` words of
  class owner `.free` (`hGko`), `Q` an equivalence: `InsA G Q NP own cls kt c hs μ` of the body.
* **`LocalPath.insAVQW`**: the same for a `LocalPath` restricted to start states `Q0` (as `LocalPath.safeVQW`).
* **`LocalPath.insAVQ`**: `LocalPath.safeVQ`'s hypotheses plus `hNG` (from `insAVQW` at the trivial check, as
  `safeVQ_of_W`).

No named premise: every fact about the path is a hypothesis. New module; one existing file touched
(P2/ViewSafeGenW: `body_runVW` split out of `body_safeVW`, every statement byte-identical).
-/
import Fl4Proofs.P2.SafeVQW
import Fl4Proofs.P2.E2EADQ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner Prog HeldV PO MoveV Safe MoveHeld AltRun Adm Diff RInv VEq InsRun InsA
  DInvQ insA_of_runsQ)

noncomputable section
open Classical

section body
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko kt : U64 → ClsOwner U64} {User : U64 → Prop}
  {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
  {F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (X × S × A)}
  {p : SProg X} {Acc : X → Prop} {Locks : S → U64 → Prop} {Pre : S → Prop}
  {RS WS DS : S → U64 → Prop}

/-- **`InsA` from `body_safeVW`'s certificate when its runs touch no `G` word** (module docstring). -/
theorem body_insAVW {G : U64 → Prop} {QA : U64 → U64 → Prop} {NP : U64 → Prop} (hQA : Equivalence QA)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → kt x = .free)
    (hL : MoveHeld own) (hO : OwnDep own User)
    (hp : IsProgOn (F ar) ar st (AltOf st Pre RS cls ko User) p)
    (O : PathObl st (F ar) Acc own cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS)
    (hN : ReadOnce st ar p cls ko User Pre RS) (hT : ∀ s a, ∃ r, F ar st s a = ok r)
    (hmk : MasksWr st) {σ : S} {a : A} (hpre : Pre σ) {ρv ρ μ : U64 → U64}
    (hρ : ∀ x, Aligned x → ¬ User x → L.mem σ x = ρv x)
    (hV : VEq own cls kt (L.cpu σ) (Locks σ) ρ μ)
    {N Kc NW DD : U64 → Prop}
    (hN1 : ∀ x, N x → ρv x = ρ x) (hN2 : ∀ x, N x → own ρv x = own ρ x) (hKc : ∀ x, Kc x → ko x = kt x)
    (hNW : ∀ x, NW x → N x ∧ Kc x)
    (hO1 : ∀ m m' : U64 → U64, (∀ x, Aligned x → ¬ User x → ρv x = ρ x → m x = m' x) →
      ∀ y, ¬ DD y → own m y = own m' y)
    {VW : S → S → Prop}
    (hO2W : ∀ q, NW q → ∀ (s : S) v (m : U64 → U64), VW s (L.wr s q v) →
      (∀ x, Aligned x → ¬ User x → ρv x = ρ x → m x = L.mem s x) → ∀ y, DD y → own (Function.update m q v) y = own m y)
    {NR NWs : S → U64 → Prop} (hNR : ∀ s0 b, NR s0 b → N b ∧ (RS s0 b ∨ Kc b)) (hNWs : ∀ s0 b, NWs s0 b → NW b)
    (hNarA : ∀ s0 r, Pre s0 → L.cpu s0 = L.cpu σ → (∀ x, Aligned x → ¬ User x → L.mem s0 x = ρv x) → F ar st s0 a = ok r → Acc r.1 →
      F ar (guard st (NR s0) (NWs s0)) s0 a = ok r)
    (hNarD : ∀ s0 r, Pre s0 → L.cpu s0 = L.cpu σ → (∀ x, Aligned x → ¬ User x → L.mem s0 x = ρv x) → F ar st s0 a = ok r →
      ¬ Acc r.1 → ∀ s' r', Alt st (RS s0) cls ko User s0 s' → F ar st s' a = ok r' →
        F ar (guard st (NR s0) (NWs s0)) s' a = ok r')
    (hVA : ∀ s0 r, Pre s0 → L.cpu s0 = L.cpu σ → (∀ x, Aligned x → ¬ User x → L.mem s0 x = ρv x) → F ar st s0 a = ok r → Acc r.1 →
      F ar (mguard st VW) s0 a = ok r)
    (hVD : ∀ s0 r, Pre s0 → L.cpu s0 = L.cpu σ → (∀ x, Aligned x → ¬ User x → L.mem s0 x = ρv x) → F ar st s0 a = ok r →
      ¬ Acc r.1 → ∀ s' r', Alt st (RS s0) cls ko User s0 s' → F ar st s' a = ok r' →
        F ar (mguard st VW) s' a = ok r')
    (hNG : ∀ s0 s, Pre s0 → L.cpu s0 = L.cpu σ → (∀ x, Aligned x → ¬ User x → L.mem s0 x = ρv x) →
      Alt st (RS s0) cls ko User s0 s → Within st ar (fun b => ¬ G b) (fun b => User b ∨ ¬ G b) p s a) :
    InsA G QA NP own cls kt (L.cpu σ) (Locks σ) μ
      (tr (RS σ) User cls ko (L.cpu σ) (L.ksb σ) (masksOf st σ) ar p ∅ a) := by
  obtain ⟨hRI, hrun⟩ := body_runVW hL hO hp O Sd hN hT hmk hpre hρ hV hN1 hN2 hKc hNW hO1 hO2W hNR hNWs hNarA hNarD
    hVA hVD
  refine insA_of_runsQ hQA hL hGo hGko _ ∅ μ (fun _ => none) ⟨fun ν hν => ?_, fun y u hu => (by cases hu),
    fun y u hu => (by cases hu), fun y u hu => (by cases hu), hRI, fun y u hu => (by cases hu)⟩
  obtain ⟨κ, s0, s, Rr, Wr, hD, hAR, hp0, hc0, hm0, hAl, hm, hk, hc, hWa, hW, hOn, hrd⟩ := hrun ν hν
  have hG := hNG s0 s hp0 hc0 hm0 hAl
  refine ⟨κ, hD, hAR, ?_⟩
  exact insT_sim (L := L) hmk (G := G) (Q := QA) (NP := NP) (R := RS σ) (ko := ko) (Rr := Rr) (Wr := Wr) hWa p s a
    ∅ ∅ ν hW (insT_of_within p s a hG) (Within.mono (fun b hb hg => absurd hg hb) (fun _ _ => trivial) p s a hG)
    hOn hm hk hc hrd

end body

section path
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko kt : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **`LocalPath.safeVQW`'s `InsA` counterpart** (module docstring): its hypotheses plus `hNG` at the start states
`Q0` and their alternatives. -/
theorem LocalPath.insAVQW (P : LocalPath own cls ko User) {G : U64 → Prop} {QA : U64 → U64 → Prop}
    {NP : U64 → Prop} (hQA : Equivalence QA)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → kt x = .free)
    (hL : MoveHeld own) (hO : OwnDep own User)
    {ρv ρ μ : U64 → U64} {σ : P.S} {a : P.A} (hpre : P.Pre σ)
    (hρ : ∀ x, Aligned x → ¬ User x → P.L.mem σ x = ρv x)
    (hV : VEq own cls kt (P.L.cpu σ) (P.Locks σ) ρ μ)
    {N Kc NW DD : U64 → Prop}
    (hN1 : ∀ x, N x → ρv x = ρ x) (hN2 : ∀ x, N x → own ρv x = own ρ x) (hKc : ∀ x, Kc x → ko x = kt x)
    (hNW : ∀ x, NW x → N x ∧ Kc x)
    (hO1 : ∀ m m' : U64 → U64, (∀ x, Aligned x → ¬ User x → ρv x = ρ x → m x = m' x) →
      ∀ y, ¬ DD y → own m y = own m' y)
    {VW : P.S → P.S → Prop}
    (hO2W : ∀ q, NW q → ∀ (s : P.S) v (m : U64 → U64), VW s (P.L.wr s q v) →
      (∀ x, Aligned x → ¬ User x → ρv x = ρ x → m x = P.L.mem s x) → ∀ y, DD y →
        own (Function.update m q v) y = own m y)
    {NR NWs : P.S → U64 → Prop} (hNR : ∀ s0 b, NR s0 b → N b ∧ (P.RS s0 b ∨ Kc b))
    (hNWs : ∀ s0 b, NWs s0 b → NW b)
    (Q0 : P.S → Prop) (hQ0 : Q0 σ)
    (hQu : ∀ s b v, P.Pre s → Q0 s → User b → Aligned b → Q0 (P.L.wr s b v))
    (hNarA : ∀ s0 r, P.Pre s0 → Q0 s0 → P.L.cpu s0 = P.L.cpu σ → (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) →
      P.F P.ar P.st s0 a = ok r → P.Acc r.1 → P.F P.ar (guard P.st (NR s0) (NWs s0)) s0 a = ok r)
    (hNarD : ∀ s0 r, P.Pre s0 → Q0 s0 → P.L.cpu s0 = P.L.cpu σ → (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) →
      P.F P.ar P.st s0 a = ok r → ¬ P.Acc r.1 → ∀ s' r', @Alt _ P.st P.L (P.RS s0) cls ko User s0 s' →
        P.F P.ar P.st s' a = ok r' → P.F P.ar (guard P.st (NR s0) (NWs s0)) s' a = ok r')
    (hVA : ∀ s0 r, P.Pre s0 → Q0 s0 → P.L.cpu s0 = P.L.cpu σ → (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) →
      P.F P.ar P.st s0 a = ok r → P.Acc r.1 → P.F P.ar (mguard P.st VW) s0 a = ok r)
    (hVD : ∀ s0 r, P.Pre s0 → Q0 s0 → P.L.cpu s0 = P.L.cpu σ → (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) →
      P.F P.ar P.st s0 a = ok r → ¬ P.Acc r.1 → ∀ s' r', @Alt _ P.st P.L (P.RS s0) cls ko User s0 s' →
        P.F P.ar P.st s' a = ok r' → P.F P.ar (mguard P.st VW) s' a = ok r')
    (hNG : ∀ s0 s, P.Pre s0 → Q0 s0 → P.L.cpu s0 = P.L.cpu σ →
      (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) → @Alt _ P.st P.L (P.RS s0) cls ko User s0 s →
      Within P.st P.ar (fun b => ¬ G b) (fun b => User b ∨ ¬ G b) P.p s a) :
    InsA G QA NP own cls kt (P.L.cpu σ) (P.Locks σ) μ (P.body σ a) := by
  let _ := P.L
  have hp : IsProgOn (P.F P.ar) P.ar P.st (AltOf P.st (fun s => P.Pre s ∧ Q0 s) P.RS cls ko User) P.p :=
    fun st' hN s hs a' => by
      obtain ⟨s0, h0, hA⟩ := hs
      exact P.isProg st' hN s ⟨s0, h0.1, hA⟩ a'
  have O : PathObl P.st (P.F P.ar) P.Acc own cls ko User P.Locks (fun s => P.Pre s ∧ Q0 s) P.RS P.WS P.DS :=
    ⟨fun s a' r h => P.obl.acc s a' r h.1, fun s a' r h => P.obl.dec_alt s a' r h.1,
      fun s x h => P.obl.read_own s x h.1, fun s x h => P.obl.write_own s x h.1,
      fun s x h => P.obl.aligned s x h.1, fun s a' r h => P.obl.move s a' r h.1⟩
  have Sd : PathSide P.st (P.F P.ar) cls ko User P.Locks (fun s => P.Pre s ∧ Q0 s) P.RS P.WS P.DS :=
    ⟨fun s s' a' r h => P.side.read_aligned s s' a' r h.1, fun s x h => P.side.rs_aligned s x h.1,
      P.side.ko_aligned, fun s b v h hu ha => by
        obtain ⟨e1, e2, e3, e4, e5⟩ := P.side.user_free s b v h.1 hu ha
        exact ⟨⟨e1, hQu s b v h.1 h.2 hu ha⟩, e2, e3, e4, e5⟩⟩
  have hN : ReadOnce P.st P.ar P.p cls ko User (fun s => P.Pre s ∧ Q0 s) P.RS :=
    fun s s' a' r h => P.once s s' a' r h.1
  exact body_insAVW hQA hGo hGko hL hO hp O Sd hN P.total P.masks ⟨hpre, hQ0⟩ hρ hV hN1 hN2 hKc hNW hO1 hO2W hNR
    hNWs
    (fun s0 r h1 h0 h2 h3 h4 => hNarA s0 r h1.1 h1.2 h0 h2 h3 h4)
    (fun s0 r h1 h0 h2 h3 h4 => hNarD s0 r h1.1 h1.2 h0 h2 h3 h4)
    (fun s0 r h1 h0 h2 h3 h4 => hVA s0 r h1.1 h1.2 h0 h2 h3 h4)
    (fun s0 r h1 h0 h2 h3 h4 => hVD s0 r h1.1 h1.2 h0 h2 h3 h4)
    (fun s0 s h1 h0 h2 h3 => hNG s0 s h1.1 h1.2 h0 h2 h3)

/-- **`LocalPath.safeVQ`'s `InsA` counterpart** (module docstring): `insAVQW` at the trivial check, as
`safeVQ_of_W`. -/
theorem LocalPath.insAVQ (P : LocalPath own cls ko User) {G : U64 → Prop} {QA : U64 → U64 → Prop}
    {NP : U64 → Prop} (hQA : Equivalence QA)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → kt x = .free)
    (hL : MoveHeld own) (hO : OwnDep own User)
    {ρv ρ μ : U64 → U64} {σ : P.S} {a : P.A} (hpre : P.Pre σ)
    (hρ : ∀ x, Aligned x → ¬ User x → P.L.mem σ x = ρv x)
    (hV : VEq own cls kt (P.L.cpu σ) (P.Locks σ) ρ μ)
    {N Kc NW DD : U64 → Prop}
    (hN1 : ∀ x, N x → ρv x = ρ x) (hN2 : ∀ x, N x → own ρv x = own ρ x) (hKc : ∀ x, Kc x → ko x = kt x)
    (hNW : ∀ x, NW x → N x ∧ Kc x)
    (hO1 : ∀ m m' : U64 → U64, (∀ x, Aligned x → ¬ User x → ρv x = ρ x → m x = m' x) →
      ∀ y, ¬ DD y → own m y = own m' y)
    (hO2 : ∀ q, NW q → ∀ (m : U64 → U64) v y, DD y → own (Function.update m q v) y = own m y)
    {NR NWs : P.S → U64 → Prop} (hNR : ∀ s0 b, NR s0 b → N b ∧ (P.RS s0 b ∨ Kc b))
    (hNWs : ∀ s0 b, NWs s0 b → NW b)
    (Q0 : P.S → Prop) (hQ0 : Q0 σ)
    (hQu : ∀ s b v, P.Pre s → Q0 s → User b → Aligned b → Q0 (P.L.wr s b v))
    (hNarA : ∀ s0 r, P.Pre s0 → Q0 s0 → P.L.cpu s0 = P.L.cpu σ → (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) →
      P.F P.ar P.st s0 a = ok r → P.Acc r.1 → P.F P.ar (guard P.st (NR s0) (NWs s0)) s0 a = ok r)
    (hNarD : ∀ s0 r, P.Pre s0 → Q0 s0 → P.L.cpu s0 = P.L.cpu σ → (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) →
      P.F P.ar P.st s0 a = ok r → ¬ P.Acc r.1 → ∀ s' r', @Alt _ P.st P.L (P.RS s0) cls ko User s0 s' →
        P.F P.ar P.st s' a = ok r' → P.F P.ar (guard P.st (NR s0) (NWs s0)) s' a = ok r')
    (hNG : ∀ s0 s, P.Pre s0 → Q0 s0 → P.L.cpu s0 = P.L.cpu σ →
      (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) → @Alt _ P.st P.L (P.RS s0) cls ko User s0 s →
      Within P.st P.ar (fun b => ¬ G b) (fun b => User b ∨ ¬ G b) P.p s a) :
    InsA G QA NP own cls kt (P.L.cpu σ) (P.Locks σ) μ (P.body σ a) := by
  let _ := P.L
  have hv : ∀ s0 r, AltOf P.st P.Pre P.RS cls ko User s0 → P.F P.ar P.st s0 a = ok r →
      P.F P.ar (mguard P.st (fun _ _ => True)) s0 a = ok r := by
    intro s0 r hs h
    rw [P.isProg _ (Narrow.mguard _ _) s0 hs a]
    rw [P.isProg _ (Narrow.self _) s0 hs a] at h
    exact Fl4Proofs.P2.E2EV.mguard_of_withinM P.p s0 a r h (withinM_true P.p s0 a)
  exact P.insAVQW hQA hGo hGko hL hO hpre hρ hV hN1 hN2 hKc hNW hO1 (VW := fun _ _ => True)
    (fun q hq _ v m _ _ y hy => hO2 q hq m v y hy) hNR hNWs Q0 hQ0 hQu hNarA hNarD
    (fun s0 r h1 _ _ _ h _ => hv s0 r (AltOf.pre h1) h)
    (fun s0 _ h1 _ _ _ _ _ s' r' hA h => hv s' r' ⟨s0, h1, hA⟩ h) hNG

end path

end
end Fl4Proofs.P2.E2E
