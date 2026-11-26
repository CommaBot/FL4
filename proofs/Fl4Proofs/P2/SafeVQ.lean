/-
# P2 (line p3mc, gen 12): `LocalPath.safeV` on a restricted set of start states, and one run for all of them

* **`LocalPath.safeVQ`**: `LocalPath.safeV` (P2/ViewSafeGen) where the narrowed run facts `hNarA` / `hNarD` are
  asked only at start states satisfying a predicate `Q` that holds at the start and is kept by user writes. It is
  `body_safeV` with `Pre ∧ Q` for `Pre`: every field of the path (`isProg`, `obl`, `side`, `once`) restricts to
  `Pre ∧ Q` (`side.user_free` by `hQu`).
* **`run_transfer`**: a guarded run of a path's tree from one state `σ` gives the same guarded run from every state
  that agrees with `σ` on the guard's read set, the kernel base, the core and the frame masks
  (`PathAgree.interp_agree`; the plain run there is that guarded run, `interp_guard`).

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.ViewSafeGen
import Fl4Proofs.P2.PathAgree
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner VEq Safe MoveHeld)

noncomputable section
open Classical

section safe
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko kt : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **`LocalPath.safeV` with the narrowed run facts asked only at starts satisfying `Q`** (module docstring). -/
theorem LocalPath.safeVQ (P : LocalPath own cls ko User) (hL : MoveHeld own) (hO : OwnDep own User)
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
    (Q : P.S → Prop) (hQ : Q σ)
    (hQu : ∀ s b v, P.Pre s → Q s → User b → Aligned b → Q (P.L.wr s b v))
    (hNarA : ∀ s0 r, P.Pre s0 → Q s0 → P.L.cpu s0 = P.L.cpu σ → (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) →
      P.F P.ar P.st s0 a = ok r → P.Acc r.1 → P.F P.ar (guard P.st (NR s0) (NWs s0)) s0 a = ok r)
    (hNarD : ∀ s0 r, P.Pre s0 → Q s0 → P.L.cpu s0 = P.L.cpu σ → (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) →
      P.F P.ar P.st s0 a = ok r → ¬ P.Acc r.1 → ∀ s' r', @Alt _ P.st P.L (P.RS s0) cls ko User s0 s' →
        P.F P.ar P.st s' a = ok r' → P.F P.ar (guard P.st (NR s0) (NWs s0)) s' a = ok r') :
    Safe own cls kt (P.L.cpu σ) (P.Locks σ) μ (P.body σ a) := by
  let _ := P.L
  have hp : IsProgOn (P.F P.ar) P.ar P.st (AltOf P.st (fun s => P.Pre s ∧ Q s) P.RS cls ko User) P.p :=
    fun st' hN s hs a' => by
      obtain ⟨s0, h0, hA⟩ := hs
      exact P.isProg st' hN s ⟨s0, h0.1, hA⟩ a'
  have O : PathObl P.st (P.F P.ar) P.Acc own cls ko User P.Locks (fun s => P.Pre s ∧ Q s) P.RS P.WS P.DS :=
    ⟨fun s a' r h => P.obl.acc s a' r h.1, fun s a' r h => P.obl.dec_alt s a' r h.1,
      fun s x h => P.obl.read_own s x h.1, fun s x h => P.obl.write_own s x h.1,
      fun s x h => P.obl.aligned s x h.1, fun s a' r h => P.obl.move s a' r h.1⟩
  have Sd : PathSide P.st (P.F P.ar) cls ko User P.Locks (fun s => P.Pre s ∧ Q s) P.RS P.WS P.DS :=
    ⟨fun s s' a' r h => P.side.read_aligned s s' a' r h.1, fun s x h => P.side.rs_aligned s x h.1,
      P.side.ko_aligned, fun s b v h hu ha => by
        obtain ⟨e1, e2, e3, e4, e5⟩ := P.side.user_free s b v h.1 hu ha
        exact ⟨⟨e1, hQu s b v h.1 h.2 hu ha⟩, e2, e3, e4, e5⟩⟩
  have hN : ReadOnce P.st P.ar P.p cls ko User (fun s => P.Pre s ∧ Q s) P.RS :=
    fun s s' a' r h => P.once s s' a' r h.1
  exact body_safeV hL hO hp O Sd hN P.total P.masks ⟨hpre, hQ⟩ hρ hV hN1 hN2 hKc hNW hO1 hO2 hNR hNWs
    (fun s0 r h1 h0 h2 h3 h4 => hNarA s0 r h1.1 h1.2 h0 h2 h3 h4)
    (fun s0 r h1 h0 h2 h3 h4 => hNarD s0 r h1.1 h1.2 h0 h2 h3 h4)

end safe

section transfer
variable {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}

/-- **One guarded run for every agreeing state** (module docstring). -/
theorem run_transfer (hm : MasksWr st) {F : machine.Store S → S → A → Result (X × S × A)} {p : SProg X}
    (hz : NoZero p) {G : S → Prop} (hp : IsProgOn F ar st G p) {Rd Wr : U64 → Prop}
    (hRal : ∀ w, Rd w → Aligned w) (hWal : ∀ w, Wr w → Aligned w)
    {σ s' : S} {a : A} {rσ r' : X × S × A} (hσ : G σ) (hs' : G s')
    (h1 : L.ksb s' = L.ksb σ) (h2 : L.cpu s' = L.cpu σ) (h3 : st.frame_masks s' = st.frame_masks σ)
    (h4 : ∀ w, Rd w → L.mem s' w = L.mem σ w)
    (hg : F (guard st Rd Wr) σ a = ok rσ) (hr : F st s' a = ok r') :
    F (guard st Rd Wr) s' a = ok r' := by
  rw [hp _ (Narrow.guard _ _ _) σ hσ a] at hg
  obtain ⟨x, s1, a1⟩ := rσ
  obtain ⟨s1', h'⟩ := interp_agree hm hRal hWal p hz σ s' a x s1 a1 h1 h2 h3 h4 hg
  have e := (interp_guard p s' a _ h').1
  rw [hp _ (Narrow.self _) s' hs' a, e] at hr
  rw [hp _ (Narrow.guard _ _ _) s' hs' a, h', hr]

end transfer

end
end Fl4Proofs.P2.E2E
