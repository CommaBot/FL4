/-
# P2 (line p3mc, gen 19): `LocalPath.safeVQ` with value-checked writes (`LocalPath.safeVQW`)

* **`LocalPath.safeVQW`**: `LocalPath.safeVQ` (P2/SafeVQ) over `body_safeVW` (P2/ViewSafeGenW): the owner fact
  `hO2W` is asked only for writes passing a step check `VW` (store state before and after the write), at a memory
  agreeing with the store state off `{ρv ≠ ρ}`; the accepted run from every start state satisfying `Q` and the
  declined runs at its alternatives pass `mguard P.st VW` (`hVA` / `hVD`).
* **`safeVQ_of_W`**: the old `safeVQ` statement, proved from `safeVQW` with `VW := fun _ _ => True` (the old
  `hO2` gives `hO2W`; every run passes `mguard st (fun _ _ => True)`, `withinM_true` + `mguard_of_withinM`). So
  `safeVQW` generalises `safeVQ`.

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.ViewSafeGenW
import Fl4Proofs.P2.SafeVQ
import Fl4Proofs.P2.E2EVCut
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner VEq Safe MoveHeld)

noncomputable section
open Classical

section safe
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko kt : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **`LocalPath.safeVQ` with value-checked writes** (module docstring). -/
theorem LocalPath.safeVQW (P : LocalPath own cls ko User) (hL : MoveHeld own) (hO : OwnDep own User)
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
    (Q : P.S → Prop) (hQ : Q σ)
    (hQu : ∀ s b v, P.Pre s → Q s → User b → Aligned b → Q (P.L.wr s b v))
    (hNarA : ∀ s0 r, P.Pre s0 → Q s0 → P.L.cpu s0 = P.L.cpu σ → (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) →
      P.F P.ar P.st s0 a = ok r → P.Acc r.1 → P.F P.ar (guard P.st (NR s0) (NWs s0)) s0 a = ok r)
    (hNarD : ∀ s0 r, P.Pre s0 → Q s0 → P.L.cpu s0 = P.L.cpu σ → (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) →
      P.F P.ar P.st s0 a = ok r → ¬ P.Acc r.1 → ∀ s' r', @Alt _ P.st P.L (P.RS s0) cls ko User s0 s' →
        P.F P.ar P.st s' a = ok r' → P.F P.ar (guard P.st (NR s0) (NWs s0)) s' a = ok r')
    (hVA : ∀ s0 r, P.Pre s0 → Q s0 → P.L.cpu s0 = P.L.cpu σ → (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) →
      P.F P.ar P.st s0 a = ok r → P.Acc r.1 → P.F P.ar (mguard P.st VW) s0 a = ok r)
    (hVD : ∀ s0 r, P.Pre s0 → Q s0 → P.L.cpu s0 = P.L.cpu σ → (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) →
      P.F P.ar P.st s0 a = ok r → ¬ P.Acc r.1 → ∀ s' r', @Alt _ P.st P.L (P.RS s0) cls ko User s0 s' →
        P.F P.ar P.st s' a = ok r' → P.F P.ar (mguard P.st VW) s' a = ok r') :
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
  exact body_safeVW hL hO hp O Sd hN P.total P.masks ⟨hpre, hQ⟩ hρ hV hN1 hN2 hKc hNW hO1 hO2W hNR hNWs
    (fun s0 r h1 h0 h2 h3 h4 => hNarA s0 r h1.1 h1.2 h0 h2 h3 h4)
    (fun s0 r h1 h0 h2 h3 h4 => hNarD s0 r h1.1 h1.2 h0 h2 h3 h4)
    (fun s0 r h1 h0 h2 h3 h4 => hVA s0 r h1.1 h1.2 h0 h2 h3 h4)
    (fun s0 r h1 h0 h2 h3 h4 => hVD s0 r h1.1 h1.2 h0 h2 h3 h4)

end safe

section triv
variable {S A X : Type} {st : machine.Store S} {ar : machine.Arch A}

/-- Every run keeps the trivial step check. -/
theorem withinM_true (p : SProg X) : ∀ (s : S) (a : A), WithinM st ar (fun _ _ => True) p s a := by
  induction p with
  | ret x => intro s a; trivial
  | err e => intro s a; trivial
  | rd q k ih => intro s a; simp only [WithinM]; exact fun v _ => ih v s a
  | rdp q k ih => intro s a; simp only [WithinM]; exact fun v _ => ih v s a
  | wr q v k ih => intro s a; simp only [WithinM]; exact fun s' _ => ⟨trivial, ih s' a⟩
  | zero q n k ih => intro s a; simp only [WithinM]; exact fun s' _ => ⟨trivial, ih s' a⟩
  | clr q n k ih => intro s a; simp only [WithinM]; exact fun s' _ => ⟨trivial, ih s' a⟩
  | ksb k ih => intro s a; simp only [WithinM]; exact fun v _ => ih v s a
  | cpu k ih => intro s a; simp only [WithinM]; exact fun v _ => ih v s a
  | masks k ih => intro s a; simp only [WithinM]; exact fun v _ => ih v s a
  | arch op k ih => intro s a; simp only [WithinM]; exact fun v a' _ => ih v s a'

end triv

section of_W
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko kt : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **The old `safeVQ` is `safeVQW` at `VW := True`** (module docstring): the statement of `LocalPath.safeVQ`,
proved through `LocalPath.safeVQW`. -/
theorem safeVQ_of_W (P : LocalPath own cls ko User) (hL : MoveHeld own) (hO : OwnDep own User)
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
  have hv : ∀ s0 r, AltOf P.st P.Pre P.RS cls ko User s0 → P.F P.ar P.st s0 a = ok r →
      P.F P.ar (mguard P.st (fun _ _ => True)) s0 a = ok r := by
    intro s0 r hs h
    rw [P.isProg _ (Narrow.mguard _ _) s0 hs a]
    rw [P.isProg _ (Narrow.self _) s0 hs a] at h
    exact Fl4Proofs.P2.E2EV.mguard_of_withinM P.p s0 a r h (withinM_true P.p s0 a)
  exact P.safeVQW hL hO hpre hρ hV hN1 hN2 hKc hNW hO1 (VW := fun _ _ => True)
    (fun q hq _ v m _ _ y hy => hO2 q hq m v y hy) hNR hNWs Q hQ hQu hNarA hNarD
    (fun s0 r h1 _ _ _ h _ => hv s0 r (AltOf.pre h1) h)
    (fun s0 _ h1 _ _ _ _ _ s' r' hA h => hv s' r' ⟨s0, h1, hA⟩ h)

end of_W

end
end Fl4Proofs.P2.E2E
