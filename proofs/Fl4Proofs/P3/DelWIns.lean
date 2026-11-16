/-
P3 (DESIGN.md §9), CSpace: **the TCB cap installs' insert as a W-step**
(DelW's `SlotHypW`): FL4's checks and `cdt::insert` into a TCB slot write
only slot words (`install_after_frame`, `check_insert_frame`), and the
spec's `check_cap_at`/`cap_insert` is `CnK` (`nkn_checkCapAt`,
`cnk_of_inst`).
-/
import Fl4Proofs.P3.DelW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## The spec's checks and insert are `CnK` -/

section Spec
open Fl4Spec Ipc

theorem nkn_checkCapAt {m : SMonad Unit Unit} (h : NKN m) (c : Cap) (sl : CslotPtr) :
    NKN (checkCapAt (Z := Unit) c sl m) := by
  unfold checkCapAt
  refine nkn_bind (nkn_getCap _) fun _ => ?_
  unfold NonDet.when
  split
  · exact h
  · exact nkn_pure _

theorem cnk_of_liftE {m : SMonad Unit Unit} (h : NKN m) {σ σ' : State Unit}
    (hr : ((.ok (), σ') : Except Unit Unit × State Unit) ∈ ((NonDetE.liftE (ε := Unit) m).run σ).1) :
    CnK σ σ' := by
  unfold NonDetE.liftE at hr
  rw [ExceptT.run_lift] at hr
  obtain ⟨x, hx, hy⟩ := hr
  have e : ((.ok (), σ') : Except Unit Unit × State Unit) = (.ok x.1, x.2) := Set.mem_singleton_iff.1 hy
  have e2 : σ' = x.2 := congrArg Prod.snd e
  subst e2
  exact h σ x hx

/-- **The install's spec step is `CnK`**: `unless` the new cap is null,
the two checks and `cap_insert`. -/
theorem cnk_of_inst {b : Prop} [Decidable b] {c1 c2 c : Cap} {sl1 sl2 src dst : CslotPtr} {σ σ' : State Unit}
    (h : (NonDetE.unlessE (ε := Unit) b (NonDetE.liftE (checkCapAt c1 sl1 (checkCapAt c2 sl2
      (capInsert (Z := Unit) c src dst))))).run σ = ({(.ok (), σ')}, False)) : CnK σ σ' := by
  have hm : ((.ok (), σ') : Except Unit Unit × State Unit) ∈ ((NonDetE.unlessE (ε := Unit) b
      (NonDetE.liftE (checkCapAt c1 sl1 (checkCapAt c2 sl2 (capInsert (Z := Unit) c src dst))))).run σ).1 := by
    rw [h]; rfl
  unfold NonDetE.unlessE at hm
  split at hm
  · have e : ((.ok (), σ') : Except Unit Unit × State Unit) = (.ok (), σ) := Set.mem_singleton_iff.1 hm
    have e2 : σ' = σ := congrArg Prod.snd e
    subst e2; exact CnK.refl _
  · exact cnk_of_liftE (nkn_checkCapAt (nkn_checkCapAt (capInsert_nkn _ _ _) _ _) _ _) hm

/-- The frame cap's checks and insert are `CnK`. -/
theorem cnk_of_check {c1 c2 c : Cap} {sl1 sl2 src dst : CslotPtr} {σ σ' : State Unit}
    (h : checkCapAt (Z := Unit) c1 sl1 (checkCapAt c2 sl2 (capInsert (Z := Unit) c src dst)) σ = ({((), σ')}, False)) :
    CnK σ σ' :=
  nkn_checkCapAt (nkn_checkCapAt (capInsert_nkn _ _ _) _ _) _ _ σ ((), σ') (by rw [h]; rfl)

end Spec

/-! ## FL4's checks and insert write only slot words -/

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem still_valid_eq' (s : S) (t slot src : U64) (nc : capability.Cap) (hsrc : src ≠ 0#u64) :
    tcb.still_valid st s t slot nc src =
      ok (soB nc (capV (L.mem s) src) && soB (.Thread t) (capV (L.mem s) slot)) := by
  unfold tcb.still_valid
  simp only [is_null_eq, hsrc, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, capAt_capV, bind_ok,
    soB_eq]
  cases soB nc (capV (L.mem s) src) <;> simp

/-- **The frame cap's checks and insert write only slot words.** -/
theorem check_insert_frame (hP : Placed th) (s1 : S) {G : MdbGhost} (hM : MdbLinks th (L.mem s1) G)
    (hD : DelInv th (L.mem s1)) (t slot : U64) (nc : capability.Cap) {src dest : U64} (hsrc : IsSlot th src)
    (hdst : IsSlot th dest) :
    (do
      let b ← tcb.still_valid st s1 t slot nc src
      if b = true then cdt.insert st s1 nc src dest else ok s1) ⦃ s4 => Vs.SlotFrame2 (L := L) th s1 s4 ⦄ := by
  rw [still_valid_eq' _ _ _ _ nc (hsrc.ne_zero hP)]
  simp only [bind_ok]
  split
  · exact Vs.insert_frame2 hP s1 nc src dest hsrc hdst _ (capAt_capV _ _) (nb_of hP hM hD hsrc).2
  · rw [WP.spec_ok]; exact Vs.SlotFrame2.refl s1

/-- **The install's checks and insert write only slot words.** -/
theorem install_after_frame {A : Type} (hP : Placed th) (s1 : S) (a1 : A) {G : MdbGhost}
    (hM : MdbLinks th (L.mem s1) G) (hD : DelInv th (L.mem s1)) (t slot : U64) (nc : capability.Cap)
    {src dest : U64} (hsrc : IsSlot th src) (hdst : IsSlot th dest) :
    (do
      let b ← nc.is_null
      if b = true then ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s1, a1)
        else do
          let b1 ← tcb.still_valid st s1 t slot nc src
          if b1 = true then do
              let s2 ← cdt.insert st s1 nc src dest
              ok (core.result.Result.Ok (), s2, a1)
            else ok (core.result.Result.Ok (), s1, a1)) ⦃ res =>
      Vs.SlotFrame2 (L := L) th s1 res.2.1 ⦄ := by
  by_cases hnn : nc = .Null
  · subst hnn
    rw [cap_is_null_null]; simp only [bind_ok, ↓reduceIte, WP.spec_ok]
    exact Vs.SlotFrame2.refl s1
  rw [cap_is_null_ne hnn]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  rw [still_valid_eq' _ _ _ _ nc (hsrc.ne_zero hP)]
  simp only [bind_ok]
  split
  · exact WP.spec_bind (Vs.insert_frame2 hP s1 nc src dest hsrc hdst _ (capAt_capV _ _) (nb_of hP hM hD hsrc).2)
      fun s2 h => (WP.spec_ok _).2 h
  · rw [WP.spec_ok]; exact Vs.SlotFrame2.refl s1

end


/-! ## An invariant of the memory and the ghost tree as a `W` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- An invariant `Q` of the memory and the ghost tree, kept by every ghost
step, as a W-invariant. -/
abbrev WQ (Q : (U64 → U64) → MdbGhost → Prop) : S → A → Fl4Spec.State Unit → MdbGhost → Prop :=
  fun s _ _ G => Q (L.mem s) G

/-- **The deletion's W-premises at `WQ Q`**, from the plain ones and `Q`
kept by the ghost steps. -/
theorem delHypsW_Q {Q : (U64 → U64) → MdbGhost → Prop} (hQ : ∀ m G m' G', MdbStep m G m' G' → Q m G → Q m' G')
    {th : TypedHeap} (hO : FinObjHyp (L := L) arI th) (hPP : PPHypD (L := L) arI th)
    (hPD : PostDelHyp (L := L) arI th) : DelHypsW (L := L) arI (WQ (L := L) (A := A) Q) th := by
  refine ⟨fun s a σ G sl c hDS hW hA hc hk => ?_, fun s a σ G hDS hW => ?_, fun s a σ G cl hDS hW h1 h2 h3 => ?_,
    fun s s' a σ σ' G G' hW _ _ _ _ hSt => hQ _ _ _ _ hSt hW⟩
  · refine WP.spec_mono (hO s a σ G sl c hDS hA hc hk) ?_
    rintro r ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, hQ _ _ _ _ h8 hW⟩
  · refine WP.spec_mono (hPP s a σ G hDS) ?_
    rintro r ⟨hS, σ', hc, hCR⟩
    exact ⟨hS, σ', hc, hCR, hQ _ _ _ _ (MdbStep.of_same hDS.1.2.2.1 hS) hW⟩
  · refine WP.spec_mono (hPD s a σ G cl hDS h1 h2 h3) ?_
    rintro r ⟨hS, σ', hc, hCR⟩
    exact ⟨hS, σ', hc, hCR, hQ _ _ _ _ (MdbStep.of_same hDS.1.2.2.1 hS) hW⟩

end

end

end Fl4Proofs.P3
