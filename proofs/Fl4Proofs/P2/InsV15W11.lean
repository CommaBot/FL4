/-
# P2 (line p3mc, gen 48): the W11 paths at a CoreView start touch no paging word of the epoch

`LocalPath.insAVQ` / `insAVQW` (P2/InsVQ) need `hNG`: every run from a start state of the view, or from an
alternative of one, touches no `PWE K E` word but user words. mmuAD's `w11_noG` (P2/E2EPU3d) gives this for every W11
path at every memory parameter `m`, at start states satisfying `QPs (KU K E)`; its `qPs_ku` derives that `QPs` from
agreement of the start state with the epoch state on **every** kernel word. At a view start the state agrees with
the view; `QPs (KU K E)` reads only the ASID table words `atAF K.ksb hi` (region `.none`), which the view keeps and
which equal the epoch memory `E` there (gate words off `PWE`, `EpochJ.eq`).

* `qPs_ku_of`: `QPs (KU K E)` from `QPs K`, `K.ptes = ptesR K E` and agreement with `E` on the ASID table words
  (`qPs_ku`'s argument without its kernel-word premise).
* **`atAF_view`**: at a CoreView start (`VEq` to the physical memory, `EpochJV`, no VCPU, a bundle state), the view
  equals `E` on the ASID table words.
* `LocalPath.NoGStarts P G ρv`: every run from a start state of `P` agreeing with `ρv` on the aligned kernel words,
  or from an alternative of one, reads no `G` word and writes only user words or words off `G`.
* **`w11C_noGS`** / **`w11B_noGS`** / **`w11A_noGS`**: every path of `fl4LocW11JC` / `fl4LocW11JB` / `fl4LocW11JA` at
  the view has `NoGStarts (PWE K E)` (`w11_noG`'s argument, `allC` / `allB` / `allA` at `KU K E`).

No named premise. New module; no existing file touched.
-/
import Fl4Proofs.P2.InsVQ
import Fl4Proofs.P2.InsV15O
import Fl4Proofs.P2.E2EPU3d
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2E
open Fl4Proofs.P1

section nog
variable {own : (U64 → U64) → U64 → Serial.Owner U64 U64} {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64}
  {User : U64 → Prop}

/-- **The runs from a path's start states agreeing with `ρv` on the aligned kernel words, and from their
alternatives, touch no `G` word but user words** (module docstring). -/
def LocalPath.NoGStarts (P : LocalPath own cls ko User) (G : U64 → Prop) (ρv : U64 → U64) : Prop :=
  ∀ (s1 s2 : P.S) (a : P.A), P.Pre s1 → (∀ x, Aligned x → ¬ User x → P.L.mem s1 x = ρv x) →
    @PathObl.Alt _ P.st P.L (P.RS s1) cls ko User s1 s2 →
    PathObl.Within P.st P.ar (fun b => ¬ G b) (fun b => User b ∨ ¬ G b) P.p s2 a

end nog

end Fl4Proofs.P2.E2E

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg VEq)
open Fl4Proofs.P2.MmuAD (ADEq NotPresent)

noncomputable section
open Classical

section qps
variable {K : KLayoutP} {E : U64 → U64}

/-- **`QPs (KU K E)` from agreement with `E` on the ASID table words** (module docstring). -/
theorem qPs_ku_of {S : Type} {st : machine.Store S} [L : LawfulStore st] (hcv : K.ptes = ptesR K E) {σ : S}
    (hq : QPs K st σ) (hm : ∀ hi : U64, hi.val < 2048 → L.mem σ (atAF K.ksb hi) = E (atAF K.ksb hi)) :
    QPs (KU K E) st σ := by
  have hnA : ∀ b, AsidW K.ksb E b → ¬ PWE K E b := fun b hb => pwe_asid hcv hb
  refine ⟨fun o ho hb => ?_, hq.ksb, ?_, hq.al, hq.uoff⟩
  · obtain ⟨hp, -⟩ := hb
    rcases hp with hp | h
    · exact hq.ks o ho hp
    · exact h.2.2.2.2 o ho rfl
  · intro hi hhi
    rw [hq.ksb]
    refine ⟨fun hb => hnA _ (Or.inl ⟨hi, hhi, rfl⟩) hb.1, fun lo hlo hne hb => ?_⟩
    rw [hm hi hhi] at hne hb
    exact hnA _ (Or.inr ⟨hi, hhi, hne, lo, hlo, rfl⟩) hb.1

/-- **The view equals the epoch memory on the ASID table words** (module docstring). -/
theorem atAF_view {S' : Type} {st' : machine.Store S'} (L' : LawfulStore st') {s : Cfg U64 U64 U64 U64}
    (J : EpochJV K E s) (nv : K.vcpus = ∅) (hM : MapsP K s) {c : U64} {hs : U64 → Prop} {ρ : U64 → U64}
    (hV : VEq s.own s.cls s.ko c hs ρ s.mem) (hb : ∃ σe, SlJAt (L := L') K.toKLayout σe) {hi : U64}
    (hhi : hi.val < 2048) : CoreView.view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi) := by
  obtain ⟨σe, A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B⟩ := hb
  have hr := region_none_tab B hhi
  have hnP : ¬ PWE K E (atAF K.ksb hi) := pwe_asid J.conv (Or.inl ⟨hi, hhi, rfl⟩)
  have hg : GateW K (atAF K.ksb hi) := gateW_of_region hr (fun hp => hnP (Or.inl hp)) nv
  rw [CoreView.view_none (by unfold CoreView.repl CoreView.repl2; rw [hr])]
  rw [hV.2.1 _ (by rw [hM.own, hg s.mem]; exact Or.inr rfl)]
  exact J.eq _ hg hnP

end qps

section w11
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- **Every `fl4LocW11JC` path at the view has `NoGStarts (PWE K E)`** (module docstring). -/
theorem w11C_noGS (i : Fl4IxW (S := S)) {K : KLayoutP} {E : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    (nv : K.vcpus = ∅) (hcv : K.ptes = ptesR K E) {c : U64} {ρ : U64 → U64}
    (hT : ∀ hi : U64, hi.val < 2048 → CoreView.view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi)) :
    (fl4LocW11JC st ar hA hm hSt a0 i K (CoreView.view K.toKLayout c ρ) hK hU).NoGStarts (PWE K E)
      (CoreView.view K.toKLayout c ρ) := by
  intro s1 s2 a hp hmm hAl
  letI := (fl4LocW11JC st ar hA hm hSt a0 i K (CoreView.view K.toKLayout c ρ) hK hU).L
  have hqK : QPt K (fl4LocW11JC st ar hA hm hSt a0 i K (CoreView.view K.toKLayout c ρ) hK hU) s1 := hp.2
  have hq : QPt (KU K E) (fl4LocW11JC st ar hA hm hSt a0 i K (CoreView.view K.toKLayout c ρ) hK hU) s1 :=
    qPs_ku_of hcv hqK fun hi hhi =>
      (hmm _ (hqK.al hi hhi) (fun hu => hqK.uoff _ (Or.inl hu) hi hhi rfl)).trans (hT hi hhi)
  have hK' := regionOKP_ku (E := E) hK nv
  have hU' := userOKP_ku (E := E) hU
  have hAv := allC st ar hA hm hSt a0 i (KU K E) (CoreView.view K.toKLayout c ρ) hK' hU'
  obtain ⟨hp1, -⟩ := hp
  exact LocalPath.noPWE_of_avoid _ (fun _ _ h => ownV_pwe_gate hK nv h) hAv ⟨hp1, hq⟩ hAl
    (fun x hx hn => ⟨hx, fun hp => hn (pte_ku hU hp)⟩) a

/-- **Every `fl4LocW11JB` path at the view has `NoGStarts (PWE K E)`** (module docstring). -/
theorem w11B_noGS (i : Fl4IxW (S := S)) {K : KLayoutP} {E : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    (nv : K.vcpus = ∅) (hcv : K.ptes = ptesR K E) {c : U64} {ρ : U64 → U64}
    (hT : ∀ hi : U64, hi.val < 2048 → CoreView.view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi)) :
    (fl4LocW11JB st ar hA hm hSt a0 i K (CoreView.view K.toKLayout c ρ) hK hU).NoGStarts (PWE K E)
      (CoreView.view K.toKLayout c ρ) := by
  intro s1 s2 a hp hmm hAl
  letI := (fl4LocW11JB st ar hA hm hSt a0 i K (CoreView.view K.toKLayout c ρ) hK hU).L
  have hqK : QPt K (fl4LocW11JB st ar hA hm hSt a0 i K (CoreView.view K.toKLayout c ρ) hK hU) s1 := hp.2
  have hq : QPt (KU K E) (fl4LocW11JB st ar hA hm hSt a0 i K (CoreView.view K.toKLayout c ρ) hK hU) s1 :=
    qPs_ku_of hcv hqK fun hi hhi =>
      (hmm _ (hqK.al hi hhi) (fun hu => hqK.uoff _ (Or.inl hu) hi hhi rfl)).trans (hT hi hhi)
  have hK' := regionOKP_ku (E := E) hK nv
  have hU' := userOKP_ku (E := E) hU
  have hAv := allB st ar hA hm hSt a0 i (KU K E) (CoreView.view K.toKLayout c ρ) hK' hU'
  obtain ⟨hp1, -⟩ := hp
  exact LocalPath.noPWE_of_avoid _ (fun _ _ h => ownV_pwe_gate hK nv h) hAv ⟨hp1, hq⟩ hAl
    (fun x hx hn => ⟨hx, fun hp => hn (pte_ku hU hp)⟩) a

/-- **Every `fl4LocW11JA` path at the view has `NoGStarts (PWE K E)`** (`w11_noG`). -/
theorem w11A_noGS (i : Fl4IxW (S := S)) {K : KLayoutP} {E : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    (nv : K.vcpus = ∅) (hcv : K.ptes = ptesR K E) {c : U64} {ρ : U64 → U64}
    (hT : ∀ hi : U64, hi.val < 2048 → CoreView.view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi)) :
    (fl4LocW11JA st ar hA hm hSt a0 i K (CoreView.view K.toKLayout c ρ) hK hU).NoGStarts (PWE K E)
      (CoreView.view K.toKLayout c ρ) := by
  intro s1 s2 a hp hmm hAl
  letI := (fl4LocW11JA st ar hA hm hSt a0 i K (CoreView.view K.toKLayout c ρ) hK hU).L
  have hqK : QPt K (fl4LocW11JA st ar hA hm hSt a0 i K (CoreView.view K.toKLayout c ρ) hK hU) s1 := hp.2
  exact w11_noG st ar hA hm hSt a0 i (E := E) hK hU nv s1 s2 a hp
    (qPs_ku_of hcv hqK fun hi hhi =>
      (hmm _ (hqK.al hi hhi) (fun hu => hqK.uoff _ (Or.inl hu) hi hhi rfl)).trans (hT hi hhi)) hAl

end w11

end
end Fl4Proofs.P2.E2EP
