/-
# P2 (line p3mc, gen 48): `InsV15N` [J] at the st starts whose target is homed on the core

U18 proves the st body `Safe` at a view start whose target is, in `ρ`, homed on `c` (`st_k0_safeC`) by
`LocalPath.safeVQW` with st's narrowed / checked run facts (`st_k0_nar`, split out of `st_k0_safeC` in place this
generation, statement of `st_k0_safeC` unchanged). The same facts and the W11 path's avoidance of the epoch's paging
words at the view (`w11C_noGS`, P2/InsV15W11) give `InsA` by `LocalPath.insAVQW` (P2/InsVQ).

* **`st_k0_insAH`**: the st body is `InsA (PWE K E') ADEq NotPresent` at the physical memory at every view start
  whose target is homed (given the view's ASID table words equal `E'`, `K.ptes = ptesR K E'`, no VCPU).
* **`st_insA_annV_h`**: U9's re-annotated body is `InsA` at every `StHAt` start (`insA_narrow`; the no-VCPU fact from
  `stC_glue`, `epochPteN_view_of`, `atAF_view` from the chain's bundle).
* `StHPm c ρ i` (the st indices of the PageMap index type whose target is homed), **`insAP_stH_view`**: `InsV15N`'s
  obligation of `nativePmKAD B` at those starts.

No named premise. Existing files touched: P2/E2EPU18 (`st_k0_nar` split out of `st_k0_safeC`), P2/SafeVQ and
P2/SafeVQW (the propositions `LocalPath.VQNar` / `VQNarW` added); every existing statement byte-identical.
-/
import Fl4Proofs.P2.InsV15W11
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg VEq Safe narrowSP PO HeldV InsA InsAP insAP_of_insA insA_narrow)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

section body
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)

set_option maxHeartbeats 4000000 in
/-- **The st body is `InsA` at every view start whose target is homed** (module docstring). -/
theorem st_k0_insAH (j : StArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP) (E' : U64 → U64)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (hH : ρ (fld j.target oAFFINITY) = c) (nv : K.vcpus = ∅) (hcv : K.ptes = ptesR K E')
    (hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E' (atAF K.ksb hi))
    (hS : StartAt (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0 (.st j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ k0 := by
  have hko := Fl4Proofs.P2.CoreView.ko_of_veq hK hV
  have hG := w11C_noGS st ar hA (masksWr_plain st) L.total a0 (.st j) hK hU nv hcv hT
  by_cases hp : (stSlotC st ar hA (masksWr_plain st)).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = (stSlotC st ar hA (masksWr_plain st)).path j K.toKLayoutV (view K.toKLayout c ρ) hK.base hU.base hp →
        (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv).NoGStarts (PWE K E')
          (view K.toKLayout c ρ) →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ k0 := by
      rintro P W hAv rfl hG' hS'
      obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := hS'
      have hc' : L.cpu σ = c := hc
      obtain ⟨⟨hNA, hND⟩, hVA, hVD⟩ := st_k0_nar st ar hA j K hK hU c ρ hH hp W hAv σ a hc'
      have := E2E.LocalPath.insAVQW
        (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv)
        (NP := NotPresent) adEq_equiv (pwe_own hK) (fun x hx => pwe_ko hK μ hx)
        (moveHeldP hK) (ownDepP hK hU) (ρv := view K.toKLayout c ρ) (ρ := ρ) (μ := μ) (σ := σ) (a := a)
        hpre hμ (by rw [hc, hl]; exact hV)
        (N := VN K c ρ) (Kc := VKc K.toKLayout c ρ) (NW := StNW K c ρ) (DD := VDD K.toKLayout c ρ)
        (fun x h => h.1) (fun x h => h.2) (fun x h => by rw [hko]; exact h) (fun x h => ⟨h.1, h.2.1⟩)
        (fun m m' h y hy => Fl4Proofs.P2.CoreView.vown_off hK hU m m' h y hy)
        (VW := @StVW S st L K.toKLayout c ρ)
        (fun q hq s v m hW hm y hy => stVW_own (L := L) hK hU hq.2.2 s v m hW hm y hy)
        (NR := @StNR S st L K c ρ j.lk) (NWs := fun _ => StNW K c ρ) (fun _ _ h => h) (fun _ _ h => h)
        (fun s0 => L.cpu s0 = L.cpu σ ∧ L.ksb s0 = L.ksb σ ∧ st.frame_masks s0 = st.frame_masks σ ∧
          ∀ x, Aligned x → x ∉ K.user → L.mem s0 x = L.mem σ x)
        ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
        (fun s b v _ hQ hu hb => by
          refine ⟨(L.cpu_wr s b v).trans hQ.1, (L.ksb_wr s b v).trans hQ.2.1,
            (masksWr_plain st s b v).trans hQ.2.2.1, fun x hx hu' => ?_⟩
          exact (mem_wr_ne' (L := L) hb hx (fun e => hu' (e ▸ hu))).trans (hQ.2.2.2 x hx hu'))
        hNA hND hVA hVD (fun s0 s h1 _ _ h2 h3 => hG' s0 s a h1 h2 h3)
      rw [hc, hl] at this; exact this
    exact key _ _ (allC st ar hA (masksWr_plain st) L.total a0 (.st j) K (view K.toKLayout c ρ) hK hU)
      (SlotU.fam_pos _ _ hp) hG hS
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = LocalPath.void (fl4Dflt st ar (masksWr_plain st))
          (OwnMap.ko_aligned (regionOK_userV hK.base) (userOK_userV hK.base hU.base) (view K.toKLayout c ρ)) →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ k0 := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, -⟩ := hS'
      exact absurd hpre.1 id
    exact key _ _ (allC st ar hA (masksWr_plain st) L.total a0 (.st j) K (view K.toKLayout c ρ) hK hU)
      (dif_neg hp) hS

end body

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- The chain's bundle state. -/
theorem bun_of_chain {Ch : S → Prop} {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) :
    ∃ σe, SlJAt (L := L) K.toKLayout σe := by
  obtain ⟨σe, hC'⟩ := hC
  have hσe : Ch σe := by
    obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
    exact h'
  exact ⟨σe, ChainOf.bun hC' σe hσe⟩

set_option maxHeartbeats 4000000 in
/-- **U9's re-annotated body is `InsA` at every st start whose target is homed** (module docstring). -/
theorem st_insA_annV_h {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)} (E : U64 → U64)
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (J : EpochJV K E s)
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : StHAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · have h' : StartU2C st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
        (.st j) := hsf
    obtain ⟨_, ⟨hR, -⟩, -⟩ := stC_glue st ar hA a0 h'
    have hpr : K.toKLayoutV.vcpus = ∅ ∧ StPremK2B st j K.toKLayoutV (view K.toKLayout c ρ) := hR
    have hE := epochPteN_view_of J hpr.1 hM hV
    have hS := startAt_stC st ar hA a0 (s := { s with mem := CoreView.view K.toKLayout c ρ }) hC hE h'
    have hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi) :=
      fun hi hhi => atAF_view L J hpr.1 hM hV (bun_of_chain st (arI := arI) (AR := AR) (MR := MR) hC) hhi
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    exact insA_narrow _ (st_k0_insAH st ar hA a0 j K hK hU c _ ρ s.mem k E hV hf hpr.1 J.conv hT hS) ∅
  all_goals exact False.elim hf

end all

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The st indices of the PageMap index type whose target is, in `ρ`, homed on `c` (U18's `StHAt`). -/
def StHPm (c : U64) (ρ : U64 → U64) : IxV13Pm S → Prop
  | .inl (.inl (.st j)) => ρ (fld j.target oAFFINITY) = c
  | _ => False

set_option maxHeartbeats 4000000 in
/-- **`InsV15N`'s obligation of `nativePmKAD B` at every st start whose target is homed** (module docstring). -/
theorem insAP_stH_view (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (E : U64 → U64) {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (hx : StHPm (S := S) c ρ i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (J : EpochJV K E s)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with (((j | j | j | j | j | j | j) | j) | j)
  all_goals try exact False.elim hx
  have hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inl (.inl (.st j))) := fun h => h
  rw [if_pos hn]
  have hsf0 : StartV13 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 (.inl (.st j)) := hsf
  have hsf' := startV2C_of_V13 st ar hA a0 hC hsf0
  exact insAP_of_insA (st_insA_annV_h st ar hA a0 (i := .inl (.st j)) E hC J hsf' hM hV hx)

end pm

end
end Fl4Proofs.P2.E2EP
