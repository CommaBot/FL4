/-
# P2 (line p3mc, gen 48): `InsV15V` at the homed sl starts and the homed vmR starts

U15 / U16 prove the sl body `Safe` at a view start whose decided thread is homed (`SlHome`, `sl_k0_safeB`) and U14 the
vmR body at a view start whose reply names no thread homed off the core (`¬ RFH`, `vmR_k0_safe`), both by
`LocalPath.safeVQ`. Their run facts are split out in place this generation (`sl_k0_nar`, P2/E2EPU16; `vmR_k0_nar`,
P2/E2EPU14; statements of `sl_k0_safeB` / `vmR_k0_safe` unchanged); with the W11 paths' avoidance of the epoch's
paging words at the view (`w11B_noGS` / `w11A_noGS`, P2/InsV15W11) they give `InsA` by `LocalPath.insAVQ`.

These starts' start facts reach the body only through `EpochPteN` of the view, i.e. only at a layout without a VCPU,
and their action / bundle facts (`sl_v0_SFB`, `vmR_act0_SF`) use the platform `P`: so the obligations here are
`InsV15V`'s (P2/E2EPV15AD, `K.vcpus = ∅` assumed) and take `P`, `hIoa`.

* **`sl_k0_insAH`**, **`sl_insA_annV_h`**: the sl body / its re-annotation at a homed sl start.
* **`vmR_k0_insAH`**, **`vmR_insA_annV_h`**: the vmR body / its re-annotation at a vmR start with `¬ RFH`.
* `SlHPm`, `VmRHPm` (those indices of the PageMap index type), **`insAP_slH_view`**, **`insAP_vmRH_view`**.

No named premise. Existing files touched: P2/E2EPU16 (`sl_k0_nar`), P2/E2EPU14 (`vmR_k0_nar`); every existing
statement byte-identical.
-/
import Fl4Proofs.P2.InsV15StH
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
/-- **The sl body is `InsA` at every view start whose decided thread is homed** (module docstring). -/
theorem sl_k0_insAH (j : SlArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP) (E' : U64 → U64)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (h0 : SlV0 st K c ρ) (hH : SlHome st K c ρ j) (hcv : K.ptes = ptesR K E')
    (hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E' (atAF K.ksb hi))
    (hS : StartAt (fl4LocW11JB st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ k0 := by
  have hko := Fl4Proofs.P2.CoreView.ko_of_veq hK hV
  have hG := w11B_noGS st ar hA (masksWr_plain st) L.total a0 (.sl j) hK hU nv hcv hT
  by_cases hp : (slSlotB st ar hA (masksWr_plain st) L.total a0).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) (· ∈ K.user)) (W : AvoidV K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.cutLiftV hK.base hU.base
          (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv (view K.toKLayout c ρ)) P W).rJ K (fun b hb => Or.inl hb))),
        P = (slSlotB st ar hA (masksWr_plain st) L.total a0).path j K.toKLayoutV (view K.toKLayout c ρ)
          hK.base hU.base hp →
        (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv).NoGStarts (PWE K E')
          (view K.toKLayout c ρ) →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ k0 := by
      rintro P W hAv rfl hG' hS'
      obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := hS'
      have hc' : L.cpu σ = c := hc
      obtain ⟨hNA, hND⟩ := sl_k0_nar st ar hA a0 j K hK hU nv c ρ h0 hH hp W hAv σ a hc'
      have := E2E.LocalPath.insAVQ
        (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv)
        (NP := NotPresent) adEq_equiv (pwe_own hK) (fun x hx => pwe_ko hK μ hx)
        (moveHeldP hK) (ownDepP hK hU) (ρv := view K.toKLayout c ρ) (ρ := ρ) (μ := μ) (σ := σ) (a := a)
        hpre hμ (by rw [hc, hl]; exact hV)
        (N := VN K c ρ) (Kc := VKc K.toKLayout c ρ) (NW := VNW K c ρ) (DD := VDD K.toKLayout c ρ)
        (fun x h => h.1) (fun x h => h.2) (fun x h => by rw [hko]; exact h) (fun x h => ⟨h.1, h.2.1⟩)
        (fun m m' h y hy => Fl4Proofs.P2.CoreView.vown_off hK hU m m' h y hy)
        (fun q hq m v y hy => Fl4Proofs.P2.CoreView.vown_upd hK hq.2.2 m v y hy)
        (NR := fun s0 b => VN K c ρ b ∧
          (rsE (· ∈ K.ptes) (rsV K.toKLayoutV (SlRS (st := st) K.toKLayout j.Locks)) s0 b ∨ VKc K.toKLayout c ρ b))
        (NWs := fun _ => VNW K c ρ) (fun _ _ h => h) (fun _ _ h => h)
        (fun s0 => L.cpu s0 = L.cpu σ ∧ L.ksb s0 = L.ksb σ ∧ st.frame_masks s0 = st.frame_masks σ ∧
          ∀ x, Aligned x → x ∉ K.user → L.mem s0 x = L.mem σ x)
        ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
        (fun s b v _ hQ hu hb => by
          refine ⟨(L.cpu_wr s b v).trans hQ.1, (L.ksb_wr s b v).trans hQ.2.1,
            (masksWr_plain st s b v).trans hQ.2.2.1, fun x hx hu' => ?_⟩
          exact (mem_wr_ne' (L := L) hb hx (fun e => hu' (e ▸ hu))).trans (hQ.2.2.2 x hx hu'))
        hNA hND (fun s0 s h1 _ _ h2 h3 => hG' s0 s a h1 h2 h3)
      rw [hc, hl] at this; exact this
    exact key _ _ (allB st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
      (SlotC.fam_pos _ _ hp) hG hS
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) (· ∈ K.user)) (W : AvoidV K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.cutLiftV hK.base hU.base
          (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv (view K.toKLayout c ρ)) P W).rJ K (fun b hb => Or.inl hb))),
        P = LocalPath.void (fl4Dflt st ar (masksWr_plain st)) (OwnMap.ko_aligned hK.base.base hU.base.base
          (view K.toKLayout c ρ)) →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ k0 := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, -⟩ := hS'
      exact absurd hpre.1 id
    exact key _ _ (allB st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
      (dif_neg hp) hS

set_option maxHeartbeats 4000000 in
/-- **The vmR body is `InsA` at every view start with action 0 whose reply names no thread homed elsewhere** (module
docstring). -/
theorem vmR_k0_insAH (j : VmRArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP) (E' : U64 → U64)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (hLk : LkC j.Locks) (h0 : Act0V st K c ρ) (hTR : TabRV st K c ρ) (hF : ¬ RFH (S := S) K c ρ j)
    (nv : K.vcpus = ∅) (hcv : K.ptes = ptesR K E')
    (hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E' (atAF K.ksb hi))
    (hS : StartAt (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0 (.vmR j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ k0 := by
  have hBv : view K.toKLayout c ρ (rTcbA j.rptr) ≠ 0#u64 →
      ρ (affA (view K.toKLayout c ρ (rTcbA j.rptr))) = c := fun h1 => by
    by_contra h2; exact hF ⟨h1, h2⟩
  have hko := Fl4Proofs.P2.CoreView.ko_of_veq hK hV
  have hG := w11A_noGS st ar hA (masksWr_plain st) L.total a0 (.vmR j) hK hU nv hcv hT
  by_cases hp : (vmRSlotA st ar hA (masksWr_plain st)).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = (vmRSlotA st ar hA (masksWr_plain st)).path j K.toKLayoutV (view K.toKLayout c ρ) hK.base hU.base hp →
        (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv).NoGStarts (PWE K E')
          (view K.toKLayout c ρ) →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ k0 := by
      rintro P W hAv rfl hG' hS'
      obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := hS'
      obtain ⟨hNA, hND⟩ := vmR_k0_nar st ar hA j K hK hU c ρ hLk h0 hTR hBv hp W hAv σ a hpre hc hμ
      have := E2E.LocalPath.insAVQ
        (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv)
        (NP := NotPresent) adEq_equiv (pwe_own hK) (fun x hx => pwe_ko hK μ hx)
        (moveHeldP hK) (ownDepP hK hU) (ρv := view K.toKLayout c ρ) (ρ := ρ) (μ := μ) (σ := σ) (a := a)
        hpre hμ (by rw [hc, hl]; exact hV)
        (N := VN K c ρ) (Kc := VKc K.toKLayout c ρ) (NW := VNW K c ρ) (DD := VDD K.toKLayout c ρ)
        (fun x h => h.1) (fun x h => h.2) (fun x h => by rw [hko]; exact h) (fun x h => ⟨h.1, h.2.1⟩)
        (fun m m' h y hy => Fl4Proofs.P2.CoreView.vown_off hK hU m m' h y hy)
        (fun q hq m v y hy => Fl4Proofs.P2.CoreView.vown_upd hK hq.2.2 m v y hy)
        (NR := fun s0 b => VN K c ρ b ∧
          (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) j.Locks) s0 b ∨ VKc K.toKLayout c ρ b))
        (NWs := fun _ => VNW K c ρ) (fun _ _ h => h) (fun _ _ h => h)
        (fun s0 => L.cpu s0 = L.cpu σ ∧ L.ksb s0 = L.ksb σ ∧ st.frame_masks s0 = st.frame_masks σ ∧
          ∀ x, Aligned x → x ∉ K.user → L.mem s0 x = L.mem σ x)
        ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
        (fun s b v _ hQ hu hb => by
          refine ⟨(L.cpu_wr s b v).trans hQ.1, (L.ksb_wr s b v).trans hQ.2.1,
            (masksWr_plain st s b v).trans hQ.2.2.1, fun x hx hu' => ?_⟩
          exact (mem_wr_ne' (L := L) hb hx (fun e => hu' (e ▸ hu))).trans (hQ.2.2.2 x hx hu'))
        hNA hND (fun s0 s h1 _ _ h2 h3 => hG' s0 s a h1 h2 h3)
      rw [hc, hl] at this; exact this
    exact key _ _ (allA st ar hA (masksWr_plain st) L.total a0 (.vmR j) K (view K.toKLayout c ρ) hK hU)
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
    exact key _ _ (allA st ar hA (masksWr_plain st) L.total a0 (.vmR j) K (view K.toKLayout c ρ) hK hU)
      (dif_neg hp) hS

end body

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`sl_insA_annV_h` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem sl_insA_annV_h_C (P : LocPlatCR st arI AR MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {j : SlArg S} (E : U64 → U64) (nv : K.vcpus = ∅)
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (J : EpochJV K E s)
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
      (.inl (.sl j)))
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) (hH : SlHome st K c ρ j) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  have h' : StartU2B st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
      (.sl j) := hsf
  have hE := epochPteN_view_of J nv hM hV
  have hS := startAt_slB_C st ar hA a0 P.run (s := { s with mem := CoreView.view K.toKLayout c ρ }) hC hE h'
  have h0 := sl_v0_SFB_C st ar hA a0 P (hK := hK) (hU := hU) hC nv hsf
  have hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi) :=
    fun hi hhi => atAF_view L J nv hM hV (bun_of_chain st (arI := arI) (AR := AR) (MR := MR) hC) hhi
  unfold annV
  rw [hM.own, hM.cls, hM.ko] at hV ⊢
  exact insA_narrow _ (sl_k0_insAH st ar hA a0 j K hK hU nv c _ ρ s.mem k E hV h0 hH J.conv hT hS) ∅

set_option maxHeartbeats 4000000 in
/-- **`vmR_insA_annV_h` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem vmR_insA_annV_h_C (P : LocPlatCR st arI AR MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {j : VmRArg S} (E : U64 → U64) (nv : K.vcpus = ∅)
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (J : EpochJV K E s)
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
      (.inl (.vmR j)))
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hF : ¬ RFH (S := S) K c ρ j) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  have h' : StartU2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
      (.vmR j) := hsf
  have hE := epochPteN_view_of J nv hM hV
  have hS := startAt_UN_C st ar hA (masksWr_plain st) L.total a0 P.run
    (s := { s with mem := CoreView.view K.toKLayout c ρ }) hC hE (startU_of_U2 st ar hA a0 hC nv h')
  have h0 := vmR_act0_SF_C st ar hA a0 P (hK := hK) (hU := hU) hC nv hsf
  have hTR := vmR_bun_SF st ar hA a0 (hK := hK) (hU := hU) hC nv hsf
  have hLk : LkC j.Locks := by
    obtain ⟨q0, ⟨hL, -⟩, -⟩ := h'
    exact hL
  have hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi) :=
    fun hi hhi => atAF_view L J nv hM hV (bun_of_chain st (arI := arI) (AR := AR) (MR := MR) hC) hhi
  unfold annV
  rw [hM.own, hM.cls, hM.ko] at hV ⊢
  exact insA_narrow _
    (vmR_k0_insAH st ar hA a0 j K hK hU c _ ρ s.mem k E hV hLk h0 hTR hF nv J.conv hT hS) ∅

end all

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The sl indices of the PageMap index type whose decided thread is homed (U15's `SlHome`). -/
def SlHPm (K : KLayoutP) (c : U64) (ρ : U64 → U64) : IxV13Pm S → Prop
  | .inl (.inl (.sl j)) => SlHome st K c ρ j
  | _ => False

/-- The vmR indices of the PageMap index type whose reply names no thread homed elsewhere (`¬ RFH`, U13). -/
def VmRHPm (K : KLayoutP) (c : U64) (ρ : U64 → U64) : IxV13Pm S → Prop
  | .inl (.inl (.vmR j)) => ¬ RFH (S := S) K c ρ j
  | _ => False

set_option maxHeartbeats 4000000 in
/-- **`insAP_slH_view` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem insAP_slH_view_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (E : U64 → U64) {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : SlHPm st K c ρ i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with (((j | j | j | j | j | j | j) | j) | j)
  all_goals try exact False.elim hx
  have hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inl (.inl (.sl j))) := fun h => h
  rw [if_pos hn]
  have hsf0 : StartV13 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 (.inl (.sl j)) := hsf
  have hsf' := startV2C_of_V13 st ar hA a0 hC hsf0
  exact insAP_of_insA (sl_insA_annV_h_C st ar hA a0 P E nv hC J hsf' hM hV hx)

set_option maxHeartbeats 4000000 in
/-- **`insAP_vmRH_view` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem insAP_vmRH_view_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (E : U64 → U64) {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : VmRHPm (S := S) K c ρ i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with (((j | j | j | j | j | j | j) | j) | j)
  all_goals try exact False.elim hx
  have hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inl (.inl (.vmR j))) := fun h => h
  rw [if_pos hn]
  have hsf0 : StartV13 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 (.inl (.vmR j)) := hsf
  have hsf' := startV2C_of_V13 st ar hA a0 hC hsf0
  exact insAP_of_insA (vmR_insA_annV_h_C st ar hA a0 P E nv hC J hsf' hM hV hx)

end pm

end
end Fl4Proofs.P2.E2EP
