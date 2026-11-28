/-
# P2 (line p3mc, gen 47): `InsV15N` [J] at the vx starts

`InsV15N cfg` [J] (P2/InsV15N) asks, at every CoreView start, `InsAP (PWE K E) ADEq NotPresent … ∅` at the physical
memory of the armed program. This module discharges it at the **vx** starts of the authoritative instance
`ExecCfg.nativePmKAD B` (V13's slots and PageMap with the walker's A/D writes).

## 1. A decline certificate for `InsA` (`PathObl.insA_tr_dec`)
The `InsA` counterpart of U20's `safe_tr_dec`: a program that, at every state carrying `ρ` on a read set `Rd`, runs
on every store answering `Rd` (so it writes nothing), with `Rd` inside the annotated read set `R0 ∧ Qv` and off `G`,
gives `InsA G Q NP … μ (narrowSP cls kt c Qv ∅ (tr R0 User cls kv …))` — by gen 46's `insA_narrow_tr_wrU_noG` with
empty write set (`Once` by `once_of_guardG`, `StepOK` from the `mguard` run).

## 2. The vx slot (`vx_fh_insA`, `vx_insA_annV`, `insAP_vx_view`)
* `vo_of_pwe`: a paging word of the epoch is region `.none`, so the view keeps its owner (`VO`); with `pwe_own`,
  `pwe_ko`, `pwe_user` these are the certificate's side conditions on `G := PWE K E`.
* **`vx_fh_insA`**: U19's armed vx program with `v = 0` is `InsA` at a view start: the read set is U19's (`vx_fh_rd`,
  split out of `vx_fh_annV` in place this generation, statement of `vx_fh_annV` unchanged), its words are off the
  PTE words and region-tagged, hence no paging word of the epoch (`PWE`); the run is U19's `vx_dec_run`.
* **`vx_insA_annV`**: at a vx start (`StartV2C`), the re-annotated body is `InsA` at the physical memory (glue: U19's
  `vx_start_data`, shared with `vx_annV`).
* **`insAP_vx_view`**: `InsV15N`'s obligation of `nativePmKAD B` at every vx index (`InsAP … ∅`, `insAP_of_insA`;
  the vx index is re-annotated: `NoV` holds there).

The narrowed premise and the new top are in P2/InsV15O. No named premise. Existing files touched: P2/E2EPU19 (`vx_fh_annV`'s read-set block split into `vx_rd_node`, `vx_rd_st`,
`vx_fh_rd`, `vx_annV`'s glue into `vx_start_data`; every existing statement byte-identical), root imports.
-/
import Fl4Proofs.P2.InsV15N
import Fl4Proofs.P2.E2EPU20
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once tr reads exists_mem_state OwnDep MasksWr masksOf masksOf_eq InsT insT_of_within)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm InsA narrowSP)

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **A program that declines writing nothing, on every store answering a read set `Rd` off `G`, is `InsA` in its
re-annotated form** (module docstring §1). -/
theorem insA_tr_dec {X : Type} {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt kv : U64 → ClsOwner U64} {User : U64 → Prop} {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop}
    (hQ : Equivalence Q) (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → kt x = .free)
    (hGU : ∀ b, G b → ¬ User b)
    {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64} {σ : S} {a : A} (p : SProg X) (hz : NoZero p)
    (hc : L.cpu σ = c) {R0 Qv Rd : U64 → Prop} (hGQ : ∀ b, G b → Qv b)
    (hal : ∀ b, Rd b → Aligned b) (hR0 : ∀ q, Rd q → (R0 q ∧ Qv q) ∧ ¬ User q) (hRdG : ∀ b, Rd b → ¬ G b)
    (hRPO : ∀ x, ¬ User x → (R0 x ∧ Qv x) → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∀ (gS : machine.Store S) (R : U64 → Prop), GRd gS st R → (∀ b, Rd b → R b) →
        ∃ r, interp gS ar p s a = ok r) :
    InsA G Q NP own cls kt c hs μ
      (narrowSP cls kt c Qv ∅ (tr R0 User cls kv c (L.ksb σ) (masksOf st σ) ar p ∅ a)) := by
  refine insA_narrow_tr_wrU_noG ar hQ hL hO hmk hGo hGko hGU p hc hGQ (Ru := fun _ => False)
    (Wd := fun _ => False) hal hR0 (fun _ h => h.elim) (fun _ h => h.elim) hRdG (fun _ h => h.elim)
    (fun _ h => h.elim) hRPO hρμ ?_
  intro s h1 h2 h3
  obtain ⟨r, hg⟩ := hgo s h1 h2 h3 (guard st (fun b => Rd b ∨ False) (fun _ => False)) (fun b => Rd b ∨ False)
    inferInstance (fun _ h => Or.inl h)
  obtain ⟨r', hM⟩ := hgo s h1 h2 h3 (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z)))
    (fun _ => True)
    { read := fun _ _ => rfl, read_pair := fun _ _ _ => rfl, ks_base := rfl, cur_cpu := rfl, frame_masks := rfl }
    (fun _ _ => trivial)
  have hWM := (interp_mguard _ s a r' hM).2
  have hO1 := once_of_guardG (R := fun b => Rd b ∨ False) (W := fun _ => False) (User := User)
    (fun q hq => (hR0 q (hq.resolve_right id)).2) _ hz ∅ ∅ s a r hg
  have hOnce := once_monoR (R := fun b => Rd b ∨ False) (R' := fun x => R0 x ∧ Qv x) (User := User)
    (fun b hb => (hR0 b (hb.resolve_right id)).1) _ ∅ ∅ ∅ s a hO1 (fun _ h => h)
  exact ⟨r, hg, hWM, hOnce⟩

end

end
end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW GateField TimerField GField tcbOwner)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP PO HeldV
  InsA InsAP insAP_of_insA)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD VDec nf_node)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

/-- **A paging word of the epoch keeps its owner under the view** (region `.none`; module docstring §2). -/
theorem vo_of_pwe {K : KLayoutP} (hK : RegionOKP K) {E : U64 → U64} {c : U64} {ρ : U64 → U64} {b : U64}
    (h : PWE K E b) : VO K c ρ b := by
  have hr := pwe_region hK h
  unfold VO ownP ownV
  by_cases hp : b ∈ K.ptes
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp]
    by_cases hv : ∃ v, InVcpu K.toKLayoutV v b
    · rw [dif_pos hv, dif_pos hv]
    · rw [dif_neg hv, dif_neg hv]
      simp only [OwnMap.own, hr]

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **U19's armed vx program with `v = 0` is `InsA` at a view start** (module docstring §2). -/
theorem vx_fh_insA (hmk : E2E.MasksWr st) {K : KLayoutP} (hK : RegionOKP K)
    (hU : UserOKP K) {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64} (E : U64 → U64)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {v n : U64} {σ : S} {a : A} (hv : v = 0#u64)
    (hJ : SlJAt (L := L) K.toKLayout σ) (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    InsA (PWE K E) ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (fun x => VexitRS K.toKLayoutV st lk σ x ∧ ¬ x ∈ K.ptes) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localvm.handle_vcpu_exit_local v n) ∅ a)) := by
  subst hv
  have W := vx_fh_rd (lk := lk) hK hJ hc hmm
  have hal : ∀ b, VxRd (L := L) σ b → Aligned b := fun b hb => (W b hb).1.1.1
  have hR0 : ∀ q, VxRd (L := L) σ q →
      ((VexitRS K.toKLayoutV st lk σ q ∧ ¬ q ∈ K.ptes) ∧ VO K c ρ q) ∧ q ∉ K.user := fun q hq =>
    ⟨⟨(W q hq).1, (W q hq).2.1.1.2⟩, (W q hq).2.2.1⟩
  have hRdρ : ∀ b, VxRd (L := L) σ b → ρ b = L.mem σ b := fun b hb =>
    (W b hb).2.1.1.1.symm.trans (hmm b (hal b hb) (W b hb).2.2.1).symm
  have hRdG : ∀ b, VxRd (L := L) σ b → ¬ PWE K E b := fun b hb hp => by
    rcases hp with hp | hp
    · exact (W b hb).1.2 hp
    · exact (W b hb).2.2.2 hp.2.2.1
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hRPO : ∀ x, x ∉ K.user → ((VexitRS K.toKLayoutV st lk σ x ∧ ¬ x ∈ K.ptes) ∧ VO K c ρ x) →
      PO c hs (ownP K μ x) := by
    intro x hu hx
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      rw [ownP_off hx.1.2, ← hc, ← hl]
      exact po_of_rperm (hx.1.1.2.resolve_left hu)
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      localvm.handle_vcpu_exit_local mm ar x a 0#u64 n =
        interp mm ar (R.localvm.handle_vcpu_exit_local 0#u64 n) x a :=
    fun mm x a => congrFun (congrFun (vexit_isProg S 0#u64 n A ar mm) x) a
  refine PathObl.insA_tr_dec (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar adEq_equiv (moveHeldP hK) (ownDepP hK hU) hmk (pwe_own hK)
    (fun x hx => pwe_ko hK μ hx) (fun b hb => pwe_user hU hb) (a := a)
    (R.localvm.handle_vcpu_exit_local 0#u64 n) (vexit_noZero 0#u64 n) hc (Rd := VxRd (L := L) σ)
    (fun b hb => vo_of_pwe hK hb) hal hR0 hRdG hRPO (fun x hx => hV.2.1 x hx) ?_
  intro s sc sk hag gS Rg iR hR
  have hag' : ∀ b, VxRd (L := L) σ b → L.mem s b = L.mem σ b := fun b hb => (hag b hb).trans (hRdρ b hb)
  have eN : ∀ o, L.nodeAt s (L.cpu s) o = L.nodeAt σ (L.cpu σ) o := fun o => by
    rw [sc]; exact nodeAt_of_ksb sk _ o
  have hcur : L.curW s = L.curW σ := by
    unfold LawfulStore.curW
    rw [eN]
    exact hag' _ (Or.inl rfl)
  have r1 : Rg (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) := hR _ (Or.inl (eN _))
  have r2 : Rg (L.nodeAt s (L.cpu s) layout.node.CUR_SC) := hR _ (Or.inr (Or.inl (eN _)))
  have r3 : Rg (core.num.U64.wrapping_add (L.curW s) 3328#u64) := hR _ (Or.inr (Or.inr (by rw [hcur])))
  have hg := vx_dec_run ar (gS := gS) (R := Rg) (a := a) (n := n) r1 r2 r3
  rw [hp] at hg
  exact ⟨_, hg⟩

end main

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **U9's re-annotated body is `InsA` at every vx start** (module docstring §2; the glue is U19's `vx_start_data`). -/
theorem vx_insA_annV {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)} (E : U64 → U64)
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : VxAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  obtain ⟨σ', a, lk, v, n, hv0, hJ, hc', hl', hmm, rfl⟩ := vx_start_data st ar hA a0 hsf hf
  unfold annV
  rw [hM.own, hM.cls, hM.ko] at hV ⊢
  have h := vx_fh_insA ar (masksWr_plain st) hK hU E hV (lk := lk) (n := n) (a := a) hv0 hJ hc' hl' hmm
  rw [tr_cut (VexitRS K.toKLayoutV st lk σ') (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout)
    (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ') (masksOf st σ') ar
    (R.localvm.handle_vcpu_exit_local v n) ∅ a] at h
  exact h

end all

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The vx indices of the PageMap index type. -/
def VxPm : IxV13Pm S → Prop
  | .inl (.inl (.vq (.inl _))) => True
  | _ => False

/-- **`InsV15N`'s obligation of `nativePmKAD B` at every vx start** (module docstring §2). -/
theorem insAP_vx_view (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (E : U64 → U64) {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (hx : VxPm (S := S) i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hM : MapsP K s)
    (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with (((j | j | j | j | j | j | j) | j) | j)
  all_goals try exact False.elim hx
  rcases j with j | j
  · have hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inl (.inl (.vq (.inl j)))) :=
      fun h => h
    rw [if_pos hn]
    have hsf0 : StartV13 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c
        (fun l => s.lk l = some c) k0 (.inl (.vq (.inl j))) := hsf
    have hsf' := startV2C_of_V13 st ar hA a0 hC hsf0
    exact insAP_of_insA (vx_insA_annV st ar hA a0 (i := .inl (.vq (.inl j))) E hsf' hM hV trivial)
  · exact False.elim hx

end pm

end
end Fl4Proofs.P2.E2EP
