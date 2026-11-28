/-
# P2 (line p3mc, gen 47): `InsV15N` [J] at the vt starts

At a vt view start the armed program (`localvm.handle_vm_timer_irq_local`) declines writing nothing on every store
answering its read set `VtRd` (U20: no thread is bound to a VCPU at a P3 bundle state). So it is `InsA` at the
physical memory by the decline certificate `PathObl.insA_tr_dec` (P2/InsV15Vx).

* **`vt_fh_insA`**: U20's read-set facts (`vt_fh_W`) and run (`vt_fh_go`), both split out of `vt_fh_annV` in place
  this generation (statement unchanged); the read words are off the PTE words and region-tagged or kernel-static
  (`vt_fh_reg`, new: the IRQ state word is `K.ksb + i` with `i < 13568`), hence no paging word of the epoch.
* **`vt_insA_annV`** (glue: U20's `vt_start_data`, split out of `vt_annV` in place, shared; `EpochPteN` of the view
  from `EpochJV` under the start's no-VCPU fact, `epochPteN_view_of`), **`insAP_vt_view`**: `InsV15N`'s obligation of
  `nativePmKAD B` at every vt index (`VtPm`).

No named premise. Existing file touched: P2/E2EPU20 (`vt_fh_W`, `vt_fh_go`, `vt_start_data` split out, `vt_fh_reg`
added; every existing statement byte-identical).
-/
import Fl4Proofs.P2.InsV15St
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg VEq Safe narrowSP PO HeldV InsA InsAP insAP_of_insA)
open Fl4Proofs.P2.CoreView (view)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **U9's armed vt program is `InsA` at a view start** (module docstring). -/
theorem vt_fh_insA (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {K : KLayoutP} (hK : RegionOKP K)
    (hU : UserOKP K) {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64} (E' : U64 → U64)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {irq n : U64} {pl : localtimer.TimerIrqPlan} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hq : QPs K st σ)
    (hiq : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i →
      Aligned (core.num.U64.wrapping_add (L.ksb σ) i) ∧
        region K.toKLayout (core.num.U64.wrapping_add (L.ksb σ) i) = .none ∧
        ¬ ∃ w, InVcpu K.toKLayoutV w (core.num.U64.wrapping_add (L.ksb σ) i))
    (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (fun x => VexitRS K.toKLayoutV st lk σ x ∧ ¬ x ∈ K.ptes) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localvm.handle_vm_timer_irq_local irq pl n) ∅ a)) := by
  have W := vt_fh_W (lk := lk) hK hJ hq hiq hc hmm
  have Rg := vt_fh_reg (c := c) (ρ := ρ) (irq := irq) hJ
  have hal : ∀ b, VtRd (L := L) K c ρ irq σ b → Aligned b := fun b hb => (W b hb).1.1.1.1
  have hRdG : ∀ b, VtRd (L := L) K c ρ irq σ b → ¬ PWE K E' b := fun b hb hp => by
    rcases hp with hp | hp
    · exact (W b hb).1.1.2 hp
    · rcases Rg b hb with hr | ⟨o, ho, e⟩
      · exact hr hp.2.2.1
      · exact hp.2.2.2.2 o ho e
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
  exact PathObl.insA_tr_dec (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar adEq_equiv (moveHeldP hK) (ownDepP hK hU) hmk (pwe_own hK)
    (fun x hx => pwe_ko hK μ hx) (fun b hb => pwe_user hU hb) (a := a)
    (R.localvm.handle_vm_timer_irq_local irq pl n) (vtimer_noZero irq pl n) hc (Rd := VtRd (L := L) K c ρ irq σ)
    (fun b hb => vo_of_pwe hK hb) hal W hRdG hRPO (fun x hx => hV.2.1 x hx)
    (vt_fh_go ar hA (lk := lk) hK hJ hq hiq hc hmm (n := n) (pl := pl) (a := a))

end main

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **U9's re-annotated body is `InsA` at every vt start** (module docstring; glue: U20's `vt_start_data`). -/
theorem vt_insA_annV {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)} (E : U64 → U64)
    (J : EpochJV K E s)
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : VtAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  obtain ⟨σ', a, lk, irq, n, pl, hJ, hq, hiq, hc', hl', hmm, rfl⟩ :=
    vt_start_data st ar hA a0 (fun nv => epochPteN_view_of J nv hM hV) hsf hf
  unfold annV
  rw [hM.own, hM.cls, hM.ko] at hV ⊢
  have h := vt_fh_insA ar hA (masksWr_plain st) hK hU E hV (lk := lk) (n := n) (pl := pl) (a := a) hJ hq hiq hc'
    hl' hmm
  rw [tr_cut (VexitRS K.toKLayoutV st lk σ') (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout)
    (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ') (masksOf st σ') ar
    (R.localvm.handle_vm_timer_irq_local irq pl n) ∅ a] at h
  exact h

end all

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The vt indices of the PageMap index type. -/
def VtPm : IxV13Pm S → Prop
  | .inl (.inl (.vq (.inr _))) => True
  | _ => False

set_option maxHeartbeats 4000000 in
/-- **`InsV15N`'s obligation of `nativePmKAD B` at every vt start** (module docstring). -/
theorem insAP_vt_view (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (E : U64 → U64) {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (hx : VtPm (S := S) i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (J : EpochJV K E s)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with (((j | j | j | j | j | j | j) | j) | j)
  all_goals try exact False.elim hx
  rcases j with j | j
  · exact False.elim hx
  · have hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inl (.inl (.vq (.inr j)))) := fun h => h
    rw [if_pos hn]
    have hsf0 : StartV13 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c
        (fun l => s.lk l = some c) k0 (.inl (.vq (.inr j))) := hsf
    have hsf' := startV2C_of_V13 st ar hA a0 hC hsf0
    exact insAP_of_insA (vt_insA_annV st ar hA a0 (i := .inl (.vq (.inr j))) E J hsf' hM hV trivial)

end pm

end
end Fl4Proofs.P2.E2EP
