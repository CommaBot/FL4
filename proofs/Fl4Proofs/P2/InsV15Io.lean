/-
# P2 (line p3mc, gen 50): `InsV15V` at every io start

The io starts are not re-annotated (`NoV` fails there: `IoIx`), so `InsV15V`'s obligation of `nativePmKAD B` at an io
start is `InsA (PWE K E) …` of the armed program `k0` itself at the physical memory. Its `Safe` counterpart is U8's
`io_viewSafe` (`CoreView.viewSafeAt_of_narrow` on `io_narrowV`, i.e. `E2E.LocalPath.safeV`). The `InsA` counterpart of
that certificate is gen 48's `E2E.LocalPath.insAVQ` (at the trivial restriction `Q0 := True`), which asks in addition
`hNG`: every run from a start state of the view, or an alternative of one, touches no `PWE` word but user words; for
the io path (`fl4LocW11JA … (.io j)`) that is gen 48's `w11A_noGS`. So:

* **`io_k0_insA`**: the io body is `InsA (PWE K E)` at every view start (`insAVQ` with `io_narrowV`'s two halves and
  `w11A_noGS`);
* `IoPm`, **`insAP_io_view`** (glue: `startAt_UNC` gives the io path's `StartAt` at the view, `atAF_view` the ASID
  table words, `epochPteN_view_of` the epoch facts).

## The open set and the top
* `Open52 s K c ρ k0 i := Open51 … ∧ ¬ IoPm i`.
* **`insV15NOV52_of_51`** (`Open52 ⊆ Open51`), **`insV15NOV51_of_52`** (at the io starts by `insAP_io_view`; needs `P`,
  `hIoa` for `startAt_UNC`): equivalent for `nativePmKAD B`.
* **`serializable_fl4_V15_pmKADO`** (authoritative): `serializable_fl4_V15_pmKADC` with `InsV15NOV … Open52` [J] for
  `InsV15NOV … Open51` [J], all other premises unchanged; **`serializable_fl4_V15_pmKADCofO`**: the previous statement
  from it.

Named premises: `InsV15NOV … Open52` [J] (replaces `InsV15NOV … Open51` [J]; justification as `InsV15` [J],
P2/E2EPV15AD). New module; no existing statement changed.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `insV15NOV52_of_51`,
`serializable_fl4_V15_pmKADO`, `serializable_fl4_V15_pmKADCofO`.
-/
import Fl4Proofs.P2.InsV15CM
import Fl4Proofs.P2.InsV15W11
import Fl4Proofs.P2.ViewSafeIoU8
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll VEq InsA InsAP insAP_of_insA)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

section body
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)

set_option maxHeartbeats 4000000 in
/-- **The io body is `InsA` at every view start without a VCPU** (module docstring). -/
theorem io_k0_insA (j : IoArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP) (E' : U64 → U64)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (hcv : K.ptes = ptesR K E')
    (hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E' (atAF K.ksb hi))
    (hS : StartAt (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0 (.io j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ k0 := by
  have hko := Fl4Proofs.P2.CoreView.ko_of_veq hK hV
  have hG := w11A_noGS st ar hA (masksWr_plain st) L.total a0 (.io j) hK hU nv hcv hT
  have hN := io_narrowV st ar hA (masksWr_plain st) L.total a0 j K hK hU c ρ
  obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := hS
  have := E2E.LocalPath.insAVQ
    (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0 (.io j) K (view K.toKLayout c ρ) hK hU)
    (NP := NotPresent) adEq_equiv (pwe_own hK) (fun x hx => pwe_ko hK μ hx)
    (moveHeldP hK) (ownDepP hK hU) (ρv := view K.toKLayout c ρ) (ρ := ρ) (μ := μ) (σ := σ) (a := a)
    hpre hμ (by rw [hc, hl]; exact hV)
    (N := VN K c ρ) (Kc := VKc K.toKLayout c ρ) (NW := VNW K c ρ) (DD := VDD K.toKLayout c ρ)
    (fun x h => h.1) (fun x h => h.2) (fun x h => by rw [hko]; exact h) (fun x h => ⟨h.1, h.2.1⟩)
    (fun m m' h y hy => Fl4Proofs.P2.CoreView.vown_off hK hU m m' h y hy)
    (fun q hq m v y hy => Fl4Proofs.P2.CoreView.vown_upd hK hq.2.2 m v y hy)
    (NR := fun s0 b => VN K c ρ b ∧
      ((fl4LocW11JA st ar hA (masksWr_plain st) L.total a0 (.io j) K (view K.toKLayout c ρ) hK hU).RS s0 b ∨
        VKc K.toKLayout c ρ b))
    (NWs := fun _ => VNW K c ρ) (fun _ _ h => h) (fun _ _ h => h)
    (fun _ => True) trivial (fun _ _ _ _ _ _ _ => trivial)
    (fun s0 r h1 _ h0 h2 h3 h4 => hN.1 s0 a r h1 (h0.trans hc) h2 h3 h4)
    (fun s0 r h1 _ h0 h2 h3 h4 => hN.2 s0 a r h1 (h0.trans hc) h2 h3 h4)
    (fun s0 s h1 _ _ h2 h3 => hG s0 s a h1 h2 h3)
  rw [hc, hl] at this; exact this

end body

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The io indices of the PageMap index type. -/
def IoPm : IxV13Pm S → Prop
  | .inl (.inl (.io _)) => True
  | _ => False

set_option maxHeartbeats 4000000 in
/-- **`insAP_io_view` on the re-based platform** (gen 54, in place: `hRun : ChainRun` for `P` / `hIoa`). -/
theorem insAP_io_view_C (hRun : ChainRun st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    {E : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : IoPm (S := S) i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with (((j | j | j | j | j | j | j) | j) | j)
  all_goals try exact False.elim hx
  have hn : ¬ (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inl (.inl (.io j))) := fun h => h trivial
  rw [if_neg hn]
  have hsf0 : StartV13 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 (.inl (.io j)) := hsf
  have hsf' := startV2C_of_V13 st ar hA a0 hC hsf0
  have hE := epochPteN_view_of J nv hM hV
  have hS := startAt_UNC_C st ar hA a0 hRun (s := { s with mem := CoreView.view K.toKLayout c ρ }) (i := .io j)
    hC hE hsf'
  have hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi) :=
    fun hi hhi => atAF_view L J nv hM hV (bun_of_chain st (arI := arI) (AR := AR) (MR := MR) hC) hhi
  rw [hM.own, hM.cls, hM.ko] at hV ⊢
  exact insAP_of_insA (io_k0_insA st ar hA a0 j K hK hU nv c _ ρ s.mem k0 E hV J.conv hT hS)

set_option maxHeartbeats 4000000 in
/-- **`InsV15V`'s obligation of `nativePmKAD B` at every io start** (module docstring). -/
theorem insAP_io_view (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    {E : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : IoPm (S := S) i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) :=
  insAP_io_view_C st ar hA a0 (chainRun_of P hIoa) B nv hx hC J hM hV hsf

/-- **The view starts at which the obligation is still asked after gen 50's io step** (module docstring). -/
def Open52 (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64) (ρ : U64 → U64) (k0 : SP) (i : IxV13Pm S) : Prop :=
  Open51 st s K c ρ k0 i ∧ ¬ IoPm (S := S) i

set_option maxHeartbeats 4000000 in
/-- **`insV15NOV51_of_52` on the re-based platform** (gen 54, in place: `hRun : ChainRun` for `P` / `hIoa`). -/
theorem insV15NOV51_of_52_C (hRun : ChainRun st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks)
    (h : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open52 st)) :
    InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open51 st) := by
  intro Ch s K E hK hU c k0 ρ i nv hO hC J hM hVq hi
  by_cases hl : IoPm (S := S) i
  · exact insAP_io_view_C st ar hA a0 hRun B nv hl hC J hM hVq hi
  exact h Ch s K E hK hU c k0 ρ i nv ⟨hO, hl⟩ hC J hM hVq hi

set_option maxHeartbeats 4000000 in
/-- **`InsV15NOV … Open52` gives `InsV15NOV … Open51`** for `nativePmKAD B` (module docstring). -/
theorem insV15NOV51_of_52 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks)
    (h : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open52 st)) :
    InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open51 st) :=
  insV15NOV51_of_52_C st ar hA a0 (chainRun_of P hIoa) B h

/-- **`serializable_fl4_V15_pmKADO` on the re-based platform**
(gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem serializable_fl4_V15_pmKADO_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks)
    (hI : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open52 st))
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitC P.toC K0.toKLayoutV (Ch0 e))
    (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15C (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) P.toC s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_V15_pmKADC_C st ar hA a0 P B (insV15NOV51_of_52_C st ar hA a0 P.run B hI) h0 hA0 hB hc0 hM0
    h hq

end pm

end
end Fl4Proofs.P2.E2EP
