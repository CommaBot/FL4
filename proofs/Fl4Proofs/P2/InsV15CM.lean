/-
# P2 (line p3mc, gen 50): `InsV15V` at every Copy / Mint start

The Copy / Mint certificate `inv_cm_annA` (P2/InvCMAnnA, U27) is `PathObl.safe_tr_wrU` on a read set `IoRS ∧ SR` and
the aligned user words; `IoRS` may hold upper paging words (gate words of region `.none`), so the `InsA` twin cuts
the read set by the region-tagged or kernel-static words (`RTK`, gen 49), as handoff §54f planned. Gen 50 split the
two 16M monoliths of P2/InvCMAnnA in place (statements unchanged) into pieces generic in a word class `H`
(`inv_cm_gdH`, `cm_hgoH`); here `H := RTK`:

* **`gcl_rtk`**: every word class of the Copy / Mint run (`GCl`: node words, the current thread's words and
  registers, the slots' base / second words, the current SC's words, `CUR_DOMAIN` / `DOMAIN_TIME`, the earliest timer's
  deadline, the release head's `SC` word and refill head) is region-tagged or kernel-static, from the bundle alone.
* **`inv_cm_insA`**: U27's armed Copy / Mint program is `InsA (PWE K E)` at a view start, by gen 46's
  `insA_narrow_tr_wrU_noG` on `cm_hgoH` at `H := RTK`: read words are `RTK` and off `K.ptes` (`rt_notPWE'`), written
  words are held (region-tagged, `wperm_region`) and off `K.ptes`, or user words.
* **`cm_insA_annV`** (glue as `inv_annV_cmA`), `CmPm`, **`insAP_cm_view`** (`InsV15V`'s obligation of
  `nativePmKAD B` at every Copy / Mint start without a VCPU).

## The open set and the top
* `Open51 s K c ρ k0 i := Open50 … ∧ ¬ CmPm i`.
* **`insV15NOV51_of_50`** (`Open51 ⊆ Open50`), **`insV15NOV50_of_51`** (at the Copy / Mint starts by
  `insAP_cm_view`): equivalent for `nativePmKAD B`.
* **`serializable_fl4_V15_pmKADC`** (authoritative): `serializable_fl4_V15_pmKADI` with `InsV15NOV … Open51` [J] for
  `InsV15NOV … Open50` [J], all other premises unchanged; **`serializable_fl4_V15_pmKADIofC`**: the previous statement
  from it.

Named premises: `InsV15NOV … Open51` [J] (replaces `InsV15NOV … Open50` [J]; justification as `InsV15` [J],
P2/E2EPV15AD). New module; existing file touched: P2/InvCMAnnA (in-place split, every existing statement
byte-identical).

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `insV15NOV51_of_50`,
`serializable_fl4_V15_pmKADC`, `serializable_fl4_V15_pmKADIofC`.
-/
import Fl4Proofs.P2.InsV15Irq
import Fl4Proofs.P2.E2EPU27
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll VEq Safe InsA InsAP insAP_of_insA narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The word classes of the Copy / Mint run are region-tagged or kernel-static** (module docstring). -/
theorem gcl_rtk {K : KLayoutP} {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan}
    {m : U64 → U64} {s : S}
    (hJ : SlJAt (L := L) K.toKLayout s) (hq : InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) :
    GCl st K.toKLayout K.toKLayout.heap.scBits (RTK K.toKLayout) s := by
  have hX := hJ.regionOKX
  obtain ⟨hk, -⟩ := hJ.kc
  obtain ⟨Ac', B⟩ := bunIx_of hJ
  have hI := B.bxi
  have hP := stPre_ofS B.ac
  have h0 := hI.1.choose_spec.choose_spec
  have hN : NodePlaced st (Heap.tcbs K.toKLayout.heap) s (L.cpu s) := h0.nodes _ h0.cur
  have hcT : L.curW s ∈ K.toKLayout.heap.tcbs := h0.curT
  have htH : K.toKLayout.heap (L.curW s) = some .tcb := hcT
  have PE := hq.1.1.1
  have hL8 : Slot8 K.toKLayout := fun q hq => PE.lay.slot8 q hq
  have hcsc0 : L.cscW s ≠ 0#u64 := by
    intro e
    obtain ⟨z, hz'⟩ := hP.csc
    rw [e] at hz'
    have hz2 : K.toKLayout.heap 0#u64 = some (.sc z) := hz'
    rw [slJAt_heap0 hJ] at hz2
    cases hz2
  have hne : L.mem s (scA (L.curW s)) ≠ 0#u64 := by rw [hP.sct]; exact hcsc0
  obtain ⟨hcs1, -, -⟩ := hI.2.2.1.2.2.bound _ h0.curT hne
  have hcs : L.cscW s ∈ Heap.scs K.toKLayout.heap := by rw [← hP.sct]; exact hcs1
  have rW : ∀ b, SlotW K.toKLayout b → RTK K.toKLayout b := fun b ⟨q, hq', hin⟩ =>
    rtk_of (PE.lay.slotw q hq' b hin) (by simp)
  have sW0 : ∀ q, q ∈ K.slots → SlotW K.toKLayout q := fun q hq' => by
    have := slotW_of hL8 hq' (o := 0#u64) (by simp); rwa [wadd_zero (hL8 q hq').2] at this
  have rKs : ∀ o : U64, o.val < 13568 → RTK K.toKLayout (core.num.U64.wrapping_add (L.ksb s) o) := fun o ho =>
    Or.inr ⟨o, ho, by rw [hk]⟩
  exact
    { n := fun o ho => PathObl.SlJAt.rtNode hJ hN ho
      t := fun k h1 h2 h3 => rtk_tcb hX htH (by omega) h2 h3
      r := fun r hr => rtk_reg hX htH hr
      sl := fun q hq' => ⟨rW _ (sW0 q hq'), rW _ (slotW_of hL8 hq' (o := 8#u64) (by simp))⟩
      sc := fun b _ hb => rtk_sc hX (st_scH (K := K) hcs) hb
      ks := by
        rintro o (rfl | rfl)
        · exact rKs _ (by simp [layout.ks.CUR_DOMAIN])
        · exact rKs _ (by simp [layout.ks.DOMAIN_TIME])
      td := fun hne' => by
        obtain ⟨tmT, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne'
        exact rtk_tcb hX (show K.toKLayout.heap _ = some .tcb from tmT) (o := 3528#u64) (by simp) (by simp)
          (by simp)
      rs := fun hne' => by
        obtain ⟨r1, -, -, r4, -⟩ := rel_facts hI hne'
        obtain ⟨-, hsc', ha'⟩ := bxi_rh PE.bxi hne'
        obtain ⟨hWf, -⟩ := bxi_scin PE.bxi hsc' ha'
        exact ⟨rtk_tcb hX (show K.toKLayout.heap _ = some .tcb from r1) (o := 3464#u64) (by simp) (by simp)
          (by simp), (scAccRT hX (st_scH (K := K) r4)).head hWf⟩ }

set_option maxHeartbeats 4000000 in
/-- **U27's armed Copy / Mint program is `InsA` at a view start** (module docstring). -/
theorem inv_cm_insA (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    (E : U64 → U64) {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {number : I64} {σ : S} {a : A}
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ (K' : OwnMap.KLayout) (s : S) (b v : U64), SlJAt (L := L) K' s → b ∈ K'.user → Aligned b →
      Locks (L.wr s b v) = Locks s)
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (hq : InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout (view K.toKLayout c ρ) σ) (hqu : QU st K σ)
    (hc : L.cpu σ = c) (hl : Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    InsA (PWE K E) ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (fun x => InvCMRS (st := st) K.toKLayout Locks σ x ∧ ¬ x ∈ K.ptes) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.invBodyG number p) ∅ a)) := by
  obtain ⟨hWd, hRPO⟩ := cm_own (st := st) (Locks := Locks) hK hU nv hV hc hl hmm
  have PE := hq.1.1.1
  have rW : ∀ b, SlotW K.toKLayout b → RTK K.toKLayout b := fun b ⟨q, hq', hin⟩ =>
    rtk_of (PE.lay.slotw q hq' b hin) (by simp)
  have hgo := cm_hgoH ar hA hK hU nv hV (number := number) (a := a) hCs hlk hJ hq hqu hc hmm
    (H := RTK K.toKLayout) (fun _ h1 h2 => gcl_rtk h1 h2) rW
  let Rd : U64 → Prop := fun b => (IoRS (st := st) K.toKLayout Locks σ b ∧ RTK K.toKLayout b) ∧ SR K c ρ b
  have hR0 : ∀ q, Rd q →
      ((InvCMRS (st := st) K.toKLayout Locks σ q ∧ ¬ q ∈ K.ptes) ∧ VO K c ρ q) ∧ ¬ q ∈ K.user := fun q hq' =>
    ⟨⟨⟨ioRS_cm hq'.1.1, hq'.2.2⟩, hq'.2.1.2⟩, hq'.1.1.2.1⟩
  have hal : ∀ b, Rd b → Aligned b := fun b hb => hb.1.1.1
  have hRdG : ∀ b, Rd b → ¬ PWE K E b := fun b hb => rt_notPWE' hK hb.2.2 hb.1.2
  have hWdG : ∀ b, DelWd K c ρ (IoWS (st := st) K.toKLayout Locks σ) b → b ∈ K.user ∨ ¬ PWE K E b := by
    rintro b (⟨⟨-, hw⟩, hp, -⟩ | hu)
    · exact Or.inr (rt_notPWE' hK hp (Or.inl (wperm_region hw)))
    · exact Or.inl hu.2
  exact PathObl.insA_narrow_tr_wrU_noG (own := ownP K) (cls := OwnMap.cls K.toKLayout)
    (kt := OwnMap.ko K.toKLayout μ) (User := (· ∈ K.user)) ar adEq_equiv (moveHeldP hK) (ownDepP hK hU)
    (masksWr_plain st) (pwe_own hK) (fun x hx => pwe_ko hK μ hx) (fun b hb => pwe_user hU hb) (a := a)
    (R.invBodyG number p) hc (R0 := fun x => InvCMRS (st := st) K.toKLayout Locks σ x ∧ ¬ x ∈ K.ptes)
    (Qv := VO K c ρ) (Rd := Rd) (Ru := PathObl.UserW K.toKLayout)
    (Wd := DelWd K c ρ (IoWS (st := st) K.toKLayout Locks σ)) (fun b hb => vo_of_pwe hK hb) hal hR0
    (fun b h => h.1) (fun b h => h.2) hRdG hWdG hWd hRPO (fun x hx => hV.2.1 x hx) hgo

end main

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **U9's re-annotated body is `InsA` at every Copy / Mint start** (module docstring; glue as `inv_annV_cmA`). -/
theorem cm_insA_annV {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {j : InvArg S} (E : U64 → U64)
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
      (.inr (.inr j)))
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  obtain ⟨σe, hC'⟩ := hC
  have hσe : Ch σe := by
    obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
    exact h'
  have hsf' := hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v
  obtain ⟨q0, ⟨h, σ, a, he, hc, hl, hμ, e⟩, rfl⟩ := hsf'
  subst e
  have hJ : SlJAt (L := L) K.toKLayout σ := ChainOf.bun hC' σ he.1
  have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x := hμ
  have hqu : QU st K σ :=
    qU_startN st ⟨σe, ChainOf.bun hC' σe hσe⟩ hJ hE (fun x hx hu => hμ x hx hu)
  have hc' : L.cpu σ = c := hc
  have hl' : j.Locks σ = (fun l => s.lk l = some c) := hl
  unfold annV
  rw [hM.own, hM.cls, hM.ko] at hV ⊢
  have h1 := inv_cm_insA ar hA hK hU h.nv E hV (number := j.number) (a := a) (h.hCs st) h.lk hJ he.2 hqu hc' hl'
    hmm
  rw [tr_cut (InvCMRS (st := st) K.toKLayout j.Locks σ) (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout)
    (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
    (R.invBodyG j.number j.p) ∅ a] at h1
  have eRS : (cmPathVU st ar hA (masksWr_plain st) j K (view K.toKLayout c ρ) hK hU h).RS σ =
      InvCMRS (st := st) K.toKLayout j.Locks σ :=
    funext fun x => propext ⟨fun h' => h'.1, fun h' => ⟨h', not_vData_empty h.nv⟩⟩
  convert h1 using 3
  unfold LocalPath.body
  rw [hc, eRS]
  all_goals rfl

end all

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The Copy / Mint indices of the PageMap index type. -/
def CmPm : IxV13Pm S → Prop
  | .inl (.inr (.inr _)) => True
  | _ => False

set_option maxHeartbeats 4000000 in
/-- **`InsV15V`'s obligation of `nativePmKAD B` at every Copy / Mint start** (module docstring). -/
theorem insAP_cm_view (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    {E : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : CmPm (S := S) i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with ((j | ((j | j) | j)) | j)
  all_goals try exact False.elim hx
  have hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inl (.inr (.inr j))) := fun h => h
  rw [if_pos hn]
  have hsf0 : StartV13 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 (.inr (.inr j)) := hsf
  have hsf' := startV2C_of_V13 st ar hA a0 hC hsf0
  exact insAP_of_insA (cm_insA_annV st ar hA a0 E hC (epochPteN_view_of J nv hM hV) hsf' hM hV)

/-- **The view starts at which the obligation is still asked after gen 50's Copy / Mint step** (module docstring). -/
def Open51 (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64) (ρ : U64 → U64) (k0 : SP) (i : IxV13Pm S) : Prop :=
  Open50 st s K c ρ k0 i ∧ ¬ CmPm (S := S) i

set_option maxHeartbeats 4000000 in
/-- **`InsV15NOV … Open51` gives `InsV15NOV … Open50`** for `nativePmKAD B` (module docstring). -/
theorem insV15NOV50_of_51 (B : PmObl7 st Cs Ω Sg Ac Locks)
    (h : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open51 st)) :
    InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open50 st) := by
  intro Ch s K E hK hU c k0 ρ i nv hO hC J hM hVq hi
  by_cases hl : CmPm (S := S) i
  · exact insAP_cm_view st ar hA a0 B nv hl hC J hM hVq hi
  exact h Ch s K E hK hU c k0 ρ i nv ⟨hO, hl⟩ hC J hM hVq hi

/-- **`serializable_fl4_V15_pmKADC` on the re-based platform**
(gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem serializable_fl4_V15_pmKADC_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks)
    (hI : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open51 st))
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitC P.toC K0.toKLayoutV (Ch0 e))
    (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15C (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) P.toC s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_V15_pmKADI_C st ar hA a0 P B (insV15NOV50_of_51 st ar hA a0 B hI) h0 hA0 hB hc0 hM0 h hq

end pm

end
end Fl4Proofs.P2.E2EP
