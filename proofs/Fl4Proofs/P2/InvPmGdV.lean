/-
# P2 (line p3mc, gen 44): `PmGdV` discharged — the PageMap run on the view-cut checked store

Gen 44's InvPmAnnV reduced the PageMap `VSafe9` premise `PmFhK` [J] to `PmGdV` [J]: at a PageMap view start the run
of `R.invBodyPmG` on `gd st DelRdP DelPwP` (read set `IoRS ∩ SR`, the locked leaves and the aligned user words) is the
real one. mmuAD's PageMap decode-block lemmas (int26: P2/InvPmDecRd, P2/InvPmMvB, P2/InvPmBlkE) are stated on a store
reading **every** `IoRS (ptU K)` word, which the cut store does not. They are used here in the forms with the read
hypothesis cut by a word class `G` (since gen 45 these live next to their originals, which are their instances at
`G := fun _ => True`) (`∀ b, IoRS (ptU K) s b → G b → R b`), the class facts asked only at the words the block
actually reads (the caller's node, registers and TCB fields `STATE` / `SC` / `IN_QUEUE` / 3512, the slots, the SC's
`max` word, the walk words off the leaves, the ks `FEATURES` word), and the leaf asked only when locked:

* `pm_decRdC`, `pm_decWalkC` (P2/InvPmDecRd.lean), `pmAccG2C` (P2/InvPmMvB.lean), `pmFinGC` (P2/InvPmBlkE.lean):
  the cut decode block (proved there; gen 44 had them here);
* **`pm_run_gdV`**: the PageMap analogue of `inv_run_gdP` (P2/InvDelPteGd.lean): every run of
  `handle_invocation_local` at a `PmPreG` entry runs on `gd st R Pw` as on `st` (accepted runs by `inv_acc_genV`
  with the block from `pmAccG2C` / `pmFinGC`; declined runs by `inv_dec_genV` + `io_alt_midRV`);
* **`pmV_gcl`**: at a PageMap view start the classes `GCl` hold for `G := SR K c ρ` (as P2/InvDelPteAnnA's
  `inv_pte_gdA`), with the ks words below 256 in `SR`;
* **`pmGdV_holds`**: **`PmGdV` is a theorem** (`pm_run_gdV` + `pm_isProgOn`);
* **`pmFhK_holds`**: gen 44's [J] `PmFhK B7` is a theorem (`pmFhK_of_gd`, P2/InvPmAnnV.lean);
* **`serializable_fl4_V15_pmKF`**: the PageMap top with neither `PmFhK` nor `PmGdV`: premises `B7 : PmObl7` ([P]
  `cs`, `lk`) beyond V13's.

No named premise. New module; no existing statement changes.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `serializable_fl4_V15_pmKF`.
-/
import Fl4Proofs.P2.InvPmAnnV
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  oAFFINITY oTIMER_DEADLINE)
open Fl4Proofs.P2.E2E (SP tr masksOf Once StartAt LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN NotForeign vn_of_nf nf_node nf_slot nf_none nf_tcb TZero)

noncomputable section

/-! ## Every PageMap run on a cut checked store -/

section run
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **Every PageMap run at a `PmPreG` entry runs on the checked store `gd st R Pw` as on `st`** (module
docstring; the PageMap analogue of `inv_run_gdP`). -/
theorem pm_run_gdV {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64} {s : S}
    (hE : PmPreG st Cs Ω Sg Ac Locks p K m s)
    {R G : U64 → Prop} {Pw : S → U64 → U64 → Prop}
    (Gc : GCl st K.toKLayout K.toKLayout.heap.scBits G s)
    (hR' : ∀ b, IoRSR st K.toKLayout Locks s b → G b → R b)
    (hRp : ∀ b, IoRS (st := st) K.ptU Locks s b → G b → R b)
    (hGs : ∀ b, SlotW K.toKLayout b → G b) (hGv : ∀ b, VsW K.toKLayout b → b ∉ K.ptes → G b)
    (hGf : G (core.num.U64.wrapping_add (L.ksb s) layout.ks.FEATURES))
    (hW : IoWr st (WAll Pw) K.toKLayout.heap.scBits s)
    (hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      ∀ x, Pw x (core.num.U64.wrapping_add (L.curW s) layout.tcb.STATE) v)
    (hc0 : ∀ x v, NullOrFrame v → Pw x p.slot v)
    (hW8 : WAll Pw (core.num.U64.wrapping_add p.slot 8#u64))
    (hRu : ∀ b, PathObl.UserW K.toKLayout b → R b) (hWu : ∀ b, PathObl.UserW K.toKLayout b → WAll Pw b)
    (hRe : ∀ b, b ∈ K.ptes → Locks s b → R b) (hWe : ∀ b, b ∈ K.ptes → Locks s b → WAll Pw b)
    {a : A} {number : I64} {r : Bool × S × A}
    (h : syscall.handle_invocation_local st ar s a number p = ok r) :
    syscall.handle_invocation_local (gd st R Pw) ar s a number p = ok r := by
  have hE0 := hE
  obtain ⟨⟨hJ, hq, hG⟩, -, -⟩ := hE
  have PE := hq.1.1.1
  have P := PE.ptU hG
  have hL : Slot8 K.toKLayout := fun q hq => PE.lay.slot8 q hq
  obtain ⟨-, -, -, -, -, -, hsl, -, -, hSn⟩ := pm_core hq
  have hSeen : ∀ x, SeenW p x → R x := by
    intro x hx
    refine hRp _ (pm_seen hJ hq P x hx) ?_
    rcases hSn x hx with rfl | rfl
    · exact hGs _ (slotW_of hL hsl (o := layout.cte.CAP0) (by simp [layout.cte.CAP0]))
    · exact hGs _ (slotW_of hL hsl (o := layout.cte.CAP1) (by simp [layout.cte.CAP1]))
  have hps : R p.slot ∧ R (core.num.U64.wrapping_add p.slot 8#u64) := by
    have r0 := pm_slotRS hJ hq P (o := 0#u64) (by simp) (by simp)
    rw [wadd_zero (hL _ hsl).2] at r0
    exact ⟨hRp _ r0 (Gc.sl _ hsl).1, hRp _ (pm_slotRS hJ hq P (o := 8#u64) (by simp) (by simp)) (Gc.sl _ hsl).2⟩
  have hmi : R (regA (L.curW s) layout.reg.MSG_INFO) :=
    hR' _ (PE.regR (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1 (Gc.r _ (by simp [layout.reg.MSG_INFO]))
  have hfl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64) :=
    hR' _ (PE.homeR (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField])).1 (Gc.t _ (by simp) (by simp) (by simp))
  have hnx : R (regA (L.curW s) layout.reg.NEXT_IP) :=
    hR' _ (PE.regR (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1 (Gc.r _ (by simp [layout.reg.NEXT_IP]))
  have Ent := PE.entV Gc hR' hW
  have hsw : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING → SWr (gd st R Pw) st (L.curW s) v :=
    fun v hv X => gd_write (hst v hv X)
  obtain ⟨b, s', a'⟩ := r
  by_cases hb : b = true
  · subst hb
    refine inv_acc_genV (gS := gd st R Pw) (W := WAll Pw) hA PE hW Ent hmi hfl hnx
      (fun C hroot hcl hsl hsc0 info emi => PE.midV Gc hR' hW hroot hcl hsl hsc0 info emi) hSeen hps ?_ h
    intro info nx s1 s2 a1 buf length cap emi C _ hcap y hy
    have hmx := maxA_facts PE.bxi.2.2.1.1 PE.cscS
    obtain ⟨hdec, hrep⟩ := pmAccG2C (gS := gd st R Pw) (R := R) (W := WAll Pw) (G := G) hA hE0 hRp hRu (fun b hp hl _ => hRe b hp hl) hW hsw
      (fun x v hv => gd_write (hc0 x v hv)) hW8 hWu hWe (fun o ho => Gc.n o ho) (fun r hr => Gc.r r hr) Gc.sl
      hGv (by have := Gc.t 3328#u64 (by simp) (by simp) (by simp); rw [Fl4Proofs.P1.stA_eq]; exact this)
      (Gc.t 3464#u64 (by simp) (by simp) (by simp)) (Gc.t 3592#u64 (by simp) (by simp) (by simp))
      (Gc.sc _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩) (Gc.t 3512#u64 (by simp) (by simp) (by simp)) hGf emi C hcap hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ := pmFinGC (gS := gd st R Pw) hA hE0 Ent (hsw _ (Or.inr rfl)) emi C hcap hy hz'
    exact ⟨hrep z hz', h1, h2⟩
  · exact inv_dec_genV (gS := gd st R Pw) (W := WAll Pw) Ent.acc.nd hmi hfl hnx
      (hW.reg _ (by simp [layout.reg.FAULT_IP]))
      (fun nx s1 s2 a1 _ e1 e2 => io_alt_midRV (m0 := m) hA PE Gc hR' (Alt.refl s) e1 e2) hSeen h hb

end run

/-! ## `PmGdV` holds -/

section gdv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The word classes of a PageMap view start are `SR`** (as P2/InvDelPteAnnA's `inv_pte_gdA`). -/
theorem pmV_gcl {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64}
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (hq : PmQF st Cs Ω Sg Ac Locks p K (view K.toKLayout c ρ) σ) (hqu : QU st K σ)
    (hc : L.cpu σ = c)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    GCl st K.toKLayout K.toKLayout.heap.scBits (SR K c ρ) σ ∧
      (∀ b, SlotW K.toKLayout b → SR K c ρ b) ∧
      (∀ o : U64, o.val < 256 → o.val % 8 = 0 → SR K c ρ (core.num.U64.wrapping_add (L.ksb σ) o)) := by
  have hX := hJ.regionOKX
  obtain ⟨Ac', B⟩ := bunIx_of hJ
  have hI := B.bxi
  have hL := B.stLay
  have hP := stPre_ofS B.ac
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced K.toKLayout.heap.tcbs := h0.tcbs
  have hcT : L.curW σ ∈ K.toKLayout.heap.tcbs := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have hcur : ρ (fld (L.curW σ) oAFFINITY) = c := vx_cur_home hJ hmm
  have PE := hq.1.1.1
  have hL8 : Slot8 K.toKLayout := fun q hq => PE.lay.slot8 q hq
  have hQ := hqu.1
  have ct0 : L.curW σ ≠ 0#u64 := fun e => (hT _ hcT).ne0 (by rw [e]; rfl)
  -- homes (as P2/IrqWhAnn)
  have hO := hI.2.2.1.1
  have scHome : ∀ p, p ∈ Heap.scs K.toKLayout.heap → L.mem σ (scTcbA p) ≠ 0#u64 → ρ (fld p 16#u64) = c := by
    intro p hp hp0
    obtain ⟨hP', hz⟩ := hO.sc _ hp
    obtain ⟨h8, h128, hfit⟩ := sc_lo hP' hz
    have hv : (scTcbA p).val = p.val + 24 := by
      unfold scTcbA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have hr : region K.toKLayout (scTcbA p) = .sc p :=
      hX.scW p _ (st_scH (K := K) hp) _ ⟨by omega, by omega⟩
    have ha : Aligned (scTcbA p) := by unfold Aligned; rw [hv]; omega
    have hku : scTcbA p ∉ K.user := hL.nu_sc hp ⟨by omega, by omega⟩
    exact CoreView.view_sctcb_home (K := K.toKLayout) hr (by omega) (by rw [← hmm _ ha hku]; exact hp0)
  have hcsc0 : L.cscW σ ≠ 0#u64 := by
    intro e
    obtain ⟨z, hz'⟩ := hP.csc
    rw [e] at hz'
    have hz2 : K.toKLayout.heap 0#u64 = some (.sc z) := hz'
    rw [slJAt_heap0 hJ] at hz2
    cases hz2
  have hne : L.mem σ (scA (L.curW σ)) ≠ 0#u64 := by rw [hP.sct]; exact hcsc0
  obtain ⟨hcs1, htcb1, -⟩ := hI.2.2.1.2.2.bound _ h0.curT hne
  have hcs : L.cscW σ ∈ Heap.scs K.toKLayout.heap := by rw [← hP.sct]; exact hcs1
  have cscHome : ρ (fld (L.cscW σ) 16#u64) = c := by
    rw [← hP.sct]
    exact scHome _ hcs1 (fun e => ct0 (htcb1.symm.trans e))
  have rhHome : ∀ (h00 : L.mem σ (rhA (L := L) σ) ≠ 0#u64),
      ρ (fld (L.mem σ (rhA (L := L) σ)) oAFFINITY) = c ∧
        ρ (fld (L.mem σ (scA (L.mem σ (rhA (L := L) σ)))) 16#u64) = c := by
    intro h00
    obtain ⟨⟨Q, Rq, hq'⟩, hb, ⟨-, -, hX'⟩, -, -⟩ := id hI
    obtain ⟨hTr, -, -⟩ := bxi_rh hI h00
    have hne' : L.mem σ (scA (L.mem σ (rhA (L := L) σ))) ≠ 0#u64 := by
      intro e0
      have hfl := hb.r _ hTr
      have hrel := hq'.release _ hq'.cur
      have hd : L.mem σ (rhA (L := L) σ) = (Rq (L.cpu σ)).headD 0#u64 := hrel.head
      have hmR : L.mem σ (rhA (L := L) σ) ∈ Rq (L.cpu σ) := by
        cases hl' : Rq (L.cpu σ) with
        | nil => rw [hl'] at hd; exact absurd hd h00
        | cons r rs => rw [hl'] at hd; rw [hd]; simp
      exact hfl ((hq'.released _ hTr).2 (by rw [hq'.inR _ hq'.cur _ hmR]; exact hmR)) e0
    obtain ⟨hcs', htcb, -⟩ := hX'.bound _ hTr hne'
    refine ⟨?_, scHome _ hcs' (fun e => h00 (htcb.symm.trans e))⟩
    have hrH : K.toKLayout.heap (L.mem σ (rhA (L := L) σ)) = some .tcb := hTr
    obtain ⟨hr, hv, ha⟩ := hX.tcbW _ hrH 3464#u64 (by simp) (by simp) (by simp)
    have hu : scA (L.mem σ (rhA (L := L) σ)) ∉ K.user := hL.nu_tcb hTr (k := 3464#u64) (by simp) (by simp)
    refine CoreView.view_tzero_home hr (by rw [hv]; simp [TZero]) ?_
    rw [← hmm _ ha hu]; exact hne'
  have armρ : L.mem σ (tmA (L := L) σ) ≠ 0#u64 → ρ (fld (L.mem σ (tmA (L := L) σ)) oTIMER_DEADLINE) ≠ 0#u64 := by
    intro hne'
    obtain ⟨tmT, arm⟩ := tmin_facts (BXI.blk hI) h0.cur hne'
    have tH : K.toKLayout.heap (L.mem σ (tmA (L := L) σ)) = some .tcb := tmT
    obtain ⟨hr0, hv0, hal⟩ := hX.tcbW _ tH 3528#u64 (by simp) (by simp) (by simp)
    have hr : region K.toKLayout (tdA (L.mem σ (tmA (L := L) σ))) = .tcb (L.mem σ (tmA (L := L) σ)) := hr0
    have hv : (tdA (L.mem σ (tmA (L := L) σ))).val - (L.mem σ (tmA (L := L) σ)).val = (3528#u64).val := hv0
    have hu : tdA (L.mem σ (tmA (L := L) σ)) ∉ K.user := hL.nu_tcb tmT (k := 3528#u64) (by simp) (by simp)
    have e1 := hmm (tdA (L.mem σ (tmA (L := L) σ))) hal hu
    have e2 : view K.toKLayout c ρ (tdA (L.mem σ (tmA (L := L) σ))) = ρ (tdA (L.mem σ (tmA (L := L) σ))) :=
      CoreView.view_timer_keep hr (by rw [hv]; simp) (by rw [hv]; simp)
    intro e
    exact arm.1 (by rw [e1, e2]; exact e)
  -- the word classes are `SR`
  have srN : ∀ o : U64, o.val < 4288 → SR K c ρ (L.nodeAt σ (L.cpu σ) o) := fun o ho => by
    have hr : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node (L.cpu σ) := hL.nd o ho
    have hr' : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node c := by rw [hr, hc]
    exact sr_nf hK (by rw [hr']; intro h; cases h) (nf_node hr')
  have srT : ∀ k : U64, 192 ≤ k.val → k.val < 4096 → k.val % 8 = 0 →
      SR K c ρ (core.num.U64.wrapping_add (L.curW σ) k) := fun k h1 h2 h3 =>
    sr_tcb hK hX htH hcur (o := k) h1 h2 h3
  have srW : ∀ b, SlotW K.toKLayout b → SR K c ρ b := fun b ⟨q, hq', hin⟩ => by
    have hr := PE.lay.slotw q hq' b hin
    exact sr_nf hK (by rw [hr]; intro h; cases h) (nf_slot hr)
  have sW0 : ∀ q, q ∈ K.slots → SlotW K.toKLayout q := fun q hq' => by
    have := slotW_of hL8 hq' (o := 0#u64) (by simp); rwa [wadd_zero (hL8 q hq').2] at this
  have srC : ∀ b, InSC (L.cscW σ) (K.toKLayout.heap.scBits (L.cscW σ)) b → SR K c ρ b := fun b hb =>
    (srw_sc hK hX (st_scH (K := K) hcs) cscHome hb).1
  have srK : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → SR K c ρ (core.num.U64.wrapping_add (L.ksb σ) o) := by
    intro o h1 h2
    obtain ⟨k8, kf⟩ := PE.lay.ksf
    have hv : (core.num.U64.wrapping_add (L.ksb σ) o).val = (L.ksb σ).val + o.val := by
      rw [← PE.kb]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have hr : region K.toKLayout (core.num.U64.wrapping_add (L.ksb σ) o) = .none := by
      refine PE.lay.ks _ ?_ ?_ ?_
      · unfold Aligned; rw [hv, ← PE.kb]; omega
      · rw [hv, ← PE.kb]; omega
      · rw [hv, ← PE.kb]; omega
    exact ⟨vn_of_nf hK (nf_none hr), hQ.ksw (by omega)⟩
  refine ⟨?_, srW, srK⟩
  exact
    { n := srN
      t := fun k h1 h2 h3 => srT k (by omega) h2 h3
      r := fun r hr => by
        obtain ⟨o, ho, e⟩ := regA_eq' (t := L.curW σ) hr
        rw [e]; exact srT o (by omega) (by omega) (by omega)
      sl := fun q hq' => ⟨srW _ (sW0 q hq'), srW _ (slotW_of hL8 hq' (o := 8#u64) (by simp))⟩
      sc := fun b _ hb => srC b hb
      ks := by
        rintro o (rfl | rfl)
        · exact ⟨vn_of_nf hK (nf_none hL.dom), hQ.ksw (by simp [layout.ks.CUR_DOMAIN])⟩
        · exact ⟨vn_of_nf hK (nf_none hL.dtm), hQ.ksw (by simp [layout.ks.DOMAIN_TIME])⟩
      td := fun hne' => by
        obtain ⟨tmT, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne'
        exact sr_timer hK hX (show K.toKLayout.heap _ = some .tcb from tmT) (o := 3528#u64) (by simp) (by simp)
          (by simp) (armρ hne')
      rs := fun hne' => by
        obtain ⟨r1, -, -, r4, -⟩ := rel_facts hI hne'
        obtain ⟨-, hsc', ha'⟩ := bxi_rh PE.bxi hne'
        obtain ⟨hWf, -⟩ := bxi_scin PE.bxi hsc' ha'
        refine ⟨sr_tcb hK hX (show K.toKLayout.heap _ = some .tcb from r1) (rhHome hne').1 (o := 3464#u64)
          (by simp) (by simp) (by simp), ?_⟩
        have hSA : ScAcc (SR K c ρ) (fun _ => True) (L.mem σ (scA (L.mem σ (rhA (L := L) σ))))
            (K.toKLayout.heap.scBits (L.mem σ (scA (L.mem σ (rhA (L := L) σ))))) :=
          ⟨fun b _ hb => (srw_sc hK hX (st_scH (K := K) r4) (rhHome hne').2 hb).1, fun _ _ _ => trivial, trivial⟩
        exact hSA.head hWf }

set_option maxHeartbeats 4000000 in
/-- **`PmGdV` holds** (module docstring): at a PageMap view start the run of the PageMap body on
`gd st DelRdP DelPwP` is the real one. -/
theorem pmGdV_holds (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} :
    PmGdV st ar Cs Ω Sg Ac Locks := by
  intro K hK hU c ρ j σ a hPre hqu hc hmm
  have hJ : SlJAt (L := L) K.toKLayout σ := hPre.1.1
  have hq := hPre.1.2.1
  have hK0 := hJ.regionOK
  have hLA := hJ.ioLayA
  have PE := hq.1.1.1
  have hL8 : Slot8 K.toKLayout := fun q hq => PE.lay.slot8 q hq
  obtain ⟨Gc, srW, srK⟩ := pmV_gcl hK hJ hq hqu hc hmm
  have hQ := hqu.1
  have hX := hJ.regionOKX
  obtain ⟨Ac', B⟩ := bunIx_of hJ
  have h0 := B.bxi.1.choose_spec.choose_spec
  have hcT : L.curW σ ∈ K.toKLayout.heap.tcbs := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have hcur : ρ (fld (L.curW σ) oAFFINITY) = c := vx_cur_home hJ hmm
  have srN : ∀ o : U64, o.val < 4288 → SR K c ρ (L.nodeAt σ (L.cpu σ) o) := fun o ho => Gc.n o ho
  have srT : ∀ k : U64, 192 ≤ k.val → k.val < 4096 → k.val % 8 = 0 →
      SR K c ρ (core.num.U64.wrapping_add (L.curW σ) k) := fun k h1 h2 h3 =>
    sr_tcb hK hX htH hcur (o := k) h1 h2 h3
  have srC : ∀ b, Aligned b → InSC (L.cscW σ) (K.toKLayout.heap.scBits (L.cscW σ)) b → SR K c ρ b :=
    fun b ha hb => Gc.sc b ha hb
  have sW0 : ∀ q, q ∈ K.slots → SlotW K.toKLayout q := fun q hq' => by
    have := slotW_of hL8 hq' (o := 0#u64) (by simp); rwa [wadd_zero (hL8 q hq').2] at this
  -- the read set
  let Rd : U64 → Prop := DelRdP K c ρ (IoRS (st := st) K.toKLayout Locks σ) (Locks σ)
  have hR' : ∀ b, IoRSR st K.toKLayout Locks σ b → SR K c ρ b → Rd b :=
    fun b h g => Or.inl (Or.inl ⟨h.1, g⟩)
  have hRp : ∀ b, IoRS (st := st) K.ptU Locks σ b → SR K c ρ b → Rd b :=
    fun b h g => Or.inl (Or.inl ⟨⟨h.1, fun hu => h.2.1 (Or.inl hu), h.2.2⟩, g⟩)
  -- the checked writes (as `inv_pte_gdA`)
  let Pw : S → U64 → U64 → Prop := DelPw (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ)
    (IoWS (st := st) K.toKLayout Locks σ) (L.curW σ) (L.mem σ) (Locks σ)
  have wdW : ∀ b, IoWS (st := st) K.toKLayout Locks σ b → SR K c ρ b →
      IoWS (st := st) K.toKLayout Locks σ b ∧ b ∉ K.ptes ∧ VO K c ρ b := fun b h g => ⟨h, g.2, g.1.2⟩
  have hWr : IoWr st (WAll Pw) K.toKLayout.heap.scBits σ :=
    { nd := fun o h1 h2 => fun _ _ => Or.inl ⟨nodeAt_aligned PE.np h1 h2,
        safe_notDecW hK0 hLA (Or.inl ⟨L.cpu σ, PE.lay.node _ _ (PE.inNode o h1)⟩),
        wdW _ ((PE.ioWr (Locks := Locks)).nd o h1 h2) (srN o h1)⟩
      reg := fun r hr => by
        have w := (PE.ioWr (Locks := Locks)).reg r hr
        obtain ⟨k, hk, e⟩ := regA_eq PE.tA hr
        have hk4 : k.val < 4096 := by omega
        rw [e] at w ⊢
        exact fun _ _ => Or.inl ⟨field_aligned PE.tA hk4 (by omega),
          safe_notDecW hK0 hLA (Or.inr (Or.inl ⟨L.curW σ, k.val, PE.hT _ PE.cT,
            PE.lay.tcbw _ (PE.hT _ PE.cT) k (by omega) hk4, hk4, tcb_wadd_val PE.tA hk4, by omega, by omega,
            by omega, by omega, by omega, by omega⟩)),
          wdW _ w (srT k (by omega) hk4 (by omega))⟩
      ring := fun b ha hb => fun _ _ => Or.inl ⟨ha,
        safe_notDecW hK0 hLA (Or.inr (Or.inr ⟨L.cscW σ, PE.lay.scw _ _ (PE.hSc _ PE.cscS) b hb.inSC,
          by have := hb.1; omega⟩)),
        wdW _ ((PE.ioWr (Locks := Locks)).ring b ha hb) (srC b ha hb.inSC)⟩
      cons := by
        obtain ⟨hP', hz⟩ := PE.bxi.2.2.1.1.sc _ PE.cscS
        obtain ⟨h8, h128, -⟩ := sc_lo hP' hz
        have hv := sc_word_val hP' hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
        have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
        have hin : InSC (L.cscW σ) (K.toKLayout.heap.scBits (L.cscW σ))
            (core.num.U64.wrapping_add (L.cscW σ) layout.sc.CONSUMED) := ⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩
        have hal : Aligned (core.num.U64.wrapping_add (L.cscW σ) layout.sc.CONSUMED) := by
          unfold Aligned; rw [hv, hcv]; omega
        exact fun _ _ => Or.inl ⟨hal,
          safe_notDecW hK0 hLA (Or.inr (Or.inr ⟨L.cscW σ, PE.lay.scw _ _ (PE.hSc _ PE.cscS) _ hin,
            by rw [hv, hcv]; omega⟩)),
          wdW _ (PE.ioWr (Locks := Locks)).cons (srC _ hal hin)⟩ }
  -- the PageMap writes
  let Pw' : S → U64 → U64 → Prop := DelPwP (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ)
    (IoWS (st := st) K.toKLayout Locks σ) (L.curW σ) (L.mem σ) (Locks σ)
  have hWr' : IoWr st (WAll Pw') K.toKLayout.heap.scBits σ := hWr.mono (fun b h x v => Or.inl (h x v))
  obtain ⟨fp, rt, asid0, va0, mp, hcs, hsl, -, hlkS, -⟩ := pm_core hq
  have hsl0 : Locks σ j.2.slot := hlkS (fun e => slJAt_slot0 hJ (e ▸ hsl))
  have hO : OutsideObjs st K.heap.tcbs Cs σ j.2.slot := by
    obtain ⟨x, hx, hxs⟩ := hq.2
    obtain ⟨Cw, hroot, hcl, hC⟩ := PE.walk
    obtain ⟨q0, r0, m0, y0, hq0, hm0, hs0⟩ := lookup_slot_cn hroot hcl hx
    rw [← hxs, hs0]; exact (hC q0 r0 m0 y0 hq0 hm0).2.1
  have hnT : ¬ TcbSlot K.toKLayout j.2.slot := notTcbSlot_of hO
  have hnf := nof_of_frame_slot hcs
  have hc0 : ∀ x v, NullOrFrame v → Pw' x j.2.slot v := by
    intro x v hv
    have r := (PE.lockSlot hsl hsl0 (o := 0#u64) (by simp) (by simp)).1
    rw [wadd_zero (hL8 _ hsl).2] at r
    exact Or.inl (Or.inr (Or.inr (Or.inl ⟨hsl, hnT, ⟨r, srW _ (sW0 _ hsl)⟩, hnf, hv, hsl0⟩)))
  have hW8 : WAll Pw' (core.num.U64.wrapping_add j.2.slot 8#u64) := by
    obtain ⟨q8, qf⟩ := PE.lay.slot8 j.2.slot hsl
    have hv := PathObl.slot_word_val qf (o := 8#u64) (by simp)
    have hr := PE.lay.slotw j.2.slot hsl _ (slot_inW qf (o := 8#u64) (by simp))
    have hne' : core.num.U64.wrapping_add j.2.slot 8#u64 ≠ j.2.slot := fun e => by
      have := congrArg UScalar.val e; rw [hv] at this; simp at this
    have ha : Aligned (core.num.U64.wrapping_add j.2.slot 8#u64) := by
      unfold Aligned; rw [hv]; simp; omega
    exact fun _ _ => Or.inl (Or.inl ⟨ha, OwnMap.nondec_slotw hK0 hr hne',
      wdW _ ((PE.lockSlot hsl hsl0 (o := 8#u64) (by simp) (by simp)).2 (Or.inr ⟨hnT, hnf⟩))
        (srW _ (slotW_of hL8 hsl (o := 8#u64) (by simp)))⟩)
  have hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      ∀ x, Pw' x (core.num.U64.wrapping_add (L.curW σ) layout.tcb.STATE) v :=
    fun v hv _ => Or.inl (Or.inr (Or.inl ⟨rfl, hv⟩))
  have hWu : ∀ b, PathObl.UserW K.toKLayout b → WAll Pw' b :=
    fun b h _ _ => Or.inl (Or.inr (Or.inr (Or.inr h)))
  have hWe : ∀ b, b ∈ K.ptes → Locks σ b → WAll Pw' b := fun b hb hl _ _ => Or.inr ⟨hb, hl⟩
  -- the run at `σ` on the checked store, and its tree
  obtain ⟨r, hr0⟩ := inv_total (st := st) hA j.1 j.2 σ a
  have hgσ0 := pm_run_gdV (R := Rd) (G := SR K c ρ) (Pw := Pw') hA hPre Gc hR' hRp srW
    (fun b hb hp => ⟨vn_of_nf hK (nf_none hb.2.1), hp⟩)
    (srK _ (by simp [layout.ks.FEATURES]) (by simp [layout.ks.FEATURES])) hWr' hst hc0 hW8
    (fun b h => Or.inr h) hWu (fun b hb hl => Or.inl (Or.inr ⟨hb, hl⟩)) hWe hr0
  have hpR := pm_isProgOn (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) (p := j.2)
    (K := K) (μ := view K.toKLayout c ρ) hA j.1
  exact ⟨r, (inv_hp hpR (Narrow.gd _ _ _) (AltOf.pre hPre.1) a).symm.trans hgσ0,
    (inv_hp hpR (Narrow.self st) (AltOf.pre hPre.1) a).symm.trans hr0⟩

end gdv

/-! ## The top without `PmFhK` / `PmGdV` -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- **Gen 44's [J] `PmFhK` is a theorem** (`pmFhK_of_gd` with `pmGdV_holds`). -/
theorem pmFhK_holds (B : PmObl7 st Cs Ω Sg Ac Locks) :
    PmFhK st ar hA (arI := arI) (AR := AR) (MR := MR) B :=
  pmFhK_of_gd st ar hA B (pmGdV_holds ar hA)

end top

end
end Fl4Proofs.P2.E2EP
