/-
# P2 (line p3mc, gen 28): the Copy / Mint certificate at every view start

Handoff §32d item 2. The Copy / Mint (`cmSlotU`) analogue of P2/InvDelAnnA, same route: `PathObl.safe_tr_wrU` with
the read set `IoRS ∩ SR` plus the aligned user words (`DelRd`), the write set `DelWd`, the state-independent checked
writes `DelPw` (P2/InvDelAnnA; their slot clause, a Null / Frame value into a locked non-TCB slot of the read set
holding Null / Frame, is the CDT insert's write of the derived **Frame** cap into `dest`'s `CAP0`, whose `StepOK`
is `stepOK_slot`):

* **`wrsCM_facts`**: aligned user-word writes keep `SlJAt`, `InvQCMW`, `QU`, the locks, `IoRS`, `IoWS`, the current
  thread (`hufQCMW_of`, `qU_wr`, `SlJAt.curW_wr`; the locks by `hlk`, the existing `InvPremW.lk` [P]);
* **`inv_cm_gdA`**: at a bundle state of the view with `InvQCMW` and `QU`, the run on `gd st DelRd DelPw` is the
  real one (`inv_run_gdCM`, P2/InvCMGd), and the tree's (`inv_isProgOnR` with `cmSC_ofZ`);
* **`inv_cm_annA`**: as `inv_del_annA`, `Once` from `inv_pathCME`'s `once`.

No named premise (`hCs`, `hlk` are the start record's `InvPremW.hCs` / `InvPremW.lk` [P]). New module; no existing
statement changes.
-/
import Fl4Proofs.P2.InvDelAnnA
import Fl4Proofs.P2.InvCMGd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE oSTATE InW GateField TimerField GField
  tcbOwner TcbSlot NullOrFrame)
open Fl4Proofs.P2.E2E (SP tr masksOf Once)
open Fl4Proofs.P2.Serial (Owner VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN NotForeign vn_of_nf nf_node nf_slot nf_none nf_tcb TZero)

noncomputable section
open Classical

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)

/-- **Aligned user-word writes keep the Copy / Mint view start's facts** (module docstring). -/
theorem wrsCM_facts {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP}
    {m f : U64 → U64} (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ (K' : OwnMap.KLayout) (s : S) (b v : U64), SlJAt (L := L) K' s → b ∈ K'.user → Aligned b →
      Locks (L.wr s b v) = Locks s) :
    ∀ (l : List U64) (s : S), (∀ x ∈ l, Aligned x ∧ x ∈ K.user) → SlJAt (L := L) K.toKLayout s →
      InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s → QU st K s →
      SlJAt (L := L) K.toKLayout (E2E.wrs st f l s) ∧
      InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m (E2E.wrs st f l s) ∧ QU st K (E2E.wrs st f l s) ∧
      Locks (E2E.wrs st f l s) = Locks s ∧
      IoRS (st := st) K.toKLayout Locks (E2E.wrs st f l s) = IoRS (st := st) K.toKLayout Locks s ∧
      IoWS (st := st) K.toKLayout Locks (E2E.wrs st f l s) = IoWS (st := st) K.toKLayout Locks s ∧
      L.curW (E2E.wrs st f l s) = L.curW s := by
  intro l
  induction l with
  | nil => intro s _ h1 h2 h3; exact ⟨h1, h2, h3, rfl, rfl, rfl, rfl⟩
  | cons x l ih =>
    intro s hl h1 h2 h3
    obtain ⟨ha, hu⟩ := hl x (List.mem_cons_self ..)
    obtain ⟨⟨g1, g2⟩, g3, g4, g5, -⟩ := hufQCMW_of (ioPre_wr_hIw (Ω := Ω) (Sg := Sg) (Ac := Ac) hCs) hlk
      K.toKLayout m s x (f x) h1 h2 hu ha
    have g6 : QU st K (L.wr s x (f x)) := qU_wr h3 hu ha
    have g7 := h1.curW_wr hu ha (f x)
    obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := ih _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) g1 g2 g6
    exact ⟨k1, k2, k3, k4.trans g3, k5.trans g4, k6.trans g5, k7.trans g7⟩

set_option maxHeartbeats 16000000 in
/-- **At a Copy / Mint view start the run on `gd st DelRd DelPw` is the real one** (module docstring). -/
theorem inv_cm_gdA (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {c : U64} {ρ : U64 → U64}
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {number : I64} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (hq : InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout (view K.toKLayout c ρ) σ) (hqu : QU st K σ)
    (hc : L.cpu σ = c)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    ∃ r, interp (gd st (DelRd K c ρ (IoRS (st := st) K.toKLayout Locks σ))
        (DelPw (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ) (IoWS (st := st) K.toKLayout Locks σ)
          (L.curW σ) (L.mem σ) (Locks σ))) ar (R.invBodyG number p) σ a = ok r ∧
      interp st ar (R.invBodyG number p) σ a = ok r := by
  have hX := hJ.regionOKX
  have hK0 := hJ.regionOK
  have hUO := hJ.userOK
  have hLA := hJ.ioLayA
  obtain ⟨Ac', B⟩ := bunIx_of hJ
  have hI := B.bxi
  have hL := B.stLay
  have hP := stPre_ofS B.ac
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced K.toKLayout.heap.tcbs := h0.tcbs
  have hcT : L.curW σ ∈ K.toKLayout.heap.tcbs := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have ht' := hT _ hcT
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
  let G : U64 → Prop := SR K c ρ
  have Gc : GCl st K.toKLayout K.toKLayout.heap.scBits G σ :=
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
        have hSA : ScAcc G (fun _ => True) (L.mem σ (scA (L.mem σ (rhA (L := L) σ))))
            (K.toKLayout.heap.scBits (L.mem σ (scA (L.mem σ (rhA (L := L) σ))))) :=
          ⟨fun b _ hb => (srw_sc hK hX (st_scH (K := K) r4) (rhHome hne').2 hb).1, fun _ _ _ => trivial, trivial⟩
        exact hSA.head hWf }
  -- the read set, the checked writes
  let Rd : U64 → Prop := DelRd K c ρ (IoRS (st := st) K.toKLayout Locks σ)
  have hR : ∀ b, IoRS (st := st) K.toKLayout Locks σ b → b ∉ K.ptes → G b → Rd b := fun b h _ g => Or.inl ⟨h, g⟩
  let Pw : S → U64 → U64 → Prop := DelPw (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ)
    (IoWS (st := st) K.toKLayout Locks σ) (L.curW σ) (L.mem σ) (Locks σ)
  have wdW : ∀ b, IoWS (st := st) K.toKLayout Locks σ b → SR K c ρ b →
      IoWS (st := st) K.toKLayout Locks σ b ∧ b ∉ K.ptes ∧ VO K c ρ b := fun b h g => ⟨h, g.2, g.1.2⟩
  -- the writes the run needs
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
        wdW _ ((PE.ioWr (Locks := Locks)).ring b ha hb) (srC b hb.inSC)⟩
      cons := by
        obtain ⟨hP', hz⟩ := PE.bxi.2.2.1.1.sc _ PE.cscS
        obtain ⟨h8, h128, -⟩ := sc_lo hP' hz
        have hv := sc_word_val hP' hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
        have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
        have hin : InSC (L.cscW σ) (K.toKLayout.heap.scBits (L.cscW σ))
            (core.num.U64.wrapping_add (L.cscW σ) layout.sc.CONSUMED) := ⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩
        exact fun _ _ => Or.inl ⟨by unfold Aligned; rw [hv, hcv]; omega,
          safe_notDecW hK0 hLA (Or.inr (Or.inr ⟨L.cscW σ, PE.lay.scw _ _ (PE.hSc _ PE.cscS) _ hin,
            by rw [hv, hcv]; omega⟩)),
          wdW _ (PE.ioWr (Locks := Locks)).cons (srC _ hin)⟩ }
  have hwS : ∀ q o, q ∈ K.slots → Locks σ q → o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val →
      (16 ≤ o.val ∨ (¬ TcbSlot K.toKLayout q ∧ NullOrFrame (L.mem σ q))) →
        WAll Pw (core.num.U64.wrapping_add q o) := by
    intro q o hq' hl' ho h8 h8' hc'
    obtain ⟨q8, qf⟩ := PE.lay.slot8 q hq'
    have hv := PathObl.slot_word_val qf ho
    have hr := PE.lay.slotw q hq' _ (slot_inW qf ho)
    have hne' : core.num.U64.wrapping_add q o ≠ q := fun e => by
      have := congrArg UScalar.val e; rw [hv] at this; omega
    have ha : Aligned (core.num.U64.wrapping_add q o) := by unfold Aligned; rw [hv]; omega
    exact fun _ _ => Or.inl ⟨ha, OwnMap.nondec_slotw hK0 hr hne',
      wdW _ ((PE.lockSlot hq' hl' ho h8).2 hc') (srW _ (slotW_of hL8 hq' ho))⟩
  have hw0 : ∀ q, q ∈ K.slots → Locks σ q → ¬ TcbSlot K.toKLayout q → NullOrFrame (L.mem σ q) →
      ∀ x v, NullOrFrame v → Pw x q v := by
    intro q hq' hl' hT' hn x v hv
    have r := (PE.lockSlot hq' hl' (o := 0#u64) (by simp) (by simp)).1
    rw [wadd_zero (hL8 q hq').2] at r
    exact Or.inr (Or.inr (Or.inl ⟨hq', hT', ⟨r, srW _ (sW0 q hq')⟩, hn, hv, hl'⟩))
  have hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      ∀ x, Pw x (core.num.U64.wrapping_add (L.curW σ) layout.tcb.STATE) v :=
    fun v hv _ => Or.inr (Or.inl ⟨rfl, hv⟩)
  have hWu : ∀ b, PathObl.UserW K.toKLayout b → WAll Pw b := fun b h _ _ => Or.inr (Or.inr (Or.inr h))
  -- the run at `σ` on the checked store, and its tree
  obtain ⟨r, hr0⟩ := inv_total (st := st) hA number p σ a
  have hgσ0 := inv_run_gdCM hA hK hU ⟨hJ, hq⟩ hQ.ks Gc hR srW hWr hwS hw0 hst (fun b h => Or.inr h) hWu hr0
  have hSC : InvSlotCN st K.toKLayout p
      (fun s => (SlJAt (L := L) K.toKLayout s ∧
        InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout (view K.toKLayout c ρ) s) ∧ QU st K s) :=
    fun s h => cmSC_ofZ K.toKLayout (view K.toKLayout c ρ) s h.1
  have hpR := inv_isProgOnR (Locks := Locks) (m0 := view K.toKLayout c ρ) hA
    (P := fun s => (SlJAt (L := L) K.toKLayout s ∧
      InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout (view K.toKLayout c ρ) s) ∧ QU st K s)
    (fun _ h => h.1.2.1.1.1) hSC (inv_isProg S number p)
  have hgσ : interp (gd st Rd Pw) ar (R.invBodyG number p) σ a = ok r :=
    (hpR (gd st Rd Pw) (Narrow.gd _ _ _) σ ⟨σ, ⟨⟨hJ, hq⟩, hqu⟩, Alt.refl σ⟩ a).symm.trans hgσ0
  exact ⟨r, (hpR (gd st Rd Pw) (Narrow.gd _ _ _) σ ⟨σ, ⟨⟨hJ, hq⟩, hqu⟩, Alt.refl σ⟩ a).symm.trans hgσ0,
    (hpR st (Narrow.self st) σ ⟨σ, ⟨⟨hJ, hq⟩, hqu⟩, Alt.refl σ⟩ a).symm.trans hr0⟩

set_option maxHeartbeats 16000000 in
/-- **U9's armed Copy / Mint program is `Safe` at every Copy / Mint view start** (module docstring). -/
theorem inv_cm_annA (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {number : I64} {σ : S} {a : A}
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ (K' : OwnMap.KLayout) (s : S) (b v : U64), SlJAt (L := L) K' s → b ∈ K'.user → Aligned b →
      Locks (L.wr s b v) = Locks s)
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (hq : InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout (view K.toKLayout c ρ) σ) (hqu : QU st K σ)
    (hc : L.cpu σ = c) (hl : Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (fun x => InvCMRS (st := st) K.toKLayout Locks σ x ∧ ¬ x ∈ K.ptes) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.invBodyG number p) ∅ a)) := by

  have hX := hJ.regionOKX
  have hK0 := hJ.regionOK
  have hUO := hJ.userOK
  have hLA := hJ.ioLayA
  obtain ⟨Ac', B⟩ := bunIx_of hJ
  have hI := B.bxi
  have hL := B.stLay
  have hP := stPre_ofS B.ac
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced K.toKLayout.heap.tcbs := h0.tcbs
  have hcT : L.curW σ ∈ K.toKLayout.heap.tcbs := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have ht' := hT _ hcT
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
  let G : U64 → Prop := SR K c ρ
  have Gc : GCl st K.toKLayout K.toKLayout.heap.scBits G σ :=
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
        have hSA : ScAcc G (fun _ => True) (L.mem σ (scA (L.mem σ (rhA (L := L) σ))))
            (K.toKLayout.heap.scBits (L.mem σ (scA (L.mem σ (rhA (L := L) σ))))) :=
          ⟨fun b _ hb => (srw_sc hK hX (st_scH (K := K) r4) (rhHome hne').2 hb).1, fun _ _ _ => trivial, trivial⟩
        exact hSA.head hWf }
  -- the read sets
  let Rd : U64 → Prop := fun b => IoRS (st := st) K.toKLayout Locks σ b ∧ SR K c ρ b
  let Ro : U64 → Prop := fun q => (InvCMRS (st := st) K.toKLayout Locks σ q ∧ ¬ q ∈ K.ptes) ∧ VO K c ρ q
  have hR0 : ∀ q, Rd q → Ro q ∧ ¬ q ∈ K.user := fun q hq' =>
    ⟨⟨⟨ioRS_cm hq'.1, hq'.2.2⟩, hq'.2.1.2⟩, hq'.1.2.1⟩
  have hal : ∀ b, Rd b → Aligned b := fun b hb => hb.1.1
  have kvR : ∀ b, Rd b → L.mem σ b = ρ b := fun b hb =>
    (hmm b hb.1.1 hb.1.2.1).trans hb.2.1.1
  let Ru : U64 → Prop := PathObl.UserW K.toKLayout
  let RdU : U64 → Prop := DelRd K c ρ (IoRS (st := st) K.toKLayout Locks σ)
  have hRal : ∀ b, RdU b → Aligned b := fun b h => h.elim (fun h => h.1.1) (fun h => h.1)
  -- the write sets
  let Wd : U64 → Prop := DelWd K c ρ (IoWS (st := st) K.toKLayout Locks σ)
  let Pw : S → U64 → U64 → Prop := DelPw (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ)
    (IoWS (st := st) K.toKLayout Locks σ) (L.curW σ) (L.mem σ) (Locks σ)
  have wdW : ∀ b, IoWS (st := st) K.toKLayout Locks σ b → SR K c ρ b →
      IoWS (st := st) K.toKLayout Locks σ b ∧ b ∉ K.ptes ∧ VO K c ρ b := fun b h g => ⟨h, g.2, g.1.2⟩
  have eSt : core.num.U64.wrapping_add (L.curW σ) layout.tcb.STATE = core.num.U64.wrapping_add (L.curW σ) 3328#u64 := by
    rw [← Fl4Proofs.P1.stA_eq]; rfl
  have hPW : ∀ x q v, Pw x q v → Wd q := by
    rintro x q v (⟨-, -, h⟩ | ⟨rfl, -⟩ | ⟨hq', hT', hRd, hn, -, hl'⟩ | hu)
    · exact Or.inl h
    · have e := wdW _ PE.stw.2
      rw [Fl4Proofs.P1.stA_eq] at e
      rw [eSt]; exact Or.inl (e (srT 3328#u64 (by simp) (by simp) (by simp)))
    · have w := (PE.lockSlot hq' hl' (o := 0#u64) (by simp) (by simp)).2 (Or.inr ⟨hT', hn⟩)
      rw [wadd_zero (hL8 q hq').2] at w
      exact Or.inl (wdW _ w hRd.2)
    · exact Or.inr hu
  have hWal : ∀ b, Wd b → Aligned b := fun b h => h.elim (fun h => h.1.1) (fun h => h.1)
  have hPal : ∀ x q v, Pw x q v → Aligned q := fun x q v h => hWal q (hPW x q v h)
  -- the checked writes pass `StepOK`, keeping the invariant
  have hpA : fld (L.curW σ) oAFFINITY ∉ K.ptes := (srT 3520#u64 (by simp) (by simp) (by simp)).2
  have hμc : μ (fld (L.curW σ) oAFFINITY) = c := by
    have hpo : PO c hs (ownP K μ (fld (L.curW σ) oAFFINITY)) := by
      right; rw [ownP_eq_own nv hpA]; exact OwnMap.own_aff_gate hK0 htH μ
    rw [← hV.2.1 _ hpo]; exact hcur
  have affC : L.mem σ (fld (L.curW σ) oAFFINITY) = c := by
    have hu : fld (L.curW σ) oAFFINITY ∉ K.user := hL.nu_tcb hcT (k := 3520#u64) (by simp) (by simp)
    have ha : Aligned (fld (L.curW σ) oAFFINITY) := field_aligned ht' (by simp [OwnMap.oAFF_val])
      (by simp [OwnMap.oAFF_val])
    rw [hmm _ ha hu]
    exact CoreView.view_aff hK0 htH c ρ
  have aA : Aligned (fld (L.curW σ) oAFFINITY) := field_aligned ht' (by simp [OwnMap.oAFF_val])
    (by simp [OwnMap.oAFF_val])
  have aS : Aligned (fld (L.curW σ) oSTATE) := by rw [← OwnMap.stA_fld]; exact field_aligned ht' (by simp) (by simp)
  have dA : OwnMap.DecW K.toKLayout (fld (L.curW σ) oAFFINITY) := OwnMap.decW_tcb htH (Or.inl rfl)
  have dS : OwnMap.DecW K.toKLayout (fld (L.curW σ) oSTATE) := OwnMap.decW_tcb htH (Or.inr (Or.inl rfl))
  have nAS : fld (L.curW σ) oAFFINITY ≠ fld (L.curW σ) oSTATE :=
    OwnMap.fld_ne_off hK0 htH (Or.inl rfl) (Or.inr (Or.inl rfl)) (by simp [OwnMap.oAFF_val, OwnMap.oSTATE_val])
  have nSl : ∀ q, q ∈ K.slots → ∀ off, OwnMap.DecOff off → fld (L.curW σ) off ≠ q := fun q hq' off ho e => by
    have h1 := (hK0.tcb _ htH off ho.reg).1
    rw [e, hK0.slot _ hq'] at h1; exact OwnMap.Region.noConfusion h1
  have eS' : core.num.U64.wrapping_add (L.curW σ) layout.tcb.STATE = fld (L.curW σ) oSTATE := by
    rw [← OwnMap.stA_fld]; rfl
  let Inv : S → Prop := fun x => L.mem x (fld (L.curW σ) oAFFINITY) = c ∧
    ¬ OwnMap.QueuedState (L.mem x (fld (L.curW σ) oSTATE)) ∧
    ∀ q, q ∈ K.slots → ¬ TcbSlot K.toKLayout q → Rd q → NullOrFrame (L.mem σ q) → NullOrFrame (L.mem x q)
  have hStep : ∀ (x : S) (q v : U64) (x' : S), Inv x → Pw x q v → st.write x q v = ok x' →
      PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs (L.mem x)
        (L.mem x') ∧ Inv x' := by
    intro x q v x' hI' hP hw
    rw [L.write_eq] at hw
    have e := ok_inj_ff hw
    subst e
    have ha := hPal x q v hP
    obtain ⟨i1, i2, i3⟩ := hI'
    rcases hP with ⟨-, hnd, -⟩ | ⟨rfl, hv⟩ | ⟨hq', hT', hRd, hn, hv, -⟩ | hu
    · refine ⟨stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha hnd)),
        ?_, ?_, ?_⟩
      · rw [OwnMap.mem_wr_upd ha aA, Function.update_of_ne (fun h => hnd (by rw [← h]; exact dA))]; exact i1
      · rw [OwnMap.mem_wr_upd ha aS, Function.update_of_ne (fun h => hnd (by rw [← h]; exact dS))]; exact i2
      · intro q' hq' hT' hRd' hn'
        have dq : OwnMap.DecW K.toKLayout q' := Or.inr (Or.inl hq')
        rw [OwnMap.mem_wr_upd ha (hal q' hRd'), Function.update_of_ne (fun h => hnd (by rw [← h]; exact dq))]
        exact i3 q' hq' hT' hRd' hn'
    · rw [eS'] at ha ⊢
      refine ⟨stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_state hK0 hUO (m0 := μ) htH i1 hμc
        (fun hq' => absurd hq' i2) (fun hq' => absurd hq' (nq_run hv)))), ?_, ?_, ?_⟩
      · rw [OwnMap.mem_wr_upd ha aA, Function.update_of_ne nAS]; exact i1
      · rw [OwnMap.mem_wr_upd ha aS, Function.update_self]; exact nq_run hv
      · intro q' hq' hT' hRd' hn'
        rw [OwnMap.mem_wr_upd ha (hal q' hRd'), Function.update_of_ne (nSl q' hq' _ (Or.inr (Or.inl rfl))).symm]
        exact i3 q' hq' hT' hRd' hn'
    · refine ⟨stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base
        (OwnMap.stepOK_slot hK0 hUO (m0 := μ) hq' hT' (i3 q hq' hT' hRd hn) hv)), ?_, ?_, ?_⟩
      · rw [OwnMap.mem_wr_upd ha aA, Function.update_of_ne (nSl q hq' _ (Or.inl rfl))]; exact i1
      · rw [OwnMap.mem_wr_upd ha aS, Function.update_of_ne (nSl q hq' _ (Or.inr (Or.inl rfl)))]; exact i2
      · intro q' hq'' hT'' hRd' hn'
        rw [OwnMap.mem_wr_upd ha (hal q' hRd')]
        by_cases e : q' = q
        · subst e; rw [Function.update_self]; exact hv
        · rw [Function.update_of_ne e]; exact i3 q' hq'' hT'' hRd' hn'
    · have hnd : ¬ OwnMap.DecW K.toKLayout q := fun hd => (OwnMap.decW_ok hUO hd).2 hu.2
      refine ⟨stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha hnd)),
        ?_, ?_, ?_⟩
      · rw [OwnMap.mem_wr_upd ha aA, Function.update_of_ne (fun h => hnd (by rw [← h]; exact dA))]; exact i1
      · rw [OwnMap.mem_wr_upd ha aS, Function.update_of_ne (fun h => hnd (by rw [← h]; exact dS))]; exact i2
      · intro q' hq' hT' hRd' hn'
        have dq : OwnMap.DecW K.toKLayout q' := Or.inr (Or.inl hq')
        rw [OwnMap.mem_wr_upd ha (hal q' hRd'), Function.update_of_ne (fun h => hnd (by rw [← h]; exact dq))]
        exact i3 q' hq' hT' hRd' hn'
  -- ownership of the read and written words at the physical memory
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hWd : ∀ x, Wd x → Aligned x ∧ (¬ x ∈ K.user → HeldV c hs (ownP K μ x)) := by
    rintro x (⟨⟨ha, hw⟩, hp, hvo⟩ | hu)
    · refine ⟨ha, fun _ => ?_⟩
      have h1 : HeldV c hs (ownP K (L.mem σ) x) := by
        rw [ownP_eq_own nv hp, ← hc, ← hl]
        exact heldV_of_heldBy hw
      rw [eown, hvo] at h1
      rw [hV.1 x (Or.inl h1)]
      exact h1
    · exact ⟨hu.1, fun h => absurd hu.2 h⟩
  have hRPO : ∀ x, ¬ x ∈ K.user → Ro x → PO c hs (ownP K μ x) := by
    intro x hu hx
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      rw [ownP_eq_own nv hx.1.2, ← hc, ← hl]
      exact po_of_rperm (cmRS_nu hx.1.1 hu).2.2
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  -- the aligned user words
  have hfin : Set.Finite {x : U64 | Aligned x ∧ x ∈ K.user} := Set.toFinite _
  obtain ⟨ul, hul⟩ : ∃ l : List U64, ∀ x, x ∈ l ↔ Aligned x ∧ x ∈ K.user :=
    ⟨hfin.toFinset.toList, fun x => by simp⟩
  have slNU : ∀ q, q ∈ K.slots → Aligned q ∧ q ∉ K.user := fun q hq' => OwnMap.decW_ok hUO (Or.inr (Or.inl hq'))
  -- every state carrying `ρ` on the kernel reads runs as a view start with its user words
  have hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∃ r, interp (guard st (fun b => Rd b ∨ Ru b) Wd) ar (R.invBodyG number p) s a = ok r ∧
        WithinM st ar (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ)
          (· ∈ K.user) c hs (L.mem x) (L.mem y)) (R.invBodyG number p) s a ∧
        Once st ar Ro (· ∈ K.user) ∅ ∅ (R.invBodyG number p) s a := by
    intro s hcs' hks hag
    have hagR : ∀ b, Rd b → L.mem s b = L.mem σ b := fun b hb => (hag b hb).trans (kvR b hb).symm
    obtain ⟨σ', hσ'⟩ : ∃ x, x = E2E.wrs st (L.mem s) ul σ := ⟨_, rfl⟩
    obtain ⟨c1, c2, c3⟩ := E2E.wrs_const st (ν := L.mem s) (masksWr_plain st) ul σ
    have hM := E2E.wrs_mem st (ν := L.mem s) ul σ (fun x hx => ((hul x).mp hx).1)
    obtain ⟨hJ', hq', hqu', eL, eRS, eWS, eCur⟩ := wrsCM_facts (f := L.mem s) hCs hlk ul σ
      (fun x hx => (hul x).mp hx) hJ hq hqu
    rw [← hσ'] at c1 c2 c3 hM hJ' hq' hqu' eL eRS eWS eCur
    have hmm' : ∀ x, Aligned x → x ∉ K.user → L.mem σ' x = view K.toKLayout c ρ x := fun x hx hu => by
      rw [hM x hx, if_neg (fun h => hu ((hul x).mp h).2)]; exact hmm x hx hu
    obtain ⟨r', hg', hs'⟩ := inv_cm_gdA ar hA hK hU (number := number) (a := a) hJ' hq' hqu' (c1.trans hc) hmm'
    have eP : DelPw (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ') (IoWS (st := st) K.toKLayout Locks σ')
        (L.curW σ') (L.mem σ') (Locks σ') = Pw := by
      rw [eRS, eWS, eCur, eL]
      exact delPw_mem fun q hq' => by
        rw [hM q (slNU q hq').1, if_neg (fun h => (slNU q hq').2 ((hul q).mp h).2)]
    rw [eP, eRS] at hg'
    have hagU : ∀ b, RdU b → L.mem s b = L.mem σ' b := by
      rintro b (hb | hb)
      · rw [hagR b hb, hM b hb.1.1, if_neg (fun h => hb.1.2.1 ((hul b).mp h).2)]
      · rw [hM b hb.1, if_pos ((hul b).mpr hb)]
    have hmk' : st.frame_masks s = st.frame_masks σ' := by
      rw [PlainStore.frame_masks_eq, PlainStore.frame_masks_eq]
    obtain ⟨x0, s0', a0'⟩ := r'
    obtain ⟨s1', hs1⟩ := interp_agree_gd (st := st) (masksWr_plain st) hRal hPal (fun _ _ _ _ _ h => h)
      (R.invBodyG number p) (inv_noZero number p) σ' s a x0 s0' a0' (hks.trans c2.symm) (hcs'.trans c1.symm)
      hmk' hagU hg'
    have hgs := interp_gd_guard (R' := RdU) (W := Wd) (fun q h => h) hPW _ s a _ hs1
    -- `StepOK` per write
    have hI0 : Inv s := by
      have rA : Rd (fld (L.curW σ) oAFFINITY) :=
        ⟨PE.gate (Locks := Locks) (off := 3520#u64) PE.cT (by simp) (by simp) (by simp) (by simp [GateField]),
          srT 3520#u64 (by simp) (by simp) (by simp)⟩
      have rS : Rd (fld (L.curW σ) oSTATE) := by
        rw [← OwnMap.stA_fld]
        refine ⟨PE.stw.1, ?_⟩
        rw [Fl4Proofs.P1.stA_eq]; exact srT 3328#u64 (by simp) (by simp) (by simp)
      refine ⟨(hagR _ rA).trans affC, ?_, fun q hq' hT' hRd hn => by rw [hagR q hRd]; exact hn⟩
      rw [hagR _ rS, ← OwnMap.stA_fld]
      exact nq_run PE.run
    have hm := interp_gd (R := RdU) (P := Pw)
      (Q := fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs
        (L.mem x) (L.mem y)) (I := Inv) hStep _ s a _ hI0 hs1
    -- `Once`: the path's `ReadOnce` at `σ'`, carried to `s`, narrowed
    have hO1 : Once st ar (InvCMRS (st := st) K.toKLayout Locks σ') (· ∈ K.user) ∅ ∅ (R.invBodyG number p) σ' a :=
      (inv_pathCME (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number p
      (masksWr_plain st) hCs hlk K.toKLayout (view K.toKLayout c ρ) hK.base.base hU.base.base).once σ' σ' a _
      ⟨hJ', hq'⟩ (Alt.refl (L := L) σ') hs'
    have eCM : InvCMRS (st := st) K.toKLayout Locks σ' = InvCMRS (st := st) K.toKLayout Locks σ := by
      funext x; unfold InvCMRS; rw [eRS]
    have hO1' : Once st ar (InvCMRS (st := st) K.toKLayout Locks σ) (· ∈ K.user) ∅ ∅ (R.invBodyG number p) σ' a := by
      have h' := hO1
      rw [eCM] at h'
      exact h'
    have hgσ' := interp_gd_guard (R' := RdU) (W := Wd) (fun q h => h) hPW _ σ' a _ hg'
    have hO2 := once_agreeJ (masksWr_plain st) (Rd := InvCMRS (st := st) K.toKLayout Locks σ) (User := (· ∈ K.user))
      hRal hWal (R.invBodyG number p) (inv_noZero number p) σ' s a _ ∅ ∅ (hks.trans c2.symm) (hcs'.trans c1.symm)
      hmk' hagU hgσ' hO1'
    have hO3 := once_downR (R := Rd) (Ro := Ro) (R' := InvCMRS (st := st) K.toKLayout Locks σ) (U := Ru) (W := Wd)
      (User := (· ∈ K.user)) (fun q h => (hR0 q h).2) (fun q h => (hR0 q h).1) (fun q h => h.1.1) (fun q h => h.2)
      (R.invBodyG number p) (inv_noZero number p) ∅ ∅ s a _ hgs hO2
    exact ⟨_, hgs, (interp_mguard _ s a _ hm).2, hO3⟩
  have h := PathObl.safe_tr_wrU (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar (moveHeldP hK) (ownDepP hK hU) (masksWr_plain st) (a := a)
    (R.invBodyG number p) hc (Ro := Ro) (Rd := Rd) (Ru := Ru) (Wd := Wd) hal hR0 (fun b h => h.1)
    hWd hRPO (fun x hx => hV.2.1 x hx) hgo
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

end main

end
end Fl4Proofs.P2.E2EP
