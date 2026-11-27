/-
# P2 (line p3mc, gen 27): the CNodeDelete certificate at a view start

Handoff §31c. At a CNodeDelete (`invSlotU`) view start `σ` (a P3 bundle state of core `c`'s view of `ρ` with
`InvQF`, `QU`, the caller's message of length at least 2), U9's re-annotated body is `Safe`, by
`PathObl.safe_tr_wr` with

* `Rd := IoRS σ ∩ SR` (the run's reads the view keeps): the word classes the run reads (`GCl`, P2/InvRunV) are `SR` —
  node words of `c`, the current thread's words and registers (homed: `vx_cur_home`), capability-slot words
  (`nf_slot`), the current SC's words (homed through its `TCB` word), the two domain words (region `.none`), the
  earliest timer's deadline (armed: `sr_timer`), the release head's `SC` word and refill head (homed), the walk's
  page-table words off `K.ptes` (region `.none`);
* `Wd` := aligned, write-permitted at `σ`, off `K.ptes`, owner kept by the view; the checked writes `Pw` (independent
  of the state): aligned non-deciding `Wd` words, the caller's `STATE` with `RESTART` / `RUNNING`, and a locked
  non-TCB slot's `CAP0` of an `Rd` slot holding Null / Frame at `σ` with a Null / Frame value;
* at `σ` the run on `gd st Rd Pw` is the real one (`inv_run_gdV`, P2/InvDelGd), and the tree's (`inv_isProgOnR`);
  `interp_agree_gd` moves it to any state carrying `ρ` on `Rd`; `interp_gd` with the invariant "the caller's
  `AFFINITY` is `c`, its `STATE` is not queued, the `Rd` slots holding Null / Frame at `σ` still do" gives `StepOK`
  per write (`stepOK_nondec`, `stepOK_state`, `stepOK_slot`, lifted to `ownP`).

**`inv_del_annV`**. `InvLen` is a hypothesis (the exemption carries it, P2/E2EPU25). No named premise. New module.
-/
import Fl4Proofs.P2.InvDelGd
import Fl4Proofs.P2.IrqWhAnn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE oSTATE InW GateField TimerField GField
  tcbOwner TcbSlot NullOrFrame)
open Fl4Proofs.P2.E2E (SP tr masksOf)
open Fl4Proofs.P2.Serial (Owner VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN NotForeign vn_of_nf nf_node nf_slot nf_none nf_tcb TZero)

noncomputable section
open Classical

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 16000000 in
/-- **U9's armed CNodeDelete program is `Safe` at a view start whose message has length at least 2** (module
docstring). -/
theorem inv_del_annV (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {number : I64} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (hq : InvQF st Cs Ω Sg Ac Locks p K.toKLayout (view K.toKLayout c ρ) σ) (hqu : QU st K σ)
    (hc : L.cpu σ = c) (hl : Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hlen : InvLen st σ) :
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
  -- the read set
  let Rd : U64 → Prop := fun b => IoRS (st := st) K.toKLayout Locks σ b ∧ SR K c ρ b
  have hR : ∀ b, IoRS (st := st) K.toKLayout Locks σ b → b ∉ K.ptes → G b → Rd b := fun b h _ g => ⟨h, g⟩
  let Ro : U64 → Prop := fun q => (InvCMRS (st := st) K.toKLayout Locks σ q ∧ ¬ q ∈ K.ptes) ∧ VO K c ρ q
  have hR0 : ∀ q, Rd q → Ro q ∧ ¬ q ∈ K.user := fun q hq' =>
    ⟨⟨⟨ioRS_cm hq'.1, hq'.2.2⟩, hq'.2.1.2⟩, hq'.1.2.1⟩
  have hal : ∀ b, Rd b → Aligned b := fun b hb => hb.1.1
  have kvR : ∀ b, Rd b → L.mem σ b = ρ b := fun b hb =>
    (hmm b hb.1.1 hb.1.2.1).trans hb.2.1.1
  -- the write sets
  let Wd : U64 → Prop := fun b => Aligned b ∧ WPerm (OwnMap.own K.toKLayout) (L.cpu σ) (Locks σ) (L.mem σ) b ∧
    b ∉ K.ptes ∧ VO K c ρ b
  let Pw : S → U64 → U64 → Prop := fun _ q v =>
    (Aligned q ∧ ¬ OwnMap.DecW K.toKLayout q ∧ Wd q) ∨
    (q = core.num.U64.wrapping_add (L.curW σ) layout.tcb.STATE ∧ (v = sched.TS_RESTART ∨ v = sched.TS_RUNNING)) ∨
    (q ∈ K.slots ∧ ¬ TcbSlot K.toKLayout q ∧ Rd q ∧ NullOrFrame (L.mem σ q) ∧ NullOrFrame v ∧ Locks σ q)
  have wdW : ∀ b, IoWS (st := st) K.toKLayout Locks σ b → SR K c ρ b → Wd b := fun b h g => ⟨h.1, h.2, g.2, g.1.2⟩
  have eSt : core.num.U64.wrapping_add (L.curW σ) layout.tcb.STATE = core.num.U64.wrapping_add (L.curW σ) 3328#u64 := by
    rw [← Fl4Proofs.P1.stA_eq]; rfl
  have hPW : ∀ x q v, Pw x q v → Wd q := by
    rintro x q v (⟨-, -, h⟩ | ⟨rfl, -⟩ | ⟨hq', hT', hRd, hn, -, hl'⟩)
    · exact h
    · have e := wdW _ PE.stw.2
      rw [Fl4Proofs.P1.stA_eq] at e
      rw [eSt]; exact e (srT 3328#u64 (by simp) (by simp) (by simp))
    · have w := (PE.lockSlot hq' hl' (o := 0#u64) (by simp) (by simp)).2 (Or.inr ⟨hT', hn⟩)
      rw [wadd_zero (hL8 q hq').2] at w
      exact wdW _ w hRd.2
  have hPal : ∀ x q v, Pw x q v → Aligned q := fun x q v h => (hPW x q v h).1
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
      ∀ x, Pw x q 0#u64 := by
    intro q hq' hl' hT' hn x
    have r := (PE.lockSlot hq' hl' (o := 0#u64) (by simp) (by simp)).1
    rw [wadd_zero (hL8 q hq').2] at r
    exact Or.inr (Or.inr ⟨hq', hT', ⟨r, srW _ (sW0 q hq')⟩, hn, OwnMap.nof_zero, hl'⟩)
  have hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      ∀ x, Pw x (core.num.U64.wrapping_add (L.curW σ) layout.tcb.STATE) v :=
    fun v hv _ => Or.inr (Or.inl ⟨rfl, hv⟩)
  -- the run at `σ` on the checked store, and its tree
  obtain ⟨r, hr0⟩ := inv_total (st := st) hA number p σ a
  have hgσ0 := inv_run_gdV hA hK hU ⟨hJ, hq⟩ hQ.ks hqu.2 hlen Gc hR srW
    (fun b hb hp => ⟨vn_of_nf hK (nf_none hb.2.1), hp⟩) hWr hwS hw0 hst hr0
  have hSC : InvSlotCN st K.toKLayout p
      (fun s => (SlJAt (L := L) K.toKLayout s ∧
        InvQF st Cs Ω Sg Ac Locks p K.toKLayout (view K.toKLayout c ρ) s) ∧ QU st K s) :=
    fun s h => invSlotCNK_of (Q := InvQF st Cs Ω Sg Ac Locks p) (fun _ _ _ _ hq => hq) K.toKLayout
      (view K.toKLayout c ρ) s h.1
  have hpR := inv_isProgOnR (Locks := Locks) (m0 := view K.toKLayout c ρ) hA
    (P := fun s => (SlJAt (L := L) K.toKLayout s ∧
      InvQF st Cs Ω Sg Ac Locks p K.toKLayout (view K.toKLayout c ρ) s) ∧ QU st K s)
    (fun _ h => h.1.2.1.1.1) hSC (inv_isProg S number p)
  have hgσ : interp (gd st Rd Pw) ar (R.invBodyG number p) σ a = ok r :=
    (hpR (gd st Rd Pw) (Narrow.gd _ _ _) σ ⟨σ, ⟨⟨hJ, hq⟩, hqu⟩, Alt.refl σ⟩ a).symm.trans hgσ0
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
    rcases hP with ⟨-, hnd, -⟩ | ⟨rfl, hv⟩ | ⟨hq', hT', hRd, hn, hv, -⟩
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
  -- ownership of the read and written words at the physical memory
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hWd : ∀ x, Wd x → Aligned x ∧ (¬ x ∈ K.user → HeldV c hs (ownP K μ x)) := by
    intro x hx
    obtain ⟨ha, hw, hp, hvo⟩ := hx
    refine ⟨ha, fun _ => ?_⟩
    have h1 : HeldV c hs (ownP K (L.mem σ) x) := by
      rw [ownP_eq_own nv hp, ← hc, ← hl]
      exact heldV_of_heldBy hw
    rw [eown, hvo] at h1
    rw [hV.1 x (Or.inl h1)]
    exact h1
  have hRPO : ∀ x, ¬ x ∈ K.user → Ro x → PO c hs (ownP K μ x) := by
    intro x hu hx
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      rw [ownP_eq_own nv hx.1.2, ← hc, ← hl]
      exact po_of_rperm (cmRS_nu hx.1.1 hu).2.2
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  -- every state carrying `ρ` on the reads runs as the view start
  have hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∃ r, interp (guard st Rd Wd) ar (R.invBodyG number p) s a = ok r ∧
        WithinM st ar (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ)
          (· ∈ K.user) c hs (L.mem x) (L.mem y)) (R.invBodyG number p) s a := by
    intro s hcs' hks hag
    have hagR : ∀ b, Rd b → L.mem s b = L.mem σ b := fun b hb => (hag b hb).trans (kvR b hb).symm
    obtain ⟨x0, s0', a0'⟩ := r
    obtain ⟨s1', hs1⟩ := interp_agree_gd (st := st) (masksWr_plain st) hal hPal (fun _ _ _ _ _ h => h)
      (R.invBodyG number p) (inv_noZero number p) σ s a x0 s0' a0' hks hcs'
      (by rw [PlainStore.frame_masks_eq, PlainStore.frame_masks_eq]) hagR hgσ
    refine ⟨_, interp_gd_guard (R' := Rd) (W := Wd) (fun q h => h) hPW _ s a _ hs1, ?_⟩
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
    have hm := interp_gd (R := Rd) (P := Pw)
      (Q := fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs
        (L.mem x) (L.mem y)) (I := Inv) hStep _ s a _ hI0 hs1
    exact (interp_mguard _ s a _ hm).2
  have h := PathObl.safe_tr_wr (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar (moveHeldP hK) (ownDepP hK hU) (masksWr_plain st) (a := a)
    (R.invBodyG number p) (inv_noZero number p) hc (Ro := Ro) (Rd := Rd) (Wd := Wd) hal hR0
    hWd hRPO (fun x hx => hV.2.1 x hx) hgo
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

end main

end
end Fl4Proofs.P2.E2EP
