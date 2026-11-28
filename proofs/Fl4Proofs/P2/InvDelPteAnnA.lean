/-
# P2 (line p3mc, gen 29): the PTE-arm CNodeDelete certificate at every view start

Handoff §33d item 1. U9's re-annotated PTE-arm (`delPteSlot`) program is `Safe` at **every** PTE-delete view start,
by `PathObl.safe_tr_wrU` as gen 28's `inv_del_annA` (P2/InvDelAnnA). The body is the path's own (`delPtePath`,
read set `InvRSP`, not cut by the PTEs); `SR` excludes the leaf entries, so the plan's **locked** leaf words are
added to the agreement set explicitly (`PteRd`):

* `PteRd K lk b` (`b ∈ K.ptes`, locked); `DelRdP` = gen 28's `IoRS ∩ SR`, the locked leaves and the aligned user
  words; `DelWdP` / `DelPwP` = gen 28's `DelWd` / `DelPw` and the locked leaves (any value);
* a locked leaf is region `.none` (`RegionOKP.none`), so the view keeps its value (`nf_none` → `vn_of_nf`); its owner
  is `lock b` for every memory (`ownP_pte`, so `VO`), held (the start's locks); its write decides no owner
  (`pte_nondec`), so `StepOK` is `stepOK_nondec`'s, lifted to `ownP`, and the invariant (caller's `AFFINITY`,
  `STATE`, the read Null / Frame slots) is untouched;
* **`wrsP_facts`**: aligned user-word writes keep `PreP`, `QU`, the locks, `IoRS`, `IoWS` and the current thread
  (`invUfPP`, `SlJAt.ioRWDS_wrSt`, `qU_wr`, `SlJAt.curW_wr`; the locks by `hlk`, the start record's
  `DelPtePrem.lk` [P]);
* **`inv_pte_gdA`**: at a view start the run on `gd st DelRdP DelPwP` is the real one (`inv_run_gdP`,
  P2/InvDelPteGd), and the tree's (`inv_isProgOnP`);
* **`inv_pte_annA`**: the certificate (`safe_tr_wrU`; `Once` from the path's `ReadOnce` `invRoPP` at the user-word
  variant `σ'`, carried by `once_agreeJ`, narrowed by `once_downR`).

No named premise (`hCs`, `hlk` are the start record's `DelPtePrem.hCs` / `DelPtePrem.lk` [P]). New module; no
existing statement changes.

**Gen 51 (line p3mc), in-place split, every existing statement byte-identical up to `:=`**: `inv_pte_annA` (16M) is
re-proved from pieces of ≤ 4M heartbeats — **`pte_stepOK`** (the checked writes are in `DelWdP`, pass `StepOK`, keep
P2/InvDelAnnA's `DelStInv`) and **`pte_hgoX`** (the run oracle, plus the user-word variant `σ'` of the start: `PreP`,
`QU`, agreeing with the oracle state on the read set, kernel base, core and masks, its run inside `DelRdP` /
`DelWdP`). P2/InsV15Del uses `pte_hgoX` for the `InsA` twin.
-/
import Fl4Proofs.P2.InvDelAnnA
import Fl4Proofs.P2.InvDelPteGd
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

/-! ## The sets -/

/-- The locked leaf entries. -/
def PteRd (K : KLayoutP) (lk : U64 → Prop) (b : U64) : Prop := b ∈ K.ptes ∧ lk b

/-- The read set: gen 28's `RS ∩ SR`, the locked leaves, and the aligned user words. -/
def DelRdP (K : KLayoutP) (c : U64) (ρ : U64 → U64) (RS : U64 → Prop) (lk : U64 → Prop) (b : U64) : Prop :=
  ((RS b ∧ SR K c ρ b) ∨ PteRd K lk b) ∨ PathObl.UserW K.toKLayout b

/-- The write set: gen 28's `DelWd` and the locked leaves. -/
def DelWdP (K : KLayoutP) (c : U64) (ρ : U64 → U64) (WS : U64 → Prop) (lk : U64 → Prop) (b : U64) : Prop :=
  DelWd K c ρ WS b ∨ PteRd K lk b

/-- The checked writes (state-independent): gen 28's `DelPw` and the locked leaves with any value. -/
def DelPwP {S : Type} (K : KLayoutP) (c : U64) (ρ : U64 → U64) (RS WS : U64 → Prop) (t : U64) (m : U64 → U64)
    (lk : U64 → Prop) : S → U64 → U64 → Prop := fun x q v =>
  DelPw (S := S) K c ρ RS WS t m lk x q v ∨ PteRd K lk q

theorem delPwP_mem {S : Type} {K : KLayoutP} {c : U64} {ρ : U64 → U64} {RS WS : U64 → Prop} {t : U64}
    {m m' : U64 → U64} {lk : U64 → Prop} (h : ∀ q ∈ K.slots, m q = m' q) :
    DelPwP (S := S) K c ρ RS WS t m lk = DelPwP (S := S) K c ρ RS WS t m' lk := by
  unfold DelPwP
  rw [delPw_mem h]

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)

/-- **Aligned user-word writes keep the PTE-delete view start's facts** (module docstring). -/
theorem wrsP_facts {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP}
    {m f : U64 → U64} (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ (K' : OwnMap.KLayout) (s : S) (b v : U64), SlJAt (L := L) K' s → b ∈ K'.user → Aligned b →
      Locks (L.wr s b v) = Locks s) :
    ∀ (l : List U64) (s : S), (∀ x ∈ l, Aligned x ∧ x ∈ K.user) →
      PreP st Cs Ω Sg Ac Locks p K m s → QU st K s →
      PreP st Cs Ω Sg Ac Locks p K m (E2E.wrs st f l s) ∧ QU st K (E2E.wrs st f l s) ∧
      Locks (E2E.wrs st f l s) = Locks s ∧
      IoRS (st := st) K.toKLayout Locks (E2E.wrs st f l s) = IoRS (st := st) K.toKLayout Locks s ∧
      IoWS (st := st) K.toKLayout Locks (E2E.wrs st f l s) = IoWS (st := st) K.toKLayout Locks s ∧
      L.curW (E2E.wrs st f l s) = L.curW s := by
  intro l
  induction l with
  | nil => intro s _ h1 h3; exact ⟨h1, h3, rfl, rfl, rfl, rfl⟩
  | cons x l ih =>
    intro s hl h1 h3
    obtain ⟨ha, hu⟩ := hl x (List.mem_cons_self ..)
    obtain ⟨g1, g3, -, -, -⟩ := invUfPP hCs hlk s x (f x) h1 hu ha
    obtain ⟨g4, g5, -⟩ := h1.1.ioRWDS_wrSt hu ha (f x) g3
    have g6 : QU st K (L.wr s x (f x)) := qU_wr h3 hu ha
    have g7 := h1.1.curW_wr hu ha (f x)
    obtain ⟨k1, k3, k4, k5, k6, k7⟩ := ih _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) g1 g6
    exact ⟨k1, k3, k4.trans g3, k5.trans g4, k6.trans g5, k7.trans g7⟩

set_option maxHeartbeats 16000000 in
/-- **At a PTE-delete view start the run on `gd st DelRdP DelPwP` is the real one** (module docstring). -/
theorem inv_pte_gdA (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {ρ : U64 → U64}
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {number : I64} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (hq : InvQFP st Cs Ω Sg Ac Locks p K.toKLayout (view K.toKLayout c ρ) σ) (hqu : QU st K σ)
    (hc : L.cpu σ = c)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    ∃ r, interp (gd st (DelRdP K c ρ (IoRS (st := st) K.toKLayout Locks σ) (Locks σ))
        (DelPwP (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ) (IoWS (st := st) K.toKLayout Locks σ)
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
  let Rd : U64 → Prop := DelRdP K c ρ (IoRS (st := st) K.toKLayout Locks σ) (Locks σ)
  have hR : ∀ b, IoRS (st := st) K.toKLayout Locks σ b → b ∉ K.ptes → G b → Rd b :=
    fun b h _ g => Or.inl (Or.inl ⟨h, g⟩)
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
      ∀ x, Pw x q 0#u64 := by
    intro q hq' hl' hT' hn x
    have r := (PE.lockSlot hq' hl' (o := 0#u64) (by simp) (by simp)).1
    rw [wadd_zero (hL8 q hq').2] at r
    exact Or.inr (Or.inr (Or.inl ⟨hq', hT', ⟨r, srW _ (sW0 q hq')⟩, hn, OwnMap.nof_zero, hl'⟩))
  have hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      ∀ x, Pw x (core.num.U64.wrapping_add (L.curW σ) layout.tcb.STATE) v :=
    fun v hv _ => Or.inr (Or.inl ⟨rfl, hv⟩)
  have hWu : ∀ b, PathObl.UserW K.toKLayout b → WAll Pw b := fun b h _ _ => Or.inr (Or.inr (Or.inr h))
  -- the PTE arm's checked writes
  let Pw' : S → U64 → U64 → Prop := DelPwP (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ)
    (IoWS (st := st) K.toKLayout Locks σ) (L.curW σ) (L.mem σ) (Locks σ)
  have hWr' : IoWr st (WAll Pw') K.toKLayout.heap.scBits σ := hWr.mono (fun b h x v => Or.inl (h x v))
  have hwS' : ∀ q o, q ∈ K.slots → Locks σ q → o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val →
      (16 ≤ o.val ∨ (¬ TcbSlot K.toKLayout q ∧ NullOrFrame (L.mem σ q))) →
        WAll Pw' (core.num.U64.wrapping_add q o) :=
    fun q o h1 h2 h3 h4 h5 h6 x v => Or.inl (hwS q o h1 h2 h3 h4 h5 h6 x v)
  have hw0' : ∀ q, q ∈ K.slots → Locks σ q → ¬ TcbSlot K.toKLayout q → NullOrFrame (L.mem σ q) →
      ∀ x, Pw' x q 0#u64 := fun q h1 h2 h3 h4 x => Or.inl (hw0 q h1 h2 h3 h4 x)
  have hst' : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      ∀ x, Pw' x (core.num.U64.wrapping_add (L.curW σ) layout.tcb.STATE) v :=
    fun v hv x => Or.inl (hst v hv x)
  have hWu' : ∀ b, PathObl.UserW K.toKLayout b → WAll Pw' b := fun b h x v => Or.inl (hWu b h x v)
  have hWe : ∀ b, b ∈ K.ptes → Locks σ b → WAll Pw' b := fun b hb hl _ _ => Or.inr ⟨hb, hl⟩
  -- the run at `σ` on the checked store, and its tree
  obtain ⟨r, hr0⟩ := inv_total (st := st) hA number p σ a
  have hgσ0 := inv_run_gdP hA hK hU nv ⟨hJ, hq⟩ hQ.ks hqu.2 Gc hR srW
    (fun b hb hp => ⟨vn_of_nf hK (nf_none hb.2.1), hp⟩) hWr' hwS' hw0' hst' (fun b h => Or.inr h) hWu'
    (fun b hb hl => Or.inl (Or.inr ⟨hb, hl⟩)) hWe hr0
  have hpR := inv_isProgOnP (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks)
    (number := number) (p := p) (m := view K.toKLayout c ρ) hA hK
  have hPre : PreP st Cs Ω Sg Ac Locks p K (view K.toKLayout c ρ) σ := ⟨hJ, hq, hqu.2⟩
  exact ⟨r, (hpR (gd st Rd Pw') (Narrow.gd _ _ _) σ ⟨σ, hPre, Alt.refl σ⟩ a).symm.trans hgσ0,
    (hpR st (Narrow.self st) σ ⟨σ, hPre, Alt.refl σ⟩ a).symm.trans hr0⟩

set_option maxHeartbeats 4000000 in
/-- (gen 51, split out of `inv_pte_annA` in place) **The PTE-delete run's checked writes are in its write set, pass
`StepOK` and keep `DelStInv`** (P2/InvDelAnnA). -/
theorem pte_stepOK {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (hq : InvQFP st Cs Ω Sg Ac Locks p K.toKLayout (view K.toKLayout c ρ) σ)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    (∀ x q v, DelPwP (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ) (IoWS (st := st) K.toKLayout Locks σ)
        (L.curW σ) (L.mem σ) (Locks σ) x q v → DelWdP K c ρ (IoWS (st := st) K.toKLayout Locks σ) (Locks σ) q) ∧
    ∀ (x : S) (q v : U64) (x' : S), DelStInv (st := st) K c ρ Locks σ x →
      DelPwP (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ) (IoWS (st := st) K.toKLayout Locks σ)
        (L.curW σ) (L.mem σ) (Locks σ) x q v → st.write x q v = ok x' →
      PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs (L.mem x)
        (L.mem x') ∧ DelStInv (st := st) K c ρ Locks σ x' := by
  have hX := hJ.regionOKX
  have hK0 := hJ.regionOK
  have hUO := hJ.userOK
  obtain ⟨Ac', B⟩ := bunIx_of hJ
  have hI := B.bxi
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced K.toKLayout.heap.tcbs := h0.tcbs
  have hcT : L.curW σ ∈ K.toKLayout.heap.tcbs := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have ht' := hT _ hcT
  have hcur : ρ (fld (L.curW σ) oAFFINITY) = c := vx_cur_home hJ hmm
  have PE := hq.1.1.1
  have hL8 : Slot8 K.toKLayout := fun q hq => PE.lay.slot8 q hq
  have srT : ∀ k : U64, 192 ≤ k.val → k.val < 4096 → k.val % 8 = 0 →
      SR K c ρ (core.num.U64.wrapping_add (L.curW σ) k) := fun k h1 h2 h3 =>
    sr_tcb hK hX htH hcur (o := k) h1 h2 h3
  have kPte : ∀ b, b ∈ K.ptes → Aligned b ∧ b ∉ K.user := fun b hb => hU.kern b hb
  -- the write sets
  let Wd : U64 → Prop := DelWdP K c ρ (IoWS (st := st) K.toKLayout Locks σ) (Locks σ)
  let Pw0 : S → U64 → U64 → Prop := DelPw (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ)
    (IoWS (st := st) K.toKLayout Locks σ) (L.curW σ) (L.mem σ) (Locks σ)
  let Pw : S → U64 → U64 → Prop := DelPwP (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ)
    (IoWS (st := st) K.toKLayout Locks σ) (L.curW σ) (L.mem σ) (Locks σ)
  have wdW : ∀ b, IoWS (st := st) K.toKLayout Locks σ b → SR K c ρ b →
      IoWS (st := st) K.toKLayout Locks σ b ∧ b ∉ K.ptes ∧ VO K c ρ b := fun b h g => ⟨h, g.2, g.1.2⟩
  have eSt : core.num.U64.wrapping_add (L.curW σ) layout.tcb.STATE = core.num.U64.wrapping_add (L.curW σ) 3328#u64 := by
    rw [← Fl4Proofs.P1.stA_eq]; rfl
  have hPW0 : ∀ x q v, Pw0 x q v → DelWd K c ρ (IoWS (st := st) K.toKLayout Locks σ) q := by
    rintro x q v (⟨-, -, h⟩ | ⟨rfl, -⟩ | ⟨hq', hT', hRd, hn, -, hl'⟩ | hu)
    · exact Or.inl h
    · have e := wdW _ PE.stw.2
      rw [Fl4Proofs.P1.stA_eq] at e
      rw [eSt]; exact Or.inl (e (srT 3328#u64 (by simp) (by simp) (by simp)))
    · have w := (PE.lockSlot hq' hl' (o := 0#u64) (by simp) (by simp)).2 (Or.inr ⟨hT', hn⟩)
      rw [wadd_zero (hL8 q hq').2] at w
      exact Or.inl (wdW _ w hRd.2)
    · exact Or.inr hu
  have hPW : ∀ x q v, Pw x q v → Wd q := by
    rintro x q v (h | h)
    · exact Or.inl (hPW0 x q v h)
    · exact Or.inr h
  have hWal : ∀ b, Wd b → Aligned b := by
    rintro b ((h | h) | h)
    · exact h.1.1
    · exact h.1
    · exact (kPte b h.1).1
  have hPal : ∀ x q v, Pw x q v → Aligned q := fun x q v h => hWal q (hPW x q v h)
  -- the checked writes pass `StepOK`, keeping the invariant
  have hpA : fld (L.curW σ) oAFFINITY ∉ K.ptes := (srT 3520#u64 (by simp) (by simp) (by simp)).2
  have hμc : μ (fld (L.curW σ) oAFFINITY) = c := by
    have hpo : PO c hs (ownP K μ (fld (L.curW σ) oAFFINITY)) := by
      right; rw [ownP_eq_own nv hpA]; exact OwnMap.own_aff_gate hK0 htH μ
    rw [← hV.2.1 _ hpo]; exact hcur
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
  let Inv : S → Prop := DelStInv (st := st) K c ρ Locks σ
  have hStep : ∀ (x : S) (q v : U64) (x' : S), Inv x → Pw x q v → st.write x q v = ok x' →
      PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs (L.mem x)
        (L.mem x') ∧ Inv x' := by
    intro x q v x' hI' hP hw
    rw [L.write_eq] at hw
    have e := ok_inj_ff hw
    subst e
    have ha := hPal x q v hP
    obtain ⟨i1, i2, i3⟩ := hI'
    rcases hP with (⟨-, hnd, -⟩ | ⟨rfl, hv⟩ | ⟨hq', hT', hRd, hn, hv, -⟩ | hu) | ⟨hp, -⟩
    · refine ⟨stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha hnd)),
        ?_, ?_, ?_⟩
      · rw [OwnMap.mem_wr_upd ha aA, Function.update_of_ne (fun h => hnd (by rw [← h]; exact dA))]; exact i1
      · rw [OwnMap.mem_wr_upd ha aS, Function.update_of_ne (fun h => hnd (by rw [← h]; exact dS))]; exact i2
      · intro q' hq' hT' hRd' hn'
        have dq : OwnMap.DecW K.toKLayout q' := Or.inr (Or.inl hq')
        rw [OwnMap.mem_wr_upd ha (hRd'.1.1), Function.update_of_ne (fun h => hnd (by rw [← h]; exact dq))]
        exact i3 q' hq' hT' hRd' hn'
    · rw [eS'] at ha ⊢
      refine ⟨stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_state hK0 hUO (m0 := μ) htH i1 hμc
        (fun hq' => absurd hq' i2) (fun hq' => absurd hq' (nq_run hv)))), ?_, ?_, ?_⟩
      · rw [OwnMap.mem_wr_upd ha aA, Function.update_of_ne nAS]; exact i1
      · rw [OwnMap.mem_wr_upd ha aS, Function.update_self]; exact nq_run hv
      · intro q' hq' hT' hRd' hn'
        rw [OwnMap.mem_wr_upd ha (hRd'.1.1), Function.update_of_ne (nSl q' hq' _ (Or.inr (Or.inl rfl))).symm]
        exact i3 q' hq' hT' hRd' hn'
    · refine ⟨stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base
        (OwnMap.stepOK_slot hK0 hUO (m0 := μ) hq' hT' (i3 q hq' hT' hRd hn) hv)), ?_, ?_, ?_⟩
      · rw [OwnMap.mem_wr_upd ha aA, Function.update_of_ne (nSl q hq' _ (Or.inl rfl))]; exact i1
      · rw [OwnMap.mem_wr_upd ha aS, Function.update_of_ne (nSl q hq' _ (Or.inr (Or.inl rfl)))]; exact i2
      · intro q' hq'' hT'' hRd' hn'
        rw [OwnMap.mem_wr_upd ha (hRd'.1.1)]
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
        rw [OwnMap.mem_wr_upd ha (hRd'.1.1), Function.update_of_ne (fun h => hnd (by rw [← h]; exact dq))]
        exact i3 q' hq' hT' hRd' hn'
    · have hnd : ¬ OwnMap.DecW K.toKLayout q := pte_nondec hK hp
      refine ⟨stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha hnd)),
        ?_, ?_, ?_⟩
      · rw [OwnMap.mem_wr_upd ha aA, Function.update_of_ne (fun h => hnd (by rw [← h]; exact dA))]; exact i1
      · rw [OwnMap.mem_wr_upd ha aS, Function.update_of_ne (fun h => hnd (by rw [← h]; exact dS))]; exact i2
      · intro q' hq' hT' hRd' hn'
        have dq : OwnMap.DecW K.toKLayout q' := Or.inr (Or.inl hq')
        rw [OwnMap.mem_wr_upd ha (hRd'.1.1), Function.update_of_ne (fun h => hnd (by rw [← h]; exact dq))]
        exact i3 q' hq' hT' hRd' hn'
  exact ⟨hPW, hStep⟩

set_option maxHeartbeats 4000000 in
/-- (gen 51, split out of `inv_pte_annA` in place) **`inv_pte_annA`'s run oracle, with the user-word variant of the
start it runs at** (as `del_hgoX`): the original's three facts, and `σ'` = `σ` with `s`'s user words is again a view
start (`PreP`, `QU`), agreeing with `s` on the read set, the kernel base, the core and the masks, its run inside
`DelRdP` / `DelWdP`. -/
theorem pte_hgoX (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {number : I64} {σ : S} {a : A}
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ (K' : OwnMap.KLayout) (s : S) (b v : U64), SlJAt (L := L) K' s → b ∈ K'.user → Aligned b →
      Locks (L.wr s b v) = Locks s)
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (hq : InvQFP st Cs Ω Sg Ac Locks p K.toKLayout (view K.toKLayout c ρ) σ) (hqu : QU st K σ)
    (hc : L.cpu σ = c)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ →
      (∀ b, ((IoRS (st := st) K.toKLayout Locks σ b ∧ SR K c ρ b) ∨ PteRd K (Locks σ) b) → L.mem s b = ρ b) →
      ∃ r, interp (guard st (fun b => ((IoRS (st := st) K.toKLayout Locks σ b ∧ SR K c ρ b) ∨ PteRd K (Locks σ) b) ∨
          PathObl.UserW K.toKLayout b) (DelWdP K c ρ (IoWS (st := st) K.toKLayout Locks σ) (Locks σ))) ar
          (R.invBodyG number p) s a = ok r ∧
        WithinM st ar (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ)
          (· ∈ K.user) c hs (L.mem x) (L.mem y)) (R.invBodyG number p) s a ∧
        Once st ar (fun q => InvRSP st K Locks σ q ∧ VO K c ρ q) (· ∈ K.user) ∅ ∅ (R.invBodyG number p) s a ∧
        ∃ σ' : S, PreP st Cs Ω Sg Ac Locks p K (view K.toKLayout c ρ) σ' ∧ QU st K σ' ∧
          (∀ x, Aligned x → x ∉ K.user → L.mem σ' x = view K.toKLayout c ρ x) ∧
          L.ksb s = L.ksb σ' ∧ L.cpu s = L.cpu σ' ∧ st.frame_masks s = st.frame_masks σ' ∧
          (∀ b, DelRdP K c ρ (IoRS (st := st) K.toKLayout Locks σ) (Locks σ) b → L.mem s b = L.mem σ' b) ∧
          Within st ar (DelRdP K c ρ (IoRS (st := st) K.toKLayout Locks σ) (Locks σ))
            (DelWdP K c ρ (IoWS (st := st) K.toKLayout Locks σ) (Locks σ)) (R.invBodyG number p) σ' a := by
  have hX := hJ.regionOKX
  have hK0 := hJ.regionOK
  have hUO := hJ.userOK
  obtain ⟨Ac', B⟩ := bunIx_of hJ
  have hI := B.bxi
  have hL := B.stLay
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced K.toKLayout.heap.tcbs := h0.tcbs
  have hcT : L.curW σ ∈ K.toKLayout.heap.tcbs := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have ht' := hT _ hcT
  have hcur : ρ (fld (L.curW σ) oAFFINITY) = c := vx_cur_home hJ hmm
  have PE := hq.1.1.1
  have srT : ∀ k : U64, 192 ≤ k.val → k.val < 4096 → k.val % 8 = 0 →
      SR K c ρ (core.num.U64.wrapping_add (L.curW σ) k) := fun k h1 h2 h3 =>
    sr_tcb hK hX htH hcur (o := k) h1 h2 h3
  obtain ⟨hPW, hStep⟩ := pte_stepOK (Locks := Locks) hK hU nv hV hJ hq hmm
  -- the read sets
  have kPte : ∀ b, b ∈ K.ptes → Aligned b ∧ b ∉ K.user := fun b hb => hU.kern b hb
  have vPte : ∀ b, b ∈ K.ptes → VN K c ρ b := fun b hb => vn_of_nf hK (nf_none (hK.none b hb))
  have oPte : ∀ b, b ∈ K.ptes → VO K c ρ b := fun b hb => by unfold VO; rw [ownP_pte hb, ownP_pte hb]
  let Rd : U64 → Prop := fun b => (IoRS (st := st) K.toKLayout Locks σ b ∧ SR K c ρ b) ∨ PteRd K (Locks σ) b
  let Ro : U64 → Prop := fun q => InvRSP st K Locks σ q ∧ VO K c ρ q
  have hR0 : ∀ q, Rd q → Ro q ∧ ¬ q ∈ K.user := by
    rintro q (⟨h1, h2⟩ | ⟨hp, hl'⟩)
    · exact ⟨⟨⟨h1.1, Or.inr ⟨h1, fun hp => absurd hp h2.2⟩⟩, h2.1.2⟩, h1.2.1⟩
    · exact ⟨⟨⟨(kPte q hp).1, Or.inr ⟨VsW.ioRS ⟨(kPte q hp).1, hK.none q hp, (kPte q hp).2⟩, fun _ => hl'⟩⟩,
        oPte q hp⟩, (kPte q hp).2⟩
  have hal : ∀ b, Rd b → Aligned b := by
    rintro b (hb | hb)
    · exact hb.1.1
    · exact (kPte b hb.1).1
  have kvR : ∀ b, Rd b → L.mem σ b = ρ b := by
    rintro b (hb | hb)
    · exact (hmm b hb.1.1 hb.1.2.1).trans hb.2.1.1
    · exact (hmm b (kPte b hb.1).1 (kPte b hb.1).2).trans (vPte b hb.1).1
  let Ru : U64 → Prop := PathObl.UserW K.toKLayout
  let RdU : U64 → Prop := DelRdP K c ρ (IoRS (st := st) K.toKLayout Locks σ) (Locks σ)
  have hRal : ∀ b, RdU b → Aligned b := fun b h => Or.elim h (hal b) (fun h => h.1)
  -- the write sets
  let Wd : U64 → Prop := DelWdP K c ρ (IoWS (st := st) K.toKLayout Locks σ) (Locks σ)
  let Pw : S → U64 → U64 → Prop := DelPwP (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ)
    (IoWS (st := st) K.toKLayout Locks σ) (L.curW σ) (L.mem σ) (Locks σ)
  have hWal : ∀ b, Wd b → Aligned b := by
    rintro b ((h | h) | h)
    · exact h.1.1
    · exact h.1
    · exact (kPte b h.1).1
  have hPal : ∀ x q v, Pw x q v → Aligned q := fun x q v h => hWal q (hPW x q v h)
  have affC : L.mem σ (fld (L.curW σ) oAFFINITY) = c := by
    have hu : fld (L.curW σ) oAFFINITY ∉ K.user := hL.nu_tcb hcT (k := 3520#u64) (by simp) (by simp)
    have ha : Aligned (fld (L.curW σ) oAFFINITY) := field_aligned ht' (by simp [OwnMap.oAFF_val])
      (by simp [OwnMap.oAFF_val])
    rw [hmm _ ha hu]
    exact CoreView.view_aff hK0 htH c ρ
  let Rd0 : U64 → Prop := fun b => IoRS (st := st) K.toKLayout Locks σ b ∧ SR K c ρ b
  -- the aligned user words
  have hfin : Set.Finite {x : U64 | Aligned x ∧ x ∈ K.user} := Set.toFinite _
  obtain ⟨ul, hul⟩ : ∃ l : List U64, ∀ x, x ∈ l ↔ Aligned x ∧ x ∈ K.user :=
    ⟨hfin.toFinset.toList, fun x => by simp⟩
  have slNU : ∀ q, q ∈ K.slots → Aligned q ∧ q ∉ K.user := fun q hq' => OwnMap.decW_ok hUO (Or.inr (Or.inl hq'))
  have hPre : PreP st Cs Ω Sg Ac Locks p K (view K.toKLayout c ρ) σ := ⟨hJ, hq, hqu.2⟩
  -- every state carrying `ρ` on the kernel reads runs as a view start with its user words
  intro s hcs' hks hag
  have hagR : ∀ b, Rd b → L.mem s b = L.mem σ b := fun b hb => (hag b hb).trans (kvR b hb).symm
  obtain ⟨σ', hσ'⟩ : ∃ x, x = E2E.wrs st (L.mem s) ul σ := ⟨_, rfl⟩
  obtain ⟨c1, c2, c3⟩ := E2E.wrs_const st (ν := L.mem s) (masksWr_plain st) ul σ
  have hM := E2E.wrs_mem st (ν := L.mem s) ul σ (fun x hx => ((hul x).mp hx).1)
  obtain ⟨hPre', hqu', eL, eRS, eWS, eCur⟩ := wrsP_facts (f := L.mem s) hCs hlk ul σ
    (fun x hx => (hul x).mp hx) hPre hqu
  rw [← hσ'] at c1 c2 c3 hM hPre' hqu' eL eRS eWS eCur
  have hmm' : ∀ x, Aligned x → x ∉ K.user → L.mem σ' x = view K.toKLayout c ρ x := fun x hx hu => by
    rw [hM x hx, if_neg (fun h => hu ((hul x).mp h).2)]; exact hmm x hx hu
  obtain ⟨r', hg', hs'⟩ := inv_pte_gdA ar hA hK hU nv (number := number) (a := a) hPre'.1 hPre'.2.1 hqu'
    (c1.trans hc) hmm'
  have eP : DelPwP (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ') (IoWS (st := st) K.toKLayout Locks σ')
      (L.curW σ') (L.mem σ') (Locks σ') = Pw := by
    rw [eRS, eWS, eCur, eL]
    exact delPwP_mem fun q hq' => by
      rw [hM q (slNU q hq').1, if_neg (fun h => (slNU q hq').2 ((hul q).mp h).2)]
  rw [eP, eRS, eL] at hg'
  have hagU : ∀ b, RdU b → L.mem s b = L.mem σ' b := by
    rintro b (hb | hb)
    · rw [hagR b hb, hM b (hal b hb), if_neg (fun h => (hR0 b hb).2 ((hul b).mp h).2)]
    · rw [hM b hb.1, if_pos ((hul b).mpr hb)]
  have hmk' : st.frame_masks s = st.frame_masks σ' := by
    rw [PlainStore.frame_masks_eq, PlainStore.frame_masks_eq]
  obtain ⟨x0, s0', a0'⟩ := r'
  obtain ⟨s1', hs1⟩ := interp_agree_gd (st := st) (masksWr_plain st) hRal hPal (fun _ _ _ _ _ h => h)
    (R.invBodyG number p) (inv_noZero number p) σ' s a x0 s0' a0' (hks.trans c2.symm) (hcs'.trans c1.symm)
    hmk' hagU hg'
  have hgs := interp_gd_guard (R' := RdU) (W := Wd) (fun q h => h) hPW _ s a _ hs1
  -- `StepOK` per write
  have hI0 : DelStInv (st := st) K c ρ Locks σ s := by
    have rA : Rd0 (fld (L.curW σ) oAFFINITY) :=
      ⟨PE.gate (Locks := Locks) (off := 3520#u64) PE.cT (by simp) (by simp) (by simp) (by simp [GateField]),
        srT 3520#u64 (by simp) (by simp) (by simp)⟩
    have rS : Rd0 (fld (L.curW σ) oSTATE) := by
      rw [← OwnMap.stA_fld]
      refine ⟨PE.stw.1, ?_⟩
      rw [Fl4Proofs.P1.stA_eq]; exact srT 3328#u64 (by simp) (by simp) (by simp)
    refine ⟨(hagR _ (Or.inl rA)).trans affC, ?_, fun q hq' hT' hRd hn => by rw [hagR q (Or.inl hRd)]; exact hn⟩
    rw [hagR _ (Or.inl rS), ← OwnMap.stA_fld]
    exact nq_run PE.run
  have hm := interp_gd (R := RdU) (P := Pw)
    (Q := fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs
      (L.mem x) (L.mem y)) (I := DelStInv (st := st) K c ρ Locks σ) hStep _ s a _ hI0 hs1
  -- `Once`: the path's `ReadOnce` at `σ'`, carried to `s`, narrowed
  have hO1 : Once st ar (InvRSP st K Locks σ') (· ∈ K.user) ∅ ∅ (R.invBodyG number p) σ' a :=
    invRoPP hA (masksWr_plain st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) (number := number)
      (p := p) (m := view K.toKLayout c ρ) hK hU nv σ' σ' a _ hPre' (Alt.refl (L := L) σ') hs'
  have eCM : InvRSP st K Locks σ' = InvRSP st K Locks σ := by
    funext x; unfold InvRSP IoRSP; rw [eRS, eL]
  have hO1' : Once st ar (InvRSP st K Locks σ) (· ∈ K.user) ∅ ∅ (R.invBodyG number p) σ' a := by
    have h' := hO1
    rw [eCM] at h'
    exact h'
  have hgσ' := interp_gd_guard (R' := RdU) (W := Wd) (fun q h => h) hPW _ σ' a _ hg'
  have hO2 := once_agreeJ (masksWr_plain st) (Rd := InvRSP st K Locks σ) (User := (· ∈ K.user))
    hRal hWal (R.invBodyG number p) (inv_noZero number p) σ' s a _ ∅ ∅ (hks.trans c2.symm) (hcs'.trans c1.symm)
    hmk' hagU hgσ' hO1'
  have hO3 := once_downR (R := Rd) (Ro := Ro) (R' := InvRSP st K Locks σ) (U := Ru) (W := Wd)
    (User := (· ∈ K.user)) (fun q h => (hR0 q h).2) (fun q h => (hR0 q h).1) (fun q h => h.1) (fun q h => h.2)
    (R.invBodyG number p) (inv_noZero number p) ∅ ∅ s a _ hgs hO2
  exact ⟨_, hgs, (interp_mguard _ s a _ hm).2, hO3, σ', hPre', hqu', hmm', hks.trans c2.symm, hcs'.trans c1.symm,
    hmk', hagU, (interp_guard _ σ' a _ hgσ').2⟩

set_option maxHeartbeats 16000000 in
/-- **U9's armed PTE-arm Delete program is `Safe` at every PTE-delete view start** (module docstring). -/
theorem inv_pte_annA (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {number : I64} {σ : S} {a : A}
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ (K' : OwnMap.KLayout) (s : S) (b v : U64), SlJAt (L := L) K' s → b ∈ K'.user → Aligned b →
      Locks (L.wr s b v) = Locks s)
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (hq : InvQFP st Cs Ω Sg Ac Locks p K.toKLayout (view K.toKLayout c ρ) σ) (hqu : QU st K σ)
    (hc : L.cpu σ = c) (hl : Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (InvRSP st K Locks σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.invBodyG number p) ∅ a)) := by
  have hgoX := pte_hgoX ar hA hK hU nv hV (number := number) (a := a) hCs hlk hJ hq hqu hc hmm
  -- the read sets
  have kPte : ∀ b, b ∈ K.ptes → Aligned b ∧ b ∉ K.user := fun b hb => hU.kern b hb
  have oPte : ∀ b, b ∈ K.ptes → VO K c ρ b := fun b hb => by unfold VO; rw [ownP_pte hb, ownP_pte hb]
  let Rd : U64 → Prop := fun b => (IoRS (st := st) K.toKLayout Locks σ b ∧ SR K c ρ b) ∨ PteRd K (Locks σ) b
  let Ro : U64 → Prop := fun q => InvRSP st K Locks σ q ∧ VO K c ρ q
  have hR0 : ∀ q, Rd q → Ro q ∧ ¬ q ∈ K.user := by
    rintro q (⟨h1, h2⟩ | ⟨hp, hl'⟩)
    · exact ⟨⟨⟨h1.1, Or.inr ⟨h1, fun hp => absurd hp h2.2⟩⟩, h2.1.2⟩, h1.2.1⟩
    · exact ⟨⟨⟨(kPte q hp).1, Or.inr ⟨VsW.ioRS ⟨(kPte q hp).1, hK.none q hp, (kPte q hp).2⟩, fun _ => hl'⟩⟩,
        oPte q hp⟩, (kPte q hp).2⟩
  have hal : ∀ b, Rd b → Aligned b := by
    rintro b (hb | hb)
    · exact hb.1.1
    · exact (kPte b hb.1).1
  let Ru : U64 → Prop := PathObl.UserW K.toKLayout
  let Wd : U64 → Prop := DelWdP K c ρ (IoWS (st := st) K.toKLayout Locks σ) (Locks σ)
  -- ownership of the read and written words at the physical memory
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hWd : ∀ x, Wd x → Aligned x ∧ (¬ x ∈ K.user → HeldV c hs (ownP K μ x)) := by
    rintro x ((⟨⟨ha, hw⟩, hp, hvo⟩ | hu) | ⟨hp, hlx⟩)
    · refine ⟨ha, fun _ => ?_⟩
      have h1 : HeldV c hs (ownP K (L.mem σ) x) := by
        rw [ownP_eq_own nv hp, ← hc, ← hl]
        exact heldV_of_heldBy hw
      rw [eown, hvo] at h1
      rw [hV.1 x (Or.inl h1)]
      exact h1
    · exact ⟨hu.1, fun h => absurd hu.2 h⟩
    · refine ⟨(kPte x hp).1, fun _ => ?_⟩
      rw [ownP_pte hp]
      show hs x
      rw [← hl]; exact hlx
  have hRPO : ∀ x, ¬ x ∈ K.user → Ro x → PO c hs (ownP K μ x) := by
    intro x hu hx
    have hio : IoRSP st K Locks σ x := hx.1.2.resolve_left hu
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      have := po_of_rperm (ioRSP_rperm nv hio)
      rw [hc, hl] at this
      exact this
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  -- every state carrying `ρ` on the kernel reads runs as a view start with its user words (`pte_hgoX`)
  have hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∃ r, interp (guard st (fun b => Rd b ∨ Ru b) Wd) ar (R.invBodyG number p) s a = ok r ∧
        WithinM st ar (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ)
          (· ∈ K.user) c hs (L.mem x) (L.mem y)) (R.invBodyG number p) s a ∧
        Once st ar Ro (· ∈ K.user) ∅ ∅ (R.invBodyG number p) s a := by
    intro s hcs' hks hag
    obtain ⟨r, h1, h2, h3, -⟩ := hgoX s hcs' hks hag
    exact ⟨r, h1, h2, h3⟩
  have h := PathObl.safe_tr_wrU (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar (moveHeldP hK) (ownDepP hK hU) (masksWr_plain st) (a := a)
    (R.invBodyG number p) hc (Ro := Ro) (Rd := Rd) (Ru := Ru) (Wd := Wd) hal hR0 (fun b h => h.1)
    hWd hRPO (fun x hx => hV.2.1 x hx) hgo
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

end main

end
end Fl4Proofs.P2.E2EP
