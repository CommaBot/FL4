/-
# P2 (line p3mc, gen 25): the timer interrupt's certificate at a view start whose signal's head waiter is foreign

Handoff §29c item 1 (W-f), for the irq view starts whose earliest thread `tm` of `c`'s timer tree is, in `ρ`, on
`c`, with a bound notification `N` that is `WAITING` and whose head waiter `w` is, in `ρ`, another core's
(`IrqWfR`). The real run declines inside `fire_ok` (`wake_ok` → `may_run_here`: `w`'s `AFFINITY` is not the core),
while at the view start `σ` (every `AFFINITY` reads `c`) it may accept: the gen-16 counter-shape. So, as gen 23 did
for a foreign `tm`, the run is taken at the real state `s` (carrying `ρ` on the read set, which here holds `w`'s
`AFFINITY` too) and only the part that needs P1's invariant comes from `σ`:

* the head (`plan_objects`) at `s` (`irq_pl_guardE`, P2/IrqWfG);
* the tail: by `irqTailF_plan` (P2/IrqWfG) the tail with the plan is the tail with the plan's `tm` set to 0, since at
  `s` `fire_ok` declines with the plan (`fire_ok_guardWF` + `fireTail_falseW`: the tree words agree with `σ`'s, the
  notification is waiting with head `w`, `w`'s `AFFINITY` reads `ρ`'s, another core) as with the empty plan
  (`fire_ok_tm0`); the tail with the empty plan runs at `σ` on gen 23's checked store (`irqTail_guardT`) and is moved
  to `s` by `interp_agree_gd` (every word it reads is `SR`).

**`irq_wf_annV`**: `PathObl.safe_tr_wr` with `Rd :=` gen 24's `IrqHnRd` ∪ the tree / notification words (`FTree`,
`FNt`) ∪ {`w`'s `AFFINITY`} (a gate word: readable, owner kept by the view; its value is not kept, only `ρ`'s is
used), `Wd :=` gen 23's `IrqFhWd`, write predicate gen 23's `IrqFhP` (no fire write happens).

Gen 49 (in place, statement of `irq_wf_annV` unchanged): its certificate data is split out as **`irq_wf_cert`**
(read set `IrqWfRd`, write set `IrqFhWd`, the guarded run, the writes' `WPerm` at the start, `tm ≠ 0`, the head
waiter a thread) for the `InsA` twin (P2/InsV15Irq).

No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.IrqWfG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE oTIMER_HEIGHT oSTATE InW GateField
  TimerField GField tcbOwner ntfnOwner)
open Fl4Proofs.P2.E2E (SP tr masksOf)
open Fl4Proofs.P2.Serial (Owner VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec NotForeign vn_of_nf nf_node nf_sc nf_slot nf_none nf_tcb
  TZero)

noncomputable section
open Classical

/-- **The earliest thread `tm` is on `c`, its bound notification is waiting, and the head waiter is another
core's, in `ρ`** (module docstring). -/
def IrqWfR (ρ : U64 → U64) (c tm : U64) : Prop :=
  tm ≠ 0#u64 ∧ ρ (affA tm) = c ∧ ρ (boundA tm) ≠ 0#u64 ∧
    (ρ (epTSA (ρ (boundA tm))) &&& 3#u64) = obj.NTFN_WAITING ∧ ρ (affA (ρ (epHeadA (ρ (boundA tm))))) ≠ c

section sets
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **The read set of `irq_wf_annV`'s certificate** (gen 49, split out of `irq_wf_annV`): gen 24's `IrqHnRd`, the
tree / notification words, and the head waiter's `AFFINITY`. -/
def IrqWfRd (T : Set U64) (Z : U64 → Nat) (irq : U64) (σ : S) (b : U64) : Prop :=
  (IrqHnRd st T Z irq σ b ∨ (Aligned b ∧ FTree st T σ b) ∨ (Aligned b ∧ FNt st σ b)) ∨
    b = affA (L.mem σ (epHeadA (L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN))))))

end sets

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The data of `irq_wf_annV`'s certificate** (gen 49, split out of `irq_wf_annV` in place): the read set
`IrqWfRd`, aligned and readable, the write set `IrqFhWd`, held at the start, the guarded run with `StepOK` at every
state carrying `ρ` on the read set, `tm ≠ 0` and the head waiter a thread. -/
theorem irq_wf_cert (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {irq : U64} {pl : localtimer.TimerIrqPlan} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hq : QPs K st σ) (hirq : irq.val < 128)
    (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hH : IrqWfR ρ c (ρ (tmA (L := L) σ))) :
    (∀ b, IrqWfRd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) irq σ b → Aligned b) ∧
    (∀ q, IrqWfRd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) irq σ q → (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ q ∧ VO K c ρ q) ∧ ¬ q ∈ K.user) ∧
    (∀ x, IrqFhWd st (Heap.scBits K.toKLayout.heap) σ x → Aligned x ∧ (¬ x ∈ K.user → HeldV c hs (ownP K μ x))) ∧
    (∀ q, ¬ q ∈ K.user → (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ q ∧ VO K c ρ q) → PO c hs (ownP K μ q)) ∧
    (∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, IrqWfRd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) irq σ b → L.mem s b = ρ b) →
      ∃ r, interp (guard st (IrqWfRd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) irq σ) (IrqFhWd st (Heap.scBits K.toKLayout.heap) σ)) ar
          (R.localtimer.handle_timer_irq_local irq pl) s a = ok r ∧
        WithinM st ar (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ)
          (· ∈ K.user) c hs (L.mem x) (L.mem y)) (R.localtimer.handle_timer_irq_local irq pl) s a) ∧
    (∀ x, IrqFhWd st (Heap.scBits K.toKLayout.heap) σ x → PathObl.WPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) x) ∧
    L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN) ≠ 0#u64 ∧
    L.mem σ (epHeadA (L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN))))) ∈ Heap.tcbs K.toKLayout.heap := by
  have hX := hJ.regionOKX
  have hK0 := hJ.regionOK
  have hUO := hJ.userOK
  obtain ⟨hk, hcp⟩ := hJ.kc
  obtain ⟨Ω, Ac, EM⟩ := IrqPreJ3.entM (st := st) (K := K.toKLayout) (m := L.mem σ) (s := σ) (irq := irq)
    ⟨hJ, fun _ _ _ => rfl⟩
  have E0 := EM.ent
  have hI := E0.inv
  have hL := E0.lay
  have hY := E0.ly
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced (Heap.tcbs K.toKLayout.heap) := h0.tcbs
  have hN : NodePlaced st (Heap.tcbs K.toKLayout.heap) σ (L.cpu σ) := h0.nodes _ h0.cur
  have hcT : L.curW σ ∈ Heap.tcbs K.toKLayout.heap := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have ht' := hT _ hcT
  have hcur : ρ (fld (L.curW σ) oAFFINITY) = c := vx_cur_home hJ hmm
  have hcs : L.cscW σ ∈ Heap.scs K.toKLayout.heap := hI.2.2.1.2.2.cur
  have hO := hI.2.2.1.1
  have hSs := hI.2.2.2.2
  have ct0 : L.curW σ ≠ 0#u64 := fun e => (hT _ hcT).ne0 (by rw [e]; rfl)
  have csc0 : L.cscW σ ≠ 0#u64 := fun e => by
    have h1 := st_scH (K := K) hcs
    rw [e, slJAt_heap0 hJ] at h1
    cases h1
  -- a thread's `AFFINITY` at the view is the core
  have affC : ∀ t, t ∈ Heap.tcbs K.toKLayout.heap → L.mem σ (affA t) = L.cpu σ := fun t ht => by
    have hu : affA t ∉ K.user := hL.nu_tcb ht (k := 3520#u64) (by simp) (by simp)
    have ha : Aligned (affA t) := field_aligned (hT _ ht) (by simp) (by simp)
    rw [hmm _ ha hu, hc]
    exact CoreView.view_aff hK0 ht c ρ
  have ownT : ∀ t k, t ∈ Heap.tcbs K.toKLayout.heap → 256 ≤ k.val → k.val < 4096 →
      OwnMap.own K.toKLayout (L.mem σ) (core.num.U64.wrapping_add t k) = tcbOwner (L.mem σ) t k.val :=
    fun t k ht h1 h2 => by
      have e := hL.own_tcb hT (L.mem σ) ht (k := k) h1 h2
      unfold fld at e
      exact e
  -- homes
  have scHome : ∀ p, p ∈ Heap.scs K.toKLayout.heap → L.mem σ (scTcbA p) ≠ 0#u64 → ρ (fld p 16#u64) = c := by
    intro p hp hp0
    obtain ⟨hP, hz⟩ := hO.sc _ hp
    obtain ⟨h8, h128, hfit⟩ := sc_lo hP hz
    have hv : (scTcbA p).val = p.val + 24 := by
      unfold scTcbA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have hr : region K.toKLayout (scTcbA p) = .sc p :=
      hX.scW p _ (st_scH (K := K) hp) _ ⟨by omega, by omega⟩
    have ha : Aligned (scTcbA p) := by unfold Aligned; rw [hv]; omega
    have hku : scTcbA p ∉ K.user := hL.nu_sc hp ⟨by omega, by omega⟩
    exact CoreView.view_sctcb_home (K := K.toKLayout) hr (by omega) (by rw [← hmm _ ha hku]; exact hp0)
  have cscHome : IrqOk st σ → ρ (fld (L.cscW σ) 16#u64) = c := by
    intro hok
    have hne : L.mem σ (scA (L.curW σ)) ≠ 0#u64 := by rw [hok.sc]; exact csc0
    obtain ⟨hcs', htcb, -⟩ := hI.2.2.1.2.2.bound _ h0.curT hne
    rw [← hok.sc]
    exact scHome _ hcs' (fun e => ct0 (htcb.symm.trans e))
  have rhHome : ∀ (h00 : L.mem σ (rhA (L := L) σ) ≠ 0#u64),
      ρ (fld (L.mem σ (rhA (L := L) σ)) oAFFINITY) = c ∧
        ρ (fld (L.mem σ (scA (L.mem σ (rhA (L := L) σ)))) 16#u64) = c := by
    intro h00
    obtain ⟨⟨Q, Rq, hq'⟩, hb, ⟨-, -, hX'⟩, -, -⟩ := id hI
    obtain ⟨hTr, -, -⟩ := bxi_rh hI h00
    have hne : L.mem σ (scA (L.mem σ (rhA (L := L) σ))) ≠ 0#u64 := by
      intro e0
      have hfl := hb.r _ hTr
      have hrel := hq'.release _ hq'.cur
      have hd : L.mem σ (rhA (L := L) σ) = (Rq (L.cpu σ)).headD 0#u64 := hrel.head
      have hmR : L.mem σ (rhA (L := L) σ) ∈ Rq (L.cpu σ) := by
        cases hl' : Rq (L.cpu σ) with
        | nil => rw [hl'] at hd; exact absurd hd h00
        | cons r rs => rw [hl'] at hd; rw [hd]; simp
      exact hfl ((hq'.released _ hTr).2 (by rw [hq'.inR _ hq'.cur _ hmR]; exact hmR)) e0
    obtain ⟨hcs', htcb, -⟩ := hX'.bound _ hTr hne
    refine ⟨?_, scHome _ hcs' (fun e => h00 (htcb.symm.trans e))⟩
    have hrH : K.toKLayout.heap (L.mem σ (rhA (L := L) σ)) = some .tcb := hTr
    obtain ⟨hr, hv, ha⟩ := hX.tcbW _ hrH 3464#u64 (by simp) (by simp) (by simp)
    have hu : scA (L.mem σ (rhA (L := L) σ)) ∉ K.user := hL.nu_tcb hTr (k := 3464#u64) (by simp) (by simp)
    refine CoreView.view_tzero_home hr (by rw [hv]; simp [TZero]) ?_
    rw [← hmm _ ha hu]; exact hne
  set tm := L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN) with htm
  have armρ : tm ≠ 0#u64 → ρ (fld tm oTIMER_DEADLINE) ≠ 0#u64 := by
    intro hne
    obtain ⟨tmT, arm⟩ := tmin_facts (BXI.blk hI) h0.cur hne
    have tH : K.toKLayout.heap tm = some .tcb := tmT
    obtain ⟨hr0, hv0, hal⟩ := hX.tcbW tm tH 3528#u64 (by simp) (by simp) (by simp)
    have hr : region K.toKLayout (tdA tm) = .tcb tm := hr0
    have hv : (tdA tm).val - tm.val = (3528#u64).val := hv0
    have hu : tdA tm ∉ K.user := hL.nu_tcb tmT (k := 3528#u64) (by simp) (by simp)
    have e1 := hmm (tdA tm) hal hu
    have e2 : view K.toKLayout c ρ (tdA tm) = ρ (tdA tm) :=
      CoreView.view_timer_keep hr (by rw [hv]; simp) (by rw [hv]; simp)
    intro e
    exact arm.1 (by rw [e1, e2]; exact e)
  -- the good read words
  let G : U64 → Prop := fun b => Aligned b ∧ RPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) b ∧
    b ∉ K.user ∧ SR K c ρ b
  have gN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → G (L.nodeAt σ (L.cpu σ) o) := by
    intro o ho h8
    have hr : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node (L.cpu σ) := hL.nd o ho
    have hr' : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node c := by rw [hr, hc]
    exact ⟨nodeAt_aligned hN ho h8, Or.inl (held_core (hL.own_node _ ho)), hL.nu_node ho,
      sr_nf hK (by rw [hr']; intro h; cases h) (nf_node hr')⟩
  have gC : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) →
      k.val ≠ 3496 → k.val ≠ 3504 → G (core.num.U64.wrapping_add (L.curW σ) k) := by
    intro k h1 h2 h3 h4 h5 h6
    refine ⟨field_aligned ht' h2 h3, ?_, hL.nu_tcb hcT h1 h2, sr_tcb hK hX htH hcur (by omega) h2 h3⟩
    by_cases hg : GateField k.val
    · exact Or.inr (by unfold GateOnly; rw [ownT _ k hcT h1 h2, tcbOwner, if_pos hg])
    · refine Or.inl (held_core ?_)
      rw [ownT _ k hcT h1 h2, tcbOwner, if_neg hg, if_neg (by unfold TimerField; omega),
        if_neg (by unfold GField; omega)]
      exact congrArg Owner.core (affC _ hcT)
  have gT : IrqOk st σ → ∀ b, Aligned b → IrqRdT st (Heap.scBits K.toKLayout.heap) σ b → G b := by
    intro hok b ha hb
    have hrp := irq_rd_own hK0 hI hL hY E0.aff hok (lk := lk σ) (irqRdT_sub hb)
    have hnu := irq_rd_nu hI hL hY (irqRdT_sub hb)
    refine ⟨ha, hrp, hnu, ?_⟩
    rcases hb with ⟨o, ho, h8, rfl⟩ | ⟨k, h1, h2, h3, h4, h5, h6, rfl⟩ | hb | ⟨hne, rfl | hb⟩ | ⟨hne, rfl⟩ |
        ⟨k, hk', hk32, h8, rfl⟩
    · exact (gN o ho h8).2.2.2
    · exact (gC k h1 h2 h3 h4 h5 h6).2.2.2
    · exact (srw_sc hK hX (st_scH (K := K) hcs) (cscHome hok) hb).1
    · obtain ⟨r1, -, -, -, -⟩ := rel_facts hI hne
      exact sr_tcb hK hX (show K.toKLayout.heap _ = some .tcb from r1) (rhHome hne).1 (o := 3464#u64)
        (by simp) (by simp) (by simp)
    · obtain ⟨-, -, -, r4, -⟩ := rel_facts hI hne
      exact (srw_sc hK hX (st_scH (K := K) r4) (rhHome hne).2 hb).1
    · obtain ⟨tmT, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne
      exact sr_timer hK hX (show K.toKLayout.heap _ = some .tcb from tmT) (o := 3528#u64) (by simp) (by simp)
        (by simp) (armρ hne)
    · obtain ⟨p, hr, -, -⟩ := hY.cs k hk' hk32
      exact sr_nf hK (by rw [hr]; intro h; cases h) (nf_slot hr)
  have gSc : L.mem σ (scA (L.curW σ)) ≠ 0#u64 → G (scCoreA (L.mem σ (scA (L.curW σ)))) := by
    intro hne
    obtain ⟨hcs0, htcb0, -⟩ := hI.2.2.1.2.2.bound _ h0.curT hne
    have hcs' : L.mem σ (scA (L.curW σ)) ∈ Heap.scs K.toKLayout.heap := hcs0
    have htcb : L.mem σ (scTcbA (L.mem σ (scA (L.curW σ)))) = L.curW σ := htcb0
    have hcore : L.mem σ (scCoreA (L.mem σ (scA (L.curW σ)))) = L.cpu σ := (E0.aff _ hcT hne).trans (affC _ hcT)
    clear hcs0 htcb0
    generalize hpq : L.mem σ (scA (L.curW σ)) = p at hcs' htcb hne hcore ⊢
    have hz := st_scH (K := K) hcs'
    obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
      (by simp [layout.sc.CORE])
    have e := sc_own hL hcs' hin hcore
    refine ⟨am, ?_, hL.nu_sc hcs' hin, (srw_sc hK hX hz (scHome _ hcs' (fun e => ct0 (htcb.symm.trans e))) hin).1⟩
    split at e
    · exact Or.inr e
    · exact Or.inl (held_core e)
  have gK : ∀ o : U64, (o = layout.ks.CUR_DOMAIN ∨ o = layout.ks.DOMAIN_TIME ∨ o = layout.ks.KERNEL_ROOT) →
      G (core.num.U64.wrapping_add (L.ksb σ) o) := by
    rintro o (rfl | rfl | rfl)
    · exact ⟨hL.domA, rperm_none hL.dom _, hL.domU,
        ⟨vn_of_nf hK (nf_none hL.dom), hq.ksw (by simp [layout.ks.CUR_DOMAIN])⟩⟩
    · exact ⟨hL.dtmA, rperm_none hL.dtm _, hL.dtmU,
        ⟨vn_of_nf hK (nf_none hL.dtm), hq.ksw (by simp [layout.ks.DOMAIN_TIME])⟩⟩
    · exact ⟨hY.kr.1, rperm_none hY.kr.2 _, hY.krU,
        ⟨vn_of_nf hK (nf_none hY.kr.2), hq.ksw (by simp [layout.ks.KERNEL_ROOT])⟩⟩
  have gI : ∀ i, interrupt.state_off irq = ok i → G (core.num.U64.wrapping_add (L.ksb σ) i) := fun i hi => by
    obtain ⟨ha, hr⟩ := hY.iq hirq i hi
    exact ⟨ha, rperm_none hr _, hY.iqU hirq i hi, ⟨vn_of_nf hK (nf_none hr), hq.ksw (state_off_lt hirq hi)⟩⟩
  have gTab : IrqOk st σ → ∀ hi : U64, hi.val < 2048 → G (atAF (L.ksb σ) hi) ∧
      ∀ lo : U64, lo.val < 512 → L.mem σ (atAF (L.ksb σ) hi) ≠ 0#u64 → G (peAF (L.mem σ (atAF (L.ksb σ) hi)) lo) := by
    intro _ hi hhi
    obtain ⟨⟨a0, r0⟩, hlo'⟩ := hY.tab hi hhi
    refine ⟨⟨a0, rperm_none r0 _, (hY.tabU hi hhi).1, ⟨vn_of_nf hK (nf_none r0), (hq.tab hi hhi).1⟩⟩,
      fun lo hlo hne => ?_⟩
    obtain ⟨a1, r1⟩ := hlo' lo hlo hne
    exact ⟨a1, rperm_none r1 _, (hY.tabU hi hhi).2 lo hlo hne,
      ⟨vn_of_nf hK (nf_none r1), (hq.tab hi hhi).2 lo hlo hne⟩⟩
  have gR : ∀ b, IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ b → G b := by
    intro b hb
    rcases hb with ⟨o, ho, h8, rfl⟩ | ⟨k, h1, h2, h3, h4, h5, h6, rfl⟩ | ⟨hok, ha, hb⟩ | ⟨hne, rfl⟩ |
        ⟨o, ho, rfl⟩ | ⟨-, i, hi, rfl⟩ | ⟨hok, hi, hhi, rfl | ⟨lo, hlo, hne, rfl⟩⟩
    · exact gN o ho h8
    · exact gC k h1 h2 h3 h4 h5 h6
    · exact gT hok b ha hb
    · exact gSc hne
    · exact gK o ho
    · exact gI i hi
    · exact (gTab hok hi hhi).1
    · exact (gTab hok hi hhi).2 lo hlo hne
  -- membership helpers
  have rN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ (L.nodeAt σ (L.cpu σ) o) :=
    fun o h1 h2 => Or.inl ⟨o, h1, h2, rfl⟩
  have rC : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) →
      k.val ≠ 3496 → k.val ≠ 3504 →
      IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ (core.num.U64.wrapping_add (L.curW σ) k) :=
    fun k h1 h2 h3 h4 h5 h6 => Or.inr (Or.inl ⟨k, h1, h2, h3, h4, h5, h6, rfl⟩)
  have rK : ∀ o : U64, (o = layout.ks.CUR_DOMAIN ∨ o = layout.ks.DOMAIN_TIME ∨ o = layout.ks.KERNEL_ROOT) →
      IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ (core.num.U64.wrapping_add (L.ksb σ) o) :=
    fun o ho => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨o, ho, rfl⟩))))
  have rI : ∀ i, interrupt.state_off irq = ok i →
      IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ (core.num.U64.wrapping_add (L.ksb σ) i) :=
    fun i hi => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hirq, i, hi, rfl⟩)))))
  have rSt : IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ (stA (L.curW σ)) := by
    rw [Fl4Proofs.P1.stA_eq]
    exact rC 3328#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)
  have rAf : IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ (affA (L.curW σ)) :=
    rC 3520#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)
  -- (gen 24) values the view keeps
  have kvR : ∀ b, G b → L.mem σ b = ρ b := fun b g => by
    rw [hmm b g.1 g.2.2.1]; exact g.2.2.2.1.1
  have hY := E0.ly
  have eTm : L.mem σ (tmA (L := L) σ) = ρ (tmA (L := L) σ) :=
    kvR _ (gN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
  have hW : IrqWfR ρ c tm := by
    have h' : IrqWfR ρ c (L.mem σ (tmA (L := L) σ)) := by rw [eTm]; exact hH
    exact h'
  obtain ⟨hH0, hH1, hH3, hH4, hH5⟩ := hW
  have hne : tm ≠ 0#u64 := hH0
  obtain ⟨tmT, tmArm⟩ := tmin_facts (BXI.blk hI) h0.cur hne
  have tH : K.toKLayout.heap tm = some .tcb := tmT
  have hHome : ρ (fld tm oAFFINITY) = c := hH1
  -- armed in the view ⇒ armed in `ρ`
  have armY : ∀ y, y ∈ Heap.tcbs K.toKLayout.heap → L.mem σ (tdA y) ≠ 0#u64 → ρ (fld y oTIMER_DEADLINE) ≠ 0#u64 := by
    intro y yT hy
    have yH : K.toKLayout.heap y = some .tcb := yT
    obtain ⟨hr0, hv0, hal⟩ := hX.tcbW y yH 3528#u64 (by simp) (by simp) (by simp)
    have hr : region K.toKLayout (tdA y) = .tcb y := hr0
    have hv : (tdA y).val - y.val = (3528#u64).val := hv0
    have hu : tdA y ∉ K.user := hL.nu_tcb yT (k := 3528#u64) (by simp) (by simp)
    have e1 := hmm (tdA y) hal hu
    have e2 : view K.toKLayout c ρ (tdA y) = ρ (tdA y) :=
      CoreView.view_timer_keep hr (by rw [hv]; simp) (by rw [hv]; simp)
    intro e
    exact hy (by rw [e1, e2]; exact e)
  -- the timer words of the keys armed in `c`'s tree
  have gKey : ∀ y k, y ∈ Heap.tcbs K.toKLayout.heap → FootLtArmed st σ (L.cpu σ) y → 3528 ≤ k.val → k.val < 3576 →
      k.val % 8 = 0 → G (core.num.U64.wrapping_add y k) := by
    intro y k yT ya h1 h2 h3
    have yH : K.toKLayout.heap y = some .tcb := yT
    have hs' : SR K c ρ (fld y k) := sr_timer hK hX yH h1 (by omega) h3 (armY y yT ya.1)
    exact ⟨field_aligned (hT _ yT) (by omega) h3, Or.inl (held_core (ftree_own hL hT yT ya h1 h2 h3)),
      hL.nu_tcb yT (by omega) (by omega), hs'⟩
  -- `tm`'s words off its timer fields
  have gTm : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) →
      k.val ≠ 3496 → k.val ≠ 3504 → G (core.num.U64.wrapping_add tm k) := by
    intro k h1 h2 h3 h4 h5 h6
    refine ⟨field_aligned (hT _ tmT) h2 h3, ?_, hL.nu_tcb tmT h1 h2, sr_tcb hK hX tH hHome (by omega) h2 h3⟩
    by_cases hg : GateField k.val
    · exact Or.inr (by unfold GateOnly; rw [ownT _ k tmT h1 h2, tcbOwner, if_pos hg])
    · refine Or.inl (held_core ?_)
      rw [ownT _ k tmT h1 h2, tcbOwner, if_neg hg, if_neg (by unfold TimerField; omega),
        if_neg (by unfold GField; omega)]
      exact congrArg Owner.core (affC _ tmT)
  -- `tm`'s bound notification
  set N := L.mem σ (boundA tm) with hNdef
  have ntAll : N ≠ 0#u64 → L.mem σ (ntfnBtA N) = tm ∧ ∀ k : U64, k.val < 64 → k.val % 8 = 0 →
      G (core.num.U64.wrapping_add N k) ∧
        (k.val ≠ 24 → OwnMap.own K.toKLayout (L.mem σ) (core.num.U64.wrapping_add N k) = .core (L.cpu σ)) := by
    intro hb
    have hNt : N ∈ K.toKLayout.heap.ntfns := hI.2.2.1.2.2.bnd _ tmT hb
    have hbt : L.mem σ (ntfnBtA N) = tm := hI.2.2.1.2.2.bs.tb _ tmT hb
    refine ⟨hbt, fun k h1 h2 => ?_⟩
    have hpH : K.toKLayout.heap N = some .ntfn := hNt
    obtain ⟨r24, -, a24⟩ := hX.ntW _ hpH 24#u64 (by simp) (by simp)
    have r24' : region K.toKLayout (fld N 24#u64) = .ntfn N := r24
    have eA : fld N 24#u64 = ntfnBtA N := by
      unfold fld ntfnBtA layout.ntfn.BOUND_TCB
      rfl
    have hbσ : L.mem σ (fld N 24#u64) = tm := by rw [eA]; exact hbt
    have hbρ : ρ (fld N 24#u64) = tm := by
      have e1 : view K.toKLayout c ρ (fld N 24#u64) = ρ (fld N 24#u64) := view_ntfn r24'
      have e2 : L.mem σ (fld N 24#u64) = view K.toKLayout c ρ (fld N 24#u64) :=
        hmm (fld N 24#u64) a24 (hL.nu (by rw [r24']; intro h; cases h))
      rw [← e1, ← e2]; exact hbσ
    obtain ⟨r, v, ha⟩ := hX.ntW _ hpH k h1 h2
    have own_e : OwnMap.own K.toKLayout (L.mem σ) (core.num.U64.wrapping_add N k) =
        ntfnOwner K.toKLayout (L.mem σ) N k.val := by
      simp only [OwnMap.own, r, v]
    have hcore : k.val ≠ 24 → OwnMap.own K.toKLayout (L.mem σ) (core.num.U64.wrapping_add N k) = .core (L.cpu σ) :=
      fun h24 => by
        rw [own_e, ntfnOwner, if_neg h24, hbσ, if_pos tH]
        exact congrArg Owner.core (affC tm tmT)
    refine ⟨⟨ha, ?_, hL.nu (by rw [r]; intro h; cases h),
      sr_nf hK (by rw [r]; intro h; cases h) (nf_ntfn r (fun _ => by rw [hbρ]; exact hHome))⟩, hcore⟩
    by_cases h24 : k.val = 24
    · exact Or.inr (by unfold GateOnly; rw [own_e, ntfnOwner, if_pos h24])
    · exact Or.inl (held_core (hcore h24))
  -- every word of `IrqRd`, once `current_ok` passed
  have gIrq : IrqOk st σ → ∀ b, Aligned b → IrqRd st (Heap.scBits K.toKLayout.heap) σ b → G b := by
    intro hok b ha hb
    have hrp := irq_rd_own hK0 hI hL hY E0.aff hok (lk := lk σ) hb
    have hnu := irq_rd_nu hI hL hY hb
    refine ⟨ha, hrp, hnu, ?_⟩
    rcases hb with ⟨o, ho, h8, rfl⟩ | ⟨k, h1, h2, h3, h4, h5, h6, rfl⟩ | hb | ⟨hne', rfl | hb⟩ | ⟨-, hb⟩ |
        ⟨k, hk', hk32, h8, rfl⟩
    · exact (gN o ho h8).2.2.2
    · exact (gC k h1 h2 h3 h4 h5 h6).2.2.2
    · exact (srw_sc hK hX (st_scH (K := K) hcs) (cscHome hok) hb).1
    · obtain ⟨r1, -, -, -, -⟩ := rel_facts hI hne'
      exact sr_tcb hK hX (show K.toKLayout.heap _ = some .tcb from r1) (rhHome hne').1 (o := 3464#u64)
        (by simp) (by simp) (by simp)
    · obtain ⟨-, -, -, r4, -⟩ := rel_facts hI hne'
      exact (srw_sc hK hX (st_scH (K := K) r4) (rhHome hne').2 hb).1
    · rcases hb with ⟨k, hk, rfl⟩ | ⟨-, ⟨k, hk, rfl⟩ | ⟨hb0, rfl | rfl⟩⟩
      · rcases hk with e | e | e | e
        · exact sr_tcb hK hX tH hHome (o := k) (by omega) (by omega) (by omega)
        · exact (gKey tm k tmT tmArm (by omega) (by omega) (by omega)).2.2.2
        · exact (gKey tm k tmT tmArm (by omega) (by omega) (by omega)).2.2.2
        · exact sr_tcb hK hX tH hHome (o := k) (by omega) (by omega) (by omega)
      · exact sr_tcb hK hX tH hHome (o := k) (by rcases hk with e | e | e <;> omega)
          (by rcases hk with e | e | e <;> omega) (by rcases hk with e | e | e <;> omega)
      · exact ((ntAll hb0).2 _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE])).1.2.2.2
      · exact ((ntAll hb0).2 _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB])).1.2.2.2
    · obtain ⟨p, hr, -, -⟩ := hY.cs k hk' hk32
      exact sr_nf hK (by rw [hr]; intro h; cases h) (nf_slot hr)
  have gFire : IrqOk st σ → ∀ b, Aligned b →
      FireRd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) σ b → G b := by
    intro hok b ha hb
    rcases hb with hb | ⟨y, hy, ya, k, h1, h2, h8, rfl⟩ | ⟨-, hb0, k, hk, h8, rfl⟩
    · exact gIrq hok b ha hb
    · exact gKey y k hy ya h1 h2 h8
    · exact ((ntAll hb0).2 k hk h8).1
  have gPl : ∀ b, IrqHnPl st σ b → G b := by
    rintro b (⟨k, hk, rfl⟩ | ⟨hb0, rfl | rfl⟩)
    · by_cases e : k.val = 3568
      · exact gKey tm k tmT tmArm (by omega) (by omega) (by omega)
      · exact gTm k (by rcases hk with e' | e' | e' | e' | e' | e' <;> omega)
          (by rcases hk with e' | e' | e' | e' | e' | e' <;> omega)
          (by rcases hk with e' | e' | e' | e' | e' | e' <;> omega)
          (by rcases hk with e' | e' | e' | e' | e' | e' <;> omega)
          (by rcases hk with e' | e' | e' | e' | e' | e' <;> omega)
          (by rcases hk with e' | e' | e' | e' | e' | e' <;> omega)
    · exact ((ntAll hb0).2 _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE])).1
    · exact ((ntAll hb0).2 _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB])).1  -- (gen 25) the waiting notification and its head waiter
  have eB : ρ (boundA tm) = N := by
    have g := gTm 3368#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)
    exact (kvR _ g).symm
  have hN0 : N ≠ 0#u64 := by rw [← eB]; exact hH3
  have hNt : N ∈ K.toKLayout.heap.ntfns := hI.2.2.1.2.2.bnd _ tmT hN0
  have hpH : K.toKLayout.heap N = some .ntfn := hNt
  obtain ⟨hbt, gA⟩ := ntAll hN0
  have gTS := (gA layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])).1
  have gHd := (gA layout.ep.HEAD (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])).1
  have eT : L.mem σ (epTSA N) = ρ (epTSA N) := kvR _ gTS
  have eH : L.mem σ (epHeadA N) = ρ (epHeadA N) := kvR _ gHd
  rw [eB] at hH4 hH5
  have hwσ : L.epState σ N = obj.NTFN_WAITING := by
    unfold LawfulStore.epState
    rw [eT]
    exact hH4
  set w := L.mem σ (epHeadA N) with hwdef
  have hwF : ρ (affA w) ≠ c := by rw [eH]; exact hH5
  have wT : w ∈ Heap.tcbs K.toKLayout.heap := by
    have h := (ntfn_wait_head h0 hpH).2.2 hwσ
    exact h
  have wH : K.toKLayout.heap w = some .tcb := wT
  -- `w`'s `AFFINITY`: a gate word, readable, owner kept by the view
  have aW : (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ (affA w) ∧ VO K c ρ (affA w)) ∧
      affA w ∉ K.user ∧ Aligned (affA w) := by
    have nuV : ∀ b, b ∉ K.user → b ∉ (userV K.toKLayoutV).user := fun b hb hu =>
      (mem_userV.1 hu).elim hb (not_vData_empty nv)
    obtain ⟨r, -, ha⟩ := hX.tcbW w wH 3520#u64 (by simp) (by simp) (by simp)
    have r' : region K.toKLayout (core.num.U64.wrapping_add w 3520#u64) = .tcb w := r
    have hpt : core.num.U64.wrapping_add w 3520#u64 ∉ K.ptes := fun hp => by
      have h := hK.none _ hp
      rw [r'] at h
      cases h
    have hnu : core.num.U64.wrapping_add w 3520#u64 ∉ K.user := hL.nu_tcb wT (k := 3520#u64) (by simp) (by simp)
    refine ⟨⟨⟨⟨Or.inr ?_, ha, nuV _ hnu⟩, hpt⟩, ?_⟩, hnu, ha⟩
    · show OwnMap.own K.toKLayout (L.mem σ) (fld w oAFFINITY) = .gate
      exact OwnMap.own_aff_gate hK0 wH _
    · show ownP K (view K.toKLayout c ρ) (fld w oAFFINITY) = ownP K ρ (fld w oAFFINITY)
      have hpt' : fld w oAFFINITY ∉ K.ptes := hpt
      rw [ownP_eq_own nv hpt', ownP_eq_own nv hpt']
      exact (OwnMap.own_aff_gate hK0 wH _).trans (OwnMap.own_aff_gate hK0 wH _).symm
  -- the read sets
  let Rn : U64 → Prop := IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ
  let Rs : U64 → Prop := fun b =>
    IrqHnRd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) irq σ b ∨
      (Aligned b ∧ FTree st (Heap.tcbs K.toKLayout.heap) σ b) ∨ (Aligned b ∧ FNt st σ b)
  let Rd : U64 → Prop := fun b => Rs b ∨ b = affA w
  have gRs : ∀ b, Rs b → G b := by
    rintro b ((hb | ⟨hok, ha, hb⟩ | hb) | ⟨-, ⟨y, hy, ya, k, h1, h2, h8, rfl⟩⟩ | ⟨-, ⟨-, hb0, k, hk, h8, rfl⟩⟩)
    · exact gR b hb
    · exact gFire hok b ha hb
    · exact gPl b hb
    · exact gKey y k hy ya h1 h2 h8
    · exact ((ntAll hb0).2 k hk h8).1
  have rPlS : ∀ k : U64, (k.val = 3520 ∨ k.val = 3568 ∨ k.val = 3368 ∨ k.val = 3328 ∨ k.val = 3336 ∨
      k.val = 3360) → Rs (core.num.U64.wrapping_add tm k) :=
    fun k hk => Or.inl (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩)))
  have rPl : ∀ k : U64, (k.val = 3520 ∨ k.val = 3568 ∨ k.val = 3368 ∨ k.val = 3328 ∨ k.val = 3336 ∨
      k.val = 3360) → Rd (core.num.U64.wrapping_add tm k) := fun k hk => Or.inl (rPlS k hk)
  have ftAl : ∀ b, FTree st (Heap.tcbs K.toKLayout.heap) σ b → Aligned b := by
    rintro b ⟨y, hy, -, k, -, h2, h8, rfl⟩
    exact field_aligned (hT y hy) (by omega) h8
  have rRn : ∀ b, Rn b → Rd b := fun b h => Or.inl (Or.inl (Or.inl h))
  have rNt : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → Rd (core.num.U64.wrapping_add N k) := fun k hk h8 =>
    Or.inl (Or.inr (Or.inr ⟨((ntAll hN0).2 k hk h8).1.1, hne, hN0, k, hk, h8, rfl⟩))
  let Ro : U64 → Prop := fun q => rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ q ∧ VO K c ρ q
  have nuV : ∀ b, b ∉ K.user → b ∉ (userV K.toKLayoutV).user := fun b hb hu =>
    (mem_userV.1 hu).elim hb (not_vData_empty nv)
  have gRo : ∀ b, G b → Ro b ∧ b ∉ K.user := fun b g =>
    ⟨⟨⟨⟨g.2.1, g.1, nuV b g.2.2.1⟩, g.2.2.2.2⟩, g.2.2.2.1.2⟩, g.2.2.1⟩
  have hR0 : ∀ q, Rd q → Ro q ∧ ¬ q ∈ K.user := by
    rintro q (hq | rfl)
    · exact gRo q (gRs q hq)
    · exact ⟨aW.1, aW.2.1⟩
  have hal : ∀ b, Rd b → Aligned b := by
    rintro b (hb | rfl)
    · exact (gRs b hb).1
    · exact aW.2.2
  -- the write sets (gen 23's: the tail declines or accepts without firing)
  let Wd : U64 → Prop := IrqFhWd st (Heap.scBits K.toKLayout.heap) σ
  let P : S → U64 → U64 → Prop := IrqFhP st (Heap.scBits K.toKLayout.heap) c σ
  have hPW : ∀ x q v, P x q v → Wd q := by
    rintro x q v (h | ⟨rfl, -⟩)
    · exact Or.inl h
    · exact Or.inr rfl
  have wSR : ∀ b, Aligned b → PathObl.WPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) b → SR K c ρ b →
      Aligned b ∧ PathObl.WPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) b ∧ b ∉ K.ptes ∧
        VO K c ρ b := fun b ha hw hs => ⟨ha, hw, hs.2, hs.1.2⟩
  have gW : ∀ b, Wd b → Aligned b ∧ PathObl.WPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) b ∧
      b ∉ K.ptes ∧ VO K c ρ b := by
    rintro b ((⟨hok, ha, hw, -⟩ | rfl | rfl) | rfl)
    · have hwp := irq_wr_own hI hL hok (lk := lk σ) hw
      refine wSR b ha hwp ?_
      rcases hw with ⟨o, ho, h8, rfl⟩ | ⟨k, h1, h2, h3, rfl⟩ | h | rfl | rfl | rfl | rfl
      · exact (gN o ho h8).2.2.2
      · exact sr_tcb hK hX htH hcur (o := k) (by omega) (by omega) h3
      · exact (srw_sc hK hX (st_scH (K := K) hcs) (cscHome hok) h.inSC).1
      · exact (srw_sc hK hX (st_scH (K := K) hcs) (cscHome hok) (scq_of hO hSs hcs).2.2.1.1).1
      · exact sr_tcb hK hX htH hcur (o := 3480#u64) (by simp) (by simp) (by simp)
      · exact sr_tcb hK hX htH hcur (o := 3488#u64) (by simp) (by simp) (by simp)
      · exact sr_tcb hK hX htH hcur (o := 3592#u64) (by simp) (by simp) (by simp)
    · have g := gN layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      exact wSR _ g.1 (held_core (hL.own_node _ (by simp [layout.node.CUR_TIME]))) g.2.2.2
    · have g := gN layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
      exact wSR _ g.1 (held_core (hL.own_node _ (by simp [layout.node.CONSUMED]))) g.2.2.2
    · have g := gC 3328#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)
      rw [Fl4Proofs.P1.stA_eq]
      refine wSR _ g.1 (held_core ?_) g.2.2.2
      rw [ownT _ 3328#u64 hcT (by simp) (by simp), tcbOwner, if_neg (by simp [GateField]),
        if_neg (by simp [TimerField]), if_neg (by simp [GField])]
      exact congrArg Owner.core (affC _ hcT)
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hWd : ∀ x, Wd x → Aligned x ∧ (¬ x ∈ K.user → HeldV c hs (ownP K μ x)) := by
    intro x hx
    obtain ⟨ha, hw, hp, hvo⟩ := gW x hx
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
      exact po_of_rperm hx.1.1.1
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  -- the checked writes
  have hpA : fld (L.curW σ) oAFFINITY ∉ K.ptes := (gC 3520#u64 (by simp) (by simp) (by simp) (Or.inl (by simp))
    (by simp) (by simp)).2.2.2.2
  have hμc : μ (fld (L.curW σ) oAFFINITY) = c := by
    have hpo : PO c hs (ownP K μ (fld (L.curW σ) oAFFINITY)) := by
      right; rw [ownP_eq_own nv hpA]; exact OwnMap.own_aff_gate hK0 htH μ
    rw [← hV.2.1 _ hpo]; exact hcur
  have hPal : ∀ x q v, P x q v → Aligned q := by
    rintro x q v ((⟨-, ha, -, -⟩ | rfl | rfl) | ⟨rfl, -⟩)
    · exact ha
    · exact (gN layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
    · exact (gN layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
    · rw [Fl4Proofs.P1.stA_eq]; exact field_aligned ht' (by simp) (by simp)
  have hStep : ∀ (x : S) (q v : U64) (x' : S), (fun _ : S => True) x → P x q v → st.write x q v = ok x' →
      PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs (L.mem x)
        (L.mem x') ∧ (fun _ : S => True) x' := by
    intro x q v x' _ hP hw
    rw [L.write_eq] at hw
    have e := ok_inj_ff hw
    subst e
    refine ⟨?_, trivial⟩
    have ha := hPal x q v hP
    rcases hP with hW | ⟨rfl, rfl, e3, e4⟩
    · have hnd : ¬ OwnMap.DecW K.toKLayout q := by
        rcases hW with ⟨-, -, hw', hn⟩ | rfl | rfl
        · exact irq_wr_nondec hK0 hI hL hw' hn
        · exact OwnMap.nondec_of_region hK0 (Or.inr (Or.inl ⟨_, hL.nd _ (by simp [layout.node.CUR_TIME])⟩))
        · exact OwnMap.nondec_of_region hK0 (Or.inr (Or.inl ⟨_, hL.nd _ (by simp [layout.node.CONSUMED])⟩))
      exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha hnd))
    · have es : stA (L.curW σ) = fld (L.curW σ) oSTATE := by rw [Fl4Proofs.P1.stA_eq]; rfl
      rw [es]
      exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_state hK0 hUO (m0 := μ) htH e4 hμc
        (fun hq' => absurd hq' (by rw [← es, e3]; simp [OwnMap.QueuedState, sched.TS_RESTART]))
        (fun hq' => absurd hq' (by simp [OwnMap.QueuedState, sched.TS_RUNNING]))))
  have hPd : ∀ x x' q v, (∀ w, Rn w → L.mem x' w = L.mem x w) → P x q v → P x' q v := by
    rintro x x' q v hag' (h | ⟨e1, e2, e3, e4⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e1, e2, by rw [hag' _ rSt]; exact e3, by rw [hag' _ rAf]; exact e4⟩
  -- disjointness from the clock words
  have tcbNe : ∀ y k o, y ∈ Heap.tcbs K.toKLayout.heap → k.val < 4096 → o.val < 4288 →
      core.num.U64.wrapping_add y k ≠ L.nodeAt σ (L.cpu σ) o := fun y k o hy hk ho =>
    tcb_node_ne hN hy (hT y hy) hk ho
  have ntNe : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → ∀ o : U64, o.val < 4288 →
      core.num.U64.wrapping_add N k ≠ L.nodeAt σ (L.cpu σ) o := by
    intro k hk h8 o ho e
    obtain ⟨r, -, -⟩ := hX.ntW _ hpH k hk h8
    have r' : region K.toKLayout (core.num.U64.wrapping_add N k) = .ntfn N := r
    rw [e, hL.nd o ho] at r'
    cases r'
  -- the run
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      localtimer.handle_timer_irq_local mm ar x a irq pl =
        interp mm ar (R.localtimer.handle_timer_irq_local irq pl) x a :=
    fun mm x a => congrFun (congrFun (irq_isProg S irq pl A ar mm) x) a
  have hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∃ r, interp (guard st Rd Wd) ar (R.localtimer.handle_timer_irq_local irq pl) s a = ok r ∧
        WithinM st ar (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ)
          (· ∈ K.user) c hs (L.mem x) (L.mem y)) (R.localtimer.handle_timer_irq_local irq pl) s a := by
    intro s hcs' hks hag
    have eN : ∀ o, L.nodeAt s (L.cpu s) o = L.nodeAt σ (L.cpu σ) o := fun o => by
      rw [hcs']; exact nodeAt_of_ksb hks _ o
    have hagS : ∀ b, Rs b → L.mem s b = L.mem σ b := fun b hb =>
      (hag b (Or.inl hb)).trans (kvR b (gRs b hb)).symm
    have hagR : ∀ b, Rn b → L.mem s b = L.mem σ b := fun b hb => hagS b (Or.inl (Or.inl hb))
    have eTM : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = tm := by
      rw [eN]; exact hagR _ (rN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
    have eirq : interrupt.irq_state st s irq = interrupt.irq_state st σ irq := by
      unfold interrupt.irq_state
      refine bind_guard_congr rfl fun i hi => ?_
      rw [eq_of_spec_fd (obj.ks_get.spec (L := L) s i), eq_of_spec_fd (obj.ks_get.spec (L := L) σ i), hks,
        hagR _ (rI i hi)]
    have hNs : NodePlaced st (Heap.tcbs K.toKLayout.heap) s (L.cpu s) := by rw [hcs']; exact hN.ksb hks
    have eCt : ctA (L := L) s = L.nodeAt σ (L.cpu σ) layout.node.CUR_TIME := eN _
    have eCn : cnA (L := L) s = L.nodeAt σ (L.cpu σ) layout.node.CONSUMED := eN _
    have eB' : L.mem s (boundA tm) = N := hagS _ (rPlS 3368#u64 (Or.inr (Or.inr (Or.inl (by simp)))))
    have rStT : Rd (core.num.U64.wrapping_add tm layout.tcb.STATE) := by
      show Rd (stA tm)
      rw [Fl4Proofs.P1.stA_eq]
      exact rPl 3328#u64 (by simp)
    have hBn : ∀ n, obj.Tcb.bound_ntfn st tm s = ok n → n ≠ 0#u64 →
        Rd (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) ∧
          Rd (core.num.U64.wrapping_add n layout.ntfn.BOUND_TCB) := by
      intro n en _
      rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en
      have en' : L.mem s (boundA tm) = n := ok_inj_ff en
      rw [eB'] at en'
      subst en'
      exact ⟨Or.inl (Or.inl (Or.inr (Or.inr (Or.inr ⟨hN0, Or.inl rfl⟩)))),
        Or.inl (Or.inl (Or.inr (Or.inr (Or.inr ⟨hN0, Or.inr rfl⟩))))⟩
    have hPT : PlanTm st Rd s tm := ⟨rPl 3520#u64 (Or.inl (by simp)), rPl 3568#u64 (Or.inr (Or.inl (by simp))),
      rPl 3368#u64 (Or.inr (Or.inr (Or.inl (by simp)))), fun _ => ⟨rStT, rPl 3336#u64 (by simp),
        rPl 3360#u64 (by simp), hBn⟩⟩
    obtain ⟨r, hr, -⟩ := spec_ex_fd (P0.localtimer.handle_timer_irq_local.p0 st ar s a irq pl LawfulStore.total hA)
    obtain ⟨r', hr'⟩ : ∃ r', localtimer.handle_timer_irq_local (gd st Rd P) ar s a irq pl = ok r' := by
      refine irq_pl_guardE ar (gS := gd st Rd P) (R := Rd)
        (fun _ i hi => by rw [hks]; exact rRn _ (rI i hi))
        (by rw [eN]; exact rRn _ (rN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])))
        (fun _ => by rw [eTM]; exact hPT) ?_ hr
      intro mx emx hle ei1 tip etip eb
      rw [hcs']
      have ei1σ : interrupt.irq_state st σ irq = ok interrupt.IRQ_TIMER := by rw [← eirq]; exact ei1
      -- the plan's `tm` / `ntfn`
      have hsp := same_plan_tm eb
      have hpl : pl.tm ≠ 0#u64 → pl.tm = tm ∧ pl.ntfn = N := by
        intro hp0
        rcases plan_facts' etip with ⟨t1, -⟩ | ⟨t1, -, -, t4⟩
        · exact absurd (hsp.1.symm.trans t1) hp0
        · have e1 : pl.tm = tm := by rw [← hsp.1, t1, eTM]
          refine ⟨e1, ?_⟩
          rw [← hsp.2, t4, hsp.1, e1, eB']
      -- the tail with an empty plan, at the view start, moved to `s`
      obtain ⟨p0, hp0⟩ : ∃ p0 : localtimer.TimerIrqPlan, p0.tm = 0#u64 := ⟨{ pl with tm := 0#u64 }, rfl⟩
      obtain ⟨r0, er0, -⟩ := spec_ex_fd (irqTailF_p0 st ar σ a irq (L.cpu σ) p0 LawfulStore.total hA)
      have g0 : irqTailF (gd st Rn P) ar σ a irq (L.cpu σ) p0 = ok r0 :=
        irqTail_guardT (gS := gd st Rn P) (R := Rn) (W := WAll P) ar hA hI
          (fun o h1 h2 => rN o h1 h2)
          (current_ok.guardC2 (gS := gd st Rn P) σ _ _ _ csc0 rAf (fun _ =>
            ⟨rSt, rC 3472#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp),
              rC 3664#u64 (by simp) (by simp) (by simp) (Or.inr (by simp)) (by simp) (by simp),
              rC 3464#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp),
              fun hne' => Or.inr (Or.inr (Or.inr (Or.inl ⟨hne', rfl⟩))),
              rN _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]),
              rC 3432#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp),
              rK _ (Or.inl rfl)⟩))
          (fun hok w ha hw => Or.inr (Or.inr (Or.inl ⟨hok, ha, hw⟩)))
          (fun hok w ha hw hn => fun _ _ => Or.inl (Or.inl ⟨hok, ha, hw, hn⟩))
          (fun _ i hi => rI i hi)
          (fun _ => rK _ (Or.inl rfl)) (fun _ => rK _ (Or.inr (Or.inl rfl)))
          (fun _ _ X hX haff => gd_write (Or.inr ⟨rfl, rfl, hX, haff.trans hc⟩))
          (fun _ => rK _ (Or.inr (Or.inr rfl)))
          (fun hok hi hhi => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hok, hi, hhi, Or.inl rfl⟩))))),
            fun lo hlo hne' => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hok, hi, hhi, Or.inr ⟨lo, hlo, hne', rfl⟩⟩)))))⟩)
          E0.asid (fun _ _ => Or.inl (Or.inr (Or.inl rfl))) (fun _ _ => Or.inl (Or.inr (Or.inr rfl)))
          emx hle ei1σ hp0 er0
      have gS0 : interp (gd st Rn P) ar (irqTailS irq (L.cpu σ) p0) σ a = ok r0 := by
        rw [irqTailS_eq, g0]; simp only [bind_ok, bind_tc_ok]
      obtain ⟨x0, s0', a0'⟩ := r0
      obtain ⟨s1', hs1⟩ := interp_agree_gd (st := st) (masksWr_plain st) (fun w hw => (gR w hw).1) hPal hPd
        (irqTailS irq (L.cpu σ) p0) (irqTailS_nz _ _ _) σ s a x0 s0' a0' hks hcs'
        (by rw [PlainStore.frame_masks_eq, PlainStore.frame_masks_eq]) (fun w hw => hagR w hw) gS0
      have hmono := interp_gd_mono (R' := Rd) (P' := P) (fun q hq' => rRn q hq') (fun _ _ _ h => h) _ s a _ hs1
      rw [irqTailS_eq] at hmono
      obtain ⟨r1, er1, -⟩ := bind_eq_ok hmono
      refine ⟨r1, ?_⟩
      rw [irqTailF_plan (gd st Rd P) ar s a irq (L.cpu σ) pl p0 ?_]
      · exact er1
      -- `fire_ok` declines with the plan as with the empty plan
      intro s1 a1 now ct eu _ _
      rw [PathObl.sched.update_timestamp.guard (gS := gd st Rd P) ar s a
        (by rw [eCt]; exact rRn _ (rN _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])))
        (fun _ _ => Or.inl (Or.inr (Or.inl eCt)))
        (by rw [eCn]; exact rRn _ (rN _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])))
        (fun _ _ => Or.inl (Or.inr (Or.inr eCn)))] at eu
      obtain ⟨n1, -, er⟩ := ut_now ar hA hNs eu
      simp only at er
      have c1 : L.cpu s1 = L.cpu σ := by rw [er, utW_cpu, hcs']
      have m0 : ∀ b, Aligned b → b ≠ L.nodeAt σ (L.cpu σ) layout.node.CUR_TIME →
          b ≠ L.nodeAt σ (L.cpu σ) layout.node.CONSUMED → L.mem s1 b = L.mem s b := fun b hb h1 h2 => by
        rw [er]
        exact utW_mem hNs n1 hb (by rw [eCt]; exact h1) (by rw [eCn]; exact h2)
      rw [fire_ok_tm0 (gd st Rd P) s1 (L.cpu σ) ct now hp0]
      refine fire_ok_guardWF (gS := gd st Rd P) (R := Rd) (s := σ) (s1 := s1) hI hL
        (fun b hb => Or.inl (Or.inr (Or.inl ⟨ftAl b hb, hb⟩))) c1 ?_ ?_ ct now ?_
      · rintro b ⟨y, hy, ya, k, h1, h2, h8, rfl⟩
        have ha := field_aligned (hT y hy) (by omega) h8
        rw [m0 _ ha (tcbNe y k _ hy (by omega) (by simp [layout.node.CUR_TIME]))
          (tcbNe y k _ hy (by omega) (by simp [layout.node.CONSUMED]))]
        exact hagS _ (Or.inr (Or.inl ⟨ha, ⟨y, hy, ya, k, h1, h2, h8, rfl⟩⟩))
      · intro hp0'
        exact (hpl hp0').1
      · intro hp0'
        obtain ⟨-, eNt⟩ := hpl hp0'
        have mNt : ∀ k : U64, k.val < 64 → k.val % 8 = 0 →
            L.mem s1 (core.num.U64.wrapping_add N k) = L.mem σ (core.num.U64.wrapping_add N k) := by
          intro k hk h8
          have ha := ((ntAll hN0).2 k hk h8).1.1
          rw [m0 _ ha (ntNe k hk h8 _ (by simp [layout.node.CUR_TIME])) (ntNe k hk h8 _ (by simp [layout.node.CONSUMED]))]
          exact hagS _ (Or.inr (Or.inr ⟨ha, hne, hN0, k, hk, h8, rfl⟩))
        have aw := aW.2.2
        have mAf : L.mem s1 (affA w) = ρ (affA w) := by
          rw [m0 _ aw (tcbNe w 3520#u64 _ wT (by simp) (by simp [layout.node.CUR_TIME]))
            (tcbNe w 3520#u64 _ wT (by simp) (by simp [layout.node.CONSUMED]))]
          exact hag _ (Or.inr rfl)
        refine fireTail_falseW (R := Rd) (gS := gd st Rd P) (x := s1) (ct := ct) (p := pl) (w := w)
          (by rw [eNt]; exact hN0)
          (by rw [eNt]; exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr ⟨hN0, Or.inl rfl⟩)))))
          (by rw [eNt]; exact rNt layout.ntfn.HEAD (by simp [layout.ntfn.HEAD]) (by simp [layout.ntfn.HEAD]))
          ?_ ?_ ?_
        · rw [eNt]
          unfold LawfulStore.epState
          rw [show epTSA N = core.num.U64.wrapping_add N layout.ep.TAIL_STATE from rfl,
            mNt _ (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])]
          exact hwσ
        · rw [eNt, show epHeadA N = core.num.U64.wrapping_add N layout.ep.HEAD from rfl,
            mNt _ (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])]
          rfl
        · intro _ _
          refine ⟨L.mem s1 (affA w), ?_, ?_⟩
          · rw [PathObl.gst_read (g := gd st Rd P) (R := Rd) (Or.inr rfl), L.read_eq]
          · rw [mAf, c1, hc]
            exact hwF
    rw [hp] at hr'
    refine ⟨r', interp_gd_guard (R' := Rd) (W := Wd) (fun q h => h) hPW _ s a r' hr', ?_⟩
    have hm := interp_gd (R := Rd) (P := P)
      (Q := fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs
        (L.mem x) (L.mem y)) (I := fun _ => True) hStep _ s a r' trivial hr'
    exact (interp_mguard _ s a r' hm).2
  exact ⟨hal, hR0, hWd, hRPO, hgo, fun x hx => (gW x hx).2.1, hne, wT⟩

set_option maxHeartbeats 32000000 in
/-- **U9's armed timer-interrupt program is `Safe` at a view start whose earliest thread is homed and whose bound
notification is waiting with a head waiter of another core** (module docstring). -/
theorem irq_wf_annV (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {irq : U64} {pl : localtimer.TimerIrqPlan} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hq : QPs K st σ) (hirq : irq.val < 128)
    (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hH : IrqWfR ρ c (ρ (tmA (L := L) σ))) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localtimer.handle_timer_irq_local irq pl) ∅ a)) := by
  obtain ⟨hal, hR0, hWd, hRPO, hgo, -, -, -⟩ := irq_wf_cert ar hA hK hU nv hV hJ hq hirq hc hl hmm hH
  have h := PathObl.safe_tr_wr (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar (moveHeldP hK) (ownDepP hK hU) (masksWr_plain st) (a := a)
    (R.localtimer.handle_timer_irq_local irq pl) (irq_noZero irq pl) hc
    (Ro := fun q => rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ q ∧ VO K c ρ q)
    (Rd := IrqWfRd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) irq σ) (Wd := IrqFhWd st (Heap.scBits K.toKLayout.heap) σ)
    hal hR0 hWd hRPO (fun x hx => hV.2.1 x hx) hgo
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

end main

end
end Fl4Proofs.P2.E2EP
