/-
# P2 (line p3mc, gen 23): the timer interrupt's certificate at a view start whose earliest thread is not homed

Handoff §27b item 1. At an irq view start `σ` (a bundle state `SlJAt`, `QPs`, the aligned kernel words core `c`'s
view of `ρ`, core `c`, locks `hs`) whose earliest thread `tm` of `c`'s timer tree is, in `ρ`, not on `c` (or there is
none), U9's re-annotated armed program (the extracted tree) is `Safe` at the physical memory `μ`.

The run at a state `s` carrying `ρ` on the read set is not the run at `σ`: really `tm`'s `AFFINITY` is not `c`, so
`plan_objects` stops there and the plan is empty (`irq_fh_guard2`, as gen 22's `irq_fh_guard`, with the head's IRQ
facts handed to the tail); the tail with the empty plan (`p.tm = 0`, no fire) reads only words the view keeps, so
its run at `s` is its run at `σ` (`irqTail_guardT` at `σ`, P1's invariant holding there) moved by
`interp_agree_gd`.

* `IrqFhRn` (the tail's reads, all kept by the view: `c`'s node words, the current thread's words off its timer and
  queue links, `IrqRdT` once `current_ok` passed, the current thread's SC's `CORE` word, three kernel-state words, the
  IRQ word, the ASID table and pools once `current_ok` passed), `IrqFhWn` / `IrqFhWd` (the tail's writes: `IrqWr`
  once `current_ok` passed, the two clock words, the current thread's `STATE`), `IrqFhP` (the checked store's
  write predicate: `IrqFhWn`, or `STATE := RUNNING` from `RESTART` with the thread's `AFFINITY` the core — the one
  write `stepOK_state` needs a state fact for).
* **`irq_fh_annV`**: `PathObl.safe_tr_wr` (gen 22) with `Rd := IrqFhRn ∪ {tm's AFFINITY}`, `Wd := IrqFhWd`; at
  each state `s` the run on `gd st Rd IrqFhP` gives both the guarded run (`interp_gd_guard`) and the per-write check
  (`interp_gd`, `StepOK` by `stepOK_nondec` / `stepOK_state`, i.e. the `withinM_of_within` variant keeping the
  current thread's `AFFINITY` asked for in the handoff: here the store checks it at the write).

No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.IrqFhGd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE oSTATE InW GateField TimerField GField
  tcbOwner)
open Fl4Proofs.P2.E2E (SP tr masksOf)
open Fl4Proofs.P2.Serial (Owner VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec NotForeign vn_of_nf nf_node nf_sc nf_slot nf_none nf_tcb TZero)

noncomputable section
open Classical

section sets
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **The tail's reads at a foreign-`tm` irq view start** (module docstring). -/
def IrqFhRn (Z : U64 → Nat) (irq : U64) (σ : S) (b : U64) : Prop :=
  (∃ o : U64, o.val < 4288 ∧ o.val % 8 = 0 ∧ b = L.nodeAt σ (L.cpu σ) o) ∨
  (∃ k : U64, 256 ≤ k.val ∧ k.val < 4096 ∧ k.val % 8 = 0 ∧ (k.val < 3528 ∨ 3576 ≤ k.val) ∧ k.val ≠ 3496 ∧
      k.val ≠ 3504 ∧ b = core.num.U64.wrapping_add (L.curW σ) k) ∨
  (IrqOk st σ ∧ Aligned b ∧ IrqRdT st Z σ b) ∨
  (L.mem σ (scA (L.curW σ)) ≠ 0#u64 ∧ b = scCoreA (L.mem σ (scA (L.curW σ)))) ∨
  (∃ o : U64, (o = layout.ks.CUR_DOMAIN ∨ o = layout.ks.DOMAIN_TIME ∨ o = layout.ks.KERNEL_ROOT) ∧
      b = core.num.U64.wrapping_add (L.ksb σ) o) ∨
  (irq.val < 128 ∧ ∃ i, interrupt.state_off irq = ok i ∧ b = core.num.U64.wrapping_add (L.ksb σ) i) ∨
  (IrqOk st σ ∧ ∃ hi : U64, hi.val < 2048 ∧ (b = atAF (L.ksb σ) hi ∨ ∃ lo : U64, lo.val < 512 ∧
      L.mem σ (atAF (L.ksb σ) hi) ≠ 0#u64 ∧ b = peAF (L.mem σ (atAF (L.ksb σ) hi)) lo))

/-- **The tail's writes but the current thread's `STATE`** (module docstring). -/
def IrqFhWn (Z : U64 → Nat) (σ : S) (b : U64) : Prop :=
  (IrqOk st σ ∧ Aligned b ∧ IrqWr st Z σ b ∧ b ≠ stA (L.curW σ)) ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ

/-- **The tail's writes** (module docstring). -/
def IrqFhWd (Z : U64 → Nat) (σ : S) (b : U64) : Prop :=
  IrqFhWn st Z σ b ∨ b = stA (L.curW σ)

/-- **The checked store's write predicate** (module docstring). -/
def IrqFhP (Z : U64 → Nat) (c : U64) (σ : S) (x : S) (q v : U64) : Prop :=
  IrqFhWn st Z σ q ∨ (q = stA (L.curW σ) ∧ v = sched.TS_RUNNING ∧ L.mem x (stA (L.curW σ)) = sched.TS_RESTART ∧
    L.mem x (affA (L.curW σ)) = c)

end sets

theorem heldV_of_heldBy {c : U64} {lk : U64 → Prop} {o : Owner U64 U64} (h : HeldBy c lk o) : HeldV c lk o := by
  cases o <;> exact h

section guard
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {R : U64 → Prop} {gS : machine.Store S} [PathObl.GRd gS st R] {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **`irq_fh_guard` with the head's IRQ facts handed to the tail** (module docstring). -/
theorem irq_fh_guard2 {s : S} {a : A} {irq : U64} {p : localtimer.TimerIrqPlan} {r : Bool × S × A}
    (hi : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))
    (h2 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) 3520#u64))
    (hoff : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s (affA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ L.cpu s)
    (htail : ∀ mx, layout.irq.MAX = ok mx → ¬ irq > mx →
      interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER → p.tm = 0#u64 →
      ∀ r', irqTailF st ar s a irq (L.cpu s) p = ok r' → irqTailF gS ar s a irq (L.cpu s) p = ok r')
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok r) :
    localtimer.handle_timer_irq_local gS ar s a irq p = ok r := by
  have hpl := plan_objects.guard_off (gS := gS) h1 h2 hoff
  revert h
  rw [irq_splitF st, irq_splitF gS, PathObl.gst_cur_cpu (g := gS), L.cur_cpu_eq]
  simp only [bind_ok, num_domains_ne_one_false, Bool.false_eq_true, ↓reduceIte]
  refine tr_bind_same (fun mx emx => ?_)
  refine tr_ite (fun _ h => h) (fun hle => ?_)
  have hlt : irq.val < 128 := by
    rw [eq_of_spec_fd layout.irq.MAX.spec] at emx
    have e := ok_inj_ff emx
    subst e
    scalar_tac
  have eirq : interrupt.irq_state gS s irq = interrupt.irq_state st s irq := by
    unfold interrupt.irq_state
    exact bind_guard_congr rfl fun i ei => PathObl.obj.ks_get.guard (gS := gS) s i (hi hlt i ei)
  rw [eirq]
  refine tr_bind_same (fun i1 ei1 => ?_)
  refine tr_ite (fun _ h => h) (fun hi1 => ?_)
  have e1 : i1 = interrupt.IRQ_TIMER := by
    by_contra hne
    exact hi1 (bne_iff_ne.mpr hne)
  subst e1
  rw [hpl]
  refine tr_bind_same (fun tip etip => ?_)
  refine tr_bind_same (fun b eb => ?_)
  refine tr_ite (fun hb => ?_) (fun _ h => h)
  subst hb
  have hp0 : p.tm = 0#u64 := (same_plan_tm eb).1.symm.trans (plan_objects_off_tm hoff etip)
  exact htail mx emx hle ei1 hp0 r

end guard

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 16000000 in
/-- **U9's armed timer-interrupt program is `Safe` at a view start whose earliest thread is not homed** (module
docstring). -/
theorem irq_fh_annV (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {irq : U64} {pl : localtimer.TimerIrqPlan} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hq : QPs K st σ) (hirq : irq.val < 128)
    (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hF : ρ (tmA (L := L) σ) ≠ 0#u64 → ρ (affA (ρ (tmA (L := L) σ))) ≠ c) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localtimer.handle_timer_irq_local irq pl) ∅ a)) := by
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
  -- the read sets
  let Rn : U64 → Prop := IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ
  let Rd : U64 → Prop := fun b => Rn b ∨ (tm ≠ 0#u64 ∧ b = core.num.U64.wrapping_add tm 3520#u64)
  let Ro : U64 → Prop := fun q => rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ q ∧ VO K c ρ q
  have nuV : ∀ b, b ∉ K.user → b ∉ (userV K.toKLayoutV).user := fun b hb hu =>
    (mem_userV.1 hu).elim hb (not_vData_empty nv)
  have gRo : ∀ b, G b → Ro b ∧ b ∉ K.user := fun b g =>
    ⟨⟨⟨⟨g.2.1, g.1, nuV b g.2.2.1⟩, g.2.2.2.2⟩, g.2.2.2.1.2⟩, g.2.2.1⟩
  have aG : tm ≠ 0#u64 → Ro (core.num.U64.wrapping_add tm 3520#u64) ∧
      core.num.U64.wrapping_add tm 3520#u64 ∉ K.user ∧ Aligned (core.num.U64.wrapping_add tm 3520#u64) := by
    intro hne
    obtain ⟨tmT, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne
    have tH : K.toKLayout.heap tm = some .tcb := tmT
    obtain ⟨r, -, ha⟩ := hX.tcbW tm tH 3520#u64 (by simp) (by simp) (by simp)
    have r' : region K.toKLayout (core.num.U64.wrapping_add tm 3520#u64) = .tcb tm := r
    have hpt : core.num.U64.wrapping_add tm 3520#u64 ∉ K.ptes := fun hp => by
      have h := hK.none _ hp
      rw [r'] at h
      cases h
    have hnu : core.num.U64.wrapping_add tm 3520#u64 ∉ K.user := hL.nu_tcb tmT (k := 3520#u64) (by simp) (by simp)
    refine ⟨⟨⟨⟨Or.inr ?_, ha, nuV _ hnu⟩, hpt⟩, ?_⟩, hnu, ha⟩
    · show OwnMap.own K.toKLayout (L.mem σ) (fld tm oAFFINITY) = .gate
      exact OwnMap.own_aff_gate hK0 tH _
    · show ownP K (view K.toKLayout c ρ) (fld tm oAFFINITY) = ownP K ρ (fld tm oAFFINITY)
      have hpt' : fld tm oAFFINITY ∉ K.ptes := hpt
      rw [ownP_eq_own nv hpt', ownP_eq_own nv hpt']
      exact (OwnMap.own_aff_gate hK0 tH _).trans (OwnMap.own_aff_gate hK0 tH _).symm
  have hR0 : ∀ q, Rd q → Ro q ∧ ¬ q ∈ K.user := by
    rintro q (hq' | ⟨hne, rfl⟩)
    · exact gRo q (gR q hq')
    · exact ⟨(aG hne).1, (aG hne).2.1⟩
  have hal : ∀ b, Rd b → Aligned b := by
    rintro b (hb | ⟨hne, rfl⟩)
    · exact (gR b hb).1
    · exact (aG hne).2.2
  -- the write sets
  let Wd : U64 → Prop := IrqFhWd st (Heap.scBits K.toKLayout.heap) σ
  let P : S → U64 → U64 → Prop := IrqFhP st (Heap.scBits K.toKLayout.heap) c σ
  have hPW : ∀ x q v, P x q v → Wd q := by
    rintro x q v (h | ⟨rfl, -⟩)
    · exact Or.inl h
    · exact Or.inr rfl
  -- the good write words: aligned, held at `σ`, no PTE word, owner kept by the view
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
  -- the run
  have kv : ∀ b, Rn b → L.mem σ b = ρ b := fun b hb => by
    have g := gR b hb
    rw [hmm b g.1 g.2.2.1]; exact g.2.2.2.1.1
  have hF' : tm ≠ 0#u64 → ρ (affA tm) ≠ c := by
    have e : L.mem σ (tmA (L := L) σ) = ρ (tmA (L := L) σ) :=
      kv _ (rN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
    intro hne
    have h1 := hF (by rw [← e]; exact hne)
    rwa [← e] at h1
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
    have hagR : ∀ b, Rn b → L.mem s b = L.mem σ b := fun b hb => (hag b (Or.inl hb)).trans (kv b hb).symm
    have eTM : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = tm := by
      rw [eN]; exact hagR _ (rN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
    have eirq : interrupt.irq_state st s irq = interrupt.irq_state st σ irq := by
      unfold interrupt.irq_state
      refine bind_guard_congr rfl fun i hi => ?_
      rw [eq_of_spec_fd (obj.ks_get.spec (L := L) s i), eq_of_spec_fd (obj.ks_get.spec (L := L) σ i), hks,
        hagR _ (rI i hi)]
    obtain ⟨r, hr, -⟩ := spec_ex_fd (P0.localtimer.handle_timer_irq_local.p0 st ar s a irq pl LawfulStore.total hA)
    have hgd : localtimer.handle_timer_irq_local (gd st Rd P) ar s a irq pl = ok r := by
      refine irq_fh_guard2 ar (gS := gd st Rd P) (R := Rd)
        (fun _ i hi => by rw [hks]; exact Or.inl (rI i hi))
        (by rw [eN]; exact Or.inl (rN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])))
        (fun hne => by rw [eTM] at hne ⊢; exact Or.inr ⟨hne, rfl⟩)
        (fun hne => by
          rw [eTM] at hne ⊢
          have ea : L.mem s (core.num.U64.wrapping_add tm 3520#u64) = ρ (core.num.U64.wrapping_add tm 3520#u64) :=
            hag _ (Or.inr ⟨hne, rfl⟩)
          show L.mem s (core.num.U64.wrapping_add tm 3520#u64) ≠ L.cpu s
          rw [ea, hcs', hc]
          exact hF' hne)
        ?_ hr
      intro mx emx hle ei1s hp0 r' hr'
      have ei1 : interrupt.irq_state st σ irq = ok interrupt.IRQ_TIMER := by rw [← eirq]; exact ei1s
      rw [hcs'] at hr' ⊢
      obtain ⟨r0, er0, -⟩ := spec_ex_fd (irqTailF_p0 st ar σ a irq (L.cpu σ) pl LawfulStore.total hA)
      have g0 : irqTailF (gd st Rn P) ar σ a irq (L.cpu σ) pl = ok r0 :=
        irqTail_guardT (gS := gd st Rn P) (R := Rn) (W := WAll P) ar hA hI
          (fun o h1 h2 => rN o h1 h2)
          (current_ok.guardC2 (gS := gd st Rn P) σ _ _ _ csc0 rAf (fun _ =>
            ⟨rSt, rC 3472#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp),
              rC 3664#u64 (by simp) (by simp) (by simp) (Or.inr (by simp)) (by simp) (by simp),
              rC 3464#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp),
              fun hne => Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, rfl⟩))),
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
            fun lo hlo hne => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hok, hi, hhi, Or.inr ⟨lo, hlo, hne, rfl⟩⟩)))))⟩)
          E0.asid (fun _ _ => Or.inl (Or.inr (Or.inl rfl))) (fun _ _ => Or.inl (Or.inr (Or.inr rfl)))
          emx hle ei1 hp0 er0
      have gS0 : interp (gd st Rn P) ar (irqTailS irq (L.cpu σ) pl) σ a = ok r0 := by
        rw [irqTailS_eq, g0]; simp only [bind_ok, bind_tc_ok]
      obtain ⟨x0, s0', a0'⟩ := r0
      obtain ⟨s1', hs1⟩ := interp_agree_gd (st := st) (masksWr_plain st) (fun w hw => (gR w hw).1) hPal hPd
        (irqTailS irq (L.cpu σ) pl) (irqTailS_nz _ _ _) σ s a x0 s0' a0' hks hcs'
        (by rw [PlainStore.frame_masks_eq, PlainStore.frame_masks_eq]) (fun w hw => hagR w hw) gS0
      have hst := interp_gd_st _ s a _ hs1
      have hr'' := irqTailS_run st ar hr'
      have e := ok_inj_ff (hst.symm.trans hr'')
      have hmono := interp_gd_mono (R' := Rd) (P' := P) (fun q hq' => Or.inl hq') (fun _ _ _ h => h) _ s a _ hs1
      rw [e, irqTailS_eq] at hmono
      obtain ⟨⟨x1, y1, z1⟩, er1, e1⟩ := bind_eq_ok hmono
      have e2 := ok_inj_ff e1
      rw [← e2]
      exact er1
    rw [hp] at hgd
    refine ⟨r, interp_gd_guard (R' := Rd) (W := Wd) (fun q h => h) hPW _ s a r hgd, ?_⟩
    have hm := interp_gd (R := Rd) (P := P)
      (Q := fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs
        (L.mem x) (L.mem y)) (I := fun _ => True) hStep _ s a r trivial hgd
    exact (interp_mguard _ s a r hm).2
  have h := PathObl.safe_tr_wr (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar (moveHeldP hK) (ownDepP hK hU) (masksWr_plain st) (a := a)
    (R.localtimer.handle_timer_irq_local irq pl) (irq_noZero irq pl) hc (Ro := Ro) (Rd := Rd) (Wd := Wd) hal hR0
    hWd hRPO (fun x hx => hV.2.1 x hx) hgo
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

end main

end
end Fl4Proofs.P2.E2EP
