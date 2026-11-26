/-
# P2 (line p3mc, gen 24): the timer interrupt's certificate at a view start whose earliest thread is homed

Handoff §27b item 3 / §28b item 1, for the starts whose earliest thread `tm` of `c`'s timer tree is, in `ρ`, on `c`
and whose bound notification, in `ρ`, wakes nobody (`NoWakeR`: none, or neither idle nor waiting, or idle with no
bound thread or one not blocked on receive). There every word the run reads is one the view keeps (`SR`): `c`'s node
words, the current thread / SC and the release head (homed, as gen 23), `tm`'s words (homed), its bound
notification's words (bound back to `tm`, homed), and the timer words of every thread armed in `c`'s tree (armed in
`ρ` too: `vn_timer`). So the run at a state `s` carrying `ρ` on the read set **is** the run at the view start `σ`,
where P1's invariant holds, moved by `interp_agree_gd`.

* `IrqHnPl` (`plan_objects`' reads of `tm`), `IrqHnRd` (`IrqFhRn` ∪ `FireRd` once `current_ok` passed ∪ `IrqHnPl`),
  `IrqHnWF` (the tree's link words and the notification's words but `BOUND_TCB`), `IrqHnWd`, `IrqHnP` (gen 23's
  `IrqFhP`, `IrqHnWF`, the height of an armed key keeping its core, `tm`'s deadline with `tm`'s `AFFINITY` the core —
  the checks `stepOK_height` / `stepOK_deadline` need, read from words of `IrqHnRd`).
* **`irq_hn_annV`**: `PathObl.safe_tr_wr` with `Rd := IrqHnRd`, `Wd := IrqHnWd`. At `σ` the run on
  `gd st Rd IrqHnP` is the real one: an accepted fire case by `irq_acc_fire_nwG` (P2/IrqHnG; the deadline write
  asked for `tm` only, `GED`), every other run by `irq_pl_guard` + `irqTail_guardP` (P2/IrqTailP) with `fire_ok`
  by `fire_ok_guardNW`. Then `interp_agree_gd` σ → `s`, `interp_gd_guard` and `interp_gd` (`StepOK` per write:
  `stepOK_nondec`, `stepOK_state`, `stepOK_height`, `stepOK_deadline`).

The waking fire case (the notification idle with `tm` blocked on receive, or waiting) is not covered: a waiting
notification's head may be another core's thread, whose `AFFINITY` the view rewrites (the counter-shape of §19), and
the waking tail (`fire_tail_wk2`) asks `PlanLk` / `SlotLay` facts. No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.IrqHnG
import Fl4Proofs.P2.IrqTailP
import Fl4Proofs.P2.IrqFhAnn
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

/-- **The bound notification of `tm` wakes nobody, in `ρ`** (module docstring; `NoWake` over a memory). -/
def NoWakeR (ρ : U64 → U64) (tm : U64) : Prop :=
  ρ (boundA tm) = 0#u64 ∨
  ((ρ (epTSA (ρ (boundA tm))) &&& 3#u64) ≠ obj.NTFN_IDLE ∧ (ρ (epTSA (ρ (boundA tm))) &&& 3#u64) ≠ obj.NTFN_WAITING) ∨
  ((ρ (epTSA (ρ (boundA tm))) &&& 3#u64) = obj.NTFN_IDLE ∧
    (ρ (ntfnBtA (ρ (boundA tm))) = 0#u64 ∨ ρ (stA (ρ (ntfnBtA (ρ (boundA tm))))) ≠ sched.TS_BLOCKED_ON_RECV))

section sets
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **`plan_objects`' reads of the earliest thread** (module docstring). -/
def IrqHnPl (σ : S) (b : U64) : Prop :=
  (∃ k : U64, (k.val = 3520 ∨ k.val = 3568 ∨ k.val = 3368 ∨ k.val = 3328 ∨ k.val = 3336 ∨ k.val = 3360) ∧
    b = core.num.U64.wrapping_add (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN)) k) ∨
  (L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN))) ≠ 0#u64 ∧
    (b = core.num.U64.wrapping_add (L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN))))
        layout.ntfn.TAIL_STATE ∨
      b = core.num.U64.wrapping_add (L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN))))
        layout.ntfn.BOUND_TCB))

/-- **The reads at a homed-`tm` irq view start** (module docstring). -/
def IrqHnRd (T : Set U64) (Z : U64 → Nat) (irq : U64) (σ : S) (b : U64) : Prop :=
  IrqFhRn st Z irq σ b ∨ (IrqOk st σ ∧ Aligned b ∧ FireRd st T Z σ b) ∨ IrqHnPl st σ b

/-- **The fire case's link and notification writes** (module docstring). -/
def IrqHnWF (T : Set U64) (σ : S) (b : U64) : Prop :=
  IrqOk st σ ∧ Aligned b ∧ (FTreeL st T σ b ∨ FNtW st σ b)

/-- **The writes at a homed-`tm` irq view start** (module docstring). -/
def IrqHnWd (T : Set U64) (Z : U64 → Nat) (σ : S) (b : U64) : Prop :=
  IrqFhWd st Z σ b ∨ IrqHnWF st T σ b ∨
  (IrqOk st σ ∧ ∃ y, y ∈ T ∧ FootLtArmed st σ (L.cpu σ) y ∧ b = thA y) ∨
  (IrqOk st σ ∧ b = tdA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN)))

/-- **The checked store's write predicate at a homed-`tm` irq view start** (module docstring). -/
def IrqHnP (T : Set U64) (Z : U64 → Nat) (c : U64) (σ : S) (x : S) (q v : U64) : Prop :=
  IrqFhP st Z c σ x q v ∨ IrqHnWF st T σ q ∨
  (IrqOk st σ ∧ ∃ y, y ∈ T ∧ FootLtArmed st σ (L.cpu σ) y ∧ q = thA y ∧
    (L.mem x (tdA y) ≠ 0#u64 → (L.mem x (thA y)).val >>> 8 = c.val ∧ v.val >>> 8 = c.val)) ∨
  (IrqOk st σ ∧ q = tdA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN)) ∧
    L.mem x (affA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN))) = c ∧
    (L.mem x (tdA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN))) ≠ 0#u64 ∨ v ≠ 0#u64 →
      (L.mem x (thA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN)))).val >>> 8 = c.val))

end sets

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 32000000 in
/-- **U9's armed timer-interrupt program is `Safe` at a view start whose earliest thread is homed and wakes nobody**
(module docstring). -/
theorem irq_hn_annV (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {irq : U64} {pl : localtimer.TimerIrqPlan} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hq : QPs K st σ) (hirq : irq.val < 128)
    (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hH : ρ (tmA (L := L) σ) ≠ 0#u64 ∧ ρ (affA (ρ (tmA (L := L) σ))) = c ∧ NoWakeR ρ (ρ (tmA (L := L) σ))) :
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
  -- (gen 24) values the view keeps
  have kvR : ∀ b, G b → L.mem σ b = ρ b := fun b g => by
    rw [hmm b g.1 g.2.2.1]; exact g.2.2.2.1.1
  have hY := E0.ly
  have eTm : L.mem σ (tmA (L := L) σ) = ρ (tmA (L := L) σ) :=
    kvR _ (gN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
  obtain ⟨hH0, hH1, hH2⟩ := hH
  have hne : tm ≠ 0#u64 := fun e => hH0 (by rw [← eTm]; exact e)
  obtain ⟨tmT, tmArm⟩ := tmin_facts (BXI.blk hI) h0.cur hne
  have tH : K.toKLayout.heap tm = some .tcb := tmT
  have hHome : ρ (fld tm oAFFINITY) = c := by
    have h' : ρ (affA (L.mem σ (tmA (L := L) σ))) = c := by rw [eTm]; exact hH1
    exact h'
  have hW2 : NoWakeR ρ tm := by
    have h' : NoWakeR ρ (L.mem σ (tmA (L := L) σ)) := by rw [eTm]; exact hH2
    exact h'
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
    · exact ((ntAll hb0).2 _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB])).1
  -- the read set
  let Rd : U64 → Prop := IrqHnRd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) irq σ
  have gRd : ∀ b, Rd b → G b := by
    rintro b (hb | ⟨hok, ha, hb⟩ | hb)
    · exact gR b hb
    · exact gFire hok b ha hb
    · exact gPl b hb
  have rn : ∀ b, IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ b → Rd b := fun b h => Or.inl h
  have rPl : ∀ k : U64, (k.val = 3520 ∨ k.val = 3568 ∨ k.val = 3368 ∨ k.val = 3328 ∨ k.val = 3336 ∨
      k.val = 3360) → Rd (core.num.U64.wrapping_add tm k) := fun k hk => Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩))
  have rF : IrqOk st σ → ∀ b, Aligned b →
      FireRd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) σ b → Rd b :=
    fun hok b ha hb => Or.inr (Or.inl ⟨hok, ha, hb⟩)
  let Ro : U64 → Prop := fun q => rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ q ∧ VO K c ρ q
  have nuV : ∀ b, b ∉ K.user → b ∉ (userV K.toKLayoutV).user := fun b hb hu =>
    (mem_userV.1 hu).elim hb (not_vData_empty nv)
  have gRo : ∀ b, G b → Ro b ∧ b ∉ K.user := fun b g =>
    ⟨⟨⟨⟨g.2.1, g.1, nuV b g.2.2.1⟩, g.2.2.2.2⟩, g.2.2.2.1.2⟩, g.2.2.1⟩
  have hR0 : ∀ q, Rd q → Ro q ∧ ¬ q ∈ K.user := fun q hq => gRo q (gRd q hq)
  have hal : ∀ b, Rd b → Aligned b := fun b hb => (gRd b hb).1
  -- the write sets
  let Wd : U64 → Prop := IrqHnWd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) σ
  let P : S → U64 → U64 → Prop := IrqHnP st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) c σ
  have hPW : ∀ x q v, P x q v → Wd q := by
    rintro x q v ((h | ⟨rfl, -⟩) | h | ⟨hok, y, hy, ya, rfl, -⟩ | ⟨hok, rfl, -⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨hok, y, hy, ya, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hok, rfl⟩))
  have wSR : ∀ b, Aligned b → PathObl.WPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) b → SR K c ρ b →
      Aligned b ∧ PathObl.WPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) b ∧ b ∉ K.ptes ∧
        VO K c ρ b := fun b ha hw hs => ⟨ha, hw, hs.2, hs.1.2⟩
  have gW : ∀ b, Wd b → Aligned b ∧ PathObl.WPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) b ∧
      b ∉ K.ptes ∧ VO K c ρ b := by
    rintro b (((⟨hok, ha, hw, -⟩ | rfl | rfl) | rfl) | ⟨hok, ha, hw | hw⟩ | ⟨hok, y, hy, ya, rfl⟩ | ⟨hok, rfl⟩)
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
    · obtain ⟨y, hy, ya, k, h1, h2, h8, rfl⟩ := hw
      exact wSR _ ha (held_core (ftree_own hL hT hy ya (by omega) (by omega) h8))
        (gKey y k hy ya (by omega) (by omega) h8).2.2.2
    · obtain ⟨-, hb0, k, hk, h8, h24, rfl⟩ := hw
      exact wSR _ ha (held_core (((ntAll hb0).2 k hk h8).2 h24)) ((ntAll hb0).2 k hk h8).1.2.2.2
    · have g := gKey y 3568#u64 hy ya (by simp) (by simp) (by simp)
      exact wSR _ g.1 (held_core (ftree_own hL hT hy ya (k := 3568#u64) (by simp) (by simp) (by simp))) g.2.2.2
    · have g := gKey tm 3528#u64 tmT tmArm (by simp) (by simp) (by simp)
      exact wSR _ g.1 (held_core (ftree_own hL hT tmT tmArm (k := 3528#u64) (by simp) (by simp) (by simp))) g.2.2.2
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
  have hpT : fld tm oAFFINITY ∉ K.ptes := (gTm 3520#u64 (by simp) (by simp) (by simp) (Or.inl (by simp))
    (by simp) (by simp)).2.2.2.2
  have hμT : μ (fld tm oAFFINITY) = c := by
    have hpo : PO c hs (ownP K μ (fld tm oAFFINITY)) := by
      right; rw [ownP_eq_own nv hpT]; exact OwnMap.own_aff_gate hK0 tH μ
    rw [← hV.2.1 _ hpo]; exact hHome
  have hPal : ∀ x q v, P x q v → Aligned q := fun x q v h => (gW q (hPW x q v h)).1
  have heapT : ∀ y, y ∈ Heap.tcbs K.toKLayout.heap → K.toKLayout.heap y = some .tcb := fun y hy => hy
  have hStep : ∀ (x : S) (q v : U64) (x' : S), (fun _ : S => True) x → P x q v → st.write x q v = ok x' →
      PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs (L.mem x)
        (L.mem x') ∧ (fun _ : S => True) x' := by
    intro x q v x' _ hP hw
    rw [L.write_eq] at hw
    have e := ok_inj_ff hw
    subst e
    refine ⟨?_, trivial⟩
    have ha := hPal x q v hP
    rcases hP with (hW | ⟨rfl, rfl, e3, e4⟩) | ⟨-, -, hw' | hw'⟩ | ⟨-, y, hy, -, rfl, hcnd⟩ | ⟨-, rfl, e3, hcnd⟩
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
    · have hnd : ¬ OwnMap.DecW K.toKLayout q := by
        obtain ⟨y, hy, -, k, h1, h2, -, rfl⟩ := hw'
        apply OwnMap.nondec_of_region hK0
        have e : (core.num.U64.wrapping_add y k).val - y.val = k.val := by
          rw [field_val (hT y hy) (by omega)]; omega
        exact Or.inl ⟨y, hL.tcb y hy k (by omega) (by omega), by omega, by omega, by omega, by omega, by omega⟩
      exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha hnd))
    · have hnd : ¬ OwnMap.DecW K.toKLayout q := by
        obtain ⟨hne', hb, k, hk, -, h24, rfl⟩ := hw'
        apply OwnMap.nondec_of_region hK0
        obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne'
        have hNt := hI.2.2.1.2.2.bnd _ q1 hb
        obtain ⟨p1, p2⟩ := hI.2.2.1.1.ntP _ hNt
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hY.ntw _ hNt k hk, ?_⟩))))
        rw [ntfn_word_val p1 p2 hk]
        omega
      exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha hnd))
    · have eh : thA y = fld y oTIMER_HEIGHT := rfl
      rw [eh]
      exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (stepOK_height hK0 hUO (m0 := μ) (heapT y hy) hcnd))
    · exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (stepOK_deadline hK0 hUO (m0 := μ) tH e3 hμT hcnd))
  have hPd : ∀ x x' q v, (∀ w, Rd w → L.mem x' w = L.mem x w) → P x q v → P x' q v := by
    rintro x x' q v hag' ((h | ⟨e1, e2, e3, e4⟩) | h | ⟨hok, y, hy, ya, e1, hcnd⟩ | ⟨hok, e1, e3, hcnd⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨e1, e2, by rw [hag' _ (rn _ rSt)]; exact e3, by rw [hag' _ (rn _ rAf)]; exact e4⟩)
    · exact Or.inr (Or.inl h)
    · have yT := hT _ hy
      have d1 : Rd (tdA y) := rF hok _ (field_aligned yT (by simp) (by simp))
        (Or.inr (Or.inl ⟨y, hy, ya, 3528#u64, by simp, by simp, by simp, rfl⟩))
      have d2 : Rd (thA y) := rF hok _ (field_aligned yT (by simp) (by simp))
        (Or.inr (Or.inl ⟨y, hy, ya, 3568#u64, by simp, by simp, by simp, rfl⟩))
      refine Or.inr (Or.inr (Or.inl ⟨hok, y, hy, ya, e1, ?_⟩))
      rw [hag' _ d1, hag' _ d2]
      exact hcnd
    · have d0 : Rd (affA tm) := rPl 3520#u64 (Or.inl (by simp))
      have d1 : Rd (tdA tm) := rF hok _ (field_aligned (hT _ tmT) (by simp) (by simp))
        (Or.inr (Or.inl ⟨tm, tmT, tmArm, 3528#u64, by simp, by simp, by simp, rfl⟩))
      have d2 : Rd (thA tm) := rPl 3568#u64 (Or.inr (Or.inl (by simp)))
      have e3' : L.mem x (affA tm) = c := e3
      have hc' : L.mem x (tdA tm) ≠ 0#u64 ∨ v ≠ 0#u64 → (L.mem x (thA tm)).val >>> 8 = c.val := hcnd
      have d0' : L.mem x' (affA tm) = L.mem x (affA tm) := hag' _ d0
      have d1' : L.mem x' (tdA tm) = L.mem x (tdA tm) := hag' _ d1
      have d2' : L.mem x' (thA tm) = L.mem x (thA tm) := hag' _ d2
      have hc'' : L.mem x' (tdA tm) ≠ 0#u64 ∨ v ≠ 0#u64 → (L.mem x' (thA tm)).val >>> 8 = c.val := by
        rw [d1', d2']; exact hc'
      exact Or.inr (Or.inr (Or.inr ⟨hok, e1, d0'.trans e3', hc''⟩))
  -- `NoWake` at the view start
  have hNWσ : NoWake st σ := by
    have e1 : ρ (boundA tm) = N := by
      have g := gTm 3368#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)
      exact (kvR _ g).symm
    unfold NoWake
    show N = 0#u64 ∨ (L.epState σ N ≠ obj.NTFN_IDLE ∧ L.epState σ N ≠ obj.NTFN_WAITING) ∨
      (L.epState σ N = obj.NTFN_IDLE ∧
        (L.mem σ (ntfnBtA N) = 0#u64 ∨ L.mem σ (stA (L.mem σ (ntfnBtA N))) ≠ sched.TS_BLOCKED_ON_RECV))
    by_cases hb0 : N = 0#u64
    · exact Or.inl hb0
    obtain ⟨hbt, gA⟩ := ntAll hb0
    have eT : L.mem σ (epTSA N) = ρ (epTSA N) :=
      kvR _ (gA layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])).1
    have eS : L.epState σ N = ρ (epTSA N) &&& 3#u64 := by
      unfold LawfulStore.epState
      rw [eT]
    have eB : L.mem σ (ntfnBtA N) = ρ (ntfnBtA N) :=
      kvR _ (gA layout.ntfn.BOUND_TCB (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB])).1
    have eSt : L.mem σ (stA tm) = ρ (stA tm) := by
      rw [Fl4Proofs.P1.stA_eq]
      exact kvR _ (gTm 3328#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp))
    have hW3 := hW2
    unfold NoWakeR at hW3
    rw [e1] at hW3
    rcases hW3 with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h hb0
    · exact Or.inr (Or.inl ⟨by rw [eS]; exact h1, by rw [eS]; exact h2⟩)
    · refine Or.inr (Or.inr ⟨by rw [eS]; exact h1, ?_⟩)
      rw [← eB, hbt] at h2
      rw [hbt, eSt]
      exact h2
  -- the run at the view start, on the checked store
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      localtimer.handle_timer_irq_local mm ar x a irq pl =
        interp mm ar (R.localtimer.handle_timer_irq_local irq pl) x a :=
    fun mm x a => congrFun (congrFun (irq_isProg S irq pl A ar mm) x) a
  obtain ⟨r, hr, -⟩ := spec_ex_fd (P0.localtimer.handle_timer_irq_local.p0 st ar σ a irq pl LawfulStore.total hA)
  have hgσ : localtimer.handle_timer_irq_local (gd st Rd P) ar σ a irq pl = ok r := by
    by_cases hfa : r.1 = true ∧ IrqFire st ar σ a
    · obtain ⟨b, s', a'⟩ := r
      obtain ⟨hb, hq'⟩ := hfa
      simp only at hb
      subst hb
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, eok, -⟩ := fire_eqs ar hA hq' hr
      obtain ⟨hmr, hsct, hcore⟩ := current_ok_true eok
      obtain ⟨-, haff, -, -⟩ := may_run_here_true hmr
      have hok : IrqOk st σ := ⟨haff, hsct, hcore⟩
      exact irq_acc_fire_nwG (gS := gd st Rd P) (R := Rd) (W := WAll P) ar hA hI hL hY.ntw E0.nth hq' hNWσ
        (fun hok' w ha hw => rF hok' w ha hw)
        (fun hok' w ha hw hn => fun _ _ => by
          rcases hw with hw | hw | hw
          · exact Or.inl (Or.inl (Or.inl ⟨hok', ha, hw, hn⟩))
          · exact Or.inr (Or.inl ⟨hok', ha, Or.inl hw⟩)
          · exact Or.inr (Or.inl ⟨hok', ha, Or.inr hw⟩))
        (fun _ i hi => rn _ (rI i hi)) (fun _ => rn _ (rK _ (Or.inl rfl)))
        (fun _ => rn _ (rK _ (Or.inr (Or.inl rfl))))
        (fun _ X hX haff => gd_write (Or.inl (Or.inr ⟨rfl, rfl, hX, haff.trans hc⟩)))
        (fun X y v hy ya hcnd => gd_write (Or.inr (Or.inr (Or.inl ⟨hok, y, hy, ya, rfl, fun h => by
          rw [← hc]; exact hcnd h⟩))))
        (fun X y v hy ya hyt ha1 _ hcnd => by
          subst hyt
          exact gd_write (Or.inr (Or.inr (Or.inr ⟨hok, rfl, ha1.trans hc, fun h => by
            rw [← hc]; exact hcnd h⟩)))) hr
    · refine irq_pl_guard ar (gS := gd st Rd P) (R := Rd)
        (fun _ i hi => rn _ (rI i hi))
        (rn _ (rN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])))
        (fun _ => ⟨rPl 3520#u64 (Or.inl (by simp)), rPl 3568#u64 (Or.inr (Or.inl (by simp))),
          rPl 3368#u64 (Or.inr (Or.inr (Or.inl (by simp)))), fun _ => ⟨?_, rPl 3336#u64 (by simp),
          rPl 3360#u64 (by simp), fun n en hn0 => ?_⟩⟩) ?_ hr
      · show Rd (stA tm)
        rw [Fl4Proofs.P1.stA_eq]
        exact rPl 3328#u64 (by simp)
      · rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) σ _)] at en
        have en' : L.mem σ (boundA tm) = n := ok_inj_ff en
        subst en'
        exact ⟨Or.inr (Or.inr (Or.inr ⟨hn0, Or.inl rfl⟩)), Or.inr (Or.inr (Or.inr ⟨hn0, Or.inr rfl⟩))⟩
      · intro mx emx hle ei1 tip etip eb hrt
        exact irqTail_guardP (gS := gd st Rd P) (R := Rd) (W := WAll P) ar hA hI
          (fun o h1 h2 => rn _ (rN o h1 h2))
          (current_ok.guardC2 (gS := gd st Rd P) σ _ _ _ csc0 (rn _ rAf) (fun _ =>
            ⟨rn _ rSt, rn _ (rC 3472#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)),
              rn _ (rC 3664#u64 (by simp) (by simp) (by simp) (Or.inr (by simp)) (by simp) (by simp)),
              rn _ (rC 3464#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)),
              fun hne' => rn _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne', rfl⟩)))),
              rn _ (rN _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])),
              rn _ (rC 3432#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)),
              rn _ (rK _ (Or.inl rfl))⟩))
          (fun hok w ha hw => rn _ (Or.inr (Or.inr (Or.inl ⟨hok, ha, hw⟩))))
          (fun hok w ha hw hn => fun _ _ => Or.inl (Or.inl (Or.inl ⟨hok, ha, hw, hn⟩)))
          (fun _ i hi => rn _ (rI i hi))
          (fun _ => rn _ (rK _ (Or.inl rfl))) (fun _ => rn _ (rK _ (Or.inr (Or.inl rfl))))
          (fun _ _ X hX haff => gd_write (Or.inl (Or.inr ⟨rfl, rfl, hX, haff.trans hc⟩)))
          (fun _ => rn _ (rK _ (Or.inr (Or.inr rfl))))
          (fun hok hi hhi => ⟨rn _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hok, hi, hhi, Or.inl rfl⟩)))))),
            fun lo hlo hne' => rn _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hok, hi, hhi, Or.inr ⟨lo, hlo, hne', rfl⟩⟩))))))⟩)
          E0.asid (fun _ _ => Or.inl (Or.inl (Or.inr (Or.inl rfl)))) (fun _ _ => Or.inl (Or.inl (Or.inr (Or.inr rfl))))
          emx hle ei1
          (fun hok s1 a1 now eu _ => by
            obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
            simp only at er
            exact fire_ok_guardNW hI hL hY.ntw (fun w ha hw => rF hok w ha hw) hNWσ (by rw [er, utW_ksb])
              (by rw [er, utW_cpu]) (fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2) etip eb _ _)
          (fun h1 h2 => hfa ⟨h1, h2⟩) hrt
  rw [hp] at hgσ
  -- every state carrying `ρ` on the reads runs as the view start
  have hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∃ r, interp (guard st Rd Wd) ar (R.localtimer.handle_timer_irq_local irq pl) s a = ok r ∧
        WithinM st ar (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ)
          (· ∈ K.user) c hs (L.mem x) (L.mem y)) (R.localtimer.handle_timer_irq_local irq pl) s a := by
    intro s hcs' hks hag
    have hagR : ∀ b, Rd b → L.mem s b = L.mem σ b := fun b hb => (hag b hb).trans (kvR b (gRd b hb)).symm
    obtain ⟨x0, s0', a0'⟩ := r
    obtain ⟨s1', hs1⟩ := interp_agree_gd (st := st) (masksWr_plain st) hal hPal hPd
      (R.localtimer.handle_timer_irq_local irq pl) (irq_noZero irq pl) σ s a x0 s0' a0' hks hcs'
      (by rw [PlainStore.frame_masks_eq, PlainStore.frame_masks_eq]) hagR hgσ
    refine ⟨_, interp_gd_guard (R' := Rd) (W := Wd) (fun q h => h) hPW _ s a _ hs1, ?_⟩
    have hm := interp_gd (R := Rd) (P := P)
      (Q := fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs
        (L.mem x) (L.mem y)) (I := fun _ => True) hStep _ s a _ trivial hs1
    exact (interp_mguard _ s a _ hm).2
  have h := PathObl.safe_tr_wr (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar (moveHeldP hK) (ownDepP hK hU) (masksWr_plain st) (a := a)
    (R.localtimer.handle_timer_irq_local irq pl) (irq_noZero irq pl) hc (Ro := Ro) (Rd := Rd) (Wd := Wd) hal hR0
    hWd hRPO (fun x hx => hV.2.1 x hx) hgo
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

end main

end
end Fl4Proofs.P2.E2EP
