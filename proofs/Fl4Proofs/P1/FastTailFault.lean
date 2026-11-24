/-
# m62's `FaultNvm` derived (FL4 #16, m70)

At the state where `fastpath.fault` is entered (`BXI`, `XG` there, what
`budget_ok.bxc` leaves), the handler an accepted fault fast path switches to
is current and `Running` at the run's end (`faultNvm_of`), so not
`TS_RUNNING_VM`: the fault run up to `s15` is m61 / m63's (`FaultKeep`,
`finKeep15`), the handler's SC is active (the handler is blocked on receive,
`BoundInv.sact`) so well formed, `unblock_sporadic` keeps it well formed
(`unblock_sporadic_wf`), and the tail is `switch_to_nvm` (FastTailNvm).
`FaultNvmPre.of_asid`: m67's `FaultNvmPre` [J] at every entry state with
`EntryInv` and `AsidOff`.
-/
import Fl4Proofs.P1.FastTailNvm
import Fl4Proofs.P1.FastFaultEnt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- `unblock_sporadic` keeps the thread's SC well formed. -/
theorem unblock_sporadic_wf {X s15 : S} {d : obj.Tcb} {A : U64} {sb : Nat} (h : UsOff (L := L) X d A sb)
    (hW : RefillsWF st X (L.mem X (scA d)) sb)
    (e : endpoint.unblock_sporadic st X d = ok s15) : RefillsWF st s15 (L.mem X (scA d)) sb := by
  unfold endpoint.unblock_sporadic at e
  rw [eq_of_spec_fd (obj.Tcb.sc.spec (L := L) X d)] at e
  simp only [bind_ok, bind_tc_ok] at e
  rw [sc_sporadic_eq] at e; simp only [bind_ok, bind_tc_ok] at e
  by_cases h0 : L.mem X (scA d) = 0#u64
  · simp only [h0, ↓reduceIte, Bool.false_eq_true, bind_ok, bind_tc_ok] at e
    obtain rfl := ok_inj_ff e
    exact hW
  simp only [h0, ↓reduceIte] at e
  by_cases h1 : (L.mem X (sporA (L.mem X (scA d))) != 0#u64) = true
  swap
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, bind_ok, bind_tc_ok] at e
    obtain rfl := ok_inj_ff e
    exact hW
  simp only [h1, ↓reduceIte] at e
  rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X)] at e
  simp only [bind_ok, bind_tc_ok] at e
  obtain ⟨b1, hb1, -⟩ := spec_ex_fd (sc_ne.spec (L.mem X (scA d)) (L.mem X (L.nodeA X layout.node.CUR_SC)))
  rw [hb1] at e; simp only [bind_ok, bind_tc_ok] at e
  cases b1
  · simp only [Bool.false_eq_true, ↓reduceIte] at e
    obtain rfl := ok_inj_ff e
    exact hW
  · simp only [↓reduceIte] at e
    have := sporadic.unblock_check.wf hW h.rp
    rw [e, WP.spec_ok] at this; exact this

variable {A : Type _} (ar : machine.Arch A)

/-- The handler an accepted fault fast path finds is blocked on receive (it
heads the endpoint's queue, `EpsWit`; the endpoint typed by
`EntryHyps0.tmoOK`, as in `faultEntAt_of`). -/
theorem faultRecv_of {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {P3Ok : S → Prop}
    (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s : S} {t : obj.Tcb} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (et : sched.cur_thread st s = ok t) {ptr badge dest r : U64} (hc : FaultChecks st s t ptr badge dest r) :
    L.mem s (stA dest) = sched.TS_BLOCKED_ON_RECV := by
  have et' : t = L.curW s := by
    rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)] at et; exact (ok_inj_ff et).symm
  obtain ⟨-, -, hcap⟩ := E0.tmoOK Ac s hG hI
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  obtain ⟨sl, x, y, g, gr, esl, ecap, -⟩ := hc.cap
  have hpH : H ptr = some .ep := by
    have h1 := hcap layout.tcb.SLOT_FAULT_HANDLER (Or.inr rfl)
    rw [← et', esl, WP.spec_ok, ecap, WP.spec_ok] at h1
    exact h1.1 ptr badge x y g gr rfl
  obtain ⟨E, EQ, hW⟩ := hSQ.eps
  obtain ⟨w1, -, -, w4, -, w6⟩ := hW
  have hpE : ptr ∈ E := (w6.2.2.1 ptr).2 (Or.inl hpH)
  obtain ⟨-, -, hQ⟩ := w1 ptr hpE
  have hst : L.epState s ptr = obj.EP_RECV := by
    have h1 := hc.ep
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) s ptr)] at h1; exact ok_inj_ff h1
  have hst2 : L.epState s ptr = 2#u64 := by rw [hst, ep_recv_val']
  have hhd : dest = L.mem s (epHeadA ptr) := by
    have h1 := hc.head
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) s ptr)] at h1; exact (ok_inj_ff h1).symm
  cases hl : EQ ptr with
  | nil =>
    have h1 := (w6.2.2.2.2.2 ptr hpE hl).1 hpH
    rw [hst2] at h1; exact absurd h1 (by decide)
  | cons y0 rest =>
    rw [hl] at hQ
    have hy0 : y0 = dest := by
      have h1 := hQ.head
      simp only [LawfulStore.epQ, List.headD_cons] at h1
      rw [hhd]; exact h1.symm
    subst hy0
    have hmem : y0 ∈ EQ ptr := by rw [hl]; exact List.mem_cons_self
    obtain ⟨-, -, hbl⟩ := w4 ptr hpE y0 hmem
    obtain ⟨k1, -, k3⟩ := w6.2.2.2.2.1 ptr hpE y0 hmem
    rcases hbl with e | e | e
    · have := k1 e; rw [hst2] at this; exact absurd this (by decide)
    · exact e
    · have := k3 e; rw [hst2] at this; exact absurd this (by decide)

set_option maxHeartbeats 1600000 in
/-- **m70's `faultNvm_ofR` over the fault** (pf1): a run of `faultTailG … f ty`
from checks that held (an UnknownSyscall or a VM fault, `set_fault f` writing
`sfG … ty w0 w1 w2`) ends with the handler current and not `TS_RUNNING_VM`. -/
theorem faultNvm_tailG {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar)
    {s : S} {a : A} {t : obj.Tcb} {f : error.Fault} {ty w0 w1 w2 : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hrecv0 : ∀ {ptr badge dest r : U64}, FaultChecks st s t ptr badge dest r →
      L.mem s (stA dest) = sched.TS_BLOCKED_ON_RECV)
    (hF : FaultEntAt (L := L) T Cs Ω U Sg Rp s t)
    (hty' : ty = fl4_abi.consts.fault.UnknownSyscall ∨ ty = fl4_abi.consts.fault.VMFault)
    (hsf : faults.set_fault st s t f = ok (sfG (L := L) s t ty w0 w1 w2))
    {ptr badge dest r : U64} {sF : S} {aF : A} (hc : FaultChecks st s t ptr badge dest r)
    (hfast : faultTailG st ar s a t f ty ptr badge dest r = ok (true, sF, aF)) :
    L.mem sF (stA (L.curW sF)) ≠ sched.TS_RUNNING_VM := by
  have hrecv := hrecv0 hc
  obtain ⟨⟨Q, R, hSQ⟩, hB, hX, hSg, hS⟩ := hI
  have hX0 : ScExtra0 st T Cs Scs Nt s := hX.2.2.toScExtra0
  have hO := hX.1
  rw [faultTailG_eq st ar a t f ty ptr badge dest r hsf] at hfast
  have hf0 := hfast
  unfold faultTail2G at hfast
  obtain ⟨rb, hbuf, h1⟩ := bind_eq_ok hfast
  obtain ⟨⟨sent, S6⟩, hmrs, h2⟩ := bind_eq_ok h1
  try simp only [uncurry_apply_pair] at h2
  obtain ⟨mi, hmi, h3⟩ := bind_eq_ok h2
  obtain ⟨S7, hS7, h4⟩ := bind_eq_ok h3
  obtain ⟨S8, hS8, -⟩ := bind_eq_ok h4
  rw [faultTail2G_eq ar _ a t ty dest r badge hbuf hmrs hmi hS7 hS8, faultTail3_eq] at hf0
  obtain ⟨s15, h15, hfin⟩ := bind_eq_ok hf0
  obtain ⟨hr, rest, E⟩ := hF.2 ptr badge dest r hc
  obtain ⟨-, -, K⟩ := faultReads_ofG ar hty' E hbuf hmrs hS7 hS8
  have HF := here_facts (L := L) hc.here
  have hT := E.hT
  have hdT : dest ∈ T := E.hq.mem dest (by simp)
  have hd' := hT dest hdT
  have hN := E.hN
  have hcC := E.hcC
  have hΩ := E.hΩ
  -- the handler's SC: active (blocked on receive), well formed
  have hdsc : L.mem s (scA dest) ∈ Scs := (hX0.bound dest hdT HF.sc).1
  obtain ⟨hPl, hZ7⟩ := hO.sc _ hdsc
  have scW : ∀ b, Aligned b → InSC (L.mem s (scA dest)) (Z (L.mem s (scA dest))) b → b ∈ Ω :=
    fun b hb h => hS.sub _ ((hS.all _ hdsc).2.2 b hb h)
  have spWF : L.mem s (sporA (L.mem s (scA dest))) ≠ 0#u64 →
      RefillsWF st s (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    fun h => (hS.all _ hdsc).1 ((hS.act _ hdsc).1 (hS.spor _ hdsc h))
  have hact : L.mem s (scA dest) ∈ Ac :=
    hB.sact dest hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hrecv)))))))) HF.sc
  have hWs : RefillsWF st s (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    (hS.all _ hdsc).1 ((hS.act _ hdsc).1 hact)
  have nrt : ∀ c ∈ Scs, ∀ b, InSC c (Z c) b → b ≠ rTcbA r := fun c hc' b hin e => by
    have := hO.rpSc r hr _ hc'; subst e; unfold InSC at hin; rw [rTcbA_val0] at hin; omega
  have hU := usOff_of E K scW (hS.sub _ (hS.spSg _ hdsc)) spWF (hO.rpSc r hr _ hdsc) hZ7 hPl.fits
  have w15 := unblock_sporadic_fr hU h15
  have esc14 : L.mem (fS14 (L := L) S8 t dest r) (scA dest) = L.mem s (scA dest) :=
    K.tcb dest hdT 3464#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hW14 : RefillsWF st (fS14 (L := L) S8 t dest r) (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    hWs.agree fun b hb hin => K.omg b (scW b hb hin) (nrt _ hdsc b hin)
  have hW15 : RefillsWF st s15 (L.mem s (scA dest)) (Z (L.mem s (scA dest))) := by
    have := unblock_sporadic_wf hU (by rw [esc14]; exact hW14) h15
    rw [esc14] at this; exact this
  rw [esc14] at w15
  have K15 := finKeep15 hT hN hcC hΩ K scW w15
  -- the handler `Running` at `s15`
  have sA : Aligned (stA dest) := by rw [stA_eq]; exact field_aligned hd' (by simp) (by simp)
  have st14 : L.mem (fS14 (L := L) S8 t dest r) (stA dest) = sched.TS_RUNNING := by
    unfold fS14; exact L.mem_wr_same sA
  have st15 : L.mem s15 (stA dest) = sched.TS_RUNNING := by
    rw [w15.mem_eq sA ?_]; exact st14
    rintro (hin | e)
    · exact out_ne_field (hΩ _ (scW _ sA hin.inSC)) hdT hd' (K := 3328#u64) (by simp) (by rw [stA_eq])
    · have eR : L.nodeA (fS14 (L := L) S8 t dest r) layout.node.REPROGRAM =
          L.nodeAt s (L.cpu s) layout.node.REPROGRAM := by
        unfold LawfulStore.nodeA; rw [K.cpu, nodeAt_of_ksb K.ksb]
      rw [eR, stA_eq] at e
      exact node_ne_field hN (by simp [layout.node.REPROGRAM]) hdT hd' (by simp) e.symm
  -- the fast end: the handler's links cleared, then `switch_to`
  try unfold fastFin at hfin
  rw [obj.Tcb.set_sched_next.ok] at hfin; simp only [bind_ok] at hfin
  rw [obj.Tcb.set_sched_prev.ok] at hfin; simp only [bind_ok] at hfin
  obtain ⟨⟨x1, x2⟩, hsw, hx⟩ := bind_eq_ok hfin
  have hx' := ok_inj_ff hx
  simp only [Prod.mk.injEq, true_and] at hx'
  obtain ⟨rfl, rfl⟩ := hx'
  generalize hY : L.wr (L.wr s15 (nextA .Sched dest) 0#u64) (prevA .Sched dest) 0#u64 = Y at hsw
  have nA : Aligned (nextA .Sched dest) := by unfold nextA nextOff; exact field_aligned hd' (by simp) (by simp)
  have pA : Aligned (prevA .Sched dest) := by unfold prevA prevOff; exact field_aligned hd' (by simp) (by simp)
  have kY : L.ksb Y = L.ksb s := by rw [← hY, L.ksb_wr, L.ksb_wr, K15.ksb]
  have cY : L.cpu Y = L.cpu s := by rw [← hY, LawfulStore.cpu_wr, LawfulStore.cpu_wr, K15.cpu]
  have agY : ∀ b, Aligned b → b ≠ nextA .Sched dest → b ≠ prevA .Sched dest → L.mem Y b = L.mem s15 b := by
    intro b hb h1 h2
    rw [← hY, mem_wr_ne' pA hb (Ne.symm h2), mem_wr_ne' nA hb (Ne.symm h1)]
  have lkΩ : ∀ b ∈ Ω, b ≠ nextA .Sched dest ∧ b ≠ prevA .Sched dest := fun b hb =>
    ⟨fun e => out_ne_field (hΩ b hb) hdT hd' (K := 3480#u64) (by simp) (by rw [e]; rfl),
     fun e => out_ne_field (hΩ b hb) hdT hd' (K := 3488#u64) (by simp) (by rw [e]; rfl)⟩
  have lkT : ∀ K : U64, K.val < 4096 → K.val ≠ 3480 → K.val ≠ 3488 →
      core.num.U64.wrapping_add dest K ≠ nextA .Sched dest ∧ core.num.U64.wrapping_add dest K ≠ prevA .Sched dest :=
    fun K hK h1 h2 => ⟨field_ne hd' hd' hK (K2 := 3480#u64) (by simp) (fun _ => by simpa using h1),
      field_ne hd' hd' hK (K2 := 3488#u64) (by simp) (fun _ => by simpa using h2)⟩
  have agΩ : ∀ b ∈ Ω, L.mem Y b = L.mem s15 b := fun b hb => agY b (hΩ b hb).1 (lkΩ b hb).1 (lkΩ b hb).2
  have agT : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 →
      L.mem Y (core.num.U64.wrapping_add dest K) = L.mem s15 (core.num.U64.wrapping_add dest K) :=
    fun K hK h8 h1 h2 => agY _ (field_aligned hd' hK h8) (lkT K hK h1 h2).1 (lkT K hK h1 h2).2
  -- the placement, the handler's words and the two SCs at `Y`
  have P : TailPld (L := L) T Cs Ω Y dest :=
    (⟨hT, hdT, hN, hcC, hΩ⟩ : TailPld (L := L) T Cs Ω s dest).ksb kY cY
  have escY : L.mem Y (scA dest) = L.mem s (scA dest) := by
    rw [scA_eq, agT _ (by simp) (by simp) (by simp) (by simp)]
    exact K15.tcb dest hdT 3464#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have stY : L.mem Y (stA dest) = sched.TS_RUNNING := by
    rw [stA_eq, agT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact st15
  have eyY : L.mem Y (yieldA dest) = L.mem s (yieldA dest) := by
    rw [show yieldA dest = core.num.U64.wrapping_add dest 3472#u64 from rfl, agT _ (by simp) (by simp) (by simp)
      (by simp)]
    exact K15.tcb dest hdT 3472#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have csA : Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_SC) :=
    nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have ecY : L.cscW Y = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [cY, nodeAt_of_ksb kY]
    rw [agY _ csA (fun e => node_ne_field hN (by simp [layout.node.CUR_SC]) hdT hd' (K := 3480#u64) (by simp) e)
      (fun e => node_ne_field hN (by simp [layout.node.CUR_SC]) hdT hd' (K := 3488#u64) (by simp) e)]
    exact K15.node _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  have hWY : RefillsWF st Y (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    hW15.agree fun b hb hin => agΩ b (scW b hb hin)
  have hcs : L.cscW s ∈ Scs := hX0.cur
  have hcq0 : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := by
    obtain ⟨hP, hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
    exact ⟨(hS.all _ hcs).1, fun b hb hi => hS.sub _ ((hS.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩, by unfold Aligned; rw [hv, hcv]; omega⟩, ⟨a2, a3⟩, a1⟩
  have hcY : SCq st Y Ω (L.cscW Y) (Z (L.cscW Y)) := by
    rw [ecY]
    refine ⟨fun hm => ?_, hcq0.2.1, hcq0.2.2⟩
    by_cases hcd : L.cscW s = L.mem s (scA dest)
    · rw [hcd]; exact hWY
    · have agC : ∀ b, Aligned b → InSC (L.cscW s) (Z (L.cscW s)) b → L.mem Y b = L.mem s b := by
        intro b hb hin
        have hbΩ := hcq0.2.1 b hb hin
        rw [agΩ b hbΩ]
        refine K15.omg b hbΩ (nrt _ hcs b hin) fun hR => ?_
        have := hO.scDisj _ hcs _ hdsc hcd
        unfold InSC at hin; unfold InRing at hR; omega
      have em : L.rmax Y (L.cscW s) = L.rmax s (L.cscW s) := by
        obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
        exact agC _ a1 ⟨a2, a3⟩
      exact (hcq0.1 (em ▸ hm)).agree agC
  have htY : L.mem Y (scA dest) ≠ L.cscW Y → SCin st Y Ω (L.mem Y (scA dest)) (Z (L.mem Y (scA dest))) ∧
      ∀ b, InSC (L.mem Y (scA dest)) (Z (L.mem Y (scA dest))) b → Outside b (L.cscW Y) (Z (L.cscW Y)) := by
    rw [escY, ecY]
    intro hne
    refine ⟨⟨hWY, scW⟩, fun b hin => ?_⟩
    have := hO.scDisj _ hdsc _ hcs hne
    unfold InSC at hin; unfold Outside; omega
  have hyY : L.mem Y (yieldA dest) ≠ 0#u64 → L.mem Y (yieldA dest) ∈ Scs := by
    rw [eyY]; exact hX0.yt.2.1 dest hdT
  have hend := switch_to_nvm hA Y a P (ObjsOK.any hO) hS.sub hcY htY (Or.inl stY) hyY
  rw [hsw, WP.spec_ok] at hend
  obtain ⟨h1, h2⟩ := hend
  rw [h1, h2]
  simp [sched.TS_RUNNING, sched.TS_RUNNING_VM]

/-- **m62's `FaultNvm` from the P1 invariants where `fastpath.fault` is
entered** (module docstring), with the handler's receive state as an
argument (m73: `faultNvm_of` reads it off `EntryHyps0.tmoOK` by
`faultRecv_of`; P3 reads it off the joint relation). -/
theorem faultNvm_ofR {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar)
    {s : S} {a : A} {t : obj.Tcb} {n : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hrecv0 : ∀ {ptr badge dest r : U64}, FaultChecks st s t ptr badge dest r →
      L.mem s (stA dest) = sched.TS_BLOCKED_ON_RECV)
    (hF : FaultEntAt (L := L) T Cs Ω U Sg Rp s t) : FaultNvm (L := L) ar s a t n := by
  intro sF aF h
  obtain ⟨ptr, badge, dest, r, hc, hfast⟩ := fault_acc st ar h
  exact faultNvm_tailG ar hA hI hrecv0 hF (ty := fl4_abi.consts.fault.UnknownSyscall) (w0 := n) (w1 := 0#u64)
    (w2 := 0#u64) (f := error.Fault.UnknownSyscall n) (Or.inl rfl) (set_fault_us (L := L) s t n) hc hfast

/-- **m62's `FaultNvm` from the P1 invariants where `fastpath.fault` is
entered** (module docstring): `faultNvm_ofR` with the handler's receive
state from `EntryHyps0.tmoOK` (`faultRecv_of`). -/
theorem faultNvm_of {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {P3Ok : S → Prop}
    (hA : P0.ArchTotal ar) (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s : S} {a : A} {t : obj.Tcb} {n : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (et : sched.cur_thread st s = ok t)
    (hF : FaultEntAt (L := L) T Cs Ω U Sg Rp s t) : FaultNvm (L := L) ar s a t n :=
  faultNvm_ofR ar hA hI (fun hc => faultRecv_of ar E0 hI hG et hc) hF

/-- **m67's `FaultNvmPre` [J] derived**: at an entry state with `EntryInv`
(a `P3Ok` state, the `Hyps4` fields `EntryHyps0` / `XferHyps`) and
`AsidOff`, on both routes into `fastpath.fault` (as `FastFaultPre.of_asid`). -/
theorem FaultNvmPre.of_asid {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {P3Ok : S → Prop} (hA : P0.ArchTotal ar) (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (XH : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s : S} {a : A} {n : I64} (hP : P3Ok s) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hAs : AsidOff (L := L) Ω Sg s) :
    FaultNvmPre (L := L) ar s a n := by
  intro t nx s1 et enx es1
  have h0 := h.1.choose_spec.choose_spec
  have et' : t = L.curW s := by
    rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)] at et; exact (ok_inj_ff et).symm
  have htT : t ∈ T := by rw [et']; exact h0.curT
  have h1 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := by
    have := reg_entry (r := layout.reg.FAULT_IP) (v := core.num.U64.wrapping_sub nx 2#u64) h htT
      (by simp [layout.reg.FAULT_IP])
    rw [es1, WP.spec_ok] at this; exact this
  have hW := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
    (h0.tcbs t htT) (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW
  obtain ⟨K, hK, e1⟩ := hW
  have hal : Aligned (core.num.U64.wrapping_add (L.curW s) K) := by
    rw [← et']; exact field_aligned (h0.tcbs t htT)
      (by rw [hK]; simp [layout.reg.FAULT_IP]) (by rw [hK]; simp [layout.reg.FAULT_IP])
  have e1' : s1 = L.wr s (core.num.U64.wrapping_add (L.curW s) K) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [e1, et']
  have he1 : EntAt st P3Ok s1 := ⟨s, hP, Ent.prefix hK hal e1' (WritesIn.refl _ _)⟩
  have hN1 : NodePlaced st T s1 (L.cpu s1) := (h1.1.choose_spec.choose_spec).nodes _ h1.1.choose_spec.choose_spec.cur
  have hcur0 : L.curW s ∈ T := h0.curT
  have hAs2 : ∀ s2, WritesIn st s1 s2 (L.NodeOf s1 (L.cpu s1) fun _ => True) → AsidOff (L := L) Ω Sg s2 :=
    fun s2 w2 => AsidOff.ent h0.tcbs hcur0 h0.cur (h0.nodes _ h0.cur) h0.omega (Ent.prefix hK hal e1' w2) hAs
  refine ⟨fun s2 a2 t2 hb et2 => ?_, fun t1 s3 a3 et1 hd => ?_⟩
  · have hx := syscall.budget_ok.bxc hA E0 s1 a h1 he1.xg
    rw [hb, WP.spec_ok] at hx
    have hf := syscall.budget_ok.fr hA s1 a hN1
    rw [hb, WP.spec_ok] at hf
    exact faultNvm_of ar hA E0 hx.1 (hx.2.2 rfl) et2 (faultEntAt_of ar E0 XH hx.1 (hx.2.2 rfl) et2 (hAs2 s2 (hf rfl)))
  · intro s2 a2 t2 hb et2
    have et1' : t1 = L.curW s1 := by
      rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s1)] at et1; exact (ok_inj_ff et1).symm
    have hd' := hd
    rw [et1'] at hd'
    have hdi := E0.debug Ac s1 a n he1 h1
    rw [hd', WP.spec_ok] at hdi
    obtain ⟨Ac3, h3⟩ := hdi
    have hsame := syscall.debug_syscall.same (L := L) hA s1 a (L.curW s1) n
    rw [hd', WP.spec_ok] at hsame
    have e3 : s3 = s1 := hsame rfl
    subst e3
    have hx := syscall.budget_ok.bxc hA E0 s3 a3 h3 he1.xg
    rw [hb, WP.spec_ok] at hx
    have hf := syscall.budget_ok.fr hA s3 a3 hN1
    rw [hb, WP.spec_ok] at hf
    exact faultNvm_of ar hA E0 hx.1 (hx.2.2 rfl) et2 (faultEntAt_of ar E0 XH hx.1 (hx.2.2 rfl) et2 (hAs2 s2 (hf rfl)))

end

end Fl4Proofs.P1
