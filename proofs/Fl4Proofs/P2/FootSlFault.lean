/-
# P2 (line p2sl): the accepted fault fast path writes only its footprint

`sl_fault_foot`: an accepted `fastpath.fault s a t n` (the trap arm of
`handle_syscall_local`, entered after the prefix) writes only `FootSl` words
of the state `s` where it is entered, with the endpoint `ptr` of the fault
handler cap and the reply object `r` of the endpoint's head locked. The run,
as P1 reads it (`fault_acc`, `faultTailG_eq`, `faultTail2G_eq`,
`faultTail3_eq`; the reads from `faultReads_ofG`, the tail's SC facts as in
P1's `faultNvm_tailG`):

* `set_fault`: four fault words of the current thread `t`;
* the dequeue (`epFast`): the endpoint's two words (locked), the handler
  `dest`'s queue links and, when `dest` is not the tail, the next queued
  thread's `EP_PREV` (queue links of the locked endpoint's queue);
* the fault message (`xfer_foot_S8` over `{dest}` and `dest`'s buffer): the
  handler's registers and IPC-buffer words (`dest` is on this core:
  `schedulable_here` checked its affinity);
* the reply's `TCB` word (locked), the two threads' state words, `t`'s reply
  word, the handler's SC ring and the node's `REPROGRAM` (`unblock_sporadic`),
  the handler's scheduler links, and the tail `switch_to` (`sl_switch_to_foot`).

Hypotheses at `s`: P1's invariants `BXI`, the handler blocked on receive and
`FaultEntAt` (as P1's `faultNvm_tailG` takes them), and

* `hy0` [J]: the handler yields to no SC (`YIELD_TO = 0`). A thread blocked
  on an endpoint has none in every reachable state (`yield_switches` sets it
  only on the running caller, which stays runnable until `activate_thread`
  completes the yield; `suspend` cancels it), but P1's invariants do not
  state it (P1 `YT` only types it). Without it `switch_to`'s
  `complete_yield_to` would write the `CONSUMED` and `YIELD_FROM` words of
  the SC yielded to, which `FootSl` does not hold.
-/
import Fl4Proofs.P2.FootSlDefs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {A : Type _} {st : machine.Store S} [L : LawfulStore st] (ar : machine.Arch A)

theorem sl_wt {T : Set U64} {Z : U64 → Nat} {s X Y : S} {ep r : U64} (h1 : WritesIn st s X (FootSl st T Z s ep r))
    (h2 : WritesIn st X Y (FootSl st T Z s ep r)) : WritesIn st s Y (FootSl st T Z s ep r) := h1.trans1 h2

set_option maxHeartbeats 8000000 in
/-- **An accepted fault fast path writes only `FootSl`** (module docstring). -/
theorem sl_fault_foot {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar) {s : S} {a : A} {t : obj.Tcb} {n : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hrecv0 : ∀ {ptr badge dest r : U64}, FaultChecks st s t ptr badge dest r →
      L.mem s (stA dest) = sched.TS_BLOCKED_ON_RECV)
    (hF : FaultEntAt (L := L) T Cs Ω U Sg Rp s t)
    (hy0 : ∀ {ptr badge dest r : U64}, FaultChecks st s t ptr badge dest r → L.mem s (yieldA dest) = 0#u64)
    {sF : S} {aF : A} (h : fastpath.fault st ar s a t n = ok (true, sF, aF)) :
    ∃ ptr badge dest r, FaultChecks st s t ptr badge dest r ∧ WritesIn st s sF (FootSl st T Z s ptr r) := by
  obtain ⟨ptr, badge, dest, r, hc, hfast⟩ := fault_acc st ar h
  refine ⟨ptr, badge, dest, r, hc, ?_⟩
  have hrecv := hrecv0 hc
  obtain ⟨⟨Q, R, hSQ⟩, hB, hX, hSg, hS⟩ := hI
  have hX0 : ScExtra0 st T Cs Scs Nt s := hX.2.2.toScExtra0
  have hO := hX.1
  unfold faultTail at hfast
  rw [faultTailG_eq st ar a t _ _ ptr badge dest r (set_fault_us (L := L) s t n)] at hfast
  have hf0 := hfast
  unfold faultTail2G at hfast
  obtain ⟨rb, hbuf, h1⟩ := bind_eq_ok hfast
  obtain ⟨⟨sent, S6⟩, hmrs, h2⟩ := bind_eq_ok h1
  try simp only [uncurry_apply_pair] at h2
  obtain ⟨mi, hmi, h3⟩ := bind_eq_ok h2
  obtain ⟨S7, hS7, h4⟩ := bind_eq_ok h3
  obtain ⟨S8, hS8, -⟩ := bind_eq_ok h4
  rw [faultTail2G_eq ar _ a t _ dest r badge hbuf hmrs hmi hS7 hS8, faultTail3_eq] at hf0
  obtain ⟨s15, h15, hfin⟩ := bind_eq_ok hf0
  obtain ⟨hr, rest, E⟩ := hF.2 ptr badge dest r hc
  obtain ⟨RR, -, KF⟩ := faultReads_ofG ar (ty := fl4_abi.consts.fault.UnknownSyscall) (fw0 := n) (fw1 := 0#u64)
    (fw2 := 0#u64) (Or.inl rfl) E hbuf hmrs hS7 hS8
  have HF := here_facts (L := L) hc.here
  have hT := E.hT
  have hdT : dest ∈ T := E.hq.mem dest (by simp)
  have hd' := hT dest hdT
  have ht' := hT t E.ht
  have hN := E.hN
  have hcC := E.hcC
  have hΩ := E.hΩ
  -- the handler's SC (as P1's `faultNvm_tailG`)
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
  have hUo := usOff_of E KF scW (hS.sub _ (hS.spSg _ hdsc)) spWF (hO.rpSc r hr _ hdsc) hZ7 hPl.fits
  have w15 := unblock_sporadic_fr hUo h15
  have esc14 : L.mem (fS14 (L := L) S8 t dest r) (scA dest) = L.mem s (scA dest) :=
    KF.tcb dest hdT 3464#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hW14 : RefillsWF st (fS14 (L := L) S8 t dest r) (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    hWs.agree fun b hb hin => KF.omg b (scW b hb hin) (nrt _ hdsc b hin)
  have hW15 : RefillsWF st s15 (L.mem s (scA dest)) (Z (L.mem s (scA dest))) := by
    have := unblock_sporadic_wf hUo (by rw [esc14]; exact hW14) h15
    rw [esc14] at this; exact this
  rw [esc14] at w15
  have K15 := finKeep15 hT hN hcC hΩ KF scW w15
  -- the end: the handler's links cleared, then `switch_to`
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
  have P : TailPld (L := L) T Cs Ω Y dest :=
    (⟨hT, hdT, hN, hcC, hΩ⟩ : TailPld (L := L) T Cs Ω s dest).ksb kY cY
  have escY : L.mem Y (scA dest) = L.mem s (scA dest) := by
    rw [scA_eq, agT _ (by simp) (by simp) (by simp) (by simp)]
    exact K15.tcb dest hdT 3464#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
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
  /- The footprint: the threads `t` (current) and `dest` (affinity this core). -/
  have hcurW : L.curW s = t := E.hcur
  have tOn : SlOn st T s t := ⟨E.ht, Or.inr hcurW.symm⟩
  have dOn : SlOn st T s dest := slOn_aff hdT HF.aff
  have hhd : L.mem s (epHeadA ptr) = dest := by
    have h1 := hc.head
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) s ptr)] at h1; exact ok_inj_ff h1
  have hdR : SlReach (L.mem s) T ptr dest := by
    have := SlReach.head (m := L.mem s) (T := T) (ep := ptr) (by rw [hhd]; exact hdT)
    rw [hhd] at this; exact this
  have fT : ∀ K : U64, K.val < 4096 → ¬ (3528 ≤ K.val ∧ K.val < 3576) → K.val ≠ 3496 ∧ K.val ≠ 3504 →
      FootSl st T Z s ptr r (core.num.U64.wrapping_add t K) := fun K h1 h2 h3 =>
    FootSl.tcb (slTcb_at tOn h1 h2 h3)
  have fD : ∀ K : U64, K.val < 4096 → ¬ (3528 ≤ K.val ∧ K.val < 3576) → K.val ≠ 3496 ∧ K.val ≠ 3504 →
      FootSl st T Z s ptr r (core.num.U64.wrapping_add dest K) := fun K h1 h2 h3 =>
    FootSl.tcb (slTcb_at dOn h1 h2 h3)
  have fN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → FootSl st T Z s ptr r (L.nodeAt s (L.cpu s) o) :=
    fun o h1 h2 => FootSl.node (slNode_at h1 h2)
  have fQd : FootSl st T Z s ptr r (nextA .Ep dest) ∧ FootSl st T Z s ptr r (prevA .Ep dest) :=
    ⟨FootSl.q ⟨dest, hdR, Or.inl rfl⟩, FootSl.q ⟨dest, hdR, Or.inr rfl⟩⟩
  -- the next queued thread, when `dest` is not the tail
  have hafT : (L.epQ s ptr).end ≠ dest → L.mem s (nextA .Ep dest) ∈ T := by
    intro hl
    cases rest with
    | nil => exact absurd (E.hq.last.trans rfl) hl
    | cons y ys =>
      rw [E.hq.head_next]
      exact E.hq.mem y (by simp)
  /- `s → S5`: `set_fault`, then the dequeue. -/
  have a0 : Aligned (faultA t) := field_aligned (K := 3376#u64) ht' (by simp) (by simp)
  have a1' : Aligned (core.num.U64.wrapping_add t 3384#u64) := field_aligned ht' (by simp) (by simp)
  have a2' : Aligned (core.num.U64.wrapping_add t 3392#u64) := field_aligned ht' (by simp) (by simp)
  have a3' : Aligned (core.num.U64.wrapping_add t 3400#u64) := field_aligned ht' (by simp) (by simp)
  have w2 : WritesIn st s (sfW (L := L) s t n) (FootSl st T Z s ptr r) := by
    unfold sfW
    refine ((((writesIn_wr a0).trans (writesIn_wr a1')).trans (writesIn_wr a2')).trans (writesIn_wr a3')).mono ?_
    rintro b (((rfl | rfl) | rfl) | rfl)
    · exact fT 3376#u64 (by simp) (by simp) (by simp)
    · exact fT 3384#u64 (by simp) (by simp) (by simp)
    · exact fT 3392#u64 (by simp) (by simp) (by simp)
    · exact fT 3400#u64 (by simp) (by simp) (by simp)
  have aH := (ep_aligned E.hE).1
  have aTS := (ep_aligned E.hE).2
  have aNd : Aligned (nextA .Ep dest) := nextA_aligned hd' .Ep
  have aPd : Aligned (prevA .Ep dest) := prevA_aligned hd' .Ep
  -- a TCB word `y + K` against `set_fault`'s words
  have nTt : ∀ (y K : U64), TcbAddr y → K.val < 4096 →
      (y = t → K.val ≠ 3376 ∧ K.val ≠ 3384 ∧ K.val ≠ 3392 ∧ K.val ≠ 3400) →
      core.num.U64.wrapping_add y K ≠ faultA t ∧
      core.num.U64.wrapping_add y K ≠ core.num.U64.wrapping_add t 3384#u64 ∧
      core.num.U64.wrapping_add y K ≠ core.num.U64.wrapping_add t 3392#u64 ∧
      core.num.U64.wrapping_add y K ≠ core.num.U64.wrapping_add t 3400#u64 := by
    intro y K hy hK hne
    exact ⟨field_ne hy ht' hK (K2 := 3376#u64) (by simp) (fun e => by simpa using (hne e).1),
      field_ne hy ht' hK (K2 := 3384#u64) (by simp) (fun e => by simpa using (hne e).2.1),
      field_ne hy ht' hK (K2 := 3392#u64) (by simp) (fun e => by simpa using (hne e).2.2.1),
      field_ne hy ht' hK (K2 := 3400#u64) (by simp) (fun e => by simpa using (hne e).2.2.2)⟩
  have eaf : L.mem (sfW (L := L) s t n) (nextA .Ep dest) = L.mem s (nextA .Ep dest) := by
    obtain ⟨n1, n2, n3, n4⟩ := nTt dest 3496#u64 hd' (by simp) (fun e => absurd e E.hdt)
    exact sfW_mem aNd ⟨a0, Ne.symm n1⟩ ⟨a1', Ne.symm n2⟩ ⟨a2', Ne.symm n3⟩ ⟨a3', Ne.symm n4⟩
  have eend : (L.epQ (sfW (L := L) s t n) ptr).end = (L.epQ s ptr).end := by
    have m1 := (sl_ep_ne_field E.hE E.ht ht' (K := 3376#u64) (by simp)).2
    have m2 := (sl_ep_ne_field E.hE E.ht ht' (K := 3384#u64) (by simp)).2
    have m3 := (sl_ep_ne_field E.hE E.ht ht' (K := 3392#u64) (by simp)).2
    have m4 := (sl_ep_ne_field E.hE E.ht ht' (K := 3400#u64) (by simp)).2
    show L.mem (sfW (L := L) s t n) (epTSA ptr) &&& ~~~3#u64 = L.mem s (epTSA ptr) &&& ~~~3#u64
    rw [sfW_mem aTS ⟨a0, Ne.symm m1⟩ ⟨a1', Ne.symm m2⟩ ⟨a2', Ne.symm m3⟩ ⟨a3', Ne.symm m4⟩]
  have w25 : WritesIn st (sfW (L := L) s t n) (epFast (L := L) (sfW (L := L) s t n) ptr dest)
      (FootSl st T Z s ptr r) := by
    have lkE := slLk_ep (r := r) E.hE
    unfold epFast epW
    dsimp only
    rw [eend, eaf]
    by_cases hl : (L.epQ s ptr).end = dest
    · rw [if_pos hl]
      refine ((((writesIn_wr aH).trans (writesIn_wr aTS)).trans (writesIn_wr aNd)).trans (writesIn_wr aPd)).mono ?_
      rintro b (((rfl | rfl) | rfl) | rfl)
      · exact FootSl.lk lkE.1
      · exact FootSl.lk lkE.2
      · exact fQd.1
      · exact fQd.2
    · rw [if_neg hl]
      have haf := hT _ (hafT hl)
      have fQa : FootSl st T Z s ptr r (prevA .Ep (L.mem s (nextA .Ep dest))) :=
        FootSl.q ⟨_, SlReach.next hdR (hafT hl), Or.inr rfl⟩
      refine (((((writesIn_wr (prevA_aligned haf .Ep)).trans (writesIn_wr aH)).trans (writesIn_wr aTS)).trans
        (writesIn_wr aNd)).trans (writesIn_wr aPd)).mono ?_
      rintro b ((((rfl | rfl) | rfl) | rfl) | rfl)
      · exact fQa
      · exact FootSl.lk lkE.1
      · exact FootSl.lk lkE.2
      · exact fQd.1
      · exact fQd.2
  have w5 := sl_wt w2 w25
  /- `S5 → S8`: the fault message, over `{dest}` and `dest`'s buffer. -/
  have kD : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem (epFast (L := L) (sfW (L := L) s t n) ptr dest) (core.num.U64.wrapping_add dest K) =
        L.mem s (core.num.U64.wrapping_add dest K) := by
    intro K hK h8 h1 h2
    have aK := field_aligned hd' hK h8
    obtain ⟨n1, n2, n3, n4⟩ := nTt dest K hd' hK (fun e => absurd e E.hdt)
    obtain ⟨e1, e2⟩ := sl_ep_ne_field E.hE hdT hd' hK
    rw [epFast_mem aK ⟨aH, e1⟩ ⟨aTS, e2⟩ ⟨aNd, ?_⟩ ⟨aPd, ?_⟩ ?_]
    · exact sfW_mem aK ⟨a0, Ne.symm n1⟩ ⟨a1', Ne.symm n2⟩ ⟨a2', Ne.symm n3⟩ ⟨a3', Ne.symm n4⟩
    · exact field_ne hd' hd' (K1 := 3496#u64) (by simp) hK (fun _ => by simpa using Ne.symm h1)
    · exact field_ne hd' hd' (K1 := 3504#u64) (by simp) hK (fun _ => by simpa using Ne.symm h2)
    · intro hl
      rw [eend] at hl
      rw [eaf]
      have haf := hT _ (hafT hl)
      exact ⟨prevA_aligned haf .Ep,
        field_ne haf hd' (K1 := 3504#u64) (by simp) hK (fun _ => by simpa using Ne.symm h2)⟩
  have ebuf : msg.lookup_ipc_buffer st (epFast (L := L) (sfW (L := L) s t n) ptr dest) true dest =
      msg.lookup_ipc_buffer st s true dest := by
    have e72 : core.num.U64.wrapping_add (sbA dest) 8#u64 = core.num.U64.wrapping_add dest 72#u64 := by
      apply UScalar.eq_of_val_eq
      rw [field_val hd' (by simp), core.num.U64.wrapping_add_val_eq, sbA_val hd']
      have := hd'.fits
      simp [U64.size_def, U64.numBits]
      omega
    refine lookup_buf_agree (kD 3512#u64 (by simp) (by simp) (by simp) (by simp)) ?_ ?_
    · rw [sbA_field hd']; exact kD 64#u64 (by simp) (by simp) (by simp) (by simp)
    · rw [e72]; exact kD 72#u64 (by simp) (by simp) (by simp) (by simp)
  have hbs : msg.lookup_ipc_buffer st s true dest = ok rb := ebuf ▸ hbuf
  have hBU : BufOK U rb := by have := E.hbuf; rw [hbs, WP.spec_ok] at this; exact this
  let Ud : Set U64 := {b | rb ≠ 0#u64 ∧ b ∈ U ∧ ∃ i : U64, i.val < 128 ∧
      b = core.num.U64.wrapping_add rb (core.num.U64.wrapping_mul i 8#u64)}
  have hUa : ∀ b ∈ Ud, Aligned b := fun b hb => (E.hU b hb.2.1).1.1
  have hbU : BufOK Ud rb := fun h0 i hi => ⟨h0, hBU h0 i hi, i, hi, rfl⟩
  have hTd : TcbPlaced ({dest} : Set U64) := fun y hy => by
    rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hd'
  obtain ⟨-, w58⟩ := xfer_foot_S8 ar hTd (Set.mem_singleton dest) hUa hbU RR.hR5 hmrs hS7 hS8
  have fX : ∀ b, XferRegW ({dest} : Set U64) Ud b → FootSl st T Z s ptr r b := by
    rintro b (⟨y, hy, K, h1, h2, h3, rfl⟩ | ⟨h0, -, i, hi, rfl⟩)
    · rw [Set.mem_singleton_iff] at hy; rw [hy]
      exact fD K (by omega) (by omega) (by omega)
    · exact FootSl.buf ⟨dest, dOn, true, rb, hbs, h0, i, hi, rfl⟩
  have w8 := sl_wt w5 (w58.mono fX)
  /- `S8 → S14`: the reply's `TCB` word, the states, `t`'s reply word. -/
  have aR : Aligned (rTcbA r) := (hΩ _ E.hrΩ).1
  have aSd : Aligned (stA dest) := by rw [stA_eq]; exact field_aligned hd' (by simp) (by simp)
  have aSt : Aligned (stA t) := by rw [stA_eq]; exact field_aligned ht' (by simp) (by simp)
  have aRt : Aligned (replyA t) := field_aligned (K := 3360#u64) ht' (by simp) (by simp)
  have fR : FootSl st T Z s ptr r (rTcbA r) := FootSl.lk slLk_rtcb
  have fSd : FootSl st T Z s ptr r (stA dest) := by rw [stA_eq]; exact fD _ (by simp) (by simp) (by simp)
  have fSt : FootSl st T Z s ptr r (stA t) := by rw [stA_eq]; exact fT _ (by simp) (by simp) (by simp)
  have fRt : FootSl st T Z s ptr r (replyA t) := fT 3360#u64 (by simp) (by simp) (by simp)
  have w14 : WritesIn st S8 (fS14 (L := L) S8 t dest r) (FootSl st T Z s ptr r) := by
    unfold fS14 fS13 fS10
    refine ((((((writesIn_wr aR).trans (writesIn_wr aSd)).trans (writesIn_wr aR)).trans (writesIn_wr aSt)).trans
      (writesIn_wr aRt)).trans (writesIn_wr aSd)).mono ?_
    intro b hb
    rcases hb with (((((h | h) | h) | h) | h) | h)
    · rw [h]; exact fR
    · rw [h]; exact fSd
    · rw [h]; exact fR
    · rw [h]; exact fSt
    · rw [h]; exact fRt
    · rw [h]; exact fSd
  /- `S14 → s15`: `unblock_sporadic`. -/
  have w15' : WritesIn st (fS14 (L := L) S8 t dest r) s15 (FootSl st T Z s ptr r) := w15.mono fun b hb => by
    rcases hb with hb | rfl
    · exact FootSl.sc (slSc_ring (Or.inr ⟨dest, dOn, rfl, HF.sc⟩) hb)
    · have eR : L.nodeA (fS14 (L := L) S8 t dest r) layout.node.REPROGRAM =
          L.nodeAt s (L.cpu s) layout.node.REPROGRAM := by
        unfold LawfulStore.nodeA; rw [KF.cpu, nodeAt_of_ksb KF.ksb]
      rw [eR]; exact fN _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
  /- `s15 → Y`: the handler's scheduler links. -/
  have wY : WritesIn st s15 Y (FootSl st T Z s ptr r) := by
    rw [← hY]
    exact ((writesIn_wr nA).trans (writesIn_wr pA)).mono fun b hb => by
      rcases hb with rfl | rfl
      · exact fD 3480#u64 (by simp) (by simp) (by simp)
      · exact fD 3488#u64 (by simp) (by simp) (by simp)
  /- `Y → sF`: the switch to the handler. -/
  have wsw := sl_switch_to_foot (ar := ar) hA Y a P hcY htY (by rw [eyY]; exact hy0 hc)
    (B := FootSl st T Z s ptr r)
    (fun o h1 h2 => by rw [cY, nodeAt_of_ksb kY]; exact fN o h1 h2)
    (fun b hb h => by
      rw [ecY] at h
      rcases h with h | rfl
      · exact FootSl.sc (slSc_ring (Or.inl rfl) h)
      · exact FootSl.sc ⟨_, Or.inl rfl, hcq0.2.2.1.1⟩)
    (fun _ b hb h => by
      rw [escY] at h
      exact FootSl.sc (slSc_ring (Or.inr ⟨dest, dOn, rfl, HF.sc⟩) h))
    (fun K h1 h2 => fD K (by omega) (by omega) (by omega))
  rw [hsw, WP.spec_ok] at wsw
  exact sl_wt (sl_wt (sl_wt (sl_wt w8 w14) w15') wY) wsw

end

end Fl4Proofs.P2
