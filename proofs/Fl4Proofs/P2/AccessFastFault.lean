/-
# P2: the guarded-store lemmas for the fault fast path's write part

The pieces of `fastpath.fault` after its checks, on `guard st R W`, as P1
splits the run (`P1/FastFault.lean`): `faultTailG` to the end of the dequeue
(`faultTailG.guard_eq`, the counterpart of P1's `faultTailG_eq`), then
`faultTail2G` to the handler made `Running` (`faultTail2G.guard_eq`, of
`faultTail2G_eq`). P1's equalities need `LawfulStore` of the store they run
on, which `guard st R W` lacks: here every guarded leaf is first rewritten to
the real one (`<f>.guard`), then P1's `.ok` / `.spec` values apply.

Small guards: `obj.Ep.state`, `obj.Ep.tail`, `obj.Ep.set_queue`,
`sporadic.sc_sporadic`, `endpoint.unblock_sporadic`.

**`fastpath.fault.guard`**: an accepted `fastpath.fault s a t n` runs on
`guard st R W` as on `st` when `R` / `W` hold `FltAcc` (the words the run
reads and writes, as functions of the entry state `s` and the checks'
endpoint, handler and reply object). The checks are rewritten leaf by leaf
(both the `grant` and the `grant_reply` arm), the write part through the two
equalities above, `unblock_sporadic`, the handler's scheduler links, and the
tail `fastpath.switch_to.guard` at the pre-switch state `Y`, whose hypotheses
come from `sl_fault_foot`'s facts at `Y` (`hcY`, `htY`, `TailPld`, the
handler's ring `hWY`) and, for the release head and the timer-min thread, from
P1's `SchedQueuesInv` / `BoundInv` / `SCsOK` and `TimerOK` at `s`.

Premises of `fastpath.fault.guard`: `sl_fault_foot`'s `hy0` [J] (the handler
yields to no SC) and P1's `AsidOff` [J] (`P1/FastFinInv.lean`: the ASID table
and pools are `Ω` words outside `Sg`, so the run up to `switch_to` keeps
them).
-/
import Fl4Proofs.P2.AccessSwitchTo
import Fl4Proofs.P2.FootSlFault
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]

theorem obj.Ep.state.guard (ep : obj.Ep) (s : S) (h : R (core.num.U64.wrapping_add ep layout.ep.TAIL_STATE)) :
    obj.Ep.state (guard st R W) ep s = obj.Ep.state st ep s := by
  unfold obj.Ep.state; rw [obj.Ep.tail_state.guard ep s h]

theorem obj.Ep.tail.guard (ep : obj.Ep) (s : S) (h : R (core.num.U64.wrapping_add ep layout.ep.TAIL_STATE)) :
    obj.Ep.tail (guard st R W) ep s = obj.Ep.tail st ep s := by
  unfold obj.Ep.tail; rw [obj.Ep.tail_state.guard ep s h]

theorem obj.Ep.set_queue.guard (ep : obj.Ep) (s : S) (hd tl stt : U64)
    (hH : W (core.num.U64.wrapping_add ep layout.ep.HEAD))
    (hT : W (core.num.U64.wrapping_add ep layout.ep.TAIL_STATE)) :
    obj.Ep.set_queue (guard st R W) ep s hd tl stt = obj.Ep.set_queue st ep s hd tl stt := by
  unfold obj.Ep.set_queue
  rw [obj.Ep.set_head.guard ep s hd hH]
  refine bind_guard_congr rfl fun s1 _ => ?_
  simp only [lift, bind_ok]
  rw [obj.Ep.set_tail_state.guard ep s1 _ hT]

theorem sporadic.sc_sporadic.guard (s : S) (sc : obj.Sc) (h : sc ≠ 0#u64 → R (sporA sc)) :
    sporadic.sc_sporadic (guard st R W) s sc = sporadic.sc_sporadic st s sc := by
  unfold sporadic.sc_sporadic
  rw [eq_of_spec_fd (obj.Sc.is_null.spec sc)]; simp only [bind_ok]
  by_cases h0 : sc = 0#u64
  · simp only [h0, decide_true, ↓reduceIte]
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [obj.Sc.sporadic.guard sc s (h h0)]

variable {A : Type} (ar : machine.Arch A)

/-- **`faultTailG` on the guarded store, to the end of the dequeue** (P1's
`faultTailG_eq` for the UnknownSyscall fault): `set_fault`'s four words of
`t`, the endpoint's words, the handler's queue links and, when it is not the
tail, its successor's `EP_PREV`. -/
theorem faultTailG.guard_eq (s : S) (a : A) (t : obj.Tcb) (n ty ptr badge dest r : U64)
    (h0 : W (core.num.U64.wrapping_add t 3376#u64)) (h1 : W (core.num.U64.wrapping_add t 3384#u64))
    (h2 : W (core.num.U64.wrapping_add t 3392#u64)) (h3 : W (core.num.U64.wrapping_add t 3400#u64))
    (hts : R (core.num.U64.wrapping_add ptr layout.ep.TAIL_STATE))
    (hwh : W (core.num.U64.wrapping_add ptr layout.ep.HEAD))
    (hwt : W (core.num.U64.wrapping_add ptr layout.ep.TAIL_STATE))
    (hen : (L.epQ (sfW (L := L) s t n) ptr).end ≠ dest → R (core.num.U64.wrapping_add dest 3496#u64) ∧
      W (core.num.U64.wrapping_add (L.mem (sfW (L := L) s t n) (nextA .Ep dest)) 3504#u64))
    (hdn : W (core.num.U64.wrapping_add dest 3496#u64)) (hdp : W (core.num.U64.wrapping_add dest 3504#u64)) :
    faultTailG (guard st R W) ar s a t (error.Fault.UnknownSyscall n) ty ptr badge dest r =
      faultTail2G (guard st R W) ar (epFast (L := L) (sfW (L := L) s t n) ptr dest) a t ty dest r badge := by
  unfold faultTailG
  rw [faults.set_fault.guardU s t n h0 h1 h2 h3, set_fault_us]; simp only [bind_ok]
  rw [obj.Ep.tail.guard ptr _ hts, obj.Ep.tail.ok]; simp only [bind_ok]
  by_cases htl : (L.epQ (sfW (L := L) s t n) ptr).end = dest
  · rw [if_pos htl, obj.Ep.set_queue.guard ptr _ _ _ _ hwh hwt, obj.Ep.set_queue.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_next.guard dest _ _ hdn, obj.Tcb.set_ep_next.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_prev.guard dest _ _ hdp, obj.Tcb.set_ep_prev.ok]; simp only [bind_ok]
    unfold epFast; simp only [htl, ↓reduceIte]; rfl
  · obtain ⟨hrn, hwp⟩ := hen htl
    rw [if_neg htl]
    rw [obj.Tcb.ep_next.guard dest _ hrn, obj.Tcb.ep_next.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_prev.guard _ _ _ hwp, obj.Tcb.set_ep_prev.ok]; simp only [bind_ok]
    rw [obj.Ep.set_queue.guard ptr _ _ _ _ hwh hwt, obj.Ep.set_queue.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_next.guard dest _ _ hdn, obj.Tcb.set_ep_next.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_prev.guard dest _ _ hdp, obj.Tcb.set_ep_prev.ok]; simp only [bind_ok]
    unfold epFast; simp only [htl, ↓reduceIte]; rfl

/-- **`faultTail2G` on the guarded store, to the handler made `Running`** (P1's
`faultTail2G_eq`): the buffer lookup, the fault message (`t`'s fault and
registers read, `dest`'s registers and buffer written), the badge, the
reply's `TCB` word, both threads' states and `t`'s reply word. -/
theorem faultTail2G.guard_eq (X : S) (a : A) (t : obj.Tcb) (dest r badge : U64)
    {rb sent : U64} {S6 S7 S8 : S} {mi : msginfo.MessageInfo} {sl : U64}
    (hbuf : msg.lookup_ipc_buffer st X true dest = ok rb)
    (hmrs : faults.set_mrs_fault st ar X a t dest rb = ok (sent, S6))
    (hmi : msginfo.MessageInfo.new fl4_abi.consts.fault.UnknownSyscall 0#u64 0#u64 sent = ok mi)
    (hS7 : msg.set_msg_info st S6 dest mi = ok S7)
    (hS8 : obj.Tcb.set_reg st dest S7 layout.reg.BADGE badge = ok S8)
    (hsl : obj.Tcb.slot dest layout.tcb.SLOT_BUFFER = ok sl)
    (hI : R (core.num.U64.wrapping_add dest 3512#u64)) (hR0 : R sl) (hR8 : R (core.num.U64.wrapping_add sl 8#u64))
    (hty : L.mem X (faultA t) = fl4_abi.consts.fault.UnknownSyscall)
    (hf0 : R (core.num.U64.wrapping_add t 3376#u64)) (hf1 : R (core.num.U64.wrapping_add t 3384#u64))
    (hf2 : R (core.num.U64.wrapping_add t 3392#u64)) (hf3 : R (core.num.U64.wrapping_add t 3400#u64))
    (hsr : Regs R t) (hrw : Regs W dest) (hbw : BufW W rb)
    (hmw : W (regA dest layout.reg.MSG_INFO)) (hbd : W (regA dest layout.reg.BADGE))
    (hrt : W (core.num.U64.wrapping_add r layout.reply.TCB))
    (hsd : W (core.num.U64.wrapping_add dest layout.tcb.STATE))
    (hst : W (core.num.U64.wrapping_add t layout.tcb.STATE))
    (hrp : W (core.num.U64.wrapping_add t 3360#u64)) :
    faultTail2G (guard st R W) ar X a t fl4_abi.consts.fault.UnknownSyscall dest r badge =
      faultTail3 (guard st R W) ar (fS14 (L := L) S8 t dest r) a dest := by
  unfold faultTail2G
  rw [msg.lookup_ipc_buffer.guard X true dest hsl hI hR0 hR8, hbuf]; simp only [bind_ok]
  rw [faults.set_mrs_fault.guardU ar X a t dest rb hty hf0 hf1 hf2 hf3 hsr hrw hbw, hmrs]
  simp only [bind_ok, uncurry_apply_pair]
  rw [hmi]; simp only [bind_ok]
  rw [msg.set_msg_info.guard S6 dest mi hmw, hS7]; simp only [bind_ok]
  rw [obj.Tcb.set_reg.guard dest S7 _ _ hbd, hS8]; simp only [bind_ok]
  rw [obj.Reply.set_tcb.guard r _ _ hrt, eq_of_spec_fd (obj.Reply.set_tcb.spec (L := L) _ r _)]
  simp only [bind_ok]
  rw [obj.Tcb.set_state.guard dest _ _ hsd, eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ dest _)]
  simp only [bind_ok]
  rw [obj.Reply.set_tcb.guard r _ _ hrt, eq_of_spec_fd (obj.Reply.set_tcb.spec (L := L) _ r _)]
  simp only [bind_ok]
  rw [obj.Tcb.set_state.guard t _ _ hst, eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ t _)]
  simp only [bind_ok]
  rw [obj.Tcb.set_reply_obj.guard t _ _ hrp, eq_of_spec_fd (obj.Tcb.set_reply_obj.wr (L := L) _ t _)]
  simp only [bind_ok]
  rw [obj.Tcb.set_state.guard dest _ _ hsd, eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ dest _)]
  simp only [bind_ok]
  unfold faultTail3 fS14 fS13 fS10; rfl

/-- `faultTail3` as `unblock_sporadic` then the end (P1's `faultTail3_eq`,
on any store). -/
theorem faultTail3_split {S' : Type} (st' : machine.Store S') (S14 : S') (a : A) (dest : U64) :
    faultTail3 st' ar S14 a dest =
      (do
        let s15 ← endpoint.unblock_sporadic st' S14 dest
        let s16 ← obj.Tcb.set_sched_next st' dest s15 0#u64
        let s17 ← obj.Tcb.set_sched_prev st' dest s16 0#u64
        let (s18, a1) ← fastpath.switch_to st' ar s17 a dest
        ok (true, s18, a1)) := by
  unfold faultTail3 endpoint.unblock_sporadic
  simp only [Std.bind_assoc, bind_tc_ok, bind_ok]
  all_goals rfl

/-- `unblock_sporadic d` on the guarded store: `d`'s `SC` word, the SC's
`SPORADIC` word, the node's `CUR_SC`, and `unblock_check`'s accesses. -/
theorem endpoint.unblock_sporadic.guard (X : S) (d : obj.Tcb) {sb : Nat}
    (hsc : R (scA d)) (hsp : R (sporA (L.mem X (scA d))))
    (hcs : R (L.nodeAt X (L.cpu X) layout.node.CUR_SC))
    (hS : ScAcc R W (L.mem X (scA d)) sb) (hW : RefillsWF st X (L.mem X (scA d)) sb)
    (hrep : Aligned (L.nodeA X layout.node.REPROGRAM) ∧
      Outside (L.nodeA X layout.node.REPROGRAM) (L.mem X (scA d)) sb)
    (hct : R (ctA (L := L) X)) (hrp : W (L.nodeA X layout.node.REPROGRAM)) :
    endpoint.unblock_sporadic (guard st R W) X d = endpoint.unblock_sporadic st X d := by
  unfold endpoint.unblock_sporadic
  rw [obj.Tcb.sc.guard d X hsc, eq_of_spec_fd (obj.Tcb.sc.spec (L := L) X d)]; simp only [bind_ok]
  rw [sporadic.sc_sporadic.guard X _ (fun _ => hsp)]
  refine bind_guard_congr rfl fun b _ => ?_
  by_cases hb : b = true
  · rw [if_pos hb, if_pos hb, sched.cur_sc.guard X hcs]
    refine bind_guard_congr rfl fun c _ => ?_
    refine bind_guard_congr rfl fun b1 _ => ?_
    by_cases hb1 : b1 = true
    · rw [if_pos hb1, if_pos hb1, sporadic.unblock_check.guardS hS hW hrep hct hrp]
    · rw [if_neg hb1, if_neg hb1]
  · rw [if_neg hb, if_neg hb]

/-- **What an accepted fault fast path accesses** (at its entry state `s`,
with the checks' endpoint `ptr`, handler `dest` and reply `r`; `Z` the SC
sizes): the words the guarded sets `R` / `W` must hold for
`fastpath.fault.guard`. -/
structure FltAcc (Z : U64 → Nat) (R W : U64 → Prop) (s : S) (t ptr dest r : U64) : Prop where
  /-- The current core's node, read and written (`switch_to`'s tail). -/
  nd : ∀ o : U64, o.val < 4288 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o)
  dt : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN)
  kr : R (krA (L := L) s)
  tab : RdTab (L := L) R s
  /-- The fault handler cap of `t`. -/
  fh : ∀ sl, obj.Tcb.slot t layout.tcb.SLOT_FAULT_HANDLER = ok sl → R sl ∧ R (core.num.U64.wrapping_add sl 8#u64)
  eph : R (epHeadA ptr) ∧ W (epHeadA ptr)
  ept : R (epTSA ptr) ∧ W (epTSA ptr)
  /-- `t`: its fault words (written, then read by the message), registers,
  state and reply words. -/
  tf : ∀ K : U64, (K.val = 3376 ∨ K.val = 3384 ∨ K.val = 3392 ∨ K.val = 3400) →
    R (core.num.U64.wrapping_add t K) ∧ W (core.num.U64.wrapping_add t K)
  treg : Regs R t
  tst : W (stA t)
  trp : W (replyA t)
  /-- `dest`: the words read. -/
  drp : R (replyA dest)
  daf : R (affA dest)
  ddo : R (core.num.U64.wrapping_add dest 3432#u64)
  dsc0 : R (scA dest)
  diq : R (inqA dest)
  dpr : R (prioA dest)
  dyt : R (yieldA dest)
  dst : R (stA dest)
  dfi : R (regA dest layout.reg.FAULT_IP)
  den : R (nextA .Ep dest)
  dib : R (core.num.U64.wrapping_add dest 3512#u64)
  dvt : R (vtA dest) ∧ R (core.num.U64.wrapping_add (vtA dest) 8#u64)
  dbs : ∀ sl, obj.Tcb.slot dest layout.tcb.SLOT_BUFFER = ok sl → R sl ∧ R (core.num.U64.wrapping_add sl 8#u64)
  /-- `dest`: the words written. -/
  dw : W (nextA .Ep dest) ∧ W (prevA .Ep dest) ∧ W (nextA .Sched dest) ∧ W (prevA .Sched dest) ∧ W (stA dest)
  dreg : Regs W dest
  /-- The next queued thread's `EP_PREV`, when `dest` is not the tail. -/
  nxt : (L.epQ s ptr).end ≠ dest → W (prevA .Ep (L.mem s (nextA .Ep dest)))
  buf : ∀ rb, msg.lookup_ipc_buffer st s true dest = ok rb → BufW W rb
  rt : W (rTcbA r)
  /-- The handler's SC and the current SC. -/
  spo : R (sporA (L.mem s (scA dest)))
  dsc : ScAcc R W (L.mem s (scA dest)) (Z (L.mem s (scA dest)))
  csc : ScAcc R W (L.cscW s) (Z (L.cscW s))
  /-- The timer-min thread's deadline, the release head's SC. -/
  tm : L.mem s (tmA (L := L) s) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64)
  rh : L.mem s (rhA (L := L) s) ≠ 0#u64 → R (scA (L.mem s (rhA (L := L) s))) ∧
    (∀ b, InSC (L.mem s (scA (L.mem s (rhA (L := L) s)))) (Z (L.mem s (scA (L.mem s (rhA (L := L) s))))) b → R b) ∧
    RdHead (L := L) R s (L.mem s (scA (L.mem s (rhA (L := L) s))))

set_option maxHeartbeats 8000000 in
/-- **The accepted fault fast path on the guarded store** (`acc` for the trap
arm): with `R` / `W` holding `FltAcc` for the checks' objects, under
`sl_fault_foot`'s hypotheses (`hy0` [J] there), P1's `TimerOK` and P1's
`AsidOff` [J] (`P1/FastFinInv.lean`). -/
theorem fastpath.fault.guard {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar) {s : S} {a : A} {t : obj.Tcb} {n : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hrecv0 : ∀ {ptr badge dest r : U64}, FaultChecks st s t ptr badge dest r →
      L.mem s (stA dest) = sched.TS_BLOCKED_ON_RECV)
    (hF : FaultEntAt (L := L) T Cs Ω U Sg Rp s t)
    (hy0 : ∀ {ptr badge dest r : U64}, FaultChecks st s t ptr badge dest r → L.mem s (yieldA dest) = 0#u64)
    (hTm : TimerOK st T Cs s) (hAs : AsidOff (L := L) Ω Sg s)
    (hRW : ∀ {ptr badge dest r : U64}, FaultChecks st s t ptr badge dest r → FltAcc (L := L) Z R W s t ptr dest r)
    {sF : S} {aF : A} (h : fastpath.fault st ar s a t n = ok (true, sF, aF)) :
    fastpath.fault (guard st R W) ar s a t n = fastpath.fault st ar s a t n := by
  rw [h]
  obtain ⟨ptr, badge, dest, r, hc, hfast⟩ := fault_acc st ar h
  have hrecv := hrecv0 hc
  obtain ⟨⟨Q, RQ, hSQ⟩, hB, hX, hSg, hS⟩ := hI
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
  rw [faultTail2G_eq ar _ a t _ dest r badge hbuf hmrs hmi hS7 hS8] at hf0
  rw [faultTail3_eq] at hf0
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
  /- The guarded run. -/
  have K := hRW hc
  have hcs : L.cscW s ∈ Scs := hX0.cur
  have hrS : rTcbA r ∈ Sg := by
    have := (hO.rp r hr).1
    exact hO.rpW r hr _ (by show _ % 8 = 0; rw [rTcbA_val0]; omega) (by rw [rTcbA_val0] <;> omega)
      (by rw [rTcbA_val0]; omega)
  have eNY : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o := fun o => by rw [cY, nodeAt_of_ksb kY]
  have ndY : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 56 →
      L.mem Y (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o h1 h2 h3 h4
    rw [agY _ (nodeAt_aligned hN h1 h2) (fun e => node_ne_field hN h1 hdT hd' (K := 3480#u64) (by simp) e)
      (fun e => node_ne_field hN h1 hdT hd' (K := 3488#u64) (by simp) e)]
    exact K15.node o h1 h2 h3 h4
  have tfY : ∀ y ∈ T, ∀ K : U64, 3328 < K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3360 → K.val ≠ 3376 →
      K.val ≠ 3384 → K.val ≠ 3392 → K.val ≠ 3400 → K.val ≠ 3496 → K.val ≠ 3504 → K.val ≠ 3480 → K.val ≠ 3488 →
      L.mem Y (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    have hy' := hT y hy
    rw [agY _ (field_aligned hy' h2 h3) (field_ne hy' hd' h2 (K2 := 3480#u64) (by simp) (fun _ => by simpa using h11))
      (field_ne hy' hd' h2 (K2 := 3488#u64) (by simp) (fun _ => by simpa using h12))]
    exact K15.tcb y hy K h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hrhY : L.mem Y (rhA (L := L) Y) = L.mem s (rhA (L := L) s) := by
    show L.mem Y (L.nodeAt Y (L.cpu Y) _) = _
    rw [eNY]
    exact ndY _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have htmY : L.mem Y (tmA (L := L) Y) = L.mem s (tmA (L := L) s) := by
    show L.mem Y (L.nodeAt Y (L.cpu Y) _) = _
    rw [eNY]
    exact ndY _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  -- the release head: in `T`, its SC among `Scs` and active
  have rhF : L.mem s (rhA (L := L) s) ≠ 0#u64 → L.mem s (rhA (L := L) s) ∈ T ∧
      L.mem s (scA (L.mem s (rhA (L := L) s))) ∈ Scs ∧ L.mem s (scA (L.mem s (rhA (L := L) s))) ∈ Ac := by
    intro h0
    have hq := hSQ.release _ hcC
    have hhd : (L.relQ s (L.cpu s)).head = (RQ (L.cpu s)).headD 0#u64 := hq.head
    cases hl : RQ (L.cpu s) with
    | nil => rw [hl] at hhd; exact absurd hhd h0
    | cons y ys =>
      rw [hl] at hhd
      have e : L.mem s (rhA (L := L) s) = y := hhd
      have hyR : y ∈ RQ (L.cpu s) := by rw [hl]; simp
      have hyT := hq.mem y hyR
      have haf := hSQ.inR _ hcC y hyR
      have hfl : (L.mem s (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64 := (hSQ.released y hyT).2 (by rw [haf]; exact hyR)
      have hs0 := hB.r y hyT hfl
      rw [e]
      exact ⟨hyT, (hX0.bound y hyT hs0).1, hB.sact y hyT (Or.inr (Or.inl hfl)) hs0⟩
  -- an SC other than the handler's keeps its words to `Y`
  have scY : ∀ q ∈ Scs, q ≠ L.mem s (scA dest) → ∀ b, Aligned b → InSC q (Z q) b → L.mem Y b = L.mem s b := by
    intro q hq hne b hb hin
    have hbΩ := hS.sub _ ((hS.all _ hq).2.2 b hb hin)
    rw [agΩ b hbΩ]
    refine K15.omg b hbΩ (nrt _ hq b hin) fun hR => ?_
    have := hO.scDisj _ hq _ hdsc hne
    unfold InSC at hin; unfold InRing at hR; omega
  have hrhG : L.mem Y (rhA (L := L) Y) ≠ 0#u64 → L.mem Y (rhA (L := L) Y) ∈ T ∧
      R (scA (L.mem Y (rhA (L := L) Y))) ∧
      ∃ zq, SCin st Y Ω (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zq ∧
        (∀ b, InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zq b → R b) ∧
        (L.mem Y (scA (L.mem Y (rhA (L := L) Y))) ≠ L.cscW Y →
          ∀ b, InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zq b → Outside b (L.cscW Y) (Z (L.cscW Y))) ∧
        (L.mem Y (scA (L.mem Y (rhA (L := L) Y))) ≠ L.mem Y (scA dest) → L.mem Y (scA dest) ≠ L.cscW Y →
          ∀ b, InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zq b →
            Outside b (L.mem Y (scA dest)) (Z (L.mem Y (scA dest)))) := by
    rw [hrhY]
    intro h0
    obtain ⟨hyT, hqS, hqA⟩ := rhF h0
    obtain ⟨kr1, kr2, -⟩ := K.rh h0
    have esY : L.mem Y (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      tfY _ hyT 3464#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [esY, escY, ecY]
    generalize L.mem s (scA (L.mem s (rhA (L := L) s))) = q at hqS hqA kr2 ⊢
    refine ⟨hyT, kr1, Z q, ⟨?_, fun b hb hin => hS.sub _ ((hS.all _ hqS).2.2 b hb hin)⟩, kr2, ?_, ?_⟩
    · by_cases hqd : q = L.mem s (scA dest)
      · rw [hqd]; exact hWY
      · exact ((hS.all _ hqS).1 ((hS.act _ hqS).1 hqA)).agree (scY q hqS hqd)
    · intro hne b hin
      have := hO.scDisj _ hqS _ hcs hne
      unfold InSC at hin; unfold Outside; omega
    · intro hne _ b hin
      have := hO.scDisj _ hqS _ hdsc hne
      unfold InSC at hin; unfold Outside; omega
  have htmG : L.mem Y (tmA (L := L) Y) ≠ 0#u64 → L.mem Y (tmA (L := L) Y) ∈ T ∧
      R (core.num.U64.wrapping_add (L.mem Y (tmA (L := L) Y)) 3528#u64) := by
    rw [htmY]
    intro h0
    exact ⟨(hTm.min _ hcC).resolve_left h0, K.tm h0⟩
  have keepA : ∀ b ∈ Ω, b ∉ Sg → L.mem Y b = L.mem s b := fun b hb hs => by
    rw [agΩ b hb]
    exact K15.omg b hb (fun e => hs (e ▸ hrS)) fun hR => hs ((hS.all _ hdsc).2.2 b (hΩ b hb).1 hR.inSC)
  have hRV : RdVm (L := L) R Y dest := by
    refine ⟨K.dvt.1, K.dvt.2, ?_, ?_⟩
    · show R (core.num.U64.wrapping_add (L.ksb Y) _); rw [kY]; exact K.kr
    · refine fun hi hhi => ?_
      have aT := hAs hi hhi
      rw [kY, keepA _ aT.1 aT.2.1]
      exact K.tab hi hhi
  have hactY : L.mem Y (scA dest) = L.cscW Y → L.rmax Y (L.cscW Y) ≠ 0#u64 := by
    intro e
    rw [← e, escY]
    intro h0
    have hm := hWY.min_le
    rw [h0] at hm
    simp [sporadic.MIN_REFILLS] at hm
  have hNdY : ∀ o : U64, o.val < 4288 → R (L.nodeA Y o) ∧ W (L.nodeA Y o) := fun o ho => by
    show R (L.nodeAt Y (L.cpu Y) o) ∧ W (L.nodeAt Y (L.cpu Y) o)
    rw [eNY]; exact K.nd o ho
  have hSw := fastpath.switch_to.guard hA Y a P hcY htY hactY (by rw [eyY]; exact hy0 hc) hrhG htmG hRV hNdY
    (by rw [kY]; exact K.dt) (by rw [ecY]; exact K.csc) (fun _ => by rw [escY]; exact K.dsc)
    K.dsc0 K.dyt K.dst K.dfi (K.dreg _ (by simp [layout.reg.NEXT_IP])) K.dw.2.2.2.2 K.diq
  /- The checks. -/
  obtain ⟨sl, x, y, g, gr, hsl, hcap, hg⟩ := hc.cap
  obtain ⟨dm, p, hdm, hp, hhp⟩ := hc.prio
  obtain ⟨slb, hslb⟩ : ∃ sl, obj.Tcb.slot dest layout.tcb.SLOT_BUFFER = ok sl := by
    unfold obj.Tcb.slot; simp only [lift, bind_ok]; exact ⟨_, rfl⟩
  have hBm : RdBitmap (L := L) R s :=
    ⟨(K.nd _ (by simp [l1Off])).1, fun inv hinv => (K.nd _ (by simp; omega)).1⟩
  have tailEq : faultTailG (PathObl.guard st R W) ar s a t (error.Fault.UnknownSyscall n) fl4_abi.consts.fault.UnknownSyscall
      ptr badge dest r = ok (true, x1, x2) := by
    have tf := fun (K' : U64) (hK : K'.val = 3376 ∨ K'.val = 3384 ∨ K'.val = 3392 ∨ K'.val = 3400) => K.tf K' hK
    rw [faultTailG.guard_eq ar s a t n _ ptr badge dest r (tf 3376#u64 (by simp)).2 (tf 3384#u64 (by simp)).2
      (tf 3392#u64 (by simp)).2 (tf 3400#u64 (by simp)).2 K.ept.1 K.eph.2 K.ept.2
      (fun hl => by rw [eend] at hl; rw [eaf]; exact ⟨K.den, K.nxt hl⟩) K.dw.1 K.dw.2.1]
    rw [faultTail2G.guard_eq ar _ a t dest r badge hbuf hmrs hmi hS7 hS8 hslb K.dib (K.dbs slb hslb).1
      (K.dbs slb hslb).2 RR.hR5 (tf 3376#u64 (by simp)).1 (tf 3384#u64 (by simp)).1 (tf 3392#u64 (by simp)).1
      (tf 3400#u64 (by simp)).1 K.treg K.dreg (K.buf rb hbs) (K.dreg _ (by simp [layout.reg.MSG_INFO]))
      (K.dreg _ (by simp [layout.reg.BADGE])) K.rt K.dw.2.2.2.2 K.tst K.trp]
    rw [faultTail3_split ar (PathObl.guard st R W)]
    have h15f : endpoint.unblock_sporadic st (fS14 (L := L) S8 t dest r) dest = ok s15 := h15
    rw [endpoint.unblock_sporadic.guard _ dest K.dsc0 (by rw [esc14]; exact K.spo)
      (by rw [KF.cpu, nodeAt_of_ksb KF.ksb]; exact (K.nd _ (by simp [layout.node.CUR_SC])).1)
      (by rw [esc14]; exact K.dsc) (by rw [esc14]; exact hW14) hUo.rp
      (by show R (L.nodeAt _ (L.cpu _) _); rw [KF.cpu, nodeAt_of_ksb KF.ksb];
          exact (K.nd _ (by simp [layout.node.CUR_TIME])).1)
      (by show W (L.nodeAt _ (L.cpu _) _); rw [KF.cpu, nodeAt_of_ksb KF.ksb];
          exact (K.nd _ (by simp [layout.node.REPROGRAM])).2), h15f]
    simp only [bind_ok]
    rw [obj.Tcb.set_sched_next.guard dest s15 _ K.dw.2.2.1, obj.Tcb.set_sched_next.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_sched_prev.guard dest _ _ K.dw.2.2.2.1, obj.Tcb.set_sched_prev.ok]; simp only [bind_ok]
    rw [hY, hSw, hsw]
    simp only [bind_ok]
    rfl
  unfold fastpath.fault
  rw [sched.action.guard s (K.nd _ (by simp [layout.node.SCHED_ACTION])).1, hc.act]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [hsl]; simp only [bind_ok]
  rw [obj.Slot.cap.guard sl s (K.fh sl hsl).1 (K.fh sl hsl).2, hcap]; simp only [bind_ok]
  have hrs : L.mem s (rhA (L := L) s) ≠ 0#u64 → R (scA (L.mem s (rhA (L := L) s))) ∧
      RdHead (L := L) R s (L.mem s (scA (L.mem s (rhA (L := L) s)))) := fun h0 =>
    ⟨(K.rh h0).1, (K.rh h0).2.2⟩
  cases g <;> cases gr
  all_goals try (simp at hg; done)
  all_goals simp only [↓reduceIte, Bool.false_eq_true, if_true, if_false]
  all_goals
    rw [obj.Ep.state.guard ptr s K.ept.1, hc.ep]
    simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [obj.Ep.head.guard ptr s K.eph.1, hc.head]; simp only [bind_ok]
    rw [obj.Tcb.reply_obj.guard dest s K.drp, hc.reply]; simp only [bind_ok]
    rw [if_neg hc.r0]
    rw [fastpath.schedulable_here.guard s dest (K.nd _ (by simp [layout.node.CUR_TIME])).1
      (K.nd _ (by simp [layout.node.TIMER_MIN])).1 (K.nd _ (by simp [layout.node.RELEASE_HEAD])).1
      K.tm hrs K.dt K.cd K.daf K.ddo K.dsc0 K.diq, hc.here]
    simp only [bind_ok, ↓reduceIte]
    rw [sched.cur_domain.guard s K.cd, hdm]; simp only [bind_ok]
    rw [obj.Tcb.prio.guard dest s K.dpr, hp]; simp only [bind_ok]
    rw [sched.is_highest_prio.guard s dm p hBm, hhp]; simp only [bind_ok, ↓reduceIte]
    exact tailEq

end

end Fl4Proofs.P2.PathObl
