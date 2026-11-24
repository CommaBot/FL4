/-
# The ReplyRecv reads from the dispatch state, first batch (FL4 #56, m67 (R-a'))

m66's `RRReads` lists the general path's reads along an accepted ReplyRecv
run. This module derives seven of them from placement facts at the dispatch
state `X0` (`RREnt`: the TCBs placed, the current thread `t` and the reply's
thread `u` among them, the reply's TCB word, the endpoint and `t`'s SC
`REFILL_MAX` word outside the TCBs, `rptr ≠ 0`) and the run's own explicit
writes:

* `rt1` / `us1` / `sch1` at `X1` (only `t`'s state word written, Restart is
  runnable: `is_schedulable_congr`);
* `run6` (`u`'s state word just written Restart);
* `ns15` (`t`'s state word written BlockedOnRecv at `X9`; the writes up to
  `X15` are other TCB fields of `t`, the reply's TCB word and the endpoint's
  two words);
* `ucn` (`u` a TCB, 4K-aligned, is not `CHOOSE_NEW` = 1), `r0`.

The rest stay the bundle `RRReads2` (same parameters); `RRReads.of_ent`
assembles `RRReads`, `RRPre.of2` gives m66's `RRPre` from `RRPre2` and
`RREnt` at every accepted run's checks.
-/
import Fl4Proofs.P1.FastRRSame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- A word outside every TCB of `T`. -/
def OutT (T : Set U64) (a : U64) : Prop := Aligned a ∧ ∀ y ∈ T, a.val < y.val ∨ y.val + 2 ^ 12 ≤ a.val

theorem restart_runnable : Runnable sched.TS_RESTART := Or.inr (Or.inl rfl)

/-- `is_schedulable` reads `t`'s state (as runnable or not), its SC word, the
SC's `REFILL_MAX` word and `t`'s queue word. -/
theorem is_schedulable_congr {s s' : S} {t : U64}
    (hr : Runnable (L.mem s' (stA t)) ↔ Runnable (L.mem s (stA t)))
    (hsc : L.mem s' (scA t) = L.mem s (scA t))
    (hm : L.mem s (scA t) ≠ 0#u64 → L.rmax s' (L.mem s (scA t)) = L.rmax s (L.mem s (scA t)))
    (hq : L.mem s' (inqA t) = L.mem s (inqA t)) :
    sched.is_schedulable st s' t = sched.is_schedulable st s t := by
  unfold sched.is_schedulable
  rw [eq_of_spec_fd (sched.is_runnable.spec (L := L) s' t), eq_of_spec_fd (sched.is_runnable.spec (L := L) s t)]
  have hd : decide (L.mem s' (stA t) = sched.TS_RUNNING ∨ L.mem s' (stA t) = sched.TS_RESTART ∨
      L.mem s' (stA t) = sched.TS_RUNNING_VM) = decide (L.mem s (stA t) = sched.TS_RUNNING ∨
      L.mem s (stA t) = sched.TS_RESTART ∨ L.mem s (stA t) = sched.TS_RUNNING_VM) := by
    unfold Runnable at hr; exact decide_eq_decide.2 hr
  rw [hd]; simp only [bind_ok]
  split
  · simp only [eq_of_spec_fd (obj.Tcb.sc.spec (L := L) s' t), eq_of_spec_fd (obj.Tcb.sc.spec (L := L) s t), hsc,
      bind_ok, eq_of_spec_fd (obj.Sc.is_null.spec _)]
    split
    · rfl
    · rename_i h0
      have h0' : L.mem s (scA t) ≠ 0#u64 := by simpa using h0
      unfold sporadic.sc_active
      simp only [eq_of_spec_fd (obj.Sc.refill_max.spec (L := L) s' _),
        eq_of_spec_fd (obj.Sc.refill_max.spec (L := L) s _), hm h0', bind_ok,
        eq_of_spec_fd (sched.in_release_queue.spec (L := L) s' t),
        eq_of_spec_fd (sched.in_release_queue.spec (L := L) s t), hq]
  · rfl

theorem tcbw_ne_out {T : Set U64} {a y K : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hK : K.val < 4096)
    (ha : OutT T a) : core.num.U64.wrapping_add y K ≠ a := by
  intro e
  have e' := congrArg UScalar.val e
  rw [tcb_wadd_val (hT y hy) hK] at e'
  rcases ha.2 y hy with h | h <;> omega

theorem tcbw_al {T : Set U64} {y K : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hK : K.val < 4096)
    (h8 : K.val % 8 = 0) : Aligned (core.num.U64.wrapping_add y K) := by
  show _ % 8 = 0; rw [tcb_wadd_val (hT y hy) hK]; have := (hT y hy).align; omega

theorem tcbw_val {T : Set U64} {y K : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hK : K.val < 4096) :
    (core.num.U64.wrapping_add y K).val = y.val + K.val := tcb_wadd_val (hT y hy) hK

/-- **Placement facts at the dispatch state `X0`** of an accepted ReplyRecv
run (current thread `t`, reply `rptr`, endpoint `ep`, the reply's thread
`u`), from the P1 invariants there (`rrEnt_of`). -/
structure RREnt (T : Set U64) (X0 : S) (t rptr ep u : U64) : Prop where
  hT : TcbPlaced T
  ht : t ∈ T
  hu : u ∈ T
  hrO : OutT T (rTcbA rptr)
  hE : EpPlaced T ep
  hmO : L.mem X0 (scA t) ≠ 0#u64 → OutT T (maxA (L.mem X0 (scA t)))
  hr0 : rptr ≠ 0#u64

end

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- **The reads of `RRReads` left after the first batch** (m67): all but
`sch1`, `rt1`, `us1`, `run6`, `r0`, `ucn`, `ns15`, which `RRReads.of_ent`
derives from `RREnt` and the run's writes. -/
structure RRReads2 (t rptr ep u usc : U64) (X1 X2 X6 X7 X8 X11 X12 X15 : S) (a2 : A) : Prop where
  sc2 : obj.Tcb.sc st u X2 = ok usc
  sch6 : sched.schedule_tcb st X6 u = ok X6
  sc6 : obj.Tcb.sc st u X6 = ok usc
  rdy6 : sporadic.ready st X6 usc = ok true
  suf6 : sporadic.sufficient st ar X6 a2 usc 0#u64 = ok true
  pst : sched.possible_switch_to st X6 u = ok X7
  st7 : obj.Tcb.state st t X7 = ok sched.TS_RESTART
  act8 : L.actionW X8 ≠ sched.ACTION_RESUME_CURRENT
  ct8 : sched.cur_thread st X8 = ok t
  lk8 : ∃ i i1 b0 b1 b3 b4 g, obj.Tcb.reg st t X8 layout.reg.CAP = ok i1 ∧
    cspace.lookup_cap st X8 t i1 = ok (core.result.Result.Ok (capability.Cap.Endpoint ep b0 b1 true b3 b4)) ∧
    obj.Tcb.reg st t X8 layout.reg.REPLY = ok i ∧
    cspace.lookup_cap st X8 t i = ok (core.result.Result.Ok (capability.Cap.Reply rptr g))
  rt8 : obj.Reply.tcb st rptr X8 = ok 0#u64
  ntfn8 : ∃ n, obj.Tcb.bound_ntfn st t X8 = ok n ∧
    (n = 0#u64 ∨ (n ≠ 0#u64 ∧ ∃ i7, obj.Ntfn.state st n X8 = ok i7 ∧ ¬ i7 = obj.NTFN_ACTIVE ∧
      notification.maybe_return_sched_context st X8 n t = ok X8))
  ep8 : obj.Ep.state st ep X8 = ok obj.EP_IDLE
  act11 : L.actionW X11 ≠ sched.ACTION_RESUME_CURRENT
  q12 : ∃ q, endpoint.get_queue st X12 ep = ok q ∧ q.head = 0#u64
  T15 : L.mem X15 (L.nodeAt X15 (L.cpu X15) layout.node.TIMER_MIN) = 0#u64 ∨
    L.mem X15 (L.nodeAt X15 (L.cpu X15) layout.node.CUR_TIME) <
      L.mem X15 (tdA (L.mem X15 (L.nodeAt X15 (L.cpu X15) layout.node.TIMER_MIN)))
  R15 : L.mem X15 (L.nodeAt X15 (L.cpu X15) layout.node.RELEASE_HEAD) = 0#u64 ∨
    ¬ ((L.refill X15 (L.mem X15 (scA (L.mem X15 (L.nodeAt X15 (L.cpu X15) layout.node.RELEASE_HEAD))))
        (L.rhead X15 (L.mem X15 (scA (L.mem X15 (L.nodeAt X15 (L.cpu X15) layout.node.RELEASE_HEAD)))))).time ≤
      L.curTime X15)
  act15 : sched.action st X15 = ok u
  ct15 : sched.cur_thread st X15 = ok t
  hp15 : ∃ t1 b7 ff, sched.idle_thread st X15 = ok t1 ∧ obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t1 = ok b7 ∧
    (if b7 then ok true else do
      let i11 ← obj.Tcb.prio st u X15
      let i12 ← obj.Tcb.prio st t X15
      if i11 < i12 then ok true else ok false) = ok ff ∧
    (¬ ff = true ∨ (ff = true ∧ ∃ i11 i12 b8, sched.cur_domain st X15 = ok i11 ∧ obj.Tcb.prio st u X15 = ok i12 ∧
      sched.is_highest_prio st X15 i11 i12 = ok b8 ∧ b8 = true))
  dq15 : sched.dequeue st X15 u = ok X15
  /-- (#57, m67) The thread the accepted run switches to (`u`, made
  `TS_RESTART` at `X6`, so `activate_thread` makes it `TS_RUNNING`) is not
  `TS_RUNNING_VM` at the run's end: the general `finish`'s `vcpu.check` is a
  no-op (`finish_rr`). A read of the end state, as m62's `FaultNvm`. -/
  nvm : ∀ s' a', fastpath.switch_to st ar X15 a2 u = ok (s', a') →
    L.mem s' (stA (L.curW s')) ≠ sched.TS_RUNNING_VM

set_option maxHeartbeats 1600000 in
/-- **`RRReads` from `RREnt`, the checks and the remaining reads**. -/
theorem RRReads.of_entG {ty : U64} [HfrRestart st ar ty] {T : Set U64} {X0 : S} {a : A} {t rptr ep u usc : U64}
    {X1 X2 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 : S} {a2 : A}
    (E : RREnt (L := L) T X0 t rptr ep u) (C : RRChecksG st ar ty X0 a t rptr ep u usc)
    (e1 : obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1)
    (e6 : obj.Tcb.set_state st u X5 sched.TS_RESTART = ok X6)
    (e9 : obj.Tcb.set_state st t X8 sched.TS_BLOCKED_ON_RECV = ok X9)
    (e10 : obj.Tcb.set_block_obj st t X9 ep = ok X10)
    (e11 : obj.Tcb.set_reply_obj st t X10 rptr = ok X11)
    (e12 : obj.Reply.set_tcb st rptr X11 t = ok X12)
    (e13 : obj.Tcb.set_ep_next st t X12 0#u64 = ok X13)
    (e14 : obj.Tcb.set_ep_prev st t X13 0#u64 = ok X14)
    (e15 : obj.Ep.set_queue st ep X14 t t obj.EP_RECV = ok X15)
    (R : RRReads2 (L := L) ar t rptr ep u usc X1 X2 X6 X7 X8 X11 X12 X15 a2) :
    RRReads (L := L) ar t rptr ep u usc X1 X2 X6 X7 X8 X11 X12 X15 a2 := by
  have hT := E.hT
  have ht' := hT t E.ht
  have hu' := hT u E.hu
  -- the states as writes
  have w1 : X1 = L.wr X0 (stA t) sched.TS_RESTART := by
    have := obj.Tcb.set_state.spec (L := L) X0 t sched.TS_RESTART; rw [e1, WP.spec_ok] at this; exact this
  have w6 : X6 = L.wr X5 (stA u) sched.TS_RESTART := by
    have := obj.Tcb.set_state.spec (L := L) X5 u sched.TS_RESTART; rw [e6, WP.spec_ok] at this; exact this
  have w9 : X9 = L.wr X8 (stA t) sched.TS_BLOCKED_ON_RECV := by
    have := obj.Tcb.set_state.spec (L := L) X8 t sched.TS_BLOCKED_ON_RECV; rw [e9, WP.spec_ok] at this; exact this
  have w10 : X10 = L.wr X9 (blockA t) ep := by
    have := obj.Tcb.set_block_obj.wr (L := L) X9 t ep; rw [e10, WP.spec_ok] at this; exact this
  have w11 : X11 = L.wr X10 (replyA t) rptr := by
    have := obj.Tcb.set_reply_obj.wr (L := L) X10 t rptr; rw [e11, WP.spec_ok] at this; exact this
  have w12 : X12 = L.wr X11 (rTcbA rptr) t := by
    have := obj.Reply.set_tcb.spec (L := L) X11 rptr t; rw [e12, WP.spec_ok] at this; exact this
  have w13 : X13 = L.wr X12 (nextA .Ep t) 0#u64 := by
    rw [obj.Tcb.set_ep_next.ok] at e13; exact (ok_inj_ff e13).symm
  have w14 : X14 = L.wr X13 (prevA .Ep t) 0#u64 := by
    rw [obj.Tcb.set_ep_prev.ok] at e14; exact (ok_inj_ff e14).symm
  have w15 : X15 = epW (L := L) X14 ep t t obj.EP_RECV := by
    rw [obj.Ep.set_queue.ok] at e15; exact (ok_inj_ff e15).symm
  -- values and alignments
  have vS : (stA t).val = t.val + 3328 := by rw [stA_eq]; exact tcbw_val hT E.ht (by decide)
  have vSu : (stA u).val = u.val + 3328 := by rw [stA_eq]; exact tcbw_val hT E.hu (by decide)
  have vSc : (scA t).val = t.val + 3464 := tcbw_val hT E.ht (by decide)
  have vQ : (inqA t).val = t.val + 3592 := tcbw_val hT E.ht (by decide)
  have vB : (blockA t).val = t.val + 3336 := tcbw_val hT E.ht (by decide)
  have vRp : (replyA t).val = t.val + 3360 := tcbw_val hT E.ht (by decide)
  have vN : (nextA .Ep t).val = t.val + 3496 := by rw [nextA_val ht']; rfl
  have vP : (prevA .Ep t).val = t.val + 3504 := by rw [prevA_val ht']; rfl
  have vH : (epHeadA ep).val = ep.val := epHeadA_val
  have vTS : (epTSA ep).val = ep.val + 8 := epTSA_val E.hE
  have ta := ht'.align; have tf := ht'.fits; have ua := hu'.align; have uf := hu'.fits
  have ea := E.hE.align; have ed := E.hE.disj t E.ht
  have aS : Aligned (stA t) := by show _ % 8 = 0; omega
  have aSu : Aligned (stA u) := by show _ % 8 = 0; omega
  have aSc : Aligned (scA t) := by show _ % 8 = 0; omega
  have aQ : Aligned (inqA t) := by show _ % 8 = 0; omega
  have aB : Aligned (blockA t) := by show _ % 8 = 0; omega
  have aRp : Aligned (replyA t) := by show _ % 8 = 0; omega
  have aN : Aligned (nextA .Ep t) := by show _ % 8 = 0; omega
  have aP : Aligned (prevA .Ep t) := by show _ % 8 = 0; omega
  have aH : Aligned (epHeadA ep) := by show _ % 8 = 0; omega
  have aTS : Aligned (epTSA ep) := by show _ % 8 = 0; omega
  have nRO : stA t ≠ rTcbA rptr := by rw [stA_eq]; exact tcbw_ne_out hT E.ht (by decide) E.hrO
  have ne : ∀ a b : U64, a.val ≠ b.val → a ≠ b := fun a b h e => h (congrArg UScalar.val e)
  -- `u ≠ t`: `u` blocked on reply, `t` schedulable
  obtain ⟨b0, hsch0, hb0⟩ := C.sch
  subst hb0
  have hsp := sched.is_schedulable.spec' (L := L) X0 t
  rw [hsch0, WP.spec_ok] at hsp
  obtain ⟨hrun0, hsc0, -, -⟩ := hsp rfl
  obtain ⟨iu, hiu, hiuc⟩ := C.ust
  have hiu' : iu = sched.TS_BLOCKED_ON_REPLY := UScalar.eq_of_val_eq (by simpa using hiuc)
  have hus0 : L.mem X0 (stA u) = sched.TS_BLOCKED_ON_REPLY := by
    rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) X0 u)] at hiu; rw [← hiu', ok_inj_ff hiu]
  have hut : u ≠ t := by
    rintro rfl; rw [hus0] at hrun0; exact bor_not_runnable hrun0
  have hutv : u.val ≠ t.val := fun e => hut (UScalar.eq_of_val_eq e)
  have nSu : stA t ≠ stA u := by
    apply ne; rw [vS, vSu]
    rcases Nat.lt_or_ge t.val u.val with h | h <;> omega
  -- X1 reads
  have rt1 : obj.Reply.tcb st rptr X1 = ok u := by
    have h0 := C.tcb
    rw [eq_of_spec_fd (obj.Reply.tcb.blk (L := L) X0 rptr)] at h0
    rw [eq_of_spec_fd (obj.Reply.tcb.blk (L := L) X1 rptr), w1, mem_wr_ne' aS E.hrO.1 nRO]; exact h0
  have us1 : obj.Tcb.state st u X1 = ok sched.TS_BLOCKED_ON_REPLY := by
    rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) X1 u), w1, mem_wr_ne' aS aSu nSu, hus0]
  have sch1 : sched.is_schedulable st X1 t = ok true := by
    rw [← hsch0, w1]
    refine is_schedulable_congr ?_ ?_ ?_ ?_
    · rw [LawfulStore.mem_wr_same aS]; exact ⟨fun _ => hrun0, fun _ => restart_runnable⟩
    · exact mem_wr_ne' aS aSc (ne _ _ (by rw [vS, vSc]; omega))
    · intro h0
      unfold LawfulStore.rmax
      exact mem_wr_ne' aS (E.hmO h0).1 (by rw [stA_eq]; exact tcbw_ne_out hT E.ht (by decide) (E.hmO h0))
    · exact mem_wr_ne' aS aQ (ne _ _ (by rw [vS, vQ]; omega))
  -- X6 / X15 reads
  have run6 : sched.is_runnable st X6 u = ok true := by
    rw [eq_of_spec_fd (sched.is_runnable.spec (L := L) X6 u), w6, LawfulStore.mem_wr_same aSu]; simp
  have st15 : L.mem X15 (stA t) = sched.TS_BLOCKED_ON_RECV := by
    rw [w15]; unfold epW
    rw [mem_wr_ne' aTS aS (ne _ _ (by rw [vTS, vS]; omega)), mem_wr_ne' aH aS (ne _ _ (by rw [vH, vS]; omega)),
      w14, mem_wr_ne' aP aS (ne _ _ (by rw [vP, vS]; omega)), w13, mem_wr_ne' aN aS (ne _ _ (by rw [vN, vS]; omega)),
      w12, mem_wr_ne' E.hrO.1 aS (Ne.symm nRO), w11, mem_wr_ne' aRp aS (ne _ _ (by rw [vRp, vS]; omega)),
      w10, mem_wr_ne' aB aS (ne _ _ (by rw [vB, vS]; omega)), w9, LawfulStore.mem_wr_same aS]
  have ns15 : sched.is_schedulable st X15 t = ok false := by
    refine is_schedulable_not X15 t ?_
    rw [st15]; exact blocked_not_runnable (Or.inr (Or.inl rfl))
  have ucn : ¬ u = sched.ACTION_CHOOSE_NEW := by
    intro e; have := congrArg UScalar.val e; simp at this; omega
  exact {
    sch1 := sch1, rt1 := rt1, us1 := us1, sc2 := R.sc2, sch6 := R.sch6, sc6 := R.sc6, run6 := run6,
    rdy6 := R.rdy6, suf6 := R.suf6, pst := R.pst, st7 := R.st7, act8 := R.act8, ct8 := R.ct8, lk8 := R.lk8,
    rt8 := R.rt8, ntfn8 := R.ntfn8, ep8 := R.ep8, act11 := R.act11, r0 := E.hr0, q12 := R.q12, T15 := R.T15,
    R15 := R.R15, act15 := R.act15, ucn := ucn, ct15 := R.ct15, ns15 := ns15, hp15 := R.hp15, dq15 := R.dq15,
    nvm := R.nvm }

/-- `RRReads.of_entG` at an UnknownSyscall fault (pf1). -/
theorem RRReads.of_ent {T : Set U64} {X0 : S} {a : A} {t rptr ep u usc : U64}
    {X1 X2 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 : S} {a2 : A}
    (E : RREnt (L := L) T X0 t rptr ep u) (C : RRChecks st ar X0 a t rptr ep u usc)
    (e1 : obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1)
    (e6 : obj.Tcb.set_state st u X5 sched.TS_RESTART = ok X6)
    (e9 : obj.Tcb.set_state st t X8 sched.TS_BLOCKED_ON_RECV = ok X9)
    (e10 : obj.Tcb.set_block_obj st t X9 ep = ok X10)
    (e11 : obj.Tcb.set_reply_obj st t X10 rptr = ok X11)
    (e12 : obj.Reply.set_tcb st rptr X11 t = ok X12)
    (e13 : obj.Tcb.set_ep_next st t X12 0#u64 = ok X13)
    (e14 : obj.Tcb.set_ep_prev st t X13 0#u64 = ok X14)
    (e15 : obj.Ep.set_queue st ep X14 t t obj.EP_RECV = ok X15)
    (R : RRReads2 (L := L) ar t rptr ep u usc X1 X2 X6 X7 X8 X11 X12 X15 a2) :
    RRReads (L := L) ar t rptr ep u usc X1 X2 X6 X7 X8 X11 X12 X15 a2 := by
  apply RRReads.of_entG (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


/-- `lookup_cap` of a cptr whose walk from the root found a slot. -/
theorem lookup_cap_of_found {s : S} {t sl : U64} {root : capability.Cap} {i : U64} {found : cspace.Resolved}
    {c : capability.Cap}
    (hsl : obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok sl) (hroot : obj.Slot.cap st sl s = ok root)
    (hr : cspace.resolve_address_bits st s root i cspace.WORD_BITS = ok (core.result.Result.Ok found))
    (hc : obj.Slot.cap st found.slot s = ok c) :
    cspace.lookup_cap st s t i = ok (core.result.Result.Ok c) := by
  unfold cspace.lookup_cap cspace.lookup_slot
  rw [hsl]; simp only [bind_ok]
  rw [hroot]; simp only [bind_ok]
  rw [hr]; simp only [bind_ok]
  rw [hc]; simp only [bind_ok]

/-- **`RREnt` at the dispatch state** from the P1 invariants there (`BXI`,
`XG`) and the receive-side cap typing (`EntryHyps0.recvOK`): the `REPLY` cap
names a reply object (so `rptr ≠ 0` and its thread `u ≠ 0` is a TCB,
`ReplyInv.back`; its TCB word is a frame word, `ObjsOK.rpW`), the `CAP` cap a
heap endpoint (placed, `EpsOK`), `t`'s SC an SC whose `REFILL_MAX` word is
among `Ω` (`ScExtra.bound`, `ObjsOK.scW`). -/
theorem rrEnt_lkG {ty : U64} [HfrRestart st ar ty] {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {s : S} {a : A} {t rptr ep u usc : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hlk : ∀ cptr, cspace.lookup_cap st s (L.curW s) cptr ⦃ r => ∀ c, r = .Ok c → CapTyped H Rp Nt c ⦄)
    (et : sched.cur_thread st s = ok t)
    (hrc : fastpath.reply_caps st s t = ok (some (rptr, ep))) (C : RRChecksG st ar ty s a t rptr ep u usc) :
    RREnt (L := L) T s t rptr ep u := by
  have et' : t = L.curW s := by
    rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)] at et; exact (ok_inj_ff et).symm
  obtain ⟨⟨Q, R, hSQ⟩, hB, hX, hSg, hS⟩ := hI
  obtain ⟨⟨sl, root, hsl, hroot, ⟨i, found, g, hi, hr, hc⟩, ⟨i1, found1, b0, b1, b3, b4, hi1, hr1, hc1⟩⟩⟩ :=
    reply_caps_some st hrc
  have hl1 := hlk i
  rw [← et', lookup_cap_of_found hsl hroot hr hc, WP.spec_ok] at hl1
  have hrR : rptr ∈ Rp := (hl1 _ rfl).2.2 rptr g rfl
  have hl2 := hlk i1
  rw [← et', lookup_cap_of_found hsl hroot hr1 hc1, WP.spec_ok] at hl2
  have hpH : H ep = some .ep := (hl2 _ rfl).1 ep b0 b1 true b3 b4 rfl
  have hrt : L.mem s (rTcbA rptr) = u := by
    have h0 := C.tcb; rw [eq_of_spec_fd (obj.Reply.tcb.blk (L := L) s rptr)] at h0; exact ok_inj_ff h0
  have hu0 : u ≠ 0#u64 := by
    obtain ⟨b, hb, hbn⟩ := C.u0
    rw [is_null_ok] at hb; have e := ok_inj_ff hb; subst e; simpa using hbn
  obtain ⟨hr0, huT, -, -⟩ := hX.2.1.back rptr hrR (by rw [hrt]; exact hu0)
  rw [hrt] at huT
  have hrΩ : rTcbA rptr ∈ Ω := by
    refine hSg.sub _ (hX.1.rpW rptr hrR _ ?_ ?_ ?_)
    · show (rTcbA rptr).val % 8 = 0
      rw [rTcbA_val0]; have := (hX.1.rp rptr hrR).1; omega
    · rw [rTcbA_val0]
    · rw [rTcbA_val0]; omega
  have oR := hSQ.omega _ hrΩ
  obtain ⟨E, EQ, hW⟩ := hSQ.eps
  obtain ⟨w1, -, -, -, -, w6⟩ := hW
  have hpE : ep ∈ E := (w6.2.2.1 ep).2 (Or.inl hpH)
  obtain ⟨hEP, -, -⟩ := w1 ep hpE
  have htT : t ∈ T := by rw [et']; exact hSQ.curT
  refine ⟨hSQ.tcbs, htT, huT, ⟨oR.1, oR.2.1⟩, hEP, fun h0 => ?_, hr0⟩
  have hcS : L.mem s (scA t) ∈ Scs := (hX.2.2.toScExtra0.bound t htT h0).1
  obtain ⟨hal, h1, h2⟩ := maxA_facts hX.1 hcS
  have oM := hSQ.omega _ (hX.1.scW _ hcS _ hal ⟨h1, h2⟩)
  exact ⟨oM.1, oM.2.1⟩

/-- `rrEnt_lkG` at an UnknownSyscall fault (pf1). -/
theorem rrEnt_lk {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {s : S} {a : A} {t rptr ep u usc : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hlk : ∀ cptr, cspace.lookup_cap st s (L.curW s) cptr ⦃ r => ∀ c, r = .Ok c → CapTyped H Rp Nt c ⦄)
    (et : sched.cur_thread st s = ok t)
    (hrc : fastpath.reply_caps st s t = ok (some (rptr, ep))) (C : RRChecks st ar s a t rptr ep u usc) :
    RREnt (L := L) T s t rptr ep u := by
  apply rrEnt_lkG (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


/-- `rrEnt_lk` with the cap typing from `EntryHyps0.recvOK` at an `XG` state. -/
theorem rrEnt_ofG {ty : U64} [HfrRestart st ar ty] {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {P3Ok : S → Prop}
    (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s : S} {a : A} {t rptr ep u usc : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (et : sched.cur_thread st s = ok t)
    (hrc : fastpath.reply_caps st s t = ok (some (rptr, ep))) (C : RRChecksG st ar ty s a t rptr ep u usc) :
    RREnt (L := L) T s t rptr ep u :=
  rrEnt_lkG ar hI (E0.recvOK Ac s hG hI).1 et hrc C

/-- `rrEnt_ofG` at an UnknownSyscall fault (pf1). -/
theorem rrEnt_of {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {P3Ok : S → Prop}
    (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s : S} {a : A} {t rptr ep u usc : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (et : sched.cur_thread st s = ok t)
    (hrc : fastpath.reply_caps st s t = ok (some (rptr, ep))) (C : RRChecks st ar s a t rptr ep u usc) :
    RREnt (L := L) T s t rptr ep u := by
  apply rrEnt_ofG (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


/-- **The ReplyRecv read bundle after the first batch** (m67): m66's `RRPre`
with `RRReads2` (seven reads fewer) in place of `RRReads`. -/
def RRPre2G (ty : U64) (X0 : S) (a : A) : Prop :=
  ∀ (t rptr ep u usc : U64) (X1 X2 : S) (a1 : A) (b9 : Bool) (X3 : S),
    sched.cur_thread st X0 = ok t → fastpath.reply_caps st X0 t = ok (some (rptr, ep)) →
    RRChecksG st ar ty X0 a t rptr ep u usc →
    obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1 →
    ipc.reply_remove st ar X1 a rptr u = ok (X2, a1) →
    sporadic.sc_sporadic st X2 usc = ok b9 →
    (if b9 then do
      let i13 ← obj.Sc.cpu st usc X2
      let i14 ← obj.node_get st X2 i13 layout.node.CUR_SC
      if usc != i14 then sporadic.unblock_check st X2 usc else ok X2
    else ok X2) = ok X3 →
    RRR3G (st := st) ty X3 t u ∧
    ∀ (X4 : S) (a2 : A) (X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 : S),
      faults.handle_fault_reply st ar X3 a1 u t = ok (true, X4, a2) →
      faults.clear_fault st X4 u = ok X5 →
      obj.Tcb.set_state st u X5 sched.TS_RESTART = ok X6 →
      sched.set_action st X6 u = ok X7 →
      obj.Tcb.set_state st t X7 sched.TS_RUNNING = ok X8 →
      obj.Tcb.set_state st t X8 sched.TS_BLOCKED_ON_RECV = ok X9 →
      obj.Tcb.set_block_obj st t X9 ep = ok X10 →
      obj.Tcb.set_reply_obj st t X10 rptr = ok X11 →
      obj.Reply.set_tcb st rptr X11 t = ok X12 →
      obj.Tcb.set_ep_next st t X12 0#u64 = ok X13 →
      obj.Tcb.set_ep_prev st t X13 0#u64 = ok X14 →
      obj.Ep.set_queue st ep X14 t t obj.EP_RECV = ok X15 →
      RRReads2 (L := L) ar t rptr ep u usc X1 X2 X6 X7 X8 X11 X12 X15 a2

/-- `RRPre2G` at an UnknownSyscall fault (pf1). -/
abbrev RRPre2 (X0 : S) (a : A) : Prop :=
  RRPre2G (L := L) ar fl4_abi.consts.fault.UnknownSyscall X0 a


/-- `RRPre` from `RRPre2` and `RREnt` at every accepted run's checks. -/
theorem RRPre.of2G {ty : U64} [HfrRestart st ar ty] {T : Set U64} {X0 : S} {a : A}
    (hE : ∀ t rptr ep u usc, sched.cur_thread st X0 = ok t → fastpath.reply_caps st X0 t = ok (some (rptr, ep)) →
      RRChecksG st ar ty X0 a t rptr ep u usc → RREnt (L := L) T X0 t rptr ep u)
    (h : RRPre2G (L := L) ar ty X0 a) : RRPreG (L := L) ar ty X0 a := by
  intro t rptr ep u usc X1 X2 a1 b9 X3 hct hrc hC e1 e2 e3s e3
  obtain ⟨R3, hR⟩ := h t rptr ep u usc X1 X2 a1 b9 X3 hct hrc hC e1 e2 e3s e3
  refine ⟨R3, fun X4 a2 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 => ?_⟩
  exact RRReads.of_entG ar (hE t rptr ep u usc hct hrc hC) hC e1 e6 e9 e10 e11 e12 e13 e14 e15
    (hR X4 a2 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15)

/-- `RRPre.of2G` at an UnknownSyscall fault (pf1). -/
theorem RRPre.of2 {T : Set U64} {X0 : S} {a : A}
    (hE : ∀ t rptr ep u usc, sched.cur_thread st X0 = ok t → fastpath.reply_caps st X0 t = ok (some (rptr, ep)) →
      RRChecks st ar X0 a t rptr ep u usc → RREnt (L := L) T X0 t rptr ep u)
    (h : RRPre2 (L := L) ar X0 a) : RRPre (L := L) ar X0 a := by
  apply RRPre.of2G (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


/-- **`RRPreAt` with `RRPre2`**: the bundle at every dispatch state of the
entry, seven reads fewer than m66's `RRPreAt`. -/
def RRPreAt2G (ty : U64) (s : S) (a : A) : Prop :=
  ∀ t nx s1 s2 a2, sched.cur_thread st s = ok t → obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
    obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
    syscall.budget_ok st ar s1 a = ok (true, s2, a2) → RRPre2G (L := L) ar ty s2 a2

/-- `RRPreAt2G` at an UnknownSyscall fault (pf1). -/
abbrev RRPreAt2 (s : S) (a : A) : Prop :=
  RRPreAt2G (L := L) ar fl4_abi.consts.fault.UnknownSyscall s a


/-- **`RRPreAt` from `RRPreAt2`** at an entry state: the dispatch state is a
`BXI` / `XG` state (`budget_ok.bxc` after `reg_entry`), so `rrEnt_of` gives
`RREnt` there. -/
theorem RRPreAt.of2G {ty : U64} [HfrRestart st ar ty] {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {P3Ok : S → Prop}
    (hA : P0.ArchTotal ar) (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s : S} {a : A} (hP : P3Ok s) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hR : RRPreAt2G (L := L) ar ty s a) : RRPreAtG (L := L) ar ty s a := by
  intro t nx s1 s2 a2 et enx es1 hb
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
  have hx := syscall.budget_ok.bxc hA E0 s1 a h1 he1.xg
  rw [hb, WP.spec_ok] at hx
  exact RRPre.of2G ar (T := T) (fun t' rptr ep u usc et2 hrc hC => rrEnt_ofG ar E0 hx.1 (hx.2.2 rfl) et2 hrc hC)
    (hR t nx s1 s2 a2 et enx es1 hb)

/-- `RRPreAt.of2G` at an UnknownSyscall fault (pf1). -/
theorem RRPreAt.of2 {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {P3Ok : S → Prop}
    (hA : P0.ArchTotal ar) (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s : S} {a : A} (hP : P3Ok s) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hR : RRPreAt2 (L := L) ar s a) : RRPreAt (L := L) ar s a := by
  apply RRPreAt.of2G (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- **Native kernel entries keep `EntryInv`, ReplyRecv half from seven reads
fewer** (m67 (R-a') first batch): `entry_of7r` with `hRP : RRPreAt` replaced
by `hRP : RRPreAt2` (`RRReads2`: `sch1`, `rt1`, `us1`, `run6`, `r0`, `ucn`,
`ns15` derived from the P1 invariants at the dispatch state, `rrEnt_of`, and
the run's writes, `RRReads.of_ent`). -/
theorem kernel_entry.entry_of7r2 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps4 st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hNv : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → FaultNvmPre (L := L) ar s a number)
    (hRP : RRPreAt2 (L := L) ar s a) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) := by
  have E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact (G.gaps3 hA hσ C Pd Pt P.xfer).gaps hA P C
    exact (EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  exact kernel_entry.entry_of7r hA GF hσ s a hP h hX hAs hNv (RRPreAt.of2 ar hA E0 hP h hRP)

end

end Fl4Proofs.P1
