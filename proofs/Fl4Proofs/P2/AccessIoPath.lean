/-
# P2: the accepted I/O port local path on the guarded store (line p2io)

`syscall.handle_ioport_local.guard_acc`: an accepted run of the I/O port
local path (`true`) on `guard st R W` ends exactly as the real run, given the
words each step touches, stated where the step runs (run-relative):

* at the entry state: the node's words (read and written), the current
  thread's `MSG_INFO`, flags, `NEXT_IP` (read) and `FAULT_IP` (written);
* after the prefix (`FAULT_IP` write, `update_timestamp`), `IoMid`: the
  current thread's `CAP`, `YIELD_TO`, `MSG_INFO`, `R10`, its CSpace walk
  (`invocation_ok.guard` / `handle_invocation.guard_io`'s premises), the
  current SC's head refill, `schedulable_here`'s words, the I/O port arm's
  words (`IoK`), and the facts `guard_io` uses (`msg_info`, current thread);
* after the invocation, `FinOK`: `finish.guard_resume`'s premises (nothing
  due, action `RESUME_CURRENT`, the switch / interrupt / activate / vcpu
  steps), with the entry's kernel base and core.

The two arms (`SysSend`, `SysCall`) are the same term `ioTail`
(`handle_ioport_local_eq`, by `rfl` on the real store's definition only).

Generic over the Arch instance. Premises: none (the hypotheses are the
run-relative sets, discharged in the I/O port obligation).
-/
import Fl4Proofs.P2.AccessIoFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]

/-- The I/O port local path after the trap-flag check (both arms). -/
def ioTail {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (t : obj.Tcb)
    (info : msginfo.MessageInfo) (number : I64) : Result (Bool × S × A) := do
  let b ← ioport.is_port_label info.label
  if b
  then
    let next ← obj.Tcb.reg m t s layout.reg.NEXT_IP
    let i2 ← lift (core.num.U64.wrapping_sub next 2#u64)
    let s1 ← obj.Tcb.set_reg m t s layout.reg.FAULT_IP i2
    let (s2, a1) ← sched.update_timestamp m ar s1 a
    let cptr ← obj.Tcb.reg m t s2 layout.reg.CAP
    let csc ← sched.cur_sc m s2
    let i3 ← sched.action m s2
    if i3 != sched.ACTION_RESUME_CURRENT
    then ok (false, s2, a1)
    else
      let i4 ← obj.Tcb.yield_to m t s2
      if i4 != 0#u64
      then ok (false, s2, a1)
      else
        if info.extra_caps != 0#u64
        then ok (false, s2, a1)
        else
          let b1 ← ioport.invocation_ok m s2 t cptr info
          if b1
          then
            let i5 ← sched.consumed m s2
            let b2 ← sporadic.sufficient m ar s2 a1 csc i5
            if b2
            then
              let b3 ← fastpath.schedulable_here m s2 t
              if b3
              then
                let (r, s3, a2) ←
                  syscall.handle_invocation m ar s2 a1 (number = fl4_abi.syscall.SysCall) true
                    (number = fl4_abi.syscall.SysCall) false cptr
                let (_, s4, a3) ← syscall.after_invocation m ar s3 a2 r
                let (s5, a4) ← syscall.finish m ar s4 a3
                ok (true, s5, a4)
              else ok (false, s2, a1)
            else ok (false, s2, a1)
          else ok (false, s2, a1)
  else ok (false, s, a)

theorem handle_ioport_local_eq {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)
    (number : I64) :
    syscall.handle_ioport_local m ar s a number = (do
      let t ← sched.cur_thread m s
      let info ← msg.msg_info m s t
      if layout.NUM_DOMAINS != 1#u64
      then ok (false, s, a)
      else
        let i ← obj.Tcb.flags m t s
        let i1 ← lift (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS)
        if i1 != 0#u64
        then ok (false, s, a)
        else
          if number != fl4_abi.syscall.SysCall
          then
            if number != fl4_abi.syscall.SysSend
            then ok (false, s, a)
            else ioTail m ar s a t info number
          else ioTail m ar s a t info number) := rfl

/-- The words the steps between the prefix and the invocation touch, at the
post-prefix state `s2` (entry `s`, current thread `t`, `cptr` its `CAP`; `C` the
CNodes the CSpace walk may enter, `sl` the thread's CTABLE slot). -/
structure IoMid (R W : U64 → Prop) (s s2 : S) (t : U64) (info : msginfo.MessageInfo) (cptr : U64)
    (C : U64 → Prop) (sl : U64) : Prop where
  k : L.ksb s2 = L.ksb s
  c : L.cpu s2 = L.cpu s
  cur : L.curW s2 = t
  mi : msg.msg_info st s2 t = ok info
  rmi : R (regA t layout.reg.MSG_INFO)
  r10 : R (regA t layout.reg.R10)
  cap : R (regA t layout.reg.CAP)
  yld : R (core.num.U64.wrapping_add t 3472#u64)
  hsl : obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok sl
  hR0 : R sl
  hR8 : R (core.num.U64.wrapping_add sl 8#u64)
  hRc : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s2 = ok (.CNode p' r' gs' g') →
    R (cnSlot p off) ∧ R (core.num.U64.wrapping_add (cnSlot p off) 8#u64)
  hcl : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s2 = ok (.CNode p' r' gs' g') → C p'
  hroot : ∀ p r gs g, obj.Slot.cap st sl s2 = ok (.CNode p r gs g) → C p
  hRf : ∀ x, cspace.lookup_slot st s2 t cptr = ok (.Ok x) →
    R x.slot ∧ R (core.num.U64.wrapping_add x.slot 8#u64)
  rh : RdHead (L := L) R s2 (L.cscW s2)
  td : L.mem s2 (tmA (L := L) s2) ≠ 0#u64 →
    R (core.num.U64.wrapping_add (L.mem s2 (tmA (L := L) s2)) 3528#u64)
  rs : L.mem s2 (rhA (L := L) s2) ≠ 0#u64 → R (scA (L.mem s2 (rhA (L := L) s2))) ∧
    RdHead (L := L) R s2 (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))
  dt : R (core.num.U64.wrapping_add (L.ksb s2) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb s2) layout.ks.CUR_DOMAIN)
  af : R (affA t)
  dom : R (core.num.U64.wrapping_add t 3432#u64)
  iok : IoK (L := L) R W s2 t

/-- `finish.guard_resume`'s premises at the post-invocation state `s3`, with
the entry's kernel base and core. -/
structure FinOK {A : Type} (R W : U64 → Prop) (ar : machine.Arch A) (s s3 : S) (a3 : A) : Prop where
  k : L.ksb s3 = L.ksb s
  c : L.cpu s3 = L.cpu s
  h0 : L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN) = 0#u64
  h1 : L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.RELEASE_HEAD) = 0#u64
  ha : L.actionW s3 = sched.ACTION_RESUME_CURRENT
  hsw : ∀ s4, sched.set_action st s3 sched.ACTION_RESUME_CURRENT = ok s4 →
    sched.switch_sched_context (PathObl.guard st R W) ar s4 a3 = sched.switch_sched_context st ar s4 a3
  hfr : ∀ s4 s5 a4, sched.set_action st s3 sched.ACTION_RESUME_CURRENT = ok s4 →
    sched.switch_sched_context st ar s4 a3 = ok (s5, a4) →
    L.ksb s5 = L.ksb s3 ∧ L.cpu s5 = L.cpu s3 ∧
    (L.mem s5 (L.nodeAt s5 (L.cpu s5) layout.node.REPROGRAM) ≠ 0#u64 →
      sched.set_next_interrupt (PathObl.guard st R W) ar s5 a4 = sched.set_next_interrupt st ar s5 a4 ∧
      ∀ s7 a5, sched.set_next_interrupt st ar s5 a4 = ok (s7, a5) → L.ksb s7 = L.ksb s3 ∧ L.cpu s7 = L.cpu s3)
  hact : ∀ s1 a1, sched.schedule st ar s3 a3 = ok (s1, a1) →
    sched.activate_thread (PathObl.guard st R W) ar s1 a1 = sched.activate_thread st ar s1 a1
  hvc : ∀ s1 a1 s2 a2, sched.schedule st ar s3 a3 = ok (s1, a1) →
    sched.activate_thread st ar s1 a1 = ok (s2, a2) →
    R (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) ∧ R (stA (L.curW s2)) ∧
      L.mem s2 (stA (L.curW s2)) = sched.TS_RUNNING

/-- **The I/O port path after the flag check, accepted, on the guarded store.** -/
theorem ioTail.guard {A : Type} (ar : machine.Arch A) {s s' : S} {a a' : A} {t : U64}
    {info : msginfo.MessageInfo} {number : I64}
    (hNd : ∀ o : U64, o.val < 4288 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hnx : R (regA t layout.reg.NEXT_IP)) (hfi : W (regA t layout.reg.FAULT_IP))
    (hmid : ∀ nx s1 s2 a1, obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) →
      ∃ C sl, IoMid (L := L) R W s s2 t info (L.mem s2 (regA t layout.reg.CAP)) C sl)
    (hfin : ∀ s2 a1 r s3 a2, syscall.handle_invocation st ar s2 a1 (decide (number = fl4_abi.syscall.SysCall))
      true (decide (number = fl4_abi.syscall.SysCall)) false (L.mem s2 (regA t layout.reg.CAP)) = ok (r, s3, a2) →
      FinOK (L := L) R W ar s s3 a2)
    (h : ioTail st ar s a t info number = ok (true, s', a')) :
    ioTail (PathObl.guard st R W) ar s a t info number = ok (true, s', a') := by
  unfold ioTail at h ⊢
  revert h
  refine tr_bind_same (fun b _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  refine tr_bind (fun x hx _ => by rw [obj.Tcb.reg.guard t s _ hnx]; exact hx) (fun nx enx => ?_)
  simp only [lift, bind_ok]
  refine tr_bind (fun x hx _ => by rw [obj.Tcb.set_reg.guard t s _ _ hfi]; exact hx) (fun s1 es1 => ?_)
  have e1 : s1 = L.wr s (regA t layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [set_reg_ok'] at es1; exact (ok_inj_ff es1).symm
  have k1 : L.ksb s1 = L.ksb s := by rw [e1, L.ksb_wr]
  have c1 : L.cpu s1 = L.cpu s := by rw [e1, LawfulStore.cpu_wr]
  refine tr_bind (fun x hx _ => by
      rw [sched.update_timestamp.guard ar s1 a (nd_at hNd k1 c1 _ (by simp [layout.node.CUR_TIME])).1
        (nd_at hNd k1 c1 _ (by simp [layout.node.CUR_TIME])).2
        (nd_at hNd k1 c1 _ (by simp [layout.node.CONSUMED])).1
        (nd_at hNd k1 c1 _ (by simp [layout.node.CONSUMED])).2]; exact hx)
    (fun x eu => ?_)
  obtain ⟨s2, a1⟩ := x
  simp only [uncurry_apply_pair]
  obtain ⟨C, sl, M⟩ := hmid nx s1 s2 a1 enx es1 eu
  have nd2 := nd_at hNd M.k M.c
  have Mc := M.cur
  subst Mc
  rw [obj.Tcb.reg.guard (L.curW s2) s2 _ M.cap, reg_ok]
  simp only [bind_ok]
  rw [sched.cur_sc.guard s2 (nd2 _ (by simp [layout.node.CUR_SC])).1]
  refine tr_bind_same (fun csc ecsc => ?_)
  rw [sched.action.guard s2 (nd2 _ (by simp [layout.node.SCHED_ACTION])).1]
  refine tr_bind_same (fun i3 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.yield_to.guard (L.curW s2) s2 M.yld]
  refine tr_bind_same (fun i4 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  beta_reduce
  refine tr_ite (fun _ h => h) (fun hx0 => ?_)
  have hx : info.extra_caps = 0#u64 := by
    simp only [bne_iff_ne, ne_eq, not_not] at hx0; exact hx0
  refine tr_bind (fun b1 hb1 _ => ioport.invocation_ok.guard C M.hsl M.hR0 M.hR8 M.hRc M.hcl M.hroot
    M.hRf M.iok.1.ib M.iok.1.bs M.r10 hb1) (fun b1 eb1 => ?_)
  beta_reduce
  refine tr_ite (fun hb => ?_) (fun _ h => h)
  rw [sched.consumed.guard s2 (nd2 _ (by simp [layout.node.CONSUMED])).1]
  refine tr_bind_same (fun i5 _ => ?_)
  have ecsc' : csc = L.cscW s2 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s2)] at ecsc; exact (ok_inj_ff ecsc).symm
  subst ecsc'
  rw [sporadic.sufficient.guard ar s2 a1 _ i5 M.rh]
  refine tr_bind_same (fun b2 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [fastpath.schedulable_here.guard s2 (L.curW s2) (nd2 _ (by simp [layout.node.CUR_TIME])).1
    (nd2 _ (by simp [layout.node.TIMER_MIN])).1 (nd2 _ (by simp [layout.node.RELEASE_HEAD])).1
    M.td M.rs M.dt M.cd M.af M.dom M.iok.1.sc M.iok.1.inq]
  refine tr_bind_same (fun b3 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  have hb1t : b1 = true := by assumption
  subst hb1t
  refine tr_bind (fun y ey _ => by
      have e := syscall.handle_invocation.guard_io ar (call := decide (number = fl4_abi.syscall.SysCall))
        (blocking := true) (cd := decide (number = fl4_abi.syscall.SysCall)) (fp := false) C
        (nd2 _ (by simp [layout.node.CUR_THREAD])).1 M.mi M.rmi hx
        eb1 M.hsl M.hR0 M.hR8 M.hRc M.hcl M.hroot M.hRf
        M.iok ey
      exact e.1)
    (fun y ey => ?_)
  obtain ⟨r, s3, a2⟩ := y
  simp only [uncurry_apply_pair]
  have F := hfin s2 a1 r s3 a2 ey
  have hr : r = .Ok () := by
    have e := syscall.handle_invocation.guard_io (R := R) (W := W) ar
        (call := decide (number = fl4_abi.syscall.SysCall))
        (blocking := true) (cd := decide (number = fl4_abi.syscall.SysCall)) (fp := false) C
        (nd2 _ (by simp [layout.node.CUR_THREAD])).1 M.mi M.rmi hx
        eb1 M.hsl M.hR0 M.hR8 M.hRc M.hcl M.hroot M.hRf
        M.iok ey
    exact e.2
  subst hr
  rw [syscall.after_invocation.ok_eq, syscall.after_invocation.ok_eq]
  simp only [bind_ok, uncurry_apply_pair]
  rw [syscall.finish.guard_resume ar s3 a2 (nd_at hNd F.k F.c) F.h0 F.h1 F.ha F.hsw F.hfr F.hact F.hvc]
  exact fun h => h

/-- **`syscall.handle_ioport_local.guard_acc`: the accepted I/O port local
path on the guarded store ends as the real run** (module docstring). -/
theorem syscall.handle_ioport_local.guard_acc {A : Type} (ar : machine.Arch A) {s s' : S} {a a' : A}
    {number : I64}
    (hNd : ∀ o : U64, o.val < 4288 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hmi : R (regA (L.curW s) layout.reg.MSG_INFO))
    (hfl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (hnx : R (regA (L.curW s) layout.reg.NEXT_IP)) (hfi : W (regA (L.curW s) layout.reg.FAULT_IP))
    (hmid : ∀ info nx s1 s2 a1, msg.msg_info st s (L.curW s) = ok info →
      obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) →
      ∃ C sl, IoMid (L := L) R W s s2 (L.curW s) info (L.mem s2 (regA (L.curW s) layout.reg.CAP)) C sl)
    (hfin : ∀ s2 a1 r s3 a2, syscall.handle_invocation st ar s2 a1 (decide (number = fl4_abi.syscall.SysCall))
      true (decide (number = fl4_abi.syscall.SysCall)) false (L.mem s2 (regA (L.curW s) layout.reg.CAP)) =
        ok (r, s3, a2) → FinOK (L := L) R W ar s s3 a2)
    (h : syscall.handle_ioport_local st ar s a number = ok (true, s', a')) :
    syscall.handle_ioport_local (PathObl.guard st R W) ar s a number = ok (true, s', a') := by
  rw [handle_ioport_local_eq] at h ⊢
  revert h
  rw [sched.cur_thread.guard s (hNd _ (by simp [layout.node.CUR_THREAD])).1, cur_thread_ok]
  simp only [bind_ok]
  rw [msg.msg_info.guard s _ hmi]
  refine tr_bind_same (fun info emi => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.flags.guard _ s hfl]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  have hT := fun (h : ioTail st ar s a (L.curW s) info number = ok (true, s', a')) =>
    ioTail.guard ar hNd hnx hfi (fun nx s1 s2 a1 e1 e2 e3 => hmid info nx s1 s2 a1 emi e1 e2 e3) hfin h
  refine tr_ite (fun _ => tr_ite (fun _ h => h) (fun _ => hT)) (fun _ => hT)

end

end Fl4Proofs.P2.PathObl
