/-
# P2 (line stpost, generation 12): `acc` of the frame-cap invocation path, reduced to the decode block

`InvAccW` (an accepted `handle_invocation_local` run on the store guarded to `IoRS s` / `IoWS s` ends as the real
one) with everything but the decode proved: the entry reads (`cur_thread`, `msg_info`, flags), the prefix
(`FAULT_IP`, `update_timestamp`), the checks (`action`, `yield_to`, `sufficient`, `schedulable_here`) on the words
the I/O port's `io_hmid'` gives, `still_holds` (`still_holds_guard`, its words in `IoRS` by `hSeen`), the IPC
buffer lookup, the invoked slot's cap, and after the decode `after_invocation` (`Ok`) and `finish`
(`finish.guard_resume`, from `FinOK`). What is left is the decode block itself, stated as `InvBlkW`.

* `InvChk`: the accepted run's prefix and checks at the post-prefix state;
* `InvMid`: the words the checks and the buffer lookup read (a subset of `IoMid`);
* `invTail.guard`, `syscall.handle_invocation_local.guard_acc`: the accepted run on any guarded store `gS`,
  given `InvMid`, `still_holds` alike on `gS`, the invoked slot readable, and the decode block (`hblk`);
* `InvBlkW` [W]: on `guard st (IoRS s) (IoWS s)` the decode (`decode_invocation` on the plan's slot) and the reply
  (`invRep`) run as on `st`, the reply's result is `Ok ()`, and `FinOK` holds after it;
* `inv_acc_gen`: the accepted run on any `gS` reading `IoRS s` as `st` and writing a set `W ⊇` the prefix words;
* **`invAccW_of`**: `InvAccW` from `hA`, `hPE` (`IoPre`), [J] `hSeen`, [J] `hps` (the invoked slot's cap words are
  in `IoRS`) and [W] `hblk : InvBlkW`;
* `InvBlkGdW` [W] (the decode block on p2sl's checked store `gd st (IoRS s) (PW …)`) and **`invMoveW_of`**:
  `InvMoveW` by the I/O port's `io_move` route (`OwnMap.run_gd_mguard`), from [J] `hK`/`hU`/`hLA`/`hmA`, `hPE`,
  `hSeen`, `hps`, [P] `hp` (`IsProgOn`, the tree of `hpz`) and [W] `hblk : InvBlkGdW`;
* **`inv_pathsKA`**: `inv_pathsKD` with `hacc` / `hmv` from `invAccW_of` / `invMoveW_of` (StartAt: `inv_pathsK_startAt`'s
  pattern, `⟨σ, a, ⟨h7 …, hq⟩, hc, hl, hμ, rfl⟩`).

No existing statement changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvDec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField)

section g
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

variable (st) in
/-- The accepted run's prefix and checks (entry `s`, current thread `t`, post-prefix state `s2`). -/
def InvChk {A : Type} (ar : machine.Arch A) (s : S) (a : A) (t : U64) (p : localinv.Plan) (nx : U64) (s1 s2 : S)
    (a1 : A) : Prop :=
  obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx ∧
    obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 ∧
    sched.update_timestamp st ar s1 a = ok (s2, a1) ∧
    sched.action st s2 = ok sched.ACTION_RESUME_CURRENT ∧ obj.Tcb.yield_to st t s2 = ok 0#u64 ∧
    fastpath.schedulable_here st s2 t = ok true ∧ localinv.Plan.still_holds st p s2 = ok true

/-- The words the checks and the IPC buffer lookup read at the post-prefix state `s2`. -/
structure InvMid (R : U64 → Prop) (s s2 : S) (t : U64) : Prop where
  k : L.ksb s2 = L.ksb s
  c : L.cpu s2 = L.cpu s
  cur : L.curW s2 = t
  yld : R (core.num.U64.wrapping_add t 3472#u64)
  rh : RdHead (L := L) R s2 (L.cscW s2)
  td : L.mem s2 (tmA (L := L) s2) ≠ 0#u64 →
    R (core.num.U64.wrapping_add (L.mem s2 (tmA (L := L) s2)) 3528#u64)
  rs : L.mem s2 (rhA (L := L) s2) ≠ 0#u64 → R (scA (L.mem s2 (rhA (L := L) s2))) ∧
    RdHead (L := L) R s2 (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))
  dt : R (core.num.U64.wrapping_add (L.ksb s2) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb s2) layout.ks.CUR_DOMAIN)
  af : R (affA t)
  dom : R (core.num.U64.wrapping_add t 3432#u64)
  sc : R (scA t)
  inq : R (inqA t)
  ib : R (core.num.U64.wrapping_add t 3512#u64)
  bs : ∀ bsl, obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok bsl → R bsl ∧ R (core.num.U64.wrapping_add bsl 8#u64)

set_option maxHeartbeats 1000000 in
/-- **The accepted frame-cap invocation tail on the guarded store** (`hblk`: the decode block). -/
theorem invTail.guard {A : Type} (ar : machine.Arch A) {s s' : S} {a a' : A} {t : U64}
    {info : msginfo.MessageInfo} {p : localinv.Plan}
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hnx : R (regA t layout.reg.NEXT_IP)) (hfi : W (regA t layout.reg.FAULT_IP))
    (hmid : ∀ nx s1 s2 a1, obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) → InvMid (L := L) R s s2 t)
    (hsh : ∀ x, localinv.Plan.still_holds gS p x = localinv.Plan.still_holds st p x)
    (hps : R p.slot ∧ R (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : ∀ nx s1 s2 a1 buf length cap, InvChk st ar s a t p nx s1 s2 a1 →
      ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
        syscall.decode_invocation gS ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
        ∀ z, invRep st t y.2.1 y.2.2 y.1 = ok z →
          invRep gS t y.2.1 y.2.2 y.1 = ok z ∧ z.2.2 = core.result.Result.Ok () ∧
          FinOK (L := L) gS R W ar s z.1 z.2.1)
    (h : invTail st ar s a t info p = ok (true, s', a')) :
    invTail gS ar s a t info p = ok (true, s', a') := by
  unfold invTail at h ⊢
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
      rw [sched.update_timestamp.guard ar s1 a (nd_at hNd k1 c1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
        (nd_at hNd k1 c1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2
        (nd_at hNd k1 c1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
        (nd_at hNd k1 c1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2]; exact hx)
    (fun x eu => ?_)
  obtain ⟨s2, a1⟩ := x
  simp only [uncurry_apply_pair]
  have M := hmid nx s1 s2 a1 enx es1 eu
  have nd2 := nd_at hNd M.k M.c
  have Mc := M.cur
  subst Mc
  rw [sched.cur_sc.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1]
  refine tr_bind_same (fun csc ecsc => ?_)
  rw [sched.action.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1]
  refine tr_bind_same (fun i3 ei3 => ?_)
  beta_reduce
  refine tr_ite (fun _ h => h) (fun hi3 => ?_)
  rw [obj.Tcb.yield_to.guard (gS := gS) (L.curW s2) s2 M.yld]
  refine tr_bind_same (fun i4 ei4 => ?_)
  beta_reduce
  refine tr_ite (fun _ h => h) (fun hi4 => ?_)
  rw [sched.consumed.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1]
  refine tr_bind_same (fun i5 _ => ?_)
  have ecsc' : csc = L.cscW s2 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s2)] at ecsc; exact (ok_inj_ff ecsc).symm
  subst ecsc'
  rw [sporadic.sufficient.guard (gS := gS) ar s2 a1 _ i5 M.rh]
  refine tr_bind_same (fun b1 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [fastpath.schedulable_here.guard (gS := gS) s2 (L.curW s2) (nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
    (nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1 (nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])).1
    M.td M.rs M.dt M.cd M.af M.dom M.sc M.inq]
  refine tr_bind_same (fun b2 eb2 => ?_)
  beta_reduce
  refine tr_ite (fun hb2 => ?_) (fun _ h => h)
  rw [hsh s2]
  refine tr_bind_same (fun b3 eb3 => ?_)
  beta_reduce
  refine tr_ite (fun hb3 => ?_) (fun _ h => h)
  have C : InvChk st ar s a (L.curW s2) p nx s1 s2 a1 := by
    simp only [bne_iff_ne, ne_eq, not_not] at hi3 hi4
    subst hi3 hi4 hb2 hb3
    exact ⟨enx, es1, eu, ei3, ei4, eb2, eb3⟩
  obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s2)
  rw [msg.lookup_ipc_buffer.guard (gS := gS) s2 false (L.curW s2) hbsl M.ib (M.bs _ hbsl).1 (M.bs _ hbsl).2]
  refine tr_bind_same (fun buf _ => ?_)
  refine tr_bind_same (fun length _ => ?_)
  rw [obj.Slot.cap.guard (gS := gS) p.slot s2 hps.1 hps.2]
  refine tr_bind_same (fun cap _ => ?_)
  refine tr_bind (fun y ey _ => (hblk nx s1 s2 a1 buf length cap C y ey).1) (fun y ey => ?_)
  have B := (hblk nx s1 s2 a1 buf length cap C y ey).2
  obtain ⟨r, s3, a2⟩ := y
  simp only [uncurry_apply_pair]
  refine tr_bind (fun z ez _ => (B z ez).1) (fun z ez => ?_)
  obtain ⟨-, hr1, F⟩ := B z ez
  obtain ⟨s4, a3, r1⟩ := z
  dsimp only at hr1 F
  subst hr1
  simp only [uncurry_apply_pair]
  rw [syscall.after_invocation.ok_eq, syscall.after_invocation.ok_eq]
  simp only [bind_ok, uncurry_apply_pair]
  rw [syscall.finish.guard_resume ar s4 a3 (nd_at hNd F.k F.c) F.nd F.td F.rs F.ha F.hsw F.hfr F.hact F.hvc]
  exact fun h => h

/-- **The accepted frame-cap invocation local path on the guarded store ends as the real run.** -/
theorem syscall.handle_invocation_local.guard_acc {A : Type} (ar : machine.Arch A) {s s' : S} {a a' : A}
    {number : I64} {p : localinv.Plan}
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hmi : R (regA (L.curW s) layout.reg.MSG_INFO))
    (hfl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (hnx : R (regA (L.curW s) layout.reg.NEXT_IP)) (hfi : W (regA (L.curW s) layout.reg.FAULT_IP))
    (hmid : ∀ info nx s1 s2 a1, msg.msg_info st s (L.curW s) = ok info →
      obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) → InvMid (L := L) R s s2 (L.curW s))
    (hsh : ∀ x, localinv.Plan.still_holds gS p x = localinv.Plan.still_holds st p x)
    (hps : R p.slot ∧ R (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : ∀ info nx s1 s2 a1 buf length cap, msg.msg_info st s (L.curW s) = ok info →
      InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
      ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
        syscall.decode_invocation gS ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
        ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
          invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧ z.2.2 = core.result.Result.Ok () ∧
          FinOK (L := L) gS R W ar s z.1 z.2.1)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local gS ar s a number p = ok (true, s', a') := by
  rw [handle_invocation_local_eq] at h ⊢
  revert h
  rw [sched.cur_thread.guard (gS := gS) s (hNd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1, cur_thread_ok]
  simp only [bind_ok]
  rw [msg.msg_info.guard (gS := gS) s _ hmi]
  refine tr_bind_same (fun info emi => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.flags.guard (gS := gS) _ s hfl]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  exact tr_ite (fun _ h => h) (fun _ ht => invTail.guard ar hNd hnx hfi
    (fun nx s1 s2 a1 e1 e2 e3 => hmid info nx s1 s2 a1 emi e1 e2 e3) hsh hps
    (fun nx s1 s2 a1 buf length cap hc => hblk info nx s1 s2 a1 buf length cap emi hc) ht)

end g

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- [W] **The decode block of an accepted frame-cap invocation run on the guarded store** (entry `s` at `Pre`): at
a post-prefix state passing the checks (`InvChk`), `decode_invocation` on the plan's slot runs on
`guard st (IoRS s) (IoWS s)` as on `st`, and so does the reply `invRep`, whose result is `Ok ()`; after it the
finish's facts (`FinOK`) hold. For the Delete arm this is `cnode.decode` → `lookup_target_slot` →
`cdt.delete` → `finalise_slot_immediate` (a small RAM frame, unmapped: remainder `Null`) → `empty_slot`. -/
def InvBlkW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (p : localinv.Plan)
    (K : KLayout) (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap, P s → msg.msg_info st s (L.curW s) = ok info →
    InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
    ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
      syscall.decode_invocation (guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) ar s2 a1
          info.label length p.slot cap true true true false buf p.extra = ok y ∧
      ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
        invRep (guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
        z.2.2 = core.result.Result.Ok () ∧
        FinOK (L := L) (guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s))
          (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s) ar s z.1 z.2.1

/-- **The accepted run on a guarded store `gS` reading `IoRS s` as `st` and writing a set `W` the prefix's words lie
in (`IoWr`)**, from the entry facts, [J] `hSeen`, [J] `hps` and the decode block `hblk` on `gS`. -/
theorem inv_acc_gen {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {s s' : S} {a a' : A} {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K Locks s)]
    [GWr gS st W] (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hW : IoWr st W Z s)
    (hSeen : ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : IoRS (st := st) K Locks s p.slot ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : ∀ info nx s1 s2 a1 buf length cap, msg.msg_info st s (L.curW s) = ok info →
      InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
      ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
        syscall.decode_invocation gS ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
        ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
          invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧ z.2.2 = core.result.Result.Ok () ∧
          FinOK (L := L) gS (IoRS (st := st) K Locks s) W ar s z.1 z.2.1)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local gS ar s a number p = ok (true, s', a') := by
  obtain ⟨info, -, -, -, ht⟩ := handle_inv_inv h
  obtain ⟨nx0, s10, s20, a10, -, -, es10, eu0, -, -, -, hh0, -⟩ := invTail_inv ht
  have hsc2 := (here_facts hh0).sc
  have w := prefix_writes ar hA P.tp P.np P.cT es10 eu0
  have e1 : L.mem s20 (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    w.2.2 _ (field_aligned P.tA (by simp) (by simp)) (preW_tcb P.tA P.np P.cT (K := 3464#u64) (by simp) (by simp))
  have hsc0 : L.mem s (scA (L.curW s)) = L.cscW s := (P.hcsc (by rw [← e1]; exact hsc2)).symm
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨⟨Q, Rq, hq⟩, hbd, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  refine syscall.handle_invocation_local.guard_acc (gS := gS) ar (P.ent (Locks := Locks) hW).acc.nd
    (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1
    (P.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
    (P.reg (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1 (hW.reg _ (by simp [layout.reg.FAULT_IP]))
    ?_ (fun x => still_holds_congr p x (fun w hw => GRd.read (hSeen w hw) x)) hps hblk h
  intro info nx s1 s2 a1 emi enx es1 eu
  have M2 := io_hmid' (a := a) ar hA hq.tcbs (hq.nodes _ hq.cur) hq.cur hq.curT
    (P.mid (Locks := Locks) (P.ioWr (Locks := Locks)) hroot hcl (fun p r m y hp hm => (hC p r m y hp hm).1) hsc0)
    (fun p r m y hp hm => (hC p r m y hp hm).2) (fun x hx => (P.fin x hx).2) (hd hX.cur)
    (fun h0 => ⟨(bxi_rh P.bxi h0).1, hd (bxi_rh P.bxi h0).2.1⟩) info nx _ s2 a1 emi enx es1 eu
  exact ⟨M2.k, M2.c, M2.cur, M2.yld, M2.rh, M2.td, M2.rs, M2.dt, M2.cd, M2.af, M2.dom, M2.iok.1.sc, M2.iok.1.inq,
    M2.iok.1.ib, M2.iok.1.bs⟩

/-- (stpost gen 12) **`InvAccW` from the decode block**: `hA`, and at each `Pre` state `hPE` (`IoPre`), [J] `hSeen`
(the seen words in `IoRS`), [J] `hps` (the invoked slot's cap words in `IoRS`), and [W] `hblk : InvBlkW`. -/
theorem invAccW_of {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : ∀ s, P s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : InvBlkW st ar p K Locks P) :
    InvAccW st ar number p K Locks P := fun s a _ _ hE h =>
  inv_acc_gen hA (hPE s hE) ((hPE s hE).ioWr (Locks := Locks)) (hSeen s hE) (hps s hE)
    (fun info nx s1 s2 a1 buf length cap emi hc => hblk s a info nx s1 s2 a1 buf length cap hE emi hc) h

/-- [W] **The decode block on p2sl's checked store** `gd st (IoRS s) (PW …)` (as `InvBlkW`, with the checked store
and its write set `WAll PW`): what `move` of accepted runs needs besides the program tree. -/
def InvBlkGdW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (p : localinv.Plan)
    (K : KLayout) (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap, P s → msg.msg_info st s (L.curW s) = ok info →
    InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
    ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
      syscall.decode_invocation (gd st (IoRS (st := st) K Locks s) (OwnMap.PW (L := L) K (L.cpu s) (Locks s) (L.mem s)))
          ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
      ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
        invRep (gd st (IoRS (st := st) K Locks s) (OwnMap.PW (L := L) K (L.cpu s) (Locks s) (L.mem s)))
          (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
        z.2.2 = core.result.Result.Ok () ∧
        FinOK (L := L) (gd st (IoRS (st := st) K Locks s) (OwnMap.PW (L := L) K (L.cpu s) (Locks s) (L.mem s)))
          (IoRS (st := st) K Locks s) (WAll (OwnMap.PW (L := L) K (L.cpu s) (Locks s) (L.mem s))) ar s z.1 z.2.1

/-- (stpost gen 12) **`InvMoveW` from the decode block on the checked store** (I/O port's `io_move` route:
the accepted run on `gd`, then `OwnMap.run_gd_mguard` over the program tree `q`): `hA`; at each `Pre` state
[J] `hK` (`RegionOK`), [J] `hU` (`UserOK`), [J] `hLA` (`IoLayA`), `hPE`, [J] `hSeen`, [J] `hps`, [J] `hmA` (`m0`
agrees with the state on every TCB's `AFFINITY`); [P] `hp` (`IsProgOn` of the body, the `hpz` tree); [W] `hblk`. -/
theorem invMoveW_of {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {m0 : U64 → U64} {P : S → Prop} (hK : ∀ s, P s → RegionOK K) (hU : ∀ s, P s → E2E.UserOK K)
    (hLA : ∀ s, P s → IoLayA K) (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : ∀ s, P s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hmA : ∀ s, P s → ∀ d, K.heap d = some .tcb → m0 (fld d OwnMap.oAFFINITY) = L.mem s (fld d OwnMap.oAFFINITY))
    {q : SProg Bool}
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q)
    (hblk : InvBlkGdW st ar p K Locks P) :
    InvMoveW st ar number p K Locks m0 P := by
  intro s a s1 a1 hE h
  have hg := inv_acc_gen (gS := gd st (IoRS (st := st) K Locks s) (OwnMap.PW (L := L) K (L.cpu s) (Locks s) (L.mem s)))
    hA (hPE s hE) ((hPE s hE).mvWr (hK s hE) (hLA s hE)) (hSeen s hE) (hps s hE)
    (fun info nx s1 s2 a1 buf length cap emi hc => hblk s a info nx s1 s2 a1 buf length cap hE emi hc) h
  rw [inv_hp hp (Narrow.gd _ _ _) (AltOf.pre hE) a] at hg
  rw [inv_hp hp (Narrow.mguard _ _) (AltOf.pre hE) a]
  exact OwnMap.run_gd_mguard (hK s hE) (hU s hE) (hmA s hE) q hg

end acc

/-! ## The path with `acc`, `dec_alt`, `move`, `read_aligned` reduced to the decode block -/

section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- (stpost gen 12) **The frame-cap invocation path with `acc` / `move` reduced to the decode block**:
`inv_pathsKD` with `hacc := invAccW_of`, `hmv := invMoveW_of` (the tree of `hpz`). Premises: `hA`, `hm` [P], `Q`,
`hPE`, [J] `hSeen : InvSeenRS`, [J] `hps` (the invoked slot's cap words in `IoRS`), [J] `hmA` (`m` agrees with the
state on every TCB's `AFFINITY`), [W] `hblk` (`InvBlkW`), [W] `hblkG` (`InvBlkGdW`), [J] `huf`, `hpz`
([P] IsProgOn ∧ [W] NoZero ∧ [W] InvRoW, unchanged shape). -/
noncomputable def inv_pathsKA (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hSeen : InvSeenRS st Locks p Q)
    (hps : ∀ K m s, SlJAt (L := L) K s → Q K m s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hmA : ∀ K m s, SlJAt (L := L) K s → Q K m s → ∀ d, K.heap d = some .tcb →
      m (fld d OwnMap.oAFFINITY) = L.mem s (fld d OwnMap.oAFFINITY))
    (hblk : ∀ K m, InvBlkW st ar p K Locks (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (hblkG : ∀ K m, InvBlkGdW st ar p K Locks (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∀ K m, ∃ q : SProg Bool, IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (fun s => SlJAt (L := L) K s ∧ Q K m s) (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m)
        (· ∈ K.user)) q ∧ NoZero q ∧
      InvRoW st ar number p K Locks m q (fun s => SlJAt (L := L) K s ∧ Q K m s)) :
    E2E.Paths Unit :=
  inv_pathsKD ar hA number p hm Q hPE
    (fun K m => invAccW_of hA (fun s h => hPE K m s h.1 h.2) (fun s h => hSeen K m s h.1 h.2)
      (fun s h => hps K m s h.1 h.2) (hblk K m))
    hSeen
    (fun K m => invMoveW_of hA (fun _ h => h.1.regionOK) (fun _ h => h.1.userOK) (fun _ h => h.1.ioLayA)
      (fun s h => hPE K m s h.1 h.2) (fun s h => hSeen K m s h.1 h.2) (fun s h => hps K m s h.1 h.2)
      (fun s h => hmA K m s h.1 h.2) (hpz K m).choose_spec.1 (hblkG K m))
    huf hpz

end paths

end Fl4Proofs.P2.PathObl
