/-
# P2 (line slhuf, gen 12): the Copy / Mint decode block with its IPC buffer, and `inv_pathsKCM3`

`InvBlkUW2` (stpost gen 14, P2/InvDelU.lean) quantifies the decode's IPC buffer `buf` freely; Copy / Mint read
`buf + 40` / `buf + 48` (`copied_cap`), which are user words only for the buffer the run looked up. So the chain is
copied with the run's `msg.lookup_ipc_buffer st s2 false t = ok buf` as an extra hypothesis of the decode block:
`invTail.guard3`, `syscall.handle_invocation_local.guard_acc3`, `inv_acc_gen3` (InvBlk's `…2` with `hb`),
`InvBlkUW3` / `InvBlkGdUW3` (InvDelU's `InvBlkUW2` / `InvBlkGdUW2` with `hb`), `invUAccW_of3`, `invMoveW_ofU3`.
-/
import Fl4Proofs.P2.InvDelU
import Fl4Proofs.P2.InvCM
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section g3
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

set_option maxHeartbeats 1000000 in
/-- **The accepted frame-cap invocation tail on the guarded store** (`hblk`: the decode block). -/
theorem invTail.guard3 {A : Type} (ar : machine.Arch A) {s s' : S} {a a' : A} {t : U64}
    {info : msginfo.MessageInfo} {p : localinv.Plan}
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hnx : R (regA t layout.reg.NEXT_IP)) (hfi : W (regA t layout.reg.FAULT_IP))
    (hmid : ∀ nx s1 s2 a1, obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) → InvMid (L := L) R s s2 t)
    (hsh : ∀ x, localinv.Plan.still_holds gS p x = localinv.Plan.still_holds st p x)
    (hps : R p.slot ∧ R (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : ∀ nx s1 s2 a1 buf length cap, InvChk st ar s a t p nx s1 s2 a1 →
      msg.lookup_ipc_buffer st s2 false t = ok buf →
      (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
        obj.Slot.cap st p.slot s2 = ok cap →
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
  refine tr_bind_same (fun buf ebuf => ?_)
  refine tr_bind_same (fun length elen => ?_)
  rw [obj.Slot.cap.guard (gS := gS) p.slot s2 hps.1 hps.2]
  refine tr_bind_same (fun cap ecap => ?_)
  refine tr_bind (fun y ey _ => (hblk nx s1 s2 a1 buf length cap C ebuf elen ecap y ey).1) (fun y ey => ?_)
  have B := (hblk nx s1 s2 a1 buf length cap C ebuf elen ecap y ey).2
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
theorem syscall.handle_invocation_local.guard_acc3 {A : Type} (ar : machine.Arch A) {s s' : S} {a a' : A}
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
      msg.lookup_ipc_buffer st s2 false (L.curW s) = ok buf →
      (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
        obj.Slot.cap st p.slot s2 = ok cap →
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
  exact tr_ite (fun _ h => h) (fun _ ht => invTail.guard3 ar hNd hnx hfi
    (fun nx s1 s2 a1 e1 e2 e3 => hmid info nx s1 s2 a1 emi e1 e2 e3) hsh hps
    (fun nx s1 s2 a1 buf length cap hc hb hl hk => hblk info nx s1 s2 a1 buf length cap emi hc hb hl hk) ht)


end g3

section acc3
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- **The accepted run on a guarded store `gS` reading `IoRS s` as `st` and writing a set `W` the prefix's words lie
in (`IoWr`)**, from the entry facts, [J] `hSeen`, [J] `hps` and the decode block `hblk` on `gS`. -/
theorem inv_acc_gen3 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {s s' : S} {a a' : A} {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K Locks s)]
    [GWr gS st W] (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hW : IoWr st W Z s)
    (hSeen : ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : IoRS (st := st) K Locks s p.slot ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : ∀ info nx s1 s2 a1 buf length cap, msg.msg_info st s (L.curW s) = ok info →
      InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
      msg.lookup_ipc_buffer st s2 false (L.curW s) = ok buf →
      (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
        obj.Slot.cap st p.slot s2 = ok cap →
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
  refine syscall.handle_invocation_local.guard_acc3 (gS := gS) ar (P.ent (Locks := Locks) hW).acc.nd
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



/-- [W] (slhuf gen 12) **`InvBlkUW2` with the run's IPC buffer** (`msg.lookup_ipc_buffer st s2 false (curW s) = ok buf`). -/
def InvBlkUW3 (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (p : localinv.Plan)
    (K : KLayout) (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap, P s → msg.msg_info st s (L.curW s) = ok info →
    InvChk st ar s a (L.curW s) p nx s1 s2 a1 → msg.lookup_ipc_buffer st s2 false (L.curW s) = ok buf →
    (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
      obj.Slot.cap st p.slot s2 = ok cap →
    ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
      syscall.decode_invocation (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) ar s2 a1
          info.label length p.slot cap true true true false buf p.extra = ok y ∧
      ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
        invRep (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
        z.2.2 = core.result.Result.Ok () ∧
        FinOK (L := L) (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s))
          (IoRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s) ar s z.1 z.2.1

/-- [W] (slhuf gen 12) **`InvBlkGdUW2` with the run's IPC buffer.** -/
def InvBlkGdUW3 (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (p : localinv.Plan)
    (K : KLayout) (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap, P s → msg.msg_info st s (L.curW s) = ok info →
    InvChk st ar s a (L.curW s) p nx s1 s2 a1 → msg.lookup_ipc_buffer st s2 false (L.curW s) = ok buf →
    (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
      obj.Slot.cap st p.slot s2 = ok cap →
    ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
      syscall.decode_invocation (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) ar s2 a1
          info.label length p.slot cap true true true false buf p.extra = ok y ∧
      ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
        invRep (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
        z.2.2 = core.result.Result.Ok () ∧
        FinOK (L := L) (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))
          (IoRS (st := st) K Locks s) (WAll (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) ar s z.1 z.2.1

/-- (slhuf gen 12) **`InvCMAccW` from the decode block with the IPC buffer** (`invUAccW_of2` over `inv_acc_gen3`). -/
theorem invUAccW_of3 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : ∀ s, P s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : InvBlkUW3 st ar p K Locks P) :
    InvCMAccW st ar number p K Locks P := fun s a _ _ hE h => by
  have : GRd (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) st
      (IoRS (st := st) K Locks s) := grd_sub (fun _ hy => ioRS_cm hy)
  exact inv_acc_gen3 (W := InvCMWS (st := st) K Locks s) hA (hPE s hE)
    (((hPE s hE).ioWr (Locks := Locks)).mono (fun _ hy => ioWS_cm hy)) (hSeen s hE) (hps s hE)
    (fun info nx s1 s2 a1 buf length cap emi hc hb hl hk => hblk s a info nx s1 s2 a1 buf length cap hE emi hc hb hl hk) h

/-- (slhuf gen 12) **`InvMoveW` from the decode block on `gd st (InvCMRS s) (PWs …)` with the IPC buffer**
(`invMoveW_ofU` over `inv_acc_gen3`). -/
theorem invMoveW_ofU3 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {m0 : U64 → U64} {P : S → Prop} (hK : ∀ s, P s → RegionOK K) (hU : ∀ s, P s → E2E.UserOK K)
    (hLA : ∀ s, P s → IoLayA K) (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : ∀ s, P s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hmA : ∀ s, P s → ∀ d, K.heap d = some .tcb → m0 (fld d OwnMap.oAFFINITY) = L.mem s (fld d OwnMap.oAFFINITY))
    {q : SProg Bool}
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q)
    (hblk : InvBlkGdUW3 st ar p K Locks P) :
    InvMoveW st ar number p K Locks m0 P := by
  intro s a s1 a1 hE h
  have : GRd (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) st
      (IoRS (st := st) K Locks s) := gdr_sub (fun _ hy => ioRS_cm hy)
  have hg := inv_acc_gen3 (gS := (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))))
    hA (hPE s hE) (mvWrS (hPE s hE) (hK s hE) (hLA s hE)) (hSeen s hE) (hps s hE)
    (fun info nx s1 s2 a1 buf length cap emi hc hb hl hk => hblk s a info nx s1 s2 a1 buf length cap hE emi hc hb hl hk) h
  rw [inv_hp hp (Narrow.gd _ _ _) (AltOf.pre hE) a] at hg
  rw [inv_hp hp (Narrow.mguard _ _) (AltOf.pre hE) a]
  exact OwnMap.run_gds_mguard (hK s hE) (hU s hE) (hmA s hE) q hg

end acc3

/-! ## The sender-side IPC buffer -/

section buf
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- `lookup_ipc_buffer` (either side) reads only the three `IbSame` words (P1's `lookup_ipc_buffer_same`, any side). -/
theorem lookup_ipc_buffer_sameR {s s' : S} {t : U64} (rcv : Bool) (h : IbSame (L := L) s s' t) :
    msg.lookup_ipc_buffer st s' rcv t = msg.lookup_ipc_buffer st s rcv t := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold msg.lookup_ipc_buffer
  rw [ipc_buffer_word, ipc_buffer_word, h1]
  have hs : obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok (sbWordA t) := by simp [obj.Tcb.slot, lift, sbWordA]
  rw [hs]; simp only [bind_ok]
  have hc : obj.Slot.cap st (sbWordA t) s' = obj.Slot.cap st (sbWordA t) s := by
    unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, h2, h3]
  rw [hc]

/-- (slhuf gen 12) **The prefix keeps the current thread's IPC buffer lookup.** -/
theorem lib_prefix {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A} {p : localinv.Plan}
    {nx : U64} {s1 s2 : S} {a1 : A} (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1) (rcv : Bool) :
    msg.lookup_ipc_buffer st s2 rcv (L.curW s) = msg.lookup_ipc_buffer st s rcv (L.curW s) := by
  have w := prefix_writes ar hA P.tp P.np P.cT C.2.1 C.2.2.1
  apply lookup_ipc_buffer_sameR
  refine ⟨?_, ?_, ?_⟩
  · exact w.2.2 _ (field_aligned P.tA (by simp) (by simp))
      (preW_tcb P.tA P.np P.cT (K := 3512#u64) (by simp) (by simp))
  · rw [sbWordA_eq]
    exact w.2.2 _ (field_aligned P.tA (by simp) (by simp))
      (preW_tcb P.tA P.np P.cT (K := 64#u64) (by simp) (by simp))
  · rw [sbWordA8_eq]
    exact w.2.2 _ (field_aligned P.tA (by simp) (by simp))
      (preW_tcb P.tA P.np P.cT (K := 72#u64) (by simp) (by simp))

variable (st) in
/-- [J] (slhuf gen 12) **The caller's send-side IPC buffer words are aligned user words** (`InvBufJ` for the
sender-side lookup `msg.lookup_ipc_buffer st s false`, the buffer `decode_invocation` reads arguments 4 / 5 from). -/
def InvBufSJ (K : KLayout) (s : S) : Prop :=
  ∀ b, msg.lookup_ipc_buffer st s false (L.curW s) = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 512 →
    UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64))

variable (st) in
/-- [J] (slhuf gen 12) **A capability slot whose first word decodes to `Null` holds a Null / Frame encoding**
(slot words are cap encodings: `Cap.decode` also maps the unused tags to `Null`). -/
def InvNulJ (K : KLayout) (s : S) : Prop :=
  ∀ q, q ∈ K.slots → ∀ c, capability.Cap.decode (L.mem s (core.num.U64.wrapping_add q layout.cte.CAP0)) 0#u64 = ok c →
    capability.Cap.is_null c = ok true → NullOrFrame (L.mem s q)

end buf

end Fl4Proofs.P2.PathObl
