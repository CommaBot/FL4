/-
P3 (line stpost, generation 4): **the ReplyRecv receive at stable ghosts, proved** (StPostMid's
`JMidRecvHypSt` [W] replaced by FL4 facts at the mid state).

On the accepted ReplyRecv fast path the general path's receive (`handle_recv` at the state `X8`
after the reply, P1 FastRRSync's `handle_recv_rr`) finds the receive Endpoint cap and the Reply
cap again, the reply object free (`reply_remove` cleared it), the endpoint idle and no active bound
notification lending the thread its SC, and the scheduler action is the switch to the replied-to
thread (`possible_switch_to u` from RESUME_CURRENT). `RRMidSt` names exactly these words of the
mid state (P1's `RRReads` fields `ct8`, `act8`/`act15`, `lk8`, `rt8`, `ntfn8`, `ep8`, in P3's
vocabulary; the notification's SC word in the form XTopJointRecvIpcBound's
`receive_ipc_blockN_red` reads).

* `JStabR.mv`; `handle_recv_rrSt`: `handle_recv … true true` at a mid state with `JAtZ` at
  `Z`, `MidE` with a pending switch, the current thread in no ready queue and `RRMidSt`, ends at
  `RelTopM ∧ JStabR Z H Cs` (StPostRecvBlk's `recvIpcBlockJGMSt` without a bound notification,
  `recvIpcBlockNJGMSt` with an idle or waiting one whose SC is not the thread's; the two lookups
  against the spec's `lookupCap` / `lookupReply` as IpcRecvTopH's `handle_recv_refinesH`, its
  other branches unreachable). No premise.
* `mid_invRecvReplyJStF`, `dispatch_replyRecvJStF`: StPostMid's `mid_invRecvReplyJSt` /
  `dispatch_replyRecvJSt` without `hRS : JMidRecvHypSt` [W]: the run of `handle_invocation` named
  (`hMid`: it ends at `X8` with `RRMidSt`, which P1's `handle_invocation_rr` / `rr_x8G` give on an
  accepted run), `hP : JMidPerfHypQ` [W] (KEntry10M's form of StPostMid's `hW`) for the ready
  queues and the action at the mid state, `hnq0` (JEntryAt's `ctnq`). l4v: `receive_ipc_corres`
  inside `handle_recv_corres`, blocking on an idle endpoint.
-/
import Fl4Proofs.P3.StPostRecvBlk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section StRecvA
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- (stpost) **The FL4 words of the ReplyRecv mid state** (module docstring): the current
thread `t`, the action word neither RESUME_CURRENT nor CHOOSE_NEW (a switch), the CAP register's
receive Endpoint cap on `ep` and the REPLY register's Reply cap on `rptr`, the reply object free,
the endpoint idle, and the bound notification absent or not active and not lending `t` its SC. -/
structure RRMidSt (s : S) (t rptr ep : U64) : Prop where
  ct : sched.cur_thread st s = ok t
  act0 : L.actionW s ≠ 0#u64
  act1 : L.actionW s ≠ 1#u64
  lk : ∃ (b0 : U64) (b1 b3 b4 g : Bool),
    cspace.lookup_cap st s t (L.mem s (regA t layout.reg.CAP)) =
      ok (.Ok (.Endpoint ep b0 b1 true b3 b4)) ∧
    cspace.lookup_cap st s t (L.mem s (regA t layout.reg.REPLY)) = ok (.Ok (.Reply rptr g))
  rt : L.mem s (rTcbA rptr) = 0#u64
  ep : stOf (L.mem s) ep = 0#u64
  ntfn : L.mem s (tBoundA t) = 0#u64 ∨ (stOf (L.mem s) (L.mem s (tBoundA t)) ≠ obj.NTFN_ACTIVE ∧
    (L.mem s (nScA (L.mem s (tBoundA t))) = 0#u64 ∨
      L.mem s (nScA (L.mem s (tBoundA t))) ≠ L.mem s (P1.scA t)))

end StRecvA

section StRecvB
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64}
  {MR : A → Fl4Spec.MachineState → Prop}

theorem JStabR.mv {G : MdbGhost} {V : XVs} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JStabR (L := L) arI AR (Z.mv G V) H Cs s a σ) : JStabR (L := L) arI AR Z H Cs s a σ := by
  obtain ⟨G', V', Ac', Lst', D', J'⟩ := h
  exact ⟨G', V', Ac', Lst', D', J'⟩

set_option maxHeartbeats 16000000 in
/-- (stpost) **The ReplyRecv receive at stable ghosts** (module docstring). -/
theorem handle_recv_rrJSt {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (hni : MidE σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {t rptr ep : U64} (hM : RRMidSt (st := st) s t rptr ep) :
    syscall.handle_recv st arI s a true true ⦃ r => ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) true true σ).1,
      RelTopM (L := L) r.1 z.2 ∧ JStabR (L := L) arI AR Z H Cs r.1 r.2 z.2 ⦄ := by
  obtain ⟨b0, b1, b3, b4, g, hlc, hlr⟩ := hM.lk
  have hct := hM.ct
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨htcb, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : t ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  have hxs := hI.1.toE.at_tcb hctT hks
  have hR := J.xtop.rel.2.1.1
  have hV := J.xtop.rel.2.1.2.1
  have hk' : σ.kheap σ.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hcapr : (L.mem s (regA t layout.reg.CAP)).bv = xs.tcbArch.tcbContext.userRegs Fl4Spec.cap_register := by
    rw [← regIdx_cap]; exact hxs.regs _
  have hrepr : (L.mem s (regA t layout.reg.REPLY)).bv = xs.tcbArch.tcbContext.userRegs Fl4Spec.replyRegister := by
    rw [← regIdx_reply]; exact hxs.regs _
  have hcp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs Fl4Spec.cap_register) =
      Fl4Spec.toBl (L.mem s (regA t layout.reg.CAP)).bv := by rw [← hcapr]; rfl
  have hrp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs Fl4Spec.replyRegister) =
      Fl4Spec.toBl (L.mem s (regA t layout.reg.REPLY)).bv := by rw [← hrepr]; rfl
  -- the spec's two lookups
  have hLc := lookup_cap_refines Z.th s σ hR hV t htcb (L.mem s (regA t layout.reg.CAP))
  rw [hlc, WP.spec_ok] at hLc
  obtain ⟨e, he, hrel⟩ := hLc
  cases e with
  | error _ => exact hrel.elim
  | ok ac =>
  have hcr0 : CapRel (.Endpoint ep b0 b1 true b3 b4) ac := hrel
  have hac := hcr0.abs
  subst hac
  have hLr := lookup_cap_refines Z.th s σ hR hV t htcb (L.mem s (regA t layout.reg.REPLY))
  rw [hlr, WP.spec_ok] at hLr
  obtain ⟨e1, he1, hrel1⟩ := hLr
  cases e1 with
  | error _ => exact hrel1.elim
  | ok ac1 =>
  have hcr1 : CapRel (.Reply rptr g) ac1 := hrel1
  have hac1 := hcr1.abs
  subst hac1
  have he1' : (Fl4Spec.lookupCap (Z := Unit) σ.curThread
      (Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs Fl4Spec.replyRegister))).run σ =
      ({(.ok (absCap (.Reply rptr g)), σ)}, False) := by
    rw [hrp, hcur]; exact he1
  have hcf := mem_capFault_ok (c := Fl4Spec.ofBl (Fl4Spec.toBl (L.mem s (regA t layout.reg.CAP)).bv)) (rp := true) he
  -- the caps held, their objects
  have hHc := lookup_cap_held Z.th s σ hR hV t htcb (L.mem s (regA t layout.reg.CAP))
  rw [hlc, WP.spec_ok] at hHc
  have hHd : JHeld (L := L) Z.th s (.Endpoint ep b0 b1 true b3 b4) := hHc _ rfl
  have hHr0 := lookup_cap_held Z.th s σ hR hV t htcb (L.mem s (regA t layout.reg.REPLY))
  rw [hlr, WP.spec_ok] at hHr0
  have hHrr : JHeld (L := L) Z.th s (.Reply rptr g) := hHr0 _ rfl
  have hHr : ∀ q g', (capability.Cap.Reply rptr g) = .Reply q g' → JHeld (L := L) Z.th s (.Reply rptr g) :=
    fun _ _ _ => hHrr
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have heE : ep ∈ Z.E := by
    obtain ⟨y, hy, hcv⟩ := hHd
    exact J.hset.1 ep ((hJ.typed _ hy).1 ep b0 b1 true b3 b4 hcv)
  obtain ⟨xe, hke, -⟩ := hI.1.ep ep heE
  have hrR : rptr ∈ Z.R := by
    obtain ⟨y, hy, hcv⟩ := hHrr
    exact J.hset.2.2 rptr ((hJ.typed _ hy).2.2 rptr g hcv)
  obtain ⟨xr, hkr, -⟩ := hI.1.reply rptr hrR
  have hx := hI.1.toE.at_ep heE hke
  have hns : ∀ q, xe ≠ .sendEP q := by
    intro q hq
    subst hq
    have h1 := hx.1
    rw [hM.ep] at h1
    exact absurd h1 (by decide)
  have hcB : Endp.CanBlock true xe := by
    cases xe with
    | idleEP => trivial
    | recvEP q => rfl
    | sendEP q => exact absurd rfl (hns q)
  obtain ⟨rv, hra⟩ := J.replyArg_of (rc := .Reply rptr g) (Or.inr ⟨hcr1, rptr, g, rfl, xr, hkr⟩)
    (Or.inr ⟨rptr, g, rfl, hM.rt⟩)
  obtain ⟨hcov, hcovR⟩ := J.recvCov_of heE hHd hHr hra
  -- the receive leaf: block on the idle endpoint
  have leaf : endpoint.receive_ipc st arI s a t (.Endpoint ep b0 b1 true b3 b4) true (.Reply rptr g) ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (absCap (.Endpoint ep b0 b1 true b3 b4)) true
        (absCap (.Reply rptr g)) σ).1,
        RelTopM (L := L) r.1 z.2 ∧ JStabR (L := L) arI AR Z H Cs r.1 r.2 z.2 ⦄ := by
    by_cases h0 : L.mem s (tBoundA t) = 0#u64
    · have hbS : xs.tcbBoundNotification = none := by rw [hxs.bound, h0, Notif.optRef_zero]
      exact J.recvIpcBlockJGMSt hctT hcur hni hsw hnq hks heE hke hcB hcov hra hcovR b0 b1 true b3 b4 b0.bv
        (rightsOf b1 true b3 b4) (fun h => receive_ipc_block_red hra h0 (Or.inl hM.ep) h)
        (receiveIpc_noSend b0.bv (rightsOf b1 true b3 b4) true (replyArg_spec J.ip.e hI.1.toE hra) hks hbS hke hns)
    · obtain ⟨hstN, hwn⟩ := hM.ntfn.resolve_left h0
      have hbS : xs.tcbBoundNotification = some (L.mem s (tBoundA t)).bv := by
        rw [hxs.bound, Notif.optRef_ne h0]
      obtain ⟨xn, hkn⟩ := J.sv.tcbNtfn t.bv xs _ hks hbS
      obtain ⟨n', hn', e'⟩ := J.obj.ntfn _ xn hkn
      obtain rfl := Sched.bv_inj e'
      have hxn := hI.1.toN.at_ntfn hn' hkn
      have hna : Fl4Spec.isActive xn = false := by
        have ho := hxn.obj
        cases hxo : xn.ntfnObj with
        | activeNtfn b' => rw [hxo] at ho; exact absurd (ho.1.trans ntfn_consts.2.2.symm) hstN
        | idleNtfn => simp [Fl4Spec.isActive, hxo]
        | waitingNtfn q => simp [Fl4Spec.isActive, hxo]
      have hnr : ¬ (xn.ntfnSc = xs.tcbSchedContext ∧ xn.ntfnSc ≠ none) := by
        have hsN : xn.ntfnSc = Notif.optRef (L.mem s (nScA (L.mem s (tBoundA t)))) := hxn.sc
        obtain ⟨Q0, R0, -, hs0⟩ := J.xtop.fin.1.1.1.lists
        obtain ⟨xt0, hkt0, -, -, hsct, -⟩ := hs0.tcb t hctT
        rw [hks] at hkt0; cases hkt0
        rintro ⟨h1, h2⟩
        rw [hsN, hsct] at h1
        rw [hsN] at h2
        have a0 : L.mem s (nScA (L.mem s (tBoundA t))) ≠ 0#u64 := fun e => by rw [e, Notif.optRef_zero] at h2; exact h2 rfl
        rcases hwn with hw | hw
        · exact a0 hw
        · rw [Notif.optRef_ne a0] at h1
          have b0' : L.mem s (P1.scA t) ≠ 0#u64 := fun e => by rw [e, Notif.optRef_zero] at h1; cases h1
          rw [Notif.optRef_ne b0'] at h1
          exact hw (Sched.bv_inj (Option.some.inj h1))
      exact J.recvIpcBlockNJGMSt hctT hcur hni hsw hnq hks hn' hbS hkn hna hnr heE hke hcB hcov hra hcovR
        b0 b1 true b3 b4 b0.bv (rightsOf b1 true b3 b4)
  -- FL4's `handle_recv` down to the receive, the spec's `handleRecv` along the same branch
  have top : ∀ y : Unit × Fl4Spec.State Unit, ((.ok y.1, y.2) : Except Fl4Spec.Fault Unit × _) ∈
      ((hrBody true true t.bv (Fl4Spec.toBl (L.mem s (regA t layout.reg.CAP)).bv)).run σ).1 →
      y ∈ (Fl4Spec.handleRecv (Z := Unit) true true σ).1 := by
    intro y hy
    apply handleRecv_mem hk'
    rw [hcp, hcur]; exact mem_catch_ok hy
  unfold syscall.handle_recv
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s t layout.reg.CAP) ?_
  rintro c0 rfl
  rw [hlc]; simp only [bind_ok, ↓reduceIte]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s t layout.reg.REPLY) ?_
  rintro c1 rfl
  rw [hlr]; simp only [bind_ok]
  refine WP.spec_mono leaf fun r ⟨z, hz, hR⟩ => ⟨z, top z ?_, hR⟩
  have hrights : Fl4Spec.AllowRecv ∈ rightsOf b1 true b3 b4 := by simp [rightsOf, Fl4Spec.AllowRecv]
  unfold hrBody
  refine mem_bindE_ok hcf ?_
  dsimp only [absCap]
  rw [if_pos hrights]
  simp only [↓reduceIte]
  exact mem_bindE_ok (mem_lookupReply_ok hk' he1' rfl) (mem_liftE hz)

set_option maxHeartbeats 4000000 in
/-- (stpost) **The ReplyRecv invocation then receive at stable ghosts, the receive proved**
(module docstring; StPostMid's `mid_invRecvReplyJSt` with `hMid` and `hP` for `hRS`). -/
theorem mid_invRecvReplyJStF [Fl4Proofs.P1.PlainStore st] {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (hnf : ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbFault = none)
    (hnq0 : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hA : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hR0 : MR ar σ.machineState)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (found : cspace.Resolved)
    (hls : cspace.lookup_slot st s ct (L.mem s (regA ct layout.reg.REPLY)) = ok (.Ok found))
    {rptr : U64} {g : Bool} (hcap : obj.Slot.cap st found.slot s = ok (.Reply rptr g))
    (hP : MidRun.JMidPerfHypQ true (Fl4Spec.toBl (L.mem s (regA ct layout.reg.REPLY)).bv) σ)
    (hMid : ∃ (X8 : S) (a8 : A) (rptr' ep : U64),
      syscall.handle_invocation st arI s ar false false true true (L.mem s (regA ct layout.reg.REPLY)) =
        ok (.Ok (), X8, a8) ∧ RRMidSt (st := st) X8 ct rptr' ep) :
    (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s ar false false true true (L.mem s (regA ct layout.reg.REPLY))
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      if b then syscall.handle_recv st arI s2 a2 true true else ok (s2, a2)) ⦃ r =>
      ∃ y ∈ ((DispMid Fl4Spec.replyRegister true).run σ).1, y.1 = .ok () ∧ RelTopM (L := L) r.1 y.2 ∧
        JStabR (L := L) arI AR Z H Cs r.1 r.2 y.2 ∧ MR r.2 y.2.machineState ⦄ := by
  obtain ⟨X8, a8, rptr', ep, hinv, hMs⟩ := hMid
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨-, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hxs := (J.xtop.irelK J.ks J.buf).1.toE.at_tcb hctT hks
  have hcp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs Fl4Spec.replyRegister) =
      Fl4Spec.toBl (L.mem s (regA ct layout.reg.REPLY)).bv := by
    rw [← regIdx_reply, hxs.regs]; rfl
  have hk' : σ.kheap σ.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hreg := mem_getCapReg hk' Fl4Spec.replyRegister
  rw [hcp] at hreg
  have hME := J.midEntry hni hnf
  have hs : MidRun.CQ σ.curThread σ :=
    ⟨⟨rfl, fun x hx => ⟨hME.run x hx, hME.nf x hx⟩⟩, hnq0, by rw [hni.2]; intro e; cases e⟩
  have hInv : syscall.handle_invocation st arI s ar false false true true (L.mem s (regA ct layout.reg.REPLY))
      ⦃ r => r = (.Ok (), X8, a8) ⦄ := by rw [hinv, WP.spec_ok]
  refine WP.spec_bind (WP.spec_and (handle_invocation_replyJSt s ar σ J hA hmax htu hmb hM hKD hni hR0 ct hct true true _
    found hls hcap) hInv) ?_
  rintro ⟨r, s1, a1⟩ ⟨⟨⟨y1, σm⟩, hy, hc, hrel, hX⟩, heqr⟩
  simp only [Prod.mk.injEq] at heqr
  obtain ⟨-, rfl, rfl⟩ := heqr
  -- `s1`, `a1` are now `s1`, `a1`'s names
  rcases hc with ⟨hr1, hy1⟩ | ⟨hr1, -⟩
  swap
  · dsimp only at hr1; subst hr1; rw [if_pos rfl] at hX; exact hX.elim
  dsimp only at hr1 hy1
  subst hr1 hy1
  rw [if_neg (fun h => by cases h)] at hX
  obtain ⟨hJs, hMm⟩ := hX
  have hC : CurRun σm := MidRun.jMidRunHyp_of hP.toP hME _ hy rfl
  obtain ⟨⟨hct0, -⟩, hnq', hsw'⟩ := MidRun.midRunQ_shell true true _ σ hs hME.nq hP _ hy
  obtain ⟨G1, V1, Ac1, Lst1, D1, J1⟩ := hJs
  have hid : σm.curThread ≠ σm.idleThread := curRun_ne_idle hC J1.act.2
  have hact : ActRel (L.actionW s1) σm.schedulerAction := by
    have hSR := J1.xtop.fin.1.1.1
    obtain ⟨Q, R', hcq, -⟩ := hSR.lists
    have h := hSR.act
    rw [← hcq.cur] at h
    exact h
  have hsw : σm.schedulerAction ≠ .resumeCurThread := by
    intro e; rw [e] at hact; exact hMs.act0 hact
  have hmE : MidE σm := by
    refine ⟨hid, hC, Or.inr ?_⟩
    cases e : σm.schedulerAction with
    | resumeCurThread => exact absurd e hsw
    | chooseNewThread => rw [e] at hact; exact absurd hact hMs.act1
    | switchThread w => exact ⟨w, rfl, fun hw => hsw' (by rw [e, hw, hct0])⟩
  have hnqm : ∀ d p, σm.curThread ∉ σm.readyQueues d p := by rw [hct0]; exact hnq'
  show (do
    let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
    if b then syscall.handle_recv st arI s2 a2 true true else ok (s2, a2)) ⦃ _ ⦄
  rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
    unfold syscall.after_invocation; rfl, bind_ok]
  show (if true = true then syscall.handle_recv st arI s1 a1 true true else ok (s1, a1)) ⦃ _ ⦄
  rw [if_pos rfl]
  have hRS : syscall.handle_recv st arI s1 a1 true true ⦃ r => ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) true true σm).1,
      RelTopM (L := L) r.1 z.2 ∧ JStabR (L := L) arI AR Z H Cs r.1 r.2 z.2 ⦄ :=
    WP.spec_mono (handle_recv_rrJSt s1 a1 σm J1 hmE hsw hnqm hMs) fun r ⟨z, hz, h1, h2⟩ =>
      ⟨z, hz, h1, JStabR.mv h2⟩
  refine WP.spec_mono (spec_mrz hM hRS (MKD.syscall_handle_recv L.total hA hKD hMm)
    (fun z hz => congrArg Prod.fst (MachT.mtk_handleRecvG true true _ z hz))) ?_
  rintro r ⟨z, hz, ⟨hrl, hJ⟩, hMz⟩
  exact ⟨(.ok z.1, z.2), mem_bindE_ok (mem_liftE (ε := Unit) hreg) (mem_bindE_ok hy (mem_liftE hz)),
    rfl, hrl, hJ, hMz⟩

set_option maxHeartbeats 4000000 in
/-- (stpost) **`dispatch_syscall` for `SysReplyRecv` with a Reply cap, stable ghosts, the receive
proved** (StPostMid's `dispatch_replyRecvJSt` at `mid_invRecvReplyJStF`). -/
theorem dispatch_replyRecvJStF [Fl4Proofs.P1.PlainStore st] {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (hnf : ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbFault = none)
    (hnq0 : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hA : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hR0 : MR ar σ.machineState)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (found : cspace.Resolved)
    (hls : cspace.lookup_slot st s ct (L.mem s (regA ct layout.reg.REPLY)) = ok (.Ok found))
    {rptr : U64} {g : Bool} (hcap : obj.Slot.cap st found.slot s = ok (.Reply rptr g))
    (hP : MidRun.JMidPerfHypQ true (Fl4Spec.toBl (L.mem s (regA ct layout.reg.REPLY)).bv) σ)
    (hMid : ∃ (X8 : S) (a8 : A) (rptr' ep : U64),
      syscall.handle_invocation st arI s ar false false true true (L.mem s (regA ct layout.reg.REPLY)) =
        ok (.Ok (), X8, a8) ∧ RRMidSt (st := st) X8 ct rptr' ep) :
    syscall.dispatch_syscall st arI s ar fl4_abi.syscall.SysReplyRecv ⦃ r =>
      ∃ y ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) true .sysReplyRecv).run σ).1, y.1 = .ok () ∧
        RelTopM (L := L) r.1 y.2 ∧ JStabR (L := L) arI AR Z H Cs r.1 r.2 y.2 ∧ MR r.2 y.2.machineState ⦄ := by
  have hn : MidSysR fl4_abi.syscall.SysReplyRecv .sysReplyRecv layout.reg.REPLY Fl4Spec.replyRegister true :=
    Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩
  have h := mid_invRecvReplyJStF s ar σ J hni hnf hnq0 hA hmax htu hmb hM hKD hR0 ct hct found hls hcap hP hMid
  rw [fl4HandleSyscall_mid hn]
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 -
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
  rintro c1 rfl
  rw [if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysSend; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBSend; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysCall; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysRecv; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBRecv; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysWait; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBWait; decide), if_pos trivial]
  exact h

end StRecvB

end

end Fl4Proofs.P3
