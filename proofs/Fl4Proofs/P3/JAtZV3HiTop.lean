/-
P3 (line mmuAD, gen 41): **the whole `fl4HandleInvocationVF` step for a VCPU cap at `JAtZV3`** — FL4's
`syscall.handle_invocation` (syscall.rs l. 171-215) when the looked-up cap is `Cap::Vcpu`, against the extended
spec's `fl4HandleInvocationVF onCore remoteCur true` (Ext/VirtKernelF; `reportError` = FL4's
`KERNEL_INVOCATION_REPORT_ERROR_IPC`, set).

* The spec's phases with the extended decoder and dispatcher: `hiMEV`, `hiMFinVF` (HandleTop's `hiME` / `hiMFin`
  with `fl4DecodeInvocationV` / `fl4PerformInvocationVF`), `hi_memVF`, `hiMEV_run`, `hiMFinVF_ok`.
* `zv_liftE_inv`: a single outcome of `liftE m` is one of `m`.
* `JAtZV3.bufFrames`: the caller's receive-buffer words are aligned user-frame words (as `JAtZ.replyErrJ`'s `hfr`).
* **`ZvPost`**: `JAtZV3` at some ghosts (`V`, `X` fixed). **`ZvFaultHyp` [W]**: FL4's `handle_fault ct f` at the
  front end's state against the spec's `handleFault ct f'`, ending in `ZvPost` — the fault-IPC send at
  `JAtZV3`, not proved (P3/XTopJointFault* prove it at `JAtZ`, landing at `JAt` with ghosts no `JAtZV3` frame can
  reach; a `JAtZV3` port is a whole sub-proof). Asked only when `blocking` and the lookup or the extra-cap lookup
  faults, at that state, as HandleTopX's `hFL` / `hrr`.
* **`JAtZV3.vcpuHandleJ`** — the top. Hypotheses: the front end's reads and their single spec outcomes (as
  HandleTopX's `handle_invocation_refinesMX`), the faults (`ZvFaultHyp`, blocking only), and the scopes
  **`hVc`** (the cap the lookup finds is a VCPU cap: this theorem is the VCPU arm), **`IoFreshEx`** for
  EnableIOPort (Q2, as gen 40), and **[J] `ZvCtRun`** (`hrun`): the current thread's spec state is `running` at
  a syscall (FL4 kernel/entry.rs `exit` l. 718-790: a `TS_RUNNING_VM` thread is only ever resumed into its guest
  (`vm::run`), never to user mode, so no syscall comes from one; `Restart` is turned into `Running` by
  `activate_thread` before user mode, sched.rs l. 687-698; l4v's `handle_event` precondition `ct_running`). Post: FL4 `Ok`, a spec outcome
  `.ok ()` of `fl4HandleInvocationVF`, `ZvPost` between them.
  Success: the spec restarts the caller, performs (`zc_restart_perform`: the same outcome from the restart state
  as `VFrontPost`'s from `σ`), reads `Restart`, replies and sets `Running` (`zc_tail` / `specTail_nil`); FL4
  either restarts at the decode's end and runs `flTail` (`JAtZV3.restartJ`, `flTail3`) or replied in the decode
  (`vreply3`, `replyWsRun3`; `flTail` does nothing, `flTailNo`). Decode error: `reply_error` (`replyFailJ3`).

Named premises: **[W] `ZvFaultHyp`** (blocking faults only), **[J] `ZvCtRun`** (as `hrun`); platform ones of
`vcpuFrontJ` ([P] `ZvSyncKeep`, `ZvVirtAgree`, `CapAgree`, `P0.ArchTotal`, `ARKeep`); scope `IoFreshEx`, `hVc`.
No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3HiErr
import Fl4Proofs.P3.JAtZV3HiLen
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## The spec's phases with the extended dispatcher -/

section
open Fl4Spec

/-- The decode phase with the extended decoder. -/
def hiMEV (thread : ObjRef) (info : MessageInfo) (cptr : CapRef) (firstPhase : Bool) :
    CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef → SEMonad Unit Fl4InvocationV :=
  fun (slot, cap, extracaps, buffer) => do
    let args ← NonDetE.liftE <| getMrs thread buffer info
    fl4DecodeInvocationV firstPhase info.miLabel args cptr slot cap extracaps buffer

/-- The invocation phase with the extended dispatcher. -/
def hiMFinVF (onCore remoteCur : ObjRef → Bool) (thread : ObjRef) (calling blocking canDonate : Bool) :
    Fl4InvocationV → PMonad Unit Unit :=
  fun oper => do
    withoutPreemption <| setThreadState thread .restart
    let reply ← fl4PerformInvocationVF onCore remoteCur blocking calling canDonate oper
    withoutPreemption <| do
        let state ← getThreadState thread
        match state with
        | .restart => do
          NonDet.when calling <|
            replyFromKernel thread (0, reply)
          setThreadState thread .running
        | _ => return ()

theorem hi_memVF {σ : State Unit} (onCore remoteCur : ObjRef → Bool) (rep : Bool)
    {calling blocking canDonate firstPhase : Bool} {cptr : CapRef} {mi : MessageInfo} {t : ObjRef}
    (hcur : σ.curThread = t) (hmi : getMessageInfo (Z := Unit) t σ = ({(mi, σ)}, False))
    {y : Except Unit Unit × State Unit}
    (h : y ∈ ((syscall (hiMF t mi cptr) (fun fault => NonDet.when blocking <| handleFault t fault)
      (hiMEV t mi cptr firstPhase)
      (fun err => NonDet.when calling <| fl4ReplyFromKernelError rep t <| msgFromSyscallError err)
      (hiMFinVF onCore remoteCur t calling blocking canDonate)).run σ).1) :
    y ∈ ((fl4HandleInvocationVF (Z := Unit) onCore remoteCur rep calling blocking canDonate firstPhase cptr).run σ).1 := by
  unfold fl4HandleInvocationVF
  refine mem_bindE_ok (a := σ.curThread) (s' := σ) (mem_liftE (x := (σ.curThread, σ)) rfl) ?_
  refine mem_bindE_ok (a := mi) (s' := σ) (mem_liftE (x := (mi, σ)) (by rw [hcur, hmi]; rfl)) ?_
  rw [hcur]
  exact h

theorem hiMEV_run {σ : State Unit} {t : ObjRef} {mi : MessageInfo} {cptr : CapRef} {fp : Bool} {a : Cap}
    {sl : CslotPtr} {buffer : Option ObjRef} {exs : List (Cap × CslotPtr)} {args : List Data}
    (hm : getMrs (Z := Unit) t buffer mi σ = ({(args, σ)}, False)) :
    ExceptT.run (hiMEV t mi cptr fp (sl, a, exs, buffer)) σ =
      (fl4DecodeInvocationV (Z := Unit) fp mi.miLabel args cptr sl a exs buffer).run σ := by
  unfold hiMEV
  exact run_bind_ok (run_liftE hm) _

theorem hiMFinVF_ok {σ σ1 σy : State Unit} (onCore remoteCur : ObjRef → Bool) {t : ObjRef}
    {calling blocking canDonate : Bool} {inv : Fl4InvocationV} {rr : List Data} {z : Unit × State Unit}
    (hst : setThreadState (Z := Unit) t .restart σ = ({((), σ1)}, False))
    (hy : (.ok rr, σy) ∈ ((fl4PerformInvocationVF (Z := Unit) onCore remoteCur blocking calling canDonate inv).run σ1).1)
    (hz : z ∈ (specTail calling t rr σy).1) :
    ((.ok z.1, z.2) : Except Unit Unit × State Unit) ∈
      ((hiMFinVF onCore remoteCur t calling blocking canDonate inv).run σ).1 := by
  unfold hiMFinVF withoutPreemption
  refine mem_bindE_ok (a := ()) (s' := σ1) (mem_liftE (x := ((), σ1)) (by rw [hst]; rfl)) ?_
  refine mem_bindE_ok (a := rr) (s' := σy) hy ?_
  exact mem_liftE hz

theorem zv_liftE_inv {ε α : Type} {m : NonDet (State Unit) α} {σ σ' : State Unit} {a : α}
    (h : ExceptT.run (NonDetE.liftE (ε := ε) m) σ = ({(.ok a, σ')}, False)) : m σ = ({(a, σ')}, False) := by
  unfold NonDetE.liftE at h
  rw [ExceptT.run_lift] at h
  change (m >>= _) σ = _ at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  rw [nd_bind_apply] at h1 h2
  simp only at h1 h2
  refine Prod.ext ?_ ?_
  · ext ⟨b, s⟩
    constructor
    · intro hb
      have : ((.ok b : Except ε α), s) ∈ ({(.ok a, σ')} : Set (Except ε α × State Unit)) := by
        rw [← h1]; exact ⟨(b, s), hb, rfl⟩
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, Except.ok.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      exact rfl
    · intro hb
      simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hb
      obtain ⟨hb1, hb2⟩ := hb
      rw [hb1, hb2]
      have : ((.ok a : Except ε α), σ') ∈ ({(.ok a, σ')} : Set (Except ε α × State Unit)) := rfl
      rw [← h1] at this
      obtain ⟨⟨b, s⟩, hb, hq⟩ := this
      have hq' : ((.ok a : Except ε α), σ') = (.ok b, s) := hq
      simp only [Prod.mk.injEq, Except.ok.injEq] at hq'
      obtain ⟨rfl, rfl⟩ := hq'
      exact hb
  · apply propext
    constructor
    · intro hf; rw [← h2]; exact Or.inl hf
    · intro hf; exact hf.elim

end

/-! ## The premise, the post -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- `JAtZV3` at some ghosts (module docstring). -/
def ZvPost (arI : machine.Arch A) (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ

/-- **[W] The fault handler at `JAtZV3`** (module docstring): FL4's `handle_fault ct f` at the front end's
state against the spec's `handleFault ct f'`, ending in `ZvPost`. -/
def ZvFaultHyp (arI : machine.Arch A) (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (ct : U64) (f : error.Fault) (f' : Fl4Spec.Fault) : Prop :=
  faults.handle_fault st arI s a ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1,
    ZvPost (L := L) arI V X AR r.1 r.2 z.2 ⦄

end

/-- **[J] The caller is `running` at a syscall** (module docstring): the current thread's spec state is
`.running`. FL4: a `TS_RUNNING_VM` thread is only resumed into its guest (kernel/entry.rs `exit` l. 718-790,
`vm::run`), never to user mode, so it makes no syscall; `TS_RESTART` becomes `TS_RUNNING` in `activate_thread`
before user mode (fl4-core sched.rs l. 687-698); l4v's `handle_event` precondition `ct_running`. -/
def ZvCtRun (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  ∀ x, σ.kheap ct.bv = some (.tcb x) → x.tcbState = .running

end

/-! ## The buffer frames -/

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- The caller's receive-buffer words are aligned user-frame words (module docstring). -/
theorem JAtZV3.bufFrames (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : ct ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) :
    ∀ p, Endp.ipcBufOf true x = some p → ∀ k, k < 128 →
      (Endp.bufAddr p k).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p k) σ := by
  have B := J.z2.zv.base
  intro p hp k hk128
  obtain ⟨w, hw, -⟩ := P1.spec_ex_fd (P0.msg.lookup_ipc_buffer.p0 st s true ct (P1.LawfulStore.total (st := st)))
  have hb := J.replyBuf hct hk
  rw [hw, WP.spec_ok] at hb
  have hb' : JBufR Z.B w (Endp.ipcBufOf true x) := hb
  rw [hp] at hb'
  exact ⟨Endp.bufAddr_aligned B.xtop.fin.1.2.ep hb'.2.1 k, buf_frame_of_ok B.bok hk hp k hk128⟩

end

/-! ## The top -/

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The `fl4HandleInvocationVF` step for a VCPU cap at `JAtZV3`** (module docstring). -/
theorem JAtZV3.vcpuHandleJ (hK : ARKeep arI AR) (hSy : ZvSyncKeep arI AR)
    (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a') (hAT : P0.ArchTotal arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (onCore remoteCur : Fl4Spec.ObjRef → Bool)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {info : msginfo.MessageInfo} (hinfo : msg.msg_info st s ct = ok info)
    {mi : Fl4Spec.MessageInfo} (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    {buf : U64} (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf)
    {buffer : Option Fl4Spec.ObjRef}
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    (hr2 : ipc.lookup_extra_caps st s ct buf info = ok r2)
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))}
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False))
    (hrr : (∃ e exs, r2 = .Ok e ∧ er = .ok exs ∧
        (info.label = fl4_abi.label.X86VCPUEnableIOPort → IoFreshEx (L.mem s) e)) ∨
      (∃ f f', r2 = .Err f ∧ er = .error f' ∧
        (blocking = true → ZvFaultHyp (L := L) arI V X AR s a σ ct f f')))
    {args : List Fl4Spec.Data} (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(args, σ)}, False))
    (hFL : blocking = true → ∀ lf lf', LookupFaultRel lf lf' →
      ZvFaultHyp (L := L) arI V X AR s a σ ct (.Cap cptr false lf)
        (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) false lf'))
    (hVc : ∀ r1, cspace.lookup_slot st s ct cptr = ok (.Ok r1) → ∃ p, capV (L.mem s) r1.slot = .Vcpu p)
    (hrun : ZvCtRun σ ct) :
    syscall.handle_invocation st arI s a is_call blocking can_donate first_phase cptr ⦃ res =>
      ∃ y ∈ ((Fl4Spec.fl4HandleInvocationVF (Z := Unit) onCore remoteCur true is_call blocking can_donate first_phase
          (Fl4Spec.toBl cptr.bv)).run σ).1,
        res.1 = .Ok () ∧ y.1 = .ok () ∧ ZvPost (L := L) arI V X AR res.2.1 res.2.2 y.2 ⦄ := by
  have B := J.z2.zv.base
  obtain ⟨hcur, -⟩ := B.curEq hct
  obtain ⟨htcb, x, hk⟩ := B.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem B.xtop.fin.1 hcur.symm
  have hxr : x.tcbState = .running := hrun x hk
  have hP0 : ZvPost (L := L) arI V X AR s a σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  unfold syscall.handle_invocation
  rw [hct]; simp only [bind_ok, hinfo]
  obtain ⟨rl, hrl, -⟩ := P1.spec_ex_fd (P0.cspace.lookup_slot.p0 st s ct cptr (P1.LawfulStore.total (st := st)))
  have hLS := lookup_slot_refines (Z := Unit) Z.th s σ B.xtop.rel.2.1.1 B.xtop.rel.2.1.2.1 ct htcb cptr
  rw [hrl, WP.spec_ok] at hLS
  rw [hrl, bind_ok]
  obtain ⟨e, he, hrel, hok⟩ := hLS
  cases rl with
  | Err lf =>
    cases e with
    | ok v => exact hrel.elim
    | error lf' =>
      simp only
      have hl : (Fl4Spec.lookupCapAndSlot (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ =
          ({(.error lf', σ)}, False) := by
        unfold Fl4Spec.lookupCapAndSlot; exact run_bind_error (s := σ) he _
      have hmF := hiMF_lookup_err (mi := mi) hl
      cases blocking
      · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨(.ok (), σ), hi_memVF onCore remoteCur true hcur hmi (mem_syscall_fault (z := ((), σ)) hmF
          (mem_when (fun h => by cases h) (fun _ => rfl))), trivial, rfl, hP0⟩
      · simp only [↓reduceIte]
        refine WP.spec_bind (hFL rfl lf lf' hrel) ?_
        rintro ⟨s1, a1⟩ ⟨z, hz, hZ⟩
        refine (WP.spec_ok _).2 ?_
        exact ⟨(.ok z.1, z.2), hi_memVF onCore remoteCur true hcur hmi
          (mem_syscall_fault hmF (mem_when (fun _ => hz) (fun h => by cases h))), rfl, rfl, hZ⟩
  | Ok r1 =>
    cases e with
    | error lf' => exact hrel.elim
    | ok v =>
      obtain ⟨sl, rest⟩ := v
      obtain ⟨hsl, -⟩ := hrel
      obtain ⟨pc, hp, hth, -⟩ := hok
      obtain ⟨c, ac, hc, hca, hget⟩ := B.xtop.rel.2.1.1.slot_cap hp hth
      obtain ⟨pv, hpv⟩ := hVc r1 hrl
      have hxs : r1.slot = cslotAddr sl := hsl
      have hcv : capV (L.mem s) (cslotAddr sl) = .Vcpu pv := by rw [← hxs]; exact hpv
      have hcc : c = .Vcpu pv := by
        have h1 := capAt_capV (L.mem s) (cslotAddr sl)
        rw [hc, hcv] at h1; exact ok_inj h1
      subst hcc
      have hA : AbsSlot Z.th sl := ⟨pc, hp, Or.inl hth⟩
      have hl : (Fl4Spec.lookupCapAndSlot (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ =
          ({(.ok (ac, sl), σ)}, False) := by
        unfold Fl4Spec.lookupCapAndSlot
        rw [run_bind_ok he]
        simp only
        rw [run_bind_ok (run_liftE hget)]
        rfl
      simp only
      rw [slot_cap_eq, hsl, hc]
      simp only [bind_ok, hbuf, hr2]
      rcases hrr with ⟨ex, exs, rfl, rfl, hIo⟩ | ⟨f, f', rfl, rfl, hfh⟩
      · simp only
        rw [msgLen_eq]; simp only [bind_ok]
        have hca' : absCap (.Vcpu pv) = ac := hca.2
        subst hca'
        have hmF := hiMF_ok (mi := mi) hl hbuffer her
        have hmE := hiMEV_run (cptr := Fl4Spec.toBl cptr.bv) (fp := first_phase) (a := absCap (.Vcpu pv)) (sl := sl)
          (exs := exs) hmrs
        have hab : absCap (.Vcpu pv) = Fl4Spec.Cap.archObjectCap (Fl4Spec.ArchCap.vcpuCap pv.bv) := rfl
        refine WP.spec_bind (J.vcpuFrontJ hK hSy hVA hCap hAT hct hinfo hmi hbuf hbuffer hr2 her hmrs hA.isSlot hcv
          (cslotAddr sl) blocking is_call can_donate first_phase hIo) ?_
        rintro ⟨r3, s1, a1⟩ hVP
        rcases hVP first_phase (Fl4Spec.toBl cptr.bv) sl onCore remoteCur blocking is_call can_donate with
          ⟨e3, e', he3, hse, hdec, hs1, J1⟩ | ⟨inv, rep, s', σ', Ac', Lst', hok3, hdec, hperf, J', hT⟩
        · simp only at he3 hs1
          subst he3 hs1
          cases e3 with
          | Sys e2 =>
            refine WP.spec_mono (J1.replyFailJ3 hcur is_call e2 e' (Or.inl hse)) ?_
            rintro res ⟨hres, z, hz, Jz⟩
            exact ⟨(.ok z.1, z.2), hi_memVF onCore remoteCur true hcur hmi
              (mem_syscall_err hmF (by rw [hmE, hab, hdec]; rfl) hz), hres, rfl, ⟨_, _, _, _, _, _, Jz⟩⟩
          | Fault _ => cases e' <;> exact hse.elim
          | Lookup _ => cases e' <;> exact hse.elim
          | Preempted => cases e' <;> exact hse.elim
        · simp only at hok3; subst hok3
          have hpv' : Fl4Spec.performVcpuInvocationF (Z := Unit) inv σ = ({(rep, σ')}, False) :=
            zv_liftE_inv (by rw [← zv_perfV_vcpu onCore remoteCur blocking is_call can_donate]; exact hperf)
          have hkc : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
          obtain ⟨hst, hperfR, hk', hc'⟩ := zc_restart_perform hpv' hkc (by rw [hxr]; exact fun h => by cases h)
            onCore remoteCur blocking is_call can_donate
          rw [hcur] at hst hperfR hk' hc'
          have hmem : ((Except.ok rep : Except Unit (List Fl4Spec.Data)), zcR ct.bv σ') ∈
              ((Fl4Spec.fl4PerformInvocationVF (Z := Unit) onCore remoteCur blocking is_call can_donate
                (.vcpu inv)).run (zcR ct.bv σ)).1 := by rw [hperfR]; exact Set.mem_singleton _
          have hdecO : ((Except.ok (Fl4Spec.Fl4InvocationV.vcpu inv) : Except Fl4Spec.SyscallError _), σ) ∈
              (ExceptT.run (hiMEV ct.bv mi (Fl4Spec.toBl cptr.bv) first_phase (sl, absCap (.Vcpu pv), exs, buffer)) σ).1 := by
            rw [hmE, hab, hdec]; exact Set.mem_singleton _
          have hfin : ∀ z, z ∈ (specTail is_call ct.bv rep (zcR ct.bv σ')).1 →
              ((Except.ok z.1 : Except Unit Unit), z.2) ∈ ((Fl4Spec.fl4HandleInvocationVF (Z := Unit) onCore remoteCur
                true is_call blocking can_donate first_phase (Fl4Spec.toBl cptr.bv)).run σ).1 := fun z hz =>
            hi_memVF onCore remoteCur true hcur hmi (mem_syscall_fin hmF hdecO (hiMFinVF_ok onCore remoteCur hst hmem hz))
          have hrun' : x.tcbState = .running := hxr
          have hctS' : sched.cur_thread st s' = ok ct := by
            obtain ⟨c', hc'', -⟩ := P1.spec_ex_fd (P0.sched.cur_thread.p0 st s' (P1.LawfulStore.total (st := st)))
            have hcc := (J'.z2.zv.base.curEq hc'').1
            rw [hc'', VirtSanEq.u64_ext (hcc.symm.trans hc')]
          rcases hT with ⟨hr0, hs1⟩ | ⟨y, hry, hs1⟩ | ⟨ws, hrw, hs1⟩
          · -- the empty reply: FL4 restarts at the decode's end, then `flTail`
            subst hr0
            obtain ⟨Lst1, J1⟩ := J'.restartJ (hc'.trans rfl) hk' (B.thTcb hctT) (by rw [hrun']; rfl) hs1
            rw [← zcR_of hk'] at J1
            have hkR : (zcR ct.bv σ').kheap ct.bv = some (.tcb { x with tcbState := .restart }) := by
              rw [zcR_kheap hk', Function.update_self]
            refine WP.spec_mono (J1.flTail3 hctT hkR is_call) ?_
            rintro res ⟨hres, z, hz, Lz, Jz⟩
            exact ⟨_, hfin z hz, hres, rfl, ⟨_, _, _, _, _, _, Jz⟩⟩
          · -- one word, replied in the decode
            subst hry
            have hR := J'.vreply3 hctS' hctT hk' hrun' is_call y
            rw [hs1, WP.spec_ok] at hR
            obtain ⟨Lst1, J1⟩ := hR
            have hk1 : (stsAct (updK (if is_call then replyState σ' ct.bv x [y.bv] else σ') ct.bv
                (.tcb { (if is_call then replyTcbB x (Endp.ipcBufOf true x) [y.bv] else x) with
                  tcbState := .running })) ct.bv).kheap ct.bv =
                some (.tcb { (if is_call then replyTcbB x (Endp.ipcBufOf true x) [y.bv] else x) with
                  tcbState := .running }) := by rw [stsAct_kheap]; simp [updK]
            refine WP.spec_mono (J1.flTailNo hctT hk1 (fun h => by cases h) is_call) ?_
            rintro res rfl
            refine ⟨_, hfin ((), _) ?_, rfl, rfl, ⟨_, _, _, _, _, _, J1⟩⟩
            rw [zc_tail hk' hrun' hc' is_call [y.bv] (by simp [Fl4Spec.msgMaxLength])
              (fun p hp z hz => J'.bufFrames hctT hk' p hp z.1 (mrPairs_lt hz))]
            exact Set.mem_singleton _
          · -- a word list, replied in the decode
            subst hrw
            have hlen : (ws.map (·.bv)).length ≤ 64 := zv_rep_len (zv_decV_mem hdec) hpv'
            have hlen' : ws.length ≤ 120 := by rw [List.length_map] at hlen; omega
            have hR := J'.replyWsRun3 hctT hk' hrun' is_call ws hlen'
            rw [hs1, WP.spec_ok] at hR
            obtain ⟨Lst1, J1⟩ := hR
            have hk1 : (stsAct (updK (if is_call then replyState σ' ct.bv x (ws.map (·.bv)) else σ') ct.bv
                (.tcb { (if is_call then replyTcbB x (Endp.ipcBufOf true x) (ws.map (·.bv)) else x) with
                  tcbState := .running })) ct.bv).kheap ct.bv =
                some (.tcb { (if is_call then replyTcbB x (Endp.ipcBufOf true x) (ws.map (·.bv)) else x) with
                  tcbState := .running }) := by rw [stsAct_kheap]; simp [updK]
            refine WP.spec_mono (J1.flTailNo hctT hk1 (fun h => by cases h) is_call) ?_
            rintro res rfl
            refine ⟨_, hfin ((), _) ?_, rfl, rfl, ⟨_, _, _, _, _, _, J1⟩⟩
            rw [zc_tail hk' hrun' hc' is_call (ws.map (·.bv)) (by simp [Fl4Spec.msgMaxLength] at hlen ⊢; omega)
              (fun p hp z hz => J'.bufFrames hctT hk' p hp z.1 (mrPairs_lt hz))]
            exact Set.mem_singleton _
      · simp only
        have hmF := hiMF_extra_err (cptr := Fl4Spec.toBl cptr.bv) hl hbuffer her
        cases blocking
        · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          exact ⟨(.ok (), σ), hi_memVF onCore remoteCur true hcur hmi (mem_syscall_fault (z := ((), σ)) hmF
            (mem_when (fun h => by cases h) (fun _ => rfl))), trivial, rfl, hP0⟩
        · simp only [↓reduceIte]
          refine WP.spec_bind (hfh rfl) ?_
          rintro ⟨s1, a1⟩ ⟨z, hz, hZ⟩
          refine (WP.spec_ok _).2 ?_
          exact ⟨(.ok z.1, z.2), hi_memVF onCore remoteCur true hcur hmi
            (mem_syscall_fault hmF (mem_when (fun _ => hz) (fun h => by cases h))), rfl, rfl, hZ⟩

end

end Fl4Proofs.P3
