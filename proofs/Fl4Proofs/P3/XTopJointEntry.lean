/-
P3 (DESIGN.md §9): **one invocation entry at `J`** (`handle_invocation_refinesJ`):
the J-level decodes composed into FL4's `syscall::handle_invocation`, from
`JAtZ` at entry to the spec's `fl4HandleInvocationR` outcome with `JAt`
after (`JAtPre` after a preempted invocation).

The XTop-level counterpart is HandleTopX's `handle_invocation_refinesMX`
(`X` threaded through the lookup, the decode, the reply and the fault
handler), with every cap's `hDec` at `XTop` from TopXAll's `decOK_XTop`
(most caps named there: `TcbXHyp`, `CnodeXHyp`, …). No composition above
`handle_invocation` exists at XTop either (no P3 theorem about
`handle_syscall`, `dispatch_syscall`, `after_invocation`, `finish`, or the
spec's `callKernel`); P1 has only `handle_syscall.entry` (`EntryInv`).

* `HIPostMXP`, `handle_invocation_refinesMXP`: `handle_invocation_refinesMX`
  with `XP` after a preempted invocation (`X` after any other), the decode's
  statement `XCapP` (XTopJointCnDel), and the invoked slot a CNode slot of
  the typed heap (from the lookup, `WalkRel`) passed to `hDec`. Its reply
  premises are narrower than HandleTopX's `ReplyHypMX`: the success tail
  (`hRepS`) only from states whose current thread is still the invoker
  (`hPK`: the invocation keeps the current thread), the error reply
  (`hRepF`) only at the entry state (a decode error leaves FL4's and the
  spec's states unchanged).
* The reply tails at `J` (XTopJointReplyTail): `JAtZ.flTailJ` (success,
  empty result) and `JAtZ.replyFailJ` (the error reply with the debug word,
  so the top theorem is against `fl4HandleInvocationR true`, FL4's
  `KERNEL_INVOCATION_REPORT_ERROR_IPC`), from `JEntryGlob`'s buffer facts
  and `PerfCurKeep` (proved: SpecPerfCur's `perfCurKeep`).
* The premises, by scope (`JEntryHyps` bundles them):
  - `JEntryGlob`: platform [P] and ∀-state facts at the typed heap [J]/[W];
  - `JEntryAt`: facts at the entry state [J];
  - `JPath`: per cap, the facts of exactly that cap's decode path; a cap or
    label with no J proof yet is one named `XCapP` (`JCapOpen`, [W]).
* `decOK_J`: the dispatch on the cap (the table in its docstring).
* `handle_invocation_refinesJ`: the composition. The front end's reads are
  proved related (FrontEndExtra): the label words (`JAtZ.frontJ`:
  `info.label.bv = mi.miLabel`), the extra slots (`ExtraOK`, giving every
  path's `ExtraRel`/`ExtraRel2`/`ExtraSRel`/`XcRel`) and the argument words
  (`JAtZ.argsJ`: `msgLen`, `syscall_arg`, `ArgRel`). The spec decodes
  labels by FL4's numbers (PORTING.md "Invocation label numbers"), so every
  path's label fact holds at `slbl = lbl.bv` (FrontEndLabel): directly for
  SchedControl, IRQ control, IO port control, IO ports and Untyped; for
  CNode, Thread, SchedContext, IRQ handler and Domain, whose decodes take an
  equality with an FL4-label map, at a canonical label with the same spec
  decode (`*_canon`, `XCapP.lbl_congr`). The VSpace paths' labels too
  (`pt_label` … `frame_label`, `makePool_label`), and their extra caps from
  `ExtraOK` (XTopJointVsCap's `ExtraOK.vsExtra`, `.poolExtra`, `.mpExtra`).

`JAtZ` is used only through the J decodes, `J.xtop`, `J.curEq` and
`SpecGlob` at entry, so changes of `JAtZ`'s fields leave this module alone.
-/
import Fl4Proofs.P3.XTopJointTcb
import Fl4Proofs.P3.JEntryKs
import Fl4Proofs.P3.JEntryIrq
import Fl4Proofs.P3.XTopJointCnDel
import Fl4Proofs.P3.XTopJointIrqDel
import Fl4Proofs.P3.XTopJointIrqL
import Fl4Proofs.P3.ScMsgOK
import Fl4Proofs.P3.TopXAll
import Fl4Proofs.P3.XTopJointIpcJ
import Fl4Proofs.P3.XTopJointSendPushD
import Fl4Proofs.P3.XTopJointVsCap
import Fl4Proofs.P3.XTopJointVsMap
import Fl4Proofs.P3.XTopJointVsFb
import Fl4Proofs.P3.XTopJointVsOff
import Fl4Proofs.P3.XTopJointVsReply
import Fl4Proofs.P3.XTopJointVsSub
import Fl4Proofs.P3.XTopJointMakePool
import Fl4Proofs.P3.XTopJointUt
import Fl4Proofs.P3.UtEpRet
import Fl4Proofs.P3.ScJointUnbind
import Fl4Proofs.P3.ScJointConsumed
import Fl4Proofs.P3.ScJointYield
import Fl4Proofs.P3.XTopJointReplyTail
import Fl4Proofs.P3.SpecPerfCur
import Fl4Proofs.P3.FrontEndExtra
import Fl4Proofs.P3.FrontEndLabel
import Fl4Proofs.P3.XTopJointNoFault
import Fl4Proofs.P3.XTopJointFaultEp
import Fl4Proofs.P3.XTopJointFaultRecv
import Fl4Proofs.P3.UtRetResetJ
import Fl4Proofs.P3.UtDevUt
import Fl4Proofs.P3.UtDevReset
import Fl4Proofs.P3.XTopJointFaultTmo
import Fl4Proofs.P3.MpDirtyJ
import Fl4Proofs.P3.BufJ
import Fl4Proofs.P3.XTopJointTdx
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## `handle_invocation` with `XP` after a preemption -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The result of `handle_invocation` with `XP` after a preemption**
(`HIPostMX` with `X` replaced by `XP` when the result is `Preempted`). -/
def HIPostMXP (X XP : S → A → Fl4Spec.State Unit → Prop) (rep : Bool) (σ : Fl4Spec.State Unit)
    (calling blocking canDonate firstPhase : Bool) (cptr : Fl4Spec.CapRef)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) rep calling blocking canDonate firstPhase cptr).run σ).1,
    ((res.1 = .Ok () ∧ y.1 = .ok ()) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
    RelTopM (L := L) res.2.1 y.2 ∧
    (if res.1 = .Err .Preempted then XP res.2.1 res.2.2 y.2 else X res.2.1 res.2.2 y.2)

theorem ifP_ok {X XP : S → A → Fl4Spec.State Unit → Prop} {r : core.result.Result Unit error.Exc} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : r = .Ok ()) (hx : X s a σ) :
    (if r = .Err .Preempted then XP s a σ else X s a σ) := by
  subst h; rw [if_neg (fun h => by cases h)]; exact hx

theorem ifP_X {X XP : S → A → Fl4Spec.State Unit → Prop} {r : core.result.Result Unit error.Exc} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : r ≠ .Err .Preempted)
    (hx : if r = .Err .Preempted then XP s a σ else X s a σ) : X s a σ := by
  rw [if_neg h] at hx; exact hx

/-- **`handle_invocation` refines l4v's, keeping `X` (`XP` if preempted)**
(`handle_invocation_refinesMX` with the decode's `XCapP`; `hDec` also gets
the invoked slot as a CNode slot of `th`). -/
theorem handle_invocation_refinesMXP (X XP : S → A → Fl4Spec.State Unit → Prop) (rep : Bool) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (th : TypedHeap) (G : MdbGhost)
    (hP : Placed th) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hDR : DomRel (L.mem s) (L.ksb s) σ) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (hX0 : X s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64)
    -- the front end's reads (`HIRead`)
    (info : msginfo.MessageInfo) (hinfo : msg.msg_info st s ct = ok info)
    (mi : Fl4Spec.MessageInfo) (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    (buf : U64) (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf)
    (buffer : Option Fl4Spec.ObjRef)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
    (hr2 : ipc.lookup_extra_caps st s ct buf info = ok r2)
    (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr)))
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False))
    (hrr : (∃ e exs, r2 = .Ok e ∧ er = .ok exs) ∨
      (∃ f f', r2 = .Err f ∧ er = .error f' ∧ (blocking = true → faults.handle_fault st arI s ar ct f ⦃ r =>
        ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1, RelTopM (L := L) r.1 z.2 ∧ X r.1 r.2 z.2 ⦄)))
    (args : List Fl4Spec.Data) (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(args, σ)}, False))
    -- the fault of a failed lookup
    (hFL : blocking = true → ∀ lf lf', LookupFaultRel lf lf' →
      faults.handle_fault st arI s ar ct (.Cap cptr false lf) ⦃ r =>
        ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) false lf') σ).1,
          RelTopM (L := L) r.1 z.2 ∧ X r.1 r.2 z.2 ⦄)
    -- the success tail (from `X` with the invoker still current) and the error reply (at the entry state)
    (hRepS : ∀ (s1 : S) (a1 : A) (σ' : Fl4Spec.State Unit), RelTopM (L := L) s1 σ' → X s1 a1 σ' →
      σ'.curThread = ct.bv → flTail (st := st) ct is_call s1 a1 ⦃ res => res.1 = .Ok () ∧
        ∃ z ∈ (specTail is_call ct.bv [] σ').1, RelTopM (L := L) res.2.1 z.2 ∧ X res.2.1 res.2.2 z.2 ⦄)
    (hRepF : ∀ (a1 : A) (e : error.SysError) (e' : Fl4Spec.SyscallError), X s a1 σ → ErrRel (.Sys e) e' →
      ((if is_call then do
          let s2 ← syscall.reply_error st s ct e
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)
        else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s, a1)) :
        Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ res =>
        res.1 = .Ok () ∧ ∃ z ∈ ((Fl4Spec.NonDet.when is_call <|
          Fl4Spec.fl4ReplyFromKernelError rep ct.bv (Fl4Spec.msgFromSyscallError e')) σ).1,
          RelTopM (L := L) res.2.1 z.2 ∧ X res.2.1 res.2.2 z.2 ⦄)
    -- the invocation keeps the current thread
    (hPK : ∀ inv σ1 y, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blocking is_call can_donate inv).run σ1).1 →
      y.2.curThread = ct.bv)
    -- the decode and invocation of the cap
    (hDec : ∀ (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
      (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ th p = some (.cnode sl.2.length)) →
      capAt (L.mem s) (cslotAddr sl) = ok c →
      Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) → r2 = .Ok e → er = .ok exs →
      XCapP (L := L) arI X XP s ar σ info.label (msgLen info buf) (cslotAddr sl) c blocking is_call can_donate
        first_phase buf e mi.miLabel args (Fl4Spec.toBl cptr.bv) sl exs buffer ct) :
    syscall.handle_invocation st arI s ar is_call blocking can_donate first_phase cptr ⦃ res =>
      HIPostMXP (L := L) X XP rep σ is_call blocking can_donate first_phase (Fl4Spec.toBl cptr.bv) res ⦄ := by
  have hRT0 : RelTopM (L := L) s σ := ⟨th, G, hP, hCR, hFI, hDR, hFR⟩
  unfold syscall.handle_invocation
  rw [hct]; simp only [bind_ok, hinfo]
  refine WP.spec_bind (lookup_slot_refines (Z := Unit) th s σ hCR.1 hCR.2.1 ct htcb cptr) ?_
  rintro r ⟨e, he, hrel, hok⟩
  cases r with
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
        exact ⟨(.ok (), σ), hi_memR rep hcur hmi (mem_syscall_fault (z := ((), σ)) hmF
          (mem_when (fun h => by cases h) (fun _ => rfl))), Or.inl ⟨rfl, rfl⟩, hRT0, ifP_ok rfl hX0⟩
      · simp only [↓reduceIte]
        refine WP.spec_bind (hFL rfl lf lf' hrel) ?_
        rintro ⟨s1, a1⟩ ⟨z, hz, hRT, hXz⟩
        refine (WP.spec_ok _).2 ?_
        exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_fault hmF (mem_when (fun _ => hz) (fun h => by cases h))),
          Or.inl ⟨rfl, rfl⟩, hRT, ifP_ok rfl hXz⟩
  | Ok r1 =>
    cases e with
    | error lf' => exact hrel.elim
    | ok v =>
      obtain ⟨sl, rest⟩ := v
      obtain ⟨hsl, -⟩ := hrel
      obtain ⟨p, hp, hth, -⟩ := hok
      obtain ⟨c, a, hc, hca, hget⟩ := hCR.1.slot_cap hp hth
      have hl : (Fl4Spec.lookupCapAndSlot (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ =
          ({(.ok (a, sl), σ)}, False) := by
        unfold Fl4Spec.lookupCapAndSlot
        rw [run_bind_ok he]
        simp only
        rw [run_bind_ok (run_liftE hget)]
        rfl
      simp only
      rw [slot_cap_eq, hsl, hc]
      simp only [bind_ok, hbuf, hr2]
      rcases hrr with ⟨ex, exs, rfl, rfl⟩ | ⟨f, f', rfl, rfl, hfh⟩
      · simp only
        rw [msgLen_eq]; simp only [bind_ok]
        have hca' : absCap c = a := hca.2
        subst hca'
        have hmF := hiMF_ok (mi := mi) hl hbuffer her
        have hmE := hiME_run (cptr := Fl4Spec.toBl cptr.bv) (fp := first_phase) (a := absCap c) (sl := sl)
          (exs := exs) hmrs
        rcases hDec sl c ex exs ⟨p, hp, hth⟩ hc hget rfl rfl with hD | hD
        swap
        · refine WP.spec_bind hD ?_
          rintro ⟨r3, s1, a1⟩ (⟨e3, he3, hs1, ⟨e', hdec, herr⟩, hXe⟩ | ⟨hok3, hne, inv, hdec, σ1, hst, rr, σy, hy, z, hz, hRT, hXz⟩)
          · simp only at he3 hs1
            subst he3 hs1
            cases e3 with
            | Sys e2 =>
              refine WP.spec_mono (hRepF a1 e2 e' hXe herr) ?_
              rintro res ⟨hres, z, hz, hRT, hXz⟩
              exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_err hmF (by rw [hmE, hdec]; rfl) hz),
                Or.inl ⟨hres, rfl⟩, hRT, ifP_ok hres hXz⟩
            | Fault _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
            | Lookup _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
            | Preempted => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          simp only at hok3; subst hok3
          refine WP.spec_bind (tcb_state_spec' (st := st) s1 ct) ?_
          rintro v rfl
          rw [if_neg hne]
          refine (WP.spec_ok _).2 ?_
          exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_fin hmF (by rw [hmE]; exact hdec.1)
            (hiMFin_ok (by rw [← hcur]; exact hst) hy hz)), Or.inl ⟨rfl, rfl⟩, hRT, ifP_ok rfl hXz⟩
        refine WP.spec_bind hD ?_
        rintro ⟨r3, s1, a1⟩ hq
        rcases hq with ⟨e3, he3, hs1, ⟨e', hdec, herr⟩, hXe⟩ |
            ⟨inv, hdec, σ1, hst, y, hy, ⟨th', G', hcase, hP', hCR', hFI', hDR', hFR'⟩, hXy⟩
        · simp only at he3 hs1
          subst he3 hs1
          cases e3 with
          | Sys e2 =>
            refine WP.spec_mono (hRepF a1 e2 e' (ifP_X (r := .Err (.Sys e2)) (fun h => by cases h) hXe) herr) ?_
            rintro res ⟨hres, z, hz, hRT, hXz⟩
            exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_err hmF (by rw [hmE, hdec]; rfl) hz),
              Or.inl ⟨hres, rfl⟩, hRT, ifP_ok hres hXz⟩
          | Fault _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          | Lookup _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          | Preempted => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
        · rcases hcase with ⟨hok3, hyr⟩ | ⟨hpre, hyr⟩
          · simp only at hok3
            subst hok3
            refine WP.spec_mono (hRepS s1 a1 y.2 ⟨th', G', hP', hCR', hFI', hDR', hFR'⟩ (ifP_X (r := .Ok ()) (fun h => by cases h) hXy)
              (hPK inv σ1 y hst hy)) ?_
            rintro res ⟨hres, z, hz, hRT, hXz⟩
            obtain ⟨y1, y2⟩ := y
            simp only at hyr; subst hyr
            exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_fin hmF (by rw [hmE]; exact hdec.1)
              (hiMFin_ok (by rw [← hcur]; exact hst) hy hz)), Or.inl ⟨hres, rfl⟩, hRT, ifP_ok hres hXz⟩
          · simp only at hpre
            subst hpre
            refine (WP.spec_ok _).2 ?_
            obtain ⟨y1, y2⟩ := y
            simp only at hyr; subst hyr
            exact ⟨(.error (), y2), hi_memR rep hcur hmi (mem_syscall_fin hmF (by rw [hmE]; exact hdec.1)
              (hiMFin_pre (by rw [← hcur]; exact hst) hy)), Or.inr ⟨rfl, rfl⟩,
              ⟨th', G', hP', hCR', hFI', hDR', hFR'⟩, hXy⟩
      · simp only
        have hmF := hiMF_extra_err (cptr := Fl4Spec.toBl cptr.bv) hl hbuffer her
        cases blocking
        · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          exact ⟨(.ok (), σ), hi_memR rep hcur hmi (mem_syscall_fault (z := ((), σ)) hmF
            (mem_when (fun h => by cases h) (fun _ => rfl))), Or.inl ⟨rfl, rfl⟩, hRT0, ifP_ok rfl hX0⟩
        · simp only [↓reduceIte]
          refine WP.spec_bind (hfh rfl) ?_
          rintro ⟨s1, a1⟩ ⟨z, hz, hRT, hXz⟩
          refine (WP.spec_ok _).2 ?_
          exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_fault hmF (mem_when (fun _ => hz) (fun h => by cases h))),
            Or.inl ⟨rfl, rfl⟩, hRT, ifP_ok rfl hXz⟩

end

end

/-! ## The premises -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The premises at the entry state**, each exactly as a J decode takes it (the
kernel-global placement facts `hcw`, `hact2`, `hact3`, `hksO`, `hactK` and
`DomPlaced` are proved from `JAtZ`: JEntryKs). -/
structure JEntryAt (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- [J] no reschedule or switch pending at the invocation (`Entered`). -/
  ni : Entered σ
  /-- [J] the current thread in no ready queue at the invocation (l4v
  `ct_not_in_q`, part of `valid_sched`, under `scheduler_action =
  resume_cur_thread`, `ni`; FL4's `switch_to_thread` dequeues the thread it
  switches to): the Endpoint cap's blocking send blocks it (`sendLeafJ`,
  `JAtZ.sendBlockJ`: P1's `CanBlock.nq` and the spec's `NotQueued`). -/
  ctnq : ∀ d q, σ.curThread ∉ σ.readyQueues d q
  /-- [J] the spec's global references at the invocation (SpecGlob: the IRQ
  node's slots null or notification caps, no cap but a frame cap naming an
  IRQ node CNode or the idle thread; l4v `valid_irq_node`,
  `valid_global_refs`), carried by the deletion loop. -/
  sg : SpecGlob σ
  /-- [J] `hRd0`: at a zero consumed time the current SC's head ready (l4v
  `cur_sc_offset_ready 0`; ScEntryRd's `OffReady.rd0` from `OffReady` at
  the invocation, which `budget_ok_offReady` gives from `OffReady` at
  kernel entry). -/
  rd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
    Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true
  /-- [P] the Thread decode's `hstall'` (the remote stall a no-op, one core). -/
  stall : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [J] the Thread decode's `hFl` (SetFlags): FL4's flags word of every TCB
  of `T` against the spec's `tcb_flags` at the invocation (l4v `tcb_relation`'s
  `tcbFlags`; framed across the caller's restart by `JAtZ.flagsRestart`). -/
  flags : FlagsRel Z.T (L.mem s) σ
  /-- [J] the CNode decode's `hQ` (the endpoint queues' precondition). -/
  epQ : ∀ e, Sched.EpQPre σ e
  /-- [J] the IRQ control decode's `hHA`. -/
  handlers : HandlersActive (L.mem s) (L.ksb s) Z.G
  /-- [J] the IO port control decode's `hPA`. -/
  ports : IoPortsAlloc (L.mem s) (L.ksb s) Z.G
  /-- [P] the IRQ control decode's `hnum`, `hnA` (the IOAPIC count). -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] the IRQ control decode's `hAR`. -/
  archIrq : ArchIrqRel arI ar σ
  /-- [J] the current thread's fault handler is null or an endpoint cap with
  send and grant or grant-reply rights (l4v `valid_objs`' `valid_tcb`, the
  `tcb_cap_cases` entry of `tcb_fault_handler`: `valid_fault_handler`; FL4's
  TCB SetSpace/Configure/SetSchedParams check `valid_fault_handler`
  before installing, a retyped TCB's slots are null, deletion nulls); for a
  fault (`JAtZ.faultHypJZ`: any other cap is a spec `fail`). -/
  vfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler
  /-- [J] the current thread has no fault at the invocation (l4v MCS
  `fault_tcbs_valid_states`: a thread with a fault is not active; the spec
  sets a fault only in `send_fault_ipc`, whose sender then blocks on the
  endpoint or on a reply or goes `Inactive`, and `cancel_ipc` (restart,
  suspend) and the fault reply clear it, `restart_thread_if_no_fault` leaves
  a faulted thread `Inactive`): the Endpoint cap's send is a normal transfer
  (`sendLeafJ2`'s `hnf`). -/
  cnf : ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbFault = none
  /-- [J] a mapped page-table, page-directory or PDPT cap whose table is in
  no set of `Z` (a detype pruned it while the cap still says mapped,
  handoff/vsreach.md): the spec's table of that kind at its address (l4v
  `valid_cap`'s `typ_at` for the cap's table; `valid_objs`) and the table's
  frame 4 KiB-aligned and apart from the sets' objects and the typed heap
  (l4v `pspace_aligned`, `pspace_distinct`: the frame is one spec object, an
  arch object, so no TCB, CNode, endpoint, notification, reply, SC or
  kernel-global word, and no table or pool of the sets); XTopJointVsOff's
  `OffTabOK`, what the Unmap of such a cap reads (`decode_invocation_page_tableJO`). -/
  vsTyp : ∀ y, IsSlot Z.th y → OffTabOK (L := L) Z s σ (capV (L.mem s) y)
  /-- [J] the liveness of FL4's caps at the invocation, at the entry's `JAtZ`
  ghost (XTopJointWJLRestart's `LiveDN`): `LiveJ` (l4v `if_unsafe_then_cap`
  and `if_live_then_nonz_cap` for the debug lists' TCBs; `zombies_final` and
  `cap_removeable` for a zombie's unused slots, a TCB zombie's TCB not
  `live`), `DbgWF` (the debug lists well formed: FL4's TCB debug list, as
  l4v's `valid_objs`/`valid_idle`-style list invariants) and `NullOrig` (a
  null slot carries no original bit: l4v `valid_nullcaps` of `valid_mdb'`).
  The deletion at `WJL` (CNode Revoke/Delete, the IRQ handler's
  SetIRQHandler/ClearIRQHandler, the Thread cap's SetTimeoutEndpoint,
  SetSpace, SetIPCBuffer, Configure and SetSchedParams installs) carries it
  from here across the caller's restart (`WJL.restart`) and the installs'
  inserts (XTopJointWJLIns' `LiveDN.insT`). -/
  live : LiveDN (L := L) Z.th H Cs Z.G s σ
  /-- [J] no non-device frame cap names the null pointer (`FrNZ`; l4v
  `pspace_in_kernel_window` / `cap_refs_in_kernel_window`: a non-device frame
  is RAM, in the kernel window; FL4's `UtW` puts RAM untypeds at or above
  `PPTR_BASE` and a non-device frame is retyped from one): SetIPCBuffer /
  Configure's frame install (`JAtZ.bokInstall`, the spec's `IpcBufCapOK`
  asks the IPC frame's pointer nonzero). -/
  fnz : FrNZ Z.th (L.mem s)
  /-- [J] the free part of every RAM untyped cap reads zero in the spec's
  memory (`UtZero`; l4v `untyped_ranges_zero`: true in reachable states, the
  spec's memory is written only by the IPC-buffer and frame stores (inside
  objects, so off every free part, `freeOut_of_obj`), `freeMemory` and
  `clearMemory`, both zeroing): the frame retype's new pages read zero
  (XTopJointUtEp's `UtFreeZ`, `B` grown at them, UtFrameAdd). The untyped decode runs at the
  entry state; the restart keeps the spec's memory. -/
  urz : UtZero (L.mem s) Z.G σ
  /-- [J] every RAM untyped region misses the 64 cores' node slots
  (XTopJointUtEp's `UtNodesJ`; l4v `kernel_window`/`valid_untyped`: FL4's
  kernel-state block, all `MAX_NODES` = 64 nodes, is static kernel data,
  never untyped memory; `JCovD.ks` names only `Cs`'s nodes): the frame
  retype's new `B` words miss every node (`JAtZ.nodeB`). -/
  utks : UtNodesJ (L.mem s) Z.G (L.ksb s)

/-- **A decode path with no J proof** [W]: the cap's statement at `JAt`
(`JAtPre` if preempted), named. -/
abbrev JCapOpen (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length : U64)
    (c : capability.Cap) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop :=
  XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ lbl length (cslotAddr sl) c blk call don fp
    buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct

/-- **A VT-x cap's decode** (VCPU, EPT, an EPT-mapped frame, an IO port
owned by a VCPU, a TCB's SetEPTRoot) [scope]: outside the semantic scope
(DESIGN §9: the VCPU/EPT invocation families have no functional refinement
yet; P0 covers their extracted core), as ScSignalJ's `SignalRestJHyp`'s
`RunningVM` case: the cap's statement at `JAt`, named. -/
abbrev JVtxScope (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length : U64)
    (c : capability.Cap) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop :=
  XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ lbl length (cslotAddr sl) c blk call don fp
    buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct

/-- The SchedControl path: ScJointStep's `decode_invocation_sched_controlJ`
premises. -/
structure JSchedCPath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length cpu : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (ct : U64) : Prop where
  /-- [P] the platform's timer constants (`TimeAgree`, `min_budget`, `maxTicksToUs`, `ticks_to_us`). -/
  tm : TimeAgree arI
  mb : sporadic.min_budget arI ar ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄
  max : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv
  tu : ∀ v, arI.ticks_to_us ar v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄
  /-- [P] one core (as `JEntryAt.stall`): the cap's core is the current one
  (`decode_configure_refines` needs it; with several cores a SchedControl cap
  of another core is valid, l4v `valid_cap` only bounds its core). -/
  core : cpu = Z.c
  /-- [P] the decode's timer and IPI operations keep `AR`. -/
  arch : syscall.decode_invocation st arI s ar lbl length (cslotAddr sl) (.SchedControl cpu) blk call don fp buf extra
    ⦃ r => ∀ c, AR ar c → AR r.2.2 c ⦄
  /-- [P] ScJointStep's `ScStepP1` (P1-supplied: the debug word kept, `BlkOK` after). -/
  rest : ∀ (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ →
    syscall.decode_invocation st arI s ar lbl length (cslotAddr sl) (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => r.1 = .Ok () → ∀ σ' inv σ1,
        (Fl4Spec.decodeSchedControlInvocationFlags (Z := Unit) slbl (argsU.map UScalar.bv) (excaps.map Prod.fst)).run σ =
          ({(.ok inv, σ)}, False) →
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
        Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv σ1 = ({((), σ')}, False) →
        ScStepP1 (L := L) Z H Cs s r.2.1 ⦄

/-- **The SchedContext invocations through ScJointStep's
`decode_invocation_sched_contextJ`**: Consumed, Bind, UnbindObject (Unbind,
YieldTo and the other labels have their own J decodes: ScJointUnbind,
ScJointYield). -/
def ScJLabel (s : S) (lbl sc : U64) : Prop :=
  lbl = fl4_abi.label.SchedContextConsumed ∨ lbl = fl4_abi.label.SchedContextBind ∨
    lbl = fl4_abi.label.SchedContextUnbindObject

/-- The SchedContext path (`ScJLabel`): ScJointStep's
`decode_invocation_sched_contextJ` premises. The invoked SC's facts are
`JAtZ.scCtxCap`'s, the current thread's schedulability `CurInv`'s. -/
structure JSchedCtxPath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length sc sb : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (ct : U64) : Prop where
  /-- [P] the platform's timer constants (as `JSchedCPath`'s). -/
  tm : TimeAgree arI
  mb : sporadic.min_budget arI ar ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄
  max : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv
  tu : ∀ v, arI.ticks_to_us ar v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄
  /-- [P] the decode's timer and IPI operations keep `AR`. -/
  arch : syscall.decode_invocation st arI s ar lbl length (cslotAddr sl) (.SchedContext sc sb) blk call don fp buf
    extra ⦃ r => ∀ c, AR ar c → AR r.2.2 c ⦄
  /-- [P] ScJointStep's `ScStepP1` (P1-supplied: the debug word kept, `BlkOK` after). -/
  rest : ∀ (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ →
    syscall.decode_invocation st arI s ar lbl length (cslotAddr sl) (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => r.1 = .Ok () → ∀ σ1, (∃ inv σ0,
        (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ =
          ({(.ok inv, σ)}, False) ∧
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) ∧
        Fl4Spec.invokeSchedContext (Z := Unit) inv σ0 = ({([], σ1)}, False)) →
        ScStepP1 (L := L) Z H Cs s r.2.1 ⦄

/-- The SchedContext YieldTo path (ScJointYield's
`decode_invocation_sched_context_yieldJ`): [P] the platform's timer
constants (as `JSchedCtxPath`'s). -/
structure JSchedYieldPath (ar : A) : Prop where
  mb : sporadic.min_budget arI ar ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄
  max : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv
  tu : ∀ v, arI.ticks_to_us ar v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄

/-- The Thread path (a native label): the Thread decode's per-invocation
premises. -/
structure JThreadPath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length p : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop where
  /-- [J] ReadFPU's destination frame (XTopJointReadFpu's `FpuFrameJHyp`: l4v
  `valid_cap` for the first extra cap's frame, at the start: its bytes lie in
  spec user frames; a theorem of `JAtZ`, `JAtZ.fpuFrameJ`). -/
  hFr : lbl = fl4_abi.label.TCBReadFPU → ∀ x0, Aeneas.Std.Array.index_usize extra 0#usize = ok x0 →
    FpuFrameJHyp (L := L) Z s σ x0

/-- The device Untyped path (losfair/FL4#34): XTopJointUt's
`decode_invocation_untypedJ` premises for a device untyped cap, the
invocation from UtDevReset's `JAtZ.jUtRetHypDev`. -/
structure JDevPath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length p sb fi : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop where
  /-- [P] `CONFIG_RETYPE_FAN_OUT_LIMIT` is FL4's 256 (as `JUtPath.fan`). -/
  fan : Fl4Spec.retypeFanOutLimit = 256#64
  /-- [scope] a VT-x object type (14 to 18), as `JUtPath.vtx` (the decode of a
  device cap refuses these types on both sides; `decode_invocation_untypedJ`
  takes the native types only). -/
  vtx : ∀ x, argsU.head? = some x → 14 ≤ x.val → x.val < 19 →
    JVtxScope (L := L) arI AR s ar σ lbl length (.Untyped p sb fi true) blk call don fp buf extra slbl argsU ci sl
      excaps buffer ct
  /-- [P] one core (as `JUtPath.core0`). -/
  core0 : Z.c = 0#u64
  /-- [J] as `JUtPath.bufObj`. -/
  bufObj : BufObjHyp Z.B σ
  /-- [J] as `JUtPath.heapH`. -/
  heapH : ArchFitHyp H σ ∧ RegionUnrefAt (L := L) H Cs D s
  /-- [J] DevJ's `DevApart` at the entry's sets and heap (l4v `valid_untyped` /
  `pspace_no_overlap` for device caps with `valid_global_refs` /
  `kernel_window`: no device untyped range covers a kernel object, a typed-heap
  object or a RAM object, `H`'s objects meeting it lie below its free index, and
  its range lies in one canonical half with a nonzero base, of size bits at
  least 4, l4v `untyped_min_bits`): true from boot by
  the boot checks (e408a625: no device untyped over the kernel image's names;
  9ab17db1: none at the pointer 0; RAM and device physical ranges are
  disjoint; physical memory below `2^47`; boot.rs gives out blocks of at
  least `MIN_UNTYPED` = 4 size bits), kept by retype
  (UtDevRet's `DevApart.retype`: a device child is a sub-range, a new device
  frame lies below the source's new free index). -/
  devApart : DevApart (L := L) Z.th H Z.G Cs s
  /-- [J] UtDevRet's `DevFreeT` (l4v `valid_untyped` for device caps: no spec
  object in a device untyped cap's free part): true from boot (no spec object
  in a device range), kept by retype (DevFree's `DevFree.retype`,
  UtDevUt's `SpecFreeP.retypeU`). -/
  devFree : DevFreeT (L.mem s) Z.G σ
  /-- [J] UtDevDrop's `DevGpm` (l4v `valid_global_refs`: no untyped range
  covers a global kernel object): the spec's global PML4 lies off every
  device untyped cap's range; true from boot (the global PML4 is a static of
  the kernel image, fl4-kernel paging.rs, and the boot check e408a625 skips
  device memory over the image), kept (`x64GlobalPml4` never changes, a
  device child is a sub-range). For the reset of a used device cap
  (UtDevReset's `JAtZ.utDevResetJ`, UtDevDrop's `JAtZ.dropAD`). -/
  devGpm : DevGpm (L.mem s) Z.G σ
  /-- [J] the reset's `VsReachMiss` at the restart's state, as
  `JUtPath.vsReach`, for the device cap's region (UtDevDrop's `JAtZ.dropAD`
  in UtDevReset's `JAtZ.reset_untypedDJ`). Asked only when the cap has no
  descendants (FINDING g7b-2: unguarded it is false). -/
  vsReach : (∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr sl)) → ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1)
  /-- [P] `CONFIG_RESET_CHUNK_BITS` is FL4's 16, as `JUtPath.rcb` (the spec's
  device reset, UtDevDrop's `reset_devX`). -/
  rcb : Fl4Spec.resetChunkBits = 16

end

/-! ## The dispatch and the composition -/

end Fl4Proofs.P3
