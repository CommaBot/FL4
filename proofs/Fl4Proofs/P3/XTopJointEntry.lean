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
  the typed heap (from the lookup, `WalkRel`) passed to `hDec`.
* The premises, by scope (`JEntryHyps` bundles them):
  - `JEntryGlob`: platform [P] and ∀-state facts at the typed heap [J]/[W];
  - `JEntryAt`: facts at the entry state [J];
  - `JPath`: per cap, the facts of exactly that cap's decode path; a cap or
    label with no J proof yet is one named `XCapP` (`JCapOpen`, [W]).
* `decOK_J`: the dispatch on the cap (the table in its docstring).
* `handle_invocation_refinesJ`: the composition.

`JAtZ` is used only through the J decodes, `J.xtop`, `J.curEq` and
`JDelParts.thr.idle`, so changes of `JAtZ`'s fields leave this module alone.
-/
import Fl4Proofs.P3.XTopJointTcb
import Fl4Proofs.P3.XTopJointCnDel
import Fl4Proofs.P3.TopXAll
import Fl4Proofs.P3.XTopJointIpcJ
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
      (∃ f f', r2 = .Err f ∧ er = .error f' ∧ (blocking = true → FaultHypAtMX (L := L) arI X s σ ct f f')))
    (args : List Fl4Spec.Data) (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(args, σ)}, False))
    -- the fault of a failed lookup
    (hFL : blocking = true → ∀ lf lf', LookupFaultRel lf lf' →
      FaultHypAtMX (L := L) arI X s σ ct (.Cap cptr false lf)
        (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) false lf'))
    -- the reply writes
    (hRep : ReplyHypMX (L := L) X rep ct is_call)
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
        refine WP.spec_bind (hFL rfl lf lf' hrel ar hX0) ?_
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
              refine WP.spec_mono (hRep.fail _ a1 σ e2 e' hRT0 hXe herr) ?_
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
            refine WP.spec_mono (hRep.fail _ a1 σ e2 e' hRT0 (ifP_X (r := .Err (.Sys e2)) (fun h => by cases h) hXe) herr) ?_
            rintro res ⟨hres, z, hz, hRT, hXz⟩
            exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_err hmF (by rw [hmE, hdec]; rfl) hz),
              Or.inl ⟨hres, rfl⟩, hRT, ifP_ok hres hXz⟩
          | Fault _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          | Lookup _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          | Preempted => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
        · rcases hcase with ⟨hok3, hyr⟩ | ⟨hpre, hyr⟩
          · simp only at hok3
            subst hok3
            refine WP.spec_mono (hRep.succ s1 a1 y.2 ⟨th', G', hP', hCR', hFI', hDR', hFR'⟩ (ifP_X (r := .Ok ()) (fun h => by cases h) hXy)) ?_
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
          refine WP.spec_bind (hfh rfl ar hX0) ?_
          rintro ⟨s1, a1⟩ ⟨z, hz, hRT, hXz⟩
          refine (WP.spec_ok _).2 ?_
          exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_fault hmF (mem_when (fun _ => hz) (fun h => by cases h))),
            Or.inl ⟨rfl, rfl⟩, hRT, ifP_ok rfl hXz⟩

end

end

/-! ## The premises -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The global premises** (platform, or ∀-state at the typed heap `th`),
each exactly as a J decode takes it. -/
structure JEntryGlob (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  /-- [P] the arch relation's interface (`ARKeep`, `ARMask`). -/
  ari : ARIface arI AR
  /-- [P] the arch operations total. -/
  tot : P0.ArchTotal arI
  /-- [J]/[P] XTopJointDelR's `JDelParts`: the deletion's named steps (its
  own fields tagged there; `live` (`LiveJ` [J]), `recvRep`
  (`RecvReplyLinksHyp` [J]) and `thr.idle` [J] are also used by the IO port
  and Thread decodes). -/
  delParts : JDelParts (L := L) arI AR th
  /-- [P] one domain. -/
  nd : Fl4Spec.numDomains = 1
  /-- [P] the preemption point's platform (`PPPlat`). -/
  pp : PPPlat arI AR
  /-- [P] the interrupt and IO-port layout at every related state of `th`
  (the CNode cleanups). -/
  lay : ∀ (Z' : XSets) s' a' σ', Z'.th = th → XTopAt (L := L) AR Z' s' a' σ' →
    IntLayout th (L.ksb s') ∧ IoLayout th (L.ksb s')
  /-- [W] XTopJoint's `CsGlobal` (the IPC, scheduler, VSpace and CSpace
  steps of the Thread cap and the IRQ/IO-port controls at `XTop`). -/
  csG : CsGlobal (L := L) arI AR th
  /-- [J] the Thread decode's `hA` (`ActReady` at every `WX` state). -/
  actReady : ∀ s a σ G, WX (L := L) AR th s a σ G → Notif.ActReady σ
  /-- [J] the Thread decode's `hBT` (IPC-buffer words). -/
  bufT : ∀ (Z' : XSets) s' a' σ', Z'.th = th → XTopAt (L := L) AR Z' s' a' σ' → BufWordRel Z'.T (L.mem s') σ'
  /-- [J] the Thread decode's `hOK` (l4v `valid_ipc_buffer_cap`). -/
  ipcBufOK : ∀ (Z' : XSets) s' a' σ', Z'.th = th → XTopAt (L := L) AR Z' s' a' σ' → Endp.IpcBufCapOK σ'
  /-- [J] the Thread decode's `hBC`. -/
  bufCover : ∀ (Z' : XSets) s' a' σ', Z'.th = th → XTopAt (L := L) AR Z' s' a' σ' → Endp.BufCover Z'.T Z'.B σ'
  /-- [J] the Thread decode's `hBPl`. -/
  bufPlaced : ∀ (Z' : XSets) s' a' σ', Z'.th = th → XTopAt (L := L) AR Z' s' a' σ' →
    Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ'
  /-- [J] the Thread decode's `hFl` (the TCB flags). -/
  flags : ∀ (Z' : XSets) s' a' σ', Z'.th = th → XTopAt (L := L) AR Z' s' a' σ' → FlagsRel Z'.T (L.mem s') σ'
  /-- [J] the IRQ handler decode's `FinObjHyp` (DelRound). -/
  finObj : FinObjHyp (L := L) arI th
  /-- [J] the IRQ handler decode's `PostDelHyp` (DelRound). -/
  postDel : PostDelHyp (L := L) arI th
  /-- [J] the IRQ handler decode's `NtfnKeepHyp` (DelOne). -/
  ntfnKeep : NtfnKeepHyp (L := L) arI th
  /-- [P] the domain configuration (`DomConfig`). -/
  dom : DomConfig
  /-- [P] the port-in values (`PortInVal`, the IO port decode for a call). -/
  portIn : PortInVal arI
  /-- [J] ScSignalJ's `SignalRestJHyp` (a notification's bound thread
  `RunningVM`: FL4's remote stall, VT-x, outside the spec model), at every
  `P1.Heap` and set of cores as `JDelParts.recvRep`: the notification cap's
  `send_signal` (`notifLeafJ`). -/
  sigRest : ∀ (H : P1.Heap) (Cs : Set U64), SignalRestJHyp (L := L) arI AR H Cs

/-- **The premises at the entry state**, each exactly as a J decode takes it. -/
structure JEntryAt (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- [J] no reschedule or switch pending at the invocation (`Entered`). -/
  ni : Entered σ
  /-- [J] `hRd0`: at a zero consumed time the current SC's head ready (l4v
  `cur_sc_offset_ready 0`; ScEntryRd's `OffReady.rd0` from `OffReady` at
  the invocation, which `budget_ok_offReady` gives from `OffReady` at
  kernel entry). -/
  rd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
    Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true
  /-- [P] the Thread decode's `hstall'` (the remote stall a no-op, one core). -/
  stall : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [J] the Thread decode's `hcw` (the current-thread word outside objects). -/
  cw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
  /-- [J] the CNode decode's `hQ` (the endpoint queues' precondition). -/
  epQ : ∀ e, Sched.EpQPre σ e
  /-- [J] the CNode decode's `hE` (an endpoint cap's object in `E`). -/
  epE : ∀ (Z' : XSets) (e b : U64) (sl : Fl4Spec.CslotPtr), XTopAt (L := L) AR Z' s ar σ → AbsSlot Z.th sl →
    capV (L.mem s) (cslotAddr sl) = .Endpoint e b true true true true → e ∈ Z'.E
  /-- [J] the IRQ control decode's `hHA`. -/
  handlers : HandlersActive (L.mem s) (L.ksb s) Z.G
  /-- [J] the IO port control decode's `hPA`. -/
  ports : IoPortsAlloc (L.mem s) (L.ksb s) Z.G
  /-- [J] the IRQ control decode's `hact2`. -/
  act2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i
  /-- [J] the IO port control decode's `hact3`. -/
  act3 : ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w
  /-- [J] the domain decode's `hksO`. -/
  ksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects Z.th (ksW (L.ksb s) o)
  /-- [J] the domain decode's `hactK`. -/
  actK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val
  /-- [J] the IRQ handler decode's `hD`. -/
  domPl : DomPlaced (L := L) Z.th s
  /-- [P] the IRQ control decode's `hnum`, `hnA` (the IOAPIC count). -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] the IRQ control decode's `hAR`. -/
  archIrq : ArchIrqRel arI ar σ

/-- **A decode path with no J proof** [W]: the cap's statement at `JAt`
(`JAtPre` if preempted), named. -/
abbrev JCapOpen (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length : U64)
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
  /-- [W] ScYieldTo's `MsgOK` (the `set_consumed` message leaf, `ScExtra`'s). -/
  msg : MsgOK st Z.N Z.T Z.C Z.c
  /-- [W] the front end's label. -/
  hlbl : Fl4Spec.genInvocationType slbl = .schedControlConfigureFlags ↔ lbl = fl4_abi.label.SchedControlConfigureFlags
  /-- [J] the cap's core is the current one (l4v `valid_cap` of the SchedControl cap; one core). -/
  core : cpu = Z.c
  /-- [W] the front end's extra slot (`ExtraRel`); [J] an SC extra cap valid
  (l4v `valid_cap`, its SC's bound TCB back-linked: `sym_refs`) and not the
  idle SC (l4v: no user cap names `idle_sc_ptr`). -/
  hx : ∃ x0, Aeneas.Std.Array.index_usize extra 0#usize = ok x0 ∧ ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst) ∧
    (∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → sb.val < 64) ∧
    (∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p ∈ Z.C ∧ p ≠ 0#u64 ∧
      ∃ x, σ.kheap p.bv = some (.schedContext x (sb.val - Fl4Spec.minSchedContextBits)) ∧
        ∀ t : U64, x.scTcb = some t.bv →
          t ∈ Z.T ∧ ∃ xt, σ.kheap t.bv = some (.tcb xt) ∧ xt.tcbSchedContext = some p.bv) ∧
    (∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p.bv ≠ Fl4Spec.idleScPtr)
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

/-- The CNode path [W] (the front end's label and extra slots). -/
structure JCnodePath (Z : XSets) (s : S) (lbl : U64) (slbl : Fl4Spec.Data) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) : Prop where
  hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl
  hex : ∃ x0 x1, Aeneas.Std.Array.index_usize extra 0#usize = ok x0 ∧
    Aeneas.Std.Array.index_usize extra 1#usize = ok x1 ∧ ExtraRel2 Z.th (L.mem s) x0 x1 (excaps.map Prod.fst)

/-- The Thread path (a native label): the Thread decode's per-invocation
premises. -/
structure JThreadPath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length p : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop where
  /-- [W] the front end's label. -/
  hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl
  /-- [W] the front end's extension label. -/
  hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl
  /-- [W] the front end's extra slots (`XcRel`); [J] `NcHyp`, the untyped
  extra cap's children (`NoChildrenRel`), an SC extra cap's object in `C`. -/
  hx : ∃ x0 x1 x2, Aeneas.Std.Array.index_usize extra 0#usize = ok x0 ∧
    Aeneas.Std.Array.index_usize extra 1#usize = ok x1 ∧ Aeneas.Std.Array.index_usize extra 2#usize = ok x2 ∧
    XcRel Z.th (L.mem s) x0 x1 x2 excaps ∧ NcHyp (st := st) s σ x0 x1 x2 ∧
    (∀ sl : Fl4Spec.CslotPtr, x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl) ∧
    (x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
  /-- [W] the front end's argument 5 (`ArgRel`). -/
  hA5 : ArgRel (st := st) s σ ct buf buffer 5
  /-- [J] TcbExt's `GetBpHyp`. -/
  hGb : GetBpHyp (st := st) s ct p
  /-- [W] XTopTcbRest's `TcbXIpc` (the IPC steps of the Thread cap). -/
  hI : TcbXIpc (L := L) arI AR Z.th s ar σ p ct buf argsU blk call don
  /-- [W] XTopTcbFpu's `FpuFrameXHyp` (the FPU frame). -/
  hFr : ∀ (x ptr offset r : U64) (sz : capability.FrameSize) (m ep : Bool) (asid va : U64),
    capV (L.mem s) x = .Frame ptr sz r false m ep asid va → FpuPass true offset r sz →
    FpuFrameXHyp (L := L) AR Z p (core.num.U64.wrapping_add ptr offset)
  /-- [W] the labels still open at `JAt` (`TcbJOpen`): XTopJointStep's
  `JPostHyp` per label. -/
  hR : TcbJOpen lbl → JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl) (.Thread p) blk call don fp buf
    extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct

/-- The IRQ control path [W] (the front end's labels and extra slot). -/
structure JIrqCPath (Z : XSets) (s : S) (lbl : U64) (slbl : Fl4Spec.Data) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) : Prop where
  hlbl : IrqCLabel lbl slbl
  hrm : decide (lbl.val = 72) = Fl4Spec.isFl4RemappedLabel slbl
  hex : ∃ x0, Aeneas.Std.Array.index_usize extra 0#usize = ok x0 ∧ ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst)

/-- The IO port control path [W] (the front end's label and extra slot). -/
structure JIoCPath (Z : XSets) (s : S) (lbl : U64) (slbl : Fl4Spec.Data) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) : Prop where
  hlbl : lbl.val = 63 ↔ Fl4Spec.invocationType slbl = .archInvocationLabel .x64IOPortControlIssue
  hex : ∃ x0, Aeneas.Std.Array.index_usize extra 0#usize = ok x0 ∧ ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst)

/-- The IRQ handler path. -/
structure JIrqHPath (Z : XSets) (s : S) (lbl : U64) (slbl : Fl4Spec.Data) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (ct irq : U64) : Prop where
  /-- [W] the front end's label. -/
  hlbl : Fl4Spec.genInvocationType slbl = irqHLabelOf lbl
  /-- [J] IrqHandler's `IrqSlotOK` at the IRQ's node slot. -/
  hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq)
  /-- [W] the front end's extra slot (SetNotification); [J] it is not the
  IRQ's node slot. -/
  hex : ∃ x0, Aeneas.Std.Array.index_usize extra 0#usize = ok x0 ∧
    (lbl.val = 35 → ExtraSRel Z.th (L.mem s) x0 excaps) ∧ (lbl.val = 35 → x0 ≠ nodeA (L.ksb s) irq)
  /-- [J] IrqDom's `IrqDelP1`. -/
  hP1 : IrqDelP1 (L := L) s ct irq

/-- The domain path [W] (the front end's label and extra slot). -/
structure JDomPath (Z : XSets) (s : S) (lbl : U64) (slbl : Fl4Spec.Data) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) : Prop where
  hlbl : Fl4Spec.genInvocationType slbl = domLabelOf lbl
  hex : ∃ x0, Aeneas.Std.Array.index_usize extra 0#usize = ok x0 ∧ ExtraSRel Z.th (L.mem s) x0 excaps

/-- **Per cap, the premises of its decode path** (`decOK_J`'s table). -/
def JPath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : capability.Cap → Prop
  | .Null | .Zombie .. | .Notification .. => True
  | .Endpoint p b sd _ g gr => ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      sd = true → JSendRestHyp (L := L) arI AR s1 ar σ1 blk call b g gr don ct p
  | .Reply p g => ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      JReplyRestHyp (L := L) arI AR s1 ar σ1 ct p g
  | .CNode .. => JCnodePath (L := L) Z s lbl slbl extra excaps
  | .Thread p =>
      (lbl = fl4_abi.label.TCBSetEPTRoot →
        JCapOpen (L := L) arI AR s ar σ lbl length (.Thread p) blk call don fp buf extra slbl argsU ci sl excaps buffer
          ct) ∧
      (lbl ≠ fl4_abi.label.TCBSetEPTRoot →
        JThreadPath (L := L) arI AR Z s ar σ lbl length p blk call don fp buf extra slbl argsU ci sl excaps buffer ct)
  | .IoPort first last z =>
      (z = 0#u64 → PortLabel lbl slbl) ∧
      (z ≠ 0#u64 → JCapOpen (L := L) arI AR s ar σ lbl length (.IoPort first last z) blk call don fp buf extra slbl
        argsU ci sl excaps buffer ct)
  | .IrqControl => JIrqCPath (L := L) Z s lbl slbl extra excaps
  | .IoPortControl => JIoCPath (L := L) Z s lbl slbl extra excaps
  | .IrqHandler irq => JIrqHPath (L := L) Z s lbl slbl extra excaps ct irq
  | .Domain => JDomPath (L := L) Z s lbl slbl extra excaps
  | .SchedControl cpu => JSchedCPath (L := L) arI AR Z s ar σ lbl length cpu blk call don fp buf extra slbl argsU sl
      excaps ct
  | c => JCapOpen (L := L) arI AR s ar σ lbl length c blk call don fp buf extra slbl argsU ci sl excaps buffer ct

end

/-! ## The dispatch and the composition -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **Every cap's statement at `JAt`** (`JAtPre` if preempted), by dispatch
on the cap:

| cap | from | still named (`JPath`) |
|---|---|---|
| Null, Zombie | the decode fails, the state unchanged | — |
| Notification | `decode_notificationDMX`, `notifLeafJ` | — (`SignalRestJHyp` [J] in `JEntryGlob`) |
| Reply | `decode_replyDMX`, `replyLeafJ` | `JReplyRestHyp` (the rest after `reply_remove`) [W] |
| Endpoint | `decode_endpointDMX`, `sendLeafJ` | `JSendRestHyp` (a blocking send, or one to a receiver) [W] |
| CNode | `decode_invocation_cnodeJ_steps` | `JCnodePath` (front end) |
| Thread | `decode_invocation_threadJ_step` | `JThreadPath` (incl. `JPostHyp` at `TcbJOpen`); SetEPTRoot whole [W] |
| IO port | `decode_invocation_ioportJ` | `PortLabel`; a nonzero third field whole [W] |
| IRQ control, IO port control, IRQ handler, Domain | `decode_invocation_{irq_control,ioport_control,irq_handler,domain}J` | `JIrqCPath`, `JIoCPath`, `JIrqHPath`, `JDomPath` |
| SchedControl | `decode_invocation_sched_controlJ` | `JSchedCPath` |
| SchedContext, Untyped, Frame, PageTable, PageDirectory, PDPT, PML4, ASID control, ASID pool, VCPU, EPT | — | `JCapOpen` [W] |
-/
theorem decOK_J [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (lbl length : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length))
    (c : capability.Cap) (hc : capAt (L.mem s) (cslotAddr sl) = ok c)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hN : JPath (L := L) arI AR Z s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ lbl length (cslotAddr sl) c blk call
      don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  have hX0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hPre : ∀ s a σ, JAt (L := L) arI AR s a σ → JAtPre (L := L) arI AR s a σ := fun _ _ _ h => Or.inl h
  obtain ⟨σ1, hst⟩ := XTop.restart (L := L) (show XTop (L := L) AR s ar σ from ⟨Z, J.xtop⟩)
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨p, hp, hth⟩ := hsl; exact ⟨p, hp, Or.inl hth⟩
  have hsc : capV (L.mem s) (cslotAddr sl) = c := capV_of_capAt hc
  have hUt := delUtHyp_of_live arI hG.delParts.live
  have hni := hE.ni
  cases c
  case Null =>
    refine XCap.toP arI (Or.inl ?_) hPre
    unfold DecOKDMX syscall.decode_invocation
    rw [hct]; simp only [bind_ok, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩
  case Zombie p zt n =>
    refine XCap.toP arI (Or.inl ?_) hPre
    unfold DecOKDMX syscall.decode_invocation
    rw [hct]; simp only [bind_ok, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩
  case Endpoint p b sd rv g gr =>
    exact XCap.toP arI (Or.inl (decode_endpointDMX arI _ s ar σ lbl length _ p b sd rv g gr blk call don fp buf extra
      slbl _ ci sl excaps buffer ct hct hX0 hst fun hsd => sendLeafJ J hni hct hAs hc hst blk call g gr don
        (fun s1 σ1' h1 h2 => hN s1 σ1' h1 h2 hsd) hX0)) hPre
  case Notification p b sd rv =>
    exact XCap.toP arI (Or.inl (decode_notificationDMX arI _ s ar σ lbl length _ p b sd rv blk call don fp buf extra
      slbl _ ci sl excaps buffer ct hct hX0 hst fun _ => notifLeafJ hG.tot (hG.sigRest H Cs) (hG.delParts.recvRep H Cs)
        hG.pp.minBudget J hni hct hAs hc hst hX0)) hPre
  case Reply p g =>
    exact XCap.toP arI (Or.inl (decode_replyDMX arI _ s ar σ lbl length _ p g blk call don fp buf extra slbl _ ci sl
      excaps buffer ct hct hst (replyLeafJ hG.tot J hni hct hAs hc hst hN hX0))) hPre
  case CNode p r gs g =>
    have hN : JCnodePath (L := L) Z s lbl slbl extra excaps := hN
    obtain ⟨x0, x1, hx0, hx1, hex⟩ := hN.hex
    exact decode_invocation_cnodeJ_steps arI s ar σ J hni hG.ari hG.tot hG.delParts hG.nd hG.pp hE.rd0 hG.lay lbl
      slbl hN.hlbl length buf ct hct argsU hlen hargs sl hAs p r gs g hsc extra x0 x1 hx0 hx1 excaps hex hE.epQ
      hE.epE blk call don fp ci buffer
  case Thread p =>
    obtain ⟨hEpt, hN⟩ := hN
    by_cases hn : lbl = fl4_abi.label.TCBSetEPTRoot
    · exact hEpt hn
    obtain ⟨hlbl, hext, ⟨x0, x1, x2, hx0, hx1, hx2, hXc, hnc, hnc0, hcapC⟩, hA5, hGb, hI, hFr, hR⟩ := hN hn
    have hpI : p ≠ L.idleW s :=
      (hG.delParts.thr.idle Z H Cs Ac Lst D s ar σ rfl J _ p hAs.isSlot hsc).symm
    exact (decode_invocation_threadJ_step arI s ar σ J hni hG.csG hG.ari hG.tot hG.actReady hG.bufT hG.ipcBufOK
      hG.bufCover hG.bufPlaced hG.flags lbl length p blk call don fp buf extra ct hct slbl hlbl argsU hlen hargs ci sl
      hAs hsc excaps buffer hext hE.stall hn hE.cw hpI x0 x1 x2 hx0 hx1 hx2 hXc hnc hnc0 hcapC hA5 hGb hI hFr
      hG.delParts.recvRep hG.pp.minBudget hR).toP arI hPre
  case IoPort first last z =>
    obtain ⟨hz, hOpen⟩ := hN
    by_cases h0 : z = 0#u64
    · subst h0
      exact (decode_invocation_ioportJ arI s ar σ J hni hG.ari hG.tot hG.delParts.live lbl slbl (hz rfl) length buf ct
        hct argsU hlen hargs sl hAs first last hsc call (fun _ => hG.portIn) blk don fp extra ci excaps buffer).toP
        arI hPre
    · exact hOpen h0
  case IrqControl =>
    have hN : JIrqCPath (L := L) Z s lbl slbl extra excaps := hN
    obtain ⟨x0, hx0, hex⟩ := hN.hex
    obtain ⟨nA, hnum, hnA⟩ := hE.ioapics
    obtain ⟨sl1, idxs⟩ := sl
    obtain ⟨p0, hp0, hth0⟩ := hsl
    try simp only at hp0 hth0
    subst hp0
    exact (decode_invocation_irq_controlJ arI s ar σ J hni hG.csG hG.ari hG.tot hUt hE.handlers lbl slbl hN.hlbl
      hN.hrm length buf ct hct argsU hlen hargs hE.act2 extra x0 hx0 excaps hex hth0 rfl hc nA hnum hnA hE.archIrq
      blk call don fp ci buffer).toP arI hPre
  case IoPortControl =>
    have hN : JIoCPath (L := L) Z s lbl slbl extra excaps := hN
    obtain ⟨x0, hx0, hex⟩ := hN.hex
    obtain ⟨sl1, idxs⟩ := sl
    obtain ⟨p0, hp0, hth0⟩ := hsl
    try simp only at hp0 hth0
    subst hp0
    exact (decode_invocation_ioport_controlJ arI s ar σ J hni hG.csG hG.ari hG.tot hUt hE.ports lbl slbl hN.hlbl
      length buf ct hct argsU hlen hargs hE.act3 extra x0 hx0 excaps hex hth0 rfl hc blk call don fp ci
      buffer).toP arI hPre
  case IrqHandler irq =>
    have hN : JIrqHPath (L := L) Z s lbl slbl extra excaps ct irq := hN
    obtain ⟨x0, hx0, hex, hxn⟩ := hN.hex
    exact (decode_invocation_irq_handlerJ arI s ar σ J hni hG.csG hG.ari hG.tot hUt hG.finObj hG.postDel hG.ntfnKeep
      lbl slbl hN.hlbl ct hct sl hAs irq hsc hN.hok extra x0 hx0 excaps hex hxn hE.domPl hN.hP1 length buf blk call
      don fp _ ci buffer).toP arI hPre
  case Domain =>
    have hN : JDomPath (L := L) Z s lbl slbl extra excaps := hN
    obtain ⟨x0, hx0, hex⟩ := hN.hex
    exact (decode_invocation_domainJ arI hG.dom s ar σ J hni hG.ari hUt ct hct hE.ksO hE.actK lbl slbl hN.hlbl length
      buf argsU hlen hargs extra x0 hx0 excaps hex _ blk call don fp ci sl buffer).toP arI hPre
  case SchedControl cpu =>
    have hN : JSchedCPath (L := L) arI AR Z s ar σ lbl length cpu blk call don fp buf extra slbl argsU sl excaps ct := hN
    obtain ⟨x0, hx0, hex, hsb, hsc0, hpi⟩ := hN.hx
    exact (decode_invocation_sched_controlJ s ar σ J hni hN.tm hN.mb hN.max hN.tu hN.msg lbl slbl hN.hlbl cpu length
      buf ct hN.core hct argsU hlen hargs extra x0 hx0 excaps hex hsb hsc0 hpi (cslotAddr sl) blk call don fp ci sl
      buffer hN.arch (hN.rest H Cs Ac Lst D J)).toP arI hPre
  all_goals exact hN

/-- **The premises of one invocation at `J`** (`handle_invocation_refinesJ`):
the global ones, those at the entry state, the front end's argument words,
the reply and fault handler at `JAt`, and per cap its decode path. -/
structure JEntryHyps (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64)
    (rep is_call blocking can_donate first_phase : Bool) (cptr : U64) (info : msginfo.MessageInfo)
    (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef) (argsU : List U64)
    (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
    (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) : Prop where
  /-- `JEntryGlob` ([P]/[J]/[W] per field). -/
  glob : JEntryGlob (L := L) arI AR Z.th
  /-- `JEntryAt` ([J]/[P] per field). -/
  atE : JEntryAt (L := L) arI AR Z s ar σ
  /-- [W] the front end: the message's words (the spec's `getMrs`) are FL4's
  `syscall_arg`s, as many as FL4's `msgLen`. -/
  len : (msgLen info buf).val = argsU.length
  args : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x
  /-- [W] HandleTopX's `ReplyHypMX` at `JAt`: the success tail for an empty
  result and the error reply keep `JAt` (XTopJointReply's `jReplyHyp`
  proves `reply1` at `J`; not yet bridged to `flTail`). -/
  reply : ReplyHypMX (L := L) (JAt (L := L) arI AR) rep ct is_call
  /-- [W] the fault handler at `JAt` for a failed cap lookup. -/
  lookupFault : blocking = true → ∀ lf lf', LookupFaultRel lf lf' →
    FaultHypAtMX (L := L) arI (JAt (L := L) arI AR) s σ ct (.Cap cptr false lf)
      (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) false lf')
  /-- [W] the extra caps' lookup: both succeed, or both fault with the
  fault handler at `JAt`. -/
  extraLookup : (∃ e exs, r2 = .Ok e ∧ er = .ok exs) ∨
    (∃ f f', r2 = .Err f ∧ er = .error f' ∧ (blocking = true → FaultHypAtMX (L := L) arI (JAt (L := L) arI AR) s σ ct f f'))
  /-- Per cap, its decode path (`JPath`). -/
  path : ∀ (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
    (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
    capAt (L.mem s) (cslotAddr sl) = ok c → Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) →
    r2 = .Ok e → er = .ok exs →
    JPath (L := L) arI AR Z s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
      mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

set_option maxHeartbeats 4000000 in
/-- **One invocation at `J`**: from `JAtZ` at entry, FL4's
`handle_invocation` refines the spec's `fl4HandleInvocationR`, with `JAt`
after (`JAtPre` after a preempted invocation), from `JEntryHyps`. The front
end's reads are the equations of `handle_invocation_refinesMX`. -/
theorem handle_invocation_refinesJ [Fl4Proofs.P1.PlainStore st] (rep : Bool) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64)
    (info : msginfo.MessageInfo) (hinfo : msg.msg_info st s ct = ok info)
    (mi : Fl4Spec.MessageInfo) (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    (buf : U64) (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf)
    (buffer : Option Fl4Spec.ObjRef)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
    (hr2 : ipc.lookup_extra_caps st s ct buf info = ok r2)
    (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr)))
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False))
    (argsU : List U64)
    (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(argsU.map UScalar.bv, σ)}, False))
    (hH : JEntryHyps (L := L) arI AR Z s ar σ ct rep is_call blocking can_donate first_phase cptr info mi buf buffer
      argsU r2 er) :
    syscall.handle_invocation st arI s ar is_call blocking can_donate first_phase cptr ⦃ res =>
      HIPostMXP (L := L) (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) rep σ is_call blocking can_donate first_phase
        (Fl4Spec.toBl cptr.bv) res ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (J.xtop.curTcb hcur).1
  have hX := J.xtop
  refine handle_invocation_refinesMXP arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) rep s ar σ Z.th Z.G
    hX.rel.1 hX.rel.2.1 hX.rel.2.2.1 hX.rel.2.2.2.1 hX.rel.2.2.2.2.1 ⟨Z, H, Cs, Ac, Lst, D, J⟩ ct hct hcur htcb
    is_call blocking can_donate first_phase cptr info hinfo mi hmi buf hbuf buffer hbuffer r2 hr2 er her
    hH.extraLookup (argsU.map UScalar.bv) hmrs hH.lookupFault hH.reply ?_
  intro sl c e exs hsl hc hget h1 h2
  exact decOK_J arI s ar σ J hH.glob hH.atE ct hct info.label (msgLen info buf) blocking is_call can_donate first_phase
    buf e mi.miLabel argsU hH.len hH.args (Fl4Spec.toBl cptr.bv) sl hsl c hc exs buffer
    (hH.path sl c e exs hsl hc hget h1 h2)

end

end Fl4Proofs.P3
