/-
P3 (DESIGN.md §9): **`handle_invocation` with an extra relation `X`**
(`handle_invocation_refinesMX`), parallel to TopM's
`handle_invocation_refinesM`, for relations the CSpace one does not cover
(the IPC relation, the VSpace relations).

* `TopPostDMX` / `DecOKDMX`: `TopPostDM` with `X` on the outcome, and the
  invocation's spec result `[]` on success: an invocation that returns data
  replies itself (`DecOKRMX`, FL4 writing the reply registers and setting
  `Running`), so only an empty result reaches FL4's success tail
  (`reply_success_empty`). `DecOKDMX.ofDM` gives it from `DecOKDM` and the
  decode's `rr = []` (for `X` true).
* `ReplyHypMX`: `ReplyHypM` keeping `X`, its success tail for `rr = []` only,
  its error reply against `fl4ReplyFromKernelError rep` (Ext/ReplyError:
  with `rep`, FL4's `KERNEL_INVOCATION_REPORT_ERROR_IPC`, the debug word);
  `handle_invocation_refinesMX` is against `fl4HandleInvocationR rep`, which
  is `fl4HandleInvocation` for `rep` false.
* `FaultHypAtMX`, `HIPostMX`, with the projections `TopPostDMX.toDM`,
  `HIPostMX.toM`, `ReplyHypM.toX`.
-/
import Fl4Proofs.P3.VsDecReply
import Fl4Spec.Ext.ReplyError
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`TopPostDM` with `X` on the outcome and an empty result.** -/
def TopPostDMX (X : S → A → Fl4Spec.State Unit → Prop) (σ : Fl4Spec.State Unit) (blk call don : Bool)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation) (s : S) (res : core.result.Result Unit error.Exc × S × A) :
    Prop :=
  (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ (∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∧
    X res.2.1 res.2.2 σ) ∨
  (∃ inv, DecOut m σ inv ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1, (∃ th' G',
      ((res.1 = .Ok () ∧ y.1 = .ok []) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
      Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
      DomRel (L.mem res.2.1) (L.ksb res.2.1) y.2 ∧ MdbOKV (L.ksb res.2.1) (L.mem res.2.1) G') ∧
      X res.2.1 res.2.2 y.2)

theorem TopPostDMX.toDM {X : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostDMX (L := L) X σ blk call don m s res) : TopPostDM (L := L) σ blk call don m s res := by
  rcases h with ⟨e, h1, h2, h3, -⟩ | ⟨inv, h1, σ1, h2, y, hy, ⟨th', G', h3, h4⟩, -⟩
  · exact Or.inl ⟨e, h1, h2, h3⟩
  · refine Or.inr ⟨inv, h1, σ1, h2, y, hy, th', G', ?_, h4⟩
    rcases h3 with ⟨a, b⟩ | h
    · exact Or.inl ⟨a, [], b⟩
    · exact Or.inr h

/-- `TopPostDM` with an empty result on success is `TopPostDMX` for `X`
true. -/
theorem TopPostDMX.ofDM {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostDM (L := L) σ blk call don m s res)
    (hnil : ∀ inv, DecOut m σ inv → ∀ σ1 y, y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1 →
      ∀ rr, y.1 = .ok rr → rr = []) :
    TopPostDMX (L := L) (fun _ _ _ => True) σ blk call don m s res := by
  rcases h with ⟨e, h1, h2, h3⟩ | ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4⟩
  · exact Or.inl ⟨e, h1, h2, h3, trivial⟩
  · refine Or.inr ⟨inv, h1, σ1, h2, y, hy, ⟨th', G', ?_, h4⟩, trivial⟩
    rcases h3 with ⟨a, rr, b⟩ | h
    · exact Or.inl ⟨a, by rw [b, hnil inv h1 σ1 y hy rr b]⟩
    · exact Or.inr h

/-- **`DecOKDM` with `X` and an empty result.** -/
abbrev DecOKDMX (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length slot : U64) (c : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    TopPostDMX (L := L) X σ blk call don (specDec fp slbl args ci sl c excaps buffer) s res ⦄

/-- **The reply writes keeping `X`**: the success tail for an empty result,
and the error reply. -/
structure ReplyHypMX (X : S → A → Fl4Spec.State Unit → Prop) (rep : Bool) (ct : U64) (is_call : Bool) : Prop where
  succ : ∀ (s1 : S) (a1 : A) (σ' : Fl4Spec.State Unit), RelTopM (L := L) s1 σ' → X s1 a1 σ' →
    flTail (st := st) ct is_call s1 a1 ⦃ res => res.1 = .Ok () ∧
      ∃ z ∈ (specTail is_call ct.bv [] σ').1, RelTopM (L := L) res.2.1 z.2 ∧ X res.2.1 res.2.2 z.2 ⦄
  fail : ∀ (s1 : S) (a1 : A) (σ' : Fl4Spec.State Unit) (e : error.SysError) (e' : Fl4Spec.SyscallError),
    RelTopM (L := L) s1 σ' → X s1 a1 σ' → ErrRel (.Sys e) e' →
    ((if is_call then do
        let s2 ← syscall.reply_error st s1 ct e
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)
      else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s1, a1)) :
      Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ res =>
      res.1 = .Ok () ∧ ∃ z ∈ ((Fl4Spec.NonDet.when is_call <|
        Fl4Spec.fl4ReplyFromKernelError rep ct.bv (Fl4Spec.msgFromSyscallError e')) σ').1,
        RelTopM (L := L) res.2.1 z.2 ∧ X res.2.1 res.2.2 z.2 ⦄

/-- `ReplyHypM` is `ReplyHypMX` for `X` true. -/
theorem ReplyHypM.toX {ct : U64} {is_call : Bool} (h : ReplyHypM (L := L) ct is_call (A := A)) :
    ReplyHypMX (L := L) (fun (_ : S) (_ : A) (_ : Fl4Spec.State Unit) => True) false ct is_call :=
  ⟨fun s1 a1 σ' hR _ => WP.spec_mono (h.succ s1 a1 σ' [] hR) fun _ ⟨h1, z, hz, h2⟩ => ⟨h1, z, hz, h2, trivial⟩,
   fun s1 a1 σ' e e' hR _ he => WP.spec_mono (h.fail s1 a1 σ' e e' hR he) fun _ ⟨h1, z, hz, h2⟩ =>
     ⟨h1, z, hz, h2, trivial⟩⟩

/-- **The fault handler keeping `X`.** -/
def FaultHypAtMX (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (σ : Fl4Spec.State Unit) (ct : U64)
    (f : error.Fault) (f' : Fl4Spec.Fault) : Prop :=
  ∀ a : A, X s a σ → faults.handle_fault st arI s a ct f ⦃ r =>
    ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1, RelTopM (L := L) r.1 z.2 ∧ X r.1 r.2 z.2 ⦄

theorem FaultHypAtM.toX {s : S} {σ : Fl4Spec.State Unit} {ct : U64} {f : error.Fault} {f' : Fl4Spec.Fault}
    (h : FaultHypAtM (L := L) arI s σ ct f f') : FaultHypAtMX (L := L) arI (fun _ _ _ => True) s σ ct f f' :=
  fun a _ => WP.spec_mono (h a) fun _ ⟨z, hz, h2⟩ => ⟨z, hz, h2, trivial⟩

/-- **The result of `handle_invocation` with `X`.** -/
def HIPostMX (X : S → A → Fl4Spec.State Unit → Prop) (rep : Bool) (σ : Fl4Spec.State Unit)
    (calling blocking canDonate firstPhase : Bool) (cptr : Fl4Spec.CapRef)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) rep calling blocking canDonate firstPhase cptr).run σ).1,
    ((res.1 = .Ok () ∧ y.1 = .ok ()) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
    RelTopM (L := L) res.2.1 y.2 ∧ X res.2.1 res.2.2 y.2

theorem HIPostMX.toM {X : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit}
    {calling blocking canDonate firstPhase : Bool} {cptr : Fl4Spec.CapRef}
    {res : core.result.Result Unit error.Exc × S × A}
    (h : HIPostMX (L := L) X false σ calling blocking canDonate firstPhase cptr res) :
    HIPostM (L := L) σ calling blocking canDonate firstPhase cptr res := by
  obtain ⟨y, hy, h1, h2, -⟩ := h
  exact ⟨y, hy, h1, h2⟩

/-- `hi_mem` for `fl4HandleInvocationR`. -/
theorem hi_memR {σ : Fl4Spec.State Unit} (rep : Bool) {calling blocking canDonate firstPhase : Bool}
    {cptr : Fl4Spec.CapRef} {mi : Fl4Spec.MessageInfo} {t : Fl4Spec.ObjRef} (hcur : σ.curThread = t)
    (hmi : Fl4Spec.getMessageInfo (Z := Unit) t σ = ({(mi, σ)}, False))
    {y : Except Unit Unit × Fl4Spec.State Unit}
    (h : y ∈ ((Fl4Spec.syscall (hiMF t mi cptr) (fun fault => Fl4Spec.NonDet.when blocking <| Fl4Spec.handleFault t fault)
      (hiME t mi cptr firstPhase)
      (fun err => Fl4Spec.NonDet.when calling <| Fl4Spec.fl4ReplyFromKernelError rep t <|
        Fl4Spec.msgFromSyscallError err)
      (hiMFin t calling blocking canDonate)).run σ).1) :
    y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) rep calling blocking canDonate firstPhase cptr).run σ).1 := by
  unfold Fl4Spec.fl4HandleInvocationR
  refine mem_bindE_ok (a := σ.curThread) (s' := σ) (mem_liftE (x := (σ.curThread, σ)) rfl) ?_
  refine mem_bindE_ok (a := mi) (s' := σ) (mem_liftE (x := (mi, σ)) (by rw [hcur, hmi]; rfl)) ?_
  rw [hcur]
  exact h

/-- **`handle_invocation` refines l4v's, keeping `X`** (`handle_invocation_refinesM`
with `X` threaded through the decode, the reply and the fault handler). -/
theorem handle_invocation_refinesMX (X : S → A → Fl4Spec.State Unit → Prop) (rep : Bool) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (th : TypedHeap) (G : MdbGhost)
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
      (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), capAt (L.mem s) (cslotAddr sl) = ok c →
      Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) → r2 = .Ok e → er = .ok exs →
      DecOKDMX (L := L) arI X s ar σ info.label (msgLen info buf) (cslotAddr sl) c blocking is_call can_donate first_phase
        buf e mi.miLabel args (Fl4Spec.toBl cptr.bv) sl exs buffer ∨
      DecOKRMX (L := L) arI X s ar σ info.label (msgLen info buf) (cslotAddr sl) c blocking is_call can_donate first_phase
        buf e mi.miLabel args (Fl4Spec.toBl cptr.bv) sl exs buffer ct) :
    syscall.handle_invocation st arI s ar is_call blocking can_donate first_phase cptr ⦃ res =>
      HIPostMX (L := L) X rep σ is_call blocking can_donate first_phase (Fl4Spec.toBl cptr.bv) res ⦄ := by
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
          (mem_when (fun h => by cases h) (fun _ => rfl))), Or.inl ⟨rfl, rfl⟩, hRT0, hX0⟩
      · simp only [↓reduceIte]
        refine WP.spec_bind (hFL rfl lf lf' hrel ar hX0) ?_
        rintro ⟨s1, a1⟩ ⟨z, hz, hRT, hXz⟩
        refine (WP.spec_ok _).2 ?_
        exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_fault hmF (mem_when (fun _ => hz) (fun h => by cases h))),
          Or.inl ⟨rfl, rfl⟩, hRT, hXz⟩
  | Ok r1 =>
    cases e with
    | error lf' => exact hrel.elim
    | ok v =>
      obtain ⟨sl, rest⟩ := v
      obtain ⟨hsl, -⟩ := hrel
      obtain ⟨p, hp, hth⟩ := hok
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
        rcases hDec sl c ex exs hc hget rfl rfl with hD | hD
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
                Or.inl ⟨hres, rfl⟩, hRT, hXz⟩
            | Fault _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
            | Lookup _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
            | Preempted => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          simp only at hok3; subst hok3
          refine WP.spec_bind (tcb_state_spec' (st := st) s1 ct) ?_
          rintro v rfl
          rw [if_neg hne]
          refine (WP.spec_ok _).2 ?_
          exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_fin hmF (by rw [hmE]; exact hdec.1)
            (hiMFin_ok (by rw [← hcur]; exact hst) hy hz)), Or.inl ⟨rfl, rfl⟩, hRT, hXz⟩
        refine WP.spec_bind hD ?_
        rintro ⟨r3, s1, a1⟩ hq
        rcases hq with ⟨e3, he3, hs1, ⟨e', hdec, herr⟩, hXe⟩ |
            ⟨inv, hdec, σ1, hst, y, hy, ⟨th', G', hcase, hP', hCR', hFI', hDR', hFR'⟩, hXy⟩
        · simp only at he3 hs1
          subst he3 hs1
          cases e3 with
          | Sys e2 =>
            refine WP.spec_mono (hRep.fail _ a1 σ e2 e' hRT0 hXe herr) ?_
            rintro res ⟨hres, z, hz, hRT, hXz⟩
            exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_err hmF (by rw [hmE, hdec]; rfl) hz),
              Or.inl ⟨hres, rfl⟩, hRT, hXz⟩
          | Fault _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          | Lookup _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          | Preempted => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
        · rcases hcase with ⟨hok3, hyr⟩ | ⟨hpre, hyr⟩
          · simp only at hok3
            subst hok3
            refine WP.spec_mono (hRep.succ s1 a1 y.2 ⟨th', G', hP', hCR', hFI', hDR', hFR'⟩ hXy) ?_
            rintro res ⟨hres, z, hz, hRT, hXz⟩
            obtain ⟨y1, y2⟩ := y
            simp only at hyr; subst hyr
            exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_fin hmF (by rw [hmE]; exact hdec.1)
              (hiMFin_ok (by rw [← hcur]; exact hst) hy hz)), Or.inl ⟨hres, rfl⟩, hRT, hXz⟩
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
            (mem_when (fun h => by cases h) (fun _ => rfl))), Or.inl ⟨rfl, rfl⟩, hRT0, hX0⟩
        · simp only [↓reduceIte]
          refine WP.spec_bind (hfh rfl ar hX0) ?_
          rintro ⟨s1, a1⟩ ⟨z, hz, hRT, hXz⟩
          refine (WP.spec_ok _).2 ?_
          exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_fault hmF (mem_when (fun _ => hz) (fun h => by cases h))),
            Or.inl ⟨rfl, rfl⟩, hRT, hXz⟩

end

end

end Fl4Proofs.P3
