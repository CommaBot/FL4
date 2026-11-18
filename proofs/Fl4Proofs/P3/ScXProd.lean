/-
P3, scheduling contexts: **the SC producers at `XTop`** (`ScXHyp`'s
part): the spec steps of SchedControl Configure, SchedContext Bind,
UnbindObject and a YieldTo from an SC yielded to by none are `ScTKw`-steps
(`tk_setThreadState`, `tk_invokeSchedContext`, the `NKT` lemmas), and with
FL4's `TFoot` writes (`ScFine`) the composite relation is kept
(`xtop_sc_step`).

* `RetP`: every successful outcome of a decode satisfies `P` (the decoded
  invocation's shape, `retP_bindDec`, `retP_unbindObjDec`,
  `retP_yieldToDec`).
* `ScExtra`: the producers' extra premises, a named bundle beside `XTopAt`.
* `decode_invocation_sched_controlXT`: the SchedControl cap, `DecOKDMX` at
  `XTop`.
* `decode_invocation_sched_contextXT`: the SchedContext cap for Bind,
  UnbindObject and YieldTo (yielded to by none): `DecOKDMX` at `XTop` when no
  data is returned, else (a YieldTo returning at once) `DecOKRMX` with `X`
  true.
* The leaves still named, in the `XLeaf` shape: `ScReplyLeaf` (the
  `set_consumed` reply, any target: Consumed's and an at-once YieldTo's to
  the caller, `complete_yield_to`'s to the yielder) and `ScUnbindReplyLeaf`
  (Unbind's `unbind_reply`).

Each producer also takes `hArch`: the decode's run keeps `AR` (the SC
code's `now`, `set_deadline`, `remote_stall` and `send_reschedule` keep the
CR3 relation).
-/
import Fl4Proofs.P3.ScXStep
import Fl4Proofs.P3.ScTopX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

/-! ## The spec steps -/

theorem nkt_schedContextUnbindTcb (p : ObjRef) : NKT (schedContextUnbindTcb (Z := Unit) p) := by
  unfold schedContextUnbindTcb; repeat nkt_step2

theorem nkt_schedContextUnbindNtfn (p : ObjRef) : NKT (schedContextUnbindNtfn (Z := Unit) p) := by
  unfold schedContextUnbindNtfn; repeat nkt_step2

theorem nkt_returnConsumed (p : ObjRef) : NKT (returnConsumed (Z := Unit) p) := by
  unfold returnConsumed schedContextUpdateConsumed; repeat nkt_step2

/-- A runnable state blocks on no IPC object. -/
theorem ipcFree_of_runnable {ts : ThreadState} (h : runnable ts = true) : IpcFree ts := by
  cases ts <;> simp [runnable] at h <;> exact ⟨rfl, rfl, fun _ e => by cases e⟩

/-- **`set_thread_state`** between IPC-free states is a step of the thread. -/
theorem tk_setThreadState {σ : State Unit} {t : ObjRef} {ts : ThreadState} {x : Tcb}
    (hk : σ.kheap t = some (.tcb x)) (h0 : IpcFree x.tcbState) (h1 : IpcFree ts) :
    ∀ y ∈ (setThreadState (Z := Unit) t ts σ).1, ScTKw (fun p => p = t) σ y.2 := by
  intro y ⟨z, hz, hy⟩
  have hz' : ScTKw (fun p => p = t) σ z.2 := by
    obtain ⟨w, hw, hz⟩ := hz
    obtain ⟨hk', hs⟩ := getsThe_getTcb_mem hw
    rw [hs] at hz
    obtain ⟨k, hk'', -, e⟩ := setObject_mem hz
    rw [hk] at hk'; cases hk'
    rw [e]
    exact ScTKw.upd hk (Or.inr (Or.inl ⟨_, _, rfl, rfl, rfl, Or.inr ⟨rfl, h0, h1⟩⟩))
  have hn : NKT (setThreadStateAct (Z := Unit) t) := by
    unfold setThreadStateAct setSchedulerAction; repeat nkt_step2
  exact hz'.trans ((hn _ _ hy).mono fun _ h => h.elim)

/-- **A YieldTo from an SC yielded to by none** changes only scheduling
fields (no `complete_yield_to`, so no reply). -/
theorem nkt_schedContextYieldTo {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (hyf : x.scYieldFrom = none) :
    ∀ y ∈ (schedContextYieldTo (Z := Unit) p σ).1, ScTKw (fun _ => False) σ y.2 := by
  intro y hy
  unfold schedContextYieldTo at hy
  rw [nd_bind_one (getScObjRef_eq hk _), hyf] at hy
  refine (show NKT _ from ?_) σ y hy
  refine nkt_bind ?_ fun _ => ?_
  · unfold NonDet.when; simp only [ne_eq, not_true_eq_false, ↓reduceIte]; exact nkt_pure' _
  unfold returnConsumed schedContextUpdateConsumed
  repeat nkt_step2

theorem ipcFree_restart : IpcFree .restart := ⟨rfl, rfl, fun _ e => by cases e⟩

/-! ## The decoded invocation's shape -/

/-- Every successful outcome of `m` satisfies `P`. -/
def RetP {α : Type} (P : α → Prop) (m : SEMonad Unit α) : Prop :=
  ∀ σ x, x ∈ (m.run σ).1 → ∀ v, x.1 = .ok v → P v

theorem retP_bind {α β : Type} {P : β → Prop} (m : SEMonad Unit α) {f : α → SEMonad Unit β}
    (hf : ∀ a, RetP P (f a)) : RetP P (m >>= f) := by
  intro σ x hx v hv
  rw [ExceptT.run_bind] at hx
  obtain ⟨⟨e, σ'⟩, -, hx⟩ := hx
  cases e with
  | error e => rw [Set.mem_singleton_iff.1 hx] at hv; cases hv
  | ok a => exact hf a σ' x hx v hv

theorem retP_pure {α : Type} {P : α → Prop} {a : α} (h : P a) : RetP P (pure a : SEMonad Unit α) := by
  intro σ x hx v hv
  rw [Set.mem_singleton_iff.1 hx] at hv; cases hv; exact h

theorem retP_throw {α : Type} {P : α → Prop} (e : SyscallError) :
    RetP P (NonDetE.throwError e : SEMonad Unit α) := by
  intro σ x hx v hv
  rw [Set.mem_singleton_iff.1 hx] at hv; cases hv

theorem RetP.of_run {α : Type} {P : α → Prop} {m : SEMonad Unit α} (h : RetP P m) {σ : State Unit} {v : α}
    (hr : m.run σ = ({(.ok v, σ)}, False)) : P v :=
  h σ (.ok v, σ) (by rw [hr]; exact Set.mem_singleton _) v rfl

macro "retp_auto" : tactic => `(tactic| repeat (first
  | exact retP_pure ⟨_, rfl⟩ | exact retP_pure rfl | exact retP_throw _
  | (refine retP_bind _ fun _ => ?_) | split | (dsimp only)))

theorem retP_bindDec (sc : ObjRef) (excaps : List Cap) :
    RetP (fun v => ∃ cap, v = .invokeSchedContextBind sc cap) (decodeSchedContextBind (Z := Unit) sc excaps) := by
  unfold decodeSchedContextBind; retp_auto

theorem retP_unbindObjDec (sc : ObjRef) (excaps : List Cap) :
    RetP (fun v => ∃ cap, v = .invokeSchedContextUnbindObject sc cap)
      (decodeSchedContextUnbindObject (Z := Unit) sc excaps) := by
  unfold decodeSchedContextUnbindObject; retp_auto

theorem retP_yieldToDec (sc : ObjRef) :
    RetP (fun v => v = .invokeSchedContextYieldTo sc) (decodeSchedContextYieldTo (Z := Unit) sc) := by
  unfold decodeSchedContextYieldTo; retp_auto

/-- **The SC invocations changing only scheduling fields**: Bind,
UnbindObject, and a YieldTo from an SC yielded to by none. -/
theorem tk_invokeSchedContext {σ : State Unit} {inv : SchedContextInvocation}
    (h : (∃ sc cap, inv = .invokeSchedContextBind sc cap) ∨ (∃ sc cap, inv = .invokeSchedContextUnbindObject sc cap) ∨
      (∃ sc x n, inv = .invokeSchedContextYieldTo sc ∧ σ.kheap sc = some (.schedContext x n) ∧ x.scYieldFrom = none)) :
    ∀ y ∈ (invokeSchedContext (Z := Unit) inv σ).1, ScTKw (fun _ => False) σ y.2 := by
  rcases h with ⟨sc, cap, rfl⟩ | ⟨sc, cap, rfl⟩ | ⟨sc, x, n, rfl, hk, hyf⟩
  · refine (show NKT (invokeSchedContext (Z := Unit) (.invokeSchedContextBind sc cap)) from ?_) σ
    unfold invokeSchedContext
    cases cap
    all_goals first
      | exact nkt_fail
      | exact nkt_bind (nkt_schedContextBindTcb _ _) fun _ => nkt_pure _
      | exact nkt_bind (nkt_schedContextBindNtfn _ _) fun _ => nkt_pure _
  · refine (show NKT (invokeSchedContext (Z := Unit) (.invokeSchedContextUnbindObject sc cap)) from ?_) σ
    unfold invokeSchedContext
    cases cap
    all_goals first
      | exact nkt_fail
      | exact nkt_bind (nkt_schedContextUnbindTcb _) fun _ => nkt_pure _
      | exact nkt_bind (nkt_schedContextUnbindNtfn _) fun _ => nkt_pure _
  · exact nkt_schedContextYieldTo hk hyf

end

/-! ## The producers -/

section
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3 Fl4Proofs.P3.Ipc
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **The SC producers' extra premises** beside `XTopAt` at `Z` (a named
bundle, not an `XTop` field): the scheduler invariants of the spec (`NSC`,
`Inv`, `CurInv`, `OffOK`, `ActIdle`), the yield-to, MCP and call-stack
relations, the replies' and slots' placement, the IPC placement and the
notifications apart from the kernel-global block, and the platform facts
(`TimeAgree`, the minimum budget, `ticks_to_us`, the Ep side's `MsgOK`). -/
structure ScExtra (ar : machine.Arch A) (Z : XSets) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  nsc : NSC Z.N Z.C σ
  inv : Inv σ
  cur : CurInv σ
  off : OffOK σ
  yld : YieldRel Z.T Z.C (L.mem s) σ
  act : ActIdle σ
  mcp : McpRel Z.T (L.mem s) σ
  c0 : ∀ q ∈ Z.C, q ≠ 0#u64
  call : ∃ Lst : U64 → List U64, CallRel (L.mem s) Z.R Z.C σ Lst ∧ RFree (L.mem s) Z.R Z.C σ Lst
  rp : RPlaced st Z.N Z.T Z.C Z.R Z.c s σ
  apart : SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s σ
  ip : IPlaced Z.N Z.T Z.E Z.R Z.B
  nk : ∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val
  tm : TimeAgree ar
  mb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄
  max : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv
  tu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄
  msg : MsgOK st Z.N Z.T Z.C Z.c

/-- **The SchedControl cap at `XTop`** (`ConfigureFlags`, no data): from
`XTopAt` at `Z`, the decode's post keeps `XTop`, by `xtop_sc_step` (FL4's
`KFoot` writes, the spec's restart and configure `ScTKw`-steps). The extra
premises are `ScExtra` and the cap's (`decode_configure_refines`'), and the
run's arch state keeping `AR` (`hArch`: the SC code's timer and IPI
operations keep the CR3 relation). -/
theorem decode_invocation_sched_controlXT {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s a σ) (hE : ScExtra (L := L) ar Z s a σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .schedControlConfigureFlags ↔
      lbl = fl4_abi.label.SchedControlConfigureFlags)
    (cpu length buf ct : U64) (hcpu : cpu = Z.c) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (hsb : x0 ≠ 0#u64 → ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → sb.val < 64)
    (hsc : x0 ≠ 0#u64 → ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p ∈ Z.C ∧ p ≠ 0#u64 ∧
      ∃ x, σ.kheap p.bv = some (.schedContext x (sb.val - Fl4Spec.minSchedContextBits)) ∧
        ∀ t : U64, x.scTcb = some t.bv →
          t ∈ Z.T ∧ ∃ xt, σ.kheap t.bv = some (.tcb xt) ∧ xt.tcbSchedContext = some p.bv)
    {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc)) (hrun : Fl4Spec.runnable xc.tcbState = true)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef)
    (hArch : syscall.decode_invocation st ar s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => ∀ c, AR a c → AR r.2.2 c ⦄) :
    DecOKDMX (L := L) ar (XTop (L := L) AR) s a σ lbl length slot (.SchedControl cpu) blk call don fp buf extra
      slbl (args.map UScalar.bv) ci sl excaps buffer := by
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  obtain ⟨hN, hI, hC, hO⟩ := And.intro hE.nsc (And.intro hE.inv (And.intro hE.cur hE.off))
  have hT := hE.tm
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  have key : syscall.decode_invocation st ar s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ res => (fp = true ∧ res = (.Err (.Sys (.InvalidCapability 0#u64)), s, a)) ∨
        (fp = false ∧ CPost σ (Fl4Spec.decodeSchedControlInvocationFlags (Z := Unit) slbl (args.map UScalar.bv)
          (excaps.map Prod.fst)) s a
        (fun inv res => ∃ σ1 σ', Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) ∧
          Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv σ1 = ({((), σ')}, False) ∧
          res.1 = .Ok () ∧ SchedRel st Z.N Z.T Z.C Z.c res.2.1 σ' ∧ NtfnStateRel Z.N Z.T (L.mem res.2.1) σ' ∧
          NSC Z.N Z.C σ' ∧ Inv σ' ∧ WritesIn st s res.2.1 (KFoot st Z.T Z.N Z.C Z.c s σ)) res) ⦄ := by
    unfold syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    cases fp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact WP.spec_mono (decode_configure_refines hT Z.th s a σ hS hR hN hI hC hO lbl slbl hlbl cpu length buf ct
        hcpu hct args hlen hargs extra x0 hx0 _ hex hsb hsc hkc hrun) fun r h => Or.inr ⟨by trivial, h⟩
    · simp only [↓reduceIte, WP.spec_ok]
      exact Or.inl ⟨by trivial, by trivial⟩
  unfold DecOKDMX
  refine WP.spec_mono (WP.spec_and hArch key) ?_
  rintro ⟨r0, s', a'⟩ ⟨hA, hq⟩
  rcases hq with ⟨rfl, he⟩ | ⟨rfl, hq⟩
  · cases he
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩
  rcases hq with ⟨e, e', he, hrun', herr⟩ | ⟨inv, hrun', σ1, σ', he1, he2, hr1, hS', hR', -, -, hw⟩
  · cases he
    exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err hrun', herr⟩, ⟨Z, hX⟩⟩
  have hK : ScTKw (fun p => p = ct.bv) σ σ' :=
    (tk_setThreadState hkc (ipcFree_of_runnable hrun) ipcFree_restart _ (by rw [he1]; exact Set.mem_singleton _)).trans
      ((nkt_invokeSchedControlConfigureFlags inv σ1 ((), σ') (by rw [he2]; exact Set.mem_singleton _)).mono
        fun _ h => h.elim)
  have hX' : XTopAt (L := L) AR Z s' a' σ' :=
    xtop_sc_step hX hE.ip hE.nk (WritesIn.tfoot_of_kfoot hw) hK hS' hR' fun h => hA _ h
  obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := hX'.rel
  refine Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun'), σ1, by rw [hcur]; exact he1, (.ok [], σ'), ?_,
    ⟨Z.th, Z.G, Or.inl ⟨hr1, rfl⟩, hPl, hCR, hFI, hD, hMO⟩, ⟨Z, hX'⟩⟩
  exact mem_bindE_ok (mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv)
    (s := σ1) (x := ((), σ')) (by rw [he2]; exact Set.mem_singleton _)) (Set.mem_singleton _)

set_option maxHeartbeats 1000000 in
/-- **The SchedContext cap at `XTop`** for Bind, UnbindObject and a YieldTo
from an SC yielded to by none (`hl`): when the invocation returns no data
(Bind, UnbindObject, a switching YieldTo), `DecOKDMX` at `XTop`, by
`xtop_sc_step` (FL4's `TFoot` writes, `ScFine`; the spec's restart and
invocation `ScTKw`-steps); a YieldTo returning at once has replied
(`set_consumed`), `DecOKRMX` with `X` true, its `XTop` the reply leaf's
(`ScReplyLeaf`). -/
theorem decode_invocation_sched_contextXT {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s a σ) (hE : ScExtra (L := L) ar Z s a σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    {sc : U64} (sb : U64) (hsc : sc ∈ Z.C) (hpi : sc.bv ≠ Fl4Spec.idleScPtr)
    (hl : lbl = fl4_abi.label.SchedContextBind ∨ lbl = fl4_abi.label.SchedContextUnbindObject ∨
      (lbl = fl4_abi.label.SchedContextYieldTo ∧ L.mem s (scYieldFromA sc) = 0#u64))
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ Z.T ∧ L.mem s (scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    (hbn : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → ∀ m : U64, y.scNtfn = some m.bv → m ∈ Z.N)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) (hcs : Fl4Spec.schedulable ct.bv σ = true)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (hcapT : x0 ≠ 0#u64 → ∀ p, capAt (L.mem s) x0 = ok (.Thread p) → p ∈ Z.T)
    (hcapN : x0 ≠ 0#u64 → ∀ p b w r, capAt (L.mem s) x0 = ok (.Notification p b w r) → p ∈ Z.N ∧ p ≠ 0#u64)
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef)
    (hArch : syscall.decode_invocation st ar s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => ∀ c, AR a c → AR r.2.2 c ⦄) :
    DecOKDMX (L := L) ar (XTop (L := L) AR) s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      slbl args ci sl excaps buffer ∨
    DecOKRMX (L := L) ar (fun _ _ _ => True) s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      slbl args ci sl excaps buffer ct := by
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  obtain ⟨hP, hCRel, hFI, hDR, hFR, -, -⟩ := hX.rel
  obtain ⟨Lst, hCR, hRF⟩ := hE.call
  have hRP := hE.rp
  have hA := hE.apart
  have hNk := hE.nk
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  have hctT : ct ∈ Z.T := hct' ▸ hc.curT
  have hf := hc.node.fits
  have hal := hc.node.align
  simp only [LawfulStore.nodeBase] at hf hal
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by omega
  have hka : (L.ksb s).val % 8 = 0 := by omega
  obtain ⟨xc, -, -, -, hkc, -, hrunc, -⟩ := schedulable_inv hcs
  have key : syscall.decode_invocation st ar s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ res => (fp = true ∧ res = (.Err (.Sys (.InvalidCapability 0#u64)), s, a)) ∨
        (fp = false ∧ CPost σ (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)) s a
          (ScQ (fun s' σ' => ScAll (st := st) Z.N Z.T Z.C Z.R Z.c s σ s' σ' ∧
            ScFine (st := st) Z.N Z.T Z.C Z.c lbl sc ct s σ s' σ') σ ct call) res) ⦄ := by
    unfold syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    cases fp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact WP.spec_mono (sc_decode_refines hE.tm Z.th s a σ hS hR hE.nsc hE.inv hE.yld hE.act hE.mcp hE.c0 hCR hRP
        hRF lbl slbl hlbl hsc hpi hback hbn hct hcs call extra x0 hx0 _ hex hcapT hcapN hE.mb hE.max hE.tu hE.msg)
        fun r h => Or.inr ⟨by trivial, h⟩
    · simp only [↓reduceIte, WP.spec_ok]
      exact Or.inl ⟨by trivial, by trivial⟩
  obtain ⟨r, hr, hA2, hq⟩ := spec_exists (WP.spec_and hArch key)
  have tr : ∀ P : core.result.Result Unit error.Exc × S × A → Prop, P r →
      syscall.decode_invocation st ar s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra ⦃ P ⦄ :=
    fun P hP => by rw [hr]; exact (WP.spec_ok _).2 hP
  rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, hq⟩
  · left
    exact tr _ (Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
  rcases hq with ⟨e, e', he, hrun, herr⟩ | ⟨inv, hrun, hr1, σ0, data, σ1, σ2, he0, he1, hcase, hall, hfine⟩
  · left
    subst he
    exact tr _ (Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err hrun, herr⟩, ⟨Z, hX⟩⟩)
  have hw := hall.2.2.2.2.2
  have hSS := slotsSame_of_ufoot hP hS hRP hA hw
  have hdw : ∀ o ∈ domOffs, L.mem r.2.1 (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o) := fun o ho =>
    hw.mem_eq (ksW_al hkf hka (domOffs_lt ho).1 (domOffs_lt ho).2) fun hb => UFoot.ne_ks hS hRP hNk hb (domOffs_lt ho).1 rfl
  have fin : ∀ σ' : Fl4Spec.State Unit, SOK (false, false) σ σ' →
      CRel Z.th (L.mem r.2.1) σ' Z.G ∧ FinInv Z.th (L.mem r.2.1) σ' Z.G ∧ DomRel (L.mem r.2.1) (L.ksb r.2.1) σ' ∧
        MdbOKV (L.ksb r.2.1) (L.mem r.2.1) Z.G := by
    intro σ' hk
    obtain ⟨h1, h2⟩ := crel_of_sok hCRel hFI hSS hk
    exact ⟨h1, h2, by rw [hw.1]; exact hDR.frame hdw hk.dl hk.dsi, by rw [hw.1]; exact MdbOKV.of_same hCRel.2.2.1 hSS hFR⟩
  have hsok1 : SOK (false, false) σ σ1 := ((pres_setThreadState _ _ _).of_eq he0).trans
    (((pres_invokeSchedContext inv).of_eq he1).weaken (fun h => by cases h) (fun h => by cases h))
  have hdec : DecOut (specDec false slbl args ci sl (.SchedContext sc sb) excaps buffer) σ
      (.invokeSchedContext inv) := DecOut.of_eq (run_liftME_ok hrun)
  have hmem : ((.ok data, σ1) : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeSchedContext inv)).run σ0).1 :=
    mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) inv) (s := σ0) (x := (data, σ1))
      (by rw [he1]; exact Set.mem_singleton _)
  rcases hcase with ⟨hd, hσ⟩ | ⟨⟨xr, hkr, hrs⟩, hdo⟩
  · -- no data: `XTop` after
    left
    rw [hσ] at hall hfine
    -- the spec's restart
    have hσ0 := the_result (Fl4Proofs.P3.Notif.setThreadState_eq .restart hkc) he0
    have hko : ∀ q, q ≠ ct.bv → σ0.kheap q = σ.kheap q := fun q hq => by
      rw [hσ0, stsAct_kheap]; simp [updK, hq]
    have hkc0 : σ0.kheap ct.bv = some (.tcb { xc with tcbState := .restart }) := by
      rw [hσ0, stsAct_kheap]; simp [updK]
    have hK0 : ScTKw (fun p => p = ct.bv) σ σ0 :=
      tk_setThreadState hkc (ipcFree_of_runnable hrunc) ipcFree_restart _ (by rw [he0]; exact Set.mem_singleton _)
    -- the invocation's shape
    have hK1 : ScTKw (fun _ => False) σ0 σ1 := by
      refine tk_invokeSchedContext ?_ (data, σ1) (by rw [he1]; exact Set.mem_singleton _)
      rcases hl with l | l | ⟨l, hy0⟩
      · have hg : Fl4Spec.genInvocationType slbl = .schedContextBind := by rw [hlbl, l]; unfold scLabelOf; simp
        simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
        obtain ⟨cap, rfl⟩ := (retP_bindDec _ _).of_run hrun
        exact Or.inl ⟨_, _, rfl⟩
      · have hg : Fl4Spec.genInvocationType slbl = .schedContextUnbindObject := by
          rw [hlbl, l]; unfold scLabelOf; simp
        simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
        obtain ⟨cap, rfl⟩ := (retP_unbindObjDec _ _).of_run hrun
        exact Or.inr (Or.inl ⟨_, _, rfl⟩)
      · have hg : Fl4Spec.genInvocationType slbl = .schedContextYieldTo := by rw [hlbl, l]; unfold scLabelOf; simp
        simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
        have e := (retP_yieldToDec _).of_run hrun
        obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
        have hyf : x.scYieldFrom = none := by rw [hx.yieldFrom, ← scYieldFromA_eq, hy0, optRef_zero]
        have hpc : sc.bv ≠ ct.bv := fun e => by rw [e, hkc] at hk; cases hk
        exact Or.inr (Or.inr ⟨_, x, n, e, by rw [hko _ hpc]; exact hk, hyf⟩)
    -- FL4's writes
    have hW : WritesIn st s r.2.1 (TFoot st Z.T Z.N Z.C Z.c s σ) := by
      rcases hl with l | l | ⟨l, hy0⟩
      · exact hfine.1 (Or.inl l)
      · exact hfine.1 (Or.inr l)
      · obtain ⟨y, hky, -, hy⟩ := hK1.tcb hkc0
        exact hfine.2 l hy0 y hky (hy.elim id fun h => h.1.elim)
    have hX' : XTopAt (L := L) AR Z r.2.1 r.2.2 σ1 :=
      xtop_sc_step hX hE.ip hNk hW (hK0.trans (hK1.mono fun _ h => h.elim)) hall.1.1 hall.1.2.1 fun h => hA2 _ h
    obtain ⟨c1, c2, c3, c4⟩ := fin σ1 hsok1
    exact tr _ (Or.inr ⟨_, hdec, σ0, by rw [hcur]; exact he0, _, hmem,
      ⟨Z.th, Z.G, Or.inl ⟨hr1, by rw [hd]⟩, hP, c1, c2, c3, c4⟩, ⟨Z, hX'⟩⟩)
  · -- data: FL4 has replied
    right
    have hsok2 : SOK (false, false) σ σ2 := hsok1.trans
      ((pres_bind (pres_when _ (pres_replyFromKernel _ _ _)) fun _ => pres_setThreadState _ _ _).of_eq hdo)
    obtain ⟨c1, c2, c3, c4⟩ := fin σ2 hsok2
    obtain ⟨y2, hky2, hrun2⟩ := running_after hkr hdo
    obtain ⟨x2, hkx2, hrel2⟩ := hall.1.2.1.tcb ct hctT
    rw [hky2] at hkx2; cases hkx2
    have hne : L.mem r.2.1 (stA ct) ≠ sched.TS_RESTART := by
      intro e
      have h1 := hrel2.st
      rw [hrun2] at h1
      rw [show tStA ct = stA ct by rw [tStA_eq, stA_eq], e, tsVals.2.1] at h1
      simp [tsCode] at h1
    have hz : ((), σ2) ∈ (Fl4Proofs.P3.specTail call ct.bv data σ1).1 := by
      rw [specTail_of_restart hkr hrs, hdo]; exact Set.mem_singleton _
    exact tr _ (Or.inr ⟨hr1, hne, _, hdec, σ0, by rw [hcur]; exact he0, data, σ1, hmem, ((), σ2), hz,
      ⟨Z.th, Z.G, hP, c1, c2, c3, c4⟩, trivial⟩)

/-! ## The named leaves -/

/-- **The `set_consumed` reply at `XTop`** (`XLeaf` shape): FL4's
`set_consumed p t wm` (the SC's consumed time read and cleared, then, when
`wm`, reported to `t` as a reply from the kernel) refining
`sched_context_update_consumed p`, then, when `wm`, `reply_from_kernel t (0,
words)`. With `t` the caller and `wm` the call flag it is Consumed's and an
at-once YieldTo's reply (`return_consumed` and `handle_invocation`'s reply;
the caller's `Running` after is an `ScTKw`-step); with `t` the yielder and
`wm` true it is `complete_yield_to`'s `set_consumed`. The reply writes `t`'s
registers (`RegW`), which the IPC relations see, so it is not an
`ScTKw`-step. -/
def ScReplyLeaf (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) (p t : U64)
    (wm : Bool) : Prop :=
  XLeaf (L := L) (XTop (L := L) AR) s a σ (do
      let s' ← schedcontext.set_consumed st ar s a p t wm
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s', a))
    ((do
      let cv ← Fl4Spec.schedContextUpdateConsumed (Z := Unit) p.bv
      Fl4Spec.NonDet.when (wm = true) (Fl4Spec.replyFromKernel (Z := Unit) t.bv (0, Fl4Spec.wordsFromTime cv)) :
      Fl4Spec.SMonad Unit Unit) σ)

/-- **The SC's reply unlinked at `XTop`** (`XLeaf` shape): Unbind's last
step, FL4's `unbind_reply` (the head reply's `NEXT` word and the SC's
`REPLY` word cleared) refining `sched_context_unbind_reply` (the head
reply's SC and the SC's reply list cleared). It changes a reply object, so
it is not an `ScTKw`-step; it is the SC half of `reply_remove`, for the IPC
side's `reply_remove` / `reply_unlink` on `IpcRel` to discharge. (P3's
`reply_unlink_rel`, `reply_unlink_i`, `_c`, `_n` are `ipc.reply_unlink`'s,
the TCB↔reply link, another operation.) -/
def ScUnbindReplyLeaf (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) (sc : U64) : Prop :=
  XLeaf (L := L) (XTop (L := L) AR) s a σ (do
      let s' ← schedcontext.unbind_reply st s sc
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s', a))
    (Fl4Spec.schedContextUnbindReply (Z := Unit) sc.bv σ)

end

end Fl4Proofs.P3.Sched
