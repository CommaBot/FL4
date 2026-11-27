/-
P3 (DESIGN.md §9), invariant line YS (iolay gen 4): **YieldScope kept by the syscall entry and by every kernel
event** (spec side only, outside the JAtZ cone): the hand-proved functions of SpecInvYieldScopeT's skip list
(`proofs/scratch/invA/skipYS.txt`) and the tops.

* The receive: `receiveIpcBlocked` / `receiveIpc` for a thread of `L` (its `blockedOnReceive` write is allowed by
  `ys_setThreadState`'s `t ∈ L`), `handle_recv` from a state whose current thread is in `L`.
* The yield: `schedContextYieldTo` writes `ct.tcbYieldTo := some sc` with `ct` the current thread; it runs in
  `YO [] ct` = `YSL []` and the frame `OPG (fnR ct) univ (· = ct)` (SpecInvFaultTcbsG: the current thread is `ct`
  and `ct` is not `blockedOnReceive`), which every function before the write keeps (`fg_*`). `handle_invocation`
  enters the perform phase after `set_thread_state ct Restart`, so `YO [] ct` holds there (`yo_fl4HandleInvocationR`).
* The first-phase invocations (ReplyRecv, NBSendRecv, NBSendWait: `firstPhase = true`) never perform a
  scheduling-context invocation: `fl4DecodeInvocation true` throws on a SchedContext cap (`ro_decode_fp`), so they
  keep `YSL [ct]` (`ys_fl4HandleInvocationR_fp`), and the receive that follows them runs with `ct ∈ L`; the current
  thread is still `ct` there by ft3's bundle `B` (`b_fl4HandleInvocationR`).
* `activate_thread` clears the current thread's yield (`completeYieldTo`), so every kernel exit has
  `CurYieldNone` (`ys_activateThread`).
* Tops: **`kentry_yieldScope`** (`fl4KernelEntrySyscall`, from `YieldScopeS ∧ CurYieldNone` and ft3's entry facts
  `FaultTcbsS ∧ NQB`, `CtEntry`), **`kcall_yieldScope`** (`fl4CallKernel rep ev` for a non-syscall event, from
  `YieldScopeS`), `kcallF_yieldScope` (the same after the FaultIP write), `boot_curYieldNone`.

No premise ([J]/[P]/[W]): `CtEntry` and `FaultTcbsS ∧ NQB` are hypotheses of the tops, as in SpecInvFaultTcbsH10;
the J layer discharges them from `SInvX` (`SInvA.fts` / `nqb`, `SInvB.entryJ`).
-/
import Fl4Proofs.P3.SpecInvYieldScopeF4
import Fl4Proofs.P3.SpecInvFaultTcbsH10
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {L : List ObjRef}

/-! ## `YSL` lists -/

theorem ysl_mono {L' : List ObjRef} (h : ∀ p ∈ L', p ∈ L) {σ : State Unit} (hs : YSL L σ) : YSL L' σ :=
  fun p x hp => ⟨(hs p x hp).1, fun hm => (hs p x hp).2 (h p hm)⟩

theorem ysl_nil {σ : State Unit} (hs : YSL L σ) : YSL [] σ := ysl_mono (fun _ h => by simp at h) hs

theorem ysl_cons {σ : State Unit} (h : YSL L σ) {t : ObjRef}
    (ht : ∀ x, σ.kheap t = some (.tcb x) → x.tcbYieldTo = none) : YSL (t :: L) σ := by
  intro p x hp
  refine ⟨(h p x hp).1, fun hm => ?_⟩
  rcases List.mem_cons.1 hm with rfl | hm
  · exact ht x hp
  · exact (h p x hp).2 hm

theorem ik_apply {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} {σ : State Unit}
    {y : α × State Unit} (hσ : P σ) (hy : y ∈ (m σ).1) (h : IK P m) : P y.2 := h σ hσ y hy

/-! ## The current thread through the generic frame -/

/-- The trivial per-thread predicate. -/
def Ftriv : FQ where
  R _ _ _ := True
  clr _ _ _ _ := trivial
  st _ _ _ _ := trivial
  dflt _ := trivial

theorem opg_triv {C : ObjRef → Prop} {σ : State Unit} (h : C σ.curThread) : OPG Ftriv Set.univ C σ := by
  refine ⟨fun p o _ => ?_, h⟩
  cases o <;> first | trivial | exact fun _ _ => trivial

/-- `set_thread_state` keeps the trivial predicate. -/
macro_rules | `(tactic| fg_leaf) => `(tactic| ((with_reducible refine fg_setThreadState _ _ ?_); intro _ _ _; trivial))

/-- `ct` is the current thread and is not `blockedOnReceive`. -/
def fnR (ct : ObjRef) : FQ where
  R p _ s := p = ct → notRecvSt s
  clr _ _ _ h := h
  st _ _ _ _ _ := trivial
  dflt _ _ := trivial

/-- `YSL L` and the frame of `ct`. -/
abbrev YO (L : List ObjRef) (ct : ObjRef) (σ : State Unit) : Prop :=
  YSL L σ ∧ OPG (fnR ct) Set.univ (· = ct) σ

theorem yo_of {ct : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : YSK L m)
    (h2 : FGK (fnR ct) Set.univ (· = ct) m) : IK (YO L ct) m := ik_and h1 h2

theorem yo_ofE {ct : ObjRef} {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : YSKE L m)
    (h2 : FGKE (fnR ct) Set.univ (· = ct) m) : IKE (YO L ct) m := ik_and h1 h2

theorem notRecv_of_active {ts : ThreadState} (h : activeSt ts) : notRecvSt ts := by
  cases ts <;> simp_all [activeSt, notRecvSt]

/-- The frame of an active current thread. -/
theorem opg_fnR {σ : State Unit} (h : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState) :
    OPG (fnR σ.curThread) Set.univ (· = σ.curThread) σ := by
  refine ⟨fun p o hp => ?_, rfl⟩
  cases o with
  | tcb x => intro e; subst e; exact notRecv_of_active (h x hp)
  | notification n => exact fun _ _ => trivial
  | _ => trivial

/-- A `gets curThread` read under a predicate fixing the current thread. -/
theorem ik_gets_cur_bind {P : State Unit → Prop} {ct : ObjRef} {β : Type} {k : ObjRef → NonDet (State Unit) β}
    (hc : ∀ s, P s → s.curThread = ct) (h : IK P (k ct)) :
    IK P (NonDet.gets (fun s : State Unit => s.curThread) >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  dsimp only at hx
  rw [hc σ hσ] at hx
  exact h σ hσ x hx

/-! ## The receive -/

theorem ys_receiveIpcBlocked (blk : Bool) (t ep : ObjRef) (r : Option ObjRef) (ht : t ∈ L) :
    YSK L (receiveIpcBlocked (Z := Unit) blk t ep r) := by
  unfold receiveIpcBlocked
  split
  · refine ik_bind (ys_setThreadState _ _ (Or.inr ht)) fun _ => ?_
    ys_auto
  · ys_auto
macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine ys_receiveIpcBlocked _ _ _ _ ?_); assumption))

set_option maxHeartbeats 4000000 in
theorem ys_receiveIpc (t : ObjRef) (c : Cap) (blk : Bool) (rc : Cap) (ht : t ∈ L) :
    YSK L (receiveIpc (Z := Unit) t c blk rc) := by
  unfold receiveIpc; ys_auto
macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine ys_receiveIpc _ _ _ _ ?_); assumption))

/-- **`handle_recv`** from a state whose current thread is in `L`. -/
theorem ys_handleRecv (blk cr : Bool) {σ : State Unit} (hσ : YSL L σ) (hc : σ.curThread ∈ L)
    {y : Unit × State Unit} (hy : y ∈ (handleRecv (Z := Unit) blk cr σ).1) : YSL L y.2 := by
  unfold handleRecv at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [mem_gets h1] at hy
  (try dsimp only at hy)
  refine ik_apply hσ hy ?_
  ys_auto

/-! ## The yield -/

/-- **The only `tcbYieldTo := some _` write**: on the current thread `ct`, which is not receive-blocked. -/
theorem yo_setYield (ct sc : ObjRef) :
    IK (YO [] ct) (setTcbObjRef (Z := Unit) tcbYieldToUpdate ct (some sc)) := by
  show IK _ (threadSet _ ct)
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => ?_
  intro hσ y hy
  have hk := getTcb_kheap hx
  rw [mem_setObject hy]
  have hr : notRecvSt x.tcbState := (hσ.2.1 ct (.tcb x) hk : (fnR ct).R ct x.tcbFault x.tcbState) rfl
  refine ⟨tp_update hσ.1 ct _ fun t ht => ?_, opg_update hσ.2 ct _ fun _ => hr⟩
  cases ht
  exact ⟨fun _ => hr, fun h => nomatch h⟩

set_option maxHeartbeats 4000000 in
/-- **`sched_context_yield_to`** in `YO [] ct`. -/
theorem yo_schedContextYieldTo (ct sc : ObjRef) : IK (YO [] ct) (schedContextYieldTo (Z := Unit) sc) := by
  unfold schedContextYieldTo
  refine ik_bind (yo_of (by ys_auto) (by fg_auto)) fun _ => ?_
  refine ik_bind (yo_of (by ys_auto) (by fg_auto)) fun _ => ?_
  refine ik_bind (yo_of (by ys_auto) (by fg_auto)) fun _ => ?_
  refine ik_bind ?_ fun _ => yo_of (by ys_auto) (by fg_auto)
  refine ik_bind (yo_of (by ys_auto) (by fg_auto)) fun _ => ?_
  refine ik_bind (ik_assertOpt _) fun tcbPtr => ?_
  refine ik_gets_bind fun σ => ikp_of_ik ?_ σ
  refine ik_ite _ ?_ (ik_pure _)
  refine ik_gets_cur_bind (ct := ct) (fun s h => h.2.2) ?_
  refine ik_bind (yo_of (by ys_auto) (by fg_auto)) fun _ => ?_
  refine ik_bind (yo_of (by ys_auto) (by fg_auto)) fun _ => ?_
  refine ik_ite _ (yo_of (by ys_auto) (by fg_auto)) ?_
  exact ik_bind (yo_setYield ct sc) fun _ => yo_of (by ys_auto) (by fg_auto)

theorem yo_invokeSchedContext (ct : ObjRef) (i : SchedContextInvocation) :
    IK (YO [] ct) (invokeSchedContext (Z := Unit) i) := by
  cases i
  case invokeSchedContextYieldTo sc => exact yo_schedContextYieldTo ct sc
  all_goals exact yo_of (by simp only [invokeSchedContext]; ys_auto) (fg_invokeSchedContext _)

/-- Every invocation but a scheduling-context one keeps `YSL L`. -/
theorem ys_fl4PerformInvocation_nSC (bl call don : Bool) (i : Fl4Invocation)
    (h : ∀ j, i ≠ .invokeSchedContext j) : YSKE L (fl4PerformInvocation (Z := Unit) bl call don i) := by
  cases i
  case invokeSchedContext j => exact absurd rfl (h j)
  all_goals (simp only [fl4PerformInvocation]; ys_auto)

/-- Every invocation, from `YO [] ct`. -/
theorem yo_fl4PerformInvocation (ct : ObjRef) (bl call don : Bool) (i : Fl4Invocation) :
    HKE (YO [] ct) (YSL []) (fl4PerformInvocation (Z := Unit) bl call don i) := by
  by_cases hs : ∃ j, i = .invokeSchedContext j
  · obtain ⟨j, rfl⟩ := hs
    simp only [fl4PerformInvocation, withoutPreemption]
    intro σ hσ y hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    exact (yo_invokeSchedContext ct j σ hσ x hx).1
  · exact fun σ hσ y hy => ys_fl4PerformInvocation_nSC (L := []) bl call don i (fun j e => hs ⟨j, e⟩) σ hσ.1 y hy

/-! ## The decode's result in the first phase -/

/-- Every `ok` result of `m` satisfies `R`. -/
def RO {ε α : Type} (R : α → Prop) (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ s y, y ∈ ((ExceptT.run m) s).1 → ∀ a, y.1 = .ok a → R a

section RO
variable {ε α β : Type} {R : β → Prop}

theorem ro_throw (e : ε) : RO R (NonDetE.throwError e : NonDetE (State Unit) ε β) := by
  intro s y hy a ha
  rw [Set.mem_singleton_iff.1 hy] at ha
  cases ha

theorem ro_returnOk {b : β} (h : R b) : RO R (NonDetE.returnOk b : NonDetE (State Unit) ε β) := by
  intro s y hy a ha
  rw [Set.mem_singleton_iff.1 hy] at ha
  cases ha
  exact h

theorem ro_liftME {f : α → β} {m : NonDetE (State Unit) ε α} (hf : ∀ x, R (f x)) :
    RO R (NonDetE.liftME f m) := by
  intro s y hy b hb
  unfold NonDetE.liftME at hy
  obtain ⟨z, -, ⟨a, -, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
  · rw [Set.mem_singleton_iff.1 hy] at hb
    cases hb
    exact hf a
  · cases hb

theorem ro_bind {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hg : ∀ a, RO R (g a)) :
    RO R (m >>= g) := by
  intro s y hy b hb
  obtain ⟨z, -, ⟨a, -, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
  · exact hg a _ y hy b hb
  · cases hb

end RO

/-- **The first-phase decode never returns a scheduling-context invocation** (it throws on a SchedContext cap). -/
theorem ro_decode_fp (label : Data) (args : List Data) (ci : CapRef) (slot : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    RO (fun b => ∀ j, b ≠ Fl4Invocation.invokeSchedContext j)
      (fl4DecodeInvocation (Z := Unit) true label args ci slot cap ex buf) := by
  cases cap <;> simp only [fl4DecodeInvocation, ↓reduceIte] <;> (try split) <;>
    first
    | exact ro_throw _
    | exact ro_returnOk (by intro j h; cases h)
    | exact ro_liftME (by intro x j h; cases h)

/-! ## `handle_invocation` -/

set_option maxHeartbeats 4000000 in
/-- **The first phase keeps `YSL L`** (no scheduling-context invocation, `ro_decode_fp`). -/
theorem ys_fl4HandleInvocationR_fp (rep cl bl dn : Bool) (cptr : CapRef) :
    YSKE L (fl4HandleInvocationR (Z := Unit) rep cl bl dn true cptr) := by
  unfold fl4HandleInvocationR
  refine hke_gets_bind fun σ hσ => ?_
  simp only [withoutPreemption]
  refine hke_bind (R := YSL L) (hk_liftE (hk_of_ik (by ys_auto))) (fun info => ?_) (fun _ h => h) σ hσ
  intro σ' hσ' y0 hy0
  refine ft_syscall_post (I := YSL L) (Q := YSL L) ?_ ?_ ?_ ?_ ?_ y0 hy0
  · exact (by ys_auto : YSKE L _) σ' hσ'
  · intro f s hs v hv
    exact (by ys_auto : YSK L _) s hs v hv
  · intro a s has w hw
    have hs : YSL L s := (by ys_auto : YSKE L _) σ' hσ' _ has
    obtain ⟨sl, cap, ex, buf⟩ := a
    exact (by ys_auto : YSKE L _) s hs w hw
  · intro e s hs v hv
    exact (by ys_auto : YSK L _) s hs v hv
  · intro a s b s' _ hd hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hb : ∀ j, b ≠ Fl4Invocation.invokeSchedContext j :=
      ro_bind (fun _ => ro_decode_fp _ _ _ _ _ _ _) s _ hd b rfl
    refine ik_apply hI hy ?_
    refine ike_bind (ike_liftE (ys_setThreadState _ _ (Or.inl trivial))) fun _ => ?_
    refine ike_bind (ys_fl4PerformInvocation_nSC _ _ _ b hb) fun _ => ?_
    ys_auto

set_option maxHeartbeats 4000000 in
/-- **Any phase, from `YO [] ct`** (the yield runs after `set_thread_state ct Restart`). -/
theorem yo_fl4HandleInvocationR (ct : ObjRef) (rep cl bl dn fp : Bool) (cptr : CapRef) :
    HKE (YO [] ct) (YSL []) (fl4HandleInvocationR (Z := Unit) rep cl bl dn fp cptr) := by
  unfold fl4HandleInvocationR
  refine hke_gets_bind fun σ hσ => ?_
  have hc : σ.curThread = ct := hσ.2.2
  simp only [hc, withoutPreemption]
  refine hke_bind (R := YO [] ct) (hk_liftE (hk_of_ik (yo_of (by ys_auto) (by fg_auto)))) (fun info => ?_)
    (fun _ h => h.1) σ hσ
  intro σ' hσ' y0 hy0
  refine ft_syscall_post (I := YO [] ct) (Q := YSL []) ?_ ?_ ?_ ?_ ?_ y0 hy0
  · exact (yo_ofE (by ys_auto) (by fg_auto)) σ' hσ'
  · intro f s hs v hv
    exact (by ys_auto : YSK [] _) s hs.1 v hv
  · intro a s has w hw
    have hs : YO [] ct s := (yo_ofE (by ys_auto) (by fg_auto)) σ' hσ' _ has
    obtain ⟨sl, cap, ex, buf⟩ := a
    exact (yo_ofE (by ys_auto) (by fg_auto)) s hs w hw
  · intro e s hs v hv
    exact (by ys_auto : YSK [] _) s hs.1 v hv
  · intro a s b s' _ _ hI y hy
    refine hke_bind (R := YO [] ct) (Q := YSL [])
      (hk_liftE (hk_of_ik (yo_of (ys_setThreadState ct .restart (Or.inl trivial))
        (fg_setThreadState ct .restart fun _ _ _ _ => trivial)))) (fun _ => ?_) (fun _ h => h.1) s' hI y hy
    refine hke_bind (R := YSL []) (yo_fl4PerformInvocation ct _ _ _ b) (fun _ => ?_) (fun _ h => h)
    exact hk_of_ik (by ys_auto)

/-! ## `handle_syscall` -/

/-- The syscall's start: `YSL [ct]`, ft3's bundle and the frame of `ct`. -/
abbrev P0 (ct : ObjRef) (σ : State Unit) : Prop :=
  YSL [ct] σ ∧ B [ct] [ct] [ct] (· = ct) σ ∧ OPG (fnR ct) Set.univ (· = ct) σ

theorem p0_frame {ct : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : YSK [ct] m) (h2 : GF (· = ct) m) :
    IK (P0 ct) m :=
  fun σ hσ y hy => ⟨h1 σ hσ.1 y hy, b_of_gf h2 σ hσ.2.1 y hy, h2 _ _ σ hσ.2.2 y hy⟩

theorem hke_and {P Q : State Unit → Prop} {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : YSKE L m)
    (h2 : HKE P Q m) : HKE (fun s => YSL L s ∧ P s) (fun s => YSL L s ∧ Q s) m :=
  fun σ hσ y hy => ⟨h1 σ hσ.1 y hy, h2 σ hσ.2 y hy⟩

set_option maxHeartbeats 4000000 in
theorem ys_fl4HandleSyscall (ct : ObjRef) (rep : Bool) (c : Syscall) :
    HKE (P0 ct) (YSL []) (fl4HandleSyscall (Z := Unit) rep c) := by
  have hInv : ∀ (cl bl dn fp : Bool), HKE (P0 ct) (YSL []) (do
      let cptr ← NonDetE.liftE (getCapReg (Z := Unit) cap_register)
      fl4HandleInvocationR rep cl bl dn fp cptr) := by
    intro cl bl dn fp
    refine hke_bind (R := YO [] ct) (hk_liftE ?_) (fun cptr => yo_fl4HandleInvocationR ct rep cl bl dn fp cptr)
      (fun _ h => h.1)
    intro σ hσ y hy
    exact ⟨ysl_nil ((by ys_auto : YSK [ct] _) σ hσ.1 y hy), fg_getCapReg (Fq := fnR ct) (Sq := Set.univ) (Cq := (· = ct)) _ σ hσ.2.2 y hy⟩
  have hRecv : ∀ b r, HKE (P0 ct) (YSL []) (withoutPreemption (Z := Unit) (handleRecv b r)) := by
    intro b r
    refine hk_liftE fun σ hσ y hy => ysl_nil (ys_handleRecv b r hσ.1 ?_ hy)
    rw [hσ.2.2.2]; exact List.mem_singleton_self _
  have hRR : ∀ (m : SMonad Unit CapRef) (hm1 : YSK [ct] m) (hm2 : GF (· = ct) m) (bl : Bool),
      HKE (P0 ct) (YSL []) (do
        let cp ← withoutPreemption (Z := Unit) m
        fl4HandleInvocationR rep false false true true cp
        withoutPreemption <| handleRecv true bl) := by
    intro m hm1 hm2 bl
    refine hke_bind (R := fun s => YSL [ct] s ∧ B [ct] [ct] [ct] (· = ct) s)
      (hk_liftE fun σ hσ y hy => ⟨hm1 σ hσ.1 y hy, b_of_gf hm2 σ hσ.2.1 y hy⟩) (fun cp => ?_)
      (fun _ h => ysl_nil h.1)
    refine hke_bind (R := fun s => YSL [ct] s ∧
        (B [ct] [ct] [ct] (· = ct) s ∨ (false = true ∧ B [] [] [ct] (· = ct) s)))
      (hke_and (ys_fl4HandleInvocationR_fp rep false false true cp) (b_fl4HandleInvocationR ct rep false false true true cp))
      (fun _ => ?_) (fun _ h => ysl_nil h.1)
    refine hk_liftE fun σ hσ y hy => ysl_nil (ys_handleRecv true bl hσ.1 ?_ hy)
    have hc : σ.curThread = ct := by
      rcases hσ.2 with h | h
      · exact h.1.2
      · exact absurd h.1 (by simp)
    rw [hc]; exact List.mem_singleton_self _
  cases c
  case sysSend => simp only [fl4HandleSyscall]; exact hInv _ _ _ _
  case sysNBSend => simp only [fl4HandleSyscall]; exact hInv _ _ _ _
  case sysCall => simp only [fl4HandleSyscall]; exact hInv _ _ _ _
  case sysYield =>
    simp only [fl4HandleSyscall, withoutPreemption]
    exact hk_liftE fun σ hσ y hy => ysl_nil ((by ys_auto : YSK [ct] _) σ hσ.1 y hy)
  case sysReplyRecv =>
    simp only [fl4HandleSyscall]
    exact hRR _ (by ys_auto) (fun F S => by fg_auto) true
  case sysNBSendRecv =>
    simp only [fl4HandleSyscall]
    exact hRR _ (by ys_auto) (fun F S => by fg_auto) true
  case sysNBSendWait =>
    simp only [fl4HandleSyscall]
    exact hRR _ (by ys_auto) (fun F S => by fg_auto) false
  all_goals
    simp only [fl4HandleSyscall]
    exact hRecv _ _

/-! ## The events -/

set_option maxHeartbeats 4000000 in
theorem ys_fl4HandleEvent_sys (ct : ObjRef) (rep : Bool) (c : Syscall) :
    HKE (P0 ct) (YSL []) (fl4HandleEvent (Z := Unit) rep (.syscallEvent c)) := by
  simp only [fl4HandleEvent]
  refine hke_bind (R := P0 ct) (hk_liftE (hk_of_ik (p0_frame (by ys_auto) fun F S => fg_updateTimeStamp)))
    (fun _ => ?_) (fun _ h => ysl_nil h.1)
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    simp only [Except.ok.injEq] at ha; subst ha
    obtain ⟨e1, -⟩ := b_checkBudgetRestart (L := [ct]) (E := []) (K := [ct]) ct (List.mem_singleton_self _)
      (List.mem_singleton_self _) (by simp) hσ.2.1 hw
    have hw2 : YSL [ct] w.2 := (by ys_auto : YSK [ct] (checkBudgetRestart (Z := Unit))) σ hσ.1 w hw
    unfold NonDetE.whenE at hy
    split at hy
    · rename_i hr
      rw [e1 hr] at hy
      exact ys_fl4HandleSyscall ct rep c σ hσ y hy
    · rw [Set.mem_singleton_iff.1 hy]
      exact ysl_nil hw2
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

/-- Every non-syscall event (l4v's `handle_event`). -/
theorem ys_handleEvent (ev : Event) (hev : ∀ c, ev ≠ .syscallEvent c) : YSKE L (handleEvent (Z := Unit) ev) := by
  cases ev
  case syscallEvent c => exact absurd rfl (hev c)
  all_goals (simp only [handleEvent]; ys_auto)

/-! ## The kernel exit -/

/-- After `thread_set (tcb_yield_to := None)` on `t`, `t` has no yield. -/
theorem clearYield_post (t : ObjRef) {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (threadSet (Z := Unit) (tcbYieldToUpdate fun _ => none) t σ).1) :
    ∀ x, y.2.kheap t = some (.tcb x) → x.tcbYieldTo = none := by
  unfold threadSet at hy
  obtain ⟨z, hz, hy⟩ := hy
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some a =>
    rw [e] at hz
    have hz' := Set.mem_singleton_iff.1 hz
    subst hz'
    rw [mem_setObject hy]
    intro x hx
    dsimp only at hx
    simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hx
    rw [← hx]
    rfl

theorem ys_cancelYieldTo_cons (t : ObjRef) : HK (YSL L) (YSL (t :: L)) (schedContextCancelYieldTo (Z := Unit) t) := by
  intro σ hσ y hy
  unfold schedContextCancelYieldTo at hy
  obtain ⟨y1, h1, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet h1
  (try dsimp only at hy)
  cases hyt : x.tcbYieldTo with
  | none =>
    rw [hyt] at hy
    simp only [NonDet.maybeM] at hy
    rw [Set.mem_singleton_iff.1 hy]
    exact ysl_cons hσ fun x' hx' => by rw [hx] at hx'; cases hx'; exact hyt
  | some sc =>
    rw [hyt] at hy
    simp only [NonDet.maybeM] at hy
    obtain ⟨y2, h2, hy⟩ := hy
    have hs2 : YSL L y2.2 := by refine ik_apply hσ h2 ?_; ys_auto
    exact ysl_cons (ys_clearYield t y2.2 hs2 y hy) (clearYield_post t hy)

theorem ys_completeYieldTo_cons (t : ObjRef) : HK (YSL L) (YSL (t :: L)) (completeYieldTo (Z := Unit) t) := by
  intro σ hσ y hy
  unfold completeYieldTo at hy
  obtain ⟨y1, h1, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet h1
  (try dsimp only at hy)
  cases hyt : x.tcbYieldTo with
  | none =>
    rw [hyt] at hy
    simp only [NonDet.maybeM] at hy
    rw [Set.mem_singleton_iff.1 hy]
    exact ysl_cons hσ fun x' hx' => by rw [hx] at hx'; cases hx'; exact hyt
  | some sc =>
    rw [hyt] at hy
    simp only [NonDet.maybeM] at hy
    obtain ⟨y2, h2, hy⟩ := hy
    have hs2 : YSL L y2.2 := by refine ik_apply hσ h2 ?_; ys_auto
    exact ys_cancelYieldTo_cons t y2.2 hs2 y hy

/-- **`activate_thread` clears the current thread's yield**: every kernel exit has `CurYieldNone`. -/
theorem ys_activateThread {σ : State Unit} (hσ : YSL [] σ) {y : Unit × State Unit}
    (hy : y ∈ (activateThread (Z := Unit) σ).1) : YieldScopeS y.2 ∧ CurYieldNone y.2 := by
  unfold activateThread at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [mem_gets h1] at hy
  (try dsimp only at hy)
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet h2
  (try dsimp only at hy)
  obtain ⟨y3, h3, hy⟩ := hy
  have hA : YSL [σ.curThread] y3.2 ∧ y3.2.curThread = σ.curThread := by
    unfold NonDet.when at h3
    split at h3
    · exact ⟨ys_completeYieldTo_cons _ σ hσ y3 h3,
        (ik_apply (opg_triv (C := (· = σ.curThread)) rfl) h3 (fg_completeYieldTo _)).2⟩
    · rename_i hn
      rw [Set.mem_singleton_iff.1 h3]
      refine ⟨ysl_cons hσ fun x' hx' => ?_, rfl⟩
      rw [hx] at hx'; cases hx'; exact not_not.1 hn
  have hY : YSL [σ.curThread] y.2 := by
    refine ik_apply hA.1 hy ?_
    ys_auto
  have hC : y.2.curThread = σ.curThread := by
    refine (ik_apply (opg_triv (C := (· = σ.curThread)) hA.2) hy ?_).2
    fg_auto
  refine ⟨(YSL.nil_iff _).1 (ysl_nil hY), fun x' hx' => ?_⟩
  rw [hC] at hx'
  exact (hY _ x' hx').2 (List.mem_singleton_self _)

/-- **`fl4CallKernel`**: the handler ends in `YSL []` (also on an error, then `preemption_path`), then
`fl4Awaken`, `schedule` and `activate_thread`. -/
theorem ys_fl4CallKernel (rep : Bool) (ev : Event) {P : State Unit → Prop}
    (h : HKE P (YSL []) (fl4HandleEvent (Z := Unit) rep ev)) :
    HK P (fun s => YieldScopeS s ∧ CurYieldNone s) (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  intro σ hσ y ⟨y1, h1, hy⟩
  have hq : YSL [] y1.2 := by
    unfold NonDetE.handleE at h1
    rw [ExceptT.run_mk] at h1
    obtain ⟨z, hz, h1⟩ := h1
    have hz' := h σ hσ z hz
    obtain ⟨r, s⟩ := z
    cases r with
    | ok a => rw [Set.mem_singleton_iff.1 h1]; exact hz'
    | error e =>
      obtain ⟨w, hw, rfl⟩ := ft_mem_liftE (m := preemptionPath (Z := Unit)) h1
      exact (by ys_auto : YSK [] (preemptionPath (Z := Unit))) s hz' w hw
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 : YSL [] y2.2 := (by ys_auto : YSK [] (fl4Awaken (Z := Unit))) _ hq y2 h2
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : YSL [] y3.2 := (by ys_auto : YSK [] (schedule (Z := Unit))) _ hb2 y3 h3
  exact ys_activateThread hb3 hy

/-! ## The tops -/

/-- **YieldScope across the syscall entry** (`fl4KernelEntrySyscall`), from the entry half `CurYieldNone` and
ft3's entry facts. -/
theorem kentry_yieldScope (rep : Bool) (c : Syscall) {σ : State Unit} (hY : YieldScopeS σ) (hC : CurYieldNone σ)
    (hF : FaultTcbsS σ ∧ NQB σ) (hJ : CtEntry σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, YieldScopeS y.2 ∧ CurYieldNone y.2 := by
  intro y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hP : P0 σ.curThread σ := ⟨YSL.ofCur hY hC, b_entry_of hF hJ, opg_fnR hJ.1⟩
  have hP2 : P0 σ.curThread y2.2 :=
    p0_frame (by ys_auto) (fun F S => fg_fl4SyscallFaultIP _) σ hP y2 h2
  exact ys_fl4CallKernel rep _ (ys_fl4HandleEvent_sys σ.curThread rep c) y2.2 hP2 y hy

/-- **YieldScope across a non-syscall kernel event** (`fl4CallKernel rep ev`). -/
theorem kcall_yieldScope (rep : Bool) (ev : Event) (hev : ∀ c, ev ≠ .syscallEvent c) {σ : State Unit}
    (hY : YieldScopeS σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, YieldScopeS y.2 ∧ CurYieldNone y.2 := by
  refine fun y hy => ys_fl4CallKernel rep ev (P := YSL []) (fun σ' h z hz => ?_) σ ((YSL.nil_iff σ).2 hY) y hy
  rw [fl4HandleEvent_other rep ev hev] at hz
  exact ys_handleEvent ev hev σ' h z hz

/-- **The same after the FaultIP write** of the current thread (the trap entries). -/
theorem kcallF_yieldScope (rep : Bool) (ev : Event) (hev : ∀ c, ev ≠ .syscallEvent c) {σ : State Unit}
    (hY : YieldScopeS σ) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) w.2).1, YieldScopeS y.2 ∧ CurYieldNone y.2 := by
  intro w hw
  refine kcall_yieldScope rep ev hev ((YSL.nil_iff _).1 ?_)
  exact (by ys_auto : YSK [] (fl4SyscallFaultIP (Z := Unit) σ.curThread)) σ ((YSL.nil_iff σ).2 hY) w hw

/-- **The entry half at boot**: the initial state's current thread does not yield. -/
theorem boot_curYieldNone : CurYieldNone (initASt (Z := Unit)) := by
  intro x hp
  simp only [initASt, initKheap, Function.update_apply] at hp
  split_ifs at hp <;> first | (cases hp; done) | (cases hp; rfl)

end

end Fl4Proofs.P3.SInv
