/-
P3 (p3J gen 32, built gen 33): **the mid invocation's decode leaf split by the invoked cap; the cap kinds `CKI` excludes proved
unreachable**.

* **`MidDecStW W`**: P3JMidInv's `MidDecSt` with one more antecedent `W cp` on the looked-up cap (as JBootQ1Disp's
  `JPathAtMU44w`).
* **`midDecSt_of_w`**: at a dispatch state `CKI` holds (`MidDecSt`'s own antecedent), so the looked-up cap
  (`getCap sl σb` returns it: `getCap_set_iff`) is `KW` — no untyped, SchedControl, IRQ-control or arch cap; hence
  `MidDecStW (KW ∧ P)` and `MidDecStW (KW ∧ ¬ P)` give `MidDecSt` for any `P` (cases on `P`). The excluded kinds
  need no leaf.
* `IsReplyCap cp` (a Reply cap). **`DispStabFootLk` [J]** {inv, midDecReply (`MidDecStW (KW ∧ IsReplyCap)`),
  midDecOther (`MidDecStW (KW ∧ ¬ IsReplyCap)`), midSpec, midRecvSw}; **`dispStabFootLd_of_Lk`**; top
  **`kernel_entry_runMcWKR_sysLk`** (globals as `_sysLd`).

Narrowing honesty: `midDecReply` / `midDecOther` are `midDec` restricted by an antecedent (each implied by `midDec`;
together they imply it). Removed from the [J] content: the decode leaves of untyped, SchedControl, IRQ-control and
arch caps in the mid class (unreachable on `CKI` states).

Named premises: `DispStabFootLk` [J] (above; `MidDecStW` is its fields' shape). No sorry. New module; no existing
statement changed.
-/
import Fl4Proofs.P3.P3JMidInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- A Reply cap. -/
def IsReplyCap (cp : capability.Cap) : Prop := ∃ p g, cp = .Reply p g

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 32) **`MidDecSt` with one more antecedent on the looked-up cap** (module docstring). -/
def MidDecStW (W : capability.Cap → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64)
    (c : Fl4Spec.Syscall) : Prop :=
  ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
    KFrontB (L := L) arI s a s' a' → JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
    MR a' σb.machineState → SInvCk.CKI σb → SInvRr.RR σb →
    ∀ ct rg sr cr, sched.cur_thread st s' = ok ct → MidSysR n c rg sr cr →
    ∀ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef)
      (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
      (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) (argsU : List U64),
      msg.msg_info st s' ct = ok info →
      Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False) →
      msg.lookup_ipc_buffer st s' false ct = ok buf →
      Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False) →
      ipc.lookup_extra_caps st s' ct buf info = ok r2 →
      (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False) →
      Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σb = ({(argsU.map UScalar.bv, σb)}, False) →
      ∀ (sl : Fl4Spec.CslotPtr) (cp : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
        (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
        capAt (L.mem s') (cslotAddr sl) = ok cp → Fl4Spec.getCap (Z := Unit) sl σb = ({(absCap cp, σb)}, False) →
        r2 = .Ok e → er = .ok exs → W cp →
        XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
          info.label (msgLen info buf) (cslotAddr sl) cp false false true true buf e mi.miLabel
          (argsU.map UScalar.bv) (Fl4Spec.toBl (L.mem s' (regA ct rg)).bv) sl exs buffer ct

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

/-- (p3J gen 32) **The two halves of a split on `P` among the `KW` caps give `MidDecSt`** (module docstring). -/
theorem midDecSt_of_w (P : capability.Cap → Prop) {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {c : Fl4Spec.Syscall}
    (h1 : MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ P cp) Z H Cs s a σ n c)
    (h2 : MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ ¬ P cp) Z H Cs s a σ n c) :
    MidDecSt (L := L) arI AR MR Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs
  have hK : SInvCk.KW (absCap cp) := by
    obtain ⟨o, i⟩ := sl
    exact hCb o i (absCap cp) ((getCap_set_iff σb o i (absCap cp)).1 (congrArg Prod.fst hget))
  by_cases hP : P cp
  · exact h1 σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hK, hP⟩
  · exact h2 σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hK, hP⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 32) **`DispStabFootLk` [J]**: `DispStabFootLd` with the mid decode leaf split into the Reply cap and the
other `KW` caps (module docstring). -/
structure DispStabFootLk (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- The invoking class (`SysSend`, `SysNBSend`, `SysCall`), verbatim from `DispStabFootLw`. -/
  inv : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n (invSysOf call bl)
  /-- The mid decode leaf of a Reply cap. -/
  midDecReply : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsReplyCap cp) Z H Cs s a σ n c
  /-- The mid decode leaf of every other `KW` cap. -/
  midDecOther : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ ¬ IsReplyCap cp) Z H Cs s a σ n c
  /-- `DispStabFootLm.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLm.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 32) **`DispStabFootLk → DispStabFootLd`** (module docstring). -/
theorem dispStabFootLd_of_Lk {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLk (L := L) arI AR MR s a σ) :
    DispStabFootLd (L := L) arI AR MR s a σ where
  inv := h.inv
  midDec := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecSt_of_w IsReplyCap (h.midDecReply hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
      (h.midDecOther hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 32) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLk` only** (`hLk` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLk [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLk : DispStabFootLk (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLd hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLd_of_Lk hLk)

end

end Fl4Proofs.P3.Mc
