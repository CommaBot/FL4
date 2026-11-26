/-
P3 (line p3J, gen 15): **what U45nv's per-entry path premise still asks at the root-thread witness**: exactly
K6 at the root's thread cap invoked with label `TCBSetEPTRoot`; every other invocation is covered.

`kernel_entry_reachU45nv`'s syscall clause, at a state `σ` reached by `JReachU40`, takes per entry (besides the
TRAP_SYSCALLS flag fact) `∀ σb, BudgetAt σ σb true → … → KDispHypsKVU44 … σb n c`, whose leaves
(`JPathMEU44`, XTopJointKEntryU44) are, at the invoked cap: SchedControl `cpu = Z.c` (K1 [S]), Untyped VT-x scope
∧ core 0 (K3 [scope] / K4 [S]), Thread at `TCBSetEPTRoot` `JVtxScope` (**K6** [scope]), Frame EPT `JVtxScope`
(K7 [scope]), everything else `True`.

* `JPathAtMU44w W` / `KDispHypsKVU44w W`: `JPathAtMU44` / `KDispHypsKVU44` (same binder chain, verbatim) with
  one more antecedent `W info.label c` on the label and the invoked cap. **`KDispHypsKVU44.of_w`**: the `W` and
  the `¬ W` instances give `KDispHypsKVU44` (by cases on `W`), so the pair splits the premise exactly.
* `NK6 lbl c := ∀ p, c = .Thread p → lbl ≠ TCBSetEPTRoot` (not the K6 case); the K6 case is `¬ NK6`, i.e. a
  thread cap at label 88, where `JPathMEU44` is K6's `JVtxScope` and nothing else.
* `budgetAt_capOpt`: the FaultIP write and a passing budget check (`BudgetAt σ σb true`) keep every slot's cap
  (`SInvV.hv_fl4SyscallFaultIP` at the frame `hV · = hV σ`; `specBudget_true_shape`: the heap is unchanged).
* **`kDispHypsKVU44w_σ1`** (no premise but `numDomains = 1`, which U45nv itself takes and `u40_w1I1` gives):
  at every dispatch state `σb` of the first entry from the root-thread witness `σ1` (`BudgetAt σ1 σb true`),
  for every arch, ghost set, FL4 state, syscall and invoked cap, `KDispHypsKVU44w NK6` holds: `σ1`'s caps are
  null or the root's CNode / thread / SC caps (`capAt1`), so no SchedControl, Untyped or Frame cap is ever the
  invoked one, and a thread cap off label 88 asks nothing.
* **`kDispHypsKVU44_σ1_of_k6`**: so at those states `KDispHypsKVU44` is equivalent to its K6 part
  `KDispHypsKVU44w (¬ NK6 · ·)`: the root thread invoking its own thread cap (the only thread cap in `σ1`) with
  label `TCBSetEPTRoot`. That part stays an undischarged [scope] premise: the port has no TCB label 88
  (`specDec_ept_noOk`, P3JVtxMR), so `JVtxScope` there asks FL4's EPT-root decode (`tcb.rs:410-420`, which
  can end in `Ok ()`) to match a spec outcome that does not exist; it is not provable from the chain and is
  not weakened here.

Named premises: none new. K6 [scope] remains (stated, not assumed, by `kDispHypsKVU44_σ1_of_k6`'s hypothesis).
Scope: the first entry from `σ1` (later entries need the cap set carried along the run: open). No sorry.
New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootQ1U40
import Fl4Proofs.P3.XTopJointKEntryU46
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtMU44` with one more antecedent `W info.label c`** (module docstring). -/
def JPathAtMU44w (W : U64 → capability.Cap → Prop) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (ct : U64) (is_call blocking can_donate first_phase : Bool) (cptr : U64) : Prop :=
  ∀ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef)
    (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
    (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) (argsU : List U64),
    msg.msg_info st s ct = ok info →
    Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False) →
    msg.lookup_ipc_buffer st s false ct = ok buf →
    Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False) →
    ipc.lookup_extra_caps st s ct buf info = ok r2 →
    (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False) →
    Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(argsU.map UScalar.bv, σ)}, False) →
    ∀ (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
      (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
      capAt (L.mem s) (cslotAddr sl) = ok c → Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) →
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c → W info.label c →
      JPathMEU44 (L := L) arI AR Z s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

/-- **`KDispHypsKVU44` on `JPathAtMU44w W`.** -/
structure KDispHypsKVU44w (W : U64 → capability.Cap → Prop) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JPathAtMU44w (L := L) arI W AR Z s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JPathAtMU44w (L := L) arI W AR Z s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

theorem JPathAtMU44w.of_w {W : U64 → capability.Cap → Prop} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S}
    {ar : A} {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (h1 : JPathAtMU44w (L := L) arI W AR Z s ar σ ct ic bl cd fp cptr)
    (h2 : JPathAtMU44w (L := L) arI (fun l c => ¬ W l c) AR Z s ar σ ct ic bl cd fp cptr) :
    JPathAtMU44 (L := L) arI AR Z s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl c e exs a8 a9 a10 a11 a12 a13 a14
  by_cases hW : W info.label c
  · exact h1 info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl c e exs a8 a9 a10 a11 a12 a13 a14 hW
  · exact h2 info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl c e exs a8 a9 a10 a11 a12 a13 a14 hW

/-- **The `W` and `¬ W` halves give `KDispHypsKVU44`.** -/
theorem KDispHypsKVU44.of_w {W : U64 → capability.Cap → Prop} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h1 : KDispHypsKVU44w (L := L) arI W AR Z H Cs D s a σ n c)
    (h2 : KDispHypsKVU44w (L := L) arI (fun l c => ¬ W l c) AR Z H Cs D s a σ n c) :
    KDispHypsKVU44 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => (h1.inv ct call bl don hct hi).of_w (h2.inv ct call bl don hct hi),
   fun ct rg sr cr hct hm => (h1.mid ct rg sr cr hct hm).of_w (h2.mid ct rg sr cr hct hm)⟩

end

/-- **Not the K6 case**: the invoked cap is no thread cap, or the label is not `TCBSetEPTRoot`. -/
def NK6 (lbl : U64) (c : capability.Cap) : Prop := ∀ p, c = .Thread p → lbl ≠ fl4_abi.label.TCBSetEPTRoot

/-- **The FaultIP write and a passing budget check keep every slot's cap.** -/
theorem budgetAt_capOpt (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (h : BudgetAt σ σb true)
    (p : Fl4Spec.ObjRef) (cref : Fl4Spec.CnodeIndex) : capOpt (σb.kheap p) cref = capOpt (σ.kheap p) cref := by
  obtain ⟨σ0, h0, hb⟩ := h
  rw [(specBudget_true_shape hnd hb).1]
  exact SInvV.hV_cap
    ((SInvV.hv_fl4SyscallFaultIP (P := fun x => SInvV.hV x = SInvV.hV σ) σ.curThread) σ rfl _ h0) p cref

end

end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.JBootQ
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **Every invocation but K6 is covered at the dispatch states of the first entry from `σ1`** (module
docstring). -/
theorem jPathAtMU44w_σ1 (hnd : Fl4Spec.numDomains = 1) {σb : Fl4Spec.State Unit} (hb : BudgetAt σ1 σb true)
    {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A} {ct : U64} {ic bl cd fp : Bool} {cptr : U64} :
    JPathAtMU44w (L := L) arI NK6 AR Z s ar σb ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU _ _ _ _ _ _ _ sl c e exs _ _ hgc _ _ _ _ hW
  have hcap : capOpt (σ1.kheap sl.1) sl.2 = some (absCap c) := by
    rw [← budgetAt_capOpt hnd hb]
    obtain ⟨o, i⟩ := sl
    exact (getCap_set_iff σb o i (absCap c)).1 (congrArg Prod.fst hgc)
  have h1 := capAt1 (sl := sl) (c := absCap c) (by rw [SInvUZ.capAt_capOpt]; exact hcap)
  cases c
  all_goals first
    | (intro h; exact absurd h (hW _ rfl))
    | trivial
    | (exfalso; rcases h1 with e1 | ⟨-, e1⟩ | ⟨-, e1⟩ | ⟨-, e1⟩ <;> simp [absCap] at e1; done)

/-- **`KDispHypsKVU44w NK6` at every dispatch state of the first entry from `σ1`.** -/
theorem kDispHypsKVU44w_σ1 (hnd : Fl4Spec.numDomains = 1) {σb : Fl4Spec.State Unit} (hb : BudgetAt σ1 σb true)
    {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A} {n : I64}
    {c : Fl4Spec.Syscall} : KDispHypsKVU44w (L := L) arI NK6 AR Z H Cs D s a σb n c :=
  ⟨fun _ _ _ _ _ _ => jPathAtMU44w_σ1 hnd hb, fun _ _ _ _ _ _ => jPathAtMU44w_σ1 hnd hb⟩

/-- **At those states `KDispHypsKVU44` is its K6 part**: given the K6 case (the root thread's own thread cap
invoked at label `TCBSetEPTRoot`, [scope], not discharged), the per-entry premise of U45nv holds. -/
theorem kDispHypsKVU44_σ1_of_k6 (hnd : Fl4Spec.numDomains = 1) {σb : Fl4Spec.State Unit}
    (hb : BudgetAt σ1 σb true) {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {n : I64} {c : Fl4Spec.Syscall}
    (hK6 : KDispHypsKVU44w (L := L) arI (fun l c => ¬ NK6 l c) AR Z H Cs D s a σb n c) :
    KDispHypsKVU44 (L := L) arI AR Z H Cs D s a σb n c :=
  KDispHypsKVU44.of_w (kDispHypsKVU44w_σ1 hnd hb) hK6

/-- The converse: `KDispHypsKVU44` gives its K6 part (so the K6 part is exactly what is left). -/
theorem kDispHypsKVU44_k6 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σb : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU44 (L := L) arI AR Z H Cs D s a σb n c) :
    KDispHypsKVU44w (L := L) arI (fun l c => ¬ NK6 l c) AR Z H Cs D s a σb n c :=
  ⟨fun ct call bl don hct hi info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl c e exs a8 a9 a10 a11 a12 a13
      a14 _ => h.inv ct call bl don hct hi info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl c e exs a8 a9 a10
      a11 a12 a13 a14,
   fun ct rg sr cr hct hm info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl c e exs a8 a9 a10 a11 a12 a13
      a14 _ => h.mid ct rg sr cr hct hm info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl c e exs a8 a9 a10
      a11 a12 a13 a14⟩

end

/-- **U45nv applies at the root-thread witness** (its start is `u40_w1I1`'s, `NoVirt` is `noVirt_warI1`): the
joint invariant it concludes, under the global opaque [P]s `OpaqueWK`, `FpuImplDet`, `FpuWriteDet`,
`KCfgFL4`. -/
theorem u45nv_w1I1 (O : OpaqueWK) (hFpu : Sched.FpuImplDet) (hFW : FpuWriteDet) (hCfg : KCfgFL4) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := wL) warI1 wAR Z H Cs Ac Lst D w1 σ1.machineState σ1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hJ⟩ := u40_w1I1 O
  obtain ⟨Z, H, Cs, Ac, Lst, D, hZ, -⟩ :=
    kernel_entry_reachU45nv warI1 wAR ipiMR h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 hFpu hFW hCfg
      noVirt_warI1 hJ
  exact ⟨Z, H, Cs, Ac, Lst, D, hZ⟩

end

end Fl4Proofs.P3.JBootQ
