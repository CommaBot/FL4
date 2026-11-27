/-
# P2 (line p3mc, gen 31): the word-level YieldBlock `YBW` is kept by every FL4 kernel entry P3 covers

Gen 30 (P2/E2EPV13) stated V13's last [J] `ybw` on FL4's words: **`YBW st Kl s`**, every TCB of `Kl`'s heap with
`YIELD_TO` (offset 3472) ≠ 0 has a `STATE` (offset 3328) not in {3, 4, 5, 6}. This module proves that the word fact
is kept by FL4's kernel entries, at the word level, together with its entry half **`CYW`** (the current thread's
`YIELD_TO` word is 0, the word form of P3's `CurYieldNone`; `activate_thread`, `sched.rs` l.689–690, clears it before
a thread runs).

## Route: through P3's refinement, not P1's footprints
P1's footprints (`KW` / `KWN` / `FootN`, P2/FootN*) say *which* words a function may write, not *what* it writes:
`STATE` and `YIELD_TO` are both in every TCB-writing footprint (`set_thread_state`, `set_yield_to` targets), so no
footprint lemma can show that a blocked state is written only to a thread whose yield is 0. A value-level P1 proof
would restate, function by function, P3's YieldBlock proofs (P3/SpecInvYieldBlockT/F1..F4/H, ~4k lines) on words.
Instead the word fact is moved to and from P3's spec fact at every joint state:
* **`ybwH_of_yb`** / **`yb_of_ybwH`**: at a `JAtZ` state, `YBWH H s` (the word form over the joint heap `H`) iff
  P3's `YieldBlockS σ` (`JAtZ.tcbs_eq`: `Z.T` = `H`'s TCBs; `TcbRel.st` reads the state word, `YieldRel.tcb` the
  yield word; every spec TCB is a `Z.T` TCB, `JAtZ.obj.tcb`).
* **`cyw_of_cyn`** / **`cyn_of_cyw`**: `CYW s` iff `CurYieldNone σ` (`JKern.cur`, `JKern.curT`, `YieldRel.tcb`).
* **`jreachYB_of_ybw`**: a reachable joint state (`JReachU17`) with the two word facts at one of its bundles is a
  `JReachYB` state; **`JReachYB.ybw`**: at a `JReachYB` state the word facts hold at **every** bundle.

## Proved
* **`kernel_entry_ybwU29`**: P3's `kernel_entry_yieldScope2U29` with its `JReachYB` hypothesis replaced by the word
  facts (`JReachU17`, a bundle, `YBWH`, `CYW`), and each of its six posts strengthened by the word facts at every
  exit bundle (`YbwPost`): **`YBW` before implies `YBW` after** for
  1. `handle_syscall`, every native syscall (`NativeSys`), from a non-idle current thread;
  2. `handle_interrupt_entry` (any current thread);
  3. `handle_user_exception`; 4. `handle_vm_fault`; 5. `handle_trap_syscall`;
  6. `handle_syscall`, every unknown syscall (`UnkSys`, `NoDbgSys`).
  Premises: exactly `kernel_entry_reachU29`'s (P3's platform [P]s and per-entry hypotheses), nothing new.
* **`ybw_yBOut`**: the local runs (the chain's step relation): a spec outcome of `YBOut` shape (`loc_chain_all`'s
  clauses 2–6 and 8–10: the trap arm, ReplyRecv fast path, I/O port, `TCB_SetTimer`, the timer interrupt,
  invocations, VM fault, VM ReplyRecv) from a reachable bundle with the word facts lands, at every bundle of its
  target state, in the word facts (`ybOut_keep`, `SInvX` from `jreach_invU3`).
* **`ybw_of_jreachYB`**: `JReachYB` gives `YBW` at the layout of any clause-7 bundle (`SlJAtZ`) at that state, the
  form the vmF / vmR / sl records ask.

## Not covered (the entries / steps these do not reach)
* States that are not `JReachU17` (P3 covers no other store state), so in particular the execution's physical
  memory between P2 steps (only P3 chain states and exits are joint states).
* The fl4-sync glue (dispatcher, `with_locks`, the plan checks): not extracted.
* Serial bodies as P2 sees them: `Serial.Step.serial` runs an arbitrary `Run p`; P3 covers the kernel entry, but
  nothing ties P2's serial step to it (`serX` [P] picks *some* `JReachU17` exit).
* Other cores' steps as seen from core `c`'s view (the rely, handoff §3 R1): P3 is a per-core refinement; a local run
  of core `d` is covered at `d`'s view only.
* Boot at the store level: P3 has `boot_yieldBlock'` at the spec's `initASt` only, no store-state boot (handoff §35e,
  `hB`).
* `handle_syscall` / `handle_user_exception` / `handle_vm_fault` / `handle_trap_syscall` from the idle thread (the
  posts' `σ.curThread ≠ σ.idleThread`, as in P3).

No premise added ([J]/[P]/[W]); no existing statement changed (root import list only).
-/
import Fl4Proofs.P2.E2EPV13
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section words
variable {S : Type} (st : machine.Store S) [L : P1.LawfulStore st]

/-- **The word-level YieldBlock over a heap**: `E2EP.YBW` at the layout's heap (`ybw_iff`). Every TCB of `H` whose
`YIELD_TO` word is nonzero has a `STATE` word coding no blocked state (3 receive, 4 send, 5 reply, 6 notification). -/
def YBWH (H : P1.Heap) (s : S) : Prop :=
  ∀ t ∈ P1.Heap.tcbs H, L.mem s (Fl4Proofs.P1.yieldA t) ≠ 0#u64 →
    ¬ ((L.mem s (tStA t)).val = 3 ∨ (L.mem s (tStA t)).val = 4 ∨
      (L.mem s (tStA t)).val = 5 ∨ (L.mem s (tStA t)).val = 6)

/-- **The current thread's `YIELD_TO` word is 0** (the word form of `CurYieldNone`). -/
def CYW (s : S) : Prop := L.mem s (Fl4Proofs.P1.yieldA (L.curW s)) = 0#u64

theorem ybw_iff (Kl : Fl4Proofs.P2.OwnMap.KLayout) (s : S) :
    Fl4Proofs.P2.E2EP.YBW st Kl s ↔ YBWH st Kl.heap s := Iff.rfl

end words

section joint
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **YieldBlock gives the word form** at a joint state (`JAtZ.tcbs_eq`, `JAtZ.yield0_blk`). -/
theorem ybwH_of_yb (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hY : SInv.YieldBlockS σ) : YBWH st H s := by
  intro t ht h0 hb
  have htT : t ∈ Z.T := by rw [J.tcbs_eq.1]; exact ht
  exact h0 (JAtZ.yield0_blk J hY htT hb)

/-- **The word form gives YieldBlock** at a joint state (every spec TCB is a `Z.T` TCB of `H`; its state and yield
are read off the words, `TcbRel.st`, `YieldRel.tcb`). -/
theorem yb_of_ybwH (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (h : YBWH st H s) : SInv.YieldBlockS σ := by
  intro p x hk hy
  obtain ⟨t, ht, rfl⟩ := J.obj.tcb p x hk
  obtain ⟨x1, hk1, hr⟩ := J.xtop.ipc.tcb t ht
  obtain ⟨x2, hk2, hyr⟩ := J.yld.tcb t ht
  rw [hk] at hk1 hk2
  cases hk1
  cases hk2
  have htH : t ∈ P1.Heap.tcbs H := by rw [← J.tcbs_eq.1]; exact ht
  have h0 : L.mem s (Fl4Proofs.P1.yieldA t) ≠ 0#u64 := by
    intro e
    apply hy
    rw [hyr, e]
    unfold optRef
    simp
  have hb := h t htH h0
  rw [hr.st] at hb
  revert hb
  generalize x.tcbState = ts
  cases ts <;> simp [tsCode, SInv.notBlkSt]

/-- **`CurYieldNone` gives the word form** (`JKern.cur`, `YieldRel.tcb`). -/
theorem cyw_of_cyn (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hC : SInv.CurYieldNone σ) : CYW st s := by
  have hT := J.thT _ J.kern.curT
  obtain ⟨x2, hk2, hyr⟩ := J.yld.tcb _ hT
  have hn := hC x2 (by rw [J.kern.cur]; exact hk2)
  rw [hyr] at hn
  unfold optRef at hn
  unfold CYW
  by_contra h0
  rw [if_neg h0] at hn
  cases hn

/-- **The word form gives `CurYieldNone`.** -/
theorem cyn_of_cyw (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (h : CYW st s) : SInv.CurYieldNone σ := by
  intro x hk
  have hT := J.thT _ J.kern.curT
  obtain ⟨x2, hk2, hyr⟩ := J.yld.tcb _ hT
  rw [J.kern.cur, hk2] at hk
  cases hk
  rw [hyr]
  unfold CYW at h
  rw [h]
  unfold optRef
  simp

end joint

section reach
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- **A reachable joint state with the word facts at one bundle is a `JReachYB` state.** -/
theorem jreachYB_of_ybw {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : JReachU17 (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hW : YBWH st H s) (hC : CYW st s) :
    JReachYB (L := L) arI AR MR s a σ :=
  ⟨hR, yb_of_ybwH J hW, cyn_of_cyw J hC⟩

/-- **At a `JReachYB` state the word facts hold at every bundle.** -/
theorem JReachYB.ybw {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachYB (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : YBWH st H s ∧ CYW st s :=
  ⟨ybwH_of_yb J h.2.1, cyw_of_cyn J h.2.2⟩

/-- **A `JReachYB` state has a bundle** (`jreach_invU3`), so the word facts are not vacuous there. -/
theorem JReachYB.ybw_ex (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JReachYB (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ YBWH st H s ∧ CYW st s := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, -⟩ := jreach_invU3 hnd h.1.1
  exact ⟨Z, H, Cs, Ac, Lst, D, J, h.ybw J⟩

/-- **The word-level post of a kernel exit**: P3's `RJ ∧ JReachYB` at some spec state, and the word facts at every
bundle of the exit. -/
def YbwPost (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)
    (r : S × A) : Prop :=
  ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧ JReachYB (L := L) arI AR MR r.1 r.2 σ' ∧
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D r.1 r.2 σ' → YBWH st H r.1 ∧ CYW st r.1

theorem ybwPost_of {r : S × A}
    (h : ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧ JReachYB (L := L) arI AR MR r.1 r.2 σ') :
    YbwPost (st := st) arI AR MR r := by
  obtain ⟨σ', hRJ, hY⟩ := h
  exact ⟨σ', hRJ, hY, fun _ _ _ _ _ _ J => hY.ybw J⟩

end reach

section top
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 4000000 in
/-- **`YBW` is kept by every kernel entry P3 covers** (module docstring): at a reachable joint state with the word
facts at one bundle, each of the six entry kinds ends, under `kernel_entry_reachU29`'s hypotheses, in a `JReachYB`
exit with the word facts at every exit bundle. Premises: `kernel_entry_reachU29`'s, nothing new. -/
theorem kernel_entry_ybwU29 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : JReachU17 (L := L) arI AR MR s a σ)
    {Z0 : XSets} {H0 : P1.Heap} {Cs0 Ac0 : Set U64} {Lst0 : U64 → List U64} {D0 : Set U64}
    (J0 : JAtZ (L := L) arI AR Z0 H0 Cs0 Ac0 Lst0 D0 s a σ) (hW : YBWH st H0 s) (hC : CYW st s) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ YBWH st H s ∧ CYW st s ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU29 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r => YbwPost (st := st) arI AR MR r ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => YbwPost (st := st) arI AR MR r ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => YbwPost (st := st) arI AR MR r ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => YbwPost (st := st) arI AR MR r ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => YbwPost (st := st) arI AR MR r ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => YbwPost (st := st) arI AR MR r ⦄) := by
  have hJ := jreachYB_of_ybw hR J0 hW hC
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hY, hC', hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_yieldScope2U29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, ybwH_of_yb J hY, cyw_of_cyn J hC', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    exact WP.spec_mono (hSys n c hct hn hfl hK hDL hFin) fun r hr => ybwPost_of hr
  · intro w a1 hIh hE
    exact WP.spec_mono (hIrq w a1 hIh hE) fun r hr => ybwPost_of hr
  · intro n c hct hU hE
    exact WP.spec_mono (hUs n c hct hU hE) fun r hr => ybwPost_of hr
  · intro ad c ft hct hV hE
    exact WP.spec_mono (hVm ad c ft hct hV hE) fun r hr => ybwPost_of hr
  · intro v hct hv hE
    exact WP.spec_mono (hTr v hct hv hE) fun r hr => ybwPost_of hr
  · intro n hct hU hND hE
    exact WP.spec_mono (hSU n hct hU hND hE) fun r hr => ybwPost_of hr

variable {arI AR MR}

/-- **The chain's local runs keep the word facts** (module docstring): a `YBOut` spec outcome (each of
`loc_chain_all`'s local clauses 2–6, 8–10 gives one) from a reachable state with the word facts at one bundle ends,
at every bundle of the target, in the word facts. -/
theorem ybw_yBOut (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hR : JReachU17 (L := L) arI AR MR s a σ)
    {Z0 : XSets} {H0 : P1.Heap} {Cs0 Ac0 : Set U64} {Lst0 : U64 → List U64} {D0 : Set U64}
    (J0 : JAtZ (L := L) arI AR Z0 H0 Cs0 Ac0 Lst0 D0 s a σ) (hW : YBWH st H0 s) (hC : CYW st s)
    {σ' : Fl4Spec.State Unit} (hO : Fl4Proofs.P2.PathObl.YBOut σ σ') {s' : S} {a' : A}
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a' σ') : YBWH st H s' ∧ CYW st s' := by
  obtain ⟨-, -, -, -, -, -, -, hX, -⟩ := jreach_invU3 hnd hR.1
  have h2 := Fl4Proofs.P2.PathObl.ybOut_keep hX (yb_of_ybwH J0 hW) (cyn_of_cyw J0 hC) hO
  exact ⟨ybwH_of_yb J h2.1, cyw_of_cyn J h2.2⟩

end top

end

end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P2.PathObl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`YBW` at every clause-7 bundle of a `JReachYB` state whose spec state is the bundle's.** -/
theorem ybw_of_jreachYB {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {s : S} {a : A3} {σ : Fl4Spec.State Unit}
    (h : Fl4Proofs.P3.SInvR.G5.JReachYB (L := L) arI AR MR s a σ) {Kl : OwnMap.KLayout}
    {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D Kl s a σ) : YBW st Kl s :=
  ybw_of_bun B h.2.1

end
end Fl4Proofs.P2.E2EP
