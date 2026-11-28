/-
P3 (DESIGN.md §9), invariant line G4 (g4a, KENTRY-PLAN g4a; INV-PLAN §4
"G4" and the 2026-11-20 lead decision): **`kernel_entryJ35`** and the
induction **`JReach` / `jreach_inv` / `kernel_entry_reach`**, started from ANY
state satisfying the carried invariants (not from `initASt`).

* **`SInvX σ := SInvW σ ∧ RPos σ`** (spec-only): rd14h's bundle `SInvW` and
  epq2's `RPos` (l4v `valid_refills`, sporadic part), the one spec field
  `EpQAll` needs beyond `SInvW`. `kentry_sinvX` / `kcall_sinvX`: kept by the
  syscall entry and every event (rd14h's `kentry_rdyOff9` / `kcall_rdyOff9`,
  epq2's `kentry_rpos` / `kcall_rpos`; inputs `numDomains = 1` and the
  non-idle scope). `boot_sinvX` is a non-vacuity check only.
* The per-state spec premises of `kernel_entryJ34` as projections of `SInvX`:
  `SInvX.entered` (`Entered σ` from SInvCR's `RS` and `ct ≠ idle`),
  `SInvX.sb` (SInvB), `SInvX.ctQ` (ct in no ready queue), `SInvX.epQAll`
  (`epQAll_of`), and `offReady_faultIPSt` (`OffReady` across the FaultIP
  write, which touches ct's TCB only).
* `KDispHypsKV35`: `KDispHypsKV33` without `JEntryGlobM32` (every field of it
  is a premise of the top: ten duplicates of the [P] / [S] premises, and
  `ArchRefines` / `PortInVal` [P], now top-level) and with `JPathAtM35`
  (`JPathAtM` asked only for native caps: the Vcpu / Ept / owned IoPort /
  mapped EPT-frame cases are refuted by `J.ext.nat` at the dispatch state).
* **`kernel_entryJ35`**: `kernel_entryJ34` from `JAtZ`, `ct ≠ idle` [S],
  `MR`, `SInvX`, the [P] bundle, the [S] scope and the remaining open
  per-state bundles `hK` / `hFin` (KENTRY-PLAN g4a (1), class (d)); its post
  is `KPostX`: the spec entry fails, or an outcome σ' with `RJ` and `SInvX σ'`.
* **`JReach`**: `start` (any `JAtZ ∧ SInvX ∧ MR` state) and `step` (a native
  syscall from a non-idle thread whose FL4 run ends in `(s', a')` and whose
  spec outcome σ' is related by `RJ`, with `MR` at the exit — the one carry
  `KPost` does not give, KENTRY-PLAN g4a (d) T4). **`jreach_inv`**: every
  reachable state carries `JAtZ` (at some ghosts) ∧ `SInvX` ∧ `MR`.
  **`kernel_entry_reach`**: at every reachable state, at the ghosts the
  invariant gives, the syscall entry refines the spec and every related exit
  is reachable again (given `MR` there).
-/
import Fl4Proofs.P3.XTopJointKEntry33
import Fl4Proofs.P3.XTopJointKEntry30D
import Fl4Proofs.P3.SpecInvRd14hC
import Fl4Proofs.P3.SpecInvEqS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G4
open Fl4Spec Fl4Proofs.P3.SInvR.B8w

noncomputable section

/-! ## The carried spec bundle -/

/-- **The carried spec invariant of G4** (module docstring). -/
abbrev SInvX (σ : State Unit) : Prop := SInvW σ ∧ SInvE.RPos σ

/-- `SInvX` at boot (non-vacuity only; G4 starts from any `SInvX` state). -/
theorem boot_sinvX : SInvX (initASt (Z := Unit)) := ⟨boot_sinvW, SInvE.boot_rpos⟩

variable {σ : State Unit}

theorem SInvX.w (h : SInvX σ) : SInvW σ := h.1

theorem SInvX.sb (h : SInvX σ) : SInvAll.SInvB σ := h.1.sb

theorem SInvX.cq (h : SInvX σ) : SInvAll.SInvCQ σ := h.1.1.1.1.1

theorem SInvX.cr (h : SInvX σ) : SInvAll.SInvCR σ := h.1.1.1.1

theorem SInvX.ctQ (h : SInvX σ) : ∀ d p, σ.curThread ∉ σ.readyQueues d p := SInvAll.SInvCQ.ctQ h.cq

theorem SInvX.entered (h : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) : Entered σ :=
  SInvAll.SInvCR.entered h.cr hct

theorem SInvX.offReady (h : SInvX σ) : Sched.OffReady σ := h.1.2.2.1

theorem SInvX.epQAll (h : SInvX σ) : SInvE.EpQAll σ :=
  SInvE.epQAll_of h.1.2.1 h.1.a.scInv h.1.a.epq h.2

/-- **`SInvX` at every outcome of the syscall entry.** -/
theorem kentry_sinvX (hnd : numDomains = 1) (c : Syscall) (h : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvX y.2 := fun y hy =>
  ⟨A14h.kentry_rdyOff9 hnd c h.1 hct y hy, SInvE.kentry_rpos true c h.2 h.1.2.1 h.1.a.scInv y hy⟩

/-- **`SInvX` at every outcome of every kernel event.** -/
theorem kcall_sinvX (hnd : numDomains = 1) (rep : Bool) (ev : Event) (h : SInvX σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvX y.2 := fun y hy =>
  ⟨A14h.kcall_rdyOff9 hnd rep ev h.1 hev y hy, SInvE.kcall_rpos rep ev h.2 h.1.2.1 h.1.a.scInv y hy⟩

/-- **`OffReady` across the FaultIP write** (module docstring): the write
replaces ct's TCB; the current SC, its refills and the times are kept (if the
current SC pointer were ct, it would name a TCB after the write, so the claim
is vacuous there). -/
theorem offReady_faultIPSt {t : ObjRef} {x : Tcb} (h : Sched.OffReady σ) :
    Sched.OffReady (faultIPSt σ t x) := by
  intro y n hy
  by_cases e : σ.curSc = t
  · exfalso
    have : (faultIPSt σ t x).kheap (faultIPSt σ t x).curSc = some (.tcb (Notif.setReg x .faultIP
        (x.tcbArch.tcbContext.userRegs .nextIP - 2))) := by
      show Function.update σ.kheap t _ σ.curSc = _
      rw [e, Function.update_self]
    rw [this] at hy; cases hy
  · have hy' : σ.kheap σ.curSc = some (.schedContext y n) := by
      have : (faultIPSt σ t x).kheap (faultIPSt σ t x).curSc = σ.kheap σ.curSc := by
        show Function.update σ.kheap t _ σ.curSc = _
        rw [Function.update_of_ne e]
      rw [← this]; exact hy
    exact h y n hy'

end

end Fl4Proofs.P3.SInvR.G4

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## The dispatch bundle without the platform part, native caps only -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtM` asked only for native caps** (module docstring): the cap
kinds `JExt.nat` excludes from every slot (Vcpu, Ept, an IoPort owned by a
VCPU, a mapped EPT frame) ask nothing. -/
def JPathAtM35 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c →
      JPathM (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

/-- **`KDispHypsKV33` without `JEntryGlobM32`, with `JPathAtM35`** (module
docstring). -/
structure KDispHypsKV35 (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR3 (L := L) arI AR Z s a σ ∧
    JPathAtM35 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR3 (L := L) arI AR Z s a σ ∧
    JPathAtM35 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct

variable {arI}

/-- `JPathAtM` from `JPathAtM35` at a `JAtZ` state: the invoked slot is a
slot of the typed heap, so its cap is native (`J.ext.nat`). -/
theorem JPathAtM35.toM {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtM35 (L := L) arI AR Z H Cs D s a σ ct ic bl cd fp cptr) :
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs hsl hc hg hr he
  have hN : Vs.NativeCap c := by
    obtain ⟨p, h1', h2'⟩ := id hsl
    have hx : IsSlot Z.th (cslotAddr sl) := AbsSlot.isSlot ⟨p, h1', Or.inl h2'⟩
    have := J.ext.nat _ hx
    rwa [capV_of_capAt hc] at this
  exact h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs hsl hc hg hr he hN

/-- **`JEntryGlobM32` from the top's [P] / [S] premises** (every field a
duplicate, but `archRef` and `portIn`). -/
theorem jEntryGlobM32_of {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} (th : TypedHeap) (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPA : PPPlatA arI AR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) : JEntryGlobM32 arI AR MR th :=
  ⟨hARI, hA, ⟨hRef, hARI.toARKeep, ⟨hmax, htu⟩⟩, hnd, hPA, ⟨hnd⟩, hPI, hT, hmax, htu⟩

theorem KDispHypsKV35.to33 {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets}
    {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {n : I64} {c : Fl4Spec.Syscall} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hG : JEntryGlobM32 arI AR MR Z.th) (h : KDispHypsKV35 (L := L) arI AR MR Z H Cs D s a σ n c) :
    KDispHypsKV33 (L := L) arI AR MR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hI => let ⟨e, p, v⟩ := h.inv ct call bl don hct hI; ⟨hG, e, p.toM J, v⟩,
    fun ct rg sr cr hct hM => let ⟨e, p, v⟩ := h.mid ct rg sr cr hct hM; ⟨hG, e, p.toM J, v⟩⟩

end

/-! ## The top -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

variable (arI) in
/-- **The entry's post with the carried spec bundle at the chosen outcome**:
the spec entry fails, or an outcome is related (`RJ`: RelTopM ∧ JAt) and
satisfies `SInvX`. -/
def KPostX (AR : A → Fl4Spec.Cr3 → Prop) (c : Fl4Spec.Syscall) (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).2 ∨
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ'

end

/-! ## The induction -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states** (INV-PLAN §4 "Target statement", with the
lead's 2026-11-20 decision): `start` is ANY state with `JAtZ` at some ghosts,
the carried spec bundle `SInvX` and the platform relation `MR`; `step` is a
native syscall from a non-idle thread whose FL4 entry returns `(s', a')`,
with a spec outcome `σ'` of the entry related to it by `RJ` and `MR` at the
exit ([W]: the one carry `KPost` does not give, KENTRY-PLAN g4a T4). -/
inductive JReach : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → SInvX σ → MR a σ.machineState → JReach s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReach s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJ (L := L) arI AR s' a' σ' → MR a' σ'.machineState → JReach s' a' σ'

variable {arI AR MR}

end

end

end Fl4Proofs.P3
