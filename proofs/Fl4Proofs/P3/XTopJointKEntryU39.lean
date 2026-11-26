/-
P3 (line p3J, gen 5): **`kernel_entry_reachU39`** = `kernel_entry_reachU38` with the per-entry [P] fields
`JEntryAtR7W.map` / `.mapr` (IOAPIC routing succeeds) stated once, at the backend level.

* `JEntryAtR7W`'s two fields mention only the arch `arI` (they quantify every arch state `a`; the joint state,
  ghosts and spec state are phantom), so asking them per entry, at every dispatch state of an invocation, asks
  one backend fact again and again. **`IoaMap arI`** [P] (platform premise, global): exactly those two fields
  (FL4 x86_64 `arch.rs` `ioapic_map` / `ioapic_map_remapped`: in range (`ioapic < count()`, `pin < pins(ioapic)`,
  level / polarity bits, handle below 2^16) the routing writes the redirection entry and answers `true`).
* `KDispHypsKVU39` = `KDispHypsKVU38` without `JEntryAtR7W` (only the `JPathAtMU35` path [J]s in `inv` and
  `mid`); `KDispHypsKVU39.toU38` (from `IoaMap`), `KDispHypsKVU38.toU39` (dropped).

**Premise diff U38 → U39**: new global premise `hMap : IoaMap arI` [P]; in the syscall clause
`KDispHypsKVU38 …` ↦ `KDispHypsKVU39 …` (`map`, `mapr` removed in `inv` and `mid`). Start condition
(`JReachU38`) and conclusion verbatim. [W] 0. The global premise is not weaker than the per-entry one: U38 asks
it only when an invocation is dispatched, U39 always; at any platform where some entry dispatches an invocation
the two coincide (`IoaMap.of_entry`).

Named premises: those of U38 (module XTopJointKEntryU38: the platform premises [P], the start condition
`JReachU38` with `IoaRel` [P], the per-entry syscall [J]s `KDispHypsKVU39` (path), `JDecMRLK`, `KFinAtR13`, the
event [J]s `KFinEv13`) plus `IoaMap` [P].
No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU38
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **IOAPIC routing succeeds in range** [P] (module docstring; platform premise, global): `JEntryAtR7W`'s
fields, which mention only the backend. -/
structure IoaMap : Prop where
  /-- [P] `ArchIrqRelN.map`: in-range IOAPIC routing succeeds and routes (`true`). -/
  map : ∀ (a : A) (n i p l po v np : U64), arI.num_ioapics a = ok n → ¬ i >= n → arI.ioapic_pins a i = ok np →
    ¬ p >= np → ¬ l > 1#u64 → ¬ po > 1#u64 → ∃ a', arI.ioapic_map a i p l po v = ok (true, a')
  /-- [P] `ArchIrqRelN.mapr`: the remapped form. -/
  mapr : ∀ (a : A) (n i p l po v h np : U64), arI.num_ioapics a = ok n → ¬ i >= n → arI.ioapic_pins a i = ok np →
    ¬ p >= np → ¬ l > 1#u64 → ¬ po > 1#u64 → ¬ h >= 65536#u64 →
    ∃ a', arI.ioapic_map_remapped a i p l po v h = ok (true, a')

/-- **`KDispHypsKVU38` without `JEntryAtR7W`**: the path [J]s only. -/
structure KDispHypsKVU39 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  /-- [J] as `KDispHypsKVU38.inv` without `map` / `mapr`. -/
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JPathAtMU35 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  /-- [J] as `KDispHypsKVU38.mid` without `map` / `mapr`. -/
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JPathAtMU35 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

/-- `JEntryAtR7W` is `IoaMap` (at any joint state). -/
theorem IoaMap.toW (hM : IoaMap arI) {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} : JEntryAtR7W (S := S) arI AR Z s ar σ :=
  ⟨hM.map, hM.mapr⟩

/-- `IoaMap` from one `JEntryAtR7W` (any joint state): the per-entry and the global premise coincide as soon
as one entry asks it. -/
theorem IoaMap.of_entry {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (h : JEntryAtR7W (S := S) arI AR Z s ar σ) : IoaMap arI :=
  ⟨h.map, h.mapr⟩

/-- **`KDispHypsKVU39` gives `KDispHypsKVU38`** under `IoaMap`. -/
theorem KDispHypsKVU39.toU38 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU39 (L := L) arI AR Z H Cs D s a σ n c) (hM : IoaMap arI) :
    KDispHypsKVU38 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => ⟨hM.toW, h.inv ct call bl don hct hi⟩,
   fun ct rg sr cr hct hm => ⟨hM.toW, h.mid ct rg sr cr hct hm⟩⟩

/-- **`KDispHypsKVU38` gives `KDispHypsKVU39`** (fields dropped). -/
theorem KDispHypsKVU38.toU39 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU38 (L := L) arI AR Z H Cs D s a σ n c) :
    KDispHypsKVU39 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => (h.inv ct call bl don hct hi).2,
   fun ct rg sr cr hct hm => (h.mid ct rg sr cr hct hm).2⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU39`** (module docstring): U38 with `map` / `mapr` as the global `IoaMap`. -/
theorem kernel_entry_reachU39 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatK arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hMap : IoaMap arI)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU38 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvIB.IrqCapBound σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU39 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU38 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU38 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU38 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU38 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU38 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU38 (L := L) arI AR MR r.1 r.2 σ' ⦄)   := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, hSys, hRest⟩ :=
    kernel_entry_reachU38 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, ?_, hRest⟩
  intro n c hct hn hfl hK hDL hFin
  exact hSys n c hct hn hfl (fun σb hb V' Ac' Lst' D' s' a' hF J' =>
    (hK σb hb V' Ac' Lst' D' s' a' hF J').toU38 hMap) hDL hFin

end

end

end Fl4Proofs.P3.SInvR.G5
