/-
P3 (DESIGN.md §9), invariant line g5b (KENTRY-PLAN g5b; g5a's handoff, INV-PLAN
§1.3 E8 / E9 / E17, P1): **`kernel_entryJ36E`** = `kernel_entryJ37` (the `MR`
carry of g4b) with `kernel_entryJ35E`'s reduced dispatch bundle, and the
induction `JReachI` / `jreach_invI` / `kernel_entry_reachI` over
`JAtZ ∧ SInvX ∧ SInvIR ∧ MR`.

Two of g5a's four spec-only entry facts (`SInvI`) are no longer asked:
* `SpecIrqH` (the IRQ handler caps' lines valid and not inactive): the bound
  `irq ≤ maxIRQ` was never needed (FL4's `CapValid` of an IRQ handler cap
  already bounds the line below 128, `handlersActive_of_vih`), and the rest
  is l4v `valid_irq_handlers`, already carried in `SInvX` (`SInvA.vih`, vih3's
  `kentry_validIrqMasks`). So `HandlersActive` is a theorem of `JAtZ` and
  `SInvX` (`JAtZ.handlersJV`).
* `SpecFrPg` (ReadFPU's destination frame in one spec data page): g5b
  restated XTopJointReadFpu's `FpuFrameJHyp` per byte (`UFr`), which is
  `JAtZ.fcap` at the slot (`JAtZ.fpuFrameJ`, no spec fact).
`flags` (`FlagsRel`, FL4's flags words vs the spec's `tcb_flags`) leaves the
dispatch bundle: asked at the entry state and carried to the dispatch state
(`flags_front`; `KDispHypsKV36E`, `JEntryAtR6`).
The Frame path's `hno` (`JFramePath`) likewise: `LargeFrOK` (every MDB
slot's large non-device frame cap against every MDB cap) at the entry state,
kept by the front (`front_slotsSame`, `LargeFrOK.of_same`), gives it at the
invoked slot (`JPathAtM36E.to35E`).
Left: **`SInvIR σ`** = `SpecIoP σ ∧ SpecUtZ σ` (l4v `valid_ioports`,
`untyped_ranges_zero`) [J] spec, asked at the entry and carried to the
dispatch state (`sinvIR_disp`). Their carry across a whole syscall is NOT
proved (KENTRY-PLAN g5b): `JReachI.step` asks `SInvIR` of the exit state
(the one open carry of this induction, like g4a's `MR` before g4b).
-/
import Fl4Proofs.P3.XTopJointKEntry37
import Fl4Proofs.P3.XTopJointKEntry35E
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **[J] FL4 (l4v `valid_cap` / the frame-cap overlap discipline,
INV-PLAN P8; `JFramePath.hno` for every MDB slot at once)**: every MDB slot's
large non-device frame cap is, against every MDB slot's physical cap,
disjoint from it, or that cap is a non-revocable frame cap, or it lies within
that cap. A statement about the state alone (no invocation): asked at the
entry state and carried to the dispatch state (`largeFr_front`). Since g5j
only physical caps are compared (the non-physical ones never meet the
`same_region_as` test `DeriveSubframe`'s `InsFCtx.k2` reads), and so it is a
theorem of every `JAtZ` (`JAtZ.largeFrOK`, XTopJointKEntryU2L: from
`NoOverlap` in `MdbOKV`). -/
def LargeFrOK (G : MdbGhost) (m : U64 → U64) : Prop :=
  ∀ y ∈ G.chains.flatten, ∀ (p rt : U64) (mp : Bool) (asid va : U64),
    capV m y = .Frame p .Large rt false mp false asid va → ∀ x ∈ G.chains.flatten, physF (capV m x) = true →
      Disj (capV m x) (.Frame p .Large rt false mp false asid va) ∨
      (isFrame (capV m x) = true ∧ revOf m x = false) ∨
      Within (.Frame p .Large rt false mp false asid va) (capV m x)

/-- `LargeFrOK` across a step keeping every slot of the typed heap. -/
theorem LargeFrOK.of_same {th : TypedHeap} {G : MdbGhost} {m m' : U64 → U64} (h : LargeFrOK G m)
    (hG : ∀ y ∈ G.chains.flatten, IsSlot th y) (hS : SlotsSame th m m') : LargeFrOK G m' := by
  intro y hy p rt mp asid va hc x hx hp
  have ex := hS.capV (hG x hx)
  have ey := hS.capV (hG y hy)
  have er : revOf m' x = revOf m x := by unfold revOf; rw [(hS x (hG x hx)).2.2.2]
  rw [ex] at hp
  rw [ex, er]
  exact h y hy p rt mp asid va (by rw [← ey]; exact hc) x hx hp

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {th : TypedHeap}

/-- **`HandlersActive` from l4v's `valid_irq_handlers` alone** (no `maxIRQ`
bound: FL4's `CapValid` of a handler cap gives the line below 128). -/
theorem handlersActive_of_vih {s : S} {kb : U64} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hR : StateRel th (L.mem s) σ) (hM : MdbLinks th (L.mem s) G) (hIR : IrqRel (L.mem s) kb σ)
    (hV : SInvV.ValidIrqHandlers σ) : HandlersActive (L.mem s) kb G := by
  intro y hy i hi
  obtain ⟨ysl, hys, rfl⟩ := ((hM.members _).1 hy).1.abs
  obtain ⟨c, ac, hc, hca, hg⟩ := hR.abs_cap hys
  rw [capV_of_capAt hc] at hi; subst hi
  have h128 : i.val < 128 := hca.1
  rw [hca.abs] at hg
  obtain ⟨-, hco⟩ := SInvV.vih_mem_getCap (o := ysl.1) (c := ysl.2) (x := (_, σ))
    (by rw [hg]; exact Set.mem_singleton _)
  have h2 := hV _ _ _ hco
  refine ⟨h128, fun h0 => h2 ?_⟩
  rw [hIR.st i h128, (irqSt_inactive _).2 h0]

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **`HandlersActive` at `J` from `SInvX`'s `valid_irq_handlers`.** -/
theorem JAtZ.handlersJV (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : SInvV.ValidIrqHandlers σ) :
    HandlersActive (L.mem s) (L.ksb s) Z.G :=
  handlersActive_of_vih J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.2.1 J.xtop.fin.1.1.2.2.2.1 hV

set_option maxHeartbeats 4000000 in
/-- **The FL4 front keeps every slot** (`front_writes`: `FAULT_IP` and two node
words, none a slot word; as in g2c's `liveDN_front`). -/
theorem front_slotsSame (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR)
    (hA : P0.ArchTotal arI) {s' : S} {a' : A} (hF : KFrontB (L := L) arI s a s' a') :
    SlotsSame Z.th (L.mem s) (L.mem s') := by
  obtain ⟨ct, v, hct, hb⟩ := hF
  have hw := front_writes J hAK hA hct hb
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hta := J.ip.e.tcb ct hctT
  have h17 : layout.reg.FAULT_IP.val = 17 := by unfold layout.reg.FAULT_IP; rfl
  have hra : (regA ct layout.reg.FAULT_IP).val = ct.val + 392 := by
    rw [regA_val hta (by rw [h17]; omega), h17]
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hN : P1.NodePlaced st Z.T s (L.cpu s) := by
    rw [hc.cur, J.tcbs_eq.1]; exact P1.TInv.nodes J.blk Z.c hcC
  have hnv : ∀ o : U64, o.val < 4288 → (L.nodeAt s (L.cpu s) o).val = L.nodeBase s Z.c + o.val :=
    fun o ho => by rw [P1.nodeAt_val hN ho, hc.cur]
  have h48 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
  have h40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
  have hCT := hnv _ (by rw [h48]; omega)
  have hCO := hnv _ (by rw [h40]; omega)
  rw [h48] at hCT; rw [h40] at hCO
  exact J.xtop.slotsSame_of hw fun b hb => by
    rcases hb with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨ct, hctT, by rw [hra]; omega, by rw [hra]; omega⟩))
    · exact Or.inl ⟨by rw [hCT]; omega, by rw [hCT]; omega⟩
    · exact Or.inl ⟨by rw [hCO]; omega, by rw [hCO]; omega⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- **The two spec-only entry facts left** (module docstring): l4v
`valid_ioports`, `untyped_ranges_zero`. -/
structure SInvIR (σ : Fl4Spec.State Unit) : Prop where
  ioP : SpecIoP σ
  utZ : SpecUtZ σ

theorem SInvIR.frame {σ σ' : Fl4Spec.State Unit} (h : SInvIR σ) (hcap : ∀ sl, SInvU.capAt σ' sl = SInvU.capAt σ sl)
    (ha : σ'.archState.x64AllocatedIoPorts = σ.archState.x64AllocatedIoPorts)
    (hm : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory) : SInvIR σ' where
  ioP sl f l hc := by rw [ha]; exact h.ioP sl f l (by rw [← hcap]; exact hc)
  utZ sl ptr sz fi hc a h1 h2 := by rw [hm]; exact h.utZ sl ptr sz fi (by rw [← hcap]; exact hc) a h1 h2

/-- **`SInvIR` from the entry state to the dispatch state** (as g5a's
`sinvI_disp`). -/
theorem sinvIR_disp (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} {x : Fl4Spec.Tcb}
    (hk : σ.kheap σ.curThread = some (.tcb x)) (hBA : BudgetAt σ σb true) (h : SInvIR σ) : SInvIR σb := by
  obtain ⟨⟨σu, hu, ebu⟩, ek, -⟩ := BudgetAt.shape27 hnd hk hBA
  have ek' : σb.kheap = Function.update σ.kheap σ.curThread
      (some (.tcb (setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek
  have hE := Sched.updateTimeStamp_eq' hnd
    (doMachineOp_single (getCurrentTime_eq (faultIPSt σ σ.curThread x).machineState))
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  refine h.frame (capAt_updTcb hk (by rfl) ek') ?_ ?_ <;> rw [ebu, e] <;> rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- `JEntryAtR5` to `JEntryAtR3` from `SInvX`'s `valid_irq_handlers` and `SInvIR`. -/
theorem _root_.Fl4Proofs.P3.JEntryAtR5.toR3V {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hV : SInvV.ValidIrqHandlers σ) (hI : SInvIR σ)
    (E : JEntryAtR5 (L := L) arI AR Z s ar σ) : JEntryAtR3 (L := L) arI AR Z s ar σ where
  stall := E.stall
  flags := E.flags
  handlers := J.handlersJV hV
  ports := J.portsJ hI.ioP
  ioapics := E.ioapics
  archIrq := E.archIrq
  vsTyp := E.vsTyp
  fnz := J.fnzJ
  urz := J.urzJ hI.utZ
  utks := J.utksJ

/-- `valid_irq_handlers` at the dispatch state (the FaultIP write keeps every
cap, `update_time_stamp` the interrupt states). -/
theorem vih_disp (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} {x : Fl4Spec.Tcb}
    (hk : σ.kheap σ.curThread = some (.tcb x)) (hBA : BudgetAt σ σb true) (h : SInvV.ValidIrqHandlers σ) :
    SInvV.ValidIrqHandlers σb := by
  obtain ⟨⟨σu, hu, ebu⟩, ek, -⟩ := BudgetAt.shape27 hnd hk hBA
  have ek' : σb.kheap = Function.update σ.kheap σ.curThread
      (some (.tcb (setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek
  have hE := Sched.updateTimeStamp_eq' hnd
    (doMachineOp_single (getCurrentTime_eq (faultIPSt σ σ.curThread x).machineState))
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  have hi : σb.interruptStates = σ.interruptStates := by rw [ebu, e]; rfl
  intro p cref irq hc
  rw [hi]
  apply h p cref irq
  rw [ek'] at hc
  by_cases hp : p = σ.curThread
  · subst hp
    rw [Function.update_self] at hc
    rw [hk]; exact hc
  · rwa [Function.update_of_ne hp] at hc

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JEntryAtR5` without `flags`** (asked at the entry state and carried to
the dispatch state, `flags_front`): the three [P] fields and `vsTyp` [J]. -/
structure JEntryAtR6 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) :
    Prop where
  /-- [P] `JEntryAt.stall` (one core). -/
  stall : ∀ q ∈ Z.T, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [P] `JEntryAt.ioapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `JEntryAt.archIrq`. -/
  archIrq : ArchIrqRel arI ar σ
  /-- [J] joint `JEntryAt.vsTyp` (l4v `valid_cap` typ_at, `pspace_distinct`). -/
  vsTyp : ∀ y, IsSlot Z.th y → OffTabOK (L := L) Z s σ (capV (L.mem s) y)

/-- **`JPathME` without the frame path's `JFramePath`** (`hno`, from the
entry state's `LargeFrOK`): the Frame case asks only the VT-x scope part. -/
def JPathME6 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl length : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : capability.Cap → Prop
  | .Frame p sz rt d m ep asid va =>
      ep = true ∨ lbl = fl4_abi.label.X86PageMapEPT → JVtxScope (L := L) arI AR s ar σ lbl length
        (.Frame p sz rt d m ep asid va) blk call don fp buf extra slbl argsU ci sl excaps buffer ct
  | c => JPathME (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c

/-- **`JPathAtM35E` with `JPathME6`.** -/
def JPathAtM36E (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathME6 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

variable {arI} in
theorem JPathAtM36E.to35E {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (hM : MdbLinks Z.th (L.mem s) Z.G) (hLF : LargeFrOK Z.G (L.mem s))
    {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtM36E (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtM35E (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  cases c
  case Frame p sz rt d m ep asid va =>
    refine ⟨hP, fun hep => ⟨fun hsz hd x hx hpx => ?_⟩⟩
    subst hep hsz hd
    obtain ⟨q, hq1, hq2⟩ := h8
    have hy : cslotAddr sl ∈ Z.G.chains.flatten :=
      (hM.members _).2 ⟨AbsSlot.isSlot ⟨q, hq1, Or.inl hq2⟩, _, h9, fun h => by cases h⟩
    exact hLF _ hy p rt m asid va (capV_of_capAt h9) x hx hpx
  all_goals exact hP

variable {arI}

theorem JEntryAtR6.toR5 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (hFl : FlagsRel Z.T (L.mem s) σ) (E : JEntryAtR6 (L := L) arI AR Z s ar σ) :
    JEntryAtR5 (L := L) arI AR Z s ar σ :=
  ⟨E.stall, hFl, E.ioapics, E.archIrq, E.vsTyp⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with `SInvIR`** (module docstring): `start`
from `JAtZ ∧ SInvX ∧ SInvIR ∧ MR`; `step` along `RJM` (what
`kernel_entryJ36E` delivers) with `SInvIR` of the exit (the open carry). -/
inductive JReachI : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → SInvX σ → SInvIR σ → MR a σ.machineState → JReachI s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReachI s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJM (L := L) arI AR MR s' a' σ' → SInvIR σ' → JReachI s' a' σ'

variable {arI AR MR}

end

end

end Fl4Proofs.P3.SInvR.G5
