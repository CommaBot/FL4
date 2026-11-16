/-
P3 (DESIGN.md §9), IO ports: **the IO port cap's `In` labels at the
composite relation** (`PortInXHyp` discharged).

FL4's `In` (labels 64..66) restarts the caller, reads the port (the arch
`port_in`), replies when called and sets the caller `Running`: its tail is
VSpace's `vspace::reply1` of the value read. The spec restarts the caller,
runs the `In` invocation (a machine operation) and the success tail
(`specTail`: `reply_from_kernel (0, [v])` when called, then `Running`).

* `port_in_perform`: the spec's `In` has an outcome changing the machine
  state's rest only.
* `PortInVal`: **hypothesis** (the arch backend): the value FL4's `port_in`
  returns is the spec's read value at some outcome of the `In` invocation,
  the memory kept. Used only when the caller called (the reply carries it).
* `portInTail_xtop`: the tail at `XTop`, by the restart and the access as
  primitive steps (`Steps.xtop`), then `reply1` by VSpace's `reply1_invT`
  (the reply registers and `set_thread_state Running` at `RInv`, by
  `sts_inv`: `restart_top` for any state below 3), `XTopAt` rebuilt.
* `decode_invocation_ioport_inX`: the `In` labels' `DecOKRMX` at `XTop`;
  `portInXHyp_of`: `PortInXHyp` from it; `decode_invocation_ioportXT`: the
  IO port cap's `IoXHyp`, every label.
-/
import Fl4Proofs.P3.XTopIoPort
import Fl4Proofs.P3.DomSched
import Fl4Proofs.P3.TopM
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
open Fl4Spec

theorem molGets_ex' {β : Type} (f : MachineRestMonad Unit) (g : MachineState → β) (ms : MachineState) :
    ∃ ms', ms'.underlyingMemory = ms.underlyingMemory ∧
      (g ms', ms') ∈ ((machineOpLift f >>= fun _ => NonDet.gets g) ms).1 := by
  obtain ⟨ms', hu, h⟩ := mol_ex' f ms
  exact ⟨ms', hu, mem_bind_nd h rfl⟩

/-- **The spec's `In` access has an outcome**, the memory kept. -/
theorem port_in_perform (σ : State Unit) (port : IoPort) (n : Nat) :
    ∃ r, ∃ ms : MachineState, ms.underlyingMemory = σ.machineState.underlyingMemory ∧
      (.ok [r], { σ with machineState := ms }) ∈
        ((archPerformInvocation (Z := Unit) (.invokeIOPort (.ioPortInvocation port (inData n)))).run σ).1 := by
  have key : ∃ r, ∃ ms : MachineState, ms.underlyingMemory = σ.machineState.underlyingMemory ∧
      ([r], { σ with machineState := ms }) ∈
        (performIoPortInvocation (Z := Unit) (.ioPortInvocation port (inData n)) σ).1 := by
    unfold inData
    split
    · obtain ⟨ms, hu, h⟩ := molGets_ex' (in8Impl port) in8Val σ.machineState
      exact ⟨_, ms, hu, mem_bind_nd (dmo_ex _ σ h) rfl⟩
    · obtain ⟨ms, hu, h⟩ := molGets_ex' (in16Impl port) in16Val σ.machineState
      exact ⟨_, ms, hu, mem_bind_nd (dmo_ex _ σ h) rfl⟩
    · obtain ⟨ms, hu, h⟩ := molGets_ex' (in32Impl port) in32Val σ.machineState
      exact ⟨_, ms, hu, mem_bind_nd (dmo_ex _ σ h) rfl⟩
  obtain ⟨r, ms, hu, h⟩ := key
  refine ⟨r, ms, hu, ?_⟩
  unfold archPerformInvocation NonDetE.liftE
  rw [ExceptT.run_lift]
  exact mem_bind_nd h rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **Hypothesis: the value read** (module docstring): FL4's `port_in`'s
value is the spec's `In` result at some outcome, the memory kept. An
arch-backend obligation, with `ARMask` (XTopCaps) and `ARKeep` (ArchKeep). -/
def PortInVal : Prop :=
  ∀ (a a' : A) (p z v : U64), arI.port_in a p z = ok (v, a') → ∀ σ : Fl4Spec.State Unit,
    ∃ ms : Fl4Spec.MachineState, ms.underlyingMemory = σ.machineState.underlyingMemory ∧
      (.ok [v.bv], { σ with machineState := ms }) ∈ ((Fl4Spec.archPerformInvocation (Z := Unit)
        (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 p.val) (inData z.val)))).run σ).1

theorem spec_bind_assoc {α β γ : Type} {m : Result α} {f : α → Result β} {k : β → Result γ} {Q : β → Prop}
    {P : γ → Prop} (h1 : (m >>= f) ⦃ Q ⦄) (h2 : ∀ y, Q y → k y ⦃ P ⦄) : (m >>= fun x => f x >>= k) ⦃ P ⦄ := by
  rw [← bind_assoc_eq]; exact WP.spec_bind h1 h2

set_option maxHeartbeats 8000000 in
/-- **The `In` tail at `XTop`** (module docstring). -/
theorem portInTail_xtop {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) {Z : XSets} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDel : XDelNtfnHyp (L := L) arI AR Z.th)
    {ct : U64} (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) (port z : U64) (call : Bool)
    (hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a')) (hval : call = true → PortInVal arI) :
    portInTail (st := st) arI s ar ct port z call ⦃ res => res.1 = .Ok () ∧
      L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧ ∀ σ1,
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
        ∃ rr σy, (.ok rr, σy) ∈ ((Fl4Spec.archPerformInvocation (Z := Unit)
          (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val) (inData z.val)))).run σ1).1 ∧
        ∃ w ∈ (specTail call ct.bv rr σy).1, RelTopM (L := L) res.2.1 w.2 ∧ XTop (L := L) AR res.2.1 res.2.2 w.2 ⦄ := by
  obtain ⟨htcb, x, hk⟩ := hX.curTcb hcur
  have hrun : Fl4Spec.runnable x.tcbState = true := hC x (by rw [hcur]; exact hk)
  set σ1 := Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv with hσ1
  have hst : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) :=
    Notif.setThreadState_eq .restart hk
  unfold portInTail
  have hts := WP.spec_and (set_thread_state_cpu (L := L) s ct sched.TS_RESTART)
    (spec_self (set_thread_state_cpu (L := L) s ct sched.TS_RESTART))
  refine WP.spec_bind hts ?_
  rintro s1 ⟨⟨hk1, hc1⟩, hr1⟩
  obtain ⟨hX1, -, hC1⟩ := hX.restart' hC hcur hr1 hst
  obtain ⟨v, a1, hv⟩ := hin ar port z
  rw [hv]; simp only [bind_ok]
  -- the spec's `In`
  obtain ⟨rr, ms, hu, hmem, hrr⟩ : ∃ rr, ∃ ms : Fl4Spec.MachineState,
      ms.underlyingMemory = σ1.machineState.underlyingMemory ∧
      (.ok rr, { σ1 with machineState := ms }) ∈ ((Fl4Spec.archPerformInvocation (Z := Unit)
        (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val) (inData z.val)))).run σ1).1 ∧
      specTail call ct.bv rr { σ1 with machineState := ms } =
        specTail call ct.bv [v.bv] { σ1 with machineState := ms } := by
    cases call
    · obtain ⟨r, ms, hu, hmem⟩ := port_in_perform σ1 (BitVec.ofNat 16 port.val) z.val
      refine ⟨[r], ms, hu, hmem, ?_⟩
      have hky : ({ σ1 with machineState := ms } : Fl4Spec.State Unit).kheap ct.bv =
          some (.tcb { x with tcbState := .restart }) := by
        show σ1.kheap ct.bv = _; rw [hσ1, Notif.stsAct_kheap, Notif.updK_kheap, Function.update_self]
      rw [specTail_restart hky rfl false r, specTail_restart hky rfl false v.bv]
      simp only [Bool.false_eq_true, ↓reduceIte]
    · obtain ⟨ms, hu, hmem⟩ := hval rfl ar a1 port z v hv σ1
      exact ⟨[v.bv], ms, hu, hmem, rfl⟩
  set σy : Fl4Spec.State Unit := { σ1 with machineState := ms } with hσy
  -- the restart and the access, as primitive steps
  have hstp : Steps (L := L) arI Z.th s1 ar σ1 s1 a1 σy :=
    (Steps.ksSpec arI (s := s1) (σ := σ1) (σ' := σy) (by constructor <;> first | rfl | exact hu) rfl rfl
      (fun h => ⟨h.st, h.node⟩) (fun h => h)).trans arI
      (Steps.arch arI (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨port, z, v, hv⟩))))))
  obtain ⟨G', hXy, -, hky⟩ := hstp _ (stepClosed_xtop arI hAM hDel) Z rfl hX1 (by rw [hk1]; exact hKA) hC1 hTh
  -- `reply1`
  set Z' : XSets := { Z with G := G' }
  have hI : Vs.RInv (L := L) Z'.th Z'.P Z'.L4 Z'.L3 Z'.L2 Z'.L1 Z'.N Z'.T Z'.C Z'.E Z'.R Z'.B Z'.c AR Z'.G s1 a1 σy :=
    ⟨hXy.rel.2.1, hXy.rel.2.2.1, hXy.rel.2.2.2.2.1, hXy.rel.2.2.2.1, hXy.fin⟩
  have hkY : σy.kheap ct.bv = some (.tcb { x with tcbState := .restart }) := by
    show σ1.kheap ct.bv = _; rw [hσ1, Notif.stsAct_kheap, Notif.updK_kheap, Function.update_self]
  have hcurY : ct.bv = σy.curThread := by
    show ct.bv = σ1.curThread; rw [hσ1, stsAct_cur]; exact hcur.symm
  have hact1 : OutsideObjects Z'.th (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) := by
    rw [hc1]; simp only [P1.LawfulStore.nodeAt, hk1]; exact hact
  refine spec_bind_assoc (Vs.reply1_invT s1 a1 σy hI ct htcb hcurY hkY rfl hact1 call v) ?_
  rintro s3 ⟨hne, hks3, w, hw, hI3, hz3⟩
  rw [WP.spec_ok]
  refine ⟨rfl, hne, fun σ1' hσ1' => ?_⟩
  have e : σ1' = σ1 := by
    rw [hst] at hσ1'
    exact ((Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hσ1'))).2).symm
  subst e
  have hSch := hI3.2.2.2.2.1.1.1
  refine ⟨rr, σy, hmem, w, by rw [hrr]; exact hw, hI3.relTop, ⟨Z', hI3.2.2.2.2, ⟨hXy.rel.1, hI3.1, hI3.2.1,
    hI3.2.2.2.1, hI3.2.2.1, by rw [hks3]; exact hXy.rel.2.2.2.2.2.1, hXy.rel.2.2.2.2.2.2.mono hz3⟩,
    IpcRel.of hI3.2.2.2.2.1.1.2.2.1 hI3.2.2.2.2.1.1.2.1 (sched_sc hSch), hXy.esa.mono hks3 hz3⟩⟩

set_option maxHeartbeats 8000000 in
/-- **IOPort `In`** (labels 64..66, any `call`) at `XTop`: the replying shape
(`DecOKRMX`), from `portInTail_xtop`. -/
theorem decode_invocation_ioport_inX {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl : U64) (hl : 64 ≤ lbl.val ∧ lbl.val ≤ 66)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.invocationType slbl = .archInvocationLabel (inLabel (portSz lbl)))
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (first last : U64) (hfl : first.val ≤ last.val) (hl16 : last.val < 65536)
    {Z : XSets} (hX0 : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDel : XDelNtfnHyp (L := L) arI AR Z.th)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a')) (call : Bool)
    (hval : call = true → PortInVal arI)
    (slot : U64) (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    DecOKRMX (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot (.IoPort first last 0#u64) blk call don fp buf
      extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  unfold DecOKRMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hsz : portSz lbl = 1 ∨ portSz lbl = 2 ∨ portSz lbl = 4 := by unfold portSz; split_ifs <;> simp
  have hspec : specDec fp slbl (args.map UScalar.bv) ci sl (.IoPort first last 0#u64) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec
        (Fl4Spec.decodePortInvocation slbl (args.map UScalar.bv)
          (.ioPortCap (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val)))) := rfl
  rw [hspec, decode_in_eq slbl _ _ hsz hlbl]
  unfold ioport.decode
  simp only
  rw [hct, port_size_eq lbl ⟨hl.1, by omega⟩, is_port_in_eq lbl ⟨hl.1, by omega⟩]
  simp only [bind_ok]
  have hszU : (if lbl.val = 64 ∨ lbl.val = 67 then 1#u64 else if lbl.val = 65 ∨ lbl.val = 68 then 2#u64
      else 4#u64) = ⟨BitVec.ofNat 64 (portSz lbl)⟩ := by
    unfold portSz; split_ifs <;> rfl
  rw [hszU]
  have hsz0 : ¬ (⟨BitVec.ofNat 64 (portSz lbl)⟩ : U64) = 0#u64 := by
    rw [u64_eq_iff]; show ¬ (BitVec.ofNat 64 (portSz lbl)).toNat = 0
    rcases hsz with h | h | h <;> rw [h] <;> decide
  rw [if_neg hsz0, decide_eq_true (by omega : lbl.val ≤ 66)]
  simp only [↓reduceIte]
  -- the argument
  by_cases h1 : length < 1#u64
  · rw [if_pos h1]; simp only [error.truncated, bind_ok]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, run_liftME_err (run_liftME_err ?_), Or.inl trivial⟩, ⟨Z, hX0⟩⟩
    unfold Fl4Spec.argsAtLeast
    rw [whenE_pos (show 1 > (args.map UScalar.bv).length by rw [List.length_map, ← hlen]; scalar_tac)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  rw [if_neg h1]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  simp only [hargs 0#u64 y0 (by simp), lift, bind_ok]
  unfold Fl4Spec.argsAtLeast
  rw [whenE_neg (show ¬ 1 > ((y0 :: rest).map UScalar.bv).length by simp), retOk_bind, retOk_bind]
  have hmap : List.map UScalar.bv (y0 :: rest) = y0.bv :: rest.map UScalar.bv := rfl
  have g0 : (y0.bv :: rest.map UScalar.bv)[0]? = some y0.bv := rfl
  rw [hmap, g0, the_some]
  set port := y0 &&& 65535#u64 with hport
  have hpv : port.val < 65536 := by rw [hport, and_ffff]; omega
  have hp16 : (Fl4Spec.ucast 16 y0.bv : BitVec 16) = BitVec.ofNat 16 port.val := by
    apply BitVec.eq_of_toNat_eq; rw [ucast16_toNat, BitVec.toNat_ofNat, hport, and_ffff]; omega
  rw [hp16]
  have hszv : (⟨BitVec.ofNat 64 (portSz lbl)⟩ : U64).val = portSz lbl := by
    show (BitVec.ofNat 64 (portSz lbl)).toNat = _
    rw [BitVec.toNat_ofNat]; rcases hsz with h | h | h <;> rw [h]
  rw [allowed_eq first last port _ hl16 hpv (by rw [hszv]; exact hsz)]
  simp only [hszv, bind_ok]
  have hens := ensure_run first last hfl hl16 port hpv hsz σ
  by_cases hc : port.val < first.val ∨ port.val + portSz lbl - 1 > last.val
  · rw [if_pos hc]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok]
    rw [if_pos hc] at hens
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err (run_liftME_err (run_bind_error hens _)),
      Or.inl trivial⟩, ⟨Z, hX0⟩⟩
  rw [if_neg hc]
  rw [if_neg hc] at hens
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_mono (portInTail_xtop arI hAM hX0 hKA hC hTh hDel hcur hact port ⟨BitVec.ofNat 64 (portSz lbl)⟩
    call hin hval) ?_
  rintro res ⟨hres, hne, hall⟩
  obtain ⟨htcb, x, hk⟩ := hX0.curTcb hcur
  have hst : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ =
      ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv)}, False) :=
    Notif.setThreadState_eq .restart hk
  obtain ⟨rr, σy, hy, z, hz, hRT, hXT⟩ := hall _ hst
  rw [hszv] at hy
  refine Or.inr ⟨hres, hne, .invokeArchObject (.spec (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val)
    (inData (portSz lbl))))), ?_, _, by rw [hcur]; exact hst, rr, σy, hy, z, hz, hRT, hXT⟩
  exact DecOut.of_eq (run_liftME_ok (run_liftME_ok ((run_bind_ok hens _).trans rfl)))

/-- **`PortInXHyp` discharged** (`decode_invocation_ioport_inX`), given
`PortInVal` when called. -/
theorem portInXHyp_of {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl : U64) (hl : 64 ≤ lbl.val ∧ lbl.val ≤ 66) (slbl : Fl4Spec.Data)
    (hlbl : PortLabel lbl slbl) (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (first last : U64) (hfl : first.val ≤ last.val) (hl16 : last.val < 65536)
    {Z : XSets} (hX0 : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDel : XDelNtfnHyp (L := L) arI AR Z.th)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a')) (call : Bool)
    (hval : call = true → PortInVal arI)
    (slot : U64) (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    PortInXHyp (L := L) arI AR s ar σ lbl length slot first last blk call don fp buf extra slbl (args.map UScalar.bv)
      ci sl excaps buffer ct :=
  Or.inr (decode_invocation_ioport_inX arI hAM s ar σ lbl hl slbl (hlbl.1 hl) length buf ct hct args hlen hargs hcur
    first last hfl hl16 hX0 hKA hC hTh hDel hact hin call hval slot blk don fp extra ci sl excaps buffer)

/-- **`IoXHyp` for the IO port cap, every label** (`decode_invocation_ioportX`
with `PortInXHyp` from `portInXHyp_of`); `PortInVal` when called. -/
theorem decode_invocation_ioportXT {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : PortLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) {Z : XSets} (hX0 : XTopAt (L := L) AR Z s ar σ)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (first last : U64) (hfl : first.val ≤ last.val) (hl16 : last.val < 65536) (call : Bool)
    (hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a'))
    (hout : ∀ (a : A) p z d, ∃ a', arI.port_out a p z d = ok a') (hval : call = true → PortInVal arI)
    (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T)
    (hDel : XDelNtfnHyp (L := L) arI AR Z.th)
    (slot : U64) (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot (.IoPort first last 0#u64) blk call don fp buf extra
      slbl (args.map UScalar.bv) ci sl excaps buffer ct :=
  decode_invocation_ioportX arI hAM Z.th hX0.rel.1 s ar σ lbl slbl hlbl length buf ct hct args hlen hargs hcur
    (hX0.curTcb hcur).1 hact first last hfl hl16 call hout rfl hX0 hKA hC hTh hDel slot blk don fp extra ci sl excaps
    buffer fun hI => portInXHyp_of arI hAM s ar σ lbl hI slbl hlbl length buf ct hct args hlen hargs hcur first last
      hfl hl16 hX0 hKA hC hTh hDel hact hin call hval slot blk don fp extra ci sl excaps buffer

end

end

end Fl4Proofs.P3
