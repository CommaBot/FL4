import Fl4Proofs.P2.WitUncond
import Fl4Proofs.P3.IrqFixGen
import Fl4Proofs.P3.JBoot5CtlQ

/-! jboot gen 5 (scratch): a dry run of IrqFixXport's transport on `wit_U2_io`'s cone under irqfix's `specD`
(plus `extra`), continuing past failures; prints each constant whose copy fails while all its deps exist. -/

namespace JB5
open Lean Meta Elab Command
open Fl4Proofs.P3.IrqFix

def extra : List (Name × Name) :=
  [(``Fl4Proofs.P3.irq_ioapic_refinesM, ``Fl4Proofs.P3.irq_ioapic_refinesMQ0),
   (``Fl4Proofs.P3.irq_remap_refinesM, ``Fl4Proofs.P3.irq_remap_refinesMQ0)]

def specW : Spec where
  recMap := specD.recMap
  defMap := specD.defMap
  constMap := specD.constMap ++ extra

/-- the pre-run (irqfix's run B maps with the IOAPIC / remap re-proofs). -/
def specBW : Spec where
  recMap := specB.recMap
  defMap := specB.defMap
  constMap := specB.constMap ++ extra

def q0 : List (Name × Name) :=
  [(``Fl4Proofs.P3.jDecMRL_of, `Fl4Proofs.P3.jDecMRL_ofQ0),
   (``Fl4Proofs.P3.jDecMRL2_ofT, `Fl4Proofs.P3.jDecMRL2_ofTQ0),
   (``Fl4Proofs.P3.jDecMRLK_ofU, `Fl4Proofs.P3.jDecMRLK_ofUQ0)]

def specM : Spec where
  recMap := specD.recMap
  defMap := specD.defMap
  constMap := specD.constMap ++ extra ++ q0

/-- the constants of `probes`' types / values that the main run maps (in its Tr or fixed). -/
def info (σ : Spec) (roots probes : List Name) : CoreM Unit := do
  let env ← getEnv
  let mut cone : NameSet := {}
  let mut wl : List Name := roots
  let mut deps : Std.HashMap Name (Array Name) := {}
  repeat
    match wl with
    | [] => break
    | n :: rest =>
      wl := rest
      if cone.contains n then continue
      cone := cone.insert n
      let ds := (Fl4Proofs.P3.StallNarrow.depsOf env n).filter ours
      deps := deps.insert n ds
      for d in ds do
        if !cone.contains d then wl := d :: wl
  let mut rev : Std.HashMap Name (List Name) := {}
  for n in cone.toList do
    for d in deps.getD n #[] do
      rev := rev.insert d (n :: rev.getD d [])
  let mut tr : NameSet := {}
  let mut wl2 : List Name := cone.toList.filter (fun n =>
    σ.recMap.any (fun (a, _) => a.isPrefixOf n) || σ.defMap.any (fun (a, _) => a == n))
  repeat
    match wl2 with
    | [] => break
    | n :: more =>
      wl2 := more
      if tr.contains n then continue
      tr := tr.insert n
      for u in rev.getD n [] do
        if !tr.contains u then wl2 := u :: wl2
  for p in probes do
    let some ci := env.find? p | IO.println s!"XI missing {p}"; continue
    let ty := ci.type.getUsedConstants.filter fun d => tr.contains d || isFixed σ d
    let vl := (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[]).filter
      fun d => tr.contains d || isFixed σ d
    IO.println s!"XI {p} TYPE {ty.toList.eraseDups} VALUE {vl.toList.eraseDups}"

def dry (σ : Spec) (roots : List Name) : CoreM Unit := do
  let env ← getEnv
  let mut cone : NameSet := {}
  let mut wl : List Name := roots
  let mut deps : Std.HashMap Name (Array Name) := {}
  repeat
    match wl with
    | [] => break
    | n :: rest =>
      wl := rest
      if cone.contains n then continue
      cone := cone.insert n
      let ds := if σ.constMap.any (·.1 == n) then #[] else
        (Fl4Proofs.P3.StallNarrow.depsOf env n).filter ours
      deps := deps.insert n ds
      for d in ds do
        if !cone.contains d then wl := d :: wl
  let coneL := cone.toList
  let mut rev : Std.HashMap Name (List Name) := {}
  for n in coneL do
    for d in deps.getD n #[] do
      rev := rev.insert d (n :: rev.getD d [])
  let mut tr : NameSet := {}
  let mut wl2 : List Name := coneL.filter (fun n =>
    σ.recMap.any (fun (a, _) => a.isPrefixOf n) || σ.defMap.any (fun (a, _) => a == n))
  repeat
    match wl2 with
    | [] => break
    | n :: more =>
      wl2 := more
      if tr.contains n then continue
      tr := tr.insert n
      for u in rev.getD n [] do
        if !tr.contains u then wl2 := u :: wl2
  IO.println s!"XD cone {cone.size} tr {tr.size}"
  let mut done : NameSet := {}
  let mut seen : NameSet := {}
  let mut order : Array Name := #[]
  for n0 in tr.toList do
    if done.contains n0 then continue
    let mut stack : List (Name × Bool) := [(n0, false)]
    repeat
      match stack with
      | [] => break
      | (n, exp) :: rest =>
        stack := rest
        if exp then
          if !done.contains n then
            done := done.insert n
            order := order.push n
        else if !seen.contains n then
          seen := seen.insert n
          stack := (n, true) :: stack
          for d in deps.getD n #[] do
            if tr.contains d && !seen.contains d then stack := (d, false) :: stack
  let mut failed : NameSet := {}
  let mut ok := 0
  let mut reused := 0
  for n in order do
    if σ.constMap.any (·.1 == n) || σ.defMap.any (·.1 == n) then continue
    let n' := mapName σ n
    if σ.recMap.any (·.1.isPrefixOf n) && (← getEnv).contains n' then continue
    let some ci := (← getEnv).find? n | IO.println s!"XD MISSING {n}"; continue
    let bad := (deps.getD n #[]).filter (failed.contains ·)
    if !bad.isEmpty then
      failed := failed.insert n
      continue
    if let some ci' := (← getEnv).find? n' then
      let same ← withCurrHeartbeats do pure (ci'.type == (← trE σ tr ci.type))
      if same then reused := reused + 1 else
        IO.println s!"XD REUSE-MISMATCH {n}"
        failed := failed.insert n
      continue
    let mod := match env.getModuleIdxFor? n with | some i => env.header.moduleNames[i.toNat]! | none => `here
    try
      withCurrHeartbeats do
        match ci with
        | .thmInfo v =>
          addDecl (.thmDecl (⟨⟨n', v.levelParams, (← trE σ tr v.type)⟩, (← trE σ tr v.value), [n']⟩ : TheoremVal))
        | .defnInfo v =>
          addDecl (.defnDecl (mkDefinitionValEx n' v.levelParams (← trE σ tr v.type) (← trE σ tr v.value) v.hints v.safety [n']))
        | .opaqueInfo v =>
          addDecl (.opaqueDecl (⟨⟨n', v.levelParams, (← trE σ tr v.type)⟩, (← trE σ tr v.value), v.isUnsafe, [n']⟩ : OpaqueVal))
        | .inductInfo v =>
          unless v.all.length == 1 do throwError "mutual inductive {n}"
          let ctors ← v.ctors.mapM fun k => do
            let some kc := (← getEnv).find? k | throwError "missing constructor {k}"
            pure (⟨mapName σ k, (← trE σ tr kc.type)⟩ : Constructor)
          addDecl (.inductDecl v.levelParams v.numParams [(⟨n', (← trE σ tr v.type), ctors⟩ : InductiveType)] v.isUnsafe)
        | .ctorInfo _ | .recInfo _ => pure ()
        | _ => throwError "unsupported constant {n}"
      ok := ok + 1
    catch e =>
      failed := failed.insert n
      let msg := (← e.toMessageData.toString)
      IO.println s!"XD FAIL {n} @{mod} :: {(msg.take 400).replace "\n" " "}"
  IO.println s!"XD copied {ok} reused {reused} failed {failed.size}"

end JB5

set_option maxRecDepth 200000 in
open Lean Elab Command in
run_cmd liftCoreM do
  JB5.info JB5.specW [`Fl4Proofs.P2.Wit.wit_U2_io]
    [``Fl4Proofs.P3.jDecMRL_of, ``Fl4Proofs.P3.jDecMRL2_ofT, ``Fl4Proofs.P3.jDecMRLK_ofU]
  JB5.info JB5.specBW [``Fl4Proofs.P3.decode_invocation_irq_controlXSM, ``Fl4Proofs.P3.jDecMRL2_ofT,
    ``Fl4Proofs.P3.jDecMRLK_ofU] [``Fl4Proofs.P3.jDecMRL2_ofT, ``Fl4Proofs.P3.jDecMRLK_ofU]

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.IrqFix Lean Elab Command in
run_cmd liftCoreM do
  let (n, r) ← transport JB5.specBW [``Fl4Proofs.P3.decode_invocation_irq_controlXSM,
    ``Fl4Proofs.P3.jDecMRL2_ofT, ``Fl4Proofs.P3.jDecMRLK_ofU]
  IO.println s!"XB pre-run: {n} copied, {r} reused"

#check @Fl4ProofsQ.P3.decode_invocation_irq_controlXSM
#check @Fl4ProofsQ.P3.jDecMRL2_ofT
#check @Fl4ProofsQ.P3.jDecMRLK_ofU

open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`JDecMRL` from `JDecMRL2`** at a dispatch state (module docstring): the
IO port cap by `XCapP.mr` (FL4 `MKD.decode_ioport` under `MRKeepIo`, spec
`dec_quiet`), the IRQ handler cap by `XCapP.mrG` (`MKD.decode_irq_handler_mr`,
`perfF_irqH`), the IRQ control cap by `decode_invocation_irq_controlXSM`,
the rest by `JDecMRL2`. -/
theorem jDecMRL_ofQ0 [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hNs : NativeScope σ) (hM : MachPlatT arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR)
    (hIoa : MRKeepIoapic arI MR) (hDL : JDecMRL2Q (L := L) arI AR MR Z H Cs D s ar σ ct) :
    JDecMRL (L := L) arI AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc hcl
    excaps buffer hXO hXN hLb hA5 hN
  obtain ⟨hlo, hNat⟩ := hcl
  have hA := hG.tot
  have hX0 := decOK_JMU arI s ar σ J hG hE ct hct lbl length blk call don fp buf extra slbl argsU hlen hargs
    hbuf hl ci sl hsl c hc excaps buffer hXO hXN hLb hA5 hN hPD hR hVT hVI hNs
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨p', hp, hth⟩ := hsl; exact ⟨p', hp, Or.inl hth⟩
  cases c <;> simp only [LoudF] at hlo
  case IoPort first last z =>
    exact Fl4ProofsQ.P3.XCapP.mr hM hX0 (MKD.decode_ioport L.total hA hKD hIo hR)
      (fun inv hd => MachT.dec_quiet fp slbl _ ci sl _ excaps buffer (by simp [absCap, MachT.QuietS]) σ _ hd.1 inv rfl)
  case IrqHandler irq =>
    have hirq : irq.val < 128 := (slot_cap_wf J.xtop hAs (capV_of_capAt hc)).1
    subst hLb
    exact Fl4ProofsQ.P3.XCapP.mrG (f := fun ms => if lbl = fl4_abi.label.IRQAckIRQ then unmaskMs ms irq else ms) hM hX0 (MKD.decode_irq_handler_mr L.total hA hKD (hDL.2 sl irq hsl hc hirq hR) hR)
      (perfF_irqH irq hirq lbl σ blk call don fp _ ci sl excaps buffer)
  case IrqControl =>
    subst hLb
    have hPl : Placed Z.th := J.xtop.rel.1
    have hex := ExtraOK.rel1 hPl hXO
    obtain ⟨nA, hnum, hnA⟩ := hE.ioapics
    obtain ⟨sl1, idxs⟩ := sl
    obtain ⟨p0, hp0, hth0⟩ := hsl
    try simp only at hp0 hth0
    subst hp0
    obtain ⟨hcur, -⟩ := J.curEq hct
    exact (Fl4ProofsQ.P3.decode_invocation_irq_controlXSM arI Z.th s ar σ Z.G J.intL hE.handlers lbl lbl.bv (irqControl_label lbl)
      (irqControl_remap lbl) length buf ct hct argsU hlen hargs hcur J.kern.act J.act2 extra _ (exAt_idx0 extra) excaps
      hex hth0 rfl hc nA hnum hnA (maskIrq_total arI hA) hE.archIrq rfl rfl J.xtop (J.curRun.run hE.ni) _
      ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩
      (fun _ _ _ h => Steps.jat arI hG.ari.toMask (jStepHyps arI) h rfl J (J.zNoBlk hE.sg)) (fun _ _ _ h => JAt.xtop arI h)
      blk call don fp ci buffer hM.mask (fun a ms ms' h e => Fl4ProofsQ.P3.mF_mr hM h e) hR hIoa).toPN arI (specDec_noPreK (by trivial))
  all_goals
    exact hDL.1 hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc
      ⟨trivial, hNat⟩ excaps buffer hXO hXN hLb hA5 hN

set_option maxHeartbeats 4000000 in
/-- `jDecMRL2_ofT` (its transported copy) carrying `IrqAckU`. -/
theorem jDecMRL2_ofTQ0 [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hM : MachPlatT arI MR) (hKD : MRKeepD arI MR)
    (hR3 : JDecMRLKQ (L := L) arI LoudT AR MR Z H Cs D s ar σ ct) :
    JDecMRL2Q (L := L) arI AR MR Z H Cs D s ar σ ct :=
  ⟨Fl4ProofsQ.P3.jDecMRL2_ofT arI s ar σ J hG hE ct hct hM hKD hR3.1, hR3.2⟩

set_option maxHeartbeats 4000000 in
/-- `jDecMRLK_ofU` (its transported copy) carrying `IrqAckU`. -/
theorem jDecMRLK_ofUQ0 [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hM : MachPlatT arI MR) (hKD : MRKeepD arI MR)
    (hVx : JDecMRLKQ (L := L) arI VtxK AR MR Z H Cs D s ar σ ct)
    (hUR : JUtResetHyp (L := L) arI AR MR Z H Cs D s ar σ ct) :
    JDecMRLKQ (L := L) arI LoudT AR MR Z H Cs D s ar σ ct :=
  ⟨Fl4ProofsQ.P3.jDecMRLK_ofU arI s ar σ J hG hE ct hct hM hKD hVx.1 hUR, hVx.2⟩

end

end

end Fl4Proofs.P3


#print axioms Fl4Proofs.P3.jDecMRL_ofQ0
#print axioms Fl4Proofs.P3.jDecMRLK_ofUQ0

set_option maxRecDepth 200000 in
open Lean Elab Command in
run_cmd liftCoreM do
  JB5.dry JB5.specM [`Fl4Proofs.P2.Wit.wit_U2_io]
