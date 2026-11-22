/-
P3 (DESIGN.md §9), invariant line G4 (g4j, KENTRY-PLAN g4j): **the Untyped
cap's decode with `MR` at the chosen outcome**, for the retypes without a
reset; the retypes with a reset asked as the narrow [W] `JUtResetMR`.

* `UtRetPostJMM`: UtRetResetJM's `UtRetPostJM` with `JAtM` (`MR` at the
  outcome) after a non-preempted invocation.
* `UtRetPostJM.mrK`: `UtRetPostJM` gives `UtRetPostJMM` when FL4 ends with
  `MR` of the decode state's machine state and every perform outcome keeps
  `msF` (the restart keeps it, `msF_restart`).
* `perf_ut_nr`: the spec's retype without a reset keeps `msFT` (no
  `resetUntypedCap`: `getCap`, `setCap`, `retypeRegionWith`,
  `initArchObjects`, `createCap`).
* `JUtRetHypDMM`, `JUtResetMR` [W] (the retype run with `reset = true`, at
  `UtRetPostJMM`; l4v `invoke_untyped_corres` with `reset_untyped_cap`'s
  `preemption_point` under the shared machine state), `jUtRetHypDMM_of`: the
  no-reset runs from `JUtRetHypDM` + FL4's `MKD.untyped_retype_nr` +
  `perf_ut_nr`, the reset runs by `JUtResetMR`.
* `decode_invocation_untypedJMM`: `decode_invocation_untypedJM` at `JAtM`.
-/
import Fl4Proofs.P3.UtRetResetJM
import Fl4Proofs.P3.XTopJointKEntry38
import Fl4Proofs.P3.MachKeepG4j
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
open Fl4Spec

/-- **The spec's retype without a reset keeps `msFT`** (module docstring). -/
theorem perf_ut_nr (b c d : Bool) (sl : CslotPtr) (base rb : Word) (t : ApiObjectType) (us : Nat)
    (slots : List CslotPtr) (dev : Bool) :
    MachT.MTKE (fl4PerformInvocation (Z := Unit) b c d (.invokeUntyped (.retype sl false base rb t us slots dev))) := by
  simp only [fl4PerformInvocation, fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true,
    ↓reduceIte]
  mtk_auto

end

section
open Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`UtRetPostJM` with `MR` at the outcome** (module docstring). -/
def UtRetPostJMM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (σ : Fl4Spec.State Unit)
    (blk call don : Bool) (inv : Fl4Spec.UntypedInvocation) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeUntyped inv)).run σ1).1, (∃ th' G',
      ((res.1 = .Ok () ∧ y.1 = .ok []) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
      Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
      DomRel (L.mem res.2.1) (L.ksb res.2.1) y.2 ∧ MdbOKV (L.ksb res.2.1) (L.mem res.2.1) G') ∧
      (if res.1 = .Err .Preempted then JAtPreMV (L := L) arI AR MR res.2.1 res.2.2 y.2
        else JAtM (L := L) arI AR MR res.2.1 res.2.2 y.2)

/-- **The retype after the decode with `MR` at the outcome** (`JUtRetHypDM`
with `UtRetPostJMM`). -/
def JUtRetHypDMM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (th : TypedHeap) (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (p sb fi : U64) (dev : Bool) (ct : U64)
    (blk call don : Bool) (argsU : List U64) : Prop :=
  ∀ (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64),
    argsU.head? = some nt → RetCtx (L := L) th s σ sl sb fi dev nt us dest off win t r reset fiv →
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr sl) reset ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us
        dest off win dev) ⦃ res =>
      UtRetPostJMM (L := L) arI AR MR σ blk call don (.retype sl reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev)
        res ⦄

/-- **[W] The retype with a reset, `MR` at the outcome** (module docstring):
`JUtRetHypDMM` for the runs whose decode chose `reset = true` (the cap has no
children and a non-zero free index). l4v: `invoke_untyped_corres` with
`reset_untyped_cap_corres` (its `preemption_point` and `do_machine_op`
clears under the shared machine state). FL4's reset loop carries `MR` in its
invariant (mr4's `JAtZ.reset_loopJM`), dropped by `ResetJPostM`'s Ok exit. -/
def JUtResetMR (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (th : TypedHeap) (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (p sb fi : U64) (dev : Bool) (ct : U64)
    (blk call don : Bool) (argsU : List U64) : Prop :=
  ∀ (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (fiv : U64),
    argsU.head? = some nt → RetCtx (L := L) th s σ sl sb fi dev nt us dest off win t r true fiv →
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr sl) true ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us
        dest off win dev) ⦃ res =>
      UtRetPostJMM (L := L) arI AR MR σ blk call don (.retype sl true p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev)
        res ⦄

variable {arI}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`UtRetPostJM` gives `UtRetPostJMM`** (module docstring). -/
theorem UtRetPostJM.mrK (hM : MachPlat arI MR) {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {inv : Fl4Spec.UntypedInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (h : UtRetPostJM (L := L) arI AR MR σ blk call don inv res) (hR : MR res.2.2 σ.machineState)
    (hq : ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      ∀ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeUntyped inv)).run σ1).1,
        MachF.msF y.2 = MachF.msF σ1) :
    UtRetPostJMM (L := L) arI AR MR σ blk call don inv res := by
  obtain ⟨σ1, hst, y, hy, hrel, hX⟩ := h
  refine ⟨σ1, hst, y, hy, hrel, ?_⟩
  by_cases hp : res.1 = .Err .Preempted
  · rw [if_pos hp] at hX ⊢; exact hX
  · rw [if_neg hp] at hX ⊢; exact ⟨hX, msF_mr hM hR ((hq σ1 hst y hy).trans (msF_restart hst))⟩

set_option maxHeartbeats 4000000 in
/-- **`JUtRetHypDMM` from `JUtRetHypDM` and `JUtResetMR`** (module docstring). -/
theorem jUtRetHypDMM_of (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hA : P0.ArchTotal arI) {th : TypedHeap}
    {s : S} {ar : A} {σ : Fl4Spec.State Unit} {sl : Fl4Spec.CslotPtr} {p sb fi : U64} {dev : Bool} {ct : U64}
    {blk call don : Bool} {argsU : List U64}
    (h0 : JUtRetHypDM (L := L) arI AR MR th s ar σ sl p sb fi dev ct blk call don argsU)
    (hRs : JUtResetMR (L := L) arI AR MR th s ar σ sl p sb fi dev ct blk call don argsU)
    (hR : MR ar σ.machineState) :
    JUtRetHypDMM (L := L) arI AR MR th s ar σ sl p sb fi dev ct blk call don argsU := by
  intro nt us dest off win t r reset fiv hh hctx
  cases reset
  · have hW : (do
        let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
        untyped.retype st arI s2 ar (cslotAddr sl) false ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt
          us dest off win dev) ⦃ r => MR r.2.2 σ.machineState ⦄ := by
      step
      all_goals first | exact L.total | exact hA | exact MKD.untyped_retype_nr L.total hA hKD hR
    refine WP.spec_mono (WP.spec_and (h0 nt us dest off win t r false fiv hh hctx) hW) fun res ⟨h1, h2⟩ => ?_
    exact h1.mrK hM h2 fun σ1 _ y hy =>
      congrArg Prod.fst (perf_ut_nr blk call don _ _ _ _ _ _ _ σ1 y hy)
  · exact hRs nt us dest off win t r fiv hh hctx

variable {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}

/-- **An untyped cap's decode at `JAtM`** (`decode_invocation_untypedJM` with
`JUtRetHypDMM`). -/
theorem decode_invocation_untypedJMM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hMR : MR ar σ.machineState)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (argsU : List U64)
    (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hNative : ∀ x, argsU.head? = some x → x.val < 14 ∨ 19 ≤ x.val)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (p sb fi : U64) {dev : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hR : JUtRetHypDMM (L := L) arI AR MR Z.th s ar σ sl p sb fi dev ct blk call don argsU) :
    XCapP (L := L) arI (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl)
      (.Untyped p sb fi dev) blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  have hX0 : JAtM (L := L) arI AR MR s ar σ := ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hMR⟩
  obtain ⟨hP, ⟨hSR, hV, hM, hC, hI⟩, -⟩ := J.xtop.rel
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (untyped_decode_refines_fl4 arI Z.th s ar σ Z.G hSR hV hP hM hC hI lbl slbl hlbl length buf ct
    hct argsU hlen hargs hNative _ sl rfl hAs p sb fi dev hc extra x0 hx0 _ hex hfan
    (fun inv res => UtRetPostJMM (L := L) arI AR MR σ blk call don inv res) hR) ?_
  rintro res (⟨e, e', rfl, h1, h2⟩ | ⟨inv, hrun, σ1, hst, y, hy, hrel, hx⟩)
  · exact TopPostDMX.errP ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, hX0⟩
  · exact Or.inr ⟨.invokeUntyped inv, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, y, hy, hrel, hx⟩

end

end

end Fl4Proofs.P3
