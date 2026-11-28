/-
P3 (p3J gen 39): **the Thread cap's decode leaf at stable ghosts for both classes at every label of no TCB
invocation** (outside 2–24, and not the VT-x label `TCBSetEPTRoot` = 88); the rest set {CNode at Revoke / Delete,
Thread at 2–24 or SetEPTRoot}.

* **`decThIllSt`** (any flags): XTopTcb's `tcb_illegalX` (the spec's `IllegalOperation`, the state unchanged, any
  post holding at the start) through `syscall.decode_invocation` as XTopTcb's `decode_invocation_threadX` does at
  such a label; the target's stall a no-op (StallNarrowTcb's `JAtZ.stallT`, the target among `Z.T` by
  `slot_cap_wf`); the canonical label (`tcb_canon`, `specDec_thread`, `XCapP.lbl_congr`); never preempted
  (`thread_noPre_of`). The post `(JStab (Z.mv Z.G V') H Cs ∧ WritesIn s' · (ProjW H Cs s')) ∧ MR` holds at the
  start (`J.stab`, `WritesIn.refl`, `MR` at the dispatch state), which is the outcome's state: no footprint and no
  `MR` lemma needed.
* `ThHard l`: `2 ≤ l ≤ 24` or `l = TCBSetEPTRoot`. `IsRestCap9 cp l`: CNode with `CnDel l`, or Thread with
  `ThHard l`. `restCap8_of9`, `restCap9_of`. **`midDecRest8_of_th`** / **`invDecRest8_of_th`**,
  `midDecStWL_of_8` / `invDecStWL_of_8`.
* **`DispStabFootLzb` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap9`, midSpec, midRecvSw verbatim};
  **`dispStabFootLza_of_Lzb`**, **`dispStabFootLzb_of_Lza`** (honesty, proved); top **`kernel_entry_runMcWKR_sysLzb`**
  (globals verbatim as `_sysLza`).

Premise honesty: `DispStabFootLzb` is `DispStabFootLza` at the smaller antecedent (`IsRestCap9 → IsRestCap8`),
midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzb` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JCnCbs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 39) The Thread labels left: the TCB invocations (2–24) and the VT-x `TCBSetEPTRoot`. -/
def ThHard (l : U64) : Prop := (2 ≤ l.val ∧ l.val ≤ 24) ∨ l = fl4_abi.label.TCBSetEPTRoot

/-- (p3J gen 39) The caps left after the Thread illegal-label leaf, with the message label. -/
def IsRestCap9 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard l
  | _, _ => False

theorem restCap9_of {cp : capability.Cap} {l : U64} (h : IsRestCap8 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ ¬ ThHard l) : IsRestCap9 cp l := by
  cases cp
  case CNode => exact h
  case Thread p =>
    show ThHard l
    by_contra hc
    exact hS ⟨p, rfl, hc⟩
  all_goals exact False.elim h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 39) **The Thread cap's decode at a dispatch state at a label of no TCB invocation, any flags**
(module docstring). -/
theorem decThIllSt [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb)
    (hMb : MR a' σb.machineState) {ct : U64} (hct : sched.cur_thread st s' = ok ct)
    {info : msginfo.MessageInfo} {mi : Fl4Spec.MessageInfo} {buf : U64} {buffer : Option Fl4Spec.ObjRef}
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))}
    (hinfo : msg.msg_info st s' ct = ok info)
    (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False))
    (hbuf : msg.lookup_ipc_buffer st s' false ct = ok buf)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False))
    (hr2 : ipc.lookup_extra_caps st s' ct buf info = ok r2)
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False))
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.Thread p))
    (e : Aeneas.Std.Array obj.Slot 3#usize) (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hl : ¬ ThHard info.label) (args : List Fl4Spec.Data) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.Thread p) bl call don fp buf e mi.miLabel
      args ci sl exs buffer ct := by
  unfold ThHard at hl
  have hlo : ¬ (2 ≤ info.label.val ∧ info.label.val ≤ 24) := fun h => hl (Or.inl h)
  have hN : info.label ≠ fl4_abi.label.TCBSetEPTRoot := fun h => hl (Or.inr h)
  have hX0 : (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s')) ∧ MR a' σb.machineState :=
    ⟨⟨J.stab, P1.WritesIn.refl _ _⟩, hMb⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  obtain ⟨hLb, -⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  rw [← hLb]
  obtain ⟨sl', hlbl, hext, hd⟩ := tcb_canon info.label
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  have hl5 : info.label.val ≠ 5 ∧ info.label.val ≠ 8 ∧ info.label.val ≠ 9 ∧ info.label.val ≠ 10 ∧
      info.label.val ≠ 11 := ⟨by omega, by omega, by omega, by omega, by omega⟩
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .Thread p := capV_of_capAt hc
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ (Z.mv Z.G V').T := J.thT p hp
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact tcb_illegalX arI s' a' σb hX0 info.label p _ bl call don sl' hlbl args ci sl exs buffer hext
      (J.stallT p hpT) hN hlo
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 39) **`MidDecStWL` at `KW ∧ IsRestCap8` from the Thread illegal-label leaf** (module docstring). -/
theorem midDecRest8_of_th [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap9 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap8 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ ¬ ThHard info.label
  · obtain ⟨p, rfl, hl⟩ := hS
    exact decThIllSt J hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc e exs hl _ _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap9_of hW.2 hS⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

end Fl4Proofs.P3.Mc
