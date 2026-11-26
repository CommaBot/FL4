/-
# P2 (line p3mc, gen 10): U11, U10 with vmF's `VSafe9` discharged also at the declining starts

## The discharged starts (`VmDisAt`)
At the vmF indices, `VmDisAt` is `FHStart` (U10: foreign handler, action 0) or
* `ActStart`: the prefix state's action is not `RESUME_CURRENT` and the current SC is homed on `c` in `ρ`
  (`VmDecTop.vmF_act_annV`), or
* `NoGoStart`: the action is `RESUME_CURRENT` and wherever the fault-handler slot holds an endpoint cap whose endpoint
  receives, the cap grants nothing and the head is homed on `c` in `ρ` (`VmDecTop.vmF_nogo_annV`).
**`vmF_annV_dis`**: at each the re-annotated body `annV k0` is `Safe` at the physical memory.

## U11
`ExecWPRV10` (U10's chain step, generic in the exempt starts `FH`) with `FH := VmDisAt`:
**`serializable_fl4_localU11`**; `execWPRV10_mono` (a wider `FH` asks less), **`serializable_fl4_localU10of11`**.

## Premises of `serializable_fl4_localU11` vs `serializable_fl4_localU10`
* **Removed: `VSafe9` [J] at the vmF starts with `ActStart` or `NoGoStart`.** Nothing added.
* `VSafe9` [J] stays at the vmF starts with neither `FHStart`, `ActStart` nor `NoGoStart`:
  1. action `RESUME_CURRENT`, a granting endpoint cap, the endpoint receiving, its head homed on `c` (the fast path
     may accept: handoff p3mc §13, `vm_accN`);
  2. action not `RESUME_CURRENT` and the current SC another core's in `ρ` (possible at the view only with
     `cur.sc = 0`: `BoundInv.resume`). Not provable by the `Once`-based certificate: the racy refill head index `i`
     of a foreign SC may be `2^60 - 1`, for which `r_time`'s address `sc + 96 + 16 i` is `REFILL_HEAD` itself, so the
     tree reads that racy word twice (handoff p3mc §13).
  and at every other non-io slot, as in U10. Everything else unchanged.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.VmDecTop
import Fl4Proofs.P2.E2EPU10
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP)
open Fl4Proofs.P2.CoreView (view)

noncomputable section
open Classical

section dis
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

/-- **A vmF start at `c`'s view whose prefix action is not `RESUME_CURRENT`, the current SC homed** (module
docstring). -/
def ActStart (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (j : VmFArg S) (k0 : SP) : Prop :=
  ∃ (σ : S) (a : A), VmFPremA st ar j K.toKLayoutV ∧
    VmPre st ar (userV K.toKLayoutV) j.T j.Cs j.Ω j.U j.H j.Sg j.Rp j.Scs j.Nt j.Z j.Ac j.Locks σ ∧
    QPs K st σ ∧ L.cpu σ = c ∧ j.Locks σ = hs ∧
    (∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) ∧ ρ (fld (L.cscW σ) 16#u64) = c ∧
    (∃ (s1 : S) (a1 : A), sched.update_timestamp st ar σ a = ok (s1, a1) ∧ L.actionW s1 ≠ 0#u64) ∧
    k0 = tr (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) j.Locks) σ) (· ∈ K.user)
      (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
      (R.syscall.handle_vm_fault_local j.addr j.code) ∅ a

/-- **A vmF start at `c`'s view with action `RESUME_CURRENT` whose fast path is not entered** (module docstring). -/
def NoGoStart (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (j : VmFArg S) (k0 : SP) : Prop :=
  ∃ (σ : S) (a : A), VmFPremA st ar j K.toKLayoutV ∧
    VmPre st ar (userV K.toKLayoutV) j.T j.Cs j.Ω j.U j.H j.Sg j.Rp j.Scs j.Nt j.Z j.Ac j.Locks σ ∧
    QPs K st σ ∧ L.cpu σ = c ∧ j.Locks σ = hs ∧
    (∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) ∧ L.actionW σ = 0#u64 ∧
    (∃ (s1 : S) (a1 : A), sched.update_timestamp st ar σ a = ok (s1, a1) ∧
      ∀ sl ptr badge x' y g gr, obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
        obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr) →
        L.epState s1 ptr = obj.EP_RECV → (g = false ∧ gr = false) ∧ ρ (affA (L.mem s1 (epHeadA ptr))) = c) ∧
    k0 = tr (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) j.Locks) σ) (· ∈ K.user)
      (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
      (R.syscall.handle_vm_fault_local j.addr j.code) ∅ a

/-- The discharged vmF starts of U11, `False` at the other indices. -/
def VmDisAt (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.vmF j) => FHStart st ar K c hs ρ j k0 ∨ ActStart st ar K c hs ρ j k0 ∨ NoGoStart st ar K c hs ρ j k0
  | _ => False

theorem fhAt_dis {K : KLayoutP} {c : U64} {hs : U64 → Prop} {ρ : U64 → U64} {k0 : SP}
    {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)} (h : FHAt st ar K c hs ρ k0 i) :
    VmDisAt st ar K c hs ρ k0 i := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact Or.inl h
  all_goals exact h

/-- **U9's re-annotated body is `Safe` at a discharged start of U11** (module docstring). -/
theorem vmF_annV_dis (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (hK : RegionOKP K) (hU : UserOKP K) {c : U64} {k0 : SP} {ρ : U64 → U64}
    {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)} (hM : MapsP K s)
    (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : VmDisAt st ar K c (fun l => s.lk l = some c) ρ k0 i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k0) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · rcases hf with hf | hf | hf
    · exact vmF_annV_fh st ar hA hmk hK hU (i := .inl (.vmF j)) hM hV hf
    · obtain ⟨σ, a, hpr, hP, hq, hc, hl, hmm, hcH, ⟨s1, a1, eu, hact⟩, rfl⟩ := hf
      unfold annV
      rw [hM.own, hM.cls, hM.ko] at hV ⊢
      exact vmF_act_annV hA hmk hK hU hpr.nv ⟨hpr.lay.slot8, hpr.lay.tcb, hpr.lay.ntfn8, hpr.lay.sc8⟩ hV hP hq hc hl
        hmm hcH eu hact
    · obtain ⟨σ, a, hpr, hP, hq, hc, hl, hmm, hact, ⟨s1, a1, eu, hno⟩, rfl⟩ := hf
      unfold annV
      rw [hM.own, hM.cls, hM.ko] at hV ⊢
      exact vmF_nogo_annV hA hmk hK hU hpr.nv ⟨hpr.lay.slot8, hpr.lay.tcb, hpr.lay.ntfn8, hpr.lay.sc8⟩ hV hP hq hc
        hl hmm hact eu hno
  all_goals exact False.elim hf

end dis

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A wider set of exempt starts asks less**: every `ExecWPRV10` with `FH` is one with any `FH' ⊇ FH`. -/
theorem execWPRV10_mono {LP : PathsP ι} {NoV : ι → Prop}
    {FH FH' : KLayoutP → U64 → (U64 → Prop) → (U64 → U64) → SP → ι → Prop}
    (hF : ∀ K c hs ρ k i, FH K c hs ρ k i → FH' K c hs ρ k i)
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop}
    (h : ExecWPRV10 LP NoV FH SF P s0 K0 Ch0 s K Ch) : ExecWPRV10 LP NoV FH' SF P s0 K0 Ch0 s K Ch := by
  induction h with
  | refl => exact .refl
  | step _ hS g ih =>
    refine .step ih hS ⟨g.arm, fun p0 k W hph hK hU => ?_, g.serX, g.serC, g.serG, g.keep⟩
    obtain ⟨ρ, hV, i, k0, hi, hvs⟩ := g.start p0 k W hph hK hU
    refine ⟨ρ, hV, i, k0, hi, ?_⟩
    rcases hvs with h1 | ⟨hk, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨hk, fun hn hf => h2 hn (fun h => hf (hF _ _ _ _ _ _ h))⟩
  | hw _ hH ih => exact .hw ih hH

end exec

/-! ## U11 -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end, U10 with vmF's `VSafe9` discharged also at the declining starts** (module docstring). The
conclusion is about the physical memory. -/
theorem serializable_fl4_localU11 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (VmDisAt st ar) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0
  refine serializable_e2ePV9 _ h0 hA0 hK0 hU0 hM0 (execPV9_of_WPRV10 ?_ ?_ ?_ P h0 hA0 hB hc0 hM0 h).1 hq
  · intro Ch K s hK hU c hs q i hC hE hsf
    have nv : K.vcpus = ∅ := by
      obtain ⟨_, ⟨nv, _⟩, _⟩ := hE
      exact nv
    rcases i with i | ((j | j) | j)
    · exact startAt_UN st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE (startU_of_U2 st ar hA a0 hC nv hsf)
    · exact delPteStart_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact invStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact cmStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · intro s K hK hU c k ρ i hM hV hn
    exact vSafe_io st ar hA a0 hM hV (not_not.mp hn)
  · intro s K hK hU c k ρ i hM hV hf
    exact vmF_annV_dis st ar hA (masksWr_plain st) hK hU hM hV hf

/-- **U10 follows from U11** (every U10 execution is a U11 one). -/
theorem serializable_fl4_localU10of11 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (FHAt st ar) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU11 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0
    (execWPRV10_mono (fun _ _ _ _ _ _ h => fhAt_dis st ar h) h) hq

end top

end
end Fl4Proofs.P2.E2EP
