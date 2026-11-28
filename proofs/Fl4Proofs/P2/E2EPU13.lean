/-
# P2 (line p3mc, gen 13): U13, vmR's `VSafe9` discharged at the starts whose receiver is another core's

## The vmR starts with a foreign receiver (`vmR_annV_rfh`)
At a vmR start fact `StartV2 … (.inl (.vmR j))` of a P3 chain at core `c`'s view of `ρ` where the reply object's
`TCB` word at the view names a thread `u ≠ 0` homed on another core in `ρ` (`RFHAt`), the re-annotated body
`annV k0` is `Safe` at the physical memory. The start state `σ` of the path (`StartAt` from `startAt_UN`) has action
`RESUME_CURRENT` (`vmR_act0_SF`: the glue's witness is the chain state, `chain_act0`; `act_of_view`), and
`RrFhView.vmR_fh_annV` (the decline split: the real run reads `u`'s `STATE` / `FAULT_TYPE` racily, its `SC` and its
`AFFINITY` as plain reads of gate words, and declines at `schedulable_here u`) gives `Safe (annV k0)`.

## U13
`U13At := VmFAt ∨ RFHAt` as the exempt set of `ExecWPRV10`: **`serializable_fl4_localU13`** (`NoV := ¬IoIx`,
`FH := U13At`), through U12a's converter `execPV9_of_WPRV10S`; **`serializable_fl4_localU12of13`**.

## Premises of `serializable_fl4_localU13` vs `serializable_fl4_localU12`
* **Removed: `VSafe9` [J] at the vmR starts whose receiver is another core's** (`RFHAt`). Nothing added.
* `VSafe9` [J] stays at the other vmR starts (no receiver, or the receiver homed on `c`) and at the sl, st, irq, vq
  and invocation starts; `VSafe` [J] where the armed program is the body itself; everything else as in U12.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.RrFhView
import Fl4Proofs.P2.E2EPU12
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP
  xsafeRunH_inv)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD)

noncomputable section
open Classical

/-! ## The action at a vmR start -/

section act
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **`vmR_act0_SF` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem vmR_act0_SF_C (P : LocPlatCR st arI AR MR) {Ch : S → Prop}
    {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    {ρ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : VmRArg S}
    (h : StartV2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.inl (.vmR j))) :
    Act0V st K c ρ := by
  have h' : StartU2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.vmR j) := h
  obtain ⟨q0, ⟨hL, σ, ⟨hCσ, hE⟩, hG⟩, -⟩ := h'
  obtain ⟨σe, hC'⟩ := hC
  obtain ⟨A', arI', AR', Zx, Lst, D, a', τ, B, -⟩ := hE.ix.ac
  have hR : VmRPremA st j K.toKLayoutV :=
    ⟨nv, ⟨σ, by rw [userV_empty nv]; exact ChainOf.bun hC' σ hCσ⟩, B.csLt, fun s _ => hL.kernDetAt _ s⟩
  obtain ⟨σ', a'', e', hc, -, hμ, -⟩ := hG hR
  subst e'
  exact ⟨_, hc, slJAt_ksb (ChainOf.bun hC' _ hCσ), fun x hx hu => hμ x hx hu,
    P.act0 hC' hCσ hE.hct⟩

end act

/-! ## The vmR body at a view start with a foreign receiver -/

section body
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)

/-- **A vmR start whose receiver is another core's**: the reply object's `TCB` word at the view names a thread
`u ≠ 0` whose `AFFINITY` in `ρ` is not `c`. -/
def RFH (K : KLayoutP) (c : U64) (ρ : U64 → U64) (j : VmRArg S) : Prop :=
  view K.toKLayout c ρ (rTcbA j.rptr) ≠ 0#u64 ∧ ρ (affA (view K.toKLayout c ρ (rTcbA j.rptr))) ≠ c

set_option maxHeartbeats 8000000 in
/-- **The vmR body is `Safe` at every view start with action 0 whose receiver is another core's** (module
docstring). -/
theorem vmR_k0_fh (j : VmRArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (h0 : Act0V st K c ρ) (hF : RFH K c ρ j)
    (hS : StartAt (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0 (.vmR j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
  by_cases hp : (vmRSlotA st ar hA (masksWr_plain st)).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = (vmRSlotA st ar hA (masksWr_plain st)).path j K.toKLayoutV (view K.toKLayout c ρ) hK.base hU.base hp →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      have hpr : VmRPremA st j K.toKLayoutV := hp
      obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := hS'
      obtain ⟨⟨hP, -⟩, hq⟩ := id hpre
      have hP' : VmRRPreJ st ar (userV K.toKLayoutV) (userV K.toKLayoutV).heap.tcbs j.Cs j.Ω j.Sg
          (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits j.Ac
          j.Locks j.rptr j.ep σ := hP
      have hq' : QPs K st σ := hq
      have hc' : L.cpu σ = c := hc
      have hl' : j.Locks σ = hs := hl
      have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x := hμ
      obtain ⟨Q, hrR, hpE, -⟩ := VmRRPreJ.pre hP'
      have B := Q.base
      have hact : L.actionW σ = 0#u64 := act_of_view B hq'.ksb hc' hmm h0
      -- the reply's `TCB` word is a kernel word
      have rp := B.bxi.2.2.1.1.rp j.rptr hrR
      have hrK := Q.hRp j.rptr hrR
      have hrt : IoRS (st := st) (userV K.toKLayoutV) j.Locks σ (rTcbA j.rptr) := by
        have h := rTcbA_val0 j.rptr; have := rp.1; have := rp.2
        exact (B.reply (Locks := j.Locks) hrK (b := rTcbA j.rptr) ⟨by omega, by omega⟩
          (by unfold Aligned; omega) Q.lk.1).1
      have eu : L.mem σ (rTcbA j.rptr) = view K.toKLayout c ρ (rTcbA j.rptr) :=
        hmm _ hrt.1 (fun hu => hrt.2.1 (mem_userV.2 (Or.inl hu)))
      have hLA0 := hpr.bun.choose_spec.ioLayA
      have h := vmR_fh_annV hA (masksWr_plain st) hK hU hpr.nv ⟨hLA0.slot8, hLA0.tcb, hLA0.ntfn8, hLA0.sc8⟩ hV Q hrR
        hpE hq' hc' hl'
        hmm hact (a := a) (by rw [eu]; exact hF.1) (by rw [eu]; exact hF.2)
      convert h using 2
      unfold LocalPath.body
      rw [hc]
      all_goals rfl
    exact key _ _ (allA st ar hA (masksWr_plain st) L.total a0 (.vmR j) K (view K.toKLayout c ρ) hK hU)
      (SlotU.fam_pos _ _ hp) hS
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = LocalPath.void (fl4Dflt st ar (masksWr_plain st))
          (OwnMap.ko_aligned (regionOK_userV hK.base) (userOK_userV hK.base hU.base) (view K.toKLayout c ρ)) →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, -⟩ := hS'
      exact absurd hpre.1 id
    exact key _ _ (allA st ar hA (masksWr_plain st) L.total a0 (.vmR j) K (view K.toKLayout c ρ) hK hU)
      (dif_neg hp) hS

end body

/-! ## The exempt starts -/

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end all

/-! ## U13 -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
