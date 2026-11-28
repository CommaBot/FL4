/-
# P2 (line p3mc, gen 25): U23, irq's `VSafe9` discharged also at the irq starts whose earliest thread is homed and
# whose signal's head waiter is another core's

## The irq starts discharged
`IrqWfAt`: an irq start (`.inl (.irq j)`) where, in `ρ`, the earliest thread `tm` of core `c`'s timer tree (the word
`irqTmW K.ksb c`) is a thread whose `AFFINITY` is `c`, whose bound notification is `WAITING`, and whose head waiter's
`AFFINITY` is not `c` (`IrqWfR`). Its certificate is `irq_wf_annV` (P2/IrqWfAnn): the real run declines inside
`fire_ok` (the waiter may not run here), so the run at a state carrying `ρ` on the read set is computed there, the
part of the tail before `fire_ok` coming from the view start.

**`irq_annV_wf`** (glue, as gen 24's `irq_annV_hn`), `U23At := U22At ∨ IrqWfAt`, **`serializable_fl4_localU23`**,
**`serializable_fl4_localU22of23`**.

## Premises of `serializable_fl4_localU23` vs `serializable_fl4_localU22`
* **Removed: `VSafe9` [J] at every irq start whose earliest thread of `c`'s tree is, in `ρ`, homed on `c` with a
  waiting bound notification whose head waiter is another core's.** Nothing added; family and start facts unchanged
  (`fl4LocW11JC` / `StartV2C` [P]).
* Open: `VSafe9` [J] at the irq starts whose earliest thread is homed and whose bound notification wakes a thread of
  `c` (waiting with a homed head waiter, or idle with `tm` blocked on receive), and at the invocation starts;
  `VSafe` [J] unchanged.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.E2EPU22
import Fl4Proofs.P2.IrqWfAnn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD VDec)

noncomputable section
open Classical

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The irq starts whose earliest thread is homed and whose signal's head waiter is another core's** (module
docstring). -/
def IrqWfAt (K : KLayoutP) (c : U64) (_hs : U64 → Prop) (ρ : U64 → U64) (_k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.irq _) => IrqWfR ρ c (ρ (irqTmW K.ksb c))
  | _ => False

/-- **The exempt starts of U23**: U22's and the irq starts whose signal's head waiter is another core's. -/
def U23At (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop :=
  U22At (S := S) K c hs ρ k0 i ∨ IrqWfAt (S := S) K c hs ρ k0 i

set_option maxHeartbeats 8000000 in
/-- **U9's re-annotated body is `Safe` at every irq start whose earliest thread is homed and whose signal's head
waiter is another core's** (module docstring). -/
theorem irq_annV_wf {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : IrqWfAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · obtain ⟨σe, hC'⟩ := hC
    obtain ⟨hLk, hG0⟩ := hsf
    obtain ⟨q0, ⟨h1, hG⟩, e⟩ := hG0 (fun s _ => hLk.kernDetS _ s)
    obtain ⟨σ', a, hCh, hc, hl, hμ, rfl⟩ := hG
    subst e
    have hJ : SlJAt (L := L) K.toKLayout σ' := ChainOf.bun hC' σ' hCh
    have h1' : K.toKLayoutV.vcpus = ∅ ∧ IrqPremK2B st j K.toKLayoutV (view K.toKLayout c ρ) := h1
    have hc' : L.cpu σ' = c := hc
    have hl' : j.lk σ' = (fun l => s.lk l = some c) := hl
    have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ' x = view K.toKLayout c ρ x := hμ
    obtain ⟨s1, ⟨nv, he⟩, hkeep⟩ := hE
    have hq : QPs K st σ' :=
      qPs_of_convRN (S' := S) (st' := st) (L' := L) (L := L) (σ := σ') he nv ⟨σ', hJ⟩ hkeep hJ.kc.1 hmm
    have etm : tmA (L := L) σ' = irqTmW K.ksb c := irqTmW_eq hq.ksb hc'
    have hF : IrqWfR ρ c (ρ (tmA (L := L) σ')) := by
      rw [etm]; exact hf
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    have h := irq_wf_annV ar hA hK hU nv hV (lk := j.lk) (irq := j.irq) (pl := j.pl) (a := a) hJ hq h1'.2.lt hc'
      hl' hmm hF
    have h' : Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) c (fun l => s.lk l = some c)
        s.mem (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) c (VO K c ρ) ∅
          (tr (fun x => MaxR (userV K.toKLayoutV) st j.lk σ' x ∧ ¬ x ∈ K.ptes) (· ∈ K.user)
            (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ') (masksOf st σ') ar
            (R.localtimer.handle_timer_irq_local j.irq j.pl) ∅ a)) := h
    rw [tr_cut (MaxR (userV K.toKLayoutV) st j.lk σ') (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ') (masksOf st σ') ar
      (R.localtimer.handle_timer_irq_local j.irq j.pl) ∅ a] at h'
    convert h' using 3
    unfold LocalPath.body
    rw [hc]
    all_goals rfl
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf

end all

end
end Fl4Proofs.P2.E2EP
