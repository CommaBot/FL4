/-
# P2 (line p3mc, gen 29): U28, `VSafe9` discharged at every PTE-delete start too

`InvPteAllAt`: every PTE-arm CNodeDelete start (`delPteSlot`, the summand `.inr (.inl (.inl j))`). Its certificate
is `inv_pte_annA` (P2/InvDelPteAnnA: `safe_tr_wrU`, as `inv_del_annA`, with the plan's locked leaf entries added to
the agreement set); `hCs` / `hlk` are the start record's `DelPtePrem.hCs` / `DelPtePrem.lk` [P], already fields of
the start fact.

* `InvPteAllAt`, `U28At := U27At ∨ InvPteAllAt`, **`u28At_pte`**;
* **`inv_annV_pteA`** (glue at the PTE-delete summand: `DelPteStart`'s `GlueAt` gives the start state, the body is
  `delPtePath`'s own, read set `InvRSP`, no cut);
* **`serializable_fl4_localU28`**, **`serializable_fl4_localU27of28`**.

## Premises of `serializable_fl4_localU28` vs `serializable_fl4_localU27`
* **Removed: `VSafe9` [J] at every PTE-delete (`delPteSlot`) start.** Nothing added; family and start facts
  unchanged (`fl4LocW11JC` ⊕ invocations / `StartV2C` [P]).
* With U24's `u24At_irq` and U26 / U27, every non-io start class is now exempt (P2/E2EPV11: the top without
  `VSafe9`). Open: `VSafe` [J].

No existing statement changed except the root import list.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `serializable_fl4_localU28`.
-/
import Fl4Proofs.P2.E2EPU27
import Fl4Proofs.P2.InvDelPteAnnA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD VDec nf_node)

noncomputable section
open Classical

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **Every PTE-delete start** (module docstring). -/
def InvPteAllAt (K : KLayoutP) (c : U64) (_hs : U64 → Prop) (_ρ : U64 → U64) (_k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inr (.inl (.inl _)) => True
  | _ => False

/-- **The exempt starts of U28**: U27's and every PTE-delete start. -/
def U28At (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop :=
  U27At (S := S) K c hs ρ k0 i ∨ InvPteAllAt (S := S) K c hs ρ k0 i

/-- **Every PTE-delete start is a U28 exempt start.** -/
theorem u28At_pte (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP) (j : InvArg S) :
    U28At (S := S) K c hs ρ k0 (.inr (.inl (.inl j))) := Or.inr trivial

set_option maxHeartbeats 8000000 in
/-- **U9's re-annotated body is `Safe` at every PTE-delete start** (module docstring). -/
theorem inv_annV_pteA {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : InvPteAllAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with (j | ((j | j) | j))
  · exact False.elim hf
  · obtain ⟨σe, hC'⟩ := hC
    have hσe : Ch σe := by
      obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
      exact h'
    have hsf' := hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v
    obtain ⟨h, σ, a, he, hc, hl, hμ, e⟩ := hsf'
    subst e
    have hJ : SlJAt (L := L) K.toKLayout σ := ChainOf.bun hC' σ he.1
    have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x := hμ
    have hqu : QU st K σ :=
      qU_startN st ⟨σe, ChainOf.bun hC' σe hσe⟩ hJ hE (fun x hx hu => hμ x hx hu)
    have hc' : L.cpu σ = c := hc
    have hl' : j.Locks σ = (fun l => s.lk l = some c) := hl
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    have h1 := inv_pte_annA ar hA hK hU h.nv hV (number := j.number) (a := a) (h.hCs st) h.lk hJ he.2 hqu hc' hl'
      hmm
    convert h1 using 3
    unfold LocalPath.body
    rw [hc]
    all_goals rfl
  · exact False.elim hf
  · exact False.elim hf

end all

end
end Fl4Proofs.P2.E2EP
