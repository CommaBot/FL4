/-
# P2 (line p3mc, gen 28): U27, `VSafe9` discharged at every Copy / Mint start too

`InvCMAllAt`: every Copy / Mint start (`cmSlotU`, the summand `.inr (.inr j)`). Its certificate is `inv_cm_annA`
(P2/InvCMAnnA: `safe_tr_wrU`, as `inv_del_annA`); `hCs` / `hlk` are the start record's `InvPremW.hCs` /
`InvPremW.lk` [P], already fields of the start fact.

* `InvCMAllAt`, `U27At := U26At ∨ InvCMAllAt`, **`u27At_cm`**, **`u27At_del`** (every Copy / Mint and every
  CNodeDelete start is exempt);
* **`inv_annV_cmA`** (glue as `inv_annV_delA`, at the Copy / Mint summand, `cmPathVU`);
* **`serializable_fl4_localU27`**, **`serializable_fl4_localU26of27`**.

## Premises of `serializable_fl4_localU27` vs `serializable_fl4_localU26`
* **Removed: `VSafe9` [J] at every Copy / Mint (`cmSlotU`) start.** Nothing added; family and start facts unchanged
  (`fl4LocW11JC` ⊕ invocations / `StartV2C` [P]).
* Open: `VSafe9` [J] at the PTE-delete (`delPteSlot`) starts; `VSafe` [J].

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.E2EPU26
import Fl4Proofs.P2.InvCMAnnA
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

/-- **Every Copy / Mint start** (module docstring). -/
def InvCMAllAt (K : KLayoutP) (c : U64) (_hs : U64 → Prop) (_ρ : U64 → U64) (_k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inr (.inr _) => True
  | _ => False

/-- **The exempt starts of U27**: U26's and every Copy / Mint start. -/
def U27At (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop :=
  U26At (S := S) K c hs ρ k0 i ∨ InvCMAllAt (S := S) K c hs ρ k0 i

/-- **Every Copy / Mint start is a U27 exempt start.** -/
theorem u27At_cm (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP) (j : InvArg S) :
    U27At (S := S) K c hs ρ k0 (.inr (.inr j)) := Or.inr trivial

/-- **Every CNodeDelete start is a U27 exempt start.** -/
theorem u27At_del (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP) (j : InvArg S) :
    U27At (S := S) K c hs ρ k0 (.inr (.inl (.inr j))) := Or.inl (u26At_del K c hs ρ k0 j)

set_option maxHeartbeats 8000000 in
/-- **U9's re-annotated body is `Safe` at every Copy / Mint start** (module docstring). -/
theorem inv_annV_cmA {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : InvCMAllAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with (j | ((j | j) | j))
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · obtain ⟨σe, hC'⟩ := hC
    have hσe : Ch σe := by
      obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
      exact h'
    have hsf' := hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v
    obtain ⟨q0, ⟨h, σ, a, he, hc, hl, hμ, e⟩, rfl⟩ := hsf'
    subst e
    have hJ : SlJAt (L := L) K.toKLayout σ := ChainOf.bun hC' σ he.1
    have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x := hμ
    have hqu : QU st K σ :=
      qU_startN st ⟨σe, ChainOf.bun hC' σe hσe⟩ hJ hE (fun x hx hu => hμ x hx hu)
    have hc' : L.cpu σ = c := hc
    have hl' : j.Locks σ = (fun l => s.lk l = some c) := hl
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    have h1 := inv_cm_annA ar hA hK hU h.nv hV (number := j.number) (a := a) (h.hCs st) h.lk hJ he.2 hqu hc' hl' hmm
    rw [tr_cut (InvCMRS (st := st) K.toKLayout j.Locks σ) (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
      (R.invBodyG j.number j.p) ∅ a] at h1
    have eRS : (cmPathVU st ar hA (masksWr_plain st) j K (view K.toKLayout c ρ) hK hU h).RS σ =
        InvCMRS (st := st) K.toKLayout j.Locks σ :=
      funext fun x => propext ⟨fun h' => h'.1, fun h' => ⟨h', not_vData_empty h.nv⟩⟩
    convert h1 using 3
    unfold LocalPath.body
    rw [hc, eRS]
    all_goals rfl

end all

end
end Fl4Proofs.P2.E2EP
