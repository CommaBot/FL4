/-
# P2 (line p3mc, gen 28): U26, the CNodeDelete `VSafe9` discharged at every CNodeDelete start

`InvDelAllAt`: every CNodeDelete start (`invSlotU`, the summand `.inr (.inl (.inr j))`), whatever the length of the
caller's message. Its certificate is `inv_del_annA` (P2/InvDelAnnA: `safe_tr_wrU`, the truncated Delete's IPC-buffer
read included); `hCs` / `hlk` are the start record's `InvPremW.hCs` / `InvPremW.lk` [P], already fields of the start
fact.

* `InvDelAllAt`, `U26At := U25At ∨ InvDelAllAt`, **`u26At_del`** (every CNodeDelete start is exempt);
* **`inv_annV_delA`** (glue as gen 27's `inv_annV_del`, without `invLen_of_view`);
* **`serializable_fl4_localU26`**, **`serializable_fl4_localU25of26`**.

## Premises of `serializable_fl4_localU26` vs `serializable_fl4_localU25`
* **Removed: `VSafe9` [J] at the truncated CNodeDelete starts (message length < 2 in `ρ`); with U25, `VSafe9` [J] is
  asked at no CNodeDelete start.** Nothing added; family and start facts unchanged (`fl4LocW11JC` ⊕ invocations /
  `StartV2C` [P]).
* Open: `VSafe9` [J] at the PTE-delete and Copy / Mint starts; `VSafe` [J].

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.E2EPU25
import Fl4Proofs.P2.InvDelAnnA
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

/-- **Every CNodeDelete start** (module docstring). -/
def InvDelAllAt (K : KLayoutP) (c : U64) (_hs : U64 → Prop) (_ρ : U64 → U64) (_k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inr (.inl (.inr _)) => True
  | _ => False

/-- **The exempt starts of U26**: U25's and every CNodeDelete start. -/
def U26At (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop :=
  U25At (S := S) K c hs ρ k0 i ∨ InvDelAllAt (S := S) K c hs ρ k0 i

/-- **Every CNodeDelete start is a U26 exempt start.** -/
theorem u26At_del (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP) (j : InvArg S) :
    U26At (S := S) K c hs ρ k0 (.inr (.inl (.inr j))) := Or.inr trivial

set_option maxHeartbeats 8000000 in
/-- **U9's re-annotated body is `Safe` at every CNodeDelete start** (module docstring). -/
theorem inv_annV_delA {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : InvDelAllAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with (j | ((j | j) | j))
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
    have h1 := inv_del_annA ar hA hK hU h.nv hV (number := j.number) (a := a) (h.hCs st) h.lk hJ he.2 hqu hc' hl' hmm
    rw [tr_cut (InvCMRS (st := st) K.toKLayout j.Locks σ) (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
      (R.invBodyG j.number j.p) ∅ a] at h1
    have eRS : (invPathVU st ar hA (masksWr_plain st) j K (view K.toKLayout c ρ) hK hU h).RS σ =
        InvCMRS (st := st) K.toKLayout j.Locks σ :=
      funext fun x => propext ⟨fun h' => h'.1, fun h' => ⟨h', not_vData_empty h.nv⟩⟩
    convert h1 using 3
    unfold LocalPath.body
    rw [hc, eRS]
    all_goals rfl
  · exact False.elim hf

/-- **FL4 end to end with CNodeDelete's `VSafe9` discharged at every CNodeDelete start** (module docstring), over
U18's family. The conclusion is about the physical memory. -/
theorem serializable_fl4_localU26 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U26At (S := S)) (StartV2C st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0
  refine serializable_e2ePV9 _ h0 hA0 hK0 hU0 hM0 (execPV9_of_WPRV10S ?_ ?_ ?_ P h0 hA0 hB hc0 hM0 h).1 hq
  · intro Ch K s hK hU c hs q i hC hE hsf
    rcases i with i | ((j | j) | j)
    · exact startAt_UNC st ar hA a0 P hIoa hC hE hsf
    · exact delPteStart_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact invStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact cmStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · intro s K hK hU c k ρ i hM hV hn
    exact vSafe_ioC st ar hA a0 hM hV (not_not.mp hn)
  · intro Ch s K hK hU c k ρ i hC hE hsf hM hV hf
    rcases hf with ((((((((((((hf | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf)
    · exact vmF_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact vmR_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact sl_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact st_annV_fh st ar hA a0 hC hE hsf hM hV hf
    · exact st_annV_h st ar hA a0 hC hE hsf hM hV hf
    · exact vx_annV st ar hA a0 hsf hM hV hf
    · exact vt_annV st ar hA a0 hE hsf hM hV hf
    · exact irq_annV_fh st ar hA a0 hC hE hsf hM hV hf
    · exact irq_annV_hn st ar hA a0 hC hE hsf hM hV hf
    · exact irq_annV_wf st ar hA a0 hC hE hsf hM hV hf
    · exact irq_annV_wh st ar hA a0 hC hE hsf hM hV hf
    · exact inv_annV_del st ar hA a0 hC hE hsf hM hV hf
    · exact inv_annV_delA st ar hA a0 hC hE hsf hM hV hf

/-- **U25's statement follows from U26** (every U25 execution is a U26 one). -/
theorem serializable_fl4_localU25of26 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U25At (S := S)) (StartV2C st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU26 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0
    (execWPRV10_mono (fun _ _ _ _ _ _ hf => Or.inl hf) h) hq

end all

end
end Fl4Proofs.P2.E2EP
