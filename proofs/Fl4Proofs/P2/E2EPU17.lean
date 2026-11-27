/-
# P2 (line p3mc, gen 18): U17, st's `VSafe9` discharged at the st starts whose target is another core's

## The family
`fl4LocW11JC` (P2/StFamC): `fl4LocW11JB` with the st slot's program the extracted tree
`R.localtimer.handle_set_timer_local n target` too. Start facts `StartV2C` [P] (the st glue about that tree).

## The st starts discharged
**`st_k0_fhC`**: at a view start of an st index `j` whose target is, in `ρ`, another core's
(`ρ (fld j.target oAFFINITY) ≠ c`), the armed body is `Safe` at the physical memory: the start state `σ` (`SlJAt`,
`Q`, `QPs`, the view's kernel words, core `c`, locks `hs`) carries the st entry facts (`StPremK2B.pe`,
`stEntK_userV`), and P2/StFhView's `st_fh_annV` applies (the real run declines at `set_timer_target_ok`'s first
read, having written nothing). `StFhAt` (these starts), `U17At := U16At ∨ StFhAt`, **`st_annV_fh`**.

## U17
**`serializable_fl4_localU17`** (`ExecWPRV10 (fl4LocW11JC ⊕ invocations) (¬IoIx) U17At StartV2C`);
**`serializable_fl4_localU16of17`**: U16's statement over the new family (`serializable_fl4_localU16C`'s premises:
`U16At`, `StartV2C`) follows from U17.

## Premises of `serializable_fl4_localU17` vs `serializable_fl4_localU16`
* **Removed: `VSafe9` [J] at the st starts whose target is another core's in `ρ`.** Nothing added.
* **Changed: the family and the start fact**: `fl4LocW11JB` / `StartV2B` [P] become `fl4LocW11JC` / `StartV2C` [P]
  (P2/StFamC: st's glue about the extracted tree; the same claim, only the slot's program is named).
* **Open: `VSafe9` [J] at the st starts whose target is homed on `c`** (the accepting route: `set_timer_target_ok`
  then reads the target's `TIMER_DEADLINE` and, if armed, core `c`'s timer tree — whose nodes may be threads of other
  cores armed in `c`'s tree, timer words owned by `c` — and the accepted run inserts the target in `c`'s tree; the
  U14/U15 `safeVQ` route with st view pins, not done), and at irq (route (a)), vq and invocation starts. `VSafe` [J]
  unchanged.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.StFhView
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD)

noncomputable section
open Classical

section body
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)

set_option maxHeartbeats 8000000 in
/-- **The st body is `Safe` at every view start whose target is another core's** (module docstring). -/
theorem st_k0_fhC (j : StArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (hF : ρ (fld j.target oAFFINITY) ≠ c)
    (hS : StartAt (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0 (.st j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
  by_cases hp : (stSlotC st ar hA (masksWr_plain st)).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = (stSlotC st ar hA (masksWr_plain st)).path j K.toKLayoutV (view K.toKLayout c ρ) hK.base hU.base hp →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := hS'
      obtain ⟨⟨hJ, hQ⟩, -⟩ := id hpre
      have hJ' : SlJAt (L := L) K.toKLayout σ := hJ
      have hQ' : j.Q K.toKLayoutV (view K.toKLayout c ρ) σ := hQ
      have hc' : L.cpu σ = c := hc
      have hl' : j.lk σ = hs := hl
      have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x := hμ
      have hpr : K.toKLayoutV.vcpus = ∅ ∧ StPremK2B st j K.toKLayoutV (view K.toKLayout c ρ) := hp
      have vf : VFacts L K.toKLayoutV := VFacts.ofEmpty hpr.1 hpr.2.bun.choose_spec
      have E := (stEntK_userV hK.base (vf.v hJ').1 (vf.v hJ').2.1 (slJAt_ksb hJ') (hpr.2.pe σ hJ' hQ')).ent
      have h := st_fh_annV ar hA (masksWr_plain st) hK hU hpr.1 hV (lk := j.lk) (n := j.n) (a := a) hJ' E hc'
        hl' hmm (by rw [OwnMap.affA_fld]; exact hF)
      convert h using 2
      unfold LocalPath.body
      rw [hc]
      all_goals rfl
    exact key _ _ (allC st ar hA (masksWr_plain st) L.total a0 (.st j) K (view K.toKLayout c ρ) hK hU)
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
    exact key _ _ (allC st ar hA (masksWr_plain st) L.total a0 (.st j) K (view K.toKLayout c ρ) hK hU)
      (dif_neg hp) hS

end body

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The st starts whose target is another core's in `ρ`.** -/
def StFhAt (_K : KLayoutP) (c : U64) (_hs : U64 → Prop) (ρ : U64 → U64) (_k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.st j) => ρ (fld j.target oAFFINITY) ≠ c
  | _ => False

/-- **The exempt starts of U17**: U16's and the st starts whose target is another core's. -/
def U17At (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop :=
  U16At (S := S) K c hs ρ k0 i ∨ StFhAt (S := S) K c hs ρ k0 i

/-- **U9's re-annotated body is `Safe` at every st start of a chain whose target is another core's** (module
docstring). -/
theorem st_annV_fh {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : StFhAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · have h' : StartU2C st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
        (.st j) := hsf
    have hS := startAt_stC st ar hA a0 (s := { s with mem := CoreView.view K.toKLayout c ρ }) hC hE h'
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    exact st_k0_fhC st ar hA a0 j K hK hU c _ ρ s.mem k hV hf hS
  all_goals exact False.elim hf

/-- **FL4 end to end with st's `VSafe9` discharged at the st starts whose target is another core's** (module
docstring), over the family whose sl and st programs are the extracted trees. The conclusion is about the physical
memory. -/
theorem serializable_fl4_localU17 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U17At (S := S)) (StartV2C st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
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
    rcases hf with (((hf | hf) | hf) | hf)
    · exact vmF_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact vmR_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact sl_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact st_annV_fh st ar hA a0 hC hE hsf hM hV hf

/-- **U16's statement over the new family follows from U17** (every such execution is a U17 one). -/
theorem serializable_fl4_localU16of17 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U16At (S := S)) (StartV2C st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU17 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0
    (execWPRV10_mono (fun _ _ _ _ _ _ hf => Or.inl hf) h) hq

end all

end
end Fl4Proofs.P2.E2EP
