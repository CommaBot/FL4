/-
# P2 (line p3mc, gen 23): U21, irq's `VSafe9` discharged at the irq starts whose earliest thread is not homed

## The irq starts discharged
`IrqFhAt`: an irq start (`.inl (.irq j)`) where, in `ρ`, the earliest thread of core `c`'s timer tree (the word
`TIMER_MIN` of `c`'s node, address `irqTmW K.ksb c`) is either none (`0`) or a thread whose `AFFINITY` is not `c`.
There the real `plan_objects` returns the empty plan, so the run never fires a timer (handoff §26a); its certificate
is `irq_fh_annV` (P2/IrqFhAnn): the run at a state carrying `ρ` on the read set goes through the head with the empty
plan and through the tail exactly as at the view start, where P1's invariant holds.

**`irq_annV_fh`** (glue): `StartV2C`'s irq clause is `StartU2`'s, i.e. (through `StartU` … `StartP3W11JV`, `StartP3W4`)
a `GlueAt` of `irqSlotP3W`'s lifted path (`irq_localPathV`, program the extracted tree `R.localtimer.handle_timer_irq_
local`, read set `MaxR (userV K)`), cut at the PTE words (`tr_cut`); the glue state is on the chain (`ChainOf.bun`:
`SlJAt`), `QPs` from `EpochPteN` (`qPs_of_convRN`), and the node word `TIMER_MIN` is `irqTmW K.ksb c` there
(`QPs.ksb`).

`U21At := U20At ∨ IrqFhAt`, **`serializable_fl4_localU21`**, **`serializable_fl4_localU20of21`**.

## Premises of `serializable_fl4_localU21` vs `serializable_fl4_localU20`
* **Removed: `VSafe9` [J] at every irq start whose earliest thread of `c`'s tree is, in `ρ`, none or another core's.**
  Nothing added; family and start facts unchanged (`fl4LocW11JC` / `StartV2C` [P]).
* Open: `VSafe9` [J] at the irq starts whose earliest thread is homed (an accepted fire run is possible there; handoff
  §27b item 3) and at the invocation starts; `VSafe` [J] unchanged.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.IrqFhAnn
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

/-- Core `c`'s node word `TIMER_MIN` at kernel base `kb` (`LawfulStore.nodeAt` unfolded). -/
def irqTmW (kb c : U64) : U64 :=
  core.num.U64.wrapping_add
    (core.num.U64.wrapping_add (core.num.U64.wrapping_add kb 13568#u64) (core.num.U64.wrapping_mul c 4288#u64))
    layout.node.TIMER_MIN

theorem irqTmW_eq {S : Type} {st : machine.Store S} [L : LawfulStore st] {σ : S} {kb c : U64}
    (hk : L.ksb σ = kb) (hc : L.cpu σ = c) : tmA (L := L) σ = irqTmW kb c := by
  unfold tmA LawfulStore.nodeAt irqTmW
  rw [hk, hc]

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The irq starts whose earliest thread is not homed** (module docstring). -/
def IrqFhAt (K : KLayoutP) (c : U64) (_hs : U64 → Prop) (ρ : U64 → U64) (_k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.irq _) => ρ (irqTmW K.ksb c) ≠ 0#u64 → ρ (affA (ρ (irqTmW K.ksb c))) ≠ c
  | _ => False

/-- **The exempt starts of U21**: U20's and the irq starts whose earliest thread is not homed. -/
def U21At (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop :=
  U20At (S := S) K c hs ρ k0 i ∨ IrqFhAt (S := S) K c hs ρ k0 i

set_option maxHeartbeats 8000000 in
/-- **U9's re-annotated body is `Safe` at every irq start whose earliest thread is not homed** (module docstring). -/
theorem irq_annV_fh {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : IrqFhAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
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
    have hF : ρ (tmA (L := L) σ') ≠ 0#u64 → ρ (affA (ρ (tmA (L := L) σ'))) ≠ c := by
      rw [etm]; exact hf
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    have h := irq_fh_annV ar hA hK hU nv hV (lk := j.lk) (irq := j.irq) (pl := j.pl) (a := a) hJ hq h1'.2.lt hc'
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

/-- **FL4 end to end with irq's `VSafe9` discharged at the starts whose earliest thread is not homed** (module
docstring), over U18's family. The conclusion is about the physical memory. -/
theorem serializable_fl4_localU21 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U21At (S := S)) (StartV2C st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
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
    rcases hf with (((((((hf | hf) | hf) | hf) | hf) | hf) | hf) | hf)
    · exact vmF_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact vmR_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact sl_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact st_annV_fh st ar hA a0 hC hE hsf hM hV hf
    · exact st_annV_h st ar hA a0 hC hE hsf hM hV hf
    · exact vx_annV st ar hA a0 hsf hM hV hf
    · exact vt_annV st ar hA a0 hE hsf hM hV hf
    · exact irq_annV_fh st ar hA a0 hC hE hsf hM hV hf

/-- **U20's statement follows from U21** (every U20 execution is a U21 one). -/
theorem serializable_fl4_localU20of21 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U20At (S := S)) (StartV2C st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU21 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0
    (execWPRV10_mono (fun _ _ _ _ _ _ hf => Or.inl hf) h) hq

end all

end
end Fl4Proofs.P2.E2EP
