/-
# P2 (line pte, generation 15): `blk` discharged — the PageMap slot with `PmObl5` (no `blk`)

* **`pm_blkG`**: gen 13's [W] `PmBlkUW2` at `PmPreG`, proved at every layout with `RegionOKP K` (InvPmBlkD's
  `pmAccG` and InvPmBlkE's `pmFinG` at the store `guard st (PmRSU s) (PmWSU s)`: `IoRS (ptU K) ⊆ PmRSU`
  (`pmRSU_ioRS`), `IoWS (ptU K) ⊆ PmWSU` (`pmWSU_ioWS`), aligned user words and the leaf's `PmRS` / `PmWS` are
  `PmRSU` / `PmWSU` words by definition);
* `PmObl5` = `PmObl4` without `blk`: [W] `mv`, [W] `roA`, [P] `cs`, [P] `lk`; `pmPathsI` (gen 13's `pmPathsG` with
  `acc` from `pm_blkG`; `RegionOKP K` is the family's layout hypothesis), `StartPmI` (= gen 14's `StartPmH`),
  `pm_hSFQI`, **`serializable_fl4_localW11PRIPmI`**.

Premises of `serializable_fl4_localW11PRIPmI` beyond `serializable_fl4_localW11PR`'s (`B : PmObl5`): [W] `mv`,
[W] `roA`, [P] `cs`, [P] `lk`. (Not named `…Pm3`: it still has [W] fields.)

No new named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmBlkE
import Fl4Proofs.P2.InvPmRoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (Once ReadOnce StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)

noncomputable section

section blk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`blk` at `PmPreG`** (gen 13's [W] `PmBlkUW2`, proved; module docstring). -/
theorem pm_blkG (hA : P0.ArchTotal ar) (hK : RegionOKP K) :
    PmBlkUW2 st ar p K Locks (PmPreG st Cs Ω Sg Ac Locks p K μ) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C _ hcap y hy
  have hG := hE.1.2.2
  have P := hE.1.2.1.1.1.1.ptU hG
  have hW : IoWr st (PmWSU st K Locks s) K.heap.scBits s :=
    (P.ioWr (Locks := Locks)).mono (fun _ hy => pmWSU_ioWS hK hy)
  obtain ⟨hdec, hrep⟩ := pmAccG (R := PmRSU st K Locks s) (W := PmWSU st K Locks s)
    (gS := guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) hA hE (fun _ h => pmRSU_ioRS hG h)
    (fun b hb => ⟨hb.1, Or.inl hb.2⟩) (fun b hb => ⟨hb.1, Or.inr hb⟩) hW (fun _ h => pmWSU_ioWS hK h)
    (fun b hb => ⟨hb.1, Or.inl hb.2⟩) (fun b hb => ⟨hb.1, Or.inr hb⟩) emi C hcap hy
  refine ⟨hdec, fun z hz => ⟨hrep z hz, ?_⟩⟩
  have hsw : SWr (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) st (L.curW s) sched.TS_RUNNING :=
    SWr.of_W (pmWSU_ioWS hK (P.stw (Locks := Locks)).2)
  haveI : GRd (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) st (IoRS (st := st) K.ptU Locks s) :=
    grd_sub (fun _ hy => pmRSU_ioRS hG hy)
  exact pmFinG hA hE hW hsw emi C hcap hy hz

end blk

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **What is left of the PageMap slot's obligations** (`PmObl4` without `blk`; module docstring). -/
structure PmObl5 (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) : Prop where
  /-- [W] `move`. -/
  mv : ∀ (j : I64 × localinv.Plan) K m, PmMoveW st ar j.1 j.2 K Locks m (PmPreG st Cs Ω Sg Ac Locks j.2 K m)
  /-- [W] `ReadOnce` of accepting runs (the buffer word read once before its write). -/
  roA : ∀ (j : I64 × localinv.Plan) K m,
    PmRoAccW st ar j.1 j.2 K Locks m (R.invBodyPmG j.1 j.2) (PmPreG st Cs Ω Sg Ac Locks j.2 K m)
  /-- [P] the core set is below 64. -/
  cs : ∀ c ∈ Cs, c.val < 64
  /-- [P] the locks survive a user write. -/
  lk : PmLk st Locks

variable {st ar}

/-- **The PageMap slot family with `blk` proved** (gen 13's `pmPathsG` with `pm_blkG`). -/
def pmPathsI {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl5 st ar Cs Ω Sg Ac Locks) :
    PathsP (I64 × localinv.Plan) :=
  fun j K m hK hU =>
    pm_localPathU (K := K) (m0 := m) (Locks := Locks) ar hA hK hU j.1 j.2 hm
      (P := PmPreG st Cs Ω Sg Ac Locks j.2 K m) (fun _ h => h.1.2.1.1.1.1)
      (pm_accU_of_blkG hA hK (pm_blkG hA hK)) (fun s a r hE => pm_dec hA j.1 s a r hE.1) (B.mv j K m)
      (fun s s' a r0 r hE => pm_ra hA j.1 s s' a r0 r hE.1)
      (pm_hufG (pm_iw B.cs) B.lk j K m)
      (R.invBodyPmG j.1 j.2)
      ((pm_isProgOn hA j.1).mono (fun _ hy => by
        obtain ⟨s0, hP, Al⟩ := hy
        exact ⟨s0, hP.1, alt_pmU Al⟩))
      (pm_noZero j.1 j.2) (B.roA j K m) (fun s s' a r hE => pm_ro hA j.1 s s' a r hE.1)

/-- **The PageMap slot's start fact** (gen 14's `StartPmH` for `pmPathsI`: `PmQF ∧ PmEx`, both from the plan). -/
def StartPmI {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl5 st ar Cs Ω Sg Ac Locks)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) (j : I64 × localinv.Plan) : Prop :=
  ∃ (σ : S) (a : A), Ch σ ∧ PmQF st Cs Ω Sg Ac Locks j.2 K m σ ∧ PmEx st j.2 σ ∧
    L.cpu σ = c ∧ Locks σ = hs ∧
    (∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x) ∧ q = (pmPathsI hA hm B j K m hK hU).body σ a

variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **`hSFQ` of `serializable_fl4_localW11PRI` for `pmPathsI`** (gen 13's `pm_hSFQG` route, `PmRoot` from the
plan by `pmRoot_of_qf`). -/
theorem pm_hSFQI {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl5 st ar Cs Ω Sg Ac Locks) :
    ∀ Ch K m hK hU c hs q j, (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → m x = s1.mem x) →
      StartPmI hA hm B Ch K m hK hU c hs q j → StartAt (pmPathsI hA hm B j K m hK hU) c hs m q := by
  rintro Ch K m hK hU c hs q j ⟨σe, hC⟩ ⟨s1, hc1, hg⟩ ⟨σ, a, hCh, hQ, hEx, hc, hl, hμ, rfl⟩
  obtain ⟨Z, H, Cx, nc, -, -, -, hCL, -⟩ := hC
  exact ⟨σ, a, ⟨⟨hCL.bun σ hCh, hQ, s1.mem, hc1, fun x hx ha hu => (hμ x ha hu).trans (hg x hx)⟩, hEx,
    pmRoot_of_qf hQ⟩, hc, hl, hμ, rfl⟩

end slot

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end over W11's slots and the PageMap slot with `blk` proved** (module docstring). -/
theorem serializable_fl4_localW11PRIPmI (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl5 st ar Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPR (PathsP.sum (fl4LocW11J st ar hA hm hSt a0) (pmPathsI hA hm B))
      (StartW11RI st ar hA hm hSt a0 arI AR MR (StartPmI hA hm B)) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localW11PRI st ar hA hm hSt a0 P hIoa (pmPathsI hA hm B) (pm_hSFQI hA hm B) h0 hA0 hB hc0 hM0
    h hq

end top

end
end Fl4Proofs.P2.E2EP
