/-
# P2 (line pte, generation 16): `roA` discharged — the PageMap slot with only [P] premises (`…Pm3`)

* **`pm_roAG`**: gen 12's [W] `PmRoAccW` at `PmPreG` under `RegionOKP K` (invj's `invURoTrW_of` route): `Once` of
  `R.invBodyPmG` at the entry (`pm_entOnce`, P2/InvPmRoD.lean), carried to every alternative `s'` by `once_agreeJ`
  over the accepted run on `guard st (PmRSU s) (PmWSU s)` (`pm_accU_of_blkG` with `pm_blkG`, turned into the tree
  by `pm_isProgOn` / `inv_hp`); the alternative agrees with `s` on `PmRSU s`, the kernel base, the core and the
  masks (`Alt`). (invj's `once_meetG` moves `Once` between read sets along a guarded run; here the read set is the
  path's own `PmRSU` from the start, so it is not needed.)
* `PmObl7` = [P] `cs`, [P] `lk`; `pmPathsK` (`pmPathsJ` with `roA := pm_roAG`), `StartPmK`, `pm_hSFQK`,
  **`serializable_fl4_localW11PRIPm3`**.

Premises of `serializable_fl4_localW11PRIPm3` beyond `serializable_fl4_localW11PR`'s (`B : PmObl7`): [P] `cs` (the
core set is below 64), [P] `lk` (the locks survive a user write). No [W], no [J].

No new named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmRoD
import Fl4Proofs.P2.InvPmMvC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (Once ReadOnce StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)
open Fl4Proofs.P2.OwnMap (KLayout own region TcbSlot NullOrFrame fld)

noncomputable section

section ro
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP}
variable {A : Type} {ar : machine.Arch A}

/-- **`roA` at `PmPreG`** (gen 12's [W] `PmRoAccW`, proved; module docstring). -/
theorem pm_roAG (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hK : RegionOKP K) {number : I64} {m : U64 → U64} :
    PmRoAccW st ar number p K Locks m (R.invBodyPmG number p) (PmPreG st Cs Ω Sg Ac Locks p K m) := by
  intro s s' a r hE hac Al _
  obtain ⟨s1, a1, h0⟩ := hac
  have hg := pm_accU_of_blkG (number := number) hA hK (pm_blkG hA hK) s a s1 a1 hE h0
  have hp := pm_isProgOn (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) (p := p) (K := K)
    (μ := m) hA number
  rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE.1) a] at hg
  have h0' : interp st ar (R.invBodyPmG number p) s a = ok (true, s1, a1) := by
    rw [← inv_hp hp (Narrow.self st) (AltOf.pre hE.1) a]; exact h0
  have hent := pm_entOnce (number := number) hA s a _ hE ⟨s1, a1, h0⟩ h0'
  exact once_agreeJ hm (fun w hw => hw.1) (fun w hw => hw.1) _ (pm_noZero number p) s s' a _ ∅ ∅ Al.ksb Al.cpu
    Al.masks Al.read hg hent

end ro

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **What is left of the PageMap slot's obligations** (`PmObl6` without `roA`: only [P] facts). -/
structure PmObl7 (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) : Prop where
  /-- [P] the core set is below 64. -/
  cs : ∀ c ∈ Cs, c.val < 64
  /-- [P] the locks survive a user write. -/
  lk : PmLk st Locks

variable {st ar}

/-- **The PageMap slot family with `blk`, `mv` and `roA` proved** (`pmPathsJ` with `pm_roAG`). -/
def pmPathsK {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :
    PathsP (I64 × localinv.Plan) :=
  fun j K m hK hU =>
    pm_localPathU (K := K) (m0 := m) (Locks := Locks) ar hA hK hU j.1 j.2 hm
      (P := PmPreG st Cs Ω Sg Ac Locks j.2 K m) (fun _ h => h.1.2.1.1.1.1)
      (pm_accU_of_blkG hA hK (pm_blkG hA hK)) (fun s a r hE => pm_dec hA j.1 s a r hE.1) (pm_mvG hA hK hU)
      (fun s s' a r0 r hE => pm_ra hA j.1 s s' a r0 r hE.1)
      (pm_hufG (pm_iw B.cs) B.lk j K m)
      (R.invBodyPmG j.1 j.2)
      ((pm_isProgOn hA j.1).mono (fun _ hy => by
        obtain ⟨s0, hP, Al⟩ := hy
        exact ⟨s0, hP.1, alt_pmU Al⟩))
      (pm_noZero j.1 j.2) (pm_roAG hA hm hK) (fun s s' a r hE => pm_ro hA j.1 s s' a r hE.1)

/-- **The PageMap slot's start fact** (gen 14's `StartPmH` for `pmPathsK`). -/
def StartPmK {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) (j : I64 × localinv.Plan) : Prop :=
  ∃ (σ : S) (a : A), Ch σ ∧ PmQF st Cs Ω Sg Ac Locks j.2 K m σ ∧ PmEx st j.2 σ ∧
    L.cpu σ = c ∧ Locks σ = hs ∧
    (∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x) ∧ q = (pmPathsK hA hm B j K m hK hU).body σ a

variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **`hSFQ` of `serializable_fl4_localW11PRI` for `pmPathsK`** (as `pm_hSFQJ`). -/
theorem pm_hSFQK {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :
    ∀ Ch K m hK hU c hs q j, (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → m x = s1.mem x) →
      StartPmK hA hm B Ch K m hK hU c hs q j → StartAt (pmPathsK hA hm B j K m hK hU) c hs m q := by
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

/-- **FL4 end to end over W11's slots and the PageMap slot, no [W]** (module docstring). Premises beyond
`serializable_fl4_localW11PR`'s: `B : PmObl7` = [P] `cs`, [P] `lk`. -/
theorem serializable_fl4_localW11PRIPm3 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPR (PathsP.sum (fl4LocW11J st ar hA hm hSt a0) (pmPathsK hA hm B))
      (StartW11RI st ar hA hm hSt a0 arI AR MR (StartPmK hA hm B)) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localW11PRI st ar hA hm hSt a0 P hIoa (pmPathsK hA hm B) (pm_hSFQK hA hm B) h0 hA0 hB hc0 hM0
    h hq

end top

end
end Fl4Proofs.P2.E2EP
