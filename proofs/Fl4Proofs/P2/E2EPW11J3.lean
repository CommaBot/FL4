/-
P2 (line nscope, gen 8): **vmF's `lay` [J] discharged** — `serializable_fl4_localW11PJ3`.

The audit (handoff, gen 8) found no slot made vacuous by the convention's `K.vcpus = ∅`: every W11 start record
already asks it (vmF `VmFEntJ10.nv`, vmR `VmRPremP3.nv`, io `IoPremW9.nv`, st `StPremW3.nv`, irq / sl via
`SlotC.ofP3` / `SlotU.ofP3`, vx `VxPremP3.nv`, vt `VtPremP7.nv` / `VtEntJ8.nv`). Of the [J]s left in the premise table,
vmF's `VmFPrem.lay` (`IoLayA (userV K)`, the layout's alignment facts) is a pure layout fact: it holds at every
bundle state of the layout (`SlJAt.ioLayA`, `ioLayA_userV`), and the current chain has one (`ChainOf`'s `Ch σe`).

* **`VmFPremNL`**: `VmFPrem` without `lay`; `VmFPremNL.toPrem`.
* **`StartP3W11L`**: `StartP3W11` with vmF's record `VmFPremNL` — the `GlueAt` asked for every proof of `lay`
  (proof-irrelevant, so for the one there is: a weaker glue obligation). **`startP3W11_of_L`**: given the chain,
  `StartP3W11L` ⇒ `StartP3W11` (lay from the chain's exit state).
* **`ExecWPJ.monoC`**: `ExecWPJ.mono` with the current chain available to the start-fact map (`SerExitW` carried).
* **`serializable_fl4_localW11PJ3`**: `serializable_fl4_localW11PJ2` with `StartP3W11JL` (= `StartP3W11L` [P], the
  armed program the cut relabelling) — vmF's `lay` [J] gone.

No existing statement or file changed.
-/
import Fl4Proofs.P2.E2EPW11J2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY)
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

section prem
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **`VmFPrem` without `lay`** (module docstring). -/
structure VmFPremNL (i : VmFArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [J] `ko`'s memory agrees on TCB affinity words. -/
  mA : ∀ s, VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s →
    ∀ d, (userV K).heap d = some .tcb → m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY)
  /-- [J] `VmPre`, locks and sets kept by user writes. -/
  uf : ∀ s b v, VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s →
    b ∈ (userV K).user → Aligned b →
    VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks (L.wr s b v) ∧
      i.Locks (L.wr s b v) = i.Locks s ∧
      IoRS (st := st) (userV K) i.Locks (L.wr s b v) = IoRS (st := st) (userV K) i.Locks s ∧
      IoWS (st := st) (userV K) i.Locks (L.wr s b v) = IoWS (st := st) (userV K) i.Locks s ∧
      IoDS (st := st) (L.wr s b v) = IoDS (st := st) s

variable {st ar} in
theorem VmFPremNL.toPrem {i : VmFArg S} {K : KLayoutV} {m : U64 → U64} (h : VmFPremNL st ar i K m)
    (hl : IoLayA (userV K)) : VmFPrem st ar i K m :=
  ⟨hl, h.mA, h.uf⟩

end prem

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **`StartP3W11` with vmF's `lay` not asked** (module docstring). -/
def StartP3W11L (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vmF j => ∃ h : VmFPremNL st ar j K m, ∀ hl : IoLayA (userV K),
      GlueAt ((vmFSlot st ar hA hm).liftAt j K m hK hU (h.toPrem hl))
        (fun σ : S => Ch σ ∧ VmFEntJ10 st ar arI AR MR j K σ) c hs m q
  | i => StartP3W11 st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i

variable {arI AR MR}

/-- **`StartP3W11L` gives `StartP3W11`** at the current chain (vmF's `lay` from the chain's exit state). -/
theorem startP3W11_of_L {Ch : S → Prop} {K : KLayoutV} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartP3W11L st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartP3W11 st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i := by
  cases i with
  | vmF j =>
    obtain ⟨σe, hC'⟩ := hC
    have hσ : Ch σe := by obtain ⟨-, -, -, -, -, -, -, -, h'⟩ := hC'; exact h'
    have hl : IoLayA (userV K) := ioLayA_userV (SlJAt.ioLayA (ChainOf.bun hC' σe hσ))
    obtain ⟨h1, hG⟩ := h
    exact ⟨h1.toPrem hl, hG hl⟩
  | vmR j => exact h
  | io j => exact h
  | st j => exact h
  | irq j => exact h
  | sl j => exact h
  | vq j => exact h

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start fact, vmF's `lay` not asked, the armed program cut.** -/
def StartP3W11JL (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K)
    (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : Fl4IxW (S := S)) : Prop :=
  ∃ q0, StartP3W11L st ar hA hm hSt a0 arI AR MR Ch K.toKLayoutV m hK.base hU.base c hs q0 i ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

variable {arI AR MR}

/-- **`ExecWPJ.mono` with the current chain** (the start-fact map may use `SerExitW` of the current layout). -/
theorem ExecWPJ.monoC {ι : Type} {LP : PathsP ι}
    {SF SF' : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι →
      Prop}
    {P : LocPlat st arI AR MR}
    (hSF : ∀ Ch K m hK hU c hs q i, (∃ σe, ChainOf (L := L) arI AR MR σe (KLayoutP.toKLayoutV K).toKLayout Ch) →
      SF Ch K m hK hU c hs q i → SF' Ch K m hK hU c hs q i)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (hB : SerExitW P K0.toKLayoutV Ch0)
    (h : ExecWPJ LP SF P s0 K0 Ch0 s K Ch) : ExecWPJ LP SF' P s0 K0 Ch0 s K Ch ∧ SerExitW P K.toKLayoutV Ch := by
  induction h with
  | refl => exact ⟨.refl, hB⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hX⟩ := ih
    refine ⟨.step hE hS ⟨g.arm, fun p0 k W hph hK hU => ?_, g.serX, g.serC, g.serG, g.keep⟩, ?_⟩
    · obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
      exact ⟨i, hSF _ _ _ _ _ _ _ _ _ hX.chainOf hi⟩
    · by_cases hs : SerStep s1 c1
      · exact g.serX hs
      · obtain ⟨e1, e2⟩ := g.keep hs
        rw [e1, e2]; exact hX
  | hw _ hH ih => exact ⟨.hw ih.1 hH, ih.2⟩

/-- **FL4 end to end, W11's family and glue, rule 8 with the PTE set by convention, vmF's `lay` [J] discharged**
(module docstring): `serializable_fl4_localW11PJ2` with `StartP3W11JL` starts. -/
theorem serializable_fl4_localW11PJ3 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesCanon st K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPJ (fl4LocW11J st ar hA hm hSt a0) (StartP3W11JL st ar hA hm hSt a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  have h' := (ExecWPJ.monoC st (SF' := StartP3W11JC st ar hA hm hSt a0 arI AR MR)
    (fun Ch K m hK hU c hs q i hC hsf => by
      obtain ⟨q0, hW, e⟩ := hsf
      exact ⟨q0, startP3W11_of_L st ar hA hm hSt a0 hC hW, e⟩) hB h).1
  exact serializable_fl4_localW11PJ2 st ar hA hm hSt a0 P hIoa h0 hA0 hB hc0 hM0 h' hq

end top

end
end Fl4Proofs.P2.E2EP
