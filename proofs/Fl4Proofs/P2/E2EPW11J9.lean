/-
P2 (line jsweep, gen 2): **`serializable_fl4_localW11PJ8`** — the top over `fl4LocW11JA` (E2EPW11J8: the
`AFFINITY` agreement in the vmF / vmR paths' `Pre`, `VtTP` in vt's), with no `mA` / `M` / `tp` / `UB` / `pSg` [J].

* **`execP_of_WPJG`**: `execP_of_WPJ` for any family and start fact, given a map from the start fact (with the
  current chain and the epoch invariant `PteConv` + `GateW` agreement) to `StartAt`.
* **`startAt_cutA`**: a `StartAt` of `fl4LocA`'s `ownV` path gives the `StartAt` of its restricted, PTE-cut path
  (`QPs` by `qPs_of_conv` / `pre_ksbA`; the armed program is `cutP` of the body: `body_cutLiftP`).
* **`StartA`** [P] (the glue's start fact): vmF `∃ h : VmFPremA, GlueAt (Ch ∧ VmFEntJ10)`; vmR
  `∃ h : VmRPremA, GlueAt (Ch ∧ VmREntJ11)`; vt `∃ h : VtPremA0, ∃ σ, (Ch σ ∧ VtEntJ8 σ) ∧ ∀ eu, GlueAt (· = σ)`; the
  other five indices `StartP3W11JV` (jsweep gen 1); the armed program is `cutP` of the `ownV` program in each case.
  `startAtV_A` / **`startAt_A`**: `StartA` ⇒ `StartAt` of `fl4LocW11JA` (the new `Pre` conjuncts from the glue's
  memory link, `affAg_of_link`, and the chain's bundle, `vtTP_of_bun`).
* **`serializable_fl4_localW11PJ8`**: premises as `serializable_fl4_localW11PJ7` with `StartA` starts.
* **Satisfiability** (`startA_vmR_sat`, `startA_vt_sat`, `startA_vmF_sat`): at any chain state `σ` with the slot's
  entry facts the start fact holds for `m := L.mem σ` — no hypothesis on the number of cores or on other states'
  memory; the old records were refuted by `vmRPremP3_false` / `vmFPremNL_false` / `vtPremP7M_false` (E2EPW11J8).

No existing statement or file changed.
-/
import Fl4Proofs.P2.E2EPW11J8
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY)
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg xsafeRun_greach
  allowed_of_sinv)

noncomputable section
open Classical

/-! ## Executions, generic in the family -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **An `ExecWPJ` is an `ExecP`, with the epoch invariant**, for any family whose start facts give `StartAt`
(`execP_of_WPJ`'s proof, the start step abstracted as `hSF`). -/
theorem execP_of_WPJG {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) →
      (∃ s1, PteConv st K s1 ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesCanon st K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecWPJ LP SF P s0 K0 Ch0 s K Ch) :
    ExecP LP s0 K0 s K ∧ SerExitW P K.toKLayoutV Ch ∧
      ∃ s1, PteConv st K s1 ∧ ∀ x, GateW K x → s.mem x = s1.mem x := by
  obtain ⟨hC0, hK0, hU0⟩ := boot_okP st P hB hc0
  induction h with
  | refl => exact ⟨.refl, hB, s0, hC0, fun _ _ => rfl⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    have hst : Fl4StepP LP s1 K1 c1 s1' K1' := by
      refine ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hn => (g.keep hn).1⟩
      · obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
        exact ⟨i, hSF _ _ _ _ _ _ _ _ _ hX.chainOf ⟨e1, hCe, hk1⟩ hi⟩
      · have hok := serExitW_ok (g.serX hs) (vcpuLay_empty (g.serC hs).1)
        obtain ⟨σe, hC, hσ⟩ := (g.serX hs).lay
        have hc := pteConv_canon ⟨σe, hC.bun σe hσ⟩ (g.serC hs).1 (g.serC hs).2
        have hP := okP_of_conv hc hok.1 hok.2
        exact ⟨hP.1, hP.2, g.serG hs⟩
    refine ⟨.step hE hS hst, ?_, ?_⟩
    · by_cases hs : SerStep s1 c1
      · exact g.serX hs
      · obtain ⟨e1, e2⟩ := g.keep hs
        rw [e1, e2]; exact hX
    · by_cases hs : SerStep s1 c1
      · obtain ⟨σe, hC, hσ⟩ := (g.serX hs).lay
        exact ⟨s1', pteConv_canon ⟨σe, hC.bun σe hσ⟩ (g.serC hs).1 (g.serC hs).2, fun _ _ => rfl⟩
      · obtain ⟨eK, -⟩ := g.keep hs
        subst eK
        obtain ⟨hr, -, -, hM⟩ := exec_safeRunP h0 hA0 hK0 hU0 hM0 hE
        obtain ⟨-, hSI, -⟩ := xsafeRun_greach h0 hA0 hr
        refine ⟨e1, hCe, fun x hx => ?_⟩
        rw [← hk1 x hx]
        exact step_gate_keep hM (allowed_of_sinv hSI c1) hS hs hx
  | @hw s1 K1 Ch1 v a y _ hH ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    obtain ⟨-, hK, -, hM⟩ := exec_safeRunP h0 hA0 hK0 hU0 hM0 hE
    refine ⟨.hw hE hH, hX, e1, hCe, fun x hx => ?_⟩
    rw [← hk1 x hx]
    exact hw_gate_keep hK hM hH hx

end exec

/-! ## From the `ownV` start to the cut path's start -/

section cut
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- **The cut path's start from the `ownV` path's** (module docstring). -/
theorem startAt_cutA (i : Fl4IxW (S := S)) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K)
    (hU : UserOKP K) {c : U64} {hs : U64 → Prop} {q0 : SP}
    (hS : StartAt ((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV s.mem hK.base hU.base)
      c hs s.mem q0)
    (hE : ∃ s1, PteConv st K s1 ∧ ∀ x, GateW K x → s.mem x = s1.mem x) :
    StartAt (fl4LocW11JA st ar hA hm hSt a0 i K s.mem hK hU) c hs s.mem
      (cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) c q0 ∅) := by
  obtain ⟨s1, hCe, hk1⟩ := hE
  obtain ⟨σ, a, hP, hc, hl, hμ, e⟩ := hS
  have hk := pre_ksbA st ar hA hm hSt a0 i K s.mem hK hU σ hP
  have hq := qPs_of_conv
    (L' := ((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV s.mem hK.base hU.base).L)
    hCe hk1 hk (fun x hx hu => hμ x hx hu)
  refine ⟨σ, a, ⟨hP, hq⟩, hc, hl, hμ, ?_⟩
  show _ = (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _
    (allA st ar hA hm hSt a0 i K s.mem hK hU)).body σ a
  refine Eq.trans ?_ (body_cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _
    (allA st ar hA hm hSt a0 i K s.mem hK hU) σ a).symm
  change _ = cutP _ _ _ _
    (((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV s.mem hK.base hU.base).L.cpu σ)
    (((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV s.mem hK.base hU.base).body σ a) ∅
  rw [hc, ← e]

end cut

/-! ## The start fact -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start fact of `fl4LocW11JA`** [P] (module docstring). -/
def StartA (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vmF j => ∃ q0, (∃ h : VmFPremA st ar j K.toKLayoutV,
      GlueAt ((vmFSlotA st ar hA hm).liftAt j K.toKLayoutV m hK.base hU.base h)
        (fun σ : S => Ch σ ∧ VmFEntJ10 st ar arI AR MR j K.toKLayoutV σ) c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | .vmR j => ∃ q0, (∃ h : VmRPremA st j K.toKLayoutV,
      GlueAt ((vmRSlotA st ar hA hm).liftAt j K.toKLayoutV m hK.base hU.base h)
        (fun σ : S => Ch σ ∧ VmREntJ11 st ar arI AR MR j (userV K.toKLayoutV) σ) c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | .vq (.inr j) => ∃ q0, (∃ h : VtPremA0 st j K.toKLayoutV, ∃ σ : S, (Ch σ ∧ VtEntJ8 st j K.toKLayoutV σ) ∧
      ∀ E : VtEuX st j K.toKLayoutV,
        GlueAt ((vtSlotA st ar hA hm).path j K.toKLayoutV m hK.base hU.base ⟨h, E⟩) (fun σ' : S => σ' = σ)
          c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | i => StartP3W11JV st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i

variable {arI AR MR}

/-- **`StartA` gives a start of `fl4LocA`'s `ownV` path** (with the program it cuts to). -/
theorem startAtV_A (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch)
    {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartA st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    ∃ q0, StartAt ((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
      c hs m q0 ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅ := by
  have hC0 := hC
  obtain ⟨σe, hC'⟩ := hC
  have old : ∀ i : Fl4IxW (S := S), StartP3W11JV st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i →
      ∃ q0, StartAt ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
        c hs m q0 ∧
        q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅ := by
    intro i h
    obtain ⟨q0, hW, e⟩ := h
    have hW' := startP3W11_of_L st ar hA hm hSt a0 hC0 (startP3W11L_of_S st ar hA hm hSt a0
      (startP3W11S_of_T st ar hA hm hSt a0 (startP3W11T_of_U st ar hA hm hSt a0
        (startP3W11U_of_V st ar hA hm hSt a0 hW))))
    exact ⟨q0, startAt_P3W11 st ar hA hm hSt a0 P hIoa hC0 hW', e⟩
  cases i with
  | vmF j =>
    obtain ⟨q0, ⟨h, hG⟩, e⟩ := h
    refine ⟨q0, ?_, e⟩
    show StartAt ((vmFSlotA st ar hA hm).lift (fl4Dflt st ar hm) j K.toKLayoutV m hK.base hU.base) c hs m q0
    rw [SlotU.lift_eq _ _ h]
    exact hG.startAt fun σ he hμ =>
      ⟨he.2.pre st ar hA hK.base (chain_run P hIoa hC' he.1 he.2.hct), affAg_of_link hK.base hU.base hμ⟩
  | vmR j =>
    obtain ⟨q0, ⟨h, hG⟩, e⟩ := h
    refine ⟨q0, ?_, e⟩
    show StartAt ((vmRSlotA st ar hA hm).lift (fl4Dflt st ar hm) j K.toKLayoutV m hK.base hU.base) c hs m q0
    rw [SlotU.lift_eq _ _ h]
    refine hG.startAt fun σ he hμ => ⟨⟨?_, (VmREntJ11.toJ10 st ar hA he.2).toPre st ar hA
      (chain_run P hIoa hC' he.1 he.2.hct)⟩, affAg_of_link hK.base hU.base hμ⟩
    rw [userV_empty h.nv]
    exact ChainOf.bun hC' σ he.1
  | io j => exact old (.io j) h
  | st j => exact old (.st j) h
  | irq j => exact old (.irq j) h
  | sl j => exact old (.sl j) h
  | vq j =>
    cases j with
    | inl j => exact old (.vq (.inl j)) h
    | inr j =>
      obtain ⟨q0, ⟨h0, σ, ⟨hCσ, hE⟩, hG⟩, e⟩ := h
      refine ⟨q0, ?_, e⟩
      have E : VtEuX st j K.toKLayoutV := vtEu_of hE
      have hp : (vtSlotA st ar hA hm).Prem j K.toKLayoutV m := ⟨h0, E⟩
      show StartAt ((vtSlotA st ar hA hm).fam (fl4Dflt st ar hm) j K.toKLayoutV m hK.base hU.base) c hs m q0
      rw [SlotN.fam_pos _ _ hp]
      refine (hG E).startAt fun σ' e' _ => ?_
      subst e'
      have hV := VtEntJ8.pre st hE
      exact ⟨hV, vtTP_of_bun hV.ent.inv (ChainOf.bun hC' σ' hCσ)⟩

/-- **`StartA` gives `StartAt` of `fl4LocW11JA`**, given the current chain and the epoch invariant. -/
theorem startAt_A (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutP} {s : Cfg U64 U64 U64 U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop}
    {q : SP} {i : Fl4IxW (S := S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch)
    (hE : ∃ s1, PteConv st K s1 ∧ ∀ x, GateW K x → s.mem x = s1.mem x)
    (h : StartA st ar hA hm hSt a0 arI AR MR Ch K s.mem hK hU c hs q i) :
    StartAt (fl4LocW11JA st ar hA hm hSt a0 i K s.mem hK hU) c hs s.mem q := by
  obtain ⟨q0, hS, rfl⟩ := startAtV_A st ar hA hm hSt a0 P hIoa hC h
  exact startAt_cutA st ar hA hm hSt a0 i K s hK hU hS hE

end start

/-! ## The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end, W11's glue, PTE convention, the `AFFINITY` agreement in the paths' `Pre`** (module
docstring): every `ExecWPJ` over `fl4LocW11JA` whose starts are `StartA` facts ran as some serial order of its
completed entries. vmF's record keeps `uf` [J]; vmR's `cs` / `kd` [P]; vt's `kd` [P]; no `mA`, `M`, `tp`, `UB`,
`OL`, `SL`, `PL`, `pSg`. -/
theorem serializable_fl4_localW11PJ8 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesCanon st K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPJ (fl4LocW11JA st ar hA hm hSt a0) (StartA st ar hA hm hSt a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨-, hK0, hU0⟩ := boot_okP st P hB hc0
  exact serializable_e2eP _ h0 hA0 hK0 hU0 hM0
    (execP_of_WPJG (fun _ _ _ _ _ _ _ _ _ hC hE hsf => startAt_A st ar hA hm hSt a0 P hIoa hC hE hsf)
      P h0 hA0 hB hc0 hM0 h).1 hq

end top

/-! ## Satisfiability at a chain state, any number of cores -/

section sat
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **vmR's start fact holds at every chain state with vmR's entry facts** (memory `L.mem σ`, core `L.cpu σ`,
locks `j.Locks σ`), given the [P]s `cs` / `kd` and the convention `K.vcpus = ∅`. Nothing is asked about other
states or the number of cores (contrast `vmRPremP3_false`). -/
theorem startA_vmR_sat {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ) (nv : K.vcpus = ∅)
    {j : VmRArg S} (hE : VmREntJ11 st ar arI AR MR j (userV K.toKLayoutV) σ) (cs : ∀ c ∈ j.Cs, c.val < 64)
    (kd : ∀ s : S, SlJAt (L := L) (userV K.toKLayoutV) s → KernDetAt (L := L) (userV K.toKLayoutV) j.Locks s)
    (a : A) :
    ∃ q, StartA st ar hA hm hSt a0 arI AR MR Ch K (L.mem σ) hK hU (L.cpu σ) (j.Locks σ) q (.vmR j) := by
  have h : VmRPremA st j K.toKLayoutV :=
    ⟨nv, ⟨σ, by rw [userV_empty nv]; exact ChainOf.bun hC σ hσ⟩, cs, kd⟩
  exact ⟨_, _, ⟨h, σ, a, ⟨hσ, hE⟩, rfl, rfl, fun _ _ _ => rfl, rfl⟩, rfl⟩

/-- **vt's start fact holds at every chain state with vt's entry facts**, given the [P] `kd` and P1's typing `Nt`. -/
theorem startA_vt_sat {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ)
    {j : VtArg S} (hE : VtEntJ8 st j K.toKLayoutV σ) (kd : ∀ s, KernDetS (L := L) (userV K.toKLayoutV).user j.lk s)
    (Nt : ∀ q ∈ j.Nt, j.H q = some .ntfn) (a : A) :
    ∃ q, StartA st ar hA hm hSt a0 arI AR MR Ch K (L.mem σ) hK hU (L.cpu σ) (j.lk σ) q (.vq (.inr j)) := by
  have h : VtPremA0 st j K.toKLayoutV := ⟨hE.nv, ⟨σ, ChainOf.bun hC σ hσ⟩, kd, Nt⟩
  have E0 : VtEuX st j K.toKLayoutV := vtEu_of hE
  exact ⟨_, ((vtSlotA st ar hA hm).path j K.toKLayoutV (L.mem σ) hK.base hU.base ⟨h, E0⟩).body σ a,
    ⟨h, σ, ⟨hσ, hE⟩, fun _ => ⟨σ, a, rfl, rfl, rfl, fun _ _ _ => rfl, rfl⟩⟩, rfl⟩

/-- **vmF's start fact holds at every chain state with vmF's entry facts**, given `uf` [J] (a statement about the
index and layout only; it does not mention `m`). -/
theorem startA_vmF_sat {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ)
    {j : VmFArg S} (hE : VmFEntJ10 st ar arI AR MR j K.toKLayoutV σ)
    (uf : ∀ s b v, VmPre st ar (userV K.toKLayoutV) j.T j.Cs j.Ω j.U j.H j.Sg j.Rp j.Scs j.Nt j.Z j.Ac j.Locks s →
      b ∈ (userV K.toKLayoutV).user → Aligned b →
      VmPre st ar (userV K.toKLayoutV) j.T j.Cs j.Ω j.U j.H j.Sg j.Rp j.Scs j.Nt j.Z j.Ac j.Locks (L.wr s b v) ∧
        j.Locks (L.wr s b v) = j.Locks s ∧
        IoRS (st := st) (userV K.toKLayoutV) j.Locks (L.wr s b v) = IoRS (st := st) (userV K.toKLayoutV) j.Locks s ∧
        IoWS (st := st) (userV K.toKLayoutV) j.Locks (L.wr s b v) = IoWS (st := st) (userV K.toKLayoutV) j.Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (a : A) :
    ∃ q, StartA st ar hA hm hSt a0 arI AR MR Ch K (L.mem σ) hK hU (L.cpu σ) (j.Locks σ) q (.vmF j) := by
  have h : VmFPremA st ar j K.toKLayoutV := ⟨hE.nv, ⟨σ, ChainOf.bun hC σ hσ⟩, uf⟩
  exact ⟨_, _, ⟨h, σ, a, ⟨hσ, hE⟩, rfl, rfl, fun _ _ _ => rfl, rfl⟩, rfl⟩

end sat

end
end Fl4Proofs.P2.E2EP
