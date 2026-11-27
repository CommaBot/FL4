/-
# P2 (line p3mc, gen 42): V15 with a CoreView PageMap slot; V13's slot obligations proved; the PageMap `VSafe9` left as one named [J]

## The native obligations, proved
**`slotOblV13`**: `SlotOblV15` of `ExecCfg.native` (gen 41), assembled from U28's per-slot lemmas: `sf` by
`startV2C_of_V13` (the chain is in the obligation's hypotheses) and U28's start cases, `vs` by `vSafe_ioC`, `fh` by
`u28At_all` (every non-io start is a U28 exempt start) and U28's fifteen `…_annV_…` discharges. So
**`serializable_fl4_localV13viaV15`** proves V13's exact statement through `serializable_fl4_V15_exact` (a second,
independent route besides gen 41's `serializable_fl4_localV13ofV15`).

## The CoreView PageMap slot
* Family **`fl4LocV13Pm B`** = `fl4LocV13` ⊕ `pmPathsG hA (masksWr_plain st) B` (the W11PR line's PageMap path,
  P2/InvPmTop3; a `PathsP` is memory-parametric, so the CoreView step instantiates it at core `c`'s view).
* Start fact **`StartPmV`** [P] (stated on the view: the step's `SF` is evaluated at `CoreView.view K c ρ`):
  W11PR's `StartPmG` **plus `GateEp` of the start state**. Reason (finding below): `StartPmG` leaves `GateEp` to
  the epoch witness of the physical line (`pm_hSFQG`: every `GateW` word agrees with the epoch memory), which the
  CoreView obligation does not provide — it only gives `EpochPteN` (region-`.none` words), and the view does rewrite
  a gate-owned word (`tcbRepl`, TCB offset 3520 of another core's thread, `tcbRepl_own`). With `GateEp` in the
  record, `pmStartV_at` (`sf` for PageMap) is a theorem.
* `NoV` (`NoVPm`): V13's on V13's indices, `True` on PageMap (armed re-annotated, as every non-io start).
* **`ExecCfg.nativePm B`** (`Fam := fl4LocV13Pm B`, `SF := StartV13Pm`, `VcpuOK := vcpus = ∅`, `AdStep := False`).
* **`PmFhV B`** [J]: the PageMap `VSafe9` content — at a PageMap start of core `c`'s view whose start fact holds, the
  re-annotated body is `Safe` at the physical memory (the `fh` obligation of `SlotOblV15` at the PageMap summand).
  Not discharged (module "What is missing").
* **`slotOblV13Pm`**: `SlotOblV15 (ExecCfg.nativePm B)` from `slotOblV13`, `pmStartV_at` and `PmFhV`;
  **`serializable_fl4_V15_pm`**: `RunAll s.log s0.mem s.mem` over `ExecV15 (ExecCfg.nativePm B)` — the **exact** form
  (the physical-memory PageMap top `serializable_fl4_localW11PRIPmG` is exact; nothing here needs a permuted
  linearisation: the permutation of mmuAD's tops comes from A/D writes, `AdStep`, not from PageMap).
* **`ExecV15.map`** (an execution over one configuration is one over another when start facts, `NoV`, `VcpuOK`,
  `AdStep` map along an index map) and **`serializable_fl4_localV13ofV15Pm`**: V13's exact statement from
  `serializable_fl4_V15_pm` (V13's executions embed by `.inl`). The converse does not hold (PageMap starts).

## What is missing for `PmFhV` (not cheap, checked)
The Copy / Mint analogue took a CoreView path (`cmPathVU`, P2/InvCMV, InvCMPath8), a guarded-run analysis at every
state agreeing with the view on the read set (`InvCMGd`, `inv_cm_gdA`) and the certificate `inv_cm_annA`
(`PathObl.safe_tr_wrU`: read set `Rd` permitted-owned, write set held, `hgo` = the guarded run is `ok`, `WithinM
StepOK`, `Once`), about 1300 lines on top of the shared InvDel* framework. For PageMap the same three pieces are
needed: (1) its read set at the view — the current thread's TCB and CSpace slots, the own node, the held plan locks'
slots and the held leaf PTEs, the gate-owned upper paging and ASID words (`view_comm_of_region` / `view_pte_comm` /
`view_none_eq` show the view keeps the `.none`-region and PTE words; TCB / node words of the own core are kept by
`view_home` / `view_node_self`); (2) `PmGd`: the guarded PageMap run equals the real one at every state agreeing on
that set (the plan's walk, `pm_accU_of_blkG` is the physical-memory form, through PmObl4's [W] `blk`); (3) the
certificate. (2) also has to restate PmObl4's three [W] fields at the view (they are stated at `PmPreG`), which the
mmuAD line discharged in InvPmRo* / InvPmMv* / InvPmFoot (≈ 3300 lines, not on `par/p3mc`).

No premise on any existing top. New premises of the new top: `B : PmObl4` (its [W] `blk`, `mv`, `roA`, [P] `cs`,
`lk`, as `serializable_fl4_localW11PRIPmG`), `PmFhV B` [J], and the start facts `StartPmV` [P].
-/
import Fl4Proofs.P2.E2EPV15Bridge
import Fl4Proofs.P2.InvPmTop3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP)

noncomputable section
open Classical

/-! ## Mapping an execution along an index map -/

section map
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι κ : Type}

/-- **An execution over `c1` is one over `c2`** along `f`, when start facts, `NoV`, `VcpuOK` and `AdStep` map. -/
theorem ExecV15.map {c1 : ExecCfg S ι} {c2 : ExecCfg S κ} (f : ι → κ)
    (hSF : ∀ Ch K m hK hU c hs q i, c1.SF Ch K m hK hU c hs q i → c2.SF Ch K m hK hU c hs q (f i))
    (hN : ∀ i, ¬ c1.NoV i → ¬ c2.NoV (f i)) (hV : ∀ K m, c1.VcpuOK K m → c2.VcpuOK K m)
    (hA : ∀ K E m a x, c1.AdStep K E m a x → c2.AdStep K E m a x) {P : LocPlat st arI AR MR}
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} {E : U64 → U64}
    (h : ExecV15 c1 P s0 K0 Ch0 s K Ch E) : ExecV15 c2 P s0 K0 Ch0 s K Ch E := by
  induction h with
  | refl => exact .refl
  | step _ hS g ih =>
    refine .step ih hS ⟨g.arm, fun p0 k W hph hK hU => ?_, g.serX,
      fun hs => ⟨hV _ _ (g.serC hs).1, (g.serC hs).2⟩, g.serG, g.keep⟩
    obtain ⟨ρ, hVq, i, k0, hi, hk⟩ := g.start p0 k W hph hK hU
    exact ⟨ρ, hVq, f i, k0, hSF _ _ _ _ _ _ _ _ _ hi, hk.imp (fun ⟨e, hn⟩ => ⟨e, hN i hn⟩) id⟩
  | hw _ hH ih => exact .hw ih hH
  | ad _ hA' ih => exact .ad ih (hA _ _ _ _ _ hA')

end map

/-! ## V13's slot obligations -/

section native
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **V13's slot obligations hold** (module docstring). -/
theorem slotOblV13 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) :
    SlotOblV15 (L := L) arI AR MR (ExecCfg.native st ar hA a0 arI AR MR) where
  sf := by
    intro Ch K s hK hU c hs q i hC hE hsf
    have hsf' := startV2C_of_V13 st ar hA a0 hC hsf
    rcases i with i | ((j | j) | j)
    · exact startAt_UNC st ar hA a0 P hIoa hC hE hsf'
    · exact delPteStart_atN st ar hA (masksWr_plain st) hC hE (hsf'.2 fun _ s b v _ _ _ => hsf'.1.wr s b v)
    · exact invStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf'.2 fun _ s b v _ _ _ => hsf'.1.wr s b v)
    · exact cmStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf'.2 fun _ s b v _ _ _ => hsf'.1.wr s b v)
  vs := by
    intro s K hK hU c k ρ i hM hV hn
    exact vSafe_ioC st ar hA a0 hM hV (not_not.mp hn)
  fh := by
    intro Ch s K hK hU c k ρ i hC hE hsf0 hM hV hn
    have hsf := startV2C_of_V13 st ar hA a0 hC hsf0
    have hf := u28At_all (S := S) K c (fun l => s.lk l = some c) ρ k i hn
    rcases hf with ((((((((((((((hf | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf)
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
    · exact inv_annV_cmA st ar hA a0 hC hE hsf hM hV hf
    · exact inv_annV_pteA st ar hA a0 hC hE hsf hM hV hf

/-- **V13's exact statement through `serializable_fl4_V15_exact`** (module docstring). -/
theorem serializable_fl4_localV13viaV15 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV12 (fl4LocV13 st ar hA a0) (fun i => ¬ IoIx (S := S) i) (StartV13 st ar hA a0 arI AR MR) P s0 K0 Ch0
      s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨E, h'⟩ := (execV15_native_iff st ar hA a0).2 h
  exact serializable_fl4_V15_exact (slotOblV13 st ar hA a0 P hIoa) (native_noAd st ar hA a0 arI AR MR)
    (native_vcpuNone st ar hA a0 arI AR MR) P h0 hA0 hB hc0 hM0 h' hq

end native

/-! ## The CoreView PageMap slot -/

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The index type with PageMap. -/
abbrev IxV13Pm (S : Type) := (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) ⊕ (I64 × localinv.Plan)

/-- **The family with the PageMap slot.** -/
abbrev fl4LocV13Pm (B : PmObl4 st ar Cs Ω Sg Ac Locks) : PathsP (IxV13Pm S) :=
  PathsP.sum (fl4LocV13 st ar hA a0) (pmPathsG hA (masksWr_plain st) B)

/-- **The PageMap start fact on the view** [P] (module docstring): `StartPmG` with `GateEp` of the start state. -/
def StartPmV (B : PmObl4 st ar Cs Ω Sg Ac Locks) (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K)
    (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (j : I64 × localinv.Plan) : Prop :=
  ∃ (σ : S) (a : A), Ch σ ∧ PmQF st Cs Ω Sg Ac Locks j.2 K m σ ∧ PmEx st j.2 σ ∧ PmRoot st j.2 σ ∧ GateEp st K σ ∧
    L.cpu σ = c ∧ Locks σ = hs ∧ (∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x) ∧
    q = (pmPathsG hA (masksWr_plain st) B j K m hK hU).body σ a

/-- **The start facts with PageMap.** -/
def StartV13Pm (B : PmObl4 st ar Cs Ω Sg Ac Locks) (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64)
    (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) : IxV13Pm S → Prop
  | .inl i => StartV13 st ar hA a0 arI AR MR Ch K m hK hU c hs q i
  | .inr j => StartPmV st ar hA B Ch K m hK hU c hs q j

/-- The re-annotated paths: V13's on its indices, every PageMap start. -/
def NoVPm : IxV13Pm S → Prop
  | .inl i => ¬ IoIx (S := S) i
  | .inr _ => True

/-- **The native configuration with PageMap.** -/
def ExecCfg.nativePm (B : PmObl4 st ar Cs Ω Sg Ac Locks) : ExecCfg S (IxV13Pm S) where
  Fam := fl4LocV13Pm st ar hA a0 B
  NoV := NoVPm (S := S)
  SF := StartV13Pm st ar hA a0 arI AR MR B
  VcpuOK := fun K _ => K.vcpus = ∅
  AdStep := fun _ _ _ _ _ => False

variable {arI AR MR}

/-- **[J] The PageMap `VSafe9` content on CoreView** (module docstring): the re-annotated body is `Safe` at the
physical memory at every PageMap start of the view. -/
def PmFhV (B : PmObl4 st ar Cs Ω Sg Ac Locks) : Prop :=
  ∀ (Ch : S → Prop) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (k : SP)
    (ρ : U64 → U64) (j : I64 × localinv.Plan),
    (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → EpochPteN K (CoreView.view K.toKLayout c ρ) →
    StartPmV st ar hA B Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k j → MapsP K s →
    VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem →
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k)

/-- **The PageMap start gives `StartAt`** (`sf` at the PageMap summand). -/
theorem pmStartV_at (B : PmObl4 st ar Cs Ω Sg Ac Locks) {Ch : S → Prop} {K : KLayoutP} {m : U64 → U64}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : I64 × localinv.Plan}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (h : StartPmV st ar hA B Ch K m hK hU c hs q j) :
    StartAt (pmPathsG hA (masksWr_plain st) B j K m hK hU) c hs m q := by
  obtain ⟨σe, Z, H, Cx, nc, -, -, -, hCL, -⟩ := hC
  obtain ⟨σ, a, hCh, hQ, hEx, hRt, hG, hc, hl, hμ, rfl⟩ := h
  exact ⟨σ, a, ⟨⟨hCL.bun σ hCh, hQ, hG⟩, hEx, hRt⟩, hc, hl, hμ, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **The slot obligations with PageMap** (module docstring). -/
theorem slotOblV13Pm (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (B : PmObl4 st ar Cs Ω Sg Ac Locks) (hPm : PmFhV st ar hA (arI := arI) (AR := AR) (MR := MR) B) :
    SlotOblV15 (L := L) arI AR MR (ExecCfg.nativePm st ar hA a0 arI AR MR B) where
  sf := by
    intro Ch K s hK hU c hs q i hC hE hsf
    rcases i with i | j
    · exact (slotOblV13 st ar hA a0 P hIoa).sf Ch K s hK hU c hs q i hC hE hsf
    · exact pmStartV_at st ar hA B hC hsf
  vs := by
    intro s K hK hU c k ρ i hM hV hn
    rcases i with i | j
    · exact (slotOblV13 st ar hA a0 P hIoa).vs s K hK hU c k ρ i hM hV hn
    · exact absurd trivial hn
  fh := by
    intro Ch s K hK hU c k ρ i hC hE hsf hM hV hn
    rcases i with i | j
    · exact (slotOblV13 st ar hA a0 P hIoa).fh Ch s K hK hU c k ρ i hC hE hsf hM hV hn
    · exact hPm Ch s K hK hU c k ρ j hC hE hsf hM hV

theorem nativePm_noAd (B : PmObl4 st ar Cs Ω Sg Ac Locks) :
    (ExecCfg.nativePm st ar hA a0 arI AR MR B).NoAd := fun _ _ _ _ _ h => h

theorem nativePm_vcpuNone (B : PmObl4 st ar Cs Ω Sg Ac Locks) :
    (ExecCfg.nativePm st ar hA a0 arI AR MR B).VcpuNone := fun _ _ h => h

/-- **FL4 end to end over V13's slots and the CoreView PageMap slot** (module docstring): exact form. -/
theorem serializable_fl4_V15_pm (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (B : PmObl4 st ar Cs Ω Sg Ac Locks) (hPm : PmFhV st ar hA (arI := arI) (AR := AR) (MR := MR) B)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15 (ExecCfg.nativePm st ar hA a0 arI AR MR B) P s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_V15_exact (slotOblV13Pm st ar hA a0 P hIoa B hPm) (nativePm_noAd st ar hA a0 B)
    (nativePm_vcpuNone st ar hA a0 B) P h0 hA0 hB hc0 hM0 h hq

/-- **V13's exact statement from the PageMap top** (V13's executions embed by `.inl`). -/
theorem serializable_fl4_localV13ofV15Pm (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (B : PmObl4 st ar Cs Ω Sg Ac Locks) (hPm : PmFhV st ar hA (arI := arI) (AR := AR) (MR := MR) B)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV12 (fl4LocV13 st ar hA a0) (fun i => ¬ IoIx (S := S) i) (StartV13 st ar hA a0 arI AR MR) P s0 K0 Ch0
      s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨E, h'⟩ := (execV15_native_iff st ar hA a0).2 h
  have h2 := ExecV15.map (c2 := ExecCfg.nativePm st ar hA a0 arI AR MR B) Sum.inl
    (fun _ _ _ _ _ _ _ _ _ hi => hi) (fun _ hn => hn) (fun _ _ h => h) (fun _ _ _ _ _ h => h) h'
  exact serializable_fl4_V15_pm st ar hA a0 P hIoa B hPm h0 hA0 hB hc0 hM0 h2 hq

end pm

end
end Fl4Proofs.P2.E2EP
