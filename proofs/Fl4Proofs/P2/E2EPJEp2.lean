/-
P2 (line nscope, gen 5): **the serial-exit PTE fact as a glue convention**, the kernel base at every start, and
**the VSpace objects are region `.none` at a bundle state**. Family-agnostic (any `PathsP`); new file only.

1. **No memory link at the serial exit exists in the glue.** `SerExitW` (P2/E2EVFl4W3) reads `K.toKLayout` and the
   chain `Ch` off *some* P3 exit state `σe` (`chainC`), `ExitGhostV` fixes only the ghost maps of the exit `Cfg`, and
   the chain is layout-level (`JReachSt.exit` admits every exit state with the same layout data), so nothing relates
   the serial-exit `Cfg` memory to a store state. Gen 4's `SerExitPte` asked exactly that link. It is avoided here:
   the convention subtracts from the PTE set the ASID-table / pool words *of the epoch start's own memory*:
   **`ptesE K E m`** = the words of `E` that are no ASID-table word and no word of a pool `m`'s table names.
   **`PteConv st K s1`**: some bundle state of `K.toKLayout` (ghost `Zx`) with `K.ptes ⊆ ptesE K (ptesJ Zx) s1.mem`,
   `K.vcpus = ∅`. It is a *choice*, always available: at a serial exit `SerExitW.lay` gives a bundle state of the new
   layout (`ChainLay.bun`), and `K.ptes := ptesE K {b | PtW Zx.L1 b} s1.mem` (the leaf entries) satisfies it
   (`pteConv_of`). **`qPs_at_startC`**: from `PteConv` at the epoch starts, `QPs K st σ` at every start state `σ`
   of the epoch (memory link of `StartAt` / `GlueAt`, `L.ksb σ = K.ksb`). No memory premise at the exit.
   The convention's choice also gives the layout facts `Fl4StepP.ser` asks of the PTE part:
   **`regionOKP_of_conv`** (`RegionOKP` from `RegionOKV`: PTEs region `.none` by (3), no VCPU) and
   **`userOKP_of_conv`** (aligned, not user: `TopPlaced.disj`, IPC-buffer words are `OObj`, page-table words `VObj`).
2. **`L.ksb σ = K.ksb` at every start**: every start fact of the P3 families (`StartP3W4` … `StartP3W9`, `StartW2`)
   has `Ch σ` in its `GlueAt` entry predicate for every slot (vmF, vmR, io, st, irq, sl, vx, vt alike), and
   `ChainLay.bun` makes every chain state a bundle state of `K.toKLayout`: **`ksb_of_chain`**. So it holds at the
   vt / vx / irq / stm starts too, from the glue as it is.
3. **`region_none_other`** (generic, `LayP`): a word of an `H` object of kind `.other n`, in no slot, is region
   `.none`. At a bundle state (`SlJAtZ`): **`region_none_ptw`** (every word of the four levels' tables:
   `PtWAll Zx.L4 Zx.L3 Zx.L2 Zx.L1`) and **`region_none_pool`** (every ASID pool entry `peA p lo`, `p ∈ Zx.P`);
   the ASID-table words are `RegionOKX.asidT`. Sources: `PtRel` / `VsRel.pool` (spec arch objects), `SpecCover.arch`
   (`H` holds them as `.other n`, `12 ≤ n`), `TopPlaced.po` / `.vo` (outside every typed-heap object, so in no slot),
   `TopPlaced.pt` / `VsPlaced.pal` (4 KiB aligned), `LayP` (nodes apart from `H`'s objects, `H` disjoint).

`PtePlanLocked`'s [J] half under the convention: the planned leaf entry must be in `ptesE …` — a leaf entry of the
exit ghost's `L1` and no ASID word of the epoch start's memory. By (3) every word the walk reads above the leaf is
region `.none`, off `K.ptes` (`K.ptes` holds leaf entries only), so `GateW` (`gateW_of_region`) and unchanged in the
epoch (`exec_epoch`); the walk at a start therefore reads the exit-state values. What is still missing: the PageMap
path, a `lookup_pt_slot` read-set lemma, and that the exit ghost's walk lands in `Zx.L1` (P3 `VsRel` / `PoolsIn` /
the `PxERel`s at the bundle state) — left to the PageMap line.

No new [J]/[P]/[W]: `PteConv` is the glue's choice of `K.ptes`, shown satisfiable. No existing statement changed.
-/
import Fl4Proofs.P2.E2EPJEp
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step Allowed Held HwWr hwCfg)

noncomputable section
open Classical

/-! ## 3. The VSpace objects are region `.none` -/

section reg
open Fl4Proofs.P2.OwnMap

/-- **A word of an `.other` object of `H`, in no slot, lies in no region** of `own`. -/
theorem region_none_other {K : KLayout} (hL : LayP K) {q : U64} {n : Nat} (hq : K.heap q = some (.other n))
    {b : U64} (hb : InW q (2 ^ n) b) (hsl : ¬ ∃ p ∈ K.slots, InW p 32 b) : region K b = .none := by
  have hob : InW q (2 ^ (HKind.other n).bits) b := hb
  have huniq : ∀ p k, K.heap p = some k → InW p (2 ^ k.bits) b → k = .other n :=
    fun p k hp hpb => ((hL.uniq hq hp hob hpb).2).symm
  have h1 : ¬ ∃ c, InNode K c b := by
    rintro ⟨c, hc, hb1, hb2⟩
    have hn : q.val + 2 ^ n ≤ K.ksb.val + 13568 + c.val * 4288 ∨
        K.ksb.val + 13568 + c.val * 4288 + 4288 ≤ q.val := hL.node c hc q _ hq
    obtain ⟨hq1, hq2⟩ := hb
    generalize 2 ^ n = N at hn hq2
    omega
  have h3 : ¬ ∃ t, K.heap t = some .tcb ∧ InW t (2 ^ 12) b :=
    fun ⟨t, ht, hb'⟩ => by have := huniq t _ ht hb'; cases this
  have h4 : ¬ ∃ p, K.heap p = some .ntfn ∧ InW p (2 ^ 6) b :=
    fun ⟨p, hp, hb'⟩ => by have := huniq p _ hp hb'; cases this
  have h5 : ¬ ∃ p, (K.heap p = some .ep ∧ InW p (2 ^ 4) b) ∨ (K.heap p = some .reply ∧ InW p (2 ^ 5) b) := by
    rintro ⟨p, ⟨hp, hb'⟩ | ⟨hp, hb'⟩⟩
    · have := huniq p _ hp hb'; cases this
    · have := huniq p _ hp hb'; cases this
  have h6 : ¬ ∃ p z, K.heap p = some (.sc z) ∧ InW p (2 ^ z) b :=
    fun ⟨p, z, hp, hb'⟩ => by have := huniq p _ hp hb'; cases this
  unfold region
  rw [dif_neg h1, dif_neg hsl, dif_neg h3, dif_neg h4, dif_neg h5, dif_neg h6]

variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A' : Type} {arI : machine.Arch A'}
  {AR : A' → Fl4Spec.Cr3 → Prop} {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64}
  {D : Set U64} {K : KLayout} {s : S} {a' : A'} {σ : Fl4Spec.State Unit}

/-- A word outside every typed-heap object is in no slot of the bundle's layout. -/
theorem noSlot_of_outside (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {b : U64}
    (ho : Fl4Proofs.P3.OutsideObjects Zx.th b) : ¬ ∃ p ∈ K.slots, InW p 32 b := by
  rintro ⟨p, hp, hpb⟩
  rw [B.slots] at hp
  obtain ⟨p0, j, hj, rfl⟩ := hp
  obtain ⟨k, hk, hs⟩ := hj.size
  have hv := hj.val B.j.xtop.fin.1.2.pl
  obtain ⟨h1, h2⟩ := hpb
  rw [hv] at h1 h2
  exact ho.2 p0 k hk ⟨by omega, by omega⟩

/-- `H`'s object at a spec arch object, as `SpecCover.arch` gives it. -/
theorem heap_arch (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {q : U64} {ao}
    (hk : σ.kheap q.bv = some (.archObj ao)) : ∃ n, 12 ≤ n ∧ K.heap q = some (.other n) :=
  B.j.cover.arch q.bv ao hk

/-- **Every word of a page table (any of the four levels) is region `.none`** at a bundle state. -/
theorem region_none_ptw (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {b : U64}
    (hb : Fl4Proofs.P3.Vs.PtWAll Zx.L4 Zx.L3 Zx.L2 Zx.L1 b) : region K b = .none := by
  have hTP := B.j.xtop.fin.1.2
  have hPR := B.j.xtop.fin.2.2.1
  have ho := hTP.po b hb
  obtain ⟨q, hq, i, hi, rfl⟩ := hb
  have hao : ∃ ao, σ.kheap q.bv = some (.archObj ao) := by
    rcases hq with h | h | h | h
    · obtain ⟨f, hk, -⟩ := hPR.l4 q h; exact ⟨_, hk⟩
    · obtain ⟨f, hk, -⟩ := hPR.l3 q h; exact ⟨_, hk⟩
    · obtain ⟨f, hk, -⟩ := hPR.l2 q h; exact ⟨_, hk⟩
    · obtain ⟨f, hk, -⟩ := hPR.l1 q h; exact ⟨_, hk⟩
  obtain ⟨ao, hk⟩ := hao
  obtain ⟨n, hn, hH⟩ := heap_arch B hk
  have hpa : q.val % 4096 = 0 := hTP.pt q hq
  have hv := Fl4Proofs.P3.Vs.peA_val (Fl4Proofs.P3.Vs.tbl_fit hpa) hi
  have h12 : 2 ^ 12 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine region_none_other B.layP hH ⟨by rw [hv]; omega, by rw [hv]; omega⟩
    (noSlot_of_outside B ho)

/-- **Every ASID pool entry is region `.none`** at a bundle state. -/
theorem region_none_pool (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {p lo : U64} (hp : p ∈ Zx.P)
    (hlo : lo.val < 512) : region K (Fl4Proofs.P3.Vs.peA p lo) = .none := by
  have hTP := B.j.xtop.fin.1.2
  have hVR := B.j.xtop.fin.2.1
  have ho := hTP.vo _ (Or.inr ⟨p, hp, lo, hlo, rfl⟩)
  obtain ⟨f, hk, -⟩ := hVR.pool p hp
  obtain ⟨n, hn, hH⟩ := heap_arch B hk
  have hpa := (hTP.vs.pal p hp).1
  have hv := Fl4Proofs.P3.Vs.peA_val (Fl4Proofs.P3.Vs.tbl_fit hpa) hlo
  have h12 : 2 ^ 12 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact region_none_other B.layP hH ⟨by rw [hv]; omega, by rw [hv]; omega⟩ (noSlot_of_outside B ho)

/-- **The ASID-table words are region `.none`** at a bundle state (`RegionOKX.asidT`). -/
theorem region_none_tab (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {hi : U64} (hhi : hi.val < 2048) :
    region K (atAF K.ksb hi) = .none :=
  (B.regionOKX.asidT hi hhi).1

end reg

/-! ## 2. The kernel base at every start -/

section ksb
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **A chain state has the layout's kernel base** (every start fact carries `Ch σ`; `ChainLay.bun`). -/
theorem ksb_of_chain {K : OwnMap.KLayout} {Ch : S → Prop} (hCh : ∀ σ, Ch σ → SlJAt (L := L) K σ) {σ : S}
    (h : Ch σ) : L.ksb σ = K.ksb := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B⟩ := hCh σ h
  exact B.ksb

end ksb

/-! ## 1. The convention -/

section conv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The words of `E` that are no ASID-table word and no entry of a pool `m`'s table names.** -/
def ptesE (K : KLayoutP) (E : Set U64) (m : U64 → U64) : Set U64 :=
  {b | b ∈ E ∧ ∀ hi : U64, hi.val < 2048 → b ≠ atAF K.ksb hi ∧
    (m (atAF K.ksb hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 → b ≠ peAF (m (atAF K.ksb hi)) lo)}

variable (st) in
/-- **The PTE-set convention at an epoch start `s1`** (module docstring): a bundle state of `K.toKLayout` with
ghost `Zx`, `K.ptes` inside `ptesE K (ptesJ Zx) s1.mem`, no VCPU. -/
def PteConv (K : KLayoutP) (s1 : Cfg U64 U64 U64 U64) : Prop :=
  ∃ (σe : S) (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Cx Ax : Set U64) (Lst : U64 → List U64) (D : Set U64) (a' : A') (τ : Fl4Spec.State Unit),
    SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σe a' τ ∧ K.ptes ⊆ ptesE K (ptesJ Zx) s1.mem ∧ K.vcpus = ∅

/-- **The convention is a choice**: the leaf entries of a bundle ghost minus the epoch start's ASID words. -/
theorem pteConv_of {K : KLayoutP} {s1 : Cfg U64 U64 U64 U64} {σe : S} {A' : Type} {arI : machine.Arch A'}
    {AR : A' → Fl4Spec.Cr3 → Prop} {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64}
    {D : Set U64} {a' : A'} {τ : Fl4Spec.State Unit} (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σe a' τ)
    (nv : K.vcpus = ∅) (hsub : K.ptes ⊆ ptesE K {b | Fl4Proofs.P3.Vs.PtW Zx.L1 b} s1.mem) : PteConv st K s1 :=
  ⟨σe, A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B, fun _ hb => ⟨ptesL1_sub Zx (hsub hb).1, (hsub hb).2⟩, nv⟩

/-- **`RegionOKP` from the convention's choice** (PTE words are page-table words: region `.none`). -/
theorem regionOKP_of_conv {K : KLayoutP} {σe : S} {A' : Type} {arI : machine.Arch A'}
    {AR : A' → Fl4Spec.Cr3 → Prop} {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64}
    {D : Set U64} {a' : A'} {τ : Fl4Spec.State Unit} (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σe a' τ)
    (hV : RegionOKV K.toKLayoutV) (hsub : K.ptes ⊆ ptesJ Zx) (nv : K.vcpus = ∅) : RegionOKP K :=
  ⟨hV, fun _ he => region_none_ptw B (hsub he), fun _ _ => by rintro ⟨v, hv⟩; exact not_inVcpu_empty nv hv⟩

/-- **`UserOKP` from the convention's choice** (PTE words aligned, no IPC-buffer word). -/
theorem userOKP_of_conv {K : KLayoutP} {σe : S} {A' : Type} {arI : machine.Arch A'}
    {AR : A' → Fl4Spec.Cr3 → Prop} {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64}
    {D : Set U64} {a' : A'} {τ : Fl4Spec.State Unit} (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σe a' τ)
    (hU : UserOKV K.toKLayoutV) (hsub : K.ptes ⊆ ptesJ Zx) : UserOKP K := by
  have hTP := B.j.xtop.fin.1.2
  refine ⟨hU, fun e he => ⟨Fl4Proofs.P3.Vs.PtWAll.aligned hTP.pt (hsub he), fun hu => ?_⟩⟩
  have hUs : K.user = {b | ∃ wp ∈ Zx.B, wp.1 = b} := B.user
  rw [hUs] at hu
  obtain ⟨wp, hwp, hwe⟩ := hu
  obtain ⟨q, hq, i, hi, hqe⟩ := hsub he
  have hpa : q.val % 4096 = 0 := hTP.pt q hq
  have hv := Fl4Proofs.P3.Vs.peA_val (Fl4Proofs.P3.Vs.tbl_fit hpa) hi
  rw [← hqe] at hv
  apply hTP.disj e (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hwp, by rw [hwe], by rw [hwe]; omega⟩)))))))
  exact Or.inr (Or.inr (Or.inl ⟨q, Or.inr hq, by omega, by omega⟩))

/-- **`QPs` at every start of an epoch from the convention** (module docstring): no memory premise at the exit. -/
theorem qPs_at_startC {ι : Type} {LP : PathsP ι} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0) (hU0 : UserOKP K0) (hM0 : MapsP K0 s0)
    (h : ExecP LP s0 K0 s K) (hEp : ∀ s1, EpochStart LP s0 K0 s1 K → PteConv st K s1)
    {σ : S} (hk : L.ksb σ = K.ksb) (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = s.mem x) :
    QPs K st σ := by
  obtain ⟨s1, hS1, hkeep⟩ := exec_epoch h0 hA0 hK0 hU0 hM0 h
  obtain ⟨σe, A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B, hsub, nv⟩ := hEp s1 hS1
  have Q : QPs K st σe := qPs_of_bundle B (fun b hb => (hsub hb).1) nv
  have hnu : ∀ hi : U64, hi.val < 2048 → atAF K.ksb hi ∉ K.user :=
    fun hi hhi hu => Q.uoff _ (Or.inl hu) hi hhi rfl
  have hnp : ∀ hi : U64, hi.val < 2048 → atAF K.ksb hi ∉ K.ptes :=
    fun hi hhi hb => ((hsub hb).2 hi hhi).1 rfl
  have hm : ∀ hi : U64, hi.val < 2048 → L.mem σ (atAF K.ksb hi) = s1.mem (atAF K.ksb hi) := by
    intro hi hhi
    rw [hμ _ (Q.al hi hhi) (hnu hi hhi)]
    exact hkeep _ (gateW_of_region (region_none_tab B hhi) (hnp hi hhi) nv)
  refine ⟨Q.ks, hk, ?_, Q.al, Q.uoff⟩
  intro hi hhi
  rw [hk]
  refine ⟨hnp hi hhi, fun lo hlo hne hb => ?_⟩
  rw [hm hi hhi] at hne hb
  exact ((hsub hb).2 hi hhi).2 hne lo hlo rfl

end conv

end

end Fl4Proofs.P2.E2EP
