/-
# P2 (line p3mc, gen 41): bridges for V15 — `CoreView.view` and environment writes; `HwStepP`'s write set; P3 chains under VCPU-word writes

## (a) The view commutes with a write the view does not rewrite or decide on
`CoreView.view K c m b` rewrites only words of TCB, SC and node regions and decides only on TCB `AFFINITY` and SC
`CORE` words (`repl2`, `repl2_decEq`). So a write to a word of any other region commutes with every core's view:
* **`CoreView.view_update_off`**: region not `tcb` / `sc` / `node` ⇒ `view (m[a := x]) = (view m)[a := x]`;
* **`CoreView.view_update_none`**: the same at region `.none` (this generalises `epochPteN_view`, which is the case
  "the view keeps every region-`.none` word": `view_none_eq`);
* **`CoreView.view_comm_of_region`**: for any word set `PW` all of whose words have region `.none`, every write
  `a := x` with `PW a` commutes with every core's view — mmuAD's `MmuAD (PWE K E) m a x` writes such a word
  (`MmuAD.pw`, and `pwe_region` on `par/mmuAD`, P2/MmuADEpoch: `PWE K E b → region b = .none` under `RegionOKP`);
* **`view_pte_comm`**: in particular for the leaf words `K.ptes` (`RegionOKP.none`).

## (3) `HwStepP`'s write set (the Architect's claim, checked)
`HwStepP K s v a x` (`HwStepV`, P2/E2EV): `frame : VmRunFrame K v m m[a := x]`, `kern : a ∉ K.user`, `chg`, `free`.
**`hwStepP_writes`**: the one written word `a` is a kernel word (`a ∉ K.user`) of VCPU `v` (`InVcpu`), not one of
its gate (binding) words, owned by `lock v`. So the claim "`HwStepP` writes only VCPU data words and guest frames"
is **half right**: it writes exactly one VCPU data word (`VData`, `hwStepP_vdata`) and **never a guest-frame / user
word** (`kern`); the write need not be aligned (`HwStepV` asks nothing of it).
**`chain_vcpuWr`**: every P3 chain (`ChainOf … K Ch`) is closed under the write of an aligned, non-user VCPU data word,
given the VT-x [J] layout facts `VcpuHeap`, `VcpuSpec`, `VcpuKsOff` (P2/E2EVHeap, E2EVVcpuWr; the content of
`VFacts`) — by `JAtZ.vcpuWrJ` at the chain state's `JAtSt` witness (σ kept) and `JReachU3.start` (the spec invariants
of `jreach_invU3` at the same σ). **`hwStep_chain`**: hence after an `HwStepP` step every chain state `σ` of every core
that agreed with the memory off user words has a chain state agreeing with the new memory (`L.wr σ a x` for an aligned
`a`, `σ` itself otherwise). `JAtZ.userWrB` is not needed: `HwStepP` writes no user word. Not cheap beyond this: the
`VFacts` [J] are unprovable at P3 scope today (no spec VCPU object at the boot), so the lemma is conditional on them.

No premise on any top. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.E2EPV15Base
import Fl4Proofs.P2.E2EVVcpuWr
import Fl4Proofs.P2.SlJLocMv
open Aeneas Aeneas.Std Result

/-! ## (a) The view and writes outside its rewrite set -/

namespace Fl4Proofs.P2.CoreView
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.OwnMapP (KLayoutP RegionOKP)

/-- **A write to a word that is no TCB, SC or node word commutes with every core's view.** -/
theorem view_update_off {K : KLayout} (hK : RegionOK K) (c : U64) (m : U64 → U64) {a : U64} (x : U64)
    (h1 : ∀ t, region K a ≠ .tcb t) (h2 : ∀ p, region K a ≠ .sc p) (h3 : ∀ d, region K a ≠ .node d) :
    view K c (Function.update m a x) = Function.update (view K c m) a x := by
  have hd : DecEq K m (Function.update m a x) := by
    refine ⟨fun t ht => ?_, fun p b hb => ?_⟩
    · obtain ⟨hr, -⟩ := hK.tcb t ht oAFFINITY (Or.inl rfl)
      exact Function.update_of_ne (fun h => h1 t (by rw [← h]; exact hr)) _ _
    · obtain ⟨hr, -⟩ := hK.scw p b hb
      exact Function.update_of_ne (fun h => h2 p (by rw [← h]; exact hr)) _ _
  funext b
  by_cases hb : b = a
  · subst hb
    rw [Function.update_self]
    have hn : repl K c (Function.update m b x) b = none := by
      unfold repl repl2
      split
      · rename_i t hr; exact absurd hr (h1 t)
      · rename_i p hr; exact absurd hr (h2 p)
      · rename_i d hr; exact absurd hr (h3 d)
      · rfl
    rw [view_none hn, Function.update_self]
  · rw [Function.update_of_ne hb]
    unfold view repl
    rw [repl2_decEq hK hd, Function.update_of_ne hb]

/-- **The view keeps every region-`.none` word** (`epochPteN_view`'s content). -/
theorem view_none_eq {K : KLayout} {c : U64} {m : U64 → U64} {b : U64} (hb : region K b = .none) :
    view K c m b = m b :=
  view_none (by simp only [repl, repl2, hb])

/-- **A write to a region-`.none` word commutes with every core's view.** -/
theorem view_update_none {K : KLayout} (hK : RegionOK K) (c : U64) (m : U64 → U64) {a : U64} (x : U64)
    (ha : region K a = .none) : view K c (Function.update m a x) = Function.update (view K c m) a x :=
  view_update_off hK c m x (fun t h => by rw [ha] at h; cases h) (fun p h => by rw [ha] at h; cases h)
    (fun d h => by rw [ha] at h; cases h)

/-- **An environment write into a word set of region `.none` commutes with every core's view** (mmuAD's `MmuAD (PWE K
E)`: `pwe_region`). -/
theorem view_comm_of_region {K : KLayout} (hK : RegionOK K) {PW : U64 → Prop} (hPW : ∀ b, PW b → region K b = .none)
    (c : U64) (m : U64 → U64) {a : U64} (x : U64) (ha : PW a) :
    view K c (Function.update m a x) = Function.update (view K c m) a x :=
  view_update_none hK c m x (hPW a ha)

/-- **A write to a leaf PTE word commutes with every core's view.** -/
theorem view_pte_comm {K : KLayoutP} (hK : RegionOKP K) (c : U64) (m : U64 → U64) {a : U64} (x : U64)
    (ha : a ∈ K.ptes) : view K.toKLayout c (Function.update m a x) = Function.update (view K.toKLayout c m) a x :=
  view_update_none hK.base.base c m x (hK.none a ha)

end Fl4Proofs.P2.CoreView

/-! ## (3) The hardware step's write set and the P3 chains -/

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout layoutJ)
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G5
open Fl4Proofs.P2.Serial (Cfg)

noncomputable section

/-- **What `HwStepP` writes** (module docstring): one kernel, non-gate word of the VCPU `v`, owned by `lock v`. -/
theorem hwStepP_writes {K : KLayoutP} (hK : RegionOKP K) {s : Cfg U64 U64 U64 U64} {v a x : U64}
    (H : HwStepP K s v a x) :
    a ∉ K.user ∧ InVcpu K.toKLayoutV v a ∧ ¬ VcpuGate (a.val - v.val) ∧ ownV K.toKLayoutV s.mem a = .lock v := by
  have hne : Function.update s.mem a x a ≠ s.mem a := by simpa using H.chg
  rcases H.frame a hne with h | ⟨h1, h2⟩
  · exact absurd h H.kern
  · refine ⟨H.kern, h1, fun hg => ?_, h2⟩
    rw [ownV_on hK.base h1] at h2
    simp [vcpuOwner, hg] at h2

/-- **The word `HwStepP` writes is a VCPU data word.** -/
theorem hwStepP_vdata {K : KLayoutP} (hK : RegionOKP K) {s : Cfg U64 U64 U64 U64} {v a x : U64}
    (H : HwStepP K s v a x) : VData K.toKLayoutV a :=
  ⟨v, (hwStepP_writes hK H).2.1, (hwStepP_writes hK H).2.2.1⟩

section chain
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **A P3 chain is closed under the write of an aligned, non-user VCPU data word** (module docstring; VT-x [J]
facts `VcpuHeap`, `VcpuSpec`, `VcpuKsOff` as hypotheses). -/
theorem chain_vcpuWr (hnd : Fl4Spec.numDomains = 1) {K : KLayoutV} (hV : VcpuHeap K) (hS : VcpuSpec L K)
    (hO : VcpuKsOff K) {σe : S} {Ch : S → Prop} (hC : ChainOf (L := L) arI AR MR σe K.toKLayout Ch) {σ : S}
    (hσ : Ch σ) {b : U64} (hb : VData K b) (hba : Aligned b) (hu : b ∉ K.user) (w : U64) : Ch (L.wr σ b w) := by
  obtain ⟨Z, H, Cx, nc, hK, hnc, hCh, -, -⟩ := hC
  rw [hCh] at hσ ⊢
  obtain ⟨a, τ, hR⟩ := hσ
  obtain ⟨Z', Ac, Lst, D, hth, hB, hk, J, hvx⟩ := hR.atSt' (locKeepSt_st _ _ _ _ _)
  obtain ⟨-, -, -, -, -, -, -, hX, -, hIP, -, hMR, -, hUt, -⟩ := jreach_invU3 hnd hR.reach.1
  have hres : τ.schedulerAction = .resumeCurThread := hX.cr.2
  have elay : layoutJ Z' H (L.ksb σ) nc = layoutJ Z H (L.ksb σe) nc := by
    rw [hk]; unfold layoutJ; rw [hth, hB]
  have B0 : SlJAtZ (L := L) arI AR Z' Cx Ac Lst D (layoutJ Z H (L.ksb σe) nc) σ a τ := ⟨J, elay, hnc, hres⟩
  have B : SlJAtZ (L := L) arI AR Z' Cx Ac Lst D K.toKLayout σ a τ := by rw [hK]; exact B0
  obtain ⟨p, ⟨hp, g1, g2⟩, -⟩ := hb
  have hσp := hS σ A3 arI AR Z' Cx Ac Lst D a τ B p hp
  have hH : H p = some (.other 15) := by
    rw [show H = K.toKLayout.heap from (congrArg OwnMap.KLayout.heap hK).symm]
    exact hV p hp
  have eks : K.ksb = L.ksb σ := (congrArg OwnMap.KLayout.ksb hK).trans hk.symm
  have hks : p.val + 32768 ≤ (L.ksb σ).val ∨ (L.ksb σ).val + 304384 ≤ p.val := by
    rw [← eks]; exact hO p hp
  have hnB : ∀ wp ∈ Z'.B, wp.1 ≠ b := fun wp hw e => hu (by
    show b ∈ K.toKLayout.user
    rw [congrArg OwnMap.KLayout.user hK]
    exact ⟨wp, by rw [← hB]; exact hw, e⟩)
  have J' := J.vcpuWrJ hσp hH hks hba g1 g2 hnB w
  exact ⟨a, τ, .exit ⟨JReachU3.start J' hvx hX hIP hMR hUt, hR.reach.2⟩
    ⟨Z', Ac, Lst, D, hth, hB, (L.ksb_wr _ _ _).trans hk, J', hvx⟩⟩

/-- **A hardware step keeps every chain's agreement with memory** (module docstring): if `σ` is on the chain and agrees
with `m` off user words, some chain state agrees with `m[a := x]` off user words. -/
theorem hwStep_chain (hnd : Fl4Spec.numDomains = 1) {K : KLayoutP} (hK : RegionOKP K) (hV : VcpuHeap K.toKLayoutV)
    (hS : VcpuSpec L K.toKLayoutV) (hO : VcpuKsOff K.toKLayoutV) {σe : S} {Ch : S → Prop}
    (hC : ChainOf (L := L) arI AR MR σe K.toKLayout Ch) {s : Cfg U64 U64 U64 U64} {v a x : U64}
    (H : HwStepP K s v a x) {σ : S} (hσ : Ch σ) (hμ : ∀ y, Aligned y → y ∉ K.user → L.mem σ y = s.mem y) :
    ∃ σ', Ch σ' ∧ ∀ y, Aligned y → y ∉ K.user → L.mem σ' y = Function.update s.mem a x y := by
  by_cases ha : Aligned a
  · refine ⟨L.wr σ a x, chain_vcpuWr hnd hV hS hO hC hσ (hwStepP_vdata hK H) ha H.kern x, fun y hy hyu => ?_⟩
    by_cases e : y = a
    · subst e; rw [Function.update_self, L.mem_wr _ _ _ _ hy hy, if_pos rfl]
    · rw [Function.update_of_ne e, mem_wr_ne' ha hy (Ne.symm e)]; exact hμ y hy hyu
  · refine ⟨σ, hσ, fun y hy hyu => ?_⟩
    have e : y ≠ a := fun e => ha (e ▸ hy)
    rw [Function.update_of_ne e]; exact hμ y hy hyu

end chain

end

end Fl4Proofs.P2.E2EP
