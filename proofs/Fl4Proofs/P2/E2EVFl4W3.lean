/-
P2 (line famw, gen 2): **`Fl4StepV.ser` [J] and `Fl4StepV.start` [P] derived from P3's chain and named glue premises**
(new definitions only; `serializable_fl4_localW2` and everything it uses are unchanged).

## 1. The VCPU fields of `RegionOKV` (`regionOKV_of_JAtZ`)

`RegionOKV K` is `RegionOK K.toKLayout` (P3 at a serial exit: `OwnMap.ok_of_JAtZ`, `loc_chain_all`'s `hK`) plus three
VCPU fields. All three are derived here from the layout convention **`VcpuHeap`** [J] (every VCPU of the layout is a
heap object `.other 15`) and P1's heap disjointness (`HeapOK.disj`, `LayP.node`), with one more ingredient for the
slots:
* `none` (a VCPU word lies in no region of `own`): `region_vcpu_none` — nodes by `LayP.node`, TCB / notification /
  endpoint / reply / SC objects by `noVcpu_of_kind`, and **slots by `slot_noVcpu`**: a slot of `Z.th` lies in its
  CNode or TCB `q` (`IsSlotAt.val`, `JPlaced.cnode` / `.tcb`), `q` is a spec CNode / TCB (`StateRel`), a VCPU of the
  layout a spec `vcpu` object (`VcpuSpec` [J], gen 6's `VFacts.spec`), so `q ≠ v` and the two heap objects are apart.
  (Heap kinds alone do not separate them: a CNode of 2^10 slots is `.other 15` too.)
* `disj`: two VCPUs sharing a word are one (`HeapOK.disj`); `tcbw`: `v + 0x5000` does not wrap (`HeapOK.fits`).
**`regionOKV_of_JAtZ`**: `RegionOKV K` from `RegionOK K.toKLayout`, a bundle state `SlJAt K.toKLayout s`, `VcpuHeap K`
and `VcpuSpec L K`. **`regionOKV_of_empty`**: at `K.vcpus = ∅` (P3-scope layouts) from `RegionOK` alone.

## 2. The glue premises, named

* **`ExitGhostV K c`** [P] (Rust glue: fl4-sync's gate release after a serial entry): the ghost maps a serial step
  installs are rule 7's for the new layout (`own := ownV K`, `cls`, `ko`). It is `SerExit.ExitGhost`'s map part with
  `own` replaced by `ownV`; its memory part is not needed for `ser`.
* **`SerExitW P K Ch`** [P] (ghost choice): the new layout `K` (its `KLayout` part) and the chain `Ch` of store states
  the following local paths start from are the ones P3 gives (`chainC`, a choice from **`chainOf_exists`**, i.e.
  `loc_chain_all`) at some P3 exit state `σe` (`JReachU17`). Its P3 content (`ChainOf`: `K = layoutJ …`, `Ch` the
  `JReachSt` chain from `σe`, `RegionOK`, `UserOK`, clause 7 on `Ch`, `σe ∈ Ch`) is **proved** (`chainC_spec`); what is
  assumed is only that the model's ghost is that choice and that the serial step's exit is a P3 exit.
* **`VcpuLay L K`** [J] (VT-x layout cluster, with `hvK`): `VcpuHeap K ∧ VcpuSpec L K`; vacuous at `K.vcpus = ∅`
  (`vcpuLay_empty`).
* **`GlueAt P Ent c hs μ q`** [P] (Rust glue: the entry asm and fl4-sync's `local_syscall` / `local_vm_fault` /
  `run_timer_irq` / `local_vm_exit`): the program `q` core `c` starts is the body of path `P` run from a store state `σ`
  on core `c` with exactly the locks `hs`, agreeing with the model memory `μ` off user words, and `Ent σ` — the entry
  facts, which always include `Ch σ` (σ is a state of P3's current chain) where the path's `Pre` uses the bundle.
  This is `StartAt` with `Pre` replaced by `Ent`; `GlueAt.startAt` turns it back given `Ent → Pre`.

**Why these cannot be proved in Lean.** `Serial.Cfg` is an abstract model of fl4-sync's gate / active-flag protocol
(`P2/Serial.lean`): its memory, lock table and ghost maps are model state, and its programs are annotated with the
store state they start from. The correspondence between a model step and a run of the real kernel — that the core's
registers and memory at `local_*` entry are a store state on P3's chain, that the locks fl4-sync took are the path's
`Locks`, that the extracted body is what runs (`q = body σ a`), and which ghost maps a serial exit installs — is the
refinement between the trusted Rust glue (`crates/fl4-sync`, the entry asm in `crates/fl4-arch-*`, both outside the
Charon/Aeneas extraction, listed in `TRUSTED`) and `Serial`, which no Lean model of the glue exists to discharge.

## 3. `Fl4StepV` from the glue premises (`ExecW`)

`Fl4StepW LP SF P s K Ch c s' K' Ch'`: a core step with ghost chain `Ch` beside the layout: `arm` [P] (as before),
`start` [P] (some index `i` with `SF Ch K s.mem hK hU c locks k i`, a per-path start fact), `ser` (`SerExitW` [P] ∧
`VcpuLay` [J] ∧ `ExitGhostV` [P]), `keep` (layout and chain kept off serial steps). `ExecW` is `ExecV` with those
steps. **`execV_of_W`**: an `ExecW` is an `ExecV` (`Fl4StepV.ser` by `serExitW_ok`: `RegionOKV` by
`regionOKV_of_JAtZ` at `σe`, `UserOKV` by `chainC_spec`; `Fl4StepV.start` by the caller's `SF → StartAt` given clause 7
on `Ch`), and its layout stays `SerExitW`.

For `fl4LocW2`, **`StartW2`** is the start fact, per index (`Fl4Ix`):

| index | slot record (was inside `start` [P]) | `Ent σ` (beside `GlueAt` [P]) | `Pre` from |
|---|---|---|---|
| `vmF` | `VmFPrem` | the path's `Pre` (`VmPre (userV K) …`) [J] | itself |
| `vmR` | `VmRPrem` | the path's `Pre` (`VmRRPre (userV K) …`) [J] | itself |
| `io` | `IoPremW2` | `Ch σ ∧ Q K m σ` ([J] `Q`) | clause 7 (`SlJAt K`) |
| `st` | `StPremK2` | `Ch σ ∧ Q K m σ` ([J] `Q`) | clause 7 |
| `irq` | `IrqPremK2` | `Ch σ` | clause 7 + `GlueAt`'s memory link (`IrqPreV`) |
| `sl` | `SlPremK` | `Ch σ ∧ SlQ … σ` ([J]/[P] as `SlQ`) | clause 7 |
| `vx` | `VxPrem` | `Ch σ ∧ VxEntJ` | `vexitEnt_of` / `vexitPEnt_of` at clause 7 |
| `vt` | `VtPremW` | `Ch σ ∧ VtEntJ` | `vtPre_ofJ` at clause 7 |

`startAt_W2` proves `SF → StartAt` for every index (`SlotU/C.lift_eq`, `SlotN.fam_pos`, `GlueAt.startAt`).

**`serializable_fl4_localW3`**: `serializable_fl4_localW2`'s conclusion for every `ExecW` over `fl4LocW2` with start
fact `StartW2`.

## Premise table diff vs `serializable_fl4_localW2`

| removed | added |
|---|---|
| `RegionOKV K0`, `UserOKV K0` [J] | `SerExitW P K0 Ch0` [P] (boot exit is a P3 exit; ghost = P3's chain), `VcpuLay L K0` [J] |
| `Fl4StepV.ser` [J] per serial step | `SerExitW` [P], `VcpuLay` [J] (vacuous at `vcpus = ∅`), `ExitGhostV` [P] |
| `Fl4StepV.start` [P] per start (opaque: `StartAt` of some family member) | `StartW2`: `GlueAt` [P] (core / locks / memory / body, start state on the chain) + the slot's record (as before, now visible) + the table's `Ent` caller facts |
| — | `LocPlat` (`loc_chain_all`'s platform premises, P3's, tagged there), `[PlainStore st]` |

`Fl4StepV.arm` [P] and `HwStepV` [P] are unchanged. The `SlJAt K` part of every bundle-based `Pre` (io / st / irq /
sl / vx / vt) is no longer asked: it is clause 7 of `loc_chain_all`.
-/
import Fl4Proofs.P2.E2EVFl4W2
open Aeneas Aeneas.Std Result

/-! ## The chain P3 gives at a serial exit -/

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

noncomputable section

section chain
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The P3 facts of one chain** of store states with layout `K`: `RegionOK` / `UserOK` of `K` and P3's bundle
(clause 7 of `loc_chain_all`) at every state of the chain. -/
structure ChainLay (K : KLayout) (Ch : S → Prop) : Prop where
  hK : RegionOK K
  hU : Fl4Proofs.P2.E2E.UserOK K
  bun : ∀ σ, Ch σ → SlJAt (L := L) K σ

/-- **`loc_chain_all`'s platform premises** (P3's, tagged there), bundled. -/
structure LocPlat (st : machine.Store S) [LawfulStore st] {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) : Prop where
  ari : ARIface arI AR
  tot : P0.ArchTotal arI
  nd : Fl4Spec.numDomains = 1
  mach : MachPlat arI MR
  kd : MRKeepD arI MR
  io : MRKeepIo arI MR
  pa : PPPlatA arI AR
  ia : IrqPlatA arI AR
  t : TimeAgree arI
  max : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv
  tu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄
  ref : ArchRefines arI AR
  pi : PortInValMR arI MR
  sx : P1.StoreExt st
  dr : SetDlDetR (A := A3) MR

variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The chain P3 gives from the exit `σe`** (`loc_chain_all`'s conclusion for `K` and `Ch`): `K` is the layout read
off `σe` at some ghosts, `Ch` the `JReachSt` chain from `σe` at those ghosts, `ChainLay K Ch`, and `σe ∈ Ch`. -/
def ChainOf (σe : S) (K : KLayout) (Ch : S → Prop) : Prop :=
  ∃ (Z : XSets) (H : Heap) (Cx : Set U64) (nc : Nat), K = layoutJ Z H (L.ksb σe) nc ∧ (∀ c : U64, c ∈ Cx ↔ c.val < nc) ∧
    Ch = (fun σ => ∃ (a : A3) (τ : Fl4Spec.State Unit),
      JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb σe) σ a τ) ∧
    ChainLay (L := L) K Ch ∧ Ch σe

variable {arI AR MR}

/-- **At every P3 exit there is such a chain** (`loc_chain_all`). -/
theorem chainOf_exists [Fl4Proofs.P1.PlainStore st] (P : LocPlat st arI AR MR) {σe : S} {a3 : A3}
    {τ : Fl4Spec.State Unit} (h : JReachU17 (L := L) arI AR MR σe a3 τ) :
    ∃ KC : KLayout × (S → Prop), ChainOf (L := L) arI AR MR σe KC.1 KC.2 := by
  obtain ⟨Z, H, Cx, nc, hnc, hK, hU, -, h1, -, -, -, -, -, h7, -, -, -⟩ :=
    loc_chain_all P.ari P.tot P.nd P.mach P.kd P.io P.pa P.ia P.t P.max P.tu P.ref P.pi P.sx P.dr h
  exact ⟨(layoutJ Z H (L.ksb σe) nc, fun σ => ∃ (a : A3) (τ : Fl4Spec.State Unit),
      JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb σe) σ a τ),
    Z, H, Cx, nc, rfl, hnc, rfl, ⟨hK, hU, fun σ ⟨a, τ', hσ⟩ => h7 σ a τ' hσ⟩, ⟨a3, τ, h1⟩⟩

/-- **The chain chosen at a P3 exit** (a choice from `chainOf_exists`). -/
def chainC [Fl4Proofs.P1.PlainStore st] (P : LocPlat st arI AR MR) {σe : S} {a3 : A3} {τ : Fl4Spec.State Unit}
    (h : JReachU17 (L := L) arI AR MR σe a3 τ) : KLayout × (S → Prop) :=
  Classical.choose (chainOf_exists P h)

theorem chainC_spec [Fl4Proofs.P1.PlainStore st] (P : LocPlat st arI AR MR) {σe : S} {a3 : A3}
    {τ : Fl4Spec.State Unit} (h : JReachU17 (L := L) arI AR MR σe a3 τ) :
    ChainOf (L := L) arI AR MR σe (chainC P h).1 (chainC P h).2 :=
  Classical.choose_spec (chainOf_exists P h)

end chain
end
end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld region InW InNode LayP RegionOK layoutJ)
open Fl4Proofs.P2.E2E (LocalPath StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

/-! ## 1. The VCPU fields of `RegionOKV` -/

section regv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutV}

/-- **A slot word is no VCPU word** at a bundle state where the VCPUs are spec `vcpu` objects (module docstring). -/
theorem slot_noVcpu {s : S} (hJ : SlJAt (L := L) K.toKLayout s) (hS : VcpuSpec L K) (hV : VcpuHeap K)
    {p : U64} (hp : p ∈ K.slots) {b : U64} (hb : InW p 32 b) : ¬ ∃ v, InVcpu K v b := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
  have hsl : p ∈ {a | Fl4Proofs.P3.IsSlot Zx.th a} := B.slots ▸ hp
  obtain ⟨q, i, hqi, rfl⟩ := hsl
  obtain ⟨Tr, Cq, hJP⟩ := B.j.jpl
  have hval := hqi.val hJP.pl
  have hR := B.j.xtop.rel.2.1.1
  rintro ⟨v, hvK, hv1, hv2⟩
  obtain ⟨x, hx⟩ := hS s A' arI AR Zx Cx Ax Lst D a' σ B v hvK
  have hVv : K.heap v = some (.other 15) := hV v hvK
  have hH : HeapOK K.heap := hJP.heap
  obtain ⟨k, hq, hfit, hne⟩ : ∃ k, K.heap q = some k ∧ q.val + 32 * i + 32 ≤ q.val + 2 ^ k.bits ∧ q ≠ v := by
    rcases hqi with ⟨r, hq, hi⟩ | ⟨hq, hi⟩
    · obtain ⟨cs, hcs, -⟩ := hR.cnode q r hq
      refine ⟨_, hJP.cnode q r hq, ?_, ?_⟩
      · show q.val + 32 * i + 32 ≤ q.val + 2 ^ (r + 5)
        have e : 2 ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; ring
        rw [e]
        have hi' : i < 2 ^ r := hi
        generalize 2 ^ r = N at hi' ⊢
        omega
      · rintro rfl; rw [hx] at hcs; cases hcs
    · obtain ⟨tc, htc, -⟩ := hR.tcb q hq
      refine ⟨_, (hJP.tcb q).1 hq, ?_, ?_⟩
      · show q.val + 32 * i + 32 ≤ q.val + 4096
        have hi' : i < 6 := hi
        omega
      · rintro rfl; rw [hx] at htc; cases htc
  have hd := hH.disj q k v _ hq hVv hne
  have e15 : (HKind.other 15).bits = 15 := rfl
  rw [e15, two15] at hd
  obtain ⟨hb1, hb2⟩ := hb
  rw [hval] at hb1 hb2
  generalize 2 ^ k.bits = N at hd hfit
  omega

/-- **A VCPU word lies in no region of `own`** (`RegionOKV.none`). -/
theorem region_vcpu_none (hL : LayP K.toKLayout) (hV : VcpuHeap K)
    (hsl : ∀ p ∈ K.slots, ∀ b, InW p 32 b → ¬ ∃ v, InVcpu K v b) {v b : U64} (h : InVcpu K v b) :
    region K.toKLayout b = .none := by
  have hv : ∃ v, InVcpu K v b := ⟨v, h⟩
  have hH : HeapOK K.heap := hL.heap
  have h1 : ¬ ∃ c, InNode K.toKLayout c b := by
    rintro ⟨c, hc, hb1, hb2⟩
    have hn := hL.node c hc v _ (hV v h.1)
    obtain ⟨-, hv1, hv2⟩ := h
    have e15 : (HKind.other 15).bits = 15 := rfl
    rw [e15, two15] at hn
    change K.ksb.val + 13568 + c.val * 4288 ≤ b.val at hb1
    change b.val < K.ksb.val + 13568 + c.val * 4288 + 4288 at hb2
    change v.val + 32768 ≤ K.ksb.val + 13568 + c.val * 4288 ∨
      K.ksb.val + 13568 + c.val * 4288 + 4288 ≤ v.val at hn
    omega
  have h2 : ¬ ∃ p ∈ K.toKLayout.slots, InW p 32 b := fun ⟨p, hp, hb⟩ => hsl p hp b hb hv
  have h3 : ¬ ∃ t, K.toKLayout.heap t = some .tcb ∧ InW t (2 ^ 12) b :=
    fun ⟨t, ht, hb⟩ => noVcpu_of_kind hH hV ht (by simp) hb hv
  have h4 : ¬ ∃ p, K.toKLayout.heap p = some .ntfn ∧ InW p (2 ^ 6) b :=
    fun ⟨p, hp, hb⟩ => noVcpu_of_kind hH hV hp (by simp) hb hv
  have h5 : ¬ ∃ p, (K.toKLayout.heap p = some .ep ∧ InW p (2 ^ 4) b) ∨
      (K.toKLayout.heap p = some .reply ∧ InW p (2 ^ 5) b) := by
    rintro ⟨p, ⟨hp, hb⟩ | ⟨hp, hb⟩⟩
    · exact noVcpu_of_kind hH hV hp (by simp) hb hv
    · exact noVcpu_of_kind hH hV hp (by simp) hb hv
  have h6 : ¬ ∃ p z, K.toKLayout.heap p = some (.sc z) ∧ InW p (2 ^ z) b :=
    fun ⟨p, z, hp, hb⟩ => noVcpu_of_kind hH hV hp (by simp) hb hv
  unfold region
  rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_neg h6]

/-- Two VCPUs of the layout sharing a word are one (`RegionOKV.disj`). -/
theorem vcpu_disj (hH : HeapOK K.heap) (hV : VcpuHeap K) {v w b : U64} (hv : InVcpu K v b)
    (hw : InVcpu K w b) : v = w := by
  by_contra hne
  have hd := hH.disj v _ w _ (hV v hv.1) (hV w hw.1) hne
  have e15 : (HKind.other 15).bits = 15 := rfl
  rw [e15, two15] at hd
  obtain ⟨-, a1, a2⟩ := hv
  obtain ⟨-, b1, b2⟩ := hw
  omega

/-- A VCPU's `TCB` word does not wrap (`RegionOKV.tcbw`). -/
theorem vcpu_tcbw (hH : HeapOK K.heap) (hV : VcpuHeap K) {v : U64} (hv : v ∈ K.vcpus) :
    (fld v oVTCB).val = v.val + 20480 := by
  have hf := hH.fits v _ (hV v hv)
  have e15 : (HKind.other 15).bits = 15 := rfl
  rw [e15, two15] at hf
  unfold fld oVTCB
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  omega

/-- **`RegionOKV` from `RegionOK`, P1's placement, `VcpuHeap` and the slots' apartness.** -/
theorem regionOKV_of (hK : RegionOK K.toKLayout) (hL : LayP K.toKLayout) (hV : VcpuHeap K)
    (hsl : ∀ p ∈ K.slots, ∀ b, InW p 32 b → ¬ ∃ v, InVcpu K v b) : RegionOKV K :=
  ⟨hK, fun _ _ h => region_vcpu_none hL hV hsl h, fun _ _ _ => vcpu_disj hL.heap hV,
    fun _ hv => vcpu_tcbw hL.heap hV hv⟩

/-- **`regionOKV_of_JAtZ`** (module docstring, item 1): at a bundle state of `K.toKLayout`, `RegionOK` of it,
`VcpuHeap` [J] and `VcpuSpec` [J] give `RegionOKV K`. -/
theorem regionOKV_of_JAtZ {s : S} (hK : RegionOK K.toKLayout) (hJ : SlJAt (L := L) K.toKLayout s)
    (hV : VcpuHeap K) (hS : VcpuSpec L K) : RegionOKV K := by
  have hL : LayP K.toKLayout := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := hJ
    exact B.layP
  exact regionOKV_of hK hL hV fun p hp b hb => slot_noVcpu hJ hS hV hp hb

/-- **`RegionOKV` of a layout without VCPUs** (P3 scope) from `RegionOK` alone. -/
theorem regionOKV_of_empty (hK : RegionOK K.toKLayout) (he : K.vcpus = ∅) : RegionOKV K :=
  have hn : ∀ v, v ∉ K.vcpus := fun v hv => by rw [he] at hv; exact hv
  ⟨hK, fun v _ h => (hn v h.1).elim, fun v _ _ h => (hn v h.1).elim, fun v hv => (hn v hv).elim⟩

/-- **The VCPU layout facts** [J] (VT-x layout cluster, with lvm's `hvK`): `VcpuHeap` and `VcpuSpec`. -/
def VcpuLay (L : LawfulStore st) (K : KLayoutV) : Prop := VcpuHeap K ∧ VcpuSpec L K

theorem vcpuLay_empty (he : K.vcpus = ∅) : VcpuLay L K :=
  ⟨fun _ hv => by rw [he] at hv; exact hv.elim, fun _ _ _ _ _ _ _ _ _ _ _ _ _ hv => by rw [he] at hv; exact hv.elim⟩

end regv

/-! ## 2. The glue premises -/

/-- **The exit ghost with rule 7** [P] (Rust glue: fl4-sync's gate release after a serial entry; module docstring):
the ghost maps a serial step installs are `ownV K`'s (`SerExit.ExitGhost`'s map part with `own := ownV K`). -/
structure ExitGhostV (K : KLayoutV) (c : Cfg U64 U64 U64 U64) : Prop where
  own : c.own = ownV K
  cls : c.cls = OwnMap.cls K.toKLayout
  ko : c.ko = OwnMap.ko K.toKLayout c.mem

theorem ExitGhostV.maps {K : KLayoutV} {c : Cfg U64 U64 U64 U64} (h : ExitGhostV K c) : MapsV K c :=
  ⟨h.own, h.cls, h.ko⟩

section glue
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **The glue's entry correspondence** [P] (Rust glue: the entry asm and fl4-sync's `local_*`; module docstring):
the program `q` core `c` starts is `P`'s body from a store state `σ` of core `c` holding exactly `hs`, agreeing with
the model memory `μ` off user words, with the entry facts `Ent σ` (which name `σ` a state of P3's chain where the
path's `Pre` uses the bundle). `StartAt` with `Pre` replaced by `Ent`. -/
def GlueAt (P : LocalPath own cls ko User) (Ent : P.S → Prop) (c : U64) (hs : U64 → Prop) (μ : U64 → U64)
    (q : SP) : Prop :=
  ∃ (σ : P.S) (a : P.A), Ent σ ∧ P.L.cpu σ = c ∧ P.Locks σ = hs ∧
    (∀ x, Aligned x → ¬ User x → P.L.mem σ x = μ x) ∧ q = P.body σ a

theorem GlueAt.startAt {P : LocalPath own cls ko User} {Ent : P.S → Prop} {c : U64} {hs : U64 → Prop}
    {μ : U64 → U64} {q : SP} (h : GlueAt P Ent c hs μ q)
    (hP : ∀ σ, Ent σ → (∀ x, Aligned x → ¬ User x → P.L.mem σ x = μ x) → P.Pre σ) : StartAt P c hs μ q := by
  obtain ⟨σ, a, he, hc, hl, hμ, rfl⟩ := h
  exact ⟨σ, a, hP σ he hμ, hc, hl, hμ, rfl⟩

end glue

/-! ## 3. Slots at a given record -/

section slots
variable {ι : Type}

/-- A route-U slot's lifted path at a record. -/
def SlotU.liftAt (X : SlotU ι) (i : ι) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K)
    (h : X.Prem i K m) : LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  LocalPath.liftV hK (LocalPath.atV hK (X.path i K m hK hU h) (X.W i K m hK hU h))
    (noVcpuRd_atV hK _ (X.W i K m hK hU h))

/-- A route-C slot's lifted path at a record. -/
def SlotC.liftAt (X : SlotC ι) (i : ι) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K)
    (h : X.Prem i K m) : LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  LocalPath.cutLiftV hK hU (fun x ⟨_, hv, _⟩ => ko_vcpu hK hv m) (X.path i K m hK hU h) (X.Av i K m hK hU h)

theorem liftV_atV_congr {K : KLayoutV} {m : U64 → U64} (hK : RegionOKV K)
    {P P' : LocalPath (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user)}
    (e : P = P') (W : NoVcpuRW K P) (W' : NoVcpuRW K P') :
    LocalPath.liftV hK (LocalPath.atV hK P W) (noVcpuRd_atV hK P W) =
      LocalPath.liftV hK (LocalPath.atV hK P' W') (noVcpuRd_atV hK P' W') := by
  subst e; rfl

theorem cutLiftV_congr {K : KLayoutV} {m : U64 → U64} (hK : RegionOKV K) (hU : UserOKV K) (hko)
    {P P' : LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user)}
    (e : P = P') (W : AvoidV K P) (W' : AvoidV K P') :
    LocalPath.cutLiftV hK hU hko P W = LocalPath.cutLiftV hK hU hko P' W' := by
  subst e; rfl

theorem SlotU.lift_eq (D : Dflt) (X : SlotU ι) {i : ι} {K : KLayoutV} {m : U64 → U64} {hK : RegionOKV K}
    {hU : UserOKV K} (h : X.Prem i K m) : X.lift D i K m hK hU = X.liftAt i K m hK hU h :=
  liftV_atV_congr hK (X.fam_pos D h) _ _

theorem SlotC.lift_eq (D : Dflt) (X : SlotC ι) {i : ι} {K : KLayoutV} {m : U64 → U64} {hK : RegionOKV K}
    {hU : UserOKV K} (h : X.Prem i K m) : X.lift D i K m hK hU = X.liftAt i K m hK hU h :=
  cutLiftV_congr hK hU _ (X.fam_pos D h) _ _

end slots

/-! ## 4. The per-path start fact of `fl4LocW2` -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **The vexit path's entry facts beside the bundle** (`vxPre_ofJ`'s premises but `SlJAt`, with `VcpuHeap` in place
of `VFacts`). -/
structure VxEntJ (i : VxArg S) (K : KLayoutV) (m : U64 → U64) (s : S) : Prop where
  /-- [J] P1's invariant. -/
  inv : BXI st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s
  /-- [J] -/
  lay : StLay K.toKLayout st i.T i.Scs i.Z s
  /-- [J] -/
  ntw : ∀ p ∈ i.Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p
  /-- [J] -/
  cs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
    region K.toKLayout (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ OwnMap.TcbSlot K.toKLayout p ∧
      (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16
  /-- [J] -/
  aff : ∀ t ∈ i.T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t)
  /-- [J] -/
  curAff : L.mem s (affA (L.curW s)) = L.cpu s
  /-- [J] -/
  cscCore : L.mem s (scCoreA (L.cscW s)) = L.cpu s
  /-- [P] -/
  vlk : i.v ≠ 0#u64 → i.lk s i.v
  /-- [J] -/
  usr : ∀ x, x ∈ K.user → Aligned x → UsrW st i.T i.Cs i.H i.Sg i.Scs i.Z s x
  /-- [P] -/
  buf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK {x | x ∈ K.user ∧ Aligned x} b ⦄
  /-- [J] -/
  aff0 : m (fld (L.curW s) OwnMap.oAFFINITY) = L.mem s (affA (L.curW s))
  /-- [J] (VT-x layout cluster) -/
  vh : VcpuHeap K
  /-- P1's sets convention (the glue's choice of the index). -/
  hKH : K.heap = i.H
  hTs : i.T = i.H.tcbs
  hΩ : i.Ω = i.H.omega
  hSg : i.Sg = i.H.frame
  hScs : ∀ c ∈ i.Scs, i.H c = some (.sc (i.Z c))
  hNt : ∀ q ∈ i.Nt, i.H q = some .ntfn
  /-- [J] (VT-x layout cluster; vacuous at `K.vcpus = ∅` with `v = 0`) -/
  hvK : i.v ≠ 0#u64 → i.v ∈ K.vcpus

/-- **The vtimer path's entry facts beside the bundle** (`vtPre_ofJ`'s premises but `SlJAt`). -/
structure VtEntJ (i : VtArg S) (K : KLayoutV) (s : S) : Prop where
  /-- [J] -/
  inv : BXI st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s
  /-- [J] -/
  lay : StLay K.toKLayout st i.T i.Scs i.Z s
  /-- [J] -/
  ntw : ∀ p ∈ i.Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p
  /-- [J] -/
  cs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
    region K.toKLayout (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ OwnMap.TcbSlot K.toKLayout p ∧
      (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16
  /-- [J] -/
  aff : ∀ t ∈ i.T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t)
  /-- [J] -/
  curAff : L.mem s (affA (L.curW s)) = L.cpu s
  /-- [J] -/
  cscCore : L.mem s (scCoreA (L.cscW s)) = L.cpu s
  /-- [P] -/
  vlk : vOf st s ≠ 0#u64 → i.lk s (vOf st s)
  /-- [J] -/
  vf : VFacts L K
  /-- P1's sets convention. -/
  hKH : K.heap = i.H
  hTs : i.T = i.H.tcbs
  hΩ : i.Ω = i.H.omega
  hScs : ∀ c ∈ i.Scs, i.H c = some (.sc (i.Z c))
  hNt : ∀ q ∈ i.Nt, i.H q = some .ntfn
  /-- [J] (VT-x layout cluster) -/
  hvK : vOf st s ≠ 0#u64 → vOf st s ∈ K.vcpus
  /-- [J] -/
  hAs : AsidOff (L := L) i.Ω i.Sg s

theorem VxEntJ.pre {i : VxArg S} {K : KLayoutV} {m : U64 → U64} {s : S} (h : VxEntJ st i K m s)
    (hJ : SlJAt (L := L) K.toKLayout s) : VxPre st i K m s :=
  ⟨vexitEnt_of h.inv h.lay h.ntw h.cs h.aff h.curAff h.cscCore h.vlk hJ h.vh h.hKH h.hTs h.hΩ h.hScs h.hNt h.hvK,
    vexitPEnt_of h.inv h.usr h.buf h.aff0 hJ h.vh h.hKH h.hTs h.hΩ h.hSg h.hScs h.hvK⟩

theorem VtEntJ.pre {i : VtArg S} {K : KLayoutV} {s : S} (h : VtEntJ st i K s)
    (hJ : SlJAt (L := L) K.toKLayout s) : VtPre st i K s :=
  vtPre_ofJ st h.inv h.lay h.ntw h.cs h.aff h.curAff h.cscCore h.vlk hJ h.vf h.hKH h.hTs h.hΩ h.hScs h.hNt h.hvK
    h.hAs

variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- The index type of `fl4LocW2`. -/
abbrev Fl4IxW := Fl4Ix (VmFArg S) (VmRArg S) (IoArg S) (StArg S) (IrqArg S) (SlArg S) (VxArg S ⊕ VtArg S)

end start

/-! ## 5. Executions with the glue premises -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The serial exit's ghost choice** [P] (module docstring): the layout `K` (its `KLayout` part) and the chain `Ch`
are the ones `chainC` chooses at some P3 exit state `σe` (`JReachU17`). -/
def SerExitW (P : LocPlat st arI AR MR) (K : KLayoutV) (Ch : S → Prop) : Prop :=
  ∃ (σe : S) (a3 : A3) (τ : Fl4Spec.State Unit) (hJ : Fl4Proofs.P3.SInvR.G5.JReachU17 (L := L) arI AR MR σe a3 τ),
    chainC P hJ = (K.toKLayout, Ch)

theorem SerExitW.chainOf {P : LocPlat st arI AR MR} {K : KLayoutV} {Ch : S → Prop} (h : SerExitW P K Ch) :
    ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch := by
  obtain ⟨σe, a3, τ, hJ, e⟩ := h
  have hs := chainC_spec P hJ
  rw [e] at hs
  exact ⟨σe, hs⟩

/-- Clause 7 and the layout facts on the chosen chain. -/
theorem SerExitW.lay {P : LocPlat st arI AR MR} {K : KLayoutV} {Ch : S → Prop} (h : SerExitW P K Ch) :
    ∃ σe, ChainLay (L := L) K.toKLayout Ch ∧ Ch σe := by
  obtain ⟨σe, Z, H, Cx, nc, -, -, -, hC, hσ⟩ := h.chainOf
  exact ⟨σe, hC, hσ⟩

/-- **`Fl4StepV.ser`'s conclusion from the glue premises** (`regionOKV_of_JAtZ` at the exit). -/
theorem serExitW_ok {P : LocPlat st arI AR MR} {K : KLayoutV} {Ch : S → Prop} (h : SerExitW P K Ch)
    (hV : VcpuLay L K) : RegionOKV K ∧ UserOKV K := by
  obtain ⟨σe, hC, hσ⟩ := h.lay
  exact ⟨regionOKV_of_JAtZ hC.hK (hC.bun σe hσ) hV.1 hV.2, ⟨hC.hU⟩⟩

variable {ι : Type}

/-- **A step of FL4 with the glue premises named** (module docstring, item 3). `SF Ch K m hK hU c hs q i`: the
glue starts `q` as path `i` (per family; `StartW2` for `fl4LocW2`). -/
structure Fl4StepW (LP : PathsV ι)
    (SF : (S → Prop) → ∀ K : KLayoutV, (U64 → U64) → RegionOKV K → UserOKV K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutV) (Ch : S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutV) (Ch' : S → Prop) : Prop where
  /-- [P] an armed program is pure glue (as `Fl4StepV.arm`). -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start: the start fact (`GlueAt` and the path's record / entry facts) of some path. -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKV K) (hU : UserOKV K),
    ∃ i, SF Ch K s.mem hK hU c (fun l => s.lk l = some c) k i
  /-- [P] the serial exit's ghost choice. -/
  serX : SerStep s c → SerExitW P K' Ch'
  /-- [J] the new layout's VCPU facts (vacuous at `K'.vcpus = ∅`). -/
  serV : SerStep s c → VcpuLay L K'
  /-- [P] the exit ghost with rule 7. -/
  serG : SerStep s c → ExitGhostV K' s'
  /-- Layout and chain change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **An execution of FL4 with the glue premises named**: `ExecV` with `Fl4StepW` steps and a ghost chain. -/
inductive ExecW (LP : PathsV ι)
    (SF : (S → Prop) → ∀ K : KLayoutV, (U64 → U64) → RegionOKV K → UserOKV K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutV) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutV → (S → Prop) → Prop
  | refl : ExecW LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutV} {Ch Ch' : S → Prop} {c : U64} :
      ExecW LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepW LP SF P s K Ch c s' K' Ch' →
      ExecW LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutV} {Ch : S → Prop} {v a x : U64} :
      ExecW LP SF P s0 K0 Ch0 s K Ch → HwStepV K s v a x → ExecW LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

/-- **An `ExecW` is an `ExecV`** (module docstring, item 3): `Fl4StepV.ser` from `serExitW_ok` and the exit ghost,
`Fl4StepV.start` from the family's `SF → StartAt` at clause 7 of the current chain. -/
theorem execV_of_W {LP : PathsV ι}
    {SF : (S → Prop) → ∀ K : KLayoutV, (U64 → U64) → RegionOKV K → UserOKV K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) c hs q i,
      (∀ σ, Ch σ → SlJAt (L := L) K.toKLayout σ) → SF Ch K m hK hU c hs q i → StartAt (LP i K m hK hU) c hs m q)
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV} {Ch0 Ch : S → Prop}
    (hB : SerExitW P K0 Ch0) (h : ExecW LP SF P s0 K0 Ch0 s K Ch) :
    ExecV LP s0 K0 s K ∧ SerExitW P K Ch := by
  induction h with
  | refl => exact ⟨.refl, hB⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hX⟩ := ih
    obtain ⟨σe, hC, -⟩ := hX.lay
    refine ⟨.step hE hS ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hn => (g.keep hn).1⟩, ?_⟩
    · obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
      exact ⟨i, hSF _ _ _ _ _ _ _ _ i hC.bun hi⟩
    · have hok := serExitW_ok (g.serX hs) (g.serV hs)
      exact ⟨hok.1, hok.2, (g.serG hs).maps⟩
    · by_cases hs : SerStep s1 c1
      · exact g.serX hs
      · obtain ⟨e1, e2⟩ := g.keep hs
        rw [e1, e2]; exact hX
  | hw _ hH ih => exact ⟨.hw ih.1 hH, ih.2⟩

end exec

/-! ## 6. The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EV
