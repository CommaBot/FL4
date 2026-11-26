/-
# P2 (line mmuAD, gen 13): **VX11 under page-walker A/D writes** — `serializable_fl4_localVX11AD`

vmscope's `serializable_fl4_localVX11` (P2/E2EPVX11.lean) runs every U1 slot in native and VM epochs (`ExecVX4`),
with no MMU A/D writes. Here `ExecVX4b` adds gen 3's `mmu` step (the host page walker sets A / D in a present paging
word of the epoch, [P] `MmuAD`, P2/MmuADWalk.lean) with the epoch memory as an index, as `ExecU3b` does for U3.

* `EpochJV`: gen 3's `EpochJ` without `vcpus = ∅` (the convention `K.ptes = ptesR K E` holds at every serial exit
  of `ExecVX4`, native or VM: `Fl4StepVX4.ser`); `epochJV_ser` / `_keep` / `_mmu`, `EpochJV.toJ`.
* **`execVX4b_aRunR`**: an `ExecVX4b` execution is a `SerialADR.ARunR ADEq NotPresent` one at `PWE K E`, given the
  start facts (`hSF`, as VX11G's, with the native epoch's `NatEp` rebuilt from `EpochJV` by `epoch_start`) and, at
  every start, `InsA` of the started body (`hIns`). Hence (`serializable_VX4b_of`) every quiescent state is serial:
  `RunAll s.log s0.mem s.mem` — no deferral is needed because **no slot of VX11's family stores a present paging
  entry** (W11, delPte, CNodeDelete, Copy / Mint natively; VM exit, VM timer, I/O port, st, IRQ, sl, CNodeDelete,
  Copy / Mint, delPte, VM fault, VM ReplyRecv in VM epochs: the PTE stores are delPte's / `unmap_page`'s `0`; no EPT
  map slot is in the family).
* `vx11_startAt`: VX11G's start case split (copied), for `hSF`.
* **`serializable_fl4_localVX11AD`**: VX11's premises over `ExecVX4b`, plus [P] `MmuAD` (in the `mmu` step) and the
  named premise `hVm : VmInsAD` below. The native slots' `hIns` shares are gen 5 / 7's (`insA_w11`, `insA_delR`,
  `insA_invR`, `insA_cm`: a native start has `vcpus = ∅`, so `EpochJV.toJ`).

## The EPT walker
In a VM epoch a guest's EPT walk could set EPT A/D bits only if the EPTP enables them (bit 6). FL4's EPTP is
`physical(root) | 6 | (3 << 3)` (fl4-arch-x86_64 `vm.rs` l. 1002): write-back, 4-level, **bit 6 clear**, so the EPT
walker writes no EPT entry (Intel SDM 3C §29.3.5). The host walker (other cores running native threads) is `MmuAD`'s.

Named premises of `serializable_fl4_localVX11AD` beyond VX11's and [P] `MmuAD`:
* [W] `VmInsAD` (11 fields, one per VM-epoch slot of VX11): a body that slot starts in a VM epoch is `InsA` at the
  epoch's paging words. Gen 5 / 7 prove these for the native slots only: their device (`KU K E`, `regionOKP_ku` /
  `userOKP_ku`) needs `vcpus = ∅`, and the VM slots' avoidance proofs (`AvoidV`) are at `K.ptes`, not at every paging
  word. Expected to hold (each VM slot's reads of paging words are `unmap_page`'s masked walk — CNodeDelete, delPte —
  or none; stores of paging words are `0`), but not proved here.

No existing statement changed.
-/
import Fl4Proofs.P2.E2EPVX11
import Fl4Proofs.P2.E2EPU3f
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg HwWr allowed_of_sinv
  InsA ARunR aRunR_inv serializable_safeR)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv adEq_trans adOr_adEq)

noncomputable section
open Classical

section epoch
variable {K : KLayoutP} {E : U64 → U64}

/-- **The epoch invariant with A/D writes, native or VM** (gen 3's `EpochJ` without `nv`). -/
structure EpochJV (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) : Prop where
  conv : K.ptes = ptesR K E
  pw : ∀ x, GateW K x → PWE K E x → ADEq (s.mem x) (E x)
  eq : ∀ x, GateW K x → ¬ PWE K E x → s.mem x = E x

theorem EpochJV.toJ {s : Cfg U64 U64 U64 U64} (J : EpochJV K E s) (nv : K.vcpus = ∅) : EpochJ K E s :=
  ⟨nv, J.conv, J.pw, J.eq⟩

theorem epochJV_ser {s : Cfg U64 U64 U64 U64} (hc : K.ptes = ptesR K s.mem) : EpochJV K s.mem s :=
  ⟨hc, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem epochJV_keep {s s' : Cfg U64 U64 U64 U64} (J : EpochJV K E s) (hk : ∀ x, GateW K x → s'.mem x = s.mem x) :
    EpochJV K E s' :=
  ⟨J.conv, fun x hg hp => by rw [hk x hg]; exact J.pw x hg hp,
    fun x hg hp => by rw [hk x hg]; exact J.eq x hg hp⟩

theorem epochJV_mmu {s : Cfg U64 U64 U64 U64} {a y : U64} (J : EpochJV K E s) (h : MmuAD (PWE K E) s.mem a y) :
    EpochJV K E (hwCfg s a y) := by
  refine ⟨J.conv, fun x hg hp => ?_, fun x hg hp => ?_⟩
  · show ADEq (Function.update s.mem a y x) (E x)
    by_cases hx : x = a
    · subst hx; rw [Function.update_self]; exact adEq_trans (adOr_adEq h.ad) (J.pw x hg hp)
    · rw [Function.update_of_ne hx]; exact J.pw x hg hp
  · show Function.update s.mem a y x = E x
    have hx : x ≠ a := fun e => hp (e ▸ h.pw)
    rw [Function.update_of_ne hx]; exact J.eq x hg hp

end epoch

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **An `ExecVX4` execution with the host walker's A/D writes to the epoch's paging words**; the last index is the
epoch memory (the memory at the last serial exit). -/
inductive ExecVX4b (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → (U64 → U64) → Prop
  | refl : ExecVX4b LP SF P s0 K0 Ch0 s0 K0 Ch0 s0.mem
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} {E : U64 → U64} :
      ExecVX4b LP SF P s0 K0 Ch0 s K Ch E → Step s c s' → Fl4StepVX4 LP SF P s K Ch c s' K' Ch' →
      ExecVX4b LP SF P s0 K0 Ch0 s' K' Ch' (if SerStep s c then s'.mem else E)
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {E : U64 → U64} {v a x : U64} :
      ExecVX4b LP SF P s0 K0 Ch0 s K Ch E → HwStepP K s v a x → ExecVX4b LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch E
  | mmu {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {E : U64 → U64} {a x : U64} :
      ExecVX4b LP SF P s0 K0 Ch0 s K Ch E → MmuAD (PWE K E) s.mem a x →
      ExecVX4b LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch E

/-- **An `ExecVX4b` execution is an `ARunR` one at the epoch's paging words** (module docstring). -/
theorem execVX4b_aRunR {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (P : LocPlat st arI AR MR)
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEp P K Ch s) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (Ch : S → Prop) (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K)
      (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : ι),
      (K.vcpus = ∅ → SerExitW P K.toKLayoutV Ch) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) → EpochJV K E s →
      MapsP K s → SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q →
      InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecVX4b LP SF P s0 K0 Ch0 s K Ch E) :
    ARunR ADEq NotPresent s0 s (PWE K E) ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s ∧
      (K.vcpus = ∅ → SerExitW P K.toKLayoutV Ch) ∧ (K.vcpus ≠ ∅ → VtxBundle4 st L K) ∧ EpochJV K E s := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  induction h with
  | refl => exact ⟨.refl _, hK0, hU0, hM0, fun _ => hB, fun hn => (hn hc0.1).elim, epochJV_ser hc0.2⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 E1 _ hS g ih =>
    obtain ⟨hR, hK, hU, hM, hX, hV, J⟩ := ih
    obtain ⟨⟨H, I⟩, -, hSI, -⟩ := aRunR_inv adEq_equiv h0 hA0 hR
    have hN : K1.vcpus = ∅ → NatEp P K1 Ch1 s1 := fun nv => ⟨hX nv, epoch_start (J.toJ nv)⟩
    have hst : ∀ p0 k W, s1.ph c1 = .loc p0 (.start k) W →
        ∃ i, SF Ch1 K1 s1.mem hK hU c1 (fun l => s1.lk l = some c1) k i ∧
          StartAt (LP i K1 s1.mem hK hU) c1 (fun l => s1.lk l = some c1) s1.mem k := by
      intro p0 k W hph
      obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
      exact ⟨i, hi, hSF _ _ s1 _ _ _ _ _ i hN hV hi⟩
    have hok : Fl4Proofs.P2.Serial.SafeStep s1 c1 s1' := by
      refine ⟨g.arm, fun p0 k W hph => ?_⟩
      obtain ⟨i, -, hP⟩ := hst p0 k W hph
      rw [hM.own, hM.cls, hM.ko]
      exact (LP i K1 s1.mem hK hU).safe (moveHeldP hK) (ownDepP hK hU) hP
    by_cases hs : SerStep s1 c1
    · rw [if_pos hs]
      have hnl := I.inv.clo hs.1
      have hR' := ARunR.regate (PWE K1' s1'.mem) hR hs.1
      have hst' : ARunR ADEq NotPresent s0 s1' (PWE K1' s1'.mem) :=
        .step hR' hS hok (fun p0 k W hph => absurd (by rw [hph]; trivial) (hnl c1))
      rcases g.ser hs with ⟨hXs, nv, hc⟩ | ⟨hne, hc, hb⟩
      · have hK' := okP_R hXs ⟨nv, hc⟩
        exact ⟨hst', hK'.1, hK'.2, g.serG hs, fun _ => hXs, fun hn => (hn nv).elim, epochJV_ser hc⟩
      · have hK' := hb.b.okP hc
        exact ⟨hst', hK'.1, hK'.2, g.serG hs, fun nv => (hne nv).elim, fun _ => hb, epochJV_ser hc⟩
    · rw [if_neg hs]
      obtain ⟨eK, eC⟩ := g.keep hs
      subst eK eC
      have hal := allowed_of_sinv hSI c1
      refine ⟨.step hR hS hok (fun p0 k W hph => ?_), hK, hU, maps_stepP hK hM hal hS hs, hX, hV,
        epochJV_keep J (fun x hx => step_gate_keep hM hal hS hs hx)⟩
      obtain ⟨i, hi, hP⟩ := hst p0 k W hph
      exact hIns _ _ _ _ hK hU _ _ _ i hX hV J hM hi hP
  | hw _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, hV, J⟩ := ih
    exact ⟨.hw hR (hH.hwWr hK hM), hK, hU, maps_hwP hK hM hH, hX, hV,
      epochJV_keep J (fun x hx => hw_gate_keep hK hM hH hx)⟩
  | mmu _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, hV, J⟩ := ih
    exact ⟨.ad hR (adWr_pwe hK hM hH), hK, hU, maps_pwe hK hM hH, hX, hV, epochJV_mmu J hH⟩

/-- **Every quiescent `ExecVX4b` state is serial**, given `hSF` and `hIns`. -/
theorem serializable_VX4b_of {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (P : LocPlat st arI AR MR)
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEp P K Ch s) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (Ch : S → Prop) (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K)
      (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : ι),
      (K.vcpus = ∅ → SerExitW P K.toKLayoutV Ch) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) → EpochJV K E s →
      MapsP K s → SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q →
      InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecVX4b LP SF P s0 K0 Ch0 s K Ch E) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_safeR adEq_equiv h0 hA0 (execVX4b_aRunR P hSF hIns h0 hA0 hB hc0 hM0 h).1 hq

end exec

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- VX11's family (`serializable_fl4_localVX11`'s). -/
abbrev famVX11 :=
  PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum
    (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (fl4LocW11JA st ar hA hm hSt a0)
      (PathsP.sum (PathsP.sum (delPteSlot st ar hA hm) (invSlotU st ar hA hm)) (cmSlotU st ar hA hm)))
    (vxSlotPV st ar hA hm)) (vtSlotPV st ar hA hm)) (ioSlotPX st ar hA hm)) (stSlotPX st ar hA hm))
    (irqSlotPX st ar hA hm)) (slSlotPX st ar hA hm hSt a0)) (invSlotVX st ar hA hm)) (cmSlotVX st ar hA hm))
    (delPteSlotVX st ar hA hm)) (vmFSlotPY st ar hA hm)) (vmRSlotPY st ar hA hm)

/-- VX11's start facts. -/
abbrev StartVX11U :=
  StartVX11 st ar hA hm hSt a0 (StartU1 st ar hA hm hSt a0 arI AR MR (StartInvU2 st ar hA hm))

/-- One VM-epoch slot family's share of `hIns`: a body it starts in a VM epoch is `InsA` at the epoch's paging
words. -/
def InsAV {ιv : Type} (LPv : PathsP ιv) : Prop :=
  ∀ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) (j : ιv), K.vcpus ≠ ∅ → VtxBundle4 st L K → EpochJV K E s → MapsP K s →
    StartAt (LPv j K s.mem hK hU) c hs s.mem q → InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q

/-- **[W] The VM-epoch slots under A/D writes** (named premise; module docstring): each VM-epoch slot of VX11 is
`InsA` at the epoch's paging words. Rust: `syscall.rs` / `fastpath_vm.rs` / `vcpu.rs` (VM exit, VM timer, I/O port,
st, IRQ, sl, VM fault, VM ReplyRecv: no paging-word access), `cnode.rs` / `cdt.rs` → `vspace.rs` `unmap_page`
(CNodeDelete, delPte: masked walk, store `0`), Copy / Mint (no table walk). -/
structure VmInsAD : Prop where
  /-- [W] VM exit. -/
  vx : InsAV st (vxSlotPV st ar hA hm)
  /-- [W] VM timer. -/
  vt : InsAV st (vtSlotPV st ar hA hm)
  /-- [W] I/O port. -/
  io : InsAV st (ioSlotPX st ar hA hm)
  /-- [W] the st slot. -/
  stS : InsAV st (stSlotPX st ar hA hm)
  /-- [W] IRQ. -/
  irq : InsAV st (irqSlotPX st ar hA hm)
  /-- [W] the sl slot. -/
  sl : InsAV st (slSlotPX st ar hA hm hSt a0)
  /-- [W] CNodeDelete in VM epochs. -/
  inv : InsAV st (invSlotVX st ar hA hm)
  /-- [W] Copy / Mint in VM epochs. -/
  cm : InsAV st (cmSlotVX st ar hA hm)
  /-- [W] delPte in VM epochs. -/
  del : InsAV st (delPteSlotVX st ar hA hm)
  /-- [W] VM fault. -/
  vmF : InsAV st (vmFSlotPY st ar hA hm)
  /-- [W] VM ReplyRecv. -/
  vmR : InsAV st (vmRSlotPY st ar hA hm)

/-- **VX11G's start case split** (copied from `serializable_fl4_localVX11G`, native family U1's). -/
theorem vx11_startAt (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) :
    ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEp P K Ch s) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      StartVX11U st ar hA hm hSt a0 (arI := arI) (AR := AR) (MR := MR) Ch K s.mem hK hU c hs q i →
      StartAt (famVX11 st ar hA hm hSt a0 i K s.mem hK hU) c hs s.mem q := by
  intro Ch K s hK hU c hs q i hN hV hsf
  rcases i with ((((((((((i | j) | j) | j) | j) | j) | j) | j) | j) | j) | j) | j
  · have hsf' : K.vcpus = ∅ ∧ StartU1 st ar hA hm hSt a0 arI AR MR (StartInvU2 st ar hA hm) Ch K s.mem hK hU c hs
        q i := hsf
    obtain ⟨nv, hsf'⟩ := hsf'
    obtain ⟨hX, hE⟩ := hN nv
    rcases i with i | ((j | j) | j)
    · exact startAt_U st ar hA hm hSt a0 P hIoa hX.chainOf hE hsf'
    · exact delPteStart_at st ar hA hm hX.chainOf hE hsf'
    · exact invStartU2_at st ar hA hm hX.chainOf hE hsf'
    · exact cmStartU2_at st ar hA hm hX.chainOf hE hsf'
  · have hsf' : VxStartV2 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact vxStartV_at st ar hA hm (vxStartV_of_V2 (hV (vxStartV2_ne hsf')).b hsf')
  · have hsf' : VtStartV4 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact vtStartV2_at (hV hsf'.1).b (vtStartV2_of_V4 (hV hsf'.1).b hsf')
  · have hsf' : IoStartX5 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact ioStartX_at (hV hsf'.1) (ioStartX_of_X5 (hV hsf'.1) hsf')
  · have hsf' : StStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact stStartX_at (hV hsf'.1) hsf'
  · have hsf' : IrqStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact irqStartX_at (hV hsf'.1) hsf'
  · have hsf' : SlStartX st ar hA hm hSt a0 K s.mem hK hU c hs q j := hsf
    exact slStartX_at (hV hsf'.1) hsf'
  · have hsf' : InvStartX9 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact invStartX_at (hV hsf'.1) (invStartX_of9 (hV hsf'.1) hsf')
  · have hsf' : CMStartX9 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact cmStartX_at (hV hsf'.1) (cmStartX_of9 (hV hsf'.1) hsf')
  · have hsf' : DelPteStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact delPteStartX_at (hV hsf'.1) hsf'
  · have hsf' : VmFStartY st ar hA hm K s.mem hK hU c hs q j := hsf
    exact vmFStartY_at (hV hsf'.1) hsf'
  · have hsf' : VmRStartY st ar hA hm K s.mem hK hU c hs q j := hsf
    exact vmRStartY_at (hV hsf'.1) hsf'

/-- **FL4 end to end with every U1 slot in native and VM epochs and the host walker's A/D writes** (module
docstring): VX11's premises (`P`, [P] `hIoa`, `h0`, `hA0`, `hB`, `hc0`, `hM0`, the execution, `hq`) over
`ExecVX4b`, [P] `MmuAD` (its `mmu` step), and [W] `hVm : VmInsAD`. -/
theorem serializable_fl4_localVX11AD (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (hVm : VmInsAD st ar hA hm hSt a0)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4b (famVX11 st ar hA hm hSt a0) (StartVX11U st ar hA hm hSt a0 (arI := arI) (AR := AR) (MR := MR))
      P s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  refine serializable_VX4b_of P (vx11_startAt st ar hA hm hSt a0 P hIoa) ?_ h0 hA0 hB hc0 hM0 h hq
  intro Ch K E s hK hU c hs q i hX hV J hM hsf hP
  rcases i with ((((((((((i | j) | j) | j) | j) | j) | j) | j) | j) | j) | j) | j
  · have hsf' : K.vcpus = ∅ ∧ StartU1 st ar hA hm hSt a0 arI AR MR (StartInvU2 st ar hA hm) Ch K s.mem hK hU c hs
        q i := hsf
    have nv := hsf'.1
    have J' := J.toJ nv
    have hb : ∃ σe, SlJAt (L := L) K.toKLayout σe := by
      obtain ⟨σe, hC'⟩ := (hX nv).chainOf
      have hσe : Ch σe := by
        obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
        exact h'
      exact ⟨σe, ChainOf.bun hC' σe hσe⟩
    rcases i with i | ((j | j) | j)
    · exact insA_w11 st ar hA hm hSt a0 i (hK := hK) (hU := hU) hb J' hM hP
    · exact insA_delR st ar hA hm j (hK := hK) (hU := hU) hb J' hM hP
    · exact insA_invR st ar hA hm j (hK := hK) (hU := hU) hb J' hM hP
    · exact insA_cm st ar hA hm j (hK := hK) (hU := hU) hb J' hM hP
  · have hsf' : VxStartV2 st ar hA hm K s.mem hK hU c hs q j := hsf
    have hne := vxStartV2_ne hsf'
    exact hVm.vx K E s hK hU c hs q j hne (hV hne) J hM hP
  · have hsf' : VtStartV4 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact hVm.vt K E s hK hU c hs q j hsf'.1 (hV hsf'.1) J hM hP
  · have hsf' : IoStartX5 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact hVm.io K E s hK hU c hs q j hsf'.1 (hV hsf'.1) J hM hP
  · have hsf' : StStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact hVm.stS K E s hK hU c hs q j hsf'.1 (hV hsf'.1) J hM hP
  · have hsf' : IrqStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact hVm.irq K E s hK hU c hs q j hsf'.1 (hV hsf'.1) J hM hP
  · have hsf' : SlStartX st ar hA hm hSt a0 K s.mem hK hU c hs q j := hsf
    exact hVm.sl K E s hK hU c hs q j hsf'.1 (hV hsf'.1) J hM hP
  · have hsf' : InvStartX9 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact hVm.inv K E s hK hU c hs q j hsf'.1 (hV hsf'.1) J hM hP
  · have hsf' : CMStartX9 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact hVm.cm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) J hM hP
  · have hsf' : DelPteStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact hVm.del K E s hK hU c hs q j hsf'.1 (hV hsf'.1) J hM hP
  · have hsf' : VmFStartY st ar hA hm K s.mem hK hU c hs q j := hsf
    exact hVm.vmF K E s hK hU c hs q j hsf'.1 (hV hsf'.1) J hM hP
  · have hsf' : VmRStartY st ar hA hm K s.mem hK hU c hs q j := hsf
    exact hVm.vmR K E s hK hU c hs q j hsf'.1 (hV hsf'.1) J hM hP

end top

end
end Fl4Proofs.P2.E2EP
