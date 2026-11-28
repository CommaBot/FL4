/-
# P2 (line mmuAD, gen 14): **the VM-epoch slots under A/D writes** — `serializable_fl4_localVX11AE`

Gen 13's `serializable_fl4_localVX11AD` (P2/E2EPVX11AD.lean) has the named premise [W] `VmInsAD`, one field per
VM-epoch slot of VX11. This module shows that `VmInsAD` **is false as stated** (counterexample below), states
the missing VM layout fact as an [S] record `VmPwe`, carried by a new execution relation `ExecVX4c`, and discharges
eight of the eleven fields under it.

## Counterexample to `VmInsAD.vx` (and why the native device needed `vcpus = ∅`)
`PWE K E` (P2/MmuADEpoch.lean) takes every upper-level entry a walk from a pool-named root reads in `E` (`UpW`)
that is region `.none`, not user, off the kernel-global block, and no ASID word. **VCPU words are region `.none`**
(`RegionOKV.none`), are not user (`UserObj`), and lie off the kernel-global block (`VcpuKsOff`). Nothing in
`InsAV`'s hypotheses (`RegionOKP K`, `UserOKP K`, `K.vcpus ≠ ∅`, `VtxBundle4`, `EpochJV`, `MapsP`, `StartAt`) relates
the *values* of the epoch's paging entries to the VCPU objects. Take a VM-epoch start of the VM-exit slot with
exiting VCPU `v`, bound notification `n` active (`!ntfn_quiet`), `v.PENDING = 0` (word `v + 0x5028`), and an epoch
memory `E` whose named root `r` has the L4 entry `E (peA r 0) = (v + 0x5000) ||| 1`. Then for a user VA with L4
index 0 and L3 index 5, `walk1 E r va = some (v + 0x5028)`, so `v + 0x5028 ∈ UpW`, and by the three facts above
`PWE K E (v + 0x5028)`. `handle_vcpu_exit_local` (fl4-core `localvm.rs` l. 387) reads `vcpu::get(s, v, PENDING)` and
declines when it is `0` (with `n` active), continues when it is `0x20`; `0x20` is `ADEq`-equivalent to `0`, so the
`rd` clause of `InsA (PWE K E) ADEq NotPresent …` fails at the start memory. Every hypothesis of `InsAV` is a
statement about layouts and gate words, none about where page-table entries point, so the field is unprovable
(and false for this instance). The same applies to any VM slot that reads or stores VCPU data (vt, vmF, vmR).
On real hardware the instance does not occur: paging objects and VCPU objects are distinct retyped objects
(fl4-core `arch/x86_64/objects.rs` `create_arch_object`), and an upper entry's address is written only by a map
invocation on a paging-object cap. That is the content of `VmPwe.nov` below.

## What is here
* **`VmPwe K E`** [S] (VM layout fact at a VM serial exit): `nov` — no paging word of the epoch lies in a VCPU;
  `tab` — the ASID-table words are the gate's (natively `RegionOKX.asidT` + `gateW_of_region`; in VM epochs no P3
  bundle gives the table's region). Rust: `layout.rs` `ASID_TABLE` (kernel-global block, no object there, no VCPU
  there by `VcpuKsOff`), `objects.rs` `create_arch_object`, `vspace.rs` map operations.
* **`ExecVX4c`**: `ExecVX4b` whose VM serial exits also give `VmPwe K' s'.mem`; **`execVX4c_aRunR`** (as
  `execVX4b_aRunR`, the invariant also carries `K.vcpus ≠ ∅ → VmPwe K E`), `serializable_VX4c_of`.
* The VM version of gen 5's enlarged layout: `regionOKP_kuV` (from `VmPwe.nov`, no `vcpus = ∅`), `ownV_pwe_gateV`,
  **`qPs_kuV`** (`QPs (KU K E)` at a VM start, from `EpochJV` and `VmPwe.tab`).
* Generic: **`kuV_noG`** / **`insA_kuV`** — for any `ownV` path `R` whose `QPs`-restriction avoids the PTE words at
  every layout (`AvoidP K (R.rJ K _)` and `AvoidP (KU K E) (R.rJ (KU K E) _)`), a start of its PTE-cut lift is `InsA`
  at `PWE K E`.
* **`insAW_vx`, `insAW_vt`, `insAW_io`, `insAW_st`, `insAW_irq`, `insAW_sl`, `insAW_vmF`, `insAW_vmR`**: the eight
  `rJ`-shaped VM slots, each one `insA_kuV` with the slot's existing avoidance lemma at `K` and at `KU K E`.
* **`serializable_fl4_localVX11AE`**: VX11's premises over `ExecVX4c` (so [S] `VmPwe` at VM serial exits), [P]
  `MmuAD`, and [W] **`VmInsAE`** with three fields only: CNodeDelete, Copy / Mint and delPte in VM epochs.

## Named premises of `serializable_fl4_localVX11AE` beyond VX11's and [P] `MmuAD`
* [S] `VmPwe K' s'.mem` at every VM serial exit (in `ExecVX4c`'s step; the counterexample shows it is needed).
* [W] `VmInsAE` (3 fields): `inv` (CNodeDelete: its stale-frame arm walks the upper levels, `unmap_page`'s masked
  walk, gen 7's `accIns_invR` at the VM layout), `cm` (Copy / Mint: its path `cmPathVX` is built at `K` with the
  entry fact `FCM st j K m`, not `rJ`-shaped, so `insA_kuV` does not apply as is), `del` (delPte: masked walk).

No existing statement changed (new file; root import list extended).

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `execVX4c_aRunR`,
`serializable_VX4c_of`, `serializable_fl4_localVX11AE`.
-/
import Fl4Proofs.P2.E2EPVX11AD
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

/-! ## 1. The VM layout fact and the VM version of the enlarged layout -/

section ku
variable {K : KLayoutP} {E : U64 → U64}

/-- **[S] The VM layout fact of an epoch** (module docstring): no paging word of the epoch lies in a VCPU, and the
ASID-table words are the gate's.

Justification (accepted by the line's coordinator, gen 14 review): page-table entries point only to page tables and
frames, never to VCPU objects, so this is a true layout invariant. Rust: fl4-core `arch/x86_64/objects.rs`
(`create_arch_object`: paging objects, ASID pools and `bits::VCPU` objects are retyped from distinct untyped ranges),
`arch/x86_64/vspace.rs` (an upper entry's address field is written only by a map invocation whose argument is a
paging-object cap; frames are mapped only as leaves), `layout.rs` (`ASID_TABLE` in the kernel-global block, where no
object and, by `VcpuKsOff`, no VCPU lies). Natively both halves follow from P3's bundle: `RegionOKX`
(`region_none_ptw`, `region_none_pool`, `RegionOKX.asidT`, P2/E2EPJEp2.lean, from the spec arch objects `PtRel` /
`VsRel.pool` and `SpecCover.arch`) with `vcpus = ∅`. In VM epochs it has the status of vmscope's other [S] layout facts
(`VtxBundle4`), pending the VT-x refinement. -/
structure VmPwe (K : KLayoutP) (E : U64 → U64) : Prop where
  /-- [S] No paging word of the epoch is a VCPU word (paging and VCPU objects are distinct retyped objects). -/
  nov : ∀ b, PWE K E b → ¬ ∃ v, InVcpu K.toKLayoutV v b
  /-- [S] The ASID-table words are the gate's (kernel-global block; natively `RegionOKX.asidT`). -/
  tab : ∀ hi : U64, hi.val < 2048 → GateW K (atAF K.ksb hi)

theorem regionOKP_kuV (hK : RegionOKP K) (hP : VmPwe K E) : RegionOKP (KU K E) :=
  ⟨hK.base, fun _ he => pwe_region hK he.1, fun e he => hP.nov e he.1⟩

/-- A paging word of the epoch is the gate's under `ownV` (`VmPwe.nov`). -/
theorem ownV_pwe_gateV (hK : RegionOKP K) (hP : VmPwe K E) {m : U64 → U64} {b : U64} (h : PWE K E b) :
    ownV K.toKLayoutV m b = .gate := by
  unfold ownV
  rw [dif_neg (hP.nov b h)]
  exact own_pwe_gate hK h

/-- **`QPs (KU K E)` at a start state of a VM epoch** (`qPs_ku` with `EpochJV` and `VmPwe.tab`). -/
theorem qPs_kuV {S : Type} {st : machine.Store S} [L : LawfulStore st] {s : Cfg U64 U64 U64 U64}
    (J : EpochJV K E s) (hP : VmPwe K E) {σ : S} (hq : QPs K st σ)
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = s.mem x) : QPs (KU K E) st σ := by
  have hnA : ∀ b, AsidW K.ksb E b → ¬ PWE K E b := fun b hb => pwe_asid J.conv hb
  have hm : ∀ hi : U64, hi.val < 2048 → L.mem σ (atAF K.ksb hi) = E (atAF K.ksb hi) := by
    intro hi hhi
    have ht : AsidW K.ksb E (atAF K.ksb hi) := Or.inl ⟨hi, hhi, rfl⟩
    rw [hμ _ (hq.al hi hhi) (fun hu => hq.uoff _ (Or.inl hu) hi hhi rfl)]
    exact J.eq _ (hP.tab hi hhi) (hnA _ ht)
  refine ⟨fun o ho hb => ?_, hq.ksb, ?_, hq.al, hq.uoff⟩
  · obtain ⟨hp, -⟩ := hb
    rcases hp with hp | h
    · exact hq.ks o ho hp
    · exact h.2.2.2.2 o ho rfl
  · intro hi hhi
    rw [hq.ksb]
    refine ⟨fun hb => hnA _ (Or.inl ⟨hi, hhi, rfl⟩) hb.1, fun lo hlo hne hb => ?_⟩
    rw [hm hi hhi] at hne hb
    exact hnA _ (Or.inr ⟨hi, hhi, hne, lo, hlo, rfl⟩) hb.1

end ku

/-! ## 2. Generic: a PTE-cut lift of an `rJ`-avoiding `ownV` path -/

section gen
variable {K : KLayoutP} {E : U64 → U64}

/-- **The runs of an `rJ`-avoiding path, at `QPs (KU K E)` states, touch no paging word of the epoch.** -/
theorem kuV_noG {m : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K) (hP : VmPwe K E)
    (R : LocalPath (ownV K.toKLayoutV) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user))
    (hAvK : AvoidP K (R.rJ K (fun b hb => Or.inl hb)))
    (hAvU : AvoidP (KU K E) (R.rJ (KU K E) (fun b hb => Or.inl hb)))
    (s1 s2 : R.S) (a : R.A)
    (hp : (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ hAvK).Pre s1)
    (hq : QPt (KU K E) R s1)
    (hAl : @Alt _ R.st R.L ((LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ hAvK).RS s1)
      (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) s1 s2) :
    Within R.st R.ar (fun b => ¬ PWE K E b) (fun b => b ∈ K.user ∨ ¬ PWE K E b) R.p s2 a := by
  obtain ⟨hp1, -⟩ := hp
  exact LocalPath.noPWE_of_avoid _ (fun _ _ h => ownV_pwe_gateV hK hP h) hAvU ⟨hp1, hq⟩ hAl
    (fun x hx hn => ⟨hx, fun hp' => hn (pte_ku hU hp')⟩) a

/-- **A start of the PTE-cut lift of an `rJ`-avoiding path in a VM epoch is `InsA` at the epoch's paging words.** -/
theorem insA_kuV {s : Cfg U64 U64 U64 U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop}
    {q : SP} (hP : VmPwe K E) (J : EpochJV K E s) (hM : MapsP K s)
    (R : LocalPath (ownV K.toKLayoutV) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) (· ∈ K.user))
    (hAvK : AvoidP K (R.rJ K (fun b hb => Or.inl hb)))
    (hAvU : AvoidP (KU K E) (R.rJ (KU K E) (fun b hb => Or.inl hb)))
    (h : StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ hAvK) c hs s.mem q) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q := by
  obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := h
  letI := R.L
  have hq : QPt (KU K E) R σ := qPs_kuV J hP hpre.2 (fun x hx hu => hμ x hx hu)
  have h' : StartAt ((LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ hAvK).restrQ
      (QPt (KU K E) (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ hAvK))
      (qPt_stab (KU K E) _ (fun b hb => Or.inl hb))) c hs s.mem
      ((LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ hAvK).body σ a) :=
    ⟨σ, a, ⟨hpre, hq⟩, hc, hl, hμ, rfl⟩
  rw [hM.own, hM.cls, hM.ko]
  refine LocalPath.insA _ (moveHeldP hK) (ownDepP hK hU) (pwe_own hK) ?_ h'
  intro s1 s2 a' hp1 hA'
  exact kuV_noG hK hU hP R hAvK hAvU s1 s2 a' hp1.1 hp1.2 hA'

end gen

/-! ## 3. `ExecVX4c`: VM serial exits give `VmPwe` -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **`ExecVX4b` whose VM serial exits give the [S] layout fact `VmPwe`** of the new epoch. -/
inductive ExecVX4c (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → (U64 → U64) → Prop
  | refl : ExecVX4c LP SF P s0 K0 Ch0 s0 K0 Ch0 s0.mem
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} {E : U64 → U64} :
      ExecVX4c LP SF P s0 K0 Ch0 s K Ch E → Step s c s' → Fl4StepVX4 LP SF P s K Ch c s' K' Ch' →
      /- [S] the VM layout fact at a VM serial exit -/
      (SerStep s c → K'.vcpus ≠ ∅ → VmPwe K' s'.mem) →
      ExecVX4c LP SF P s0 K0 Ch0 s' K' Ch' (if SerStep s c then s'.mem else E)
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {E : U64 → U64} {v a x : U64} :
      ExecVX4c LP SF P s0 K0 Ch0 s K Ch E → HwStepP K s v a x → ExecVX4c LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch E
  | mmu {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {E : U64 → U64} {a x : U64} :
      ExecVX4c LP SF P s0 K0 Ch0 s K Ch E → MmuAD (PWE K E) s.mem a x →
      ExecVX4c LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch E

end exec

/-! ## 4. The VM-epoch slots -/

section slots
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- One VM-epoch slot family's share of `hIns` given the [S] `VmPwe` (`InsAV` with `VmPwe K E`). -/
def InsAW {ιv : Type} (LPv : PathsP ιv) : Prop :=
  ∀ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) (j : ιv), K.vcpus ≠ ∅ → VtxBundle4 st L K → VmPwe K E → EpochJV K E s →
    MapsP K s → StartAt (LPv j K s.mem hK hU) c hs s.mem q →
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q

/-- **VM exit.** -/
theorem insAW_vx : InsAW st (vxSlotPV st ar hA hm) := by
  intro K E s hK hU c hs q j _ _ hP J hM h
  exact insA_kuV hP J hM _ (vx_avoidPV st ar hA hm j K s.mem hK hU)
    (vx_avoidPV st ar hA hm j (KU K E) s.mem (regionOKP_kuV hK hP) (userOKP_ku hU)) h

/-- **VM timer.** -/
theorem insAW_vt : InsAW st (vtSlotPV st ar hA hm) := by
  intro K E s hK hU c hs q j _ _ hP J hM h
  exact insA_kuV hP J hM _ (vt_avoidPV st ar hA hm j K s.mem hK hU)
    (vt_avoidPV st ar hA hm j (KU K E) s.mem (regionOKP_kuV hK hP) (userOKP_ku hU)) h

/-- **I/O port.** -/
theorem insAW_io : InsAW st (ioSlotPX st ar hA hm) := by
  intro K E s hK hU c hs q j _ _ hP J hM h
  exact insA_kuV hP J hM _ (io_avoidPX st ar hA hm j K s.mem hK hU)
    (io_avoidPX st ar hA hm j (KU K E) s.mem (regionOKP_kuV hK hP) (userOKP_ku hU)) h

/-- **The st slot.** -/
theorem insAW_st : InsAW st (stSlotPX st ar hA hm) := by
  intro K E s hK hU c hs q j _ _ hP J hM h
  exact insA_kuV hP J hM _ (st_avoidPX st ar hA hm j K s.mem hK hU)
    (st_avoidPX st ar hA hm j (KU K E) s.mem (regionOKP_kuV hK hP) (userOKP_ku hU)) h

/-- **IRQ.** -/
theorem insAW_irq : InsAW st (irqSlotPX st ar hA hm) := by
  intro K E s hK hU c hs q j _ _ hP J hM h
  exact insA_kuV hP J hM _ (irq_avoidPX st ar hA hm j K s.mem hK hU)
    (irq_avoidPX st ar hA hm j (KU K E) s.mem (regionOKP_kuV hK hP) (userOKP_ku hU)) h

/-- **The sl slot.** -/
theorem insAW_sl : InsAW st (slSlotPX st ar hA hm hSt a0) := by
  intro K E s hK hU c hs q j _ _ hP J hM h
  exact insA_kuV hP J hM _ (sl_avoidPXf st ar hA hm hSt a0 j K s.mem hK hU)
    (sl_avoidPXf st ar hA hm hSt a0 j (KU K E) s.mem (regionOKP_kuV hK hP) (userOKP_ku hU)) h

/-- **VM fault.** -/
theorem insAW_vmF : InsAW st (vmFSlotPY st ar hA hm) := by
  intro K E s hK hU c hs q j _ _ hP J hM h
  exact insA_kuV hP J hM _ (vmF_avoidPY st ar hA hm j K s.mem hK hU)
    (vmF_avoidPY st ar hA hm j (KU K E) s.mem (regionOKP_kuV hK hP) (userOKP_ku hU)) h

/-- **VM ReplyRecv.** -/
theorem insAW_vmR : InsAW st (vmRSlotPY st ar hA hm) := by
  intro K E s hK hU c hs q j _ _ hP J hM h
  exact insA_kuV hP J hM _ (vmR_avoidPY st ar hA hm j K s.mem hK hU)
    (vmR_avoidPY st ar hA hm j (KU K E) s.mem (regionOKP_kuV hK hP) (userOKP_ku hU)) h

/-- **[W] The three VM-epoch slots left** (named premise; module docstring): CNodeDelete, Copy / Mint and delPte in
VM epochs are `InsA` at the epoch's paging words, given `VmPwe`. -/
structure VmInsAE : Prop where
  /-- [W] CNodeDelete in VM epochs (masked walk of `unmap_page`). -/
  inv : InsAW st (invSlotVX st ar hA hm)
  /-- [W] Copy / Mint in VM epochs (no table walk; path not `rJ`-shaped). -/
  cm : InsAW st (cmSlotVX st ar hA hm)
  /-- [W] delPte in VM epochs (masked walk, store `0`). -/
  del : InsAW st (delPteSlotVX st ar hA hm)

end slots

/-! ## 5. The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
