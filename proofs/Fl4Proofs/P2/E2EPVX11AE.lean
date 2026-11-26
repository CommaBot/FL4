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

/-- **An `ExecVX4c` execution is an `ARunR` one at the epoch's paging words**; `hIns` also receives `VmPwe` in VM
epochs (`execVX4b_aRunR`'s proof). -/
theorem execVX4c_aRunR {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (P : LocPlat st arI AR MR)
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEp P K Ch s) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (Ch : S → Prop) (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K)
      (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : ι),
      (K.vcpus = ∅ → SerExitW P K.toKLayoutV Ch) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      (K.vcpus ≠ ∅ → VmPwe K E) → EpochJV K E s →
      MapsP K s → SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q →
      InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecVX4c LP SF P s0 K0 Ch0 s K Ch E) :
    ARunR ADEq NotPresent s0 s (PWE K E) ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s ∧
      (K.vcpus = ∅ → SerExitW P K.toKLayoutV Ch) ∧ (K.vcpus ≠ ∅ → VtxBundle4 st L K) ∧
      (K.vcpus ≠ ∅ → VmPwe K E) ∧ EpochJV K E s := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  induction h with
  | refl => exact ⟨.refl _, hK0, hU0, hM0, fun _ => hB, fun hn => (hn hc0.1).elim, fun hn => (hn hc0.1).elim,
      epochJV_ser hc0.2⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 E1 _ hS g hPw ih =>
    obtain ⟨hR, hK, hU, hM, hX, hV, hW, J⟩ := ih
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
        exact ⟨hst', hK'.1, hK'.2, g.serG hs, fun _ => hXs, fun hn => (hn nv).elim, fun hn => (hn nv).elim,
          epochJV_ser hc⟩
      · have hK' := hb.b.okP hc
        exact ⟨hst', hK'.1, hK'.2, g.serG hs, fun nv => (hne nv).elim, fun _ => hb, hPw hs,
          epochJV_ser hc⟩
    · rw [if_neg hs]
      obtain ⟨eK, eC⟩ := g.keep hs
      subst eK eC
      have hal := allowed_of_sinv hSI c1
      refine ⟨.step hR hS hok (fun p0 k W hph => ?_), hK, hU, maps_stepP hK hM hal hS hs, hX, hV, hW,
        epochJV_keep J (fun x hx => step_gate_keep hM hal hS hs hx)⟩
      obtain ⟨i, hi, hP⟩ := hst p0 k W hph
      exact hIns _ _ _ _ hK hU _ _ _ i hX hV hW J hM hi hP
  | hw _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, hV, hW, J⟩ := ih
    exact ⟨.hw hR (hH.hwWr hK hM), hK, hU, maps_hwP hK hM hH, hX, hV, hW,
      epochJV_keep J (fun x hx => hw_gate_keep hK hM hH hx)⟩
  | mmu _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, hV, hW, J⟩ := ih
    exact ⟨.ad hR (adWr_pwe hK hM hH), hK, hU, maps_pwe hK hM hH, hX, hV, hW, epochJV_mmu J hH⟩

/-- **Every quiescent `ExecVX4c` state is serial**, given `hSF` and `hIns`. -/
theorem serializable_VX4c_of {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (P : LocPlat st arI AR MR)
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEp P K Ch s) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (Ch : S → Prop) (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K)
      (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : ι),
      (K.vcpus = ∅ → SerExitW P K.toKLayoutV Ch) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      (K.vcpus ≠ ∅ → VmPwe K E) → EpochJV K E s →
      MapsP K s → SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q →
      InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecVX4c LP SF P s0 K0 Ch0 s K Ch E) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_safeR adEq_equiv h0 hA0 (execVX4c_aRunR P hSF hIns h0 hA0 hB hc0 hM0 h).1 hq

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

/-- **FL4 end to end with every U1 slot in native and VM epochs and the host walker's A/D writes** (module
docstring): VX11's premises (`P`, [P] `hIoa`, `h0`, `hA0`, `hB`, `hc0`, `hM0`, the execution, `hq`) over `ExecVX4c`
(so [S] `VmPwe` at VM serial exits), [P] `MmuAD` (its `mmu` step), and [W] `hVm : VmInsAE` (three fields). -/
theorem serializable_fl4_localVX11AE (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (hVm : VmInsAE st ar hA hm)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4c (famVX11 st ar hA hm hSt a0) (StartVX11U st ar hA hm hSt a0 (arI := arI) (AR := AR) (MR := MR))
      P s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  refine serializable_VX4c_of P (vx11_startAt st ar hA hm hSt a0 P hIoa) ?_ h0 hA0 hB hc0 hM0 h hq
  intro Ch K E s hK hU c hs q i hX hV hW J hM hsf hP
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
    exact insAW_vx st ar hA hm K E s hK hU c hs q j hne (hV hne) (hW hne) J hM hP
  · have hsf' : VtStartV4 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_vt st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1) J hM hP
  · have hsf' : IoStartX5 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_io st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1) J hM hP
  · have hsf' : StStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_st st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1) J hM hP
  · have hsf' : IrqStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_irq st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1) J hM hP
  · have hsf' : SlStartX st ar hA hm hSt a0 K s.mem hK hU c hs q j := hsf
    exact insAW_sl st ar hA hm hSt a0 K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1) J hM hP
  · have hsf' : InvStartX9 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact hVm.inv K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1) J hM hP
  · have hsf' : CMStartX9 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact hVm.cm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1) J hM hP
  · have hsf' : DelPteStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact hVm.del K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1) J hM hP
  · have hsf' : VmFStartY st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_vmF st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1) J hM hP
  · have hsf' : VmRStartY st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_vmR st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1) J hM hP

end top

end
end Fl4Proofs.P2.E2EP
