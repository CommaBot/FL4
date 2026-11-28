/-
# P2 (line p3mc, gen 40): a vmF start at the second boot start `(sR, σR)`; V13 on an execution whose start carries `ybw`; σR's reachability

Gen 39 built `(sR, σR)` (a running, current root thread) and V13's vmF entry record `vmFEnt_R`, at an index whose lock
set is every address. A start fact names the lock set the core holds at the start (`GlueAt`'s `Locks σ = hs`), and
the start configurations of gen 37 hold no lock, so that index cannot start. Here:

* **The index `jR O`** (fault `addr = code = 0`, P1's sets of `KR O`, **no lock**: `Locks = fun _ _ => False`) and
  **`vmFEnt0_R`**: `VmFEntV13` at `sR` with `nv`, `ix`, `hct : NonIdle` [P], `lk` [P], `ybw` [J], `gl` [P] all
  proved. `lk` / `gl` are now not trivial: after `update_timestamp` (`ut_R`: it is `utW sR n`, writing `CUR_TIME` /
  `CONSUMED` only) the root thread's fault-handler slot (`tRw + 96`) still holds two zero words, so `Cap::decode`
  gives `Null`, never an endpoint (**`noEp_R`**): the fault fast path's checks fail and no lock is needed.
* The memory side at `KR O`: `sR_memR` (`bsL.mem sR = memR`), `KR_ksb`, `ptesR_R` / **`hc0_R`**, **`homed_R`**,
  **`view_R`** (core 0's view of `memR` is `memR`; as gen 37's `homed_B` / `view_B`).
* **`startVmF_R`**: `StartV13`'s `.vmF` clause at `ChR O`, `KR O`, memory `memR`, core 0, no lock held:
  `LkC`, and given `KernDetS`, `VmFPremB` (`nv`, `bun`, `kd`), the record at `σ = sR`, and for every
  `h' : VmFPremA` the `GlueAt` of the lifted VM-fault body at `sR` — the program is `q0R` (the body at `h'`, by
  proof irrelevance one program for every `h'`).
* The execution: `kR` (`annV` of the PTE cut of `q0R`), `g3R` (the `.start` step's `Fl4StepV15` fields
  at the native configuration, gen 56),
  **`execStartV13_R`** (arm → enter → `.start` of the vmF path from `cfg0 (KR O) memR`), `stFree_kR`,
  **`runEndV13_R`** (the whole body run, `run_loc`, then leave), **`topV13_R`**: `serializable_fl4_localV13`
  applied to it, `Run (.start (kR O a)) memR s.mem`. **The start fact used carries `ybw` [J] and `NonIdle` [P],
  both proved at its chain state `sR`.**

## σR's reachability (goal 3a; reading + two lemmas)
`σR` is a state of the ported spec and a `JReachU3.start` start of P3, but **not seL4-reachable**:
* the root TCB's timeout-handler slot (`tcbCnodeIndex 4`) holds `schedContextCap scRp 0`. The only writer of that
  slot with a non-null cap is `invokeTcb (.threadControlCaps …)`'s `installTcbCap target slot 4`, whose cap comes
  only from `decodeSetTimeoutEp` (Fl4Spec/Decode l.765–772, l4v `decode_set_timeout_ep`) through `checkHandlerEp`,
  i.e. it passes `validFaultHandler` (Decode l.671–674, l4v `valid_fault_handler`: an endpoint cap with handler
  rights, or null); retype creates TCBs with null caps, and CNode operations reach CNode slots only (lookups go
  through `resolve_address_bits`). l4v keeps the same restriction as an invariant (`tcb_cap_cases` index 4,
  `valid_tcb`). **`tcbR_tmo_not_vfh`**: the cap fails `validFaultHandler`.
* the CSpace-root slot (`tcbCnodeIndex 0`) holds `threadCap tRp`; its only installer, `decodeCvSpace` (Decode
  l.704), requires `isCnodeCap`. **`tcbR_ctable_not_cnode`**.
Cheapest reachable alternative (not built, size below): seL4's initial-thread shape — a root CNode `cnR` (radix 1,
two slots) holding `threadCap tRp` and `schedContextCap scRp 0`, `tcbCtable := cnodeCap cnR 1 []`, slot 4 null.
That changes the typed heap (`HR`, `thR`: one more CNode object, its two slots in the MDB with `GR`), the store
words (`cnR`'s 64 bytes, the root slot's cap word), and so every gen-39 unit that enumerates objects or slots
(`StateRel` / `SlotsValid`, `MdbLinks` / `CdtRel` / `MdbInv`, `KTyped`, `JCovD`, `LiveJ`, `SInvX`'s cap fields,
`CnDom`, `IfLiveT` / `ScLiveT` witnesses): about 2500–3500 lines (gen 39 was 4670 with six executors).

No premise beyond `OpaqueH` (where `locPlat_archT` is used). No existing statement changed except the root import
list.

## Arch-parametric vmF start chain (p3J gen 62)
The chain above is stated once over the configuration's arch `ar` / `hA`, the entry record's `arI` / `AR` / `MR`, a
platform record `PG`, and a layout `K` / chain `Ch` through `sR` (`ChainLay`, `Ch sR`, `K.ksb = kbB`, no VCPU, no PTE
word, `SerExitW PG K Ch`): `homed_of`, `view_of`, `vmFEnt0_RP`, the index `jRP` (+ `jRP_spec`), the programs
`q0RP` / `k0RP` / `kRP`, `startVmF_RP`, `kRP_eq`, `g3RP`, `stFree_kRP`, `runEndV13_RP` (with P2/BootStart's
`exec_startG`, P2/BootRJAtZ's `ybw_of`). The `archT` names (`jR`, `q0R`, `k0R`, `kR`, `jR_spec`, `vmFEnt0_R`,
`startVmF_R`, `kR_eq`, `g3R`, `stFree_kR`, `homed_R`, `view_R`) are their instances at `KR O`, `ChR O`,
`locPlat_archT O bs_ext`, with statements unchanged; the defs' values are now the generic defs applied (definitionally
the old bodies). P3/P3JBootV15T1 uses the chain at `archT1`.
-/
import Fl4Proofs.P2.BootRJAtZ
import Fl4Proofs.P2.BootRun
import Fl4Proofs.P1.EntryVacuous
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical
open Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2EV Fl4Proofs.P2.OwnMapP Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.E2EP
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue Phase Gate Prog Run release VEq
  narrowSP)
open Fl4Proofs.P2.E2E (SerStep SP tr rdN)

noncomputable section

/-! ## σR's reachability (goal 3a) -/

/-- **The root thread's timeout-handler cap fails l4v's `valid_fault_handler`** (module docstring). -/
theorem tcbR_tmo_not_vfh : ¬ Fl4Spec.validFaultHandler tcbR.tcbTimeoutHandler := by
  unfold Fl4Spec.validFaultHandler
  rintro (⟨h, -⟩ | h)
  · simp [tcbR, Fl4Spec.isEpCap] at h
  · simp [tcbR] at h

/-- **The root thread's CSpace-root cap is no CNode cap** (`decodeCvSpace` installs CNode caps only). -/
theorem tcbR_ctable_not_cnode : Fl4Spec.isCnodeCap tcbR.tcbCtable = false := rfl

/-! ## The memory at the second boot start -/

/-- **The second boot store's word map is `memR`.** -/
theorem sR_memR : bsL.mem sR = memR := by
  funext a
  by_cases ha : Aligned a
  · exact memR_mem ha
  · show (if Aligned a then memR a else 0#u64) = memR a
    rw [if_neg ha]
    show 0#u64 = wordR a.val
    unfold Aligned at ha
    exact (wordR_zero_of (by omega)).symm

theorem KR_ksb (O : LocPlatM.OpaqueH) : (KR O).ksb = kbB := by
  obtain ⟨Z, H, Cx, nc, hK, -⟩ := chainC_spec (LocPlatM.locPlat_archT O bs_ext) jReach_R
  exact (congrArg OwnMap.KLayout.ksb hK).trans rfl

theorem namedM_R {r : U64} : ¬ NamedM memR kbB r := by
  rintro ⟨hi, hh, hne, -⟩
  apply hne
  show wordR (Vs.atA kbB hi).val = 0#u64
  rw [Vs.atA_val (by rw [kbB_val]; norm_num) hh, kbB_val]
  exact wordR_zero_of (by omega)

/-- (p3J gen 61) No leaf PTE is reachable in `memR` at every layout with kernel base `kbB`. -/
theorem ptesR_memR_of {K : KLayoutP} (hK : K.ksb = kbB) : ptesR K memR = ∅ := by
  ext e
  constructor
  · intro he
    obtain ⟨⟨r, hr, -⟩, -⟩ := he
    rw [hK] at hr
    exact (namedM_R hr).elim
  · intro he
    exact False.elim he

theorem ptesR_R (O : LocPlatM.OpaqueH) : ptesR (KR O) memR = ∅ := ptesR_memR_of (KR_ksb O)

/-- **`hc0` at the second boot layout and memory.** -/
theorem hc0_R (O : LocPlatM.OpaqueH) : (KR O).vcpus = ∅ ∧ (KR O).ptes = ptesR (KR O) memR :=
  ⟨rfl, (ptesR_R O).symm⟩

/-- (p3J gen 62) **`memR` is homed on core 0** at every layout with kernel base `kbB` whose bundle holds at `sR`
(`homed_R` below is its instance at `KR O`). -/
theorem homed_of {K : KLayoutP} (hJ : SlJAt (L := bsL) K.toKLayout sR) (hks : K.ksb = kbB) :
    CoreView.Homed K.toKLayout 0#u64 memR := by
  refine ⟨fun t ht => ?_, fun p b hb => ?_, fun d b hb hd _ => ?_⟩
  · obtain ⟨-, -, e⟩ := GlueCross.slJAt_aff hJ ht
    rw [sR_memR] at e
    exact e
  · obtain ⟨z, hp, -⟩ := OwnMap.region_sc_inv hb
    obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
    have hpC := B.j.hscC p z hp
    have e1 := B.j.xtop.fin.1.1.1.core p hpC
    obtain ⟨Q, R0, hcq, -⟩ := B.j.xtop.fin.1.1.1.lists
    have e2 := hcq.cur
    rw [sR_memR] at e1
    exact e1.trans e2.symm
  · obtain ⟨-, h1, -⟩ := region_node_inv' hb
    have hk : K.toKLayout.ksb = kbB := hks
    have hd1 : d.val ≠ 0 := fun h0 => hd (UScalar.eq_of_val_eq (by simp [h0]))
    rw [hk, kbB_val] at h1
    show wordR b.val = 0#u64
    exact wordR_zero_of (by omega)

/-- **`memR` is homed on core 0 at `KR O`** (as `homed_B`). -/
theorem homed_R (O : LocPlatM.OpaqueH) : CoreView.Homed (KR O).toKLayout 0#u64 memR :=
  homed_of (slJAt_sR O) (KR_ksb O)

/-- (p3J gen 62) **Core 0's view of `memR` is `memR`** at every such layout on a chain through `sR`. -/
theorem view_of {K : KLayoutP} {Ch : BS → Prop} (hL : ChainLay (L := bsL) K.toKLayout Ch) (hC : Ch sR)
    (hks : K.ksb = kbB) : CoreView.view K.toKLayout 0#u64 memR = memR :=
  CoreView.view_eq_self hL.hK (homed_of (hL.bun sR hC) hks)

/-- **Core 0's view of `memR` is `memR`.** -/
theorem view_R (O : LocPlatM.OpaqueH) : CoreView.view (KR O).toKLayout 0#u64 memR = memR :=
  CoreView.view_eq_self (chR_lay O).hK (homed_R O)

/-! ## No endpoint in the root thread's fault-handler slot after `update_timestamp` -/

section ut
variable {A : Type} (ar : machine.Arch A)

theorem nodePlaced_R : NodePlaced bst HR.tcbs sR (bsL.cpu sR) := uF_nodePlaced

/-- **`update_timestamp` at `sR` is `utW sR n`** for the clock reading `n`. -/
theorem ut_R {a a1 : A} {s1 : BS} (h : sched.update_timestamp bst ar sR a = ok (s1, a1)) :
    ∃ n, s1 = utW (L := bsL) sR n := by
  have h' := h
  unfold sched.update_timestamp at h'
  rw [cur_time_ok] at h'
  simp only [bind_ok] at h'
  obtain ⟨⟨n, a2⟩, hn, -⟩ := bind_eq_ok h'
  rw [update_timestamp_ok ar nodePlaced_R hn] at h
  exact ⟨n, (congrArg Prod.fst (ok_inj_ff h)).symm⟩

theorem ctA_R_val : (ctA (L := bsL) sR).val = 18446744071562114304 + 48 := by
  show (bsL.nodeAt sR 0#u64 layout.node.CUR_TIME).val = _
  rw [sR_nodeAt_val (by simp [layout.node.CUR_TIME])]
  simp [layout.node.CUR_TIME]

theorem cnA_R_val : (cnA (L := bsL) sR).val = 18446744071562114304 + 40 := by
  show (bsL.nodeAt sR 0#u64 layout.node.CONSUMED).val = _
  rw [sR_nodeAt_val (by simp [layout.node.CONSUMED])]
  simp [layout.node.CONSUMED]

/-- `update_timestamp`'s writes miss every other aligned word of `sR`. -/
theorem utR_mem (n : U64) {b : U64} (hb : Aligned b) (h1 : b.val ≠ 18446744071562114304 + 48)
    (h2 : b.val ≠ 18446744071562114304 + 40) : bsL.mem (utW (L := bsL) sR n) b = bsL.mem sR b :=
  utW_mem nodePlaced_R n hb (fun e => h1 (by rw [e, ctA_R_val])) (fun e => h2 (by rw [e, cnA_R_val]))

/-- **The current thread after `update_timestamp` is the root thread.** -/
theorem utR_curW (n : U64) : bsL.curW (utW (L := bsL) sR n) = tRw := by
  have e : bsL.curW (utW (L := bsL) sR n) = bsL.curW sR := by
    unfold LawfulStore.curW
    rw [utW_cpu, nodeAt_of_ksb (utW_ksb sR n)]
    have hv : (bsL.nodeAt sR (bsL.cpu sR) layout.node.CUR_THREAD).val = 18446744071562114304 := by
      show (bsL.nodeAt sR 0#u64 layout.node.CUR_THREAD).val = _
      rw [sR_nodeAt_val (by rw [curth0]; omega), curth0]
    exact utR_mem n (nodeR_aligned (by rw [curth0]; omega) (by rw [curth0])) (by rw [hv]; omega)
      (by rw [hv]; omega)
  rw [e, sR_curW]

theorem fhA_val : (slotIdx tRw layout.tcb.SLOT_FAULT_HANDLER).val = 18446744071562076160 + 96 := by
  have h3 : layout.tcb.SLOT_FAULT_HANDLER.val = 3 := by simp [layout.tcb.SLOT_FAULT_HANDLER]
  unfold slotIdx
  simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, tRw_val, h3]
  simp [U64.size, U64.numBits]

theorem fhA8_val : (core.num.U64.wrapping_add (slotIdx tRw layout.tcb.SLOT_FAULT_HANDLER) 8#u64).val =
    18446744071562076160 + 104 := by
  simp only [core.num.U64.wrapping_add_val_eq, fhA_val]
  simp [U64.size, U64.numBits]

/-- **No endpoint cap in the current thread's fault-handler slot after `update_timestamp` at `sR`.** -/
theorem noEp_R {a a1 : A} {s1 : BS} {sl ptr badge : U64} {x y g gr : Bool}
    (h : sched.update_timestamp bst ar sR a = ok (s1, a1))
    (hsl : obj.Tcb.slot (bsL.curW s1) layout.tcb.SLOT_FAULT_HANDLER = ok sl)
    (hc : obj.Slot.cap bst sl s1 = ok (capability.Cap.Endpoint ptr badge x y g gr)) : False := by
  obtain ⟨n, rfl⟩ := ut_R ar h
  rw [utR_curW, tcb_slot_val] at hsl
  have e := ok_inj_ff hsl
  subst e
  have z1 : wordR (18446744071562076160 + 96) = 0#u64 := wordR_zero_of (by omega)
  have z2 : wordR (18446744071562076160 + 104) = 0#u64 := wordR_zero_of (by omega)
  rw [slot_cap_dec, utR_mem n (by show _ % 8 = 0; rw [fhA_val]) (by rw [fhA_val]; omega) (by rw [fhA_val]; omega),
    utR_mem n (by show _ % 8 = 0; rw [fhA8_val]) (by rw [fhA8_val]; omega) (by rw [fhA8_val]; omega),
    memR_at fhA_val (by omega), memR_at fhA8_val (by omega), z1, z2, decode_encode_null.2] at hc
  have e2 := ok_inj_ff hc
  cases e2

end ut

/-! ## The vmF index without locks and its entry record -/

/-- (p3J gen 62) **V13's vmF entry record at an index without locks** at every layout without VCPU whose bundle
holds at `sR`, on a chain `Ch` through `sR`, for every arch pair (`vmFEnt0_R` below is its instance at `KR O`,
`ChR O`, `archT`). -/
theorem vmFEnt0_RP {K : KLayoutP} {Ch : BS → Prop} (hv : K.vcpus = ∅) (hJ : SlJAt (L := bsL) K.toKLayout sR)
    (hC : Ch sR) {A : Type} (ar : machine.Arch A) {A3 : Type} (arI : machine.Arch A3)
    (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop) :
    ∃ i : VmFArg BS, i.Locks = (fun _ _ => False) ∧ Ch sR ∧
      VmFEntV13 bst ar arI AR MR i K.toKLayoutV sR := by
  obtain ⟨Cs, Ac, Ω, U, hB⟩ := bunIxV_of hJ
  refine ⟨⟨0#u64, 0#u64, K.toKLayout.heap.tcbs, Cs, Ω, U, K.toKLayout.heap.frame,
    K.toKLayout.heap.replies, K.toKLayout.heap.scs, K.toKLayout.heap.ntfns, Ac,
    K.toKLayout.heap, K.toKLayout.heap.scBits, fun _ _ => False⟩, rfl, hC, ?_⟩
  exact
    { nv := hv
      ix := hB
      hct := nonIdle_R
      lk := fun a s1 a1 ptr badge dest r hu hF => by
        obtain ⟨sl, x, y, g, gr, hsl, hc, -⟩ := hF.cap
        exact (noEp_R ar hu hsl hc).elim
      ybw := ybw_of hJ
      gl := fun a s1 a1 sl ptr badge x y g gr hu hsl hc => (noEp_R ar hu hsl hc).elim }

/-- **V13's vmF entry record at an index without locks** (module docstring). -/
theorem vmFEnt0_R (O : LocPlatM.OpaqueH) {A : Type} (ar : machine.Arch A) :
    ∃ i : VmFArg BS, i.Locks = (fun _ _ => False) ∧ ChR O sR ∧
      VmFEntV13 bst ar LocPlatM.archT LocPlatM.ART modelMR i (KR O).toKLayoutV sR :=
  vmFEnt0_RP rfl (slJAt_sR O) (chR_sR O) ar LocPlatM.archT LocPlatM.ART modelMR

/-- (p3J gen 62) **The index** `vmFEnt0_RP` chooses (`jR` below is its instance). -/
def jRP {K : KLayoutP} {Ch : BS → Prop} (hv : K.vcpus = ∅) (hJ : SlJAt (L := bsL) K.toKLayout sR) (hC : Ch sR)
    {A : Type} (ar : machine.Arch A) {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) : VmFArg BS :=
  Classical.choose (vmFEnt0_RP hv hJ hC ar arI AR MR)

theorem jRP_spec {K : KLayoutP} {Ch : BS → Prop} (hv : K.vcpus = ∅) (hJ : SlJAt (L := bsL) K.toKLayout sR)
    (hC : Ch sR) {A : Type} (ar : machine.Arch A) {A3 : Type} (arI : machine.Arch A3)
    (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop) :
    (jRP hv hJ hC ar arI AR MR).Locks = (fun _ _ => False) ∧ Ch sR ∧
      VmFEntV13 bst ar arI AR MR (jRP hv hJ hC ar arI AR MR) K.toKLayoutV sR :=
  Classical.choose_spec (vmFEnt0_RP hv hJ hC ar arI AR MR)

/-- **The index**: `vmFEnt0_R`'s, at the family's arch. -/
def jR (O : LocPlatM.OpaqueH) : VmFArg BS :=
  jRP (K := KR O) rfl (slJAt_sR O) (chR_sR O) LocPlatM.archT LocPlatM.archT LocPlatM.ART modelMR

theorem jR_spec (O : LocPlatM.OpaqueH) : (jR O).Locks = (fun _ _ => False) ∧ ChR O sR ∧
    VmFEntV13 bst LocPlatM.archT LocPlatM.archT LocPlatM.ART modelMR (jR O) (KR O).toKLayoutV sR :=
  jRP_spec rfl (slJAt_sR O) (chR_sR O) LocPlatM.archT LocPlatM.archT LocPlatM.ART modelMR

/-! ## The start fact -/

section vmFG
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar)

/-- (p3J gen 62) The lifted VM-fault body from `sR` at the configuration's arch `ar`, index `i`, layout `K`
(`q0R` below is its instance). -/
def q0RP (i : VmFArg BS) (K : KLayoutP) (a : A) (hK : RegionOKP K) (hU : UserOKP K) : SP :=
  if h : VmFPremA bst ar i K.toKLayoutV then
    ((vmFSlotA bst ar hA (masksWr_plain bst)).liftAt i K.toKLayoutV memR hK.base hU.base h).body sR a
  else .done

/-- (p3J gen 62) The PTE cut of `q0RP` (`k0R` below is its instance). -/
def k0RP (i : VmFArg BS) (K : KLayoutP) (a : A) (hK : RegionOKP K) (hU : UserOKP K) : SP :=
  cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout memR) 0#u64
    (q0RP ar hA i K a hK hU) ∅

/-- (p3J gen 62) The re-annotated `k0RP` (`kR` below is its instance). -/
def kRP (i : VmFArg BS) (K : KLayoutP) (a : A) : SP :=
  if h : RegionOKP K ∧ UserOKP K then annV (cfg0 K memR) K 0#u64 memR (k0RP ar hA i K a h.1 h.2)
  else .done

variable (a0 : A) {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
  (MR : A3 → Fl4Spec.MachineState → Prop)

/-- (p3J gen 62) **`StartV13`'s vmF clause at `sR`** for an index `i` without locks whose entry record holds
there, at every layout whose bundle holds at `sR` (`startVmF_R` below is its instance). -/
theorem startVmF_RP {K : KLayoutP} {Ch : BS → Prop} {i : VmFArg BS} (hJ : SlJAt (L := bsL) K.toKLayout sR)
    (hi : i.Locks = (fun _ _ => False) ∧ Ch sR ∧ VmFEntV13 bst ar arI AR MR i K.toKLayoutV sR)
    (a : A) (hK : RegionOKP K) (hU : UserOKP K) (hs : U64 → Prop)
    (hhs : (fun _ => False) = hs) :
    StartV13 bst ar hA a0 arI AR MR Ch K memR hK hU 0#u64 hs (k0RP ar hA i K a hK hU) (.inl (.vmF i)) := by
  subst hhs
  obtain ⟨hL, hC, hE⟩ := hi
  refine ⟨⟨fun _ => False, hL⟩, fun hk => ⟨q0RP ar hA i K a hK hU, ⟨⟨hE.nv, ⟨sR, hJ⟩, hk⟩, sR, ⟨hC, hE⟩,
    fun h' => ⟨sR, a, rfl, rfl, ?_, fun x hx _ => memR_mem hx, ?_⟩⟩, rfl⟩⟩
  · show i.Locks sR = fun _ => False
    rw [hL]
  · unfold q0RP
    rw [dif_pos h']

theorem kRP_eq (i : VmFArg BS) (K : KLayoutP) (a : A) (hK : RegionOKP K) (hU : UserOKP K) :
    kRP ar hA i K a = annV (dfg2 K memR (kRP ar hA i K a)) K 0#u64 memR (k0RP ar hA i K a hK hU) := by
  unfold kRP
  rw [dif_pos ⟨hK, hU⟩]
  rfl

variable {arI AR MR}

/-- (p3J gen 62) **The `.start` step's fields** at a vmF index of `sR`, at every platform record `PG`, layout and
chain through `sR` (`g3R` below is its instance). -/
theorem g3RP (PG : LocPlat bst arI AR MR) {K : KLayoutP} {Ch : BS → Prop} {i : VmFArg BS}
    (hL : ChainLay (L := bsL) K.toKLayout Ch) (hC : Ch sR) (hks : K.ksb = kbB)
    (hi : i.Locks = (fun _ _ => False) ∧ Ch sR ∧ VmFEntV13 bst ar arI AR MR i K.toKLayoutV sR)
    (hB : SerExitW PG K.toKLayoutV Ch) (hc : K.vcpus = ∅ ∧ K.ptes = ptesR K memR) (a : A) :
    Fl4StepV15 (ExecCfg.native bst ar hA a0 arI AR MR) PG
      (dfg2 K memR (kRP ar hA i K a)) K (fun _ => Ch) 0#u64 (dfg3 K memR (kRP ar hA i K a)) K (fun _ => Ch) where
  arm p h := by rw [dfg3_ph0] at h; cases h
  start p0 k W h hK hU := by
    rw [dfg2_ph0] at h
    injection h with e1 e2 e3
    injection e2 with e2
    subst e2
    refine ⟨memR, ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, .inl (.vmF i), k0RP ar hA i K a hK hU, ?_,
      Or.inr (kRP_eq ar hA i K a hK hU)⟩
    rw [view_of hL hC hks]
    exact startVmF_RP ar hA a0 arI AR MR (hL.bun sR hC) hi a hK hU _ (dfg2_lk _ _ _)
  serX _ := fun _ => hB
  serC _ := hc
  serG _ := mapsP_dfg3 _ _ _
  keep _ := ⟨rfl, rfl⟩

/-- (p3J gen 62) **The armed vmF body has no `.start` node** (`stFree_kR` below is its instance). -/
theorem stFree_kRP (i : VmFArg BS) (K : KLayoutP) (a : A) : StFree (kRP ar hA i K a) := by
  unfold kRP
  split
  · refine stFree_narrow _ _ _ _ _ _ (stFree_cutP _ _ _ _ _ _ _ ?_)
    unfold q0RP
    split
    · exact stFree_tr _ _ _ _ _ _ _ _ _ _ _
    · trivial
  · trivial

/-- (p3J gen 62) **V13: the vmF start at `sR`, its whole body, and the leave**, at every platform record `PG`,
layout and chain through `sR` (`runEndV13_R` below is its instance). -/
theorem runEndV13_RP (PG : LocPlat bst arI AR MR) {K : KLayoutP} {Ch : BS → Prop} {i : VmFArg BS}
    (hL : ChainLay (L := bsL) K.toKLayout Ch) (hC : Ch sR) (hks : K.ksb = kbB)
    (hi : i.Locks = (fun _ _ => False) ∧ Ch sR ∧ VmFEntV13 bst ar arI AR MR i K.toKLayoutV sR)
    (hB : SerExitW PG K.toKLayoutV Ch) (hc : K.vcpus = ∅ ∧ K.ptes = ptesR K memR) (a : A) :
    ∃ (s : Cfg U64 U64 U64 U64) (E : U64 → U64),
      ExecV15 (ExecCfg.native bst ar hA a0 arI AR MR) PG (cfg0 K memR) K (fun _ => Ch) s K (fun _ => Ch) E ∧
      NoLoc s ∧ s.log = [.start (kRP ar hA i K a)] := by
  obtain ⟨E, he⟩ := exec_startG (fun _ => hB) hc (g3RP ar hA a0 PG hL hC hks hi hB hc a)
  obtain ⟨s, he', hq, hl⟩ := runEnd (stFree_kRP ar hA i K a) he
  exact ⟨s, E, he', hq, hl⟩

end vmFG

/-- The lifted VM-fault body from `sR` (one program for every proof of the slot's premise). -/
def q0R (O : LocPlatM.OpaqueH) (a : Fl4Spec.MachineState) (hK : RegionOKP (KR O)) (hU : UserOKP (KR O)) : SP :=
  q0RP LocPlatM.archT LocPlatM.archT_total (jR O) (KR O) a hK hU

/-- **The started program**: the PTE cut of `q0R`. -/
def k0R (O : LocPlatM.OpaqueH) (a : Fl4Spec.MachineState) (hK : RegionOKP (KR O)) (hU : UserOKP (KR O)) : SP :=
  k0RP LocPlatM.archT LocPlatM.archT_total (jR O) (KR O) a hK hU

/-- **`StartV13`'s vmF clause at the second boot start** (module docstring). -/
theorem startVmF_R (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) (hK : RegionOKP (KR O))
    (hU : UserOKP (KR O)) (hs : U64 → Prop) (hhs : (fun _ => False) = hs) :
    StartV13 bst LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART modelMR (ChR O) (KR O) memR hK hU
      0#u64 hs (k0R O a hK hU) (.inl (.vmF (jR O))) :=
  startVmF_RP LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART modelMR (slJAt_sR O) (jR_spec O)
    a hK hU hs hhs

/-! ## The execution: arm, enter, start, run, leave -/

/-- **The armed body**: the re-annotated started program. -/
def kR (O : LocPlatM.OpaqueH) (a : Fl4Spec.MachineState) : SP :=
  kRP LocPlatM.archT LocPlatM.archT_total (jR O) (KR O) a

theorem kR_eq (O : LocPlatM.OpaqueH) (a : Fl4Spec.MachineState) (hK : RegionOKP (KR O)) (hU : UserOKP (KR O)) :
    kR O a = annV (dfg2 (KR O) memR (kR O a)) (KR O) 0#u64 memR (k0R O a hK hU) :=
  kRP_eq LocPlatM.archT LocPlatM.archT_total (jR O) (KR O) a hK hU

/-- **The `.start` step's fields** at the vmF index. -/
theorem g3R (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) :
    Fl4StepV15 (ExecCfg.native bst LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART modelMR)
      (LocPlatM.locPlat_archT O bs_ext)
      (dfg2 (KR O) memR (kR O a)) (KR O) (fun _ => ChR O) 0#u64 (dfg3 (KR O) memR (kR O a)) (KR O)
      (fun _ => ChR O) :=
  g3RP LocPlatM.archT LocPlatM.archT_total a0 (LocPlatM.locPlat_archT O bs_ext) (chR_lay O) (chR_sR O) (KR_ksb O)
    (jR_spec O) (serExitW_R O) (hc0_R O) a

/-- **V13: an execution from the second boot start whose last step is the `.start` of the vmF path.** -/
theorem execStartV13_R (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) :
    ∃ E, ExecV15 (ExecCfg.native bst LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART modelMR)
      (LocPlatM.locPlat_archT O bs_ext) (cfg0 (KR O) memR) (KR O) (fun _ => ChR O) (dfg3 (KR O) memR (kR O a))
      (KR O) (fun _ => ChR O) E :=
  exec_start (fun _ => serExitW_R O) (hc0_R O) (g3R O a0 a)

/-- **The armed vmF body has no `.start` node.** -/
theorem stFree_kR (O : LocPlatM.OpaqueH) (a : Fl4Spec.MachineState) : StFree (kR O a) :=
  stFree_kRP LocPlatM.archT LocPlatM.archT_total (jR O) (KR O) a

/-- **V13: the vmF start, its whole body, and the leave.** -/
theorem runEndV13_R (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) :
    ∃ (s : Cfg U64 U64 U64 U64) (E : U64 → U64),
      ExecV15 (ExecCfg.native bst LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART modelMR)
        (LocPlatM.locPlat_archT O bs_ext) (cfg0 (KR O) memR) (KR O) (fun _ => ChR O) s (KR O) (fun _ => ChR O) E ∧
      NoLoc s ∧ s.log = [.start (kR O a)] := by
  obtain ⟨E, he⟩ := execStartV13_R O a0 a
  obtain ⟨s, he', hq, hl⟩ := runEnd (stFree_kR O a) he
  exact ⟨s, E, he', hq, hl⟩

end

end Fl4Proofs.P2.BootSt
