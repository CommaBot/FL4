/-
# P2 (line vmscope, gen 4): fewer VM-timer [S]s; the I/O-port slot in VM epochs — `serializable_fl4_localVX4`

`serializable_fl4_localVX2` (P2/E2EPVX3.lean) runs U1's family in native epochs (`K.vcpus = ∅`) and the VM-exit and
VM-timer slots in VM epochs, the latter under a start entry with six [S] parts (`VtmEnt`, `VtmU`, `VtFx.ub`, `.sl`,
`.pSg`, `QPs`). This module

1. **shrinks the VM-timer start entry** (`VtEntS`, below): `VtmU`'s IRQ-state / kernel-root / ASID-table clauses and
   the whole `sl` (`SlotLayV`) are now **derived** from the epoch's `VtxBundle` (`UserLayX`) and `QPs`; what is left
   is one documented [S] structure `VtEntS` beside `VtxBundle`;
2. **stage 4 (subset): the I/O-port slot (`handle_ioport_local`) starts in VM epochs.** Its path is the existing
   generic one (`io_localPathG2`: `IsProg`, `NoZero`, `ReadOnce` discharged) at `userV K`, with a `Pre` that has no
   P3 bundle (`IoPreX` = `IoPre ∧ AffAg ∧ Q`; at a VM-epoch state `SlJAt` is false: `JExt.vw` puts every TCB's VCPU
   word at 0); `NoVcpuRW` and the PTE avoidance (`io_avoidPX_path`) are the native proofs, which never used
   `vcpus = ∅`. The facts the native record took from `VFacts.ofEmpty nv bun` come from the epoch's bundle.

* **`slotLayV_ofLayX`** (`SlotLayV` of any threads at any state from `UserLayX`: `RegionOKX.tslot` + `LayP.region_slotW`),
  **`vtmU_ofX`** (`VtmU` from `UserLayX.uks`, `QPs.uoff` and the pool-entry clause), **`VtEntS`** [S],
  **`vtPreA_of_S`**, **`VtStartV4`**, **`vtStartV2_of_V4`**.
* **`VtxBundle4`** [S] = `VtxBundle` + `VcpuKsOff` + `IoLayA` (layout facts), **`vtxBundle4_of_vfacts`** (every P3
  bundle with `VFacts` [J] gives it: consistency), **`vcpuKs_ofKo`**.
* **`curW_wrX`**, **`ioRWDS_wrVX`** (`ioRWDS_wrV` without `SlJAt`), **`IoPreX`**, **`IoPremX`**, **`ioSlotX`**
  (`SlotU`), **`io_avoidPX_path`** / **`io_avoidPX`**, **`ioSlotPX`**; **`IoPremX2`** + **`.toX`**, **`IoStartX`**,
  **`ioStartX_at`**.
* **`Fl4StepVX4`** / **`ExecVX4`** (`ExecVX2` with `VtxBundle4` at VM exits), **`execVX_of_VX4`**, **`StartVX4`**,
  **`serializable_fl4_localVX4G`**, **`serializable_fl4_localVX4`** = VX2's family ⊕ `ioSlotPX`.

## Premise diff vs `serializable_fl4_localVX2`
| where | VX2 | VX4 |
|---|---|---|
| VM serial exit | `VtxBundle` [S] | `VtxBundle4` [S] = `VtxBundle` + `ko : VcpuKsOff` + `la : IoLayA` |
| vt start entry | `VtmEnt`, `VtmU`, `ub`, `sl`, `pSg`, `QPs` [S] | `VtEntS` [S] = `VtmEnt`, `pool`, `ub`, `pSg`, `QPs`; **`VtmU` minus `pool` and all of `sl` derived** |
| io slot | native epochs only | also VM epochs: record `IoPremX2` (`iw` [J], `qf` [J], `kd` [P]), start entry `IoPre ∧ Q ∧ QPs` [S], `GlueAt` data [P] |
| everything else | | unchanged |

## [S] justification (Rust: fl4-core `arch/x86_64/objects.rs`, `vcpu.rs`, `layout.rs`, `localvm.rs`, `syscall.rs`)
* `VtxBundle4.ko` — a VCPU is an untyped-retyped `bits::VCPU` object (32 KiB, `create_arch_object`), never in the
  kernel-global area `[ksb, ksb + 304384)` (the ks block, the per-core nodes, the ASID table at `ks::ASID_TABLE`), which
  is not untyped memory. Native: `VFacts.ks` [J].
* `VtxBundle4.la` — slots 8-aligned, TCBs nonzero and 4 KiB aligned, notification / SC words aligned: properties of
  the heap layout that a running guest does not change. Native: `SlJAt.ioLayA`.
* `VtEntS.pool` — the ASID-pool entries (`asid::pool_entry`) are words of untyped-retyped ASID-pool objects, never user
  frames (native: `VFacts.pool` / `tabU`).
* `VtEntS.ent` / `ub` / `pSg` / `qps` — the state facts at a guest-running entry (P1's `BXI` there, every IPC buffer a
  frame-cap page, `PENDING` a word of a VCPU object, the ASID table and pool entries no page-table word); P3 reaches no
  such state (`JExt.vw`), so they are scope, not [J].
* io start entry `IoPre ∧ Q ∧ QPs` — the I/O-port syscall's P1 entry facts at a state where another core runs a guest:
  `IoPre` reads the current thread, its scheduling context, its CSpace walk and the timer tree, none of which a guest
  touches; P3 has no such state.

## [J] justification of the io record
* `IoPremX2.iw` — `IoPre` survives a write of a user word or a VCPU data word: the same fact as `hIw` [J] of
  `InvJ.hufQF_of2` / `SlJStLocStart.ioQ_wr`, at VM-epoch states (user frames and VCPU objects lie outside every object
  `IoPre` reads). Native io records get it from `SlJAt` (`pe` at every bundle state, `slJAt_wrV`).
* `IoPremX2.qf` — the caller's `Q` survives such a write (`IoPremW2B.qf` [J], at `Pre` states instead of bundle states).
* `IoPremX2.kd` [P] — `IoPremW2B.kd` with "at `Pre` states" for "at bundle states".

No sorry / admit / native_decide / bv_decide. No existing statement or file changed except the root import list.
`NtfnLk` (gen 3) is not wired: no vx / vt record field is subsumed by it (`VxPremV2` / `VtPremV2` carry no
notification-lock clause, `VexitEnt.nfar` is about the far-ness of the bound notification's word, not its lock).
-/
import Fl4Proofs.P2.E2EPVX3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW RegionOK LayP TcbSlot)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

/-! ## Part 1: the VM-timer start entry, shrunk -/

section vtS
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`SlotLayV` from the layout**: the VSpace slot words of every TCB lie in its slot 1 (`RegionOKX.tslot`,
`LayP.region_slotW`), at any state. -/
theorem slotLayV_ofLayX {Kl : KLayout} (B : UserLayX L Kl) {T : Set U64} (hTH : ∀ y ∈ T, Kl.heap y = some .tcb)
    (s : S) : SlotLayV Kl st T s := by
  intro y hy k hk
  have hyH := hTH y hy.1
  obtain ⟨hps, hts, -, -, -, -⟩ := B.rx.tslot y hyH 1#u64 (by simp)
  have hf := B.lp.heap.fits y _ hyH
  simp only [HKind.bits] at hf
  have h1 : (1#u64 : U64).val = 1 := by simp
  have hpv : (slotIdx y 1#u64).val = y.val + 32 := by
    rw [slj_slotIdx_val (by rw [h1]; omega), h1]
  have hkv : (core.num.U64.wrapping_add y k).val = y.val + k.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hin : InW (slotIdx y 1#u64) 32 (core.num.U64.wrapping_add y k) := by
    unfold InW; rw [hpv, hkv]; omega
  exact ⟨_, B.lp.region_slotW hps hin, hts, by rw [hpv, hkv]; omega⟩

/-- **`VtmU` from the layout**: the IRQ-state word and the kernel root are ks-block words (`UserLayX.uks`), the ASID
table's words are no user words (`QPs.uoff`); only the pool-entry clause is a state fact. -/
theorem vtmU_ofX {K : KLayoutV} {X : S} (B : UserLayX L K.toKLayout) (hk : L.ksb X = K.ksb) {irq : U64}
    (huo : ∀ b ∈ K.user, ∀ hi : U64, hi.val < 2048 → b ≠ atAF K.ksb hi)
    (hpool : ∀ hi : U64, hi.val < 2048 → ∀ lo : U64, lo.val < 512 → L.mem X (atAF (L.ksb X) hi) ≠ 0#u64 →
      peAF (L.mem X (atAF (L.ksb X) hi)) lo ∉ K.user) : VtmU K st irq X where
  iqU h128 i hi hu := B.uks _ hu i (state_off_lt h128 hi) (by rw [hk])
  krU hu := by
    have e : krA (L := L) X = core.num.U64.wrapping_add K.ksb layout.ks.KERNEL_ROOT := by unfold krA; rw [hk]
    rw [e] at hu
    exact B.uks _ hu _ (by simp [layout.ks.KERNEL_ROOT]) rfl
  tabU hi hhi := ⟨fun hu => huo _ hu hi hhi (by rw [hk]), fun lo hlo hne => hpool hi hhi lo hlo hne⟩

variable (st) in
/-- **The VM-timer start entry** [S] (module docstring): what is left of VX2's six [S] parts. -/
structure VtEntS (K : KLayoutP) (j : VtArg S) (s : S) : Prop where
  /-- [S] lvm's entry facts (`VtmEnt`: the VM-exit entry at the bound VCPU, IRQ / root / ASID words placed). -/
  ent : VtmEnt K.toKLayoutV st j.T j.Cs j.Ω j.H j.Sg j.Rp j.Scs j.Nt j.Z j.Ac j.lk j.irq j.n s
  /-- [S] the ASID-pool entries are no user words. -/
  pool : ∀ hi : U64, hi.val < 2048 → ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
    peAF (L.mem s (atAF (L.ksb s) hi)) lo ∉ K.user
  /-- [S] some user-word set with P1 `UserOK` holding every TCB's IPC-buffer lookup. -/
  ub : ∃ U : Set U64, Fl4Proofs.P1.UserOK st j.T j.Cs j.Ω j.H U s ∧
    ∀ y ∈ j.T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄
  /-- [S] the bound VCPU's `PENDING` is no frame word. -/
  pSg : core.num.U64.wrapping_add (vOf st s) vcpu.PENDING ∉ j.Sg
  /-- [S] the PTE facts at the start state. -/
  qps : QPs K st s

variable {A : Type} {ar : machine.Arch A} {hA : P0.ArchTotal ar} {hm : E2E.MasksWr st}

/-- **The path's `Pre` and `QPs` from `VtEntS`, the epoch's bundle and the memory link.** -/
theorem vtPreA_of_S {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (E : VtxBundle st L K) {j : VtArg S}
    (h : VtPremV2 st j K.toKLayoutV) {m : U64 → U64} {σ : S}
    (hμ : ∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) (e : VtEntS st K j σ) :
    VtPreA st j K.toKLayoutV m σ ∧ QPs K st σ := by
  have hTH : ∀ y ∈ j.T, K.heap y = some .tcb := fun y hy => by rw [h.ix.hT, ← h.ix.hKH] at hy; exact hy
  refine ⟨⟨e.ent, vtmU_ofX E.ul e.qps.ksb (fun b hb hi hhi => e.qps.uoff b (Or.inl hb) hi hhi) e.pool,
    affAg_of_linkP hK hU hμ, e.ub, slotLayV_ofLayX E.ul hTH σ, e.pSg⟩, e.qps⟩

variable (st ar hA hm)

/-- **The VM-timer slot's start fact with `VtEntS`** ([S] entry, `GlueAt` data [P]). -/
def VtStartV4 (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : VtArg S) : Prop :=
  K.vcpus ≠ ∅ ∧ ∃ q0, (∃ h : VtPremV2 st j K.toKLayoutV, ∃ (σ : S) (a : A),
      VtEntS st K j σ ∧ L.cpu σ = c ∧ j.lk σ = hs ∧
      (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
      ∀ E : VtxBundle st L K,
        q0 = ((vtSlotV st ar hA hm).path j K.toKLayoutV m hK.base hU.base (h.toV E)).body σ a) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

variable {st ar hA hm}

/-- **`VtStartV4` and the epoch's bundle give VX2's `VtStartV2`.** -/
theorem vtStartV2_of_V4 {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : VtArg S} (E : VtxBundle st L K) (h : VtStartV4 st ar hA hm K μ hK hU c hs q j) :
    VtStartV2 st ar hA hm K μ hK hU c hs q j := by
  obtain ⟨hne, q0, ⟨hp, σ, a, he, hc, hl, hμ, hq⟩, rfl⟩ := h
  exact ⟨hne, q0, ⟨hp, σ, a, vtPreA_of_S hK hU E hp hμ he, hc, hl, hμ, hq⟩, rfl⟩

end vtS

/-! ## Part 2: the VM-epoch layout facts -/

section bun4
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **The VT-x layout of a VM epoch** [S] (module docstring): `VtxBundle` and two more layout facts the native
slots read (`VcpuKsOff`: no VCPU meets the kernel-global area; `IoLayA`). -/
structure VtxBundle4 (L : LawfulStore st) (K : KLayoutP) : Prop where
  /-- [S] VX2's bundle. -/
  b : VtxBundle st L K
  /-- [S] no VCPU meets `[ksb, ksb + 304384)` (native: `VFacts.ks`). -/
  ko : VcpuKsOff K.toKLayoutV
  /-- [S] the I/O path's layout facts (native: `SlJAt.ioLayA`). -/
  la : IoLayA K.toKLayout

variable {st}

/-- **Consistency**: every P3 bundle state with the VT-x cluster `VFacts` [J] gives `VtxBundle4`. -/
theorem vtxBundle4_of_vfacts {K : KLayoutP} {s : S} (B : SlJAt (L := L) K.toKLayout s)
    (vf : VFacts L K.toKLayoutV) : VtxBundle4 st L K :=
  ⟨vtxBundle_of_vfacts B vf, vf.ks, B.ioLayA⟩

theorem vcpuKs_ofKo {K : KLayoutV} (h : VcpuKsOff K) : VcpuKs K := fun v b hin hb => by
  obtain ⟨hv, h1, h2⟩ := hin
  rcases h v hv with h' | h' <;> omega

end bun4

/-! ## Part 3: the I/O-port slot at any layout -/

section ioF
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutV}

/-- **The current thread survives a user or VCPU-data write** without a P3 bundle (`SlJAt.curW_wr` /
`curW_wrVD`: the node word is no user word by `UserLayX.unode`, and off every VCPU by `VcpuKsOff`). -/
theorem curW_wrX (ul : UserLayX L K.toKLayout) (ko : VcpuKsOff K) {T : Set U64} {s : S}
    (hN : NodePlaced st T s (L.cpu s)) (hk : L.ksb s = K.ksb) (hc : (L.cpu s).val < 64) {b : U64}
    (hb : b ∈ (userV K).user) (hba : Aligned b) (v : U64) : L.curW (L.wr s b v) = L.curW s := by
  have hv := nodeAt_val hN (off := layout.node.CUR_THREAD) (by rw [curth_val]; omega)
  have h0 := curth_val
  unfold LawfulStore.curW
  rw [nodeAt_wr, LawfulStore.cpu_wr]
  refine mem_wr_ne' hba (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) fun e => ?_
  rcases mem_userV.1 hb with hu | ⟨w, hin, -⟩
  · have h := ul.unode b hu (L.cpu s) hc s hk
    rw [e] at h
    omega
  · obtain ⟨hw, h1, h2⟩ := hin
    rw [e] at h1 h2
    simp only [LawfulStore.nodeBase, hk] at hv
    rcases ko w hw with h | h <;> omega

/-- **`IoRS` / `IoWS` / `IoDS` survive a user or VCPU-data write** at an `IoPre` state (`ioRWDS_wrV` without
`SlJAt`). -/
theorem ioRWDS_wrVX (hK : RegionOKV K) (hU : UserOKV K) (ul : UserLayX L K.toKLayout) (ko : VcpuKsOff K)
    {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {Locks : S → U64 → Prop} {s : S}
    (P : IoPre st (userV K) T Cs Ω H Sg Rp Scs Nt Z Ac s) {b : U64} (hb : b ∈ (userV K).user) (hba : Aligned b)
    (v : U64) (hl : Locks (L.wr s b v) = Locks s) :
    IoRS (st := st) (userV K) Locks (L.wr s b v) = IoRS (st := st) (userV K) Locks s ∧
      IoWS (st := st) (userV K) Locks (L.wr s b v) = IoWS (st := st) (userV K) Locks s ∧
      IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  have eo : OwnMap.own (userV K) (L.mem (L.wr s b v)) = OwnMap.own (userV K) (L.mem s) :=
    E2E.ownDep (regionOK_userV hK) (userOK_userV hK hU) _ _
      (fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb)))
  have h0 := P.bxi.1.choose_spec.choose_spec
  have hN := h0.nodes _ h0.cur
  have hc : (L.cpu s).val < 64 := Nat.lt_of_lt_of_le P.nc ul.nc
  have ecur : L.curW (L.wr s b v) = L.curW s := curW_wrX ul ko hN P.kb.symm hc hb hba v
  refine ⟨?_, ?_, ?_⟩ <;> funext w
  · simp only [IoRS, RPerm, GateOnly, eo, hl, LawfulStore.cpu_wr]
  · simp only [IoWS, WPerm, eo, hl, LawfulStore.cpu_wr]
  · simp only [IoDS, ecur, LawfulStore.cpu_wr, nodeAt_wr]

end ioF

section ioS
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The I/O path's `Pre` in VM epochs**: P1's `IoPre` at `userV K`, the map memory's `AFFINITY` agreement and the
caller's `Q` (no P3 bundle). -/
abbrev IoPreX (i : IoArg S) (K : KLayoutV) (m : U64 → U64) (s : S) : Prop :=
  IoPre st (userV K) K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac s ∧
    AffAg st K.toKLayout m s ∧ i.Q K m s

/-- **The I/O-port record at any layout** (module docstring). -/
structure IoPremX (i : IoArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- The user-word layout facts (from the epoch's `VtxBundle`). -/
  ul : UserLayX L K.toKLayout
  /-- No VCPU meets the kernel-global area (from the epoch's `VtxBundle4`). -/
  ko : VcpuKsOff K
  /-- The I/O path's layout facts (from the epoch's `VtxBundle4`). -/
  la : IoLayA K.toKLayout
  /-- [J] `IoPre` survives a user / VCPU-data write at a `Pre` state (`hIw` of `InvJ.hufQF_of2`). -/
  iw : ∀ s b v, IoPreX st i K m s → b ∈ (userV K).user → Aligned b →
    IoPre st (userV K) K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac
      (L.wr s b v)
  /-- [J] the caller's `Q` survives such a write (`IoPremW2B.qf`). -/
  qf : ∀ s b v, IoPreX st i K m s → b ∈ (userV K).user → Aligned b → i.Q K m (L.wr s b v)
  /-- [P] at `Pre` states the locks are determined by the words off `(userV K).user` (`IoPremW2B.kd`). -/
  kd : ∀ s, IoPreX st i K m s → KernDetS (L := L) (userV K).user i.Locks s

variable {st}

theorem IoPremX.huf {i : IoArg S} {K : KLayoutV} {m : U64 → U64} (hK : RegionOKV K) (hU : UserOKV K)
    (h : IoPremX st i K m) : ∀ s b v, IoPreX st i K m s → b ∈ (userV K).user → Aligned b →
      IoPreX st i K m (L.wr s b v) ∧ i.Locks (L.wr s b v) = i.Locks s ∧
        IoRS (st := st) (userV K) i.Locks (L.wr s b v) = IoRS (st := st) (userV K) i.Locks s ∧
        IoWS (st := st) (userV K) i.Locks (L.wr s b v) = IoWS (st := st) (userV K) i.Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  intro s b v hP hb hba
  have hl := hlk_of_kernelDetU (P := IoPreX st i K m) h.kd s b v hP hb hba
  have e := ioRWDS_wrVX hK hU h.ul h.ko hP.1 hb hba v hl
  have haf : AffAg st K.toKLayout m (L.wr s b v) := fun d hd => by
    rw [hP.2.1 d hd]
    exact (wr_nu hba hb v ((userOK_userV hK hU).tcb d hd oAFFINITY (Or.inl rfl))).symm
  exact ⟨⟨h.iw s b v hP hb hba, haf, h.qf s b v hP hb hba⟩, hl, e.1, e.2.1, e.2.2⟩

variable (st)

/-- **The I/O-port slot at any layout** (route U: `io_localPathG2` at `userV K`, `Pre := IoPreX`). -/
def ioSlotX : SlotU (IoArg S) where
  Prem i K m := IoPremX st i K m
  path i K m hK hU h :=
    io_localPathG2 (K := userV K) (m0 := m) (Locks := i.Locks) ar hA (regionOK_userV hK) (userOK_userV hK hU)
      (ioLayA_userV h.la) (number := i.number) hm (P := IoPreX st i K m) (fun s hs => hs.1) (fun s hs => hs.2.1)
      (h.huf hK hU)
  W i K m hK hU h :=
    ⟨fun _ _ _ hr => ioRS_noV hr, fun _ _ hp hw => hw.elim (ioWS_noV hK) fun hd =>
      Or.inl (safeW_noV hK (IoDS.safe hp.1 hd).2)⟩

/-- **The I/O-port path at any layout reads no PTE word under `QPs`** (`io_avoidPJ_path`'s proof with `Pre :=
IoPreX`; it never used `vcpus = ∅`). -/
theorem io_avoidPX_path (i : IoArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (ioSlotX st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) (((ioSlotX st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => hb)) := by
  have pre : ∀ s, IoPreX st i K.toKLayoutV m s →
      IoPre st (userV K.toKLayoutV) K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits i.Ac s :=
    fun s hs => hs.1
  have preP : ∀ s, IoPreX st i K.toKLayoutV m s ∧ QPs K st s →
      IoPre st (userP K) K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits i.Ac s :=
    fun s hs => ioPre_userP hK hs.2.ks (pre s hs.1)
  have hro := io_hro (K := userV K.toKLayoutV) (Locks := i.Locks) (m0 := m) hA (number := i.number)
    (P := IoPreX st i K.toKLayoutV m) pre
  have hex : ∃ p : SProg Bool, IsProg (ioBodyP S i.number) p ∧ NoZero p ∧
      ∀ s s' a r, IoPreX st i K.toKLayoutV m s →
        (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a i.number = ok (true, s1, a1)) →
        PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
          (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' →
        interp st ar p s' a = ok r →
        E2E.Once st ar (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (· ∈ (userV K.toKLayoutV).user) ∅ ∅ p s' a :=
    ⟨_, io_isProg S i.number, io_noZero i.number, hro⟩
  have hIP := io_isProgOn (K := userV K.toKLayoutV) (Locks := i.Locks) (m0 := m) hA
    (P := IoPreX st i K.toKLayoutV m) pre (io_isProg S i.number)
  refine ⟨?_, ?_, ?_⟩
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : IoPreX st i K.toKLayoutV m s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : syscall.handle_ioport_local st ar s a i.number = ok (true, s1, a1) := hr
    have g1 := io_acc hA (Locks := i.Locks) (pre s hs') hr'
    have g2 := io_acc hA (Locks := i.Locks) (preP s ⟨hs', hq⟩) hr'
    have e := fun (st' : machine.Store S) (N : Narrow st st') => hIP st' N s (AltOf.pre hs') a
    have w1 := (interp_guard _ s a _ ((e _ (Narrow.guard _ _ _)).symm.trans g1)).2
    have w2 := (interp_guard _ s a _ ((e _ (Narrow.guard _ _ _)).symm.trans g2)).2
    show syscall.handle_ioport_local
      (guard st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) i.Locks) s)
        (IoWS (st := st) (userV K.toKLayoutV) i.Locks s)) ar s a i.number = ok (true, s1, a1)
    exact (e _ (Narrow.guard _ _ _)).trans (guard_of_within (st := st) (L := L) (ar := ar) _ s a _
      ((e _ (Narrow.self _)).symm.trans hr')
      (Within.mono (fun b hb => ⟨hb.1, fun hq => hb.2.2.1 (Or.inr hq)⟩) (fun b hb => hb.1) _ s a
        (Fl4Proofs.P2.E2E.within_and _ s a w1 w2)))
  · intro s a r hs hr hn s' r' hA' h'
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : IoPreX st i K.toKLayoutV m s := hs1
    have hq : QPs K st s := hs2
    have hAl : PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' := hA'
    have hr' : syscall.handle_ioport_local st ar s a i.number = ok r := hr
    have h'' : syscall.handle_ioport_local st ar s' a i.number = ok r' := h'
    have hn' : r.1 ≠ true := hn
    have g := io_ra_decU hA (Locks := i.Locks) (m0 := m) (preP s ⟨hs', hq⟩) (alt_userP hAl) hr' hn' h''
    have e := fun (st' : machine.Store S) (N : Narrow st st') => hIP st' N s' ⟨s, hs', hAl⟩ a
    show syscall.handle_ioport_local (guard st (fun b => ¬ b ∈ K.ptes) (fun _ => True)) ar s' a i.number = ok r'
    exact (e _ (Narrow.guard _ _ _)).trans (interp_mono (st := st) (fun q hq hp => hq.2 (Or.inr hp))
      (fun _ h => h) _ (io_noZero i.number) s' a r' ((e _ (Narrow.guard _ _ _)).symm.trans g))
  · intro st' N σ g a
    obtain ⟨s, hs, hAc⟩ := g
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : IoPreX st i K.toKLayoutV m s := hs1
    have hq : QPs K st s := hs2
    have hAc' : PathObl.Alt st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) i.Locks) s)
        (OwnMap.cls (userV K.toKLayoutV)) (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s σ := hAc
    have g2 : AltOf st (fun s => IoPreX st i K.toKLayoutV m s ∧ QPs K st s)
        (IoRS (st := st) (userP K) i.Locks) (OwnMap.cls (userP K)) (OwnMap.ko (userP K) m) (· ∈ (userP K).user) σ :=
      ⟨s, ⟨hs', hq⟩, ⟨hAc'.cpu, hAc'.ksb, hAc'.masks,
        fun x hx => hAc'.read x ⟨⟨hx.1, fun hu => hx.2.1 (Or.inl hu), hx.2.2⟩, fun hp => hx.2.1 (Or.inr hp)⟩,
        fun x hx hu hk => hAc'.clsEq x (fun hr => hx ⟨hr.1.1, fun hu' => Or.elim hu' hr.1.2.1 hr.2, hr.1.2.2⟩)
          (fun h => hu (Or.inl h)) hk⟩⟩
    exact io_isProgOn (K := userP K) (Locks := i.Locks) (m0 := m) hA
      (P := fun s => IoPreX st i K.toKLayoutV m s ∧ QPs K st s) preP
      (Classical.choose_spec hex).1 st' N σ g2 a

/-- **The I/O-port slot's family member reads no PTE word under `QPs`** (the empty path where `IoPremX` fails). -/
theorem io_avoidPX (i : IoArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) :
    AvoidP K (((ioSlotX st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  by_cases hp : (ioSlotX st ar hA hm).Prem i K.toKLayoutV m
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
        P = (ioSlotX st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
        AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb)) := by
      rintro P W rfl
      exact avoidE_liftAtV_rJ hK.base _ W (io_avoidPX_path st ar hA hm i K m hK hU hp)
    exact key _ _ (SlotU.fam_pos _ _ hp)
  · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)

/-- **The I/O-port slot under `ownP`**: lifted, restricted to `QPs` states, PTE-cut. -/
def ioSlotPX : PathsP (IoArg S) :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (io_avoidPX st ar hA hm i K m hK hU)

/-- **The I/O-port record without the bundle's fields**: `iw` [J], `qf` [J], `kd` [P]. -/
structure IoPremX2 (i : IoArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [J] -/
  iw : ∀ s b v, IoPreX st i K m s → b ∈ (userV K).user → Aligned b →
    IoPre st (userV K) K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac
      (L.wr s b v)
  /-- [J] -/
  qf : ∀ s b v, IoPreX st i K m s → b ∈ (userV K).user → Aligned b → i.Q K m (L.wr s b v)
  /-- [P] -/
  kd : ∀ s, IoPreX st i K m s → KernDetS (L := L) (userV K).user i.Locks s

variable {st}

theorem IoPremX2.toX {K : KLayoutP} {i : IoArg S} {m : U64 → U64} (h : IoPremX2 st i K.toKLayoutV m)
    (E : VtxBundle4 st L K) : IoPremX st i K.toKLayoutV m :=
  ⟨E.b.ul, E.ko, E.la, h.iw, h.qf, h.kd⟩

variable (st)

/-- **The I/O-port slot's start fact in a VM epoch** (module docstring): the record, a start state with P1's
`IoPre`, the caller's `Q` and `QPs` ([S] entry), its core, locks and memory link ([P], as `GlueAt`), the armed program
the cut of the slot's body there. -/
def IoStartX (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : IoArg S) : Prop :=
  K.vcpus ≠ ∅ ∧ ∃ q0, (∃ h : IoPremX2 st j K.toKLayoutV m, ∃ (σ : S) (a : A),
      (IoPre st K.toKLayout K.heap.tcbs j.Cs j.Ω K.heap j.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits
          j.Ac σ ∧ j.Q K.toKLayoutV m σ ∧ QPs K st σ) ∧
      L.cpu σ = c ∧ j.Locks σ = hs ∧ (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
      ∀ E : VtxBundle4 st L K,
        q0 = (LocalPath.liftV hK.base (LocalPath.atV hK.base
          ((ioSlotX st ar hA hm).path j K.toKLayoutV m hK.base hU.base (h.toX E))
          ((ioSlotX st ar hA hm).W _ _ _ _ _ _)) (noVcpuRd_atV hK.base _ _)).body σ a) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

variable {st ar hA hm}

/-- **`StartAt` of the I/O-port slot** from its start fact and the epoch's bundle. -/
theorem ioStartX_at {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : IoArg S} (E : VtxBundle4 st L K) (h : IoStartX st ar hA hm K μ hK hU c hs q j) :
    StartAt (ioSlotPX st ar hA hm j K μ hK hU) c hs μ q := by
  obtain ⟨-, q0, ⟨hp, σ, a, ⟨hio, hQ, hq⟩, hc, hl, hμ, hb⟩, rfl⟩ := h
  have hpre : IoPreX st j K.toKLayoutV μ σ :=
    ⟨ioPre_userV hK.base (vcpuKs_ofKo E.ko) hio, affAg_of_linkP hK hU hμ, hQ⟩
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) μ) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P)
      (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
        (fun b hb => Or.inl hb))),
      P = (ioSlotX st ar hA hm).path j K.toKLayoutV μ hK.base hU.base (hp.toX E) →
      StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv) c hs μ
        (cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c q0 ∅) := by
    rintro P W hAv rfl
    have e : q0 = (LocalPath.liftV hK.base (LocalPath.atV hK.base
        ((ioSlotX st ar hA hm).path j K.toKLayoutV μ hK.base hU.base (hp.toX E)) W)
        (noVcpuRd_atV hK.base _ W)).body σ a := hb E
    refine ⟨σ, a, ⟨hpre, hq⟩, hc, hl, hμ, ?_⟩
    rw [body_cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv σ a, e, ← hc]
    rfl
  exact key _ _ _ (SlotU.fam_pos _ _ (hp.toX E))

end ioS

/-! ## Part 4: executions whose VM epochs carry `VtxBundle4` -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4 with native and VM epochs, VM exits carrying `VtxBundle4`** (`Fl4StepVX2` with `VtxBundle4`). -/
structure Fl4StepVX4 (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (Ch : S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact. -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ i, SF Ch K s.mem hK hU c (fun l => s.lk l = some c) k i
  /-- The serial exit: native ([P] `SerExitW`, convention) or VM (convention `vcpus ≠ ∅`, `ptes = ptesR`;
  [S] `VtxBundle4`). -/
  ser : SerStep s c → (SerExitW P K'.toKLayoutV Ch' ∧ K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem) ∨
    (K'.vcpus ≠ ∅ ∧ K'.ptes = ptesR K' s'.mem ∧ VtxBundle4 st L K')
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chain change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **An execution of FL4 whose VM epochs carry `VtxBundle4`.** -/
inductive ExecVX4 (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → Prop
  | refl : ExecVX4 LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} :
      ExecVX4 LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepVX4 LP SF P s K Ch c s' K' Ch' →
      ExecVX4 LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {v a x : U64} :
      ExecVX4 LP SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecVX4 LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

/-- The start facts with the epoch's `VtxBundle4` added. -/
def SFaV4 (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι →
    Prop) (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) (i : ι) : Prop :=
  (K.vcpus ≠ ∅ → VtxBundle4 st L K) ∧ SF Ch K m hK hU c hs q i

/-- **An `ExecVX4` is an `ExecVX`** whose start facts carry the epoch's `VtxBundle4`. -/
theorem execVX_of_VX4 {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop}
    (hc0 : K0.vcpus = ∅) (h : ExecVX4 LP SF P s0 K0 Ch0 s K Ch) :
    ExecVX LP (SFaV4 (st := st) SF) P s0 K0 Ch0 s K Ch ∧ (K.vcpus ≠ ∅ → VtxBundle4 st L K) := by
  induction h with
  | refl => exact ⟨.refl, fun hn => (hn hc0).elim⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hV⟩ := ih
    have hst : Fl4StepVX LP (SFaV4 (st := st) SF) P s1 K1 Ch1 c1 s1' K1' Ch1' := by
      refine ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, g.serG, g.keep⟩
      · obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
        exact ⟨i, hV, hi⟩
      · rcases g.ser hs with hN | ⟨hne, he, hb⟩
        · exact Or.inl hN
        · exact Or.inr ⟨hne, hb.b.okP he⟩
    refine ⟨.step hE hS hst, fun hne => ?_⟩
    by_cases hs : SerStep s1 c1
    · rcases g.ser hs with ⟨-, hc, -⟩ | ⟨-, -, hb⟩
      · exact absurd hc hne
      · exact hb
    · obtain ⟨eK, -⟩ := g.keep hs
      subst eK
      exact hV hne
  | @hw s1 K1 Ch1 v a y _ hH ih =>
    obtain ⟨hE, hV⟩ := ih
    exact ⟨.hw hE hH, hV⟩

end exec

/-! ## Part 5: the tops -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The start facts with the VM-exit, VM-timer and VM-epoch I/O-port slots** (VX2's, the VM-timer slot at
`VtStartV4`, the I/O-port slot at `IoStartX`). -/
def StartVX4 {ιN : Type}
    (SFN : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ιN → Prop)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : ((ιN ⊕ VxArg S) ⊕ VtArg S) ⊕ IoArg S → Prop
  | .inl (.inl i) => StartVX2 st ar hA hm SFN Ch K m hK hU c hs q i
  | .inl (.inr j) => VtStartV4 st ar hA hm K m hK hU c hs q j
  | .inr j => IoStartX st ar hA hm K m hK hU c hs q j

/-- **FL4 end to end with native and VM epochs; the VM-exit, VM-timer and I/O-port slots in VM epochs; generic in
the native family** (`serializable_fl4_localVX3G` over `ExecVX4`). -/
theorem serializable_fl4_localVX4G (P : LocPlat st arI AR MR) {ιN : Type} (LN : PathsP ιN)
    {SFN : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ιN → Prop}
    (hSFN : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SFN Ch K s.mem hK hU c hs q i → StartAt (LN i K s.mem hK hU) c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4 (PathsP.sum (PathsP.sum (PathsP.sum LN (vxSlotPV st ar hA hm)) (vtSlotPV st ar hA hm))
        (ioSlotPX st ar hA hm))
      (StartVX4 st ar hA hm SFN) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  have hX := (execVX_of_VX4 hc0.1 h).1
  refine serializable_e2eP _ h0 hA0 hK0 hU0 hM0 (execP_of_VX P ?_ h0 hA0 hB hc0 hM0 hX).1 hq
  intro Ch K s hK hU c hs q i hN hsf
  obtain ⟨hV, hsf⟩ := hsf
  rcases i with ((i | j) | j) | j
  · have hsf' : K.vcpus = ∅ ∧ SFN Ch K s.mem hK hU c hs q i := hsf
    obtain ⟨nv, hsf'⟩ := hsf'
    obtain ⟨hX, hE⟩ := hN nv
    exact hSFN Ch K s hK hU c hs q i hX.chainOf hE hsf'
  · have hsf' : VxStartV2 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact vxStartV_at st ar hA hm (vxStartV_of_V2 (hV (vxStartV2_ne hsf')).b hsf')
  · have hsf' : VtStartV4 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact vtStartV2_at (hV hsf'.1).b (vtStartV2_of_V4 (hV hsf'.1).b hsf')
  · have hsf' : IoStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact ioStartX_at (hV hsf'.1) hsf'

/-- **FL4 end to end with every U1 slot in native epochs and the VM-exit, VM-timer and I/O-port slots in VM epochs**
(module docstring): `serializable_fl4_localVX2` with the VM-timer start entry shrunk to `VtEntS` [S] and the
I/O-port slot `ioSlotPX` added for VM epochs (record `IoPremX2`: `iw` [J], `qf` [J], `kd` [P]; start entry [S]); VM
serial exits carry `VtxBundle4` [S]. No [W]. -/
theorem serializable_fl4_localVX4 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4 (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (fl4LocW11JA st ar hA hm hSt a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA hm) (invSlotU st ar hA hm)) (cmSlotU st ar hA hm)))
        (vxSlotPV st ar hA hm)) (vtSlotPV st ar hA hm)) (ioSlotPX st ar hA hm))
      (StartVX4 st ar hA hm (StartU1 st ar hA hm hSt a0 arI AR MR (StartInvU2 st ar hA hm))) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  refine serializable_fl4_localVX4G st ar hA hm P _ ?_ h0 hA0 hB hc0 hM0 h hq
  intro Ch K s hK hU c hs q i hC hE hsf
  rcases i with i | ((j | j) | j)
  · exact startAt_U st ar hA hm hSt a0 P hIoa hC hE hsf
  · exact delPteStart_at st ar hA hm hC hE hsf
  · exact invStartU2_at st ar hA hm hC hE hsf
  · exact cmStartU2_at st ar hA hm hC hE hsf

end top

end
end Fl4Proofs.P2.E2EP
