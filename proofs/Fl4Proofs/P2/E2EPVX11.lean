/-
# P2 (line vmscope, gen 11): VM fault and VM ReplyRecv in VM epochs — `serializable_fl4_localVX11`

`serializable_fl4_localVX10` (P2/E2EPVX10.lean) runs every U1 slot in native epochs and all of them except vmF (VM
fault, `handle_vm_fault_local`) and vmR (ReplyRecv answering a VM fault, `handle_reply_recv_vm_local`) in VM epochs.
This module adds those two, so **every slot of U1 now starts in both kinds of epoch**.

## Rust check: a VM epoch does not change which branch is accepted
`fastpath_vm::vm_fault` / `reply_recv_vm_found` (fl4-core `fastpath_vm.rs`) and their callers
(`syscall::handle_vm_fault_local` / `handle_reply_recv_vm_local`, fl4-sync `local_vm_fault` / `local_syscall`) decide
on the scheduler action, the fault-handler cap, the endpoint's state and head, the handler's reply object,
`fastpath::schedulable_here` (timer tree, release head, domain, `AFFINITY`, SC, queues), priorities, the reply's
`TCB` / `next`, the faulted thread's state and `fault_type`, and the caller's bound notification. **None reads
`TCB.VCPU` (`vcpu::bound`) or a VCPU object**, and neither writes one; `switch_to` (`set_vm_root`, `activate_thread`)
does not either (`vcpu::cancel_run` is called only from `suspend`). So the handler `dest` (head of an `EP_RECV`
endpoint: blocked on receive) or the replied-to thread `u` (`TS_BLOCKED_ON_REPLY`) may be bound to a VCPU — a VMM
thread taking a native page fault, or a VMM handler — and the run is the same as natively: the bound VCPU is never
looked at. A thread *running* a guest (`TS_RUNNING_VM`, on another core) cannot be `dest` or `u` (wrong state), and
the faulting / replying thread runs natively on this core. Hence the faithful model is the existing extracted
functions at the VM epoch's layout, with VCPU data words counted as user words (`userV K`): the paths read no such
word (`NoVcpuRW` by `ioRS_noV` / `ioWS_noV` / `safeW_noV`, as io's). Neither path reads or writes a PTE word (the
native avoidance proofs never used `vcpus = ∅`), so the slots are route U lifted by `cutLiftP`; no locked-word
`ownP` path (gen 10's trick) is needed.

## What is done (bundle-free, as gens 4–10)
1. **`VmLY`** (store-free layout of the frame lemmas: VX2's `UserLayX`, `RegionOK`, `UserOK`, ASID-table words off
   user words) with `VmLY.nuNode` / `.nuAsid` / **`.vmBase_ag`** / **`.vmFootHyps_ag`** / `.ut_ag` / `.ioRWDS_wr`
   / **`.vmPre_wr`** (jsweep's `vmPre_wrX` without the P3 bundle) and `.curW_wr` / `.lp_wr` / **`.vmRPre_wr`** /
   `.rdTab_wr` / **`.vm_hufR`** (slhuf's `SlJAt.vmRPre_wr` / `vm_hufRK` without the bundle, at `VmRRPre` states).
2. vmF: `VmFIxY` (index convention: canonical sets as natively `BunIxV`, cores below 64 as natively `SlJAtZ.csLt`),
   record **`VmFPremY`** (`ix`, `kd` [P] = U1's `VmFPremB.kd`, `ly`, `la` from the epoch), `VmFPremY.huf`
   (U1's `uf` derived), slot **`vmFSlotY`** (`vm_localPathA` at `userV K`), `vmF_avoidPY_path` (copy of
   `vmF_avoidPJ_pathA`), `vmF_avoidPY`, `vmFSlotPY`; supplied record `VmFPremY2` (`ix`, `kd`), start fact
   **`VmFStartY`**, **`vmFStartY_at`** (`ly` from `VtxBundle4` + `QPs` + the start's node placement:
   `userLayX_userV`, `ksb_fit_of_np`, `QPs.uoff`; `AffAg` by `affAg_of_linkP`).
3. vmR: `rr_pathOblY` (copy of `rr_pathOblA` at `Pre = VmRRPre ∧ AffAg`), **`rr_localPathY`** (P1's `rr_pathSide` /
   `rr_readOnce` / `rr_hro` at `VmRRPre`, no bundle and no `VmFoundC` in `Pre`: the found objects' typing is part of
   `VmRRPre`), `VmRPreY`, record **`VmRPremY`** (`cs` [P] = U1's `VmRPremA.cs`, `kd` [P] at `VmRRPre` states = U1's
   `VmRPremA.kd` read at entry states instead of bundle states, `ly`, `la`), slot **`vmRSlotY`**,
   `vmR_avoidPY_path`, `vmR_avoidPY`, `vmRSlotPY`; `VmRPremY2`, start fact **`VmRStartY`**, **`vmRStartY_at`**.
4. Tops: **`StartVX11`**, **`serializable_fl4_localVX11G`**, **`serializable_fl4_localVX11`** = VX10's family ⊕
   `vmFSlotPY` ⊕ `vmRSlotPY`, glue `ExecVX4`.

## Premise diff vs `serializable_fl4_localVX10`
| where | VX10 | VX11 |
|---|---|---|
| vmF record | native only (`VmFPremB`: `nv`, `bun`, `kd` [P]) | also VM epochs: `VmFPremY2` = `ix` (convention), `kd` [P] (= U1's) |
| vmF start entry | native (`Ch σ ∧ VmFEntJ14`: `yb` [J], `hct`/`lk`/`gl` [P]) | VM epochs: `VmPre (userV K) ∧ QPs` at the start state [S] (`VmFStartY`); `GlueAt` data [P] |
| vmR record | native only (`VmRPremA`: `nv`, `bun`, `cs` [P], `kd` [P] at bundle states) | also VM epochs: `VmRPremY2` = `cs` [P] (= U1's), `kd` [P] at `VmRRPre` states |
| vmR start entry | native (`Ch σ ∧ VmREntU`: `yb` [J], `hct`/`lk`/`nbc` [P], `fd`) | VM epochs: `VmRRPre (userV K) ∧ QPs` at the start state [S] (`VmRStartY`); `GlueAt` data [P] |
| everything else | | unchanged |
No new [J], no [W]. Two new [S] start entries (one per slot, the same shape as io's / st's entry), no new layout [S].

## [S] justification (Rust: fl4-core `fastpath_vm.rs`, `fastpath.rs`, `syscall.rs`, `faults.rs`, `msg.rs`,
`ipc.rs`, `sched.rs`, `vcpu.rs`, `arch/x86_64/objects.rs`; fl4-sync `lib.rs` `local_vm_fault` / `local_syscall`)
* vmF entry `VmPre (userV K) ∧ QPs` — P1's entry facts of `handle_vm_fault_local` (`VmFPre`: `VmBase` = BXI, the
  current thread / SC / node / timer tree, the fault-handler cap names an endpoint, the handler's reply and IPC
  buffer, `AsidOff`; `VmGlue`: fl4-sync's locks on the endpoint and the handler's reply (`local_vm_fault` locks
  `(ptr, 16)` and `(dest.reply_obj, 32)`); `RdTab`) at a state where another core runs a guest. Everything it reads
  is a node / TCB / SC / endpoint / reply / CNode-slot / ks-block / ASID-pool word; a guest writes only its VCPU's
  data words and guest frames (`HwStepP`), and VCPUs are untyped-retyped `bits::VCPU` objects (`other 15`,
  `create_arch_object`), so none of these words is a VCPU word, and the path never reads `TCB.VCPU` (above).
  Natively `VmFEntJ10.pre` from the bundle (with `yb` [J] / `hyt` [J] inside); P3 has no guest-running state
  (`JExt.vw`), so it is scope, not [J].
* vmR entry `VmRRPre (userV K) ∧ QPs` — the same for `handle_reply_recv_vm_local` (`VmRPre`: base, the dispatch
  facts `mid`, the locks on `rptr` / `ep` (`local_syscall` locks `(r, 32)`, `(ep, 16)`), the reply's no-neighbour
  check, typing; plus `rptr` a reply and `ep` an endpoint — `fastpath::reply_caps` returns them from the caller's
  reply / endpoint caps, which name typed objects — and `RdTab`). Natively `VmRRPreJ.pre` from the bundle and
  fl4-sync's `VmFoundC`.
* `QPs` (both): ks block / ASID table / pool entries hold no PTE word and are no user / VCPU-data word — as every
  VM-epoch entry since gen 1.
* `VtxBundle4` and the other slots' entries: unchanged.

## [P]s
`VmFPremY2.kd` (U1's `VmFPremB.kd`, unconditional), `VmRPremY2.cs` (U1's), `VmRPremY2.kd` (U1's `VmRPremA.kd` read
at the entry states: fl4-sync's lock set `{rptr, ep}` comes from `found`, kernel words), `GlueAt` data.

No sorry / admit / native_decide / bv_decide. No existing statement or file changed except the root import list.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `serializable_fl4_localVX11G`,
`serializable_fl4_localVX11`.
-/
import Fl4Proofs.P2.E2EPVX10
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld own oAFFINITY InW RegionOK LayP)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

/-! ## Part 1: the frame lemmas without a P3 bundle -/

section fr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Kl : KLayout} {Cs Ω U Sg Ac : Set U64}

/-- **The store-free layout facts the vmF / vmR frame lemmas read** (module docstring): VX2's `UserLayX`, the
layout's `RegionOK` / `UserOK`, and the ASID-table words are no user words (natively `SlJAt.userAsid`; in VM epochs
`QPs.uoff`). -/
structure VmLY (Kl : KLayout) : Prop where
  ul : UserLayX L Kl
  rok : RegionOK Kl
  uok : E2E.UserOK Kl
  ua : ∀ x ∈ Kl.user, ∀ hi : U64, hi.val < 2048 → x ≠ atAF Kl.ksb hi

/-- A node word of a core below 64 is `NU` (`SlJAt.nuNode64` from `UserLayX.unode`). -/
theorem VmLY.nuNode (B : VmLY (L := L) Kl) {X : S} (hk : L.ksb X = Kl.ksb) {T : Set U64} {c : U64}
    (hc : c.val < 64) (hN : NodePlaced st T X c) {o : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    NU Kl (L.nodeAt X c o) := by
  refine ⟨nodeAt_aligned hN ho h8, fun hu => ?_⟩
  have h := B.ul.unode _ hu c hc X hk
  have v := nodeAt_val hN ho
  rw [v] at h
  omega

/-- An ASID-table word is `NU` (`SlJAt.nuAsid` from `RegionOKX.asidT` and `ua`). -/
theorem VmLY.nuAsid (B : VmLY (L := L) Kl) {X : S} (hk : L.ksb X = Kl.ksb) {hi : U64} (hhi : hi.val < 2048) :
    NU Kl (atAF (L.ksb X) hi) := by
  rw [hk]
  exact ⟨(B.ul.rx.asidT hi hhi).2, fun hu => B.ua _ hu hi hhi rfl⟩

/-- **`VmBase` across an `NU`-agreeing pair** (`vmBase_ag` without the bundle). -/
theorem VmLY.vmBase_ag (B : VmLY (L := L) Kl) {X X' : S} (hCs : ∀ c ∈ Cs, c.val < 64)
    (P : VmBase st Kl Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac X)
    (G : Ag st (NU Kl) X X') :
    VmBase st Kl Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac X' := by
  have hX := B.ul.rx
  have hk : L.ksb X = Kl.ksb := P.kb.symm
  have nd : ∀ {o : U64}, o.val < 4288 → o.val % 8 = 0 → NU Kl (L.nodeAt X (L.cpu X) o) :=
    fun ho h8 => B.nuNode hk (Nat.lt_of_lt_of_le P.nc B.ul.nc) P.np ho h8
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem X' (L.nodeAt X' (L.cpu X') o) = L.mem X (L.nodeAt X (L.cpu X) o) :=
    fun o ho h8 => by rw [G.node]; exact G.m _ (nd ho h8)
  have ecur : L.curW X' = L.curW X := eN _ (by rw [curth_val]; omega) (by rw [curth_val])
  have ecsc : L.cscW X' = L.cscW X := eN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have etm : L.mem X' (tmA (L := L) X') = L.mem X (tmA (L := L) X) :=
    eN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have hcH : Kl.heap (L.curW X) = some .tcb := P.hT _ P.cT
  obtain ⟨⟨Qq, Rq, hq⟩, -, hXI, -, -⟩ := P.bxi
  refine
  { bxi := bxi_userX B.ul hk hCs P.bxi G
    csc := by rw [ecsc]; exact P.csc
    hcsc := ?_
    run := ?_
    lay := P.lay
    kb := by rw [G.k]; exact P.kb
    nc := by rw [G.c]; exact P.nc
    hT := P.hT
    hSc := P.hSc
    curAff := ?_
    cscCore := ?_
    affSc := ?_
    tmc := ?_ }
  · have e : L.mem X' (scA (L.curW X)) = L.mem X (scA (L.curW X)) :=
      G.m _ (nu_tcb hX hcH (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [ecur, ecsc, e]; exact P.hcsc
  · have e : L.mem X' (stA (L.curW X)) = L.mem X (stA (L.curW X)) :=
      G.m _ (nu_tcb hX hcH (o := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val]; omega)
        (by rw [st_val]))
    rw [ecur, e]; exact P.run
  · have e : L.mem X' (affA (L.curW X)) = L.mem X (affA (L.curW X)) :=
      G.m _ (nu_tcb hX hcH (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ecur, G.c, e]; exact P.curAff
  · have e : L.mem X' (scCoreA (L.cscW X)) = L.mem X (scCoreA (L.cscW X)) :=
      G.m _ (nu_scw hX (P.hSc _ P.cscS) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    rw [ecsc, G.c, e]; exact P.cscCore
  · intro t ht h0
    have es : L.mem X' (scA t) = L.mem X (scA t) :=
      G.m _ (nu_tcb hX ht (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [es] at h0 ⊢
    have hsc := (hXI.2.2.bound t ht h0).1
    have ec : L.mem X' (scCoreA (L.mem X (scA t))) = L.mem X (scCoreA (L.mem X (scA t))) :=
      G.m _ (nu_scw hX (P.hSc _ hsc) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    have ea : L.mem X' (affA t) = L.mem X (affA t) :=
      G.m _ (nu_tcb hX ht (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ec, ea]; exact P.affSc t ht h0
  · intro h0
    rw [etm] at h0 ⊢
    have hT := (hXI.2.2.tm.min _ hq.cur).resolve_left h0
    have ed : L.mem X' (tdA (L.mem X (tmA (L := L) X))) = L.mem X (tdA (L.mem X (tmA (L := L) X))) :=
      G.m _ (nu_tcb hX hT (o := 3528#u64) (by simp) (by simp) (by simp))
    have eh : L.mem X' (thA (L.mem X (tmA (L := L) X))) = L.mem X (thA (L.mem X (tmA (L := L) X))) :=
      G.m _ (nu_tcb hX hT (o := 3568#u64) (by simp) (by simp) (by simp))
    rw [ed, eh, G.c]; exact P.tmc h0

/-- **`VmFootHyps` across an `NU`-agreeing pair** (`vmFootHyps_ag` without the bundle). -/
theorem VmLY.vmFootHyps_ag (B : VmLY (L := L) Kl) {X X' : S} (hk : L.ksb X = Kl.ksb)
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (h : VmFootHyps (L := L) Kl.heap.tcbs Cs Ω U Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Ac Kl.heap
      Kl.heap.scBits X)
    (G : Ag st (NU Kl) X X') :
    VmFootHyps (L := L) Kl.heap.tcbs Cs Ω U Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Ac Kl.heap
      Kl.heap.scBits X' := by
  have hX := B.ul.rx
  have hK := B.rok
  have h0 := h.bxi.1.choose_spec.choose_spec
  have hN : NodePlaced st Kl.heap.tcbs X (L.cpu X) := h0.nodes _ h0.cur
  have ecur : L.curW X' = L.curW X := by
    show L.mem X' (L.nodeAt X' (L.cpu X') layout.node.CUR_THREAD) = L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD)
    rw [G.node]
    exact G.m _ (B.nuNode hk (hCs _ h0.cur) hN (by rw [curth_val]; omega) (by rw [curth_val]))
  have hcH : Kl.heap (L.curW X) = some .tcb := h0.curT
  have tw : ∀ y, Kl.heap y = some .tcb → ∀ o : U64, o.val < 4096 → o.val % 8 = 0 →
      L.mem X' (core.num.U64.wrapping_add y o) = L.mem X (core.num.U64.wrapping_add y o) := fun y hy o h1 h2 => by
    have ht' : TcbAddr y := h0.tcbs y hy
    exact G.m _ ⟨field_aligned ht' h1 h2, fun hu => B.ul.userObj hu hy (fun z e => by cases e)
      (by unfold InW; rw [field_val ht' h1]; simp only [HKind.bits]; omega)⟩
  refine ⟨bxi_userX B.ul hk hCs h.bxi G, ?_, ?_, fun b hb => ⟨(h.user b hb).1.ksb G.k, (h.user b hb).2⟩, ?_,
    asidOff_agN (fun hi hhi => B.nuAsid hk hhi) G h.asid⟩
  · have e : L.mem X' (stA (L.curW X)) = L.mem X (stA (L.curW X)) :=
      G.m _ (nu_tcb hX hcH (o := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val]; omega)
        (by rw [st_val]))
    rw [ecur, e]; exact h.nb
  · have hc := h.cap
    obtain ⟨n0, n8⟩ := nu_tslot hK hX hcH (i := layout.tcb.SLOT_FAULT_HANDLER) (by simp [layout.tcb.SLOT_FAULT_HANDLER])
    rw [ecur]
    rw [tcb_slot_val, WP.spec_ok] at hc ⊢
    rw [cap_congr_ag G n0 n8]
    exact hc
  · intro y hy
    have ht' : TcbAddr y := h0.tcbs y hy
    have e1 : L.mem X' (ibA y) = L.mem X (ibA y) := tw y hy 3512#u64 (by simp) (by simp)
    have e2 : L.mem X' (sbA y) = L.mem X (sbA y) := by rw [sbA_field ht']; exact tw y hy 64#u64 (by simp) (by simp)
    have e3 : L.mem X' (core.num.U64.wrapping_add (sbA y) 8#u64) =
        L.mem X (core.num.U64.wrapping_add (sbA y) 8#u64) := by
      rw [sbA8_field ht']; exact tw y hy 72#u64 (by simp) (by simp)
    rw [lookup_buf_agree e1 e2 e3]
    exact h.buf y hy

variable {A : Type} {ar : machine.Arch A}

/-- **The `update_timestamp` commutation** (`ut_agX` without the bundle). -/
theorem VmLY.ut_ag (hA : P0.ArchTotal ar) (B : VmLY (L := L) Kl) {X X' : S} (hk : L.ksb X = Kl.ksb)
    (hc : (L.cpu X).val < 64) {T : Set U64} (hN : NodePlaced st T X (L.cpu X)) (G : Ag st (NU Kl) X X')
    {a a1 : A} {s1' : S} (eu' : sched.update_timestamp st ar X' a = ok (s1', a1)) :
    ∃ s1, sched.update_timestamp st ar X a = ok (s1, a1) ∧ L.ksb s1 = L.ksb X ∧ Ag st (NU Kl) s1 s1' := by
  obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  have eu := update_timestamp_ok ar hN hn
  obtain ⟨ea, G1⟩ := vm_ag_upd nu_al G
    (B.nuNode hk hc hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    (B.nuNode hk hc hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])) eu eu'
  subst ea
  exact ⟨_, eu, utW_ksb X n, G1⟩

variable {Locks : S → U64 → Prop}

/-- **`IoRS`, `IoWS`, `IoDS` are kept by a user-word write** (`ioRWDS_wrX` without the bundle). -/
theorem VmLY.ioRWDS_wr (B : VmLY (L := L) Kl) {X : S} {b : U64} (hb : b ∈ Kl.user) (hba : Aligned b)
    (v : U64) (hl : Locks (L.wr X b v) = Locks X) (ecur : L.curW (L.wr X b v) = L.curW X) :
    IoRS (st := st) Kl Locks (L.wr X b v) = IoRS (st := st) Kl Locks X ∧
      IoWS (st := st) Kl Locks (L.wr X b v) = IoWS (st := st) Kl Locks X ∧
      IoDS (st := st) (L.wr X b v) = IoDS (st := st) X := by
  have eo : own Kl (L.mem (L.wr X b v)) = own Kl (L.mem X) :=
    E2E.ownDep B.rok B.uok _ _ (fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb)))
  refine ⟨?_, ?_, ?_⟩ <;> funext w
  · simp only [IoRS, RPerm, WPerm, GateOnly, eo, hl, LawfulStore.cpu_wr]
  · simp only [IoWS, WPerm, eo, hl, LawfulStore.cpu_wr]
  · simp only [IoDS, ecur, LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]

/-- **`VmPre` and the sets across a user-word write at any `VmPre` state** (jsweep's `vmPre_wrX` without the P3
bundle: canonical sets, `Cs` below 64 cores, the locks kept). -/
theorem VmLY.vmPre_wr (hA : P0.ArchTotal ar) (B : VmLY (L := L) Kl) {X : S} (hCs : ∀ c ∈ Cs, c.val < 64)
    (P : VmPre st ar Kl Kl.heap.tcbs Cs Ω U Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac
      Locks X)
    {b : U64} (hb : b ∈ Kl.user) (hba : Aligned b) (v : U64) (hl : Locks (L.wr X b v) = Locks X) :
    VmPre st ar Kl Kl.heap.tcbs Cs Ω U Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac
      Locks (L.wr X b v) ∧
      IoRS (st := st) Kl Locks (L.wr X b v) = IoRS (st := st) Kl Locks X ∧
      IoWS (st := st) Kl Locks (L.wr X b v) = IoWS (st := st) Kl Locks X ∧
      IoDS (st := st) (L.wr X b v) = IoDS (st := st) X := by
  obtain ⟨F, Gl, Tb⟩ := P
  have Pb := F.base
  have hX := B.ul.rx
  have hk : L.ksb X = Kl.ksb := Pb.kb.symm
  have hc : (L.cpu X).val < 64 := Nat.lt_of_lt_of_le Pb.nc B.ul.nc
  have hN := Pb.np
  have G : Ag st (NU Kl) X (L.wr X b v) := ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun x hx => wr_nu hba hb v hx⟩
  have ecur : L.curW (L.wr X b v) = L.curW X := by
    show L.mem (L.wr X b v) (L.nodeAt (L.wr X b v) (L.cpu (L.wr X b v)) layout.node.CUR_THREAD) =
      L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD)
    rw [G.node]
    exact G.m _ (B.nuNode hk hc hN (by rw [curth_val]; omega) (by rw [curth_val]))
  obtain ⟨eR, eW, eD⟩ := B.ioRWDS_wr (Locks := Locks) hb hba v hl ecur
  have UT : ∀ a s1' a1, sched.update_timestamp st ar (L.wr X b v) a = ok (s1', a1) →
      ∃ s1, sched.update_timestamp st ar X a = ok (s1, a1) ∧ L.ksb s1 = L.ksb X ∧
        Ag st (IoRS (st := st) Kl Locks X) s1 s1' ∧ L.curW s1' = L.curW X ∧ VmDF st Kl Kl.heap.tcbs Locks X s1 ∧
        Ag st (NU Kl) s1 s1' := by
    intro a s1' a1 eu'
    obtain ⟨s1, eu, k1, G1⟩ := B.ut_ag hA hk hc hN G eu'
    have D := vm_dfOf hA F Gl eu
    have G1R : Ag st (IoRS (st := st) Kl Locks X) s1 s1' := ⟨G1.k, G1.c, fun x hx => G1.m x ⟨hx.1, hx.2.1⟩⟩
    have ec : L.curW s1' = L.curW X := by
      show L.mem s1' (L.nodeAt s1' (L.cpu s1') layout.node.CUR_THREAD) = _
      rw [G1R.node, G1R.m _ (D.nd _ (by rw [curth_val]; omega) (by rw [curth_val]))]
      exact D.cur
    exact ⟨s1, eu, k1, G1R, ec, D, G1⟩
  refine ⟨⟨⟨B.vmBase_ag hCs Pb G, ?_, ?_, F.hEp, F.hRp, ?_⟩, ?_, ?_⟩, eR, eW, eD⟩
  · intro a s1' a1 eu'
    obtain ⟨s1, eu, k1, -, -, -, G1⟩ := UT a s1' a1 eu'
    exact B.vmFootHyps_ag (by rw [k1, hk]) hCs (F.hyp a s1 a1 eu) G1
  · intro a s1' a1 ptr badge dest r eu' C'
    obtain ⟨s1, eu, -, G1R, ec, D, -⟩ := UT a s1' a1 eu'
    rw [ec] at C'
    have C := vm_chk_back D G1R C'
    rw [← D.cur] at C
    rw [hl]
    exact F.lk a s1 a1 ptr badge dest r eu C
  · intro a s1' a1 ptr badge dest r eu' C'
    obtain ⟨s1, eu, -, G1R, ec, D, -⟩ := UT a s1' a1 eu'
    rw [ec] at C'
    have C := vm_chk_back D G1R C'
    have hdT : Kl.heap dest = some .tcb := by
      obtain ⟨-, ⟨sl, x, y, g, gr, hS, hcap, -⟩, hep, hh, -⟩ := C
      obtain ⟨-, -, hHT⟩ := D.ep sl ptr badge x y g gr hS hcap
      have hst : L.epState s1 ptr = obj.EP_RECV := by
        rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) s1 ptr)] at hep; exact ok_inj_ff hep
      have hdd : dest = L.mem s1 (epHeadA ptr) := by
        rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) s1 ptr)] at hh; exact (ok_inj_ff hh).symm
      rw [hdd]; exact hHT hst
    rw [← D.cur] at C
    rw [wr_nu (x := yieldA dest) hba hb v (nu_tcb hX hdT (o := 3472#u64) (by simp) (by simp) (by simp))]
    exact F.hyt a s1 a1 ptr badge dest r eu C
  · intro a s1' a1 sl ptr badge x y g gr eu' hsl hcap
    obtain ⟨s1, eu, -, G1R, ec, D, -⟩ := UT a s1' a1 eu'
    rw [ec] at hsl
    obtain ⟨r0, r8⟩ := D.sl sl hsl
    rw [cap_congr_ag G1R r0 r8] at hcap
    rw [hl]
    exact Gl a s1 a1 sl ptr badge x y g gr eu (by rw [D.cur]; exact hsl) hcap
  · rw [eR]
    intro hi hhi
    have ea : L.mem (L.wr X b v) (atAF (L.ksb X) hi) = L.mem X (atAF (L.ksb X) hi) :=
      wr_nu hba hb v (B.nuAsid hk hhi)
    rw [L.ksb_wr, ea]
    exact Tb hi hhi

/-- **The current thread is kept by a user-word write** (`SlJAt.curW_wr` from `UserLayX.unode`). -/
theorem VmLY.curW_wr (B : VmLY (L := L) Kl) {s : S} {T : Set U64} (hN : NodePlaced st T s (L.cpu s))
    (hk : L.ksb s = Kl.ksb) (hc : (L.cpu s).val < 64) {b : U64} (hb : b ∈ Kl.user) (hba : Aligned b) (v : U64) :
    L.curW (L.wr s b v) = L.curW s := by
  have hv := nodeAt_val hN (off := layout.node.CUR_THREAD) (by rw [curth_val]; omega)
  rw [curth_val] at hv
  unfold LawfulStore.curW
  rw [nodeAt_wr, LawfulStore.cpu_wr]
  refine mem_wr_ne' hba (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) fun e => ?_
  have hbv : b.val = L.nodeBase s (L.cpu s) := by rw [e]; omega
  rcases B.ul.unode b hb (L.cpu s) hc s hk with h | h <;> omega

variable (ar) in
/-- **The commuting lemma** (`SlJAt.lp_wr` / VX6's `SlLX.lp_wr` from `VmLY`). -/
theorem VmLY.lp_wr (hA : P0.ArchTotal ar) (B : VmLY (L := L) Kl) {s : S} (hk : L.ksb s = Kl.ksb)
    (hc : (L.cpu s).val < 64) {T : Set U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s))
    (hcT : L.curW s ∈ T) (hcH : Kl.heap (L.curW s) = some .tcb)
    {b : U64} (hb : b ∈ Kl.user) (hba : Aligned b) (v : U64) {a a1 : A} {X' : S}
    (LP' : LocalPre (st := st) ar (L.wr s b v) a (X', a1)) :
    ∃ X, LocalPre (st := st) ar s a (X, a1) ∧ Ag st (NU Kl) X X' := by
  have ecur := B.curW_wr hN hk hc hb hba v
  have hX := B.ul.rx
  obtain ⟨KN, hKN, eKN⟩ := regA_eq (hT _ hcT) (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])
  have hKN' : KN.val = 256 + 8 * layout.reg.NEXT_IP.val := hKN
  have nNx : NU Kl (regA (L.curW s) layout.reg.NEXT_IP) := by
    rw [eKN]
    exact nu_tcb hX hcH (by rw [hKN']; simp [layout.reg.NEXT_IP])
      (by rw [hKN']; simp [layout.reg.NEXT_IP]) (by rw [hKN']; simp [layout.reg.NEXT_IP])
  obtain ⟨X, LP, hag⟩ := lp_alt ar hA (Q := NU Kl) nu_al hT hN hcT (L.ksb_wr _ _ _) (L.cpu_wr _ _ _) ecur
    (fun x hx => mem_wr_ne' hba hx.1 (fun e => hx.2 (e ▸ hb))) nNx
    (B.nuNode hk hc hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    (B.nuNode hk hc hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])) LP'
  have hN' : NodePlaced st T (L.wr s b v) (L.cpu (L.wr s b v)) := by
    rw [L.cpu_wr]; exact NodePlaced.of_ksb (L.ksb_wr _ _ _) hN
  obtain ⟨kX, cX, -⟩ := sl_pre_agree (Cs := ∅) ar hA hT hN hcT LP
  obtain ⟨kX', cX', -⟩ := sl_pre_agree (Cs := ∅) ar hA hT hN' (by rw [ecur]; exact hcT) LP'
  refine ⟨X, LP, ⟨?_, ?_, hag⟩⟩
  · rw [kX', kX, L.ksb_wr]
  · rw [cX', cX, L.cpu_wr]

/-- **`VmRPre` is kept by a user-word write** (slhuf's `SlJAt.vmRPre_wr` without the bundle: canonical sets, `Cs`
below 64 cores, the locks kept, the reply a heap reply). -/
theorem VmLY.vmRPre_wr (hA : P0.ArchTotal ar) (B : VmLY (L := L) Kl) {s : S} (hCs : ∀ c ∈ Cs, c.val < 64)
    {rptr ep : U64}
    (Q : VmRPre st ar Kl Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac
      Locks s rptr ep)
    (hrp : Kl.heap rptr = some .reply) {b : U64} (hb : b ∈ Kl.user) (hba : Aligned b) (v : U64)
    (hl : Locks (L.wr s b v) = Locks s) :
    VmRPre st ar Kl Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac
      Locks (L.wr s b v) rptr ep := by
  have P := Q.base
  have hX := B.ul.rx
  have hk : L.ksb s = Kl.ksb := P.kb.symm
  have hc : (L.cpu s).val < 64 := Nat.lt_of_lt_of_le P.nc B.ul.nc
  have ecur := B.curW_wr P.np hk hc hb hba v
  have Gw : Ag st (NU Kl) s (L.wr s b v) := ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun x hx => wr_nu hba hb v hx⟩
  have hcH : Kl.heap (L.curW s) = some .tcb := P.hT _ P.cT
  obtain ⟨⟨Qq, Rq, hq⟩, -, hXI, -, -⟩ := P.bxi
  refine
  { base := B.vmBase_ag hCs P Gw
    mid := ?_
    lk := by rw [hl]; exact Q.lk
    nb := ?_
    hEp := Q.hEp
    hRp := Q.hRp
    hNt := Q.hNt
    nbt := ?_ }
  · intro a X' a2 LP'
    obtain ⟨X, LP, G⟩ := B.lp_wr ar hA hk hc P.tp P.np P.cT hcH hb hba v LP'
    obtain ⟨kX, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA P.tp P.np P.cT LP
    obtain ⟨hI, hAs, hP⟩ := Q.mid a X a2 LP
    have hnd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → NU Kl (L.nodeAt X (L.cpu X) o) :=
      fun o h1 h2 => by rw [cX, nodeAt_of_ksb kX]; exact B.nuNode hk hc P.np h1 h2
    have D : RrDR (L := L) (NU Kl) X (L.curW s) rptr ep := by
      obtain ⟨t, nx, s1, et, enx, e1, eu⟩ := LP
      rw [cur_thread_ok] at et
      obtain rfl := ok_inj_ff et
      rw [set_reg_ok'] at e1
      obtain rfl := ok_inj_ff e1
      have hN1 : NodePlaced st Kl.heap.tcbs
          (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64))
          (L.cpu (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64))) := by
        rw [LawfulStore.cpu_wr]; exact P.np.wr
      obtain ⟨⟨n0, a3⟩, hn, -⟩ := spec_ex_fd (hA.now a)
      rw [update_timestamp_ok ar hN1 hn] at eu
      have eX : X = rrX (L := L) s (core.num.U64.wrapping_sub nx 2#u64) n0 :=
        (Prod.mk.inj (ok_inj_ff eu)).1.symm
      subst eX
      exact (rr_dr Q hrp Q.hEp _ n0).alt ⟨rfl, rfl, fun _ _ => rfl⟩ (fun x hx => ⟨hx.1, hx.2.1⟩)
    refine ⟨bxi_userX B.ul (kX.trans hk) hCs hI G,
      asidOff_agN (fun hi hhi => B.nuAsid (kX.trans hk) hhi) G hAs, fun u usc C' => ?_⟩
    rw [ecur] at C' ⊢
    have C := rr_chk_backG D G C'
    obtain ⟨Pl, hy⟩ := hP u usc C
    refine ⟨rrPl_ag hX hnd hrp Q.hEp hI G Pl, ?_⟩
    rw [G.m (yieldA u) (nu_tcb hX Pl.hu (o := 3472#u64) (by simp) (by simp) (by simp))]
    exact hy
  · rw [wr_nu (x := rPrevA rptr) hba hb v (nu_rp hX hrp (o := layout.reply.PREV) (by simp [layout.reply.PREV])
        (by simp [layout.reply.PREV])),
      wr_nu (x := rNextA rptr) hba hb v (nu_rp hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT])
        (by simp [layout.reply.NEXT]))]
    exact Q.nb
  · have eb : L.mem (L.wr s b v) (boundA (L.curW s)) = L.mem s (boundA (L.curW s)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := 3368#u64) (by simp) (by simp) (by simp))
    rw [ecur, eb]
    intro h0
    have hn : L.mem s (boundA (L.curW s)) ∈ Kl.heap.ntfns := hXI.2.2.bnd _ hcH h0
    obtain ⟨r, -, a⟩ := hX.ntW _ hn 24#u64 (by simp) (by simp)
    have hnu : NU Kl (core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) 24#u64) :=
      nu_of_region hX a (by rw [r]; intro h; cases h)
    rw [wr_nu (x := fld (L.mem s (boundA (L.curW s))) 24#u64) hba hb v hnu]
    exact Q.nbt h0

/-- **`RdTab` is kept by a user-word write** (the ASID-table words are `NU`). -/
theorem VmLY.rdTab_wr (B : VmLY (L := L) Kl) {s : S} (hk : L.ksb s = Kl.ksb) {b : U64} (hb : b ∈ Kl.user)
    (hba : Aligned b) (v : U64) (e : IoRS (st := st) Kl Locks (L.wr s b v) = IoRS (st := st) Kl Locks s)
    (h : RdTab (L := L) (IoRS (st := st) Kl Locks s) s) :
    RdTab (L := L) (IoRS (st := st) Kl Locks (L.wr s b v)) (L.wr s b v) := by
  rw [e]
  intro hi hhi
  have ea : L.mem (L.wr s b v) (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) :=
    wr_nu hba hb v (B.nuAsid hk hhi)
  rw [L.ksb_wr, ea]
  exact h hi hhi

/-- **`huf` of the VM ReplyRecv path at `VmRRPre` states** (slhuf's `vm_hufRK` without the bundle and without
`VmFoundC`: the found objects' typing is part of `VmRRPre`). -/
theorem VmLY.vm_hufR (hA : P0.ArchTotal ar) (B : VmLY (L := L) Kl) (hCs : ∀ c ∈ Cs, c.val < 64) {rptr ep : U64}
    (hlk : ∀ s b v, VmRRPre st ar Kl Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns
      Kl.heap.scBits Ac Locks rptr ep s → b ∈ Kl.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    ∀ s b v, VmRRPre st ar Kl Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns
        Kl.heap.scBits Ac Locks rptr ep s → b ∈ Kl.user → Aligned b →
      VmRRPre st ar Kl Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns
          Kl.heap.scBits Ac Locks rptr ep (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) Kl Locks (L.wr s b v) = IoRS (st := st) Kl Locks s ∧
        IoWS (st := st) Kl Locks (L.wr s b v) = IoWS (st := st) Kl Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := fun s b v hE hb hba => by
  have hl := hlk s b v hE hb hba
  obtain ⟨hV, hrp, hep, hT⟩ := hE
  have hk : L.ksb s = Kl.ksb := hV.base.kb.symm
  have hc : (L.cpu s).val < 64 := Nat.lt_of_lt_of_le hV.base.nc B.ul.nc
  have ecur := B.curW_wr hV.base.np hk hc hb hba v
  obtain ⟨eR, eW, eD⟩ := B.ioRWDS_wr (Locks := Locks) hb hba v hl ecur
  exact ⟨⟨B.vmRPre_wr hA hCs hV hrp hb hba v hl, hrp, hep, B.rdTab_wr hk hb hba v eR hT⟩, hl, eR, eW, eD⟩

end fr

/-! ## Part 2: the VM ReplyRecv path at `Pre = VmRRPre ∧ AffAg` -/

section vmr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`PathObl` of the VM ReplyRecv path at `VmRRPre ∧ AffAg`** (`rr_pathOblA` without the bundle). -/
theorem rr_pathOblY (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K) (hLA : IoLayA K)
    {rptr ep : U64} {p : SProg Bool}
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_reply_recv_vm_local m ar x a (rptr, ep) = interp m ar p x a) :
    PathObl st (fun m s a => syscall.handle_reply_recv_vm_local m ar s a (rptr, ep)) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks
      (fun s => VmRRPre st ar K K.heap.tcbs Cs Ω K.heap Sg (Heap.replies K.heap) K.heap.scs K.heap.ntfns
        K.heap.scBits Ac Locks rptr ep s ∧ AffAg st K m0 s)
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE' h hb
    have hE := hE'.1
    subst hb
    exact rr_vm_acc hA hE.1 hE.2.2.2 h
  · intro s a r hE' h hn s' r' Al h'
    exact rr_dec_alt hA hK hLA hE'.1 h hn Al h'
  · intro s x _ hx _; exact hx.2.2
  · intro s x hE' hx _
    have hE := hE'.1
    rcases hx with hx | hx
    · exact hx.2
    · rcases hx with rfl | rfl | rfl
      · exact (hE.1.base.reg (Locks := Locks) (by simp [layout.reg.FAULT_IP])).2.2
      · exact (hE.1.base.nd (Locks := Locks) _ (by simp [layout.node.CUR_TIME])
          (by simp [layout.node.CUR_TIME])).2.2
      · exact (hE.1.base.nd (Locks := Locks) _ (by simp [layout.node.CONSUMED])
          (by simp [layout.node.CONSUMED])).2.2
  · intro s x hE' hx
    have hE := hE'.1
    rcases hx with hx | hx
    · exact hx.1
    · exact (hE.1.base.dsSafe hx).1
  · rintro s a ⟨b, s1, a1⟩ hE' h
    have hE := hE'.1
    cases b
    · exact (rr_dec_alt hA hK hLA hE h Bool.false_ne_true (Alt.refl s) h).2.2
    · exact rr_move hA hK hU hE.1 hE.2.2.2 hE'.2 hp h

variable (ar) in
/-- **The VM ReplyRecv local path with no P3 bundle** (module docstring): `Pre = VmRRPre ∧ AffAg`; `PathSide` /
`ReadOnce` by P1's `rr_pathSide` / `rr_readOnce` / `rr_hro` at `VmRRPre`, `huf` a premise. -/
noncomputable def rr_localPathY (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hLA : IoLayA K) {rptr ep : U64} (hm : E2E.MasksWr st)
    (huf : ∀ s b v, VmRRPre st ar K K.heap.tcbs Cs Ω K.heap Sg (Heap.replies K.heap) K.heap.scs K.heap.ntfns
        K.heap.scBits Ac Locks rptr ep s → b ∈ K.user → Aligned b →
      VmRRPre st ar K K.heap.tcbs Cs Ω K.heap Sg (Heap.replies K.heap) K.heap.scs K.heap.ntfns
          K.heap.scBits Ac Locks rptr ep (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := rrBody S rptr ep
  p := R.syscall.handle_reply_recv_vm_local (rptr, ep)
  Acc := fun b => b = true
  Locks := Locks
  Pre := fun s => VmRRPre st ar K K.heap.tcbs Cs Ω K.heap Sg (Heap.replies K.heap) K.heap.scs K.heap.ntfns
    K.heap.scBits Ac Locks rptr ep s ∧ AffAg st K m0 s
  RS := IoRS (st := st) K Locks
  WS := IoWS (st := st) K Locks
  DS := IoDS (st := st)
  isProg := IsProg.on (rr_isProg S rptr ep) _ _ _
  obl := rr_pathOblY hA hK hU hLA (fun mm x a => congrFun (congrFun (rr_isProg S rptr ep A ar mm) x) a)
  side := (rr_pathSide (m0 := m0) hA hK hLA (fun mm x a => congrFun (congrFun (rr_isProg S rptr ep A ar mm) x) a)
    (rr_noZero rptr ep) hm huf).restrA
    (fun _ _ _ _ hq hb ha => affAg_wr hU hq hb ha)
  once := fun s s' a r h => rr_readOnce (m0 := m0) hA hK hLA
    (fun mm x a => congrFun (congrFun (rr_isProg S rptr ep A ar mm) x) a) (rr_noZero rptr ep) hm
    (rr_hro hA) s s' a r h.1
  total := fun s a => rr_total hA (rptr, ep) s a
  masks := hm

end vmr

/-! ## Part 3: the two slots at any layout -/

section slots
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **vmF's index convention** (natively `BunIxV`'s canonical sets and `SlJAtZ.csLt`). -/
structure VmFIxY (i : VmFArg S) (K : KLayoutV) : Prop where
  hT : i.T = K.heap.tcbs
  hH : i.H = K.heap
  hRp : i.Rp = K.heap.replies
  hScs : i.Scs = K.heap.scs
  hNt : i.Nt = K.heap.ntfns
  hZ : i.Z = K.heap.scBits
  hCs : ∀ c ∈ i.Cs, c.val < 64

/-- **vmF's record at any layout** (module docstring): convention, `kd` [P], and layout facts from the epoch. -/
structure VmFPremY (i : VmFArg S) (K : KLayoutV) : Prop where
  /-- Index convention. -/
  ix : VmFIxY i K
  /-- [P] the locks are determined by the core, the kernel base and the words off `(userV K).user` (U1's
  `VmFPremB.kd`). -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.Locks s
  /-- Layout facts at `userV K` (from the epoch's `VtxBundle4` and `QPs`). -/
  ly : VmLY (L := L) (userV K)
  /-- The I/O path's layout facts (from the epoch's `VtxBundle4`). -/
  la : IoLayA K.toKLayout

variable {st ar} in
/-- **U1's `VmFPremA.uf` at any layout** (`VmLY.vmPre_wr`, the locks by `kd`). -/
theorem VmFPremY.huf {i : VmFArg S} {K : KLayoutV} (hA : P0.ArchTotal ar) (h : VmFPremY st i K) :
    ∀ s b v, VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s →
      b ∈ (userV K).user → Aligned b →
      VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks (L.wr s b v) ∧
        i.Locks (L.wr s b v) = i.Locks s ∧
        IoRS (st := st) (userV K) i.Locks (L.wr s b v) = IoRS (st := st) (userV K) i.Locks s ∧
        IoWS (st := st) (userV K) i.Locks (L.wr s b v) = IoWS (st := st) (userV K) i.Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  intro s b v hP hb hba
  have hl : i.Locks (L.wr s b v) = i.Locks s := hlk_of_lkDetS (h.kd s) hb hba v rfl
  obtain ⟨hT, hH, hRp, hScs, hNt, hZ, hCs⟩ := h.ix
  rw [hT, hRp, hScs, hNt, hZ, hH] at hP ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h.ly.vmPre_wr hA hCs hP hb hba v hl
  exact ⟨h1, hl, h2, h3, h4⟩

/-- **The VM-fault slot at any layout** (route U: `vm_localPathA` at `userV K`). -/
def vmFSlotY : SlotU (VmFArg S) where
  Prem i K _ := VmFPremY st i K
  path i K m hK hU h :=
    vm_localPathA (T := i.T) (Cs := i.Cs) (Ω := i.Ω) (U := i.U) (H := i.H) (Sg := i.Sg) (Rp := i.Rp)
      (Scs := i.Scs) (Nt := i.Nt) (Z := i.Z) (Ac := i.Ac) (Locks := i.Locks) (m0 := m)
      ar hA (regionOK_userV hK) (userOK_userV hK hU) (ioLayA_userV h.la) (addr := i.addr) (code := i.code) hm
      (h.huf hA)
  W i K m hK hU h :=
    ⟨fun _ _ _ hr => ioRS_noV hr, fun _ _ hp hw => hw.elim (ioWS_noV hK) fun hd =>
      Or.inl (safeW_noV hK (hp.1.1.base.dsSafe hd).2)⟩

/-- **vmR's `Pre` part** (canonical sets at `userV K`). -/
abbrev VmRPreY (i : VmRArg S) (K : KLayoutV) (s : S) : Prop :=
  VmRRPre st ar (userV K) K.heap.tcbs i.Cs i.Ω K.heap i.Sg (Heap.replies K.heap) K.heap.scs K.heap.ntfns
    K.heap.scBits i.Ac i.Locks i.rptr i.ep s

/-- **vmR's record at any layout** (module docstring). -/
structure VmRPremY (i : VmRArg S) (K : KLayoutV) : Prop where
  /-- [P] the glue's core set is below 64 (U1's `VmRPremA.cs`). -/
  cs : ∀ c ∈ i.Cs, c.val < 64
  /-- [P] at entry states the locks are determined by the words off `(userV K).user` (U1's `VmRPremA.kd`, read at
  `VmRRPre` states instead of bundle states). -/
  kd : ∀ s, VmRPreY st ar i K s → KernDetS (L := L) (userV K).user i.Locks s
  /-- Layout facts at `userV K` (from the epoch's `VtxBundle4` and `QPs`). -/
  ly : VmLY (L := L) (userV K)
  /-- The I/O path's layout facts (from the epoch's `VtxBundle4`). -/
  la : IoLayA K.toKLayout

/-- **The VM ReplyRecv slot at any layout** (route U: `rr_localPathY` at `userV K`). -/
def vmRSlotY : SlotU (VmRArg S) where
  Prem i K _ := VmRPremY st ar i K
  path i K m hK hU h :=
    rr_localPathY (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Ac := i.Ac) (Locks := i.Locks) (m0 := m)
      ar hA (regionOK_userV hK) (userOK_userV hK hU) (ioLayA_userV h.la) (rptr := i.rptr) (ep := i.ep) hm
      (h.ly.vm_hufR hA h.cs (hlk_of_kernelDetU (P := VmRPreY st ar i K) h.kd))
  W i K m hK hU h :=
    ⟨fun _ _ _ hr => ioRS_noV hr, fun _ _ hp hw => hw.elim (ioWS_noV hK) fun hd =>
      Or.inl (safeW_noV hK (hp.1.1.base.dsSafe hd).2)⟩

end slots

/-! ## Part 4: PTE avoidance under `QPs` and the `ownP` slots -/

section av
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The VM-fault path at any layout reads no PTE word under `QPs`** (`vmF_avoidPJ_pathA`'s proof). -/
theorem vmF_avoidPY_path (i : VmFArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vmFSlotY st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) (((vmFSlotY st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => hb)) := by
  have eP : ∀ (a : A) (mm : machine.Store S) (x : S), syscall.handle_vm_fault_local mm ar x a i.addr i.code =
      interp mm ar (R.syscall.handle_vm_fault_local i.addr i.code) x a :=
    fun a mm x => congrFun (congrFun (vm_isProg S i.addr i.code A ar mm) x) a
  have hla : IoLayA (userV K.toKLayoutV) := ioLayA_userV h.la
  refine ⟨?_, ?_, IsProg.on (vm_isProg S i.addr i.code) _ _ _⟩
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VmPre st ar (userV K.toKLayoutV) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s := hs1.1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : syscall.handle_vm_fault_local st ar s a i.addr i.code = ok (true, s1, a1) := hr
    have g1 := vm_acc (Locks := i.Locks) hA hs'.1 hs'.2.2 hr'
    have g2 := vm_acc (Locks := i.Locks) hA (vmFPre_userP hK hq.ks hs'.1) (rdTab_userP hs'.2.2 hq.tab) hr'
    have w1 := (interp_guard _ s a _ ((eP a _ s).symm.trans g1)).2
    have w2 := (interp_guard _ s a _ ((eP a _ s).symm.trans g2)).2
    show syscall.handle_vm_fault_local
      (guard st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) i.Locks) s)
        (IoWS (st := st) (userV K.toKLayoutV) i.Locks s)) ar s a i.addr i.code = ok (true, s1, a1)
    exact (eP a _ s).trans (guard_of_within (st := st) (L := L) (ar := ar) _ s a _ ((eP a st s).symm.trans hr')
      (Within.mono (fun b hb => ⟨hb.1, fun hq => hb.2.2.1 (Or.inr hq)⟩) (fun b hb => hb.1) _ s a
        (Fl4Proofs.P2.E2E.within_and _ s a w1 w2)))
  · intro s a r hs hr hn s' r' hA' h'
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VmPre st ar (userV K.toKLayoutV) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s := hs1.1
    have hq : QPs K st s := hs2
    have hAl : PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' := hA'
    have hr' : syscall.handle_vm_fault_local st ar s a i.addr i.code = ok r := hr
    have h'' : syscall.handle_vm_fault_local st ar s' a i.addr i.code = ok r' := h'
    have hP := vmFPre_userP hK hq.ks hs'.1
    have hn0 : r.1 ≠ true := hn
    have hn' : r'.1 ≠ true :=
      (vm_dec_alt (m0 := m) hA (regionOK_userV hK.base) hla hs'.1 hs'.2.1 hr' hn0 hAl h'').1
    have hg := vm_dec_tr hA hP hs'.2.1 (ag_userP hAl)
      (R'' := fun b => IoRS (st := st) (userP K) i.Locks s b ∨ VmRep st ar s a b) (fun b hb => Or.inl hb)
      (fun s1 a1 sl ptr badge x y g gr eu hsl hcap hst hne =>
        Or.inr ⟨s1, a1, sl, ptr, badge, x, y, g, gr, eu, hsl, hcap, hst, hne, rfl⟩) h'' hn'
    show syscall.handle_vm_fault_local (guard st (fun b => ¬ b ∈ K.ptes) (fun _ => True)) ar s' a i.addr i.code
      = ok r'
    exact (eP a _ s').trans (interp_mono (st := st)
      (fun q hq => Or.elim hq (fun h1 => (ioRS_of_userP h1).2) (fun h2 => VmRep.notPte hA hK hP hs'.2.1 h2))
      (fun _ _ => trivial) _ (vm_noZero i.addr i.code) s' a r' ((eP a _ s').symm.trans hg))

/-- **The VM ReplyRecv path at any layout reads no PTE word under `QPs`** (`vmR_avoidPJ_pathA`'s proof; the
found objects' typing from `VmRRPre` itself). -/
theorem vmR_avoidPY_path (i : VmRArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vmRSlotY st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) (((vmRSlotY st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => hb)) := by
  have eP : ∀ (a : A) (mm : machine.Store S) (x : S), syscall.handle_reply_recv_vm_local mm ar x a (i.rptr, i.ep) =
      interp mm ar (R.syscall.handle_reply_recv_vm_local (i.rptr, i.ep)) x a :=
    fun a mm x => congrFun (congrFun (rr_isProg S i.rptr i.ep A ar mm) x) a
  have hla : IoLayA (userV K.toKLayoutV) := ioLayA_userV h.la
  refine ⟨?_, ?_, IsProg.on (rr_isProg S i.rptr i.ep) _ _ _⟩
  · intro s a r hs hr hb
    have hE : VmRPreY st ar i K.toKLayoutV s := hs.1.1
    have hq : QPs K st s := hs.2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : syscall.handle_reply_recv_vm_local st ar s a (i.rptr, i.ep) = ok (true, s1, a1) := hr
    have g1 := rr_vm_acc (Locks := i.Locks) hA hE.1 hE.2.2.2 hr'
    have g2 := rr_vm_acc (Locks := i.Locks) hA (vmRPre_userP hK hq.ks hE.1)
      (rdTab_userP hE.2.2.2 hq.tab) hr'
    have w1 := (interp_guard _ s a _ ((eP a _ s).symm.trans g1)).2
    have w2 := (interp_guard _ s a _ ((eP a _ s).symm.trans g2)).2
    show syscall.handle_reply_recv_vm_local
      (guard st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) i.Locks) s)
        (IoWS (st := st) (userV K.toKLayoutV) i.Locks s)) ar s a (i.rptr, i.ep) = ok (true, s1, a1)
    exact (eP a _ s).trans (guard_of_within (st := st) (L := L) (ar := ar) _ s a _ ((eP a st s).symm.trans hr')
      (Within.mono (fun b hb => ⟨hb.1, fun hq => hb.2.2.1 (Or.inr hq)⟩) (fun b hb => hb.1) _ s a
        (Fl4Proofs.P2.E2E.within_and _ s a w1 w2)))
  · intro s a r hs hr hn s' r' hA' h'
    have hE : VmRPreY st ar i K.toKLayoutV s := hs.1.1
    have hq : QPs K st s := hs.2
    have hAl : PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' := hA'
    have hr' : syscall.handle_reply_recv_vm_local st ar s a (i.rptr, i.ep) = ok r := hr
    have h'' : syscall.handle_reply_recv_vm_local st ar s' a (i.rptr, i.ep) = ok r' := h'
    have hEP : VmRRPre st ar (userP K) (userV K.toKLayoutV).heap.tcbs i.Cs i.Ω K.heap i.Sg (Heap.replies K.heap)
        (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits i.Ac i.Locks
        i.rptr i.ep s :=
      ⟨vmRPre_userP hK hq.ks hE.1, hE.2.1, hE.2.2.1, rdTab_userP hE.2.2.2 hq.tab⟩
    have hn0 : r.1 ≠ true := hn
    have hn' : r'.1 ≠ true :=
      (rr_dec_alt (m0 := m) hA (regionOK_userV hK.base) hla hE hr' hn0 hAl h'').1
    have hg := rr_dec_tr hA hEP (ag_userP hAl)
      (R'' := fun b => IoRS (st := st) (userP K) i.Locks s b ∨ RrRep st i.rptr s b) (fun b hb => Or.inl hb)
      (fun b hb => Or.inr hb) h'' hn'
    show syscall.handle_reply_recv_vm_local (guard st (fun b => ¬ b ∈ K.ptes) (fun _ => True)) ar s' a
      (i.rptr, i.ep) = ok r'
    exact (eP a _ s').trans (interp_mono (st := st)
      (fun q hq => Or.elim hq (fun h1 => (ioRS_of_userP h1).2) (fun h2 => RrRep.notPte hK hEP.1.base hE.2.1 h2))
      (fun _ _ => trivial) _ (rr_noZero i.rptr i.ep) s' a r' ((eP a _ s').symm.trans hg))

/-- **The VM-fault slot's family member reads no PTE word under `QPs`** (the empty path where `VmFPremY` fails). -/
theorem vmF_avoidPY (i : VmFArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) :
    AvoidP K (((vmFSlotY st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  by_cases hp : (vmFSlotY st ar hA hm).Prem i K.toKLayoutV m
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
        P = (vmFSlotY st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
        AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb)) := by
      rintro P W rfl
      exact avoidE_liftAtV_rJ hK.base _ W (vmF_avoidPY_path st ar hA hm i K m hK hU hp)
    exact key _ _ (SlotU.fam_pos _ _ hp)
  · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)

/-- **The VM ReplyRecv slot's family member reads no PTE word under `QPs`.** -/
theorem vmR_avoidPY (i : VmRArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) :
    AvoidP K (((vmRSlotY st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  by_cases hp : (vmRSlotY st ar hA hm).Prem i K.toKLayoutV m
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
        P = (vmRSlotY st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
        AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb)) := by
      rintro P W rfl
      exact avoidE_liftAtV_rJ hK.base _ W (vmR_avoidPY_path st ar hA hm i K m hK hU hp)
    exact key _ _ (SlotU.fam_pos _ _ hp)
  · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)

/-- **The VM-fault slot under `ownP`**: lifted, restricted to `QPs` states, PTE-cut. -/
def vmFSlotPY : PathsP (VmFArg S) :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (vmF_avoidPY st ar hA hm i K m hK hU)

/-- **The VM ReplyRecv slot under `ownP`**: lifted, restricted to `QPs` states, PTE-cut. -/
def vmRSlotPY : PathsP (VmRArg S) :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (vmR_avoidPY st ar hA hm i K m hK hU)

end av

/-! ## Part 5: the start facts in VM epochs -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **vmF's supplied record**: the index convention and U1's `kd` [P]. -/
structure VmFPremY2 (i : VmFArg S) (K : KLayoutV) : Prop where
  ix : VmFIxY i K
  /-- [P] U1's `VmFPremB.kd`. -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.Locks s

/-- **vmR's supplied record**: U1's `cs` [P] and `kd` [P] at entry states. -/
structure VmRPremY2 (i : VmRArg S) (K : KLayoutV) : Prop where
  /-- [P] U1's `VmRPremA.cs`. -/
  cs : ∀ c ∈ i.Cs, c.val < 64
  /-- [P] U1's `VmRPremA.kd` at `VmRRPre` states. -/
  kd : ∀ s, VmRPreY st ar i K s → KernDetS (L := L) (userV K).user i.Locks s

/-- **The VM-fault slot's start fact in a VM epoch** (module docstring): the record, a start state with P1's
`VmPre` at `userV K` and `QPs` ([S] entry), `GlueAt` data [P], the armed program the cut of the lifted slot's body. -/
def VmFStartY (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : VmFArg S) : Prop :=
  K.vcpus ≠ ∅ ∧ ∃ q0, (∃ _h : VmFPremY2 st j K.toKLayoutV, ∃ (σ : S) (a : A),
      (VmPre st ar (userV K.toKLayoutV) j.T j.Cs j.Ω j.U j.H j.Sg j.Rp j.Scs j.Nt j.Z j.Ac j.Locks σ ∧
        QPs K st σ) ∧
      L.cpu σ = c ∧ j.Locks σ = hs ∧ (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
      ∀ h' : VmFPremY st j K.toKLayoutV,
        q0 = (LocalPath.liftV hK.base (LocalPath.atV hK.base
          ((vmFSlotY st ar hA hm).path j K.toKLayoutV m hK.base hU.base h')
          ((vmFSlotY st ar hA hm).W _ _ _ _ _ _)) (noVcpuRd_atV hK.base _ _)).body σ a) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

/-- **The VM ReplyRecv slot's start fact in a VM epoch**: as `VmFStartY`, entry `VmRRPre (userV K) ∧ QPs` [S]. -/
def VmRStartY (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : VmRArg S) : Prop :=
  K.vcpus ≠ ∅ ∧ ∃ q0, (∃ _h : VmRPremY2 st ar j K.toKLayoutV, ∃ (σ : S) (a : A),
      (VmRPreY st ar j K.toKLayoutV σ ∧ QPs K st σ) ∧
      L.cpu σ = c ∧ j.Locks σ = hs ∧ (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
      ∀ h' : VmRPremY st ar j K.toKLayoutV,
        q0 = (LocalPath.liftV hK.base (LocalPath.atV hK.base
          ((vmRSlotY st ar hA hm).path j K.toKLayoutV m hK.base hU.base h')
          ((vmRSlotY st ar hA hm).W _ _ _ _ _ _)) (noVcpuRd_atV hK.base _ _)).body σ a) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

variable {st}

/-- **`VmLY` at `userV K` in a VM epoch** from the epoch's `VtxBundle4`, `QPs` at a state and a node placement
there (`userLayX_userV`, `ksb_fit_of_np`, `QPs.uoff`). -/
theorem vmLY_of {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (E : VtxBundle4 st L K) {σ : S} {T : Set U64}
    (hq : QPs K st σ) (hN : NodePlaced st T σ (L.cpu σ)) : VmLY (L := L) (userV K.toKLayoutV) :=
  ⟨userLayX_userV E.b.ul hK.base E.b.vh E.ko E.b.vsl (ksb_fit_of_np hN hq.ksb), regionOK_userV hK.base,
    userOK_userV hK.base hU.base, fun x hx hi hhi => hq.uoff x hx hi hhi⟩

variable {ar hA hm}

/-- **`StartAt` of the VM-fault slot** from its start fact and the epoch's bundle. -/
theorem vmFStartY_at {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : VmFArg S} (E : VtxBundle4 st L K)
    (h : VmFStartY st ar hA hm K μ hK hU c hs q j) :
    StartAt (vmFSlotPY st ar hA hm j K μ hK hU) c hs μ q := by
  obtain ⟨-, q0, ⟨hp, σ, a, ⟨hvm, hq⟩, hc, hl, hμ, hb⟩, rfl⟩ := h
  have hP : VmFPremY st j K.toKLayoutV := ⟨hp.ix, hp.kd, vmLY_of hK hU E hq hvm.1.base.np, E.la⟩
  have hpre : VmPre st ar (userV K.toKLayoutV) j.T j.Cs j.Ω j.U j.H j.Sg j.Rp j.Scs j.Nt j.Z j.Ac j.Locks σ ∧
      AffAg st (userV K.toKLayoutV) μ σ :=
    ⟨hvm, affAg_of_linkP hK hU hμ⟩
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) μ) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P)
      (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
        (fun b hb => Or.inl hb))),
      P = (vmFSlotY st ar hA hm).path j K.toKLayoutV μ hK.base hU.base hP →
      StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv) c hs μ
        (cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c q0 ∅) := by
    rintro P W hAv rfl
    have e : q0 = (LocalPath.liftV hK.base (LocalPath.atV hK.base
        ((vmFSlotY st ar hA hm).path j K.toKLayoutV μ hK.base hU.base hP) W)
        (noVcpuRd_atV hK.base _ W)).body σ a := hb hP
    refine ⟨σ, a, ⟨hpre, hq⟩, hc, hl, hμ, ?_⟩
    rw [body_cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv σ a, e, ← hc]
    rfl
  exact key _ _ _ (SlotU.fam_pos _ _ hP)

/-- **`StartAt` of the VM ReplyRecv slot** from its start fact and the epoch's bundle. -/
theorem vmRStartY_at {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : VmRArg S} (E : VtxBundle4 st L K)
    (h : VmRStartY st ar hA hm K μ hK hU c hs q j) :
    StartAt (vmRSlotPY st ar hA hm j K μ hK hU) c hs μ q := by
  obtain ⟨-, q0, ⟨hp, σ, a, ⟨hvm, hq⟩, hc, hl, hμ, hb⟩, rfl⟩ := h
  have hP : VmRPremY st ar j K.toKLayoutV := ⟨hp.cs, hp.kd, vmLY_of hK hU E hq hvm.1.base.np, E.la⟩
  have hpre : VmRPreY st ar j K.toKLayoutV σ ∧ AffAg st (userV K.toKLayoutV) μ σ :=
    ⟨hvm, affAg_of_linkP hK hU hμ⟩
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) μ) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P)
      (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
        (fun b hb => Or.inl hb))),
      P = (vmRSlotY st ar hA hm).path j K.toKLayoutV μ hK.base hU.base hP →
      StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv) c hs μ
        (cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c q0 ∅) := by
    rintro P W hAv rfl
    have e : q0 = (LocalPath.liftV hK.base (LocalPath.atV hK.base
        ((vmRSlotY st ar hA hm).path j K.toKLayoutV μ hK.base hU.base hP) W)
        (noVcpuRd_atV hK.base _ W)).body σ a := hb hP
    refine ⟨σ, a, ⟨hpre, hq⟩, hc, hl, hμ, ?_⟩
    rw [body_cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv σ a, e, ← hc]
    rfl
  exact key _ _ _ (SlotU.fam_pos _ _ hP)

end start

/-! ## Part 6: the tops -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The start facts, gen 11** (VX10's, plus `VmFStartY` / `VmRStartY` for vmF / vmR in VM epochs). -/
def StartVX11 {ιN : Type}
    (SFN : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ιN → Prop)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) :
    ((((((((((ιN ⊕ VxArg S) ⊕ VtArg S) ⊕ IoArg S) ⊕ StArg S) ⊕ IrqArg S) ⊕ SlArg S) ⊕ InvArg S) ⊕ InvArg S) ⊕
      InvArg S) ⊕ VmFArg S) ⊕ VmRArg S → Prop
  | .inl (.inl i) => StartVX10 st ar hA hm hSt a0 SFN Ch K m hK hU c hs q i
  | .inl (.inr j) => VmFStartY st ar hA hm K m hK hU c hs q j
  | .inr j => VmRStartY st ar hA hm K m hK hU c hs q j

end top

end
end Fl4Proofs.P2.E2EP
