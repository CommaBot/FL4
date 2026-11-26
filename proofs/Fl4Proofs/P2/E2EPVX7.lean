/-
# P2 (line vmscope, gen 7): the syscall entry in VM epochs — `serializable_fl4_localVX7`

`serializable_fl4_localVX5` (P2/E2EPVX5.lean) runs vx, vt, io, st and irq in VM epochs (states where some core runs
a guest, outside P3's scope). This module adds the syscall entry `syscall.handle_syscall_local` (sl), route C (the
path at `K.toKLayout`, cut by `AvoidV`), on VX6's bundle-free frame `SlLX` (P2/E2EPVX6.lean).

## 1. The path's entry facts without a P3 bundle (`PathObl`)
`sl_localPathK` reads `SlJAt` for `SlEntJ` (`dsR`, `hep`), `SlHereJ` (`ksb`, `cpu`, `cs`, `csc`) and `SlAccK` (`pool`,
`frl`, `jz`, the last only for `SlAccJ.rbuf` via `JAtZ.rbufAt`). Derived from `SlLX`: **`SlLX.dsR`**, **`SlLX.entJ`**
(`dsR` by the layout's `LayP`, `hep` by `SlLX.hep`, `hrp` by `SlLX.rrG`), **`SlLX.hereJ`** (`ksb` / `cpu` by
`SlLX.kc`, `ep` by `SlLX.rrG`), **`slAccJ_ofX`** (`fbuf` by `fbuf_of`, `frl` [P] from `SlAccR` as natively). Not
derivable without P3's chain, folded into **`SlEntX`** [S]: `cs` / `csc` (natively `SlJAtZ.cscFacts`: P1's
`EntryInv` at an entry with the action resume, P3's `CurInv` and `SchedCore.aff`), `pool` (natively `SlJAtZ.pool`
and `vsU`: P3's VSpace placement), `rbuf` (natively `JAtZ.rbufAt`, stated at the entry state; **`rbuf_ofX`** carries
it to the prefix state by `lookup_buf_agreeB`). **`SlEntX.wr`**: `SlEntX` survives an aligned user-word write at a
`SlLX` state (node, TCB, SC, TCB-slot, ASID-table words are `NU`). **`slEntsX`**: `SlEnt`, `SlHere`, `SlAccJ` at
`SlLX ∧ SlEntX ∧ SlQ`. **`sl_localPathX`**: `sl_localPathK` with `SlJAt` replaced by `SlLX ∧ SlEntX`.

## 2. `ReadOnce` without a P3 bundle
**`SlOFX`** (`SlOF` with `B : SlLX` and `Xe : SlEntX`), **`slOFX_of`**, **`SlLX.tabNU`** (the pool words by
`SlEntX.pool`), **`rdTabNX`**, and copies of the `SlOF` lemmas of `SlOnceN`/`A`/`B`/`R1` (`fltAcc_nuTX`,
`sl_trap_acc_guardNX`, `rrDec_nuX`, `sl_dec_guardNX`, `sl_alt_preX`, `sl_alt_preDecX`, `sl_alt_hhdX`,
`sl_once_trap_awayX`, `sl_once_rr_awayX`, `rrAccNB_nuX`: `slCom_nu` / `fltDec_nu` / `rrDR_nu` replaced by VX6's
`_X` forms, `rdTabN` by `rdTabNX`, otherwise unchanged), **`sl_rr_onceX`**, **`sl_hroX`** (no premise but `hSt`, `hA`,
`hm`, `a0`).

## 3. VCPU and PTE avoidance
**`sl_avoidVKE_X`** / **`sl_avoidVKE_rQX`** (`sl_avoidVKE` / `_rQ` for `sl_localPathX`: the block's fit by
`ksb_fit_of_np`, `HeapOK` by `UserLayX.lp`), **`sl_avoidVX`** (`AvoidV`: `Ex := VData K`, the ASID words by
`TabNoV` at the `Pre` states). **`avoidE_cutLiftV_X`** / **`avoidE_cutLiftV_rJX`**: route C with VCPUs present
(`avoidE_cutLiftV_empty` needs `K.vcpus = ∅`): a path avoiding `VData K ∨ Ex` and `VData K` has a cut-lift avoiding
`Ex` (`alt_back` writes a cut alternative back to a path alternative, `sim_off` transfers its run). Used with
`Ex := (· ∈ K.ptes)` and the path avoiding `VData ∨ ptes` under `QPs` (`regionOKE_vpte`, `userNoE_vpte`).

## 4. Slot, start fact, tops (`E2EP`)
`SlPreX` = `SlLX ∧ SlEntX ∧ TabNoV ∧ SlQ`; record **`SlPremX`** (`vh`, `ko`, `vu` from the epoch's `VtxBundle4`; `cs`
[P], `kd` [P]); **`sl_hufVX`**; **`slSlotX`** (route C, `ReadOnce` by `sl_hroX`, `AvoidV` by `sl_avoidVX`);
**`sl_avoidPX`**, **`sl_avoidPXf`**, **`slSlotPX`**; record **`SlPremX5`** (`cs`, `kd` [P]) and **`SlPremX5.toX`**;
start entry **`SlEntV`** [S] (`ents` = VX6's `SlEntS`, `entx` = `SlEntX`, `tab` = `TabNoV`, `qps` = `QPs`; `q` = U1's
`SlQ`); start fact **`SlStartX`**; **`slStartX_at`** (`SlLX` by VX6's `SlLX.ofVtx`); satisfiability **`slPremX5_sat`**
(every layout, any core count: constant lock map, as VX6's `ioPremX5_sat`) and **`slStartX_of`** (the start fact from a
start state with `SlEntV`, the armed program built from the epoch's bundle). Tops **`StartVX7`**,
**`serializable_fl4_localVX7G`**, **`serializable_fl4_localVX7`** = VX5's family ⊕ `slSlotPX`, glue `ExecVX4`.

Slots starting in VM epochs: vx, vt, io, st, irq, **sl**. Native epochs: all of U1's.

## Premise diff vs `serializable_fl4_localVX5`
| where | VX5 | VX7 |
|---|---|---|
| sl record | native epochs only (`SlPremP6`: `bun`, `cs` [P], `kd` [P] at `SlJAt` states) | also VM epochs: `SlPremX5`: `cs` [P] (= U1's), `kd` [P] (U1's, read at `SlLX` states); `vh`/`ko`/`vu` derived from `VtxBundle4` |
| sl start entry | `Ch σ ∧ SlQ` (P3 chain) | VM epochs: `SlEntV` [S] = `SlEntS` [S] (VX6) ∧ `SlEntX` [S] ∧ `TabNoV` [S] ∧ `QPs` [S] ∧ `SlQ` (U1's: `SlPreB`, `SlEntL` [P], `SlSyncC` [P], `SlAccR` [P]); `GlueAt` data [P] |
| everything else | | unchanged |
No new [J], no [W].

## [S] justification (Rust: fl4-core `syscall.rs`, `fastpath.rs`, `sched.rs`, `schedcontext.rs`, `msg.rs`, `vcpu.rs`,
`arch/x86_64/vspace.rs`, `arch/x86_64/objects.rs`; fl4-sync `lib.rs`)
A guest writes only its VCPU's data words and guest frames (`HwStepP`); VCPUs are untyped-retyped `bits::VCPU`
(`other 15`) objects, never frames, CNode slots, TCBs, SCs, nodes or ASID pools (`VtxBundle`). So each fact below is
the one of the last native state, where P3 gives it:
* `SlEntX.cs` / `.csc`: at a syscall entry the kernel runs the current thread on `CUR_SC` (`sched::cur_sc`), an
  active SC homed on this core (the scheduler switches `CUR_SC` to the chosen thread's SC;
  the `CORE` word is written only at boot and by SchedControl configure, `schedcontext.rs`: `set_cpu(cpu)` together with
  `smp::migrate_tcb(thread, cpu)`, so it is the bound thread's affinity). Natively `SlJAtZ.cscFacts`.
* `SlEntX.pool`, `SlEntV.tab`: the ASID table (`ks` block at `+288000`) names only untyped-retyped ASID-pool objects
  (ASIDControl make-pool, `arch/x86_64/vspace.rs`: a whole non-device untyped of `bits::ASID_POOL`
  with no children, then `set_asid_table`), never a frame and never a `bits::VCPU` object. Natively `SlJAtZ.pool` / `vsU`
  and `VFacts`' `VcpuTabOff` / `PoolObj`.
* `SlEntX.rbuf`: `msg::lookup_ipc_buffer(.., false, cur)` reads the `SLOT_BUFFER` frame cap, a user frame page
  (VCPUs are never frames). Natively `JAtZ.rbufAt`.
* `SlEntV.ents` (VX6's `SlEntS`) and `qps`: as VX6 / VX4.
`SlEntV.q` (`SlQ`) is U1's sl start fact unchanged; its [P] parts are fl4-sync's contract.

## [P]s
`SlPremX5.cs` = U1's `SlPremP6.cs`. `SlPremX5.kd` = U1's `SlPremP6.kd` (locks determined by kernel words) read at
`SlLX` states: fl4-sync `local_syscall` locks the objects of its plan, read from the current thread's TCB, CSpace and
endpoint words, none of which a guest writes. Satisfiable as VX6's `ioPremX5_sat` (a constant lock map).

No sorry / admit / native_decide / bv_decide. No existing statement or file changed except the root import list.
-/
import Fl4Proofs.P2.E2EPVX6
open Aeneas Aeneas.Std Result

/-! ## Part 1: the syscall entry's facts without a P3 bundle -/

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once ReadOnce)

section ent
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S}

variable (st) in
/-- **The syscall entry's state facts beyond `SlLX`** [S] (module docstring): what P3's bundle gives natively
(`SlJAtZ.cscFacts`, `SlJAtZ.pool` / `vsU`, `JAtZ.rbufAt`). -/
structure SlEntX (K : KLayout) (s : S) : Prop where
  /-- [S] `CUR_SC` is an active heap SC homed on this core (natively `SlJAtZ.cscFacts.1`). -/
  cs : ScHere (st := st) K K.heap.scBits K.heap.scs s (L.cscW s)
  /-- [S] the current thread's SC is `CUR_SC` (natively `SlJAtZ.cscFacts.2`). -/
  csc : L.mem s (scA (L.curW s)) = L.cscW s
  /-- [S] the ASID pools the table names are aligned, in no region and no user words (natively `SlJAtZ.pool`,
  `SlJAtZ.vsU`). -/
  pool : ∀ hi : U64, hi.val < 2048 → L.mem s (atAF K.ksb hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 →
    Aligned (peAF (L.mem s (atAF K.ksb hi)) lo) ∧ region K (peAF (L.mem s (atAF K.ksb hi)) lo) = .none ∧
      peAF (L.mem s (atAF K.ksb hi)) lo ∉ K.user
  /-- [S] the current thread's IPC buffer is aligned user words (natively `JAtZ.rbufAt`). -/
  rbuf : ∀ buf, msg.lookup_ipc_buffer st s false (L.curW s) = ok buf →
    BufW (fun b => Aligned b ∧ b ∈ K.user) buf

/-- **`SlEntX` survives an aligned user-word write** at a `SlLX` state (every word it reads is a node, TCB, SC,
TCB-slot or ASID-table word: `NU`). -/
theorem SlEntX.wr (B : SlLX (L := L) K s) (Xe : SlEntX st K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) : SlEntX st K (L.wr s b v) := by
  have hX := B.regionOKX
  have hK := B.regionOK
  obtain ⟨hcH, -⟩ := B.cur
  have ecur := B.curW_wr hb hba v
  have Gw : Ag st (NU K) s (L.wr s b v) := ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun x hx => wr_nu hba hb v hx⟩
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s b v) (L.nodeAt (L.wr s b v) (L.cpu (L.wr s b v)) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o ho h8 => by rw [Gw.node]; exact Gw.m _ (B.nuNode B.np ho h8)
  have ecsc : L.cscW (L.wr s b v) = L.cscW s := eN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨hz, hin, hmx, hco⟩ := Xe.cs
    rw [ecsc]
    refine ⟨hz, hin, ?_, ?_⟩
    · have e : L.mem (L.wr s b v) (maxA (L.cscW s)) = L.mem s (maxA (L.cscW s)) :=
        Gw.m _ (nu_scw hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
          (by simp [layout.sc.REFILL_MAX]))
      show L.mem (L.wr s b v) (maxA (L.cscW s)) ≠ 0#u64
      rw [e]; exact hmx
    · have e : L.mem (L.wr s b v) (fld (L.cscW s) 16#u64) = L.mem s (fld (L.cscW s) 16#u64) :=
        Gw.m _ (nu_scw hX hz (o := 16#u64) (by simp) (by simp))
      rw [e, L.cpu_wr]; exact hco
  · have e : L.mem (L.wr s b v) (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [ecur, ecsc, e]; exact Xe.csc
  · intro hi hhi h0 lo hlo
    have hn : NU K (atAF K.ksb hi) := by
      have h := B.nuAsid (X := s) rfl hhi
      rwa [B.kc.1] at h
    have ea : L.mem (L.wr s b v) (atAF K.ksb hi) = L.mem s (atAF K.ksb hi) := wr_nu hba hb v hn
    rw [ea] at h0 ⊢
    exact Xe.pool hi hhi h0 lo hlo
  · intro buf hbuf
    rw [ecur] at hbuf
    have es : sbA (L.curW s) = slotIdx (L.curW s) 2#u64 := by
      unfold sbA slotIdx
      congr 1
      simp [layout.tcb.SLOT_BUFFER, layout.cte.SIZE]
    have nts := nu_tslot hK hX hcH (i := 2#u64) (by simp)
    have e1 : L.mem (L.wr s b v) (ibA (L.curW s)) = L.mem s (ibA (L.curW s)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := 3512#u64) (by simp) (by simp) (by simp))
    have e2 : L.mem (L.wr s b v) (sbA (L.curW s)) = L.mem s (sbA (L.curW s)) := by
      rw [es]; exact wr_nu hba hb v nts.1
    have e3 : L.mem (L.wr s b v) (core.num.U64.wrapping_add (sbA (L.curW s)) 8#u64) =
        L.mem s (core.num.U64.wrapping_add (sbA (L.curW s)) 8#u64) := by
      rw [es]; exact wr_nu hba hb v nts.2
    rw [lookup_buf_agreeB false e1 e2 e3] at hbuf
    exact Xe.rbuf buf hbuf

/-- **`SlEntJ.dsR` at `SlLX`** (`SlJAtZ.dsR` without the bundle). -/
theorem SlLX.dsR (B : SlLX (L := L) K s) {T : Set U64} (hN : NodePlaced st T s (L.cpu s)) :
    ∀ x, SlDS (L := L) s x → (∃ c, region K x = .node c) ∨ region K x = .tcb (L.curW s) := by
  obtain ⟨hk, hc⟩ := B.kc
  have hnode : ∀ o : U64, o.val < 4288 → region K (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) := by
    intro o ho
    have v := nodeAt_val hN ho
    exact slj_region_node ⟨hc, by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega,
      by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega⟩
  intro x hx
  rcases hx with rfl | rfl | rfl
  · right
    have ht : K.heap (L.curW s) = some .tcb := B.cur.1
    have hf := B.layP.heap.fits _ _ ht
    simp only [HKind.bits] at hf
    have hv := slj_faultIp_val (t := L.curW s) (by omega)
    exact B.layP.region_tcb ht ⟨by omega, by omega⟩ (by omega)
  · exact Or.inl ⟨_, hnode _ (by simp [layout.node.CUR_TIME])⟩
  · exact Or.inl ⟨_, hnode _ (by simp [layout.node.CONSUMED])⟩

/-- **`SlEntJ` at `SlLX`** from fl4-sync's contract and the lock facts (`SlJAt.entJ` / `entR`). -/
theorem SlLX.entJ {Locks : S → U64 → Prop} {n : I64} {found : U64 × U64} (B : SlLX (L := L) K s)
    {T : Set U64} (hN : NodePlaced st T s (L.cpu s)) (C : SlSyncC st n found s)
    (E : SlEntL (st := st) K Locks found s) : SlEntJ (st := st) K Locks found s :=
  ⟨B.dsR hN, fun _ hE => B.hep hE, fun hS => (B.rrG C.fd hS (C.arm hS)).1, E.lep, E.lrp⟩

/-- **`SlHereJ` at `SlLX`**, `cs` / `csc` from `SlEntX` [S]. -/
theorem SlLX.hereJ {n : I64} {found : U64 × U64} (B : SlLX (L := L) K s) (Xe : SlEntX st K s)
    (C : SlSyncC st n found s) : SlHereJ (st := st) K K.heap.scBits K.heap.scs found s :=
  ⟨B.kc.1, B.kc.2, Xe.cs, fun _ => by rw [Xe.csc]; exact Xe.cs, fun hS => (B.rrG C.fd hS (C.arm hS)).2⟩

variable {Locks : S → U64 → Prop} {A : Type} (ar : machine.Arch A)
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **`SlAccJ.rbuf` from `SlEntX.rbuf`** (the buffer words carried to the prefix state by `lp_mem`, as
`rbuf_of`). -/
theorem rbuf_ofX (hA : P0.ArchTotal ar) (B : SlLX (L := L) K s) (Xe : SlEntX st K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {buf : U64}
    (hb : msg.lookup_ipc_buffer st X false (L.curW s) = ok buf) :
    BufW (fun b => Aligned b ∧ b ∈ K.user) buf := by
  have hK := B.regionOK
  have hX := B.regionOKX
  obtain ⟨hk, hcp⟩ := B.kc
  have hc := E.hSt.1
  have e1 : L.mem X (ibA (L.curW s)) = L.mem s (ibA (L.curW s)) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hc 3512#u64 (by simp) (by simp) (by simp)).2.2
      (not_slDS_tcb hX E.hN E.hT E.hcT hc hk hcp hc (by simp) (by simp) (by simp) (by simp))
  have es : sbA (L.curW s) = slotIdx (L.curW s) 2#u64 := by
    unfold sbA slotIdx
    congr 1
    simp [layout.tcb.SLOT_BUFFER, layout.cte.SIZE]
  obtain ⟨hsl, -, r8, -, al0, al8⟩ := hX.tslot _ hc 2#u64 (by simp)
  have r0 := hK.slot _ hsl
  have e2 : L.mem X (sbA (L.curW s)) = L.mem s (sbA (L.curW s)) := by
    rw [es]
    exact lp_mem ar hA E.hT E.hN E.hcT LP al0 (not_slDS_reg hX E.hN E.hT E.hcT hc hk hcp
      (by rw [r0]; intro c h; cases h) (by rw [r0]; intro h; cases h))
  have e3 : L.mem X (core.num.U64.wrapping_add (sbA (L.curW s)) 8#u64) =
      L.mem s (core.num.U64.wrapping_add (sbA (L.curW s)) 8#u64) := by
    rw [es]
    exact lp_mem ar hA E.hT E.hN E.hcT LP al8 (not_slDS_reg hX E.hN E.hT E.hcT hc hk hcp
      (by rw [r8]; intro c h; cases h) (by rw [r8]; intro h; cases h))
  rw [lookup_buf_agreeB false e1 e2 e3] at hb
  exact Xe.rbuf buf hb

/-- **`SlAccJ` at `SlLX`** (`pool`, `rbuf` from `SlEntX` [S]; `fbuf` by `fbuf_of`; `frl` [P] from `SlAccR`). -/
theorem slAccJ_ofX (hA : P0.ArchTotal ar) (B : SlLX (L := L) K s) (Xe : SlEntX st K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (Ar : SlAccR (st := st) ar K Locks found s) : SlAccJ (st := st) ar K Locks found s where
  pool := fun hi hhi h0 lo hlo => ⟨(Xe.pool hi hhi h0 lo hlo).1, (Xe.pool hi hhi h0 lo hlo).2.1⟩
  frl := Ar.frl
  fbuf := fun hS a X a1 LP {_p _b _d _r} hc rb hrb => fbuf_of ar (fun _ h => h) E hS LP hc rb hrb
  rbuf := fun _ a X a1 LP buf hb => rbuf_ofX ar hA B Xe E LP hb

/-- **The path obligations' entry facts at `SlLX ∧ SlEntX ∧ SlQ`** (`SlEnt` by `slEnt_of`, `SlHere` by
`slHere_of`, `SlAccJ` by `slAccJ_ofX`). -/
theorem slEntsX (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (a0 : A) (B : SlLX (L := L) K s)
    (Xe : SlEntX st K s) (q : SlQ st ar Locks n found Cs Ω Sg Ac K m0 s) :
    SlEnt (st := st) K Locks found s ∧ SlHere (st := st) K K.heap.scBits K.heap.scs found s ∧
      SlAccJ (st := st) ar K Locks found s := by
  obtain ⟨E, El, C, Ar⟩ := q
  have hX := B.regionOKX
  have N := slEnt_of ar hSt hA hX (slSets_conv K) a0 E (B.entJ E.hN C El)
  exact ⟨N, slHere_of ar hSt hA hX (slSets_conv K) a0 E N (B.hereJ Xe C), slAccJ_ofX ar hA B Xe E Ar⟩

/-- **The syscall entry as a local path without a P3 bundle** (`sl_localPathK` with `SlJAt` replaced by
`SlLX ∧ SlEntX`, the entry facts by `slEntsX`). -/
noncomputable def sl_localPathX (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {P : S → Prop}
    (hJ : ∀ s, P s → SlLX (L := L) K s) (hXe : ∀ s, P s → SlEntX st K s)
    (hQ : ∀ s, P s → SlQ st ar Locks n found Cs Ω Sg Ac K m0 s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) P
        (SlRS (st := st) K Locks)) :
    Fl4Proofs.P2.E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) :=
  have hEN : ∀ s, P s → SlEnt (st := st) K Locks found s ∧ SlHere (st := st) K K.heap.scBits K.heap.scs found s ∧
      SlAccJ (st := st) ar K Locks found s :=
    fun s hP => slEntsX ar hSt hA a0 (hJ s hP) (hXe s hP) (hQ s hP)
  have O : ∀ s, P s → PathObl st (fun m s a => syscall.handle_syscall_local m ar s a n found)
      (fun b => b = true) (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
    fun s hP => sl_pathObl_j ar hA hK (hJ s hP).regionOKX hU hpz.choose_spec.1 hpz.choose_spec.2.1 hm
      (slSets_conv K) (fun s hP => (hQ s hP).1) (fun s hP => (hEN s hP).1) (fun s hP => (hEN s hP).2.1)
      (fun s hP => (hEN s hP).2.2)
  have Sd : ∀ s, P s → PathSide st (fun m s a => syscall.handle_syscall_local m ar s a n found)
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
    fun s hP => sl_pathSide_j ar hSt hA hK (hJ s hP).regionOKX hU hpz.choose_spec.1 hpz.choose_spec.2.1 hm
      (slSets_conv K) (fun s hP => (hQ s hP).1) (fun s hP => (hEN s hP).1) (fun s hP => (hEN s hP).2.1)
      (fun s hP => (hEN s hP).2.2) huf
  { S := S
    A := A
    X := Bool
    st := st
    L := L
    ar := ar
    F := slBody S n found
    p := hpz.choose
    Acc := fun b => b = true
    Locks := Locks
    Pre := P
    RS := SlRS (st := st) K Locks
    WS := SlWS (st := st) K Locks
    DS := SlDS (L := L)
    isProg := IsProg.on hpz.choose_spec.1 _ _ _
    obl :=
      { acc := fun s a r hP => (O s hP).acc s a r hP
        dec_alt := fun s a r hP => (O s hP).dec_alt s a r hP
        read_own := fun s x hP => (O s hP).read_own s x hP
        write_own := fun s x hP => (O s hP).write_own s x hP
        aligned := fun s x hP => (O s hP).aligned s x hP
        move := fun s a r hP => (O s hP).move s a r hP }
    side :=
      { read_aligned := fun s s' a r hP => (Sd s hP).read_aligned s s' a r hP
        rs_aligned := fun s x hP => (Sd s hP).rs_aligned s x hP
        ko_aligned := fun x hx => Fl4Proofs.P2.ko_aligned hK hU x hx
        user_free := fun s b v hP => (Sd s hP).user_free s b v hP }
    once := hpz.choose_spec.2.2
    total := fun s a => sl_total hSt hA n found s a
    masks := hm }

end ent

/-! ## Part 2: `ReadOnce` without a P3 bundle (`SlOnceN`/`A`/`B`/`R1`/`R3` at `SlLX ∧ SlEntX`) -/

section N
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {Cs Ω Sg Ac : Set U64}

/-- **Every entry fact of the syscall path at `SlLX ∧ SlEntX` with the canonical `Q`** (`SlOF` without the
bundle). -/
structure SlOFX (K : KLayout) (Locks : S → U64 → Prop) (m0 : U64 → U64) (n : I64) (found : U64 × U64)
    (Cs Ω Sg Ac : Set U64) (s : S) : Prop where
  B : SlLX (L := L) K s
  Xe : SlEntX st K s
  E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
    K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s
  C : SlSyncC st n found s
  N : SlEnt (st := st) K Locks found s
  Hh : SlHere (st := st) K K.heap.scBits K.heap.scs found s
  Ai : SlAccIn (st := st) ar K Locks K.heap.scBits K.heap.scs found s
  P : SlPre (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
    K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s
  I : SlThrIn (st := st) K Locks found.1 s
  D : SlDecIn (st := st) ar K Locks found s

theorem slOFX_of (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (a0 : A) {s : S} (hJ : SlLX (L := L) K s)
    (hXe : SlEntX st K s) (hq : SlQ st ar Locks n found Cs Ω Sg Ac K m0 s) :
    SlOFX (st := st) ar K Locks m0 n found Cs Ω Sg Ac s := by
  have hK := hJ.regionOK
  have hX := hJ.regionOKX
  obtain ⟨N, Hh, Aj⟩ := slEntsX ar hSt hA a0 hJ hXe hq
  obtain ⟨E, -, C, -⟩ := hq
  have Ai := slAccIn_of ar hA hK hX (slSets_conv K) E N Hh Aj
  have P := slPre_of ar hA hK hX E N Hh Ai
  exact ⟨hJ, hXe, E, C, N, Hh, Ai, P, slThrIn_of hK hX P.preG E.hSt.1 N, slDecIn_of ar hA hK hX E N Hh⟩

/-- **No ASID-table or ASID-pool word is a user word** at a `SlLX ∧ SlEntX` state (`SlJAt.tabNU`). -/
theorem SlLX.tabNU {s : S} (B : SlLX (L := L) K s) (Xe : SlEntX st K s) {hi : U64} (hhi : hi.val < 2048) :
    NU K (atAF (L.ksb s) hi) ∧ ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
      NU K (peAF (L.mem s (atAF (L.ksb s) hi)) lo) := by
  refine ⟨B.nuAsid rfl hhi, fun lo hlo h0 => ?_⟩
  rw [B.kc.1] at h0 ⊢
  obtain ⟨h1, -, h3⟩ := Xe.pool hi hhi h0 lo hlo
  exact ⟨h1, h3⟩

/-- The ASID table and pools read by `set_vm_root`, at the prefix state, are `NU` (`rdTabN` at `SlLX`). -/
theorem rdTabNX (hA : P0.ArchTotal ar) {s : S} (hJ : SlLX (L := L) K s) (hXe : SlEntX st K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (Hh : SlHere (st := st) K K.heap.scBits K.heap.scs found s) {a X a1}
    (LP : LocalPre (st := st) ar s a (X, a1)) : RdTab (L := L) (NU K) X := by
  have hX := hJ.regionOKX
  obtain ⟨kX, -, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  intro hi hhi
  rw [kX]
  have e0 : L.mem X (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) := by
    rw [Hh.ksb]
    obtain ⟨r0, a0⟩ := hX.asidT hi hhi
    exact lp_mem ar hA E.hT E.hN E.hcT LP a0 (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu
      (by rw [r0]; intro c h; cases h) (by rw [r0]; intro h; cases h))
  obtain ⟨n1, n2⟩ := hJ.tabNU hXe hhi
  exact ⟨n1, fun lo hlo hne => by rw [e0] at hne ⊢; exact n2 lo hlo hne⟩

set_option maxHeartbeats 4000000 in
/-- **The trap arm's access facts at `NU K`** (`fltAcc_wn` with every read word shown not a user word;
writes unconstrained). -/
theorem fltAcc_nuTX (hA : P0.ArchTotal ar) {s : S} (F : SlOFX (st := st) ar K Locks m0 n found Cs Ω Sg Ac s)
    (hS : SlTrap st s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) :
    FltAcc (L := L) K.heap.scBits (NU K) (fun _ => True) X (L.curW s) ptr dest r := by
  have B := F.B
  have E := F.E
  have Hh := F.Hh
  have hK := B.regionOK
  have hX := B.regionOKX
  have C := slCom_nuX ar hA B E LP
  obtain ⟨kX, cX, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have hc0 := E.hSt.1
  obtain ⟨hep, -⟩ := trap_ep ar hA E F.N F.I hS LP hc
  obtain ⟨hdt, -, -, -⟩ := E.hSd hS a X a1 LP hc
  have nT : ∀ {t o : U64}, K.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu ht h1 h2 h3 h4
  obtain ⟨hz, -, -, -⟩ := F.Ai.dsc hS a X a1 LP hc
  have eSc : L.mem X (scA dest) = L.mem s (scA dest) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hdt 3464#u64 (by simp) (by simp) (by simp)).2.2
      (nT hdt (by simp) (by simp) (by simp) (by simp))
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have eRh : L.mem X (rhA (L := L) X) = L.mem s (rhA (L := L) s) := by
    show L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)
    rw [nX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])) (not_slDS_node E.hN E.hT E.hcT (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
  have tw : ∀ y, K.heap y = some .tcb → ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      NU K (core.num.U64.wrapping_add y o) := fun y hy o h1 h2 h3 => nu_tcb hX hy h1 h2 h3
  exact
  { nd := fun o h1 h2 => ⟨C.nd o h1 h2, trivial⟩
    dt := C.dt
    cd := C.cd
    kr := by
      show NU K (core.num.U64.wrapping_add (L.ksb X) layout.ks.KERNEL_ROOT)
      rw [kX]
      exact B.nuKs E.hN (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
    tab := rdTabNX ar hA B F.Xe E Hh LP
    fh := fun sl hsl => by
      rw [tcb_slot_val] at hsl
      obtain rfl := ok_inj_ff hsl
      exact nu_tslot hK hX hc0 (by simp [layout.tcb.SLOT_FAULT_HANDLER])
    eph := ⟨nu_ep hX hep (o := layout.ep.HEAD) (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD]), trivial⟩
    ept := ⟨nu_ep hX hep (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE])
      (by simp [layout.ep.TAIL_STATE]), trivial⟩
    tf := fun o ho => ⟨tw _ hc0 o (by rcases ho with h | h | h | h <;> omega)
      (by rcases ho with h | h | h | h <;> omega) (by rcases ho with h | h | h | h <;> omega), trivial⟩
    treg := nuRegs hX hc0
    trp := trivial
    drp := tw _ hdt 3360#u64 (by simp) (by simp) (by simp)
    daf := tw _ hdt 3520#u64 (by simp) (by simp) (by simp)
    ddo := tw _ hdt 3432#u64 (by simp) (by simp) (by simp)
    dsc0 := tw _ hdt 3464#u64 (by simp) (by simp) (by simp)
    diq := tw _ hdt 3592#u64 (by simp) (by simp) (by simp)
    dpr := tw _ hdt 3448#u64 (by simp) (by simp) (by simp)
    dyt := tw _ hdt 3472#u64 (by simp) (by simp) (by simp)
    dst := by rw [stA_eq]; exact tw _ hdt 3328#u64 (by simp) (by simp) (by simp)
    dfi := nuReg hX hdt (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    den := tw _ hdt 3496#u64 (by simp) (by simp) (by simp)
    dib := tw _ hdt 3512#u64 (by simp) (by simp) (by simp)
    dvt := by
      rw [vtA_slot]
      exact nu_tslot hK hX hdt (by simp [layout.tcb.SLOT_VTABLE])
    dbs := fun sl hsl => by
      rw [tcb_slot_val] at hsl
      obtain rfl := ok_inj_ff hsl
      exact nu_tslot hK hX hdt (by simp [layout.tcb.SLOT_BUFFER])
    dw := ⟨trivial, trivial, trivial, trivial⟩
    dreg := fun _ _ => trivial
    nxt := fun _ => trivial
    buf := fun _ _ _ _ _ => trivial
    rt := trivial
    spo := by
      rw [eSc]
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact nu_sc hX hz am hin
    dsc := by rw [eSc]; exact scAccNU hX hz
    csc := by
      rw [ecs]
      obtain ⟨hz', -, -, -⟩ := Hh.cs
      exact scAccNU hX hz'
    tm := C.tm
    rh := fun h => by
      refine ⟨(C.rh h).1, ?_, (C.rh h).2⟩
      rw [eRh] at h ⊢
      obtain ⟨ht, hs⟩ := Hh.rh h
      have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
        lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
          (nT ht (by simp) (by simp) (by simp) (by simp))
      rw [eS]
      obtain ⟨hz', -, -, -⟩ := hs
      exact fun b ha hb => nu_sc hX hz' ha hb }

/-- **An accepted trap arm runs on `guard st (NU K) ⊤`** (`guard_acc` at `R := NU K`, `W := ⊤`). -/
theorem sl_trap_acc_guardNX (hA : P0.ArchTotal ar) {s : S} (F : SlOFX (st := st) ar K Locks m0 n found Cs Ω Sg Ac s)
    (hS : SlTrap st s) {a : A} {s1 : S} {a1 : A}
    (h : syscall.handle_syscall_local st ar s a n found = ok (true, s1, a1)) :
    syscall.handle_syscall_local (guard st (NU K) (fun _ => True)) ar s a n found = ok (true, s1, a1) := by
  have E := F.E
  have hX := F.B.regionOKX
  have hpre : PreAcc (L := L) (NU K) (fun _ => True) s :=
    ⟨fun o h1 h2 => ⟨F.B.nuNode E.hN h1 h2, trivial⟩,
      nu_tcb hX E.hSt.1 (o := 3456#u64) (by simp) (by simp) (by simp),
      nuReg hX E.hSt.1 (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP]), trivial⟩
  have hhd : ∀ X a1 csc, LocalPre (st := st) ar s a (X, a1) → sched.cur_sc st X = ok csc →
      RdHead (L := L) (NU K) X csc := by
    intro X a1 csc LP hcs
    obtain ⟨-, -, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    have e : csc = L.cscW s := by
      rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X)] at hcs
      rw [← ok_inj_ff hcs]; exact ecs
    subst e
    exact rdHead_hereN ar hA hX E F.Hh LP F.Hh.cs
  exact syscall.handle_syscall_local.guard_acc (gS := guard st (NU K) (fun _ => True))
    (R := NU K) (W := fun _ => True) ar hA E.hT E.hN E.hcT hpre hhd (E.hI a) (E.hAs a)
    (fun h' => E.hrecv h' a) (fun h' => E.hF h' a) (fun h' => E.hy0f h' a) (fun h' => E.hTm h' a)
    (fun _ X a1 LP {_p _b _d _r} hc => fltAcc_nuTX ar hA F hS LP hc)
    (fun _ _ _ _ {_p _b _d _r} _ => ⟨SWr.of_W (W := fun _ => True) trivial,
      fun _ _ => SWr.of_W (W := fun _ => True) trivial⟩)
    (fun h' => absurd hS h') (fun h' => absurd hS h') (fun h' => absurd hS h') (fun h' => absurd hS h')
    (fun h' => absurd hS h') h

set_option maxHeartbeats 4000000 in
/-- **The ReplyRecv arm's declining reads at `NU K`** (`rrDR_nuX`, with the current thread's `REFILL_MAX` and
the replied thread's state, fault and SC words unconditionally, its SC head from `SlHere`). -/
theorem rrDec_nuX (hA : P0.ArchTotal ar) {s : S} (F : SlOFX (st := st) ar K Locks m0 n found Cs Ω Sg Ac s)
    (hS : ¬ SlTrap st s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) :
    RrDec (L := L) (NU K) X (L.curW s) found.1 found.2 := by
  have B := F.B
  have E := F.E
  have Hh := F.Hh
  have I := F.I
  have hX := B.regionOKX
  have D' := rrDR_nuX ar hA B E F.C hS LP
  have C := slCom_nuX ar hA B E LP
  obtain ⟨-, hcX, aT, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have hc := E.hSt.1
  have nT : ∀ {t o : U64}, K.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc Hh.ksb Hh.cpu ht h1 h2 h3 h4
  obtain ⟨hz, -, -, -⟩ := Hh.csc hS
  have eS : L.mem X (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    aT _ E.hcT 3464#u64 (by simp) (by simp) (by simp)
  refine RrDec.of ⟨D'.nd, D'.dt, D'.cd, C.bm, D'.tm, D'.rh, D'.tSt, D'.tSc, ?_, D'.tIq, D'.tMi, D'.tBn,
    D'.tPr, ?_, D'.rRt, D'.rNx, D'.eTS⟩ ?_
  · rw [eS]
    exact nu_scw hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX]) (by simp [layout.sc.REFILL_MAX])
  · intro nt hnt hne
    have e1 := (eq_of_spec_fd (obj.Tcb.bound_ntfn.val X (L.curW s))).symm.trans hnt
    have en : nt = L.mem X (boundA (L.curW s)) := (ok_inj_ff e1).symm
    subst en
    exact D'.ntf (fun h0 => by rw [h0] at hne; simp at hne)
  · intro u hu hu0
    have h1 := obj.Reply.tcb.blk (st := st) X found.1
    rw [hu, WP.spec_ok, slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP] at h1
    have lv := slLive_rr (st := st) hS (by rw [← h1]; exact hu0)
    have ht := F.N.hthr lv
    rw [h1]
    have tw : ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
        NU K (core.num.U64.wrapping_add (slThr st found.1 s) o) := fun o h1 h2 h3 => nu_tcb hX ht h1 h2 h3
    refine ⟨by rw [stA_eq]; exact tw _ (by simp) (by simp) (by simp), tw 3376#u64 (by simp) (by simp) (by simp),
      tw 3464#u64 (by simp) (by simp) (by simp), tw 3520#u64 (by simp) (by simp) (by simp),
      fun hh => ⟨tw 3432#u64 (by simp) (by simp) (by simp), tw 3592#u64 (by simp) (by simp) (by simp),
        tw 3448#u64 (by simp) (by simp) (by simp), fun usc eu hne => ?_⟩⟩
    have af := I.af lv
    have hh' : L.mem s (affA (slThr st found.1 s)) = L.cpu s := by
      rw [← lp_mem ar hA E.hT E.hN E.hcT LP af.1.1 af.2, hh, hcX]
    have eU : L.mem X (scA (slThr st found.1 s)) = L.mem s (scA (slThr st found.1 s)) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
        (nT ht (by simp) (by simp) (by simp) (by simp))
    have e1 : usc = L.mem s (scA (slThr st found.1 s)) := by
      rw [tcb_sc_ok] at eu; rw [← ok_inj_ff eu, eU]
    subst e1
    exact rdHead_hereN ar hA hX E Hh LP (Hh.usc hS lv hh' hne)

/-- **A declined run of the syscall entry runs on `guard st (NU K) ⊤`** (`guard_dec` at `R := NU K`: the trap
arm by `fltDec_nuX`, the ReplyRecv arm by `rrDec_nuX`, whoever the decided thread's home). -/
theorem sl_dec_guardNX (hA : P0.ArchTotal ar) {s : S} (F : SlOFX (st := st) ar K Locks m0 n found Cs Ω Sg Ac s)
    {a : A} {r : Bool × S × A} (h : syscall.handle_syscall_local st ar s a n found = ok r) (hn : r.1 ≠ true) :
    syscall.handle_syscall_local (guard st (NU K) (fun _ => True)) ar s a n found = ok r := by
  have E := F.E
  have hX := F.B.regionOKX
  have hp : PreDec (L := L) (NU K) (fun _ => True) s :=
    ⟨fun o h1 h2 => F.B.nuNode E.hN h1 h2, trivial, trivial,
      nu_tcb hX E.hSt.1 (o := 3456#u64) (by simp) (by simp) (by simp),
      nuReg hX E.hSt.1 (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP]), trivial⟩
  refine syscall.handle_syscall_local.guard_dec (gS := guard st (NU K) (fun _ => True)) hA E.hT E.hN E.hcT hp
    (fun X a1 csc LP hcs => ?_) (fun _ X a1 n' LP hf => fastpath.fault.guard_dec (fltDec_nuX ar hA F.B E LP) hf hn)
    (fun hS X a1 LP hf => fastpath.reply_recv_found.guard_dec (rrDec_nuX ar hA F hS LP) hf hn) h
  obtain ⟨-, -, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have e : csc = L.cscW s := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X)] at hcs
    rw [← ok_inj_ff hcs]; exact ecs
  subst e
  exact rdHead_hereN ar hA hX E F.Hh LP F.Hh.cs

end N

section altA
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {Cs Ω Sg Ac : Set U64}

/-- **An alternative's prefix state agrees with an entry's prefix state on `SlRS s`** (`lp_alt`). -/
theorem sl_alt_preX (hA : P0.ArchTotal ar) {s s' : S} {a : A}
    (F : SlOFX (st := st) ar K Locks m0 n found Cs Ω Sg Ac s)
    (Al : Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {X' : S} {a1' : A} (LP' : LocalPre (st := st) ar s' a (X', a1')) :
    ∃ X, LocalPre (st := st) ar s a (X, a1') ∧
      (∀ b, SlRS (st := st) K Locks s b → L.mem X' b = L.mem X b) ∧ L.ksb X' = L.ksb X ∧ L.cpu X' = L.cpu X := by
  have E := F.E
  have hcur := sl_alt_cur F.P.preG Al
  have hN' : NodePlaced st K.heap.tcbs s' (L.cpu s') := by rw [Al.cpu]; exact NodePlaced.of_ksb Al.ksb E.hN
  have hc' : L.curW s' ∈ K.heap.tcbs := by rw [hcur]; exact E.hcT
  have hct : SlRS (st := st) K Locks s (ctA (L := L) s) :=
    (F.P.preG.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
  have hcn : SlRS (st := st) K Locks s (cnA (L := L) s) :=
    (F.P.preG.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
  obtain ⟨X, LP, hag⟩ := lp_alt ar hA (fun b hb => hb.1) E.hT E.hN E.hcT Al.ksb Al.cpu hcur Al.read
    F.P.preG.nx hct hcn LP'
  obtain ⟨hkX, hcX, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  obtain ⟨hkX', hcX', -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT hN' hc' LP'
  exact ⟨X, LP, hag, by rw [hkX', hkX, Al.ksb], by rw [hcX', hcX, Al.cpu]⟩

/-- The prefix facts at an alternative, on `SlRN s` / `NU K`. -/
theorem sl_alt_preDecX {s s' : S} (F : SlOFX (st := st) ar K Locks m0 n found Cs Ω Sg Ac s)
    (Al : Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s') :
    PreDec (L := L) (SlRN (st := st) K Locks s) (NU K) s' := by
  have E := F.E
  have hX := F.B.regionOKX
  have hcur := sl_alt_cur F.P.preG Al
  refine ⟨fun o h1 h2 => by rw [slDS_node Al.ksb Al.cpu]; exact ⟨(F.P.preG.nd o h1 h2).1, F.B.nuNode E.hN h1 h2⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · show NU K (L.nodeAt s' (L.cpu s') layout.node.CUR_TIME)
    rw [slDS_node Al.ksb Al.cpu]
    exact F.B.nuNode E.hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  · show NU K (L.nodeAt s' (L.cpu s') layout.node.CONSUMED)
    rw [slDS_node Al.ksb Al.cpu]
    exact F.B.nuNode E.hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  · rw [hcur]; exact ⟨F.P.preG.fl, nu_tcb hX E.hSt.1 (o := 3456#u64) (by simp) (by simp) (by simp)⟩
  · rw [hcur]; exact ⟨F.P.preG.nx, nuReg hX E.hSt.1 (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])⟩
  · rw [hcur]; exact nuReg hX E.hSt.1 (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])

/-- The current SC's head refill at an alternative's prefix state, on `SlRN s`. -/
theorem sl_alt_hhdX (hA : P0.ArchTotal ar) {s s' : S} {a : A}
    (F : SlOFX (st := st) ar K Locks m0 n found Cs Ω Sg Ac s)
    (Al : Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s') :
    ∀ X' a1 csc, LocalPre (st := st) ar s' a (X', a1) → sched.cur_sc st X' = ok csc →
      RdHead (L := L) (SlRN (st := st) K Locks s) X' csc := by
  intro X' a1' csc LP' ecsc
  have E := F.E
  have hX := F.B.regionOKX
  obtain ⟨X, LP, hag, hk, hc⟩ := sl_alt_preX ar hA F Al LP'
  obtain ⟨hkX, hcX, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have rcs : SlRS (st := st) K Locks s (L.nodeA X layout.node.CUR_SC) := by
    unfold LawfulStore.nodeA; rw [hcX, nodeAt_of_ksb hkX]
    exact (F.P.preG.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
  have en : L.nodeA X' layout.node.CUR_SC = L.nodeA X layout.node.CUR_SC := by
    unfold LawfulStore.nodeA; exact slDS_node hk hc
  have ecsc' : sched.cur_sc st X = ok csc := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X')] at ecsc
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X), ← hag _ rcs, ← en]
    exact ecsc
  have h1 := F.P.hhd a X a1' csc LP ecsc'
  have e : csc = L.cscW s := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X)] at ecsc'
    rw [← ok_inj_ff ecsc']; exact ecs
  have h2 : RdHead (L := L) (NU K) X csc := by
    rw [e]; exact rdHead_hereN ar hA hX E F.Hh LP F.Hh.cs
  exact RdHead.congr (fun b hb => hag b hb.1) (RdHead.meet h1 h2)

set_option maxHeartbeats 4000000 in
/-- **`Once` at an alternative, trap arm, decided thread homed elsewhere** (module docstring). -/
theorem sl_once_trap_awayX (hA : P0.ArchTotal ar) {s s' : S} {a : A} {rp ep : U64}
    (F : SlOFX (st := st) ar K Locks m0 n (rp, ep) Cs Ω Sg Ac s)
    (Al : Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    (hS : SlTrap st s) (hh : L.mem s (affA (slThr st rp s)) ≠ L.cpu s)
    {r' : Bool × S × A} (h : interp st ar (R.syscall.handle_syscall_local n (rp, ep)) s' a = ok r') :
    Once st ar (SlRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_syscall_local n (rp, ep)) s' a := by
  have E := F.E
  have B := F.B
  have hX := B.regionOKX
  have I := F.I
  have hcur := sl_alt_cur F.P.preG Al
  have hTr := slTrap_alt F.P.preG.fl Al hcur
  have hN' : NodePlaced st K.heap.tcbs s' (L.cpu s') := by rw [Al.cpu]; exact NodePlaced.of_ksb Al.ksb E.hN
  have hc' : L.curW s' ∈ K.heap.tcbs := by rw [hcur]; exact E.hcT
  refine sl_pre_once (R0 := SlRN (st := st) K Locks s) (W0 := NU K) (fun q hq => ⟨hq.1, hq.2.2⟩)
    (fun q hq => hq.2) hA E.hT hN' hc' (sl_alt_preDecX ar F Al) (sl_alt_hhdX ar hA F Al) h ?_
    (fun hS' => absurd (hTr.2 hS) hS')
  intro _ X' a1' n' LP' h' Wd
  obtain ⟨X, LP, hag, hk, hc⟩ := sl_alt_preX ar hA F Al LP'
  have hag' : ∀ b, SlRN (st := st) K Locks s b → L.mem X' b = L.mem X b := fun b hb => hag b hb.1
  have DT : FltDecT (L := L) (SlRN (st := st) K Locks s) X' (L.curW s) :=
    FltDecT.congr hk hc hag' (FltDecT.meet (F.D.fT hS a X a1' LP) (FltDec.toT (fltDec_nuX ar hA B E LP)))
  rw [hcur] at h' ⊢
  refine fault_away_once (fun q hq => ⟨hq.1, hq.2.2⟩) DT ?_ h' Wd
  intro ptr bb x y g gr hcp hst'
  have DT0 := F.D.fT hS a X a1' LP
  have hc0 : obj.Slot.cap st (fhA (L := L) s) X = ok (capability.Cap.Endpoint ptr bb x y g gr) :=
    (cap_congr (hag _ DT0.fh.1) (hag _ DT0.fh.2)).symm.trans hcp
  have ets : L.mem X' (epTSA ptr) = L.mem X (epTSA ptr) := hag _ (DT0.ep ptr bb x y g gr hc0).1
  have hst : obj.Ep.state st ptr X = ok obj.EP_RECV := by
    rw [← ep_state_congr (st := st) ets, eq_of_spec_fd (obj.Ep.state.spec (L := L) X' ptr), hst']
  have lv := slLive_trap ar hA E.hT E.hN E.hcT I hS LP hc0 hst
  have af := I.af lv
  have e1 := slThr_hd_trap ar hA E.hT E.hN E.hcT I hS LP hc0
  have eh : L.mem X' (epHeadA ptr) = slThr st rp s := by
    rw [hag _ (DT0.ep ptr bb x y g gr hc0).2, e1]
  rw [eh]
  obtain ⟨-, hcX0, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  refine ⟨⟨af.1, nu_tcb hX (F.N.hthr lv) (o := 3520#u64) (by simp) (by simp) (by simp)⟩, fun e => hh ?_⟩
  rw [← lp_mem ar hA E.hT E.hN E.hcT LP af.1.1 af.2, ← hag _ af.1, e, hc, hcX0]

end altA

section altB
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64}
  {Cs Ω Sg Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`Once` at an alternative, ReplyRecv arm, decided thread homed elsewhere** (module docstring). -/
theorem sl_once_rr_awayX (hA : P0.ArchTotal ar) {s s' : S} {a : A} {rp ep : U64}
    (F : SlOFX (st := st) ar K Locks m0 n (rp, ep) Cs Ω Sg Ac s)
    (Al : Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    (hS : ¬ SlTrap st s) (hh : L.mem s (affA (slThr st rp s)) ≠ L.cpu s)
    {r' : Bool × S × A} (h : interp st ar (R.syscall.handle_syscall_local n (rp, ep)) s' a = ok r') :
    Once st ar (SlRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_syscall_local n (rp, ep)) s' a := by
  have E := F.E
  have B := F.B
  have hX := B.regionOKX
  have I := F.I
  have hcur := sl_alt_cur F.P.preG Al
  have hTr := slTrap_alt F.P.preG.fl Al hcur
  have hN' : NodePlaced st K.heap.tcbs s' (L.cpu s') := by rw [Al.cpu]; exact NodePlaced.of_ksb Al.ksb E.hN
  have hc' : L.curW s' ∈ K.heap.tcbs := by rw [hcur]; exact E.hcT
  refine sl_pre_once (R0 := SlRN (st := st) K Locks s) (W0 := NU K) (fun q hq => ⟨hq.1, hq.2.2⟩)
    (fun q hq => hq.2) hA E.hT hN' hc' (sl_alt_preDecX ar F Al) (sl_alt_hhdX ar hA F Al) h
    (fun hS' => absurd (hTr.1 hS') hS) ?_
  intro _ X' a1' LP' h' Wd
  obtain ⟨X, LP, hag, hk, hc⟩ := sl_alt_preX ar hA F Al LP'
  have hag' : ∀ b, SlRN (st := st) K Locks s b → L.mem X' b = L.mem X b := fun b hb => hag b hb.1
  have DT : RrDecT (L := L) (SlRN (st := st) K Locks s) X' (L.curW s) rp ep :=
    RrDecT.congr hk hc hag' (RrDecT.meet (F.D.rT hS a X a1' LP) (RrDec.toT (rrDec_nuX ar hA F hS LP)))
  rw [hcur] at h' ⊢
  refine rr_away_once (fun q hq => ⟨hq.1, hq.2.2⟩) DT ?_ h' Wd
  intro hu0
  have DT0 := F.D.rT hS a X a1' LP
  have e1 : L.mem X' (rTcbA rp) = slThr st rp s := by
    rw [hag _ DT0.rRt]; exact slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP
  rw [e1] at hu0 ⊢
  have lv := slLive_rr (st := st) hS hu0
  have af := I.af lv
  obtain ⟨-, hcX0, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  refine ⟨⟨af.1, nu_tcb hX (F.N.hthr lv) (o := 3520#u64) (by simp) (by simp) (by simp)⟩, fun e => hh ?_⟩
  rw [← lp_mem ar hA E.hT E.hN E.hcT LP af.1.1 af.2, ← hag _ af.1, e, hc, hcX0]

end altB

section R1
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout}
variable {A : Type} (ar : machine.Arch A)
variable {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}


set_option maxHeartbeats 4000000 in
/-- **The accepted ReplyRecv arm's words (but the buffer's) are `NU`** (`rrAcc_wn` with `NU` facts). -/
theorem rrAccNB_nuX (hA : P0.ArchTotal ar) {s : S} (F : SlOFX (st := st) ar K Locks m0 n found Cs Ω Sg Ac s)
    (hS : ¬ SlTrap st s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {u usc : U64}
    (hc : RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc) :
    RrAccNB (L := L) K.heap.scBits (NU K) (NU K) X (L.curW s) found.1 found.2 u usc := by
  have B := F.B
  have E := F.E
  have Hh := F.Hh
  have N := F.N
  have I := F.I
  have hK := B.regionOK
  have hX := B.regionOKX
  have C := slCom_nuX ar hA B E LP
  have D' := rrDR_nuX ar hA B E F.C hS LP
  obtain ⟨kX, cX, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have hc0 := E.hSt.1
  obtain ⟨hut, hus, -, -, -⟩ := E.hSu hS a X a1 LP u usc hc
  have nT : ∀ {t o : U64}, K.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu ht h1 h2 h3 h4
  have eu : u = slThr st found.1 s := by
    have h1 := obj.Reply.tcb.blk (st := st) X found.1
    rw [hc.tcb, WP.spec_ok, slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP] at h1
    exact h1
  have lv : SlLive st found.1 s := slLive_rr (st := st) hS (by rw [← eu]; exact u_ne0 hc.u0)
  have haf : L.mem s (affA (slThr st found.1 s)) = L.cpu s := by rw [← eu, affA_fld]; exact hus.1
  have eusc : usc = L.mem s (scA u) := by
    have h1 := hc.sc
    rw [tcb_sc_ok] at h1
    rw [← ok_inj_ff h1]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hut 3464#u64 (by simp) (by simp) (by simp)).2.2
      (nT hut (by simp) (by simp) (by simp) (by simp))
  have husc0 : usc ≠ 0#u64 := by
    obtain ⟨b, hb, hn⟩ := hc.sc0
    rw [eq_of_spec_fd (obj.Sc.is_null.spec usc)] at hb
    rw [← ok_inj_ff hb] at hn
    simpa using hn
  have Hs := Hh.usc hS lv haf (by rw [← eu, ← eusc]; exact husc0)
  rw [← eu, ← eusc] at Hs
  obtain ⟨hz, hin0, hmx0, hco⟩ := Hs
  have hrp := N.hrp hS
  have hepH := Hh.ep hS
  obtain ⟨-, aC, hinC, rC⟩ := sc_off hX hz (o := layout.sc.CORE) (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE])
  have eC : L.mem X (core.num.U64.wrapping_add usc layout.sc.CORE) = L.cpu X := by
    rw [lp_mem ar hA E.hT E.hN E.hcT LP aC (not_slDS_reg hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu
      (by rw [rC]; intro c h; cases h) (by rw [rC]; intro h; cases h)), cX]
    have e : core.num.U64.wrapping_add usc layout.sc.CORE = fld usc 16#u64 := by simp [fld, layout.sc.CORE]
    rw [e]
    exact hco
  obtain ⟨hzc, -, -, -⟩ := Hh.csc hS
  have eSt : L.mem X (scA (L.curW s)) = L.mem s (scA (L.curW s)) := by
    obtain ⟨-, -, aT, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    exact aT _ E.hcT 3464#u64 (by simp) (by simp) (by simp)
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have eRh : L.mem X (rhA (L := L) X) = L.mem s (rhA (L := L) s) := by
    show L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)
    rw [nX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])) (not_slDS_node E.hN E.hT E.hcT (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
  have tw : ∀ y, K.heap y = some .tcb → ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      NU K (core.num.U64.wrapping_add y o) := fun y hy o h1 h2 h3 => nu_tcb hX hy h1 h2 h3
  exact
  { nd := fun o h1 h2 => ⟨C.nd o h1 h2, C.nd o h1 h2⟩
    dt := C.dt
    cd := C.cd
    kr := by
      show NU K (core.num.U64.wrapping_add (L.ksb X) layout.ks.KERNEL_ROOT)
      rw [kX]
      exact B.nuKs E.hN (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
    tab := rdTabNX ar hA B F.Xe E Hh LP
    tSt := D'.tSt
    tSc := D'.tSc
    tMx := by
      rw [eSt]
      exact nu_scw hX hzc (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
    tIq := D'.tIq
    tMi := D'.tMi
    tBn := D'.tBn
    tPr := D'.tPr
    tReg := nuRegs hX hc0
    tBuf := ⟨_, tcb_slot_val _ _, tw _ hc0 3512#u64 (by simp) (by simp) (by simp),
      (nu_tslot hK hX hc0 (by simp [layout.tcb.SLOT_BUFFER])).1, (nu_tslot hK hX hc0 (by simp [layout.tcb.SLOT_BUFFER])).2⟩
    ntf := fun nt hnt hne => by
      have e1 := (eq_of_spec_fd (obj.Tcb.bound_ntfn.val X (L.curW s))).symm.trans hnt
      have en : nt = L.mem X (boundA (L.curW s)) := (ok_inj_ff e1).symm
      subst en
      exact D'.ntf (fun h0 => by rw [h0] at hne; simp at hne)
    wRp := tw _ hc0 3360#u64 (by simp) (by simp) (by simp)
    wEn := tw _ hc0 3496#u64 (by simp) (by simp) (by simp)
    wEp := tw _ hc0 3504#u64 (by simp) (by simp) (by simp)
    rRt := nu_rp hX hrp (o := layout.reply.TCB) (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
    rNx := nu_rp hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT])
    rPv := nu_rp hX hrp (o := layout.reply.PREV) (by simp [layout.reply.PREV]) (by simp [layout.reply.PREV])
    wNx := nu_rp hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT])
    wPv := nu_rp hX hrp (o := layout.reply.PREV) (by simp [layout.reply.PREV]) (by simp [layout.reply.PREV])
    wRt := nu_rp hX hrp (o := layout.reply.TCB) (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
    uSt := by rw [stA_eq]; exact tw _ hut 3328#u64 (by simp) (by simp) (by simp)
    uFt := ⟨tw _ hut 3376#u64 (by simp) (by simp) (by simp), tw _ hut 3376#u64 (by simp) (by simp) (by simp)⟩
    uSc := tw _ hut 3464#u64 (by simp) (by simp) (by simp)
    uPr := tw _ hut 3448#u64 (by simp) (by simp) (by simp)
    uAf := tw _ hut 3520#u64 (by simp) (by simp) (by simp)
    uDo := tw _ hut 3432#u64 (by simp) (by simp) (by simp)
    uIq := tw _ hut 3592#u64 (by simp) (by simp) (by simp)
    uMx := by
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
      exact nu_sc hX hz am hin
    uReg := nuRegs hX hut
    uYt := tw _ hut 3472#u64 (by simp) (by simp) (by simp)
    uFi := nuReg hX hut (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    uVt := by
      rw [vtA_slot]
      exact nu_tslot hK hX hut (by simp [layout.tcb.SLOT_VTABLE])
    eTS := nu_ep hX hepH (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])
    wEh := nu_ep hX hepH (o := layout.ep.HEAD) (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])
    wEt := nu_ep hX hepH (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])
    spo := by
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact nu_sc hX hz am hin
    cor := nu_sc hX hz aC hinC
    ccs := by
      rw [eC]
      exact C.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
    uHd := rdHead_hereN ar hA hX E Hh LP ⟨hz, hin0, hmx0, hco⟩
    uscA := scAccNN hX hz
    csc := by
      rw [ecs]
      obtain ⟨hz', -, -, -⟩ := Hh.cs
      exact scAccNN hX hz'
    tm := C.tm
    rh := fun h => by
      refine ⟨(C.rh h).1, ?_, (C.rh h).2⟩
      rw [eRh] at h ⊢
      obtain ⟨ht, hs⟩ := Hh.rh h
      have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
        lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
          (nT ht (by simp) (by simp) (by simp) (by simp))
      rw [eS]
      obtain ⟨hz', -, -, -⟩ := hs
      exact fun b ha hb => nu_sc hX hz' ha hb }

end R1

section hro
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {Locks : S → U64 → Prop} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`Once` of an accepted ReplyRecv run at its own entry state, no P3 bundle** (`sl_rr_once` at
`SlLX ∧ SlEntX`). -/
theorem sl_rr_onceX (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (a0 : A) (K : KLayout) (m : U64 → U64) :
    ∀ s a s1 a1, SlLX (L := L) K s → SlEntX st K s → SlQ st ar Locks n found Cs Ω Sg Ac K m s →
      ¬ SlTrap st s → syscall.handle_syscall_local st ar s a n found = ok (true, s1, a1) →
      Once st ar (SlRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_syscall_local n found) s a := by
  intro s a s1 a1 hJ hXe hq hS h0
  have F := slOFX_of ar hSt hA a0 hJ hXe hq
  have E := F.E
  have hX := F.B.regionOKX
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      syscall.handle_syscall_local mm ar x a n found = interp mm ar (R.syscall.handle_syscall_local n found) x a :=
    fun mm x a => congrFun (congrFun (sl_isProg S n found A ar mm) x) a
  have h := h0
  rw [hp] at h
  obtain ⟨rp, ep⟩ := found
  refine sl_pre_once (R0 := SlRN (st := st) K Locks s) (W0 := NU K) (fun q hq => ⟨hq.1, hq.2.2⟩)
    (fun q hq => hq.2) hA E.hT E.hN E.hcT (sl_alt_preDecX ar F (Alt.refl s)) (sl_alt_hhdX ar hA F (Alt.refl s)) h
    (fun hS' => absurd hS' hS) ?_
  intro _ X a1' LP h' Wd
  have hf : fastpath.reply_recv_found st ar X a1' (L.curW s) rp ep = ok (true, s1, a1) := by
    have h'' := h'
    rw [R.fastpath.reply_recv_found_eq] at h''
    obtain ⟨⟨b', s', a'⟩, hv, e⟩ := bind_shape h''
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact hv
  have hc0 := E.hSt.1
  refine rr_acc_once ar (R := SlRN (st := st) K Locks s) (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q)
    (fun q hq => ⟨hq.1, hq.2.2⟩) (fun q hq => hq.2.2) hA (E.hI a X a1' LP) (E.hPl hS a X a1' LP)
    (E.hrz hS a X a1' LP) (E.hy0r hS a X a1' LP) (E.hAs a X a1' LP)
    (fun u usc C => (F.P.hRWrG hS a X a1' LP u usc C).toNB.meet (rrAccNB_nuX ar hA F hS LP C))
    (fun u usc C => ?_) hf h' Wd
  have hw := E.hSu hS a X a1' LP u usc C
  have nSt : NU K (stA (L.curW s)) := by rw [stA_eq]; exact nu_tcb hX hc0 (o := 3328#u64) (by simp) (by simp) (by simp)
  have nBl : NU K (blockA (L.curW s)) := nu_tcb hX hc0 (o := 3336#u64) (by simp) (by simp) (by simp)
  have nSu : NU K (stA u) := by rw [stA_eq]; exact nu_tcb hX hw.1 (o := 3328#u64) (by simp) (by simp) (by simp)
  exact
    { tR := SWr.of_W (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q) ⟨hw.2.2.1, nSt⟩
      tN := SWr.of_W (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q) ⟨hw.2.2.1, nSt⟩
      tB := fun _ _ => gst_write (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q) ⟨hw.2.2.1, nSt⟩
      bl := fun _ => gst_write (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q) ⟨hw.2.2.2.1, nBl⟩
      uI := SWr.of_W (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q) ⟨hw.2.2.2.2, nSu⟩
      uR := SWr.of_W (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q) ⟨hw.2.2.2.2, nSu⟩
      uN := SWr.of_W (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q) ⟨hw.2.2.2.2, nSu⟩ }

set_option maxHeartbeats 4000000 in
/-- **`ReadOnce` of the syscall entry's tree at `SlLX ∧ SlEntX ∧ SlQ`** (`sl_hro2` without the bundle; no
premise but `hSt`, `hA`, `hm`, `a0`). -/
theorem sl_hroX (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (a0 : A) :
    ∀ K m, ReadOnce st ar (R.syscall.handle_syscall_local n found) (OwnMap.cls K) (OwnMap.ko K m)
      (· ∈ K.user) (fun s => SlLX (L := L) K s ∧ SlEntX st K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
      (SlRS (st := st) K Locks) := by
  intro K m s s' a r ⟨hJ, hXe, hq⟩ Al h
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      syscall.handle_syscall_local mm ar x a n found = interp mm ar (R.syscall.handle_syscall_local n found) x a :=
    fun mm x a => congrFun (congrFun (sl_isProg S n found A ar mm) x) a
  have F := slOFX_of ar hSt hA a0 hJ hXe hq
  have E := F.E
  obtain ⟨⟨b0, s1, a1⟩, h0, -⟩ := spec_ex_fd (Fl4Proofs.P0.syscall.handle_syscall_local.p0 st ar s a n found L.total hA)
  cases b0
  · -- declined at the entry
    by_cases hh : L.mem s (affA (slThr st found.1 s)) = L.cpu s
    · have g1 := sl_home ar hA F.P F.I F.D h0 Bool.false_ne_true hh
      have g2 := sl_dec_guardNX ar hA F h0 Bool.false_ne_true
      rw [hp] at g1 g2
      exact sl_once_accN ar hm (W0 := fun q => SlDS (L := L) s q ∧ True)
        (fun w hw => (SlDS.ws F.P.preG hw.1).1) Al
        (interp_guard_meet _ (sl_noZero n found) s a _ g1 g2)
    · obtain ⟨rp, ep⟩ := found
      by_cases hS : SlTrap st s
      · exact sl_once_trap_awayX ar hA F Al hS hh h
      · exact sl_once_rr_awayX ar hA F Al hS hh h
  · -- accepted at the entry
    by_cases hS : SlTrap st s
    · have g1 := sl_acc ar hA F.P h0
      have g2 := sl_trap_acc_guardNX ar hA F hS h0
      rw [hp] at g1 g2
      exact sl_once_accN ar hm (W0 := fun q => SlWS (st := st) K Locks s q ∧ True)
        (fun w hw => hw.1.1) Al (interp_guard_meet _ (sl_noZero n found) s a _ g1 g2)
    · have g1 := sl_acc ar hA F.P h0
      rw [hp] at g1
      exact once_agree hm (R0 := SlRS (st := st) K Locks s) (W0 := SlWS (st := st) K Locks s)
        (fun w hw => hw.1) (fun w hw => hw.1) _ (sl_noZero n found) s s' a _ ∅ ∅ Al.ksb Al.cpu Al.masks Al.read g1
        (sl_rr_onceX ar hSt hA a0 K m s a s1 a1 hJ hXe hq hS h0)

end hro

end Fl4Proofs.P2.PathObl

/-! ## Part 3: VCPU / PTE avoidance at `SlLX ∧ SlEntX` -/

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap

noncomputable section
open Classical

section av
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Ex : U64 → Prop} {K : KLayoutV} {Locks : S → U64 → Prop}
variable {A : Type}
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **`SlEntAllE` at `SlLX ∧ SlEntX ∧ SlQ`** (`slEntsX`, `slAccIn_of`). -/
theorem sl_entAllX (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (a0 : A) {s : S}
    (hJ : SlLX (L := L) K.toKLayout s) (hXe : SlEntX st K.toKLayout s)
    (hq : Fl4Proofs.P2.PathObl.SlQ st ar Locks n found Cs Ω Sg Ac K.toKLayout m0 s) :
    SlEntAllE (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s := by
  obtain ⟨N, Hh, Aj⟩ := slEntsX ar hSt hA a0 hJ hXe hq
  exact ⟨hq.1, N, Hh, slAccIn_of ar hA hJ.regionOK hJ.regionOKX (slSets_conv K.toKLayout) hq.1 N Hh Aj⟩

/-- **`sl_avoidVKE` for `sl_localPathX`** (no P3 bundle: the block's fit by `ksb_fit_of_np`, `HeapOK` by
`UserLayX.lp`). -/
theorem sl_avoidVKE_X (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (hK : RegionOKE Ex K) (hU : Fl4Proofs.P2.E2E.UserOK K.toKLayout)
    {P : S → Prop}
    (hJ : ∀ s, P s → SlLX (L := L) K.toKLayout s) (hXe : ∀ s, P s → SlEntX st K.toKLayout s)
    (hQ' : ∀ s, P s → Fl4Proofs.P2.PathObl.SlQ st ar Locks n found Cs Ω Sg Ac K.toKLayout m0 s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K.toKLayout Locks (L.wr s b v) = SlRS (st := st) K.toKLayout Locks s ∧
        SlWS (st := st) K.toKLayout Locks (L.wr s b v) = SlWS (st := st) K.toKLayout Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) P
        (SlRS (st := st) K.toKLayout Locks))
    (hks : ∀ s, P s → KsNoE Ex K) (hTN : ∀ s, P s → TabNoE (L := L) Ex s) (hUo : UserNoE Ex K) :
    Fl4Proofs.P2.E2EP.AvoidE Ex (sl_localPathX ar hSt hA hm a0 hK.base hU hJ hXe hQ' huf hpz) := by
  have hX : ∀ s, P s → RegionOKX K.toKLayout := fun s hP => (hJ s hP).regionOKX
  have hf : ∀ s, P s → K.ksb.val + 13568 ≤ 2 ^ 64 := fun s hP =>
    Fl4Proofs.P2.E2EP.ksb_fit_of_np (hJ s hP).np (hJ s hP).kc.1
  letI : LawfulStore (sl_localPathX ar hSt hA hm a0 hK.base hU hJ hXe hQ' huf hpz).st := L
  exact ⟨sl_avAccE (L := L) ar hA hK hX (fun s h => sl_entAllX ar hSt hA a0 (hJ s h) (hXe s h) (hQ' s h)) hks hf
      hTN (fun s h => (hJ s h).layP.heap) trivial hUo,
    sl_avDecE (L := L) ar hA hK hm hpz.choose_spec.1 hpz.choose_spec.2.1 hX
      (fun s h => sl_entAllX ar hSt hA a0 (hJ s h) (hXe s h) (hQ' s h)) hks hf,
    IsProg.on hpz.choose_spec.1 _ _ _⟩

/-- **`sl_avoidVKE_X` for the path restricted by `Q`**, the avoidance facts asked at `P ∧ Q` states only. -/
theorem sl_avoidVKE_rQX (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (hK : RegionOKE Ex K) (hU : Fl4Proofs.P2.E2E.UserOK K.toKLayout)
    {P : S → Prop}
    (hJ : ∀ s, P s → SlLX (L := L) K.toKLayout s) (hXe : ∀ s, P s → SlEntX st K.toKLayout s)
    (hQ' : ∀ s, P s → Fl4Proofs.P2.PathObl.SlQ st ar Locks n found Cs Ω Sg Ac K.toKLayout m0 s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K.toKLayout Locks (L.wr s b v) = SlRS (st := st) K.toKLayout Locks s ∧
        SlWS (st := st) K.toKLayout Locks (L.wr s b v) = SlWS (st := st) K.toKLayout Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) P
        (SlRS (st := st) K.toKLayout Locks))
    (Q : S → Prop) (hQ : ∀ s b v, P s → Q s → b ∈ K.user → Aligned b → Q (L.wr s b v))
    (hks : ∀ s, P s → Q s → KsNoE Ex K) (hTN : ∀ s, P s → Q s → TabNoE (L := L) Ex s) (hUo : UserNoE Ex K) :
    Fl4Proofs.P2.E2EP.AvoidE Ex
      ((sl_localPathX ar hSt hA hm a0 hK.base hU hJ hXe hQ' huf hpz).restrQ Q hQ) := by
  have hX : ∀ s, P s → RegionOKX K.toKLayout := fun s hP => (hJ s hP).regionOKX
  have hf : ∀ s, P s → K.ksb.val + 13568 ≤ 2 ^ 64 := fun s hP =>
    Fl4Proofs.P2.E2EP.ksb_fit_of_np (hJ s hP).np (hJ s hP).kc.1
  exact ⟨sl_avAccE (L := L) ar hA hK (P := fun s => P s ∧ Q s) (fun s h => hX s h.1)
      (fun s h => sl_entAllX ar hSt hA a0 (hJ s h.1) (hXe s h.1) (hQ' s h.1))
      (fun s h => hks s h.1 h.2) (fun s h => hf s h.1) (fun s h => hTN s h.1 h.2)
      (fun s h => (hJ s h.1).layP.heap) trivial hUo,
    sl_avDecE (L := L) ar hA hK hm hpz.choose_spec.1 hpz.choose_spec.2.1 (P := fun s => P s ∧ Q s)
      (fun s h => hX s h.1) (fun s h => sl_entAllX ar hSt hA a0 (hJ s h.1) (hXe s h.1) (hQ' s h.1))
      (fun s h => hks s h.1 h.2) (fun s h => hf s h.1),
    IsProg.on hpz.choose_spec.1 _ _ _⟩

/-- **`AvoidV` of `sl_localPathX`** (`Ex := VData K`): the block by `VcpuKs`, the ASID words by `TabNoV` [S] at
the `Pre` states, the user words by `UserObj`. -/
theorem sl_avoidVX (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (hK : RegionOKV K) (hU : Fl4Proofs.P2.E2E.UserOK K.toKLayout)
    {P : S → Prop}
    (hJ : ∀ s, P s → SlLX (L := L) K.toKLayout s) (hXe : ∀ s, P s → SlEntX st K.toKLayout s)
    (hQ' : ∀ s, P s → Fl4Proofs.P2.PathObl.SlQ st ar Locks n found Cs Ω Sg Ac K.toKLayout m0 s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K.toKLayout Locks (L.wr s b v) = SlRS (st := st) K.toKLayout Locks s ∧
        SlWS (st := st) K.toKLayout Locks (L.wr s b v) = SlWS (st := st) K.toKLayout Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) P
        (SlRS (st := st) K.toKLayout Locks))
    (hko : VcpuKs K) (hTN : ∀ s, P s → TabNoV (L := L) K s) (hUo : UserObj K) :
    AvoidV K (sl_localPathX ar hSt hA hm a0 hK.base hU hJ hXe hQ' huf hpz) := by
  have h := sl_avoidVKE_X (Ex := VData K) ar hSt hA hm a0 (regionOKE_vcpu hK) hU hJ hXe hQ' huf hpz
    (fun s hP o ho => notVData_of_noVcpu (noVcpu_ks hko
      (Fl4Proofs.P2.E2EP.ksb_fit_of_np (hJ s hP).np (hJ s hP).kc.1) ho))
    hTN (fun b hb => notVData_of_noVcpu (hUo b hb))
  exact ⟨h.acc, h.dec, h.prog⟩

end av

end

end Fl4Proofs.P2.E2EV

/-! ## Part 4: the cut with VCPUs present, the slot, its start fact and the tops -/

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld InW RegionOK LayP)
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

section cut
variable {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop}

open Fl4Proofs.P2.E2E in
/-- **Route C with VCPUs present**: an `own` path avoiding `VData K ∨ Ex` (and `VData K` alone, `AvoidV`) has a
VCPU cut-lift avoiding `Ex`. `avoidE_cutLiftV_empty` without `K.vcpus = ∅`: an alternative for the cut read set is
written back to one for the path's own (`alt_back`), whose declining run reads no `VData ∨ Ex` word; the two states
agree off `VData K`, so the run from the cut alternative reads the same words (`sim_off`). -/
theorem avoidE_cutLiftV_X {K : KLayoutV} {Ex : U64 → Prop} (hK : RegionOKV K) (hU : UserOKV K)
    (hko : ∀ x, VData K x → ko x = .free) (P : LocalPath (OwnMap.own K.toKLayout) cls ko User)
    (W : AvoidV K P) (h : AvoidE (fun b => VData K b ∨ Ex b) P) :
    AvoidE Ex (LocalPath.cutLiftV hK hU hko P W) := by
  letI := P.L
  have e' : rsE Ex (rsV K P.RS) = rsE (fun b => VData K b ∨ Ex b) P.RS :=
    funext fun s => funext fun x => propext
      ⟨fun h => ⟨h.1.1, fun h' => h'.elim h.1.2 h.2⟩,
        fun h => ⟨⟨h.1, fun h' => h.2 (Or.inl h')⟩, fun h' => h.2 (Or.inr h')⟩⟩
  obtain ⟨ha, hdec, hp⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show AvAccE Ex P.st (P.F P.ar) P.Acc P.Pre (rsV K P.RS) P.WS
    intro s a r hs hr hac
    rw [congrFun e' s]
    exact ha s a r hs hr hac
  · show @AvDecE P.S P.A P.X Ex P.st P.L (P.F P.ar) P.Acc cls ko User P.Pre (rsV K P.RS)
    intro s a r hs hr hd s' r' hA h'
    have e0 := fun (st' : machine.Store P.S) (N : Narrow P.st st') (σ : P.S)
      (g : AltCut K P.st P.Pre P.RS cls ko User σ) => W.progCut st' N σ g a
    obtain ⟨s'', hA'', hAg⟩ := alt_back P.side P.masks hs hA
    obtain ⟨r'', h''⟩ := P.total s'' a
    have g1 := hdec s a r hs hr hd s'' r'' hA'' h''
    have w1 := (interp_guard P.p s'' a r''
      ((e0 _ (Narrow.guard _ _ _) s'' (.inl ⟨s, hs, hA''⟩)).symm.trans g1)).2
    have w2 := dec_within W.progCut P.obl P.side W.dec hs hr hd hA'' h''
    have hO := P.once s s'' a r'' hs hA''
      ((e0 P.st (Narrow.self P.st) s'' (.inl ⟨s, hs, hA''⟩)).symm.trans h'')
    have S1 := sim_off P.masks (G := fun b => GV K b ∧ ¬ (VData K b ∨ Ex b)) (W := fun b => P.DS s b ∧ True)
      (fun b hb => hb.1) (fun b hb => P.obl.aligned s b hs (Or.inr hb.1)) P.p s' s'' a ∅ ∅ hAg
      (within_and P.p s'' a w2 w1) hO
    exact (e0 _ (Narrow.guard _ _ _) s' (.inr ⟨s, hs, hA⟩)).trans (guard_of_within P.p s' a r'
      ((e0 P.st (Narrow.self P.st) s' (.inr ⟨s, hs, hA⟩)).symm.trans h')
      (Within.mono (fun b hb hx => hb.2 (Or.inr hx)) (fun _ _ => trivial) P.p s' a S1.1))
  · show IsProgOn (P.F P.ar) P.ar P.st (@AltOf P.S P.st P.L P.Pre (rsE Ex (rsV K P.RS)) cls ko User) P.p
    rw [e']; exact hp

/-- **Route C with VCPUs present, restricted to `QPs` states** (`avoidE_cutLiftV_rJ` without `vcpus = ∅`). -/
theorem avoidE_cutLiftV_rJX {Kp : KLayoutP} {Ex : U64 → Prop} (hK : RegionOKV Kp.toKLayoutV)
    (hU : UserOKV Kp.toKLayoutV) (hko : ∀ x, VData Kp.toKLayoutV x → ko x = .free)
    (P : E2E.LocalPath (OwnMap.own Kp.toKLayout) cls ko (· ∈ Kp.user)) (W : AvoidV Kp.toKLayoutV P)
    (h : AvoidE (fun b => VData Kp.toKLayoutV b ∨ Ex b) (P.rJ Kp (fun b hb => Or.inl hb))) :
    AvoidE Ex ((LocalPath.cutLiftV hK hU hko P W).rJ Kp (fun b hb => Or.inl hb)) := by
  have e : (LocalPath.cutLiftV hK hU hko P W).rJ Kp (fun b hb => Or.inl hb) =
      LocalPath.cutLiftV hK hU hko (P.rJ Kp (fun b hb => Or.inl hb)) (avoidV_restrQ W) := rfl
  rw [e]
  exact avoidE_cutLiftV_X hK hU hko _ _ h

theorem regionOKE_vpte {K : KLayoutP} (hK : RegionOKP K) :
    RegionOKE (fun b => VData K.toKLayoutV b ∨ b ∈ K.ptes) K.toKLayoutV :=
  ⟨hK.base.base, fun b hb hx => hx.elim (notVData_of_region' hK.base hb) (fun hp => hb (hK.none b hp))⟩

theorem userNoE_vpte {K : KLayoutP} (hU : UserOKP K) (hUo : UserObj K.toKLayoutV) :
    UserNoE (fun b => VData K.toKLayoutV b ∨ b ∈ K.ptes) K.toKLayoutV :=
  fun b hb hx => hx.elim (notVData_of_noVcpu (hUo b hb)) (fun hp => (hU.kern b hp).2 hb)

end cut

section slS
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- **The syscall slot's `Pre` in a VM epoch**: `SlLX` (VX6), `SlEntX` [S], `TabNoV` [S] and the canonical `SlQ`. -/
def SlPreX (i : SlArg S) (K : KLayoutV) (m : U64 → U64) (s : S) : Prop :=
  SlLX (L := L) K.toKLayout s ∧ SlEntX st K.toKLayout s ∧ TabNoV (L := L) K s ∧
    Fl4Proofs.P2.PathObl.SlQ st ar i.Locks i.n i.found i.Cs i.Ω i.Sg i.Ac K.toKLayout m s

/-- **The syscall record at any layout** (module docstring): the epoch's layout facts, U1's core-set premise and
the lock premise at `SlLX` states. -/
structure SlPremX (i : SlArg S) (K : KLayoutV) : Prop where
  /-- `VcpuHeap` (from the epoch's `VtxBundle`). -/
  vh : VcpuHeap K
  /-- No VCPU meets the kernel-global area (from the epoch's `VtxBundle4`). -/
  ko : VcpuKsOff K
  /-- `UserObj` (from the epoch's `VtxBundle`). -/
  vu : UserObj K
  /-- [P] the glue's core set is below 64 (U1's `SlPremP6.cs`, unchanged). -/
  cs : ∀ c ∈ i.Cs, c.val < 64
  /-- [P] at `SlLX` states the locks are determined by the core, the kernel base and the aligned words off the
  user words (U1's `SlPremP6.kd`, read at `SlLX` states instead of bundle states). -/
  kd : ∀ s : S, SlLX (L := L) K.toKLayout s → KernDetS (L := L) K.user i.Locks s

variable {st ar}

/-- **`TabNoV` survives a user-word write** at a `SlLX` state (the ASID-table words are `NU`). -/
theorem tabNoV_wrX {K : KLayoutV} {s : S} (B : SlLX (L := L) K.toKLayout s) (h : TabNoV (L := L) K s)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64) : TabNoV (L := L) K (L.wr s b v) := by
  intro hi hhi
  have ea : L.mem (L.wr s b v) (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) :=
    wr_nu (K := K.toKLayout) hba hb v (B.nuAsid rfl hhi)
  rw [L.ksb_wr, ea]
  exact h hi hhi

/-- **The slot's `huf`** (`sl_hufX`, `SlEntX.wr`, `tabNoV_wrX`; the locks by the record's `kd` [P]). -/
theorem sl_hufVX (hA : P0.ArchTotal ar) {i : SlArg S} {K : KLayoutV} {m : U64 → U64} (h : SlPremX st i K) :
    ∀ s b v, SlPreX st ar i K m s → b ∈ K.user → Aligned b →
      SlPreX st ar i K m (L.wr s b v) ∧ i.Locks (L.wr s b v) = i.Locks s ∧
        SlRS (st := st) K.toKLayout i.Locks (L.wr s b v) = SlRS (st := st) K.toKLayout i.Locks s ∧
        SlWS (st := st) K.toKLayout i.Locks (L.wr s b v) = SlWS (st := st) K.toKLayout i.Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s := by
  intro s b v hP hb hba
  obtain ⟨hJ, hXe, hT, hq⟩ := hP
  obtain ⟨h1, h3⟩ := sl_hufX ar hA h.cs (m := m) h.kd s b v ⟨hJ, hq⟩ hb hba
  exact ⟨⟨h1.1, SlEntX.wr hJ hXe hb hba v, tabNoV_wrX hJ hT hb hba v, h1.2⟩, h3⟩

variable (st ar)

/-- **The syscall slot at any layout** (route C, `sl_localPathX` at `Pre := SlPreX`, no P3 bundle; `ReadOnce`
by `sl_hroX`, `AvoidV` by `sl_avoidVX`). -/
def slSlotX : SlotC (SlArg S) where
  Prem i K _ := SlPremX st i K
  path i K m hK hU h :=
    sl_localPathX (Locks := i.Locks) (n := i.n) (found := i.found) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg)
      (Ac := i.Ac) (m0 := m) (P := SlPreX st ar i K m) ar hSt hA hm a0 hK.base hU.base
      (fun _ hP => hP.1) (fun _ hP => hP.2.1) (fun _ hP => hP.2.2.2) (sl_hufVX hA h)
      ⟨_, sl_isProg S i.n i.found, sl_noZero i.n i.found,
        fun s s' a r hP => sl_hroX ar hSt hA hm a0 K.toKLayout m s s' a r ⟨hP.1, hP.2.1, hP.2.2.2⟩⟩
  Av i K m hK hU h :=
    sl_avoidVX ar hSt hA hm a0 hK hU.base _ _ _ _ _ (vcpuKs_ofKo h.ko) (fun s (hP : SlPreX st ar i K m s) => hP.2.2.1) h.vu

/-- **The syscall slot reads no PTE word under `QPs`** (route C with VCPUs: `avoidE_cutLiftV_rJX`, the path
avoiding `VData ∨ ptes` by `sl_avoidVKE_rQX`). -/
theorem sl_avoidPX (i : SlArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (slSlotX st ar hA hm hSt a0).Prem i K.toKLayoutV m) :
    AvoidP K (((slSlotX st ar hA hm hSt a0).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
      (· ∈ K.user)) (W : AvoidV K.toKLayoutV P),
      P = (slSlotX st ar hA hm hSt a0).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K ((LocalPath.cutLiftV hK.base hU.base (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv m) P W).rJ K
        (fun b hb => Or.inl hb)) := by
    rintro P W rfl
    apply avoidE_cutLiftV_rJX hK.base hU.base
    dsimp only [slSlotX]
    exact sl_avoidVKE_rQX ar hSt hA hm a0 (regionOKE_vpte hK) hU.base.base _ _ _ _ _ _ _
      (fun s (hP : SlPreX st ar i K.toKLayoutV m s) (hq : QPs K st s) o ho hx => hx.elim
        (notVData_of_noVcpu (noVcpu_ks (vcpuKs_ofKo h.ko) (ksb_fit_of_np hP.1.np hP.1.kc.1) ho))
        (hq.ks o ho))
      (fun s (hP : SlPreX st ar i K.toKLayoutV m s) (hq : QPs K st s) hi hhi =>
        ⟨fun hx => hx.elim (hP.2.2.1 hi hhi).1 (hq.tab hi hhi).1,
          fun lo hlo h0 hx => hx.elim ((hP.2.2.1 hi hhi).2 lo hlo h0) ((hq.tab hi hhi).2 lo hlo h0)⟩)
      (userNoE_vpte hU h.vu)
  exact key _ _ (SlotC.fam_pos _ _ h)

/-- **The syscall slot's family member reads no PTE word under `QPs`** (the empty path where `SlPremX` fails). -/
theorem sl_avoidPXf (i : SlArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) :
    AvoidP K (((slSlotX st ar hA hm hSt a0).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  by_cases hp : (slSlotX st ar hA hm hSt a0).Prem i K.toKLayoutV m
  · exact sl_avoidPX st ar hA hm hSt a0 i K m hK hU hp
  · exact avoidE_restrQ_noPre (SlotC.noPre (fl4Dflt st ar hm) _ hp)

/-- **The syscall slot under `ownP`**: lifted, restricted to `QPs` states, PTE-cut. -/
def slSlotPX : PathsP (SlArg S) :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (sl_avoidPXf st ar hA hm hSt a0 i K m hK hU)

/-- **The syscall record without the bundle's fields**: U1's `cs` [P] and `kd` [P] (at `SlLX` states). -/
structure SlPremX5 (i : SlArg S) (K : KLayoutV) : Prop where
  /-- [P] (U1's `SlPremP6.cs`). -/
  cs : ∀ c ∈ i.Cs, c.val < 64
  /-- [P] (U1's `SlPremP6.kd` at `SlLX` states). -/
  kd : ∀ s : S, SlLX (L := L) K.toKLayout s → KernDetS (L := L) K.user i.Locks s

/-- **The syscall entry's facts at a guest-running start state** [S] (module docstring). -/
structure SlEntV (K : KLayoutP) (j : SlArg S) (m : U64 → U64) (s : S) : Prop where
  /-- [S] VX6's `SlEntS` (core, fault-handler cap, CSpace walk, `reply_caps` typing). -/
  ents : SlEntS st K s
  /-- [S] `SlEntX` (current SC, ASID pools, IPC buffer). -/
  entx : SlEntX st K.toKLayout s
  /-- [S] no ASID-table or pool word is a VCPU data word (natively `VFacts`' `VcpuTabOff` / `PoolObj`). -/
  tab : TabNoV (L := L) K.toKLayoutV s
  /-- The canonical entry fact (as U1's sl start fact: `SlPreB` ∧ `SlEntL` [P] ∧ `SlSyncC` [P] ∧ `SlAccR` [P]). -/
  q : Fl4Proofs.P2.PathObl.SlQ st ar j.Locks j.n j.found j.Cs j.Ω j.Sg j.Ac K.toKLayout m s
  /-- [S] the PTE facts at the start state. -/
  qps : QPs K st s

variable {st ar}

theorem SlPremX5.toX {K : KLayoutP} {i : SlArg S} (h : SlPremX5 st i K.toKLayoutV) (E : VtxBundle4 st L K) :
    SlPremX st i K.toKLayoutV :=
  ⟨E.b.vh, E.ko, E.b.vu, h.cs, h.kd⟩

variable (st ar)

/-- **The syscall slot's start fact in a VM epoch** (module docstring): the record, a start state with `SlEntV`
([S] entry; `SlQ` as natively), its core, locks and memory link ([P], as `GlueAt`), the armed program the cut of
the lifted slot's body there. -/
def SlStartX (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : SlArg S) : Prop :=
  K.vcpus ≠ ∅ ∧ ∃ q0, (∃ h : SlPremX5 st j K.toKLayoutV, ∃ (σ : S) (a : A),
      SlEntV st ar K j m σ ∧ L.cpu σ = c ∧ j.Locks σ = hs ∧ (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
      ∀ E : VtxBundle4 st L K,
        q0 = ((slSlotX st ar hA hm hSt a0).liftAt j K.toKLayoutV m hK.base hU.base (h.toX E)).body σ a) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

variable {st ar hA hm hSt a0}

/-- **`StartAt` of the syscall slot** from its start fact and the epoch's bundle (`SlLX` by VX6's `SlLX.ofVtx`). -/
theorem slStartX_at {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : SlArg S} (E : VtxBundle4 st L K)
    (h : SlStartX st ar hA hm hSt a0 K μ hK hU c hs q j) :
    StartAt (slSlotPX st ar hA hm hSt a0 j K μ hK hU) c hs μ q := by
  obtain ⟨-, q0, ⟨hp, σ, a, he, hc, hl, hμ, hb⟩, rfl⟩ := h
  have hpre : SlPreX st ar j K.toKLayoutV μ σ :=
    ⟨SlLX.ofVtx E.b he.qps he.q.1 he.ents, he.entx, he.tab, he.q⟩
  have key : ∀ (Pf : E2E.LocalPath (ownV K.toKLayoutV) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user))
      (hAv : AvoidP K (Pf.rJ K (fun b hb => Or.inl hb))),
      Pf = (slSlotX st ar hA hm hSt a0).liftAt j K.toKLayoutV μ hK.base hU.base (hp.toX E) →
      StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv) c hs μ
        (cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c q0 ∅) := by
    rintro Pf hAv rfl
    refine ⟨σ, a, ⟨hpre, he.qps⟩, hc, hl, hμ, ?_⟩
    rw [body_cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv σ a, hb E, ← hc]
    rfl
  exact key _ _ (SlotC.lift_eq _ _ (hp.toX E))

/-- **`SlPremX5` is satisfiable at every layout** (any core count): the index with a constant lock map (the held
set `hs` of the start fact's `j.Locks σ = hs`) and any core set below 64 cores (`kernDetS_constV`). -/
theorem slPremX5_sat (K : KLayoutV) (n : I64) (found : U64 × U64) (Cs Ω Sg Ac : Set U64)
    (hCs : ∀ c ∈ Cs, c.val < 64) (hs : U64 → Prop) :
    ∃ i : SlArg S, i.Cs = Cs ∧ i.Locks = (fun _ => hs) ∧ SlPremX5 st i K :=
  ⟨{ n := n, found := found, Cs := Cs, Ω := Ω, Sg := Sg, Ac := Ac, Locks := fun _ => hs }, rfl, rfl,
    hCs, fun s _ => kernDetS_constV (L := L) (fun _ _ => rfl) s⟩

/-- **The start fact from its parts** (the armed program built from the epoch's bundle `E`; by proof irrelevance
it is the same for every bundle). -/
theorem slStartX_of {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {j : SlArg S} (E : VtxBundle4 st L K) (hv : K.vcpus ≠ ∅) (h : SlPremX5 st j K.toKLayoutV)
    {σ : S} (a : A) (he : SlEntV st ar K j μ σ) (hc : L.cpu σ = c) (hl : j.Locks σ = hs)
    (hμ : ∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = μ x) :
    SlStartX st ar hA hm hSt a0 K μ hK hU c hs
      (cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c
        (((slSlotX st ar hA hm hSt a0).liftAt j K.toKLayoutV μ hK.base hU.base (h.toX E)).body σ a) ∅) j :=
  ⟨hv, _, ⟨h, σ, a, he, hc, hl, hμ, fun _ => rfl⟩, rfl⟩


end slS

/-! ## Part 5: the tops -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The start facts with the syscall slot in VM epochs too** (VX5's, plus `SlStartX`). -/
def StartVX7 {ιN : Type}
    (SFN : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ιN → Prop)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : (((((ιN ⊕ VxArg S) ⊕ VtArg S) ⊕ IoArg S) ⊕ StArg S) ⊕ IrqArg S) ⊕ SlArg S → Prop
  | .inl i => StartVX5 st ar hA hm SFN Ch K m hK hU c hs q i
  | .inr j => SlStartX st ar hA hm hSt a0 K m hK hU c hs q j

/-- **FL4 end to end with native and VM epochs; the VM-exit, VM-timer, I/O-port, `TCB_SetTimer`, timer-interrupt
and syscall slots in VM epochs; generic in the native family** (`serializable_fl4_localVX5G` with `slSlotPX`
added). -/
theorem serializable_fl4_localVX7G (P : LocPlat st arI AR MR) {ιN : Type} (LN : PathsP ιN)
    {SFN : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ιN → Prop}
    (hSFN : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SFN Ch K s.mem hK hU c hs q i → StartAt (LN i K s.mem hK hU) c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4 (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum LN
        (vxSlotPV st ar hA hm)) (vtSlotPV st ar hA hm)) (ioSlotPX st ar hA hm)) (stSlotPX st ar hA hm))
        (irqSlotPX st ar hA hm)) (slSlotPX st ar hA hm hSt a0))
      (StartVX7 st ar hA hm hSt a0 SFN) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  have hX := (execVX_of_VX4 hc0.1 h).1
  refine serializable_e2eP _ h0 hA0 hK0 hU0 hM0 (execP_of_VX P ?_ h0 hA0 hB hc0 hM0 hX).1 hq
  intro Ch K s hK hU c hs q i hN hsf
  obtain ⟨hV, hsf⟩ := hsf
  rcases i with (((((i | j) | j) | j) | j) | j) | j
  · have hsf' : K.vcpus = ∅ ∧ SFN Ch K s.mem hK hU c hs q i := hsf
    obtain ⟨nv, hsf'⟩ := hsf'
    obtain ⟨hX, hE⟩ := hN nv
    exact hSFN Ch K s hK hU c hs q i hX.chainOf hE hsf'
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

/-- **FL4 end to end with every U1 slot in native epochs and the VM-exit, VM-timer, I/O-port, `TCB_SetTimer`,
timer-interrupt and syscall slots in VM epochs** (module docstring): `serializable_fl4_localVX5` with `slSlotPX`
added (record `SlPremX5`: U1's `cs` [P], `kd` [P] at `SlLX` states; start entry `SlEntV` [S] with U1's `SlQ`).
No new [J], no [W]. -/
theorem serializable_fl4_localVX7 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4 (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum
        (fl4LocW11JA st ar hA hm hSt a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA hm) (invSlotU st ar hA hm)) (cmSlotU st ar hA hm)))
        (vxSlotPV st ar hA hm)) (vtSlotPV st ar hA hm)) (ioSlotPX st ar hA hm)) (stSlotPX st ar hA hm))
        (irqSlotPX st ar hA hm)) (slSlotPX st ar hA hm hSt a0))
      (StartVX7 st ar hA hm hSt a0 (StartU1 st ar hA hm hSt a0 arI AR MR (StartInvU2 st ar hA hm)))
      P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  refine serializable_fl4_localVX7G st ar hA hm hSt a0 P _ ?_ h0 hA0 hB hc0 hM0 h hq
  intro Ch K s hK hU c hs q i hC hE hsf
  rcases i with i | ((j | j) | j)
  · exact startAt_U st ar hA hm hSt a0 P hIoa hC hE hsf
  · exact delPteStart_at st ar hA hm hC hE hsf
  · exact invStartU2_at st ar hA hm hC hE hsf
  · exact cmStartU2_at st ar hA hm hC hE hsf

end top

end
end Fl4Proofs.P2.E2EP
