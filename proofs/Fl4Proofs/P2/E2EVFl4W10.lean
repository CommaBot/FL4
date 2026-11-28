/-
P2 (line iolay, gen 2): **`serializable_fl4_localW10`: the VM slots' residual [J] shrunk** (new definitions only,
on top of W9; no existing statement changes; no `kernel_entry_reach*` touched).

## 1. The index at `OmegaU` is needed, not optional

vmF's `hyp.asid` and vmR's `mid` ask `AsidOff Ω Sg` at the index's `Ω`, whose first conjunct is "every ASID-table
word is an `Ω` word". With `BunIx` (`Ω = Heap.omega H`, the words of heap objects) this asks the 2048 table words at
`ksb + 288000` to lie in some reply / SC / `other` / notification object of `H`; P3 places them only in `VsU`
(`TopPlaced.vo`: outside every object of `Zx.th`; untyped memory is kept off `[ksb, ksb + 304384)` by
`UtKsApart`), and nothing places a heap object there. So at `Ω = H.omega` the fields are not derivable (and are
expected false: the table is kernel-image memory). P3 proves `AsidOff` at the bundle witness's `OmegaU`
(`JAtZ.asidOffU`). Hence vmF and vmR move to famw's `OmegaU` convention: vmF by **`BunIxV`** (`BunIxU` plus
`U = BufU`, the buffer words P3 keeps outside the objects and off `OmegaU`, `JAtZ.bufU_out`), vmR by famw's
**`BunIxU`** (vmR has no `U`). `bunIxV_of`: satisfiable at every bundle state (a choice of index).
`BunIxU.vmBase`: `VmBase` at `OmegaU` from the bundle (`bxiU`; `csc` / `hcsc` from `JAtZ.entryInv`, which do not
read `Ω`; `curAff` / `cscCore` / `tmc` as W7; `VmLay` from W9).

## 2. vmF `hyp` derived (`SlJAtZ.footU`)

`VmFootHyps` at the state after `update_timestamp`, at `Ω = OmegaU`, `U = BufU`: `bxi` by P1's
`update_timestamp.entry` from `EntryInv` at `OmegaU` (`JAtZ.entryInvU`: `bxiU` + `entryInv`'s `Ω`-free tail); the
rest at the entry state, carried over `utW` (it writes the node's `CUR_TIME` / `CONSUMED` only; every other word
read is a TCB word, a slot word, an ASID-table word or a buffer word, none a node word: `ne_ut_of_region`):
`nb` from `run` (W9's `chain_run`); `cap` from `JPlaced.typed` at the fault-handler slot; `user` / `buf` from
`JAtZ.bufU_out` / `JAtZ.bufOK`; `asid` from `JAtZ.asidOffU`.

## 3. vmR: `hNt`, `nbt` derived; `mid` split

* `hNt` (**`SlJAt.hNtR`**): from `LayP` (heap alignment / fit, `LayP.region_ntfn`).
* `nbt` (**`BXI.nbt`**): P1's carried bound-link symmetry `ScExtra0.bs : BndS` (`tb`: a TCB's bound notification
  names it back in `BOUND_TCB`).
* `mid`'s `BXI` and `AsidOff` at the dispatch state (**`lp_bxiAsid`**): `EntryInv` at `OmegaU` through the
  `FAULT_IP` write (`EntryInv.set_reg`) and `update_timestamp.entry`; `AsidOff` carried over the two writes (the
  table words are in no region, the written words are a TCB register word and two node words).
* What stays: **`rr`** [J] = for the ReplyRecv checks at the dispatch state, `RRPl` and the receiver's
  `YIELD_TO = 0`. `RRPl` needs no missing fact: P1's `rrPl_lkG` builds it from `BXI` (now derived), `JAtZ.lkTyped`
  and `reply_caps` at the dispatch state, both of which need a frame lemma over `LocalPre`'s two writes (CSpace
  walk words and the `REPLY` register are no node / `FAULT_IP` words) — not written this generation.

## 4. `hyt` (vmF) and the receiver's `YIELD_TO` (vmR `rr`): stay [J]; missing fact named

Both ask that an endpoint's head thread blocked on receive has `YIELD_TO = 0`. Missing: a P1 (or P3 spec) invariant
"`YIELD_TO ≠ 0` ⇒ the thread is not blocked on an endpoint" (P1 does not track `YIELD_TO`; P3's `SInv` has no
`tcbYieldTo` clause). **True at reachable states** by the spec (Fl4Spec/Schedule.lean `schedContextYieldTo`: the only
setter of `tcbYieldTo := some _` acts on the caller `ct`, which stays `running` and is enqueued; Fl4Spec/Tcb.lean
`activateThread` runs `completeYieldTo` — clearing it — before a thread returns to user mode, and a thread becomes
`blockedOnReceive` only by its own receive; fl4-core: `schedcontext::yield_switches`, `sched::activate_thread`, see
`VmFPre.hyt`'s docstring). No counterexample state exists; discharging it is a new spec-invariant preservation proof
across P3's whole step relation.

## 5. Entry facts and the top

* vmF **`VmFEntJ10`** = `nv`, `BunIxV`, `hct` [P], `lk` [P], `hyt` [J], `gl` [P] (`hyp` derived).
* vmR **`VmREntJ10`** = `BunIxU`, `hct` [P], `rr` [J], `lk` / `nb` [P], `fd` (`mid`'s BXI / AsidOff, `hNt`, `nbt`
  derived).
* `StartP3W10` (W9's with vmF / vmR at these), `startAt_P3W10` (vmF / vmR straight to `startAt_P3W`'s path `Pre`),
  **`serializable_fl4_localW10`** (same premises as W9).

| slot | removed (vs W9's entry facts) | added |
|---|---|---|
| vmF | `hyp` [J]; `BunIx` (`Ω = H.omega`) | `BunIxV` (index convention at `OmegaU` / `BufU`) |
| vmR | `mid` [J] → `rr` [J] (RRPl + receiver `YIELD_TO` only), `hNt` [J], `nbt` [J]; `BunIx` | `BunIxU` (convention) |
-/
import Fl4Proofs.P2.E2EVFl4W9
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs

section nd
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {T : Set U64} {s : S}

/-- **A word whose region is no node is neither word `update_timestamp` writes.** -/
theorem ne_ut_of_region (hk : K.ksb = L.ksb s) (hc : (L.cpu s).val < K.ncores) (hN : NodePlaced st T s (L.cpu s))
    {b : U64} (hr : ∀ c, region K b ≠ .node c) : b ≠ ctA (L := L) s ∧ b ≠ cnA (L := L) s := by
  have hin : ∀ o : U64, o.val < 4288 → InNode K (L.cpu s) (L.nodeAt s (L.cpu s) o) := fun o ho => by
    have hv := nodeAt_val hN ho
    refine ⟨hc, ?_, ?_⟩ <;> rw [hv, hk] <;> unfold LawfulStore.nodeBase <;> omega
  constructor
  · rintro rfl; exact hr _ (slj_region_node (hin _ (by simp [layout.node.CUR_TIME])))
  · rintro rfl; exact hr _ (slj_region_node (hin _ (by simp [layout.node.CONSUMED])))

end nd

section foot
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit}

/-- **`EntryInv` at `OmegaU`**: `bxiU` and `entryInv`'s `Ω`-free tail. -/
theorem SlJAtZ.entryInvU (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    EntryInv st (Heap.tcbs K.heap) Cx (OmegaU K.heap Zx (L.ksb s) σ) K.heap (Heap.frame K.heap)
      (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ax s := by
  have hIU := B.j.bxiU
  have hE0 := B.j.entryInv B.res
  exact ⟨hIU.1, hIU.2.1, hIU.2.2.1, hIU.2.2.2.2, hE0.2.2.2.2⟩

variable {A : Type} {ar : machine.Arch A}

/-- **vmF's `hyp` at `OmegaU` / `BufU`** (module docstring, item 2). -/
theorem SlJAtZ.footU (hA : P0.ArchTotal ar) (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ)
    (hrun : L.mem s (Fl4Proofs.P1.stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (Fl4Proofs.P1.stA (L.curW s)) = sched.TS_RUNNING) :
    ∀ a s1 a1, sched.update_timestamp st ar s a = ok (s1, a1) →
      VmFootHyps (L := L) (Heap.tcbs K.heap) Cx (OmegaU K.heap Zx (L.ksb s) σ) (BufU Zx σ) (Heap.frame K.heap)
        (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) Ax K.heap (Heap.scBits K.heap) s1 := by
  intro a s1 a1 eu
  have hEU := B.entryInvU
  have hIU := B.j.bxiU
  have hp := post_of_ok (sched.update_timestamp.entry hA s a hEU) eu
  obtain ⟨hI1, -⟩ := hp
  obtain ⟨hT, hN, hcT⟩ := hIU.tcbNode
  obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  rw [update_timestamp_ok (ar := ar) hN hn] at eu
  have eS := (Prod.mk.inj (ok_inj_ff eu)).1
  subst eS
  have hP := B.layP
  have X := B.regionOKX
  have hk : K.ksb = L.ksb s := B.ksb.symm
  have hc : (L.cpu s).val < K.ncores := B.cpu
  have hcH : K.heap (L.curW s) = some .tcb := B.j.kern.curH
  refine ⟨hI1, ?_, ?_, ?_, ?_, ?_⟩
  · -- nb
    rw [ut_cur hN n, Fl4Proofs.P1.stA_eq, ut_tcb hN hT n hcT (Kx := 3328#u64) (by simp) (by simp), ← Fl4Proofs.P1.stA_eq]
    intro hb
    have hv := Calm.val (v := L.mem s (Fl4Proofs.P1.stA (L.curW s))) hrun
    rcases hb with e | e | e <;> rw [e] at hv <;>
      simp [sched.TS_BLOCKED_ON_SEND, sched.TS_BLOCKED_ON_RECV, sched.TS_BLOCKED_ON_NTFN] at hv
  · -- cap
    rw [ut_cur hN n, Fl4Proofs.P1.tcb_slot_val, WP.spec_ok]
    have hFH : layout.tcb.SLOT_FAULT_HANDLER.val < 6 := by unfold layout.tcb.SLOT_FAULT_HANDLER; simp
    obtain ⟨hs, -, r8, -, a0, a8⟩ := X.tslot _ hcH _ hFH
    have r0 : region K (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) =
        .slot (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) := hP.region_slot hs
    have n0 := ne_ut_of_region hk hc hN (b := slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER)
      (fun c => by rw [r0]; intro e; cases e)
    have n8 := ne_ut_of_region hk hc hN
      (b := core.num.U64.wrapping_add (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) 8#u64)
      (fun c => by rw [r8]; intro e; cases e)
    have ecap : obj.Slot.cap st (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) (utW (L := L) s n) =
        obj.Slot.cap st (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) s := by
      unfold obj.Slot.cap
      rw [L.read_pair_eq, L.read_pair_eq, utW_mem hN n a0 n0.1 n0.2, utW_mem hN n a8 n8.1 n8.2]
    obtain ⟨Tr, Cq, hJ⟩ := B.j.jpl
    have hsS := hs
    rw [B.slots] at hsS
    have hcv : obj.Slot.cap st (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) s =
        ok (Fl4Proofs.P3.capV (L.mem s) (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER)) := by
      rw [Fl4Proofs.P3.slot_cap_eq]; exact Fl4Proofs.P3.capAt_capV _ _
    rw [ecap, hcv, WP.spec_ok]
    exact hJ.typed _ hsS
  · -- user
    intro b hb
    exact ⟨(B.j.bufU_out hb).1.ksb (utW_ksb s n), (B.j.bufU_out hb).2⟩
  · -- buf
    intro y hy
    have e1 : L.mem (utW (L := L) s n) (ibWordA y) = L.mem s (ibWordA y) := by
      unfold ibWordA; exact ut_tcb hN hT n hy (Kx := 3512#u64) (by simp) (by simp)
    have e2 : L.mem (utW (L := L) s n) (sbWordA y) = L.mem s (sbWordA y) := by
      rw [sbWordA_eq]; exact ut_tcb hN hT n hy (Kx := 64#u64) (by simp) (by simp)
    have e3 : L.mem (utW (L := L) s n) (core.num.U64.wrapping_add (sbWordA y) 8#u64) =
        L.mem s (core.num.U64.wrapping_add (sbWordA y) 8#u64) := by
      rw [sbWordA8_eq]; exact ut_tcb hN hT n hy (Kx := 72#u64) (by simp) (by simp)
    rw [lookup_ipc_buffer_same (s := s) (s' := utW (L := L) s n) (t := y) ⟨e1, e2, e3⟩]
    exact B.j.bufOK hy
  · -- asid
    intro hi hhi
    have hA0 := B.j.asidOffU hi hhi
    rw [utW_ksb]
    obtain ⟨rN, aT⟩ := X.asidT hi hhi
    rw [hk] at rN aT
    have nT := ne_ut_of_region hk hc hN (b := atAF (L.ksb s) hi) (fun c => by rw [rN]; intro e; cases e)
    rw [utW_mem hN n aT nT.1 nT.2]
    exact hA0

/-- **`mid`'s `BXI` and `AsidOff` at the dispatch state** (module docstring, item 3). -/
theorem SlJAtZ.lpBxiAsid (hA : P0.ArchTotal ar) (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    ∀ a s2 a2, LocalPre (st := st) ar s a (s2, a2) →
      BXI st (Heap.tcbs K.heap) Cx (OmegaU K.heap Zx (L.ksb s) σ) K.heap (Heap.frame K.heap) (Heap.replies K.heap)
        (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ax s2 ∧
      AsidOff (L := L) (OmegaU K.heap Zx (L.ksb s) σ) (Heap.frame K.heap) s2 := by
  intro a s2 a2 hLP
  obtain ⟨t, nx, s1, et, -, es1, eu⟩ := hLP
  have et' : t = L.curW s := (ok_inj_ff ((cur_thread_ok (L := L) s).symm.trans et)).symm
  subst et'
  have hEU := B.entryInvU
  have hIU := B.j.bxiU
  obtain ⟨hT, hN, hcT⟩ := hIU.tcbNode
  have hr : layout.reg.FAULT_IP.val < 384 := by simp [layout.reg.FAULT_IP]
  have hE1 := post_of_ok (EntryInv.set_reg hEU hcT hr (v := core.num.U64.wrapping_sub nx 2#u64)) es1
  have hp := post_of_ok (sched.update_timestamp.entry hA s1 a hE1) eu
  obtain ⟨hI2, -⟩ := hp
  refine ⟨hI2, ?_⟩
  obtain ⟨Kr, hKr, e1⟩ := post_of_ok (obj.Tcb.set_reg.wrK s (L.curW s) layout.reg.FAULT_IP
    (core.num.U64.wrapping_sub nx 2#u64) (hT _ hcT) hr) es1
  subst e1
  have hN1' := hE1.1.choose_spec.choose_spec.nodes _ hE1.1.choose_spec.choose_spec.cur
  obtain ⟨⟨n, a3⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  rw [update_timestamp_ok (ar := ar) hN1' hn] at eu
  have eS := (Prod.mk.inj (ok_inj_ff eu)).1
  subst eS
  have X := B.regionOKX
  have hk : K.ksb = L.ksb s := B.ksb.symm
  have hc : (L.cpu s).val < K.ncores := B.cpu
  have hfv : Kr.val = 256 + 8 * layout.reg.FAULT_IP.val := hKr
  have hfv' : layout.reg.FAULT_IP.val = 17 := by simp [layout.reg.FAULT_IP]
  intro hi hhi
  have hA0 := B.j.asidOffU hi hhi
  rw [utW_ksb, L.ksb_wr]
  obtain ⟨rN, aT⟩ := X.asidT hi hhi
  rw [hk] at rN aT
  have nT := ne_ut_of_region hk hc hN (b := atAF (L.ksb s) hi) (fun c => by rw [rN]; intro e; cases e)
  have hrT := (X.tcbW _ B.j.kern.curH Kr (by omega) (by omega) (by omega))
  have nW : core.num.U64.wrapping_add (L.curW s) Kr ≠ atAF (L.ksb s) hi := by
    intro e; rw [e, rN] at hrT; cases hrT.1
  have em : L.mem (utW (L := L) (L.wr s (core.num.U64.wrapping_add (L.curW s) Kr) (core.num.U64.wrapping_sub nx 2#u64)) n)
      (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) := by
    rw [utW_mem hN1' n aT (by rw [ctA_wr]; exact nT.1) (by rw [cnA_wr]; exact nT.2)]
    exact mem_wr_ne' hrT.2.2 aT nW
  rw [em]
  exact hA0

end foot

section ntfn
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {Kl : KLayout} {s : S}

/-- **vmR's `hNt` from the bundle** (module docstring, item 3). -/
theorem SlJAt.hNtR (hJ : SlJAt (L := L) Kl s) :
    ∀ p ∈ Kl.heap.ntfns, Kl.heap p = some .ntfn ∧ p.val % 64 = 0 ∧ p.val + 64 ≤ 2 ^ 64 ∧
      ∀ b, InW p 64 b → region Kl b = .ntfn p := by
  intro p hp
  have hp' : Kl.heap p = some .ntfn := hp
  have hP := hJ.layP
  have hf := hP.heap.fits p _ hp'
  have ha := hP.heap.align p _ hp'
  simp only [HKind.bits] at hf ha
  exact ⟨hp', by simpa using ha, by simpa using hf, fun b hb => hP.region_ntfn hp' (by simpa using hb)⟩

/-- **vmR's `nbt` from P1's bound-link symmetry** (`BndS.tb`). -/
theorem BXI.nbt (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hcT : L.curW s ∈ T) :
    L.mem s (boundA (L.curW s)) ≠ 0#u64 → L.mem s (fld (L.mem s (boundA (L.curW s))) 24#u64) = L.curW s := by
  intro h0
  have h := hI.2.2.1.2.2.toScExtra0.bs.tb _ hcT h0
  have e : ntfnBtA (L.mem s (boundA (L.curW s))) = fld (L.mem s (boundA (L.curW s))) 24#u64 := by
    unfold ntfnBtA fld; congr 1; simp [layout.ntfn.BOUND_TCB]
  rw [← e]; exact h

end ntfn

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot InW InNode)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

/-! ## 1. The indices at `OmegaU` -/

section bun
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Kl : OwnMap.KLayout} {T Cs Ω U : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
  {Ac : Set U64} {s : S}

/-- **vmF's index: the bundle's sets, `Ω` the witness's `OmegaU` and `U` its `BufU`** (module docstring, item 1;
a choice of index: `bunIxV_of`). -/
structure BunIxV (Kl : OwnMap.KLayout) (T Cs Ω U : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat)
    (Ac : Set U64) (s : S) : Prop where
  hKH : Kl.heap = H
  hT : T = H.tcbs
  hSg : Sg = H.frame
  hRp : Rp = H.replies
  hScs : Scs = H.scs
  hNt : Nt = H.ntfns
  hZ : Z = H.scBits
  /-- Clause 7 at the state, `Cs` / `Ac` its ghosts, `Ω` / `U` its witness's `OmegaU` / `BufU`. -/
  ac : ∃ (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
    SlJAtZ (L := L) arI AR Zx Cs Ac Lst D Kl s a' σ ∧ Ω = Fl4Proofs.P3.OmegaU Kl.heap Zx (L.ksb s) σ ∧
      U = Fl4Proofs.P3.BufU Zx σ

/-- **Some index sets satisfy `BunIxV` at every bundle state.** -/
theorem bunIxV_of (h : SlJAt (L := L) Kl s) : ∃ Cs Ac Ω U, BunIxV (L := L) Kl Kl.heap.tcbs Cs Ω U Kl.heap
    Kl.heap.frame Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  exact ⟨Cx, Ax, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨A', arI, AR, Zx, Lst, D, a', σ, B, rfl, rfl⟩⟩

theorem BunIxV.toU (BV : BunIxV (L := L) Kl T Cs Ω U H Sg Rp Scs Nt Z Ac s) :
    BunIxU (L := L) Kl T Cs Ω H Sg Rp Scs Nt Z Ac s := by
  obtain ⟨hKH, hT, hSg, hRp, hScs, hNt, hZ, ⟨A', arI, AR, Zx, Lst, D, a', σ, B, hΩ, -⟩⟩ := BV
  exact ⟨hKH, hT, hSg, hRp, hScs, hNt, hZ, ⟨A', arI, AR, Zx, Lst, D, a', σ, B, hΩ⟩⟩

/-- **`VmBase` at `OmegaU` from the bundle and `run`** (module docstring, item 1). -/
theorem BunIxU.vmBase (BU : BunIxU (L := L) Kl T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING) :
    VmBase st Kl T Cs Ω H Sg Rp Scs Nt Z Ac s := by
  have hS := BU.slJAtS
  have hac := hS.curAffCore
  have hce := curEnt_of hS hrun
  have hJ := hS.slJAt
  have hI := BU.bxi
  have haff := BU.aff
  obtain ⟨hKH, hT, hSg, hRp, hScs, hNt, hZ, ⟨A', arI, AR, Zx, Lst, D, a', σ, B, hΩ⟩⟩ := BU
  subst hKH hT hSg hRp hScs hNt hZ hΩ
  have hE := B.j.entryInv B.res
  exact
  { bxi := hI
    csc := hE.csc
    hcsc := hE.hcsc
    run := hrun
    lay := PathObl.SlJAt.vmLay hJ
    kb := B.ksb.symm
    nc := B.cpu
    hT := fun t ht => ht
    hSc := fun c ⟨z, hz⟩ => by simp only [Heap.scBits, hz]
    curAff := hac.1
    cscCore := hac.2
    affSc := haff
    tmc := hce.tmc }

/-- `RdTab` from any `BXI` at a bundle state (W7's `rdTab_ofBun` without `BunIx`). -/
theorem rdTab_of (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hJ : SlJAt (L := L) Kl s) {Locks : S → U64 → Prop} :
    RdTab (L := L) (IoRS (st := st) Kl Locks s) s := by
  have hY := irqLayK_of_slJAt hI hJ
  intro hi hhi
  exact ⟨⟨(hY.tab hi hhi).1.1, (hY.tabU hi hhi).1, rperm_none (hY.tab hi hhi).1.2 _⟩,
    fun lo hlo hne => ⟨((hY.tab hi hhi).2 lo hlo hne).1, (hY.tabU hi hhi).2 lo hlo hne,
      rperm_none ((hY.tab hi hhi).2 lo hlo hne).2 _⟩⟩

end bun

/-! ## 2. Entry facts -/

section ent
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **vmF's start entry facts** (module docstring, item 5): `hyp` derived, the index at `OmegaU` / `BufU`. -/
structure VmFEntJ10 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : VmFArg S) (K : KLayoutV) (s : S) : Prop where
  /-- No VCPU in the layout (the glue's layout choice at P3 scope). -/
  nv : K.vcpus = ∅
  /-- Index convention at `OmegaU` / `BufU` (a choice of index: `bunIxV_of`). -/
  ix : BunIxV (L := L) K.toKLayout i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [P] as `VmFPre.lk`. -/
  lk : ∀ a s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
    FaultChecks st s1 (L.curW s1) ptr badge dest r → i.Locks s ptr ∧ i.Locks s r
  /-- [J] as `VmFPre.hyt` (module docstring, item 4: true at reachable states; the missing invariant is
  "`YIELD_TO ≠ 0` ⇒ not blocked on an endpoint"). -/
  hyt : ∀ a s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
    FaultChecks st s1 (L.curW s1) ptr badge dest r → L.mem s (yieldA dest) = 0#u64
  /-- [P] -/
  gl : VmGlue st ar i.Locks s

/-- **vmF's path `Pre` from `VmFEntJ10` and `run`.** -/
theorem VmFEntJ10.pre (hA : P0.ArchTotal ar) {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : VmFArg S} {K : KLayoutV} {s : S}
    (E : VmFEntJ10 st ar arI AR MR i K s) (hK : RegionOKV K)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING) :
    VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s := by
  have BU := E.ix.toU
  have hb := BU.vmBase hrun
  have hJ := BU.slJAtS.slJAt
  have hhyp : ∀ a s1 a1, sched.update_timestamp st ar s a = ok (s1, a1) →
      VmFootHyps (L := L) i.T i.Cs i.Ω i.U i.Sg i.Rp i.Scs i.Nt i.Ac i.H i.Z s1 := by
    obtain ⟨hKH, hT, hSg, hRp, hScs, hNt, hZ, ⟨A', arI', AR', Zx, Lst, D, a', σ, B, hΩ, hU⟩⟩ := E.ix
    rw [hT, hSg, hRp, hScs, hNt, hZ, hΩ, hU, ← hKH]
    exact B.footU hA hrun
  have hEp : ∀ p, i.H p = some .ep → K.toKLayout.heap p = some .ep := fun p hp => by rw [E.ix.hKH]; exact hp
  have hRp : ∀ r ∈ i.Rp, K.toKLayout.heap r = some .reply := fun r hr => by
    rw [E.ix.hKH]; rw [E.ix.hRp] at hr; exact hr
  exact vmPre_userV_empty hK E.nv ⟨⟨hb, hhyp, E.lk, hEp, hRp, E.hyt⟩, E.gl, rdTab_of BU.bxi hJ⟩

/-- **vmR's start entry facts** (module docstring, item 5): `mid`'s BXI / AsidOff, `hNt`, `nbt` derived, the index at
`OmegaU`. -/
structure VmREntJ10 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : VmRArg S) (Kl : OwnMap.KLayout) (s : S) : Prop where
  /-- Index convention at `OmegaU` (famw's `BunIxU`, a choice of index: `bunIxU_of`). -/
  ix : BunIxU (L := L) Kl Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns
    Kl.heap.scBits i.Ac s
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [J] what stays of `VmRPre.mid` (module docstring, items 3 and 4): `RRPl` (derivable by `rrPl_lkG` once a
  frame lemma carries `lkTyped` / `reply_caps` over `LocalPre`) and the receiver's `YIELD_TO = 0` (missing invariant,
  true at reachable states). -/
  rr : ∀ a s2 a2, LocalPre (st := st) ar s a (s2, a2) →
    ∀ u usc, RRChecksG st ar fl4_abi.consts.fault.VMFault s2 a2 (L.curW s) i.rptr i.ep u usc →
      RRPl (L := L) Kl.heap.tcbs i.Cs i.Ω i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits s2
        (L.curW s) i.rptr i.ep u usc ∧ L.mem s2 (yieldA u) = 0#u64
  /-- [P] -/
  lk : i.Locks s i.rptr ∧ i.Locks s i.ep
  /-- [P] -/
  nb : L.mem s (rPrevA i.rptr) = 0#u64 ∧ L.mem s (rNextA i.rptr) = 0#u64
  /-- `loc_chain_all` clause 10's fl4-sync input `hfd`. -/
  fd : VmFoundC st i.rptr i.ep s

/-- **vmR's `VmRPre` from `VmREntJ10` and `run`.** -/
theorem VmREntJ10.toPre (hA : P0.ArchTotal ar) {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : VmRArg S} {Kl : OwnMap.KLayout} {s : S}
    (E : VmREntJ10 st ar arI AR MR i Kl s)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING) :
    (Kl.heap i.ep = some .ep → VmRPre st ar Kl Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg (Heap.replies Kl.heap)
      Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits i.Ac i.Locks s i.rptr i.ep) ∧
    RdTab (L := L) (IoRS (st := st) Kl i.Locks s) s ∧ VmFoundC st i.rptr i.ep s := by
  have hb := E.ix.vmBase hrun
  have hJ := E.ix.slJAtS.slJAt
  have hI := E.ix.bxi
  have hmid : ∀ a s2 a2, LocalPre (st := st) ar s a (s2, a2) →
      BXI st Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits i.Ac s2 ∧
        AsidOff (L := L) i.Ω i.Sg s2 := by
    obtain ⟨-, -, hSg, -, -, -, -, ⟨A', arI', AR', Zx, Lst, D, a', σ, B, hΩ⟩⟩ := E.ix
    rw [hSg, hΩ]
    exact B.lpBxiAsid hA
  refine ⟨fun hep =>
    { base := hb
      mid := fun a s2 a2 hLP => ⟨(hmid a s2 a2 hLP).1, (hmid a s2 a2 hLP).2, E.rr a s2 a2 hLP⟩
      lk := E.lk
      nb := E.nb
      hEp := hep
      hRp := fun _ hr => hr
      hNt := PathObl.SlJAt.hNtR hJ
      nbt := BXI.nbt hI hI.1.choose_spec.choose_spec.curT }, rdTab_of hI hJ, E.fd⟩

end ent

/-! ## 3. Satisfiability -/

section sat
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **vmF's index convention is satisfiable at every bundle state** (with the bundle's `Ω` / `U`). -/
theorem vmFIx10_sat {K : KLayoutV} {s : S} (h : SlJAt (L := L) K.toKLayout s) :
    ∃ Cs Ac Ω U : Set U64, ∀ i : VmFArg S, i.T = K.heap.tcbs → i.Cs = Cs → i.Ω = Ω → i.U = U → i.H = K.heap →
      i.Sg = K.heap.frame → i.Rp = K.heap.replies → i.Scs = K.heap.scs → i.Nt = K.heap.ntfns →
      i.Z = K.heap.scBits → i.Ac = Ac →
      BunIxV (L := L) K.toKLayout i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s := by
  obtain ⟨Cs, Ac, Ω, U, BV⟩ := bunIxV_of h
  refine ⟨Cs, Ac, Ω, U, fun i e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 => ?_⟩
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  exact BV

end sat

/-! ## 4. The start fact and the top -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start fact of `fl4LocP3W6`, vmF / vmR at their W10 entry facts** (module docstring, item 5). -/
def StartP3W10 (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vmF j => ∃ h : VmFPrem st ar j K m, GlueAt ((vmFSlot st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ VmFEntJ10 st ar arI AR MR j K σ) c hs m q
  | .vmR j => ∃ h : VmRPremP3 st ar j K m, GlueAt ((vmRSlotP3 st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ VmREntJ10 st ar arI AR MR j (userV K) σ) c hs m q
  | i => StartP3W9 st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i

variable {arI AR MR}

/-- **`startAt_P3W10` on the re-based platform** (gen 54, in place: `hRun : ChainRun` for `P` / `hIoa`). -/
theorem startAt_P3W10_C (hRun : ChainRun st arI AR MR) {Ch : S → Prop}
    {K : KLayoutV} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartP3W10 st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartAt ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K m hK hU) c hs m q := by
  obtain ⟨σe, hC'⟩ := hC
  have hCh := ChainOf.bun hC'
  cases i with
  | vmF j =>
    obtain ⟨h, hG⟩ := h
    exact startAt_P3W st ar hA hSt hm a0 hCh (i := .vmF j)
      ⟨h, hG.mono fun σ he _ => he.2.pre st ar hA hK (hRun hC' he.1 he.2.hct)⟩
  | vmR j =>
    obtain ⟨h, hG⟩ := h
    exact startAt_P3W st ar hA hSt hm a0 hCh (i := .vmR j)
      ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toPre st ar hA (hRun hC' he.1 he.2.hct)⟩⟩
  | io j => exact startAt_P3W9_C st ar hA hm hSt a0 hRun ⟨σe, hC'⟩ (i := .io j) h
  | st j => exact startAt_P3W9_C st ar hA hm hSt a0 hRun ⟨σe, hC'⟩ (i := .st j) h
  | irq j => exact startAt_P3W9_C st ar hA hm hSt a0 hRun ⟨σe, hC'⟩ (i := .irq j) h
  | sl j => exact startAt_P3W9_C st ar hA hm hSt a0 hRun ⟨σe, hC'⟩ (i := .sl j) h
  | vq j => exact startAt_P3W9_C st ar hA hm hSt a0 hRun ⟨σe, hC'⟩ (i := .vq j) h

/-- **`StartAt` of `fl4LocP3W6`'s family from `StartP3W10`**, given the current chain. -/
theorem startAt_P3W10 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutV} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartP3W10 st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartAt ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K m hK hU) c hs m q :=
  startAt_P3W10_C st ar hA hm hSt a0 (chainRun_of P hIoa) hC h

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EV
