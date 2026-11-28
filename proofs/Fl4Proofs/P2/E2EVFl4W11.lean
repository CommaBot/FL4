/-
P2 (line iolay, gen 3): **`serializable_fl4_localW11`: vmR's `rr` [J] shrunk to the receiver's `YIELD_TO`** (new
definitions only, on top of W10; no existing statement changes; no `kernel_entry_reach*` touched).

## 1. `RRPl` at the dispatch state (`SlJAtZ.rrPlU`)

`LocalPre` writes three words: the current thread's `FAULT_IP` register (offset 392) and the node's `CUR_TIME` /
`CONSUMED` (`localPre_w3`, a sharper `localPre_foot`). P1's `rrPl_lkG` builds `RRPl` at the dispatch state from
`BXI` there (W10's `lpBxiAsid`), the lookup typing and `reply_caps`:
* lookup typing (`lookup_cap_back3`): a lookup at the dispatch state found at the entry state (`lookup_slot_back`
  with `JAtZ.cnOffU`'s closure; the root slot is the TCB's word 0 / 8, the indexed slots are outside the objects and
  nodes, so none of the three words), then `JAtZ.lkTyped`;
* `reply_caps` (`VmFoundC`, the clause-10 input) carried over by P1's `reply_caps_keep` (its `REPLY` / `CAP`
  registers and root words are not offset 392 and no node word; the walk words are `CapSW`).

So `rr` [J] is replaced by **`ry`** [J]: only the receiver's `YIELD_TO = 0`.

## 2. `YIELD_TO`: not carried by P3 — exact gap

Checked (as line nscope did for `NativeScope`): `SInvX` = `SInvW ∧ RPos`, `SInvA`'s 19 fields (vfh, cnDom, fts, nqb,
ns, sg, idleOut, dom, vim, vih, vmt, ut, nq, epq, live, vi, ft, sl, cs), `SchedValid` (`tcbYieldTo` / `scYieldFrom`
only name an SC / its TCB back), `SInvI.ValidIdle` (the idle thread's `tcbYieldTo = none`), `UtDropSpec` (yield
links avoid a dropped region), `ScYield.lean`'s relation (`x.tcbYieldTo = optRef (m (yieldA t))`), and P1's carried
invariants (`QueueHeapDrop.yto`: a nonzero `YIELD_TO` is a kept reference; `FastTailNvm`'s `hyt`: it names an SC).
**None states or implies "`tcbYieldTo ≠ none` ⇒ not blocked on receive"** (nor the FL4-side `YIELD_TO = 0` for a
receive-blocked thread). So no `kernel_entry_yieldToU29` can be exported from existing facts; both `hyt` (vmF) and
`ry` (vmR) stay [J]. What a preservation proof needs (stopped here as asked):
* the invariant `YB σ := ∀ t x, σ.kheap t = some (.tcb x) → x.tcbYieldTo ≠ none → ¬ ∃ e r d,
  x.tcbState = .blockedOnReceive e r d`, plus an entry fact `ct.tcbYieldTo = none` at `Entered` states (true because
  every exit runs `activateThread`, Fl4Spec/Tcb.lean:74, whose `completeYieldTo` clears it);
* spec steps that matter: the only `blockedOnReceive` writer `receiveIPC` (Fl4Spec/Ipc.lean:284, on the current
  thread: needs the entry fact, and that no earlier step of the same entry set ct's `tcbYieldTo`); the only setter of
  `tcbYieldTo := some _`, `schedContextYieldTo` (Fl4Spec/Schedule.lean:263, on `ct`, which stays `running` to the
  exit); `activateThread` / `completeYieldTo` / `schedContextCancelYieldTo` (only clear); every other `threadSet` /
  `setThreadState` (frame: neither field to the bad combination); object creation (`tcbYieldTo := none`,
  Structures.lean:386);
* size: comparable to `NativeScopeS` (P3/SpecInvNativeScope*.lean, 9 files, ~2600 lines over the same step
  families), plus the entry-fact half through `activateThread` — a line of its own.
* Alternative without a new invariant: P1's non-VM fault tail already runs with a nonzero receiver `YIELD_TO`
  (`FastTailNvm.YWd`, premise only "`YIELD_TO ≠ 0` ⇒ it names an SC", which `SchedValid.tcbYieldTo` + the SC relation
  give); generalising the VM fault / ReplyRecv tails' footprint (AccessVmTail / AccessVmRR's `dyt` / `uYt`) the same
  way would remove `hyt` / `ry` at the cost of reworking those access proofs.

## 3. The top

* vmR **`VmREntJ11`** = `BunIxU`, `hct` [P], `ry` [J], `lk` / `nb` [P], `fd` (`RRPl`, `mid`'s BXI / AsidOff,
  `hNt`, `nbt` derived). vmF as W10 (`hyt` [J]).
* `StartP3W11`, `startAt_P3W11`, **`serializable_fl4_localW11`** (same premises as W10).

| slot | removed (vs W10) | added |
|---|---|---|
| vmR | `rr` [J] (RRPl + receiver `YIELD_TO`) | `ry` [J] (receiver `YIELD_TO` only) |
-/
import Fl4Proofs.P2.E2EVFl4W10
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs

section w3
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {T : Set U64}

/-- The three words `LocalPre` writes. -/
def W3 (s : S) (b : U64) : Prop :=
  b = core.num.U64.wrapping_add (L.curW s) 392#u64 ∨ b = ctA (L := L) s ∨ b = cnA (L := L) s

/-- **`LocalPre` writes only the `FAULT_IP` register and the two timestamp words** (`localPre_foot`, sharper). -/
theorem localPre_w3 (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s))
    (hcT : L.curW s ∈ T) (h : LocalPre (st := st) ar s a (s', a')) : WritesIn st s s' (W3 (L := L) s) := by
  obtain ⟨t, nx, s1, et, -, es1, eu⟩ := h
  rw [cur_thread_ok] at et
  obtain rfl := ok_inj_ff et
  have hW1 := obj.Tcb.set_reg.wrK (L := L) s (L.curW s) layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
    (hT _ hcT) (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW1
  obtain ⟨K, hK, e1⟩ := hW1
  have hK' : K = 392#u64 := UScalar.eq_of_val_eq (by rw [hK]; simp [layout.reg.FAULT_IP])
  subst hK'
  have aF : Aligned (core.num.U64.wrapping_add (L.curW s) 392#u64) := field_aligned (hT _ hcT) (by simp) (by simp)
  obtain ⟨⟨n, a1⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [e1, LawfulStore.cpu_wr]; exact hN.wr
  rw [update_timestamp_ok ar hN1 hn] at eu
  obtain ⟨rfl, -⟩ := Prod.mk.inj (ok_inj_ff eu)
  have w1 : WritesIn st s s1 (W3 (L := L) s) := by
    rw [e1]; exact (writesIn_wr aF).mono fun b e => Or.inl e
  have ec : ctA (L := L) s1 = ctA (L := L) s := by rw [e1, ctA_wr]
  have en : cnA (L := L) s1 = cnA (L := L) s := by rw [e1, cnA_wr]
  refine (w1.trans (Fl4Proofs.P2.utW_writes hN1 n)).mono fun b hb => hb.elim id fun hb => ?_
  rw [ec, en] at hb
  exact Or.inr hb

/-- A current-thread word other than `FAULT_IP` is none of the three. -/
theorem w3_tcb {s : S} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T) {K : U64}
    (hK : K.val < 4096) (hne : K.val ≠ 392) : ¬ W3 (L := L) s (core.num.U64.wrapping_add (L.curW s) K) := by
  rintro (e | e | e)
  · have h := congrArg UScalar.val e
    rw [tcb_wadd_val (hT _ hcT) hK, tcb_wadd_val (hT _ hcT) (by simp)] at h
    simp at h <;> omega
  · exact node_ne_field hN (by simp [layout.node.CUR_TIME]) hcT (hT _ hcT) hK e.symm
  · exact node_ne_field hN (by simp [layout.node.CONSUMED]) hcT (hT _ hcT) hK e.symm

/-- A word outside the objects and nodes is none of the three. -/
theorem w3_out {Cs : Set U64} {s : S} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hcC : L.cpu s ∈ Cs) {b : U64} (hb : OutsideObjs st T Cs s b) : ¬ W3 (L := L) s b := by
  rintro (e | e | e)
  · have h := hb.2.1 _ hcT
    rw [e, tcb_wadd_val (hT _ hcT) (by simp)] at h
    simp at h <;> omega
  · exact out_ne_node (o := layout.node.CUR_TIME) hb hcC hN (by simp [layout.node.CUR_TIME]) (by rw [e])
  · exact out_ne_node (o := layout.node.CONSUMED) hb hcC hN (by simp [layout.node.CONSUMED]) (by rw [e])

end w3

section rr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit}

/-- **`RRPl` at the dispatch state** (module docstring, item 1), at `OmegaU`. -/
theorem SlJAtZ.rrPlU (hA : P0.ArchTotal ar) (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {rptr ep : U64}
    (hfd : VmFoundC st rptr ep s) :
    ∀ a s2 a2, LocalPre (st := st) ar s a (s2, a2) →
      ∀ u usc, RRChecksG st ar fl4_abi.consts.fault.VMFault s2 a2 (L.curW s) rptr ep u usc →
        RRPl (L := L) (Heap.tcbs K.heap) Cx (OmegaU K.heap Zx (L.ksb s) σ) (Heap.frame K.heap)
          (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) s2 (L.curW s) rptr ep u usc := by
  intro a s2 a2 hLP u usc hC
  have hI2 := (B.lpBxiAsid hA a s2 a2 hLP).1
  obtain ⟨hT, hN, hcT⟩ := B.j.bxiU.tcbNode
  have hcC : L.cpu s ∈ Cx := B.j.kern.cpuCs
  have hW := localPre_w3 (ar := ar) hA hT hN hcT hLP
  have et := cur_thread_ok (L := L) s
  have hCn := B.cnOffU et
  have hcA : TcbAddr (L.curW s) := hT _ hcT
  -- the current thread is kept
  have ecur : L.curW s2 = L.curW s := by
    unfold LawfulStore.curW
    rw [hW.2.1, nodeAt_of_ksb hW.1]
    refine hW.mem_eq (nodeAt_aligned hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])) ?_
    rintro (e | e | e)
    · exact node_ne_field hN (by simp [layout.node.CUR_THREAD]) hcT hcA (by simp) e
    · unfold ctA at e
      have h := congrArg UScalar.val e
      rw [nodeAt_val hN (off := layout.node.CUR_THREAD) (by simp [layout.node.CUR_THREAD]),
        nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])] at h
      simp [layout.node.CUR_THREAD, layout.node.CUR_TIME] at h
    · unfold cnA at e
      have h := congrArg UScalar.val e
      rw [nodeAt_val hN (off := layout.node.CUR_THREAD) (by simp [layout.node.CUR_THREAD]),
        nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])] at h
      simp [layout.node.CUR_THREAD, layout.node.CONSUMED] at h
  have et2 : sched.cur_thread st s2 = ok (L.curW s) := by rw [cur_thread_ok, ecur]
  -- reply_caps
  have hrc2 : fastpath.reply_caps st s2 (L.curW s) = ok (some (rptr, ep)) := by
    refine reply_caps_keep (T := Heap.tcbs K.heap) (Cs := Cx) (Sg := Heap.frame K.heap ∪ K.user) hcA (hfd _ et) hW
      ?_ ?_ hCn
    · intro Kk hK
      have hKv : Kk.val < 4096 ∧ Kk.val ≠ 392 := by
        rcases hK with h | h | h | h <;>
          (try simp [layout.reg.REPLY, layout.reg.R12, layout.reg.CAP, layout.reg.RDI] at h) <;> omega
      exact w3_tcb hT hN hcT hKv.1 hKv.2
    · intro b hb
      exact w3_out hT hN hcT hcC hb.1
  -- the lookup typing
  have hlk : ∀ cptr, cspace.lookup_cap st s2 (L.curW s2) cptr ⦃ r => ∀ c, r = .Ok c →
      CapTyped K.heap (Heap.replies K.heap) (Heap.ntfns K.heap) c ⦄ := by
    intro cptr
    rw [ecur]
    obtain ⟨r, hr, -⟩ := spec_ex_fd (P0.cspace.lookup_cap.p0 st s2 (L.curW s) cptr L.total)
    rw [hr, WP.spec_ok]
    intro c hc
    subst hc
    have hroot0 : obj.Slot.cap st (L.curW s) s = ok (Fl4Proofs.P3.capV (L.mem s) (L.curW s)) := by
      rw [Fl4Proofs.P3.slot_cap_eq]; exact Fl4Proofs.P3.capAt_capV _ _
    obtain ⟨C, hC0, hcl, hWc⟩ := hCn _ _ (tcb_slot_ctable (L.curW s)) hroot0
    have capK : ∀ b, CapSW (L := L) (Heap.tcbs K.heap) Cx (Heap.frame K.heap ∪ K.user) s b → L.mem s2 b = L.mem s b :=
      fun b hb => hW.mem_eq hb.1.1 (w3_out hT hN hcT hcC hb.1)
    have eC : ∀ p r m y, C p r → cspace.mask r = ok m →
        obj.Slot.cap st (cnSlot p (y &&& m)) s2 = obj.Slot.cap st (cnSlot p (y &&& m)) s := by
      intro p r m y hp hm
      obtain ⟨h1, h2⟩ := hWc p r m y hp hm
      unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, capK _ h1, capK _ h2]
    have e0 : obj.Slot.cap st (L.curW s) s2 = obj.Slot.cap st (L.curW s) s := by
      have k0 : L.mem s2 (L.curW s) = L.mem s (L.curW s) := by
        have := hW.mem_eq (b := core.num.U64.wrapping_add (L.curW s) 0#u64)
          (field_aligned hcA (by simp) (by simp)) (w3_tcb hT hN hcT (by simp) (by simp))
        have e00 : core.num.U64.wrapping_add (L.curW s) 0#u64 = L.curW s := by
          apply UScalar.eq_of_val_eq; rw [tcb_wadd_val hcA (by simp)]; simp
        rwa [e00] at this
      have k8 := hW.mem_eq (b := core.num.U64.wrapping_add (L.curW s) 8#u64)
        (field_aligned hcA (by simp) (by simp)) (w3_tcb hT hN hcT (by simp) (by simp))
      unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, k0, k8]
    have hroot : ∀ p r gs g, obj.Slot.cap st (L.curW s) s = ok (.CNode p r gs g) → C p r := fun p r gs g h =>
      hC0 p r gs g (ok_inj_ff (hroot0.symm.trans h))
    unfold cspace.lookup_cap at hr
    obtain ⟨r0, h0, hr⟩ := bind_eq_ok hr
    cases r0 with
    | Ok r1 =>
      obtain ⟨c', hc', hr⟩ := bind_eq_ok hr
      have ecc := ok_inj_ff hr
      injection ecc with ecc
      subst ecc
      have h0s := lookup_slot_back (tcb_slot_ctable (L.curW s)) e0 eC hcl hroot h0
      obtain ⟨p, r, m, y, hp, hm, ey⟩ := lookup_slot_in hroot hcl h0s
      have hcs : obj.Slot.cap st r1.slot s = ok c' := by rw [← hc', ey, eC p r m y hp hm]
      have hls : cspace.lookup_cap st s (L.curW s) cptr = ok (.Ok c') := by
        unfold cspace.lookup_cap; rw [h0s]; simp only [bind_ok]; rw [hcs]; simp only [bind_ok]
      have hty := post_of_ok (B.j.lkTyped cptr) hls
      exact hty _ rfl
    | Err lf =>
      have := ok_inj_ff hr
      cases this
  exact rrPl_lkG (ty := fl4_abi.consts.fault.VMFault) ar (fun _ h => h) hI2 hlk et2 hrc2 hC

end rr

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot InW InNode)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

section ent
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **vmR's start entry facts** (module docstring, item 3): `RRPl` derived, `ry` the receiver's `YIELD_TO` only. -/
structure VmREntJ11 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : VmRArg S) (Kl : OwnMap.KLayout) (s : S) : Prop where
  /-- Index convention at `OmegaU` (famw's `BunIxU`, a choice of index: `bunIxU_of`). -/
  ix : BunIxU (L := L) Kl Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns
    Kl.heap.scBits i.Ac s
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [J] the ReplyRecv receiver's `YIELD_TO = 0` at the dispatch state (module docstring, item 2: not carried by
  P3; true at reachable states; the missing invariant is "`tcbYieldTo ≠ none` ⇒ not blocked on receive"). -/
  ry : ∀ a s2 a2, LocalPre (st := st) ar s a (s2, a2) →
    ∀ u usc, RRChecksG st ar fl4_abi.consts.fault.VMFault s2 a2 (L.curW s) i.rptr i.ep u usc →
      L.mem s2 (yieldA u) = 0#u64
  /-- [P] -/
  lk : i.Locks s i.rptr ∧ i.Locks s i.ep
  /-- [P] -/
  nb : L.mem s (rPrevA i.rptr) = 0#u64 ∧ L.mem s (rNextA i.rptr) = 0#u64
  /-- `loc_chain_all` clause 10's fl4-sync input `hfd`. -/
  fd : VmFoundC st i.rptr i.ep s

theorem VmREntJ11.toJ10 (hA : P0.ArchTotal ar) {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : VmRArg S} {Kl : OwnMap.KLayout} {s : S}
    (E : VmREntJ11 st ar arI AR MR i Kl s) : VmREntJ10 st ar arI AR MR i Kl s := by
  refine ⟨E.ix, E.hct, ?_, E.lk, E.nb, E.fd⟩
  intro a s2 a2 hLP u usc hC
  refine ⟨?_, E.ry a s2 a2 hLP u usc hC⟩
  obtain ⟨-, -, hSg, -, -, -, -, ⟨A', arI', AR', Zx, Lst, D, a', σ, B, hΩ⟩⟩ := E.ix
  rw [hSg, hΩ]
  exact B.rrPlU hA E.fd a s2 a2 hLP u usc hC

end ent

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start fact of `fl4LocP3W6`, vmR at `VmREntJ11`** (module docstring, item 3). -/
def StartP3W11 (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vmR j => ∃ h : VmRPremP3 st ar j K m, GlueAt ((vmRSlotP3 st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ VmREntJ11 st ar arI AR MR j (userV K) σ) c hs m q
  | i => StartP3W10 st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i

variable {arI AR MR}

/-- **`startAt_P3W11` on the re-based platform** (gen 54, in place: `hRun : ChainRun` for `P` / `hIoa`). -/
theorem startAt_P3W11_C (hRun : ChainRun st arI AR MR) {Ch : S → Prop}
    {K : KLayoutV} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartP3W11 st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartAt ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K m hK hU) c hs m q := by
  cases i with
  | vmR j =>
    obtain ⟨h, hG⟩ := h
    exact startAt_P3W10_C st ar hA hm hSt a0 hRun hC (i := .vmR j)
      ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toJ10 st ar hA⟩⟩
  | vmF j => exact startAt_P3W10_C st ar hA hm hSt a0 hRun hC (i := .vmF j) h
  | io j => exact startAt_P3W10_C st ar hA hm hSt a0 hRun hC (i := .io j) h
  | st j => exact startAt_P3W10_C st ar hA hm hSt a0 hRun hC (i := .st j) h
  | irq j => exact startAt_P3W10_C st ar hA hm hSt a0 hRun hC (i := .irq j) h
  | sl j => exact startAt_P3W10_C st ar hA hm hSt a0 hRun hC (i := .sl j) h
  | vq j => exact startAt_P3W10_C st ar hA hm hSt a0 hRun hC (i := .vq j) h

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EV
