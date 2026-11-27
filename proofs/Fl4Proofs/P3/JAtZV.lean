/-
P3 (line mmuAD, gen 23): **the VM-epoch joint invariant `JAtZV`** (gen 22's "Goal 4" list, first part).

* **`JAtZB`**: `JAtZ` (P3/JointAt) with its `ext : JExt` field dropped — the 50 other fields, statements copied
  verbatim (generated from P3/JointAt's structure). `JAtZ.toB`, `JAtZB.toJAtZ` (with a `JExt`).
* **`JAtZV V X …`**: `base : JAtZB`, `extv : JExtV V X Z.th s`, `rvm : RunVmB Z.th s`, `vm : JVm V H s σ`,
  `vl : VList st V Z.th s`. `JAtZV.toJAtZ`: at `V = X = ∅` it gives `JAtZ` back (`JExtV.toJExt`).
* **`JAtZ.toV`**: `JAtZ` ⇒ `JAtZV ∅ ∅` given `R : RunVmB` and the empty list (head word 0 + its placement). Neither
  is a `JAtZ` field: natively `RunVmB` says no TCB is `TS_RUNNING_VM`, which is P3's `NativeScope` (an [S], the
  native IPC lemmas' named premise) — **`JAtZ.rvm_of_ns`** derives `RunVmB` from it; the head word's value and
  placement are not `JAtZ` facts (no field reads `VCPU_HEAD`), so `JAtZ.toV` takes them as `h0` / `hd` [J].
* Boot: **`JBoot.jAtZV_w1`** — `JAtZV ∅ ∅` at the richer boot witness `w1` (`jAtZ_w1`, `w1_rvm`, `w1_vhead0`,
  `w1_vhd`), no premise.
* Preservation, representative steps:
  - **`JAtZV.of_native`**: at `V = ∅` every native step theorem `JAtZ → JAtZ` lifts, given the step keeps
    `RunVmB` and the list words (`VList.writes`);
  - **`JAtZV.vcpuWr0`**: a write of a VCPU object word (`JAtZ.vcpuWrJ`'s premises) keeps `JAtZV ∅ ∅` (no premise
    beyond `vcpuWrJ`'s: `RunVmB` and `VList` frames derived from the heap separation and `JVm`-style `hks`);
  - **`JAtZV.mk'`**: for `V ≠ ∅` the decomposition: a step's `JAtZB` at the post-state plus the four extension
    parts (each with its proved per-step lemma, gens 19–23) give `JAtZV`. What is **not** proved: `JAtZB`
    preservation for any step from a `JAtZV` state with `V ≠ ∅`; every existing preservation proof consumes
    `JAtZ.ext` (`JExt`), false once a VCPU cap exists, and `xtop.rel` relates FL4 to the *ported* spec
    (`SInvA.ns` / `NativeScopeS` false while a guest runs).

No [P] / [W] / [S] premise of the structure; `JAtZ.rvm_of_ns`'s `hN` is the existing [S] `NativeScope`; `JAtZ.toV`'s
`h0` / `hd` [J]. No existing statement changed. No P2 [S] discharge is claimed: `JAtZV` reachability over VM steps
is open.
-/
import Fl4Proofs.P3.JExtVListSteps
import Fl4Proofs.P3.JBoot1JAt
import Fl4Proofs.P3.VcpuWrJ
import Fl4Proofs.P3.JCurRunR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JAtZ` without `ext`** (module docstring; fields as P3/JointAt's `JAtZ`). -/
structure JAtZB (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  -- 1a: the refinement relation
  xtop : XTopAt (L := L) AR Z s a σ
  call : Sched.CallRel (L.mem s) Z.R Z.C σ Lst
  rfree : Sched.RFree (L.mem s) Z.R Z.C σ Lst
  /-- A reply bound to a thread blocked receiving has null links (ScRecvLinks;
  l4v `valid_replies`). -/
  rrecv : Sched.RRecv (L.mem s) Z.R σ
  yld : Sched.YieldRel Z.T Z.C (L.mem s) σ
  mcp : Sched.McpRel Z.T (L.mem s) σ
  buf : BufWordRel Z.T (L.mem s) σ
  -- 1b: placement
  ks : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)
  thT : ∀ t, Z.th t = some .tcb → t ∈ Z.T
  /-- [carried] `Z.th` holds TCBs and CNodes only (its one producer, the
  retype's `ThX`, adds `thKindN`'s kinds; deletions only drop entries). -/
  thk : ∀ q k, Z.th q = some k → k = .tcb ∨ ∃ r, k = .cnode r
  ip : IPlaced Z.N Z.T Z.E Z.R Z.B
  rp : Sched.RPlaced st Z.N Z.T Z.C Z.R Z.c s σ
  apart : Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s σ
  nk : ∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val
  /-- [carried] The IPC-buffer words miss every node slot of the kernel-state
  block (all 64 cores', not only `Cs`'s: the buffer words are user frames;
  kept by every step, `Z.B` grows only by a frame retype from an untyped
  region, which misses the block). -/
  nodeB : ∀ wp ∈ Z.B, ∀ c : U64, c.val < 64 → wp.1.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ wp.1.val
  jpl : ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s σ
  cover : Sched.SpecCover H σ
  obj : Sched.ObjCover Z.N Z.T Z.E Z.R Z.C σ
  /-- [carried] The sets' objects are `H`'s (derivable: `IpcRel`/`SchedRel`
  and `SpecCover`, `JPlaced`). -/
  zH : (∀ t ∈ Z.T, H t = some .tcb) ∧ (∀ e ∈ Z.E, H e = some .ep) ∧ (∀ r ∈ Z.R, H r = some .reply) ∧
    (∀ n ∈ Z.N, H n = some .ntfn)
  sfree : Sched.SpecFree (L.mem s) Z.G σ
  /-- [carried] `H`'s endpoints, notifications and replies are the sets'
  (the converse of `zH`; for the `SchedValid` rebuild). -/
  hset : (∀ e, H e = some .ep → e ∈ Z.E) ∧ (∀ n, H n = some .ntfn → n ∈ Z.N) ∧
    (∀ r, H r = some .reply → r ∈ Z.R)
  /-- [carried] `H`'s SCs are `Z.C`'s (the converse of `JPlaced.sc` with
  `ObjCover.sc`; l4v: an SC object of the heap is one the scheduler
  relation covers). Kept by every step at `J` (each keeps `H` and `Z.C`;
  a retype adds its new SCs to both). The idle SC, when the spec has one at
  a non-null address, is in both (`JPlaced.sc`, `ObjCover.sc`); a cap never
  names it (`CapObjH`). With `JPlaced.cobj` it gives an SC cap's spec SC
  (`JAtZ.scCap`). -/
  hscC : ∀ c z, H c = some (.sc z) → c ∈ Z.C
  jcov : Sched.JCovD (L := L) Z.th H Z.G D Cs s
  kern : JKern (L := L) arI H Cs D Z.th s σ
  -- 1c: CSpace
  del : DelInv Z.th (L.mem s)
  ut : UtInv (L.mem s) Z.G
  bound : DelBound Z.th
  /-- [carried] `FinM` at every tree of the slots (`FinInv` gives it at
  `Z.G`; `DelE` reads every `G`). -/
  finM : ∀ G, MdbLinks Z.th (L.mem s) G → FinM (L.mem s) G
  /-- [carried] The RAM untyped caps' facts (`UtCapP3`: l4v `valid_untyped`,
  `valid_cap`, the kernel's placement). Not asked of device untypeds: since
  losfair/FL4#34 a device untyped's pointer `paddr + PPTR_BASE` may lie in
  the kernel image, so its region may hold the kernel-state block with the
  IRQ node's CNodes (`IntLayout.node`, objects of `Z.th` with MDB slots) and
  the preemption point's word: `free`, `nostr`, `nsFree`, `ns` and `pp` are
  false of such a cap at boot. -/
  utc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
    Sched.UtCapP3 (L := L) arI Z.th s σ Z.G sl p sb fi
  -- 1d: the scheduler
  nsc : Sched.NSC Z.N Z.C σ
  inv : Sched.Inv σ
  /-- `CurInv` unless a reschedule is pending (mid-entry, as `ScEntry`). -/
  cur : σ.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ
  /-- The current SC's owner, or the current SC unowned (`CurOwnW`, what
  `schedule` from a mid-entry state reads; unowned after the current thread
  deleted itself or unbound its SC; `curOwn_of_curInv` where `CurInv`
  holds). -/
  own : Sched.CurOwnW Z.T Z.C σ
  off : Sched.OffOK σ
  act : Sched.ActIdle σ
  c0 : ∀ q ∈ Z.C, q ≠ 0#u64
  bsa : Sched.BlockedScActive σ
  sv : Sched.SchedValid σ
  /-- The spec's IPC queues sorted by priority (l4v `sorted_ipc_queues`). -/
  isorted : Sched.IpcSorted σ
  /-- The spec's SC, TCB and notification links (per-op; for the
  `SchedValid` rebuild). -/
  slink : Sched.ScLinkHyp σ
  /-- The current thread runnable, or the idle thread current (`CurRunW`:
  at kernel exit `schedule` may have chosen the idle thread), unless a
  reschedule or switch is pending (`CurRunM`: mid-entry after a blocking
  step, or after suspending the current thread with a switch pending). -/
  curRun : CurRunM σ
  -- 1e: P1
  blk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
    (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s
  /-- [carried] The interrupt state and node layout (`IntLayout`, the boot's
  [P]; kept by every step: `Z.th` and the kernel-state base are kept). -/
  intL : IntLayout Z.th (L.ksb s)
  /-- [carried] **The VSpace caps placed in the relation's own sets**, weakened
  (VsCapW's `VsCapsW`: l4v `valid_cap` for the arch caps with
  `valid_table_caps`), at every slot of the typed heap: an unmapped page-table/directory/PDPT cap's table in
  its set, a PML4 or ASID pool cap's object in its set, the ASID and
  alignment facts; a mapped table may lie outside the sets (pruned by a
  detype). Kept by every step (`VsSlotsW.of_eq` for slots kept,
  `VsSlotsT` for the slot steps, `VCapW.transfer` for a copy), the sets kept
  or grown. -/
  vsc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s)
  /-- [carried] **Every IPC frame cap valid** (l4v `valid_ipc_buffer_cap`,
  from `valid_objs`; FL4's form `Endp.IpcBufCapOK`: the buffer's words in a
  user frame, so an alias inside a large page from `Page_DeriveSubframe`
  counts). Kept by every step not touching an IPC frame or a data page
  (`IpcFrKeep`), set by SetIPCBuffer/Configure (`IpcBufCapOK.setFrame`, the
  cap checked), dropped TCBs' frames by `IpcBufCapOK.sdrop`. -/
  bok : Endp.IpcBufCapOK σ
  /-- [carried] **`B` covers every word of every non-device user frame**
  (`FrameCover`; FL4's ghost `B` relates FL4 memory and the spec's
  `underlyingMemory` there, l4v's shared `machine_state`). Kept by every step
  keeping the data pages (`FrameCover.ipcFr`), grown with `B` at the frame
  retype, shrunk with `B` at the detype (`FrameCover.sdrop`). -/
  fcov : FrameCover Z.B σ
  /-- [carried] **Every non-device frame cap names user frames** (l4v
  `valid_cap` for frame caps: each byte of a slot's frame cap range lies in a
  non-device data page). Kept by every step keeping the data pages and moving
  frame caps within old ranges (`Vs.VsSlotsT`'s `FrSlots` part: copy, mint,
  move, swap, DeriveSubframe's sub-range), set at the frame retype for the new
  pages, released at the detype by `FrameOffJ`. -/
  fcap : Vs.FrSlots Z.th (UFr σ) (L.mem s)
  /-- [carried] **The liveness bundle at the ghosts** (KENTRY-PLAN g2i; INV-PLAN
  E15, the former `JEntryAt.live` / `kernel_entryJ33`'s `hLv` [J]): `LiveJ`
  (l4v `if_unsafe_then_cap`, `if_live_then_nonz_cap`, `zombies_final`; the idle
  thread and the kernel-state block exempt, KENTRY-PLAN g2e), `DbgWF` (FL4's
  debug lists) and `NullOrig` (l4v `valid_nullcaps`) at `Z.th`, `H`, `Cs`,
  `Z.G`. Each construction proves it where its frames are visible
  (`JAtZ.liveX` for a step keeping the slots). -/
  live : LiveDN (L := L) Z.th H Cs Z.G s σ
  /-- [carried] **The TCB zombies' TCBs are in the dead set** (so a frame step's
  dead-set carry keeps `LiveJ.zdead`; every TCB zombie's TCB is `DeadP` by
  `live`, so `D ∪ ZTcb` is always a dead set: `JAtZ.addDeadSet`). -/
  zD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D
  /-- [carried] **The `JCarry` facts** (KENTRY-PLAN g7b-4, jc1): the IPC-buffer
  words in non-device data pages (`BufPgHyp`, C21 / C24 bufObj) and `H`'s arch
  objects no larger than their spec objects (`ArchFitHyp`, the first half of C16 /
  C22 / C24 heapH); jc2: the device untyped caps' apartness (`DevApart`, C25) with
  RAM/device range separation (`DevSep`). A frame step keeps the σ part by
  `JCarry.frame` (a `JCarryS`) and the device part by `JCarry.devStep` (`JCarryS.withP`). -/
  carry : JCarry (L := L) Z H Cs s σ


/-- **The VM-epoch joint invariant** (module docstring). -/
structure JAtZV (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  base : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ
  extv : JExtV (L := L) V X Z.th s
  rvm : RunVmB (L := L) Z.th s
  vm : JVm (L := L) V H s σ
  vl : VList st V Z.th s

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

theorem JAtZ.toB (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ :=
  ⟨J.xtop, J.call, J.rfree, J.rrecv, J.yld, J.mcp, J.buf, J.ks, J.thT, J.thk, J.ip, J.rp, J.apart, J.nk, J.nodeB, J.jpl, J.cover, J.obj, J.zH, J.sfree, J.hset, J.hscC, J.jcov, J.kern, J.del, J.ut, J.bound, J.finM, J.utc, J.nsc, J.inv, J.cur, J.own, J.off, J.act, J.c0, J.bsa, J.sv, J.isorted, J.slink, J.curRun, J.blk, J.intL, J.vsc, J.bok, J.fcov, J.fcap, J.live, J.zD, J.carry⟩

theorem JAtZB.toJAtZ (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (E : JExt (L := L) Z.th s) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ :=
  ⟨B.xtop, B.call, B.rfree, B.rrecv, B.yld, B.mcp, B.buf, B.ks, B.thT, B.thk, B.ip, B.rp, B.apart, B.nk, B.nodeB, B.jpl, B.cover, B.obj, B.zH, B.sfree, B.hset, B.hscC, B.jcov, B.kern, B.del, B.ut, B.bound, B.finM, B.utc, B.nsc, B.inv, B.cur, B.own, B.off, B.act, B.c0, B.bsa, B.sv, B.isorted, B.slink, B.curRun, B.blk, B.intL, B.vsc, B.bok, B.fcov, B.fcap, E, B.live, B.zD, B.carry⟩

/-- At `V = X = ∅`, `JAtZV` gives `JAtZ`. -/
theorem JAtZV.toJAtZ (J : JAtZV (L := L) arI ∅ ∅ AR Z H Cs Ac Lst D s a σ) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ :=
  J.base.toJAtZ J.extv.toJExt

/-- **`JAtZ` ⇒ `JAtZV ∅ ∅`** (module docstring; `R` and the empty list `h0` / `hd` [J]). -/
theorem JAtZ.toV (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (R : RunVmB (L := L) Z.th s)
    (h0 : L.mem s (P1.vHeadA st s) = 0#u64)
    (hd : P1.Aligned (P1.vHeadA st s) ∧ ¬ JW ∅ Z.th (P1.vHeadA st s) ∧ ¬ SW Z.th (P1.vHeadA st s)) :
    JAtZV (L := L) arI ∅ ∅ AR Z H Cs Ac Lst D s a σ :=
  ⟨J.toB, J.extV, R, JVm.empty, VList.empty h0 hd⟩

/-- **At `V = ∅` a native step lifts** (module docstring). -/
theorem JAtZV.of_native {Z' : XSets} {H' : P1.Heap} {Cs' Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64}
    {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (J' : JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σ')
    (R' : RunVmB (L := L) Z'.th s') (Vl' : VList st ∅ Z'.th s') :
    JAtZV (L := L) arI ∅ ∅ AR Z' H' Cs' Ac' Lst' D' s' a' σ' :=
  ⟨J'.toB, J'.extV, R', JVm.empty, Vl'⟩

/-- **The decomposition** for any `V` (module docstring): the post-state's `JAtZB` and the extension's parts. -/
theorem JAtZV.mk' (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (E : JExtV (L := L) V X Z.th s)
    (R : RunVmB (L := L) Z.th s) (Jv : JVm (L := L) V H s σ) (Vl : VList st V Z.th s) :
    JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ := ⟨B, E, R, Jv, Vl⟩

/-- **`RunVmB` from `NativeScope`** (no spec thread `runningVM`, the [S]): every typed-heap TCB's state word is
the `tsCode` of its spec state, never 8. -/
theorem JAtZ.rvm_of_ns (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hN : NativeScope σ) :
    RunVmB (L := L) Z.th s := by
  intro t ht h8
  exfalso
  obtain ⟨x, hk, -⟩ := J.xtop.rel.2.1.1.tcb t ht
  have hw := (J.xtop.fin.1.1.2.2.1.at_tcb (J.thT t ht) hk).st
  have hvm := hN _ _ hk
  rw [Sched.stA_tStA] at h8
  rw [h8] at hw
  cases hx : x.tcbState <;> rw [hx] at hw hvm <;> simp_all [tsCode]

set_option maxHeartbeats 4000000 in
/-- **A VCPU word written at `JAtZV ∅ ∅`** (`JAtZ.vcpuWrJ`; module docstring). -/
theorem JAtZV.vcpuWr0 (J : JAtZV (L := L) arI ∅ ∅ AR Z H Cs Ac Lst D s a σ) {p w : U64}
    (hσ : ∃ x, σ.kheap p.bv = some (.archObj (.vcpu x))) (hH : H p = some (.other 15))
    (hks : p.val + 32768 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ p.val)
    (hal : P1.Aligned w) (g1 : p.val ≤ w.val) (g2 : w.val < p.val + 32768)
    (hnB : ∀ wp ∈ Z.B, wp.1 ≠ w) (x : U64) :
    JAtZV (L := L) arI ∅ ∅ AR Z H Cs Ac Lst D (L.wr s w x) a σ := by
  have J0 := J.toJAtZ
  have J1 := J0.vcpuWrJ hσ hH hks hal g1 g2 hnB x
  have hW : P1.WritesIn st s (L.wr s w x) (· = w) := P1.writesIn_wr hal
  have hHO := J0.kern.heap
  have apT : ∀ t, Z.th t = some .tcb → t.val + 4096 ≤ p.val ∨ p.val + 32768 ≤ t.val := by
    intro t ht
    have htH : H t = some .tcb := J0.zH.1 t (J0.thT t ht)
    have hne : t ≠ p := fun e => by rw [e, hH] at htH; cases htH
    have d := hHO.disj t _ p _ htH hH hne
    simp only [P1.HKind.bits, Nat.reducePow] at d
    exact d
  have kT : ∀ t, Z.th t = some .tcb → L.mem (L.wr s w x) (P1.stA t) = L.mem s (P1.stA t) ∧
      L.mem (L.wr s w x) (tVcpuA t) = L.mem s (tVcpuA t) := by
    intro t ht
    have hta := J0.ip.e.tcb t (J0.thT t ht)
    have e1 := lay_stA_val hta
    have e2 := lay_tVcpu_val hta
    have ha := hta.align
    have d := apT t ht
    refine ⟨hW.mem_eq (by unfold P1.Aligned; omega) fun e => ?_, hW.mem_eq (by unfold P1.Aligned; omega) fun e => ?_⟩
    · have := congrArg UScalar.val e; omega
    · have := congrArg UScalar.val e; omega
  have R' : RunVmB (L := L) Z.th (L.wr s w x) := by
    intro t ht h8
    rw [(kT t ht).2]
    exact J.rvm t ht (by rw [← (kT t ht).1]; exact h8)
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J0.kern.ksbFit
  have Vl' : VList st ∅ Z.th (L.wr s w x) := J.vl.writes hW fun b hb => by
    rcases hb with rfl | ⟨w', hw', -⟩
    · exact ⟨J.vl.hd.1, fun e => by have := congrArg UScalar.val e; omega⟩
    · exact hw'.elim
  exact ⟨J1.toB, J1.extV, R', JVm.empty, Vl'⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Classical

theorem w1_vhead_val : (P1.vHeadA wst w1).val = 18446744071562133584 := by
  unfold P1.vHeadA
  rw [ksb_w1, vHead_val (by rw [fkb_val]; norm_num), fkb_val]

/-- The VCPU list is empty at `w1`. -/
theorem w1_vhead0 : wL.mem w1 (P1.vHeadA wst w1) = 0#u64 := by
  rw [mem1_al w1_vhead_val (by norm_num)]; img1z

/-- The head word's placement at `w1`: in no slot, no TCB VCPU / state word (`thW1`'s objects off `fkb + 80`). -/
theorem w1_vhd (a : MachineState) :
    P1.Aligned (P1.vHeadA wst w1) ∧ ¬ JW ∅ thW1 (P1.vHeadA wst w1) ∧ ¬ SW thW1 (P1.vHeadA wst w1) := by
  have hv := w1_vhead_val
  have Ly := (jAtZ_w1 a).jvLay (V := ∅) JVm.empty
  refine ⟨by unfold P1.Aligned; omega, Ly.nJS (fun p k hp g1 g2 => ?_) (fun w hw => hw.elim)⟩
  exfalso
  rw [hv] at g1 g2
  thc1 hp <;> simp only [objSize, Nat.pow_zero, Nat.mul_one, Nat.pow_one] at g2 <;> omega

/-- **`JAtZV ∅ ∅` at the boot witness `w1`** (no premise). -/
theorem jAtZV_w1 (a : MachineState) :
    JAtZV (L := wL) warI ∅ ∅ wAR Zw1 Hw1 Csw C1 (fun _ => []) Dw w1 a σ1 :=
  (jAtZ_w1 a).toV w1_rvm w1_vhead0 (w1_vhd a)

end Fl4Proofs.P3.JBoot
