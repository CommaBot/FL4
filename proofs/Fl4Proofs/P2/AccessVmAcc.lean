/-
# P2: `PathObl.acc` for the VM-fault local path, up to the handler running (line p2e, VM paths)

The accepted run of `syscall.handle_vm_fault_local` on the store guarded to the maximal sets
`IoRS K Locks s` / `IoWS K Locks s` (`P2/AccessIoOwn.lean`) at its entry state `s`, with the locks
fl4-sync's `local_vm_fault` holds (the fault endpoint and the handler's reply object, `VmFPre.lk`).

* `VmFPre`: the entry facts (module `AccessVmPre`'s `VmBase`, P1's fast-path facts after the
  entry's `update_timestamp` (`VmFootHyps`, what P3's `JAtZ.vmFaultOK` supplies), the locks, the
  typing of endpoints and reply objects in the layout);
* `ut_*`: the words `update_timestamp` keeps (`utW`);
* `vm_queue`: the handler and its successor are queued on the endpoint (receive state, `BLOCK_OBJ`
  the endpoint);
* `vm_chk`: the fast path's checks pass on the guarded store (`FaultChecks.guard`);
* `vm_preRW`: the words `vmPre14` touches (`VmPreRW`);
* `vm_acc_of_tail`: the whole path, given the tail from the handler `Running` (`faultTail3`) agrees
  on the guarded store.

Premises (fields of `VmFPre`):
* `base`: `VmBase`'s, as tagged there;
* `hyp` [J]: P1's fast-path facts after the prefix (`VmFootHyps`; P3 `JAtZ.vmFaultOK`);
* `lk` [P]: fl4-sync's `local_vm_fault` holds the locks of the endpoint and the reply object the
  fast path finds (it locks them before calling the body, and the body reads the same words);
* `hEp`, `hRp` [J]: the layout's heap types P1's endpoints and reply objects (`K.heap = H` at P3's
  `layoutJ`).
* `hyt` [J]: the dequeued handler's `YIELD_TO` is 0 (fl4-core argument in its docstring; to be
  discharged by a P1 invariant "`YIELD_TO ≠ 0` ⇒ Running/Restart").
-/
import Fl4Proofs.P2.AccessVmPre
import Fl4Proofs.P2.FootVm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region GateField TimerField GField tcbOwner TcbSlot NullOrFrame
  slotOwner treeCore)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- **The entry facts of the VM-fault local path** (module docstring). -/
structure VmFPre {A : Type} (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (K : KLayout)
    (T Cs Ω U : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64)
    (Locks : S → U64 → Prop) (s : S) : Prop where
  base : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s
  hyp : ∀ a s1 a1, sched.update_timestamp st ar s a = ok (s1, a1) →
    VmFootHyps (L := L) T Cs Ω U Sg Rp Scs Nt Ac H Z s1
  lk : ∀ a s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
    FaultChecks st s1 (L.curW s1) ptr badge dest r → Locks s ptr ∧ Locks s r
  hEp : ∀ p, H p = some .ep → K.heap p = some .ep
  hRp : ∀ r ∈ Rp, K.heap r = some .reply
  /-- **`hyt`** [J]: the handler the fast path dequeues (blocked on receive) has `YIELD_TO = 0`,
  so `activate_thread` does not enter `complete_yield_to`. Argument (fl4-core): the only writer of a
  nonzero `YIELD_TO` is `schedcontext::yield_switches` (schedcontext.rs ~178), run on the caller
  `ct` during its own YieldTo syscall; it leaves `ct` in `TS_RUNNING` and enqueued. A thread enters
  Recv only by executing a receive itself, and before it returns to user it passes
  `sched::activate_thread` (sched.rs ~689), which calls `complete_yield_to` → `cancel_yield_to` and
  zeroes `YIELD_TO`; `suspend` also cancels it. So a thread blocked on an endpoint has
  `YIELD_TO = 0`. Discharge (follow-up): a P1 invariant "`YIELD_TO ≠ 0` ⇒ state Running/Restart". -/
  hyt : ∀ a s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
    FaultChecks st s1 (L.curW s1) ptr badge dest r → L.mem s (yieldA dest) = 0#u64

/-! ## What `update_timestamp` keeps -/

theorem ut_tcb {s : S} (hN : NodePlaced st T s (L.cpu s)) (hT : TcbPlaced T) (n : U64) {y : U64} (hy : y ∈ T)
    {Kx : U64} (hK : Kx.val < 4096) (h8 : Kx.val % 8 = 0) :
    L.mem (utW (L := L) s n) (core.num.U64.wrapping_add y Kx) = L.mem s (core.num.U64.wrapping_add y Kx) :=
  utW_mem hN n (field_aligned (hT y hy) hK h8)
    (fun e => node_ne_field hN (by simp [layout.node.CUR_TIME]) hy (hT y hy) hK e.symm)
    (fun e => node_ne_field hN (by simp [layout.node.CONSUMED]) hy (hT y hy) hK e.symm)

theorem ut_node {s : S} (hN : NodePlaced st T s (L.cpu s)) (n : U64) {o : U64} (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (h1 : o.val ≠ layout.node.CUR_TIME.val) (h2 : o.val ≠ layout.node.CONSUMED.val) :
    L.mem (utW (L := L) s n) (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
  utW_mem hN n (nodeAt_aligned hN ho h8) (nodeAt_ne hN ho (by simp [layout.node.CUR_TIME]) h1)
    (nodeAt_ne hN ho (by simp [layout.node.CONSUMED]) h2)

theorem ut_out {s : S} (hN : NodePlaced st T s (L.cpu s)) (hcC : L.cpu s ∈ Cs) (n : U64) {b : U64}
    (hb : OutsideObjs st T Cs s b) : L.mem (utW (L := L) s n) b = L.mem s b :=
  utW_mem hN n hb.1
    (fun e => out_ne_node (o := layout.node.CUR_TIME) hb hcC hN (by simp [layout.node.CUR_TIME]) (by rw [e]))
    (fun e => out_ne_node (o := layout.node.CONSUMED) hb hcC hN (by simp [layout.node.CONSUMED]) (by rw [e]))

/-- A node word of `utW s n` at its own core, as a node word of `s`. -/
theorem ut_nodeAt (s : S) (n o : U64) :
    L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) o = L.nodeAt s (L.cpu s) o := by
  rw [utW_cpu, nodeAt_of_ksb (utW_ksb s n)]

theorem ut_cur {s : S} (hN : NodePlaced st T s (L.cpu s)) (n : U64) : L.curW (utW (L := L) s n) = L.curW s := by
  unfold LawfulStore.curW
  rw [ut_nodeAt]
  exact ut_node hN n (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD, layout.node.CUR_TIME]) (by simp [layout.node.CUR_THREAD, layout.node.CONSUMED])

theorem ut_csc {s : S} (hN : NodePlaced st T s (L.cpu s)) (n : U64) : L.cscW (utW (L := L) s n) = L.cscW s := by
  unfold LawfulStore.cscW LawfulStore.nodeA
  rw [ut_nodeAt]
  exact ut_node hN n (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
    (by simp [layout.node.CUR_SC, layout.node.CUR_TIME]) (by simp [layout.node.CUR_SC, layout.node.CONSUMED])

/-! ## The handler's queue -/

/-- **The handler and (if the queue goes on) its successor are queued on the endpoint**: TCBs
of `T`, `BLOCK_OBJ` the endpoint, in the receive state. -/
theorem vm_queue {Ω Sg Rp Scs Nt Ac : Set U64} {Z : U64 → Nat} {s1 : S} {ptr dest : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hpH : H ptr = some .ep)
    (hst : L.epState s1 ptr = obj.EP_RECV) (hhd : dest = L.mem s1 (epHeadA ptr))
    (hrecv : L.mem s1 (stA dest) = sched.TS_BLOCKED_ON_RECV) :
    ∀ y, (y = dest ∨ ((L.epQ s1 ptr).end ≠ dest ∧ y = L.mem s1 (nextA .Ep dest))) →
      y ∈ T ∧ L.mem s1 (blockA y) = ptr ∧ L.mem s1 (stA y) = sched.TS_BLOCKED_ON_RECV := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  obtain ⟨E, EQ, hW⟩ := hSQ.eps
  obtain ⟨w1, -, -, w4, -, w6⟩ := hW
  have hpE : ptr ∈ E := (w6.2.2.1 ptr).2 (Or.inl hpH)
  obtain ⟨-, -, hQ⟩ := w1 ptr hpE
  have hst2 : L.epState s1 ptr = 2#u64 := by rw [hst, ep_recv_val']
  have hm : ∀ y, (y = dest ∨ ((L.epQ s1 ptr).end ≠ dest ∧ y = L.mem s1 (nextA .Ep dest))) →
      y ∈ EQ ptr ∧ dest ∈ EQ ptr := by
    intro y hy
    cases hl : EQ ptr with
    | nil =>
      have h1 := (w6.2.2.2.2.2 ptr hpE hl).1 hpH
      rw [hst2] at h1; exact absurd h1 (by decide)
    | cons y0 rest =>
      have hQ' := hQ
      rw [hl] at hQ'
      have hy0 : y0 = dest := by
        have h1 := hQ'.head
        simp only [LawfulStore.epQ, List.headD_cons] at h1
        rw [hhd]; exact h1.symm
      rw [hy0] at hQ' ⊢
      refine ⟨?_, List.mem_cons_self⟩
      rcases hy with e | ⟨hne, e⟩
      · rw [e]; exact List.mem_cons_self
      · have hl' := hQ'.last
        have hsg := hQ'.seg
        cases rest with
        | nil => exact absurd (by rw [hl']; rfl) hne
        | cons z zs =>
          simp only [Seg_cons] at hsg
          rw [e, hsg.2.1]; simp
  intro y hy
  obtain ⟨hmy, hmd⟩ := hm y hy
  refine ⟨hQ.mem y hmy, (w4 ptr hpE y hmy).2.1, ?_⟩
  rw [w6.2.2.2.1 ptr hpE y hmy dest hmd]; exact hrecv

theorem recv_queued : OwnMap.QueuedState sched.TS_BLOCKED_ON_RECV := by
  unfold OwnMap.QueuedState; left; simp [sched.TS_BLOCKED_ON_RECV]

/-! ## The checks and the writes up to the handler running -/

theorem tcb_slot_eq (y i : U64) :
    obj.Tcb.slot y i = ok (core.num.U64.wrapping_add y (core.num.U64.wrapping_mul i layout.cte.SIZE)) := by
  simp only [obj.Tcb.slot, lift, bind_ok]

/-! ## The words the path writes, by region -/

/-- **Words whose class nobody tracks**, by their region: node words, endpoint / reply-object
words, TCB words off the deciding offsets (`AFFINITY`, `STATE`, `BLOCK_OBJ`, the timer fields'
ends) and SC words other than the one `own` reads (offset 16). Every word the accepted VM-fault
run writes, besides two threads' `STATE`, is one (`OwnMap`'s `DecW` excludes them, `AccessVmMv`). -/
def VmWd (K : KLayout) (b : U64) : Prop :=
  (∃ c, region K b = .node c) ∨ (∃ p, region K b = .obj p) ∨
  (∃ t, region K b = .tcb t ∧ b.val - t.val ≠ 3520 ∧ b.val - t.val ≠ 3328 ∧ b.val - t.val ≠ 3336 ∧
    b.val - t.val ≠ 3528 ∧ b.val - t.val ≠ 3568) ∨
  (∃ p, region K b = .sc p ∧ b.val ≠ p.val + 16)

section
variable (P : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
include P

theorem VmBase.wdNode {o : U64} (ho : o.val < 4288) : VmWd K (L.nodeAt s (L.cpu s) o) :=
  Or.inl ⟨_, P.lay.io.node _ _ (P.inNode o ho)⟩

theorem VmBase.wdTcb {y off : U64} (hy : y ∈ T) (h1 : 192 ≤ off.val) (h2 : off.val < 4096)
    (hne : off.val ≠ 3520 ∧ off.val ≠ 3328 ∧ off.val ≠ 3336 ∧ off.val ≠ 3528 ∧ off.val ≠ 3568) :
    VmWd K (fld y off) := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := hne
  have e : (fld y off).val - y.val = off.val := by unfold fld; rw [tcb_wadd_val (P.tp y hy) h2]; omega
  refine Or.inr (Or.inr (Or.inl ⟨y, P.lay.io.tcbw y (P.hT y hy) off h1 h2, ?_, ?_, ?_, ?_, ?_⟩)) <;> rw [e] <;> omega

theorem VmBase.wdReg {y r : U64} (hy : y ∈ T) (hr : r.val < 384) : VmWd K (regA y r) := by
  obtain ⟨k, hk, e⟩ := regA_eq (P.tp y hy) hr
  rw [e]
  exact P.wdTcb (off := k) hy (by omega) (by omega) ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem VmBase.wdEp {p b : U64} (hp : K.heap p = some .ep) (hb : InW p 16 b) : VmWd K b :=
  Or.inr (Or.inl ⟨p, P.lay.epw p hp b hb⟩)

theorem VmBase.wdRp {p b : U64} (hp : K.heap p = some .reply) (hb : InW p 32 b) : VmWd K b :=
  Or.inr (Or.inl ⟨p, P.lay.rpw p hp b hb⟩)

theorem VmBase.wdSc {c b : U64} (hc : c ∈ Scs) (hb : InW c (2 ^ Z c) b) (hne : b.val ≠ c.val + 16) : VmWd K b :=
  Or.inr (Or.inr (Or.inr ⟨c, P.lay.io.scw c (Z c) (P.hSc c hc) b hb, hne⟩))

/-- An SC's `ScAcc` for any write set `W` holding the `VmWd` words of `IoWS`. -/
theorem VmBase.scaccW {W : U64 → Prop} (hW : ∀ b, VmWd K b → IoWS (st := st) K Locks s b → W b) {c : U64}
    (hc : c ∈ Scs) (h : ScAcc (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s) c (Z c)) :
    ScAcc (IoRS (st := st) K Locks s) W c (Z c) where
  rd := h.rd
  wr b ha hb := hW b (P.wdSc hc hb.inSC (by have := hb.1; omega)) (h.wr b ha hb)
  cons := by
    obtain ⟨hP, hz⟩ := P.bxi.2.2.1.1.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    exact hW _ (P.wdSc hc ⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩ (by rw [hv, hcv]; omega)) h.cons

end

/-- The facts at the state after the prefix that the checks and `vmPre14` use, read off the entry
facts (`vm_mid_facts`). -/
structure VmMidF (st : machine.Store S) [L : LawfulStore st] (K : KLayout) (T : Set U64) (H : Heap)
    (Rp : Set U64) (Locks : S → U64 → Prop) (s s1 : S) (t ptr dest r : U64) : Prop where
  k : L.ksb s1 = L.ksb s
  c : L.cpu s1 = L.cpu s
  cur : t = L.curW s
  tT : t ∈ T
  dT : dest ∈ T
  hT : TcbPlaced T
  hN : NodePlaced st T s (L.cpu s)
  ep : EpPlaced T ptr
  epK : K.heap ptr = some .ep
  rK : K.heap r = some .reply
  rP : r.val % 32 = 0 ∧ r.val + 32 ≤ 2 ^ 64
  lp : Locks s ptr
  lr : Locks s r
  aff : L.mem s (affA dest) = L.cpu s
  /-- The handler and its successor, queued on the endpoint, at `s`. -/
  q : ∀ y, (y = dest ∨ ((L.epQ s1 ptr).end ≠ dest ∧ y = L.mem s1 (nextA .Ep dest))) →
    y ∈ T ∧ L.mem s (blockA y) = ptr ∧ L.mem s (stA y) = sched.TS_BLOCKED_ON_RECV

section
variable {s1 : S} {t ptr dest r : U64}
variable (P : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (M : VmMidF st K T H Rp Locks s s1 t ptr dest r)
include P M

/-- A node word at `s1`. -/
theorem VmMidF.nd (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    IoRS (st := st) K Locks s (L.nodeAt s1 (L.cpu s1) o) ∧ IoWS (st := st) K Locks s (L.nodeAt s1 (L.cpu s1) o) :=
  nd_at (fun o ho h8 => P.nd o ho h8) M.k M.c o ho h8

theorem VmMidF.epw {b : U64} (hb : InW ptr 16 b) (ha : Aligned b) :
    IoRS (st := st) K Locks s b ∧ IoWS (st := st) K Locks s b := P.ep M.epK hb ha M.lp

theorem VmMidF.hd : IoRS (st := st) K Locks s (core.num.U64.wrapping_add ptr layout.ep.HEAD) ∧
    IoWS (st := st) K Locks s (core.num.U64.wrapping_add ptr layout.ep.HEAD) := by
  have h := epHeadA_val (ep := ptr)
  have := M.ep.fits; have := M.ep.align
  exact M.epw P (b := epHeadA ptr) ⟨by omega, by omega⟩ (by unfold Aligned; omega)

theorem VmMidF.ts : IoRS (st := st) K Locks s (core.num.U64.wrapping_add ptr layout.ep.TAIL_STATE) ∧
    IoWS (st := st) K Locks s (core.num.U64.wrapping_add ptr layout.ep.TAIL_STATE) := by
  have h := epTSA_val M.ep
  have := M.ep.fits; have := M.ep.align
  exact M.epw P (b := epTSA ptr) ⟨by omega, by omega⟩ (by unfold Aligned; omega)

/-- A home word of the handler. -/
theorem VmMidF.dh {off : U64} (h1 : 192 ≤ off.val) (h2 : off.val < 4096) (h8 : off.val % 8 = 0)
    (hg : ¬ GateField off.val) (htm : ¬ TimerField off.val) (hG : ¬ GField off.val) :
    IoRS (st := st) K Locks s (fld dest off) ∧ IoWS (st := st) K Locks s (fld dest off) :=
  P.homeOf M.dT M.aff h1 h2 h8 hg htm hG

/-- A home word of the faulting thread. -/
theorem VmMidF.th {off : U64} (h1 : 192 ≤ off.val) (h2 : off.val < 4096) (h8 : off.val % 8 = 0)
    (hg : ¬ GateField off.val) (htm : ¬ TimerField off.val) :
    IoRS (st := st) K Locks s (fld t off) ∧ IoWS (st := st) K Locks s (fld t off) := by
  rw [M.cur]; exact P.home h1 h2 h8 hg htm

/-- A queue link of the handler or its successor. -/
theorem VmMidF.link {y off : U64} (hy : y = dest ∨ ((L.epQ s1 ptr).end ≠ dest ∧ y = L.mem s1 (nextA .Ep dest)))
    (hoff : off.val = 3496 ∨ off.val = 3504) :
    IoRS (st := st) K Locks s (fld y off) ∧ IoWS (st := st) K Locks s (fld y off) := by
  obtain ⟨hyT, hb, hs⟩ := M.q y hy
  exact P.link hyT (by rw [hs]; exact recv_queued) hb M.lp hoff

theorem VmMidF.rt : IoWS (st := st) K Locks s (core.num.U64.wrapping_add r layout.reply.TCB) := by
  have h := rTcbA_val0 r
  have := M.rP.1; have := M.rP.2
  exact (P.reply M.rK (b := rTcbA r) ⟨by omega, by omega⟩ (by unfold Aligned; omega) M.lr).2

theorem VmMidF.wdHd : VmWd K (core.num.U64.wrapping_add ptr layout.ep.HEAD) := by
  have h := epHeadA_val (ep := ptr)
  have := M.ep.fits; have := M.ep.align
  exact P.wdEp (b := epHeadA ptr) M.epK ⟨by omega, by omega⟩

theorem VmMidF.wdTs : VmWd K (core.num.U64.wrapping_add ptr layout.ep.TAIL_STATE) := by
  have h := epTSA_val M.ep
  have := M.ep.fits; have := M.ep.align
  exact P.wdEp (b := epTSA ptr) M.epK ⟨by omega, by omega⟩

theorem VmMidF.wdRt : VmWd K (core.num.U64.wrapping_add r layout.reply.TCB) := by
  have h := rTcbA_val0 r
  have := M.rP.1; have := M.rP.2
  exact P.wdRp (b := rTcbA r) M.rK ⟨by omega, by omega⟩

/-- **The checks on a store answering `IoRS` words as `st`.** -/
theorem VmMidF.chk {gS : machine.Store S} {W : U64 → Prop} [GRd gS st (IoRS (st := st) K Locks s)] [GWr gS st W]
    {badge : U64} (C : FaultChecks st s1 t ptr badge dest r)
    (hhere : fastpath.schedulable_here gS s1 dest = fastpath.schedulable_here st s1 dest) :
    FaultChecks gS s1 t ptr badge dest r := by
  refine FaultChecks.guard (gS := gS) C (M.nd P _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
    (fun sl hsl => ?_) (M.ts P).1 (M.hd P).1
    (M.dh P (off := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
      (by simp [GField])).1 hhere ?_
    (P.gate (off := 3448#u64) M.dT (by simp) (by simp) (by simp) (by simp [GateField])) ?_
  · rw [M.cur] at hsl
    exact P.tslot P.cT hsl (by simp [layout.tcb.SLOT_FAULT_HANDLER])
  · rw [M.k]; exact P.ksw (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
  · refine ⟨(M.nd P l1Off (by rw [l1Off_val]; omega) (by rw [l1Off_val])).1, fun inv hinv => ?_⟩
    exact (M.nd P _ (by simp only [w64_val]; omega) (by simp only [w64_val]; omega)).1


/-- `set_fault` keeps every aligned word outside the faulting thread's TCB. -/
theorem VmMidF.sfo {w0 w1 w2 b : U64} (hb : Aligned b) (ho : b.val < t.val ∨ t.val + 4096 ≤ b.val) :
    L.mem (sfG (L := L) s1 t fl4_abi.consts.fault.VMFault w0 w1 w2) b = L.mem s1 b := by
  have ht' := M.hT t M.tT
  have ne : ∀ Kx : U64, Kx.val < 4096 → core.num.U64.wrapping_add t Kx ≠ b := fun Kx hKx e => by
    have := congrArg UScalar.val e; rw [field_val ht' hKx] at this; omega
  exact sfG_mem hb ⟨field_aligned ht' (K := 3376#u64) (by simp) (by simp), ne 3376#u64 (by simp)⟩
    ⟨field_aligned ht' (by simp) (by simp), ne _ (by simp)⟩ ⟨field_aligned ht' (by simp) (by simp), ne _ (by simp)⟩
    ⟨field_aligned ht' (by simp) (by simp), ne _ (by simp)⟩

/-- `set_fault` keeps every TCB word other than the four fault words. -/
theorem VmMidF.sft {w0 w1 w2 y Kx : U64} (hy : y ∈ T) (hK : Kx.val < 4096) (h8 : Kx.val % 8 = 0)
    (hne : Kx.val < 3376 ∨ 3400 < Kx.val) :
    L.mem (sfG (L := L) s1 t fl4_abi.consts.fault.VMFault w0 w1 w2) (core.num.U64.wrapping_add y Kx) =
      L.mem s1 (core.num.U64.wrapping_add y Kx) := by
  have ht' := M.hT t M.tT
  have hy' := M.hT y hy
  have ne : ∀ K2 : U64, K2.val < 4096 → 3376 ≤ K2.val → K2.val ≤ 3400 →
      core.num.U64.wrapping_add t K2 ≠ core.num.U64.wrapping_add y Kx :=
    fun K2 h1 h2 h3 => field_ne ht' hy' h1 hK (fun _ => by omega)
  exact sfG_mem (field_aligned hy' hK h8)
    ⟨field_aligned ht' (K := 3376#u64) (by simp) (by simp), ne 3376#u64 (by simp) (by simp) (by simp)⟩
    ⟨field_aligned ht' (by simp) (by simp), ne _ (by simp) (by simp) (by simp)⟩
    ⟨field_aligned ht' (by simp) (by simp), ne _ (by simp) (by simp) (by simp)⟩
    ⟨field_aligned ht' (by simp) (by simp), ne _ (by simp) (by simp) (by simp)⟩

theorem VmMidF.sfQ {w0 w1 w2 : U64} :
    L.epQ (sfG (L := L) s1 t fl4_abi.consts.fault.VMFault w0 w1 w2) ptr = L.epQ s1 ptr := by
  have hd := M.ep.disj t M.tT
  have := M.ep.align; have := M.ep.fits
  have h0 := M.sfo P (w0 := w0) (w1 := w1) (w2 := w2) (b := epHeadA ptr)
    (by unfold Aligned; rw [epHeadA_val]; omega) (by rw [epHeadA_val]; omega)
  have h8 := M.sfo P (w0 := w0) (w1 := w1) (w2 := w2) (b := epTSA ptr)
    (by unfold Aligned; rw [epTSA_val M.ep]; omega) (by rw [epTSA_val M.ep]; omega)
  unfold LawfulStore.epQ; rw [h0, h8]

/-- **The words `vmPre14` touches**, for the VM fault `VmFault w0 w1 ins`, the writes in any `W`
holding the `VmWd` words of `IoWS`. -/
theorem VmMidF.preRW {A : Type} (ar : machine.Arch A) (a1 : A) (w0 w1 : U64) (ins : Bool) {W : U64 → Prop}
    (hW : ∀ b, VmWd K b → IoWS (st := st) K Locks s b → W b) :
    VmPreRW (st := st) (IoRS (st := st) K Locks s) W ar s1 a1 t
      (error.Fault.VmFault w0 w1 ins) ptr dest r := by
  have hT := M.hT
  have ht' := hT t M.tT
  have hd' := hT dest M.dT
  have nT : ∀ y ∈ T, ∀ Kx : U64, Kx.val < 4096 → Kx.val ≠ 3376 →
      core.num.U64.wrapping_add y Kx ≠ faultA t :=
    fun y hy Kx hKx hne => field_ne (hT y hy) ht' hKx (K2 := 3376#u64) (by simp) (fun _ => by simpa using hne)
  refine
  { fw := ⟨hW _ (P.wdTcb (off := 3376#u64) M.tT (by simp) (by simp) (by simp))
        (M.th P (off := 3376#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2,
      hW _ (P.wdTcb (off := 3384#u64) M.tT (by simp) (by simp) (by simp))
        (M.th P (off := 3384#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2,
      hW _ (P.wdTcb (off := 3392#u64) M.tT (by simp) (by simp) (by simp))
        (M.th P (off := 3392#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2,
      hW _ (P.wdTcb (off := 3400#u64) M.tT (by simp) (by simp) (by simp))
        (M.th P (off := 3400#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2⟩
    ts := (M.ts P).1
    wh := hW _ (M.wdHd P) (M.hd P).2
    wt := hW _ (M.wdTs P) (M.ts P).2
    nx := (M.link P (y := dest) (off := 3496#u64) (Or.inl rfl) (Or.inl (by simp))).1
    pv := ?_
    dn := hW _ (P.wdTcb (off := 3496#u64) M.dT (by simp) (by simp) (by simp))
      (M.link P (y := dest) (off := 3496#u64) (Or.inl rfl) (Or.inl (by simp))).2
    dp := hW _ (P.wdTcb (off := 3504#u64) M.dT (by simp) (by simp) (by simp))
      (M.link P (y := dest) (off := 3504#u64) (Or.inl rfl) (Or.inr (by simp))).2
    ib := P.gate (off := 3512#u64) M.dT (by simp) (by simp) (by simp) (by simp [GateField])
    bs := ⟨_, tcb_slot_eq dest _, P.tslot M.dT (tcb_slot_eq dest _) (by simp [layout.tcb.SLOT_BUFFER])⟩
    ty := ?_
    mrs :=
      { ft := (M.th P (off := 3376#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
        w0 := (M.th P (off := 3384#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
        w1 := (M.th P (off := 3392#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
        w2 := (M.th P (off := 3400#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
        ip := by rw [M.cur]; exact (P.reg (by simp [layout.reg.FAULT_IP])).1
        mr := fun i _ r e => hW _ (P.wdReg M.dT (post_of_ok (msg.msg_register.lt i) e))
          (P.regOf M.dT M.aff (post_of_ok (msg.msg_register.lt i) e)).2 }
    mi := hW _ (P.wdReg M.dT (by simp [layout.reg.MSG_INFO])) (P.regOf M.dT M.aff (by simp [layout.reg.MSG_INFO])).2
    bd := hW _ (P.wdReg M.dT (by simp [layout.reg.BADGE, layout.reg.RDI]))
      (P.regOf M.dT M.aff (by simp [layout.reg.BADGE, layout.reg.RDI])).2
    rt := hW _ (M.wdRt P) (M.rt P)
    ro := hW _ (P.wdTcb (off := 3360#u64) M.tT (by simp) (by simp) (by simp))
      (M.th P (off := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2 }
  · -- the successor's `EP_PREV`
    intro s2 tl i6 e2 etl hne e6
    rw [set_fault_vm] at e2
    obtain rfl := ok_inj_ff e2
    rw [obj.Ep.tail.ok] at etl
    obtain rfl := ok_inj_ff etl
    rw [obj.Tcb.ep_next.ok] at e6
    obtain rfl := ok_inj_ff e6
    rw [M.sfQ P] at hne
    have en : L.mem (sfG (L := L) s1 t fl4_abi.consts.fault.VMFault w0 w1 (if ins then 1#u64 else 0#u64))
        (nextA .Ep dest) = L.mem s1 (nextA .Ep dest) := by
      rw [nextA_eq']; exact M.sft P M.dT (by simp [nextOff]) (by simp [nextOff]) (Or.inr (by simp [nextOff]))
    rw [en]
    exact hW _ (P.wdTcb (off := 3504#u64) (M.q _ (Or.inr ⟨hne, rfl⟩)).1 (by simp) (by simp) (by simp))
      (M.link P (y := L.mem s1 (nextA .Ep dest)) (off := 3504#u64) (Or.inr ⟨hne, rfl⟩) (Or.inr (by simp))).2
  · -- the fault type read back after the dequeue
    intro s2 tl s3 s4 s5 e2 etl e3 e4 e5
    rw [set_fault_vm] at e2
    obtain rfl := ok_inj_ff e2
    generalize hs2 : sfG (L := L) s1 t fl4_abi.consts.fault.VMFault w0 w1 (if ins then 1#u64 else 0#u64) = s2
      at etl e3 e4 e5
    rw [obj.Ep.tail.ok] at etl
    obtain rfl := ok_inj_ff etl
    have e45 : s5 = epFast (L := L) s2 ptr dest := by
      rw [obj.Tcb.set_ep_next.ok] at e4
      obtain rfl := ok_inj_ff e4
      rw [obj.Tcb.set_ep_prev.ok] at e5
      obtain rfl := ok_inj_ff e5
      by_cases htl : (L.epQ s2 ptr).end = dest
      · rw [if_pos htl, obj.Ep.set_queue.ok] at e3
        obtain rfl := ok_inj_ff e3
        unfold epFast; simp only [htl, ↓reduceIte]
      · rw [if_neg htl, obj.Tcb.ep_next.ok] at e3
        simp only [bind_ok] at e3
        rw [obj.Tcb.set_ep_prev.ok] at e3
        simp only [bind_ok] at e3
        rw [obj.Ep.set_queue.ok] at e3
        obtain rfl := ok_inj_ff e3
        unfold epFast; simp only [htl, ↓reduceIte]
    subst e45
    rw [fault_type_ok]
    congr 1
    have fA : Aligned (faultA t) := field_aligned ht' (K := 3376#u64) (by simp) (by simp)
    have vF : (faultA t).val = t.val + 3376 := field_val ht' (K := 3376#u64) (by simp)
    have hdj := M.ep.disj t M.tT
    have hsucc : (L.epQ s2 ptr).end ≠ dest → L.mem s2 (nextA .Ep dest) ∈ T := fun h => by
      have eQ : L.epQ s2 ptr = L.epQ s1 ptr := by rw [← hs2]; exact M.sfQ P
      have en : L.mem s2 (nextA .Ep dest) = L.mem s1 (nextA .Ep dest) := by
        rw [← hs2, nextA_eq']; exact M.sft P M.dT (by simp [nextOff]) (by simp [nextOff]) (Or.inr (by simp [nextOff]))
      rw [eQ] at h; rw [en]
      exact (M.q _ (Or.inr ⟨h, rfl⟩)).1
    rw [epFast_mem fA
      ⟨by unfold Aligned; rw [epHeadA_val]; exact M.ep.align, fun e => by
        have := congrArg UScalar.val e; rw [epHeadA_val, vF] at this; omega⟩
      ⟨by unfold Aligned; rw [epTSA_val M.ep]; have := M.ep.align; omega, fun e => by
        have := congrArg UScalar.val e; rw [epTSA_val M.ep, vF] at this; omega⟩
      ⟨by rw [nextA_eq']; exact field_aligned hd' (by simp [nextOff]) (by simp [nextOff]),
        by rw [nextA_eq']; exact nT dest M.dT _ (by simp [nextOff]) (by simp [nextOff])⟩
      ⟨by rw [prevA_eq']; exact field_aligned hd' (by simp [prevOff]) (by simp [prevOff]),
        by rw [prevA_eq']; exact nT dest M.dT _ (by simp [prevOff]) (by simp [prevOff])⟩
      (fun h => ⟨by rw [prevA_eq']; exact field_aligned (hT _ (hsucc h)) (by simp [prevOff]) (by simp [prevOff]),
        by rw [prevA_eq']; exact nT _ (hsucc h) _ (by simp [prevOff]) (by simp [prevOff])⟩)]
    rw [← hs2]
    unfold sfG
    have ne : ∀ Kx : U64, Kx.val < 4096 → Kx.val ≠ 3376 → core.num.U64.wrapping_add t Kx ≠ faultA t :=
      fun Kx hKx hne => nT t M.tT Kx hKx hne
    rw [mem_wr_ne' (field_aligned ht' (by simp) (by simp)) fA (ne _ (by simp) (by simp)),
      mem_wr_ne' (field_aligned ht' (by simp) (by simp)) fA (ne _ (by simp) (by simp)),
      mem_wr_ne' (field_aligned ht' (by simp) (by simp)) fA (ne _ (by simp) (by simp)), L.mem_wr_same fA]

end


/-- The current SC's head refill word lies outside the TCBs and nodes. -/
theorem bxi_headOut (B : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) {c : U64} (hc : c ∈ Scs) :
    OutsideObjs st T Cs s (headA c) := by
  obtain ⟨⟨Q, Rq, hq⟩, -, ⟨hO, -, -⟩, -, hS⟩ := B
  obtain ⟨hP, hz⟩ := hO.sc _ hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hh := headA_val' hP hz
  exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))

/-- A head refill read after `update_timestamp`, as one at the entry. -/
theorem rdHead_ut {R : U64 → Prop} (B : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (n : U64) {c : U64} (hc : c ∈ Scs)
    (h : RdHead (L := L) R s c) : RdHead (L := L) R (utW (L := L) s n) c := by
  obtain ⟨-, hN, -⟩ := B.tcbNode
  have hcC : L.cpu s ∈ Cs := by obtain ⟨⟨Q, Rq, hq⟩, -, -, -, -⟩ := B; exact hq.cur
  have e : L.rhead (utW (L := L) s n) c = L.rhead s c := ut_out hN hcC n (bxi_headOut B hc)
  unfold RdHead at h ⊢; rw [e]; exact h

/-- The `STATE` writes of the accepted VM-fault run as a hypothesis on the store `gS`: a thread
of `T` homed on this core (queued at the entry only on a held lock) is written the values
`INACTIVE`, `RUNNING`, `BLOCKED_ON_REPLY` as by `st`. -/
def VmSW (st : machine.Store S) [L : LawfulStore st] (gS : machine.Store S) (T : Set U64)
    (Locks : S → U64 → Prop) (s : S) : Prop :=
  ∀ d v, d ∈ T → L.mem s (affA d) = L.cpu s →
    (OwnMap.QueuedState (L.mem s (stA d)) → Locks s (L.mem s (blockA d))) →
    (v = sched.TS_INACTIVE ∨ v = sched.TS_RUNNING ∨ v = sched.TS_BLOCKED_ON_REPLY) → SWr gS st d v

/-- **The accepted VM-fault local path, up to its tail, on any store `gS`** answering `IoRS K Locks s`
words as `st`, writes of the `VmWd` words of `IoWS K Locks s` as `st` (`hW`) and the `STATE` writes
(`VmSW`): given the tail from the handler `Running` (`faultTail3`) agrees on `gS`, the run on `gS`
ends exactly as the real run. -/
theorem vm_acc_of_tail {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s' : S} {a a' : A}
    {addr code : U64} (P : VmFPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s)
    {gS : machine.Store S} {W : U64 → Prop} [GRd gS st (IoRS (st := st) K Locks s)] [GWr gS st W]
    (hW : ∀ b, VmWd K b → IoWS (st := st) K Locks s b → W b) (hSW : VmSW st gS T Locks s)
    (htail : ∀ s1 a1 t ins ptr badge dest r s14, sched.update_timestamp st ar s a = ok (s1, a1) →
      sched.cur_thread st s1 = ok t → FaultChecks st s1 t ptr badge dest r →
      vmPre14 st ar s1 a1 t (error.Fault.VmFault addr code ins) fl4_abi.consts.fault.VMFault ptr badge dest r =
        ok s14 →
      faultTail3 st ar s14 a1 dest = ok (true, s', a') →
      faultTail3 gS ar s14 a1 dest = ok (true, s', a'))
    (h : syscall.handle_vm_fault_local st ar s a addr code = ok (true, s', a')) :
    syscall.handle_vm_fault_local gS ar s a addr code = ok (true, s', a') := by
  have B := P.base
  have hN := B.np
  have hT := B.tp
  have hcC : L.cpu s ∈ Cs := by obtain ⟨⟨Q, Rq, hq⟩, -, -, -, -⟩ := B.bxi; exact hq.cur
  -- `update_timestamp` is `utW`
  have hut : ∀ s1 a1, sched.update_timestamp st ar s a = ok (s1, a1) → ∃ n, s1 = utW (L := L) s n := by
    intro s1 a1 eu
    obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
    rw [update_timestamp_ok ar hN hn] at eu
    exact ⟨n, (Prod.mk.inj (ok_inj_ff eu)).1.symm⟩
  refine syscall.handle_vm_fault_local.guard_acc (gS := gS) ar
    (B.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
    (hW _ (B.wdNode (by simp [layout.node.CUR_TIME]))
      (B.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2)
    (B.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
    (hW _ (B.wdNode (by simp [layout.node.CONSUMED]))
      (B.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2) ?_ ?_ ?_ h
  · intro s1 a1 eu
    obtain ⟨n, rfl⟩ := hut s1 a1 eu
    rw [ut_nodeAt, ut_nodeAt, ut_nodeAt]
    exact ⟨(B.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1,
      (B.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1,
      (B.nd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1⟩
  · intro s1 a1 csc eu ecsc
    obtain ⟨n, rfl⟩ := hut s1 a1 eu
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecsc
    have e : csc = L.cscW s := by
      rw [← ut_csc hN n]; exact (ok_inj_ff ecsc).symm
    subst e
    exact rdHead_ut B.bxi n B.cscS (B.cscacc.head B.cscwf)
  · intro s1 a1 t i2 f eu et ef ptr badge dest r C
    have et' : t = L.curW s1 := by rw [cur_thread_ok] at et; exact (ok_inj_ff et).symm
    have hlk := P.lk a s1 a1 ptr badge dest r eu (by rw [← et']; exact C)
    have HY := P.hyp a s1 a1 eu
    have htl := htail s1 a1 t (i2 != 0#u64) ptr badge dest r
    have ef' : f = error.Fault.VmFault addr code (i2 != 0#u64) := by
      unfold vspace.vm_fault at ef; exact (ok_inj_ff ef).symm
    subst ef'
    obtain ⟨n, rfl⟩ := hut s1 a1 eu
    -- P1's facts at the post-prefix state
    have hF := faultEntAt_ofT HY.bxi et HY.nb HY.cap HY.user HY.buf HY.asid
    obtain ⟨hr, rest, E⟩ := hF.2 ptr badge dest r C
    have hrecv := faultRecv_ofT HY.bxi et HY.cap C
    have hpH : H ptr = some .ep := by
      obtain ⟨sl, x, y, g, gr, esl, ecap, -⟩ := C.cap
      have h1 := HY.cap
      rw [← et', esl, WP.spec_ok, ecap, WP.spec_ok] at h1
      exact h1.1 ptr badge x y g gr rfl
    have hhd : dest = L.mem (utW (L := L) s n) (epHeadA ptr) := by
      have h1 := C.head
      rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) _ ptr)] at h1; exact (ok_inj_ff h1).symm
    have hQ := vm_queue HY.bxi hpH E.hst hhd hrecv
    have hdT : dest ∈ T := E.hq.mem dest (by simp)
    have HF := here_facts (L := L) C.here
    have hrP : r.val % 32 = 0 ∧ r.val + 32 ≤ 2 ^ 64 := by
      obtain ⟨-, -, hX, -, -⟩ := HY.bxi; exact hX.1.rp r hr
    have M : VmMidF st K T H Rp Locks s (utW (L := L) s n) t ptr dest r :=
      { k := utW_ksb s n
        c := utW_cpu s n
        cur := by rw [et', ut_cur hN n]
        tT := E.ht
        dT := hdT
        hT := hT
        hN := hN
        ep := E.hE
        epK := P.hEp ptr hpH
        rK := P.hRp r hr
        rP := hrP
        lp := hlk.1
        lr := hlk.2
        aff := by
          have e := ut_tcb hN hT n hdT (Kx := 3520#u64) (by simp) (by simp)
          calc L.mem s (affA dest) = L.mem (utW (L := L) s n) (affA dest) := e.symm
            _ = L.cpu (utW (L := L) s n) := HF.aff
            _ = L.cpu s := utW_cpu s n
        q := fun y hy => by
          obtain ⟨hyT, hb, hs⟩ := hQ y hy
          refine ⟨hyT, ?_, ?_⟩
          · rw [← hb, blockA_eq]; exact (ut_tcb hN hT n hyT (by simp) (by simp)).symm
          · rw [← hs, stA_eq]; exact (ut_tcb hN hT n hyT (by simp) (by simp)).symm }
    -- `schedulable_here` on the guarded store
    have etm : L.mem (utW (L := L) s n) (tmA (L := L) (utW (L := L) s n)) = L.mem s (tmA (L := L) s) := by
      show L.mem (utW (L := L) s n) (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) layout.node.TIMER_MIN) = _
      rw [ut_nodeAt]
      exact ut_node hN n (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
        (by simp [layout.node.TIMER_MIN, layout.node.CUR_TIME]) (by simp [layout.node.TIMER_MIN, layout.node.CONSUMED])
    have erh : L.mem (utW (L := L) s n) (rhA (L := L) (utW (L := L) s n)) = L.mem s (rhA (L := L) s) := by
      show L.mem (utW (L := L) s n) (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) layout.node.RELEASE_HEAD) = _
      rw [ut_nodeAt]
      exact ut_node hN n (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
        (by simp [layout.node.RELEASE_HEAD, layout.node.CUR_TIME])
        (by simp [layout.node.RELEASE_HEAD, layout.node.CONSUMED])
    have hhere := fastpath.schedulable_here.guard (gS := gS)
      (utW (L := L) s n) dest
      (M.nd B _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
      (M.nd B _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1
      (M.nd B _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])).1
      (fun h0 => by rw [etm] at h0 ⊢; exact B.td h0)
      (fun h0 => by
        rw [erh] at h0 ⊢
        obtain ⟨hrT, hscS, -⟩ := bxi_rh B.bxi h0
        have esc : L.mem (utW (L := L) s n) (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
          ut_tcb hN hT n hrT (Kx := 3464#u64) (by simp) (by simp)
        rw [esc]
        obtain ⟨h1, h2⟩ := B.rs h0
        exact ⟨h1, rdHead_ut B.bxi n hscS h2⟩)
      (by rw [utW_ksb]; exact B.ksw (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME]))
      (by rw [utW_ksb]; exact B.ksw (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN]))
      (B.gate (off := 3520#u64) hdT (by simp) (by simp) (by simp) (by simp [GateField]))
      (B.gate (off := 3432#u64) hdT (by simp) (by simp) (by simp) (by simp [GateField]))
      (B.gate (off := 3464#u64) hdT (by simp) (by simp) (by simp) (by simp [GateField]))
      (M.dh B (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
        (by simp [GField])).1
    have hq0 := M.q dest (Or.inl rfl)
    have hsd : ∀ v, (v = sched.TS_INACTIVE ∨ v = sched.TS_RUNNING) → SWr gS st dest v := fun v hv =>
      hSW dest v hdT M.aff (fun _ => by rw [hq0.2.1]; exact M.lp) (hv.elim Or.inl (fun e => Or.inr (Or.inl e)))
    have nq : ¬ OwnMap.QueuedState (L.mem s (stA (L.curW s))) := by
      unfold OwnMap.QueuedState
      rcases B.run with e | e <;> rw [e] <;> simp [sched.TS_RESTART, sched.TS_RUNNING]
    have hst : SWr gS st t sched.TS_BLOCKED_ON_REPLY := by
      rw [M.cur]
      exact hSW _ _ B.cT B.curAff (fun hq => absurd hq nq) (Or.inr (Or.inr rfl))
    exact
    { chk := M.chk B (gS := gS) C hhere
      pre := vmPre14.guard (gS := gS) ar _ a1 t addr code (i2 != 0#u64) _ ptr badge dest r
        (M.preRW B ar a1 addr code _ hW) hsd hst
      tail := fun s14 e14 h3 => htl s14 eu et C e14 h3 }

end

end Fl4Proofs.P2.PathObl
