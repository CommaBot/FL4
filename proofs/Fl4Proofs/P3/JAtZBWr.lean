/-
P3 (line mmuAD, gen 24): **a write of a VCPU word keeps `JAtZV V X` for any `V`** — the first `JAtZB`
preservation proof from a VM-epoch state (gen 23 plan item 2).

`JAtZ.vcpuWrJ` (P3/VcpuWrJ, over `JAtZ.frameWrJ` of P3/XTopJointReadFpu and the `cs_frame` family of
P3/XTopJointStep) reads `JAtZ.ext` only to rebuild `ext` at the end (`J.ext.step hvT hv` in `JAtZ.cs_frame`,
the `VKeep` argument of `cs_frameK`). This module copies that chain over `JAtZB` (names `JAtZB.<same name>`;
`JCs.same` → `JCs.sameB`): `vsFr_other`, `tcbs_eq`, `deadY_tcb`, `deadP_keep`, `idleW_keep`, `kern_keepA`,
`notDbg'`, `notDbg`, `tcbZ`, `tdA_val'`, `jcov_keep`, `cs_frameVD`, `cs_frameV`, `bfK`, `cs_frame`, `liveX`,
`zDX`, `cs_frameK`, `vsShr`, `vsSS`, `JCs.sameB`, `frameWrJ`, `vcpuWrJ`. Proofs verbatim, except that the
`JExt` argument (`hext`) of `cs_frameVD` / `cs_frameV` and the `VKeep` argument (`hv`) of `cs_frame` /
`cs_frameK` are dropped (they only fed the dropped field).

**`JAtZV.vcpuWr`**: from `J : JAtZV V X …`, writing any aligned word `w` of a VCPU `p ∈ V` other than its
`TCB` (offset 20480), `NEXT` (20488) and `PREV` (20496) words keeps `JAtZV V X` with σ unchanged (guest-state /
VMCS-shadow writes, `vcpu.decode`'s register writes, `vcpu.enter`'s VMX/SVM words). All of `vcpuWrJ`'s side
facts come from `JVm` (`spec`, `heap`, `ks`) and `JCarry.bufPg` + `JVm.sep` (no IPC-buffer word in the VCPU);
`JExtV` by `JExtV.of_writes` + `JVLay.nJS_v`; `RunVmB` as in `JAtZV.vcpuWr0`; `VList` by `VList.writes` (the list
words of other VCPUs by `JVLay.vv`, the head word by `JVm.ks`); `JVm` (it reads only `ksb`).

No named premise (the three excluded offsets are the statement's scope: those words are written only by
`vcpu.init` / `finalise` / SetTCB / detach, proved separately in gens 20–23). No existing statement changed.
-/
import Fl4Proofs.P3.JAtZBLay
import Fl4Proofs.P3.VcpuWrJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **A VSpace frame is an `other` object of `H` of at least a page**: a
spec arch object (`VsRel.pool`, `PtRel`), so `H`'s (`SpecCover.arch`). -/
theorem JAtZB.vsFr_other {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {q : U64} (hq : VsFr Z q) : ∃ n, 12 ≤ n ∧ H q = some (.other n) := by
  have hF := J.xtop.fin
  have hk : ∃ ao, σ.kheap q.bv = some (.archObj ao) := by
    rcases hq with hq | hq | hq | hq | hq
    · obtain ⟨f, hf, -⟩ := hF.2.1.pool q hq; exact ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l4 q hq; exact ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l3 q hq; exact ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l2 q hq; exact ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l1 q hq; exact ⟨_, hf⟩
  obtain ⟨ao, hao⟩ := hk
  obtain ⟨n, hn, hH⟩ := J.cover.arch _ ao hao
  exact ⟨n, hn, hH⟩

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- The sets' TCBs and replies are `H`'s. -/
theorem JAtZB.tcbs_eq {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) : Z.T = P1.Heap.tcbs H ∧ Z.R = P1.Heap.replies H := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact ⟨Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩,
    Set.ext fun r => ⟨fun h => J.zH.2.2.1 r h, fun h => J.hset.2.2 r h⟩⟩

end

section
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **A dead thread's `YIELD_TO` word stays null** (`YieldRel` before and
after, the spec's field kept null). -/
theorem JAtZB.deadY_tcb {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hY' : YieldRel Z.T Z.C (L.mem s') σ') {q : U64} (hYD : YDeadKeep σ σ' q.bv) (hqT : q ∈ Z.T)
    (h0 : L.mem s (P1.yieldA q) = 0#u64) : L.mem s' (P1.yieldA q) = 0#u64 := by
  obtain ⟨x, hx, e⟩ := J.yld.tcb q hqT
  obtain ⟨y, hy, e'⟩ := hY'.tcb q hqT
  exact optRef_eq_none (by rw [← e', hYD.1 x hx (by rw [e, h0, optRef_zero]) y hy])

end

section
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 4000000 in
/-- **The dead stay dead** (module docstring). -/
theorem JAtZB.deadP_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hS' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ') (hI' : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s') σ')
    {q : U64}
    (hT : ∀ x, σ.kheap q.bv = some (.tcb x) → tsCode x.tcbState = 0 → ∃ y, σ'.kheap q.bv = some (.tcb y) ∧
      y.tcbState = x.tcbState ∧ y.tcbBoundNotification = x.tcbBoundNotification ∧
      (y.tcbSchedContext = x.tcbSchedContext ∨ y.tcbSchedContext = none))
    (hE : ∀ x, σ.kheap q.bv = some (.endpoint x) → σ'.kheap q.bv = some (.endpoint x))
    (hN : ∀ x, σ.kheap q.bv = some (.notification x) → ∃ y, σ'.kheap q.bv = some (.notification y) ∧
      (y.ntfnObj = x.ntfnObj ∨ ∀ l, y.ntfnObj ≠ .waitingNtfn l) ∧ y.ntfnBoundTcb = x.ntfnBoundTcb ∧
      (y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none))
    (hRp : ∀ x, σ.kheap q.bv = some (.reply x) → ∃ y, σ'.kheap q.bv = some (.reply y) ∧ y.replyTcb = x.replyTcb)
    (hSc : ∀ x n, σ.kheap q.bv = some (.schedContext x n) → ∃ y, σ'.kheap q.bv = some (.schedContext y n) ∧
      (y.scTcb = x.scTcb ∨ y.scTcb = none) ∧ (y.scNtfn = x.scNtfn ∨ y.scNtfn = none))
    (hRW : q ∈ Z.C → L.mem s' (P1.scReplyA q) = L.mem s (P1.scReplyA q))
    (hOut : ∀ z, H q = some (.sc z) → q ∉ Z.C → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s' (scW q K) = L.mem s (scW q K))
    (hidle : σ'.idleThread = σ.idleThread) (hAS : ActSched σ')
    (hY' : YieldRel Z.T Z.C (L.mem s') σ') (hYD : YDeadKeep σ σ' q.bv)
    (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have hI := hX.ipc
  refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_, fun hq => ?_, fun z hq => ?_⟩
  · -- a TCB
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd.1 hq
    have hqT : q ∈ Z.T := by rw [J.tcbs_eq.1]; exact hq
    obtain ⟨x, hk, hR⟩ := hI.tcb q hqT
    obtain ⟨x', hk', hR'⟩ := hI'.tcb q hqT
    have hst0 : tsCode x.tcbState = 0 := by
      have := hR.st; rw [← stA_tStA, d1] at this; unfold sched.TS_INACTIVE at this; simpa using this.symm
    obtain ⟨y, hy, hstate, hso, e⟩ := hT x hk hst0
    rw [hk'] at hy; cases hy
    have hxs : x.tcbSchedContext = none := by rw [hR.sc, d2, optRef_zero]
    have hxs' : x'.tcbSchedContext = none := by
      rcases e with e | e
      · rw [e, hxs]
      · exact e
    refine ⟨?_, ?_, ?_, ?_, ?_, J.deadY_tcb hY' hYD hqT d6⟩
    · have h1 : (L.mem s' (tStA q)).val = (L.mem s (tStA q)).val := by rw [hR'.st, hR.st, hstate]
      rw [stA_tStA, UScalar.eq_of_val_eq h1, ← stA_tStA, d1]
    · exact optRef_eq_none (by rw [← hR'.sc, hxs'])
    · have hb : x'.tcbBoundNotification = x.tcbBoundNotification := hso
      have h1 := hR.bound
      rw [show tBoundA q = P1.boundA q from rfl, d3, optRef_zero] at h1
      exact optRef_eq_none (by rw [show P1.boundA q = tBoundA q from rfl, ← hR'.bound, hb, h1])
    · intro e
      have hact := hS'.act
      have ea : L.actionW s' = Sched.nodeW st s' Z.c layout.node.SCHED_ACTION := by
        unfold P1.LawfulStore.actionW Sched.nodeW; rw [hc'.cur]
      rw [← ea, ← e] at hact
      revert hact
      cases hsa : σ'.schedulerAction with
      | resumeCurThread =>
        intro h; simp only [ActRel] at h; subst h
        rw [J.kern.h0] at hq; cases hq
      | chooseNewThread =>
        intro h; simp only [ActRel] at h; subst h
        have := J.kern.heap.align _ _ hq
        simp [P1.HKind.bits] at this
      | switchThread t =>
        intro h; simp only [ActRel] at h
        obtain ⟨-, -, ht⟩ := h
        obtain ⟨x2, scp, -, -, hk2, hsc2, -⟩ := schedulable_inv (hAS t hsa)
        rw [← ht, hk'] at hk2; cases hk2
        rw [hxs'] at hsc2; cases hsc2
    · have ei : L.idleW s' = L.idleW s := by
        unfold P1.LawfulStore.idleW
        apply P1.eq_of_bv
        have h1 := hs'.idleTh; have h2 := hs.idleTh
        unfold Sched.nodeW at h1 h2
        rw [hc'.cur, hc.cur, ← h1, ← h2, hidle]
      rw [ei]; exact d5
  · -- an endpoint
    have hqE : q ∈ Z.E := J.hset.1 q hq
    obtain ⟨x, hk, hR⟩ := hI.ep q hqE
    obtain ⟨x', hk', hR'⟩ := hI'.ep q hqE
    rw [hE x hk] at hk'; cases hk'
    rw [epState_eq, stOf_ep hR hR', ← epState_eq]; exact hd.2.1 hq
  · -- a notification
    obtain ⟨d1, d2, d3⟩ := hd.2.2.1 hq
    have hqN : q ∈ Z.N := J.hset.2.1 q hq
    obtain ⟨x, hk, hR⟩ := hI.ntfn q hqN
    obtain ⟨x', hk', hR'⟩ := hI'.ntfn q hqN
    obtain ⟨y, hy, ho, hb, e⟩ := hN x hk
    rw [hk'] at hy; cases hy
    have hxs : x.ntfnSc = none := by rw [hR.sc, show nScA q = P1.ntfnScA q from rfl, d3, optRef_zero]
    have hxs' : x'.ntfnSc = none := by
      rcases e with e | e
      · rw [e, hxs]
      · exact e
    refine ⟨?_, ?_, ?_⟩
    · rw [epState_eq]
      have hO' := hR'.obj
      rcases ho with ho | ho
      · rw [ho] at hO'
        rw [stOf_ntfn hR.obj hO', ← epState_eq]; exact d1
      · revert hO'
        cases hx' : x'.ntfnObj with
        | waitingNtfn l => exact absurd hx' (ho l)
        | idleNtfn => intro hO'; rw [hO'.1]; decide
        | activeNtfn b => intro hO'; rw [hO'.1]; decide
    · have h1 := hR.bound
      rw [show nBoundA q = P1.ntfnBtA q from rfl, d2, optRef_zero] at h1
      exact optRef_eq_none (by rw [show P1.ntfnBtA q = nBoundA q from rfl, ← hR'.bound, hb, h1])
    · exact optRef_eq_none (by rw [show P1.ntfnScA q = nScA q from rfl, ← hR'.sc, hxs'])
  · -- a reply
    have hqR : q ∈ Z.R := J.hset.2.2 q hq
    obtain ⟨x, hk, hR⟩ := hI.reply q hqR
    obtain ⟨x', hk', hR'⟩ := hI'.reply q hqR
    obtain ⟨y, hy, e⟩ := hRp x hk
    rw [hk'] at hy; cases hy
    have h1 := hR
    rw [show Endp.rTcbA q = P1.rTcbA q from rfl, hd.2.2.2.1 hq, optRef_zero] at h1
    exact optRef_eq_none (by rw [show P1.rTcbA q = Endp.rTcbA q from rfl, ← hR', e, h1])
  · -- an SC
    obtain ⟨d1, d2, d3, d4⟩ := hd.2.2.2.2 z hq
    by_cases hqC : q ∈ Z.C
    · obtain ⟨x, n, hk, hR⟩ := hs.scs q hqC
      obtain ⟨x', n', hk', hR'⟩ := hs'.scs q hqC
      obtain ⟨y, hy, e1, e2⟩ := hSc x n hk
      rw [hk'] at hy; cases hy
      have hxt : x.scTcb = none := by rw [hR.tcb, scW_tcb, d1, optRef_zero]
      have hxn : x.scNtfn = none := by rw [hR.ntfn, scW_ntfn, d3, optRef_zero]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← scW_tcb]; refine optRef_eq_none ?_; rw [← hR'.tcb]
        rcases e1 with e | e
        · rw [e, hxt]
        · exact e
      · rw [hRW hqC]; exact d2
      · rw [← scW_ntfn]; refine optRef_eq_none ?_; rw [← hR'.ntfn]
        rcases e2 with e | e
        · rw [e, hxn]
        · exact e
      · rw [scYieldFromA_eq]; refine optRef_eq_none ?_; rw [← hR'.yieldFrom]
        exact hYD.2 x _ hk (by rw [hR.yieldFrom, ← scYieldFromA_eq, d4, optRef_zero]) x' _ hk'
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← scW_tcb, hOut z hq hqC _ (by decide) (by decide), scW_tcb]; exact d1
      · rw [scReplyA_eq', hOut z hq hqC _ (by decide) (by decide), ← scReplyA_eq']; exact d2
      · rw [← scW_ntfn, hOut z hq hqC _ (by decide) (by decide), scW_ntfn]; exact d3
      · rw [scYieldFromA_eq, hOut z hq hqC _ (by decide) (by decide), ← scYieldFromA_eq]; exact d4

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **The idle words kept**: both states relate the current core's
`IDLE_THREAD` and `IDLE_SC` words to the spec's `idle_thread` and `idle_sc`
(`SchedSpec.idleTh`, `SchedSpec.idleSc`), which the step keeps. -/
theorem JAtZB.idleW_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hS' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ') (hid : σ'.idleThread = σ.idleThread)
    (hisc : σ'.idleSc = σ.idleSc) : Sched.IdleKeep (L := L) s s' := by
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  constructor
  · unfold P1.LawfulStore.idleW
    apply P1.eq_of_bv
    have h1 := hs'.idleTh; have h2 := hs.idleTh
    unfold Sched.nodeW at h1 h2
    rw [hc'.cur, hc.cur, ← h1, ← h2, hid]
  · unfold Sched.idleScW
    apply P1.eq_of_bv
    have h1 := hs'.idleSc; have h2 := hs.idleSc
    unfold Sched.nodeW at h1 h2
    rw [hc'.cur, hc.cur, h1, h2, hisc]

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **`JKern` across an arch step** (`kern_keep` with the global PML4 kept a
PML4 rather than every arch object kept). -/
theorem JAtZB.kern_keepA {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hks : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s)
    (hS' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ') (F : ArFr σ σ')
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    JKern (L := L) arI H Cs D Z.th s' σ' := by
  have K := J.kern
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have ecw : L.curW s' = L.curW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curThread; have h2 := hs.curThread
    unfold P1.LawfulStore.curW
    rw [hcpu, hna, hc.cur]
    unfold Sched.nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, F.ct]
  have ecs : L.cscW s' = L.cscW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curSc; have h2 := hs.curSc
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
    rw [hcpu, hna, hc.cur]
    unfold Sched.nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, F.csc]
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  refine ⟨fun sl h => K.orig sl (by rw [← F.orig]; exact h), by rw [ecw, F.ct]; exact K.cur,
    by rw [ecw]; exact K.curT, by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
    by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu, ecw]; exact K.dwNe, ?_,
    by rw [F.gpml4]; exact F.hasPm K.gpm, by rw [F.gpml4]; exact K.ga, by rw [F.gpml4]; exact K.gf,
    K.heap, K.h0, by rw [hks]; exact K.hks, by rw [hks]; exact K.hksIn, fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
    by rw [hks]; exact K.ksbFit, by rw [hks]; exact K.ksbAl, by rw [hks, hcpu]; exact K.nodeFit,
    by rw [hcpu]; exact K.cpuCs, by rw [ecw]; exact K.curH, by rw [ecs]; exact K.cscH,
    K.csLt, K.cs0, K.csN, K.tdx.frame F.plat⟩
  rw [hna, hDbg]; exact K.head

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **A word outside the TCBs and off the nodes' head words is no debug word.** -/
theorem JAtZB.notDbg' {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hobj : ∀ p, H p = some .tcb → b.val < p.val ∨ p.val + 2 ^ P1.HKind.bits .tcb ≤ b.val)
    (hnode : ∀ c ∈ Cs, b.val ≠ L.nodeBase s c + 88) :
    ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b := by
  obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
  have hT := hq.tcbs
  have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
  rintro (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
  · have h1 := hobj y hy
    rw [e, show P1.dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, P1.field_val (hT y hy) (by simp), e12]
      at h1
    have : (3576#u64 : U64).val = 3576 := by simp
    omega
  · have h1 := hobj y hy
    rw [e, show P1.dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, P1.field_val (hT y hy) (by simp), e12]
      at h1
    have : (3584#u64 : U64).val = 3584 := by simp
    omega
  · have h1 := hnode c hc
    rw [e, P1.nodeAt_val (hq.nodes c hc) (by simp [P1.debug_val]), P1.debug_val] at h1
    exact h1 rfl

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **A word outside the TCBs and the nodes is no debug word.** -/
theorem JAtZB.notDbg {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hobj : ∀ p, H p = some .tcb → b.val < p.val ∨ p.val + 2 ^ P1.HKind.bits .tcb ≤ b.val)
    (hnode : ∀ c ∈ Cs, b.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ b.val) :
    ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b :=
  J.notDbg' hobj fun c hc => by rcases hnode c hc with h | h <;> omega

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- A TCB of `H` is in `Z.T`. -/
theorem JAtZB.tcbZ (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : H t = some .tcb) : t ∈ Z.T := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact J.thT t ((hJ.tcb t).2 ht)

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

theorem JAtZB.tdA_val' (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) :
    (P1.tdA t).val = t.val + 3528 :=
  Notif.tfield_val (J.ip.e.tcb t ht) (K := 3528#u64) (by simp)

end

section
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **`JCovD` across a step keeping every slot and the dead dead**
(`JCovD.same`, the MDB kept). -/
theorem JAtZB.jcov_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hks : L.ksb s' = L.ksb s)
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hdead : ∀ q ∈ D, DeadP (L := L) H s' q)
    (hidl : Sched.IdleKeep (L := L) s s') (hDX : Sched.DXKeep (L := L) H Cs s s') :
    JCovD (L := L) Z.th H Z.G D Cs s' := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  refine J.jcov.same (fun y hy _ _ => ⟨hy, hSS.capV (hsl y hy)⟩) (fun q hq _ => hdead q hq)
    (J.jcov.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hSS.capV (hsl x hx)]; exact hc⟩) hidl hks
    (J.jcov.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hSS.capV (hsl x hx)]; exact hc⟩)
    (fun q _ h => h.keep hDX)

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

set_option maxHeartbeats 1000000 in
/-- **`JAtZ` across a CSpace-shaped step** (module docstring). -/
theorem JAtZB.cs_frameVD {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {G' : MdbGhost} {V' : Set U64 × Set U64 × Set U64 × Set U64 × Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR (Z.mv G' V') s' a' σ') (hkb : KBack σ σ') (hbf : JBuf (L := L) Z s' σ')
    (hC : JCs (L := L) (Z.mv G' V') s' σ') (R : JRest (L := L) arI (Z.mv G' V') H Cs Ac' Lst' D' s' σ')
    (hvc : Vs.VsSlotsW Z.th V'.1 V'.2.1 V'.2.2.1 V'.2.2.2.1 V'.2.2.2.2 (L.mem s'))
    (hlv : LiveDN (L := L) Z.th H Cs G' s' σ') (hzD : ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D')
    (hcy : JCarryS Z.B H σ') (hdv : IdleH (L := L) H s' → DevApart (L := L) Z.th H G' Cs s' ∧ DevSep G' (L.mem s'))
    (hvy : VsTyp (L := L) (Z.mv G' V') s' σ') (htb : DevTab G' (L.mem s') σ')
    (hvn : (Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s') (L.ksb s'))) :
    JAtZB (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ' :=
  have hsl : Sched.ScLinkHyp σ' := scLink_rebuild hX J.tcbs_eq.1 (J.obj.kback hkb) R.blk J.hset.2.1 R.jpl J.c0
  ⟨hX, R.call, R.rfree, R.rrecv, R.yld, R.mcp, R.buf, by rw [hks]; exact J.ks, J.thT, J.thk, J.ip, R.rp, R.apart,
    fun n hn => by rw [hks]; exact J.nk n hn,
    fun wp hw c hc => by simp only [P1.LawfulStore.nodeBase, hks]; exact J.nodeB wp hw c hc, R.jpl, J.cover.kback hkb, J.obj.kback hkb, J.zH, hC.sfree, J.hset, J.hscC, R.jcov,
    R.kern, hC.del, hC.ut, J.bound, hC.finM, R.utc, R.nsc, R.inv, R.cur, R.own, R.off, R.act, J.c0, R.bsa,
    schedValid_rebuild hX J.tcbs_eq.1 J.tcbs_eq.2 (J.obj.kback hkb) R.blk J.hset.1 J.hset.2.1 R.call R.yld J.c0 R.inv
      hsl, R.isorted, hsl, R.curRun, R.blk, by rw [hks]; exact J.intL, hvc, hbf.1, hbf.2.1, hbf.2.2, hlv, hzD,
      hcy.withP (hdv (idleH_of hX (J.obj.kback hkb) J.zH.1 R.jpl R.inv R.act)) hvy htb hvn⟩

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- `cs_frameVD` from the untyped caps' `DevFrom`/`UtFrom`. -/
theorem JAtZB.cs_frameV {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {G' : MdbGhost} {V' : Set U64 × Set U64 × Set U64 × Set U64 × Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR (Z.mv G' V') s' a' σ') (hkb : KBack σ σ') (hbf : JBuf (L := L) Z s' σ')
    (hC : JCs (L := L) (Z.mv G' V') s' σ') (R : JRest (L := L) arI (Z.mv G' V') H Cs Ac' Lst' D' s' σ')
    (hvc : Vs.VsSlotsW Z.th V'.1 V'.2.1 V'.2.2.1 V'.2.2.2.1 V'.2.2.2.2 (L.mem s'))
    (hlv : LiveDN (L := L) Z.th H Cs G' s' σ') (hzD : ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D')
    (hcy : JCarryS Z.B H σ') (hdu : DevFrom Z.G G' (L.mem s) (L.mem s') ∧ Sched.UtFrom Z.G G' (L.mem s) (L.mem s'))
    (hvy : VsTyp (L := L) (Z.mv G' V') s' σ') (hAF : ArchFwd σ σ') (hvn : (Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s') (L.ksb s'))) :
    JAtZB (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ' :=
  J.cs_frameVD (hvn := hvn) hks hX hkb hbf hC R hvc hlv hzD hcy (fun hI => J.carry.devStep hks hdu hI) hvy
    (J.carry.devTab.frame hdu.1.sub (tabBack_of hkb hAF))

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- `JAtZ.bok`/`fcov`/`fcap` across an `IpcFrKeep` step (`B` kept) whose
slots step by `VsSlotsT`. -/
theorem JAtZB.bfK {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} (hfk : IpcFrKeep σ σ')
    (hT : Vs.VsSlotsT Z.th (L.mem s) (L.mem s')) : JBuf (L := L) Z s' σ' :=
  ⟨J.bok.keep hfk, J.fcov.ipcFr hfk, J.fcap.keepU hT hfk.page⟩

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- `cs_frameV` at the same VSpace sets. -/
theorem JAtZB.cs_frame {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {G' : MdbGhost} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR { Z with G := G' } s' a' σ') (hkb : KBack σ σ') (hfk : IpcFrKeep σ σ') (hcy : JCarryS Z.B H σ')
    (hdu : DevFrom Z.G G' (L.mem s) (L.mem s') ∧ Sched.UtFrom Z.G G' (L.mem s) (L.mem s'))
    (hC : JCs (L := L) { Z with G := G' } s' σ') (R : JRest (L := L) arI { Z with G := G' } H Cs Ac' Lst' D' s' σ')
    (hvT : Vs.VsSlotsT Z.th (L.mem s) (L.mem s'))
    (hlv : LiveDN (L := L) Z.th H Cs G' s' σ') (hzD : ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D')
    (hvn : (Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s') (L.ksb s'))) :
    JAtZB (L := L) arI AR { Z with G := G' } H Cs Ac' Lst' D' s' a' σ' :=
  J.cs_frameV (V' := Z.vs) (hvn := hvn) hks hX hkb (J.bfK hfk hvT) hC R (J.vsc.step hvT) hlv hzD hcy hdu
    (J.carry.vsStep rfl hvT subset_rfl subset_rfl subset_rfl subset_rfl rfl hks (ArchFwd.of_ipcFr hfk)) (ArchFwd.of_ipcFr hfk)

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- **`LiveDN` across a step keeping the slots**, at `J` (`liveDN_frame`). -/
theorem JAtZB.liveX (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {Z' : XSets} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z' s' a' σ') (hth : Z'.th = Z.th) (hT : Z'.T = Z.T)
    (hc : Z'.c = Z.c) (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hidl : L.idleW s' = L.idleW s) (hdead : ∀ p ∈ ZTcb (L := L) Z.th s, Sched.DeadP (L := L) H s' p) :
    LiveDN (L := L) Z.th H Cs Z'.G s' σ' :=
  liveDN_frame J.xtop J.live ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩ J.kern.cs0
    (by obtain ⟨Tr, Cq, hJ⟩ := J.jpl
        exact Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩)
    hX hth hT hc hSS hK horig hidl hdead

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- **`JAtZ.zD` across a step keeping the slots**, the dead set grown. -/
theorem JAtZB.zDX (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {D' : Set U64}
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hDD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D') :
    ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D' := fun p hp => hDD p (ZTcb.of_same hSS hp)

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- **`cs_frame` for a step keeping every slot and the dead set** (KENTRY-PLAN
g2i): `JAtZ.live` by `liveX` (the original bits by `orig_eq_of_slots`, the idle
word from the spec's idle thread kept), `zD` by `zDX`; the step owes P1's
`DbgKeep`. -/
theorem JAtZB.cs_frameK {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR Z s' a' σ') (hkb : KBack σ σ') (hfk : IpcFrKeep σ σ') (hcy : JCarryS Z.B H σ')
    (hC : JCs (L := L) Z s' σ') (R : JRest (L := L) arI Z H Cs Ac' Lst' D s' σ')
    (hvT : Vs.VsSlotsT Z.th (L.mem s) (L.mem s'))
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s')
    (hid : σ'.idleThread = σ.idleThread) (hvn : (Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s') (L.ksb s'))) :
    JAtZB (L := L) arI AR Z H Cs Ac' Lst' D s' a' σ' :=
  J.cs_frame (G' := Z.G) (hvn := hvn) hks hX hkb hfk hcy
    (devFrom_same J.xtop.rel.2.1.2.2.1 hX.rel.2.1.2.2.1 hSS) hC R hvT
    (J.liveX hX rfl rfl rfl hSS hK
      (orig_eq_of_slots J.xtop.rel.2.1.2.2.2.1 hX.rel.2.1.2.2.2.1 J.kern.orig R.kern.orig hSS)
      (XTopAt.idleW_eqS J.xtop hX hid) fun p hp => R.jcov.dead p (J.zD p hp))
    (J.zDX hSS J.zD)

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- (F1 stage 5, item 4) **`vsNamed` across a step with `VsKeep` and `ArchShr`**, `XTopAt` after at
`Z`'s VSpace sets (`XTopAt.vsNamedShr`). -/
theorem JAtZB.vsShr (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {G' : MdbGhost} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR (Z.mv G' Z.vs) s' a' σ') (hks : L.ksb s' = L.ksb s)
    {th' : TypedHeap} (hK : Vs.VsKeep Z.th th' (L.mem s) (L.mem s')) (hsh : Vs.ArchShr σ σ') :
    Z.vx = ∅ → Vs.VsNamed th' (L.mem s') (L.ksb s') :=
  fun h => J.xtop.vsNamedShr hX (J.carry.vsNamed h) J.vsc hks hK hsh

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- `vsShr` with the slots kept. -/
theorem JAtZB.vsSS (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {G' : MdbGhost} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR (Z.mv G' Z.vs) s' a' σ') (hks : L.ksb s' = L.ksb s)
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hsh : Vs.ArchShr σ σ') :
    Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s') (L.ksb s') :=
  J.vsShr hX hks (Vs.VsKeep.of_eq fun y hy => hSS.capV hy) hsh

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- **The CSpace fields across a step keeping every slot and the objects'
sizes** (module docstring). -/
theorem JCs.sameB {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hk : KSz σ σ') : JCs (L := L) Z s' σ' := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  refine ⟨J.del.of_same hSS, UtInv.of_same hM J.ut hSS, fun G hG => ?_, ?_⟩
  · have hG0 : MdbLinks Z.th (L.mem s) G := hG.of_same_symm hSS
    have hsl' : ∀ x ∈ G.chains.flatten, IsSlot Z.th x := fun x h => ((hG0.members x).1 h).1
    exact (J.finM G hG0).of_capV fun x hx => hSS.capV (hsl' x hx)
  · refine SpecFree.frame J.sfree (fun x' hx' p sb fi' d hc => ⟨x', hx', fi', ?_, le_rfl⟩) hk
    rw [← hSS.capV (hsl x' hx')]; exact hc

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 16000000 in
/-- **A frame word that is not an IPC-buffer word, written at `J`** (module
docstring; the spec state kept). -/
theorem JAtZB.frameWrJ (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {w : U64}
    (hu : UserW (L := L) Z s σ w) (hnB : ∀ wp ∈ Z.B, wp.1 ≠ w)
    (hAp : ∀ q k, H q = some k → (∀ z, k ≠ .other z) → w.val + 8 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ w.val)
    (hObj : ∃ o ko, σ.kheap o = some ko ∧ o.toNat ≤ w.val ∧ w.val < o.toNat + 2 ^ Fl4Spec.objBits ko)
    (hks : w.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ w.val) (v : U64) :
    JAtZB (L := L) arI AR Z H Cs Ac Lst D (L.wr s w v) a σ := by
  set s1 := L.wr s w v with hs1
  have F : ArFr σ σ := ⟨fun _ => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hP := J.xtop.fin.1.2
  have hal : P1.Aligned w := hu.al
  have hW : P1.WritesIn st s s1 (· = w) := P1.writesIn_wr hal
  have hkb : L.ksb s1 = L.ksb s := hW.1
  have hcpu : L.cpu s1 = L.cpu s := hW.2.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) :=
    slotsSame_wr hP.pl s v hal fun x hx ⟨h1, h2⟩ =>
      hu.vobj (vobj_of_slot hP.pl Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) hx h1 h2)
  have hX1 : XTopAt (L := L) AR Z s1 a σ := J.xtop.userWr hu hnB v
  -- the frame words
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHk := J.kern.heap
  have objK : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → ∀ w' : U64, P1.Aligned w' → p.val ≤ w'.val →
      w'.val < p.val + 2 ^ k.bits → L.mem s1 w' = L.mem s w' := fun p k hp hk w' hal' g1 g2 =>
    hW.mem_eq hal' fun hb => by rw [hb] at g1 g2; rcases hAp p k hp hk with e | e <;> omega
  have tcbK : ∀ t ∈ Z.T, ∀ w' : U64, P1.Aligned w' → t.val ≤ w'.val → w'.val < t.val + 4096 →
      L.mem s1 w' = L.mem s w' := fun t ht w' hal' g1 g2 =>
    objK t .tcb (J.zH.1 t ht) (fun _ e => by cases e) w' hal' g1 (by simpa [P1.HKind.bits] using g2)
  have k1 : ∀ t ∈ Z.T, L.mem s1 (mcpA t) = L.mem s (mcpA t) ∧ L.mem s1 (flagsA t) = L.mem s (flagsA t) := fun t ht =>
    ⟨tcbK t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega),
      tcbK t ht _ (flagsA_aligned hT ht) (by rw [flagsA_val hT ht]; omega) (by rw [flagsA_val hT ht]; omega)⟩
  have k2 : ∀ t ∈ Z.T, L.mem s1 (P1.yieldA t) = L.mem s (P1.yieldA t) := fun t ht =>
    tcbK t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega)
  have kb : ∀ t ∈ Z.T, L.mem s1 (tIpcBufA t) = L.mem s (tIpcBufA t) := fun t ht =>
    tcbK t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega)
  have scw : ∀ q z, H q = some (.sc z) → ∀ w' : U64, P1.Aligned w' → q.val ≤ w'.val → w'.val < q.val + 2 ^ z →
      L.mem s1 w' = L.mem s w' := fun q z hq w' hal' g1 g2 =>
    objK q _ hq (fun _ e => by cases e) w' hal' g1 (by simpa only [P1.HKind.bits] using g2)
  have k3 : ∀ q ∈ Z.C, L.mem s1 (P1.scReplyA q) = L.mem s (P1.scReplyA q) := fun q hq => by
    obtain ⟨xq, nq, hkq, hin⟩ := screply_obj J.xtop.fin.1.1.1 hq
    have hHq := (hJ.sc q xq nq (J.c0 q hq) hkq).2
    exact scw q _ hHq _ (sc_reply_word J.xtop.fin.1.1.1 hq).1 hin.1 hin.2
  have k4 : ∀ r ∈ Z.R, L.mem s1 (P1.rPrevA r) = L.mem s (P1.rPrevA r) ∧
      L.mem s1 (P1.rNextA r) = L.mem s (P1.rNextA r) := by
    intro r hr
    have hal' := J.rp.align r hr
    have hHr : H r = some .reply := J.zH.2.2.1 r hr
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s1 a' = L.mem s a' := fun a' ha =>
      objK r _ hHr (fun _ e => by cases e) a' (J.rp.aligned hr ha) (by omega)
        (by simp only [P1.HKind.bits]; omega)
    exact ⟨k _ (Or.inl (rPrevA_val hal')), k _ (Or.inr (rNextA_val hal'))⟩
  have hOut : ∀ q z, H q = some (.sc z) → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s1 (scW q K) = L.mem s (scW q K) := by
    intro q z hq K hK8 hK
    have hal' := hHk.align q _ hq
    have hfit := hHk.fits q _ hq
    have hz := hHk.scmin q z hq
    simp only [P1.HKind.bits] at hal' hfit
    have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
    have hq8 : q.val % 8 = 0 := by
      have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
      rw [← Nat.mod_mod_of_dvd q.val hd, hal']
    have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
    exact scw q z hq _ (by show (scW q K).val % 8 = 0; rw [hv]; omega) (by omega) (by omega)
  -- the debug word and the IRQ node: in the kernel-global data, which the word misses
  have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ J.kern.cs0
  have hnb0 : L.nodeBase s 0#u64 = (L.ksb s).val + 13568 := by
    show (L.ksb s).val + 13568 + (0#u64 : U64).val * 4288 = _; simp
  have hDbg : L.mem s1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hdv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
    have hdo : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
    exact hW.mem_eq J.kern.dwAl fun hb => by
      rw [hb, hnb0] at hdv; omega
  have hirq : ∀ i : U64, i.val < 128 → capV (L.mem s1) (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hW J.kern.ksbFit J.kern.ksbAl fun b hb => by
      rw [hb]; omega
  -- the dead stay dead
  have hAI : ActIdle σ := J.act.ar F
  have yk : YKeep σ σ := ⟨fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩,
    fun p x n hp => ⟨x, F.sc.2 hp, rfl⟩, fun p y n hp => ⟨y, F.sc.1 hp, rfl⟩⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s1 q := fun q hq =>
    J.deadP_keep hX1.fin.1.1.1 hX1.ipc
      (fun x hx _ => ⟨x, (F.look (fun _ e => by cases e)).2 hx, rfl, rfl, Or.inl rfl⟩)
      (fun x hx => (F.look (fun _ e => by cases e)).2 hx)
      (fun x hx => ⟨x, F.ntfn.2 hx, Or.inl rfl, rfl, Or.inl rfl⟩)
      (fun x hx => ⟨x, (F.look (fun _ e => by cases e)).2 hx, rfl⟩)
      (fun x n hx => ⟨x, F.sc.2 hx, Or.inl rfl, Or.inl rfl⟩) (k3 q) (fun z hz _ => hOut q z hz) F.idle hAI.1
      (J.yld.frame k2 yk) (yk.dk q.bv) (J.jcov.dead q hq)
  -- P1's `BlkOK`
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s1 := by
    refine (P1.blk_of_untracked J.blk hW fun b hb => ⟨⟨by rw [hb]; exact hal, fun t ht => ?_, fun c hc => ?_⟩,
      fun e he => ?_, fun hf => ?_⟩).1
    · subst hb
      rcases hAp t .tcb ht (fun _ e => by cases e) with e | e
      · left; omega
      · right; simpa [P1.HKind.bits] using e
    · subst hb
      have hcl := J.kern.csLt c hc
      have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
      omega
    · subst hb
      rcases he with he | he
      · rcases hAp e _ he (fun _ e => by cases e) with e | e
        · left; omega
        · right; simp only [P1.HKind.bits] at e; omega
      · rcases hAp e _ he (fun _ e => by cases e) with e | e
        · left; omega
        · right; simp only [P1.HKind.bits] at e; omega
    · subst hb
      obtain ⟨-, p, k, hp, hk, hin⟩ := hf
      have hko : ∀ z, k ≠ .other z := by
        rcases hk with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩ <;> intro z e <;> cases e
      obtain ⟨g1, g2⟩ := hin
      rcases hAp p k hp hko with e | e <;> omega
  -- the untyped caps' facts
  have hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s1) (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s1 σ Z.G sl p sb fi := by
    intro sl p sb fi dev hsl hcap hdv
    have hna : ∀ c o, L.nodeAt s1 c o = L.nodeAt s c o := P1.nodeAt_of_ksb hkb
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
      rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
    have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
    have U := J.utc sl p sb fi dev hsl hcap0 hdv
    have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
      (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
    have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
    refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_,
      U.sb4, U.nostr, U.nsFree,
      fun h0 => U.ns (by rw [F.cdt] at h0; exact h0),
      ?_, fun g => by rw [hna]; exact U.dwReg (B g),
      fun g => by rw [F.gpml4]; exact U.gReg (B g)⟩
    · intro g w' hal' h1 h2
      rw [hW.mem_eq hal' fun hb => ?_]
      · exact U.zero (B g) w' hal' h1 h2
      rw [hb] at h1 h2
      obtain ⟨o, ko, hko, g1, g2⟩ := hObj
      have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) o ko hko
      omega
    · intro g h0 hf0
      rw [F.cdt] at h0
      obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
      exact ⟨fun sl' h => r1 sl' (by rw [← F.orig]; exact h), by rw [hna, hDbg]; exact r3⟩
  -- the spec's frames
  have ck : Sched.CKeep σ σ := ⟨fun q y n hq => ⟨y, F.sc.2 hq, rfl⟩,
    fun q x hq => ⟨x, (F.look (fun _ e => by cases e)).2 hq, rfl, rfl⟩, fun p x n hp => ⟨x, F.sc.1 hp⟩⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hkb ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s1 σ :=
    ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => F.szKeep q.bv y n hq) hkb hirq (J.idleW_keep hX1.fin.1.1.1 F.idle F.isc).2⟩
  have hkern := J.kern_keepA hkb hcpu hX1.fin.1.1.1 F hDbg
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s1 := dbgKeep_of_writes J.blk hW fun b hb => by
    subst hb
    refine J.notDbg (fun t ht => ?_) (fun c hc => ?_)
    · rcases hAp t .tcb ht (fun _ e => by cases e) with e | e
      · left; omega
      · right; simpa [P1.HKind.bits] using e
    · have hcl := J.kern.csLt c hc
      have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
      omega
  have hTd : Sched.TdKeep (L := L) H s s1 := fun q hq =>
    tcbK q (J.tcbZ hq) _ (P1.field_aligned (J.ip.e.tcb q (J.tcbZ hq)) (K := 3528#u64) (by simp) (by simp))
      (by rw [J.tdA_val' (J.tcbZ hq)]; omega) (by rw [J.tdA_val' (J.tcbZ hq)]; omega)
  have R : JRest (L := L) arI { Z with G := Z.G } H Cs Ac Lst D s1 σ :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 yk, J.mcp.frame k1 (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩),
      J.buf.frame kb (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩), hRP',
      J.apart.sc_frame hkb F.szKeep, hjpl, J.jcov_keep hkb hSS hdead (J.idleW_keep hX1.fin.1.1.1 F.idle F.isc) (DXKeep.of_dbg hKd hTd), hkern,
      hutc, J.nsc.ar F, J.inv.ar F, CurInvW.ar J.cur F, J.own.ar F,
      J.off.ar F, hAI, J.bsa.ar F, J.isorted.ar F, J.curRun.ar F, hblk⟩
  exact J.cs_frameK (hvn := J.vsSS (G' := Z.G) hX1 hkb hSS (Vs.ArchShr.refl _)) hkb hX1 F.kback F.ipcFr (J.carry.frame subset_rfl F.ipcFr F.ksz) (JCs.sameB J hSS F.ksz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy)
    hSS hKd F.idle

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 8000000 in
/-- **A word of a VCPU written at `J`** (module docstring; the spec state kept). -/
theorem JAtZB.vcpuWrJ (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {p w : U64}
    (hσ : ∃ x, σ.kheap p.bv = some (.archObj (.vcpu x))) (hH : H p = some (.other 15))
    (hks : p.val + 32768 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ p.val)
    (hal : P1.Aligned w) (g1 : p.val ≤ w.val) (g2 : w.val < p.val + 32768)
    (hnB : ∀ wp ∈ Z.B, wp.1 ≠ w) (v : U64) :
    JAtZB (L := L) arI AR Z H Cs Ac Lst D (L.wr s w v) a σ := by
  obtain ⟨x, hσx⟩ := hσ
  have hHO := J.kern.heap
  have h15 : (2 : Nat) ^ 15 = 32768 := by norm_num
  have hw8 : w.val % 8 = 0 := hal
  have hpa : p.val % 32768 = 0 := by
    have := hHO.align p _ hH; simpa [P1.HKind.bits, h15] using this
  -- apart from every other `H` object
  have wap : ∀ q k', H q = some k' → q ≠ p → w.val + 8 ≤ q.val ∨ q.val + 2 ^ k'.bits ≤ w.val := by
    intro q k' hq hne
    rcases hHO.disj p _ q k' hH hq (Ne.symm hne) with h | h
    · simp only [P1.HKind.bits, h15] at h; left; omega
    · right; omega
  have hneK : ∀ q k', H q = some k' → (∀ z, k' ≠ .other z) → q ≠ p := fun q k' hq hk' e => by
    subst e; rw [hH] at hq; exact hk' 15 (Option.some.inj hq).symm
  have hAp : ∀ q k, H q = some k → (∀ z, k ≠ .other z) → w.val + 8 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ w.val :=
    fun q k hq hk => wap q k hq (hneK q k hq hk)
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hR := J.xtop.rel.2.1.1
  -- the typed heap's CNodes are spec CNodes, so not the VCPU
  have hcn : ∀ q r, Z.th q = some (.cnode r) → w.val + 8 ≤ q.val ∨ q.val + 32 * 2 ^ r ≤ w.val := by
    intro q r hq
    have hne : q ≠ p := fun e => by
      subst e; obtain ⟨cs, hc, -⟩ := hR.cnode q r hq; rw [hc] at hσx; cases hσx
    have e32 : 2 ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; norm_num; ring
    have := wap q _ (hJ.cnode q r hq) hne
    simp only [P1.HKind.bits] at this; rw [e32] at this; exact this
  have htc : ∀ t, Z.th t = some .tcb → w.val + 8 ≤ t.val ∨ t.val + 4096 ≤ w.val := by
    intro t ht
    have hHt := (hJ.tcb t).1 ht
    have := hAp t _ hHt fun _ e => by cases e
    simpa [P1.HKind.bits] using this
  -- the sets' tables and pools are spec tables / pools, so not the VCPU
  have hF := J.xtop.fin
  have hvs : ∀ q', (q' ∈ Z.P ∨ q' ∈ Z.L4 ∨ q' ∈ Z.L3 ∨ q' ∈ Z.L2 ∨ q' ∈ Z.L1) →
      w.val + 8 ≤ q'.val ∨ q'.val + 4096 ≤ w.val := by
    intro q' hq'
    obtain ⟨n', hn', hH'⟩ := J.vsFr_other hq'
    have hne : q' ≠ p := by
      intro e; subst e
      rcases hq' with hv | hv | hv | hv | hv
      · obtain ⟨f, hf, -⟩ := hF.2.1.pool q' hv; rw [hf] at hσx; cases hσx
      · obtain ⟨f, hf, -⟩ := hF.2.2.1.l4 q' hv; rw [hf] at hσx; cases hσx
      · obtain ⟨f, hf, -⟩ := hF.2.2.1.l3 q' hv; rw [hf] at hσx; cases hσx
      · obtain ⟨f, hf, -⟩ := hF.2.2.1.l2 q' hv; rw [hf] at hσx; cases hσx
      · obtain ⟨f, hf, -⟩ := hF.2.2.1.l1 q' hv; rw [hf] at hσx; cases hσx
    have h4 : 2 ^ 12 ≤ 2 ^ n' := Nat.pow_le_pow_right (by decide) hn'
    rcases wap q' _ hH' hne with h | h
    · exact Or.inl h
    · simp only [P1.HKind.bits] at h; right; omega
  -- core `Z.c`'s node lies below the ASID-table area
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hcq.cur ▸ J.kern.cpuCs
  have hc64 := J.kern.csLt Z.c hcC
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  have hksw : w.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ w.val := by omega
  have hu : UserW (L := L) Z s σ w :=
    { al := hal
      far := ⟨by rw [hnb]; omega,
        fun t ht => by
          have := hAp t _ (J.zH.1 t ht) fun _ e => by cases e
          simpa [P1.HKind.bits] using this,
        fun sc hsc y n hky => by
          have hHs := (hJ.sc sc y n (J.c0 sc hsc) hky).2
          have := hAp sc _ hHs fun _ e => by cases e
          simpa [P1.HKind.bits] using this⟩
      vobj := fun hv => by
        rcases hv with ⟨q, r, hq, c1, c2⟩ | ⟨t, ht, c1, c2⟩ | ⟨q', hq', c1, c2⟩ | h
        · have := hcn q r hq; omega
        · have := htc t ht; omega
        · have := hvs q' hq'; omega
        · omega
      ep := fun e he => by
        have := hAp e _ (J.zH.2.1 e he) fun _ e => by cases e
        simpa [P1.HKind.bits] using this
      rep := fun r hr => by
        have := hAp r _ (J.zH.2.2.1 r hr) fun _ e => by cases e
        simpa [P1.HKind.bits] using this
      ntfn := fun n hn => by
        have := hAp n _ (J.zH.2.2.2 n hn) fun _ e => by cases e
        simpa [P1.HKind.bits] using this }
  have hObj : ∃ o ko, σ.kheap o = some ko ∧ o.toNat ≤ w.val ∧ w.val < o.toNat + 2 ^ Fl4Spec.objBits ko :=
    ⟨p.bv, _, hσx, g1, by
      show w.val < p.val + 2 ^ Fl4Spec.archKobjSize (.vcpu x)
      simp only [Fl4Spec.archKobjSize, h15]; exact g2⟩
  exact J.frameWrJ hu hnB hAp hObj hksw v

end

section
open fl4_core Classical

set_option maxHeartbeats 4000000 in
/-- **A VCPU word written at `JAtZV V X`** (module docstring; σ unchanged). -/
theorem JAtZV.vcpuWr (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p w : U64} (hp : p ∈ V)
    (hal : P1.Aligned w) (g1 : p.val ≤ w.val) (g2 : w.val < p.val + 32768)
    (hw : w.val ≠ p.val + 20480 ∧ w.val ≠ p.val + 20488 ∧ w.val ≠ p.val + 20496) (x : U64) :
    JAtZV (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s w x) a σ := by
  have B := J.base
  have Ly := B.jvLay J.vm
  have hW : P1.WritesIn st s (L.wr s w x) (· = w) := P1.writesIn_wr hal
  have hf := Ly.vfit p hp
  -- no IPC-buffer word lies in the VCPU
  have hnB : ∀ wp ∈ Z.B, wp.1 ≠ w := by
    intro wp hwp e
    obtain ⟨q, vms, hq, q1, q2⟩ := B.carry.bufPg wp hwp
    obtain ⟨y, hy⟩ := J.vm.spec p hp
    have hne : q ≠ p.bv := fun e' => by rw [e', hy] at hq; cases hq
    have eb : Fl4Spec.objBits (.archObj (.dataPage false vms)) = Fl4Spec.pageBitsForSize vms := by
      simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]
    have ev : wp.1.val = w.val := by rw [e]
    rcases J.vm.sep p hp q _ hq hne with e1 | e1
    · rw [eb] at e1; omega
    · omega
  have B' := B.vcpuWrJ (J.vm.spec p hp) (J.vm.heap p hp) (J.vm.ks p hp) hal g1 g2 hnB x
  -- the extension
  have E' : JExtV (L := L) V X Z.th (L.wr s w x) :=
    J.extv.of_writes (B.jwPl J.vm) hW fun b hb => by subst hb; exact (Ly.nJS_v hp g1 g2 hw.1).1
  have hHO := B.kern.heap
  have apT : ∀ t, Z.th t = some .tcb → t.val + 4096 ≤ p.val ∨ p.val + 32768 ≤ t.val := by
    intro t ht
    have htH : H t = some .tcb := B.zH.1 t (B.thT t ht)
    have hne : t ≠ p := fun e => by rw [e, J.vm.heap p hp] at htH; cases htH
    have d := hHO.disj t _ p _ htH (J.vm.heap p hp) hne
    simp only [P1.HKind.bits, Nat.reducePow] at d
    exact d
  have kT : ∀ t, Z.th t = some .tcb → L.mem (L.wr s w x) (P1.stA t) = L.mem s (P1.stA t) ∧
      L.mem (L.wr s w x) (tVcpuA t) = L.mem s (tVcpuA t) := by
    intro t ht
    have hta := B.ip.e.tcb t (B.thT t ht)
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
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val B.kern.ksbFit
  have Vl' : VList st V Z.th (L.wr s w x) := J.vl.writes hW fun b hb => by
    refine ⟨J.vl.lw_al Ly.vfit hb, fun e => ?_⟩
    have ew := congrArg UScalar.val e
    rcases hb with rfl | ⟨u, hu, rfl | rfl⟩
    · rcases J.vm.ks p hp with h | h <;> omega
    · rw [lay_next_val (Ly.vfit u hu).2] at ew
      by_cases hup : u = p
      · subst hup; exact hw.2.1 ew.symm
      · rcases Ly.vv u hu p hp hup with h | h <;> omega
    · rw [lay_prev_val (Ly.vfit u hu).2] at ew
      by_cases hup : u = p
      · subst hup; exact hw.2.2 ew.symm
      · rcases Ly.vv u hu p hp hup with h | h <;> omega
  have Jv' : JVm (L := L) V H (L.wr s w x) σ :=
    ⟨J.vm.spec, J.vm.heap, fun v hv => by rw [hW.1]; exact J.vm.ks v hv, J.vm.sep⟩
  exact ⟨B', E', R', Jv', Vl'⟩

end

end

end

end Fl4Proofs.P3
