/-
P3 (DESIGN.md §9), CSpace: **the per-kind `JRest` discharge of `JAtZ`'s step
closure** (`JStepHyps`, XTopJointStep), in the SC family's pattern
(`ScStepRest`, ScJointRest).

* The restart (`jowes_restart`): FL4 writes the caller's state word
  (`SFoot`), the spec only the caller's TCB (`ScTKw`, `tk_setThreadState`).
  Discharged: the call stacks, yield, MCP and reply placement (`ScAll.of_k`),
  the buffer words, slots apart, `JPlaced`, the kernel words, the untyped
  caps' facts, the dead set (ScJointRest's `sc_*` frames), `NSC`, `Inv`
  (`Inv.restart`), the current thread's invariants (`CurInv.restart`,
  `CurOwn`), `OffOK` (`OffOK.restart`), `ActIdle` (`ActIdle.updState`),
  `BlockedScActive` (`bk_restart`), the sorted IPC queues (`IpcSorted.tkw`), `CurRun`.
  Named (`RestartRest` [W], as `ScStepRest`'s): the dead set after, the
  node-0 `DEBUG_TCBS` word kept, P1's `BlkOK` after.
-/
import Fl4Proofs.P3.XTopJointStep
import Fl4Proofs.P3.ScJointRest
import Fl4Proofs.P3.ScJointStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

theorem nsc_updTcb {N C : Set U64} {σ : State Unit} (h : NSC N C σ) (p : ObjRef) (y : Tcb) :
    NSC N C (stsAct (updK σ p (.tcb y)) p) := by
  intro n hn x q hx hq
  rw [stsAct_kheap, updK_kheap] at hx
  by_cases e : n.bv = p
  · rw [e, Function.update_self] at hx; cases hx
  · rw [Function.update_of_ne e] at hx; exact h n hn x q hx hq

theorem scLink_updTcb {σ : State Unit} (h : ScLinkHyp σ) {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x))
    (ts : ThreadState) : ScLinkHyp (stsAct (updK σ p (.tcb { x with tcbState := ts })) p) := by
  have ek : ∀ q, (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).kheap q =
      Function.update σ.kheap p (some (.tcb { x with tcbState := ts })) q := fun q => by
    rw [stsAct_kheap, updK_kheap]
  have back : ∀ q o, (o.isSome → ∀ y, o ≠ some (.tcb y)) → (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).kheap q = o →
      σ.kheap q = o := by
    intro q o ho h1
    rw [ek] at h1
    by_cases e : q = p
    · subst e; rw [Function.update_self] at h1; subst h1; exact absurd rfl (ho rfl _)
    · rwa [Function.update_of_ne e] at h1
  refine ⟨fun sc y k f hy hf => ?_, fun sc y k n hy hn => ?_, fun t z n ht hn => ?_, fun sc y k hy hs => ?_⟩
  · obtain ⟨z, hz⟩ := h.scTcb sc y k f (back _ _ (fun _ _ e => by cases e) hy) hf
    rw [ek]
    by_cases e : f = p
    · subst e; exact ⟨_, Function.update_self ..⟩
    · rw [Function.update_of_ne e]; exact ⟨z, hz⟩
  · obtain ⟨xn, hxn⟩ := h.scNtfn sc y k n (back _ _ (fun _ _ e => by cases e) hy) hn
    refine ⟨xn, ?_⟩
    rw [ek]
    by_cases e : n = p
    · subst e; rw [hk] at hxn; cases hxn
    · rw [Function.update_of_ne e]; exact hxn
  · rw [ek] at ht
    have hz : ∃ z0, σ.kheap t = some (.tcb z0) ∧ z0.tcbBoundNotification = z.tcbBoundNotification := by
      by_cases e : t = p
      · subst e; rw [Function.update_self] at ht; cases ht; exact ⟨x, hk, rfl⟩
      · rw [Function.update_of_ne e] at ht; exact ⟨z, ht, rfl⟩
    obtain ⟨z0, hz0, ez⟩ := hz
    obtain ⟨xn, hxn⟩ := h.tcbNtfn t z0 n hz0 (ez ▸ hn)
    refine ⟨xn, ?_⟩
    rw [ek]
    by_cases e : n = p
    · subst e; rw [hk] at hxn; cases hxn
    · rw [Function.update_of_ne e]; exact hxn
  · exact h.scSpor sc y k (back _ _ (fun _ _ e => by cases e) hy) hs

theorem curOwn_updTcb {T : Set U64} {σ : State Unit} (h : CurOwn T σ) {p : ObjRef} {x : Tcb}
    (hk : σ.kheap p = some (.tcb x)) (ts : ThreadState) :
    CurOwn T (stsAct (updK σ p (.tcb { x with tcbState := ts })) p) := by
  obtain ⟨e1, e2, e3, e4⟩ := stsAct_fields (updK σ p (.tcb { x with tcbState := ts })) p
  have ek : (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).kheap =
      Function.update σ.kheap p (some (.tcb { x with tcbState := ts })) := by rw [e1]; rfl
  have ecs : (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).curSc = σ.curSc := by rw [e3]; rfl
  have erq : (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).releaseQueue = σ.releaseQueue := by rw [e4]; rfl
  have hc : (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).consumedTime = σ.consumedTime := by
    unfold stsAct; split_ifs <;> rfl
  obtain ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ := h
  refine ⟨u, hu, ?_⟩
  by_cases e : u.bv = p
  · rw [e, hk] at hkt; cases hkt
    refine ⟨{ x with tcbState := ts }, by rw [ek, e, Function.update_self], by rw [ecs]; exact hxs, fun y n hy => ?_,
      by rw [hc, erq]; exact hnr⟩
    rw [ek, ecs] at hy
    by_cases e' : σ.curSc = p
    · rw [e', Function.update_self] at hy; cases hy
    · rw [Function.update_of_ne e'] at hy; exact hown y n hy
  · refine ⟨xt, by rw [ek, Function.update_of_ne e]; exact hkt, by rw [ecs]; exact hxs, fun y n hy => ?_,
      by rw [hc, erq]; exact hnr⟩
    rw [ek, ecs] at hy
    by_cases e' : σ.curSc = p
    · rw [e', Function.update_self] at hy; cases hy
    · rw [Function.update_of_ne e'] at hy; exact hown y n hy

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **What the restart still owes** [W] (`ScStepRest`'s P1-supplied and
dead-set parts): the dead set after, the node-0 `DEBUG_TCBS` word kept, P1's
`BlkOK` after. -/
def RestartRest (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s s1 : S) : Prop :=
  ∃ (Ac' D' : Set U64), (D' ⊆ D ∧ (∀ q ∈ D', DeadP (L := L) H s1 q) ∧
      ∀ q ∈ D, q ∉ D' →
        (∀ k, Z.th q = some k → Covered (L.mem s1) Z.G q.val (q.val + max (objSize k) 1)) ∧
        (∀ k, H q = some k → Covered (L.mem s1) Z.G q.val (q.val + 2 ^ k.bits))) ∧
    L.mem s1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ∧
    P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s1

set_option maxHeartbeats 8000000 in
/-- **`JStepHyps.restart` from `RestartRest`** (module docstring). -/
theorem jowes_restart {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (ct : U64) (x : Fl4Spec.Tcb) (s1 : S) (hcur : σ.curThread = ct.bv) (hk : σ.kheap ct.bv = some (.tcb x))
    (htcb : th ct = some .tcb) (hrun : Fl4Spec.runnable x.tcbState = true)
    (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1)
    (hR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → RestartRest (L := L) Z H Cs D s s1) :
    JOwes (L := L) arI AR th s a σ s1 a
      (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) := by
  intro Z H Cs Ac Lst D hth J hX1
  set σ1 := Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv with hσ1
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hT : ct ∈ Z.T := J.thT ct (hth ▸ htcb)
  have he1 : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := setThreadState_eq' hk _
  have hm1 : ((), σ1) ∈ (Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ).1 := by
    rw [he1]; exact Set.mem_singleton _
  have hK : ScTKw (fun p => p = ct.bv) σ σ1 :=
    tk_setThreadState hk (ipcFree_of_runnable hrun) ipcFree_restart _ hm1
  have hwS : P1.WritesIn st s s1 (SFoot st Z.T Z.c s) := by
    have h := set_thread_state_sfoot (L := L) hS hT sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h; exact h
  have hwK : P1.WritesIn st s s1 (KFoot st Z.T Z.N Z.C Z.c s σ) := hwS.mono fun b hb => KFoot.of_sfoot hb
  have hwT : P1.WritesIn st s s1 (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_of_kfoot hwK
  have hS1 := hX1.fin.1.1.1
  have hN1 := hX1.fin.1.1.2.2.1
  have hNsc : NSC Z.N Z.C σ1 := nsc_updTcb J.nsc _ _
  have hI1 : Inv σ1 := Inv.restart J.inv hk hrun
  have hSOK : SOK (true, true) σ σ1 := pres_setThreadState (f := (true, true)) _ _ σ _ hm1
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS1, hN1, hNsc, hI1⟩, hwK, hSOK⟩
  have hF : FK σ σ1 := (fk_setThreadState _ _).of_eq he1
  obtain ⟨Ac', D', ⟨hDD, hDead, hCov⟩, hDbg, hBlk'⟩ := hR Z H Cs Ac Lst D hth J
  have hkc : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  have hcur' : σ1.schedulerAction = .chooseNewThread ∨ CurInv σ1 := by
    rcases J.cur with h | h
    · left
      show (Notif.stsAct _ ct.bv).schedulerAction = _
      unfold Notif.stsAct; split_ifs with hc
      · rfl
      · exact h
    · right
      have := CurInv.restart h hkc
      rw [hcur] at this; exact this
  have hB' : BlockedScActive σ1 := J.bsa.bk (bk_restart hk hrun hm1) hSOK
  have hCR'' : CurRun σ1 := by
    intro y hy
    rw [show σ1.curThread = σ.curThread from (stsAct_fields _ _).2.1, hcur, stsAct_kheap, updK_kheap,
      Function.update_self] at hy
    cases hy; rfl
  refine ⟨Ac', Lst', D', ⟨hCR', hRF', hY', hM', J.sc_buf hwT hK, hRP', J.sc_apart hwT hK, J.sc_jpl hwT hK,
    J.sc_jcov hwT hDead hCov, J.sc_kern hwT hK hF hX1 hDbg hDD, J.sc_utc hwT hK hDbg, hNsc, hI1, hcur',
    curOwn_updTcb J.own hk _, OffOK.restart J.off _, (ActIdle.updState J.act hk hrun .restart rfl).ofSts ct.bv, hB',
    J.isorted.tkw hK, hCR'', hBlk'⟩⟩

end

end

end Fl4Proofs.P3
