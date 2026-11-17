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
  The dead stay dead (`JAtZ.deadP_sc_step`: `ScTKw`, `LK ∅` by
  `lkm_setThreadState`). Named (`RestartRest` [W], as `ScStepRest`'s): the
  node-0 `DEBUG_TCBS` word kept, P1's `BlkOK` after.
-/
import Fl4Proofs.P3.XTopJointStep
import Fl4Proofs.P3.ScJointRest
import Fl4Proofs.P3.ScJointStep
import Fl4Proofs.P3.SpecKeepC
import Fl4Proofs.P3.ScDeadStep
import Fl4Proofs.P3.DeadKeep
import Fl4Proofs.P3.SlotOrig
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

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

/-- `curOwn_updTcb` for the weak form (`CurOwnW`: an unowned current SC
stays unowned, a TCB written over no SC). -/
theorem curOwnW_updTcb {T C : Set U64} {σ : State Unit} (h : CurOwnW T C σ) {p : ObjRef} {x : Tcb}
    (hk : σ.kheap p = some (.tcb x)) (ts : ThreadState) :
    CurOwnW T C (stsAct (updK σ p (.tcb { x with tcbState := ts })) p) := by
  obtain ⟨e1, -, e3, -⟩ := stsAct_fields (updK σ p (.tcb { x with tcbState := ts })) p
  have ek : (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).kheap =
      Function.update σ.kheap p (some (.tcb { x with tcbState := ts })) := by rw [e1]; rfl
  have ecs : (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).curSc = σ.curSc := by rw [e3]; rfl
  refine h.imp (fun o => curOwn_updTcb o hk ts) ecs fun y n hy => Or.inr ⟨y, ?_, rfl⟩
  rw [ek] at hy
  by_cases e' : σ.curSc = p
  · rw [e', Function.update_self] at hy; cases hy
  · rw [Function.update_of_ne e'] at hy; exact hy

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **What the restart still owes** [W] (`ScStepRest`'s P1-supplied parts):
the node-0 `DEBUG_TCBS` word kept, P1's `BlkOK` after. -/
def RestartRest (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s s1 : S) : Prop :=
  ∃ (Ac' : Set U64),
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
  obtain ⟨Ac', hDbg, hBlk'⟩ := hR Z H Cs Ac Lst D hth J
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
  have hAI : ActIdle σ1 := (ActIdle.updState J.act hk hrun .restart rfl).ofSts ct.bv
  have hL : LK (fun _ => False) σ σ1 := (lkm_setThreadState (W := fun _ => False) _ _).of_eq he1
  have hDead : ∀ q ∈ D, DeadP (L := L) H s1 q := fun q hq =>
    J.deadP_sc_step hX1 hwT hK (fun p y e hy => by subst e; rw [hk] at hy; cases hy; exact hrun) hL hF hAI.1
      (fun h => h) (J.jcov.dead q hq)
  refine ⟨Ac', Lst', D, ⟨hCR', hRF', hY', hM', J.sc_buf hwT hK, hRP', J.sc_apart hwT hK, J.sc_jpl hwT hK,
    J.sc_jcov hwT hDead (fun q hq hn => absurd hq hn), J.sc_kern hwT hK hF hX1 hDbg (fun _ h => h),
    J.sc_utc hwT hK hDbg, hNsc, hI1, hcur', curOwnW_updTcb J.own hk _, OffOK.restart J.off _, hAI, hB',
    J.isorted.tkw hK, Or.inl hCR'', hBlk'⟩⟩

/-! ## The slot steps (an insertion, a CNode-only step) -/

/-- **A word outside every slot is kept by writes of slot words** (the slot
steps' write set, `InSlot`). -/
theorem inSlot_keep {th : TypedHeap} {s s' : S} (hw : P1.WritesIn st s s' (InSlot th)) {b : U64} (hb : P1.Aligned b)
    (hout : ∀ a, IsSlot th a → b.val < a.val ∨ a.val + 32 ≤ b.val) : L.mem s' b = L.mem s b :=
  hw.mem_eq hb fun ⟨a, ha, h1, h2⟩ => by rcases hout a ha with h | h <;> omega

/-- **The scheduler's words a slot step keeps** (from `SlotsApart`): the TCBs'
`MCP`, `YIELD_TO` and IPC-buffer words, the SCs' `REPLY` words, the replies'
links. -/
theorem inSlot_keeps {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (InSlot Z.th)) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hT := hc.tcbs
  have hA := J.apart
  have tw : ∀ t ∈ Z.T, ∀ b : U64, P1.Aligned b → t.val + 256 ≤ b.val → b.val < t.val + 4096 → L.mem s' b = L.mem s b :=
    fun t ht b hb h1 h2 => inSlot_keep hw hb fun x hx => by rcases (hA x hx).1 t ht with h | h <;> omega
  refine ⟨fun t ht => tw t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega),
    fun t ht => tw t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega),
    fun t ht => tw t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega), fun q hq => ?_, fun r hr => ?_⟩
  · obtain ⟨hal, hv, hfit⟩ := sc_reply_word hS hq
    obtain ⟨x, n, hk, -⟩ := (hS.lists.choose_spec.choose_spec.2).scs q hq
    have hf := hfit x n hk
    exact inSlot_keep hw hal fun y hy => by
      rcases (hA y hy).2.2.2.1 q hq x n hk with h | h <;> omega
  · have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    refine ⟨inSlot_keep hw (J.rp.aligned hr (Or.inl h8)) fun y hy => ?_,
      inSlot_keep hw (J.rp.aligned hr (Or.inr h16)) fun y hy => ?_⟩
    · rcases (hA y hy).2.2.2.2 r hr with h | h <;> omega
    · rcases (hA y hy).2.2.2.2 r hr with h | h <;> omega

/-- **What a slot step still owes** [W] (each reads the caps changed): the
joint placement, the covering caps
surviving and no new untyped region (`CoverKept`, `UtKept`: `jcov_cover`),
the new original bits at `AbsSlot`s (`kern_keep`), the untyped caps' facts
and P1's `BlkOK`. -/
def SlotRest (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s s' : S) (σ σ' : Fl4Spec.State Unit) : Prop :=
  ∃ (Ac' : Set U64), (∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ') ∧
    CoverKept Z.th (L.mem s) (L.mem s') ∧ UtKept Z.th (L.mem s) (L.mem s') ∧
    (∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot Z.th sl) ∧
    (∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) →
      UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi) ∧
    P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s'

set_option maxHeartbeats 4000000 in
/-- **A slot step's `JOwesCs` from `SlotRest`**: FL4 writes slot words only
(`inSlot_keeps`), the spec changes CNodes only (`CnStep`, SpecKeepC); the
CSpace fields by `jcs_slot` (`DelInv` kept by the step, the objects' kinds kept, `KSz`). -/
theorem jowes_slotOf {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {G' : MdbGhost} (s s' : S) (a : A)
    (σ σ' : Fl4Spec.State Unit) (hcn : Ipc.CnK σ σ') (hkc : KeepC σ σ') (hw : P1.WritesIn st s s' (InSlot th))
    {kb : U64} (hFI : FinInv th (L.mem s') σ' G') (hMO : MdbOKV kb (L.mem s') G') (hkz : KSz σ σ')
    (hDl : DelInv th (L.mem s) → DelInv th (L.mem s'))
    (hR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → XTopAt (L := L) AR { Z with G := G' } s' a σ' →
      SlotRest (L := L) arI { Z with G := G' } H Cs s s' σ σ') :
    JOwesCs (L := L) arI AR th G' s a σ s' a σ' := by
  intro Z H Cs Ac Lst D hth J hX'
  subst hth
  have hC := CnStep.of_cnK hcn hkc
  obtain ⟨k1, k2, kb, k3, k4⟩ := inSlot_keeps arI J hw
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, hC.sc.2 hq, rfl⟩, fun q x hq => ⟨x, (hC.look (fun _ _ e => by cases e)).2 hq,
    rfl, rfl⟩, fun p x n hp => ⟨x, hC.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => ⟨x, hC.tcb.2 hp, rfl⟩, fun p x n hp => ⟨x, hC.sc.2 hp, rfl⟩,
    fun p y n hp => ⟨y, hC.sc.1 hp, rfl⟩⟩
  have mk : McpKeep σ σ' := fun p x hp => ⟨x, hC.tcb.2 hp, rfl⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hw.1 ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  obtain ⟨Ac', hjpl, hCK, hUK, horig, hutc, hblk⟩ := hR Z H Cs Ac Lst D rfl J hX'
  have hdead : ∀ q ∈ D, DeadP (L := L) H s q → DeadP (L := L) H s' q := fun q _ hd =>
    J.deadP_hstep hX' hC.toHStep k3 (fun q z hq K h8 hK => J.inSlot_scKeep hw hq h8 hK) (J.act.cn hC).1 hd
  obtain ⟨-, ⟨-, -, hM', -, -⟩, -⟩ := hX'.rel
  have hJC := J.jcs_slot hM' hMO hFI hUK hkz (hDl J.del)
  have hjc := J.jcov_cover hw.1 hM' hCK hUK fun q hq => hdead q hq (J.jcov.dead q hq)
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  have hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcn.1; exact e
  have hkern := J.kern_keep hw.1 hw.2.1 hX'.fin.1.1.1 hC.ct hC.csc horig hgp
    (fun p ao h => (hC.look (fun _ _ e => by cases e)).2 h) hDbg
    (D' := D) J.kern.cscLive
  refine ⟨hJC, Ac', Lst, D, ⟨hCR', hRF', J.yld.frame k2 yk, J.mcp.frame k1 mk,
    J.buf.frame kb (fun p x hp => ⟨x, hC.tcb.2 hp, rfl⟩), hRP', J.apart.sc_frame hw.1 (SzKeep.of_keepC hkc), hjpl,
    hjc, hkern, hutc, J.nsc.cn hC.toHStep, J.inv.cn hC, CurInvW.cn J.cur hC, J.own.cn hC.toHStep, J.off.cn hC.toHStep,
    J.act.cn hC,
    J.bsa.cn hC.toHStep, J.isorted.cn hC.toHStep, J.curRun.cn hC.toHStep, hblk⟩⟩

/-- **What an insertion still owes** [W]: `SlotRest` but for the caps' cover,
the untyped regions and the original bits, which the insertion gives (one
slot changed, from `Null`, to no untyped cap; `capInsert_orig`): the joint
placement, the untyped caps' facts and P1's
`BlkOK`. -/
def InsRest (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s' : S) (σ' : Fl4Spec.State Unit) : Prop :=
  ∃ (Ac' : Set U64), (∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ') ∧
    (∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) →
      UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi) ∧
    P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s'

/-- **`JStepHyps.slot` from `InsRest`** (an insertion between two CNodes'
slots: `CnK`, and `KeepC` from the two CNodes, `capInsert_nko`; the
destination's cap the only one changed, from `Null` and to no untyped cap:
`CoverKept`, `UtKept`; its original bit the only one set, at an `AbsSlot`). -/
theorem jowes_ins {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {G' : MdbGhost} (s s' : S) (a : A)
    (σ σ' : Fl4Spec.State Unit) (c : Fl4Spec.Cap) (ps pd : U64) (rs rd : Nat) (idxs idxd : List Bool)
    (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    (hci : Fl4Spec.capInsert (Z := Unit) c (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False))
    (hld : idxd.length = rd)
    (hcap : ∀ y, IsSlot th y → y ≠ cslotAddr (pd.bv, idxd) → capV (L.mem s') y = capV (L.mem s) y)
    (hnull : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (hnu : ∀ p sb fi d, capV (L.mem s') (cslotAddr (pd.bv, idxd)) ≠ .Untyped p sb fi d)
    (hw : P1.WritesIn st s s' (InSlot th)) (hFI : FinInv th (L.mem s') σ' G') (hMO : MdbOKV (L.ksb s) (L.mem s') G')
    (hDl : DelInv th (L.mem s) → DelInv th (L.mem s'))
    (hR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → XTopAt (L := L) AR { Z with G := G' } s' a σ' →
      InsRest (L := L) arI { Z with G := G' } H Cs s' σ') :
    JOwesCs (L := L) arI AR th G' s a σ s' a σ' := by
  intro Z H Cs Ac Lst D hth J hX'
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) c (ps.bv, idxs) (pd.bv, idxd) σ).1 := by rw [hci]; rfl
  have hcn := capInsert_nkn c _ _ σ _ hmem
  have hSt := J.xtop.rel.2.1.1
  subst hth
  have hkc : KeepC σ σ' := keepC_of hcn (capInsert_nko c _ _ σ _ hmem) (by
    rintro p (rfl | hp)
    · obtain ⟨cs, h, -⟩ := hSt.cnode ps rs hps; exact ⟨rs, cs, h⟩
    · rw [Set.mem_singleton_iff.1 hp]; obtain ⟨cs, h, -⟩ := hSt.cnode pd rd hpd; exact ⟨rd, cs, h⟩)
  refine jowes_slotOf arI s s' a σ σ' hcn hkc hw hFI hMO (capInsert_nkz c _ _ σ _ hmem) hDl
    (fun Z2 H2 Cs2 Ac2 Lst2 D2 hth2 J2 hX2 => ?_) Z H Cs Ac Lst D rfl J hX'
  obtain ⟨Ac', hjpl, hutc, hblk⟩ := hR Z2 H2 Cs2 Ac2 Lst2 D2 hth2 J2 hX2
  have hcap' : ∀ y, IsSlot Z2.th y → y ≠ cslotAddr (pd.bv, idxd) → capV (L.mem s') y = capV (L.mem s) y :=
    fun y h => hcap y (hth2 ▸ h)
  have hn0 : capV (L.mem s) (cslotAddr (pd.bv, idxd)) = .Null := by
    have h := capAt_capV (L.mem s) (cslotAddr (pd.bv, idxd)); rw [hnull] at h; exact (eq_of_ok_eq h).symm
  refine ⟨Ac', hjpl, fun y hy hp hu => ?_, fun x hx p sb fi d hc => ?_, fun sl h => ?_, hutc, hblk⟩
  · have hyd : y ≠ cslotAddr (pd.bv, idxd) := fun e => by rw [e, hn0, physF_null] at hp; cases hp
    have e := hcap' y hy hyd
    exact ⟨y, hy, by rw [e]; exact hp, by rw [e]; exact hu, by rw [e], by rw [e]⟩
  · have hxd : x ≠ cslotAddr (pd.bv, idxd) := fun e => hnu p sb fi d (e ▸ hc)
    exact ⟨x, hx, fi, d, by rw [← hcap' x hx hxd]; exact hc, Or.inl le_rfl⟩
  · by_cases e : sl = (pd.bv, idxd)
    · right; subst e; exact ⟨pd, rfl, Or.inl (by rw [hld]; exact hth2 ▸ hpd)⟩
    · left; rw [← capInsert_orig c _ _ σ ((), σ') hmem sl e]; exact h

/-- **`JStepHyps.cslot` from `InsRest`** (a CNode copy, mint, move, mutate
or rotate: `CnK`, `KeepC`, and the cover, the untyped regions and the
original bits from the step, StepSem's `cslot`). -/
theorem jowes_cn {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {G' : MdbGhost} (s s' : S) (a : A)
    (σ σ' : Fl4Spec.State Unit) (hcn : Ipc.CnK σ σ') (hkc : KeepC σ σ')
    (hCK : CoverKept th (L.mem s) (L.mem s')) (hUK : UtKept th (L.mem s) (L.mem s'))
    (horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot th sl)
    (hw : P1.WritesIn st s s' (InSlot th)) (hFI : FinInv th (L.mem s') σ' G') (hMO : MdbOKV (L.ksb s) (L.mem s') G')
    (hkz : KSz σ σ') (hDl : DelInv th (L.mem s) → DelInv th (L.mem s'))
    (hR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → XTopAt (L := L) AR { Z with G := G' } s' a σ' →
      InsRest (L := L) arI { Z with G := G' } H Cs s' σ') :
    JOwesCs (L := L) arI AR th G' s a σ s' a σ' := by
  refine jowes_slotOf arI s s' a σ σ' hcn hkc hw hFI hMO hkz hDl (fun Z2 H2 Cs2 Ac2 Lst2 D2 hth2 J2 hX2 => ?_)
  obtain ⟨Ac', hjpl, hutc, hblk⟩ := hR Z2 H2 Cs2 Ac2 Lst2 D2 hth2 J2 hX2
  subst hth2
  exact ⟨Ac', hjpl, hCK, hUK, horig, hutc, hblk⟩

/-! ## A kernel-state step -/

/-- **A word outside the kernel-state block is kept by `KsW` writes** (the
kernel-state steps' write set). -/
theorem ksW_keep {s s' : S} (hw : P1.WritesIn st s s' (KsW (L.ksb s))) {b : U64} (hb : P1.Aligned b)
    (hout : b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ b.val) : L.mem s' b = L.mem s b :=
  hw.mem_eq hb fun h => by obtain ⟨K, h1, h2, -, e⟩ := h; omega

/-- **The scheduler's words a kernel-state step keeps** (as `inSlot_keeps`):
the TCBs, the SCs and the replies lie outside the kernel-state block. -/
theorem ksW_keeps {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (KsW (L.ksb s))) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hko : ∀ t ∈ Z.T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := fun t ht => by
    rcases hc.ksOut t ht with h | h <;> omega
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  refine ⟨fun t ht => ksW_keep hw (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; rcases hko t ht with h | h <;> omega),
    fun t ht => ksW_keep hw (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; rcases hko t ht with h | h <;> omega),
    fun t ht => ksW_keep hw (tIpcBufA_aligned (hT t ht)) (by
      rw [tIpcBufA_val (hT t ht)]; rcases hko t ht with h | h <;> omega), fun q hq => ?_, fun r hr => ?_⟩
  · obtain ⟨hal, hv, hfit⟩ := sc_reply_word hS hq
    obtain ⟨x, n, hk, hx⟩ := hs.scs q hq
    have := (hS.scOutIn hq (a := scReplyA q) ⟨by rw [hv]; omega, by rw [hv]; omega⟩).2.2.2
    exact ksW_keep hw hal (by omega)
  · have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    have hk := J.rp.ksb r hr
    exact ⟨ksW_keep hw (J.rp.aligned hr (Or.inl h8)) (by omega), ksW_keep hw (J.rp.aligned hr (Or.inr h16)) (by omega)⟩

/-- **`JPlaced` across a step** keeping every slot, the kernel-state base,
the SCs' sizes and the IRQ node's caps (`JPlaced.same`). -/
theorem JAtZ.jpl_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hkh : σ'.kheap = σ.kheap) (hks : L.ksb s' = L.ksb s)
    (hI : ∀ i : U64, i.val < 128 → capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i)) :
    ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact ⟨Tr, Cq, hJ.same hSS (fun c y n _ hk => ⟨y, by rw [← hkh]; exact hk⟩) hks hI⟩

/-- **The IRQ node's caps are kept by writes outside its words.** -/
theorem irqNode_keep {s s' : S} {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hW : ∀ b, W b → b.val < (L.ksb s).val + 1248 ∨ (L.ksb s).val + 5344 ≤ b.val) (i : U64) (hi : i.val < 128) :
    capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) := by
  have hv := nodeA_val hf hi
  have hv8 : (wordOf (nodeA (L.ksb s) i) 8#u64).val = (L.ksb s).val + 1248 + 32 * i.val + 8 := by
    rw [wordOf_val (by rw [hv]; simp; omega), hv]; rfl
  unfold capV
  rw [hw.mem_eq (b := nodeA (L.ksb s) i) (by unfold P1.Aligned; rw [hv]; omega) fun h => by
      rcases hW _ h with e | e <;> omega,
    hw.mem_eq (b := wordOf (nodeA (L.ksb s) i) 8#u64) (by unfold P1.Aligned; rw [hv8]; omega) fun h => by
      rcases hW _ h with e | e <;> omega]

/-- **What a kernel-state step still owes** [W]: the untyped caps' facts and
P1's `BlkOK`. -/
def KsRest (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s' : S) (σ' : Fl4Spec.State Unit) : Prop :=
  ∃ (Ac' : Set U64),
    (∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) →
      UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi) ∧
    P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s'

set_option maxHeartbeats 4000000 in
/-- **`JStepHyps.ks` from `KsRest`**: FL4 writes kernel-state words only
(`ksW_keeps`), the spec keeps the heap and the scheduler's fields (`KsStep`,
so `CnStep`). -/
theorem jowes_ks {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (s s' : S) (a a' : A) (σ σ' : Fl4Spec.State Unit)
    (hw : P1.WritesIn st s s' (KsW (L.ksb s))) (hO : KsStep σ σ')
    (hR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → XTopAt (L := L) AR Z s' a' σ' →
      KsRest (L := L) arI Z H Cs D s' σ') :
    JOwes (L := L) arI AR th s a σ s' a' σ' := by
  intro Z H Cs Ac Lst D hth J hX'
  have hC : CnStep σ σ' := ⟨⟨fun p => Or.inl (by rw [hO.kh]), hO.rel, hO.ct, hO.csc, hO.ctime, hO.cons, hO.idle⟩,
    hO.rq, hO.act⟩
  obtain ⟨k1, k2, kb, k3, k4⟩ := ksW_keeps arI J hw
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, hC.sc.2 hq, rfl⟩, fun q x hq => ⟨x, (hC.look (fun _ _ e => by cases e)).2 hq,
    rfl, rfl⟩, fun p x n hp => ⟨x, hC.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => ⟨x, hC.tcb.2 hp, rfl⟩, fun p x n hp => ⟨x, hC.sc.2 hp, rfl⟩,
    fun p y n hp => ⟨y, hC.sc.1 hp, rfl⟩⟩
  have mk : McpKeep σ σ' := fun p x hp => ⟨x, hC.tcb.2 hp, rfl⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hw.1 ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  obtain ⟨Ac', hutc, hblk⟩ := hR Z H Cs Ac Lst D hth J hX'
  have hI : ∀ i : U64, i.val < 128 → capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hw J.kern.ksbFit J.kern.ksbAl fun b hb => by
      obtain ⟨K, -, -, -, e, h⟩ := hb; omega
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hf := J.kern.nodeFit
    have hv := nodeAt_val' (st := st) (s := s) (c := 0#u64) (off := layout.node.DEBUG_TCBS) (by simp; omega)
      (by simp [layout.node.DEBUG_TCBS])
    exact ksW_keep hw J.kern.dwAl (by rw [hv]; omega)
  have hkern := J.kern_keep hw.1 hw.2.1 hX'.fin.1.1.1 hO.ct hO.csc (fun sl h => Or.inl (by rw [← hO.orig]; exact h)) hO.gpml4 (fun p ao h => by rw [hO.kh]; exact h)
    hDbg (D' := D) J.kern.cscLive
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b hb => by obtain ⟨K, h1, h2, -, e⟩ := hb; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_hstep hX' hC.toHStep k3 (fun q z hq K h8 hK => J.ksW_scKeep hw hq h8 hK) (J.act.cn hC).1 (J.jcov.dead q hq)
  exact ⟨Ac', Lst, D, ⟨hCR', hRF', J.yld.frame k2 yk, J.mcp.frame k1 mk,
    J.buf.frame kb (fun p x hp => ⟨x, hC.tcb.2 hp, rfl⟩), hRP', J.apart.sc_frame hw.1 (SzKeep.of_kheap hO.kh),
    J.jpl_keep arI hSS hO.kh hw.1 hI, J.jcov_keep hw.1 hSS hdead, hkern, hutc, J.nsc.cn hC.toHStep, J.inv.cn hC, CurInvW.cn J.cur hC, J.own.cn hC.toHStep, J.off.cn hC.toHStep,
    J.act.cn hC,
    J.bsa.cn hC.toHStep, J.isorted.cn hC.toHStep, J.curRun.cn hC.toHStep, hblk⟩⟩

/-! ## A scheduler step -/

/-- **The scheduler's words a scheduler step keeps** (as `inSlot_keeps`, for
`SchW`: the TCBs' queue words, the node, the domain words). -/
theorem schW_keeps {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (SchW (L := L) Z.T Z.c s)) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  have hP := J.xtop.fin.1.2
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hko : ∀ t ∈ Z.T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := fun t ht => by
    rcases hc.ksOut t ht with h | h <;> omega
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  have hnd := hc.node.disj
  -- a word apart from the TCBs' queue words, the node and the domain words
  have keep : ∀ b : U64, P1.Aligned b → (∀ y ∈ Z.T, b.val ≠ y.val + 3480 ∧ b.val ≠ y.val + 3488 ∧ b.val ≠ y.val + 3592) →
      (b.val < L.nodeBase s Z.c ∨ L.nodeBase s Z.c + 4288 ≤ b.val) →
      (b.val + 8 ≤ (L.ksb s).val + 16 ∨ (L.ksb s).val + 216 < b.val) → L.mem s' b = L.mem s b := by
    intro b hb h1 h2 h3
    refine hw.mem_eq hb fun hb' => ?_
    rcases schW_val hT hkf hb' with ⟨y, hy, e | e | e⟩ | ⟨g1, g2⟩ | ⟨g1, g2, -⟩
    · exact (h1 y hy).1 e
    · exact (h1 y hy).2.1 e
    · exact (h1 y hy).2.2 e
    · omega
    · omega
  have tw : ∀ t ∈ Z.T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 → K.val ≠ 3592 →
      L.mem s' (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K) := by
    intro t ht K h1 h8 n1 n2 n3
    have hv := Notif.tfield_val (hT t ht) h1 (K := K)
    refine keep _ (P1.field_aligned (hT t ht) h1 h8) (fun y hy => ?_) ?_ ?_
    · by_cases e : y = t
      · subst e; omega
      · have := tcb_disj hP.ep ht hy e; omega
    · have := hnd t ht; omega
    · rcases hko t ht with h | h <;> omega
  refine ⟨fun t ht => tw t ht 3440#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
    fun t ht => tw t ht 3472#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
    fun t ht => tw t ht 3512#u64 (by simp) (by simp) (by simp) (by simp) (by simp), fun q hq => ?_, fun r hr => ?_⟩
  · obtain ⟨hal, hv, -⟩ := sc_reply_word hS hq
    obtain ⟨-, o1, o2, o3⟩ := hS.scOutIn hq (a := scReplyA q) ⟨by rw [hv]; omega, by rw [hv]; omega⟩
    refine keep _ hal (fun y hy => ?_) (by omega) (by omega)
    rcases o2 y hy with h | h <;> omega
  · have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    have hk := J.rp.ksb r hr
    have ht := J.rp.tcb r hr
    refine ⟨keep _ (J.rp.aligned hr (Or.inl h8)) (fun y hy => ?_) (by omega) (by omega),
      keep _ (J.rp.aligned hr (Or.inr h16)) (fun y hy => ?_) (by omega) (by omega)⟩
    · rcases ht y hy with h | h <;> omega
    · rcases ht y hy with h | h <;> omega

/-- **What a scheduler step still owes** [W]: `Inv` (its ready queues), the
current thread's invariant and `ActIdle` (the action changed), the joint
the node-0 `DEBUG_TCBS` word kept (the node may be core 0's), the untyped
caps' facts and P1's `BlkOK`. -/
def SchedRest (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s s' : S) (σ' : Fl4Spec.State Unit) : Prop :=
  Inv σ' ∧ (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ ActIdle σ' ∧
  ∃ (Ac' : Set U64),
    L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ∧
    (∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) →
      UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi) ∧
    P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s'

set_option maxHeartbeats 4000000 in
/-- **`JStepHyps.sched` from `SchedRest`**: FL4 writes the scheduler's words
(`schW_keeps`), the spec keeps the heap (`SchedK`, so `HStep`). -/
theorem jowes_sched {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit)
    (hS : SchedStep (L := L) th s σ s' σ')
    (hR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → XTopAt (L := L) AR Z s' a σ' →
      SchedRest (L := L) arI Z H Cs D s s' σ') :
    JOwes (L := L) arI AR th s a σ s' a σ' := by
  intro Z H Cs Ac Lst D hth J hX'
  subst hth
  obtain ⟨hK, hS2⟩ := hS
  have hw := (hS2 Z.N Z.T Z.C Z.c J.thT J.xtop.fin.1.1.1 J.xtop.fin.1.1.2.2.1).2.1
  have hC : HStep σ σ' := ⟨fun p => Or.inl (by rw [hK.kh]), hK.rel, hK.ct, hK.csc, hK.ctime, hK.cons, hK.idle⟩
  obtain ⟨k1, k2, kb, k3, k4⟩ := schW_keeps arI J hw
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, hC.sc.2 hq, rfl⟩, fun q x hq => ⟨x, (hC.look (fun _ _ e => by cases e)).2 hq,
    rfl, rfl⟩, fun p x n hp => ⟨x, hC.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => ⟨x, hC.tcb.2 hp, rfl⟩, fun p x n hp => ⟨x, hC.sc.2 hp, rfl⟩,
    fun p y n hp => ⟨y, hC.sc.1 hp, rfl⟩⟩
  have mk : McpKeep σ σ' := fun p x hp => ⟨x, hC.tcb.2 hp, rfl⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hw.1 ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  obtain ⟨hI', hcur', hA', Ac', hDbg, hutc, hblk⟩ := hR Z H Cs Ac Lst D rfl J hX'
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := J.kern.ksbFit
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  have hko : ∀ t ∈ Z.T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := fun t ht => by
    rcases hcq.ksOut t ht with h | h <;> omega
  have hI : ∀ i : U64, i.val < 128 → capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hw hkf J.kern.ksbAl fun b hb => by
      rcases schW_val hcq.tcbs hkf hb with ⟨y, hy, e | e | e⟩ | ⟨g1, g2⟩ | ⟨g1, g2, -⟩
      all_goals first
        | omega
        | (rcases hko y hy with h | h <;> omega)
  have hkern := J.kern_keep hw.1 hw.2.1 hX'.fin.1.1.1 hK.ct hK.csc (fun sl h => Or.inl (by rw [← hK.orig]; exact h)) (by rw [hK.arch])
    (fun p ao h => by rw [hK.kh]; exact h) hDbg (D' := D) J.kern.cscLive
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b hb => schW_oobj J.xtop.fin.1.1.1.placed.tcb hb
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_hstep hX' hC k3 (fun q z hq K h8 hK => J.schW_scKeep hw hq h8 hK) hA'.1 (J.jcov.dead q hq)
  exact ⟨Ac', Lst, D, ⟨hCR', hRF', J.yld.frame k2 yk, J.mcp.frame k1 mk,
    J.buf.frame kb (fun p x hp => ⟨x, hC.tcb.2 hp, rfl⟩), hRP', J.apart.sc_frame hw.1 (SzKeep.of_kheap hK.kh),
    J.jpl_keep arI hSS hK.kh hw.1 hI, J.jcov_keep hw.1 hSS hdead, hkern, hutc, J.nsc.cn hC, hI', hcur', J.own.cn hC, J.off.cn hC, hA', J.bsa.cn hC, J.isorted.cn hC,
    J.curRun.cn hC, hblk⟩⟩

end

end

end Fl4Proofs.P3
