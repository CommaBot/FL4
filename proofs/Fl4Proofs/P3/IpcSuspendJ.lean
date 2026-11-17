/-
P3 (DESIGN.md §9), TCB invocations: **Suspend from `JAtZ`** (the fold's
re-scoping of `suspendXLeaf_of`).

* Spec frames for a TCB update keeping the fields the scheduler invariants
  read (`TView`: state, SC, bound notification, yield-to):
  `SchedValid.tcbView`, `ObjCover.tcbView`, `NSC.tcbView`.
* `removeTcbOK_fault`: `RemoveTcbOK` across `cancel_ipc`'s fault clear, the
  one state `cancel_ipc` calls `reply_remove_tcb` at
  (`cancel_ipc_irelP`'s `P`).
-/
import Fl4Proofs.P3.IpcTcbJ
import Fl4Proofs.P3.IpcYK
import Fl4Proofs.P3.IpcSuspend
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec

noncomputable section

section Spec

/-- A TCB update keeping what the scheduler invariants read. -/
def TView (σ σ' : State Unit) : Prop :=
  ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧
    y.tcbState = x.tcbState ∧ y.tcbSchedContext = x.tcbSchedContext ∧
    y.tcbBoundNotification = x.tcbBoundNotification ∧ y.tcbYieldTo = x.tcbYieldTo

theorem TView.upd {σ : State Unit} {p : ObjRef} {x y : Tcb} (hk : σ.kheap p = some (.tcb x))
    (h1 : y.tcbState = x.tcbState) (h2 : y.tcbSchedContext = x.tcbSchedContext)
    (h3 : y.tcbBoundNotification = x.tcbBoundNotification) (h4 : y.tcbYieldTo = x.tcbYieldTo) :
    TView σ (Notif.updK σ p (.tcb y)) := by
  intro q
  by_cases e : q = p
  · subst e; exact Or.inr ⟨x, y, hk, by simp [Notif.updK], h1, h2, h3, h4⟩
  · exact Or.inl (by simp [Notif.updK, Function.update_of_ne e])

section
variable {σ σ' : State Unit} (h : TView σ σ')
include h

theorem TView.fwd {q : ObjRef} {x : Tcb} (hq : σ.kheap q = some (.tcb x)) :
    ∃ y, σ'.kheap q = some (.tcb y) ∧ y.tcbState = x.tcbState ∧ y.tcbSchedContext = x.tcbSchedContext ∧
      y.tcbBoundNotification = x.tcbBoundNotification ∧ y.tcbYieldTo = x.tcbYieldTo := by
  rcases h q with e | ⟨a, b, ha, hb, e1, e2, e3, e4⟩
  · exact ⟨x, e.trans hq, rfl, rfl, rfl, rfl⟩
  · rw [hq] at ha; cases ha; exact ⟨b, hb, e1, e2, e3, e4⟩

theorem TView.bwd {q : ObjRef} {y : Tcb} (hq : σ'.kheap q = some (.tcb y)) :
    ∃ x, σ.kheap q = some (.tcb x) ∧ y.tcbState = x.tcbState ∧ y.tcbSchedContext = x.tcbSchedContext ∧
      y.tcbBoundNotification = x.tcbBoundNotification ∧ y.tcbYieldTo = x.tcbYieldTo := by
  rcases h q with e | ⟨a, b, ha, hb, e1, e2, e3, e4⟩
  · exact ⟨y, by rw [← e]; exact hq, rfl, rfl, rfl, rfl⟩
  · rw [hq] at hb; cases hb; exact ⟨a, ha, e1, e2, e3, e4⟩

theorem TView.ntcb {q : ObjRef} {o : KernelObject} (ho : ∀ x, o ≠ .tcb x) :
    σ'.kheap q = some o ↔ σ.kheap q = some o := by
  rcases h q with e | ⟨a, b, ha, hb, -⟩
  · rw [e]
  · rw [ha, hb]; constructor <;> intro e <;> cases e <;> exact absurd rfl (ho _)

end

theorem TView.qrdy {σ σ' : State Unit} (h : TView σ σ') (ht : σ'.curTime = σ.curTime) {u : ObjRef}
    (hq : QRdy σ u) : QRdy σ' u := by
  obtain ⟨x, hx, hr⟩ := hq
  obtain ⟨y, hy, -, e2, -⟩ := h.fwd hx
  refine ⟨y, hy, fun c hc yc k hk ha => ?_⟩
  rw [ht]
  exact hr c (e2 ▸ hc) yc k ((h.ntcb (fun _ e => by cases e)).1 hk) ha

/-- **`SchedValid` across a `TView` step** keeping the time. -/
theorem SchedValid.tcbView {σ σ' : State Unit} (hV : SchedValid σ) (h : TView σ σ') (ht : σ'.curTime = σ.curTime) :
    SchedValid σ' := by
  have nE : ∀ {q x}, σ'.kheap q = some (.endpoint x) ↔ σ.kheap q = some (.endpoint x) :=
    h.ntcb (fun _ e => by cases e)
  have nN : ∀ {q x}, σ'.kheap q = some (.notification x) ↔ σ.kheap q = some (.notification x) :=
    h.ntcb (fun _ e => by cases e)
  have nR : ∀ {q x}, σ'.kheap q = some (.reply x) ↔ σ.kheap q = some (.reply x) :=
    h.ntcb (fun _ e => by cases e)
  have nS : ∀ {q y k}, σ'.kheap q = some (.schedContext y k) ↔ σ.kheap q = some (.schedContext y k) :=
    h.ntcb (fun _ e => by cases e)
  refine ⟨fun e x hx => ?_, fun n x hx => ?_, fun t x ep ro d hx hs => ?_, fun t x ep pl hx hs => ?_,
    fun t x n hx hs => ?_, fun t x ep r d hx hs => ?_, fun t x r hx hs => ?_, fun r xr t hr ht' => ?_,
    fun sc y k r hy hr => ?_, fun sc y k f hy hf => ?_, fun sc y k n hy hn => ?_, fun sc y k t hy hyf => ?_,
    fun t x p hx hp => ?_, fun t x n hx hn => ?_, fun n xn t hn ht' => ?_, fun sc y k hy hs => ?_⟩
  · obtain ⟨h1, h2⟩ := hV.epQ e x (nE.1 hx)
    exact ⟨h1, fun u hu => h.qrdy ht (h2 u hu)⟩
  · obtain ⟨h1, h2⟩ := hV.ntfnQ n x (nN.1 hx)
    refine ⟨h1, fun u hu => ?_⟩
    obtain ⟨xu, hku, hs⟩ := h2 u hu
    obtain ⟨y, hy, e1, -⟩ := h.fwd hku
    exact ⟨y, hy, e1.trans hs⟩
  · obtain ⟨x0, hx0, e1, -⟩ := h.bwd hx
    obtain ⟨xe, hke, hm⟩ := hV.recvQ t x0 ep ro d hx0 (e1 ▸ hs)
    exact ⟨xe, nE.2 hke, hm⟩
  · obtain ⟨x0, hx0, e1, -⟩ := h.bwd hx
    obtain ⟨xe, hke, hm⟩ := hV.sendQ t x0 ep pl hx0 (e1 ▸ hs)
    exact ⟨xe, nE.2 hke, hm⟩
  · obtain ⟨x0, hx0, e1, -⟩ := h.bwd hx
    obtain ⟨xn, hkn, hm⟩ := hV.ntfnW t x0 n hx0 (e1 ▸ hs)
    exact ⟨xn, nN.2 hkn, hm⟩
  · obtain ⟨x0, hx0, e1, -⟩ := h.bwd hx
    obtain ⟨xr, hkr, hm⟩ := hV.recvReply t x0 ep r d hx0 (e1 ▸ hs)
    exact ⟨xr, nR.2 hkr, hm⟩
  · obtain ⟨x0, hx0, e1, -⟩ := h.bwd hx
    obtain ⟨xr, hkr, hm⟩ := hV.onReply t x0 r hx0 (e1 ▸ hs)
    exact ⟨xr, nR.2 hkr, hm⟩
  · obtain ⟨x, hx, hs⟩ := hV.replyTcb r xr t (nR.1 hr) ht'
    obtain ⟨y, hy, e1, -⟩ := h.fwd hx
    exact ⟨y, hy, by rw [e1]; exact hs⟩
  · obtain ⟨xr, hkr, h1, h2⟩ := hV.replies sc y k r (nS.1 hy) hr
    exact ⟨xr, nR.2 hkr, h1, h2⟩
  · obtain ⟨x, hx⟩ := hV.scTcb sc y k f (nS.1 hy) hf
    obtain ⟨y', hy', -⟩ := h.fwd hx
    exact ⟨y', hy'⟩
  · obtain ⟨xn, hkn⟩ := hV.scNtfn sc y k n (nS.1 hy) hn
    exact ⟨xn, nN.2 hkn⟩
  · obtain ⟨x, hx, hyt⟩ := hV.scYieldFrom sc y k t (nS.1 hy) hyf
    obtain ⟨y', hy', -, -, -, e4⟩ := h.fwd hx
    exact ⟨y', hy', e4.trans hyt⟩
  · obtain ⟨x0, hx0, -, -, -, e4⟩ := h.bwd hx
    obtain ⟨y, k, hk⟩ := hV.tcbYieldTo t x0 p hx0 (e4 ▸ hp)
    exact ⟨y, k, nS.2 hk⟩
  · obtain ⟨x0, hx0, -, -, e3, -⟩ := h.bwd hx
    obtain ⟨xn, hkn⟩ := hV.tcbNtfn t x0 n hx0 (e3 ▸ hn)
    exact ⟨xn, nN.2 hkn⟩
  · obtain ⟨x, hx⟩ := hV.ntfnTcb n xn t (nN.1 hn) ht'
    obtain ⟨y', hy', -⟩ := h.fwd hx
    exact ⟨y', hy'⟩
  · exact hV.scSpor sc y k (nS.1 hy) hs

theorem ObjCover.tcbView {N T E R C : Set U64} {σ σ' : State Unit} (hO : ObjCover N T E R C σ) (h : TView σ σ') :
    ObjCover N T E R C σ' := by
  refine ⟨fun o x hx => ?_, fun o x hx => hO.ntfn o x ((h.ntcb (fun _ e => by cases e)).1 hx),
    fun o x hx => hO.ep o x ((h.ntcb (fun _ e => by cases e)).1 hx),
    fun o x hx => hO.reply o x ((h.ntcb (fun _ e => by cases e)).1 hx),
    fun o y k hx => hO.sc o y k ((h.ntcb (fun _ e => by cases e)).1 hx)⟩
  obtain ⟨x0, hx0, -⟩ := h.bwd hx
  exact hO.tcb o x0 hx0

theorem NSC.tcbView {N C : Set U64} {σ σ' : State Unit} (hN : NSC N C σ) (h : TView σ σ') : NSC N C σ' :=
  fun n hn x p hx hp => hN n hn x p ((h.ntcb (fun _ e => by cases e)).1 hx) hp

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`RemoveTcbOK` across a `TView` step** keeping the call-stack words,
the kernel-state base and the SCs' sizes. -/
theorem removeTcbOK_tview {s s' : S} {σ σ' : Fl4Spec.State Unit} (h : RemoveTcbOK st N T C E R c s σ)
    (hV : TView σ σ') (hq : σ'.readyQueues = σ.readyQueues) (hr : σ'.releaseQueue = σ.releaseQueue)
    (ht : σ'.curTime = σ.curTime) (hks : L.ksb s' = L.ksb s)
    (hs : ∀ sc ∈ C, L.mem s' (scReplyA sc) = L.mem s (scReplyA sc))
    (hm : ∀ r ∈ R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) :
    RemoveTcbOK st N T C E R c s' σ' := by
  obtain ⟨Lst, hCR, hRF, hRP, hN, hI, hC0, hSV, hOC⟩ := h
  have nR : ∀ {q x}, σ'.kheap q = some (.reply x) ↔ σ.kheap q = some (.reply x) :=
    hV.ntcb (fun _ e => by cases e)
  have nS : ∀ {q y k}, σ'.kheap q = some (.schedContext y k) ↔ σ.kheap q = some (.schedContext y k) :=
    hV.ntcb (fun _ e => by cases e)
  refine ⟨Lst, hCR.frame hs hm (fun q _ y n hy => ⟨y, nS.2 hy, rfl⟩) (fun d _ x hx => ⟨x, nR.2 hx, rfl⟩),
    hRF.frame hm (fun d _ ⟨x, hx, e⟩ => ⟨x, nR.1 hx, e⟩), hRP.frame hks (fun p x n hp => ⟨x, nS.1 hp⟩),
    hN.tcbView hV, ?_, hC0, hSV.tcbView hV ht, hOC.tcbView hV⟩
  refine hI.tcbView (fun p => ?_) hq hr ht
  rcases hV p with e | ⟨x, y, h1, h2, e1, e2, -⟩
  · exact Or.inl e
  · exact Or.inr ⟨x, y, h1, h2, e1, e2⟩

/-- **`RemoveTcbOK` across `cancel_ipc`'s fault clear** (`cancel_ipc_irelP`'s
`P` at `RemoveTcbOK`). -/
theorem removeTcbOK_fault (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (h : RemoveTcbOK st N T C E R c s σ) :
    RemoveTcbOK st N T C E R c (L.wr s (tFaultA t) 0#u64) (updK σ t.bv (.tcb { x with tcbFault := none })) := by
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hta := hc.tcbs t ht
  have hw := (a_fault hta).1
  have hfv := val_fault hta
  obtain ⟨-, -, -, hRP, -⟩ := id h
  refine removeTcbOK_tview h (TView.upd hk rfl rfl rfl rfl) rfl rfl rfl (L.ksb_wr _ _ _) (fun sc hsc => ?_)
    (fun r hr => ?_)
  · obtain ⟨y, n, hky, hy⟩ := hs.scs sc hsc
    obtain ⟨hal, hin⟩ := hy.hdr (K := 32#u64) (by decide) (by decide)
    rw [scReplyA_eq]
    refine rd_wr_ne hw hal fun e => ?_
    have := (hS.scOutIn hsc hin).2.2.1 t ht
    rw [← e, hfv] at this; omega
  · have hra := hRP.align r hr
    have htr := hRP.tcb r hr t ht
    refine ⟨rd_wr_ne hw (hRP.aligned hr (Or.inl (rPrevA_val hra))) fun e => ?_,
      rd_wr_ne hw (hRP.aligned hr (Or.inr (rNextA_val hra))) fun e => ?_⟩
    · have := congrArg UScalar.val e; rw [hfv, rPrevA_val hra] at this; omega
    · have := congrArg UScalar.val e; rw [hfv, rNextA_val hra] at this; omega

/-- **`RemoveTcbHypP` at `RemoveTcbOK`** (`reply_remove_tcb_irel`). -/
theorem removeTcbHypP_ok (hP0 : IPlaced N T E R B) :
    RemoveTcbHypP st th cr N T C E R B c (RemoveTcbOK st N T C E R c) := by
  intro s σ t x r hX hOK ht hk hst
  obtain ⟨Lst, hCR, hRF, hRP, hN, hI, hC0, hSV, hOC⟩ := hOK
  exact reply_remove_tcb_irel hP0 s σ hX hSV hOC hCR hRF hRP hN hI hC0 ht hk hst

/-- A write to a word off every TCB's yield word keeps them. -/
theorem yield_wr {s : S} {a v y : U64} (hT : TcbPlaced T) (hy : y ∈ T) (ha : Aligned a)
    (hne : ∀ y ∈ T, a.val ≠ y.val + 3472) : L.mem (L.wr s a v) (yieldA y) = L.mem s (yieldA y) := by
  have hya := hT y hy
  have hv : (yieldA y).val = y.val + 3472 := by unfold yieldA; rw [tfield_val hya (by decide)]; rfl
  refine rd_wr_ne ha (field_aligned hya (by decide) (by decide)) fun e => ?_
  exact hne y hy (by rw [e, hv])

theorem reg_ne_yield {t y i : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hy : y ∈ T) (hi : i.val < 24) :
    t.val + 256 + 8 * i.val ≠ y.val + 3472 := by
  have h1 := (hT t ht).align; have h2 := (hT y hy).align
  by_cases e : y = t
  · subst e; omega
  · have := val_ne_of_ne e; omega

/-- The scheduler's words (`SFootI`) are off every TCB's yield word. -/
theorem yield_sfootI {s s' : S} (hT : TcbPlaced T) (hN : NodePlaced st T s c)
    (hw : WritesIn st s s' (SFootI st T c s)) {y : U64} (hy : y ∈ T) :
    L.mem s' (yieldA y) = L.mem s (yieldA y) := by
  have hya := hT y hy
  refine hw.mem_eq (field_aligned hya (by decide) (by decide)) fun hb => ?_
  rcases hb with ⟨y', hy', hb⟩ | ⟨g1, g2⟩
  · have hya' := hT y' hy'
    rcases hb with e | e | e <;>
      exact tfield_ne hya hya' (K1 := 3472#u64) (by decide) (by decide) (fun _ => by decide) e
  · obtain ⟨o, ho, e⟩ := node_word hN g1 g2
    exact nodeAt_ne_tfield hN ho hy hya (K := 3472#u64) (by decide) e

set_option maxHeartbeats 8000000 in
/-- **`suspend` on `IRel`, the yield-to relation carried** (`suspend_irel`
re-scoped): `YieldRel` at the start, carried to `cancel_yield_to` across
`cancel_ipc` (FL4: P1's `KeepT`, from `BlkOK`; the spec: `YK.yk_cancelIpc`),
the restart PC, the dequeue and the release-queue removal (FL4: the
scheduler's words, `SFootI`). `RemoveTcbHyp` at the states `P`, `P` at the
fault-cleared state. -/
theorem suspend_irelY (hP0 : IPlaced N T E R B) {P : S → Fl4Spec.State Unit → Prop}
    (hRT : RemoveTcbHypP st th cr N T C E R B c P)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T)
    (hSV : SchedValid σ) (hOC : ObjCover N T E R C σ) (hInv : Inv σ)
    (hPf : ∀ x, σ.kheap t.bv = some (.tcb x) →
      P (L.wr s (tFaultA t) 0#u64) (updK σ t.bv (.tcb { x with tcbFault := none })))
    (hY : YieldRel T C (L.mem s) σ)
    {Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : P1.Heap} {Zb : U64 → Nat}
    (hB : P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Zb Ac s) :
    sched.suspend st ar s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.suspend (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c r.1 σ' ⦄ := by
  obtain ⟨x, hk, -⟩ := hX.1.tcb t ht
  obtain ⟨⟨Q1, R1, h0⟩, hBd, hXI, -, hSg⟩ := hB
  have hT : TcbPlaced T := hP0.e.tcb
  unfold sched.suspend
  refine WP.spec_bind (WP.spec_and (cancel_ipc_irelP hP0 hRT s a σ hX ht hk hSV hOC hInv (hPf x hk))
    (Fl4Proofs.P1.ipc.cancel_ipc.all s a t Q1 R1 h0 ht hBd hXI hSg.sub)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨rfl, σ1, x1, hc1, hX1, hk1, hs1⟩, hP1⟩
  try simp only [WP.uncurry'_pair] at hP1
  obtain ⟨-, -, -, -, -, -, k1, -⟩ := hP1
  have y1 : ∀ y ∈ T, L.mem s1 (yieldA y) = L.mem s (yieldA y) := fun y hy =>
    k1.fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  have yk1 : YK.YKS σ σ1 := YK.yk_cancelIpc t.bv σ ((), σ1) (by rw [hc1]; exact Set.mem_singleton _)
  step with P1.obj.Tcb.state.spec as ⟨i, hi⟩
  obtain ⟨x1', hk1', hTR1⟩ := hX1.1.tcb t ht
  rw [hk1] at hk1'; cases hk1'
  have hw : i.val = tsCode x1.tcbState := by rw [hi]; exact hTR1.st
  have hrun : i = sched.TS_RUNNING ↔ x1.tcbState = .running := by
    constructor
    · intro h; rw [h] at hw; unfold sched.TS_RUNNING at hw
      generalize x1.tcbState = ts at hw ⊢; cases ts <;> simp_all [tsCode]
    · intro h; rw [h] at hw; apply UScalar.eq_of_val_eq; unfold sched.TS_RUNNING; simp [tsCode] at hw; simp [hw]
  -- the restart PC
  have hreg : (if i = sched.TS_RUNNING then do
        let ip ← obj.Tcb.reg st t s1 layout.reg.NEXT_IP
        obj.Tcb.set_reg st t s1 layout.reg.FAULT_IP ip
      else ok s1) ⦃ s2 => ∃ σ2 x2,
        Fl4Spec.NonDet.when (x1.tcbState = .running) (Fl4Spec.updateRestartPc (Z := Unit) t.bv) σ1 =
          ({((), σ2)}, False) ∧ IRel st th cr N T C E R B c s2 σ2 ∧ σ2.kheap t.bv = some (.tcb x2) ∧
          x2.tcbState = x1.tcbState ∧ YK.YKS σ1 σ2 ∧ ∀ y ∈ T, L.mem s2 (yieldA y) = L.mem s1 (yieldA y) ⦄ := by
    by_cases hr : x1.tcbState = .running
    · rw [if_pos (hrun.2 hr)]
      step with Endp.obj.Tcb.reg.spec as ⟨ip, hip⟩
      refine WP.spec_mono (Endp.obj.Tcb.set_reg.spec s1 t _ ip) ?_
      rintro s2 rfl
      have hF : layout.reg.FAULT_IP = regIdx .faultIP := by unfold layout.reg.FAULT_IP; rfl
      have hNx : layout.reg.NEXT_IP = regIdx .nextIP := by unfold layout.reg.NEXT_IP; rfl
      have hipv : ip.bv = x1.tcbArch.tcbContext.userRegs .nextIP := by rw [hip, hNx]; exact hTR1.regs .nextIP
      rw [hF]
      refine ⟨_, Notif.setReg x1 .faultIP ip.bv, ?_, reg_wr_irel hP0 hX1 ht hk1 .faultIP (by decide) ip,
        by simp [Notif.updK], rfl, YK.YKS.updTcb hk1 rfl, fun y hy => yield_wr hT hy (a_reg (hT t ht) .faultIP).1
          (fun y hy => by rw [regA_val (hT t ht) (regIdx_lt _)]; exact reg_ne_yield hT ht hy (regIdx_lt _))⟩
      unfold Fl4Spec.NonDet.when
      rw [if_pos hr, updateRestartPc_eq hk1, hipv]
    · rw [if_neg (fun h => hr (hrun.1 h)), WP.spec_ok]
      refine ⟨σ1, x1, ?_, hX1, hk1, rfl, YK.YKS.refl _, fun _ _ => rfl⟩
      unfold Fl4Spec.NonDet.when
      rw [if_neg hr]; rfl
  refine WP.spec_bind hreg ?_
  rintro s2 ⟨σ2, x2, hw2, hX2, hk2, hs2, yk2, y2⟩
  -- the ready queue
  have hS2 := hX2.2.2.1
  refine WP.spec_bind (WP.spec_and (dequeue_refines s2 σ2 hS2 t ht) (dequeue_sfootI hS2 ht)) ?_
  rintro s3 ⟨⟨σ3, he3, hk3, -, -, hS3⟩, hw3⟩
  have hX3 := sc_step_lift hP0 hX2 (hw3.mono fun _ h => Or.inr h) (NKS.of_eq (nks_tcbSchedActionI _ _) he3) hS3
  have y3 : ∀ y ∈ T, L.mem s3 (yieldA y) = L.mem s2 (yieldA y) := fun y hy =>
    yield_sfootI hT (let ⟨_, _, hc, _⟩ := hS2.lists; hc.node) hw3 hy
  have yk3 : YK.YKS σ2 σ3 := YK.yk_tcbSchedAction _ _ σ2 ((), σ3) (by rw [he3]; exact Set.mem_singleton _)
  -- the release queue
  have hS3' := hX3.2.2.1
  refine WP.spec_bind (WP.spec_and (release_remove_refines s3 σ3 hS3' ht) (release_remove_sfootI hS3' ht)) ?_
  rintro s4 ⟨⟨σ4, he4, ⟨bb, hσ4⟩, -, hS4⟩, hw4⟩
  have hX4 := sc_step_lift hP0 hX3 (hw4.mono fun _ h => Or.inr h) (NKS.of_eq (nks_tcbReleaseRemove _) he4) hS4
  have hk4 : σ4.kheap t.bv = some (.tcb x2) := by rw [hσ4]; show σ3.kheap t.bv = _; rw [hk3]; exact hk2
  have y4 : ∀ y ∈ T, L.mem s4 (yieldA y) = L.mem s3 (yieldA y) := fun y hy =>
    yield_sfootI hT (let ⟨_, _, hc, _⟩ := hS3'.lists; hc.node) hw4 hy
  have yk4 : YK.YKS σ3 σ4 := YK.yk_tcbReleaseRemove _ σ3 ((), σ4) (by rw [he4]; exact Set.mem_singleton _)
  have hY4 : YieldRel T C (L.mem s4) σ4 :=
    hY.frame (fun y hy => ((y4 y hy).trans (y3 y hy)).trans ((y2 y hy).trans (y1 y hy)))
      (yk1.trans (yk2.trans (yk3.trans yk4))).ykeep
  -- the yield-to pair
  refine WP.spec_bind (cancel_yield_to_irel hP0 hX4 hY4 ht) ?_
  rintro s5 ⟨σ5, he5, hX5, hk5f⟩
  obtain ⟨x5, hk5, hs5⟩ := hk5f x2 hk4
  have hst5 : x5.tcbState = cancelSt x.tcbState := by rw [hs5, hs2, hs1]
  -- inactive
  obtain ⟨x5', hk5', hTR5⟩ := hX5.1.tcb t ht
  rw [hk5] at hk5'; cases hk5'
  have hc5 := cancelSt_code x.tcbState
  have hw5 : (L.mem s5 (tStA t)).val = tsCode (cancelSt x.tcbState) := by rw [hTR5.st, hst5]
  have hq := IpcRel.not_ep_queued hX5.1 (t := t) ⟨by rw [hw5]; exact hc5.1, by rw [hw5]; exact hc5.2.1⟩
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP0.e
  have hSR := IpcRel.toSRN hX5.1 hX5.2
  refine WP.spec_bind (set_thread_state_c hH hP0 hP0.e _ _ hX5.1.toE hSR ht hk5 hq (by rw [hst5]; exact hc5.2.2)
    .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
  rintro s6 ⟨hR6, hS6⟩
  rw [WP.spec_ok]
  refine ⟨rfl, _, ?_, IpcRel.ofSRN hR6 hS6⟩
  unfold Fl4Spec.suspend
  rw [nd_bind_one hc1, nd_bind_one (getThreadState_eq hk1), nd_bind_one hw2, nd_bind_one he3, nd_bind_one he4,
    nd_bind_one he5, Notif.setThreadState_eq _ hk5]


end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- `RemoveTcbOK` from `JAtZ`. -/
theorem JAtZ.removeTcbOK {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : RemoveTcbOK st Z.N Z.T Z.C Z.E Z.R Z.c s σ :=
  ⟨Lst, J.call, J.rfree, J.rp, J.nsc, J.inv, J.c0, J.sv, J.obj⟩

set_option maxHeartbeats 4000000 in
/-- **Suspend from `JAtZ`** (`suspendXLeaf_of` re-scoped): the restart
(`xleaf_restartJ`), then `suspend_irelY` with `JAtZ`'s facts after the
restart: `SchedValid`, `ObjCover`, `Inv`, `YieldRel`, P1's `BlkOK` (its
TCBs `Z.T`, `JAtZ.tcbs_eq`), and `RemoveTcbOK` carried to the fault clear
(`removeTcbOK_fault`). Named: the target among the TCBs. -/
theorem suspendXLeafJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} {p : U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hJS : JStepHyps (L := L) arI AR Z.th)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) (hpT : p ∈ Z.T) :
    SuspendXLeaf (L := L) arI AR s ar σ σ1 p := by
  refine xleaf_restartJ J hJS hst fun s1 Ac' Lst' D' J' _ hI1 => ?_
  have hP0 := J.ip
  have hAR : AR ar σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  have hB := J'.blk
  rw [← J'.tcbs_eq.1] at hB
  refine WP.spec_bind (suspend_irelY (ar := arI) hP0 (removeTcbHypP_ok hP0) s1 ar σ1 hI1 hpT J'.sv J'.obj J'.inv
    (fun x hk => removeTcbOK_fault hP0 hI1 hpT hk J'.removeTcbOK) J'.yld hB) ?_
  rintro ⟨s2, a2⟩ ⟨rfl, σ2, hm, hI2⟩
  exact (WP.spec_ok _).2 ⟨rfl, hAR, ((), σ2), by rw [hm]; exact Set.mem_singleton _, hI2⟩

end

end

end Fl4Proofs.P3
