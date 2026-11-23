/-
P3 (DESIGN.md §9), untyped: **P1's creation of TCBs at `J`** (handoff/utj.md
"uttypes", ut39; l4v `retype_region` of `TCBObject`s; seL4 `tcbDebugAppend`).

* `dbgLinks_tcb`: P1's `DbgLinksOK` after a TCB retype from UtTcbLoopC's
  `TcbC` (each new TCB's `DEBUG_NEXT` the previous one or the old head, its
  `DEBUG_PREV` the next one or 0, the old head's `DEBUG_PREV` the first new
  TCB, core 0's head word the last new TCB) and the old links kept (every
  write misses them but the old head's `DEBUG_PREV` and core 0's head);
* `JAtZ.create_noresetTB`: UtBodyJ's `create_noresetB` (P1's creation from
  one `JAtZ` state) for TCBs (`n = 1`), with `dbgLinks_tcb` for
  `dbgLinks_nonTcb`;
* `JKern.keepH`: `JAtZ.kern_keep` from `JKern`, any typed heap, the new
  debug-list head given.
-/
import Fl4Proofs.P3.UtEpJ
import Fl4Proofs.P3.UtBodyJ
import Fl4Proofs.P3.UtTcbLoopC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **`DbgLinksOK` after a TCB retype** (module docstring). -/
theorem dbgLinks_tcb {H1 : Heap} {Cs : Set U64} {sR s' : S} {A w : Nat} {Pw : U64 → Prop} {d0 : U64}
    (hP : DropOK st H1 (RegionD H1 A (A + w * 4096)) Cs sR) (hTm : TimerOK st H1.tcbs Cs sR)
    (hW : WFrame (L := L) sR s' Pw)
    (hfr : ∀ v, Pw v → (∀ y ∈ H1.tcbs, ¬ RegionD H1 A (A + w * 4096) y →
        v ≠ dnA y ∧ (y ≠ L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS) → v ≠ dpA y)) ∧
      ∀ c ∈ Cs, c ≠ 0#u64 → v ≠ L.nodeAt sR c layout.node.DEBUG_TCBS)
    (hal : ∀ y ∈ H1.tcbs, P1.Aligned (dnA y) ∧ P1.Aligned (dpA y))
    (hnal : ∀ c ∈ Cs, P1.Aligned (L.nodeAt sR c layout.node.DEBUG_TCBS)) (h0Cs : 0#u64 ∈ Cs)
    (hC : TcbC (L.mem s') A (L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)) d0
      (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS) w)
    (hw1 : 1 ≤ w) (hfit : A + w * 4096 ≤ 2 ^ 64) :
    DbgLinksOK st H1 Cs s' A (A + w * 4096) A 4096 w 1 := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC
  have kept : ∀ x, Tz H1.tcbs x → KeptRef H1 (RegionD H1 A (A + w * 4096)) x →
      NewTcbRef H1 A (A + w * 4096) A 4096 w 1 x := by
    intro x hz hk
    rcases hz with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨hx, hk (by rw [show H1 x = some .tcb from hx]; simp)⟩)
  have newB : ∀ j, j < w → NewTcbRef H1 A (A + w * 4096) A 4096 w 1 (bT A j) :=
    fun j hj => Or.inr (Or.inr ⟨rfl, j, hj, bT_v hj hfit⟩)
  have hna : ∀ c, L.nodeAt s' c layout.node.DEBUG_TCBS = L.nodeAt sR c layout.node.DEBUG_TCBS := fun c => by
    simp [LawfulStore.nodeAt, hW.1]
  have h0ok : NewTcbRef H1 A (A + w * 4096) A 4096 w 1 (L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)) :=
    kept _ (hTm.dh _ h0Cs) (hP.node _ h0Cs).2.2
  refine ⟨fun y hy hy0 => ?_, fun c hc => ?_⟩
  · rcases hy with h0' | ⟨hyt, hyD⟩ | ⟨-, j, hj, hyv⟩
    · exact absurd h0' hy0
    · obtain ⟨-, -, -, k4, k5⟩ := hP.tl y hyt hyD
      have e4 : L.mem s' (dnA y) = L.mem sR (dnA y) :=
        hW.2.2 _ (hal y hyt).1 (fun h => ((hfr _ h).1 y hyt hyD).1 rfl)
      refine ⟨by rw [e4]; exact kept _ (hTm.dn y hyt) k4, ?_⟩
      by_cases hyh : y = L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)
      · rw [hyh, c6 (by omega) (hyh ▸ hy0)]; exact newB 0 (by omega)
      · rw [hW.2.2 _ (hal y hyt).2 (fun h => ((hfr _ h).1 y hyt hyD).2 hyh rfl)]
        exact kept _ (hTm.dp y hyt) k5
    · have hy : y = bT A j := UScalar.eq_of_val_eq (by rw [hyv, bT_v hj hfit])
      subst hy
      refine ⟨?_, ?_⟩
      · rw [c3 j hj]
        split_ifs with hj0
        · exact h0ok
        · exact newB (j - 1) (by omega)
      · by_cases hjl : j + 1 < w
        · rw [c4 j hjl]; exact newB (j + 1) hjl
        · rw [c5 j (by omega)]; exact Or.inl rfl
  · rw [hna]
    by_cases hc0 : c = 0#u64
    · subst hc0; rw [c7, if_neg (by omega)]; exact newB (w - 1) (by omega)
    · rw [hW.2.2 _ (hnal c hc) (fun h => (hfr _ h).2 c hc hc0 rfl)]
      exact kept _ (hTm.dh c hc) (hP.node c hc).2.2

/-- **`JKern` across a step, the debug-list head given after** (`JAtZ.kern_keep`
from `JKern` and the scheduler relation before, at any typed heap: the head
word of core 0 may change, e.g. to a new TCB). -/
theorem JKern.keepH {H : P1.Heap} {Cs D D' : Set U64} {th : TypedHeap} {N T C : Set U64} {c : U64}
    {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (K : JKern (L := L) H Cs D th s σ) (hS : Sched.SchedRel st N T C c s σ)
    (hks : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s)
    (hS' : Sched.SchedRel st N T C c s' σ')
    (hct : σ'.curThread = σ.curThread) (hcsc : σ'.curSc = σ.curSc)
    (horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot th sl)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hao : ∀ p ao, σ.kheap p = some (.archObj ao) → σ'.kheap p = some (.archObj ao))
    (hhead : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th (L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)))) :
    JKern (L := L) H Cs D' th s' σ' := by
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have ecw : L.curW s' = L.curW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curThread; have h2 := hs.curThread
    unfold P1.LawfulStore.curW
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hct]
  have ecs : L.cscW s' = L.cscW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curSc; have h2 := hs.curSc
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hcsc]
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  obtain ⟨pt, hpt⟩ := K.gpm
  refine ⟨fun sl h => (horig sl h).elim (K.orig sl) id, by rw [ecw, hct]; exact K.cur,
    by rw [ecw]; exact K.curT, by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
    by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu, ecw]; exact K.dwNe, by rw [hna]; exact hhead,
    ⟨pt, by rw [hgp]; exact hao _ _ hpt⟩, by rw [hgp]; exact K.ga, by rw [hgp]; exact K.gf,
    K.heap, K.h0, by rw [hks]; exact K.hks, by rw [hks]; exact K.hksIn, fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
    by rw [hks]; exact K.ksbFit, by rw [hks]; exact K.ksbAl, by rw [hks, hcpu]; exact K.nodeFit,
    by rw [hcpu]; exact K.cpuCs, by rw [ecw]; exact K.curH, by rw [ecs]; exact K.cscH,
    K.csLt, K.cs0⟩


set_option maxHeartbeats 4000000 in
/-- **`JAtZ.create_noresetB` for TCBs** (`n = 1`, `dbgLinks_tcb`). As `create_noresetB`: **`JAtZ.create_noresetW` from one `JAtZ` state**: the creation starts at
the `JAtZ` state itself (after the restart, or after a reset), entered
(`Entered`: no switch pending, the current thread runnable); the kept objects'
and FL4's lists' references to the window's objects are the premise `hRU` at
that state (`RegionUnrefJ`'s conclusion there; no restart in between). -/
theorem JAtZ.create_noresetTB {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs)
    {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {s' : S} {th' : TypedHeap} {G' : MdbGhost} {A0 k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
    (hE : RetExp Z.th th' (L.mem s) (L.mem s') Z.G G' A0 k w dslot cj (cslotAddr (pp.bv, idx)))
    (hRU : KeptRefsP3 (L := L) H (RegionD H A0 (A0 + w * k)) s ∧ DbgTimerKept (L := L) H (RegionD H A0 (A0 + w * k)) Cs s)
    {n us : Nat} (hcjU : newKind n us ≠ none → ∀ j, j < w → isUt (cj j) = false)
    (hn1 : n = 1) (hk : k = 4096) (hAk : A0 % k = 0)
    {T pml4 : Prop} (hT : T) (hP4 : ¬ pml4)
    (hW : WFrame (L := L) s s' (fun v => ((T ∧ TcbLoopW Z.th A0 w (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)
      (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) v) ∨ SlotSpan Z.th v) ∨
      (pml4 ∧ A0 ≤ v.val ∧ v.val < A0 + w * k)))
    (hWZ : WinZero (L.mem s') A0 k w T) {d0 : U64}
    (hC : TcbC (L.mem s') A0 (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) d0
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) w) (hw1 : 1 ≤ w) (hidl : IdleKeep (L := L) s s') :
    ∃ (H' : Heap) (Ac' : Set U64),
      BlkOK st (Heap.tcbs H') Cs (Heap.omega H') H' (Heap.frame H') (Heap.replies H') (Heap.scs H')
        (Heap.ntfns H') (Heap.scBits H') Ac' s' ∧
      HOut H H' A0 (A0 + w * k) A0 k w (newKind n us) ∧
      JCovD (L := L) th' H' G' {q | q ∈ D ∧ ¬ NewQ A0 k w cj q} Cs s' := by
  let ex : Aeneas.Std.Array obj.Slot 3#usize := Aeneas.Std.Array.repeat 3#usize 0#u64
  have hres : σ.schedulerAction ≠ .chooseNewThread := by rw [hni.2]; simp
  have UJ := J.utJoint (extra := ex) hres hpp hidx rfl hcap (by
    intro x hx h0; exfalso; apply h0; simpa [ex, Aeneas.Std.Array.repeat, List.mem_replicate] using hx)
  have hfr : Frame2 (L := L) s s (stA (L.curW s)) (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
    fun _ _ _ _ => rfl
  obtain ⟨hP, ⟨-, -, hM, -, hI⟩, -⟩ := J.xtop.rel
  have hS := J.xtop.fin.1.1.1
  have hact : ∀ y ∈ H.tcbs, L.actionW s ≠ y := fun y hy =>
    actionW_ne_of hS (by rw [J.tcbs_eq.1]; exact hy) (fun e => by rw [hni.2] at e; cases e)
  obtain ⟨-, x, hkx, hrx⟩ := J.curRunnable hni (cur_thread_eq s)
  have hcT : L.curW s ∈ Z.T := by rw [J.tcbs_eq.1]; exact J.kern.curH
  have hrun : Runnable (L.mem s (stA (L.curW s))) := by
    show Runnable (L.mem s (P1.stA (L.curW s))); rw [stA_tStA]; exact (runnable_iff (J.xtop.fin.1.1.2.2.1.at_tcb hcT hkx).st).2 hrx
  -- the window, in the source's free part
  have hcv := capV_of_capAt hcap
  obtain ⟨hxG, p1, sb1, fi0', fi1, d1, e0, -, hpA, -, hAs, -, -⟩ := hE.usrc
  rw [hcv] at e0
  simp only [capability.Cap.Untyped.injEq] at e0
  obtain ⟨hp1, hsb1, hfi1, -⟩ := e0
  subst p1 sb1 fi0'
  have hAs' : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have U := J.utc _ p sb fi false hAs' hcap rfl
  obtain ⟨hk1', hk2, -⟩ := J.jcov.ks _ hxG p sb fi hcv
  have hk1 : 1 ≤ k := hE.k1
  have hfitW : A0 + w * k ≤ 2 ^ 64 := le_trans hAs U.pfit
  have hpos : 0 < A0 := by
    have := U.high (notDev_ram hcv); omega
  have RD : ∀ q kd, H q = some kd → RegionD H A0 (A0 + w * k) q → q ∈ D ∧ DeadP (L := L) H s q := by
    intro q kd hq hr
    refine (retype_window_dead J.jcov J.ut hI hE ⟨p, sb, fi, hcv⟩).1 q kd hq ?_
    unfold RegionD at hr; rw [hq] at hr; simp only [Option.elim] at hr
    unfold MeetsR at hr; unfold MeetsW; omega
  have hreg : A0 + w * k ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ A0 := by rcases hk1' with h | h <;> omega
  obtain ⟨hKR, hDT⟩ := hRU
  have hdrop := dead_dropOK UJ RD hfr rfl rfl rfl rfl hact hrun hKR hDT hreg
  have hRON : RegionOffNodes st Cs s A0 (A0 + w * k) := by
    refine ⟨fun c hc => ?_, ?_⟩
    · rcases hk2 c hc with h | h <;> omega
    · rcases hk1' with h | h <;> omega
  have hb1 := J.blk
  have hTm : TimerOK st H.tcbs Cs s := hb1.2.2.1.2.2.tm
  obtain ⟨Tr, Cq, hJP⟩ := J.jpl
  have hSC : SlotCapW Z.th H.tcbs H.omega H.frame := slotCapW_of_in hP J.kern.heap (fun a ha => hJP.slot_in ha)
  have hsoff : ∀ v, SlotSpan Z.th v → (∀ y, H y = some .tcb → v ≠ dnA y ∧ v ≠ dpA y) ∧
      (∀ c ∈ Cs, v.val < L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ v.val) := fun v hv => by
    obtain ⟨o1, o2⟩ := slot_word_off hJP J.kern.hnd hv
    exact ⟨o1, fun c hc => o2 c hc⟩
  have hh0T : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ≠ 0#u64 →
      H (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb :=
    fun hne => (hTm.dh _ J.kern.cs0).resolve_left hne
  have h88 : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
  have h88v : layout.node.DEBUG_TCBS.val = 88 := by simp [layout.node.DEBUG_TCBS]
  have hdv : ∀ c ∈ Cs, (L.nodeAt s c layout.node.DEBUG_TCBS).val = L.nodeBase s c + 88 := fun c hc => by
    rw [nodeAt_val (hTm.npl c hc) h88, h88v]
  have hwin : ∀ v : U64, A0 ≤ v.val → v.val < A0 + w * k →
      (∀ y ∈ H.tcbs, ¬ RegionD H A0 (A0 + w * k) y → v ≠ dnA y ∧ v ≠ dpA y) ∧
      ∀ c ∈ Cs, v ≠ L.nodeAt s c layout.node.DEBUG_TCBS := by
    intro v hv1 hv2
    refine ⟨fun y hy hyD => ?_, fun c hc e => ?_⟩
    · have hy' : H y = some .tcb := hy
      have hdn : (dnA y).val = y.val + 3576 := tcb_word J.kern.heap hy (by simp)
      have hdp : (dpA y).val = y.val + 3584 := tcb_word J.kern.heap hy (by simp)
      refine ⟨fun e => hyD ?_, fun e => hyD ?_⟩ <;>
        (unfold RegionD MeetsR; rw [hy']; simp only [Option.elim, HKind.bits, Nat.reducePow]; subst e; omega)
    · have hc2 := hk2 c hc
      have := hdv c hc
      subst e
      rw [this] at hv1 hv2
      rcases hc2 with h | h <;> omega
  have hdbg : DbgLinksOK st H Cs s' A0 (A0 + w * k) A0 k w n := by
    subst hk hn1
    refine dbgLinks_tcb hdrop hTm hW (fun v hv => ?_) (fun y hy => ?_) (fun c hc => ?_) J.kern.cs0 hC hw1 hfitW
    · have slotCase : SlotSpan Z.th v → (∀ y ∈ H.tcbs, ¬ RegionD H A0 (A0 + w * 4096) y →
          v ≠ dnA y ∧ (y ≠ L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) → v ≠ dpA y)) ∧
          ∀ c ∈ Cs, c ≠ 0#u64 → v ≠ L.nodeAt s c layout.node.DEBUG_TCBS := fun hsl => by
        obtain ⟨o1, o2⟩ := hsoff v hsl
        refine ⟨fun y hy _ => ⟨(o1 y hy).1, fun _ => (o1 y hy).2⟩, fun c hc _ e => ?_⟩
        have := o2 c hc
        rw [e, hdv c hc] at this
        omega
      rcases hv with (⟨-, hv⟩ | hsl) | ⟨hp4, -⟩
      · rcases hv with hsl | ⟨j, hj, hin⟩ | rfl | ⟨hne, hvv⟩
        · exact slotCase hsl
        · have hjv := bT_v hj hfitW
          obtain ⟨i1, i2, -⟩ := hin
          have hjk : (j + 1) * 4096 ≤ w * 4096 := Nat.mul_le_mul_right _ hj
          rw [Nat.add_mul, Nat.one_mul] at hjk
          have hw' := hwin v (by unfold bT at hjv; rw [hjv] at i1; omega) (by unfold bT at hjv; rw [hjv] at i2; omega)
          exact ⟨fun y hy hyD => ⟨(hw'.1 y hy hyD).1, fun _ => (hw'.1 y hy hyD).2⟩, fun c hc _ => hw'.2 c hc⟩
        · refine ⟨fun y hy _ => ⟨fun e => ?_, fun _ e => ?_⟩, fun c hc hc0 e => ?_⟩
          · have hdn : (dnA y).val = y.val + 3576 := tcb_word J.kern.heap hy (by simp)
            have := J.kern.hnd y .tcb hy 0#u64 J.kern.cs0
            have hd0 := hdv 0#u64 J.kern.cs0
            have e' := congrArg UScalar.val e
            simp only [HKind.bits, Nat.reducePow] at this
            rw [hd0, hdn] at e'; omega
          · have hdp : (dpA y).val = y.val + 3584 := tcb_word J.kern.heap hy (by simp)
            have := J.kern.hnd y .tcb hy 0#u64 J.kern.cs0
            have hd0 := hdv 0#u64 J.kern.cs0
            have e' := congrArg UScalar.val e
            simp only [HKind.bits, Nat.reducePow] at this
            rw [hd0, hdp] at e'; omega
          · have e' := congrArg UScalar.val e
            rw [hdv 0#u64 J.kern.cs0, hdv c hc] at e'
            simp only [P1.LawfulStore.nodeBase] at e'
            exact hc0 (UScalar.eq_of_val_eq (by simp at e' ⊢; omega))
        · have hh0 := hh0T hne
          refine ⟨fun y hy _ => ⟨fun e => ?_, fun hyh e => ?_⟩, fun c hc _ e => ?_⟩
          · have hdn : (dnA y).val = y.val + 3576 := tcb_word J.kern.heap hy (by simp)
            have e' := congrArg UScalar.val e
            rw [hdn] at e'
            by_cases hyq : y = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)
            · rw [← hyq] at hvv; omega
            · have hd := J.kern.heap.disj y .tcb _ .tcb hy hh0 hyq
              simp only [HKind.bits, Nat.reducePow] at hd; omega
          · have hdp : (dpA y).val = y.val + 3584 := tcb_word J.kern.heap hy (by simp)
            have e' := congrArg UScalar.val e
            rw [hdp] at e'
            have hd := J.kern.heap.disj y .tcb _ .tcb hy hh0 hyh
            simp only [HKind.bits, Nat.reducePow] at hd; omega
          · have e' := congrArg UScalar.val e
            rw [hdv c hc] at e'
            have := J.kern.hnd _ .tcb hh0 c hc
            simp only [HKind.bits, Nat.reducePow] at this; omega
      · exact slotCase hsl
      · exact absurd hp4 hP4
    · have hal := J.kern.heap.align y .tcb hy
      simp only [HKind.bits] at hal
      have hdn : (dnA y).val = y.val + 3576 := tcb_word J.kern.heap hy (by simp)
      have hdp : (dpA y).val = y.val + 3584 := tcb_word J.kern.heap hy (by simp)
      unfold P1.Aligned
      rw [hdn, hdp]; omega
    · exact nodeAt_aligned (hTm.npl c hc) (by simp [layout.node.DEBUG_TCBS]) (by simp [layout.node.DEBUG_TCBS])
  have hkd : ∀ kd, newKind n us = some kd → 2 ^ kd.bits = k := fun kd h => by rw [newKind_bits h, hk, hn1]; simp [zOf]
  have hwp : WinPlaced A0 k w n us := by
    refine ⟨fun kd h => ?_, hfitW, hpos, fun h => by omega⟩
    rw [hkd kd h]
    exact ⟨hAk, Nat.mod_self _⟩
  have hh0 : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ≠ 0#u64 →
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ∈ Heap.tcbs H :=
    fun hne => (hTm.dh _ J.kern.cs0).resolve_left hne
  obtain ⟨H', Ac', hb', hkeep, hshape, hnew, hdead'⟩ := creation_step (n := n) (us := us) hb1
    (fun kd h => (hkd kd h).le) hdrop hRON hdbg hwp hW hP hSC J.kern.cs0 hh0 (fun _ => hk) hfitW
    (fun _ _ w0 hw0 h1 h2 => (hWZ w0 hw0 h1 h2).imp_right fun h => ⟨hn1, h.2⟩) (fun _ => hk)
  have hout : HOut H H' A0 (A0 + w * k) A0 k w (newKind n us) :=
    hOut_of_steps hk1 le_rfl le_rfl (Or.inl ⟨rfl, rfl, rfl⟩) hkeep hshape hnew
  have hdk : ∀ q kd, H q = some kd → DeadP (L := L) H s q → DeadQ st H s q := fun q kd hq hd =>
    deadQ_keep J.kern.heap hq hd (fun _ _ _ _ => rfl) rfl (fun hqt e => hact q hqt e.symm)
  have hnewQ : ∀ q, NewAt A0 k w q → newKind n us ≠ none → NewQ A0 k w cj q := by
    rintro q ⟨j, hj, hq⟩ hK
    exact ⟨j, hj, hq, hcjU hK j hj⟩
  -- jc6e: a dead TCB that is no new TCB is off the window (TCB-aligned); the TCB loop writes
  -- neither its `DEBUG_PREV` nor its deadline word, and core 0's head after is the last new TCB
  have hfit4 : A0 + w * 4096 ≤ 2 ^ 64 := by rw [← hk]; exact hfitW
  have hA4 : A0 % 4096 = 0 := by rw [← hk]; exact hAk
  have hK1 : newKind n us ≠ none := by rw [hn1]; simp [newKind]
  have hdxT : ∀ q ∈ D, ¬ NewQ A0 k w cj q → Sched.DeadX (L := L) H Cs s q → Sched.DeadX (L := L) H Cs s' q := by
    intro q _ hnq hd
    refine deadX_of_frame J.kern.heap hW (fun hq v hv => ?_) (fun hq c hc => ?_)
      (fun c hc => nodeAt_aligned (hTm.npl c hc) (by simp [layout.node.DEBUG_TCBS]) (by simp [layout.node.DEBUG_TCBS]))
      hd
    · have hal := J.kern.heap.align q .tcb hq
      simp only [HKind.bits] at hal
      have hdp : (P1.dpA q).val = q.val + 3584 := tcb_word J.kern.heap hq (by simp)
      have htd : (P1.tdA q).val = q.val + 3528 := tcb_word J.kern.heap hq (by simp)
      have slotC : SlotSpan Z.th v → v ≠ P1.dpA q ∧ v ≠ P1.tdA q := fun hsl =>
        ⟨((hsoff v hsl).1 q hq).2, slot_word_ne_tw hJP hsl hq (K := 3528#u64) (by simp) (by simp)⟩
      rcases hv with (⟨-, hv⟩ | hsl) | ⟨hp4, -⟩
      · rcases hv with hsl | ⟨j, hj, hin⟩ | rfl | ⟨hne, hvv⟩
        · exact slotC hsl
        · have hjv := bT_v hj hfit4
          obtain ⟨i1, i2, -⟩ := hin
          unfold bT at hjv
          rw [hjv] at i1 i2
          refine ⟨fun e' => hnq ⟨j, hj, ?_, hcjU hK1 j hj⟩, fun e' => hnq ⟨j, hj, ?_, hcjU hK1 j hj⟩⟩
          · rw [e', hdp] at i1 i2; rw [hk]; omega
          · rw [e', htd] at i1 i2; rw [hk]; omega
        · have := J.kern.hnd q .tcb hq 0#u64 J.kern.cs0
          have hd0 := hdv 0#u64 J.kern.cs0
          simp only [HKind.bits, Nat.reducePow] at this
          refine ⟨fun e' => ?_, fun e' => ?_⟩
          · have e'' := congrArg UScalar.val e'
            rw [hd0, hdp] at e''; omega
          · have e'' := congrArg UScalar.val e'
            rw [hd0, htd] at e''; omega
        · have hh0 := hh0T hne
          have hal0 := J.kern.heap.align _ .tcb hh0
          simp only [HKind.bits] at hal0
          refine ⟨fun e' => (hd hq).2.1 0#u64 J.kern.cs0 (UScalar.eq_of_val_eq ?_), fun e' => ?_⟩
          · have e'' := congrArg UScalar.val e'
            rw [hdp] at e''; omega
          · have e'' := congrArg UScalar.val e'
            rw [htd] at e''; omega
      · exact slotC hsl
      · exact absurd hp4 hP4
    · by_cases hc0 : c = 0#u64
      · right
        subst hc0
        obtain ⟨-, -, -, -, -, -, c7⟩ := hC
        rw [c7, if_neg (show ¬ w = 0 by omega)]
        intro e'
        apply hnq
        refine ⟨w - 1, by omega, ?_, hcjU hK1 (w - 1) (by omega)⟩
        have hb := bT_v (A := A0) (j := w - 1) (win := w) (by omega) hfit4
        rw [e'] at hb
        rw [hb, hk]
      · left
        intro v hv e'
        subst e'
        rcases hv with (⟨-, hv⟩ | hsl) | ⟨hp4, -⟩
        · rcases hv with hsl | ⟨j, hj, hin⟩ | e0 | ⟨hne, hvv⟩
          · have := (hsoff _ hsl).2 c hc
            rw [hdv c hc] at this
            omega
          · have hjv := bT_v hj hfit4
            obtain ⟨i1, i2, -⟩ := hin
            have hjk : (j + 1) * 4096 ≤ w * 4096 := Nat.mul_le_mul_right _ hj
            rw [Nat.add_mul, Nat.one_mul] at hjk
            unfold bT at hjv
            rw [hjv] at i1 i2
            exact (hwin (L.nodeAt s c layout.node.DEBUG_TCBS) (by omega) (by rw [hk]; omega)).2 c hc rfl
          · have e'' := congrArg UScalar.val e0
            rw [hdv 0#u64 J.kern.cs0, hdv c hc] at e''
            simp only [P1.LawfulStore.nodeBase] at e''
            exact hc0 (UScalar.eq_of_val_eq (by simp at e'' ⊢; omega))
          · rw [hdv c hc] at hvv
            have := J.kern.hnd _ .tcb (hh0T hne) c hc
            simp only [HKind.bits, Nat.reducePow] at this; omega
        · have := (hsoff _ hsl).2 c hc
          rw [hdv c hc] at this
          omega
        · exact absurd hp4 hP4
  have hdx' : ∀ q ∈ D, ¬ NewQ A0 k w cj q → H' q = H q → Sched.DeadX (L := L) H Cs s q →
      Sched.DeadX (L := L) H Cs s' q := fun q hq hn _ hd => hdxT q hq hn hd
  refine ⟨H', Ac', hb', hout, J.jcov.retype hE (fun q kd hq => ?_) (fun q hqD hnq e hd => ?_) hW.1
    hidl hdx' ⟨p, sb, fi, hcv⟩⟩
  · rcases hshape q kd hq with ⟨h1, hm⟩ | ⟨hna', hk'⟩
    · refine Or.inl ⟨h1, ?_⟩
      rintro ⟨j, hj, hv, -⟩
      apply hm
      unfold MeetsR
      have h1' : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
      rw [Nat.add_mul, Nat.one_mul] at h1'
      have := Nat.one_le_two_pow (n := kd.bits)
      omega
    · exact Or.inr ⟨hnewQ q hna' (by rw [hk']; simp), (hkd kd hk').le⟩
  · cases hHq : H q with
    | none => exact DeadP.none (e.trans hHq)
    | some kd =>
      have hq' : H' q = some kd := e.trans hHq
      rcases hshape q kd hq' with ⟨h1, -⟩ | ⟨hna', hk''⟩
      · exact hdead' q (hq'.trans h1.symm) (hdk q kd hHq hd)
      · exact absurd (hnewQ q hna' (by rw [hk'']; simp)) hnq

end

end

end Fl4Proofs.P3
