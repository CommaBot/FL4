/-
P3 (DESIGN.md §9), untyped: **`JRest`'s scheduler-side fields across a
retype of TCBs** (handoff/utj.md "uttypes", ut39; l4v `retype_region` of
`TCBObject`s, `default_tcb`).

* `inSlotTW_keeps`: UtPmKeep's `inSlotW_keeps` with the extra write words
  `Win` allowed in a TCB of `T` at its `DEBUG_PREV` word (offset 3584: the
  old debug-list head's back link), which is no MCP, yield or buffer word;
* `JAtZ.uaRestT`: `JAtZ.uaRestW` with UtTcbSpec's `IdleNewT` (default TCBs
  among the new objects) and `inSlotTW_keeps`, at the old sets;
* the fields over the new TCBs `W` (`default_tcb`, their words zero):
  `Sched.YieldRel.addT`, `Sched.McpRel.addT`, `Endp.BufWordRel.addT`,
  `Sched.CurOwnW.monoT`, `Sched.RPlaced.addT`, `Sched.SlotsApart.addT`.
-/
import Fl4Proofs.P3.UtTcbSpec
import Fl4Proofs.P3.UtPmKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
  Fl4Proofs.P1

noncomputable section

/-! ## The fields over the new TCBs -/

section New
variable {σ : Fl4Spec.State Unit} {T C W : Set U64} {m : U64 → U64}

theorem Sched.YieldRel.addT (h : Sched.YieldRel T C m σ)
    (hk : ∀ t ∈ W, ∃ d, σ.kheap t.bv = some (.tcb (Fl4Spec.defaultTcb d)))
    (hy : ∀ t ∈ W, m (P1.yieldA t) = 0#u64) : Sched.YieldRel (T ∪ W) C m σ := by
  refine ⟨fun t ht => ?_, fun t ht h0 => ?_, fun sc hsc y n hy' p hp => ?_⟩
  · rcases ht with ht | ht
    · exact h.tcb t ht
    · obtain ⟨d, hd⟩ := hk t ht
      exact ⟨_, hd, by rw [hy t ht, optRef_zero]; rfl⟩
  · rcases ht with ht | ht
    · exact h.toSc t ht h0
    · exact absurd (hy t ht) h0
  · obtain ⟨t, ht, e1, e2⟩ := h.frm sc hsc y n hy' p hp
    exact ⟨t, Or.inl ht, e1, e2⟩

theorem Sched.McpRel.addT (h : Sched.McpRel T m σ)
    (hk : ∀ t ∈ W, ∃ d, σ.kheap t.bv = some (.tcb (Fl4Spec.defaultTcb d)))
    (hy : ∀ t ∈ W, m (Sched.mcpA t) = 0#u64 ∧ m (Sched.flagsA t) = 0#u64) : Sched.McpRel (T ∪ W) m σ := by
  intro t ht
  rcases ht with ht | ht
  · exact h t ht
  · obtain ⟨d, hd⟩ := hk t ht
    exact ⟨_, hd, by rw [(hy t ht).1]; rfl, by rw [(hy t ht).2]; exact Sched.w2f_zero⟩

theorem Endp.BufWordRel.addT (h : Endp.BufWordRel T m σ)
    (hk : ∀ t ∈ W, ∃ d, σ.kheap t.bv = some (.tcb (Fl4Spec.defaultTcb d)))
    (hy : ∀ t ∈ W, m (Endp.tIpcBufA t) = 0#u64) : Endp.BufWordRel (T ∪ W) m σ := by
  intro t ht
  rcases ht with ht | ht
  · exact h t ht
  · obtain ⟨d, hd⟩ := hk t ht
    exact ⟨_, hd, by rw [hy t ht]; rfl⟩

theorem Sched.CurOwnW.monoT (h : Sched.CurOwnW T C σ) : Sched.CurOwnW (T ∪ W) C σ := by
  rcases h with ⟨u, hu, rest⟩ | h
  · exact Or.inl ⟨u, Or.inl hu, rest⟩
  · exact Or.inr h

end New

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

theorem Sched.RPlaced.addT {N T C R W : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (h : Sched.RPlaced st N T C R c s σ) (hW : ∀ r ∈ R, ∀ t ∈ W, r.val + 32 ≤ t.val ∨ t.val + 4096 ≤ r.val) :
    Sched.RPlaced st N (T ∪ W) C R c s σ :=
  ⟨h.align, h.ksb, fun r hr t ht => ht.elim (h.tcb r hr t) (hW r hr t), h.ntfn, h.sc⟩

theorem Sched.SlotsApart.addT {th : TypedHeap} {N T C R W : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (h : Sched.SlotsApart (st := st) th T N C R c s σ)
    (hW : ∀ a, IsSlot th a → ∀ t ∈ W, a.val + 32 ≤ t.val + 256 ∨ t.val + 4096 ≤ a.val) :
    Sched.SlotsApart (st := st) th (T ∪ W) N C R c s σ := fun a ha => by
  obtain ⟨h1, h2⟩ := h a ha
  exact ⟨fun t ht => ht.elim (h1 t) (hW a ha t), h2⟩

/-- `inSlotTW_keeps` over `JAtZB` (mmuAD gen 42b25, in place; `inSlotTW_keeps` is its corollary). -/
theorem inSlotTW_keepsB {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {Win : U64 → Prop}
    (hw : P1.WritesIn st s s' (fun b => InSlot Z.th b ∨ Win b))
    (hWT : ∀ b, Win b → ∀ t ∈ Z.T, b.val < t.val ∨ t.val + 4096 ≤ b.val ∨ b.val = t.val + 3584)
    (hWC : ∀ b, Win b → ∀ q ∈ Z.C, ∀ x n, σ.kheap q.bv = some (.schedContext x n) →
      b.val < q.val ∨ q.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ b.val)
    (hWR : ∀ b, Win b → ∀ r ∈ Z.R, b.val < r.val ∨ r.val + 32 ≤ b.val) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t) ∧ L.mem s' (flagsA t) = L.mem s (flagsA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hT := hc.tcbs
  have hA := J.apart
  have kw : ∀ b : U64, P1.Aligned b → (∀ x, IsSlot Z.th x → b.val < x.val ∨ x.val + 32 ≤ b.val) → ¬ Win b →
      L.mem s' b = L.mem s b := fun b hb hs hn =>
    hw.mem_eq hb fun h => h.elim (fun ⟨x, hx, h1, h2⟩ => by rcases hs x hx with e | e <;> omega) hn
  have tw : ∀ t ∈ Z.T, ∀ b : U64, P1.Aligned b → t.val + 256 ≤ b.val → b.val < t.val + 4096 →
      b.val ≠ t.val + 3584 → L.mem s' b = L.mem s b :=
    fun t ht b hb h1 h2 h3 => kw b hb (fun x hx => by rcases (hA x hx).1 t ht with h | h <;> omega)
      (fun h => by rcases hWT b h t ht with e | e | e <;> omega)
  refine ⟨fun t ht => ⟨tw t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega)
      (by rw [mcpA_val hT ht]; omega),
      tw t ht _ (flagsA_aligned hT ht) (by rw [flagsA_val hT ht]; omega) (by rw [flagsA_val hT ht]; omega)
      (by rw [flagsA_val hT ht]; omega)⟩,
    fun t ht => tw t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega)
      (by rw [yieldA_val hT ht]; omega),
    fun t ht => tw t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega) (by rw [tIpcBufA_val (hT t ht)]; omega), fun q hq => ?_, fun r hr => ?_⟩
  · obtain ⟨hal, hv, hfit⟩ := sc_reply_word hS hq
    obtain ⟨x, n, hk, -⟩ := (hS.lists.choose_spec.choose_spec.2).scs q hq
    have hf := hfit x n hk
    exact kw _ hal (fun y hy => by rcases (hA y hy).2.2.2.1 q hq x n hk with h | h <;> omega)
      (fun h => by rcases hWC _ h q hq x n hk with e | e <;> omega)
  · have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    refine ⟨kw _ (J.rp.aligned hr (Or.inl h8)) (fun y hy => ?_) (fun h => ?_),
      kw _ (J.rp.aligned hr (Or.inr h16)) (fun y hy => ?_) (fun h => ?_)⟩
    · rcases (hA y hy).2.2.2.2 r hr with h | h <;> omega
    · rcases hWR _ h r hr with e | e <;> omega
    · rcases (hA y hy).2.2.2.2 r hr with h | h <;> omega
    · rcases hWR _ h r hr with e | e <;> omega

/-- **`inSlotW_keeps` with a TCB's `DEBUG_PREV` word among the writes**. -/
theorem inSlotTW_keeps {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {Win : U64 → Prop}
    (hw : P1.WritesIn st s s' (fun b => InSlot Z.th b ∨ Win b))
    (hWT : ∀ b, Win b → ∀ t ∈ Z.T, b.val < t.val ∨ t.val + 4096 ≤ b.val ∨ b.val = t.val + 3584)
    (hWC : ∀ b, Win b → ∀ q ∈ Z.C, ∀ x n, σ.kheap q.bv = some (.schedContext x n) →
      b.val < q.val ∨ q.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ b.val)
    (hWR : ∀ b, Win b → ∀ r ∈ Z.R, b.val < r.val ∨ r.val + 32 ≤ b.val) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t) ∧ L.mem s' (flagsA t) = L.mem s (flagsA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) :=
  inSlotTW_keepsB J.toB hw hWT hWC hWR


set_option maxHeartbeats 2000000 in
/-- `uaRestT` over `JAtZB` (mmuAD gen 42b25, in place; `JAtZ.uaRestT` is its corollary). -/
theorem JAtZB.uaRestT {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {Win : U64 → Prop}
    (hw : P1.WritesIn st s s' (fun b => InSlot Z.th b ∨ Win b))
    (hWT : ∀ b, Win b → ∀ t ∈ Z.T, b.val < t.val ∨ t.val + 4096 ≤ b.val ∨ b.val = t.val + 3584)
    (hWC : ∀ b, Win b → ∀ q ∈ Z.C, ∀ x n, σ.kheap q.bv = some (.schedContext x n) →
      b.val < q.val ∨ q.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ b.val)
    (hWR : ∀ b, Win b → ∀ r ∈ Z.R, b.val < r.val ∨ r.val + 32 ≤ b.val)
    {σB σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop} {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject}
    (hA : SpecAdd σ σB W o) (hi : IdleNewT W o) (hcn : CnK σB σ') {Nn : Set U64} (hWn : ∀ n ∈ Nn, W n.bv)
    (hcW : ¬ W σ.curThread) :
    CallRel (L.mem s') Z.R Z.C σ' Lst ∧ RPlaced st Z.N Z.T Z.C Z.R Z.c s' σ' ∧ RFree (L.mem s') Z.R Z.C σ' Lst ∧
    RRecv (L.mem s') Z.R σ' ∧ YieldRel Z.T Z.C (L.mem s') σ' ∧ McpRel Z.T (L.mem s') σ' ∧
    BufWordRel Z.T (L.mem s') σ' ∧ NSC (Z.N ∪ Nn) Z.C σ' ∧ Inv σ' ∧
    (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ CurOwnW Z.T Z.C σ' ∧ OffOK σ' ∧ ActIdle σ' ∧
    BlockedScActive σ' ∧ IpcSorted σ' ∧ CurRunM σ' := by
  have hC := CnStep.of_cnK hcn
  obtain ⟨k1, k2, kb, k3, k4⟩ := inSlotTW_keepsB J hw hWT hWC hWR
  have ck := uaCKeepT hA hi hC
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hw.1 ck
  refine ⟨hCR', hRP', RFree.carry J.rfree J.call k4 ck, J.rrecv.uaddT hA hi hC k4,
    J.yld.frame k2 (uaYKeepT hA hi hC), J.mcp.frame k1 (uaMcpKeepT hA hC), J.buf.frame kb (uaBufKeepT hA hC),
    (J.nsc.uaddT hA hi hWn).cn hC.toHStep, (Inv.add J.inv hA hi.fresh).cn hC,
    CurInvW.cn (CurInvW.uaddT J.cur hA hi) hC, (J.own.uaddT hA hi).cn hC.toHStep, (J.off.uaddT hA hi).cn hC.toHStep,
    (J.act.uaddT hA hi).cn hC, (BlockedScActive.add J.bsa hA hi.fresh).cn hC.toHStep,
    (J.isorted.uaddT hA hi).cn hC.toHStep, (J.curRun.uaddT hA hi hcW).cn hC.toHStep (Or.inr hC.act)⟩


/-- **`JAtZ.uaRestW` for a retype's fresh objects with default TCBs**
(module docstring), at the old sets; the current thread not a new object. -/
theorem JAtZ.uaRestT {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {Win : U64 → Prop}
    (hw : P1.WritesIn st s s' (fun b => InSlot Z.th b ∨ Win b))
    (hWT : ∀ b, Win b → ∀ t ∈ Z.T, b.val < t.val ∨ t.val + 4096 ≤ b.val ∨ b.val = t.val + 3584)
    (hWC : ∀ b, Win b → ∀ q ∈ Z.C, ∀ x n, σ.kheap q.bv = some (.schedContext x n) →
      b.val < q.val ∨ q.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ b.val)
    (hWR : ∀ b, Win b → ∀ r ∈ Z.R, b.val < r.val ∨ r.val + 32 ≤ b.val)
    {σB σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop} {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject}
    (hA : SpecAdd σ σB W o) (hi : IdleNewT W o) (hcn : CnK σB σ') {Nn : Set U64} (hWn : ∀ n ∈ Nn, W n.bv)
    (hcW : ¬ W σ.curThread) :
    CallRel (L.mem s') Z.R Z.C σ' Lst ∧ RPlaced st Z.N Z.T Z.C Z.R Z.c s' σ' ∧ RFree (L.mem s') Z.R Z.C σ' Lst ∧
    RRecv (L.mem s') Z.R σ' ∧ YieldRel Z.T Z.C (L.mem s') σ' ∧ McpRel Z.T (L.mem s') σ' ∧
    BufWordRel Z.T (L.mem s') σ' ∧ NSC (Z.N ∪ Nn) Z.C σ' ∧ Inv σ' ∧
    (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ CurOwnW Z.T Z.C σ' ∧ OffOK σ' ∧ ActIdle σ' ∧
    BlockedScActive σ' ∧ IpcSorted σ' ∧ CurRunM σ' :=
  JAtZB.uaRestT J.toB hw hWT hWC hWR hA hi hcn hWn hcW

end

end

end Fl4Proofs.P3
