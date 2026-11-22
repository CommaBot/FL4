/-
P3 (DESIGN.md §9), TCB: **the debug-list words keep `XTopAt`**
(`XTopAt.dbgStep`): FL4's debug list (the TCBs' `DEBUG_NEXT`/`DEBUG_PREV`
words, offsets 3576 and 3584, and the core's `DEBUG_TCBS` node word, offset
88) is read by no relation of `XTopAt` and is not in the spec: writes to
those words keep `XTopAt` at the same spec state. As `XTopAt.tmStep`, with
`SAgree` leaving the node's `DEBUG_TCBS` word out.
-/
import Fl4Proofs.P3.XTopTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Ipc Fl4Proofs.P3.Endp

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- The debug-list words on core `c`: the TCBs' debug links and the node's
`DEBUG_TCBS` word. -/
def DbgWc (T : Set U64) (c : U64) (s : S) (b : U64) : Prop :=
  (∃ y ∈ T, b = P1.dnA y ∨ b = P1.dpA y) ∨ b = L.nodeAt s c layout.node.DEBUG_TCBS

set_option maxHeartbeats 8000000 in
/-- **The debug-list words keep `XTopAt`** (module docstring). -/
theorem XTopAt.dbgStep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a : A}
    {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ)
    (hw : P1.WritesIn st s s' (DbgWc (L := L) Z.T Z.c s)) :
    XTopAt (L := L) AR Z s' a σ := by
  have hSch := hX.fin.1.1.1
  have hP := hX.fin.1.2
  have hE := hX.esa
  obtain ⟨Q, R0, hc, hs⟩ := hSch.lists
  have hT := hc.tcbs
  have hN := hc.node
  have hnd := hN.disj
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hko : ∀ t ∈ Z.T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := fun t ht => by
    rcases hc.ksOut t ht with h | h <;> omega
  have hnb : ∀ c, L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := fun _ => rfl
  have h88 : layout.node.DEBUG_TCBS.val = 88 := by simp [layout.node.DEBUG_TCBS]
  have hdv := P1.nodeAt_val hN (off := layout.node.DEBUG_TCBS) (by rw [h88]; omega)
  -- the words written, by value
  have hV : ∀ {b : U64}, DbgWc (L := L) Z.T Z.c s b →
      (∃ y ∈ Z.T, y.val + 3576 ≤ b.val ∧ b.val < y.val + 3592) ∨ b.val = L.nodeBase s Z.c + 88 := by
    intro b hb
    rcases hb with ⟨y, hy, rfl | rfl⟩ | rfl
    · left
      have hv : (P1.dnA y).val = y.val + 3576 := by
        unfold P1.dnA; rw [Notif.tfield_val (hT y hy) (by decide)]; rfl
      exact ⟨y, hy, by omega, by omega⟩
    · left
      have hv : (P1.dpA y).val = y.val + 3584 := by
        unfold P1.dpA; rw [Notif.tfield_val (hT y hy) (by decide)]; rfl
      exact ⟨y, hy, by omega, by omega⟩
    · right; rw [hdv, h88]
  -- the node words other than `DEBUG_TCBS` are kept
  have hnk : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 88 →
      L.mem s' (L.nodeAt s Z.c o) = L.mem s (L.nodeAt s Z.c o) := by
    intro o ho h8 h1
    refine hw.mem_eq (P1.nodeAt_aligned hN ho h8) fun hb => ?_
    have hv := P1.nodeAt_val hN ho
    rcases hV hb with ⟨y, hy, g1, g2⟩ | g
    · have := hnd y hy; omega
    · omega
  -- words of the kernel-state block, off the TCBs' debug fields, are kept
  have hne : ∀ b : U64, P1.Aligned b → b.val < (L.ksb s).val + 13568 →
      (∀ y ∈ Z.T, b.val < y.val + 3576 ∨ y.val + 3592 ≤ b.val) → L.mem s' b = L.mem s b :=
    fun b hb h0 h1 => hw.mem_eq hb fun hb' => by
      rcases hV hb' with ⟨y, hy, g1, g2⟩ | g
      · rcases h1 y hy with h | h <;> omega
      · rw [hnb] at g; omega
  have hSA : Sched.SAgree st Z.T Z.C Z.c s s' := by
    refine ⟨hw.1, hw.2.1, fun o ho h8 _ _ _ _ h88' => hnk o ho h8 h88', fun y hy K hK => ?_, ?_, ?_,
      fun sc hsc b hb hin => hw.mem_eq hb fun hb' => ?_⟩
    · obtain ⟨h1, h2, -⟩ := Sched.schedField_ok hK
      refine hw.mem_eq (P1.field_aligned (hT y hy) h1 h2) fun hb => ?_
      have hv := Notif.tfield_val (hT y hy) h1 (K := K)
      have hKv : K.val = 3520 ∨ K.val = 3448 ∨ K.val = 3432 ∨ K.val = 3464 ∨ K.val = 3592 ∨ K.val = 3480 ∨
          K.val = 3488 := by
        rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      rcases hV hb with ⟨y', hy', g1, g2⟩ | g
      · by_cases e : y' = y
        · subst e; omega
        · have := tcb_disj hP.ep hy hy' e; omega
      · have := hnd y hy; omega
    · refine hne _ ?_ ?_ fun y hy => ?_
      · unfold Sched.curDomA; unfold P1.Aligned
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      · simp [Sched.curDomA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      · simp [Sched.curDomA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
        rcases hko y hy with h | h <;> omega
    · refine hne _ ?_ ?_ fun y hy => ?_
      · unfold Sched.dtA; unfold P1.Aligned
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      · simp [Sched.dtA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      · simp [Sched.dtA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
        rcases hko y hy with h | h <;> omega
    · obtain ⟨-, o1, o2, -⟩ := hSch.scOutIn hsc hin
      rcases hV hb' with ⟨y, hy, g1, g2⟩ | g
      · rcases o2 y hy with h | h <;> omega
      · omega
  have hnw : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 88 →
      Sched.nodeW st s' Z.c o = Sched.nodeW st s Z.c o := by
    intro o ho h8 h1; unfold Sched.nodeW; rw [Sched.nodeAt_ksb hw.1]; exact hnk o ho h8 h1
  have hSch' := hSch.of_sagree hSA
    (hnw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
    (hnw _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
    ⟨rfl, rfl, fun _ => Or.inl rfl⟩
  refine hX.frameStepV hw (fun b hb => ?_) (fun b hb hf => ?_) (fun b hb hf => ?_) (fun hb => ?_) (fun hb => ?_)
    rfl rfl rfl rfl rfl rfl rfl rfl hSch' ?_ ?_ ?_ hX.fin.1.1.2.2.2.2.2.2
  · -- no VSpace object word
    rcases hb with ⟨y, hy, rfl | rfl⟩ | rfl
    · exact hP.disj _ (tcb_oobj hy (hT y hy) (by decide) (by decide))
    · exact hP.disj _ (tcb_oobj hy (hT y hy) (by decide) (by decide))
    · exact hP.disj _ (Or.inl (by rw [hdv, h88]; omega))
  · -- not read by the endpoint relation
    have hPe := hP.ep
    rcases hV hb with ⟨y, hy, g1, g2⟩ | g
    · rcases hf with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hwp, h⟩
      · have := hPe.et e he y hy; omega
      · have := hPe.rt r hr y hy; omega
      · by_cases e : t = y
        · subst e; obtain ⟨-, h2⟩ := h; unfold Endp.TOffN at h2; omega
        · have := tcb_disj hPe ht hy (Ne.symm e); have := h.range; omega
      · by_cases e : t = y
        · subst e; unfold Endp.TL at h; omega
        · have := tcb_disj hPe ht hy (Ne.symm e); unfold Endp.TL at h; omega
      · have := hPe.bt wp hwp y hy; rw [← h] at this; omega
    · exact hE.node b (by omega) (by omega) hf
  · -- not read by the notification relation
    have hPn := hSch.placed
    rcases hV hb with ⟨y, hy, g1, g2⟩ | g
    · rcases hf with ⟨n, hn, h1, h2⟩ | ⟨t, ht, h⟩
      · have := hPn.disj n hn y hy; omega
      · have hv := nfootT_val (hT t ht) h
        by_cases e : t = y
        · subst e; omega
        · have := tcb_disj hP.ep ht hy (Ne.symm e); omega
    · obtain ⟨o, ho, rfl⟩ := node_word' hc.node (b := b) (by omega) (by omega)
      rcases hf with ⟨n, hn, n1, n2⟩ | ⟨t, ht, h⟩
      · exact hSch.nodeNW o ho (Or.inl ⟨n, hn, n1, n2⟩)
      · have hv := nfootT_val (hT t ht) h
        have := hnd t ht; omega
  · -- not the kernel root
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rcases hV hb with ⟨y, hy, g1, g2⟩ | g
    · rcases hko y hy with h' | h' <;> omega
    · rw [hnb] at g; omega
  · -- not the FEATURES word (#65)
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.FEATURES).val = (L.ksb s).val + 72 := by
      unfold layout.ks.FEATURES
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rcases hV hb with ⟨y, hy, g1, g2⟩ | g
    · rcases hko y hy with h' | h' <;> omega
    · rw [hnb] at g; omega
  · -- the IRQ relation
    have hI := hX.fin.1.1.2.2.2.1
    refine ⟨fun i hi => ?_, fun i hi => hI.node i hi⟩
    have hv := irqStA_val hkf hi
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (by omega)
      (fun y hy => by rcases hko y hy with h | h <;> omega)]
    exact hI.st i hi
  · -- the IO-port relation
    have hI := hX.fin.1.1.2.2.2.2.1
    intro p hp
    have hwi : (wI p).val < 1024 := by rw [wI_val hp]; omega
    have hv := ioA_val hkf hwi
    unfold bitOf
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (by omega)
      (fun y hy => by rcases hko y hy with h | h <;> omega)]
    exact hI p hp
  · -- the domain schedule
    refine hX.rel.2.2.2.1.frame (fun o ho => ?_) rfl rfl
    have h8 := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    exact hne _ (by unfold P1.Aligned; rw [hv]; omega) (by omega)
      (fun y hy => by rcases hko y hy with h | h <;> omega)

end

end

end Fl4Proofs.P3
