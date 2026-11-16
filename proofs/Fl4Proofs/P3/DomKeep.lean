/-
P3 (DESIGN.md §9): **FL4 steps keeping the domain schedule's words**, for
the decodes' `DomFrame`s (DecDomHyp, AllDom).

* `DK4 s s'`: the kernel-global base and the five words of the domain
  schedule (offsets `domOffs0`, AllDom's `domOffs`) are kept; reflexive and
  transitive.
* `DomPlaced th s`: the base fits and is aligned, every object of `th` and
  the current core's scheduler-action word lie apart from the first 256 bytes
  of the kernel-global area; kept by any step keeping the base and the core.
* The leaves: a write apart from the first 256 bytes (`DK4.wr`), the IRQ
  state word (`DK4.irqSt`), `set_thread_state` (`sts_dk4`, `sts_dk4c`),
  `cdt::insert` (`DK4.of_slotFrame`, from `insert_frame`) and
  `invoke_irq_control` (`invoke_ctl_dk4c`). The deletion's frame is IrqDom's.
-/
import Fl4Proofs.P3.IntFrame
import Fl4Proofs.P3.IntRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The offsets of the domain schedule's words in the kernel-global area. -/
def domOffs0 : List U64 := [32#u64, 192#u64, 200#u64, 208#u64, 216#u64]

theorem domOffs0_lt {o : U64} (ho : o ∈ domOffs0) : o.val < 256 ∧ o.val % 8 = 0 := by
  simp only [domOffs0, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The base and the domain schedule's words kept. -/
def DK4 (s s' : S) : Prop :=
  L.ksb s' = L.ksb s ∧ ∀ o ∈ domOffs0,
    L.mem s' (core.num.U64.wrapping_add (L.ksb s) o) = L.mem s (core.num.U64.wrapping_add (L.ksb s) o)

theorem DK4.refl (s : S) : DK4 (L := L) s s := ⟨rfl, fun _ _ => rfl⟩

theorem DK4.trans {s1 s2 s3 : S} (h1 : DK4 (L := L) s1 s2) (h2 : DK4 (L := L) s2 s3) : DK4 (L := L) s1 s3 :=
  ⟨h2.1.trans h1.1, fun o ho => by have := h2.2 o ho; rw [h1.1] at this; exact this.trans (h1.2 o ho)⟩

/-- **Where the domain schedule sits**: the base fits and is aligned, the
objects and the core's scheduler-action word lie apart from its first 256
bytes. -/
structure DomPlaced (th : TypedHeap) (s : S) : Prop where
  fits : (L.ksb s).val + 13568 ≤ 2 ^ 64
  align : (L.ksb s).val % 8 = 0
  apart : ∀ p k, th p = some k → p.val + objSize k ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ p.val
  act : (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val + 8 ≤ (L.ksb s).val ∨
    (L.ksb s).val + 256 ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val
  actAl : P1.Aligned (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)

/-- The base fits and is aligned, the objects lie apart from the first 256
bytes (`DomPlaced` without the core's action word). -/
structure KsbOK (th : TypedHeap) (s : S) : Prop where
  fits : (L.ksb s).val + 13568 ≤ 2 ^ 64
  align : (L.ksb s).val % 8 = 0
  apart : ∀ p k, th p = some k → p.val + objSize k ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ p.val

theorem DomPlaced.toK {th : TypedHeap} {s : S} (h : DomPlaced (L := L) th s) : KsbOK (L := L) th s :=
  ⟨h.fits, h.align, h.apart⟩

theorem KsbOK.same {th : TypedHeap} {s s' : S} (h : KsbOK (L := L) th s) (hk : L.ksb s' = L.ksb s) :
    KsbOK (L := L) th s' :=
  ⟨hk ▸ h.fits, hk ▸ h.align, hk ▸ h.apart⟩

theorem DomPlaced.same {th : TypedHeap} {s s' : S} (h : DomPlaced (L := L) th s) (hk : L.ksb s' = L.ksb s)
    (hc : L.cpu s' = L.cpu s) : DomPlaced (L := L) th s' := by
  have e : L.nodeAt s' (L.cpu s') layout.node.SCHED_ACTION = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION := by
    rw [hc]; exact P1.nodeAt_of_ksb hk _ _
  exact ⟨hk ▸ h.fits, hk ▸ h.align, hk ▸ h.apart, by rw [e, hk]; exact h.act, by rw [e]; exact h.actAl⟩

theorem dw_val {kb o : U64} (hf : kb.val + 13568 ≤ 2 ^ 64) (ho : o ∈ domOffs0) :
    (core.num.U64.wrapping_add kb o).val = kb.val + o.val := by
  have := (domOffs0_lt ho).1
  rw [core.num.U64.wrapping_add_val_eq]; simp [U64.size_def, U64.numBits]; omega

/-- **A write apart from the first 256 bytes** of the kernel-global area. -/
theorem DK4.wr {s : S} (hf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (ha : (L.ksb s).val % 8 = 0) {w : U64}
    (hw8 : P1.Aligned w) (hw : w.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ w.val ∨
      ∀ o ∈ domOffs0, w.val ≠ (L.ksb s).val + o.val) (v : U64) :
    DK4 (L := L) s (L.wr s w v) := by
  refine ⟨L.ksb_wr _ _ _, fun o ho => ?_⟩
  have hv := dw_val hf ho
  have := domOffs0_lt ho
  refine L.mem_wr_ne hw8 (by unfold P1.Aligned; rw [hv]; omega) fun e => ?_
  have ev := e
  rw [hv] at ev
  rcases hw with h | h | h
  · omega
  · omega
  · exact h o ho ev

/-- **A write into an object of `th`.** -/
theorem DK4.wr_obj {th : TypedHeap} {s : S} (hD : DomPlaced (L := L) th s) {w p : U64} {k : ObjKind}
    (hp : th p = some k) (hw1 : p.val ≤ w.val) (hw2 : w.val < p.val + objSize k) (hw8 : P1.Aligned w)
    (v : U64) : DK4 (L := L) s (L.wr s w v) := by
  refine DK4.wr hD.fits hD.align hw8 ?_ v
  rcases hD.apart p k hp with h | h
  · left; unfold P1.Aligned at hw8; have := hD.align; omega
  · right; left; omega

/-- **IRQ `irq`'s state word.** -/
theorem DK4.irqSt {s : S} (hf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (ha : (L.ksb s).val % 8 = 0) {irq : U64}
    (hi : irq.val < 128) (v : U64) : DK4 (L := L) s (L.wr s (irqStA (L.ksb s) irq) v) := by
  have hv := irqStA_val hf hi
  refine DK4.wr hf ha (by unfold P1.Aligned; rw [hv]; omega) (Or.inr (Or.inr fun o ho => ?_)) v
  have := (domOffs0_lt ho).1
  simp only [domOffs0, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rw [hv]; rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

/-- **`set_thread_state` of a TCB.** -/
theorem sts_dk4 {th : TypedHeap} (hP : Placed th) {s : S} (hD : DomPlaced (L := L) th s) {t : U64}
    (ht : th t = some .tcb) (v : U64) :
    sched.set_thread_state st s t v ⦃ s' => DK4 (L := L) s s' ⦄ := by
  have htf := hP.fits t _ ht
  have hta := hP.align t _ ht
  have e4 : objSize ObjKind.tcb = 4096 := rfl
  rw [e4] at htf
  have hstv : (stA t).val = t.val + 3328 := by
    rw [stA_eq, wordOf_val (by simp [objSize] at htf; simp; omega)]; simp
  have h1 : DK4 (L := L) s (L.wr s (stA t) v) :=
    DK4.wr_obj hD ht (k := .tcb) (by rw [hstv]; omega) (by rw [hstv, e4]; omega)
      (by unfold P1.Aligned; rw [hstv]; omega) v
  refine WP.spec_mono (set_thread_state_cases s t v) ?_
  rintro s' (rfl | rfl)
  · exact h1
  · refine h1.trans ?_
    have hD1 := hD.same (s' := L.wr s (stA t) v) (L.ksb_wr _ _ _) (L.cpu_wr _ _ _)
    have e : L.nodeAt (L.wr s (stA t) v) (L.cpu (L.wr s (stA t) v)) layout.node.SCHED_ACTION =
        L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION := by
      rw [L.cpu_wr]; exact P1.nodeAt_of_ksb (L.ksb_wr _ _ _) _ _
    refine DK4.wr hD1.fits hD1.align ?_ ?_ _
    · rw [← e]; exact hD1.actAl
    · rw [← e] at *; rcases hD1.act with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

/-- **`cdt::insert`'s frame** (`SlotFrame`): every word outside the objects,
the domain schedule's among them, kept. -/
theorem DK4.of_slotFrame {th : TypedHeap} {s s' : S} (hD : KsbOK (L := L) th s)
    (h : SlotFrame (L := L) th s s') : DK4 (L := L) s s' := by
  refine ⟨h.1, fun o ho => h.2 _ ⟨?_, fun p k hp ⟨h1, h2⟩ => ?_⟩⟩
  · have hv := dw_val hD.fits ho
    have := domOffs0_lt ho
    unfold P1.Aligned; rw [hv]; have := hD.align; omega
  · have hv := dw_val hD.fits ho
    have := (domOffs0_lt ho).1
    rw [hv] at h1 h2
    rcases hD.apart p k hp with h | h <;> omega

end

/-! ## Conditional forms, for the refinement posts -/

section
variable {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] (arI : machine.Arch A)

/-- `sts_dk4` under its placement premise, for any start. -/
theorem sts_dk4c {th : TypedHeap} (hP : Placed th) (s : S) {t : U64} (ht : th t = some .tcb) (v : U64) :
    sched.set_thread_state st s t v ⦃ s' => DomPlaced (L := L) th s → DK4 (L := L) s s' ⦄ := by
  by_cases hD : DomPlaced (L := L) th s
  · exact WP.spec_mono (sts_dk4 hP hD ht v) fun _ h _ => h
  · exact WP.spec_mono (set_thread_state_cases s t v) fun _ _ h => absurd h hD

/-- **`invoke_irq_control`**: the IRQ's state word (`DK4.irqSt`), then the
insertion of the handler cap (`insert_frame`), between slots of the MDB. -/
theorem invoke_ctl_dk4c {th : TypedHeap} (hP : Placed th) (s : S) (ar : A) {G : MdbGhost}
    (hL : IntLayout th (L.ksb s)) (hM : MdbLinks th (L.mem s) G)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (irq : U64) (hirq : irq.val < 128) {src dest : U64} (hs : IsSlot th src) (hd : IsSlot th dest)
    (hsrc : capAt (L.mem s) src = ok .IrqControl) :
    interrupt.invoke_irq_control st arI s ar irq dest src ⦃ r => KsbOK (L := L) th s → DK4 (L := L) s r.1 ⦄ := by
  unfold interrupt.invoke_irq_control
  obtain ⟨a1, ha1⟩ := hmask ar irq (decide (interrupt.IRQ_SIGNAL = interrupt.IRQ_INACTIVE))
  rw [set_irq_state_eq arI s ar _ irq ha1]
  simp only [bind_ok]
  have hS := IntLayout.slotsSame (L := L) hP hL s hirq interrupt.IRQ_SIGNAL
  have hsrc1 : capAt (L.mem (L.wr s (irqStA (L.ksb s) irq) interrupt.IRQ_SIGNAL)) src = ok .IrqControl := by
    rw [hS.capAt hs, hsrc]
  have hnx : nextOf (L.mem (L.wr s (irqStA (L.ksb s) irq) interrupt.IRQ_SIGNAL)) src = 0#u64 ∨
      IsSlot th (nextOf (L.mem (L.wr s (irqStA (L.ksb s) irq) interrupt.IRQ_SIGNAL)) src) := by
    rw [hS.nextOf hs]
    have hsm : src ∈ G.chains.flatten := (hM.members _).2 ⟨hs, _, hsrc, by simp⟩
    rcases hM.next_mem hsm with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ((hM.members _).1 h).1
  refine WP.spec_bind (insert_frame hP _ (.IrqHandler irq) src dest hs hd _ hsrc1 hnx) fun s2 h2 => ?_
  refine (WP.spec_ok _).2 fun hK => ?_
  exact (DK4.irqSt hK.fits hK.align hirq _).trans (DK4.of_slotFrame (hK.same (L.ksb_wr _ _ _)) h2)

end

end

end Fl4Proofs.P3
