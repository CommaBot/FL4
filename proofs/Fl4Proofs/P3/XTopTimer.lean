/-
P3 (DESIGN.md §9), CSpace and TCB: **SetTimer at `XTop`** (`tcb_set_timerX`).

* `TmW`: the words FL4's `timer::insert` writes (P1's `timer.insert.foot`):
  the TCB timer fields (offsets 3528..3576), every core's timer-tree root and
  min node words (104, 112, `P1.TW`; the timer may sit on another core's
  tree) and the core's `REPROGRAM`, which it keeps or sets to 1.
* `OtherTmOK` [J-side]: the other cores' timer words are read by no relation
  of `XTopAt` (`JAtZ.otherTmOK` in XTopJoint).
* `XTopAt.tmStep`: such writes keep `XTopAt`, the spec's reprogram flag or'ed
  with whether `REPROGRAM` was set (`SchedRel.of_sagreeR`).
* `TimerInsHyp` [W]: `timer::insert`'s footprint after the restart, as P1's
  (`JAtZ.timerIns` in XTopJoint).
* `tcb_set_timerX`: the length check, the restart, `timer::insert`, against
  the spec's SetTimer (its reprogram flag chosen as FL4's).
-/
import Fl4Proofs.P3.XTopTcbFpu
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Ipc Fl4Proofs.P3.Endp

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **`SchedRel` across an agreeing step that may change `REPROGRAM`**
(`SchedRel.of_sagree` with the spec's flag related to the new word). -/
theorem Sched.SchedRel.of_sagreeR {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : Sched.SchedRel st N T C c s σ) (ha : Sched.SAgree st T C c s s')
    (hact : Sched.nodeW st s' c layout.node.SCHED_ACTION = Sched.nodeW st s c layout.node.SCHED_ACTION)
    (v : Bool) (hrp : v = decide (Sched.nodeW st s' c layout.node.REPROGRAM ≠ 0#u64)) :
    Sched.SchedRel st N T C c s' { σ with reprogramTimer := v } := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hs' := hs.agree ha
  refine ⟨hS.placed, fun o ho => by rw [Sched.nodeAt_ksb ha.ksb]; exact hS.nodeNW o ho,
    by rw [Sched.curDomA_ksb ha.ksb]; exact hS.domNW, by rw [Sched.dtA_ksb ha.ksb]; exact hS.dtNW,
    Sched.scOut_transfer ha.ksb (SzKeep.of_kheap rfl) hS.scOut,
    Sched.scDisj_transfer (SzKeep.of_kheap rfl) hS.scDisj, by rw [hact]; exact hS.actW,
    by rw [hact]; exact hS.act, hrp, hs.core_eq ha.sc hS.core, Q, R,
    hc.agree ha.toC, ?_⟩
  exact ⟨fun p hp => hs'.rq p hp, fun d p hd => hs'.rqDom d p hd, hs'.rel, hs'.curThread,
    hs'.curSc, hs'.curTime, hs'.consumed, hs'.curDom, fun t ht => hs'.tcb t ht, hs'.scMem,
    fun sc hsc => hs'.scs sc hsc, hs'.idleSc, hs'.domTime, hs'.idleTh⟩

/-- **The other cores' timer words** [J-side facts]: for each other core of
`Cs`, its node is placed and its timer-tree words 104, 112 are read by no
relation of `XTopAt` (no VSpace object, no endpoint or notification
footprint word, no word of a spec SC). -/
def OtherTmOK (Z : XSets) (Cs : Set U64) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ c' ∈ Cs, c' ≠ Z.c → P1.NodePlaced st Z.T s c' ∧ ∀ o : U64, (o.val = 104 ∨ o.val = 112) →
    ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) (L.nodeAt s c' o) ∧
    ¬ Endp.EFoot Z.T Z.E Z.R Z.B (L.nodeAt s c' o) ∧ ¬ Notif.NFoot Z.N Z.T (L.nodeAt s c' o) ∧
    ∀ sc ∈ Z.C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → ¬ Sched.ScObj sc n (L.nodeAt s c' o)

/-- `OtherTmOK` reads the state through the kernel-state base and the spec's
SCs only. -/
theorem OtherTmOK.trans {Z : XSets} {Cs : Set U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : OtherTmOK (L := L) Z Cs s σ) (hk : L.ksb s' = L.ksb s)
    (hsc : ∀ p x n, σ'.kheap p = some (.schedContext x n) → σ.kheap p = some (.schedContext x n)) :
    OtherTmOK (L := L) Z Cs s' σ' := by
  intro c' hc' e
  obtain ⟨hN, ho⟩ := h c' hc' e
  have hnb : L.nodeBase s' c' = L.nodeBase s c' := by simp only [P1.LawfulStore.nodeBase, hk]
  refine ⟨⟨by rw [hnb]; exact hN.align, by rw [hnb]; exact hN.fits, by rw [hnb]; exact hN.disj⟩, fun o h1 => ?_⟩
  rw [P1.nodeAt_of_ksb hk, hk]
  obtain ⟨g1, g2, g3, g4⟩ := ho o h1
  exact ⟨g1, g2, g3, fun sc hsc' x n hx => g4 sc hsc' x n (hsc _ x n hx)⟩

/-- `timer::insert`'s write set (P1's `timer.insert.foot`): the timer words
of every core (`P1.TW`) and the core's `REPROGRAM`. -/
def TmW (T Cs : Set U64) (c : U64) (s : S) (b : U64) : Prop :=
  P1.TW st T Cs s b ∨ b = L.nodeAt s c layout.node.REPROGRAM

set_option maxHeartbeats 8000000 in
/-- **`timer::insert`'s writes keep `XTopAt`** (module docstring: every
core's timer words, `REPROGRAM` kept or set to 1, the
spec's flag or'ed with whether it was set). -/
theorem XTopAt.tmStep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {Cs : Set U64} {s s' : S} {a : A}
    {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ)
    (hO : OtherTmOK (L := L) Z Cs s σ) (hw : P1.WritesIn st s s' (TmW (L := L) Z.T Cs Z.c s))
    (hR : L.mem s' (L.nodeAt s Z.c layout.node.REPROGRAM) = L.mem s (L.nodeAt s Z.c layout.node.REPROGRAM) ∨
      L.mem s' (L.nodeAt s Z.c layout.node.REPROGRAM) = 1#u64) :
    ∃ r : Bool, XTopAt (L := L) AR Z s' a { σ with reprogramTimer := σ.reprogramTimer || r } := by
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
  have h56 : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have hrv := P1.nodeAt_val hN (off := layout.node.REPROGRAM) (by omega)
  -- the words written, by value
  have hV : ∀ {b : U64}, TmW (L := L) Z.T Cs Z.c s b →
      (∃ y ∈ Z.T, y.val + 3528 ≤ b.val ∧ b.val < y.val + 3576) ∨
      (b.val = L.nodeBase s Z.c + 104 ∨ b.val = L.nodeBase s Z.c + 112 ∨ b.val = L.nodeBase s Z.c + 56) ∨
      (∃ c' ∈ Cs, c' ≠ Z.c ∧ ∃ o : U64, (o.val = 104 ∨ o.val = 112) ∧ b = L.nodeAt s c' o ∧
        b.val = L.nodeBase s c' + o.val) := by
    intro b hb
    rcases hb with (⟨y, hy, K, h1, h2, rfl⟩ | ⟨c', hc', o, ho, rfl⟩) | rfl
    · left; exact ⟨y, hy, by rw [Notif.tfield_val (hT y hy) (by omega)]; omega,
        by rw [Notif.tfield_val (hT y hy) (by omega)]; omega⟩
    · by_cases e : c' = Z.c
      · subst e; right; left; rw [P1.nodeAt_val hN (by omega)]; omega
      · right; right
        exact ⟨c', hc', e, o, ho, rfl, P1.nodeAt_val (hO c' hc' e).1 (by omega)⟩
    · right; left; rw [hrv, h56]; omega
  have cne : ∀ c' : U64, c' ≠ Z.c → c'.val ≠ Z.c.val := fun c' e h => e (UScalar.eq_of_val_eq h)
  -- the node words other than the timer-tree words and `REPROGRAM` are kept
  have hnk : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 104 → o.val ≠ 112 → o.val ≠ 56 →
      L.mem s' (L.nodeAt s Z.c o) = L.mem s (L.nodeAt s Z.c o) := by
    intro o ho h8 h1 h2 h3
    refine hw.mem_eq (P1.nodeAt_aligned hN ho h8) fun hb => ?_
    have hv := P1.nodeAt_val hN ho
    rcases hV hb with ⟨y, hy, g1, g2⟩ | g | ⟨c', -, e, o', ho', -, g⟩
    · have := hnd y hy; omega
    · omega
    · have := cne c' e; rw [hnb] at g hv
      rcases Nat.lt_or_gt_of_ne this with h | h
      · have : c'.val * 4288 + 4288 ≤ Z.c.val * 4288 := by nlinarith
        omega
      · have : Z.c.val * 4288 + 4288 ≤ c'.val * 4288 := by nlinarith
        omega
  -- words of the kernel-state block, off the TCBs' timer fields, are kept
  have hne : ∀ b : U64, P1.Aligned b → b.val < (L.ksb s).val + 13568 →
      (∀ y ∈ Z.T, b.val < y.val + 3528 ∨ y.val + 3576 ≤ b.val) → L.mem s' b = L.mem s b :=
    fun b hb h0 h1 => hw.mem_eq hb fun hb' => by
      rcases hV hb' with ⟨y, hy, g1, g2⟩ | g | ⟨c', -, e, o', ho', -, g⟩
      · rcases h1 y hy with h | h <;> omega
      · rw [hnb] at g; omega
      · rw [hnb] at g; omega
  have hSA : Sched.SAgree st Z.T Z.C Z.c s s' := by
    refine ⟨hw.1, hw.2.1, fun o ho h8 _ h56' h1 h2 _ => hnk o ho h8 h1 h2 h56', fun y hy K hK => ?_, ?_, ?_,
      fun sc hsc b hb hin => hw.mem_eq hb fun hb' => ?_⟩
    · obtain ⟨h1, h2, -⟩ := Sched.schedField_ok hK
      refine hw.mem_eq (P1.field_aligned (hT y hy) h1 h2) fun hb => ?_
      have hv := Notif.tfield_val (hT y hy) h1 (K := K)
      have hKv : K.val = 3520 ∨ K.val = 3448 ∨ K.val = 3432 ∨ K.val = 3464 ∨ K.val = 3592 ∨ K.val = 3480 ∨
          K.val = 3488 := by
        rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      rcases hV hb with ⟨y', hy', g1, g2⟩ | g | ⟨c', hc', e, o', ho', -, g⟩
      · by_cases e : y' = y
        · subst e; omega
        · have := tcb_disj hP.ep hy hy' e; omega
      · have := hnd y hy; omega
      · have := (hO c' hc' e).1.disj y hy; omega
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
      rcases hV hb' with ⟨y, hy, g1, g2⟩ | g | ⟨c', hc', e, o', ho', eb, -⟩
      · rcases o2 y hy with h | h <;> omega
      · omega
      · obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
        exact ((hO c' hc' e).2 o' ho').2.2.2 sc hsc x n hk (eb ▸ hx.in_obj hin)
  have hact : Sched.nodeW st s' Z.c layout.node.SCHED_ACTION = Sched.nodeW st s Z.c layout.node.SCHED_ACTION := by
    unfold Sched.nodeW; rw [Sched.nodeAt_ksb hw.1]
    exact hnk _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  have erp : Sched.nodeW st s' Z.c layout.node.REPROGRAM = L.mem s' (L.nodeAt s Z.c layout.node.REPROGRAM) := by
    unfold Sched.nodeW; rw [Sched.nodeAt_ksb hw.1]
  have erp0 : Sched.nodeW st s Z.c layout.node.REPROGRAM = L.mem s (L.nodeAt s Z.c layout.node.REPROGRAM) := rfl
  obtain ⟨r, hr⟩ : ∃ r : Bool, (σ.reprogramTimer || r) = decide (Sched.nodeW st s' Z.c layout.node.REPROGRAM ≠ 0#u64) := by
    rcases hR with e | e
    · exact ⟨false, by rw [Bool.or_false, hSch.repr, erp, erp0, e]⟩
    · exact ⟨true, by rw [Bool.or_true, erp, e]; decide⟩
  have hSch' := hSch.of_sagreeR hSA hact _ hr
  refine ⟨r, hX.frameStepV hw (fun b hb => ?_) (fun b hb hf => ?_) (fun b hb hf => ?_) (fun hb => ?_)
    rfl rfl rfl rfl rfl rfl rfl hSch' ?_ ?_ ?_ hX.fin.1.1.2.2.2.2.2.2⟩
  · -- no VSpace object word
    rcases hb with (⟨y, hy, K, h1, h2, rfl⟩ | ⟨c', hc', o, ho, rfl⟩) | rfl
    · exact hP.disj _ (tcb_oobj hy (hT y hy) (by omega) (by omega))
    · by_cases e : c' = Z.c
      · subst e; exact hP.disj _ (Or.inl (by rw [P1.nodeAt_val hN (by omega)]; omega))
      · exact ((hO c' hc' e).2 o ho).1
    · exact hP.disj _ (Or.inl (by rw [hrv, h56]; omega))
  · -- not read by the endpoint relation
    have hPe := hP.ep
    rcases hV hb with ⟨y, hy, g1, g2⟩ | g | ⟨c', hc', e, o', ho', eb, -⟩
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
    · exact ((hO c' hc' e).2 o' ho').2.1 (eb ▸ hf)
  · -- not read by the notification relation
    have hPn := hSch.placed
    rcases hV hb with ⟨y, hy, g1, g2⟩ | g | ⟨c', hc', e, o', ho', eb, -⟩
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
    · exact ((hO c' hc' e).2 o' ho').2.2.1 (eb ▸ hf)
  · -- not the kernel root
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rcases hV hb with ⟨y, hy, g1, g2⟩ | g | ⟨c', -, e, o', ho', -, g⟩
    · rcases hko y hy with h' | h' <;> omega
    · rw [hnb] at g; omega
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

/-- **Hypothesis: `timer::insert`'s footprint, every core** [W] (P1's
`timer.insert.foot`; `JAtZ.timerIns`): after the restart, arming `p`'s timer
writes only timer words of every core and the core's `REPROGRAM`, which it
keeps or sets to 1. -/
def TimerInsHyp (T Cs : Set U64) (s : S) (ct p : U64) : Prop :=
  ∀ s1 d b, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    timer.insert st s1 p d b ⦃ s' => P1.WritesIn st s1 s' (TmW (L := L) T Cs (L.cpu s1) s1) ∧
      (L.mem s' (L.nodeAt s1 (L.cpu s1) layout.node.REPROGRAM) =
          L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.REPROGRAM) ∨
        L.mem s' (L.nodeAt s1 (L.cpu s1) layout.node.REPROGRAM) = 1#u64) ⦄

/-- SetTimer's outcomes include the reprogram flag set, or not. -/
theorem setTimer_memB (blk call don : Bool) (σ1 : Fl4Spec.State Unit) (t d b : Fl4Spec.Data) (r : Bool) :
    ((.ok [], { σ1 with reprogramTimer := σ1.reprogramTimer || r }) :
      Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeFl4TCB (.setTimer t d b))).run σ1).1 := by
  show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
  refine mem_liftE (x := ([], { σ1 with reprogramTimer := σ1.reprogramTimer || r })) ?_
  refine mem_bind_nd (x := (r, σ1)) ⟨trivial, rfl⟩ ?_
  refine mem_bind_nd (x := ((), { σ1 with reprogramTimer := σ1.reprogramTimer || r })) ?_ (Set.mem_singleton _)
  exact Set.mem_singleton _

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **TcbXOpen1's SetTimer at `XTop`** (module docstring): the length check,
the restart, `timer::insert` (`TimerInsHyp` [W], `OtherTmOK`;
`XTopAt.tmStep`), the spec's reprogram flag chosen as FL4's. -/
theorem tcb_set_timerX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hDI : DelInv Z.th (L.mem s))
    (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .setTimer)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) {Cs : Set U64} (hO : OtherTmOK (L := L) Z Cs s σ) (hTI : TimerInsHyp (L := L) Z.T Cs s ct p)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSetTimer p ⟨length, buf, call, slot, extra⟩ blk
      call don slbl (args.map UScalar.bv) ci sl excaps buffer := by
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4SetTimer (Z := Unit) (args.map UScalar.bv) p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKX
  rw [decode_timer_eq arI s ar p _ hstall, hdec0]
  by_cases h1 : length < 2#u64
  · simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeFl4SetTimer
    rw [whenE_pos (by rw [List.length_map, ← hlen]; scalar_tac)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [h1, ↓reduceIte]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
    | [_], h => exfalso; simp only [List.length_singleton] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  rw [ha0, ha1]; simp only [bind_ok]
  obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, -, -, -⟩ := restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
  have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
    rw [← hcur]; exact hst1
  obtain ⟨hX1, hk1, -⟩ := hX.restart' hC hcur hs1 hst1'
  rw [hrc1]; simp only [bind_ok]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
      (Fl4Spec.decodeFl4SetTimer (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) p.bv)).run σ =
      ({(.ok (.invokeFl4TCB (.setTimer p.bv y0.bv y1.bv)), σ)}, False) := by
    apply run_liftME_ok
    unfold Fl4Spec.decodeFl4SetTimer
    rw [whenE_neg (by simp), retOk_bind]
    rfl
  have hKA1 : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s1) := by rw [hk1]; exact hKA
  have hO1 : OtherTmOK (L := L) Z Cs s1 σ1 := by
    obtain ⟨-, x, hk⟩ := hX.curTcb hcur
    have h2 := hst1'
    rw [Notif.setThreadState_eq .restart hk] at h2
    have e := congrArg (fun q => ((), σ1) ∈ q.1) h2
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at e
    have e' : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv :=
      of_eq_true e.symm.symm
    refine hO.trans hk1 fun q y n hq => ?_
    rw [e'] at hq
    unfold Notif.stsAct at hq
    by_cases hqc : q = ct.bv
    · subst hqc; split_ifs at hq <;> simp at hq
    · split_ifs at hq <;> simpa [Function.update, hqc] using hq
  refine WP.spec_bind (hTI s1 y0 y1 hs1) ?_
  rintro s2 ⟨hw, hR2⟩
  have hc1 : L.cpu s1 = Z.c := by obtain ⟨Q, R0, hc, -⟩ := hX1.fin.1.1.1.lists; exact hc.cur
  rw [hc1] at hw hR2
  obtain ⟨r, hXm⟩ := hX1.tmStep hO1 hw hR2
  have fin : ∀ σ' : Fl4Spec.State Unit,
      ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
        ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeFl4TCB (.setTimer p.bv y0.bv y1.bv))).run
          σ1).1 → XTopAt (L := L) AR Z s2 ar σ' →
      (ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, ar)) ⦃ res =>
        TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
            (Fl4Spec.decodeFl4SetTimer (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) p.bv)) s res ⦄ :=
    fun σ' hm hX' => (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ'), hm,
      ⟨Z.th, Z.G, Or.inl ⟨rfl, rfl⟩, hX'.rel.1, hX'.rel.2.1, hX'.rel.2.2.1, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩,
      ⟨Z, hX'⟩⟩)
  exact fin _ (setTimer_memB blk call don σ1 p.bv y0.bv y1.bv r) hXm

/-- **`TcbXOpen1` from `TimerInsHyp`** [W]: no Thread-cap label is left open. -/
theorem tcbXOpen1_of {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hDI : DelInv Z.th (L.mem s)) (lbl length : U64) (p : U64) (blk call don : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {Cs : Set U64} (hO : OtherTmOK (L := L) Z Cs s σ) (hTI : TimerInsHyp (L := L) Z.T Cs s ct p) :
    TcbXOpen1 (L := L) arI (XTop (L := L) AR) s ar σ lbl p ⟨length, buf, call, cslotAddr sl, extra⟩ blk call
      don slbl (argsU.map UScalar.bv) ci sl excaps buffer := by
  refine ⟨?_⟩
  rintro rfl
  obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .setTimer by
    simp [tcbExtOf])
  exact tcb_set_timerX arI s ar σ hX hKA hC hDI p slbl hg he length buf ct hct argsU hlen hargs hcur hact
    (hstall' p) hO hTI call _ extra blk don ci sl excaps buffer

end

end

end Fl4Proofs.P3
