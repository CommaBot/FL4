/-
P3 (DESIGN.md §9), CSpace and TCB: **SetTimer at `XTop`** (`tcb_set_timerX`).

* `TmW`: the timer words of FL4's `timer::insert`: the TCB timer fields
  (offsets 3528..3576) of the sets' TCBs and the core's timer-tree root and
  min node words (104, 112).
* `XTopAt.tmStep`: writes of timer words keep `XTopAt` (no relation reads
  them; `SchedRel` by `SAgree`, which leaves the two node words free).
* `XTopAt.reprStep`: the core's `REPROGRAM` word set, with the spec's
  `reprogram_timer` set (`SchedRel.set_reprogram`).
* `TimerInsHyp` [W]: `timer::insert`'s footprint (P1's, to be exported): the
  timer words, then possibly `REPROGRAM` set.
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

/-- **The timer words** (module docstring). -/
def TmW (T : Set U64) (c : U64) (s : S) (b : U64) : Prop :=
  (∃ y ∈ T, ∃ K : U64, 3528 ≤ K.val ∧ K.val < 3576 ∧ b = core.num.U64.wrapping_add y K) ∨
  (∃ o : U64, (o.val = 104 ∨ o.val = 112) ∧ b = L.nodeAt s c o)

/-- A timer word's value: a TCB timer field, or node word 104 or 112. -/
theorem tmW_val' {T : Set U64} {c : U64} {s : S} (hT : P1.TcbPlaced T) (hN : P1.NodePlaced st T s c) {b : U64}
    (h : TmW (L := L) T c s b) :
    (∃ y ∈ T, y.val + 3528 ≤ b.val ∧ b.val < y.val + 3576) ∨
    (b.val = L.nodeBase s c + 104 ∨ b.val = L.nodeBase s c + 112) := by
  rcases h with ⟨y, hy, K, h1, h2, rfl⟩ | ⟨o, ho, rfl⟩
  · left
    refine ⟨y, hy, ?_, ?_⟩ <;> rw [Notif.tfield_val (hT y hy) (by omega)] <;> omega
  · right; rw [P1.nodeAt_val hN (by omega)]; omega

set_option maxHeartbeats 4000000 in
/-- **Writes of timer words keep `XTopAt`** (module docstring). -/
theorem XTopAt.tmStep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hw : P1.WritesIn st s s' (TmW (L := L) Z.T Z.c s)) : XTopAt (L := L) AR Z s' a σ := by
  have hSch := hX.fin.1.1.1
  have hP := hX.fin.1.2
  have hE := hX.esa
  obtain ⟨Q, R0, hc, -⟩ := hSch.lists
  have hT := hc.tcbs
  have hN := hc.node
  have hnd := hN.disj
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hko : ∀ t ∈ Z.T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := fun t ht => by
    rcases hc.ksOut t ht with h | h <;> omega
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  have hV := fun {b : U64} (hb : TmW (L := L) Z.T Z.c s b) => tmW_val' hT hN hb
  -- the node words other than the timer-tree words are kept
  have hnk : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 104 → o.val ≠ 112 →
      L.mem s' (L.nodeAt s Z.c o) = L.mem s (L.nodeAt s Z.c o) := by
    intro o ho h8 h1 h2
    refine hw.mem_eq (P1.nodeAt_aligned hN ho h8) fun hb => ?_
    have hv := P1.nodeAt_val hN ho
    rcases hV hb with ⟨y, hy, g1, g2⟩ | g | g
    · have := hnd y hy; omega
    · omega
    · omega
  have hSA : Sched.SAgree st Z.T Z.C Z.c s s' := by
    refine ⟨hw.1, hw.2.1, fun o ho h8 _ _ h1 h2 => hnk o ho h8 h1 h2, fun y hy K hK => ?_, ?_, ?_,
      fun sc hsc b hb hin => hw.mem_eq hb fun hb' => ?_⟩
    · obtain ⟨h1, h2, -⟩ := Sched.schedField_ok hK
      refine hw.mem_eq (P1.field_aligned (hT y hy) h1 h2) fun hb => ?_
      have hv := Notif.tfield_val (hT y hy) h1 (K := K)
      have hKv : K.val = 3520 ∨ K.val = 3448 ∨ K.val = 3432 ∨ K.val = 3464 ∨ K.val = 3592 ∨ K.val = 3480 ∨
          K.val = 3488 := by
        rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      rcases hV hb with ⟨y', hy', g1, g2⟩ | g | g
      · by_cases e : y' = y
        · subst e; omega
        · have := tcb_disj hP.ep hy hy' e; omega
      · have := hnd y hy; omega
      · have := hnd y hy; omega
    · refine hw.mem_eq ?_ fun hb => ?_
      · unfold Sched.curDomA; unfold P1.Aligned
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      · have hv : (Sched.curDomA st s).val = (L.ksb s).val + 8 := by
          simp [Sched.curDomA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        rcases hV hb with ⟨y, hy, g1, g2⟩ | g | g
        · rcases hko y hy with h | h <;> omega
        · omega
        · omega
    · refine hw.mem_eq ?_ fun hb => ?_
      · unfold Sched.dtA; unfold P1.Aligned
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      · have hv : (Sched.dtA st s).val = (L.ksb s).val + 16 := by
          simp [Sched.dtA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        rcases hV hb with ⟨y, hy, g1, g2⟩ | g | g
        · rcases hko y hy with h | h <;> omega
        · omega
        · omega
    · obtain ⟨-, o1, o2, -⟩ := hSch.scOutIn hsc hin
      rcases hV hb' with ⟨y, hy, g1, g2⟩ | g | g
      · rcases o2 y hy with h | h <;> omega
      · omega
      · omega
  have hSch' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ := by
    refine hSch.of_sagree hSA ?_ ?_ ⟨rfl, rfl, fun _ => Or.inl rfl⟩
    · unfold Sched.nodeW; rw [Sched.nodeAt_ksb hw.1]
      exact hnk _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
        (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
    · unfold Sched.nodeW; rw [Sched.nodeAt_ksb hw.1]
      exact hnk _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
        (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
  have hne : ∀ b : U64, P1.Aligned b → (∀ y ∈ Z.T, b.val < y.val + 3528 ∨ y.val + 3576 ≤ b.val) →
      b.val ≠ L.nodeBase s Z.c + 104 → b.val ≠ L.nodeBase s Z.c + 112 → L.mem s' b = L.mem s b :=
    fun b hb h1 h2 h3 => hw.mem_eq hb fun hb' => by
      rcases hV hb' with ⟨y, hy, g1, g2⟩ | g | g
      · rcases h1 y hy with h | h <;> omega
      · exact h2 g
      · exact h3 g
  refine hX.frameStep hw (fun b hb => ?_) (fun b hb hf => ?_) (fun b hb hf => ?_) (fun hb => ?_)
    rfl rfl rfl rfl rfl rfl rfl hSch' ?_ ?_ ?_ hX.fin.1.1.2.2.2.2.2.2
  · -- the words written are the other objects'
    rcases hb with ⟨y, hy, K, h1, h2, rfl⟩ | ⟨o, ho, rfl⟩
    · exact tcb_oobj hy (hT y hy) (by omega) (by omega)
    · left; rw [P1.nodeAt_val hN (by omega)]; omega
  · -- not read by the endpoint relation
    have hPe := hP.ep
    rcases hV hb with ⟨y, hy, g1, g2⟩ | g | g
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
    all_goals exact hE.node b (by omega) (by omega) hf
  · -- not read by the notification relation
    have hPn := hSch.placed
    rcases hV hb with ⟨y, hy, g1, g2⟩ | g | g
    · rcases hf with ⟨n, hn, h1, h2⟩ | ⟨t, ht, h⟩
      · have := hPn.disj n hn y hy; omega
      · have hv := nfootT_val (hT t ht) h
        by_cases e : t = y
        · subst e; omega
        · have := tcb_disj hP.ep ht hy (Ne.symm e); omega
    all_goals
      obtain ⟨o, ho, rfl⟩ := node_word' hc.node (b := b) (by omega) (by omega)
      rcases hf with ⟨n, hn, n1, n2⟩ | ⟨t, ht, h⟩
      · exact hSch.nodeNW o ho (Or.inl ⟨n, hn, n1, n2⟩)
      · have hv := nfootT_val (hT t ht) h
        have := hnd t ht; omega
  · -- not the kernel root
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rcases hV hb with ⟨y, hy, g1, g2⟩ | g | g
    · rcases hko y hy with h' | h' <;> omega
    · omega
    · omega
  · -- the IRQ relation
    have hI := hX.fin.1.1.2.2.2.1
    refine ⟨fun i hi => ?_, fun i hi => hI.node i hi⟩
    have hv := irqStA_val hkf hi
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (fun y hy => by rcases hko y hy with h | h <;> omega)
      (by omega) (by omega)]
    exact hI.st i hi
  · -- the IO-port relation
    have hI := hX.fin.1.1.2.2.2.2.1
    intro p hp
    have hwi : (wI p).val < 1024 := by rw [wI_val hp]; omega
    have hv := ioA_val hkf hwi
    unfold bitOf
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (fun y hy => by rcases hko y hy with h | h <;> omega)
      (by omega) (by omega)]
    exact hI p hp
  · -- the domain schedule
    refine hX.rel.2.2.2.1.frame (fun o ho => ?_) rfl rfl
    have h8 := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    exact hne _ (by unfold P1.Aligned; rw [hv]; omega) (fun y hy => by rcases hko y hy with h | h <;> omega)
      (by omega) (by omega)

set_option maxHeartbeats 4000000 in
/-- **The core's `REPROGRAM` word set**, with the spec's `reprogram_timer`
set, keeps `XTopAt` (`SchedRel.set_reprogram`). -/
theorem XTopAt.reprStep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) :
    XTopAt (L := L) AR Z (L.wr s (L.nodeAt s Z.c layout.node.REPROGRAM) 1#u64) a
      { σ with reprogramTimer := true } := by
  have hSch := hX.fin.1.1.1
  have hP := hX.fin.1.2
  have hE := hX.esa
  obtain ⟨Q, R0, hc, -⟩ := hSch.lists
  have hT := hc.tcbs
  have hN := hc.node
  have hnd := hN.disj
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hko : ∀ t ∈ Z.T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := fun t ht => by
    rcases hc.ksOut t ht with h | h <;> omega
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  have h56 : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have hrv := P1.nodeAt_val hN (off := layout.node.REPROGRAM) (by omega)
  have hA : P1.Aligned (L.nodeAt s Z.c layout.node.REPROGRAM) := P1.nodeAt_aligned hN (by omega) (by omega)
  have hw : P1.WritesIn st s (L.wr s (L.nodeAt s Z.c layout.node.REPROGRAM) 1#u64)
      (· = L.nodeAt s Z.c layout.node.REPROGRAM) := P1.writesIn_wr hA
  have hne : ∀ b : U64, P1.Aligned b → b.val ≠ L.nodeBase s Z.c + 56 →
      L.mem (L.wr s (L.nodeAt s Z.c layout.node.REPROGRAM) 1#u64) b = L.mem s b :=
    fun b hb h => hw.mem_eq hb fun e => h (by rw [e, hrv, h56])
  refine hX.frameStep hw (fun b hb => ?_) (fun b hb hf => ?_) (fun b hb hf => ?_) (fun hb => ?_)
    rfl rfl rfl rfl rfl rfl rfl hSch.set_reprogram.1 ?_ ?_ ?_ hX.fin.1.1.2.2.2.2.2.2
  · subst hb; left; omega
  · subst hb; exact hE.node _ (by omega) (by omega) hf
  · subst hb
    rcases hf with ⟨n, hn, n1, n2⟩ | ⟨t, ht, h⟩
    · exact hSch.nodeNW _ (by omega) (Or.inl ⟨n, hn, n1, n2⟩)
    · have hv := nfootT_val (hT t ht) h
      have := hnd t ht; omega
  · have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have := congrArg UScalar.val hb
    rw [hkv, hrv] at this; omega
  · have hI := hX.fin.1.1.2.2.2.1
    refine ⟨fun i hi => ?_, fun i hi => hI.node i hi⟩
    have hv := irqStA_val hkf hi
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (by omega)]
    exact hI.st i hi
  · have hI := hX.fin.1.1.2.2.2.2.1
    intro p hp
    have hwi : (wI p).val < 1024 := by rw [wI_val hp]; omega
    have hv := ioA_val hkf hwi
    unfold bitOf
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (by omega)]
    exact hI p hp
  · refine hX.rel.2.2.2.1.frame (fun o ho => ?_) rfl rfl
    have h8 := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    exact hne _ (by unfold P1.Aligned; rw [hv]; omega) (by omega)

/-- **Hypothesis: `timer::insert`'s footprint** [W] (P1's fine footprint, to
be exported with its `Cur0W` work): after the restart, arming `p`'s timer
writes only timer words (`TmW`: the TCB timer fields 3528..3576 and node
words 104, 112 of core `c`), then possibly sets the core's `REPROGRAM`
word. -/
def TimerInsHyp (T : Set U64) (c : U64) (s : S) (ct p : U64) : Prop :=
  ∀ s1 d b, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    timer.insert st s1 p d b ⦃ s' => ∃ sm, P1.WritesIn st s1 sm (TmW (L := L) T c s1) ∧
      (s' = sm ∨ s' = L.wr sm (L.nodeAt sm c layout.node.REPROGRAM) 1#u64) ⦄

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
the restart, `timer::insert` (`TimerInsHyp` [W]; `XTopAt.tmStep`,
`XTopAt.reprStep`), the spec's reprogram flag chosen as FL4's. -/
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
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (hTI : TimerInsHyp (L := L) Z.T Z.c s ct p)
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
  refine WP.spec_bind (hTI s1 y0 y1 hs1) ?_
  rintro s2 ⟨sm, hw, hs2⟩
  have hXm := hX1.tmStep hKA1 hw
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
  rcases hs2 with rfl | rfl
  · have hm := setTimer_memB blk call don σ1 p.bv y0.bv y1.bv false
    rw [Bool.or_false] at hm
    exact fin σ1 hm hXm
  · have hm := setTimer_memB blk call don σ1 p.bv y0.bv y1.bv true
    rw [Bool.or_true] at hm
    exact fin _ hm hXm.reprStep

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
    (hTI : TimerInsHyp (L := L) Z.T Z.c s ct p) :
    TcbXOpen1 (L := L) arI (XTop (L := L) AR) s ar σ lbl p ⟨length, buf, call, cslotAddr sl, extra⟩ blk call
      don slbl (argsU.map UScalar.bv) ci sl excaps buffer := by
  refine ⟨?_⟩
  rintro rfl
  obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .setTimer by
    simp [tcbExtOf])
  exact tcb_set_timerX arI s ar σ hX hKA hC hDI p slbl hg he length buf ct hct argsU hlen hargs hcur hact
    (hstall' p) hTI call _ extra blk don ci sl excaps buffer

end

end

end Fl4Proofs.P3
