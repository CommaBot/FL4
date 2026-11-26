/-
P3 (line mmuAD, gen 20): **`JExtV` / `RunVmB` kept by the extracted VT-x binding steps** (`vcpu.stall`,
`vcpu.report`, `vcpu.detach`, `vcpu.decode` at `X86VCPUSetTCB`; fl4-core vcpu.rs l. 706-735, 853-860), stated
WP-style over the extracted functions as the P1 / P3 files do.

## The words the extension reads, and what a step must miss

* `JW V th`: the words `JExtV V X th` reads — both words of every slot of `th`, every TCB's VCPU word
  (`tVcpuA`, offset 3664) and every `V` VCPU's `TCB` word (`vTcbA`, offset 0x5000). `SW th`: every TCB's state
  word (`P1.stA`), which `RunVmB` reads besides the VCPU words.
* `JExtV.of_writes`: a step whose `WritesIn` footprint misses `JW` keeps `JExtV` (the bridge from P1-style
  footprints to `JExtV.of_eq`). `RunVmB.of_foot`: a footprint whose state words are written to a value other than
  `TS_RUNNING_VM` (or with the VCPU word nonzero) and whose VCPU words are written only on threads not in
  `TS_RUNNING_VM` (or to nonzero) keeps `RunVmB`. `JExtV.unbind_w` / `JExtV.bind_w`: gen 19's `unbind` / `bind`
  with their frame premises derived from a two-word `WritesIn` footprint and the placement `JWPl`.

## Footprints of the extracted functions (proved here)

* `vcpu_stall_w`: `vcpu.stall` writes at most the current core's `IPI_PENDING` node word (P1's
  `smp.remote_tcb_stall.spec`).
* `sched_tcb_w`, `sts_w`: `sched.schedule_tcb` writes at most the current core's `SCHED_ACTION` node word;
  `sched.set_thread_state t x` writes `t`'s state word (left at `x`) and that word.
* `set_mr_w`, `vcpu_report_w`: `vcpu.report` (via P1's generic `vcpu.report.gen`) writes at most `P1.RepW t U`
  (the thread's register words and the user words `U` of its IPC buffer), the bound VCPU's `PENDING` word, the
  thread's state word (left at `TS_RUNNING`) and `SCHED_ACTION`.

## Theorems on the extracted steps

* **`vcpu_detach_jv`**: `vcpu.detach t` keeps `JExtV V X th` and `RunVmB th`, leaves `t`'s VCPU word 0 and the
  `TCB` word of `t`'s old VCPU 0, and writes only those two words plus the clean words `CW` (`DetPost`).
* **`vcpu_decode_settcb_jv`**: `vcpu.decode` at label `X86VCPUSetTCB` on a VCPU `v ∈ V` keeps `JExtV V X th` and
  `RunVmB th` (both detaches, the binding writes `JExtV.bind_w`, the caller restarted).

## Named premises (all [J]: placement / typing facts of the joint state, not derived here)

* `JWPl V th` [J]: the `JW` / `SW` words aligned, state words none of `JW`, slot words / TCB VCPU words / `V`'s
  `TCB` words pairwise apart (TCB, CNode and VCPU objects disjoint, the offsets 3664 / 3328 / 0x5000 inside their
  objects; P3's `TcbPlaced`, `Placed`, P1's `VcpuPl` give them natively).
* `DetPl V th Ub` [J]: `JWPl`, no TCB at 0, every TCB a `P1.TcbAddr`, each TCB's user-buffer word set `Ub t`
  aligned, its `RepW` words and `V`'s `PENDING` / `SVM_CPU` words aligned and none of `JW` / `SW` (register words
  of a TCB and VCPU-internal words; the IPC buffer is a user frame, P1's `XferHyps.buf`).
* `DetAt V th Ub s` [J]: the current core's node placed (`P1.NodePlaced`), its `IPI_PENDING` / `SCHED_ACTION` words
  none of `JW` / `SW` (kernel-global area), and the IPC-buffer lookup of every TCB, at every state reached from `s`
  by `JW` / `CW` writes, lands in `Ub t` (P1's `XferHyps.buf` / `BufOK`).
* `vcpu_decode_settcb_jv`'s `hex` [J] (the extra cap slot is a slot of `th`, a `Thread` cap there names a TCB;
  P1's `DecPre.extra`) and `hct` [J] (the current thread is a TCB; P3's `CurT`).

No [P] / [W] / [S] premise. No existing statement changed.
-/
import Fl4Proofs.P3.JExtV
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem wadd_inj {a b k : U64} (h : core.num.U64.wrapping_add a k = core.num.U64.wrapping_add b k) : a = b := by
  have e := congrArg UScalar.val h
  have ha := a.hBounds
  have hb := b.hBounds
  have hk := k.hBounds
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, UScalar.size] at e ha hb hk
  apply UScalar.eq_of_val_eq
  omega

theorem tVcpuA_inj {a b : U64} (h : tVcpuA a = tVcpuA b) : a = b := wadd_inj h
theorem vTcbA_inj {a b : U64} (h : vTcbA a = vTcbA b) : a = b := wadd_inj h
theorem stA_inj {a b : U64} (h : P1.stA a = P1.stA b) : a = b := wadd_inj h

/-- A VCPU's `PENDING` word. -/
def pendA (v : U64) : U64 := core.num.U64.wrapping_add v vcpu.PENDING
/-- A VCPU's `SVM_CPU` word. -/
def svmA (v : U64) : U64 := core.num.U64.wrapping_add v vcpu.SVM_CPU

/-- The words `JExtV V X th` reads (module docstring). -/
def JW (V : Set U64) (th : TypedHeap) (b : U64) : Prop :=
  (∃ y, IsSlot th y ∧ (b = y ∨ b = wordOf y 8#u64)) ∨ (∃ t, th t = some .tcb ∧ b = tVcpuA t) ∨
    (∃ v ∈ V, b = vTcbA v)

/-- The TCB state words (`RunVmB` reads them). -/
def SW (th : TypedHeap) (b : U64) : Prop := ∃ t, th t = some .tcb ∧ b = P1.stA t

/-- **The placement of the extension's words** [J] (module docstring). -/
structure JWPl (V : Set U64) (th : TypedHeap) : Prop where
  jw : ∀ b, JW V th b → P1.Aligned b
  sw : ∀ b, SW th b → P1.Aligned b
  swjw : ∀ b, SW th b → ¬ JW V th b
  slv : ∀ y, IsSlot th y → ∀ t, th t = some .tcb → y ≠ tVcpuA t ∧ wordOf y 8#u64 ≠ tVcpuA t
  slb : ∀ y, IsSlot th y → ∀ v ∈ V, y ≠ vTcbA v ∧ wordOf y 8#u64 ≠ vTcbA v
  vb : ∀ t, th t = some .tcb → ∀ v ∈ V, tVcpuA t ≠ vTcbA v

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The current core's `IPI_PENDING` node word. -/
def ipiA (st : machine.Store S) [L : P1.LawfulStore st] (s : S) : U64 :=
  L.nodeAt s (L.cpu s) layout.node.IPI_PENDING
/-- The current core's `SCHED_ACTION` node word. -/
def actA (st : machine.Store S) [L : P1.LawfulStore st] (s : S) : U64 :=
  L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION
/-- The current core's `CUR_THREAD` node word. -/
def curA (st : machine.Store S) [L : P1.LawfulStore st] (s : S) : U64 :=
  L.nodeAt s (L.cpu s) layout.node.CUR_THREAD

theorem ipiA_of {s s' : S} {W : U64 → Prop} (h : P1.WritesIn st s s' W) : ipiA st s' = ipiA st s := by
  unfold ipiA; rw [h.2.1, P1.nodeAt_of_ksb h.1]
theorem actA_of {s s' : S} {W : U64 → Prop} (h : P1.WritesIn st s s' W) : actA st s' = actA st s := by
  unfold actA; rw [h.2.1, P1.nodeAt_of_ksb h.1]
theorem curA_of {s s' : S} {W : U64 → Prop} (h : P1.WritesIn st s s' W) : curA st s' = curA st s := by
  unfold curA; rw [h.2.1, P1.nodeAt_of_ksb h.1]

theorem writesIn_or {s s' : S} {a : U64} (ha : P1.Aligned a) (h : s' = s ∨ ∃ x, s' = L.wr s a x) :
    P1.WritesIn st s s' (· = a) := by
  rcases h with rfl | ⟨x, rfl⟩
  · exact P1.WritesIn.refl _ _
  · exact P1.writesIn_wr ha

variable {V X : Set U64} {th : TypedHeap} {s s' : S}

/-! ## From footprints to the extension -/

/-- **A footprint missing `JW` keeps `JExtV`.** -/
theorem JExtV.of_writes (E : JExtV (L := L) V X th s) (P : JWPl V th) {W : U64 → Prop}
    (hW : P1.WritesIn st s s' W) (hd : ∀ b, W b → ¬ JW V th b) : JExtV (L := L) V X th s' := by
  have k : ∀ b, JW V th b → L.mem s' b = L.mem s b := fun b hb =>
    hW.mem_eq (P.jw b hb) fun hw => hd b hw hb
  refine E.of_eq (fun y hy => ?_) (fun t ht => k _ (Or.inr (Or.inl ⟨t, ht, rfl⟩)))
    (fun v hv => k _ (Or.inr (Or.inr ⟨v, hv, rfl⟩)))
  unfold capV
  rw [k y (Or.inl ⟨y, hy, Or.inl rfl⟩), k _ (Or.inl ⟨y, hy, Or.inr rfl⟩)]

/-- **`RunVmB` from a footprint**: written state words end outside `TS_RUNNING_VM` or with the VCPU word nonzero;
written VCPU words belong to threads not in `TS_RUNNING_VM` before, or end nonzero. -/
theorem RunVmB.of_foot (R : RunVmB (L := L) th s) (P : JWPl V th) {W : U64 → Prop}
    (hW : P1.WritesIn st s s' W)
    (hs : ∀ t, th t = some .tcb → W (P1.stA t) →
      L.mem s' (P1.stA t) ≠ 8#u64 ∨ L.mem s' (tVcpuA t) ≠ 0#u64)
    (hv : ∀ t, th t = some .tcb → W (tVcpuA t) →
      L.mem s (P1.stA t) ≠ 8#u64 ∨ L.mem s' (tVcpuA t) ≠ 0#u64) : RunVmB (L := L) th s' := by
  intro t ht h8
  have aS : P1.Aligned (P1.stA t) := P.sw _ ⟨t, ht, rfl⟩
  have aV : P1.Aligned (tVcpuA t) := P.jw _ (Or.inr (Or.inl ⟨t, ht, rfl⟩))
  by_cases ws : W (P1.stA t)
  · rcases hs t ht ws with h | h
    · exact absurd h8 h
    · exact h
  · have h8' : L.mem s (P1.stA t) = 8#u64 := by rw [← hW.mem_eq aS ws]; exact h8
    by_cases wv : W (tVcpuA t)
    · rcases hv t ht wv with h | h
      · exact absurd h8' h
      · exact h
    · rw [hW.mem_eq aV wv]; exact R t ht h8'

/-- `RunVmB` across a footprint none of whose words is a state or VCPU word. -/
theorem RunVmB.of_clean (R : RunVmB (L := L) th s) (P : JWPl V th) {W : U64 → Prop}
    (hW : P1.WritesIn st s s' W) (hd : ∀ b, W b → ¬ JW V th b ∧ ¬ SW th b) : RunVmB (L := L) th s' :=
  R.of_foot P hW (fun t ht hw => ((hd _ hw).2 ⟨t, ht, rfl⟩).elim)
    (fun t ht hw => ((hd _ hw).1 (Or.inr (Or.inl ⟨t, ht, rfl⟩))).elim)

/-- **Unbinding from a two-word footprint** (`JExtV.unbind` with its frames from `JWPl`). -/
theorem JExtV.unbind_w (E : JExtV (L := L) V X th s) (P : JWPl V th) {t v : U64} (ht : th t = some .tcb)
    (hv : v ∈ V) (htv : L.mem s (tVcpuA t) = v) (hvt : L.mem s (vTcbA v) = t)
    (hW : P1.WritesIn st s s' (fun b => b = vTcbA v ∨ b = tVcpuA t))
    (h1 : L.mem s' (tVcpuA t) = 0#u64) (h2 : L.mem s' (vTcbA v) = 0#u64) : JExtV (L := L) V X th s' := by
  refine E.unbind hv htv hvt (fun y hy => ?_) h1 h2 (fun t' ht' hne => ?_) (fun w hw hne => ?_)
  · unfold capV
    rw [hW.mem_eq (P.jw _ (Or.inl ⟨y, hy, Or.inl rfl⟩)) (by
          rintro (e | e)
          · exact (P.slb y hy v hv).1 e
          · exact (P.slv y hy t ht).1 e),
        hW.mem_eq (P.jw _ (Or.inl ⟨y, hy, Or.inr rfl⟩)) (by
          rintro (e | e)
          · exact (P.slb y hy v hv).2 e
          · exact (P.slv y hy t ht).2 e)]
  · exact hW.mem_eq (P.jw _ (Or.inr (Or.inl ⟨t', ht', rfl⟩))) (by
      rintro (e | e)
      · exact P.vb t' ht' v hv e
      · exact hne (tVcpuA_inj e))
  · exact hW.mem_eq (P.jw _ (Or.inr (Or.inr ⟨w, hw, rfl⟩))) (by
      rintro (e | e)
      · exact hne (vTcbA_inj e)
      · exact P.vb t ht w hw e.symm)

/-- **Binding from a two-word footprint** (`JExtV.bind` with its frames from `JWPl`). -/
theorem JExtV.bind_w (E : JExtV (L := L) V X th s) (P : JWPl V th) {t v : U64} (ht : th t = some .tcb)
    (hv : v ∈ V) (hw0 : L.mem s (tVcpuA t) = 0#u64) (hb0 : L.mem s (vTcbA v) = 0#u64) (h0 : th 0#u64 ≠ some .tcb)
    (hW : P1.WritesIn st s s' (fun b => b = vTcbA v ∨ b = tVcpuA t))
    (h1 : L.mem s' (tVcpuA t) = v) (h2 : L.mem s' (vTcbA v) = t) : JExtV (L := L) V X th s' := by
  refine E.bind ht hv hw0 hb0 h0 (fun y hy => ?_) h1 h2 (fun t' ht' hne => ?_) (fun w hw hne => ?_)
  · unfold capV
    rw [hW.mem_eq (P.jw _ (Or.inl ⟨y, hy, Or.inl rfl⟩)) (by
          rintro (e | e)
          · exact (P.slb y hy v hv).1 e
          · exact (P.slv y hy t ht).1 e),
        hW.mem_eq (P.jw _ (Or.inl ⟨y, hy, Or.inr rfl⟩)) (by
          rintro (e | e)
          · exact (P.slb y hy v hv).2 e
          · exact (P.slv y hy t ht).2 e)]
  · exact hW.mem_eq (P.jw _ (Or.inr (Or.inl ⟨t', ht', rfl⟩))) (by
      rintro (e | e)
      · exact P.vb t' ht' v hv e
      · exact hne (tVcpuA_inj e))
  · exact hW.mem_eq (P.jw _ (Or.inr (Or.inr ⟨w, hw, rfl⟩))) (by
      rintro (e | e)
      · exact hne (vTcbA_inj e)
      · exact P.vb t ht w hw e.symm)

end

/-! ## Footprints of the extracted functions -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

/-- **`vcpu.stall`** writes at most the current core's `IPI_PENDING` word. -/
theorem vcpu_stall_w (hA : P0.ArchTotal ar) (s : S) (a : A) (v : U64) (ha : P1.Aligned (ipiA st s)) :
    vcpu.stall st ar s a v ⦃ r => P1.WritesIn st s r.1 (· = ipiA st s) ⦄ := by
  unfold vcpu.stall
  refine WP.spec_bind (hA.vcpu_barrier a) fun a1 _ => ?_
  unfold vcpu.get
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun t _ => ?_
  refine WP.spec_bind (P1.obj.Tcb.is_null.spec t) fun b _ => ?_
  split
  · exact (WP.spec_ok _).2 (P1.WritesIn.refl _ _)
  · exact WP.spec_mono (P1.smp.remote_tcb_stall.spec hA s a1 t) fun ⟨s', a'⟩ h => writesIn_or ha h

/-- **`sched.schedule_tcb`** writes at most the current core's `SCHED_ACTION` word. -/
theorem sched_tcb_w (s : S) (t : obj.Tcb) :
    sched.schedule_tcb st s t ⦃ s' => s' = s ∨ ∃ x, s' = L.wr s (actA st s) x ⦄ := by
  unfold sched.schedule_tcb
  refine WP.spec_bind (P1.sched.cur_thread.spec s) fun t1 _ => ?_
  refine WP.spec_bind (P1.tcb_eq.blk t t1) fun b _ => ?_
  split
  · refine WP.spec_bind (P1.sched.action.spec s) fun i _ => ?_
    split
    · refine WP.spec_bind (P1.sched.is_schedulable.spec s t) fun b1 _ => ?_
      split
      · exact (WP.spec_ok _).2 (Or.inl rfl)
      · exact WP.spec_mono (P1.sched.set_action.spec s _) fun s' e => Or.inr ⟨_, e⟩
    · exact (WP.spec_ok _).2 (Or.inl rfl)
  · exact (WP.spec_ok _).2 (Or.inl rfl)

/-- **`sched.set_thread_state t x`** writes `t`'s state word (left at `x`) and `SCHED_ACTION`. -/
theorem sts_w (s : S) (t x : U64) (hsa : P1.Aligned (P1.stA t)) (haa : P1.Aligned (actA st s))
    (hne : actA st s ≠ P1.stA t) :
    sched.set_thread_state st s t x ⦃ s' => P1.WritesIn st s s' (fun b => b = P1.stA t ∨ b = actA st s) ∧
      L.mem s' (P1.stA t) = x ⦄ := by
  unfold sched.set_thread_state
  refine WP.spec_bind (P1.obj.Tcb.set_state.spec s t x) fun s2 e2 => ?_
  subst e2
  have w2 : P1.WritesIn st s (L.wr s (P1.stA t) x) (· = P1.stA t) := P1.writesIn_wr hsa
  have m2 : L.mem (L.wr s (P1.stA t) x) (P1.stA t) = x := by rw [L.mem_wr _ _ _ _ hsa hsa, if_pos rfl]
  have ea : actA st (L.wr s (P1.stA t) x) = actA st s := actA_of w2
  refine WP.spec_mono (sched_tcb_w _ t) fun s3 h3 => ?_
  rcases h3 with rfl | ⟨y, rfl⟩
  · exact ⟨w2.mono fun b hb => Or.inl hb, m2⟩
  · rw [ea]
    refine ⟨(w2.trans (P1.writesIn_wr haa)).mono fun b hb => hb.elim Or.inl Or.inr, ?_⟩
    rw [L.mem_wr _ _ _ _ haa hsa, if_neg hne, m2]

/-- A message-register write (`msg.set_mr`): a register word of the thread or a word of its IPC buffer
(`P1.msg.set_mr.xw` with only the buffer words' alignment). -/
theorem set_mr_w {U : Set U64} (s : S) {t buf i v : U64} (hta : P1.TcbAddr t) (hb : P1.BufOK U buf)
    (hU : ∀ b ∈ U, P1.Aligned b) (hi : i.val < 127) :
    msg.set_mr st s t buf i v ⦃ r => P1.WritesIn st s r.2 (P1.RepW t U) ⦄ := by
  unfold msg.set_mr
  split
  · refine WP.spec_bind (P1.msg.msg_register.lt i) fun r hr => ?_
    refine WP.spec_bind (P1.obj.Tcb.set_reg.wrS s t r v hta hr) fun s1 hs1 => ?_
    obtain ⟨K, hK, e⟩ := hs1
    subst e
    simp only [lift, bind_ok]
    exact (WP.spec_ok _).2 ((P1.writesIn_wr (P1.field_aligned hta (by omega) (by omega))).mono fun b e =>
      Or.inl ⟨K, by omega, by omega, by omega, e⟩)
  · split
    · rename_i hne
      have h0 : buf ≠ 0#u64 := by simpa using hne
      simp only [lift, bind_ok]
      have hi1 : (core.num.U64.wrapping_add i 1#u64).val < 128 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      have hu := hb h0 _ hi1
      refine WP.spec_bind (Pₘ := fun s1 => P1.WritesIn st s s1 (P1.RepW t U)) ?_ fun s1 h1 => (WP.spec_ok _).2 h1
      unfold msg.buf_set
      simp only [lift, bind_ok]
      refine WP.spec_mono (P1.LawfulStore.write_spec s _ v) fun s' e => ?_
      subst e
      exact (P1.writesIn_wr (hU _ hu)).mono fun b e => Or.inr (e ▸ hu)
    · exact (WP.spec_ok _).2 (P1.WritesIn.refl _ _)

set_option maxHeartbeats 4000000 in
/-- **`vcpu.report`'s footprint** (P1's `vcpu.report.gen`): the `RepW` words, the bound VCPU's `PENDING` word, the
thread's state word (left at `TS_RUNNING`) and `SCHED_ACTION`. -/
theorem vcpu_report_w (hA : P0.ArchTotal ar) {s : S} (a : A) {t badge : U64} {U : Set U64}
    (hta : P1.TcbAddr t) (hU : ∀ b ∈ U, P1.Aligned b)
    (hbuf : msg.lookup_ipc_buffer st s true t ⦃ P1.BufOK U ⦄)
    (hpa : P1.Aligned (pendA (L.mem s (tVcpuA t)))) (hsa : P1.Aligned (P1.stA t))
    (haa : P1.Aligned (actA st s)) (hne : actA st s ≠ P1.stA t) :
    vcpu.report st ar s a t badge ⦃ s' => P1.WritesIn st s s' (fun b => P1.RepW t U b ∨
      b = pendA (L.mem s (tVcpuA t)) ∨ b = P1.stA t ∨ b = actA st s) ∧
      L.mem s' (P1.stA t) = sched.TS_RUNNING ⦄ := by
  refine P1.vcpu.report.gen (Bok := P1.BufOK U) (vOk := fun v => v = L.mem s (tVcpuA t))
    (P := fun s1 => P1.WritesIn st s s1 (fun b => P1.RepW t U b ∨ b = pendA (L.mem s (tVcpuA t)))) hA
    ⟨fun s1 b i v hb h1 hi => WP.spec_mono (set_mr_w s1 hta hb hU (by omega)) fun r hr =>
        (h1.trans hr).mono fun b hb => hb.elim id Or.inl,
     fun s1 r v h1 hr => WP.spec_mono (P1.obj.Tcb.set_reg.wrS s1 t r v hta (by
        rcases hr with rfl | rfl | rfl <;>
          simp [layout.reg.MSG_INFO, layout.reg.BADGE, layout.reg.FAULT_IP, layout.reg.RSI, layout.reg.RDI]))
        fun s' ⟨K, hK, e⟩ => by
          subst e
          have hr' : r.val < 384 := by
            rcases hr with rfl | rfl | rfl <;>
              simp [layout.reg.MSG_INFO, layout.reg.BADGE, layout.reg.FAULT_IP, layout.reg.RSI, layout.reg.RDI]
          exact (h1.trans (P1.writesIn_wr (P1.field_aligned hta (by omega) (by omega)))).mono fun b hb =>
            hb.elim id fun e => Or.inl (Or.inl ⟨K, by omega, by omega, by omega, e⟩),
     fun s1 v h1 hv => by
        subst hv
        unfold vcpu.set
        simp only [lift, bind_ok]
        exact WP.spec_mono (P1.LawfulStore.write_spec s1 _ _) fun s' e => by
          subst e
          exact (h1.trans (P1.writesIn_wr hpa)).mono fun b hb => hb.elim id Or.inr⟩
    (fun s1 h1 => WP.spec_mono (sts_w s1 t sched.TS_RUNNING hsa (by rw [actA_of h1]; exact haa)
      (by rw [actA_of h1]; exact hne)) fun s' ⟨w, e⟩ => ⟨by
        rw [actA_of h1] at w
        exact (h1.trans w).mono fun b hb => hb.elim (fun h => h.elim Or.inl fun e => Or.inr (Or.inl e))
          fun h => h.elim (fun e => Or.inr (Or.inr (Or.inl e))) fun e => Or.inr (Or.inr (Or.inr e)), e⟩)
    (P1.WritesIn.refl _ _) hbuf (fun _ _ => rfl)

end

/-! ## `vcpu.detach` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

/-- The words a detach may write besides the binding words (module docstring): the current core's
`IPI_PENDING` / `SCHED_ACTION`, every TCB's `RepW` words (user buffer words `Ub t`) and state word, every `V`
VCPU's `PENDING` / `SVM_CPU` words. -/
def CW (st : machine.Store S) [L : P1.LawfulStore st] (V : Set U64) (th : TypedHeap) (Ub : U64 → Set U64)
    (s : S) (b : U64) : Prop :=
  b = ipiA st s ∨ b = actA st s ∨ (∃ t, th t = some .tcb ∧ (P1.RepW t (Ub t) b ∨ b = P1.stA t)) ∨
    (∃ v ∈ V, b = pendA v ∨ b = svmA v)

/-- **The static placement a detach needs** [J] (module docstring). -/
structure DetPl (V : Set U64) (th : TypedHeap) (Ub : U64 → Set U64) : Prop where
  pl : JWPl V th
  h0 : th 0#u64 ≠ some .tcb
  ta : ∀ t, th t = some .tcb → P1.TcbAddr t
  ua : ∀ t, th t = some .tcb → ∀ b ∈ Ub t, P1.Aligned b
  rep : ∀ t, th t = some .tcb → ∀ b, P1.RepW t (Ub t) b → ¬ JW V th b ∧ ¬ SW th b
  vca : ∀ v ∈ V, P1.Aligned (pendA v) ∧ P1.Aligned (svmA v)
  vc : ∀ v ∈ V, ∀ b, (b = pendA v ∨ b = svmA v) → ¬ JW V th b ∧ ¬ SW th b

/-- **The per-state facts a detach needs** [J] (module docstring). -/
structure DetAt (st : machine.Store S) [L : P1.LawfulStore st] (V : Set U64) (th : TypedHeap)
    (Ub : U64 → Set U64) (s : S) : Prop where
  node : ∃ T, P1.NodePlaced st T s (L.cpu s)
  nd : ∀ b, (b = ipiA st s ∨ b = actA st s) → ¬ JW V th b ∧ ¬ SW th b
  buf : ∀ s1, P1.WritesIn st s s1 (fun b => JW V th b ∨ CW st V th Ub s b) → ∀ t, th t = some .tcb →
    msg.lookup_ipc_buffer st s1 true t ⦃ P1.BufOK (Ub t) ⦄

variable {V X : Set U64} {th : TypedHeap} {Ub : U64 → Set U64}

theorem CW.of {s s' : S} {W : U64 → Prop} (h : P1.WritesIn st s s' W) {b : U64} (hb : CW st V th Ub s' b) :
    CW st V th Ub s b := by
  unfold CW at hb ⊢; rw [ipiA_of h, actA_of h] at hb; exact hb

theorem CW.njw (D : DetPl V th Ub) {s : S} (Da : DetAt st V th Ub s) {b : U64} (hb : CW st V th Ub s b) :
    ¬ JW V th b := by
  rcases hb with e | e | ⟨t, ht, h | e⟩ | ⟨v, hv, h⟩
  · exact (Da.nd b (Or.inl e)).1
  · exact (Da.nd b (Or.inr e)).1
  · exact (D.rep t ht b h).1
  · exact D.pl.swjw b ⟨t, ht, e⟩
  · exact (D.vc v hv b h).1

theorem DetAt.ipiA_al {s : S} (Da : DetAt st V th Ub s) : P1.Aligned (ipiA st s) := by
  obtain ⟨T, hN⟩ := Da.node
  exact P1.nodeAt_aligned hN (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING])

theorem DetAt.actA_al {s : S} (Da : DetAt st V th Ub s) : P1.Aligned (actA st s) := by
  obtain ⟨T, hN⟩ := Da.node
  exact P1.nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])

theorem DetAt.curA_al {s : S} (Da : DetAt st V th Ub s) : P1.Aligned (curA st s) := by
  obtain ⟨T, hN⟩ := Da.node
  exact P1.nodeAt_aligned hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])

theorem DetAt.cur_ne_ipi {s : S} (Da : DetAt st V th Ub s) : curA st s ≠ ipiA st s := by
  obtain ⟨T, hN⟩ := Da.node
  exact P1.nodeAt_ne hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.IPI_PENDING])
    (by simp [layout.node.CUR_THREAD, layout.node.IPI_PENDING])

/-- `DetAt` carried along a `JW` / `CW` footprint. -/
theorem DetAt.mono {s s' : S} (Da : DetAt st V th Ub s)
    (h : P1.WritesIn st s s' (fun b => JW V th b ∨ CW st V th Ub s b)) : DetAt st V th Ub s' where
  node := by obtain ⟨T, hN⟩ := Da.node; exact ⟨T, by rw [h.2.1]; exact hN.ksb h.1⟩
  nd b hb := Da.nd b (by rw [ipiA_of h, actA_of h] at hb; exact hb)
  buf s1 h1 t ht := Da.buf s1 ((h.trans h1).mono fun b hb => hb.elim id fun h' => h'.elim Or.inl
    fun c => Or.inr (CW.of h c)) t ht

/-- **What a detach of `t` leaves** (module docstring). -/
structure DetPost (st : machine.Store S) [L : P1.LawfulStore st] (V X : Set U64) (th : TypedHeap)
    (Ub : U64 → Set U64) (t : U64) (s s' : S) : Prop where
  ext : JExtV (L := L) V X th s'
  rvm : RunVmB (L := L) th s'
  w0 : L.mem s' (tVcpuA t) = 0#u64
  b0 : ∀ w ∈ V, L.mem s (tVcpuA t) = w → L.mem s' (vTcbA w) = 0#u64
  foot : P1.WritesIn st s s' (fun b => (L.mem s (tVcpuA t) ≠ 0#u64 ∧
    (b = tVcpuA t ∨ b = vTcbA (L.mem s (tVcpuA t)))) ∨ CW st V th Ub s b)

theorem DetPost.footJ {t : U64} {s s' : S} (Dp : DetPost st V X th Ub t s s') (ht : th t = some .tcb)
    (hb : L.mem s (tVcpuA t) ≠ 0#u64 → L.mem s (tVcpuA t) ∈ V) :
    P1.WritesIn st s s' (fun b => JW V th b ∨ CW st V th Ub s b) :=
  Dp.foot.mono fun b h => by
    rcases h with ⟨h0, e | e⟩ | c
    · exact Or.inl (Or.inr (Or.inl ⟨t, ht, e⟩))
    · exact Or.inl (Or.inr (Or.inr ⟨_, hb h0, e⟩))
    · exact Or.inr c

set_option maxHeartbeats 8000000 in
/-- **`vcpu.detach` keeps the extension** (module docstring): `JExtV V X th` and `RunVmB th` afterwards, `t`'s VCPU
word 0, its old VCPU's `TCB` word 0, the writes those two words and `CW` words. -/
theorem vcpu_detach_jv (hA : P0.ArchTotal ar) (D : DetPl V th Ub) {s : S} (Da : DetAt st V th Ub s)
    (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s) (a : A) {t : U64} (ht : th t = some .tcb) :
    vcpu.detach st ar s a t ⦃ r => DetPost st V X th Ub t s r.1 ⦄ := by
  have P := D.pl
  have JWt : JW V th (tVcpuA t) := Or.inr (Or.inl ⟨t, ht, rfl⟩)
  have aT : P1.Aligned (tVcpuA t) := P.jw _ JWt
  unfold vcpu.detach vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  have ev' : v = L.mem s (tVcpuA t) := ev
  split
  · rename_i hv0
    have h0 : L.mem s (tVcpuA t) = 0#u64 := by rw [← ev']; exact hv0
    exact (WP.spec_ok _).2 ⟨E, R, h0,
      fun w hw (e : L.mem s (tVcpuA t) = w) => absurd (e.symm.trans h0) (E.nz w hw), P1.WritesIn.refl _ _⟩
  rename_i hv0
  have hvne : L.mem s (tVcpuA t) ≠ 0#u64 := by rw [← ev']; exact hv0
  obtain ⟨hvV, hvt⟩ := (E.bnd t ht).resolve_left hvne
  rw [← ev'] at hvV hvt
  have JWb : JW V th (vTcbA v) := Or.inr (Or.inr ⟨v, hvV, rfl⟩)
  have aB : P1.Aligned (vTcbA v) := P.jw _ JWb
  have aS : P1.Aligned (svmA v) := (D.vca v hvV).2
  have clS : ∀ b, b = svmA v → ¬ JW V th b ∧ ¬ SW th b := fun b e => D.vc v hvV b (Or.inr e)
  refine WP.spec_bind (vcpu_stall_w hA s a v Da.ipiA_al) ?_
  rintro ⟨s1, a1⟩ w1
  try simp only [uncurry_apply_pair]
  have w1' : P1.WritesIn st s s1 (· = ipiA st s) := w1
  have cl1 : ∀ b, b = ipiA st s → ¬ JW V th b ∧ ¬ SW th b := fun b e => Da.nd b (Or.inl e)
  have E1 := E.of_writes P w1' fun b hb => (cl1 b hb).1
  have R1 := R.of_clean P w1' cl1
  have kJ : ∀ b, JW V th b → L.mem s1 b = L.mem s b := fun b hb =>
    w1'.mem_eq (P.jw b hb) fun e => (cl1 b e).1 hb
  have Da1 : DetAt st V th Ub s1 := Da.mono (w1'.mono fun b e => Or.inr (Or.inl e))
  refine WP.spec_bind (P1.obj.Tcb.state.spec s1 t) fun i ei => ?_
  refine WP.spec_bind (Pₘ := fun s2 => P1.WritesIn st s1 s2 (fun b => P1.RepW t (Ub t) b ∨ b = pendA v ∨
      b = P1.stA t ∨ b = actA st s) ∧ L.mem s2 (P1.stA t) ≠ 8#u64) ?_ ?_
  · split
    · have hpa : P1.Aligned (pendA (L.mem s1 (tVcpuA t))) := by
        rw [kJ _ JWt, ← ev']; exact (D.vca v hvV).1
      have hne : actA st s1 ≠ P1.stA t := fun e => (Da1.nd _ (Or.inr rfl)).2 ⟨t, ht, e⟩
      refine WP.spec_mono (vcpu_report_w hA a1 (D.ta t ht) (D.ua t ht) (Da1.buf s1 (P1.WritesIn.refl _ _) t ht)
        hpa (P.sw _ ⟨t, ht, rfl⟩) Da1.actA_al hne) fun s2 ⟨w, e⟩ => ⟨?_, by rw [e]; simp [sched.TS_RUNNING]⟩
      rw [kJ _ JWt, ← ev', actA_of w1'] at w
      exact w
    · rename_i hi8
      exact (WP.spec_ok _).2 ⟨P1.WritesIn.refl _ _, by rw [← ei]; simpa [sched.TS_RUNNING_VM] using hi8⟩
  intro s2 ⟨w2, h82⟩
  have cl2 : ∀ b, (P1.RepW t (Ub t) b ∨ b = pendA v ∨ b = P1.stA t ∨ b = actA st s) → ¬ JW V th b := by
    rintro b (h | e | e | e)
    · exact (D.rep t ht b h).1
    · exact (D.vc v hvV b (Or.inl e)).1
    · exact P.swjw b ⟨t, ht, e⟩
    · exact (Da.nd b (Or.inr e)).1
  have E2 := E1.of_writes P w2 cl2
  have R2 : RunVmB (L := L) th s2 := R1.of_foot P w2
    (fun t' ht' hw => by
      rcases hw with h | e | e | e
      · exact ((D.rep t ht _ h).2 ⟨t', ht', rfl⟩).elim
      · exact ((D.vc v hvV _ (Or.inl e)).2 ⟨t', ht', rfl⟩).elim
      · exact Or.inl (by rw [stA_inj e]; exact h82)
      · exact ((Da.nd _ (Or.inr e)).2 ⟨t', ht', rfl⟩).elim)
    (fun t' ht' hw => by
      have J' : JW V th (tVcpuA t') := Or.inr (Or.inl ⟨t', ht', rfl⟩)
      rcases hw with h | e | e | e
      · exact ((D.rep t ht _ h).1 J').elim
      · exact ((D.vc v hvV _ (Or.inl e)).1 J').elim
      · exact (P.swjw _ ⟨t, ht, e⟩ J').elim
      · exact ((Da.nd _ (Or.inr e)).1 J').elim)
  have k2 : ∀ b, JW V th b → L.mem s2 b = L.mem s1 b := fun b hb =>
    w2.mem_eq (P.jw b hb) fun h => cl2 b h hb
  have htv2 : L.mem s2 (tVcpuA t) = v := by rw [k2 _ JWt, kJ _ JWt]; exact ev'.symm
  have hvt2 : L.mem s2 (vTcbA v) = t := by rw [k2 _ JWb, kJ _ JWb]; exact hvt
  simp only [vcpu.set, lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
  subst e3
  step as ⟨o2, ho2⟩
  subst ho2
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s4 e4 => ?_
  subst e4
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s5 e5 => ?_
  subst e5
  refine (WP.spec_ok _).2 ?_
  show DetPost st V X th Ub t s (L.wr (L.wr (L.wr s2 (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (svmA v) 0#u64)
  have w34 : P1.WritesIn st s2 (L.wr (L.wr s2 (vTcbA v) 0#u64) (tVcpuA t) 0#u64)
      (fun b => b = vTcbA v ∨ b = tVcpuA t) := (P1.writesIn_wr aB).trans (P1.writesIn_wr aT)
  have m4T : L.mem (L.wr (L.wr s2 (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (tVcpuA t) = 0#u64 := by
    rw [L.mem_wr _ _ _ _ aT aT, if_pos rfl]
  have m4B : L.mem (L.wr (L.wr s2 (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (vTcbA v) = 0#u64 := by
    rw [L.mem_wr _ _ _ _ aT aB, if_neg (P.vb t ht v hvV), L.mem_wr _ _ _ _ aB aB, if_pos rfl]
  have E4 := E2.unbind_w P ht hvV htv2 hvt2 w34 m4T m4B
  have w5 : P1.WritesIn st (L.wr (L.wr s2 (vTcbA v) 0#u64) (tVcpuA t) 0#u64)
      (L.wr (L.wr (L.wr s2 (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (svmA v) 0#u64) (· = svmA v) :=
    P1.writesIn_wr aS
  refine ⟨E4.of_writes P w5 fun b e => (clS b e).1, ?_, ?_, ?_, ?_⟩
  · refine R2.of_foot P (w34.trans w5) (fun t' ht' hw => ?_) (fun t' ht' hw => ?_)
    · have S' : SW th (P1.stA t') := ⟨t', ht', rfl⟩
      rcases hw with (e | e) | e
      · exact (P.swjw _ S' (Or.inr (Or.inr ⟨v, hvV, e⟩))).elim
      · exact (P.swjw _ S' (Or.inr (Or.inl ⟨t, ht, e⟩))).elim
      · exact ((clS _ e).2 S').elim
    · rcases hw with (e | e) | e
      · exact (P.vb t' ht' v hvV e).elim
      · exact Or.inl (by rw [tVcpuA_inj e]; exact h82)
      · exact ((clS _ e).1 (Or.inr (Or.inl ⟨t', ht', rfl⟩))).elim
  · rw [w5.mem_eq aT fun e => (clS _ e).1 JWt]; exact m4T
  · intro w hw e
    have ew : w = v := e.symm.trans ev'.symm
    subst ew
    rw [w5.mem_eq aB fun e => (clS _ e).1 JWb]; exact m4B
  · refine (((w1'.trans w2).trans w34).trans w5).mono fun b h => ?_
    unfold CW
    rcases h with ((e | (h | e | e | e)) | (e | e)) | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨v, hvV, Or.inl e⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr e⟩)))
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inl ⟨hvne, Or.inr (by rw [← ev']; exact e)⟩
    · exact Or.inl ⟨hvne, Or.inl e⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨v, hvV, Or.inr e⟩)))

end

end

end Fl4Proofs.P3
