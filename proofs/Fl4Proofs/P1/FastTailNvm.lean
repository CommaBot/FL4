/-
# The fast paths' tail keeps the switched-to thread off `TS_RUNNING_VM` (FL4 #16, m70)

m62 / m67 asked, as reads of the fast runs' end states, that the thread an
accepted fast path switches to is not `TS_RUNNING_VM` at the run's end
(`FaultNvm` inside `FastFaultOK` / `FaultNvmPre`, `RRReads5.nvm`). Both runs end
with `fastpath.switch_to Y a d`: `set_vm_root` (no write), `CUR_THREAD := d`,
the action RESUME, then the tail `switch_sched_context`, the `REPROGRAM` branch
(`set_next_interrupt`), `send_pending`, `activate_thread` (with
`complete_yield_to` when `d` has a `YIELD_TO`).

* `switch_to_nvm`: from placement facts and the two SCs `switch_sched_context`
  touches at `Y` (the current SC `SCq`, the thread's SC `SCin`, as
  QueueSc's footprint lemmas take them), `d`'s state `Running` or `Restart`
  and `d`'s `YIELD_TO` an SC of `Scs` (if nonzero), the end state's current
  thread is `d` and not `TS_RUNNING_VM`. The P1 invariants are NOT needed at
  the tail's intermediate states: the tail writes free words only
  (`switch_sched_context.free`, `set_next_interrupt.free`,
  `send_pending.free`), and `complete_yield_to` is re-read with a narrow
  footprint (`complete_yield_to.ywN`: `Ω` words and `d`'s own TCB words other
  than its state) from `ObjsOK` (which does not depend on the state).
-/
import Fl4Proofs.P1.FastRRLk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
variable {T Cs Ω Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- `ObjsOK` does not depend on the state. -/
theorem ObjsOK.any {s s' : S} (h : ObjsOK st Ω Sg Rp Scs Nt Z s) : ObjsOK st Ω Sg Rp Scs Nt Z s' :=
  ⟨h.rp, h.sc, h.rpW, h.scW, h.fixW, h.scDisj, h.rpSc, h.repW, h.ntW, h.ntRp, h.ntSc, h.ntAl, h.ntP, h.ntB,
    h.ntORp, h.ntOSc, h.snW, h.syW, h.mxW, h.nt0, h.rp0⟩

/-- `d`'s register words (below the state word). -/
def RegWd (Ω : Set U64) (d : U64) (b : U64) : Prop :=
  b ∈ Ω ∨ ∃ K : U64, K.val < 3328 ∧ K.val % 8 = 0 ∧ b = core.num.U64.wrapping_add d K

theorem reg_rw {s : S} {d r v : U64} (hd : TcbAddr d) (hr : r.val < 384) :
    obj.Tcb.set_reg st d s r v ⦃ s' => WritesIn st s s' (RegWd Ω d) ⦄ :=
  WP.spec_mono (obj.Tcb.set_reg.wrK s d r v hd hr) fun s' ⟨K, hK, e⟩ => by
    subst e
    exact (writesIn_wr (field_aligned hd (by omega) (by omega))).mono fun b e =>
      Or.inr ⟨K, by omega, by omega, e⟩

theorem rwd_trans {d : U64} {s₁ s₂ s₃ : S} (h₁ : WritesIn st s₁ s₂ (RegWd Ω d)) (h₂ : WritesIn st s₂ s₃ (RegWd Ω d)) :
    WritesIn st s₁ s₃ (RegWd Ω d) := (h₁.trans h₂).mono fun _ hb => hb.elim id id

theorem sc_word_om {s : S} {c o : U64} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hc : c ∈ Scs) (ho : o.val < 128)
    (h8 : o.val % 8 = 0) : Aligned (core.num.U64.wrapping_add c o) ∧ core.num.U64.wrapping_add c o ∈ Ω := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨c8, c128, cfit⟩ := sc_lo hP hz
  have hv : (core.num.U64.wrapping_add c o).val = c.val + o.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have ha : Aligned (core.num.U64.wrapping_add c o) := by unfold Aligned; rw [hv]; omega
  exact ⟨ha, hO.scW c hc _ ha ⟨by rw [hv]; omega, by rw [hv]; omega⟩⟩

theorem schedcontext.update_consumed.rw {s : S} {a : A} {c d : U64} (hA : P0.ArchTotal ar)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hc : c ∈ Scs) :
    schedcontext.update_consumed st ar s a c ⦃ r => WritesIn st s r.2 (RegWd Ω d) ⦄ := by
  obtain ⟨ha, hw⟩ := sc_word_om (o := layout.sc.CONSUMED) hO hc (by simp [layout.sc.CONSUMED])
    (by simp [layout.sc.CONSUMED])
  unfold schedcontext.update_consumed
  step with obj.Sc.consumed.spec as ⟨x, _hx⟩
  split
  · step as ⟨y, hy⟩
    refine WP.spec_bind (obj.Sc.set_consumed.spec' s c y) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ =>
      (WP.spec_ok _).2 ((writesIn_wr ha).mono fun b e => by rw [e]; exact Or.inl hw)
  · refine WP.spec_bind (obj.Sc.set_consumed.spec' s c 0#u64) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ =>
      (WP.spec_ok _).2 ((writesIn_wr ha).mono fun b e => by rw [e]; exact Or.inl hw)

/-- `set_consumed` writes the SC's `CONSUMED` word and `d`'s registers. -/
theorem schedcontext.set_consumed.rw (hA : P0.ArchTotal ar) (s : S) (a : A) (c d : U64) (wm : Bool)
    (hd : TcbAddr d) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hc : c ∈ Scs) :
    schedcontext.set_consumed st ar s a c d wm ⦃ s' => WritesIn st s s' (RegWd Ω d) ⦄ := by
  unfold schedcontext.set_consumed
  refine WP.spec_bind (schedcontext.update_consumed.rw (d := d) hA hO hc) ?_
  rintro ⟨x, s1⟩ w1
  simp only at w1
  try simp only [WP.uncurry'_pair]
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s1 true d L.total) fun buf _ => ?_
    refine WP.spec_bind (reg_rw (Ω := Ω) (r := layout.reg.BADGE) hd (by simp [layout.reg.BADGE, layout.reg.RDI]))
      fun s2 w2 => ?_
    unfold msg.set_mr
    simp only [show (0#u64 < msg.N_MSG_REGISTERS) = True from by simp [msg.N_MSG_REGISTERS], if_true]
    simp only [msg.msg_register, if_true, Aeneas.Std.bind_ok]
    refine WP.spec_bind (Pₘ := fun r : U64 × S => WritesIn st s2 r.2 (RegWd Ω d)) ?_ ?_
    · refine WP.spec_bind (reg_rw (Ω := Ω) (r := layout.reg.R10) hd (by simp [layout.reg.R10])) fun s3 hh => ?_
      simp only [lift, Aeneas.Std.bind_ok, WP.spec_ok]; exact hh
    rintro ⟨len, s3⟩ w3
    simp only at w3
    try simp only [WP.uncurry'_pair]
    unfold msginfo.MessageInfo.new msg.set_msg_info
    simp only [Aeneas.Std.bind_ok]
    refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ => ?_
    exact WP.spec_mono (reg_rw (Ω := Ω) (r := layout.reg.MSG_INFO) hd (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
      fun s4 w4 => rwd_trans w1 (rwd_trans w2 (rwd_trans w3 w4))
  · exact (WP.spec_ok _).2 w1

/-- `d`'s words but its state, and `Ω`. -/
def YWd (Ω : Set U64) (d : U64) (b : U64) : Prop := RegWd Ω d b ∨ b = yieldA d

theorem schedcontext.cancel_yield_to.ywN (s : S) (d : U64) (hd : TcbAddr d) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hΩa : ∀ b ∈ Ω, Aligned b)
    (hyt : L.mem s (yieldA d) ≠ 0#u64 → L.mem s (yieldA d) ∈ Scs) :
    schedcontext.cancel_yield_to st s d ⦃ s' => WritesIn st s s' (YWd Ω d) ⦄ := by
  unfold schedcontext.cancel_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, _⟩
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  split
  · rename_i hi
    have hiS : i ∈ Scs := by rw [ei]; exact hyt (by rw [← ei]; simpa using hi)
    have hm : scYieldFromA i ∈ Ω := hsub _ (hO.syW i hiS)
    step with obj.Sc.set_yield_from.spec as ⟨s1, e1⟩
    subst e1
    step with obj.Tcb.set_yield_to.spec as ⟨s2, e2⟩
    subst e2
    have w1 := (writesIn_wr (st := st) (s := s) (v := 0#u64) (hΩa _ hm)).mono
      fun b e => (by rw [e]; exact Or.inl (Or.inl hm) : YWd Ω d b)
    have w2 := (writesIn_wr (st := st) (s := L.wr s (scYieldFromA i) 0#u64) (v := 0#u64)
      (field_aligned (K := 3472#u64) hd (by simp) (by simp))).mono
      fun b e => (Or.inr e : YWd Ω d b)
    exact (w1.trans w2).mono fun _ hb => hb.elim id id
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- **`complete_yield_to` with a narrow footprint**: `Ω` words and `d`'s TCB
words other than its state (no P1 invariant: `ObjsOK` and `d`'s `YIELD_TO`
an SC of `Scs`). -/
theorem schedcontext.complete_yield_to.ywN (hA : P0.ArchTotal ar) (s : S) (a : A) (d : U64)
    (hd : TcbAddr d) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hΩa : ∀ b ∈ Ω, Aligned b) (hΩd : ∀ b ∈ Ω, b.val < d.val ∨ d.val + 2 ^ 12 ≤ b.val)
    (hyt : L.mem s (yieldA d) ≠ 0#u64 → L.mem s (yieldA d) ∈ Scs) :
    schedcontext.complete_yield_to st ar s a d ⦃ r => WritesIn st s r.1 (YWd Ω d) ⦄ := by
  unfold schedcontext.complete_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  split
  · rename_i hi
    have hiS : i ∈ Scs := by rw [ei]; exact hyt (by rw [← ei]; simpa using hi)
    refine WP.spec_bind (schedcontext.set_consumed.rw hA s a i d true hd hO hiS) fun s1 w1 => ?_
    have ya : Aligned (yieldA d) := field_aligned (K := 3472#u64) hd (by simp) (by simp)
    have yv : (yieldA d).val = d.val + 3472 := field_val hd (K := 3472#u64) (by simp)
    have ey : L.mem s1 (yieldA d) = L.mem s (yieldA d) := w1.mem_eq ya fun h => by
      rcases h with hm | ⟨K, hK, -, e⟩
      · have := hΩd _ hm; rw [yv] at this; omega
      · have := congrArg UScalar.val e; rw [yv, field_val hd (by omega)] at this; omega
    refine WP.spec_bind (schedcontext.cancel_yield_to.ywN s1 d hd (ObjsOK.any hO) hsub hΩa (by rw [ey]; exact hyt))
      fun s2 w2 => ?_
    exact (WP.spec_ok _).2 ((w1.trans w2).mono fun b hb => hb.elim (fun h => Or.inl h) id)
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-! ## The words the argument reads -/

theorem ne_of_valne {a b : U64} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg UScalar.val e)

/-- The current core's free words of `X` (`Ω` and the low node words): what
the tail writes. -/
def FreeCd (X : S) (Ω : Set U64) (b : U64) : Prop :=
  b ∈ Ω ∨ ∃ o : U64, LowFree o.val ∧ b = L.nodeAt X (L.cpu X) o

/-- What the tail argument needs of a state, besides the current thread. -/
structure TailPld (T Cs Ω : Set U64) (X : S) (d : U64) : Prop where
  hT : TcbPlaced T
  hd : d ∈ T
  hN : NodePlaced st T X (L.cpu X)
  hcC : L.cpu X ∈ Cs
  hΩ : ∀ b ∈ Ω, OutsideObjs st T Cs X b

theorem TailPld.ksb {X X' : S} {d : U64} (P : TailPld (L := L) T Cs Ω X d) (hk : L.ksb X' = L.ksb X)
    (hc : L.cpu X' = L.cpu X) : TailPld (L := L) T Cs Ω X' d :=
  ⟨P.hT, P.hd, by rw [hc]; exact P.hN.ksb hk, by rw [hc]; exact P.hcC, fun b hb => (P.hΩ b hb).ksb hk⟩

/-- A TCB word of `d` is neither an `Ω` word nor a node word. -/
theorem TailPld.tcb_nfree {X : S} {d K : U64} (P : TailPld (L := L) T Cs Ω X d) (hK : K.val < 4096) :
    ¬ FreeCd (L := L) X Ω (core.num.U64.wrapping_add d K) := by
  rintro (hm | ⟨o, ho, e⟩)
  · exact out_ne_field (P.hΩ _ hm) P.hd (P.hT d P.hd) hK rfl
  · simp only [LowFree] at ho
    exact node_ne_field P.hN (by omega) P.hd (P.hT d P.hd) hK e.symm

/-- The `CUR_THREAD` word is not free. -/
theorem TailPld.cur_nfree {X : S} {d : U64} (P : TailPld (L := L) T Cs Ω X d) :
    ¬ FreeCd (L := L) X Ω (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD) := by
  rintro (hm | ⟨o, ho, e⟩)
  · exact out_ne_node (P.hΩ _ hm) P.hcC P.hN (by rw [curth_val]; omega) rfl
  · simp only [LowFree] at ho
    have := congrArg UScalar.val e
    rw [nodeAt_val P.hN (by rw [curth_val]; omega), nodeAt_val P.hN (by omega), curth_val] at this
    omega

theorem TailPld.curAl {X : S} {d : U64} (P : TailPld (L := L) T Cs Ω X d) :
    Aligned (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD) :=
  nodeAt_aligned P.hN (by rw [curth_val]; omega) (by rw [curth_val])

theorem TailPld.tcbAl {X : S} {d K : U64} (P : TailPld (L := L) T Cs Ω X d) (hK : K.val < 4096)
    (h8 : K.val % 8 = 0) : Aligned (core.num.U64.wrapping_add d K) := field_aligned (P.hT d P.hd) hK h8

/-- `schedule_tcb` writes at most the action word. -/
theorem schedule_tcb_act (s : S) (x : obj.Tcb) :
    sched.schedule_tcb st s x ⦃ s' => s' = s ∨ s' = L.wr s (actA (L := L) s) sched.ACTION_CHOOSE_NEW ⦄ := by
  unfold sched.schedule_tcb
  step with sched.cur_thread.spec as ⟨t1, _⟩
  step with tcb_eq.blk as ⟨b, _⟩
  split
  · step with sched.action.spec as ⟨i, _⟩
    split
    · step with sched.is_schedulable.spec as ⟨b1, _⟩
      split
      · exact (WP.spec_ok _).2 (Or.inl rfl)
      · exact WP.spec_mono (sched.set_action.spec s _) fun s' e => Or.inr e
    · exact (WP.spec_ok _).2 (Or.inl rfl)
  · exact (WP.spec_ok _).2 (Or.inl rfl)

theorem set_thread_state_act (s : S) (x : obj.Tcb) (v : U64) :
    sched.set_thread_state st s x v ⦃ s' => s' = L.wr s (stA x) v ∨
      s' = L.wr (L.wr s (stA x) v) (actA (L := L) s) sched.ACTION_CHOOSE_NEW ⦄ := by
  unfold sched.set_thread_state
  refine WP.spec_bind (obj.Tcb.set_state.spec s x v) fun s3 e3 => ?_
  subst e3
  refine WP.spec_mono (schedule_tcb_act _ x) fun s4 e4 => ?_
  rw [actA_wr] at e4; exact e4

/-- **`activate_thread` of `d` (current, `Running` or `Restart`) ends with
`d` current and not `TS_RUNNING_VM`.** -/
theorem activate_nvm (hA : P0.ArchTotal ar) (X : S) (a : A) {d : U64}
    (P : TailPld (L := L) T Cs Ω X d) (hO : ObjsOK st Ω Sg Rp Scs Nt Z X) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hcur : L.curW X = d)
    (hst : L.mem X (stA d) = sched.TS_RUNNING ∨ L.mem X (stA d) = sched.TS_RESTART)
    (hyt : L.mem X (yieldA d) ≠ 0#u64 → L.mem X (yieldA d) ∈ Scs) :
    sched.activate_thread st ar X a ⦃ r => L.curW r.1 = d ∧ L.mem r.1 (stA d) = sched.TS_RUNNING ⦄ := by
  have hd' := P.hT d P.hd
  have hΩa : ∀ b ∈ Ω, Aligned b := fun b hb => (P.hΩ b hb).1
  have hΩd : ∀ b ∈ Ω, b.val < d.val ∨ d.val + 2 ^ 12 ≤ b.val := fun b hb => (P.hΩ b hb).2.1 d P.hd
  have sA : Aligned (stA d) := by rw [stA_eq]; exact P.tcbAl (by simp) (by simp)
  have sv : (stA d).val = d.val + 3328 := by rw [stA_eq]; exact field_val hd' (by simp)
  -- a YWd word is not the state word nor CUR_THREAD
  have nYs : ¬ YWd Ω d (stA d) := by
    rintro ((hm | ⟨K, hK, -, e⟩) | e)
    · have := hΩd _ hm; rw [sv] at this; omega
    · have := congrArg UScalar.val e; rw [sv, field_val hd' (by omega)] at this; omega
    · have := congrArg UScalar.val e
      rw [sv, show yieldA d = core.num.U64.wrapping_add d 3472#u64 from rfl, field_val hd' (by simp)] at this
      simp at this
  have nYc : ∀ X' : S, L.ksb X' = L.ksb X → L.cpu X' = L.cpu X →
      ¬ YWd Ω d (L.nodeAt X' (L.cpu X') layout.node.CUR_THREAD) := by
    intro X' hk hc
    rw [hc, nodeAt_of_ksb hk]
    rintro ((hm | ⟨K, hK, -, e⟩) | e)
    · exact P.cur_nfree (Or.inl hm)
    · exact node_ne_field P.hN (by rw [curth_val]; omega) P.hd hd' (by omega) e
    · exact node_ne_field P.hN (by rw [curth_val]; omega) P.hd hd' (by simp) e
  unfold sched.activate_thread
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have ect' : ct = d := by rw [ect]; exact hcur
  subst ect'
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => L.ksb r.1 = L.ksb X ∧ L.cpu r.1 = L.cpu X ∧ L.curW r.1 = ct ∧
      (L.mem r.1 (stA ct) = sched.TS_RUNNING ∨ L.mem r.1 (stA ct) = sched.TS_RESTART)) ?_ ?_
  · split
    · refine WP.spec_mono (schedcontext.complete_yield_to.ywN hA X a ct hd' hO hsub hΩa hΩd hyt) ?_
      rintro ⟨s1, a1⟩ w
      refine ⟨w.1, w.2.1, ?_, by rw [w.mem_eq sA nYs]; exact hst⟩
      show L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD) = _
      rw [w.mem_eq (by rw [w.2.1, nodeAt_of_ksb w.1]; exact P.curAl) (nYc s1 w.1 w.2.1)]
      rw [w.2.1, nodeAt_of_ksb w.1]; exact hcur
    · exact (WP.spec_ok _).2 ⟨rfl, rfl, hcur, hst⟩
  rintro ⟨s1, a1⟩ ⟨k1, c1, cu1, st1⟩
  try simp only [WP.uncurry'_pair]
  have P1 := P.ksb k1 c1
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · rename_i hv
    step with obj.Tcb.reg.spec as ⟨pc, _⟩
    refine WP.spec_bind (obj.Tcb.set_reg.wrK s1 ct layout.reg.NEXT_IP pc hd' (by simp [layout.reg.NEXT_IP])) ?_
    rintro s2 ⟨K, hK, e2⟩
    subst e2
    have hK' : K.val < 3328 := by rw [hK]; simp [layout.reg.NEXT_IP]
    have kA : Aligned (core.num.U64.wrapping_add ct K) := P.tcbAl (by omega) (by rw [hK]; omega)
    refine WP.spec_bind (set_thread_state_act _ ct sched.TS_RUNNING) fun s4 e4 => ?_
    simp only [WP.spec_ok]
    have cA := P1.curAl
    have aA : Aligned (actA (L := L) s1) := nodeAt_aligned P1.hN (by rw [act_val]; omega) (by rw [act_val])
    have nK : core.num.U64.wrapping_add ct K ≠ L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD :=
      fun e => node_ne_field P1.hN (by rw [curth_val]; omega) P.hd hd' (by omega) e.symm
    have nS : stA ct ≠ L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD := by
      rw [stA_eq]; exact fun e => node_ne_field P1.hN (by rw [curth_val]; omega) P.hd hd' (by simp) e.symm
    have nA : actA (L := L) s1 ≠ L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD := by
      apply ne_of_valne
      rw [nodeAt_val P1.hN (by rw [act_val]; omega), nodeAt_val P1.hN (by rw [curth_val]; omega), act_val, curth_val]
      omega
    have nAS : actA (L := L) s1 ≠ stA ct := by
      rw [stA_eq]; exact node_ne_field P1.hN (by rw [act_val]; omega) P.hd hd' (by simp)
    have cu3 : L.curW (L.wr (L.wr s1 (core.num.U64.wrapping_add ct K) pc) (stA ct) sched.TS_RUNNING) = ct := by
      simp only [LawfulStore.curW, nodeAt_wr, LawfulStore.cpu_wr]
      rw [mem_wr_ne' sA cA nS, mem_wr_ne' kA cA nK]; exact cu1
    have st3 : L.mem (L.wr (L.wr s1 (core.num.U64.wrapping_add ct K) pc) (stA ct) sched.TS_RUNNING) (stA ct) =
        sched.TS_RUNNING := L.mem_wr_same sA
    rcases e4 with rfl | rfl
    · exact ⟨cu3, st3⟩
    · have eA : actA (L := L) (L.wr s1 (core.num.U64.wrapping_add ct K) pc) = actA (L := L) s1 := actA_wr _ _ _
      rw [eA]
      refine ⟨?_, by rw [mem_wr_ne' aA sA nAS]; exact st3⟩
      simp only [LawfulStore.curW, nodeAt_wr, LawfulStore.cpu_wr] at cu3 ⊢
      rw [mem_wr_ne' aA cA nA]; exact cu3
  · rename_i hv
    simp only [WP.spec_ok]
    refine ⟨cu1, ?_⟩
    rcases st1 with h | h
    · exact h
    · exact absurd (by rw [ev, h]) hv

/-- **The fast paths' end, from `Y`** (module docstring): an accepted run's
`fastpath.switch_to Y a d` ends with `d` current and `Running`. -/
theorem switch_to_nvm (hA : P0.ArchTotal ar) (Y : S) (a : A) {d : U64} {zc zt : Nat}
    (P : TailPld (L := L) T Cs Ω Y d) (hO : ObjsOK st Ω Sg Rp Scs Nt Z Y) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hc : SCq st Y Ω (L.cscW Y) zc)
    (ht : L.mem Y (scA d) ≠ L.cscW Y → SCin st Y Ω (L.mem Y (scA d)) zt ∧
      ∀ b, InSC (L.mem Y (scA d)) zt b → Outside b (L.cscW Y) zc)
    (hst : L.mem Y (stA d) = sched.TS_RUNNING ∨ L.mem Y (stA d) = sched.TS_RESTART)
    (hyt : L.mem Y (yieldA d) ≠ 0#u64 → L.mem Y (yieldA d) ∈ Scs) :
    fastpath.switch_to st ar Y a d ⦃ r => L.curW r.1 = d ∧ L.mem r.1 (stA d) = sched.TS_RUNNING ⦄ := by
  have hd' := P.hT d P.hd
  unfold fastpath.switch_to
  refine WP.spec_bind (vspace.set_vm_root.same hA Y a d) ?_
  rintro ⟨Y1, a1⟩ e1
  simp only at e1; subst Y1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (sched.set_cur_thread.spec Y d) fun s2 e2 => ?_
  subst e2
  refine WP.spec_bind (sched.set_action.spec _ sched.ACTION_RESUME_CURRENT) fun s3 e3 => ?_
  subst e3
  simp only [nodeAt_wr, LawfulStore.cpu_wr]
  have cA := P.curAl
  have aA : Aligned (L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION) :=
    nodeAt_aligned P.hN (by rw [act_val]; omega) (by rw [act_val])
  have nAC : L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION ≠ L.nodeAt Y (L.cpu Y) layout.node.CUR_THREAD := by
    apply ne_of_valne
    rw [nodeAt_val P.hN (by rw [act_val]; omega), nodeAt_val P.hN (by rw [curth_val]; omega), act_val, curth_val]
    omega
  generalize hX : L.wr (L.wr Y (L.nodeAt Y (L.cpu Y) layout.node.CUR_THREAD) d)
    (L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION) sched.ACTION_RESUME_CURRENT = X
  have kX : L.ksb X = L.ksb Y := by rw [← hX, L.ksb_wr, L.ksb_wr]
  have cX : L.cpu X = L.cpu Y := by rw [← hX, LawfulStore.cpu_wr, LawfulStore.cpu_wr]
  have PX := P.ksb kX cX
  -- X agrees with Y on every word but the two node words
  have ag : ∀ b, Aligned b → b ≠ L.nodeAt Y (L.cpu Y) layout.node.CUR_THREAD →
      b ≠ L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION → L.mem X b = L.mem Y b := by
    intro b hb h1 h2
    rw [← hX, mem_wr_ne' aA hb (Ne.symm h2), mem_wr_ne' cA hb (Ne.symm h1)]
  have agΩ : ∀ b ∈ Ω, L.mem X b = L.mem Y b := fun b hb => ag b (P.hΩ b hb).1
    (fun e => out_ne_node (P.hΩ b hb) P.hcC P.hN (by rw [curth_val]; omega) (by rw [e]))
    (fun e => out_ne_node (P.hΩ b hb) P.hcC P.hN (by rw [act_val]; omega) (by rw [e]))
  have agT : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem X (core.num.U64.wrapping_add d K) = L.mem Y (core.num.U64.wrapping_add d K) := fun K hK h8 =>
    ag _ (P.tcbAl hK h8) (fun e => node_ne_field P.hN (by rw [curth_val]; omega) P.hd hd' hK e.symm)
      (fun e => node_ne_field P.hN (by rw [act_val]; omega) P.hd hd' hK e.symm)
  have csA : Aligned (L.nodeAt Y (L.cpu Y) layout.node.CUR_SC) :=
    nodeAt_aligned P.hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have ecs : L.mem X (L.nodeA X layout.node.CUR_SC) = L.cscW Y := by
    unfold LawfulStore.nodeA LawfulStore.cscW LawfulStore.nodeA
    rw [cX, nodeAt_of_ksb kX]
    have v24 := nodeAt_val P.hN (off := layout.node.CUR_SC) (by simp [layout.node.CUR_SC])
    have v0 := nodeAt_val P.hN (off := layout.node.CUR_THREAD) (by simp [layout.node.CUR_THREAD])
    have v16 := nodeAt_val P.hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
    refine ag _ csA ?_ ?_ <;> apply ne_of_valne
    · rw [v24, v0]; simp [layout.node.CUR_SC, layout.node.CUR_THREAD]
    · rw [v24, v16]; simp [layout.node.CUR_SC, layout.node.SCHED_ACTION]
  have hcur : L.mem X (L.nodeA X layout.node.CUR_THREAD) = d := by
    unfold LawfulStore.nodeA
    rw [cX, nodeAt_of_ksb kX, ← hX, mem_wr_ne' aA cA nAC, L.mem_wr_same cA]
  have esc : L.mem X (scA d) = L.mem Y (scA d) := by rw [scA_eq]; exact agT _ (by simp) (by simp)
  have est : L.mem X (stA d) = L.mem Y (stA d) := by rw [stA_eq]; exact agT _ (by simp) (by simp)
  have eyt : L.mem X (yieldA d) = L.mem Y (yieldA d) := agT 3472#u64 (by simp) (by simp)
  have hcX : SCq st X Ω (L.mem X (L.nodeA X layout.node.CUR_SC)) zc := by
    rw [ecs]
    refine ⟨fun hm => ?_, hc.2.1, hc.2.2⟩
    have em : L.rmax X (L.cscW Y) = L.rmax Y (L.cscW Y) :=
      agΩ _ (hc.2.1 _ hc.2.2.2.2 hc.2.2.2.1)
    exact (hc.1 (em ▸ hm)).agree fun b hb hin => agΩ b (hc.2.1 b hb hin)
  have htX : L.mem X (scA (L.mem X (L.nodeA X layout.node.CUR_THREAD))) ≠ L.mem X (L.nodeA X layout.node.CUR_SC) →
      SCin st X Ω (L.mem X (scA (L.mem X (L.nodeA X layout.node.CUR_THREAD)))) zt ∧
      ∀ b, InSC (L.mem X (scA (L.mem X (L.nodeA X layout.node.CUR_THREAD)))) zt b →
        Outside b (L.mem X (L.nodeA X layout.node.CUR_SC)) zc := by
    rw [hcur, esc, ecs]
    intro hne
    obtain ⟨h1, h2⟩ := ht hne
    exact ⟨h1.agree agΩ, h2⟩
  have fN : ∀ o : U64, LowFree o.val → FreeCd (L := L) X Ω (L.nodeA X o) := fun o ho => Or.inr ⟨o, ho, rfl⟩
  refine WP.spec_bind (sched.switch_sched_context.fp hA X a1 (zt := zt) (zc := zc) (B := FreeCd (L := L) X Ω)
    PX.hcC PX.hN PX.hΩ hcX htX (fN _ (by simp [layout.node.REPROGRAM, LowFree]))
    (fN _ (by simp [layout.node.CONSUMED, LowFree])) (fN _ (by simp [layout.node.CUR_SC, LowFree]))
    (fun hne b hb h => Or.inl ((htX hne).1.2 b hb h.inSC))
    (fun b hb h => by
      rcases h with h | rfl
      · exact Or.inl (hcX.2.1 b hb h.inSC)
      · exact Or.inl (hcX.2.1 _ hb hcX.2.2.1.1))) ?_
  rintro ⟨s4, a2⟩ ⟨w4, -⟩
  try simp only [WP.uncurry'_pair]
  have P4 := PX.ksb w4.1 w4.2.1
  have fN4 : ∀ o : U64, LowFree o.val → FreeCd (L := L) X Ω (L.nodeAt s4 (L.cpu s4) o) := fun o ho =>
    Or.inr ⟨o, ho, by rw [w4.2.1, nodeAt_of_ksb w4.1]⟩
  step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
  step with obj.node_get.spec as ⟨i, _⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => WritesIn st X r.1 (FreeCd (L := L) X Ω)) ?_ ?_
  · split
    · refine WP.spec_bind (sched.set_next_interrupt.fp hA s4 a2 (B := FreeCd (L := L) X Ω) P4.hN
        (fN4 _ (by simp [layout.node.ARMED, LowFree]))) ?_
      rintro ⟨s6, a4⟩ w6
      try simp only [WP.uncurry'_pair]
      refine WP.spec_bind (obj.node_set.spec s6 c _ _) fun s7 e7 => ?_
      subst e7
      simp only [WP.spec_ok]
      have w7 : WritesIn st s6 (L.wr s6 (L.nodeAt s6 c layout.node.REPROGRAM) 0#u64) (FreeCd (L := L) X Ω) := by
        rw [ec, nodeAt_of_ksb w6.1]
        exact (writesIn_wr (nodeAt_aligned P4.hN (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM]))).mono fun b e => by
            rw [e]; exact fN4 _ (by simp [layout.node.REPROGRAM, LowFree])
      exact ((w4.trans w6).trans w7).mono fun b hb => by
        rcases hb with (h | h) | h <;> exact h
    · exact (WP.spec_ok _).2 w4
  rintro ⟨s5, a3⟩ w5
  try simp only [WP.uncurry'_pair]
  have P5 := PX.ksb w5.1 w5.2.1
  refine WP.spec_bind (smp.send_pending.fp hA s5 a3 (B := FreeCd (L := L) X Ω) P5.hN
    (Or.inr ⟨layout.node.IPI_PENDING, by simp [layout.node.IPI_PENDING, LowFree],
      by rw [w5.2.1, nodeAt_of_ksb w5.1]⟩)) ?_
  rintro ⟨s6, a4⟩ w6'
  try simp only [WP.uncurry'_pair]
  have w6 : WritesIn st X s6 (FreeCd (L := L) X Ω) := (w5.trans w6').mono fun b hb => hb.elim id id
  have P6 := PX.ksb w6.1 w6.2.1
  have kT : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s6 (core.num.U64.wrapping_add d K) = L.mem X (core.num.U64.wrapping_add d K) := fun K hK h8 =>
    w6.mem_eq (PX.tcbAl hK h8) (PX.tcb_nfree hK)
  refine activate_nvm hA s6 a4 P6 (ObjsOK.any hO) hsub ?_ ?_ ?_
  · show L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.CUR_THREAD) = d
    rw [w6.2.1, nodeAt_of_ksb w6.1, w6.mem_eq PX.curAl PX.cur_nfree]; exact hcur
  · rw [stA_eq, kT _ (by simp) (by simp), ← stA_eq, est]; exact hst
  · rw [show yieldA d = core.num.U64.wrapping_add d 3472#u64 from rfl, kT _ (by simp) (by simp)]
    rw [show core.num.U64.wrapping_add d 3472#u64 = yieldA d from rfl, eyt]; exact hyt

end

end Fl4Proofs.P1
