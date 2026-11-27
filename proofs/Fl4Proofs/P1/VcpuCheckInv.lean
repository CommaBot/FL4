/-
P1 (vmchk): **`vcpu::check` of the current thread keeps `EntryInv`**
(`vcpu.check.entry`), the fact `EntryHyps0` / `P3Place` used to assume as their
`vmchk` field. Moved here from P2/EntryTail (par/actv), with P1 copies of the
few P2 helpers it used, so that P1's `finish.entry` (QueueEntry) can use it.

* `VckW y s0`: the words `vcpu::check` of `y` writes: words outside the TCBs and
  nodes that are no SC `REPLY`/`TCB` header (`VckR`'s first kind: a
  notification's `TAIL_STATE`, a user word, the VCPU's `PENDING` word), `y`'s
  register words (`256 ≤ K < 3328`), `y`'s `STATE` and the executing core's
  `SCHED_ACTION`. `VckW.frames`: such a write keeps the core, the current/idle
  thread, the current SC, every node word but `SCHED_ACTION` and every TCB
  field but `y`'s registers and `STATE`. (P2's `TW` contains `VckW`.)
* `vcpu.report.xfV`: P1's `vcpu.report.xf` without its no-pending-exit premise:
  the VCPU's `PENDING` word, when the report clears it, is one more user word.
* `vcpu.check.vck`: `vcpu::check` of the current thread keeps `EntryInv`, as a
  `VckW` step (`VckPost`): off `RUNNING_VM` a no-op; on it the report (with a
  pending exit or the bound notification's badge, the notification made idle
  first), its user words and the VCPU's `PENDING` word, then the thread made
  running. **`vcpu.check.entry`**: its `EntryInv` part.

Named premises of `vcpu.check.vck` / `vcpu.check.entry` (both placement):
* `hbuf` **[P]**: the current thread's IPC buffer lies in user words `U`
  (`BufOK U`; as `BufAt`'s);
* `hpw` **[P]**: the thread's bound VCPU's `PENDING` word is in `U` (a VCPU is
  a heap object of its own, `.other 15`; P1 `VcpuPl.bound`). `UsrW` of that word
  does not follow from `VcpuPl` + `HeapOK` alone: the heap gives it off the
  TCBs, endpoints, notifications, frames and SCs, but not off the core nodes
  `Cs` nor off the kernel-global area (`VcpuPl.listed` gives the latter only for
  listed VCPUs), and `VcpuPl` holds only at `Fr0`-states of an entry.
-/
import Fl4Proofs.P1.QueueFire
import Fl4Proofs.P1.VcpuHooks
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}
variable {A : Type _} {ar : machine.Arch A}

/-! ## Helpers (P1 copies of P2's `EntryInv.blkOK`, `actionW_of`, `sclink_in`,
`set_thread_state.w2`, and of QueueKeeps' `EntryInv.of_step`) -/

theorem EntryInv.vckBlk {s : S} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.1.sg⟩

/-- `EntryInv` after a step that keeps `BlkOK`, the current thread and SC,
every thread's SC field, and keeps the action or makes it `CHOOSE_NEW`. -/
theorem EntryInv.vckStep {s s' : S} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (h' : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s') (ecs : L.cscW s' = L.cscW s) (ec : L.curW s' = L.curW s)
    (ea : L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64) (esc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y)) :
    EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  have hcT : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  have hT := h.1.choose_spec.choose_spec.tcbs
  obtain ⟨-, -, -, -, -, hcA, hna, hcsc⟩ := h
  obtain ⟨q, b, x, sc, sg⟩ := h'
  refine ⟨q, b, x, sc, x.2.2.tm, by rw [ecs]; exact hcA, ?_, ?_⟩
  · rw [ec]
    rcases ea with e | e
    · rw [e]; exact hna
    · rw [e]; intro e'; exact notT_small hT (by rw [← e']; decide) hcT
  · rw [ec, esc _ hcT, ecs]; exact hcsc

/-- A step whose writes miss the action word keeps the action. -/
theorem vck_actionW_of {s s' : S} {B : U64 → Prop} (h : WritesIn st s s' B) (hN : NodePlaced st T s (L.cpu s))
    (hn : ¬ B (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) : L.actionW s' = L.actionW s := by
  unfold LawfulStore.actionW
  rw [h.2.1, nodeAt_of_ksb h.1]
  exact h.mem_eq (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val])) hn

/-- The SC link words are aligned words of their SC. -/
theorem vck_sclink_in {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c : U64} (hc : c ∈ Scs) :
    (Aligned (scReplyA c) ∧ InSC c (Z c) (scReplyA c)) ∧ (Aligned (scTcbA c) ∧ InSC c (Z c) (scTcbA c)) := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hr := scReplyA_val hP hz
  have ht := scTcbA_val hP hz
  exact ⟨⟨by unfold Aligned; omega, by omega, by omega⟩, ⟨by unfold Aligned; omega, by omega, by omega⟩⟩

/-- `set_thread_state` writes the thread's `STATE` word and possibly the
executing core's `SCHED_ACTION` (to `CHOOSE_NEW`). -/
theorem sched.set_thread_state.vckW2 (s : S) (t : obj.Tcb) (v : U64) (hT : TcbPlaced T)
    (hN : NodePlaced st T s (L.cpu s)) (ht : t ∈ T) :
    sched.set_thread_state st s t v ⦃ s' => WritesIn st s s'
        (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) ∧
      (L.actionW s' = L.actionW s ∨ L.actionW s' = sched.ACTION_CHOOSE_NEW) ∧ L.mem s' (stA t) = v ⦄ := by
  have hta := hT t ht
  have a1 : Aligned (stA t) := by rw [stA_eq]; exact field_aligned hta (by simp) (by simp)
  have w1 : WritesIn st s (L.wr s (stA t) v)
      (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
    (writesIn_wr a1).mono fun b hb => Or.inl hb
  have e1 : L.actionW (L.wr s (stA t) v) = L.actionW s := act_wr_field hN ht hta (stA_eq t) (by simp) (by simp)
  have ok1 : (ok (L.wr s (stA t) v) : Result S) ⦃ s' => WritesIn st s s'
        (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) ∧
      (L.actionW s' = L.actionW s ∨ L.actionW s' = sched.ACTION_CHOOSE_NEW) ∧ L.mem s' (stA t) = v ⦄ :=
    (WP.spec_ok _).2 ⟨w1, Or.inl e1, L.mem_wr_same a1⟩
  unfold sched.set_thread_state
  refine WP.spec_bind (obj.Tcb.set_state.spec s t v) fun s1 es1 => ?_
  subst es1
  unfold sched.schedule_tcb
  step with sched.cur_thread.spec as ⟨t1, et1⟩
  step with tcb_eq.blk as ⟨b, eb⟩
  split
  · step with sched.action.spec as ⟨i, ei⟩
    split
    · step with sched.is_schedulable.spec as ⟨b1, eb1⟩
      split
      · exact ok1
      · refine WP.spec_mono (sched.set_action.spec _ _) fun s' e' => ?_
        subst e'
        have hk1 : L.ksb (L.wr s (stA t) v) = L.ksb s := L.ksb_wr _ _ _
        have hc1 : L.cpu (L.wr s (stA t) v) = L.cpu s := L.cpu_wr _ _ _
        rw [hc1, nodeAt_of_ksb hk1]
        have ha : Aligned (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
          nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val])
        refine ⟨(w1.trans (writesIn_wr ha)).mono fun b hb => hb.elim id Or.inr, Or.inr ?_, ?_⟩
        · unfold LawfulStore.actionW
          rw [L.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _), hc1, nodeAt_of_ksb hk1]
          exact L.mem_wr_same ha
        · rw [L.mem_wr_ne ha a1 (fun e => node_ne_field (K := 3328#u64) hN (by rw [act_val]; omega) ht hta
            (by simp) (by rw [← stA_eq]; exact UScalar.eq_of_val_eq e))]
          exact L.mem_wr_same a1
    · exact ok1
  · exact ok1


/-! ## The words of `vcpu::check` -/

/-- Words outside the TCBs and nodes that are no SC header, and `y`'s register words. -/
def VckR (st : machine.Store S) [L : LawfulStore st] (T Cs Scs : Set U64) (y : U64) (s0 : S) (b : U64) : Prop :=
  (OutsideObjs st T Cs s0 b ∧ ∀ c ∈ Scs, b ≠ scReplyA c ∧ b ≠ scTcbA c) ∨
  (∃ K : U64, 256 ≤ K.val ∧ K.val < 3328 ∧ K.val % 8 = 0 ∧ b = core.num.U64.wrapping_add y K)

/-- **The words of `vcpu::check` of `y`** (module docstring). -/
def VckW (st : machine.Store S) [L : LawfulStore st] (T Cs Scs : Set U64) (y : U64) (s0 : S) (b : U64) : Prop :=
  VckR st T Cs Scs y s0 b ∨ b = stA y ∨ b = L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION

theorem VckR.ksb {y : U64} {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0)
    (h : VckR st T Cs Scs y s1 b) : VckR st T Cs Scs y s0 b := by
  rcases h with ⟨ho, hh⟩ | h
  · exact Or.inl ⟨ho.ksb hk.symm, hh⟩
  · exact Or.inr h

theorem VckW.ksb {y : U64} {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (hc : L.cpu s1 = L.cpu s0)
    (h : VckW st T Cs Scs y s1 b) : VckW st T Cs Scs y s0 b := by
  rcases h with h | h | h
  · exact Or.inl (VckR.ksb hk h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by rw [h, hc, nodeAt_of_ksb hk]))

theorem VckW.trans {y : U64} {s0 s1 s2 : S} (h1 : WritesIn st s0 s1 (VckW st T Cs Scs y s0))
    (h2 : WritesIn st s1 s2 (VckW st T Cs Scs y s1)) : WritesIn st s0 s2 (VckW st T Cs Scs y s0) :=
  (h1.trans h2).mono fun _ hb => hb.elim id (VckW.ksb h1.1 h1.2.1)

theorem VckR.vckW {y : U64} {s0 s1 : S} (h : WritesIn st s0 s1 (VckR st T Cs Scs y s0)) :
    WritesIn st s0 s1 (VckW st T Cs Scs y s0) := h.mono fun _ hb => Or.inl hb

theorem VckR.not_fld {y z K : U64} {s0 : S} (hT : TcbPlaced T) (hy : y ∈ T) (hz : z ∈ T) (hK : K.val < 4096)
    (hne : z = y → K.val < 256 ∨ 3328 ≤ K.val) : ¬ VckR st T Cs Scs y s0 (core.num.U64.wrapping_add z K) := by
  rintro (⟨hout, -⟩ | ⟨K', h1, h2, -, e⟩)
  · exact out_ne_field hout hz (hT z hz) hK rfl
  · exact field_ne (hT z hz) (hT y hy) hK (by omega) (fun h => by have := hne h; omega) e

theorem VckW.not_fld {y z K : U64} {s0 : S} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s0 c)
    (hcpu : L.cpu s0 ∈ Cs) (hy : y ∈ T) (hz : z ∈ T) (hK : K.val < 4096)
    (hne : z = y → K.val < 256 ∨ 3328 < K.val) :
    ¬ VckW st T Cs Scs y s0 (core.num.U64.wrapping_add z K) := by
  rintro (h | e | e)
  · exact VckR.not_fld hT hy hz hK (fun h => by have := hne h; omega) h
  · rw [stA_eq] at e
    have h3 : (3328#u64 : U64).val = 3328 := by simp
    exact field_ne (hT z hz) (hT y hy) hK (by omega) (fun h => by have := hne h; omega) e
  · exact node_ne_field (NP _ hcpu) (by rw [act_val]; omega) hz (hT z hz) hK e.symm

theorem VckR.not_node {y c o : U64} {s0 : S} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s0 c)
    (hy : y ∈ T) (hc : c ∈ Cs) (ho : o.val < 4288) : ¬ VckR st T Cs Scs y s0 (L.nodeAt s0 c o) := by
  rintro (⟨hout, -⟩ | ⟨K, -, hK, -, e⟩)
  · exact out_ne_node hout hc (NP c hc) ho rfl
  · exact node_ne_field (NP c hc) ho hy (hT y hy) (by omega) e

theorem VckW.not_node {y c o : U64} {s0 : S} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s0 c)
    (hcpu : L.cpu s0 ∈ Cs) (hy : y ∈ T) (hc : c ∈ Cs) (ho : o.val < 4288)
    (h16 : c = L.cpu s0 → o.val ≠ 16) : ¬ VckW st T Cs Scs y s0 (L.nodeAt s0 c o) := by
  rintro (h | e | e)
  · exact VckR.not_node hT NP hy hc ho h
  · rw [stA_eq] at e; exact node_ne_field (NP c hc) ho hy (hT y hy) (by simp) e
  · by_cases hcc : c = L.cpu s0
    · subst hcc
      exact nodeAt_ne (NP _ hcpu) ho (by rw [act_val]; omega) (by rw [act_val]; exact h16 rfl) e
    · exact nodeAt_ne_cpu (NP c hc) (NP _ hcpu) ho (by rw [act_val]; omega) hcc e

/-- **The frame of a `VckW` write.** -/
theorem VckW.frames {y : U64} {s s' : S} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hy : y ∈ T) (w : WritesIn st s s' (VckW st T Cs Scs y s)) :
    L.cpu s' = L.cpu s ∧ L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧ L.idleW s' = L.idleW s ∧
      (∀ z ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (z = y → K.val < 256 ∨ 3328 < K.val) →
        L.mem s' (core.num.U64.wrapping_add z K) = L.mem s (core.num.U64.wrapping_add z K)) ∧
      (∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → (c = L.cpu s → o.val ≠ 16) →
        L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) := by
  have hT := hq.tcbs
  have NP := hq.nodes
  have hc := hq.cur
  have nd : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → (c = L.cpu s → o.val ≠ 16) →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := fun c hc' o ho h8 h16 =>
    w.mem_eq (nodeAt_aligned (NP c hc') ho h8) (VckW.not_node hT NP hc hy hc' ho h16)
  refine ⟨w.2.1, ?_, ?_, ?_, fun z hz K hK hK8 hne =>
    w.mem_eq (field_aligned (hT z hz) hK hK8) (VckW.not_fld hT NP hc hy hz hK hne), nd⟩
  · unfold LawfulStore.curW
    rw [w.2.1, nodeAt_of_ksb w.1]
    exact nd _ hc _ (by rw [curth0]; omega) (by rw [curth0]) (fun _ => by rw [curth0]; omega)
  · unfold LawfulStore.cscW LawfulStore.nodeA
    rw [w.2.1, nodeAt_of_ksb w.1]
    exact nd _ hc _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (fun _ => by simp [layout.node.CUR_SC])
  · unfold LawfulStore.idleW
    rw [w.2.1, nodeAt_of_ksb w.1]
    exact nd _ hc _ (by rw [idle8]; omega) (by rw [idle8]) (fun _ => by rw [idle8]; omega)

/-! ## `vcpu::check` -/

/-- (#80 / #81) **`vcpu.report` of a `RUNNING_VM` thread, a pending exit
allowed**: as P1's `vcpu.report.xf`, its writes before the final state change
are `RepW` words, the VCPU's `PENDING` word (cleared when set) being a user
word of `U`. -/
theorem vcpu.report.xfV (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t badge : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hvm : L.mem s (stA t) = sched.TS_RUNNING_VM)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hbuf : msg.lookup_ipc_buffer st s true t ⦃ b => BufOK U b ⦄)
    (hpw : L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add t 3664#u64)) vcpu.PENDING) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add t 3664#u64)) vcpu.PENDING ∈ U) :
    vcpu.report st ar s a t badge ⦃ s' => ∃ s1, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧
      L.mem s1 (stA t) = sched.TS_RUNNING_VM ∧ WritesIn st s s1 (RepW t U) ∧
      sched.set_thread_state st s1 t sched.TS_RUNNING = ok s' ⦄ := by
  have hS0 : P0.StoreTotal st := L.total
  have hT : TcbPlaced T := h.1.choose_spec.choose_spec.tcbs
  refine vcpu.report.gen (Bok := BufOK U) (vOk := fun v => core.num.U64.wrapping_add v vcpu.PENDING ∈ U)
    (P := fun s1 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧ L.mem s1 (stA t) = sched.TS_RUNNING_VM ∧
      WritesIn st s s1 (RepW t U)) hA ⟨?_, ?_, ?_⟩ ?_ ⟨h, hvm, WritesIn.refl _ _⟩ hbuf hpw
  · rintro s1 b i v hb ⟨h1, st1, w1⟩ hi
    exact WP.spec_mono (msg.set_mr.xw s1 (hT t ht) hb (fun b hb => (hU b hb).ksb w1.1) (by omega)) fun r w =>
      xw_step h1 st1 w1 (fun b hb => (hU b hb).ksb w1.1) w ht
  · rintro s1 r v ⟨h1, st1, w1⟩ hr
    have hr' : r.val < 384 := by
      rcases hr with rfl | rfl | rfl <;>
        simp [layout.reg.MSG_INFO, layout.reg.BADGE, layout.reg.FAULT_IP, layout.reg.RSI, layout.reg.RDI]
    refine WP.spec_mono (obj.Tcb.set_reg.wrS s1 t r v (hT t ht) hr') fun s2 hs2 => ?_
    obtain ⟨K, hK, e⟩ := hs2
    subst e
    exact xw_step h1 st1 w1 (fun b hb => (hU b hb).ksb w1.1) ((writesIn_wr (field_aligned (hT t ht) (by omega)
      (by omega))).mono fun b e => Or.inl ⟨K, by omega, by omega, by omega, e⟩) ht
  · rintro s1 v ⟨h1, st1, w1⟩ hv
    have hv' : core.num.U64.wrapping_add v vcpu.PENDING ∈ U := hv
    unfold vcpu.set
    simp only [lift, bind_ok]
    refine WP.spec_mono (LawfulStore.write_spec s1 _ 0#u64) fun s2 e => ?_
    subst e
    exact xw_step h1 st1 w1 (fun b hb => (hU b hb).ksb w1.1)
      ((writesIn_wr (hU _ hv').out.1).mono fun b e => Or.inr (by rw [e]; exact hv')) ht
  · intro s1 h1
    exact WP.spec_mono (spec_eq' (Fl4Proofs.P0.sched.set_thread_state.p0 _ _ _ _ hS0)) fun s' hs' =>
      ⟨s1, h1.1, h1.2.1, h1.2.2, hs'.1⟩

/-- The report's `RepW` words are `VckR` words. -/
theorem RepW.vckR {s : S} {t b : U64} (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (h : RepW t U b) : VckR st T Cs Scs t s b := by
  rcases h with ⟨K, h1, h2, h3, e⟩ | hu
  · exact Or.inr ⟨K, h1, h2, h3, e⟩
  · refine Or.inl ⟨(hU b hu).out, fun c hc => ?_⟩
    obtain ⟨⟨-, i1⟩, ⟨-, i2⟩⟩ := vck_sclink_in hO hc
    exact ⟨fun e => (hU b hu).sc c hc (by rw [e]; exact i1), fun e => (hU b hu).sc c hc (by rw [e]; exact i2)⟩

/-- The post of `vcpu.check` (and its report) as a `VckW` step. -/
abbrev VckPost (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (y : U64) (s s' : S) : Prop :=
  EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ WritesIn st s s' (VckW st T Cs Scs y s) ∧
    (L.actionW s' = L.actionW s ∨ L.actionW s' = sched.ACTION_CHOOSE_NEW) ∧
    (L.mem s' (stA y) = L.mem s (stA y) ∨ (Runnable (L.mem s (stA y)) ∧ L.mem s' (stA y) = sched.TS_RUNNING))

theorem VckPost.trans {y : U64} {s s1 s2 : S} (h1 : VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac y s s1)
    (h2 : VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac y s1 s2) : VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac y s s2 := by
  obtain ⟨-, w1, a1, t1⟩ := h1
  obtain ⟨E2, w2, a2, t2⟩ := h2
  refine ⟨E2, VckW.trans w1 w2, ?_, ?_⟩
  · rcases a2 with e2 | e2
    · rw [e2]; exact a1
    · exact Or.inr e2
  · rcases t2 with e2 | ⟨r2, e2⟩
    · rw [e2]; exact t1
    · rcases t1 with e1 | ⟨r1, -⟩
      · rw [e1] at r2; exact Or.inr ⟨r2, e2⟩
      · exact Or.inr ⟨r1, e2⟩

/-- **The current thread's report keeps `EntryInv`**, as a `VckW` step. -/
theorem vcpu.report.vck (hA : P0.ArchTotal ar) {s : S} (a : A) (y badge : U64)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y = L.curW s)
    (hvm : L.mem s (stA y) = sched.TS_RUNNING_VM)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hbuf : msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (hpw : L.mem s (core.num.U64.wrapping_add y 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add y 3664#u64)) vcpu.PENDING) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add y 3664#u64)) vcpu.PENDING ∈ U) :
    vcpu.report st ar s a y badge ⦃ s' => VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac y s s' ⦄ := by
  subst hy
  have hb := (EntryInv.vckBlk h)
  obtain ⟨⟨Q, R, hq⟩, -, hX, -, -⟩ := (EntryInv.vckBlk h)
  have hT := hq.tcbs
  have hcT : L.curW s ∈ T := hq.curT
  refine WP.spec_mono (vcpu.report.xfV hA s a _ badge hb hcT hvm hU hbuf hpw) ?_
  rintro s' ⟨s2, h2, st2, w2, e⟩
  have w2' : WritesIn st s s2 (VckW st T Cs Scs (L.curW s) s) := VckR.vckW (w2.mono fun b hb => RepW.vckR hU hX.1 hb)
  obtain ⟨-, eC2, ec2, -, fld2, -⟩ := VckW.frames hq hcT w2'
  have hN := hq.nodes _ hq.cur
  have ea2 : L.actionW s2 = L.actionW s := vck_actionW_of w2 hN (by
    rintro (⟨K, -, hK, -, e'⟩ | hu)
    · exact node_ne_field hN (by rw [act_val]; omega) hcT (hT _ hcT) (by omega) e'
    · exact out_ne_node (hU _ hu).out hq.cur hN (by rw [act_val]; omega) rfl)
  have esc2 : ∀ z ∈ T, L.mem s2 (scA z) = L.mem s (scA z) := fun z hz => by
    rw [scA_eq]; exact fld2 z hz _ (by simp) (by simp) (fun _ => Or.inr (by simp))
  have E2 := EntryInv.vckStep h h2 ec2 eC2 (Or.inl ea2) esc2
  obtain ⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩ := h2
  have hN2 : NodePlaced st T s2 (L.cpu s2) := by rw [w2.2.1]; exact hN.ksb w2.1
  have hst := sts_all s2 (L.curW s) _ Q2 R2 q2 hB2 hX2 hS2 hSg2 hcT not_blocked_running running_ne
    (Or.inr (by rw [st2]; exact not_blocked_vm))
    (hX2.noref (q2.tcbs _ hcT) (by rw [st2]; exact runnable_ne_reply (Or.inr (Or.inr rfl)))
      (by rw [st2]; exact runnable_ne_recv (Or.inr (Or.inr rfl))))
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩
  have hw := sched.set_thread_state.vckW2 s2 (L.curW s) sched.TS_RUNNING hT hN2 hcT
  rw [e, WP.spec_ok] at hst hw
  obtain ⟨q6, hB6, hX6, hS6, hSg6, st6, -⟩ := hst
  obtain ⟨w3, ea3, -⟩ := hw
  have w3' : WritesIn st s2 s' (VckW st T Cs Scs (L.curW s) s2) :=
    w3.mono fun b hb => hb.elim (fun e => Or.inr (Or.inl e)) (fun e => Or.inr (Or.inr e))
  obtain ⟨-, eC3, ec3, -, fld3, -⟩ := VckW.frames q2 hcT w3'
  have E3 := EntryInv.vckStep E2 ⟨⟨Q2, R2, q6.congrX empty_congr⟩, hB6, hX6, hS6, hSg6⟩ ec3 eC3
    (ea3.imp id (fun e => e.trans choose_val)) (fun z hz => by
      rw [scA_eq]; exact fld3 z hz _ (by simp) (by simp) (fun _ => Or.inr (by simp)))
  refine ⟨E3, VckW.trans w2' w3', ?_, Or.inr ⟨Or.inr (Or.inr hvm), st6⟩⟩
  rcases ea3 with e3 | e3
  · exact Or.inl (e3.trans ea2)
  · exact Or.inr e3

/-- A `VckW` write keeps the buffer-lookup words of every TCB. -/
theorem VckW.ibFr {y : U64} {s s' : S} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hy : y ∈ T) (w : WritesIn st s s' (VckW st T Cs Scs y s)) :
    IbFr (L := L) T s s' := by
  obtain ⟨-, -, -, -, fld, -⟩ := VckW.frames hq hy w
  refine ⟨w.1, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · show L.mem s' (core.num.U64.wrapping_add t 3512#u64) = L.mem s (core.num.U64.wrapping_add t 3512#u64)
    exact fld t ht _ (by simp) (by simp) (fun _ => Or.inr (by simp))
  · rw [sbWordA_eq]; exact fld t ht _ (by simp) (by simp) (fun _ => Or.inl (by simp))
  · rw [sbWordA8_eq]; exact fld t ht _ (by simp) (by simp) (fun _ => Or.inl (by simp))

/-- **`vcpu::check` of the current thread keeps `EntryInv`, as a `VckW` step**
(module docstring). Named premise `hpw` [P]: the bound VCPU's `PENDING` word
is a user word of `U`. -/
theorem vcpu.check.vck (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK U b ⦄)
    (hpw : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64)) vcpu.PENDING ∈ U) :
    vcpu.check st ar s a (L.curW s) ⦃ s' _ => VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac (L.curW s) s s' ⦄ := by
  obtain ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ := (EntryInv.vckBlk h)
  have hT := hq.tcbs
  have hcT : L.curW s ∈ T := hq.curT
  have hta := hT _ hcT
  have OK0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac (L.curW s) s s' ⦄ :=
    (WP.spec_ok _).2 ⟨h, WritesIn.refl _ _, Or.inl rfl, Or.inl rfl⟩
  unfold vcpu.check
  step with obj.Tcb.state.spec as ⟨i, ei⟩
  split
  · exact OK0
  rename_i hvm0
  have hvm : L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM := by
    rw [← ei]; by_contra hne; exact hvm0 (bne_iff_ne.mpr hne)
  have REP0 : ∀ bd : U64, (do
      let s1 ← vcpu.report st ar s a (L.curW s) bd
      ok (s1, a)) ⦃ s' _ => VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac (L.curW s) s s' ⦄ := fun bd =>
    WP.spec_bind (vcpu.report.vck hA a _ bd h rfl hvm hU hbuf (fun h0 _ => hpw h0)) fun s1 hs1 =>
      (WP.spec_ok _).2 hs1
  -- the bound notification's badge (the VCPU, if any, has no pending exit)
  have NT : (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64)) vcpu.PENDING) =
        0#u64) → ∀ n : U64, n = L.mem s (boundA (L.curW s)) → n ≠ 0#u64 → L.epState s n = obj.NTFN_ACTIVE →
      (do
        let badge ← obj.Ntfn.badge st n s
        let s1 ← obj.Ntfn.set_state st n s obj.NTFN_IDLE
        let s2 ← vcpu.report st ar s1 a (L.curW s) badge
        ok (s2, a)) ⦃ s' _ => VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac (L.curW s) s s' ⦄ := by
    intro hP0 n en hn0 hact
    have hnN : n ∈ Nt := by rw [en]; exact hX.2.2.bnd _ hcT (by rw [← en]; exact hn0)
    have hnH := hNt n hnN
    obtain ⟨E, EQ, hEW⟩ := hq.eps
    have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hnH)
    obtain ⟨hE, hEN, -⟩ := hEW.1 n he
    have hEΩ : ∀ x ∈ Ω, x.val + 8 ≤ n.val ∨ n.val + 16 ≤ x.val := hEW.2.2.1 n he
    have hTS := epTSA_val hE
    have a2 : Aligned (epTSA n) := (ep_aligned hE).2
    refine WP.spec_bind (obj.Ntfn.badge.any s n) fun bd _ => ?_
    refine WP.spec_bind (obj.Ntfn.set_state.val s n _) fun s1 e1 => ?_
    subst e1
    obtain ⟨h2, hB2, hX2, hS2, hSg2, f2, -, ea2, -, ec2⟩ :=
      ntfn_idle_all hq hB hX hS hSg hnH (by rw [hact, ntfn_active_val])
    set s1 := L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)) with hs1
    -- the notification word is a `VckW` word
    have hout : OutsideObjs st T Cs s (epTSA n) := by
      refine ⟨a2, fun t ht => ?_, fun c hc => ?_⟩
      · have := hE.disj t ht; rw [hTS]; omega
      · have := hEN.1 c hc; rw [hTS]; omega
    have hnh : ∀ c ∈ Scs, epTSA n ≠ scReplyA c ∧ epTSA n ≠ scTcbA c := by
      intro c hc
      obtain ⟨⟨a1, i1⟩, ⟨a3, i3⟩⟩ := vck_sclink_in hX.1 hc
      have r1 := hEΩ _ (hX.1.scW c hc _ a1 i1)
      have r3 := hEΩ _ (hX.1.scW c hc _ a3 i3)
      refine ⟨fun e => ?_, fun e => ?_⟩
      · have := congrArg UScalar.val e; rw [hTS] at this; omega
      · have := congrArg UScalar.val e; rw [hTS] at this; omega
    have w1 : WritesIn st s s1 (VckW st T Cs Scs (L.curW s) s) :=
      (writesIn_wr a2).mono fun b e => Or.inl (Or.inl (by rw [e]; exact ⟨hout, hnh⟩))
    obtain ⟨-, eC1, ec1, -, fld1, -⟩ := VckW.frames hq hcT w1
    have h1 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s1 :=
      EntryInv.vckStep h ⟨⟨Q, R, h2⟩, hB2, hX2, hS2, hSg2⟩ ec1 eC1 (Or.inl ea2) fun z hz => by
        rw [scA_eq]; exact fld1 z hz _ (by simp) (by simp) (fun _ => Or.inr (by simp))
    have st1 : L.mem s1 (stA (L.curW s)) = sched.TS_RUNNING_VM := by
      rw [stA_eq, f2 _ hcT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hvm
    have C1 : VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac (L.curW s) s s1 :=
      ⟨h1, w1, Or.inl ea2, Or.inl (by rw [st1, hvm])⟩
    have hU1 : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s1 b := fun b hb => (hU b hb).ksb w1.1
    have hbuf1 : msg.lookup_ipc_buffer st s1 true (L.curW s) ⦃ b => BufOK U b ⦄ := by
      rw [lookup_ipc_buffer_same ((VckW.ibFr hq hcT w1).2 _ hcT)]; exact hbuf
    have ev1 : L.mem s1 (core.num.U64.wrapping_add (L.curW s) 3664#u64) =
        L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) :=
      f2 _ hcT _ (by simp) (by simp) (by simp) (by simp)
    have hp1 : L.mem s1 (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
        L.mem s1 (core.num.U64.wrapping_add (L.mem s1 (core.num.U64.wrapping_add (L.curW s) 3664#u64))
          vcpu.PENDING) = 0#u64 := by
      intro hv0
      rw [ev1] at hv0 ⊢
      have hu := hU _ (hpw hv0)
      have hne := hu.eps n (Or.inr hnH)
      rw [hs1, L.mem_wr_ne a2 hu.out.1 (by rw [hTS]; omega)]
      exact hP0 hv0
    refine WP.spec_bind (vcpu.report.vck hA a _ bd h1 eC1.symm st1 hU1 hbuf1 (fun h0 hp => absurd (hp1 h0) hp))
      fun s2 hs2 => (WP.spec_ok _).2 (C1.trans hs2)
  unfold vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  split
  · rename_i hv0
    unfold vcpu.get
    simp only [lift, bind_ok]
    refine WP.spec_bind (LawfulStore.read_spec s _) fun i1 ei1 => ?_
    split
    · exact REP0 0#u64
    · rename_i hi1
      have hP0 : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
          L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64))
            vcpu.PENDING) = 0#u64 := fun _ => by
              rw [← ev, ← ei1]; by_contra hne; exact hi1 (bne_iff_ne.mpr hne)
      refine WP.spec_bind (obj.Tcb.bound_ntfn.val s _) fun i2 ei2 => ?_
      split
      · rename_i hi2
        refine WP.spec_bind (obj.Ntfn.state.spec s i2) fun i3 ei3 => ?_
        split
        · rename_i hi3
          exact NT hP0 i2 ei2 (by simpa using hi2) (by rw [← ei3]; exact hi3)
        · split
          · exact REP0 0#u64
          · exact OK0
      · split
        · exact REP0 0#u64
        · exact OK0
  · rename_i hv0
    have hP0 : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
        L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64))
          vcpu.PENDING) = 0#u64 := fun hne => absurd (by rw [← ev]; by_contra hne'; exact hv0 (bne_iff_ne.mpr hne')) hne
    refine WP.spec_bind (obj.Tcb.bound_ntfn.val s _) fun i2 ei2 => ?_
    split
    · rename_i hi2
      refine WP.spec_bind (obj.Ntfn.state.spec s i2) fun i3 ei3 => ?_
      split
      · rename_i hi3
        exact NT hP0 i2 ei2 (by simpa using hi2) (by rw [← ei3]; exact hi3)
      · split
        · exact REP0 0#u64
        · exact OK0
    · split
      · exact REP0 0#u64
      · exact OK0

/-- **(P1) `vcpu::check` of the current thread keeps `EntryInv`** (what
`EntryHyps0` / `P3Place` used to assume as `vmchk`; `EntryHyps0.vmchk` derives
it from their placement field `vmpl`). Named premises `hbuf` [P] (the thread's
IPC buffer in `U`) and `hpw` [P]: the thread's bound VCPU's `PENDING` word is a
user word of `U` (a VCPU is a heap object off the kernel's typed objects, P1
`VcpuPl.bound`). -/
theorem vcpu.check.entry (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK U b ⦄)
    (hpw : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64)) vcpu.PENDING ∈ U) :
    vcpu.check st ar s a (L.curW s) ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  refine WP.spec_mono (vcpu.check.vck hA hNt s a h hU hbuf hpw) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  exact hh.1

end

end Fl4Proofs.P1
