/-
P1 (vmchk, AArch64): **`vcpu::check` of the current thread keeps `EntryInv`** (`vcpu.check.entry`) and
[J] `RunVcpuInv` (`vcpu.check.rv`). An AArch64 rework of x86_64's `Fl4Proofs.P1.VcpuCheckInv`, not a port:
AArch64 `vcpu::check` of a `TS_RUNNING_VM` thread does not report through `vcpu::report` (the identity on
AArch64); it either resumes the thread (`RUN_VCPU` 0: `FAULT_IP := NEXT_IP`, state `RUNNING`) or, with the
bound notification active, makes the notification idle and completes the thread's `ARMVCPURun`
(`vcpu::complete_run`): it may copy the VCPU's state into the run frame (the frame of the thread's
IPC-buffer cap at the VCPU's `RUN_OFFSET`, `read_state_to_frame`), clears the VCPU's `RUN_CALLER` word and
the thread's `RUN_VCPU` word (TCB + 3672), writes the thread's `BADGE` / X2..X5 / message-info / `FAULT_IP`
registers, makes it `RUNNING` and reloads its VM root (`set_vm_root`, no write).

* `VckW y s0`: the words `vcpu::check` of `y` writes: x86's (`VckR`: words outside the TCBs and nodes that
  are no SC `REPLY`/`TCB` header, and `y`'s register words 256..3328; `y`'s `STATE`; the executing core's
  `SCHED_ACTION`) and **`y`'s `RUN_VCPU` word** (`runVcpuA y`). `VckW.frames`: such a write keeps every TCB
  field but `y`'s registers, `STATE` and `RUN_VCPU`.
* `VckPost`: x86's four conjuncts and a fifth, `RunVcpuInv` carried along.
* `FrU U f`: the 128 words from `f` are in `U` (`BufOK`'s body, without its null guard);
  `vcpu.read_state_to_frame.fw`: the copy into a frame `f` with `FrU U f` writes `U` words only.
* `RunBuf U s y`: the run frame of `y` (when `complete_run` would copy into it) satisfies `FrU U`.
* `vcpu.complete_run.vck`, `vcpu.check.vck`: as `VckPost` steps; **`vcpu.check.entry`**, `vcpu.check.rv`.

Named premises of `vcpu.complete_run.vck` / `vcpu.check.vck` / `vcpu.check.entry` / `vcpu.check.rv`
(both placement, the A64 counterparts of x86's `hbuf` / `hpw`, same shape and tag):
* `hbuf` **[P]** (`RunBuf U s y`): the thread's run frame lies in the user words `U`: if its IPC-buffer
  slot holds a writable non-device frame cap and the VCPU's `RUN_OFFSET` passes `complete_run`'s checks
  (64-aligned, inside the frame, `vcpu_state_mask::SIZE` = 1024 bytes to its end), the 128 words from
  frame + offset are in `U` (x86: `msg.lookup_ipc_buffer … ⦃ BufOK U ⦄`, the IPC buffer in `U`);
* `hpw` **[P]**: the thread's run VCPU's `RUN_CALLER` word is in `U` (x86: the bound VCPU's `PENDING`
  word; a VCPU is a heap object of its own, P1 gives no `UsrW` for its words).
No [J] premise: `vcpu.check.rv` proves that `vcpu::check` keeps [J] `RunVcpuInv` (it is not assumed).
-/
import Fl4ProofsA64.P1.QueueFire
import Fl4ProofsA64.P1.VcpuHooks
import Fl4ProofsA64.P1.VmRootRd
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}
variable {A : Type _} {ar : machine.Arch A}

/-! ## Helpers (as x86's VcpuCheckInv) -/

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

/-- a64: a write of a TCB's `RUN_VCPU` word (field 3672) keeps `BlkOK` and the thread's state word
(`reg_all`'s proof at K = 3672). -/
theorem rv_all {s : S} {t K v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hK : K.val = 3672) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add t K) v) ∧
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (stA t) = L.mem s (stA t) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hta := hT t ht
  obtain ⟨b1, b2⟩ := bx_field (K := K) (v := v) h0 hB hX hSg.sub ht (by omega) (by omega)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega) (Or.inr (by omega))
  refine ⟨⟨⟨Q, R, inv_wr_field h0 ht (by omega) (by omega)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)⟩, b1, b2,
    SCsOK.field h0 hS hX ht (by omega) (by omega) (by omega),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩, ?_⟩
  rw [stA_eq]
  exact L.mem_wr_ne (field_aligned hta (by omega) (by omega)) (field_aligned hta (by simp) (by simp))
    (fun e => field_ne (K1 := K) (K2 := 3328#u64) hta hta (by omega) (by simp)
      (fun _ => by first | omega | (simp; omega) | simp) (UScalar.eq_of_val_eq e))

/-! ## The words of `vcpu::check` -/

/-- Words outside the TCBs and nodes that are no SC header, and `y`'s register words. -/
def VckR (st : machine.Store S) [L : LawfulStore st] (T Cs Scs : Set U64) (y : U64) (s0 : S) (b : U64) : Prop :=
  (OutsideObjs st T Cs s0 b ∧ ∀ c ∈ Scs, b ≠ scReplyA c ∧ b ≠ scTcbA c) ∨
  (∃ K : U64, 256 ≤ K.val ∧ K.val < 3328 ∧ K.val % 8 = 0 ∧ b = core.num.U64.wrapping_add y K)

/-- **The words of `vcpu::check` of `y`** (module docstring): x86's, and `y`'s `RUN_VCPU` word. -/
def VckW (st : machine.Store S) [L : LawfulStore st] (T Cs Scs : Set U64) (y : U64) (s0 : S) (b : U64) : Prop :=
  VckR st T Cs Scs y s0 b ∨ b = stA y ∨ b = L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION ∨ b = runVcpuA y

theorem VckR.ksb {y : U64} {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0)
    (h : VckR st T Cs Scs y s1 b) : VckR st T Cs Scs y s0 b := by
  rcases h with ⟨ho, hh⟩ | h
  · exact Or.inl ⟨ho.ksb hk.symm, hh⟩
  · exact Or.inr h

theorem VckW.ksb {y : U64} {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (hc : L.cpu s1 = L.cpu s0)
    (h : VckW st T Cs Scs y s1 b) : VckW st T Cs Scs y s0 b := by
  rcases h with h | h | h | h
  · exact Or.inl (VckR.ksb hk h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (by rw [h, hc, nodeAt_of_ksb hk])))
  · exact Or.inr (Or.inr (Or.inr h))

theorem VckW.trans {y : U64} {s0 s1 s2 : S} (h1 : WritesIn st s0 s1 (VckW st T Cs Scs y s0))
    (h2 : WritesIn st s1 s2 (VckW st T Cs Scs y s1)) : WritesIn st s0 s2 (VckW st T Cs Scs y s0) :=
  (h1.trans h2).mono fun _ hb => hb.elim id (VckW.ksb h1.1 h1.2.1)

theorem VckR.not_fld {y z K : U64} {s0 : S} (hT : TcbPlaced T) (hy : y ∈ T) (hz : z ∈ T) (hK : K.val < 4096)
    (hne : z = y → K.val < 256 ∨ 3328 ≤ K.val) : ¬ VckR st T Cs Scs y s0 (core.num.U64.wrapping_add z K) := by
  rintro (⟨hout, -⟩ | ⟨K', h1, h2, -, e⟩)
  · exact out_ne_field hout hz (hT z hz) hK rfl
  · exact field_ne (hT z hz) (hT y hy) hK (by omega) (fun h => by have := hne h; omega) e

theorem VckW.not_fld {y z K : U64} {s0 : S} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s0 c)
    (hcpu : L.cpu s0 ∈ Cs) (hy : y ∈ T) (hz : z ∈ T) (hK : K.val < 4096)
    (hne : z = y → K.val < 256 ∨ (3328 < K.val ∧ K.val ≠ 3672)) :
    ¬ VckW st T Cs Scs y s0 (core.num.U64.wrapping_add z K) := by
  rintro (h | e | e | e)
  · exact VckR.not_fld hT hy hz hK (fun h => by have := hne h; omega) h
  · rw [stA_eq] at e
    have h3 : (3328#u64 : U64).val = 3328 := by simp
    exact field_ne (hT z hz) (hT y hy) hK (by omega) (fun h => by have := hne h; omega) e
  · exact node_ne_field (NP _ hcpu) (by rw [act_val]; omega) hz (hT z hz) hK e.symm
  · have h3 : (3672#u64 : U64).val = 3672 := by simp
    exact field_ne (K2 := 3672#u64) (hT z hz) (hT y hy) hK (by omega) (fun h => by have := hne h; omega) e

theorem VckR.not_node {y c o : U64} {s0 : S} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s0 c)
    (hy : y ∈ T) (hc : c ∈ Cs) (ho : o.val < 4288) : ¬ VckR st T Cs Scs y s0 (L.nodeAt s0 c o) := by
  rintro (⟨hout, -⟩ | ⟨K, -, hK, -, e⟩)
  · exact out_ne_node hout hc (NP c hc) ho rfl
  · exact node_ne_field (NP c hc) ho hy (hT y hy) (by omega) e

theorem VckW.not_node {y c o : U64} {s0 : S} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s0 c)
    (hcpu : L.cpu s0 ∈ Cs) (hy : y ∈ T) (hc : c ∈ Cs) (ho : o.val < 4288)
    (h16 : c = L.cpu s0 → o.val ≠ 16) : ¬ VckW st T Cs Scs y s0 (L.nodeAt s0 c o) := by
  rintro (h | e | e | e)
  · exact VckR.not_node hT NP hy hc ho h
  · rw [stA_eq] at e; exact node_ne_field (NP c hc) ho hy (hT y hy) (by simp) e
  · by_cases hcc : c = L.cpu s0
    · subst hcc
      exact nodeAt_ne (NP _ hcpu) ho (by rw [act_val]; omega) (by rw [act_val]; exact h16 rfl) e
    · exact nodeAt_ne_cpu (NP c hc) (NP _ hcpu) ho (by rw [act_val]; omega) hcc e
  · exact node_ne_field (K := 3672#u64) (NP c hc) ho hy (hT y hy) (by simp) e

/-- **The frame of a `VckW` write.** -/
theorem VckW.frames {y : U64} {s s' : S} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hy : y ∈ T) (w : WritesIn st s s' (VckW st T Cs Scs y s)) :
    L.cpu s' = L.cpu s ∧ L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧ L.idleW s' = L.idleW s ∧
      (∀ z ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (z = y → K.val < 256 ∨ (3328 < K.val ∧ K.val ≠ 3672)) →
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

/-- A `VckW` write keeps the buffer-lookup words of every TCB. -/
theorem VckW.ibFr {y : U64} {s s' : S} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hy : y ∈ T) (w : WritesIn st s s' (VckW st T Cs Scs y s)) :
    IbFr (L := L) T s s' := by
  obtain ⟨-, -, -, -, fld, -⟩ := VckW.frames hq hy w
  refine ⟨w.1, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · show L.mem s' (core.num.U64.wrapping_add t 3512#u64) = L.mem s (core.num.U64.wrapping_add t 3512#u64)
    exact fld t ht _ (by simp) (by simp) (fun _ => Or.inr ⟨by simp, by simp⟩)
  · rw [sbWordA_eq]; exact fld t ht _ (by simp) (by simp) (fun _ => Or.inl (by simp))
  · rw [sbWordA8_eq]; exact fld t ht _ (by simp) (by simp) (fun _ => Or.inl (by simp))

/-- The user words `U` (`UsrW`) are `VckR` words. -/
theorem usr_vckR {s : S} {t b : U64} (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hu : b ∈ U) : VckR st T Cs Scs t s b := by
  refine Or.inl ⟨(hU b hu).out, fun c hc => ?_⟩
  obtain ⟨⟨-, i1⟩, ⟨-, i2⟩⟩ := vck_sclink_in hO hc
  exact ⟨fun e => (hU b hu).sc c hc (by rw [e]; exact i1), fun e => (hU b hu).sc c hc (by rw [e]; exact i2)⟩

/-- **The post of `vcpu.check`** as a `VckW` step: x86's four conjuncts and [J] `RunVcpuInv` carried. -/
abbrev VckPost (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (y : U64) (s s' : S) : Prop :=
  EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ WritesIn st s s' (VckW st T Cs Scs y s) ∧
    (L.actionW s' = L.actionW s ∨ L.actionW s' = sched.ACTION_CHOOSE_NEW) ∧
    (L.mem s' (stA y) = L.mem s (stA y) ∨ (Runnable (L.mem s (stA y)) ∧ L.mem s' (stA y) = sched.TS_RUNNING)) ∧
    (RunVcpuInv st T s → RunVcpuInv st T s')

theorem VckPost.refl {y : U64} {s : S} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac y s s := ⟨h, WritesIn.refl _ _, Or.inl rfl, Or.inl rfl, id⟩

theorem VckPost.trans {y : U64} {s s1 s2 : S} (h1 : VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac y s s1)
    (h2 : VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac y s1 s2) : VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac y s s2 := by
  obtain ⟨-, w1, a1, t1, r1⟩ := h1
  obtain ⟨E2, w2, a2, t2, r2⟩ := h2
  refine ⟨E2, VckW.trans w1 w2, ?_, ?_, fun h => r2 (r1 h)⟩
  · rcases a2 with e2 | e2
    · rw [e2]; exact a1
    · exact Or.inr e2
  · rcases t2 with e2 | ⟨r2, e2⟩
    · rw [e2]; exact t1
    · rcases t1 with e1 | ⟨r1, -⟩
      · rw [e1] at r2; exact Or.inr ⟨r2, e2⟩
      · exact Or.inr ⟨r1, e2⟩

/-- **The end of a completion: `set_thread_state RUNNING`** of the current thread, from a `BlkOK` state
`s2` reached from an `EntryInv` state `s` by `VckW` writes that kept the action, with the thread still in
`TS_RUNNING_VM` and its `RUN_VCPU` word 0. -/
theorem vck_fin {s s2 : S} {y : U64} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y = L.curW s)
    (hvm : L.mem s (stA y) = sched.TS_RUNNING_VM) (h2 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2)
    (st2 : L.mem s2 (stA y) = sched.TS_RUNNING_VM) (w2 : WritesIn st s s2 (VckW st T Cs Scs y s))
    (ea2 : L.actionW s2 = L.actionW s) (rv2 : L.mem s2 (runVcpuA y) = 0#u64) :
    sched.set_thread_state st s2 y sched.TS_RUNNING ⦃ s' => VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac y s s' ⦄ := by
  subst hy
  obtain ⟨⟨Q, R, hq⟩, -, -, -, -⟩ := EntryInv.vckBlk h
  have hT := hq.tcbs
  have hcT : L.curW s ∈ T := hq.curT
  obtain ⟨-, eC2, ec2, -, fld2, -⟩ := VckW.frames hq hcT w2
  have esc2 : ∀ z ∈ T, L.mem s2 (scA z) = L.mem s (scA z) := fun z hz => by
    rw [scA_eq]; exact fld2 z hz _ (by simp) (by simp) (fun _ => Or.inr ⟨by simp, by simp⟩)
  have E2 := EntryInv.vckStep h h2 ec2 eC2 (Or.inl ea2) esc2
  obtain ⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩ := h2
  have hN := hq.nodes _ hq.cur
  have hN2 : NodePlaced st T s2 (L.cpu s2) := by rw [w2.2.1]; exact hN.ksb w2.1
  have hst := sts_all s2 (L.curW s) _ Q2 R2 q2 hB2 hX2 hS2 hSg2 hcT not_blocked_running running_ne
    (Or.inr (by rw [st2]; exact not_blocked_vm))
    (hX2.noref (q2.tcbs _ hcT) (by rw [st2]; exact runnable_ne_reply (Or.inr (Or.inr rfl)))
      (by rw [st2]; exact runnable_ne_recv (Or.inr (Or.inr rfl))))
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩
  have hw := sched.set_thread_state.vckW2 s2 (L.curW s) sched.TS_RUNNING hT hN2 hcT
  refine WP.spec_mono (WP.spec_and hst hw) fun s' ⟨hst', hw'⟩ => ?_
  obtain ⟨q6, hB6, hX6, hS6, hSg6, st6, -⟩ := hst'
  obtain ⟨w3, ea3, -⟩ := hw'
  have w3' : WritesIn st s2 s' (VckW st T Cs Scs (L.curW s) s2) :=
    w3.mono fun b hb => hb.elim (fun e => Or.inr (Or.inl e)) (fun e => Or.inr (Or.inr (Or.inl e)))
  obtain ⟨-, eC3, ec3, -, fld3, -⟩ := VckW.frames q2 hcT w3'
  have E3 := EntryInv.vckStep E2 ⟨⟨Q2, R2, q6.congrX empty_congr⟩, hB6, hX6, hS6, hSg6⟩ ec3 eC3
    (ea3.imp id (fun e => e.trans choose_val)) (fun z hz => by
      rw [scA_eq]; exact fld3 z hz _ (by simp) (by simp) (fun _ => Or.inr ⟨by simp, by simp⟩))
  have wA := VckW.trans w2 w3'
  obtain ⟨-, -, -, -, fldA, -⟩ := VckW.frames hq hcT wA
  refine ⟨E3, wA, ?_, Or.inr ⟨Or.inr (Or.inr hvm), st6⟩, fun hRV z hz h0 => ?_⟩
  · rcases ea3 with e3 | e3
    · exact Or.inl (e3.trans ea2)
    · exact Or.inr e3
  · by_cases hzc : z = L.curW s
    · subst hzc
      have hta := hT _ hcT
      have e : L.mem s' (runVcpuA (L.curW s)) = L.mem s2 (runVcpuA (L.curW s)) := by
        refine w3.mem_eq (field_aligned (K := 3672#u64) hta (by simp) (by simp)) ?_
        rintro (e | e)
        · rw [stA_eq] at e
          exact field_ne (K1 := 3672#u64) (K2 := 3328#u64) hta hta (by simp) (by simp) (fun _ => by simp) e
        · exact node_ne_field (K := 3672#u64) hN2 (by rw [act_val]; omega) hcT hta (by simp) e.symm
      exact absurd (e.trans rv2) h0
    · have es : L.mem s' (stA z) = L.mem s (stA z) := by
        rw [stA_eq]; exact fldA z hz _ (by simp) (by simp) (fun e => absurd e hzc)
      have er : L.mem s' (runVcpuA z) = L.mem s (runVcpuA z) :=
        fldA z hz 3672#u64 (by simp) (by simp) (fun e => absurd e hzc)
      rw [es]; exact hRV z hz (by rw [← er]; exact h0)

/-- `set_vm_root` and the `cur_thread` test before it leave the store unchanged. -/
theorem vck_vm_tail (hA : P0.ArchTotal ar) (s : S) (a : A) (y : U64) {P : S → Prop} (hP : P s) :
    (do
      let t ← sched.cur_thread st s
      let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq y t
      if b then vspace.set_vm_root st ar s a y else ok (s, a)) ⦃ s' _ => P s' ⦄ := by
  refine WP.spec_bind (P0.sched.cur_thread.p0 st s L.total) fun t _ => ?_
  refine WP.spec_bind (tcb_eq.blk y t) fun b _ => ?_
  split
  · refine WP.spec_mono (spec_eq' (P0.vspace.set_vm_root.p0 st ar s a y L.total hA)) fun r hr => ?_
    obtain ⟨s', a'⟩ := r
    have e : s' = s := set_vm_root_ok_s ar hr.1
    simp only [WP.uncurry'_pair]
    rw [e]; exact hP
  · exact (WP.spec_ok _).2 hP

/-! ## The copy into the run frame (`read_state_to_frame`) -/

/-- The 128 words from `f` are in `U` (`BufOK U f` without its null guard). -/
def FrU (U : Set U64) (f : U64) : Prop :=
  ∀ i : U64, i.val < 128 → core.num.U64.wrapping_add f (core.num.U64.wrapping_mul i 8#u64) ∈ U

theorem FrU.at {f r m : U64} (h : FrU U f) (hm : m.val = r.val * 8) (hr : r.val < 128) :
    core.num.U64.wrapping_add f m ∈ U := by
  have e : m = core.num.U64.wrapping_mul r 8#u64 := by
    apply UScalar.eq_of_val_eq
    simp [core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
  rw [e]; exact h r hr

theorem FrU.at2 {f g c m i : U64} (h : FrU U f) (hg : g = core.num.U64.wrapping_add f c) (hc : c.val = 512)
    (hm : m.val = i.val * 8) (hi : i.val < 64) : core.num.U64.wrapping_add g m ∈ U := by
  have e : core.num.U64.wrapping_add g m =
      core.num.U64.wrapping_add f (core.num.U64.wrapping_mul (core.num.U64.wrapping_add 64#u64 i) 8#u64) := by
    subst hg; apply UScalar.eq_of_val_eq
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    omega
  rw [e]; exact h _ (by simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega)

theorem wrU {s s1 : S} {b v : U64} (hal : ∀ b ∈ U, Aligned b) (w : WritesIn st s s1 (· ∈ U)) (hb : b ∈ U) :
    WritesIn st s (L.wr s1 b v) (· ∈ U) :=
  (w.trans (writesIn_wr (hal b hb))).mono fun x hx => hx.elim id (fun e => e ▸ hb)

theorem ite_total {α : Type _} {c : Prop} [Decidable c] {m1 m2 : Result α} (h1 : m1 ⦃ _ => True ⦄)
    (h2 : m2 ⦃ _ => True ⦄) : (if c then m1 else m2) ⦃ _ => True ⦄ := by
  split
  · exact h1
  · exact h2

theorem vcpu.copy_reg_range_to_frame_loop.fw (s0 : S) (vc f e : U64)
    (hf : ∀ m r : U64, m.val = r.val * 8 → r.val < 128 → core.num.U64.wrapping_add f m ∈ U)
    (hal : ∀ b ∈ U, Aligned b) (he : e.val < 128) (s : S) (r : U64) (w : WritesIn st s0 s (· ∈ U)) :
    vcpu.copy_reg_range_to_frame_loop st s vc f e r ⦃ s' => WritesIn st s0 s' (· ∈ U) ⦄ := by
  unfold vcpu.copy_reg_range_to_frame_loop
  apply loop.spec_decr_nat (measure := fun x : S × U64 => e.val + 1 - x.2.val)
    (inv := fun x : S × U64 => WritesIn st s0 x.1 (· ∈ U))
  · rintro ⟨s1, r1⟩ w1
    dsimp only at w1 ⊢
    unfold vcpu.copy_reg_range_to_frame_loop.body
    simp only [lift, bind_ok, L.write_eq]
    by_cases hr : r1 ≤ e
    · rw [if_pos hr]
      have hr' : r1.val ≤ e.val := hr
      step as ⟨i, hi⟩
      refine WP.spec_bind (P0.vcpu.reg_get.p0 st s1 vc r1 L.total) fun v _ => ?_
      try simp only [bind_ok]
      step as ⟨r2, hr2⟩
      try rw [WP.spec_ok]
      exact ⟨wrU hal w1 (hf _ _ hi (by omega)), by first | omega | (dsimp only; omega)⟩
    · rw [if_neg hr, WP.spec_ok]; exact w1
  · exact w

theorem vcpu.read_state_to_frame_loop0.fw (s0 : S) (vc f : U64) (g : Bool)
    (hf : ∀ m r : U64, m.val = r.val * 8 → r.val < 128 → core.num.U64.wrapping_add f m ∈ U)
    (hal : ∀ b ∈ U, Aligned b) (s : S) (r : U64) (w : WritesIn st s0 s (· ∈ U)) :
    vcpu.read_state_to_frame_loop0 st s vc f g r ⦃ s' => WritesIn st s0 s' (· ∈ U) ⦄ := by
  unfold vcpu.read_state_to_frame_loop0
  apply loop.spec_decr_nat (measure := fun x : S × U64 => 48 - x.2.val)
    (inv := fun x : S × U64 => WritesIn st s0 x.1 (· ∈ U))
  · rintro ⟨s1, r1⟩ w1
    dsimp only at w1 ⊢
    unfold vcpu.read_state_to_frame_loop0.body
    simp only [lift, bind_ok, L.write_eq, fl4_abi.consts.vcpu_reg.VGIC_AP1R3]
    by_cases hr : r1 ≤ 47#u64
    · rw [if_pos hr]
      have hr' : r1.val ≤ 47 := hr
      refine WP.spec_bind (ite_total (P0.vcpu.reg_get.p0 st s1 vc r1 L.total) ((WP.spec_ok _).2 trivial))
        fun v _ => ?_
      step as ⟨i, hi⟩
      try simp only [bind_ok]
      step as ⟨r2, hr2⟩
      try rw [WP.spec_ok]
      exact ⟨wrU hal w1 (hf _ _ hi (by omega)), by first | omega | (dsimp only; omega)⟩
    · rw [if_neg hr, WP.spec_ok]; exact w1
  · exact w

theorem vcpu.read_state_to_frame_loop1.fw (s0 : S) (vc f lrs : U64)
    (hf : ∀ m r : U64, m.val = r.val * 8 → r.val < 128 → core.num.U64.wrapping_add f m ∈ U)
    (hal : ∀ b ∈ U, Aligned b) (s : S) (r : U64) (w : WritesIn st s0 s (· ∈ U)) :
    vcpu.read_state_to_frame_loop1 st s vc f lrs r ⦃ s' => WritesIn st s0 s' (· ∈ U) ⦄ := by
  unfold vcpu.read_state_to_frame_loop1
  apply loop.spec_decr_nat (measure := fun x : S × U64 => 16 - x.2.val)
    (inv := fun x : S × U64 => WritesIn st s0 x.1 (· ∈ U))
  · rintro ⟨s1, r1⟩ w1
    dsimp only at w1 ⊢
    unfold vcpu.read_state_to_frame_loop1.body
    simp only [lift, bind_ok, L.write_eq, fl4_abi.consts.vcpu_reg.VGIC_LR0]
    by_cases hr : r1 < 16#u64
    · rw [if_pos hr]
      have hr' : r1.val < 16 := hr
      have hx : (core.num.U64.wrapping_add 48#u64 r1).val = 48 + r1.val := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      refine WP.spec_bind (ite_total (P0.vcpu.reg_get.p0 st s1 vc _ L.total) ((WP.spec_ok _).2 trivial))
        fun v _ => ?_
      step as ⟨i, hi⟩
      try simp only [bind_ok]
      step as ⟨r2, hr2⟩
      try rw [WP.spec_ok]
      exact ⟨wrU hal w1 (hf _ _ hi (by omega)), by first | omega | (dsimp only; omega)⟩
    · rw [if_neg hr, WP.spec_ok]; exact w1
  · exact w

theorem vcpu.read_state_to_frame_loop2.fw (s0 : S) (g tp : U64)
    (hg : ∀ m i : U64, m.val = i.val * 8 → i.val < 64 → core.num.U64.wrapping_add g m ∈ U)
    (hal : ∀ b ∈ U, Aligned b) (s : S) (r : U64) (w : WritesIn st s0 s (· ∈ U)) :
    vcpu.read_state_to_frame_loop2 st s g tp r ⦃ s' => WritesIn st s0 s' (· ∈ U) ⦄ := by
  unfold vcpu.read_state_to_frame_loop2
  apply loop.spec_decr_nat (measure := fun x : S × U64 => 37 - x.2.val)
    (inv := fun x : S × U64 => WritesIn st s0 x.1 (· ∈ U))
  · rintro ⟨s1, r1⟩ w1
    dsimp only at w1 ⊢
    unfold vcpu.read_state_to_frame_loop2.body
    simp only [lift, bind_ok, L.write_eq, layout.reg.COUNT]
    by_cases hr : r1 < 37#u64
    · rw [if_pos hr]
      have hr' : r1.val < 37 := hr
      refine WP.spec_bind (ite_total (P0.obj.Tcb.reg.p0 st tp s1 r1 L.total) ((WP.spec_ok _).2 trivial))
        fun v _ => ?_
      step as ⟨i, hi⟩
      try simp only [bind_ok]
      step as ⟨r2, hr2⟩
      try rw [WP.spec_ok]
      exact ⟨wrU hal w1 (hg _ _ hi (by omega)), by first | omega | (dsimp only; omega)⟩
    · rw [if_neg hr, WP.spec_ok]; exact w1
  · exact w

theorem loop3_eq (s : S) (vc f lrs r : U64) :
    vcpu.read_state_to_frame_loop3 st s vc f lrs r = vcpu.read_state_to_frame_loop1 st s vc f lrs r := by
  unfold vcpu.read_state_to_frame_loop3 vcpu.read_state_to_frame_loop1
  rfl

theorem loop4_eq (s : S) (g tp r : U64) :
    vcpu.read_state_to_frame_loop4 st s g tp r = vcpu.read_state_to_frame_loop2 st s g tp r := by
  unfold vcpu.read_state_to_frame_loop4 vcpu.read_state_to_frame_loop2
  rfl

theorem loop5_eq (s : S) (g tp r : U64) :
    vcpu.read_state_to_frame_loop5 st s g tp r = vcpu.read_state_to_frame_loop2 st s g tp r := by
  unfold vcpu.read_state_to_frame_loop5 vcpu.read_state_to_frame_loop2
  rfl

/-- **`read_state_to_frame` into a frame `f` with `FrU U f` writes `U` words only.** -/
theorem vcpu.read_state_to_frame.fw (hA : P0.ArchTotal ar) (s : S) (a : A) (vc f mask : U64)
    (hfr : FrU U f) (hal : ∀ b ∈ U, Aligned b) :
    vcpu.read_state_to_frame st ar s a vc f mask ⦃ s' => WritesIn st s s' (· ∈ U) ⦄ := by
  have W0 : WritesIn st s s (· ∈ U) := WritesIn.refl _ _
  have hf : ∀ m r : U64, m.val = r.val * 8 → r.val < 128 → core.num.U64.wrapping_add f m ∈ U :=
    fun m r hm hr => hfr.at hm hr
  have CP : ∀ (s1 : S) (lo hi : U64), hi.val < 128 → WritesIn st s s1 (· ∈ U) →
      vcpu.copy_reg_range_to_frame st s1 vc f lo hi ⦃ s' => WritesIn st s s' (· ∈ U) ⦄ :=
    fun s1 lo hi hh w => vcpu.copy_reg_range_to_frame_loop.fw s vc f hi hf hal hh s1 lo w
  have GP : ∀ (s1 : S) (c tp : U64), c.val = 512 → WritesIn st s s1 (· ∈ U) →
      vcpu.read_state_to_frame_loop2 st s1 (core.num.U64.wrapping_add f c) tp 0#u64
        ⦃ s' => WritesIn st s s' (· ∈ U) ⦄ :=
    fun s1 c tp hc w => vcpu.read_state_to_frame_loop2.fw s _ tp
      (fun m i hm hi => hfr.at2 rfl hc hm hi) hal s1 _ w
  unfold vcpu.read_state_to_frame
  rw [eq_of_spec_fd P0.Consts.fl4_abi.consts.vcpu_state_mask.EL1_SYSREGS.spec,
    eq_of_spec_fd P0.Consts.fl4_abi.consts.vcpu_state_mask.HYP.spec,
    eq_of_spec_fd P0.Consts.fl4_abi.consts.vcpu_state_mask.TIMER.spec,
    eq_of_spec_fd P0.Consts.fl4_abi.consts.vcpu_state_mask.VGIC.spec,
    eq_of_spec_fd P0.Consts.fl4_abi.consts.vcpu_state_mask.GPRS.spec,
    eq_of_spec_fd P0.Consts.fl4_abi.consts.vcpu_state_mask.VGIC_LR.spec]
  simp only [lift, bind_ok, L.read_eq, L.write_eq, loop3_eq, loop4_eq, loop5_eq,
    fl4_abi.consts.vcpu_reg.CSSELR_EL1, fl4_abi.consts.vcpu_reg.ACTLR_EL1, fl4_abi.consts.vcpu_reg.MDCCINT_EL1,
    fl4_abi.consts.vcpu_reg.VMPIDR_EL2, fl4_abi.consts.vcpu_reg.VDISR_EL2, fl4_abi.consts.vcpu_reg.VPIDR_EL2,
    fl4_abi.consts.vcpu_reg.VSESR_EL2, fl4_abi.consts.vcpu_reg.FAR_EL2, fl4_abi.consts.vcpu_reg.ESR_EL2,
    fl4_abi.consts.vcpu_reg.CNTV_CTL, fl4_abi.consts.vcpu_reg.CNTKCTL_EL1, fl4_abi.consts.vcpu_reg.VGIC_VTR,
    fl4_abi.consts.vcpu_reg.VGIC_HCR, fl4_abi.consts.vcpu_reg.VGIC_AP0R3, fl4_abi.consts.vcpu_reg.VGIC_AP1R0,
    fl4_abi.consts.vcpu_reg.VGIC_ELRSR]
  by_cases h0 : mask = 0#u64
  · rw [if_pos h0]; exact (WP.spec_ok _).2 W0
  rw [if_neg h0]
  -- EL1 system registers
  refine WP.spec_bind (Pₘ := fun s1 => WritesIn st s s1 (· ∈ U)) ?_ fun s1 w1 => ?_
  · split
    · exact WP.spec_bind (CP s _ _ (by simp) W0) fun s2 w2 => CP s2 _ _ (by simp) w2
    · exact (WP.spec_ok _).2 W0
  -- hypervisor registers
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s s2 (· ∈ U)) ?_ fun s2 w2 => ?_
  · split
    · step as ⟨i4, hi4⟩
      refine WP.spec_bind (P0.vcpu.reg_get.p0 st s1 vc _ L.total) fun i6 _ => ?_
      try simp only [bind_ok]
      step as ⟨i7, hi7⟩
      refine WP.spec_bind (P0.vcpu.reg_get.p0 st _ vc _ L.total) fun i9 _ => ?_
      try simp only [bind_ok]
      have w3 := wrU (v := i9) hal (wrU (v := i6) hal w1 (hf i4 15#u64 (by simp [hi4]) (by simp))) (hf i7 20#u64 (by simp [hi7]) (by simp))
      exact WP.spec_bind (CP _ _ _ (by simp) w3) fun s5 w5 => CP s5 _ _ (by simp) w5
    · exact (WP.spec_ok _).2 w1
  -- timer
  refine WP.spec_bind (Pₘ := fun s3 => WritesIn st s s3 (· ∈ U)) ?_ fun s3 w3 => ?_
  · split
    · refine WP.spec_bind (CP s2 _ _ (by simp) w2) fun s4 w4 => ?_
      step as ⟨i6, hi6⟩
      step as ⟨i7, hi7⟩
      exact wrU hal w4 (hf _ _ hi7 (by scalar_tac))
    · exact (WP.spec_ok _).2 w2
  -- VGIC
  split
  · refine WP.spec_bind (P0.vcpu.num_lrs.p0 ar a hA) fun lrs _ => ?_
    refine WP.spec_bind (hA.vcpu_gic_version a) fun i8 _ => ?_
    step as ⟨i9, hi9⟩
    refine WP.spec_bind (hA.vcpu_vgic_vtr a) fun i11 _ => ?_
    refine WP.spec_bind (P0.vcpu.abi_vgic_vtr.p0 _ _) fun i12 _ => ?_
    try simp only [bind_ok]
    have w4 := wrU (v := i12) hal w3 (hf i9 34#u64 (by simp [hi9]) (by simp))
    refine WP.spec_bind (CP _ _ _ (by simp) w4) fun s5 w5 => ?_
    refine WP.spec_bind (vcpu.read_state_to_frame_loop0.fw s vc f _ hf hal s5 _ w5) fun s6 w6 => ?_
    refine WP.spec_bind (vcpu.read_state_to_frame_loop1.fw s vc f lrs hf hal s6 _ w6) fun s7 w7 => ?_
    split
    · step as ⟨i15, hi15⟩
      exact GP s7 i15 _ (by scalar_tac) w7
    · exact (WP.spec_ok _).2 w7
  · split
    · refine WP.spec_bind (P0.vcpu.num_lrs.p0 ar a hA) fun lrs _ => ?_
      step as ⟨i10, hi10⟩
      refine WP.spec_bind (P0.vcpu.reg_get.p0 st s3 vc _ L.total) fun i12 _ => ?_
      try simp only [bind_ok]
      step as ⟨i13, hi13⟩
      refine WP.spec_bind (P0.vcpu.reg_get.p0 st _ vc _ L.total) fun i15 _ => ?_
      try simp only [bind_ok]
      have w5 := wrU (v := i15) hal (wrU (v := i12) hal w3 (hf i10 35#u64 (by simp [hi10]) (by simp))) (hf i13 39#u64 (by simp [hi13]) (by simp))
      refine WP.spec_bind (vcpu.read_state_to_frame_loop1.fw s vc f lrs hf hal _ _ w5) fun s6 w6 => ?_
      split
      · step as ⟨i18, hi18⟩
        exact GP s6 i18 _ (by scalar_tac) w6
      · exact (WP.spec_ok _).2 w6
    · split
      · step as ⟨i12, hi12⟩
        exact GP s3 i12 _ (by scalar_tac) w3
      · exact (WP.spec_ok _).2 w3

/-! ## `complete_run` -/

/-- The address of a VCPU's `RUN_OFFSET` word. -/
def runOffA (v : U64) : U64 := core.num.U64.wrapping_add v vcpu.RUN_OFFSET

/-- **[P] (A64 `hbuf`) The run frame of `y` lies in the user words `U`**: when `y`'s IPC-buffer slot holds
a writable non-device frame cap and its run VCPU's `RUN_OFFSET` passes `complete_run`'s checks (64-aligned,
inside the frame, 1024 bytes to its end), the 128 words from frame + offset are in `U`. -/
def RunBuf (st : machine.Store S) [L : LawfulStore st] (U : Set U64) (s : S) (y : U64) : Prop :=
  ∀ (ptr : U64) (size : capability.FrameSize) (rights : U64) (dev x1 x2 : Bool) (x3 x4 bits sz : U64),
    obj.Slot.cap st (sbWordA y) s = ok (capability.Cap.Frame ptr size rights dev x1 x2 x3 x4) →
    dev = false → rights = capability.VM_READ_WRITE →
    capability.FrameSize.bits size = ok bits → (1#u64 <<< (bits &&& 63#u64) : Result U64) = ok sz →
    (L.mem s (runOffA (L.mem s (runVcpuA y))) &&& 63#u64) = 0#u64 →
    (L.mem s (runOffA (L.mem s (runVcpuA y)))).val < sz.val →
    1024 ≤ sz.val - (L.mem s (runOffA (L.mem s (runVcpuA y)))).val →
    FrU U (core.num.U64.wrapping_add ptr (L.mem s (runOffA (L.mem s (runVcpuA y)))))

/-- `RunBuf` along a step that keeps the slot's cap, the `RUN_VCPU` word and the `RUN_OFFSET` word. -/
theorem RunBuf.of_eq {s s1 : S} {y : U64} (h : RunBuf st U s y)
    (hc : obj.Slot.cap st (sbWordA y) s1 = obj.Slot.cap st (sbWordA y) s)
    (hv : L.mem s1 (runVcpuA y) = L.mem s (runVcpuA y))
    (ho : L.mem s1 (runOffA (L.mem s (runVcpuA y))) = L.mem s (runOffA (L.mem s (runVcpuA y)))) :
    RunBuf st U s1 y := by
  intro ptr size rights dev x1 x2 x3 x4 bits sz e1 e2 e3 e4 e5
  rw [hv, ho]
  exact h ptr size rights dev x1 x2 x3 x4 bits sz (hc ▸ e1) e2 e3 e4 e5

/-- The register words of `y`. -/
def RegW (y b : U64) : Prop :=
  ∃ K : U64, 256 ≤ K.val ∧ K.val < 3328 ∧ K.val % 8 = 0 ∧ b = core.num.U64.wrapping_add y K

theorem obj.Tcb.set_reg.regW {s0 : S} (s : S) {y r v : U64} (hta : TcbAddr y) (hr : r.val < 384)
    (w : WritesIn st s0 s (RegW y)) : obj.Tcb.set_reg st y s r v ⦃ s' => WritesIn st s0 s' (RegW y) ⦄ := by
  refine WP.spec_mono (obj.Tcb.set_reg.wrS s y r v hta hr) fun s' ⟨K, hK, e⟩ => ?_
  subst e
  exact (w.trans (writesIn_wr (field_aligned hta (by omega) (by omega)))).mono fun b hb =>
    hb.elim id fun e => ⟨K, by omega, by omega, by omega, e⟩

theorem msg_register_lt (i : U64) : msg.msg_register i ⦃ r => r.val < 384 ⦄ := by
  unfold msg.msg_register
  split
  · exact (WP.spec_ok _).2 (by simp [layout.reg.X2])
  split
  · exact (WP.spec_ok _).2 (by simp [layout.reg.X3])
  split
  · exact (WP.spec_ok _).2 (by simp [layout.reg.X4])
  · exact (WP.spec_ok _).2 (by simp [layout.reg.X5])

/-- The register writes of `complete_run` (`BADGE`, X2..X5, message info, `FAULT_IP`). -/
theorem vck_regs (s : S) (y stop w1 w2 w3 : U64) (hta : TcbAddr y) {P : S → Result (S × A)}
    {Q : S × A → Prop} (hP : ∀ s', WritesIn st s s' (RegW y) → P s' ⦃ Q ⦄) :
    (do
      let s4 ← obj.Tcb.set_reg st y s layout.reg.BADGE 0#u64
      let i6 ← msg.msg_register 0#u64
      let s5 ← obj.Tcb.set_reg st y s4 i6 stop
      let i7 ← msg.msg_register 1#u64
      let s6 ← obj.Tcb.set_reg st y s5 i7 w1
      let i8 ← msg.msg_register 2#u64
      let s7 ← obj.Tcb.set_reg st y s6 i8 w2
      let i9 ← msg.msg_register 3#u64
      let s8 ← obj.Tcb.set_reg st y s7 i9 w3
      let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 4#u64
      let s9 ← msg.set_msg_info st s8 y mi
      let ip ← obj.Tcb.reg st y s9 layout.reg.NEXT_IP
      let s10 ← obj.Tcb.set_reg st y s9 layout.reg.FAULT_IP ip
      P s10) ⦃ Q ⦄ := by
  have W0 : WritesIn st s s (RegW y) := WritesIn.refl _ _
  refine WP.spec_bind (obj.Tcb.set_reg.regW s hta (by simp [layout.reg.BADGE, layout.reg.X0]) W0)
    fun s4 w4 => ?_
  refine WP.spec_bind (msg_register_lt _) fun i6 h6 => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.regW s4 hta h6 w4) fun s5 w5 => ?_
  refine WP.spec_bind (msg_register_lt _) fun i7 h7 => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.regW s5 hta h7 w5) fun s6 w6 => ?_
  refine WP.spec_bind (msg_register_lt _) fun i8 h8 => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.regW s6 hta h8 w6) fun s7 w7 => ?_
  refine WP.spec_bind (msg_register_lt _) fun i9 h9 => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.regW s7 hta h9 w7) fun s8 w8 => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
  refine WP.spec_bind (Pₘ := fun s9 => WritesIn st s s9 (RegW y)) ?_ fun s9 w9 => ?_
  · unfold msg.set_msg_info
    refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 mi) fun i _ => ?_
    exact obj.Tcb.set_reg.regW s8 hta (by simp [layout.reg.MSG_INFO, layout.reg.X1]) w8
  refine WP.spec_bind (P0.obj.Tcb.reg.p0 st y s9 _ L.total) fun ip _ => ?_
  exact WP.spec_bind (obj.Tcb.set_reg.regW s9 hta (by simp [layout.reg.FAULT_IP]) w9) hP

/-- **`complete_run` of the current thread, in `TS_RUNNING_VM`, keeps `EntryInv`**, as a `VckW` step.
Named premises `hbuf` [P] (`RunBuf`: its run frame in `U`) and `hpw` [P] (its run VCPU's `RUN_CALLER` word
in `U`). -/
theorem vcpu.complete_run.vck (hA : P0.ArchTotal ar) (s : S) (a : A) (y stop m1 m2 m3 : U64)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y = L.curW s)
    (hvm : L.mem s (stA y) = sched.TS_RUNNING_VM)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hbuf : RunBuf st U s y)
    (hpw : L.mem s (runVcpuA y) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (runVcpuA y)) vcpu.RUN_CALLER ∈ U) :
    vcpu.complete_run st ar s a y stop m1 m2 m3 ⦃ s' _ => VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac y s s' ⦄ := by
  have hb := EntryInv.vckBlk h
  obtain ⟨⟨Q, R, hq⟩, -, hX, -, -⟩ := hb
  have hT := hq.tcbs
  have hyT : y ∈ T := by rw [hy]; exact hq.curT
  have hta := hT y hyT
  have hN := hq.nodes _ hq.cur
  have hal : ∀ b ∈ U, Aligned b := fun b hb => (hU b hb).out.1
  unfold vcpu.complete_run
  rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec]
  simp only [lift, bind_ok, L.read_eq, L.write_eq]
  by_cases hv0 : L.mem s (core.num.U64.wrapping_add y 3672#u64) = 0#u64
  · rw [if_pos hv0]; exact (WP.spec_ok _).2 (VckPost.refl h)
  rw [if_neg hv0]
  refine WP.spec_bind (hA.vcpu_flush_state _ _ _) fun a1 _ => ?_
  -- the copy into the run frame: `U` words
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s s2 (· ∈ U)) ?_ fun s2 w2 => ?_
  · split
    · have hs : obj.Tcb.slot y layout.tcb.SLOT_BUFFER = ok (sbWordA y) := by
        simp [obj.Tcb.slot, lift, sbWordA]
      rw [hs, bind_ok]
      refine WP.spec_bind (spec_eq' (P0.obj.Slot.cap.p0 st (sbWordA y) s L.total)) fun c hc0 => ?_
      obtain ⟨hc, -⟩ := hc0
      cases c
      all_goals try exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      rename_i ptr size rights dev c1 c2 c3 c4
      refine WP.spec_bind (spec_eq' (P0.capability.FrameSize.bits.p0 size)) fun bits ⟨hbits, _⟩ => ?_
      have h63 : (bits &&& 63#u64).val < 64 := by
        rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by simp)
      refine WP.spec_bind (spec_eq' (P0.one_shift_positive _ h63)) fun sz ⟨hsz, _⟩ => ?_
      by_cases hd : dev = true
      · rw [if_pos hd]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      rw [if_neg hd]
      split
      · rename_i hrw
        split
        · rename_i ho
          split
          · rename_i hlt
            have hlt' : (L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add y 3672#u64))
                vcpu.RUN_OFFSET)).val < sz.val := hlt
            step as ⟨i7, hi7⟩
            split
            · rename_i hge
              have hge' : 1024 ≤ i7.val := by scalar_tac
              have hF := hbuf ptr size rights dev c1 c2 c3 c4 bits sz hc (by simpa using hd) hrw hbits hsz
                ho hlt' (by unfold runOffA runVcpuA; omega)
              exact vcpu.read_state_to_frame.fw hA s a1 _ _ _ hF hal
            · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
          · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
        · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  -- `RUN_CALLER` (a `U` word), then `RUN_VCPU`
  have hrc : core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add y 3672#u64)) vcpu.RUN_CALLER ∈ U :=
    hpw hv0
  have w3' := wrU (v := 0#u64) hal w2 hrc
  set s3 := L.wr s2 (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add y 3672#u64)) vcpu.RUN_CALLER)
    0#u64 with hs3
  obtain ⟨h3, f3⟩ := bufw_xfer (EntryInv.vckBlk h) hU (w3'.mono fun b hb => (Or.inr hb : XferFoot T U b))
  have st3 : L.mem s3 (stA y) = sched.TS_RUNNING_VM := by
    rw [stA_eq, f3 y hyT _ (by simp) (by simp) (by simp), ← stA_eq]; exact hvm
  obtain ⟨h4, st4⟩ := rv_all (K := 3672#u64) (v := 0#u64) h3 hyT (by simp)
  set s4 := L.wr s3 (core.num.U64.wrapping_add y 3672#u64) 0#u64 with hs4
  have a4 : Aligned (core.num.U64.wrapping_add y 3672#u64) := field_aligned hta (by simp) (by simp)
  have rv4 : L.mem s4 (runVcpuA y) = 0#u64 := L.mem_wr_same a4
  have k4 : L.ksb s4 = L.ksb s := by rw [hs4, L.ksb_wr]; exact w3'.1
  have hU4 : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s4 b := fun b hb => (hU b hb).ksb k4
  have w4 : WritesIn st s s4 (fun b => b ∈ U ∨ b = runVcpuA y) :=
    (w3'.trans (writesIn_wr a4)).mono fun b hb => hb.elim Or.inl Or.inr
  refine vck_regs s4 y stop m1 m2 m3 hta fun s10 w10 => ?_
  obtain ⟨h10, f10⟩ := bufw_xfer h4 hU4 (w10.mono fun b ⟨K, h1, h2, h3, e⟩ =>
    (Or.inl ⟨y, hyT, K, h2, h3, e⟩ : XferFoot T U b))
  have st10 : L.mem s10 (stA y) = sched.TS_RUNNING_VM := by
    rw [stA_eq, f10 y hyT _ (by simp) (by simp) (by simp), ← stA_eq, st4]; exact st3
  have rv10 : L.mem s10 (runVcpuA y) = 0#u64 := by
    rw [show runVcpuA y = core.num.U64.wrapping_add y 3672#u64 from rfl,
      f10 y hyT _ (by simp) (by simp) (by simp)]; exact rv4
  have wA : WritesIn st s s10 (fun b => (b ∈ U ∨ b = runVcpuA y) ∨ RegW y b) := w4.trans w10
  have wV : WritesIn st s s10 (VckW st T Cs Scs y s) := wA.mono fun b hb => by
    rcases hb with (hu | e) | ⟨K, h1, h2, h3, e⟩
    · exact Or.inl (usr_vckR hU hX.1 hu)
    · exact Or.inr (Or.inr (Or.inr e))
    · exact Or.inl (Or.inr ⟨K, h1, h2, h3, e⟩)
  have ea : L.actionW s10 = L.actionW s := vck_actionW_of wA hN (by
    rintro ((hu | e) | ⟨K, -, hK, -, e⟩)
    · exact out_ne_node (hU _ hu).out hq.cur hN (by rw [act_val]; omega) rfl
    · exact node_ne_field (K := 3672#u64) hN (by rw [act_val]; omega) hyT hta (by simp) e
    · exact node_ne_field hN (by rw [act_val]; omega) hyT hta (by omega) e)
  exact WP.spec_bind (vck_fin h hy hvm h10 st10 wV ea rv10) fun s11 h11 => vck_vm_tail hA s11 a1 y h11

/-! ## `vcpu::check` -/

/-- **`vcpu::check` of the current thread keeps `EntryInv`, as a `VckW` step** (module docstring).
Named premises `hbuf` [P] (`RunBuf`) and `hpw` [P] (the run VCPU's `RUN_CALLER` word in `U`). -/
theorem vcpu.check.vck (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : RunBuf st U s (L.curW s))
    (hpw : L.mem s (runVcpuA (L.curW s)) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (runVcpuA (L.curW s))) vcpu.RUN_CALLER ∈ U) :
    vcpu.check st ar s a (L.curW s) ⦃ s' _ => VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac (L.curW s) s s' ⦄ := by
  obtain ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ := (EntryInv.vckBlk h)
  have hT := hq.tcbs
  have hcT : L.curW s ∈ T := hq.curT
  have hta := hT _ hcT
  have hN := hq.nodes _ hq.cur
  have OK0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac (L.curW s) s s' ⦄ :=
    (WP.spec_ok _).2 (VckPost.refl h)
  unfold vcpu.check
  step with obj.Tcb.state.spec as ⟨i, ei⟩
  split
  · exact OK0
  rename_i hvm0
  have hvm : L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM := by
    rw [← ei]; by_contra hne; exact hvm0 (bne_iff_ne.mpr hne)
  rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec]
  simp only [lift, bind_ok, L.read_eq]
  by_cases hv0 : L.mem s (core.num.U64.wrapping_add (L.curW s) 3672#u64) = 0#u64
  · -- no run in flight: `FAULT_IP := NEXT_IP`, then `RUNNING`
    rw [if_pos hv0]
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st _ s _ L.total) fun ip _ => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.wrS s _ layout.reg.FAULT_IP ip hta (by simp [layout.reg.FAULT_IP]))
      fun s1 ⟨K, hK, e1⟩ => ?_
    subst e1
    have hK' : 256 ≤ K.val ∧ K.val < 3328 := by simp [layout.reg.FAULT_IP] at hK; omega
    have hK8 : K.val % 8 = 0 := by simp [layout.reg.FAULT_IP] at hK; omega
    obtain ⟨h1, st1⟩ := reg_all (v := ip) hq hB hX hS hSg hcT hK' hK8
    have aK := field_aligned hta (by omega) hK8
    have w1 : WritesIn st s (L.wr s (core.num.U64.wrapping_add (L.curW s) K) ip)
        (VckW st T Cs Scs (L.curW s) s) :=
      (writesIn_wr aK).mono fun b e => Or.inl (Or.inr ⟨K, hK'.1, hK'.2, hK8, e⟩)
    have ea : L.actionW (L.wr s (core.num.U64.wrapping_add (L.curW s) K) ip) = L.actionW s :=
      vck_actionW_of (writesIn_wr aK) hN (fun e => node_ne_field hN (by rw [act_val]; omega) hcT hta (by omega) e)
    have rv1 : L.mem (L.wr s (core.num.U64.wrapping_add (L.curW s) K) ip) (runVcpuA (L.curW s)) = 0#u64 := by
      rw [show runVcpuA (L.curW s) = core.num.U64.wrapping_add (L.curW s) 3672#u64 from rfl, L.mem_wr_ne aK (field_aligned (K := 3672#u64) hta (by simp) (by simp))
        (fun e => field_ne (K1 := K) (K2 := 3672#u64) hta hta (by omega) (by simp)
          (fun _ => by first | omega | (simp; omega) | simp) (UScalar.eq_of_val_eq e))]
      exact hv0
    exact WP.spec_bind (vck_fin h rfl hvm h1 (st1.trans hvm) w1 ea rv1) fun s2 h2 => (WP.spec_ok _).2 h2
  rw [if_neg hv0]
  -- the bound notification's badge completes the run
  have NT : ∀ n : U64, n = L.mem s (boundA (L.curW s)) → n ≠ 0#u64 → L.epState s n = obj.NTFN_ACTIVE →
      (do
        let badge ← obj.Ntfn.badge st n s
        let s1 ← obj.Ntfn.set_state st n s obj.NTFN_IDLE
        vcpu.complete_run st ar s1 a (L.curW s) fl4_abi.consts.vcpu_run_stop.INTERRUPT badge 0#u64 0#u64)
        ⦃ s' _ => VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac (L.curW s) s s' ⦄ := by
    intro n en hn0 hact
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
        rw [scA_eq]; exact fld1 z hz _ (by simp) (by simp) (fun _ => Or.inr ⟨by simp, by simp⟩)
    have st1 : L.mem s1 (stA (L.curW s)) = sched.TS_RUNNING_VM := by
      rw [stA_eq, f2 _ hcT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hvm
    have ev1 : L.mem s1 (runVcpuA (L.curW s)) = L.mem s (runVcpuA (L.curW s)) :=
      f2 _ hcT _ (by simp) (by simp) (by simp) (by simp)
    have C1 : VckPost st T Cs Ω H Sg Rp Scs Nt Z Ac (L.curW s) s s1 := by
      refine ⟨h1, w1, Or.inl ea2, Or.inl (by rw [st1, hvm]), fun hRV z hz h0 => ?_⟩
      have es : L.mem s1 (stA z) = L.mem s (stA z) := by
        rw [stA_eq]; exact f2 z hz _ (by simp) (by simp) (by simp) (by simp)
      have er : L.mem s1 (runVcpuA z) = L.mem s (runVcpuA z) := f2 z hz _ (by simp) (by simp) (by simp) (by simp)
      rw [es]; exact hRV z hz (by rw [← er]; exact h0)
    have hU1 : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s1 b := fun b hb => (hU b hb).ksb w1.1
    -- the run VCPU's `RUN_CALLER` word is a user word, so its `RUN_OFFSET` word is not the notification's
    have hrc := hpw hv0
    have hu := hU _ hrc
    have hne := hu.eps n (Or.inr hnH)
    have hal8 := hu.out.1
    set vc := L.mem s (runVcpuA (L.curW s)) with hvc
    have v24 : (core.num.U64.wrapping_add vc vcpu.RUN_CALLER).val = (vc.val + 24) % 2 ^ 64 := by
      simp [core.num.U64.wrapping_add_val_eq, vcpu.RUN_CALLER, U64.size_def, U64.numBits]
    have v32 : (runOffA vc).val = (vc.val + 32) % 2 ^ 64 := by
      simp [runOffA, core.num.U64.wrapping_add_val_eq, vcpu.RUN_OFFSET, U64.size_def, U64.numBits]
    have aO : Aligned (runOffA vc) := by
      unfold Aligned at hal8 ⊢; rw [v32]; rw [v24] at hal8; omega
    have eo : L.mem s1 (runOffA vc) = L.mem s (runOffA vc) := by
      rw [hs1]
      refine L.mem_wr_ne a2 aO ?_
      rw [hTS, v32]; rw [v24] at hne; omega
    have hbuf1 : RunBuf st U s1 (L.curW s) := by
      refine RunBuf.of_eq hbuf ?_ ev1 (by rw [← hvc]; exact eo)
      unfold obj.Slot.cap
      rw [L.read_pair_eq, L.read_pair_eq, sbWordA8_eq, sbWordA_eq,
        f2 _ hcT _ (by simp) (by simp) (by simp) (by simp), f2 _ hcT _ (by simp) (by simp) (by simp) (by simp)]
    have hpw1 : L.mem s1 (runVcpuA (L.curW s)) ≠ 0#u64 →
        core.num.U64.wrapping_add (L.mem s1 (runVcpuA (L.curW s))) vcpu.RUN_CALLER ∈ U := fun _ => by
      rw [ev1]; exact hrc
    exact WP.spec_mono (vcpu.complete_run.vck hA s1 a _ _ _ _ _ h1 eC1.symm st1 hU1 hbuf1 hpw1)
      fun r hr => by
        obtain ⟨s', a'⟩ := r
        simp only [WP.uncurry'_pair] at hr ⊢
        exact C1.trans hr
  refine WP.spec_bind (obj.Tcb.bound_ntfn.val s _) fun i2 ei2 => ?_
  split
  · rename_i hi2
    refine WP.spec_bind (obj.Ntfn.state.spec s i2) fun i3 ei3 => ?_
    split
    · rename_i hi3
      exact NT i2 ei2 (by simpa using hi2) (by rw [← ei3]; exact hi3)
    · exact OK0
  · exact OK0

/-- **(P1) `vcpu::check` of the current thread keeps `EntryInv`** (what `EntryHyps0` / `P3Place` assume as
`vmchk` on x86_64). Named premises `hbuf` [P] (`RunBuf`: the thread's run frame in `U`) and `hpw` [P] (its run
VCPU's `RUN_CALLER` word in `U`). -/
theorem vcpu.check.entry (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : RunBuf st U s (L.curW s))
    (hpw : L.mem s (runVcpuA (L.curW s)) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (runVcpuA (L.curW s))) vcpu.RUN_CALLER ∈ U) :
    vcpu.check st ar s a (L.curW s) ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  refine WP.spec_mono (vcpu.check.vck hA hNt s a h hU hbuf hpw) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  exact hh.1

/-- **`vcpu::check` keeps [J] `RunVcpuInv`** (proved, not assumed): off `TS_RUNNING_VM` it does nothing; on
it the thread becomes `RUNNING` with its `RUN_VCPU` word 0 (cleared by `complete_run`, or 0 already), and no
other thread's `STATE` / `RUN_VCPU` word is written. Same placement premises as `vcpu.check.entry`. -/
theorem vcpu.check.rv (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : RunBuf st U s (L.curW s))
    (hpw : L.mem s (runVcpuA (L.curW s)) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (runVcpuA (L.curW s))) vcpu.RUN_CALLER ∈ U)
    (hRV : RunVcpuInv st T s) :
    vcpu.check st ar s a (L.curW s) ⦃ s' _ => RunVcpuInv st T s' ⦄ := by
  refine WP.spec_mono (vcpu.check.vck hA hNt s a h hU hbuf hpw) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  exact hh.2.2.2.2 hRV

end

end Fl4ProofsA64.P1
