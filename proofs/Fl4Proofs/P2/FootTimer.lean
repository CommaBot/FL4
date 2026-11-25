/-
# P2 (2): the write footprints of the local timer paths (DESIGN.md §7, §9 P2)

`localtimer.handle_set_timer_local` (`TCB_SetTimer` beside the serial gate) and
`localtimer.handle_timer_irq_local` (the kernel timer interrupt beside it).
DESIGN.md §7 "What a local path may write, its footprint", made concrete over the
entry state `s0` and its core `c = L.cpu s0` (`FootLt T Scs Z Lk s0`):

* `FootLtNode`: the words of core `c`'s node;
* `FootLtThr`: the words past the cap slots (offset 192 up) of the threads `y ∈ T`
  with `affinity` `c` at `s0`, except their queue links (`EP_NEXT`, `EP_PREV`) while
  blocked on an endpoint or notification (`FootLtBlk`) and their timer fields
  (`TIMER_DEADLINE ..= TIMER_HEIGHT`) while armed in another core's tree (DESIGN:
  "Not in it, of a thread on this core");
* `FootLtSc`: the scheduling contexts `x ∈ Scs` (`Z x` bits) with `CORE` `c`;
* `FootLtTmr`: the timer links `TIMER_LEFT ..= TIMER_HEIGHT` of the threads armed in
  core `c`'s tree (`FootLtArmed`: deadline nonzero, `TIMER_HEIGHT >> 8 = c`; by
  `TimerRB` exactly the keys of `c`'s tree), which may be other cores' threads;
* `FootLtLk Lk`: the locked objects `Lk` (address, bytes) and the queue links of the
  threads blocked on one of them.

No cap slot is in it (a TCB's slots lie below offset 192, CNode slots in CNodes), and
`TCB_SetTimer`'s `Lk` is empty: the slots its lookup locks are read, never written.
The paths write no IPC buffer word (`reply_success_empty` writes registers only), so
the footprint names none. The timer interrupt's end (`ack_irq`) is an `Arch` effect,
not a store word.

This module: the footprint, its combinators, and the **decline** cases of both paths
(`set_timer_decline_foot`, `irq_decline_foot`): a declined run writes only the
caller's `FAULT_IP` and the core's `CUR_TIME` / `CONSUMED`.

No named premises.
-/
import Fl4Proofs.P1.LocalTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-! ## The footprint -/

/-- `y` is blocked on an endpoint or a notification at `s0` (its queue links belong
to that object's queue). -/
def FootLtBlk (st : machine.Store S) [L : LawfulStore st] (s0 : S) (y : U64) : Prop :=
  L.mem s0 (stA y) = sched.TS_BLOCKED_ON_SEND ∨ L.mem s0 (stA y) = sched.TS_BLOCKED_ON_RECV ∨
    L.mem s0 (stA y) = sched.TS_BLOCKED_ON_NTFN

/-- `y` is armed in core `c`'s timer tree at `s0` (`core_of`). -/
def FootLtArmed (st : machine.Store S) [L : LawfulStore st] (s0 : S) (c y : U64) : Prop :=
  L.mem s0 (tdA y) ≠ 0#u64 ∧ (L.mem s0 (thA y)).val >>> 8 = c.val

/-- Core `c`'s node words. -/
def FootLtNode (st : machine.Store S) [L : LawfulStore st] (s0 : S) (c w : U64) : Prop :=
  ∃ o : U64, o.val < 4288 ∧ w = L.nodeAt s0 c o

/-- The words of core `c`'s threads (`affinity` `c` at `s0`) past their cap slots,
but the queue links of a blocked one and the timer fields of one armed in another
core's tree. -/
def FootLtThr (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c w : U64) : Prop :=
  ∃ y ∈ T, L.mem s0 (affA y) = c ∧ ∃ K : U64, 192 ≤ K.val ∧ K.val < 4096 ∧
    w = core.num.U64.wrapping_add y K ∧
    ((K.val = 3496 ∨ K.val = 3504) → ¬ FootLtBlk st s0 y) ∧
    ((3528 ≤ K.val ∧ K.val < 3576) → L.mem s0 (tdA y) = 0#u64 ∨ FootLtArmed st s0 c y)

/-- The words of core `c`'s scheduling contexts (`CORE` `c` at `s0`). -/
def FootLtSc (st : machine.Store S) [L : LawfulStore st] (Scs : Set U64) (Z : U64 → Nat) (s0 : S) (c w : U64) :
    Prop :=
  ∃ x ∈ Scs, L.mem s0 (scCoreA x) = c ∧ InSC x (Z x) w

/-- The timer links (`TIMER_LEFT ..= TIMER_HEIGHT`) of the threads armed in core
`c`'s tree. -/
def FootLtTmr (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c w : U64) : Prop :=
  ∃ y ∈ T, FootLtArmed st s0 c y ∧ ∃ K : U64, 3544 ≤ K.val ∧ K.val < 3576 ∧ w = core.num.U64.wrapping_add y K

/-- The locked objects `Lk` (address, bytes) and the queue links of the threads
blocked on one of them. -/
def FootLtLk (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (Lk : List (U64 × Nat)) (s0 : S) (w : U64) :
    Prop :=
  (∃ p ∈ Lk, p.1.val ≤ w.val ∧ w.val < p.1.val + p.2) ∨
    ∃ y ∈ T, FootLtBlk st s0 y ∧ (∃ p ∈ Lk, L.mem s0 (blockA y) = p.1) ∧
      (w = nextA .Ep y ∨ w = prevA .Ep y)

/-- **The footprint of a local timer path from `s0`** (DESIGN.md §7). -/
def FootLt (st : machine.Store S) [L : LawfulStore st] (T Scs : Set U64) (Z : U64 → Nat) (Lk : List (U64 × Nat))
    (s0 : S) (w : U64) : Prop :=
  FootLtNode st s0 (L.cpu s0) w ∨ FootLtThr st T s0 (L.cpu s0) w ∨ FootLtSc st Scs Z s0 (L.cpu s0) w ∨
    FootLtTmr st T s0 (L.cpu s0) w ∨ FootLtLk st T Lk s0 w

/-- The objects a timer-interrupt plan locks: its notification (64 bytes), endpoint
(16) and reply object (32), those nonzero. -/
def planLk (p : localtimer.TimerIrqPlan) : List (U64 × Nat) :=
  (if p.ntfn = 0#u64 then [] else [(p.ntfn, 64)]) ++ (if p.ep = 0#u64 then [] else [(p.ep, 16)]) ++
    (if p.reply = 0#u64 then [] else [(p.reply, 32)])

/-- A run from `s0` to `s` writes only the footprint. -/
abbrev InFootLt (st : machine.Store S) [L : LawfulStore st] (T Scs : Set U64) (Z : U64 → Nat)
    (Lk : List (U64 × Nat)) (s0 s : S) : Prop :=
  WritesIn st s0 s (FootLt st T Scs Z Lk s0)

/-- The shape the unified P2 statement takes: every aligned word outside the
footprint reads the same. -/
theorem InFootLt.unchanged {T Scs : Set U64} {Z : U64 → Nat} {Lk : List (U64 × Nat)} {s0 s : S}
    (h : InFootLt st T Scs Z Lk s0 s) : ∀ w, Aligned w → ¬ FootLt st T Scs Z Lk s0 w → L.mem s w = L.mem s0 w :=
  fun w hw hn => h.2.2 w hw hn

/-! ## Footprint words -/

variable {T Scs : Set U64} {Z : U64 → Nat} {Lk : List (U64 × Nat)}

theorem footLt_node {s0 : S} {o : U64} (ho : o.val < 4288) :
    FootLt st T Scs Z Lk s0 (L.nodeAt s0 (L.cpu s0) o) := Or.inl ⟨o, ho, rfl⟩

theorem footLt_thr {s0 : S} {y K : U64} (hy : y ∈ T) (ha : L.mem s0 (affA y) = L.cpu s0) (hK : 192 ≤ K.val)
    (hK' : K.val < 4096) (hE : K.val ≠ 3496 ∧ K.val ≠ 3504) (hTm : K.val < 3528 ∨ 3576 ≤ K.val) :
    FootLt st T Scs Z Lk s0 (core.num.U64.wrapping_add y K) :=
  Or.inr (Or.inl ⟨y, hy, ha, K, hK, hK', rfl, fun h => by omega, fun h => by omega⟩)

/-- A timer field of a thread of this core that is disarmed or armed in this core's
tree. -/
theorem footLt_thr_tmr {s0 : S} {y K : U64} (hy : y ∈ T) (ha : L.mem s0 (affA y) = L.cpu s0)
    (hK : 3528 ≤ K.val) (hK' : K.val < 3576) (hd : L.mem s0 (tdA y) = 0#u64 ∨ FootLtArmed st s0 (L.cpu s0) y) :
    FootLt st T Scs Z Lk s0 (core.num.U64.wrapping_add y K) :=
  Or.inr (Or.inl ⟨y, hy, ha, K, by omega, by omega, rfl, fun h => by omega, fun _ => hd⟩)

theorem footLt_tmr {s0 : S} {y K : U64} (hy : y ∈ T) (ha : FootLtArmed st s0 (L.cpu s0) y) (hK : 3544 ≤ K.val)
    (hK' : K.val < 3576) : FootLt st T Scs Z Lk s0 (core.num.U64.wrapping_add y K) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨y, hy, ha, K, hK, hK', rfl⟩)))

theorem footLt_sc {s0 : S} {x w : U64} (hx : x ∈ Scs) (hc : L.mem s0 (scCoreA x) = L.cpu s0) (hw : InSC x (Z x) w) :
    FootLt st T Scs Z Lk s0 w :=
  Or.inr (Or.inr (Or.inl ⟨x, hx, hc, hw⟩))

theorem footLt_lk {s0 : S} {p : U64 × Nat} {w : U64} (hp : p ∈ Lk) (h1 : p.1.val ≤ w.val) (h2 : w.val < p.1.val + p.2) :
    FootLt st T Scs Z Lk s0 w :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, h1, h2⟩))))

theorem footLt_epl {s0 : S} {y w : U64} (hy : y ∈ T) (hb : FootLtBlk st s0 y) {p : U64 × Nat} (hp : p ∈ Lk)
    (he : L.mem s0 (blockA y) = p.1) (hw : w = nextA .Ep y ∨ w = prevA .Ep y) : FootLt st T Scs Z Lk s0 w :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨y, hy, hb, ⟨p, hp, he⟩, hw⟩))))

/-! ## Combinators -/

theorem InFootLt.refl (s0 : S) : InFootLt st T Scs Z Lk s0 s0 := WritesIn.refl _ _

/-- A run writes only the footprint if its writes are footprint words. -/
theorem InFootLt.of {s0 s : S} {B : U64 → Prop} (h : WritesIn st s0 s B)
    (hB : ∀ b, Aligned b → B b → FootLt st T Scs Z Lk s0 b) : InFootLt st T Scs Z Lk s0 s :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb fun hh => hn (hB b hb hh)⟩

/-- Continue a run from `s` with a step writing `B`, every `B` word a footprint word. -/
theorem InFootLt.step {s0 s s' : S} {B : U64 → Prop} (h : InFootLt st T Scs Z Lk s0 s) (w : WritesIn st s s' B)
    (hB : ∀ b, Aligned b → B b → FootLt st T Scs Z Lk s0 b) : InFootLt st T Scs Z Lk s0 s' :=
  ⟨w.1.trans h.1, w.2.1.trans h.2.1, fun b hb hn =>
    (w.2.2 b hb fun hh => hn (hB b hb hh)).trans (h.2.2 b hb hn)⟩

/-! ## The checks the paths make, read back -/

/-- `may_run_here` passed: `t` is a thread of core `cpu`, not running a VM, with no
yield to complete, and its scheduling context (if any) on `cpu`. -/
theorem may_run_here_true {s : S} {cpu t : U64} (h : localtimer.may_run_here st s cpu t = ok true) :
    t ≠ 0#u64 ∧ L.mem s (affA t) = cpu ∧ L.mem s (stA t) ≠ sched.TS_RUNNING_VM ∧
      (L.mem s (scA t) = 0#u64 ∨ L.mem s (scCoreA (L.mem s (scA t))) = cpu) := by
  unfold localtimer.may_run_here at h
  rw [eq_of_spec_fd (obj.Tcb.is_null.spec t)] at h
  simp only [bind_ok] at h
  by_cases h0 : t = 0#u64
  · simp [h0] at h
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at h
  rw [aff_ok] at h
  simp only [bind_ok] at h
  by_cases h1 : L.mem s (affA t) = cpu
  swap
  · simp [h1] at h
  simp only [h1, ↓reduceIte] at h
  rw [eq_of_spec_fd (obj.Tcb.state.spec s t)] at h
  simp only [bind_ok] at h
  by_cases h2 : (L.mem s (stA t) != sched.TS_RUNNING_VM) = true
  swap
  · rw [if_neg h2] at h; simp at h
  rw [if_pos h2] at h
  obtain ⟨y, -, h⟩ := bind_eq_ok h
  split at h
  swap
  · simp at h
  rw [eq_of_spec_fd (obj.Tcb.sc.spec s t)] at h
  simp only [bind_ok] at h
  refine ⟨h0, h1, by simpa using h2, ?_⟩
  by_cases h3 : L.mem s (scA t) = 0#u64
  · exact Or.inl h3
  rw [if_neg h3] at h
  rw [eq_of_spec_fd (obj.Sc.cpu.spec s _)] at h
  simp only [bind_ok] at h
  exact Or.inr (by simpa using ok_inj_ff h)

/-- `current_ok` passed: `ct` may run here and runs on `csc`, a scheduling context
of core `cpu`. -/
theorem current_ok_true {s : S} {cpu ct csc : U64} (h : localtimer.current_ok st s cpu ct csc = ok true) :
    localtimer.may_run_here st s cpu ct = ok true ∧ L.mem s (scA ct) = csc ∧ L.mem s (scCoreA csc) = cpu := by
  unfold localtimer.current_ok at h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  rw [eq_of_spec_fd (obj.Tcb.sc.spec s ct)] at h
  simp only [bind_ok] at h
  by_cases h1 : L.mem s (scA ct) = csc
  swap
  · simp [h1] at h
  simp only [h1, ↓reduceIte] at h
  rw [eq_of_spec_fd (obj.Sc.cpu.spec s csc)] at h
  simp only [bind_ok] at h
  by_cases h2 : L.mem s (scCoreA csc) = cpu
  swap
  · simp [h2] at h
  exact ⟨eb, h1, h2⟩

end

/-! ## Decline -/

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]
variable {T Scs : Set U64} {Z : U64 → Nat} {Lk : List (U64 × Nat)}

/-- `update_timestamp` writes only the core's `CUR_TIME` and `CONSUMED`, footprint
words. -/
theorem ut_foot (hA : P0.ArchTotal ar) {s0 s s1 : S} {a a1 : A} (hN : NodePlaced st T s (L.cpu s))
    (hk : L.ksb s = L.ksb s0) (hc : L.cpu s = L.cpu s0) (h : sched.update_timestamp st ar s a = ok (s1, a1)) :
    WritesIn st s s1 (FootLt st T Scs Z Lk s0) := by
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN h
  simp only at er
  subst er
  obtain ⟨hct, hcn, -⟩ := ct_cn hN
  refine ⟨utW_ksb _ _, utW_cpu _ _, fun b hb hn => utW_mem hN n1 hb (fun e => hn ?_) (fun e => hn ?_)⟩
  · subst e; unfold ctA; rw [nodeAt_of_ksb hk, hc]
    exact footLt_node (by simp [layout.node.CUR_TIME])
  · subst e; unfold cnA; rw [nodeAt_of_ksb hk, hc]
    exact footLt_node (by simp [layout.node.CONSUMED])

set_option maxHeartbeats 4000000 in
/-- **A declined timer-interrupt local path writes only the footprint** (the core's
`CUR_TIME` and `CONSUMED`, or nothing). -/
theorem irq_decline_foot (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (hN : NodePlaced st T s (L.cpu s))
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (false, s', a')) :
    InFootLt st T Scs Z Lk s s' := by
  rcases irq_local_decline ar h with ⟨rfl, -⟩ | hu
  · exact InFootLt.refl _
  · exact ut_foot ar hA hN rfl rfl hu

set_option maxHeartbeats 8000000 in
/-- The decline walk of `handle_set_timer_local`, keeping the checks that ran
before its first write: the entry state, or the `FAULT_IP` write of the current
thread `t` (which `current_ok` showed is this core's) and a timestamp update. -/
theorem set_timer_decline_walk {s s' : S} {a a' : A} {n : I64} {target : U64}
    (h : localtimer.handle_set_timer_local st ar s a n target = ok (false, s', a')) :
    (s' = s ∧ a' = a) ∨ ∃ t csc nx s1, sched.cur_thread st s = ok t ∧
      localtimer.current_ok st s (L.cpu s) t csc = ok true ∧
      obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 ∧
      sched.update_timestamp st ar s1 a = ok (s', a') := by
  have fin : ∀ {x y : S} {u v : A}, (ok (false, x, u) : Result (Bool × S × A)) = ok (false, y, v) → y = x ∧ v = u := by
    intro x y u v e
    have e := ok_inj_ff e
    simp only [Prod.mk.injEq, true_and] at e
    exact ⟨e.1.symm, e.2.symm⟩
  unfold localtimer.handle_set_timer_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨cpu, ecpu, h⟩ := bind_eq_ok h
  rw [L.cur_cpu_eq] at ecpu
  have hcpu : cpu = L.cpu s := (ok_inj_ff ecpu).symm
  subst hcpu
  obtain ⟨info, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases cn : (n != fl4_abi.syscall.SysCall) = true
  · rw [if_pos cn] at h; exact Or.inl (fin h)
  rw [if_neg cn] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; exact Or.inl (fin h)
  rw [if_neg c1] at h
  by_cases c2 : (info.label != fl4_abi.label.TCBSetTimer) = true
  · rw [if_pos c2] at h; exact Or.inl (fin h)
  rw [if_neg c2] at h
  by_cases c3 : (info.extra_caps != 0#u64) = true
  · rw [if_pos c3] at h; exact Or.inl (fin h)
  rw [if_neg c3] at h
  by_cases c4 : info.length < 2#u64
  · rw [if_pos c4] at h; exact Or.inl (fin h)
  rw [if_neg c4] at h
  obtain ⟨csc, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
  cases b1
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨i2, -, h⟩ := bind_eq_ok h
  by_cases c5 : (i2 != sched.TS_RUNNING) = true
  · rw [if_pos c5] at h; exact Or.inl (fin h)
  rw [if_neg c5] at h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  right
  obtain ⟨nx, -, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨e1, e2⟩ : s' = s2 ∧ a' = a1 := by
    have h' := spec_of_eq_fd h
    clear h
    revert h'
    decl_walk
    all_goals decl_leaf
  subst e1 e2
  try rw [insn_len_eq] at es1
  exact ⟨t, csc, nx, s1, et, eb1, es1, eu⟩

/-- **A declined `TCB_SetTimer` local path writes only the footprint**: the current
thread's `FAULT_IP` (a register of a thread of this core, `current_ok`) and the
core's `CUR_TIME` and `CONSUMED`, or nothing. -/
theorem set_timer_decline_foot (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {n : I64} {target : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (h : localtimer.handle_set_timer_local st ar s a n target = ok (false, s', a')) :
    InFootLt st T Scs Z Lk s s' := by
  rcases set_timer_decline_walk ar h with ⟨rfl, -⟩ | ⟨t, csc, nx, s1, et, eok, es1, eu⟩
  · exact InFootLt.refl _
  have htT : t ∈ T := by rw [cur_thread_ok] at et; rw [← ok_inj_ff et]; exact hcT
  have ht' := hT t htT
  obtain ⟨hmr, -, -⟩ := current_ok_true eok
  obtain ⟨-, haff, -, -⟩ := may_run_here_true hmr
  have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) ht'
    (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW1
  obtain ⟨KF, hKF, e1⟩ := hW1
  have hKF' : KF.val = 392 := by rw [hKF]; simp [layout.reg.FAULT_IP]
  have aF : Aligned (core.num.U64.wrapping_add t KF) := field_aligned ht' (by omega) (by omega)
  have w1 : InFootLt st T Scs Z Lk s s1 := by
    rw [e1]
    exact InFootLt.of (writesIn_wr aF) fun b _ hb => hb ▸ footLt_thr htT haff (by omega) (by omega) (by omega)
      (by omega)
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [e1, LawfulStore.cpu_wr]; exact hN.wr
  exact InFootLt.step w1 (ut_foot ar hA hN1 w1.1 w1.2.1 eu) fun _ _ hb => hb

end

end Fl4Proofs.P2
