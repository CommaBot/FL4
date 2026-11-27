/-
# The local timer entries beside the serial gate (FL4 #94 / #97, KENTRY-PLAN lt1)

`localtimer.handle_timer_irq_local` (fl4-sync's `local_timer_irq`, a kernel
timer interrupt) and `localtimer.handle_set_timer_local` (fl4-sync's
`local_set_timer`, a `TCB_SetTimer` invocation by `SysCall`):

* `irq_local_same`: an accepted timer-interrupt entry ends where
  `syscall.handle_interrupt_entry` ends. After read-only checks (the plan,
  `current_ok`, `sched_quiet`, `release_due`, `round_robin_ok` / `fire_ok`)
  it runs the general entry's own `update_timestamp`, `check_budget`,
  `handle_interrupt` and `finish`'s three calls, in that order; the plan is
  an input that only narrows when it runs. `irq_local_decline`: a declined run
  returned the entry state or one `update_timestamp`; `irq_pre_same`: from
  that update the general entry runs as from the entry state with the Arch
  value it left (two updates are the later one, `utW_twice`).
* `set_timer_local_same`: an accepted `TCB_SetTimer` entry ends where
  `syscall.handle_syscall … SysCall` ends, given `BXI` and `CnOff` at the
  entry state, the top's flag fact, fl4-sync's contract (the general CSpace
  lookup of the `CAP` register finds a slot holding `Thread target`: fl4-sync
  found `target` with that lookup's slots locked, `lookup_slot_locked`) and
  `target ∈ T`. The general path: the same `FAULT_IP` write and
  `update_timestamp` (`lt_prefix`); `budget_ok` passes without writing
  (`check_budget_restart_suf`); `handle_invocation` reads the same message
  info, finds the same slot and cap (`lookup_slot_keep`, `found_cap_keep`),
  no extra caps (`lec_none`); `remote_tcb_stall` stalls nothing (`target`'s
  affinity is this core: `stall_none`); the decode's `SetTimer` arm reads the
  same two message registers (`syscall_arg_reg`), restarts the caller and runs
  the same `timer.insert`, which writes only timer words (`timer.insert.foot`),
  so the caller is still `Restart` and the reply arm runs as the local entry's;
  `after_invocation` passes; `finish`. `set_timer_local_decline`: the entry
  state or `LocalPre` (with `RoT`), as lcd's declines.
-/
import Fl4Proofs.P1.FastLocalDecline
import Fl4Proofs.P1.LocalInv
import Fl4Proofs.P1.QueueEntry
import Fl4Proofs.P1.QueueTimerSet
import Fl4Proofs.P1.QueueInvoke
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-! ## The timer interrupt -/

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **`irq_local_same`: the timer interrupt beside the serial gate, where it
ran, is `handle_interrupt_entry`.** -/
theorem irq_local_same {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    syscall.handle_interrupt_entry st ar s a irq = ok (s', a') := by
  unfold localtimer.handle_timer_irq_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨cpu, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : irq > i
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  obtain ⟨i1, -, h⟩ := bind_eq_ok h
  by_cases c2 : (i1 != interrupt.IRQ_TIMER) = true
  · rw [if_pos c2] at h; simp at h
  rw [if_neg c2] at h
  obtain ⟨tip, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨ct, -, h⟩ := bind_eq_ok h
  obtain ⟨csc, -, h⟩ := bind_eq_ok h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨s1, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, -, h⟩ := bind_eq_ok h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i2, -, h⟩ := bind_eq_ok h
  obtain ⟨b4, -, h⟩ := bind_eq_ok h
  obtain ⟨due, -, h⟩ := bind_eq_ok h
  obtain ⟨ok1, -, h⟩ := bind_eq_ok h
  cases ok1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨x, s2, a2⟩, ecb, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨⟨s3, a3⟩, ehi, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s4, a4⟩, esc, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s5, a5⟩, eac, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨⟨s6, a6⟩, evc, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq, true_and] at e
  obtain ⟨rfl, rfl⟩ := e
  unfold syscall.handle_interrupt_entry syscall.finish
  rw [eu]; simp only [bind_ok, uncurry_apply_pair]
  rw [ecb]; simp only [bind_ok, uncurry_apply_pair]
  rw [ehi]; simp only [bind_ok, uncurry_apply_pair]
  rw [esc]; simp only [bind_ok, uncurry_apply_pair]
  rw [eac]; simp only [bind_ok, uncurry_apply_pair]
  rw [et]; simp only [bind_ok]
  rw [evc]

set_option maxHeartbeats 4000000 in
/-- **A declined timer-interrupt entry**: the entry state, or one
`update_timestamp` (fl4-sync then runs `handle_interrupt_entry` from it). -/
theorem irq_local_decline {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (false, s', a')) :
    (s' = s ∧ a' = a) ∨ sched.update_timestamp st ar s a = ok (s', a') := by
  unfold localtimer.handle_timer_irq_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨cpu, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  have fin : ∀ {x y : S} {u v : A}, (ok (false, x, u) : Result (Bool × S × A)) = ok (false, y, v) → y = x ∧ v = u := by
    intro x y u v e
    have e := ok_inj_ff e
    simp only [Prod.mk.injEq, true_and] at e
    exact ⟨e.1.symm, e.2.symm⟩
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : irq > i
  · rw [if_pos c1] at h; exact Or.inl (fin h)
  rw [if_neg c1] at h
  obtain ⟨i1, -, h⟩ := bind_eq_ok h
  by_cases c2 : (i1 != interrupt.IRQ_TIMER) = true
  · rw [if_pos c2] at h; exact Or.inl (fin h)
  rw [if_neg c2] at h
  obtain ⟨tip, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨ct, -, h⟩ := bind_eq_ok h
  obtain ⟨csc, -, h⟩ := bind_eq_ok h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  right
  obtain ⟨⟨s1, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨e1, e2⟩ : s' = s1 ∧ a' = a1 := by
    have h' := spec_of_eq_fd h
    clear h
    revert h'
    decl_walk
    all_goals decl_leaf
  subst e1 e2
  exact eu

variable [L : LawfulStore st]

/-- **After a timestamp update the general interrupt entry runs as from the
entry state** with the Arch value the update left. -/
theorem irq_pre_same (hX : StoreExt st) (hA : P0.ArchTotal ar) {T : Set U64} {s : S}
    (hN : NodePlaced st T s (L.cpu s)) {a : A} {r : S × A} (h : sched.update_timestamp st ar s a = ok r)
    (irq : U64) :
    syscall.handle_interrupt_entry st ar r.1 r.2 irq = syscall.handle_interrupt_entry st ar s r.2 irq := by
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN h
  rw [er]
  obtain ⟨⟨n2, b2⟩, hn, -⟩ := spec_ex_fd (hA.now r.2)
  unfold syscall.handle_interrupt_entry
  rw [update_timestamp_ok ar (utW_placed hN n1) hn, update_timestamp_ok ar hN hn, utW_twice hX hN]

/-- **The timer-interrupt local entry where it ran: the general entry's
postconditions** (on the `true` results). -/
theorem irq_local_triple (hA : P0.ArchTotal ar) {s : S} {a : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    {P : S × A → Prop} (hG : syscall.handle_interrupt_entry st ar s a irq ⦃ P ⦄) :
    localtimer.handle_timer_irq_local st ar s a irq p ⦃ r => r.1 = true → P (r.2.1, r.2.2) ⦄ := by
  obtain ⟨⟨b, s', a'⟩, e, -⟩ := spec_ex_fd (P0.localtimer.handle_timer_irq_local.p0 st ar s a irq p L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := irq_local_same ar e
  rw [hs, WP.spec_ok] at hG
  exact hG

end

/-! ## `TCB_SetTimer` -/

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A)

theorem insn_len_eq : localtimer.SYSCALL_INSN_LEN = 2#u64 := by
  first | rfl | (unfold localtimer.SYSCALL_INSN_LEN; rfl) | simp [localtimer.SYSCALL_INSN_LEN]

set_option maxHeartbeats 8000000 in
/-- **A declined `handle_set_timer_local`**: the entry state, or the prefix
(`SysCall`, trap clear). -/
theorem set_timer_local_decline {s s' : S} {a a' : A} {n : I64} {target : U64}
    (h : localtimer.handle_set_timer_local st ar s a n target = ok (false, s', a')) :
    (s' = s ∧ a' = a) ∨ (LocalPre (st := st) ar s a (s', a') ∧ RoT st s n) := by
  have fin : ∀ {x y : S} {u v : A}, (ok (false, x, u) : Result (Bool × S × A)) = ok (false, y, v) → y = x ∧ v = u := by
    intro x y u v e
    have e := ok_inj_ff e
    simp only [Prod.mk.injEq, true_and] at e
    exact ⟨e.1.symm, e.2.symm⟩
  unfold localtimer.handle_set_timer_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨cpu, -, h⟩ := bind_eq_ok h
  obtain ⟨info, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases cn : (n != fl4_abi.syscall.SysCall) = true
  · rw [if_pos cn] at h; exact Or.inl (fin h)
  rw [if_neg cn] at h
  have hn : n = fl4_abi.syscall.SysCall := by simp only [bne_iff_ne, ne_eq, not_not] at cn; exact cn
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
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
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
  obtain ⟨nx, enx, h⟩ := bind_eq_ok h
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
  subst hn
  exact ⟨⟨t, nx, s1, et, enx, es1, eu⟩, Or.inl rng_call⟩

variable [L : LawfulStore st]

/-- Two distinct placed TCBs' words (or one TCB's two offsets) differ. -/
theorem tcb_word_ne {u y K1 K2 : U64} (hu : TcbAddr u) (hy : TcbAddr y) (h1 : K1.val < 4096) (h2 : K2.val < 4096)
    (hne : u = y → K1.val ≠ K2.val) :
    core.num.U64.wrapping_add u K1 ≠ core.num.U64.wrapping_add y K2 := by
  intro e
  have e' := congrArg UScalar.val e
  rw [tcb_wadd_val hu h1, tcb_wadd_val hy h2] at e'
  by_cases huy : u = y
  · subst huy; exact hne rfl (by omega)
  · have hv : u.val ≠ y.val := fun hv => huy (UScalar.eq_of_val_eq hv)
    have := hu.align; have := hy.align
    omega

/-- A TCB word is no word of a placed node. -/
theorem tcb_node_ne {T : Set U64} {s : S} {c u K o : U64} (hN : NodePlaced st T s c) (huT : u ∈ T) (hu : TcbAddr u)
    (hK : K.val < 4096) (ho : o.val < 4288) :
    core.num.U64.wrapping_add u K ≠ L.nodeAt s c o := by
  intro e
  have e' := congrArg UScalar.val e
  rw [tcb_wadd_val hu hK, nodeAt_val hN ho] at e'
  have := hN.disj u huT
  omega

/-- **The prefix of the local `TCB_SetTimer` entry** (`FAULT_IP` write,
`update_timestamp`): it writes only `t`'s `FAULT_IP` and the core's `CUR_TIME`
/ `CONSUMED`. -/
theorem lt_prefix {T : Set U64} {s s1 s2 : S} {a a2 : A} {t v : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (htT : t ∈ T)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP v = ok s1)
    (hu : sched.update_timestamp st ar s1 a = ok (s2, a2)) (hA : P0.ArchTotal ar) :
    ∃ KF : U64, KF.val = 392 ∧
      WritesIn st s s2 (fun b => b = core.num.U64.wrapping_add t KF ∨ b = ctA (L := L) s ∨ b = cnA (L := L) s) := by
  have ht' := hT t htT
  obtain ⟨hct, hcn, -⟩ := ct_cn hN
  have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP v ht' (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW1
  obtain ⟨KF, hKF, e1⟩ := hW1
  have hKF' : KF.val = 392 := by rw [hKF]; simp [layout.reg.FAULT_IP]
  have aF : Aligned (core.num.U64.wrapping_add t KF) := field_aligned ht' (by omega) (by omega)
  obtain ⟨⟨n, b2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [e1, LawfulStore.cpu_wr]; exact hN.wr
  rw [update_timestamp_ok ar hN1 hn] at hu
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff hu)
  have ec : ctA (L := L) s1 = ctA (L := L) s := by rw [e1, ctA_wr]
  have en : cnA (L := L) s1 = cnA (L := L) s := by rw [e1, cnA_wr]
  refine ⟨KF, hKF', ?_, ?_, fun b hb hn' => ?_⟩
  · unfold utW; rw [e1]; simp only [L.ksb_wr]
  · unfold utW; rw [e1]; simp only [LawfulStore.cpu_wr]
  · unfold utW
    rw [ec, en, mem_wr_ne' hcn hb (fun e => hn' (Or.inr (Or.inr e.symm))),
      mem_wr_ne' hct hb (fun e => hn' (Or.inr (Or.inl e.symm))), e1,
      mem_wr_ne' aF hb (fun e => hn' (Or.inl e.symm))]

/-- A word of a placed TCB other than `t`'s `FAULT_IP`, across the prefix. -/
theorem lt_tcbK {T : Set U64} {s s2 : S} {t KF : U64} (hKF : KF.val = 392) (hT : TcbPlaced T)
    (hN : NodePlaced st T s (L.cpu s)) (htT : t ∈ T)
    (hW : WritesIn st s s2 (fun b => b = core.num.U64.wrapping_add t KF ∨ b = ctA (L := L) s ∨ b = cnA (L := L) s))
    {u K : U64} (huT : u ∈ T) (hK : K.val < 4096) (h8 : K.val % 8 = 0) (hne : u = t → K.val ≠ 392) :
    L.mem s2 (core.num.U64.wrapping_add u K) = L.mem s (core.num.U64.wrapping_add u K) := by
  have hu := hT u huT
  refine hW.mem_eq (field_aligned hu hK h8) ?_
  rintro (e | e | e)
  · exact tcb_word_ne hu (hT t htT) hK (by omega) (fun h => by rw [hKF]; exact hne h) e
  · exact tcb_node_ne hN huT hu hK (by simp [layout.node.CUR_TIME]) e
  · exact tcb_node_ne hN huT hu hK (by simp [layout.node.CONSUMED]) e

/-- **The slot a lookup found reads the same cap across a write that misses
the cap-slot words** (`CnOff`). -/
theorem found_cap_keep {T Cs Sg : Set U64} {s s' : S} {t c : U64} {r : cspace.Resolved}
    (hCn : CnOff (L := L) T Cs Sg s t)
    (oK : ∀ b, OutsideObjs st T Cs s b → L.mem s' b = L.mem s b)
    (h : cspace.lookup_slot st s t c = ok (core.result.Result.Ok r)) :
    obj.Slot.cap st r.slot s' = obj.Slot.cap st r.slot s := by
  unfold cspace.lookup_slot at h
  obtain ⟨sl, hsl, h⟩ := bind_eq_ok h
  obtain ⟨root, hroot, h⟩ := bind_eq_ok h
  obtain ⟨C, hC0, hcl, hWc⟩ := hCn sl root hsl hroot
  have slotK : ∀ p r, C p r → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) s' = obj.Slot.cap st (cnSlot p (x &&& m)) s := by
    intro p r hp m hm x
    obtain ⟨h1, h2⟩ := hWc p r m x hp hm
    unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, oK _ h1.1, oK _ h2.1]
  obtain ⟨p, r', m, y, hp, hm, hs⟩ := rab_loop_slot st C hcl 66 root _ 65#u64 r (by simp) hC0 h
  rw [hs, slotK p r' hp m hm y]

/-- No extra caps: `lookup_extra_caps` returns. -/
theorem lec_none (s : S) (t : obj.Tcb) (buf : U64) {info : msginfo.MessageInfo} (h0 : info.extra_caps = 0#u64) :
    ∃ e, ipc.lookup_extra_caps st s t buf info = ok (core.result.Result.Ok e) := by
  unfold ipc.lookup_extra_caps
  by_cases hb : buf = 0#u64
  · rw [if_pos hb]; exact ⟨_, rfl⟩
  · rw [if_neg hb, lecLoop_unfold, h0]
    have h00 : ¬ (0#u64 < 0#u64) := by scalar_tac
    unfold ipc.lookup_extra_caps_loop.body
    rw [if_neg h00]
    simp

/-- A message register argument does not read the buffer. -/
theorem syscall_arg_reg (s : S) (t : obj.Tcb) (b b' i : U64) (hi : i < msg.N_MSG_REGISTERS) :
    msg.syscall_arg st s t b i = msg.syscall_arg st s t b' i := by
  unfold msg.syscall_arg; rw [if_pos hi, if_pos hi]

/-- `remote_tcb_stall` of a thread of this core stalls nothing. -/
theorem stall_none (s : S) (a : A) (y : U64) (hy : L.mem s (affA y) = L.cpu s) :
    smp.remote_tcb_stall st ar s a y = ok (s, a) := by
  unfold smp.remote_tcb_stall
  rw [aff_ok, L.cur_cpu_eq, hy]
  simp

set_option maxHeartbeats 4000000 in
/-- `tcb.decode` at `TCB_SetTimer` once the stall did nothing: its `SetTimer`
arm. -/
theorem decode_set_timer {s : S} {a : A} {y : U64} {c : tcb.Ctx}
    (hst : smp.remote_tcb_stall st ar s a y = ok (s, a)) (hlen : ¬ c.length < 2#u64) :
    tcb.decode st ar s a fl4_abi.label.TCBSetTimer y c =
      (do
        let deadline ← tcb.arg st s c 0#u64
        let badge ← tcb.arg st s c 1#u64
        let s2 ← tcb.restart_caller st s
        let s3 ← timer.insert st s2 y deadline badge
        ok (core.result.Result.Ok (), s3, a)) := by
  unfold tcb.decode
  rw [hst]; simp only [bind_ok, uncurry_apply_pair]
  simp (config := { decide := true }) only [fl4_abi.label.TCBSetTimer, fl4_abi.label.TCBSetEPTRoot,
    fl4_abi.label.TCBReadRegisters, fl4_abi.label.TCBWriteRegisters, fl4_abi.label.TCBCopyRegisters,
    fl4_abi.label.TCBSuspend, fl4_abi.label.TCBResume, fl4_abi.label.TCBConfigure,
    fl4_abi.label.TCBSetPriority, fl4_abi.label.TCBSetMCPriority, fl4_abi.label.TCBSetSchedParams,
    fl4_abi.label.TCBSetIPCBuffer, fl4_abi.label.TCBSetSpace, fl4_abi.label.TCBSetTimeoutEndpoint,
    fl4_abi.label.TCBBindNotification, fl4_abi.label.TCBUnbindNotification,
    fl4_abi.label.TCBConfigureSingleStepping, fl4_abi.label.TCBSetBreakpoint, fl4_abi.label.TCBGetBreakpoint,
    fl4_abi.label.TCBUnsetBreakpoint, fl4_abi.label.TCBSetTLSBase, fl4_abi.label.TCBSetFlags,
    ↓reduceIte, if_true, if_false, hlen]

set_option maxHeartbeats 16000000 in
/-- **`set_timer_local_same`: the `TCB_SetTimer` entry beside the serial
gate, where it ran, is the general entry** `syscall.handle_syscall … SysCall`
(module docstring). -/
theorem set_timer_local_same (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s s' : S} {a a' : A} {n : I64}
    {target : U64} {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hflag : ∀ t v, sched.cur_thread st s = ok t → obj.Tcb.flags st t (L.wr s (regA t layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hL : ∀ t, sched.cur_thread st s = ok t → ∃ r : cspace.Resolved,
      cspace.lookup_slot st s t (L.mem s (regA t layout.reg.CAP)) = ok (core.result.Result.Ok r) ∧
      obj.Slot.cap st r.slot s = ok (capability.Cap.Thread target))
    (htg : target ∈ T)
    (h : localtimer.handle_set_timer_local st ar s a n target = ok (true, s', a')) :
    syscall.handle_syscall st ar s a n = ok (s', a') := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  unfold localtimer.handle_set_timer_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨cpu, ecpu, h⟩ := bind_eq_ok h
  rw [L.cur_cpu_eq] at ecpu
  have hcpu : cpu = L.cpu s := (ok_inj_ff ecpu).symm
  subst hcpu
  obtain ⟨info, ei, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases cn : (n != fl4_abi.syscall.SysCall) = true
  · rw [if_pos cn] at h; simp at h
  rw [if_neg cn] at h
  have hn : n = fl4_abi.syscall.SysCall := by simp only [bne_iff_ne, ne_eq, not_not] at cn; exact cn
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  by_cases c2 : (info.label != fl4_abi.label.TCBSetTimer) = true
  · rw [if_pos c2] at h; simp at h
  rw [if_neg c2] at h
  have hlbl : info.label = fl4_abi.label.TCBSetTimer := by
    simp only [bne_iff_ne, ne_eq, not_not] at c2; exact c2
  by_cases c3 : (info.extra_caps != 0#u64) = true
  · rw [if_pos c3] at h; simp at h
  rw [if_neg c3] at h
  have hx0 : info.extra_caps = 0#u64 := by simp only [bne_iff_ne, ne_eq, not_not] at c3; exact c3
  by_cases c4 : info.length < 2#u64
  · rw [if_pos c4] at h; simp at h
  rw [if_neg c4] at h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  by_cases c5 : (i2 != sched.TS_RUNNING) = true
  · rw [if_pos c5] at h; simp at h
  rw [if_neg c5] at h
  have hrun : i2 = sched.TS_RUNNING := by simp only [bne_iff_ne, ne_eq, not_not] at c5; exact c5
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨nx, enx, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  try rw [insn_len_eq] at es1
  obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, -, h⟩ := bind_eq_ok h
  obtain ⟨dl, edl, h⟩ := bind_eq_ok h
  obtain ⟨bd, ebd, h⟩ := bind_eq_ok h
  obtain ⟨cns, ecns, h⟩ := bind_eq_ok h
  obtain ⟨b4, eb4, h⟩ := bind_eq_ok h
  cases b4
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b5, -, h⟩ := bind_eq_ok h
  cases b5
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨b6, -, h⟩ := bind_eq_ok h
  cases b6
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  -- both deadline arms run the same tail
  have tail : (do
      let s3 ← sched.set_thread_state st s2 t sched.TS_RESTART
      let s4 ← timer.insert st s3 target dl bd
      let s5 ← msg.reply_success_empty st s4 t
      let s6 ← sched.set_thread_state st s5 t sched.TS_RUNNING
      let (s7, a2) ← sched.schedule st ar s6 a1
      let (s8, a3) ← sched.activate_thread st ar s7 a2
      let t1 ← sched.cur_thread st s8
      let (s9, a4) ← vcpu.check st ar s8 a3 t1
      ok (true, s9, a4)) = ok (true, s', a') := by
    by_cases cd : (dl != 0#u64) = true
    · rw [if_pos cd] at h
      by_cases cd2 : dl <= now
      · rw [if_pos cd2] at h; simp at h
      · rw [if_neg cd2] at h; exact h
    · rw [if_neg cd] at h; exact h
  clear h
  obtain ⟨s3, es3, h⟩ := bind_eq_ok tail
  obtain ⟨s4, es4, h⟩ := bind_eq_ok h
  obtain ⟨s5, es5, h⟩ := bind_eq_ok h
  obtain ⟨s6, es6, h⟩ := bind_eq_ok h
  obtain ⟨⟨s7, a2⟩, es7, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s8, a3⟩, es8, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨t1, et1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s9, a4⟩, es9, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq, true_and] at e
  obtain ⟨rfl, rfl⟩ := e
  -- the prefix
  have htT : t ∈ T := by
    rw [cur_thread_ok] at et; rw [← ok_inj_ff et]; exact hcT
  have ht' := hT t htT
  have htg' := hT target htg
  obtain ⟨et2, tK, oK⟩ := inv_prefix ar hT hN hcC et htT es1 eu hA
  obtain ⟨KF, hKF, hW⟩ := lt_prefix ar hT hN htT es1 eu hA
  have uK : ∀ {u K : U64}, u ∈ T → K.val < 4096 → K.val % 8 = 0 → (u = t → K.val ≠ 392) →
      L.mem s2 (core.num.U64.wrapping_add u K) = L.mem s (core.num.U64.wrapping_add u K) :=
    fun huT hK h8 hne => lt_tcbK hKF hT hN htT hW huT hK h8 hne
  -- cur_sc at the dispatch state
  have ecsc2 : sched.cur_sc st s2 = ok csc := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at ecsc
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s2), ← ok_inj_ff ecsc]
    have aC : Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_SC) :=
      nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
    have eA : L.nodeA s2 layout.node.CUR_SC = L.nodeA s layout.node.CUR_SC := by
      unfold LawfulStore.nodeA; rw [hW.2.1, nodeAt_of_ksb hW.1]
    rw [eA]
    unfold LawfulStore.nodeA
    refine congrArg ok (hW.mem_eq aC ?_)
    have vS := nodeAt_val hN (off := layout.node.CUR_SC) (by simp [layout.node.CUR_SC])
    have vb := nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
    have vn := nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
    rintro (e | e | e)
    · exact tcb_node_ne hN htT ht' (by omega) (by simp [layout.node.CUR_SC]) e.symm
    · have e' := congrArg UScalar.val e; unfold ctA at e'; rw [vS, vb] at e'
      simp [layout.node.CUR_SC, layout.node.CUR_TIME] at e'
    · have e' := congrArg UScalar.val e; unfold cnA at e'; rw [vS, vn] at e'
      simp [layout.node.CUR_SC, layout.node.CONSUMED] at e'
  have hb : syscall.budget_ok st ar s1 a = ok (true, s2, a1) := by
    unfold syscall.budget_ok
    rw [eu]; simp only [bind_ok, uncurry_apply_pair]
    exact check_budget_restart_suf ar ecsc2 ecns eb4
  -- the flags word at the `FAULT_IP`-written state
  have hs1 : s1 = L.wr s (regA t layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
      ht' (by simp [layout.reg.FAULT_IP])
    rw [es1, WP.spec_ok] at hW1
    obtain ⟨K, hK, e1⟩ := hW1
    obtain ⟨K', hK', eK'⟩ := regA_eq ht' (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    rw [e1, eK']; congr 2; apply UScalar.eq_of_val_eq; rw [hK, hK']
  have hfl := hflag t (core.num.U64.wrapping_sub nx 2#u64) et
  rw [← hs1] at hfl
  obtain ⟨fl, efl, hfl0⟩ := spec_ex_fd hfl
  have c1' : ¬ (fl &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true := by
    rw [hfl0]; simp
  -- the reads of `handle_invocation` at the dispatch state
  have ei2' : msg.msg_info st s2 t = ok info := by
    unfold msg.msg_info at ei ⊢
    rw [reg_keepK ht' (r := layout.reg.MSG_INFO) (by simp) (by simp) tK]; exact ei
  have ecap2 : obj.Tcb.reg st t s2 layout.reg.CAP = ok (L.mem s (regA t layout.reg.CAP)) := by
    rw [reg_keepK ht' (r := layout.reg.CAP) (by simp) (by simp) tK, reg_ok]
  obtain ⟨r, er, ecr⟩ := hL t et
  have er2 := lookup_slot_keep ht' (hCn t et) tK oK er
  have ecr2 : obj.Slot.cap st r.slot s2 = ok (capability.Cap.Thread target) := by
    rw [found_cap_keep (hCn t et) oK er]; exact ecr
  obtain ⟨buf, ebuf, -⟩ := spec_ex_fd (P0.msg.lookup_ipc_buffer.p0 st s2 false t L.total)
  obtain ⟨ex, eex⟩ := lec_none (st := st) (L := L) s2 t buf hx0
  -- the stall: `target` is this core's
  have haff : L.mem s (affA target) = L.cpu s := by
    unfold localtimer.set_timer_target_ok at eb
    obtain ⟨ia, eia, eb⟩ := bind_eq_ok eb
    by_cases ca : (ia != L.cpu s) = true
    · rw [if_pos ca] at eb; simp at eb
    · simp only [bne_iff_ne, ne_eq, not_not] at ca
      rw [aff_ok] at eia; rw [ok_inj_ff eia]; exact ca
  have haff2 : L.mem s2 (affA target) = L.cpu s2 := by
    rw [hW.2.1]
    have e : affA target = core.num.U64.wrapping_add target 3520#u64 := rfl
    rw [e, uK htg (by simp) (by simp) (fun _ => by simp), ← e, haff]
  have hst := stall_none (st := st) (L := L) ar s2 a1 target haff2
  -- the length passed to the decode
  have hlen : ∀ len : U64, (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS
      else ok info.length) else ok info.length : Result U64) = ok len → ¬ len < 2#u64 := by
    intro len e
    have hN4 : msg.N_MSG_REGISTERS = 4#u64 := by unfold msg.N_MSG_REGISTERS; rfl
    by_cases g1 : info.length > msg.N_MSG_REGISTERS
    · rw [if_pos g1] at e
      by_cases g2 : buf = 0#u64
      · rw [if_pos g2] at e; rw [← ok_inj_ff e, hN4]; decide
      · rw [if_neg g2] at e; rw [← ok_inj_ff e]; exact c4
    · rw [if_neg g1] at e; rw [← ok_inj_ff e]; exact c4
  obtain ⟨len, elen, -⟩ : ∃ len, (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64
      then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length : Result U64) = ok len ∧ True := by
    by_cases g1 : info.length > msg.N_MSG_REGISTERS
    · rw [if_pos g1]
      by_cases g2 : buf = 0#u64
      · rw [if_pos g2]; exact ⟨_, rfl, trivial⟩
      · rw [if_neg g2]; exact ⟨_, rfl, trivial⟩
    · rw [if_neg g1]; exact ⟨_, rfl, trivial⟩
  have hlen' := hlen len elen
  -- the decode's two arguments and the restart
  have hNR : ∀ i : U64, i.val < 2 → i < msg.N_MSG_REGISTERS := by
    intro i hi
    have hN4 : msg.N_MSG_REGISTERS = 4#u64 := by unfold msg.N_MSG_REGISTERS; rfl
    rw [hN4]; scalar_tac
  have earg0 : tcb.arg st s2 { length := len, buf := buf, call := true, slot := r.slot, extra := ex } 0#u64 = ok dl := by
    unfold tcb.arg; rw [et2]; simp only [bind_ok]
    rw [syscall_arg_reg (st := st) (L := L) s2 t buf 0#u64 0#u64 (hNR _ (by decide))]; exact edl
  have earg1 : tcb.arg st s2 { length := len, buf := buf, call := true, slot := r.slot, extra := ex } 1#u64 = ok bd := by
    unfold tcb.arg; rw [et2]; simp only [bind_ok]
    rw [syscall_arg_reg (st := st) (L := L) s2 t buf 0#u64 1#u64 (hNR _ (by decide))]; exact ebd
  have erc : tcb.restart_caller st s2 = ok s3 := by
    unfold tcb.restart_caller; rw [et2]; simp only [bind_ok]; exact es3
  -- the caller is still `Restart` after the timer insert
  have hst4 : obj.Tcb.state st t s4 = ok sched.TS_RESTART := by
    have hI1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := by
      have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
        ht' (by simp [layout.reg.FAULT_IP])
      rw [es1, WP.spec_ok] at hW1
      obtain ⟨K, hK, e1⟩ := hW1
      have hK' : K.val = 392 := by rw [hK]; simp [layout.reg.FAULT_IP]
      rw [e1]; exact (regW_all (BXI.blk hI) htT (by omega) (by omega) (by omega)).1
    have hB2 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s2 := by
      have := sched.update_timestamp.bxc hA s1 a (BlkOK.bxi hI1)
      rw [eu, WP.spec_ok] at this
      try simp only [WP.uncurry'_pair] at this
      exact this.1.1
    have ec2 : L.curW s2 = t := by
      rw [cur_thread_ok] at et2; exact ok_inj_ff et2
    have est : stA t = core.num.U64.wrapping_add t 3328#u64 := stA_eq t
    have hs2t : L.mem s2 (stA t) = sched.TS_RUNNING := by
      rw [est, uK htT (by simp) (by simp) (fun _ => by simp), ← est]
      rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s t)] at ei2
      rw [ok_inj_ff ei2]; exact hrun
    have hnb : ¬ Blocked (L.mem s2 (stA (L.curW s2))) := by
      rw [ec2, hs2t]; unfold Blocked
      simp [sched.TS_RUNNING, sched.TS_BLOCKED_ON_SEND, sched.TS_BLOCKED_ON_RECV, sched.TS_BLOCKED_ON_NTFN]
    have hnr : L.mem s2 (stA (L.curW s2)) ≠ sched.TS_BLOCKED_ON_REPLY := by
      rw [ec2, hs2t]; simp [sched.TS_RUNNING, sched.TS_BLOCKED_ON_REPLY]
    have hR := tcb.restart_caller.blk (Es := ∅) s2 (BXI.blk hB2) hnb hnr
    rw [erc, WP.spec_ok] at hR
    obtain ⟨hBk3, -, hR3, -⟩ := hR
    rw [ec2] at hR3
    have hF := timer.insert.foot s3 target dl bd (BlkOK.tinv hBk3) htg
    rw [es4, WP.spec_ok] at hF
    obtain ⟨-, -, hW4, -⟩ := hF
    have q3 := hBk3.1.choose_spec.choose_spec
    have aS : Aligned (stA t) := by rw [est]; exact field_aligned ht' (by simp) (by simp)
    rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s4 t), hW4.mem_eq aS ?_, hR3]
    rw [est]
    rintro ((⟨y, hy, K, hK1, hK2, e⟩ | ⟨c, hc, o, ho, e⟩) | e)
    · exact tcb_word_ne ht' (hT y hy) (by simp) (by omega) (fun _ => by simp; omega) e
    · exact tcb_node_ne (q3.nodes c hc) htT ht' (by simp) (by omega) e
    · exact tcb_node_ne (q3.nodes _ q3.cur) htT ht' (by simp) (by simp [layout.node.REPROGRAM]) e
  -- the general run
  have c2s : ¬ fl4_abi.syscall.SysCall < fl4_abi.syscall.SYSCALL_MIN := rng_call.1
  have c3s : ¬ fl4_abi.syscall.SysCall > fl4_abi.syscall.SYSCALL_MAX := rng_call.2
  have nRR : ¬ fl4_abi.syscall.SysCall = fl4_abi.syscall.SysReplyRecv := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysReplyRecv; decide
  have n15 : ¬ fl4_abi.syscall.SysCall = fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysSend; decide
  have n16 : ¬ fl4_abi.syscall.SysCall = fl4_abi.syscall.SysNBSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysNBSend; decide
  have edec : tcb.decode st ar s2 a1 info.label target
      { length := len, buf := buf, call := true, slot := r.slot, extra := ex } = ok (core.result.Result.Ok (), s4, a1) := by
    rw [hlbl, decode_set_timer ar (c := { length := len, buf := buf, call := true, slot := r.slot, extra := ex }) hst hlen']
    rw [earg0]; simp only [bind_ok]
    rw [earg1]; simp only [bind_ok]
    rw [erc]; simp only [bind_ok]
    rw [es4]; simp only [bind_ok]
  rw [hn]
  unfold syscall.handle_syscall syscall.syscall
  rw [et]; simp only [bind_ok]
  rw [enx]; simp only [lift, bind_ok]
  rw [es1]; simp only [bind_ok]
  rw [efl]; simp only [lift, bind_ok, if_neg c1', if_neg c2s, if_neg c3s]
  rw [hb]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte, if_true, eq_self_iff_true, nRR]
  unfold syscall.dispatch_syscall
  rw [et2]; simp only [bind_ok]
  rw [ecap2]; simp only [bind_ok]
  rw [reg_ok]; simp only [bind_ok]
  simp only [n15, n16, ↓reduceIte, if_true, if_false]
  unfold syscall.handle_invocation
  rw [et2]; simp only [bind_ok]
  rw [ei2']; simp only [bind_ok]
  rw [er2]; simp only [bind_ok]
  rw [ecr2]; simp only [bind_ok]
  rw [ebuf]; simp only [bind_ok]
  rw [eex]; simp only [bind_ok]
  rw [elen]; simp only [bind_ok]
  unfold syscall.decode_invocation
  rw [et2]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  rw [edec]; simp only [bind_ok, uncurry_apply_pair]
  rw [hst4]; simp only [bind_ok, ↓reduceIte, eq_self_iff_true, if_true]
  rw [es5]; simp only [bind_ok]
  rw [es6]; simp only [bind_ok, uncurry_apply_pair]
  unfold syscall.after_invocation; simp only [bind_ok, uncurry_apply_pair]
  unfold syscall.finish
  rw [es7]; simp only [bind_ok, uncurry_apply_pair]
  rw [es8]; simp only [bind_ok, uncurry_apply_pair]
  rw [et1]; simp only [bind_ok]
  rw [es9]
  try simp only [bind_ok, uncurry_apply_pair]

/-- **The `TCB_SetTimer` local entry where it ran: the general entry's
postconditions** (on the `true` results). -/
theorem set_timer_local_triple (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s : S} {a : A} {n : I64}
    {target : U64} {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {P : S × A → Prop}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hflag : ∀ t v, sched.cur_thread st s = ok t → obj.Tcb.flags st t (L.wr s (regA t layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hL : ∀ t, sched.cur_thread st s = ok t → ∃ r : cspace.Resolved,
      cspace.lookup_slot st s t (L.mem s (regA t layout.reg.CAP)) = ok (core.result.Result.Ok r) ∧
      obj.Slot.cap st r.slot s = ok (capability.Cap.Thread target))
    (htg : target ∈ T) (hG : syscall.handle_syscall st ar s a n ⦃ P ⦄) :
    localtimer.handle_set_timer_local st ar s a n target ⦃ r => r.1 = true → P (r.2.1, r.2.2) ⦄ := by
  obtain ⟨⟨b, s', a'⟩, e, -⟩ :=
    spec_ex_fd (P0.localtimer.handle_set_timer_local.p0 st ar s a n target L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := set_timer_local_same ar hA hI hCn hflag hL htg e
  rw [hs, WP.spec_ok] at hG
  exact hG

end

end Fl4Proofs.P1
