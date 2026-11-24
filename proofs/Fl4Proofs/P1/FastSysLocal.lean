/-
# The syscall entry beside the serial gate, accepted (KENTRY-PLAN lcs)

`syscall.handle_syscall_local` (fl4-sync's `local_syscall` for a trapped
thread or a ReplyRecv) where it returns `true` is the general entry
`syscall.handle_syscall` itself, fast paths included:

* its trap arm (`TRAP_SYSCALLS` set) runs `fastpath.fault` with the number
  `trapped_syscall_number!` (the extraction's `IScalar.hcast .U64 number`)
  after the `FAULT_IP` write, `update_timestamp` and a passing `sufficient`:
  the general `syscall … true` takes the same `FAULT_IP` write, reads the same
  flags word (`flags_fip`: the flags word is not the `FAULT_IP` register), and
  `unknown_syscall_fault … true` passes `budget_ok` without writing
  (`check_budget_restart_suf`), re-reads the same current thread
  (`local_prefix_keep`) and calls the same `fastpath.fault`;
* its ReplyRecv arm runs `fastpath.reply_recv_found` with fl4-sync's `found`:
  the general `syscall … SysReplyRecv true` passes the same checks and its own
  fast path `fastpath.reply_recv` reads `reply_caps` at the dispatch state,
  which is `found` (fl4-sync computes it at the entry state; `local_prefix_keep`).

So no general-path reads are needed (unlike the VM entries, whose fast paths
are not `handle_syscall`'s): `syscall_local_same` / `syscall_local_triple`.
-/
import Fl4Proofs.P1.FastVmLocal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

theorem flags_spec_mem (s : S) (t : U64) :
    obj.Tcb.flags st t s ⦃ f => f = L.mem s (core.num.U64.wrapping_add t 3456#u64) ⦄ := by
  unfold obj.Tcb.flags layout.tcb.FLAGS layout.tcb.F
  step as ⟨i, hi⟩
  have e : core.num.U64.wrapping_add t i = core.num.U64.wrapping_add t 3456#u64 := by
    apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, hi]
  simp only [lift, bind_ok]
  rw [L.read_eq, WP.spec_ok, e]

theorem flags_mem (s : S) (t : U64) :
    obj.Tcb.flags st t s = ok (L.mem s (core.num.U64.wrapping_add t 3456#u64)) := by
  obtain ⟨f, e, hf⟩ := spec_ex_fd (flags_spec_mem (L := L) s t)
  rw [e, hf]

/-- **The flags word past the `FAULT_IP` write** (offset 3456 against the
register at 392). -/
theorem flags_fip {s : S} {t v : U64} (ht : TcbAddr t) :
    obj.Tcb.flags st t (L.wr s (regA t layout.reg.FAULT_IP) v) = obj.Tcb.flags st t s := by
  obtain ⟨K, hK, eK⟩ := regA_eq ht (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
  have hK' : K.val = 392 := by rw [hK]; simp [layout.reg.FAULT_IP]
  have aF : Aligned (core.num.U64.wrapping_add t K) := field_aligned ht (by omega) (by omega)
  have aL : Aligned (core.num.U64.wrapping_add t 3456#u64) := field_aligned ht (by simp) (by simp)
  rw [flags_mem, flags_mem, eK, mem_wr_ne' aF aL ?_]
  intro e
  have e' := congrArg UScalar.val e
  rw [tcb_wadd_val ht (o := K) (by omega), tcb_wadd_val ht (o := 3456#u64) (by simp)] at e'
  simp at e'; omega

/-- The `FAULT_IP` write of `syscall` as a store write (`rr_vm_local_same`'s `hs1`). -/
theorem set_fip_wr {s s1 : S} {t v : U64} (ht : TcbAddr t)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP v = ok s1) :
    s1 = L.wr s (regA t layout.reg.FAULT_IP) v := by
  have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP v ht (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW1
  obtain ⟨K, hK, e1⟩ := hW1
  obtain ⟨K', hK', eK'⟩ := regA_eq ht (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
  rw [e1, eK']; congr 2; apply UScalar.eq_of_val_eq; rw [hK, hK']

/-- **The general `syscall … SysReplyRecv` with its fast paths enabled, where
`fastpath.reply_recv` runs at the dispatch state** (`syscall_rr_true`'s
accepted twin). -/
theorem syscall_rr_fast {s s1 s2 s' : S} {a a2 a' : A} {t nx i1 : U64}
    (et : sched.cur_thread st s = ok t) (enx : obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1)
    (ef : obj.Tcb.flags st t s1 = ok i1)
    (c1 : ¬ (i1 &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true)
    (eb : syscall.budget_ok st ar s1 a = ok (true, s2, a2))
    (hrr : fastpath.reply_recv st ar s2 a2 = ok (true, s', a')) :
    syscall.syscall st ar s a fl4_abi.syscall.SysReplyRecv true = ok (true, s', a') := by
  have c2 : ¬ fl4_abi.syscall.SysReplyRecv < fl4_abi.syscall.SYSCALL_MIN := by
    unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SYSCALL_MIN
    first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
  have c3 : ¬ fl4_abi.syscall.SysReplyRecv > fl4_abi.syscall.SYSCALL_MAX := by
    unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SYSCALL_MAX
    first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
  unfold syscall.syscall
  rw [et]; simp only [bind_ok]
  rw [enx]; simp only [lift, bind_ok]
  rw [es1]; simp only [bind_ok]
  rw [ef]; simp only [lift, bind_ok, if_neg c1, if_neg c2, if_neg c3]
  rw [eb]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte, if_true, eq_self_iff_true]
  rw [hrr]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte]

/-- **The general `syscall … true` of a trapped thread, where
`fastpath.fault` runs after `budget_ok`.** -/
theorem syscall_trap_fast {s s1 s2 s' : S} {a a2 a' : A} {t nx i1 : U64} {n : I64}
    (et : sched.cur_thread st s = ok t) (enx : obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1)
    (ef : obj.Tcb.flags st t s1 = ok i1)
    (c1 : (i1 &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true)
    (eb : syscall.budget_ok st ar s1 a = ok (true, s2, a2))
    (et2 : sched.cur_thread st s2 = ok t)
    (hf : fastpath.fault st ar s2 a2 t (IScalar.hcast .U64 n) = ok (true, s', a')) :
    syscall.syscall st ar s a n true = ok (true, s', a') := by
  unfold syscall.syscall
  rw [et]; simp only [bind_ok]
  rw [enx]; simp only [lift, bind_ok]
  rw [es1]; simp only [bind_ok]
  rw [ef]; simp only [lift, bind_ok, if_pos c1]
  unfold syscall.unknown_syscall_fault
  rw [eb]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte]
  rw [et2]; simp only [bind_ok, ↓reduceIte]
  rw [hf]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte]

/-- **`syscall_local_same`: the syscall entry beside the serial gate, where it
ran, is the general entry** `syscall.handle_syscall` (module docstring), given
the placement facts at the entry state that `local_prefix_keep` reads and
fl4-sync's contract on `found` (asked only where the ReplyRecv arm runs: the
current thread's flags word at entry has `TRAP_SYSCALLS` clear and the number
is `SysReplyRecv`). -/
theorem syscall_local_same (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s s' : S} {a a' : A} {n : I64}
    {found : U64 × U64}
    {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hfd : ∀ t f, sched.cur_thread st s = ok t → obj.Tcb.flags st t s = ok f →
      (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 → n = fl4_abi.syscall.SysReplyRecv →
      fastpath.reply_caps st s t = ok (some found))
    (h : syscall.handle_syscall_local st ar s a n found = ok (true, s', a')) :
    syscall.handle_syscall st ar s a n = ok (s', a') := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  have hT : TcbPlaced T := hSQ.tcbs
  have hcC : L.cpu s ∈ Cs := hSQ.cur
  have hN : NodePlaced st T s (L.cpu s) := hSQ.nodes _ hcC
  have hcT : L.curW s ∈ T := hSQ.curT
  obtain ⟨rptr, ep⟩ := found
  unfold syscall.handle_syscall_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  try simp only [lift, bind_ok] at h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  have htT : t ∈ T := by
    rw [cur_thread_ok] at et; rw [← ok_inj_ff et]; exact hcT
  have ht' := hT t htT
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · -- the trap arm: `fastpath.fault`
    rw [if_pos c1] at h
    obtain ⟨nx, enx, h⟩ := bind_eq_ok h
    obtain ⟨s1, es1, h⟩ := bind_eq_ok h
    obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
    obtain ⟨c, ec, h⟩ := bind_eq_ok h
    obtain ⟨b, eb, h⟩ := bind_eq_ok h
    cases b
    · simp at h
    simp only [↓reduceIte, if_pos c1] at h
    try simp only [lift, bind_ok] at h
    have hb : syscall.budget_ok st ar s1 a = ok (true, s2, a1) := by
      unfold syscall.budget_ok
      rw [eu]; simp only [bind_ok, uncurry_apply_pair]
      exact check_budget_restart_suf ar ecsc ec eb
    have et2 := (local_prefix_keep ar hT hN hcC et htT (hCn t et) es1 hb hA).1
    have ef : obj.Tcb.flags st t s1 = ok i := by
      rw [set_fip_wr ht' es1, flags_fip ht', ei]
    have hs := syscall_trap_fast ar et enx es1 ef c1 hb et2 h
    unfold syscall.handle_syscall
    rw [hs]; simp only [bind_ok, uncurry_apply_pair]
  · -- the ReplyRecv arm: `fastpath.reply_recv_found` with `found`
    rw [if_neg c1] at h
    by_cases c2 : (n != fl4_abi.syscall.SysReplyRecv) = true
    · rw [if_pos c2] at h; simp at h
    rw [if_neg c2] at h
    have hn : n = fl4_abi.syscall.SysReplyRecv := by simpa only [bne_iff_ne, ne_eq, not_not] using c2
    obtain ⟨nx, enx, h⟩ := bind_eq_ok h
    obtain ⟨s1, es1, h⟩ := bind_eq_ok h
    obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
    obtain ⟨c, ec, h⟩ := bind_eq_ok h
    obtain ⟨b, eb, h⟩ := bind_eq_ok h
    cases b
    · simp at h
    simp only [↓reduceIte, if_neg c1] at h
    try dsimp only at h
    have hb : syscall.budget_ok st ar s1 a = ok (true, s2, a1) := by
      unfold syscall.budget_ok
      rw [eu]; simp only [bind_ok, uncurry_apply_pair]
      exact check_budget_restart_suf ar ecsc ec eb
    have hi0 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 := by
      simpa only [bne_iff_ne, ne_eq, not_not] using c1
    obtain ⟨et2, hrcK⟩ := local_prefix_keep ar hT hN hcC et htT (hCn t et) es1 hb hA
    have hrc := hrcK rptr ep (hfd t i et ei hi0 hn)
    have hrr : fastpath.reply_recv st ar s2 a1 = ok (true, s', a') := by
      unfold fastpath.reply_recv
      rw [et2]; simp only [bind_ok]
      rw [hrc]; simp only [bind_ok]
      exact h
    have ef : obj.Tcb.flags st t s1 = ok i := by
      rw [set_fip_wr ht' es1, flags_fip ht', ei]
    subst hn
    have hs := syscall_rr_fast ar et enx es1 ef c1 hb hrr
    unfold syscall.handle_syscall
    rw [hs]; simp only [bind_ok, uncurry_apply_pair]

/-- **The syscall local entry where it ran: the general entry's
postconditions** (on the `true` results). -/
theorem syscall_local_triple (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s : S} {a : A} {n : I64}
    {found : U64 × U64} {P : S × A → Prop}
    {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hfd : ∀ t f, sched.cur_thread st s = ok t → obj.Tcb.flags st t s = ok f →
      (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 → n = fl4_abi.syscall.SysReplyRecv →
      fastpath.reply_caps st s t = ok (some found))
    (hG : syscall.handle_syscall st ar s a n ⦃ P ⦄) :
    syscall.handle_syscall_local st ar s a n found ⦃ r => r.1 = true → P (r.2.1, r.2.2) ⦄ := by
  obtain ⟨⟨b, s', a'⟩, e, -⟩ := spec_ex_fd (P0.syscall.handle_syscall_local.p0 st ar s a n found L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := syscall_local_same ar hA hI hCn hfd e
  rw [hs, WP.spec_ok] at hG
  exact hG

/-- **A trapped-or-out-of-range entry asks nothing of `found`**: where the
flags word after the `FAULT_IP` write has `TRAP_SYSCALLS` set (or the number
is outside the native range), fl4-sync's `found` contract holds vacuously. -/
theorem found_vacuous {T Cs Sg : Set U64} {s : S} {n : I64} {found : U64 × U64}
    {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hU : n < fl4_abi.syscall.SYSCALL_MIN ∨ n > fl4_abi.syscall.SYSCALL_MAX ∨
      ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
        ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) ≠ 0#u64 ⦄) :
    ∀ t f, sched.cur_thread st s = ok t → obj.Tcb.flags st t s = ok f →
      (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 → n = fl4_abi.syscall.SysReplyRecv →
      fastpath.reply_caps st s t = ok (some found) := by
  intro t f et ef hf hn
  exfalso
  subst hn
  rcases hU with hU | hU | hU
  · revert hU
    unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SYSCALL_MIN
    first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
  · revert hU
    unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SYSCALL_MAX
    first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
  · obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
    have htT : t ∈ T := by
      have et' := et
      rw [cur_thread_ok] at et'; rw [← ok_inj_ff et']; exact hSQ.curT
    have h1 := hU t 0#u64 et
    rw [flags_fip (hSQ.tcbs t htT), ef, WP.spec_ok] at h1
    exact h1 hf

end

end Fl4Proofs.P1
