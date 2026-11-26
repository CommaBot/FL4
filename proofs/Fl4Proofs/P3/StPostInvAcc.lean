/-
P3 (line stpost, generations 8–9): **an accepted frame-cap invocation's dispatch-state facts**
(`P1.inv_local_acc`; the P1 side of StPostInvTop's route).

fl4-sync's plan `localinv.plan s n = some p` decides from the invoked cap and the label
(`localinv.plan_with`): a CNode Copy / Mint / Delete runs only on a `CNode` cap, an `X86PageMap`
only on a small, non-device, non-EPT frame cap (read once, `Plan.read_cap`, from a fresh plan:
the words read are the slot's cap words). So:

* `P1.InvLocCap st s lbl sl`: the label is one of the four local labels, a CNode label goes with
  a `CNode` cap in `sl`, the page-map label with a small RAM frame cap (non-EPT).
* `P1.read_cap_new`: `Plan.read_cap` from a plan that has read nothing yet reads the slot's cap
  (`obj.Slot.cap`).
* `P1.plan_with_cap`: `plan_with … lbl slot extra = some p → InvLocCap st s lbl slot`.
* `P1.plan_fieldsW`: `plan_fields` with the `plan_with` call it ends in.
* **`P1.inv_local_acc`**: an accepted `handle_invocation_local … n p` has number `SysCall`, and
  at the general entry's dispatch state (after its `FAULT_IP` write and passing `budget_ok`) the
  current thread is unchanged, the `CAP` lookup finds the plan's slot, and with the message info
  there `InvLocCap` holds (the message-info register and the slot's cap words survive the
  prefix: `reg_keepK`, `found_cap_keep`); at `CNodeDelete` (gen 9) `InvDelDest` holds there.
  `inv_local_same`'s walk, stopped at the budget check.
* (gen 9) `P1.InvDelDest st s t sl`: with the first two message registers (any buffer: they are
  registers, `sarg0_reg` / `sarg1_reg`), the cap in `sl` resolves a target slot holding a small RAM
  frame cap. `P1.plan_with_del`: the plan at `CNodeDelete` gives it at the entry state (the target cap
  read first from a fresh plan, `read_cap_new`; `small_ram_frame`). `P1.target_keep`: the target
  lookup from the cap the `CAP` lookup found, and the target's cap, survive a write that misses the
  cap-slot words the walks reach (`CnOff`'s closure: the invoked CNode is reached from the root,
  `rab_loop_slot`, `rab_loop_congr2`).

No premise added (the placement facts `BXI` / `CnOff` are those of `inv_local_same`).
-/
import Fl4Proofs.P1.LocalInv
import Fl4Proofs.P1.LocalTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- (stpost) **The cap a local label runs on** (module docstring). -/
def InvLocCap (st : machine.Store S) (s : S) (lbl : U64) (sl : obj.Slot) : Prop :=
  (lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeDelete ∨
    lbl = fl4_abi.label.X86PageMap) ∧
  (lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeDelete →
    ∃ p r gs g, obj.Slot.cap st sl s = ok (.CNode p r gs g)) ∧
  (lbl = fl4_abi.label.X86PageMap → ∃ fp rt m asid va,
    obj.Slot.cap st sl s = ok (.Frame fp .Small rt false m false asid va))

theorem lbl_mint_ne_copy : fl4_abi.label.CNodeMint ≠ fl4_abi.label.CNodeCopy := by
  unfold fl4_abi.label.CNodeMint fl4_abi.label.CNodeCopy; decide
theorem lbl_del_ne_copy : fl4_abi.label.CNodeDelete ≠ fl4_abi.label.CNodeCopy := by
  unfold fl4_abi.label.CNodeDelete fl4_abi.label.CNodeCopy; decide
theorem lbl_del_ne_mint : fl4_abi.label.CNodeDelete ≠ fl4_abi.label.CNodeMint := by
  unfold fl4_abi.label.CNodeDelete fl4_abi.label.CNodeMint; decide
theorem lbl_map_ne_copy : fl4_abi.label.X86PageMap ≠ fl4_abi.label.CNodeCopy := by
  unfold fl4_abi.label.X86PageMap fl4_abi.label.CNodeCopy; decide
theorem lbl_map_ne_mint : fl4_abi.label.X86PageMap ≠ fl4_abi.label.CNodeMint := by
  unfold fl4_abi.label.X86PageMap fl4_abi.label.CNodeMint; decide
theorem lbl_map_ne_del : fl4_abi.label.X86PageMap ≠ fl4_abi.label.CNodeDelete := by
  unfold fl4_abi.label.X86PageMap fl4_abi.label.CNodeDelete; decide

/-- (stpost) `Plan.read_cap` from a plan that has read nothing yet reads the slot's cap. -/
theorem read_cap_new {q : localinv.Plan} {s : S} {sl : obj.Slot} {x : capability.Cap × localinv.Plan}
    (hq : q.nseen = 0#usize) (h : localinv.Plan.read_cap st q s sl = ok x) :
    obj.Slot.cap st sl s = ok x.1 := by
  unfold localinv.Plan.read_cap at h
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  obtain ⟨⟨w0, q1⟩, e1, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  obtain ⟨⟨w1, q2⟩, e2, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨c, ec, h⟩ := bind_eq_ok h
  have e := ok_inj_ff h
  subst e
  simp only [lift, ok.injEq] at ei ei1
  have hM : localinv.MAX_LOCKS.val = 4 := by unfold localinv.MAX_LOCKS; rfl
  unfold localinv.Plan.read at e1
  have nlt0 : ¬ (q.nseen >= localinv.MAX_LOCKS) := by
    show ¬ (localinv.MAX_LOCKS ≤ q.nseen)
    intro hc; have h2 : localinv.MAX_LOCKS.val ≤ q.nseen.val := hc; rw [hM, hq] at h2; simp at h2
  rw [if_neg nlt0] at e1
  obtain ⟨v0, ev0, e1⟩ := bind_eq_ok e1
  obtain ⟨a0, -, e1⟩ := bind_eq_ok e1
  obtain ⟨n0, en0, e1⟩ := bind_eq_ok e1
  have e1' := ok_inj_ff e1
  simp only [Prod.mk.injEq] at e1'
  obtain ⟨rfl, rfl⟩ := e1'
  have hn1 : n0.val = 1 := by
    obtain ⟨z, hze, hzv⟩ := spec_ex_fd (Usize.add_spec (x := 0#usize) (y := 1#usize) (by scalar_tac))
    rw [hq, hze] at en0
    rw [← ok_inj_ff en0, hzv]; simp
  unfold localinv.Plan.read at e2
  have nlt1 : ¬ (n0 >= localinv.MAX_LOCKS) := by
    show ¬ (localinv.MAX_LOCKS ≤ n0)
    intro hc; have h2 : localinv.MAX_LOCKS.val ≤ n0.val := hc; rw [hM, hn1] at h2; simp at h2
  rw [if_neg nlt1] at e2
  obtain ⟨v1, ev1, e2⟩ := bind_eq_ok e2
  obtain ⟨a1, -, e2⟩ := bind_eq_ok e2
  obtain ⟨n1, -, e2⟩ := bind_eq_ok e2
  have e2' := ok_inj_ff e2
  simp only [Prod.mk.injEq] at e2'
  obtain ⟨rfl, rfl⟩ := e2'
  rw [L.read_eq] at ev0 ev1
  have h0 : i = sl := by
    rw [← ei]; apply UScalar.eq_of_val_eq
    rw [core.num.U64.wrapping_add_val_eq]; simp only [layout.cte.CAP0.val_eq, Nat.add_zero]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  have h1 : i1 = core.num.U64.wrapping_add sl 8#u64 := by
    rw [← ei1]; apply UScalar.eq_of_val_eq
    rw [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_add_val_eq, layout.cte.CAP1.val_eq]; rfl
  subst h0 h1
  unfold obj.Slot.cap
  rw [L.read_pair_eq, ok_inj_ff ev0, ok_inj_ff ev1]
  simp only [bind_ok]
  exact ec

set_option maxHeartbeats 16000000 in
/-- (stpost) **What `plan_with` decides from the label and the cap** (module docstring). -/
theorem plan_with_cap {s : S} {t : obj.Tcb} {lbl : U64} {slot : obj.Slot} {extra : Array obj.Slot 3#usize}
    {p : localinv.Plan} (h : localinv.plan_with st s t lbl slot extra = ok (some p)) :
    InvLocCap st s lbl slot := by
  unfold localinv.plan_with at h
  obtain ⟨q, eq, h⟩ := bind_eq_ok h
  obtain ⟨cap, ecap, h⟩ := bind_eq_ok h
  have hq : q.nseen = 0#usize := by
    unfold localinv.Plan.new at eq; rw [← ok_inj_ff eq]
  by_cases c1 : lbl = fl4_abi.label.CNodeCopy
  · rw [if_pos c1] at h
    refine ⟨Or.inl c1, fun _ => ?_, fun e => absurd (e.symm.trans c1) lbl_map_ne_copy⟩
    obtain ⟨b, eb, h⟩ := bind_eq_ok h
    cases b
    · simp at h
    rw [ecap]
    cases cap <;> simp at eb ⊢
  rw [if_neg c1] at h
  by_cases c2 : lbl = fl4_abi.label.CNodeMint
  · rw [if_pos c2] at h
    refine ⟨Or.inr (Or.inl c2), fun _ => ?_, fun e => absurd (e.symm.trans c2) lbl_map_ne_mint⟩
    obtain ⟨b, eb, h⟩ := bind_eq_ok h
    cases b
    · simp at h
    rw [ecap]
    cases cap <;> simp at eb ⊢
  rw [if_neg c2] at h
  by_cases c3 : lbl = fl4_abi.label.CNodeDelete
  · rw [if_pos c3] at h
    refine ⟨Or.inr (Or.inr (Or.inl c3)), fun _ => ?_, fun e => absurd (e.symm.trans c3) lbl_map_ne_del⟩
    obtain ⟨b, eb, h⟩ := bind_eq_ok h
    cases b
    · simp at h
    rw [ecap]
    cases cap <;> simp at eb ⊢
  rw [if_neg c3] at h
  unfold localinv.is_page_map at h
  simp only [bind_ok] at h
  by_cases c4 : lbl = fl4_abi.label.X86PageMap
  swap
  · simp only [c4, decide_false, Bool.false_eq_true, ↓reduceIte] at h; simp at h
  simp only [c4, decide_true, ↓reduceIte] at h
  refine ⟨Or.inr (Or.inr (Or.inr c4)), fun hc => ?_, fun _ => ?_⟩
  · rcases hc with e | e | e
    · exact absurd (c4.symm.trans e) lbl_map_ne_copy
    · exact absurd (c4.symm.trans e) lbl_map_ne_mint
    · exact absurd (c4.symm.trans e) lbl_map_ne_del
  obtain ⟨⟨frame, q1⟩, ef, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  have hfr := read_cap_new hq ef
  simp only at hfr
  obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  rw [hfr]
  unfold localinv.small_ram_frame at eb1
  cases frame with
  | Frame fp fs rt d m ep asid va =>
    cases fs <;> cases d <;> cases ep <;> simp at eb1
    exact ⟨fp, rt, m, asid, va, rfl⟩
  | _ => simp at eb1

/-- (stpost) **`plan_fields` with the `plan_with` call it ends in.** -/
theorem plan_fieldsW {s : S} {n : I64} {p : localinv.Plan} (h : localinv.plan st s n = ok (some p)) :
    ∃ t info cptr r buf e, sched.cur_thread st s = ok t ∧ msg.msg_info st s t = ok info ∧
      obj.Tcb.reg st t s layout.reg.CAP = ok cptr ∧
      cspace.lookup_slot st s t cptr = ok (core.result.Result.Ok r) ∧
      msg.lookup_ipc_buffer st s false t = ok buf ∧
      ipc.lookup_extra_caps st s t buf info = ok (core.result.Result.Ok e) ∧
      localinv.plan_with st s t info.label r.slot e = ok (some p) := by
  unfold localinv.plan at h
  split at h
  · simp at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨info, ei, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  split at h
  swap
  · simp at h
  obtain ⟨cptr, ec, h⟩ := bind_eq_ok h
  obtain ⟨r, er, h⟩ := bind_eq_ok h
  cases r with
  | Err _ => simp at h
  | Ok r1 =>
    try simp only at h
    obtain ⟨buf, eb, h⟩ := bind_eq_ok h
    obtain ⟨r2, er2, h⟩ := bind_eq_ok h
    cases r2 with
    | Err _ => simp at h
    | Ok e =>
      try simp only at h
      exact ⟨t, info, cptr, r1, buf, e, et, ei, ec, er, eb, er2, h⟩

/-- (stpost) **The plan's delete target at a state**: with the message registers' first two words as
the decode reads them (any buffer), the slot's cap resolves a target slot holding a small RAM frame
cap (non-EPT). -/
def InvDelDest (st : machine.Store S) (s : S) (t : U64) (sl : obj.Slot) : Prop :=
  ∀ buf y0 y1, msg.syscall_arg st s t buf 0#u64 = ok y0 → msg.syscall_arg st s t buf 1#u64 = ok y1 →
    ∃ c dest, obj.Slot.cap st sl s = ok c ∧ cspace.lookup_target_slot st s c y0 y1 = ok (.Ok dest) ∧
      ∃ fp rt m asid va, obj.Slot.cap st dest s = ok (.Frame fp .Small rt false m false asid va)

theorem sarg0_reg (s : S) (t buf : U64) :
    msg.syscall_arg st s t buf 0#u64 = obj.Tcb.reg st t s layout.reg.R10 := by
  unfold msg.syscall_arg
  rw [if_pos (by simp [msg.N_MSG_REGISTERS])]
  simp [msg.msg_register]

theorem sarg1_reg (s : S) (t buf : U64) :
    msg.syscall_arg st s t buf 1#u64 = obj.Tcb.reg st t s layout.reg.R8 := by
  unfold msg.syscall_arg
  rw [if_pos (by simp [msg.N_MSG_REGISTERS])]
  simp [msg.msg_register]

set_option maxHeartbeats 16000000 in
/-- (stpost) **What `plan_with` decides at `CNodeDelete`**: the target slot the first two message
registers name holds a small RAM frame cap. -/
theorem plan_with_del {s : S} {t : obj.Tcb} {slot : obj.Slot} {extra : Array obj.Slot 3#usize}
    {p : localinv.Plan} (h : localinv.plan_with st s t fl4_abi.label.CNodeDelete slot extra = ok (some p)) :
    ∃ c i i1 dest, obj.Slot.cap st slot s = ok c ∧ localinv.reg_arg st s t 0#u64 = ok i ∧
      localinv.reg_arg st s t 1#u64 = ok i1 ∧ cspace.lookup_target_slot st s c i i1 = ok (.Ok dest) ∧
      ∃ fp rt m asid va, obj.Slot.cap st dest s = ok (.Frame fp .Small rt false m false asid va) := by
  unfold localinv.plan_with at h
  obtain ⟨q, eq, h⟩ := bind_eq_ok h
  obtain ⟨cap, ecap, h⟩ := bind_eq_ok h
  have hq : q.nseen = 0#usize := by
    unfold localinv.Plan.new at eq; rw [← ok_inj_ff eq]
  rw [if_neg lbl_del_ne_copy, if_neg lbl_del_ne_mint, if_pos rfl] at h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  obtain ⟨r, er, h⟩ := bind_eq_ok h
  obtain ⟨o, eo, h⟩ := bind_eq_ok h
  obtain ⟨cf, ecf, h⟩ := bind_eq_ok h
  cases r with
  | Err e =>
    simp only [core.result.Result.ok] at eo
    cases ok_inj_ff eo
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch] at ecf
    cases ok_inj_ff ecf
    simp [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual] at h
  | Ok dest =>
    simp only [core.result.Result.ok] at eo
    cases ok_inj_ff eo
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch] at ecf
    cases ok_inj_ff ecf
    try simp only at h
    obtain ⟨⟨c, q1⟩, ec, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    have hc := read_cap_new hq ec
    simp only at hc
    refine ⟨cap, i, i1, dest, ecap, ei, ei1, er, ?_⟩
    obtain ⟨i2, -, h⟩ := bind_eq_ok h
    obtain ⟨⟨i3, q2⟩, -, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    obtain ⟨i4, -, h⟩ := bind_eq_ok h
    obtain ⟨⟨i5, q3⟩, -, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    obtain ⟨nx, -, h⟩ := bind_eq_ok h
    obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
    cases b1
    · simp at h
    rw [hc]
    unfold localinv.small_ram_frame at eb1
    cases c with
    | Frame fp fs rt d m ep asid va =>
      cases fs <;> cases d <;> cases ep <;> simp at eb1
      exact ⟨fp, rt, m, asid, va, rfl⟩
    | _ => simp at eb1

/-- (stpost) **`lookup_target_slot` from the cap a `CAP` lookup found, across a write that misses `t`'s
root slot and the cap-slot words the walks reach** (`CnOff`): the same target, its cap kept. -/
theorem target_keep {T Cs Sg : Set U64} {s s' : S} {t c : U64} {r : cspace.Resolved} {cn : capability.Cap}
    {y0 y1 : U64} {dest : obj.Slot}
    (hCn : CnOff (L := L) T Cs Sg s t)
    (oK : ∀ b, OutsideObjs st T Cs s b → L.mem s' b = L.mem s b)
    (h : cspace.lookup_slot st s t c = ok (core.result.Result.Ok r)) (hc : obj.Slot.cap st r.slot s = ok cn)
    (hl : cspace.lookup_target_slot st s cn y0 y1 = ok (.Ok dest)) :
    cspace.lookup_target_slot st s' cn y0 y1 = ok (.Ok dest) ∧
      obj.Slot.cap st dest s' = obj.Slot.cap st dest s := by
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
  have hCn' : ∀ p1 r1 gs1 g1, cn = .CNode p1 r1 gs1 g1 → C p1 r1 := by
    rintro p1 r1 gs1 g1 rfl
    rw [hs] at hc
    exact hcl p r' m y p1 r1 gs1 g1 hp hm hc
  cases cn with
  | CNode p1 r1 gs1 g1 =>
    unfold cspace.lookup_target_slot cspace.lookup_slot_for_cnode_op at hl ⊢
    simp only [bind_ok, ↓reduceIte] at hl ⊢
    by_cases d1 : y1 < 1#u64
    · rw [if_pos d1] at hl; simp at hl
    rw [if_neg d1] at hl ⊢
    by_cases d2 : y1 > cspace.WORD_BITS
    · rw [if_pos d2] at hl; simp at hl
    rw [if_neg d2] at hl ⊢
    unfold cspace.resolve_address_bits at hl ⊢
    obtain ⟨res, eres, hl⟩ := bind_eq_ok hl
    have eres' := rab_loop_congr2 st C slotK hcl 66 _ _ 65#u64 res (by simp) hCn' eres
    rw [eres']; simp only [bind_ok]
    refine ⟨hl, ?_⟩
    cases res with
    | Err lf => simp at hl
    | Ok r2 =>
      simp only at hl
      by_cases hb : (r2.bits_left != 0#u64) = true
      · rw [if_pos hb] at hl; simp at hl
      rw [if_neg hb] at hl
      have e := ok_inj_ff hl
      simp only [core.result.Result.Ok.injEq] at e
      subst e
      obtain ⟨p2, r3, m2, y2, hp2, hm2, hs2⟩ := rab_loop_slot st C hcl 66 _ _ 65#u64 r2 (by simp) hCn' eres
      rw [hs2]; exact slotK p2 r3 hp2 m2 hm2 y2
  | _ =>
    unfold cspace.lookup_target_slot cspace.lookup_slot_for_cnode_op at hl
    simp at hl

end

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

set_option maxHeartbeats 16000000 in
/-- (stpost) **An accepted frame-cap invocation beside the gate: its number, and the cap and label
at its dispatch state** (module docstring; `inv_local_same`'s walk). -/
theorem inv_local_acc (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s s' : S} {a a' : A} {n : I64}
    {p : localinv.Plan}
    {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hp : localinv.plan st s n = ok (some p))
    (h : syscall.handle_invocation_local st ar s a n p = ok (true, s', a')) :
    n = fl4_abi.syscall.SysCall ∧
    ∀ ct nx s2 a2, sched.cur_thread st s = ok ct → obj.Tcb.reg st ct s layout.reg.NEXT_IP = ok nx →
      syscall.budget_ok st ar (L.wr s (regA ct layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) a =
        ok (true, s2, a2) →
      sched.cur_thread st s2 = ok ct ∧ ∃ (found : cspace.Resolved) (info : msginfo.MessageInfo),
        cspace.lookup_slot st s2 ct (L.mem s2 (regA ct layout.reg.CAP)) = ok (.Ok found) ∧
        msg.msg_info st s2 ct = ok info ∧ InvLocCap st s2 info.label found.slot ∧
        msg.msg_info st s ct = ok info ∧
        (info.label = fl4_abi.label.CNodeDelete → InvDelDest st s2 ct found.slot) := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  have hT : TcbPlaced T := hSQ.tcbs
  have hcC : L.cpu s ∈ Cs := hSQ.cur
  have hN : NodePlaced st T s (L.cpu s) := hSQ.nodes _ hcC
  have hcT : L.curW s ∈ T := hSQ.curT
  obtain ⟨t0, info0, cptr0, r0, buf0, e0, et0, ei0, ec0, er0, -, -, hpw⟩ := plan_fieldsW hp
  have hLC := plan_with_cap hpw
  unfold syscall.handle_invocation_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  have htt : t0 = t := ok_inj_ff (et0.symm.trans et)
  subst htt
  obtain ⟨info, ei, h⟩ := bind_eq_ok h
  have hii : info0 = info := ok_inj_ff (ei0.symm.trans ei)
  subst hii
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  by_cases cn : (n != fl4_abi.syscall.SysCall) = true
  · rw [if_pos cn] at h; simp at h
  rw [if_neg cn] at h
  have hn : n = fl4_abi.syscall.SysCall := by
    by_contra hne; exact cn (bne_iff_ne.mpr hne)
  refine ⟨hn, fun ct nx0 s2g a2g hct hnx hb2 => ?_⟩
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨nx, enx, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨act, -, h⟩ := bind_eq_ok h
  by_cases c3 : (act != sched.ACTION_RESUME_CURRENT) = true
  · rw [if_pos c3] at h; simp at h
  rw [if_neg c3] at h
  obtain ⟨yt, -, h⟩ := bind_eq_ok h
  by_cases c4 : (yt != 0#u64) = true
  · rw [if_pos c4] at h; simp at h
  rw [if_neg c4] at h
  obtain ⟨c, ec, h⟩ := bind_eq_ok h
  obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  have htT : t0 ∈ T := by
    rw [cur_thread_ok] at et; rw [← ok_inj_ff et]; exact hcT
  have ht' := hT t0 htT
  obtain ⟨et2, tK, oK⟩ := inv_prefix ar hT hN hcC et htT es1 eu hA
  have hb : syscall.budget_ok st ar s1 a = ok (true, s2, a1) := by
    unfold syscall.budget_ok
    rw [eu]; simp only [bind_ok, uncurry_apply_pair]
    exact check_budget_restart_suf ar ecsc ec eb1
  -- the general prefix is this one
  have e1 : ct = t0 := ok_inj_ff (hct.symm.trans et)
  subst e1
  have e2 : nx0 = nx := ok_inj_ff (hnx.symm.trans enx)
  subst e2
  have hs1 : s1 = L.wr s (regA ct layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx0 2#u64) := by
    have hW1 := obj.Tcb.set_reg.wrK (L := L) s ct layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx0 2#u64)
      ht' (by simp [layout.reg.FAULT_IP])
    rw [es1, WP.spec_ok] at hW1
    obtain ⟨K, hK, e1⟩ := hW1
    obtain ⟨K', hK', eK'⟩ := regA_eq ht' (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    rw [e1, eK']; congr 2; apply UScalar.eq_of_val_eq; rw [hK, hK']
  rw [← hs1, hb] at hb2
  have e3 := ok_inj_ff hb2
  simp only [Prod.mk.injEq] at e3
  obtain ⟨-, rfl, rfl⟩ := e3
  -- the reads at the dispatch state
  have ei2 : msg.msg_info st s2 ct = ok info0 := by
    unfold msg.msg_info at ei ⊢
    rw [reg_keepK ht' (r := layout.reg.MSG_INFO) (by simp) (by simp) tK]; exact ei
  have ec2 : obj.Tcb.reg st ct s2 layout.reg.CAP = ok cptr0 := by
    rw [reg_keepK ht' (r := layout.reg.CAP) (by simp) (by simp) tK]; exact ec0
  rw [reg_ok] at ec2
  have ec2' := ok_inj_ff ec2
  have er2 := lookup_slot_keep ht' (hCn ct et) tK oK er0
  have hcap : ∀ c, obj.Slot.cap st r0.slot s = ok c → obj.Slot.cap st r0.slot s2 = ok c := fun c hc => by
    rw [found_cap_keep (hCn ct et) oK er0]; exact hc
  refine ⟨et2, r0, info0, by rw [ec2']; exact er2, ei2, ?_, ei, ?_⟩
  · obtain ⟨hl, hC, hF⟩ := hLC
    refine ⟨hl, fun hc => ?_, fun hm => ?_⟩
    · obtain ⟨p1, p2, p3, p4, e⟩ := hC hc; exact ⟨p1, p2, p3, p4, hcap _ e⟩
    · obtain ⟨p1, p2, p3, p4, p5, e⟩ := hF hm; exact ⟨p1, p2, p3, p4, p5, hcap _ e⟩
  · -- the delete target, read at the entry state, kept to the dispatch state
    intro hd
    rw [hd] at hpw
    obtain ⟨c, i, i1, dest, hc, ei0', ei1', hl, fr⟩ := plan_with_del hpw
    have hk := target_keep (hCn ct et) oK er0 hc hl
    intro buf y0 y1 e0 e1
    have r0e : msg.syscall_arg st s2 ct buf 0#u64 = localinv.reg_arg st s ct 0#u64 := by
      unfold localinv.reg_arg
      rw [sarg0_reg, sarg0_reg, reg_keepK ht' (r := layout.reg.R10) (by simp) (by simp) tK]
    have r1e : msg.syscall_arg st s2 ct buf 1#u64 = localinv.reg_arg st s ct 1#u64 := by
      unfold localinv.reg_arg
      rw [sarg1_reg, sarg1_reg, reg_keepK ht' (r := layout.reg.R8) (by simp) (by simp) tK]
    rw [r0e, ei0'] at e0
    rw [r1e, ei1'] at e1
    cases ok_inj_ff e0
    cases ok_inj_ff e1
    obtain ⟨fp, rt, m, asid, va, e⟩ := fr
    exact ⟨c, dest, hcap _ hc, hk.1, fp, rt, m, asid, va, by rw [hk.2]; exact e⟩

end

end Fl4Proofs.P1
