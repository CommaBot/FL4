/-
# The frame-cap invocation beside the serial gate, accepted (lcv)

`syscall.handle_invocation_local` (fl4-sync's `local_invocation`, with the
plan `localinv.plan` computed at the entry state) where it returns `true`:

* `plan_fields`: a plan `localinv.plan s n = some p` holds the slot the
  invoked cap's CSpace lookup finds and the extra caps' lookup
  (`plan_with` only records reads and locks: `PlanKP`, `plan_with_kp`);
* `inv_prefix`: the local entry's prefix (`FAULT_IP` write, `update_timestamp`)
  keeps the current thread, every word of the current TCB but `FAULT_IP`, and
  every word outside the TCBs and the nodes;
* lookup congruence per plan field across that prefix: `reg_keepK`
  (`MSG_INFO`, `CAP`), `lookup_slot_keep` (root slot words and `CnOff`'s
  cap-slot words), `lookup_buf_keep` (the sender's buffer lookup, TCB words),
  `lec_keep` (`lookup_extra_caps`: the buffer's extra-cap words, given the
  sender's `BufOK`, and the lookups);
* **`inv_local_same`**: an accepted `handle_invocation_local` ends where
  `syscall.handle_syscall` ends (the same `FAULT_IP` write and
  `update_timestamp`; `budget_ok` then passes without writing; `dispatch_syscall`
  reaches `handle_invocation`, whose lookups find the plan's slots, the same
  `decode_invocation` call and reply arms); `inv_local_triple`.
-/
import Fl4Proofs.P1.FastVmLocal
import Fl4Proofs.P1.FastFaultInv
import Fl4Proofs.P1.FastRRLk
import Fl4Proofs.P1.RabCongr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-! ## The plan's slot and extra caps -/

/-- A plan with the slot `sl` and the extra caps `ex`. -/
def PlanKP (sl : obj.Slot) (ex : Array obj.Slot 3#usize) (q : localinv.Plan) : Prop :=
  q.slot = sl ∧ q.extra = ex

section
variable {S : Type _} {st : machine.Store S}

theorem kp_new {sl : obj.Slot} {ex : Array obj.Slot 3#usize} {q : localinv.Plan} (h : localinv.Plan.new sl ex = ok q) : PlanKP sl ex q := by
  unfold localinv.Plan.new at h
  have e := ok_inj_ff h
  subst e
  exact ⟨rfl, rfl⟩

theorem kp_read {sl : obj.Slot} {ex : Array obj.Slot 3#usize} {q : localinv.Plan} {s : S} {ad : U64} {x : U64 × localinv.Plan}
    (h : localinv.Plan.read st q s ad = ok x) (hq : PlanKP sl ex q) : PlanKP sl ex x.2 := by
  unfold localinv.Plan.read at h
  split at h
  · have e := ok_inj_ff h; subst e; exact hq
  · obtain ⟨v, -, h⟩ := bind_eq_ok h
    obtain ⟨a1, -, h⟩ := bind_eq_ok h
    obtain ⟨i, -, h⟩ := bind_eq_ok h
    have e := ok_inj_ff h; subst e; exact hq

theorem kp_read_cap {sl : obj.Slot} {ex : Array obj.Slot 3#usize} {q : localinv.Plan} {s : S} {sl0 : obj.Slot} {x : capability.Cap × localinv.Plan}
    (h : localinv.Plan.read_cap st q s sl0 = ok x) (hq : PlanKP sl ex q) : PlanKP sl ex x.2 := by
  unfold localinv.Plan.read_cap at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  obtain ⟨⟨w0, q1⟩, e1, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨i1, -, h⟩ := bind_eq_ok h
  obtain ⟨⟨w1, q2⟩, e2, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨c, -, h⟩ := bind_eq_ok h
  have e := ok_inj_ff h
  subst e
  exact kp_read e2 (kp_read e1 hq)

theorem kp_add {sl : obj.Slot} {ex : Array obj.Slot 3#usize} {q : localinv.Plan} {ad : U64} {x : Bool × localinv.Plan}
    (h : localinv.Plan.add q ad = ok x) (hq : PlanKP sl ex q) : PlanKP sl ex x.2 := by
  unfold localinv.Plan.add at h
  split at h
  · have e := ok_inj_ff h; subst e; exact hq
  · split at h
    · have e := ok_inj_ff h; subst e; exact hq
    · obtain ⟨a1, -, h⟩ := bind_eq_ok h
      obtain ⟨i, -, h⟩ := bind_eq_ok h
      have e := ok_inj_ff h; subst e; exact hq

theorem kp_add_pte {sl : obj.Slot} {ex : Array obj.Slot 3#usize} {q : localinv.Plan} {ad : U64} {x : Bool × localinv.Plan}
    (h : localinv.Plan.add_pte q ad = ok x) (hq : PlanKP sl ex q) : PlanKP sl ex x.2 := by
  unfold localinv.Plan.add_pte at h
  exact kp_add h hq

theorem kp_some_if {sl : obj.Slot} {ex : Array obj.Slot 3#usize} {b : Bool} {q p : localinv.Plan}
    (h : localinv.some_if b q = ok (some p)) (hq : PlanKP sl ex q) : PlanKP sl ex p := by
  unfold localinv.some_if at h
  split at h
  · split at h
    · have e := ok_inj_ff h
      simp only [Option.some.injEq] at e
      subst e; exact hq
    · simp at h
  · simp at h

/-- One step of `plan_with_kp`'s walk: after a bind, record what the bound
call keeps of the plan. -/
local macro "kp_go" : tactic => `(tactic| repeat' (first
  | (intro h; exact kp_some_if h (by assumption))
  | (simp only [bind_tc_ok, bind_ok, bind_assoc_eq, Aeneas.Std.bind_assoc, Aeneas.Std.uncurry,
      Bool.false_eq_true, ↓reduceIte])
  | p0_cases_prod
  | (dsimp only)
  | (refine eq_ite_imp (fun _ => ?_) (fun _ => ?_))
  | split
  | (refine eq_bind_imp (fun x hx => ?_);
      (try have := kp_read hx (by assumption));
      (try have := kp_read_cap hx (by assumption));
      (try have := kp_add hx (by assumption));
      (try have := kp_add_pte hx (by assumption));
      (try have := kp_new hx))
  | (refine eq_bind_imp' (fun x hx => ?_);
      (try have := kp_read hx (by assumption));
      (try have := kp_read_cap hx (by assumption));
      (try have := kp_add hx (by assumption));
      (try have := kp_add_pte hx (by assumption));
      (try have := kp_new hx))
  | (intro h; simp [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual] at h; done)))

set_option maxHeartbeats 16000000 in
/-- **`plan_with` keeps the slot and the extra caps it was given**: every
plan it builds is `Plan.new slot extra` updated by `read` / `read_cap` / `add`
/ `add_pte`, which change only the recorded words and the locks. -/
theorem plan_with_kp {s : S} {t : obj.Tcb} {lbl : U64} {slot : obj.Slot} {extra : Array obj.Slot 3#usize}
    {p : localinv.Plan} (h : localinv.plan_with st s t lbl slot extra = ok (some p)) :
    PlanKP slot extra p := by
  unfold localinv.plan_with at h
  revert h
  kp_go

/-- **What a plan holds** (fl4-sync's `localinv::plan` at the entry state):
the slot the invoked cap's lookup finds and the extra caps'. -/
theorem plan_fields {s : S} {n : I64} {p : localinv.Plan} (h : localinv.plan st s n = ok (some p)) :
    ∃ t info cptr r buf e, sched.cur_thread st s = ok t ∧ msg.msg_info st s t = ok info ∧
      obj.Tcb.reg st t s layout.reg.CAP = ok cptr ∧
      cspace.lookup_slot st s t cptr = ok (core.result.Result.Ok r) ∧
      msg.lookup_ipc_buffer st s false t = ok buf ∧
      ipc.lookup_extra_caps st s t buf info = ok (core.result.Result.Ok e) ∧
      p.slot = r.slot ∧ p.extra = e := by
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
      obtain ⟨h1, h2⟩ := plan_with_kp h
      exact ⟨t, info, cptr, r1, buf, e, et, ei, ec, er, eb, er2, h1, h2⟩

end

/-! ## Read congruence across the prefix -/

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- **The local entry's prefix** (`FAULT_IP` write, `update_timestamp`): the
current thread kept, every word of its TCB but `FAULT_IP` (offset 392)
kept, every word outside the TCBs and nodes kept (pf1c's `rr_prefix_keep`'s
footprint). -/
theorem inv_prefix {T Cs : Set U64} {s s1 s2 : S} {a a2 : A} {t v : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcC : L.cpu s ∈ Cs)
    (et : sched.cur_thread st s = ok t) (htT : t ∈ T)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP v = ok s1)
    (hu : sched.update_timestamp st ar s1 a = ok (s2, a2)) (hA : P0.ArchTotal ar) :
    sched.cur_thread st s2 = ok t ∧
      (∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 392 →
        L.mem s2 (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K)) ∧
      (∀ b, OutsideObjs st T Cs s b → L.mem s2 b = L.mem s b) := by
  have ht' := hT t htT
  obtain ⟨hct, hcn, hne⟩ := ct_cn hN
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
  have hW : WritesIn st s (utW (L := L) s1 n)
      (fun b => b = core.num.U64.wrapping_add t KF ∨ b = ctA (L := L) s ∨ b = cnA (L := L) s) := by
    refine ⟨?_, ?_, fun b hb hn' => ?_⟩
    · unfold utW; rw [e1]; simp only [L.ksb_wr]
    · unfold utW; rw [e1]; simp only [LawfulStore.cpu_wr]
    · unfold utW
      rw [ec, en, mem_wr_ne' hcn hb (fun e => hn' (Or.inr (Or.inr e.symm))),
        mem_wr_ne' hct hb (fun e => hn' (Or.inr (Or.inl e.symm))), e1,
        mem_wr_ne' aF hb (fun e => hn' (Or.inl e.symm))]
  have vb := nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
  have vn := nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
  have nd := hN.disj t htT
  have tvF := tcb_wadd_val ht' (o := KF) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · have vC := nodeAt_val hN (off := layout.node.CUR_THREAD) (by simp [layout.node.CUR_THREAD])
    have aC : Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
      nodeAt_aligned hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
    have eC : L.nodeAt (utW (L := L) s1 n) (L.cpu (utW (L := L) s1 n)) layout.node.CUR_THREAD =
        L.nodeAt s (L.cpu s) layout.node.CUR_THREAD := by
      rw [hW.2.1, nodeAt_of_ksb hW.1]
    have hm : L.mem (utW (L := L) s1 n) (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) =
        L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) := by
      refine hW.mem_eq aC ?_
      rintro (e | e | e) <;> (have e' := congrArg UScalar.val e)
      · rw [vC, tvF] at e'; simp [layout.node.CUR_THREAD] at e'; omega
      · unfold ctA at e'; rw [vC, vb] at e'; simp [layout.node.CUR_THREAD, layout.node.CUR_TIME] at e'
      · unfold cnA at e'; rw [vC, vn] at e'; simp [layout.node.CUR_THREAD, layout.node.CONSUMED] at e'
    rw [cur_thread_ok] at et ⊢
    rw [← ok_inj_ff et]
    unfold LawfulStore.curW; rw [eC, hm]
  · intro K hK h8 hK392
    refine hW.mem_eq (field_aligned ht' hK h8) ?_
    have tvK := tcb_wadd_val ht' (o := K) hK
    rintro (e | e | e) <;> (have e' := congrArg UScalar.val e)
    · rw [tvK, tvF] at e'; omega
    · unfold ctA at e'; rw [vb, tvK] at e'; simp [layout.node.CUR_TIME] at e'; omega
    · unfold cnA at e'; rw [vn, tvK] at e'; simp [layout.node.CONSUMED] at e'; omega
  · rintro b ⟨hal, oT, oN⟩
    refine hW.mem_eq hal ?_
    have bt := oT t htT
    have bn := oN _ hcC
    rintro (e | e | e) <;> (have e' := congrArg UScalar.val e)
    · rw [tvF] at e'; omega
    · unfold ctA at e'; rw [vb] at e'; simp [layout.node.CUR_TIME] at e'; omega
    · unfold cnA at e'; rw [vn] at e'; simp [layout.node.CONSUMED] at e'; omega

/-- A register other than `FAULT_IP`, across `inv_prefix`. -/
theorem reg_keepK {s s2 : S} {t r : U64} (ht : TcbAddr t) (hr : r.val < 384) (hr' : r.val ≠ 17)
    (tK : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K)) :
    obj.Tcb.reg st t s2 r = obj.Tcb.reg st t s r := by
  obtain ⟨K, hK, eK⟩ := regA_eq ht hr
  rw [reg_ok, reg_ok, eK, tK K (by omega) (by omega) (by omega)]

/-- **`lookup_slot` across a write that misses `t`'s root slot and the
cap-slot words its walk reaches** (`CnOff`). -/
theorem lookup_slot_keep {T Cs Sg : Set U64} {s s' : S} {t c : U64} {r : cspace.Resolved}
    (ht' : TcbAddr t) (hCn : CnOff (L := L) T Cs Sg s t)
    (tK : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 392 →
      L.mem s' (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K))
    (oK : ∀ b, OutsideObjs st T Cs s b → L.mem s' b = L.mem s b)
    (h : cspace.lookup_slot st s t c = ok (core.result.Result.Ok r)) :
    cspace.lookup_slot st s' t c = ok (core.result.Result.Ok r) := by
  unfold cspace.lookup_slot at h ⊢
  obtain ⟨sl, hsl, h⟩ := bind_eq_ok h
  obtain ⟨root, hroot, h⟩ := bind_eq_ok h
  obtain ⟨C, hC0, hcl, hWc⟩ := hCn sl root hsl hroot
  have slotK : ∀ p r, C p r → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) s' = obj.Slot.cap st (cnSlot p (x &&& m)) s := by
    intro p r hp m hm x
    obtain ⟨h1, h2⟩ := hWc p r m x hp hm
    unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, oK _ h1.1, oK _ h2.1]
  have esl : sl = core.num.U64.wrapping_add t (core.num.U64.wrapping_mul layout.tcb.SLOT_CTABLE layout.cte.SIZE) := by
    simp only [obj.Tcb.slot, lift, bind_ok] at hsl; exact (ok_inj_ff hsl).symm
  have tf := ht'.fits
  have vsl : sl.val = t.val := by
    rw [esl]; simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    all_goals omega
  have e0 : sl = core.num.U64.wrapping_add t 0#u64 := by
    apply UScalar.eq_of_val_eq; rw [vsl, tcb_wadd_val ht' (by decide)]; simp
  have e8 : core.num.U64.wrapping_add sl 8#u64 = core.num.U64.wrapping_add t 8#u64 := by
    apply UScalar.eq_of_val_eq; rw [tcb_wadd_val ht' (by decide)]
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, vsl]; omega
  have hroot' : obj.Slot.cap st sl s' = ok root := by
    rw [← hroot]; unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, e8, e0,
      tK 0#u64 (by decide) (by decide) (by decide), tK 8#u64 (by decide) (by decide) (by decide)]
  rw [hsl]; simp only [bind_ok]
  rw [hroot']; simp only [bind_ok]
  exact rab_loop_congr2 st C slotK hcl 66 root _ 65#u64 _ (by simp) hC0 h

/-- **`lookup_ipc_buffer` across a write that misses the TCB's buffer
words** (either receiver flag). -/
theorem lookup_buf_keep {s s' : S} {t : U64} (ht' : TcbAddr t) (b : Bool)
    (tK : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 392 →
      L.mem s' (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K)) :
    msg.lookup_ipc_buffer st s' b t = msg.lookup_ipc_buffer st s b t := by
  have tf := ht'.fits
  have e64 : sbA t = core.num.U64.wrapping_add t 64#u64 := by
    apply UScalar.eq_of_val_eq; rw [sbA_val ht', tcb_wadd_val ht' (by decide)]; simp
  have e72 : core.num.U64.wrapping_add (sbA t) 8#u64 = core.num.U64.wrapping_add t 72#u64 := by
    apply UScalar.eq_of_val_eq; rw [tcb_wadd_val ht' (by decide)]
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, sbA_val ht']; omega
  refine lookup_buf_agreeB b ?_ ?_ ?_
  · unfold ibA; exact tK 3512#u64 (by decide) (by decide) (by decide)
  · rw [e64]; exact tK 64#u64 (by decide) (by decide) (by decide)
  · rw [e72]; exact tK 72#u64 (by decide) (by decide) (by decide)

theorem buf_get_ok (s : S) (w i : U64) :
    msg.buf_get st s w i = ok (L.mem s (core.num.U64.wrapping_add w (core.num.U64.wrapping_mul i 8#u64))) := by
  unfold msg.buf_get; simp only [lift, bind_ok, L.read_eq]

/-- `lookup_extra_caps_loop` unfolded once. -/
theorem lecLoop_unfold (s : S) (t : obj.Tcb) (buf : U64) (caps : Array obj.Slot 3#usize) (n i : U64) :
    ipc.lookup_extra_caps_loop st s t buf caps n i =
      (do
        let r ← ipc.lookup_extra_caps_loop.body st s t buf n caps i
        match r with
        | ControlFlow.cont x => ipc.lookup_extra_caps_loop st s t buf x.1 n x.2
        | ControlFlow.done z => ok z) := by
  conv_lhs => unfold ipc.lookup_extra_caps_loop; rw [loop]
  congr 1
  funext r
  cases r with
  | cont x => obtain ⟨a, b⟩ := x; rfl
  | done z => rfl

/-- The loop body reads the buffer's extra-cap word `i` and looks it up. -/
theorem lec_body_keep {s s' : S} {t : obj.Tcb} {buf n i : U64} {caps : Array obj.Slot 3#usize}
    {y : ControlFlow (Array obj.Slot 3#usize × U64) (core.result.Result (Array obj.Slot 3#usize) error.Fault)}
    (hb : ∀ k : U64, k.val < 128 →
      L.mem s' (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul k 8#u64)) =
        L.mem s (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul k 8#u64)))
    (hls : ∀ c r, cspace.lookup_slot st s t c = ok (core.result.Result.Ok r) →
      cspace.lookup_slot st s' t c = ok (core.result.Result.Ok r))
    (hy : ipc.lookup_extra_caps_loop.body st s t buf n caps i = ok y)
    (hne : ∀ f, y ≠ ControlFlow.done (core.result.Result.Err f)) :
    ipc.lookup_extra_caps_loop.body st s' t buf n caps i = ok y ∧
      ∀ x, y = ControlFlow.cont x → i.val < 3 ∧ x.2.val = i.val + 1 := by
  unfold ipc.lookup_extra_caps_loop.body at hy ⊢
  by_cases c1 : i < n
  · rw [if_pos c1] at hy ⊢
    by_cases c2 : i < 3#u64
    · rw [if_pos c2] at hy ⊢
      have hi3 : i.val < 3 := by scalar_tac
      obtain ⟨i1, e1, hy⟩ := bind_eq_ok hy
      obtain ⟨i2, e2, hy⟩ := bind_eq_ok hy
      obtain ⟨cp, e3, hy⟩ := bind_eq_ok hy
      obtain ⟨r, er, hy⟩ := bind_eq_ok hy
      have hi1 : i1 = 122#u64 := by
        have h0 := msg.BUF_CAPS.spec; rw [e1, WP.spec_ok] at h0; exact h0
      subst hi1
      have e2' : ok (core.num.U64.wrapping_add 122#u64 i) = (ok i2 : Result U64) := e2
      have hi2v : i2 = core.num.U64.wrapping_add 122#u64 i := (ok_inj_ff e2').symm
      have hi2 : i2.val < 128 := by
        rw [hi2v]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      rw [buf_get_ok] at e3
      rw [e1]; simp only [bind_ok]
      rw [e2]; simp only [bind_ok]
      rw [buf_get_ok, hb i2 hi2, e3]; simp only [bind_ok]
      cases r with
      | Err lf =>
        try dsimp only at hy
        exact absurd (ok_inj_ff hy).symm (hne _)
      | Ok r1 =>
        have hy0 := hy
        try dsimp only at hy
        obtain ⟨i3, -, hy2⟩ := bind_eq_ok hy
        obtain ⟨a', -, hy2⟩ := bind_eq_ok hy2
        obtain ⟨i4, e4, hy2⟩ := bind_eq_ok hy2
        refine ⟨?_, fun x hx => ?_⟩
        · rw [hls _ _ er, bind_ok]; exact hy0
        · subst hx
          have e := ok_inj_ff hy2
          injection e with e
          subst e
          refine ⟨hi3, ?_⟩
          show i4.val = i.val + 1
          obtain ⟨z, hz, hv⟩ := spec_ex_fd (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
          rw [hz] at e4
          have := ok_inj_ff e4
          subst this
          simp at hv; omega
    · rw [if_neg c2] at hy ⊢
      refine ⟨hy, fun x hx => ?_⟩
      subst hx; simp at hy
  · rw [if_neg c1] at hy ⊢
    refine ⟨hy, fun x hx => ?_⟩
    subst hx; simp at hy

/-- **`lookup_extra_caps_loop` read congruence** (induction on the words
left): a successful run at `s` is the same run at `s'`. -/
theorem lec_loop_keep {s s' : S} {t : obj.Tcb} {buf n : U64}
    (hb : ∀ k : U64, k.val < 128 →
      L.mem s' (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul k 8#u64)) =
        L.mem s (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul k 8#u64)))
    (hls : ∀ c r, cspace.lookup_slot st s t c = ok (core.result.Result.Ok r) →
      cspace.lookup_slot st s' t c = ok (core.result.Result.Ok r)) :
    ∀ (N : Nat) (caps : Array obj.Slot 3#usize) (i : U64) (e : Array obj.Slot 3#usize),
      3 - i.val < N →
      ipc.lookup_extra_caps_loop st s t buf caps n i = ok (core.result.Result.Ok e) →
      ipc.lookup_extra_caps_loop st s' t buf caps n i = ok (core.result.Result.Ok e) := by
  intro N
  induction N with
  | zero => intro _ _ _ hN; omega
  | succ N ih =>
    intro caps i e hN h
    rw [lecLoop_unfold] at h ⊢
    obtain ⟨y, hy, hk⟩ := bind_eq_ok h
    have hne : ∀ f, y ≠ ControlFlow.done (core.result.Result.Err f) := by
      rintro f rfl; simp at hk
    obtain ⟨hy', hc⟩ := lec_body_keep hb hls hy hne
    rw [hy', bind_ok]
    cases y with
    | done z => exact hk
    | cont x =>
      obtain ⟨h3, hx⟩ := hc x rfl
      exact ih x.1 x.2 e (by omega) hk

/-- **`lookup_extra_caps` read congruence**: the buffer's words (when there
is a buffer) and the lookups agree, so a successful lookup at `s` is the same
at `s'`. -/
theorem lec_keep {s s' : S} {t : obj.Tcb} {buf : U64} {info : msginfo.MessageInfo}
    {e : Array obj.Slot 3#usize}
    (hb : buf ≠ 0#u64 → ∀ k : U64, k.val < 128 →
      L.mem s' (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul k 8#u64)) =
        L.mem s (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul k 8#u64)))
    (hls : ∀ c r, cspace.lookup_slot st s t c = ok (core.result.Result.Ok r) →
      cspace.lookup_slot st s' t c = ok (core.result.Result.Ok r))
    (h : ipc.lookup_extra_caps st s t buf info = ok (core.result.Result.Ok e)) :
    ipc.lookup_extra_caps st s' t buf info = ok (core.result.Result.Ok e) := by
  unfold ipc.lookup_extra_caps at h ⊢
  by_cases h0 : buf = 0#u64
  · rw [if_pos h0] at h ⊢; exact h
  · rw [if_neg h0] at h ⊢
    exact lec_loop_keep (hb h0) hls 4 _ _ _ (by simp) h

/-! ## The accepted entry -/

set_option maxHeartbeats 8000000 in
/-- **`inv_local_same`: the frame-cap invocation beside the serial gate,
where it ran, is the general entry** `syscall.handle_syscall … SysCall`
(module docstring), given the placement facts at the entry state (`BXI`,
`CnOff`, the sender buffer's words outside the TCBs and nodes), the top's
flag fact, and that `p` is the plan fl4-sync computed at the entry state. -/
theorem inv_local_same (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s s' : S} {a a' : A} {n : I64}
    {p : localinv.Plan}
    {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hbuf : ∀ t, sched.cur_thread st s = ok t →
      msg.lookup_ipc_buffer st s false t ⦃ w => BufOK {b | OutsideObjs st T Cs s b} w ⦄)
    (hflag : ∀ t v, sched.cur_thread st s = ok t → obj.Tcb.flags st t (L.wr s (regA t layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hp : localinv.plan st s n = ok (some p))
    (h : syscall.handle_invocation_local st ar s a n p = ok (true, s', a')) :
    syscall.handle_syscall st ar s a n = ok (s', a') := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  have hT : TcbPlaced T := hSQ.tcbs
  have hcC : L.cpu s ∈ Cs := hSQ.cur
  have hN : NodePlaced st T s (L.cpu s) := hSQ.nodes _ hcC
  have hcT : L.curW s ∈ T := hSQ.curT
  obtain ⟨t0, info0, cptr0, r0, buf0, e0, et0, ei0, ec0, er0, eb0, ee0, hps, hpe⟩ := plan_fields hp
  unfold syscall.handle_invocation_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  have htt : t0 = t := ok_inj_ff (et0.symm.trans et)
  rw [htt] at ei0 ec0 er0 eb0 ee0
  obtain ⟨info, ei, h⟩ := bind_eq_ok h
  have hii : info0 = info := ok_inj_ff (ei0.symm.trans ei)
  rw [hii] at ee0
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
  rw [hn]
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
  simp only [↓reduceIte] at h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  · simp at h
  simp only [↓reduceIte] at h
  -- the prefix and the reads at the dispatch state
  have htT : t ∈ T := by
    rw [cur_thread_ok] at et; rw [← ok_inj_ff et]; exact hcT
  have ht' := hT t htT
  obtain ⟨et2, tK, oK⟩ := inv_prefix ar hT hN hcC et htT es1 eu hA
  have hb : syscall.budget_ok st ar s1 a = ok (true, s2, a1) := by
    unfold syscall.budget_ok
    rw [eu]; simp only [bind_ok, uncurry_apply_pair]
    exact check_budget_restart_suf ar ecsc ec eb1
  have ei2 : msg.msg_info st s2 t = ok info := by
    unfold msg.msg_info at ei ⊢
    rw [reg_keepK ht' (r := layout.reg.MSG_INFO) (by simp) (by simp) tK]; exact ei
  have ec2 : obj.Tcb.reg st t s2 layout.reg.CAP = ok cptr0 := by
    rw [reg_keepK ht' (r := layout.reg.CAP) (by simp) (by simp) tK]; exact ec0
  have er2 := lookup_slot_keep ht' (hCn t et) tK oK er0
  have eb2 : msg.lookup_ipc_buffer st s2 false t = ok buf0 := by
    rw [lookup_buf_keep ht' false tK]; exact eb0
  have hBO := hbuf t et
  rw [eb0, WP.spec_ok] at hBO
  have ee2 := lec_keep (s' := s2) (fun h0 k hk => oK _ (hBO h0 k hk))
    (fun _ _ e => lookup_slot_keep ht' (hCn t et) tK oK e) ee0
  -- the flags word at the `FAULT_IP`-written state: trap clear (the top's fact)
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
  have c2s : ¬ fl4_abi.syscall.SysCall < fl4_abi.syscall.SYSCALL_MIN := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SYSCALL_MIN
    first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
  have c3s : ¬ fl4_abi.syscall.SysCall > fl4_abi.syscall.SYSCALL_MAX := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SYSCALL_MAX
    first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
  have nRR : ¬ fl4_abi.syscall.SysCall = fl4_abi.syscall.SysReplyRecv := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysReplyRecv; decide
  have n15 : ¬ fl4_abi.syscall.SysCall = fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysSend; decide
  have n16 : ¬ fl4_abi.syscall.SysCall = fl4_abi.syscall.SysNBSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysNBSend; decide
  -- the rest of the local run
  obtain ⟨buf, ebuf, h⟩ := bind_eq_ok h
  have hbb : buf = buf0 := ok_inj_ff (ebuf.symm.trans eb2)
  subst hbb
  obtain ⟨len, elen, h⟩ := bind_eq_ok h
  obtain ⟨cap, ecap, h⟩ := bind_eq_ok h
  obtain ⟨⟨r, s3, a2⟩, edec, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s4, a3, r1⟩, em, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨x5, s5, a4⟩, eai, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s6, a5⟩, efin, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq, true_and] at e
  obtain ⟨rfl, rfl⟩ := e
  rw [hps] at ecap edec
  rw [hpe] at edec
  -- the general run
  unfold syscall.handle_syscall syscall.syscall
  rw [et]; simp only [bind_ok]
  rw [enx]; simp only [lift, bind_ok]
  rw [es1]; simp only [bind_ok]
  rw [efl]; simp only [lift, bind_ok, if_neg c1', if_neg c2s, if_neg c3s]
  rw [hb]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte, if_true, eq_self_iff_true, nRR]
  unfold syscall.dispatch_syscall
  rw [et2]; simp only [bind_ok]
  rw [ec2]; simp only [bind_ok]
  rw [reg_ok]; simp only [bind_ok]
  simp only [n15, n16, ↓reduceIte, if_true, if_false]
  unfold syscall.handle_invocation
  rw [et2]; simp only [bind_ok]
  rw [ei2]; simp only [bind_ok]
  rw [er2]; simp only [bind_ok]
  rw [ecap]; simp only [bind_ok]
  rw [eb2]; simp only [bind_ok]
  rw [ee2]; simp only [bind_ok]
  rw [elen]; simp only [bind_ok]
  rw [edec]; simp only [bind_ok, uncurry_apply_pair]
  cases r with
  | Ok u =>
    try simp only [bind_ok, uncurry_apply_pair]
    try dsimp only at em
    obtain ⟨i6, es6, em⟩ := bind_eq_ok em
    obtain ⟨t1, et1, em⟩ := bind_eq_ok em
    have e := ok_inj_ff em
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    rw [es6]; simp only [bind_ok]
    by_cases hr : i6 = sched.TS_RESTART
    · rw [if_pos hr] at et1
      rw [if_pos hr]
      try simp only [↓reduceIte, if_true, eq_self_iff_true]
      obtain ⟨s5', e5, e6⟩ := bind_eq_ok et1
      rw [e5]; simp only [bind_ok]
      rw [e6]; simp only [bind_ok, uncurry_apply_pair]
      rw [eai]; simp only [bind_ok, uncurry_apply_pair]
      rw [efin]; simp only [bind_ok, uncurry_apply_pair]
    · rw [if_neg hr] at et1
      rw [if_neg hr]
      have e := ok_inj_ff et1
      subst e
      simp only [bind_ok, uncurry_apply_pair]
      rw [eai]; simp only [bind_ok, uncurry_apply_pair]
      rw [efin]; simp only [bind_ok, uncurry_apply_pair]
  | Err ex =>
    cases ex
    case Sys e1 =>
      simp only [bind_ok, bind_assoc_eq, uncurry_apply_pair, ↓reduceIte, if_true, eq_self_iff_true] at em ⊢
      obtain ⟨x, ex, em⟩ := bind_eq_ok em
      obtain ⟨s5', e5, ex⟩ := bind_eq_ok ex
      have ex' := ok_inj_ff ex
      subst ex'
      try simp only [uncurry_apply_pair] at em
      try dsimp only at em
      have e := ok_inj_ff em
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      rw [e5]; simp only [bind_ok, uncurry_apply_pair]
      rw [eai]; simp only [bind_ok, uncurry_apply_pair]
      rw [efin]; simp only [bind_ok, uncurry_apply_pair]
    all_goals
      simp only [bind_ok, bind_assoc_eq, uncurry_apply_pair, ↓reduceIte] at em ⊢
      have e := ok_inj_ff em
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      rw [eai]; simp only [bind_ok, uncurry_apply_pair]
      rw [efin]; simp only [bind_ok, uncurry_apply_pair]

/-- **The frame-cap local entry where it ran: the general entry's
postconditions** (on the `true` results). -/
theorem inv_local_triple (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s : S} {a : A} {n : I64}
    {p : localinv.Plan} {P : S × A → Prop}
    {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hbuf : ∀ t, sched.cur_thread st s = ok t →
      msg.lookup_ipc_buffer st s false t ⦃ w => BufOK {b | OutsideObjs st T Cs s b} w ⦄)
    (hflag : ∀ t v, sched.cur_thread st s = ok t → obj.Tcb.flags st t (L.wr s (regA t layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hp : localinv.plan st s n = ok (some p))
    (hG : syscall.handle_syscall st ar s a n ⦃ P ⦄) :
    syscall.handle_invocation_local st ar s a n p ⦃ r => r.1 = true → P (r.2.1, r.2.2) ⦄ := by
  obtain ⟨⟨b, s', a'⟩, e, -⟩ := spec_ex_fd (P0.syscall.handle_invocation_local.p0 st ar s a n p L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := inv_local_same ar hA hI hCn hbuf hflag hp e
  rw [hs, WP.spec_ok] at hG
  exact hG

end

end Fl4Proofs.P1
