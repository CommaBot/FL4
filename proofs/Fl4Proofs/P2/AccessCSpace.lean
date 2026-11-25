/-
# P2: guarded-store lemmas for the CSpace and message helpers (line p2io)

For `PathObl.acc` (`P2/PathObl.lean`): a run of a callee on `PathObl.guard st R W`
ends as on `st`, given that the words the run reads are in `R` and the words
it writes are in `W`. The callees here branch on what they read, so the
lemmas are stated **run-relative**: from `h : f st … = ok y` and hypotheses
naming only the words that run reads (conditioned on the values `st` returns),
`f gS … = ok y`. Leaves come from `P2/AccessLeaf.lean`.

* tools: `tr_bind` / `tr_ite` (transfer an `= ok y` equation along a bind or an
  `if` whose condition and continuation agree), `msg.buf_get.guard`
  (registers, refills and the scheduler checks: `P2/AccessSched.lean`, line p2sl);
* `rab_body.guard`, `rab_loop.guard`, `rab.guard`: the CSpace walk
  (`resolve_address_bits`, fuel induction as P1's `rab_loop_congr`) reads the
  slot words of the CNode-valued slots it walks through (`hRc`, closed under a
  predicate `C` on CNode pointers) and of the slot it returns (`hRf`);
* `lookup_slot.guard`: the CTable root slot and the walk;
* `lookup_ipc_buffer.guard`: the `IPC_BUFFER` word and the buffer slot;
* `syscall_arg.guard`, `lookup_extra_caps.guard_zero` (no extra caps: no
  access), `msg_info.guard`.

Premises: none.
-/
import Fl4Proofs.P2.AccessSched
import Fl4Proofs.P1.RabCongr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section tools

/-- Transfer along a bind: the first computation answers the same, the
continuation then ends the same. -/
theorem tr_bind {α β : Type _} {m m' : Result α} {k k' : α → Result β} {y : β}
    (h1 : ∀ x, m = ok x → k x = ok y → m' = ok x) (h2 : ∀ x, m = ok x → k x = ok y → k' x = ok y) :
    Std.bind m k = ok y → Std.bind m' k' = ok y := fun h => by
  obtain ⟨x, e, hx⟩ := bind_eq_ok h
  rw [h1 x e hx]; simp only [bind_ok, bind_tc_ok]; exact h2 x e hx

/-- Transfer along a bind on the same computation. -/
theorem tr_bind_same {α β : Type _} {m : Result α} {k k' : α → Result β} {y : β}
    (h2 : ∀ x, m = ok x → k x = ok y → k' x = ok y) :
    Std.bind m k = ok y → Std.bind m k' = ok y :=
  tr_bind (fun _ hx _ => hx) h2

/-- Transfer along an `if` on the same condition. -/
theorem tr_ite {β : Type _} {c : Prop} [Decidable c] {x z x' z' : Result β} {y : β}
    (h1 : c → x = ok y → x' = ok y) (h2 : ¬ c → z = ok y → z' = ok y) :
    (if c then x else z) = ok y → (if c then x' else z') = ok y := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact h1 hc
  · rw [if_neg hc, if_neg hc]; exact h2 hc

end tools

section leaf
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]

theorem msg.buf_get.guard (s : S) (buf i : U64)
    (h : R (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64))) :
    msg.buf_get gS s buf i = msg.buf_get st s buf i := by
  unfold msg.buf_get
  simp only [lift, bind_ok]
  exact gst_read_of h rfl

theorem msg.msg_info.guard (s : S) (t : obj.Tcb) (h : R (regA t layout.reg.MSG_INFO)) :
    msg.msg_info gS s t = msg.msg_info st s t := by
  unfold msg.msg_info
  rw [obj.Tcb.reg.guard t s _ h]

/-- The register a message register `i < 4` lives in. -/
theorem msg_register_ok (i : U64) : ∃ r, msg.msg_register i = ok r := by
  unfold msg.msg_register
  split_ifs <;> exact ⟨_, rfl⟩

theorem msg.syscall_arg.guard (s : S) (t : obj.Tcb) (buf i : U64)
    (hreg : ∀ r, msg.msg_register i = ok r → R (regA t r))
    (hbuf : R (core.num.U64.wrapping_add buf
      (core.num.U64.wrapping_mul (core.num.U64.wrapping_add i 1#u64) 8#u64))) :
    msg.syscall_arg gS s t buf i = msg.syscall_arg st s t buf i := by
  unfold msg.syscall_arg
  split_ifs with h1 h2
  · obtain ⟨r, hr⟩ := msg_register_ok i
    rw [hr]; simp only [bind_ok]
    exact obj.Tcb.reg.guard t s r (hreg r hr)
  · simp only [lift, bind_ok]
    exact msg.buf_get.guard s buf _ hbuf
  · rfl

/-! ## The CSpace walk -/

/-- One step of the walk on a CNode cap. -/
theorem rab_body.guard {s : S} {cptr n fuel p r gs g : U64}
    {y : ControlFlow (capability.Cap × U64 × U64) (core.result.Result cspace.Resolved error.LookupFault)}
    (hR : ∀ off c, obj.Slot.cap st (cnSlot p off) s = ok c →
      ((∃ p' r' gs' g', c = .CNode p' r' gs' g') ∨
        ∃ bl, y = ControlFlow.done (core.result.Result.Ok { slot := cnSlot p off, bits_left := bl })) →
      R (cnSlot p off) ∧ R (core.num.U64.wrapping_add (cnSlot p off) 8#u64))
    (h : cspace.resolve_address_bits_loop.body st s cptr (.CNode p r gs g) n fuel = ok y) :
    cspace.resolve_address_bits_loop.body gS s cptr (.CNode p r gs g) n fuel = ok y := by
  unfold cspace.resolve_address_bits_loop.body at h ⊢
  simp only [obj.Slot.index, lift, bind_ok] at h ⊢
  revert h
  repeat' (first
    | (exact fun h => h)
    | (with_reducible refine tr_ite (fun _ => ?_) (fun _ => ?_))
    | (with_reducible_and_instances refine tr_bind_same (fun _ _ => ?_)))
  all_goals
    with_reducible_and_instances refine tr_bind (fun c hc hk => ?_) (fun _ _ hk => hk)
    rw [← hc]
    obtain ⟨h0, h8⟩ := hR _ c hc (by
      cases c <;>
        first
        | exact Or.inl ⟨_, _, _, _, rfl⟩
        | exact Or.inr ⟨_, (ok_inj_ff hk).symm⟩)
    exact obj.Slot.cap.guard _ s h0 h8

/-- The walk's step on a non-CNode cap touches no store. -/
theorem rab_body_nonCN (st st' : machine.Store S) (s : S) (cptr : U64) (cap : capability.Cap) (n fuel : U64)
    (hc : ∀ p r gs g, cap ≠ .CNode p r gs g) :
    cspace.resolve_address_bits_loop.body st' s cptr cap n fuel =
      cspace.resolve_address_bits_loop.body st s cptr cap n fuel := by
  cases cap <;> first | rfl | exact absurd rfl (hc _ _ _ _)

/-- **The walk** (fuel induction): it reads the slots of the CNode caps it
walks (`C`-closed) holding a CNode (`hRc`) and the slot it returns (`hRf`). -/
theorem rab_loop.guard {s : S} {cptr : U64} (C : U64 → Prop)
    (hRc : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') →
      R (cnSlot p off) ∧ R (core.num.U64.wrapping_add (cnSlot p off) 8#u64))
    (hcl : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') → C p') :
    ∀ (N : Nat) (cap : capability.Cap) (n fuel : U64) (res : core.result.Result cspace.Resolved error.LookupFault),
      fuel.val < N → (∀ p r gs g, cap = .CNode p r gs g → C p) →
      (∀ x, res = .Ok x → R x.slot ∧ R (core.num.U64.wrapping_add x.slot 8#u64)) →
      cspace.resolve_address_bits_loop st cap s cptr n fuel = ok res →
      cspace.resolve_address_bits_loop gS cap s cptr n fuel = ok res := by
  intro N
  induction N with
  | zero => intro _ _ _ _ hf; omega
  | succ N ih =>
    intro cap n fuel res hf hc hRf h
    rw [rabLoop_unfold] at h ⊢
    obtain ⟨y, hy, hk⟩ := bind_eq_ok h
    by_cases hcn : ∃ p r gs g, cap = .CNode p r gs g
    · obtain ⟨p, r, gs, g, rfl⟩ := hcn
      have hy' : cspace.resolve_address_bits_loop.body gS s cptr (.CNode p r gs g) n fuel = ok y := by
        refine rab_body.guard (fun off c hc' hb => ?_) hy
        rcases hb with ⟨p', r', gs', g', rfl⟩ | ⟨bl, rfl⟩
        · exact hRc p off p' r' gs' g' (hc _ _ _ _ rfl) hc'
        · exact hRf _ (ok_inj_ff hk).symm
      rw [hy']; simp only [bind_ok]
      cases y with
      | done z => exact hk
      | cont x =>
        obtain ⟨off, hoff, hlt⟩ := rab_body_cont st hy
        exact ih x.1 x.2.1 x.2.2 res (by omega)
          (fun p' r' gs' g' e => hcl p off p' r' gs' g' (hc _ _ _ _ rfl) (e ▸ hoff)) hRf hk
    · rw [rab_body_nonCN st gS s cptr cap n fuel (fun p r gs g e => hcn ⟨p, r, gs, g, e⟩), hy]
      simp only [bind_ok]
      cases y with
      | done z => exact hk
      | cont x =>
        exfalso
        (cases cap <;> (try simp [cspace.resolve_address_bits_loop.body] at hy)) <;>
          exact hcn ⟨_, _, _, _, rfl⟩

/-- `resolve_address_bits` (the loop with fuel 65). -/
theorem rab.guard {s : S} {root : capability.Cap} {cptr n : U64}
    {res : core.result.Result cspace.Resolved error.LookupFault} (C : U64 → Prop)
    (hRc : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') →
      R (cnSlot p off) ∧ R (core.num.U64.wrapping_add (cnSlot p off) 8#u64))
    (hcl : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') → C p')
    (hroot : ∀ p r gs g, root = .CNode p r gs g → C p)
    (hRf : ∀ x, res = .Ok x → R x.slot ∧ R (core.num.U64.wrapping_add x.slot 8#u64))
    (h : cspace.resolve_address_bits st s root cptr n = ok res) :
    cspace.resolve_address_bits gS s root cptr n = ok res :=
  rab_loop.guard C hRc hcl 66 root n 65#u64 res (by simp) hroot hRf h

/-- The CTable root slot of `t`. -/
theorem ctable_slot_ok (t : U64) : ∃ sl, obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok sl := by
  unfold obj.Tcb.slot; simp only [lift, bind_ok]; exact ⟨_, rfl⟩

/-- **`lookup_slot`**: the CTable root slot (`sl`, both words) and the walk. -/
theorem cspace.lookup_slot.guard {s : S} {t cptr sl : U64}
    {res : core.result.Result cspace.Resolved error.LookupFault} (C : U64 → Prop)
    (hsl : obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok sl)
    (hR0 : R sl) (hR8 : R (core.num.U64.wrapping_add sl 8#u64))
    (hRc : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') →
      R (cnSlot p off) ∧ R (core.num.U64.wrapping_add (cnSlot p off) 8#u64))
    (hcl : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') → C p')
    (hroot : ∀ p r gs g, obj.Slot.cap st sl s = ok (.CNode p r gs g) → C p)
    (hRf : ∀ x, res = .Ok x → R x.slot ∧ R (core.num.U64.wrapping_add x.slot 8#u64))
    (h : cspace.lookup_slot st s t cptr = ok res) :
    cspace.lookup_slot gS s t cptr = ok res := by
  unfold cspace.lookup_slot at h ⊢
  rw [hsl] at h ⊢; simp only [bind_ok] at h ⊢
  rw [obj.Slot.cap.guard sl s hR0 hR8]
  obtain ⟨root, er, h⟩ := bind_eq_ok h
  rw [er]; simp only [bind_ok]
  exact rab.guard C hRc hcl (fun p r gs g e => hroot p r gs g (e ▸ er)) hRf h

/-! ## IPC buffer, extra caps -/

/-- The buffer slot of `t`. -/
theorem buffer_slot_ok (t : U64) : ∃ sl, obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok sl := by
  unfold obj.Tcb.slot; simp only [lift, bind_ok]; exact ⟨_, rfl⟩

/-- **`lookup_ipc_buffer`**: the `IPC_BUFFER` word and both words of the
buffer slot. -/
theorem msg.lookup_ipc_buffer.guard (s : S) (rcv : Bool) (t : obj.Tcb) {sl : U64}
    (hsl : obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok sl)
    (hI : R (core.num.U64.wrapping_add t 3512#u64)) (hR0 : R sl) (hR8 : R (core.num.U64.wrapping_add sl 8#u64)) :
    msg.lookup_ipc_buffer gS s rcv t = msg.lookup_ipc_buffer st s rcv t := by
  unfold msg.lookup_ipc_buffer
  rw [obj.Tcb.ipc_buffer.guard t s hI, hsl]
  simp only [bind_ok]
  rw [obj.Slot.cap.guard sl s hR0 hR8]

/-- **`lookup_extra_caps` with no extra caps** reads nothing. -/
theorem ipc.lookup_extra_caps.guard_zero (s : S) (t : obj.Tcb) (buf : U64) (info : msginfo.MessageInfo)
    (h0 : info.extra_caps = 0#u64) :
    ipc.lookup_extra_caps gS s t buf info = ipc.lookup_extra_caps st s t buf info := by
  unfold ipc.lookup_extra_caps
  split_ifs
  · rfl
  · rw [h0]
    unfold ipc.lookup_extra_caps_loop
    rw [loop, loop]
    have e : ∀ (st' : machine.Store S) (c : Array obj.Slot 3#usize),
        ipc.lookup_extra_caps_loop.body st' s t buf 0#u64 c 0#u64 = ok (ControlFlow.done (.Ok c)) := by
      intro st' c
      unfold ipc.lookup_extra_caps_loop.body
      simp
    simp only [e, bind_ok]

end leaf

end Fl4Proofs.P2.PathObl
